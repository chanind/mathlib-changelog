### [2020-10-31 22:44:12](https://github.com/leanprover-community/mathlib/commit/6f7c539)
docs(order/complete_lattice): make two docstrings more detailed ([#4859](https://github.com/leanprover-community/mathlib/pull/4859))
Following [discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Constructing.20a.20complete.20lattice), clarify information about how to construct a complete lattice while preserving good definitional equalities.

### [2020-10-31 20:22:31](https://github.com/leanprover-community/mathlib/commit/51cbb83)
refactor(tactic/norm_num): move norm_num extensions ([#4822](https://github.com/leanprover-community/mathlib/pull/4822))
[#4820](https://github.com/leanprover-community/mathlib/pull/4820) adds the long awaited ability for `norm_num` to be extended in other files. There are two norm_num extensions currently in mathlib: `norm_digits`, which was previously exposed as a standalone tactic, and `eval_prime`, which was a part of `norm_num` and so caused `tactic.norm_num` to depend on `data.nat.prime`. This PR turns both of these into norm_num extensions, and changes the dependencies so that `data.nat.prime` can import `norm_num` rather than the other way around (which required splitting `pnat` primality and gcd facts to their own file).

### [2020-10-31 17:41:26](https://github.com/leanprover-community/mathlib/commit/be161d1)
feat(category_theory/sites): functor inclusion constructions ([#4845](https://github.com/leanprover-community/mathlib/pull/4845))

### [2020-10-31 17:41:24](https://github.com/leanprover-community/mathlib/commit/d91c878)
chore(group_theory/group_action): introduce `smul_comm_class` ([#4770](https://github.com/leanprover-community/mathlib/pull/4770))

### [2020-10-31 15:07:49](https://github.com/leanprover-community/mathlib/commit/9a03bdf)
chore(algebra/ordered_group): use implicit args, add `add_eq_coe` ([#4853](https://github.com/leanprover-community/mathlib/pull/4853))
* Use implicit arguments in various `iff` lemmas about `with_top`.
* Add `add_eq_coe`.
* Rewrite `with_top.ordered_add_comm_monoid` moving `begin .. end` blocks inside the structure.
This way we don't depend on the fact that `refine` doesn't introduce any `id`s and it's easier to see right away which block proves which statement.

### [2020-10-31 13:30:44](https://github.com/leanprover-community/mathlib/commit/e14c378)
refactor(order/filter): move some proofs to `bases` ([#3478](https://github.com/leanprover-community/mathlib/pull/3478))
Move some proofs to `order/filter/bases` and add `filter.has_basis` versions.
Non-bc API changes:
* `filter.inf_ne_bot_iff`; change `∀ {U V}, U ∈ f → V ∈ g → ...` to `∀ ⦃U⦄, U ∈ f → ∀ ⦃V⦄, V ∈ g → ...`
  so that `simp` lemmas about `∀ U ∈ f` can further simplify the result;
* `filter.inf_eq_bot_iff`: similarly, change `∃ U V, ...` to `∃ (U ∈ f) (V ∈ g), ...`
* `cluster_pt_iff`: similarly, change `∀ {U V : set α}, U ∈ 𝓝 x → V ∈ F → ...` to
  `∀ ⦃U : set α⦄ (hU : U ∈ 𝓝 x) ⦃V⦄ (hV : V ∈ F), ...`

### [2020-10-31 08:44:02](https://github.com/leanprover-community/mathlib/commit/f9c8abe)
chore(data/finset/basic): a few lemmas about `finset.piecewise` ([#4852](https://github.com/leanprover-community/mathlib/pull/4852))

### [2020-10-31 08:44:00](https://github.com/leanprover-community/mathlib/commit/7756265)
chore(linear_algebra/affine_space/ordered): compare endpoints to midpoint ([#4851](https://github.com/leanprover-community/mathlib/pull/4851))

### [2020-10-31 08:43:59](https://github.com/leanprover-community/mathlib/commit/1f61621)
feat(linear_algebra/affine_space/affine_map): add `affine_map.proj` ([#4850](https://github.com/leanprover-community/mathlib/pull/4850))

### [2020-10-31 08:43:57](https://github.com/leanprover-community/mathlib/commit/6a44930)
refactor(data/pnat): move data.pnat.prime ([#4839](https://github.com/leanprover-community/mathlib/pull/4839))
Remove the dependency `data.pnat.basic -> data.nat.prime`. Needed for [#4822](https://github.com/leanprover-community/mathlib/pull/4822).

### [2020-10-31 08:43:55](https://github.com/leanprover-community/mathlib/commit/3b2c97f)
feat(data/dfinsupp): Port `finsupp.lsum` and lemmas about `lift_add_hom` ([#4833](https://github.com/leanprover-community/mathlib/pull/4833))
This then removes the proofs of any `direct_sum` lemmas which become equivalent to the `lift_add_hom` lemmas

### [2020-10-31 08:43:53](https://github.com/leanprover-community/mathlib/commit/17697a6)
feat(data/dfinsupp): Add dfinsupp.single_eq_single_iff, and subtype.heq_iff_coe_eq ([#4810](https://github.com/leanprover-community/mathlib/pull/4810))
This ought to make working with dfinsupps over subtypes easier

### [2020-10-31 06:18:28](https://github.com/leanprover-community/mathlib/commit/67c2b5a)
feat(analysis/normed_space/add_torsor): distance to midpoint ([#4849](https://github.com/leanprover-community/mathlib/pull/4849))

### [2020-10-31 06:18:25](https://github.com/leanprover-community/mathlib/commit/1521da6)
feat(order/conditionally_complete_lattice): nested intervals lemma ([#4848](https://github.com/leanprover-community/mathlib/pull/4848))
* Add a few versions of the nested intervals lemma.
* Add `pi`-instance for `conditionally_complete_lattice`.

### [2020-10-31 06:18:24](https://github.com/leanprover-community/mathlib/commit/f5fd218)
feat(algebra/module/ordered): add pi instance ([#4847](https://github.com/leanprover-community/mathlib/pull/4847))

### [2020-10-31 06:18:21](https://github.com/leanprover-community/mathlib/commit/6fc3517)
feat(category_theory/sites): generate lemmas ([#4840](https://github.com/leanprover-community/mathlib/pull/4840))
A couple of simple lemmas about the sieve generated by certain presieves.

### [2020-10-31 06:18:19](https://github.com/leanprover-community/mathlib/commit/517f0b5)
feat(ring_theory/polynomial/basic): prerequisites for galois_definition ([#4829](https://github.com/leanprover-community/mathlib/pull/4829))

### [2020-10-31 06:18:16](https://github.com/leanprover-community/mathlib/commit/0f39d7a)
feat(data/prod): comp_map ([#4826](https://github.com/leanprover-community/mathlib/pull/4826))

### [2020-10-31 04:53:40](https://github.com/leanprover-community/mathlib/commit/2283cf0)
chore(order/filter/bases): golf a proof ([#4834](https://github.com/leanprover-community/mathlib/pull/4834))
* rename `filter.has_basis.forall_nonempty_iff_ne_bot` to
  `filter.has_basis.ne_bot_iff`, swap LHS with RHS;
* add `filter.has_basis.eq_bot_iff`;
* golf the proof of `filter.has_basis.ne_bot` using `filter.has_basis.forall_iff`.

### [2020-10-31 02:07:09](https://github.com/leanprover-community/mathlib/commit/94fa905)
feat(analysis/calculus/times_cont_diff): differentiability of field inverse ([#4795](https://github.com/leanprover-community/mathlib/pull/4795))

### [2020-10-31 00:58:01](https://github.com/leanprover-community/mathlib/commit/d5650a7)
chore(scripts): update nolints.txt ([#4844](https://github.com/leanprover-community/mathlib/pull/4844))
I am happy to remove some nolints for you!

### [2020-10-30 18:58:08](https://github.com/leanprover-community/mathlib/commit/cc7f06b)
feat(data/polynomial/lifts): polynomials that lift ([#4796](https://github.com/leanprover-community/mathlib/pull/4796))
Given semirings `R` and `S` with a morphism `f : R →+* S`, a polynomial with coefficients in `S` lifts if there exist `q : polynomial R` such that `map f p = q`. I proved some basic results about polynomials that lifts, for example concerning the sum etc.
Almost all the proof are trivial (and essentially identical), fell free to comment just the first ones, I will do the changes in all the relevant lemmas.
The proofs of `lifts_iff_lifts_deg` (a polynomial that lifts can be lifted to a polynomial of the same degree) and of `lifts_iff_lifts_deg_monic` (the same for monic polynomials) are quite painful, but this are the shortest proofs I found... I think that at least these two results deserve to be in mathlib (I'm using them to prove that the cyclotomic polynomial lift to `\Z`).

### [2020-10-30 14:20:39](https://github.com/leanprover-community/mathlib/commit/bfadf05)
feat(algebra, logic): Pi instances for nontrivial and monoid_with_zero ([#4766](https://github.com/leanprover-community/mathlib/pull/4766))

### [2020-10-30 11:09:12](https://github.com/leanprover-community/mathlib/commit/58f8817)
feat(number_theory/fermat4): The n=4 case of fermat ([#4720](https://github.com/leanprover-community/mathlib/pull/4720))
Fermat's last theorem for n=4.

### [2020-10-30 11:09:05](https://github.com/leanprover-community/mathlib/commit/d28e3d1)
feat(ring_theory/witt_vector/is_poly): supporting ghost calculations ([#4691](https://github.com/leanprover-community/mathlib/pull/4691))
Most operations on Witt vectors can be described/defined
by evaluating integral polynomials on the coefficients of Witt vectors.
One can prove identities between combinations of such operations
by applying the non-injective ghost map,
and continuing to prove the resulting identity of ghost components.
Such a calculation is called a ghost calculation.
This file provides the theoretical justification for why
applying the non-injective ghost map is a legal move,
and it provides tactics that aid in applying this step
to the point that it is almost transparent.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-30 08:20:23](https://github.com/leanprover-community/mathlib/commit/3aac028)
feat(field_theory/intermediate_field): equalities from inclusions and dimension bounds ([#4828](https://github.com/leanprover-community/mathlib/pull/4828))

### [2020-10-30 08:20:21](https://github.com/leanprover-community/mathlib/commit/6ec7aec)
feat(data/polynomial): ext lemmas for homomorphisms from `polynomial R` ([#4823](https://github.com/leanprover-community/mathlib/pull/4823))

### [2020-10-30 08:20:19](https://github.com/leanprover-community/mathlib/commit/03a477c)
feat(data/dfinsupp): Port over the `finsupp.lift_add_hom` API ([#4821](https://github.com/leanprover-community/mathlib/pull/4821))
These lemmas are mostly copied with minimal translation from `finsupp`.
A few proofs are taken from `direct_sum`.
The API of `direct_sum` is deliberately unchanged in this PR.

### [2020-10-30 08:20:18](https://github.com/leanprover-community/mathlib/commit/5ae192e)
feat(data/equiv, algebra/*): Add simps projections to many equivs and homs ([#4818](https://github.com/leanprover-community/mathlib/pull/4818))
This doesn't actually change any existing lemmas to use these projections.

### [2020-10-30 08:20:16](https://github.com/leanprover-community/mathlib/commit/d46d0c2)
chore(topology/basic): the set of cluster pts of a filter is a closed set ([#4815](https://github.com/leanprover-community/mathlib/pull/4815))

### [2020-10-30 08:20:14](https://github.com/leanprover-community/mathlib/commit/072cfc5)
chore(data/dfinsupp): Provide dfinsupp with a semimodule instance ([#4801](https://github.com/leanprover-community/mathlib/pull/4801))
finsupp already has one, it seems pointless to hide the one for dfinsupp behind a def.

### [2020-10-30 08:20:09](https://github.com/leanprover-community/mathlib/commit/63c0dac)
refactor(module/ordered): make ordered_semimodule a mixin ([#4719](https://github.com/leanprover-community/mathlib/pull/4719))
Per @urkud's suggestion at [#4683](https://github.com/leanprover-community/mathlib/pull/4683). This should avoid having to introduce a separate `ordered_algebra` class.

### [2020-10-30 05:28:30](https://github.com/leanprover-community/mathlib/commit/4003b3e)
feat(*): a, switch to lean 3.23 ([#4802](https://github.com/leanprover-community/mathlib/pull/4802))
There are three changes affecting mathlib:
1. `ℕ → ℕ` is now elaborated as `∀ ᾰ : ℕ, ℕ`.  This means that `intro` introduces assumptions with names like `ᾰ_1`, etc.  These names should not be used, and instead provided explicitly to `intro` (and other tactics).
2. The heuristic to determine the definition name for `instance : foo bar` has been changed.
3. `by_contra` now uses classical logic, and defaults to the hypothesis name `h`.
4. adds a few new simp-lemmas in `data/typevec`

### [2020-10-30 02:02:16](https://github.com/leanprover-community/mathlib/commit/581b2af)
feat(analysis/asymptotics): Equivalent definitions for `is_[oO] u v l` looking like `u = φ * v` for some `φ` ([#4646](https://github.com/leanprover-community/mathlib/pull/4646))
The advantage of these statements over `u/v` tendsto 0 / is bounded is they do not require any nonvanishing assumptions about `v`

### [2020-10-30 01:08:49](https://github.com/leanprover-community/mathlib/commit/f510728)
chore(scripts): update nolints.txt ([#4825](https://github.com/leanprover-community/mathlib/pull/4825))
I am happy to remove some nolints for you!

### [2020-10-29 22:37:58](https://github.com/leanprover-community/mathlib/commit/fc307f9)
feat(tactic/norm_num): make norm_num extensible ([#4820](https://github.com/leanprover-community/mathlib/pull/4820))
This allows you to extend `norm_num` by defining additional tactics of type `expr → tactic (expr × expr)` with the `@[norm_num]` attribute. It still requires some tactic proficiency to use correctly, but it at least allows us to move all the possible norm_num extensions to their own files instead of the current dependency cycle problem.
This could potentially become a performance problem if too many things are marked `@[norm_num]`, as they are simply looked through in linear order. It could be improved by having extensions register a finite set of constants that they wish to evaluate, and dispatch to the right extension tactic using a `name_map`.
```lean
def foo : ℕ := 1
@[norm_num] meta def eval_foo : expr → tactic (expr × expr)
| `(foo) := pure (`(1:ℕ), `(eq.refl 1))
| _ := tactic.failed
example : foo = 1 := by norm_num
```

### [2020-10-29 19:28:13](https://github.com/leanprover-community/mathlib/commit/2c7efdf)
feat(category_theory/sites): Grothendieck topology on a space ([#4819](https://github.com/leanprover-community/mathlib/pull/4819))
The grothendieck topology associated to a topological space.
I also changed a definition I meant to change in [#4816](https://github.com/leanprover-community/mathlib/pull/4816), and updated the TODOs of some docstrings; I can split these into separate PRs if needed but I think all the changes are quite minor

### [2020-10-29 19:28:10](https://github.com/leanprover-community/mathlib/commit/92af9fa)
feat(category_theory/limits/pullbacks): pullback self is id iff mono ([#4813](https://github.com/leanprover-community/mathlib/pull/4813))

### [2020-10-29 19:28:07](https://github.com/leanprover-community/mathlib/commit/78811e0)
feat(ring_theory/unique_factorization_domain): `unique_factorization_monoid` structure on polynomials over ufd ([#4774](https://github.com/leanprover-community/mathlib/pull/4774))
Provides the `unique_factorization_monoid` structure on polynomials over a UFD

### [2020-10-29 19:28:03](https://github.com/leanprover-community/mathlib/commit/856381c)
chore(data/equiv/basic): arrow_congr preserves properties of binary operators ([#4759](https://github.com/leanprover-community/mathlib/pull/4759))

### [2020-10-29 19:28:00](https://github.com/leanprover-community/mathlib/commit/ccc98d0)
refactor(*): `midpoint`, `point_reflection`, and Mazur-Ulam in affine spaces ([#4752](https://github.com/leanprover-community/mathlib/pull/4752))
* redefine `midpoint` for points in an affine space;
* redefine `point_reflection` for affine spaces (as `equiv`,
  `affine_equiv`, and `isometric`);
* define `const_vsub` as `equiv`, `affine_equiv`, and `isometric`;
* define `affine_map.of_map_midpoint`;
* fully migrate the proof of Mazur-Ulam theorem to affine spaces;

### [2020-10-29 19:27:56](https://github.com/leanprover-community/mathlib/commit/4d19191)
feat(algebra/monoid_algebra): Add an equivalence between `add_monoid_algebra` and `monoid_algebra` in terms of `multiplicative` ([#4402](https://github.com/leanprover-community/mathlib/pull/4402))

### [2020-10-29 18:26:22](https://github.com/leanprover-community/mathlib/commit/d709ed6)
feat(algebra/direct_sum*): relax a lot of constraints to add_comm_monoid ([#3537](https://github.com/leanprover-community/mathlib/pull/3537))

### [2020-10-29 15:42:46](https://github.com/leanprover-community/mathlib/commit/f83468d)
feat(category_theory/functor_category): monos in the functor category ([#4811](https://github.com/leanprover-community/mathlib/pull/4811))

### [2020-10-29 14:18:55](https://github.com/leanprover-community/mathlib/commit/7d7e850)
chore(category_theory/sites): nicer names ([#4816](https://github.com/leanprover-community/mathlib/pull/4816))
Changes the name `arrows_with_codomain` to `presieve` which is more suggestive and shorter, and changes `singleton_arrow` to `singleton`, since it's in the presieve namespace anyway.

### [2020-10-29 13:24:15](https://github.com/leanprover-community/mathlib/commit/8b858d0)
feat(data/dfinsupp): Relax requirements of semimodule conversion to add_comm_monoid ([#3490](https://github.com/leanprover-community/mathlib/pull/3490))
The extra `_`s required to make this still build are unfortunate, but hopefully someone else can work out how to remove them in a later PR.

### [2020-10-29 09:49:53](https://github.com/leanprover-community/mathlib/commit/d510a63)
feat(linear_algebra/finite_dimensional): finite dimensional algebra_hom of fields is bijective ([#4793](https://github.com/leanprover-community/mathlib/pull/4793))
Changes to finite_dimensional.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)

### [2020-10-29 07:30:22](https://github.com/leanprover-community/mathlib/commit/1baf701)
feat(category_theory/Fintype): Adds the category of finite types and its "standard" skeleton. ([#4809](https://github.com/leanprover-community/mathlib/pull/4809))
This PR adds the category `Fintype` of finite types, as well as its "standard" skeleton whose objects are `fin n`.

### [2020-10-29 01:05:47](https://github.com/leanprover-community/mathlib/commit/d9c8215)
chore(scripts): update nolints.txt ([#4814](https://github.com/leanprover-community/mathlib/pull/4814))
I am happy to remove some nolints for you!

### [2020-10-28 20:49:21](https://github.com/leanprover-community/mathlib/commit/69d41da)
feat(tactic/dependencies): add tactics to compute (reverse) dependencies ([#4602](https://github.com/leanprover-community/mathlib/pull/4602))
These are the beginnings of an API about dependencies between expressions. For
now, we only deal with dependencies and reverse dependencies of hypotheses,
which are easy to compute.
Breaking change: `tactic.revert_deps` is renamed to
`tactic.revert_reverse_dependencies_of_hyp` for consistency. Its implementation
is completely new, but should be equivalent to the old one except for the order
in which hypotheses are reverted. (But the old implementation made no particular
guarantees about this order anyway.)

### [2020-10-28 18:09:43](https://github.com/leanprover-community/mathlib/commit/d75da1a)
feat(topology/algebra/group_with_zero): introduce `has_continuous_inv'` ([#4804](https://github.com/leanprover-community/mathlib/pull/4804))
Move lemmas about continuity of division from `normed_field`, add a few new lemmas, and introduce a new typeclass. Also use it for `nnreal`s.

### [2020-10-28 18:09:41](https://github.com/leanprover-community/mathlib/commit/80ffad0)
chore(data/dfinsupp): Make some lemma arguments explicit ([#4803](https://github.com/leanprover-community/mathlib/pull/4803))
This file is long and this is not exhaustive, but this hits most of the simpler ones

### [2020-10-28 18:09:39](https://github.com/leanprover-community/mathlib/commit/7a37dd4)
feat(algebra/monoid_algebra): Bundle lift_nc_mul and lift_nc_one into a ring_hom and alg_hom ([#4789](https://github.com/leanprover-community/mathlib/pull/4789))

### [2020-10-28 18:09:37](https://github.com/leanprover-community/mathlib/commit/28cc74f)
feat(ring_theory/unique_factorization_domain): a `normalization_monoid` structure for ufms ([#4772](https://github.com/leanprover-community/mathlib/pull/4772))
Provides a default `normalization_monoid` structure on a `unique_factorization_monoid`

### [2020-10-28 18:09:35](https://github.com/leanprover-community/mathlib/commit/25df267)
feat(category_theory/limits/presheaf): free cocompletion ([#4740](https://github.com/leanprover-community/mathlib/pull/4740))
Fill in the missing part of [#4401](https://github.com/leanprover-community/mathlib/pull/4401), showing that the yoneda extension is unique. Also adds some basic API around [#4401](https://github.com/leanprover-community/mathlib/pull/4401).

### [2020-10-28 18:09:33](https://github.com/leanprover-community/mathlib/commit/dfa85b5)
feat(archive/imo): formalize IMO 1981 problem Q3 ([#4599](https://github.com/leanprover-community/mathlib/pull/4599))
Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.

### [2020-10-28 15:21:10](https://github.com/leanprover-community/mathlib/commit/40da087)
feat(equiv/basic): use @[simps] ([#4652](https://github.com/leanprover-community/mathlib/pull/4652))
Use the `@[simps]` attribute to automatically generate equation lemmas for equivalences.
The names `foo_apply` and `foo_symm_apply` are used for the projection lemmas of `foo`.

### [2020-10-28 10:34:25](https://github.com/leanprover-community/mathlib/commit/e8f8de6)
feat(ring_theory/valuation): ring of integers ([#4729](https://github.com/leanprover-community/mathlib/pull/4729))

### [2020-10-28 09:18:54](https://github.com/leanprover-community/mathlib/commit/216cbc4)
feat(analysis/special_functions/trigonometric): simp attributes for trig values ([#4806](https://github.com/leanprover-community/mathlib/pull/4806))
simp attributes for the trig values that didn't already have them

### [2020-10-28 07:49:32](https://github.com/leanprover-community/mathlib/commit/6dfa952)
refactor(order/filter): make `filter.has_mem semireducible ([#4807](https://github.com/leanprover-community/mathlib/pull/4807))
This way `simp only []` does not simplify `s ∈ f` to `s ∈ f.sets`.
* Add protected simp lemmas `filter.mem_mk` and `filter.mem_sets`.
* Use implicit argument in `filter.mem_generate_iff`.
* Use `∃ t, s ∈ ...` instead of `s ∈ ⋃ t, ...` in
  `filter.mem_infi_finite` and `filter.mem_infi_finite'`.
* Use an implicit argument in `(non/ne_)empty_of_mem_ultrafilter`.

### [2020-10-28 06:06:38](https://github.com/leanprover-community/mathlib/commit/7807f3d)
chore(linear_algebra/affine_space/basic): split ([#4767](https://github.com/leanprover-community/mathlib/pull/4767))
* Split `linear_algebra/affine_space/basic` into two files: `affine_map` and `affine_subspace`.
* Move notation `affine_space` to the bottom of `algebra/add_torsor`.

### [2020-10-28 01:11:30](https://github.com/leanprover-community/mathlib/commit/4d1da54)
chore(scripts): update nolints.txt ([#4808](https://github.com/leanprover-community/mathlib/pull/4808))
I am happy to remove some nolints for you!

### [2020-10-27 22:22:51](https://github.com/leanprover-community/mathlib/commit/c737996)
feat(algebra/algebra/subalgebra): algebra equalizer ([#4791](https://github.com/leanprover-community/mathlib/pull/4791))
Changes to subalgebra.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)

### [2020-10-27 22:22:50](https://github.com/leanprover-community/mathlib/commit/2a7e215)
feat(data/vector2): scanl and associated lemmas ([#4613](https://github.com/leanprover-community/mathlib/pull/4613))

### [2020-10-27 19:53:05](https://github.com/leanprover-community/mathlib/commit/51e12c0)
chore(ring_theory/fractional_ideal): change exists_eq_span_singleton_mul ([#4800](https://github.com/leanprover-community/mathlib/pull/4800))
Replace assumption `(a : K)` with `(a : R)`
Add result `a \ne 0` 
Change `span_singleton` a to `span singleton (g.to_map a)^-1`
.. in the statement of lemma `exists_eq_span_singleton_mul`
Adapt dependences

### [2020-10-27 19:53:03](https://github.com/leanprover-community/mathlib/commit/97065db)
refactor(data/polynomial): use `linear_map` for `monomial`, review `degree` ([#4784](https://github.com/leanprover-community/mathlib/pull/4784))

### [2020-10-27 19:53:01](https://github.com/leanprover-community/mathlib/commit/a1ab984)
feat(data/finset/lattice,order/basic): add lemmas in order_dual, prove dual order exchanges max' and min' ([#4715](https://github.com/leanprover-community/mathlib/pull/4715))
Introduce functionality to work with order duals and monotone decreasing maps.  The pretty part of the code is by Johan Commelin, the ugly part is my own addition!

### [2020-10-27 17:20:51](https://github.com/leanprover-community/mathlib/commit/1efbf13)
feat(data/vector2): add lemma map_id ([#4799](https://github.com/leanprover-community/mathlib/pull/4799))
`map_id` proves that a vector is unchanged when mapped under the `id` function. This is similar to `list.map_id`. This lemma was marked with the `simp` attribute to make it available to the simplifier.

### [2020-10-27 17:20:47](https://github.com/leanprover-community/mathlib/commit/40e514c)
feat(algebra/monoid_algebra): formula for `lift_nc f g (c • φ)` ([#4782](https://github.com/leanprover-community/mathlib/pull/4782))

### [2020-10-27 17:20:45](https://github.com/leanprover-community/mathlib/commit/99acfda)
feat(category_theory/sites): pretopology ([#4648](https://github.com/leanprover-community/mathlib/pull/4648))
Adds pretopologies.

### [2020-10-27 14:39:13](https://github.com/leanprover-community/mathlib/commit/a027a37)
feat(tactic/simps): user-provided names for projections ([#4663](https://github.com/leanprover-community/mathlib/pull/4663))
Adds the functionality to specify custom projection names, like this:
```lean
initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)
```
These names will always be used and cannot (yet) be manually overridden. 
Implement this for embeddings: `initialize_simps_projections embedding (to_fun → apply)`.
Rename `fixed_points.to_alg_hom_apply -> fixed_points.to_alg_hom_apply_apply`, since `@[simps]` now generates the name `to_alg_hom_apply` instead of `to_alg_hom_to_fun`.

### [2020-10-27 11:55:33](https://github.com/leanprover-community/mathlib/commit/e0b153b)
refactor(*): drop `decidable_linear_order`, switch to Lean 3.22.0 ([#4762](https://github.com/leanprover-community/mathlib/pull/4762))
The main non-bc change in Lean 3.22.0 is leanprover-community/lean[#484](https://github.com/leanprover-community/mathlib/pull/484) which merges `linear_order`
with `decidable_linear_order`. This is the `mathlib` part of this PR.
## List of API changes
* All `*linear_order*` typeclasses now imply decidability of `(≤)`, `(<)`, and `(=)`.
* Drop `classical.DLO`.
* Drop `discrete_linear_ordered_field`, use `linear_ordered_field` instead.
* Drop `decidable_linear_ordered_semiring`, use `linear_ordered_semiring` instead.
* Drop `decidable_linear_ordered_comm_ring`, use `linear_ordered_comm_ring` instead;
* Rename `decidable_linear_ordered_cancel_add_comm_monoid` to `linear_ordered_cancel_add_comm_monoid`.
* Rename `decidable_linear_ordered_add_comm_group` to `linear_ordered_add_comm_group`.
* Modify some lemmas to use weaker typeclass assumptions.
* Add more lemmas about `ordering.compares`, including `linear_order_of_compares` which
  constructs a `linear_order` instance from `cmp` function.

### [2020-10-27 01:56:15](https://github.com/leanprover-community/mathlib/commit/69db7a3)
chore(scripts): update nolints.txt ([#4797](https://github.com/leanprover-community/mathlib/pull/4797))
I am happy to remove some nolints for you!

### [2020-10-26 23:04:21](https://github.com/leanprover-community/mathlib/commit/6e2980c)
chore(*): reflow some long lines ([#4794](https://github.com/leanprover-community/mathlib/pull/4794))

### [2020-10-26 23:04:19](https://github.com/leanprover-community/mathlib/commit/8746f08)
feat(data/equiv/basic): equiv.set.powerset ([#4790](https://github.com/leanprover-community/mathlib/pull/4790))

### [2020-10-26 21:30:45](https://github.com/leanprover-community/mathlib/commit/c76c3c5)
feat(degree/basic.lean): degree_lt_iff_coeff_zero ([#4792](https://github.com/leanprover-community/mathlib/pull/4792))
Changes to degree/basic.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)

### [2020-10-26 18:39:32](https://github.com/leanprover-community/mathlib/commit/95b3add)
fix(tactic/derive_fintype): add support for props ([#4777](https://github.com/leanprover-community/mathlib/pull/4777))
This adds support for propositional arguments in inductive constructors.
It was previously not handled, and while it *almost* works without
change, we have to use `Sigma' (a:A) (b:B) (c:C), unit` to tuple up the
arguments instead of `Sigma' (a:A) (b:B), C` because it would cause problems
in the unary case where there is only one propositional field.

### [2020-10-26 18:39:30](https://github.com/leanprover-community/mathlib/commit/9428598)
feat(tactic/rcases): add `rintro (x y : t)` support ([#4722](https://github.com/leanprover-community/mathlib/pull/4722))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rintros/near/213999254

### [2020-10-26 18:39:29](https://github.com/leanprover-community/mathlib/commit/877a20e)
feat(ring_theory/finiteness): some finiteness notions in commutative algebra ([#4634](https://github.com/leanprover-community/mathlib/pull/4634))

### [2020-10-26 18:39:27](https://github.com/leanprover-community/mathlib/commit/61c095f)
chore(algebra/module,linear_algebra): split off a `linear_map` file ([#4476](https://github.com/leanprover-community/mathlib/pull/4476))
In order to make `algebra/module/basic.lean` and `linear_algebra/basic.lean` a bit more manageable, move the basic facts about `linear_map`s and `linear_equiv`s into a separate file. `linear_algebra/basic.lean` still needs to be split a bit more.

### [2020-10-26 16:13:21](https://github.com/leanprover-community/mathlib/commit/83edb50)
feat(simps): improve error messages ([#4653](https://github.com/leanprover-community/mathlib/pull/4653))
If a custom projection has a different type than the expected projection, then it will show a more specific error message.
Also reflow most long lines
Also add some tests

### [2020-10-26 14:18:36](https://github.com/leanprover-community/mathlib/commit/ba5594a)
feat(data/dfinsupp): Add missing to_additive lemmas ([#4788](https://github.com/leanprover-community/mathlib/pull/4788))

### [2020-10-26 13:22:48](https://github.com/leanprover-community/mathlib/commit/2e90c60)
feat(ring_theory/witt_vector/basic): verifying the ring axioms ([#4694](https://github.com/leanprover-community/mathlib/pull/4694))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-26 05:21:12](https://github.com/leanprover-community/mathlib/commit/7be82f9)
chore(scripts): update nolints.txt ([#4785](https://github.com/leanprover-community/mathlib/pull/4785))
I am happy to remove some nolints for you!

### [2020-10-26 05:21:10](https://github.com/leanprover-community/mathlib/commit/b2b39ed)
chore(order/galois_connection): define `with_bot.gi_get_or_else_bot` ([#4781](https://github.com/leanprover-community/mathlib/pull/4781))
This Galois insertion can be used to golf proofs about
`polynomial.degree` vs `polynomial.nat_degree`.

### [2020-10-26 05:21:08](https://github.com/leanprover-community/mathlib/commit/121c9a4)
chore(algebra/group/hom): use `coe_comp` in `simp` lemmas ([#4780](https://github.com/leanprover-community/mathlib/pull/4780))
This way Lean will simplify `⇑(f.comp g)` even if it is not applied to
an element.

### [2020-10-26 05:21:06](https://github.com/leanprover-community/mathlib/commit/6e4fe98)
chore(data/polynomial/{degree/basic, eval}): Some trivial lemmas about polynomials ([#4768](https://github.com/leanprover-community/mathlib/pull/4768))
I have added the lemma `supp_card_le_succ_nat_degree` about the cardinality of the support of a polynomial and removed the useless commutativity assumptio in `map_sum` and `map_neg`.

### [2020-10-26 04:25:05](https://github.com/leanprover-community/mathlib/commit/4036212)
feat(algebra/big_operators/nat_antidiagonal): a few more lemmas ([#4783](https://github.com/leanprover-community/mathlib/pull/4783))

### [2020-10-25 21:53:20](https://github.com/leanprover-community/mathlib/commit/a9d3ce8)
feat(analysis/normed_space/add_torsor): continuity of `vadd`/`vsub` ([#4751](https://github.com/leanprover-community/mathlib/pull/4751))
Prove that `vadd`/`vsub` are Lipschitz continuous, hence uniform
continuous and continuous.

### [2020-10-25 18:29:34](https://github.com/leanprover-community/mathlib/commit/e7a4b12)
fix(tactic/core): fix infinite loop in emit_code_here ([#4746](https://github.com/leanprover-community/mathlib/pull/4746))
Previously `emit_code_here "\n"` would go into an infinite loop because the `command_like` parser consumes nothing, but the string is not yet empty. Now we recurse on the length of the string to ensure termination.

### [2020-10-25 16:45:20](https://github.com/leanprover-community/mathlib/commit/151f0dd)
chore(linear_algebra/tensor_product): missing simp lemmas ([#4769](https://github.com/leanprover-community/mathlib/pull/4769))

### [2020-10-25 16:45:18](https://github.com/leanprover-community/mathlib/commit/69f550c)
chore(ring_theory/unique_factorization_domain): fix some lemma names ([#4765](https://github.com/leanprover-community/mathlib/pull/4765))
Fixes names of some lemmas that were erroneously renamed with find-and-replace
Changes some constructor names to use dot notation
Names replaced:
`exists_prime_of_factor` -> `exists_prime_factors`
`wf_dvd_monoid_of_exists_prime_of_factor` -> `wf_dvd_monoid.of_exists_prime_factors`
`irreducible_iff_prime_of_exists_prime_of_factor` -> `irreducible_iff_prime_of_exists_prime_factors`
`unique_factorization_monoid_of_exists_prime_of_factor` -> `unique_factorization_monoid.of_exists_prime_factors`
`unique_factorization_monoid_iff_exists_prime_of_factor` -> `unique_factorization_monoid.iff_exists_prime_factors`
`irreducible_iff_prime_of_exists_unique_irreducible_of_factor` -> `irreducible_iff_prime_of_exists_unique_irreducible_factors`
`unique_factorization_monoid.of_exists_unique_irreducible_of_factor` -> `unique_factorization_monoid.of_exists_unique_irreducible_factors`
`no_factors_of_no_prime_of_factor` -> `no_factors_of_no_prime_factors`
`dvd_of_dvd_mul_left_of_no_prime_of_factor` -> `dvd_of_dvd_mul_left_of_no_prime_factors`
`dvd_of_dvd_mul_right_of_no_prime_of_factor` -> `dvd_of_dvd_mul_right_of_no_prime_factors`

### [2020-10-25 14:56:50](https://github.com/leanprover-community/mathlib/commit/14cff9a)
chore(algebra/group/pi): add `pi.has_div` ([#4776](https://github.com/leanprover-community/mathlib/pull/4776))
Motivated by [#4646](https://github.com/leanprover-community/mathlib/pull/4646)

### [2020-10-24 22:07:59](https://github.com/leanprover-community/mathlib/commit/f056468)
chore(analysis/normed_space): add 2 `@[simp]` attrs ([#4775](https://github.com/leanprover-community/mathlib/pull/4775))
Add `@[simp]` to `norm_pos_iff` and `norm_le_zero_iff`

### [2020-10-24 11:48:11](https://github.com/leanprover-community/mathlib/commit/cae77dc)
feat(algebra/direct_sum): Fix two todos about generalizing over unique types ([#4764](https://github.com/leanprover-community/mathlib/pull/4764))
Also promotes `id` to a `≃+`, and prefers coercion over direct use of `subtype.val`.

### [2020-10-24 05:36:36](https://github.com/leanprover-community/mathlib/commit/de6a9d4)
feat(ring_theory/polynomial/content): `gcd_monoid` instance on polynomials over gcd domain ([#4760](https://github.com/leanprover-community/mathlib/pull/4760))
Refactors `ring_theory/polynomial/content` a bit to introduce `prim_part`
Provides a `gcd_monoid` instance on polynomials over a gcd domain

### [2020-10-24 05:36:34](https://github.com/leanprover-community/mathlib/commit/570c293)
feat(data/polynomial/ring_division): Two easy lemmas about polynomials ([#4742](https://github.com/leanprover-community/mathlib/pull/4742))
Two easy lemmas from my previous, now splitted, PR.

### [2020-10-24 05:36:32](https://github.com/leanprover-community/mathlib/commit/b9a94d6)
feat(linear_algebra/nonsingular_inverse): add stronger form of Cramer's rule ([#4737](https://github.com/leanprover-community/mathlib/pull/4737))
Also renaming `cramer_transpose_eq_adjugate_mul_vec` --> `cramer_eq_adjugate_mul_vec` after the transpose was rendered redundant.

### [2020-10-24 03:10:11](https://github.com/leanprover-community/mathlib/commit/2987a49)
fix(tactic/core): use eval_pexpr in run_parser_cmd ([#4761](https://github.com/leanprover-community/mathlib/pull/4761))
Continuation of [#4745](https://github.com/leanprover-community/mathlib/pull/4745), see https://github.com/leanprover-community/mathlib/pull/4745#discussion_r510771137

### [2020-10-24 01:02:28](https://github.com/leanprover-community/mathlib/commit/8255507)
feat(data/pnat/basic): Add strong induction on pnat ([#4736](https://github.com/leanprover-community/mathlib/pull/4736))
I added strong induction on `pnat`. (This was from a previous PR that I am splitting.)

### [2020-10-23 22:12:51](https://github.com/leanprover-community/mathlib/commit/c141eed)
feat(data/list/basic): Add prod_reverse_noncomm ([#4757](https://github.com/leanprover-community/mathlib/pull/4757))

### [2020-10-23 22:12:50](https://github.com/leanprover-community/mathlib/commit/4ec88db)
feat(algebra/direct_sum): Bundle the homomorphisms ([#4754](https://github.com/leanprover-community/mathlib/pull/4754))

### [2020-10-23 22:12:48](https://github.com/leanprover-community/mathlib/commit/aa59039)
feat(category_theory): presheaf is colimit of representables ([#4401](https://github.com/leanprover-community/mathlib/pull/4401))
Show every presheaf (on a small category) is a colimit of representables, and some related results. 
Suggestions for better names more than welcome.

### [2020-10-23 20:04:40](https://github.com/leanprover-community/mathlib/commit/5afeb9b)
chore(*): a few more type-specific ext lemmas ([#4741](https://github.com/leanprover-community/mathlib/pull/4741))
* mark lemmas about homs from `multiplicative nat` and `multiplicative int` as `@[ext]`;
* add a special case lemma about linear maps from the base semiring;
* ext lemmas for ring homs from `(add_)monoid_algebra`;
* ext lemmas for multiplicative homs from `multiplicative (α →₀ M)`;
* make sure that Lean can chain ext lemmas by using hom equalities in lemmas about `finsupp`/`(add_)monoid_algebra`.

### [2020-10-23 17:42:40](https://github.com/leanprover-community/mathlib/commit/0bbf3e2)
fix(deprecated/group): Correct the name of `is_add_group_hom has_neg.neg` ([#4755](https://github.com/leanprover-community/mathlib/pull/4755))
Rename `inv.is_add_group_hom` to `neg.is_add_group_hom`.

### [2020-10-23 13:03:43](https://github.com/leanprover-community/mathlib/commit/5886961)
feat(data/{nat,list}/basic): Add some trivial lemmas ([#4738](https://github.com/leanprover-community/mathlib/pull/4738))

### [2020-10-23 10:15:32](https://github.com/leanprover-community/mathlib/commit/b651c6f)
feat(tactic/core): add `run_parser` user command ([#4745](https://github.com/leanprover-community/mathlib/pull/4745))
Allows for writing things like:
```lean
import tactic.core
run_parser emit_code_here "def foo := 1"
```
Relevant Zulip conversation: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universes/near/214229509

### [2020-10-23 10:15:30](https://github.com/leanprover-community/mathlib/commit/fb4aee0)
fix(deprecated/*): remove instances ([#4735](https://github.com/leanprover-community/mathlib/pull/4735))
Remove all instances constructing structures from `is_*` predicates, like for example:
```lean
instance subset.ring {S : set R} [is_subring S] : ring S :=
...
```
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>

### [2020-10-23 10:15:28](https://github.com/leanprover-community/mathlib/commit/70b14ce)
refactor(*): use is_scalar_tower instead of restrict_scalars ([#4733](https://github.com/leanprover-community/mathlib/pull/4733))
- rename `semimodule.restrict_scalars` to `restrict_scalars`
- rename `restrict_scalars` to `subspace.restrict_scalars`
- use `is_scalar_tower` wherever possible
- add warnings to docstrings about `restrict_scalars` to encourage `is_scalar_tower` instead

### [2020-10-23 10:15:26](https://github.com/leanprover-community/mathlib/commit/82b4843)
feat(ring_theory/roots_of_unity): Roots of unity as union of primitive roots ([#4644](https://github.com/leanprover-community/mathlib/pull/4644))
I have added some lemmas about roots of unity, especially `root_of_unity_eq_uniun_prim` that says that, if there is a primitive `n`-th root of unity in `R`, then the set of `n`-th roots of unity is equal to the union of `primitive_roots i R` for `i | n`.
I will use this lemma in to develop the theory of cyclotomic polynomials.

### [2020-10-23 10:15:24](https://github.com/leanprover-community/mathlib/commit/278a14b)
feat(analysis/p_series): prove the p-series convergence test ([#4360](https://github.com/leanprover-community/mathlib/pull/4360))

### [2020-10-23 10:15:21](https://github.com/leanprover-community/mathlib/commit/04b5572)
feat(ring_theory/witt_vector/defs): type of witt vectors + ring operations ([#4332](https://github.com/leanprover-community/mathlib/pull/4332))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-23 07:42:45](https://github.com/leanprover-community/mathlib/commit/9e4ef85)
feat(linear_algebra/affine_space): define `affine_equiv.mk'` ([#4750](https://github.com/leanprover-community/mathlib/pull/4750))
Similarly to `affine_map.mk'`, this constructor checks that the map
agrees with its linear part only for one base point.

### [2020-10-23 07:42:43](https://github.com/leanprover-community/mathlib/commit/468c01c)
chore(topology/*): add two missing simp coe lemmas ([#4748](https://github.com/leanprover-community/mathlib/pull/4748))

### [2020-10-23 07:42:40](https://github.com/leanprover-community/mathlib/commit/458c833)
chore(algebra/group/basic): Mark inv_involutive simp ([#4744](https://github.com/leanprover-community/mathlib/pull/4744))
This means expressions like `has_inv.inv ∘ has_inv.inv` can be simplified

### [2020-10-23 05:47:36](https://github.com/leanprover-community/mathlib/commit/bb52355)
feat(linear_algebra/basic): define `linear_equiv.neg` ([#4749](https://github.com/leanprover-community/mathlib/pull/4749))
Also weaken requirements for `has_neg (M →ₗ[R] M₂)` from
`[add_comm_group M]` `[add_comm_group M₂]` to `[add_comm_monoid M]`
`[add_comm_group M₂]`.

### [2020-10-23 05:47:34](https://github.com/leanprover-community/mathlib/commit/dc4ad81)
refactor(*): lmul is an algebra hom ([#4724](https://github.com/leanprover-community/mathlib/pull/4724))
also, make some arguments implicit, and add simp lemmas

### [2020-10-23 05:47:32](https://github.com/leanprover-community/mathlib/commit/ff711a3)
feat(measure_theory/measure_space): Added lemmas for commuting restrict for outer measures and measures ([#4673](https://github.com/leanprover-community/mathlib/pull/4673))
This also adds `of_function_apply` and `Inf_apply` (for `outer_measure`). I had some difficulty getting
these functions to expand (as represented by the length of `Inf_apply`) in a clean way.
I also think `Inf_apply` is instructive in terms of making it clear what the definition of `Inf` is. Once `Inf` is rewritten,
then the large set of operations available for `infi_le` and `le_infi` (and `ennreal.tsum_le_tsum`) can be used.
`measure.restrict_Inf_eq_Inf_restrict` will be helpful in getting more results about the subtraction of measures,
specifically writing down the result of `(a - b)` when `a` is not less than or equal to `b` and `b` is not less than
or equal to `a`.

### [2020-10-23 04:31:09](https://github.com/leanprover-community/mathlib/commit/f279313)
feat(category_theory/yoneda): better simp lemmas for small yoneda ([#4743](https://github.com/leanprover-community/mathlib/pull/4743))
Gives nicer (d)simp lemmas for yoneda_sections_small.

### [2020-10-23 01:10:33](https://github.com/leanprover-community/mathlib/commit/8bd1df5)
chore(scripts): update nolints.txt ([#4747](https://github.com/leanprover-community/mathlib/pull/4747))
I am happy to remove some nolints for you!

### [2020-10-22 17:33:36](https://github.com/leanprover-community/mathlib/commit/de12036)
chore(data/polynomial): remove monomial_one_eq_X_pow ([#4734](https://github.com/leanprover-community/mathlib/pull/4734))
monomial_one_eq_X_pow was a duplicate of X_pow_eq_monomial

### [2020-10-22 14:57:55](https://github.com/leanprover-community/mathlib/commit/6eb5564)
chore(data/equiv/basic): Add a simp lemma perm.coe_mul ([#4723](https://github.com/leanprover-community/mathlib/pull/4723))
This mirrors `equiv.coe_trans`

### [2020-10-22 07:48:25](https://github.com/leanprover-community/mathlib/commit/add5096)
chore(*): 3 unrelated small changes ([#4732](https://github.com/leanprover-community/mathlib/pull/4732))
* fix universe levels in `equiv.set.compl`: by default Lean uses some
`max` universes both for `α` and `β`, and it backfires when one tries
to apply it.
* add `nat.mul_factorial_pred`;
* add instance `fixed_points.decidable`.
Part of [#4731](https://github.com/leanprover-community/mathlib/pull/4731)

### [2020-10-22 07:48:23](https://github.com/leanprover-community/mathlib/commit/aba31c9)
feat(algebra/monoid_algebra): define a non-commutative version of `lift` ([#4725](https://github.com/leanprover-community/mathlib/pull/4725))
* [X] define `monoid_algebra.lift_c` and `add_monoid_algebra.lift_nc` to be generalizations of `(mv_)polynomial.eval₂` to `(add_)monoid_algebra`s.
* [X] use `to_additive` in many proofs about `add_monoid_algebra`;
* [X] define `finsupp.nontrivial`, use it for `(add_)monoid_algebra.nontrivial`;
* [X] copy more lemmas about `lift` from `monoid_algebra` to `add_monoid_algebra`;
* [X] use `@[ext]` on more powerful type-specific lemmas;
* [x] fix docstrings of `(add_)monoid_algebra.lift₂`;
* [x] fix compile failures.

### [2020-10-22 07:48:21](https://github.com/leanprover-community/mathlib/commit/fb5ef2b)
feat(linear_algebra/nonsingular_inverse): state Cramer's rule explicitly ([#4700](https://github.com/leanprover-community/mathlib/pull/4700))
Mostly so that we can add an entry to the Freek 100.

### [2020-10-22 06:38:42](https://github.com/leanprover-community/mathlib/commit/03f0285)
refactor(algebra/add_torsor): define pointwise `-ᵥ` and `+ᵥ` on sets ([#4710](https://github.com/leanprover-community/mathlib/pull/4710))
This seems more natural than `vsub_set` to me.

### [2020-10-22 05:15:46](https://github.com/leanprover-community/mathlib/commit/4c4d47c)
feat(algebra/gcd_monoid): noncomputably defines `gcd_monoid` structures from partial information ([#4664](https://github.com/leanprover-community/mathlib/pull/4664))
Adds the following 4 noncomputable functions which define `gcd_monoid` instances.
`gcd_monoid_of_gcd` takes as input a `gcd` function and a few of its properties
`gcd_monoid_of_lcm` takes as input a `lcm` function and a few of its properties
`gcd_monoid_of_exists_gcd` takes as input the prop that every two elements have a `gcd`
`gcd_monoid_of_exists_lcm` takes as input the prop that every two elements have an `lcm`

### [2020-10-22 01:14:08](https://github.com/leanprover-community/mathlib/commit/fca876e)
chore(scripts): update nolints.txt ([#4730](https://github.com/leanprover-community/mathlib/pull/4730))
I am happy to remove some nolints for you!

### [2020-10-21 15:31:43](https://github.com/leanprover-community/mathlib/commit/df45002)
feat(archive): formalize compiler correctness by McCarthy and Painter ([#4702](https://github.com/leanprover-community/mathlib/pull/4702))
Add a formalization of the correctness of a compiler from arithmetic expressions to machine language described by McCarthy and Painter, which is considered the first proof of compiler correctness.

### [2020-10-21 15:31:40](https://github.com/leanprover-community/mathlib/commit/1b4e769)
feat(linear_algebra/affine_space): define `affine_equiv` ([#2909](https://github.com/leanprover-community/mathlib/pull/2909))
Define
* [X] `affine_equiv` to be an invertible affine map (e.g., extend both `affine_map` and `equiv`);
* [X] conversion to `linear_equiv`;
* [X] `group` structure on affine automorphisms;
* [X] prove standard lemmas for equivalences (`apply_symm_apply`, `symm_apply_eq` etc).
API changes
* make `G` implicit in `equiv.vadd_const`.

### [2020-10-21 13:35:00](https://github.com/leanprover-community/mathlib/commit/75316ca)
chore(linear_algebra/basic): a few simp lemmas ([#4727](https://github.com/leanprover-community/mathlib/pull/4727))
* add `submodule.nonempty`;
* add `@[simp]` to `submodule.map_id`;
* add `submodule.neg_coe`, `protected submodule.map_neg`, and `submodule.span_neg`.

### [2020-10-21 01:39:35](https://github.com/leanprover-community/mathlib/commit/01c1e6f)
chore(scripts): update nolints.txt ([#4721](https://github.com/leanprover-community/mathlib/pull/4721))
I am happy to remove some nolints for you!

### [2020-10-21 01:39:33](https://github.com/leanprover-community/mathlib/commit/3a860cc)
fixup(category_theory/sites): add arrow sets that aren't sieves  ([#4703](https://github.com/leanprover-community/mathlib/pull/4703))
Broken off from [#4648](https://github.com/leanprover-community/mathlib/pull/4648).
- I realised that by creating a type `arrows_with_codomain` I can avoid using `set (over X)` entirely (the bit I was missing was that `derive complete_lattice` works on the new type even though it wasn't inferred on the pi-type), so I changed sieves to use that instead. 
- I added constructors for special arrow sets. The definitions of `singleton_arrow` and `pullback_arrows` look a bit dubious because of the equality and `eq_to_hom` stuff; I don't love that either so if there's a suggestion on how to achieve the same things (in particular stating (1) and (3) from: https://stacks.math.columbia.edu/tag/00VH, as well as a complete lattice structure) I'd be happy to consider.
- I added a coercion so we can write `S f` instead of `S.arrows f` for sieves.

### [2020-10-21 00:42:57](https://github.com/leanprover-community/mathlib/commit/857cbd5)
chore(category_theory/limits/preserves): split up files and remove redundant defs ([#4717](https://github.com/leanprover-community/mathlib/pull/4717))
Broken off from [#4163](https://github.com/leanprover-community/mathlib/pull/4163) and [#4716](https://github.com/leanprover-community/mathlib/pull/4716).
While the diff of this PR is quite big, it actually doesn't do very much: 
- I removed the definitions of `preserves_(co)limits_iso` from `preserves/basic`, since there's already a version in `preserves/shapes` which has lemmas about it. (I didn't keep them in `preserves/basic` since that file is already getting quite big, so I chose to instead put them into the smaller file.
- I split up `preserves/shapes` into two files: `preserves/limits` and `preserves/shapes`. From my other PRs my plan is for `shapes` to contain isomorphisms and constructions for special shapes, eg `fan.mk` and `fork`s, some of which aren't already present, and `limits` to have things for the general case. In this PR I don't change the situation for special shapes (other than simplifying some proofs), other than moving it into a separate file for clarity.

### [2020-10-20 13:15:11](https://github.com/leanprover-community/mathlib/commit/8489972)
feat(data/complex/module): ![1, I] is a basis of C over R ([#4713](https://github.com/leanprover-community/mathlib/pull/4713))

### [2020-10-20 10:23:27](https://github.com/leanprover-community/mathlib/commit/cf551ee)
chore(*): review some lemmas about injectivity of coercions ([#4711](https://github.com/leanprover-community/mathlib/pull/4711))
API changes:
* rename `linear_map.coe_fn_congr` to `protected
  linear_map.congr_arg`;
* rename `linear_map.lcongr_fun` to `protected linear_map.congr_fun`;
* rename `enorm.coe_fn_injective` to `enorm.injective_coe_fn`, add
  `enorm.coe_inj`;
* rename `equiv.coe_fn_injective` to `equiv.injective_coe_fn`,
  reformulate in terms of `function.injective`;
* add `equiv.coe_inj`;
* add `affine_map.injective_coe_fn`, `protected affine_map.congr_arg`,
  and `protected affine_map.congr_fun`;
* rename `linear_equiv.to_equiv_injective` to
  `linear_equiv.injective_to_equiv`, add `linear_equiv.to_equiv_inj`;
* rename `linear_equiv.eq_of_linear_map_eq` to
  `linear_equiv.injective_to_linear_map`, formulate as `injective
  coe`;
* add `linear_equiv.to_linear_map_inj`;
* rename `outer_measure.coe_fn_injective` to
  `outer_measure.injective_coe_fn`;
* rename `rel_iso.to_equiv_injective` to `rel_iso.injective_to_equiv`;
* rename `rel_iso.coe_fn_injective` to `rel_iso.injective_coe_fn`;
* rename `continuous_linear_map.coe_fn_injective` to
  `injective_coe_fn`.

### [2020-10-20 10:23:25](https://github.com/leanprover-community/mathlib/commit/5d52ea4)
chore(.gitignore): gitignore for emacs temp files ([#4699](https://github.com/leanprover-community/mathlib/pull/4699))
Emacs backup files end in `~`, and you don't want them in the repo. Just makes things mildly easier for emacs users if that pattern is in the gitignore.

### [2020-10-20 08:10:53](https://github.com/leanprover-community/mathlib/commit/8131349)
fix(tactic/norm_num): remove one_div from simp set ([#4705](https://github.com/leanprover-community/mathlib/pull/4705))
fixes [#4701](https://github.com/leanprover-community/mathlib/pull/4701)

### [2020-10-20 08:10:51](https://github.com/leanprover-community/mathlib/commit/617e829)
feat(linear_algebra/affine_space/ordered): define `slope` ([#4669](https://github.com/leanprover-community/mathlib/pull/4669))
* Review API of `ordered_semimodule`:
  - replace `lt_of_smul_lt_smul_of_nonneg` with `lt_of_smul_lt_smul_of_pos`;
    it's equivalent but is easier to prove;
  - add more lemmas;
  - add a constructor for the special case of an ordered semimodule over
	a linearly ordered field; in this case it suffices to verify only
	`a < b → 0 < c → c • a ≤ c • b`;
  - use the new constructor in `analysis/convex/cone`;
* Define `units.smul_perm_hom`, reroute `mul_action.to_perm` through it;
* Add a few more lemmas unfolding `affine_map.line_map` in special cases;
* Define `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` and prove a handful
  of monotonicity properties.

### [2020-10-20 05:38:10](https://github.com/leanprover-community/mathlib/commit/b46190f)
chore(data/finsupp): minor review ([#4712](https://github.com/leanprover-community/mathlib/pull/4712))
* add a few lemmas about injectivity of `coe_fn` etc;
* simplify definition of `finsupp.on_finset`;
* replace the proof of `support_on_finset` by `rfl`;
* make `finsupp.mem_support_on_finset` a `simp` lemma.

### [2020-10-20 05:38:08](https://github.com/leanprover-community/mathlib/commit/288802b)
chore(data/polynomial): slightly generalize `map_eq_zero` and `map_ne_zero` ([#4708](https://github.com/leanprover-community/mathlib/pull/4708))
We don't need the codomain to be a field.

### [2020-10-20 05:38:07](https://github.com/leanprover-community/mathlib/commit/21415c8)
chore(topology/algebra/ordered): drop section vars, golf 2 proofs ([#4706](https://github.com/leanprover-community/mathlib/pull/4706))
* Explicitly specify explicit arguments instead of using section
  variables;
* Add `continuous_min` and `continuous_max`;
* Use them for `tendsto.min` and `tendsto.max`

### [2020-10-20 05:38:04](https://github.com/leanprover-community/mathlib/commit/0cf8a98)
chore(data/set): a few more lemmas about `image2` ([#4695](https://github.com/leanprover-community/mathlib/pull/4695))
Also add `@[simp]` to `set.image2_singleton_left` and `set.image2_singleton_rigt`.

### [2020-10-20 05:38:01](https://github.com/leanprover-community/mathlib/commit/050b5a1)
feat(data/real/pi): Leibniz's series for pi ([#4228](https://github.com/leanprover-community/mathlib/pull/4228))
Freek No. 26 
<!-- put comments you want to keep out of the PR commit here -->

### [2020-10-20 03:17:38](https://github.com/leanprover-community/mathlib/commit/cd884eb)
feat(measure_theory): finite_spanning_sets_in ([#4668](https://github.com/leanprover-community/mathlib/pull/4668))
* We define a new Type-valued structure `finite_spanning_sets_in` which consists of a countable sequence of sets that span the type, have finite measure, and live in a specified collection of sets, 
* `sigma_finite` is redefined in terms of `finite_spanning_sets_in`
* One of the ext lemmas is now conveniently formulated in terms of `finite_spanning_sets_in`
* `finite_spanning_sets_in` is also used to remove a little bit of code duplication in `prod` (which occurred because `sigma_finite` was a `Prop`, and forgot the actual construction)
* Define a predicate `is_countably_spanning` which states that a collection of sets has a countable spanning subset. This is useful for one particular lemma in `prod`.
* Generalize some lemmas about products in the case that the σ-algebras are generated by a collection of sets. This can be used to reason about iterated products.
* Prove `prod_assoc_prod`.
* Cleanup in `measurable_space` and somewhat in `measure_space`.
* Rename `measurable.sum_rec -> measurable.sum_elim` (and give a different but definitionally equal statement)

### [2020-10-20 01:14:13](https://github.com/leanprover-community/mathlib/commit/9755ae3)
chore(scripts): update nolints.txt ([#4704](https://github.com/leanprover-community/mathlib/pull/4704))
I am happy to remove some nolints for you!

### [2020-10-19 22:45:26](https://github.com/leanprover-community/mathlib/commit/accc50e)
chore(data/finsupp): `to_additive` on `on_finset_sum` ([#4698](https://github.com/leanprover-community/mathlib/pull/4698))

### [2020-10-19 22:45:23](https://github.com/leanprover-community/mathlib/commit/706b484)
chore(data/multiset): add a few lemmas ([#4697](https://github.com/leanprover-community/mathlib/pull/4697))

### [2020-10-19 22:45:21](https://github.com/leanprover-community/mathlib/commit/b707e98)
refactor(ring_theory/witt_vector): move lemmas to separate file ([#4693](https://github.com/leanprover-community/mathlib/pull/4693))
This new file has almost no module docstring.
This is on purpose, it is a refactor PR.
A follow-up PR will add a module docstring and more definitions.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-19 22:45:19](https://github.com/leanprover-community/mathlib/commit/b300302)
feat(algebra/free_algebra): Add a ring instance ([#4692](https://github.com/leanprover-community/mathlib/pull/4692))
This also adds a ring instance to `tensor_algebra`.
The approach here does not work for `exterior_algebra` and `clifford_algebra`, and produces weird errors.
Those will be easier to investigate when their foundations are in mathlib.

### [2020-10-19 22:45:17](https://github.com/leanprover-community/mathlib/commit/cc6594a)
doc(algebra/algebra/basic): Fixes some documentation about `R`-algebras ([#4689](https://github.com/leanprover-community/mathlib/pull/4689))
See the associated zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/The.20Type.20of.20R-algebras/near/213722713

### [2020-10-19 22:45:15](https://github.com/leanprover-community/mathlib/commit/86d65f8)
chore(topology/instances/ennreal): prove `nnreal.not_summable_iff_tendsto_nat_at_top` ([#4670](https://github.com/leanprover-community/mathlib/pull/4670))
* use `ℝ≥0` notation in `data/real/ennreal`;
* add `ennreal.forall_ne_top`, `ennreal.exists_ne_top`,
  `ennreal.ne_top_equiv_nnreal`, `ennreal.cinfi_ne_top`,
  `ennreal.infi_ne_top`, `ennreal.csupr_ne_top`, `ennreal.sup_ne_top`,
  `ennreal.supr_ennreal`;
* add `nnreal.injective_coe`, add `@[simp, norm_cast]` to
  `nnreal.tendsto_coe`, and add `nnreal.tendsto_coe_at_top`; move
  `nnreal.infi_real_pos_eq_infi_nnreal_pos` from `ennreal` to `nnreal`;
* use `function.injective` instead of an unfolded definition in `filter.comap_map`;
* add `ennreal.nhds_top'`, `ennreal.tendsto_nhds_top_iff_nnreal`,
  `ennreal.tendsto_nhds_top_iff_nat`;
  
* upgrade `ennreal.tendsto_coe_nnreal_nhds_top` to an `iff`, rename to
  `ennreal.tendsto_coe_nhds_top`;
* `nnreal.has_sum_iff_tendsto_nat` now takes  `r` as an implicit argument;
* add `nnreal.not_summable_iff_tendsto_nat_at_top` and
  `not_summable_iff_tendsto_nat_at_top_of_nonneg`.

### [2020-10-19 22:45:12](https://github.com/leanprover-community/mathlib/commit/3019581)
feat({field,ring}_theory/adjoin): generalize `induction_on_adjoin` ([#4647](https://github.com/leanprover-community/mathlib/pull/4647))
We can prove `induction_on_adjoin` for both `algebra.adjoin` and `intermediate_field.adjoin` in a very similar way, if we add a couple of small lemmas. The extra lemmas I introduced for `algebra.adjoin` shorten the proof of `intermediate_field.adjoin` noticeably.

### [2020-10-19 22:45:10](https://github.com/leanprover-community/mathlib/commit/006b2e7)
feat(data/polynomial/reverse): define `reverse f`, prove that `reverse` is a multiplicative monoid homomorphism ([#4598](https://github.com/leanprover-community/mathlib/pull/4598))

### [2020-10-19 22:45:07](https://github.com/leanprover-community/mathlib/commit/0c70cf3)
feat(tactic/unify_equations): add unify_equations tactic ([#4515](https://github.com/leanprover-community/mathlib/pull/4515))
`unify_equations` is a first-order unification tactic for propositional
equalities. It implements the algorithm that `cases` uses to simplify
indices of inductive types, with one extension: `unify_equations` can
derive a contradiction from 'cyclic' equations like `n = n + 1`.
`unify_equations` is unlikely to be particularly useful on its own, but
I'll use it as part of my new `induction` tactic.

### [2020-10-19 22:45:05](https://github.com/leanprover-community/mathlib/commit/a249c9a)
feat(archive/imo): formalize IMO 1998 problem 2 ([#4502](https://github.com/leanprover-community/mathlib/pull/4502))

### [2020-10-19 22:45:03](https://github.com/leanprover-community/mathlib/commit/5065471)
feat(data/monoid_algebra): add missing has_coe_to_fun ([#4315](https://github.com/leanprover-community/mathlib/pull/4315))
Also does the same for the additive version `semimodule k (add_monoid_algebra k G)`.

### [2020-10-19 20:01:36](https://github.com/leanprover-community/mathlib/commit/0523b61)
chore(logic/function): `simp`lify applications of `(un)curry` ([#4696](https://github.com/leanprover-community/mathlib/pull/4696))

### [2020-10-19 15:37:07-04:00](https://github.com/leanprover-community/mathlib/commit/a1f1770)
Revert "chore(data/multiset): add a few lemmas"
This reverts commit 45caa4f392fe4f7622fef576cf3811b9ff6fd307.

### [2020-10-19 15:30:42-04:00](https://github.com/leanprover-community/mathlib/commit/45caa4f)
chore(data/multiset): add a few lemmas

### [2020-10-19 15:11:45](https://github.com/leanprover-community/mathlib/commit/cacc297)
fix(tactic/norm_num): remove unnecessary argument to rat.cast_zero ([#4682](https://github.com/leanprover-community/mathlib/pull/4682))
See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60norm_num.60.20error.20message).

### [2020-10-19 11:39:07](https://github.com/leanprover-community/mathlib/commit/0f1bc68)
feat(ring_theory/witt_vector/structure_polynomial): examples and basic properties ([#4467](https://github.com/leanprover-community/mathlib/pull/4467))
This is the 4th and final PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-19 11:39:05](https://github.com/leanprover-community/mathlib/commit/4140f78)
feat(algebra/ordered_semiring): relax 0 < 1 to 0 ≤ 1 ([#4363](https://github.com/leanprover-community/mathlib/pull/4363))
Per [discussion](https://github.com/leanprover-community/mathlib/pull/4296#issuecomment-701953077) in [#4296](https://github.com/leanprover-community/mathlib/pull/4296).

### [2020-10-19 10:38:52](https://github.com/leanprover-community/mathlib/commit/ef9d00f)
feat(linear_algebra/matrix): multiplying `is_basis.to_matrix` and `linear_map.to_matrix` ([#4650](https://github.com/leanprover-community/mathlib/pull/4650))
This basically tells us that `is_basis.to_matrix` is indeed a basis change matrix.

### [2020-10-19 10:38:50](https://github.com/leanprover-community/mathlib/commit/47dcecd)
feat(data/complex/exponential): bounds on exp ([#4432](https://github.com/leanprover-community/mathlib/pull/4432))
Define `real.exp_bound` using `complex.exp_bound`.  Deduce numerical
bounds on `exp 1` analogous to those we have for pi.

### [2020-10-19 10:38:48](https://github.com/leanprover-community/mathlib/commit/c38d128)
feat(ring_theory/polynomial/chebyshev): chebyshev polynomials of the first kind ([#4267](https://github.com/leanprover-community/mathlib/pull/4267))
If T_n denotes the n-th Chebyshev polynomial of the first kind, then the
polynomials 2*T_n(X/2) form a Lambda structure on Z[X].
I call these polynomials the lambdashev polynomials, because, as far as I
am aware they don't have a name in the literature.
We show that they commute, and that the p-th polynomial is congruent to X^p
mod p. In other words: a Lambda structure.

### [2020-10-19 07:13:04](https://github.com/leanprover-community/mathlib/commit/f75dbd3)
feat(algebra/*): some simp lemmas, and changing binders ([#4681](https://github.com/leanprover-community/mathlib/pull/4681))

### [2020-10-19 07:13:01](https://github.com/leanprover-community/mathlib/commit/41c227a)
feat(algebra/infinite_sum): make tsum irreducible ([#4679](https://github.com/leanprover-community/mathlib/pull/4679))
See https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/congr'.20is.20slow

### [2020-10-19 07:12:58](https://github.com/leanprover-community/mathlib/commit/7601a7a)
feat(ring_theory/adjoin): adjoin_singleton_one ([#4633](https://github.com/leanprover-community/mathlib/pull/4633))

### [2020-10-19 04:45:06](https://github.com/leanprover-community/mathlib/commit/4b890a2)
feat(*): make int.nonneg irreducible ([#4601](https://github.com/leanprover-community/mathlib/pull/4601))
In [#4474](https://github.com/leanprover-community/mathlib/pull/4474), `int.lt` was made irreducible. We make `int.nonneg` irreducible, which is stronger as `int.lt` is expressed in terms of `int.nonneg`.

### [2020-10-19 01:25:23](https://github.com/leanprover-community/mathlib/commit/d174295)
chore(scripts): update nolints.txt ([#4680](https://github.com/leanprover-community/mathlib/pull/4680))
I am happy to remove some nolints for you!

### [2020-10-19 01:25:21](https://github.com/leanprover-community/mathlib/commit/9d1bbd1)
fix(data/equiv): nolint typo ([#4677](https://github.com/leanprover-community/mathlib/pull/4677))

### [2020-10-19 01:25:19](https://github.com/leanprover-community/mathlib/commit/49bb5dd)
refactor(tactic/norm_num): define prove_ne_zero using prove_ne ([#4626](https://github.com/leanprover-community/mathlib/pull/4626))
This is trickier than it sounds because of a cyclic dependency. As a result we
now have two versions of `prove_ne_zero` and `prove_clear_denom` is
generic over them. One version proves ne using an order relation on the
target, while the other uses `uncast` lemmas to reduce to `rat` and
then uses the first `prove_ne_zero`. (This is why we actually want two versions -
we can't solve this with a large mutual def, because it would
result in an infinite recursion.)

### [2020-10-18 23:06:55](https://github.com/leanprover-community/mathlib/commit/1ac5d82)
fix(logic/nontrivial): change tactic doc entry tag to more common "type class" ([#4676](https://github.com/leanprover-community/mathlib/pull/4676))

### [2020-10-18 21:34:51](https://github.com/leanprover-community/mathlib/commit/61e1111)
chore(linear_algebra/affine_space): introduce notation for `affine_map` ([#4675](https://github.com/leanprover-community/mathlib/pull/4675))

### [2020-10-18 21:34:49](https://github.com/leanprover-community/mathlib/commit/4faf2e2)
chore(order/filter): use implicit arguments in `tendsto_at_top` etc ([#4672](https://github.com/leanprover-community/mathlib/pull/4672))
Also weaken some assumptions from a decidable linear order to a linear order.

### [2020-10-18 21:34:47](https://github.com/leanprover-community/mathlib/commit/392d52c)
chore(order/filter): run `dsimp only [set.mem_set_of_eq]` in `filter_upwards` ([#4671](https://github.com/leanprover-community/mathlib/pull/4671))

### [2020-10-18 19:21:09](https://github.com/leanprover-community/mathlib/commit/93b7e63)
feat(analysis/special_functions/trigonometric): range_{exp,cos,sin} ([#4595](https://github.com/leanprover-community/mathlib/pull/4595))

### [2020-10-18 16:02:22](https://github.com/leanprover-community/mathlib/commit/fee2dfa)
chore(analysis/calculus/fderiv): golf a lemma using new `nontriviality` ([#4584](https://github.com/leanprover-community/mathlib/pull/4584))

### [2020-10-18 09:59:52](https://github.com/leanprover-community/mathlib/commit/e21dc7a)
feat(topology/subset_properties): define `filter.cocompact` ([#4666](https://github.com/leanprover-community/mathlib/pull/4666))
The filter of complements to compact subsets.

### [2020-10-18 05:51:33](https://github.com/leanprover-community/mathlib/commit/cc32876)
chore(analysis/normed_space/basic): add `continuous_at.inv'`, `continuous.div` etc ([#4667](https://github.com/leanprover-community/mathlib/pull/4667))
Also add `continuous_on_(cos/sin)`.

### [2020-10-18 04:29:30](https://github.com/leanprover-community/mathlib/commit/db06b67)
feat(measure_theory/prod): product measures and Fubini's theorem ([#4590](https://github.com/leanprover-community/mathlib/pull/4590))
* Define the product measure of two σ-finite measures.
* Prove Tonelli's theorem.
* Prove Fubini's theorem.

### [2020-10-18 01:46:58](https://github.com/leanprover-community/mathlib/commit/c7782bb)
chore(scripts): update nolints.txt ([#4665](https://github.com/leanprover-community/mathlib/pull/4665))
I am happy to remove some nolints for you!

### [2020-10-18 01:46:56](https://github.com/leanprover-community/mathlib/commit/77dc679)
chore(data/set/intervals): more lemmas ([#4662](https://github.com/leanprover-community/mathlib/pull/4662))

### [2020-10-18 01:46:53](https://github.com/leanprover-community/mathlib/commit/9585210)
chore(order/filter): add a few lemmas ([#4661](https://github.com/leanprover-community/mathlib/pull/4661))

### [2020-10-18 01:46:51](https://github.com/leanprover-community/mathlib/commit/f990838)
chore(data/finsupp/basic): rename type variables ([#4624](https://github.com/leanprover-community/mathlib/pull/4624))
Use `M`, `N`, `P` for types with `has_zero`, `add_monoid`, or
`add_comm_monoid` structure, and `R`, `S` for types with at least
a `semiring` instance.
API change: `single_add_erase` and `erase_add_single` now use explicit arguments.

### [2020-10-18 01:46:49](https://github.com/leanprover-community/mathlib/commit/ebd2b7f)
feat(logic/nontrivial): make `nontriviality` work for more goals ([#4574](https://github.com/leanprover-community/mathlib/pull/4574))
The goal is to make `nontriviality` work for the following goals:
* [x] `nontriviality α` if the goal is `is_open s`, `s : set α`;
* [x] `nontriviality E` if the goal is `is_O f g` or `is_o f g`, where `f : α → E`;
* [x] `nontriviality R` if the goal is `linear_independent R _`;
* [ ] `nontriviality R` if the goal is `is_O f g` or `is_o f g`, where `f : α → E`, `[semimodule R E]`;
  in this case `nontriviality` should add a local instance `semimodule.subsingleton R`.
The last case was never needed in `mathlib`, and there is a workaround: run `nontriviality E`, then deduce `nontrivial R` from `nontrivial E`.
Misc feature:
* [x] make `nontriviality` accept an optional list of additional `simp` lemmas.

### [2020-10-18 01:46:47](https://github.com/leanprover-community/mathlib/commit/b977dba)
fix(solve_by_elim): handle multiple goals with different hypotheses ([#4519](https://github.com/leanprover-community/mathlib/pull/4519))
Previously `solve_by_elim*` would operate on multiple goals (only succeeding if it could close all of them, and performing backtracking across goals), however it would incorrectly only use the local context from the main goal. If other goals had different sets of hypotheses, ... various bad things could happen!
This PR arranges so that `solve_by_elim*` inspects the local context later, so it picks up the correct hypotheses.

### [2020-10-17 23:24:37](https://github.com/leanprover-community/mathlib/commit/13cd192)
feat(measure_theory/measure_space): added sub for measure_theory.measure ([#4639](https://github.com/leanprover-community/mathlib/pull/4639))
This definition is useful for proving the Lebesgue-Radon-Nikodym theorem for non-negative measures.

### [2020-10-17 23:24:35](https://github.com/leanprover-community/mathlib/commit/e83458c)
feat(algebra/group_power): Add mul/add variants of powers_hom and friends ([#4636](https://github.com/leanprover-community/mathlib/pull/4636))

### [2020-10-17 23:24:33](https://github.com/leanprover-community/mathlib/commit/c83c28a)
feat(archive/imo): add IMO 2019 problem 4 ([#4482](https://github.com/leanprover-community/mathlib/pull/4482))

### [2020-10-17 20:50:45](https://github.com/leanprover-community/mathlib/commit/95d33ee)
refactor(algebra/quadratic_discriminant): drop linearity condition; cleanup ([#4656](https://github.com/leanprover-community/mathlib/pull/4656))
Renames:
- `discriminant_le_zero` to `discrim_le_zero`
- `discriminant_lt_zero` to `discrim_lt_zero`

### [2020-10-17 20:50:43](https://github.com/leanprover-community/mathlib/commit/0367467)
chore(group/type_tags): Add missing simp lemmas ([#4651](https://github.com/leanprover-community/mathlib/pull/4651))

### [2020-10-17 20:50:41](https://github.com/leanprover-community/mathlib/commit/0b9afe1)
chore(linear_algebra/affine_space): redefine `line_map`, add `to_affine_subspace` ([#4643](https://github.com/leanprover-community/mathlib/pull/4643))
* now `line_map` takes two points on the line, not a point and a
  direction, update/review lemmas;
* add `submodule.to_affine_subspace`;
* add `affine_map.fst` and `affine_map.snd`;
* prove that an affine map `ℝ → ℝ` sends an unordered interval to an unordered interval.

### [2020-10-17 18:26:05](https://github.com/leanprover-community/mathlib/commit/589ebf5)
chore(algebra/*): add a few `prod.*` instances ([#4659](https://github.com/leanprover-community/mathlib/pull/4659))
* `prod.left_cancel_semigroup`;
* `prod_right_cancel_semigroup`;
* `prod.ordered_cancel_comm_monoid`;
* `ordered_comm_group`.

### [2020-10-17 18:26:02](https://github.com/leanprover-community/mathlib/commit/6e5b6cc)
feat(algebra/gcd_monoid, polynomial/field_division): generalizing `normalization_monoid` on polynomials ([#4655](https://github.com/leanprover-community/mathlib/pull/4655))
Defines a `normalization_monoid` instance on any `comm_group_with_zero`, including fields
Defines a `normalization_monoid` instance on `polynomial R` when `R` has a `normalization_monoid` instance

### [2020-10-17 18:26:00](https://github.com/leanprover-community/mathlib/commit/edddb3b)
feat(finsupp/basic): Add a variant of `prod_map_domain_index` for when f is injective ([#4645](https://github.com/leanprover-community/mathlib/pull/4645))
This puts much weaker restrictions on `h`, making this easier to apply in some situations

### [2020-10-17 18:25:58](https://github.com/leanprover-community/mathlib/commit/85eb12d)
feat(algebra/algebra/basic): product of two algebras ([#4632](https://github.com/leanprover-community/mathlib/pull/4632))

### [2020-10-17 18:25:57](https://github.com/leanprover-community/mathlib/commit/82ff1e5)
feat(algebra/algebra/subalgebra): subalgebra.subsingleton ([#4631](https://github.com/leanprover-community/mathlib/pull/4631))

### [2020-10-17 18:25:55](https://github.com/leanprover-community/mathlib/commit/688157f)
feat(ring_theory/polynomial/content): definition of content + proof that it is multiplicative ([#4393](https://github.com/leanprover-community/mathlib/pull/4393))
Defines `polynomial.content` to be the `gcd` of the coefficients of a polynomial
Says a polynomial `is_primitive` if its content is 1
Proves that `(p * q).content = p.content * q.content

### [2020-10-17 16:08:01](https://github.com/leanprover-community/mathlib/commit/b145c36)
feat(archive/imo): variant solution to IMO 1962 problem 4 ([#4640](https://github.com/leanprover-community/mathlib/pull/4640))
Continuation of a discussion at [#4518](https://github.com/leanprover-community/mathlib/pull/4518)

### [2020-10-17 13:41:26](https://github.com/leanprover-community/mathlib/commit/25d8343)
feat(topology/sheaves): an equivalent sheaf condition ([#4538](https://github.com/leanprover-community/mathlib/pull/4538))
Another condition equivalent to the sheaf condition: for every open cover `U`, `F.obj (supr U)` is the limit point of the diagram consisting of all the `F.obj V`, where `V ≤ U i` for some `i`.
This condition is particularly straightforward to state, and makes some proofs easier (however we don't do this here: just prove the equivalence with the "official" definition). It's particularly nice because there is no case splitting (depending on whether you're looking at single or double intersections) when checking the sheaf condition.
This is the statement Lurie uses in Spectral Algebraic Geometry.
Later I may propose that we make this the official definition, but I'll wait to see how it pans out in actual use, first. For now it's just provided as yet another equivalent version of the sheaf condition.

### [2020-10-17 01:11:20](https://github.com/leanprover-community/mathlib/commit/ca2e6f4)
chore(scripts): update nolints.txt ([#4654](https://github.com/leanprover-community/mathlib/pull/4654))
I am happy to remove some nolints for you!

### [2020-10-16 21:43:46](https://github.com/leanprover-community/mathlib/commit/7b9acd9)
chore(measure_theory/*): reflow long lines ([#4642](https://github.com/leanprover-community/mathlib/pull/4642))
Also do some minor golfing.

### [2020-10-16 19:41:32](https://github.com/leanprover-community/mathlib/commit/189e538)
feat(geometry/manifold): stab at diffeomorphisms ([#4351](https://github.com/leanprover-community/mathlib/pull/4351))

### [2020-10-16 18:01:28](https://github.com/leanprover-community/mathlib/commit/86b298f)
feat(category_theory/sites): grothendieck topologies ([#4577](https://github.com/leanprover-community/mathlib/pull/4577))

### [2020-10-16 16:28:29](https://github.com/leanprover-community/mathlib/commit/0d9227f)
feat(category_theory/monad/kleisli): add Kleisli category of a monad ([#4542](https://github.com/leanprover-community/mathlib/pull/4542))
Adds the Kleisli category of a monad, and shows the Kleisli category for a lawful control monad is equivalent to the Kleisli category of its category-theoretic version.
Following discussion at https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/kleisli.20vs.20kleisli.
I'd appreciate suggestions for names more sensible than the ones already there.

### [2020-10-16 07:43:42](https://github.com/leanprover-community/mathlib/commit/f675a00)
chore(set_theory/zfc): split long lines ([#4641](https://github.com/leanprover-community/mathlib/pull/4641))
Also add `Set.subset_def` and rewrite `Set.mem_pair_sep` in tactic mode

### [2020-10-16 05:34:17](https://github.com/leanprover-community/mathlib/commit/1cce606)
feat(analysis/special_functions/trigonometric): some lemmas ([#4638](https://github.com/leanprover-community/mathlib/pull/4638))
The following changes:
- `sin_sub_sin` and friends (sum-to-product lemmas) moved from `trigonometric` to the earlier file `exponential`.  (I think the distinction between the files is that `trigonometric` collects the facts that require either differentiation or the definition `pi`, whereas purely algebraic facts about trigonometry go in `exponential`?  For example the double-angle formula is in `exponential`).
- rewrite proof of `cos_lt_cos_of_nonneg_of_le_pi_div_two` to avoid dependence on `cos_eq_one_iff_of_lt_of_lt` (but not sure if the result is actually simpler, feel free to propose this be reverted)
- some new explicit values of trig functions, `cos (π / 3)` and similar
- correct a series of lemmas in the `complex` namespace that were stated for real arguments (presumably the author copy-pasted but forgot to rewrite)
- lemmas `sin_eq_zero_iff`, `cos_eq_cos_iff`, `sin_eq_sin_iff`

### [2020-10-16 05:34:15](https://github.com/leanprover-community/mathlib/commit/e7b8421)
chore(linear_algebra/finsupp): turn `finsupp.lsum` into `add_equiv` ([#4597](https://github.com/leanprover-community/mathlib/pull/4597))

### [2020-10-16 03:25:42](https://github.com/leanprover-community/mathlib/commit/8280190)
chore(scripts): update nolints.txt ([#4637](https://github.com/leanprover-community/mathlib/pull/4637))
I am happy to remove some nolints for you!

### [2020-10-16 03:25:39](https://github.com/leanprover-community/mathlib/commit/cc14658)
chore(algebra/group_powers): Add missing lemmas ([#4635](https://github.com/leanprover-community/mathlib/pull/4635))
This part of the file defines four equivalences, but goes on to state lemmas about only one of them.
This provides the lemmas for the other three.

### [2020-10-16 00:56:13](https://github.com/leanprover-community/mathlib/commit/dca1393)
feat(data/equiv/basic): add `equiv.set.compl` ([#4630](https://github.com/leanprover-community/mathlib/pull/4630))
Given an equivalence between two sets `e₀ : s ≃ t`, the set of
`e : α ≃ β` that agree with `e₀` on `s` is equivalent to `sᶜ ≃ tᶜ`.
Also add a bunch of lemmas to `data/set/function`; some of them are
used in the definition of `equiv.set.compl`.

### [2020-10-16 00:56:11](https://github.com/leanprover-community/mathlib/commit/b0b61e6)
feat(order/category/omega-complete): omega-complete partial orders form a complete category ([#4397](https://github.com/leanprover-community/mathlib/pull/4397))
as discussed in [#4348](https://github.com/leanprover-community/mathlib/pull/4348).

### [2020-10-15 23:48:19](https://github.com/leanprover-community/mathlib/commit/3e12a7b)
chore(category_theory/limits/binary_products): fixup binary product lemmas ([#4376](https://github.com/leanprover-community/mathlib/pull/4376))
The main changes in here are:
- `prod.map` is now a def, not an abbreviation. I think this is an important change because oftentimes `simp` will reduce it to `lim.map` and then get stuck, which is tough to debug and usually the wrong step to take. Instead, the `prod.map_fst` and `snd` lemmas are proved directly rather than with simp, and these are used to get everything else.
- I added a couple of new simp lemmas and rewrote a few others: the overall guide here is that more things can be proved by `rw` or `simp` *without using ext*. The idea of this is that when you're dealing with a chain of compositions containing product morphisms, it's much nicer to be able to rewrite (or simp) the parts you want rather than needing to do an auxiliary `have` and use `ext` in there, then rewrite using this lemma inside your big chain. In this file at least I managed to get rid of a bunch of uses of `ext` (and also convert `tidy` to `simp`) so I'm pretty sure these changes were positive.
- Moved around some definitions and lemmas. No big changes here, mostly just putting things which work similarly closer.
- Weakened typeclass assumptions: in particular for `prod_comparison`.
- Renamed some `prod_` lemmas to `prod.`, since there used to be a mix between the two; so I've made the usage consistent.
+ dual versions of all the above.

### [2020-10-15 22:31:38](https://github.com/leanprover-community/mathlib/commit/b7d176e)
feat(category_theory/cones): some isomorphisms relating operations ([#4536](https://github.com/leanprover-community/mathlib/pull/4536))

### [2020-10-15 20:34:24](https://github.com/leanprover-community/mathlib/commit/8985e39)
feat(archive/100-theorems-list/70_perfect_numbers): Perfect Number Theorem, Direction 2 ([#4621](https://github.com/leanprover-community/mathlib/pull/4621))
Adds a few extra lemmas about `divisors`, `proper_divisors` and sums of proper divisors
Proves Euler's direction of the Perfect Number theorem, finishing Freek 70

### [2020-10-15 16:29:11](https://github.com/leanprover-community/mathlib/commit/d473517)
chore(algebra/group/hom): add `monoid_hom.eval` ([#4629](https://github.com/leanprover-community/mathlib/pull/4629))

### [2020-10-15 16:29:09](https://github.com/leanprover-community/mathlib/commit/38a5f5d)
chore(data/equiv/mul_add): add `monoid_hom.to_mul_equiv` ([#4628](https://github.com/leanprover-community/mathlib/pull/4628))

### [2020-10-15 16:29:07](https://github.com/leanprover-community/mathlib/commit/46b0528)
refactor(data/polynomial): Move some lemmas to `monoid_algebra` ([#4627](https://github.com/leanprover-community/mathlib/pull/4627))
The `add_monoid_algebra.mul_apply_antidiagonal` lemma is copied verbatim from `monoid_algebra.mul_apply_antidiagonal`.

### [2020-10-15 16:29:05](https://github.com/leanprover-community/mathlib/commit/abaf3c2)
feat(algebra/category/Algebra/basic): Add free/forget adjunction. ([#4620](https://github.com/leanprover-community/mathlib/pull/4620))
This PR adds the usual free/forget adjunction for the category of `R`-algebras.

### [2020-10-15 16:29:03](https://github.com/leanprover-community/mathlib/commit/07ee11e)
feat(algebra/algebra/basic): Add `map_finsupp_(sum|prod)` to `alg_(hom|equiv)` ([#4603](https://github.com/leanprover-community/mathlib/pull/4603))
Also copies some lemmas from `alg_hom` to `alg_equiv` that were missing

### [2020-10-15 16:29:00](https://github.com/leanprover-community/mathlib/commit/bb1f549)
feat(algebra/gcd_monoid): in a gcd_domain a coprime factor of a power is a power ([#4589](https://github.com/leanprover-community/mathlib/pull/4589))
The main result is:
```
theorem associated_pow_of_mul_eq_pow {a b c : α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : α), associated (d ^ k) a
```

### [2020-10-15 16:28:58](https://github.com/leanprover-community/mathlib/commit/b01ca81)
feat(data/matrix/notation): simp lemmas for constant-indexed elements ([#4491](https://github.com/leanprover-community/mathlib/pull/4491))
If you use the `![]` vector notation to define a vector, then `simp`
can extract elements `0` and `1` from that vector, but not element `2`
or subsequent elements.  (This shows up in particular in geometry if
defining a triangle with a concrete vector of vertices and then
subsequently doing things that need to extract a particular vertex.)
Add `bit0` and `bit1` `simp` lemmas to allow any element indexed by a
numeral to be extracted (even when the numeral is larger than the
length of the list, such numerals in `fin n` being interpreted mod
`n`).
This ends up quite long; `bit0` and `bit1` semantics mean extracting
alternate elements of the vector in a way that can wrap around to the
start of the vector when the numeral is `n` or larger, so the lemmas
need to deal with constructing such a vector of alternate elements.
As I've implemented it, some definitions also need an extra hypothesis
as an argument to control definitional equalities for the vector
lengths, to avoid problems with non-defeq types when stating
subsequent lemmas.  However, even the example added to
`test/matrix.lean` of extracting element `123456789` of a 5-element
vector is processed quite quickly, so this seems efficient enough.
Note also that there are two `@[simp]` lemmas whose proofs are just
`by simp`, but that are in fact needed for `simp` to complete
extracting some elements and that the `simp` linter does not (at least
when used with `#lint` for this single file) complain about.  I'm not
sure what's going on there, since I didn't think a lemma that `simp`
can prove should normally need to be marked as `@[simp]`.

### [2020-10-15 15:01:02](https://github.com/leanprover-community/mathlib/commit/85d4b57)
feat(data/polynomial/eval): bit0_comp, bit1_comp ([#4617](https://github.com/leanprover-community/mathlib/pull/4617))

### [2020-10-15 14:04:18](https://github.com/leanprover-community/mathlib/commit/1444fa5)
fix(haar_measure): minor changes ([#4623](https://github.com/leanprover-community/mathlib/pull/4623))
There were some mistakes in the doc, which made it sound like `chaar` and `haar_outer_measure` coincide on compact sets, which is not generally true. 
Also cleanup various proofs.

### [2020-10-15 08:51:18](https://github.com/leanprover-community/mathlib/commit/7559d1c)
lint(data/num/*): add docs and remove some [has_zero] requirements ([#4604](https://github.com/leanprover-community/mathlib/pull/4604))

### [2020-10-15 07:30:22](https://github.com/leanprover-community/mathlib/commit/fa65282)
chore(category_theory/monoidal): fix typo in docstrings ([#4625](https://github.com/leanprover-community/mathlib/pull/4625))

### [2020-10-15 01:11:53](https://github.com/leanprover-community/mathlib/commit/2e1129e)
chore(scripts): update nolints.txt ([#4622](https://github.com/leanprover-community/mathlib/pull/4622))
I am happy to remove some nolints for you!

### [2020-10-14 18:39:39](https://github.com/leanprover-community/mathlib/commit/084b7e7)
chore(algebra/order,data/set/intervals): a few more trivial lemmas ([#4611](https://github.com/leanprover-community/mathlib/pull/4611))
* a few more lemmas for `has_le.le` and `has_lt.lt` namespaces;
* a few lemmas about intersections of intervals;
* fix section header in `topology/algebra/module`.

### [2020-10-14 18:39:37](https://github.com/leanprover-community/mathlib/commit/d11eb84)
fix(tactic/suggest): properly remove "Try this: exact " prefix from library_search hole command ([#4609](https://github.com/leanprover-community/mathlib/pull/4609))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/mechanisms.20to.20search.20through.20mathlilb/near/213223321)

### [2020-10-14 17:31:01](https://github.com/leanprover-community/mathlib/commit/40844f0)
doc(category_theory/comma): Fix markdown rendering in docs ([#4618](https://github.com/leanprover-community/mathlib/pull/4618))

### [2020-10-14 14:46:32](https://github.com/leanprover-community/mathlib/commit/de46349)
feat(data/set/intervals): more lemmas about `unordered_interval` ([#4607](https://github.com/leanprover-community/mathlib/pull/4607))
Add images/preimages of unordered intervals under common arithmetic operations.

### [2020-10-14 14:46:30](https://github.com/leanprover-community/mathlib/commit/442ef22)
feat(linear_algebra/clifford_algebra): Add a definition derived from exterior_algebra.lean ([#4430](https://github.com/leanprover-community/mathlib/pull/4430))

### [2020-10-14 15:36:40+02:00](https://github.com/leanprover-community/mathlib/commit/1a1655c)
doc(docs/100): link to actual triangle inequality ([#4614](https://github.com/leanprover-community/mathlib/pull/4614))

### [2020-10-14 09:45:28](https://github.com/leanprover-community/mathlib/commit/f7edbca)
feat(algebra/char_zero): char_zero.infinite ([#4593](https://github.com/leanprover-community/mathlib/pull/4593))

### [2020-10-14 09:45:26](https://github.com/leanprover-community/mathlib/commit/6f5ccc1)
chore(linear_algebra/linear_independent): review API ([#4567](https://github.com/leanprover-community/mathlib/pull/4567))
### API changes
#### New definitions and lemmas
* `subalgebra.to_submodule_equiv`: a linear equivalence between a subalgebra and its coercion
  to a submodule;
* `algebra.to_submodule_bot`: coercion of `⊥ : subalgebra R A` to `submodule R A` is
  `submodule.span {1}`;
* `submodule.disjoint_def'`: one more expansion of `disjoint` for submodules;
* `submodule.is_compl_range_inl_inr`: ranges of `inl` and `inr` are complement submodules;
* `finsupp.supported_inter`, `finsupp.disjojint_supported_supported`,
  `finsupp.disjoint_supported_supported_iff` : more lemmas about `finsupp.supported`;
* `finsupp.total_unique`: formula for `finsupp.total` on a `unique` type;
* `linear_independent_iff_injective_total`, `linear_independent.injective_total` :
  relate `linear_independent R v` to `injective (finsupp.total ι M R v)`;
* `fintype.linear_independent_iff`: a simplified test for
  `linear_independent R v` if the domain of `v` is a `fintype`;
* `linear_independent.map'`: an injective linear map sends linearly
  independent families of vectors to linearly independent families of
  vectors;
* `linear_map.linear_independent_iff`: if `f` is an injective linear
  map, then `f ∘ v` is linearly independent iff `v` is linearly
  independent;
* `linear_independent.disjoint_span_image`: if `v` is a linearly
  independent family of vectors, then the submodules spanned by
  disjoint subfamilies of `v` are disjoint;
* `linear_independent_sum`: a test for linear independence of a
  disjoint union of two families of vectors;
* `linear_independent.sum_type`: `iff.mpr` from `linear_independent_sum`;
* `linear_independent_unique_iff`, `linear_independent_unique`: a test
  for linear independence of a single-vector family;
* `linear_independent_option'`, `linear_independent_option`, `linear_independent.option`:
  test for linear independence of a family indexed by `option ι`;
* `linear_independent_pair`: test for independence of `{v₁, v₂}`;
* `linear_independent_fin_cons`, `linear_independent.fin_cons`,
  `linear_independent_fin_succ`, `linear_independent_fin2`: tests for
  linear independence of families indexed by `i : fin n`.
#### Rename
* `_root_.disjoint_span_singleton` → `submodule.disjoint_span_singleton'`;
* `linear_independent.image` → `linear_independent.map`
* `linear_independent_of_comp` → `linear_independent.of_comp`;
#### Changes in type signature
* `is_basis.to_dual`, `is_basis.to_dual_flip`, `is_basis.to_dual_equiv`: take `B` as an explicit
  argument to improve readability of the pretty-printed output;

### [2020-10-14 08:24:05](https://github.com/leanprover-community/mathlib/commit/8511729)
refactor(data/int/gcd,ring_theory/int/basic): collect integer divisibility results from various files ([#4572](https://github.com/leanprover-community/mathlib/pull/4572))
Applying comments from PR [#4384](https://github.com/leanprover-community/mathlib/pull/4384). In particular:
1) Move the gcd and lcm results from gcd_monoid to `data/int/gcd.lean` with new proofs (for a few lcm results) that do not need ring theory.
2) Try to collect applications of ring theory to ℕ and ℤ into a new file `ring_theory/int/basic.lean`.

### [2020-10-14 08:24:03](https://github.com/leanprover-community/mathlib/commit/20006f1)
feat(data/polynomial/field_division, field_theory/splitting_field): Splits if enough roots ([#4557](https://github.com/leanprover-community/mathlib/pull/4557))
I have added some lemmas about polynomials that split. In particular the fact that if `p` has as many roots as its degree than it can be written as a product of `(X - a)` and so it splits.
The proof of this for monic polynomial, in `eq_prod_of_card_roots_monic`, is rather messy and can probably be improved a lot.

### [2020-10-14 01:06:37](https://github.com/leanprover-community/mathlib/commit/1c12bd9)
chore(scripts): update nolints.txt ([#4610](https://github.com/leanprover-community/mathlib/pull/4610))
I am happy to remove some nolints for you!

### [2020-10-13 23:51:13](https://github.com/leanprover-community/mathlib/commit/e2dd1c6)
feat(analysis/normed_space): unconditionally convergent series in `R^n` is absolutely convergent ([#4551](https://github.com/leanprover-community/mathlib/pull/4551))

### [2020-10-13 21:59:53](https://github.com/leanprover-community/mathlib/commit/2543b68)
refactor(*): migrate to `dense` API ([#4447](https://github.com/leanprover-community/mathlib/pull/4447))
@PatrickMassot introduced `dense` in [#4399](https://github.com/leanprover-community/mathlib/pull/4399). In this PR I review the API and migrate many definitions and lemmas
to use `dense s` instead of `closure s = univ`. I also generalize `second_countable_of_separable` to a `uniform_space`
with a countably generated uniformity filter.
## API changes
### Use `dense` or `dense_range` instead of `closure _ = univ`
#### Lemmas
- `has_fderiv_within_at.unique_diff_within_at`;
- `exists_dense_seq`;
- `dense_Inter_of_open_nat`;
- `dense_sInter_of_open`;
- `dense_bInter_of_open`;
- `dense_Inter_of_open`;
- `dense_sInter_of_Gδ`;
- `dense_bInter_of_Gδ`;
- `eventually_residual`;
- `mem_residual`;
- `dense_bUnion_interior_of_closed`;
- `dense_sUnion_interior_of_closed`;
- `dense_Union_interior_of_closed`;
- `Kuratowski_embeddinng.embedding_of_subset_isometry`;
- `continuous_extend_from`;
#### Definitions
- `unique_diff_within_at`;
- `residual`;
### Rename
- `submodule.linear_eq_on` → `linear_map.eq_on_span`, `linear_map.eq_on_span'`;
- `submodule.linear_map.ext_on` → `linear_map.ext_on_range`;
- `filter.is_countably_generated.has_antimono_basis` →
  `filter.is_countably_generated.exists_antimono_basis`;
- `exists_countable_closure_eq_univ` → `exists_countable_dense`, use `dense`;
- `dense_seq_dense` → `dense_range_dense_seq`, use `dense`;
- `dense_range.separable_space` is now `protected`;
- `dense_of_subset_dense` → `dense.mono`;
- `dense_inter_of_open_left` → `dense.inter_of_open_left`;
- `dense_inter_of_open_right` → `dense.inter_of_open_right`;
- `continuous.dense_image_of_dense_range` → `dense_range.dense_image`;
- `dense_range.inhabited`, `dense_range.nonempty`: changed API, TODO;
- `quotient_dense_of_dense` → `dense.quotient`, use `dense`;
- `dense_inducing.separable` → `dense_inducing.separable_space`, add `protected`;
- `dense_embedding.separable` → `dense_embedding.separable_space`, add `protected`;
- `dense_inter_of_Gδ` → `dense.inter_of_Gδ`;
- `stone_cech_unit_dense` → `dense_range_stone_cech_unit`;
- `abstract_completion.dense'` → `abstract_completion.closure_range`;
- `Cauchy.pure_cauchy_dense` → `Cauchy.dense_range_pure_cauchy`;
- `completion.dense` → `completion.dense_range_coe`;
- `completion.dense₂` → `completion.dense_range_coe₂`;
- `completion.dense₃` → `completion.dense_range_coe₃`;
### New
- `has_fderiv_within_at.unique_on` : if `f'` and `f₁'` are two derivatives of `f`
  within `s` at `x`, then they are equal on the tangent cone to `s` at `x`;
- `local_homeomorph.mdifferentiable.mfderiv_bijective`,
  `local_homeomorph.mdifferentiable.mfderiv_surjective`
- `continuous_linear_map.eq_on_closure_span`: if two continuous linear maps are equal on `s`,
  then they are equal on `closure (submodule.span s)`;
- `continuous_linear_map.ext_on`: if two continuous linear maps are equal on a set `s` such that
  `submodule.span s` is dense, then they are equal;
- `dense_closure`: `closure s` is dense iff `s` is dense;
- `dense.of_closure`, `dense.closure`: aliases for `dense_closure.mp` and `dense_closure.mpr`;
- `dense_univ`: `univ` is dense;
- `dense.inter_open_nonempty`: alias for `dense_iff_inter_open.mp`;
- `dense.nonempty_iff`: if `s : set α` is a dense set, then `s` is nonempty iff `α` is nonempty;
- `dense.nonempty`: a dense set in a nonempty type is nonempty;
- `dense_range.some`: given a function with `dense_range` and a point in the codomain, returns a point in the domain;
- `function.surjective.dense_range`: a surjective function has dense range;
- `continuous.range_subset_closure_image_dense`: closure of the image of a dense set under
  a continuous function includes the range of this function;
- `dense_range.dense_of_maps_to`: if a function with dense range maps a dense set `s` to `t`, then
  `t` is dense in the codomain;
- `dense_range.quotient`;
- `dense.prod`: product of two dense sets is dense in the product;
- `set.eq_on.closure`;
- `continuous.ext_on`;
- `linear_map.ext_on`

### [2020-10-13 19:48:34](https://github.com/leanprover-community/mathlib/commit/fde3d78)
chore(multiset): dedicated notation for multiset.cons ([#4600](https://github.com/leanprover-community/mathlib/pull/4600))

### [2020-10-13 18:44:25](https://github.com/leanprover-community/mathlib/commit/7368d71)
chore(number_theory/arithmetic_function): Define in terms of zero_hom ([#4606](https://github.com/leanprover-community/mathlib/pull/4606))
No need to write these proofs in two places

### [2020-10-13 16:46:02](https://github.com/leanprover-community/mathlib/commit/b1c1033)
feat(analysis/normed_space/operator_norm): construct a continuous_linear_equiv from a linear_equiv and bounds in both directions ([#4583](https://github.com/leanprover-community/mathlib/pull/4583))

### [2020-10-13 16:46:00](https://github.com/leanprover-community/mathlib/commit/7cff825)
feat(data/vector2): induction principle, define last, and some lemmas (blocked by [#4578](https://github.com/leanprover-community/mathlib/pull/4578)) ([#4554](https://github.com/leanprover-community/mathlib/pull/4554))

### [2020-10-13 15:24:50](https://github.com/leanprover-community/mathlib/commit/71bb9f2)
chore(linear_algebra/finsupp): Implement lsingle in terms of single_add_hom ([#4605](https://github.com/leanprover-community/mathlib/pull/4605))
While not shorter, this makes it easier to relate the two definitions

### [2020-10-13 14:02:34](https://github.com/leanprover-community/mathlib/commit/ca6af1c)
chore(algebra/monoid_algebra): Replace `algebra_map'` with `single_(zero|one)_ring_hom` ([#4582](https://github.com/leanprover-community/mathlib/pull/4582))
`algebra_map'` is now trivially equal to `single_(zero|one)_ring_hom.comp`, so is no longer needed.

### [2020-10-13 11:12:28](https://github.com/leanprover-community/mathlib/commit/9f9344d)
feat(algebra/char_p): fields with a hom between them have same char ([#4594](https://github.com/leanprover-community/mathlib/pull/4594))

### [2020-10-13 09:47:17](https://github.com/leanprover-community/mathlib/commit/dd8bf2c)
feat(data/polynomial/eval): easy lemmas + speedup ([#4596](https://github.com/leanprover-community/mathlib/pull/4596))

### [2020-10-13 06:30:22](https://github.com/leanprover-community/mathlib/commit/7fff35f)
chore(algebra/pointwise): remove `@[simp]` from `singleton_one`/`singleton_zero` ([#4592](https://github.com/leanprover-community/mathlib/pull/4592))
This lemma simplified `{1}` and `{0}` to `1` and `0` making them unusable for other `singleton` lemmas.

### [2020-10-13 06:30:20](https://github.com/leanprover-community/mathlib/commit/c9ae9e6)
chore(linear_algebra/dimension): more same-universe versions of `is_basis.mk_eq_dim` ([#4591](https://github.com/leanprover-community/mathlib/pull/4591))
While all the `lift` magic is good for general theory, it is not that convenient for the case when everything is in `Type`.
* add `mk_eq_mk_of_basis'`: same-universe version of `mk_eq_mk_of_basis`;
* generalize `is_basis.mk_eq_dim''` to any index type in the same universe as `V`, not necessarily `s : set V`;
* reorder lemmas to optimize the total length of the proofs;
* drop one `finite_dimensional` assumption in `findim_of_infinite_dimensional`.

### [2020-10-13 04:39:56](https://github.com/leanprover-community/mathlib/commit/766d860)
fix(big_operators): fix imports ([#4588](https://github.com/leanprover-community/mathlib/pull/4588))
Previously `algebra.big_operators.pi` imported `algebra.big_operators.default`. That import direction is now reversed.

### [2020-10-13 03:48:58](https://github.com/leanprover-community/mathlib/commit/505b969)
feat(archive/imo): formalize IMO 1962 problem Q1 ([#4450](https://github.com/leanprover-community/mathlib/pull/4450))
The problem statement:
Find the smallest natural number $n$ which has the following properties:
(a) Its decimal representation has 6 as the last digit.
(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.
This is a proof that 153846 is the smallest member of the set satisfying these conditions.

### [2020-10-13 02:01:14](https://github.com/leanprover-community/mathlib/commit/e957269)
chore(scripts): update nolints.txt ([#4587](https://github.com/leanprover-community/mathlib/pull/4587))
I am happy to remove some nolints for you!

### [2020-10-13 02:01:12](https://github.com/leanprover-community/mathlib/commit/9eb341a)
feat(mv_polynomial): minor simplification in coeff_mul ([#4586](https://github.com/leanprover-community/mathlib/pull/4586))
The proof was already golfed in [#4472](https://github.com/leanprover-community/mathlib/pull/4472).
Use `×` instead of `sigma`.
Shorten one line over 100 chars.

### [2020-10-13 02:01:09](https://github.com/leanprover-community/mathlib/commit/7dcaee1)
feat(archive/imo): formalize IMO 1962 problem 4 ([#4518](https://github.com/leanprover-community/mathlib/pull/4518))
The problem statement: Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.
There are a bunch of trig formulas I proved along the way; there are sort of an infinite number of trig formulas so I'm open to feedback on whether some should go in the core libraries. Also possibly some of them have a shorter proof that would render the lemma unnecessary.
For what it's worth, the actual method of solution is not how a human would do it; a more intuitive human method is to simplify in terms of `cos x` and then solve, but I think this is simpler in Lean because it doesn't rely on solving `cos x = y` for several different `y`.

### [2020-10-13 02:01:07](https://github.com/leanprover-community/mathlib/commit/b231d8e)
feat(archive/imo): formalize IMO 1960 problem 1 ([#4366](https://github.com/leanprover-community/mathlib/pull/4366))
The problem:
Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.
Art of Problem Solving offers three solutions to this problem - https://artofproblemsolving.com/wiki/index.php/1960_IMO_Problems/Problem_1 - but they all involve a fairly large amount of bashing through cases and solving basic algebra. This proof is also essentially bashing through cases, using the `iterate` tactic and calls to `norm_num`.

### [2020-10-12 23:17:41](https://github.com/leanprover-community/mathlib/commit/a6d445d)
feat(data/finsupp): Add `map_finsupp_prod` to homs ([#4585](https://github.com/leanprover-community/mathlib/pull/4585))
This is a convenience alias for `map_prod`, which is awkward to use.

### [2020-10-12 23:17:40](https://github.com/leanprover-community/mathlib/commit/d1bb5ea)
feat(topology/category/Compactum): Compact Hausdorff spaces ([#4555](https://github.com/leanprover-community/mathlib/pull/4555))
This PR provides the equivalence between the category of compact Hausdorff topological spaces and the category of algebras for the ultrafilter monad.
## Notation
1. `Compactum` is the category of algebras for the ultrafilter monad. It's a wrapper around `monad.algebra (of_type_functor $ ultrafilter)`.
2. `CompHaus` is the full subcategory of `Top` consisting of topological spaces which are compact and Hausdorff.

### [2020-10-12 23:17:37](https://github.com/leanprover-community/mathlib/commit/bc77a23)
feat(data/list/*): add left- and right-biased versions of map₂ and zip ([#4512](https://github.com/leanprover-community/mathlib/pull/4512))
When given lists of different lengths, `map₂` and `zip` truncate the output to
the length of the shorter input list. This commit adds variations on `map₂` and
`zip` whose output is always as long as the left/right input.

### [2020-10-12 20:50:13](https://github.com/leanprover-community/mathlib/commit/d3d70f1)
chore(algebra/order*): move `abs`/`min`/`max`, review ([#4581](https://github.com/leanprover-community/mathlib/pull/4581))
* make `algebra.ordered_group` import `algebra.order_functions`, not vice versa;
* move some proofs from `algebra.ordered_functions` to `algebra.ordered_group` and `algebra.ordered_ring`;
* deduplicate API;
* golf some proofs.

### [2020-10-12 20:50:11](https://github.com/leanprover-community/mathlib/commit/6ea6200)
feat(tactic/rcases): rcases_many ([#4569](https://github.com/leanprover-community/mathlib/pull/4569))
This allows you to pattern match many variables at once, using the
syntax `obtain ⟨a|b, c|d⟩ := ⟨x, y⟩`. This doesn't require any change
to the front end documentation, as it is in some sense the obvious thing,
but this doesn't break any existing uses because this could never work
before (since the expected type of the tuple expression is not known).

### [2020-10-12 20:50:09](https://github.com/leanprover-community/mathlib/commit/9bed456)
feta(data/fin): induction principle on fin (n + 1) ([#4546](https://github.com/leanprover-community/mathlib/pull/4546))

### [2020-10-12 20:50:06](https://github.com/leanprover-community/mathlib/commit/8ccfb0a)
chore(control/functor): linting ([#4496](https://github.com/leanprover-community/mathlib/pull/4496))

### [2020-10-12 18:08:56](https://github.com/leanprover-community/mathlib/commit/9713e96)
chore(*): update to Lean 3.21.0c ([#4578](https://github.com/leanprover-community/mathlib/pull/4578))
The only real change is the removal of notation for `vector.cons`.

### [2020-10-12 18:08:53](https://github.com/leanprover-community/mathlib/commit/6816b83)
feat(archive/100-theorems-list/70_perfect_numbers): Direction 1 of the Perfect Number Theorem ([#4544](https://github.com/leanprover-community/mathlib/pull/4544))
Proves Euclid's half of the Euclid-Euler Theorem that if `2 ^ (k + 1) - 1` is prime, then `2 ^ k * (2 ^ (k + 1) - 1)` is an (even) perfect number.

### [2020-10-12 17:14:21](https://github.com/leanprover-community/mathlib/commit/9379050)
chore(data/hash_map): linting ([#4498](https://github.com/leanprover-community/mathlib/pull/4498))

### [2020-10-12 14:57:35](https://github.com/leanprover-community/mathlib/commit/266895f)
fix(algebra/ordered_group): use `add_neg` in autogenerated lemma name ([#4580](https://github.com/leanprover-community/mathlib/pull/4580))
Explicitly add `sub_le_sub_iff` with `a - b`.

### [2020-10-12 14:57:33](https://github.com/leanprover-community/mathlib/commit/b3ce883)
feat(algebra/*_power): simplify `(-a)^(bit0 _)` and `(-a)^(bit1 _)` ([#4573](https://github.com/leanprover-community/mathlib/pull/4573))
Works for `pow` and `fpow`. Also simplify powers of `I : ℂ`.

### [2020-10-12 14:57:31](https://github.com/leanprover-community/mathlib/commit/38e9ed3)
feat(archive/imo): IMO 2020 Q2 ([#4565](https://github.com/leanprover-community/mathlib/pull/4565))
Add a proof of IMO 2020 Q2 (directly following one of the official
solutions; there are many very similar approaches possible).
In support of this solution, add `geom_mean_le_arith_mean4_weighted`
to `analysis.mean_inequalities`, for both `real` and `nnreal`,
analogous to the versions for two and three numbers (and also add
`geom_mean_le_arith_mean3_weighted` for `real` as it was only present
for `nnreal`).

### [2020-10-12 14:57:28](https://github.com/leanprover-community/mathlib/commit/5022425)
feat(algebra/free_algebra): Add an inductive principle ([#4335](https://github.com/leanprover-community/mathlib/pull/4335))

### [2020-10-12 14:57:26](https://github.com/leanprover-community/mathlib/commit/3d1f16a)
feat(analysis/normed_space/multilinear): define `mk_pi_algebra` ([#4316](https://github.com/leanprover-community/mathlib/pull/4316))
I'm going to use this definition for converting `(mv_)power_series` to `formal_multilinear_series`.

### [2020-10-12 12:21:50](https://github.com/leanprover-community/mathlib/commit/1362701)
refactor(field_theory): Adjoin intermediate field ([#4468](https://github.com/leanprover-community/mathlib/pull/4468))
Refactor adjoin to be an intermediate field rather than a subalgebra.

### [2020-10-12 10:16:23](https://github.com/leanprover-community/mathlib/commit/8fa9125)
feat(data/polynomial/degree/erase_lead): definition and basic lemmas ([#4527](https://github.com/leanprover-community/mathlib/pull/4527))
erase_lead serves as the reduction step in an induction, breaking off one monomial from a polynomial.  It is used in a later PR to prove that reverse is a multiplicative monoid map on polynomials.

### [2020-10-12 08:30:01](https://github.com/leanprover-community/mathlib/commit/0bfc68f)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_int_prop ([#4466](https://github.com/leanprover-community/mathlib/pull/4466))
This is the 3rd PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-12 06:33:28](https://github.com/leanprover-community/mathlib/commit/b953717)
feat(set_theory/cardinal): cardinality of powerset ([#4576](https://github.com/leanprover-community/mathlib/pull/4576))
adds a lemma for cardinality of powerset

### [2020-10-12 01:08:24](https://github.com/leanprover-community/mathlib/commit/81b8123)
chore(scripts): update nolints.txt ([#4575](https://github.com/leanprover-community/mathlib/pull/4575))
I am happy to remove some nolints for you!

### [2020-10-11 21:16:36](https://github.com/leanprover-community/mathlib/commit/665cc13)
chore(topology/algebra/group): review ([#4570](https://github.com/leanprover-community/mathlib/pull/4570))
* Ensure that we don't use `[topological_group G]` when it suffices to ask for, e.g., `[has_continuous_mul G]`.
* Introduce `[has_continuous_sub]`, add an instance for `nnreal`.

### [2020-10-11 20:09:45](https://github.com/leanprover-community/mathlib/commit/952a407)
feat(data/nat/digits): add norm_digits tactic ([#4452](https://github.com/leanprover-community/mathlib/pull/4452))
This adds a basic tactic for normalizing expressions of the form `nat.digits a b = l`. As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/simplifying.20nat.2Edigits/near/212152395

### [2020-10-11 20:09:43](https://github.com/leanprover-community/mathlib/commit/b1ca33e)
feat(analysis/calculus/times_cont_diff, analysis/calculus/inverse): smooth inverse function theorem ([#4407](https://github.com/leanprover-community/mathlib/pull/4407))
The inverse function theorem, in the C^k and smooth categories.

### [2020-10-11 18:49:02](https://github.com/leanprover-community/mathlib/commit/b48b4ff)
feat(analysis/normed_space/inner_product): Cauchy-Schwarz equality case and other lemmas ([#4571](https://github.com/leanprover-community/mathlib/pull/4571))

### [2020-10-11 18:49:00](https://github.com/leanprover-community/mathlib/commit/0f085b9)
chore(linear_algebra/finite_dimensional): rename `of_finite_basis` ([#4562](https://github.com/leanprover-community/mathlib/pull/4562))
* rename `of_finite_basis` to `of_fintype_basis`;
* add new `of_finite_basis` assuming that the domain the basis is a
  `finite` set;
* allow `s : finset ι` and any function `s → V` in `of_finset_basis`.

### [2020-10-11 16:27:35](https://github.com/leanprover-community/mathlib/commit/14dcfe0)
chore(*): assorted lemmas ([#4566](https://github.com/leanprover-community/mathlib/pull/4566))
Non-bc changes:
* make some lemmas use `coe` instead of `subtype.val`;
* make the arguments of `range_comp` explicit, reorder them.

### [2020-10-11 16:27:33](https://github.com/leanprover-community/mathlib/commit/918e5d8)
chore(data/finsupp): replace `eq_zero_of_zero_eq_one` with `finsupp.unique_of_right` ([#4563](https://github.com/leanprover-community/mathlib/pull/4563))
Also add a lemma `semimodule.subsingleton`: if `R` is a subsingleton semiring, then any semimodule over `R` is a subsingleton.

### [2020-10-11 15:12:38](https://github.com/leanprover-community/mathlib/commit/33f7870)
chore(measure_theory/measurable_space): add `finset.is_measurable_bUnion` etc ([#4553](https://github.com/leanprover-community/mathlib/pull/4553))
I always forget how to convert `finset` or `set.finite` to `set.countable. Also `finset.is_measurable_bUnion` uses `finset`'s `has_mem`, not coercion to `set`.
Also replace `tendsto_at_top_supr_nat` etc with slightly more general versions using a `[semilattice_sup β] [nonempty β]` instead of `nat`.

### [2020-10-11 12:30:22](https://github.com/leanprover-community/mathlib/commit/99130d8)
chore(algebra/monoid_algebra): Reorder lemmas, name some sections for clarity ([#4535](https://github.com/leanprover-community/mathlib/pull/4535))
This also reduces the scope of `local attribute [reducible] add_monoid_algebra` to the sections which actually need it.

### [2020-10-11 10:42:23](https://github.com/leanprover-community/mathlib/commit/0487a1d)
chore(algebra/algebra/basic): fix definition of `ring_hom.to_algebra` ([#4561](https://github.com/leanprover-community/mathlib/pull/4561))
The new definition uses `to_ring_hom := i` instead of `.. i` to get
defeq `algebra_map R S = i`, and adds it as a lemma.

### [2020-10-11 04:06:05](https://github.com/leanprover-community/mathlib/commit/2c53e5e)
chore(order/well_founded): move to a file ([#4568](https://github.com/leanprover-community/mathlib/pull/4568))
I want to use `order/rel_classes` before `data/set/basic`.

### [2020-10-11 03:06:27](https://github.com/leanprover-community/mathlib/commit/4dbebe3)
chore(scripts): update nolints.txt ([#4564](https://github.com/leanprover-community/mathlib/pull/4564))
I am happy to remove some nolints for you!

### [2020-10-11 01:02:23](https://github.com/leanprover-community/mathlib/commit/d8d6e18)
feat(data/finset/basic): equivalence of finsets from equivalence of types ([#4560](https://github.com/leanprover-community/mathlib/pull/4560))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`, and simp lemmas about it.

### [2020-10-10 23:06:12](https://github.com/leanprover-community/mathlib/commit/df5adc5)
chore(topology/*): golf some proofs ([#4528](https://github.com/leanprover-community/mathlib/pull/4528))
* move `exists_nhds_split` to `topology/algebra/monoid`, rename to `exists_nhds_one_split`;
* add a version `exists_open_nhds_one_split`;
* move `exists_nhds_split4` to `topology/algebra/monoid`, rename to `exists_nhds_one_split4`;
* move `one_open_separated_mul` to `topology/algebra/monoid`, rename to `exists_open_nhds_one_mul_subset`;
* add `mem_prod_nhds_iff`;
* golf some proofs.

### [2020-10-10 20:25:23](https://github.com/leanprover-community/mathlib/commit/c726898)
feat(data/equiv/basic): equivalence on functions from bool ([#4559](https://github.com/leanprover-community/mathlib/pull/4559))
An equivalence of functions from bool and pairs, together with some simp lemmas about it.
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).

### [2020-10-10 18:28:05](https://github.com/leanprover-community/mathlib/commit/f91e0c6)
feat(data/finset/pi): pi singleton lemmas ([#4558](https://github.com/leanprover-community/mathlib/pull/4558))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259). 
Two lemmas to reduce `finset.pi` on singletons.

### [2020-10-10 15:18:44](https://github.com/leanprover-community/mathlib/commit/c8738cb)
feat(topology/uniform_space/cauchy): generalize `second_countable_of_separable` to uniform spaces ([#4530](https://github.com/leanprover-community/mathlib/pull/4530))
Also generalize `is_countably_generated.has_antimono_basis` to `is_countably_generated.exists_antimono_subbasis` and add a few lemmas about bases of the uniformity filter.

### [2020-10-10 09:40:05](https://github.com/leanprover-community/mathlib/commit/6676917)
feat(analysis/special_functions/*): a few more simp lemmas ([#4550](https://github.com/leanprover-community/mathlib/pull/4550))
Add more lemmas for simplifying inequalities with `exp`, `log`, and
`rpow`. Lemmas that generate more than one inequality are not marked
as `simp`.

### [2020-10-10 01:04:50](https://github.com/leanprover-community/mathlib/commit/b084a06)
chore(scripts): update nolints.txt ([#4556](https://github.com/leanprover-community/mathlib/pull/4556))
I am happy to remove some nolints for you!

### [2020-10-09 19:22:53](https://github.com/leanprover-community/mathlib/commit/40b55c0)
feat(measure_theory): additions ([#4324](https://github.com/leanprover-community/mathlib/pull/4324))
Many additional lemmas. 
Notable addition: sequential limits of measurable functions into a metric space are measurable.
Rename `integral_map_measure` -> `integral_map` (to be consistent with the version for `lintegral`)
Fix the precedence of all notations for integrals. From now on `∫ x, abs ∥f x∥ ∂μ` will be parsed
correctly (previously it gave a parse error).
Some cleanup (moving lemmas, and some nicer presentation by opening locales and namespaces).

### [2020-10-09 18:15:49](https://github.com/leanprover-community/mathlib/commit/d533e1c)
feat(ring_theory/power_series): inverse lemmas ([#4552](https://github.com/leanprover-community/mathlib/pull/4552))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).

### [2020-10-09 15:44:20](https://github.com/leanprover-community/mathlib/commit/b167809)
feat(topology/basic): Lim_spec etc. cleanup ([#4545](https://github.com/leanprover-community/mathlib/pull/4545))
Fixes [#4543](https://github.com/leanprover-community/mathlib/pull/4543)
See [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/More.20point.20set.20topology.20questions/near/212757136)

### [2020-10-09 13:16:06](https://github.com/leanprover-community/mathlib/commit/fcaf6e9)
feat(meta/expr): add parser for generated binder names ([#4540](https://github.com/leanprover-community/mathlib/pull/4540))
During elaboration, Lean generates a name for anonymous Π binders. This commit
adds a parser that recognises such names.

### [2020-10-09 13:16:04](https://github.com/leanprover-community/mathlib/commit/306dc8a)
chore(algebra/big_operators/basic): add lemma prod_multiset_count' that generalize prod_multiset_count to consider a function to a monoid ([#4534](https://github.com/leanprover-community/mathlib/pull/4534))
I have added `prod_multiset_count'` that is very similar to `prod_multiset_count` but takes into account a function `f : \a \r M` where `M` is a commutative monoid. The proof is essentially the same (I didn't try to prove it using `prod_multiset_count` because maybe we can remove it and just keep the more general version).

### [2020-10-09 11:06:01](https://github.com/leanprover-community/mathlib/commit/656ef0a)
chore(topology/instances/nnreal): use notation ([#4548](https://github.com/leanprover-community/mathlib/pull/4548))

### [2020-10-09 11:05:59](https://github.com/leanprover-community/mathlib/commit/d0f45f5)
lint(various): nolint has_inhabited_instance for injective functions ([#4541](https://github.com/leanprover-community/mathlib/pull/4541))
`function.embedding`, `homeomorph`, `isometric` represent injective/bijective functions, so it's silly to expect them to be inhabited.

### [2020-10-09 08:54:38](https://github.com/leanprover-community/mathlib/commit/cc75e4e)
chore(data/nat/cast): a few `simp`/`norm_cast` lemmas ([#4549](https://github.com/leanprover-community/mathlib/pull/4549))

### [2020-10-09 01:44:31](https://github.com/leanprover-community/mathlib/commit/f6836c1)
chore(scripts): update nolints.txt ([#4547](https://github.com/leanprover-community/mathlib/pull/4547))
I am happy to remove some nolints for you!

### [2020-10-08 23:44:06](https://github.com/leanprover-community/mathlib/commit/8004fb6)
chore(topology/algebra/group): move a lemma to `group_theory/coset` ([#4522](https://github.com/leanprover-community/mathlib/pull/4522))
`quotient_group_saturate` didn't use any topology. Move it to
`group_theory/coset` and rename to
`quotient_group.preimage_image_coe`.
Also rename `quotient_group.open_coe` to `quotient_group.is_open_map_coe`

### [2020-10-08 22:15:42](https://github.com/leanprover-community/mathlib/commit/ce999a8)
feat(topology/basic): add `is_open_iff_ultrafilter` ([#4529](https://github.com/leanprover-community/mathlib/pull/4529))
Requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F)
by Adam Topaz

### [2020-10-08 18:04:05](https://github.com/leanprover-community/mathlib/commit/a912455)
fix(bors.toml, build.yml): check for new linter, rename linter to "Lint style" ([#4539](https://github.com/leanprover-community/mathlib/pull/4539))

### [2020-10-08 15:41:18](https://github.com/leanprover-community/mathlib/commit/73f119e)
refactor(category_theory/pairwise): change direction of morphisms in the category of pairwise intersections ([#4537](https://github.com/leanprover-community/mathlib/pull/4537))
Even though this makes some proofs slightly more awkward, this is the more natural definition.
In a subsequent PR about another equivalent sheaf condition, it also makes proofs less awkward, too!

### [2020-10-08 15:41:16](https://github.com/leanprover-community/mathlib/commit/0ae4a3d)
fix(update-copy-mod-doc-exceptions.sh): cleanup, sort properly ([#4533](https://github.com/leanprover-community/mathlib/pull/4533))
Followup to [#4513](https://github.com/leanprover-community/mathlib/pull/4513).

### [2020-10-08 15:41:14](https://github.com/leanprover-community/mathlib/commit/427564e)
chore(algebra/monoid_algebra): Fix TODO about unwanted unfolding ([#4532](https://github.com/leanprover-community/mathlib/pull/4532))
For whatever reason, supplying `zero` and `add` explicitly makes the proofs work inline.
This TODO was added by @johoelzl in f09abb1c47a846c33c0e996ffa9bf12951b40b15.

### [2020-10-08 15:41:12](https://github.com/leanprover-community/mathlib/commit/0c18d96)
chore(data/padics/*): linting + squeeze_simp speedup ([#4531](https://github.com/leanprover-community/mathlib/pull/4531))

### [2020-10-08 15:41:08](https://github.com/leanprover-community/mathlib/commit/60be8ed)
feat(data/equiv/*): to_monoid_hom_injective and to_ring_hom_injective ([#4525](https://github.com/leanprover-community/mathlib/pull/4525))

### [2020-10-08 15:41:06](https://github.com/leanprover-community/mathlib/commit/253f225)
lint(computability/halting): docstrings ([#4524](https://github.com/leanprover-community/mathlib/pull/4524))
Adds docstrings in `computability/halting.lean`

### [2020-10-08 15:41:04](https://github.com/leanprover-community/mathlib/commit/e74bd26)
chore(*): add a few more `unique` instances ([#4511](https://github.com/leanprover-community/mathlib/pull/4511))
* `linear_map.unique_of_left`, `linear_map.unique_of_right`,
  `continuous_linear_map.unique_of_left`,
  `continuous_linear_map.unique_of_right`: if either `M` or `M₂` is a
  `subsingleton`, then both `M →ₗ[R] M₂` and `M →L[R] M₂` are
  `unique`;
* `pi.unique`: if each `β a` is `unique`, then `Π a, β a` is `unique`;
* rename `function.injective.comap_subsingleton` to
  `function.injective.subsingleton`;
* add `unique.mk'` and `function.injective.unique`;
* add a few `simp` lemmas for `default`;
* drop `nonempty_unique_or_exists_ne` and `subsingleton_or_exists_ne`;
* rename `linear_map.coe_inj` to `coe_injective` and `continuous_linear_map.coe_inj` to `coe_fn_injective`,
  make them use `function.injective`.
Motivated by [#4407](https://github.com/leanprover-community/mathlib/pull/4407)

### [2020-10-08 15:41:02](https://github.com/leanprover-community/mathlib/commit/7b42c71)
feat(archive/imo): revive @kbuzzard's imo2019_q1 ([#4377](https://github.com/leanprover-community/mathlib/pull/4377))

### [2020-10-08 15:40:59](https://github.com/leanprover-community/mathlib/commit/9b0d30c)
feat(number_theory/arithmetic_function): define `is_multiplicative` on `arithmetic_function`s, provides examples ([#4312](https://github.com/leanprover-community/mathlib/pull/4312))
Provides a few basic examples of important arithmetic functions
Defines what it means for an arithmetic function to be multiplicative

### [2020-10-08 13:27:56](https://github.com/leanprover-community/mathlib/commit/5a01549)
lint(multiset/pi): remove unused instance ([#4526](https://github.com/leanprover-community/mathlib/pull/4526))
Removes an unused instance from `multiset/pi`

### [2020-10-08 13:27:54](https://github.com/leanprover-community/mathlib/commit/48a3604)
feat(logic/nontrivial): a tactic to summon nontrivial instances ([#4374](https://github.com/leanprover-community/mathlib/pull/4374))
```
Given a goal `a = b` or `a ≤ b` in a type `α`, generates an additional hypothesis `nontrivial α`
(as otherwise `α` is a subsingleton and the goal is trivial).
Alternatively, given a hypothesis `a ≠ b` or `a < b` in a type `α`, tries to generate a `nontrivial α`
hypothesis from existing hypotheses using `nontrivial_of_ne` and `nontrivial_of_lt`.
```

### [2020-10-08 10:23:23](https://github.com/leanprover-community/mathlib/commit/43f52dd)
chore(algebra/char_zero): rename vars, add `with_top` instance ([#4523](https://github.com/leanprover-community/mathlib/pull/4523))
Motivated by [#3135](https://github.com/leanprover-community/mathlib/pull/3135).
* Use `R` as a `Type*` variable;
* Add `add_monoid_hom.map_nat_cast` and `with_top.coe_add_hom`;
* Drop versions of `char_zero_of_inj_zero`, use `[add_left_cancel_monoid R]` instead.

### [2020-10-08 05:32:06](https://github.com/leanprover-community/mathlib/commit/34a4471)
chore(data/quot): `quot.mk` etc are surjective ([#4517](https://github.com/leanprover-community/mathlib/pull/4517))

### [2020-10-08 05:32:04](https://github.com/leanprover-community/mathlib/commit/4f75760)
chore(*/hom,equiv): Split `monoid_hom` into more fundamental structures, and reuse them elsewhere ([#4423](https://github.com/leanprover-community/mathlib/pull/4423))
Notably this adds `add_hom` and `mul_hom`, which become base classes of `add_equiv`, `mul_equiv`, `linear_map`, and `linear_equiv`.
Primarily to avoid breaking assumptions of field order in `monoid_hom` and `add_monoid_hom`, this also adds `one_hom` and `zero_hom`.
A massive number of lemmas here are totally uninteresting and hold for pretty much all objects that define `coe_to_fun`.
This PR translates all those lemmas, but doesn't bother attempting to generalize later ones.

### [2020-10-08 04:37:20](https://github.com/leanprover-community/mathlib/commit/b4dc912)
ci(*): run style lint in parallel job, fix update-copy-mod-doc-exceptions.sh ([#4513](https://github.com/leanprover-community/mathlib/pull/4513))
Followup to [#4486](https://github.com/leanprover-community/mathlib/pull/4486):
- run the linter in a separate parallel job, per request
- the update-*.sh script now correctly generates a full exceptions file
- add some more comments to the shell scripts

### [2020-10-08 04:37:18](https://github.com/leanprover-community/mathlib/commit/3d1d4fb)
feat(data/polynomial/degree/trailing_degree): fixed formatting and streamlined a couple of proofs ([#4509](https://github.com/leanprover-community/mathlib/pull/4509))

### [2020-10-08 03:44:56](https://github.com/leanprover-community/mathlib/commit/7a71554)
doc(tactic/slim_check): improve advice in error message ([#4520](https://github.com/leanprover-community/mathlib/pull/4520))
The error message in `slim_check` suggests to look for `testable` and it now specifies which namespace to find `testable` in.

### [2020-10-08 01:08:47](https://github.com/leanprover-community/mathlib/commit/e9d1dc4)
chore(scripts): update nolints.txt ([#4521](https://github.com/leanprover-community/mathlib/pull/4521))
I am happy to remove some nolints for you!

### [2020-10-07 23:27:32](https://github.com/leanprover-community/mathlib/commit/a5b0376)
chore(topology/algebra/monoid,group): rename variables ([#4516](https://github.com/leanprover-community/mathlib/pull/4516))
Use `M`, `N` for monoids, `G`, `H` for groups.

### [2020-10-07 21:39:17](https://github.com/leanprover-community/mathlib/commit/d67062f)
chore(algebra/pointwise): add `###` here and there ([#4514](https://github.com/leanprover-community/mathlib/pull/4514))

### [2020-10-07 21:39:15](https://github.com/leanprover-community/mathlib/commit/fa8b7ba)
chore(topology/*): use dot notation for `is_open.prod` and `is_closed.prod` ([#4510](https://github.com/leanprover-community/mathlib/pull/4510))

### [2020-10-07 20:25:40](https://github.com/leanprover-community/mathlib/commit/2b89d59)
chore(ring_theory/coprime): weaken assumptions of finset.prod_dvd_of_coprime ([#4506](https://github.com/leanprover-community/mathlib/pull/4506))

### [2020-10-07 18:09:31](https://github.com/leanprover-community/mathlib/commit/4635aee)
chore(algebra/continuous_functions): `coninuous` -> `continuous` ([#4508](https://github.com/leanprover-community/mathlib/pull/4508))

### [2020-10-07 18:09:28](https://github.com/leanprover-community/mathlib/commit/4e8427e)
fix(data/list/defs): remove map_head; rename map_last to modify_last ([#4507](https://github.com/leanprover-community/mathlib/pull/4507))
`map_head` is removed in favour of the equivalent `modify_head`.
`map_last` is renamed to `modify_last` for consistency with the other
`modify_*` functions.

### [2020-10-07 18:09:25](https://github.com/leanprover-community/mathlib/commit/a4a20ac)
doc(data/num/basic): added doc-strings to most defs ([#4439](https://github.com/leanprover-community/mathlib/pull/4439))

### [2020-10-07 16:08:11](https://github.com/leanprover-community/mathlib/commit/8f9c10f)
feat(data/matrix): add `matrix.mul_sub` and `matrix.sub_mul` ([#4505](https://github.com/leanprover-community/mathlib/pull/4505))
I was quite surprised that we didn't have this yet, but I guess they weren't needed when `sub_eq_add_neg` was still `@[simp]`.

### [2020-10-07 16:08:08](https://github.com/leanprover-community/mathlib/commit/2d34e94)
chore(*big_operators*): line length ([#4504](https://github.com/leanprover-community/mathlib/pull/4504))

### [2020-10-07 16:08:05](https://github.com/leanprover-community/mathlib/commit/6b50fb9)
fix(tactic/ring): use int_sub_hack to avoid defeq blowup ([#4503](https://github.com/leanprover-community/mathlib/pull/4503))

### [2020-10-07 14:27:03](https://github.com/leanprover-community/mathlib/commit/4db1c72)
ci(scripts/*): linting for copyright, imports, module docstrings, line length ([#4486](https://github.com/leanprover-community/mathlib/pull/4486))
This PR adds some scripts to check the `.lean` files in `src/` and `archive/` for the following issues (which are out of scope for the current linter):
- Malformed or missing copyright header
- More than one file imported per line
- Module docstring missing, or too late
- Lines of length > 100 (unless they contain `http`)
The scripts are run at the end of our "tests" job since the "lint" job usually takes longer to run. (This isn't a big deal though, since they're quick.)
Current problems are saved in the file `scripts/copy-mod-doc-exceptions.txt` and ignored so that we don't have to fix everything up front. Over time, this should get shorter as we fix things!
Separately, this also fixes some warnings in our GitHub actions workflow (see [this blog post](https://github.blog/changelog/2020-10-01-github-actions-deprecating-set-env-and-add-path-commands/)).

### [2020-10-07 14:26:58](https://github.com/leanprover-community/mathlib/commit/c9d4567)
lint(data/matrix/basic): add definition docstrings ([#4478](https://github.com/leanprover-community/mathlib/pull/4478))

### [2020-10-07 10:12:05](https://github.com/leanprover-community/mathlib/commit/6a85279)
fix(tactic/doc_commands): do not construct json by hand ([#4501](https://github.com/leanprover-community/mathlib/pull/4501))
Fixes three lines going over the 100 character limit.
The first one was a hand-rolled JSON serializer, I took the liberty to migrate it to the new `json` API.

### [2020-10-07 10:12:04](https://github.com/leanprover-community/mathlib/commit/0386ada)
chore(data/tree): linting ([#4499](https://github.com/leanprover-community/mathlib/pull/4499))

### [2020-10-07 10:12:02](https://github.com/leanprover-community/mathlib/commit/cbbc123)
lint(category_theory/equivalence): docstring and a module doc ([#4495](https://github.com/leanprover-community/mathlib/pull/4495))

### [2020-10-07 10:12:00](https://github.com/leanprover-community/mathlib/commit/8a4b491)
feat(ring_theory/witt_vector/structure_polynomial): {map_}witt_structure_int ([#4465](https://github.com/leanprover-community/mathlib/pull/4465))
This is the second PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-07 07:56:34](https://github.com/leanprover-community/mathlib/commit/e5ce9d3)
chore(data/quot): linting ([#4500](https://github.com/leanprover-community/mathlib/pull/4500))

### [2020-10-07 07:56:32](https://github.com/leanprover-community/mathlib/commit/ed9ef1b)
chore(*): normalise copyright headers ([#4497](https://github.com/leanprover-community/mathlib/pull/4497))
This diff makes sure that all files start with a copyright header
of the following shape
```
/-
Copyright ...
... Apache ...
Author...
-/
```
Some files used to have a short description of the contents
in the same comment block.
Such comments have *not* been turned into module docstrings,
but simply moved to a regular comment block below the copyright header.
Turning these comments into good module docstrings is an
effort that should be undertaken in future PRs.

### [2020-10-07 06:23:11](https://github.com/leanprover-community/mathlib/commit/3c75527)
lint(group_theory/*): docstrings and an inhabited instance ([#4493](https://github.com/leanprover-community/mathlib/pull/4493))
An inhabited instance for `presented_group`
Docstrings in `group_theory/abelianization` and `group_theory/congruence`.

### [2020-10-07 04:25:17](https://github.com/leanprover-community/mathlib/commit/8c528b9)
lint(group_theory/perm/*): docstrings ([#4492](https://github.com/leanprover-community/mathlib/pull/4492))
Adds missing docstrings in `group_theory/perm/cycles` and `group_theory/perm/sign`.

### [2020-10-07 01:06:50](https://github.com/leanprover-community/mathlib/commit/cb3118d)
chore(scripts): update nolints.txt ([#4490](https://github.com/leanprover-community/mathlib/pull/4490))
I am happy to remove some nolints for you!

### [2020-10-07 01:06:47](https://github.com/leanprover-community/mathlib/commit/2e77ef6)
lint(order/lexographic, pilex): docstrings ([#4489](https://github.com/leanprover-community/mathlib/pull/4489))
Docstrings in `order/lexographic` and `order/pilex`

### [2020-10-07 01:06:45](https://github.com/leanprover-community/mathlib/commit/afffab1)
lint(order/order_iso_nat): docstrings ([#4488](https://github.com/leanprover-community/mathlib/pull/4488))
Adds docstrings to `rel_embedding.nat_lt` and `rel_embedding.nat_gt`

### [2020-10-07 01:06:42](https://github.com/leanprover-community/mathlib/commit/93cdc3a)
feat(control/traversable/basic): composition of applicative transformations ([#4487](https://github.com/leanprover-community/mathlib/pull/4487))
Added composition law for applicative transformations, added rest of interface for coercion of applicative transformations to functions (lifted from `monoid_hom`), and proved composition was associative and has an identity.  Also corrected some documentation.

### [2020-10-07 01:06:41](https://github.com/leanprover-community/mathlib/commit/fe8b631)
lint(ring_theory/*): docstrings ([#4485](https://github.com/leanprover-community/mathlib/pull/4485))
Docstrings in `ring_theory/ideal/operations`, `ring_theory/multiplicity`, and `ring_theory/ring_invo`.

### [2020-10-06 22:45:54](https://github.com/leanprover-community/mathlib/commit/7488f8e)
lint(order/bounded_lattice): docstring ([#4484](https://github.com/leanprover-community/mathlib/pull/4484))

### [2020-10-06 22:45:52](https://github.com/leanprover-community/mathlib/commit/f4ccbdf)
feat(data/nat/basic): add_succ_lt_add ([#4483](https://github.com/leanprover-community/mathlib/pull/4483))
Add the lemma that, for natural numbers, if `a < b` and `c < d` then
`a + c + 1 < b + d` (i.e. a stronger version of `add_lt_add` for the
natural number case).  `library_search` did not find this in mathlib.

### [2020-10-06 22:45:50](https://github.com/leanprover-community/mathlib/commit/f88234d)
feat(measure_theory): integral of a non-negative function is >0 iff μ(support f) > 0 ([#4410](https://github.com/leanprover-community/mathlib/pull/4410))
Also add a few supporting lemmas

### [2020-10-06 21:23:34](https://github.com/leanprover-community/mathlib/commit/5192fd9)
feat(data/polynomial/degree/basic): add lemmas dealing with monomials, their support and their nat_degrees ([#4475](https://github.com/leanprover-community/mathlib/pull/4475))

### [2020-10-06 21:23:32](https://github.com/leanprover-community/mathlib/commit/d768e46)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_rat{_prop} ([#4464](https://github.com/leanprover-community/mathlib/pull/4464))
This is the first PR in a series on a fundamental theorem for Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-10-06 19:36:49](https://github.com/leanprover-community/mathlib/commit/7948b5a)
chore(*): fix authorship for split files ([#4480](https://github.com/leanprover-community/mathlib/pull/4480))
A few files with missing copyright headers in [#4477](https://github.com/leanprover-community/mathlib/pull/4477) came from splitting up older files, so the attribution was incorrect:
- `data/setoid/partition.lean` was split from `data/setoid.lean` in [#2853](https://github.com/leanprover-community/mathlib/pull/2853).
- `data/finset/order.lean` was split from `algebra/big_operators.lean` in [#3495](https://github.com/leanprover-community/mathlib/pull/3495).
- `group_theory/submonoid/operations.lean` was split from `group_theory/submonoid.lean` in  [#3058](https://github.com/leanprover-community/mathlib/pull/3058).

### [2020-10-06 17:40:04](https://github.com/leanprover-community/mathlib/commit/ac05889)
chore(topology/list): one import per line ([#4479](https://github.com/leanprover-community/mathlib/pull/4479))
This one seems to have slipped through previous efforts

### [2020-10-06 15:23:11](https://github.com/leanprover-community/mathlib/commit/e559ca9)
chore(*): add copyright headers ([#4477](https://github.com/leanprover-community/mathlib/pull/4477))

### [2020-10-06 15:23:09](https://github.com/leanprover-community/mathlib/commit/7416127)
feat(data/polynomial/ring_division): add multiplicity of sum of polynomials is at least minimum of multiplicities ([#4442](https://github.com/leanprover-community/mathlib/pull/4442))
I've added the lemma `root_multiplicity_add` inside `data/polynomial/ring_division` that says that the multiplicity of a root in a sum of two polynomials is at least the minimum of the multiplicities.

### [2020-10-06 12:41:50](https://github.com/leanprover-community/mathlib/commit/8d19939)
feat(*): make `int.le` irreducible ([#4474](https://github.com/leanprover-community/mathlib/pull/4474))
There's very rarely a reason to unfold `int.le` and it can create trouble: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/deep.20recursion.20was.20detected.20at.20'replace'

### [2020-10-06 12:41:47](https://github.com/leanprover-community/mathlib/commit/99e308d)
chore(parity): even and odd in semiring ([#4473](https://github.com/leanprover-community/mathlib/pull/4473))
Replaces the ad-hoc `nat.even`, `nat.odd`, `int.even` and `int.odd` by definitions that make sense in semirings and get that `odd` can be `rintros`/`rcases`'ed. This requires almost no change except that `even` is not longer usable as a dot notation (which I see as a feature since I find `even n` to be more readable than `n.even`).

### [2020-10-06 12:41:45](https://github.com/leanprover-community/mathlib/commit/1d1a041)
chore(data/mv_polynomial/basic): coeff_mul, more golfing and speedup ([#4472](https://github.com/leanprover-community/mathlib/pull/4472))

### [2020-10-06 12:41:43](https://github.com/leanprover-community/mathlib/commit/8cebd2b)
chore(algebra/algebra): Split subalgebras into their own file ([#4471](https://github.com/leanprover-community/mathlib/pull/4471))
This matches how `subring` and `submonoid` both have their own files.
This also remove `noncomputable theory` which is unnecessary for almost all the definitions

### [2020-10-06 12:41:42](https://github.com/leanprover-community/mathlib/commit/94bc31d)
lint(logic/unique): module doc, docstring ([#4461](https://github.com/leanprover-community/mathlib/pull/4461))

### [2020-10-06 12:41:40](https://github.com/leanprover-community/mathlib/commit/2fc6598)
lint(group_theory/eckmann_hilton): docs, module docs, unused argument ([#4459](https://github.com/leanprover-community/mathlib/pull/4459))

### [2020-10-06 12:41:38](https://github.com/leanprover-community/mathlib/commit/f4207aa)
feat(data/*): lemmas about lists and finsets ([#4457](https://github.com/leanprover-community/mathlib/pull/4457))
A part of [#4316](https://github.com/leanprover-community/mathlib/pull/4316)

### [2020-10-06 12:41:36](https://github.com/leanprover-community/mathlib/commit/1fa07c2)
chore(category_theory/monoidal): add module docs ([#4454](https://github.com/leanprover-community/mathlib/pull/4454))

### [2020-10-06 12:41:33](https://github.com/leanprover-community/mathlib/commit/4d9406e)
feat(geometry/euclidean/monge_point): orthocentric systems ([#4448](https://github.com/leanprover-community/mathlib/pull/4448))
Define orthocentric systems of points, and prove some basic properties
of them.  In particular, if we say that an orthocentric system
consists of four points, one of which is the orthocenter of the
triangle formed by the other three, then each of the points is the
orthocenter of the triangle formed by the other three, and all four
triangles have the same circumradius.

### [2020-10-06 10:22:31](https://github.com/leanprover-community/mathlib/commit/e9b43b6)
lint(data/equiv/ring): docstrings, inhabited ([#4460](https://github.com/leanprover-community/mathlib/pull/4460))

### [2020-10-06 10:22:29](https://github.com/leanprover-community/mathlib/commit/58a54d3)
chore(category_theory/*): doc-strings ([#4453](https://github.com/leanprover-community/mathlib/pull/4453))

### [2020-10-06 10:22:27](https://github.com/leanprover-community/mathlib/commit/6b59725)
chore(control/traversable/{basic,equiv,instances,lemmas}): linting ([#4444](https://github.com/leanprover-community/mathlib/pull/4444))
The `nolint`s in `instances.lean` are there because all the arguments need to be there for `is_lawful_traversable`.  In the same file, I moved `traverse_map` because it does not need the `is_lawful_applicative` instances.

### [2020-10-06 10:22:25](https://github.com/leanprover-community/mathlib/commit/372d294)
feat(data/finsupp): lift a collection of `add_monoid_hom`s to an `add_monoid_hom` on `α →₀ β` ([#4395](https://github.com/leanprover-community/mathlib/pull/4395))

### [2020-10-06 09:02:45](https://github.com/leanprover-community/mathlib/commit/b1d3ef9)
chore(data/mv_polynomial/basic): speedup coeff_mul ([#4469](https://github.com/leanprover-community/mathlib/pull/4469))

### [2020-10-06 09:02:43](https://github.com/leanprover-community/mathlib/commit/c08a868)
feat(trailing_degree): added two lemmas support_X, support_X_empty computing the support of X, simplified a couple of lemmas ([#4294](https://github.com/leanprover-community/mathlib/pull/4294))

### [2020-10-06 09:02:41](https://github.com/leanprover-community/mathlib/commit/fc7e943)
feat(normed_space/basic): remove localized notation ([#4246](https://github.com/leanprover-community/mathlib/pull/4246))
Remove notation for `tendsto` in `nhds`. 
Also make `is_bounded_linear_map.tendsto` protected.

### [2020-10-06 07:07:40](https://github.com/leanprover-community/mathlib/commit/32b5b68)
chore(topology/compacts): inhabit instances ([#4462](https://github.com/leanprover-community/mathlib/pull/4462))

### [2020-10-06 07:07:38](https://github.com/leanprover-community/mathlib/commit/d3b1d65)
lint(measure_theory): docstrings and style ([#4455](https://github.com/leanprover-community/mathlib/pull/4455))

### [2020-10-06 02:54:28](https://github.com/leanprover-community/mathlib/commit/523bddb)
doc(data/nat/prime, data/int/basic, data/int/modeq): docstrings ([#4445](https://github.com/leanprover-community/mathlib/pull/4445))
Filling in docstrings on `data/nat/prime`, `data/int/basic`, `data/int/modeq`.

### [2020-10-06 02:54:26](https://github.com/leanprover-community/mathlib/commit/cd78599)
lint(category_theory/monad): doc-strings ([#4428](https://github.com/leanprover-community/mathlib/pull/4428))

### [2020-10-06 02:04:28](https://github.com/leanprover-community/mathlib/commit/a228af6)
chore(scripts): update nolints.txt ([#4456](https://github.com/leanprover-community/mathlib/pull/4456))
I am happy to remove some nolints for you!

### [2020-10-06 00:55:20](https://github.com/leanprover-community/mathlib/commit/27b6c23)
lint(category_theory/limits): docstrings and inhabited instances ([#4435](https://github.com/leanprover-community/mathlib/pull/4435))

### [2020-10-06 00:09:52](https://github.com/leanprover-community/mathlib/commit/37879aa)
feat(undergrad): minimal polynomial ([#4308](https://github.com/leanprover-community/mathlib/pull/4308))
Adds minimal polynomial of endomorphisms to the undergrad list, although its use will be hard to guess for undergrads.

### [2020-10-05 23:18:37](https://github.com/leanprover-community/mathlib/commit/432da5f)
feat(measure_theory/integration): add lintegral_with_density_eq_lintegral_mul ([#4350](https://github.com/leanprover-community/mathlib/pull/4350))
This is Exercise 1.2.1 from Terence Tao's "An Epsilon of Room"

### [2020-10-05 22:01:48](https://github.com/leanprover-community/mathlib/commit/97c444e)
lint(topology/algebra): docstrings ([#4446](https://github.com/leanprover-community/mathlib/pull/4446))

### [2020-10-05 19:45:24](https://github.com/leanprover-community/mathlib/commit/21158c4)
lint(data/pnat): Docstrings and an unused argument in `pnat.basic`, `pnat.factors` ([#4443](https://github.com/leanprover-community/mathlib/pull/4443))
Adds docstrings
Changes `div_exact` from having one unused input of type `k | m` to `div_exact m k`.

### [2020-10-05 19:45:21](https://github.com/leanprover-community/mathlib/commit/45347f9)
lint(src/order/rel_iso): docstrings and inhabited ([#4441](https://github.com/leanprover-community/mathlib/pull/4441))

### [2020-10-05 19:45:19](https://github.com/leanprover-community/mathlib/commit/2127165)
chore(linear_algebra/basis): split off `linear_independent.lean` ([#4440](https://github.com/leanprover-community/mathlib/pull/4440))
The file `basis.lean` was getting rather long (1500 lines), so I decided to split it into two not as long files at a natural point: everything using `linear_independent` but not `basis` can go into a new file `linear_independent.lean`. As a result, we can import `basis.lean` a bit later in the `ring_theory` hierarchy.

### [2020-10-05 19:45:18](https://github.com/leanprover-community/mathlib/commit/88c76ab)
feat(order/filter/ultrafilter): Add variant of `exists_ultrafilter`. ([#4436](https://github.com/leanprover-community/mathlib/pull/4436))
The lemma `exists_ultrafilter` tells us that any proper filter can be extended to an ultrafilter (using Zorn's lemma). This PR adds a variant, called `exists_ultrafilter_of_finite_inter_nonempty` which says that any collection of sets `S` can be extended to an ultrafilter whenever it satisfies the property that the intersection of any finite subcollection `T` is nonempty.

### [2020-10-05 19:45:15](https://github.com/leanprover-community/mathlib/commit/9151532)
lint(order/conditionally_complete_lattice): docstrings ([#4434](https://github.com/leanprover-community/mathlib/pull/4434))

### [2020-10-05 19:45:13](https://github.com/leanprover-community/mathlib/commit/221ec60)
feat(ring_theory/ideal): ideals in product rings ([#4431](https://github.com/leanprover-community/mathlib/pull/4431))

### [2020-10-05 19:45:10](https://github.com/leanprover-community/mathlib/commit/f9e3779)
lint(category_theory/whiskering): add doc-strings ([#4417](https://github.com/leanprover-community/mathlib/pull/4417))

### [2020-10-05 19:45:08](https://github.com/leanprover-community/mathlib/commit/d2140ef)
feat(algebra/gcd_monoid): `gcd_mul_dvd_mul_gcd` ([#4386](https://github.com/leanprover-community/mathlib/pull/4386))
Adds a `gcd_monoid` version of `nat.gcd_mul_dvd_mul_gcd`

### [2020-10-05 17:20:44](https://github.com/leanprover-community/mathlib/commit/c58c4e6)
docs(tactic/{fin_cases,lift}): lint ([#4421](https://github.com/leanprover-community/mathlib/pull/4421))

### [2020-10-05 17:20:42](https://github.com/leanprover-community/mathlib/commit/e89d0ed)
chore(*/multilinear): generalize `comp_linear_map` to a family of linear maps ([#4408](https://github.com/leanprover-community/mathlib/pull/4408))
Together with [#4316](https://github.com/leanprover-community/mathlib/pull/4316) this will give us multilinear maps corresponding to monomials.

### [2020-10-05 15:18:22](https://github.com/leanprover-community/mathlib/commit/7f74e6b)
feat(data/mv_polynomial/basic): map_map_range_eq_iff ([#4438](https://github.com/leanprover-community/mathlib/pull/4438))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)

### [2020-10-05 15:18:20](https://github.com/leanprover-community/mathlib/commit/39f5d6b)
feat(data/rat/basic): denom_eq_one_iff ([#4437](https://github.com/leanprover-community/mathlib/pull/4437))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)

### [2020-10-05 15:18:18](https://github.com/leanprover-community/mathlib/commit/22398f3)
chore(src/linear_algebra): linting ([#4427](https://github.com/leanprover-community/mathlib/pull/4427))

### [2020-10-05 11:39:07](https://github.com/leanprover-community/mathlib/commit/ca269b4)
feat(linear_algebra/affine_space/finite_dimensional): collinearity ([#4433](https://github.com/leanprover-community/mathlib/pull/4433))
Define collinearity of a set of points in an affine space for a vector
space (as meaning the `vector_span` has dimension at most 1), and
prove some basic lemmas about it, leading to three points being
collinear if and only if they are not affinely independent.

### [2020-10-05 11:39:05](https://github.com/leanprover-community/mathlib/commit/b0fe280)
chore(category_theory/yoneda): doc-strings ([#4429](https://github.com/leanprover-community/mathlib/pull/4429))

### [2020-10-05 11:39:03](https://github.com/leanprover-community/mathlib/commit/1501bf6)
chore(data/fin2): linting ([#4426](https://github.com/leanprover-community/mathlib/pull/4426))

### [2020-10-05 11:39:01](https://github.com/leanprover-community/mathlib/commit/dd73dd2)
chore(linear_algebra/finsupp*): linting ([#4425](https://github.com/leanprover-community/mathlib/pull/4425))

### [2020-10-05 11:38:58](https://github.com/leanprover-community/mathlib/commit/c058524)
chore(data/fintype/basic): linting ([#4424](https://github.com/leanprover-community/mathlib/pull/4424))

### [2020-10-05 11:38:56](https://github.com/leanprover-community/mathlib/commit/70b8e82)
data(data/dlist/{basic,instances}): linting ([#4422](https://github.com/leanprover-community/mathlib/pull/4422))

### [2020-10-05 11:38:54](https://github.com/leanprover-community/mathlib/commit/da1265c)
chore(data/buffer/basic): linting ([#4420](https://github.com/leanprover-community/mathlib/pull/4420))

### [2020-10-05 11:38:52](https://github.com/leanprover-community/mathlib/commit/768ff76)
chore(data/array/lemmas): linting ([#4419](https://github.com/leanprover-community/mathlib/pull/4419))

### [2020-10-05 11:38:50](https://github.com/leanprover-community/mathlib/commit/c370bd0)
chore(data/W): linting ([#4418](https://github.com/leanprover-community/mathlib/pull/4418))

### [2020-10-05 11:38:48](https://github.com/leanprover-community/mathlib/commit/6a4fd24)
lint(category_theory/adjunction): add doc-strings ([#4415](https://github.com/leanprover-community/mathlib/pull/4415))

### [2020-10-05 11:38:46](https://github.com/leanprover-community/mathlib/commit/17b607f)
chore(algebra/direct_sum): linting ([#4412](https://github.com/leanprover-community/mathlib/pull/4412))

### [2020-10-05 11:38:43](https://github.com/leanprover-community/mathlib/commit/b44e927)
feat(data/finsupp): Make `finsupp.dom_congr` a `≃+` ([#4398](https://github.com/leanprover-community/mathlib/pull/4398))
Since this has additional structure, it may as well be part of the type

### [2020-10-05 11:38:41](https://github.com/leanprover-community/mathlib/commit/54a2c6b)
chore(algebra/group/with_one): prove `group_with_zero` earlier, drop custom lemmas ([#4385](https://github.com/leanprover-community/mathlib/pull/4385))

### [2020-10-05 11:38:39](https://github.com/leanprover-community/mathlib/commit/7236084)
refactor(linear_algebra/matrix): consistent naming ([#4345](https://github.com/leanprover-community/mathlib/pull/4345))
The naming of the maps between `linear_map` and `matrix` was a mess. This PR proposes to clean it up by standardising on two forms:
 * `linear_map.to_matrix` and `matrix.to_linear_map` are the equivalences (in the respective direction) between `M₁ →ₗ[R] M₂` and `matrix m n R`, given bases for `M₁` and `M₂`.
 * `linear_map.to_matrix'` and `matrix.to_lin'` are the equivalences between `((n → R) →ₗ[R] (m → R))` and `matrix m n R` in the respective directions
The following declarations are renamed:
 * `comp_to_matrix_mul` -> `linear_map.to_matrix'_comp`
 * `linear_equiv_matrix` -> `linear_map.to_matrix`
 * `linear_equiv_matrix_{apply,comp,id,mul,range}` -> `linear_map.to_matrix_{apply,comp,id,mul,range}`
 * `linear_equiv_matrix_symm_{apply,mul,one}` -> `matrix.to_lin_{apply,mul,one}`
 * `linear_equiv_matrix'` -> `linear_map.to_matrix'`
 * `linear_map.to_matrix_id` ->`linear_map.to_matrix'_id`
 * `matrix.mul_to_lin` -> `matrix.to_lin'_mul`
 * `matrix.to_lin` -> `matrix.mul_vec_lin` (which should get simplified to `matrix.to_lin'`)
 * `matrix.to_lin_apply` -> `matrix.to_lin'_apply`
 * `matrix.to_lin_one` -> `matrix.to_lin'_one`
 * `to_lin_to_matrix` -> `matrix.to_lin'_to_matrix'`
 * `to_matrix_to_lin` -> `linear_map.to_matrix'_to_lin'`
The following declarations are deleted as unnecessary:
 * `linear_equiv_matrix_apply'` (use `linear_map.to_matrix_apply` instead)
 * `linear_equiv_matrix'_apply` (the original `linear_map.to_matrix` doesn't exist any more)
 * `linear_equiv_matrix'_symm_apply` (the original `matrix.to_lin` doesn't exist any more)
 * `linear_map.to_matrixₗ` (use `linear_map.to_matrix'` instead)
 * `linear_map.to_matrix` (use `linear_map.to_matrix'` instead)
 * `linear_map.to_matrix_of_equiv` (use `linear_map.to_matrix'_apply` instead)
 * `matrix.eval` (use `matrix.to_lin'` instead)
 * `matrix.to_lin.is_add_monoid_hom` (use `linear_equiv.to_add_monoid_hom` instead)
 * `matrix.to_lin_{add,zero,neg}` (use `linear_equiv.map_{add,zero,neg} matrix.to_lin'` instead)
 * `matrix.to_lin_of_equiv` (use `matrix.to_lin'_apply` instead)
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Refactoring.20.60linear_map.20.3C-.3E.20matrix.60

### [2020-10-05 08:49:57](https://github.com/leanprover-community/mathlib/commit/67b312c)
chore(logic/relation): linting ([#4414](https://github.com/leanprover-community/mathlib/pull/4414))

### [2020-10-05 08:49:55](https://github.com/leanprover-community/mathlib/commit/186660c)
feat(*): assorted `simp` lemmas for IMO 2019 q1 ([#4383](https://github.com/leanprover-community/mathlib/pull/4383))
* mark some lemmas about cancelling in expressions with `(-)` as `simp`;
* simplify `a * b = a * c` to `b = c ∨ a = 0`, and similarly for
  `a * c = b * c;
* change `priority` of `monoid.has_pow` and `group.has_pow` to the
  default priority.
* simplify `monoid.pow` and `group.gpow` to `has_pow.pow`.

### [2020-10-05 08:49:53](https://github.com/leanprover-community/mathlib/commit/8f4475b)
feat(combinatorics/partitions): Add partitions ([#4303](https://github.com/leanprover-community/mathlib/pull/4303))

### [2020-10-05 07:39:36](https://github.com/leanprover-community/mathlib/commit/ca679ac)
chore(algebra/direct_limit): linting ([#4411](https://github.com/leanprover-community/mathlib/pull/4411))

### [2020-10-05 07:39:32](https://github.com/leanprover-community/mathlib/commit/581b141)
feat(data/complex): norm_cast lemmas ([#4405](https://github.com/leanprover-community/mathlib/pull/4405))
Mark various existing lemmas such as `abs_of_real` and `of_real_exp`
as `norm_cast` lemmas so that `norm_cast` and related tactics can
handle expressions involving those functions, and add lemmas
`of_real_prod` and `of_real_sum` to allow those tactics to work with
sums and products involving coercions from real to complex.

### [2020-10-05 07:39:30](https://github.com/leanprover-community/mathlib/commit/1c8bb42)
feat(linear_algebra/affine_space/finite_dimensional): more lemmas ([#4389](https://github.com/leanprover-community/mathlib/pull/4389))
Add more lemmas concerning dimensions of affine spans of finite
families of points.  In particular, various forms of the lemma that `n + 1`
points are affinely independent if and only if their `vector_span` has
dimension `n` (or equivalently, at least `n`).  With suitable
definitions, this is equivalent to saying that three points are
affinely independent or collinear, four are affinely independent or
coplanar, etc., thus preparing for giving a definition of `collinear`
(for any set of points in an affine space for a vector space) in terms
of dimension and proving some basic properties of it including
relating it to affine independence.

### [2020-10-05 07:39:28](https://github.com/leanprover-community/mathlib/commit/565e961)
feat(number_theory/arithmetic_function): Define arithmetic functions/the Dirichlet ring ([#4352](https://github.com/leanprover-community/mathlib/pull/4352))
Defines a type `arithmetic_function A` of functions from `nat` to `A` sending 0 to 0
Defines the Dirichlet ring structure on `arithmetic_function A`

### [2020-10-05 05:24:10](https://github.com/leanprover-community/mathlib/commit/9ab7f05)
feat(category_theory/limits/terminal): limit of a diagram with initial object ([#4404](https://github.com/leanprover-community/mathlib/pull/4404))
If the index category for a functor has an initial object, the image of the functor is a limit.

### [2020-10-05 05:24:08](https://github.com/leanprover-community/mathlib/commit/91d9e96)
chore(algebra/ring/basic): docs, simps ([#4375](https://github.com/leanprover-community/mathlib/pull/4375))
* add docstrings to all typeclasses in `algebra/ring/basic`;
* add `ring_hom.inhabited := ⟨id α⟩` to make linter happy;
* given `f : α →+* β`, simplify `f.to_monoid_hom` and
`f.to_add_monoid_hom` to coercions;
* add `simp` lemmas for coercions of `ring_hom.mk f _ _ _ _` to
`monoid_hom` and `add_monoid_hom`.

### [2020-10-05 05:24:06](https://github.com/leanprover-community/mathlib/commit/08cdf37)
feat(analysis/complex/roots_of_unity): complex (primitive) roots of unity ([#4330](https://github.com/leanprover-community/mathlib/pull/4330))

### [2020-10-05 04:08:17](https://github.com/leanprover-community/mathlib/commit/bf99889)
feat(category_theory/limits): lift self limit ([#4403](https://github.com/leanprover-community/mathlib/pull/4403))
A couple of little lemmas to simplify lift of a limit cone.

### [2020-10-05 02:16:27](https://github.com/leanprover-community/mathlib/commit/916b5d3)
feat(topology): completion of separable space is separable ([#4399](https://github.com/leanprover-community/mathlib/pull/4399))
API change:
* `dense` renamed to `exists_between`;
* new `dense (s : set α)` means `∀ x, x ∈ closure s`.

### [2020-10-05 01:18:46](https://github.com/leanprover-community/mathlib/commit/fc09dba)
feat(analysis/special_functions/pow): exp_mul ([#4409](https://github.com/leanprover-community/mathlib/pull/4409))
Add the lemma that `exp (x * y) = (exp x) ^ y`, for real `x` and `y`.

### [2020-10-04 20:49:23](https://github.com/leanprover-community/mathlib/commit/d13d21b)
feat(algebra/big_operators/order): bounding finite fibration cardinalities from below ([#4396](https://github.com/leanprover-community/mathlib/pull/4396))
Also including unrelated change `finset.inter_eq_sdiff_sdiff`.

### [2020-10-04 19:18:31](https://github.com/leanprover-community/mathlib/commit/f437365)
feat(linear_algebra/dimension): one-dimensional spaces ([#4400](https://github.com/leanprover-community/mathlib/pull/4400))
Add some lemmas about the vectors in spaces and subspaces of dimension
at most 1.

### [2020-10-04 15:27:55](https://github.com/leanprover-community/mathlib/commit/8f53676)
feat(data/nat): Slightly strengthen nat.coprime_of_dvd/nat.coprime_of_dvd' ([#4368](https://github.com/leanprover-community/mathlib/pull/4368))
It is sufficient to consider prime factors.
The theorems now depend on nat.prime (data/nat/prime.lean), which depends on
data/nat/gcd.lean, so I moved them to prime.lean.

### [2020-10-04 11:10:48](https://github.com/leanprover-community/mathlib/commit/729b60a)
feat(data/set/basic): subsingleton_coe ([#4388](https://github.com/leanprover-community/mathlib/pull/4388))
Add a lemma relating a set being a subsingleton set to its coercion to
a type being a subsingleton type.

### [2020-10-04 11:10:45](https://github.com/leanprover-community/mathlib/commit/e8b65e6)
feat(data/set/basic): eq_singleton_iff_unique_mem ([#4387](https://github.com/leanprover-community/mathlib/pull/4387))
We have this lemma for `finset`.  Add a version for `set` (with the
same name).

### [2020-10-04 11:10:43](https://github.com/leanprover-community/mathlib/commit/e1b1d17)
feat(algebra/group): construct `add_monoid_hom` from `map_sub` ([#4382](https://github.com/leanprover-community/mathlib/pull/4382))

### [2020-10-04 11:10:41](https://github.com/leanprover-community/mathlib/commit/231271d)
chore(data/equiv/mul_add): add more `equiv` lemmas to `mul_equiv` namespace ([#4380](https://github.com/leanprover-community/mathlib/pull/4380))
Also make `apply_eq_iff_eq` and `apply_eq_iff_eq_symm_apply` use
implicit arguments.

### [2020-10-04 11:10:39](https://github.com/leanprover-community/mathlib/commit/5d35b9a)
feat(algebra/gcd_monoid, data/*set/gcd): a few lemmas about gcds ([#4354](https://github.com/leanprover-community/mathlib/pull/4354))
Adds lemmas about gcds useful for proving Gauss's Lemma

### [2020-10-04 09:48:24](https://github.com/leanprover-community/mathlib/commit/509dd9e)
feat(linear_algebra/basic): span_singleton smul lemmas ([#4394](https://github.com/leanprover-community/mathlib/pull/4394))
Add two submodule lemmas relating `span R ({r • x})` and `span R {x}`.

### [2020-10-04 06:59:45](https://github.com/leanprover-community/mathlib/commit/c3d0835)
chore(data/mv_polynomial): rename `pderivative` to `pderiv` ([#4381](https://github.com/leanprover-community/mathlib/pull/4381))
This name matches `fderiv` and `deriv` we have in `analysis/`.

### [2020-10-04 05:39:03](https://github.com/leanprover-community/mathlib/commit/e902cae)
feat(category_theory/limits/cofinal): better API for cofinal functors ([#4276](https://github.com/leanprover-community/mathlib/pull/4276))
This PR
1. Proves that `F : C ⥤ D` being cofinal is equivalent to `colimit (F ⋙ G) ≅ colimit G` for all `G : D ⥤ E`. (Previously we just had the implication.)
2. Proves that if `F` is cofinal then `limit (F.op ⋙ H) ≅ limit H` for all `H: Dᵒᵖ ⥤ E`.

### [2020-10-04 03:45:24](https://github.com/leanprover-community/mathlib/commit/e738e90)
feat(algebra/group_power/identities): named ring identities ([#4390](https://github.com/leanprover-community/mathlib/pull/4390))
This PR adds a new file containing some "named" ring identities provable by `ring`.

### [2020-10-04 01:55:07](https://github.com/leanprover-community/mathlib/commit/f2044a5)
chore(scripts): update nolints.txt ([#4392](https://github.com/leanprover-community/mathlib/pull/4392))
I am happy to remove some nolints for you!

### [2020-10-03 23:52:40](https://github.com/leanprover-community/mathlib/commit/333c216)
chore(algebra/group/type_tags): Use ≃ instead of → ([#4346](https://github.com/leanprover-community/mathlib/pull/4346))
These functions are all equivalences, so we may as well expose that in their type
This also fills in some conversions that were missing.
Unfortunately this requires some type ascriptions in a handful of places.
It might be possible to remove these somehow.
This zulip thread contains a mwe: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20inference.20on.20.60.E2.86.92.60.20vs.20.60.E2.89.83.60/near/211922501.

### [2020-10-03 20:51:17](https://github.com/leanprover-community/mathlib/commit/a0ba5e7)
doc(data/real/*): add a few docstrings, `ereal.has_zero`, and `ereal.inhabited` ([#4378](https://github.com/leanprover-community/mathlib/pull/4378))

### [2020-10-03 20:51:15](https://github.com/leanprover-community/mathlib/commit/e593ffa)
feat(algebra/ordered*): more simp lemmas ([#4359](https://github.com/leanprover-community/mathlib/pull/4359))
Simplify expressions like `0 < a * b`, `0 < a / b`, `a / b < 1` etc. to FOL formulas of inequalities on `a`, `b`.

### [2020-10-03 18:56:38](https://github.com/leanprover-community/mathlib/commit/b790b27)
feat(slim_check): sampleable instance for generating functions and injective functions ([#3967](https://github.com/leanprover-community/mathlib/pull/3967))
This also adds `printable_prop` to trace why propositions hold or don't hold and `sampleable_ext` to allow the data structure generated and shrunken by `slim_check` to have a different type from the type we are looking for.

### [2020-10-03 15:26:49](https://github.com/leanprover-community/mathlib/commit/c39170e)
doc(*): add a few short module docstrings ([#4370](https://github.com/leanprover-community/mathlib/pull/4370))

### [2020-10-03 10:25:54](https://github.com/leanprover-community/mathlib/commit/946ab02)
chore(.github/workflows): github action for crossing off PR dependencies ([#4367](https://github.com/leanprover-community/mathlib/pull/4367))

### [2020-10-03 05:00:16](https://github.com/leanprover-community/mathlib/commit/069952b)
chore(category_theory/limits/binary_products): weaken assumptions ([#4373](https://github.com/leanprover-community/mathlib/pull/4373))
weakens the assumptions on which limits need to exist for these constructions
not much of a change but the assumptions I used were too strong so just a small fix

### [2020-10-03 05:00:15](https://github.com/leanprover-community/mathlib/commit/9e455c1)
feat(data/monoid_algebra): Allow R ≠ k in semimodule R (monoid_algebra k G) ([#4365](https://github.com/leanprover-community/mathlib/pull/4365))
Also does the same for the additive version `semimodule R (add_monoid_algebra k G)`.

### [2020-10-03 04:08:49](https://github.com/leanprover-community/mathlib/commit/6ab3eb7)
chore(category_theory/limits/equalizers): some equalizer fixups ([#4372](https://github.com/leanprover-community/mathlib/pull/4372))
A couple of minor changes for equalizers:
- Add some `simps` attributes
- Removes some redundant brackets
- Simplify the construction of an iso between cones (+dual)
- Show the equalizer fork is a limit (+dual)

### [2020-10-03 01:06:52](https://github.com/leanprover-community/mathlib/commit/6a52400)
chore(scripts): update nolints.txt ([#4371](https://github.com/leanprover-community/mathlib/pull/4371))
I am happy to remove some nolints for you!

### [2020-10-02 20:49:45](https://github.com/leanprover-community/mathlib/commit/da24add)
feat(data/multiset): ordered sum lemmas ([#4305](https://github.com/leanprover-community/mathlib/pull/4305))
Add some lemmas about products in ordered monoids and sums in ordered add monoids, and a multiset count filter lemma (and a rename of a count filter lemma)

### [2020-10-02 18:01:52](https://github.com/leanprover-community/mathlib/commit/2634c1b)
feat(category_theory/cones): map_cone_inv as an equivalence ([#4253](https://github.com/leanprover-community/mathlib/pull/4253))
When `G` is an equivalence, we have `G.map_cone_inv : cone (F ⋙ G) → cone F`, and that this is an inverse to `G.map_cone`, but not quite that these constitute an equivalence of categories. This PR fixes that.

### [2020-10-02 13:06:24](https://github.com/leanprover-community/mathlib/commit/2ce359b)
feat(data/nat/parity,data/int/parity): odd numbers ([#4357](https://github.com/leanprover-community/mathlib/pull/4357))
As discussed at
<https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/formalizing.20IMO.20problems>,
define `nat.odd` and `int.odd` to allow a more literal expression
(outside of mathlib; for example, in formal olympiad problem
statements) of results whose informal statement refers to odd numbers.
These definitions are not expected to be used in mathlib beyond the
`simp` lemmas added here that translate them back to `¬ even`.  This
is similar to how `>` is defined but almost all mathlib results are
expected to use `<` instead.
It's likely that expressing olympiad problem statements literally in
Lean will end up using some other such definitions, where avoiding API
duplication means almost everything relevant in mathlib is developed
in terms of the expansion of the definition.

### [2020-10-02 12:12:21](https://github.com/leanprover-community/mathlib/commit/53570c0)
chore(README): add zulip badge ([#4362](https://github.com/leanprover-community/mathlib/pull/4362))

### [2020-10-02 10:14:33](https://github.com/leanprover-community/mathlib/commit/eeb9bb6)
feat(data/polynomial/coeff): single-variate `C_dvd_iff_dvd_coeff` ([#4355](https://github.com/leanprover-community/mathlib/pull/4355))
Adds a single-variate version of the lemma `mv_polynomial.C_dvd_iff_dvd_coeff`
(Useful for Gauss's Lemma)

### [2020-10-02 10:14:31](https://github.com/leanprover-community/mathlib/commit/8876ba2)
feat(ring_theory/roots_of_unity): (primitive) roots of unity ([#4260](https://github.com/leanprover-community/mathlib/pull/4260))

### [2020-10-02 08:35:04](https://github.com/leanprover-community/mathlib/commit/d631126)
chore(algebra): move algebra and monoid algebra to algebra/ ([#4298](https://github.com/leanprover-community/mathlib/pull/4298))
On the basis that all the basic definitions of algebraic gadgets are otherwise in `src/algebra/`, I'd like to move `ring_theory/algebra.lean`, `ring_theory/algebra_operations.lean`, and `data/monoid_algebra.lean` there too.

### [2020-10-02 07:19:29](https://github.com/leanprover-community/mathlib/commit/1f91d93)
chore(ring_theory/power_series): rename variables ([#4361](https://github.com/leanprover-community/mathlib/pull/4361))
Use `R`, `S`, `T` for (semi)rings and `k` for a field.

### [2020-10-02 05:57:43](https://github.com/leanprover-community/mathlib/commit/140db10)
chore(data/monoid_algebra): Make the style in `lift` consistent ([#4347](https://github.com/leanprover-community/mathlib/pull/4347))
This continues from a06c87ed28989d062aa3d5324e880e62edf4a2f8, which changed add_monoid_algebra.lift but not monoid_algebra.lift.
Note only the additive proof needs `erw` (to unfold `multiplicative`).

### [2020-10-02 01:04:21](https://github.com/leanprover-community/mathlib/commit/d41f386)
chore(scripts): update nolints.txt ([#4358](https://github.com/leanprover-community/mathlib/pull/4358))
I am happy to remove some nolints for you!

### [2020-10-01 20:40:02](https://github.com/leanprover-community/mathlib/commit/4ef680b)
feat(group_theory): subgroups of real numbers ([#4334](https://github.com/leanprover-community/mathlib/pull/4334))
This fills the last hole in the "Topology of R" section of our undergrad curriculum: additive subgroups of real numbers are either dense or cyclic. Most of this PR is supporting material about ordered abelian groups. 
Co-Authored-By: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>

### [2020-10-01 18:43:08](https://github.com/leanprover-community/mathlib/commit/4851857)
chore(analysis/normed_space): define `norm_one_class` ([#4323](https://github.com/leanprover-community/mathlib/pull/4323))
Many normed rings have `∥1⊫1`. Add a typeclass mixin for this property.
API changes:
* drop `normed_field.norm_one`, use `norm_one` instead;
* same with `normed_field.nnnorm_one`;
* new typeclass `norm_one_class` for `∥1∥ = 1`;
* add `list.norm_prod_le`, `list.norm_prod_le`, `finset.norm_prod_le`, `finset.norm_prod_le'`:
  norm of the product of finitely many elements is less than or equal to the product of their norms;
  versions with prime assume that a `list` or a `finset` is nonempty, while the other versions
  assume `[norm_one_class]`;
* rename `norm_pow_le` to `norm_pow_le'`, new `norm_pow_le` assumes `[norm_one_class]` instead
  of `0 < n`;
* add a few supporting lemmas about `list`s and `finset`s.

### [2020-10-01 17:37:36](https://github.com/leanprover-community/mathlib/commit/d5834ee)
feat(data/real/irrational): add a lemma to deduce nat_degree from irrational root ([#4349](https://github.com/leanprover-community/mathlib/pull/4349))
This PR is splitted from [#4301](https://github.com/leanprover-community/mathlib/pull/4301) .

### [2020-10-01 17:37:34](https://github.com/leanprover-community/mathlib/commit/ddaa325)
feat(archive/imo): formalize IMO 1969 problem 1 ([#4261](https://github.com/leanprover-community/mathlib/pull/4261))
This is a formalization of the problem and solution for the first problem on the 1969 IMO:
Prove that there are infinitely many natural numbers $a$ with the following property: the number $z = n^4 + a$ is not prime for any natural number $n$

### [2020-10-01 16:43:25](https://github.com/leanprover-community/mathlib/commit/7767ef8)
feat(number_theory/divisors): defines the finsets of divisors/proper divisors, perfect numbers, etc. ([#4310](https://github.com/leanprover-community/mathlib/pull/4310))
Defines `nat.divisors n` to be the set of divisors of `n`, and `nat.proper_divisors` to be the set of divisors of `n` other than `n`.
Defines `nat.divisors_antidiagonal` in analogy to other `antidiagonal`s used to define convolutions
Defines `nat.perfect`, the predicate for perfect numbers

### [2020-10-01 14:28:11](https://github.com/leanprover-community/mathlib/commit/f10dda0)
feat(data/nat/basic): simp-lemmas for bit0 and bit1 mod two ([#4343](https://github.com/leanprover-community/mathlib/pull/4343))
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>

### [2020-10-01 14:28:07](https://github.com/leanprover-community/mathlib/commit/0fc7b29)
feat(data/mv_polynomial): stub on invertible elements ([#4320](https://github.com/leanprover-community/mathlib/pull/4320))
More from the Witt vector branch.

### [2020-10-01 14:28:01](https://github.com/leanprover-community/mathlib/commit/3d58fce)
feat(linear_algebra): determinant of `matrix.block_diagonal` ([#4300](https://github.com/leanprover-community/mathlib/pull/4300))
This PR shows the determinant of `matrix.block_diagonal` is the product of the determinant of each subblock.
The only contributing permutations in the expansion of the determinant are those which map each block to the same block. Each of those permutations has the form `equiv.prod_congr_left σ`. Using `equiv.perm.extend` and `equiv.prod_congr_right`, we can compute the sign of `equiv.prod_congr_left σ`, and with a bit of algebraic manipulation we reach the conclusion.

### [2020-10-01 14:27:59](https://github.com/leanprover-community/mathlib/commit/13e9cc4)
feat(linear_algebra/exterior_algebra): Add an exterior algebra ([#4297](https://github.com/leanprover-community/mathlib/pull/4297))
This adds the basic exterior algebra definitions using a very similar approach to `universal_enveloping_algebra`.
It's based off the `exterior_algebra` branch, dropping the `wedge` stuff for now as development in multilinear maps is happening elsewhere.

### [2020-10-01 14:27:57](https://github.com/leanprover-community/mathlib/commit/268073a)
feat(geometry/manifold): derivative of the zero section of the tangent bundle ([#4292](https://github.com/leanprover-community/mathlib/pull/4292))
We show that the zero section of the tangent bundle to a smooth manifold is smooth, and compute its derivative.
Along the way, some streamlining of supporting material.

### [2020-10-01 14:27:55](https://github.com/leanprover-community/mathlib/commit/11cdc8c)
feat(data/polynomial/*) : as_sum_support  ([#4286](https://github.com/leanprover-community/mathlib/pull/4286))

### [2020-10-01 12:28:37](https://github.com/leanprover-community/mathlib/commit/0ccc157)
feat(data/nat/fact, analysis/specific_limits): rename nat.fact, add few lemmas about its behaviour along at_top ([#4309](https://github.com/leanprover-community/mathlib/pull/4309))
Main content : 
- Rename `nat.fact` to `nat.factorial`, and add notation `n!` in locale `factorial`. This fixes [#2786](https://github.com/leanprover-community/mathlib/pull/2786)
- Generalize `prod_inv_distrib` to `comm_group_with_zero` *without any nonzero assumptions*
- `factorial_tendsto_at_top` : n! --> infinity as n--> infinity
- `tendsto_factorial_div_pow_self_at_top` : n!/(n^n) --> 0 as n --> infinity

### [2020-10-01 09:16:51](https://github.com/leanprover-community/mathlib/commit/9c241b0)
feat(*): a few more tests for `summable`, docstrings ([#4325](https://github.com/leanprover-community/mathlib/pull/4325))
### Important new theorems:
* `summable_geometric_iff_norm_lt_1`: a geometric series in a normed field is summable iff the norm of the common ratio is less than 1;
* `summable.tendsto_cofinite_zero`: divergence test: if `f` is a `summable` function, then `f x` tends to zero along `cofinite`;
### API change
* rename `cauchy_seq_of_tendsto_nhds` to `filter.tendsto.cauchy_seq` to enable dot syntax.

### [2020-10-01 09:16:49](https://github.com/leanprover-community/mathlib/commit/fb2b1de)
feat(algebra/ordered_ring): ask for 0 < 1 earlier. ([#4296](https://github.com/leanprover-community/mathlib/pull/4296))
It used to be that `linear_ordered_semiring` asked for `0 < 1`, while `ordered_semiring` didn't.
I'd prefer that `ordered_semiring` asks for this already:
1. because lots of interesting examples (e.g. rings of operators) satisfy this property
2. because the rest of mathlib doesn't care

### [2020-10-01 07:41:14](https://github.com/leanprover-community/mathlib/commit/9ceb114)
feat(analysis/normed_space/inner_product): Define the inner product based on `is_R_or_C` ([#4057](https://github.com/leanprover-community/mathlib/pull/4057))

### [2020-10-01 02:57:05](https://github.com/leanprover-community/mathlib/commit/1b97326)
feat(data/fintype): pigeonhole principles ([#4096](https://github.com/leanprover-community/mathlib/pull/4096))
Add pigeonhole principles for finitely and infinitely many pigeons in finitely many holes. There are also strong versions of these, which say that there is a hole containing at least as many pigeons as the average number of pigeons per hole. Fixes [#2272](https://github.com/leanprover-community/mathlib/pull/2272).

### [2020-10-01 01:07:36](https://github.com/leanprover-community/mathlib/commit/af99416)
chore(scripts): update nolints.txt ([#4341](https://github.com/leanprover-community/mathlib/pull/4341))
I am happy to remove some nolints for you!