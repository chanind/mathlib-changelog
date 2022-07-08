### [2020-07-31 19:09:51](https://github.com/leanprover-community/mathlib/commit/37ab426)
feat(complete_lattice): put supr_congr and infi_congr back ([#3646](https://github.com/leanprover-community/mathlib/pull/3646))

### [2020-07-31 17:41:12](https://github.com/leanprover-community/mathlib/commit/7e570ed)
chore(*): assorted small lemmas ([#3644](https://github.com/leanprover-community/mathlib/pull/3644))

### [2020-07-31 17:41:10](https://github.com/leanprover-community/mathlib/commit/396a764)
feat(analysis/calculus/fderiv): inversion is differentiable ([#3510](https://github.com/leanprover-community/mathlib/pull/3510))
At an invertible element `x` of a complete normed algebra, the inversion operation of the algebra is Fréchet-differentiable, with derivative `λ t, - x⁻¹ * t * x⁻¹`.

### [2020-07-31 16:13:36](https://github.com/leanprover-community/mathlib/commit/3ae893d)
fix(tactic/simps): do not reach unreachable code ([#3637](https://github.com/leanprover-community/mathlib/pull/3637))
Fixes [#3636](https://github.com/leanprover-community/mathlib/pull/3636)

### [2020-07-30 22:46:17](https://github.com/leanprover-community/mathlib/commit/f78a012)
feat(group_theory/subgroup): Add `mem_infi` and `coe_infi` ([#3634](https://github.com/leanprover-community/mathlib/pull/3634))
These already existed for submonoid, but were not lifted to subgroup.
Also adds some missing `norm_cast` attributes to similar lemmas.

### [2020-07-30 21:46:00](https://github.com/leanprover-community/mathlib/commit/985a56b)
ci(fetch_olean_cache.sh): error handling ([#3628](https://github.com/leanprover-community/mathlib/pull/3628))
Previously, the CI would be interrupted if extracting the olean cache failed. After this PR, if that step fails, all oleans are deleted and then CI continues.
I also changed the search for ancestor commits with caches to look for `.xz` files instead of `.gz` files, for consistency.

### [2020-07-30 20:16:57](https://github.com/leanprover-community/mathlib/commit/1a393e7)
feat(tactic/explode): support exploding "let" expressions and improve handling of "have" expressions ([#3632](https://github.com/leanprover-community/mathlib/pull/3632))
The current #explode has little effect on proofs using "let" expressions, e.g., #explode nat.exists_infinite_primes. #explode also
occasionally ignores certain dependencies due to macros occurring in "have" expressions. See examples below. This PR fixes these issues.
theorem foo {p q : Prop}: p → p :=
λ hp, have hh : p, from hp, hh
#explode foo -- missing dependencies at forall introduction
theorem bar {p q : Prop}: p → p :=
λ hp, (λ (hh : p), hh) hp
#explode bar -- expected behavior

### [2020-07-30 17:59:32](https://github.com/leanprover-community/mathlib/commit/43ccce5)
feat(geometry): first stab on Lie groups ([#3529](https://github.com/leanprover-community/mathlib/pull/3529))

### [2020-07-30 13:59:09](https://github.com/leanprover-community/mathlib/commit/77f3fa4)
feat(tactic/interactive_expr): add copy button to type tooltip ([#3633](https://github.com/leanprover-community/mathlib/pull/3633))
There should now be a 'copy expression' button in each tooltip which can
be used to copy the current expression to the clipboard.
![image](https://user-images.githubusercontent.com/5064353/88916012-374ff580-d25d-11ea-8260-8149966fc84a.png)
I have not tested on windows yet.
Also broke out `widget_override.goals_accomplished_message` so that
users can override it. For example:
```
meta def my_new_msg {α : Type} : widget.html α := "my message"
attribute [vm_override my_new_msg] widget_override.goals_accomplished_message
```

### [2020-07-30 13:18:00](https://github.com/leanprover-community/mathlib/commit/e7075b8)
chore(topology/algebra/ordered): fix assumptions in some lemmas ([#3629](https://github.com/leanprover-community/mathlib/pull/3629))
* Some `nhds_within_I??_eq_nhds_within_I??` lemmas assumed strict
  inequalities when this was not needed.
* Remove TFAEs that only stated equality of three `nhds_within`s.
  Prove equality of `nhds_within`s instead.
* Genralize `I??_mem_nhds_within_I??` to `order_closed_topology`.

### [2020-07-30 08:41:45](https://github.com/leanprover-community/mathlib/commit/29d5f11)
chore(algebra/group_with_zero): weaken assumptions in some lemmas ([#3630](https://github.com/leanprover-community/mathlib/pull/3630))

### [2020-07-30 07:34:56](https://github.com/leanprover-community/mathlib/commit/e1fa5cb)
feat(linear_algebra): invariant basis number property ([#3560](https://github.com/leanprover-community/mathlib/pull/3560))

### [2020-07-30 05:41:44](https://github.com/leanprover-community/mathlib/commit/03c302d)
feat(field_theory/fixed): field is separable over fixed subfield under group action ([#3568](https://github.com/leanprover-community/mathlib/pull/3568))

### [2020-07-29 23:48:24](https://github.com/leanprover-community/mathlib/commit/ef89e9a)
feat(data/qpf): compositional data type framework for inductive / coinductive types ([#3317](https://github.com/leanprover-community/mathlib/pull/3317))
First milestone of the QPF project. Includes multivariate quotients of polynomial functors and compiler for coinductive types.
Not included in this PR
 * nested inductive / coinductive data types
 * universe polymorphism with more than one variable
 * inductive / coinductive families
 * equation compiler
 * efficient byte code implementation
Those are coming in future PRs

### [2020-07-30 01:14:09+02:00](https://github.com/leanprover-community/mathlib/commit/4985ad5)
Revert "feat(topology): path connected spaces"
This reverts commit 9208c2bd1f6c8dedc0cd1646dd107842f05b0b0c.

### [2020-07-30 01:12:56+02:00](https://github.com/leanprover-community/mathlib/commit/9208c2b)
feat(topology): path connected spaces

### [2020-07-29 21:50:21](https://github.com/leanprover-community/mathlib/commit/86c83c3)
feat(topology): two missing connectedness lemmas ([#3626](https://github.com/leanprover-community/mathlib/pull/3626))
From the sphere eversion project.

### [2020-07-29 20:38:16](https://github.com/leanprover-community/mathlib/commit/ebeeee7)
feat(filters): a couple more lemmas ([#3625](https://github.com/leanprover-community/mathlib/pull/3625))
Random lemmas gathered while thinking about https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/nhds_left.20and.20nhds_right

### [2020-07-29 13:58:44](https://github.com/leanprover-community/mathlib/commit/652fb2e)
chore(doc/*): add README files ([#3623](https://github.com/leanprover-community/mathlib/pull/3623))

### [2020-07-29 11:45:51](https://github.com/leanprover-community/mathlib/commit/37e13a0)
feat(tactic/lint): quieter output by default ([#3622](https://github.com/leanprover-community/mathlib/pull/3622))
* The behavior of `lint-` hasn't changed.
* `lint` will now suppress the output of successful checks. If everything succeeds, it will print "All linting checks passed!"
* `lint+` behaves like the old `lint`. It prints a confirmation for each test.
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/quiet.20linter

### [2020-07-29 11:19:36](https://github.com/leanprover-community/mathlib/commit/b0d1d17)
feat(data/ulift): add `monad ulift` and `monad plift` ([#3588](https://github.com/leanprover-community/mathlib/pull/3588))
We add `functor`/`applicative`/`monad` instances for `ulift` and `plift`.

### [2020-07-29 08:21:11](https://github.com/leanprover-community/mathlib/commit/80f2762)
feat(topology): assorted topological lemmas ([#3619](https://github.com/leanprover-community/mathlib/pull/3619))
from the sphere eversion project

### [2020-07-29 00:35:48](https://github.com/leanprover-community/mathlib/commit/e14ba7b)
chore(scripts): update nolints.txt ([#3620](https://github.com/leanprover-community/mathlib/pull/3620))
I am happy to remove some nolints for you!

### [2020-07-28 23:25:03](https://github.com/leanprover-community/mathlib/commit/e245254)
feat(category_theory/monoidal): λ_ (𝟙_ C) = ρ_ (𝟙_ C) ([#3556](https://github.com/leanprover-community/mathlib/pull/3556))
The incredibly tedious proof from the axioms that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)` in any monoidal category.
One would hope that it falls out from a coherence theorem, but we're not close to having one, and I suspect that this result might be a step in any proof.

### [2020-07-28 22:08:48](https://github.com/leanprover-community/mathlib/commit/2e6c488)
chore(order/complete_lattice): use `Prop` args in `infi_inf` etc ([#3611](https://github.com/leanprover-community/mathlib/pull/3611))
This way one can `rw binfi_inf` first, then prove `∃ i, p i`.
Also move some code up to make it available near `infi_inf`.

### [2020-07-28 21:33:31](https://github.com/leanprover-community/mathlib/commit/aafc486)
feat(topology/ordered): intervals frontiers ([#3617](https://github.com/leanprover-community/mathlib/pull/3617))
from the sphere eversion project

### [2020-07-28 20:45:39](https://github.com/leanprover-community/mathlib/commit/5cd6eeb)
chore(ci): only store oleans in azure cache ([#3616](https://github.com/leanprover-community/mathlib/pull/3616))

### [2020-07-28 20:12:44](https://github.com/leanprover-community/mathlib/commit/4ae8752)
chore(data/mv_polynomial): use bundled homs ([#3595](https://github.com/leanprover-community/mathlib/pull/3595))
I've done a lot of the scut work, but there are still about half a dozen broken proofs, if anyone would like to take a bash at them!

### [2020-07-28 19:31:16](https://github.com/leanprover-community/mathlib/commit/b765570)
chore(topology): rename interior_eq_of_open ([#3614](https://github.com/leanprover-community/mathlib/pull/3614))
This allows to use dot notation and is more consistent with
its closed twin is_closed.closure_eq

### [2020-07-28 17:35:02](https://github.com/leanprover-community/mathlib/commit/9f51e33)
feat(measure_theory/measurable_space): introduce `filter.is_measurably_generated` ([#3594](https://github.com/leanprover-community/mathlib/pull/3594))
Sometimes I want to extract an `is_measurable` witness of a `filter.eventually` statement.

### [2020-07-28 17:35:00](https://github.com/leanprover-community/mathlib/commit/7236938)
feat(measure_theory/measure_space): add `count_apply_infinite` ([#3592](https://github.com/leanprover-community/mathlib/pull/3592))
Also add some supporting lemmas about `set.infinite`.

### [2020-07-28 17:02:06](https://github.com/leanprover-community/mathlib/commit/f6f6f8a)
feat(linear_algebra/affine_space): more affine subspace lemmas ([#3552](https://github.com/leanprover-community/mathlib/pull/3552))
Add more lemmas on affine subspaces that came up in the course of
proving existence and uniqueness of the circumcenter of a simplex in a
Euclidean space.

### [2020-07-28 15:30:51](https://github.com/leanprover-community/mathlib/commit/7848f28)
feat(category_theory): Mon_ (Type u) ≌ Mon.{u} ([#3562](https://github.com/leanprover-community/mathlib/pull/3562))
Verifying that internal monoid objects in Type are the same thing as bundled monoid objects.

### [2020-07-28 14:20:39](https://github.com/leanprover-community/mathlib/commit/9e841c8)
feat(data/list/basic): add a proof that `(a :: l) ≠ l` ([#3584](https://github.com/leanprover-community/mathlib/pull/3584))
`list.cons_ne_self` is motivated by the existence of `nat.succ_ne_self`.

### [2020-07-28 13:45:08](https://github.com/leanprover-community/mathlib/commit/f1dfece)
feat(linear_algebra/affine_space): bundled affine independent families ([#3561](https://github.com/leanprover-community/mathlib/pull/3561))
Define `affine_space.simplex` as `n + 1` affine independent points,
with the specific case of `affine_space.triangle`.  I expect most
definitions and results for these types (such as `circumcenter` and
`circumradius`, which I'm currently working on) will be specific to
the case of Euclidean affine spaces, but some make sense in a more
general affine space context.

### [2020-07-28 11:47:58](https://github.com/leanprover-community/mathlib/commit/5a876ca)
feat(category_theory): monoidal_category (C ⥤ C) ([#3557](https://github.com/leanprover-community/mathlib/pull/3557))

### [2020-07-28 10:21:52](https://github.com/leanprover-community/mathlib/commit/be99e53)
chore(ci): remove unused build step ([#3607](https://github.com/leanprover-community/mathlib/pull/3607))

### [2020-07-28 10:21:50](https://github.com/leanprover-community/mathlib/commit/f1ad7a8)
docs(topology/sheaves): better docs for presheaf ([#3596](https://github.com/leanprover-community/mathlib/pull/3596))
Add module doc-strings to two files.

### [2020-07-28 10:21:48](https://github.com/leanprover-community/mathlib/commit/35f1f63)
doc(topology/basic): docstrings for nhds and a few related lemmas ([#3548](https://github.com/leanprover-community/mathlib/pull/3548))
`nhds` was the only `def` in the file which didn't have an explanation, so I documented it.
I also went ahead and documented a few related lemmas which I felt were worth calling out.

### [2020-07-28 09:27:12](https://github.com/leanprover-community/mathlib/commit/037821b)
chore(category_theory/limits/types): remove simp lemmas ([#3604](https://github.com/leanprover-community/mathlib/pull/3604))
No one wants to see how the sausage is being made.
Or at least, no one wants `simp` to show you without asking.

### [2020-07-28 09:27:10](https://github.com/leanprover-community/mathlib/commit/a574db1)
refactor(algebra/category/*/limits): refactor concrete limits ([#3463](https://github.com/leanprover-community/mathlib/pull/3463))
We used to construct categorical limits for `AddCommGroup` and `CommRing`.
Now we construct them for
* `(Add)(Comm)Mon`
* `(Add)(Comm)Group`
* `(Comm)(Semi)Ring`
* `Module R`
* `Algebra R`
Even better, we reuse structure along the way, and show that all the relevant forgetful functors preserve limits.
We're still not at the point were this can either be done by
* automation, or
* noticing that everything is a model of a Lawvere theory
but ... maybe one day.

### [2020-07-28 08:55:31](https://github.com/leanprover-community/mathlib/commit/ce70305)
feat(category_theory): monoidal_category (C ⥤ D) when D is monoidal ([#3571](https://github.com/leanprover-community/mathlib/pull/3571))
When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.
The initial intended application is tensor product of presheaves.

### [2020-07-28 07:54:19](https://github.com/leanprover-community/mathlib/commit/3576381)
chore(ring_theory/subsemiring): tidy up docstrings ([#3580](https://github.com/leanprover-community/mathlib/pull/3580))

### [2020-07-28 02:35:47](https://github.com/leanprover-community/mathlib/commit/865e888)
chore(*): make sure definitions don't generate `s x`, `s : set _` ([#3591](https://github.com/leanprover-community/mathlib/pull/3591))
Fix the following definitions: `subtype.fintype`, `pfun.dom`, `pfun.as_subtype`, `pfun.equiv_subtype`.

### [2020-07-28 02:35:45](https://github.com/leanprover-community/mathlib/commit/d04e3fc)
feat(linear_algebra/char_poly): relates the characteristic polynomial to trace, determinant, and dimension ([#3536](https://github.com/leanprover-community/mathlib/pull/3536))
adds lemmas about the number of fixed points of a permutation
adds lemmas connecting the trace, determinant, and dimension of a matrix to its characteristic polynomial

### [2020-07-28 02:35:42](https://github.com/leanprover-community/mathlib/commit/a9481d9)
feat(analysis/convex/basic): add lemmas about transformations of convex sets and functions ([#3524](https://github.com/leanprover-community/mathlib/pull/3524))

### [2020-07-28 02:35:40](https://github.com/leanprover-community/mathlib/commit/005201a)
feat(linear_algebra/adic_completion): basic definitions about completions of modules ([#3452](https://github.com/leanprover-community/mathlib/pull/3452))

### [2020-07-28 01:10:52](https://github.com/leanprover-community/mathlib/commit/7cd1e26)
feat(data/set/basic): range_unique ([#3582](https://github.com/leanprover-community/mathlib/pull/3582))
Add a lemma on the `range` of a function from a `unique` type.

### [2020-07-28 01:10:50](https://github.com/leanprover-community/mathlib/commit/23bd09a)
chore(deprecated/ring): removing uses ([#3577](https://github.com/leanprover-community/mathlib/pull/3577))
This strips out a lot of the use of `deprecated.ring`. It's now only imported by `data.polynomial.eval`, and `ring_theory.free_ring`.

### [2020-07-28 01:10:48](https://github.com/leanprover-community/mathlib/commit/7d4d985)
chore(data/polynomial): make eval2 irreducible ([#3543](https://github.com/leanprover-community/mathlib/pull/3543))
A while back @gebner identified that [an unfortunate timeout could be avoided](https://github.com/leanprover-community/mathlib/pull/3380#issuecomment-657449148) by making `polynomial.eval2` irreducible.
This PR does that.
It's not perfect: on a few occasions I have to temporarily set it back to semireducible, because it looks like the proofs really do some heavy refling.
I'd like to make more things irreducible in the polynomial API, but not yet.

### [2020-07-28 00:39:31](https://github.com/leanprover-community/mathlib/commit/4afb214)
chore(scripts): update nolints.txt ([#3593](https://github.com/leanprover-community/mathlib/pull/3593))
I am happy to remove some nolints for you!

### [2020-07-27 20:50:19](https://github.com/leanprover-community/mathlib/commit/7556353)
feat(data/int/cast): monoid_hom.ext_int ([#3587](https://github.com/leanprover-community/mathlib/pull/3587))

### [2020-07-27 20:50:17](https://github.com/leanprover-community/mathlib/commit/864a22a)
chore(ci): delete doc generation steps ([#3586](https://github.com/leanprover-community/mathlib/pull/3586))
Doc generation will be run on schedule in another repo for security reasons.

### [2020-07-27 20:50:15](https://github.com/leanprover-community/mathlib/commit/2ecf70f)
feat(data/finset/basic): more lemmas on finsets of subtypes ([#3575](https://github.com/leanprover-community/mathlib/pull/3575))
Add two more lemmas related to `not_mem_map_subtype_of_not_property`.

### [2020-07-27 15:26:50](https://github.com/leanprover-community/mathlib/commit/3550f4f)
feat(*): remaining preliminaries for Haar measure ([#3541](https://github.com/leanprover-community/mathlib/pull/3541))
Define `has_mul (finset α)`
more convenient formulation of `is_compact.finite_compact_cover`
some lemma additions

### [2020-07-27 14:54:00](https://github.com/leanprover-community/mathlib/commit/adfcfe7)
feat(category_theory/concrete_category): epi_of_surjective ([#3585](https://github.com/leanprover-community/mathlib/pull/3585))
Also, change the proof of `mono_of_injective` to use the fact that the forgetful function reflects monomorphisms.

### [2020-07-27 12:21:03](https://github.com/leanprover-community/mathlib/commit/aeff5fc)
chore(ci): get xz archive ([#3581](https://github.com/leanprover-community/mathlib/pull/3581))
We've been storing both .gz and .xz for a while for backward compatibility but will eventually drop .gz support.

### [2020-07-27 12:20:59](https://github.com/leanprover-community/mathlib/commit/133067c)
feat(set_theory/cardinal_ordinal): cardinal.mk_finset_eq_mk ([#3578](https://github.com/leanprover-community/mathlib/pull/3578))

### [2020-07-27 11:35:50](https://github.com/leanprover-community/mathlib/commit/4a5e25c)
chore(ci): remove branch update script ([#3579](https://github.com/leanprover-community/mathlib/pull/3579))
For security reasons, this will move to a scheduled action in a different repo.

### [2020-07-27 11:35:48](https://github.com/leanprover-community/mathlib/commit/8ba59d8)
feat(measure_theory/measure_space): 2 lemmas about compact sets ([#3573](https://github.com/leanprover-community/mathlib/pull/3573))
A compact set `s` has finite (resp., zero) measure if every point of
`s` has a neighborhood within `s` of finite (resp., zero) measure.

### [2020-07-27 11:35:46](https://github.com/leanprover-community/mathlib/commit/da64c7f)
chore(order/filter/basic): use `set.eq_on` in a few lemmas ([#3565](https://github.com/leanprover-community/mathlib/pull/3565))

### [2020-07-27 10:07:11](https://github.com/leanprover-community/mathlib/commit/8c8d6a2)
feat(topology/tactic): continuity faster and more powerful ([#3545](https://github.com/leanprover-community/mathlib/pull/3545))
Following up on the recent introduction of Reid's continuity tactic in [#2879](https://github.com/leanprover-community/mathlib/pull/2879), I've made some tweaks that make it both faster and more capable.
1. we use `apply_rules {md:=semireducible}`, taking advantage of [#3538](https://github.com/leanprover-community/mathlib/pull/3538). This makes examples like
`example : continuous (λ x : ℝ, exp ((max x (-x)) + sin (cos x))^2) := by continuity` viable.
2. in `apply_rules`, if we pull in lemmas using an attribute, we reverse the list of lemmas (on the heuristic that older lemmas are more frequently applicable than newer lemmas)
3. in `continuity`, I removed the `apply_assumption` step in the `tidy` loop, since `apply_rules` is already calling `assumption`
4. also in the `tidy` loop, I moved `intro1` above `apply_rules`.
The example in the test file
```
example {κ ι : Type}
  (K : κ → Type) [∀ k, topological_space (K k)] (I : ι → Type) [∀ i, topological_space (I i)]
  (e : κ ≃ ι) (F : Π k, homeomorph (K k) (I (e k))) :
  continuous (λ (f : Π k, K k) (i : ι), F (e.symm i) (f (e.symm i))) :=
by show_term { continuity }
```
which previously timed out now runs happily even with `-T50000`.

### [2020-07-27 06:09:20](https://github.com/leanprover-community/mathlib/commit/4c0881e)
feat(measure_theory/measure_space): several lemmas about `restrict` ([#3574](https://github.com/leanprover-community/mathlib/pull/3574))

### [2020-07-27 04:33:38](https://github.com/leanprover-community/mathlib/commit/d5d463e)
chore(topology/subset_properties): +2 lemmas about `is_compact` ([#3567](https://github.com/leanprover-community/mathlib/pull/3567))
Also use `variables {s t : set α}`

### [2020-07-27 03:38:45](https://github.com/leanprover-community/mathlib/commit/8673f23)
chore(data/finsupp): move into finsupp folder ([#3566](https://github.com/leanprover-community/mathlib/pull/3566))

### [2020-07-27 02:48:13](https://github.com/leanprover-community/mathlib/commit/d6e399f)
chore(order/filter/basic): add `@[simp]` to `principal_empty/univ` ([#3572](https://github.com/leanprover-community/mathlib/pull/3572))

### [2020-07-27 01:32:13](https://github.com/leanprover-community/mathlib/commit/d06f62d)
feat(analysis/calculus/times_cont_diff): more thorough times_cont_diff interface ([#3551](https://github.com/leanprover-community/mathlib/pull/3551))
Add missing lemmas on smooth functions between vector spaces, that were necessary to solve the manifold exercises in Lftcm2020.
Changes the `{x : E}` argument from implicit to explicit in `lemma times_cont_diff_within_at.comp` and `lemma times_cont_diff_within_at.comp'`.

### [2020-07-27 00:02:05](https://github.com/leanprover-community/mathlib/commit/ca6cebc)
feat(data/nat/digits): add `last_digit_ne_zero` ([#3544](https://github.com/leanprover-community/mathlib/pull/3544))
The proof of `base_pow_length_digits_le` was refactored as suggested by @fpvandoorn in [#3498](https://github.com/leanprover-community/mathlib/pull/3498).

### [2020-07-26 23:00:29](https://github.com/leanprover-community/mathlib/commit/3c4abe0)
chore(ci): remove update_nolint action ([#3570](https://github.com/leanprover-community/mathlib/pull/3570))
this action will move to another repository for security reasons

### [2020-07-26 22:16:42](https://github.com/leanprover-community/mathlib/commit/4763feb)
chore(topology/basic): directly use `self_of_nhds` in `eq_of_nhds` ([#3569](https://github.com/leanprover-community/mathlib/pull/3569))

### [2020-07-26 17:38:11](https://github.com/leanprover-community/mathlib/commit/a6d3d65)
chore(data/set/intervals): more `simp` lemmas ([#3564](https://github.com/leanprover-community/mathlib/pull/3564))

### [2020-07-26 14:16:23](https://github.com/leanprover-community/mathlib/commit/692a689)
feat(data/list/chain): chain'.append_overlap ([#3559](https://github.com/leanprover-community/mathlib/pull/3559))

### [2020-07-26 10:41:56](https://github.com/leanprover-community/mathlib/commit/f4106af)
feat(order/filters, topology): relation between neighborhoods of a in [a, u), [a, u] and [a,+inf) + various nhds_within lemmas ([#3516](https://github.com/leanprover-community/mathlib/pull/3516))
Content : 
- two lemmas about filters, namely `tendsto_sup` and `eventually_eq_inf_principal_iff`
- a few lemmas about `nhds_within`
- duplicate and move parts of the lemmas `tfae_mem_nhds_within_[Ioi/Iio/Ici/Iic]` that only require `order_closed_topology α` instead of `order_topology α`. This allows to turn any left/right neighborhood of `a` into its "canonical" form (i.e `Ioi`/`Iio`/`Ici`/`Iic`) with a weaker assumption than before

### [2020-07-26 09:05:48](https://github.com/leanprover-community/mathlib/commit/f95e90b)
chore(order/liminf_limsup): use dot notation and `order_dual` ([#3555](https://github.com/leanprover-community/mathlib/pull/3555))
## New
* `filter.has_basis.Limsup_eq_infi_Sup`
## Rename
### Namespace `filter`
* `is_bounded_of_le` → `is_bounded_mono`;
* `is_bounded_under_of_is_bounded` → `is_bounded.is_bounded_under`;
* `is_cobounded_of_is_bounded` → `is_bounded.is_cobounded_flip`;
* `is_cobounded_of_le` → `is_cobounded.mono`;
### Top namespace
* `is_bounded_under_le_of_tendsto` → `filter.tendsto.is_bounded_under_le`;
* `is_cobounded_under_ge_of_tendsto` → `filter.tendsto.is_cobounded_under_ge`;
* `is_bounded_under_ge_of_tendsto` → `filter.tendsto.is_bounded_under_ge`;
* `is_cobounded_under_le_of_tendsto` → `filter.tendsto.is_cobounded_under_le`.
## Remove
* `filter.is_trans_le`, `filter.is_trans_ge`: we have both
  in `order/rel_classes`.

### [2020-07-26 09:05:46](https://github.com/leanprover-community/mathlib/commit/493a5b0)
feat(data/set/lattice): add lemmas `disjoint.union_left/right` etc ([#3554](https://github.com/leanprover-community/mathlib/pull/3554))

### [2020-07-26 07:41:04](https://github.com/leanprover-community/mathlib/commit/3c1f332)
feat(tactic/to_additive): automate substructure naming ([#3553](https://github.com/leanprover-community/mathlib/pull/3553))
This is all @cipher1024's work, improving `to_additive` to correctly generate names when we're talking about structures (rather than just operations).

### [2020-07-26 07:03:20](https://github.com/leanprover-community/mathlib/commit/d7fcd8c)
chore(analysis/normed_space): remove 2 `norm_zero` lemmas ([#3558](https://github.com/leanprover-community/mathlib/pull/3558))
We have a general `norm_zero` lemma and these lemmas are not used
before we introduce `normed_group` instances.

### [2020-07-26 02:39:04](https://github.com/leanprover-community/mathlib/commit/11179d5)
feat(algebra/category/Group/*): compare categorical (co)kernels/images with the usual notions ([#3443](https://github.com/leanprover-community/mathlib/pull/3443))

### [2020-07-25 15:53:29](https://github.com/leanprover-community/mathlib/commit/8582b06)
feat(logic/basic): mark cast_eq as a `simp` lemma ([#3547](https://github.com/leanprover-community/mathlib/pull/3547))
The theorem `cast_eq` is in core and says `theorem cast_eq : ∀ {α : Sort u} (h : α = α) (a : α), cast h a = a`

### [2020-07-25 15:23:48](https://github.com/leanprover-community/mathlib/commit/3484194)
chore(geometry/manifold/real_instance): remove global fact instance ([#3549](https://github.com/leanprover-community/mathlib/pull/3549))
Remove global `fact` instance that was used to get a manifold structure on `[0, 1]`, and register only the manifold structure.

### [2020-07-25 10:09:45](https://github.com/leanprover-community/mathlib/commit/e90c7b9)
feat(data/num/prime): kernel-friendly decision procedure for prime ([#3525](https://github.com/leanprover-community/mathlib/pull/3525))

### [2020-07-25 07:31:35](https://github.com/leanprover-community/mathlib/commit/0379d3a)
chore(*): minor import cleanup ([#3546](https://github.com/leanprover-community/mathlib/pull/3546))

### [2020-07-25 06:33:04](https://github.com/leanprover-community/mathlib/commit/2a456a9)
feat(topology/*, geometry/*): missing lemmas ([#3528](https://github.com/leanprover-community/mathlib/pull/3528))
Grab bag of missing lemmas on topology and geometry that were needed for the manifold exercises in Lftcm2020.

### [2020-07-25 06:33:02](https://github.com/leanprover-community/mathlib/commit/12a7ce3)
feat(category_theory/isomorphism): lemmas about cancelling isomorphisms ([#3436](https://github.com/leanprover-community/mathlib/pull/3436))

### [2020-07-25 05:30:35](https://github.com/leanprover-community/mathlib/commit/2d29f80)
feat(data/finsupp): lattice structure on finsupp ([#3335](https://github.com/leanprover-community/mathlib/pull/3335))
adds facts about order_isos respecting lattice operations
defines lattice structures on finsupps to N
constructs an order_iso out of finsupp.to_multiset

### [2020-07-25 04:26:19](https://github.com/leanprover-community/mathlib/commit/8d55eda)
feat(topology/tactic): `continuity` tactic ([#2879](https://github.com/leanprover-community/mathlib/pull/2879))

### [2020-07-24 21:19:13](https://github.com/leanprover-community/mathlib/commit/6f9da35)
feat(tactic/simps): improvements ([#3477](https://github.com/leanprover-community/mathlib/pull/3477))
Features:
* `@[simps]` will look for `has_coe_to_sort` and `has_coe_to_fun` instances, and use those instead of direct projections. This should make it way more applicable for `equiv`, `local_equiv` and all other structures that coerce to a function (and for the few structures that coerce to a type). This works out-of-the-box without special configuration.
* Use `has_mul.mul`, `has_zero.zero` and all the other "notation projections" instead of the projections directly. This should make it more useful in category theory and the algebraic hierarchy (note: the `[notation_class]` attribute still needs to be added to all notation classes not defined in `init.core`)
* Add an easy way to specify custom projections of structures (like using `⇑e.symm` instead of `e.inv_fun`). They have to be definitionally equal to the projection.
Minor changes:
* Change the syntax to specify options.
* `prod` (and `pprod`) are treated as a special case: we do not recursively apply projections of these structure. This was the most common reason that we had to write the desired projections manually. You can still override this behavior by writing out the projections manually.
* A flag to apply `simp` to the rhs of the generated lemma, so that they are in simp-normal-form.
* Added an options to add more attributes to the generated lemmas
* Added an option which definitions to unfold to determine whether a type is a function type. By default it will unfold reducible definitions and instances (but e.g. not `set α`)
* Added an option to unfold definitions in the declaration to determine whether it is a constructor. (default: none)
* Added an option to not fully-apply the terms in the generated lemmas.
Design decisions:
* For every field in a structure there is a specified "projection expression" that acts as the projection for that field. For most fields this is just the projection of the structure, but this will be automatically overridden under certain conditions, like a coercion to functions/sorts existing, or a notation typeclass existing for a certain field.
* The first time you call `simps` for a specific structure, these projection expressions are cached using an attribute for that structure, and it is assumed you want to use the same projection expressions every time.
* You can also manually specify the projection. See Note [custom simps projection].

### [2020-07-24 18:42:44](https://github.com/leanprover-community/mathlib/commit/4d81149)
chore(ring_theory/prod): move file to algebra/ring/prod ([#3540](https://github.com/leanprover-community/mathlib/pull/3540))

### [2020-07-24 17:03:22](https://github.com/leanprover-community/mathlib/commit/47efcf3)
chore(algebraic_geometry/presheafed_space): use projection rather than fancy coercion ([#3507](https://github.com/leanprover-community/mathlib/pull/3507))
We'd gone to great effort when writing `PresheafedSpace` to create a coercion from morphisms of `PresheafedSpace`s to morphisms in `Top`.
It's hard to read, it's fragile.
So this PR rips out that coercion, and renames the "continuous map between base spaces" field from `f` to `base`, and uses that throughout.

### [2020-07-24 13:04:01](https://github.com/leanprover-community/mathlib/commit/229cf6e)
feat(data/polynomial): irreducible_of_irreducible_mod_prime ([#3539](https://github.com/leanprover-community/mathlib/pull/3539))
I was waiting on this, an exercise from Johan's tutorial at LftCM, to see if a participant would PR it. Perhaps not, so I'll contribute this now.

### [2020-07-24 13:03:59](https://github.com/leanprover-community/mathlib/commit/579b142)
feat(field_theory/fixed): a field is normal over the fixed subfield under a group action ([#3520](https://github.com/leanprover-community/mathlib/pull/3520))
From my Galois theory repo.

### [2020-07-24 11:52:28](https://github.com/leanprover-community/mathlib/commit/a6ad904)
feat(tactic/apply_rules): allow apply_cfg argument ([#3538](https://github.com/leanprover-community/mathlib/pull/3538))
This allows passing an `apply_cfg` argument to `apply_rules` (and simplifies the configuration argument to `solve_by_elim`).
This is prompted by the desire to try using `apply_rules` with `md := semireducible` when working on the `continuity` tactic.

### [2020-07-24 11:07:23](https://github.com/leanprover-community/mathlib/commit/2d47d0c)
chore(measure_theory/indicator_function): split into 2 files deps: 3503 ([#3509](https://github.com/leanprover-community/mathlib/pull/3509))
Split `measure_theory/indicator_function` into 2 files.
This file formulated all lemmas for `measure.ae` but they hold for any filter.

### [2020-07-24 09:01:42](https://github.com/leanprover-community/mathlib/commit/6fe81bd)
chore(*): remove `plift` from some lemmas about `infi`/`supr` ([#3503](https://github.com/leanprover-community/mathlib/pull/3503))
Now `supr_eq_supr_finset` etc assume `ι` is a `Type*` and don't use `plift`. If you want
to apply it to a `Sort*`, rewrite on `equiv.plift.surjective.supr_comp` first.
## Full list of API changes:
### `data/equiv/basic`
* `equiv.ulift`: change the order of universe arguments to match `ulift`;
* add `coe_ulift`, `coe_plift`, `coe_ulift_symm`, `coe_plift_symm`;
### `data/finset/lattice`
* `supr_eq_supr_finset`, `infi_eq_infi_finset`: assume `ι` is a `Type*`, avoid `plift`;
* `Union_eq_Union_finset`, `Inter_eq_Inter_finset`: same as above;
### `data/set/basic`
* `function.surjective.range_comp`: generalize to `Sort*` for 2 of 3 arguments;
### `order/complete_lattice`
* remove `supr_congr` and `infi_congr`;
* add `function.surjective.supr_comp` and `function.surjective.infi_comp`.

### [2020-07-24 08:19:54](https://github.com/leanprover-community/mathlib/commit/499cb9b)
refactor(data/nat/digits): refactor into sections ([#3527](https://github.com/leanprover-community/mathlib/pull/3527))
Refactor `data.nat.digits` into sections and grouping similar lemmas together.

### [2020-07-24 07:44:28](https://github.com/leanprover-community/mathlib/commit/5d41ec7)
feat(ring_theory/polynomial/basic): remove unnecessary commutativity assumption ([#3535](https://github.com/leanprover-community/mathlib/pull/3535))

### [2020-07-24 00:41:59](https://github.com/leanprover-community/mathlib/commit/c88f8be)
chore(scripts): update nolints.txt ([#3534](https://github.com/leanprover-community/mathlib/pull/3534))
I am happy to remove some nolints for you!

### [2020-07-23 23:18:12](https://github.com/leanprover-community/mathlib/commit/bad4f97)
feat(algebra/direct_sum): Add ⨁ notation ([#3473](https://github.com/leanprover-community/mathlib/pull/3473))
This uses the unicode character "n-ary circled plus operator", which seems to be the usual symbol for this operation

### [2020-07-23 19:52:19](https://github.com/leanprover-community/mathlib/commit/289d17c)
chore(data/equiv/basic): avoid `λ ⟨a, b⟩` in some defs, add `simp` lemmas ([#3530](https://github.com/leanprover-community/mathlib/pull/3530))

### [2020-07-23 18:29:16](https://github.com/leanprover-community/mathlib/commit/2d395a9)
refactor(algebra/pi_instance): delete pi_instance file, and move instances to group/ring etc appropriately ([#3513](https://github.com/leanprover-community/mathlib/pull/3513))

### [2020-07-23 14:56:16](https://github.com/leanprover-community/mathlib/commit/ed33a99)
chore(measure_theory/l1_space): make `measure` argument of `integrable` optional ([#3508](https://github.com/leanprover-community/mathlib/pull/3508))
Other changes:
* a few trivial lemmas;
* fix notation for `∀ᵐ`: now Lean can use it for printing, not only
  for parsing.

### [2020-07-23 13:44:07](https://github.com/leanprover-community/mathlib/commit/396a66a)
chore(order/filter/*): use `[nonempty _]` instead of `(_ : nonempty _)` ([#3526](https://github.com/leanprover-community/mathlib/pull/3526))
In most cases Lean can find an instance automatically.

### [2020-07-23 11:08:28](https://github.com/leanprover-community/mathlib/commit/b9beca0)
chore(set_theory/ordinal): split into multiple files ([#3517](https://github.com/leanprover-community/mathlib/pull/3517))
Split the file `ordinal.lean` into three files, and add docstrings for all definitions and file-level docstrings. This is just shuffling things around: no new content, no erased content.

### [2020-07-23 08:52:03](https://github.com/leanprover-community/mathlib/commit/79df8cc)
refactor(order/filter/at_top): import order.filter.bases ([#3523](https://github.com/leanprover-community/mathlib/pull/3523))
This way we can use facts about `filter.has_basis` in `filter.at_top`.
Also generalize `is_countably_generated_at_top_finset_nat`
to `at_top` filter on any `encodable` type.

### [2020-07-23 07:50:13](https://github.com/leanprover-community/mathlib/commit/d974457)
feat(ring_theory/ideal_over): a prime ideal lying over a maximal ideal is maximal ([#3488](https://github.com/leanprover-community/mathlib/pull/3488))
By making the results in `ideal_over.lean` a bit more general, we can transfer to quotient rings. This allows us to prove a strict inclusion `I < J` of ideals in `S` results in a strict inclusion `I.comap f < J.comap f` if `R` if `f : R ->+* S` is nice enough. As a corollary, a prime ideal lying over a maximal ideal is maximal.

### [2020-07-23 02:51:42](https://github.com/leanprover-community/mathlib/commit/7397db7)
chore(data/sym2) : simplify proofs ([#3522](https://github.com/leanprover-community/mathlib/pull/3522))
This shouldn't change any declarations, only proofs.

### [2020-07-23 01:10:58](https://github.com/leanprover-community/mathlib/commit/c149839)
chore(topology/uniform_space/basic): golf a proof ([#3521](https://github.com/leanprover-community/mathlib/pull/3521))
Also prove that a `subsingleton` has a unique `topological_space` structure.

### [2020-07-23 01:10:56](https://github.com/leanprover-community/mathlib/commit/4a918fb)
chore(order/complete_lattice): add `supr/infi_of_empty(')` ([#3519](https://github.com/leanprover-community/mathlib/pull/3519))

### [2020-07-23 01:10:54](https://github.com/leanprover-community/mathlib/commit/827fcd0)
feat(analysis/convex/basic): add lemmas about convex combination of endpoints of intervals ([#3482](https://github.com/leanprover-community/mathlib/pull/3482))

### [2020-07-22 23:58:19](https://github.com/leanprover-community/mathlib/commit/fbcd890)
chore(data/subtype,order/complete_lattice): use `coe` instead of `subtype.val` ([#3518](https://github.com/leanprover-community/mathlib/pull/3518))

### [2020-07-22 19:30:06](https://github.com/leanprover-community/mathlib/commit/1dd69d3)
refactor(data/polynomial): re-organizing ([#3512](https://github.com/leanprover-community/mathlib/pull/3512))
This builds on [#3407](https://github.com/leanprover-community/mathlib/pull/3407), trying to get related material closer together. 
There shouldn't be any change to the set of declarations, just the order they come in and the imports required to get them.
The major changes are:
1. `data.polynomial.derivative` now has much weaker imports
2. generally, material has been moved "upwards" to the first place it can be done (a lot of material moved out of `data.polynomial.degree` into `data.polynomial.degree.basic` -- essentially `degree` is the material about `degree` that also needs `eval` and friends; a further rename might be appropriate)
3. some of the later material is no longer a big chain of linear dependencies, but compiles separately

### [2020-07-22 16:16:15](https://github.com/leanprover-community/mathlib/commit/36ea9e8)
chore(*): cleanup imports ([#3511](https://github.com/leanprover-community/mathlib/pull/3511))
A not-very-interesting cleanup of imports.
I deleted 
```
instance orbit_fintype (b : β) [fintype α] [decidable_eq β] :	
  fintype (orbit α b) := set.fintype_range _
```
which wasn't being used, for the sake of not having to import everything about finiteness into `algebra.group_action`.

### [2020-07-22 16:16:13](https://github.com/leanprover-community/mathlib/commit/a8cedf9)
feat(data/nat/digits): a number is bigger than base^(digits length - 1) ([#3498](https://github.com/leanprover-community/mathlib/pull/3498))

### [2020-07-22 14:52:45](https://github.com/leanprover-community/mathlib/commit/acc2802)
feat(tactic/extract_goal): remove annoying spaces ([#3514](https://github.com/leanprover-community/mathlib/pull/3514))
closes [#3375](https://github.com/leanprover-community/mathlib/pull/3375)

### [2020-07-22 14:04:33](https://github.com/leanprover-community/mathlib/commit/a971a88)
refactor(linear_algebra/nonsingular_inverse, data/matrix/basic): update_* rectangular matrices ([#3403](https://github.com/leanprover-community/mathlib/pull/3403))

### [2020-07-22 11:32:56](https://github.com/leanprover-community/mathlib/commit/90d3386)
feat(category_theory/kernels): compute kernel (f ≫ g) when one is an iso ([#3438](https://github.com/leanprover-community/mathlib/pull/3438))

### [2020-07-22 10:18:14](https://github.com/leanprover-community/mathlib/commit/39f8f02)
refactor(algebra/big_operators): split file, reduce imports ([#3495](https://github.com/leanprover-community/mathlib/pull/3495))
I've split up `algebra.big_operators`. It wasn't completely obvious how to divide it up, but this is an attempt to balance coherence / file size / minimal imports.

### [2020-07-22 08:55:49](https://github.com/leanprover-community/mathlib/commit/197b501)
feat(tactic/extract_goal): better support for `let` expressions ([#3496](https://github.com/leanprover-community/mathlib/pull/3496))
Improve treatment of let expressions [#3375](https://github.com/leanprover-community/mathlib/pull/3375)

### [2020-07-22 05:08:37](https://github.com/leanprover-community/mathlib/commit/64335de)
chore(topology/category/): switch to bundled morphisms in Top ([#3506](https://github.com/leanprover-community/mathlib/pull/3506))
This is a natural follow-up to @Nicknamen's recent PRs splitting bundled continuous maps out of `compact_open`.
There is a slight regression in `algebraic_geometry.presheafed_space` and `algebraic_geometry.stalks`, requiring a more explicit coercion. I'd encourage reviewers to ignore this, as I'll make a separate PR simplifying this (basically: having a coercion from morphisms of `PresheafedSpace`s to morphisms of `Top`s is unrealistically ambitious, and moreover harder to read, than just using the projection notation, and removing it makes everything easier).

### [2020-07-22 03:47:11](https://github.com/leanprover-community/mathlib/commit/dced343)
feat(data/list/basic): induction from both ends ([#3448](https://github.com/leanprover-community/mathlib/pull/3448))
This was originally an induction principle on palindromes, but researching Coq solutions made me realize that weakening the statement made it simpler and much easier to prove.
- ["The way we proceeded was to prove first an induction principle for lists, considering insertions at both ends..."][1]
- ["... generalizing a single variable in that definition would create another inductive definition of a list."][2]
[1]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html
[2]: https://danilafe.com/blog/coq_palindrome/
This also adds the lemmas `length_init` and `init_append_last`.

### [2020-07-22 02:38:08](https://github.com/leanprover-community/mathlib/commit/55e7dcc)
fix(ring_theory/jacobson): Clean up documentation in Jacobson Ring definitions ([#3501](https://github.com/leanprover-community/mathlib/pull/3501))
Fixes to formatting and documentation found after merging the definition of Jacobson Rings in https://github.com/leanprover-community/mathlib/pull/3404

### [2020-07-22 01:12:15](https://github.com/leanprover-community/mathlib/commit/314b209)
chore(scripts): update nolints.txt ([#3505](https://github.com/leanprover-community/mathlib/pull/3505))
I am happy to remove some nolints for you!

### [2020-07-22 00:27:14](https://github.com/leanprover-community/mathlib/commit/2219dc1)
feat(tactic/linarith): put certificate generation in tactic monad ([#3504](https://github.com/leanprover-community/mathlib/pull/3504))

### [2020-07-22 00:27:12](https://github.com/leanprover-community/mathlib/commit/219e298)
feat(ring_theory/discrete_valuation_ring): add DVR ([#3476](https://github.com/leanprover-community/mathlib/pull/3476))

### [2020-07-21 23:16:29](https://github.com/leanprover-community/mathlib/commit/84d6497)
fix(algebra/ring): add coe_neg_one lemma to units ([#3489](https://github.com/leanprover-community/mathlib/pull/3489))
Follow up to [#3472](https://github.com/leanprover-community/mathlib/pull/3472) - adds `coe_neg_one`, which allows `norm_cast` to handle hypotheses like `↑-1 = 1`

### [2020-07-21 22:26:30](https://github.com/leanprover-community/mathlib/commit/e448bb1)
feat(tactic/linarith): modularize coefficient oracle ([#3502](https://github.com/leanprover-community/mathlib/pull/3502))
This makes it easy to plug an alternate certificate search method (e.g. simplex-based) into `linarith`, should one desire.

### [2020-07-21 21:58:58](https://github.com/leanprover-community/mathlib/commit/c6aa8e7)
feat(algebra/invertible): invertible elements are units ([#3499](https://github.com/leanprover-community/mathlib/pull/3499))

### [2020-07-21 21:58:56](https://github.com/leanprover-community/mathlib/commit/2fb6a05)
feat(group_theory/semidirect_product): semidirect_product.map ([#3492](https://github.com/leanprover-community/mathlib/pull/3492))

### [2020-07-21 21:29:16](https://github.com/leanprover-community/mathlib/commit/dfef07a)
chore(analysis/special_functions): moved trig vals out of real.pi, added new trig vals ([#3497](https://github.com/leanprover-community/mathlib/pull/3497))
Moved trigonometric lemmas from real.pi to analysis.special_functions.trigonometric. Also added two new trig lemmas, tan_pi_div_four and arctan_one, to analysis.special_functions.trigonometric.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Trig.20function.20values

### [2020-07-21 16:25:32](https://github.com/leanprover-community/mathlib/commit/c47d1d0)
feat(data/{mv_}polynomial): make args to aeval implicit ([#3494](https://github.com/leanprover-community/mathlib/pull/3494))

### [2020-07-21 16:25:30](https://github.com/leanprover-community/mathlib/commit/7efdd99)
feat(algebra/invertible): lemmas ([#3493](https://github.com/leanprover-community/mathlib/pull/3493))
Coauthored by: Johan Commelin <johan@commelin.net>

### [2020-07-21 15:23:28](https://github.com/leanprover-community/mathlib/commit/5776f4c)
feat(topology): more lemmas about Ici and Iic neighborhoods ([#3474](https://github.com/leanprover-community/mathlib/pull/3474))
Main feature :  add `tfae_mem_nhds_within_Ici` and `tfae_mem_nhds_within_Iic`, analogous to the existing `tfae_mem_nhds_within_Ioi` and `tfae_mem_nhds_within_Iio`, as well as related lemmas (again imitating the open case)
I also added a few lemmas in `data/set/intervals/basic.lean` that were useful for this and a few upcoming PRs

### [2020-07-21 12:58:53](https://github.com/leanprover-community/mathlib/commit/49049e4)
feat(topology): implemented continuous bundled maps ([#3486](https://github.com/leanprover-community/mathlib/pull/3486))
In this PR we defined continuous bundled maps, adapted the file `compact_open` accordingly, and proved instances of algebraic structures over the type `continuous_map` of continuous bundled maps. This feature was suggested on Zulip multiple times, see for example https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Continuous.20maps

### [2020-07-21 11:50:25](https://github.com/leanprover-community/mathlib/commit/5c55e15)
feat(data/finset/intervals): Lemma about filter and Ico ([#3479](https://github.com/leanprover-community/mathlib/pull/3479))
Add "if you filter an Ico based on being less than or equal to its bottom element, you get the singleton bottom element".

### [2020-07-21 10:37:37](https://github.com/leanprover-community/mathlib/commit/d57130b)
feat(field_theory/mv_polynomial): char_p instance ([#3491](https://github.com/leanprover-community/mathlib/pull/3491))

### [2020-07-21 09:25:11](https://github.com/leanprover-community/mathlib/commit/1a31e69)
chore(algebra/group/anti_hom): remove is_group_anti_hom ([#3485](https://github.com/leanprover-community/mathlib/pull/3485))
`is_group_anti_hom` is no longer used anywhere, so I'm going to count it as deprecated and propose removing it.

### [2020-07-21 08:38:58](https://github.com/leanprover-community/mathlib/commit/3169970)
feat(category_theory/kernels): helper lemmas for constructing kernels ([#3439](https://github.com/leanprover-community/mathlib/pull/3439))
This does for kernels what [#3398](https://github.com/leanprover-community/mathlib/pull/3398) did for pullbacks.

### [2020-07-21 07:47:44](https://github.com/leanprover-community/mathlib/commit/d174d3d)
refactor(linear_algebra/*): postpone importing material on direct sums ([#3484](https://github.com/leanprover-community/mathlib/pull/3484))
This is just a refactor, to avoid needing to develop material on direct sums before we can even define an algebra.

### [2020-07-21 04:06:36](https://github.com/leanprover-community/mathlib/commit/c71e67a)
feat(ring_theory/jacobson): definition of Jacobson rings ([#3404](https://github.com/leanprover-community/mathlib/pull/3404))

### [2020-07-21 01:55:48](https://github.com/leanprover-community/mathlib/commit/0322d89)
refactor(topology/algebra/monoid): changed topological_monoid into has_continuous_mul ([#3481](https://github.com/leanprover-community/mathlib/pull/3481))

### [2020-07-21 01:05:11](https://github.com/leanprover-community/mathlib/commit/079d409)
chore(scripts): update nolints.txt ([#3483](https://github.com/leanprover-community/mathlib/pull/3483))
I am happy to remove some nolints for you!

### [2020-07-21 01:05:09](https://github.com/leanprover-community/mathlib/commit/6721ddf)
refactor(ring_theory): remove unbundled leftovers in `ideal.quotient` ([#3467](https://github.com/leanprover-community/mathlib/pull/3467))
This PR aims to smooth some corners in the `ideal.quotient` namespace left by the move to bundled `ring_hom`s. The main irritation is the ambiguity between different ways to map `x : R` to the quotient ring: `quot.mk`, `quotient.mk`, `quotient.mk'`, `submodule.quotient.mk`, `ideal.quotient.mk` and `ideal.quotient.mk_hom`, which caused a lot of duplication and more awkward proofs.
The specific changes are:
 * delete function `ideal_quotient.mk`
 * rename ring hom `ideal.quotient.mk_hom` to `ideal.quotient.mk`
 * make new `ideal_quotient.mk` the `simp` normal form
 * delete obsolete `mk_eq_mk_hom`
 * delete obsolete `mk_...` `simp` lemmas (use `ring_hom.map_...` instead)
 * delete `quotient.map_mk` which was unused and had no lemmas (`ideal.map quotient.mk` is used elsewhere)

### [2020-07-21 01:05:07](https://github.com/leanprover-community/mathlib/commit/564ab02)
feat(category_theory/kernels): cokernel (image.ι f) ≅ cokernel f ([#3441](https://github.com/leanprover-community/mathlib/pull/3441))

### [2020-07-20 23:42:11](https://github.com/leanprover-community/mathlib/commit/32c082f)
fix(tactic/library_search): group monotone lemmas with le lemmas ([#3471](https://github.com/leanprover-community/mathlib/pull/3471))
This lets `library_search` use `monotone` lemmas to prove `\le` goals, and vice versa, resolving a problem people were experiencing in Patrick's exercises at LftCM2020:
```
import order.filter.basic
open filter
example {α β γ : Type*} {A : filter α} {B : filter β} {C : filter γ} {f : α → β} {g : β → γ}
  (hf : tendsto f A B) (hg : tendsto g B C) : tendsto (g ∘ f) A C :=
calc
map (g ∘ f) A = map g (map f A) : by library_search
          ... ≤ map g B         : by library_search!
          ... ≤ C               : by library_search!
```

### [2020-07-20 22:17:29](https://github.com/leanprover-community/mathlib/commit/2915fae)
feat(data/finset/basic): Cardinality of intersection with singleton ([#3480](https://github.com/leanprover-community/mathlib/pull/3480))
Intersecting with a singleton produces a set of cardinality either 0 or 1.

### [2020-07-20 20:30:53](https://github.com/leanprover-community/mathlib/commit/1f74ddd)
feat(topology/local_extr): add lemmas on composition with continuous functions ([#3459](https://github.com/leanprover-community/mathlib/pull/3459))

### [2020-07-20 18:42:24](https://github.com/leanprover-community/mathlib/commit/7aa85c2)
fix(algebra/group/units): add missing coe lemmas to units ([#3472](https://github.com/leanprover-community/mathlib/pull/3472))
Per @kbuzzard's suggestions [here](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Shortening.20proof.20on.20product.20of.20units.20in.20Z.html[#204406319](https://github.com/leanprover-community/mathlib/pull/204406319)):
- Add a new lemma `coe_eq_one` to `units` API
- Tag `eq_iff` with `norm_cast`

### [2020-07-20 17:56:13](https://github.com/leanprover-community/mathlib/commit/b66d1be)
feat(data/multivariate/qpf): definition ([#3395](https://github.com/leanprover-community/mathlib/pull/3395))
Part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)

### [2020-07-20 15:42:49](https://github.com/leanprover-community/mathlib/commit/78f438b)
feat(tactic/squeeze_*): improve suggestions ([#3431](https://github.com/leanprover-community/mathlib/pull/3431))
This makes this gives `squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` the `?` optional argument that indicates that we should consider all `simp` lemmas that are also `_refl_lemma`

### [2020-07-20 14:17:48](https://github.com/leanprover-community/mathlib/commit/d0df6b8)
feat(data/equiv/mul_add): refl_apply and trans_apply ([#3470](https://github.com/leanprover-community/mathlib/pull/3470))

### [2020-07-20 14:17:46](https://github.com/leanprover-community/mathlib/commit/2994f1b)
feat(solve_by_elim): add tracing ([#3468](https://github.com/leanprover-community/mathlib/pull/3468))
When `solve_by_elim` fails, it now prints:
```
`solve_by_elim` failed.
Try `solve_by_elim { max_depth := N }` for a larger `N`,
or use `set_option trace.solve_by_elim true` to view the search.
```
and with `set_option trace.solve_by_elim true` we get messages like:
```
example (n m : ℕ) (f : ℕ → ℕ → Prop) (h : f n m) : ∃ p : ℕ × ℕ, f p.1 p.2 :=
begin
  repeat { fsplit },
  solve_by_elim*,
end
```
producing:
```
[solve_by_elim . ✅ `n` solves `⊢ ℕ`]
[solve_by_elim .. ✅ `n` solves `⊢ ℕ`]
[solve_by_elim ... ❌ failed to solve `⊢ f (n, n).fst (n, n).snd`]
[solve_by_elim .. ✅ `m` solves `⊢ ℕ`]
[solve_by_elim ... ✅ `h` solves `⊢ f (n, m).fst (n, m).snd`]
[solve_by_elim .... success!]
```
Fixed [#3063](https://github.com/leanprover-community/mathlib/pull/3063)

### [2020-07-20 14:17:44](https://github.com/leanprover-community/mathlib/commit/38b95c8)
feat(set_theory/cardinal): simp lemmas about numerals ([#3450](https://github.com/leanprover-community/mathlib/pull/3450))

### [2020-07-20 14:17:41](https://github.com/leanprover-community/mathlib/commit/9a92363)
feat(logic/basic): nonempty.some ([#3449](https://github.com/leanprover-community/mathlib/pull/3449))
Could we please have this? I've a number of times been annoyed by the difficulty of extracting an element from a `nonempty`.
(Criterion for alternative solutions: `library_search` solves `nonempty X -> X`.)

### [2020-07-20 14:17:39](https://github.com/leanprover-community/mathlib/commit/469043f)
refactor(tactic/generalizes): reimplement generalizes' ([#3416](https://github.com/leanprover-community/mathlib/pull/3416))
The new implementation is somewhat simpler. It is inspired by the C++
function `generalize_indices` in `library/tactic/cases_tactic.cpp`,
which performs essentially the same construction.
The only non-internal change is the return type of `generalizes_intro`.

### [2020-07-20 12:54:51](https://github.com/leanprover-community/mathlib/commit/593b1bb)
feat(linear_algebra/affine_space): lemmas on affine spans ([#3453](https://github.com/leanprover-community/mathlib/pull/3453))
Add more lemmas on affine spans; in particular, that the points in an
`affine_span` are exactly the `affine_combination`s where the sum of
weights equals 1, provided the underlying ring is nontrivial.

### [2020-07-20 12:54:49](https://github.com/leanprover-community/mathlib/commit/65208ed)
refactor(data/polynomial/*): further refactors ([#3435](https://github.com/leanprover-community/mathlib/pull/3435))
There's a lot further to go, but I need to do other things for a while so will PR what I have so far.

### [2020-07-20 12:54:47](https://github.com/leanprover-community/mathlib/commit/cb06214)
feat(tactic/interactive_expr): always select all arguments ([#3384](https://github.com/leanprover-community/mathlib/pull/3384))
If you hover over `id id 0` in the widget (or really any function with more than one argument), then it is possible to select the partial application `id id`.  The popup will then only show the function `id` and the argument `id`, but not the second argument `0`.
This PR changes this behavior so that you can't select partial applications and always see all argument in the popup.

### [2020-07-20 11:25:58](https://github.com/leanprover-community/mathlib/commit/4a3755a)
chore(algebra/ring): fix a mistake ([#3469](https://github.com/leanprover-community/mathlib/pull/3469))

### [2020-07-20 09:41:20](https://github.com/leanprover-community/mathlib/commit/4dc0814)
feat (algebra/module): lemma about submodules ([#3466](https://github.com/leanprover-community/mathlib/pull/3466))
Add a 3-line lemma saying that a linear combination of elements of a submodule is still in that submodule.

### [2020-07-20 08:16:52](https://github.com/leanprover-community/mathlib/commit/a400adb)
fix(tactic/library_search): 1 ≤ n goals in nat ([#3462](https://github.com/leanprover-community/mathlib/pull/3462))
Fixes [#3432](https://github.com/leanprover-community/mathlib/pull/3432).
This PR changes `library_search` and `suggest`:
1. instead of just selecting lemma with a single `name` as their head symbol, allows selecting from a `name_set`.
2. when the goal is `≤` on certain `ℕ` goals, set that `name_set` to `[has_lt.lt, has_le.le]`, for more flexible matching of inequality lemmas about `ℕ`
3. now successfully solves `theorem nonzero_gt_one (n : ℕ) : ¬ n = 0 → n ≥ 1 := by library_search!`
4. splits the `test/library_search/basic.lean` file into two parts, one which doesn't import `data.nat.basic`, for faster testing

### [2020-07-20 06:04:37](https://github.com/leanprover-community/mathlib/commit/5080dd5)
feat(data/padics/padic_norm): lemmas about padic_val_nat ([#3230](https://github.com/leanprover-community/mathlib/pull/3230))
Collection of lemmas about `padic_val_nat`, culminating in `lemma prod_pow_prime_padic_val_nat : ∀ (n : nat) (s : n ≠ 0) (m : nat) (pr : n < m),  ∏ p in finset.filter nat.prime (finset.range m), pow p (padic_val_nat p n) = n`.

### [2020-07-20 05:06:14](https://github.com/leanprover-community/mathlib/commit/84d4ea7)
feat(data/nat/digits): a bigger number has more digits ([#3457](https://github.com/leanprover-community/mathlib/pull/3457))

### [2020-07-20 05:06:12](https://github.com/leanprover-community/mathlib/commit/792f541)
feat(field_theory/tower): tower law ([#3355](https://github.com/leanprover-community/mathlib/pull/3355))

### [2020-07-20 03:39:14](https://github.com/leanprover-community/mathlib/commit/501aeb7)
feat(data/quot.lean): add lift_on_beta\_2 ([#3456](https://github.com/leanprover-community/mathlib/pull/3456))
This corresponds to `lift_on\_2` in `library/init/data/quot.lean` just as `lift_beta` and `lift_on_beta` correspond to `lift` and `lift_on`. It greatly simplifies quotient proofs but was, surprisingly, missing.

### [2020-07-20 03:10:32](https://github.com/leanprover-community/mathlib/commit/697488c)
feat(tactic/unfold_cases): add unfold_cases tactic ([#3396](https://github.com/leanprover-community/mathlib/pull/3396))

### [2020-07-20 00:16:06](https://github.com/leanprover-community/mathlib/commit/2975f93)
chore(tactic/interactive): move non-monadic part of `clean` to `expr.clean` ([#3461](https://github.com/leanprover-community/mathlib/pull/3461))

### [2020-07-20 00:16:04](https://github.com/leanprover-community/mathlib/commit/db18144)
chore(order/bounded_lattice): add `is_compl.inf_left_eq_bot_iff` etc ([#3460](https://github.com/leanprover-community/mathlib/pull/3460))

### [2020-07-19 21:18:59](https://github.com/leanprover-community/mathlib/commit/1bb3d19)
refactor(order/filter/basic): add class `filter.ne_bot` ([#3454](https://github.com/leanprover-community/mathlib/pull/3454))
This way Lean will f`≠ ⊥` in a few most common cases
(incl. `nhds_ne_bot`, `at_top_ne_bot`) automatically.
Other API changes:
* many lemmas now take `[ne_bot l]` instead of `(hl : l ≠ ⊥)`;
* some lemmas got `'` versions that take an explicit `(hl : ne_bot l)`;
* rename `ultrafilter_unique` to `is_ultrafilter.unique`;
* `cauchy_downwards` is now `cauchy.mono` (instance arg) and `cauchy.mono'` (explicit arg);
* `cauchy_map` is now `cauchy.map`;
* `cauchy_comap` is now `cauchy.comap`;
* `totally_bounded_closure` is now `totally_bounded.closure`;
* `totally_bounded_image` is now `totally_bounded.image`;

### [2020-07-19 21:18:58](https://github.com/leanprover-community/mathlib/commit/953ab3a)
feat(geometry/manifold/charted_space): open subset of a manifold is a manifold ([#3442](https://github.com/leanprover-community/mathlib/pull/3442))
An open subset of a charted space is naturally a charted space.  If the charted space has structure groupoid `G` (with `G` closed under restriction), then the open subset does also.
Most of the work is in `topology/local_homeomorph`, where it is proved that a local homeomorphism whose source is `univ` is an open embedding, and conversely.

### [2020-07-19 16:12:23](https://github.com/leanprover-community/mathlib/commit/bc278b7)
fix(tactic/apply_rules): fix stuck metavariable bug ([#3451](https://github.com/leanprover-community/mathlib/pull/3451))
`apply_rules` had the same bug `solve_by_elim` used to suffer from: applying a lemma once would fix its arguments, and prevent it from being applied a second time with different arguments.
This essentially ports over the fix from `solve_by_elim`: rather than carrying around a `list expr`, we carry a `list (tactic expr)` and generate on demand.

### [2020-07-19 15:29:48](https://github.com/leanprover-community/mathlib/commit/9b0435a)
fix(tactic/linarith): find correct zero_lt_one ([#3455](https://github.com/leanprover-community/mathlib/pull/3455))
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/linarith.20and.20ordinal.20file

### [2020-07-19 14:44:28](https://github.com/leanprover-community/mathlib/commit/47ea2a6)
feat(topology, analysis) : add lemmas about `has_neg.neg` (preliminaries for L'Hopital's rule) ([#3392](https://github.com/leanprover-community/mathlib/pull/3392))
This PR contains a few lemmas about the `has_neg.neg` function, such as : 
- its limit along `at_top` and `at_bot`
- its limit along `nhds a`, `nhds_within a (Ioi a)` and similar filters
- its differentiability and derivative

### [2020-07-19 14:13:17](https://github.com/leanprover-community/mathlib/commit/8187551)
feat(topology/algebra/continuous_functions): algebra structure over continuous functions ([#3383](https://github.com/leanprover-community/mathlib/pull/3383))

### [2020-07-19 09:29:38](https://github.com/leanprover-community/mathlib/commit/5228d55)
feat(linear_algebra/basic): add span_zero ([#3306](https://github.com/leanprover-community/mathlib/pull/3306))
`simp` now proves span_zero for both submodules and ideals

### [2020-07-19 06:24:31](https://github.com/leanprover-community/mathlib/commit/3354476)
feat(data/indicator_function): more lemmas ([#3424](https://github.com/leanprover-community/mathlib/pull/3424))
Add some lemmas of use when using `set.indicator` to manipulate
functions involved in summations.

### [2020-07-19 05:43:15](https://github.com/leanprover-community/mathlib/commit/8312419)
refactor(data/polynomial): remove has_coe_to_fun, and @[reducible] on monomial ([#3420](https://github.com/leanprover-community/mathlib/pull/3420))
I'm going to refactor in stages, trying to clean up some of the cruftier aspects of `data/polynomial/*`.
This PR:
1. removes the `has_coe_to_fun` on polynomial

### [2020-07-19 04:53:42](https://github.com/leanprover-community/mathlib/commit/eca55c9)
feat(category_theory/equivalence): injectivity simp lemmas for equivalences ([#3437](https://github.com/leanprover-community/mathlib/pull/3437))

### [2020-07-19 04:53:40](https://github.com/leanprover-community/mathlib/commit/eb68f4c)
feat (linear_algebra/matrix): make diag and trace compatible with semirings ([#3433](https://github.com/leanprover-community/mathlib/pull/3433))
changes ring and related instances to semiring etc. in requirements for matrix.diag and matrix.trace

### [2020-07-19 04:53:38](https://github.com/leanprover-community/mathlib/commit/e6bfe18)
feat(topology/algebra/module): pi and proj for CLM ([#3430](https://github.com/leanprover-community/mathlib/pull/3430))

### [2020-07-19 03:42:37](https://github.com/leanprover-community/mathlib/commit/f83cf57)
feat(data/equiv/mul_add): minor lemmas ([#3447](https://github.com/leanprover-community/mathlib/pull/3447))

### [2020-07-19 03:42:35](https://github.com/leanprover-community/mathlib/commit/61bd966)
feat(data/list/basic): add concat lemmas ([#3445](https://github.com/leanprover-community/mathlib/pull/3445))
The first two are taken after the `head_eq_of_cons_eq` and `tail_eq_of_cons_eq` lemmas further up in the file.
The third, `reverse_concat`, is like `reverse_cons'` but with the `::` and `concat` swapped.

### [2020-07-19 03:15:24](https://github.com/leanprover-community/mathlib/commit/91ca927)
feat(geometry/manifold/local_invariant_properties):  local structomorphism is `local_invariant_prop` ([#3434](https://github.com/leanprover-community/mathlib/pull/3434))
For a groupoid `G`, define the property of being a local structomorphism; prove that if `G` is closed under restriction then this property satisfies `local_invariant_prop` (i.e., is local and `G`-invariant).

### [2020-07-18 16:49:37](https://github.com/leanprover-community/mathlib/commit/4760a33)
feat(algebra/polynomial, data/polynomial): lemmas about monic polynomials ([#3402](https://github.com/leanprover-community/mathlib/pull/3402))

### [2020-07-18 16:19:16](https://github.com/leanprover-community/mathlib/commit/37cf166)
feat(data/complex/exponential): added @[mono] tag to exp_le_exp and exp_lt_exp ([#3318](https://github.com/leanprover-community/mathlib/pull/3318))
added @[mono] tag to exp_le_exp and exp_lt_exp.

### [2020-07-18 12:28:11](https://github.com/leanprover-community/mathlib/commit/e3e0aa0)
chore(linear_algebra/direct_sum_module): add dosctrings ([#3418](https://github.com/leanprover-community/mathlib/pull/3418))

### [2020-07-18 11:26:57](https://github.com/leanprover-community/mathlib/commit/21a1683)
feat(data/finsupp): sums over on_finset ([#3427](https://github.com/leanprover-community/mathlib/pull/3427))
There aren't many lemmas about `finsupp.on_finset`.  Add one that's
useful for manipulating sums over `on_finset`.

### [2020-07-18 11:26:55](https://github.com/leanprover-community/mathlib/commit/4767b30)
feat(algebra/big_operators): more general prod_insert_one ([#3426](https://github.com/leanprover-community/mathlib/pull/3426))
I found I had a use for a slightly more general version of
`prod_insert_one` / `sum_insert_zero`.  Add that version and use it in
the proof of `prod_insert_one`.

### [2020-07-18 10:34:10](https://github.com/leanprover-community/mathlib/commit/f81568a)
feat(group_theory/semidirect_product): mk_eq_inl_mul_inr and hom_ext ([#3408](https://github.com/leanprover-community/mathlib/pull/3408))

### [2020-07-18 09:27:48](https://github.com/leanprover-community/mathlib/commit/907147a)
feat(linear_algebra/matrix): define equivalences for reindexing matrices with equivalent types ([#3409](https://github.com/leanprover-community/mathlib/pull/3409))

### [2020-07-18 06:56:08](https://github.com/leanprover-community/mathlib/commit/06823d6)
chore(*): add copyright header, cleanup imports ([#3440](https://github.com/leanprover-community/mathlib/pull/3440))
Fixes
1. a missing copyright header
2. moves `tactic.obviously` into the imports of `tactic.basic`, so everyone has `tidy` and `obviously` available.
3. removes a few redundant imports

### [2020-07-17 14:49:16](https://github.com/leanprover-community/mathlib/commit/9616f44)
feat(algebra/ordered_group): decidable_linear_order for multiplicative and additive ([#3429](https://github.com/leanprover-community/mathlib/pull/3429))

### [2020-07-17 14:49:14](https://github.com/leanprover-community/mathlib/commit/3acf220)
feat(group_theory/semidirect_product): inl_aut_inv ([#3410](https://github.com/leanprover-community/mathlib/pull/3410))

### [2020-07-17 13:47:53](https://github.com/leanprover-community/mathlib/commit/8999625)
chore(*): more import reduction ([#3421](https://github.com/leanprover-community/mathlib/pull/3421))
Another import reduction PR. (This is by hand, not just removing transitive imports.)
Mostly this one is from staring at `leanproject import-graph --to data.polynomial.basic` and wondering about weird edges in the graph.

### [2020-07-17 12:38:22](https://github.com/leanprover-community/mathlib/commit/207a1d4)
feat(data/finset/basic): finset of empty type ([#3425](https://github.com/leanprover-community/mathlib/pull/3425))
In a proof working by cases for whether a type is nonempty, I found I
had a use for the result that a `finset` of an empty type is empty.

### [2020-07-17 09:26:56](https://github.com/leanprover-community/mathlib/commit/4a6b716)
fix(tactic/nlinarith): stop nlinarith failing in the presence of squares when there is no order ([#3417](https://github.com/leanprover-community/mathlib/pull/3417))
As reported by Heather Macbeth at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/app_builder_exception.20in.20.60nlinarith.60/near/204138256

### [2020-07-17 07:23:09](https://github.com/leanprover-community/mathlib/commit/7d31f77)
refactor(measure_theory/*): big refactor ([#3373](https://github.com/leanprover-community/mathlib/pull/3373))
Big refactor of integrals, fixes [#3084](https://github.com/leanprover-community/mathlib/pull/3084) 
Make `integral (f : α → E) (μ : measure α)` the main definition, and use `notation` for other integrals
(over a set and/or w.r.t. the canonical measure `volume`).

### [2020-07-17 05:45:27](https://github.com/leanprover-community/mathlib/commit/819bd86)
feat(tactic/squeeze_*): add `squeeze_dsimp` ([#3386](https://github.com/leanprover-community/mathlib/pull/3386))

### [2020-07-17 03:52:34](https://github.com/leanprover-community/mathlib/commit/9d74f9b)
chore(data/polynomial): reduce imports ([#3419](https://github.com/leanprover-community/mathlib/pull/3419))
Now that @jalex-stark has split up `data.polynomial` into submodules, this PR minimises imports.

### [2020-07-17 00:03:26](https://github.com/leanprover-community/mathlib/commit/f1b687c)
feat (order/order_iso): lemmas about order_isos on lattices ([#3397](https://github.com/leanprover-community/mathlib/pull/3397))
shows that `order_embedding`s and `order_iso`s respect `lattice` operations

### [2020-07-16 19:13:26](https://github.com/leanprover-community/mathlib/commit/33d45bf)
chore(data/polynomial): break up behemoth file ([#3407](https://github.com/leanprover-community/mathlib/pull/3407))
Polynomial refactor
The goal is to split `data/polynomial.lean` into several self-contained files in the same place. For the time being, the new place for all these files is `data/polynomial/`.
Future PRs may simplify proofs, remove duplicate lemmas, and move files out of the `data` directory.

### [2020-07-16 18:00:07](https://github.com/leanprover-community/mathlib/commit/6fd4f8f)
feat(meta/expr): add tactic_format instance for declaration ([#3390](https://github.com/leanprover-community/mathlib/pull/3390))
This allows you to `trace d` where `d : declaration`. Useful for debugging metaprograms.

### [2020-07-16 14:24:27](https://github.com/leanprover-community/mathlib/commit/25be04a)
feat(data/nat/digits): add lemmas about digits ([#3406](https://github.com/leanprover-community/mathlib/pull/3406))
Added `lt_base_pow_length_digits`, `of_digits_lt_base_pow_length`, `of_digits_append` and `of_digits_digits_append_digits`

### [2020-07-16 12:55:24](https://github.com/leanprover-community/mathlib/commit/a8c10e1)
chore(topology/algebra/ordered): rename `lim*_eq_of_tendsto` to `tendsto.lim*_eq` ([#3415](https://github.com/leanprover-community/mathlib/pull/3415))
Also add `tendsto_of_le_liminf_of_limsup_le`

### [2020-07-16 07:53:56](https://github.com/leanprover-community/mathlib/commit/1311eb2)
feat(tactic/obviously): improve error reporting ([#3412](https://github.com/leanprover-community/mathlib/pull/3412))
If `obviously` (used for auto_params) fails, it now prints a more useful message than "chain tactic made no progress"
If the goal presented to obviously contains `sorry`, it just uses `sorry` to discard it.

### [2020-07-16 06:45:37](https://github.com/leanprover-community/mathlib/commit/9ca3ce6)
chore(data/opposite): pp_nodot on op and unop ([#3413](https://github.com/leanprover-community/mathlib/pull/3413))
Since it's not possible to write `X.op`, its extremely unhelpful for the pretty printer to output this.

### [2020-07-15 23:05:39](https://github.com/leanprover-community/mathlib/commit/c1a5ae9)
chore(order/directed): use implicit args in `iff`s ([#3411](https://github.com/leanprover-community/mathlib/pull/3411))

### [2020-07-15 16:50:18](https://github.com/leanprover-community/mathlib/commit/5fe67b7)
feat(measure_theory): preliminaries for Haar measure ([#3195](https://github.com/leanprover-community/mathlib/pull/3195))
Move properties about lattice operations on encodable types to a new file. These are generalized from lemmas in the measure theory folder, for lattice operations and not just for `ennreal`. Also move them to the `encodable` namespace.
Rename `outer_measure.Union_aux` to `encodable.Union_decode2`.
Generalize some properties for outer measures to arbitrary complete lattices. This is useful for operations that behave like outer measures on a subset of `set α`.

### [2020-07-15 13:56:45](https://github.com/leanprover-community/mathlib/commit/5f5d641)
feat(algebra/ordered_group): instances for additive/multiplicative ([#3405](https://github.com/leanprover-community/mathlib/pull/3405))

### [2020-07-15 11:42:20](https://github.com/leanprover-community/mathlib/commit/a41a307)
refactor(topology/algebra/infinite_sum): review ([#3371](https://github.com/leanprover-community/mathlib/pull/3371))
## Rename
- `has_sum_unique` → `has_sum.unique`;
- `summable.summable_comp_of_injective` → `summable.comp_injective`;
- `has_sum_iff_tendsto_nat_of_summable` → `summable.has_sum_iff_tendsto_nat`;
- `tsum_eq_has_sum` → `has_sum.tsum_eq`;
- `support_comp` → `support_comp_subset`, delete `support_comp'`;
## Change arguments
- `tsum_eq_tsum_of_ne_zero_bij`, `has_sum_iff_has_sum_of_ne_zero_bij`: use functions from `support` instead of `Π x, f x ≠ 0 → β`;
## Add
- `indicator_compl_add_self_apply`, `indicator_compl_add_self`;
- `indicator_self_add_compl_apply`, `indicator_self_add_compl`;
- `support_subset_iff`, `support_subset_iff'`;
- `support_subset_comp`;
- `support_prod_mk`;
- `embedding.coe_subtype`;

### [2020-07-15 09:51:42](https://github.com/leanprover-community/mathlib/commit/503a40a)
feat(logic/basic) forall_imp ([#3391](https://github.com/leanprover-community/mathlib/pull/3391))
Added a missing lemma, which is the one-way implication version of `forall_congr`.

### [2020-07-15 05:11:12](https://github.com/leanprover-community/mathlib/commit/51a75ff)
feat(category_theory/pullback): make the is_limit helper lemmas more ergonomic ([#3398](https://github.com/leanprover-community/mathlib/pull/3398))

### [2020-07-15 00:57:03](https://github.com/leanprover-community/mathlib/commit/8495f76)
feat(geometry/manifold/times_cont_mdiff): smooth functions between manifolds ([#3387](https://github.com/leanprover-community/mathlib/pull/3387))
We define smooth functions between smooth manifolds, and prove their basic properties (including the facts that a composition of smooth functions is smooth, and that the tangent map of a smooth map is smooth).
To avoid reproving always the same stuff in manifolds, we build a general theory of local invariant properties in the model space (i.e., properties which are local, and invariant under the structure groupoids) and show that the lift of such properties to charted spaces automatically inherit all the good behavior of the original property. We apply this general machinery to prove most basic properties of smooth functions between manifolds.

### [2020-07-14 16:40:34](https://github.com/leanprover-community/mathlib/commit/708e481)
chore(data/set/basic): simp attribute on set.image_subset_iff ([#3394](https://github.com/leanprover-community/mathlib/pull/3394))
see discussion here with @sgouezel :
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.233387.3A.20smooth.20functions.20on.20manifolds/near/203751071

### [2020-07-14 15:06:30](https://github.com/leanprover-community/mathlib/commit/6c1ae3b)
chore(category_theory/natural_isomorphism): move lemmas to correct namespace, add simp lemma ([#3401](https://github.com/leanprover-community/mathlib/pull/3401))

### [2020-07-14 15:06:28](https://github.com/leanprover-community/mathlib/commit/f7825bf)
feat(algebra/polynomial): big_operators lemmas for polynomials ([#3378](https://github.com/leanprover-community/mathlib/pull/3378))
This starts a new folder algebra/polynomial. As we refactor data/polynomial.lean, much of that content should land in this folder.

### [2020-07-14 14:42:05](https://github.com/leanprover-community/mathlib/commit/bcf61df)
feat(data/qpf): uniformity iff preservation of supp ([#3388](https://github.com/leanprover-community/mathlib/pull/3388))

### [2020-07-14 14:05:54](https://github.com/leanprover-community/mathlib/commit/02f2f94)
refactor(category_theory/finite_limits): missing piece of [#3320](https://github.com/leanprover-community/mathlib/pull/3320) ([#3400](https://github.com/leanprover-community/mathlib/pull/3400))
A recent PR [#3320](https://github.com/leanprover-community/mathlib/pull/3320) did some refactoring of special shapes of limits. It seems I forgot to include `wide_pullbacks` in that refactor, so I've done that here.

### [2020-07-14 11:42:20](https://github.com/leanprover-community/mathlib/commit/a0846da)
chore(category_theory/limits/over): split a slow file ([#3399](https://github.com/leanprover-community/mathlib/pull/3399))
This was previously the last file to finish compiling when compiling `category_theory/`. This PR splits it into some smaller pieces which can compile in parallel (and some pieces now come earlier in the import hierarchy).
No change to content.

### [2020-07-14 11:42:18](https://github.com/leanprover-community/mathlib/commit/0fff477)
feat(analysis/normed_space): complex Hahn-Banach theorem ([#3286](https://github.com/leanprover-community/mathlib/pull/3286))
This proves the complex Hahn-Banach theorem by reducing it to the real version.
The corollaries from [#3021](https://github.com/leanprover-community/mathlib/pull/3021) should be generalized as well at some point.

### [2020-07-14 11:05:58](https://github.com/leanprover-community/mathlib/commit/5f01b54)
feat(category_theory/kernels): kernel_iso_of_eq ([#3372](https://github.com/leanprover-community/mathlib/pull/3372))
This provides two useful isomorphisms when working with abstract (co)kernels:
```
def kernel_zero_iso_source [has_kernel (0 : X ⟶ Y)] : kernel (0 : X ⟶ Y) ≅ X :=
def kernel_iso_of_eq {f g : X ⟶ Y} [has_kernel f] [has_kernel g] (h : f = g) : kernel f ≅ kernel g :=
```
and some associated simp lemmas.

### [2020-07-14 09:01:17](https://github.com/leanprover-community/mathlib/commit/58dde5b)
chore(*): generalize tensor product to semirings ([#3389](https://github.com/leanprover-community/mathlib/pull/3389))

### [2020-07-14 01:25:26](https://github.com/leanprover-community/mathlib/commit/0410946)
chore(linear_algebra/nonsingular_inverse): swap update_row/column names ([#3393](https://github.com/leanprover-community/mathlib/pull/3393))
The names for `update_row` and `update_column` did not correspond to their definitions. Doing a global swap of the names keep all the proofs valid and makes the semantics match.

### [2020-07-13 20:57:57](https://github.com/leanprover-community/mathlib/commit/32c75d0)
feat(linear_algebra/affine_space): more lemmas on directions of affine subspaces ([#3377](https://github.com/leanprover-community/mathlib/pull/3377))
Add more lemmas on directions of affine subspaces, motivated by uses
for Euclidean geometry.

### [2020-07-13 20:02:35](https://github.com/leanprover-community/mathlib/commit/1132237)
feat(ring_theory/ideal_over): lemmas for nonzero ideals lying over nonzero ideals ([#3385](https://github.com/leanprover-community/mathlib/pull/3385))
Let `f` be a ring homomorphism from `R` to `S` and `I` be an ideal in `S`. To show that `I.comap f` is not the zero ideal, we can show `I` contains a non-zero root of some non-zero polynomial `p : polynomial R`. As a corollary, if `S` is algebraic over `R` (e.g. the integral closure of `R`), nonzero ideals in `S` lie over nonzero ideals in `R`.
I created a new file because `integral_closure.comap_ne_bot` depends on `comap_ne_bot_of_algebraic_mem`, but `ring_theory/algebraic.lean` imports `ring_theory/integral_closure.lean` and I didn't see any obvious join in the dependency graph where they both belonged.

### [2020-07-13 19:35:16](https://github.com/leanprover-community/mathlib/commit/45477c8)
feat(analysis/normed_space/real_inner_product): orthogonal subspaces ([#3369](https://github.com/leanprover-community/mathlib/pull/3369))
Define the subspace of vectors orthogonal to a given subspace and
prove some basic properties of it, building on the existing results
about minimizers.  This is in preparation for doing similar things in
Euclidean geometry (working with the affine subspace through a given
point and orthogonal to a given affine subspace, for example).

### [2020-07-13 19:01:01](https://github.com/leanprover-community/mathlib/commit/2ae7ad8)
feat(functor): definition multivariate functors ([#3360](https://github.com/leanprover-community/mathlib/pull/3360))
One part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317)

### [2020-07-13 12:37:11](https://github.com/leanprover-community/mathlib/commit/f034899)
feat(data/equiv/mul_add): conj as a mul_aut ([#3367](https://github.com/leanprover-community/mathlib/pull/3367))

### [2020-07-13 09:46:22](https://github.com/leanprover-community/mathlib/commit/e26b459)
feat(data/polynomial): some lemmas about eval2 and algebra_map ([#3382](https://github.com/leanprover-community/mathlib/pull/3382))

### [2020-07-13 08:17:18](https://github.com/leanprover-community/mathlib/commit/792faae)
chore(data/polynomial): missing a simp attribute ([#3381](https://github.com/leanprover-community/mathlib/pull/3381))

### [2020-07-13 08:17:16](https://github.com/leanprover-community/mathlib/commit/afa534c)
chore(tactic/show_term): use Try this: ([#3374](https://github.com/leanprover-community/mathlib/pull/3374))

### [2020-07-12 23:29:02](https://github.com/leanprover-community/mathlib/commit/eb851ae)
chore(data/nat/prime): @[pp_nodot] nat.prime ([#3379](https://github.com/leanprover-community/mathlib/pull/3379))

### [2020-07-12 10:32:15](https://github.com/leanprover-community/mathlib/commit/a8d6bdf)
feat(algebra/category/AddCommGroup): has_image_maps ([#3366](https://github.com/leanprover-community/mathlib/pull/3366))

### [2020-07-12 09:02:34](https://github.com/leanprover-community/mathlib/commit/fa6c45a)
feat(data/polynomial): simp lemmas for bit0 / bit1 ([#3376](https://github.com/leanprover-community/mathlib/pull/3376))
Add lemmas on polynomials and bit0/bit1 (as suggested [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Eval.20of.20constant.20polynomial))

### [2020-07-12 07:43:26](https://github.com/leanprover-community/mathlib/commit/4e603f4)
feat(geometry/manifold/charted_space):  typeclass `closed_under_restriction` for structure groupoids ([#3347](https://github.com/leanprover-community/mathlib/pull/3347))
* Define a typeclass `closed_under_restriction` for structure groupoids.
* Prove that it is equivalent to requiring that the structure groupoid contain all local homeomorphisms equivalent to the restriction of the identity to an open subset.
* Verify that `continuous_groupoid` and `times_cont_diff_groupoid` satisfy `closed_under_restriction`.  
* Show that a charted space defined by a single chart is `has_groupoid` for any structure groupoid satisfying `closed_under_restriction`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Restriction.20in.20structure.20groupoid)

### [2020-07-12 05:07:52](https://github.com/leanprover-community/mathlib/commit/0e1c2bc)
feat(algebra/add_torsor): more cancellation lemmas ([#3368](https://github.com/leanprover-community/mathlib/pull/3368))
Add more cancellation lemmas for `vsub`, similar to lemmas already
present for `vadd`.

### [2020-07-12 03:42:43](https://github.com/leanprover-community/mathlib/commit/b047396)
feat(data/set/finite): add a version of `prod_preimage` for `inj_on` ([#3342](https://github.com/leanprover-community/mathlib/pull/3342))
* rename `finset.prod_preimage` to `finset.prod_preimage_of_bij`;
* new `prod_preimage` assumes `∀ x ∈ s, x ∉ range f, g x = 1`;
* rename `finset.image_preimage` to `finset.image_preimage_of_bij`;
* new `finset.image_preimage` says
  `image f (preimage s hf) = s.filter (λ x, x ∈ set.range f)`;
* change the order of implicit arguments in the definition of `set.inj_on`;
* add `prod_filter_of_ne`;
* use `coe` instead of `subtype.val` in `prod_attach`;
* add `finset.image_subset_iff`, `finset.image_subset_iff_subset_preimage`,
  `finset.map_subset_iff_subset_preimage`.

### [2020-07-12 00:42:49](https://github.com/leanprover-community/mathlib/commit/298caa0)
chore(scripts): update nolints.txt ([#3370](https://github.com/leanprover-community/mathlib/pull/3370))
I am happy to remove some nolints for you!

### [2020-07-11 10:11:11](https://github.com/leanprover-community/mathlib/commit/d7ac180)
feat(data/fintype/basic): set.to_finset_empty ([#3361](https://github.com/leanprover-community/mathlib/pull/3361))
Add set.to_finset_empty, analogously to set.to_finset_univ.

### [2020-07-11 10:11:09](https://github.com/leanprover-community/mathlib/commit/34d3fe1)
chore(category_theory/comma): split into three files ([#3358](https://github.com/leanprover-community/mathlib/pull/3358))
Just reorganisation.

### [2020-07-11 08:43:40](https://github.com/leanprover-community/mathlib/commit/f742a3d)
refactor(tactic/push_neg): simp ¬ (p ∧ q) better ([#3362](https://github.com/leanprover-community/mathlib/pull/3362))
This simplifies `¬ (p ∧ q)` to `(p → ¬ q)` instead of `¬ p ∨ ¬ q`. This has better behavior when going between `\forall x, P -> Q` and `\exists x, P /\ Q'` where `Q` and `Q'` are opposite.

### [2020-07-11 08:43:39](https://github.com/leanprover-community/mathlib/commit/36a25d9)
feat(algebra/category/*): get rid of the local reducible hack ([#3354](https://github.com/leanprover-community/mathlib/pull/3354))
I thought I did this back in April, but apparently never made the PR.
We currently use a strange hack when setting up concrete categories, making them locally reducible. There's a library note about this, which ends:
```
TODO: Probably @[derive] should be able to create instances of the	
required form (without `id`), and then we could use that instead of	
this obscure `local attribute [reducible]` method.
```
This PR makes the small change required to `delta_instance` to make this happen, and then stops using the hack in setting up concrete categories (and deletes the library note explaining this hack).

### [2020-07-11 07:58:56](https://github.com/leanprover-community/mathlib/commit/75b9cfa)
feat(category/has_shift): missing simp lemmas ([#3365](https://github.com/leanprover-community/mathlib/pull/3365))

### [2020-07-11 07:58:54](https://github.com/leanprover-community/mathlib/commit/f669a78)
chore(category_theory/functor): explain how to type 𝟭 ([#3364](https://github.com/leanprover-community/mathlib/pull/3364))

### [2020-07-11 06:47:13](https://github.com/leanprover-community/mathlib/commit/574dac5)
feat(tactic/interval_cases): add `with h` option ([#3353](https://github.com/leanprover-community/mathlib/pull/3353))
closes [#2881](https://github.com/leanprover-community/mathlib/pull/2881)

### [2020-07-11 00:41:45](https://github.com/leanprover-community/mathlib/commit/5ddbdc1)
chore(scripts): update nolints.txt ([#3363](https://github.com/leanprover-community/mathlib/pull/3363))
I am happy to remove some nolints for you!

### [2020-07-10 19:01:46](https://github.com/leanprover-community/mathlib/commit/1aff3af)
feat(interactive_expr): bigger accomplishment ([#3359](https://github.com/leanprover-community/mathlib/pull/3359))
Lean is difficult, we need more incentives.

### [2020-07-10 17:35:22](https://github.com/leanprover-community/mathlib/commit/960fc8e)
feat(data/univariate/qpf): compositional data type framework for (co)inductive types ([#3325](https://github.com/leanprover-community/mathlib/pull/3325))
Define univariate QPFs (quotients of polynomial functors).  This is the first part of [#3317](https://github.com/leanprover-community/mathlib/pull/3317).

### [2020-07-10 12:28:46](https://github.com/leanprover-community/mathlib/commit/d1e63f3)
chore(category_theory/limits): remove an unnecessary import ([#3357](https://github.com/leanprover-community/mathlib/pull/3357))

### [2020-07-10 12:28:40](https://github.com/leanprover-community/mathlib/commit/699c915)
feat(number_theory): pythagorean triples ([#3200](https://github.com/leanprover-community/mathlib/pull/3200))
The classification of pythagorean triples (one of the "100 theorems")

### [2020-07-10 11:15:29](https://github.com/leanprover-community/mathlib/commit/e52108d)
chore(data/int/basic): move content requiring advanced imports ([#3334](https://github.com/leanprover-community/mathlib/pull/3334))
`data.int.basic` had grown to require substantial imports from `algebra.*`. This PR moves out the end of this file into separate files. As a consequence it's then possible to separate out `data.multiset.basic` into some further pieces.

### [2020-07-10 10:35:29](https://github.com/leanprover-community/mathlib/commit/a348944)
chore(topology): rename compact to is_compact ([#3356](https://github.com/leanprover-community/mathlib/pull/3356))

### [2020-07-10 07:09:28](https://github.com/leanprover-community/mathlib/commit/79bb8b7)
feat(linear_algebra/cayley_hamilton): the Cayley-Hamilton theorem ([#3276](https://github.com/leanprover-community/mathlib/pull/3276))
The Cayley-Hamilton theorem, following the proof at http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf.

### [2020-07-10 06:31:16](https://github.com/leanprover-community/mathlib/commit/66db1ad)
refactor(algebra/homology): handle co/homology uniformly ([#3316](https://github.com/leanprover-community/mathlib/pull/3316))
A refactor of `algebra/homology` so homology and cohomology are handled uniformly, and factor out a file `image_to_kernel_map.lean` which gains some extra lemmas (which will be useful for talking about exact sequences).

### [2020-07-10 05:40:16](https://github.com/leanprover-community/mathlib/commit/bcf733f)
feat(data/matrix): add matrix.map and supporting lemmas ([#3352](https://github.com/leanprover-community/mathlib/pull/3352))
As [requested](https://github.com/leanprover-community/mathlib/pull/3276/files#r452366674).

### [2020-07-10 04:14:30](https://github.com/leanprover-community/mathlib/commit/8b630df)
feat(ring_theory/matrix_algebra): drop commutativity assumption ([#3351](https://github.com/leanprover-community/mathlib/pull/3351))
Remove the unnecessary assumption that `A` is commutative in `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
(This didn't cause a problem for Cayley-Hamilton, but @alexjbest and Bassem Safieldeen [realised it's not necessary](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Tensor.20product.20of.20matrices).)

### [2020-07-10 04:14:28](https://github.com/leanprover-community/mathlib/commit/c949dd4)
chore(logic/embedding): reuse proofs from `data.*` ([#3341](https://github.com/leanprover-community/mathlib/pull/3341))
Other changes:
* rename `injective.prod` to `injective.prod_map`;
* add `surjective.prod_map`;
* redefine `sigma.map` without pattern matching;
* rename `sigma_map_injective` to `injective.sigma_map`;
* add `surjective.sigma_map`;
* add `injective.sum_map` and `surjective.sum_map`;
* rename `embedding.prod_congr` to `embedding.prod_map`;
* rename `embedding.sum_congr` to `embedding.sum_map`;
* delete `embedding.sigma_congr_right`, add more
  general `embedding.sigma_map`.

### [2020-07-10 02:38:09](https://github.com/leanprover-community/mathlib/commit/92d508a)
chore(*): import tactic.basic as early as possible, and reduce imports ([#3333](https://github.com/leanprover-community/mathlib/pull/3333))
As discussed on [zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/import.20refactor.20and.20library_search), [#3235](https://github.com/leanprover-community/mathlib/pull/3235) had the unfortunate effect of making `library_search` and `#where` and various other things unavailable in many places in mathlib.
This PR makes an effort to import `tactic.basic` as early as possible, while otherwise reducing unnecessary imports. 
1. import `tactic.basic` "as early as possible" (i.e. in any file that `tactic.basic` doesn't depend on, and which imports any tactic strictly between `tactic.core` and `tactic.basic`, just `import tactic.basic` itself
2. add `tactic.finish`, `tactic.tauto` and `tactic.norm_cast` to tactic.basic (doesn't requires adding any dependencies)
3. delete various unnecessary imports

### [2020-07-10 00:38:39](https://github.com/leanprover-community/mathlib/commit/997025d)
chore(scripts): update nolints.txt ([#3350](https://github.com/leanprover-community/mathlib/pull/3350))
I am happy to remove some nolints for you!

### [2020-07-09 22:44:21](https://github.com/leanprover-community/mathlib/commit/270e3c9)
chore(data/fintype/basic): add `finset.order_top` and `finset.bounded_distrib_lattice` ([#3345](https://github.com/leanprover-community/mathlib/pull/3345))

### [2020-07-09 22:44:20](https://github.com/leanprover-community/mathlib/commit/f5fa614)
chore(*): some monotonicity lemmas ([#3344](https://github.com/leanprover-community/mathlib/pull/3344))

### [2020-07-09 21:17:53](https://github.com/leanprover-community/mathlib/commit/d6e9f97)
feat(topology/basic): yet another mem_closure ([#3348](https://github.com/leanprover-community/mathlib/pull/3348))

### [2020-07-09 21:17:51](https://github.com/leanprover-community/mathlib/commit/ac62213)
chore(order/filter/at_top_bot): in `order_top` `at_top = pure ⊤` ([#3346](https://github.com/leanprover-community/mathlib/pull/3346))

### [2020-07-09 21:17:48](https://github.com/leanprover-community/mathlib/commit/4a63f3f)
feat(data/indicator_function): add `indicator_range_comp` ([#3343](https://github.com/leanprover-community/mathlib/pull/3343))
Add
* `comp_eq_of_eq_on_range`;
* `piecewise_eq_on`;
* `piecewise_eq_on_compl`;
* `piecewise_compl`;
* `piecewise_range_comp`;
* `indicator_range_comp`.

### [2020-07-09 16:34:14](https://github.com/leanprover-community/mathlib/commit/d6ecb44)
feat(topology/basic): closure in term of subtypes ([#3339](https://github.com/leanprover-community/mathlib/pull/3339))

### [2020-07-09 15:24:02](https://github.com/leanprover-community/mathlib/commit/593a4c8)
fix(tactic/norm_cast): remove bad norm_cast lemma ([#3340](https://github.com/leanprover-community/mathlib/pull/3340))
This was identified as a move_cast lemma, which meant it was rewriting to the LHS which it couldn't reduce. It's better to let the conditional rewriting handle nat subtraction -- if the right inequality is in the context there's no need to go to `int.sub_nat_nat`.

### [2020-07-09 14:50:06](https://github.com/leanprover-community/mathlib/commit/33ca9f1)
doc(category_theory/terminal): add doc-strings ([#3338](https://github.com/leanprover-community/mathlib/pull/3338))
Just adding some doc-strings.

### [2020-07-09 13:55:03](https://github.com/leanprover-community/mathlib/commit/9d47b28)
feat(data): Mark all `sqrt`s as `@[pp_nodot]` ([#3337](https://github.com/leanprover-community/mathlib/pull/3337))

### [2020-07-09 05:00:10-07:00](https://github.com/leanprover-community/mathlib/commit/e4ecf14)
I'm just another maintainer

### [2020-07-09 10:43:05](https://github.com/leanprover-community/mathlib/commit/be2e42f)
chore(ring_theory/algebraic): speedup slow proof ([#3336](https://github.com/leanprover-community/mathlib/pull/3336))

### [2020-07-09 06:11:02](https://github.com/leanprover-community/mathlib/commit/c06f500)
feat(logic/basic): add eq_iff_true_of_subsingleton ([#3308](https://github.com/leanprover-community/mathlib/pull/3308))
I'm surprised we didn't have this already.
```lean
example (x y : unit) : x = y := by simp
```

### [2020-07-09 03:35:05](https://github.com/leanprover-community/mathlib/commit/95cc1b1)
refactor(topology/dense_embedding): simplify proof ([#3329](https://github.com/leanprover-community/mathlib/pull/3329))
Using filter bases, we can give a cleaner proof of continuity of extension by continuity. Also switch to use the "new" `continuous_at` in the statement.

### [2020-07-09 03:35:03](https://github.com/leanprover-community/mathlib/commit/d5cfa87)
fix(tactic/lint/type_classes): add missing unfreeze_local_instances ([#3328](https://github.com/leanprover-community/mathlib/pull/3328))

### [2020-07-09 03:06:58](https://github.com/leanprover-community/mathlib/commit/b535b0a)
fix(tactic/default): add transport, equiv_rw ([#3330](https://github.com/leanprover-community/mathlib/pull/3330))
Also added a tactic doc entry for `transport`.

### [2020-07-09 00:41:30](https://github.com/leanprover-community/mathlib/commit/65dcf4d)
chore(scripts): update nolints.txt ([#3331](https://github.com/leanprover-community/mathlib/pull/3331))
I am happy to remove some nolints for you!

### [2020-07-08 20:57:45](https://github.com/leanprover-community/mathlib/commit/782013d)
fix(tactic/monotonicity): support monotone in mono ([#3310](https://github.com/leanprover-community/mathlib/pull/3310))
This PR allow the `mono` tactic to use lemmas stated using `monotone`.
Mostly authored by Simon Hudon

### [2020-07-08 17:40:17](https://github.com/leanprover-community/mathlib/commit/19225c3)
chore(*): update to 3.17.1 ([#3327](https://github.com/leanprover-community/mathlib/pull/3327))

### [2020-07-08 14:31:06](https://github.com/leanprover-community/mathlib/commit/27f622e)
chore(data/fintype/basic): split, and reduce imports ([#3319](https://github.com/leanprover-community/mathlib/pull/3319))
Following on from [#3256](https://github.com/leanprover-community/mathlib/pull/3256) and [#3235](https://github.com/leanprover-community/mathlib/pull/3235), this slices a little out of `data.fintype.basic`, and reduces imports, mostly in the vicinity of `data.fintype.basic`.

### [2020-07-08 14:31:04](https://github.com/leanprover-community/mathlib/commit/f90fcc9)
chore(*): use is_algebra_tower instead of algebra.comap and generalize some constructions to semirings ([#3299](https://github.com/leanprover-community/mathlib/pull/3299))
`algebra.comap` is now reserved to the **creation** of new algebra instances. For assumptions of theorems / constructions, `is_algebra_tower` is the new way to do it. For example:
```lean
variables [algebra K L] [algebra L A]
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K (comap K L A) :=
```
is now written as:
```lean
variables [algebra K L] [algebra L A] [algebra K A] [is_algebra_tower K L A]
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K A :=
```

### [2020-07-08 14:31:02](https://github.com/leanprover-community/mathlib/commit/ba8af8c)
feat(ring_theory/polynomial_algebra): polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) ([#3275](https://github.com/leanprover-community/mathlib/pull/3275))
This is a formal nonsense preliminary to the Cayley-Hamilton theorem, which comes in the next PR.
We produce the algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`, and as a consequence also the algebra isomorphism
```
matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (matrix_polynomial_equiv_polynomial_matrix m) k i j = coeff (m i j) k
```

### [2020-07-08 13:22:00](https://github.com/leanprover-community/mathlib/commit/8f6090c)
feat(algebra/ordered_field): missing lemma ([#3324](https://github.com/leanprover-community/mathlib/pull/3324))

### [2020-07-08 11:56:25](https://github.com/leanprover-community/mathlib/commit/97853b9)
doc(tactic/lean_core_docs): remove "hypothesis management" tag ([#3323](https://github.com/leanprover-community/mathlib/pull/3323))

### [2020-07-08 10:26:52](https://github.com/leanprover-community/mathlib/commit/a3e21a8)
feat(category_theory/zero): lemmas about zero objects and zero morphisms, and improve docs ([#3315](https://github.com/leanprover-community/mathlib/pull/3315))

### [2020-07-08 10:26:50](https://github.com/leanprover-community/mathlib/commit/fbb49cb)
refactor(*): place map_map in the functor namespace ([#3309](https://github.com/leanprover-community/mathlib/pull/3309))
Renames `_root_.map_map` to `functor.map_map` and `filter.comap_comap_comp` to `filter.comap_comap` (which is consistent with `filter.map_map`).

### [2020-07-08 09:01:29](https://github.com/leanprover-community/mathlib/commit/afae2c4)
doc(tactic/localized): unnecessary escape characters ([#3322](https://github.com/leanprover-community/mathlib/pull/3322))
This is probably left over from when it was a string literal instead of a doc string.

### [2020-07-08 08:25:47](https://github.com/leanprover-community/mathlib/commit/18246ac)
refactor(category_theory/finite_limits): reorganise import hierarchy ([#3320](https://github.com/leanprover-community/mathlib/pull/3320))
Previously, all of the "special shapes" that happened to be finite imported `category_theory.limits.shapes.finite_limits`. Now it's the other way round, which I think ends up being cleaner.
This also results in some significant reductions to the dependency graph (e.g. talking about homology of complexes no longer requires compiling `data.fintype.basic` and all its antecedents).
No actual content, just moving content around.

### [2020-07-08 07:12:45](https://github.com/leanprover-community/mathlib/commit/13eea4c)
chore(category_theory/images): cleanup ([#3314](https://github.com/leanprover-community/mathlib/pull/3314))
Just some cleanup, and adding two easy lemmas.

### [2020-07-08 07:12:43](https://github.com/leanprover-community/mathlib/commit/eb271b2)
feat(data/int/basic): some lemmas ([#3313](https://github.com/leanprover-community/mathlib/pull/3313))
A few small lemmas about `to_nat` that I wanted while playing with exact sequences.

### [2020-07-08 05:45:29](https://github.com/leanprover-community/mathlib/commit/ff1aea5)
feat(data/equiv): α × α ≃ α for [subsingleton α] ([#3312](https://github.com/leanprover-community/mathlib/pull/3312))

### [2020-07-08 00:37:50](https://github.com/leanprover-community/mathlib/commit/e987f62)
chore(scripts): update nolints.txt ([#3311](https://github.com/leanprover-community/mathlib/pull/3311))
I am happy to remove some nolints for you!

### [2020-07-07 19:51:20](https://github.com/leanprover-community/mathlib/commit/23f449b)
feat(topology/metric_space/basic): add closed_ball_mem_nhds ([#3305](https://github.com/leanprover-community/mathlib/pull/3305))
I found this lemma handy when converting between the epsilon-N definition of convergence and the filter definition

### [2020-07-07 17:45:54](https://github.com/leanprover-community/mathlib/commit/35940dd)
feat(linear_algebra/finite_dimensional): add dim_sup_add_dim_inf_eq ([#3304](https://github.com/leanprover-community/mathlib/pull/3304))
Adding a finite-dimensional version of dim(W+X)+dim(W \cap X)=dim(W)+dim(X)

### [2020-07-07 16:39:23](https://github.com/leanprover-community/mathlib/commit/ea10944)
feat(data/list/defs): list.singleton_append and list.bind_singleton ([#3298](https://github.com/leanprover-community/mathlib/pull/3298))
I found these useful when working with palindromes and Fibonacci words respectively.
While `bind_singleton` is available as a monad law, I find the specialized version more convenient.

### [2020-07-07 15:15:11](https://github.com/leanprover-community/mathlib/commit/11ba687)
chore(algebra/big_operators): use proper `*_with_zero` class in `prod_eq_zero(_iff)` ([#3303](https://github.com/leanprover-community/mathlib/pull/3303))
Also add a missing instance `comm_semiring → comm_monoid_with_zero`.

### [2020-07-07 09:59:21](https://github.com/leanprover-community/mathlib/commit/12c2acb)
feat(algebra/continued_fractions): add first set of approximation lemmas ([#3218](https://github.com/leanprover-community/mathlib/pull/3218))

### [2020-07-07 09:25:12](https://github.com/leanprover-community/mathlib/commit/08ffbbb)
feat(analysis/normed_space/operator_norm): normed algebra of continuous linear maps ([#3282](https://github.com/leanprover-community/mathlib/pull/3282))
Given a normed space `E`, its continuous linear endomorphisms form a normed ring, and a normed algebra if `E` is nonzero.  Moreover, the units of this ring are precisely the continuous linear equivalences.

### [2020-07-07 04:39:03](https://github.com/leanprover-community/mathlib/commit/095445e)
refactor(order/*): make `data.set.basic` import `order.bounded_lattice` ([#3285](https://github.com/leanprover-community/mathlib/pull/3285))
I have two goals:
* make it possible to refactor `set` to use `lattice` operations;
* make `submonoid.basic` independent of `data.nat.basic`.

### [2020-07-07 00:37:33](https://github.com/leanprover-community/mathlib/commit/d62e71d)
chore(scripts): update nolints.txt ([#3302](https://github.com/leanprover-community/mathlib/pull/3302))
I am happy to remove some nolints for you!

### [2020-07-06 20:20:45](https://github.com/leanprover-community/mathlib/commit/f548db4)
feat(linear_algebra/affine_space): lattice structure on affine subspaces ([#3288](https://github.com/leanprover-community/mathlib/pull/3288))
Define a `complete_lattice` instance on affine subspaces of an affine
space, and prove a few basic lemmas relating to it.  (There are plenty
more things that could be proved about it, that I think can reasonably
be added later.)

### [2020-07-06 19:04:56](https://github.com/leanprover-community/mathlib/commit/edd29d0)
chore(ring_theory/power_series): weaken assumptions for nontrivial ([#3301](https://github.com/leanprover-community/mathlib/pull/3301))

### [2020-07-06 17:34:23](https://github.com/leanprover-community/mathlib/commit/c0926f0)
chore(*): update to lean 3.17.0 ([#3300](https://github.com/leanprover-community/mathlib/pull/3300))

### [2020-07-06 16:58:21](https://github.com/leanprover-community/mathlib/commit/f06e4e0)
feat(data/sym2) Defining the symmetric square (unordered pairs) ([#3264](https://github.com/leanprover-community/mathlib/pull/3264))
This adds a type for the symmetric square of a type, which is the quotient of the cartesian square by permutations.  These are also known as unordered pairs.
Additionally, this provides some definitions and lemmas for equalities, functoriality, membership, and a relationship between symmetric relations and terms of the symmetric square.
I preferred `sym2` over `unordered_pairs` out of a combination of familiarity and brevity, but I could go either way for naming.

### [2020-07-06 15:34:25](https://github.com/leanprover-community/mathlib/commit/e3a1a61)
feat(tactic/interactive): identity tactic ([#3295](https://github.com/leanprover-community/mathlib/pull/3295))
A surprisingly missing tactic combinator.

### [2020-07-06 14:12:29](https://github.com/leanprover-community/mathlib/commit/33b6cba)
refactor(*): replace nonzero with nontrivial ([#3296](https://github.com/leanprover-community/mathlib/pull/3296))
Introduce a typeclass `nontrivial` saying that a type has at least two distinct elements, and use it instead of the predicate `nonzero` requiring that `0` is different from `1`. These two predicates are equivalent in monoids with zero, which cover essentially all relevant ring-like situations, but `nontrivial` applies also to say that a vector space is nontrivial, for instance.
Along the way, fix some quirks in the alebraic hierarchy (replacing fields `zero_ne_one` in many structures with extending `nontrivial`, for instance). Also, `quadratic_reciprocity` was timing out. I guess it was just below the threshold before the refactoring, and some of the changes related to typeclass inference made it just above after the change. So, I squeeze_simped it, going from 47s to 1.7s on my computer.
Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/nonsingleton/near/202865366

### [2020-07-06 13:27:20](https://github.com/leanprover-community/mathlib/commit/2c9d9bd)
chore(scripts/nolints_summary.sh): list number of nolints per file

### [2020-07-06 07:16:47](https://github.com/leanprover-community/mathlib/commit/5ff099b)
feat(topology): preliminaries for Haar measure ([#3194](https://github.com/leanprover-community/mathlib/pull/3194))
Define group operations on sets
Define compacts, in a similar way to opens
Prove some "separation" properties for topological groups
Rename `continuous.comap` to `opens.comap` (so that we can have comaps for other kinds of sets in topological spaces)
Rename `inf_val` to `inf_def` (unused)
Move some definitions from `topology.opens` to `topology.compacts`

### [2020-07-06 05:41:46](https://github.com/leanprover-community/mathlib/commit/2e140f1)
refactor(algebra/inj_surj): more lemmas, move to files, rename ([#3290](https://github.com/leanprover-community/mathlib/pull/3290))
* use names `function.?jective.monoid` etc;
* move definitions to different files;
* add versions for `semimodules` and various `*_with_zero`;
* add `funciton.surjective.forall` etc.

### [2020-07-06 04:31:33](https://github.com/leanprover-community/mathlib/commit/ffa504c)
fix(finset/lattice): undo removal of bUnion_preimage_singleton ([#3293](https://github.com/leanprover-community/mathlib/pull/3293))
In [#3189](https://github.com/leanprover-community/mathlib/pull/3189) I removed it, which was a mistake.

### [2020-07-06 00:39:48](https://github.com/leanprover-community/mathlib/commit/e1f6ed2)
chore(scripts): update nolints.txt ([#3294](https://github.com/leanprover-community/mathlib/pull/3294))
I am happy to remove some nolints for you!

### [2020-07-05 10:40:51](https://github.com/leanprover-community/mathlib/commit/0cd500e)
doc(tactic/explode): expand doc string ([#3271](https://github.com/leanprover-community/mathlib/pull/3271))
Explanation copied from @digama0's Zulip message [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.23explode.20error/near/202396813). Also removed a redundant function and added some type ascriptions.

### [2020-07-05 10:13:00](https://github.com/leanprover-community/mathlib/commit/293287d)
chore(category_theory/over/limits): change instance to def ([#3281](https://github.com/leanprover-community/mathlib/pull/3281))
Having this as an instance causes confusion since it's a different terminal object to the one inferred by the other limit constructions in the file.

### [2020-07-05 09:46:41](https://github.com/leanprover-community/mathlib/commit/f39e0d7)
chore(algebra/category): use preadditivity for biproducts ([#3280](https://github.com/leanprover-community/mathlib/pull/3280))
We can avoid some scary calculations thanks to abstract nonsense.

### [2020-07-04 19:11:32](https://github.com/leanprover-community/mathlib/commit/023d4f7)
feat(ring_theory/localization): order embedding of ideals, local ring instance ([#3287](https://github.com/leanprover-community/mathlib/pull/3287))

### [2020-07-04 15:02:36](https://github.com/leanprover-community/mathlib/commit/08e1adc)
feat(data/pnat): basic pnat facts needed for perfect numbers (3094) ([#3274](https://github.com/leanprover-community/mathlib/pull/3274))
define pnat.coprime
add some basic lemmas pnats, mostly about coprime, gcd
designate some existing lemmas with @[simp]

### [2020-07-04 08:32:44](https://github.com/leanprover-community/mathlib/commit/0d249d7)
feat(analysis/normed_space/*): group of units of a normed ring is open ([#3210](https://github.com/leanprover-community/mathlib/pull/3210))
In a complete normed ring, the group of units is an open subset of the ring ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Inversion.20is.20analytic))
Supporting material:
* `topology.metric_space.basic`, `analysis.normed_space.basic`, `normed_space.operator_norm`: some lemmas about limits and infinite sums in metric and normed spaces
* `analysis.normed_space.basic`, `normed_space.operator_norm`: left- and right- multiplication in a normed ring (algebra) is a bounded homomorphism (linear map); the algebra/linear-map versions are not needed for the main result but included for completeness
* `analysis.normed_space.basic`: a normed algebra is `nonzero` (not needed for the main result) ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Dangerous.20instance))
* `algebra.group_with_zero`: the `subsingleton_or_nonzero` dichotomy for monoids with zero ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/zero.20ring/near/202202187)) (written by @jcommelin )
* `analysis.specific_limits`: results on geometric series in a complete `normed_ring`; relies on
* `algebra.geom_sum`: "left" variants of some existing "right" lemmas on finite geometric series; relies on
* `algebra.opposites`, `algebra.group_power`, `algebra.big_operators`: lemmas about the opposite ring ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Finite.20geometric.20series))

### [2020-07-04 06:17:21](https://github.com/leanprover-community/mathlib/commit/c2886d3)
fix(tactic/default): import tactic.basic ([#3284](https://github.com/leanprover-community/mathlib/pull/3284))
Some basic tactics and commands (e.g. `#explode`) were not available even if `import tactic` was used. I added `import tactic.basic` to `tactic/default.lean` to remedy this.

### [2020-07-04 00:39:31](https://github.com/leanprover-community/mathlib/commit/2a43e26)
chore(scripts): update nolints.txt ([#3283](https://github.com/leanprover-community/mathlib/pull/3283))
I am happy to remove some nolints for you!

### [2020-07-03 23:00:44](https://github.com/leanprover-community/mathlib/commit/742dc88)
feat(ring_theory/polynomial): rational root theorem and integral root theorem ([#3241](https://github.com/leanprover-community/mathlib/pull/3241))
Prove the rational root theorem for a unique factorization domain `A`: Let `K` be the field of fractions of `A` and `p` a polynomial over `A`. If `x : K` is a root of `p`, then the numerator of `x` divides the constant coefficient and the denominator of `x` divides the leading coefficient. (This required defining the numerator and denominator.) As a corollary we have the integral root theorem: if `p` is monic, then its roots in `K` are in fact elements of `A`. As a second corollary, the integral closure of `A` in `K` is `A` itself.

### [2020-07-03 22:00:28](https://github.com/leanprover-community/mathlib/commit/c4bf9e4)
chore(algebra/ordered_group): deduplicate ([#3279](https://github.com/leanprover-community/mathlib/pull/3279))
For historical reasons we have some lemmas duplicated for `ordered_comm_monoid`
and `ordered_cancel_comm_monoid`. This PR merges some duplicates.

### [2020-07-03 22:00:26](https://github.com/leanprover-community/mathlib/commit/f1637e5)
feat(field_theory/splitting_field): definition of splitting field ([#3272](https://github.com/leanprover-community/mathlib/pull/3272))

### [2020-07-03 20:42:56](https://github.com/leanprover-community/mathlib/commit/48dea2f)
feat(algebra/pointwise): make instances global ([#3240](https://github.com/leanprover-community/mathlib/pull/3240))
add image2 and image3, the images of binary and ternary functions
cleanup in algebra/pointwise
make many variables implicit
make many names shorter
add some lemmas
add more simp lemmas
add type set_semiring as alias for set, with semiring instance using union as "addition"

### [2020-07-03 15:04:51](https://github.com/leanprover-community/mathlib/commit/f9f0ca6)
feat(analysic/calculus/times_cont_diff): add times_cont_diff_within_at ([#3262](https://github.com/leanprover-community/mathlib/pull/3262))
I want to refactor manifolds, defining local properties in the model space and showing that they automatically inherit nice behavior in manifolds. 
In this PR, we modify a little bit the definition of smooth functions in vector spaces by introducing a predicate `times_cont_diff_within_at` (just like we already have `continuous_within_at` or `differentiable_within_at`) and using it in all definitions and proofs. This will be the basis of the locality argument in manifolds.

### [2020-07-03 09:21:25](https://github.com/leanprover-community/mathlib/commit/53c1531)
feat(geometry/manifold/smooth_manifold_with_corners): product of smooth manifolds with corners ([#3250](https://github.com/leanprover-community/mathlib/pull/3250))

### [2020-07-03 08:38:36](https://github.com/leanprover-community/mathlib/commit/e236160)
chore(order/filter/basic): implicit arg in `eventually_of_forall` ([#3277](https://github.com/leanprover-community/mathlib/pull/3277))
Make `l : filter α` argument of `eventually_of_forall` implicit
because everywhere in `mathlib` it was used as `eventually_of_forall _`.

### [2020-07-03 07:27:21](https://github.com/leanprover-community/mathlib/commit/56ed551)
fix(algebra/group_with_zero): fix left/right ([#3278](https://github.com/leanprover-community/mathlib/pull/3278))
Rename `mul_inv_cancel_left'`/`mul_inv_cancel_right'` to match
`mul_inv_cancel_left`/`mul_inv_cancel_right`.

### [2020-07-03 04:28:12](https://github.com/leanprover-community/mathlib/commit/303740d)
feat(category_theory/abelian): every abelian category is preadditive  ([#3247](https://github.com/leanprover-community/mathlib/pull/3247))

### [2020-07-03 00:58:35](https://github.com/leanprover-community/mathlib/commit/9b086e1)
chore(*): reduce imports ([#3235](https://github.com/leanprover-community/mathlib/pull/3235))
The RFC pull request simply removes some `import tactic` or `import tactic.basic`, and then makes the necessary changes in later files to import things as needed.
I'm not sure if it's useful or not

### [2020-07-03 00:22:34](https://github.com/leanprover-community/mathlib/commit/6a49975)
feat(category_theory/limits): fully faithful functors reflect limits and colimits ([#3269](https://github.com/leanprover-community/mathlib/pull/3269))
A fully faithful functor reflects limits and colimits

### [2020-07-02 20:45:17](https://github.com/leanprover-community/mathlib/commit/838dc66)
feat(topology/basic): add `eventually_eventually_nhds` ([#3266](https://github.com/leanprover-community/mathlib/pull/3266))

### [2020-07-02 19:38:26](https://github.com/leanprover-community/mathlib/commit/d84c48c)
feat(data/real/cardinality): cardinalities of intervals of reals ([#3252](https://github.com/leanprover-community/mathlib/pull/3252))
Use the existing result `mk_real` to deduce corresponding results for
all eight kinds of intervals of reals.
It's convenient for this result to add a new lemma to
`data.set.intervals.image_preimage` about the image of an interval
under `inv`.  Just as there are only a few results there about images
of intervals under multiplication rather than a full set, so I just
added the result I needed rather than all the possible variants.  (I
think there are something like 36 reasonable variants of that lemma
that could be stated, for (image or preimage - the same thing in this
case, but still separate statements) x (interval in positive or
negative reals) x (end closer to 0 is 0 (open), nonzero (open) or
nonzero (closed)) x (other end is open, closed or infinite).)

### [2020-07-02 18:55:47](https://github.com/leanprover-community/mathlib/commit/e4fdc75)
refactor(analysis/calculus/*deriv): use eventually_eq in congruence statements ([#3261](https://github.com/leanprover-community/mathlib/pull/3261))
Use `eventually_eq` instead of `mem_sets` for congruence lemmas in continuity and differentiability statements.

### [2020-07-02 18:14:59](https://github.com/leanprover-community/mathlib/commit/237b1ea)
feat(analysis/specific_limits): proof of harmonic series diverging and preliminaries ([#3233](https://github.com/leanprover-community/mathlib/pull/3233))
This PR is made of two parts : 
- A few new generic lemmas, mostly by @PatrickMassot , in `order/filter/at_top_bot.lean` and `topology/algebra/ordered.lean`
- Definition of the harmonic series, basic lemmas about it, and proof of its divergence, in `analysis/specific_limits.lean`
Zulip : https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Harmonic.20Series.20Divergence/near/201651652

### [2020-07-02 13:05:20](https://github.com/leanprover-community/mathlib/commit/8be66ee)
fix(library_search): fix a bug with iff lemmas where both sides match ([#3270](https://github.com/leanprover-community/mathlib/pull/3270))
Also add a proper failure message for `library_search`, using Mario's text.

### [2020-07-02 13:05:18](https://github.com/leanprover-community/mathlib/commit/18a80ea)
chore(tactic/noncomm_ring): allow simp to fail ([#3268](https://github.com/leanprover-community/mathlib/pull/3268))
Fixes [#3267](https://github.com/leanprover-community/mathlib/pull/3267).

### [2020-07-02 10:27:52](https://github.com/leanprover-community/mathlib/commit/dc1d936)
feat(data/polynomial): preliminaries for Cayley-Hamilton ([#3243](https://github.com/leanprover-community/mathlib/pull/3243))
Many cheerful facts about polynomials!

### [2020-07-02 00:35:42](https://github.com/leanprover-community/mathlib/commit/cd29ede)
chore(scripts): update nolints.txt ([#3265](https://github.com/leanprover-community/mathlib/pull/3265))
I am happy to remove some nolints for you!

### [2020-07-01 23:16:08](https://github.com/leanprover-community/mathlib/commit/9309910)
chore(algebra/*): deduplicate `*_with_zero`/`semiring`/`field` ([#3259](https://github.com/leanprover-community/mathlib/pull/3259))
All moved/renamed/merged lemmas were generalized to use
`*_with_zero`/`nonzero`/`mul_zero_class` instead of
`(semi)ring`/`division_ring`/`field`.
## Moved to `group_with_zero`
The following lemmas were formulated for
`(semi_)ring`s/`division_ring`s/`field`s. Some of them had strictly
more general “prime” versions for `*_with_zero`. I either moved a
lemma to `algebra/group_with_zero` and adjusted the requirements or
removed the non-prime version and `'` from the name of the prime
version. Sometimes I also made some arguments implicit.
TL;DR: moved to `group_with_zero`, removed `name'` lemma if it was there.
* `is_unit_zero_iff`;
* `not_is_unit_zero`;
* `div_eq_one_iff_eq`;
* `eq_div_iff_mul_eq`;
* `eq_div_of_mul_eq`;
* `eq_one_div_of_mul_eq_one`;
* `eq_one_div_of_mul_eq_one_left`;
* `one_div_one_div`;
* `eq_of_one_div_eq_one_div`;
* `one_div_div`;
* `mul_eq_of_eq_div`;
* `mul_mul_div`;
* `eq_zero_of_zero_eq_one`;
* `eq_inv_of_mul_right_eq_one`;
* `eq_inv_of_mul_left_eq_one`;
* `div_right_comm`;
* `div_div_div_cancel_right`;
* `div_mul_div_cancel`;
## Renamed/merged
* rename `mul_inv''` to `mul_inv'` and merge `mul_inv'` into `mul_inv_rev'`;
* `coe_unit_mul_inv`, `coe_unit_inv_mul`: `units.mul_inv'`, `units.inv_mul'`
* `division_ring.inv_eq_iff`: `inv_eq_iff`;
* `division_ring.inv_inj`: `inv_inj'`;
* `domain.mul_left_inj`: `mul_left_inj'`;
* `domain.mul_right_inj`: `mul_right_inj'`;
* `eq_of_mul_eq_mul_of_nonzero_left` and `eq_of_mul_eq_mul_left`: `mul_left_cancel'`;
* `eq_of_mul_eq_mul_of_nonzero_right` and `eq_of_mul_eq_mul_right`: `mul_right_cancel'`;
* `inv_inj`, `inv_inj'`, `inv_inj''`: `inv_injective`, `inv_inj`, and `inv_inj'`, respectively;
* `mul_inv_cancel_assoc_left`, `mul_inv_cancel_assoc_right`,
  `inv_mul_cancel_assoc_left`, `inv_mul_cancel_assoc_right`:
  `mul_inv_cancel_left'`, `mul_inv_cacnel_right'`,
  `inv_mul_cancel_left'`, `inv_mul_cancel_right'`;
* `ne_zero_and_ne_zero_of_mul_ne_zero` : `ne_zero_and_ne_zero_of_mul`.
* `ne_zero_of_mul_left_eq_one`: `left_ne_zero_of_mul_eq_one`
* `ne_zero_of_mul_ne_zero_left` : `right_ne_zero_of_mul`;
* `ne_zero_of_mul_ne_zero_right` : `left_ne_zero_of_mul`;
* `ne_zero_of_mul_right_eq_one`: `left_ne_zero_of_mul_eq_one`
* `neg_inj` and `neg_inj` renamed to `neg_injective` and `neg_inj`;
* `one_inv_eq`: merged into `inv_one`;
* `unit_ne_zero`: `units.ne_zero`;
* `units.mul_inv'` and `units.inv_mul'`: `units.mul_inv_of_eq` and `units.inv_mul_of_eq`;
* `units.mul_left_eq_zero_iff_eq_zero`,
  `units.mul_right_eq_zero_iff_eq_zero`: `units.mul_left_eq_zero`,
  `units.mul_right_eq_zero`;
## New
* `class cancel_monoid_with_zero`: a `monoid_with_zero` such that
  left/right multiplication by a non-zero element is injective; the
  main instances are `group_with_zero`s and `domain`s;
* `monoid_hom.map_ne_zero`, `monoid_hom.map_eq_zero`,
  `monoid_hom.map_inv'`, `monoid_hom.map_div`, `monoid_hom.injective`:
  lemmas about monoid homomorphisms of two groups with zeros such that
  `f 0 = 0`;
* `mul_eq_zero_of_left`, `mul_eq_zero_of_right`, `ne_zero_of_eq_one`
* `unique_of_zero_eq_one`, `eq_of_zero_eq_one`, `nonzero_psum_unique`,
  `zero_ne_one_or_forall_eq_0`;
* `mul_left_inj'`, `mul_right_inj'`
## Misc changes
* `eq_of_div_eq_one` no more requires `b ≠ 0`;

### [2020-07-01 18:46:03](https://github.com/leanprover-community/mathlib/commit/1a419a9)
feat(data/nat/digits): add digits_lt_base ([#3246](https://github.com/leanprover-community/mathlib/pull/3246))

### [2020-07-01 17:12:55](https://github.com/leanprover-community/mathlib/commit/f00b7c0)
chore(*): work on removing deprecated is_X_hom typeclasses ([#3258](https://github.com/leanprover-community/mathlib/pull/3258))
It's far from over, but as I was bumping up against issues in `polynomial.lean` and `mv_polynomial.lean`, I'm going to PR this part for now, and then wait to return to it when other PRs affecting `polynomial.lean` have cleared.

### [2020-07-01 12:12:44](https://github.com/leanprover-community/mathlib/commit/e803c85)
feat(field_theory/separable): relating irreducibility and separability ([#3198](https://github.com/leanprover-community/mathlib/pull/3198))

### [2020-07-01 10:05:14](https://github.com/leanprover-community/mathlib/commit/a7cdab5)
chore(data/set/basic): simp attribute on mem_range_self ([#3260](https://github.com/leanprover-community/mathlib/pull/3260))

### [2020-07-01 10:05:12](https://github.com/leanprover-community/mathlib/commit/7bd19b3)
chore(data/finset, data/multiset): split into smaller files ([#3256](https://github.com/leanprover-community/mathlib/pull/3256))
This follows on from [#2341](https://github.com/leanprover-community/mathlib/pull/2341), which split the second half of `data.list.basic` into separate files. This now does the same (trying to follow a similar split) for `data.multiset` and `data.finset`.

### [2020-07-01 10:05:10](https://github.com/leanprover-community/mathlib/commit/8ba7595)
feat(category/preadditive): properties of preadditive biproducts ([#3245](https://github.com/leanprover-community/mathlib/pull/3245))
### Basic facts about morphisms between biproducts in preadditive categories.
* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.
The remaining lemmas hold in any preadditive category.
* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.
* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.
* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.
* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.
This PR is preliminary to some work on semisimple categories.

### [2020-07-01 09:03:47](https://github.com/leanprover-community/mathlib/commit/aff951a)
chore(algebra/big_operators): don't use omega ([#3255](https://github.com/leanprover-community/mathlib/pull/3255))
Postpone importing `omega` a little bit longer.

### [2020-07-01 07:55:07](https://github.com/leanprover-community/mathlib/commit/e68503a)
feat(ring_theory/valuation): definition and basic properties of valuations ([#3222](https://github.com/leanprover-community/mathlib/pull/3222))
From the perfectoid project.

### [2020-07-01 03:39:36](https://github.com/leanprover-community/mathlib/commit/a22cd4d)
chore(algebra/group_with_zero): nolint ([#3254](https://github.com/leanprover-community/mathlib/pull/3254))
Adding two doc strings to make the file lint-free again. cf. [#3253](https://github.com/leanprover-community/mathlib/pull/3253).

### [2020-07-01 01:31:04](https://github.com/leanprover-community/mathlib/commit/859edfb)
chore(scripts): update nolints.txt ([#3253](https://github.com/leanprover-community/mathlib/pull/3253))
I am happy to remove some nolints for you!

### [2020-07-01 00:28:03](https://github.com/leanprover-community/mathlib/commit/89f3bbc)
feat(data/matrix): std_basis_matrix ([#3244](https://github.com/leanprover-community/mathlib/pull/3244))
The definition of
```
def std_basis_matrix (i : m) (j : n) (a : α) : matrix m n α :=
(λ i' j', if i' = i ∧ j' = j then a else 0)
```
and associated lemmas, and some refactoring of `src/ring_theory/matrix_algebra.lean` to use it.
This is work of @jalex-stark which I'm PR'ing as part of getting Cayley-Hamilton ready.

### [2020-07-01 00:02:51](https://github.com/leanprover-community/mathlib/commit/a40be98)
feat(category_theory/limits/shapes): simp lemmas to decompose pullback_cone.mk.fst ([#3249](https://github.com/leanprover-community/mathlib/pull/3249))
Decompose `(pullback_cone.mk _ _ _).fst` into its first component (+symmetrical and dual versions)