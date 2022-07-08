### [2020-04-30 21:10:46](https://github.com/leanprover-community/mathlib/commit/c568bb4)
fix(scripts): stop updating mathlib-nightly repository ([#2576](https://github.com/leanprover-community/mathlib/pull/2576))
The `gothub` tool that we've used to push the nightlies doesn't build at the moment.  Now that we have `leanproject`, we no longer need the separate nightlies repository.

### [2020-04-30 21:10:44](https://github.com/leanprover-community/mathlib/commit/06adf7d)
chore(scripts): update nolints.txt ([#2572](https://github.com/leanprover-community/mathlib/pull/2572))
I am happy to remove some nolints for you!

### [2020-04-30 18:20:23](https://github.com/leanprover-community/mathlib/commit/caf93b7)
feat(*): small additions that prepare for Chevalley-Warning ([#2560](https://github.com/leanprover-community/mathlib/pull/2560))
A number a small changes that prepare for [#1564](https://github.com/leanprover-community/mathlib/pull/1564).

### [2020-04-30 14:07:21](https://github.com/leanprover-community/mathlib/commit/8fa8f17)
refactor(tsum): use ∑' instead of ∑ as notation ([#2571](https://github.com/leanprover-community/mathlib/pull/2571))
As discussed in: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/big.20ops/near/195821357
This is the result of
```
git grep -l '∑' | grep -v "mean_ineq" | xargs sed -i "s/∑/∑'/g"
```
after manually cleaning some occurences of `∑` in TeX strings. Probably `∑` has now also been changed in a lot of comments and docstrings, but my reasoning is that if the string "tsum" occurs in the file, then it doesn't do harm to write `∑'` instead of `∑` in the comments as well.

### [2020-04-30 14:07:19](https://github.com/leanprover-community/mathlib/commit/ee70afb)
doc(.github): remove pull-request template ([#2568](https://github.com/leanprover-community/mathlib/pull/2568))
Move the pull-request template to `CONTRIBUTING.md`.  This reduces the boilerplate in the PR description that almost nobody reads anyhow.

### [2020-04-30 11:23:34](https://github.com/leanprover-community/mathlib/commit/9c8bc7a)
fix(tactic/interactive): make `inhabit` work on quantified goals ([#2570](https://github.com/leanprover-community/mathlib/pull/2570))
This didn't work before because of the `∀` in the goal:
```lean
lemma c {α} [nonempty α] : ∀ n : ℕ, ∃ b : α, n = n :=
by inhabit α; intro; use default _; refl
```

### [2020-04-30 07:10:15](https://github.com/leanprover-community/mathlib/commit/b14a26e)
refactor(analysis/complex/exponential): split into three files in special_functions/ ([#2565](https://github.com/leanprover-community/mathlib/pull/2565))
The file `analysis/complex/exponential.lean` was growing out of control (2500 lines) and was dealing with complex and real exponentials, trigonometric functions, and power functions. I split it into three files corresponding to these three topics, and put them instead in `analysis/special_functions/`, as it was not specifically complex.
This is purely a refactor, so absolutely no new material nor changed proof.
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232565.20exponential.20split

### [2020-04-29 17:26:19](https://github.com/leanprover-community/mathlib/commit/e6491de)
chore(data/equiv/ring): make ring_aut reducible ([#2563](https://github.com/leanprover-community/mathlib/pull/2563))
This makes the coercion to fun work. This is the same approach as we used for `perm` and it worked okay for `perm`.
Related Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_aut.20coerce.20to.20function

### [2020-04-29 16:12:56](https://github.com/leanprover-community/mathlib/commit/8490c54)
refactor(analysis/complex/exponential): define log x = log |x|  for x < 0 ([#2564](https://github.com/leanprover-community/mathlib/pull/2564))
Previously we had `log  x = 0` for `x < 0`. This PR changes it to `log x = log (-x)`, to make sure that the formulas `log (xy) = log x + log y` and `log' = 1/x` are true for all nonzero variables.
Also, add a few simp lemmas on the differentiability properties of `log` to make sure that the following works:
```lean
example (x : ℝ) (h : x ≠ 0) : deriv (λ x, x * (log x - 1)) x = log x :=
by simp [h]
```
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/definition.20of.20real.20log

### [2020-04-29 13:32:57](https://github.com/leanprover-community/mathlib/commit/4580069)
feat(field_theory/subfield): is_subfield.inter and is_subfield.Inter ([#2562](https://github.com/leanprover-community/mathlib/pull/2562))
Prove that intersection of subfields is subfield.

### [2020-04-29 10:32:44](https://github.com/leanprover-community/mathlib/commit/84f8b39)
chore(data/nat/basic): move `iterate_inj` to `injective.iterate` ([#2561](https://github.com/leanprover-community/mathlib/pull/2561))
Also add versions for `surjective` and `bijective`

### [2020-04-29 07:43:15](https://github.com/leanprover-community/mathlib/commit/f8fe596)
chore(algebra/*): missing `simp`/`inj` lemmas ([#2557](https://github.com/leanprover-community/mathlib/pull/2557))
Sometimes I have a specialized `ext` lemma for `A →+ B` that uses structure of `A` (e.g., `A = monoid_algebra α R`) and want to apply it to `A →+* B` or `A →ₐ[R] B`. These `coe_*_inj` lemmas make it easier.
Also add missing `simp` lemmas for bundled multiplication and rename `pow_of_add` and `gpow_of_add` to `of_add_smul` and `of_add_gsmul`, respectively.

### [2020-04-29 05:44:26](https://github.com/leanprover-community/mathlib/commit/cb3a017)
chore(category_theory): remove `[𝒞 : category.{v₁} C] / include 𝒞` ([#2556](https://github.com/leanprover-community/mathlib/pull/2556))
It is no longer necessary in Lean 3.9.0, thanks to
https://github.com/leanprover-community/lean/commit/01063857bb6814374156433e8cbc0c94a9483f52

### [2020-04-29 04:34:22](https://github.com/leanprover-community/mathlib/commit/ba9fc4d)
doc(install/*): remove outdated youtube links ([#2559](https://github.com/leanprover-community/mathlib/pull/2559))
Fixes [#2558](https://github.com/leanprover-community/mathlib/pull/2558).

### [2020-04-28 23:03:24](https://github.com/leanprover-community/mathlib/commit/94ff59a)
chore(scripts): update nolints.txt ([#2555](https://github.com/leanprover-community/mathlib/pull/2555))
I am happy to remove some nolints for you!

### [2020-04-28 19:57:52](https://github.com/leanprover-community/mathlib/commit/d12db89)
chore(category): rename to control ([#2516](https://github.com/leanprover-community/mathlib/pull/2516))
This is parallel to https://github.com/leanprover-community/lean/pull/202 for community Lean (now merged).
It seems the changes are actually completely independent; this compiles against current community Lean, and that PR. (I'm surprised, but I guess it's just that everything is in the root namespace, and in `init/`.)
This PR anticipates then renaming `category_theory/` to `category/`.

### [2020-04-28 19:57:50](https://github.com/leanprover-community/mathlib/commit/c435b1c)
feat(analysis/calculus/inverse): Inverse function theorem ([#2228](https://github.com/leanprover-community/mathlib/pull/2228))
Ref [#1849](https://github.com/leanprover-community/mathlib/pull/1849)

### [2020-04-28 17:54:30](https://github.com/leanprover-community/mathlib/commit/3c02800)
chore(data/dfinsupp): use more precise `decidable` requirement ([#2535](https://github.com/leanprover-community/mathlib/pull/2535))
Removed `decidable_zero_symm` and replaced all `[Π i, decidable_pred (eq (0 : β i))]` with `[Π i (x : β i), decidable (x ≠ 0)]`. This should work better with `open_locale classical` because now the lemmas and definitions don't assume that `[Π i (x : β i), decidable (x ≠ 0)]` comes from `decidable_zero_symm`.

### [2020-04-28 15:02:18](https://github.com/leanprover-community/mathlib/commit/f6c9372)
feat(data/fin): add some lemmas about coercions ([#2522](https://github.com/leanprover-community/mathlib/pull/2522))
Two of these lemmas allow norm_cast to work with inequalities
involving fin values converted to ℕ.  The rest are for simplifying
expressions where coercions are used to convert from ℕ to fin, in
cases where an inequality means those coercions do not in fact change
the value.
There are very few lemmas relating to coercions from ℕ to fin in
mathlib at present; the lemma of_nat_eq_coe (and val_add on which it
depends, and a few similarly trivial lemmas alongside val_add) is
moved from data.zmod.basic to fin.basic for use in proving the other
lemmas, while the nat lemma add_mod is moved to data.nat.basic for use
in the proof of of_nat_eq_coe, and mul_mod is moved alongside it as
suggested in review.  These lemmas were found useful in formalising
solutions to an olympiad problem, see
<https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations>,
and seem more generally relevant than to just that particular problem.

### [2020-04-28 12:08:15](https://github.com/leanprover-community/mathlib/commit/f567962)
feat(data/complex/basic): inv_I and div_I ([#2550](https://github.com/leanprover-community/mathlib/pull/2550))

### [2020-04-28 12:08:13](https://github.com/leanprover-community/mathlib/commit/9c81886)
fix(tactic/doc_commands): clean up copy_doc_string command ([#2543](https://github.com/leanprover-community/mathlib/pull/2543))
[#2471](https://github.com/leanprover-community/mathlib/pull/2471) added a command for copying a doc string from one decl to another. This PR:
* documents this command
* extends it to copy to a list of decls
* moves `add_doc_string` from root to the `tactic` namespace

### [2020-04-28 06:54:15](https://github.com/leanprover-community/mathlib/commit/ae06db3)
feat(category_theory/concrete): make constructing morphisms easier ([#2502](https://github.com/leanprover-community/mathlib/pull/2502))
Previously, if you wrote:
```lean
example (R : CommMon.{u}) : R ⟶ R :=
{ to_fun := λ x, _,
  map_one' := sorry,
  map_mul' := sorry, }
```
you were told the expected type was `↥(bundled.map comm_monoid.to_monoid R)`, which is not particularly reassuring unless you understand the details of how we've set up concrete categories.
If you called `dsimp`, this got better, just giving `R.α`. This still isn't ideal, as we prefer to talk about the underlying type of a bundled object via the coercion, not the structure projection.
After this PR, which provides a slightly different mechanism for constructing "induced" categories from bundled categories, the expected type is exactly what you might have hoped for: `↥R`.
There seems to be one place where we used to get away with writing `𝟙 _` and now have to write `𝟙 A`, but otherwise there appear to be no ill-effects of this change.
(For follow-up, I think I can entirely get rid of our `local attribute [reducible]` work-arounds when setting up concrete categories, and in fact construct most of the instances in `@[derive]` handlers, but these will be separate PRs.)

### [2020-04-27 16:34:48](https://github.com/leanprover-community/mathlib/commit/fd3afb4)
chore(ring_theory/algebra): move instances about complex to get rid of dependency ([#2549](https://github.com/leanprover-community/mathlib/pull/2549))
Previously `ring_theory.algebra` imported the complex numbers. This PR moves some instances in order to get rid of that dependency.

### [2020-04-27 14:30:55](https://github.com/leanprover-community/mathlib/commit/948d0ff)
chore(topology/algebra/module): don't use unbundled homs for `algebra` instance ([#2545](https://github.com/leanprover-community/mathlib/pull/2545))
Define special `algebra.of_semimodule` and `algebra.of_semimodule'`
constructors instead.
ref. [#2534](https://github.com/leanprover-community/mathlib/pull/2534)

### [2020-04-27 05:41:19](https://github.com/leanprover-community/mathlib/commit/2fc9b15)
chore(data/real/*): use bundled homs to prove `coe_sum` etc ([#2533](https://github.com/leanprover-community/mathlib/pull/2533))

### [2020-04-26 21:58:07](https://github.com/leanprover-community/mathlib/commit/134c5a5)
chore(scripts): update nolints.txt ([#2548](https://github.com/leanprover-community/mathlib/pull/2548))
I am happy to remove some nolints for you!

### [2020-04-26 20:47:49](https://github.com/leanprover-community/mathlib/commit/039c5a6)
chore(ring_theory/adjoin_root): drop `is_ring_hom` instance ([#2546](https://github.com/leanprover-community/mathlib/pull/2546))
ref [#2534](https://github.com/leanprover-community/mathlib/pull/2534)

### [2020-04-26 19:06:10](https://github.com/leanprover-community/mathlib/commit/942b795)
doc(field_theory/subfield): don't mention unbundled homs in the comment ([#2544](https://github.com/leanprover-community/mathlib/pull/2544))
ref [#2534](https://github.com/leanprover-community/mathlib/pull/2534)

### [2020-04-26 13:59:51](https://github.com/leanprover-community/mathlib/commit/fa13d16)
chore(scripts): update nolints.txt ([#2542](https://github.com/leanprover-community/mathlib/pull/2542))
I am happy to remove some nolints for you!

### [2020-04-26 12:04:36](https://github.com/leanprover-community/mathlib/commit/30ae5ba)
chore(scripts): update nolints.txt ([#2541](https://github.com/leanprover-community/mathlib/pull/2541))
I am happy to remove some nolints for you!

### [2020-04-26 12:04:34](https://github.com/leanprover-community/mathlib/commit/74b9647)
feat(measure_theory/measure_space): pigeonhole principle in a measure space ([#2538](https://github.com/leanprover-community/mathlib/pull/2538))
ref [#2272](https://github.com/leanprover-community/mathlib/pull/2272)

### [2020-04-26 09:29:30](https://github.com/leanprover-community/mathlib/commit/c170ce3)
chore(data/finset): add `coe_map`, `coe_image_subset_range`, and `coe_map_subset_range` ([#2530](https://github.com/leanprover-community/mathlib/pull/2530))

### [2020-04-26 09:29:28](https://github.com/leanprover-community/mathlib/commit/40e97d3)
feat(topology/algebra/module): ker, range, cod_restrict, subtype_val, coprod ([#2525](https://github.com/leanprover-community/mathlib/pull/2525))
Also move `smul_right` to `general_ring` and define some
maps/equivalences useful for the inverse/implicit function theorem.

### [2020-04-26 09:29:26](https://github.com/leanprover-community/mathlib/commit/11ccc1b)
feat(analysis/calculus/deriv): define `has_strict_deriv_at` ([#2524](https://github.com/leanprover-community/mathlib/pull/2524))
Also make more proofs explicitly use their `has_fderiv*` counterparts
and mark some lemmas in `fderiv` as `protected`.

### [2020-04-26 06:46:28](https://github.com/leanprover-community/mathlib/commit/21b7292)
feat(data/nat/basic): add `iterate_one` and `iterate_mul` ([#2540](https://github.com/leanprover-community/mathlib/pull/2540))

### [2020-04-26 06:46:26](https://github.com/leanprover-community/mathlib/commit/21d8e0a)
chore(data/real/ennreal): +2 simple lemmas ([#2539](https://github.com/leanprover-community/mathlib/pull/2539))
Extracted from [#2311](https://github.com/leanprover-community/mathlib/pull/2311)

### [2020-04-26 06:46:24](https://github.com/leanprover-community/mathlib/commit/401d321)
feat(analysis/normed_space/basic): add continuous_at.div ([#2532](https://github.com/leanprover-community/mathlib/pull/2532))
When proving a particular function continuous at a particular point,
lemmas such as continuous_at.mul, continuous_at.add and
continuous_at.comp can be used to build this up from continuity
properties of simpler functions.  It's convenient to have something
similar for division as well.
This adds continuous_at.div for normed fields, as suggested by Yury.
If mathlib gets topological (semi)fields in future, this should become
a result for those.

### [2020-04-26 06:46:22](https://github.com/leanprover-community/mathlib/commit/1182e91)
refactor(tactic/nth_rewrite): enable rewriting hypotheses, add docstrings ([#2471](https://github.com/leanprover-community/mathlib/pull/2471))
This PR
* renames the interactive tactic `perform_nth_rewrite` to `nth_rewrite`
* enables rewriting at hypotheses, instead of only the target
* renames the directory and namespace `rewrite_all` to `nth_rewrite`
* adds a bunch of docstrings

### [2020-04-26 03:56:10](https://github.com/leanprover-community/mathlib/commit/c34add7)
chore(scripts): update nolints.txt ([#2537](https://github.com/leanprover-community/mathlib/pull/2537))
I am happy to remove some nolints for you!

### [2020-04-26 03:56:08](https://github.com/leanprover-community/mathlib/commit/bda206a)
chore(data/option,order/bounded_lattice): 2 simple lemmas about `get_or_else` ([#2531](https://github.com/leanprover-community/mathlib/pull/2531))
I'm going to use these lemmas for `polynomial.nat_degree`. I don't want to PR
this change to `data/polynomial` because this would create merge conflicts later.

### [2020-04-26 03:56:06](https://github.com/leanprover-community/mathlib/commit/ee6f20a)
chore(algebra/module): use bundled homs for `smul_sum` and `sum_smul` ([#2529](https://github.com/leanprover-community/mathlib/pull/2529))

### [2020-04-25 23:03:27](https://github.com/leanprover-community/mathlib/commit/5219ca1)
doc(data/nat/modeq): add module docstring and lemma ([#2528](https://github.com/leanprover-community/mathlib/pull/2528))
I add a simple docstrong and also a lemma which I found useful for a codewars kata.

### [2020-04-25 23:03:25](https://github.com/leanprover-community/mathlib/commit/ba4dc1a)
doc(algebra/order_functions): add docstring and lemma ([#2526](https://github.com/leanprover-community/mathlib/pull/2526))
I added a missing lemma, and then figured that while I was here I should add a docstring

### [2020-04-25 19:55:53](https://github.com/leanprover-community/mathlib/commit/a8ae8e8)
feat(data/bool): add de Morgan's laws ([#2523](https://github.com/leanprover-community/mathlib/pull/2523))
I will go away with my tail between my legs if someone can show me that our esteemed mathematics library already contains de Morgan's laws for booleans. I also added a docstring. I can't lint the file because it's so high up in the import heirarchy, but I also added a docstring for the two instances.

### [2020-04-25 19:55:51](https://github.com/leanprover-community/mathlib/commit/94fd41a)
refactor(data/padics/*): use [fact p.prime] to assume that p is prime ([#2519](https://github.com/leanprover-community/mathlib/pull/2519))

### [2020-04-25 18:43:05](https://github.com/leanprover-community/mathlib/commit/632c4ba)
feat(continued_fractions) add equivalence of convergents computations ([#2459](https://github.com/leanprover-community/mathlib/pull/2459))
### What
Add lemmas showing that the two methods for computing the convergents of a continued fraction (recurrence relation vs direct evaluation) coincide. A high-level overview on how the proof works is given in the header of the file. 
### Why
One wants to be able to relate both computations. The recurrence relation can be faster to compute, the direct evaluation is more intuitive and might be easier for some proofs.
### How
The proof of the equivalence is by induction. To make the induction work, one needs to "squash" a sequence into a shorter one while maintaining the value of the convergents computations. Most lemmas in this commit deal with this squashing operation.

### [2020-04-25 09:58:14](https://github.com/leanprover-community/mathlib/commit/d9327e4)
refactor(geometry/manifold/real_instances): use fact instead of lt_class ([#2521](https://github.com/leanprover-community/mathlib/pull/2521))
To define a manifold with boundary structure on the interval `[x, y]`, typeclass inference needs to know that `x < y`. This used to be provided by the introduction of a dummy class `lt_class`. The new mechanism based on `fact` makes it possible to remove this dummy class.

### [2020-04-25 09:58:12](https://github.com/leanprover-community/mathlib/commit/2b95532)
refactor(*): use [fact p.prime] for frobenius and perfect_closure ([#2518](https://github.com/leanprover-community/mathlib/pull/2518))
This also removes the dependency of `algebra.char_p` on `data.padics.padic_norm`, which was only there to make `nat.prime` a class.
I also used this opportunity to rename all alphas and betas to `K` and `L` in the perfect closure file.

### [2020-04-25 08:51:08](https://github.com/leanprover-community/mathlib/commit/f192f2f)
chore(*): move quadratic_reciprocity to number_theory/ ([#2520](https://github.com/leanprover-community/mathlib/pull/2520))
I've never really understood why we put all these cool theorems under the data/ directory, so I suggest moving them out of there, and into the place where thy "belong".

### [2020-04-25 05:42:30](https://github.com/leanprover-community/mathlib/commit/3c8584d)
feat(order/filter/bases): add `exists_iff` and `forall_iff` ([#2507](https://github.com/leanprover-community/mathlib/pull/2507))

### [2020-04-25 05:42:28](https://github.com/leanprover-community/mathlib/commit/199f6fe)
refactor(tactic/suggest): call library_search and suggest with additional lemmas, better lemma caching ([#2429](https://github.com/leanprover-community/mathlib/pull/2429))
This PR is mainly a refactoring of suggest. The changes include:
* Removed `(discharger : tactic unit := done)` from `library_search`, `suggest`, `suggest_scripts` `suggest_core`, `suggest_core'`, `apply_declaration` and `apply_and_solve` and replaced by `(opt : by_elim_opt := { })` from `solve_by_elim`.
* Replaced all occurences of `discharger` by `opt`, `opt.discharger`, or `..opt`.
* inserted a do block into the interactive `library_search` function.
* Added `asms ← mk_assumption_set no_dflt hs attr_names`, to the interactive `suggest` and `library_search` functions. This is so `library_search` and `suggest` don't rebuild the assumption set each time a lemma is applied.
* Added several inputs for the interactive `library_search` and `suggest` function. These parameters were lifted from the interactive `solve_by_elim` function and allow the user to control how `solve_by_elim` is utilized by `library_search` and `suggest`.
* Removed the `message` function (redundant code.)
* Removed several unnecessary `g ← instantiate_mvars g`, lines.

### [2020-04-25 04:11:06](https://github.com/leanprover-community/mathlib/commit/06f8c55)
chore(scripts): update nolints.txt ([#2517](https://github.com/leanprover-community/mathlib/pull/2517))
I am happy to remove some nolints for you!

### [2020-04-25 02:22:56](https://github.com/leanprover-community/mathlib/commit/22d89c4)
chore(scripts): update nolints.txt ([#2515](https://github.com/leanprover-community/mathlib/pull/2515))
I am happy to remove some nolints for you!

### [2020-04-24 23:37:04](https://github.com/leanprover-community/mathlib/commit/e918f72)
refactor(zmod): merge `zmodp` into `zmod`, use `[fact p.prime]` for tc search ([#2511](https://github.com/leanprover-community/mathlib/pull/2511))
This PR introduces the class `fact P := P` for `P : Prop`, which is a way to inject elementary propositions into the type class system. This desing is inspired by @cipher1024 's https://gist.github.com/cipher1024/9bd785a75384a4870b331714ec86ad6f#file-zmod_redesign-lean.
We use this to endow `zmod p` with a `field` instance under the assumption `[fact p.prime]`.
As a consequence, the type `zmodp` is no longer needed, which removes a lot of duplicate code.
Besides that, we redefine `zmod n`, so that `n` is a natural number instead of a *positive* natural number, and `zmod 0` is now definitionally the integers.
To preserve computational properties, `zmod n` is not defined as quotient type, but rather as `int` and `fin n`, depending on whether `n` is `0` or `(k+1)`.
The rest of this PR is adapting the library to the new definitions (most notably quadratic reciprocity and Lagrange's four squares theorem).
Future work: Refactor the padics to use `[fact p.prime]` instead of making `nat.prime` a class in those files. This will address [#1601](https://github.com/leanprover-community/mathlib/pull/1601) and [#1648](https://github.com/leanprover-community/mathlib/pull/1648). Once that is done, we can clean up the mess in `char_p` (where the imports are really tangled) and finally get some movement in [#1564](https://github.com/leanprover-community/mathlib/pull/1564).

### [2020-04-24 23:37:01](https://github.com/leanprover-community/mathlib/commit/3e54e97)
chore(topology/separation): prove that `{y | y ≠ x}` is open ([#2506](https://github.com/leanprover-community/mathlib/pull/2506))

### [2020-04-24 21:12:05](https://github.com/leanprover-community/mathlib/commit/ee8451b)
feat(data/list): more lemmas on joins and sums ([#2501](https://github.com/leanprover-community/mathlib/pull/2501))
A few more lemmas on lists (especially joins) and sums. I also linted the file `lists/basic.lean` and converted some comments to section headers.
Some lemmas got renamed:
`of_fn_prod_take` -> `prod_take_of_fn`
`of_fn_sum_take` -> `sum_take_of_fn`
`of_fn_prod` ->`prod_of_fn`
`of_fn_sum` -> `sum_of_fn`
The arguments of `nth_le_repeat` were changed for better `simp` efficiency

### [2020-04-24 20:10:09](https://github.com/leanprover-community/mathlib/commit/6795c9d)
chore(scripts): update nolints.txt ([#2514](https://github.com/leanprover-community/mathlib/pull/2514))
I am happy to remove some nolints for you!

### [2020-04-24 17:09:09](https://github.com/leanprover-community/mathlib/commit/3162c1c)
feat(tactic/delta_instance): protect names and deal with functions ([#2477](https://github.com/leanprover-community/mathlib/pull/2477))
There were (at least) two issues with the `delta_instance` derive handler:
* It couldn't protect the names of the instances it generated, so they had to be ugly to avoid clashes.
* It didn't deal well with deriving instances on function types, so `@[derive monad]` usually failed.
This should fix both. The first is possible with recent(ish) additions to core.
closes [#1951](https://github.com/leanprover-community/mathlib/pull/1951)

### [2020-04-24 14:15:51](https://github.com/leanprover-community/mathlib/commit/2f6b8d7)
chore(scripts): update nolints.txt ([#2510](https://github.com/leanprover-community/mathlib/pull/2510))
I am happy to remove some nolints for you!

### [2020-04-24 14:15:48](https://github.com/leanprover-community/mathlib/commit/7a71866)
chore(topology/algebra/module): make `id` use explicit args ([#2509](https://github.com/leanprover-community/mathlib/pull/2509))

### [2020-04-24 14:15:46](https://github.com/leanprover-community/mathlib/commit/62feebc)
chore(*): add missing copyright headers ([#2505](https://github.com/leanprover-community/mathlib/pull/2505))
I think these are close to the last remaining files without copyright headers.
(We decided at some point to allow that `import`-only files don't need one.)

### [2020-04-24 14:15:44](https://github.com/leanprover-community/mathlib/commit/c8946c9)
chore(tactic/*): remove some unused args in commands ([#2498](https://github.com/leanprover-community/mathlib/pull/2498))

### [2020-04-24 11:14:03](https://github.com/leanprover-community/mathlib/commit/00d7da2)
docs(*): merge rewrite tactic tag into rewriting ([#2512](https://github.com/leanprover-community/mathlib/pull/2512))
We had two overlapping tags in the docs.

### [2020-04-24 11:14:01](https://github.com/leanprover-community/mathlib/commit/13393e3)
chore(data/list/*): various renamings to use dot notation ([#2481](https://github.com/leanprover-community/mathlib/pull/2481))
* use dot notation
* add a version of `list.perm.prod_eq` that only assumes that elements of the list pairwise commute instead of commutativity of the monoid.
## List of renamed symbols
### `data/list/basic`
* `append_sublist_append_of_sublist_right` : `sublist.append_right`;
* `reverse_sublist` : `sublist.reverse`;
* `append_sublist_append` : `sublist.append`;
* `subset_of_sublist`: `sublist.subset`;
* `sublist_antisymm` : `sublist.antisymm`;
* `filter_map_sublist_filter_map` : `sublist.filter_map`
* `map_sublist_map` : `sublist.map`
* `erasep_sublist_erasep`: `sublist.erasep`
* `erase_sublist_erase` : `sublist.erase`;
* `diff_sublist_of_sublist` : `sublist.diff_right`;
### `data/list/perm`
* `perm.skip` : `perm.cons`;
* `perm_comm` (new);
* `perm_subset` : `perm.subset`;
* `mem_of_perm` : `perm.mem_iff`;
* `perm_app_left` : `perm.append_right` (note `right` vs `left`)
* `perm_app_right` : `perm.append_left` (note `right` vs `left`)
* `perm_app` : `perm.append`;
* `perm_app_cons` : `perm.append_cons`;
* `perm_cons_app` : `perm_append_singleton`;
* `perm_app_comm` : `perm_append_comm`;
* `perm_length` : `perm.length_eq`;
* `eq_nil_of_perm_nil` : `perm.eq_nil` and `perm.nil_eq`
  with different choices of lhs/rhs;
* `eq_singleton_of_perm_inv` : `perm.eq_singleton` and `perm.singleton_eq`
  with different choices of lhs/rhs;
* `perm_singleton` and `singleton_perm`: `iff` versions
  of `perm.eq_singleton` and `perm.singleton_eq`;
* `eq_singleton_of_perm` : `singleton_perm_singleton`;
* `perm_cons_app_cons` : `perm_cons_append_cons`;
* `perm_repeat` : `repeat_perm`; new `perm_repeat` differs from it
  in the choice of lhs/rhs;
* `perm_erase` : `perm_cons_erase`;
* `perm_filter_map` : `perm.filter_map`;
* `perm_map` : `perm.map`;
* `perm_pmap` : `perm.pmap`;
* `perm_filter` : `perm.filter`;
* `subperm_of_sublist` : `sublist.subperm`;
* `subperm_of_perm` : `perm.subperm`;
* `subperm.refl` : now has `@[refl]` attribute;
* `subperm.trans` : now has `@[trans]` attribute;
* `length_le_of_subperm` : `subperm.length_le`;
* `subset_of_subperm` : `subperm.subset`;
* `exists_perm_append_of_sublist` : `sublist.exists_perm_append`;
* `perm_countp` : `perm.countp_eq`;
* `countp_le_of_subperm` : `subperm.countp_le`;
* `perm_count` : `perm.count_eq`;
* `count_le_of_subperm` : `subperm.count_le`;
* `foldl_eq_of_perm` : `perm.foldl_eq`, added a primed version
  with slightly weaker assumptions;
* `foldr_eq_of_perm` : `perm.foldr_eq`;
* `rec_heq_of_perm` : `perm.eec_heq`;
* `fold_op_eq_of_perm` : `perm.fold_op_eq`;
* `prod_eq_of_perm`: `perm.prod_eq` and `perm.prod_eq'`;
* `perm_cons_inv` : `perm.cons_inv`;
* `perm_cons` : now is a `@[simp]` lemma;
* `perm_app_right_iff` : `perm_append_right_iff`;
* `subperm_app_left` : `subperm_append_left`;
* `subperm_app_right` : `subperm_append_right`;
* `perm_ext_sublist_nodup` : `nodup.sublist_ext`;
* `erase_perm_erase` : `perm.erase`;
* `subperm_cons_erase` (new);
* `erase_subperm_erase` : `subperm.erase`;
* `perm_diff_left` : `perm.diff_right` (note `left` vs `right`);
* `perm_diff_right` : `perm.diff_left` (note `left` vs `right`);
* `perm.diff`, `subperm.diff_right`, `erase_cons_subperm_cons_erase` (new);
* `perm_bag_inter_left` : `perm.bag_inter_right` (note `left` vs `right`);
* `perm_bag_inter_right` : `perm.bag_inter_left` (note `left` vs `right`);
* `perm.bag_inter` (new);
* `perm_erase_dup_of_perm` : `perm.erase_dup`;
* `perm_union_left` : `perm.union_right` (note `left` vs `right`);
* `perm_union_right` : `perm.union_left` (note `left` vs `right`);
* `perm_union` : `perm.union`;
* `perm_inter_left` : `perm.inter_right` (note `left` vs `right`);
* `perm_inter_right` : `perm.inter_left` (note `left` vs `right`);
* `perm_inter` : `perm.inter`;
* `perm_nodup` : `perm.nodup_iff`;
* `perm_bind_left` : `perm.bind_right` (note `left` vs `right`);
* `perm_bind_right` : `perm.bind_left` (note `left` vs `right`);
* `perm_product_left` : `perm.product_right` (note `left` vs `right`);
* `perm_product_right` : `peerm.product_left` (note `left` vs `right`);
* `perm_product` : `perm.product`;
* `perm_erasep` : `perm.erasep`;
### `data/list/sigma`
* `nodupkeys.pairwise_ne` (new);
* `perm_kreplace` : `perm.kreplace`;
* `perm_kerase` : `perm.kerase`;
* `perm_kinsert` : `perm.kinsert`;
* `erase_dupkeys_cons` : now take `x : sigma β` instead
  of `{x : α}` and `{y : β x}`;
* `perm_kunion_left` : `perm.kunion_right` (note `left` vs `right`);
* `perm_kunion_right` : `perm.kunion_left` (note `left` vs `right`);
* `perm_kunion` : `perm.kunion`;
*

### [2020-04-24 11:13:59](https://github.com/leanprover-community/mathlib/commit/3ae22de)
feat(linear_algebra): quadratic forms ([#2480](https://github.com/leanprover-community/mathlib/pull/2480))
Define quadratic forms over a module, maps from quadratic forms to bilinear forms and matrices, positive definite quadratic forms and the discriminant of quadratic forms.
Along the way, I added some definitions to `data/matrix/basic.lean` and `linear_algebra/bilinear_form.lean` and did some cleaning up.

### [2020-04-24 06:43:01](https://github.com/leanprover-community/mathlib/commit/e7bd312)
chore(tactic/pi_instance): add a docstring, remove a little bit of redundancy ([#2500](https://github.com/leanprover-community/mathlib/pull/2500))

### [2020-04-24 04:03:04](https://github.com/leanprover-community/mathlib/commit/b7af283)
feat(algebra): define `invertible` typeclass ([#2504](https://github.com/leanprover-community/mathlib/pull/2504))
In the discussion for [#2480](https://github.com/leanprover-community/mathlib/pull/2480), we decided that the definitions would be cleaner if the elaborator could supply us with a suitable value of `1/2`. With these changes, we can now add an `[invertible 2]` argument to write `⅟ 2`.
Related to Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232480.20bilinear.20forms

### [2020-04-24 01:03:57](https://github.com/leanprover-community/mathlib/commit/02d7308)
feat(cmd/simp): let `#simp` use declared `variables` ([#2478](https://github.com/leanprover-community/mathlib/pull/2478))
Let `#simp` see declared `variables`.
~~Sits atop the minor `tactic.core` rearrangement in [#2465](https://github.com/leanprover-community/mathlib/pull/2465).~~
@semorrison It turns out that `push_local_scope` and `pop_local_scope` weren't required; the parser is smarter than we thought, and if you declared some `variables` and then tried to `#simp` them, lean would half-know what you are talking about.
Indeed, the parsed `pexpr` from the command would include this information, but `to_expr` would report `no such 'blah'` when called afterward. To fix this you have to add the local variables you want `simp` to be able to see as local hypotheses in the same `tactic_state` in which you invoke `expr.simp`---so no wrapping your call to `expr.simp` directly in `lean.parser.of_tactic` (since this cooks up a fresh `tactic_state` for you).
Closes [#2475](https://github.com/leanprover-community/mathlib/pull/2475).
<br>
<br>

### [2020-04-23 23:53:50](https://github.com/leanprover-community/mathlib/commit/0196748)
chore(scripts): update nolints.txt ([#2503](https://github.com/leanprover-community/mathlib/pull/2503))
I am happy to remove some nolints for you!

### [2020-04-23 21:05:16](https://github.com/leanprover-community/mathlib/commit/fdbf22d)
doc(tactic/*): doc entries for some missing tactics ([#2489](https://github.com/leanprover-community/mathlib/pull/2489))
This covers most of the remaining list in the old issue [#450](https://github.com/leanprover-community/mathlib/pull/450). I've already checked off my additions.

### [2020-04-23 18:01:07](https://github.com/leanprover-community/mathlib/commit/fc7ac67)
feat(data/string): add docstrings and improve semantics ([#2497](https://github.com/leanprover-community/mathlib/pull/2497))
Could have gone in [#2493](https://github.com/leanprover-community/mathlib/pull/2493), but I didn't want to hold up [#2478](https://github.com/leanprover-community/mathlib/pull/2478). Besides, what's a tiny pull request between friends.
This "writing docstrings" thing really lets helps you discover tiny little tweaks here and here.
<br>
<br>
<br>

### [2020-04-23 15:14:10](https://github.com/leanprover-community/mathlib/commit/9ccfa92)
feat(data/string): add phrasings common to conventional languages ([#2493](https://github.com/leanprover-community/mathlib/pull/2493))
Just add a pair of string comparison functions with semantics which are common to conventional programming languages.
<br>
<br>
<br>

### [2020-04-23 12:15:02](https://github.com/leanprover-community/mathlib/commit/64e464f)
chore(*): remove unnecessary transitive imports ([#2496](https://github.com/leanprover-community/mathlib/pull/2496))
This removes all imports which have already been imported by other imports.
Overall, this is slightly over a third of the total import lines. This should have no effect whatsoever on compilation, but should make `leanproject import-graph` somewhat... leaner!

### [2020-04-23 09:12:20](https://github.com/leanprover-community/mathlib/commit/8a7b94f)
chore(tactic/suggest): add a docstring ([#2499](https://github.com/leanprover-community/mathlib/pull/2499))

### [2020-04-23 02:52:58](https://github.com/leanprover-community/mathlib/commit/7c10fd2)
feat(category_theory/epi_mono): opposite epi mono properties ([#2479](https://github.com/leanprover-community/mathlib/pull/2479))
Relating epis and monos to the opposite category.

### [2020-04-23 01:10:17](https://github.com/leanprover-community/mathlib/commit/4d94de4)
feat(category_theory): wide pullbacks and limits in the over category ([#2461](https://github.com/leanprover-community/mathlib/pull/2461))
This PR introduces [wide pullbacks](https://ncatlab.org/nlab/show/wide+pullback). 
Ordinary pullbacks are then defined as a special case of wide pullbacks, which simplifies some of the definitions and proofs there. 
Finally we show that the existence of wide pullbacks in `C` gives products in the slice `C/B`, and in fact gives all limits.

### [2020-04-22 23:11:50](https://github.com/leanprover-community/mathlib/commit/4dadd26)
chore(scripts): update nolints.txt ([#2495](https://github.com/leanprover-community/mathlib/pull/2495))
I am happy to remove some nolints for you!

### [2020-04-22 21:20:58](https://github.com/leanprover-community/mathlib/commit/bcbdeba)
chore(tactic/apply_fun): add doc string and remove duplication ([#2485](https://github.com/leanprover-community/mathlib/pull/2485))
I was just adding a docstring to `tactic.apply_fun`, and then saw some duplication and removed it. An example of a use of [#2484](https://github.com/leanprover-community/mathlib/pull/2484).
<br>
<br>
<br>

### [2020-04-22 18:31:17](https://github.com/leanprover-community/mathlib/commit/691a230)
chore(scripts): update nolints.txt ([#2494](https://github.com/leanprover-community/mathlib/pull/2494))
I am happy to remove some nolints for you!

### [2020-04-22 18:31:15](https://github.com/leanprover-community/mathlib/commit/2fb6022)
feat(mk_iff_of_inductive_prop): add, use, and document command ([#2490](https://github.com/leanprover-community/mathlib/pull/2490))
This existed as an (undocumented) tactic that was being called with `run_cmd`. It deserves to be a documented user command.

### [2020-04-22 16:17:53](https://github.com/leanprover-community/mathlib/commit/591a0a0)
chore(*): only import one file per line ([#2470](https://github.com/leanprover-community/mathlib/pull/2470))
This perhaps-unnecessarily-obsessive PR puts every import statement on its own line.
Why?
1. it's nice to be able to grep for `import X`
2. ~~if we enforced this, it would be easier deal with commands after imports, etc.~~ (irrelevant in 3.9)
3. it means I can remove all unnecessary transitive imports with a script
4. it's just tidier. :-)

### [2020-04-22 15:09:08](https://github.com/leanprover-community/mathlib/commit/8865b00)
chore(scripts): update nolints.txt ([#2491](https://github.com/leanprover-community/mathlib/pull/2491))
I am happy to remove some nolints for you!

### [2020-04-22 12:17:00](https://github.com/leanprover-community/mathlib/commit/d40662f)
chore(tactic/auto_cases): add docstring and remove duplication ([#2488](https://github.com/leanprover-community/mathlib/pull/2488))
I was just adding a docstring, and I saw some duplication so I removed it too.
<br>
<br>
<br>

### [2020-04-22 12:16:58](https://github.com/leanprover-community/mathlib/commit/f760ad5)
chore(meta/expr): add a docstring ([#2487](https://github.com/leanprover-community/mathlib/pull/2487))
Add a docstring.
<br>
<br>
<br>

### [2020-04-22 12:16:56](https://github.com/leanprover-community/mathlib/commit/62a613f)
feat(data/option): add `option.mmap` and `option.maybe` ([#2484](https://github.com/leanprover-community/mathlib/pull/2484))
Please let me know if something like this exists already! Over the last few days I've wanted it multiple times, and it is used in [#2485](https://github.com/leanprover-community/mathlib/pull/2485).
<br>
<br>
<br>

### [2020-04-22 12:16:54](https://github.com/leanprover-community/mathlib/commit/e4abced)
chore(data/polynomial): rename type vars ([#2483](https://github.com/leanprover-community/mathlib/pull/2483))
Rename `α` to `R` etc; use `ι` for index types
No other changes

### [2020-04-22 12:16:52](https://github.com/leanprover-community/mathlib/commit/5965370)
feat(data/monoid_algebra): algebra structure, lift of morphisms ([#2366](https://github.com/leanprover-community/mathlib/pull/2366))
Prove that for a monoid homomorphism `f : G →* R` from a monoid `G` to a `k`-algebra `R` there exists a unique algebra morphism `g : k[G] →ₐ[k] R` such that `∀ x : G, g (single x 1) = f x`.
This is expressed as `def lift : (G →* R) ≃ (monoid_algebra k G →ₐ[k] R)`.
I want to use this to define `aeval` and `eval₂` for polynomials. This way we'll have many properties for free.

### [2020-04-22 09:12:07](https://github.com/leanprover-community/mathlib/commit/142f001)
chore(cmd/where): remove unused argument ([#2486](https://github.com/leanprover-community/mathlib/pull/2486))
Just remove an unused argument from the `#where` declaration, satisfying the linter.
<br>
<br>
<br>

### [2020-04-22 03:48:09](https://github.com/leanprover-community/mathlib/commit/5e2025f)
feat(group_theory/bundled_subgroup): bundled subgroup ([#2140](https://github.com/leanprover-community/mathlib/pull/2140))
Add bundled subgroups. While `is_subgroup` is a class taking `s : set G` as an argument, `subgroup G` is a structure with a field `carrier : set G` and a coercion to `set G`.

### [2020-04-21 20:46:05](https://github.com/leanprover-community/mathlib/commit/585d77a)
chore(scripts): update nolints.txt ([#2482](https://github.com/leanprover-community/mathlib/pull/2482))
I am happy to remove some nolints for you!

### [2020-04-21 17:16:35](https://github.com/leanprover-community/mathlib/commit/ffa97d0)
fix(tactic/where): remove hackery from `#where`, using Lean 3c APIs ([#2465](https://github.com/leanprover-community/mathlib/pull/2465))
We remove almost all of the hackery from `#where`, using the Lean 3c APIs exposed by @cipher1024. In doing so we add pair of library functions which make this a tad more convenient.
The last "hack" which remains is by far the most mild; we expose `lean.parser.get_current_namespace`, which creates a dummy definition in the environment in order to obtain the current namespace. Of course this should be replaced with an exposed C++ function when the time comes (crossref with the leanprover-community/lean issue here: https://github.com/leanprover-community/lean/issues/196).

### [2020-04-21 10:37:45](https://github.com/leanprover-community/mathlib/commit/533a552)
feat(tactic/hint): if hint can solve the goal, say so ([#2474](https://github.com/leanprover-community/mathlib/pull/2474))
It used to be that `hint` would print:
```
the following tactics make progress:
----
tac1
tac2
tac3
```
with the tactics listed in order of number of resulting goals. In particular, if `tac1` and `tac2` actually solve the goal, while `tac3` only makes progress, this isn't explained.
With this PR, if any of those tactics actually close the goal, we only print those tactics, with text:
```
the following tactics solve the goal:
----
tac1
tac2
```

### [2020-04-21 10:37:42](https://github.com/leanprover-community/mathlib/commit/15d35b1)
feat(tactic/#simp): a user_command for #simp ([#2446](https://github.com/leanprover-community/mathlib/pull/2446))
```lean
#simp 5 - 5
```
prints `0`.
If anyone knows how to get access to local `variables` while parsing an expression, that would be awesome. Then we could write 
```lean
variable (x : ℝ)
#simp [exp_ne_zero] : deriv (λ x, (sin x) / (exp x)) x
```
as well as
```lean
#simp [exp_ne_zero] : λ x, deriv (λ x, (sin x) / (exp x)) x
```

### [2020-04-21 07:42:40](https://github.com/leanprover-community/mathlib/commit/df84064)
fix(tactic/clear): don't use rb_map unnecessarily ([#2325](https://github.com/leanprover-community/mathlib/pull/2325))
The `clear_dependent` tactic seems to unnecessarily convert `list` back and forth to an `rb_map`, for no purpose, and this makes the internal tactic unnecessarily difficult to call.

### [2020-04-21 05:12:16](https://github.com/leanprover-community/mathlib/commit/3edb6a4)
fix(category_theory/concrete): access the carrier type by the coercion ([#2473](https://github.com/leanprover-community/mathlib/pull/2473))
This should marginally reduce the pain of using concrete categories, as the underlying types of a bundled object should more uniformly described via a coercion, rather than the `.α` projection.
(There's still some separate pain involving `bundled.map`, but it has an orthogonal fix which I'm working on in another branch.)

### [2020-04-21 01:17:00](https://github.com/leanprover-community/mathlib/commit/7a13a11)
chore(category_theory): delete two empty files ([#2472](https://github.com/leanprover-community/mathlib/pull/2472))

### [2020-04-20 18:19:41](https://github.com/leanprover-community/mathlib/commit/5d0a724)
chore(docs/naming): update ([#2468](https://github.com/leanprover-community/mathlib/pull/2468))
This file has been bit-rotting.

### [2020-04-20 15:36:57](https://github.com/leanprover-community/mathlib/commit/7626763)
fix(algebra/category/*/colimits): cleaning up ([#2469](https://github.com/leanprover-community/mathlib/pull/2469))
With the passage of time, it seems some difficulties have dissolved away, and steps in the semi-automated construction of colimits in algebraic categories which previously required `rw` or even `erw`, can now be handled by `simp`. Yay!

### [2020-04-20 15:36:55](https://github.com/leanprover-community/mathlib/commit/8adfafd)
feat(data/nat,data/int): add some modular arithmetic lemmas ([#2460](https://github.com/leanprover-community/mathlib/pull/2460))
These lemmas (a) were found useful in formalising solutions to some
olympiad problems, see
<https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations>;
(b) seem more generally relevant than to just those particular
problems; (c) do not show up through library_search as being already
present.

### [2020-04-20 15:36:53](https://github.com/leanprover-community/mathlib/commit/d1ba87a)
feat(category_theory/faithful): faithful.of_iso ([#2453](https://github.com/leanprover-community/mathlib/pull/2453))
A minor useful lemma, about to be abandoned on another branch.

### [2020-04-20 15:36:51](https://github.com/leanprover-community/mathlib/commit/51e03aa)
feat(data/monoid_algebra): the distrib_mul_action ([#2417](https://github.com/leanprover-community/mathlib/pull/2417))

### [2020-04-20 14:24:18](https://github.com/leanprover-community/mathlib/commit/036b038)
chore(category_theory/opposites): typo fix ([#2466](https://github.com/leanprover-community/mathlib/pull/2466))
As mentioned in [#2464](https://github.com/leanprover-community/mathlib/pull/2464).

### [2020-04-20 13:15:51](https://github.com/leanprover-community/mathlib/commit/59a767e)
chore(scripts): update nolints.txt ([#2467](https://github.com/leanprover-community/mathlib/pull/2467))
I am happy to remove some nolints for you!

### [2020-04-20 11:18:14](https://github.com/leanprover-community/mathlib/commit/4474382)
feat(category_theory/opposites): some opposite category properties ([#2464](https://github.com/leanprover-community/mathlib/pull/2464))
Add some more basic properties relating to the opposite category.
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
For reviewers: [code review check list](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/code-review.md)
If you're confused by comments on your PR like `bors r+` or `bors d+`, please see our [notes on bors](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/bors.md) for information on our merging workflow.

### [2020-04-20 08:26:52](https://github.com/leanprover-community/mathlib/commit/58088cc)
fix(tactic/delta_instance): handle universe metavariables ([#2463](https://github.com/leanprover-community/mathlib/pull/2463))

### [2020-04-20 07:17:35](https://github.com/leanprover-community/mathlib/commit/9b25578)
fix(category_theory/limits): avoid a rewrite in a definition ([#2458](https://github.com/leanprover-community/mathlib/pull/2458))
The proof that every equalizer of `f` and `g` is an isomorphism if `f = g` had an ugly rewrite in a definition (introduced by yours truly). This PR reformulates the proof in a cleaner way by working with two morphisms `f` and `g` and a proof of `f = g` right from the start, which is easy to specialze to the case `(f, f)`, instead of trying to reduce the `(f, g)` case to the `(f, f)` case by rewriting.
This also lets us get rid of `fork.eq_of_ι_ι`, unless someone wants to keep it, but personally I don't think that using it is ever a good idea.

### [2020-04-20 01:36:42](https://github.com/leanprover-community/mathlib/commit/c0afa80)
chore(tactic/simp_result): forgot to import in tactic.basic ([#2462](https://github.com/leanprover-community/mathlib/pull/2462))
When I write a new tactic, I tend not to import it into `tactic.basic` or `tactic.interactive` while testing it and PR'ing it, to save having to recompile the whole library every time I tweak the tactic.
But then, inevitably, I forget to add the import before the review process is finished.
This imports `simp_result`, from [#2356](https://github.com/leanprover-community/mathlib/pull/2356), into `tactic.basic`.

### [2020-04-19 15:18:08](https://github.com/leanprover-community/mathlib/commit/a8edb5e)
fix(category_theory/limits): make image.map_comp a simp lemma ([#2456](https://github.com/leanprover-community/mathlib/pull/2456))
This was not possible in Lean 3.8. Many thanks to @gebner for tracking down and fixing leanprover-community/lean[#181](https://github.com/leanprover-community/mathlib/pull/181) in Lean 3.9.

### [2020-04-19 15:18:06](https://github.com/leanprover-community/mathlib/commit/e6aa533)
fix(category_theory/limits): remove an unnecessary axiom in has_image_map ([#2455](https://github.com/leanprover-community/mathlib/pull/2455))
I somehow missed the fact that `has_image_map.factor_map` is actually a consequence of `has_image_map.map_ι` together with the fact that `image.ι` is always a monomorphism.

### [2020-04-19 14:00:03](https://github.com/leanprover-community/mathlib/commit/aa55f8b)
feat(category_theory/eq_to_iso): missing simp lemma ([#2454](https://github.com/leanprover-community/mathlib/pull/2454))
A missing simp lemma.

### [2020-04-19 14:00:01](https://github.com/leanprover-community/mathlib/commit/9801c1c)
feat(continued_fractions) add stabilisation under termination lemmas ([#2451](https://github.com/leanprover-community/mathlib/pull/2451))
- continued fractions: add lemmas for stabilisation of computations under termination and add them to default exports
- seq: make argument in seq.terminated_stable explicit

### [2020-04-19 13:02:57](https://github.com/leanprover-community/mathlib/commit/6054f7c)
chore(number_theory/sum_four_squares): slightly shorten proof ([#2457](https://github.com/leanprover-community/mathlib/pull/2457))
This proof was unnecessarily long due to a ring bug which has now been fixed.

### [2020-04-19 19:50:13+10:00](https://github.com/leanprover-community/mathlib/commit/d344310)
chore(category_theory/monoidal): some arguments that need to be made explicit in 3.8

### [2020-04-19 07:58:32](https://github.com/leanprover-community/mathlib/commit/11d89a2)
chore(algebra/module): replace typeclass arguments with inferred arguments ([#2444](https://github.com/leanprover-community/mathlib/pull/2444))
This doesn't change the explicit type signature of any functions, but makes some inferable typeclass arguments implicit.
Beyond the potential performance improvement, my motivation for doing this was that in `monoid_algebra` we currently have two possible `module k (monoid_algebra k G)` instances: one directly from `monoid_algebra.module`, and another one via `restrict_scalars`. These are equal, but not definitionally. In another experimental branch, I couldn't even express the isomorphism between these module structures, because type inference was filling in the `monoid_algebra.module` instance in composition of linear maps, and then failing because one of the linear maps was actually using the other module structure...
This change fixes this.

### [2020-04-19 01:55:09](https://github.com/leanprover-community/mathlib/commit/0ceac44)
feat(data/nat/prime) factors of a prime number is the list [p] ([#2452](https://github.com/leanprover-community/mathlib/pull/2452))
The factors of a prime number are [p].

### [2020-04-18 23:47:08](https://github.com/leanprover-community/mathlib/commit/99245b3)
chore(*): switch to lean 3.9.0 ([#2449](https://github.com/leanprover-community/mathlib/pull/2449))
It's been too long since the last Lean release.

### [2020-04-18 23:47:06](https://github.com/leanprover-community/mathlib/commit/d76a882)
feat(category_theory/limits/over): over category has connected limits ([#2438](https://github.com/leanprover-community/mathlib/pull/2438))
Show that the forgetful functor from the over category creates connected limits.
The key consequence of this is that the over category has equalizers, which we will use to show that it has all (finite) limits if the base category does.
I've also moved the connected category examples into `category_theory/connected.lean`.
Also I removed the proof of
`instance {B : C} [has_pullbacks.{v} C] : has_pullbacks.{v} (over B)`
which I wrote and semorrison massively improved, as the new instances generalise it. 
I also added a `reassoc` for `is_limit.fac`, which simplified one of the proofs I had.

### [2020-04-18 21:59:03](https://github.com/leanprover-community/mathlib/commit/8ec447d)
fix(*): remove `@[nolint simp_nf]` ([#2450](https://github.com/leanprover-community/mathlib/pull/2450))
This removes a couple more nolints:
 - `coe_units_equiv_ne_zero` doesn't cause any problems anymore
 - `coe_mk` is redundant
 - `mk_eq_div` was not in simp-normal form (previously the linter timed out instead of reporting it as an error)
 - `factor_set.coe_add` is redundant

### [2020-04-18 17:48:38](https://github.com/leanprover-community/mathlib/commit/5107c2b)
fix(docs/extra/calc.md): remove extra space ([#2448](https://github.com/leanprover-community/mathlib/pull/2448))
This was breaking the rendered doc at https://leanprover-community.github.io/mathlib_docs/calc.html#using-more-than-one-operator

### [2020-04-18 17:48:36](https://github.com/leanprover-community/mathlib/commit/16552e6)
fix(group_theory/submonoid): looping simp lemma ([#2447](https://github.com/leanprover-community/mathlib/pull/2447))
Removes a `@[nolint simp_nf]`.  I have no idea why I didn't notice this earlier, but `coe_coe` loops due to `coe_sort_coe_base` since `submonoid` doesn't have it's own `has_coe_to_sort` instance.

### [2020-04-18 15:15:21](https://github.com/leanprover-community/mathlib/commit/4e87223)
feat(tactic/transport): transport structures across equivalences ([#2251](https://github.com/leanprover-community/mathlib/pull/2251))
~~Blocked by [#2246](https://github.com/leanprover-community/mathlib/pull/2246).~~
~~Blocked on [#2319](https://github.com/leanprover-community/mathlib/pull/2319) and [#2334](https://github.com/leanprover-community/mathlib/pull/2334), which both fix lower tactic layers used by `transport`.~~
From the doc-string:
---
Given a goal `⊢ S β` for some parametrized structure type `S`,
`transport` will look for a hypothesis `s : S α` and an equivalence `e : α ≃ β`,
and attempt to close the goal by transporting `s` across the equivalence `e`.
```lean
example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport.
```
You can specify the object to transport using `transport s`,
and the equivalence to transport across using `transport s using e`.
---
You can just as easily transport a [`semilattice_sup_top`](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/lattice.20with.20antiautomorphism) or a `lie_ring`.
In the `test/transport.lean` file we transport `semiring` from `nat` to `mynat`, and verify that it's possible to do simple things with the transported structure.

### [2020-04-18 12:23:55](https://github.com/leanprover-community/mathlib/commit/ffb99a3)
chore(algebra/group/type_tags): add `additive.to_mul` etc ([#2363](https://github.com/leanprover-community/mathlib/pull/2363))
Don't make `additive` and `multiplicative` irreducible (yet?) because
it breaks compilation here and there.
Also prove that homomorphisms from `ℕ`, `ℤ` and their `multiplicative`
versions are defined by the image of `1`.

### [2020-04-18 10:03:42](https://github.com/leanprover-community/mathlib/commit/8b21231)
chore(data/mv_polynomial): adding a comment about a T50000 regression ([#2442](https://github.com/leanprover-community/mathlib/pull/2442))

### [2020-04-18 07:33:17](https://github.com/leanprover-community/mathlib/commit/a530a81)
refactor(data/nat/fib): simplify proof of fib_succ_succ ([#2443](https://github.com/leanprover-community/mathlib/pull/2443))
By tweaking some of the lemmas, I managed to shorten `fib_succ_succ` from 7 complicated lines to a single call to `simp`.
An alternative expression would be:
```lean
unfold fib,
repeat { rw fib_aux_stream_succ },
unfold fib_aux_step,
```
I can change to that if you think the `simp` is too pithy.

### [2020-04-18 04:12:58](https://github.com/leanprover-community/mathlib/commit/1ef989f)
docs(install/*): put extra emphasis ([#2439](https://github.com/leanprover-community/mathlib/pull/2439))
Put extra emphasis on creating and working with projects
If people like this change I'll also make it on the other pages.

### [2020-04-18 00:48:02](https://github.com/leanprover-community/mathlib/commit/6b09575)
feat(tactic/lint): lint for missing has_coe_to_fun instances ([#2437](https://github.com/leanprover-community/mathlib/pull/2437))
Enforces the library note "function coercion":
https://github.com/leanprover-community/mathlib/blob/715be9f7466f30f1d4cbff4e870530af43767fba/src/logic/basic.lean#L69-L94
See [#2434](https://github.com/leanprover-community/mathlib/pull/2434) for a recent PR where this issue popped up.

### [2020-04-17 21:00:09](https://github.com/leanprover-community/mathlib/commit/24d464c)
fix(github/workflows): ignore new bors branch ([#2441](https://github.com/leanprover-community/mathlib/pull/2441))
Two hours ago, bors renamed the temporary branches. https://github.com/bors-ng/bors-ng/pull/933  :roll_eyes:

### [2020-04-17 19:48:56](https://github.com/leanprover-community/mathlib/commit/da29275)
chore(scripts): update nolints.txt ([#2440](https://github.com/leanprover-community/mathlib/pull/2440))
I am happy to remove some nolints for you!

### [2020-04-17 16:30:37](https://github.com/leanprover-community/mathlib/commit/64f6903)
chore(*): migrate `nat/int/rat.eq_cast` to bundled homs ([#2427](https://github.com/leanprover-community/mathlib/pull/2427))
Now it is `ring_hom.eq_*_cast`, `ring_hom.map_*_cast`, `add_monoid_hom.eq_int/nat_cast`.
Also turn `complex.of_real` into a `ring_hom`.

### [2020-04-17 13:44:40](https://github.com/leanprover-community/mathlib/commit/855e70b)
feat(data/nat): Results about nat.choose ([#2421](https://github.com/leanprover-community/mathlib/pull/2421))
A convenience lemma for symmetry of choose and inequalities about choose.
More results from my combinatorics project.

### [2020-04-17 09:39:01](https://github.com/leanprover-community/mathlib/commit/0bc15f8)
feat(analysis/analytic/composition): the composition of analytic functions is analytic ([#2399](https://github.com/leanprover-community/mathlib/pull/2399))
The composition of analytic functions is analytic. 
The argument is the following. Assume `g z = ∑ qₙ (z, ..., z)` and `f y = ∑ pₖ (y, ..., y)`. Then
```
g (f y) = ∑ qₙ (∑ pₖ (y, ..., y), ..., ∑ pₖ (y, ..., y))
= ∑ qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y)).
```
For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.
The main difficulty is to make sense of this (especially the ellipsis) in a way that Lean understands. For this, this PR uses a structure containing a decomposition of `n` as a sum `i_1 + ... i_k` (called `composition`), and a whole interface around it developed in [#2398](https://github.com/leanprover-community/mathlib/pull/2398). Once it is available, the main proof is not too hard.
This supersedes [#2328](https://github.com/leanprover-community/mathlib/pull/2328), after a new start implementing compositions using sequences.

### [2020-04-17 06:57:05](https://github.com/leanprover-community/mathlib/commit/715be9f)
chore(scripts): update nolints.txt ([#2436](https://github.com/leanprover-community/mathlib/pull/2436))
I am happy to remove some nolints for you!

### [2020-04-17 05:53:51](https://github.com/leanprover-community/mathlib/commit/0567b7f)
feat(category_theory/limits): strong epimorphisms and strong epi-mono factorizations ([#2433](https://github.com/leanprover-community/mathlib/pull/2433))
This PR contains the changes I mentioned in [#2374](https://github.com/leanprover-community/mathlib/pull/2374). It contains:
* the definition of a lift of a commutative square
* the definition of a strong epimorphism
* a proof that every regular epimorphism is strong
* the definition of a strong epi-mono factorization
* the class `has_strong_epi_images`
* the construction `has_strong_epi_images` -> `has_image_maps`
* a small number of changes which should have been part of [#2423](https://github.com/leanprover-community/mathlib/pull/2423)

### [2020-04-17 04:14:01](https://github.com/leanprover-community/mathlib/commit/f347147)
feat(category_theory):  creation of limits and reflection of isomorphisms ([#2426](https://github.com/leanprover-community/mathlib/pull/2426))
Define creation of limits and reflection of isomorphisms.
Part 2 of a sequence of PRs aiming to resolve my TODO [here](https://github.com/leanprover-community/mathlib/blob/cf89963e14cf535783cefba471247ae4470fa8c3/src/category_theory/limits/over.lean#L143) - that the forgetful functor from the over category creates connected limits.
Remaining:
- [x] Add an instance or def which gives that if `F` creates limits and `K ⋙ F` `has_limit` then `has_limit K` as well.
- [x] Move the forget creates limits proof to limits/over, and remove the existing proof since this one is strictly stronger - make sure to keep the statement there though using the previous point.
- [x] Add more docstrings
Probably relevant to @semorrison and @TwoFX.

### [2020-04-17 02:42:19](https://github.com/leanprover-community/mathlib/commit/0d3e546)
chore(scripts): update nolints.txt ([#2435](https://github.com/leanprover-community/mathlib/pull/2435))
I am happy to remove some nolints for you!

### [2020-04-17 01:11:58](https://github.com/leanprover-community/mathlib/commit/d2db3e8)
chore(algebra/lie_algebra): add function coercion for morphisms ([#2434](https://github.com/leanprover-community/mathlib/pull/2434))
In fact three different changes are being made here:
 1. Adding direct function coercion for `lie_algebra.morphism`, allowing us to tidy up `map_lie` and increase simp scope
 2. Providing a zero element for `lie_subalgebra`, thus allowing removal of a `has_inhabited_instance` exception in nolints.txt
 3. Providing a zero element for `lie_submodule`, thus allowing removal of a `has_inhabited_instance` exception in nolints.txt

### [2020-04-16 14:03:47](https://github.com/leanprover-community/mathlib/commit/c3d943e)
feat(computability): strong reducibility and degrees ([#1203](https://github.com/leanprover-community/mathlib/pull/1203))

### [2020-04-16 12:26:28](https://github.com/leanprover-community/mathlib/commit/a113d6e)
chore(scripts): update nolints.txt ([#2432](https://github.com/leanprover-community/mathlib/pull/2432))
I am happy to remove some nolints for you!

### [2020-04-16 11:10:10](https://github.com/leanprover-community/mathlib/commit/846cbab)
feat(analysis/calculus): let simp compute derivatives ([#2422](https://github.com/leanprover-community/mathlib/pull/2422))
After this PR:
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```
Excerpts from the docstrings:
The simplifier is set up to prove automatically that some functions are differentiable, or differentiable at a point (but not differentiable on a set or within a set at a point, as checking automatically that the good domains are mapped one to the other when using composition is not something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general complicated multidimensional linear maps), but it will compute one-dimensional derivatives.
To make sure that the simplifier can prove automatically that functions are differentiable, we tag many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable functions is differentiable, as well as their product, their cartesian product, and so on. A notable exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are differentiable, then their composition also is: `simp` would always be able to match this lemma, by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`), we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding some boilerplate lemmas, but these can also be useful in their own right. 
Tests for this ability of the simplifier (with more examples) are provided in `tests/differentiable.lean`.

### [2020-04-16 11:10:08](https://github.com/leanprover-community/mathlib/commit/ec80061)
refactor(analysis/asymptotics): make is_o irreducible ([#2416](https://github.com/leanprover-community/mathlib/pull/2416))
`is_o` is currently not irreducible. Since it is a complicated type, Lean can have trouble checking if two types with `is_o` are defeq or not, leading to timeouts as described in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/undergraduate.20calculus/near/193776607
This PR makes `is_o` irreducible.

### [2020-04-16 08:33:27](https://github.com/leanprover-community/mathlib/commit/5fd4afc)
refactor(tactic/norm_cast): simplified attributes and numeral support ([#2407](https://github.com/leanprover-community/mathlib/pull/2407))
This is @pnmadelaine's work, I'm just updating it to work with current mathlib.
New and improved version of `norm_cast` as described in the paper "normalizing casts and coercions": https://arxiv.org/abs/2001.10594
The main new user-facing feature are the simplified attributes.  There is now only the `@[norm_cast]` attribute which subsumes the previous `norm_cast`, `elim_cast`, `squash_cast`, and `move_cast` attributes.
There is a new `set_option trace.norm_cast true` option to enable debugging output.

### [2020-04-16 04:20:38](https://github.com/leanprover-community/mathlib/commit/7270af9)
chore(scripts): update nolints.txt ([#2430](https://github.com/leanprover-community/mathlib/pull/2430))
I am happy to remove some nolints for you!

### [2020-04-16 01:05:50](https://github.com/leanprover-community/mathlib/commit/5ac2b48)
feat(category_theory): connected categories ([#2413](https://github.com/leanprover-community/mathlib/pull/2413))
- Define connected categories (using the convention that they must be nonempty) by asserting every functor to a discrete category is isomorphic to a constant functor. We also give some equivalent conditions which are more useful in practice: for instance that any function which is constant for objects which have a single morphism between them is constant everywhere.
- Give the definition of connected category as specified on wikipedia, and show it's equivalent. (This is more intuitive but it seems harder to both prove and use in lean, it also seems nicer stated with `head'`. If reviewers believe this should be removed, I have no objection, but I include it for now since it is the more familiar definition).
- Give three examples of connected categories.
- Prove that `X × -` preserves connected limits.
This PR is the first of three PRs aiming to resolve my TODO [here](https://github.com/leanprover-community/mathlib/blob/cf89963e14cf535783cefba471247ae4470fa8c3/src/category_theory/limits/over.lean#L143) - that the forgetful functor from the over category creates connected limits.
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
If this PR is related to a discussion on Zulip, please include a link in the discussion.
For reviewers: [code review check list](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/code-review.md)

### [2020-04-15 22:29:29](https://github.com/leanprover-community/mathlib/commit/66cc298)
feat(data/finset): existence of a smaller set ([#2420](https://github.com/leanprover-community/mathlib/pull/2420))
Show the existence of a smaller finset contained in a given finset.
The next in my series of lemmas for my combinatorics project.

### [2020-04-15 18:44:26](https://github.com/leanprover-community/mathlib/commit/8510f07)
chore(scripts): update nolints.txt ([#2425](https://github.com/leanprover-community/mathlib/pull/2425))
I am happy to remove some nolints for you!

### [2020-04-15 17:53:24](https://github.com/leanprover-community/mathlib/commit/1e212d7)
fix(data/zmod/basic): typo ([#2424](https://github.com/leanprover-community/mathlib/pull/2424))

### [2020-04-15 16:47:40](https://github.com/leanprover-community/mathlib/commit/ce72cde)
feat(category_theory/limits): special shapes API cleanup ([#2423](https://github.com/leanprover-community/mathlib/pull/2423))
This is the 2.5th PR in a series of most likely three PRs about the cohomology functor. This PR has nothing to do with cohomology, but I'm going to need a lemma from this pull request in the final PR in the series.
In this PR, I
* perform various documentation and cleanup tasks
* add lemmas similar to the ones seen in [#2396](https://github.com/leanprover-community/mathlib/pull/2396) for equalizers, kernels and pullbacks (NB: these are not needed for biproducts since the `simp` and `ext` lemmas for products and coproducts readily fire)
* generalize `prod.hom_ext` to the situation where we have a `binary_fan X Y` and an `is_limit` for that specific fan (and similar for the other shapes)
* add "bundled" versions of lift and desc. Here is the most important example:
```lean
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : {l : W ⟶ kernel f // l ≫ kernel.ι f = k} :=
⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩
```
This definition doesn't really do anything by itself, but it makes proofs comforable and readable. For example, if you say `obtain ⟨t, ht⟩ := kernel.lift' g p hpg`, then the interesting property of `t` is right there in the tactic view, which I find helpful in keeping track of things when a proof invokes a lot of universal properties.

### [2020-04-15 13:54:37](https://github.com/leanprover-community/mathlib/commit/9b797ee)
feat(library_search): (efficiently) try calling symmetry before searching the library ([#2415](https://github.com/leanprover-community/mathlib/pull/2415))
This fixes a gap in `library_search` we've known about for a long time: it misses lemmas stated "the other way round" than what you were looking for.
This PR fixes that. I cache the `tactic_state` after calling `symmetry`, so it is only called once, regardless of how much of the library we're searching.
When `library_search` was already succeeding, it should still succeed, with the same run time.
When it was failing, it will now either succeed (because it found a lemma after calling `symmetry`), or fail (in the same time, if `symmetry` fails, or approximately twice the time, if `symmetry` succeeds). I think this is a reasonable time trade-off for better search results.

### [2020-04-15 07:41:54](https://github.com/leanprover-community/mathlib/commit/8e8037f)
chore(category_theory/limits): remove dependency on concrete_categories ([#2411](https://github.com/leanprover-community/mathlib/pull/2411))
Just move some content around, so that `category_theory/limits/cones.lean` doesn't need to depend on the development of `concrete_category`.

### [2020-04-14 12:45:29](https://github.com/leanprover-community/mathlib/commit/fd0dc27)
chore(scripts): update nolints.txt ([#2418](https://github.com/leanprover-community/mathlib/pull/2418))
I am happy to remove some nolints for you!

### [2020-04-14 11:02:03](https://github.com/leanprover-community/mathlib/commit/96a07a7)
refactor(analysis/calculus/deriv): split comp and scomp ([#2410](https://github.com/leanprover-community/mathlib/pull/2410))
The derivative of the composition of a function and a scalar function was written using `smul`, regardless of the fact that the first function was vector-valued (in which case `smul` is not avoidable)  or scalar-valued (in which case it can be replaced by `mul`). Instead, this PR introduces two sets of lemmas (named `scomp` for the first type and `comp` for the second type) to get the usual multiplication in the formula for the derivative of the composition of two scalar functions.

### [2020-04-14 11:02:02](https://github.com/leanprover-community/mathlib/commit/15fcb8a)
feat(algebra/lie_algebra): define equivalences, direct sums of Lie algebras ([#2404](https://github.com/leanprover-community/mathlib/pull/2404))
This pull request does two things:
1. Defines equivalences of Lie algebras (and proves that these do indeed form an equivalence relation)
2. Defines direct sums of Lie algebras
The intention is to knock another chip off https://github.com/leanprover-community/mathlib/issues/1093

### [2020-04-14 08:19:33](https://github.com/leanprover-community/mathlib/commit/ba154bc)
fix(library_search): find id ([#2414](https://github.com/leanprover-community/mathlib/pull/2414))
Previously `library_search` could not find theorems that did not have a head symbol (e.g. were function types with source and target both "variables all the way down"). Now it can, so it solves:
```lean
example (α : Prop) : α → α :=
by library_search -- says: `exact id`
example (p : Prop) [decidable p] : (¬¬p) → p :=
by library_search -- says: `exact not_not.mp`
example (a b : Prop) (h : a ∧ b) : a := 
by library_search -- says: `exact h.left`
example (P Q : Prop) [decidable P] [decidable Q]: (¬ Q → ¬ P) → (P → Q) :=
by library_search -- says: `exact not_imp_not.mp`
```

### [2020-04-14 07:18:15](https://github.com/leanprover-community/mathlib/commit/af27ee3)
chore(analysis): two more -T50000 challenges ([#2393](https://github.com/leanprover-community/mathlib/pull/2393))
Refactor two proofs to bring them under `-T50000`, in the hope that we can later add this requirement to CI, per [#2276](https://github.com/leanprover-community/mathlib/pull/2276).

### [2020-04-13 17:33:51](https://github.com/leanprover-community/mathlib/commit/8356b79)
feat(logic/basic): a few simp lemmas about `and` and `or` ([#2408](https://github.com/leanprover-community/mathlib/pull/2408))

### [2020-04-13 17:33:49](https://github.com/leanprover-community/mathlib/commit/fe878ea)
feat(algebra/big-operators): some big operator lemmas ([#2152](https://github.com/leanprover-community/mathlib/pull/2152))
Lemmas I found useful in my [combinatorics](https://b-mehta.github.io/combinatorics/) project
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
If this PR is related to a discussion on Zulip, please include a link in the discussion.
For reviewers: [code review check list](https://github.com/leanprover/mathlib/blob/master/docs/contribute/code-review.md)

### [2020-04-13 17:33:47](https://github.com/leanprover-community/mathlib/commit/67e363f)
feat(data/finset): finset lemmas from combinatorics ([#2149](https://github.com/leanprover-community/mathlib/pull/2149))
The beginnings of moving results from my combinatorics project
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
For reviewers: [code review check list](https://github.com/leanprover/mathlib/blob/master/docs/contribute/code-review.md)

### [2020-04-13 14:53:40](https://github.com/leanprover-community/mathlib/commit/f3ac7b7)
feat(combinatorics/composition): introduce compositions of an integer ([#2398](https://github.com/leanprover-community/mathlib/pull/2398))
A composition of an integer `n` is a decomposition of `{0, ..., n-1}` into blocks of consecutive
integers. Equivalently, it is a decomposition `n = i₀ + ... + i_{k-1}` into a sum of positive
integers. We define compositions in this PR, and introduce a whole interface around it. The goal is to use this as a tool in the proof that the composition of analytic functions is analytic

### [2020-04-13 13:52:21](https://github.com/leanprover-community/mathlib/commit/01ac691)
feat(category_theory/limits/shapes/binary_products): add some basic API for prod and coprod ([#2396](https://github.com/leanprover-community/mathlib/pull/2396))
Adding explicit proofs of some basic results about maps into A x B and maps from A coprod B

### [2020-04-13 12:55:12](https://github.com/leanprover-community/mathlib/commit/cf89963)
chore(scripts): update nolints.txt ([#2405](https://github.com/leanprover-community/mathlib/pull/2405))
I am happy to remove some nolints for you!

### [2020-04-13 08:52:34](https://github.com/leanprover-community/mathlib/commit/17b2d06)
refactor(order/filter): refactor filters infi and bases ([#2384](https://github.com/leanprover-community/mathlib/pull/2384))
This PR expands what Yury wrote about filter bases, and takes the opportunity to bring long overdue clarification to our treatment of infimums of filters (and also improve documentation and ordering in
filter.basic). I'm sorry it mixes reorganization and some new content, but this was hard to avoid (I do keep what motivated all this for a later PR).
The fundamental problem is that the infimum construction remained mysterious in filter.basic. All lemmas about it assume a directed family of filters. Yet there are many uses of infimums without this condition, notatably things like `⨅ i, principal (s i)` without condition on the indexed family of sets `s`.
Related to this, `filter.generate` stayed mysterious. It was used only as a technical device to lift the complete lattice structure from `set (set a)`. However it has a perfectly valid mathematical existence,
as explained by the lemma 
```lean
lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets
```
which justifies the docstring of `generate`: `generate g` is the smallest filter containing the sets `g`.
As an example of the mess this created, consider:
https://github.com/leanprover-community/mathlib/blob/e758263/src/topology/bases.lean#L25 
```lean
def has_countable_basis (f : filter α) : Prop :=
∃ s : set (set α), countable s ∧ f = ⨅ t ∈ s, principal t
```
As it stands, this definition is not clearly related to asking for the existence of a countable `s` such that `f = generate s`.
Here the main mathematical content this PR adds in this direction:
```lean
lemma mem_generate_iff (s : set $ set α) {U : set α} : U ∈ generate s ↔
∃ t ⊆ s, finite t ∧ ⋂₀ t ⊆ U
lemma infi_eq_generate (s : ι → filter α) : infi s = generate (⋃ i, (s
i).sets) 
lemma mem_infi_iff {ι} {s : ι → filter α} {U : set α} : (U ∈ ⨅ i, s i) ↔
  ∃ I : set ι, finite I ∧ ∃ V : {i | i ∈ I} → set α, (∀ i, V i ∈ s i) ∧
  (⋂ i, V i) ⊆ U
```
All the other changes in filter.basic are either:
* moving out stuff that should have been in other files (such as the lemmas that used to be at
the very top of this file)
* reordering lemmas so that we can have section headers and things are easier to find, 
* adding to the module docstring. This module docstring contains more mathematical explanation than our usual ones. I feel this is needed because many people think filters are exotic (whereas I'm more and more convinced we should teach filters).
The reordering stuff makes it clear we could split this file into a linear chain of files, like we did with topology, but this is open for discussion.
Next I added a lot to `filter.bases`. Here the issue is filter bases are used in two different ways. If you already have a filter, but you want to point out it suffices to use certain sets in it. Here you want to use Yury's `has_basis`. Or you can start with a (small) family of sets having nice properties, and build a filter out of it. Currently we don't have this in mathlib, but this is crucial for incoming PRs from the perfectoid project. For instance, in order to define the I-adic topology, you start with powers of I, make a filter and then make a topology. This also reduces the gap with Bourbaki which uses filter bases everywhere.
I turned `has_basis` into a single field structure. It makes it very slightly less convenient to prove (you need an extra pair of angle brackets) but much easier to extend when you want to record more
properties of the basis, like being countable or decreasing. Also I proved the fundamental property that `f.has_basis p s` implies that `s` (filtered by `p`) actually *is* a filter basis. This is of course easy but crucial to connect with real world maths.
At the end of this file, I moved the countable filter basis stuff that is currently in topology.bases (aiming for first countable topologies) except that I used the foundational work on filter.basic to clearly prove all different formulations. In particular:
```lean
lemma generate_eq_generate_inter (s : set (set α)) : generate s = generate (sInter '' { t | finite t ∧ t ⊆ s})
```
clarifies things because the right-hand colleciton is countable if `s` is, and has the nice directedness condition.
I also took the opportunity to simplify a proof in topology.sequences, showcasing the power of the newly introduced
```lean
lemma has_antimono_basis.tendsto [semilattice_sup ι] [nonempty ι] {l :
filter α} {p : ι → Prop} {s : ι → set α} (hl : l.has_antimono_basis p s)
{φ : ι → α} (h : ∀ i : ι, φ i ∈ s i) : tendsto φ at_top l
```
(I will add more to that sequences file in the next PR).

### [2020-04-13 08:52:32](https://github.com/leanprover-community/mathlib/commit/92c8d93)
feat(algebra/homology): the cohomology functor ([#2374](https://github.com/leanprover-community/mathlib/pull/2374))
This is the second in a series of most likely three PRs about the cohomology functor. As such, this PR depends on [#2373](https://github.com/leanprover-community/mathlib/pull/2373).
In the project laid out in `homology.lean`, @semorrison asks what the minimal assumptions are that are needed to get induced maps on images. In this PR, I offer a tautologial answer to this question: We get induced maps on images when there are induced maps on images. In this way, we can let type class resolution answer the question whether cohomology is functorial.
In particular, the third PR will contain the fact that if our images are strong epi-mono factorizations, then we get induced maps on images. Since the regular coimage construction in regular categories is a strong epi-mono factorization, the approach in this PR generalizes the previous suggestion of requiring `V` to be regular.
A quick remark about cohomology and dependent types: As you can see, at one point Lean forces us to write `i - 1 + 1` instead of `i` because these two things are not definitionally equal. I am afraid, as we do more with cohomology, there will be many cases of this issue, and to compose morphisms whose types contain different incarnations of the same integer, we will have to insert some `eq_to_hom`-esque glue and pray that we will be able to rewrite them all away in the proofs without getting the beloved `motive is not type correct` error. Maybe there is some better way to solve this problem? (Or am I overthinking this and it is not actually going to be an issue at all?)

### [2020-04-13 07:55:23](https://github.com/leanprover-community/mathlib/commit/ca98659)
chore(scripts): update nolints.txt ([#2403](https://github.com/leanprover-community/mathlib/pull/2403))
I am happy to remove some nolints for you!

### [2020-04-13 05:19:08](https://github.com/leanprover-community/mathlib/commit/51f7319)
chore(algebra/module): rename type vars, minor cleanup, add module docstring ([#2392](https://github.com/leanprover-community/mathlib/pull/2392))
* Use `R`, `S` for rings, `k` for a field, `M`, `M₂` etc for modules;
* Add a `semiring` version of `ring_hom.to_module`;
* Stop using `{rα : ring α}` trick as Lean 3.7 tries unification before class search;
* Add a short module docstring

### [2020-04-13 03:08:38](https://github.com/leanprover-community/mathlib/commit/64fa9a2)
chore(*): futureproof import syntax ([#2402](https://github.com/leanprover-community/mathlib/pull/2402))
The next community version of Lean will treat a line starting in the first column
after an import as a new command, not a continuation of the import.

### [2020-04-12 20:36:49](https://github.com/leanprover-community/mathlib/commit/ef4d235)
feat(category_theory): biproducts, and biproducts in AddCommGroup ([#2187](https://github.com/leanprover-community/mathlib/pull/2187))
This PR
1. adds typeclasses `has_biproducts` (implicitly restricting to finite biproducts, which is the only interesting case) and `has_binary_biproducts`, and the usual tooling for special shapes of limits.
2. provides customised `has_products` and `has_coproducts` instances for `AddCommGroup`, which are both just dependent functions (for `has_coproducts` we have to assume the indexed type is finite and decidable)
3. because these custom instances have identical underlying objects, it's trivial to put them together to get a `has_biproducts AddCommGroup`.
4. as for 2 & 3 with binary biproducts for AddCommGroup, implemented simply as the cartesian group.

### [2020-04-12 18:17:30](https://github.com/leanprover-community/mathlib/commit/1433f05)
fix(tactic/norm_cast): typo ([#2400](https://github.com/leanprover-community/mathlib/pull/2400))

### [2020-04-12 06:01:35](https://github.com/leanprover-community/mathlib/commit/d84de80)
feat(set_theory/game): short games, boards, and domineering ([#1540](https://github.com/leanprover-community/mathlib/pull/1540))
This is a do-over of my previous attempt to implement the combinatorial game of domineering. This time, we get a nice clean definition, and it computes!
To achieve this, I follow Reid's advice: generalise! We define 
```
class state (S : Type u) :=
(turn_bound : S → ℕ)
(L : S → finset S)
(R : S → finset S)
(left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s)
(right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s)
```
a typeclass describing `S` as "the state of a game", and provide `pgame.of [state S] : S \to pgame`.
This allows a short and straightforward definition of Domineering:
```lean
/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def board := finset (ℤ × ℤ)
...
/-- The instance describing allowed moves on a Domineering board. -/
instance state : state board :=
{ turn_bound := λ s, s.card / 2,
  L := λ s, (left s).image (move_left s),
  R := λ s, (right s).image (move_right s),
  left_bound := _
  right_bound := _, }
```
which computes:
```
example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) := dec_trivial
```

### [2020-04-12 00:32:35](https://github.com/leanprover-community/mathlib/commit/0f89392)
chore(scripts): update nolints.txt ([#2395](https://github.com/leanprover-community/mathlib/pull/2395))
I am happy to remove some nolints for you!

### [2020-04-11 22:53:11](https://github.com/leanprover-community/mathlib/commit/ee8cb15)
feat(category_theory): functorial images ([#2373](https://github.com/leanprover-community/mathlib/pull/2373))
This is the first in a series of most likely three PRs about the cohomology functor. In this PR, I
* add documentation for `comma.lean`,
* introduce the arrow category as a special case of the comma construction, and
* introduce the notion of functorial images, which means that commutative squares induce morphisms on images making the obvious diagram commute.

### [2020-04-11 21:19:21](https://github.com/leanprover-community/mathlib/commit/aa42f3b)
chore(scripts): update nolints.txt ([#2391](https://github.com/leanprover-community/mathlib/pull/2391))
I am happy to remove some nolints for you!

### [2020-04-11 18:44:17](https://github.com/leanprover-community/mathlib/commit/5f1bfcf)
chore(tactic/lean_core_docs): add API docs for core Lean tactics ([#2371](https://github.com/leanprover-community/mathlib/pull/2371))
This is an attempt to get some documentation of most core Lean tactics into the API docs.
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/undocumented.20core.20tactics (and the link in my second message in that thread) for background.
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
Co-Authored-By: Scott Morrison <scott@tqft.net>
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

### [2020-04-11 18:44:15](https://github.com/leanprover-community/mathlib/commit/80340d8)
feat(category_theory): define action_category ([#2358](https://github.com/leanprover-community/mathlib/pull/2358))
This is a simple construction that I couldn't find anywhere else: given a monoid/group action on X, we get a category/groupoid structure on X. The plan is to use to use the action groupoid in the proof of Nielsen-Schreier, where the projection onto the single object groupoid is thought of as a covering map.
To make sense of "stabilizer is mul_equiv to End", I added the simple fact that the stabilizer of any multiplicative action is a submonoid. This already existed for group actions. As far as I can tell, this instance shouldn't cause any problems as it is a Prop.

### [2020-04-11 16:16:28](https://github.com/leanprover-community/mathlib/commit/e1feab4)
refactor(*): rename ordered groups/monoids to ordered add_ groups/monoids ([#2347](https://github.com/leanprover-community/mathlib/pull/2347))
In the perfectoid project we need ordered commutative monoids, and they are multiplicative. So the additive versions should be renamed to make some place.

### [2020-04-11 14:27:08](https://github.com/leanprover-community/mathlib/commit/c9fca15)
chore(algebra/category): remove some [reducible] after Lean 3.8 ([#2389](https://github.com/leanprover-community/mathlib/pull/2389))
Now that Lean 3.8 has arrived, we can essentially revert [#2290](https://github.com/leanprover-community/mathlib/pull/2290), but leave in the examples verifying that everything still works.
Lovely!

### [2020-04-11 13:00:39](https://github.com/leanprover-community/mathlib/commit/83359d1)
chore(scripts): update nolints.txt ([#2390](https://github.com/leanprover-community/mathlib/pull/2390))
I am happy to remove some nolints for you!

### [2020-04-11 09:58:11](https://github.com/leanprover-community/mathlib/commit/4fa2924)
chore(scripts): update nolints.txt ([#2388](https://github.com/leanprover-community/mathlib/pull/2388))
I am happy to remove some nolints for you!

### [2020-04-11 09:58:09](https://github.com/leanprover-community/mathlib/commit/81d8104)
feat(actions): manage labels on PR review ([#2387](https://github.com/leanprover-community/mathlib/pull/2387))
Github actions will now add "ready-to-merge" to PRs that are approved by writing "bors r+" / "bors merge" in a PR reviews. It will also remove the "request-review" label, if present.

### [2020-04-11 09:58:07](https://github.com/leanprover-community/mathlib/commit/c68f23d)
chore(category_theory/types): add documentation, remove bad simp lemmas and instances, add notation for functions as morphisms ([#2383](https://github.com/leanprover-community/mathlib/pull/2383))
* Add module doc and doc strings for `src/category_theory/types.lean`.
* Remove some bad simp lemmas and instances in that file and `src/category_theory/category/default.lean`.
* Add a notation `↾f` which enables Lean to see a function `f : α → β` as a morphism `α ⟶ β` in the category of types.

### [2020-04-11 09:58:05](https://github.com/leanprover-community/mathlib/commit/00b510e)
perf(data/*): add inline attributes ([#2380](https://github.com/leanprover-community/mathlib/pull/2380))
This is part of an effort to bring `rewrite_search` to mathlib. Depends on [#2375](https://github.com/leanprover-community/mathlib/pull/2375).

### [2020-04-11 09:58:03](https://github.com/leanprover-community/mathlib/commit/690643a)
fix(tactic/equiv_rw): don't use `subst` unnecessarily ([#2334](https://github.com/leanprover-community/mathlib/pull/2334))
This removes an unnecessary `subst` from the algorithm in `equiv_rw`, which was responsible for inserting `eq.rec`'s in data terms.

### [2020-04-11 07:17:19](https://github.com/leanprover-community/mathlib/commit/8556499)
feat(category_theory): make defining groupoids easier ([#2360](https://github.com/leanprover-community/mathlib/pull/2360))
The point of this PR is to lower the burden of proof in showing that a category is a groupoid. Rather than constructing well-defined two-sided inverses everywhere, with `groupoid.of_trunc_split_mono` you'll only need to show that every morphism has some retraction. This makes defining the free groupoid painless. There the retractions are defined by recursion on a quotient, so this saves the work of showing that all the retractions agree.
I used `trunc` instead of `nonempty` to avoid choice / noncomputability.
I don't understand why the @'s are needed: it seems Lean doesn't know what category structure C has without specifying it?

### [2020-04-11 04:27:56](https://github.com/leanprover-community/mathlib/commit/597704a)
chore(*): switch to lean 3.8.0 ([#2361](https://github.com/leanprover-community/mathlib/pull/2361))
Switch to Lean 3.8.

### [2020-04-10 20:56:06](https://github.com/leanprover-community/mathlib/commit/ebdeb3b)
chore(scripts): update nolints.txt ([#2386](https://github.com/leanprover-community/mathlib/pull/2386))
I am happy to remove some nolints for you!

### [2020-04-10 18:03:50](https://github.com/leanprover-community/mathlib/commit/29080c8)
feat(data/list/range): add sum lemmas ([#2385](https://github.com/leanprover-community/mathlib/pull/2385))
Adding the proof that left and right multiplication in a ring commute with list sum.

### [2020-04-10 18:03:48](https://github.com/leanprover-community/mathlib/commit/61fa489)
feat(tactic/trunc_cases): a tactic for case analysis on trunc hypotheses ([#2368](https://github.com/leanprover-community/mathlib/pull/2368))
```
/--
Perform case analysis on a `trunc` expression, 
preferentially using the recursor `trunc.rec_on_subsingleton` 
when the goal is a subsingleton, 
and using `trunc.rec` otherwise.
Additionally, if the new hypothesis is a type class, 
reset the instance cache.
-/
```

### [2020-04-10 15:39:37](https://github.com/leanprover-community/mathlib/commit/3cc7a32)
feat(order/complete_lattice): add a constructor from `partial_order` and `Inf` ([#2359](https://github.com/leanprover-community/mathlib/pull/2359))
Also use `∃!` in `data/setoid`.

### [2020-04-10 13:48:32](https://github.com/leanprover-community/mathlib/commit/5169595)
chore(tactic/omega): add trace.omega option to show internal representation ([#2377](https://github.com/leanprover-community/mathlib/pull/2377))
This is helpful when debugging issues such as [#2376](https://github.com/leanprover-community/mathlib/pull/2376) and [#1484](https://github.com/leanprover-community/mathlib/pull/1484).

### [2020-04-10 13:48:30](https://github.com/leanprover-community/mathlib/commit/bf8f25a)
feat(algebra/lie_algebra): quotients of Lie modules are Lie modules ([#2335](https://github.com/leanprover-community/mathlib/pull/2335))

### [2020-04-10 12:54:03](https://github.com/leanprover-community/mathlib/commit/1a099b3)
chore(scripts): update nolints.txt ([#2381](https://github.com/leanprover-community/mathlib/pull/2381))
I am happy to remove some nolints for you!

### [2020-04-10 12:54:02](https://github.com/leanprover-community/mathlib/commit/a714245)
feat(group_theory/order_of_element): order_of_dvd_iff_pow_eq_one ([#2364](https://github.com/leanprover-community/mathlib/pull/2364))

### [2020-04-10 11:53:26](https://github.com/leanprover-community/mathlib/commit/55814dc)
fix(.github/workflows/add_label): add missing outputs ([#2379](https://github.com/leanprover-community/mathlib/pull/2379))
I hope this fixes the `add_label` workflow.

### [2020-04-10 11:53:24](https://github.com/leanprover-community/mathlib/commit/808fa8d)
chore(.github): remove linebreaks from pull request template ([#2378](https://github.com/leanprover-community/mathlib/pull/2378))
github treats a newline in the markdown text as a linebreak.

### [2020-04-10 10:19:59](https://github.com/leanprover-community/mathlib/commit/e758263)
refactor(ring_theory/algebra): use bundled homs, allow semirings ([#2303](https://github.com/leanprover-community/mathlib/pull/2303))
Fixes [#2297](https://github.com/leanprover-community/mathlib/pull/2297)
Build fails because of some class instance problems, asked [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Need.20help.20with.20class.20instance.20resolution), no answer yet.

### [2020-04-10 07:02:46](https://github.com/leanprover-community/mathlib/commit/f723f37)
feat(ci): switch from mergify to bors ([#2322](https://github.com/leanprover-community/mathlib/pull/2322))
This PR (joint work with @gebner) changes the automation that merges our PRs from mergify to a service called [bors](https://bors.tech/). Currently, the "time-to-master" of an approved PR grows linearly with the number of currently queued PRs, since mergify builds PRs against master one at a time. bors batches approved PRs together before building them against master so that most PRs should merge within 2*(current build time).
As far as day-to-day use goes, the main difference is that maintainers will approve PRs by commenting with the magic words "`bors r+`" instead of "approving" on Github and adding the "ready-to-merge" label. Contributors should be aware that pushing additional commits to an approved PR will now require a new approval.
Some longer notes on bors and mathlib can be found [here](https://github.com/leanprover-community/mathlib/blob/2ea15d65c32574aaf513e27feb24424354340eea/docs/contribute/bors.md).

### [2020-04-10 06:01:10](https://github.com/leanprover-community/mathlib/commit/495deb9)
chore(scripts): update nolints.txt

### [2020-04-10 05:27:11](https://github.com/leanprover-community/mathlib/commit/6152d45)
refactor(field_theory/perfect_closure): use bundled homs, review ([#2357](https://github.com/leanprover-community/mathlib/pull/2357))
* refactor(field_theory/perfect_closure): use bundled homs, review
Also add lemmas like `monoid_hom.iterate_map_mul`.
* Fix a typo spotted by `lint`
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>

### [2020-04-10 02:46:37](https://github.com/leanprover-community/mathlib/commit/b15c213)
chore(*): replace uses of `---` delimiter in tactic docs ([#2372](https://github.com/leanprover-community/mathlib/pull/2372))
* update abel doc string
the tactic doc entry seems completely fine as the doc string,
I don't know why these were separated
* replace uses of --- in docs

### [2020-04-09 23:56:46](https://github.com/leanprover-community/mathlib/commit/19e1a96)
doc(add_tactic_doc): slight improvement to docs ([#2365](https://github.com/leanprover-community/mathlib/pull/2365))
* doc(add_tactic_doc): slight improvement to docs
* Update docs/contribute/doc.md
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* sentence
* update add_tactic_doc doc entry

### [2020-04-09 21:05:16](https://github.com/leanprover-community/mathlib/commit/4a1dc42)
chore(scripts): update nolints.txt

### [2020-04-09 20:31:33](https://github.com/leanprover-community/mathlib/commit/6a7db27)
feat(tactic/ring_exp) allow ring_exp inside of conv blocks ([#2369](https://github.com/leanprover-community/mathlib/pull/2369))
* allow ring_exp inside of conv blocks
* Update test/ring_exp.lean
* Update test/ring_exp.lean
* Update test/ring_exp.lean
* add docstrings

### [2020-04-09 17:41:23](https://github.com/leanprover-community/mathlib/commit/d240f38)
feat(tactic/simp_result): tactics for simplifying the results of other tactics ([#2356](https://github.com/leanprover-community/mathlib/pull/2356))
* feat(tactic/simp_result): tactics for simplifying the results of other tactics
* word
* better tests
* order of arguments
* Revert "order of arguments"
This reverts commit 38cfec6867459fcc4c5ef2d41f5313a5b0466c53.
* fix add_tactic_doc
* slightly robustify testing
* improve documentation

### [2020-04-09 12:44:49](https://github.com/leanprover-community/mathlib/commit/63fc23a)
feat(data/list): chain_iff_nth_le ([#2354](https://github.com/leanprover-community/mathlib/pull/2354))
* feat(data/list): chain_iff_nth_le
* Update src/data/list/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* move
* fix

### [2020-04-09 10:08:54](https://github.com/leanprover-community/mathlib/commit/bda8a05)
doc(docs/extras/tactic_writing) add cheap method ([#2198](https://github.com/leanprover-community/mathlib/pull/2198))
* doc(docs/extras/tactic_writing) add cheap method
About 50% of my personal use cases for writing tactics are just because I want a simple way of stringing several tactics together, so I propose adding this so I will know where to look when I realise I can't remember the syntax.
* style fixes
* Update tactic_writing.md
* Update tactic_writing.md
* Update docs/extras/tactic_writing.md

### [2020-04-09 09:03:53](https://github.com/leanprover-community/mathlib/commit/a8797ce)
feat(data/set/basic): add lemmata ([#2353](https://github.com/leanprover-community/mathlib/pull/2353))
* feat(data/set/basic): add lemmata
* switch to term mode proof
* removing dupe
* make linter happy
* Update src/data/set/basic.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* change proof

### [2020-04-09 06:10:23](https://github.com/leanprover-community/mathlib/commit/80d3ed8)
fix(algebra/euclidean_domain): remove decidable_eq assumption ([#2362](https://github.com/leanprover-community/mathlib/pull/2362))
This PR removes the `decidable_eq` assumption on the `field.to_euclidean_domain` instance.  Decidable equality was only used to define the remainder with an if-then-else, but this can also be done by exploiting the fact that `0⁻¹ = 0`.
The current instance is a bit problematic since it can cause `a + b : ℝ` to be noncomputable if type-class inference happens to choose the wrong instance (going through `euclidean_domain` instead of "directly" through some kind of ring).

### [2020-04-09 03:16:05](https://github.com/leanprover-community/mathlib/commit/67b121e)
chore(scripts): update nolints.txt

### [2020-04-09 02:50:30](https://github.com/leanprover-community/mathlib/commit/fbc9592)
chore(data/list): move some sections to separate files ([#2341](https://github.com/leanprover-community/mathlib/pull/2341))
* move list.func namespace to its own file
* move erase_dup to its own file
* move rotate to its own file
* move tfae to its own file
* move bag_inter and intervals
* move range out
* move nodup
* move chain and pairwise
* move zip
* move forall2
* move of_fn
* add copyright headers
* remove unnecessary sections, move defns to func.set and tfae
* fixes
* oops, forgot to add file

### [2020-04-09 00:00:42](https://github.com/leanprover-community/mathlib/commit/e4e483e)
Bugfix for norm num when testing divisibility of integers ([#2355](https://github.com/leanprover-community/mathlib/pull/2355))
they were assumed nats somehow

### [2020-04-08 21:12:22](https://github.com/leanprover-community/mathlib/commit/c3d9cf9)
feat(analysis/analytic/basic): change origin of power series ([#2327](https://github.com/leanprover-community/mathlib/pull/2327))
* feat(analysis/analytic/basic): move basepoint of power series
* docstring
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>

### [2020-04-08 18:19:54](https://github.com/leanprover-community/mathlib/commit/dae7154)
chore(scripts): update nolints.txt

### [2020-04-08 17:46:11](https://github.com/leanprover-community/mathlib/commit/55d430c)
feat(tactic/linter): add decidable_classical linter ([#2352](https://github.com/leanprover-community/mathlib/pull/2352))
* feat(tactic/linter): add decidable_classical linter
* docstring
* cleanup
* fix build, cleanup
* fix test
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/default.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/data/dfinsupp.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>

### [2020-04-08 15:10:31](https://github.com/leanprover-community/mathlib/commit/65a5dc0)
feat(data/support): define support of a function and prove some properties ([#2340](https://github.com/leanprover-community/mathlib/pull/2340))
* feat(data/support): define support of a function and prove some properties
* Add `support_mul'` for `group_with_zero`

### [2020-04-08 12:29:19](https://github.com/leanprover-community/mathlib/commit/b550c16)
fix(tactic/solve_by_elim): fix metavariable bug from [#2269](https://github.com/leanprover-community/mathlib/pull/2269) ([#2289](https://github.com/leanprover-community/mathlib/pull/2289))
* chore(tactic/solve_by_elim): fix metavariable bug from [#2269](https://github.com/leanprover-community/mathlib/pull/2269)
* tests
* forgot to save file?
* fix bug, and tweak docs
* fix
* oops, remove stray
* provide both `lemmas` and `lemma_thunks` fields
* fix
* fix
* remove code duplication
* fix indenting
* add comments about evaluating thunks in mk_assumption_set

### [2020-04-08 09:55:55](https://github.com/leanprover-community/mathlib/commit/bd21cff)
feat(data/list/basic): some lemmas about sum/head/tail for list ℕ ([#2342](https://github.com/leanprover-community/mathlib/pull/2342))
* feat(data/list/basic): some lemmas about sum/head/tail for list ℕ
* Add comment
* remove lemma, moving to another PR
* suggestion from review

### [2020-04-08 07:20:14](https://github.com/leanprover-community/mathlib/commit/cb8d8ac)
feat (data/list/basic): lemmas about prod and take ([#2345](https://github.com/leanprover-community/mathlib/pull/2345))
* feat (data/list/basic): lemmas about prod and take
* move lemma
* one more
* using to_additive properly

### [2020-04-08 01:12:13](https://github.com/leanprover-community/mathlib/commit/732f710)
feat(data/list/basic): nth_le 0 = head ([#2350](https://github.com/leanprover-community/mathlib/pull/2350))
* feat(data/list/basic): nth_le 0 = head
* oops

### [2020-04-07 22:38:07](https://github.com/leanprover-community/mathlib/commit/0e2970c)
feat(algebra/group/basic.lean): add inv_mul_eq_one ([#2349](https://github.com/leanprover-community/mathlib/pull/2349))

### [2020-04-07 19:50:30](https://github.com/leanprover-community/mathlib/commit/34ae62a)
feat(algebra/homology): functoriality of induced maps on cycles ([#2338](https://github.com/leanprover-community/mathlib/pull/2338))
* feat(algebra/homology): Functoriality of induced maps on cycles
* Rename cycles to cocycles, induced_maps_on_cocycles_functor to kernels_functor
* update names

### [2020-04-07 17:07:59](https://github.com/leanprover-community/mathlib/commit/e2fa8b2)
chore(test/refine_struct): remove dead code ([#2348](https://github.com/leanprover-community/mathlib/pull/2348))

### [2020-04-07 16:06:37](https://github.com/leanprover-community/mathlib/commit/abccc30)
chore(scripts): update nolints.txt

### [2020-04-07 15:31:37](https://github.com/leanprover-community/mathlib/commit/6f75c57)
refactor(measure_theory/borel): `borel` is not an `instance` ([#2326](https://github.com/leanprover-community/mathlib/pull/2326))
Redo Borel spaces in a way similar to `closed_order_topology`/`order_topology`.
* `borel` is no longer an `instance`;
* define typeclass `opens_measurable_space` for a space with `measurable_space` and `topological_space` structures such that all open sets are measurable;
* define typeclass `borel_space` for a space with `measurable_space` and `topological_space` structures such that `measurable_space` structure is equal to `borel`;
* use dot syntax in more cases;
* review some proofs that started to fail because of this change.

### [2020-04-07 12:40:05](https://github.com/leanprover-community/mathlib/commit/97c4302)
feat(data/list/basic): add map_take/drop_take ([#2344](https://github.com/leanprover-community/mathlib/pull/2344))

### [2020-04-07 10:10:41](https://github.com/leanprover-community/mathlib/commit/2f2e016)
chore(data/list/basic): rename take_all -> take_length ([#2343](https://github.com/leanprover-community/mathlib/pull/2343))
* chore(data/list/basic): rename take_all -> take_length
* also rename drop_all

### [2020-04-07 08:48:42](https://github.com/leanprover-community/mathlib/commit/d936c28)
feat(data/real/nnreal): coe_max and coe_min ([#2346](https://github.com/leanprover-community/mathlib/pull/2346))

### [2020-04-07 06:44:18](https://github.com/leanprover-community/mathlib/commit/c85453d)
fix(tactic/refine_struct): don't add unnecessary `eq.mpr` or `id` ([#2319](https://github.com/leanprover-community/mathlib/pull/2319))
* fix(tactic/interactive): don't unfold non-Prop goals
The old behaviour caused `eq.mpr`'s in `pi_instance` output.
* add a test file
* move test
* actually move test
* Update test/refine_struct.lean
* test: fix compile
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Try a fix by @gebner and @cipher1024
* Update test/refine_struct.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* apply Gabriel's suggestion

### [2020-04-07 04:14:25](https://github.com/leanprover-community/mathlib/commit/df64ea9)
chore(scripts): update nolints.txt

### [2020-04-07 03:42:42](https://github.com/leanprover-community/mathlib/commit/60d1457)
chore(algebra/big_operators): drop some `decidable_eq` assumptions ([#2332](https://github.com/leanprover-community/mathlib/pull/2332))
* chore(algebra/big_operators): drop some `decidable_eq` assumptions
I wonder why `lint` didn't report them.
* Drop unused arguments

### [2020-04-06 23:32:14](https://github.com/leanprover-community/mathlib/commit/7628c6c)
chore(scripts): update nolints.txt

### [2020-04-06 23:05:14](https://github.com/leanprover-community/mathlib/commit/48cc0c8)
feat(algebra/group_with_zero): groups with a zero element adjoined ([#2242](https://github.com/leanprover-community/mathlib/pull/2242))
* feat(algebra/group_with_zero*): Basics on groups with a zero adjoined
* feat(algebra/group_with_zero*): Basics on groups with a zero adjoined
* Make argument implicit
* Move inv_eq_zero out of gwz namespace
* Partial refactor
* Remove open_locale classical
* Fix build
* Factor out monoid_with_zero
* Fix linter errors, hopefully
* Fix build
* Fix tests
* Replace G with G0
* Add spaces around `^`
* Add spaces and backticks in docstrings
* Fix docstring of `mk0`
* Fix statement of inv_eq_iff
* Golf inv_injective
* Golf inv_eq_zero
* Remove the gwz namespace
* Fix build

### [2020-04-06 21:01:55](https://github.com/leanprover-community/mathlib/commit/89fdec6)
fix(data/finset): add comment ([#2336](https://github.com/leanprover-community/mathlib/pull/2336))
* doc(data/finset): adding comment
* fix(topology/metric_space/basic): comment typo

### [2020-04-06 18:20:25](https://github.com/leanprover-community/mathlib/commit/7b120a3)
feat(data/mv_polynomial): add pderivative_eq_zero_of_not_mem_vars ([#2324](https://github.com/leanprover-community/mathlib/pull/2324))
* feat(data/mv_polynomial): add pderivative_eq_zero_of_not_mem_vars
* Added doc comment for `pderivative.add_monoid_hom`
* Fix formatting
* fixed issues from review
* change begin end to braces.
* fix issues from review

### [2020-04-06 15:34:03](https://github.com/leanprover-community/mathlib/commit/ff910dc)
feat(topology/bounded_continuous_function): composition of limits when uniform convergence ([#2260](https://github.com/leanprover-community/mathlib/pull/2260))
* feat(topology/bounded_continuous_function): composition of limits when uniform convergence
* better statement
* uniform space version
* cleanup
* fix linter
* reviewer's comments

### [2020-04-06 12:39:52](https://github.com/leanprover-community/mathlib/commit/572fad1)
chore(topology/instances/ennreal): prove `tendsto_iff_edist_tendsto_0` ([#2333](https://github.com/leanprover-community/mathlib/pull/2333))

### [2020-04-06 10:15:13](https://github.com/leanprover-community/mathlib/commit/3d60e13)
chore(algebra/field): move some lemmas from `field` to `division_ring` ([#2331](https://github.com/leanprover-community/mathlib/pull/2331))

### [2020-04-05 23:39:22](https://github.com/leanprover-community/mathlib/commit/a2e7639)
feat(order/filter): more eventually/frequently API ([#2330](https://github.com/leanprover-community/mathlib/pull/2330))
* feat(order/filter): more eventually/frequently API
* Update after review
* Add simp attribute
* Update src/order/filter/basic.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* Update src/order/filter/basic.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>

### [2020-04-05 17:46:07](https://github.com/leanprover-community/mathlib/commit/26bf273)
feat(logic/embedding): embedding punit/prod ([#2315](https://github.com/leanprover-community/mathlib/pull/2315))
* feat(logic/embedding): embedding punit/prod
* renaming to sectl
* Revert disambiguations no longer needed

### [2020-04-05 05:53:08](https://github.com/leanprover-community/mathlib/commit/23681c3)
feat(tactic/linarith): split conjunctions in hypotheses ([#2320](https://github.com/leanprover-community/mathlib/pull/2320))
* feat(tactic/linarith): split conjunctions in hypotheses
* update doc

### [2020-04-04 17:59:00](https://github.com/leanprover-community/mathlib/commit/dea8bd4)
feat(*/multilinear): more material ([#2197](https://github.com/leanprover-community/mathlib/pull/2197))
* feat(*/multilinear): more material
* improvements
* docstring
* elaboration strategy
* remove begin ... end
* fix build
* linter

### [2020-04-04 16:43:46](https://github.com/leanprover-community/mathlib/commit/8406896)
chore(ci): always push release to azure ([#2321](https://github.com/leanprover-community/mathlib/pull/2321))
PR [#2048](https://github.com/leanprover-community/mathlib/pull/2048) changed the CI so that olean caches are not pushed to Azure if a later commit on the same branch occurs. The reasoning was that it was unlikely that anyone would fetch those caches. That's changed as of [#2278](https://github.com/leanprover-community/mathlib/pull/2278), since `fetch_olean_cache.sh` now looks for caches from commits earlier in the history. This means that currently, we can observe the following wasteful sequence of events in several PRs (e.g. [#2258](https://github.com/leanprover-community/mathlib/pull/2258)):
1. commit A gets pushed to a certain branch and CI_A starts.
2. While CI_A is still running the `leanpkg build` step, commit B is pushed and CI_B starts.
3. CI_A finishes `leanpkg build` but doesn't upload its cache to Azure because of [#2048](https://github.com/leanprover-community/mathlib/pull/2048) 
4. Now commit C is pushed and can't use the results of CI_A
5. CI_B finishes `leanpkg build` but doesn't upload its cache
6. Commit D is pushed and can't use the results of CI_A or CI_B ...
(This can keep happening as long as the next commit arrives before the most recent CI uploads to Azure).
I also cleaned up some stuff that was left over from when we ran the build on both "pr" and "push" events.

### [2020-04-04 08:11:40](https://github.com/leanprover-community/mathlib/commit/63aa8b1)
feat(data/mv_polynomial): add partial derivatives ([#2298](https://github.com/leanprover-community/mathlib/pull/2298))
* feat(data/mv_polynomial): add partial derivatives
* Added suggestions from PR.
* trying to placate simp linter
* Updated implementation of `pderivative`
* formatting suggestions from Bryan
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Suggestions from review.
* rearrange aux lemmas

### [2020-04-04 05:20:52](https://github.com/leanprover-community/mathlib/commit/906874e)
feat(category_theory): quotient categories ([#2310](https://github.com/leanprover-community/mathlib/pull/2310))
This constructs the quotient of a category by an arbitrary family of relations on its hom-sets. Analogous to "quotient of a group by the normal closure of a subset", as opposed to "quotient of a group by a normal subgroup".
The plan is to eventually use this together with the path category to construct the free groupoid on a graph.

### [2020-04-03 12:34:08](https://github.com/leanprover-community/mathlib/commit/a590d4b)
feat(group_theory/monoid_localization): some homs induced on localizations: lift, map ([#2118](https://github.com/leanprover-community/mathlib/pull/2118))
* should I be changing and committing toml idk
* initial monoid loc lemmas
* responding to PR comments
* removing bad @[simp]
* inhabited instances
* remove #lint
* additive inhabited instance
* using is_unit & is_add_unit
* doc string
* remove simp
* submonoid.monoid_loc... -> submonoid.localization
* submonoid.monoid_loc... -> submonoid.localization
* generalize inhabited instance
* remove inhabited instance
* 2nd section
* docs and linting
* removing questionable `@[simp]s`
* removing away
* adding lemmas, removing 'include'
* removing import
* responding to PR comments
* use eq_of_eq to prove comp_eq_of_eq
* name change
* trying to update mathlib
* make lemma names consistent
* Update src/algebra/group/is_unit.lean
* Update src/algebra/group/is_unit.lean
* fix build
* documentation and minor changes
* spacing
* fix build
* applying comments

### [2020-04-03 08:57:48](https://github.com/leanprover-community/mathlib/commit/6af5901)
chore(scripts): update nolints.txt

### [2020-04-03 08:24:57](https://github.com/leanprover-community/mathlib/commit/8af4bb8)
refactor(tactic/lint): split into multiple files ([#2299](https://github.com/leanprover-community/mathlib/pull/2299))
The `lint.lean` file is getting too long for me to comfortably navigate.  This PR splits the file up into several parts:
 * `tactic.lint.basic` defining the `linter` structure and the `@[linter]` and `@[nolint]` attributes
 * `tactic.lint.frontend` defined the functions to run the linters and the various `#lint` commands
 * The linters are split into three separate files, the simp linters, the type class linters, and the rest.
 * `tactic.lint` imports all of the files above so `import tactic.lint` still works as before

### [2020-04-03 06:55:45](https://github.com/leanprover-community/mathlib/commit/cb0a1b5)
feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations ([#2314](https://github.com/leanprover-community/mathlib/pull/2314))
* feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations
* Remove `@[congr]`
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>

### [2020-04-03 04:11:38](https://github.com/leanprover-community/mathlib/commit/1b24e0a)
chore(test/*): move tests into individual files ([#2317](https://github.com/leanprover-community/mathlib/pull/2317))

### [2020-04-02 19:25:32](https://github.com/leanprover-community/mathlib/commit/d3b8622)
fix(tactic/lint): simp_nf: do not ignore errors ([#2266](https://github.com/leanprover-community/mathlib/pull/2266))
This PR fixes some bugs in the `simp_nf` linter.  Previously it ignored all errors (from failing tactics).  I've changed this so that errors from linters are handled centrally and reported as linter warnings.  The `simp_is_conditional` function was also broken.
As usual, new linters find new issues:
 1. Apparently Lean sometimes throws away simp lemmas.  https://github.com/leanprover-community/lean/issues/163
 2. Some types define `has_coe` but have an incorrect `has_coe_to_fun`, causing the simplifier to loop `⇑f a = ⇑↑f a = ⇑f a`.  See the new library note:

### [2020-04-02 16:19:33](https://github.com/leanprover-community/mathlib/commit/654533f)
feat(logic/basic): a few lemmas about `exists_unique` ([#2283](https://github.com/leanprover-community/mathlib/pull/2283))
The goal is to be able to deal with formulas like `∃! x ∈ s, p x`. Lean parses them as `∃! x, ∃! (hx : x ∈ s), p x`. While this is equivalent to `∃! x, x ∈ s ∧ p x`, it is not defeq to this formula.

### [2020-04-02 13:55:30](https://github.com/leanprover-community/mathlib/commit/a88356f)
chore(topology/metric_space): use dot notation ([#2313](https://github.com/leanprover-community/mathlib/pull/2313))
* in `continuous.dist` and `continuous.edist`;
* in `tendsto.dist` and `tendsto.edist`.

### [2020-04-02 11:19:51](https://github.com/leanprover-community/mathlib/commit/3c27d28)
feat(algebra/pi_instances): bundled homs for apply and single ([#2186](https://github.com/leanprover-community/mathlib/pull/2186))
feat(algebra/pi_instances): bundled homs for apply and single ([#2186](https://github.com/leanprover-community/mathlib/pull/2186))
This adds some bundled monoid homomorphisms, in particular
```
def monoid_hom.apply (i : I) : (Π i, f i) →* f i := ...
```
and
```
def add_monoid_hom.single (i : I) : f i →+ Π i, f i :=
```
and supporting lemmas.

### [2020-04-02 08:17:59](https://github.com/leanprover-community/mathlib/commit/313cc2f)
chore(category_theory/concrete_category): take an instance, rather than extending, category ([#2195](https://github.com/leanprover-community/mathlib/pull/2195))
chore(category_theory/concrete_category): take an instance, rather than extending, category ([#2195](https://github.com/leanprover-community/mathlib/pull/2195))
Our current design for `concrete_category` has it extend `category`.
This PR changes that so that is takes an instance, instead.
I want to do this because I ran into a problem defining `concrete_monoidal_category`, which is meant to be a monoidal category, whose faithful functor to Type is lax monoidal. (The prime example here is `Module R`, where there's a map `F(X) \otimes F(Y) \to F(X \otimes Y)`, but not the other way: here `F(X) \otimes F(Y)` is just the monoidal product in Type, i.e. cartesian product, and the function here is `(x, y) \mapsto x \otimes y`.)
Now, `monoidal_category` does not extend `category`, but instead takes a typeclass, so with the old design `concrete_monoidal_category` was going to be a Frankenstein, extending `concrete_category` and taking a `[monoidal_category]` type class. However, when 3.7 landed this went horribly wrong, and even defining `concrete_monoidal_category` caused an unbounded typeclass search.
So.... I've made everything simpler, and just not used `extends` at all. It's all just typeclasses. This makes some places a bit more verbose, as we have to summon lots of separate typeclasses, but besides that everything works smoothly.
(Note, this PR makes the change to `concrete_category`, but does not yet introduce `concrete_monoidal_category`.)

### [2020-04-02 05:51:39](https://github.com/leanprover-community/mathlib/commit/f55e3ce)
refactor(*): move `algebra` below `polynomial` in the `import` chain ([#2294](https://github.com/leanprover-community/mathlib/pull/2294))
* Move `algebra` below `polynomial` in the `import` chain
This PR only moves code and slightly generalizes
`mv_polynomial.aeval`.
* Fix compile
* Update src/data/mv_polynomial.lean
* Apply suggestions from code review
* Apply suggestions from code review
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>

### [2020-04-02 03:27:11](https://github.com/leanprover-community/mathlib/commit/652fc17)
chore(data/set/lattice): add `set_of_exists` and `set_of_forall` ([#2312](https://github.com/leanprover-community/mathlib/pull/2312))

### [2020-04-01 22:05:57](https://github.com/leanprover-community/mathlib/commit/5b972be)
chore(scripts): update nolints.txt

### [2020-04-01 21:30:30](https://github.com/leanprover-community/mathlib/commit/33764ab)
chore(tactic/transport): rename to transform_decl ([#2308](https://github.com/leanprover-community/mathlib/pull/2308))
* chore(tactic/transport): rename to transform_decl
* satisfying the linter
* oops, wrong comment format

### [2020-04-01 18:42:34](https://github.com/leanprover-community/mathlib/commit/badc615)
chore(scripts): update nolints.txt

### [2020-04-01 18:06:00](https://github.com/leanprover-community/mathlib/commit/a8076b2)
refactor(data/real/irrational): review ([#2304](https://github.com/leanprover-community/mathlib/pull/2304))
* refactor(data/real/irrational): review
* Update src/data/real/irrational.lean
* Update src/data/real/irrational.lean
* Apply suggestions from code review

### [2020-04-01 13:29:58](https://github.com/leanprover-community/mathlib/commit/203ebb2)
feat(tactic/simp_rw): support `<-` in `simp_rw` ([#2309](https://github.com/leanprover-community/mathlib/pull/2309))

### [2020-04-01 10:26:28](https://github.com/leanprover-community/mathlib/commit/fb658ac)
chore(scripts): update nolints.txt

### [2020-04-01 09:50:28](https://github.com/leanprover-community/mathlib/commit/003141c)
chore(algebra/module): cleanup `is_linear_map` ([#2296](https://github.com/leanprover-community/mathlib/pull/2296))
* reuse facts about `→+`;
* add `map_smul`
* add a few docstrings

### [2020-04-01 06:47:48](https://github.com/leanprover-community/mathlib/commit/c7fb84b)
refactor(group_theory/submonoid): review API ([#2173](https://github.com/leanprover-community/mathlib/pull/2173))
The old API was mirroring the API for unbundled submonoids, while the
new one is based on the API of `submodule`.
Also move some facts about `monoid`/`group` structure on `M × N` to
`algebra/group/prod`.

### [2020-04-01 04:05:06](https://github.com/leanprover-community/mathlib/commit/67e7f90)
fix(algebra/category): make has_coe_to_sort instances for bundled categories reducible ([#2290](https://github.com/leanprover-community/mathlib/pull/2290))
* fix(algebra/category): make has_coe_to_sort instances for bundled categories reducible
* fix library notes
* fix import
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix notes

### [2020-04-01 01:14:10](https://github.com/leanprover-community/mathlib/commit/cc20a86)
feat(data/nat/basic): `simp` lemmas about inequalities with `bit*` ([#2207](https://github.com/leanprover-community/mathlib/pull/2207))
* feat(data/nat/basic): `simp` lemmas about inequalities with `bit*`
* Fix compile of `computability/partrec_code`
* Fix `nat.bit_cases` to work for `Type*` too
* Generalize some lemmas to `linear_ordered_semiring`s
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Apply suggestions from code review
Co-Authored-By: Scott Morrison <scott@tqft.net>
* fixing a proof