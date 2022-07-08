### [2020-08-31 22:41:43](https://github.com/leanprover-community/mathlib/commit/036527a)
feat(linear_algebra/finite_dimensional): eq_of_le_of_findim_eq ([#4005](https://github.com/leanprover-community/mathlib/pull/4005))
Add a variant of `eq_top_of_findim_eq`, where instead of proving a
submodule equal to `⊤`, it's shown equal to another finite-dimensional
submodule with the same dimension that contains it.  The two lemmas
are related by the `comap_subtype` lemmas, so the proof is short, but
it still seems useful to have this form.

### [2020-08-31 22:11:18](https://github.com/leanprover-community/mathlib/commit/be3b175)
feat(analysis/normed_space/real_inner_product): inner_add_sub_eq_zero_iff ([#4004](https://github.com/leanprover-community/mathlib/pull/4004))
Add a lemma that the sum and difference of two vectors are orthogonal
if and only if they have the same norm.  (This can be interpreted
geometrically as saying e.g. that a median of a triangle from a vertex
is orthogonal to the opposite edge if and only if the triangle is
isosceles at that vertex.)

### [2020-08-31 19:25:35](https://github.com/leanprover-community/mathlib/commit/d0a8cc4)
feat(analysis/special_functions/trigonometric): ranges of `real.sin` and `real.cos` ([#3998](https://github.com/leanprover-community/mathlib/pull/3998))

### [2020-08-31 17:07:43](https://github.com/leanprover-community/mathlib/commit/d4484a4)
fix(widget): workaround for webview rendering bug ([#3997](https://github.com/leanprover-community/mathlib/pull/3997))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/extension.20performance
The bug seems to go away if we collapse the extra nested spans made by `block` in to one span.
Still should do some tests to make sure this doesn't break anything else.
Minimal breaking example is:
```
import tactic.interactive_expr
example :
0+1+2+3+4+5+6+7+8+9 +
0+1+2+3+4+5+6+7+8+9 =
0+1+2+3+4+5+6+7+8+9 :=
by skip
```

### [2020-08-31 15:32:01](https://github.com/leanprover-community/mathlib/commit/d2b18a1)
feat(algebra/field, ring_theory/ideal/basic): an ideal is maximal iff the quotient is a field ([#3986](https://github.com/leanprover-community/mathlib/pull/3986))
One half of the theorem was already proven (the implication maximal
ideal implies that the quotient is a field), but the other half was not,
mainly because it was missing a necessary predicate.
I added the predicate is_field that can be used to tell Lean that the
usual ring structure on the quotient extends to a field. The predicate
along with proofs to move between is_field and field were provided by
Kevin Buzzard. I also added a lemma that the inverse is unique in
is_field.
At the end I also added the iff statement of the theorem.

### [2020-08-31 14:45:05](https://github.com/leanprover-community/mathlib/commit/8089f50)
chore(category_theory/limits): some simp lemmas ([#3993](https://github.com/leanprover-community/mathlib/pull/3993))

### [2020-08-31 13:17:44](https://github.com/leanprover-community/mathlib/commit/9e9e318)
feat(data/fin): simplify fin.mk ([#3996](https://github.com/leanprover-community/mathlib/pull/3996))
After the recent changes to make `fin n` a subtype, expressions
involving `fin.mk` were not getting simplified as they used to be,
since the `simp` lemmas are for the anonymous constructor, which is
`subtype.mk` not `fin.mk`.  Add a `simp` lemma converting `fin.mk` to
the anonymous constructor.
In particular, unsimplified expressions involving `fin.mk` were coming
out of `fin_cases` (I think this comes from `fin_range` in
`data/list/range.lean` using `fin.mk`).  I don't know if that should
be avoiding creating the `fin.mk` expressions in the first place, but
simplifying them seems a good idea in any case.

### [2020-08-31 08:47:27](https://github.com/leanprover-community/mathlib/commit/10ebb71)
feat(measure_theory): induction principles in measure theory ([#3978](https://github.com/leanprover-community/mathlib/pull/3978))
This commit adds three induction principles for measure theory
* To prove something for arbitrary simple functions
* To prove something for arbitrary measurable functions into `ennreal`
* To prove something for arbitrary measurable + integrable functions.
This also adds some basic lemmas to various files. Not all of them are used in this PR, some will be used by near-future PRs.

### [2020-08-31 08:11:24](https://github.com/leanprover-community/mathlib/commit/bf7487b)
fix(algebraic_geometry/Spec): inline TeX in heading ([#3992](https://github.com/leanprover-community/mathlib/pull/3992))

### [2020-08-31 05:09:37](https://github.com/leanprover-community/mathlib/commit/b79fc03)
feature(algebraic_geometry/Scheme): the category of schemes ([#3961](https://github.com/leanprover-community/mathlib/pull/3961))
The definition of a `Scheme`, and the category of schemes as the full subcategory of locally ringed spaces.

### [2020-08-30 23:20:13](https://github.com/leanprover-community/mathlib/commit/e88843c)
feat(data/finset/sort): range_mono_of_fin ([#3987](https://github.com/leanprover-community/mathlib/pull/3987))
Add a `simp` lemma giving the range of `mono_of_fin`.

### [2020-08-30 18:40:35](https://github.com/leanprover-community/mathlib/commit/861f182)
feat(widget): add go to definition button. ([#3982](https://github.com/leanprover-community/mathlib/pull/3982))
Now you can hit a new button in the tooltip and it will reveal the definition location in the editor!

### [2020-08-30 17:12:27](https://github.com/leanprover-community/mathlib/commit/f9ee416)
feat(topology/tactic): optionally make `continuity` verbose with `?` ([#3962](https://github.com/leanprover-community/mathlib/pull/3962))

### [2020-08-30 15:37:08](https://github.com/leanprover-community/mathlib/commit/1073204)
feat(logic/nontrivial): function.injective.exists_ne ([#3983](https://github.com/leanprover-community/mathlib/pull/3983))
Add a lemma that an injective function from a nontrivial type has an
argument at which it does not take a given value.

### [2020-08-30 11:24:28](https://github.com/leanprover-community/mathlib/commit/942c779)
feat(meta/widget): Add css classes for indentation as required by group and nest. ([#3764](https://github.com/leanprover-community/mathlib/pull/3764))
this is a transplant of https://github.com/leanprover-community/lean/pull/439
the relevant css section looks more or less like this:
```css
        .indent-code {
            text-indent: calc(var(--indent-level) * -1ch);
            padding-left: calc(var(--indent-level) * 1ch);
        }
```
For details, one can play around here: https://jsfiddle.net/xbzhL60m/45/

### [2020-08-30 05:38:17](https://github.com/leanprover-community/mathlib/commit/ffce8f6)
feat(data/complex/is_R_or_C): add typeclass for real or complex ([#3934](https://github.com/leanprover-community/mathlib/pull/3934))

### [2020-08-30 04:53:26](https://github.com/leanprover-community/mathlib/commit/a18f142)
feat(set_theory/game): computation of grundy_value (nim n + nim m) ([#3977](https://github.com/leanprover-community/mathlib/pull/3977))

### [2020-08-30 01:59:33](https://github.com/leanprover-community/mathlib/commit/dfdb38a)
feat(data/fin): nontrivial instance ([#3979](https://github.com/leanprover-community/mathlib/pull/3979))
Add an instance `nontrivial (fin (n + 2))`.

### [2020-08-29 17:36:23](https://github.com/leanprover-community/mathlib/commit/14e7fe8)
feat(linear_algebra/char_poly/coeff,*): prerequisites for friendship theorem ([#3953](https://github.com/leanprover-community/mathlib/pull/3953))
adds several assorted lemmas about matrices and `zmod p`
proves that if `M` is a square matrix with entries in `zmod p`, then `tr M^p = tr M`, needed for friendship theorem

### [2020-08-29 17:36:21](https://github.com/leanprover-community/mathlib/commit/4c4243c)
feat(linear_algebra): determinant of vectors in a basis ([#3919](https://github.com/leanprover-community/mathlib/pull/3919))
From the sphere eversion project, define the determinant of a family of vectors with respects to a basis. 
The main result is `is_basis.iff_det` asserting a family of vectors is a basis iff its determinant in some basis is invertible.
Also renames `equiv_fun_basis` to `is_basis.equiv_fun` and `equiv_fun_basis_symm_apply` to `is_basis.equiv_fun_symm_apply`, in order to use dot notation.

### [2020-08-29 15:59:15](https://github.com/leanprover-community/mathlib/commit/94b1292)
doc(topology/sheaves): update module docs ([#3971](https://github.com/leanprover-community/mathlib/pull/3971))

### [2020-08-29 15:59:13](https://github.com/leanprover-community/mathlib/commit/ba41f0a)
feat(data/nat): API for test_bit and bitwise operations ([#3964](https://github.com/leanprover-community/mathlib/pull/3964))

### [2020-08-29 14:16:16](https://github.com/leanprover-community/mathlib/commit/faf1df4)
chore(topology/sheaves/sheaf_of_functions): rely less on defeq ([#3972](https://github.com/leanprover-community/mathlib/pull/3972))
This backports some changes from the `prop_limits` branch.

### [2020-08-29 14:16:14](https://github.com/leanprover-community/mathlib/commit/fd4628f)
chore(*): bump to lean 3.19.0c, fin is now a subtype ([#3955](https://github.com/leanprover-community/mathlib/pull/3955))
* Some `decidable.*` order theorems have been moved to core.
* `fin` is now a subtype. 
This means that the whnf of `fin n` is now `{i // i < n}`.
Also, the coercion `fin n → nat` is now preferred over `subtype.val`.
The entire library has been refactored accordingly. (Although I probably missed some cases.)
* `in_current_file'` was removed since the bug in 
`in_current_file` was fixed in core.
* The syntax of `guard_hyp` in core was changed from
`guard_hyp h := t` to `guard_hyp h : t`, so the syntax
for the related `guard_hyp'`, `match_hyp` and
`guard_hyp_strict` tactics in `tactic.interactive` was changed as well.

### [2020-08-29 13:43:16](https://github.com/leanprover-community/mathlib/commit/17c4651)
feat(algebraic_geometry): structure sheaf on Spec R ([#3907](https://github.com/leanprover-community/mathlib/pull/3907))
This defines the structure sheaf on Spec R, following Hartshorne, as a sheaf in `CommRing` on `prime_spectrum R`.
We still need to show at the stalk at a point is just the localization; this is another page of Hartshorne, and will come in a subsequent PR.

### [2020-08-29 11:21:31](https://github.com/leanprover-community/mathlib/commit/84d47a0)
refactor(set_theory/game): make impartial a class ([#3974](https://github.com/leanprover-community/mathlib/pull/3974))
* Misc. style cleanups and code golf
* Changed naming and namespace to adhere more closely to the naming convention
* Changed `impartial` to be a `class`. I am aware that @semorrison explicitly requested not to make `impartial` a class in the [#3855](https://github.com/leanprover-community/mathlib/pull/3855), but after working with the definition a bit I concluded that making it a class is worth it, simply because writing `impartial_add (nim_impartial _) (nim_impartial _)` gets annoying quite quickly, but also because you tend to get goal states of the form `Grundy_value _ = Grundy_value _`. By making `impartial` a class and making the game argument explicit, these goal states look like `grundy_value G = grundy_value H`, which is much nicer to work with.

### [2020-08-29 04:30:09](https://github.com/leanprover-community/mathlib/commit/ea177c2)
feat(analysis/convex): add correspondence between convex cones and ordered semimodules ([#3931](https://github.com/leanprover-community/mathlib/pull/3931))
This shows that a convex cone defines an ordered semimodule and vice-versa.

### [2020-08-29 02:58:36](https://github.com/leanprover-community/mathlib/commit/53275f4)
chore(algebra/group_with_zero): adjust some instance priorities ([#3968](https://github.com/leanprover-community/mathlib/pull/3968))
Use priority 100 for these `extends` instances.

### [2020-08-29 00:44:57](https://github.com/leanprover-community/mathlib/commit/2d3530d)
chore(scripts): update nolints.txt ([#3969](https://github.com/leanprover-community/mathlib/pull/3969))
I am happy to remove some nolints for you!

### [2020-08-28 16:07:49](https://github.com/leanprover-community/mathlib/commit/4ccbb51)
feat(linear_algebra): eigenspaces of linear maps ([#3927](https://github.com/leanprover-community/mathlib/pull/3927))
Add eigenspaces and eigenvalues of linear maps. Add lemma that in a
finite-dimensional vector space over an algebraically closed field,
eigenvalues exist. Add lemma that eigenvectors belonging to distinct
eigenvalues are linearly independent.
This is a rework of [#3864](https://github.com/leanprover-community/mathlib/pull/3864), following Cyril's suggestion. Generalized
eigenspaces will come in a subsequent PR.

### [2020-08-28 15:21:57](https://github.com/leanprover-community/mathlib/commit/1353b7e)
chore(group_theory/perm/sign): speed up proofs ([#3963](https://github.com/leanprover-community/mathlib/pull/3963))
fixes [#3958](https://github.com/leanprover-community/mathlib/pull/3958) 
based on my completely unscientific test methods, this went from 40 seconds to ~~19~~ 17 seconds (on my laptop).
What I've done here is just `squeeze_simp`, but further speedup is definitely possible. Suggestions for what to do with `simp [*, eq_inv_iff_eq] at * <|> cc` are welcome, and should speed this file up a bit more.

### [2020-08-28 14:46:42](https://github.com/leanprover-community/mathlib/commit/d77798a)
doc(representation_theory/maschke): fix latex ([#3965](https://github.com/leanprover-community/mathlib/pull/3965))

### [2020-08-28 14:11:16](https://github.com/leanprover-community/mathlib/commit/31db0bd)
feat(category_theory/limits): add kernel pairs ([#3925](https://github.com/leanprover-community/mathlib/pull/3925))
Add a subsingleton data structure expressing that a parallel pair of morphisms is a kernel pair of a given morphism.
Another PR from my topos project. A pretty minimal API since I didn't need much there - I also didn't introduce anything like `has_kernel_pairs` largely because I didn't need it, but also because I don't know that it's useful for anyone, and it might conflict with ideas in the prop-limits branch.

### [2020-08-28 10:25:09](https://github.com/leanprover-community/mathlib/commit/a08fb2f)
feat(tactic/congr): additions to the congr' tactic ([#3936](https://github.com/leanprover-community/mathlib/pull/3936))
This PR gives a way to apply `ext` after `congr'`.
`congr' 3 with x y : 2` is a new notation for `congr' 3; ext x y : 2`.
New tactic `rcongr` that recursively keeps applying `congr'` and `ext`.
Move `congr'` and every tactic depending on it from `tactic/interactive` to a new file `tactic/congr`.
The original `tactic.interactive.congr'` is now best called as `tactic.congr'`. 
Other than the tactics `congr'` and `rcongr` no tactics have been (essentially) changed.

### [2020-08-28 07:24:16](https://github.com/leanprover-community/mathlib/commit/ceacf54)
feat(category_theory/filtered): filtered categories, and filtered colimits in `Type` ([#3960](https://github.com/leanprover-community/mathlib/pull/3960))
This is some work @rwbarton did last year. I've merged master, written some comments, and satisfied the linter.

### [2020-08-28 05:18:40](https://github.com/leanprover-community/mathlib/commit/513f740)
feat(topology/sheaves): checking the sheaf condition under a forgetful functor ([#3609](https://github.com/leanprover-community/mathlib/pull/3609))
# Checking the sheaf condition on the underlying presheaf of types.
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.
The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.
## References
* https://stacks.math.columbia.edu/tag/0073

### [2020-08-28 03:16:37](https://github.com/leanprover-community/mathlib/commit/7e6393f)
feat(topology/sheaves): the sheaf condition for functions satisfying a local predicate ([#3906](https://github.com/leanprover-community/mathlib/pull/3906))
Functions satisfying a local predicate form a sheaf.
This sheaf has a natural map from the stalk to the original fiber, and we give conditions for this map to be injective or surjective.

### [2020-08-27 20:30:40](https://github.com/leanprover-community/mathlib/commit/eaaac99)
feat(geometry/euclidean/basic): reflection ([#3932](https://github.com/leanprover-community/mathlib/pull/3932))
Define the reflection of a point in an affine subspace, as a bundled
isometry, in terms of the orthogonal projection onto that subspace,
and prove some basic lemmas about it.

### [2020-08-27 18:31:26](https://github.com/leanprover-community/mathlib/commit/359261e)
feat(data/nat): commutativity of bitwise operations ([#3956](https://github.com/leanprover-community/mathlib/pull/3956))

### [2020-08-27 14:44:42](https://github.com/leanprover-community/mathlib/commit/6b556cf)
feat(combinatorics/adjacency_matrix): defines adjacency matrices of simple graphs ([#3672](https://github.com/leanprover-community/mathlib/pull/3672))
defines the adjacency matrix of a simple graph
proves lemmas about adjacency matrix that will form the bulk of the proof of the friendship theorem (freek 83)

### [2020-08-27 06:25:31](https://github.com/leanprover-community/mathlib/commit/ea9bf31)
refactor(analysis/normed_space/real_inner_product,geometry/euclidean): orthogonal projection hypotheses ([#3952](https://github.com/leanprover-community/mathlib/pull/3952))
As advised by Patrick in [#3932](https://github.com/leanprover-community/mathlib/pull/3932), define `orthogonal_projection` (for
both real inner product spaces and Euclidean affine spaces) without
taking hypotheses of the subspace being nonempty and complete,
defaulting to the identity map if those conditions are not satisfied,
so making `orthogonal_projection` more convenient to use with those
properties only being needed on lemmas but not simply to refer to the
orthogonal projection at all.
The hypotheses are removed from lemmas that don't need them because
they are still true with the identity map.  Some `nonempty` hypotheses
are also removed where they follow from another hypothesis that gives
a point or a nonempty set of points in the subspace.
The unbundled `orthogonal_projection_fn` that's used only to prove
properties needed to define a bundled linear or affine map still takes
the original hypotheses, then a bundled map taking those hypotheses is
defined under a new name, then that map is used to define plain
`orthogonal_projection` which does not take any of those hypotheses
and is the version expected to be used in all lemmas after it has been
defined.

### [2020-08-27 00:47:46](https://github.com/leanprover-community/mathlib/commit/5627aed)
chore(scripts): update nolints.txt ([#3954](https://github.com/leanprover-community/mathlib/pull/3954))
I am happy to remove some nolints for you!

### [2020-08-26 20:24:56](https://github.com/leanprover-community/mathlib/commit/c147894)
feat(data/fin): flesh out API for fin ([#3769](https://github.com/leanprover-community/mathlib/pull/3769))
Provide more API for `fin n`. Lemma names chosen to match equivalent lemmas in `nat`. Does not develop docstrings for the lemmas.
New lemmas:
iff lemmas for comparison
`ne_iff_vne`
`eq_mk_iff_coe_eq`
`succ_le_succ_iff`
`succ_lt_succ_iff`
lemmas about explicit numerals
`val_zero'`
`mk_zero`
`mk_one`
`mk_bit0`
`mk_bit1`
`cast_succ_zero`
`succ_zero_eq_one`
`zero_ne_one`
`pred_one`
lemmas about order
`zero_le`
`succ_pos`
`mk_succ_pos`
`one_pos`
`one_lt_succ_succ`
`succ_succ_ne_one`
`pred_mk_succ`
`cast_succ_lt_last`
`cast_succ_lt_succ`
`lt_succ`
`last_pos`
`le_coe_last`
coe lemmas:
`coe_eq_cast_succ`
`coe_succ_eq_succ`
`coe_nat_eq_last`
succ_above API:
`succ_above_below`
`succ_above_zero`
`succ_above_last`
`succ_above_above`
`succ_above_pos`
addition API:
`add_one_pos`
`pred_add_one`
Co-authored by: Yury Kudryashov urkud@ya.ru

### [2020-08-26 18:55:44](https://github.com/leanprover-community/mathlib/commit/26dfea5)
feat(algebra/big_operators): sum of two products ([#3944](https://github.com/leanprover-community/mathlib/pull/3944))

### [2020-08-26 18:55:42](https://github.com/leanprover-community/mathlib/commit/64aad5b)
feat(category_theory/adjunction): uniqueness of adjunctions ([#3940](https://github.com/leanprover-community/mathlib/pull/3940))
Co-authored by @thjread

### [2020-08-26 18:55:40](https://github.com/leanprover-community/mathlib/commit/080746f)
feat(algebra/category/*/limits): don't rely on definitions ([#3873](https://github.com/leanprover-community/mathlib/pull/3873))
This is a second attempt (which works **much** better) at [#3860](https://github.com/leanprover-community/mathlib/pull/3860), after @TwoFX explained how to do it properly.
This PR takes the constructions of limits in the concrete categories `(Add)(Comm)[Mon|Group]`, `(Comm)(Semi)Ring`, `Module R`, and `Algebra R`, and makes sure that they never rely on the actual definitions of limits in "prior" categories.
Of course, at this stage the `has_limit` typeclasses still contain data, so it's hard to judge whether we're really not relying on the definitions. I've marked all the `has_limits` instances in these files as irreducible, but the real proof is just that this same code is working over on the `prop_limits` branch.

### [2020-08-26 17:53:30](https://github.com/leanprover-community/mathlib/commit/2d9ab61)
feat(ring_theory/ideal/basic): R/I is an ID iff I is prime ([#3951](https://github.com/leanprover-community/mathlib/pull/3951))
`is_integral_domain_iff_prime (I : ideal α) : is_integral_domain I.quotient ↔ I.is_prime`

### [2020-08-26 16:20:07](https://github.com/leanprover-community/mathlib/commit/2b6924d)
feat(topology/algebra/ordered): conditions for a strictly monotone function to be a homeomorphism ([#3843](https://github.com/leanprover-community/mathlib/pull/3843))
If a strictly monotone function between linear orders is surjective, it is a homeomorphism.
If a strictly monotone function between conditionally complete linear orders is continuous, and tends to `+∞` at `+∞` and to `-∞` at `-∞`, then it is a homeomorphism.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Order.20topology)
Co-authored by: Yury Kudryashov <urkud@ya.ru>

### [2020-08-26 14:45:52](https://github.com/leanprover-community/mathlib/commit/f4f0854)
feat(ring_theory/bundled_subring): add bundled subrings ([#3886](https://github.com/leanprover-community/mathlib/pull/3886))

### [2020-08-26 14:45:50](https://github.com/leanprover-community/mathlib/commit/0d67a02)
feat(ring_theory/noetherian): maximal among set iff Noetherian ([#3846](https://github.com/leanprover-community/mathlib/pull/3846))
Main theorem is `set_has_maximal_iff_noetherian,` which relates well foundedness of `<` to being noetherian.
Most notably a result of
`well_founded.well_founded_iff_has_max'` provides the fact that on a partial ordering, `well_founded >` is equivalent to each nonempty set having a maximal element.
`well_founded.well_founded_iff_has_min` provides an analogous fact for `well_founded <`.
Some other miscellaneous lemmas are as follows
`localization_map.integral_domain_of_local_at_prime` is the localization of an integral domain at a prime's complement is an integral domain
`ideal.mul_eq_bot` is the fact that in an integral domain if I*J = 0, then at least one is 0.
`submodule.nonzero_mem_of_gt_bot` is that if ⊥ < J, then J has a nonzero member.
`lt_add_iff_not_mem` is that b is not a member of J iff J < J+(b).
`bot_prime` states that 0 is a prime ideal of an integral domain.

### [2020-08-26 13:12:40](https://github.com/leanprover-community/mathlib/commit/187bfa5)
feat(set/basic): additions to prod ([#3943](https://github.com/leanprover-community/mathlib/pull/3943))
Also add one lemma about `Inter`.

### [2020-08-26 13:12:38](https://github.com/leanprover-community/mathlib/commit/fb6046e)
feat(*/category/*): add coe_of simp lemmas ([#3938](https://github.com/leanprover-community/mathlib/pull/3938))

### [2020-08-26 11:39:01](https://github.com/leanprover-community/mathlib/commit/206673e)
chore(*): trivial golfing using dec_trivial tactic ([#3949](https://github.com/leanprover-community/mathlib/pull/3949))

### [2020-08-26 10:32:55](https://github.com/leanprover-community/mathlib/commit/dd742dc)
feat(finsupp/basic): add hom_ext ([#3941](https://github.com/leanprover-community/mathlib/pull/3941))
Two R-module homs from finsupp X R which agree on `single x 1` agree everywhere.
```
lemma hom_ext [semiring β] [add_comm_monoid γ] [semimodule β γ] (φ ψ : (α →₀ β) →ₗ[β] γ)
  (h : ∀ a : α, φ (single a 1) = ψ (single a 1)) : φ = ψ
```

### [2020-08-26 09:56:27](https://github.com/leanprover-community/mathlib/commit/a31096d)
fix(set_theory/game): remove stray #lint introduced in [#3939](https://github.com/leanprover-community/mathlib/pull/3939) ([#3948](https://github.com/leanprover-community/mathlib/pull/3948))

### [2020-08-26 00:44:38](https://github.com/leanprover-community/mathlib/commit/da47548)
chore(scripts): update nolints.txt ([#3945](https://github.com/leanprover-community/mathlib/pull/3945))
I am happy to remove some nolints for you!

### [2020-08-25 19:52:43](https://github.com/leanprover-community/mathlib/commit/666a2e2)
feat(algebra/group/with_one): more API for with_zero ([#3716](https://github.com/leanprover-community/mathlib/pull/3716))

### [2020-08-25 16:55:18](https://github.com/leanprover-community/mathlib/commit/4478719)
feat(data/padic/padic_integers): homs to zmod(p ^ n) ([#3882](https://github.com/leanprover-community/mathlib/pull/3882))
This is the next PR in a series of PRs on the padic numbers/integers that should culminate in a proof that Z_p is isomorphic to the ring of Witt vectors of zmod p.
In this PR we build ring homs from Z_p to zmod (p ^ n).

### [2020-08-25 14:36:42](https://github.com/leanprover-community/mathlib/commit/b03ce61)
chore(set_theory/game): various cleanup and code golf ([#3939](https://github.com/leanprover-community/mathlib/pull/3939))

### [2020-08-25 14:36:40](https://github.com/leanprover-community/mathlib/commit/878c44f)
feat(category_theory/adjunction): restrict adjunction to full subcategory ([#3924](https://github.com/leanprover-community/mathlib/pull/3924))
Blocked by [#3923](https://github.com/leanprover-community/mathlib/pull/3923).

### [2020-08-25 13:04:30](https://github.com/leanprover-community/mathlib/commit/a5a9858)
feat(data/sigma/basic): cleanup ([#3933](https://github.com/leanprover-community/mathlib/pull/3933))
Use namespaces
Add `sigma.ext_iff`, `psigma.ext` and `sigma.ext_iff`

### [2020-08-25 12:10:39](https://github.com/leanprover-community/mathlib/commit/3409388)
doc(ring_theory/*): add some module docstrings ([#3880](https://github.com/leanprover-community/mathlib/pull/3880))

### [2020-08-24 23:25:19](https://github.com/leanprover-community/mathlib/commit/d4d33de)
feat(combinatorics): define simple graphs ([#3458](https://github.com/leanprover-community/mathlib/pull/3458))
adds basic definition of `simple_graph`s

### [2020-08-24 19:17:49](https://github.com/leanprover-community/mathlib/commit/8af1579)
refactor(geometry/euclidean): split up file ([#3926](https://github.com/leanprover-community/mathlib/pull/3926))
Split up `geometry/euclidean.lean` into four smaller files in
`geometry/euclidean`.  There should be no changes to any of the
individual definitions, or to the set of definitions present, but
module doc strings have been expanded.
Various definitions in `geometry/euclidean/basic.lean` are not used by
all the other files, so it would be possible to split it up further,
but that doesn't seem necessary for now, and more of those things may
be used by more other files in future.  (For example,
`geometry/euclidean/circumcenter.lean` doesn't make any use of angles
at present.  But a version of the law of sines involving the
circumradius would naturally go in
`geometry/euclidean/circumcenter.lean`, and would introduce such a
dependency.)

### [2020-08-24 16:57:27](https://github.com/leanprover-community/mathlib/commit/1404ad8)
feat(algebra/add_torsor): vsub_vadd_comm ([#3928](https://github.com/leanprover-community/mathlib/pull/3928))
Add another (commutative) `add_torsor` rearrangement lemma.

### [2020-08-24 16:23:09](https://github.com/leanprover-community/mathlib/commit/96b559c)
feat(set_theory/game): grundy number of single-heap nim ([#3930](https://github.com/leanprover-community/mathlib/pull/3930))

### [2020-08-24 01:55:42](https://github.com/leanprover-community/mathlib/commit/1ccdbb9)
feat(category_theory/images): unique image ([#3921](https://github.com/leanprover-community/mathlib/pull/3921))
Show that the strong-epi mono factorisation of a morphism is unique.

### [2020-08-24 01:55:40](https://github.com/leanprover-community/mathlib/commit/685d9dd)
feat(category_theory): cancel fully faithful functor ([#3920](https://github.com/leanprover-community/mathlib/pull/3920))
Construct the natural isomorphism between `F` and `G` given a natural iso between `F ⋙ H` and `G ⋙ H` for a fully faithful `H`.

### [2020-08-24 01:00:11](https://github.com/leanprover-community/mathlib/commit/ebd3351)
chore(category_theory/conj): add a new simp lemma ([#3922](https://github.com/leanprover-community/mathlib/pull/3922))
Mark a new simp lemma which I think is helpful and simplify some proofs using it.

### [2020-08-24 01:00:09](https://github.com/leanprover-community/mathlib/commit/f230409)
feat(category_theory/adjunction): opposite adjunctions ([#3899](https://github.com/leanprover-community/mathlib/pull/3899))
Add two constructions for adjoints for opposite functors.

### [2020-08-24 01:00:07](https://github.com/leanprover-community/mathlib/commit/bfc8c66)
feat(category_theory/limits/shapes/finite*): finite limits from limits ([#3800](https://github.com/leanprover-community/mathlib/pull/3800))
Add some missing derivations in the new has_limits hierarchy

### [2020-08-23 23:56:34](https://github.com/leanprover-community/mathlib/commit/bf6cd28)
feat(category_theory/fully_faithful): equivalence of homsets ([#3923](https://github.com/leanprover-community/mathlib/pull/3923))
I was *so sure* I'd already made this PR but I can't find it nor this construction, so here it is.

### [2020-08-23 16:22:06](https://github.com/leanprover-community/mathlib/commit/7d4f773)
feat(ring_theory/jacobson): Proof that if a ring is a Jacobson Ring then so is its localization at a single element ([#3651](https://github.com/leanprover-community/mathlib/pull/3651))
The main result here is that the localization of a Jacobson ring to a single element is also a Jacobson ring, which is one of the things needed for the proof that `R` is Jacobson if and only if `R[x]` is Jacobson.
Two characterization of Jacobson rings in terms of their quotient rings are also included, again needed to prove `R[x]` is Jacobson.

### [2020-08-23 15:35:50](https://github.com/leanprover-community/mathlib/commit/e216755)
feat(linear_algebra/affine_space): more lemmas ([#3918](https://github.com/leanprover-community/mathlib/pull/3918))
Add some more affine space lemmas.  In particular, this includes
lemmas about the dimension of the span of a finite affinely
independent family.

### [2020-08-23 14:51:36](https://github.com/leanprover-community/mathlib/commit/d80f3ef)
feat(geometry/euclidean): Monge point and orthocenter ([#3872](https://github.com/leanprover-community/mathlib/pull/3872))
The main purpose of this PR is to define the orthocenter of a
triangle.
Simplices in more than two dimensions do not in general have an
orthocenter: the altitudes are not necessarily concurrent.  However,
there is a n-dimensional generalization of the orthocenter in the form
of the Monge point of a simplex.  Define a Monge plane to be an
(n-1)-dimensional subspace that passes through the centroid of an
(n-2)-dimensional face of the simplex and is orthogonal to the
opposite edge.  Then the Monge planes of a simplex are always
concurrent, and their point of concurrence is known as the Monge point
of the simplex.  Furthermore, the circumcenter O, centroid G and Monge
point M are collinear in that order on the Euler line, with OG : GM =
(n-1) : 2.
Here, we use that ratio as a convenient way to define the Monge point
in terms of the existing definitions of the circumcenter and the
centroid.  First we set up some infrastructure for dealing with affine
combinations of the vertices of a simplex together with its
circumcenter, which can be convenient for computations rather than
dealing with combinations of the vertices alone; the use of an
inductive type `points_with_circumcenter_index` seemed to be more
convenient than other options for how to index such combinations.
Then, a straightforward calculation using `inner_weighted_vsub` shows
that the point defined in terms of the circumcenter and the centroid
does indeed lie in the Monge planes, so justifying the definition as
being a definition of the Monge point.  It is then shown to be the
only point in that intersection (in fact, the only point in the
intersection of all the Monge planes where one of the two vertices
needed to specify a Monge plane is fixed).
The altitudes of a simplex are then defined.  In the case of a
triangle, the orthocenter is defined to be the Monge point, the
altitudes are shown to equal the Monge planes (mathematically trivial,
but involves quite a bit of fiddling around with `fin 3`) and thus the
orthocenter is shown to lie in the altitudes and to be the unique
point lying in any two of them (again, involves various fiddling
around with `fin 3` to link up with the previous lemmas).  Because of
the definition chosen for the Monge point, the position of the
orthocenter on the Euler line of the triangle comes for free (not
quite `rfl`, but two rewrites of `rfl` lemmas plus `norm_num`).

### [2020-08-23 13:21:25](https://github.com/leanprover-community/mathlib/commit/588e46c)
feat(tactic/*,meta/expr): refactor and extend binder matching functions ([#3830](https://github.com/leanprover-community/mathlib/pull/3830))
This PR deals with meta functions that deconstruct expressions starting
with pi or lambda binders. Core defines `mk_local_pis` to deconstruct pi
binders and `tactic.core` used to contain some ad-hoc variations of its
functionality. This PR unifies all these variations and adds several
more, for both pi and lambda binders. Specifically:
- We remove `mk_local_pis_whnf`. Use `whnf e md >>= mk_local_pis` instead.
  Note: we reuse the name for another function with different semantics;
  see below.
- We add `mk_{meta,local}_{pis,lambdas}`, `mk_{meta,local}_{pis,lambdas}n`,
  `mk_{meta,local}_{pis,lambdas}_whnf`, `mk_{meta,local}_{pis,lambdas}n_whnf`.
  These can all be used to 'open' a pi or lambda binder. The binder is
  instantiated with a fresh local for the `local` variants and a fresh
  metavariable for the `meta` variants. The `whnf` variants normalise
  the input expression before checking for leading binders. The
  `{pis,lambdas}n` variants match a given number of leading binders.
  Some of these functions were already defined, but we now implement
  them in terms of a new function, `mk_binders`, which abstracts over
  the common functionality.
- We rename `get_pi_binders_dep` to `get_pi_binders_nondep`. This function returns
  the nondependent binders, so the old name was misleading.
- We add `expr.match_<C>` for every constructor `C` of `expr`. `match_pi`
  and `match_lam` are needed to implement the `mk_*` functions; the
  other functions are added for completeness.
- (Bonus) We add `get_app_fn_args_whnf` and `get_app_fn_whnf`. These are variants
  of `get_app_fn_args` and `get_app_fn`, respectively, which normalise the input
  expression as necessary.
The refactoring might be a slight performance regression because the new
implementation adds some indirection. But the affected functions aren't
widely used anyway and I suspect that the performance loss is very
minor, so having clearer and more concise code is probably worth it.

### [2020-08-23 12:27:41](https://github.com/leanprover-community/mathlib/commit/ffd8626)
refactor(linear_algebra/affine_space/basic): make more arguments of smul_vsub_vadd_mem implicit ([#3917](https://github.com/leanprover-community/mathlib/pull/3917))
Came up in [#3872](https://github.com/leanprover-community/mathlib/pull/3872).

### [2020-08-23 06:36:27](https://github.com/leanprover-community/mathlib/commit/7d88a30)
fix(data/sigma/basic): rename `ext` to `sigma.ext` ([#3916](https://github.com/leanprover-community/mathlib/pull/3916))

### [2020-08-23 05:18:43](https://github.com/leanprover-community/mathlib/commit/ff97055)
feat(data/finset/basic): insert_singleton_comm ([#3914](https://github.com/leanprover-community/mathlib/pull/3914))
Add the result that `({a, b} : finset α) = {b, a}`.  This came up in
[#3872](https://github.com/leanprover-community/mathlib/pull/3872), and `library_search` does not show it as already present.

### [2020-08-23 02:34:47](https://github.com/leanprover-community/mathlib/commit/7ac7246)
feat(linear_algebra/finite_dimensional): Add `linear_equiv.of_inj_endo` and related lemmas ([#3878](https://github.com/leanprover-community/mathlib/pull/3878))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move the section `zero_dim` up.
* Add several lemmas about finite dimensional vector spaces. The only new definition is `linear_equiv.of_injective_endo`, which produces a linear equivalence from an injective endomorphism.

### [2020-08-22 18:09:38](https://github.com/leanprover-community/mathlib/commit/abe4459)
feat(analysis/convex): define concavity of functions ([#3849](https://github.com/leanprover-community/mathlib/pull/3849))

### [2020-08-22 15:14:00](https://github.com/leanprover-community/mathlib/commit/9e9b380)
doc(algebra/linear_recurrence): fix a mistake in module docstring ([#3911](https://github.com/leanprover-community/mathlib/pull/3911))

### [2020-08-22 15:13:58](https://github.com/leanprover-community/mathlib/commit/65ceb00)
fix(topology): simplify proof of Heine-Cantor ([#3910](https://github.com/leanprover-community/mathlib/pull/3910))

### [2020-08-22 14:33:36](https://github.com/leanprover-community/mathlib/commit/6a85278)
feat(data/polynomial/eval): eval_finset.prod ([#3903](https://github.com/leanprover-community/mathlib/pull/3903))
Evaluating commutes with finset.prod; useful in a variety of situations in numerical analysis.

### [2020-08-22 13:26:57](https://github.com/leanprover-community/mathlib/commit/aca785a)
feat(linear_algebra): linear_equiv_matrix lemmas ([#3898](https://github.com/leanprover-community/mathlib/pull/3898))
From the sphere eversion project, with help by Anne for the crucial `linear_equiv_matrix_apply`.

### [2020-08-22 12:32:20](https://github.com/leanprover-community/mathlib/commit/e9d1067)
feat(category_theory/opposites): isomorphism of opposite functor ([#3901](https://github.com/leanprover-community/mathlib/pull/3901))
Get some lemmas generated by `simps` and add two isomorphisms for opposite functors.

### [2020-08-22 10:07:23](https://github.com/leanprover-community/mathlib/commit/011a262)
feat(set_theory/game): impartial games and the Sprague-Grundy theorem ([#3855](https://github.com/leanprover-community/mathlib/pull/3855))

### [2020-08-22 09:35:08](https://github.com/leanprover-community/mathlib/commit/e546e94)
fix(data/equiv/transfer_instance): remove stray #lint ([#3908](https://github.com/leanprover-community/mathlib/pull/3908))

### [2020-08-22 06:31:00](https://github.com/leanprover-community/mathlib/commit/13881d7)
feat(tactic/dec_trivial): make dec_trivial easier to use ([#3875](https://github.com/leanprover-community/mathlib/pull/3875))

### [2020-08-22 04:56:48](https://github.com/leanprover-community/mathlib/commit/83db96b)
feat(algebra/group/with_one): make with_one and with_zero irreducible. ([#3883](https://github.com/leanprover-community/mathlib/pull/3883))

### [2020-08-22 01:22:48](https://github.com/leanprover-community/mathlib/commit/4b24166)
chore(scripts): update nolints.txt ([#3905](https://github.com/leanprover-community/mathlib/pull/3905))
I am happy to remove some nolints for you!

### [2020-08-22 00:21:09](https://github.com/leanprover-community/mathlib/commit/278f512)
feat(data/real): define the golden ratio and its conjugate, prove irrationality of both and Binet's formula ([#3885](https://github.com/leanprover-community/mathlib/pull/3885))
Co-authored by @alreadydone and @monadius through their solutions to the corresponding Codewars Kata.

### [2020-08-21 22:13:24](https://github.com/leanprover-community/mathlib/commit/9998bee)
chore(measure_theory/*): remove some `measurable f` arguments ([#3902](https://github.com/leanprover-community/mathlib/pull/3902))

### [2020-08-21 20:49:40](https://github.com/leanprover-community/mathlib/commit/4c04f0b)
feat(topology/algebra/ordered): sum of functions with limits at_top and cst ([#3833](https://github.com/leanprover-community/mathlib/pull/3833))
Two functions which tend to `at_top` have sum tending to `at_top`.  Likewise if one tends to `at_top` and one tends to a constant.
Also made a couple of edits relating to [this conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ordered.20groups.20have.20no.20top.20element) about `no_top` for algebraic structures:

### [2020-08-21 19:07:51](https://github.com/leanprover-community/mathlib/commit/1db32c5)
feat(set/basic): some results about `set.pi` ([#3894](https://github.com/leanprover-community/mathlib/pull/3894))
New definition: `function.eval`
Also some changes in `set.basic`
Name changes:
```
pi_empty_index -> empty_pi
pi_insert_index -> insert_pi
pi_singleton_index -> singleton_pi
set.push_pull -> image_inter_preimage
set.push_pull' -> image_preimage_inter
```

### [2020-08-21 18:31:42](https://github.com/leanprover-community/mathlib/commit/0c7ac83)
feat(measure_theory/bochner_integration): add `integral_smul_measure` ([#3900](https://github.com/leanprover-community/mathlib/pull/3900))
Also add `integral_dirac`

### [2020-08-21 16:04:55](https://github.com/leanprover-community/mathlib/commit/ac56790)
feat(order/rel_iso): a new definition of order_iso, using preorder instances ([#3838](https://github.com/leanprover-community/mathlib/pull/3838))
defines (new) `order_embedding` and `order_iso`, which map both < and <=
replaces existing `rel_embedding` and `rel_iso` instances preserving < or <= with the new abbreviations

### [2020-08-21 13:01:05](https://github.com/leanprover-community/mathlib/commit/e3409c6)
feat(data/zmod/basic): morphisms to zmod are surjective (deps: [#3888](https://github.com/leanprover-community/mathlib/pull/3888)) ([#3889](https://github.com/leanprover-community/mathlib/pull/3889))
... and determined by their kernel

### [2020-08-21 11:41:54](https://github.com/leanprover-community/mathlib/commit/4921be9)
feat(analysis/special_functions/arsinh): inverse hyperbolic sine function ([#3801](https://github.com/leanprover-community/mathlib/pull/3801))
Added the following lemmas and definitions:
`cosh_def`
`sinh_def`
`cosh_pos`
`sinh_strict_mono`
`sinh_injective`
`sinh_surjective`
`sinh_bijective`
`real.cosh_sq_sub_sinh_sq`
`sqrt_one_add_sinh_sq`
`sinh_arsinh`
`arsinh_sin`
This is from the list of UG not in lean. `cosh` coming soon.

### [2020-08-21 10:07:49](https://github.com/leanprover-community/mathlib/commit/7a48761)
feat(logic/function): left/right inverse iff ([#3897](https://github.com/leanprover-community/mathlib/pull/3897))
From the sphere eversion project.

### [2020-08-21 10:07:47](https://github.com/leanprover-community/mathlib/commit/de20a39)
feat(group_theory/subroup,ring_theory/ideal/operations): lift_of_surjective ([#3888](https://github.com/leanprover-community/mathlib/pull/3888))
Surjective homomorphisms behave like quotient maps

### [2020-08-21 10:07:46](https://github.com/leanprover-community/mathlib/commit/045b6c7)
chore(topology/basic): use dot notation ([#3861](https://github.com/leanprover-community/mathlib/pull/3861))
## API changes
* add `set.range_sigma_mk`, `finset.sigma_preimage_mk`, `finset.sigma_preimage_mk_of_subset`,
  `finset.sigma_image_fst_preimage_mk`, `finset.prod_preimage'`;
* rename `filter.monotone.tendsto_at_top_finset` to `filter.tendsto_at_top_finset_of_monotone`,
  add alias `monotone.tendsto_at_top_finset`;
* add `filter.tendsto_finset_preimage_at_top_at_top`;
* add `filter.tendsto.frequently`;
* add `cluster_pt_principal_iff_frequently`, `mem_closure_iff_frequently`, `filter.frequently.mem_closure`,
  `filter.frequently.mem_of_closed`, `is_closed.mem_of_frequently_of_tendsto`;
* rename `mem_of_closed_of_tendsto` to `is_closed.mem_of_tendsto`;
* delete `mem_of_closed_of_tendsto'`; use new `is_closed.mem_of_frequently_of_tendsto` instead;

### [2020-08-21 10:07:44](https://github.com/leanprover-community/mathlib/commit/d8cde2a)
feat(measure_theory/interval_integral): more versions of FTC-1 ([#3709](https://github.com/leanprover-community/mathlib/pull/3709))
Left/right derivative, strict derivative, differentiability in both endpoints.
Other changes:
* rename `filter.tendsto_le_left` and `filter.tendsto_le_right` to `filter.tendsto.mono_left` and `filter.tendsto.mono_right`, swap arguments;
* rename `order_top.tendsto_at_top` to `order_top.tendsto_at_top_nhds`;
* introduce `tendsto_Ixx_class` instead of `is_interval_generated`.

### [2020-08-21 08:35:09](https://github.com/leanprover-community/mathlib/commit/bc3e835)
feat(tactic/rcases): clear pattern `-` in rcases ([#3868](https://github.com/leanprover-community/mathlib/pull/3868))
This allows you to write:
```lean
example (h : ∃ x : ℕ, true) : true :=
begin
  rcases h with ⟨x, -⟩,
  -- x : ℕ |- true
end
```
to clear unwanted hypotheses. Note that dependents are also cleared,
meaning that you can get into trouble if you try to keep matching when a
variable later in the pattern is deleted. The `_` pattern will match
a hypothesis even if it has been deleted, so this is the recommended way
to match on variables dependent on a deleted hypothesis.
You can use `-` if you prefer, but watch out for unintended variables
getting deleted if there are duplicate names!

### [2020-08-21 07:33:42](https://github.com/leanprover-community/mathlib/commit/da6cd55)
feat(determinant): towards multilinearity ([#3887](https://github.com/leanprover-community/mathlib/pull/3887))
From the sphere eversion project. In a PR coming soon, this will be used to prove that the determinant of a family of vectors in a given basis is multi-linear (see [here](https://github.com/leanprover-community/sphere-eversion/blob/2c776f6a92c0f9babb521a02ab0cc341a06d3f3c/src/vec_det.lean) for a preview if needed).

### [2020-08-21 05:29:48](https://github.com/leanprover-community/mathlib/commit/23749aa)
chore(measure_theory/*): use `_measure` instead of `_meas` ([#3892](https://github.com/leanprover-community/mathlib/pull/3892))

### [2020-08-21 03:53:31](https://github.com/leanprover-community/mathlib/commit/31cd6dd)
chore(order/bounded_lattice): use `⦃⦄` in `disjoint.symm` ([#3893](https://github.com/leanprover-community/mathlib/pull/3893))

### [2020-08-21 02:24:33](https://github.com/leanprover-community/mathlib/commit/1719035)
feat(category_theory/monad/*): Add category of bundled (co)monads; prove equivalence of monads with monoid objects ([#3762](https://github.com/leanprover-community/mathlib/pull/3762))
This PR constructs bundled monads, and proves the "usual" equivalence between the category of monads and the category of monoid objects in the endomorphism category.
It also includes a definition of morphisms of unbundled monads, and proves some necessary small lemmas in the following two files:
1. `category_theory.functor_category`
2. `category_theory.monoidal.internal`
Given any isomorphism in `Cat`, we construct a corresponding equivalence of categories in `Cat.equiv_of_iso`.

### [2020-08-21 01:44:02](https://github.com/leanprover-community/mathlib/commit/7271f74)
chore(scripts): update nolints.txt ([#3891](https://github.com/leanprover-community/mathlib/pull/3891))
I am happy to remove some nolints for you!

### [2020-08-21 00:08:35](https://github.com/leanprover-community/mathlib/commit/0a48f0a)
feat(system/random): a monad for (pseudo-)randomized computations ([#3742](https://github.com/leanprover-community/mathlib/pull/3742))

### [2020-08-20 23:05:44](https://github.com/leanprover-community/mathlib/commit/36386fc)
feat(linear_algebra): some easy linear map/equiv lemmas ([#3890](https://github.com/leanprover-community/mathlib/pull/3890))
From the sphere eversion project.

### [2020-08-20 21:33:51](https://github.com/leanprover-community/mathlib/commit/c9704ff)
chore(data/matrix, linear_algebra): generalize universe parameters ([#3879](https://github.com/leanprover-community/mathlib/pull/3879))
@PatrickMassot was complaining that `matrix m n R` often doesn't work when the parameters are declared as `m n : Type*` because the universe parameters were equal. This PR makes the universe parameters of `m` and `n` distinct where possible, also generalizing some other linear algebra definitions.
The types of `col` and `row` used to be `matrix n punit` but are now `matrix n unit`, otherwise the elaborator can't figure out the universe. This doesn't seem to break anything except for the cases where `punit.{n}` was explicitly written down.
There were some breakages, but the total amount of changes is not too big.

### [2020-08-20 21:33:49](https://github.com/leanprover-community/mathlib/commit/901c5bc)
feat(ring_theory/separable): a separable polynomial splits into a product of unique `X - C a` ([#3877](https://github.com/leanprover-community/mathlib/pull/3877))
Bonus result: the degree of a separable polynomial is the number of roots
in the field where it splits.

### [2020-08-20 21:33:47](https://github.com/leanprover-community/mathlib/commit/9f525c7)
chore(category_theory/limits/types): cleanup ([#3871](https://github.com/leanprover-community/mathlib/pull/3871))
Backporting some cleaning up work from `prop_limits`, while it rumbles onwards.

### [2020-08-20 16:50:10](https://github.com/leanprover-community/mathlib/commit/7a93d87)
doc(src/ring_theory/integral_domain.lean): add module docstring ([#3881](https://github.com/leanprover-community/mathlib/pull/3881))

### [2020-08-20 11:47:20](https://github.com/leanprover-community/mathlib/commit/4631018)
feat(data/polynomial): Add polynomial/eval lemmas ([#3876](https://github.com/leanprover-community/mathlib/pull/3876))
Add some lemmas about `polynomial`. In particular, add lemmas about
`eval2` for the case that the ring `S` that we evaluate into is
non-commutative.

### [2020-08-20 08:43:40](https://github.com/leanprover-community/mathlib/commit/e174f42)
feat(equiv/transfer_instances): other algebraic structures ([#3870](https://github.com/leanprover-community/mathlib/pull/3870))
Some updates to `data.equiv.transfer_instances`.
1. Use `@[to_additive]`
2. Add algebraic equivalences between the original and transferred instances.
3. Transfer modules and algebras.

### [2020-08-20 08:43:38](https://github.com/leanprover-community/mathlib/commit/d7621b9)
feat(data/list/basic): lemmas about foldr/foldl ([#3865](https://github.com/leanprover-community/mathlib/pull/3865))
This PR prepares [#3864](https://github.com/leanprover-community/mathlib/pull/3864).
* Move lemmas about `foldr`/`foldl` into the appropriate section.
* Add variants of the `foldl_map`/`foldr_map` lemmas.
* Add lemmas stating that a fold over a list of injective functions is injective.

### [2020-08-20 08:00:59](https://github.com/leanprover-community/mathlib/commit/ba06edc)
chore(data/complex/module): move `linear_map.{re,im,of_real}` from `analysis` ([#3874](https://github.com/leanprover-community/mathlib/pull/3874))
I'm going to use these `def`s in `analysis/convex/basic`, and I don't
want to `import analysis.normed_space.basic` there.

### [2020-08-20 06:10:17](https://github.com/leanprover-community/mathlib/commit/34db3c3)
feat(order/category): various categories of ordered types ([#3841](https://github.com/leanprover-community/mathlib/pull/3841))
This is a first step towards the category of simplicial sets (which are presheaves on the category of nonempty finite linear orders).

### [2020-08-20 03:32:46](https://github.com/leanprover-community/mathlib/commit/4364798)
fix(data/fin): better defeqs in fin.has_le instance ([#3869](https://github.com/leanprover-community/mathlib/pull/3869))
This ensures that the instances from `fin.decidable_linear_order` match
the direct instances. They were defeq before but not at instance reducibility.

### [2020-08-19 22:20:42](https://github.com/leanprover-community/mathlib/commit/9a8e504)
feat(linear_algebra/affine_space/basic): more direction lemmas ([#3867](https://github.com/leanprover-community/mathlib/pull/3867))
Add a few more lemmas about the directions of affine subspaces.

### [2020-08-19 21:38:08](https://github.com/leanprover-community/mathlib/commit/7e6b8a9)
feat(linear_algebra/affine_space/basic): more vector_span lemmas ([#3866](https://github.com/leanprover-community/mathlib/pull/3866))
Add more lemmas relating `vector_span` to the `submodule.span` of
particular subtractions of points.  The new lemmas fix one of the
points in the subtraction and exclude that point, or its index in the
case of an indexed family of points rather than a set, from being on
the other side of the subtraction (whereas the previous lemmas don't
exclude the trivial subtraction of a point from itself).

### [2020-08-19 17:44:57](https://github.com/leanprover-community/mathlib/commit/bd5552a)
feat(ring_theory/polynomial/basic): Isomorphism between polynomials over a quotient and quotient over polynomials ([#3847](https://github.com/leanprover-community/mathlib/pull/3847))
The main statement is `polynomial_quotient_equiv_quotient_polynomial`, which gives that If `I` is an ideal of `R`, then the ring polynomials over the quotient ring `I.quotient` is isomorphic to the quotient of `polynomial R` by the ideal `map C I`.
Also, `mem_map_C_iff` shows that `map C I` contains exactly the polynomials whose coefficients all lie in `I`

### [2020-08-19 13:32:50](https://github.com/leanprover-community/mathlib/commit/15cacf0)
feat(analysis/normed_space/real_inner_product): orthogonal subspace order ([#3863](https://github.com/leanprover-community/mathlib/pull/3863))
Define the Galois connection between `submodule ℝ α` and its
`order_dual` given by `submodule.orthogonal`.  Thus, deduce that the
inf of orthogonal subspaces is the subspace orthogonal to the sup (for
three different forms of inf), as well as replacing the proof of
`submodule.le_orthogonal_orthogonal` by a use of
`galois_connection.le_u_l`.

### [2020-08-19 13:32:45](https://github.com/leanprover-community/mathlib/commit/d963213)
refactor(algebra/add_torsor,linear_algebra/affine_space/basic): vsub_set ([#3858](https://github.com/leanprover-community/mathlib/pull/3858))
The definition of `vsub_set` in `algebra/add_torsor` does something
similar to `set.image2`, but expressed directly with `∃` inside
`{...}`.  Various lemmas in `linear_algebra/affine_space/basic`
likewise express such sets of subtractions with a given point on one
side directly rather than using `set.image`.  These direct forms can
be inconvenient to use with lemmas about `set.image2`, `set.image` and
`set.range`; in particular, they have the equality inside the binders
expressed the other way round, leading to constructs such as `conv_lhs
{ congr, congr, funext, conv { congr, funext, rw eq_comm } }` when
it's necessary to convert one form to the other.
The form of `vsub_set` was suggested in review of [#2720](https://github.com/leanprover-community/mathlib/pull/2720), the original
`add_torsor` addition, based on what was then used in
`algebra/pointwise`.  Since then, `image2` has been added to mathlib
and `algebra/pointwise` now uses `image2`.
Thus, convert these definitions to using `image2` or `''` as
appropriate, so simplifying various proofs.
This PR deliberately only addresses `vsub_set` and related definitions
for such sets of subtractions; it does not attempt to change any other
definitions in `linear_algebra/affine_space/basic` that might also be
able to use `image2` or `''` but are not such sets of subtractions,
and does not change the formulations of lemmas not involving such sets
even if a rearrangement of equalities and existential quantifiers in
some such lemmas might bring them closer to the formulations about
images of sets.

### [2020-08-19 11:58:06](https://github.com/leanprover-community/mathlib/commit/1e677e6)
chore(data/finset/basic): use `finset.map` in `sigma_eq_bind` ([#3857](https://github.com/leanprover-community/mathlib/pull/3857))

### [2020-08-19 11:22:59](https://github.com/leanprover-community/mathlib/commit/a100396)
doc(linear_algebra/sesquilinear_form): add missing backtick ([#3862](https://github.com/leanprover-community/mathlib/pull/3862))

### [2020-08-19 03:25:09](https://github.com/leanprover-community/mathlib/commit/8579a5f)
fix(test/norm_cast): fix(?) test ([#3859](https://github.com/leanprover-community/mathlib/pull/3859))

### [2020-08-18 21:50:05](https://github.com/leanprover-community/mathlib/commit/425aee9)
feat(analysis/calculus) : L'Hôpital's rule, 0/0 case ([#3740](https://github.com/leanprover-community/mathlib/pull/3740))
This proves several forms of L'Hôpital's rule for computing 0/0 indeterminate forms, based on the proof given here : [Wikibooks](https://en.wikibooks.org/wiki/Calculus/L%27H%C3%B4pital%27s_Rule). See module docstring for more details.

### [2020-08-18 20:22:26](https://github.com/leanprover-community/mathlib/commit/5d2256d)
feat(miu_language): a formalisation of the MIU language described by D. Hofstadter in "Gödel, Escher, Bach". ([#3739](https://github.com/leanprover-community/mathlib/pull/3739))
We define an inductive type `derivable` so that `derivable x`  represents the notion that the MIU string `x` is derivable in the MIU language. We show `derivable x` is equivalent to `decstr x`, viz. the condition that `x` begins with an `M`, has no `M` in its tail, and for which `count I` is congruent to 1 or 2 modulo 3.
By showing `decidable_pred decstr`, we deduce that `derivable` is decidable.

### [2020-08-18 17:14:51](https://github.com/leanprover-community/mathlib/commit/0854e83)
chore(algebra/euclidean_domain): docstrings ([#3816](https://github.com/leanprover-community/mathlib/pull/3816))

### [2020-08-18 15:37:53](https://github.com/leanprover-community/mathlib/commit/7877033)
chore(logic/basic): `and_iff_left/right_iff_imp`, `or.right_comm` ([#3854](https://github.com/leanprover-community/mathlib/pull/3854))
Also add `@[simp]` to `forall_bool` and `exists_bool`

### [2020-08-18 15:37:47](https://github.com/leanprover-community/mathlib/commit/cb4a5a2)
doc(field_theory/tower): correct docstring ([#3853](https://github.com/leanprover-community/mathlib/pull/3853))

### [2020-08-18 14:01:34](https://github.com/leanprover-community/mathlib/commit/9a70533)
feat(data/option/basic): add ne_none_iff_exists ([#3856](https://github.com/leanprover-community/mathlib/pull/3856))

### [2020-08-18 10:28:42](https://github.com/leanprover-community/mathlib/commit/67549d9)
feat(order/filter/at_top_bot): add `at_bot` versions for (almost) all `at_top` lemmas ([#3845](https://github.com/leanprover-community/mathlib/pull/3845))
There are a few lemmas I ignored, either because I thought a `at_bot` version wouldn't be useful (e.g subsequence lemmas), because there is no "order inversing" equivalent of `monotone` (I think ?), or because I just didn't understand the statement so I was unable to tell if it was useful or not.

### [2020-08-18 08:45:02](https://github.com/leanprover-community/mathlib/commit/67e0019)
refactor(topology/metric_space/baire): use choose! in Baire theorem ([#3852](https://github.com/leanprover-community/mathlib/pull/3852))
Use `choose!` in the proof of Baire theorem.

### [2020-08-18 08:45:00](https://github.com/leanprover-community/mathlib/commit/6538274)
chore(data/set/finite): explicit `f` in `finset.preimage s f hf` ([#3851](https://github.com/leanprover-community/mathlib/pull/3851))
Otherwise pretty printer shows just `finset.preimage s _`.

### [2020-08-18 08:44:58](https://github.com/leanprover-community/mathlib/commit/c356148)
feat(category_theory/abelian): pseudoelements and a four lemma ([#3803](https://github.com/leanprover-community/mathlib/pull/3803))

### [2020-08-18 07:06:45](https://github.com/leanprover-community/mathlib/commit/0494807)
feat(algebra/ordered_*): cleanup and projection notation ([#3850](https://github.com/leanprover-community/mathlib/pull/3850))
Also add a few new projection notations.

### [2020-08-18 00:46:41](https://github.com/leanprover-community/mathlib/commit/cd7c228)
chore(scripts): update nolints.txt ([#3848](https://github.com/leanprover-community/mathlib/pull/3848))
I am happy to remove some nolints for you!

### [2020-08-17 21:27:17](https://github.com/leanprover-community/mathlib/commit/b68702e)
chore(field_theory/tower): generalize tower law to modules ([#3844](https://github.com/leanprover-community/mathlib/pull/3844))

### [2020-08-17 21:27:15](https://github.com/leanprover-community/mathlib/commit/3ea8e28)
feat(tactic/choose): derive local nonempty instances ([#3842](https://github.com/leanprover-community/mathlib/pull/3842))
This allows `choose!` to work even in cases like `{A : Type} (p : A -> Prop) (h : ∀ x : A, p x → ∃ y : A, p y)`, where we don't know that `A` is nonempty because it is generic, but it can be derived from the inhabitance of other variables in the context of the `∃ y : A` statement. As requested on zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20dependent.20chooser/near/207126587

### [2020-08-17 21:27:14](https://github.com/leanprover-community/mathlib/commit/f77530e)
feat(ring_theory/localization): Generalize theorems about localization over an integral domain ([#3780](https://github.com/leanprover-community/mathlib/pull/3780))
A number of theorems about the `fraction_map` from an integral domain to its field of fractions can be generalized to apply to any `localization_map` that were the localization set doesn't contain any zero divisors. The main use for this is to show that localizing an integral domain at any set of non-zero elements is an integral domain, were previously this was only proven for the field of fractions.
I made `le_non_zero_divisors` a class so that the integral domain instance can be synthesized automatically once you show that zero isn't in the localization set, but it could be left as just a proposition instead if that seems unnecessary.

### [2020-08-17 20:43:24](https://github.com/leanprover-community/mathlib/commit/f818acb)
feat(analysis/normed_space): generalize corollaries of Hahn-Banach ([#3658](https://github.com/leanprover-community/mathlib/pull/3658))

### [2020-08-17 17:33:37](https://github.com/leanprover-community/mathlib/commit/f8bf001)
fix(ring_theory/localization): remove coe_submodule instance ([#3832](https://github.com/leanprover-community/mathlib/pull/3832))
This coe can loop. See zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Unknown.20error.20while.20type-checking.20with.20.60use.60/near/207089095

### [2020-08-17 16:59:15](https://github.com/leanprover-community/mathlib/commit/472251b)
feat(algebra): define linear recurrences and prove basic lemmas about them ([#3829](https://github.com/leanprover-community/mathlib/pull/3829))
We define "linear recurrences", i.e assertions of the form `∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`, and we introduce basic related lemmas and definitions (solution space, auxiliary polynomial). Currently, the most advanced theorem is : `q ^ n` is a solution iff `q` is a root of the auxiliary polynomial.

### [2020-08-17 15:28:54](https://github.com/leanprover-community/mathlib/commit/3edf2b2)
feat(ring_theory/DVR,padics/padic_integers): characterize ideals of DVRs, apply to `Z_p` ([#3827](https://github.com/leanprover-community/mathlib/pull/3827))
Also introduce the p-adic valuation on `Z_p`, stolen from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>

### [2020-08-17 15:28:52](https://github.com/leanprover-community/mathlib/commit/d4cb237)
feat(algebra/module): define ordered semimodules and generalize convexity of functions ([#3728](https://github.com/leanprover-community/mathlib/pull/3728))

### [2020-08-17 13:59:04](https://github.com/leanprover-community/mathlib/commit/bc72d90)
refactor(logic/basic): classical -> root, root -> decidable ([#3812](https://github.com/leanprover-community/mathlib/pull/3812))
This moves all logic lemmas with `decidable` instances into the `decidable` namespace, and moves or adds classical versions of these to the root namespace. This change hits a lot of files, mostly to remove the `classical.` prefix on explicit references to classical lemmas.

### [2020-08-17 12:15:00](https://github.com/leanprover-community/mathlib/commit/1a8f6bf)
feat(lint): improved ge_or_gt linter ([#3810](https://github.com/leanprover-community/mathlib/pull/3810))
The linter will now correctly accepts occurrences of `f (≥)` and `∃ x ≥ t, b`
The linter will still raise a false positive on `∃ x y ≥ t, b` (with 2+ bound variables in a single binder that involves `>/≥`)
In contrast to the previous version of the linter, this one *does* check hypotheses.
This should reduce the `@[nolint ge_or_gt]` attributes from ~160 to ~10.

### [2020-08-17 10:46:14](https://github.com/leanprover-community/mathlib/commit/2a8d7f3)
chore(analysis/normed_space/banach): correct typo ([#3840](https://github.com/leanprover-community/mathlib/pull/3840))
Correct a typo from an old global replace.

### [2020-08-17 09:54:31](https://github.com/leanprover-community/mathlib/commit/41cbfdc)
chore(analysis/hofer): use  the new choose! ([#3839](https://github.com/leanprover-community/mathlib/pull/3839))

### [2020-08-17 09:11:02](https://github.com/leanprover-community/mathlib/commit/626de47)
feat(linear_algebra/affine_space/combination): centroid ([#3825](https://github.com/leanprover-community/mathlib/pull/3825))
Define the centroid of points in an affine space (given by an indexed
family with a `finset` of the index type), when the underlying ring
`k` is a division ring, and prove a few lemmas about cases where this
does not involve division by zero.  For example, the centroid of a
triangle or simplex, although none of the definitions and lemmas here
require affine independence so they are all stated more generally.
(The sort of things that would be appropriate to state specifically
for the case of a simplex would be e.g. defining medians and showing
that the centroid is the intersection of any two medians.)

### [2020-08-17 04:44:59](https://github.com/leanprover-community/mathlib/commit/6773f52)
feat(category_theory): limits in the category of indexed families ([#3737](https://github.com/leanprover-community/mathlib/pull/3737))
A continuation of [#3735](https://github.com/leanprover-community/mathlib/pull/3735), hopefully useful in [#3638](https://github.com/leanprover-community/mathlib/pull/3638).

### [2020-08-17 04:10:13](https://github.com/leanprover-community/mathlib/commit/b0b5cd4)
feat(geometry/euclidean): circumradius simp lemmas ([#3834](https://github.com/leanprover-community/mathlib/pull/3834))
Mark `dist_circumcenter_eq_circumradius` as a `simp` lemma.  Also add
a variant of that lemma where the distance is the other way round so
`simp` can work with both forms.

### [2020-08-17 03:03:18](https://github.com/leanprover-community/mathlib/commit/43337f7)
chore(data/nat/digits): refactor proof of `last_digit_ne_zero` ([#3836](https://github.com/leanprover-community/mathlib/pull/3836))
I thoroughly misunderstood why my prior attempts for [#3544](https://github.com/leanprover-community/mathlib/pull/3544) weren't working. I've refactored the proof so the `private` lemma is no longer necessary.

### [2020-08-17 01:29:28](https://github.com/leanprover-community/mathlib/commit/c1fece3)
fix(tactic/refine_struct): accept synonyms for `structure` types ([#3828](https://github.com/leanprover-community/mathlib/pull/3828))

### [2020-08-17 00:44:50](https://github.com/leanprover-community/mathlib/commit/56ed455)
chore(scripts): update nolints.txt ([#3835](https://github.com/leanprover-community/mathlib/pull/3835))
I am happy to remove some nolints for you!

### [2020-08-16 20:46:14](https://github.com/leanprover-community/mathlib/commit/40214fc)
feat(ring_theory/derivations): stab on derivations ([#3688](https://github.com/leanprover-community/mathlib/pull/3688))

### [2020-08-16 18:48:55](https://github.com/leanprover-community/mathlib/commit/4f2c958)
feat(tactic/interactive/choose): nondependent choose ([#3806](https://github.com/leanprover-community/mathlib/pull/3806))
Now you can write `choose!` to eliminate propositional arguments from the chosen functions.
```
example (h : ∀n m : ℕ, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose! i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m : ℕ), n < m → m = n + i n m ∨ m + j n m = n,
  trivial
end
```

### [2020-08-16 17:15:55](https://github.com/leanprover-community/mathlib/commit/3d4f085)
chore(ring_theory/ideal): docstring for Krull's theorem and a special case ([#3831](https://github.com/leanprover-community/mathlib/pull/3831))

### [2020-08-16 13:39:50](https://github.com/leanprover-community/mathlib/commit/ee74e7f)
feat(analysis/special_functions/exp_log): `tendsto real.log at_top at_top` ([#3826](https://github.com/leanprover-community/mathlib/pull/3826))

### [2020-08-16 12:41:57](https://github.com/leanprover-community/mathlib/commit/863bf79)
feat(data/padics): more valuations, facts about norms ([#3790](https://github.com/leanprover-community/mathlib/pull/3790))
Assorted lemmas about the `p`-adics. @jcommelin and I are adding algebraic structure here as part of the Witt vector development.
Some of these declarations are stolen shamelessly from the perfectoid project.
Coauthored by: Johan Commelin <johan@commelin.net>

### [2020-08-16 11:27:24](https://github.com/leanprover-community/mathlib/commit/a6f6434)
feat(data/fin): bundled embedding ([#3822](https://github.com/leanprover-community/mathlib/pull/3822))
Add the coercion from `fin n` to `ℕ` as a bundled embedding, an
equivalent of `function.embedding.subtype`.  Once leanprover-community/lean[#359](https://github.com/leanprover-community/mathlib/pull/359) is fixed
(making `fin n` a subtype), this can go away as a duplicate, but until
then it is useful.

### [2020-08-16 10:08:53](https://github.com/leanprover-community/mathlib/commit/dda2dcd)
chore(data/*): doc strings on some definitions ([#3791](https://github.com/leanprover-community/mathlib/pull/3791))
Doc strings on definitions in `data.` which I could figure out what it does.

### [2020-08-16 08:37:23](https://github.com/leanprover-community/mathlib/commit/8f03035)
chore(algebra/with_one): docstrings ([#3817](https://github.com/leanprover-community/mathlib/pull/3817))

### [2020-08-16 07:20:48](https://github.com/leanprover-community/mathlib/commit/20fe4a1)
feat(algebra/euclidean_domain): some cleanup ([#3752](https://github.com/leanprover-community/mathlib/pull/3752))
Lower the priority of simp-lemmas which have an equivalent version in `group_with_zero`, so that the version of `group_with_zero` is found by `squeeze_simp` for types that have both structures.
Add docstrings
Remove outdated comment

### [2020-08-16 06:05:27](https://github.com/leanprover-community/mathlib/commit/490d3ce)
refactor(data/list/palindrome): use decidable_of_iff' ([#3823](https://github.com/leanprover-community/mathlib/pull/3823))
Follow-up to [#3729](https://github.com/leanprover-community/mathlib/pull/3729).
`decidable_of_iff'` allows for omitting the `eq.symm`.

### [2020-08-16 06:05:25](https://github.com/leanprover-community/mathlib/commit/62374f7)
doc(data/real/card): docs and cleanup ([#3815](https://github.com/leanprover-community/mathlib/pull/3815))

### [2020-08-16 06:05:24](https://github.com/leanprover-community/mathlib/commit/8325cf6)
feat(*): reorder implicit arguments in tsum, supr, infi ([#3809](https://github.com/leanprover-community/mathlib/pull/3809))
This is helpful for a future version of the `ge_or_gt` linter to recognize binders: the binding type is the (implicit) argument directly before the binding body.

### [2020-08-16 06:05:21](https://github.com/leanprover-community/mathlib/commit/dba3018)
feat(category_theory): the category of indexed families of objects ([#3735](https://github.com/leanprover-community/mathlib/pull/3735))
Pulling out a definition from [#3638](https://github.com/leanprover-community/mathlib/pull/3638), and add some associated basic material.

### [2020-08-16 06:05:19](https://github.com/leanprover-community/mathlib/commit/3c2ed2a)
feat(topology/sheaves): construct sheaves of functions ([#3608](https://github.com/leanprover-community/mathlib/pull/3608))
# Sheaf conditions for presheaves of (continuous) functions.
We show that
* `Top.sheaf_condition.to_Type`: not-necessarily-continuous functions into a type form a sheaf
* `Top.sheaf_condition.to_Types`: in fact, these may be dependent functions into a type family
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf

### [2020-08-16 06:05:17](https://github.com/leanprover-community/mathlib/commit/765e460)
feat(ring_theory/polynomial/homogeneous): definition and basic props ([#3223](https://github.com/leanprover-community/mathlib/pull/3223))
This PR also move ring_theory/polynomial.lean to
ring_theory/polynomial/basic.lean
This PR is part of bringing symmetric polynomials to mathlib,
and besided that, I also expect to add binomial polynomials
and Chebyshev polynomials in the future.
Altogether, this motivates the starting of a ring_theory/polynomial
directory.
The file basic.lean may need cleaning or splitting at some point.

### [2020-08-16 04:46:02](https://github.com/leanprover-community/mathlib/commit/b1e7fb2)
feat (category_theory/over): composition of `over.map` ([#3798](https://github.com/leanprover-community/mathlib/pull/3798))
Filtering in some defs from the topos project.
~~Depends on [#3797](https://github.com/leanprover-community/mathlib/pull/3797).~~

### [2020-08-16 04:46:00](https://github.com/leanprover-community/mathlib/commit/1037a3a)
feat(algebra/homology, category_theory/abelian, algebra/category/Module): exactness ([#3784](https://github.com/leanprover-community/mathlib/pull/3784))
We define what it means for two maps `f` and `g` to be exact and show that for R-modules, this is the case if and only if `range f = ker g`.

### [2020-08-16 04:45:58](https://github.com/leanprover-community/mathlib/commit/2c930a3)
refactor(algebra/gcd_monoid, ring_theory/multiplicity): generalize normalization_domain, gcd_domain, multiplicity ([#3779](https://github.com/leanprover-community/mathlib/pull/3779))
* generalize `normalization_domain`, `gcd_domain`, `multiplicity` to not reference addition and subtraction
* make `gcd_monoid` and `normalization_monoid` into mixins
* add instances of `normalization_monoid` for `nat`, `associates`

### [2020-08-16 03:16:51](https://github.com/leanprover-community/mathlib/commit/ae8abf3)
chore(order/rel_iso): rename order_iso and order_embedding to rel_iso and rel_embedding ([#3750](https://github.com/leanprover-community/mathlib/pull/3750))
renames `order_iso` and `order_embedding`, to make it clear they apply to all binary relations
makes room for a new definition of `order_embedding` that will deal with order instances

### [2020-08-16 01:06:39](https://github.com/leanprover-community/mathlib/commit/55d06a9)
chore(scripts): update nolints.txt ([#3820](https://github.com/leanprover-community/mathlib/pull/3820))
I am happy to remove some nolints for you!

### [2020-08-16 01:06:37](https://github.com/leanprover-community/mathlib/commit/bf51f82)
feat(ring_theory/integral_closure): Rings lying within an integral extension are integral extensions ([#3781](https://github.com/leanprover-community/mathlib/pull/3781))
Proofs that if an algebra tower is integral then so are the two extensions making up the tower. I needed these for another proof I'm working on, but it seemed reasonable to create a smaller PR now since they are basically self contained.

### [2020-08-16 01:06:35](https://github.com/leanprover-community/mathlib/commit/a991854)
feat(category_theory/limits): a Fubini theorem ([#3732](https://github.com/leanprover-community/mathlib/pull/3732))

### [2020-08-15 23:34:47](https://github.com/leanprover-community/mathlib/commit/ad8c7e5)
chore(algebra/group/defs): docstrings ([#3819](https://github.com/leanprover-community/mathlib/pull/3819))

### [2020-08-15 23:34:45](https://github.com/leanprover-community/mathlib/commit/ad8dcaf)
chore(algebra/field): docstrings ([#3814](https://github.com/leanprover-community/mathlib/pull/3814))

### [2020-08-15 23:34:43](https://github.com/leanprover-community/mathlib/commit/598c091)
chore(tactic/squeeze): format `simp only []` as `simp only` ([#3811](https://github.com/leanprover-community/mathlib/pull/3811))
fixes [#3150](https://github.com/leanprover-community/mathlib/pull/3150)

### [2020-08-15 23:34:42](https://github.com/leanprover-community/mathlib/commit/e75ada7)
docs(category_theory/limits/cones): cones documentation and equivalence fixup ([#3795](https://github.com/leanprover-community/mathlib/pull/3795))
Mostly adding documentation in `ct.limits.cones`, but also shortened a couple of proofs. I also adjusted a couple of statements for `is_equivalence` to match the `is_equivalence` projections which are meant to be used (these statements were only used for cones anyway).

### [2020-08-15 23:34:40](https://github.com/leanprover-community/mathlib/commit/db99f67)
docs(category_theory/adjunction): document convenience constructors for adjunctions ([#3788](https://github.com/leanprover-community/mathlib/pull/3788))
As mentioned here: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/monoid.20object/near/204930460

### [2020-08-15 22:44:14](https://github.com/leanprover-community/mathlib/commit/cd1c00d)
chore(algebra/associated): docstrings ([#3813](https://github.com/leanprover-community/mathlib/pull/3813))

### [2020-08-15 22:09:09](https://github.com/leanprover-community/mathlib/commit/8f75f96)
feat(geometry/euclidean): circumcenter and circumradius ([#3693](https://github.com/leanprover-community/mathlib/pull/3693))
Show that every simplex in a Euclidean affine space has a unique
circumcenter (in the affine subspace spanned by that simplex) and
circumradius.  There are four main pieces, which all seem closely
enough related to put them all together in the same PR.  Both (b) and
(c) have quite long proofs, but I don't see obvious pieces to extract
from them.
(a) Various lemmas about `orthogonal_projection` in relation to points
equidistant from families of points.
(b) The induction step for the existence and uniqueness of the
(circumcenter, circumradius) pair, `exists_unique_dist_eq_of_insert`
(this is actually slightly more general than is needed for the
induction; it includes going from a set of points that has a unique
circumcenter and circumradius despite being infinite or not affine
independent, to such a unique circumcenter and circumradius when
another point is added outside their affine subspace).  This is
essentially just a calculation using an explicit expression for the
distance of the circumcenter of the new set of points from its
orthogonal projection, but still involves quite a lot of manipulation
to get things down to a form `field_simp, ring` can handle.
(c) The actual induction
`exists_unique_dist_eq_of_affine_independent`, giving a unique
(circumcenter, circumradius) pair for for any affine independent
family indexed by a `fintype`, by induction on the cardinality of that
`fintype` and using the result from (b).  Given (b), this is
essentially a lot of manipulation of trivialities.
(d) Extracting definitions and basic properties of `circumcenter` and
`circumradius` from the previous result.

### [2020-08-15 20:42:02](https://github.com/leanprover-community/mathlib/commit/b97b08b)
fix(*): remove usages of ge/gt ([#3808](https://github.com/leanprover-community/mathlib/pull/3808))
These were not caught by the old `ge_or_gt` linter, but they will be caught by the new (upcoming) `ge_or_gt` linter.
The `nolint` flags are not yet removed, this will happen in a later PR.
Renamings:
```
char_is_prime_of_ge_two -> char_is_prime_of_two_le
dist_eq_sub_of_ge -> dist_eq_sub_of_le_right
gt_of_mul_lt_mul_neg_right -> lt_of_mul_lt_mul_neg_right
```

### [2020-08-15 20:42:00](https://github.com/leanprover-community/mathlib/commit/36ced83)
chore(linear_algebra/matrix): format doc using markdown ([#3807](https://github.com/leanprover-community/mathlib/pull/3807))

### [2020-08-15 20:41:57](https://github.com/leanprover-community/mathlib/commit/26f2d4e)
docs(data/sum): fix typo in sum.is_right docs ([#3805](https://github.com/leanprover-community/mathlib/pull/3805))

### [2020-08-15 20:41:56](https://github.com/leanprover-community/mathlib/commit/9339a34)
chore(data/list/defs): docstring ([#3804](https://github.com/leanprover-community/mathlib/pull/3804))

### [2020-08-15 20:41:54](https://github.com/leanprover-community/mathlib/commit/7f1a489)
fix(algebra/order): restore choiceless theorems ([#3799](https://github.com/leanprover-community/mathlib/pull/3799))
The classical_decidable linter commit made these choiceless proofs use choice
again, making them duplicates of other theorems not in the `decidable.`
namespace.

### [2020-08-15 20:41:52](https://github.com/leanprover-community/mathlib/commit/2e890e6)
feat(category_theory/comma): constructing isos in the comma,over,under cats ([#3797](https://github.com/leanprover-community/mathlib/pull/3797))
Constructors to give isomorphisms in comma, over and under categories - essentially these just let you omit checking one of the commuting squares using the fact that the components are iso and the other square works.

### [2020-08-15 20:41:50](https://github.com/leanprover-community/mathlib/commit/c9bf6f2)
feat(linear_algebra/affine_space/independent): affinely independent sets ([#3794](https://github.com/leanprover-community/mathlib/pull/3794))
Prove variants of `affine_independent_iff_linear_independent_vsub`
that relate affine independence for a set of points (as opposed to an
indexed family of points) to linear independence for a set of vectors,
so facilitating linking to results such as `exists_subset_is_basis`
expressed in terms of linearly independent sets of vectors.  There are
two variants, depending on which of the set of points or the set of
vectors is given as a hypothesis.
Thus, applying `exists_subset_is_basis`, deduce that if `k` is a
field, any affinely independent set of points can be extended to such
a set that spans the whole space.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/linear.20suffering

### [2020-08-15 20:41:48](https://github.com/leanprover-community/mathlib/commit/ef3ba8b)
docs(category_theory/adjunction): lint some adjunction defs ([#3793](https://github.com/leanprover-community/mathlib/pull/3793))

### [2020-08-15 20:41:45](https://github.com/leanprover-community/mathlib/commit/d40c06f)
feat(algebra/ordered_field): rewrite and cleanup ([#3751](https://github.com/leanprover-community/mathlib/pull/3751))
Group similar lemmas in a more intuitive way
Add docstrings, module doc and section headers
Simplify some proofs
Remove some implications if they had a corresponding `iff` lemma.
Add some more variants of some lemmas
Rename some lemmas for consistency
List of name changes (the lemma on the right might be a bi-implication, if the original version was an implication):
`add_midpoint` -> `add_sub_div_two_lt`
`le_div_of_mul_le`, `mul_le_of_le_div` -> `le_div_iff`
`lt_div_of_mul_lt`, `mul_lt_of_lt_div` -> `lt_div_iff`
`div_le_of_le_mul` -> `div_le_iff'`
`le_mul_of_div_le` -> `div_le_iff`
`div_lt_of_pos_of_lt_mul` -> `div_lt_iff'`
`mul_le_of_neg_of_div_le`, `div_le_of_neg_of_mul_le` -> `div_le_iff_of_neg`
`mul_lt_of_neg_of_div_lt`, `div_lt_of_neg_of_mul_lt` -> `div_lt_iff_of_neg`
`div_le_div_of_pos_of_le` -> `div_le_div_of_le`
`div_le_div_of_neg_of_le` -> `div_le_div_of_nonpos_of_le`
`div_lt_div_of_pos_of_lt` -> `div_lt_div_of_lt`
`div_mul_le_div_mul_of_div_le_div_nonneg` -> `div_mul_le_div_mul_of_div_le_div`
`one_le_div_of_le`, `le_of_one_le_div`, `one_le_div_iff_le` -> `one_le_div`
`one_lt_div_of_lt`, `lt_of_one_lt_div`, `one_lt_div_iff_lt` -> `one_lt_div`
`div_le_one_iff_le` -> `div_le_one`
`div_lt_one_iff_lt` -> `div_lt_one`
`one_div_le_of_pos_of_one_div_le` -> `one_div_le`
`one_div_le_of_neg_of_one_div_le` -> `one_div_le_of_neg`
`div_lt_div_of_pos_of_lt_of_pos` -> `div_lt_div_of_lt_left`
One regression I noticed in some other files: when using `div_le_iff`, and the argument is proven by some lemma about `linear_ordered_semiring` then Lean gives a type mismatch. Presumably this happens because the instance chain `ordered_field -> has_le` doesn't go via `ordered_semiring`. The fix is to give the type explicitly, for example using `div_le_iff (t : (0 : ℝ) < _)`

### [2020-08-15 20:41:42](https://github.com/leanprover-community/mathlib/commit/f953a9d)
feat(category_theory/limits/shapes/types): duals ([#3738](https://github.com/leanprover-community/mathlib/pull/3738))
Just dualising some existing material.

### [2020-08-15 19:14:07](https://github.com/leanprover-community/mathlib/commit/8ce00af)
feat(data/set/basic): pairwise_on for equality ([#3802](https://github.com/leanprover-community/mathlib/pull/3802))
Add another lemma about `pairwise_on`: if and only if `f` takes
pairwise equal values on `s`, there is some value it takes everywhere
on `s`.  This arose from discussion in [#3693](https://github.com/leanprover-community/mathlib/pull/3693).

### [2020-08-15 19:14:05](https://github.com/leanprover-community/mathlib/commit/78354e1)
feat(tactic/linarith): support case splits in preprocessing (including `ne` hypotheses) ([#3786](https://github.com/leanprover-community/mathlib/pull/3786))
This adds an API for `linarith` preprocessors to branch. Each branch results in a separate call to `linarith`, so this can be exponentially bad. Use responsibly.
Given that the functionality is there, and I needed a way to test it, I've added a feature that people have been begging for that I've resisted: you can now call `linarith {split_ne := tt}` to handle `a ≠ b` hypotheses. Again: 2^n `linarith` calls for `n` disequalities in your context.

### [2020-08-15 17:58:55](https://github.com/leanprover-community/mathlib/commit/050728b)
feat(data/fintype/basic): card lemma and finset bool alg ([#3796](https://github.com/leanprover-community/mathlib/pull/3796))
Adds the card lemma
```
finset.card_le_univ [fintype α] (s : finset α) : s.card ≤ fintype.card α
```
which I expected to see in mathlib, and upgrade the bounded_distrib_lattice instance on finset in the presence of fintype to a boolean algebra instance.

### [2020-08-15 17:58:53](https://github.com/leanprover-community/mathlib/commit/44010bc)
refactor(linear_algebra/affine_space/combination): bundled affine_combination ([#3789](https://github.com/leanprover-community/mathlib/pull/3789))
When `weighted_vsub_of_point` and `weighted_vsub` became bundled
`linear_map`s on the weights, `affine_combination` was left as an
unbundled function with different argument order from the other two
related operations.  Make it into a bundled `affine_map` on the
weights, so making it more consistent with the other two operations
and allowing general results on `affine_map`s to be used on
`affine_combination` (as illustrated by the changed proofs of
`weighted_vsub_vadd_affine_combination` and
`affine_combination_vsub`).

### [2020-08-15 17:58:51](https://github.com/leanprover-community/mathlib/commit/9216dd7)
chore(ring_theory): delete `is_algebra_tower` ([#3785](https://github.com/leanprover-community/mathlib/pull/3785))
Delete the abbreviation `is_algebra_tower` for `is_scalar_tower`, and replace all references (including the usages of the `is_algebra_tower` namespace) with `is_scalar_tower`. Documentation should also have been updated accordingly.
This change was requested in a comment on [#3717](https://github.com/leanprover-community/mathlib/pull/3717).

### [2020-08-15 16:25:49](https://github.com/leanprover-community/mathlib/commit/9451f8d)
feat(data/sum): add sum.{get_left, get_right, is_left, is_right} ([#3792](https://github.com/leanprover-community/mathlib/pull/3792))

### [2020-08-15 14:12:32](https://github.com/leanprover-community/mathlib/commit/daafd6f)
chore(number_theory/pythagorean_triples): added doc-strings ([#3787](https://github.com/leanprover-community/mathlib/pull/3787))
Added docstrings to:
`pythagorean_triple_comm`
`pythagorean_triple.zero`
`mul`
`mul_iff`

### [2020-08-15 14:12:30](https://github.com/leanprover-community/mathlib/commit/10d4811)
feat(algebra/add_torsor): injectivity lemmas ([#3767](https://github.com/leanprover-community/mathlib/pull/3767))
Add variants of the `add_action` and `add_torsor` cancellation lemmas
whose conclusion is stated in terms of `function.injective`.

### [2020-08-15 12:43:48](https://github.com/leanprover-community/mathlib/commit/5c13693)
chore(algebra/classical_lie_algebras): fix some doc strings ([#3776](https://github.com/leanprover-community/mathlib/pull/3776))

### [2020-08-15 12:43:45](https://github.com/leanprover-community/mathlib/commit/9ac6e8a)
refactor(set_theory/pgame): rename pgame lemma ([#3775](https://github.com/leanprover-community/mathlib/pull/3775))
Renamed `move_left_right_moves_neg_symm` to `move_left_left_moves_neg_symm` to make it consistent with the other 3 related lemmas

### [2020-08-15 12:43:43](https://github.com/leanprover-community/mathlib/commit/658cd38)
feat(tactic/derive_fintype): derive fintype instances ([#3772](https://github.com/leanprover-community/mathlib/pull/3772))
This adds a `@[derive fintype]` implementation, like so:
```
@[derive fintype]
inductive foo (α : Type)
| A : α → foo
| B : α → α → foo
| C : α × α → foo
| D : foo
```

### [2020-08-15 12:43:41](https://github.com/leanprover-community/mathlib/commit/18746ef)
feat(analysis/special_functions/pow): Added lemmas for rpow of neg exponent ([#3715](https://github.com/leanprover-community/mathlib/pull/3715))
I noticed that the library was missing some lemmas regarding the bounds of rpow of a negative exponent so I added them. I cleaned up the other similar preexisting lemmas for consistency. I then repeated the process for nnreal lemmas.

### [2020-08-15 12:43:39](https://github.com/leanprover-community/mathlib/commit/099f070)
feat(topology/sheaves): the sheaf condition ([#3605](https://github.com/leanprover-community/mathlib/pull/3605))
Johan and I have been working with this, and it's at least minimally viable.
In follow-up PRs we have finished:
* constructing the sheaf of dependent functions to a type family
* constructing the sheaf of continuous functions to a fixed topological space
* checking the sheaf condition under forgetful functors that reflect isos and preserve limits (https://stacks.math.columbia.edu/tag/0073)
Obviously there's more we'd like to see before being confident that a design for sheaves is workable, but we'd like to get started!

### [2020-08-15 12:06:09](https://github.com/leanprover-community/mathlib/commit/36b4a1e)
refactor(algebra/add_torsor): use `out_param` ([#3727](https://github.com/leanprover-community/mathlib/pull/3727))

### [2020-08-15 10:36:54](https://github.com/leanprover-community/mathlib/commit/2b8ece6)
feat(data/nat/basic): one mod two or higher is one ([#3763](https://github.com/leanprover-community/mathlib/pull/3763))

### [2020-08-15 10:09:19](https://github.com/leanprover-community/mathlib/commit/c444a00)
Revert "chore(ring_theory): delete `is_algebra_tower`"
This reverts commit c956ce1516ccfb3139ae3ebde7ede9c678d81968.

### [2020-08-15 10:05:13](https://github.com/leanprover-community/mathlib/commit/c956ce1)
chore(ring_theory): delete `is_algebra_tower`
Delete the abbreviation `is_algebra_tower` for `is_scalar_tower`,
and replace all references (including the usages of the `is_algebra_tower`
namespace) with `is_scalar_tower`. Documentation should also have been
updated accordingly.
This change was requested in a comment on [#3717](https://github.com/leanprover-community/mathlib/pull/3717).

### [2020-08-15 08:45:27](https://github.com/leanprover-community/mathlib/commit/67dad7f)
feat(control/equiv_functor): fintype instance ([#3783](https://github.com/leanprover-community/mathlib/pull/3783))
Requested at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/fintype.2Eequiv_congr/near/206773279

### [2020-08-15 07:22:35](https://github.com/leanprover-community/mathlib/commit/b670212)
fix(tactic/apply): fix ordering of goals produced by `apply` ([#3777](https://github.com/leanprover-community/mathlib/pull/3777))

### [2020-08-15 07:22:33](https://github.com/leanprover-community/mathlib/commit/c1a5283)
refactor(data/list/tfae): tfae.out ([#3774](https://github.com/leanprover-community/mathlib/pull/3774))
This version of `tfae.out` has slightly better automatic reduction behavior: if `h : [a, b, c].tfae` then the original of `h.out 1 2` proves `[a, b, c].nth_le 1 _ <-> [a, b, c].nth_le 2 _` while the new version of `h.out 1 2` proves `b <-> c`. These are the same, of course, and you can mostly use them interchangeably, but the second one is a bit nicer to look at (and possibly works better with e.g. subsequent rewrites).

### [2020-08-15 06:35:10](https://github.com/leanprover-community/mathlib/commit/55f4926)
fix(algebra/archimedean): switch to a more natural and general condition in exists_nat_pow_near ([#3782](https://github.com/leanprover-community/mathlib/pull/3782))
per discussion at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Starting.20to.20contribute.20to.20mathlib/near/206945824

### [2020-08-14 17:00:08](https://github.com/leanprover-community/mathlib/commit/3ae44bd)
fix(tactic/equiv_rw): fix problem with stuck universe metavariables ([#3773](https://github.com/leanprover-community/mathlib/pull/3773))

### [2020-08-14 15:47:08](https://github.com/leanprover-community/mathlib/commit/c252800)
chore(*): use notation for `filter.prod` ([#3768](https://github.com/leanprover-community/mathlib/pull/3768))
Also change from `∀ v w ∈ V` to `∀ (v ∈ V) (w ∈ V)` in `exists_nhds_split_inv`, `exists_nhds_half_neg`, `add_group_with_zero_nhd.exists_Z_half`.

### [2020-08-14 12:28:48](https://github.com/leanprover-community/mathlib/commit/0e5f44b)
chore(*): assorted lemmas for FTC-1 ([#3755](https://github.com/leanprover-community/mathlib/pull/3755))
Lemmas from FTC-1 (`has_strict_deriv` version) [#3709](https://github.com/leanprover-community/mathlib/pull/3709)

### [2020-08-14 00:40:06](https://github.com/leanprover-community/mathlib/commit/b611c5f)
chore(scripts): update nolints.txt ([#3771](https://github.com/leanprover-community/mathlib/pull/3771))
I am happy to remove some nolints for you!

### [2020-08-13 19:36:34](https://github.com/leanprover-community/mathlib/commit/32c6a73)
feat(ci): auto label merge conflicts, try 2 ([#3766](https://github.com/leanprover-community/mathlib/pull/3766))

### [2020-08-13 19:36:32](https://github.com/leanprover-community/mathlib/commit/627b431)
feat(tactic/find_unused): find the dead code in a module ([#3701](https://github.com/leanprover-community/mathlib/pull/3701))

### [2020-08-13 19:36:30](https://github.com/leanprover-community/mathlib/commit/28dfad8)
feat(ideals,submonoids,subgroups): mem_sup(r) and mem_inf(i) lemmas ([#3697](https://github.com/leanprover-community/mathlib/pull/3697))

### [2020-08-13 18:09:00](https://github.com/leanprover-community/mathlib/commit/4cc094b)
chore(data/int/basic): norm_cast attribute on int.coe_nat_mod ([#3765](https://github.com/leanprover-community/mathlib/pull/3765))

### [2020-08-13 14:29:54](https://github.com/leanprover-community/mathlib/commit/c66ecd3)
feat(intervals/image_preimage): preimage under multiplication ([#3757](https://github.com/leanprover-community/mathlib/pull/3757))
Add lemmas `preimage_mul_const_Ixx` and `preimage_const_mul_Ixx`.
Also generalize `equiv.mul_left` and `equiv.mul_right` to `units`.

### [2020-08-13 12:59:37](https://github.com/leanprover-community/mathlib/commit/f912f18)
feat(ci): auto label merge conflicts ([#3761](https://github.com/leanprover-community/mathlib/pull/3761))

### [2020-08-13 12:59:35](https://github.com/leanprover-community/mathlib/commit/34352c2)
refactor(algebra/associated): change several instances from [integral_domain] to [comm_cancel_monoid_with_zero] ([#3744](https://github.com/leanprover-community/mathlib/pull/3744))
defines `comm_cancel_monoid_with_zero`
replaces some `integral_domain` instances with `comm_cancel_monoid_with_zero`
prepares the API for refactoring `normalization_domain`, `gcd_domain`, and `unique_factorization_domain` to monoids

### [2020-08-13 12:59:33](https://github.com/leanprover-community/mathlib/commit/2c4300b)
feat(data/polynomial): adds map_comp ([#3736](https://github.com/leanprover-community/mathlib/pull/3736))
Adds lemma saying that the map of the composition of two polynomials is the composition of the maps, as mentioned [here](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Polynomial.20composition.20and.20map.20commute).

### [2020-08-13 11:32:00](https://github.com/leanprover-community/mathlib/commit/ac2f011)
feat(data/*): Add sizeof lemmas. ([#3745](https://github.com/leanprover-community/mathlib/pull/3745))

### [2020-08-13 11:01:00](https://github.com/leanprover-community/mathlib/commit/b1e56a2)
feat(analysis/special_functions/trigonometric): Added lemma cos_ne_zero_iff ([#3743](https://github.com/leanprover-community/mathlib/pull/3743))
I added the theorem `cos_ne_zero_iff`, a corollary to the preexisting theorem `cos_eq_zero_iff`
<!-- put comments you want to keep out of the PR commit here -->

### [2020-08-13 09:23:02](https://github.com/leanprover-community/mathlib/commit/ced7469)
chore(data/finset/order): use `[nonempty]` in `directed.finset_le` ([#3759](https://github.com/leanprover-community/mathlib/pull/3759))

### [2020-08-13 09:23:00](https://github.com/leanprover-community/mathlib/commit/4c24a09)
chore(data/fintype/card): add `prod_bool` ([#3758](https://github.com/leanprover-community/mathlib/pull/3758))

### [2020-08-13 09:22:58](https://github.com/leanprover-community/mathlib/commit/31a0258)
chore(data/fintype/card): DRY using `@... (multiplicative _)` ([#3756](https://github.com/leanprover-community/mathlib/pull/3756))

### [2020-08-13 09:22:56](https://github.com/leanprover-community/mathlib/commit/cc6528e)
feat(analysis/calculus/fderiv): multiplication by a complex respects real differentiability ([#3731](https://github.com/leanprover-community/mathlib/pull/3731))
If `f` takes values in a complex vector space and is real-differentiable, then `c f` is also real-differentiable when `c` is a complex number. This PR proves this fact and the obvious variations, in the general case of two fields where one is a normed algebra over the other one.
Along the way, some material on `module.restrict_scalars` is added, notably in a normed space context.

### [2020-08-13 09:22:52](https://github.com/leanprover-community/mathlib/commit/cfcbea6)
feat(data/list/palindrome): define palindromes ([#3729](https://github.com/leanprover-community/mathlib/pull/3729))
This introduces an inductive type `palindrome`, with conversions to and from the proposition `reverse l = l`.
Review of this PR indicates two things: (1) maybe the name `is_palindrome` is better, especially if we define the subtype of palindromic lists; (2) maybe defining palindrome by `reverse l = l` is simpler. We note these for future development.

### [2020-08-13 07:52:35](https://github.com/leanprover-community/mathlib/commit/c503b7a)
feat(algebra/order): more lemmas for projection notation ([#3753](https://github.com/leanprover-community/mathlib/pull/3753))
Also import `tactic.lint` and ensure that the linter passes
Move `ge_of_eq` to this file

### [2020-08-13 06:22:20](https://github.com/leanprover-community/mathlib/commit/6c8b2cd)
fix(algebra/field) remove `one_div_eq_inv` ([#3749](https://github.com/leanprover-community/mathlib/pull/3749))
It already existed as `one_div` for `group_with_zero`
Also make `one_div` a `simp` lemma and renamed `nnreal.one_div_eq_inv` to `nnreal.one_div`.

### [2020-08-13 01:10:43](https://github.com/leanprover-community/mathlib/commit/d6ffc1a)
feat(tactic/clear_value): preserve order and naming ([#3700](https://github.com/leanprover-community/mathlib/pull/3700))

### [2020-08-13 00:42:53](https://github.com/leanprover-community/mathlib/commit/cacb54e)
chore(scripts): update nolints.txt ([#3754](https://github.com/leanprover-community/mathlib/pull/3754))
I am happy to remove some nolints for you!

### [2020-08-12 23:09:20](https://github.com/leanprover-community/mathlib/commit/486830b)
feat(tactic/choose): `choose` can now decompose conjunctions ([#3699](https://github.com/leanprover-community/mathlib/pull/3699))

### [2020-08-12 20:04:21](https://github.com/leanprover-community/mathlib/commit/f8c8135)
feat(tactic/rcases): type ascriptions in rcases ([#3730](https://github.com/leanprover-community/mathlib/pull/3730))
This is a general rewrite of the `rcases` tactic, with the primary intent of adding support for type ascriptions in `rcases` patterns but it also includes a bunch more documentation, as well as making the grammar simpler, avoiding the strict tuple/alts alternations required by the previous `many` constructor (and the need for `rcases_patt_inverted` for whether the constructor means `tuple` of `alts` or `alts` of `tuple`).
From a user perspective, it should not be noticeably different, except:
* You can now use parentheses freely in patterns, so things like `a | (b | c)` work
* You can use type ascriptions
The new `rcases` is backward compatible with the old one, except that `rcases e with a` (where `a` is a name) no longer does any cases and is basically just another way to write `have a := e`; to get the same effect as `cases e with a` you have to write `rcases e with ⟨a⟩` instead.

### [2020-08-12 16:33:24](https://github.com/leanprover-community/mathlib/commit/4324778)
feat(.): add code of conduct ([#3747](https://github.com/leanprover-community/mathlib/pull/3747))

### [2020-08-12 15:04:27](https://github.com/leanprover-community/mathlib/commit/eb4b2a0)
feat(field_theory/algebraic_closure): algebraic closure ([#3733](https://github.com/leanprover-community/mathlib/pull/3733))
```lean
instance : is_alg_closed (algebraic_closure k) :=
```
TODO: Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).

### [2020-08-12 10:41:14](https://github.com/leanprover-community/mathlib/commit/bfcf640)
feat(topology/opens): open_embedding_of_le ([#3597](https://github.com/leanprover-community/mathlib/pull/3597))
Add `lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) : open_embedding (set.inclusion i)`.
Also, I was finding it quite inconvenient to have `x ∈ U` for `U : opens X` being unrelated to `x ∈ (U : set X)`. I propose we just add the simp lemmas in this PR that unfold to the set-level membership operation.
(I'd be happy to go the other way if someone has a strong opinion here; just that we pick a simp normal form for talking about membership and inclusion of opens.)

### [2020-08-11 15:31:36](https://github.com/leanprover-community/mathlib/commit/06e1405)
docs(category/default): Fix typo for monomorphism ([#3741](https://github.com/leanprover-community/mathlib/pull/3741))

### [2020-08-11 09:57:43](https://github.com/leanprover-community/mathlib/commit/f92fd0d)
refactor(algebra/divisibility, associated): generalize instances in divisibility, associated ([#3714](https://github.com/leanprover-community/mathlib/pull/3714))
generalizes the divisibility relation to noncommutative monoids
adds missing headers to algebra/divisibility
generalizes the instances in many of the lemmas in algebra/associated
reunites (some of the) divisibility API for ordinals with general monoids

### [2020-08-11 07:24:07](https://github.com/leanprover-community/mathlib/commit/57df7f5)
feat(haar_measure): define the Haar measure ([#3542](https://github.com/leanprover-community/mathlib/pull/3542))
Define the Haar measure on a locally compact Hausdorff group.
Some additions and simplifications to outer_measure and content.

### [2020-08-11 00:42:24](https://github.com/leanprover-community/mathlib/commit/43ceb3e)
chore(scripts): update nolints.txt ([#3734](https://github.com/leanprover-community/mathlib/pull/3734))
I am happy to remove some nolints for you!

### [2020-08-10 19:28:55](https://github.com/leanprover-community/mathlib/commit/9e03995)
chore(algebra/ordered_field): cleanup ([#3723](https://github.com/leanprover-community/mathlib/pull/3723))
* drop `mul_zero_lt_mul_inv_of_pos` and `mul_zero_lt_mul_inv_of_neg`;
* add `iff` lemmas `one_div_pos/neg/nonneg/nonpos` replacing old
  implications;
* some lemmas now assume `≤` instead of `<`;
* rename `mul_lt_of_gt_div_of_neg` to `mul_lt_of_neg_of_div_lt`
  replacing `>` by `<`.
* add `mul_sub_mul_div_mul_neg_iff` and `mul_sub_mul_div_mul_nonpos_iff`,
  generate implications using `alias`;
* drop `div_pos_of_pos_of_pos` (use `div_pos`) and
  `div_nonneg_of_nonneg_of_pos` (use `div_nonneg`);
* replace `div_nonpos_of_nonpos_of_pos` with
  `div_nonpos_of_nonpos_of_nonneg`;
* replace `div_nonpos_of_nonneg_of_neg` with
  `div_nonpos_of_nonneg_of_nonpos`;
* replace `div_mul_le_div_mul_of_div_le_div_pos` and
  `div_mul_le_div_mul_of_div_le_div_pos'` with
  `div_mul_le_div_mul_of_div_le_div_nonneg`; I failed to find
  in the history why we had two equivalent lemmas.
* merge `le_mul_of_ge_one_right` and `le_mul_of_one_le_right'` into
  `le_mul_of_one_le_right`, rename old `le_mul_of_one_le_right` to
  `le_mul_of_one_le_right'`;
* ditto with `le_mul_of_ge_one_left`, `le_mul_of_one_le_left`, and
  `le_mul_of_one_le_left'`;
* ditto with `lt_mul_of_gt_one_right`, `lt_mul_of_one_lt_right`, and
  `lt_mul_of_one_lt_right'`;
* rename `div_lt_of_mul_lt_of_pos` to `div_lt_of_pos_of_lt_mul`;
* rename `div_lt_of_mul_gt_of_neg` to `div_lt_of_neg_of_mul_lt`;
* rename `mul_le_of_div_le_of_neg` to `mul_le_of_neg_of_div_le`;
* rename `div_le_of_mul_le_of_neg` to `div_le_of_neg_of_mul_le`;
* rename `div_lt_div_of_lt_of_pos` to `div_lt_div_of_pos_of_lt`, swap
  arguments;
* rename `div_le_div_of_le_of_pos` to `div_le_div_of_pos_of_le`, swap
  arguments;
* rename `div_lt_div_of_lt_of_neg` to `div_lt_div_of_neg_of_lt`, swap
  arguments;
* rename `div_le_div_of_le_of_neg` to `div_le_div_of_neg_of_le`, swap
  arguments;
* rename `one_div_lt_one_div_of_lt_of_neg` to
  `one_div_lt_one_div_of_neg_of_lt`;
* rename `one_div_le_one_div_of_le_of_neg` to
  `one_div_le_one_div_of_neg_of_le`;
* rename `le_of_one_div_le_one_div_of_neg` to
  `le_of_neg_of_one_div_le_one_div`;
* rename `lt_of_one_div_lt_one_div_of_neg` to
  `lt_of_neg_of_one_div_lt_one_div`;
* rename `one_div_le_of_one_div_le_of_pos` to
  `one_div_le_of_pos_of_one_div_le`;
* rename `one_div_le_of_one_div_le_of_neg` to
  `one_div_le_of_neg_of_one_div_le`.

### [2020-08-10 19:28:53](https://github.com/leanprover-community/mathlib/commit/4a75df9)
feat(group_theory/group_action): generalize `is_algebra_tower` ([#3717](https://github.com/leanprover-community/mathlib/pull/3717))
This PR introduces a new typeclass `is_scalar_tower R M N` stating that scalar multiplications between the three types are compatible: `smul_assoc : ((x : R) • (y : M)) • (z : N) = x • (y • z)`.
This typeclass is the general form of `is_algebra_tower`. It also generalizes some of the existing instances of `is_algebra_tower`. I didn't try very hard though, so I might have missed some instances.
Related Zulip discussions:
 * https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Effect.20of.20changing.20the.20base.20field.20on.20span
 * https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/pull.20back.20an.20R.20module.20along.20.60S.20-.3E.2B*.20R.60

### [2020-08-10 17:55:47](https://github.com/leanprover-community/mathlib/commit/37e97b5)
feat(tactic): fix two bugs with generalize' ([#3710](https://github.com/leanprover-community/mathlib/pull/3710))
The name generated by `generalize'` will be exactly the given name, even if the name already occurs in the context.
There was a bug with `generalize' h : e = x` if `e` occurred in the goal.

### [2020-08-10 15:19:08](https://github.com/leanprover-community/mathlib/commit/4786136)
feat(category_theory/limits): explicit isomorphisms between preserved limits ([#3602](https://github.com/leanprover-community/mathlib/pull/3602))
When `G` preserves limits, it's nice to be able to quickly obtain the iso `G.obj (pi_obj f) ≅ pi_obj (λ j, G.obj (f j))`.

### [2020-08-10 12:46:02](https://github.com/leanprover-community/mathlib/commit/5680428)
chore(category_theory/limits): minor changes in equalizers and products ([#3603](https://github.com/leanprover-community/mathlib/pull/3603))

### [2020-08-09 01:11:07](https://github.com/leanprover-community/mathlib/commit/17ef529)
refactor(linear_algebra/affine_space): split up file ([#3726](https://github.com/leanprover-community/mathlib/pull/3726))
`linear_algebra/affine_space.lean` was the 10th largest `.lean` file
in mathlib.  Move it to `linear_algebra/affine_space/basic.lean` and
split out some pieces into separate files, so reducing its size to
41st largest as well as reducing dependencies for users not needing
all those files.
More pieces could also be split out (for example, splitting out
`homothety` would eliminate the dependence of
`linear_algebra.affine_space.basic` on
`linear_algebra.tensor_product`), but this split seems a reasonable
starting point.
This split is intended to preserve the exact set of definitions
present and their namespaces, just moving some of them to different
files, even if the existing namespaces aren't very consistent
(e.g. some definitions relating to affine combinations are in the
`finset` namespace, so allowing dot notation to be used for such
combinations, but others are in the `affine_space` namespace, and
there may not be a consistent rule for the division between the two).

### [2020-08-08 14:34:18](https://github.com/leanprover-community/mathlib/commit/f23fe9a)
doc(tactic/lean_core_docs): by_cases is classical ([#3718](https://github.com/leanprover-community/mathlib/pull/3718))
`by_cases` was changed to use classical reasoning (leanprover-community/mathlib[#3354](https://github.com/leanprover-community/mathlib/pull/3354), leanprover-community/lean[#409](https://github.com/leanprover-community/mathlib/pull/409)), but the documentation hasn't been updated yet.
I leave `by_contra` alone as it still uses `decidable`.

### [2020-08-08 13:01:43](https://github.com/leanprover-community/mathlib/commit/d27ddb4)
chore(linear_algebra/basic): rewrite `p.comap q.subtype` to `comap q.subtype p` ([#3725](https://github.com/leanprover-community/mathlib/pull/3725))
@PatrickMassot requested this change in the review of [#3720](https://github.com/leanprover-community/mathlib/pull/3720):
> I find this statement very difficult to read. I think this is a bad use of dot notation, it really feels like `p` is pulling back `q.subtype` instead of the other way around (and even the docstring is suggesting that!). The same problem happens with filter.(co)map and always try to avoid it.
> I would open submodule and then write `comap q.subtype p ≃ₗ[R] p`.

### [2020-08-08 10:16:01](https://github.com/leanprover-community/mathlib/commit/1675dc4)
chore(order/complete_lattice): use `order_dual` ([#3724](https://github.com/leanprover-community/mathlib/pull/3724))

### [2020-08-08 09:22:19](https://github.com/leanprover-community/mathlib/commit/bf1c7b7)
feat(linear_algebra/finite_dimensional): finite dimensional `is_basis` helpers ([#3720](https://github.com/leanprover-community/mathlib/pull/3720))
If we have a family of vectors in `V` with cardinality equal to the (finite) dimension of `V` over a field `K`, they span the whole space iff they are linearly independent.
This PR proves those two facts (in the form that either of the conditions of `is_basis K b` suffices to prove `is_basis K b` if `b` has the right cardinality).
We don't need to assume that `V` is finite dimensional, because the case that `findim K V = 0` will generally lead to a contradiction. We do sometimes need to assume that the family is nonempty, which seems like a much nicer condition.

### [2020-08-07 21:33:16](https://github.com/leanprover-community/mathlib/commit/d61bd4a)
feat(algebra/classical_lie_algebras): add lie_algebra.orthogonal.mem_so ([#3711](https://github.com/leanprover-community/mathlib/pull/3711))
Also unrelated change to use new notation for direct_sum

### [2020-08-07 19:53:30](https://github.com/leanprover-community/mathlib/commit/1cd74b1)
fix(linear_algebra/finite_dimensional): universe generalize cardinal_mk_le_findim_of_linear_independent ([#3721](https://github.com/leanprover-community/mathlib/pull/3721))

### [2020-08-07 18:26:21](https://github.com/leanprover-community/mathlib/commit/00e4c04)
doc(linear_algebra/affine_space): expand module doc string ([#3719](https://github.com/leanprover-community/mathlib/pull/3719))
Make module doc string discuss the main definitions relating to affine
spaces.

### [2020-08-07 18:26:19](https://github.com/leanprover-community/mathlib/commit/4e24f4c)
feat(data/list/*): add indexed versions of some list functions ([#2191](https://github.com/leanprover-community/mathlib/pull/2191))
Add `foldr_with_index`, `foldl_with_index`, `mfoldr_with_index`, `mfoldl_with_index`, `mmap_with_index` and `mmap_with_index'`. The new functions are proven correct by relating them to their non-indexed counterparts.

### [2020-08-07 16:49:27](https://github.com/leanprover-community/mathlib/commit/aacd757)
feat(measurable_space): more properties of measurable sets in a product ([#3703](https://github.com/leanprover-community/mathlib/pull/3703))
Add multiple lemmas about `prod` to `set.basic`
Some cleanup in `set.basic`
Fix the name of the instance `measure_space ℝ`
Cleanup and a couple of additions to the `prod` section of `measurable_space`.
Rename: `prod_singleton_singleton` -> `singleton_prod_singleton`
Use `prod.swap` in the statement of `image_swap_prod`.

### [2020-08-07 00:44:48](https://github.com/leanprover-community/mathlib/commit/49ba4c4)
chore(scripts): update nolints.txt ([#3712](https://github.com/leanprover-community/mathlib/pull/3712))
I am happy to remove some nolints for you!

### [2020-08-06 16:42:35](https://github.com/leanprover-community/mathlib/commit/1930601)
feat(algebra/group_power): lemmas relating pow in `multiplicative int` with multiplication in `int` ([#3706](https://github.com/leanprover-community/mathlib/pull/3706))

### [2020-08-06 16:42:33](https://github.com/leanprover-community/mathlib/commit/35ecc7b)
feat(analysis/calculus): Rolle's and Cauchy's mean value theorems with weaker assumptions (deps : 3590) ([#3681](https://github.com/leanprover-community/mathlib/pull/3681))
This introduces stronger versions of Rolle's theorem and Cauchy's mean value theorem, essentially by encapsulating an extension by continuity using the newly introduced `extend_from` of [#3590](https://github.com/leanprover-community/mathlib/pull/3590)

### [2020-08-06 16:42:31](https://github.com/leanprover-community/mathlib/commit/e57fc3d)
feat(field_theory/splitting_field): splitting field unique ([#3654](https://github.com/leanprover-community/mathlib/pull/3654))
Main theorem:
```lean
polynomial.is_splitting_field.alg_equiv {α} (β) [field α] [field β] [algebra α β]
  (f : polynomial α) [is_splitting_field α β f] : β ≃ₐ[α] splitting_field f
````

### [2020-08-06 15:42:26](https://github.com/leanprover-community/mathlib/commit/bc2bcac)
chore(algebra/module): Move submodule to its own file ([#3696](https://github.com/leanprover-community/mathlib/pull/3696))

### [2020-08-06 14:19:33](https://github.com/leanprover-community/mathlib/commit/224e0f8)
docs(tactic/interactive): Add tag `debugging` and doc `mwe` for `extract_goal` ([#3708](https://github.com/leanprover-community/mathlib/pull/3708))
Requested by @kbuzzard on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Being.20stuck.20-.3E.20MWE/near/206124861).
x-ref: leanprover-community/leanprover-community.github.io[#105](https://github.com/leanprover-community/mathlib/pull/105)

### [2020-08-06 09:35:08](https://github.com/leanprover-community/mathlib/commit/ee7bb12)
chore(ring_theory/ideal): Move ideal modules into a single folder ([#3707](https://github.com/leanprover-community/mathlib/pull/3707))
The main motivation is to fix the odd inconsistency of `ideals` being plural, while most other files have singular names.
Besides that, there seems to be precedent for grouping together such files

### [2020-08-06 06:58:32](https://github.com/leanprover-community/mathlib/commit/3eea109)
feat(measure_theory/interval_integral): introduce `∫ x in a..b, f x`, prove FTC-1 ([#3640](https://github.com/leanprover-community/mathlib/pull/3640))
Define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. With this definition for a probability measure `μ` we have `F_μ(b)-F_μ(a)=∫ x in a..b, f x ∂μ`, where `F_μ` is the cumulative distribution function.

### [2020-08-06 03:47:24](https://github.com/leanprover-community/mathlib/commit/5cba21d)
chore(*): swap order of [fintype A] [decidable_eq A] ([#3705](https://github.com/leanprover-community/mathlib/pull/3705))
@fpvandoorn  suggested in [#3603](https://github.com/leanprover-community/mathlib/pull/3603) swapping the order of some `[fintype A] [decidable_eq A]` arguments to solve a linter problem with slow typeclass lookup.
The reasoning is that Lean solves typeclass search problems from right to left, and 
* it's "less likely" that a type is a `fintype` than it has `decidable_eq`, so we can fail earlier if `fintype` comes second
* typeclass search for `[decidable_eq]` can already be slow, so it's better to avoid it.
This PR applies this suggestion across the library.

### [2020-08-06 00:42:41](https://github.com/leanprover-community/mathlib/commit/f8fd0c3)
chore(scripts): update nolints.txt ([#3704](https://github.com/leanprover-community/mathlib/pull/3704))
I am happy to remove some nolints for you!

### [2020-08-05 22:44:03](https://github.com/leanprover-community/mathlib/commit/9d3c709)
chore(algebra/module): Reuse proofs from subgroup ([#3631](https://github.com/leanprover-community/mathlib/pull/3631))
Confusingly these have opposite names - someone can always fix the names later though.

### [2020-08-05 22:44:01](https://github.com/leanprover-community/mathlib/commit/2918b00)
feat(topology): define `extend_from`, add lemmas about extension by continuity on sets and intervals and continuity gluing ([#3590](https://github.com/leanprover-community/mathlib/pull/3590))
#### Add a new file `topology/extend_from_subset` (mostly by @PatrickMassot )
Define `extend_from A f` (where `f : X → Y` and `A : set X`) to be a function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists. Although this is not really an extension, it maps with the classical meaning of extending a function *defined on a set*, hence the name. In some way it is analogous to `dense_inducing.extend`, but in `set` world.
The main theorem about this is `continuous_on_extend_from` about extension by continuity
#### Corollaries for extending functions defined on intervals
A few lemmas of the form : if `f` is continuous on `Ioo a b`, then `extend_from (Ioo a b) f` is continuous on `I[cc/co/oc] a b`, provided some assumptions about limits on the boundary (and has some other properties, e.g it is equal to `f` on `Ioo a b`)
#### More general continuity gluing
Lemmas `continuous_on_if'` and its corollaries `continuous_on_if` and `continuous_if'`, and a few other continuity lemmas

### [2020-08-05 21:26:53](https://github.com/leanprover-community/mathlib/commit/89ada87)
chore(algebra, data/pnat): refactoring comm_semiring_has_dvd into comm_monoid_has_dvd ([#3702](https://github.com/leanprover-community/mathlib/pull/3702))
changes the instance comm_semiring_has_dvd to apply to any comm_monoid
cleans up the pnat API to use this new definition

### [2020-08-05 19:30:40](https://github.com/leanprover-community/mathlib/commit/13d4fbe)
feat(tactic/interactive_attr): `@[interactive]` attribute to export interactive tactics ([#3698](https://github.com/leanprover-community/mathlib/pull/3698))
Allows one to write 
```lean
@[interactive]
meta def my_tactic := ...
```
instead of
```lean
meta def my_tactic := ...
run_cmd add_interactive [``my_tactic]
```

### [2020-08-05 16:34:55](https://github.com/leanprover-community/mathlib/commit/5fc6281)
chore(data/matrix/basic): rename _val lemmas to _apply ([#3297](https://github.com/leanprover-community/mathlib/pull/3297))
We use `_apply` for lemmas about applications of functions to arguments. Arguably "picking out the entries of a matrix" could warrant a different name, but as we treat matrices just as functions all over, I think it's better to use the usual names.

### [2020-08-05 15:41:26](https://github.com/leanprover-community/mathlib/commit/d952e8b)
chore(topology/category/Top/opens): module-doc, cleanup, and construct some morphisms ([#3601](https://github.com/leanprover-community/mathlib/pull/3601))

### [2020-08-05 11:37:40](https://github.com/leanprover-community/mathlib/commit/c63dad1)
chore(ring_theory/ideals): Move the definition of ideals out of algebra/module ([#3692](https://github.com/leanprover-community/mathlib/pull/3692))
Neatness was the main motivation - it makes it easier to reason about what would need doing in [#3635](https://github.com/leanprover-community/mathlib/pull/3635).
It also results in somewhere sensible for the docs about ideals. Also adds a very minimal docstring to `ring_theory/ideals.lean`.

### [2020-08-05 11:37:36](https://github.com/leanprover-community/mathlib/commit/4a82e84)
feat(algebra/*/ulift): algebraic instances for ulift ([#3675](https://github.com/leanprover-community/mathlib/pull/3675))

### [2020-08-05 10:42:04](https://github.com/leanprover-community/mathlib/commit/2b9ac69)
feat(linear_algebra/affine_space): faces of simplices ([#3691](https://github.com/leanprover-community/mathlib/pull/3691))
Define a `face` of an `affine_space.simplex` with any given nonempty
subset of the vertices, using `finset.mono_of_fin`.

### [2020-08-05 10:42:02](https://github.com/leanprover-community/mathlib/commit/ecb5c5f)
docs(algebra/module): Remove completed TODO ([#3690](https://github.com/leanprover-community/mathlib/pull/3690))
Today, submodule _does_ extend `add_submonoid`, which is I assume what this TODO was about

### [2020-08-05 10:42:00](https://github.com/leanprover-community/mathlib/commit/0531cb0)
feat(algebra/classical_lie_algebras): add definitions of missing classical Lie algebras ([#3661](https://github.com/leanprover-community/mathlib/pull/3661))
Copying from the comments I have added at the top of `classical_lie_algebras.lean`:
## Main definitions
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`

### [2020-08-05 09:56:01](https://github.com/leanprover-community/mathlib/commit/37119b4)
feat(topology): normed spaces are (locally) path connected ([#3689](https://github.com/leanprover-community/mathlib/pull/3689))

### [2020-08-05 09:09:06](https://github.com/leanprover-community/mathlib/commit/545186c)
refactor(*): add a notation for `nhds_within` ([#3683](https://github.com/leanprover-community/mathlib/pull/3683))
The definition is still there and can be used too.

### [2020-08-05 08:29:26](https://github.com/leanprover-community/mathlib/commit/3b26878)
feat(linear_algebra/affine_space): more lemmas ([#3615](https://github.com/leanprover-community/mathlib/pull/3615))
Add further lemmas on affine spaces.  This is the last piece of
preparation needed on the affine space side for my definitions of
`circumcenter` and `circumradius` for a simplex in a Euclidean affine
space.

### [2020-08-04 18:21:00](https://github.com/leanprover-community/mathlib/commit/84b450d)
feat(topology): path connected spaces ([#3627](https://github.com/leanprover-community/mathlib/pull/3627))
From the sphere eversion project.

### [2020-08-04 16:33:38](https://github.com/leanprover-community/mathlib/commit/f4b2790)
feat(data/list/defs): add monadic versions of list.{find,any,all,bor,band} ([#3679](https://github.com/leanprover-community/mathlib/pull/3679))
Also universe-generalise `mfind` while I'm at it.

### [2020-08-04 13:40:24](https://github.com/leanprover-community/mathlib/commit/3ae6cea)
feat(group_theory/submonoid/operations): transfer galois connection/insertion lemmas ([#3657](https://github.com/leanprover-community/mathlib/pull/3657))

### [2020-08-04 10:47:06](https://github.com/leanprover-community/mathlib/commit/78fe862)
chore(measure_theory/lebesgue_measure): review ([#3686](https://github.com/leanprover-community/mathlib/pull/3686))
* use `ennreal.of_real` instead of `coe ∘ nnreal.of_real`;
* avoid some non-finishing `simp`s;
* simplify proofs of `lebesgue_outer_Ico/Ioc/Ioo`;
* add `instance : locally_finite_measure (volume : measure ℝ)`
  instead of `real.volume_lt_top_of_bounded` and
  `real.volume_lt_top_of_compact`.

### [2020-08-04 10:47:04](https://github.com/leanprover-community/mathlib/commit/8f02ad2)
feat(geometry/euclidean): orthogonal projection ([#3662](https://github.com/leanprover-community/mathlib/pull/3662))
Define orthogonal projection onto an affine subspace of a Euclidean
affine space, and prove some basic lemmas about it.

### [2020-08-04 09:49:04](https://github.com/leanprover-community/mathlib/commit/14d206b)
feat(order/filter/interval): define class `filter.is_interval_generated` ([#3663](https://github.com/leanprover-community/mathlib/pull/3663))

### [2020-08-04 09:49:02](https://github.com/leanprover-community/mathlib/commit/ed377e1)
feat(analysis/convex): a local minimum of a convex function is a global minimum ([#3613](https://github.com/leanprover-community/mathlib/pull/3613))

### [2020-08-04 09:09:02](https://github.com/leanprover-community/mathlib/commit/b4a6651)
chore(order/filter/at_top_bot): golf three proofs ([#3684](https://github.com/leanprover-community/mathlib/pull/3684))
Also add `is_countably_generated_at_top`.

### [2020-08-04 07:11:52](https://github.com/leanprover-community/mathlib/commit/b0de811)
chore(measure_theory/borel_space): DRY by using `order_dual` ([#3685](https://github.com/leanprover-community/mathlib/pull/3685))

### [2020-08-04 02:05:22](https://github.com/leanprover-community/mathlib/commit/d9a6e47)
feat(measure_theory/group): regular, invariant, and conjugate measures ([#3650](https://github.com/leanprover-community/mathlib/pull/3650))
Define the notion of a regular measure. I did this in Borel space, which required me to add an import measure_space -> borel_space.
Define left invariant and right invariant measures for groups
Define the conjugate measure, and show it is left invariant iff the original is right invariant

### [2020-08-04 00:36:52](https://github.com/leanprover-community/mathlib/commit/acedda0)
chore(scripts): update nolints.txt ([#3682](https://github.com/leanprover-community/mathlib/pull/3682))
I am happy to remove some nolints for you!

### [2020-08-03 20:53:03](https://github.com/leanprover-community/mathlib/commit/b215e95)
fix(data/set/intervals/basic): fix a typo ([#3680](https://github.com/leanprover-community/mathlib/pull/3680))

### [2020-08-03 20:53:01](https://github.com/leanprover-community/mathlib/commit/234011d)
chore(order/filter/lift): prove `has_basis.lift` and `has_basis.lift'` ([#3618](https://github.com/leanprover-community/mathlib/pull/3618))

### [2020-08-03 19:22:21](https://github.com/leanprover-community/mathlib/commit/50d1c48)
feat(order/galois_connection): galois_coinsertions ([#3656](https://github.com/leanprover-community/mathlib/pull/3656))

### [2020-08-03 19:22:19](https://github.com/leanprover-community/mathlib/commit/40c6a29)
feat(measure_theory/content): define outer measure from content ([#3649](https://github.com/leanprover-community/mathlib/pull/3649))
Part of the development for the Haar measure: define an outer measure from a content.

### [2020-08-03 17:57:40](https://github.com/leanprover-community/mathlib/commit/018309f)
chore(linear_algebra/basis): replace explicit arguments for 0 ≠ 1 with nontrivial R ([#3678](https://github.com/leanprover-community/mathlib/pull/3678))

### [2020-08-03 17:57:38](https://github.com/leanprover-community/mathlib/commit/6186c69)
feat(group_theory/subgroup): range_gpowers_hom ([#3677](https://github.com/leanprover-community/mathlib/pull/3677))

### [2020-08-03 17:57:36](https://github.com/leanprover-community/mathlib/commit/b8df8aa)
feat(algebra/ring): the codomain of a ring hom is trivial iff ... ([#3676](https://github.com/leanprover-community/mathlib/pull/3676))
In the discussion of [#3488](https://github.com/leanprover-community/mathlib/pull/3488), Johan (currently on vacation, so I'm not pinging him) noted that we were missing the lemma "if `f` is a ring homomorphism, `∀ x, f x = 0` implies that the codomain is trivial". This PR adds a couple of ways to derive from homomorphisms that rings are trivial.
I used `0 = 1` to express that the ring is trivial because that seems to be the one that is used in practice.

### [2020-08-03 17:57:34](https://github.com/leanprover-community/mathlib/commit/5f9e427)
feat(analysis/normed_space/add_torsor): isometries of normed_add_torsors ([#3666](https://github.com/leanprover-community/mathlib/pull/3666))
Add the lemma that an isometry of `normed_add_torsor`s induces an
isometry of the corresponding `normed_group`s at any base point.
Previously discussed on Zulip, see
<https://leanprover-community.github.io/archive/stream/113488-general/topic/Undergraduate.20math.20list.html[#199450039](https://github.com/leanprover-community/mathlib/pull/199450039)>;
both statement and proof have been revised along the lines indicated
in that discussion.

### [2020-08-03 17:57:32](https://github.com/leanprover-community/mathlib/commit/aef7ade)
feat(data/set/intervals): a few lemmas needed by FTC-1 ([#3653](https://github.com/leanprover-community/mathlib/pull/3653))

### [2020-08-03 16:25:13](https://github.com/leanprover-community/mathlib/commit/c6381aa)
chore(algebra/group_ring_action): docstring, move monoid.End to algebra/group/hom ([#3671](https://github.com/leanprover-community/mathlib/pull/3671))

### [2020-08-03 14:09:09](https://github.com/leanprover-community/mathlib/commit/b2be1ee)
feat(measure_theory/measure_space): add 3 typeclasses ([#3664](https://github.com/leanprover-community/mathlib/pull/3664))
Define `probability_measure`, `finite_measure`, and `locally_finite_measure`.

### [2020-08-03 11:29:40](https://github.com/leanprover-community/mathlib/commit/3781435)
feat(algebra/category/Group): the category of abelian groups is abelian ([#3621](https://github.com/leanprover-community/mathlib/pull/3621))

### [2020-08-03 11:29:38](https://github.com/leanprover-community/mathlib/commit/6079ef9)
feat(analysis/normed_space/real_inner_product): orthogonal projection ([#3563](https://github.com/leanprover-community/mathlib/pull/3563))
`analysis.normed_space.real_inner_product` proves the existence of
orthogonal projections onto complete subspaces, but only in the form
of an existence theorem without a corresponding `def` for the function
that is proved to exist.  Add the corresponding `def` of
`orthogonal_projection` as a `linear_map` and lemmas with the basic
properties, extracted from the existing results with `some` and
`some_spec`.
For convenience in constructing the `linear_map`, some lemmas are
first proved for a version of the orthogonal projection as an
unbundled function, then used in the definition of the bundled
`linear_map` version, then restarted for the bundled version (the two
versions of each lemma being definitionally equal; the bundled version
is considered the main version that should be used in all subsequent
code).
This is preparation for defining the corresponding operation for
Euclidean affine spaces as an `affine_map`.

### [2020-08-03 10:04:53](https://github.com/leanprover-community/mathlib/commit/8e0d111)
feat(data/finset/lattice,data/finset/sort): singleton lemmas ([#3668](https://github.com/leanprover-community/mathlib/pull/3668))
Add lemmas about `min'`, `max'` and `mono_of_fin` for a singleton
`finset`.

### [2020-08-03 10:04:51](https://github.com/leanprover-community/mathlib/commit/61db67d)
chore(measure_theory/integration): define composition of a `simple_func` and a measurable function ([#3667](https://github.com/leanprover-community/mathlib/pull/3667))

### [2020-08-03 10:04:49](https://github.com/leanprover-community/mathlib/commit/292c921)
doc(category_theory): add library note about 'dsimp, simp' pattern ([#3659](https://github.com/leanprover-community/mathlib/pull/3659))

### [2020-08-03 09:08:57](https://github.com/leanprover-community/mathlib/commit/3d41e33)
feat(group_theory/submonoid/operations): mrange_eq_map ([#3673](https://github.com/leanprover-community/mathlib/pull/3673))

### [2020-08-03 08:41:40](https://github.com/leanprover-community/mathlib/commit/d3e1f5f)
feat(README): add @Vierkantor to maintainer list ([#3674](https://github.com/leanprover-community/mathlib/pull/3674))

### [2020-08-03 07:29:19](https://github.com/leanprover-community/mathlib/commit/d6c17c9)
feat(linear_algebra/affine_space): simplex ext lemmas ([#3669](https://github.com/leanprover-community/mathlib/pull/3669))
Add `ext` lemmas for `affine_space.simplex`.

### [2020-08-03 05:29:42](https://github.com/leanprover-community/mathlib/commit/60ba478)
feat(algebra/category/Module): the category of R-modules is abelian ([#3606](https://github.com/leanprover-community/mathlib/pull/3606))

### [2020-08-03 00:42:24](https://github.com/leanprover-community/mathlib/commit/fb883ea)
chore(scripts): update nolints.txt ([#3670](https://github.com/leanprover-community/mathlib/pull/3670))
I am happy to remove some nolints for you!

### [2020-08-02 22:03:03](https://github.com/leanprover-community/mathlib/commit/06df503)
chore(analysis/calculus/times_cont_diff): transpose lemmas ([#3665](https://github.com/leanprover-community/mathlib/pull/3665))
In [#3639](https://github.com/leanprover-community/mathlib/pull/3639) , I accidentally placed the new lemma `times_cont_diff_at_inverse` between `times_cont_diff_at.prod_map'` and `times_cont_diff.prod_map`.  This fixes that.

### [2020-08-02 16:01:03](https://github.com/leanprover-community/mathlib/commit/4588400)
chore(group_theory/*): refactor quotient groups to use bundled subgroups ([#3321](https://github.com/leanprover-community/mathlib/pull/3321))

### [2020-08-02 11:46:51](https://github.com/leanprover-community/mathlib/commit/6559832)
feat(order/filter/lift): a few lemmas about `filter.lift' _ powerset` ([#3652](https://github.com/leanprover-community/mathlib/pull/3652))

### [2020-08-02 11:46:49](https://github.com/leanprover-community/mathlib/commit/fe4da7b)
feat(category_theory/limits): transporting is_limit ([#3598](https://github.com/leanprover-community/mathlib/pull/3598))
Some lemmas about moving `is_limit` terms around over equivalences, or (post|pre)composing.

### [2020-08-02 11:46:47](https://github.com/leanprover-community/mathlib/commit/52c0b42)
feat(category_theory): Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D ([#3576](https://github.com/leanprover-community/mathlib/pull/3576))
When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.
This is formalised as:
* `Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`
The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

### [2020-08-02 11:46:45](https://github.com/leanprover-community/mathlib/commit/e99518b)
feat(category_theory): braided and symmetric categories ([#3550](https://github.com/leanprover-community/mathlib/pull/3550))
Just the very basics:
* the definition of braided and symmetric categories
* braided functors, and compositions thereof
* the symmetric monoidal structure coming from products
* upgrading `Type u` to a symmetric monoidal structure
This is prompted by the desire to explore modelling sheaves of modules as the monoidal category of module objects for an internal commutative monoid in sheaves of `Ab`.

### [2020-08-02 11:46:43](https://github.com/leanprover-community/mathlib/commit/8c1e2da)
feat(linear_algebra/tensor_algebra): Tensor algebras ([#3531](https://github.com/leanprover-community/mathlib/pull/3531))
This PR constructs the tensor algebra of a module over a commutative ring.
The main components are:
1. The construction of the tensor algebra: `tensor_algebra R M` for a module `M` over a commutative ring `R`.
2. The linear map `univ R M` from `M` to `tensor_algebra R M`.
3. Given a linear map `f`from `M`to an `R`-algebra `A`, the lift of `f` to `tensor_algebra R M` is denoted `lift R M f`.
4. A theorem `univ_comp_lift` asserting that the composition of `univ R M` with `lift R M f`is `f`.
5. A theorem `lift_unique` asserting the uniqueness of `lift R M f`with respect to property 4.

### [2020-08-02 10:18:28](https://github.com/leanprover-community/mathlib/commit/58f2c36)
feat(dynamics/periodic_pts): definition and basic properties ([#3660](https://github.com/leanprover-community/mathlib/pull/3660))
Also add more lemmas about `inj/surj/bij_on` and `maps_to`.

### [2020-08-02 08:31:21](https://github.com/leanprover-community/mathlib/commit/78655b6)
feat(data/set/intervals): define `set.ord_connected` ([#3647](https://github.com/leanprover-community/mathlib/pull/3647))
A set `s : set α`, `[preorder α]` is `ord_connected` if for
any `x y ∈ s` we have `[x, y] ⊆ s`. For real numbers this property
is equivalent to each of the properties `convex s`
and `is_preconnected s`. We define it for any `preorder`, prove some
basic properties, and migrate lemmas like `convex_I??` and
`is_preconnected_I??` to this API.

### [2020-08-02 08:31:19](https://github.com/leanprover-community/mathlib/commit/f2db6a8)
chore(algebra/order): enable dot syntax ([#3643](https://github.com/leanprover-community/mathlib/pull/3643))
Add dot syntax aliases to some lemmas about order (e.g.,
`has_le.le.trans`). Also remove `lt_of_le_of_ne'` (was equivalent
to `lt_of_le_of_ne`).

### [2020-08-02 06:44:24](https://github.com/leanprover-community/mathlib/commit/6394e4d)
feat(algebra/category/*): forget reflects isos ([#3600](https://github.com/leanprover-community/mathlib/pull/3600))

### [2020-08-02 04:10:31](https://github.com/leanprover-community/mathlib/commit/d76c75e)
feat(measure_theory): cleanup and generalize measure' ([#3648](https://github.com/leanprover-community/mathlib/pull/3648))
There were two functions `measure'` and `outer_measure'` with undescriptive names, and which were not very general
rename `measure'` -> `extend`
rename `outer_measure'` -> `induced_outer_measure`
generalize both `extend` and `induced_outer_measure` to an arbitrary subset of `set α` (instead of just the measurable sets). Most lemmas still hold in full generality, sometimes with a couple more assumptions. For the lemmas that need more assumptions, we have also kept the version that is just for `is_measurable`.
Move functions `extend`, `induced_outer_measure` and `trim` to `outer_measure.lean`.
rename `caratheodory_is_measurable` -> `of_function_caratheodory`
rename `trim_ge` -> `le_trim`
Make the section on caratheodory sets not private (and give a more descriptive name to lemmas).
Style in `measurable_space` and `outer_measure`

### [2020-08-02 03:20:12](https://github.com/leanprover-community/mathlib/commit/fc65ba0)
feat(analysis/calculus/times_cont_diff): inversion is smooth ([#3639](https://github.com/leanprover-community/mathlib/pull/3639))
At an invertible element of a complete normed algebra, the inversion operation is smooth.

### [2020-08-02 02:10:22](https://github.com/leanprover-community/mathlib/commit/d3de289)
feat(topology/local_homeomorph): open_embedding.continuous_at_iff ([#3599](https://github.com/leanprover-community/mathlib/pull/3599))
```
lemma continuous_at_iff
  {f : α → β} {g : β → γ} (hf : open_embedding f) {x : α} :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
```

### [2020-08-01 21:07:07](https://github.com/leanprover-community/mathlib/commit/4274ddd)
chore(*): bump to Lean 3.18.4 ([#3610](https://github.com/leanprover-community/mathlib/pull/3610))
* Remove `pi_arity` and the `vm_override` for `by_cases`, which have moved to core
* Fix fallout from the change to the definition of `max`
* Fix a small number of errors caused by changes to instance caching
* Remove `min_add`, which is generalized by `min_add_add_right`  and make `to_additive` generate some lemmas

### [2020-08-01 15:55:33](https://github.com/leanprover-community/mathlib/commit/92a20e6)
feat(order/filter/extr, topology/local_extr): links between extremas of two eventually le/eq functions ([#3624](https://github.com/leanprover-community/mathlib/pull/3624))
Add many lemmas that look similar to e.g : if f and g are equal at `a`, and `f ≤ᶠ[l] g` for some filter `l`, then `is_min_filter l f a`implies `is_min_filter l g a`

### [2020-08-01 12:08:21](https://github.com/leanprover-community/mathlib/commit/aa67315)
chore(order/filter/bases): generalize `has_basis.restrict` ([#3645](https://github.com/leanprover-community/mathlib/pull/3645))
The old lemma is renamed to `filter.has_basis.restrict_subset`

### [2020-08-01 09:06:29](https://github.com/leanprover-community/mathlib/commit/c6f3399)
feat(topology/subset_properties): add `is_compact.induction_on` ([#3642](https://github.com/leanprover-community/mathlib/pull/3642))