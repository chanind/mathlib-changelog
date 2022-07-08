### [2020-06-30 22:34:44](https://github.com/leanprover-community/mathlib/commit/0625691)
chore(topology/*): use dot syntax for some lemmas ([#3251](https://github.com/leanprover-community/mathlib/pull/3251))
Rename:
* `closure_eq_of_is_closed` to `is_closed.closure_eq`;
* `closed_of_compact` to `compact.is_closed`;
* `bdd_above_of_compact` to `compact.bdd_above`;
* `bdd_below_of_compact` to `compact.bdd_below`.
* `is_complete_of_is_closed` to `is_closed.is_complete`
* `is_closed_of_is_complete` to `is_complete.is_closed`
* `is_closed_iff_nhds` to `is_closed_iff_cluster_pt`
* `closure_subset_iff_subset_of_is_closed` to `is_closed.closure_subset_iff`
Add:
* `closure_closed_ball` (`@[simp]` lemma)
* `is_closed.closure_subset : is_closed s → closure s ⊆ s`

### [2020-06-30 17:14:16](https://github.com/leanprover-community/mathlib/commit/b391563)
feat(algebra/lie_algebra): conjugation transformation for Lie algebras of skew-adjoint endomorphims, matrices ([#3229](https://github.com/leanprover-community/mathlib/pull/3229))
The two main results are the lemmas:
 * skew_adjoint_lie_subalgebra_equiv
 * skew_adjoint_matrices_lie_subalgebra_equiv
The latter is expected to be useful when defining the classical Lie algebras
of type B and D.

### [2020-06-30 16:18:08](https://github.com/leanprover-community/mathlib/commit/ea961f7)
chore(ring_theory/polynomial): move `ring_theory.polynomial` to `ring_theory.polynomial.basic` ([#3248](https://github.com/leanprover-community/mathlib/pull/3248))
This PR is the intersection of [#3223](https://github.com/leanprover-community/mathlib/pull/3223) and [#3241](https://github.com/leanprover-community/mathlib/pull/3241), allowing them to be merged in either order.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/where.20should.20these.20definitions.20live.3F

### [2020-06-30 14:58:52](https://github.com/leanprover-community/mathlib/commit/9524dee)
feat(topology): real.image_Icc ([#3224](https://github.com/leanprover-community/mathlib/pull/3224))
The image of a segment under a real-valued continuous function is a segment.

### [2020-06-30 12:42:26](https://github.com/leanprover-community/mathlib/commit/1bc6eba)
fix(tactic/interactive_expr): show let-values in tactic state widget ([#3228](https://github.com/leanprover-community/mathlib/pull/3228))
Fixes the missing let-values in the tactic state widget:
![let_widget](https://user-images.githubusercontent.com/313929/86048315-9d740d80-ba50-11ea-9a8c-09c853687343.png)

### [2020-06-30 11:46:05](https://github.com/leanprover-community/mathlib/commit/b82ed0c)
fix(tactic/apply_fun): beta reduction was too aggressive ([#3214](https://github.com/leanprover-community/mathlib/pull/3214))
The beta reduction performed by `apply_fun` was previously too aggressive -- in particular it was unfolding `A * B` to `A.mul B` when `A` and `B` are matrices. 
This fix avoids using `dsimp`, and instead calls `head_beta` separately on the left and right sides of the new hypothesis.

### [2020-06-30 09:50:40](https://github.com/leanprover-community/mathlib/commit/6d0f40a)
chore(topology/algebra/ordered): use `continuous_at`, rename ([#3231](https://github.com/leanprover-community/mathlib/pull/3231))
* rename `Sup_mem_of_is_closed` and `Inf_mem_of_is_closed` to
  `is_closed.Sup_mem` and `is_closed.Inf_mem`, similarly with
  `cSup` and `cInf`;
* make `Sup_of_continuous` etc take `continuous_at` instead
  of `continuous`, rename to `Sup_of_continuous_at_of_monotone` etc,
  similarly with `cSup`/`cInf`.

### [2020-06-30 08:06:04](https://github.com/leanprover-community/mathlib/commit/a143c38)
refactor(linear_algebra/affine_space): allow empty affine subspaces ([#3219](https://github.com/leanprover-community/mathlib/pull/3219))
When definitions of affine spaces and subspaces were added in [#2816](https://github.com/leanprover-community/mathlib/pull/2816),
there was some discussion of whether an affine subspace should be
allowed to be empty.
After further consideration of what lemmas need to be added to fill
out the interface for affine subspaces, I've concluded that it does
indeed make sense to allow empty affine subspaces, with `nonempty`
hypotheses then added for those results that need them, to avoid
artificial `nonempty` hypotheses for other results on affine spans and
intersections of affine subspaces that don't depend on any way on
affine subspaces being nonempty and can be more cleanly stated if they
can be empty.
Thus, change the definition to allow affine subspaces to be empty and
remove the bundled `direction`.  The new definition of `direction` (as
the `vector_span` of the points in the subspace, i.e. the
`submodule.span` of the `vsub_set` of the points) is the zero
submodule for both empty affine subspaces and for those consisting of
a single point (and it's proved that in the nonempty case it contains
exactly the pairwise subtractions of points in the affine subspace).
This doesn't generally add new lemmas beyond those used in reproving
existing results (including what were previously the `add` and `sub`
axioms for affine subspaces) with the new definitions.  It also
doesn't add the complete lattice structure for affine subspaces, just
helps enable adding it later.

### [2020-06-30 05:20:57](https://github.com/leanprover-community/mathlib/commit/e250eb4)
feat(category/schur): a small corollary of the baby schur's lemma ([#3239](https://github.com/leanprover-community/mathlib/pull/3239))

### [2020-06-30 05:20:54](https://github.com/leanprover-community/mathlib/commit/d788d4b)
chore(data/set/intervals): split `I??_union_I??_eq_I??` ([#3237](https://github.com/leanprover-community/mathlib/pull/3237))
For each lemma `I??_union_I??_eq_I??` add a lemma
`I??_subset_I??_union_I??` with no assumptions.

### [2020-06-30 05:20:51](https://github.com/leanprover-community/mathlib/commit/af53c9d)
chore(algebra/ring): move some classes to `group_with_zero` ([#3232](https://github.com/leanprover-community/mathlib/pull/3232))
Move `nonzero`, `mul_zero_class` and `no_zero_divisors` to
`group_with_zero`: these classes don't need `(+)`.

### [2020-06-30 05:20:45](https://github.com/leanprover-community/mathlib/commit/da481e7)
chore(data/polynomial): partial move from is_ring_hom to ring_hom ([#3213](https://github.com/leanprover-community/mathlib/pull/3213))
This does not attempt to do a complete refactor of `polynomial.lean` and `mv_polynomial.lean` to remove use of `is_ring_hom`, but only to fix `eval₂` which we need for the current work on Cayley-Hamilton.
Having struggled with these two files for the last few days, I'm keen to get them cleaned up, so I'll promise to return to this more thoroughly in a later PR.

### [2020-06-30 04:15:21](https://github.com/leanprover-community/mathlib/commit/38904ac)
feat(data/fintype/basic): card_eq_zero_equiv_equiv_pempty ([#3238](https://github.com/leanprover-community/mathlib/pull/3238))
Adds a constructive equivalence `α ≃ pempty.{v+1}` given `fintype.card α = 0`, which I think wasn't available previously.
I would have stated this as an `iff`, but as the right hand side is data is an `equiv` itself.

### [2020-06-30 04:15:19](https://github.com/leanprover-community/mathlib/commit/1588d81)
feat(category_theory): remove nearly all universe annotations ([#3221](https://github.com/leanprover-community/mathlib/pull/3221))
Due to some recent changes to mathlib (does someone know the relevant versions/commits?) most of the universe annotations `.{v}` and `include 𝒞` statements that were previously needed in the category_theory library are no longer necessary.
This PR removes them!

### [2020-06-30 03:05:21](https://github.com/leanprover-community/mathlib/commit/056a72a)
perf(linarith): don't repeat nonneg proofs for nat-to-int casts ([#3226](https://github.com/leanprover-community/mathlib/pull/3226))
This performance issue showed up particularly when using `nlinarith` over `nat`s. Proofs that `(n : int) >= 0` were being repeated many times, which led to quadratic blowup in the `nlinarith` preprocessing.

### [2020-06-30 03:05:19](https://github.com/leanprover-community/mathlib/commit/791744b)
feat(analysis/normed_space/real_inner_product,geometry/euclidean): inner products of weighted subtractions ([#3203](https://github.com/leanprover-community/mathlib/pull/3203))
Express the inner product of two weighted sums, where the weights in
each sum add to 0, in terms of the norms of pairwise differences.
Thus, express inner products for vectors expressed in terms of
`weighted_vsub` and distances for points expressed in terms of
`affine_combination`.
This is a general form of the standard formula for a distance between
points expressed in terms of barycentric coordinates: if the
difference between the normalized barycentric coordinates (with
respect to triangle ABC) for two points is (x, y, z) then the squared
distance between them is -(a^2 yz + b^2 zx + c^2 xy).
Although some of the lemmas are given with the two vectors expressed
as sums over different indexed families of vectors or points (since
nothing in the statement or proof depends on them being the same), I
expect almost all uses will be in cases where the two indexed families
are the same and only the weights vary.

### [2020-06-30 01:43:20](https://github.com/leanprover-community/mathlib/commit/4fcd6fd)
chore(*): import expression widgets from core ([#3181](https://github.com/leanprover-community/mathlib/pull/3181))
With widgets, the rendering of the tactic state is implemented in pure Lean code.  I would like to move this part (temporarily) into mathlib to facilitate collaborative improvement and rapid iteration under a mature community review procedure.  (That is, I want other people to tweak it themselves without having to wait a week for the next Lean release to see the effect.)
I didn't need to change anything in the source code (except for adding some doc strings).  So it should be easy to copy it back to core if we want to.
There are no changes required to core for this PR.

### [2020-06-30 00:37:07](https://github.com/leanprover-community/mathlib/commit/e8fd085)
chore(scripts): update nolints.txt ([#3234](https://github.com/leanprover-community/mathlib/pull/3234))
I am happy to remove some nolints for you!

### [2020-06-29 19:03:51](https://github.com/leanprover-community/mathlib/commit/45904fb)
chore(*): change notation for `set.compl` ([#3212](https://github.com/leanprover-community/mathlib/pull/3212))
* introduce typeclass `has_compl` and notation `∁` for `has_compl.compl`
* use it instead of `has_neg` for `set` and `boolean_algebra`

### [2020-06-29 16:12:00](https://github.com/leanprover-community/mathlib/commit/d3006ba)
chore(init_/): remove this directory ([#3227](https://github.com/leanprover-community/mathlib/pull/3227))
* remove `init_/algebra`;
* move `init_/data/nat` to `data/nat/basic`;
* move `init_/data/int` to `data/int/basic`.

### [2020-06-29 15:01:42](https://github.com/leanprover-community/mathlib/commit/eb05a94)
feat(order/filter/germ): define `filter.germ` ([#3172](https://github.com/leanprover-community/mathlib/pull/3172))
Actually we already had this definition under the name
`filter_product`.

### [2020-06-29 13:48:28](https://github.com/leanprover-community/mathlib/commit/4907d5d)
feat(algebra/ring): ite_mul_one and ite_mul_zero_... ([#3217](https://github.com/leanprover-community/mathlib/pull/3217))
Three simple lemmas about if statements involving multiplication, useful while rewriting.

### [2020-06-29 13:48:26](https://github.com/leanprover-community/mathlib/commit/964f0e5)
feat(data/polynomial): work over noncommutative rings where possible ([#3193](https://github.com/leanprover-community/mathlib/pull/3193))
After downgrading `C` from an algebra homomorphism to a ring homomorphism in [69931ac](https://github.com/leanprover-community/mathlib/commit/69931acfe7b6a29f988bcf7094e090767b34fb85), which requires a few tweaks, everything else is straightforward.

### [2020-06-29 13:48:23](https://github.com/leanprover-community/mathlib/commit/a708f85)
feat(category/limits/shapes): fix biproducts ([#3175](https://github.com/leanprover-community/mathlib/pull/3175))
This is a second attempt at [#3102](https://github.com/leanprover-community/mathlib/pull/3102).
Previously the definition of a (binary) biproduct in a category with zero morphisms (but not necessarily) preadditive was just wrong.
The definition for a "bicone" was just something that was simultaneously a cone and a cocone, with the same cone points. It was a "biproduct bicone" if the cone was a limit cone and the cocone was a colimit cocone. However, this definition was not particularly useful. In particular, there was no way to prove that the two different `map` constructions providing a morphism `W ⊞ X ⟶ Y ⊞ Z` (i.e. by treating the biproducts either as cones, or as cocones) were actually equal. Blech.
So, I've added the axioms `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q` to `bicone P Q`. (Note these only require the exist of zero morphisms, not preadditivity.)
Now the two map constructions are equal.
I've then entirely removed the `has_preadditive_biproduct` typeclass. Instead we have
1. additional theorems providing `total`, when `preadditive C` is available
2. alternative constructors for `has_biproduct` that use `total` rather than `is_limit` and `is_colimit`.
This PR also introduces some abbreviations along the lines of `abbreviation has_binary_product (X Y : C) := has_limit (pair X Y)`, just to improve readability.

### [2020-06-29 13:48:21](https://github.com/leanprover-community/mathlib/commit/78beab4)
feat(linear_algebra/affine_space): affine independence ([#3140](https://github.com/leanprover-community/mathlib/pull/3140))
Define affine independent indexed families of points (in terms of no
nontrivial `weighted_vsub` in the family being zero), prove that a
family of at most one point is affine independent, and prove a family
of points is affine independent if and only if a corresponding family
of subtractions is linearly independent.
There are of course other equivalent descriptions of affine
independent families it will be useful to add later (that the affine
span of all proper subfamilies is smaller than the affine span of the
whole family, that each point is not in the affine span of the rest;
in the case of a family indexed by a `fintype`, that the dimension of
the affine span is one less than the cardinality).  But I think the
definition and one equivalent formulation is a reasonable starting
point.

### [2020-06-29 12:45:16](https://github.com/leanprover-community/mathlib/commit/36ce13f)
chore(finset/nat/antidiagonal): simplify some proofs ([#3225](https://github.com/leanprover-community/mathlib/pull/3225))
Replace some proofs with `rfl`, and avoid `multiset.to_finset` when there is a `nodup` available.

### [2020-06-29 08:15:17](https://github.com/leanprover-community/mathlib/commit/c4f9176)
feat(linear_algebra/tensor_product): ite_tmul ([#3216](https://github.com/leanprover-community/mathlib/pull/3216))
```
((if P then x₁ else 0) ⊗ₜ[R] x₂) = if P then (x₁ ⊗ₜ x₂) else 0
```
and the symmetric version.

### [2020-06-29 06:59:46](https://github.com/leanprover-community/mathlib/commit/ca44926)
chore(ring_theory/tensor_product): missing simp lemmas ([#3215](https://github.com/leanprover-community/mathlib/pull/3215))
A few missing `simp` lemmas.

### [2020-06-29 04:45:10](https://github.com/leanprover-community/mathlib/commit/a443d8b)
feat(simp_nf): instructions for linter timeout ([#3205](https://github.com/leanprover-community/mathlib/pull/3205))

### [2020-06-29 04:21:12](https://github.com/leanprover-community/mathlib/commit/9a1c0a6)
feat(data/padics/padic_norm) Fix namespacing of padic_val_nat ([#3207](https://github.com/leanprover-community/mathlib/pull/3207))
No longer need we `padic_val_rat.padic_val_nat`.

### [2020-06-29 03:57:10](https://github.com/leanprover-community/mathlib/commit/9acf590)
feat(data/matrix/notation): smul matrix lemmas ([#3208](https://github.com/leanprover-community/mathlib/pull/3208))

### [2020-06-29 03:20:59](https://github.com/leanprover-community/mathlib/commit/d2b46ab)
chore(category_theory/punit): use discrete punit instead of punit ([#3201](https://github.com/leanprover-community/mathlib/pull/3201))
Analogous to [#3191](https://github.com/leanprover-community/mathlib/pull/3191) for `punit`. I also removed some `simp` lemmas which can be generated instead by `[simps]`.

### [2020-06-29 02:24:01](https://github.com/leanprover-community/mathlib/commit/b503fb4)
chore(docs/tutorial): change category declarations ([#3220](https://github.com/leanprover-community/mathlib/pull/3220))
change category declarations to match syntax in recent commit (i.e. no more explicit typeclass naming), delete unnecessary "include" lines as they are no longer needed for Lean to include the typeclass, update tutorial text to explain new syntax

### [2020-06-28 22:51:22](https://github.com/leanprover-community/mathlib/commit/2ec83dc)
chore(group_theory/submonoid): split into 3 files ([#3058](https://github.com/leanprover-community/mathlib/pull/3058))
Now
* `group_theory.submonoid.basic` contains the definition, `complete_lattice` structure, and some basic facts about `closure`;
* `group_theory.submonoid.operations` contains definitions of various operations on submonoids;
* `group_theory.submonoid.membership` contains various facts about membership in a submonoid or the submonoid closure of a set.

### [2020-06-28 22:28:30](https://github.com/leanprover-community/mathlib/commit/4ad82e5)
feat(uniform_space): compact uniform spaces, Heine-Cantor ([#3180](https://github.com/leanprover-community/mathlib/pull/3180))
feat(uniform_space): compact uniform spaces
Compact Hausdorff spaces are uniquely uniformizable and continuous
functions on them are uniformly continuous (Heine-Cantor).

### [2020-06-28 21:26:32](https://github.com/leanprover-community/mathlib/commit/3d72c97)
chore(measure_theory/outer_measure,measure_space): use `complete_lattice_of_Inf/Sup` ([#3185](https://github.com/leanprover-community/mathlib/pull/3185))
Also add a few supporting lemmas about `bsupr`/`binfi` to `order/complete_lattice`

### [2020-06-28 13:39:01](https://github.com/leanprover-community/mathlib/commit/35fbfe0)
fix(tactic/linarith): use refine instead of apply to avoid apply bug ([#3199](https://github.com/leanprover-community/mathlib/pull/3199))
closes [#3142](https://github.com/leanprover-community/mathlib/pull/3142)

### [2020-06-28 09:35:54](https://github.com/leanprover-community/mathlib/commit/da210bf)
doc(contribute/bors.md): update some outdated info ([#3209](https://github.com/leanprover-community/mathlib/pull/3209))

### [2020-06-28 08:10:20](https://github.com/leanprover-community/mathlib/commit/2f6a5f5)
feat(nat, lattice): preliminaries for Haar measure ([#3190](https://github.com/leanprover-community/mathlib/pull/3190))
PR 2/5 to put the Haar measure in mathlib. This PR: results about lattices and lattice operations on `nat`.
add some simp lemmas for `nat.find` (simplifying a proof in `sum_four_squares`)
rename `finset.sup_val` to `finset.sup_def` (it was unused). In PR 3 I will add a new declaration `finset.sup_val`
`Inf_nat_def` and `Sup_nat_def` renamed to `nat.Inf_def` and `nat.Sup_def`, and use `set.nonempty` in statement (they were unused outside that file)

### [2020-06-28 07:12:16](https://github.com/leanprover-community/mathlib/commit/4e2b46a)
feat(algebra/big_operators): add induction principles ([#3197](https://github.com/leanprover-community/mathlib/pull/3197))
add sum_induction and prod_induction

### [2020-06-28 06:01:24](https://github.com/leanprover-community/mathlib/commit/a220286)
feat(subtype): standardize ([#3204](https://github.com/leanprover-community/mathlib/pull/3204))
Add simp lemma from x.val to coe x
Use correct ext/ext_iff naming scheme
Use coe in more places in the library

### [2020-06-28 00:34:00](https://github.com/leanprover-community/mathlib/commit/dd2f1b9)
chore(scripts): update nolints.txt ([#3206](https://github.com/leanprover-community/mathlib/pull/3206))
I am happy to remove some nolints for you!

### [2020-06-27 18:19:16](https://github.com/leanprover-community/mathlib/commit/247fe80)
feat(category_theory/cones): cone functoriality is fully faithful ([#3202](https://github.com/leanprover-community/mathlib/pull/3202))
The functors `cones.functoriality` and `cocones.functoriality` are fully faithful if the transformation functor is as well.

### [2020-06-27 10:10:55](https://github.com/leanprover-community/mathlib/commit/adcd09d)
chore(tactic/linarith): remove final linting error ([#3196](https://github.com/leanprover-community/mathlib/pull/3196))

### [2020-06-27 05:25:00](https://github.com/leanprover-community/mathlib/commit/e7e9f30)
feat(set): preliminaries for Haar measure ([#3189](https://github.com/leanprover-community/mathlib/pull/3189))
`comp_sup_eq_sup_comp` is renamed `comp_sup_eq_sup_comp_of_is_total` and there is a new version that doesn't assume that the order is linear.
`set.image_injective` is renamed `function.injective.image_injective` (in the same way as the existing `function.surjective.preimage_injective`). `set.image_injective` is now an `iff`.

### [2020-06-27 03:21:26](https://github.com/leanprover-community/mathlib/commit/8413b3f)
feat(analysis/normed_space/real_inner_product): sums and bilinear form ([#3187](https://github.com/leanprover-community/mathlib/pull/3187))
Add lemmas about distributing the inner product into a sum.  The
natural approach to proving those seems to be to use the corresponding
lemmas for bilinear forms, so also add a construction of a `bilin_form
ℝ α` from the inner product.
I realise this might all get refactored later if inner products get
refactored to cover the case of complex inner products as well.

### [2020-06-27 02:52:56](https://github.com/leanprover-community/mathlib/commit/6ed3325)
feat(category_theory/limits): limit of point iso ([#3188](https://github.com/leanprover-community/mathlib/pull/3188))
Prove a cone is a limit given that the canonical morphism from it to a limiting cone is an iso.

### [2020-06-27 00:32:10](https://github.com/leanprover-community/mathlib/commit/c6fd69d)
chore(scripts): update nolints.txt ([#3192](https://github.com/leanprover-community/mathlib/pull/3192))
I am happy to remove some nolints for you!

### [2020-06-26 23:51:42](https://github.com/leanprover-community/mathlib/commit/78d6780)
chore(category_theory/pempty): use discrete pempty instead of a special pempty category ([#3191](https://github.com/leanprover-community/mathlib/pull/3191))
Use `discrete pempty` instead of a specialised `pempty` category.
Motivation: Since we have a good API for `discrete` categories, there doesn't seem to be much point in defining a specialised `pempty` category with an equivalence, instead we might as well just use `discrete pempty`.

### [2020-06-26 16:35:02](https://github.com/leanprover-community/mathlib/commit/2d270ff)
feat(data/set/basic): +2 lemmas, +2 `simp` attrs ([#3182](https://github.com/leanprover-community/mathlib/pull/3182))

### [2020-06-26 15:11:50](https://github.com/leanprover-community/mathlib/commit/ef62d1c)
chore(*): last preparations for Heine ([#3179](https://github.com/leanprover-community/mathlib/pull/3179))
This is hopefully the last preparatory PR before we study compact uniform spaces. It has almost no mathematical content, except that I define `uniform_continuous_on`, and check it is equivalent to uniform continuity for the induced uniformity.

### [2020-06-26 13:39:18](https://github.com/leanprover-community/mathlib/commit/6624509)
feat(algebra/big_operators): telescoping sums ([#3184](https://github.com/leanprover-community/mathlib/pull/3184))
generalize sum_range_sub_of_monotone, a theorem about nats, to a theorem about commutative groups

### [2020-06-26 09:59:19](https://github.com/leanprover-community/mathlib/commit/5b97da6)
feat(ring_theory/matrix_equiv_tensor): matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) ([#3177](https://github.com/leanprover-community/mathlib/pull/3177))
When `A` is an `R`-algebra, matrices over `A` are equivalent (as an algebra) to `A ⊗[R] matrix n n R`.

### [2020-06-26 07:16:55](https://github.com/leanprover-community/mathlib/commit/3cfc0e7)
chore(category/*): linting ([#3178](https://github.com/leanprover-community/mathlib/pull/3178))
Some linting work on `category_theory/`.

### [2020-06-26 06:18:21](https://github.com/leanprover-community/mathlib/commit/c3923e3)
feat(data/fintype): trunc_sigma_of_exists ([#3166](https://github.com/leanprover-community/mathlib/pull/3166))
When working over a `fintype`, you can lift existential statements to `trunc` statements.
This PR adds:
```
def trunc_of_nonempty_fintype {α} (h : nonempty α) [fintype α] : trunc α
def trunc_sigma_of_exists {α} [fintype α] {P : α → Prop} [decidable_pred P] (h : ∃ a, P a) : trunc (Σ' a, P a)
```

### [2020-06-26 01:23:06](https://github.com/leanprover-community/mathlib/commit/616cb5e)
chore(category_theory/equivalence) explicit transitivity transformation ([#3176](https://github.com/leanprover-community/mathlib/pull/3176))
Modifies the construction of the transitive equivalence to be explicit in what exactly the natural transformations are.
The motivation for this is two-fold: firstly we get auto-generated projection lemmas for extracting the functor and inverse, and the natural transformations aren't obscured through `adjointify_η`.

### [2020-06-26 00:34:33](https://github.com/leanprover-community/mathlib/commit/abae5a3)
chore(scripts): update nolints.txt ([#3174](https://github.com/leanprover-community/mathlib/pull/3174))
I am happy to remove some nolints for you!

### [2020-06-25 23:10:54](https://github.com/leanprover-community/mathlib/commit/43a2b24)
feat(tactic/abel) teach abel to gsmul_zero ([#3173](https://github.com/leanprover-community/mathlib/pull/3173))
As reported by Heather Macbeth in:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/limitations.20of.20.60abel.60
`abel` was not negating zero to zero.

### [2020-06-25 16:36:04](https://github.com/leanprover-community/mathlib/commit/db7a53a)
refactor(ring_theory/ideals): make local_ring a prop class ([#3171](https://github.com/leanprover-community/mathlib/pull/3171))

### [2020-06-25 15:51:37](https://github.com/leanprover-community/mathlib/commit/afc1c24)
feat(category/default): comp_dite ([#3163](https://github.com/leanprover-community/mathlib/pull/3163))
Adds lemmas to "distribute" composition over `if` statements.

### [2020-06-25 15:51:35](https://github.com/leanprover-community/mathlib/commit/c6f629b)
feat(category_theory/limits): isos from reindexing limits ([#3100](https://github.com/leanprover-community/mathlib/pull/3100))
Three related constructions which are helpful when identifying "the same limit written different ways".
1. The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
2. We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.
3. The chosen limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.

### [2020-06-25 14:32:01](https://github.com/leanprover-community/mathlib/commit/158e84a)
feat(*): bump to Lean 3.16.5 ([#3170](https://github.com/leanprover-community/mathlib/pull/3170))
There should be no changes required in mathlib.

### [2020-06-25 13:06:57](https://github.com/leanprover-community/mathlib/commit/7d331eb)
chore(*): assorted lemmas about `set` and `finset` ([#3158](https://github.com/leanprover-community/mathlib/pull/3158))

### [2020-06-25 13:06:55](https://github.com/leanprover-community/mathlib/commit/80a0877)
feat(category_theory): show a pullback of a regular mono is regular ([#2780](https://github.com/leanprover-community/mathlib/pull/2780))
And adds two methods for constructing limits which I've found much easier to use in practice.

### [2020-06-25 12:26:52](https://github.com/leanprover-community/mathlib/commit/3f868fa)
feat(filter, topology): cluster_pt and principal notation, redefine compactness ([#3160](https://github.com/leanprover-community/mathlib/pull/3160))
This PR implements what is discussed in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Picking.20sides. It introduces a notation for `filter.principal`, defines `cluster_pt` and uses it to redefine compactness in a way which makes the library more consistent by always putting the neighborhood filter on the left, as in the description of closures and `nhds_within`.

### [2020-06-25 07:40:04](https://github.com/leanprover-community/mathlib/commit/e7db701)
feat(category/adjunction): missing simp lemmas ([#3168](https://github.com/leanprover-community/mathlib/pull/3168))
Just two missing simp lemmas.

### [2020-06-25 07:40:02](https://github.com/leanprover-community/mathlib/commit/d86f1c8)
chore(category/discrete): missing simp lemmas ([#3165](https://github.com/leanprover-community/mathlib/pull/3165))
Some obvious missing `simp` lemmas for `discrete.nat_iso`.

### [2020-06-25 07:40:01](https://github.com/leanprover-community/mathlib/commit/266d316)
chore(category/equivalence): cleanup ([#3164](https://github.com/leanprover-community/mathlib/pull/3164))
Previously some "shorthands" like
```
@[simp] def unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse := e.unit_iso.hom
```
had been added in `equivalence.lean`.
These were a bit annoying, as even though they were marked as `simp` sometimes the syntactic difference between `e.unit` and `e.unit_iso.hom` would get in the way of tactics working.
This PR turns these into abbreviations.
This comes at a slight cost: apparently expressions like `{ X := X }.Y` won't reduce when `.Y` is an abbreviation for `.X.Z`, so we add some `@[simp]` lemmas back in to achieve this.

### [2020-06-25 07:39:59](https://github.com/leanprover-community/mathlib/commit/e8187ac)
feat(category/preadditive): comp_sum ([#3162](https://github.com/leanprover-community/mathlib/pull/3162))
Adds lemmas to distribute composition over `finset.sum`, in a preadditive category.

### [2020-06-25 06:32:59](https://github.com/leanprover-community/mathlib/commit/3875012)
feat(data/quot): add `map'`, `hrec_on'`, and `hrec_on₂'` ([#3148](https://github.com/leanprover-community/mathlib/pull/3148))
Also add a few `simp` lemmas

### [2020-06-25 05:38:59](https://github.com/leanprover-community/mathlib/commit/553e453)
feat(algebra/big_operators): prod_dite_eq ([#3167](https://github.com/leanprover-community/mathlib/pull/3167))
Add `finset.prod_dite_eq`, the dependent analogue of `finset.prod_ite_eq`, and its primed version for the flipped equality.

### [2020-06-25 04:35:29](https://github.com/leanprover-community/mathlib/commit/8f04a92)
refactor(algebra/*): small API fixes ([#3157](https://github.com/leanprover-community/mathlib/pull/3157))
## Changes to `canonically_ordered_comm_semiring`
* in the definition of `canonically_ordered_comm_semiring` replace
  `mul_eq_zero_iff` with `eq_zero_or_eq_zero_of_mul_eq_zero`; the other
  implication is always true because of `[semiring]`;
* add instance `canonically_ordered_comm_semiring.to_no_zero_divisors`;
## Changes to `with_top`
* use `to_additive` for `with_top.has_one`, `with_top.coe_one` etc;
* move `with_top.coe_ne_zero` to `algebra.ordered_group`;
* add `with_top.has_add`, make `coe_add`, `coe_bit*` require only `[has_add α]`;
* use proper instances for lemmas about multiplication in `with_top`, not
  just `canonically_ordered_comm_semiring` for everything;
## Changes to `associates`
* merge `associates.mk_zero_eq` and `associates.mk_eq_zero_iff_eq_zero` into
  `associates.mk_eq_zero`;
* drop `associates.mul_zero`, `associates.zero_mul`, `associates.zero_ne_one`,
  and `associates.mul_eq_zero_iff` in favor of typeclass instances;
## Misc changes
* drop `mul_eq_zero_iff_eq_zero_or_eq_zero` in favor of `mul_eq_zero`;
* drop `ennreal.mul_eq_zero` in favor of `mul_eq_zero` from instance.

### [2020-06-25 01:09:38](https://github.com/leanprover-community/mathlib/commit/e1a72b5)
feat(archive/100-theorems-list/73_ascending_descending_sequences): Erdős–Szekeres ([#3074](https://github.com/leanprover-community/mathlib/pull/3074))
Prove the Erdős-Szekeres theorem on ascending or descending sequences

### [2020-06-25 00:34:07](https://github.com/leanprover-community/mathlib/commit/5c7e1a2)
chore(scripts): update nolints.txt ([#3161](https://github.com/leanprover-community/mathlib/pull/3161))
I am happy to remove some nolints for you!

### [2020-06-24 19:51:54](https://github.com/leanprover-community/mathlib/commit/2aa08c1)
chore(algebra/ordered_group): merge `add_le_add'` with `add_le_add` ([#3159](https://github.com/leanprover-community/mathlib/pull/3159))
Also drop `mul_le_mul''` (was a weaker version of `mul_le_mul'`).

### [2020-06-24 14:36:47](https://github.com/leanprover-community/mathlib/commit/04a5bdb)
feat(linear_algebra/finsupp_vector_space): is_basis.tensor_product ([#3147](https://github.com/leanprover-community/mathlib/pull/3147))
If `b : ι → M` and `c : κ → N` are bases then so is `λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`.

### [2020-06-24 10:22:57](https://github.com/leanprover-community/mathlib/commit/dd9b5c6)
refactor(tactic/linarith): big refactor and docs ([#3113](https://github.com/leanprover-community/mathlib/pull/3113))
This PR:
* Splits `linarith` into multiple files for organizational purposes
* Uses the general `zify` and `cancel_denom` tactics instead of weaker custom versions
* Refactors many components of `linarith`, in particular,
* Modularizes `linarith` preprocessing, so that users can insert custom steps
* Implements `nlinarith` preprocessing as such a custom step, so it happens at the correct point of the preprocessing stage
* Better encapsulates the FM elimination module, to make it easier to plug in alternate oracles if/when they exist
* Docs, docs, docs
The change to zification means that some goals which involved multiplication of natural numbers will no longer be solved. However, others are now in scope. `nlinarith` is a possible drop-in replacement; otherwise, generalize the product of naturals to a single natural, and `linarith` should still succeed.

### [2020-06-24 09:30:51](https://github.com/leanprover-community/mathlib/commit/194edc1)
feat(ring_theory/localization): integral closure in field extension ([#3096](https://github.com/leanprover-community/mathlib/pull/3096))
Let `A` be an integral domain with field of fractions `K` and `L` a finite extension of `K`. This PR shows the integral closure of `A` in `L` has fraction field `L`. If those definitions existed, the corollary is that the ring of integers of a number field is a number ring.
For this, we need two constructions on polynomials:
 * If `p` is a nonzero polynomial, `integral_normalization p` is a monic polynomial with roots `z * a` for `z` a root of `p` and `a` the leading coefficient of `p`
 * If `f` is the localization map from `A` to `K` and `p` has coefficients in `K`, then `f.integer_normalization p` is a polynomial with coefficients in `A` (think: `∀ i, is_integer (f.integer_normalization p).coeff i`) with the same roots as `p`.

### [2020-06-24 07:12:51](https://github.com/leanprover-community/mathlib/commit/8ecf53d)
feat(order/filter/countable_Inter): `sup` and `inf` ([#3154](https://github.com/leanprover-community/mathlib/pull/3154))

### [2020-06-24 06:13:13](https://github.com/leanprover-community/mathlib/commit/617b07e)
feat(uniform_space/separation): add separated_set ([#3130](https://github.com/leanprover-community/mathlib/pull/3130))
Also add documentation and simplify the proof of separated => t2 and add the converse.

### [2020-06-24 00:48:46](https://github.com/leanprover-community/mathlib/commit/985cce7)
chore(scripts): update nolints.txt ([#3156](https://github.com/leanprover-community/mathlib/pull/3156))
I am happy to remove some nolints for you!

### [2020-06-24 00:18:26](https://github.com/leanprover-community/mathlib/commit/d57ac08)
feat(field_theory/separable): definition and basic properties ([#3155](https://github.com/leanprover-community/mathlib/pull/3155))

### [2020-06-23 22:02:55](https://github.com/leanprover-community/mathlib/commit/340d5a9)
refactor(geometry/manifold/*): rename to charted_space and tangent_map ([#3103](https://github.com/leanprover-community/mathlib/pull/3103))
@PatrickMassot  had asked some time ago if what is currently called `manifold` in mathlib could be renamed to `charted_space`, and in a recent PR he asked if `bundled_mfderiv` could be called `tangent_map`. Both changes make sense. They are implemented in this PR, together with several tiny improvements to the manifold library.

### [2020-06-23 17:57:24](https://github.com/leanprover-community/mathlib/commit/bc3ed51)
chore(data/set/finite): use dot notation ([#3151](https://github.com/leanprover-community/mathlib/pull/3151))
Rename:
* `finite_insert` to `finite.insert`;
* `finite_union` to `finite.union`;
* `finite_subset` to `finite.subset`;
* `finite_image` to `finite.image`;
* `finite_dependent_image` to `finite.dependent_image`;
* `finite_map` to `finite.map`;
* `finite_image_iff_on` to `finite_image_iff`;
* `finite_preimage` to `finite.preimage`;
* `finite_sUnion` to `finite.sUnion`;
* `finite_bUnion` to `finite.bUnion`, merge with `finite_bUnion'` and
  use `f : Π i ∈ s, set α` instead of `f : ι → set α`;
* `finite_prod` to `finite.prod`;
* `finite_seq` to `finite.seq`;
* `finite_subsets_of_finite` to `finite.finite_subsets`;
* `bdd_above_finite` to `finite.bdd_above`;
* `bdd_above_finite_union` to `finite.bdd_above_bUnion`;
* `bdd_below_finite` to `finite.bdd_below`;
* `bdd_below_finite_union` to `finite.bdd_below_bUnion`.
Delete
* `finite_of_finite_image_on`, was a copy of `finite_of_fintie_image`;
* `finite_bUnion'`: merge with `finite_bUnion` into `finite.bUnion`.

### [2020-06-23 17:15:59](https://github.com/leanprover-community/mathlib/commit/26918a0)
feat(topology/metric_space/baire): define filter `residual` ([#3149](https://github.com/leanprover-community/mathlib/pull/3149))
Fixes [#2265](https://github.com/leanprover-community/mathlib/pull/2265). Also define a typeclass `countable_Inter_filter` and prove that both `residual`
and `μ.ae` have this property.

### [2020-06-23 16:11:19](https://github.com/leanprover-community/mathlib/commit/62e1364)
chore(linear_algebra/nonsingular_inverse): `matrix.nonsing_inv` no longer requires base ring to carry `has_inv` instance ([#3136](https://github.com/leanprover-community/mathlib/pull/3136))

### [2020-06-23 14:59:38](https://github.com/leanprover-community/mathlib/commit/ea665e7)
fix(algebra/ordered*): add norm_cast attribute ([#3132](https://github.com/leanprover-community/mathlib/pull/3132))

### [2020-06-23 13:58:52](https://github.com/leanprover-community/mathlib/commit/d287d34)
refactor(order/filter/basic): define `filter.eventually_eq` ([#3134](https://github.com/leanprover-community/mathlib/pull/3134))
* Define `eventually_eq` (`f =^f[l] g`) and `eventually_le` (`f ≤^f[l] g`).
* Use new notation and definitions in some files.

### [2020-06-23 08:40:54](https://github.com/leanprover-community/mathlib/commit/421ed70)
chore(topology/metric_space/baire): review ([#3146](https://github.com/leanprover-community/mathlib/pull/3146))
* Simplify some proofs in `topology/metric_space/baire`;
* Allow dependency on `hi : i ∈ S` in some `bUnion`/`bInter` lemmas.

### [2020-06-23 08:40:52](https://github.com/leanprover-community/mathlib/commit/159766e)
chore(topology/metric_space/basic): rename `uniform_continuous_dist'` ([#3145](https://github.com/leanprover-community/mathlib/pull/3145))
* rename `uniform_continuous_dist'` to `uniform_continuous_dist`;
* rename `uniform_continuous_dist` to `uniform_continuous.dist`;
* add `uniform_continuous.nndist`.

### [2020-06-23 07:31:42](https://github.com/leanprover-community/mathlib/commit/02d880b)
perf(tactic/cache): call `freeze_local_instances` after `reset_instance_cache` ([#3128](https://github.com/leanprover-community/mathlib/pull/3128))
Calling `unfreeze_local_instances` unfreezes the local instances of the main goal, and thereby disables the type-class cache (for this goal).  It is therefore advisable to call `freeze_local_instances` afterwards as soon as possible.  (The type-class cache will still be trashed when you switch between goals with different local instances, but that's only half as bad as disabling the cache entirely.)
To this end this PR contains several changes:
 * The `reset_instance_cache` function (and `resetI` tactic) immediately call `freeze_local_instances`.
 * The `unfreezeI` tactic is removed.  Instead we introduce `unfreezingI { tac }`, which only temporarily unfreezes the local instances while executing `tac`.  Try to keep `tac` as small as possible.
 * We add `substI h` and `casesI t` tactics (which are short for `unfreezingI { subst h }` and `unfreezingI { casesI t }`, resp.) as abbreviations for the most common uses of `unfreezingI`.
 * Various other uses of `unfreeze_local_instances` are eliminated.  Avoid use of `unfreeze_local_instances` if possible.  Use the `unfreezing tac` combinator instead (the non-interactive version of `unfreezingI`).
See discussion at https://github.com/leanprover-community/mathlib/pull/3113#issuecomment-647150256

### [2020-06-23 04:53:57](https://github.com/leanprover-community/mathlib/commit/c0d74a3)
refactor(group/perm) bundle sign of a perm as a monoid_hom ([#3143](https://github.com/leanprover-community/mathlib/pull/3143))
We're trying to bundle everything right?

### [2020-06-23 03:11:26](https://github.com/leanprover-community/mathlib/commit/23d6141)
chore(algebra/ring,char_zero): generalize some lemmas ([#3141](https://github.com/leanprover-community/mathlib/pull/3141))
`mul_eq_zero` etc only need `[mul_zero_class]` and `[no_zero_divisors]`. In particular, they don't need `has_neg`. Also deduplicate with `group_with_zero.*`.

### [2020-06-23 00:34:00](https://github.com/leanprover-community/mathlib/commit/52abfcf)
chore(scripts): update nolints.txt ([#3144](https://github.com/leanprover-community/mathlib/pull/3144))
I am happy to remove some nolints for you!

### [2020-06-22 20:52:37](https://github.com/leanprover-community/mathlib/commit/b562575)
feat(data/finset): add card_insert_of_mem ([#3137](https://github.com/leanprover-community/mathlib/pull/3137))

### [2020-06-22 19:11:00](https://github.com/leanprover-community/mathlib/commit/36e3b9f)
chore(*): update to Lean 3.16.4c ([#3139](https://github.com/leanprover-community/mathlib/pull/3139))

### [2020-06-22 19:10:58](https://github.com/leanprover-community/mathlib/commit/67844a8)
feat(order/complete_lattice): complete lattice of Sup ([#3138](https://github.com/leanprover-community/mathlib/pull/3138))
Construct a complete lattice from a least upper bound function. 
From a Xena group discussion.

### [2020-06-22 18:22:19](https://github.com/leanprover-community/mathlib/commit/f059336)
fix(algebra/pi_instances): improve definitions of `pi.*` ([#3116](https://github.com/leanprover-community/mathlib/pull/3116))
The new `test/pi_simp.lean` fails with current `master`. Note that
this is a workaround, not a proper fix for `tactic.pi_instance`.
See also [Zulip chat](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60id.60.20in.20pi_instances)
Also use `@[to_additive]` to generate additive definitions, add ordered multiplicative monoids, and add `semimodule (Π i, f i) (Π, g i)`.

### [2020-06-22 16:12:16](https://github.com/leanprover-community/mathlib/commit/54cc126)
feat(data/finset,data/fintype,algebra/big_operators): some more lemmas ([#3124](https://github.com/leanprover-community/mathlib/pull/3124))
Add some `finset`, `fintype` and `algebra.big_operators` lemmas that
were found useful in proving things related to affine independent
families.  (In all cases where results are proved for products, and
then derived for sums where possible using `to_additive`, it was the
result for sums that I actually had a use for.  In the case of
`eq_one_of_card_le_one_of_prod_eq_one` and
`eq_zero_of_card_le_one_of_sum_eq_zero`, `to_additive` couldn't be
used because it also tries to convert the `1` in `s.card ≤ 1` to `0`.)

### [2020-06-22 13:19:55](https://github.com/leanprover-community/mathlib/commit/86dcd5c)
feat(analysis/calculus): C^1 implies strictly differentiable ([#3119](https://github.com/leanprover-community/mathlib/pull/3119))
Over the reals, a continuously differentiable function is strictly differentiable.
Supporting material:  Add a standard mean-value-theorem-related trick as its own lemma, and refactor another proof (in `calculus/extend_deriv`) to use that lemma.
Other material:  an _equality_ (rather than _inequality_) version of the mean value theorem for domains; slight refactor of `normed_space/dual`.

### [2020-06-22 11:57:27](https://github.com/leanprover-community/mathlib/commit/46a8894)
feat(linear_algebra/affine_space): affine combinations for finsets ([#3122](https://github.com/leanprover-community/mathlib/pull/3122))
Extend the definitions of affine combinations over a `fintype` to the
case of sums over a `finset` of an arbitrary index type (which is
appropriate for use cases such as affine independence of a possibly
infinite family of points).
Also change to have only bundled versions of `weighted_vsub_of_point`
and `weighted_vsub`, following review, so avoiding duplicating parts
of `linear_map` API.

### [2020-06-22 10:46:14](https://github.com/leanprover-community/mathlib/commit/105fa17)
feat(linear_algebra/matrix): trace of an endomorphism independent of basis ([#3125](https://github.com/leanprover-community/mathlib/pull/3125))

### [2020-06-22 08:01:57](https://github.com/leanprover-community/mathlib/commit/068aaaf)
chore(data/finmap): nolint ([#3131](https://github.com/leanprover-community/mathlib/pull/3131))

### [2020-06-22 07:22:10](https://github.com/leanprover-community/mathlib/commit/3f9b52a)
refactor(ring_theory/*): make PID class a predicate ([#3114](https://github.com/leanprover-community/mathlib/pull/3114))

### [2020-06-22 00:33:41](https://github.com/leanprover-community/mathlib/commit/6aba958)
chore(scripts): update nolints.txt ([#3133](https://github.com/leanprover-community/mathlib/pull/3133))
I am happy to remove some nolints for you!

### [2020-06-21 21:04:24](https://github.com/leanprover-community/mathlib/commit/d59adc1)
chore(data/list/alist): nolint ([#3129](https://github.com/leanprover-community/mathlib/pull/3129))

### [2020-06-21 19:44:08](https://github.com/leanprover-community/mathlib/commit/5b5ff79)
fix(tactic/delta_instance): bug in computing pi arity ([#3127](https://github.com/leanprover-community/mathlib/pull/3127))

### [2020-06-21 19:09:48](https://github.com/leanprover-community/mathlib/commit/eff9ed3)
feat(topology/uniform_space): some basic lemmas ([#3123](https://github.com/leanprover-community/mathlib/pull/3123))
This is the second PR on the road to Heine. It contains various elementary lemmas about uniform spaces.

### [2020-06-21 17:25:22](https://github.com/leanprover-community/mathlib/commit/7073c8b)
feat(tactic/cancel_denoms): try to remove numeral denominators  ([#3109](https://github.com/leanprover-community/mathlib/pull/3109))

### [2020-06-21 16:23:00](https://github.com/leanprover-community/mathlib/commit/b7d056a)
feat(tactic/zify): move nat propositions to int ([#3108](https://github.com/leanprover-community/mathlib/pull/3108))

### [2020-06-21 15:04:19](https://github.com/leanprover-community/mathlib/commit/d097161)
fix(tactic/set): use provided type for new variable ([#3126](https://github.com/leanprover-community/mathlib/pull/3126))
closes [#3111](https://github.com/leanprover-community/mathlib/pull/3111)

### [2020-06-20 19:21:52](https://github.com/leanprover-community/mathlib/commit/8729fe2)
feat(tactic/simps): option `trace.simps.verbose` prints generated lemmas ([#3121](https://github.com/leanprover-community/mathlib/pull/3121))

### [2020-06-20 15:10:42](https://github.com/leanprover-community/mathlib/commit/e8ff6ff)
feat(*): random lemmas about sets and filters ([#3118](https://github.com/leanprover-community/mathlib/pull/3118))
This is the first in a series of PR that will culminate in a proof of Heine's theorem (a continuous function from a compact separated uniform space to any uniform space is uniformly continuous). I'm slicing a 600 lines files into PRs. This first PR is only about sets, filters and a bit of topology. Uniform spaces stuff will come later.

### [2020-06-20 11:22:01](https://github.com/leanprover-community/mathlib/commit/cd9e8b5)
fix(tactic/group): bugfix for inverse of 1 ([#3117](https://github.com/leanprover-community/mathlib/pull/3117))
The new group tactic made goals like
```lean
example {G : Type*} [group G] (x : G) (h : x = 1) : x = 1 :=
begin
  group, -- x * 1 ^(-1) = 1
  exact h,
end
```
worse, presumably from trying to move the rhs to the lhs we end up with `x * 1^(-1) = 1`, we add a couple more lemmas to try to fix this.

### [2020-06-19 13:54:55](https://github.com/leanprover-community/mathlib/commit/103743e)
doc(tactic/core,uniform_space/basic): minor doc fixes ([#3115](https://github.com/leanprover-community/mathlib/pull/3115))

### [2020-06-19 04:18:45](https://github.com/leanprover-community/mathlib/commit/8e44b9f)
feat(algebra/big_operators): `prod_apply_dite` and `prod_dite` ([#3110](https://github.com/leanprover-community/mathlib/pull/3110))
Generalize `prod_apply_ite` and `prod_ite` to dependent if-then-else. Since the proofs require `prod_attach`, it needed to move to an earlier line.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/prod_ite_eq

### [2020-06-19 00:33:30](https://github.com/leanprover-community/mathlib/commit/56a580d)
chore(scripts): update nolints.txt ([#3112](https://github.com/leanprover-community/mathlib/pull/3112))
I am happy to remove some nolints for you!

### [2020-06-18 22:26:13](https://github.com/leanprover-community/mathlib/commit/ed44541)
chore(*): regularize naming using injective ([#3071](https://github.com/leanprover-community/mathlib/pull/3071))
This begins some of the naming regularization discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/naming.20of.20injectivity.20lemmas
Some general rules:
1. Lemmas should have `injective` in the name iff they have `injective` in the conclusion
2. `X_injective` is preferable to `injective_X`.
3. Unidirectional `inj` lemmas should be dropped in favour of bidirectional ones.
Mostly, this PR tried to fix the names of lemmas that conclude `injective` (also `surjective` and `bijective`, but they seemed to be much better already).
A lot of the changes are from `injective_X` to `X_injective` style

### [2020-06-18 21:08:16](https://github.com/leanprover-community/mathlib/commit/e060c93)
feat(category_theory/discrete): build equivalence from equiv ([#3099](https://github.com/leanprover-community/mathlib/pull/3099))
* renames all the construction building functors/transformations out of discrete categories as `discrete.functor`, `discrete.nat_trans`, `discrete.nat_iso`, rather than names using `of_function`.
* adds `def discrete.equivalence {I J : Type u₁} (e : I ≃ J) : discrete I ≌ discrete J`,
* removes some redundant definitions
* breaks some long lines, 
* and adds doc-strings.

### [2020-06-18 21:08:14](https://github.com/leanprover-community/mathlib/commit/73caeaa)
perf(tactic/linarith): implement redundancy test to reduce number of comparisons ([#3079](https://github.com/leanprover-community/mathlib/pull/3079))
This implements a redundancy check in `linarith` which can drastically reduce the size of the sets of comparisons that the tactic needs to deal with.
`linarith` iteratively transforms sets of inequalities to equisatisfiable sets by eliminating a single variable. If there are `n` comparisons in the set, we expect `O(n^2)` comparisons after one elimination step. Many of these comparisons are redundant, i.e. removing them from the set does not change its satisfiability.
Deciding redundancy is expensive, but there are cheap approximations that are very useful in practice. This PR tests comparisons for non-minimal history (http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13, theorem 7). Non-minimal history implies redundancy.

### [2020-06-18 20:37:24](https://github.com/leanprover-community/mathlib/commit/21bf873)
refactor(category_theory/abelian): use has_finite_products ([#2917](https://github.com/leanprover-community/mathlib/pull/2917))
This doesn't go nearly as far as I wanted.
Really I'd like to factor out `additive`, which is a `preadditive` category with all finite biproducts, and then layer `abelian` on top of that (with (co)kernels and every epi/mono normal).
I can't do that immediately, because:
1. we don't provide the instances from `has_finite_biproducts` to `has_finite_(co)products`
2. we don't define the preadditive version of finite biproducts (we only did the binary ones)
3. hence we don't show that in a preadditive category finite products give rise to finite biproducts
@TwoFX, @b-mehta, if either of you are interested in doing any of these, that would be great. I'll hopefully get to them eventually.

### [2020-06-18 13:45:55](https://github.com/leanprover-community/mathlib/commit/53af714)
chore(*): update to lean 3.16.3 ([#3107](https://github.com/leanprover-community/mathlib/pull/3107))
The changes to mathlib are from https://github.com/leanprover-community/lean/pull/321 which removed some redundant lemmas:
* `int.of_nat_inj` -> `int.of_nat.inj`
* `int.neg_succ_of_nat_inj` -> `int.neg_succ_of_nat.inj`
* `nat.succ_inj` -> `nat.succ.inj`

### [2020-06-18 11:39:55](https://github.com/leanprover-community/mathlib/commit/24792be)
chore(data/finset): minor review ([#3105](https://github.com/leanprover-community/mathlib/pull/3105))

### [2020-06-18 09:54:38](https://github.com/leanprover-community/mathlib/commit/eb5b7fb)
fix(tactic/linarith): don't fail trying to preprocess irrelevant hypotheses ([#3104](https://github.com/leanprover-community/mathlib/pull/3104))

### [2020-06-18 01:11:41](https://github.com/leanprover-community/mathlib/commit/b91909e)
chore(category_theory/closed/cartesian): style ([#3098](https://github.com/leanprover-community/mathlib/pull/3098))
Just breaking long lines, and using braces in a multi-goal proof, for a recently added file.
 ([#2894](https://github.com/leanprover-community/mathlib/pull/2894))

### [2020-06-17 19:57:11](https://github.com/leanprover-community/mathlib/commit/b5baf55)
feat(algebra/linear_ordered_comm_group_with_zero) define linear_ordered_comm_group_with_zero ([#3072](https://github.com/leanprover-community/mathlib/pull/3072))

### [2020-06-17 19:10:21](https://github.com/leanprover-community/mathlib/commit/48c4f40)
refactor(measure_theory): make `volume` a bundled measure ([#3075](https://github.com/leanprover-community/mathlib/pull/3075))
This way we can `apply` and `rw` lemmas about `measure`s without
introducing a `volume`-specific version.

### [2020-06-17 12:07:34](https://github.com/leanprover-community/mathlib/commit/0736c95)
chore(order/filter/basic): move some parts to new files ([#3087](https://github.com/leanprover-community/mathlib/pull/3087))
Move `at_top`/`at_bot`, `cofinite`, and `ultrafilter` to new files.

### [2020-06-17 11:06:54](https://github.com/leanprover-community/mathlib/commit/077cd7c)
feat(algebra/category/Algebra): basic setup for category of bundled R-algebras ([#3047](https://github.com/leanprover-community/mathlib/pull/3047))
Just boilerplate. If I don't run out of enthusiasm I'll do tensor product of R-algebras soon. ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))

### [2020-06-17 09:57:50](https://github.com/leanprover-community/mathlib/commit/54441b5)
feat(algebra/group_action_hom): define equivariant maps ([#2866](https://github.com/leanprover-community/mathlib/pull/2866))

### [2020-06-17 03:12:21](https://github.com/leanprover-community/mathlib/commit/e40de30)
chore(category_theory/closed): move one thing to monoidal closed and fix naming ([#3090](https://github.com/leanprover-community/mathlib/pull/3090))
Move one of the CCC defs to MCC as an example, and make the naming consistent.

### [2020-06-17 00:45:09](https://github.com/leanprover-community/mathlib/commit/a19dca6)
chore(scripts): update nolints.txt ([#3091](https://github.com/leanprover-community/mathlib/pull/3091))
I am happy to remove some nolints for you!

### [2020-06-16 19:33:00](https://github.com/leanprover-community/mathlib/commit/e3c9fd8)
feat(topology): sequential compactness ([#3061](https://github.com/leanprover-community/mathlib/pull/3061))
This is the long overdue PR bringing Bolzano-Weierstrass to mathlib. I'm sorry it's a bit large. I did use a couple of preliminary PRs, that one is really about converging subsequences, but supporting material is spread in many files.

### [2020-06-16 17:58:48](https://github.com/leanprover-community/mathlib/commit/a478f91)
chore(algebra/ring): move `add_mul_self_eq` to `comm_semiring` ([#3089](https://github.com/leanprover-community/mathlib/pull/3089))
Also use `alias` instead of `def ... := @...` to make linter happy.
Fixes https://github.com/leanprover-community/lean/issues/232

### [2020-06-16 17:08:01](https://github.com/leanprover-community/mathlib/commit/ae6bf56)
feat(ring_theory/tensor_product): tensor product of algebras ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))
The R-algebra structure on the tensor product of two R-algebras.

### [2020-06-16 06:49:06](https://github.com/leanprover-community/mathlib/commit/a432a3a)
feat(analysis/convex): Carathéodory's convexity theorem ([#2960](https://github.com/leanprover-community/mathlib/pull/2960))
```
theorem caratheodory (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t
```
and more explicitly
```
theorem eq_center_mass_card_dim_succ_of_mem_convex_hull (s : set E) (x : E) (h : x ∈ convex_hull s) :
  ∃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1)
    (f : E → ℝ), (∀ y ∈ t, 0 ≤ f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x
```

### [2020-06-16 04:03:38](https://github.com/leanprover-community/mathlib/commit/b51028f)
chore(linear_algebra/finite_dimensional): lin-indep lemma typos ([#3086](https://github.com/leanprover-community/mathlib/pull/3086))

### [2020-06-16 02:35:24](https://github.com/leanprover-community/mathlib/commit/e087174)
feat(linear_algebra/finite_dimensional): bases given by finsets ([#3041](https://github.com/leanprover-community/mathlib/pull/3041))
In some cases, it might be more straightforward working with finsets of
the vector space instead of indexed types or carrying around a proof of
set.finite. Also provide a lemma on equal dimension
and basis cardinality lemma that uses a finset basis.

### [2020-06-15 23:58:09](https://github.com/leanprover-community/mathlib/commit/a796008)
feat(category_theory): cartesian closed categories ([#2894](https://github.com/leanprover-community/mathlib/pull/2894))
Cartesian closed categories, from my topos project.

### [2020-06-15 20:59:03](https://github.com/leanprover-community/mathlib/commit/25e414d)
feat(tactic/linarith): nlinarith tactic ([#2637](https://github.com/leanprover-community/mathlib/pull/2637))
Based on Coq's [nra](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.nra) tactic, and requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nonlinear.20linarith).

### [2020-06-15 16:49:19](https://github.com/leanprover-community/mathlib/commit/2e752e1)
feat(tactic/group): group normalization tactic ([#3062](https://github.com/leanprover-community/mathlib/pull/3062))
A tactic to normalize expressions in multiplicative groups.

### [2020-06-15 15:45:46](https://github.com/leanprover-community/mathlib/commit/aa35f36)
feat(analysis/hofer): Hofer's lemma ([#3064](https://github.com/leanprover-community/mathlib/pull/3064))
Adds Hofer's lemma about complete metric spaces, with supporting material.

### [2020-06-15 13:00:34](https://github.com/leanprover-community/mathlib/commit/4843bb1)
chore(linear_algebra/finsupp_vector_space): remove leftover pp.universes ([#3081](https://github.com/leanprover-community/mathlib/pull/3081))
See also [#1608](https://github.com/leanprover-community/mathlib/pull/1608).

### [2020-06-15 08:05:05](https://github.com/leanprover-community/mathlib/commit/758806e)
feat(linear_algebra/affine_space): more on affine subspaces ([#3076](https://github.com/leanprover-community/mathlib/pull/3076))
Add extensionality lemmas for affine subspaces, and a constructor to
make an affine subspace from a point and a direction.

### [2020-06-15 02:06:19](https://github.com/leanprover-community/mathlib/commit/543359c)
feat(field_theory/finite): Chevalley–Warning ([#1564](https://github.com/leanprover-community/mathlib/pull/1564))

### [2020-06-15 01:22:53](https://github.com/leanprover-community/mathlib/commit/3a66d9a)
feat(polynomial): generalising some material to (noncomm_)semiring ([#3043](https://github.com/leanprover-community/mathlib/pull/3043))

### [2020-06-15 00:49:47](https://github.com/leanprover-community/mathlib/commit/01732f7)
chore(scripts): update nolints.txt ([#3078](https://github.com/leanprover-community/mathlib/pull/3078))
I am happy to remove some nolints for you!

### [2020-06-15 00:15:36](https://github.com/leanprover-community/mathlib/commit/c91fc15)
chore(geometry/manifold/real_instances): use euclidean_space ([#3077](https://github.com/leanprover-community/mathlib/pull/3077))
Now that `euclidean_space` has been refactored to use the product topology, we can fix the geometry file that used a version of the product space (with the sup norm!) called `euclidean_space2`, using now instead the proper `euclidean_space`.

### [2020-06-14 20:40:58](https://github.com/leanprover-community/mathlib/commit/c4a32e7)
doc(topology/uniform_space/basic): library note on forgetful inheritance ([#3070](https://github.com/leanprover-community/mathlib/pull/3070))
A (long) library note explaining design decisions related to forgetful inheritance, and reference to this note in various places (I have probably forgotten a few of them).

### [2020-06-14 19:26:34](https://github.com/leanprover-community/mathlib/commit/797177c)
feat(linear_algebra/affine_space): affine combinations of points ([#2979](https://github.com/leanprover-community/mathlib/pull/2979))
Some basic definitions and lemmas related to affine combinations of
points, in preparation for defining barycentric coordinates for use in
geometry.
This version for sums over a `fintype` is probably the most convenient
for geometrical uses (where the type will be `fin 3` in the case of a
triangle, or more generally `fin (n + 1)` for an n-simplex), but other
use cases may find that `finset` or `finsupp` versions of these
definitions are of use as well.
The definition `weighted_vsub` is expected to be used with weights
that sum to zero, and the definition `affine_combination` is expected
to be used with weights that sum to 1, but such a hypothesis is only
specified for lemmas that need it rather than for those definitions.
I expect that most nontrivial geometric uses of barycentric
coordinates will need to prove such a hypothesis at some point, but
that it will still be more convenient not to need to pass it to all
the definitions and trivial lemmas.

### [2020-06-14 16:36:35](https://github.com/leanprover-community/mathlib/commit/77c5dfe)
perf(*): avoid `user_attribute.get_param` ([#3073](https://github.com/leanprover-community/mathlib/pull/3073))
Recent studies have shown that `monoid_localization.lean` is the slowest file in mathlib.  One hundred and three seconds (93%) of its class-leading runtime are spent in constructing the attribute cache for `_to_additive`.  This is due to the use of the `user_attribute.get_param` function inside `get_cache`.  See the [library note on user attribute parameters](https://leanprover-community.github.io/mathlib_docs/notes.html#user%20attribute%20parameters) for more information on this anti-pattern.
This PR removes two uses of `user_attribute.get_param`, one in `to_additive` and the other in `ancestor`.

### [2020-06-14 16:36:33](https://github.com/leanprover-community/mathlib/commit/0d05299)
chore(data/finset): rename `ext`/`ext'`/`ext_iff` ([#3069](https://github.com/leanprover-community/mathlib/pull/3069))
Now
* `ext` is the `@[ext]` lemma;
* `ext_iff` is the lemma `s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂`.
Also add 2 `norm_cast` attributes and a lemma `ssubset_iff_of_subset`.

### [2020-06-14 16:36:31](https://github.com/leanprover-community/mathlib/commit/1f16da1)
refactor(analysis/normed_space/real_inner_product): extend normed_space in the definition ([#3060](https://github.com/leanprover-community/mathlib/pull/3060))
Currently, inner product spaces do not extend normed spaces, and a norm is constructed from the inner product. This makes it impossible to put an instance on reals, because it would lead to two non-defeq norms. We refactor inner product spaces to extend normed spaces, with the condition that the norm is equal (but maybe not defeq) to the square root of the inner product, to solve this issue.
The possibility to construct a norm from a well-behaved inner product is still given by a constructor `inner_product_space.of_core`.
We also register the inner product structure on a finite product of inner product spaces (not on the Pi type, which has the sup norm, but on `pi_Lp 2 one_le_two \alpha` which has the right norm).

### [2020-06-14 15:09:35](https://github.com/leanprover-community/mathlib/commit/85b8bdc)
perf(tactic/linarith): use key/value lists instead of rb_maps to represent linear expressions ([#3004](https://github.com/leanprover-community/mathlib/pull/3004))
This has essentially no effect on the test file, but scales much better. 
See discussion at https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/Real.20analysis for an example which is in reach with this change.

### [2020-06-14 12:37:42](https://github.com/leanprover-community/mathlib/commit/7f60a62)
chore(order/basic): move unbundled order classes to `rel_classes ([#3066](https://github.com/leanprover-community/mathlib/pull/3066))
Reason: these classes are rarely used in `mathlib`, we don't need to mix them with classes extending `has_le`.

### [2020-06-14 12:37:40](https://github.com/leanprover-community/mathlib/commit/2c97f23)
feat(tactic/library_search): small improvements ([#3037](https://github.com/leanprover-community/mathlib/pull/3037))
This makes the following small improvements to `library_search`:
1. ~~Don't use `*.inj` lemmas, which are rarely useful. (Cuts test file from 95 seconds to 90 seconds.)~~
2. Some refactoring for reusability in other tactics.
3. `apply_declaration` now reports how many subgoals were successfully closed by `solve_by_elim` (for use by new tactics)

### [2020-06-14 12:37:38](https://github.com/leanprover-community/mathlib/commit/a6534db)
feat(normed_space/dual): (topological) dual of a normed space ([#3021](https://github.com/leanprover-community/mathlib/pull/3021))
Define the topological dual of a normed space, and prove that over the reals, the inclusion into the double dual is an isometry.
Supporting material:  a corollary of Hahn-Banach; material about spans of singletons added to `linear_algebra.basic` and `normed_space.operator_norm`; material about homotheties added to `normed_space.operator_norm`.

### [2020-06-14 11:55:48](https://github.com/leanprover-community/mathlib/commit/4e88687)
chore(data/complex/basic): rearrange into sections ([#3068](https://github.com/leanprover-community/mathlib/pull/3068))
Also:
* reworded some docstrings,
* removed dependence on `deprecated.field` by changing the proofs of `of_real_div` and `of_real_fpow` to use `ring_hom` lemmas instead of `is_ring_hom` lemma,
* renamed the instance `of_real.is_ring_hom` too `coe.is_ring_hom`,
* renamed `real_prod_equiv*` to `equiv_prod_real*`, and
* `conj_two` was removed in favor of `conj_bit0` and `conj_bit1`.

### [2020-06-14 09:10:57](https://github.com/leanprover-community/mathlib/commit/2cd329f)
feat(algebra/continued_fractions): add correctness of terminating computations ([#2911](https://github.com/leanprover-community/mathlib/pull/2911))
### What
Add correctness lemmas for terminating computations of continued fractions
### Why
To show that the continued fractions algorithm is computing the right thing in case of termination. For non-terminating sequences, lemmas about the limit will be added in a later PR.
### How
1. Show that the value to be approximated can always be obtained by adding the corresponding, remaining fractional part stored in `int_fract_pair.stream`.
2. Use this to derive that once the fractional part becomes 0 (and hence the continued fraction terminates), we have exactly computed the value.

### [2020-06-14 08:08:09](https://github.com/leanprover-community/mathlib/commit/fdc326c)
feat(geometry/euclidean): sum of angles of a triangle ([#2994](https://github.com/leanprover-community/mathlib/pull/2994))
Item 27 from the 100-theorems list.

### [2020-06-14 04:30:41](https://github.com/leanprover-community/mathlib/commit/c8c1869)
refactor(order/basic): make `*order.lift` use `[]` argument ([#3067](https://github.com/leanprover-community/mathlib/pull/3067))
Take an order on the codomain as a `[*order β]` argument.

### [2020-06-14 01:30:16](https://github.com/leanprover-community/mathlib/commit/67f7288)
doc(measure_theory): document basic measure theory files ([#3057](https://github.com/leanprover-community/mathlib/pull/3057))

### [2020-06-14 00:41:33](https://github.com/leanprover-community/mathlib/commit/0f98c37)
chore(scripts): update nolints.txt ([#3065](https://github.com/leanprover-community/mathlib/pull/3065))
I am happy to remove some nolints for you!

### [2020-06-13 19:37:02](https://github.com/leanprover-community/mathlib/commit/e33245c)
feat(topology/metric_space/pi_Lp): L^p distance on finite products ([#3059](https://github.com/leanprover-community/mathlib/pull/3059))
`L^p` edistance (or distance, or norm) on finite products of emetric spaces (or metric spaces, or normed groups), put on a type synonym `pi_Lp p hp α` to avoid instance clashes, and being careful to register as uniformity the product uniformity.

### [2020-06-13 13:42:10](https://github.com/leanprover-community/mathlib/commit/cc16d35)
feat(linear_algebra/finite_dimensional): cardinalities and linear independence ([#3056](https://github.com/leanprover-community/mathlib/pull/3056))

### [2020-06-13 12:38:45](https://github.com/leanprover-community/mathlib/commit/b7048a4)
feat(tactic/linarith): improve parsing expressions into linear form ([#2995](https://github.com/leanprover-community/mathlib/pull/2995))
This PR generalizes the parsing stage of `linarith`. It will try harder to recognize expressions as linear combinations of monomials, and will match monomials up to commutativity. 
```lean
example (u v r s t : ℚ) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u :=
by linarith
```
This is helpful for [#2637](https://github.com/leanprover-community/mathlib/pull/2637) .

### [2020-06-13 11:08:59](https://github.com/leanprover-community/mathlib/commit/4bb29ab)
doc(algebra/group/to_additive): add doc strings and tactic doc entry ([#3055](https://github.com/leanprover-community/mathlib/pull/3055))

### [2020-06-13 11:08:57](https://github.com/leanprover-community/mathlib/commit/a22b657)
refactor(topology/uniform_space): docstring and notation ([#3052](https://github.com/leanprover-community/mathlib/pull/3052))
The goal of this PR is to make `topology/uniform_space/basic.lean` more accessible. 
First it introduces the standard notation for relation composition that was inexplicably not used before. I used a non-standard unicode circle here `\ciw` but this is up for discussion as long as it looks like a composition circle.
Then I introduced balls as discussed on [this Zulip topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/notations.20for.20uniform.20spaces).  There could be used more, but at least this should be mostly sufficient for following PRs.
And of course I put a huge module docstring. As with `order/filter/basic.lean`, I think we need more mathematical explanations than in the average mathlib file.
I also added a bit of content about symmetric entourages but I don't have enough courage to split this off unless someone really insists.

### [2020-06-13 09:51:05](https://github.com/leanprover-community/mathlib/commit/938b73a)
feat(topology/metric_space/pi_lp): Holder and Minkowski inequalities in ennreal ([#2988](https://github.com/leanprover-community/mathlib/pull/2988))
Hölder and Minkowski inequalities for finite sums. Versions for ennreals.

### [2020-06-13 09:19:08](https://github.com/leanprover-community/mathlib/commit/dc69dc3)
refactor(ci): only update nolints once a day ([#3036](https://github.com/leanprover-community/mathlib/pull/3036))
This PR moves the update nolints step to a new GitHub actions workflow `update_nolints.yml` which runs once a day.

### [2020-06-13 07:27:55](https://github.com/leanprover-community/mathlib/commit/1645542)
feat(linear_algebra): elements of a dim zero space ([#3054](https://github.com/leanprover-community/mathlib/pull/3054))

### [2020-06-12 18:08:42](https://github.com/leanprover-community/mathlib/commit/51ad2a1)
chore(*): update to Lean 3.16.2c ([#3053](https://github.com/leanprover-community/mathlib/pull/3053))

### [2020-06-12 18:08:40](https://github.com/leanprover-community/mathlib/commit/ce594be)
feat(linear_algebra/affine_space): define a few affine maps ([#2981](https://github.com/leanprover-community/mathlib/pull/2981))

### [2020-06-12 16:33:01](https://github.com/leanprover-community/mathlib/commit/1429279)
feat(data/*): lemmas converting finset, set.finite, and their card ([#3042](https://github.com/leanprover-community/mathlib/pull/3042))

### [2020-06-12 16:32:59](https://github.com/leanprover-community/mathlib/commit/c955537)
fix(library_search): only unfold reducible definitions when matching ([#3038](https://github.com/leanprover-community/mathlib/pull/3038))
By default `library_search` only unfolds `reducible` definitions
when attempting to match lemmas against the goal.
Previously, it would unfold most definitions, sometimes giving surprising answers, or slow answers.
The old behaviour is still available via `library_search!`.

### [2020-06-12 15:35:03](https://github.com/leanprover-community/mathlib/commit/5c0000c)
chore(*): remove extra author info ([#3051](https://github.com/leanprover-community/mathlib/pull/3051))
Removing changes to author headers in files with recent changes. Authorship should be cited in the headers only for significant contributions.

### [2020-06-12 13:27:48](https://github.com/leanprover-community/mathlib/commit/64461b8)
chore(scripts): update nolints.txt ([#3049](https://github.com/leanprover-community/mathlib/pull/3049))
I am happy to remove some nolints for you!

### [2020-06-12 12:19:15](https://github.com/leanprover-community/mathlib/commit/6aa2464)
chore(scripts): update nolints.txt ([#3048](https://github.com/leanprover-community/mathlib/pull/3048))
I am happy to remove some nolints for you!

### [2020-06-12 11:43:13](https://github.com/leanprover-community/mathlib/commit/f78693d)
chore(data/complex/exponential): linting and pp_nodot ([#3045](https://github.com/leanprover-community/mathlib/pull/3045))

### [2020-06-12 11:43:11](https://github.com/leanprover-community/mathlib/commit/5808afc)
feat(analysis/mean_inequalities): Holder and Minkowski inequalities ([#3025](https://github.com/leanprover-community/mathlib/pull/3025))

### [2020-06-12 11:10:43](https://github.com/leanprover-community/mathlib/commit/27a0946)
chore(scripts): update nolints.txt ([#3046](https://github.com/leanprover-community/mathlib/pull/3046))
I am happy to remove some nolints for you!

### [2020-06-12 10:19:27](https://github.com/leanprover-community/mathlib/commit/30e620c)
chore(data/real/cau_seq): linting ([#3040](https://github.com/leanprover-community/mathlib/pull/3040))

### [2020-06-12 09:31:29](https://github.com/leanprover-community/mathlib/commit/0f6b3ca)
doc(data/complex/basic): docstrings and pp_nodots ([#3044](https://github.com/leanprover-community/mathlib/pull/3044))

### [2020-06-12 05:32:43](https://github.com/leanprover-community/mathlib/commit/96676a7)
chore(scripts): update nolints.txt ([#3039](https://github.com/leanprover-community/mathlib/pull/3039))
I am happy to remove some nolints for you!

### [2020-06-12 03:49:42](https://github.com/leanprover-community/mathlib/commit/4ec7cc5)
refactor(*): fix field names in `linear_map` and `submodule` ([#3032](https://github.com/leanprover-community/mathlib/pull/3032))
* `linear_map` now uses `map_add'` and `map_smul`';
* `submodule` now `extends add_submonoid` and adds `smul_mem'`;
* no more `submodule.is_add_subgroup` instance;
* `open_subgroup` now uses bundled subgroups;
* `is_linear_map` is not a `class` anymore: we had a couple of
  `instances` but zero lemmas taking it as a typeclass argument;
* `subgroup.mem_coe` now takes `{g : G}` as it should, not `[g : G]`.

### [2020-06-12 02:45:20](https://github.com/leanprover-community/mathlib/commit/338bbd2)
chore(measure/theory): remove useless module instances ([#3031](https://github.com/leanprover-community/mathlib/pull/3031))
Remove useless `module` and `vector_space` instances, as these words are now synonyms of `semimodule`.

### [2020-06-11 22:32:06](https://github.com/leanprover-community/mathlib/commit/593f731)
chore(scripts): update nolints.txt ([#3035](https://github.com/leanprover-community/mathlib/pull/3035))
I am happy to remove some nolints for you!

### [2020-06-11 21:56:33](https://github.com/leanprover-community/mathlib/commit/5444945)
chore(scripts): update nolints.txt ([#3034](https://github.com/leanprover-community/mathlib/pull/3034))
I am happy to remove some nolints for you!

### [2020-06-11 21:56:31](https://github.com/leanprover-community/mathlib/commit/f71e359)
chore(ring_theory/power_series): avoid id in instances ([#3033](https://github.com/leanprover-community/mathlib/pull/3033))
The power series instances contain a spurious `id`, that we remove.

### [2020-06-11 20:24:50](https://github.com/leanprover-community/mathlib/commit/9a7151c)
feat(data/finsupp): set.finite {m | m ≤ n} ([#3029](https://github.com/leanprover-community/mathlib/pull/3029))

### [2020-06-11 20:24:48](https://github.com/leanprover-community/mathlib/commit/666b9e5)
refactor(analysis/mean_inequalities): review ([#3023](https://github.com/leanprover-community/mathlib/pull/3023))
Also add several lemmas to other files

### [2020-06-11 18:53:58](https://github.com/leanprover-community/mathlib/commit/257d1b7)
feat(*): preparations for Caratheodory's convexity theorem ([#3030](https://github.com/leanprover-community/mathlib/pull/3030))

### [2020-06-11 18:53:56](https://github.com/leanprover-community/mathlib/commit/447a2d6)
chore(data/matrix/basic): move numeral section into diagonal ([#3022](https://github.com/leanprover-community/mathlib/pull/3022))
Since the numeral section defines numerals for matrices as scalar
multiples of `one_val`, which is the identity matrix, these are defined
solely for diagonal matrices of type `matrix n n r`. So the numeral
section should be in the diagonal section.

### [2020-06-11 18:19:12](https://github.com/leanprover-community/mathlib/commit/1df9301)
feat(group_theory/semidirect_product): introduce semidirect_products of groups ([#3028](https://github.com/leanprover-community/mathlib/pull/3028))

### [2020-06-11 15:35:28](https://github.com/leanprover-community/mathlib/commit/ce48b6b)
chore(data/finsupp): drop `finsupp.module` and `vector_space` ([#3009](https://github.com/leanprover-community/mathlib/pull/3009))
These instances are not needed as `module` and `vector_space` are abbreviations for `semimodule`.
Also add two bundled versions of `eval`: as `add_monoid_hom` and as `linear_map`.

### [2020-06-11 11:41:18](https://github.com/leanprover-community/mathlib/commit/cf0c6b8)
chore(*): use prod and sum notation ([#3027](https://github.com/leanprover-community/mathlib/pull/3027))

### [2020-06-11 09:43:11](https://github.com/leanprover-community/mathlib/commit/5129aed)
chore(algebra/group/to_additive): improve warning message ([#3024](https://github.com/leanprover-community/mathlib/pull/3024))
Also prevent `group_theory/subgroup` from generating this warning.

### [2020-06-11 08:03:33](https://github.com/leanprover-community/mathlib/commit/ade196f)
chore(scripts): update nolints.txt ([#3026](https://github.com/leanprover-community/mathlib/pull/3026))
I am happy to remove some nolints for you!

### [2020-06-11 06:36:39](https://github.com/leanprover-community/mathlib/commit/8863666)
feat(ring_theory/ideals): prod_dvd_of_coprime ([#2815](https://github.com/leanprover-community/mathlib/pull/2815))

### [2020-06-10 19:03:46](https://github.com/leanprover-community/mathlib/commit/2779093)
feat(linear_algebra/matrix): matrix has finite dim  ([#3013](https://github.com/leanprover-community/mathlib/pull/3013))
Using the fact that currying is a linear operation, we give matrix
a finite dimensional instance. This allows one to invoke `findim`
on matrices, giving the expected dimensions for a finite-dim matrix.
The import is changed to linear_algebra.finite_dimension,
which brings in the previous linear_algebra.dimension import.

### [2020-06-10 15:54:19](https://github.com/leanprover-community/mathlib/commit/067a96b)
chore(*): update to lean 3.16.1c ([#3020](https://github.com/leanprover-community/mathlib/pull/3020))

### [2020-06-10 15:54:17](https://github.com/leanprover-community/mathlib/commit/76e7d29)
chore(scripts): update nolints.txt ([#3019](https://github.com/leanprover-community/mathlib/pull/3019))
I am happy to remove some nolints for you!

### [2020-06-10 15:54:15](https://github.com/leanprover-community/mathlib/commit/f7654b3)
feat(tactic/generalizes): tactic for generalizing over multiple expressions ([#2982](https://github.com/leanprover-community/mathlib/pull/2982))
This commit adds a tactic `generalizes` which works like `generalize` but for multiple expressions at once. The tactic is more powerful than calling `generalize` multiple times since this usually fails when there are dependencies between the expressions. By contrast, `generalizes` handles at least some such situations.

### [2020-06-10 14:24:39](https://github.com/leanprover-community/mathlib/commit/daed8a4)
style(*): use rcases patterns with ext ([#3018](https://github.com/leanprover-community/mathlib/pull/3018))

### [2020-06-10 14:24:37](https://github.com/leanprover-community/mathlib/commit/026d639)
ci(build.yml): add -T100000 to test step ([#3017](https://github.com/leanprover-community/mathlib/pull/3017))
cf. [#2276](https://github.com/leanprover-community/mathlib/pull/2276).  This will also prevent some confusing timeouts, see e.g. https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Tests.20fail

### [2020-06-10 12:50:03](https://github.com/leanprover-community/mathlib/commit/614d1ca)
chore(*): update to lean 3.16.0 ([#3016](https://github.com/leanprover-community/mathlib/pull/3016))
The only change relevant to mathlib is that the precedence of unary `-` has changed, so that `-a^n` parses as `-(a^n)` and not (as formerly) `(-a)^n`.

### [2020-06-10 12:50:01](https://github.com/leanprover-community/mathlib/commit/4b62261)
chore(algebra/field): deduplicate with group_with_zero ([#3015](https://github.com/leanprover-community/mathlib/pull/3015))
For historical reasons there are lots of lemmas we prove for `group_with_zero`, then again for a `division_ring`. Merge some of them.

### [2020-06-10 12:49:59](https://github.com/leanprover-community/mathlib/commit/b427ebf)
chore(data/equiv/basic): add many docstrings, review ([#3008](https://github.com/leanprover-community/mathlib/pull/3008))
Non-docstring changes:
* drop `decidable_eq_of_equiv` (was a copy of `equiv.decidable_eq`);
* rename `inhabited_of_equiv` to `equiv.inhabited`;
* rename `unique_of_equiv` to `equiv.unique`, take `unique β` as an
  instance argument;
* better defeq for `equiv.list_equiv_of_equiv`;
* use `coe` instead of `subtype.val` in `equiv.set.union'`;
* use `s ∩ t ⊆ ∅` instead of `s ∩ t = ∅` in `equiv.set.union`;
  this way it agrees with `disjoint`;
* use `[decidable_pred (λ x, x ∈ s)]` instead of `[decidable_pred s]`
  in `equiv.set.union`;
* use `coe` instead of `subtype.val` in `equiv.set.sep`;
* make `f` an explicit argument in `equiv.of_bijective f hf`;

### [2020-06-10 12:49:57](https://github.com/leanprover-community/mathlib/commit/671284e)
feat(control/equiv_functor/instances): allow equiv_rw on finset ([#2997](https://github.com/leanprover-community/mathlib/pull/2997))
Allows moving `finset` over an `equiv` using `equiv_rw`, as requested by @jcommelin.
e.g.
```
import data.finset
import tactic.equiv_rw
example (σ τ : Type) (e : σ ≃ τ) : finset σ ≃ finset τ :=
by { equiv_rw e, refl, }
```

### [2020-06-10 11:19:50](https://github.com/leanprover-community/mathlib/commit/b932a51)
feat(data/set/function): add lemmas about `semiconj` ([#3007](https://github.com/leanprover-community/mathlib/pull/3007))
Also redefine `set.maps_to` to avoid unfolding `mem_preimage`.

### [2020-06-10 09:47:17](https://github.com/leanprover-community/mathlib/commit/836c0a2)
chore(*): use sum notation ([#3014](https://github.com/leanprover-community/mathlib/pull/3014))
The biggest field test of the new summation notation.

### [2020-06-10 08:49:53](https://github.com/leanprover-community/mathlib/commit/d9934b2)
feat(linear_algebra/basic): curry is linear_equiv ([#3012](https://github.com/leanprover-community/mathlib/pull/3012))
Currying provides a linear_equiv. This can be used to show that
matrix lookup is a linear operation. This should allow to easily
provide a finite_dimensional instance for matrices.

### [2020-06-10 07:15:39](https://github.com/leanprover-community/mathlib/commit/6a0412e)
chore(data/fintype): generalise `to_finset_card` ([#2316](https://github.com/leanprover-community/mathlib/pull/2316))
Slight generalisation of a lemma, allowing a more flexible `fintype` instance.
Also americanises some spelling. :-)

### [2020-06-10 00:06:07](https://github.com/leanprover-community/mathlib/commit/f1df14c)
feat(group_theory/subgroup): normal_closure and gpowers ([#2959](https://github.com/leanprover-community/mathlib/pull/2959))
Transfer some more proofs from `deprecated/subgroup`

### [2020-06-09 21:53:37](https://github.com/leanprover-community/mathlib/commit/4e1558b)
chore(algebra/group_power): simp attribute on nsmul_eq_mul and gsmul_eq_mul ([#2983](https://github.com/leanprover-community/mathlib/pull/2983))
Also fix the resulting lint failures, corresponding to the fact that several lemmas are not in simp normal form any more.

### [2020-06-09 20:16:58](https://github.com/leanprover-community/mathlib/commit/a02ab48)
refactor(group_theory/subgroup): swap `mul_mem_cancel_left/right` ([#3011](https://github.com/leanprover-community/mathlib/pull/3011))
This way the name follows the position of the term we cancel.

### [2020-06-09 19:36:31](https://github.com/leanprover-community/mathlib/commit/df34ee2)
chore(scripts): update nolints.txt ([#3010](https://github.com/leanprover-community/mathlib/pull/3010))
I am happy to remove some nolints for you!

### [2020-06-09 17:36:44](https://github.com/leanprover-community/mathlib/commit/1a4f0c2)
refactor(algebra/ordered_group): multiplicative versions of ordered monoids/groups ([#2844](https://github.com/leanprover-community/mathlib/pull/2844))
This PR defines multiplicative versions of ordered monoids and groups. It also lints the file.

### [2020-06-09 17:00:44](https://github.com/leanprover-community/mathlib/commit/f098c16)
feat(ring_theory/localization): more lemmas and defs about fields of fractions ([#3005](https://github.com/leanprover-community/mathlib/pull/3005))

### [2020-06-09 12:21:46](https://github.com/leanprover-community/mathlib/commit/ccdf1d2)
feat(category_theory/limits): prod.lift_comp_comp ([#2968](https://github.com/leanprover-community/mathlib/pull/2968))

### [2020-06-09 11:36:39](https://github.com/leanprover-community/mathlib/commit/7cb0a85)
refactor(topology): rename `lim` to `Lim` ([#2977](https://github.com/leanprover-community/mathlib/pull/2977))
Also introduce `lim (f : filter α) (g : α → β)`.

### [2020-06-09 11:05:31](https://github.com/leanprover-community/mathlib/commit/76792dc)
feat(algebra/add_torsor): add `prod.add_torsor` ([#2980](https://github.com/leanprover-community/mathlib/pull/2980))

### [2020-06-09 09:07:38](https://github.com/leanprover-community/mathlib/commit/4281343)
refactor(data/polynomial): redefine `C` as an `alg_hom` ([#3003](https://github.com/leanprover-community/mathlib/pull/3003))
As a side effect Lean parses `C 1` as `polynomial nat`. If you need `polynomial R`, then use `C (1:R)`.

### [2020-06-09 08:13:56](https://github.com/leanprover-community/mathlib/commit/34302c6)
chore(ring_theory/algebra): add comments explaining absence of 2 `simp` attrs ([#3002](https://github.com/leanprover-community/mathlib/pull/3002))

### [2020-06-09 08:13:54](https://github.com/leanprover-community/mathlib/commit/03c345f)
chore(data/real/nnreal): +2 lemmas ([#3000](https://github.com/leanprover-community/mathlib/pull/3000))

### [2020-06-09 08:13:52](https://github.com/leanprover-community/mathlib/commit/1091462)
feat(analysis/special_functions/pow): `inv_rpow`, `div_rpow` ([#2999](https://github.com/leanprover-community/mathlib/pull/2999))
Also use notation `ℝ≥0` and use `nnreal.eq` instead of `rw ← nnreal.coe_eq`.

### [2020-06-09 07:06:53](https://github.com/leanprover-community/mathlib/commit/45567dc)
chore(algebra/big_operators): add `@[simp] lemma sum_eq_zero_iff` ([#2998](https://github.com/leanprover-community/mathlib/pull/2998))

### [2020-06-09 05:24:03](https://github.com/leanprover-community/mathlib/commit/24ce416)
chore(data/matrix/basic): clean up of new lemmas on matrix numerals ([#2996](https://github.com/leanprover-community/mathlib/pull/2996))
Generalise and improve use of `@[simp]` for some newly added lemmas about matrix numerals.

### [2020-06-08 20:32:11](https://github.com/leanprover-community/mathlib/commit/7bb2d89)
feat(dynamics/fixed_points/topology): new file ([#2991](https://github.com/leanprover-community/mathlib/pull/2991))
* Move `is_fixed_pt_of_tendsto_iterate` from
  `topology.metric_space.contracting`, reformulate it without `∃`.
* Add `is_closed_fixed_points`.
* Move `dynamics.fixed_points` to `dynamics.fixed_points.basic`.

### [2020-06-08 19:36:45](https://github.com/leanprover-community/mathlib/commit/470ccd3)
chore(scripts): update nolints.txt ([#2993](https://github.com/leanprover-community/mathlib/pull/2993))
I am happy to remove some nolints for you!

### [2020-06-08 19:36:43](https://github.com/leanprover-community/mathlib/commit/94deddd)
feat(data/real/conjugate_exponents): define real conjugate exponents ([#2992](https://github.com/leanprover-community/mathlib/pull/2992))

### [2020-06-08 19:36:41](https://github.com/leanprover-community/mathlib/commit/4ee67ac)
chore(*): use prod notation ([#2989](https://github.com/leanprover-community/mathlib/pull/2989))
The biggest field test of the new product notation.

### [2020-06-08 19:36:39](https://github.com/leanprover-community/mathlib/commit/a377993)
feat(geometry/euclidean): angles and some basic lemmas ([#2865](https://github.com/leanprover-community/mathlib/pull/2865))
Define angles (undirected, between 0 and π, in terms of inner
product), and prove some basic lemmas involving angles, for real inner
product spaces and Euclidean affine spaces.
From the 100-theorems list, this provides versions of
* 04 Pythagorean Theorem,
* 65 Isosceles Triangle Theorem and
* 94 The Law of Cosines, with various existing definitions implicitly providing
* 91 The Triangle Inequality.

### [2020-06-08 19:05:30](https://github.com/leanprover-community/mathlib/commit/dbbd696)
feat(order/ideal): order ideals, cofinal sets and the Rasiowa-Sikorski lemma ([#2850](https://github.com/leanprover-community/mathlib/pull/2850))
We define order ideals and cofinal sets, and use them to prove the (very simple) Rasiowa-Sikorski lemma: given a countable family of cofinal subsets of an inhabited preorder, there is an upwards directed set meeting each one. This provides an API for certain recursive constructions.

### [2020-06-08 17:34:19](https://github.com/leanprover-community/mathlib/commit/d204daa)
chore(*): add docs and nolints ([#2990](https://github.com/leanprover-community/mathlib/pull/2990))
Other changes:
* Reuse `gmultiples_hom` for `AddCommGroup.as_hom`.
* Reuse `add_monoid_hom.ext_int` for `AddCommGroup.int_hom_ext`.
* Drop the following definitions, define an `instance` right away
  instead:
  - `algebra.div`;
  - `monoid_hom.one`, `add_monoid_hom.zero`;
  - `monoid_hom.mul`, `add_monoid_hom.add`;
  - `monoid_hom.inv`, `add_monoid_hom.neg`.

### [2020-06-08 17:34:17](https://github.com/leanprover-community/mathlib/commit/9fba817)
refactor(algebra/*): move `commute` below `ring` in `import`s ([#2973](https://github.com/leanprover-community/mathlib/pull/2973))
Fixes [#1865](https://github.com/leanprover-community/mathlib/pull/1865)
API changes:
* drop lemmas about unbundled `center`;
* add `to_additive` to `semiconj_by` and `commute`;
* drop `inv_comm_of_comm` in favor of `commute.left_inv`,
  same with `inv_comm_of_comm` and `commute.left_inv'`;
* rename `monoid_hom.map_commute` to `commute.map`, same with
  `semiconj_by`;
* drop `commute.cast_*_*` and `nat/int/rat.mul_cast_comm`, add
  `nat/int/rat.cast_commute` and `nat.int.rat.commute_cast`;
* add `commute.mul_fpow`.

### [2020-06-08 16:39:55](https://github.com/leanprover-community/mathlib/commit/2caf479)
feat(data/matrix/basic): add bit0, bit1 lemmas ([#2987](https://github.com/leanprover-community/mathlib/pull/2987))
Based on a conversation in
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Matrix.20equality.20by.20extensionality
we define simp lemmas for matrices represented by numerals.
This should result in better representation of scalar multiples of
 `one_val : matrix n n a`.

### [2020-06-08 15:06:15](https://github.com/leanprover-community/mathlib/commit/3ca4c27)
chore(algebra/ordered_ring): use le instead of ge ([#2986](https://github.com/leanprover-community/mathlib/pull/2986))

### [2020-06-08 15:06:12](https://github.com/leanprover-community/mathlib/commit/47f7335)
feat(data/nat/digits): digits, and divisibility tests for Freek 85 ([#2686](https://github.com/leanprover-community/mathlib/pull/2686))
I couldn't quite believe how much low hanging fruit there is on Lean's attempt at Freek's list, and so took a moment to do surely the lowest of the low...
This provides `digits b n`, which extracts the digits of a natural number `n` with respect to a base `b`, and `of_digits b L`, which reconstitutes a number from its digits, proves a few simple facts about these functions, and proves the usual divisibility by 3, 9, and 11 tests.

### [2020-06-08 13:54:41](https://github.com/leanprover-community/mathlib/commit/a793042)
feat(ring_theory/fractional_ideal): pushforward of fractional ideals ([#2984](https://github.com/leanprover-community/mathlib/pull/2984))
Extend `submodule.map` to fractional ideals by showing that the pushforward is also fractional.
For this, we need a slightly tweaked definition of fractional ideal: if we localize `R` at the submonoid `S`, the old definition required a nonzero `x : R` such that `xI ≤ R`, and the new definition requires `x ∈ S` instead. In the most common case, `S = non_zero_divisors R`, the results are exactly the same, and all operations are still the same.
A practical use of these pushforwards is included: `canonical_equiv` states fractional ideals don't depend on choice of localization map.

### [2020-06-08 07:55:43](https://github.com/leanprover-community/mathlib/commit/c360e01)
feat(ring/localization): add fraction map for int to rat cast ([#2921](https://github.com/leanprover-community/mathlib/pull/2921))

### [2020-06-08 07:00:32](https://github.com/leanprover-community/mathlib/commit/592f769)
feat(dynamics/circle): define translation number of a lift of a circle homeo ([#2974](https://github.com/leanprover-community/mathlib/pull/2974))
Define a structure `circle_deg1_lift`, a function `translation_number : circle_deg1_lift → ℝ`, and prove some basic properties

### [2020-06-07 17:42:45](https://github.com/leanprover-community/mathlib/commit/edd0209)
ci(deploy_docs.sh): generalize for use in doc-gen CI ([#2978](https://github.com/leanprover-community/mathlib/pull/2978))
This moves some installation steps out of `deploy_docs.sh` script and makes it accept several path arguments so that it can be re-used in the CI for `doc-gen`. 
The associated `doc-gen` PR: https://github.com/leanprover-community/doc-gen/pull/27 will be updated after this is merged.

### [2020-06-07 16:14:35](https://github.com/leanprover-community/mathlib/commit/be21b9a)
fix(data/nat/basic): use protected attribute ([#2976](https://github.com/leanprover-community/mathlib/pull/2976))

### [2020-06-07 11:42:06](https://github.com/leanprover-community/mathlib/commit/516d9b5)
chore(scripts): update nolints.txt ([#2975](https://github.com/leanprover-community/mathlib/pull/2975))
I am happy to remove some nolints for you!

### [2020-06-07 09:39:31](https://github.com/leanprover-community/mathlib/commit/a7f0069)
chore(algebra/ring): fix docs, `def`/`lemma` ([#2972](https://github.com/leanprover-community/mathlib/pull/2972))

### [2020-06-07 04:23:17](https://github.com/leanprover-community/mathlib/commit/16ad1b4)
chore(topology/basic): remove unneeded `mk_protected` ([#2971](https://github.com/leanprover-community/mathlib/pull/2971))
It was already fixed by adding `@[protect_proj]`.

### [2020-06-07 03:29:48](https://github.com/leanprover-community/mathlib/commit/b59f777)
feat(category_theory/eq_to_hom): functor extensionality using heq ([#2712](https://github.com/leanprover-community/mathlib/pull/2712))
Used in https://github.com/rwbarton/lean-homotopy-theory.
Also proves `faithful.div_comp`, but using it would create an import loop
so for now I just leave a comment.

### [2020-06-06 20:56:40](https://github.com/leanprover-community/mathlib/commit/2a36d25)
chore(analysis/normed_space/mazur_ulam): add `to_affine_map` ([#2963](https://github.com/leanprover-community/mathlib/pull/2963))

### [2020-06-06 18:14:53](https://github.com/leanprover-community/mathlib/commit/a44c9a1)
chore(*): protect some definitions to get rid of _root_ ([#2846](https://github.com/leanprover-community/mathlib/pull/2846))
These were amongst the worst offenders.

### [2020-06-06 17:40:41](https://github.com/leanprover-community/mathlib/commit/e48c2af)
feat(data/padics/padic_norm): New padic_val_nat convenience functions ([#2970](https://github.com/leanprover-community/mathlib/pull/2970))
Convenience functions to allow us to deal either with the p-adic valuation or with multiplicity in the naturals, depending on what is locally convenient.

### [2020-06-06 17:40:39](https://github.com/leanprover-community/mathlib/commit/589bdb9)
feat(number_theory/lucas_lehmer): prime (2^127 - 1) ([#2842](https://github.com/leanprover-community/mathlib/pull/2842))
This PR
1. proves the sufficiency of the Lucas-Lehmer test for Mersenne primes
2. provides a tactic that uses `norm_num` to do each step of the calculation of Lucas-Lehmer residues
3. proves 2^127 - 1 = 170141183460469231731687303715884105727 is prime
It doesn't
1. prove the necessity of the Lucas-Lehmer test (mathlib certainly has the necessary material if someone wants to do this)
2. use the trick `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]` that is essential to calculating Lucas-Lehmer residues quickly
3. manage to prove any "computer era" primes are prime! (Although my guess is that 2^521 - 1 would run in <1 day with the current implementation.)
I think using "the trick" is very plausible, and would be a fun project for someone who wanted to experiment with certified/fast arithmetic in Lean. It likely would make much larger Mersenne primes accessible.
This is a tidy-up and completion of work started by a student, Ainsley Pahljina.

### [2020-06-06 15:39:02](https://github.com/leanprover-community/mathlib/commit/ed5f636)
chore(algebra/group_with_zero_power): review ([#2966](https://github.com/leanprover-community/mathlib/pull/2966))
List of changes:
* Rename `gpow_neg_succ` to `gpow_neg_succ_of_nat` to match other names in `int` namespace.
* Add `units.coe_gpow`.
* Remove `fpow_neg_succ`, leave `fpow_neg_succ_of_nat`.
* Rewrite the proof of `fpow_add` in the same way I rewrote the proof of `gpow_add`.
* Make argument `a` implicit in some lemmas because they have an argument `ha : a ≠ 0`.
* Remove `fpow_inv`. This was a copy of `fpow_neg_one` with a misleading name.
* Remove `unit_pow` in favor of a more general `units.coe_pow`.
* Remove `unit_gpow`, add a more general `units.coe_gpow'` instead.

### [2020-06-06 15:05:30](https://github.com/leanprover-community/mathlib/commit/2f028a8)
feat(analysis/convex/specific_functions): convexity of rpow ([#2965](https://github.com/leanprover-community/mathlib/pull/2965))
The function `x -> x^p` is convex on `[0, +\infty)` when `p \ge 1`.

### [2020-06-06 13:23:11](https://github.com/leanprover-community/mathlib/commit/f096a74)
fix(tactic/ring_exp): `ring_exp` now recognizes that `2^(n+1+1) = 2 * 2^(n+1)` ([#2929](https://github.com/leanprover-community/mathlib/pull/2929))
[Zulip thread with bug report](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_exp.20needs.20ring).
The problem was a missing lemma so that `norm_num` could fire on `x^y` if `x` and `y` are coefficients.

### [2020-06-06 09:55:46](https://github.com/leanprover-community/mathlib/commit/6f27271)
fix(documentation): fix a typo in the readme ([#2969](https://github.com/leanprover-community/mathlib/pull/2969))

### [2020-06-06 08:01:08](https://github.com/leanprover-community/mathlib/commit/d1ae307)
chore(algebra/ordered_group): add `exists_pos_add_of_lt` ([#2967](https://github.com/leanprover-community/mathlib/pull/2967))
Also drop `protected` on `_root_.zero_lt_iff_ne_zero`.

### [2020-06-06 07:15:17](https://github.com/leanprover-community/mathlib/commit/d18061f)
chore(algebra/add_torsor): a few more lemmas and implicit args ([#2964](https://github.com/leanprover-community/mathlib/pull/2964))

### [2020-06-05 16:16:43](https://github.com/leanprover-community/mathlib/commit/1b2048d)
feat(analysis/special_functions/pow): rpow is differentiable ([#2930](https://github.com/leanprover-community/mathlib/pull/2930))
Differentiability of the real power function `x ↦ x^p`. Also register the lemmas about the composition with a function to make sure that the simplifier can handle automatically the differentiability of `x ↦ (f x)^p` and more complicated expressions involving powers.

### [2020-06-05 13:39:37](https://github.com/leanprover-community/mathlib/commit/5c851bd)
fix(tactic/squeeze_simp): make `squeeze_simp [←...]` work ([#2961](https://github.com/leanprover-community/mathlib/pull/2961))
`squeeze_simp` parses the argument list using a function in core Lean, and when support for backwards arguments was added to `simp`, it used a new function to parse the additional structure. This PR fixes the TODO left in the code to switch `squeeze_simp` to the new function by deleting the code that needed it - it wasn't used anyway!
To add a test for the fix, I moved the single existing `squeeze_simp` test from the deprecated file `examples.lean` to a new file.

### [2020-06-05 11:58:53](https://github.com/leanprover-community/mathlib/commit/a433eb0)
feat(analysis/special_functions/pow): real powers on ennreal ([#2951](https://github.com/leanprover-community/mathlib/pull/2951))
Real powers of extended nonnegative real numbers. We develop an API based on that of real powers of reals and nnreals, proving the corresponding lemmas.

### [2020-06-05 10:41:53](https://github.com/leanprover-community/mathlib/commit/fd623d6)
feat(data/set/intervals/image_preimage): new file ([#2958](https://github.com/leanprover-community/mathlib/pull/2958))
* Create a file for lemmas like
  `(λ x, x + a) '' Icc b c = Icc (b + a) (b + c)`.
* Prove lemmas about images and preimages of all intervals under
  `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x`.
* Move lemmas about multiplication from `basic`.

### [2020-06-05 10:10:03](https://github.com/leanprover-community/mathlib/commit/1ef65c9)
feat(linear_algebra/quadratic_form): more constructions for quadratic forms ([#2949](https://github.com/leanprover-community/mathlib/pull/2949))
Define multiplication of two linear forms to give a quadratic form and addition of quadratic forms. With these definitions, we can write a generic binary quadratic form as `a • proj R₁ 0 0 + b • proj R₁ 0 1 + c • proj R₁ 1 1 : quadratic_form R₁ (fin 2 → R₁)`.
In order to prove the linearity conditions on the constructions, there are new `simp` lemmas `polar_add_left`, `polar_smul_left`, `polar_add_right` and `polar_smul_right` copying from the corresponding fields of the `quadratic_form` structure, that use `⇑ Q` instead of `Q.to_fun`. The original field names have a `'` appended to avoid name clashes.

### [2020-06-05 08:41:12](https://github.com/leanprover-community/mathlib/commit/31ceb62)
feat(data/int|nat/basic): add `add_monoid_hom.ext_nat/int` ([#2957](https://github.com/leanprover-community/mathlib/pull/2957))

### [2020-06-05 08:41:10](https://github.com/leanprover-community/mathlib/commit/edb4422)
feat(algebra/add_torsor): add `equiv.const_vadd` and `equiv.vadd_const` ([#2907](https://github.com/leanprover-community/mathlib/pull/2907))
Also define their `isometric.*` versions in `analysis/normed_space/add_torsor`.

### [2020-06-05 07:28:47](https://github.com/leanprover-community/mathlib/commit/a130c73)
feat(topology/algebra/ordered): list of preconnected sets ([#2943](https://github.com/leanprover-community/mathlib/pull/2943))
A subset of a densely ordered conditionally complete lattice (e.g., `ℝ`) with order topology is preconnected if and only if it is one of the intervals.

### [2020-06-05 05:31:21](https://github.com/leanprover-community/mathlib/commit/8f89bd8)
chore(algebra/group_power): simplify a proof ([#2955](https://github.com/leanprover-community/mathlib/pull/2955))

### [2020-06-05 05:31:19](https://github.com/leanprover-community/mathlib/commit/d7fa405)
chore(algebra/*): merge `inv_inv''` with `inv_inv'` ([#2954](https://github.com/leanprover-community/mathlib/pull/2954))

### [2020-06-05 05:31:17](https://github.com/leanprover-community/mathlib/commit/8161888)
feat(group_theory/subgroup): define normal bundled subgroups ([#2947](https://github.com/leanprover-community/mathlib/pull/2947))
Most proofs are adapted from `deprecated/subgroup`.

### [2020-06-05 05:31:15](https://github.com/leanprover-community/mathlib/commit/2131382)
feat(data/setoid/partition): some lemmas about partitions ([#2937](https://github.com/leanprover-community/mathlib/pull/2937))

### [2020-06-05 04:53:19](https://github.com/leanprover-community/mathlib/commit/80a52e9)
chore(analysis/convex/basic): add `finset.convex_hull_eq` ([#2956](https://github.com/leanprover-community/mathlib/pull/2956))

### [2020-06-04 18:38:01](https://github.com/leanprover-community/mathlib/commit/2ceb7f7)
feat(analysis/convex): preparatory statement for caratheodory ([#2944](https://github.com/leanprover-community/mathlib/pull/2944))
Proves
```lean
lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t
```

### [2020-06-04 18:05:52](https://github.com/leanprover-community/mathlib/commit/beb5d45)
chore(scripts): update nolints.txt ([#2952](https://github.com/leanprover-community/mathlib/pull/2952))
I am happy to remove some nolints for you!

### [2020-06-04 16:18:37](https://github.com/leanprover-community/mathlib/commit/1a29796)
chore(is_ring_hom): remove some uses of is_ring_hom ([#2884](https://github.com/leanprover-community/mathlib/pull/2884))
This PR deletes the definitions `is_ring_anti_hom` and `ring_anti_equiv`, in favour of using the bundled `R →+* Rᵒᵖ` and `R ≃+* Rᵒᵖ`. It also changes the definition of `ring_invo`.
This is work towards removing the deprecated `is_*_hom` family.

### [2020-06-04 15:38:26](https://github.com/leanprover-community/mathlib/commit/7d803a9)
feat(topology/metric_space/isometry): group structure on isometries ([#2950](https://github.com/leanprover-community/mathlib/pull/2950))
Closes [#2908](https://github.com/leanprover-community/mathlib/pull/2908)

### [2020-06-04 15:38:24](https://github.com/leanprover-community/mathlib/commit/add0c9a)
feat(ring/localization): add construction of localization as a quotient type ([#2922](https://github.com/leanprover-community/mathlib/pull/2922))

### [2020-06-04 15:06:53](https://github.com/leanprover-community/mathlib/commit/2dbf550)
feat(ring_theory/eisenstein_criterion): Eisenstein's criterion ([#2946](https://github.com/leanprover-community/mathlib/pull/2946))

### [2020-06-04 14:28:44](https://github.com/leanprover-community/mathlib/commit/c2e78d2)
refactor(data/zmod): generalize zmod.cast_hom ([#2900](https://github.com/leanprover-community/mathlib/pull/2900))
Currently, `zmod.cast_hom` would cast `zmod n` to rings `R` of characteristic `n`.
This PR builds `cast_hom` for rings `R` with characteristic `m` that divides `n`.

### [2020-06-04 07:22:09](https://github.com/leanprover-community/mathlib/commit/e397b4c)
chore(scripts): update nolints.txt ([#2948](https://github.com/leanprover-community/mathlib/pull/2948))
I am happy to remove some nolints for you!

### [2020-06-04 04:42:31](https://github.com/leanprover-community/mathlib/commit/5744f89)
chore(*): fix some `ge_or_gt` lint issues ([#2945](https://github.com/leanprover-community/mathlib/pull/2945))
Also rename a few definitions:
* `ge_of_forall_ge_sub` : `le_of_forall_sub_le`;
* `power_series.order_ge_nat` : `power_series.nat_le_order`;
* `power_series.order_ge`: `power_series.le_order`;

### [2020-06-03 16:19:29](https://github.com/leanprover-community/mathlib/commit/ef6d8d9)
refactor(analysis/specific_limits): prove `0 < r → (1+r)^n→∞` for semirings ([#2935](https://github.com/leanprover-community/mathlib/pull/2935))
* Add `add_one_pow_unbounded_of_pos` and
  `tendsto_add_one_pow_at_top_at_top_of_pos` assuming
  `[linear_ordered_semiring α]` `[archimedean α]`.
* Rename `tendsto_pow_at_top_at_top_of_gt_1` to
  `tendsto_pow_at_top_at_top_of_one_lt`, generalize to an archimedean
  ordered ring.
* Rename `tendsto_pow_at_top_at_top_of_gt_1_nat` to
  `nat.tendsto_pow_at_top_at_top_of_one_lt`.

### [2020-06-03 15:11:28](https://github.com/leanprover-community/mathlib/commit/1adf204)
chore(scripts): update nolints.txt ([#2942](https://github.com/leanprover-community/mathlib/pull/2942))
I am happy to remove some nolints for you!

### [2020-06-03 15:11:26](https://github.com/leanprover-community/mathlib/commit/494b43e)
chore(category_theory/limits/over): granularity in forget preserving colimits ([#2941](https://github.com/leanprover-community/mathlib/pull/2941))
a bit more granularity for instances about forget preserving colimits

### [2020-06-03 15:11:24](https://github.com/leanprover-community/mathlib/commit/97265f9)
feat(category_theory/limits): dualise a limits result ([#2940](https://github.com/leanprover-community/mathlib/pull/2940))
Add the dual of `is_limit.of_cone_equiv`.

### [2020-06-03 13:41:29](https://github.com/leanprover-community/mathlib/commit/e205228)
feat(data/fintype/basic): to_finset_inj ([#2938](https://github.com/leanprover-community/mathlib/pull/2938))

### [2020-06-03 13:41:27](https://github.com/leanprover-community/mathlib/commit/74037cb)
feat(topology/algebra/ordered): IVT for two functions ([#2933](https://github.com/leanprover-community/mathlib/pull/2933))
Also rename some `is_connected_I*` lemmas to `is_preconnected_I*`.

### [2020-06-03 13:41:25](https://github.com/leanprover-community/mathlib/commit/f44509c)
chore(tactic/localized): lower priority of bad decidability instances in classical locale ([#2932](https://github.com/leanprover-community/mathlib/pull/2932))
Also add a decidability instance for complex numbers.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/monoid_algebra.2Emul_apply/near/199595932
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/slow.20elaboration/near/199543997

### [2020-06-03 12:09:46](https://github.com/leanprover-community/mathlib/commit/ed91bb2)
feat(data/setoid/partition): sUnion _classes ([#2936](https://github.com/leanprover-community/mathlib/pull/2936))

### [2020-06-03 12:09:44](https://github.com/leanprover-community/mathlib/commit/c3221f7)
feat(data/rat): denom_div_cast_eq_one_iff ([#2934](https://github.com/leanprover-community/mathlib/pull/2934))

### [2020-06-03 12:09:43](https://github.com/leanprover-community/mathlib/commit/1f2102d)
chore(group_theory/group_action): protect_proj attribute for mul_action ([#2931](https://github.com/leanprover-community/mathlib/pull/2931))

### [2020-06-03 12:09:41](https://github.com/leanprover-community/mathlib/commit/687fc51)
ci(bors): set `cut_body_after` to `---` ([#2927](https://github.com/leanprover-community/mathlib/pull/2927))

### [2020-06-03 12:09:39](https://github.com/leanprover-community/mathlib/commit/9fc2413)
feat(order/iterate): a few more lemmas about `f^[n]` ([#2925](https://github.com/leanprover-community/mathlib/pull/2925))

### [2020-06-03 12:09:37](https://github.com/leanprover-community/mathlib/commit/0ec9c0e)
feat(algebra/iterate_hom): add `mul_left_iterate` etc ([#2923](https://github.com/leanprover-community/mathlib/pull/2923))

### [2020-06-03 11:09:01](https://github.com/leanprover-community/mathlib/commit/8d9e541)
feat(group_theory/group_action): some lemmas about orbits ([#2928](https://github.com/leanprover-community/mathlib/pull/2928))
also remove the simp attribute unfolding the definition of orbit.
Depends on [#2924](https://github.com/leanprover-community/mathlib/pull/2924)

### [2020-06-03 09:28:49](https://github.com/leanprover-community/mathlib/commit/5020285)
chore(group_theory/group_action): simp attributes on inv_smul_smul and smul_inv_smul ([#2924](https://github.com/leanprover-community/mathlib/pull/2924))

### [2020-06-03 07:59:41](https://github.com/leanprover-community/mathlib/commit/3904374)
chore(algebra/ordered_group)`: add `strict_mono.add_const/const_add` ([#2926](https://github.com/leanprover-community/mathlib/pull/2926))

### [2020-06-03 06:31:17](https://github.com/leanprover-community/mathlib/commit/879bad2)
feat(analysis/normed_space/enorm): define extended norm ([#2897](https://github.com/leanprover-community/mathlib/pull/2897))

### [2020-06-02 21:15:28](https://github.com/leanprover-community/mathlib/commit/efae3d9)
feat(data/mv_polynomial): C_inj and C_injective ([#2920](https://github.com/leanprover-community/mathlib/pull/2920))

### [2020-06-02 19:58:24](https://github.com/leanprover-community/mathlib/commit/607286e)
feat(data/*): ring_hom.ext_{nat,int,rat,zmod} ([#2918](https://github.com/leanprover-community/mathlib/pull/2918))

### [2020-06-02 17:27:51](https://github.com/leanprover-community/mathlib/commit/62ec2c5)
feat(linear_algebra/matrix): add alg_equiv_matrix ([#2919](https://github.com/leanprover-community/mathlib/pull/2919))

### [2020-06-02 07:41:15](https://github.com/leanprover-community/mathlib/commit/1a4de99)
feat(category_theory/limits) equalizer morphism is regular mono ([#2916](https://github.com/leanprover-community/mathlib/pull/2916))
The equalizer morphism is a regular mono, and its dual

### [2020-06-02 06:13:44](https://github.com/leanprover-community/mathlib/commit/1494cc1)
feat(order/semiconj_Sup): use `Sup` to semiconjugate functions ([#2895](https://github.com/leanprover-community/mathlib/pull/2895))
Formalize two lemmas from a paper by É. Ghys.

### [2020-06-02 02:13:40](https://github.com/leanprover-community/mathlib/commit/4372d17)
chore(scripts): update nolints.txt ([#2914](https://github.com/leanprover-community/mathlib/pull/2914))
I am happy to remove some nolints for you!

### [2020-06-02 00:43:24](https://github.com/leanprover-community/mathlib/commit/eb616cf)
chore(*): split long lines ([#2913](https://github.com/leanprover-community/mathlib/pull/2913))

### [2020-06-01 23:39:34](https://github.com/leanprover-community/mathlib/commit/b95f165)
chore(group_theory/sub*): move unbundled submonoids and subgroups to `deprecated` ([#2912](https://github.com/leanprover-community/mathlib/pull/2912))
* move unbundled submonoids to `deprecated/submonoid.lean`;
* move unbundled subgroups to `deprecated/subgroup.lean`;
* move bundled subgroups to `group_theory/subgroup.lean`;
* unbundled versions import bundled.

### [2020-06-01 21:26:03](https://github.com/leanprover-community/mathlib/commit/66ce5d0)
feat(representation_theory/maschke): Maschke's theorem ([#2762](https://github.com/leanprover-community/mathlib/pull/2762))
The final theorem is
```
lemma monoid_algebra.submodule.exists_is_compl
  (not_dvd : ¬(ring_char k ∣ fintype.card G)) (p : submodule (monoid_algebra k G) V) :
  ∃ q : submodule (monoid_algebra k G) V, is_compl p q
```
for `[field k]`.
The core computation, turning a `k`-linear retraction of `k[G]`-linear map into a `k[G]`-linear retraction by averaging over `G`, happens over an arbitrary `[comm_ring k]` in which `[invertible (fintype.card G : k)]`.

### [2020-06-01 19:40:48](https://github.com/leanprover-community/mathlib/commit/085aade)
chore(linear_algebra/affine_space): use implicit args ([#2905](https://github.com/leanprover-community/mathlib/pull/2905))
Whenever we have an argument `f : affine_map k V P`, Lean can figure out `k`, `V`, and `P`.

### [2020-06-01 17:01:58](https://github.com/leanprover-community/mathlib/commit/17296e9)
feat(category_theory/abelian): Schur's lemma ([#2838](https://github.com/leanprover-community/mathlib/pull/2838))
I wrote this mostly to gain some familiarity with @TwoFX's work on abelian categories from [#2817](https://github.com/leanprover-community/mathlib/pull/2817).
That all looked great, and Schur's lemma was pleasantly straightforward.

### [2020-06-01 15:13:02](https://github.com/leanprover-community/mathlib/commit/2812cdc)
fix(ci): check nolints.txt against master ([#2906](https://github.com/leanprover-community/mathlib/pull/2906))
Currently, leanprover-community-bot makes an "update nolints" PR if both of the following hold:
- the `nolints` branch doesn't exist, meaning there isn't already an open nolints PR
- `nolints.txt` has been modified compared to HEAD.
This can lead to a duplicate nolints PR (see e.g. [#2899](https://github.com/leanprover-community/mathlib/pull/2899) and [#2901](https://github.com/leanprover-community/mathlib/pull/2901)), since a nolints PR might have been merged after this build on `master` started, but before this step runs.
This PR changes the second check so that it instead compares `nolints.txt` against the most recent `master` commit, which should fix this.

### [2020-06-01 12:17:18](https://github.com/leanprover-community/mathlib/commit/f142b42)
fix(scripts/deploy_docs): correct git push syntax ([#2903](https://github.com/leanprover-community/mathlib/pull/2903))
The suggestion I made in [#2893](https://github.com/leanprover-community/mathlib/pull/2893) didn't work.

### [2020-06-01 12:17:17](https://github.com/leanprover-community/mathlib/commit/b405a5e)
fix(tactic/equiv_rw): use kdepends_on rather than occurs ([#2898](https://github.com/leanprover-community/mathlib/pull/2898))
`kdepends_on t e` and `e.occurs t` sometimes give different answers, and it seems `equiv_rw` wants the behaviour that `kdepends_on` provides.
There is a new test which failed with `occurs`, and succeeds using `kdepends_on`. No other changes.

### [2020-06-01 11:48:05](https://github.com/leanprover-community/mathlib/commit/b9d485d)
chore(data/mv_polynomial): swap the order of mv_polynomial.ext_iff ([#2902](https://github.com/leanprover-community/mathlib/pull/2902))
The previous order of implications is not the one you usually want to simp or rw with.

### [2020-06-01 10:50:43](https://github.com/leanprover-community/mathlib/commit/0485e0f)
feat(scripts/deploy_docs): force push generated docs ([#2893](https://github.com/leanprover-community/mathlib/pull/2893))
(1) We build the full html docs in every CI run, even though they only get saved on master builds. Just compiling the .lean files used in doc generation should be enough to catch 95% of breaks. I think the bit of extra risk is worth speeding up the CI runs, especially since linting is now as fast as tests + docs. 
(2) The repo hosting the html pages was 1.3gb because we kept every revision. Half of the time spent on doc builds was just checking out the repo. I've deleted the history. This PR changes the build script to overwrite the previous version.

### [2020-06-01 09:01:28](https://github.com/leanprover-community/mathlib/commit/9172cdf)
feat(linear_algebra/affine_space): affine spaces ([#2816](https://github.com/leanprover-community/mathlib/pull/2816))
Define (very minimally) affine spaces (as an abbreviation for
add_torsor in the case where the group is a vector space), affine
subspaces, the affine span of a set of points and affine maps.

### [2020-06-01 06:43:53](https://github.com/leanprover-community/mathlib/commit/6beebb0)
chore(scripts): update nolints.txt ([#2899](https://github.com/leanprover-community/mathlib/pull/2899))
I am happy to remove some nolints for you!

### [2020-06-01 05:31:26](https://github.com/leanprover-community/mathlib/commit/7263917)
chore(order/complete_lattice): redefine `ord_continuous` ([#2886](https://github.com/leanprover-community/mathlib/pull/2886))
Redefine `ord_continuous` using `is_lub` to ensure that the definition
makes sense for `conditionally_complete_lattice`s.

### [2020-06-01 04:59:52](https://github.com/leanprover-community/mathlib/commit/ea76bd8)
chore(scripts): update nolints.txt ([#2896](https://github.com/leanprover-community/mathlib/pull/2896))
I am happy to remove some nolints for you!

### [2020-06-01 03:45:00](https://github.com/leanprover-community/mathlib/commit/5c27885)
feat(order/order_iso): group structure on order automorphisms ([#2875](https://github.com/leanprover-community/mathlib/pull/2875))
Also add a few missing lemmas about `order_iso`

### [2020-06-01 01:58:08](https://github.com/leanprover-community/mathlib/commit/73f95a7)
chore(algebra/group): move defs to `defs.lean` ([#2885](https://github.com/leanprover-community/mathlib/pull/2885))
Also delete the aliases `eq_of_add_eq_add_left` and `eq_of_add_eq_add_right`.