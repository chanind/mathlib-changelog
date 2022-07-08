### [2020-09-30 20:29:32](https://github.com/leanprover-community/mathlib/commit/bcc7c02)
feat(geometry/manifold): smooth bundled maps ([#3641](https://github.com/leanprover-community/mathlib/pull/3641))

### [2020-09-30 19:43:08](https://github.com/leanprover-community/mathlib/commit/c04e339)
feat(archive/imo): formalize IMO 1959 problem 1 ([#4340](https://github.com/leanprover-community/mathlib/pull/4340))
This is a formalization of the problem and solution for the first problem on the 1959 IMO:
Prove that the fraction (21n+4)/(14n+3) is irreducible for every natural number n.

### [2020-09-30 18:14:45](https://github.com/leanprover-community/mathlib/commit/23b04b0)
chore(ring_theory/algebra): Mark algebra.mem_top as simp ([#4339](https://github.com/leanprover-community/mathlib/pull/4339))
This is consistent with `subsemiring.mem_top` and `submonoid.mem_top`, both of which are marked simp.

### [2020-09-30 18:14:43](https://github.com/leanprover-community/mathlib/commit/decd67c)
feat(analysis/convex): slope_mono_adjacent ([#4307](https://github.com/leanprover-community/mathlib/pull/4307))

### [2020-09-30 16:47:25](https://github.com/leanprover-community/mathlib/commit/a06c87e)
chore(*): Tidy some proofs and variables ([#4338](https://github.com/leanprover-community/mathlib/pull/4338))

### [2020-09-30 16:47:23](https://github.com/leanprover-community/mathlib/commit/9921fe7)
fix(ring_theory/algebra): Fix typo "algbera" ([#4337](https://github.com/leanprover-community/mathlib/pull/4337))
Introduced in e57fc3d6c142835dc8566aa28e812f7688f14512

### [2020-09-30 14:42:25](https://github.com/leanprover-community/mathlib/commit/05038da)
feat(ring_theory/algebra): some lemmas about numerals in algebras ([#4327](https://github.com/leanprover-community/mathlib/pull/4327))

### [2020-09-30 09:51:53](https://github.com/leanprover-community/mathlib/commit/5fd2037)
chore(*): rename is_unit_pow to is_unit.pow ([#4329](https://github.com/leanprover-community/mathlib/pull/4329))
enable dot notation by renaming
is_unit_pow to is_unit.pow

### [2020-09-30 09:51:51](https://github.com/leanprover-community/mathlib/commit/ac797ad)
feat(topology/bounded_continuous_function): normed_comm_ring structure on bounded continuous functions ([#4326](https://github.com/leanprover-community/mathlib/pull/4326))
An instance of the new ([#4291](https://github.com/leanprover-community/mathlib/pull/4291)) class `normed_comm_ring`.

### [2020-09-30 09:51:49](https://github.com/leanprover-community/mathlib/commit/e53aa87)
feat(order/basic): lemmas about `strict_mono_incr_on` ([#4313](https://github.com/leanprover-community/mathlib/pull/4313))
Also move the section about `order_dual` up to use it in the proofs.
Non-BC API changes:
* Now `strict_mono_incr_on` and `strict_mono_decr_on` take `x` and `y` as `⦃⦄` args.

### [2020-09-30 09:51:46](https://github.com/leanprover-community/mathlib/commit/e1c0b0a)
feat(ring_theory/jacobson): Integral extension of Jacobson rings are Jacobson ([#4304](https://github.com/leanprover-community/mathlib/pull/4304))
Main statement given by `is_jacobson_of_is_integral `

### [2020-09-30 09:51:44](https://github.com/leanprover-community/mathlib/commit/ff66d92)
chore(category_theory/limits): facts about opposites of limit cones ([#4250](https://github.com/leanprover-community/mathlib/pull/4250))
Simple facts about limit cones and opposite categories.

### [2020-09-30 07:56:48](https://github.com/leanprover-community/mathlib/commit/da66bb8)
feat(*): preparations for roots of unity ([#4322](https://github.com/leanprover-community/mathlib/pull/4322))

### [2020-09-29 14:16:59](https://github.com/leanprover-community/mathlib/commit/743f82c)
feat(algebra/pointwise): Add missing to_additive on finset lemmas ([#4306](https://github.com/leanprover-community/mathlib/pull/4306))

### [2020-09-29 12:11:48](https://github.com/leanprover-community/mathlib/commit/669a349)
feat(data/prod): mk injective lemmas ([#4319](https://github.com/leanprover-community/mathlib/pull/4319))
More scattered lemmmas from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-29 12:11:45](https://github.com/leanprover-community/mathlib/commit/d301d43)
feat(algebra/invertible): invertible.copy ([#4318](https://github.com/leanprover-community/mathlib/pull/4318))
A useful gadget from the Witt vector project.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-29 12:11:43](https://github.com/leanprover-community/mathlib/commit/fa09f49)
feat(analysis/special_functions/*): prove that `exp` etc are measurable ([#4314](https://github.com/leanprover-community/mathlib/pull/4314))
The modifications in `measure_theory/borel_space` are a part of the
proof of measurability of `x^y`, `x : ennreal`, `y : ℝ`, but this
proof depends on a refactoring of `arcsin` I'm going to PR soon.

### [2020-09-29 12:11:41](https://github.com/leanprover-community/mathlib/commit/744e067)
feat(linear_algebra/dual): transpose of linear maps ([#4302](https://github.com/leanprover-community/mathlib/pull/4302))
This is filling an easy hole from the undergrad curriculum page: the transpose of a linear map. We don't prove much about it but at least we make contact with matrix transpose.

### [2020-09-29 10:59:46](https://github.com/leanprover-community/mathlib/commit/a5a7a75)
feat(analysis/normed_space): define `normed_comm_ring` ([#4291](https://github.com/leanprover-community/mathlib/pull/4291))
Also use section `variables`.

### [2020-09-29 09:53:22](https://github.com/leanprover-community/mathlib/commit/9962bfa)
doc(data/monoid_algebra): fix typo ([#4317](https://github.com/leanprover-community/mathlib/pull/4317))

### [2020-09-29 07:37:23](https://github.com/leanprover-community/mathlib/commit/22d034c)
feat(algebra/quandle): racks and quandles ([#4247](https://github.com/leanprover-community/mathlib/pull/4247))
This adds the algebraic structures of racks and quandles, defines a few examples, and provides the universal enveloping group of a rack.
A rack is a set that acts on itself bijectively, and sort of the point is that the action `act : α → (α ≃ α)` satisfies
```
act (x ◃ y) = act x * act y * (act x)⁻¹
```
where `x ◃ y` is the usual rack/quandle notation for `act x y`.  (Note: racks do not use `has_scalar` because it's convenient having `x ◃⁻¹ y` for the inverse action of `x` on `y`.  Plus, associative racks have a trivial action.)
In knot theory, the universal enveloping group of the fundamental quandle is isomorphic to the fundamental group of the knot complement.  For oriented knots up to orientation-reversed mirror image, the fundamental quandle is a complete invariant, unlike the fundamental group, which fails to distinguish non-prime knots with chiral summands.

### [2020-09-29 04:58:27](https://github.com/leanprover-community/mathlib/commit/0bb5e5d)
feat(ring_theory/algebra_tower): Artin--Tate lemma ([#4282](https://github.com/leanprover-community/mathlib/pull/4282))

### [2020-09-29 03:32:06](https://github.com/leanprover-community/mathlib/commit/88187ba)
chore(topology/algebra/ordered): golf a proof ([#4311](https://github.com/leanprover-community/mathlib/pull/4311))
* generalize `continuous_within_at_Ioi_iff_Ici` from `linear_order α`
  to `partial_order α`;
* base the proof on a more general fact:
  `continuous_within_at f (s \ {x}) x ↔ continuous_within_at f s x`.

### [2020-09-28 17:22:18](https://github.com/leanprover-community/mathlib/commit/89d8cc3)
refactor(data/nat/basic): review API of `nat.find_greatest` ([#4274](https://github.com/leanprover-community/mathlib/pull/4274))
Other changes:
* add `nat.find_eq_iff`;
* use weaker assumptions in `measurable_to_encodable` and `measurable_to_nat`;
* add `measurable_find`.

### [2020-09-28 15:25:45](https://github.com/leanprover-community/mathlib/commit/50dbce9)
fix(data/list/basic): Ensure that ball_cons actually works as a simp lemma ([#4281](https://github.com/leanprover-community/mathlib/pull/4281))
The LHS of the simp lemma `list.ball_cons` (aka `list.forall_mem_cons`) is not in simp-normal form, as `list.mem_cons_iff` rewrites it.
This adds a new simp lemma which is the form that `list.mem_cons_iff` rewrites it to.

### [2020-09-28 15:25:43](https://github.com/leanprover-community/mathlib/commit/40fb701)
feat(data/mv_polynomial): some lemmas on constant_coeff and rename ([#4231](https://github.com/leanprover-community/mathlib/pull/4231))
Snippet from the Witt project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-09-28 14:08:44](https://github.com/leanprover-community/mathlib/commit/8461a7d)
feat(geometry/euclidean/monge_point): lemmas on altitudes and orthocenter ([#4179](https://github.com/leanprover-community/mathlib/pull/4179))
Add more lemmas about altitudes of a simplex and the orthocenter of a
triangle.  Some of these are just building out basic API that's
mathematically trivial (e.g. showing that the altitude as defined is a
one-dimensional affine subspace and providing an explicit form of its
direction), while the results on the orthocenter have some geometrical
content that's part of the preparation for defining and proving basic
properties of orthocentric systems.

### [2020-09-28 11:21:24](https://github.com/leanprover-community/mathlib/commit/7bbb759)
chore(algebra/free_algebra): Make the second type argument to lift and ι implicit ([#4299](https://github.com/leanprover-community/mathlib/pull/4299))
These can always be inferred by the context, and just make things longer.
This is consistent with how the type argument for `id` is implicit.
The changes are applied to downstream uses too.

### [2020-09-28 11:21:22](https://github.com/leanprover-community/mathlib/commit/ad680c2)
chore(algebra/ordered_ring): remove duplicate lemma ([#4295](https://github.com/leanprover-community/mathlib/pull/4295))
`ordered_ring.two_pos` and `ordered_ring.zero_lt_two` had ended up identical. I kept `zero_lt_two`.

### [2020-09-28 05:25:33](https://github.com/leanprover-community/mathlib/commit/3986e97)
chore(algebra/lie): group Lie algebra files together in their own directory ([#4288](https://github.com/leanprover-community/mathlib/pull/4288))

### [2020-09-28 05:25:30](https://github.com/leanprover-community/mathlib/commit/d77ac51)
chore(data/fintype/card): review API ([#4287](https://github.com/leanprover-community/mathlib/pull/4287))
API changes:
* `finset.filter_mem_eq_inter` now takes `[Π i, decidable (i ∈ t)]`; this way it works better
  with `classical`;
* add `finset.mem_compl` and `finset.coe_compl`;
* [DRY] drop `finset.prod_range_eq_prod_fin` and `finset.sum_range_eq_sum_fin`:
  use `fin.prod_univ_eq_prod_range` and `fin.sum_univ_eq_sum_range` instead;
* rename `finset.prod_equiv` to `equiv.prod_comp` to enable dot notation;
* add `fintype.prod_dite`: a specialized version of `finset.prod_dite`.
Also golf a proof in `analysis/normed_space/multilinear`

### [2020-09-28 05:25:28](https://github.com/leanprover-community/mathlib/commit/66c87c0)
feat(data/*/gcd): adds gcd, lcm of finsets and multisets ([#4217](https://github.com/leanprover-community/mathlib/pull/4217))
Defines `finset.gcd`, `finset.lcm`, `multiset.gcd`, `multiset.lcm`
Proves some basic facts about those, analogous to those in `data.multiset.lattice` and `data.finset.lattice`

### [2020-09-28 04:20:18](https://github.com/leanprover-community/mathlib/commit/1761822)
chore(category_theory/limits): some limit lemmas ([#4238](https://github.com/leanprover-community/mathlib/pull/4238))
A couple of lemmas characterising definitions which are already there (the first part of [#4163](https://github.com/leanprover-community/mathlib/pull/4163))

### [2020-09-28 01:45:45](https://github.com/leanprover-community/mathlib/commit/d8726bf)
feat(ring_theory/integral_closure): Explicitly define integral extensions ([#4164](https://github.com/leanprover-community/mathlib/pull/4164))
* Defined `ring_hom.is_integral_elem` as a generalization of `is_integral` that takes a ring homomorphism rather than an algebra. The old version is is redefined to be `(algebra_map R A).is_integral_elem x`.
* Create predicates `ring_hom.is_integral` and `algebra.is_integral` representing when the entire extension is integral over the base ring.

### [2020-09-28 00:59:38](https://github.com/leanprover-community/mathlib/commit/2fa1bc6)
chore(scripts): update nolints.txt ([#4293](https://github.com/leanprover-community/mathlib/pull/4293))
I am happy to remove some nolints for you!

### [2020-09-27 20:45:01](https://github.com/leanprover-community/mathlib/commit/3897758)
feat(measure_theory): prove that more functions are measurable ([#4266](https://github.com/leanprover-community/mathlib/pull/4266))
Mostly additions to `borel_space`.
Generalize `measurable_bsupr` and `measurable_binfi` to countable sets (instead of encodable underlying types). Use the lemma `countable_encodable` to get the original behavior.
Some cleanup in `borel_space`: more instances are in `variables`, and lemmas with the same instances a bit more.
One downside: there is a big import bump in `borel_space`, it currently imports `hahn_banach`. This is (only) used in `measurable_smul_const`. If someone has a proof sketch (in math) of `measurable_smul_const` that doesn't involve Hahn Banach (and that maybe generalizes `real` to a topological field or something), please let me know.

### [2020-09-27 18:31:22](https://github.com/leanprover-community/mathlib/commit/c322471)
feat(undergrad.yaml): missing items ([#4290](https://github.com/leanprover-community/mathlib/pull/4290))

### [2020-09-27 16:34:03](https://github.com/leanprover-community/mathlib/commit/2516d7d)
feat(topology): various additions ([#4264](https://github.com/leanprover-community/mathlib/pull/4264))
Some if it is used for Fubini, but some of the results were rabbit holes I went into, which I never ended up using, but that still seem useful.

### [2020-09-27 08:58:36](https://github.com/leanprover-community/mathlib/commit/b6ce982)
refactor(*): create directory field_theory/finite ([#4212](https://github.com/leanprover-community/mathlib/pull/4212))
facts on finite fields needed facts on polynomials
facts on polynomials wanted to use things about finite fields
this PR reorganises some of the imports
at the moment it also contributes a bit of new stuff,
and depends on two other PRs that add new stuff.

### [2020-09-27 07:48:56](https://github.com/leanprover-community/mathlib/commit/95ab6ac)
docs(overview): expand analysis ([#4284](https://github.com/leanprover-community/mathlib/pull/4284))
A few additions to the "normed spaces", "convexity", "special functions" and "manifolds" sections of the overview.

### [2020-09-27 05:22:34](https://github.com/leanprover-community/mathlib/commit/a7e3435)
chore(data/option): swap sides in `ne_none_iff_exists` ([#4285](https://github.com/leanprover-community/mathlib/pull/4285))
* swap lhs and rhs of the equality in `option.ne_none_iff_exists`; the new order matches, e.g., the definition of `set.range` and `can_lift.prf`;
* the same in `with_one.ne_one_iff_exists` and `with_zero.ne_zero_iff_exists`;
* remove `option.ne_none_iff_exists'`;
* restore the original `option.ne_none_iff_exists` as `option.ne_none_iff_exists'`

### [2020-09-27 01:39:14](https://github.com/leanprover-community/mathlib/commit/5f6b07f)
chore(scripts): update nolints.txt ([#4283](https://github.com/leanprover-community/mathlib/pull/4283))
I am happy to remove some nolints for you!

### [2020-09-27 00:33:40](https://github.com/leanprover-community/mathlib/commit/5c957ec)
feat(analysis/convex/integral): Jensen's inequality for integrals ([#4225](https://github.com/leanprover-community/mathlib/pull/4225))

### [2020-09-26 20:43:15](https://github.com/leanprover-community/mathlib/commit/8600cb0)
feat(measure_space): define sigma finite measures ([#4265](https://github.com/leanprover-community/mathlib/pull/4265))
They are defined as a `Prop`. The noncomputable "eliminator" is called `spanning_sets`, and satisfies monotonicity, even though that is not required to give a `sigma_finite` instance.
I define a helper function `accumulate s := ⋃ y ≤ x, s y`. This is helpful, to separate out some monotonicity proofs. It is in its own file purely for import reasons (there is no good file to put it that imports both `set.lattice` and `finset.basic`, the latter is used in 1 lemma).

### [2020-09-26 19:15:53](https://github.com/leanprover-community/mathlib/commit/253b120)
feat(field_theory): prove primitive element theorem ([#4153](https://github.com/leanprover-community/mathlib/pull/4153))
Proof of the primitive element theorem. The main proof is in `field_theory/primitive_element.lean`. Some lemmas we used have been added to other files. We have also changed the notation for adjoining an element to a field to be easier to use.

### [2020-09-26 19:15:50](https://github.com/leanprover-community/mathlib/commit/d0b5947)
feat(algebra/universal_enveloping_algebra): construction of universal enveloping algebra and its universal property ([#4041](https://github.com/leanprover-community/mathlib/pull/4041))
## Main definitions
  * `universal_enveloping_algebra`
  * `universal_enveloping_algebra.algebra`
  * `universal_enveloping_algebra.lift`
  * `universal_enveloping_algebra.ι_comp_lift`
  * `universal_enveloping_algebra.lift_unique`
  * `universal_enveloping_algebra.hom_ext`

### [2020-09-26 17:53:17](https://github.com/leanprover-community/mathlib/commit/3ebee15)
feat(src/data/polynomial/ring_division.lean): eq_zero_of_infinite_is_root ([#4280](https://github.com/leanprover-community/mathlib/pull/4280))
add a lemma stating that a polynomial is zero if it has infinitely many roots.

### [2020-09-26 17:53:15](https://github.com/leanprover-community/mathlib/commit/376ab30)
feat(data/nat/unique_factorization): a `unique_factorization_monoid` instance on N ([#4194](https://github.com/leanprover-community/mathlib/pull/4194))
Provides a `unique_factorization_monoid` instance on `nat`
Shows its equivalence to `nat.factors`, which is list-valued

### [2020-09-26 15:49:19](https://github.com/leanprover-community/mathlib/commit/88e198a)
feat(data/multiset): count repeat lemma ([#4278](https://github.com/leanprover-community/mathlib/pull/4278))
A small lemma and renaming (of `count_repeat` to `count_repeat_self`) to count elements in a `multiset.repeat`. One part of [#4259](https://github.com/leanprover-community/mathlib/pull/4259).

### [2020-09-26 15:49:16](https://github.com/leanprover-community/mathlib/commit/8e83805)
chore(analysis/special_functions/pow): +2 lemmas about `nnreal.rpow` ([#4272](https://github.com/leanprover-community/mathlib/pull/4272))
`λ x, x^y` is continuous in more cases than `λ p, p.1^p.2`.

### [2020-09-26 15:49:14](https://github.com/leanprover-community/mathlib/commit/3177493)
feat(ring_theory/algebra, algebra/module): Add add_comm_monoid_to_add_comm_group and semiring_to_ring ([#4252](https://github.com/leanprover-community/mathlib/pull/4252))

### [2020-09-26 15:49:13](https://github.com/leanprover-community/mathlib/commit/7c0c16c)
feat(data/list/basic): Add lemmas about inits and tails ([#4222](https://github.com/leanprover-community/mathlib/pull/4222))

### [2020-09-26 13:57:50](https://github.com/leanprover-community/mathlib/commit/bc3a6cf)
chore(data/list/basic): Make it clear that `forall_mem_cons` and `ball_cons` are synonyms ([#4279](https://github.com/leanprover-community/mathlib/pull/4279))

### [2020-09-26 12:12:06](https://github.com/leanprover-community/mathlib/commit/9b09f90)
feat(ennreal): some lemmas about ennreal ([#4262](https://github.com/leanprover-community/mathlib/pull/4262))
Also some lemmas about norms in (e)nnreal.

### [2020-09-26 10:16:14](https://github.com/leanprover-community/mathlib/commit/280a42e)
chore(topology/instances/nnreal): reuse `order_topology_of_ord_connected` ([#4277](https://github.com/leanprover-community/mathlib/pull/4277))

### [2020-09-26 10:16:12](https://github.com/leanprover-community/mathlib/commit/b8b6f5d)
chore(order/filter/archimedean): move&generalize a few lemmas ([#4275](https://github.com/leanprover-community/mathlib/pull/4275))
* `tendsto_coe_nat_real_at_top_iff`: `tendsto_coe_nat_at_top_iff`,
  generalize to a linear ordered archimedean semiring;
* `tendsto_coe_nat_real_at_top_at_top`: `tendsto_coe_nat_at_top_at_top`,
  generalize to a linear ordered archimedean semiring;
* `tendsto_coe_int_real_at_top_iff`: `tendsto_coe_int_at_top_iff`,
  generalize to a linear ordered archimedean ring;
* `tendsto_coe_int_real_at_top_at_top`: `tendsto_coe_int_at_top_at_top`,
  generalize to a linear ordered archimedean ring;
* add versions for `ℚ`;
* golf the proof of `tendsto_at_top_embedding`.

### [2020-09-26 10:16:10](https://github.com/leanprover-community/mathlib/commit/aa11589)
feat(algebra/homology, category_theory/abelian): expand API on exactness ([#4256](https://github.com/leanprover-community/mathlib/pull/4256))

### [2020-09-26 10:16:08](https://github.com/leanprover-community/mathlib/commit/61897ae)
feat(data/set/intervals/infinite): intervals are infinite ([#4241](https://github.com/leanprover-community/mathlib/pull/4241))

### [2020-09-26 10:16:06](https://github.com/leanprover-community/mathlib/commit/e3cc06e)
feat(algebraic_geometry/presheafed_space): gluing presheaves ([#4198](https://github.com/leanprover-community/mathlib/pull/4198))
#### `PresheafedSpace C` has colimits.
If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.
When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.
Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.
Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)
The limit of this diagram then constitutes the colimit presheaf.

### [2020-09-26 07:58:50](https://github.com/leanprover-community/mathlib/commit/c2f896f)
feat(data/set): add some lemmas ([#4263](https://github.com/leanprover-community/mathlib/pull/4263))
Some lemmas about sets, mostly involving disjointness
I also sneaked in the lemma `(λ x : α, y) = const α y` which is useful to rewrite with.

### [2020-09-26 07:58:48](https://github.com/leanprover-community/mathlib/commit/1892724)
feat(data/matrix): definition of `block_diagonal` ([#4257](https://github.com/leanprover-community/mathlib/pull/4257))
This PR defines `matrix.block_diagonal : (o -> matrix m n R) -> matrix (m × o) (n × o) R`. The choice to put `o` on the right hand side of the product will help with relating this to `is_basis.smul`, but it won't be a huge hassle to write `matrix (o × m) (o × m) R` instead if you prefer.
I also tried making `m` and `n` depend on `o`, giving `block_diagonal M : matrix (Σ k : o, m k) (Σ k : o, n k) R`, but that turned out to be a shotcut to `eq.rec` hell.

### [2020-09-26 06:09:45](https://github.com/leanprover-community/mathlib/commit/7aef150)
feat(category_theory): sieves ([#3909](https://github.com/leanprover-community/mathlib/pull/3909))
Define sieves, from my topos project. Co-authored by @EdAyers. 
These definitions and lemmas have been battle-tested quite a bit so I'm reasonably confident they're workable.

### [2020-09-26 02:31:08](https://github.com/leanprover-community/mathlib/commit/6289adf)
fix(order/bounded_lattice): fix some misleading theorem names ([#4271](https://github.com/leanprover-community/mathlib/pull/4271))

### [2020-09-26 01:49:24](https://github.com/leanprover-community/mathlib/commit/d76f19f)
feat(overview): expand measure theory ([#4258](https://github.com/leanprover-community/mathlib/pull/4258))

### [2020-09-26 00:58:04](https://github.com/leanprover-community/mathlib/commit/4b3570f)
chore(scripts): update nolints.txt ([#4270](https://github.com/leanprover-community/mathlib/pull/4270))
I am happy to remove some nolints for you!

### [2020-09-25 19:15:25](https://github.com/leanprover-community/mathlib/commit/85bbf8a)
feat(data/fin): `zero_eq_one_iff` and `one_eq_zero_iff` ([#4255](https://github.com/leanprover-community/mathlib/pull/4255))
Just a pair of little lemmas that were handy to me. The main benefit is that `simp` can now prove `if (0 : fin 2) = 1 then 1 else 0 = 0`, which should help with calculations using `data.matrix.notation`.

### [2020-09-25 16:57:57](https://github.com/leanprover-community/mathlib/commit/3a591e8)
chore(data/list/defs): mark pairwise.nil simp to match chain.nil ([#4254](https://github.com/leanprover-community/mathlib/pull/4254))

### [2020-09-25 16:57:55](https://github.com/leanprover-community/mathlib/commit/5e8d527)
feat(ring_theory/witt_vector/witt_polynomial): definition and basic properties ([#4236](https://github.com/leanprover-community/mathlib/pull/4236))
From the Witt vector project
This is the first of a dozen of files on Witt vectors. This file contains
the definition of the so-called Witt polynomials.
Follow-up PRs will contain:
* An important structural result on the Witt polynomials
* The definition of the ring of Witt vectors (including the ring structure)
* Several common operations on Witt vectors
* Identities between thes operations
* A comparison isomorphism between the ring of Witt vectors over F_p and
the ring of p-adic integers Z_p.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-09-25 14:53:58](https://github.com/leanprover-community/mathlib/commit/565efec)
chore(data/real/ennreal): 3 lemmas stating `∞ / b = ∞` ([#4248](https://github.com/leanprover-community/mathlib/pull/4248))

### [2020-09-25 14:53:56](https://github.com/leanprover-community/mathlib/commit/1029974)
feat(*): finite rings with char = card = n are isomorphic to zmod n ([#4234](https://github.com/leanprover-community/mathlib/pull/4234))
From the Witt vector project
I've made use of the opportunity to remove some unused arguments,
and to clean up some code by using namespacing and such.

### [2020-09-25 14:53:54](https://github.com/leanprover-community/mathlib/commit/aee16bd)
feat(data/mv_polynomial/basic): counit ([#4205](https://github.com/leanprover-community/mathlib/pull/4205))
From the Witt vector project

### [2020-09-25 14:53:52](https://github.com/leanprover-community/mathlib/commit/5deb96d)
feat(data/mv_polynomial/funext): function extensionality for polynomials ([#4196](https://github.com/leanprover-community/mathlib/pull/4196))
over infinite integral domains

### [2020-09-25 12:54:20](https://github.com/leanprover-community/mathlib/commit/680f877)
feat(data/rat/basic): coe_int_div, coe_nat_div ([#4233](https://github.com/leanprover-community/mathlib/pull/4233))
Snippet from the Witt project

### [2020-09-25 12:54:18](https://github.com/leanprover-community/mathlib/commit/9591d43)
feat(data/*): lemmas on division of polynomials by constant polynomials ([#4206](https://github.com/leanprover-community/mathlib/pull/4206))
From the Witt vector project
We provide a specialized version for polynomials over zmod n,
which turns out to be convenient in practice.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-09-25 12:54:16](https://github.com/leanprover-community/mathlib/commit/c7d818c)
feat(data/mv_polynomial/variables): vars_bind₁ and friends ([#4204](https://github.com/leanprover-community/mathlib/pull/4204))
From the Witt vector project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-09-25 10:07:16](https://github.com/leanprover-community/mathlib/commit/2313602)
feat(order/bounded_lattice): custom recursors for with_bot/with_top ([#4245](https://github.com/leanprover-community/mathlib/pull/4245))

### [2020-09-25 10:07:14](https://github.com/leanprover-community/mathlib/commit/f43bd45)
fix(tactic/lint/simp): only head-beta reduce, don't whnf ([#4237](https://github.com/leanprover-community/mathlib/pull/4237))
This is necessary to accept simp lemmas like `injective reverse`.

### [2020-09-25 10:07:12](https://github.com/leanprover-community/mathlib/commit/5da451b)
feat(data/mv_polynomial/expand): replace variables by a power ([#4197](https://github.com/leanprover-community/mathlib/pull/4197))
From the Witt vectors project.

### [2020-09-25 09:07:07](https://github.com/leanprover-community/mathlib/commit/b6154d9)
feat(category_theory/limits): small lemmas ([#4251](https://github.com/leanprover-community/mathlib/pull/4251))

### [2020-09-25 08:21:16](https://github.com/leanprover-community/mathlib/commit/40f1370)
chore(measure_theory/bochner_integration): rename/add lemmas, fix docstring ([#4249](https://github.com/leanprover-community/mathlib/pull/4249))
* add `integral_nonneg` assuming `0 ≤ f`;
* rename `integral_nonpos_of_nonpos_ae` to `integral_nonpos_of_ae`;
* add `integral_nonpos` assuming `f ≤ 0`;
* rename `integral_mono` to `integral_mono_ae`;
* add `integral_mono` assuming `f ≤ g`;
* (partially?) fix module docstring.

### [2020-09-25 06:57:20](https://github.com/leanprover-community/mathlib/commit/143c074)
feat(category_theory/cofinal): cofinal functors ([#4218](https://github.com/leanprover-community/mathlib/pull/4218))

### [2020-09-25 05:46:05](https://github.com/leanprover-community/mathlib/commit/dda82fc)
chore(*): add missing copyright, cleanup imports ([#4229](https://github.com/leanprover-community/mathlib/pull/4229))
Add missing copyright, avoid use of `import tactic`, and put each `import` statement on a separate line, for easier analysis via grep.

### [2020-09-25 00:12:04](https://github.com/leanprover-community/mathlib/commit/f9a667d)
refactor(algebra/group_power, data/nat/basic): remove redundant lemmas ([#4243](https://github.com/leanprover-community/mathlib/pull/4243))
This removes lemmas about `pow` on `nat` which are redundant
with more general versions in the root namespace.
One notable removal is `nat.pow_succ`; use `pow_succ'` instead.
In order that the general versions are available already in `data.nat.basic`,
many lemmas from `algebra.group_power.lemmas` have been moved to
`algebra.group_power.basic` (basically as many as possible without adding imports).

### [2020-09-24 22:51:18](https://github.com/leanprover-community/mathlib/commit/46bf8ca)
fix(topology/path_connected): avoid a slow use of `continuity` ([#4244](https://github.com/leanprover-community/mathlib/pull/4244))
This corrects the timeout experienced by @Nicknamen in [#3641](https://github.com/leanprover-community/mathlib/pull/3641). See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.233641/near/211107487

### [2020-09-24 20:51:05](https://github.com/leanprover-community/mathlib/commit/675f5d4)
feat(algebra/char_p): nontrivial_of_char_ne_one ([#4232](https://github.com/leanprover-community/mathlib/pull/4232))
Also renames `false_of_nonzero_of_char_one` to `false_of_nontrivial_of_char_one`
Snippet from the Witt project

### [2020-09-24 19:43:34](https://github.com/leanprover-community/mathlib/commit/5eedf32)
docs(data/complex/exponential): docstring for de Moivre ([#4242](https://github.com/leanprover-community/mathlib/pull/4242))

### [2020-09-24 17:38:37](https://github.com/leanprover-community/mathlib/commit/02ca5e2)
fix(.github/workflows/add_label_from_review.yml): fix label removal ([#4240](https://github.com/leanprover-community/mathlib/pull/4240))
The API calls were referencing the wrong field, see for example https://github.com/leanprover-community/mathlib/runs/1161014126?check_suite_focus=true#step:7:3

### [2020-09-24 17:38:35](https://github.com/leanprover-community/mathlib/commit/d670746)
feat(category_theory/monad/algebra): Add faithful instances.  ([#4227](https://github.com/leanprover-community/mathlib/pull/4227))
Adds a `faithful` instance for the forgetful functors from the Eilenberg Moore category associated to a (co)monad.

### [2020-09-24 17:38:32](https://github.com/leanprover-community/mathlib/commit/5c31dea)
feat(field_theory): intermediate fields ([#4181](https://github.com/leanprover-community/mathlib/pull/4181))
Define `intermediate_field K L` as a structure extending `subalgebra K L` and `subfield L`.
This definition required some changes in `subalgebra`, which I added in [#4180](https://github.com/leanprover-community/mathlib/pull/4180).

### [2020-09-24 17:38:30](https://github.com/leanprover-community/mathlib/commit/e23b97e)
feat(ring_theory/polynomial): decomposing the kernel of an endomorphism polynomial ([#4174](https://github.com/leanprover-community/mathlib/pull/4174))

### [2020-09-24 16:49:35](https://github.com/leanprover-community/mathlib/commit/03894df)
feat(category_theory/limits/creates): Add has_(co)limit defs ([#4239](https://github.com/leanprover-community/mathlib/pull/4239))
This PR adds four `def`s:
1. `has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape` 
2. `has_limits_of_has_limits_creates_limits`
3. `has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape`
4. `has_colimits_of_has_colimits_creates_colimits`
These show that a category `C` has (co)limits (of a given shape) given a functor `F : C ⥤ D` which creates (co)limits (of the given shape) where `D` has (co)limits (of the given shape).
See the associated zulip discussion: 
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/has_limits.20of.20has_limits.20and.20creates_limits/near/211083395

### [2020-09-24 14:02:39](https://github.com/leanprover-community/mathlib/commit/03775fb)
chore(data/mv_polynomial): aeval_rename -> aeval_id_rename ([#4230](https://github.com/leanprover-community/mathlib/pull/4230))
`aeval_rename` was not general enough, so it is renamed to
`aeval_id_rename`.
Also: state and prove the more general version of `aeval_rename`.

### [2020-09-24 10:39:14](https://github.com/leanprover-community/mathlib/commit/3484e8b)
fix(data/mv_polynomial): fix doc strings ([#4219](https://github.com/leanprover-community/mathlib/pull/4219))

### [2020-09-24 10:39:13](https://github.com/leanprover-community/mathlib/commit/f0713cb)
refactor(measure_theory/simple_func_dense): split monolithic proof ([#4199](https://github.com/leanprover-community/mathlib/pull/4199))
In the new proof the sequence of approximating functions has a simpler description: `N`-th function
sends `x` to the point `e k` which is the nearest to `f x` among the points `e 0`, ..., `e N`, where `e n`
is a dense sequence such that `e 0 = 0`.

### [2020-09-24 08:37:51](https://github.com/leanprover-community/mathlib/commit/ba8fa0f)
feat(logic/embedding): use simps ([#4169](https://github.com/leanprover-community/mathlib/pull/4169))
Some lemmas are slightly reformulated, and have a worse name. But they are (almost) never typed explicitly, since they are simp lemmas (even the occurrences in other files probably came from `squeeze_simp`).

### [2020-09-24 06:54:53](https://github.com/leanprover-community/mathlib/commit/5e934cd)
chore(*): cleanup imports, split off data/finset/preimage from data/set/finite ([#4221](https://github.com/leanprover-community/mathlib/pull/4221))
Mostly this consists of moving some content from `data.set.finite` to `data.finset.preimage`, in order to reduce imports in `data.set.finite`.

### [2020-09-24 05:52:22](https://github.com/leanprover-community/mathlib/commit/ed07cac)
feat(data/mv_polynomial/rename): coeff_rename ([#4203](https://github.com/leanprover-community/mathlib/pull/4203))
Also, use the opportunity to use R as variable for the coefficient ring
throughout the file.

### [2020-09-24 03:33:52](https://github.com/leanprover-community/mathlib/commit/ef18740)
feat(linear_algebra/eigenspace): generalized eigenvectors span the entire space ([#4111](https://github.com/leanprover-community/mathlib/pull/4111))

### [2020-09-24 02:35:58](https://github.com/leanprover-community/mathlib/commit/4e41445)
chore(scripts): update nolints.txt ([#4226](https://github.com/leanprover-community/mathlib/pull/4226))
I am happy to remove some nolints for you!

### [2020-09-24 02:35:57](https://github.com/leanprover-community/mathlib/commit/6b35819)
refactor(category_theory): make `has_image` and friends a Prop ([#4195](https://github.com/leanprover-community/mathlib/pull/4195))
This is an obious follow-up to [#3995](https://github.com/leanprover-community/mathlib/pull/3995). It changes the following declarations to a `Prop`:
* `arrow.has_lift`
* `strong_epi`
* `has_image`/`has_images`
* `has_strong_epi_mono_factorisations`
* `has_image_map`/`has_image_maps`
The big win is that there is now precisely one notion of exactness in every category with kernels and images, not a (different but provably equal) notion of exactness per `has_kernels` and `has_images` instance like in the pre-[#3995](https://github.com/leanprover-community/mathlib/pull/3995) era.

### [2020-09-24 00:15:43](https://github.com/leanprover-community/mathlib/commit/96e81fa)
feat(data/(lazy_)list): various lemmas and definitions ([#4172](https://github.com/leanprover-community/mathlib/pull/4172))

### [2020-09-23 20:55:39](https://github.com/leanprover-community/mathlib/commit/6927958)
feat(data/real/irrational): add a different formulation for irrationality ([#4213](https://github.com/leanprover-community/mathlib/pull/4213))

### [2020-09-23 20:55:36](https://github.com/leanprover-community/mathlib/commit/9aeffa8)
feat(geometry/manifold): bundled smooth map ([#3904](https://github.com/leanprover-community/mathlib/pull/3904))

### [2020-09-23 18:48:10](https://github.com/leanprover-community/mathlib/commit/72e5b9f)
feat(measure_theory): ext lemmas for measures ([#3895](https://github.com/leanprover-community/mathlib/pull/3895))
Add class `sigma_finite`.
Also some cleanup.
Rename `measurable_space.is_measurable` -> `measurable_space.is_measurable'`. This is to avoid name clash with `_root_.is_measurable`, which should almost always be used instead.
define `is_pi_system`.

### [2020-09-23 16:56:11](https://github.com/leanprover-community/mathlib/commit/7cf8fa6)
fix(archive/100-thms): update link to 100.yaml in README ([#4224](https://github.com/leanprover-community/mathlib/pull/4224))

### [2020-09-23 11:10:37](https://github.com/leanprover-community/mathlib/commit/ecd889a)
feat(data/polynomial/*): higher order derivative ([#4187](https://github.com/leanprover-community/mathlib/pull/4187))

### [2020-09-23 09:47:01](https://github.com/leanprover-community/mathlib/commit/5ab7eb0)
feat(analysis/special_functions/trigonometric): continuity and differentiability of arctan ([#4138](https://github.com/leanprover-community/mathlib/pull/4138))
Added lemmas for continuity and differentiability of arctan, as well as various supporting limit lemmas.

### [2020-09-23 07:33:15](https://github.com/leanprover-community/mathlib/commit/d7aada1)
doc(data/list/tfae): Add skeletal docstring ([#4220](https://github.com/leanprover-community/mathlib/pull/4220))

### [2020-09-23 01:02:05](https://github.com/leanprover-community/mathlib/commit/937199a)
chore(scripts): update nolints.txt ([#4216](https://github.com/leanprover-community/mathlib/pull/4216))
I am happy to remove some nolints for you!

### [2020-09-22 19:08:32](https://github.com/leanprover-community/mathlib/commit/392d3e3)
feat(archive/imo/*): add IMO 1972 B2, move IMOs to a subdirectory ([#4209](https://github.com/leanprover-community/mathlib/pull/4209))

### [2020-09-22 17:01:30](https://github.com/leanprover-community/mathlib/commit/994c31d)
feat(ring_theory/ideal/basic): mem_bot ([#4211](https://github.com/leanprover-community/mathlib/pull/4211))
Snippet from the Witt project
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-09-22 14:52:30](https://github.com/leanprover-community/mathlib/commit/f2458d6)
chore(data/mv_polynomial): Rename variables ([#4208](https://github.com/leanprover-community/mathlib/pull/4208))
I renamed `α` to `R` throughout. I also changed the `\sigma` to `σ` in `basic.lean`, see leanprover-community/doc-gen[#62](https://github.com/leanprover-community/mathlib/pull/62)

### [2020-09-22 12:57:23](https://github.com/leanprover-community/mathlib/commit/516b0df)
refactor(ring_theory/algebra): re-bundle `subalgebra` ([#4180](https://github.com/leanprover-community/mathlib/pull/4180))
This PR makes `subalgebra` extend `subsemiring` instead of using `subsemiring` as a field in its definition. The refactor is needed because `intermediate_field` should simultaneously extend `subalgebra` and `subfield`, and so the type of the `carrier` fields should match.
I added some copies of definitions that use `subring` instead of `is_subring` if I needed to change these definitions anyway.

### [2020-09-22 11:28:53](https://github.com/leanprover-community/mathlib/commit/d09ef4a)
feat(category_theory/monoidal): transport monoidal structure along an equivalence ([#4123](https://github.com/leanprover-community/mathlib/pull/4123))

### [2020-09-22 11:28:51](https://github.com/leanprover-community/mathlib/commit/caffd02)
feat(data/polynomial/degree/trailing_degree): basic definitions and properties ([#4113](https://github.com/leanprover-community/mathlib/pull/4113))
Adds trailing_degree, trailing_nat_degree, trailing_coeff and various lemmas add functionality to work with trailing coefficients

### [2020-09-22 10:04:16](https://github.com/leanprover-community/mathlib/commit/58d0bfc)
feat(topology/sheaves): alternate formulation of the sheaf condition ([#4190](https://github.com/leanprover-community/mathlib/pull/4190))
Currently the sheaf condition is stated as it often is in textbooks, e.g. 
https://stacks.math.columbia.edu/tag/0072. That is, it is about an equalizer of the two maps `∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
This PR adds an equivalent formulation, saying that `F.obj (supr U)` (with its natural projection maps) is the limit of the diagram consisting of the `F.obj (U i)` and the `F.obj (U i ⊓ U j)`. 
I'd like to add further reformulations in subsequent PRs, in particular the nice one I saw in Lurie's SAG, just saying that `F.obj (supr U)` is the limit over the diagram of all `F.obj V` where `V` is an open subset of *some* `U i`. This version is actually much nicer to formalise, and I'm hoping we can translate over quite a lot of what we've already done about the sheaf condition to that version

### [2020-09-22 08:41:20](https://github.com/leanprover-community/mathlib/commit/b4641ef)
feat(l1_space): add measurability to integrable ([#4170](https://github.com/leanprover-community/mathlib/pull/4170))
This PR defines `integrable` such that `integrable` implies `measurable`. The old version is called `has_finite_integral`.
This allows us to drop *many* measurability conditions from lemmas that also require integrability.
There are some lemmas that have extra measurability conditions, if it has `integrable` as conclusion without corresponding `measurable` hypothesis.
There are many results that require an additional `[measurable_space E]` hypothesis, and some that require `[borel_space E]` or `[second_countable_space E]` (usually when using that addition is measurable).

### [2020-09-22 06:16:42](https://github.com/leanprover-community/mathlib/commit/2ae199f)
refactor(ring_theory/unique_factorization_domain): completes the refactor of `unique_factorization_domain` ([#4156](https://github.com/leanprover-community/mathlib/pull/4156))
Refactors `unique_factorization_domain` to `unique_factorization_monoid`
`unique_factorization_monoid` is a predicate
`unique_factorization_monoid` now requires no additive/subtractive structure

### [2020-09-22 00:54:05](https://github.com/leanprover-community/mathlib/commit/480c92c)
chore(scripts): update nolints.txt ([#4207](https://github.com/leanprover-community/mathlib/pull/4207))
I am happy to remove some nolints for you!

### [2020-09-21 18:45:31](https://github.com/leanprover-community/mathlib/commit/b91df55)
chore(topology/algebra/module): make `topological_module` an abbreviation ([#4200](https://github.com/leanprover-community/mathlib/pull/4200))
Also prove that a `topological_semiring` is a `topological_semimodule`.

### [2020-09-21 16:27:12](https://github.com/leanprover-community/mathlib/commit/92c0125)
chore(data/nat/digits): use nat namespace ([#4201](https://github.com/leanprover-community/mathlib/pull/4201))

### [2020-09-21 13:06:58](https://github.com/leanprover-community/mathlib/commit/4a8c38e)
chore(category_theory/limits/lattice): cleanup ([#4191](https://github.com/leanprover-community/mathlib/pull/4191))

### [2020-09-21 10:21:23](https://github.com/leanprover-community/mathlib/commit/cd4a91f)
fix(scripts/mk_all): macOS compatibility fix ([#4148](https://github.com/leanprover-community/mathlib/pull/4148))
`readlink -f` doesn't work macOS unfortunately - there are alternatives but I think it's probably safe to remove it altogether? This assumes `mk_all.sh` isn't a symlink but I can't think of a reason why it should be - and `rm_all.sh` uses `dirname "${BASH_SOURCE[0]}"` directly 🙂

### [2020-09-21 08:37:54](https://github.com/leanprover-community/mathlib/commit/e483298)
feat(ring_theory/unique_factorization_domain): API for coprime, coprime factor of a power is a power ([#4049](https://github.com/leanprover-community/mathlib/pull/4049))

### [2020-09-21 06:08:33](https://github.com/leanprover-community/mathlib/commit/40f582b)
feat(data/*/nat_antidiagonal): induction lemmas about antidiagonals ([#4193](https://github.com/leanprover-community/mathlib/pull/4193))
Adds a `nat.antidiagonal_succ` lemma for `list`, `multiset`, and `finset`, useful for proving facts about power series derivatives

### [2020-09-21 03:23:12](https://github.com/leanprover-community/mathlib/commit/d8e7bb5)
feat(tactic/tauto): optional closer tactic for `tauto` ([#4189](https://github.com/leanprover-community/mathlib/pull/4189))
`tauto` sometimes fails on easy subgoals; instead of backtracking
and discarding the work, the user can now supply a closer tactic
to the remaining goals, such as `cc`, `simp`, or `linarith`.
this also wraps `tauto` in a `focus1`, which allows for better
error messages.

### [2020-09-20 23:55:02](https://github.com/leanprover-community/mathlib/commit/f77d5d6)
feat(data/finset): add lemma for empty filter ([#4188](https://github.com/leanprover-community/mathlib/pull/4188))
A little lemma, analogous to `filter_true_of_mem` to make it convenient to reduce a filter which always fails.

### [2020-09-20 21:53:36](https://github.com/leanprover-community/mathlib/commit/db9842c)
feat(analysis/calculus/times_cont_diff): inversion of continuous linear maps is smooth ([#4185](https://github.com/leanprover-community/mathlib/pull/4185))
- Introduce an `inverse` function on the space of continuous linear maps between two Banach spaces, which is the inverse if the map is a continuous linear equivalence and zero otherwise.
- Prove that this function is `times_cont_diff_at` each `continuous_linear_equiv`.
- Some of the constructions used had been introduced in [#3282](https://github.com/leanprover-community/mathlib/pull/3282) and placed in `analysis.normed_space.operator_norm` (normed spaces); they are moved to the earlier file `topology.algebra.module` (topological vector spaces).

### [2020-09-20 21:53:34](https://github.com/leanprover-community/mathlib/commit/d774ef6)
feat(topology/path_connected): add lemmas about paths and continuous families of paths ([#4063](https://github.com/leanprover-community/mathlib/pull/4063))
From the sphere eversion project (see https://github.com/leanprover-community/sphere-eversion/pull/12)

### [2020-09-20 20:05:32](https://github.com/leanprover-community/mathlib/commit/884e90b)
feat(measure_theory): Borel-Cantelli ([#4166](https://github.com/leanprover-community/mathlib/pull/4166))
```lean
lemma measure_limsup_eq_zero {s : ℕ → set α} (hs : ∀ i, is_measurable (s i))
  (hs' : (∑' i, μ (s i)) ≠ ⊤) : μ (limsup at_top s) = 0
```
There is a converse statement that is also called Borel-Cantelli, but we can't state it yet, because we don't know what independent events are.

### [2020-09-20 16:28:24](https://github.com/leanprover-community/mathlib/commit/2c9b063)
feat(algebra/big_operators): add prod boole lemma ([#4192](https://github.com/leanprover-community/mathlib/pull/4192))
A small lemma to simplify products of indicator functions

### [2020-09-20 00:47:20](https://github.com/leanprover-community/mathlib/commit/44667ba)
feat(ring_theory/power_series): power series lemmas ([#4171](https://github.com/leanprover-community/mathlib/pull/4171))
A couple of little lemmas for multiplication and coefficients

### [2020-09-20 00:00:33](https://github.com/leanprover-community/mathlib/commit/9232032)
refactor(linear_algebra/tensor_algebra): build as a quotient of a free algebra ([#4079](https://github.com/leanprover-community/mathlib/pull/4079))

### [2020-09-19 23:11:09](https://github.com/leanprover-community/mathlib/commit/7013e5b)
feat(category_theory/internal): commutative monoid objects ([#4186](https://github.com/leanprover-community/mathlib/pull/4186))
This reprises a series of our recent PRs on monoid objects in monoidal categories, developing the same material for commutative monoid objects in braided categories.

### [2020-09-19 20:26:57](https://github.com/leanprover-community/mathlib/commit/5b143ff)
feat(data/set/basic): a few lemmas ([#4184](https://github.com/leanprover-community/mathlib/pull/4184))

### [2020-09-19 19:45:22](https://github.com/leanprover-community/mathlib/commit/640ba6c)
feat(geometry/euclidean): cospherical points ([#4178](https://github.com/leanprover-community/mathlib/pull/4178))
Define cospherical points in a Euclidean space (the general-dimension
version of the two-dimensional concept of a set of points being
concyclic) and prove some very basic lemmas about them.

### [2020-09-19 19:03:21](https://github.com/leanprover-community/mathlib/commit/02b492a)
feat(category_theory/Mon): Mon_ C has limits when C does ([#4133](https://github.com/leanprover-community/mathlib/pull/4133))
If `C` has limits, so does `Mon_ C`.
(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)

### [2020-09-19 04:51:22](https://github.com/leanprover-community/mathlib/commit/567954f)
feat(category_theory): `lim : (J ⥤ C) ⥤ C` is lax monoidal when `C` is monoidal ([#4132](https://github.com/leanprover-community/mathlib/pull/4132))
A step towards constructing limits in `Mon_ C` (and thence towards sheaves of modules as internal objects).

### [2020-09-19 03:33:07](https://github.com/leanprover-community/mathlib/commit/04fe4b6)
feat(algebra/ring_quot): quotients of noncommutative rings ([#4078](https://github.com/leanprover-community/mathlib/pull/4078))

### [2020-09-18 21:57:43](https://github.com/leanprover-community/mathlib/commit/bf7a2ed)
fix(conditionally_complete_lattice): add instance ([#4183](https://github.com/leanprover-community/mathlib/pull/4183))
there was no instance from `conditionally_complete_linear_order_bot` to `conditionally_complete_linear_order`. It is added by this change.

### [2020-09-18 21:57:41](https://github.com/leanprover-community/mathlib/commit/c2ae6c0)
doc(simps): explain short_name ([#4182](https://github.com/leanprover-community/mathlib/pull/4182))

### [2020-09-18 21:57:39](https://github.com/leanprover-community/mathlib/commit/0269a76)
feat(integration): integral commutes with continuous linear maps ([#4167](https://github.com/leanprover-community/mathlib/pull/4167))
from the sphere eversion project. Main result:
```lean
continuous_linear_map.integral_apply_comm {α : Type*} [measurable_space α] {μ : measure α} 
  {E : Type*} [normed_group E]  [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E] {F : Type*} [normed_group F]
  [second_countable_topology F] [normed_space ℝ F] [complete_space F]
  [measurable_space F] [borel_space F] 
  {φ : α → E} (L : E →L[ℝ] F) (φ_meas : measurable φ) (φ_int : integrable φ μ) :
  ∫ a, L (φ a) ∂μ = L (∫ a, φ a ∂μ)
```

### [2020-09-18 20:21:39](https://github.com/leanprover-community/mathlib/commit/4e3729b)
feat(geometry/euclidean/basic): intersections of circles ([#4088](https://github.com/leanprover-community/mathlib/pull/4088))
Add two versions of the statement that two circles in two-dimensional
space intersect in at most two points, along with some lemmas involved
in the proof (some of which can be interpreted in terms of
intersections of circles or spheres and lines).

### [2020-09-18 17:25:27](https://github.com/leanprover-community/mathlib/commit/9051aa7)
feat(polynomial): prepare for transcendence of e by adding small lemmas ([#4175](https://github.com/leanprover-community/mathlib/pull/4175))
This will be a series of pull request to prepare for the proof of transcendence of e by adding lots of small lemmas.

### [2020-09-18 11:37:08](https://github.com/leanprover-community/mathlib/commit/ae72826)
feat(data/mv_polynomial): define comap ([#4161](https://github.com/leanprover-community/mathlib/pull/4161))
More from the Witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-18 09:43:35](https://github.com/leanprover-community/mathlib/commit/953a5dc)
feat(category_theory/monoidal): monoid objects are just lax monoidal functors from punit ([#4121](https://github.com/leanprover-community/mathlib/pull/4121))

### [2020-09-18 08:44:32](https://github.com/leanprover-community/mathlib/commit/c158ce8)
feat(analysis/calculus): converse mean value inequality  ([#4173](https://github.com/leanprover-community/mathlib/pull/4173))
Also restate mean value inequality in terms of `lipschitz_on_with`.
From the sphere eversion project.

### [2020-09-18 08:44:30](https://github.com/leanprover-community/mathlib/commit/f68c936)
feat(analysis/normed_space/real_inner_product): orthogonal subspace lemmas ([#4152](https://github.com/leanprover-community/mathlib/pull/4152))
Add a few more lemmas about `submodule.orthogonal`.

### [2020-09-18 08:44:28](https://github.com/leanprover-community/mathlib/commit/b00b01f)
feat(linear_algebra/affine_space): more lemmas ([#4127](https://github.com/leanprover-community/mathlib/pull/4127))
Add another batch of lemmas relating to affine spaces.  These include
factoring out `vector_span_mono` as a combination of two other lemmas
that's used several times, and additional variants of lemmas relating
to finite-dimensional subspaces.

### [2020-09-18 07:44:06](https://github.com/leanprover-community/mathlib/commit/43ff7dc)
feat(topology/algebra/ordered): generalize two lemmas ([#4177](https://github.com/leanprover-community/mathlib/pull/4177))
they hold for conditionally complete linear orders, not just for complete linear orders

### [2020-09-18 05:39:35](https://github.com/leanprover-community/mathlib/commit/58883e3)
feat(topology/ωCPO): define Scott topology in connection with ω-complete partial orders ([#4037](https://github.com/leanprover-community/mathlib/pull/4037))

### [2020-09-18 00:57:16](https://github.com/leanprover-community/mathlib/commit/52d4b92)
chore(scripts): update nolints.txt ([#4176](https://github.com/leanprover-community/mathlib/pull/4176))
I am happy to remove some nolints for you!

### [2020-09-17 15:33:38](https://github.com/leanprover-community/mathlib/commit/5a2e7d7)
refactor(field-theory/subfield): bundled subfields ([#4159](https://github.com/leanprover-community/mathlib/pull/4159))
Define bundled subfields. The contents of the new `subfield` file are basically a copy of `subring.lean` with the replacement `subring` -> `subfield`, and the proofs repaired as necessary.
As with the other bundled subobject refactors, other files depending on unbundled subfields now import `deprecated.subfield`.

### [2020-09-17 15:33:35](https://github.com/leanprover-community/mathlib/commit/34ebade)
feat(algebra/free_algebra): free (noncommutative) algebras ([#4077](https://github.com/leanprover-community/mathlib/pull/4077))
Previously, @adamtopaz constructed the tensor algebra of an `R`-module via a direct construction of a quotient of a free algebra.
This uses essentially the same construction to build a free algebra (on a type) directly. In a PR coming shortly, I'll refactor his development of the tensor algebra to use this construction.

### [2020-09-17 14:29:36](https://github.com/leanprover-community/mathlib/commit/b62dd28)
feat(linear_algebra/eigenspace): beginning to relate minimal polynomials to eigenvalues ([#4165](https://github.com/leanprover-community/mathlib/pull/4165))
rephrases some lemmas in `linear_algebra` to use `aeval` instead of `eval2` and `algebra_map`
shows that an eigenvalue of a linear transformation is a root of its minimal polynomial, and vice versa

### [2020-09-17 05:26:28](https://github.com/leanprover-community/mathlib/commit/265c587)
doc(meta/converter/interactive): Add tactic documentation for a subset of `conv` tactics ([#4144](https://github.com/leanprover-community/mathlib/pull/4144))

### [2020-09-16 18:50:15](https://github.com/leanprover-community/mathlib/commit/7db9e13)
feat(data/monoid_algebra): ext lemma ([#4162](https://github.com/leanprover-community/mathlib/pull/4162))
A small lemma that was useful in the Witt vector project.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-16 15:49:12](https://github.com/leanprover-community/mathlib/commit/9f9a8c0)
feat(readme): add @hrmacbeth to maintainers list ([#4168](https://github.com/leanprover-community/mathlib/pull/4168))

### [2020-09-16 11:42:42](https://github.com/leanprover-community/mathlib/commit/623c846)
feat(data/mv_polynomial/variables): add facts about vars and mul ([#4149](https://github.com/leanprover-community/mathlib/pull/4149))
More from the Witt vectors branch.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-16 09:39:46](https://github.com/leanprover-community/mathlib/commit/6603c6d)
fix(simps): use coercion for algebra morphisms ([#4155](https://github.com/leanprover-community/mathlib/pull/4155))
Previously it tried to apply whnf on an open expression, which failed, so it wouldn't find the coercion. Now it applied whnf before opening the expression.
Also use `simps` for `fixed_points.to_alg_hom`. The generated lemmas are
```lean
fixed_points.to_alg_hom_to_fun : ∀ (G : Type u) (F : Type v) [_inst_4 : group G] [_inst_5 : field F]
[_inst_6 : faithful_mul_semiring_action G F],
  ⇑(to_alg_hom G F) =
    λ (g : G),
      {to_fun := (mul_semiring_action.to_semiring_hom G F g).to_fun,
       map_one' := _,
       map_mul' := _,
       map_zero' := _,
       map_add' := _,
       commutes' := _}
```

### [2020-09-16 08:03:28](https://github.com/leanprover-community/mathlib/commit/9a11efb)
feat(metric_space): add lipschitz_on_with ([#4151](https://github.com/leanprover-community/mathlib/pull/4151))
The order of the explicit arguments in this definition is open for negotiation.
From the sphere eversion project.

### [2020-09-16 08:03:26](https://github.com/leanprover-community/mathlib/commit/4c9d3a5)
feat(operator_norm): smul_right lemmas ([#4150](https://github.com/leanprover-community/mathlib/pull/4150))
from the sphere eversion project
We need a version of `continuous_linear_map.smul_right` that is itself a continuous linear map from a normed space to a space of continuous linear maps. 
breaking changes:
* rename `smul_right_norm` to `norm_smul_right_apply`
* in `homothety_norm` remove useless sign assumption and switch from assuming positive dimension to `nontrivial`

### [2020-09-16 06:06:09](https://github.com/leanprover-community/mathlib/commit/f585ce5)
feat(category_theory): monoidal natural transformations and discrete monoidal categories ([#4112](https://github.com/leanprover-community/mathlib/pull/4112))

### [2020-09-15 20:10:38](https://github.com/leanprover-community/mathlib/commit/4c896c5)
chore(undergrad.yaml): updates ([#4160](https://github.com/leanprover-community/mathlib/pull/4160))
Added a bunch of things to `undergrad.yaml`: generalized eigenspaces, conjugacy classes in a group, the orthogonal complement, continuity of monotone functions and their inverses, inverse hyperbolic trig functions, radius of convergence.  Also changed (hopefully improved) some translations.

### [2020-09-15 12:59:56](https://github.com/leanprover-community/mathlib/commit/d3a1719)
feat(category_theory/is_connected): make `is_connected` a Prop ([#4136](https://github.com/leanprover-community/mathlib/pull/4136))
Also renames `connected` to `is_connected`, and relies on `classical.arbitrary` slightly less.

### [2020-09-15 11:43:08](https://github.com/leanprover-community/mathlib/commit/427d414)
feat(data/enat): some API and a module docstring ([#4103](https://github.com/leanprover-community/mathlib/pull/4103))

### [2020-09-15 01:03:57](https://github.com/leanprover-community/mathlib/commit/7c321f8)
chore(scripts): update nolints.txt ([#4157](https://github.com/leanprover-community/mathlib/pull/4157))
I am happy to remove some nolints for you!

### [2020-09-14 23:27:33](https://github.com/leanprover-community/mathlib/commit/b83362e)
fix(order/ocpo): remove trace option ([#4154](https://github.com/leanprover-community/mathlib/pull/4154))
(it did not produce any output)

### [2020-09-14 23:27:32](https://github.com/leanprover-community/mathlib/commit/a0adcc0)
chore(category_theory/zero): lemmas for has_zero_morphisms.comp_zero|zero_comp ([#4142](https://github.com/leanprover-community/mathlib/pull/4142))
The axioms of `has_zero_morphisms` never had lemmas written for them, so everyone has been using the typeclass fields directly.

### [2020-09-14 23:27:30](https://github.com/leanprover-community/mathlib/commit/3d73bd8)
feat(topology/algebra/ordered): monotone continuous function is homeomorphism, relative version ([#4043](https://github.com/leanprover-community/mathlib/pull/4043))
A function `f : α → β` restricts to a homeomorphism `(Ioo a b) → β`, if it (1) is order-preserving within the interval; (2) is `continuous_on` the interval; (3) tends to positive infinity at the right endpoint; and (4) tends to negative infinity at the left endpoint. The orders `α`, `β` are required to be conditionally complete, and the order on `α` must also be dense.

### [2020-09-14 21:25:17](https://github.com/leanprover-community/mathlib/commit/ff2639d)
feat(tactic/pretty_cases): provide a skeleton for a proof by induction / cases ([#4093](https://github.com/leanprover-community/mathlib/pull/4093))

### [2020-09-14 19:35:47](https://github.com/leanprover-community/mathlib/commit/218ef40)
feat(measure_theory): image of Lebesgue measure under shift/rescale ([#3760](https://github.com/leanprover-community/mathlib/pull/3760))

### [2020-09-14 16:35:45](https://github.com/leanprover-community/mathlib/commit/a18be37)
feat(ring_theory/ideal/over): Going up theorem for integral extensions ([#4064](https://github.com/leanprover-community/mathlib/pull/4064))
The main statement is `exists_ideal_over_prime_of_is_integral` which shows that for an integral extension, every prime ideal of the original ring lies under some prime ideal of the extension ring.
`is_field_of_is_integral_of_is_field` is a brute force proof that if `R → S` is an integral extension, and `S` is a field, then `R` is also a field (using the somewhat new `is_field` proposition). `is_maximal_comap_of_is_integral_of_is_maximal` Gives essentially the same statement in terms of maximal ideals.
`disjoint_compl` has also been replaced with `disjoint_compl_left` and `disjoint_compl_right` variants.

### [2020-09-14 15:36:04](https://github.com/leanprover-community/mathlib/commit/6babb55)
fix(normed_space): fixed a typo from [#4099](https://github.com/leanprover-community/mathlib/pull/4099) ([#4147](https://github.com/leanprover-community/mathlib/pull/4147))
This lemma was less general that it should be because migrating it to its
mathlib place messed up the typeclass assumptions.

### [2020-09-14 15:36:02](https://github.com/leanprover-community/mathlib/commit/8877606)
chore(ci): teach bors and GitHub about new labels ([#4146](https://github.com/leanprover-community/mathlib/pull/4146))

### [2020-09-14 15:35:59](https://github.com/leanprover-community/mathlib/commit/49fc7ed)
feat(measure_theory): assorted integration lemmas ([#4145](https://github.com/leanprover-community/mathlib/pull/4145))
from the sphere eversion project
This is still preparations for differentiation of integals depending on a parameter.

### [2020-09-14 15:35:57](https://github.com/leanprover-community/mathlib/commit/5f45c0c)
feat(linear_algebra/finite_dimensional): finite-dimensional submodule lemmas / instances ([#4128](https://github.com/leanprover-community/mathlib/pull/4128))
Add the lemma that a submodule contained in a finite-dimensional
submodule is finite-dimensional, and instances that allow type class
inference to show some infs and sups involving finite-dimensional
submodules are finite-dimensional.  These are all useful when working
with finite-dimensional submodules in a space that may not be
finite-dimensional itself.
Given the new instances, `dim_sup_add_dim_inf_eq` gets its type class
requirements relaxed to require only the submodules to be
finite-dimensional rather than the whole space.
`linear_independent_iff_card_eq_findim_span` is added as a variant of
`linear_independent_of_span_eq_top_of_card_eq_findim` for vectors not
necessarily spanning the whole space (implemented as an `iff` lemma
using `findim_span_eq_card` for the other direction).

### [2020-09-14 14:48:27](https://github.com/leanprover-community/mathlib/commit/d5c58eb)
chore(category_theory/*): make all forgetful functors use explicit arguments ([#4139](https://github.com/leanprover-community/mathlib/pull/4139))
As suggested as https://github.com/leanprover-community/mathlib/pull/4131#discussion_r487527599, for the sake of more uniform API.

### [2020-09-14 12:41:02](https://github.com/leanprover-community/mathlib/commit/a998fd1)
feat(algebra/category/Module): the monoidal category of R-modules is symmetric ([#4140](https://github.com/leanprover-community/mathlib/pull/4140))

### [2020-09-14 12:41:00](https://github.com/leanprover-community/mathlib/commit/e35e287)
refactor(data/nat/*): cleanup data.nat.basic, split data.nat.choose ([#4135](https://github.com/leanprover-community/mathlib/pull/4135))
This PR rearranges `data.nat.basic` so the lemmas are now in (hopefully appropriately-named) markdown sections. It also moves several sections (mostly ones that introduced new `def`s) into new files:
- `data.nat.fact`
- `data.nat.psub` (maybe this could be named `data.nat.partial`?)
- `data.nat.log`
- `data.nat.with_bot`
`data.nat.choose` has been split into a directory:
- The definition of `nat.choose` and basic lemmas about it have been moved from `data.nat.basic` into `data.nat.choose.basic`
- The binomial theorem and related lemmas involving sums are now in `data.nat.choose.sum`; the following lemmas are now in the `nat` namespace:
  - `sum_range_choose`
  - `sum_range_choose_halfway`
  - `choose_middle_le_pow`
- Divisibility properties of binomial coefficients are now in `data.nat.choose.dvd`.
Other changes:
- added `nat.pow_two_sub_pow_two` to `data.nat.basic`.
- module docs & doc strings for `data.nat.sqrt`

### [2020-09-14 11:13:26](https://github.com/leanprover-community/mathlib/commit/39962b7)
chore(data/polynomial/derivative): golf proof of mem_support_derivative ([#4134](https://github.com/leanprover-community/mathlib/pull/4134))
Golfed proof to be similar to what it was like prior to the refactor.

### [2020-09-14 10:24:38](https://github.com/leanprover-community/mathlib/commit/6756d47)
feat(category_theory): Mon_.forget reflects isos ([#4131](https://github.com/leanprover-community/mathlib/pull/4131))
A step along the way to `sheaf X (Mon_ C) ~ Mon_ (sheaf X C)`.

### [2020-09-14 09:42:31](https://github.com/leanprover-community/mathlib/commit/bbfeff3)
feat(data/mv_polynomial/monad): mv_polynomial is a monad in two different ways ([#4080](https://github.com/leanprover-community/mathlib/pull/4080))
These definitions and lemmas significantly decrease the pain in several computations in the Witt project.

### [2020-09-14 09:42:28](https://github.com/leanprover-community/mathlib/commit/ed71b2d)
feat(computability/tm_computable): define computable (in polytime) for TMs, prove id is computable in constant time  ([#4048](https://github.com/leanprover-community/mathlib/pull/4048))
We define computability in polynomial time to be used in our future PR on P and NP.
We also prove that id is computable in constant time.
<!-- put comments you want to keep out of the PR commit here -->

### [2020-09-14 08:03:38](https://github.com/leanprover-community/mathlib/commit/dce6b37)
chore(algebra/homology): cleanup instances post [#3995](https://github.com/leanprover-community/mathlib/pull/3995) ([#4137](https://github.com/leanprover-community/mathlib/pull/4137))

### [2020-09-14 08:03:36](https://github.com/leanprover-community/mathlib/commit/1c2ddbc)
feat(field_theory/fixed): dimension over fixed field is order of group ([#4125](https://github.com/leanprover-community/mathlib/pull/4125))
```lean
theorem dim_fixed_points (G : Type u) (F : Type v) [group G] [field F]
  [fintype G] [faithful_mul_semiring_action G F] :
  findim (fixed_points G F) F = fintype.card G
````

### [2020-09-14 08:03:35](https://github.com/leanprover-community/mathlib/commit/b1e5a6b)
doc(measure_theory): docstrings for continuity from above and below ([#4122](https://github.com/leanprover-community/mathlib/pull/4122))

### [2020-09-14 08:03:33](https://github.com/leanprover-community/mathlib/commit/5a478f0)
doc(category_theory/natural_isomorphism): documentation and cleanup ([#4120](https://github.com/leanprover-community/mathlib/pull/4120))

### [2020-09-14 08:03:31](https://github.com/leanprover-community/mathlib/commit/51608f4)
feat(linear_algebra/affine_space,geometry/euclidean): simplex centers and order of points ([#4116](https://github.com/leanprover-community/mathlib/pull/4116))
Add lemmas that the centroid of an injective indexed family of points
does not depend on the indices of those points, only on the set of
points in their image, and likewise that the centroid, circumcenter
and Monge point of a simplex and thus the orthocenter of a triangle do
not depend on the order in which the vertices are indexed by `fin (n + 1)`,
only on the set of vertices.

### [2020-09-14 08:03:29](https://github.com/leanprover-community/mathlib/commit/b19fbd7)
feat(ring_theory/algebra_tower): coefficients for a basis in an algebra tower ([#4114](https://github.com/leanprover-community/mathlib/pull/4114))
This PR gives an expression for `(is_basis.smul hb hc).repr` in terms of `hb.repr` and `hc.repr`, useful if you have a field extension `L / K`, and `x y : L`, and want to write `y` in terms of the power basis of `K(x)`.

### [2020-09-14 06:53:07](https://github.com/leanprover-community/mathlib/commit/e355933)
chore(category_theory/limits): remove unnecessary typeclass arguments ([#4141](https://github.com/leanprover-community/mathlib/pull/4141))
Ongoing cleanup post [#3995](https://github.com/leanprover-community/mathlib/pull/3995).
Previously we couldn't construct things like `instance : has_kernel (0 : X \hom Y)`, because it wouldn't have agreed definitionally with more general instances. Now we can.

### [2020-09-14 00:14:59](https://github.com/leanprover-community/mathlib/commit/bd385fb)
chore(category_theory/limits/functor_category): shuffle limits in functor cats ([#4124](https://github.com/leanprover-community/mathlib/pull/4124))
Give `is_limit` versions for statements about limits in the functor category, and write the `has_limit` versions in terms of those.
This also generalises the universes a little.
As usual, suggestions for better docstrings or better names appreciated!

### [2020-09-13 08:21:22](https://github.com/leanprover-community/mathlib/commit/5d35e62)
feat(algebraic_geometry/*): Gamma the global sections functor ([#4126](https://github.com/leanprover-community/mathlib/pull/4126))

### [2020-09-13 03:55:56](https://github.com/leanprover-community/mathlib/commit/f403a8b)
feat(category_theory/limits/types): is_limit versions of limits in type ([#4130](https://github.com/leanprover-community/mathlib/pull/4130))
`is_limit` versions for definitions and lemmas about limits in `Type u`.

### [2020-09-13 01:01:54](https://github.com/leanprover-community/mathlib/commit/dd43823)
chore(scripts): update nolints.txt ([#4129](https://github.com/leanprover-community/mathlib/pull/4129))
I am happy to remove some nolints for you!

### [2020-09-12 18:30:15](https://github.com/leanprover-community/mathlib/commit/f3326db)
feat(normed_space): second countability for linear maps ([#4099](https://github.com/leanprover-community/mathlib/pull/4099))
From the sphere eversion project, various lemmas about continuous linear maps and a theorem: if E is finite dimensional and F is second countable then the space of continuous linear maps from E to F is second countable.

### [2020-09-12 16:34:13](https://github.com/leanprover-community/mathlib/commit/c8771b6)
fix(algebra/ring/basic): delete mul_self_sub_mul_self_eq ([#4119](https://github.com/leanprover-community/mathlib/pull/4119))
It's redundant with `mul_self_sub_mul_self`.
Also renamed `mul_self_sub_one_eq` to `mul_self_sub_one`.

### [2020-09-12 15:49:53](https://github.com/leanprover-community/mathlib/commit/169384a)
feat(slim_check): add test cases ([#4100](https://github.com/leanprover-community/mathlib/pull/4100))

### [2020-09-12 09:38:07](https://github.com/leanprover-community/mathlib/commit/c3a6a69)
doc(group_theory/subgroup): fix links in module doc ([#4115](https://github.com/leanprover-community/mathlib/pull/4115))

### [2020-09-12 09:38:05](https://github.com/leanprover-community/mathlib/commit/88dd01b)
chore(category_theory): minor cleanups ([#4110](https://github.com/leanprover-community/mathlib/pull/4110))

### [2020-09-12 07:45:55](https://github.com/leanprover-community/mathlib/commit/b1a210e)
feat(logic/basic): Add more simp lemmas for forall ([#4117](https://github.com/leanprover-community/mathlib/pull/4117))

### [2020-09-12 06:00:57](https://github.com/leanprover-community/mathlib/commit/3419986)
feat(category_theory/limits): make has_limit a Prop ([#3995](https://github.com/leanprover-community/mathlib/pull/3995))
We change `has_limit` so that it is only an existential statement that limit data exists, and in particular lives in `Prop`.
This means we can safely have multiple `has_limit` classes for the same functor, because proof irrelevance ensures Lean sees them all as the same.
We still have access to the API which lets us pretend we have consistently chosen limits, but now these limits are provided by the axiom of choice and hence are definitionally opaque.

### [2020-09-12 01:05:19](https://github.com/leanprover-community/mathlib/commit/f6a65cf)
chore(scripts): update nolints.txt ([#4118](https://github.com/leanprover-community/mathlib/pull/4118))
I am happy to remove some nolints for you!

### [2020-09-11 17:48:45](https://github.com/leanprover-community/mathlib/commit/7bade58)
feat(logic/basic): Add forall_apply_eq_imp_iff ([#4109](https://github.com/leanprover-community/mathlib/pull/4109))
Also adds forall_apply_eq_imp_iff' for swapped forall arguments
This means that `forall_range_iff` can now be solved by `simp`.
This requires changes in data/pfun and measure_theory/borel_space, where non-terminal `simp`s broke.

### [2020-09-11 17:48:43](https://github.com/leanprover-community/mathlib/commit/17a5807)
feat(category_theory/limits/fubini): another formulation for limits commuting ([#4034](https://github.com/leanprover-community/mathlib/pull/4034))
The statement that you can swap limits, rather than just combine into a single limit as we had before.
(This just uses two copies of the previous isomorphism.)

### [2020-09-11 17:48:40](https://github.com/leanprover-community/mathlib/commit/045619e)
feat(topology/sheaves): sheafification ([#3937](https://github.com/leanprover-community/mathlib/pull/3937))
# Sheafification of `Type` valued presheaves
We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.
We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.
We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.
## Future work
Show that the map induced on stalks by `to_sheafify` is the inverse of `stalk_to_fiber`.
Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor.

### [2020-09-11 17:48:37](https://github.com/leanprover-community/mathlib/commit/5509a30)
feat(category_theory/skeleton): add skeletal categories and construct a special case ([#3929](https://github.com/leanprover-community/mathlib/pull/3929))
I'm interested in the quotient construction of the skeleton for a thin category in particular for topos and sheafification PRs, but of course the general construction is useful too, so I've marked that as TODO and I'll make a followup PR so that this one doesn't get too big.
The advantage of handling this special case separately is that the skeleton of a thin category is a partial order, and so lattice constructions can be used (which is needed for my application), and also there are nice definitional equalities.

### [2020-09-11 15:53:17](https://github.com/leanprover-community/mathlib/commit/847f87e)
feat(geometry/euclidean/circumcenter): lemmas on orthogonal projection and reflection ([#4087](https://github.com/leanprover-community/mathlib/pull/4087))
Add more lemmas about orthogonal projection and the circumcenter of a
simplex (so substantially simplifying the proof of
`orthogonal_projection_circumcenter`).  Then prove a lemma
`eq_or_eq_reflection_of_dist_eq` that if we fix a distance a point has
to all the vertices of a simplex, any two possible positions of that
point in one dimension higher than the simplex are equal or
reflections of each other in the subspace of the simplex.

### [2020-09-11 15:53:15](https://github.com/leanprover-community/mathlib/commit/872a37e)
cleanup(group_theory/presented_group): () -> [], and remove some FIXMEs ([#4076](https://github.com/leanprover-community/mathlib/pull/4076))

### [2020-09-11 15:53:13](https://github.com/leanprover-community/mathlib/commit/377c7c9)
feat(category_theory/braided): braiding and unitors ([#4075](https://github.com/leanprover-community/mathlib/pull/4075))
The interaction between braidings and unitors in a braided category.
Requested by @cipher1024 for some work he's doing on monads.
I've changed the statements of some `@[simp]` lemmas, in particular `left_unitor_tensor`, `left_unitor_tensor_inv`, `right_unitor_tensor`, `right_unitor_tensor_inv`. The new theory is that the components of a unitor indexed by a tensor product object are "more complicated" than other unitors. (We already follow the same principle for simplifying associators using the pentagon equation.)

### [2020-09-11 15:53:11](https://github.com/leanprover-community/mathlib/commit/a1cbe88)
feat(logic/basic, logic/function/basic): involute ite  ([#4074](https://github.com/leanprover-community/mathlib/pull/4074))
Some lemmas about `ite`:
- `(d)ite_not`: exchanges the branches of an `(d)ite`
  when negating the given prop.
- `involutive.ite_not`: applying an involutive function to an `ite`
  negates the prop
Other changes:
Generalize the arguments for `(d)ite_apply` and `apply_(d)ite(2)`
to `Sort*` over `Type*`.

### [2020-09-11 15:53:09](https://github.com/leanprover-community/mathlib/commit/832acd6)
feat(data/{sym2,sym}) decidable version of sym2.mem.other, filling out some of sym API ([#4008](https://github.com/leanprover-community/mathlib/pull/4008))
Removes `sym2.vmem` and replaces it with `sym2.mem.other'`, which can get the other element of a pair in the presence of decidable equality. Writing `sym2.mem.other'` was beyond my abilities when I created `sym2.vmem`, and seeing that vmem is extremely specialized and has no immediate use, it's probably best to remove it.
Adds some assorted simp lemmas, and also an additional lemma that `sym2.mem.other` is, in some sense, an involution.
Adds to the API for `sym`.  This is from taking some of the interface for multisets.  (I was exploring whether `sym2 α` should be re-implemented as `sym α 2` and trying to add enough to `sym` to pull it off, but it doesn't seem to be worth it in the end.)
(I'm not committing a recursor for `sym α n`, which lets you represent elements by vectors of length `n`.  It needs some cleanup.)

### [2020-09-11 14:46:51](https://github.com/leanprover-community/mathlib/commit/7886c27)
feat(category_theory/monoidal): lax monoidal functors take monoids to monoids ([#4108](https://github.com/leanprover-community/mathlib/pull/4108))

### [2020-09-11 14:46:48](https://github.com/leanprover-community/mathlib/commit/bd74baa)
feat(algebra/homology/exact): lemmas about exactness ([#4106](https://github.com/leanprover-community/mathlib/pull/4106))
These are a few lemmas on the way to showing how `exact` changes under isomorphisms applied to the objects. It's not everthing one might want; I'm salvaging this from an old branch and unlikely to do more in the near future, but hopefully this is mergeable progress as is.

### [2020-09-11 14:46:45](https://github.com/leanprover-community/mathlib/commit/233a802)
feat(algebraic_geometry/Scheme): Spec as Scheme ([#4104](https://github.com/leanprover-community/mathlib/pull/4104))
```lean
def Spec (R : CommRing) : Scheme
```

### [2020-09-11 14:46:44](https://github.com/leanprover-community/mathlib/commit/34e0f31)
feat(nnreal): absolute value ([#4098](https://github.com/leanprover-community/mathlib/pull/4098))

### [2020-09-11 13:30:01](https://github.com/leanprover-community/mathlib/commit/842a324)
feat(category_theory): the Grothendieck construction ([#3896](https://github.com/leanprover-community/mathlib/pull/3896))
Given a functor `F : C ⥤ Cat`, 
the objects of `grothendieck F` consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and `φ : (F.map β).obj f ⟶ f'`.
(This is only a special case of the real thing: we should treat `Cat` as a 2-category and allow `F` to be a 2-functor / pseudofunctor.)

### [2020-09-11 11:35:29](https://github.com/leanprover-community/mathlib/commit/0c57b2d)
doc(category_theory): add doc-strings and links to the stacks project ([#4107](https://github.com/leanprover-community/mathlib/pull/4107))
We'd been discussing adding a `@[stacks "007B"]` tag to add cross-references to the stacks project (and possibly include links back again -- they say they're keen).
I'm not certain that we actually have the documentation maintenance enthusiasm to make this viable, so this PR is a more lightweight solution: adding lots of links to the stacks project from doc-strings. I'd be very happy to switch back to the attribute approach later.
This is pretty close to exhaustive for the "category theory preliminaries" chapter of the stacks project, but doesn't attempt to go beyond that. I've only included links where we formalise all, or almost all (in which case I've usually left a note), of the corresponding tag.

### [2020-09-11 11:35:27](https://github.com/leanprover-community/mathlib/commit/3965e06)
chore(*): use new `extends_priority` default of 100, part 2 ([#4101](https://github.com/leanprover-community/mathlib/pull/4101))
This completes the changes started in [#4066](https://github.com/leanprover-community/mathlib/pull/4066).

### [2020-09-11 11:35:25](https://github.com/leanprover-community/mathlib/commit/bc78621)
feat(geometry/euclidean/monge_point): reflection of circumcenter ([#4062](https://github.com/leanprover-community/mathlib/pull/4062))
Show that the distance from the orthocenter of a triangle to the
reflection of the circumcenter in a side equals the circumradius (a
key fact for proving various standard properties of orthocentric
systems).

### [2020-09-11 11:35:23](https://github.com/leanprover-community/mathlib/commit/4ce27a5)
feat(category_theory/limits): filtered colimits commute with finite limits (in Type) ([#4046](https://github.com/leanprover-community/mathlib/pull/4046))

### [2020-09-11 06:18:46](https://github.com/leanprover-community/mathlib/commit/80a9e4f)
refactor(data/mv_polynomial/pderivative): make pderivative a linear map ([#4095](https://github.com/leanprover-community/mathlib/pull/4095))
Make `pderivative i` a linear map as suggested at https://github.com/leanprover-community/mathlib/pull/4083#issuecomment-689712833

### [2020-09-11 00:47:31](https://github.com/leanprover-community/mathlib/commit/9a24f68)
chore(scripts): update nolints.txt ([#4105](https://github.com/leanprover-community/mathlib/pull/4105))
I am happy to remove some nolints for you!

### [2020-09-10 18:33:51](https://github.com/leanprover-community/mathlib/commit/7d88b31)
feat(ring_theory/algebra_operations): add le_div_iff_mul_le ([#4102](https://github.com/leanprover-community/mathlib/pull/4102))

### [2020-09-10 16:46:37](https://github.com/leanprover-community/mathlib/commit/e33a777)
feat(data/fin): iffs about succ_above ordering ([#4092](https://github.com/leanprover-community/mathlib/pull/4092))
New lemmas:
`succ_above_lt_iff`
`lt_succ_above_iff`
These help avoid needing to do case analysis when faced with
inequalities about `succ_above`.

### [2020-09-10 14:56:55](https://github.com/leanprover-community/mathlib/commit/38d1715)
chore(*): update to Lean 3.20.0c, account for nat.pow removal from core ([#3985](https://github.com/leanprover-community/mathlib/pull/3985))
Outline:
* `nat.pow` has been removed from the core library.
  We now use the instance `monoid.pow` to provide `has_pow ℕ ℕ`.
* To accomodate this, `algebra.group_power` has been split into a directory.
  `algebra.group_power.basic` contains the definitions of `monoid.pow` and `nsmul`
  and whatever lemmas can be stated with very few imports. It is imported in `data.nat.basic`.
  The rest of `algebra.group_power` has moved to `algebra.group_power.lemmas`.
* The new `has_pow ℕ ℕ` now satisfies a different definitional equality:
  `a^(n+1) = a * a^n` (rather than `a^(n+1) = a^n * a`).
  As a temporary measure, the lemma `nat.pow_succ` provides the old equality
  but I plan to deprecate it in favor of the more general `pow_succ'`.
  The lemma `nat.pow_eq_pow` is gone--the two sides are now the same in all respects
  so it can be deleted wherever it was used.
* The lemmas from core that mention `nat.pow` have been moved into `data.nat.lemmas`
  and their proofs adjusted as needed to take into account the new definition.
* The module `data.bitvec` from core has moved to `data.bitvec.core` in mathlib.
Future plans:
* Remove `nat.` lemmas redundant with general `group_power` ones, like `nat.pow_add`.
  This will be easier after further shuffling of modules.

### [2020-09-10 13:02:29](https://github.com/leanprover-community/mathlib/commit/d5be9f3)
refactor(data/mv_polynomial): move `smul` lemmas into basic.lean ([#4097](https://github.com/leanprover-community/mathlib/pull/4097))
`C_mul'`, `smul_eq_C_mul` and `smul_eval` seemed a bit out of place in `comm_ring.lean`, since they only need `comm_semiring α`. So I moved them to `basic.lean` where they probably fit in a bit better?
I've also golfed the proof of `smul_eq_C_mul`.

### [2020-09-10 13:02:28](https://github.com/leanprover-community/mathlib/commit/19b9ae6)
feat(data/mv_polynomial): a few facts about `constant_coeff` and `aeval` ([#4085](https://github.com/leanprover-community/mathlib/pull/4085))
A few additional facts about `constant_coeff_map` and `aeval` from the witt vector branch.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-10 13:02:25](https://github.com/leanprover-community/mathlib/commit/d857def)
feat(slim_check): make `shrink` recursive ([#4038](https://github.com/leanprover-community/mathlib/pull/4038))
Make example shrinking recursive to make it faster and more reliable. It now acts more like a binary search and less like a linear search.

### [2020-09-10 11:22:25](https://github.com/leanprover-community/mathlib/commit/55cab6c)
feat(data/{int,nat}/cast): dvd cast lemmas ([#4086](https://github.com/leanprover-community/mathlib/pull/4086))

### [2020-09-10 08:56:58](https://github.com/leanprover-community/mathlib/commit/49bb92d)
feat(ring_theory/dedekind_domain): definitions ([#4000](https://github.com/leanprover-community/mathlib/pull/4000))
Defines `is_dedekind_domain` in three variants:
1.  `is_dedekind_domain`: Noetherian, Integrally closed, Krull dimension 1, thanks to @Vierkantor 
2. `is_dedekind_domain_dvr`: Noetherian, localization at every nonzero prime is a DVR
3. `is_dedekind_domain_inv`: Every nonzero ideal is invertible.
TODO: prove that these definitions are equivalent.
This PR also includes some misc. lemmas required to show the definitions are independent of choice of fraction field.
Co-Authored-By: mushokunosora <knaka3435@gmail.com>
Co-Authored-By: faenuccio <filippo.nuccio@univ-st-etienne.fr>
Co-Authored-By: Vierkantor <vierkantor@vierkantor.com>

### [2020-09-10 07:43:56](https://github.com/leanprover-community/mathlib/commit/8e9b1f0)
feat(linear_algebra): add `restrict` for endomorphisms ([#4053](https://github.com/leanprover-community/mathlib/pull/4053))
Add a `restrict` function for endomorphisms. Add some lemmas about the new function, including one about generalized eigenspaces. Add some additional lemmas about `linear_map.comp` that I do not use in the final proof, but still consider useful.

### [2020-09-10 05:42:47](https://github.com/leanprover-community/mathlib/commit/47264da)
feat(linear_algebra): tiny missing pieces ([#4089](https://github.com/leanprover-community/mathlib/pull/4089))
From the sphere eversion project.

### [2020-09-10 01:34:24](https://github.com/leanprover-community/mathlib/commit/9f55ed7)
feat(data/polynomial/ring_division): make `polynomial.roots` a multiset ([#4061](https://github.com/leanprover-community/mathlib/pull/4061))
The original definition of `polynomial.roots` was basically "while ∃ x, p.is_root x { finset.insert x polynomial.roots }", so it was not
too hard to replace this with `multiset.cons`.
I tried to refactor most usages of `polynomial.roots` to talk about the multiset instead of coercing it to a finset, since that should give a bit more power to the results.

### [2020-09-09 23:56:32](https://github.com/leanprover-community/mathlib/commit/660a6c4)
feat(topology): misc topological lemmas ([#4091](https://github.com/leanprover-community/mathlib/pull/4091))
From the sphere eversion project.

### [2020-09-09 23:56:30](https://github.com/leanprover-community/mathlib/commit/9da39cf)
feat(ordered_field): missing inequality lemmas ([#4090](https://github.com/leanprover-community/mathlib/pull/4090))
From the sphere eversion project.

### [2020-09-09 22:00:53](https://github.com/leanprover-community/mathlib/commit/0967f84)
doc(*): add some docstrings ([#4073](https://github.com/leanprover-community/mathlib/pull/4073))

### [2020-09-09 16:00:30](https://github.com/leanprover-community/mathlib/commit/44d356c)
feat(tactic/explode): correctly indent long statements ([#4084](https://github.com/leanprover-community/mathlib/pull/4084))
`#explode` didn't indent long statements in the proof, such as in this lemma:
```lean
import tactic.explode
variables (p q r : ℕ → Prop)
lemma ex (h : ∃ x, ∀ y, ∃ z, p x ∧ q y ∧ r z) :
              ∃ z, ∀ y, ∃ x, p x ∧ q y ∧ r z :=
Exists.rec_on h $ λ x h',
Exists.rec_on (h' 0) $ λ z h'',
⟨z, λ y,
  Exists.rec_on (h' y) $ λ w h''',
  ⟨x, h''.1, h'''.2.1, h''.2.2⟩⟩
#explode ex
```

### [2020-09-09 16:00:28](https://github.com/leanprover-community/mathlib/commit/11e62b0)
fix(data/mv_polynomial/pderivative): rename variables and file, make it universe polymorphic ([#4083](https://github.com/leanprover-community/mathlib/pull/4083))
This file originally used different variable names to the rest of `mv_polynomial`. I've changed it to now use the same conventions as the other files.
I also renamed the file to `pderivative.lean` to be consistent with `derivative.lean` for polynomials.
The types of the coefficient ring and the indexing variables are now universe polymorphic.
The diff shows it as new files, but the only changes are fixing the statements and proofs.

### [2020-09-09 14:54:02](https://github.com/leanprover-community/mathlib/commit/98061d1)
fix(tactic/linarith): treat powers like multiplication ([#4082](https://github.com/leanprover-community/mathlib/pull/4082))
`ring` understands that natural number exponents are repeated multiplication, so it's safe for `linarith` to do the same. This is unlikely to affect anything except `nlinarith` calls, which are now slightly more powerful.

### [2020-09-09 13:02:22](https://github.com/leanprover-community/mathlib/commit/d6e7ee0)
doc(ring_theory/localization): fix docstring typo ([#4081](https://github.com/leanprover-community/mathlib/pull/4081))

### [2020-09-09 13:02:19](https://github.com/leanprover-community/mathlib/commit/297a14e)
feat(linear_algebra/affine_space): more lemmas ([#4055](https://github.com/leanprover-community/mathlib/pull/4055))
Add some more lemmas about affine spaces.  One,
`affine_span_insert_affine_span`, is extracted from the proof of
`exists_unique_dist_eq_of_affine_independent` as it turned out to be
useful elsewhere.

### [2020-09-09 13:02:17](https://github.com/leanprover-community/mathlib/commit/40de35a)
feat(order/conditionally_complete_lattice, topology/algebra/ordered): inherited order properties for `ord_connected` subset ([#3991](https://github.com/leanprover-community/mathlib/pull/3991))
If `α` is `densely_ordered`, then so is the subtype `s`, for any `ord_connected` subset `s` of `α`.
Same result for `order_topology`.
Same result for `conditionally_complete_linear_order`, under the hypothesis `inhabited s`.

### [2020-09-09 11:11:47](https://github.com/leanprover-community/mathlib/commit/2ab31f9)
chore(*): use new `extends_priority` default of 100 ([#4066](https://github.com/leanprover-community/mathlib/pull/4066))
This is the first of (most likely) two PRs which remove the use of
`set_option default_priority 100` in favor of per-instance priority
attributes, taking advantage of Lean 3.19c's new default priority
of 100 on instances produced by `extends`.

### [2020-09-09 08:45:23](https://github.com/leanprover-community/mathlib/commit/77c8415)
refactor(data/mv_polynomial): split into multiple files ([#4070](https://github.com/leanprover-community/mathlib/pull/4070))
`mv_polynomial.lean` was getting massive and hard to explore. This breaks it into (somewhat arbitrary) pieces. While `basic.lean` is still fairly long, there are a lot of basics about multivariate polynomials, and I think it's reasonable.

### [2020-09-09 04:32:30](https://github.com/leanprover-community/mathlib/commit/d5580f4)
feat(data/equiv/basic): add ext_iff for perm ([#4067](https://github.com/leanprover-community/mathlib/pull/4067))

### [2020-09-08 21:33:25](https://github.com/leanprover-community/mathlib/commit/f5ee84c)
feat(analysis/special_functions/pow): Added lemmas bounding rpow in ennreal ([#4039](https://github.com/leanprover-community/mathlib/pull/4039))
Continuation of [#3715](https://github.com/leanprover-community/mathlib/pull/3715). Added lemmas in `ennreal` corresponding to the `real` and `nnreal` lemmas added in that PR

### [2020-09-08 20:35:35](https://github.com/leanprover-community/mathlib/commit/7354042)
fix(topology/metric_space): free universe ([#4072](https://github.com/leanprover-community/mathlib/pull/4072))
Removes an unneeded and painful universe restriction

### [2020-09-08 18:11:23](https://github.com/leanprover-community/mathlib/commit/dde8bad)
doc(*): add docstrings ([#4071](https://github.com/leanprover-community/mathlib/pull/4071))
Minor docstring fixes

### [2020-09-08 12:40:23](https://github.com/leanprover-community/mathlib/commit/b2ec2b0)
chore(data/padics): fix bad markdown in doc string ([#4068](https://github.com/leanprover-community/mathlib/pull/4068))
Just noticed this in the docs

### [2020-09-08 12:40:21](https://github.com/leanprover-community/mathlib/commit/4f1399d)
feat(geometry/euclidean/basic): reflection lemmas ([#4056](https://github.com/leanprover-community/mathlib/pull/4056))
Add more lemmas about reflections of points in subspaces.

### [2020-09-08 12:40:19](https://github.com/leanprover-community/mathlib/commit/445e883)
feat(function): has_uncurry ([#3694](https://github.com/leanprover-community/mathlib/pull/3694))
By Gabriel Ebner, from the sphere eversion project. See discussion at 
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/recursive.20uncurry

### [2020-09-08 10:47:42](https://github.com/leanprover-community/mathlib/commit/1c53f91)
doc(tactic/lean_core_docs): congr understands subsingletons ([#4060](https://github.com/leanprover-community/mathlib/pull/4060))

### [2020-09-08 00:47:47](https://github.com/leanprover-community/mathlib/commit/a16112d)
doc(algebra/group/to_additive): order of to_additive relative to other attributes ([#4065](https://github.com/leanprover-community/mathlib/pull/4065))

### [2020-09-07 19:41:48](https://github.com/leanprover-community/mathlib/commit/c7d6a8e)
feat(ring_theory/unique_factorization_domain): descending chain condition for divisibility ([#4031](https://github.com/leanprover-community/mathlib/pull/4031))
Defines the strict divisibility relation `dvd_not_unit`
Defines class `wf_dvd_monoid`, indicating that `dvd_not_unit` is well-founded
Provides instances of `wf_dvd_monoid`
Prepares to refactor `unique_factorization_domain` as a predicate extending `wf_dvd_monoid`

### [2020-09-07 17:54:54](https://github.com/leanprover-community/mathlib/commit/851e83e)
feat(category_theory): colimits for pi categories ([#4054](https://github.com/leanprover-community/mathlib/pull/4054))

### [2020-09-07 13:36:36](https://github.com/leanprover-community/mathlib/commit/c259305)
feat(topology/algebra/floor_ring): add basic topological facts about `floor`, `ceil` and `fract` ([#4042](https://github.com/leanprover-community/mathlib/pull/4042))
From the sphere eversion project

### [2020-09-07 07:49:55](https://github.com/leanprover-community/mathlib/commit/f253fa0)
feat(logic/basic): apply_dite2, apply_ite2 ([#4050](https://github.com/leanprover-community/mathlib/pull/4050))
Add variants of `apply_dite` and `apply_ite` for two-argument
functions (in the case where I wanted `apply_ite`, the function was
addition).  I don't think there is any need for corresponding versions
of `dite_apply` or `ite_apply`, as two-argument versions of those
would be exactly the same as applying the one-argument version twice,
whereas that's not the case with `apply_dite2` and `apply_ite2`.

### [2020-09-07 05:46:33](https://github.com/leanprover-community/mathlib/commit/94b96cf)
feat(algebraic_geometry/structure_sheaf): stalk_iso ([#4047](https://github.com/leanprover-community/mathlib/pull/4047))
Given a ring `R` and a prime ideal `p`, construct an isomorphism of rings between the stalk of the structure sheaf of `R` at `p` and the localization of `R` at `p`.

### [2020-09-07 00:51:55](https://github.com/leanprover-community/mathlib/commit/2e198b4)
chore(scripts): update nolints.txt ([#4058](https://github.com/leanprover-community/mathlib/pull/4058))
I am happy to remove some nolints for you!

### [2020-09-06 23:47:49](https://github.com/leanprover-community/mathlib/commit/4662b20)
feat(category_theory): definition of `diag` in `binary_products` ([#4051](https://github.com/leanprover-community/mathlib/pull/4051))

### [2020-09-06 23:08:44](https://github.com/leanprover-community/mathlib/commit/4945c77)
cleanup(ring_theory/ring_invo): update old module doc, add ring_invo.involution with cleaner statement ([#4052](https://github.com/leanprover-community/mathlib/pull/4052))

### [2020-09-06 12:14:42](https://github.com/leanprover-community/mathlib/commit/de03e19)
feat(analysis/normed_space/real_inner_product): linear independence of orthogonal vectors ([#4045](https://github.com/leanprover-community/mathlib/pull/4045))
Add the lemma that an indexed family of nonzero, pairwise orthogonal
vectors is linearly independent.

### [2020-09-06 12:14:40](https://github.com/leanprover-community/mathlib/commit/1117ae7)
feat(linear_algebra): Add lemmas about powers of endomorphisms ([#4036](https://github.com/leanprover-community/mathlib/pull/4036))
Add lemmas about powers of endomorphisms and the corollary that every generalized eigenvector is a generalized eigenvector for exponent `findim K V`.

### [2020-09-06 11:28:33](https://github.com/leanprover-community/mathlib/commit/fabf34f)
feat(analysis/special_functions/trigonometric): Added lemmas for deriv of tan ([#3746](https://github.com/leanprover-community/mathlib/pull/3746))
I added lemmas for the derivative of the tangent function in both the complex and real namespaces. I also corrected two typos in comment lines.
<!-- put comments you want to keep out of the PR commit here -->

### [2020-09-06 06:48:30](https://github.com/leanprover-community/mathlib/commit/6296386)
feat(data/mv_polynomial): fill in API for vars ([#4018](https://github.com/leanprover-community/mathlib/pull/4018))
`mv_polynomial.vars` was missing a lot of API. This doesn't cover everything, but it fleshes out the theory quite a bit. There's probably more coming eventually -- this is what we have now.
Co-authored by: Johan Commelin <johan@commelin.net>

### [2020-09-06 05:07:42](https://github.com/leanprover-community/mathlib/commit/7b3c653)
chore(data/finset/lattice): remove unneeded assumptions ([#4020](https://github.com/leanprover-community/mathlib/pull/4020))

### [2020-09-05 13:51:33](https://github.com/leanprover-community/mathlib/commit/815a2f9)
feat(computability/encoding): define encoding of basic data types ([#3976](https://github.com/leanprover-community/mathlib/pull/3976))
We define the encoding of natural numbers and booleans to strings for Turing machines to be used in our future PR on polynomial time computation on Turing machines.

### [2020-09-05 09:19:56](https://github.com/leanprover-community/mathlib/commit/364d5d4)
feat(linear_algebra/char_poly): rephrase Cayley-Hamilton with `aeval', define `matrix.min_poly` ([#4040](https://github.com/leanprover-community/mathlib/pull/4040))
Rephrases the Cayley-Hamilton theorem to use `aeval`, renames it `aeval_self_char_poly`
Defines `matrix.min_poly`, the minimal polynomial of a matrix, which divides `char_poly`

### [2020-09-05 00:55:56](https://github.com/leanprover-community/mathlib/commit/ccd502a)
chore(scripts): update nolints.txt ([#4044](https://github.com/leanprover-community/mathlib/pull/4044))
I am happy to remove some nolints for you!

### [2020-09-04 11:49:24](https://github.com/leanprover-community/mathlib/commit/7c9a86d)
refactor(geometry/manifold): use a sigma type for the total space of the tangent bundle ([#3966](https://github.com/leanprover-community/mathlib/pull/3966))
Redefine the total space of the tangent bundle to be a sigma type instead of a product type. Before
```
have p : tangent_bundle I M := sorry,
rcases p with ⟨x, v⟩,
-- x: M
-- v: E
```
After
```
have p : tangent_bundle I M := sorry,
rcases p with ⟨x, v⟩,
-- x: M
-- v: tangent_space I x
```
This seems more natural, and is probably needed to do Riemannian manifolds right. The drawback is that we can not abuse identifications any more between the tangent bundle to a vector space and a product space (but we can still identify the tangent space with the vector space itself, which is the most important thing).

### [2020-09-04 00:52:11](https://github.com/leanprover-community/mathlib/commit/ecf18c6)
refactor(field_theory/minimal_polynomial, *): make `aeval`, `is_integral`, and `minimal_polynomial` noncommutative ([#4001](https://github.com/leanprover-community/mathlib/pull/4001))
Makes `aeval`, `is_integral`, and `minimal_polynomial` compatible with noncommutative algebras
Renames `eval₂_ring_hom_noncomm` to `eval₂_ring_hom'`

### [2020-09-03 21:00:06](https://github.com/leanprover-community/mathlib/commit/e3057ba)
doc(slim_check): add suggestion ([#4024](https://github.com/leanprover-community/mathlib/pull/4024))

### [2020-09-03 19:18:55](https://github.com/leanprover-community/mathlib/commit/a056ccb)
feat(slim_check): subtype instances for `le` `lt` and `list.perm` ([#4027](https://github.com/leanprover-community/mathlib/pull/4027))

### [2020-09-03 17:36:08](https://github.com/leanprover-community/mathlib/commit/2d40d9c)
feat(data/padics): universal property of Z_p ([#3950](https://github.com/leanprover-community/mathlib/pull/3950))
We establish the universal property of $\mathbb{Z}_p$ as a projective limit. Given a family of compatible ring homs $f_k : R \to \mathbb{Z}/p^n\mathbb{Z}$, there is a unique limit $R \to \mathbb{Z}_p$.
In addition, we:
* split `padic_integers.lean` into two files, creating `ring_homs.lean`
* renamings: `padic_norm_z.*` -> `padic_int.norm_*`

### [2020-09-03 16:43:52](https://github.com/leanprover-community/mathlib/commit/49173c0)
ci(scripts/detect_errors.py): enforce silent builds ([#4025](https://github.com/leanprover-community/mathlib/pull/4025))
Refactor of [#3989](https://github.com/leanprover-community/mathlib/pull/3989). 
This changes the GitHub Actions workflow so that the main build step and the test step run `lean` with `--json`. The JSON output is piped to `detect_errors.py` which now exits at the end of the build if there is any output and also writes a file `src/.noisy_files` with the names of the noisy Lean files. This file is now included in the olean caches uploaded to Azure.
The "try to find olean cache" step now uses `src/.noisy_files` to delete all of the `.olean` files corresponding to the noisy Lean files, thus making the results of CI idempotent (hopefully).

### [2020-09-03 14:47:30](https://github.com/leanprover-community/mathlib/commit/8b277a9)
feat(category_theory/filtered): finite diagrams in filtered categories admit cocones ([#4026](https://github.com/leanprover-community/mathlib/pull/4026))
This is only step towards eventual results about filtered colimits commuting with finite limits, `forget CommRing` preserving filtered colimits, and applications to `Scheme`.

### [2020-09-03 11:22:52](https://github.com/leanprover-community/mathlib/commit/fa6485a)
feat(category_theory/limits/concrete): simp lemmas ([#3973](https://github.com/leanprover-community/mathlib/pull/3973))
Some specialisations of simp lemmas about (co)limits for concrete categories, where the equation in morphisms has been applied to an element.
This isn't exhaustive; just the things I've wanted recently.

### [2020-09-03 04:04:29](https://github.com/leanprover-community/mathlib/commit/dd633c2)
feat(geometry/euclidean/circumcenter): more lemmas ([#4028](https://github.com/leanprover-community/mathlib/pull/4028))
Add some more basic lemmas about `circumcenter` and `circumradius`.

### [2020-09-03 01:52:48](https://github.com/leanprover-community/mathlib/commit/c86359f)
chore(scripts): update nolints.txt ([#4030](https://github.com/leanprover-community/mathlib/pull/4030))
I am happy to remove some nolints for you!

### [2020-09-03 01:52:46](https://github.com/leanprover-community/mathlib/commit/ca5703d)
fix(docs/100.yaml): fix indentation in 100 list ([#4029](https://github.com/leanprover-community/mathlib/pull/4029))

### [2020-09-03 00:15:49](https://github.com/leanprover-community/mathlib/commit/7b9db99)
fix(test/*): make sure tests produce no output ([#3947](https://github.com/leanprover-community/mathlib/pull/3947))
Modify tests so that they produce no output. This also means removing all uses of `sorry`/`admit`.
Replace `#eval` by `run_cmd` consistently.
Tests that produced output before are modified so that it is checked that they roughly produce the right output
Add a trace option to the `#simp` command that turns the message of only if the expression is simplified to `true`. All tests are modified so that they simplify to `true`.
The randomized tests can produce output when they find a false positive, but that should basically never happen.
Add some docstings to `src/tactic/interactive`.

### [2020-09-02 19:38:06](https://github.com/leanprover-community/mathlib/commit/9d42f6c)
feat(order/rel_iso): define `rel_hom` (relation-preserving maps) ([#3946](https://github.com/leanprover-community/mathlib/pull/3946))
Creates a typeclass for (unidirectionally) relation-preserving maps that are not necessarily injective
(In the case of <= relations, this is essentially a bundled monotone map)
Proves that these transfer well-foundedness between relations

### [2020-09-02 15:51:17](https://github.com/leanprover-community/mathlib/commit/57463fa)
feat(linear_algebra/affine_space): more lemmas ([#3990](https://github.com/leanprover-community/mathlib/pull/3990))
Add another batch of lemmas about affine spaces.  These lemmas mostly
relate to manipulating centroids and the relations between centroids
of points given by different subsets of the index type.

### [2020-09-02 15:11:55](https://github.com/leanprover-community/mathlib/commit/71ef45e)
chore(topology/sheaves): depend less on rfl ([#3994](https://github.com/leanprover-community/mathlib/pull/3994))
Another backport from the `prop_limits` branch.

### [2020-09-02 13:19:05](https://github.com/leanprover-community/mathlib/commit/895f6ee)
chore(algebra/category/CommRing/limits): don't use deprecated.subring ([#4010](https://github.com/leanprover-community/mathlib/pull/4010))

### [2020-09-02 13:19:01](https://github.com/leanprover-community/mathlib/commit/ddbdfeb)
chore(data/fin): succ_above defn compares fin terms instead of values ([#3999](https://github.com/leanprover-community/mathlib/pull/3999))
`fin.succ_above` is redefined to use a comparison between two `fin (n + 1)` instead of their coerced values in `nat`. This should delay any "escape" from `fin` into `nat` until necessary. Lemmas are added regarding `fin.succ_above`. Some proofs for existing lemmas reworked for new definition and simplified. Additionally, docstrings are added for related lemmas.
New lemmas:
Comparison after embedding:
`succ_above_lt_ge`
`succ_above_lt_gt`
Injectivity lemmas:
`succ_above_right_inj`
`succ_above_right_injective`
`succ_above_left_inj`
`succ_above_left_injective`
finset lemma:
`fin.univ_succ_above`
prod and sum lemmas:
`fin.prod_univ_succ_above`

### [2020-09-02 13:18:59](https://github.com/leanprover-community/mathlib/commit/96c80e2)
feat(ring_theory/localization): Localizations of integral extensions ([#3942](https://github.com/leanprover-community/mathlib/pull/3942))
The main definition is the algebra induced by localization at an algebra. Given an algebra `R → S` and a submonoid `M` of `R`, as well as localization maps `f : R → Rₘ` and `g : S → Sₘ`, there is a natural algebra `Rₘ → Sₘ` that makes the entire square commute, and this is defined as `localization_algebra`. 
The two main theorems are similar but distinct statements about integral elements and localizations:
* `is_integral_localization_at_leading_coeff` says that if an element `x` is algebraic over `algebra R S`, then if we localize to a submonoid containing the leading coefficient the image of `x` will be integral.
* `is_integral_localization` says that if `R → S` is an integral extension, then the algebra induced by localizing at any particular submonoid will be an integral extension.

### [2020-09-02 11:43:54](https://github.com/leanprover-community/mathlib/commit/cd36773)
feat(linear_algebra/eigenspace): add generalized eigenspaces ([#4015](https://github.com/leanprover-community/mathlib/pull/4015))
Add the definition of generalized eigenspaces, eigenvectors and eigenvalues. Add some basic lemmas about them.
Another step towards [#3864](https://github.com/leanprover-community/mathlib/pull/3864).

### [2020-09-02 08:30:45](https://github.com/leanprover-community/mathlib/commit/7310eab)
feat(field_theory/adjoin): adjoining elements to fields ([#3913](https://github.com/leanprover-community/mathlib/pull/3913))
Defines adjoining elements to fields

### [2020-09-02 06:01:22](https://github.com/leanprover-community/mathlib/commit/8026ea8)
feat(ring_theory/localization): localization away from an element ([#4019](https://github.com/leanprover-community/mathlib/pull/4019))

### [2020-09-02 00:37:30](https://github.com/leanprover-community/mathlib/commit/0b4444c)
feat(pfun/recursion): unbounded recursion ([#3778](https://github.com/leanprover-community/mathlib/pull/3778))

### [2020-09-01 23:53:35](https://github.com/leanprover-community/mathlib/commit/d94643c)
doc(slim_check): improve documentation, swap instances ([#4023](https://github.com/leanprover-community/mathlib/pull/4023))

### [2020-09-01 23:53:33](https://github.com/leanprover-community/mathlib/commit/ef22a33)
feat(slim_check/errors): improve error messages and add useful instances ([#4022](https://github.com/leanprover-community/mathlib/pull/4022))

### [2020-09-01 18:54:03](https://github.com/leanprover-community/mathlib/commit/0c2e77c)
feat(testing): property based testing (basics) ([#3915](https://github.com/leanprover-community/mathlib/pull/3915))
Add `gen` monad, `sampleable` and `testable` type classes

### [2020-09-01 12:58:32](https://github.com/leanprover-community/mathlib/commit/329393a)
feat(analysis/calculus/times_cont_diff): iterated smoothness in terms of deriv ([#4017](https://github.com/leanprover-community/mathlib/pull/4017))
Currently, iterated smoothness is only formulated in terms of the Fréchet derivative. For one-dimensional functions, it is more handy to use the one-dimensional derivative `deriv`. This PR provides a basic interface in this direction.

### [2020-09-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/849a5f9)
feat(docs,ci): move overview, undergrad, and 100 theorems lists from website ([#4016](https://github.com/leanprover-community/mathlib/pull/4016))
See conversation at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/website.20overview/near/208659351
We'll store these lists in mathlib so that we can catch breakage as soon as it happens, rather than continually repairing the website build. This PR adds the lists and a CI step that checks that every declaration name appearing in the lists actually exists in the library.

### [2020-09-01 12:18:06](https://github.com/leanprover-community/mathlib/commit/6a5241f)
refactor(algebra/category/*, category_theory/concrete_category): generalize universes for concrete categories ([#3687](https://github.com/leanprover-community/mathlib/pull/3687))
Currently, concrete categories need to be `large_category`s. In particular, if objects live in `Type u`, then morphisms live in `Type (u + 1)`. For the category of modules over some ring R, this is not necessarily true, because we have to take the universe of R into account. One way to deal with this problem is to just force the universe of the ring to be the same as the universe of the module. This [sounds like it shouldn't be much of an issue](https://github.com/leanprover-community/mathlib/pull/1420#discussion_r322607455), but unfortunately, [it is](https://github.com/leanprover-community/mathlib/pull/3621#issue-458293664).
This PR
* removes the constraint that a concrete category must be a `large_category`,
* generalizes `Module R` and `Algebra R` to accept a universe parameter for the module/algebra and
* adds a ton of universe annotations which become neccesary because of the change
As a reward, we get `abelian AddCommGroup.{u}` for arbitrary `u` without any (additional) work.

### [2020-09-01 09:54:45](https://github.com/leanprover-community/mathlib/commit/a97d71b)
feat(data/mv_polynomial): assorted lemmas ([#4002](https://github.com/leanprover-community/mathlib/pull/4002))
Assorted additions to `mv_polynomial`. This is more from the Witt vector development. Nothing too deep here, just scattered lemmas and the `constant_coeff` ring hom.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->
Hopefully this builds -- it's split off from a branch with a lot of other changes. I think it shouldn't have dependencies!

### [2020-09-01 06:48:21](https://github.com/leanprover-community/mathlib/commit/2688d42)
feat(archive/100-theorems-list): friendship theorem (nr 83) ([#3970](https://github.com/leanprover-community/mathlib/pull/3970))
defines friendship graphs
proves the friendship theorem (freek [#83](https://github.com/leanprover-community/mathlib/pull/83))

### [2020-09-01 04:51:03](https://github.com/leanprover-community/mathlib/commit/12763ec)
chore(*): more use of bundled ring homs ([#4012](https://github.com/leanprover-community/mathlib/pull/4012))

### [2020-09-01 04:51:01](https://github.com/leanprover-community/mathlib/commit/51546d2)
chore(ring_theory/free_ring): use bundled ring homs ([#4011](https://github.com/leanprover-community/mathlib/pull/4011))
Use bundled ring homs in `free_ring` and `free_comm_ring`.

### [2020-09-01 04:50:59](https://github.com/leanprover-community/mathlib/commit/93468fe)
chore(algebraic_geometry/Spec): reduce imports ([#4007](https://github.com/leanprover-community/mathlib/pull/4007))
The main change is to remove some `example`s from `topology.category.TopCommRing`, so that we don't need to know about the real and complex numbers on the way to defining a `Scheme`.
While I was staring at `leanproject import-graph --to algebraic_geometry.Scheme`, I also removed a bunch of redundant or unused imports elsewhere.

### [2020-09-01 04:50:57](https://github.com/leanprover-community/mathlib/commit/551cf8e)
refactor(algebra/associates): unite `associates.prime` with `prime` ([#3988](https://github.com/leanprover-community/mathlib/pull/3988))
deletes `associates.prime`, replaces it with the existing `prime`

### [2020-09-01 04:50:54](https://github.com/leanprover-community/mathlib/commit/7cd67b5)
feat(category_theory/limits/shapes/terminal): is_terminal object ([#3957](https://github.com/leanprover-community/mathlib/pull/3957))
Add language to talk about when an object is terminal, and generalise some results to use this

### [2020-09-01 03:18:29](https://github.com/leanprover-community/mathlib/commit/fc57cf4)
feat(data/{finset,finsupp,multiset}): more assorted lemmas ([#4006](https://github.com/leanprover-community/mathlib/pull/4006))
Another grab bag of facts from the Witt vector branch.
Coauthored by: Johan Commelin <johan@commelin.net>
<!-- put comments you want to keep out of the PR commit here -->

### [2020-09-01 01:12:55](https://github.com/leanprover-community/mathlib/commit/c33b41b)
chore(scripts): update nolints.txt ([#4009](https://github.com/leanprover-community/mathlib/pull/4009))
I am happy to remove some nolints for you!

### [2020-09-01 00:04:06](https://github.com/leanprover-community/mathlib/commit/e053bda)
feat(category_theory/monoidal/internal): Mon_ (Module R) ≌ Algebra R ([#3695](https://github.com/leanprover-community/mathlib/pull/3695))
The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
Moreover, this equivalence is compatible with the forgetful functors to `Module R`.