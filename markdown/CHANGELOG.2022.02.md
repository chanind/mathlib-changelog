### [2022-02-28 16:08:55](https://github.com/leanprover-community/mathlib/commit/456898c)
feat(data/finsupp/basic): Version of `finsupp.prod_add_index` with weaker premises ([#11353](https://github.com/leanprover-community/mathlib/pull/11353))
A simpler proof of `finsupp.prod_add_index : (f + g).prod h = f.prod h * g.prod h` with weaker premises.
Specifically, this only requires:
* `[add_zero_class M]` rather than `[add_comm_monoid M]`
* `h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1` rather than `h_zero : ∀a, h a 0 = 1`.  
* `h_add : ∀ (a ∈ f.support ∪ g.support) b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂` rather than `h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂` (thanks to Anne Baanen for spotting this weakening).
The original version has been retained and re-named to `finsupp.prod_add_index'`, since in some places this is more convenient to use.  (There was already a lemma called `prod_add_index'` which appears not to have been used anywhere.  This has been renamed to `prod_hom_add_index`.)
Discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Variant.20of.20finsupp.2Eprod_add_index.3F

### [2022-02-28 12:46:18](https://github.com/leanprover-community/mathlib/commit/1447c40)
refactor(group_theory/general_commutator): Rename `general_commutator` to `subgroup.commutator` ([#12308](https://github.com/leanprover-community/mathlib/pull/12308))
This PR renames `general_commutator` to `subgroup.commutator`.
I'll change the file name in a followup PR, so that this PR is easier to review.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)

### [2022-02-28 12:46:17](https://github.com/leanprover-community/mathlib/commit/92cbcc3)
chore(algebra): move star_ring structure on free_algebra ([#12297](https://github.com/leanprover-community/mathlib/pull/12297))
There's no need to have `algebra.star.basic` imported transitively into pretty much everything, just to put the `star_ring` structure on `free_algebra`, so I've moved this construction to its own file.
(I was changing definitions in `algebra.star.basic` to allow for more non-unital structures, it recompiling was very painful because of this transitive dependence.)

### [2022-02-28 12:46:16](https://github.com/leanprover-community/mathlib/commit/9c71c0f)
feat(algebra/monoid_algebra/basic): add monomial_hom ([#12283](https://github.com/leanprover-community/mathlib/pull/12283))
Just adding one definition

### [2022-02-28 12:46:15](https://github.com/leanprover-community/mathlib/commit/c7498d0)
feat(algebra/{group/with_one,order/monoid}): equivs for `with_zero` and `with_one` ([#12275](https://github.com/leanprover-community/mathlib/pull/12275))
This provides:
* `add_equiv.with_zero_congr : α ≃+ β → with_zero α ≃+ with_zero β`
* `mul_equiv.with_one_congr : α ≃* β → with_one α ≃* with_one β`
* `with_zero.to_mul_bot : with_zero (multiplicative α) ≃* multiplicative (with_bot α)`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/with_zero.20.28multiplicative.20A.29.20.E2.89.83*.20multiplicative.20.28with_bot.20A.29/near/272980650)

### [2022-02-28 12:46:14](https://github.com/leanprover-community/mathlib/commit/474aecb)
doc(algebra,data/fun_like): small morphism documentation improvements ([#11642](https://github.com/leanprover-community/mathlib/pull/11642))
 * The `fun_like` docs talked about a `to_fun` class, this doesn't exist (anymore).
 * Warn that `{one,mul,monoid,monoid_with_zero}_hom.{congr_fun,congr_arg,coe_inj,ext_iff}` has been superseded by `fun_like`.
Thanks to @YaelDillies for pointing out these issues.

### [2022-02-28 12:16:38](https://github.com/leanprover-community/mathlib/commit/33c0a1c)
feat(ring_theory/dedekind_domain/ideal): add height_one_spectrum ([#12244](https://github.com/leanprover-community/mathlib/pull/12244))

### [2022-02-28 10:33:37](https://github.com/leanprover-community/mathlib/commit/200c254)
feat(algebra/algebra,data/equiv/ring): `{ring,alg}_equiv.Pi_congr_right` ([#12289](https://github.com/leanprover-community/mathlib/pull/12289))
We extend `{add,mul}_equiv.Pi_congr_right` to rings and algebras.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60ring_equiv.2EPi_congr_right.60

### [2022-02-28 10:33:35](https://github.com/leanprover-community/mathlib/commit/e700d56)
feat(ring_theory/polynomial/eisenstein): add a technical lemma ([#11839](https://github.com/leanprover-community/mathlib/pull/11839))
A technical lemma about Eiseinstein minimal polynomials.
From flt-regular

### [2022-02-28 10:33:34](https://github.com/leanprover-community/mathlib/commit/770a7ce)
feat(measure_theory/function/convergence_in_measure): Define convergence in measure ([#11774](https://github.com/leanprover-community/mathlib/pull/11774))
This PR defines convergence in measure and proves some properties about them. 
In particular, we prove that 
- convergence a.e. in a finite measure space implies convergence in measure
- convergence in measure implies there exists a subsequence that converges a.e.
- convergence in Lp implies convergence in measure

### [2022-02-28 10:33:33](https://github.com/leanprover-community/mathlib/commit/b25bad7)
feat(archive/100-theorems-list): Partition theorem ([#4259](https://github.com/leanprover-community/mathlib/pull/4259))
A proof of Euler's partition theorem, from the Freek list.
The proof is sorry-free but currently unpleasant, and some parts don't belong in `archive/`, so WIP for now.

### [2022-02-28 09:09:20](https://github.com/leanprover-community/mathlib/commit/dc72624)
chore(measure_theory/function/strongly_measurable): remove useless no_zero_divisors assumption ([#12353](https://github.com/leanprover-community/mathlib/pull/12353))

### [2022-02-28 08:31:53](https://github.com/leanprover-community/mathlib/commit/58c20c1)
feat(measure_theory/group): add measures invariant under inversion/negation ([#11954](https://github.com/leanprover-community/mathlib/pull/11954))
* Define measures invariant under `inv` or `neg`
* Prove lemmas about measures invariant under `inv` similar to the lemmas about measures invariant under `mul`
* Also provide more `pi` instances in `arithmetic`.
* Rename some `integral_zero...` lemmas to `integral_eq_zero...`
* Reformulate `pi.is_mul_left_invariant_volume` using nondependent functions, so that type class inference can find it for `ι → ℝ`)
* Add some more integration lemmas, also for multiplication

### [2022-02-28 02:34:22](https://github.com/leanprover-community/mathlib/commit/f3a04ed)
feat(group_theory/subgroup/basic): Centralizer subgroup ([#11946](https://github.com/leanprover-community/mathlib/pull/11946))
This PR defines the centralizer subgroup, and provides a few basic lemmas.

### [2022-02-27 23:09:46](https://github.com/leanprover-community/mathlib/commit/2f86b49)
doc(data/set_like/basic): tidy up docstring ([#12337](https://github.com/leanprover-community/mathlib/pull/12337))
Hopefully this makes the docstring slightly clearer.

### [2022-02-27 23:09:45](https://github.com/leanprover-community/mathlib/commit/dfacfd3)
chore(linear_algebra/basic): make `linear_map.id_coe` elegible for `dsimp` ([#12334](https://github.com/leanprover-community/mathlib/pull/12334))
`dsimp` only considers lemmas which _are_ proved by `rfl`, not ones that just _could_ be.

### [2022-02-27 22:39:10](https://github.com/leanprover-community/mathlib/commit/f322fa0)
refactor(group_theory/solvable): Delete duplicate lemma ([#12307](https://github.com/leanprover-community/mathlib/pull/12307))
`map_commutator_eq_commutator_map` is a duplicate of `map_general_commutator`.
(This is one of the several orthogonal changes from [#12134](https://github.com/leanprover-community/mathlib/pull/12134))

### [2022-02-27 22:00:44](https://github.com/leanprover-community/mathlib/commit/7f52f94)
feat(analysis/complex): maximum modulus principle ([#12050](https://github.com/leanprover-community/mathlib/pull/12050))

### [2022-02-27 21:28:31](https://github.com/leanprover-community/mathlib/commit/b5faa34)
feat(analysis/complex/liouville): prove Liouville's theorem ([#12095](https://github.com/leanprover-community/mathlib/pull/12095))

### [2022-02-27 20:07:58](https://github.com/leanprover-community/mathlib/commit/a5ffb9b)
feat(analysis/special_functions): little o behaviour of exp/log at infinity ([#11840](https://github.com/leanprover-community/mathlib/pull/11840))
from the unit-fractions project

### [2022-02-27 16:32:35](https://github.com/leanprover-community/mathlib/commit/c4cf451)
fix(catgory_theory/limits): fix a typo ([#12341](https://github.com/leanprover-community/mathlib/pull/12341))

### [2022-02-27 16:04:10](https://github.com/leanprover-community/mathlib/commit/8ef4331)
feat(ring_theory/witt_vector): Witt vectors are a DVR ([#12213](https://github.com/leanprover-community/mathlib/pull/12213))
This PR adds two connected files. `mul_coeff.lean` adds an auxiliary result that's used in a few places in [#12041](https://github.com/leanprover-community/mathlib/pull/12041) . One of these places is in `discrete_valuation_ring.lean`, which shows that Witt vectors over a perfect field form a DVR.

### [2022-02-27 15:35:55](https://github.com/leanprover-community/mathlib/commit/1dfb38d)
doc(imo*,algebra/continued_fractions/computation): change \minus to - ([#12338](https://github.com/leanprover-community/mathlib/pull/12338))
Change around 14 instances of a non-standard minus to `-`.

### [2022-02-27 14:12:55](https://github.com/leanprover-community/mathlib/commit/00a3d02)
feat(geometry/euclidean/oriented_angle): oriented angles with respect to an orientation ([#12236](https://github.com/leanprover-community/mathlib/pull/12236))
Add definitions and lemmas for oriented angles defined to take an
orientation, instead of an orthonormal basis, as an argument.  These
are the versions intended to be used by most users when working with
oriented angles between vectors, instead of users needing to deal with
a choice of basis.
Apart from the last five lemmas that relate angles and rotations for
different orientations or relate them explicitly to the definitions
with respect to a basis, everything is deduced directly from the
corresponding lemma that takes an orthonormal basis as an argument.

### [2022-02-27 10:57:38](https://github.com/leanprover-community/mathlib/commit/77e76ee)
feat(data/list/basic): add last'_append and head'_append_of_ne_nil ([#12221](https://github.com/leanprover-community/mathlib/pull/12221))
we already have `head'_append` and `last'_append_of_ne_nil`, and users
might expect a symmetric API.

### [2022-02-27 09:13:42](https://github.com/leanprover-community/mathlib/commit/b1c2d70)
feat(logic/function/basic): not_surjective_Type ([#12311](https://github.com/leanprover-community/mathlib/pull/12311))

### [2022-02-27 08:45:41](https://github.com/leanprover-community/mathlib/commit/7ae0b36)
chore(category_theory/idempotents): minor suggestions ([#12303](https://github.com/leanprover-community/mathlib/pull/12303))
@joelriou, here are some minor suggestions on your earlier Karoubi envelope work (I wasn't around when the PR went through.)
The two separate suggestions are some typos, and dropping some unnecessary proofs.

### [2022-02-27 06:00:11](https://github.com/leanprover-community/mathlib/commit/07374a2)
feat(set_theory/cardinal): add three_le ([#12225](https://github.com/leanprover-community/mathlib/pull/12225))

### [2022-02-27 04:07:15](https://github.com/leanprover-community/mathlib/commit/86d686c)
feat(category_theory/category/Groupoid): Add coercion to sort ([#12324](https://github.com/leanprover-community/mathlib/pull/12324))
Use coercion to type instead of `.α`

### [2022-02-27 04:07:14](https://github.com/leanprover-community/mathlib/commit/907e5ba)
fix(set_theory/ordinal_arithmetic): Fix universes ([#12320](https://github.com/leanprover-community/mathlib/pull/12320))
`lsub_le_of_range_subset` and `lsub_eq_of_range_eq` should have had 3 universes, but they had only two.

### [2022-02-27 04:07:13](https://github.com/leanprover-community/mathlib/commit/906a88b)
feat(data/quot): primed quotient funcs on `mk` ([#12204](https://github.com/leanprover-community/mathlib/pull/12204))

### [2022-02-27 02:45:05](https://github.com/leanprover-community/mathlib/commit/4afb8d2)
feat(set_theory/ordinal_arithmetic): Added missing theorems for `lsub` and `blsub` ([#12318](https://github.com/leanprover-community/mathlib/pull/12318))
These are the analogs of `lt_sup` and `lt_bsup`, respectively.

### [2022-02-27 02:45:04](https://github.com/leanprover-community/mathlib/commit/bb9539c)
chore(set_theory/ordinal): Minor golf in `card` ([#12298](https://github.com/leanprover-community/mathlib/pull/12298))
This was suggested by @b-mehta.

### [2022-02-27 02:45:02](https://github.com/leanprover-community/mathlib/commit/b4f87d9)
feat(analysis/normed_space): add `normed_space 𝕜 (uniform_space.completion E)` ([#12148](https://github.com/leanprover-community/mathlib/pull/12148))

### [2022-02-27 01:14:05](https://github.com/leanprover-community/mathlib/commit/abf5dfc)
refactor(category_theory/eq_to_hom): conjugation by eq_to_hom same as heq ([#12025](https://github.com/leanprover-community/mathlib/pull/12025))
Xu Junyan provided this lemma for showing that `heq` gives the same as conjugation by `eq_to_hom` for equality of functor maps. I refactored `hext` using this result.
Then I added a bunch of lemmas for how `heq` interacts with composition of functors and `functor.map` applied to composition of morphisms

### [2022-02-27 01:14:04](https://github.com/leanprover-community/mathlib/commit/1fe9708)
feat(group_theory/nilpotent): is_nilpotent_of_product_of_sylow_group ([#11834](https://github.com/leanprover-community/mathlib/pull/11834))

### [2022-02-26 23:31:58](https://github.com/leanprover-community/mathlib/commit/add068d)
chore(linear_algebra/orientation): split into 2 files ([#12302](https://github.com/leanprover-community/mathlib/pull/12302))
Move parts that don't need multilinear maps to a new file.

### [2022-02-26 23:31:57](https://github.com/leanprover-community/mathlib/commit/188b371)
feat(algebra/category/GroupWithZero): The category of groups with zero ([#12278](https://github.com/leanprover-community/mathlib/pull/12278))
Define `GroupWithZero`, the category of groups with zero with monoid with zero homs.

### [2022-02-26 23:31:55](https://github.com/leanprover-community/mathlib/commit/163d1a6)
feat(category_theory/idempotents): idempotent completeness and functor categories ([#12270](https://github.com/leanprover-community/mathlib/pull/12270))

### [2022-02-26 23:31:53](https://github.com/leanprover-community/mathlib/commit/817b4c4)
feat(order/category/BoundedLattice): The category of bounded lattices ([#12257](https://github.com/leanprover-community/mathlib/pull/12257))
Define `BoundedLattice`, the category of bounded lattices with bounded lattice homs.

### [2022-02-26 22:03:39](https://github.com/leanprover-community/mathlib/commit/3d8c22f)
refactor(topology/compact_open): Remove `locally_compact_space` hypothesis in `continuous_map.t2_space` ([#12306](https://github.com/leanprover-community/mathlib/pull/12306))
This PR removes the `locally_compact_space` hypothesis in `continuous_map.t2_space`, at the cost of a longer proof.

### [2022-02-26 20:55:45](https://github.com/leanprover-community/mathlib/commit/4cf0e60)
feat(category_theory/limits): generalize has_biproduct.of_has_product  ([#12116](https://github.com/leanprover-community/mathlib/pull/12116))

### [2022-02-26 20:55:44](https://github.com/leanprover-community/mathlib/commit/09ba530)
feat(category_theory/limits): biproducts are unique up to iso ([#12114](https://github.com/leanprover-community/mathlib/pull/12114))

### [2022-02-26 20:23:50](https://github.com/leanprover-community/mathlib/commit/fe6ea3e)
feat(analysis/convex/integral): strict Jensen's inequality ([#11552](https://github.com/leanprover-community/mathlib/pull/11552))

### [2022-02-26 19:39:04](https://github.com/leanprover-community/mathlib/commit/c8150cc)
feat(analysis/normed_space/add_torsor): `dist` and `line_map` ([#12265](https://github.com/leanprover-community/mathlib/pull/12265))
Add a few lemmas about the distance between `line_map p₁ p₂ c₁` and
`line_map p₁ p₂ c₂`.

### [2022-02-26 16:53:59](https://github.com/leanprover-community/mathlib/commit/3b49fe2)
feat(algebra/star/pointwise, algebra/star/basic): add pointwise star, and a few convenience lemmas ([#12290](https://github.com/leanprover-community/mathlib/pull/12290))
This adds a star operation to sets in the pointwise locale and establishes the basic properties. The names and proofs were taken from the corresponding ones for `inv`. A few extras were added.

### [2022-02-26 16:18:11](https://github.com/leanprover-community/mathlib/commit/87fc3ea)
feat(analysis/normed_space/star/spectrum): prove the spectrum of a unitary element in a C*-algebra is a subset of the unit sphere ([#12238](https://github.com/leanprover-community/mathlib/pull/12238))
The spectrum of a unitary element in a C*-algebra is a subset of the unit sphere in the scalar field. This will be used to show that the spectrum of selfadjoint elements is real-valued.

### [2022-02-26 13:23:26](https://github.com/leanprover-community/mathlib/commit/0f1bc2c)
feat(topology,analysis): any function is continuous/differentiable on a subsingleton ([#12293](https://github.com/leanprover-community/mathlib/pull/12293))
Also add supporting lemmas about `is_o`/`is_O` and the `pure` filter
and drop an unneeded assumption in `asymptotics.is_o_const_const_iff`.

### [2022-02-26 11:40:32](https://github.com/leanprover-community/mathlib/commit/bfc0584)
refactor(topology,analysis): use `maps_to` in lemmas like `continuous_on.comp` ([#12294](https://github.com/leanprover-community/mathlib/pull/12294))

### [2022-02-26 11:03:49](https://github.com/leanprover-community/mathlib/commit/d2d6f17)
feat(analysis/inner_product_space/spectrum): `has_eigenvalue_eigenvalues` ([#12304](https://github.com/leanprover-community/mathlib/pull/12304))
similar to the existing `has_eigenvector_eigenvector_basis`

### [2022-02-26 03:29:04](https://github.com/leanprover-community/mathlib/commit/d6a8e5d)
feat(topology/compact_open): `simp`-lemmas for `compact_open.gen` ([#12267](https://github.com/leanprover-community/mathlib/pull/12267))
This PR adds some basic `simp`-lemmas for `compact_open.gen`.

### [2022-02-26 03:29:03](https://github.com/leanprover-community/mathlib/commit/7201c3b)
feat(category_theory/limits): more opposite-related transformations of cones ([#12165](https://github.com/leanprover-community/mathlib/pull/12165))

### [2022-02-26 02:44:14](https://github.com/leanprover-community/mathlib/commit/43fb516)
doc(analysis/normed_space): fixed normed_star_monoid doc-string ([#12296](https://github.com/leanprover-community/mathlib/pull/12296))

### [2022-02-25 22:23:16](https://github.com/leanprover-community/mathlib/commit/05d8188)
feat(group_theory/torsion): define torsion groups ([#11850](https://github.com/leanprover-community/mathlib/pull/11850))
I grepped for torsion group and didn't find anything -- hopefully adding this makes sense here.

### [2022-02-25 20:13:56](https://github.com/leanprover-community/mathlib/commit/3cc9ac4)
feat(analysis/normed_space/finite_dimension): add a lemma about `inf_dist` ([#12282](https://github.com/leanprover-community/mathlib/pull/12282))
Add a version of `exists_mem_frontier_inf_dist_compl_eq_dist` for a
compact set in a real normed space. This version does not assume that
the ambient space is finite dimensional.

### [2022-02-25 18:50:04](https://github.com/leanprover-community/mathlib/commit/c127fc3)
chore(measure_theory/decomposition/lebesgue): tidy a proof ([#12274](https://github.com/leanprover-community/mathlib/pull/12274))
There's no need to go through `set_integral_re_add_im` when all we need is `integral_re`.

### [2022-02-25 16:56:48](https://github.com/leanprover-community/mathlib/commit/6653544)
feat(topology/algebra/order/extr): extr on closure ([#12281](https://github.com/leanprover-community/mathlib/pull/12281))
Prove `is_max_on.closure` etc

### [2022-02-25 10:18:16](https://github.com/leanprover-community/mathlib/commit/8c485a4)
feat(order/filter/extr): add `is_*_on.comp_maps_to` ([#12280](https://github.com/leanprover-community/mathlib/pull/12280))

### [2022-02-25 07:39:47](https://github.com/leanprover-community/mathlib/commit/c1443d6)
feat(ring_theory/localization): random lemmata for edge cases ([#12146](https://github.com/leanprover-community/mathlib/pull/12146))

### [2022-02-25 07:07:50](https://github.com/leanprover-community/mathlib/commit/dae1dfe)
feat(topology/spectral/hom): Spectral maps ([#12228](https://github.com/leanprover-community/mathlib/pull/12228))
Define spectral maps in three ways:
* `is_spectral_map`, the unbundled predicate
* `spectral_map`, the bundled type
* `spectral_map_class`, the hom class
The design for `is_spectral_map` matches `continuous`. The design for `spectral_map` and `spectral_map_class` follows the hom refactor.

### [2022-02-25 05:25:18](https://github.com/leanprover-community/mathlib/commit/f2fdef6)
feat(order/partition/equipartition): Equipartitions ([#12023](https://github.com/leanprover-community/mathlib/pull/12023))
Define `finpartition.is_equipartition`, a predicate for saying that the parts of a `finpartition` of a `finset` are all the same size up to a difference of `1`.

### [2022-02-25 03:05:10](https://github.com/leanprover-community/mathlib/commit/605ea9f)
feat(algebra/symmetrized): Define the symmetrization of a ring ([#11399](https://github.com/leanprover-community/mathlib/pull/11399))
A commutative multiplication on a real or complex space can be constructed from any multiplication by
"symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
The approach taken here is inspired by `algebra.opposites`.
Previously submitted as part of [#11073](https://github.com/leanprover-community/mathlib/pull/11073).
Will be used in https://github.com/leanprover-community/mathlib/pull/11401

### [2022-02-24 20:01:42](https://github.com/leanprover-community/mathlib/commit/f7518db)
chore(topology/continuous_function/bounded): add an is_central_scalar instance ([#12272](https://github.com/leanprover-community/mathlib/pull/12272))
This is only possible very recently now that `𝕜ᵐᵒᵖ` has a metric space instance.

### [2022-02-24 20:01:41](https://github.com/leanprover-community/mathlib/commit/feb5473)
chore(*): update to 3.40.0c ([#12212](https://github.com/leanprover-community/mathlib/pull/12212))

### [2022-02-24 18:24:37](https://github.com/leanprover-community/mathlib/commit/d3d3701)
feat(analysis/mean_inequalities): AM and GM are equal on a constant tuple ([#12179](https://github.com/leanprover-community/mathlib/pull/12179))
The converse is also true, but I have not gotten around to proving it.

### [2022-02-24 16:20:33](https://github.com/leanprover-community/mathlib/commit/d620395)
feat(topology/algebra/group): homeomorphisms for div ([#12251](https://github.com/leanprover-community/mathlib/pull/12251))

### [2022-02-24 16:20:32](https://github.com/leanprover-community/mathlib/commit/ed9f73c)
feat(order/conditionally_complete_lattice.lean): two new lemmas ([#12250](https://github.com/leanprover-community/mathlib/pull/12250))

### [2022-02-24 14:39:01](https://github.com/leanprover-community/mathlib/commit/0840629)
test(instance_diamonds): verify that restrict_scalars produces no diamonds on the complex numbers ([#12273](https://github.com/leanprover-community/mathlib/pull/12273))
There is already a comment on `complex.module` that indicates an intentional solution to this diamond.

### [2022-02-24 14:38:59](https://github.com/leanprover-community/mathlib/commit/a0d2c43)
feat(algebra/punit_instances): mul_semiring_action ([#12271](https://github.com/leanprover-community/mathlib/pull/12271))
The timeouts mentioned in the file appear to no longer occur.

### [2022-02-24 14:38:57](https://github.com/leanprover-community/mathlib/commit/9dca6f4)
feat(topology/metric_space/lipschitz): add `set.maps_to` lemmas ([#12266](https://github.com/leanprover-community/mathlib/pull/12266))

### [2022-02-24 14:38:55](https://github.com/leanprover-community/mathlib/commit/d011bf2)
chore(measure_theory/function/uniform_integrable): replace `ℕ` by a type verifying enough assumptions ([#12242](https://github.com/leanprover-community/mathlib/pull/12242))
This PR does not generalize the results of the `uniform_integrable` file much, but using a generic type instead of `ℕ` makes clear where we need assumptions like `encodable`.

### [2022-02-24 14:38:54](https://github.com/leanprover-community/mathlib/commit/34cfcd0)
feat(probability/stopping): generalize `is_stopping_time.measurable_set_lt` and variants beyond `ℕ` ([#12240](https://github.com/leanprover-community/mathlib/pull/12240))
The lemma `is_stopping_time.measurable_set_lt` and the similar results for gt, ge and eq were written for stopping times with value in nat. We generalize those results to linear orders with the order topology.

### [2022-02-24 12:56:59](https://github.com/leanprover-community/mathlib/commit/79887c9)
feat(measure_theory/group/prod): generalize topological groups to measurable groups ([#11933](https://github.com/leanprover-community/mathlib/pull/11933))
* This fixes the gap in `[Halmos]` that I mentioned in `measure_theory.group.prod`
* Thanks to @sgouezel for giving me the proof to fill that gap.
* A text proof to fill the gap is [here](https://math.stackexchange.com/a/4387664/463377)

### [2022-02-24 12:56:58](https://github.com/leanprover-community/mathlib/commit/8429ec9)
feat(topology/vector_bundle): `topological_vector_prebundle` ([#8154](https://github.com/leanprover-community/mathlib/pull/8154))
In this PR we implement a new standard construction for topological vector bundles: namely a structure that permits to define a vector bundle when trivializations are given as local equivalences but there is not yet a topology on the total space. The total space is hence given a topology in such a way that there is a vector bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations.

### [2022-02-24 11:57:32](https://github.com/leanprover-community/mathlib/commit/76b1e01)
feat(data/equiv/option): option_congr ([#12263](https://github.com/leanprover-community/mathlib/pull/12263))
This is a universe-polymorphic version of the existing `equiv_functor.map_equiv option`.

### [2022-02-24 11:57:31](https://github.com/leanprover-community/mathlib/commit/b8b1b57)
chore(geometry/euclidean): split repetitive proof ([#12209](https://github.com/leanprover-community/mathlib/pull/12209))
This PR is part of the subobject refactor [#11545](https://github.com/leanprover-community/mathlib/pull/11545), fixing a timeout caused by some expensive defeq checks.
I introduce a new definition `simplex.orthogonal_projection_span s := orthogonal_projection (affine_span ℝ (set.range s.points))`, and extract a couple of its properties from (repetitive) parts of proofs in `circumcenter.lean`, especially `eq_or_eq_reflection_of_dist_eq`. This makes the latter proof noticeably faster, especially after commit [#11750](https://github.com/leanprover-community/mathlib/pull/11750).

### [2022-02-24 10:42:14](https://github.com/leanprover-community/mathlib/commit/3d97cfb)
feat(ring_theory/ideal,dedekind_domain): lemmas on `I ≤ I^e` and `I < I^e` ([#12185](https://github.com/leanprover-community/mathlib/pull/12185))

### [2022-02-24 08:26:23](https://github.com/leanprover-community/mathlib/commit/9eb78a3)
feat(measure_theory/function/ae_eq_fun): generalize scalar actions ([#12248](https://github.com/leanprover-community/mathlib/pull/12248))
This provides a more general `has_scalar` instance, along with `mul_action`, `distrib_mul_action`, `module`, `is_scalar_tower`, `smul_comm_class`, and `is_central_scalar` instances.

### [2022-02-24 04:27:02](https://github.com/leanprover-community/mathlib/commit/f6a7ad9)
feat(measure_theory/integral/average): define `measure_theory.average` ([#12128](https://github.com/leanprover-community/mathlib/pull/12128))
And use it to formulate Jensen's inequality. Also add Jensen's inequality for concave functions.

### [2022-02-24 03:44:56](https://github.com/leanprover-community/mathlib/commit/f3ee462)
chore(category_theory/adjunction/opposites): Forgotten `category_theory` namespace ([#12256](https://github.com/leanprover-community/mathlib/pull/12256))
The forgotten `category_theory` namespace means that dot notation doesn't work on `category_theory.adjunction`.

### [2022-02-24 02:51:27](https://github.com/leanprover-community/mathlib/commit/ed55593)
feat(topology/metric_space/basic): add a few lemmas ([#12259](https://github.com/leanprover-community/mathlib/pull/12259))
Add `ne_of_mem_sphere`, `subsingleton_closed_ball`, and `metric.subsingleton_sphere`.

### [2022-02-24 01:18:43](https://github.com/leanprover-community/mathlib/commit/158550d)
feat(algebra/module/basic): add `smul_right_inj` ([#12252](https://github.com/leanprover-community/mathlib/pull/12252))
Also golf the proof of `smul_right_injective` by reusing
`add_monoid_hom.injective_iff`.

### [2022-02-24 01:18:42](https://github.com/leanprover-community/mathlib/commit/2939c77)
feat(topology/metric_space): multiplicative opposites inherit the same `(pseudo_?)(e?)metric` and `uniform_space` ([#12120](https://github.com/leanprover-community/mathlib/pull/12120))
This puts the "obvious" metric on the opposite type such that `dist (op x) (op y) = dist x y`.
This also merges `subtype.pseudo_dist_eq` and `subtype.dist_eq` as the latter was a special case of the former.

### [2022-02-24 00:25:00](https://github.com/leanprover-community/mathlib/commit/890338d)
feat(analysis/normed_space/basic): use weaker assumptions ([#12260](https://github.com/leanprover-community/mathlib/pull/12260))
Assume `r ≠ 0` instead of `0 < r` in `interior_closed_ball` and `frontier_closed_ball`.

### [2022-02-24 00:24:57](https://github.com/leanprover-community/mathlib/commit/620af85)
refactor(topology/instances): put `ℕ`, `ℤ`, and `ℚ` in separate files ([#12207](https://github.com/leanprover-community/mathlib/pull/12207))
The goal here is to make `metric_space ℕ` and `metric_space ℤ` available earlier, so that I can state `has_bounded_smul ℕ A` somewhere reasonable.
No lemmas have been added, deleted, or changed here - they've just been moved out of `topology/instances/real` and into 
`topology/instances/{nat,int,rat,real}`.
The resulting import structure is:
* `rat_lemmas` → `rat`
* `rat` → {`real`, `int`, `nat`}
* `real` → {`int`}
* `nat` → {`int`}

### [2022-02-23 22:56:45](https://github.com/leanprover-community/mathlib/commit/eae6ae3)
feat(algebra/associated): add decidable instances ([#12230](https://github.com/leanprover-community/mathlib/pull/12230))
Makes equality and divisibility decidable in `associates`, given that divisibility is decidable in the general case.

### [2022-02-23 21:42:45](https://github.com/leanprover-community/mathlib/commit/2c74921)
feat(data/pfun): A new induction on pfun.fix ([#12109](https://github.com/leanprover-community/mathlib/pull/12109))
A new lemma that lets you prove predicates given `b ∈ f.fix a` if `f` preserves the predicate, and it holds for values which `f` maps to `b`.

### [2022-02-23 20:58:29](https://github.com/leanprover-community/mathlib/commit/9b333b2)
feat(topology/algebra/continuous_monoid_hom): `to_continuous_map` is a `closed_embedding` ([#12217](https://github.com/leanprover-community/mathlib/pull/12217))
This PR proves that `to_continuous_map : continuous_monoid_hom A B → C(A, B)` is a `closed_embedding`. This will be useful for showing that the Pontryagin dual is locally compact.

### [2022-02-23 17:43:01](https://github.com/leanprover-community/mathlib/commit/f04ad9a)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a selfadjoint element in a C*-algebra is its norm. ([#12211](https://github.com/leanprover-community/mathlib/pull/12211))
This establishes that the spectral radius of a selfadjoint element in a C*-algebra is its (nn)norm using the Gelfand formula for the spectral radius. The same theorem for normal elements can be proven using this once normal elements are defined in mathlib.

### [2022-02-23 16:03:57](https://github.com/leanprover-community/mathlib/commit/b72cca4)
chore(geometry/manifold/algebra/smooth_functions): golf module instance ([#12247](https://github.com/leanprover-community/mathlib/pull/12247))

### [2022-02-23 16:03:56](https://github.com/leanprover-community/mathlib/commit/3e2df83)
docs(order/order_iso_nat): Added note on `exists_increasing_or_nonincreasing_subseq` ([#12239](https://github.com/leanprover-community/mathlib/pull/12239))

### [2022-02-23 16:03:55](https://github.com/leanprover-community/mathlib/commit/162d060)
feat(measure_theory/function/strongly_measurable): more basic properties of `strongly_measurable` ([#12164](https://github.com/leanprover-community/mathlib/pull/12164))

### [2022-02-23 16:03:54](https://github.com/leanprover-community/mathlib/commit/3fe20d4)
feat(ring_theory/localization): add mk' lemmas ([#12081](https://github.com/leanprover-community/mathlib/pull/12081))

### [2022-02-23 14:40:03](https://github.com/leanprover-community/mathlib/commit/0d5bed0)
feat(ring_theory/graded_algebra): definitions and basic operations of homogeneous ideal ([#10784](https://github.com/leanprover-community/mathlib/pull/10784))
This defines homogeneous ideals (`homogeneous_ideal`) of a graded algebra.

### [2022-02-23 13:18:22](https://github.com/leanprover-community/mathlib/commit/e167efa)
chore(topology/instances/rat): rename to rat_lemmas ([#12246](https://github.com/leanprover-community/mathlib/pull/12246))
This is to make room for the changes in [#12207](https://github.com/leanprover-community/mathlib/pull/12207), which claim `topology.instances.rat` for more basic results. This has to be in a separate commit to keep the history reasonable.

### [2022-02-23 13:18:20](https://github.com/leanprover-community/mathlib/commit/c526789)
feat(set_theory/ordinal_arithmetic): `is_normal.eq_iff_zero_and_succ` ([#12222](https://github.com/leanprover-community/mathlib/pull/12222))
Two normal functions are equal iff they're equal at `0` and successor ordinals. This is used for a few lemmas in [#12202](https://github.com/leanprover-community/mathlib/pull/12202).

### [2022-02-23 13:18:19](https://github.com/leanprover-community/mathlib/commit/7de8137)
feat(topology/order/hom): Continuous order homomorphisms ([#12012](https://github.com/leanprover-community/mathlib/pull/12012))
Define continuous monotone functions, aka continuous order homomorphisms, aka Priestley homomorphisms, with notation `α →Co β`.

### [2022-02-23 12:32:53](https://github.com/leanprover-community/mathlib/commit/b0fbd91)
feat(measure_theory/measure): generalize scalar actions ([#12187](https://github.com/leanprover-community/mathlib/pull/12187))
As a result of this change, many smul lemmas now also apply to `nat` and `nnreal`, which allows some lemmas to be removed.

### [2022-02-23 12:32:52](https://github.com/leanprover-community/mathlib/commit/d01b55f)
split(analysis/functional/gauge): Split off `analysis.seminorm` ([#12054](https://github.com/leanprover-community/mathlib/pull/12054))
Move the Minkowski functional to a new file `analysis.convex.gauge`.

### [2022-02-23 10:50:57](https://github.com/leanprover-community/mathlib/commit/6179707)
feat(ring_theory/unique_factorization_domain): add count_self ([#12074](https://github.com/leanprover-community/mathlib/pull/12074))

### [2022-02-23 10:50:56](https://github.com/leanprover-community/mathlib/commit/6f1d90d)
feat(algebra/order/monoid_lemmas_gt_zero): introduce the type of positive elements and prove some lemmas ([#11833](https://github.com/leanprover-community/mathlib/pull/11833))
This PR continues the `order` refactor.  Here I start working with the type of positive elements of a type with zero and lt.  Combining `covariant_` and `contravariant_classes` where the "acting" type is the type of positive elements, we can formulate the condition that "multiplication by positive elements is monotone" and variants.
I also prove some initial lemmas, just to give a flavour of the API.
More such lemmas will come in subsequent PRs (see for instance [#11782](https://github.com/leanprover-community/mathlib/pull/11782) for a few more lemmas).  After that, I will start simplifying existing lemmas, by weakening their assumptions.

### [2022-02-23 09:39:52](https://github.com/leanprover-community/mathlib/commit/3e77124)
refactor(topology/{separation,subset_properties}): use `set.subsingleton` ([#12232](https://github.com/leanprover-community/mathlib/pull/12232))
Use `set.subsingleton s` instead of `_root_.subsingleton s` in `is_preirreducible_iff_subsingleton` and `is_preirreducible_of_subsingleton`, rename the latter to `set.subsingleton.is_preirreducible`.

### [2022-02-23 09:39:50](https://github.com/leanprover-community/mathlib/commit/dc9b8be)
feat(analysis/normed_space/linear_isometry): add lemmas to `linear_isometry_equiv` ([#12218](https://github.com/leanprover-community/mathlib/pull/12218))
Added two API lemmas to `linear_isometry_equiv` that I need elsewhere.

### [2022-02-23 09:39:49](https://github.com/leanprover-community/mathlib/commit/f44ed74)
feat(ring_theory/ideal/over): `S/p` is noetherian over `R/p` if `S` is over `R` ([#12183](https://github.com/leanprover-community/mathlib/pull/12183))

### [2022-02-23 08:16:08](https://github.com/leanprover-community/mathlib/commit/515eefa)
fix(algebra/star/basic): more type classes that should be props ([#12235](https://github.com/leanprover-community/mathlib/pull/12235))

### [2022-02-23 08:16:07](https://github.com/leanprover-community/mathlib/commit/98bcabb)
feat(group_theory/perm): add lemmas for cycles of permutations ([#11955](https://github.com/leanprover-community/mathlib/pull/11955))
`nodup_powers_of_cycle_of` : shows that the the iterates of an element in the support give rise to a nodup list
`cycle_is_cycle_of` : asserts that a given cycle c in `f. cycle_factors_finset` is `f.cycle_of a` if c a \neq a
`equiv.perm.sign_of_cycle_type` : new formula for the sign of a permutations in terms of its cycle_type — It is simpler to use (just uses number of cycles and size of support) than the earlier lemma which is renamed as equiv.perm.sign_of_cycle_type'  (it could be deleted). I made one modification to make the file compile, but I need to check compatibility with the other ones.

### [2022-02-23 07:46:35](https://github.com/leanprover-community/mathlib/commit/0eed60e)
feat(number_theory/cyclotomic/discriminant): discriminant of a p-th cyclotomic field ([#11804](https://github.com/leanprover-community/mathlib/pull/11804))
We compute the discriminant of a p-th cyclotomic field.
From flt-regular.
- [x] depends on: [#11786](https://github.com/leanprover-community/mathlib/pull/11786)

### [2022-02-23 05:24:19](https://github.com/leanprover-community/mathlib/commit/257bddf)
feat(algebra/algebra/spectrum): add spectral mapping for inverses ([#12219](https://github.com/leanprover-community/mathlib/pull/12219))
Given a unit `a` in an algebra `A` over a field `𝕜`, the equality `(spectrum 𝕜 a)⁻¹ = spectrum 𝕜 a⁻¹` holds.

### [2022-02-23 04:31:26](https://github.com/leanprover-community/mathlib/commit/e77675d)
fix(analysis/normed_space/star/basic): make prop type classes props ([#12233](https://github.com/leanprover-community/mathlib/pull/12233))
The type classes `normed_star_monoid` and `cstar_ring` are now properly declared as prop.

### [2022-02-23 04:01:36](https://github.com/leanprover-community/mathlib/commit/264dd7f)
feat(model_theory/basic): Language operations ([#12129](https://github.com/leanprover-community/mathlib/pull/12129))
Defines language homomorphisms with `first_order.language.Lhom`
Defines the sum of two languages with `first_order.language.sum`
Defines `first_order.language.with_constants`, a language with added constants, abbreviated `L[[A]]`.
Defines a `L[[A]].Structure` on `M` when `A : set M`.
(Some of this code comes from the Flypitch project)

### [2022-02-23 00:45:57](https://github.com/leanprover-community/mathlib/commit/7cc4eb9)
doc(number_theory/padics/*): typo in references ([#12229](https://github.com/leanprover-community/mathlib/pull/12229))
Fix typos in a reference.

### [2022-02-23 00:45:56](https://github.com/leanprover-community/mathlib/commit/4238868)
chore(analysis): rename times_cont_diff ([#12227](https://github.com/leanprover-community/mathlib/pull/12227))
This replaces `times_cont_diff` by `cont_diff` everywhere, and the same for `times_cont_mdiff`. There is no change at all in content.
See https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/times_cont_diff.20name

### [2022-02-23 00:45:54](https://github.com/leanprover-community/mathlib/commit/541a1a0)
refactor(combinatorics/simple_graph/{basic,degree_sum}): move darts from degree_sum to basic ([#12195](https://github.com/leanprover-community/mathlib/pull/12195))
This also changes `simple_graph.dart` to extend `prod`, so that darts are even closer to being an ordered pair.
Since this touches the module docstrings, they are updated to use fully qualified names.

### [2022-02-23 00:45:53](https://github.com/leanprover-community/mathlib/commit/f6ec999)
feat(ring_theory/localization): add a fintype instance ([#12150](https://github.com/leanprover-community/mathlib/pull/12150))

### [2022-02-22 22:49:03](https://github.com/leanprover-community/mathlib/commit/e89222a)
feat(algebra/module,linear_algebra): some `restrict_scalars` lemmas ([#12181](https://github.com/leanprover-community/mathlib/pull/12181))
 * add `linear_map.coe_restrict_scalars` (demoting `linear_map.restrict_scalars_apply` from `simp` lemma)
 * add `submodule.restrict_scalars_eq_top_iff`

### [2022-02-22 22:49:02](https://github.com/leanprover-community/mathlib/commit/2ab3e2f)
feat(algebra/group/{hom,prod}): has_mul and mul_hom.prod ([#12110](https://github.com/leanprover-community/mathlib/pull/12110))
Ported over from `monoid_hom`.

### [2022-02-22 22:49:01](https://github.com/leanprover-community/mathlib/commit/18d1bdf)
feat(topology/algebra/group): add subgroup lemmas ([#12026](https://github.com/leanprover-community/mathlib/pull/12026))

### [2022-02-22 22:49:00](https://github.com/leanprover-community/mathlib/commit/b60b790)
feat(topology/algebra/group): add continuity lemmas ([#11975](https://github.com/leanprover-community/mathlib/pull/11975))

### [2022-02-22 21:10:39](https://github.com/leanprover-community/mathlib/commit/64c8d21)
feat(set_theory/ordinal): `Inf_empty` ([#12226](https://github.com/leanprover-community/mathlib/pull/12226))
The docs mention that `Inf Ø` is defined as `0`. We prove that this is indeed the case.

### [2022-02-22 21:10:38](https://github.com/leanprover-community/mathlib/commit/d990681)
docs(set_theory/ordinal): Remove mention of `omin` from docs ([#12224](https://github.com/leanprover-community/mathlib/pull/12224))
[#11867](https://github.com/leanprover-community/mathlib/pull/11867) replaced `omin` by `Inf`. We remove all mentions of it from the docs.

### [2022-02-22 21:10:37](https://github.com/leanprover-community/mathlib/commit/f7b6f42)
feat(set_theory/ordinal_arithmetic): `out_nonempty_iff_ne_zero` ([#12223](https://github.com/leanprover-community/mathlib/pull/12223))

### [2022-02-22 21:10:36](https://github.com/leanprover-community/mathlib/commit/e50ebde)
chore(analysis/specific_limits): simplify proof of `cauchy_series_of_le_geometric` ([#12215](https://github.com/leanprover-community/mathlib/pull/12215))
This lemma is identical to the one above except over `range (n + 1)`
instead of `range n`. Perhaps it could be removed entirely? I'm not sure what the policy is on breaking changes.

### [2022-02-22 21:10:34](https://github.com/leanprover-community/mathlib/commit/48ddfd5)
chore(linear_algebra/basic): golf `linear_equiv.smul_of_unit` ([#12190](https://github.com/leanprover-community/mathlib/pull/12190))
This already exists more generally as `distrib_mul_action.to_linear_equiv`.
The name is probably more discoverable and it needs fewer arguments, so I've left it around for now.

### [2022-02-22 20:21:17](https://github.com/leanprover-community/mathlib/commit/6bb8f22)
refactor(model_theory/terms_and_formulas): Improvements to basics of first-order formulas ([#12091](https://github.com/leanprover-community/mathlib/pull/12091))
Improves the simp set of lemmas related to `realize_bounded_formula` and `realize_formula`, so that they simplify higher-level definitions directly, and keep bounded formulas and formulas separate.
Generalizes relabelling of bounded formulas.
Defines `close_with_exists` and `close_with_forall` to quantify bounded formulas into closed formulas.
Defines `bd_iff` and `iff`.

### [2022-02-22 18:15:35](https://github.com/leanprover-community/mathlib/commit/d054fca)
feat(/analysis/inner_product_space/pi_L2): `inner_matrix_row_row` ([#12177](https://github.com/leanprover-community/mathlib/pull/12177))
The inner product between rows/columns of matrices.

### [2022-02-22 18:15:34](https://github.com/leanprover-community/mathlib/commit/d0c37a1)
feat(analysis/inner_product_space/adjoint): is_self_adjoint_iff_inner… ([#12113](https://github.com/leanprover-community/mathlib/pull/12113))
…_map_self_real
A linear operator on a complex inner product space is self-adjoint
precisely when ⟪T v, v⟫ is real for all v.  I am interested in learning
style improvements!

### [2022-02-22 18:15:32](https://github.com/leanprover-community/mathlib/commit/8f16001)
chore(*): rename `erase_dup` to `dedup` ([#12057](https://github.com/leanprover-community/mathlib/pull/12057))

### [2022-02-22 18:15:31](https://github.com/leanprover-community/mathlib/commit/35ef770)
refactor(topology/compacts): Turn into structures, use `set_like`, cleanup ([#12035](https://github.com/leanprover-community/mathlib/pull/12035))
* Change `closeds`, `compacts`, `nonempty_compacts`, `positive_compacts` from `subtype` to `structure`
* Use `set_like`
* Add missing instances
  * the `lattice` and `bounded_order` instances for `closeds`
  * the `bounded_order` instance for `compacts`
  * the `semilattice_sup` and `order_top` instances for `nonempty_compacts` 
  * the `inhabited`, `semilattice_sup` and `order_top` instances for `positive_compacts`
* kill `positive_compacts_univ` in favor of `⊤` using the new `order_top` instance
* rename `nonempty_positive_compacts` to `positive_compacts.nonempty`
* sectioning the file

### [2022-02-22 15:16:21](https://github.com/leanprover-community/mathlib/commit/71da192)
chore(ring_theory/graded_algebra/basic): remove commutativity requirement ([#12208](https://github.com/leanprover-community/mathlib/pull/12208))
This wasn't used

### [2022-02-22 15:16:20](https://github.com/leanprover-community/mathlib/commit/f0401b9)
chore(ring_theory): split `localization.lean` and `dedekind_domain.lean` ([#12206](https://github.com/leanprover-community/mathlib/pull/12206))
These files were rather long and had hundreds-deep dependency graphs. I split them into smaller files with less imports, so that they are easier to build and modify.
Proof nothing was lost:
```bash
$ cat src/ring_theory/localization/*.lean | sort | comm -23 <(sort src/ring_theory/localization.lean) - | grep -E 'lemma|theorem|def|instance|class'
$ cat src/ring_theory/dedekind_domain/*.lean | sort | comm -23 <(sort src/ring_theory/dedekind_domain.lean) - | grep -E 'lemma|theorem|def|instance|class'
giving three equivalent definitions (TODO: and shows that they are equivalent).
```
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Splitting.20.60localization.2Elean.60.20and.20.60dedekind_domain.2Elean

### [2022-02-22 15:16:19](https://github.com/leanprover-community/mathlib/commit/deb5046)
feat(mv_polynomial/basic): monomial_eq_monomial_iff ([#12198](https://github.com/leanprover-community/mathlib/pull/12198))

### [2022-02-22 15:16:18](https://github.com/leanprover-community/mathlib/commit/8b09b0e)
feat(measure_theory/group/arithmetic): add `has_measurable_smul.op` and `has_measurable_smul₂.op` ([#12196](https://github.com/leanprover-community/mathlib/pull/12196))
This matches the naming of `has_continuous_smul.op`.

### [2022-02-22 15:16:17](https://github.com/leanprover-community/mathlib/commit/79c5de9)
feat(ring_theory/ideal/operations): remove unneeded assumptions from `smul_induction_on` ([#12193](https://github.com/leanprover-community/mathlib/pull/12193))

### [2022-02-22 15:16:15](https://github.com/leanprover-community/mathlib/commit/f6d397f)
feat(order/hom/basic): `order_iso_class` ([#12157](https://github.com/leanprover-community/mathlib/pull/12157))
Define `order_iso_class`, following the hom refactor. Also add a few missing lemmas.

### [2022-02-22 15:16:14](https://github.com/leanprover-community/mathlib/commit/4c6b0de)
feat(topology/bases): disjoint unions of second-countable spaces are second-countable ([#12061](https://github.com/leanprover-community/mathlib/pull/12061))

### [2022-02-22 13:18:00](https://github.com/leanprover-community/mathlib/commit/8413f07)
feat(topology/support): define topological support and compactly supported functions ([#11923](https://github.com/leanprover-community/mathlib/pull/11923))
* Also add some variants of the extreme value theorem.

### [2022-02-22 10:50:40](https://github.com/leanprover-community/mathlib/commit/80591d6)
feat(order/hom/lattice): Finitary join-/meet-preserving maps ([#12149](https://github.com/leanprover-community/mathlib/pull/12149))
Define `sup_bot_hom`, `inf_top_hom` and their associated class.

### [2022-02-22 10:50:39](https://github.com/leanprover-community/mathlib/commit/68efb10)
refactor(topology/*): Hom classes for continuous maps/homs ([#11909](https://github.com/leanprover-community/mathlib/pull/11909))
Add
* `continuous_map_class`
* `bounded_continuous_map_class`
* `continuous_monoid_hom_class`
* `continuous_add_monoid_hom_class`
* `continuous_map.homotopy_class`
to follow the `fun_like` design. Deprecate lemmas accordingly.
Also rename a few fields to match the convention in the rest of the library.

### [2022-02-22 10:50:38](https://github.com/leanprover-community/mathlib/commit/247943a)
feat(analysis/seminorm): add inf ([#11791](https://github.com/leanprover-community/mathlib/pull/11791))
Define the infimum of seminorms.

### [2022-02-22 10:10:32](https://github.com/leanprover-community/mathlib/commit/9a7ed8c)
chore(algebra/lie/engel): speed up proof of Engel's theorem slightly ([#12205](https://github.com/leanprover-community/mathlib/pull/12205))
Local measurements using `set_option profiler true` are noisy but indicate
that this speeds up elaboration of `lie_algebra.is_engelian_of_is_noetherian`
by about 20% from about 10s to about 8s.

### [2022-02-22 03:09:07](https://github.com/leanprover-community/mathlib/commit/cb45da2)
feat(category_theory/limits): is_bilimit ([#12108](https://github.com/leanprover-community/mathlib/pull/12108))

### [2022-02-22 00:37:45](https://github.com/leanprover-community/mathlib/commit/e16e093)
feat(analysis/specific_limits): dirichlet and alternating series tests  ([#11908](https://github.com/leanprover-community/mathlib/pull/11908))
Adds [Dirichlet's test](https://en.wikipedia.org/wiki/Dirichlet%27s_test) along with the [alternating series test](https://en.wikipedia.org/wiki/Alternating_series_test) as a special case of the former. For the curious, [Nick Bingham's course notes](https://www.ma.imperial.ac.uk/~bin06/M2PM3-Complex-Analysis/m2pm3abeldir.pdf) give some more context on Dirichlet's test. It's somewhat obscure.

### [2022-02-21 23:46:54](https://github.com/leanprover-community/mathlib/commit/d77e91f)
perf(geometry/euclidean): speed up proof on the edge of timing out ([#12191](https://github.com/leanprover-community/mathlib/pull/12191))

### [2022-02-21 23:46:53](https://github.com/leanprover-community/mathlib/commit/22464cf)
feat(analysis/normed_space/basic): `norm_matrix_lt_iff` ([#12151](https://github.com/leanprover-community/mathlib/pull/12151))
A strict variant of `norm_matrix_le_iff`, using `pi_norm_lt_iff`

### [2022-02-21 22:53:11](https://github.com/leanprover-community/mathlib/commit/eb5c5ed)
feat(measure_theory/integral/set_integral): Bochner integral with respect to a measure with density ([#12123](https://github.com/leanprover-community/mathlib/pull/12123))
This PR shows that `∫ a, g a ∂(μ.with_density (λ x, f x)) = ∫ a, f a • g a ∂μ`. (This fact is already available for the Lebesgue integral, not for the Bochner integral.)

### [2022-02-21 22:24:46](https://github.com/leanprover-community/mathlib/commit/8aa26b2)
feat(tactic/linear_combination): improve error messages and degenerate case ([#12062](https://github.com/leanprover-community/mathlib/pull/12062))
This threads the expected type of the combination from the target throughout the tactic call.
If no hypotheses are given to combine, the behavior is effectively to just call the normalization tactic.
closes [#11990](https://github.com/leanprover-community/mathlib/pull/11990)

### [2022-02-21 21:06:38](https://github.com/leanprover-community/mathlib/commit/2971f3d)
feat(algebra/star/self_adjoint): remove commutativity hypothesis from `has_pow (self_adjoint R)` ([#12188](https://github.com/leanprover-community/mathlib/pull/12188))
This was put in the wrong section. Powers of selfadjoint elements are still selfadjoint.

### [2022-02-21 21:06:37](https://github.com/leanprover-community/mathlib/commit/a607820)
feat(category_theory/equivalence): if two functors F and G are isomorphic, F is an equivalence iff G is ([#12162](https://github.com/leanprover-community/mathlib/pull/12162))

### [2022-02-21 21:06:35](https://github.com/leanprover-community/mathlib/commit/9a17b55)
feat(analysis/normed_space/basic): `norm_entry_le_entrywise_sup_norm` ([#12159](https://github.com/leanprover-community/mathlib/pull/12159))
The entries of a matrix are at most the entrywise sup norm.

### [2022-02-21 19:14:30](https://github.com/leanprover-community/mathlib/commit/1cfbcc6)
feat(algebra/ring/ulift): add a `field` instance ([#12141](https://github.com/leanprover-community/mathlib/pull/12141))

### [2022-02-21 16:41:40](https://github.com/leanprover-community/mathlib/commit/e3d3681)
feat(analysis/inner_product_space/spectrum): `pos_nonneg_eigenvalues` ([#12161](https://github.com/leanprover-community/mathlib/pull/12161))
If T is a positive self-adjoint operator, then its eigenvalues are
nonnegative.  Maybe there should be a definition of "positive operator",
and maybe this should be generalized.  Guidance appreciated!

### [2022-02-21 15:30:08](https://github.com/leanprover-community/mathlib/commit/02dc6f2)
feat(probability/stopping): filtrations are a complete lattice ([#12169](https://github.com/leanprover-community/mathlib/pull/12169))

### [2022-02-21 15:30:07](https://github.com/leanprover-community/mathlib/commit/9ed7179)
refactor(*): move normed field lemmas into root namespace ([#12163](https://github.com/leanprover-community/mathlib/pull/12163))
This takes the normed field lemmas given in `analysis.normed_space.basic` and moves them from the `normed_field` namespace into the root namespace.
This PR moves these lemmas and definitions: `norm_mul`, `nnnorm_mul`, `norm_hom`, `nnnorm_hom`, `norm_pow`, `nnnorm_pow`, `norm_prod`, `nnnorm_prod`, `norm_div`, `nnnorm_div`, `norm_inv`, `nnnorm_inv`, `norm_zpow`, `nnnorm_zpow`.

### [2022-02-21 15:30:06](https://github.com/leanprover-community/mathlib/commit/95d22b5)
feat(geometry/euclidean/oriented_angle): oriented angles and rotations ([#12106](https://github.com/leanprover-community/mathlib/pull/12106))
Define oriented angles and rotations in a real inner product space,
with respect to a choice of orthonormal basis indexed by `fin 2`, and
prove various lemmas about them, including that the definition depends
only on the orientation associated with the basis, and geometrical
results such as pons asinorum, "angle at center of a circle equals
twice angle at circumference" and "angles in same segment are equal" /
"opposite angles of a cyclic quadrilateral add to π" (these last two
being the same result for oriented angles mod π).

### [2022-02-21 15:30:04](https://github.com/leanprover-community/mathlib/commit/6db1577)
feat(category_theory/preadditive): separators in preadditive categories ([#11884](https://github.com/leanprover-community/mathlib/pull/11884))

### [2022-02-21 13:33:45](https://github.com/leanprover-community/mathlib/commit/3ad7395)
chore(topology/algebra/infinite_sum): reference Cauchy criterion in docs ([#12172](https://github.com/leanprover-community/mathlib/pull/12172))

### [2022-02-21 13:33:44](https://github.com/leanprover-community/mathlib/commit/634dfc8)
feat(order/*): Missing order lifting instances ([#12154](https://github.com/leanprover-community/mathlib/pull/12154))
Add a few missing pullbacks of order instances.

### [2022-02-21 13:33:43](https://github.com/leanprover-community/mathlib/commit/2f33463)
feat(group_theory/free_product): is_free_group_free_product_of_is_free_group ([#12125](https://github.com/leanprover-community/mathlib/pull/12125))

### [2022-02-21 11:38:07](https://github.com/leanprover-community/mathlib/commit/7c6678a)
doc(topology/dense_embedding): fix markdown ([#12180](https://github.com/leanprover-community/mathlib/pull/12180))
Right now it just renders as "γ -f→ α g↓ ↓e δ -h→ β"

### [2022-02-21 11:38:06](https://github.com/leanprover-community/mathlib/commit/f66a5dd)
chore(data/set/basic): add a few lemmas and a `@[simp]` attribute ([#12176](https://github.com/leanprover-community/mathlib/pull/12176))
* rename `set.exists_eq_singleton_iff_nonempty_unique_mem` to `set.exists_eq_singleton_iff_nonempty_subsingleton`, use `set.subsingleton` in the statement;
* add `@[simp]` to `set.subset_compl_singleton_iff`;
* add `set.diff_diff_right_self`.

### [2022-02-21 11:38:05](https://github.com/leanprover-community/mathlib/commit/0eb5e2d)
feat(topology/algebra): if a subobject is commutative, then so is its topological closure ([#12170](https://github.com/leanprover-community/mathlib/pull/12170))
We prove that if a submonoid (or subgroup, subsemiring, subring, subalgebra, and the additive versions where applicable) is commutative, then so is its topological closure.

### [2022-02-21 11:38:04](https://github.com/leanprover-community/mathlib/commit/56dbb60)
feat(category_theory/opposites): nat_trans.remove_unop ([#12147](https://github.com/leanprover-community/mathlib/pull/12147))

### [2022-02-21 11:38:02](https://github.com/leanprover-community/mathlib/commit/b3b5e35)
chore(data/nat/prime): slightly golf proof of mem_factors ([#12143](https://github.com/leanprover-community/mathlib/pull/12143))

### [2022-02-21 11:38:01](https://github.com/leanprover-community/mathlib/commit/afcc7e7)
feat(data/nat/prime): move nat.prime_iff_prime_int; add int.prime_two/three ([#12133](https://github.com/leanprover-community/mathlib/pull/12133))
I found it useful to have these results with somewhat lighter imports.

### [2022-02-21 11:38:00](https://github.com/leanprover-community/mathlib/commit/37019db)
feat(topology/algebra/{group,monoid}): nat and int scalar multiplication is continuous ([#12124](https://github.com/leanprover-community/mathlib/pull/12124))
These instances allow a diamond to appear in the scalar action on `continuous_affine_map`s, which we fix at the same time.

### [2022-02-21 11:37:58](https://github.com/leanprover-community/mathlib/commit/72252b3)
feat(analysis/inner_product_space/projection): norm_sq_eq_sum_norm_sq… ([#12096](https://github.com/leanprover-community/mathlib/pull/12096))
…_projection
The Pythagorean theorem for an orthogonal projection onto a submodule S.
I am sure that there are some style changes that could/should be made!

### [2022-02-21 11:37:57](https://github.com/leanprover-community/mathlib/commit/271c323)
feat(order/filter): prod_assoc ([#12002](https://github.com/leanprover-community/mathlib/pull/12002))
map (prod_assoc α β γ) ((f ×ᶠ g) ×ᶠ h) = f ×ᶠ (g ×ᶠ h)
with two tiny supporting lemmas

### [2022-02-21 11:37:56](https://github.com/leanprover-community/mathlib/commit/d8d2f54)
feat(group_theory/nilpotent): n-ary products of nilpotent group ([#11829](https://github.com/leanprover-community/mathlib/pull/11829))

### [2022-02-21 10:14:55](https://github.com/leanprover-community/mathlib/commit/e966efc)
chore(topology/constructions): golf a proof ([#12174](https://github.com/leanprover-community/mathlib/pull/12174))

### [2022-02-21 10:14:54](https://github.com/leanprover-community/mathlib/commit/d0fa7a8)
chore(category_theory/limits): make fin_category_opposite an instance ([#12153](https://github.com/leanprover-community/mathlib/pull/12153))

### [2022-02-21 09:47:15](https://github.com/leanprover-community/mathlib/commit/b04851f)
chore(tactic): fix tactic doc tags ([#12131](https://github.com/leanprover-community/mathlib/pull/12131))

### [2022-02-21 08:48:32](https://github.com/leanprover-community/mathlib/commit/8b93d3a)
feat(measure_theory/function/lp_space): generalize some `integrable` lemmas to `mem_ℒp` ([#11231](https://github.com/leanprover-community/mathlib/pull/11231))
I would like to define integrable as `mem_ℒp` for `p = 1` and remove the `has_finite_integral` prop. But first we need to generalize everything we have about `integrable` to `mem_ℒp`. This is one step towards that goal.

### [2022-02-21 08:00:52](https://github.com/leanprover-community/mathlib/commit/e60e1f2)
feat(data/real/pointwise): mul distributes over `infi` and `supr` ([#12105](https://github.com/leanprover-community/mathlib/pull/12105))

### [2022-02-21 00:51:52](https://github.com/leanprover-community/mathlib/commit/6298a43)
feat(analysis/seminorm): smul_sup ([#12103](https://github.com/leanprover-community/mathlib/pull/12103))
The `have : real.smul_max` local proof doesn't feel very general, so I've left it as a `have` rather than promoting it to a lemma.

### [2022-02-21 00:51:51](https://github.com/leanprover-community/mathlib/commit/6ecd7ab)
feat(topology/continuous_function/bounded): generalize scalar action ([#12098](https://github.com/leanprover-community/mathlib/pull/12098))
This also makes the scalar action computable

### [2022-02-20 23:53:46](https://github.com/leanprover-community/mathlib/commit/6ae1b70)
feat(topology/uniform_space/cauchy): add `cauchy_seq.comp_injective` ([#11986](https://github.com/leanprover-community/mathlib/pull/11986))
API changes:
- add `filter.at_top_le_cofinite`;
- add `function.injective.nat_tendsto_at_top`;
- add `cauchy_seq.comp_injective`, `function.bijective.cauchy_seq_comp_iff`.

### [2022-02-20 22:01:51](https://github.com/leanprover-community/mathlib/commit/7e1ef9f)
feat(ring_theory/witt_vector): assorted facts about Witt vectors over char p rings ([#12093](https://github.com/leanprover-community/mathlib/pull/12093))

### [2022-02-20 14:25:15](https://github.com/leanprover-community/mathlib/commit/334fb89)
feat(algebra/order/ring): add three_ne_zero and four_ne_zero ([#12142](https://github.com/leanprover-community/mathlib/pull/12142))

### [2022-02-20 09:43:13](https://github.com/leanprover-community/mathlib/commit/6c6e142)
chore(data/nat/factorization): Reorder lemmas and some minor golfing ([#12144](https://github.com/leanprover-community/mathlib/pull/12144))
Some minor housework on this file, reordering and regrouping lemmas, adding and editing a few docstrings and section headers, and golfing a few proofs.

### [2022-02-20 01:22:26](https://github.com/leanprover-community/mathlib/commit/55c9cff)
chore(data/nat/prime): slightly weaken assumption in nat.exists_prime_and_dvd ([#12156](https://github.com/leanprover-community/mathlib/pull/12156))
It is vacuously true for zero, as everything divides zero.

### [2022-02-20 00:00:55](https://github.com/leanprover-community/mathlib/commit/fa603fe)
feat(order/category/FinPartialOrder): The category of finite partial orders ([#11997](https://github.com/leanprover-community/mathlib/pull/11997))
Define `FinPartialOrder`, the category of finite partial orders with monotone functions.

### [2022-02-19 22:26:11](https://github.com/leanprover-community/mathlib/commit/5611533)
feat(analysis/normed_space/star/complex): real and imaginary part of an element of a star module ([#11811](https://github.com/leanprover-community/mathlib/pull/11811))
We introduce the real and imaginary parts of an element of a star module, and show that elements of the type can be decomposed into these two parts in the obvious way.

### [2022-02-19 21:14:08](https://github.com/leanprover-community/mathlib/commit/3777543)
feat(category_theory/isomorphism): two lemmas is_iso.of_iso_comp_left/right on isomorphisms ([#12056](https://github.com/leanprover-community/mathlib/pull/12056))

### [2022-02-19 19:27:37](https://github.com/leanprover-community/mathlib/commit/bc63071)
feat(algebra/is_prime_pow): dot notation for nat.prime ([#12145](https://github.com/leanprover-community/mathlib/pull/12145))

### [2022-02-19 19:27:36](https://github.com/leanprover-community/mathlib/commit/628e8fb)
doc(group_theory/coset): Mention "Lagrange's theorem" ([#12137](https://github.com/leanprover-community/mathlib/pull/12137))
Suggested here: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.E2.9C.94.20Lagrange's.20Theorem.20.28Group.20theory.29/near/272469211

### [2022-02-19 18:23:35](https://github.com/leanprover-community/mathlib/commit/e88badb)
feat(analysis/inner_product_space/pi_L2): Orthonormal basis ([#12060](https://github.com/leanprover-community/mathlib/pull/12060))
Added the structure orthonormal_basis and basic associated API
Renamed the previous definition orthonormal_basis in analysis/inner_product_space/projection to std_orthonormal_basis

### [2022-02-19 07:54:42](https://github.com/leanprover-community/mathlib/commit/518b5d2)
chore(topology/bases): golf a proof ([#12127](https://github.com/leanprover-community/mathlib/pull/12127))
Also add `function.injective_iff_pairwise_ne`.

### [2022-02-18 21:46:45](https://github.com/leanprover-community/mathlib/commit/213e2ed)
feat(algebra/group/pi): add pi.nsmul_apply ([#12122](https://github.com/leanprover-community/mathlib/pull/12122))
via to_additive

### [2022-02-18 21:46:43](https://github.com/leanprover-community/mathlib/commit/b3d0944)
feat(tactic/swap_var): name juggling, a weaker wlog ([#12006](https://github.com/leanprover-community/mathlib/pull/12006))

### [2022-02-18 19:52:47](https://github.com/leanprover-community/mathlib/commit/5f46dd0)
fix(category_theory/limits): improve inaccurate docstrings ([#12130](https://github.com/leanprover-community/mathlib/pull/12130))

### [2022-02-18 19:52:46](https://github.com/leanprover-community/mathlib/commit/7b6c407)
feat(number_theory/divisors): add `prod_div_divisors` and `sum_div_divisors` ([#12087](https://github.com/leanprover-community/mathlib/pull/12087))
Adds lemma `prod_div_divisors : ∏ d in n.divisors, f (n/d) = n.divisors.prod f` and `sum_div_divisors`.
Also proves `image_div_divisors_eq_divisors : image (λ (x : ℕ), n / x) n.divisors = n.divisors`
and `div_eq_iff_eq_of_dvd_dvd : n / x = n / y ↔ x = y` (where `n ≠ 0` and `x ∣ n` and `y ∣ n`)

### [2022-02-18 19:52:44](https://github.com/leanprover-community/mathlib/commit/33179f7)
refactor(topology/metric_space/completion): change namespace ([#12077](https://github.com/leanprover-community/mathlib/pull/12077))
Move lemmas about metric on `uniform_space.completion` from `metric.completion` namespace to `uniform_space.completion`.

### [2022-02-18 19:52:43](https://github.com/leanprover-community/mathlib/commit/18c3e3f)
feat(data/nat/fib): add that `fib` is sum of `nat.choose` along antidiagonal ([#12063](https://github.com/leanprover-community/mathlib/pull/12063))

### [2022-02-18 19:21:11](https://github.com/leanprover-community/mathlib/commit/ffc2bdf)
refactor(group_theory/abelianization): Define `commutator` in terms of `general_commutator` ([#11949](https://github.com/leanprover-community/mathlib/pull/11949))
It seems reasonable to define `commutator` in terms of `general_commutator`.

### [2022-02-18 18:09:38](https://github.com/leanprover-community/mathlib/commit/018c728)
refactor(ring_theory/fractional_ideal): rename lemmas for dot notation, add coe_pow ([#12080](https://github.com/leanprover-community/mathlib/pull/12080))
This replaces `fractional_ideal.fractional_mul` with `is_fractional.mul` and likewise for the other operations. The bundling was a distraction for the content of the lemmas anyway.

### [2022-02-18 18:09:37](https://github.com/leanprover-community/mathlib/commit/bcf8a6e)
feat(ring_theory/fractional_ideal): add coe_ideal lemmas ([#12073](https://github.com/leanprover-community/mathlib/pull/12073))

### [2022-02-18 16:58:17](https://github.com/leanprover-community/mathlib/commit/98643bc)
feat(algebra/big_operators/intervals): summation by parts ([#11814](https://github.com/leanprover-community/mathlib/pull/11814))
Add the "summation by parts" identity over intervals of natural numbers, as well as some helper lemmas.

### [2022-02-18 15:07:45](https://github.com/leanprover-community/mathlib/commit/3ca16d0)
feat(data/equiv): define `ring_equiv_class` ([#11977](https://github.com/leanprover-community/mathlib/pull/11977))
This PR applies the morphism class pattern to `ring_equiv`, producing a new `ring_equiv_class` extending `mul_equiv_class` and `add_equiv_class`. It also provides a `ring_equiv_class` instance for `alg_equiv`s.

### [2022-02-18 14:37:42](https://github.com/leanprover-community/mathlib/commit/223f149)
chore(algebra/star/self_adjoint): extract a lemma from `has_scalar` ([#12121](https://github.com/leanprover-community/mathlib/pull/12121))

### [2022-02-18 13:41:21](https://github.com/leanprover-community/mathlib/commit/aed97e0)
doc(analysis/normed/group/basic): add docstring explaining the "insert" name ([#12100](https://github.com/leanprover-community/mathlib/pull/12100))

### [2022-02-18 12:57:33](https://github.com/leanprover-community/mathlib/commit/3e6439c)
fix(category_theory/limits/shapes/images): make class a Prop ([#12119](https://github.com/leanprover-community/mathlib/pull/12119))

### [2022-02-18 11:05:58](https://github.com/leanprover-community/mathlib/commit/33b4e73)
refactor(topology/algebra): reorder imports ([#12089](https://github.com/leanprover-community/mathlib/pull/12089))
* move `mul_opposite.topological_space` and `units.topological_space` to a new file;
* import `mul_action` in `monoid`, not vice versa.
With this order of imports, we can reuse results about `has_continuous_smul` in lemmas about topological monoids.

### [2022-02-18 07:37:58](https://github.com/leanprover-community/mathlib/commit/77f264f)
feat(data/finset/basic): add lemma `filter_eq_empty_iff` ([#12104](https://github.com/leanprover-community/mathlib/pull/12104))
Add `filter_eq_empty_iff : (s.filter p = ∅) ↔ ∀ x ∈ s, ¬ p x`
We already have the right-to-left direction of this in `filter_false_of_mem`.

### [2022-02-18 05:49:20](https://github.com/leanprover-community/mathlib/commit/bb1b56c)
feat(algebra/indicator_function): smul lemmas for functions ([#12059](https://github.com/leanprover-community/mathlib/pull/12059))
And a few basic lemmas in `set/basic`.

### [2022-02-18 04:52:16](https://github.com/leanprover-community/mathlib/commit/17b3357)
feat(topology/algebra): generalize `has_continuous_smul` arguments to `has_continuous_const_smul` ([#11999](https://github.com/leanprover-community/mathlib/pull/11999))
This changes the majority of the downstream call-sites of the `const_smul` lemmas to only need the weaker typeclass.

### [2022-02-18 02:05:51](https://github.com/leanprover-community/mathlib/commit/b757206)
feat(linear_algebra/finite_dimensional): finrank_range_of_inj ([#12067](https://github.com/leanprover-community/mathlib/pull/12067))
The dimensions of the domain and range of an injective linear map are
equal.

### [2022-02-18 00:52:54](https://github.com/leanprover-community/mathlib/commit/59a183a)
feat(data/finset/locally_finite): add Ico_subset_Ico_union_Ico ([#11710](https://github.com/leanprover-community/mathlib/pull/11710))
This lemma extends the result for `set`s to `finset`s.

### [2022-02-17 22:59:24](https://github.com/leanprover-community/mathlib/commit/e93996c)
feat(topology/instances/discrete): instances for the discrete topology ([#11349](https://github.com/leanprover-community/mathlib/pull/11349))
Prove `first_countable_topology`, `second_countable_topology` and `order_topology` for the discrete topology under appropriate conditions like `encodable`, or being a linear order with `pred` and `succ`. These instances give in particular `second_countable_topology ℕ` and `order_topology ℕ`

### [2022-02-17 21:50:25](https://github.com/leanprover-community/mathlib/commit/6089f08)
feat(data/nat/totient): add Euler's product formula for totient function ([#11332](https://github.com/leanprover-community/mathlib/pull/11332))
Proving four versions of Euler's product formula for the totient function `φ`:
* `totient_eq_prod_factorization :  φ n = n.factorization.prod (λ p k, p ^ (k - 1) * (p - 1))`
* `totient_mul_prod_factors : φ n * ∏ p in n.factors.to_finset, p = n * ∏ p in n.factors.to_finset, (p - 1)`
* `totient_eq_div_factors_mul : φ n = n / (∏ p in n.factors.to_finset, p) * (∏ p in n.factors.to_finset, (p - 1))`
* `totient_eq_mul_prod_factors : (φ n : ℚ) = n * ∏ p in n.factors.to_finset, (1 - p⁻¹)`

### [2022-02-17 21:06:46](https://github.com/leanprover-community/mathlib/commit/19534b2)
feat(analysis/inner_product_space/basic) : `inner_map_self_eq_zero` ([#12065](https://github.com/leanprover-community/mathlib/pull/12065))
The main result here is:  If ⟪T x, x⟫_C = 0 for all x, then T = 0.
The proof uses a polarization identity.  Note that this is false
with R in place of C.  I am confident that my use of ring_nf is
not optimal, but I hope to learn from the cleanup process!

### [2022-02-17 22:00:06+01:00](https://github.com/leanprover-community/mathlib/commit/8b6901b)
Revert "feat(category_theory/limits): is_bilimit"
This reverts commit 8edfa75d79ad70c88dbae01ab6166dd8b1fd2ba0.

### [2022-02-17 21:56:42+01:00](https://github.com/leanprover-community/mathlib/commit/8edfa75)
feat(category_theory/limits): is_bilimit

### [2022-02-17 19:35:15](https://github.com/leanprover-community/mathlib/commit/aacc36c)
feat(group_theory/commensurable): Definition and lemmas about commensurability. ([#9545](https://github.com/leanprover-community/mathlib/pull/9545))
This defines commensurability for subgroups, proves this defines a transitive relation and then defines the commensurator subgroup. In doing so it also needs some lemmas about indices of subgroups and the definition of the conjugate of a subgroup by an element of the parent group.

### [2022-02-17 18:46:15](https://github.com/leanprover-community/mathlib/commit/8575f59)
feat(category_theory/limits): preservation of zero morphisms ([#12068](https://github.com/leanprover-community/mathlib/pull/12068))

### [2022-02-17 17:02:32](https://github.com/leanprover-community/mathlib/commit/c9e8c64)
chore(*): update to lean 3.39.2c ([#12102](https://github.com/leanprover-community/mathlib/pull/12102))

### [2022-02-17 17:02:31](https://github.com/leanprover-community/mathlib/commit/dcb2826)
feat(order/filter/basic): add eventually_eq.(smul/const_smul/sup/inf) ([#12101](https://github.com/leanprover-community/mathlib/pull/12101))

### [2022-02-17 15:34:44](https://github.com/leanprover-community/mathlib/commit/307711e)
feat(group_theory/general_commutator): subgroup.pi commutes with the general_commutator ([#11825](https://github.com/leanprover-community/mathlib/pull/11825))

### [2022-02-17 13:10:49](https://github.com/leanprover-community/mathlib/commit/b54f44f)
feat(data/matrix/notation): expansions of matrix multiplication for 2x2 and 3x3 ([#12088](https://github.com/leanprover-community/mathlib/pull/12088))
A clever way to generalize this would be to make a recursivedefinition of `mul` and `one` that's defeq to the desired `![...]` result and prove that's equal to the usual definition, but that doesn't help with actually writing the lemma statement, which is the tedious bit.

### [2022-02-17 12:16:09](https://github.com/leanprover-community/mathlib/commit/eb8d58d)
fix(topology/algebra/basic): remove duplicate lemma ([#12097](https://github.com/leanprover-community/mathlib/pull/12097))
This lemma duplicates the lemma of the same name in the root namespace, and should not be in this namespace in the first place.
The other half of [#12072](https://github.com/leanprover-community/mathlib/pull/12072), now that the dependent PR is merged.

### [2022-02-17 12:16:07](https://github.com/leanprover-community/mathlib/commit/4afd667)
feat(measure_theory/integral): add `integral_sum_measure` ([#12090](https://github.com/leanprover-community/mathlib/pull/12090))
Also add supporting lemmas about finite and infinite sums of measures.

### [2022-02-17 11:20:26](https://github.com/leanprover-community/mathlib/commit/20cf3ca)
feat(ring_theory/discriminant): add discr_eq_discr_of_to_matrix_coeff_is_integral ([#11994](https://github.com/leanprover-community/mathlib/pull/11994))
We add `discr_eq_discr_of_to_matrix_coeff_is_integral`: if `b` and `b'` are `ℚ`-basis of a number field `K` such that
`∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j` then
`discr ℚ b = discr ℚ b'`.

### [2022-02-17 10:43:57](https://github.com/leanprover-community/mathlib/commit/614758e)
feat(order/category/DistribLattice): The category of distributive lattices ([#12092](https://github.com/leanprover-community/mathlib/pull/12092))
Define `DistribLattice`, the category of distributive lattices.

### [2022-02-17 10:00:32](https://github.com/leanprover-community/mathlib/commit/58a3720)
feat(analysis/inner_product_space/pi_L2): `complex.isometry_of_orthonormal` ([#11970](https://github.com/leanprover-community/mathlib/pull/11970))
Add a definition for the isometry between `ℂ` and a two-dimensional
real inner product space given by a basis, and an associated `simp`
lemma for how this relates to `basis.map`.
This definition is just the composition of two existing definitions,
`complex.isometry_euclidean` and (the inverse of)
`basis.isometry_euclidean_of_orthonormal`.  However, it's still useful
to have it as a single definition when using it to define and prove
basic properties of oriented angles (in an oriented two-dimensional
real inner product space), to keep definitions and terms in proofs
simpler and to avoid tactics such as `simp` or `rw` rearranging things
inside this definition when not wanted (almost everything just needs
to use some isometry between these two spaces without caring about the
details of how it's defined, so it seems best to use a single `def`
for this isometry, and on the rare occasions where the details of how
it's defined matter, prove specific lemmas about the required
properties).

### [2022-02-17 07:43:58](https://github.com/leanprover-community/mathlib/commit/a355d88)
feat(topology/metric_space/gluing): metric space structure on sigma types ([#11965](https://github.com/leanprover-community/mathlib/pull/11965))
We define a (noncanonical) metric space structure on sigma types (aka arbitrary disjoint unions), as follows. Each piece is isometrically embedded in the union, while for `x` and `y` in different pieces their distance is `dist x x0 + 1 + dist y0 y`, where `x0` and `y0` are basepoints in the respective parts. This is *not* registered as an instance.
This definition was already there for sum types (aka disjoint union of two pieces). We also fix this existing definition to avoid `inhabited` assumptions.

### [2022-02-17 06:05:54](https://github.com/leanprover-community/mathlib/commit/09960ea)
feat(algebra/group_power/basic): `two_zsmul` ([#12094](https://github.com/leanprover-community/mathlib/pull/12094))
Mark `zpow_two` with `@[to_additive two_zsmul]`.  I see no apparent
reason for this result not to use `to_additive`, and I found I had a
use for the additive version.

### [2022-02-17 05:32:27](https://github.com/leanprover-community/mathlib/commit/1831d85)
feat(category_theory/limits): Preserves epi of preserves pushout. ([#12084](https://github.com/leanprover-community/mathlib/pull/12084))

### [2022-02-17 00:34:41](https://github.com/leanprover-community/mathlib/commit/84f12be)
chore(algebra/star/self_adjoint): improve definitional unfolding of pow and div ([#12085](https://github.com/leanprover-community/mathlib/pull/12085))

### [2022-02-17 00:34:40](https://github.com/leanprover-community/mathlib/commit/834fd30)
feat(topology/continuous_function/algebra): generalize algebra instances ([#12055](https://github.com/leanprover-community/mathlib/pull/12055))
This adds:
* some missing instances in the algebra hierarchy (`comm_semigroup`, `mul_one_class`, `mul_zero_class`, `monoid_with_zero`, `comm_monoid_with_zero`, `comm_semiring`).
* finer-grained scalar action instances, notably none of which require `topological_space R` any more, as they only need `has_continuous_const_smul R M` instead of `has_continuous_smul R M`.
* continuity lemmas about `zpow` on groups and `zsmul` on additive groups (copied directly from the lemmas about `pow` on monoids), which are used to avoid diamonds in the int-action. In order to make room for these, the lemmas about `zpow` on groups with zero have been renamed to `zpow₀`, which is consistent with how the similar clash with `inv` is solved.
* a few lemmas about `mk_of_compact` since an existing proof was broken by `refl` closing the goal earlier than before.

### [2022-02-17 00:34:39](https://github.com/leanprover-community/mathlib/commit/27df8a0)
feat(topology/instances/rat): some facts about topology on `rat` ([#11832](https://github.com/leanprover-community/mathlib/pull/11832))
* `ℚ` is a totally disconnected space;
* `cocompact  ℚ` is not a countably generated filter;
* hence, `alexandroff  ℚ` is not a first countable topological space.

### [2022-02-16 22:44:23](https://github.com/leanprover-community/mathlib/commit/7dae87f)
feat(topology/metric_space/basic): ext lemmas for metric spaces ([#12070](https://github.com/leanprover-community/mathlib/pull/12070))
Also add a few results in `metric_space.basic`:
* A decreasing intersection of closed sets with diameter tending to `0` is nonempty in a complete space
* new constructions of metric spaces by pulling back structures (and adjusting definitional equalities)
* fixing `metric_space empty` and `metric_space punit` to make sure the uniform structure is definitionally the right one.

### [2022-02-16 22:44:22](https://github.com/leanprover-community/mathlib/commit/5db1ae4)
feat(analysis/specific_limits): useful specializations of some lemmas ([#12069](https://github.com/leanprover-community/mathlib/pull/12069))

### [2022-02-16 22:44:21](https://github.com/leanprover-community/mathlib/commit/1bf4181)
feat(data/equiv/{basic,mul_equiv)}: add Pi_subsingleton ([#12040](https://github.com/leanprover-community/mathlib/pull/12040))

### [2022-02-16 22:44:20](https://github.com/leanprover-community/mathlib/commit/b2aaece)
feat(field_theory/is_alg_closed): alg closed and char p implies perfect ([#12037](https://github.com/leanprover-community/mathlib/pull/12037))

### [2022-02-16 21:09:23](https://github.com/leanprover-community/mathlib/commit/bd67e85)
feat(algebra/char_p/basic): add ring_char_of_prime_eq_zero ([#12024](https://github.com/leanprover-community/mathlib/pull/12024))
The characteristic of a ring is `p` if `p` is a prime and `p = 0` in the ring.

### [2022-02-16 21:09:22](https://github.com/leanprover-community/mathlib/commit/0fe91d0)
feat(data/part): Instance lemmas ([#12001](https://github.com/leanprover-community/mathlib/pull/12001))
Lemmas about `part` instances, proved by `tidy`

### [2022-02-16 19:16:09](https://github.com/leanprover-community/mathlib/commit/b395a67)
chore(data/finsupp/pointwise): golf using injective lemmas ([#12086](https://github.com/leanprover-community/mathlib/pull/12086))

### [2022-02-16 19:16:08](https://github.com/leanprover-community/mathlib/commit/0ab9b5f)
chore(topology/continuous_function/bounded): golf algebra instances ([#12082](https://github.com/leanprover-community/mathlib/pull/12082))
Using the `function.injective.*` lemmas saves a lot of proofs.
This also adds a few missing lemmas about `one` that were already present for `zero`.

### [2022-02-16 19:16:06](https://github.com/leanprover-community/mathlib/commit/d86ce02)
chore(ring_theory/fractional_ideal): golf ([#12076](https://github.com/leanprover-community/mathlib/pull/12076))

### [2022-02-16 19:16:04](https://github.com/leanprover-community/mathlib/commit/15c6eee)
feat(logic/basic): Better congruence lemmas for `or`, `or_or_or_comm` ([#12004](https://github.com/leanprover-community/mathlib/pull/12004))
Prove `or_congr_left` and `or_congr_right` and rename the existing `or_congr_left`/`or_congr_right` to `or_congr_left'`/`or_congr_right'` to match the `and` lemmas. Also prove `or_rotate`, `or.rotate`, `or_or_or_comm` based on `and` again.

### [2022-02-16 19:16:03](https://github.com/leanprover-community/mathlib/commit/5e3d465)
feat(category_theory/category/PartialFun): The category of types with partial functions ([#11866](https://github.com/leanprover-community/mathlib/pull/11866))
Define `PartialFun`, the category of types with partial functions, and show its equivalence with `Pointed`.

### [2022-02-16 17:16:29](https://github.com/leanprover-community/mathlib/commit/3c78d00)
docs(group_theory/semidirect_product): fix typo in module docs ([#12083](https://github.com/leanprover-community/mathlib/pull/12083))

### [2022-02-16 17:16:27](https://github.com/leanprover-community/mathlib/commit/3107a83)
feat(algebra/char_p/basic): Generalize `frobenius_inj`. ([#12079](https://github.com/leanprover-community/mathlib/pull/12079))

### [2022-02-16 17:16:26](https://github.com/leanprover-community/mathlib/commit/0eb160a)
feat(data/finset/basic): When `insert` is injective and other lemmas ([#11982](https://github.com/leanprover-community/mathlib/pull/11982))
* `insert`/`cons` lemmas for `finset` and `multiset`
* `has_ssubset` instance for `multiset`
* `finset.sdiff_nonempty`
* `disjoint.of_image_finset`, `finset.disjoint_image`, `finset.disjoint_map`
* `finset.exists_eq_insert_iff`
* `mem` lemmas
* change `pred` to `- 1` into the statement of `finset.card_erase_of_mem`

### [2022-02-16 17:16:25](https://github.com/leanprover-community/mathlib/commit/6bcb12c)
feat(order/antisymmetrization): Turning a preorder into a partial order ([#11728](https://github.com/leanprover-community/mathlib/pull/11728))
Define `antisymmetrization`, the quotient of a preorder by the "less than both ways" relation. This effectively turns a preorder into a partial order, and this operation is functorial as shown by the new `Preorder_to_PartialOrder`.

### [2022-02-16 16:11:48](https://github.com/leanprover-community/mathlib/commit/8a286af)
chore(topology/algebra/mul_action): rename type variables ([#12020](https://github.com/leanprover-community/mathlib/pull/12020))

### [2022-02-16 14:23:54](https://github.com/leanprover-community/mathlib/commit/e815675)
chore(topology/algebra/module/basic): remove two duplicate lemmas ([#12072](https://github.com/leanprover-community/mathlib/pull/12072))
`continuous_linear_map.continuous_nsmul` is nothing to do with `continuous_linear_map`s, and is the same as `continuous_nsmul`, but the latter doesn't require commutativity. There is no reason to keep the former.
This lemma was added in [#7084](https://github.com/leanprover-community/mathlib/pull/7084), but probably got missed due to how large that PR had to be.
We can't remove `continuous_linear_map.continuous_zsmul` until [#12055](https://github.com/leanprover-community/mathlib/pull/12055) is merged, as there is currently no `continuous_zsmul` in the root namespace.

### [2022-02-16 14:23:53](https://github.com/leanprover-community/mathlib/commit/a26d17f)
feat(mv_polynomial/supported): restrict_to_vars ([#12043](https://github.com/leanprover-community/mathlib/pull/12043))

### [2022-02-16 14:23:52](https://github.com/leanprover-community/mathlib/commit/62297cf)
feat(analysis/complex/cauchy_integral, analysis/analytic/basic): entire functions have power series with infinite radius of convergence ([#11948](https://github.com/leanprover-community/mathlib/pull/11948))
This proves that a formal multilinear series `p` which represents a function `f : 𝕜 → E` on a ball of every positive radius, then `p` represents `f` on a ball of infinite radius. Consequently, it is shown that if `f : ℂ → E` is differentiable everywhere, then `cauchy_power_series f z R` represents `f` as a power series centered at `z` in the entirety of `ℂ`, regardless of `R` (assuming `0 < R`).
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896)

### [2022-02-16 13:36:23](https://github.com/leanprover-community/mathlib/commit/22fdf47)
chore(linear_algebra/affine_space/affine_map,topology/algebra/continuous_affine_map): generalized scalar instances ([#11978](https://github.com/leanprover-community/mathlib/pull/11978))
The main result here is that `distrib_mul_action`s are available on affine maps to a module, inherited from their codomain.
This fixes a diamond in the `int`-action that was already present for `int`-affine maps, and prevents the new `nat`-action introducing a diamond.
This also removes the requirement for `R` to be a `topological_space` in the scalar action for `continuous_affine_map` by using `has_continuous_const_smul` instead of `has_continuous_smul`.

### [2022-02-16 11:53:41](https://github.com/leanprover-community/mathlib/commit/32beebb)
feat(algebra/order/monoid): add simp lemmas ([#12030](https://github.com/leanprover-community/mathlib/pull/12030))

### [2022-02-16 11:53:40](https://github.com/leanprover-community/mathlib/commit/7542119)
refactor(algebra/group/basic): add extra typeclasses for negation ([#11960](https://github.com/leanprover-community/mathlib/pull/11960))
The new typeclasses are:
* `has_involutive_inv R`, stating that `(r⁻¹)⁻¹ = r`  
  (instances: `group`, `group_with_zero`, `ennreal`, `set`, `submonoid`)
* `has_involutive_neg R`, stating that `- -r = r`
  (instances: `add_group`, `ereal`, `module.ray`, `ray_vector`, `set`, `add_submonoid`, `jordan_decomposition`)
* `has_distrib_neg R`, stating that `-a * b = a * -b = -(a * b)`
  (instances: `ring`, `units`, `unitary`, `special_linear_group`, `GL_pos`)
While the original motivation only concerned the two `neg` typeclasses, the `to_additive` machinery forced the introduction of `has_involutive_inv`, which turned out to be used in more places than expected.
Adding these typeclases removes a large number of specialized `units R` lemmas as the lemmas about `R` now match themselves. A surprising number of lemmas elsewhere in the library can also be removed. The removed lemmas are:
* Lemmas about `units` (replaced by `units.has_distrib_neg`):
  * `units.neg_one_pow_eq_or`
  * `units.neg_pow`
  * `units.neg_pow_bit0`
  * `units.neg_pow_bit1`
  * `units.neg_sq`
  * `units.neg_inv` (now `inv_neg'` for arbitrary groups with distributive negation)
  * `units.neg_neg`
  * `units.neg_mul`
  * `units.mul_neg`
  * `units.neg_mul_eq_neg_mul`
  * `units.neg_mul_eq_mul_neg`
  * `units.neg_mul_neg`
  * `units.neg_eq_neg_one_mul`
  * `units.mul_neg_one`
  * `units.neg_one_mul`
  * `semiconj_by.units_neg_right`
  * `semiconj_by.units_neg_right_iff`
  * `semiconj_by.units_neg_left`
  * `semiconj_by.units_neg_left_iff`
  * `semiconj_by.units_neg_one_right`
  * `semiconj_by.units_neg_one_left`
  * `commute.units_neg_right`
  * `commute.units_neg_right_iff`
  * `commute.units_neg_left`
  * `commute.units_neg_left_iff`
  * `commute.units_neg_one_right`
  * `commute.units_neg_one_left`
* Lemmas about groups with zero (replaced by `group_with_zero.to_has_involutive_neg`):
  * `inv_inv₀`
  * `inv_involutive₀`
  * `inv_injective₀`
  * `inv_eq_iff` (now shared with the `inv_eq_iff_inv_eq` group lemma)
  * `eq_inv_iff` (now shared with the `eq_inv_iff_eq_inv` group lemma)
  * `equiv.inv₀`
  * `measurable_equiv.inv₀`
* Lemmas about `ereal` (replaced by `ereal.has_involutive_neg`):
  * `ereal.neg_neg`
  * `ereal.neg_inj`
  * `ereal.neg_eq_neg_iff`
  * `ereal.neg_eq_iff_neg_eq`
* Lemmas about `ennreal` (replaced by `ennreal.has_involutive_inv`):
  * `ereal.inv_inv`
  * `ereal.inv_involutive`
  * `ereal.inv_bijective`
  * `ereal.inv_eq_inv`
* Other lemmas:
  * `ray_vector.neg_neg`
  * `module.ray.neg_neg`
  * `module.ray.neg_involutive`
  * `module.ray.eq_neg_iff_eq_neg`
  * `set.inv_inv`
  * `set.neg_neg`
  * `submonoid.inv_inv`
  * `add_submonoid.neg_neg`
As a bonus, this provides the group `unitary R`  with a negation operator and all the lemmas listed for `units` above.
For now this doesn't attempt to unify `units.neg_smul` and `neg_smul`.

### [2022-02-16 11:53:38](https://github.com/leanprover-community/mathlib/commit/d24792c)
feat(model_theory/terms_and_formulas): Define satisfiability and semantic equivalence of formulas ([#11928](https://github.com/leanprover-community/mathlib/pull/11928))
Defines satisfiability of theories
Provides a default model of a satisfiable theory
Defines semantic (logical) equivalence of formulas

### [2022-02-16 11:19:27](https://github.com/leanprover-community/mathlib/commit/6dfb24c)
feat(algebra/star/self_adjoint): define skew-adjoint elements of a star additive group ([#12013](https://github.com/leanprover-community/mathlib/pull/12013))
This defines the skew-adjoint elements of a star additive group, as the additive subgroup that satisfies `star x = -x`. The development is analogous to that of `self_adjoint`.

### [2022-02-16 09:30:11](https://github.com/leanprover-community/mathlib/commit/06e6b35)
feat(analysis/special_functions/trigonometric/angle): `coe_pi_add_coe_pi` ([#12064](https://github.com/leanprover-community/mathlib/pull/12064))
Add another `simp` lemma to those expressing in different ways that 2π
is zero as a `real.angle`.

### [2022-02-16 07:45:37](https://github.com/leanprover-community/mathlib/commit/daf2989)
feat(algebra/big_operators): formula for product of sums to n+1 ([#12042](https://github.com/leanprover-community/mathlib/pull/12042))

### [2022-02-16 07:16:02](https://github.com/leanprover-community/mathlib/commit/6a09cd0)
chore(topology/uniform_space): use weaker TC assumptions ([#12066](https://github.com/leanprover-community/mathlib/pull/12066))
We don't need `[uniform_space β]` to prove
`uniform_space.completion.ext`.

### [2022-02-15 20:57:33](https://github.com/leanprover-community/mathlib/commit/eeb2956)
feat(topology/algebra): relax some `Type*` assumptions to `Sort*` ([#12058](https://github.com/leanprover-community/mathlib/pull/12058))
When working on [#11720](https://github.com/leanprover-community/mathlib/pull/11720) I forgot that we have to deal with Prop-indexed infimums quite often, so this PR fixes that.

### [2022-02-15 19:34:16](https://github.com/leanprover-community/mathlib/commit/b0fe972)
feat (analysis/normed_space/spectrum): prove Gelfand's formula for the spectral radius ([#11916](https://github.com/leanprover-community/mathlib/pull/11916))
This establishes Gelfand's formula for the spectral radius in a complex Banach algebra `A`, namely that the sequence of n-th roots of the norms of n-th powers of any element tends to its spectral radius. Some results which hold in more generality concerning the function `z ↦ ring.inverse (1 - z • a)` are also given. In particular, this function is differentiable on the disk with radius the reciprocal of the spectral radius, and it has a power series on the ball with radius equal to the reciprocal of the norm of `a : A`.
Currently, the version of Gelfand's formula which appears here includes an assumption that `A` is second countable, which won't hold in general unless `A` is separable. This is not a true (i.e., mathematical) limitation, but a consequence of the current implementation of Bochner integrals in mathlib (which are an essential feature in the proof of Gelfand's formula because of its use of the Cauchy integral formula). When Bochner integrals are refactored, this type class assumption can be dropped.
- [x] depends on: [#11869](https://github.com/leanprover-community/mathlib/pull/11869)
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896) 
- [x] depends on: [#11915](https://github.com/leanprover-community/mathlib/pull/11915)

### [2022-02-15 19:34:15](https://github.com/leanprover-community/mathlib/commit/d76ac2e)
feat(category_theory): separators and detectors ([#11880](https://github.com/leanprover-community/mathlib/pull/11880))

### [2022-02-15 19:04:10](https://github.com/leanprover-community/mathlib/commit/ff2c9dc)
feat(combinatorics/simple_graph/connectivity): add functions to split walks and to create paths ([#11095](https://github.com/leanprover-community/mathlib/pull/11095))
This is chunk 3 of [#8737](https://github.com/leanprover-community/mathlib/pull/8737). Introduces `take_until` and `drop_until` to split walks at a vertex, `rotate` to rotate cycles, and `to_path` to remove internal redundancy from a walk to create a path with the same endpoints.
This also defines a bundled `path` type for `is_path` since `G.path u v` is a useful type.

### [2022-02-15 17:47:31](https://github.com/leanprover-community/mathlib/commit/5027b28)
move(data/nat/choose/bounds): Move from `combinatorics.choose.bounds` ([#12051](https://github.com/leanprover-community/mathlib/pull/12051))
This file fits better with all other files about `nat.choose`. My bad for originally proposing it goes alone under `combinatorics`.

### [2022-02-15 17:47:30](https://github.com/leanprover-community/mathlib/commit/52aaf17)
feat(data/{list,multiset,finset}/nat_antidiagonal): add lemmas to remove elements from head and tail of antidiagonal ([#12028](https://github.com/leanprover-community/mathlib/pull/12028))
Also lowered `finset.nat.map_swap_antidiagonal` down to `list` through `multiset`.

### [2022-02-15 15:53:29](https://github.com/leanprover-community/mathlib/commit/c0c673a)
feat(data/equiv,logic/embedding): add `can_lift` instances ([#12049](https://github.com/leanprover-community/mathlib/pull/12049))

### [2022-02-15 15:52:59](https://github.com/leanprover-community/mathlib/commit/c686fcc)
feat(analysis/specific_limits): add `tendsto_zero_smul_of_tendsto_zero_of_bounded` ([#12039](https://github.com/leanprover-community/mathlib/pull/12039))

### [2022-02-15 15:52:56](https://github.com/leanprover-community/mathlib/commit/6e64492)
feat(ring_theory/multiplicity): Equality of `factorization`, `multiplicity`, and `padic_val_nat` ([#12033](https://github.com/leanprover-community/mathlib/pull/12033))
Proves `multiplicity_eq_factorization : multiplicity p n = n.factorization p` for prime `p` and `n ≠ 0` and uses this to golf the proof of `padic_val_nat_eq_factorization : padic_val_nat p n = n.factorization p`.

### [2022-02-15 15:52:53](https://github.com/leanprover-community/mathlib/commit/9307f5b)
feat(topology/order/lattice): add a consequence of the continuity of sup/inf ([#12003](https://github.com/leanprover-community/mathlib/pull/12003))
Prove this lemma and its `inf` counterpart:
```lean
lemma filter.tendsto.sup_right_nhds {ι β} [topological_space β] [has_sup β] [has_continuous_sup β]
  {l : filter ι} {f g : ι → β} {x y : β} (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
```
The name is `sup_right_nhds` because `sup` already exists, and is about a supremum over the filters on the left in the tendsto.
The proofs of `tendsto_prod_iff'` and `prod.tendsto_iff` were written by  Patrick Massot.

### [2022-02-15 15:52:52](https://github.com/leanprover-community/mathlib/commit/60b77a7)
feat(analysis/special_functions/complex/circle): `real.angle.exp_map_circle` lemmas ([#11969](https://github.com/leanprover-community/mathlib/pull/11969))
Add four more `simp` lemmas about `real.angle.exp_map_circle`:
`exp_map_circle_zero`, `exp_map_circle_neg`, `exp_map_circle_add` and
`arg_exp_map_circle`.

### [2022-02-15 15:52:49](https://github.com/leanprover-community/mathlib/commit/0c33309)
feat(number_theory/zsqrtd/basic): add some lemmas ([#11964](https://github.com/leanprover-community/mathlib/pull/11964))

### [2022-02-15 15:52:48](https://github.com/leanprover-community/mathlib/commit/3d1354c)
feat(set_theory/ordinal_arithmetic): Suprema of functions with the same range are equal ([#11910](https://github.com/leanprover-community/mathlib/pull/11910))

### [2022-02-15 15:52:46](https://github.com/leanprover-community/mathlib/commit/721bace)
refactor(set_theory/ordinal_arithmetic): `omin` → `Inf` ([#11867](https://github.com/leanprover-community/mathlib/pull/11867))
We remove the redundant `omin` in favor of `Inf`. We also introduce a `conditionally_complete_linear_order_bot` instance on `cardinals`, and golf a particularly messy proof.

### [2022-02-15 15:52:45](https://github.com/leanprover-community/mathlib/commit/9acc1d4)
feat(model_theory/finitely_generated): Finitely generated and countably generated (sub)structures ([#11857](https://github.com/leanprover-community/mathlib/pull/11857))
Defines `substructure.fg` and `Structure.fg` to indicate when (sub)structures are finitely generated
Defines `substructure.cg` and `Structure.cg` to indicate when (sub)structures are countably generated

### [2022-02-15 15:52:44](https://github.com/leanprover-community/mathlib/commit/41dd6d8)
feat(data/nat/modeq): add modeq and dvd lemmas from Apostol Chapter 5 ([#11787](https://github.com/leanprover-community/mathlib/pull/11787))
Various lemmas about `modeq` from Chapter 5 of Apostol (1976) Introduction to Analytic Number Theory:
* `mul_left_iff` and `mul_right_iff`: Apostol, Theorem 5.3
* `dvd_iff_of_modeq_of_dvd`: Apostol, Theorem 5.5
* `gcd_eq_of_modeq`: Apostol, Theorem 5.6
* `eq_of_modeq_of_abs_lt`: Apostol, Theorem 5.7
* `modeq_cancel_left_div_gcd`: Apostol, Theorem 5.4; plus other cancellation lemmas following from this.

### [2022-02-15 14:39:56](https://github.com/leanprover-community/mathlib/commit/b0508f3)
feat(topology/uniform/uniform_embedding): a sum of two complete spaces is complete ([#11971](https://github.com/leanprover-community/mathlib/pull/11971))

### [2022-02-15 14:39:55](https://github.com/leanprover-community/mathlib/commit/77ca1ed)
feat(order/category/Lattice): The category of lattices ([#11968](https://github.com/leanprover-community/mathlib/pull/11968))
Define `Lattice`, the category of lattices with lattice homs.

### [2022-02-15 12:59:13](https://github.com/leanprover-community/mathlib/commit/5bcffd9)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11786](https://github.com/leanprover-community/mathlib/pull/11786))
Lemmas about the norm of `ζ - 1`.
From flt-regular.
- [x] depends on: [#11941](https://github.com/leanprover-community/mathlib/pull/11941)

### [2022-02-15 12:59:12](https://github.com/leanprover-community/mathlib/commit/a2d7b55)
feat(order/complete_boolean_algebra): Frames ([#11709](https://github.com/leanprover-community/mathlib/pull/11709))
Define the order theoretic `order.frame` and `order.coframe` and insert them between `complete_lattice` and `complete_distrib_lattice`.

### [2022-02-15 12:30:09](https://github.com/leanprover-community/mathlib/commit/440e6b3)
feat(topology/algebra/module/locally_convex): define locally convex spaces ([#11859](https://github.com/leanprover-community/mathlib/pull/11859))

### [2022-02-15 11:12:39](https://github.com/leanprover-community/mathlib/commit/c5578f9)
feat(group_theory/nilpotent): products of nilpotent groups ([#11827](https://github.com/leanprover-community/mathlib/pull/11827))

### [2022-02-15 08:27:11](https://github.com/leanprover-community/mathlib/commit/f12b3d9)
feat(topology/algebra): weaken typeclasses to only require `has_continuous_const_smul` ([#11995](https://github.com/leanprover-community/mathlib/pull/11995))
This changes all the continuity-based `const_smul` lemmas to only require `has_continuous_const_smul` rather than `has_continuous_smul`. It does not attempt to  propagate the changes out of this file.
Four new instances are added in `const_mul_action.lean` for `has_continuous_const_smul`: `mul_opposite`, `prod`, `pi`, and `units`; all copied from the corresponding `has_continuous_smul` instance in `mul_action.lean`.
Presumably these lemmas existed before this typeclass did.
At any rate, the connection was less obvious until the rename a few days ago in [#11940](https://github.com/leanprover-community/mathlib/pull/11940).

### [2022-02-15 06:34:35](https://github.com/leanprover-community/mathlib/commit/f1334b9)
chore(category_theory/triangulated/rotate): optimizing some proofs ([#12031](https://github.com/leanprover-community/mathlib/pull/12031))
Removes some non-terminal `simp`s; replaces some `simp`s by `simp only [...]` and `rw`.
Compilation time dropped from 1m40s to 1m05s on my machine.

### [2022-02-15 05:21:51](https://github.com/leanprover-community/mathlib/commit/4c76eac)
chore(probability_theory/*): Rename folder  ([#11989](https://github.com/leanprover-community/mathlib/pull/11989))
Rename `probability_theory` to `probability`.

### [2022-02-15 02:51:23](https://github.com/leanprover-community/mathlib/commit/430faa9)
chore(scripts): update nolints.txt ([#12048](https://github.com/leanprover-community/mathlib/pull/12048))
I am happy to remove some nolints for you!

### [2022-02-15 02:21:36](https://github.com/leanprover-community/mathlib/commit/a1283d0)
feat(analysis/inner_product_space/adjoint): `is_self_adjoint_iff_eq_a… ([#12047](https://github.com/leanprover-community/mathlib/pull/12047))
…djoint`
A self-adjoint linear map is equal to its adjoint.

### [2022-02-15 01:27:49](https://github.com/leanprover-community/mathlib/commit/92ac8ff)
feat(analysis/special_functions/complex/arg): `arg_coe_angle_eq_iff` ([#12017](https://github.com/leanprover-community/mathlib/pull/12017))
Add a lemma that `arg` of two numbers coerced to `real.angle` is equal
if and only if `arg` is equal.

### [2022-02-14 23:41:27](https://github.com/leanprover-community/mathlib/commit/5dc720d)
chore(number_theory/padics/padic_norm): golf `prod_pow_prime_padic_val_nat` ([#12034](https://github.com/leanprover-community/mathlib/pull/12034))
A todo comment said "this proof can probably be golfed with `factorization` stuff"; it turns out that indeed it can be. :)

### [2022-02-14 21:58:15](https://github.com/leanprover-community/mathlib/commit/f9bac45)
chore(category_theory/linear/yoneda): Removing some slow uses of `obviously` ([#11979](https://github.com/leanprover-community/mathlib/pull/11979))
Providing explicit proofs for `map_id'` and `map_comp'` rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Suggested by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)

### [2022-02-14 21:58:14](https://github.com/leanprover-community/mathlib/commit/efdce09)
refactor(topology/constructions): turn `cofinite_topology` into a type synonym ([#11967](https://github.com/leanprover-community/mathlib/pull/11967))
Instead of `cofinite_topology α : topological_space α`, define
`cofinite_topology α := α` with an instance
`topological_space (cofinite_topology α) := (old definition)`.
This way we can talk about cofinite topology without using `@` all
over the place.
Also move `homeo_of_equiv_compact_to_t2.t1_counterexample` to
`topology.alexandroff` and prove it for `alexandroff ℕ` and
`cofinite_topology (alexandroff ℕ)`.

### [2022-02-14 21:58:13](https://github.com/leanprover-community/mathlib/commit/ec11e5f)
feat(algebra/covariant_and_contravariant): covariance and monotonicity ([#11815](https://github.com/leanprover-community/mathlib/pull/11815))
Some simple lemmas about monotonicity and covariant operators. Proves things like `monotone f → monotone (λ n, f (3 + n))` by library search.

### [2022-02-14 20:17:46](https://github.com/leanprover-community/mathlib/commit/4ba8334)
doc(number_theory/cyclotomic/gal): fix typo ([#12038](https://github.com/leanprover-community/mathlib/pull/12038))

### [2022-02-14 20:17:44](https://github.com/leanprover-community/mathlib/commit/263833c)
feat(data/nat/factorization): add `le_of_mem_factorization` ([#12032](https://github.com/leanprover-community/mathlib/pull/12032))
`le_of_mem_factors`: every factor of `n` is `≤ n`
`le_of_mem_factorization`: everything in `n.factorization.support` is `≤ n`

### [2022-02-14 20:17:42](https://github.com/leanprover-community/mathlib/commit/1a3c069)
chore(data/equiv/set): more lemmas about prod ([#12022](https://github.com/leanprover-community/mathlib/pull/12022))
Note we don't need the `symm` lemmas for `prod.comm`, since `prod.comm` is involutive

### [2022-02-14 18:40:35](https://github.com/leanprover-community/mathlib/commit/583ea58)
feat(data/list/big_operators): add `list.prod_map_mul` ([#12029](https://github.com/leanprover-community/mathlib/pull/12029))
This is an analogue of the corresponding lemma `multiset.prod_map_mul`.

### [2022-02-14 14:46:55](https://github.com/leanprover-community/mathlib/commit/199e8ca)
feat(algebra/star/self_adjoint): generalize scalar action instances ([#12021](https://github.com/leanprover-community/mathlib/pull/12021))
The `distrib_mul_action` instance did not require the underlying space to be a module.

### [2022-02-14 14:46:54](https://github.com/leanprover-community/mathlib/commit/5166aaa)
feat(analysis/normed_space/linear_isometry): `trans_one`, `one_trans`, `refl_mul`, `mul_refl` ([#12016](https://github.com/leanprover-community/mathlib/pull/12016))
Add variants of the `linear_isometry_equiv.trans_refl` and
`linear_isometry_equiv.refl_trans` `simp` lemmas where `refl` is given
as `1`.  (`one_def` isn't a `simp` lemma in either direction, since
either `refl` or `1` could be the appropriate simplest form depending
on the context, but it seems clear these expressions involving `trans`
with `1` are still appropriate to simplify.)
Also add corresponding `refl_mul` and `mul_refl`.

### [2022-02-14 12:13:11](https://github.com/leanprover-community/mathlib/commit/d33792e)
feat(data/nat/factorization): add lemma `factorization_gcd` ([#11605](https://github.com/leanprover-community/mathlib/pull/11605))
For positive `a` and `b`, `(gcd a b).factorization = a.factorization ⊓ b.factorization`; i.e. the power of prime `p` in `gcd a b` is the minimum of its powers in `a` and `b`.  This is Theorem 1.12 in Apostol (1976) Introduction to Analytic Number Theory.

### [2022-02-14 10:22:27](https://github.com/leanprover-community/mathlib/commit/132ea05)
docs(computability/partrec_code): add docs ([#11929](https://github.com/leanprover-community/mathlib/pull/11929))

### [2022-02-14 10:22:26](https://github.com/leanprover-community/mathlib/commit/dce5dd4)
feat(order/well_founded, set_theory/ordinal_arithmetic): `eq_strict_mono_iff_eq_range` ([#11882](https://github.com/leanprover-community/mathlib/pull/11882))
Two strict monotonic functions with well-founded domains are equal iff their ranges are. We use this to golf `eq_enum_ord`.

### [2022-02-14 08:41:45](https://github.com/leanprover-community/mathlib/commit/a87d431)
feat(topology/algebra): add `@[to_additive]` to some lemmas ([#12018](https://github.com/leanprover-community/mathlib/pull/12018))
* rename `embed_product` to `units.embed_product`, add `add_units.embed_product`;
* add additive versions to lemmas about topology on `units M`;
* add `add_opposite.topological_space` and `add_opposite.has_continuous_add`;
* move `continuous_op` and `continuous_unop` to the `mul_opposite` namespace, add additive versions.

### [2022-02-14 08:04:35](https://github.com/leanprover-community/mathlib/commit/2ceacc1)
feat(measure_theory/measure): more lemmas about `null_measurable_set`s ([#12019](https://github.com/leanprover-community/mathlib/pull/12019))

### [2022-02-14 07:20:08](https://github.com/leanprover-community/mathlib/commit/25ebf41)
chore(analysis): move some code ([#12008](https://github.com/leanprover-community/mathlib/pull/12008))
Move the code that doesn't rely on `normed_space` from
`analysis.normed_space.add_torsor` to
`analysis.normed.group.add_torsor`.

### [2022-02-14 06:18:50](https://github.com/leanprover-community/mathlib/commit/26fd61c)
feat(analysis/complex/isometry): `rotation_trans` ([#12015](https://github.com/leanprover-community/mathlib/pull/12015))
Add a `simp` lemma about the composition of two rotations.

### [2022-02-14 06:18:49](https://github.com/leanprover-community/mathlib/commit/77dfac2)
feat(order/filter/bases): basis of infimum of filters ([#11855](https://github.com/leanprover-community/mathlib/pull/11855))

### [2022-02-14 04:42:39](https://github.com/leanprover-community/mathlib/commit/6550cba)
feat(order/partition/finpartition): Finite partitions ([#9795](https://github.com/leanprover-community/mathlib/pull/9795))
This defines finite partitions along with quite a few constructions,

### [2022-02-13 20:36:13](https://github.com/leanprover-community/mathlib/commit/f91a32d)
feat(data/nat/factorization): add lemma `prod_prime_factors_dvd` ([#11572](https://github.com/leanprover-community/mathlib/pull/11572))
For all `n : ℕ`, the product of the set of prime factors of `n` divides `n`, 
i.e. `(∏ (p : ℕ) in n.factors.to_finset, p) ∣ n`

### [2022-02-13 17:37:37](https://github.com/leanprover-community/mathlib/commit/b08dc17)
chore(number_theory/dioph): fix docs ([#12011](https://github.com/leanprover-community/mathlib/pull/12011))

### [2022-02-12 22:55:33](https://github.com/leanprover-community/mathlib/commit/af1355c)
chore(measure_theory/integral/lebesgue): use to_additive when declaring instances and basic lemmas about simple functions ([#12000](https://github.com/leanprover-community/mathlib/pull/12000))
I also grouped similar lemmas together and added one or two missing ones.

### [2022-02-12 21:57:51](https://github.com/leanprover-community/mathlib/commit/4b217ea)
chore(topology/algebra): rename file to match renamed lemmas ([#11996](https://github.com/leanprover-community/mathlib/pull/11996))
[#11940](https://github.com/leanprover-community/mathlib/pull/11940) renamed the lemmas from `continuous_smul₂` to `continuous_const_smul`, so this renames the file from `mul_action2` to `const_mul_action` accordingly.

### [2022-02-12 19:33:32](https://github.com/leanprover-community/mathlib/commit/4a4a3a9)
chore(data/finset/basic): Golf and compress ([#11987](https://github.com/leanprover-community/mathlib/pull/11987))
* Move the `lattice` instance earlier so that it can be used to prove lemmas
* Golf proofs
* Compress statements within the style guidelines

### [2022-02-12 18:45:31](https://github.com/leanprover-community/mathlib/commit/5f70cd9)
chore(measure_theory/function/ae_eq_fun): replace topological assumptions by measurability assumptions ([#11981](https://github.com/leanprover-community/mathlib/pull/11981))
Since the introduction of the `has_measurable_*` typeclasses, the topological assumptions in that file are only used to derive the measurability assumptions. This PR removes that step.

### [2022-02-12 17:23:47](https://github.com/leanprover-community/mathlib/commit/b72300f)
feat(group_theory/sylow): all max groups normal imply sylow normal ([#11841](https://github.com/leanprover-community/mathlib/pull/11841))

### [2022-02-12 16:17:52](https://github.com/leanprover-community/mathlib/commit/06e7f76)
feat(analysis/analytic/basic): add uniqueness results for power series ([#11896](https://github.com/leanprover-community/mathlib/pull/11896))
This establishes that if a function has two power series representations on balls of positive radius, then the corresponding formal multilinear series are equal; this is only for the one-dimensional case (i.e., for functions from the scalar field). Consequently, one may exchange the radius of convergence between these power series.

### [2022-02-12 09:20:49](https://github.com/leanprover-community/mathlib/commit/91cc4ae)
feat(order/category/BoundedOrder): The category of bounded orders ([#11961](https://github.com/leanprover-community/mathlib/pull/11961))
Define `BoundedOrder`, the category of bounded orders with bounded order homs along with its forgetful functors to `PartialOrder` and `Bipointed`.

### [2022-02-12 08:07:28](https://github.com/leanprover-community/mathlib/commit/1b5f8c2)
chore(topology/algebra/ordered/*): Rename folder ([#11988](https://github.com/leanprover-community/mathlib/pull/11988))
Rename `topology.algebra.ordered` to `topology.algebra.order` to match `order`, `algebra.order`, `topology.order`.

### [2022-02-12 08:07:27](https://github.com/leanprover-community/mathlib/commit/7bebee6)
chore(category_theory/monad/equiv_mon): Removing some slow uses of `obviously` ([#11980](https://github.com/leanprover-community/mathlib/pull/11980))
Providing explicit proofs for various fields rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Follow-up to this suggestion by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)

### [2022-02-12 08:07:25](https://github.com/leanprover-community/mathlib/commit/71e9006)
chore(topology/algebra/module/multilinear): relax typeclass arguments ([#11972](https://github.com/leanprover-community/mathlib/pull/11972))
Previously `module R' (continuous_multilinear_map A M₁ M₂)` required `algebra R' A`, but now it only requires `smul_comm_class A R' M₂`.
The old instance required (modulo argument reordering):
```lean
def continuous_multilinear_map.module {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [decidable_eq ι]
  [Π i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [Π i, topological_space (M₁ i)]
  [topological_space M₂] [has_continuous_add M₂] 
  {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A] [topological_space R']
  [Π i, module A (M₁ i)]  [module A M₂] [module R' M₂] [has_continuous_smul R' M₂]
  [algebra R' A] [is_scalar_tower R' A M₂] :
    module R' (continuous_multilinear_map A M₁ M₂)
```
while the new one requires
```lean
def continuous_multilinear_map.module {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [decidable_eq ι]
  [Π i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [Π i, topological_space (M₁ i)]
  [topological_space M₂] [has_continuous_add M₂]
  {R' : Type u_1} {A : Type u_2} [semiring R'] [semiring A] [topological_space R']  -- note: `R'` not commutative any more
  [Π i, module A (M₁ i)] [module A M₂] [module R' M₂] [has_continuous_smul R' M₂]
  [smul_comm_class A R' M₂] :  -- note: `R'` needs no action at all on `A`
    module R' (continuous_multilinear_map A M₁ M₂)
```
This change also adds intermediate `mul_action` and `distrib_mul_action` instances which apply in weaker situations.
As a result of this weakening, the typeclass arguments to `continuous_multilinear_map.to_normed_space` can also be weakened, and a weird instance workaround can be removed.

### [2022-02-12 08:07:23](https://github.com/leanprover-community/mathlib/commit/822244f)
refactor(measure_theory/group/basic): rename and split ([#11952](https://github.com/leanprover-community/mathlib/pull/11952))
* Rename `measure_theory/group/basic` -> `measure_theory/group/measure`. It was not the bottom file in this folder in the import hierarchy (arithmetic is below it).
* Split off some results to `measure_theory/group/integration`. This reduces imports in some files, and makes the organization more clear. Furthermore, I will add some integrability results and more integrals in a follow-up PR.
* Prove a general instance `pi.is_mul_left_invariant`
* Remove lemmas specifically about `volume` on `real` in favor on the general lemmas.
```lean
real.map_volume_add_left -> map_add_left_eq_self
real.map_volume_pi_add_left -> map_add_left_eq_self
real.volume_preimage_add_left -> measure_preimage_add
real.volume_pi_preimage_add_left -> measure_preimage_add
real.map_volume_add_right -> map_add_right_eq_self 
real.volume_preimage_add_right -> measure_preimage_add_right
```

### [2022-02-12 07:11:55](https://github.com/leanprover-community/mathlib/commit/60d3233)
feat(topology/instances/real): metric space structure on nat ([#11963](https://github.com/leanprover-community/mathlib/pull/11963))
Mostly copied from the already existing int version.

### [2022-02-12 02:46:24](https://github.com/leanprover-community/mathlib/commit/dff8393)
feat(tactic/lint): add unprintable tactic linter ([#11725](https://github.com/leanprover-community/mathlib/pull/11725))
This linter will banish the recurring issue of tactics for which `param_desc` fails, leaving a nasty error message in hovers.

### [2022-02-12 00:03:02](https://github.com/leanprover-community/mathlib/commit/227293b)
feat(category_theory/category/Twop): The category of two-pointed types ([#11844](https://github.com/leanprover-community/mathlib/pull/11844))
Define `Twop`, the category of two-pointed types. Also add `Pointed_to_Bipointed` and remove the erroneous TODOs.

### [2022-02-11 21:25:20](https://github.com/leanprover-community/mathlib/commit/788240c)
chore(order/cover): Rename `covers` to `covby` ([#11984](https://github.com/leanprover-community/mathlib/pull/11984))
This matches the way it is written. `a ⋖ b` means that `b` covers `a`, that is `a` is covered by `b`.

### [2022-02-11 19:49:06](https://github.com/leanprover-community/mathlib/commit/3fcb738)
doc(data/finset/basic): correct some function names ([#11983](https://github.com/leanprover-community/mathlib/pull/11983))

### [2022-02-11 19:49:04](https://github.com/leanprover-community/mathlib/commit/515ce79)
refactor(data/nat/factorization): Use factorization instead of factors.count ([#11384](https://github.com/leanprover-community/mathlib/pull/11384))
Refactor to use `factorization` over `factors.count`, and adjust lemmas to be stated in terms of the former instead.

### [2022-02-11 18:25:43](https://github.com/leanprover-community/mathlib/commit/da76d21)
feat(measure_theory/measure/haar_quotient): Pushforward of Haar measure is Haar ([#11593](https://github.com/leanprover-community/mathlib/pull/11593))
For `G` a topological group with discrete subgroup `Γ`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. When `Γ` is normal (and under other certain suitable conditions), we show that this measure is the Haar measure on the quotient group `G ⧸ Γ`.

### [2022-02-11 15:45:40](https://github.com/leanprover-community/mathlib/commit/edefc11)
feat(number_theory/number_field/basic) : the ring of integers of a number field is not a field  ([#11956](https://github.com/leanprover-community/mathlib/pull/11956))

### [2022-02-11 13:10:47](https://github.com/leanprover-community/mathlib/commit/1b78b4d)
feat(measure_theory/function/ae_eq_of_integral): remove a few unnecessary `@` ([#11974](https://github.com/leanprover-community/mathlib/pull/11974))
Those `@` were necessary at the time, but `measurable_set.inter` changed and they can now be removed.

### [2022-02-11 13:10:46](https://github.com/leanprover-community/mathlib/commit/114752c)
fix(algebra/monoid_algebra/basic): remove an instance that forms a diamond ([#11918](https://github.com/leanprover-community/mathlib/pull/11918))
This turns `monoid_algebra.comap_distrib_mul_action_self` from an instance to a def.
This also adds some tests to prove that this diamond exists.
Note that this diamond is not just non-defeq, it's also just plain not equal.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Schur's.20lemma/near/270990004)

### [2022-02-11 11:23:57](https://github.com/leanprover-community/mathlib/commit/492393b)
feat(model_theory/direct_limit): Direct limits of first-order structures ([#11789](https://github.com/leanprover-community/mathlib/pull/11789))
Constructs the direct limit of a directed system of first-order embeddings

### [2022-02-11 07:37:33](https://github.com/leanprover-community/mathlib/commit/024aef0)
feat(data/pi): provide `pi.mul_single` ([#11849](https://github.com/leanprover-community/mathlib/pull/11849))
the additive version was previously called `pi.single`, to this requires refactoring existing code.

### [2022-02-11 03:15:15](https://github.com/leanprover-community/mathlib/commit/8c60a92)
fix(ring_theory/algebraic): prove a diamond exists and remove the instances ([#11935](https://github.com/leanprover-community/mathlib/pull/11935))
It seems nothing used these instances anyway.

### [2022-02-11 01:36:55](https://github.com/leanprover-community/mathlib/commit/fbfdff7)
chore(data/real/ennreal, topology/instances/ennreal): change name of the order isomorphism for `inv` ([#11959](https://github.com/leanprover-community/mathlib/pull/11959))
On [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/naming.20defs/near/271228611) it was decided that the name should be changed from `ennreal.inv_order_iso` to `order_iso.inv_ennreal` in order to better accord with the rest of the library.

### [2022-02-11 01:36:54](https://github.com/leanprover-community/mathlib/commit/ae14f6a)
chore(algebra/star): generalize star_bit0, add star_inv_of ([#11951](https://github.com/leanprover-community/mathlib/pull/11951))

### [2022-02-11 01:36:53](https://github.com/leanprover-community/mathlib/commit/0227820)
feat(topology/algebra/group): added (right/left)_coset_(open/closed) ([#11876](https://github.com/leanprover-community/mathlib/pull/11876))
Added lemmas saying that, in a topological group, cosets of an open (resp. closed) set are open (resp. closed).

### [2022-02-11 01:36:52](https://github.com/leanprover-community/mathlib/commit/7351358)
refactor(order/well_founded, set_theory/ordinal_arithmetic): Fix namespace in `self_le_of_strict_mono` ([#11871](https://github.com/leanprover-community/mathlib/pull/11871))
This places `self_le_of_strict_mono` in the `well_founded` namespace. We also rename `is_normal.le_self` to `is_normal.self_le` .

### [2022-02-10 23:42:58](https://github.com/leanprover-community/mathlib/commit/4a5728f)
chore(number_theory/cyclotomic/zeta): generalize to primitive roots ([#11941](https://github.com/leanprover-community/mathlib/pull/11941))
This was done as `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ)) = zeta p ℚ ℚ(ζₚ)` is independent of Lean's type theory. Allows far more flexibility with results.

### [2022-02-10 23:42:56](https://github.com/leanprover-community/mathlib/commit/d487230)
feat(algebra/big_operators): add prod_multiset_count_of_subset ([#11919](https://github.com/leanprover-community/mathlib/pull/11919))
Inspired by [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Co-Authored-By: Bhavik Mehta <bhavikmehta8@gmail.com>

### [2022-02-10 20:44:00](https://github.com/leanprover-community/mathlib/commit/fb41da9)
feat(algebra/module/basic): turn implications into iffs ([#11937](https://github.com/leanprover-community/mathlib/pull/11937))
* Turn the following implications into `iff`, rename them accordingly, and make the type arguments explicit (`M` has to be explicit when using it in `rw`, otherwise one will have unsolved type-class arguments)
```
eq_zero_of_two_nsmul_eq_zero -> two_nsmul_eq_zero
eq_zero_of_eq_neg -> self_eq_neg
ne_neg_of_ne_zero -> self_ne_neg
```
* Also add two variants
* Generalize `ne_neg_iff_ne_zero` to work in modules over a ring

### [2022-02-10 20:43:58](https://github.com/leanprover-community/mathlib/commit/0929387)
feat(group_theory/group_action/defs): add ext attributes ([#11936](https://github.com/leanprover-community/mathlib/pull/11936))
This adds `ext` attributes to `has_scalar`, `mul_action`, `distrib_mul_action`, `mul_distrib_mul_action`, and `module`.
The `ext` and `ext_iff` lemmas were eventually generated by `category_theory/preadditive/schur.lean` anyway - we may as well generate them much earlier.
The generated lemmas are slightly uglier than the `module_ext` we already have, but it doesn't really seem worth the trouble of writing out the "nice" versions when the `ext` tactic cleans up the mess for us anyway.

### [2022-02-10 20:43:57](https://github.com/leanprover-community/mathlib/commit/007d660)
feat(analysis/inner_product_space/pi_L2): `map_isometry_euclidean_of_orthonormal` ([#11907](https://github.com/leanprover-community/mathlib/pull/11907))
Add a lemma giving the result of `isometry_euclidean_of_orthonormal`
when applied to an orthonormal basis obtained from another orthonormal
basis with `basis.map`.

### [2022-02-10 20:43:56](https://github.com/leanprover-community/mathlib/commit/923923f)
feat(analysis/special_functions/complex/arg): `arg_mul`, `arg_div` lemmas ([#11903](https://github.com/leanprover-community/mathlib/pull/11903))
Add lemmas about `(arg (x * y) : real.angle)` and `(arg (x / y) : real.angle)`,
along with preparatory lemmas that are like those such as
`arg_mul_cos_add_sin_mul_I` but either don't require the real argument
to be in `Ioc (-π) π` or that take a `real.angle` argument.
I didn't add any lemmas about `arg (x * y)` or `arg (x / y)` as a
real; if such lemmas prove useful in future, it might make sense to
deduce them from the `real.angle` versions.

### [2022-02-10 20:43:55](https://github.com/leanprover-community/mathlib/commit/1141703)
feat(group_theory/group_action/sub_mul_action): orbit and stabilizer lemmas ([#11899](https://github.com/leanprover-community/mathlib/pull/11899))
Feat: add lemmas for stabilizer and orbit for sub_mul_action

### [2022-02-10 18:46:21](https://github.com/leanprover-community/mathlib/commit/de70722)
chore(algebra/punit_instances): all actions on punit are central ([#11953](https://github.com/leanprover-community/mathlib/pull/11953))

### [2022-02-10 18:46:20](https://github.com/leanprover-community/mathlib/commit/779d836)
feat(category_theory): variants of Yoneda are fully faithful ([#11950](https://github.com/leanprover-community/mathlib/pull/11950))

### [2022-02-10 18:46:19](https://github.com/leanprover-community/mathlib/commit/8012445)
feat(group_theory/subgroup/basic): `subgroup.map_le_map_iff_of_injective` ([#11947](https://github.com/leanprover-community/mathlib/pull/11947))
If `f` is injective, then `H.map f ≤ K.map f ↔ H ≤ K`.

### [2022-02-10 18:46:18](https://github.com/leanprover-community/mathlib/commit/c28dc84)
feat(topology/subset_properties): more facts about compact sets ([#11939](https://github.com/leanprover-community/mathlib/pull/11939))
* add `tendsto.is_compact_insert_range_of_cocompact`, `tendsto.is_compact_insert_range_of_cofinite`, and `tendsto.is_compact_insert_range`;
* reuse the former in `alexandroff.compact_space`;
* rename `finite_of_is_compact_of_discrete` to `is_compact.finite_of_discrete`, add `is_compact_iff_finite`;
* add `cocompact_le_cofinite`, `cocompact_eq_cofinite`;
* add `int.cofinite_eq`, add `@[simp]` to `nat.cofinite_eq`;
* add `set.insert_none_range_some`;
* move `is_compact.image_of_continuous_on` and `is_compact_image` up;

### [2022-02-10 17:14:10](https://github.com/leanprover-community/mathlib/commit/45ab382)
chore(field_theory/galois): make `intermediate_field.fixing_subgroup_equiv` computable ([#11938](https://github.com/leanprover-community/mathlib/pull/11938))
This also golfs and generalizes some results to reuse infrastructure from elsewhere.
In particular, this generalizes:
* `intermediate_field.fixed_field` to `fixed_points.intermediate_field`, where the latter matches the API of `fixed_points.subfield`
* `intermediate_field.fixing_subgroup` to `fixing_subgroup` and `fixing_submonoid`
This removes `open_locale classical` in favor of ensuring the lemmas take in the necessary decidable / fintype arguments.

### [2022-02-10 13:11:46](https://github.com/leanprover-community/mathlib/commit/a86277a)
feat(category_theory/limits): epi equalizer implies equal ([#11873](https://github.com/leanprover-community/mathlib/pull/11873))

### [2022-02-10 13:11:45](https://github.com/leanprover-community/mathlib/commit/20ef909)
feat(data/part): add instances ([#11868](https://github.com/leanprover-community/mathlib/pull/11868))
Add common instances for `part \alpha` to be inherited from `\alpha`. Spun off of [#11046](https://github.com/leanprover-community/mathlib/pull/11046)

### [2022-02-10 13:11:42](https://github.com/leanprover-community/mathlib/commit/3b9dc08)
feat(analysis/complex): add the Cauchy-Goursat theorem for an annulus ([#11864](https://github.com/leanprover-community/mathlib/pull/11864))

### [2022-02-10 13:11:41](https://github.com/leanprover-community/mathlib/commit/efa3157)
feat(order/conditionally_complete_lattice): `cInf_le` variant without redundant assumption ([#11863](https://github.com/leanprover-community/mathlib/pull/11863))
We prove `cInf_le'` on a `conditionally_complete_linear_order_bot`. We no longer need the boundedness assumption.

### [2022-02-10 13:11:40](https://github.com/leanprover-community/mathlib/commit/66d9cc1)
feat(number_theory/cyclotomic/gal): the Galois group of K(ζₙ) ([#11808](https://github.com/leanprover-community/mathlib/pull/11808))
from flt-regular!

### [2022-02-10 13:11:39](https://github.com/leanprover-community/mathlib/commit/1373d54)
feat(group_theory/nilpotent): add nilpotent implies normalizer condition ([#11586](https://github.com/leanprover-community/mathlib/pull/11586))

### [2022-02-10 13:11:37](https://github.com/leanprover-community/mathlib/commit/c3f6fce)
feat(algebra/group_power/basic): add lemmas about pow and neg on units ([#11447](https://github.com/leanprover-community/mathlib/pull/11447))
In future we might want to add a typeclass for monoids with a well-behaved negation operator to avoid needing to repeat these lemmas. Such a typeclass would also apply to the `unitary` submonoid too.

### [2022-02-10 13:11:36](https://github.com/leanprover-community/mathlib/commit/c3d8782)
feat(category_theory/bicategory/functor_bicategory): bicategory structure on oplax functors ([#11405](https://github.com/leanprover-community/mathlib/pull/11405))
This PR defines a bicategory structure on the oplax functors between bicategories.

### [2022-02-10 10:46:35](https://github.com/leanprover-community/mathlib/commit/da164c6)
feat (category_theory/karoubi_karoubi) : idempotence of karoubi ([#11931](https://github.com/leanprover-community/mathlib/pull/11931))
In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.

### [2022-02-10 10:46:34](https://github.com/leanprover-community/mathlib/commit/0490977)
feat(algebra/lie/engel): add proof of Engel's theorem ([#11922](https://github.com/leanprover-community/mathlib/pull/11922))

### [2022-02-10 10:46:32](https://github.com/leanprover-community/mathlib/commit/f32fda7)
feat(set_theory/ordinal_arithmetic): More `lsub` and `blsub` lemmas ([#11848](https://github.com/leanprover-community/mathlib/pull/11848))
We prove variants of `sup_typein`, which serve as analogs for `blsub_id`. We also prove `sup_eq_lsub_or_sup_succ_eq_lsub`, which combines `sup_le_lsub` and `lsub_le_sup_succ`.

### [2022-02-10 10:46:31](https://github.com/leanprover-community/mathlib/commit/b7360f9)
feat(group_theory/general_commutator): subgroup.prod commutes with the general_commutator ([#11818](https://github.com/leanprover-community/mathlib/pull/11818))

### [2022-02-10 10:46:28](https://github.com/leanprover-community/mathlib/commit/6afaf36)
feat(algebra/order/hom/ring): Ordered semiring/ring homomorphisms ([#11634](https://github.com/leanprover-community/mathlib/pull/11634))
Define `order_ring_hom` with notation `→+*o` along with its hom class.

### [2022-02-10 09:27:23](https://github.com/leanprover-community/mathlib/commit/8f5fd26)
feat(data/nat/factorization): bijection between positive nats and finsupps over primes ([#11440](https://github.com/leanprover-community/mathlib/pull/11440))
Proof that for any finsupp `f : ℕ →₀ ℕ` whose support is in the primes, `f = (f.prod pow).factorization`, and hence that the positive natural numbers are bijective with finsupps `ℕ →₀ ℕ` with support in the primes.

### [2022-02-10 09:27:22](https://github.com/leanprover-community/mathlib/commit/0aa0bc8)
feat(set_theory/ordinal_arithmetic): The derivative of addition ([#11270](https://github.com/leanprover-community/mathlib/pull/11270))
We prove that the derivative of `(+) a` evaluated at `b` is given by `a * ω + b`.

### [2022-02-10 08:34:06](https://github.com/leanprover-community/mathlib/commit/e60ca6b)
feat(data/real/ennreal): `inv` is an `order_iso` to the order dual and lemmas for `supr, infi` ([#11869](https://github.com/leanprover-community/mathlib/pull/11869))
Establishes that `inv` is an order isomorphism to the order dual. We then provide some convenience lemmas which guarantee that `inv` switches `supr` and `infi` and hence also switches `limsup` and `liminf`.

### [2022-02-10 08:34:05](https://github.com/leanprover-community/mathlib/commit/b7e72ea)
feat(measure_theory/probability_mass_function): Measure calculations for additional pmf constructions ([#11858](https://github.com/leanprover-community/mathlib/pull/11858))
This PR adds calculations of the measures of sets under various `pmf` constructions.

### [2022-02-10 08:04:04](https://github.com/leanprover-community/mathlib/commit/e9a1893)
chore(tactic/default): import `linear_combination` ([#11942](https://github.com/leanprover-community/mathlib/pull/11942))

### [2022-02-10 03:40:32](https://github.com/leanprover-community/mathlib/commit/ea0e458)
refactor(topology/algebra/mul_action2): rename type classes ([#11940](https://github.com/leanprover-community/mathlib/pull/11940))
Rename `has_continuous_smul₂` and `has_continuous_vadd₂` to
`has_continuous_const_smul` and `has_continuous_const_vadd`,
respectively.

### [2022-02-09 23:10:35](https://github.com/leanprover-community/mathlib/commit/4e8d8fa)
feat(order/hom/bounded): Bounded order homomorphisms ([#11806](https://github.com/leanprover-community/mathlib/pull/11806))
Define `bounded_order_hom` in `order.hom.bounded` and move `top_hom`, `bot_hom` there.

### [2022-02-09 21:35:24](https://github.com/leanprover-community/mathlib/commit/4691159)
doc(algebra/group/hom_instances): Fix spellings ([#11943](https://github.com/leanprover-community/mathlib/pull/11943))
Fixes spelling mistakes introduced by [#11843](https://github.com/leanprover-community/mathlib/pull/11843)

### [2022-02-09 20:38:41](https://github.com/leanprover-community/mathlib/commit/352e064)
feat(topology/uniform_space/cauchy): add a few lemmas ([#11912](https://github.com/leanprover-community/mathlib/pull/11912))

### [2022-02-09 18:57:12](https://github.com/leanprover-community/mathlib/commit/2b9aca7)
feat(topology): a few more results about compact sets ([#11905](https://github.com/leanprover-community/mathlib/pull/11905))
* Also a few lemmas about sets and `mul_support`.

### [2022-02-09 18:57:10](https://github.com/leanprover-community/mathlib/commit/b8fb8e5)
feat(set_theory/ordinal_arithmetic): `le_one_iff` ([#11847](https://github.com/leanprover-community/mathlib/pull/11847))

### [2022-02-09 18:57:09](https://github.com/leanprover-community/mathlib/commit/2726e23)
feat(algebra.group.hom_instances): Define left and right multiplication operators ([#11843](https://github.com/leanprover-community/mathlib/pull/11843))
Defines left and right multiplication operators on non unital, non associative semirings.
Suggested by @ocfnash for [#11073](https://github.com/leanprover-community/mathlib/pull/11073)

### [2022-02-09 17:14:15](https://github.com/leanprover-community/mathlib/commit/5008de8)
feat(order): some properties about monotone predicates ([#11904](https://github.com/leanprover-community/mathlib/pull/11904))
* We prove that some predicates are monotone/antitone w.r.t. some order. The proofs are all trivial.
* We prove 2 `iff` statements depending on the hypothesis that a certain predicate is (anti)mono: `exists_ge_and_iff_exists` and `filter.exists_mem_and_iff`)
* The former is used to prove `bdd_above_iff_exists_ge`, the latter will be used in a later PR.

### [2022-02-09 17:14:14](https://github.com/leanprover-community/mathlib/commit/d3cdcd8)
feat(order/filter/basic): add lemma `le_prod_map_fst_snd` ([#11901](https://github.com/leanprover-community/mathlib/pull/11901))
A lemma relating filters on products and the filter-product of the projections. This lemma is particularly useful when proving the continuity of a function on a product space using filters.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff

### [2022-02-09 17:14:12](https://github.com/leanprover-community/mathlib/commit/9648ce2)
chore(data/pi): add pi.prod and use elsewhere ([#11877](https://github.com/leanprover-community/mathlib/pull/11877))
`pi.prod` is the function that underlies `add_monoid_hom.prod`, `linear_map.prod`, etc.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff/near/270851797)

### [2022-02-09 15:50:47](https://github.com/leanprover-community/mathlib/commit/ca2450f)
feat(order/atoms): finite orders are (co)atomic ([#11930](https://github.com/leanprover-community/mathlib/pull/11930))

### [2022-02-09 14:10:33](https://github.com/leanprover-community/mathlib/commit/c882753)
chore(algebra/tropical/basic): remove 3 instances ([#11920](https://github.com/leanprover-community/mathlib/pull/11920))
The three removed instances are
* `covariant_swap_add` (exists since addition is commutative and the non-swapped version is proved);
* `covariant_add_lt` (as is, this is a copy of `covariant_add` -- judging from the name, it could have been intended to have a `(<)`, but with `(<)` it is false, see below);
* `covariant_swap_add_lt` (exists since addition is commutative and the non-swapped version is proved).
Here is a proof that the second instance with `(<)` is false:
```lean
lemma not_cov_lt : ¬ covariant_class (tropical ℕ) (tropical ℕ) (+) (<) :=
begin
  refine λ h, (lt_irrefl (trop 0) _),
  cases h,
  have : trop 0 < trop 1 := show 0 < 1, from zero_lt_one,
  calc trop 0 = trop 0 + trop 0 : (trop 0).add_self.symm
          ... < trop 0 + trop 1 : h _ this
          ... = trop 0          : add_eq_left this.le,
end
```

### [2022-02-09 11:36:35](https://github.com/leanprover-community/mathlib/commit/fea68aa)
chore(data/fintype/basic): documenting elaboration bug ([#11247](https://github.com/leanprover-community/mathlib/pull/11247))
Simplifying an expression and documenting an elaboration bug that it was avoiding.

### [2022-02-09 09:56:15](https://github.com/leanprover-community/mathlib/commit/3aa5b8a)
refactor(algebra/ring/basic): rename lemmas about `a*(-b)` and `(-a)*b` ([#11925](https://github.com/leanprover-community/mathlib/pull/11925))
This renames:
* `(- a) * b = - (a * b)` from `neg_mul_eq_neg_mul_symm` to `neg_mul`
* `a * (-b) = - (a * b)` from `mul_neg_eq_neg_mul_symm` to `mul_neg`
The new names are much easier to find when compared with `sub_mul`, `mul_sub` etc, and match the existing namespaced names under `units` and `matrix`.
This also replaces rewrites by `← neg_mul_eq_neg_mul` with `neg_mul` and rewrites by `← neg_mul_eq_mul_neg` with `mul_neg`.
To avoid clashes, the names in the `matrix` namespace are now `protected`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/mul_neg.2C.20neg_mul/near/233638226)

### [2022-02-09 08:51:48](https://github.com/leanprover-community/mathlib/commit/4e17e08)
feat(data/complex/basic): re-im set product ([#11770](https://github.com/leanprover-community/mathlib/pull/11770))
`set.re_im_prod s t` (notation: `s ×ℂ t`) is the product of a set on the real axis and a set on the
imaginary axis of the complex plane.

### [2022-02-09 07:16:44](https://github.com/leanprover-community/mathlib/commit/78c3975)
feat(category_theory/pseudoabelian/basic): basic facts and contructions about pseudoabelian categories ([#11817](https://github.com/leanprover-community/mathlib/pull/11817))

### [2022-02-08 22:14:40](https://github.com/leanprover-community/mathlib/commit/56db7ed)
feat(analysis/normed_space/basic): add lemmas `nnnorm_mul_le` and `nnnorm_pow_succ_le` ([#11915](https://github.com/leanprover-community/mathlib/pull/11915))
Adds two convenience lemmas for `nnnorm`, submultiplicativity of `nnnorm` for semi-normed rings and the corresponding extension to powers. We only allow successors so as not to incur the `norm_one_class` type class constraint.

### [2022-02-08 21:07:37](https://github.com/leanprover-community/mathlib/commit/a3d6b43)
feat(topology/algebra/uniform_group): `cauchy_seq.const_mul` and friends ([#11917](https://github.com/leanprover-community/mathlib/pull/11917))
A Cauchy sequence multiplied by a constant (including `-1`) remains a Cauchy sequence.

### [2022-02-08 19:01:57](https://github.com/leanprover-community/mathlib/commit/4545e31)
feat(model_theory/substructures): More operations on substructures ([#11906](https://github.com/leanprover-community/mathlib/pull/11906))
Defines the substructure `first_order.language.hom.range`.
Defines the homomorphisms `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict`, and the embeddings `first_order.language.embedding.dom_restrict`, `first_order.language.embedding.cod_restrict` which restrict the domain or codomain of a first-order hom or embedding to a substructure.
Defines the embedding `first_order.language.substructure.inclusion` between nested substructures.

### [2022-02-08 17:19:13](https://github.com/leanprover-community/mathlib/commit/1ae8304)
chore(*): update to lean 3.39.1c ([#11926](https://github.com/leanprover-community/mathlib/pull/11926))

### [2022-02-08 13:50:04](https://github.com/leanprover-community/mathlib/commit/b1269b0)
chore(algebra/order/ring): add a few aliases ([#11911](https://github.com/leanprover-community/mathlib/pull/11911))
Add aliases `one_pos`, `two_pos`, `three_pos`, and `four_pos`.
We used to have (some of) these lemmas. They were removed during one of cleanups but it doesn't hurt to have aliases.

### [2022-02-08 12:43:42](https://github.com/leanprover-community/mathlib/commit/85d9f21)
feat(*): localized `R[X]` notation for `polynomial R` ([#11895](https://github.com/leanprover-community/mathlib/pull/11895))
I did not change `polynomial (complex_term_here taking args)` in many places because I thought it would be more confusing. Also, in some files that prove things about polynomials incidentally, I also did not include the notation and change the files.

### [2022-02-08 09:20:10](https://github.com/leanprover-community/mathlib/commit/5932581)
feat(group_theory/submonoid/operations): prod_le_iff and le_prod_iff, also for groups and modules ([#11898](https://github.com/leanprover-community/mathlib/pull/11898))

### [2022-02-08 08:51:03](https://github.com/leanprover-community/mathlib/commit/2b68801)
refactor(number_theory/bernoulli_polynomials): improve names ([#11805](https://github.com/leanprover-community/mathlib/pull/11805))
Cleanup the bernoulli_polynomials file

### [2022-02-08 04:53:51](https://github.com/leanprover-community/mathlib/commit/1077eb3)
feat(analysis/complex): a few lemmas about `dist` and `conj` ([#11913](https://github.com/leanprover-community/mathlib/pull/11913))

### [2022-02-07 20:25:46](https://github.com/leanprover-community/mathlib/commit/36d3b68)
feat(linear_algebra/basis): `basis.map_equiv_fun` ([#11888](https://github.com/leanprover-community/mathlib/pull/11888))
Add a `simp` lemma about the effect of `equiv_fun` for a basis
obtained with `basis.map`.

### [2022-02-07 19:33:57](https://github.com/leanprover-community/mathlib/commit/f94b0b3)
style(analysis/special_functions/trigonometric/angle): make types of `sin` and `cos` explicit ([#11902](https://github.com/leanprover-community/mathlib/pull/11902))
Give the types of the results of `real.angle.sin` and `real.angle.cos`
explicitly, as requested by @eric-wieser in [#11887](https://github.com/leanprover-community/mathlib/pull/11887).

### [2022-02-07 19:33:56](https://github.com/leanprover-community/mathlib/commit/9ceb3c2)
feat(topology/sheaf_condition): connect sheaves on sites and on spaces without has_products ([#11706](https://github.com/leanprover-community/mathlib/pull/11706))
As an application of [#11692](https://github.com/leanprover-community/mathlib/pull/11692), show that the is_sheaf_opens_le_cover sheaf condition on spaces is equivalent to is_sheaf on sites, thereby connecting sheaves on sites and on spaces without the value category has_products for the first time. (@justus-springer: you might want to take a look so as to determine whether and which of your work in [#9609](https://github.com/leanprover-community/mathlib/pull/9609) should be deprecated.) This could be seen as a step towards refactoring sheaves on spaces through sheaves on sites.
- [x] depends on: [#11692](https://github.com/leanprover-community/mathlib/pull/11692)

### [2022-02-07 17:28:22](https://github.com/leanprover-community/mathlib/commit/436966c)
chore(data/finsupp/basic): generalize comap_mul_action ([#11900](https://github.com/leanprover-community/mathlib/pull/11900))
This new definition is propoitionally equal to the old one in the presence of `[group G]` (all the previous `lemma`s continue to apply), but generalizes to `[monoid G]`.
This also removes `finsupp.comap_distrib_mul_action_self` as there is no need to have this as a separate definition.

### [2022-02-07 17:28:21](https://github.com/leanprover-community/mathlib/commit/7b91f00)
feat(algebra/big_operators/basic): add multiset.prod_sum ([#11885](https://github.com/leanprover-community/mathlib/pull/11885))

### [2022-02-07 15:42:07](https://github.com/leanprover-community/mathlib/commit/02c9d69)
feat(analysis/inner_product_space/basic): `orthonormal.map_linear_isometry_equiv` ([#11893](https://github.com/leanprover-community/mathlib/pull/11893))
Add a variant of `orthonormal.comp_linear_isometry_equiv` for the case
of an orthonormal basis mapped with `basis.map`.
If in future we get a bundled type of orthonormal bases with its own
`map` operation, this would no longer be a separate lemma, but until
then it's useful.

### [2022-02-07 15:42:06](https://github.com/leanprover-community/mathlib/commit/c61ea33)
feat(analysis/complex/isometry): `rotation_symm` ([#11891](https://github.com/leanprover-community/mathlib/pull/11891))
Add a `simp` lemma that the inverse of `rotation` is rotation by the
inverse angle.

### [2022-02-07 15:42:04](https://github.com/leanprover-community/mathlib/commit/2364a09)
feat(analysis/complex/circle): `exp_map_circle_neg` ([#11889](https://github.com/leanprover-community/mathlib/pull/11889))
Add the lemma `exp_map_circle_neg`, similar to other lemmas for
`exp_map_circle` that are already present.

### [2022-02-07 15:42:03](https://github.com/leanprover-community/mathlib/commit/99215e3)
feat(analysis/special_functions/trigonometric/angle): `sin`, `cos` ([#11887](https://github.com/leanprover-community/mathlib/pull/11887))
Add definitions of `sin` and `cos` that act on a `real.angle`.

### [2022-02-07 15:42:01](https://github.com/leanprover-community/mathlib/commit/98ef84e)
feat(analysis/special_functions/trigonometric/angle): `induction_on` ([#11886](https://github.com/leanprover-community/mathlib/pull/11886))
Add `real.angle.induction_on`, for use in deducing results for
`real.angle` from those for `ℝ`.

### [2022-02-07 15:42:00](https://github.com/leanprover-community/mathlib/commit/26179cc)
feat(data/list): add some lemmas. ([#11879](https://github.com/leanprover-community/mathlib/pull/11879))

### [2022-02-07 15:41:58](https://github.com/leanprover-community/mathlib/commit/dcbb59c)
feat(category_theory/limits): is_limit.exists_unique ([#11875](https://github.com/leanprover-community/mathlib/pull/11875))
Yet another restatement of the limit property which is occasionally useful.

### [2022-02-07 15:41:57](https://github.com/leanprover-community/mathlib/commit/556483f)
feat(category_theory/limits): (co)equalizers in the opposite category ([#11874](https://github.com/leanprover-community/mathlib/pull/11874))

### [2022-02-07 15:41:55](https://github.com/leanprover-community/mathlib/commit/7a2a546)
feat(data/set/opposite): the opposite of a set ([#11860](https://github.com/leanprover-community/mathlib/pull/11860))

### [2022-02-07 15:41:54](https://github.com/leanprover-community/mathlib/commit/0354e56)
feat(order/complete_lattice): infi_le_iff ([#11810](https://github.com/leanprover-community/mathlib/pull/11810))
Add missing lemma `infi_le_iff {s : ι → α} : infi s ≤ a ↔ (∀ b, (∀ i, b ≤ s i) → b ≤ a)`
Also take the opportunity to restate `Inf_le_iff` to restore consistency with `le_Sup_iff` that was broken in [#10607](https://github.com/leanprover-community/mathlib/pull/10607) and move `le_supr_iff` close to `le_Sup_iff` and remove a couple of unneeded parentheses.

### [2022-02-07 14:32:55](https://github.com/leanprover-community/mathlib/commit/a2f3f55)
chore(algebra/monoid_algebra): generalize lift_nc ([#11881](https://github.com/leanprover-community/mathlib/pull/11881))
The g argument does not need to be a bundled morphism here in the definition.
Instead, we require it be a bundled morphism only in the downstream lemmas, using the new typeclass machinery

### [2022-02-07 12:33:08](https://github.com/leanprover-community/mathlib/commit/04b9d28)
feat(data/pfun): Composition of partial functions ([#11865](https://github.com/leanprover-community/mathlib/pull/11865))
Define
* `pfun.id`: The identity as a partial function
* `pfun.comp`: Composition of partial functions
* `pfun.to_subtype`: Restrict the codomain of a function to a subtype and make it partial

### [2022-02-07 11:17:01](https://github.com/leanprover-community/mathlib/commit/0090891)
chore(model_theory/*): Split up model_theory/basic ([#11846](https://github.com/leanprover-community/mathlib/pull/11846))
Splits model_theory/basic into separate files: basic, substructures, terms_and_formulas, definability, quotients
Improves documentation throughout

### [2022-02-07 10:17:41](https://github.com/leanprover-community/mathlib/commit/3c70566)
feat(analysis/normed_space/linear_isometry): `symm_trans` ([#11892](https://github.com/leanprover-community/mathlib/pull/11892))
Add a `simp` lemma `linear_isometry_equiv.symm_trans`, like
`coe_symm_trans` but without a coercion involved.  `coe_symm_trans`
can then be proved by `simp`, so stops being a `simp` lemma itself.

### [2022-02-07 08:33:33](https://github.com/leanprover-community/mathlib/commit/b1b09eb)
refactor(data/quot): Make more `setoid` arguments implicit ([#11824](https://github.com/leanprover-community/mathlib/pull/11824))
Currently, not all of the `quotient` API can be used with non-instance setoids. This fixes it by making a few `setoid` arguments explicit rather than instances.

### [2022-02-07 03:57:45](https://github.com/leanprover-community/mathlib/commit/25297ec)
feat(analysis/complex/basic): `conj_lie_symm` ([#11890](https://github.com/leanprover-community/mathlib/pull/11890))
Add a `simp` lemma that the inverse of `conj_lie` is `conj_lie`.

### [2022-02-06 19:03:43](https://github.com/leanprover-community/mathlib/commit/e18972b)
feat(set_theory/ordinal_arithmetic): Suprema of empty families ([#11872](https://github.com/leanprover-community/mathlib/pull/11872))

### [2022-02-06 07:25:14](https://github.com/leanprover-community/mathlib/commit/24ebc5c)
feat(group_theory/sylow): the cardinality of a sylow group ([#11776](https://github.com/leanprover-community/mathlib/pull/11776))

### [2022-02-06 01:53:58](https://github.com/leanprover-community/mathlib/commit/4148990)
feat(set_theory/ordinal_arithmetic): Suprema and least strict upper bounds of constant families ([#11862](https://github.com/leanprover-community/mathlib/pull/11862))

### [2022-02-05 21:22:39](https://github.com/leanprover-community/mathlib/commit/6787a8d)
feat(category_theory): a hierarchy of balanced categories ([#11856](https://github.com/leanprover-community/mathlib/pull/11856))

### [2022-02-05 19:40:29](https://github.com/leanprover-community/mathlib/commit/0f9c153)
feat(algebra/cubic_discriminant): basics of cubic polynomials and their discriminants ([#11483](https://github.com/leanprover-community/mathlib/pull/11483))

### [2022-02-05 17:59:51](https://github.com/leanprover-community/mathlib/commit/39b1262)
feat(algebra/lie/nilpotent): nilpotency of Lie modules depends only on the Lie subalgebra of linear endomorphisms ([#11853](https://github.com/leanprover-community/mathlib/pull/11853))

### [2022-02-05 17:59:49](https://github.com/leanprover-community/mathlib/commit/b9d19ed)
feat(algebra/lie/nilpotent): nilpotency of Lie modules is preserved under surjective morphisms ([#11852](https://github.com/leanprover-community/mathlib/pull/11852))

### [2022-02-05 17:59:47](https://github.com/leanprover-community/mathlib/commit/9fcd1f2)
feat(algebra/lie/nilpotent): add lemma `lie_module.coe_lower_central_series_ideal_le` ([#11851](https://github.com/leanprover-community/mathlib/pull/11851))

### [2022-02-05 17:31:04](https://github.com/leanprover-community/mathlib/commit/df7c217)
feat(algebra/lie/nilpotent): add definition `lie_ideal.lcs` ([#11854](https://github.com/leanprover-community/mathlib/pull/11854))
This is extremely useful when proving a generalised version of Engel's lemma.

### [2022-02-05 09:52:03](https://github.com/leanprover-community/mathlib/commit/9969321)
feat(measure_theory/probability_mass_function): Lemmas connecting `pmf.support` and `pmf.to_measure` ([#11842](https://github.com/leanprover-community/mathlib/pull/11842))
Add lemmas relating the support of a `pmf` to the measures of sets under the induced measure.

### [2022-02-05 09:52:01](https://github.com/leanprover-community/mathlib/commit/612ca40)
feat(data/finset): erase is empty iff ([#11838](https://github.com/leanprover-community/mathlib/pull/11838))

### [2022-02-05 09:52:00](https://github.com/leanprover-community/mathlib/commit/31f5688)
refactor(ring_theory/valuation/basic): `fun_like` design for `valuation` ([#11830](https://github.com/leanprover-community/mathlib/pull/11830))
Introduce `valuation_class`, the companion typeclass to `valuation`. Deprecate lemmas. Rename the field from `map_add'` to `map_add_le_max'` to avoid confusion with the eponymous field from `add_hom`.

### [2022-02-05 09:51:59](https://github.com/leanprover-community/mathlib/commit/e78563c)
feat(ring_theory/power_series): reindex trunc of a power series to truncate below index n ([#10891](https://github.com/leanprover-community/mathlib/pull/10891))
Currently the definition of truncation of a univariate and multivariate power series truncates above the index, that is if we truncate a power series $\sum a_i x^i$ at index `n` the term $a_n x^n$ is included.
This makes it impossible to truncate the first monomial $x^0$ away as it is included with the smallest possible value of n, which causes some issues in applications (imagine if you could only pop elements of lists if the result was non-empty!).

### [2022-02-05 08:16:33](https://github.com/leanprover-community/mathlib/commit/6b4e269)
chore(data/fintype/basic): rename some instances ([#11845](https://github.com/leanprover-community/mathlib/pull/11845))
Rename instances from `infinite.multiset.infinite` etc to
`multiset.infinite` etc; rename `infinite.set.infinite` to
`infinite.set` to avoid name clash.
Also add `option.infinite`.

### [2022-02-05 05:19:33](https://github.com/leanprover-community/mathlib/commit/b0d9761)
feat(ring_theory/hahn_series): add a map to power series and dickson's lemma ([#11836](https://github.com/leanprover-community/mathlib/pull/11836))
Add a ring equivalence between `hahn_series` and `mv_power_series` as discussed in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/induction.20on.20an.20index.20type/near/269463528.
This required adding some partially well ordered lemmas that it seems go under the name Dickson's lemma.
This may be independently useful, a constructive version of this has been used in other provers, especially in connection to Grobner basis and commutative algebra type material.

### [2022-02-04 23:34:38](https://github.com/leanprover-community/mathlib/commit/bd7d034)
feat(ring_theory/nilpotent): add lemma `module.End.is_nilpotent_mapq` ([#11831](https://github.com/leanprover-community/mathlib/pull/11831))
Together with the other lemmas necessary for its proof.

### [2022-02-04 22:50:46](https://github.com/leanprover-community/mathlib/commit/b905eb6)
fix(group_theory/nilpotent): don’t unnecessarily `open_locale classical` ([#11779](https://github.com/leanprover-community/mathlib/pull/11779))
h/t @pechersky for noticing

### [2022-02-04 21:12:18](https://github.com/leanprover-community/mathlib/commit/b3b32c8)
feat(algebra/lie/quotient): first isomorphism theorem for morphisms of Lie algebras ([#11826](https://github.com/leanprover-community/mathlib/pull/11826))

### [2022-02-04 21:12:17](https://github.com/leanprover-community/mathlib/commit/292bf34)
feat(algebra/lie/ideal_operations): add lemma `lie_ideal_oper_eq_linear_span'` ([#11823](https://github.com/leanprover-community/mathlib/pull/11823))
It is useful to have this alternate form in situations where we have a hypothesis like `h : I = J` since we can then rewrite using `h` after applying this lemma.
An (admittedly brief) scan of the existing applications of `lie_ideal_oper_eq_linear_span` indicates that it's worth keeping both forms for convenience but I'm happy to dig deeper into this if requested.

### [2022-02-04 21:12:16](https://github.com/leanprover-community/mathlib/commit/fa20482)
feat(linear_algebra/basic): add minor lemmas, tweak `simp` attributes ([#11822](https://github.com/leanprover-community/mathlib/pull/11822))

### [2022-02-04 21:12:15](https://github.com/leanprover-community/mathlib/commit/247504c)
feat(algebra/lie/cartan_subalgebra): add lemma `lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer` ([#11820](https://github.com/leanprover-community/mathlib/pull/11820))

### [2022-02-04 21:12:13](https://github.com/leanprover-community/mathlib/commit/a2fd0bd)
feat(algebra/lie/basic): define pull back of a Lie module along a morphism of Lie algebras. ([#11819](https://github.com/leanprover-community/mathlib/pull/11819))

### [2022-02-04 21:12:12](https://github.com/leanprover-community/mathlib/commit/2e7efe9)
refactor(set_theory/ordinal_arithmetic): Change `α → Prop` to `set α` ([#11816](https://github.com/leanprover-community/mathlib/pull/11816))

### [2022-02-04 21:12:11](https://github.com/leanprover-community/mathlib/commit/a741585)
chore(algebra/group): make `coe_norm_subgroup` and `submodule.norm_coe` consistent ([#11427](https://github.com/leanprover-community/mathlib/pull/11427))
The `simp` lemmas for norms in a subgroup and in a submodule disagreed: the first inserted a coercion to the larger group, the second deleted the coercion. Currently this is not a big deal, but it will become a real issue when defining `add_subgroup_class`. I want to make them consistent by pointing them in the same direction. The consensus in the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Simp.20normal.20form.3A.20coe_norm_subgroup.2C.20submodule.2Enorm_coe) suggests `simp` should insert a coercion here, so I went with that.
After making the changes, a few places need extra `simp [submodule.coe_norm]` on the local hypotheses, but nothing major.

### [2022-02-04 20:39:46](https://github.com/leanprover-community/mathlib/commit/c3273aa)
feat(algebra/lie/subalgebra): add `lie_subalgebra.equiv_of_le` and `lie_subalgebra.equiv_range_of_injective` ([#11828](https://github.com/leanprover-community/mathlib/pull/11828))

### [2022-02-04 18:53:26](https://github.com/leanprover-community/mathlib/commit/3c00e5d)
fix(algebra/Module/colimits): Change `comm_ring` to `ring`. ([#11837](https://github.com/leanprover-community/mathlib/pull/11837))
... despite the well-known fact that all rings are commutative.

### [2022-02-04 18:53:25](https://github.com/leanprover-community/mathlib/commit/5b3cd4a)
refactor(analysis/normed_space/add_torsor): Kill `seminormed_add_torsor` ([#11795](https://github.com/leanprover-community/mathlib/pull/11795))
Delete `normed_add_torsor` in favor of the equivalent `seminormed_add_torsor` and rename `seminormed_add_torsor` to `normed_add_torsor`.

### [2022-02-04 18:53:24](https://github.com/leanprover-community/mathlib/commit/aaaeeae)
feat(category_theory/category/{Pointed,Bipointed}): The categories of pointed/bipointed types ([#11777](https://github.com/leanprover-community/mathlib/pull/11777))
Define
* `Pointed`, the category of pointed types
* `Bipointed`, the category of bipointed types
* the forgetful functors from `Bipointed` to `Pointed` and from `Pointed` to `Type*`
* `Type_to_Pointed`, the functor from `Type*` to `Pointed` induced by `option`
* `Bipointed.swap_equiv` the equivalence between `Bipointed` and itself induced by `prod.swap` both ways.

### [2022-02-04 17:10:26](https://github.com/leanprover-community/mathlib/commit/cedcf07)
chore(*): update to lean 3.39.0c ([#11821](https://github.com/leanprover-community/mathlib/pull/11821))

### [2022-02-04 08:58:31](https://github.com/leanprover-community/mathlib/commit/049a1b2)
feat(group_theory/subgroup/basic): add pi subgroups ([#11801](https://github.com/leanprover-community/mathlib/pull/11801))

### [2022-02-04 06:54:32](https://github.com/leanprover-community/mathlib/commit/46c48d7)
feat(logic/basic): add projection notation for iff ([#11803](https://github.com/leanprover-community/mathlib/pull/11803))

### [2022-02-04 02:33:18](https://github.com/leanprover-community/mathlib/commit/553cb9c)
fix(algebra/category/Module/colimits): Add some additional instances with permuted universe parameters ([#11812](https://github.com/leanprover-community/mathlib/pull/11812))

### [2022-02-04 02:33:17](https://github.com/leanprover-community/mathlib/commit/4cfc30e)
chore(*): use le_rfl instead of le_refl _ ([#11797](https://github.com/leanprover-community/mathlib/pull/11797))

### [2022-02-04 02:03:42](https://github.com/leanprover-community/mathlib/commit/6dcad02)
feat(linear_algebra/lagrange): Add recurrence formula for Lagrange polynomials ([#11762](https://github.com/leanprover-community/mathlib/pull/11762))
I have also changed `interpolate` to take in a function `f : F → F` instead of `f : s → F`, since this makes the statement of the theorem nicer.

### [2022-02-03 23:36:11](https://github.com/leanprover-community/mathlib/commit/853192c)
feat(topology/algebra): Inf and inducing preserve compatibility with algebraic structure ([#11720](https://github.com/leanprover-community/mathlib/pull/11720))
This partly duplicates @mariainesdff 's work on group topologies, but I'm using an unbundled approach which avoids defining a new `X_topology` structure for each interesting X.

### [2022-02-03 18:39:52](https://github.com/leanprover-community/mathlib/commit/30a731c)
fix(algebra/category/Module/colimits): generalize universes ([#11802](https://github.com/leanprover-community/mathlib/pull/11802))

### [2022-02-03 18:39:51](https://github.com/leanprover-community/mathlib/commit/f2be0d2)
feat(polynomial/cyclotomic): irreducible cyclotomic polynomials are minimal polynomials ([#11796](https://github.com/leanprover-community/mathlib/pull/11796))
from flt-regular

### [2022-02-03 16:59:03](https://github.com/leanprover-community/mathlib/commit/2c5f36c)
feat(data/finset/sort): an order embedding from fin ([#11800](https://github.com/leanprover-community/mathlib/pull/11800))
Given a set `s` of at least `k` element in a linear order, there is an order embedding from `fin k` whose image is contained in `s`.

### [2022-02-03 16:59:01](https://github.com/leanprover-community/mathlib/commit/25f0406)
fix(topology/connected): typos in docstrings ([#11798](https://github.com/leanprover-community/mathlib/pull/11798))
As pointed out by @YaelDillies

### [2022-02-03 15:03:19](https://github.com/leanprover-community/mathlib/commit/a4d9581)
feat(algebra/group_power/order): add pow_bit0_pos_iff ([#11785](https://github.com/leanprover-community/mathlib/pull/11785))

### [2022-02-03 14:17:31](https://github.com/leanprover-community/mathlib/commit/324d845)
feat(field_theory/krull_topology): defined Krull topology on Galois groups ([#11780](https://github.com/leanprover-community/mathlib/pull/11780))

### [2022-02-03 12:53:15](https://github.com/leanprover-community/mathlib/commit/d6e1c55)
chore(data/polynomial/monic): dedup `degree_map` ([#11792](https://github.com/leanprover-community/mathlib/pull/11792))

### [2022-02-03 12:53:14](https://github.com/leanprover-community/mathlib/commit/2f4f8ad)
feat(set_theory/principal): Principal ordinals are unbounded ([#11755](https://github.com/leanprover-community/mathlib/pull/11755))
Amazingly, this theorem requires no conditions on the operation.

### [2022-02-03 12:12:38](https://github.com/leanprover-community/mathlib/commit/50ee3d5)
feat(ring_theory/roots_of_unity): coe_injective ([#11793](https://github.com/leanprover-community/mathlib/pull/11793))
from flt-regular

### [2022-02-03 11:20:19](https://github.com/leanprover-community/mathlib/commit/934f182)
feat(field_theory/is_alg_closed/classification): Classify algebraically closed fields ([#9370](https://github.com/leanprover-community/mathlib/pull/9370))
The main results here are that two algebraically closed fields with the same characteristic and the same cardinality of transcendence basis are isomorphic. The consequence of this is that two uncountable algebraically closed fields of the same cardinality and characteristic are isomorphic. This has applications in model theory, in particular the Lefschetz principle https://proofwiki.org/wiki/Lefschetz_Principle_(First-Order)

### [2022-02-03 10:20:39](https://github.com/leanprover-community/mathlib/commit/e39f617)
feat(category_theory/linear): compatibility of linear Yoneda ([#11784](https://github.com/leanprover-community/mathlib/pull/11784))

### [2022-02-03 10:20:38](https://github.com/leanprover-community/mathlib/commit/e61ce5d)
chore(category_theory/limits): dualize strong_epi ([#11783](https://github.com/leanprover-community/mathlib/pull/11783))

### [2022-02-03 10:20:37](https://github.com/leanprover-community/mathlib/commit/93f2bdc)
feat(topology/algebra/ordered/monotone_convergence): add `antitone.{ge,le}_of_tendsto` ([#11754](https://github.com/leanprover-community/mathlib/pull/11754))

### [2022-02-03 09:25:26](https://github.com/leanprover-community/mathlib/commit/a483158)
feat(topology/algebra/group): continuity of action of a group on its own coset space ([#11772](https://github.com/leanprover-community/mathlib/pull/11772))
Given a subgroup `Γ` of a topological group `G`, there is an induced scalar action of `G` on the coset space `G ⧸ Γ`, and there is also an induced topology on `G ⧸ Γ`.  We prove that this action is continuous in each variable, and, if the group `G` is locally compact, also jointly continuous.

### [2022-02-03 04:55:55](https://github.com/leanprover-community/mathlib/commit/1816378)
chore(*): golf `by_contra, push_neg` to `by_contra'` ([#11768](https://github.com/leanprover-community/mathlib/pull/11768))

### [2022-02-03 04:21:08](https://github.com/leanprover-community/mathlib/commit/89a3c07)
feat(field_theory/laurent): Laurent expansions of rational functions ([#11199](https://github.com/leanprover-community/mathlib/pull/11199))
Also provide more API for `ratfunc`, lifting homomorphisms of (polynomial to polynomial) to (ratfunc to ratfunc).

### [2022-02-02 21:05:56](https://github.com/leanprover-community/mathlib/commit/7f3590b)
feat(field_theory/minpoly): add a nontriviality lemma ([#11781](https://github.com/leanprover-community/mathlib/pull/11781))

### [2022-02-02 20:04:39](https://github.com/leanprover-community/mathlib/commit/cdad110)
feat(tactic/equiv_rw): enhancing 'equiv_rw' ([#11730](https://github.com/leanprover-community/mathlib/pull/11730))
Expands the `equiv_rw` API by:
* Making it accept a list of equivalences instead of a single one, if intended
* Allowing multiple targets (closes [#2891](https://github.com/leanprover-community/mathlib/pull/2891))
Extra: some optimizations.

### [2022-02-02 16:48:16](https://github.com/leanprover-community/mathlib/commit/41811cd)
feat(number_theory): von Mangoldt function ([#11727](https://github.com/leanprover-community/mathlib/pull/11727))
Defines the von Mangoldt function

### [2022-02-02 16:48:15](https://github.com/leanprover-community/mathlib/commit/c235c61)
refactor(set_theory/ordinal_arithmetic): Simpler `bsup` definition ([#11386](https://github.com/leanprover-community/mathlib/pull/11386))
We also simplify some existing proofs.

### [2022-02-02 16:48:14](https://github.com/leanprover-community/mathlib/commit/4d0b398)
feat(topology/connected): Connectedness of unions of sets ([#10005](https://github.com/leanprover-community/mathlib/pull/10005))
* Add multiple results about when unions of sets are (pre)connected. In particular, the union of connected sets indexed by `ℕ` such that each set intersects the next is connected.
* Remove some `set.` prefixes in the file
* There are two minor fixes in other files, presumably caused by the fact that they now import `order.succ_pred`
* Co-authored by Floris van Doorn fpvdoorn@gmail.com

### [2022-02-02 14:51:44](https://github.com/leanprover-community/mathlib/commit/d6c002c)
feat(group_theory/p_group): finite p-groups with different p have coprime orders ([#11775](https://github.com/leanprover-community/mathlib/pull/11775))

### [2022-02-02 14:51:43](https://github.com/leanprover-community/mathlib/commit/307a456)
refactor(set_theory/ordinal): Add `covariant_class` instances for ordinal addition and multiplication ([#11678](https://github.com/leanprover-community/mathlib/pull/11678))
This replaces the old `add_le_add_left`, `add_le_add_right`, `mul_le_mul_left`, `mul_le_mul_right` theorems.

### [2022-02-02 14:51:42](https://github.com/leanprover-community/mathlib/commit/cd1d839)
feat(order/rel_classes): Unbundled typeclass to state that two relations are the non strict and strict versions ([#11381](https://github.com/leanprover-community/mathlib/pull/11381))
This defines a Prop-valued mixin `is_nonstrict_strict_order α r s` to state `s a b ↔ r a b ∧ ¬ r b a`.
The idea is to allow dot notation for lemmas about the interaction of `⊆` and `⊂` (which currently do not have a `preorder`-like typeclass). Dot notation on each of them is already possible thanks to unbundled relation classes (which allow to state lemmas for both `set` and `finset`).

### [2022-02-02 13:59:38](https://github.com/leanprover-community/mathlib/commit/d002769)
refactor(ring_theory): clean up `algebraic_iff_integral` ([#11773](https://github.com/leanprover-community/mathlib/pull/11773))
The definitions `is_algebraic_iff_integral`, `is_algebraic_iff_integral'` and `algebra.is_algebraic_of_finite` have always been annoying me, so I decided to fix that:
 * The name `is_algebraic_iff_integral'` doesn't explain how it differs from `is_algebraic_iff_integral` (namely that the whole algebra is algebraic, rather than one element), so I renamed it to `algebra.is_algebraic_iff_integral`.
 * The two `is_algebraic_iff_integral` lemmas have an unnecessarily explicit parameter `K`, so I made that implicit
 * `is_algebraic_of_finite` has no explicit parameters (so we always have to use type ascriptions), so I made them explicit
 * Half of the usages of `is_algebraic_of_finite` are of the form `is_algebraic_iff_integral.mp is_algebraic_of_finite`, even though `is_algebraic_of_finite` is proved as `is_algebraic_iff_integral.mpr (some_proof_that_it_is_integral)`, so I split it up into a part showing it is integral, that we can use directly.
As a result, I was able to golf a few proofs.

### [2022-02-02 13:59:37](https://github.com/leanprover-community/mathlib/commit/07d6d17)
refactor(field_theory/is_alg_closed/basic): Generalize alg closures to commutative rings ([#11703](https://github.com/leanprover-community/mathlib/pull/11703))

### [2022-02-02 12:30:43](https://github.com/leanprover-community/mathlib/commit/4db1f96)
chore(algebra/ne_zero): revert transitivity changes ([#11760](https://github.com/leanprover-community/mathlib/pull/11760))
The `trans` methods were a disaster for `flt-regular` - this reverts them unless a better solution can be found.

### [2022-02-02 12:30:42](https://github.com/leanprover-community/mathlib/commit/6c6fbe6)
feat(group_theory/subgroup/basic): normalizer condition implies max subgroups normal ([#11597](https://github.com/leanprover-community/mathlib/pull/11597))

### [2022-02-02 10:56:10](https://github.com/leanprover-community/mathlib/commit/1ed19a9)
feat(group_theory/nilpotent): p-groups are nilpotent ([#11726](https://github.com/leanprover-community/mathlib/pull/11726))

### [2022-02-02 10:56:09](https://github.com/leanprover-community/mathlib/commit/c1d2860)
feat(measure_theory/probability_mass_function): Measures of sets under `pmf` monad operations ([#11613](https://github.com/leanprover-community/mathlib/pull/11613))
This PR adds explicit formulas for the measures of sets under `pmf.pure`, `pmf.bind`, and `pmf.bind_on_support`.

### [2022-02-02 10:56:08](https://github.com/leanprover-community/mathlib/commit/a687cbf)
feat(field_theory/intermediate_field, ring_theory/.., algebra/algebra… ([#11168](https://github.com/leanprover-community/mathlib/pull/11168))
If `E` is an subsemiring/subring/subalgebra/intermediate_field and e is an equivalence of the larger semiring/ring/algebra/field, then e induces an equivalence from E to E.map e. We define this equivalence.

### [2022-02-02 08:53:09](https://github.com/leanprover-community/mathlib/commit/d5d5784)
chore(ring_theory/power_basis): add `simps` ([#11766](https://github.com/leanprover-community/mathlib/pull/11766))
for flt-regular

### [2022-02-02 08:53:07](https://github.com/leanprover-community/mathlib/commit/2fdc151)
refactor(power_series/basic): generalize order to semirings ([#11765](https://github.com/leanprover-community/mathlib/pull/11765))
There are still some TODOs about generalizing statements downstream of this file.

### [2022-02-02 08:53:06](https://github.com/leanprover-community/mathlib/commit/a32b0d3)
feat(group_theory/p_group): p-groups with different p are disjoint ([#11752](https://github.com/leanprover-community/mathlib/pull/11752))

### [2022-02-02 08:53:04](https://github.com/leanprover-community/mathlib/commit/664b5be)
feat(group_theory/subgroup/basic): add commute_of_normal_of_disjoint ([#11751](https://github.com/leanprover-community/mathlib/pull/11751))

### [2022-02-02 08:53:03](https://github.com/leanprover-community/mathlib/commit/a6d70aa)
feat(order/category/*): `order_dual` as an equivalence of categories ([#11743](https://github.com/leanprover-community/mathlib/pull/11743))
For `whatever` a category of orders, define
* `whatever.iso_of_order_iso`: Turns an order isomorphism into an equivalence of objects inside `whatever`
* `whatever.to_dual`: `order_dual` as a functor from `whatever` to itself
* `whatever.dual_equiv`: The equivalence of categories between `whatever` and itself induced by `order_dual` both ways
* `order_iso.dual_dual`: The order isomorphism between `α` and `order_dual (order_dual α)`

### [2022-02-02 07:21:06](https://github.com/leanprover-community/mathlib/commit/400dbb3)
refactor(ring_theory/non_zero_divisors): use fun_like ([#11764](https://github.com/leanprover-community/mathlib/pull/11764))

### [2022-02-02 07:21:05](https://github.com/leanprover-community/mathlib/commit/c8fd7e3)
chore(measure_theory/covering/besicovitch): Weaker import ([#11763](https://github.com/leanprover-community/mathlib/pull/11763))
We relax the `set_theory.cardinal_ordinal` import to the weaker `set_theory.ordinal_arithmetic` import. We also fix some trivial spacing issues in the docs.

### [2022-02-02 07:21:04](https://github.com/leanprover-community/mathlib/commit/a18680a)
chore(topology/continuous_function/ordered): split from `continuous_function/basic` ([#11761](https://github.com/leanprover-community/mathlib/pull/11761))
Split material about orders out from `continuous_function/basic`, to move that file lower down the import hierarchy.

### [2022-02-02 07:21:03](https://github.com/leanprover-community/mathlib/commit/366fd9b)
feat(analysis/special_functions): show (2 / π) * x ≤ sin x ([#11724](https://github.com/leanprover-community/mathlib/pull/11724))
I wasn't entirely sure where to put this - trigonometric/basic is too high on the import graph but here seems to work. 
This is a fairly weak inequality but it can sometimes turn out to be useful, and is important enough to be named!

### [2022-02-02 07:21:01](https://github.com/leanprover-community/mathlib/commit/5c4c1c0)
feat(topology/homotopy): Fundamental groupoid preserves products ([#11459](https://github.com/leanprover-community/mathlib/pull/11459))

### [2022-02-02 06:20:40](https://github.com/leanprover-community/mathlib/commit/fa86370)
chore(*): Golfed some random theorems ([#11769](https://github.com/leanprover-community/mathlib/pull/11769))

### [2022-02-02 05:25:14](https://github.com/leanprover-community/mathlib/commit/8ef783b)
feat(measure_theory/measure): drop more `measurable_set` args ([#11547](https://github.com/leanprover-community/mathlib/pull/11547))
Most notably, in `measure_Union_eq_supr`.

### [2022-02-02 02:57:46](https://github.com/leanprover-community/mathlib/commit/d68b480)
chore(linear_algebra): remove `bilinear_map` from imports in `pi` ([#11767](https://github.com/leanprover-community/mathlib/pull/11767))
Remove `bilinear_map` from imports in `pi`

### [2022-02-01 20:41:27](https://github.com/leanprover-community/mathlib/commit/343cbd9)
feat(sites/sheaf): simple sheaf condition in terms of limit ([#11692](https://github.com/leanprover-community/mathlib/pull/11692))
+ Given a presheaf on a site, construct a simple cone for each sieve. The sheaf condition is equivalent to all these cones being limit cones for all covering sieves of the Grothendieck topology. This is made possible by a series of work that mostly removed universe restrictions on limits.
+ Given a sieve over X : C, the diagram of its associated cone is a functor from the full subcategory of the over category C/X consisting of the arrows in the sieve, constructed from the canonical cocone over `forget : over X ⥤ C` with cone point X, which is only now added to mathlib. This cone is simpler than the multifork cone in [`is_sheaf_iff_multifork`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/sheaf.html#category_theory.presheaf.is_sheaf_iff_multifork). The underlying type of this full subcategory is equivalent to [`grothendieck_topology.cover.arrow`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/grothendieck.html#category_theory.grothendieck_topology.cover.arrow).
+ This limit sheaf condition might be more convenient to use to do sheafification, which has been done by @adamtopaz using the multifork cone before universes are sufficiently generalized for limits, though I haven't thought about it in detail. It may not be worth refactoring sheafification in terms of this sheaf condition, but we might consider using this if we ever want to do sheafification for more general (e.g. non-concrete) value categories. [#11706](https://github.com/leanprover-community/mathlib/pull/11706) is another application.
This is based on a [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/universe.20restriction.20on.20limit/near/260732627) with @adamtopaz.

### [2022-02-01 18:24:10](https://github.com/leanprover-community/mathlib/commit/ec61182)
feat(algebra/group_power): relate square equality and absolute value equality ([#11683](https://github.com/leanprover-community/mathlib/pull/11683))

### [2022-02-01 12:46:25](https://github.com/leanprover-community/mathlib/commit/23e0e29)
chore(*): register global fact instances ([#11749](https://github.com/leanprover-community/mathlib/pull/11749))
We register globally some fact instances which are necessary for integration or euclidean spaces. And also the fact that 2 and 3 are prime. See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/euclidean_space.20error/near/269992165

### [2022-02-01 11:04:30](https://github.com/leanprover-community/mathlib/commit/2508cbd)
feat(model_theory/basic.lean): Elementary embeddings and elementary substructures ([#11089](https://github.com/leanprover-community/mathlib/pull/11089))
Defines elementary embeddings between structures
Defines when substructures are elementary
Provides lemmas about preservation of realizations of terms and formulas under various maps

### [2022-02-01 10:02:45](https://github.com/leanprover-community/mathlib/commit/94a700f)
chore(set_theory/ordinal_arithmetic): Remove redundant explicit argument ([#11757](https://github.com/leanprover-community/mathlib/pull/11757))

### [2022-02-01 10:02:44](https://github.com/leanprover-community/mathlib/commit/ca2a99d)
feat(set_theory/ordinal_arithmetic): Normal functions evaluated at `ω` ([#11687](https://github.com/leanprover-community/mathlib/pull/11687))

### [2022-02-01 09:01:20](https://github.com/leanprover-community/mathlib/commit/cbad62c)
feat(set_theory/{ordinal_arithmetic, cardinal_ordinal}): Ordinals aren't a small type ([#11756](https://github.com/leanprover-community/mathlib/pull/11756))
We substantially golf and extend some results previously in `cardinal_ordinal.lean`.

### [2022-02-01 08:32:51](https://github.com/leanprover-community/mathlib/commit/30dcd70)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11753](https://github.com/leanprover-community/mathlib/pull/11753))
Various lemmas about `zeta`.
From flt-regular.

### [2022-02-01 07:42:44](https://github.com/leanprover-community/mathlib/commit/350ba8d)
feat(data/two_pointing): Two pointings of a type ([#11648](https://github.com/leanprover-community/mathlib/pull/11648))
Define `two_pointing α` as the type of two pointings of `α`. This is a Type-valued structure version of `nontrivial`.

### [2022-02-01 06:40:21](https://github.com/leanprover-community/mathlib/commit/5582d84)
feat(ring_theory/localization): fraction rings of algebraic extensions are algebraic ([#11717](https://github.com/leanprover-community/mathlib/pull/11717))

### [2022-02-01 02:13:10](https://github.com/leanprover-community/mathlib/commit/4b9f048)
feat(set_theory/principal): Define `principal` ordinals ([#11679](https://github.com/leanprover-community/mathlib/pull/11679))
An ordinal `o` is said to be principal or indecomposable under an operation when the set of ordinals less than it is closed under that operation. In standard mathematical usage, this term is almost exclusively used for additive and multiplicative principal ordinals.
For simplicity, we break usual convention and regard 0 as principal.

### [2022-02-01 00:59:42](https://github.com/leanprover-community/mathlib/commit/e37daad)
feat(linear_algebra/sesquilinear_form): Add orthogonality properties ([#10992](https://github.com/leanprover-community/mathlib/pull/10992))
Generalize lemmas about orthogonality from bilinear forms to sesquilinear forms.

### [2022-02-01 00:08:19](https://github.com/leanprover-community/mathlib/commit/b52cb02)
feat(analysis/special_functions/{log, pow}): add log_base ([#11246](https://github.com/leanprover-community/mathlib/pull/11246))
Adds `real.logb`, the log base `b` of `x`, defined as `log x / log b`. Proves that this is related to `real.rpow`.