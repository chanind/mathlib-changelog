### [2021-08-31 23:00:50](https://github.com/leanprover-community/mathlib/commit/065a35d)
feat(algebra/{pointwise,algebra/operations}): add `supr_mul` and `mul_supr` ([#8923](https://github.com/leanprover-community/mathlib/pull/8923))
Requested by @eric-wieser  on Zulip, https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/submodule.2Esupr_mul/near/250122435
and a couple of helper lemmas.

### [2021-08-31 21:31:09](https://github.com/leanprover-community/mathlib/commit/9339006)
feat(algebra/{module/linear_map, algebra/basic}): Add `distrib_mul_action.to_linear_(map|equiv)` and `mul_semiring_action.to_alg_(hom|equiv)` ([#8936](https://github.com/leanprover-community/mathlib/pull/8936))
This adds the following stronger versions of `distrib_mul_action.to_add_monoid_hom`:
* `distrib_mul_action.to_linear_map`
* `distrib_mul_action.to_linear_equiv`
* `mul_semiring_action.to_alg_hom`
* `mul_semiring_action.to_alg_equiv`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/group.20acting.20on.20algebra/near/251372497)

### [2021-08-31 15:40:30](https://github.com/leanprover-community/mathlib/commit/3d6a828)
chore(order/bounded_lattice): dot-notation lemmas ne.bot_lt and ne.lt_top ([#8935](https://github.com/leanprover-community/mathlib/pull/8935))

### [2021-08-31 15:40:29](https://github.com/leanprover-community/mathlib/commit/12bbd53)
chore(topology/metric_space/basic): add `metric.uniform_continuous_on_iff_le` ([#8906](https://github.com/leanprover-community/mathlib/pull/8906))
This is a version of `metric.uniform_continuous_on_iff` with `≤ δ` and
`≤ ε` instead of `< δ` and `< ε`. Also golf the proof of
`metric.uniform_continuous_on_iff`.

### [2021-08-31 15:40:28](https://github.com/leanprover-community/mathlib/commit/603a606)
feat(measure_theory/hausdorff_measure): dimH and Hölder/Lipschitz maps ([#8361](https://github.com/leanprover-community/mathlib/pull/8361))
* expand module docs;
* prove that a Lipschitz continuous map does not increase Hausdorff measure and Hausdorff dimension of sets;
* prove similar lemmas about Hölder continuous and antilipschitz maps;
* add convenience lemmas for some bundled types and for `Cⁿ` smooth maps;
* Hausdorff dimension of `ℝⁿ` equals `n`;
* prove a baby version of Sard's theorem: if `f : E → F` is a `C¹` smooth map between normed vector spaces such that `finrank ℝ E < finrank ℝ F`, then `(range f)ᶜ` is dense.

### [2021-08-31 13:58:34](https://github.com/leanprover-community/mathlib/commit/d9b2db9)
chore(group_theory/submonoid/center): fix typo and extend docstring ([#8937](https://github.com/leanprover-community/mathlib/pull/8937))

### [2021-08-31 10:54:15](https://github.com/leanprover-community/mathlib/commit/ab967d2)
feat(group_theory/submonoid): center of a submonoid ([#8921](https://github.com/leanprover-community/mathlib/pull/8921))
This adds `set.center`, `submonoid.center`, `subsemiring.center`, and `subring.center`, to complement the existing `subgroup.center`.
This ran into a timeout, so had to squeeze some `simp`s in an unrelated file.

### [2021-08-31 09:04:38](https://github.com/leanprover-community/mathlib/commit/6b63c03)
fix(order/rel_classes): remove looping instance ([#8931](https://github.com/leanprover-community/mathlib/pull/8931))
This instance causes loop with `is_total_preorder.to_is_total`, and was unused in the library.
Caught by the new linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932)).

### [2021-08-31 09:04:37](https://github.com/leanprover-community/mathlib/commit/53f074c)
fix(data/complex/basic): better formulas for nsmul and gsmul on complex to fix a diamond ([#8928](https://github.com/leanprover-community/mathlib/pull/8928))
As diagnosed by @eric-wieser in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/diamond.20in.20data.2Ecomplex.2Emodule/near/250318167
After the PR,
```lean
example :
  (sub_neg_monoid.has_scalar_int : has_scalar ℤ ℂ) = (complex.has_scalar : has_scalar ℤ ℂ) :=
rfl
```
works fine, while it fails on current master.

### [2021-08-31 09:04:36](https://github.com/leanprover-community/mathlib/commit/c04e8a4)
feat(logic/basic): equivalence of by_contra and choice ([#8912](https://github.com/leanprover-community/mathlib/pull/8912))
Based on an email suggestion from Freek Wiedijk: `classical.choice` is equivalent to the following Type-valued variation on `by_contradiction`:
```lean
axiom classical.by_contradiction' {α : Sort*} : ¬ (α → false) → α
```

### [2021-08-31 09:04:35](https://github.com/leanprover-community/mathlib/commit/1c13454)
feat(algebraic_geometry): Restriction of locally ringed spaces ([#8809](https://github.com/leanprover-community/mathlib/pull/8809))
Proves that restriction of presheafed spaces doesn't change the stalks and defines the restriction of a locally ringed space along an open embedding.

### [2021-08-31 07:22:54](https://github.com/leanprover-community/mathlib/commit/1dbd561)
refactor(order/atoms): reorder arguments of `is_simple_lattice.fintype` ([#8933](https://github.com/leanprover-community/mathlib/pull/8933))
Previously, this instance would first look for `decidable_eq` instances and after that for `is_simple_lattice` instances. The latter has only 4 instances, while the former takes hundreds of steps. Reordering the arguments makes a lot of type-class searches fail a lot quicker.
Caught by the new linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932)).

### [2021-08-31 02:54:16](https://github.com/leanprover-community/mathlib/commit/22a297c)
feat(algebra/module/prod,pi): instances for actions with zero ([#8929](https://github.com/leanprover-community/mathlib/pull/8929))

### [2021-08-31 01:35:58](https://github.com/leanprover-community/mathlib/commit/f4d7205)
chore(measure_theory/*): rename `probability_measure` and `finite_measure` ([#8831](https://github.com/leanprover-community/mathlib/pull/8831))
Renamed to `is_probability_measure` and `is_finite_measure`, respectively.  Also, `locally_finite_measure` becomes `is_locally_finite_measure`. See
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238337.20Weak.20convergence

### [2021-08-30 18:18:38](https://github.com/leanprover-community/mathlib/commit/6adb5e8)
feat(topology/algebra/ordered): monotone convergence in pi types ([#8841](https://github.com/leanprover-community/mathlib/pull/8841))
* add typeclasses `Sup_convergence_class` and `Inf_convergence_class`
* reformulate theorems about monotone convergence in terms of these typeclasses;
* provide instances for a linear order with order topology, for products, and for pi types.

### [2021-08-30 16:14:57](https://github.com/leanprover-community/mathlib/commit/4a65197)
chore(algebra/direct_sum/algebra): add missing rfl lemmas ([#8924](https://github.com/leanprover-community/mathlib/pull/8924))
I realized I was resorting to nasty unfolding to get these mid-proof

### [2021-08-30 16:14:56](https://github.com/leanprover-community/mathlib/commit/aa0694a)
fix(data/set/finite): drop {α : Type}, fixes universe issue ([#8922](https://github.com/leanprover-community/mathlib/pull/8922))

### [2021-08-30 16:14:55](https://github.com/leanprover-community/mathlib/commit/ad7519a)
doc(tactic/lint): instructions on fails_quickly failure ([#8910](https://github.com/leanprover-community/mathlib/pull/8910))
* Also set `is_fast` to `tt`, since it takes ~10s on all of mathlib.

### [2021-08-30 16:14:54](https://github.com/leanprover-community/mathlib/commit/b3807ee)
chore(data/finset/basic): lemmas about `(range n).nonempty` ([#8905](https://github.com/leanprover-community/mathlib/pull/8905))
Add `finset.nonempty_range_iff`, `finset.range_eq_empty_iff`, and
`range.nonempty_range_succ`.

### [2021-08-30 14:54:37](https://github.com/leanprover-community/mathlib/commit/1e89df2)
chore(algebra/monoid_algebra): convert a filename prefix into a folder ([#8925](https://github.com/leanprover-community/mathlib/pull/8925))
This moves:
* `algebra.monoid_algebra` to `algebra.monoid_algebra.basic`
* `algebra.monoid_algebra_to_direct_sum` to `algebra.monoid_algebra.to_direct_sum`

### [2021-08-30 13:16:49](https://github.com/leanprover-community/mathlib/commit/98466d2)
feat(algebra/direct_sum): graded algebras ([#8783](https://github.com/leanprover-community/mathlib/pull/8783))
This provides a `direct_sum.galgebra` structure on top of the existing `direct_sum.gmonoid` structure.
This typeclass is used to provide an `algebra R (⨁ i, A i)` instance.
This also renames and improves the stateement of `direct_sum.module.ext` to `direct_sum.linear_map_ext` and adds `direect_sum.ring_hom_ext` and `direct_sum.alg_hom_ext` to match.

### [2021-08-29 18:50:41](https://github.com/leanprover-community/mathlib/commit/2bae06a)
fix(ring_theory/polynomial/homogeneous): spelling mistake in `homogeneous` ([#8914](https://github.com/leanprover-community/mathlib/pull/8914))

### [2021-08-29 14:08:26](https://github.com/leanprover-community/mathlib/commit/395bb6c)
feat(algebraic_geometry): Lift isomorphism of sheafed spaces to locally ringed spaces ([#8887](https://github.com/leanprover-community/mathlib/pull/8887))
Adds the fact that an isomorphism of sheafed spaces can be lifted to an isomorphism of locally ringed spaces. The main ingredient is the fact that stalk maps of isomorphisms are again isomorphisms.
In particular, this implies that the forgetful functor `LocallyRingedSpace ⥤ SheafedSpace CommRing` reflects isomorphisms.

### [2021-08-28 19:59:37](https://github.com/leanprover-community/mathlib/commit/d75a2d9)
refactor(data/set/finite): use `[fintype (plift ι)]` in `finite_Union` ([#8872](https://github.com/leanprover-community/mathlib/pull/8872))
This way we can use `finite_Union` instead of `finite_Union_Prop`.

### [2021-08-28 18:30:09](https://github.com/leanprover-community/mathlib/commit/db06b5a)
feat(group_theory/perm/cycle_type): Fixed points of permutations of prime order ([#8832](https://github.com/leanprover-community/mathlib/pull/8832))
A few basic lemmas about fixed points of permutations of prime order.

### [2021-08-28 18:30:08](https://github.com/leanprover-community/mathlib/commit/e824b88)
refactor(category_theory/limits/final): Symmetric API for final and initial functors ([#8808](https://github.com/leanprover-community/mathlib/pull/8808))
Dualise the API for cofinal functors to symmetrically support final and initial functors.
This PR renames `cofinal` functors to `final` functors.

### [2021-08-28 18:30:07](https://github.com/leanprover-community/mathlib/commit/14a992b)
chore(data/set_like): some additional documentation ([#8765](https://github.com/leanprover-community/mathlib/pull/8765))
Gives some more explanation for `set_like` and what it does and is for.

### [2021-08-28 17:56:07](https://github.com/leanprover-community/mathlib/commit/0b48570)
feat(group_theory/nilpotent): add subgroups of nilpotent group are nilpotent ([#8854](https://github.com/leanprover-community/mathlib/pull/8854))

### [2021-08-28 16:48:45](https://github.com/leanprover-community/mathlib/commit/1aaff8d)
feat(measure_theory/decomposition/lebesgue): Lebesgue decomposition for sigma-finite measures ([#8875](https://github.com/leanprover-community/mathlib/pull/8875))
This PR shows sigma-finite measures `have_lebesgue_decomposition`. With this instance, `absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq` will provide the Radon-Nikodym theorem for sigma-finite measures.

### [2021-08-28 09:42:18](https://github.com/leanprover-community/mathlib/commit/42b5e80)
feat(data/polynomial/basic): monomial_eq_zero_iff ([#8897](https://github.com/leanprover-community/mathlib/pull/8897))
Via a new `monomial_injective`.

### [2021-08-28 08:03:49](https://github.com/leanprover-community/mathlib/commit/8ee05e9)
feat(data/nat/log): Ceil log ([#8764](https://github.com/leanprover-community/mathlib/pull/8764))
Defines the upper natural log, which is the least `k` such that `n ≤ b^k`.
Also expand greatly the docs of `data.nat.multiplicity`, in particular to underline that it proves Legendre's theorem.

### [2021-08-28 02:16:20](https://github.com/leanprover-community/mathlib/commit/d3c592f)
chore(scripts): update nolints.txt ([#8899](https://github.com/leanprover-community/mathlib/pull/8899))
I am happy to remove some nolints for you!

### [2021-08-28 01:06:00](https://github.com/leanprover-community/mathlib/commit/0fd51b1)
feat(data/real/irrational): exists irrational between any two distinct rationals and reals ([#8753](https://github.com/leanprover-community/mathlib/pull/8753))
Did not find these proofs in `data/real/irrational`, seemed like they belong here.  Just proving the standard facts about irrationals between rats and reals.  I am using these lemmas in a repo about the Thomae's function.

### [2021-08-27 17:22:21](https://github.com/leanprover-community/mathlib/commit/2eaec05)
feat(ring_theory): define integrally closed domains ([#8893](https://github.com/leanprover-community/mathlib/pull/8893))
In this follow-up to [#8882](https://github.com/leanprover-community/mathlib/pull/8882), we define the notion of an integrally closed domain `R`, which contains all integral elements of `Frac(R)`.
We show the equivalence to `is_integral_closure R R K` for a field of fractions `K`.
We provide instances for `is_dedekind_domain`s, `unique_fractorization_monoid`s, and to the integers of a valuation. In particular, the rational root theorem provides a proof that `ℤ` is integrally closed.

### [2021-08-27 15:28:35](https://github.com/leanprover-community/mathlib/commit/c4cf4c2)
feat(algebra/polynomial/big_operators): coeff of sums and prods of polynomials ([#8680](https://github.com/leanprover-community/mathlib/pull/8680))
Additionally, provide results for degree and nat_degree over lists,
which generalize away from requiring commutativity.

### [2021-08-27 14:36:55](https://github.com/leanprover-community/mathlib/commit/dcd60e2)
feat(ring_theory/trace): the trace form is nondegenerate ([#8777](https://github.com/leanprover-community/mathlib/pull/8777))
This PR shows the determinant of the trace form is nonzero over a finite separable field extension. This is an important ingredient in showing the integral closure of a Dedekind domain in a finite separable extension is again a Dedekind domain, i.e. that rings of integers are Dedekind domains. We extend the results of [#8762](https://github.com/leanprover-community/mathlib/pull/8762) to write the trace form as a Vandermonde matrix to get a nice expression for the determinant, then use separability to show this value is nonzero.

### [2021-08-27 14:36:54](https://github.com/leanprover-community/mathlib/commit/7f25698)
feat(analysis/complex/isometry): Show that certain complex isometries are not equal ([#8646](https://github.com/leanprover-community/mathlib/pull/8646))
1. Lemma `reflection_rotation` proves that rotation by `(a : circle)` is not equal to reflection over the x-axis (i.e, `conj_lie`).  
2. Lemma `rotation_injective` proves that rotation by different `(a b: circle)` are not the same,(i.e, `rotation` is injective).
Co-authored by Kyle Miller

### [2021-08-27 14:02:35](https://github.com/leanprover-community/mathlib/commit/7cfc987)
feat(measure_theory/decomposition/radon_nikodym): the Radon-Nikodym theorem ([#8763](https://github.com/leanprover-community/mathlib/pull/8763))
The Radon-Nikodym theorem 🎉

### [2021-08-27 12:25:45](https://github.com/leanprover-community/mathlib/commit/023a816)
feat(algebra): define a bundled type of absolute values ([#8881](https://github.com/leanprover-community/mathlib/pull/8881))
The type `absolute_value R S` is a bundled version of the typeclass `is_absolute_value R S` defined in `data/real/cau_seq.lean` (why was it defined there?), putting both in one file `algebra/absolute_value.lean`. The lemmas from `is_abs_val` have been copied mostly literally, with weakened assumptions when possible. Maps between the bundled and unbundled versions are also available.
We also define `absolute_value.abs` that represents the "standard" absolute value `abs`.
The point of this PR is both to modernize absolute values into bundled structures, and to make it easier to extend absolute values to represent "absolute values respecting the Euclidean domain structure", and from there "absolute values that show the class group is finite".

### [2021-08-27 11:47:58](https://github.com/leanprover-community/mathlib/commit/a327851)
feat(ring_theory): a typeclass `is_integral_closure` ([#8882](https://github.com/leanprover-community/mathlib/pull/8882))
The typeclass `is_integral_closure A R B` states `A` is the integral closure of `R` in `B`, i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
We also show that any integral extension of `R` contained in `B` is contained in `A`, and the integral closure is unique up to isomorphism.
This was suggested in the review of [#8701](https://github.com/leanprover-community/mathlib/pull/8701), in order to define a characteristic predicate for rings of integers.

### [2021-08-27 10:03:00](https://github.com/leanprover-community/mathlib/commit/88e47d7)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate_mul_distrib_aux ([#8681](https://github.com/leanprover-community/mathlib/pull/8681))
We prove towards the fact that the adjugate of a matrix distributes
over the product. The current proof assumes regularity of the matrices.
In the general case, this hypothesis is not required, but this lemma
will be crucial in a follow-up PR
which has to use polynomial matrices for the general case.
Additionally, we provide many API lemmas for det, cramer, 
nonsing_inv, and adjugate.

### [2021-08-27 08:03:55](https://github.com/leanprover-community/mathlib/commit/0c50326)
refactor(*): use `is_empty` instead of `not (nonempty α)` ([#8858](https://github.com/leanprover-community/mathlib/pull/8858))
`eq_empty_of_not_nonempty` gets dropped in favour of `eq_empty_of_is_empty`.

### [2021-08-27 07:04:59](https://github.com/leanprover-community/mathlib/commit/fe13f03)
feat(category_theory/structured_arrow): Duality between structured and costructured arrows ([#8807](https://github.com/leanprover-community/mathlib/pull/8807))
This PR formally sets up the duality of structured and costructured arrows as equivalences of categories. Unfortunately, the code is a bit repetitive, as the four functors introduced all follow a similar pattern, which I wasn't able to abstract out. Suggestions are welcome!

### [2021-08-27 06:31:17](https://github.com/leanprover-community/mathlib/commit/4705a6b)
doc(ring_theory/hahn_series): Update Hahn Series docstring ([#8883](https://github.com/leanprover-community/mathlib/pull/8883))
Updates `ring_theory/hahn_series` docstring to remove outdated TODOs

### [2021-08-27 05:01:51](https://github.com/leanprover-community/mathlib/commit/a9de197)
feat(algebra/big_operators/basic): add `prod_dite_of_false`, `prod_dite_of_true` ([#8865](https://github.com/leanprover-community/mathlib/pull/8865))
The proofs are not mine cf [Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60prod_dite_of_true.60)

### [2021-08-27 03:31:00](https://github.com/leanprover-community/mathlib/commit/bcd5cd3)
feat(algebra/pointwise): add to_additive attributes for pointwise smul ([#8878](https://github.com/leanprover-community/mathlib/pull/8878))
I wanted this to generalize some definitions in [#2819](https://github.com/leanprover-community/mathlib/pull/2819) but it should be independent.

### [2021-08-27 02:26:16](https://github.com/leanprover-community/mathlib/commit/bb4026f)
chore(scripts): update nolints.txt ([#8886](https://github.com/leanprover-community/mathlib/pull/8886))
I am happy to remove some nolints for you!

### [2021-08-27 00:42:51](https://github.com/leanprover-community/mathlib/commit/11e3047)
feat(algebra/ordered_monoid): min_top_(left|right) ([#8880](https://github.com/leanprover-community/mathlib/pull/8880))

### [2021-08-26 19:37:09](https://github.com/leanprover-community/mathlib/commit/e290569)
feat(data/nat/totient): add nat.totient_prime_iff ([#8833](https://github.com/leanprover-community/mathlib/pull/8833))

### [2021-08-26 19:37:08](https://github.com/leanprover-community/mathlib/commit/080362d)
feat(data/finset/pi_induction): induction on `Π i, finset (α i)` ([#8794](https://github.com/leanprover-community/mathlib/pull/8794))

### [2021-08-26 19:37:07](https://github.com/leanprover-community/mathlib/commit/83490fc)
feat(data/multiset/basic): add some lemmas ([#8787](https://github.com/leanprover-community/mathlib/pull/8787))

### [2021-08-26 18:49:05](https://github.com/leanprover-community/mathlib/commit/d9f4713)
feat(ring_theory/trace): Tr(x) is the sum of embeddings σ x into an algebraically closed field ([#8762](https://github.com/leanprover-community/mathlib/pull/8762))
The point of this PR is to provide the other formulation of "the trace of `x` is the sum of its conjugates", alongside `trace_eq_sum_roots`, namely `trace_eq_sum_embeddings`. We do so by exploiting the bijection between conjugate roots to `x : L` over `K` and embeddings of `K(x)`, then counting the number of embeddings of `x` to go to the whole of `L`.

### [2021-08-26 16:48:12](https://github.com/leanprover-community/mathlib/commit/5a2082d)
chore(category/grothendieck): split definition to avoid timeout ([#8871](https://github.com/leanprover-community/mathlib/pull/8871))
Helpful for [#8807](https://github.com/leanprover-community/mathlib/pull/8807).

### [2021-08-26 16:48:10](https://github.com/leanprover-community/mathlib/commit/9038709)
feat(analysis/normed_space/inner_product): multiplication by I is real-orthogonal ([#8852](https://github.com/leanprover-community/mathlib/pull/8852))

### [2021-08-26 16:48:09](https://github.com/leanprover-community/mathlib/commit/5bd69fd)
feat(ring_theory/ideal/local_ring): Isomorphisms are local ([#8850](https://github.com/leanprover-community/mathlib/pull/8850))
Adds the fact that isomorphisms (and ring equivs) are local ring homomorphisms.

### [2021-08-26 16:48:08](https://github.com/leanprover-community/mathlib/commit/5afdaea)
feat(data/fin): reverse_induction ([#8845](https://github.com/leanprover-community/mathlib/pull/8845))

### [2021-08-26 16:48:07](https://github.com/leanprover-community/mathlib/commit/678a2b5)
feat(data/list,multiset,finset): monotone_filter_(left|right) ([#8842](https://github.com/leanprover-community/mathlib/pull/8842))

### [2021-08-26 16:48:06](https://github.com/leanprover-community/mathlib/commit/8e87f42)
feat(tactic/lint/misc): Add syntactic tautology linter ([#8821](https://github.com/leanprover-community/mathlib/pull/8821))
Add a linter that checks whether a lemma is a declaration that `∀ a b ... z,e₁ = e₂` where `e₁` and `e₂` are equal
exprs, we call declarations of this form syntactic tautologies.
Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving basic facts
with rfl when elaboration results in a different term than the user intended.
@PatrickMassot suggested this at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/syntactic.20tautology.20linter/near/250267477.
The found problems are fixed in [#8811](https://github.com/leanprover-community/mathlib/pull/8811).

### [2021-08-26 13:06:18](https://github.com/leanprover-community/mathlib/commit/70e1f9a)
feat(data/fin): add_cases ([#8876](https://github.com/leanprover-community/mathlib/pull/8876))

### [2021-08-26 13:06:17](https://github.com/leanprover-community/mathlib/commit/976e930)
chore(archive/imo/README): whitespace breaks links ([#8874](https://github.com/leanprover-community/mathlib/pull/8874))

### [2021-08-26 13:06:15](https://github.com/leanprover-community/mathlib/commit/0d07d04)
chore(data/set): add a few lemmas and `@[simp]` attrs ([#8873](https://github.com/leanprover-community/mathlib/pull/8873))

### [2021-08-26 13:06:14](https://github.com/leanprover-community/mathlib/commit/1f13610)
feat(*): remove the `fintype` requirement from matrices. ([#8810](https://github.com/leanprover-community/mathlib/pull/8810))
For historical reasons, `matrix` has always had `fintype` attached to it. I remove this artificial limitation, but with a big caveat; multiplication is currently defined in terms of the dot product, which requires finiteness; therefore, any multiplicative structure on matrices currently requires fintypes. This can be removed in future contributions, however.

### [2021-08-26 11:17:26](https://github.com/leanprover-community/mathlib/commit/0861cc7)
refactor(*): move code about `ulift`/`plift` ([#8863](https://github.com/leanprover-community/mathlib/pull/8863))
* move old file about `ulift`/`plift` from `data.ulift` to `control.ulift`;
* redefine `ulift.map` etc without pattern matching;
* create new `data.ulift`, move `ulift.subsingleton` etc from `data.equiv.basic` to this file;
* add `ulift.is_empty` and `plift.is_empty`;
* add `ulift.exists`, `plift.exists`, `ulift.forall`, and `plift.forall`;
* rename `equiv.nonempty_iff_nonempty` to `equiv.nonempty_congr` to match `equiv.subsingleton_congr` etc;
* rename `plift.fintype` to `plift.fintype_Prop`, add a new `plift.fintype`.

### [2021-08-26 11:17:25](https://github.com/leanprover-community/mathlib/commit/2a6fef3)
refactor(order/filter/bases): allow `ι : Sort*` ([#8856](https://github.com/leanprover-community/mathlib/pull/8856))
* `ι` in `filter.has_basis (l : filter α) (p : ι → Prop) (s : ι → set )` now can be a `Sort *`;
* some lemmas now have "primed" versions that use `pprod` instead of `prod`;
* new lemma: `filter.has_basis_supr`.
I also added a few missing lemmas to `data.pprod` and golfed a couple of proofs.

### [2021-08-26 11:17:24](https://github.com/leanprover-community/mathlib/commit/3287c94)
refactor(tactic/ext): simplify ext attribute ([#8785](https://github.com/leanprover-community/mathlib/pull/8785))
This simplifies the `ext` attribute from taking a list with `*`, `(->)` and names to just `@[ext]` or `@[ext ident]`. The `(->)` option is only used once, in the file that declares the `ext` attribute itself, so it's not worth the parser complexity. The ability to remove attributes with `@[ext -foo]` is removed, but I don't think it was tested because it was never used and doesn't work anyway.
Also fixes an issue with ext attributes being quadratic (in the number of ext attributes applied), and also makes `ext` attributes remove themselves (the real work of ext attributes is done by two internal attributes `_ext_core` and `_ext_lemma_core`), so that they don't pollute `#print` output. Before:
```lean
#print funext
@[_ext_lemma_core, ext list.cons.{0} ext_param_type (sum.inr.{0 0} (option.{0} name) (option.{0} name) (option.some.{0} name (name.mk_numeral (unsigned.of_nat' (has_zero.zero.{0} nat nat.has_zero)) name.anonymous))) (list.cons.{0} ext_param_type (sum.inr.{0 0} (option.{0} name) (option.{0} name) (option.some.{0} name (name.mk_string "thunk" name.anonymous))) (list.nil.{0} ext_param_type)), intro!]
theorem funext : ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂ :=
```
After:
```lean
#print funext
@[_ext_lemma_core, intro!]
theorem funext : ∀ {α : Sort u} {β : α → Sort v} {f₁ f₂ : Π (x : α), β x}, (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂ :=
```

### [2021-08-26 11:17:23](https://github.com/leanprover-community/mathlib/commit/a4b33d3)
feat(data/matrix/kronecker): add two reindex lemmas ([#8774](https://github.com/leanprover-community/mathlib/pull/8774))
Added two lemmas `kronecker_map_reindex_right` and `kronecker_map_reindex_left` (used in LTE) and moved the two `assoc` lemmas some lines up, before the `linear` section, because they are unrelated to any linearity business.

### [2021-08-26 11:17:22](https://github.com/leanprover-community/mathlib/commit/3e5bbca)
feat(field_theory/intermediate_field): generalize `algebra` instances ([#8761](https://github.com/leanprover-community/mathlib/pull/8761))
The `algebra` and `is_scalar_tower` instances for `intermediate_field` are (again) as general as those for `subalgebra`.

### [2021-08-26 11:17:21](https://github.com/leanprover-community/mathlib/commit/2c698bd)
docs(set_theory/zfc): add module docstring and missing def docstrings ([#8744](https://github.com/leanprover-community/mathlib/pull/8744))

### [2021-08-26 10:02:38](https://github.com/leanprover-community/mathlib/commit/2e1e98f)
feat(linear_algebra/bilinear_form): bilinear forms with `det ≠ 0` are nonsingular ([#8824](https://github.com/leanprover-community/mathlib/pull/8824))
In particular, the trace form is such a bilinear form (see [#8777](https://github.com/leanprover-community/mathlib/pull/8777)).

### [2021-08-26 10:02:37](https://github.com/leanprover-community/mathlib/commit/147af57)
feat(category_theory/is_connected): The opposite of a connected category is connected ([#8806](https://github.com/leanprover-community/mathlib/pull/8806))

### [2021-08-26 10:02:36](https://github.com/leanprover-community/mathlib/commit/058f639)
feat(data/equiv/fin): fin_succ_equiv_last ([#8805](https://github.com/leanprover-community/mathlib/pull/8805))
This commit changes the type of `fin_succ_equiv'`. `fin_succ_equiv' i` used to take an argument of type `fin n` which was 
strange and it now takes an argument of type `fin (n + 1)` meaning it is now possible to send `fin.last n` to `none` if desired. I also defined `fin.succ_equiv_last`, the canonical equiv `fin (n + 1)` to `option (fin n)` sending `fin.last` to `none`.

### [2021-08-26 09:18:22](https://github.com/leanprover-community/mathlib/commit/94d4a32)
feat(linear_algebra/bilinear_form): the dual basis for a nondegenerate bilin form ([#8823](https://github.com/leanprover-community/mathlib/pull/8823))
Let `B` be a nondegenerate (symmetric) bilinear form on a finite-dimensional vector space `V` and `b` a basis on `V`. Then there is a "dual basis" `d` such that `d.repr x i = B x (b i)` and `B (d i) (b j) = B (b i) (d j) = if i = j then 1 else 0`.
In a follow-up PR, we'll show that the trace form for `L / K` produces a dual basis consisting only of elements integral over the ring of integers of `K`.

### [2021-08-26 07:01:23](https://github.com/leanprover-community/mathlib/commit/acbe935)
chore(topology/metric_space): add 2 lemmas, golf ([#8861](https://github.com/leanprover-community/mathlib/pull/8861))

### [2021-08-26 07:01:22](https://github.com/leanprover-community/mathlib/commit/9438552)
feat(data/fin): cast_add_lt ([#8830](https://github.com/leanprover-community/mathlib/pull/8830))

### [2021-08-26 07:01:21](https://github.com/leanprover-community/mathlib/commit/6c6fc02)
feat(data/fin): cast_add_right ([#8829](https://github.com/leanprover-community/mathlib/pull/8829))

### [2021-08-26 07:01:20](https://github.com/leanprover-community/mathlib/commit/bafeccf)
feat(data/fin): fin.succ_cast_succ ([#8828](https://github.com/leanprover-community/mathlib/pull/8828))

### [2021-08-26 07:01:19](https://github.com/leanprover-community/mathlib/commit/cb1932d)
feat(data/complex/exponential): bound on exp for arbitrary arguments ([#8667](https://github.com/leanprover-community/mathlib/pull/8667))
This PR is for a new lemma (currently called `exp_bound'`) which proves `exp x` is close to its `n`th degree taylor expansion for sufficiently large `n`. Unlike the previous bound, this lemma can be instantiated on any real `x` rather than just `x` with absolute value less than or equal to 1. I am separating this lemma out from [#8002](https://github.com/leanprover-community/mathlib/pull/8002) because I think it stands on its own.
The last time I checked it was sorry free - but that was before I merged with master and moved it to a different branch. It may also benefit from a little golfing.
There are a few lemmas I proved as well to support this - one about the relative size of factorials and a few about sums of geometric sequences. The ~~geometric series ones should probably be generalized and moved to another file~~ this generalization sort of exists and is in the algebra.geom_sum file. I didn't find it initially since I was searching for "geometric" not "geom".

### [2021-08-26 05:17:35](https://github.com/leanprover-community/mathlib/commit/fe47777)
feat(analysis/complex/upper_half_plane): new file ([#8377](https://github.com/leanprover-community/mathlib/pull/8377))
This file defines `upper_half_plane` to be the upper half plane in `ℂ`.
We furthermore equip it with the structure of an `SL(2,ℝ)` action by
fractional linear transformations.
Co-authored by Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
Co-authored by Marc Masdeu <marc.masdeu@gmail.com>

### [2021-08-26 03:51:48](https://github.com/leanprover-community/mathlib/commit/7e781a8)
chore(*): Fix syntactic tautologies ([#8811](https://github.com/leanprover-community/mathlib/pull/8811))
Fix a few lemmas that were accidentally tautological in the sense that they were equations with syntactically equal LHS and RHS.
A linter will be added in a second PR, for now we just fix the found issues.
It would be great if a category expert like @semorrison would check the category ones, as its unclear to me which direction they are meant to go.
As pointed out by @PatrickMassot on Zulip https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/syntactic.20tautology.20linter/near/250267477.
Thanks to @eric-wieser for helping figure out the corrected versions.

### [2021-08-26 02:42:53](https://github.com/leanprover-community/mathlib/commit/daf0d02)
feat(archive/imo): README.md ([#8799](https://github.com/leanprover-community/mathlib/pull/8799))
Proposed text for a README file in the IMO directory. I don't think we have a particular problem with IMO submissions, but thought it could be useful to set the parameters around IMO problems, as it's never been completely clear they belong in mathlib.
If we merge this, or something like it, I'll link #imo on Zulip to it.

### [2021-08-25 21:27:03](https://github.com/leanprover-community/mathlib/commit/8befa82)
feat(group_theory/perm/list): lemmas on form_perm ([#8848](https://github.com/leanprover-community/mathlib/pull/8848))

### [2021-08-25 21:27:01](https://github.com/leanprover-community/mathlib/commit/49af34d)
feat(group_theory/perm/cycles): same_cycle and cycle_of lemmas ([#8835](https://github.com/leanprover-community/mathlib/pull/8835))

### [2021-08-25 18:32:55](https://github.com/leanprover-community/mathlib/commit/40bd7c6)
feat(data/nat/modeq): Rotating list.repeat ([#8817](https://github.com/leanprover-community/mathlib/pull/8817))
Some consequences of `list.rotate_eq_self_iff_eq_repeat`.

### [2021-08-25 18:32:54](https://github.com/leanprover-community/mathlib/commit/c544742)
feat(linear_algebra/finite_dimensional): add finrank_map_le ([#8815](https://github.com/leanprover-community/mathlib/pull/8815))

### [2021-08-25 18:32:53](https://github.com/leanprover-community/mathlib/commit/6a41805)
chore(group_theory/group_action/basic): `to_additive` attributes throughout ([#8814](https://github.com/leanprover-community/mathlib/pull/8814))

### [2021-08-25 18:32:52](https://github.com/leanprover-community/mathlib/commit/b6e6c84)
feat(data/finset/basic): to_list ([#8797](https://github.com/leanprover-community/mathlib/pull/8797))
Produce a list of the elements of a finite set using choice.

### [2021-08-25 18:32:50](https://github.com/leanprover-community/mathlib/commit/aca0874)
chore(algebra/direct_sum): Move all the algebraic structure on `direct_sum` into a single directory ([#8771](https://github.com/leanprover-community/mathlib/pull/8771))
This ends up splitting one file in two, but all the contents are just moved.

### [2021-08-25 18:32:49](https://github.com/leanprover-community/mathlib/commit/df8818c)
feat(data/nat/multiplicity): bound on the factorial multiplicity ([#8767](https://github.com/leanprover-community/mathlib/pull/8767))
This proves `multiplicity p n! ≤ n/(p - 1)`, for `p` prime and `n` natural.

### [2021-08-25 18:32:48](https://github.com/leanprover-community/mathlib/commit/301eb10)
feat(data/polynomial/monic): monic.is_regular ([#8679](https://github.com/leanprover-community/mathlib/pull/8679))
This golfs/generalizes some proofs.
Additionally, provide some helper API for `is_regular`,
for non-zeros in domains,
and for smul of units.

### [2021-08-25 17:03:35](https://github.com/leanprover-community/mathlib/commit/b364cfc)
feat(linear_algebra/basis): if `R ≃ R'`, map a basis for `R`-module `M` to `R'`-module `M` ([#8699](https://github.com/leanprover-community/mathlib/pull/8699))
If `R` and `R'` are isomorphic rings that act identically on a module `M`, then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

### [2021-08-25 15:26:51](https://github.com/leanprover-community/mathlib/commit/0ad5abc)
chore(data/set/finite): golf 2 proofs ([#8862](https://github.com/leanprover-community/mathlib/pull/8862))
Also add `finset.coe_emb`.

### [2021-08-25 12:58:19](https://github.com/leanprover-community/mathlib/commit/97c327c)
feat(tactic/suggest): suggest using X, to filter results ([#8819](https://github.com/leanprover-community/mathlib/pull/8819))
You can now write `suggest using X`, to only give suggestions which make use of the local hypothesis `X`.
Similarly `suggest using X Y Z` for multiple hypotheses. `library_search using X` is also enabled.
This makes `suggest` much more useful. Previously
```
example (P Q : list ℕ) : list ℕ := by suggest
```
would have just said `exact P`.
Now you can write
```
example (P Q : list ℕ) : list ℕ := by suggest using P Q
```
and get:
```
Try this: exact list.diff P Q
Try this: exact list.union P Q
Try this: exact list.inter P Q
Try this: exact list.append P Q
Try this: exact list.bag_inter P Q
Try this: exact list.remove_all P Q
Try this: exact list.reverse_core P Q
```

### [2021-08-25 06:39:27](https://github.com/leanprover-community/mathlib/commit/26a3286)
fix(data/set/lattice): lemmas about `Union`/`Inter` over `p : Prop` ([#8860](https://github.com/leanprover-community/mathlib/pull/8860))
With recently added `@[congr]` lemmas, it suffices to deal with unions/inters over `true` and `false`.

### [2021-08-25 06:39:26](https://github.com/leanprover-community/mathlib/commit/4a0c3d7)
feat(linear_algebra/finite_dimension): nontriviality lemmas ([#8851](https://github.com/leanprover-community/mathlib/pull/8851))
A vector space of `finrank` greater than zero is `nontrivial`, likewise a vector space whose `finrank` is equal to the successor of a natural number.
Also write the non-`fact` version of `finite_dimensional_of_finrank_eq_succ`, a lemma which previously existed under a `fact` hypothesis, and rename the `fact` version to `fact_finite_dimensional_of_finrank_eq_succ`.

### [2021-08-25 06:39:25](https://github.com/leanprover-community/mathlib/commit/fd03625)
chore(ring_theory/ideal): Move local rings into separate file ([#8849](https://github.com/leanprover-community/mathlib/pull/8849))
Moves the material on local rings and local ring homomorphisms into a separate file and adds a module docstring.

### [2021-08-25 06:39:24](https://github.com/leanprover-community/mathlib/commit/88db4e2)
feat(ring_theory): `M / S` is noetherian if `M / S / R` is ([#8846](https://github.com/leanprover-community/mathlib/pull/8846))
Let `M` be an `S`-module and `S` an `R`-algebra. Then to show `M` is noetherian as an `S`-module, it suffices to show it is noetherian as an `R`-module.

### [2021-08-25 06:39:23](https://github.com/leanprover-community/mathlib/commit/00e57d3)
chore(order/rel_iso): rename `order_embedding.of_map_rel_iff` to `of_map_le_iff` ([#8839](https://github.com/leanprover-community/mathlib/pull/8839))
The old name comes from `rel_embedding`.

### [2021-08-25 06:39:21](https://github.com/leanprover-community/mathlib/commit/ef428c6)
feat(topology/metric_space): add `uniform_embedding.comap_metric_space` ([#8838](https://github.com/leanprover-community/mathlib/pull/8838))
* add `uniform_embedding.comap_metric_space` and
  `uniform_inducing.comap_pseudo_metric_space`;
* use the former for `int.metric_space`;
* also add `emetric.closed_ball_mem_nhds`.

### [2021-08-25 05:54:13](https://github.com/leanprover-community/mathlib/commit/bd9622f)
chore(category_theory/Fintype): Fix universe restriction in skeleton ([#8855](https://github.com/leanprover-community/mathlib/pull/8855))
This removes a universe restriction in the existence of a skeleton for the category `Fintype`.
Once merged, `Fintype.skeleton.{u}` will be a (small) skeleton for `Fintype.{u}`, with `u` any universe parameter.

### [2021-08-24 21:23:20](https://github.com/leanprover-community/mathlib/commit/6c3dda5)
feat(measure_theory/measure/vector_measure): add absolute continuity for vector measures ([#8779](https://github.com/leanprover-community/mathlib/pull/8779))
This PR defines absolute continuity for vector measures and shows that a signed measure is absolutely continuous wrt to a positive measure iff its total variation is absolutely continuous wrt to that measure.

### [2021-08-24 10:50:23](https://github.com/leanprover-community/mathlib/commit/1dda1cd)
feat(algebra/big_operators/finprod): a few more lemmas ([#8843](https://github.com/leanprover-community/mathlib/pull/8843))
* versions of `monoid_hom.map_finprod` that assume properties of
  `f : M →* N` instead of finiteness of the support;
* `finsum_smul`, `smul_finsum`, `finprod_inv_distrib`: missing
  analogues of lemmas from `finset.prod`/`finset.sum` API.

### [2021-08-24 09:54:38](https://github.com/leanprover-community/mathlib/commit/a21fcfa)
feat(data/real/nnreal): upgrade `nnabs` to a `monoid_with_zero_hom` ([#8844](https://github.com/leanprover-community/mathlib/pull/8844))
Other changes:
* add `nnreal.finset_sup_div`;
* rename `nnreal.coe_nnabs` to `real.coe_nnabs`;
* add `real.nndist_eq` and `real.nndist_eq'`.

### [2021-08-24 08:27:38](https://github.com/leanprover-community/mathlib/commit/19ae317)
feat(measure_theory/interval_integral): strong version of FTC-2 ([#7978](https://github.com/leanprover-community/mathlib/pull/7978))
The equality `∫ y in a..b, f' y = f b - f a` is currently proved in mathlib assuming that `f'` is continuous. We weaken the assumption, assuming only that `f'` is integrable.

### [2021-08-24 04:00:04](https://github.com/leanprover-community/mathlib/commit/737b208)
feat(linear_algebra/dimension): generalize dim_map_le to heterogeneous universes ([#8800](https://github.com/leanprover-community/mathlib/pull/8800))
Per @hrmacbeth's [request on zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Behaviour.20of.20finrank.20under.20morphisms).

### [2021-08-24 02:16:33](https://github.com/leanprover-community/mathlib/commit/4aa8705)
chore(scripts): update nolints.txt ([#8840](https://github.com/leanprover-community/mathlib/pull/8840))
I am happy to remove some nolints for you!

### [2021-08-23 20:37:30](https://github.com/leanprover-community/mathlib/commit/26448a2)
feat(analysis/normed_space/exponential): define exponential in a Banach algebra and prove basic results ([#8576](https://github.com/leanprover-community/mathlib/pull/8576))

### [2021-08-23 17:56:01](https://github.com/leanprover-community/mathlib/commit/2f4dc3a)
feat(ring_theory): generalize `exists_integral_multiple` ([#8827](https://github.com/leanprover-community/mathlib/pull/8827))
Not only is `z * (y : integral_closure R A)` integral, so is `z * (y : R)`!

### [2021-08-23 17:55:59](https://github.com/leanprover-community/mathlib/commit/700effa)
feat(ring_theory/localization): the algebraic elements over `Frac(R)` are those over `R` ([#8826](https://github.com/leanprover-community/mathlib/pull/8826))
We had this lemma for `L / K` is algebraic iff `L / A` is, but now we also have it elementwise!

### [2021-08-23 17:55:58](https://github.com/leanprover-community/mathlib/commit/2a69dc2)
feat(ring_theory): two little lemmas on Noetherianness ([#8825](https://github.com/leanprover-community/mathlib/pull/8825))
No real deep thoughts behind these lemmas, just that they are needed to show the integral closure of a Dedekind domain is Noetherian.

### [2021-08-23 17:55:57](https://github.com/leanprover-community/mathlib/commit/8a7e4f7)
feat(measure_theory): volume of a (closed) L∞-ball ([#8791](https://github.com/leanprover-community/mathlib/pull/8791))
* pi measure of a (closed or open) ball;
* volume of a (closed or open) ball in
  - `Π i, α i`;
  - `ℝ`;
  - `ι → ℝ`;
* volumes of `univ`, `emetric.ball`, and `emetric.closed_ball` in `ℝ`.

### [2021-08-23 17:55:56](https://github.com/leanprover-community/mathlib/commit/ff85e9c)
feat(measure_theory/measure/measure_space): obtain pairwise disjoint spanning sets wrt. two measures ([#8750](https://github.com/leanprover-community/mathlib/pull/8750))
Given two sigma finite measures, there exists a sequence of pairwise disjoint spanning sets that are finite wrt. both measures

### [2021-08-23 17:55:55](https://github.com/leanprover-community/mathlib/commit/98a6329)
refactor(algebra/group_power): use `covariant_class` ([#8713](https://github.com/leanprover-community/mathlib/pull/8713))
## Main changes
* use `covariant_class` instead of `canonically_ordered_*` or `ordered_add_*` as an assumption in many lemmas;
* move some lemmas to the root namespace;
* use `to_additive` for more lemmas;
## Detailed list of API changes
* `canonically_ordered_comm_semiring.pow_le_pow_of_le_left`:
  - rename to `pow_le_pow_of_le_left'`;
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_le_nsmul_of_le_right`;
* `canonically_ordered_comm_semiring.one_le_pow_of_one_le`:
  - rename to `one_le_pow_of_one_le`';
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_nonneg`;
* `canonically_ordered_comm_semiring.pow_le_one`:
  - rename to `pow_le_one'`;
  - assume `[covariant_class M M (*) (≤)]`;
  - use `to_additive` to generate `nsmul_nonpos`;
* add `pow_le_pow'`, generate `nsmul_le_nsmul`;
* add `pow_le_pow_of_le_one'` and `nsmul_le_nsmul_of_nonpos`;
* add `one_lt_pow'`, generate `nsmul_pos`;
  - as a side effect, `nsmul_pos` now assumes `n ≠ 0` instead of `0 < n`.
* add `pow_lt_one'`, generate `nsmul_neg`;
* add `pow_lt_pow'`, generate `nsmul_lt_nsmul`;
* generalize `one_le_pow_iff` and `pow_le_one_iff`, generate `nsmul_nonneg_iff` and `nsmul_nonpos_iff`;
* generalize `one_lt_pow_iff`, `pow_lt_one_iff`, and `pow_eq_one_iff`, generate `nsmul_pos_iff`, `nsmul_neg_iff`, and `nsmul_eq_zero_iff`;
* add `one_le_gpow`, generate `gsmul_nonneg`;
* rename `eq_of_sq_eq_sq` to `sq_eq_sq`, golf;
* drop `eq_one_of_pow_eq_one` in favor of the `iff` version `pow_eq_one_iff`;
* add missing instance `nat.ordered_comm_semiring`;
## Misc changes
* replace some proofs about `nat.pow` with references to generic lemmas;
* add `nnreal.coe_eq_one`;

### [2021-08-23 17:55:54](https://github.com/leanprover-community/mathlib/commit/b7f0323)
feat(topology): interior of a finite product of sets ([#8695](https://github.com/leanprover-community/mathlib/pull/8695))
Also finishes the filter inf work from [#8657](https://github.com/leanprover-community/mathlib/pull/8657) proving stronger lemmas for
filter.infi

### [2021-08-23 16:45:34](https://github.com/leanprover-community/mathlib/commit/608faf0)
feat(measure_theory/function/conditional_expectation): uniqueness of the conditional expectation ([#8802](https://github.com/leanprover-community/mathlib/pull/8802))
The main part of the PR is the new file `ae_eq_of_integral`, in which many different lemmas prove variants of the statement "if two functions have same integral on all sets, then they are equal almost everywhere".
In the file `conditional_expectation`, a similar lemma is written for functions which have same integral on all sets in a sub-sigma-algebra and are measurable with respect to that sigma-algebra. This proves the uniqueness of the conditional expectation.

### [2021-08-23 16:02:50](https://github.com/leanprover-community/mathlib/commit/9a7d9a8)
feat(group_theory/nilpotent): add def lemmas, basic lemmas on central series ([#8730](https://github.com/leanprover-community/mathlib/pull/8730))
Add to API for nilpotent groups with simp def lemmas and other basic properties of central series.

### [2021-08-23 14:22:14](https://github.com/leanprover-community/mathlib/commit/df3e886)
feat(group_theory/group_action): generalize mul_action.function_End to other endomorphisms ([#8724](https://github.com/leanprover-community/mathlib/pull/8724))
The main aim of this PR is to remove [`intermediate_field.subgroup_action`](https://leanprover-community.github.io/mathlib_docs/field_theory/galois.html#intermediate_field.subgroup_action) which is a weird special case of the much more general instance `f • a = f a`, added in this PR as `alg_equiv.apply_mul_semiring_action`. We add the same actions for all the other hom types for consistency.
These generalizations are in line with the `mul_action.function_End` (renamed to `function.End.apply_mul_action`) and `mul_action.perm` (renamed to `equiv.perm.apply_mul_action`) instances introduced by @dwarn, providing any endomorphism that has a monoid structure with a faithful `mul_action` corresponding to function application.
Note that there is no monoid structure on `ring_equiv`, or `alg_hom`, so this PR does not bother with the corresponding action.

### [2021-08-23 12:46:47](https://github.com/leanprover-community/mathlib/commit/3c49044)
feat(data/list/nodup): nodup.nth_le_inj_iff ([#8813](https://github.com/leanprover-community/mathlib/pull/8813))
This allows rewriting as an `inj_iff` lemma directly via proj notation.

### [2021-08-23 12:46:47](https://github.com/leanprover-community/mathlib/commit/f8f551a)
feat(data/fintype/basic): choose_subtype_eq ([#8812](https://github.com/leanprover-community/mathlib/pull/8812))
Choosing out of a finite subtype such that the underlying value is precisely some value of the parent type works as intended.

### [2021-08-23 12:00:47](https://github.com/leanprover-community/mathlib/commit/a85c9f6)
chore(field_theory): make `is_separable` an instance parameter ([#8741](https://github.com/leanprover-community/mathlib/pull/8741))
There were a few places that had an explicit `is_separable` parameter. For simplicity and consistency, let's make them all instance params.

### [2021-08-23 10:17:14](https://github.com/leanprover-community/mathlib/commit/8b9a47b)
feat(data/finset/basic): finset.exists_ne_of_one_lt_card ([#8816](https://github.com/leanprover-community/mathlib/pull/8816))
Analog of `fintype.exists_ne_of_one_lt_card`.

### [2021-08-23 10:17:13](https://github.com/leanprover-community/mathlib/commit/a52a9fe)
chore(data/multiset/basic): move abs_sum_le_sum_abs from algebra/big_operators/basic.lean. ([#8804](https://github.com/leanprover-community/mathlib/pull/8804))
There doesn't seem to be a reason for the place it has now.

### [2021-08-23 10:17:12](https://github.com/leanprover-community/mathlib/commit/f98fc00)
docs(logic/relation): add module docstring ([#8773](https://github.com/leanprover-community/mathlib/pull/8773))
Also fix whitespaces

### [2021-08-23 10:17:11](https://github.com/leanprover-community/mathlib/commit/c811dd7)
feat(data/nat/mul_ind): multiplicative induction principles ([#8514](https://github.com/leanprover-community/mathlib/pull/8514))

### [2021-08-23 09:16:14](https://github.com/leanprover-community/mathlib/commit/f949172)
feat(data/polynomial/basic): polynomial.op_ring_equiv ([#8537](https://github.com/leanprover-community/mathlib/pull/8537))

### [2021-08-22 20:10:11](https://github.com/leanprover-community/mathlib/commit/9945a16)
refactor(analysis/normed_space/{add_torsor, mazur_ulam}): adjust Mazur-Ulam file to use affine isometries ([#8661](https://github.com/leanprover-community/mathlib/pull/8661))

### [2021-08-22 19:02:17](https://github.com/leanprover-community/mathlib/commit/d9113ec)
doc(linear_algebra/trace): fix error in title ([#8803](https://github.com/leanprover-community/mathlib/pull/8803))
the first two lines of this were super contradictory

### [2021-08-22 16:54:23](https://github.com/leanprover-community/mathlib/commit/87f14e3)
feat(topology/basic): interior of a singleton ([#8784](https://github.com/leanprover-community/mathlib/pull/8784))
* add generic lemmas `interior_singleton`, `closure_compl_singleton`;
* add more lemmas and instances about `ne_bot (𝓝[{x}ᶜ] x)`;
* rename `dense_compl_singleton` to `dense_compl_singleton_iff_not_open`,
  add new `dense_compl_singleton` that assumes `[ne_bot (𝓝[{x}ᶜ] x)]`.

### [2021-08-22 16:54:22](https://github.com/leanprover-community/mathlib/commit/db9d4a3)
feat(data/finset,order/conditionally_complete_lattice): lemmas about `min'/max'` ([#8782](https://github.com/leanprover-community/mathlib/pull/8782))
## `data/finset/*`
* add `finset.nonempty.to_set`;
* add lemmas `finset.max'_lt_iff`, `finset.lt_min'_iff`,
  `finset.max'_eq_sup'`, `finset.min'_eq_inf'`;
* rewrite `finset.induction_on_max` without using `finset.card`,
  move one step to `finset.lt_max'_of_mem_erase_max'`;
## `order/conditionally_complete_lattice`
* add lemmas relating `Sup`/`Inf` of a nonempty finite set in a
  conditionally complete lattice to
 `finset.sup'`/`finset.inf'`/`finset.max'`/`finset.min'`;
* a few more lemmas about `Sup`/`Inf` of a nonempty finite set
  in a conditionally complete lattice / linear order;
## `order/filter/at_top_bot`
* golf the proof of `filter.high_scores`.

### [2021-08-22 16:54:21](https://github.com/leanprover-community/mathlib/commit/ea9cd02)
refactor(geometry/euclidean/basic): adjust Euclidean geometry to use affine isometries for reflections ([#8662](https://github.com/leanprover-community/mathlib/pull/8662))

### [2021-08-22 15:49:31](https://github.com/leanprover-community/mathlib/commit/a9c1300)
refactor(topology/metric_space/basic): rename `closed_ball_Icc` ([#8790](https://github.com/leanprover-community/mathlib/pull/8790))
* rename `closed_ball_Icc` to `real.closed_ball_eq`;
* add `real.ball_eq`, `int.ball_eq`, `int.closed_ball_eq`,
  `int.preimage_ball`, `int.preimage_closed_ball`.

### [2021-08-22 13:58:19](https://github.com/leanprover-community/mathlib/commit/373911d)
chore(measure_theory): make `μ` an explicit argument in `subsingleton.measure_zero` etc ([#8793](https://github.com/leanprover-community/mathlib/pull/8793))

### [2021-08-22 03:08:52](https://github.com/leanprover-community/mathlib/commit/8a96d00)
chore(scripts): update nolints.txt ([#8798](https://github.com/leanprover-community/mathlib/pull/8798))
I am happy to remove some nolints for you!

### [2021-08-22 01:10:57](https://github.com/leanprover-community/mathlib/commit/f915106)
chore(data/set/lattice): a few lemmas, golf ([#8795](https://github.com/leanprover-community/mathlib/pull/8795))

### [2021-08-21 21:43:39](https://github.com/leanprover-community/mathlib/commit/d3e20b4)
chore(data/multiset/basic): consistently use singleton notation ([#8786](https://github.com/leanprover-community/mathlib/pull/8786))

### [2021-08-21 21:43:38](https://github.com/leanprover-community/mathlib/commit/252cb02)
feat(linear_algebra/vandermonde): `vandermonde v` multiplied by its transpose ([#8776](https://github.com/leanprover-community/mathlib/pull/8776))
Two not very exciting lemmas about multiplying a Vandermonde matrix by its transpose (one for each side). I don't know if they are really useful, so I could also just inline them in [#8777](https://github.com/leanprover-community/mathlib/pull/8777).

### [2021-08-21 21:43:37](https://github.com/leanprover-community/mathlib/commit/5f51771)
feat(linear_algebra/bilinear_form): basis changing `bilin_form.to_matrix` ([#8775](https://github.com/leanprover-community/mathlib/pull/8775))
A few `simp` lemmas on bilinear forms.

### [2021-08-21 21:43:36](https://github.com/leanprover-community/mathlib/commit/c44f19f)
feat(algebra/associated): simple lemmas and dot notation ([#8770](https://github.com/leanprover-community/mathlib/pull/8770))
Introduce
* `prime.exists_mem_finset_dvd`
* `prime.not_dvd_one`
Rename
* `exists_mem_multiset_dvd_of_prime` -> `prime.exists_mem_multiset_dvd`
* `left_dvd_or_dvd_right_of_dvd_prime_mul ` ->`prime.left_dvd_or_dvd_right_of_dvd_mul`

### [2021-08-21 19:52:15](https://github.com/leanprover-community/mathlib/commit/57e127a)
refactor(order/complete_lattice): use `is_empty` ([#8796](https://github.com/leanprover-community/mathlib/pull/8796))
* change `set.univ_eq_empty_iff` to use `is_empty`;
* rename `set.range_eq_empty` to `set.range_eq_empty_iff`;
* add new `set.range_eq_empty`, it assumes `[is_empty α]`;
* combine `supr_of_empty`, `supr_of_empty'`, and `supr_empty` into `supr_of_empty`, same for `infi`;
* replace `csupr_neg` with `csupr_of_empty` and `csupr_false`;
* adjust some proofs to use `casesI is_empty_of_nonempty α` instead of `by_cases h : nonempty α`.

### [2021-08-21 19:52:14](https://github.com/leanprover-community/mathlib/commit/8eba262)
feat(topology/metric_space/basic): union of balls `ball x n`, `n : ℕ` ([#8792](https://github.com/leanprover-community/mathlib/pull/8792))

### [2021-08-21 19:52:13](https://github.com/leanprover-community/mathlib/commit/9b60e0f)
feat(data/set/basic): add `pairwise_on_pair` ([#8789](https://github.com/leanprover-community/mathlib/pull/8789))
Add `set.pairwise_on_insert`, `set.pairwise_on_pair`, and `set.pairwise_on_pair_of_symmetric`.

### [2021-08-21 19:52:12](https://github.com/leanprover-community/mathlib/commit/44b8138)
chore(topology/instances/ennreal): use `tactic.lift` ([#8788](https://github.com/leanprover-community/mathlib/pull/8788))
* use `tactic.lift` in two proofs;
* use the `order_dual` trick in one proof.

### [2021-08-21 19:52:11](https://github.com/leanprover-community/mathlib/commit/e00afed)
feat(topology/metric_space): turn `nonempty_ball` into an `iff` ([#8747](https://github.com/leanprover-community/mathlib/pull/8747))
* add `set.univ_pi_empty`;
* turn `metric.nonempty_ball` into an `iff`, mark it with `@[simp]`; add `metric.ball_eq_empty`
* do the same thing to `closed_ball`s;
* add primed versions of `metric.ball_pi` and `metric.closed_ball_pi`.

### [2021-08-21 18:46:32](https://github.com/leanprover-community/mathlib/commit/d31b85f)
feat(data/list/rotate): is_rotated_append ([#8780](https://github.com/leanprover-community/mathlib/pull/8780))
`list.append` is commutative with respect to `~r`.

### [2021-08-21 18:46:31](https://github.com/leanprover-community/mathlib/commit/0760b20)
feat(topology/metric_space): metrizable spaces ([#8759](https://github.com/leanprover-community/mathlib/pull/8759))
Define (pseudo)-metric space constructors for metrizable topological spaces.

### [2021-08-21 17:31:49](https://github.com/leanprover-community/mathlib/commit/bafe207)
chore(linear_algebra): remove `→ₗ` notation where the ring is not specified ([#8778](https://github.com/leanprover-community/mathlib/pull/8778))
This PR removes the notation `M →ₗ N` for linear maps, where the ring is not specified. This is not used much in the library, and is needed for an upcoming refactor that will generalize linear maps to semilinear maps. See the discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps).

### [2021-08-21 15:59:17](https://github.com/leanprover-community/mathlib/commit/897e4ed)
feat(field_theory): finite fields exist ([#8692](https://github.com/leanprover-community/mathlib/pull/8692))

### [2021-08-21 12:26:51](https://github.com/leanprover-community/mathlib/commit/f72126b)
chore(algebra/gcd_monoid): move `algebra.gcd_monoid` to `algebra.gcd_monoid.basic` ([#8772](https://github.com/leanprover-community/mathlib/pull/8772))

### [2021-08-21 05:42:59](https://github.com/leanprover-community/mathlib/commit/f36c98e)
chore(*): remove spurious whitespace ([#8769](https://github.com/leanprover-community/mathlib/pull/8769))

### [2021-08-20 21:38:03](https://github.com/leanprover-community/mathlib/commit/d869256)
refactor(data/nat/lattice): move code, add lemmas ([#8708](https://github.com/leanprover-community/mathlib/pull/8708))
* move `nat.conditionally_complete_linear_order_with_bot` and `enat.complete_linear_order` to a new file `data.nat.lattice`;
* add a few lemmas (`nat.supr_lt_succ` etc), move `set.bUnion_lt_succ` to the same file;
* use `galois_insertion.lift_complete_lattice` to define `enat.complete_linear_order`.

### [2021-08-20 14:42:08](https://github.com/leanprover-community/mathlib/commit/45e7eb8)
feat(dynamics/fixed_points): simple lemmas ([#8768](https://github.com/leanprover-community/mathlib/pull/8768))

### [2021-08-20 14:42:07](https://github.com/leanprover-community/mathlib/commit/6ae3747)
feat(algebra/big_operators): the product over `{x // x ∈ m}` is the product over `m.to_finset` ([#8742](https://github.com/leanprover-community/mathlib/pull/8742))

### [2021-08-20 14:42:06](https://github.com/leanprover-community/mathlib/commit/d62a461)
feat(linear_algebra/determinant): `det (M ⬝ N) = det (N ⬝ M)` if `M` is invertible ([#8720](https://github.com/leanprover-community/mathlib/pull/8720))
If `M` is a square or invertible matrix, then `det (M ⬝ N) = det (N ⬝ M)`. This is basically just using `mul_comm` on `det M * det N`, except for some tricky rewriting to handle the invertible case.

### [2021-08-20 14:42:05](https://github.com/leanprover-community/mathlib/commit/7ccf463)
feat(algebra): is_smul_regular for `pi`, `finsupp`, `matrix`, `polynomial` ([#8716](https://github.com/leanprover-community/mathlib/pull/8716))
Also provide same lemma for finsupp, and specialize it for matrices and polynomials
Inspired by 
https://github.com/leanprover-community/mathlib/pull/8681#discussion_r689320217
https://github.com/leanprover-community/mathlib/pull/8679#discussion_r689545373

### [2021-08-20 14:42:03](https://github.com/leanprover-community/mathlib/commit/aee7bad)
feat(data/list/rotate): cyclic_permutations ([#8678](https://github.com/leanprover-community/mathlib/pull/8678))
For `l ~ l'` we have `list.permutations`. We provide the list of cyclic permutations of `l` such that all members are `l ~r l'`. This relationship is proven, as well as the induced `nodup` of the list of cyclic permutants.
This also simplifies the `cycle.list` definition, and removed the requirement for decidable equality in it.

### [2021-08-20 14:42:02](https://github.com/leanprover-community/mathlib/commit/7e8432d)
chore(algebra/group_power/lemmas): Lemmas about gsmul ([#8618](https://github.com/leanprover-community/mathlib/pull/8618))
This restates some existing lemmas as `monotone` and `strict_monotone`, and provides new lemmas about the right argument of gsmul:
* `gsmul_le_gsmul'`
* `gsmul_lt_gsmul'`
* `gsmul_le_gsmul_iff'`
* `gsmul_lt_gsmul_iff'`
This also removes an unnecessary `linear_order` assumption from `gsmul_le_gsmul_iff` and `gsmul_lt_gsmul_iff`.

### [2021-08-20 14:42:00](https://github.com/leanprover-community/mathlib/commit/7265a4e)
feat(linear_algebra/dimension): generalize inequalities and invariance of dimension to arbitrary rings ([#8343](https://github.com/leanprover-community/mathlib/pull/8343))
We implement some of the results of [_Les familles libres maximales d'un module ont-elles le meme cardinal?_](http://www.numdam.org/article/PSMIR_1973___4_A4_0.pdf).
We also generalize many theorems which were previously proved only for vector spaces, but are true for modules over arbitrary rings or rings satisfying the (strong) rank condition or have invariant basis number. (These typically need entire new proofs, as the original proofs e.g. used rank-nullity.)
The main new results are:
* `basis_fintype_of_finite_spans`: 
  Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
* `union_support_maximal_linear_independent_eq_range_basis`: 
  Over any ring `R`, if `b` is a basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
* `infinite_basis_le_maximal_linear_independent`:
  Over any ring `R`, if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.
* `mk_eq_mk_of_basis`:
  We generalize the invariance of dimension theorem to any ring with the invariant basis number property.
* `basis.le_span`:
  We generalize this statement (the size of a basis is bounded by the size of any spanning set)
  to any ring satisfying the rank condition.
* `linear_independent_le_span`:
  If `R` satisfies the strong rank condition,
  then for any linearly independent family `v : ι → M`
  and any finite spanning set `w : set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linear_independent_le_basis`:
  Over any ring `R` satisfying the strong rank condition,
  if `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.
  
There is a naming discrepancy: most of the theorem names refer to `dim`,
even though the definition is of `module.rank`.
This reflects that `module.rank` was originally called `dim`, and only defined for vector spaces.
I would prefer to address this in a separate PR (note this discrepancy wasn't introduced in this PR).

### [2021-08-20 14:41:58](https://github.com/leanprover-community/mathlib/commit/15b1461)
feat(archive/imo): IMO 2006 Q3 ([#8052](https://github.com/leanprover-community/mathlib/pull/8052))
Formalization of IMO 2006/3

### [2021-08-19 16:19:58](https://github.com/leanprover-community/mathlib/commit/5dc8bc1)
feat(linear_algebra/clifford_algebra/equivs): the equivalences preserve conjugation ([#8739](https://github.com/leanprover-community/mathlib/pull/8739))

### [2021-08-19 14:31:16](https://github.com/leanprover-community/mathlib/commit/dd5e779)
fix(linear_algebra/basic): fix incorrect namespaces ([#8757](https://github.com/leanprover-community/mathlib/pull/8757))
Previously there were names in the `linear_map` namespace which were about `linear_equiv`s.
This moves:
* `linear_map.fun_congr_left` to `linear_equiv.fun_congr_left`
* `linear_map.automorphism_group` to `linear_equiv.automorphism_group`
* `linear_map.automorphism_group.to_linear_map_monoid_hom` to `linear_equiv.automorphism_group.to_linear_map_monoid_hom`

### [2021-08-19 14:31:14](https://github.com/leanprover-community/mathlib/commit/d172085)
docs(overview): add weak-* topology ([#8755](https://github.com/leanprover-community/mathlib/pull/8755))

### [2021-08-19 14:31:13](https://github.com/leanprover-community/mathlib/commit/86fccaa)
feat(measure_theory/strongly_measurable): define strongly measurable functions ([#8623](https://github.com/leanprover-community/mathlib/pull/8623))
A function `f` is said to be strongly measurable with respect to a measure `μ` if `f` is the sequential limit of simple functions whose support has finite measure.
Functions in `Lp` for `0 < p < ∞` are strongly measurable. If the measure is sigma-finite, measurable and strongly measurable are equivalent.
The main property of strongly measurable functions is `strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that `f` is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some results for those functions as if the measure was sigma-finite.
I will use this to prove properties of the form `f =ᵐ[μ] g` for `Lp` functions.

### [2021-08-19 12:44:51](https://github.com/leanprover-community/mathlib/commit/802859f)
chore(algebra/big_operators): weaken assumption for multiset.exists_smul_of_dvd_count ([#8758](https://github.com/leanprover-community/mathlib/pull/8758))
This is slightly more convenient than doing a case split on `a ∈ s` in the caller.

### [2021-08-19 12:44:50](https://github.com/leanprover-community/mathlib/commit/1efa367)
feat(group_action/defs): add missing comp_hom smul instances ([#8707](https://github.com/leanprover-community/mathlib/pull/8707))
This adds missing `smul_comm_class` and `is_scalar_tower` instances about the `comp_hom` definitions.
To resolve unification issues in finding these instances caused by the reducibility of the `comp_hom` defs, this introduces a semireducible def `has_scalar.comp.smul`.

### [2021-08-19 12:44:49](https://github.com/leanprover-community/mathlib/commit/4113db5)
feat(ring_theory): the trace of an integral element is integral ([#8702](https://github.com/leanprover-community/mathlib/pull/8702))
This PR uses `trace_gen_eq_sum_roots` and `trace_trace` to show the trace of an integral element `x : L` over `K` is a multiple of the sum of all conjugates of `x`, and concludes that the trace of `x` is integral.

### [2021-08-19 11:02:14](https://github.com/leanprover-community/mathlib/commit/159e34e)
Revert "feat(field_theory/intermediate_field): generalize `algebra` instances"
OOPS!
This reverts commit 4b525bf25aa33201bd26942a938b84b2df71f175.

### [2021-08-19 11:01:55](https://github.com/leanprover-community/mathlib/commit/4b525bf)
feat(field_theory/intermediate_field): generalize `algebra` instances
The `algebra` and `is_scalar_tower` instances for `intermediate_field` are (again) as general as those for `subalgebra`.

### [2021-08-19 09:57:42](https://github.com/leanprover-community/mathlib/commit/902d3ac)
chore(tactic/rewrite_search): reuse rw_rules_p parser ([#8752](https://github.com/leanprover-community/mathlib/pull/8752))
The parser defined here is the same as `rw_rules_p`, so use it.

### [2021-08-19 08:28:44](https://github.com/leanprover-community/mathlib/commit/28a360a)
feat(analysis/calculus/deriv): prove `deriv_inv` at `x = 0` as well ([#8748](https://github.com/leanprover-community/mathlib/pull/8748))
* turn `differentiable_at_inv` and `differentiable_at_fpow` into `iff` lemmas;
* slightly weaker assumptions for `differentiable_within_at_fpow` etc;
* prove `deriv_inv` and `fderiv_inv` for all `x`;
* prove formulas for iterated derivs of `x⁻¹` and `x ^ m`, `m : int`;
* push `coe` in these formulas;

### [2021-08-19 06:51:43](https://github.com/leanprover-community/mathlib/commit/1c60e61)
feat(topology/metric_space/basic): `emetric.ball x ∞ = univ` ([#8745](https://github.com/leanprover-community/mathlib/pull/8745))
* add `@[simp]` to `metric.emetric_ball`,
  `metric.emetric_ball_nnreal`, and
  `metric.emetric_closed_ball_nnreal`;
* add `@[simp]` lemmas `metric.emetric_ball_top` and
  `emetric.closed_ball_top`.

### [2021-08-19 03:46:27](https://github.com/leanprover-community/mathlib/commit/0e0a240)
chore(scripts): update nolints.txt ([#8754](https://github.com/leanprover-community/mathlib/pull/8754))
I am happy to remove some nolints for you!

### [2021-08-19 01:51:34](https://github.com/leanprover-community/mathlib/commit/ee3f8b8)
chore(order/complete_lattice): golf some proofs ([#8746](https://github.com/leanprover-community/mathlib/pull/8746))

### [2021-08-18 23:53:44](https://github.com/leanprover-community/mathlib/commit/8455433)
doc(tactic/simps): typo ([#8751](https://github.com/leanprover-community/mathlib/pull/8751))
Missed this review comment in [#8729](https://github.com/leanprover-community/mathlib/pull/8729)

### [2021-08-18 23:53:43](https://github.com/leanprover-community/mathlib/commit/6fe5b55)
feat(algebra/algebra): `alg_{hom,equiv}.restrict_scalars` is injective ([#8743](https://github.com/leanprover-community/mathlib/pull/8743))

### [2021-08-18 21:30:49](https://github.com/leanprover-community/mathlib/commit/e0bf9a1)
doc({topology.algebra.weak_dual_topology, analysis.normed_space.weak_dual}): fix docstrings ([#8710](https://github.com/leanprover-community/mathlib/pull/8710))
Fixing docstrings from the recently merged PR [#8598](https://github.com/leanprover-community/mathlib/pull/8598) on weak-* topology.

### [2021-08-18 21:30:47](https://github.com/leanprover-community/mathlib/commit/23cf025)
feat(algebra/ordered_sub): define truncated subtraction in general ([#8503](https://github.com/leanprover-community/mathlib/pull/8503))
* Define and prove properties of truncated subtraction in general
* We currently only instantiate it for `nat`. The other types (`multiset`, `finsupp`, `nnreal`, `ennreal`, ...) will be in future PRs.
Todo in future PRs:
* Provide `has_ordered_sub` instances for all specific cases
* Remove the lemmas specific to each individual type

### [2021-08-18 18:52:52](https://github.com/leanprover-community/mathlib/commit/0860c41)
feat(data/nat/pairing): add some `nat.pair` lemmas ([#8740](https://github.com/leanprover-community/mathlib/pull/8740))

### [2021-08-18 18:52:51](https://github.com/leanprover-community/mathlib/commit/e6fda2a)
fix(transform_decl): fix namespace bug ([#8733](https://github.com/leanprover-community/mathlib/pull/8733))
* The problem was that when writing `@[to_additive] def foo ...` every declaration used in `foo` in namespace `foo` would be additivized without changing the last part of the name. This behavior was intended to translate automatically generated declarations like `foo._proof_1`. However, if `foo` contains a non-internal declaration `foo.bar` and `add_foo.bar` didn't exist yet, it would also create a declaration `add_foo.bar` additivizing `foo.bar`.
* This PR changes the behavior: if `foo.bar` has the `@[to_additive]` attribute (potentially with a custom additive name), then we won't create a second additive version of `foo.bar`, and succeed normally. However, if `foo.bar` doesn't have the `@[to_additive]` attribute, then we fail with a nice error message. We could potentially support this behavior, but it doesn't seem that worthwhile and it would require changing a couple low-level definitions that `@[to_additive]` uses (e.g. by replacing `name.map_prefix` so that it only maps prefixes if the name is `internal`).
* So far this didn't happen in the library yet. There are currently 5 non-internal declarations `foo.bar` that are used in `foo` where `foo` has the `@[to_additive]` attribute, but all of these declarations were already had an additive version `add_foo.bar`.
* These 5 declarations are `[Mon.has_limits.limit_cone, Mon.has_limits.limit_cone_is_limit, con_gen.rel, magma.free_semigroup.r, localization.r]`
* This fixes the error in [#8707](https://github.com/leanprover-community/mathlib/pull/8707) and resolves the Zulip thread https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238707.20linter.20weirdness
* I also added some documentation / comments to the function `transform_decl_with_prefix_fun_aux`, made it non-private, and rewrote some steps.

### [2021-08-18 18:52:50](https://github.com/leanprover-community/mathlib/commit/9a249ee)
doc(tactic/simps): expand ([#8729](https://github.com/leanprover-community/mathlib/pull/8729))
* Better document custom projections that are composites of multiple projections
* Give examples of `initialize_simps_projections`
* Add `initialize_simps_projections` entry to commands.

### [2021-08-18 18:52:49](https://github.com/leanprover-community/mathlib/commit/6a83c7d)
feat(topology/compact_open): the family of constant maps collectively form a continuous map ([#8721](https://github.com/leanprover-community/mathlib/pull/8721))

### [2021-08-18 18:52:48](https://github.com/leanprover-community/mathlib/commit/3ac609b)
chore(topology/continuous_function/compact): relax typeclass assumptions for metric space structure on C(X, Y) ([#8717](https://github.com/leanprover-community/mathlib/pull/8717))

### [2021-08-18 18:52:47](https://github.com/leanprover-community/mathlib/commit/0d59511)
feat(topology/{continuous_function/bounded, metric_space/algebra}): new mixin classes ([#8580](https://github.com/leanprover-community/mathlib/pull/8580))
This PR defines mixin classes `has_lipschitz_add` and `has_bounded_smul` which are designed to abstract algebraic properties of metric spaces shared by normed groups/fields/modules and by `ℝ≥0`.
This permits the bounded continuous functions `α →ᵇ ℝ≥0` to be naturally a topological (ℝ≥0)-module, by a generalization of the proof previously written for normed groups/fields/modules.
Frankly, these typeclasses are a bit ad hoc -- but it all seems to work!

### [2021-08-18 18:52:46](https://github.com/leanprover-community/mathlib/commit/26590e9)
feat(data/list/min_max): maximum is a fold, bounded prod ([#8543](https://github.com/leanprover-community/mathlib/pull/8543))
Also provide the same lemmas for multiset.

### [2021-08-18 18:52:45](https://github.com/leanprover-community/mathlib/commit/4e7e7df)
feat(algebra/monoid_algebra): add_monoid_algebra.op_{add,ring}_equiv ([#8536](https://github.com/leanprover-community/mathlib/pull/8536))
Transport an opposite `add_monoid_algebra` to the algebra over the opposite ring.
On the way, 
- provide API lemma `mul_equiv.inv_fun_eq_symm {f : M ≃* N} : f.inv_fun = f.symm` and the additive version
- generalize simp lemmas `equiv_to_opposite_(symm_)apply` to `equiv_to_opposite_(symm_)coe`
- tag `map_range.(add_)equiv_symm` with `[simp]

### [2021-08-18 18:52:43](https://github.com/leanprover-community/mathlib/commit/15444e1)
feat(model_theory/basic): more substructure API, including subtype, map, and comap ([#7937](https://github.com/leanprover-community/mathlib/pull/7937))
Defines `first_order.language.embedding.of_injective`, which bundles an injective hom in an algebraic language as an embedding
Defines the induced `L.Structure` on an `L.substructure`
Defines the embedding `S.subtype` from `S : L.substructure M` into `M`
Defines `substructure.map` and `substructure.comap` and associated API including Galois insertions

### [2021-08-18 16:14:18](https://github.com/leanprover-community/mathlib/commit/a47d49d)
chore(set/function): remove reducible on eq_on ([#8738](https://github.com/leanprover-community/mathlib/pull/8738))
This backs out [#8736](https://github.com/leanprover-community/mathlib/pull/8736), and instead removes the unnecessary `@[reducible]`. 
This leaves the `simp` lemma available if anyone wants it (although it is not currently used in mathlib3), but should still resolve the problem that @dselsam's experimental `simp` in the binport of mathlib3 was excessively enthusiastic about using this lemma.

### [2021-08-18 16:14:17](https://github.com/leanprover-community/mathlib/commit/02b90ab)
doc(tactic/monotonicity): bad ac_mono syntax doc ([#8734](https://github.com/leanprover-community/mathlib/pull/8734))
The syntax `ac_mono h` was at some point changed to `ac_mono := h` but the documentation did not reflect the change.

### [2021-08-18 12:08:53](https://github.com/leanprover-community/mathlib/commit/83c7821)
fix(algebra/algebra/restrict_scalars): Remove a bad instance ([#8732](https://github.com/leanprover-community/mathlib/pull/8732))
This instance forms a non-defeq diamond with the following one
```lean
instance submodule.restricted_module' [module R M] [is_scalar_tower R S M] (V : submodule S M) :
  module R V :=
by apply_instance
```
The `submodule.restricted_module_is_scalar_tower` instance is harmless, but it can't exist without the first one so we remove it too.
Based on the CI result, this instance wasn't used anyway.

### [2021-08-18 12:08:52](https://github.com/leanprover-community/mathlib/commit/c0f16d2)
feat(analysis/normed_space/affine_isometry): new file, bundled affine isometries ([#8660](https://github.com/leanprover-community/mathlib/pull/8660))
This PR defines bundled affine isometries and affine isometry equivs, adapting the theory more or less wholesale from the linear isometry and affine map theories.
In follow-up PRs I re-work the Mazur-Ulam and Euclidean geometry libraries to use these objects where appropriate.

### [2021-08-18 12:08:51](https://github.com/leanprover-community/mathlib/commit/d1b34f7)
feat(ring_theory): define the ideal class group ([#8626](https://github.com/leanprover-community/mathlib/pull/8626))
This PR defines the ideal class group of an integral domain, as the quotient of the invertible fractional ideals by the principal fractional ideals. It also shows that this corresponds to the more traditional definition in a Dedekind domain, namely the quotient of the nonzero ideals by `I ~ J ↔ ∃ xy, xI = yJ`.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr

### [2021-08-18 10:32:47](https://github.com/leanprover-community/mathlib/commit/a0aee51)
chore({group,ring}_theory/sub{group,monoid,ring,semiring}): Add missing scalar action typeclasses ([#8731](https://github.com/leanprover-community/mathlib/pull/8731))
This adds `has_faithful_scalar` and `mul_semiring_action` instances for simple subtypes. 
Neither typeclass associates any new actions with these types; they just provide additionally properties of the existing actions.

### [2021-08-18 10:32:46](https://github.com/leanprover-community/mathlib/commit/6bd6c11)
refactor(field_theory,ring_theory): generalize adjoin_root.equiv to `power_basis` ([#8726](https://github.com/leanprover-community/mathlib/pull/8726))
We had two proofs that `A`-preserving maps from `A[x]` or `A(x)` to `B` are in bijection with the set of conjugate roots to `x` in `B`, so by stating the result for `power_basis` we can avoid reproving it twice, and get some generalizations (to a `comm_ring` instead of an `integral_domain`) for free.
There's probably a bit more to generalize in `adjoin_root` or `intermediate_field.adjoin`, which I will do in follow-up PRs.

### [2021-08-18 10:32:45](https://github.com/leanprover-community/mathlib/commit/3de385a)
feat(ring_theory/dedekind_domain): prime elements of `ideal A` are the prime ideals ([#8718](https://github.com/leanprover-community/mathlib/pull/8718))
This shows that Dedekind domains have unique factorization into prime *ideals*, not just prime *elements* of the monoid `ideal A`.
After some thinking, I believe Dedekind domains are the most common setting in which this equality hold. If anyone has a reference showing how to generalize this, that would be much appreciated.

### [2021-08-18 10:32:44](https://github.com/leanprover-community/mathlib/commit/f1b6c8f)
feat(data/matrix/kronecker): add two lemmas ([#8700](https://github.com/leanprover-community/mathlib/pull/8700))
Added two lemmas `kronecker_map_assoc` and `kronecker_assoc` showing associativity of the Kronecker product

### [2021-08-18 08:28:19](https://github.com/leanprover-community/mathlib/commit/5335c67)
refactor(topology/algebra/ring): `topological_ring` extends `topological_add_group` ([#8709](https://github.com/leanprover-community/mathlib/pull/8709))

### [2021-08-18 08:28:18](https://github.com/leanprover-community/mathlib/commit/1151611)
feat(algebra/pointwise): instances in locale pointwise ([#8689](https://github.com/leanprover-community/mathlib/pull/8689))
@rwbarton and @bryangingechen mentioned in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Friday.20afternoon.20puzzle.20--.2037.20.E2.88.88.2037.3F that we should put pointwise instances on sets in a locale.
This PR does that. You now have to write `open_locale pointwise` to get algebraic operations on sets and finsets.

### [2021-08-18 08:28:17](https://github.com/leanprover-community/mathlib/commit/efa34dc)
feat(data/list/perm): nodup_permutations ([#8616](https://github.com/leanprover-community/mathlib/pull/8616))
A simpler version of [#8494](https://github.com/leanprover-community/mathlib/pull/8494)
TODO: `nodup s.permutations ↔ nodup s`
TODO: `count s s.permutations = (zip_with count s s.tails).prod`

### [2021-08-18 07:53:20](https://github.com/leanprover-community/mathlib/commit/41f7b5b)
feat(linear_algebra/clifford_algebra/equivs): there is a clifford algebra isomorphic to every quaternion algebra ([#8670](https://github.com/leanprover-community/mathlib/pull/8670))
The proofs are not particularly fast here unfortunately.

### [2021-08-18 05:11:57](https://github.com/leanprover-community/mathlib/commit/40b7dc7)
chore(data/set/function): remove useless @[simp] ([#8736](https://github.com/leanprover-community/mathlib/pull/8736))
This lemma
```
lemma eq_on_empty (f₁ f₂ : α → β) : eq_on f₁ f₂ ∅ := λ x, false.elim
```
is currently marked `@[simp]`, but can never fire, because after noting `eq_on` is `@[reducible]`, the pattern we would be replacing looks like `?f ?x`, which Lean3's simp doesn't like.
On the other hand, @dselsam's experiments with discrimination trees in simp in the binport of mathlib are spending most of their time on this lemma!
Let's get rid of it.

### [2021-08-18 03:17:06](https://github.com/leanprover-community/mathlib/commit/cb3d5db)
feat(algebra/ordered_monoid): generalize {min,max}_mul_mul_{left,right} ([#8725](https://github.com/leanprover-community/mathlib/pull/8725))
Before, it has assumptions about `cancel_comm_monoid` for all the lemmas.
In fact, they hold under much weaker `has_mul`.

### [2021-08-18 02:21:49](https://github.com/leanprover-community/mathlib/commit/e23e6eb)
chore(scripts): update nolints.txt ([#8735](https://github.com/leanprover-community/mathlib/pull/8735))
I am happy to remove some nolints for you!

### [2021-08-18 00:41:07](https://github.com/leanprover-community/mathlib/commit/ce965a5)
feat(measure_theory/decomposition/lebesgue): the Lebesgue decomposition theorem ([#8687](https://github.com/leanprover-community/mathlib/pull/8687))
This PR proves the existence and uniqueness of the Lebesgue decompositions theorem which is the last step before proving the Radon-Nikodym theorem 🎉

### [2021-08-17 22:18:00](https://github.com/leanprover-community/mathlib/commit/67501f6)
feat(algebra): generalize `ring_hom.map_dvd` ([#8722](https://github.com/leanprover-community/mathlib/pull/8722))
Now it is available for `mul_hom` and `monoid_hom`, and in a `monoid` (or `semiring` in the `ring_hom` case), not just `comm_semiring`

### [2021-08-17 21:07:52](https://github.com/leanprover-community/mathlib/commit/e6e5718)
chore(lie/semisimple): tweak `lie_algebra.subsingleton_of_semisimple_lie_abelian` ([#8728](https://github.com/leanprover-community/mathlib/pull/8728))

### [2021-08-17 21:07:51](https://github.com/leanprover-community/mathlib/commit/31d5549)
docs(overview): nilpotent and presented groups ([#8711](https://github.com/leanprover-community/mathlib/pull/8711))

### [2021-08-17 18:30:13](https://github.com/leanprover-community/mathlib/commit/5b5b432)
fix(tactic/tfae): remove unused arg in tfae_have ([#8727](https://github.com/leanprover-community/mathlib/pull/8727))
Since this "discharger" argument is not using the interactive tactic parser, you can only give names of tactics here, and in any case it's unused by the body, so there is no point in specifying the discharger in the first place.

### [2021-08-17 18:30:12](https://github.com/leanprover-community/mathlib/commit/e0656d1)
chore(algebra/module/basic): golf a proof ([#8723](https://github.com/leanprover-community/mathlib/pull/8723))

### [2021-08-17 18:30:11](https://github.com/leanprover-community/mathlib/commit/579ec7d)
feat(ring_theory/power_basis): `pb.minpoly_gen = minpoly pb.gen` ([#8719](https://github.com/leanprover-community/mathlib/pull/8719))
It actually kind of surprised me that this lemma was never added!

### [2021-08-17 18:30:10](https://github.com/leanprover-community/mathlib/commit/fefdcf5)
feat(tactic/lint): add universe linter ([#8685](https://github.com/leanprover-community/mathlib/pull/8685))
* The linter checks that there are no bad `max u v` occurrences in declarations (bad means that neither `u` nor `v` occur by themselves). See documentation for more details.
* `meta/expr` now imports `meta/rb_map` (but this doesn't give any new transitive imports, so it barely matters). I also removed a transitive import from `meta/rb_map`.

### [2021-08-17 18:30:09](https://github.com/leanprover-community/mathlib/commit/3453f7a)
docs(order/filter/partial): add module docstring ([#8620](https://github.com/leanprover-community/mathlib/pull/8620))
Fix up some names:
* `core_preimage_gc ` -> `image_core_gc`
* `rtendsto_iff_le_comap` -> `rtendsto_iff_le_rcomap`
Add whitespaces around tokens

### [2021-08-17 18:30:08](https://github.com/leanprover-community/mathlib/commit/90fc064)
chore(algebra/associated): use more dot notation ([#8556](https://github.com/leanprover-community/mathlib/pull/8556))
I was getting annoyed that working with definitions such as `irreducible`, `prime` and `associated`, I had to write quite verbose terms like `dvd_symm_of_irreducible (irreducible_of_prime (prime_of_factor _ hp)) (irreducible_of_prime (prime_of_factor _ hq)) hdvd`, where a lot of redundancy can be eliminated with dot notation: `(prime_of_factor _ hp).irreducible.dvd_symm (prime_of_factor _ hq).irreducible hdvd`. This PR changes the spelling of many of the lemmas in `algebra/associated.lean` to make usage of dot notation easier. It also adds a few shortcut lemmas that address common patterns.
Since this change touches a lot of files, I'll add a RFC label / [open a thread on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/RFC.3A.20adding.20dot.20notations.20.238556) to see what everyone thinks.
Renamings:
 * `irreducible_of_prime` → `prime.irreducible`
 * `dvd_symm_of_irreducible` → `irreducible.dvd_symm`
 * `dvd_symm_iff_of_irreducible` → `irreducible.dvd_comm` (cf. `eq.symm` versus `eq_comm`)
 * `associated_mul_mul` → `associated.mul_mul`
 * `associated_pow_pow` → `associated.pow_pow`
 * `dvd_of_associated` → `associated.dvd`
 * `dvd_dvd_of_associated` → `associated.dvd_dvd`
 * `dvd_iff_dvd_of_rel_{left,right}` → `associated.dvd_iff_dvd_{left,right}`
 * `{eq,ne}_zero_iff_of_associated` → `associated.{eq,ne}_zero_iff`
 * `{irreducible,prime}_of_associated` → `associated.{irreducible,prime}`
 * `{irreducible,is_unit,prime}_iff_of_associated` → `associated.{irreducible,is_unit,prime}_iff`
  * `associated_of_{irreducible,prime}_of_dvd` → `{irreducible,prime}.associated_of_dvd`
 * `gcd_eq_of_associated_{left,right}` → `associated.gcd_eq_{left,right}`
 * `{irreducible,prime}_of_degree_eq_one_of_monic` → `monic.{irreducible,prime}_of_degree_eq_one`
  * `gcd_monoid.prime_of_irreducible` → `irreducible.prime` (since the GCD case is probably the only case we care about for this implication. And we could generalize to Schreier domains if not)
Additions:
 * `associated.is_unit := (associated.is_unit_iff _).mp` (to match `associated.prime` and `associated.irreducible`)
 * `associated.mul_left := associated.mul_mul (associated.refl _) _`
 * `associated.mul_right := associated.mul_mul _  (associated.refl _)`
Other changes:
 * `associated_normalize`, `normalize_associated`, `associates.mk_normalize`, `normalize_apply`, `prime_X_sub_C`: make their final parameter explicit, since it is only inferrable when trying to apply these lemmas. This change helped to golf a few proofs from tactic mode to term mode.
 * slight golfing and style fixes

### [2021-08-17 16:30:01](https://github.com/leanprover-community/mathlib/commit/508b13e)
chore(*): flip various `subsingleton_iff`, `nontrivial_iff` lemmas and add `simp` ([#8703](https://github.com/leanprover-community/mathlib/pull/8703))

### [2021-08-17 13:05:54](https://github.com/leanprover-community/mathlib/commit/450c2d0)
refactor(algebra/algebra/basic): move restrict_scalars into more appropriate files ([#8712](https://github.com/leanprover-community/mathlib/pull/8712))
This puts:
* `submodule.restrict_scalars` in `submodule.lean` since the proofs are all available there, and this is consistent with how `linear_map.restrict_scalars` is placed.
  This is almost a copy-paste, but all the `R` and `S` variables are swapped to match the existing convention in that file.
* The type alias `restrict_scalars` is now in its own file.
  The docstring at the top of the file is entirely new, but the rest is a direct copy and paste.
The motivation is primarily to reduce the size of `algebra/algebra/basic` a little.

### [2021-08-17 12:21:22](https://github.com/leanprover-community/mathlib/commit/0c145d8)
feat(measure_theory/measure/measure_space): add formula for `(map f μ).to_outer_measure` ([#8714](https://github.com/leanprover-community/mathlib/pull/8714))

### [2021-08-17 10:49:29](https://github.com/leanprover-community/mathlib/commit/4df3fb9)
chore(topology/maps): add tendsto_nhds_iff lemmas ([#8693](https://github.com/leanprover-community/mathlib/pull/8693))
This adds lemmas of the form `something.tendsto_nhds_iff` to ease use.
I also had to get lemmas out of a section because `α` was duplicated and that caused typechecking problems.

### [2021-08-17 09:42:21](https://github.com/leanprover-community/mathlib/commit/edb0ba4)
chore(measure_theory/measure/hausdorff): golf ([#8706](https://github.com/leanprover-community/mathlib/pull/8706))
* add a `mk_metric` version of `hausdorff_measure_le`, add `finset.sum` versions for both `mk_metric` and `hausdorff_measure`;
* slightly golf the proof.

### [2021-08-17 08:38:06](https://github.com/leanprover-community/mathlib/commit/0591c27)
feat(ring_theory/fractional_ideal): lemmas on `span_singleton _ x * I` ([#8624](https://github.com/leanprover-community/mathlib/pull/8624))
Useful in proving the basic properties of the ideal class group. See also [#8622](https://github.com/leanprover-community/mathlib/pull/8622) which proves similar things for integral ideals.

### [2021-08-17 01:58:23](https://github.com/leanprover-community/mathlib/commit/b6f1214)
chore(scripts): update nolints.txt ([#8715](https://github.com/leanprover-community/mathlib/pull/8715))
I am happy to remove some nolints for you!

### [2021-08-16 18:56:34](https://github.com/leanprover-community/mathlib/commit/1263906)
chore(data/nat/pairing): add `pp_nodot`, fix some non-finalizing `simp`s ([#8705](https://github.com/leanprover-community/mathlib/pull/8705))

### [2021-08-16 18:56:33](https://github.com/leanprover-community/mathlib/commit/40d2602)
chore(analysis/calculus/deriv): weaker assumptions for `deriv_mul_const` ([#8704](https://github.com/leanprover-community/mathlib/pull/8704))

### [2021-08-16 18:56:32](https://github.com/leanprover-community/mathlib/commit/d5ce7e5)
chore(data/vector): rename vector2 ([#8697](https://github.com/leanprover-community/mathlib/pull/8697))
This file was named this way to avoid clashing with `data/vector.lean` in core.
This renames it to `data/vector/basic.lean` which avoids the problem.
There was never a `vector2` definition, this was only ever a filename.

### [2021-08-16 16:19:26](https://github.com/leanprover-community/mathlib/commit/253712e)
feat(ring_theory/ideal): lemmas on `ideal.span {x} * I` ([#8622](https://github.com/leanprover-community/mathlib/pull/8622))
Originally created for being used in the context of the ideal class group, but didn't end up being used. Hopefully they are still useful for others.

### [2021-08-16 16:19:25](https://github.com/leanprover-community/mathlib/commit/65b0c58)
feat(ring_theory/localization): some lemmas on `coe_submodule` ([#8621](https://github.com/leanprover-community/mathlib/pull/8621))
A small assortment of results on `is_localization.coe_submodule`, needed for elementary facts about the ideal class group.

### [2021-08-16 16:19:24](https://github.com/leanprover-community/mathlib/commit/80b699b)
chore(ring_theory): generalize `non_zero_divisors` lemmas to `monoid_with_zero` ([#8607](https://github.com/leanprover-community/mathlib/pull/8607))
None of the results about `non_zero_divisors` needed a ring structure, just a `monoid_with_zero`. So the generalization is obvious.
Shall we move this file to the `algebra` namespace sometime soon?

### [2021-08-16 16:19:23](https://github.com/leanprover-community/mathlib/commit/106bd3b)
feat(group_theory/nilpotent): add nilpotent groups ([#8538](https://github.com/leanprover-community/mathlib/pull/8538))
We make basic definitions of nilpotent groups and prove the standard theorem that a group is nilpotent iff the upper resp. lower central series reaches top resp. bot.

### [2021-08-16 16:19:22](https://github.com/leanprover-community/mathlib/commit/a55084f)
feat(data/fintype/basic): card_sum, card_subtype_or ([#8490](https://github.com/leanprover-community/mathlib/pull/8490))

### [2021-08-16 16:19:21](https://github.com/leanprover-community/mathlib/commit/f8241b7)
feat(algebra/big_operators/basic): prod_subsingleton ([#8423](https://github.com/leanprover-community/mathlib/pull/8423))

### [2021-08-16 16:19:20](https://github.com/leanprover-community/mathlib/commit/e195347)
feat(finsupp/basic): lemmas about emb_domain ([#7883](https://github.com/leanprover-community/mathlib/pull/7883))

### [2021-08-16 15:18:10](https://github.com/leanprover-community/mathlib/commit/53d97e1)
puzzle(archive/oxford_invariants): Oxford Invariants Puzzle Challenges, Summer 2021, Week 3, Problem 1 ([#8656](https://github.com/leanprover-community/mathlib/pull/8656))
This is a formalisation of a problem posed by the Oxford Invariants.
Co-authored by @b-mehta

### [2021-08-16 15:18:08](https://github.com/leanprover-community/mathlib/commit/55b2e86)
feat(analysis/normed_space): normed group hom completion ([#8499](https://github.com/leanprover-community/mathlib/pull/8499))
From LTE

### [2021-08-16 15:18:07](https://github.com/leanprover-community/mathlib/commit/217308c)
feat(analysis): `x^y` is smooth as a function of `(x, y)` ([#8262](https://github.com/leanprover-community/mathlib/pull/8262))

### [2021-08-16 13:12:47](https://github.com/leanprover-community/mathlib/commit/d6aae6c)
feat(tactic/abel): check for defeq of atoms instead of syntactic eq ([#8628](https://github.com/leanprover-community/mathlib/pull/8628))
I had a call to `abel` break after adding a new typeclass instance, and it turns out this was because two terms became defeq-but-not-syntactically-eq. This PR modifies the equality check in `abel` to follow the implementation in e.g. `ring`.
By default, `abel` now unifies atoms up to `reducible`, which should not have a huge impact on build times. Use `abel!` for trying to unify up to `semireducible`.
I also renamed the `tactic.abel.cache` to `tactic.abel.context`, since we store more things in there than a few elaborated terms. To appease the docstring linter, I added docs for all of the renamed `def`s.

### [2021-08-16 11:55:51](https://github.com/leanprover-community/mathlib/commit/deedf25)
feat(algebra/lie/semisimple): adjoint action is injective for semisimple Lie algebras ([#8698](https://github.com/leanprover-community/mathlib/pull/8698))

### [2021-08-16 08:39:16](https://github.com/leanprover-community/mathlib/commit/c416a48)
feat(algebra/gcd_monoid): move the `gcd_monoid nat` instance ([#7180](https://github.com/leanprover-community/mathlib/pull/7180))
moves `gcd_monoid nat` instance, removes corresponding todos.
removes:
* `nat.normalize_eq` -- use `normalize_eq` instead
renames:
* `nat.gcd_eq_gcd` to `gcd_eq_nat_gcd`
* `nat.lcm_eq_lcm` to `lcm_eq_nat_lcm`

### [2021-08-16 08:06:39](https://github.com/leanprover-community/mathlib/commit/2b43587)
feat(measure_theory/hausdorff_measure): Hausdorff measure and volume coincide in pi types ([#8554](https://github.com/leanprover-community/mathlib/pull/8554))
co-authored by Yury Kudryashov

### [2021-08-16 06:19:36](https://github.com/leanprover-community/mathlib/commit/a983f24)
fix(*): fix universe levels ([#8677](https://github.com/leanprover-community/mathlib/pull/8677))
The universe levels in the following declarations have been fixed . 
This means that there was an argument of the form `Type (max u v)` or `Sort (max u v)`, which could be generalized to `Type u` or `Sort u`. In a few cases, I made explicit that there is a universe restriction (sometimes `max u v` is legitimately used as an arbitrary universe level higher than `u`)
In some files I also cleaned up some declarations around these.
```
algebraic_geometry.Spec.SheafedSpace_map
algebraic_geometry.Spec.to_SheafedSpace
algebraic_geometry.Spec.to_PresheafedSpace
category_theory.discrete_is_connected_equiv_punit
writer_t.uliftable'
writer_t.uliftable
equiv.prod_equiv_of_equiv_nat
free_algebra.dim_eq
linear_equiv.alg_conj
module.flat
cardinal.add_def
slim_check.injective_function.mk
topological_add_group.of_nhds_zero'
topological_group.of_nhds_one'
topological_group.of_comm_of_nhds_one
topological_add_group.of_comm_of_nhds_zero
has_continuous_mul.of_nhds_one
has_continuous_add.of_nhds_zero
has_continuous_add_of_comm_of_nhds_zero
has_continuous_mul_of_comm_of_nhds_one
uniform_space_of_compact_t2
AddCommGroup.cokernel_iso_quotient
algebraic_geometry.Scheme
algebraic_geometry.Scheme.Spec_obj
simplex_category.skeletal_functor
category_theory.Type_to_Cat.full
CommMon_.equiv_lax_braided_functor_punit.lax_braided_to_CommMon
CommMon_.equiv_lax_braided_functor_punit.unit_iso
Mon_.equiv_lax_monoidal_functor_punit.lax_monoidal_to_Mon
Mon_.equiv_lax_monoidal_functor_punit.unit_iso
uliftable.down_map
weak_dual.has_continuous_smul
stone_cech_equivalence
Compactum_to_CompHaus.full
TopCommRing.category_theory.forget₂.category_theory.reflects_isomorphisms
```

### [2021-08-16 05:42:56](https://github.com/leanprover-community/mathlib/commit/69785fe)
chore(scripts): update nolints.txt ([#8696](https://github.com/leanprover-community/mathlib/pull/8696))
I am happy to remove some nolints for you!

### [2021-08-16 03:52:43](https://github.com/leanprover-community/mathlib/commit/b97344c)
chore(algebra/module): Swap the naming of `smul_(left|right)_injective` to match the naming guide ([#8659](https://github.com/leanprover-community/mathlib/pull/8659))
The naming conventions say:
> An injectivity lemma that uses "left" or "right" should refer to the argument that "changes". For example, a lemma with the statement `a - b = a - c ↔ b = c` could be called `sub_right_inj`.
This corrects the name of `function.injective (λ c : R, c • x)` to be `smul_left_injective` instead of the previous `smul_right_injective`, and vice versa for `function.injective (λ x : M, r • x)`.
This also brings it in line with `mul_left_injective` and `mul_right_injective`.

### [2021-08-16 03:52:42](https://github.com/leanprover-community/mathlib/commit/2e9029f)
feat(tactic/ext): add tracing option ([#8633](https://github.com/leanprover-community/mathlib/pull/8633))
Adds an option to trace all lemmas that `ext` tries to apply, along with the time each attempted application takes. This was useful in debugging a slow `ext` call.

### [2021-08-16 02:20:04](https://github.com/leanprover-community/mathlib/commit/59954c1)
docs(data/pfun): add module docstring and def docstrings ([#8629](https://github.com/leanprover-community/mathlib/pull/8629))

### [2021-08-16 02:20:03](https://github.com/leanprover-community/mathlib/commit/46b3fae)
feat(topology/category/*/projective): CompHaus and Profinite have enough projectives ([#8613](https://github.com/leanprover-community/mathlib/pull/8613))

### [2021-08-16 02:20:02](https://github.com/leanprover-community/mathlib/commit/4bf5177)
feat(algebraic_geometry/EllipticCurve): add working definition of elliptic curve ([#8558](https://github.com/leanprover-community/mathlib/pull/8558))
The word "elliptic curve" is used in the literature in many different ways. Differential geometers use it to mean a 1-dimensional complex torus. Algebraic geometers nowadays use it to mean some morphism of schemes with a section and some axioms. However classically number theorists used to use a low-brow definition of the form y^2=cubic in x; this works great when the base scheme is, for example, Spec of the rationals. 
It occurred to me recently that the standard minor modification of the low-brow definition works for all commutative rings with trivial Picard group, and because this covers a lot of commutative rings (e.g. all fields, all PIDs, all integral domains with trivial class group) it would not be unreasonable to have it as a working definition in mathlib. The advantage of this definition is that people will be able to begin writing algorithms which compute various invariants of the curve, for example we can begin to formally verify the database of elliptic curves at LMFDB.org .

### [2021-08-16 01:12:19](https://github.com/leanprover-community/mathlib/commit/ec68c7e)
feat(set_theory/cardinal): lift_sup ([#8675](https://github.com/leanprover-community/mathlib/pull/8675))

### [2021-08-16 00:24:41](https://github.com/leanprover-community/mathlib/commit/462359d)
feat(measure): prove Haar measure = Lebesgue measure on R ([#8639](https://github.com/leanprover-community/mathlib/pull/8639))

### [2021-08-15 23:17:23](https://github.com/leanprover-community/mathlib/commit/8e50863)
chore(analysis/normed_space/dual): golf some proofs ([#8694](https://github.com/leanprover-community/mathlib/pull/8694))

### [2021-08-15 21:24:22](https://github.com/leanprover-community/mathlib/commit/8ac0242)
feat(topology/algebra/ring): pi instances ([#8686](https://github.com/leanprover-community/mathlib/pull/8686))
Add instances `pi.topological_ring` and `pi.topological_semiring`.

### [2021-08-15 21:24:21](https://github.com/leanprover-community/mathlib/commit/9af80f3)
feat(algebra/opposites): more scalar action instances ([#8672](https://github.com/leanprover-community/mathlib/pull/8672))
This adds weaker and stronger versions of `monoid.to_opposite_mul_action` for `has_mul`, `monoid_with_zero`, and `semiring`. It also adds an `smul_comm_class` instance.

### [2021-08-15 21:24:20](https://github.com/leanprover-community/mathlib/commit/fc7da8d)
chore(data/vector3): extract to a new file ([#8669](https://github.com/leanprover-community/mathlib/pull/8669))
This is simply a file move, with no other changes other than a minimal docstring.
In it's old location this was very hard to find.

### [2021-08-15 21:24:18](https://github.com/leanprover-community/mathlib/commit/6aefa38)
chore(topology/algebra/*,analysis/specific_limits): continuity of `fpow` ([#8665](https://github.com/leanprover-community/mathlib/pull/8665))
* add more API lemmas about continuity of `x ^ n` for natural and integer `n`;
* prove that `x⁻¹` and `x ^ n`, `n < 0`, are discontinuous at zero.

### [2021-08-15 21:24:18](https://github.com/leanprover-community/mathlib/commit/fddc1f4)
doc(tactic/congr): improve convert_to docs ([#8664](https://github.com/leanprover-community/mathlib/pull/8664))
The docs should explain how `convert` and `convert_to` differ.

### [2021-08-15 19:29:26](https://github.com/leanprover-community/mathlib/commit/ca5987f)
chore(data/set/basic): add `image_image` and `preimage_preimage` to `function.left_inverse` ([#8688](https://github.com/leanprover-community/mathlib/pull/8688))

### [2021-08-15 13:05:32](https://github.com/leanprover-community/mathlib/commit/bf6eeb2)
feat(data/list/cycle): cycle.map and has_repr ([#8170](https://github.com/leanprover-community/mathlib/pull/8170))

### [2021-08-15 07:43:38](https://github.com/leanprover-community/mathlib/commit/0bb283b)
feat(algebra/bounds): add `csupr_mul` etc ([#8584](https://github.com/leanprover-community/mathlib/pull/8584))
* add `csupr_mul`, `mul_csupr`, `csupr_div`, `csupr_add`,
  `mul_csupr`, `add_csupr`, `csupr_sub`;
* add `is_lub_csupr`, `is_lub_csupr_set`, `is_glb_cinfi`,
  `is_glb_cinfi_set`;
* add `is_lub.csupr_eq`, `is_lub.csupr_set_eq`, `is_glb.cinfi_eq`,
  `is_glb.cinfi_set_eq`;
* add `is_greatest.Sup_mem`, `is_least.Inf_mem`;
* add lemmas about `galois_connection` and `Sup`/`Inf` in
  conditionally complete lattices;
* add lemmas about `order_iso` and `Sup`/`Inf` in conditionally
  complete lattices.

### [2021-08-15 02:59:48](https://github.com/leanprover-community/mathlib/commit/b7d980c)
feat(topology/algebra/weak_dual_topology + analysis/normed_space/weak_dual_of_normed_space): add definition and first lemmas about weak-star topology ([#8598](https://github.com/leanprover-community/mathlib/pull/8598))
Add definition and first lemmas about weak-star topology.

### [2021-08-15 02:18:05](https://github.com/leanprover-community/mathlib/commit/ff721ad)
chore(scripts): update nolints.txt ([#8676](https://github.com/leanprover-community/mathlib/pull/8676))
I am happy to remove some nolints for you!

### [2021-08-15 00:01:46](https://github.com/leanprover-community/mathlib/commit/708d99a)
feat(data/real/ennreal): add `to_real_sub_of_le` ([#8674](https://github.com/leanprover-community/mathlib/pull/8674))

### [2021-08-15 00:01:45](https://github.com/leanprover-community/mathlib/commit/4644447)
fix(tactic/norm_cast): assumption_mod_cast should only work on one goal ([#8649](https://github.com/leanprover-community/mathlib/pull/8649))
fixes [#8438](https://github.com/leanprover-community/mathlib/pull/8438)

### [2021-08-14 23:29:05](https://github.com/leanprover-community/mathlib/commit/c4208d2)
chore(measure_theory): fix namespace in docstrings for docgen ([#8671](https://github.com/leanprover-community/mathlib/pull/8671))

### [2021-08-14 13:38:26](https://github.com/leanprover-community/mathlib/commit/8f863f6)
feat(measure_theory/decomposition/jordan): the Jordan decomposition theorem for signed measures ([#8645](https://github.com/leanprover-community/mathlib/pull/8645))
This PR proves the Jordan decomposition theorem for signed measures, that is, given a signed measure `s`, there exists a unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.

### [2021-08-14 11:55:36](https://github.com/leanprover-community/mathlib/commit/ba76bf7)
chore(data/option,data/set): a few lemmas, golf ([#8636](https://github.com/leanprover-community/mathlib/pull/8636))
* add `option.subsingleton_iff_is_empty` and an instance
  `option.unique`;
* add `set.is_compl_range_some_none`, `set.compl_range_some`,
  `set.range_some_inter_none`, `set.range_some_union_none`;
* split the proof of `set.pairwise_on_eq_iff_exists_eq` into
  `set.nonempty.pairwise_on_eq_iff_exists_eq` and
  `set.pairwise_on_eq_iff_exists_eq`.
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)

### [2021-08-14 10:40:01](https://github.com/leanprover-community/mathlib/commit/721f571)
feat(linear_algebra/basic) : add a small lemma for simplifying a map between equivalent quotient spaces ([#8640](https://github.com/leanprover-community/mathlib/pull/8640))

### [2021-08-14 06:36:18](https://github.com/leanprover-community/mathlib/commit/c765b04)
chore(data/(int, nat)/modeq): rationalize lemma names ([#8644](https://github.com/leanprover-community/mathlib/pull/8644))
Many `modeq` lemmas were called `nat.modeq.modeq_something` or `int.modeq.modeq_something`. I'm deleting the duplicated `modeq`, so that lemmas (usually) become `nat.modeq.something` and `int.modeq.something`. Most of them must be `protected`.
This facilitates greatly the use of dot notation on `nat.modeq` and `int.modeq` while shortening lemma names.
I'm adding a few lemmas:
* `nat.modeq.rfl`, `int.modeq.rfl`
* `nat.modeq.dvd`, `int.modeq.dvd`
* `nat.modeq_of_dvd`, `int.modeq_of_dvd`
* `has_dvd.dvd.modeq_zero_nat`, `has_dvd.dvd.zero_modeq_nat`, `has_dvd.dvd.modeq_zero_int`, `has_dvd.dvd.zero_modeq_int`
* `nat.modeq.add_left`, `nat.modeq.add_right`, `int.modeq.add_left`, `int.modeq.add_right`
* `nat.modeq.add_left_cancel'`, `nat.modeq.add_right_cancel'`, `int.modeq.add_left_cancel'`, `int.modeq.add_right_cancel'`
* `int.modeq.sub_left`, `int.modeq.sub_right`
* `nat.modeq_sub`, `int.modeq_sub`
* `int.modeq_one`
* `int.modeq_pow`
I'm also renaming some lemmas (on top of the general renaming):
* `add_cancel_left` -> `add_left_cancel`, `add_cancel_right` -> `add_right_cancel`
* `modeq_zero_iff` -> `modeq_zero_iff_dvd` in prevision of an upcoming PR

### [2021-08-14 04:51:40](https://github.com/leanprover-community/mathlib/commit/679a8a7)
docs(data/int/basic): add module docstring ([#8655](https://github.com/leanprover-community/mathlib/pull/8655))

### [2021-08-14 02:16:22](https://github.com/leanprover-community/mathlib/commit/36826cb)
chore(scripts): update nolints.txt ([#8666](https://github.com/leanprover-community/mathlib/pull/8666))
I am happy to remove some nolints for you!

### [2021-08-14 02:16:21](https://github.com/leanprover-community/mathlib/commit/1b1088c)
feat(linear_algeba/linear_independent): coe_range ([#8341](https://github.com/leanprover-community/mathlib/pull/8341))

### [2021-08-14 00:25:39](https://github.com/leanprover-community/mathlib/commit/50d3de9)
feat(logic/basic): a few lemmas about `xor` ([#8650](https://github.com/leanprover-community/mathlib/pull/8650))
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)

### [2021-08-13 21:43:57](https://github.com/leanprover-community/mathlib/commit/94e4667)
feat(order/filter): change definition of inf ([#8657](https://github.com/leanprover-community/mathlib/pull/8657))
The current definition of `filter.inf` came directly from the Galois insertion: `u ∈ f ⊓ g` if it contains `s ∩ t` for some `s ∈ f` and `t ∈ g`, but the new one is tidier: `u ∈ f ⊓ g` if `u = s ∩ t` for some `s ∈ f` and `t ∈ g`. This gives a stronger assertion to work with when assuming a set belongs to a filter inf. On the other hand it makes it harder to prove such a statement so we keep the old version as a lemma `filter.mem_inf_of_inter :  ∀ {f g : filter α} {s t u : set α}, s ∈ f → t ∈ g → s ∩ t ⊆ u → u ∈ f ⊓ g`.
Also renames lots of lemmas to remove the word "sets" that was a remnant of the very early days.
In passing I also changed the simp lemma `filter.mem_map` from  `t ∈ map m f ↔ {x | m x ∈ t} ∈ f` to 
`t ∈ map m f ↔ m ⁻¹' t ∈ f` which seemed more normal form to me. But this led to a lot of breakage, so I also kept the old version as `mem_map'`.

### [2021-08-13 20:14:43](https://github.com/leanprover-community/mathlib/commit/fdeb064)
feat(topology/*): lemmas about `dense`/`dense_range` and `is_(pre)connected` ([#8651](https://github.com/leanprover-community/mathlib/pull/8651))
* add `dense_compl_singleton`;
* extract new lemma `is_preconnected_range` from the proof of
  `is_connected_range`;
* add `dense_range.preconnected_space` and
  `dense_inducing.preconnected_space`;
* rename `self_sub_closure_image_preimage_of_open` to
  `self_subset_closure_image_preimage_of_open`.
Inspired by [#8579](https://github.com/leanprover-community/mathlib/pull/8579)

### [2021-08-13 18:20:13](https://github.com/leanprover-community/mathlib/commit/8b9c4cf)
fix(tactic/core): fix incorrect uses of with_ident_list ([#8653](https://github.com/leanprover-community/mathlib/pull/8653))
`with_ident_list` uses `tk "with" >> ident_*`, which is incorrect for some tactics, where `_` doesn't mean anything. (It is good for tactics that name hypotheses like `cases`, but not tactics that use the list to reference hypotheses like `revert_deps`.)

### [2021-08-13 18:20:12](https://github.com/leanprover-community/mathlib/commit/7f5d5b9)
feat(ring_theory): ideals in a Dedekind domain have unique factorization ([#8530](https://github.com/leanprover-community/mathlib/pull/8530))

### [2021-08-13 17:03:29](https://github.com/leanprover-community/mathlib/commit/8eca293)
feat(field_theory): more general `algebra _ (algebraic_closure k)` instance ([#8658](https://github.com/leanprover-community/mathlib/pull/8658))
For example, now we can take a field extension `L / K` and map `x : K` into the algebraic closure of `L`.

### [2021-08-13 17:03:28](https://github.com/leanprover-community/mathlib/commit/c711909)
feat(linear_algebra/basic, group_theory/quotient_group, algebra/lie/quotient): ext lemmas for morphisms out of quotients ([#8641](https://github.com/leanprover-community/mathlib/pull/8641))
This allows `ext` to see through quotients by subobjects of a type `A`, and apply ext lemmas specific to `A`.

### [2021-08-13 15:23:28](https://github.com/leanprover-community/mathlib/commit/9e83de2)
feat(data/list/perm): subperm_ext_iff ([#8504](https://github.com/leanprover-community/mathlib/pull/8504))
A helper lemma to construct proofs of `l <+~ l'`. On the way to proving
`l ~ l' -> l.permutations ~ l'.permutations`.

### [2021-08-13 08:01:49](https://github.com/leanprover-community/mathlib/commit/733e6e3)
chore(*): update lean to 3.32.1 ([#8652](https://github.com/leanprover-community/mathlib/pull/8652))

### [2021-08-13 06:38:14](https://github.com/leanprover-community/mathlib/commit/03ddb8d)
feat(finsupp/basic): restrict a finitely supported function on option A to A ([#8342](https://github.com/leanprover-community/mathlib/pull/8342))

### [2021-08-13 05:15:52](https://github.com/leanprover-community/mathlib/commit/d0804ba)
feat(linear_algebra/invariant_basis_number): basic API lemmas ([#7882](https://github.com/leanprover-community/mathlib/pull/7882))

### [2021-08-13 02:17:49](https://github.com/leanprover-community/mathlib/commit/3b37614)
chore(scripts): update nolints.txt ([#8654](https://github.com/leanprover-community/mathlib/pull/8654))
I am happy to remove some nolints for you!

### [2021-08-12 19:28:31](https://github.com/leanprover-community/mathlib/commit/4a864ed)
fix(tactic/core): mk_simp_attribute: remove superfluous disjunct ([#8648](https://github.com/leanprover-community/mathlib/pull/8648))
`with_ident_list` already returns `[]` if `with` is not present.

### [2021-08-12 19:28:30](https://github.com/leanprover-community/mathlib/commit/ce26133)
feat(data/nat/(basic, modeq)): simple lemmas ([#8647](https://github.com/leanprover-community/mathlib/pull/8647))

### [2021-08-12 19:28:29](https://github.com/leanprover-community/mathlib/commit/c2580eb)
refactor(tactic/*): mark internal attrs as `parser := failed` ([#8635](https://github.com/leanprover-community/mathlib/pull/8635))
I saw this trick in some of the other user attributes, and it seems like a good idea to apply generally. Any attribute that is "internal use only" should have its `parser` field set to `failed`, so that it is impossible for the user to write the attribute. It is still possible for meta code to set the attributes programmatically, which is generally what's happening anyway.

### [2021-08-12 19:28:28](https://github.com/leanprover-community/mathlib/commit/8a2a630)
feat(analysis/convex/basic): add lemma add_smul regarding linear combinations of convex sets ([#8608](https://github.com/leanprover-community/mathlib/pull/8608))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-08-12 19:28:27](https://github.com/leanprover-community/mathlib/commit/2412b97)
feat(algebra/quaternion_basis): add a quaternion version of complex.lift ([#8551](https://github.com/leanprover-community/mathlib/pull/8551))
This is some prework to show `clifford_algebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂]` for an appropriate `Q`.
For `complex.lift : {I' // I' * I' = -1} ≃ (ℂ →ₐ[ℝ] A)`, we could just use a subtype. For quaternions, we now have two generators and three relations, so a subtype isn't particularly viable any more; so instead this commit creates a new `quaternion_algebra.basis` structure.

### [2021-08-12 19:28:26](https://github.com/leanprover-community/mathlib/commit/8914b68)
feat(ring_theory/dedekind_domain): ideals in a DD are cancellative  ([#8513](https://github.com/leanprover-community/mathlib/pull/8513))
This PR provides a `comm_cancel_monoid_with_zero` instance on integral ideals in a Dedekind domain.
As a bonus, it deletes an out of date TODO comment.

### [2021-08-12 17:46:21](https://github.com/leanprover-community/mathlib/commit/0f59141)
docs(data/fintype/sort): add module docstring ([#8643](https://github.com/leanprover-community/mathlib/pull/8643))
And correct typo in the docstrings

### [2021-08-12 17:46:20](https://github.com/leanprover-community/mathlib/commit/3689655)
feat(measure_theory/stieltjes_measure): Stieltjes measures associated to monotone functions ([#8266](https://github.com/leanprover-community/mathlib/pull/8266))
Given a monotone right-continuous real function `f`, there exists a measure giving mass `f b - f a` to the interval `(a, b]`. These measures are called Stieltjes measures, and are especially important in probability theory. The real Lebesgue measure is a particular case of this construction, for `f x = x`. This PR extends the already existing construction of the Lebesgue measure to cover all Stieltjes measures.

### [2021-08-12 16:55:31](https://github.com/leanprover-community/mathlib/commit/7b27f46)
feat(measure_theory/vector_measure): a signed measure restricted on a positive set is a unsigned measure ([#8597](https://github.com/leanprover-community/mathlib/pull/8597))
This PR defines `signed_measure.to_measure` which is the measure corresponding to a signed measure restricted on some positive set. This definition is useful for the Jordan decomposition theorem.

### [2021-08-12 15:02:55](https://github.com/leanprover-community/mathlib/commit/ee18995)
feat(algebra/group_with_zero): `units.mk0` is a "monoid hom" ([#8625](https://github.com/leanprover-community/mathlib/pull/8625))
This PR shows that `units.mk0` sends `1` to `1` and `x * y` to `mk0 x * mk0 y`. So it is a monoid hom, if we ignore the proof fields.

### [2021-08-12 15:02:54](https://github.com/leanprover-community/mathlib/commit/e17e9ea)
feat(measure_theory/lp_space): add mem_Lp and integrable lemmas for is_R_or_C.re/im and inner product with a constant ([#8615](https://github.com/leanprover-community/mathlib/pull/8615))

### [2021-08-12 13:21:49](https://github.com/leanprover-community/mathlib/commit/f63c27b)
feat(linear_algebra): Smith normal form for submodules over a PID ([#8588](https://github.com/leanprover-community/mathlib/pull/8588))
This PR expands on `submodule.basis_of_pid` by showing that this basis can be chosen in "Smith normal form". That is: if `M` is a free module over a PID `R` and `N ≤ M`, then we can choose a basis `bN` for `N` and `bM` for `M`, such that the inclusion map from `N` to `M` expressed in these bases is a diagonal matrix in Smith normal form.
The rather gnarly induction in the original `submodule.basis_of_pid` has been turned into an even gnarlier auxiliary lemma that does the inductive step (with the induction hypothesis broken into pieces so we can apply it part by part), followed by a re-proven `submodule.basis_of_pid` that picks out part of this inductive step. Then we feed the full induction hypothesis, along with `submodule.basis_of_pid` into the same induction again, to get `submodule.exists_smith_normal_form_of_le`, and from that we conclude our new results `submodule.exists_smith_normal_form` and `ideal.exists_smith_normal_form`.

### [2021-08-12 09:52:50](https://github.com/leanprover-community/mathlib/commit/e245b24)
feat(data/nat/prime, number_theory/padics/padic_norm): list of prime_pow_factors, valuation of prime power ([#8473](https://github.com/leanprover-community/mathlib/pull/8473))

### [2021-08-12 08:32:26](https://github.com/leanprover-community/mathlib/commit/1b96e97)
feat(data/sym2): card of `sym2 α` ([#8426](https://github.com/leanprover-community/mathlib/pull/8426))
Case `n = 2` of stars and bars

### [2021-08-12 07:04:01](https://github.com/leanprover-community/mathlib/commit/c550e3a)
refactor(group_theory/sylow): make new file about actions of p groups and move lemmas there ([#8595](https://github.com/leanprover-community/mathlib/pull/8595))

### [2021-08-12 07:04:00](https://github.com/leanprover-community/mathlib/commit/0cbab37)
feat(group_theory/subgroup): there are finitely many subgroups of a finite group ([#8593](https://github.com/leanprover-community/mathlib/pull/8593))

### [2021-08-12 07:03:59](https://github.com/leanprover-community/mathlib/commit/cd2b549)
chore(measure_theory/*): make measurable_space arguments implicit, determined by the measure argument ([#8571](https://github.com/leanprover-community/mathlib/pull/8571))
In the measure theory library, most of the definitions that depend on a measure have that form:
```
def example_def {α} [measurable_space α] (μ : measure α) : some_type := sorry
```
Suppose now that we have two `measurable_space` structures on `α` : `{m m0 : measurable_space α}` and we have the measures `μ : measure α` (which is a measure on `m0`) and `μm : @measure α m`. This will be common for probability theory applications. See for example the `conditional_expectation` file.
Then we can write `example_def μ` but we cannot write `example_def μm` because the `measurable_space` inferred is `m0`, which does not match the measurable space on which `μm` is defined. We have to use `@example_def _ m μm` instead.
This PR implements a simple fix: change `[measurable_space α] (μ : measure α)` into `{m : measurable_space α} (μ : measure α)`.
Advantage: we can now use `example_def μm` since the `measurable_space` argument is deduced from the `measure` argument. This removes many `@` in all places where `measure.trim` is used.
Downsides:
- I have to write `(0 : measure α)` instead of `0` in some lemmas.
- I had to add two `apply_instance` to find `borel_space` instances.
- Whenever a lemma takes an explicit measure argument, we have to write `{m : measurable_space α} (μ : measure α)` instead of simply `(μ : measure α)`.

### [2021-08-12 05:23:15](https://github.com/leanprover-community/mathlib/commit/9ab4d28)
doc(tactic/cache): fix haveI docs ([#8637](https://github.com/leanprover-community/mathlib/pull/8637))
Applies [Bhavik's suggestion](https://github.com/leanprover-community/mathlib/pull/8631#discussion_r687260852) which missed the train for [#8631](https://github.com/leanprover-community/mathlib/pull/8631).

### [2021-08-12 03:29:23](https://github.com/leanprover-community/mathlib/commit/036c96b)
fix(tactic/lint): _ is not a linter ([#8634](https://github.com/leanprover-community/mathlib/pull/8634))
The `#lint` parser accepts `ident_`, but as far as I can tell, `_` doesn't mean anything in particular, it just tries and fails to resolve the `linter._` linter. This simplifies the parser to only accept `ident`.

### [2021-08-12 02:18:22](https://github.com/leanprover-community/mathlib/commit/8968739)
chore(scripts): update nolints.txt ([#8638](https://github.com/leanprover-community/mathlib/pull/8638))
I am happy to remove some nolints for you!

### [2021-08-11 23:46:50](https://github.com/leanprover-community/mathlib/commit/f0ae67d)
feat(analysis/normed_space/finite_dimension): asymptotic equivalence preserves summability ([#8596](https://github.com/leanprover-community/mathlib/pull/8596))

### [2021-08-11 21:52:56](https://github.com/leanprover-community/mathlib/commit/ea7e3ff)
feat(tactic/cache): allow optional := in haveI ([#8631](https://github.com/leanprover-community/mathlib/pull/8631))
This syntactic restriction was originally added because it was not possible to reset the instance cache only for a given goal. This limitation has since been lifted (a while ago, I think), and so the syntax can be made more like `have` now.

### [2021-08-11 19:55:20](https://github.com/leanprover-community/mathlib/commit/565fef6)
refactor(tactic/tidy): use @[user_attribute] ([#8630](https://github.com/leanprover-community/mathlib/pull/8630))
This is just a minor change to use the `@[user_attribute]` attribute like all other user attrs instead of calling `attribute.register`. (This came up during the census of mathlib user attrs.)

### [2021-08-11 15:48:56](https://github.com/leanprover-community/mathlib/commit/7b5c60d)
feat(data/equiv/basic): add a small lemma for simplifying map between equivalent quotient spaces induced by equivalent relations ([#8617](https://github.com/leanprover-community/mathlib/pull/8617))
Just adding a small lemma that allows us to compute the composition of the map given by `quot.congr` with `quot.mk`

### [2021-08-11 15:48:55](https://github.com/leanprover-community/mathlib/commit/3ebf9f0)
chore(group_theory/group_action/defs): add a missing is_scalar_tower instance ([#8604](https://github.com/leanprover-community/mathlib/pull/8604))

### [2021-08-11 15:48:53](https://github.com/leanprover-community/mathlib/commit/2489931)
feat(group_theory/perm/cycle_type): purge trunc references ([#8176](https://github.com/leanprover-community/mathlib/pull/8176))

### [2021-08-11 14:09:54](https://github.com/leanprover-community/mathlib/commit/2db8c79)
chore(group_theory/submonoid/membership): missing rfl lemmas ([#8619](https://github.com/leanprover-community/mathlib/pull/8619))

### [2021-08-11 11:38:30](https://github.com/leanprover-community/mathlib/commit/8d0ed03)
feat(data/rat/basic): Add nat num and denom inv lemmas ([#8581](https://github.com/leanprover-community/mathlib/pull/8581))
Add `inv_coe_nat_num`  and `inv_coe_nat_denom` lemmas.
These lemmas show that the denominator and numerator of `1/ n` given `0 < n`, are equal to `n` and `1` respectively.

### [2021-08-11 07:34:47](https://github.com/leanprover-community/mathlib/commit/1d4400c)
feat(analysis/normed_space): controlled surjectivity ([#8498](https://github.com/leanprover-community/mathlib/pull/8498))
From LTE.

### [2021-08-11 06:39:10](https://github.com/leanprover-community/mathlib/commit/9c8602b)
refactor(measure_theory): add subfolder ([#8594](https://github.com/leanprover-community/mathlib/pull/8594))
* This PR adds the subfolders `constructions` `function` `group` `integral` and `measure` to `measure_theory`
* File renamings:
```
group -> group.basic
prod_group -> group.prod
bochner_integration -> integral.bochner
integration -> integral.lebesgue
haar_measure -> measure.haar
lebesgue_measure -> measure.lebesgue
hausdorff_measure -> measure.hausdorff
```

### [2021-08-11 02:38:04](https://github.com/leanprover-community/mathlib/commit/6305769)
chore(scripts): update nolints.txt ([#8614](https://github.com/leanprover-community/mathlib/pull/8614))
I am happy to remove some nolints for you!

### [2021-08-11 02:38:03](https://github.com/leanprover-community/mathlib/commit/3c09987)
docs(data/set/lattice): add module docstring ([#8250](https://github.com/leanprover-community/mathlib/pull/8250))
This also cleans up some whitespace and replaces some `assume`s with `λ`s

### [2021-08-11 00:53:34](https://github.com/leanprover-community/mathlib/commit/694dd11)
feat(archive/imo): IMO 2001 Q6 ([#8327](https://github.com/leanprover-community/mathlib/pull/8327))
Formalization of the problem Q6 of 2001.

### [2021-08-10 18:08:28](https://github.com/leanprover-community/mathlib/commit/32735ca)
feat(measure_theory/measure_space): add mutually singular measures ([#8605](https://github.com/leanprover-community/mathlib/pull/8605))
This PR defines `mutually_singular` for measures. This is useful for Jordan and Lebesgue decomposition.

### [2021-08-10 18:08:27](https://github.com/leanprover-community/mathlib/commit/3b279c1)
feat(measure_theory/l2_space): generalize inner_indicator_const_Lp_one from R to is_R_or_C ([#8602](https://github.com/leanprover-community/mathlib/pull/8602))

### [2021-08-10 18:08:26](https://github.com/leanprover-community/mathlib/commit/d1b2a54)
feat(analysis/normed_space/inner_product): add norm_inner_le_norm ([#8601](https://github.com/leanprover-community/mathlib/pull/8601))
add this:
```
lemma norm_inner_le_norm (x y : E) : ∥⟪x, y⟫∥ ≤ ∥x∥ * ∥y∥ :=
(is_R_or_C.norm_eq_abs _).le.trans (abs_inner_le_norm x y)
```

### [2021-08-10 18:08:24](https://github.com/leanprover-community/mathlib/commit/acab4f9)
feat(algebra/pointwise): add preimage_smul and generalize a couple of assumptions ([#8600](https://github.com/leanprover-community/mathlib/pull/8600))
Some lemmas about smul spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-08-10 17:22:47](https://github.com/leanprover-community/mathlib/commit/9fb53f9)
chore(analysis/calculus/fderiv_symmetric): Squeeze some simps in a very slow proof ([#8609](https://github.com/leanprover-community/mathlib/pull/8609))
This doesn't seem to help much, but is low-hanging speedup fruit that the next person stuck on a timeout here will inevitably want solved first.

### [2021-08-10 17:22:46](https://github.com/leanprover-community/mathlib/commit/ebe0176)
feat(measure_theory/special_functions): add measurability of is_R_or_C.re and is_R_or_C.im ([#8603](https://github.com/leanprover-community/mathlib/pull/8603))

### [2021-08-10 16:39:18](https://github.com/leanprover-community/mathlib/commit/5739199)
chore(linear_algebra/quadratic_form): make Sylvester's law of inertia bold in the doc string ([#8610](https://github.com/leanprover-community/mathlib/pull/8610))

### [2021-08-10 14:03:54](https://github.com/leanprover-community/mathlib/commit/e2b7f70)
fix(docs/references.bib): add missing comma ([#8585](https://github.com/leanprover-community/mathlib/pull/8585))
* Adds a missing comma to docs/references.bib. Without this the file cannot be parsed by bibtool.
* Normalises docs/references.bib as described in [Citing other works](https://leanprover-community.github.io/contribute/doc.html#citing-other-works).

### [2021-08-10 13:22:22](https://github.com/leanprover-community/mathlib/commit/81a47a7)
docs(topology/category/Profinite/as_limit): fix typo ([#8606](https://github.com/leanprover-community/mathlib/pull/8606))

### [2021-08-10 10:54:11](https://github.com/leanprover-community/mathlib/commit/5890afb)
feat(data/list/perm): perm.permutations ([#8587](https://github.com/leanprover-community/mathlib/pull/8587))
This proves the theorem from [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/perm.20of.20permutations):
```lean
theorem perm.permutations {s t : list α} (h : s ~ t) : permutations s ~ permutations t := ...
```
It also introduces a `permutations'` function which has simpler equations (and indeed, this function is used to prove the theorem, because it is relatively easier to prove `perm.permutations'` first).

### [2021-08-10 10:54:10](https://github.com/leanprover-community/mathlib/commit/f967cd0)
refactor(group_theory/sylow): extract a lemma from Sylow proof ([#8459](https://github.com/leanprover-community/mathlib/pull/8459))

### [2021-08-10 09:12:41](https://github.com/leanprover-community/mathlib/commit/e8fc466)
feat(algebra/group/pi): Add `pi.const_(monoid|add_monoid|ring|alg)_hom` ([#8518](https://github.com/leanprover-community/mathlib/pull/8518))

### [2021-08-10 07:07:58](https://github.com/leanprover-community/mathlib/commit/e729ab4)
feat(analysis/specific_limits): limit of nat_floor (a * x) / x ([#8549](https://github.com/leanprover-community/mathlib/pull/8549))

### [2021-08-10 02:16:24](https://github.com/leanprover-community/mathlib/commit/e4cdecd)
chore(scripts): update nolints.txt ([#8599](https://github.com/leanprover-community/mathlib/pull/8599))
I am happy to remove some nolints for you!

### [2021-08-09 21:34:22](https://github.com/leanprover-community/mathlib/commit/2ab63a0)
feat(topology/algebra/infinite_sum, analysis/normed_space/basic): product of two tsums, cauchy product ([#8445](https://github.com/leanprover-community/mathlib/pull/8445))

### [2021-08-09 15:47:29](https://github.com/leanprover-community/mathlib/commit/5e59fb4)
feat(algebra/ordered_pointwise): lemmas on smul of intervals ([#8591](https://github.com/leanprover-community/mathlib/pull/8591))
Some lemmas about smul on different types of intervals, spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-08-09 15:47:27](https://github.com/leanprover-community/mathlib/commit/847fc12)
feat(algebra): `submodule.restrict_scalars p R` is `S`-isomorphic to `p` ([#8567](https://github.com/leanprover-community/mathlib/pull/8567))
To be more precise, turning `p : submodule S M` into an `R`-submodule gives the same module structure as turning it into a type and adding a module structure.

### [2021-08-09 15:47:26](https://github.com/leanprover-community/mathlib/commit/3ec899a)
chore(topology/algebra): bundled homs in group and ring completion ([#8497](https://github.com/leanprover-community/mathlib/pull/8497))
Also take the opportunity to remove is_Z_bilin (who was scheduled for
removal from the beginning).

### [2021-08-09 15:47:25](https://github.com/leanprover-community/mathlib/commit/189e90e)
feat(group_theory/subgroup): lemmas relating normalizer and map and comap ([#8458](https://github.com/leanprover-community/mathlib/pull/8458))

### [2021-08-09 15:47:24](https://github.com/leanprover-community/mathlib/commit/3dd8316)
feat(algebra/ring/basic): mul_{left,right}_cancel_of_non_zero_divisor ([#8425](https://github.com/leanprover-community/mathlib/pull/8425))
We also golf the proof that a domain is a cancel_monoid_with_zero.

### [2021-08-09 15:47:22](https://github.com/leanprover-community/mathlib/commit/4a15edd)
feat(data/polynomial/monic): monic.not_zero_divisor_iff ([#8417](https://github.com/leanprover-community/mathlib/pull/8417))
We prove that a monic polynomial is not a zero divisor. A helper lemma is proven that the product of a monic polynomial is of lesser degree iff it is nontrivial and the multiplicand is zero.

### [2021-08-09 15:47:21](https://github.com/leanprover-community/mathlib/commit/5e36848)
feat(measure_theory/decomposition/signed_hahn): signed version of the Hahn decomposition theorem ([#8388](https://github.com/leanprover-community/mathlib/pull/8388))
This PR defined positive and negative sets with respect to a vector measure and prove the signed version of the Hahn decomposition theorem.

### [2021-08-09 15:47:20](https://github.com/leanprover-community/mathlib/commit/f3b70e4)
feat(group_theory/subgroup): saturated subgroups ([#8137](https://github.com/leanprover-community/mathlib/pull/8137))
From LTE

### [2021-08-09 13:47:38](https://github.com/leanprover-community/mathlib/commit/77033a0)
chore(algebra/associated): rename div_or_div to dvd_or_dvd ([#8589](https://github.com/leanprover-community/mathlib/pull/8589))

### [2021-08-09 13:47:37](https://github.com/leanprover-community/mathlib/commit/65e2411)
feat(order/bounds): `is_lub`/`is_glb` in Pi types and product types ([#8583](https://github.com/leanprover-community/mathlib/pull/8583))
* Add `monotone_fst` and `monotone_snd`.
* Add some trivial lemmas about `upper_bounds` and `lower_bounds`.
* Turn `is_lub_pi` and `is_glb_pi` into `iff` lemmas.
* Add `is_lub_prod` and `is_glb_prod`.
* Fix some header levels in module docs of `order/bounds`.

### [2021-08-09 13:47:36](https://github.com/leanprover-community/mathlib/commit/9ce6b9a)
feat(order/complete_lattice): add `sup_eq_supr` and `inf_eq_infi` ([#8573](https://github.com/leanprover-community/mathlib/pull/8573))
* add `bool.injective_iff`, `bool.univ_eq`, and `bool.range_eq`;
* add `sup_eq_supr` and `inf_eq_infi`;
* golf `filter.comap_sup`.

### [2021-08-09 13:47:35](https://github.com/leanprover-community/mathlib/commit/45aed67)
chore(order/filter/basic): add `filter.sup_prod` and `filter.prod_sup` ([#8572](https://github.com/leanprover-community/mathlib/pull/8572))

### [2021-08-09 13:47:34](https://github.com/leanprover-community/mathlib/commit/fc694c5)
chore(linear_algebra/special_linear_group): Cleanup and golf ([#8569](https://github.com/leanprover-community/mathlib/pull/8569))
This cleans up a number things in this file:
* Many lemmas were duplicated between `↑A` and `⇑A`. This eliminates the latter spelling from all lemmas, and makes it simplify to the former. Unfortunately the elaborator fights us at every step of the way with `↑A`, so we introduce local notation to take the pain away.
* Some lemma names did not match the convention established elsewhere
* Some definitions can be bundled more heavily than they currently are. In particular, this merges together `to_lin'` and `to_linear_equiv`, as well as `to_GL` and `embedding_GL`.

### [2021-08-09 13:47:33](https://github.com/leanprover-community/mathlib/commit/8196d4a)
chore(algebra/group/units): Make coercion the simp-normal form of units ([#8568](https://github.com/leanprover-community/mathlib/pull/8568))
It's already used as the output for `@[simps]`; this makes `↑u` the simp-normal form of `u.val` and `↑(u⁻¹)` the simp-normal form of `u.inv`.

### [2021-08-09 13:47:32](https://github.com/leanprover-community/mathlib/commit/8edcf90)
feat(ring_theory/noetherian): add noeth ring lemma ([#8566](https://github.com/leanprover-community/mathlib/pull/8566))
I couldn't find this explicit statement in the library -- I feel like it's the way a mathematician would define a Noetherian ring though.

### [2021-08-09 13:47:31](https://github.com/leanprover-community/mathlib/commit/5f2d954)
feat(algebra/ordered_field): add `inv_le_of_inv_le` and `inv_lt_of_inv_lt` ([#8565](https://github.com/leanprover-community/mathlib/pull/8565))
These lemmas need positivity of only one of two variables. Mathlib already had lemmas about ordered multiplicative groups with these names, I appended prime to their names.

### [2021-08-09 13:47:29](https://github.com/leanprover-community/mathlib/commit/f29cc59)
feat(matrix/kronecker): Add the Kronecker product ([#8560](https://github.com/leanprover-community/mathlib/pull/8560))
Largely derived from [#8152](https://github.com/leanprover-community/mathlib/pull/8152), avoiding the complexity of introducing `algebra_map`s.
This introduces an abstraction `kronecker_map`, which is used to support both `mul` and `tmul` without having to redo any proofs.

### [2021-08-09 13:47:28](https://github.com/leanprover-community/mathlib/commit/7b1ce10)
fix(analysis/normed_space/basic): add an alias instance to fix an inference issue ([#8547](https://github.com/leanprover-community/mathlib/pull/8547))
This adds an instance from [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245176934).

### [2021-08-09 11:59:28](https://github.com/leanprover-community/mathlib/commit/fb63cf3)
chore(data/pfun): rename `roption` to `part`, split `data.part` off `data.pfun`  ([#8544](https://github.com/leanprover-community/mathlib/pull/8544))

### [2021-08-09 10:27:32](https://github.com/leanprover-community/mathlib/commit/6728201)
chore(data/finsupp): add missing lemmas ([#8553](https://github.com/leanprover-community/mathlib/pull/8553))
These lemmas are needed by `[simps {simp_rhs := tt}]` when composing equivs, otherwise simp doesn't make progress on `(map_range.add_equiv f).to_equiv.symm x` which should simplify to `map_range f.to_equiv.symm x`.

### [2021-08-09 08:17:21](https://github.com/leanprover-community/mathlib/commit/3f5a348)
chore(galois_connection): golf some proofs ([#8582](https://github.com/leanprover-community/mathlib/pull/8582))
* golf some proofs
* add `galois_insertion.left_inverse_l_u` and `galois_coinsertion.left_inverse_u_l`;
* drop `galois_insertion.l_supr_of_ul_eq_self` and `galois_coinsertion.u_infi_of_lu_eq_self`: these lemmas are less general than `galois_connection.l_supr` and `galois_connection.u_infi`.

### [2021-08-09 08:17:20](https://github.com/leanprover-community/mathlib/commit/24bbbdc)
feat(group_theory/sylow): Generalize proof of first Sylow theorem ([#8383](https://github.com/leanprover-community/mathlib/pull/8383))
Generalize the first proof. There is now a proof that every p-subgroup is contained in a Sylow subgroup.

### [2021-08-09 08:17:19](https://github.com/leanprover-community/mathlib/commit/4813b73)
feat(category_theory/adjunction): general adjoint functor theorem ([#4885](https://github.com/leanprover-community/mathlib/pull/4885))
A proof of the general adjoint functor theorem. This PR also adds an API for wide equalizers (essentially copied from the equalizer API), as well as results relating adjunctions to (co)structured arrow categories and weakly initial objects. I can split this into smaller PRs if necessary?

### [2021-08-09 06:49:46](https://github.com/leanprover-community/mathlib/commit/7bb4b27)
feat(group_theory/group_action): Cayley's theorem ([#8552](https://github.com/leanprover-community/mathlib/pull/8552))

### [2021-08-09 01:12:40](https://github.com/leanprover-community/mathlib/commit/9e320a2)
chore(measure_theory/special_functions): add measurability attributes ([#8570](https://github.com/leanprover-community/mathlib/pull/8570))
That attribute makes the `measurability` tactic aware of those lemmas.

### [2021-08-08 19:18:31](https://github.com/leanprover-community/mathlib/commit/ea77271)
chore(analysis/calculus/{f,}deriv): fix, add missing lemmas ([#8574](https://github.com/leanprover-community/mathlib/pull/8574))
* use `prod.fst` and `prod.snd` in lemmas like `has_fderiv_at_fst`;
* add `has_strict_deriv_at.prod`,
  `has_strict_fderiv_at.comp_has_strict_deriv_at`;
* use `set.maps_to` in some lemmas;
* golf some proofs.

### [2021-08-08 17:26:57](https://github.com/leanprover-community/mathlib/commit/3788cbf)
chore(algebra/*, data/polynomial/*): remove unnecessary imports ([#8578](https://github.com/leanprover-community/mathlib/pull/8578))
I cleaned up all of `data.polynomial`, and the files in `algebra` it imports.

### [2021-08-08 11:51:48](https://github.com/leanprover-community/mathlib/commit/87e9bec)
chore(linear_algebra/matrix/trace): relax `comm_ring` to `comm_semiring` in `matrix.trace_mul_comm` ([#8577](https://github.com/leanprover-community/mathlib/pull/8577))

### [2021-08-07 22:04:03](https://github.com/leanprover-community/mathlib/commit/0a79eec)
fix(order/bounds): remove double space ([#8575](https://github.com/leanprover-community/mathlib/pull/8575))

### [2021-08-07 20:32:48](https://github.com/leanprover-community/mathlib/commit/575fcc6)
refactor(data/nat/choose): reduce assumptions on lemmas ([#8508](https://github.com/leanprover-community/mathlib/pull/8508))
- rename `nat.choose_eq_factorial_div_factorial'` to `nat.cast_choose`
- change the cast from `ℚ` to any `char_zero` field
- get rid of the cast in `nat.choose_mul`. Generalization ensues.

### [2021-08-07 19:53:42](https://github.com/leanprover-community/mathlib/commit/d757996)
feat(analysis/complex): prove that complex functions are conformal if and only if the functions are holomorphic/antiholomorphic with nonvanishing differential ([#8424](https://github.com/leanprover-community/mathlib/pull/8424))
Complex functions are conformal if and only if the functions are holomorphic/antiholomorphic with nonvanishing differential.

### [2021-08-07 00:16:50](https://github.com/leanprover-community/mathlib/commit/b3c1de6)
feat(analysis/complex/basic): add several trivial lemmas for differentiable functions. ([#8418](https://github.com/leanprover-community/mathlib/pull/8418))
This file relates the differentiability of a function to the linearity of its `fderiv`.

### [2021-08-06 21:15:20](https://github.com/leanprover-community/mathlib/commit/2f29e09)
feat(group_action/defs): generalize faithful actions ([#8555](https://github.com/leanprover-community/mathlib/pull/8555))
This generalizes the `faithful_mul_semiring_action` typeclass to a mixin typeclass `has_faithful_scalar`, and provides instances for some simple actions:
* `has_faithful_scalar α α` (on cancellative monoids and monoids with zero)
* `has_faithful_scalar (opposite α) α`
* `has_faithful_scalar α (Π i, f i)`
* `has_faithful_scalar (units A) B`
* `has_faithful_scalar (equiv.perm α) α`
* `has_faithful_scalar M (α × β)`
* `has_faithful_scalar R (α →₀ M)`
* `has_faithful_scalar S (polynomial R)` (generalized from an existing instance)
* `has_faithful_scalar R (mv_polynomial σ S₁)`
* `has_faithful_scalar R (monoid_algebra k G)`
* `has_faithful_scalar R (add_monoid_algebra k G)`
As well as retaining the one other existing instance
* `faithful_mul_semiring_action ↥H E` where `H : subgroup (E ≃ₐ[F] E)`
The lemmas taking `faithful_mul_semiring_action` as a typeclass argument have been converted to use the new typeclass, but no attempt has been made to weaken their other hypotheses.

### [2021-08-06 17:42:38](https://github.com/leanprover-community/mathlib/commit/1b876c7)
chore(algebra/ordered_group): fix/add `order_dual` instances, add lemmas ([#8564](https://github.com/leanprover-community/mathlib/pull/8564))
* add `order_dual.has_inv`, `order_dual.group`, `order_dual.comm_group`;
* use new instances in `order_dual.ordered_comm_group` and
  `order_dual.linear_ordered_comm_group` (earlier we had only additive
  versions);
* add `le_of_forall_neg_add_le`, `le_of_forall_pos_sub_le`,
  `le_iff_forall_neg_add_le` and their multiplicative versions.

### [2021-08-06 15:53:55](https://github.com/leanprover-community/mathlib/commit/88f9480)
feat(logic/embedding): subtype_or_{embedding,equiv} ([#8489](https://github.com/leanprover-community/mathlib/pull/8489))
Provide explicit embedding from a subtype of a disjuction into a sum type.
If the disjunction is disjoint, upgrade to an equiv.
Additionally, provide `subtype.imp_embedding`, lowering a subtype
along an implication.

### [2021-08-06 10:42:04](https://github.com/leanprover-community/mathlib/commit/a23c47c)
feat(topology/instances/ennreal): ediam of intervals ([#8546](https://github.com/leanprover-community/mathlib/pull/8546))

### [2021-08-06 09:28:32](https://github.com/leanprover-community/mathlib/commit/da32780)
chore(data/polynomial/*): create file `data/polynomial/inductions` and move around lemmas ([#8563](https://github.com/leanprover-community/mathlib/pull/8563))
This PR is a precursor to [#8463](https://github.com/leanprover-community/mathlib/pull/8463): it performs the move, without introducing lemmas and squeezes some `simp`s to make some proofs faster.
I added add a doc-string to `lemma degree_pos_induction_on` with a reference to a lemma that will appear in [#8463](https://github.com/leanprover-community/mathlib/pull/8463).
The main reason why there are more added lines than removed ones is that the creation of a new file has a copyright statement, a module documentation and a few variable declarations.

### [2021-08-06 09:28:31](https://github.com/leanprover-community/mathlib/commit/b9e4c08)
refactor(algebra/regular): split out `is_regular` ([#8561](https://github.com/leanprover-community/mathlib/pull/8561))
One would like to import `is_regular` for rings. However, group powers
are too late in the algebra hierarchy,
so the proofs of powers of regular elements are factored
out to a separate file.

### [2021-08-06 09:28:30](https://github.com/leanprover-community/mathlib/commit/59c8bef)
feat (order/liminf_limsup): frequently_lt_of_lt_limsup ([#8548](https://github.com/leanprover-community/mathlib/pull/8548))

### [2021-08-06 09:28:29](https://github.com/leanprover-community/mathlib/commit/f471b89)
feat(topology,geometry/manifold): continuous and smooth partition of unity ([#8281](https://github.com/leanprover-community/mathlib/pull/8281))
Fixes [#6392](https://github.com/leanprover-community/mathlib/pull/6392)

### [2021-08-06 06:59:28](https://github.com/leanprover-community/mathlib/commit/dc6adcc)
feat(order/bounded_lattice): define the `distrib_lattice_bot` typeclass ([#8507](https://github.com/leanprover-community/mathlib/pull/8507))
Typeclass for a distributive lattice with a least element.
This typeclass is used to generalize `disjoint_sup_left` and similar.
It inserts itself in the hierarchy between `semilattice_sup_bot, semilattice_inf_bot` and `generalized_boolean_algebra`, `bounded_distrib_lattice`. I am doing it through `extends`.

### [2021-08-06 02:17:48](https://github.com/leanprover-community/mathlib/commit/e28d945)
chore(scripts): update nolints.txt ([#8562](https://github.com/leanprover-community/mathlib/pull/8562))
I am happy to remove some nolints for you!

### [2021-08-06 00:12:02](https://github.com/leanprover-community/mathlib/commit/c2a0532)
feat(logic/unique,data/fintype/basic): unique and fintype of subtype of one element ([#8491](https://github.com/leanprover-community/mathlib/pull/8491))
Additionally, a lemma proving that the cardinality of such a subtype is 1.

### [2021-08-05 20:49:21](https://github.com/leanprover-community/mathlib/commit/eb73c35)
docs(order/complete_boolean_algebra): add module docstring, add whitespaces ([#8525](https://github.com/leanprover-community/mathlib/pull/8525))

### [2021-08-05 19:03:04](https://github.com/leanprover-community/mathlib/commit/c2ed7dc)
feat(logic/basic): `ite p a b` is equal to `a` or `b` ([#8557](https://github.com/leanprover-community/mathlib/pull/8557))

### [2021-08-05 19:03:03](https://github.com/leanprover-community/mathlib/commit/52b6516)
refactor(order/disjointed): generalize `disjointed` to generalized boolean algebras ([#8409](https://github.com/leanprover-community/mathlib/pull/8409))
- Split `data.set.disjointed` into `data.set.pairwise` and `order.disjointed`. Change imports accordingly.
- In `order.disjointed`, change `set α` to `generalized_boolean_algebra α`. Redefine `disjointed` in terms of `partial_sups` to avoid needing completeness. Keep set notation variants of lemmas for easier unification.
- Rename some lemmas and reorder their arguments to make dot notation functional.
- Generalize some (where some = 2) `pairwise` lemmas.
- Delete lemmas which are unused and are a straightforward `rw` away from a simpler one (`Union_disjointed_of_mono`).

### [2021-08-05 16:28:09](https://github.com/leanprover-community/mathlib/commit/8e79ea5)
feat(data/matrix/basic): add `alg_(hom|equiv).map_matrix` ([#8527](https://github.com/leanprover-community/mathlib/pull/8527))
This also adds a few standalone lemmas about `algebra_map`.

### [2021-08-05 12:24:03](https://github.com/leanprover-community/mathlib/commit/a0cb45f)
feat(linear_algebra/clifford_algebra): the reals and complex numbers have isomorphic real clifford algebras ([#8165](https://github.com/leanprover-community/mathlib/pull/8165))

### [2021-08-04 21:40:15](https://github.com/leanprover-community/mathlib/commit/ee8e447)
chore(category_theory/whiskering): Fix docstring ([#8533](https://github.com/leanprover-community/mathlib/pull/8533))

### [2021-08-04 19:46:09](https://github.com/leanprover-community/mathlib/commit/d24faea)
chore(data/real/basic): drop some lemmas ([#8523](https://github.com/leanprover-community/mathlib/pull/8523))
Drop `real.Sup_le`, `real.lt_Sup`, `real.le_Sup`, `real.Sup_le_ub`, `real.le_Inf`, `real.Inf_lt`, `real.Inf_le`, `real.lb_le_Inf`. Use lemmas about `conditionally_complete_lattice`s instead.
Also drop unneeded assumptions in `real.lt_Inf_add_pos` and `real.add_neg_lt_Sup`.

### [2021-08-04 16:20:15](https://github.com/leanprover-community/mathlib/commit/4e9b18b)
chore(order/basic): rename monotone_of_monotone_nat and strict_mono.nat ([#8550](https://github.com/leanprover-community/mathlib/pull/8550))
For more coherence (and easier discoverability), rename `monotone_of_monotone_nat` to `monotone_nat_of_le_succ`, and `strict_mono.nat` to `strict_mono_nat_of_lt_succ`.

### [2021-08-04 08:58:37](https://github.com/leanprover-community/mathlib/commit/3a9b25d)
fix(order/lattice): make non-instances reducible ([#8541](https://github.com/leanprover-community/mathlib/pull/8541))
Some early fixes for the new linter in [#8540](https://github.com/leanprover-community/mathlib/pull/8540).

### [2021-08-04 08:58:36](https://github.com/leanprover-community/mathlib/commit/1691c6c)
feat(algebra/opposites): {add,mul,ring}_equiv.op ([#8535](https://github.com/leanprover-community/mathlib/pull/8535))
We had the equivalences of homs. Now we have equivalences of isos.

### [2021-08-04 08:58:35](https://github.com/leanprover-community/mathlib/commit/096bdb7)
refactor(group_theory/solvable): move subgroup commutators into new file ([#8534](https://github.com/leanprover-community/mathlib/pull/8534))
The theory of nilpotent subgroups also needs a theory of general commutators (if H,K : subgroup G then so is [H,K]), but I don't really want to import solvable groups to get nilpotent groups, so I am breaking the solvable group file into two, splitting off the API for these commutators.

### [2021-08-04 07:05:50](https://github.com/leanprover-community/mathlib/commit/292e3fa)
refactor(nat/basic): Move lemma about nat ([#8539](https://github.com/leanprover-community/mathlib/pull/8539))

### [2021-08-03 20:19:03](https://github.com/leanprover-community/mathlib/commit/8502571)
feat(topology/discrete_quotient): add two lemmas ([#8464](https://github.com/leanprover-community/mathlib/pull/8464))
Add lemmas `proj_bot_injective` and `proj_bot_bijective`, the former needed for the latter, and the latter needed in LTE.

### [2021-08-03 19:43:28](https://github.com/leanprover-community/mathlib/commit/d366672)
feat(measure_theory/integration): add some `with_density` lemmas ([#8517](https://github.com/leanprover-community/mathlib/pull/8517))

### [2021-08-03 17:55:51](https://github.com/leanprover-community/mathlib/commit/9d129dc)
feat(algebra/bounds): a few lemmas like `bdd_above (-s) ↔ bdd_below s` ([#8522](https://github.com/leanprover-community/mathlib/pull/8522))

### [2021-08-03 16:52:11](https://github.com/leanprover-community/mathlib/commit/c543ec9)
feat(topology/algebra/ordered/basic): sequences tending to Inf/Sup ([#8524](https://github.com/leanprover-community/mathlib/pull/8524))
We show that there exist monotone sequences tending to the Inf/Sup of a set in a conditionally complete linear order, as well as several related lemmas expressed in terms of `is_lub` and `is_glb`.

### [2021-08-03 15:41:09](https://github.com/leanprover-community/mathlib/commit/2b3cffd)
feat(algebra/floor): notation for nat_floor and nat_ceil ([#8526](https://github.com/leanprover-community/mathlib/pull/8526))
We introduce the notations ` ⌊a⌋₊` for `nat_floor a` and `⌈a⌉₊` for `nat_ceil a`, mimicking the existing notations for `floor` and `ceil` (with the `+` corresponding to the recent notation for `nnnorm`).

### [2021-08-03 11:13:43](https://github.com/leanprover-community/mathlib/commit/1700b3c)
chore(ring_theory/fractional_ideal): make `coe : ideal → fractional_ideal` a `coe_t` ([#8529](https://github.com/leanprover-community/mathlib/pull/8529))
This noticeably speeds up elaboration of `dedekind_domain.lean`, since it discourages the elaborator from going down a (nearly?)-looping path.
See also this Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Priority.20of.20.60coe_sort_trans.60

### [2021-08-03 11:13:41](https://github.com/leanprover-community/mathlib/commit/5afd09a)
chore(data/matrix/basic): move bundled versions of `matrix.map` beneath the algebra structure ([#8528](https://github.com/leanprover-community/mathlib/pull/8528))
This will give us an obvious place to add the bundled alg_hom version in a follow-up PR.
None of the moved lines have been modified.
Note that the git diff shows that instead of `matrix.map` moving down, the `algebra` structure has moved up.

### [2021-08-03 11:13:40](https://github.com/leanprover-community/mathlib/commit/3f4b836)
feat(order/bounds): add `is_lub_pi` and `is_glb_pi` ([#8521](https://github.com/leanprover-community/mathlib/pull/8521))

### [2021-08-03 11:13:39](https://github.com/leanprover-community/mathlib/commit/ad83714)
feat(fractional_ideal): `coe : ideal → fractional_ideal` as ring hom ([#8511](https://github.com/leanprover-community/mathlib/pull/8511))
This PR bundles the coercion from integral ideals to fractional ideals as a ring hom, and proves the missing `simp` lemmas that show the map indeed preserves the ring structure.

### [2021-08-03 09:27:49](https://github.com/leanprover-community/mathlib/commit/b681b6b)
chore(order/bounds): add `@[simp]` attrs, add `not_bdd_*_univ` ([#8520](https://github.com/leanprover-community/mathlib/pull/8520))

### [2021-08-03 07:45:29](https://github.com/leanprover-community/mathlib/commit/1021679)
feat(algebra/ordered_monoid): a few more `order_dual` instances ([#8519](https://github.com/leanprover-community/mathlib/pull/8519))
* add `covariant.flip` and `contravariant.flip`;
* add `[to_additive]` to `group.covariant_iff_contravariant` and
  `covconv` (renamed to `group.covconv`);
* use `group.covconv` in
  `group.covariant_class_le.to_contravariant_class_le`;
* add some `order_dual` instances for `covariant_class` and
  `contravariant_class`;
* golf `order_dual.ordered_comm_monoid`.

### [2021-08-02 23:06:35](https://github.com/leanprover-community/mathlib/commit/0bef4a0)
feat(algebra/group_with_zero): pullback a `comm_cancel_monoid_with_zero` instance across an injective hom ([#8515](https://github.com/leanprover-community/mathlib/pull/8515))
This generalizes `function.injective.cancel_monoid_with_zero` to the commutative case.
See also: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/A.20submonoid.20of.20a.20.60cancel_monoid_with_zero.60.20also.20cancels

### [2021-08-02 21:14:46](https://github.com/leanprover-community/mathlib/commit/2568d41)
feat(data/matrix/basic): Add bundled versions of matrix.diagonal ([#8510](https://github.com/leanprover-community/mathlib/pull/8510))
Also shows injectivity of `diagonal`.

### [2021-08-02 21:14:45](https://github.com/leanprover-community/mathlib/commit/77d6c8e)
feat(simps): better name for additivized simps-lemmas ([#8457](https://github.com/leanprover-community/mathlib/pull/8457))
* When using `@[to_additive foo, simps]`, the additivized simp-lemmas will have name `foo` + projection suffix (or prefix)
* Also add an option for `@[to_additive]` to accept the attribute with the correct given name. This is only useful when adding the `@[to_additive]` attribute via metaprogramming, so this option cannot be set by the `to_additive` argument parser.

### [2021-08-02 20:14:32](https://github.com/leanprover-community/mathlib/commit/17f1d28)
chore(data/matrix): delete each of the `matrix.foo_hom_map_zero` ([#8512](https://github.com/leanprover-community/mathlib/pull/8512))
These can already be found by `simp` since `matrix.map_zero` is a `simp` lemma, and we can manually use `foo_hom.map_matrix.map_zero` introduced by [#8468](https://github.com/leanprover-community/mathlib/pull/8468) instead. They also don't seem to be used anywhere in mathlib, given that deleting them with no replacement causes no build errors.

### [2021-08-02 17:05:53](https://github.com/leanprover-community/mathlib/commit/17b1e7c)
feat(data/equiv/mul_add): add `equiv.(div,sub)_(left,right)` ([#8385](https://github.com/leanprover-community/mathlib/pull/8385))

### [2021-08-02 14:22:13](https://github.com/leanprover-community/mathlib/commit/9a251f1)
refactor(data/matrix/basic): merge duplicate algebra structures ([#8486](https://github.com/leanprover-community/mathlib/pull/8486))
By putting the algebra instance in the same file as `scalar`, a future patch can probably remove `matrix.scalar` entirely (it's just another spelling of `algebra_map`).
Note that we actually had two instances of `algebra R (matrix n n R)` in different files, and the second one was strictly more general than the first. This removes the less general one.
Moving the imports around like this changes the number of simp lemmas available in downstream files, which can make `simp` slow enough to push a proof into a timeout.
A lot of files were expecting a transitive import of `algebra.algebra.basic` to import `data.fintype.card`, which it no longer does; hence the need to add this import explicitly.
There are no new lemmas or generalizations in this change; the old `matrix_algebra` has been deleted, and everything else has been moved with some variables renamed.

### [2021-08-02 12:31:20](https://github.com/leanprover-community/mathlib/commit/c8b7816)
feat(algebra/ordered_monoid): add_eq_bot_iff ([#8474](https://github.com/leanprover-community/mathlib/pull/8474))
bot addition is saturating on the bottom. On the way, typeclass arguments
were relaxed to just `[add_semigroup α]`, and helper simp lemmas
added for `bot`.
The iff lemma added (`add_eq_bot`) is not exactly according to the naming convention, but matches the top lemma and related ones in the naming style, so the style is kept consistent.
There is an API proof available, but the defeq proof (using the top equivalent) was used based on suggestions.

### [2021-08-02 12:31:19](https://github.com/leanprover-community/mathlib/commit/f354c1b)
feat(order/bounded_lattice): add some disjoint lemmas ([#8407](https://github.com/leanprover-community/mathlib/pull/8407))
This adds `disjoint.inf_left` and `disjoint.inf_right` (and primed variants) to match the existing `disjoint.sup_left` and `disjoint.sup_right`.
This also duplicates these lemmas to use set notation with `inter` instead of `inf`, matching the existing `disjoint.union_left` and `disjoint.union_right`.

### [2021-08-02 11:38:23](https://github.com/leanprover-community/mathlib/commit/af8e56a)
docs(overview): add holder continuity ([#8506](https://github.com/leanprover-community/mathlib/pull/8506))

### [2021-08-02 11:38:22](https://github.com/leanprover-community/mathlib/commit/25a4230)
chore(data/real/basic): cleanup ([#8501](https://github.com/leanprover-community/mathlib/pull/8501))
* use `is_lub` etc in the statement of `real.exists_sup`, rename it to `real.exists_is_lub`;
* move parts of the proof of `real.exists_is_lub` around;

### [2021-08-02 10:07:38](https://github.com/leanprover-community/mathlib/commit/69c6adb)
chore(data/int): move some lemmas from `basic` to a new file ([#8495](https://github.com/leanprover-community/mathlib/pull/8495))
Move `least_of_bdd`, `exists_least_of_bdd`, `coe_least_of_bdd_eq`,
`greatest_of_bdd`, `exists_greatest_of_bdd`, and
`coe_greatest_of_bdd_eq` from `data.int.basic` to `data.int.least_greatest`.

### [2021-08-02 10:07:37](https://github.com/leanprover-community/mathlib/commit/4a9cbdb)
feat(data/matrix/basic): provide equiv versions of `matrix.map`, `linear_map.map_matrix`, and `ring_hom.map_matrix`. ([#8468](https://github.com/leanprover-community/mathlib/pull/8468))
This moves all of these definitions to be adjacent, adds the standard family of functorial simp lemmas, and relaxes some typeclass requirements.
This also renames `matrix.one_map` to `matrix.map_one` to match `matrix.map_zero`.

### [2021-08-02 08:51:21](https://github.com/leanprover-community/mathlib/commit/1b771af)
feat(group_theory/coset): card_dvd_of_injective ([#8485](https://github.com/leanprover-community/mathlib/pull/8485))

### [2021-08-02 02:56:39](https://github.com/leanprover-community/mathlib/commit/0f168d3)
refactor(data/real/nnreal): use `ord_connected_subset_conditionally_complete_linear_order` ([#8502](https://github.com/leanprover-community/mathlib/pull/8502))

### [2021-08-02 02:56:38](https://github.com/leanprover-community/mathlib/commit/5994df1)
feat(algebra/group_power/lemmas): is_unit_pos_pow_iff ([#8420](https://github.com/leanprover-community/mathlib/pull/8420))

### [2021-08-02 02:15:39](https://github.com/leanprover-community/mathlib/commit/db0cd4d)
chore(scripts): update nolints.txt ([#8505](https://github.com/leanprover-community/mathlib/pull/8505))
I am happy to remove some nolints for you!

### [2021-08-01 22:56:38](https://github.com/leanprover-community/mathlib/commit/bfa6bbb)
doc(algebra/algebra/basic): add a comment to make the similar definition discoverable ([#8500](https://github.com/leanprover-community/mathlib/pull/8500))
I couldn't find this def, but was able to find lmul.

### [2021-08-01 21:03:45](https://github.com/leanprover-community/mathlib/commit/fdb0369)
feat(algebra/group/semiconj): add `semiconj_by.reflexive` and `semiconj_by.transitive` ([#8493](https://github.com/leanprover-community/mathlib/pull/8493))

### [2021-08-01 21:03:44](https://github.com/leanprover-community/mathlib/commit/60c378d)
feat(algebra/ordered_group): add `order_iso.inv` ([#8492](https://github.com/leanprover-community/mathlib/pull/8492))
* add `order_iso.inv` and `order_iso.neg`;
* use it to golf a few proofs;
* use `alias` to generate some `imp` lemmas from `iff` lemmas;
* generalize some lemmas about `order_iso` from `preorder` to `has_le`.

### [2021-08-01 21:03:43](https://github.com/leanprover-community/mathlib/commit/1530d76)
feat(group_theory/congruence): add `con.lift_on_units` etc ([#8488](https://github.com/leanprover-community/mathlib/pull/8488))
Add a helper function that makes it easier to define a function on
`units (con.quotient c)`.

### [2021-08-01 21:03:42](https://github.com/leanprover-community/mathlib/commit/9c4dd02)
feat(group_theory/order_of_element): order_of_dvd_iff_gpow_eq_one ([#8487](https://github.com/leanprover-community/mathlib/pull/8487))
Version of `order_of_dvd_iff_pow_eq_one` for integer powers

### [2021-08-01 21:03:41](https://github.com/leanprover-community/mathlib/commit/9194f20)
feat(data/nat/prime): pow_dvd_of_dvd_mul_right ([#8483](https://github.com/leanprover-community/mathlib/pull/8483))

### [2021-08-01 21:03:40](https://github.com/leanprover-community/mathlib/commit/b099103)
feat(group_theory/subgroup): add `subgroup.forall_gpowers` etc ([#8470](https://github.com/leanprover-community/mathlib/pull/8470))
* add `subgroup.forall_gpowers`, `subgroup.exists_gpowers`,
  `subgroup.forall_mem_gpowers`, and `subgroup.exists_mem_gpowers`;
* add their additive counterparts;
* drop some explicit lemmas about `add_subgroup.gmultiples`:
  `to_additive` can generate them now.

### [2021-08-01 21:03:39](https://github.com/leanprover-community/mathlib/commit/52a2e8b)
chore(algebra/group/hom_instances): add monoid_hom versions of linear_map lemmas ([#8461](https://github.com/leanprover-community/mathlib/pull/8461))
I mainly want the additive versions, but we may as well get the multiplicative ones too.
This also adds the missing `monoid_hom.map_div` and some other division versions of subtraction lemmas.

### [2021-08-01 21:03:36](https://github.com/leanprover-community/mathlib/commit/894fb0c)
feat(data/nat/totient): totient_prime_pow ([#8353](https://github.com/leanprover-community/mathlib/pull/8353))

### [2021-08-01 19:11:26](https://github.com/leanprover-community/mathlib/commit/7249afb)
feat(measure_theory/[integrable_on, set_integral]): integrals on two ae-eq sets are equal ([#8440](https://github.com/leanprover-community/mathlib/pull/8440))

### [2021-08-01 19:11:25](https://github.com/leanprover-community/mathlib/commit/d3c943b)
refactor(data/set/lattice): add congr lemmas for `Prop`-indexed `Union` and `Inter` ([#8260](https://github.com/leanprover-community/mathlib/pull/8260))
Thanks to new `@[congr]` lemmas `Union_congr_Prop` and `Inter_congr_Prop`, `simp` can simplify `p y` in `⋃ y (h : p y), f y`. As a result, LHS of many lemmas (e.g., `Union_image`) is no longer in `simp` normal form. E.g.,
```lean
lemma bUnion_range {f : ι → α} {g : α → set β} : (⋃x ∈ range f, g x) = (⋃y, g (f y)) :=
```
can no longer be a `@[simp]` lemma because `simp` simplifies `⋃x ∈ range f, g x` to `⋃ (x : α) (h : ∃ i, f i = x), g x`, then to `⋃ (x : α) (i : α) (h : f i = x), g x`. So, we add
```lean
@[simp] lemma Union_Union_eq' {f : ι → α} {g : α → set β} :
  (⋃ x y (h : f y = x), g x) = ⋃ y, g (f y) :=
```
Also, `Union` and `Inter` are semireducible, so one has to explicitly convert between these operations and `supr`/`infi`.

### [2021-08-01 17:17:28](https://github.com/leanprover-community/mathlib/commit/f961b28)
chore(deprecated/*): Make deprecated classes into structures ([#8178](https://github.com/leanprover-community/mathlib/pull/8178))
I make the deprecated classes `is_group_hom`, `is_subgroup`, ... into structures, and delete some deprecated constructions which become inconvenient or essentially unusable after these changes. I do not completely remove all deprecated imports in undeprecated files, however I push these imports much further towards the edges of the hierarchy. 
More detailed comments about what is going on here:
In the `src/deprecated/` directory, classes such as `is_ring_hom` and `is_subring` are defined (and the same for groups, fields, monoids...). These are predicate classes on functions and sets respectively, formerly used to handle ring morphisms and subrings before both were bundled. Amongst other things, this PR changes all the relevant definitions from classes to structures and then picks up the pieces (I will say more about what this means later). Before I started on this refactor, my opinion was that these classes should be turned into structures, but should be left in mathlib. After this refactor, I am now moving towards the opinion that it would be no great loss if these structures were removed completely -- I do not see any time when we really need them.
The situation I previously had in mind where the substructures could be useful is if one is (in the middle of a long tactic proof) defining an explicit subring of a ring by first defining it as a subset, or `add_subgroup` or whatever, and then doing some mathematics to prove that this subset is closed under multiplication, and hence proving that it was a subring after all. With the old approach this just involves some `S : set R` with more and more properties being proved of it and added to the type class search as the proof progresses. With the bundled set-up, we might have `S : set R` and then later on we get `S_subring : subring R` whose underlying subset equals S, and then all our hypotheses about `S` built up during the proof can no longer be used as rewrites, we need to keep rewriting or `change`ing `x \in S_subring` to `x \in S` and back again. This issue showed up only once in the refactor, in `src/ring_theory/integral_closure.lean`, around line 230, where I refactored a proof to avoid the deprecated structures and it seemed to get a bit longer. I can definitely live with this.
One could imagine a similar situation with morphisms (define f as a map between rings, and only later on prove that it's a ring homomorphism) but actually I did not see this situation arise at all. In fact the main issue I ran into with morphism classes was the following (which showed up 10 or so times): there are many constructions in mathlib which actually turn out to be, or (even worse) turn out under some extra assumptions to be, maps which preserve some structure. For example `multiset.map (f : X -> Y) : multiset X -> multiset Y` (which was in mathlib since it was born IIRC) turns out to be an add_group_hom, once the add_group structure is defined on multisets. So here I had a big choice to make: should I actually rename `multiset.map` to be `private multiset.map_aux` and then redefine `multiset.map` to be the `add_monoid_hom`? In retrospect I think that there's a case for this. In fact `data.multiset.basic` is the biggest source of these issues -- `map` and `sum` and `countp` and `count` are all `add_monoid_hom`s. I did not feel confident about ripping out these fundamental definitions so I made four new ones, `map_add_monoid_hom`, `sum_add_monoid_hom` etc. The disadvantage with this approach is that again rewrites get a bit more painful: some lemma which involves `map` may need to be rewritten so that it involves `map_add_monoid_hom` so that one can apply `add_monoid_hom.map_add`, and then perhaps rewritten back so that one can apply other rewrites. Random example: line 43 of `linear_algebra.lagrange`, where I have to rewrite `coe_eval_ring_hom` in both directions. Let me say that I am most definitely open to the idea of renaming `multiset.map_add_monoid_hom` to `multiset.map` and just nuking our current `multiset.map` or making it private or `map_aux` or whatever but we're already at 92 files changed so it might be best to get this over with and come up with a TODO list for future tidy-ups. Another example: should the fields of `complex` be `re'` and `im'`, and `complex.re` be redefined as the R-linear map? Right now in mathlib we only use the fact that it's an `add_group_hom`, and I define `re_add_group_hom` for this. Note however one can not always get away with this renaming trick, for example there are instances when a certain fundamental construction only preserves some structure under additional conditions -- for example `has_inv.inv` on groups is only a group homomorphism when the underlying group is abelian (and the same for `pow` and `gpow`). In the past this was dealt with by a typeclass `is_group_hom` on `inv` which fired in the presence of a `comm_group` but not otherwise; now this has to be dealt with by a second definition `inv_monoid_hom` whose underlying function is `inv`. You can't just get away with applying the proof of `inv (a * b) = inv a * inv b` when you need it, because sometimes you want to apply things like `monoid_hom.map_prod` which needs a `monoid_hom` as input, so won't work with `inv`: you need to rewrite one way, apply `monoid_hom.map_prod` and then rewrite back the other way now :-/ I would say that this was ultimately the main disadvantage of this approach, but it seems minor really and only shows up a few times, and if we go ahead with the renaming plan it will happen even fewer times.
I had initially played with the idea of just completely removing all deprecated imports in non-deprecated files, but there were times near the end when I just didn't feel like it (I just wanted it to be over, I was scared to mess around in `control` or `test`), so I removed most of them but added some deprecated imports higher up the tree (or lower down the tree, I never understand which way up this tree is, I mean nearer the leaves -- am I right in that computer scientists for some reason think the root of a tree is at the top?). It will not be too hard for an expert to remove those last few deprecated imports in src outside the `deprecated` directory in subsequent PR's, indeed I could do it myself but I might I might need some Zulip help. Note: it used to be the case that `subring` imported `deprecated.subring`; this is now the other way around, which is much more sensible (and matches with submonoid). Outside the deprecated directory, there are only a few deprecated imports: `control.fold` (which I don't really want to mess with),`group_theory.free_abelian_group` (there is a bunch of `seq` stuff which I am not sure is ever used but I just couldn't be bothered, it might be the sort of refactor which someone finds interesting or fun though), `ring_theory.free_comm_ring` (this file involves some definitional abuse which either needs to be redone "mathematically" or rewritten to work with bundled morphisms) and `topology.algebra.uniform_group` (which I think Patrick is refactoring?) and a test file.
If you look at the diffs you see that various things are deleted (lots of `is_add_monoid_hom foo` proofs), but many of these deletions come with corresponding additions (e.g. a new `foo_group_hom` definition if it was not there already, plus corresponding `simp` lemma, which is randomly either a `coe` or an `apply` depending on what mood I was in; this could all be done with `@[simps]` trickery apparently but I didn't read the thread carefully yet). Once nice achievement was that I refactored a bunch of basic ring and field theory to avoid the `is_` classes completely, which I think is a step in the right direction (people were occasionally being forced to use deprecated stuff when doing stuff like Galois theory because some fundamental things used to use them; this is no longer the case -- in particular I think Abel-Ruffini might now be deprecated-free, or very nearly so). 
`finset.sum_hom` and `finset.prod_hom` are gone. It is very funny to do a search for these files in mathlib current master as I write -- 98% of the time they're used, they're used backwards (with `.symm` or `\l` with a rewrite). The bundled versions (`monoid_hom.map_prod` etc) are written the other way around. I could have just left them and not bothered, but it seemed easier just to get rid of them if we're moving to bundled morphisms. One funny observation was that unary `-` seemed to be a special case: we
seem to prefer `-\sum i, f i` to `\sum i, -(f i)` . For almost every other function, we want it to go the other way.

### [2021-08-01 11:40:51](https://github.com/leanprover-community/mathlib/commit/9ed4380)
feat(measure_theory/vector_measure): define the pullback and restriction of a vector measure ([#8408](https://github.com/leanprover-community/mathlib/pull/8408))

### [2021-08-01 09:36:34](https://github.com/leanprover-community/mathlib/commit/5b9b455)
chore(order/complete_lattice): generalize `Sup_eq_supr'`, add lemmas ([#8484](https://github.com/leanprover-community/mathlib/pull/8484))
* `Sup_eq_supr'` only needs `[has_Sup α]`, add `Inf_eq_infi'`;
* add `supr_range'`, `infi_range'`, `Sup_image'`, `Inf_image'`
  lemmas that use supremum/infimum over subtypes and only require
  `[has_Sup]`/`[has_Inf]`.

### [2021-08-01 09:36:33](https://github.com/leanprover-community/mathlib/commit/de78d42)
feat(order/rel_iso): add `equiv.to_order_iso` ([#8482](https://github.com/leanprover-community/mathlib/pull/8482))
Sometimes it's easier to show `monotone e` and `monotone e.symm` than
`e x ≤ e y ↔ x ≤ y`.

### [2021-08-01 09:36:33](https://github.com/leanprover-community/mathlib/commit/4f2006e)
chore(order/iterate): slightly generalize 2 lemmas ([#8481](https://github.com/leanprover-community/mathlib/pull/8481))

### [2021-08-01 08:34:12](https://github.com/leanprover-community/mathlib/commit/2063a52)
feat(order/partial_sups): complete lattice lemmas ([#8480](https://github.com/leanprover-community/mathlib/pull/8480))

### [2021-08-01 03:28:41](https://github.com/leanprover-community/mathlib/commit/79bc732)
feat(order/galois_connection): formula for `upper_bounds (l '' s)` ([#8478](https://github.com/leanprover-community/mathlib/pull/8478))
* upgrade `galois_connection.upper_bounds_l_image_subset` and
  `galois_connection.lower_bounds_u_image` to equalities;
* prove `bdd_above (l '' s) ↔ bdd_above s` and
  `bdd_below (u '' s) ↔ bdd_below s`;
* move `galois_connection.dual` to the top and use it in some proofs;
* use `order_iso.to_galois_connection` to transfer some of these
  results to `order_iso`s;
* rename `rel_iso.to_galois_insertion` to `order_iso.to_galois_insertion`.