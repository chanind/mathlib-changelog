### [2022-03-31 23:56:26](https://github.com/leanprover-community/mathlib/commit/2b92d08)
feat(model_theory/elementary_maps): The Tarski-Vaught test ([#12919](https://github.com/leanprover-community/mathlib/pull/12919))
Proves the Tarski-Vaught test for elementary embeddings and substructures.

### [2022-03-31 17:21:48](https://github.com/leanprover-community/mathlib/commit/de50389)
split(order/chain): Split off `order.zorn` ([#13060](https://github.com/leanprover-community/mathlib/pull/13060))
Split `order.zorn` into two files, one about chains, the other one about Zorn's lemma.

### [2022-03-31 16:09:24](https://github.com/leanprover-community/mathlib/commit/13e08bf)
feat(model_theory/*): Constructors for low-arity languages and structures ([#12960](https://github.com/leanprover-community/mathlib/pull/12960))
Defines `first_order.language.mk₂` to make it easier to define a language with at-most-binary symbols.
Defines `first_order.language.Structure.mk₂` to make it easier to define a structure in a language defined with `first_order.language₂`.
Defines `first_order.language.functions.apply₁` and `first_order.language.functions.apply₂` to make it easier to construct terms using low-arity function symbols.
Defines `first_order.language.relations.formula₁` and `first_order.language.relations.formula₂` to make it easier to construct formulas using low-arity relation symbols.

### [2022-03-31 16:09:23](https://github.com/leanprover-community/mathlib/commit/f1ae620)
feat(model_theory/bundled, satisfiability): Bundled models ([#12945](https://github.com/leanprover-community/mathlib/pull/12945))
Defines `Theory.Model`, a type of nonempty bundled models of a particular theory.
Refactors satisfiability in terms of bundled models.

### [2022-03-31 15:26:34](https://github.com/leanprover-community/mathlib/commit/2861d4e)
feat(combinatorics/simple_graph/connectivity): walk constructor patterns with explicit vertices ([#13078](https://github.com/leanprover-community/mathlib/pull/13078))
This saves a couple underscores, letting you write `walk.cons' _ v _ h p` instead of `@walk.cons _ _ _ v _ h p` when you want that middle vertex in a pattern.

### [2022-03-31 14:15:57](https://github.com/leanprover-community/mathlib/commit/25ef4f0)
feat(topology/algebra/matrix): more continuity lemmas for matrices ([#13009](https://github.com/leanprover-community/mathlib/pull/13009))
This should cover all the definitions in `data/matrix/basic`, and also picks out a few notable definitions (`det`, `trace`, `adjugate`, `cramer`, `inv`) from other files.

### [2022-03-31 13:42:09](https://github.com/leanprover-community/mathlib/commit/0f6eec6)
feat(ring_theory/polynomial/pochhammer): generalize a proof from `comm_semiring` to `semiring` ([#13024](https://github.com/leanprover-community/mathlib/pull/13024))
This PR is similar to [#13018](https://github.com/leanprover-community/mathlib/pull/13018).  Lemma `pochhammer_succ_eval` was already proven with a commutativity assumption.  I generalized the proof to `semiring` by introducing a helper lemma.
I still feel that this is harder than I would like it to be: `pochhammer` "is" a polynomial in `ℕ[X]` and all these commutativity assumptions are satisfied, since `ℕ[X]` is commutative.

### [2022-03-31 13:00:33](https://github.com/leanprover-community/mathlib/commit/1b42223)
feat(analysis/locally_convex): the topology of weak duals is locally convex ([#12623](https://github.com/leanprover-community/mathlib/pull/12623))

### [2022-03-31 12:28:09](https://github.com/leanprover-community/mathlib/commit/6405a6a)
feat(analysis/locally_convex): closed balanced sets are a basis of the topology ([#12786](https://github.com/leanprover-community/mathlib/pull/12786))
We prove some topological properties of the balanced core.

### [2022-03-31 10:35:37](https://github.com/leanprover-community/mathlib/commit/7833dbe)
lint(algebra/*): fix some lint errors ([#13058](https://github.com/leanprover-community/mathlib/pull/13058))
* add some docstrings to additive versions;
* make `with_zero.ordered_add_comm_monoid` reducible.

### [2022-03-31 08:43:56](https://github.com/leanprover-community/mathlib/commit/ba9ead0)
feat(order/sup_indep): lemmas about `pairwise` and `set.pairwise` ([#12590](https://github.com/leanprover-community/mathlib/pull/12590))
The `disjoint` lemmas can now be stated in terms of these two `pairwise` definitions.
This wasn't previously possible as these definitions were not yet imported.
This also adds the `iff` versions of these lemmas, and a docstring tying them all together.

### [2022-03-31 06:51:20](https://github.com/leanprover-community/mathlib/commit/81c5d17)
chore(algebra/order/monoid_lemmas): remove exactly same lemmas ([#13068](https://github.com/leanprover-community/mathlib/pull/13068))

### [2022-03-31 06:51:19](https://github.com/leanprover-community/mathlib/commit/7a37490)
feat(ring_theory/polynomial/pochhammer): add a binomial like recursion for pochhammer ([#13018](https://github.com/leanprover-community/mathlib/pull/13018))
This PR proves the identity
`pochhammer R n + n * (pochhammer R (n - 1)).comp (X + 1) = (pochhammer R n).comp (X + 1)`
analogous to the additive recursion for binomial coefficients.
For the proof, first we prove the result for a `comm_semiring` as `pochhammer_add_pochhammer_aux`.  Next, we apply this identity in the general case.
If someone has any idea of how to make the maths statement: it suffices to show this identity for pochhammer symbols in the commutative case, I would be *very* happy to know!

### [2022-03-31 06:51:18](https://github.com/leanprover-community/mathlib/commit/290f440)
feat(order/category/Semilattice): The categories of semilattices ([#12890](https://github.com/leanprover-community/mathlib/pull/12890))
Define `SemilatticeSup` and `SemilatticeInf`, the categories of finitary supremum lattices and finitary infimum lattices.

### [2022-03-31 06:51:17](https://github.com/leanprover-community/mathlib/commit/760f1b2)
refactor(*): rename `topological_ring` to `topological_semiring` and introduce a new `topological_ring` extending `has_continuous_neg` ([#12864](https://github.com/leanprover-community/mathlib/pull/12864))
Following the discussion in this [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity/near/275553306), this renames `topological_ring` to `topological_semiring` throughout the library and weakens the typeclass assumptions from `semiring` to `non_unital_non_assoc_semiring`. Moreover, it introduces a new `topological_ring` class which takes a type class parameter of `non_unital_non_assoc_ring` and extends `topological_semiring` and `has_continuous_neg`.
In the case of *unital* (semi)rings (even non-associative), the type class `topological_semiring` is sufficient to capture the notion of `topological_ring` because negation is just multiplication by `-1`. Therefore, those working with unital (semi)rings can proceed with the small change of using `topological_semiring` instead of `topological_ring`.
The primary reason for the distinction is to weaken the type class assumptions to allow for non-unital rings, in which case `has_continuous_neg` must be explicitly assumed.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)

### [2022-03-31 06:19:33](https://github.com/leanprover-community/mathlib/commit/c2339ca)
feat(algebraic_topology): map_alternating_face_map_complex ([#13028](https://github.com/leanprover-community/mathlib/pull/13028))
In this PR, we obtain a compatibility `map_alternating_face_map_complex` of the construction of the alternating face map complex functor with respect to additive functors between preadditive categories.

### [2022-03-31 02:41:53](https://github.com/leanprover-community/mathlib/commit/8a21316)
feat(combinatorics/simple_graph/regularity/bound): Numerical bounds for Szemerédi's regularity lemma ([#12962](https://github.com/leanprover-community/mathlib/pull/12962))
Define the constants appearing in Szemerédi's regularity lemma and prove a bunch of numerical facts about them.

### [2022-03-31 02:10:17](https://github.com/leanprover-community/mathlib/commit/299984b)
feat(combinatorics/simple_graph/uniform): Graph uniformity and uniform partitions ([#12957](https://github.com/leanprover-community/mathlib/pull/12957))
Define uniformity of a pair of vertices in a graph and uniformity of a partition of vertices of a graph.

### [2022-03-31 00:12:51](https://github.com/leanprover-community/mathlib/commit/47b1d78)
feat(linear_algebra/matrix): any matrix power can be expressed as sums of powers `0 ≤ k < fintype.card n` ([#12983](https://github.com/leanprover-community/mathlib/pull/12983))
I'm not familiar enough with the polynomial API to know if we can neatly state a similar result for negative powers.

### [2022-03-30 17:30:25](https://github.com/leanprover-community/mathlib/commit/fc35cb3)
chore(data/finset/card): add `card_disj_union` ([#13061](https://github.com/leanprover-community/mathlib/pull/13061))

### [2022-03-30 16:05:51](https://github.com/leanprover-community/mathlib/commit/7f450cb)
feat(topology/sets/order): Clopen upper sets ([#12670](https://github.com/leanprover-community/mathlib/pull/12670))
Define `clopen_upper_set`, the type of clopen upper sets of an ordered topological space.

### [2022-03-30 13:52:41](https://github.com/leanprover-community/mathlib/commit/518e81a)
feat(topology): add lemmas about `frontier` ([#13054](https://github.com/leanprover-community/mathlib/pull/13054))

### [2022-03-30 13:52:39](https://github.com/leanprover-community/mathlib/commit/de62b06)
chore(data/set/pointwise): Golf using `set.image2` API ([#13051](https://github.com/leanprover-community/mathlib/pull/13051))
Add some more `set.image2` API and demonstrate use by golfing all relevant `data.set.pointwise` declarations.
Other additions

### [2022-03-30 13:52:38](https://github.com/leanprover-community/mathlib/commit/25e8730)
feat(analysis/special_functions/pow): abs value of real to complex power ([#13048](https://github.com/leanprover-community/mathlib/pull/13048))

### [2022-03-30 13:52:37](https://github.com/leanprover-community/mathlib/commit/33a323c)
feat(data/fin): lemmas about ordering and cons ([#13044](https://github.com/leanprover-community/mathlib/pull/13044))
This marks a few extra facts `simp`, since the analogous facts are `simp` for `nat`.

### [2022-03-30 13:52:33](https://github.com/leanprover-community/mathlib/commit/644a848)
fix(tactic/generalize_proofs): instantiate mvars ([#13025](https://github.com/leanprover-community/mathlib/pull/13025))
Reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/generalize_proofs.20failed/near/276965359).

### [2022-03-30 13:52:32](https://github.com/leanprover-community/mathlib/commit/af3911c)
feat(data/polynomial/erase_lead): add two erase_lead lemmas ([#12910](https://github.com/leanprover-community/mathlib/pull/12910))
The two lemmas show that removing the leading term from the sum of two polynomials of unequal `nat_degree` is the same as removing the leading term of the one of larger `nat_degree` and adding.
The second lemma could be proved with `by rw [add_comm, erase_lead_add_of_nat_degree_lt_left pq, add_comm]`, but I preferred copying the same strategy as the previous one, to avoid interdependencies.

### [2022-03-30 13:52:30](https://github.com/leanprover-community/mathlib/commit/e31f031)
feat(analysis/locally_convex): polar sets for dualities ([#12849](https://github.com/leanprover-community/mathlib/pull/12849))
Define the absolute polar for a duality and prove easy properties such as
* `linear_map.polar_eq_Inter`: The polar as an intersection.
* `linear_map.subset_bipolar`: The polar is a subset of the bipolar.
* `linear_map.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.
Moreover, the corresponding lemmas are removed in the normed space setting as they all follow directly from the general case.

### [2022-03-30 11:47:45](https://github.com/leanprover-community/mathlib/commit/f13ee54)
chore(*): sort out some to_additive and simp orderings ([#13038](https://github.com/leanprover-community/mathlib/pull/13038))
- To additive should always come after simp, unless the linter complains.
- Also make to_additive transfer the `protected` attribute for consistency.

### [2022-03-30 11:47:44](https://github.com/leanprover-community/mathlib/commit/37a8a0b)
feat(ring_theory/graded_algebra): define homogeneous localisation ([#12784](https://github.com/leanprover-community/mathlib/pull/12784))
This pr defines `homogeneous_localization`. For `x` in projective spectrum of `A`, homogeneous localisation at `x` is the subring of $$A_x$$ containing `a/b` where `a` and `b` have the same degree. This construction is mainly used in constructing structure sheaf of Proj of a graded ring

### [2022-03-30 09:48:05](https://github.com/leanprover-community/mathlib/commit/cdd1703)
feat(algebra/associates): add two instances and a lemma about the order on the monoid of associates of a monoid ([#12863](https://github.com/leanprover-community/mathlib/pull/12863))

### [2022-03-30 03:51:16](https://github.com/leanprover-community/mathlib/commit/cd51f0d)
fix(data/fintype/basic): generalize fintype instance for fintype.card_coe ([#13055](https://github.com/leanprover-community/mathlib/pull/13055))

### [2022-03-30 03:51:14](https://github.com/leanprover-community/mathlib/commit/f2fd6db)
chore(*): removing some `by { dunfold .., apply_instance }` proofs ([#13050](https://github.com/leanprover-community/mathlib/pull/13050))
Replaces the proofs `by { dunfold .., apply_instance }` by the exact term that is outputted by `show_term`.

### [2022-03-30 03:19:42](https://github.com/leanprover-community/mathlib/commit/ca3bb9e)
chore(scripts): update nolints.txt ([#13057](https://github.com/leanprover-community/mathlib/pull/13057))
I am happy to remove some nolints for you!

### [2022-03-30 02:20:22](https://github.com/leanprover-community/mathlib/commit/fc75855)
feat(measure_theory/*): refactor integral to allow non second-countable target space ([#12942](https://github.com/leanprover-community/mathlib/pull/12942))
Currently, the Bochner integral in mathlib only allows second-countable target spaces. This is an issue, since many constructions in spectral theory require integrals, and spaces of operators are typically not second-countable. The most general definition of the Bochner integral requires functions that may take values in non second-countable spaces, but which are still pointwise limits of a sequence of simple functions (so-called strongly measurable functions) -- equivalently, they are measurable and with second-countable range.
This PR refactors the Bochner integral, working with strongly measurable functions (or rather, almost everywhere strongly measurable functions, i.e., functions which coincide almost everywhere with a strongly measurable function). There are some prerequisistes (topological facts, and a good enough theory of almost everywhere strongly measurable functions) that have been PRed separately, but the remaining part of the change has to be done in one PR, as once one changes the basic definition of the integral one has to change all the files that depend on it.
Once the change is done, in many files the fix is just to remove `[measurable_space E] [borel_space E] [second_countable_topology E]` to make the linter happy, and see that everything still compiles. (Well, sometimes it is also much more painful, of course :-). For end users using `integrable`, nothing has to be changed, but if you need to prove integrability by hand, instead of checking `ae_measurable` you need to check `ae_strongly_measurable`. In second-countable spaces, the two of them are equivalent (and you can use `ae_strongly_measurable.ae_measurable` and `ae_measurable.ae_strongly_measurable` to go between the two of them).
The main changes are the following:
* change `ae_eq_fun` to base it on equivalence classes of ae strongly measurable functions
* fix everything that depends on this definition, including lp_space, set_to_L1, the Bochner integral and conditional expectation
* fix everything that depends on these, notably complex analysis (removing second-countability and measurability assumptions all over the place)
* A notion that involves a measurable function taking values in a normed space should probably better be rephrased in terms of strongly_measurable or ae_strongly_measurable. So, change a few definitions like `measurable_at_filter` (to `strongly_measurable_at_filter`) or `martingale`.

### [2022-03-30 02:20:21](https://github.com/leanprover-community/mathlib/commit/d28a163)
feat(linear_algebra/dual): define the algebraic dual pairing ([#12827](https://github.com/leanprover-community/mathlib/pull/12827))
We define the pairing of algebraic dual and show that it is nondegenerate.

### [2022-03-30 00:29:28](https://github.com/leanprover-community/mathlib/commit/c594e2b)
feat(algebra/ring/basic): neg_zero for distrib_neg ([#13049](https://github.com/leanprover-community/mathlib/pull/13049))

### [2022-03-30 00:29:27](https://github.com/leanprover-community/mathlib/commit/b446c49)
feat(set_theory/cardinal): bit lemmas for exponentiation ([#13010](https://github.com/leanprover-community/mathlib/pull/13010))

### [2022-03-30 00:29:26](https://github.com/leanprover-community/mathlib/commit/92b29c7)
fix(tactic/norm_num): make norm_num user command match norm_num better ([#12667](https://github.com/leanprover-community/mathlib/pull/12667))
Corrects some issues with the `#norm_num` user command that prevented it from fully normalizing expressions. Also, adds `expr.norm_num`.

### [2022-03-29 23:57:24](https://github.com/leanprover-community/mathlib/commit/523d177)
feat(combinatorics/simple_graph/regularity/energy): Energy of a partition ([#12958](https://github.com/leanprover-community/mathlib/pull/12958))
Define the energy of a partition.

### [2022-03-29 23:24:55](https://github.com/leanprover-community/mathlib/commit/50903f0)
feat(algebra/algebra/unitization): define unitization of a non-unital algebra ([#12601](https://github.com/leanprover-community/mathlib/pull/12601))
Given a non-unital `R`-algebra `A` (given via the type classes `[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct the minimal unital `R`-algebra containing `A` as an ideal. This object `unitization R A` is a type synonym for `R × A` on which we place a different multiplicative structure, namely, `(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity is `(1, 0)`.

### [2022-03-29 20:37:44](https://github.com/leanprover-community/mathlib/commit/119eb05)
chore(ring_theory/valuation/basic): fix valuation_apply ([#13045](https://github.com/leanprover-community/mathlib/pull/13045))
Follow-up to [#12914](https://github.com/leanprover-community/mathlib/pull/12914).

### [2022-03-29 20:37:43](https://github.com/leanprover-community/mathlib/commit/e4c6449)
feat(algebra/module): `sub_mem_iff_left` and `sub_mem_iff_right` ([#13043](https://github.com/leanprover-community/mathlib/pull/13043))
Since it's a bit of a hassle to rewrite `add_mem_iff_left` and `add_mem_iff_right` to subtraction, I made a new pair of lemmas.

### [2022-03-29 20:37:42](https://github.com/leanprover-community/mathlib/commit/9aec6df)
feat(algebra/algebra/tower): `span A s = span R s` if `R → A` is surjective ([#13042](https://github.com/leanprover-community/mathlib/pull/13042))

### [2022-03-29 18:32:04](https://github.com/leanprover-community/mathlib/commit/d3684bc)
feat(category_theory/abelian): constructor in terms of coimage-image comparison ([#12972](https://github.com/leanprover-community/mathlib/pull/12972))
The "stacks constructor" for an abelian category, following https://stacks.math.columbia.edu/tag/0109.
I also factored out the canonical morphism from the abelian coimage to the abelian image (which exists whether or not the category is abelian), and reformulated `abelian.coimage_iso_image` in terms of an `is_iso` instance for this morphism.

### [2022-03-29 17:44:57](https://github.com/leanprover-community/mathlib/commit/e92ecff)
feat(algebra/direct_sum/module): link `direct_sum.submodule_is_internal` to `is_compl` ([#12671](https://github.com/leanprover-community/mathlib/pull/12671))
This is then used to show the even and odd components of a clifford algebra are complementary.

### [2022-03-29 17:11:21](https://github.com/leanprover-community/mathlib/commit/90f0bee)
chore(analysis/normed_space/exponential): fix lemma names in docstrings ([#13032](https://github.com/leanprover-community/mathlib/pull/13032))

### [2022-03-29 14:38:00](https://github.com/leanprover-community/mathlib/commit/993d576)
chore(data/list/pairwise): add `pairwise_bind` ([#13030](https://github.com/leanprover-community/mathlib/pull/13030))

### [2022-03-29 14:37:59](https://github.com/leanprover-community/mathlib/commit/8999813)
chore(data/list): two lemmas about bind ([#13029](https://github.com/leanprover-community/mathlib/pull/13029))

### [2022-03-29 14:37:58](https://github.com/leanprover-community/mathlib/commit/cedf022)
feat(ring_theory/valuation/basic): add add_valuation.valuation ([#12914](https://github.com/leanprover-community/mathlib/pull/12914))

### [2022-03-29 13:10:46](https://github.com/leanprover-community/mathlib/commit/84b8b0d)
chore(topology/vector_bundle): fix timeout by optimizing proof ([#13026](https://github.com/leanprover-community/mathlib/pull/13026))
This PR speeds up a big and slow definition using `simp only` and `convert` → `refine`. This declaration seems to be on the edge of timing out and some other changes like [#11750](https://github.com/leanprover-community/mathlib/pull/11750) tripped it up.
Time saved if I run it with timeouts disabled:
 * master 14.8s → 6.3s
 * [#11750](https://github.com/leanprover-community/mathlib/pull/11750) 14.2s → 6.12s

### [2022-03-29 13:10:45](https://github.com/leanprover-community/mathlib/commit/d5fee32)
chore(algebra/field_power): slightly simplify proof of min_le_of_zpow_le_max ([#13023](https://github.com/leanprover-community/mathlib/pull/13023))

### [2022-03-29 13:10:44](https://github.com/leanprover-community/mathlib/commit/541c80d)
feat(group_theory/index): Golf proof of `relindex_eq_zero_of_le_left` ([#13014](https://github.com/leanprover-community/mathlib/pull/13014))
This PR uses `relindex_dvd_of_le_left` to golf the proof of `relindex_eq_zero_of_le_left`.

### [2022-03-29 13:10:43](https://github.com/leanprover-community/mathlib/commit/e109c8f)
feat(topology): basis for `𝓤 C(α, β)` and convergence of a series of `f : C(α, β)` ([#11229](https://github.com/leanprover-community/mathlib/pull/11229))
* add `filter.has_basis.compact_convergence_uniformity`;
* add a few facts about `compacts X`;
* add `summable_of_locally_summable_norm`.

### [2022-03-29 11:26:23](https://github.com/leanprover-community/mathlib/commit/66509e1)
feat(data/polynomial/div): `a - b ∣ p.eval a - p.eval b` ([#13021](https://github.com/leanprover-community/mathlib/pull/13021))

### [2022-03-29 11:26:22](https://github.com/leanprover-community/mathlib/commit/111d3a4)
chore(data/polynomial/eval): golf two proofs involving evals ([#13020](https://github.com/leanprover-community/mathlib/pull/13020))
I shortened two proofs involving `eval/eval₂/comp`.

### [2022-03-29 11:26:21](https://github.com/leanprover-community/mathlib/commit/b87c267)
feat(topology/algebra/group): add small topology lemma ([#12931](https://github.com/leanprover-community/mathlib/pull/12931))
Adds a small topology lemma by splitting `compact_open_separated_mul` into `compact_open_separated_mul_left/right`, which was useful in my proof of `Steinhaus theorem` (see [#12932](https://github.com/leanprover-community/mathlib/pull/12932)), as in a non-abelian group, the current version was not sufficient.

### [2022-03-29 09:36:12](https://github.com/leanprover-community/mathlib/commit/89c8112)
feat(topology/algebra/monoid): `finprod` is eventually equal to `finset.prod` ([#13013](https://github.com/leanprover-community/mathlib/pull/13013))
Motivated by https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Using.20partitions.20of.20unity

### [2022-03-29 09:36:11](https://github.com/leanprover-community/mathlib/commit/545c265)
feat(data/polynomial/derivative): if `p` is a polynomial, then `p.derivative.nat_degree ≤ p.nat_degree - 1` ([#12948](https://github.com/leanprover-community/mathlib/pull/12948))
I also golfed the proof that `p.derivative.nat_degree ≤ p.nat_degree`.

### [2022-03-29 09:36:10](https://github.com/leanprover-community/mathlib/commit/4bf4d9d)
feat(ring_theory/dedekind_domain/adic_valuation): add adic valuation on a Dedekind domain ([#12712](https://github.com/leanprover-community/mathlib/pull/12712))
Given a Dedekind domain R of Krull dimension 1 and a maximal ideal v of R, we define the
v-adic valuation on R and prove some of its properties, including the existence of uniformizers.

### [2022-03-29 09:36:08](https://github.com/leanprover-community/mathlib/commit/1ffd04c)
feat(analysis/locally_convex): add balanced hull and core ([#12537](https://github.com/leanprover-community/mathlib/pull/12537))

### [2022-03-29 07:35:13](https://github.com/leanprover-community/mathlib/commit/0f92307)
feat(data/list/chain): Simp lemma for `chain r a (l ++ b :: c :: m)` ([#12969](https://github.com/leanprover-community/mathlib/pull/12969))

### [2022-03-29 07:35:12](https://github.com/leanprover-community/mathlib/commit/1cdbc35)
feat(order/hom/bounded): an order_iso maps top to top and bot to bot ([#12862](https://github.com/leanprover-community/mathlib/pull/12862))

### [2022-03-29 07:35:11](https://github.com/leanprover-community/mathlib/commit/b535c2d)
feat(algebra/homology): three lemmas on homological complexes ([#12742](https://github.com/leanprover-community/mathlib/pull/12742))

### [2022-03-29 07:35:09](https://github.com/leanprover-community/mathlib/commit/1084cee)
feat(category_theory/bicategory/coherence): prove the coherence theorem for bicategories ([#12155](https://github.com/leanprover-community/mathlib/pull/12155))

### [2022-03-29 07:35:08](https://github.com/leanprover-community/mathlib/commit/7b8b8f1)
feat(set_theory/ordinal_arithmetic): Characterize principal multiplicative ordinals ([#11701](https://github.com/leanprover-community/mathlib/pull/11701))
Two lemmas were renamed in the process:
- `mul_lt_omega` → `principal_mul_omega`
- `opow_omega` → `principal_opow_omega`
Various others were moved to `principal.lean`.

### [2022-03-29 05:57:42](https://github.com/leanprover-community/mathlib/commit/ce3cece)
feat(measure_theory/constructions/borel_space): add `borelize` tactic ([#12844](https://github.com/leanprover-community/mathlib/pull/12844))

### [2022-03-29 05:57:41](https://github.com/leanprover-community/mathlib/commit/5fb7b7b)
feat(set_theory/{ordinal_arithmetic, game/nim}): Minimum excluded ordinal ([#12659](https://github.com/leanprover-community/mathlib/pull/12659))
We define `mex` and `bmex`, and use the former to golf the proof of Sprague-Grundy.

### [2022-03-29 04:19:18](https://github.com/leanprover-community/mathlib/commit/5fcad21)
feat(number_theory/frobenius_number): Frobenius numbers ([#9729](https://github.com/leanprover-community/mathlib/pull/9729))

### [2022-03-28 23:54:09](https://github.com/leanprover-community/mathlib/commit/7fea719)
feat(data/set/basic): Laws for n-ary image ([#13011](https://github.com/leanprover-community/mathlib/pull/13011))
Prove left/right commutativity, distributivity of `set.image2` in the style of `set.image2_assoc`. Also add `forall₃_imp` and `Exists₃.imp`.

### [2022-03-28 23:54:08](https://github.com/leanprover-community/mathlib/commit/9480029)
chore(data/{nat,int,rat}/cast): add bundled version of `cast_id` lemmas ([#13001](https://github.com/leanprover-community/mathlib/pull/13001))

### [2022-03-28 23:54:07](https://github.com/leanprover-community/mathlib/commit/8c9dee1)
feat(algebra/field_power): add min_le_of_zpow_le_max ([#12915](https://github.com/leanprover-community/mathlib/pull/12915))

### [2022-03-28 22:26:18](https://github.com/leanprover-community/mathlib/commit/223d9a1)
feat(group_theory/quotient_group): maps of quotients by powers of integers induced by group homomorphisms ([#12811](https://github.com/leanprover-community/mathlib/pull/12811))

### [2022-03-28 22:26:16](https://github.com/leanprover-community/mathlib/commit/1a2182c)
feat(group_theory/complement): Transversals as functions ([#12732](https://github.com/leanprover-community/mathlib/pull/12732))
This PR adds interpretations of transversals as functions mapping elements of `G` to the chosen coset representative.

### [2022-03-28 20:38:27](https://github.com/leanprover-community/mathlib/commit/40b142e)
chore(analysis/*): move matrix definitions into their own file and generalize ([#13007](https://github.com/leanprover-community/mathlib/pull/13007))
This makes it much easier to relax the typeclasses as needed.
`norm_matrix_le_iff` has been renamed to `matrix.norm_le_iff`, the rest of the lemmas have just had their typeclass arguments weakened. No proofs have changed.
The `matrix.normed_space` instance is now of the form `normed_space R (matrix n m α)` instead of `normed_space α (matrix n m α)`.

### [2022-03-28 20:38:26](https://github.com/leanprover-community/mathlib/commit/ea97ca6)
feat(group_theory/group_action): add `commute.smul_{left,right}[_iff]` lemmas ([#13003](https://github.com/leanprover-community/mathlib/pull/13003))
`(r • a) * b = b * (r • a)` follows trivially from `smul_mul_assoc` and `mul_smul_comm`

### [2022-03-28 20:38:25](https://github.com/leanprover-community/mathlib/commit/261a195)
feat(group_theory/group_action/opposite): Add `smul_eq_mul_unop` ([#12995](https://github.com/leanprover-community/mathlib/pull/12995))
This PR adds a simp-lemma `smul_eq_mul_unop`, similar to `op_smul_eq_mul` and `smul_eq_mul`.

### [2022-03-28 16:49:23](https://github.com/leanprover-community/mathlib/commit/6fe0c3b)
refactor(algebra/group/to_additive + files containing even/odd): move many lemmas involving even/odd to the same file ([#12882](https://github.com/leanprover-community/mathlib/pull/12882))
This is the first step in refactoring the definition of `even` to be the `to_additive` of `square`.
This PR simply gathers together many (though not all) lemmas that involve `even` or `odd` in their assumptions.  The choice of which lemmas to migrate to the file `algebra.parity` was dictated mostly by whether importing `algebra.parity` in the current home would create a cyclic import.
The only change that is not a simple shift from a file to another one is the addition in `to_additive` for support to change `square` in a multiplicative name to `even` in an additive name.
The change to the test file `test.ring` is due to the fact that the definition of `odd` was no longer imported by the file.

### [2022-03-28 16:49:22](https://github.com/leanprover-community/mathlib/commit/958f6b0)
refactor(measure_theory/group/fundamental_domain): allow `null_measurable_set`s ([#12005](https://github.com/leanprover-community/mathlib/pull/12005))

### [2022-03-28 15:03:16](https://github.com/leanprover-community/mathlib/commit/abaabc8)
chore(algebra/group_power/lemmas): turn `[zn]smul` lemmas into instances ([#13002](https://github.com/leanprover-community/mathlib/pull/13002))
This adds new instances such that:
* `mul_[zn]smul_assoc` is `←smul_mul_assoc`
* `mul_[zn]smul_left` is `←mul_smul_comm`
This also makes `noncomm_ring` slightly smarter, and able to handle scalar actions by `nat`.
Thanks to Christopher, this generalizes these instances to non-associative and non-unital rings.

### [2022-03-28 15:03:14](https://github.com/leanprover-community/mathlib/commit/0e1387b)
feat(category_theory): the category of small categories has all small limits ([#12979](https://github.com/leanprover-community/mathlib/pull/12979))

### [2022-03-28 15:03:13](https://github.com/leanprover-community/mathlib/commit/31e5ae2)
feat(data/list/cycle): Define the empty cycle ([#12967](https://github.com/leanprover-community/mathlib/pull/12967))
Also clean the file up somewhat, and add various `simp` lemmas.

### [2022-03-28 14:30:41](https://github.com/leanprover-community/mathlib/commit/0c6f0c2)
feat(ring_theory/dedekind_domain/ideal): add lemmas about sup of ideal with irreducible ([#12859](https://github.com/leanprover-community/mathlib/pull/12859))
These results were originally in [#9345](https://github.com/leanprover-community/mathlib/pull/9345).

### [2022-03-28 11:39:00](https://github.com/leanprover-community/mathlib/commit/4ee988d)
chore(algebra/homology/homotopy): cleanup ([#12998](https://github.com/leanprover-community/mathlib/pull/12998))
Correcting a name and some whitespace.

### [2022-03-28 11:38:59](https://github.com/leanprover-community/mathlib/commit/eba31b5)
feat(algebra/homology): some elementwise lemmas ([#12997](https://github.com/leanprover-community/mathlib/pull/12997))

### [2022-03-28 11:38:58](https://github.com/leanprover-community/mathlib/commit/dacf049)
feat(algebra/*): coe_to_equiv_symm simp lemmas ([#12996](https://github.com/leanprover-community/mathlib/pull/12996))

### [2022-03-28 11:38:57](https://github.com/leanprover-community/mathlib/commit/f0c15be)
feat(measure_theory/functions/strongly_measurable): almost everywhere strongly measurable functions ([#12985](https://github.com/leanprover-community/mathlib/pull/12985))
A function is almost everywhere strongly measurable if it is almost everywhere the pointwise limit of a sequence of simple functions. These are the functions that can be integrated in the most general version of the Bochner integral. As a prerequisite for the refactor of the Bochner integral, we define almost strongly measurable functions and build a comprehensive API for them, gathering in the file `strongly_measurable.lean` all facts that will be needed for the refactor. The API does not claim to be complete, but it is already pretty big.

### [2022-03-28 11:38:56](https://github.com/leanprover-community/mathlib/commit/fd2c6c4)
chore(data/polynomial/ring_division): remove nontrivial assumptions ([#12984](https://github.com/leanprover-community/mathlib/pull/12984))
Additionally, this removes:
* some `polynomial.monic` assumptions that can be handled by casing instead
* the explicit `R` argument from `is_field.to_field R hR`

### [2022-03-28 11:38:55](https://github.com/leanprover-community/mathlib/commit/c0421e7)
feat({ring_theory,group_theory}/localization): add some small lemmas for localisation API ([#12861](https://github.com/leanprover-community/mathlib/pull/12861))
Add the following:
* `sub_mk`: a/b - c/d = (ad - bc)/(bd)
* `mk_pow`: (a/b)^n = a^n/b^n
* `mk_int_cast`, `mk_nat_cast`: m = m/1 for integer/natural number m.

### [2022-03-28 11:38:54](https://github.com/leanprover-community/mathlib/commit/1ebb206)
feat(ring_theory/localization): lemmas about `Frac(R)`-spans ([#12425](https://github.com/leanprover-community/mathlib/pull/12425))
A couple of lemmas relating spans in the localization of `R` to spans in `R` itself.

### [2022-03-28 09:53:37](https://github.com/leanprover-community/mathlib/commit/e48f2e8)
doc(data/polynomial/field_division): fix broken docstring links ([#12981](https://github.com/leanprover-community/mathlib/pull/12981))

### [2022-03-28 09:53:36](https://github.com/leanprover-community/mathlib/commit/d31410a)
doc({linear_algebra,matrix}/charpoly): add crosslinks ([#12980](https://github.com/leanprover-community/mathlib/pull/12980))
This way someone coming from `undergrad.yaml` has an easy way to jump between the two statements.

### [2022-03-28 09:53:35](https://github.com/leanprover-community/mathlib/commit/597cbf1)
feat(topology/continuous_on): add `set.maps_to.closure_of_continuous_on` ([#12975](https://github.com/leanprover-community/mathlib/pull/12975))

### [2022-03-28 09:53:34](https://github.com/leanprover-community/mathlib/commit/ff72aa2)
feat(data/list/big_operators): add multiplicative versions ([#12966](https://github.com/leanprover-community/mathlib/pull/12966))
* add `list.length_pos_of_one_lt_prod`, generate
  `list.length_pos_of_sum_pos` using `to_additive`;
* add `list.length_pos_of_prod_lt_one` and its additive version.

### [2022-03-28 09:53:33](https://github.com/leanprover-community/mathlib/commit/443c239)
feat(data/polynomial/ring_division): `mem_root_set_iff` ([#12963](https://github.com/leanprover-community/mathlib/pull/12963))

### [2022-03-28 09:53:31](https://github.com/leanprover-community/mathlib/commit/162d83f)
chore(data/matrix/basic): square matrices over a non-unital ring form a non-unital ring ([#12913](https://github.com/leanprover-community/mathlib/pull/12913))

### [2022-03-28 09:53:30](https://github.com/leanprover-community/mathlib/commit/c030dd2)
feat(set_theory/cardinal): `cardinal.to_nat` is order-preserving on finite cardinals ([#12763](https://github.com/leanprover-community/mathlib/pull/12763))
This PR proves that `cardinal.to_nat` is order-preserving on finite cardinals.

### [2022-03-28 09:53:29](https://github.com/leanprover-community/mathlib/commit/2873b7a)
feat(set_theory/cofinality): Lemmas relating `cof` to `lsub` and `blsub` ([#12316](https://github.com/leanprover-community/mathlib/pull/12316))

### [2022-03-28 09:53:28](https://github.com/leanprover-community/mathlib/commit/b7d6b3a)
feat(topology/continuous/algebra) : giving `C(α, M)` a `has_continuous_mul` and a `has_continuous_smul` structure ([#11261](https://github.com/leanprover-community/mathlib/pull/11261))
Here, `α` is a locally compact space.

### [2022-03-28 08:03:19](https://github.com/leanprover-community/mathlib/commit/7711012)
feat(order/hom/*): equivalences mapping morphisms to their dual ([#12888](https://github.com/leanprover-community/mathlib/pull/12888))
Add missing `whatever_hom.dual` equivalences.

### [2022-03-28 06:13:19](https://github.com/leanprover-community/mathlib/commit/587af99)
chore(test/matrix): clean up an unused argument ([#12986](https://github.com/leanprover-community/mathlib/pull/12986))
these aren't caught by linters as examples don't generate declarations

### [2022-03-28 06:13:17](https://github.com/leanprover-community/mathlib/commit/562bbf5)
feat(measure_theory/measure): add some simp lemmas, golf ([#12974](https://github.com/leanprover-community/mathlib/pull/12974))
* add `top_add`, `add_top`, `sub_top`, `zero_sub`, `sub_self`;
* golf the proof of `restrict_sub_eq_restrict_sub_restrict`.

### [2022-03-28 06:13:16](https://github.com/leanprover-community/mathlib/commit/4b05a42)
feat(data/list/pairwise): `pairwise_of_forall_mem_list` ([#12968](https://github.com/leanprover-community/mathlib/pull/12968))
A relation holds pairwise on a list when it does on any two of its elements.

### [2022-03-28 06:13:15](https://github.com/leanprover-community/mathlib/commit/73a9c27)
chore(analysis/analytic/basic): golf ([#12965](https://github.com/leanprover-community/mathlib/pull/12965))
Golf a 1-line proof, drop an unneeded assumption.

### [2022-03-28 06:13:14](https://github.com/leanprover-community/mathlib/commit/33afea8)
feat(analysis/normed_space): generalize some lemmas ([#12959](https://github.com/leanprover-community/mathlib/pull/12959))
* add `metric.closed_ball_zero'`, a version of `metric.closed_ball_zero` for a pseudo metric space;
* merge `metric.closed_ball_inf_dist_compl_subset_closure'` with `metric.closed_ball_inf_dist_compl_subset_closure`, drop an unneeded assumption `s ≠ univ`;
* assume `r ≠ 0` instead of `0 < r` in `closure_ball`, `frontier_ball`, and `euclidean.closure_ball`.

### [2022-03-28 06:13:12](https://github.com/leanprover-community/mathlib/commit/c65d807)
feat(data/polynomial/erase_lead + data/polynomial/reverse): rename an old lemma, add a stronger one ([#12909](https://github.com/leanprover-community/mathlib/pull/12909))
Taking advantage of nat-subtraction in edge cases, a lemma that previously proved `x ≤ y` actually holds with `x ≤ y - 1`.
Thus, I renamed the old lemma to `original_name_aux` and `original_name` is now the name of the new lemma.  Since this lemma was used in a different file, I used the `_aux` name in the other file.
Note that the `_aux` lemma is currently an ingredient in the proof of the stronger lemma.  It may be possible to have a simple direct proof of the stronger one that avoids using the `_aux` lemma, but I have not given this any thought.

### [2022-03-28 06:13:11](https://github.com/leanprover-community/mathlib/commit/7a1e0f2)
feat(analysis/inner_product_space): an inner product space is strictly convex ([#12790](https://github.com/leanprover-community/mathlib/pull/12790))

### [2022-03-28 05:04:36](https://github.com/leanprover-community/mathlib/commit/1e72d86)
chore(data/polynomial/degree/lemmas + data/polynomial/ring_division): move lemmas, reduce assumptions, golf ([#12858](https://github.com/leanprover-community/mathlib/pull/12858))
This PR takes advantage of the reduced assumptions that are a consequence of [#12854](https://github.com/leanprover-community/mathlib/pull/12854).  Again, I moved two lemmas from their current location to a different file, where the typeclass assumptions make more sense,

### [2022-03-27 19:56:25](https://github.com/leanprover-community/mathlib/commit/e5cd2ea)
feat(analysis/von_neumann): concrete and abstract definitions of a von Neumann algebra ([#12329](https://github.com/leanprover-community/mathlib/pull/12329))

### [2022-03-27 15:52:15](https://github.com/leanprover-community/mathlib/commit/1494a9b)
feat(data/zmod/basic): add `int_coe_eq_int_coe_iff_dvd_sub` ([#12944](https://github.com/leanprover-community/mathlib/pull/12944))
This adds the following API lemma.
```
lemma int_coe_eq_int_coe_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : zmod c) = ↑b ↔ ↑c ∣ b-a
```
extending the already present version with b = 0. [(Zulip discussion)](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Missing.20zmod.20lemma.3F)

### [2022-03-27 10:05:55](https://github.com/leanprover-community/mathlib/commit/d620ad3)
feat(measure_theory/measure/measure_space): remove measurable_set assumption in ae_measurable.subtype_mk ([#12978](https://github.com/leanprover-community/mathlib/pull/12978))

### [2022-03-27 04:09:23](https://github.com/leanprover-community/mathlib/commit/2c6df07)
chore(model_theory/*): Split up big model theory files ([#12918](https://github.com/leanprover-community/mathlib/pull/12918))
Splits up `model_theory/basic` into `model_theory/basic`, `model_theory/language_maps`, and `model_theory/bundled`.
Splits up `model_theory/terms_and_formulas` into `model_theory/syntax`, `model_theory/semantics`, and `model_theory/satisfiability`.
Adds to the module docs of these files.

### [2022-03-27 03:34:03](https://github.com/leanprover-community/mathlib/commit/57a5fd7)
chore(scripts): update nolints.txt ([#12971](https://github.com/leanprover-community/mathlib/pull/12971))
I am happy to remove some nolints for you!

### [2022-03-27 00:27:34](https://github.com/leanprover-community/mathlib/commit/664247f)
chore(data/set/intervals/ord_connected): Golf proof ([#12923](https://github.com/leanprover-community/mathlib/pull/12923))

### [2022-03-27 00:27:33](https://github.com/leanprover-community/mathlib/commit/05ef694)
refactor(topology/instances/ennreal): make `ennreal` an instance of `has_continuous_inv` ([#12806](https://github.com/leanprover-community/mathlib/pull/12806))
Prior to the type class `has_continuous_inv`, `ennreal` had to have it's own hand-rolled `ennreal.continuous_inv` statement. This replaces it with a `has_continuous_inv` instance.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)

### [2022-03-26 23:54:12](https://github.com/leanprover-community/mathlib/commit/caf6f19)
refactor(category_theory/abelian): deduplicate definitions of (co)image ([#12902](https://github.com/leanprover-community/mathlib/pull/12902))
Previously we made two separate definitions of the abelian (co)image, as `kernel (cokernel.π f)` / `cokernel (kernel.ι f)`,
once for `non_preadditive_abelian C` and once for `abelian C`.
This duplication wasn't really necessary, and this PR unifies them.

### [2022-03-26 23:17:46](https://github.com/leanprover-community/mathlib/commit/f5a9d0a)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at ([#12707](https://github.com/leanprover-community/mathlib/pull/12707))
We add `cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at`.
From flt-regular

### [2022-03-26 21:16:08](https://github.com/leanprover-community/mathlib/commit/7b93889)
refactor(data/list/basic): Remove many redundant hypotheses ([#12950](https://github.com/leanprover-community/mathlib/pull/12950))
Many theorems about `last` required arguments proving that certain things were not equal to `nil`, when in fact this was always the case. These hypotheses have been removed and replaced with the corresponding proofs.

### [2022-03-26 21:16:07](https://github.com/leanprover-community/mathlib/commit/e63e332)
feat(algebra/ring/basic): all non-zero elements in a non-trivial ring with no non-zero zero divisors are regular ([#12947](https://github.com/leanprover-community/mathlib/pull/12947))
Besides what the PR description says, I also golfed two earlier proofs.

### [2022-03-26 21:16:06](https://github.com/leanprover-community/mathlib/commit/b30f25c)
fix(data/set/prod): fix the way `×ˢ` associates ([#12943](https://github.com/leanprover-community/mathlib/pull/12943))
Previously `s ×ˢ t ×ˢ u` was an element of `set ((α × β) × γ)` instead of `set (α × β × γ) = set (α × (β × γ))`.

### [2022-03-26 21:16:05](https://github.com/leanprover-community/mathlib/commit/cc8c90d)
chore(data/equiv): split and move to `logic/equiv` ([#12929](https://github.com/leanprover-community/mathlib/pull/12929))
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rearranging.20files.20in.20.60data.2F.60
This PR rearranges files in `data/equiv/` by 1) moving bundled isomorphisms to a relevant subfolder of `algebra/`; 2) moving `denumerable` and `encodable` to `logic/`; 3) moving the remainder of `data/equiv/` to `logic/equiv/`. The commits of this PR correspond to those steps.
In particular, the following files were moved:
 * `data/equiv/module.lean` → `algebra/module/equiv.lean`
 * `data/equiv/mul_add.lean` → `algebra/hom/equiv.lean`
 * `data/equiv/mul_add_aut.lean` → `algebra/hom/aut.lean`
 * `data/equiv/ring.lean` → `algebra/ring/equiv.lean`
 * `data/equiv/ring_aut.lean` → `algebra/ring/aut.lean`
 * `data/equiv/denumerable.lean` → `logic/denumerable.lean`
 * `data/equiv/encodable/*.lean` → `logic/encodable/basic.lean logic/encodable/lattice.lean logic/encodable/small.lean`
 * `data/equiv/*.lean` to: `logic/equiv/basic.lean logic/equiv/fin.lean logic/equiv/functor.lean logic/equiv/local_equiv.lean logic/equiv/option.lean logic/equiv/transfer_instance.lean logic/equiv/embedding.lean logic/equiv/fintype.lean logic/equiv/list.lean logic/equiv/nat.lean logic/equiv/set.lean`

### [2022-03-26 20:22:51](https://github.com/leanprover-community/mathlib/commit/434a938)
feat(analysis/convex/strict_convex_space): Strictly convex spaces ([#11794](https://github.com/leanprover-community/mathlib/pull/11794))
Define `strictly_convex_space`, a `Prop`-valued mixin to state that a normed space is strictly convex.

### [2022-03-26 19:19:53](https://github.com/leanprover-community/mathlib/commit/1f11f3f)
chore(order/filter/basic): rename using the zero subscript convention for groups with zero ([#12952](https://github.com/leanprover-community/mathlib/pull/12952))

### [2022-03-26 18:24:35](https://github.com/leanprover-community/mathlib/commit/a491055)
chore(measure_theory/integral/lebesgue): extend to ae_measurable ([#12953](https://github.com/leanprover-community/mathlib/pull/12953))

### [2022-03-26 14:15:19](https://github.com/leanprover-community/mathlib/commit/cb2797e)
feat(measure_theory/constructions/borel_space): drop a countability assumption ([#12954](https://github.com/leanprover-community/mathlib/pull/12954))

### [2022-03-26 12:20:15](https://github.com/leanprover-community/mathlib/commit/b7d9166)
chore(measure_theory/measure/lebesgue): delete leftovers ([#12951](https://github.com/leanprover-community/mathlib/pull/12951))

### [2022-03-26 12:20:14](https://github.com/leanprover-community/mathlib/commit/1111482)
feat(topology/bases): separable subsets of topological spaces ([#12936](https://github.com/leanprover-community/mathlib/pull/12936))

### [2022-03-26 12:20:13](https://github.com/leanprover-community/mathlib/commit/f68536e)
feat(topology/constructions): continuity of uncurried functions when the first factor is discrete ([#12935](https://github.com/leanprover-community/mathlib/pull/12935))

### [2022-03-26 12:20:12](https://github.com/leanprover-community/mathlib/commit/5e449c2)
feat(algebra/is_prime_pow): add `is_prime_pow_iff_factorization_single` ([#12167](https://github.com/leanprover-community/mathlib/pull/12167))
Adds lemma `is_prime_pow_iff_factorization_single : is_prime_pow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = finsupp.single p k`
Also adds `pow_of_factorization_single` to `data/nat/factorization`

### [2022-03-26 10:30:31](https://github.com/leanprover-community/mathlib/commit/023a783)
feat(logic/nontrivial): `exists_pair_lt` ([#12925](https://github.com/leanprover-community/mathlib/pull/12925))

### [2022-03-26 10:30:30](https://github.com/leanprover-community/mathlib/commit/c51f4f1)
feat(set_theory/cardinal_ordinal): `κ ^ n = κ` for infinite cardinals ([#12922](https://github.com/leanprover-community/mathlib/pull/12922))

### [2022-03-26 09:35:33](https://github.com/leanprover-community/mathlib/commit/9d26041)
feat(topology/instances/ennreal): add `ennreal.has_sum_to_real` ([#12926](https://github.com/leanprover-community/mathlib/pull/12926))

### [2022-03-26 03:28:38](https://github.com/leanprover-community/mathlib/commit/b83bd25)
feat(linear_algebra/sesquilinear_form): add nondegenerate ([#12683](https://github.com/leanprover-community/mathlib/pull/12683))
Defines nondegenerate sesquilinear forms as left and right separating sesquilinear forms.

### [2022-03-26 02:58:15](https://github.com/leanprover-community/mathlib/commit/17b621c)
chore(scripts): update nolints.txt ([#12946](https://github.com/leanprover-community/mathlib/pull/12946))
I am happy to remove some nolints for you!

### [2022-03-25 19:43:25](https://github.com/leanprover-community/mathlib/commit/b6d246a)
feat(topology/continuous_function/cocompact_maps): add the type of cocompact continuous maps ([#12938](https://github.com/leanprover-community/mathlib/pull/12938))
This adds the type of cocompact continuous maps, which are those functions `f : α → β` for which `tendsto f (cocompact α) (cocompact β)`. These maps are of interest primarily because of their connection with continuous functions vanishing at infinity ([#12907](https://github.com/leanprover-community/mathlib/pull/12907)). In particular, if `f : α → β` is a cocompact continuous map and `g : β →C₀ γ` is a continuous function which vanishes at infinity, then `g ∘ f : α →C₀ γ`.
These are also related to quasi-compact maps (continuous maps for which preimages of compact sets are compact) and proper maps (continuous maps which are universally closed), neither of which are currently defined in mathlib. In particular, quasi-compact maps are cocompact continuous maps, and when the codomain is Hausdorff the converse holds also. Under some additional assumptions, both of these are also equivalent to being a proper map.

### [2022-03-25 18:48:49](https://github.com/leanprover-community/mathlib/commit/221796a)
feat(topology/metric_space/metrizable): define and use a metrizable typeclass ([#12934](https://github.com/leanprover-community/mathlib/pull/12934))

### [2022-03-25 17:53:43](https://github.com/leanprover-community/mathlib/commit/5925650)
chore(nnreal): rename lemmas based on real.to_nnreal when they mention of_real ([#12937](https://github.com/leanprover-community/mathlib/pull/12937))
Many lemma using `real.to_nnreal` mention `of_real` in their names. This PR tries to make things more coherent.

### [2022-03-25 11:39:22](https://github.com/leanprover-community/mathlib/commit/2143571)
feat(topology/category/Born): The category of bornologies ([#12045](https://github.com/leanprover-community/mathlib/pull/12045))
Define `Born`, the category of bornological spaces with bounded maps.

### [2022-03-25 09:33:50](https://github.com/leanprover-community/mathlib/commit/172f317)
move(algebra/hom/*): Move group hom files together ([#12647](https://github.com/leanprover-community/mathlib/pull/12647))
Move
* `algebra.group.freiman` to `algebra.hom.freiman`
* `algebra.group.hom` to `algebra.hom.basic`
* `algebra.group.hom_instances` to `algebra.hom.instances`
* `algebra.group.units_hom` to `algebra.hom.units`
* `algebra.group_action_hom` to `algebra.hom.group_action`
* `algebra.iterate_hom` to `algebra.hom.iterate`
* `algebra.non_unital_alg_hom` to `algebra.hom.non_unital_alg`

### [2022-03-25 09:03:06](https://github.com/leanprover-community/mathlib/commit/351c32f)
docs(docs/undergrad): Update TODO list ([#12752](https://github.com/leanprover-community/mathlib/pull/12752))
Update `undergrad` with the latest additions to mathlib.

### [2022-03-25 02:56:04](https://github.com/leanprover-community/mathlib/commit/9ee02c6)
feat(data/pfun): Remove unneeded assumption from pfun.fix_induction ([#12920](https://github.com/leanprover-community/mathlib/pull/12920))
Removed a hypothesis from `pfun.fix_induction`. Note that it was two "layers" deep, so this is actually a strengthening. The original can be recovered by
```lean
/-- A recursion principle for `pfun.fix`. -/
@[elab_as_eliminator] def fix_induction_original
  {f : α →. β ⊕ α} {b : β} {C : α → Sort*} {a : α} (h : b ∈ f.fix a)
  (H : ∀ a', b ∈ f.fix a' →
    (∀ a'', /- this hypothesis was removed -/ b ∈ f.fix a'' → sum.inr a'' ∈ f a' → C a'') → C a') : C a :=
by { apply fix_induction h, intros, apply H; tauto, }
```
Note that `eval_induction` copies this syntax, so the same argument was removed there as well.
This allows for some simplifications of other parts of the code. Unfortunately, it was hard to figure out what was going on in the very dense parts of `tm_to_partrec.lean` and `partrec.lean`. I mostly just mechanically removed the hypotheses that were unnecessarily being supplied, and then checked if that caused some variable to be unused and removed that etc. But I cannot tell if this allows for greater simplifications.
I also extracted two lemmas `fix_fwd` and `fix_stop` that I thought would be useful on their own.

### [2022-03-25 00:37:21](https://github.com/leanprover-community/mathlib/commit/3dd8e4d)
feat(order/category/FinBoolAlg): The category of finite Boolean algebras ([#12906](https://github.com/leanprover-community/mathlib/pull/12906))
Define `FinBoolAlg`, the category of finite Boolean algebras.

### [2022-03-25 00:06:09](https://github.com/leanprover-community/mathlib/commit/7ec1a31)
fix(combinatorics/simple_graph/density): correct name in docstring ([#12921](https://github.com/leanprover-community/mathlib/pull/12921))

### [2022-03-24 22:53:04](https://github.com/leanprover-community/mathlib/commit/352ecfe)
feat(combinatorics/simple_graph/{connectivity,metric}): `connected` and `dist` ([#12574](https://github.com/leanprover-community/mathlib/pull/12574))

### [2022-03-24 17:30:47](https://github.com/leanprover-community/mathlib/commit/2891e1b)
feat(algebra/category/BoolRing): The category of Boolean rings ([#12905](https://github.com/leanprover-community/mathlib/pull/12905))
Define `BoolRing`, the category of Boolean rings.

### [2022-03-24 17:30:46](https://github.com/leanprover-community/mathlib/commit/f53b239)
feat(model_theory/fraisse): Construct Fraïssé limits ([#12138](https://github.com/leanprover-community/mathlib/pull/12138))
Constructs Fraïssé limits (nonuniquely)

### [2022-03-24 16:39:34](https://github.com/leanprover-community/mathlib/commit/6ac7c18)
feat(combinatorics/simple_graph/density): Edge density ([#12431](https://github.com/leanprover-community/mathlib/pull/12431))
Define the number and density of edges of a relation and of a simple graph between two finsets.

### [2022-03-24 14:49:21](https://github.com/leanprover-community/mathlib/commit/7302e11)
feat(algebra/module/torsion): define torsion submodules ([#12027](https://github.com/leanprover-community/mathlib/pull/12027))
This file defines the a-torsion and torsion submodules for a R-module M and gives some basic properties. (The ultimate goal I'm working on is to classify the finitely-generated modules over a PID).

### [2022-03-24 13:01:54](https://github.com/leanprover-community/mathlib/commit/c7745b3)
chore(order/zorn): Review ([#12175](https://github.com/leanprover-community/mathlib/pull/12175))
Lemma renames

### [2022-03-24 12:01:35](https://github.com/leanprover-community/mathlib/commit/7c48d65)
feat(topology/algebra/group): define `has_continuous_inv` and `has_continuous_neg` type classes ([#12748](https://github.com/leanprover-community/mathlib/pull/12748))
This creates the `has_continuous_inv` and `has_continuous_neg` type classes. The `has_continuous_neg` class will be helpful for generalizing `topological_ring` to the setting of `non_unital_non_assoc_semiring`s (see [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity)). In addition, `ennreal` can have a `has_continuous_inv` instance.

### [2022-03-24 10:12:39](https://github.com/leanprover-community/mathlib/commit/eabc619)
feat(ring_theory/polynomial): mv_polynomial over UFD is UFD ([#12866](https://github.com/leanprover-community/mathlib/pull/12866))

### [2022-03-24 10:12:38](https://github.com/leanprover-community/mathlib/commit/db76064)
feat(*): facts about degrees/multiplicites of derivatives ([#12856](https://github.com/leanprover-community/mathlib/pull/12856))
For `t` an `n`th repeated root of `p`, we prove that it is an `n-1`th repeated root of `p'` (and tidy the section around this). We also sharpen the theorem stating that `deg p' < deg p`.

### [2022-03-24 10:12:37](https://github.com/leanprover-community/mathlib/commit/355645e)
chore(data/polynomial/*): delete, rename and move lemmas ([#12852](https://github.com/leanprover-community/mathlib/pull/12852))
- Replace `eval_eq_finset_sum` and `eval_eq_finset_sum'` with `eval_eq_sum_range` and `eval_eq_sum_range'` which are consistent with `eval₂_eq_sum_range`, `eval₂_eq_sum_range'` `eval_eq_finset_sum`, `eval_eq_finset_sum'`. Notice that the type of `eval_eq_sum_range'` is different, but this lemma has not been used anywhere in mathlib.
- Move the lemma `C_eq_int_cast` from `data/polynomial/degree/definitions.lean` to `data/polynomial/basic.lean`. `C_eq_nat_cast` was already here.

### [2022-03-24 10:12:36](https://github.com/leanprover-community/mathlib/commit/c1fb0ed)
feat(algebra/associated): generalize nat.prime_mul_iff ([#12850](https://github.com/leanprover-community/mathlib/pull/12850))

### [2022-03-24 10:12:35](https://github.com/leanprover-community/mathlib/commit/a5a0d23)
feat(data/list/basic): nth_le+filter lemmas ([#12836](https://github.com/leanprover-community/mathlib/pull/12836))

### [2022-03-24 10:12:34](https://github.com/leanprover-community/mathlib/commit/892e611)
feat(model_theory/*): Facts about countability of first-order structures ([#12819](https://github.com/leanprover-community/mathlib/pull/12819))
Shows that in a countable language, a structure is countably generated if and only if it is countable.

### [2022-03-24 10:12:32](https://github.com/leanprover-community/mathlib/commit/e6c6f00)
feat(number_theory/arithmetic_function): The moebius function is multiplicative ([#12796](https://github.com/leanprover-community/mathlib/pull/12796))
A fundamental property of the moebius function is that it is
multiplicative, which allows many facts about Euler products to be
expressed

### [2022-03-24 10:12:31](https://github.com/leanprover-community/mathlib/commit/0faebd2)
chore(fintype/card_embedding): generalize instances ([#12775](https://github.com/leanprover-community/mathlib/pull/12775))

### [2022-03-24 10:12:30](https://github.com/leanprover-community/mathlib/commit/0427430)
feat(number_theory/function_field): add completion with respect to place at infinity ([#12715](https://github.com/leanprover-community/mathlib/pull/12715))

### [2022-03-24 09:09:50](https://github.com/leanprover-community/mathlib/commit/ca93096)
feat(topology/nhds_set): add `has_basis_nhds_set` ([#12908](https://github.com/leanprover-community/mathlib/pull/12908))
Also add `nhds_set_union`.

### [2022-03-24 07:09:35](https://github.com/leanprover-community/mathlib/commit/399ce38)
feat(measure_theory/integral): continuous functions with exponential decay are integrable ([#12539](https://github.com/leanprover-community/mathlib/pull/12539))

### [2022-03-24 05:18:39](https://github.com/leanprover-community/mathlib/commit/df34816)
feat(ring_theory/principal_ideal_domain): add some irreducible lemmas ([#12903](https://github.com/leanprover-community/mathlib/pull/12903))

### [2022-03-24 05:18:38](https://github.com/leanprover-community/mathlib/commit/a978115)
refactor(category_theory/abelian): trivial generalisations ([#12897](https://github.com/leanprover-community/mathlib/pull/12897))
Trivial generalisations of some facts in `category_theory/abelian/non_preadditive.lean`.
They are true more generally, and this refactor will make it easier to do some other clean-up I'd like to perform on abelian categories.

### [2022-03-24 05:18:37](https://github.com/leanprover-community/mathlib/commit/d4e27d0)
chore(topology/separation): move a lemma, golf ([#12896](https://github.com/leanprover-community/mathlib/pull/12896))
* move `t0_space_of_injective_of_continuous` up;
* add `embedding.t0_space`, use it for `subtype.t0_space`.

### [2022-03-24 05:18:35](https://github.com/leanprover-community/mathlib/commit/e968b6d)
feat(topology/continuous_function/bounded): add `bounded_continuous_function.tendsto_iff_tendsto_uniformly` ([#12894](https://github.com/leanprover-community/mathlib/pull/12894))
This establishes that convergence in the metric on bounded continuous functions is equivalent to uniform convergence of the respective functions.

### [2022-03-24 05:18:34](https://github.com/leanprover-community/mathlib/commit/a370cf0)
chore(data/set/intervals): golf, rename ([#12893](https://github.com/leanprover-community/mathlib/pull/12893))
* rename `set.mem_Ioo_or_eq_endpoints_of_mem_Icc` →
  `set.eq_endpoints_or_mem_Ioo_of_mem_Icc`;
* rename `set.mem_Ioo_or_eq_left_of_mem_Ico` →
  `set.eq_left_or_mem_Ioo_of_mem_Ico`;
* rename `set.mem_Ioo_or_eq_right_of_mem_Ioc` →
  `set.eq_right_or_mem_Ioo_of_mem_Ioc`;
* golf the proofs of these lemmas.
The new names better reflect the order of terms in `or`.

### [2022-03-24 05:18:33](https://github.com/leanprover-community/mathlib/commit/5ef365a)
feat(topology/separation): generalize tendsto_const_nhds_iff to t1_space ([#12883](https://github.com/leanprover-community/mathlib/pull/12883))
I noticed this when working on the sphere eversion project

### [2022-03-24 05:18:32](https://github.com/leanprover-community/mathlib/commit/6696bdd)
docs(data/set/pairwise): Explain preference for `s.pairwise_disjoint id` ([#12878](https://github.com/leanprover-community/mathlib/pull/12878))
... over `s.pairwise disjoint`.

### [2022-03-24 05:18:31](https://github.com/leanprover-community/mathlib/commit/30449be)
feat(data/complex/is_R_or_C): generalize `is_R_or_C.proper_space_span_singleton` to all finite dimensional submodules ([#12877](https://github.com/leanprover-community/mathlib/pull/12877))
Also goes on to show that finite supremums of finite_dimensional submodules are finite-dimensional.

### [2022-03-24 05:18:30](https://github.com/leanprover-community/mathlib/commit/debdd90)
feat(tactic/ext): support rintro patterns in `ext` ([#12875](https://github.com/leanprover-community/mathlib/pull/12875))
The change is actually quite simple, since `rintro_pat*` has approximately the same type as `rcases_pat*`.

### [2022-03-24 05:18:29](https://github.com/leanprover-community/mathlib/commit/8e50164)
chore(data/int/basic): remove some `eq.mpr`s from `int.induction_on'` ([#12873](https://github.com/leanprover-community/mathlib/pull/12873))

### [2022-03-24 05:18:27](https://github.com/leanprover-community/mathlib/commit/ae69578)
fix(ring_theory/algebraic): Make `is_transcendental_of_subsingleton` fully general ([#12870](https://github.com/leanprover-community/mathlib/pull/12870))
I mistyped a single letter.

### [2022-03-24 05:18:26](https://github.com/leanprover-community/mathlib/commit/706a824)
feat(data/{nat, real}/sqrt): Some simple facts about square roots ([#12851](https://github.com/leanprover-community/mathlib/pull/12851))
Prove that sqrt 1 = 1 in the natural numbers and an order relationship between real and natural square roots.

### [2022-03-24 05:18:25](https://github.com/leanprover-community/mathlib/commit/ec434b7)
feat(group_theory/order_of_element): finite orderness is closed under mul ([#12750](https://github.com/leanprover-community/mathlib/pull/12750))

### [2022-03-24 05:18:24](https://github.com/leanprover-community/mathlib/commit/c705d41)
feat(analysis/locally_convex): characterize the natural bornology in terms of seminorms ([#12721](https://github.com/leanprover-community/mathlib/pull/12721))
Add four lemmas:
* `is_vonN_bounded_basis_iff`: it suffices to check boundedness for a basis
* `seminorm_family.has_basis`: the basis sets form a basis of the topology
* `is_bounded_iff_finset_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for all finite suprema of seminorms
* `is_bounded_iff_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for each seminorm
Also make the set argument in `seminorm_family.basis_sets_iff` implicit.

### [2022-03-24 05:18:23](https://github.com/leanprover-community/mathlib/commit/cbd1e98)
chore(algebra/category/*): simp lemmas for of_hom ([#12638](https://github.com/leanprover-community/mathlib/pull/12638))

### [2022-03-24 04:46:31](https://github.com/leanprover-community/mathlib/commit/7967128)
feat(data/complex/basic): `#ℂ = 𝔠` ([#12871](https://github.com/leanprover-community/mathlib/pull/12871))

### [2022-03-23 23:02:08](https://github.com/leanprover-community/mathlib/commit/584ae9d)
chore(data/{lists,multiset}/*): More dot notation ([#12876](https://github.com/leanprover-community/mathlib/pull/12876))
Rename many `list` and `multiset` lemmas to make them eligible to dot notation. Also add a few aliases to `↔` lemmas for even more dot notation.
Renames

### [2022-03-23 21:13:19](https://github.com/leanprover-community/mathlib/commit/e620519)
feat(order/hom/*): more superclass instances for `order_iso_class` ([#12889](https://github.com/leanprover-community/mathlib/pull/12889))
 * Weaken hypotheses on `order_hom_class` and some subclasses
 * Add more instances deriving specific order hom classes from `order_iso_class`

### [2022-03-23 21:13:18](https://github.com/leanprover-community/mathlib/commit/3b8d217)
refactor(order/upper_lower): Use `⨆` rather than `Sup` ([#12644](https://github.com/leanprover-community/mathlib/pull/12644))
Turn `Sup (coe '' S)` into  `⋃ s ∈ S, ↑s` and other similar changes. This greatly simplifies the proofs.

### [2022-03-23 20:36:51](https://github.com/leanprover-community/mathlib/commit/cd94287)
feat(category_theory/abelian): right derived functor in abelian category with enough injectives ([#12810](https://github.com/leanprover-community/mathlib/pull/12810))
This pr shows that in an abelian category with enough injectives, if a functor preserves finite limits, then the zeroth right derived functor is naturally isomorphic to itself.  Dual to [#12403](https://github.com/leanprover-community/mathlib/pull/12403) ↔️

### [2022-03-23 20:36:49](https://github.com/leanprover-community/mathlib/commit/84a438e)
refactor(algebraic_geometry/*): rename structure sheaf to `Spec.structure_sheaf` ([#12785](https://github.com/leanprover-community/mathlib/pull/12785))
Following [this Zulip message](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rename.20.60structure_sheaf.60.20to.20.60Spec.2Estructure_sheaf.60/near/275649595), this pr renames `structure_sheaf` to `Spec.structure_sheaf`

### [2022-03-23 12:35:46](https://github.com/leanprover-community/mathlib/commit/16fb8e2)
chore(model_theory/terms_and_formulas): `realize_to_prenex` ([#12884](https://github.com/leanprover-community/mathlib/pull/12884))
Proves that `phi.to_prenex` has the same realization in a nonempty structure as the original formula `phi` directly, rather than using `semantically_equivalent`.

### [2022-03-23 12:35:45](https://github.com/leanprover-community/mathlib/commit/64472d7)
feat(ring_theory/polynomial/basic): the isomorphism between `R[a]/I[a]` and `(R/I[X])/(f mod I)` for `a` a root of polynomial `f` and `I` and ideal of `R` ([#12646](https://github.com/leanprover-community/mathlib/pull/12646))
This PR defines the isomorphism between the ring `R[a]/I[a]` and the ring `(R/I[X])/(f mod I)` for `a` a root of the polynomial `f` with coefficients in `R` and `I` an ideal of `R`. This is useful for proving the Dedekind-Kummer Theorem.

### [2022-03-23 10:41:04](https://github.com/leanprover-community/mathlib/commit/9126310)
chore(docs/references): Remove duplicate key ([#12901](https://github.com/leanprover-community/mathlib/pull/12901))
and clean up the rest while I'm at it.

### [2022-03-23 10:41:02](https://github.com/leanprover-community/mathlib/commit/2308b53)
feat(model_theory/terms_and_formulas): Make `Theory.model` a class ([#12867](https://github.com/leanprover-community/mathlib/pull/12867))
Makes `Theory.model` a class

### [2022-03-23 10:08:10](https://github.com/leanprover-community/mathlib/commit/92f2669)
feat(algebra/homology/quasi_iso): 2-out-of-3 property ([#12898](https://github.com/leanprover-community/mathlib/pull/12898))

### [2022-03-23 08:42:10](https://github.com/leanprover-community/mathlib/commit/11a365d)
feat(linear_algebra/matrix): add variants of the existing `det_units_conj` lemmas ([#12881](https://github.com/leanprover-community/mathlib/pull/12881))

### [2022-03-23 00:37:13](https://github.com/leanprover-community/mathlib/commit/c60bfca)
chore(data/nat/prime): golf nat.dvd_prime_pow ([#12886](https://github.com/leanprover-community/mathlib/pull/12886))

### [2022-03-22 22:13:57](https://github.com/leanprover-community/mathlib/commit/d711d2a)
feat(set_theory/ordinal): Small iff cardinality less than `cardinal.univ` ([#12887](https://github.com/leanprover-community/mathlib/pull/12887))
Characterizes when a type is small in terms of its cardinality

### [2022-03-22 20:22:10](https://github.com/leanprover-community/mathlib/commit/3838b85)
feat(model_theory/*): Language equivalences ([#12837](https://github.com/leanprover-community/mathlib/pull/12837))
Defines equivalences between first-order languages

### [2022-03-22 20:22:09](https://github.com/leanprover-community/mathlib/commit/f7905f0)
feat(order/concept): Concept lattices ([#12286](https://github.com/leanprover-community/mathlib/pull/12286))
Define `concept`, the type of concepts of a relation, and prove it forms a complete lattice.

### [2022-03-22 20:22:08](https://github.com/leanprover-community/mathlib/commit/b226b4b)
feat(*): `has_repr` instances for `option`-like types ([#11282](https://github.com/leanprover-community/mathlib/pull/11282))
This provides the `has_repr` instance for `with_bot α`, `with_top α`, `with_zero α`, `with_one α`, `alexandroff α`.

### [2022-03-22 19:50:36](https://github.com/leanprover-community/mathlib/commit/980185a)
feat(algebra/{group,module}/ulift): Missing `ulift` instances ([#12879](https://github.com/leanprover-community/mathlib/pull/12879))
Add a few missing algebraic instances for `ulift` and golf a few existing ones.

### [2022-03-22 14:24:51](https://github.com/leanprover-community/mathlib/commit/6a55ba8)
feat(algebra/subalgebra/basic): Missing scalar instances ([#12874](https://github.com/leanprover-community/mathlib/pull/12874))
Add missing scalar instances for `submonoid`, `subsemiring`, `subring`, `subalgebra`.

### [2022-03-22 14:24:49](https://github.com/leanprover-community/mathlib/commit/5215940)
feat(order/filter/basic): `filter` is a `coframe` ([#12872](https://github.com/leanprover-community/mathlib/pull/12872))
Provide the `coframe (filter α)` instance and remove now duplicated lemmas.

### [2022-03-22 14:24:48](https://github.com/leanprover-community/mathlib/commit/1f47016)
refactor(order/hom/complete_lattice): Fix the definition of `frame_hom` ([#12855](https://github.com/leanprover-community/mathlib/pull/12855))
I misread "preserves finite meet" as "preserves binary meet", meaning that currently a `frame_hom` does not have to preserve `⊤` (subtly, preserving arbitrary join does not imply that either). This fixes my mistake.

### [2022-03-22 12:35:31](https://github.com/leanprover-community/mathlib/commit/d586195)
feat(data/finset/pointwise): Missing operations ([#12865](https://github.com/leanprover-community/mathlib/pull/12865))
Define `-s`, `s⁻¹`, `s - t`, `s / t`, `s +ᵥ t`, `s • t`, `s -ᵥ t`, `a • s`, `a +ᵥ s` for `s`, `t` finsets, `a` scalar. Provide a bare API following what is already there for `s + t`, `s * t`.

### [2022-03-22 09:42:58](https://github.com/leanprover-community/mathlib/commit/28eb06f)
feat(analysis/calculus): define `diff_on_int_cont` ([#12688](https://github.com/leanprover-community/mathlib/pull/12688))

### [2022-03-22 09:42:57](https://github.com/leanprover-community/mathlib/commit/5826b2f)
feat(topology/order/hom/esakia): Esakia morphisms ([#12241](https://github.com/leanprover-community/mathlib/pull/12241))
Define pseudo-epimorphisms and Esakia morphisms following the hom refactor.

### [2022-03-22 08:35:26](https://github.com/leanprover-community/mathlib/commit/41d291c)
feat(algebra/big_operators/associated): generalize prod_primes_dvd ([#12740](https://github.com/leanprover-community/mathlib/pull/12740))

### [2022-03-22 08:03:55](https://github.com/leanprover-community/mathlib/commit/3ce4161)
refactor(measure_theory/integral): restrict interval integrals to real intervals ([#12754](https://github.com/leanprover-community/mathlib/pull/12754))
This way `∫ x in 0 .. 1, (1 : real)` means what it should, not `∫ x : nat in 0 .. 1, (1 : real)`.

### [2022-03-22 06:15:55](https://github.com/leanprover-community/mathlib/commit/b0f585c)
feat(combinatorics/simple_graph/inc_matrix): Incidence matrix ([#10867](https://github.com/leanprover-community/mathlib/pull/10867))
Define the incidence matrix of a simple graph and prove the basics, including some stuff about matrix multiplication.

### [2022-03-22 03:26:17](https://github.com/leanprover-community/mathlib/commit/01eb653)
chore(scripts): update nolints.txt ([#12868](https://github.com/leanprover-community/mathlib/pull/12868))
I am happy to remove some nolints for you!

### [2022-03-22 01:36:27](https://github.com/leanprover-community/mathlib/commit/e51377f)
feat(logic/basic): `ulift.down` is injective ([#12824](https://github.com/leanprover-community/mathlib/pull/12824))
We also make the arguments to `plift.down_inj` inferred.

### [2022-03-22 00:37:25](https://github.com/leanprover-community/mathlib/commit/d71e06c)
feat(topology/algebra/monoid): construct a unit from limits of units and their inverses ([#12760](https://github.com/leanprover-community/mathlib/pull/12760))

### [2022-03-21 20:08:03](https://github.com/leanprover-community/mathlib/commit/f9dc84e)
feat(topology/continuous_function/units): basic results about units in `C(α, β)` ([#12687](https://github.com/leanprover-community/mathlib/pull/12687))
This establishes a few facts about units in `C(α, β)` including the equivalence `C(α, βˣ) ≃ C(α, β)ˣ`. Moreover, when `β` is a complete normed field, we show that the spectrum of `f : C(α, β)` is precisely `set.range f`.

### [2022-03-21 19:25:50](https://github.com/leanprover-community/mathlib/commit/8001ea5)
feat(category_theory/abelian): right derived functor ([#12841](https://github.com/leanprover-community/mathlib/pull/12841))
This pr dualises derived.lean. Right derived functor and natural transformation between right derived functors and related lemmas are formalised. 
The docs string currently contains more than what is in this file, but everything else will come shortly after.

### [2022-03-21 18:05:19](https://github.com/leanprover-community/mathlib/commit/25ec622)
feat(data/polynomial/eval + data/polynomial/ring_division): move a lemma and remove assumptions ([#12854](https://github.com/leanprover-community/mathlib/pull/12854))
A lemma about composition of polynomials assumed `comm_ring` and `is_domain`.  The new version assumes `semiring`.
I golfed slightly the original proof: it may very well be that a shorter proof is available!
I also moved the lemma, since it seems better for this lemma to appear in the file where the definition of `comp` appears.

### [2022-03-21 18:05:18](https://github.com/leanprover-community/mathlib/commit/fd4a034)
refactor(analysis/locally_convex/with_seminorms): use abbreviations to allow for dot notation ([#12846](https://github.com/leanprover-community/mathlib/pull/12846))

### [2022-03-21 16:35:37](https://github.com/leanprover-community/mathlib/commit/a2e4802)
feat(model_theory/fraisse): Defines Fraïssé classes ([#12817](https://github.com/leanprover-community/mathlib/pull/12817))
Defines the age of a structure
(Mostly) characterizes the ages of countable structures
Defines Fraïssé classes

### [2022-03-21 16:35:35](https://github.com/leanprover-community/mathlib/commit/1b787d6)
feat(linear_algebra/span): generalize span_singleton_smul_eq ([#12736](https://github.com/leanprover-community/mathlib/pull/12736))

### [2022-03-21 16:35:34](https://github.com/leanprover-community/mathlib/commit/df299a1)
docs(order/filter/basic): fix docstring of generate ([#12734](https://github.com/leanprover-community/mathlib/pull/12734))

### [2022-03-21 16:35:33](https://github.com/leanprover-community/mathlib/commit/09750eb)
feat(measure_theory/function/uniform_integrable): add API for uniform integrability in the probability sense ([#12678](https://github.com/leanprover-community/mathlib/pull/12678))
Uniform integrability in probability theory is commonly defined as the uniform existence of a number for which the expectation of the random variables restricted on the set for which they are greater than said number is arbitrarily small. We have defined it 
in mathlib, on the other hand, as uniform integrability in the measure theory sense + existence of a uniform bound of the Lp norms. 
This PR proves the first definition implies the second while a later PR will deal with the reverse direction.

### [2022-03-21 16:35:32](https://github.com/leanprover-community/mathlib/commit/715f984)
feat(model_theory/terms_and_formulas): Prenex Normal Form ([#12558](https://github.com/leanprover-community/mathlib/pull/12558))
Defines `first_order.language.bounded_formula.to_prenex`, a function which takes a formula and outputs an equivalent formula in prenex normal form.
Proves inductive principles based on the fact that every formula is equivalent to one in prenex normal form.

### [2022-03-21 14:42:55](https://github.com/leanprover-community/mathlib/commit/091f27e)
chore(order/{complete_lattice,sup_indep}): move `complete_lattice.independent` ([#12588](https://github.com/leanprover-community/mathlib/pull/12588))
Putting this here means that in future we can talk about `pairwise_disjoint` at the same time, which was previously defined downstream of `complete_lattice.independent`.
This commit only moves existing declarations and adjusts module docstrings.
The new authorship comes from [#5971](https://github.com/leanprover-community/mathlib/pull/5971) and [#7199](https://github.com/leanprover-community/mathlib/pull/7199), which predate this file.

### [2022-03-21 12:46:46](https://github.com/leanprover-community/mathlib/commit/135c574)
feat(model_theory/definability): Definability lemmas ([#12262](https://github.com/leanprover-community/mathlib/pull/12262))
Proves several lemmas to work with definability over different parameter sets.
Shows that definability is closed under projection.

### [2022-03-21 11:08:42](https://github.com/leanprover-community/mathlib/commit/86055c5)
split(data/{finset,set}/pointwise): Split off `algebra.pointwise` ([#12831](https://github.com/leanprover-community/mathlib/pull/12831))
Split `algebra.pointwise` into
* `data.set.pointwise`: Pointwise operations on `set`
* `data.finset.pointwise`: Pointwise operations on `finset`
I'm crediting
* The same people for `data.set.pointwise`
* Floris for [#3541](https://github.com/leanprover-community/mathlib/pull/3541)

### [2022-03-21 09:13:23](https://github.com/leanprover-community/mathlib/commit/8161ba2)
feat(model_theory/ultraproducts): Ultraproducts and the Compactness Theorem ([#12531](https://github.com/leanprover-community/mathlib/pull/12531))
Defines `filter.product`, a dependent version of `filter.germ`.
Defines a structure on an ultraproduct (a `filter.product` with respect to an ultrafilter).
Proves Łoś's Theorem, characterizing when an ultraproduct realizes a formula.
Proves the Compactness theorem with ultraproducts.

### [2022-03-21 07:40:25](https://github.com/leanprover-community/mathlib/commit/8e9abe3)
feat(measure_theory/constructions/borel_space): generalize a lemma ([#12843](https://github.com/leanprover-community/mathlib/pull/12843))
Generalize `measurable_limit_of_tendsto_metric_ae` from
`at_top : filter ℕ` to any countably generated filter on a nonempty type.

### [2022-03-21 05:51:55](https://github.com/leanprover-community/mathlib/commit/d902c22)
chore(category/abelian/derived): shorten proof ([#12847](https://github.com/leanprover-community/mathlib/pull/12847))

### [2022-03-21 05:51:54](https://github.com/leanprover-community/mathlib/commit/395019e)
feat(algebra/homology/additive): dualise statement of chain complex to cochain complex ([#12840](https://github.com/leanprover-community/mathlib/pull/12840))

### [2022-03-21 05:51:53](https://github.com/leanprover-community/mathlib/commit/69d3d16)
feat(polynomial/derivative): tidy+new theorems ([#12833](https://github.com/leanprover-community/mathlib/pull/12833))
Adds `iterate_derivative_eq_zero` and strengthens other results.
New theorems: `iterate_derivative_eq_zero`, `nat_degree_derivative_le`
Deleted: `derivative_lhom` - it is one already.
Misc: Turn a docstring into a comment
Everything else only got moved around + golfed, in order to weaken assumptions.

### [2022-03-21 05:51:52](https://github.com/leanprover-community/mathlib/commit/06017e0)
feat(order/compare): add 4 dot notation lemmas ([#12832](https://github.com/leanprover-community/mathlib/pull/12832))

### [2022-03-21 05:51:51](https://github.com/leanprover-community/mathlib/commit/f5987b2)
chore(data/real/basic): tweak lemmas about `of_cauchy` ([#12829](https://github.com/leanprover-community/mathlib/pull/12829))
These lemmas are about `real.of_cauchy` not `real.cauchy`, as their name suggests.
This also flips the direction of some of the lemmas to be consistent with the zero and one lemmas.
Finally, this adds the lemmas about `real.cauchy` that are missing.

### [2022-03-21 05:51:50](https://github.com/leanprover-community/mathlib/commit/772c776)
feat(ring_theory/algebraic): Added basic lemmas + golf ([#12820](https://github.com/leanprover-community/mathlib/pull/12820))

### [2022-03-21 05:20:44](https://github.com/leanprover-community/mathlib/commit/60af3bd)
feat(data/rat/denumerable): Make `mk_rat` into a simp lemma ([#12821](https://github.com/leanprover-community/mathlib/pull/12821))

### [2022-03-20 20:14:43](https://github.com/leanprover-community/mathlib/commit/656f749)
feat(analysis/locally_convex): define von Neumann boundedness ([#12449](https://github.com/leanprover-community/mathlib/pull/12449))
Define the von Neumann boundedness and show elementary properties, including that it defines a bornology.

### [2022-03-20 15:25:50](https://github.com/leanprover-community/mathlib/commit/9502db1)
refactor(group_theory/group_action/basic): Golf definition of action on cosets ([#12823](https://github.com/leanprover-community/mathlib/pull/12823))
This PR golfs the definition of the left-multiplication action on left cosets.
I deleted `mul_left_cosets` since it's the same as `•` and has no API.

### [2022-03-20 12:26:39](https://github.com/leanprover-community/mathlib/commit/f2fa1cf)
feat(category_theory/abelian/*): add some missing lemmas ([#12839](https://github.com/leanprover-community/mathlib/pull/12839))

### [2022-03-20 00:39:53](https://github.com/leanprover-community/mathlib/commit/cdd0572)
chore(ring_theory/algebraic): fix typo + golf ([#12834](https://github.com/leanprover-community/mathlib/pull/12834))

### [2022-03-19 23:35:59](https://github.com/leanprover-community/mathlib/commit/6abfb1d)
feat(analysis/normed_space/spectrum): Prove the Gelfand-Mazur theorem ([#12787](https://github.com/leanprover-community/mathlib/pull/12787))
**Gelfand-Mazur theorem** For a complex Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse is given by selecting the (unique) element of `spectrum ℂ a`.
- [x] depends on: [#12132](https://github.com/leanprover-community/mathlib/pull/12132)

### [2022-03-19 21:04:04](https://github.com/leanprover-community/mathlib/commit/cd012fb)
chore(ring_theory/ideal): use `ideal.mul_mem_left` instead of `submodule.smul_mem` ([#12830](https://github.com/leanprover-community/mathlib/pull/12830))
In one place this saves one rewrite.

### [2022-03-19 19:33:01](https://github.com/leanprover-community/mathlib/commit/f120076)
feat(category_theory): (co)equalizers and (co)kernels when composing with monos/epis ([#12828](https://github.com/leanprover-community/mathlib/pull/12828))

### [2022-03-19 19:33:00](https://github.com/leanprover-community/mathlib/commit/49cd1cc)
refactor(analysis/seminorm): move topology induced by seminorms to its own file ([#12826](https://github.com/leanprover-community/mathlib/pull/12826))
Besides the copy and paste I removed the namespace `seminorm` from most parts (it is still there for the boundedness definitions and statements) and updated the module docstrings. No real code has changed.

### [2022-03-19 19:32:59](https://github.com/leanprover-community/mathlib/commit/2660d16)
feat(group_theory/group_action/basic): Right action of normalizer on left cosets ([#12822](https://github.com/leanprover-community/mathlib/pull/12822))
This PR adds the right action of the normalizer on left cosets.

### [2022-03-19 17:43:23](https://github.com/leanprover-community/mathlib/commit/48eacc6)
chore(*): update to lean 3.42.0c ([#12818](https://github.com/leanprover-community/mathlib/pull/12818))

### [2022-03-19 14:49:29](https://github.com/leanprover-community/mathlib/commit/42dcf35)
chore(algebra/char_p/exp_char): golf char_eq_exp_char_iff ([#12825](https://github.com/leanprover-community/mathlib/pull/12825))

### [2022-03-19 11:33:35](https://github.com/leanprover-community/mathlib/commit/3ba1c02)
feat(group_theory/subgroup/basic): Alternate version of `mem_normalizer_iff` ([#12814](https://github.com/leanprover-community/mathlib/pull/12814))
This PR adds an alternate version of `mem_normalizer_iff`, in terms of commuting rather than conjugation.

### [2022-03-19 11:33:34](https://github.com/leanprover-community/mathlib/commit/52b9b36)
feat(ring_theory/fractional_ideal): fractional ideal is one if and only if ideal is one ([#12813](https://github.com/leanprover-community/mathlib/pull/12813))

### [2022-03-19 11:33:33](https://github.com/leanprover-community/mathlib/commit/245b614)
chore(measure_theory/measure): move subtraction to a new file ([#12809](https://github.com/leanprover-community/mathlib/pull/12809))

### [2022-03-19 11:33:32](https://github.com/leanprover-community/mathlib/commit/dae6155)
chore(number_theory/primorial): golf a proof ([#12807](https://github.com/leanprover-community/mathlib/pull/12807))
Use a new lemma to golf a proof.

### [2022-03-19 11:33:31](https://github.com/leanprover-community/mathlib/commit/1d18309)
feat(linear_algebra/determinant): no need for `is_domain` ([#12805](https://github.com/leanprover-community/mathlib/pull/12805))
Nontriviality is all that was actually used, and in some cases the statement is already vacuous in the trivial case.

### [2022-03-19 11:33:30](https://github.com/leanprover-community/mathlib/commit/ef69547)
feat(group_theory/finiteness): Define the minimum number of generators ([#12765](https://github.com/leanprover-community/mathlib/pull/12765))
The PR adds a definition of the minimum number of generators, which will be needed for a statement of Schreier's lemma.

### [2022-03-19 09:56:20](https://github.com/leanprover-community/mathlib/commit/ee4472b)
feat(group_theory/group_action/embedding): group actions apply on the codomain of embeddings ([#12798](https://github.com/leanprover-community/mathlib/pull/12798))

### [2022-03-19 09:56:19](https://github.com/leanprover-community/mathlib/commit/c9fc9bf)
refactor(order/filter/pointwise): Cleanup ([#12789](https://github.com/leanprover-community/mathlib/pull/12789))
* Reduce typeclass assumptions from `monoid` to `has_mul`
* Turn lemmas into instances
* Use hom classes rather than concrete hom types
* Golf

### [2022-03-19 09:56:18](https://github.com/leanprover-community/mathlib/commit/2b6b9ff)
feat(category_theory/abelian/derived): add left_derived_zero_iso_self ([#12403](https://github.com/leanprover-community/mathlib/pull/12403))
We add `left_derived_zero_iso_self`: the natural isomorphism `(F.left_derived 0) ≅ F` if `preserves_finite_colimits F`.
From lean-liquid

### [2022-03-19 08:22:18](https://github.com/leanprover-community/mathlib/commit/4c60258)
chore(ring_theory/dedekind_domain/ideal): golf ([#12737](https://github.com/leanprover-community/mathlib/pull/12737))

### [2022-03-19 03:04:31](https://github.com/leanprover-community/mathlib/commit/128c096)
chore(scripts): update nolints.txt ([#12816](https://github.com/leanprover-community/mathlib/pull/12816))
I am happy to remove some nolints for you!

### [2022-03-19 01:22:50](https://github.com/leanprover-community/mathlib/commit/7764c60)
feat(*/sort): sorting empty sets/singletons ([#12801](https://github.com/leanprover-community/mathlib/pull/12801))

### [2022-03-18 21:54:51](https://github.com/leanprover-community/mathlib/commit/d04fff9)
feat(topology/{order,separation}): several lemmas from an old branch ([#12794](https://github.com/leanprover-community/mathlib/pull/12794))
* add `mem_nhds_discrete`;
* replace the proof of `is_open_implies_is_open_iff` by `iff.rfl`;
* add lemmas about `separated`.

### [2022-03-18 20:21:42](https://github.com/leanprover-community/mathlib/commit/7f1ba1a)
feat(algebra/char_p/two): add `simp` attribute to some lemmas involving characteristic two identities ([#12800](https://github.com/leanprover-community/mathlib/pull/12800))
I hope that these `simp` attributes will make working with `char_p R 2` smooth!
I felt clumsy with this section, so hopefully this is an improvement.

### [2022-03-18 20:21:41](https://github.com/leanprover-community/mathlib/commit/e282089)
feat(linear_algebra/sesquilinear_form): preliminary results for nondegeneracy ([#12269](https://github.com/leanprover-community/mathlib/pull/12269))
Several lemmas needed to define nondegenerate bilinear forms and show that the canonical pairing of the algebraic dual is nondegenerate.
Add domain restriction of bilinear maps in the second component and in both compenents.
Some type-class generalizations for symmetric, alternating, and reflexive sesquilinear forms.

### [2022-03-18 20:21:40](https://github.com/leanprover-community/mathlib/commit/076490a)
feat(group_theory/nilpotent): the is_nilpotent_of_finite_tfae theorem ([#11835](https://github.com/leanprover-community/mathlib/pull/11835))

### [2022-03-18 20:21:38](https://github.com/leanprover-community/mathlib/commit/8c89ae6)
feat(ring_theory/unique_factorization_domain): some lemmas relating shapes of factorisations ([#9345](https://github.com/leanprover-community/mathlib/pull/9345))
Given elements `a`, `b` in a `unique_factorization_monoid`, if there is an order-preserving bijection between the sets of factors of `associates.mk a` and `associates.mk b` then the prime factorisations of `a` and `b` have the same shape.

### [2022-03-18 18:32:32](https://github.com/leanprover-community/mathlib/commit/0c52d3b)
doc(src/tactic/doc_commands): typo “between” → “better” ([#12804](https://github.com/leanprover-community/mathlib/pull/12804))

### [2022-03-18 18:32:31](https://github.com/leanprover-community/mathlib/commit/d3703fe)
doc(archive/100-theorems-list/9_area_of_a_circle): fix `×` ([#12803](https://github.com/leanprover-community/mathlib/pull/12803))
this file used to have the category theory `\cross` as opposed to `\x`

### [2022-03-18 18:32:30](https://github.com/leanprover-community/mathlib/commit/f4e7f82)
chore(model_theory/definability): Change variable order in definability ([#12802](https://github.com/leanprover-community/mathlib/pull/12802))
Changes `first_order.language.definable` and `first_order.language.definable_set` to `set.definable` and `set.definable_set`.
Makes `set.definable` a `def` rather than a `structure`.

### [2022-03-18 18:32:29](https://github.com/leanprover-community/mathlib/commit/f6e85fc)
feat(order/rel_iso): Add `subrel` instances ([#12758](https://github.com/leanprover-community/mathlib/pull/12758))

### [2022-03-18 18:32:28](https://github.com/leanprover-community/mathlib/commit/fdd7e98)
feat(set_theory/*): Redefine `sup f` as `supr f` ([#12657](https://github.com/leanprover-community/mathlib/pull/12657))

### [2022-03-18 18:32:27](https://github.com/leanprover-community/mathlib/commit/290ad75)
feat(model_theory/terms_and_formulas): Atomic, Quantifier-Free, and Prenex Formulas ([#12557](https://github.com/leanprover-community/mathlib/pull/12557))
Provides a few induction principles for formulas
Defines atomic formulas with `first_order.language.bounded_formula.is_atomic`
Defines quantifier-free formulas with `first_order.language.bounded_formula.is_qf`
Defines `first_order.language.bounded_formula.is_prenex` indicating that a formula is in prenex normal form.

### [2022-03-18 18:32:25](https://github.com/leanprover-community/mathlib/commit/d17ecf9)
feat(category_theory/abelian) : injective resolutions of an object in a category with enough injectives ([#12545](https://github.com/leanprover-community/mathlib/pull/12545))
This pr dualises `src/category_theory/preadditive/projective_resolution.lean`. But since half of the file requires `abelian` assumption, I moved it to `src/category_theory/abelian/*`. The reason it needs `abelian` assumption is because I want class inference to deduce `exact f g` from `exact g.op f.op`.

### [2022-03-18 16:51:05](https://github.com/leanprover-community/mathlib/commit/80b8d19)
feat(model_theory/terms_and_formulas): Language maps act on terms, formulas, sentences, and theories ([#12609](https://github.com/leanprover-community/mathlib/pull/12609))
Defines the action of language maps on terms, formulas, sentences, and theories
Shows that said action commutes with realization

### [2022-03-18 16:51:04](https://github.com/leanprover-community/mathlib/commit/bf690dd)
feat(archive/100-theorems-list): add proof of thm 81 ([#7274](https://github.com/leanprover-community/mathlib/pull/7274))

### [2022-03-18 15:25:55](https://github.com/leanprover-community/mathlib/commit/b49bc77)
feat(data/nat/prime): add two lemmas with nat.primes, mul and dvd ([#12780](https://github.com/leanprover-community/mathlib/pull/12780))
These lemmas are close to available lemmas, but I could not actually find them.

### [2022-03-18 14:52:26](https://github.com/leanprover-community/mathlib/commit/5a547aa)
fix(ring_theory/power_series/basic): remove duplicate instance ([#12744](https://github.com/leanprover-community/mathlib/pull/12744))

### [2022-03-18 14:52:25](https://github.com/leanprover-community/mathlib/commit/14ee5e0)
feat(number_theory/arithmetic_function): add eq of multiplicative functions ([#12689](https://github.com/leanprover-community/mathlib/pull/12689))
To show that two multiplicative functions are equal, it suffices to show
that they are equal on prime powers. This is a commonly used strategy
when two functions are known to be multiplicative (e.g., they're both
Dirichlet convolutions of simpler multiplicative functions).
This will be used in several ongoing commits to prove asymptotics for
squarefree numbers.

### [2022-03-18 13:10:58](https://github.com/leanprover-community/mathlib/commit/ee8db20)
feat(measure_theory/group/action): add `null_measurable_set.smul` ([#12793](https://github.com/leanprover-community/mathlib/pull/12793))
Also add `null_measurable_set.preimage` and `ae_disjoint.preimage`.

### [2022-03-18 13:10:57](https://github.com/leanprover-community/mathlib/commit/2541387)
refactor(data/list/big_operators): review API ([#12782](https://github.com/leanprover-community/mathlib/pull/12782))
* merge `prod_monoid` into `big_operators`;
* review typeclass assumptions in some lemmas;
* use `to_additive` in more lemmas.

### [2022-03-18 13:10:56](https://github.com/leanprover-community/mathlib/commit/241d63d)
chore(algebraic_geometry/prime_spectrum/basic): remove TODO ([#12768](https://github.com/leanprover-community/mathlib/pull/12768))
Sober topological spaces has been defined and it has been proven (in this file) that prime spectrum is sober

### [2022-03-18 12:36:36](https://github.com/leanprover-community/mathlib/commit/cfa7f6a)
feat(group_theory/index): Intersection of finite index subgroups ([#12776](https://github.com/leanprover-community/mathlib/pull/12776))
This PR proves that if `H` and `K` are of finite index in `L`, then so is `H ⊓ K`.

### [2022-03-18 10:11:28](https://github.com/leanprover-community/mathlib/commit/5ecd27a)
refactor(topology/algebra/field): make `topological_division_ring` extend `has_continuous_inv₀` ([#12778](https://github.com/leanprover-community/mathlib/pull/12778))
Topological division ring had been rolling its own `continuous_inv` field which was almost identical to the `continuous_at_inv₀` field of `has_continuous_inv₀`. Here we refactor so that `topological_division_ring` extends `has_continuous_inv₀` instead.
- [x] depends on: [#12770](https://github.com/leanprover-community/mathlib/pull/12770)

### [2022-03-18 01:33:57](https://github.com/leanprover-community/mathlib/commit/a7cad67)
doc(overview): some additions to the Analysis section ([#12791](https://github.com/leanprover-community/mathlib/pull/12791))

### [2022-03-18 00:28:28](https://github.com/leanprover-community/mathlib/commit/a32d58b)
feat(analysis/*): generalize `set_smul_mem_nhds_zero` to topological vector spaces ([#12779](https://github.com/leanprover-community/mathlib/pull/12779))
The lemma holds for arbitrary topological vector spaces and has nothing to do with normed spaces.

### [2022-03-18 00:28:27](https://github.com/leanprover-community/mathlib/commit/adcfc58)
chore(data/matrix/block): Do not print `matrix.from_blocks` with dot notation ([#12774](https://github.com/leanprover-community/mathlib/pull/12774))
`A.from_blocks B C D` is weird and asymmetric compared to `from_blocks A B C D`. In future we might want to introduce notation.

### [2022-03-17 22:40:49](https://github.com/leanprover-community/mathlib/commit/cf8c5ff)
feat(algebra/pointwise): Subtraction/division of sets ([#12694](https://github.com/leanprover-community/mathlib/pull/12694))
Define pointwise subtraction/division on `set`.

### [2022-03-17 22:40:48](https://github.com/leanprover-community/mathlib/commit/32e5b6b)
feat(model_theory/terms_and_formulas): Casting and lifting terms and formulas ([#12467](https://github.com/leanprover-community/mathlib/pull/12467))
Defines `bounded_formula.cast_le`, which maps the `fin`-indexed variables with `fin.cast_le`
Defines `term.lift_at` and `bounded_formula.lift_at`, which raise `fin`-indexed variables above a certain threshold

### [2022-03-17 22:40:47](https://github.com/leanprover-community/mathlib/commit/a26dfc4)
feat(analysis/normed_space/basic): add `normed_division_ring` ([#12132](https://github.com/leanprover-community/mathlib/pull/12132))
This defines normed division rings and generalizes some of the lemmas that applied to normed fields instead to normed division rings.
This breaks one `ac_refl`; although this could be resolved by using `simp only {canonize_instances := tt}` first, it's easier to just tweak the proof.

### [2022-03-17 18:31:29](https://github.com/leanprover-community/mathlib/commit/2cb5edb)
chore(topology/algebra/group_with_zero): mark `has_continuous_inv₀` as a `Prop` ([#12770](https://github.com/leanprover-community/mathlib/pull/12770))
Since the type was not explicitly given, Lean marked this as a `Type`.

### [2022-03-17 18:31:28](https://github.com/leanprover-community/mathlib/commit/3e6e34e)
feat(linear_algebra/matrix): The Weinstein–Aronszajn identity ([#12767](https://github.com/leanprover-community/mathlib/pull/12767))
Notably this includes the proof of the determinant of a block matrix, which we didn't seem to have in the general case.
This also renames some of the lemmas about determinants of block matrices, and adds some missing API for `inv_of` on matrices.
There's some discussion at https://math.stackexchange.com/q/4105846/1896 about whether this name is appropriate, and whether it should be called "Sylvester's determinant theorem" instead.

### [2022-03-17 18:31:27](https://github.com/leanprover-community/mathlib/commit/6bfbb49)
docs(algebra/order/floor): Update floor_semiring docs to reflect it's just an ordered_semiring ([#12756](https://github.com/leanprover-community/mathlib/pull/12756))
The docs say that `floor_semiring` is a linear ordered semiring, but it is only an `ordered_semiring` in the code. Change the docs to reflect this fact.

### [2022-03-17 18:31:26](https://github.com/leanprover-community/mathlib/commit/ca80c8b)
feat(data/nat/sqrt_norm_num): norm_num extension for sqrt ([#12735](https://github.com/leanprover-community/mathlib/pull/12735))
Inspired by https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/2.20is.20not.20a.20square . The norm_num extension has to go in a separate file from `data.nat.sqrt` because `data.nat.sqrt` is a dependency of `norm_num`.

### [2022-03-17 18:31:25](https://github.com/leanprover-community/mathlib/commit/e944a99)
feat(algebraic_geometry/projective_spectrum) : lemmas about `vanishing_ideal` and `zero_locus` ([#12730](https://github.com/leanprover-community/mathlib/pull/12730))
This pr mimics the corresponding construction in `Spec`; other than `projective_spectrum.basic_open_eq_union_of_projection` everything else is a direct copy.

### [2022-03-17 17:30:04](https://github.com/leanprover-community/mathlib/commit/a1bdadd)
chore(topology/metric_space/hausdorff_distance): move two lemmas ([#12771](https://github.com/leanprover-community/mathlib/pull/12771))
Remove the dependence of `topology/metric_space/hausdorff_distance` on `analysis.normed_space.basic`, by moving out two lemmas.

### [2022-03-17 11:06:31](https://github.com/leanprover-community/mathlib/commit/11b2f36)
feat(algebraic_topology/fundamental_groupoid): Fundamental groupoid of punit ([#12757](https://github.com/leanprover-community/mathlib/pull/12757))
Proves the equivalence of the fundamental groupoid of punit and punit

### [2022-03-17 11:06:30](https://github.com/leanprover-community/mathlib/commit/cd196a8)
feat(group_theory/order_of_element): 1 is finite order, as is g⁻¹ ([#12749](https://github.com/leanprover-community/mathlib/pull/12749))

### [2022-03-17 11:06:29](https://github.com/leanprover-community/mathlib/commit/c9c4f40)
chore(topology/compact_open): remove `continuous_map.ev`, and rename related lemmas to `eval'` ([#12738](https://github.com/leanprover-community/mathlib/pull/12738))
This:
* Eliminates `continuous_map.ev α β` in favor of `(λ p : C(α, β) × α, p.1 p.2)`, as this unifies better and does not require lean to unfold `ev` at the right time.
* Renames `continuous_map.continuous_evalx` to `continuous_map.continuous_eval_const` to match the `smul_const`-style names.
* Renames `continuous_map.continuous_ev` to `continuous_map.continuous_eval'` to match `continuous_map.continuous_eval`.
* Renames `continuous_map.continuous_ev₁` to `continuous_map.continuous_eval_const'`.
* Adds `continuous_map.continuous_coe'` to match `continuous_map.continuous_coe`.
* Golfs some nearby lemmas.
The unprimed lemma names have the same statement but different typeclasses, so the `ev` lemmas have taken the primed name. See [this zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Evaluation.20of.20continuous.20functions.20is.20continuous/near/275502201) for discussion about whether one set of lemmas can be removed.

### [2022-03-17 11:06:28](https://github.com/leanprover-community/mathlib/commit/a6158f1)
feat(group_theory/subgroup/basic): One-sided closure induction lemmas ([#12725](https://github.com/leanprover-community/mathlib/pull/12725))
This PR adds one-sided closure induction lemmas, which I will need for Schreier's lemma.

### [2022-03-17 11:06:27](https://github.com/leanprover-community/mathlib/commit/b1bf390)
feat(number_theory/function_field): the ring of integers of a function field is not a field ([#12705](https://github.com/leanprover-community/mathlib/pull/12705))

### [2022-03-17 10:35:37](https://github.com/leanprover-community/mathlib/commit/c3ecf00)
feat(group_theory/sylow): direct product of sylow groups if all normal ([#11778](https://github.com/leanprover-community/mathlib/pull/11778))

### [2022-03-17 09:56:23](https://github.com/leanprover-community/mathlib/commit/31391dc)
feat(model_theory/basic, elementary_maps): Uses `fun_like` approach for first-order maps ([#12755](https://github.com/leanprover-community/mathlib/pull/12755))
Introduces classes `hom_class`, `strong_hom_class` to describe classes of first-order maps.

### [2022-03-17 08:18:32](https://github.com/leanprover-community/mathlib/commit/9d7a664)
feat(algebra/parity + *): generalize lemmas about parity ([#12761](https://github.com/leanprover-community/mathlib/pull/12761))
I moved more even/odd lemmas from nat/int to general semirings/rings.
Some files that explicitly used the nat/int namespace were changed along the way.

### [2022-03-17 07:17:48](https://github.com/leanprover-community/mathlib/commit/3ba25ea)
feat(topology/algebra/const_mul_action): add is_closed smul lemmas ([#12747](https://github.com/leanprover-community/mathlib/pull/12747))

### [2022-03-17 07:17:46](https://github.com/leanprover-community/mathlib/commit/87ab09c)
feat(category_theory/abelian/injective_resolution): homotopy between descents of morphism and two injective resolutions ([#12743](https://github.com/leanprover-community/mathlib/pull/12743))
This pr contains the following
* `category_theory.InjectiveResolution.desc_homotopy`: Any two descents of the same morphism are homotopic.
* `category_theory.InjectiveResolution.homotopy_equiv`: Any two injective resolutions of the same
  object are homotopically equivalent.

### [2022-03-17 06:22:26](https://github.com/leanprover-community/mathlib/commit/7000efb)
refactor(analysis/specific_limits): split into two files ([#12759](https://github.com/leanprover-community/mathlib/pull/12759))
Split the 1200-line file `analysis.specific_limits` into two:
- `analysis.specific_limits.normed` imports `normed_space` and covers limits in normed rings/fields
- `analysis.specific_limits.basic` imports only topology, and is still a bit of a grab-bag, covering limits in metric spaces, ordered rings, `ennreal`, etc.

### [2022-03-17 05:18:53](https://github.com/leanprover-community/mathlib/commit/877f2e7)
refactor(linear_algebra/ray): redefine `same_ray` to allow zero vectors ([#12618](https://github.com/leanprover-community/mathlib/pull/12618))
In a strictly convex space, the new definition is equivalent to the fact that the triangle inequality becomes an equality. The old definition was only used for nonzero vectors in `mathlib`. Also make the definition of `ray_vector` semireducible so that `ray_vector.setoid` can be an instance.

### [2022-03-17 04:20:16](https://github.com/leanprover-community/mathlib/commit/e547058)
docs(algebraic_topology/fundamental_groupoid/induced_maps): fix diagram rendering ([#12745](https://github.com/leanprover-community/mathlib/pull/12745))

### [2022-03-17 03:03:56](https://github.com/leanprover-community/mathlib/commit/d1e1304)
feat(combinatorics/simple_graph/connectivity): API for get_vert ([#12604](https://github.com/leanprover-community/mathlib/pull/12604))
From my Formalising Mathematics 2022 course.

### [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/192819b)
feat(category_theory/punit): A groupoid is equivalent to punit iff it has a unique arrow between any two objects ([#12726](https://github.com/leanprover-community/mathlib/pull/12726))
In terms of topology, when this is used with the fundamental groupoid, it means that a space is simply connected (we still need to define this) if and only if any two paths between the same points are homotopic, and contractible spaces are simply connected.

### [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/3a0532a)
feat(topology/homotopy/fundamental_group): prove fundamental group is independent of basepoint in path-connected spaces ([#12234](https://github.com/leanprover-community/mathlib/pull/12234))
Adds definition of fundamental group and proves fundamental group independent of basepoint choice in path-connected spaces.

### [2022-03-16 23:51:43](https://github.com/leanprover-community/mathlib/commit/4d350b9)
chore(*): move code, golf ([#12753](https://github.com/leanprover-community/mathlib/pull/12753))
* move `pow_pos` and `pow_nonneg` to `algebra.order.ring`;
* use the former to golf `has_pos pnat nat`;
* fix formatting.

### [2022-03-16 21:17:30](https://github.com/leanprover-community/mathlib/commit/b3abae5)
chore(category_theory/preadditive/projective_resolution): some minor golf ([#12739](https://github.com/leanprover-community/mathlib/pull/12739))

### [2022-03-16 21:17:29](https://github.com/leanprover-community/mathlib/commit/b24372f)
feat(model_theory/basic, terms_and_formulas): Helper functions for constant symbols ([#12722](https://github.com/leanprover-community/mathlib/pull/12722))
Defines a function `language.con` from `A` to constants of the language `L[[A]]`.
Changes the coercion of a constant to a term to a function `language.constants.term`.
Proves `simp` lemmas for interpretation of constant symbols and realization of constant terms.

### [2022-03-16 21:17:26](https://github.com/leanprover-community/mathlib/commit/3b91c32)
feat(group_theory/subgroup/basic): `map_le_map_iff_of_injective` for `subtype` ([#12713](https://github.com/leanprover-community/mathlib/pull/12713))
This PR adds the special case of `map_le_map_iff_of_injective` when the group homomorphism is `subtype`. This is useful when working with nested subgroups.

### [2022-03-16 19:40:36](https://github.com/leanprover-community/mathlib/commit/c459d2b)
feat(algebra/algebra/basic,data/matrix/basic): resolve a TODO about `alg_hom.map_smul_of_tower` ([#12684](https://github.com/leanprover-community/mathlib/pull/12684))
It turns out that this lemma doesn't actually help in the place I claimed it would, so I added the lemma that does help too.

### [2022-03-16 19:40:35](https://github.com/leanprover-community/mathlib/commit/6a71007)
feat(group_theory/quotient_group) finiteness of groups for sequences of homomorphisms ([#12660](https://github.com/leanprover-community/mathlib/pull/12660))

### [2022-03-16 18:34:52](https://github.com/leanprover-community/mathlib/commit/2e9985e)
feat(topology/algebra/order/basic): f ≤ᶠ[l] g implies limit of f ≤ limit of g ([#12727](https://github.com/leanprover-community/mathlib/pull/12727))
There are several implications of the form `eventually_*_of_tendsto_*`,
which involve the order relationships between the limit of a function
and other constants. What appears to be missing are reverse
implications: If two functions are eventually ordered, then their limits
respect the order.
This is lemma will be used in further work on the asymptotics of
squarefree numbers

### [2022-03-16 15:39:29](https://github.com/leanprover-community/mathlib/commit/693a3ac)
feat(number_theory/cyclotomic/basic): add is_primitive_root.adjoin ([#12716](https://github.com/leanprover-community/mathlib/pull/12716))
We add `is_cyclotomic_extension.is_primitive_root.adjoin`.
From flt-regular

### [2022-03-16 13:40:39](https://github.com/leanprover-community/mathlib/commit/b8faf13)
feat(data/finset/basic): add finset.filter_eq_self ([#12717](https://github.com/leanprover-community/mathlib/pull/12717))
and an epsilon of cleanup
from flt-regular

### [2022-03-16 13:40:38](https://github.com/leanprover-community/mathlib/commit/d495afd)
feat(category_theory/abelian/injective_resolution): descents of a morphism ([#12703](https://github.com/leanprover-community/mathlib/pull/12703))
This pr dualise `src/category_theory/preadditive/projective_resolution.lean`. The reason that it is moved to `abelian` folder is because we want `exact f g` from `exact g.op f.op` instance.
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the following:
Given `I : InjectiveResolution X` and  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a chain map `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwine the descent and the original morphism, see `category_theory.InjectiveResolution.desc_commutes`.
(Docstring contains more than what is currently in the file, but everything else will come soon)

### [2022-03-16 13:40:36](https://github.com/leanprover-community/mathlib/commit/f21a760)
feat(measure_theory/function/jacobian): change of variable formula in integrals in higher dimension ([#12492](https://github.com/leanprover-community/mathlib/pull/12492))
Let `μ` be a Lebesgue measure on a finite-dimensional real vector space, `s` a measurable set, and `f` a function which is differentiable and injective on `s`. Then `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`. (There is also a version for the Lebesgue integral, i.e., for `ennreal`-valued functions).

### [2022-03-16 11:53:36](https://github.com/leanprover-community/mathlib/commit/0964573)
feat(set_theory/cardinal): Lift `min` and `max` ([#12518](https://github.com/leanprover-community/mathlib/pull/12518))

### [2022-03-16 11:53:35](https://github.com/leanprover-community/mathlib/commit/717b11e)
feat(group_theory/noncomm_pi_coprod): homomorphism from pi monoids or groups ([#11744](https://github.com/leanprover-community/mathlib/pull/11744))

### [2022-03-16 10:05:27](https://github.com/leanprover-community/mathlib/commit/a50de33)
docs(algebra/group/hom): fix typo ([#12723](https://github.com/leanprover-community/mathlib/pull/12723))

### [2022-03-16 10:05:26](https://github.com/leanprover-community/mathlib/commit/35bb571)
chore(number_theory/primorial): speed up some proofs ([#12714](https://github.com/leanprover-community/mathlib/pull/12714))

### [2022-03-16 10:05:25](https://github.com/leanprover-community/mathlib/commit/a8bfcfe)
feat(algebraic_geometry/projective_spectrum): basic definitions of projective spectrum ([#12635](https://github.com/leanprover-community/mathlib/pull/12635))
This pr contains the basic definitions of projective spectrum of a graded ring:
- projective spectrum
- zero locus
- vanishing ideal

### [2022-03-16 10:05:24](https://github.com/leanprover-community/mathlib/commit/a7a2f9d)
feat(data/nat/fib): norm_num plugin for fib ([#12463](https://github.com/leanprover-community/mathlib/pull/12463))

### [2022-03-16 10:05:23](https://github.com/leanprover-community/mathlib/commit/500a1d3)
feat(data/pnat/find): port over `nat.find` API ([#12413](https://github.com/leanprover-community/mathlib/pull/12413))
Didn't port `pnat.find_add` because I got lost in the proof.

### [2022-03-16 10:05:22](https://github.com/leanprover-community/mathlib/commit/bbc66b5)
feat(group_theory/subsemigroup/basic): subsemigroups ([#12111](https://github.com/leanprover-community/mathlib/pull/12111))
Port over submonoid implementation to a generalization: subsemigroups.
Implement submonoids via extends using old_structure_cmd, since that is
what subsemirings do.
Copy over the attribution from submonoids because the content is almost
unchanged.
The submonoid file hasn't been changed, so no proofs rely on the
subsemigroups proofs.

### [2022-03-16 08:21:55](https://github.com/leanprover-community/mathlib/commit/50691e5)
chore(measure_theory/function): split files strongly_measurable and simple_func_dense ([#12711](https://github.com/leanprover-community/mathlib/pull/12711))
The files `strongly_measurable` and `simple_func_dense` contain general results, and results pertaining to the `L^p` space. We move the results regarding `L^p` to new files, to make sure that the main parts of the files can be imported earlier in the hierarchy. This is needed for a forthcoming integral refactor.

### [2022-03-16 08:21:54](https://github.com/leanprover-community/mathlib/commit/ba6c84d)
feat(ring_theory/fractional_ideal): two span_singleton lemmas ([#12656](https://github.com/leanprover-community/mathlib/pull/12656))

### [2022-03-16 08:21:53](https://github.com/leanprover-community/mathlib/commit/17c74f1)
feat(algebra/group_power/order): add le_pow ([#12436](https://github.com/leanprover-community/mathlib/pull/12436))
Added a new theorem so that library search will find it.

### [2022-03-16 08:21:52](https://github.com/leanprover-community/mathlib/commit/91f98e8)
feat(topology/bornology/hom): Locally bounded maps ([#12046](https://github.com/leanprover-community/mathlib/pull/12046))
Define `locally_bounded_map`, the type of locally bounded maps between two bornologies.

### [2022-03-16 08:21:51](https://github.com/leanprover-community/mathlib/commit/68033a2)
feat(set_theory/ordinal_arithmetic): A set of ordinals is bounded above iff it's small ([#11870](https://github.com/leanprover-community/mathlib/pull/11870))

### [2022-03-16 07:51:24](https://github.com/leanprover-community/mathlib/commit/a452bfa)
feat(analysis/seminorm): three simple lemmas about balls ([#12720](https://github.com/leanprover-community/mathlib/pull/12720))
The lemmas are in preparation to characterize the natural bornology in terms of seminorms in LCTVSs.

### [2022-03-16 05:24:58](https://github.com/leanprover-community/mathlib/commit/1f1289f)
feat(algebra/parity + data/{int, nat}/parity): parity lemmas for general semirings ([#12718](https://github.com/leanprover-community/mathlib/pull/12718))
This PR proves some general facts about adding even/odd elements in a semiring, thus removing the need to proving the same results for `nat` and `int`.

### [2022-03-16 03:13:34](https://github.com/leanprover-community/mathlib/commit/cbd6173)
chore(scripts): update nolints.txt ([#12728](https://github.com/leanprover-community/mathlib/pull/12728))
I am happy to remove some nolints for you!

### [2022-03-16 00:32:33](https://github.com/leanprover-community/mathlib/commit/45061f3)
chore(data/equiv/basic): use `option.elim` and `sum.elim` ([#12724](https://github.com/leanprover-community/mathlib/pull/12724))
We have these functions, why not use them?

### [2022-03-15 18:38:06](https://github.com/leanprover-community/mathlib/commit/b622d4d)
chore(algebra/associated): move prime_dvd_prime_iff_eq ([#12706](https://github.com/leanprover-community/mathlib/pull/12706))

### [2022-03-15 16:38:31](https://github.com/leanprover-community/mathlib/commit/7ed4f2c)
feat(group_theory/submonoid/operations): monoids are isomorphic to themselves as submonoids ([#12658](https://github.com/leanprover-community/mathlib/pull/12658))

### [2022-03-15 15:20:21](https://github.com/leanprover-community/mathlib/commit/375419f)
feat(algebra/algebra/subalgebra/pointwise): lemmas about `*` and `to_submodule` ([#12695](https://github.com/leanprover-community/mathlib/pull/12695))

### [2022-03-15 14:10:30](https://github.com/leanprover-community/mathlib/commit/7582e14)
feat(linear_algebra/matrix/determinant): special case of the matrix determinant lemma ([#12682](https://github.com/leanprover-community/mathlib/pull/12682))

### [2022-03-15 14:10:28](https://github.com/leanprover-community/mathlib/commit/9c09965)
feat(algebra/big_operators/finprod): finite product of power is power of finite product ([#12655](https://github.com/leanprover-community/mathlib/pull/12655))

### [2022-03-15 13:39:45](https://github.com/leanprover-community/mathlib/commit/88a5978)
doc(algebra/hierarchy_design): fix my name ([#12674](https://github.com/leanprover-community/mathlib/pull/12674))

### [2022-03-15 11:51:47](https://github.com/leanprover-community/mathlib/commit/530f008)
feat(linear_algebra/matrix/nonsingular_inverse): Add `matrix.list_prod_inv_reverse` ([#12691](https://github.com/leanprover-community/mathlib/pull/12691))

### [2022-03-15 11:51:46](https://github.com/leanprover-community/mathlib/commit/7a02c9e)
fix(set_theory/ordinal_arithmetic): remove redundant hypothesis from `CNF_rec` ([#12680](https://github.com/leanprover-community/mathlib/pull/12680))
The hypothesis in question was a theorem that could be deduced.

### [2022-03-15 11:51:45](https://github.com/leanprover-community/mathlib/commit/a3b39c6)
feat(linear_algebra/clifford_algebra/conjugation): add lemmas showing interaction between `involute` and `even_odd` ([#12672](https://github.com/leanprover-community/mathlib/pull/12672))
Often the even and odd submodules are defined in terms of involution, but this strategy doesn't actually work in characteristic two.

### [2022-03-15 11:51:44](https://github.com/leanprover-community/mathlib/commit/48ffeb7)
feat(group_theory/finiteness): quotient of fg is fg ([#12652](https://github.com/leanprover-community/mathlib/pull/12652))

### [2022-03-15 11:10:28](https://github.com/leanprover-community/mathlib/commit/a98202b)
chore(category_theory/preadditive/projective_resolution): typo ([#12702](https://github.com/leanprover-community/mathlib/pull/12702))

### [2022-03-15 11:10:27](https://github.com/leanprover-community/mathlib/commit/eefa425)
perf(analysis/convec/topology): remove topological_add_group.path_connected instance ([#12675](https://github.com/leanprover-community/mathlib/pull/12675))
The linter was right in [#10011](https://github.com/leanprover-community/mathlib/pull/10011) and `topological_add_group.path_connected` should not be an instance, because it creates enormous TC subproblems (turn on `pp.all` to get an idea of what's going on).
Apparently the instance isn't even used in mathlib.

### [2022-03-15 11:10:26](https://github.com/leanprover-community/mathlib/commit/5b90340)
feat(model_theory/terms_and_formulas): Notation for terms and formulas from Flypitch ([#12630](https://github.com/leanprover-community/mathlib/pull/12630))
Introduces some notation, localized to `first_order`, to make typing explicit terms and formulas easier.

### [2022-03-15 10:32:43](https://github.com/leanprover-community/mathlib/commit/d199eb9)
feat(ring_theory/graded_algebra/homogeneous_ideal): refactor `homogeneous_ideal` as a structure extending ideals ([#12673](https://github.com/leanprover-community/mathlib/pull/12673))
We refactored `homogeneous_ideal` as a structure extending ideals so that we can define a `set_like (homogeneous_ideal \McA) A` instance.

### [2022-03-15 10:32:41](https://github.com/leanprover-community/mathlib/commit/061d04b)
feat(category_theory/monoidal): distribute tensor over direct sum ([#12626](https://github.com/leanprover-community/mathlib/pull/12626))
This is preliminary to the monoidal structure on chain complexes.

### [2022-03-15 10:02:26](https://github.com/leanprover-community/mathlib/commit/078b213)
chore(category_theory/abelian/projective): fix typo ([#12701](https://github.com/leanprover-community/mathlib/pull/12701))

### [2022-03-15 08:11:54](https://github.com/leanprover-community/mathlib/commit/92e6759)
fix(category_theory/bicategory): remove spaces before closing parentheses ([#12700](https://github.com/leanprover-community/mathlib/pull/12700))

### [2022-03-15 08:11:53](https://github.com/leanprover-community/mathlib/commit/0bd6dc2)
chore(measure_theory): move and rename some lemmas ([#12699](https://github.com/leanprover-community/mathlib/pull/12699))
* move `ae_interval_oc_iff`, `ae_measurable_interval_oc_iff`, and `ae_interval_oc_iff'` to `measure_theory.measure.measure_space`, rename `ae_interval_oc_iff'` to `ae_restrict_interval_oc_iff`;
* add lemmas about `ae` and union of sets.

### [2022-03-15 08:11:52](https://github.com/leanprover-community/mathlib/commit/4b562f8)
doc(data/equiv/encodable): +2 docstrings ([#12698](https://github.com/leanprover-community/mathlib/pull/12698))

### [2022-03-15 08:11:51](https://github.com/leanprover-community/mathlib/commit/a3e0c85)
chore(cyclotomic/gal): update todo ([#12693](https://github.com/leanprover-community/mathlib/pull/12693))
this mentioned a non-existing old solution which got superseded by `is_primitive_root.power_basis`, but is still not the right solution in the long term

### [2022-03-15 08:11:50](https://github.com/leanprover-community/mathlib/commit/77395f1)
chore(algebra/module/basic): Move the scalar action earlier ([#12690](https://github.com/leanprover-community/mathlib/pull/12690))
This is prep work for golfing some of the instances.
This also adjust the variables slightly to be in a more sensible order.

### [2022-03-15 08:11:49](https://github.com/leanprover-community/mathlib/commit/025fe7c)
feat(group_theory/abelianization): An application of the three subgroups lemma ([#12677](https://github.com/leanprover-community/mathlib/pull/12677))
This PR uses the three subgroups lemma to prove that `⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G`.

### [2022-03-15 08:11:48](https://github.com/leanprover-community/mathlib/commit/b7978f3)
chore(analysis/seminorm): Weaken typeclasses on `convex` and `locally_convex` lemmas ([#12645](https://github.com/leanprover-community/mathlib/pull/12645))
Generalize type-classes `normed_linearly_ordered_field` to `normed_field` (otherwise it would not work over complex numbers).

### [2022-03-15 08:11:47](https://github.com/leanprover-community/mathlib/commit/53f6d68)
feat(category_theory/preadditive) : definition of injective resolution ([#12641](https://github.com/leanprover-community/mathlib/pull/12641))
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the definition of:
- `InjectiveResolution`;
- `has_injective_resolution` and `has_injective_resolutions`;
- injective object has injective resolution.

### [2022-03-15 08:11:46](https://github.com/leanprover-community/mathlib/commit/585d641)
refactor(linear_algebra/basic): split file ([#12637](https://github.com/leanprover-community/mathlib/pull/12637))
`linear_algebra.basic` has become a 2800 line monster, with lots of imports.
This is some further work on splitting it into smaller pieces, by extracting everything about (or needing) `span` to `linear_algebra.span`.

### [2022-03-15 06:38:19](https://github.com/leanprover-community/mathlib/commit/2ad9b39)
feat(algebra/associated): add irreducible.not_dvd_one ([#12686](https://github.com/leanprover-community/mathlib/pull/12686))

### [2022-03-15 03:40:54](https://github.com/leanprover-community/mathlib/commit/6d63c9b)
chore(scripts): update nolints.txt ([#12696](https://github.com/leanprover-community/mathlib/pull/12696))
I am happy to remove some nolints for you!

### [2022-03-15 03:40:53](https://github.com/leanprover-community/mathlib/commit/0fd9e30)
feat(set_theory/ordinal_arithmetic): `smul` coincides with `mul` ([#12692](https://github.com/leanprover-community/mathlib/pull/12692))

### [2022-03-15 03:05:43](https://github.com/leanprover-community/mathlib/commit/f337856)
feat(algebra/category): show categorical image in Module agrees with range ([#12605](https://github.com/leanprover-community/mathlib/pull/12605))
This just follows the existing code for the same fact in `AddCommGroup`.
This PR is preparing for a better API for homological calculations in `Module R`.

### [2022-03-15 00:51:24](https://github.com/leanprover-community/mathlib/commit/1148717)
chore(set_theory/ordinal_arithmetic): `well_founded` → `wf` ([#12615](https://github.com/leanprover-community/mathlib/pull/12615))

### [2022-03-14 20:38:51](https://github.com/leanprover-community/mathlib/commit/8d2e887)
feat(number_theory/function_field): add place at infinity  ([#12245](https://github.com/leanprover-community/mathlib/pull/12245))

### [2022-03-14 18:58:33](https://github.com/leanprover-community/mathlib/commit/c1c61d4)
feat(data/W/constructions): add constructions of W types ([#12292](https://github.com/leanprover-community/mathlib/pull/12292))
Here I write the naturals and lists as W-types and show that the definitions are equivalent. Any other interesting examples I should add?

### [2022-03-14 17:36:38](https://github.com/leanprover-community/mathlib/commit/2e56210)
chore(analysis/complex/upper_half_plane): don't use `abbreviation` ([#12679](https://github.com/leanprover-community/mathlib/pull/12679))
Some day we should add Poincaré metric as a `metric_space` instance on `upper_half_plane`.
In the meantime, make sure that Lean doesn't use `subtype` instances for `uniform_space` and/or `metric_space`.

### [2022-03-14 15:48:03](https://github.com/leanprover-community/mathlib/commit/28775ce)
feat(tactic/interactive): guard_{hyp,target}_mod_implicit ([#12668](https://github.com/leanprover-community/mathlib/pull/12668))
This adds two new tactics `guard_hyp_mod_implicit` and `guard_target_mod_implicit`, with the same syntax as `guard_hyp` and `guard_target`.  While the `guard_*` tactics check for syntax equality, the `guard_*_mod_implicit` tactics check for definitional equality with the `none` transparency

### [2022-03-14 13:59:47](https://github.com/leanprover-community/mathlib/commit/d8ef1de)
feat(topology/separation): add t2_space_iff ([#12628](https://github.com/leanprover-community/mathlib/pull/12628))
From my formalising mathematics 22 course

### [2022-03-14 13:59:46](https://github.com/leanprover-community/mathlib/commit/5242a7f)
feat(data/list/infix): add lemmas and instances ([#12511](https://github.com/leanprover-community/mathlib/pull/12511))

### [2022-03-14 13:59:45](https://github.com/leanprover-community/mathlib/commit/df3792f)
refactor(data/set): generalize `set.restrict` and take set argument first in both `set.restrict` and `subtype.restrict` ([#12510](https://github.com/leanprover-community/mathlib/pull/12510))
Generalizes `set.restrict` to Pi types and makes both this function and `subtype.restrict` take the restricting index set before the Pi type to restrict, which makes taking the image/preimage of a set of Pi types easier (`s.restrict '' pis` is shorter than `(λ p, set.restrict p s) '' pis` -- I'd argue that this is the more common case than taking the image of a set of restricting sets on a single Pi type). Changed uses of `set.restrict` to use dot notation where possible.

### [2022-03-14 13:59:43](https://github.com/leanprover-community/mathlib/commit/c1edbec)
feat(set_theory/ordinal_topology): Basic results on the order topology of ordinals ([#11861](https://github.com/leanprover-community/mathlib/pull/11861))
We link together various notions about ordinals to their topological counterparts.

### [2022-03-14 12:19:21](https://github.com/leanprover-community/mathlib/commit/09ea7fb)
feat(data/finset/noncomm_prod): finite pi lemmas ([#12291](https://github.com/leanprover-community/mathlib/pull/12291))
including a few helpers

### [2022-03-14 11:12:21](https://github.com/leanprover-community/mathlib/commit/fc882ff)
chore(ci): update trepplein to version 1.1 ([#12669](https://github.com/leanprover-community/mathlib/pull/12669))
New upstream release, fixing some performance issues.

### [2022-03-14 11:12:20](https://github.com/leanprover-community/mathlib/commit/abb8e5d)
feat(set_theory/principal): If `a` isn't additive principal, it's the sum of two smaller ordinals ([#12664](https://github.com/leanprover-community/mathlib/pull/12664))

### [2022-03-14 11:12:19](https://github.com/leanprover-community/mathlib/commit/cc6e2eb)
feat(group_theory/commutator): The three subgroups lemma ([#12634](https://github.com/leanprover-community/mathlib/pull/12634))
This PR proves the three subgroups lemma: If `⁅⁅H₂, H₃⁆, H₁⁆ = ⊥` and `⁅⁅H₃, H₁⁆, H₂⁆ = ⊥`, then `⁅⁅H₁, H₂⁆, H₃⁆ = ⊥`.

### [2022-03-14 11:12:18](https://github.com/leanprover-community/mathlib/commit/6a51706)
chore(topology/homotopy): Move more algebraic-flavored content about fundamental groupoid to algebraic_topology folder ([#12631](https://github.com/leanprover-community/mathlib/pull/12631))
Moved:
  - `topology/homotopy/fundamental_groupoid.lean` to `algebraic_topology/fundamental_groupoid/basic.lean`
  - the second half of `topology/homotopy/product.lean`, dealing with `fundamental_groupoid_functor` preserving products, to `algebraic_topology/fundamental_groupoid/product.lean`
  - `topology/homotopy/induced_maps.lean` to `algebraic_topology/fundamental_groupoid/induced_maps.lean`

### [2022-03-14 09:29:31](https://github.com/leanprover-community/mathlib/commit/a2544de)
chore(algebra/category/Module): simp lemmas for monoidal closed ([#12608](https://github.com/leanprover-community/mathlib/pull/12608))
I'm worried by the fact that I can't express the coercions here without using `@`. They do turn up in the wild, however!

### [2022-03-14 09:29:29](https://github.com/leanprover-community/mathlib/commit/31e60c8)
feat(set_theory/{ordinal, ordinal_arithmetic}): Add various instances for `o.out.α` ([#12508](https://github.com/leanprover-community/mathlib/pull/12508))

### [2022-03-14 09:29:27](https://github.com/leanprover-community/mathlib/commit/1f428f3)
feat(data/list/basic): Split and intercalate are inverses ([#12466](https://github.com/leanprover-community/mathlib/pull/12466))
Show that split and intercalate are inverses of each other (under suitable conditions)

### [2022-03-14 09:29:26](https://github.com/leanprover-community/mathlib/commit/cd001b2)
feat(category_theory/bicategory/free): define free bicategories ([#11998](https://github.com/leanprover-community/mathlib/pull/11998))

### [2022-03-14 08:31:44](https://github.com/leanprover-community/mathlib/commit/520f204)
feat(analysis/seminorm): add lemmas for inequalities and `finset.sup` ([#12650](https://github.com/leanprover-community/mathlib/pull/12650))
These lemmas are not lean-trivial since seminorms map to the `real` and not to `nnreal`.

### [2022-03-14 08:31:43](https://github.com/leanprover-community/mathlib/commit/0f3bfda)
feat(analysis/complex/schwarz): some versions of the Schwarz lemma ([#12633](https://github.com/leanprover-community/mathlib/pull/12633))

### [2022-03-14 08:31:42](https://github.com/leanprover-community/mathlib/commit/c2368be)
feat(topology/hom/open): Continuous open maps ([#12406](https://github.com/leanprover-community/mathlib/pull/12406))
Define `continuous_open_map`, the type of continuous opens maps between two topological spaces, and `continuous_open_map_class`, its companion hom class.

### [2022-03-14 07:05:57](https://github.com/leanprover-community/mathlib/commit/7b7fea5)
refactor(set_theory/cardinal_ordinal): `aleph_is_principal_aleph` → `principal_add_aleph` ([#12663](https://github.com/leanprover-community/mathlib/pull/12663))
This matches the naming scheme used throughout `set_theory/principal.lean`.

### [2022-03-14 07:05:56](https://github.com/leanprover-community/mathlib/commit/6ebb378)
feat(set_theory/ordinal): `ord 1 = 1` ([#12662](https://github.com/leanprover-community/mathlib/pull/12662))

### [2022-03-14 07:05:55](https://github.com/leanprover-community/mathlib/commit/18ba395)
feat(algebra/support) support of power is subset of support ([#12654](https://github.com/leanprover-community/mathlib/pull/12654))

### [2022-03-14 07:05:54](https://github.com/leanprover-community/mathlib/commit/6b3b567)
chore(topology/algebra/group_with_zero): fix docstring for has_continuous_inv0 ([#12653](https://github.com/leanprover-community/mathlib/pull/12653))

### [2022-03-14 07:05:53](https://github.com/leanprover-community/mathlib/commit/1f5950a)
feat(analysis/seminorm): add lemmas for `with_seminorms` ([#12649](https://github.com/leanprover-community/mathlib/pull/12649))
Two helper lemmas that make it easier to generate an instance for `with_seminorms`.

### [2022-03-14 07:05:51](https://github.com/leanprover-community/mathlib/commit/b6fa3be)
move(topology/sets/*): Move topological types of sets together ([#12648](https://github.com/leanprover-community/mathlib/pull/12648))
Move
* `topology.opens` to `topology.sets.opens`
* `topology.compacts` to `topology.sets.closeds` and `topology.sets.compacts`
`closeds` and `clopens` go into `topology.sets.closeds` and `compacts`, `nonempty_compacts`, `positive_compacts` and `compact_opens` go into `topology.sets.compacts`.

### [2022-03-14 07:05:50](https://github.com/leanprover-community/mathlib/commit/778dfd5)
chore(analysis/locally_convex/basic): generalize lemmas and add simple lemmas  ([#12643](https://github.com/leanprover-community/mathlib/pull/12643))
Gerenalize all 'simple' lemmas for `absorb` and `absorbent` to the type-class `[semi_normed_ring 𝕜] [has_scalar 𝕜 E]`.
Additionally, add the lemmas `absorbs_empty`, `balanced_mem` and `zero_singleton_balanced`.

### [2022-03-14 07:05:49](https://github.com/leanprover-community/mathlib/commit/f8d947c)
add endofunctor.algebra ([#12642](https://github.com/leanprover-community/mathlib/pull/12642))
This is the second attempt at the following outdated pull request: https://github.com/leanprover-community/mathlib/pull/12295
The original post:
In this PR I define algebras of endofunctors, make the forgetful functor to the ambient category, and show that initial algebras have isomorphisms as their structure maps. This is mostly taken from `monad.algebra`.

### [2022-03-14 05:19:50](https://github.com/leanprover-community/mathlib/commit/174f1da)
refactor(set_theory/ordinal_arithmetic): Turn various results into simp lemmas ([#12661](https://github.com/leanprover-community/mathlib/pull/12661))
In order to do this, we had to change the direction of various equalities.

### [2022-03-14 05:19:49](https://github.com/leanprover-community/mathlib/commit/ad0988b)
docs(algebra/*): Add docstrings to additive lemmas ([#12578](https://github.com/leanprover-community/mathlib/pull/12578))
Many additive lemmas had no docstrings while their multiplicative counterparts had. This adds them in all files under `algebra`.

### [2022-03-14 04:48:58](https://github.com/leanprover-community/mathlib/commit/580e1d9)
feat(analysis/inner_product_space/pi_L2): `linear_isometry.extend` ([#12192](https://github.com/leanprover-community/mathlib/pull/12192))
Let `S` be a subspace of a finite-dimensional inner product
space `V`.  A linear isometry mapping `S` into `V` can be extended to a
full isometry of `V`.  Note that this is false if we remove the
finite-dimensional hypothesis; consider the shift operator
(0, x_2, x_3, ...) to (x_2, x_3, x_4, ...).
I hope that the naming choice is consistent.  Combining the two
`simp only` blocks in `linear_isometry.extend_apply` results in a
timeout, but they seem to work okay split up.

### [2022-03-14 02:40:00](https://github.com/leanprover-community/mathlib/commit/3751ec6)
feat(measure_theory/group/fundamental_domain): ess_sup_measure_restrict ([#12603](https://github.com/leanprover-community/mathlib/pull/12603))
If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as that of `f` on all of its domain.

### [2022-03-13 14:52:04](https://github.com/leanprover-community/mathlib/commit/223e742)
feat(analysis/*/{exponential, spectrum}): spectrum of a selfadjoint element is real ([#12417](https://github.com/leanprover-community/mathlib/pull/12417))
This provides several properties of the exponential function and uses it to prove that for `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜 𝕜` maps the spectrum of `a : A` (where `A` is a `𝕜`-algebra) into the spectrum of `exp 𝕜 A a`. In addition, `exp ℂ A (I • a)` is unitary when `a` is selfadjoint. Consequently, the spectrum of a selfadjoint element is real.

### [2022-03-13 13:32:14](https://github.com/leanprover-community/mathlib/commit/7d34f78)
chore(algebra/algebra/subalgebra): reduce imports ([#12636](https://github.com/leanprover-community/mathlib/pull/12636))
Splitting a file, and reducing imports. No change in contents.

### [2022-03-13 07:59:44](https://github.com/leanprover-community/mathlib/commit/daa257f)
feat(analysis/normed_space/star/basic): `matrix.entrywise_sup_norm_star_eq_norm` ([#12201](https://github.com/leanprover-community/mathlib/pull/12201))
This is precisely the statement needed for a `normed_star_monoid`
instance on matrices using the entrywise sup norm.

### [2022-03-13 04:14:17](https://github.com/leanprover-community/mathlib/commit/73530b5)
feat(algebra/algebra/spectrum): prove spectral inclusion for algebra homomorphisms ([#12573](https://github.com/leanprover-community/mathlib/pull/12573))
If `φ : A →ₐ[R] B` is an `R`-algebra homomorphism, then for any `a : A`, `spectrum R (φ a) ⊆ spectrum R a`.

### [2022-03-13 00:04:24](https://github.com/leanprover-community/mathlib/commit/9f1f8c1)
feat(ring_theory/graded_algebra/homogeneous_ideal): definition of irrelevant ideal of a graded algebra ([#12548](https://github.com/leanprover-community/mathlib/pull/12548))
For an `ℕ`-graded ring `⨁ᵢ 𝒜ᵢ`, the irrelevant ideal refers to `⨁_{i>0} 𝒜ᵢ`.
This construction is used in the Proj construction in algebraic geometry.

### [2022-03-12 21:08:56](https://github.com/leanprover-community/mathlib/commit/5b36941)
feat(data/list/basic): Stronger form of `fold_fixed` ([#12613](https://github.com/leanprover-community/mathlib/pull/12613))

### [2022-03-12 19:48:16](https://github.com/leanprover-community/mathlib/commit/3da03b9)
refactor(group_theory/commutator): Use variables and rearrange lemmas ([#12629](https://github.com/leanprover-community/mathlib/pull/12629))
This PR adds variables, and rearranges some of the lemmas (moving the lemmas about normal subgroups to a separate section).

### [2022-03-12 18:01:22](https://github.com/leanprover-community/mathlib/commit/23269bf)
feat(category_theory/preadditive/Mat): ring version ([#12617](https://github.com/leanprover-community/mathlib/pull/12617))

### [2022-03-12 18:01:21](https://github.com/leanprover-community/mathlib/commit/707df2c)
feat(model_theory/definability): Definability with parameters ([#12611](https://github.com/leanprover-community/mathlib/pull/12611))
Extends the definition of definable sets to include a parameter set.
Defines shorthands is_definable₁ and is_definable₂ for 1- and 2-dimensional definable sets.

### [2022-03-12 18:01:20](https://github.com/leanprover-community/mathlib/commit/9293174)
feat(algebra/category/Module): monoidal_preadditive ([#12607](https://github.com/leanprover-community/mathlib/pull/12607))

### [2022-03-12 18:01:19](https://github.com/leanprover-community/mathlib/commit/e4ea2bc)
feat(topology/algebra/continuous_monoid_hom): Define the Pontryagin dual ([#12602](https://github.com/leanprover-community/mathlib/pull/12602))
This PR adds the definition of the Pontryagin dual.
We're still missing the locally compact instance. I thought I could get it from `closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B))`, but actually `C(A, B)` is almost never locally compact.

### [2022-03-12 18:01:18](https://github.com/leanprover-community/mathlib/commit/5a9fb92)
feat(topology/category/Locale): The category of locales ([#12580](https://github.com/leanprover-community/mathlib/pull/12580))
Define `Locale`, the category of locales, as the opposite of `Frame`.

### [2022-03-12 18:01:17](https://github.com/leanprover-community/mathlib/commit/96bae07)
feat(order/complete_lattice): add `complete_lattice.independent_pair` ([#12565](https://github.com/leanprover-community/mathlib/pull/12565))
This makes `complete_lattice.independent` easier to work with in the degenerate case.

### [2022-03-12 16:17:42](https://github.com/leanprover-community/mathlib/commit/7e5ac6a)
chore(analysis/convex/strict): Reduce typeclass assumptions, golf ([#12627](https://github.com/leanprover-community/mathlib/pull/12627))
Move lemmas around so they are stated with the correct generality. Restate theorems using pointwise operations. Golf proofs. Fix typos in docstrings.

### [2022-03-12 16:17:41](https://github.com/leanprover-community/mathlib/commit/22bdc8e)
feat(order/upper_lower): Upper/lower sets ([#12189](https://github.com/leanprover-community/mathlib/pull/12189))
Define upper and lower sets both as unbundled predicates and as bundled types.

### [2022-03-12 15:43:41](https://github.com/leanprover-community/mathlib/commit/dc4e5cb)
chore(analysis): move lemmas around ([#12621](https://github.com/leanprover-community/mathlib/pull/12621))
* move `smul_unit_ball` to `analysis.normed_space.pointwise`, rename it to `smul_unit_ball_of_pos`;
* reorder lemmas in `analysis.normed_space.pointwise`;
* add `vadd_ball_zero`, `vadd_closed_ball_zero`, `smul_unit`, `affinity_unit_ball`, `affinity_unit_closed_ball`.

### [2022-03-12 14:08:13](https://github.com/leanprover-community/mathlib/commit/7257ee7)
chore(data/nat/prime): restate card_multiples without finset.sep ([#12625](https://github.com/leanprover-community/mathlib/pull/12625))
As suggested by Eric Wieser in [#12592](https://github.com/leanprover-community/mathlib/pull/12592).

### [2022-03-12 14:08:12](https://github.com/leanprover-community/mathlib/commit/a63b99c)
chore(category_theory/closed/monoidal): fix notation ([#12612](https://github.com/leanprover-community/mathlib/pull/12612))
Previously the `C` in the internal hom arrow ` ⟶[C] ` was hardcoded, which wasn't very useful!
I've also reduced the precedence slightly, so we now require more parentheses, but I think these are less confusing rather than more so it is a good side effect?

### [2022-03-12 14:08:11](https://github.com/leanprover-community/mathlib/commit/956f3db)
chore(category_theory/limits): correct lemma names ([#12606](https://github.com/leanprover-community/mathlib/pull/12606))

### [2022-03-12 14:08:10](https://github.com/leanprover-community/mathlib/commit/9456a74)
feat(group_theory/commutator): Prove `commutator_eq_bot_iff_le_centralizer` ([#12598](https://github.com/leanprover-community/mathlib/pull/12598))
This lemma is needed for the three subgroups lemma.

### [2022-03-12 14:08:09](https://github.com/leanprover-community/mathlib/commit/b9ab27b)
feat(group_theory/subgroup/basic): add eq_one_of_noncomm_prod_eq_one_of_independent ([#12525](https://github.com/leanprover-community/mathlib/pull/12525))
`finset.noncomm_prod` is “injective” in `f` if `f` maps into independent subgroups.  It
generalizes (one direction of) `subgroup.disjoint_iff_mul_eq_one`.

### [2022-03-12 13:35:45](https://github.com/leanprover-community/mathlib/commit/b21c1c9)
split(analysis/locally_convex/basic): Split off `analysis.seminorm` ([#12624](https://github.com/leanprover-community/mathlib/pull/12624))
Move `balanced`, `absorbs`, `absorbent` to a new file.
For `analysis.seminorm`, I'm crediting
* Jean for [#4827](https://github.com/leanprover-community/mathlib/pull/4827)
* myself for
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
  * [#11487](https://github.com/leanprover-community/mathlib/pull/11487)
* Moritz for
  * [#11329](https://github.com/leanprover-community/mathlib/pull/11329)
  * [#11414](https://github.com/leanprover-community/mathlib/pull/11414)
  * [#11477](https://github.com/leanprover-community/mathlib/pull/11477)
For `analysis.locally_convex.basic`, I'm crediting
* Jean for [#4827](https://github.com/leanprover-community/mathlib/pull/4827)
* Bhavik for
  * [#7358](https://github.com/leanprover-community/mathlib/pull/7358)
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
* myself for
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
  * [#10999](https://github.com/leanprover-community/mathlib/pull/10999)
  * [#11487](https://github.com/leanprover-community/mathlib/pull/11487)

### [2022-03-12 11:37:20](https://github.com/leanprover-community/mathlib/commit/a4187fe)
chore(algebra/category/Module): remove unnecessary universe restriction ([#12610](https://github.com/leanprover-community/mathlib/pull/12610))

### [2022-03-12 11:37:19](https://github.com/leanprover-community/mathlib/commit/31d28c6)
fix(src/algebra/big_operators/multiset): unify prod_le_pow_card and prod_le_of_forall_le ([#12589](https://github.com/leanprover-community/mathlib/pull/12589))
using the name `prod_le_pow_card` as per https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/duplicate.20lemmas
but use the phrasing of prod_le_of_forall_le with non-implicit
`multiset`, as that is how it is used.

### [2022-03-12 11:06:34](https://github.com/leanprover-community/mathlib/commit/2241588)
feat(topology/homotopy): Homotopic maps induce naturally isomorphic functors between fundamental groupoid ([#11595](https://github.com/leanprover-community/mathlib/pull/11595))

### [2022-03-12 09:57:54](https://github.com/leanprover-community/mathlib/commit/5f3f70f)
doc(category_theory/monoidal/rigid): noting future work ([#12620](https://github.com/leanprover-community/mathlib/pull/12620))

### [2022-03-12 09:57:53](https://github.com/leanprover-community/mathlib/commit/3d41a5b)
refactor(group_theory/commutator): Golf proof of `commutator_mono` ([#12619](https://github.com/leanprover-community/mathlib/pull/12619))
This PR golfs the proof of `commutator_mono` by using `commutator_le` rather than `closure_mono`.

### [2022-03-12 09:57:52](https://github.com/leanprover-community/mathlib/commit/72c6979)
refactor(set_theory/ordinal_arithmetic): remove dot notation ([#12614](https://github.com/leanprover-community/mathlib/pull/12614))

### [2022-03-12 08:36:18](https://github.com/leanprover-community/mathlib/commit/3aaa564)
refactor(group_theory/commutator): Golf proof of `commutator_comm` ([#12600](https://github.com/leanprover-community/mathlib/pull/12600))
This PR golfs the proof of `commutator_comm`.

### [2022-03-12 05:57:32](https://github.com/leanprover-community/mathlib/commit/1463f59)
fix(tactic/suggest): fixing `library_search` ([#12616](https://github.com/leanprover-community/mathlib/pull/12616))
Further enhancing `library_search` search possibilities for 'ne' and 'not eq'
Related: https://github.com/leanprover-community/mathlib/pull/11742

### [2022-03-12 05:57:31](https://github.com/leanprover-community/mathlib/commit/e8d0cac)
feat(analysis/inner_product_space/adjoint): gram lemmas ([#12139](https://github.com/leanprover-community/mathlib/pull/12139))
The gram operator is a self-adjoint, positive operator.

### [2022-03-12 04:22:20](https://github.com/leanprover-community/mathlib/commit/1eaf499)
feat(group_theory/subgroup/basic): {multiset_,}noncomm_prod_mem ([#12523](https://github.com/leanprover-community/mathlib/pull/12523))
and same for submonoids.

### [2022-03-12 04:22:19](https://github.com/leanprover-community/mathlib/commit/6ee6203)
feat(counterexample) : a homogeneous ideal that is not prime but homogeneously prime ([#12485](https://github.com/leanprover-community/mathlib/pull/12485))
For graded rings, if the indexing set is nice, then a homogeneous ideal `I` is prime if and only if it is homogeneously prime, i.e. product of two homogeneous elements being in `I` implying at least one of them is in `I`. This fact is in `src/ring_theory/graded_algebra/radical.lean`. This counter example is meant to show that "nice condition" at least needs to include cancellation property by exhibiting an ideal in Zmod4^2 graded by a two element set being homogeneously prime but not prime. In [#12277](https://github.com/leanprover-community/mathlib/pull/12277), Eric suggests that this counter example is worth pr-ing, so here is the pr.

### [2022-03-12 02:28:54](https://github.com/leanprover-community/mathlib/commit/2e7483d)
refactor(group_theory/commutator): Move and golf `commutator_le` ([#12599](https://github.com/leanprover-community/mathlib/pull/12599))
This PR golfs `commutator_le` and moves it earlier in the file so that it can be used earlier.
This PR will conflict with [#12600](https://github.com/leanprover-community/mathlib/pull/12600), so don't merge them simultaneously (bors d+ might be better).

### [2022-03-12 02:28:53](https://github.com/leanprover-community/mathlib/commit/09d0f02)
chore({category_theory,order}/category/*): Missing `dsimp` lemmas ([#12593](https://github.com/leanprover-community/mathlib/pull/12593))
Add the `dsimp` lemmas stating `↥(of α) = α `. Also rename the few `to_dual` functors to `dual` to match the other files.

### [2022-03-12 02:28:52](https://github.com/leanprover-community/mathlib/commit/4e302f5)
feat(data/nat): add card_multiples ([#12592](https://github.com/leanprover-community/mathlib/pull/12592))

### [2022-03-12 02:28:51](https://github.com/leanprover-community/mathlib/commit/222faed)
feat(algebra/group/units_hom): make `is_unit.map` work on `monoid_hom_class` ([#12577](https://github.com/leanprover-community/mathlib/pull/12577))
`ring_hom.is_unit_map` and `mv_power_series.is_unit_constant_coeff` are now redundant, but to keep this diff small I've left them around.

### [2022-03-12 02:28:50](https://github.com/leanprover-community/mathlib/commit/8364980)
feat(category_theory): interderivability of kernel and equalizers in preadditive cats ([#12576](https://github.com/leanprover-community/mathlib/pull/12576))

### [2022-03-11 23:40:59](https://github.com/leanprover-community/mathlib/commit/c0a51cf)
chore(*): update to 3.41.0c ([#12591](https://github.com/leanprover-community/mathlib/pull/12591))

### [2022-03-11 21:59:23](https://github.com/leanprover-community/mathlib/commit/e7db193)
feat(algebra/module): add `module.nontrivial` ([#12594](https://github.com/leanprover-community/mathlib/pull/12594))

### [2022-03-11 19:18:32](https://github.com/leanprover-community/mathlib/commit/5856c0c)
feat(data/finset/noncomm_prod): add noncomm_prod_mul_distrib ([#12524](https://github.com/leanprover-community/mathlib/pull/12524))
The non-commutative version of `finset.sum_union`.

### [2022-03-11 19:18:31](https://github.com/leanprover-community/mathlib/commit/dc5f7fb)
feat(set_theory/ordinal_arithmetic): Further theorems on normal functions ([#12484](https://github.com/leanprover-community/mathlib/pull/12484))
We prove various theorems giving more convenient characterizations of normal functions.

### [2022-03-11 19:18:30](https://github.com/leanprover-community/mathlib/commit/e3ad468)
feat(data/list/prod_monoid): add prod_eq_pow_card ([#12473](https://github.com/leanprover-community/mathlib/pull/12473))

### [2022-03-11 17:31:10](https://github.com/leanprover-community/mathlib/commit/7dcba96)
feat(order/monotone): Folds of monotone functions are monotone ([#12581](https://github.com/leanprover-community/mathlib/pull/12581))

### [2022-03-11 17:31:09](https://github.com/leanprover-community/mathlib/commit/3dcc168)
feat(linear_algebra/projective_space/basic): The projectivization of a vector space. ([#12438](https://github.com/leanprover-community/mathlib/pull/12438))
This provides the initial definitions for the projective space associated to a vector space.
Future work:
- Linear subspaces of projective spaces, connection with subspaces of the vector space, etc.
- The incidence geometry structure of a projective space.
- The fundamental theorem of projective geometry.
I will tag this PR as RFC for now. If you see something missing from this *initial* PR, please let me know!

### [2022-03-11 16:25:21](https://github.com/leanprover-community/mathlib/commit/003701f)
feat(model_theory/substructures): Facts about substructures ([#12258](https://github.com/leanprover-community/mathlib/pull/12258))
Shows that `closure L s` can be viewed as the set of realizations of terms over `s`.
Bounds the cardinality of `closure L s` by the cardinality of the type of terms.
Characterizes `closure L[[A]] s`.

### [2022-03-11 16:25:19](https://github.com/leanprover-community/mathlib/commit/d6f337d)
feat(set_theory/ordinal_arithmetic): The derivative of multiplication ([#12202](https://github.com/leanprover-community/mathlib/pull/12202))
We prove that for `0 < a`, `deriv ((*) a) b = a ^ ω * b`.

### [2022-03-11 13:44:08](https://github.com/leanprover-community/mathlib/commit/e6fef39)
feat(algebra/order/monoid): add `with_zero.canonically_linear_ordered_add_monoid` ([#12568](https://github.com/leanprover-community/mathlib/pull/12568))
This also removes some non-terminal `simp`s in nearby proofs

### [2022-03-11 13:44:07](https://github.com/leanprover-community/mathlib/commit/12786d0)
feat(order/sup_indep): add `finset.sup_indep_pair` ([#12549](https://github.com/leanprover-community/mathlib/pull/12549))
This is used to provide simp lemmas about `sup_indep` on `bool` and `fin 2`.

### [2022-03-11 13:44:06](https://github.com/leanprover-community/mathlib/commit/4dc4dc8)
chore(topology/algebra/module/basic): cleanup variables and coercions ([#12542](https://github.com/leanprover-community/mathlib/pull/12542))
Having the "simple" variables in the lemmas statements rather than globally makes it easier to move lemmas around in future.
This also mean lemmas like `coe_comp` can have their arguments in a better order, as it's easier to customize the argument order at the declaration.
This also replaces a lot of `(_ : M₁ → M₂)`s with `⇑_` for brevity in lemma statements.
No lemmas statements (other than argument reorders) or proofs have changed.

### [2022-03-11 10:13:17](https://github.com/leanprover-community/mathlib/commit/02e0ab2)
refactor(group_theory/commutator): Golf some proofs ([#12586](https://github.com/leanprover-community/mathlib/pull/12586))
This PR golfs the proofs of some lemmas in `commutator.lean`.
I also renamed `bot_commutator` and `commutator_bot` to `commutator_bot_left` and `commutator_bot_right`, since "bot_commutator" didn't sound right to me (you would say "the commutator of H and K", not "H commutator K"), but I can revert to the old name if you want.

### [2022-03-11 10:13:16](https://github.com/leanprover-community/mathlib/commit/d9a774e)
feat(order/hom): `prod.swap` as an `order_iso` ([#12585](https://github.com/leanprover-community/mathlib/pull/12585))

### [2022-03-11 08:22:26](https://github.com/leanprover-community/mathlib/commit/840a042)
feat(data/list/basic): Miscellaneous `fold` lemmas ([#12579](https://github.com/leanprover-community/mathlib/pull/12579))

### [2022-03-11 08:22:25](https://github.com/leanprover-community/mathlib/commit/1a581ed)
refactor(group_theory/solvable): Golf proof ([#12552](https://github.com/leanprover-community/mathlib/pull/12552))
This PR golfs the proof of insolvability of S_5, using the new commutator notation.

### [2022-03-11 08:22:24](https://github.com/leanprover-community/mathlib/commit/1326aa7)
feat(analysis/special_functions): limit of x^s * exp(-x) for s real ([#12540](https://github.com/leanprover-community/mathlib/pull/12540))

### [2022-03-11 08:22:23](https://github.com/leanprover-community/mathlib/commit/e553f8a)
refactor(algebra/group/to_additive): monadic code cosmetics ([#12527](https://github.com/leanprover-community/mathlib/pull/12527))
as suggested by @kmill and @eric-wieser, but the merge was faster
Also improve test file.

### [2022-03-11 08:22:22](https://github.com/leanprover-community/mathlib/commit/47b1ddf)
feat(data/setoid/partition): Relate `setoid.is_partition` and `finpartition` ([#12459](https://github.com/leanprover-community/mathlib/pull/12459))
Add two functions that relate `setoid.is_partition` and `finpartition`:
* `setoid.is_partition.partition` 
* `finpartition.is_partition_parts`
Meanwhile add some lemmas related to `finset.sup` and `finset.inf` in data/finset/lattice.

### [2022-03-11 06:44:16](https://github.com/leanprover-community/mathlib/commit/115f8c7)
fix(probability): remove unused argument from `cond_cond_eq_cond_inter` ([#12583](https://github.com/leanprover-community/mathlib/pull/12583))
This was a property that we already derived within the proof itself from conditionable intersection (I think I forgot to remove this when I made the PR).

### [2022-03-11 06:44:15](https://github.com/leanprover-community/mathlib/commit/3061d18)
feat(data/nat/{nth,prime}): add facts about primes ([#12560](https://github.com/leanprover-community/mathlib/pull/12560))
Gives `{p | prime p}.infinite` as well as `infinite_of_not_bdd_above` lemma. Also gives simp lemmas for `prime_counting'`.

### [2022-03-11 06:44:14](https://github.com/leanprover-community/mathlib/commit/de4d14c)
feat(group_theory/commutator): Add some basic lemmas ([#12554](https://github.com/leanprover-community/mathlib/pull/12554))
This PR adds lemmas adds some basic lemmas about when the commutator is trivial.

### [2022-03-11 06:12:11](https://github.com/leanprover-community/mathlib/commit/355472d)
refactor(group_theory/commutator): Golf proof of `commutator_mem_commutator` ([#12584](https://github.com/leanprover-community/mathlib/pull/12584))
This PR golfs the proof of `commutator_mem_commutator`, and moves it earlier in the file so that it can be used earlier.

### [2022-03-11 02:38:57](https://github.com/leanprover-community/mathlib/commit/b5a26d0)
feat(data/list/basic): Lists over empty type are `unique` ([#12582](https://github.com/leanprover-community/mathlib/pull/12582))

### [2022-03-10 23:44:36](https://github.com/leanprover-community/mathlib/commit/f0dd6e9)
refactor(group_theory/commutator): Use commutators in `commutator_le` ([#12572](https://github.com/leanprover-community/mathlib/pull/12572))
This PR golfs the proof of `commutator_le`, and uses the new commutator notation.

### [2022-03-10 23:12:24](https://github.com/leanprover-community/mathlib/commit/6c04fcf)
refactor(group_theory/commutator): Use commutator notation in `commutator_normal` ([#12575](https://github.com/leanprover-community/mathlib/pull/12575))
This PR uses the new commutator notation in the proof of `commutator_normal`.

### [2022-03-10 21:17:59](https://github.com/leanprover-community/mathlib/commit/84cbbc9)
feat(algebra/group/to_additive + a few more files): make `to_additive` convert `unit` to `add_unit` ([#12564](https://github.com/leanprover-community/mathlib/pull/12564))
This likely involves removing names that match autogenerated names.

### [2022-03-10 19:33:06](https://github.com/leanprover-community/mathlib/commit/869ef84)
feat(data/zmod/basic): some lemmas about coercions ([#12571](https://github.com/leanprover-community/mathlib/pull/12571))
The names here are in line with `zmod.nat_coe_zmod_eq_zero_iff_dvd` and `zmod.int_coe_zmod_eq_zero_iff_dvd` a few lines above.

### [2022-03-10 19:33:05](https://github.com/leanprover-community/mathlib/commit/6fdb1d5)
chore(*): clear up some excessive by statements ([#12570](https://github.com/leanprover-community/mathlib/pull/12570))
Delete some `by` (and similar commands that do nothing, such as
- `by by blah`
- `by begin blah end`
- `{ by blah }`
- `begin { blah } end`
Also clean up the proof of `monic.map` and `nat_degree_div_by_monic` a bit.

### [2022-03-10 19:33:04](https://github.com/leanprover-community/mathlib/commit/45c22c0)
feat(field_theory/is_alg_closed/basic): add `is_alg_closed.infinite` ([#12566](https://github.com/leanprover-community/mathlib/pull/12566))
An algebraically closed field is infinite, because if it is finite then `x^(n+1) - 1` is a separable polynomial (where `n` is the cardinality of the field).

### [2022-03-10 19:33:02](https://github.com/leanprover-community/mathlib/commit/0e93816)
feat(tactic/norm_num_command): add user command to run norm_num on an expression ([#12550](https://github.com/leanprover-community/mathlib/pull/12550))
For example,
```
#norm_num 2^100 % 10
-- 6
```

### [2022-03-10 17:46:10](https://github.com/leanprover-community/mathlib/commit/f654a86)
chore(*): remove lines claiming to introduce variables ([#12569](https://github.com/leanprover-community/mathlib/pull/12569))
They don't.

### [2022-03-10 15:58:20](https://github.com/leanprover-community/mathlib/commit/4a59a4d)
chore(order/galois_connection): Make lifting instances reducible ([#12559](https://github.com/leanprover-community/mathlib/pull/12559))
and provide `infi₂` and `supr₂` versions of the lemmas.

### [2022-03-10 15:28:09](https://github.com/leanprover-community/mathlib/commit/788ccf0)
chore(cardinal_divisibility): tiny golf ([#12567](https://github.com/leanprover-community/mathlib/pull/12567))

### [2022-03-10 13:16:05](https://github.com/leanprover-community/mathlib/commit/cd111e9)
feat(data/equiv/mul_add): add to_additive attribute to `group.is_unit` ([#12563](https://github.com/leanprover-community/mathlib/pull/12563))
Unless something breaks, this PR does nothing else!

### [2022-03-10 10:38:55](https://github.com/leanprover-community/mathlib/commit/41f5c17)
chore(set_theory/ordinal_arithmetic): Make auxiliary result private ([#12562](https://github.com/leanprover-community/mathlib/pull/12562))

### [2022-03-10 10:08:31](https://github.com/leanprover-community/mathlib/commit/4048a9b)
chore(measure_theory/function/convergence_in_measure): golf proof with Borel-Cantelli ([#12551](https://github.com/leanprover-community/mathlib/pull/12551))

### [2022-03-10 09:02:58](https://github.com/leanprover-community/mathlib/commit/d56a9bc)
feat(set_theory/ordinal_arithmetic): `add_eq_zero_iff`, `mul_eq_zero_iff` ([#12561](https://github.com/leanprover-community/mathlib/pull/12561))

### [2022-03-10 09:02:56](https://github.com/leanprover-community/mathlib/commit/1e560a6)
refactor(group_theory/commutator): Generalize `map_commutator_element` ([#12555](https://github.com/leanprover-community/mathlib/pull/12555))
This PR generalizes `map_commutator_element` from `monoid_hom_class F G G` to `monoid_hom_class F G G'`.

### [2022-03-10 07:37:11](https://github.com/leanprover-community/mathlib/commit/24e3b5f)
refactor(topology/opens): Turn `opens.gi` into a Galois coinsertion ([#12547](https://github.com/leanprover-community/mathlib/pull/12547))
`topological_space.opens.gi` is currently a `galois_insertion` between `order_dual (opens α)` and `order_dual (set α)`. This turns it into the sensible thing, namely a `galois_coinsertion` between `opens α` and `set α`.

### [2022-03-10 07:37:10](https://github.com/leanprover-community/mathlib/commit/0fd9929)
feat(group_theory/double_cosets): definition of double cosets and some basic lemmas. ([#9490](https://github.com/leanprover-community/mathlib/pull/9490))
This contains the definition of double cosets and some basic lemmas about them, such as "the whole group is the disjoint union of its double cosets" and relationship to usual group quotients.

### [2022-03-10 06:34:47](https://github.com/leanprover-community/mathlib/commit/750ca95)
chore(linear_algebra/affine_space/affine_map): golf using the injective APIs ([#12543](https://github.com/leanprover-community/mathlib/pull/12543))
The extra whitespace means this isn't actually any shorter by number of lines, but it does eliminate 12 trivial proofs.
Again, the `has_scalar` instance has been hoisted from lower down the file, so that we have the `nat` and `int` actions available when we create the `add_comm_group` structure. Previously we just built the same `has_scalar` structure three times.

### [2022-03-10 06:34:46](https://github.com/leanprover-community/mathlib/commit/8836a42)
fix(linear_algebra/quadratic_form/basic): align diamonds in the nat- and int- action ([#12541](https://github.com/leanprover-community/mathlib/pull/12541))
This also provides `fun_like` and `zero_hom_class` instances.
The `has_scalar` code has been moved unchanged from further down in the file.
This change makes `coe_fn_sub` eligible for `dsimp`, since it can now be proved by `rfl`.

### [2022-03-10 06:34:44](https://github.com/leanprover-community/mathlib/commit/9e28852)
feat(field_theory/krull_topology): added krull_topology_totally_disconnected ([#12398](https://github.com/leanprover-community/mathlib/pull/12398))

### [2022-03-10 05:29:37](https://github.com/leanprover-community/mathlib/commit/bab039f)
feat(topology/opens): The frame of opens of a topological space ([#12546](https://github.com/leanprover-community/mathlib/pull/12546))
Provide the `frame` instance for `opens α` and strengthen `opens.comap` from `order_hom` to `frame_hom`.

### [2022-03-10 05:29:36](https://github.com/leanprover-community/mathlib/commit/9c2f6eb)
feat(category_theory/abelian/exact): `exact g.op f.op` ([#12456](https://github.com/leanprover-community/mathlib/pull/12456))
This pr is about `exact g.op f.op` from `exact f g` in an abelian category; this pr is taken from liquid tensor experiment. I believe the original author is @adamtopaz.

### [2022-03-10 04:56:21](https://github.com/leanprover-community/mathlib/commit/ef25c4c)
refactor(group_theory/commutator): Rename `commutator_containment` to `commutator_mem_commutator` ([#12553](https://github.com/leanprover-community/mathlib/pull/12553))
This PR renames `commutator_containment` to `commutator_mem_commutator`, uses the new commutator notation, and makes the subgroups implicit.

### [2022-03-09 13:59:57](https://github.com/leanprover-community/mathlib/commit/9facd19)
doc(combinatorics/simple_graph/basic): fix typo ([#12544](https://github.com/leanprover-community/mathlib/pull/12544))

### [2022-03-09 11:28:18](https://github.com/leanprover-community/mathlib/commit/0d6fb8a)
chore(analysis/complex/upper_half_plane): use `coe` instead of `coe_fn` ([#12532](https://github.com/leanprover-community/mathlib/pull/12532))
This matches the approach used by other files working with `special_linear_group`.

### [2022-03-09 11:28:17](https://github.com/leanprover-community/mathlib/commit/c4a3413)
chore(data/polynomial): use dot notation for monic lemmas ([#12530](https://github.com/leanprover-community/mathlib/pull/12530))
As discussed in [#12447](https://github.com/leanprover-community/mathlib/pull/12447)
- Use the notation throughout the library
- Also deleted `ne_zero_of_monic` as it was a duplicate of `monic.ne_zero` it seems.
- Cleaned up a small proof here and there too.

### [2022-03-09 09:05:27](https://github.com/leanprover-community/mathlib/commit/55d1f3e)
chore(set_theory/cardinal): `min` → `Inf` ([#12517](https://github.com/leanprover-community/mathlib/pull/12517))
Various definitions are awkwardly stated in terms of minima of subtypes. We instead rewrite them as infima and golf them. Further, we protect `cardinal.min` to avoid confusion with `linear_order.min`.

### [2022-03-09 05:46:45](https://github.com/leanprover-community/mathlib/commit/5d405e2)
chore(linear_algebra/alternating): golf using injective APIs ([#12536](https://github.com/leanprover-community/mathlib/pull/12536))
To do this, we have to move the has_scalar instance higher up in the file.

### [2022-03-09 05:46:44](https://github.com/leanprover-community/mathlib/commit/bc9dda8)
chore(algebra/module/linear_map): golf using injective APIs ([#12535](https://github.com/leanprover-community/mathlib/pull/12535))
To do this, we have to move the `has_scalar` instance higher up in the file.

### [2022-03-09 05:46:43](https://github.com/leanprover-community/mathlib/commit/94e9bb5)
chore(data/{finsupp,dfinsupp}/basic): use the injective APIs ([#12534](https://github.com/leanprover-community/mathlib/pull/12534))
This also fixes a scalar diamond in the `nat` and `int` actions on `dfinsupp`.
The diamond did not exist for `finsupp`.

### [2022-03-09 05:46:41](https://github.com/leanprover-community/mathlib/commit/b8d176e)
chore(real/cau_seq_completion): put class in Prop ([#12533](https://github.com/leanprover-community/mathlib/pull/12533))

### [2022-03-09 04:04:18](https://github.com/leanprover-community/mathlib/commit/1f6a2e9)
chore(scripts): update nolints.txt ([#12538](https://github.com/leanprover-community/mathlib/pull/12538))
I am happy to remove some nolints for you!

### [2022-03-09 00:50:46](https://github.com/leanprover-community/mathlib/commit/2a3ecad)
feat(data/equiv/basic): lemmas about composition with equivalences ([#10693](https://github.com/leanprover-community/mathlib/pull/10693))

### [2022-03-08 21:42:52](https://github.com/leanprover-community/mathlib/commit/d69cda1)
chore(order/well_founded_set): golf two proofs ([#12529](https://github.com/leanprover-community/mathlib/pull/12529))

### [2022-03-08 21:42:51](https://github.com/leanprover-community/mathlib/commit/709a3b7)
feat(set_theory/cardinal_ordinal): `#(list α) ≤ max ω (#α)` ([#12519](https://github.com/leanprover-community/mathlib/pull/12519))

### [2022-03-08 17:53:50](https://github.com/leanprover-community/mathlib/commit/feb24fb)
feat(topology/vector_bundle): direct sum of topological vector bundles ([#12512](https://github.com/leanprover-community/mathlib/pull/12512))

### [2022-03-08 17:53:49](https://github.com/leanprover-community/mathlib/commit/1d67b07)
feat(category_theory): cases in which (co)equalizers are split monos (epis) ([#12498](https://github.com/leanprover-community/mathlib/pull/12498))

### [2022-03-08 17:53:47](https://github.com/leanprover-community/mathlib/commit/b4572d1)
feat(algebra/order/hom/ring): Ordered ring isomorphisms ([#12158](https://github.com/leanprover-community/mathlib/pull/12158))
Define `order_ring_iso`, the type of ordered ring isomorphisms, along with its typeclass `order_ring_iso_class`.

### [2022-03-08 15:58:18](https://github.com/leanprover-community/mathlib/commit/4ad5c5a)
feat(data/finset/noncomm_prod): add noncomm_prod_commute ([#12521](https://github.com/leanprover-community/mathlib/pull/12521))
adding `list.prod_commute`, `multiset.noncomm_prod_commute` and
`finset.noncomm_prod_commute`.

### [2022-03-08 15:58:16](https://github.com/leanprover-community/mathlib/commit/fac5ffe)
feat(group_theory/subgroup/basic): disjoint_iff_mul_eq_one ([#12505](https://github.com/leanprover-community/mathlib/pull/12505))

### [2022-03-08 15:58:15](https://github.com/leanprover-community/mathlib/commit/1597e9a)
feat(set_theory/ordinal_arithmetic): prove `enum_ord_le_of_subset` ([#12199](https://github.com/leanprover-community/mathlib/pull/12199))
I also used this as an excuse to remove a trivial theorem and some awkward dot notation.

### [2022-03-08 14:29:38](https://github.com/leanprover-community/mathlib/commit/ab6a892)
feat(data/finset/noncomm_prod): add noncomm_prod_congr ([#12520](https://github.com/leanprover-community/mathlib/pull/12520))

### [2022-03-08 14:29:36](https://github.com/leanprover-community/mathlib/commit/c0ba4d6)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_comp_X_add_one_is_eisenstein_at ([#12447](https://github.com/leanprover-community/mathlib/pull/12447))
We add `cyclotomic_comp_X_add_one_is_eisenstein_at`: `(cyclotomic p ℤ).comp (X + 1)` is Eisenstein at `p`.
From flt-regular

### [2022-03-08 12:44:00](https://github.com/leanprover-community/mathlib/commit/94cbfad)
chore(algebra/*): move some lemmas about is_unit from associated.lean ([#12526](https://github.com/leanprover-community/mathlib/pull/12526))
There doesn't seem to be any reason for them to live there.

### [2022-03-08 12:43:59](https://github.com/leanprover-community/mathlib/commit/9c13d62)
feat(data/int/gcd): add gcd_pos_iff ([#12522](https://github.com/leanprover-community/mathlib/pull/12522))

### [2022-03-08 12:43:58](https://github.com/leanprover-community/mathlib/commit/6dd3249)
feat(set_theory/ordinal_arithmetic): `brange_const` ([#12483](https://github.com/leanprover-community/mathlib/pull/12483))
This is the `brange` analog to `set.range_const`.

### [2022-03-08 10:54:20](https://github.com/leanprover-community/mathlib/commit/0798037)
refactor(algebra/group/inj_surj): add npow and zpow to all definitions ([#12126](https://github.com/leanprover-community/mathlib/pull/12126))
Currently, we have a small handful of helpers to construct algebraic structures via pushforwards and pullbacks that preserve `has_pow` and `has_scalar` instances (added in [#10152](https://github.com/leanprover-community/mathlib/pull/10152) and [#10832](https://github.com/leanprover-community/mathlib/pull/10832)):
* `function.{inj,surj}ective.add_monoid_smul`
* `function.{inj,surj}ective.monoid_pow`
* `function.{inj,surj}ective.sub_neg_monoid_smul`
* `function.{inj,surj}ective.div_inv_monoid_smul`
* `function.{inj,surj}ective.add_group_smul`
* `function.{inj,surj}ective.group_pow`
Predating these, we have a very large collection of helpers that construct new `has_pow` and `has_scalar` instances, for all the above and also for every other one-argument algebraic structure (`comm_monoid`, `ring`, `linear_ordered_field`, ...).
This puts the user in an awkward position; either:
1. They are unaware of the complexity here, and use `add_monoid_smul` and `add_comm_monoid` within the same file, which create two nonequal scalar instances.
2. They use only the large collection, and don't get definitional control of `has_scalar` and `has_pow`, which can cause typeclass diamonds with generic `has_scalar` instances.
3. They use only the small handful of helpers (which requires remembering which ones are safe to use), and have to remember to manually construct `add_comm_monoid` as `{..add_comm_semigroup, ..add_monoid}`. If they screw up and construct it as `{..add_comm_semigroup, ..add_zero_class}`, then they're in the same position as (1) without knowing it.
This change converts every helper in the large collection to _also_ preserve scalar and power instances; as a result, these pullback and pushforward helpers once again no longer construct any new data.
As a result, all these helpers now take `nsmul`, `zsmul`, `npow`, and `zpow` arguments as necessary, to indicate that these operations are preserved by the function in question.
As a result of this change, all existing callers are now expected to have a `has_pow` or `has_scalar` implementation available ahead of time. In many cases the `has_scalar` instances already exist as a more general case, and maybe just need reordering within the file. Sometimes the general case of `has_scalar` is stated in a way that isn't general enough to describe `int` and `nat`. In these cases and the `has_pow` cases, we define new instance manually. Grepping reveals a rough summary of the new instances:
```lean
instance : has_pow (A 0) ℕ
instance has_nsmul : has_scalar ℕ (C ⟶ D)
instance has_zsmul : has_scalar ℤ (C ⟶ D)
instance has_nsmul : has_scalar ℕ (M →ₗ⁅R,L⁆ N)
instance has_zsmul : has_scalar ℤ (M →ₗ⁅R,L⁆ N)
instance has_nsmul : has_scalar ℕ {x : α // 0 ≤ x}
instance has_pow : α // 0 ≤ x} ℕ
instance : has_scalar R (ι →ᵇᵃ[I₀] M)
instance has_nat_scalar : has_scalar ℕ (normed_group_hom V₁ V₂)
instance has_int_scalar : has_scalar ℤ (normed_group_hom V₁ V₂)
instance : has_pow ℕ+ ℕ
instance subfield.has_zpow : has_pow s ℤ
instance has_nat_scalar : has_scalar ℕ (left_invariant_derivation I G)
instance has_int_scalar : has_scalar ℤ (left_invariant_derivation I G)
instance add_subgroup.has_nsmul : has_scalar ℕ H
instance subgroup.has_npow : has_pow H ℕ
instance add_subgroup.has_zsmul : has_scalar ℤ H
instance subgroup.has_zpow : has_pow H ℤ
instance add_submonoid.has_nsmul : has_scalar ℕ S
instance submonoid.has_pow : has_pow S ℕ
instance : has_pow (special_linear_group n R) ℕ
instance : has_pow (α →ₘ[μ] γ) ℕ
instance has_int_pow : has_pow (α →ₘ[μ] γ) ℤ
instance : div_inv_monoid (α →ₘ[μ] γ)
instance has_nat_pow : has_pow (α →ₛ β) ℕ
instance has_int_pow : has_pow (α →ₛ β) ℤ
instance has_nat_pow : has_pow (germ l G) ℕ
instance has_int_pow : has_pow (germ l G) ℤ
instance : has_scalar ℕ (fractional_ideal S P)
instance has_nat_scalar : has_scalar ℕ (𝕎 R)
instance has_int_scalar : has_scalar ℤ (𝕎 R)
instance has_nat_pow : has_pow (𝕎 R) ℕ
instance has_nat_scalar : has_scalar ℕ (truncated_witt_vector p n R)
instance has_int_scalar : has_scalar ℤ (truncated_witt_vector p n R)
instance has_nat_pow : has_pow (truncated_witt_vector p n R) ℕ
instance has_nat_scalar : has_scalar ℕ (α →ᵇ β)
instance has_int_scalar : has_scalar ℤ (α →ᵇ β)
instance has_nat_pow : has_pow (α →ᵇ R) ℕ
```

### [2022-03-08 08:31:06](https://github.com/leanprover-community/mathlib/commit/b4a7ad6)
chore(field_theory/laurent): drop unused 'have'. ([#12516](https://github.com/leanprover-community/mathlib/pull/12516))

### [2022-03-08 08:31:05](https://github.com/leanprover-community/mathlib/commit/dc093e9)
chore(combinatorics/configuration): don't use classical.some in a proof ([#12515](https://github.com/leanprover-community/mathlib/pull/12515))

### [2022-03-08 08:31:04](https://github.com/leanprover-community/mathlib/commit/ffa6e6d)
feat(set_theory/cardinal): `sum_le_sup_lift` ([#12513](https://github.com/leanprover-community/mathlib/pull/12513))
This is a universe-polymorphic version of `sum_le_sup`.

### [2022-03-08 08:31:03](https://github.com/leanprover-community/mathlib/commit/43cb3ff)
fix(ring_theory/ideal/operations): fix a name and dot notation ([#12507](https://github.com/leanprover-community/mathlib/pull/12507))

### [2022-03-08 08:31:02](https://github.com/leanprover-community/mathlib/commit/b2377ea)
feat(measure_theory/measure/finite_measure_weak_convergence): generalize scalar action ([#12503](https://github.com/leanprover-community/mathlib/pull/12503))
This means the smul lemmas also work for `nsmul`.

### [2022-03-08 08:31:00](https://github.com/leanprover-community/mathlib/commit/65095fe)
doc(order/succ_pred/basic): fix typo ([#12501](https://github.com/leanprover-community/mathlib/pull/12501))

### [2022-03-08 08:30:59](https://github.com/leanprover-community/mathlib/commit/47182da)
feat(algebra/group/to_additive): add to_additive doc string linter ([#12487](https://github.com/leanprover-community/mathlib/pull/12487))
it is an easy mistake to add a docstring to a lemma with `to_additive`
without also passing a string to `to_additive`. This linter checks for
that, and suggests to add a doc string when needed.

### [2022-03-08 08:30:58](https://github.com/leanprover-community/mathlib/commit/ccdcce1)
chore(set_theory/game/nim): General golfing ([#12471](https://github.com/leanprover-community/mathlib/pull/12471))
We make use of various relatively new theorems on ordinals to simplify various proofs, or otherwise clean up the file.

### [2022-03-08 08:30:57](https://github.com/leanprover-community/mathlib/commit/b3fba03)
feat(algebra/homology/homotopy) : `mk_coinductive` ([#12457](https://github.com/leanprover-community/mathlib/pull/12457))
`mk_coinductive` is the dual version of `mk_inductive` in the same file. `mk_inductive` is to build homotopy of chain complexes inductively and `mk_coinductive` is to build homotopy of cochain complexes inductively.

### [2022-03-08 07:26:43](https://github.com/leanprover-community/mathlib/commit/14997d0)
feat(analysis/normed_space): allow non-unital C^* rings ([#12327](https://github.com/leanprover-community/mathlib/pull/12327))

### [2022-03-08 06:08:39](https://github.com/leanprover-community/mathlib/commit/74746bd)
chore(counterexamples/canonically_ordered_comm_semiring_two_mul): golf ([#12504](https://github.com/leanprover-community/mathlib/pull/12504))

### [2022-03-07 22:59:51](https://github.com/leanprover-community/mathlib/commit/5f6d30e)
chore(*): move `has_scalar` instances before `add_comm_monoid` instances ([#12502](https://github.com/leanprover-community/mathlib/pull/12502))
This makes it easier for us to set `nsmul` and `zsmul` in future.

### [2022-03-07 21:31:06](https://github.com/leanprover-community/mathlib/commit/e409a90)
feat(measure_theory/integral/periodic.lean): add lemma `function.periodic.tendsto_at_bot_interval_integral_of_pos'` ([#12500](https://github.com/leanprover-community/mathlib/pull/12500))
Partner of `function.periodic.tendsto_at_top_interval_integral_of_pos'` (I probably should have included this in [#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.

### [2022-03-07 21:31:04](https://github.com/leanprover-community/mathlib/commit/390554d)
feat(ring_theory/coprime/basic): lemmas about multiplying by units ([#12480](https://github.com/leanprover-community/mathlib/pull/12480))

### [2022-03-07 21:31:03](https://github.com/leanprover-community/mathlib/commit/9728bd2)
chore(number_theory/number_field): golf `int.not_is_field` ([#12451](https://github.com/leanprover-community/mathlib/pull/12451))
Golfed proof of number_theory.number_field.int.not_is_field
Co-authored by: David Ang <dka31@cantab.ac.uk>
Co-authored by: Eric Rodriguez <ericrboidi@gmail.com>
Co-authored by: Violeta Hernández <vi.hdz.p@gmail.com>

### [2022-03-07 19:47:38](https://github.com/leanprover-community/mathlib/commit/1b4ee53)
feat(algebra/associated): add pow_not_prime ([#12493](https://github.com/leanprover-community/mathlib/pull/12493))

### [2022-03-07 19:47:36](https://github.com/leanprover-community/mathlib/commit/f28023e)
feat(measure_theory/function/uniform_integrable): Uniform integrability and Vitali convergence theorem ([#12408](https://github.com/leanprover-community/mathlib/pull/12408))
This PR defines uniform integrability (both in the measure theory sense as well as the probability theory sense) and proves the Vitali convergence theorem which establishes a relation between convergence in measure and uniform integrability with convergence in Lp.

### [2022-03-07 19:47:34](https://github.com/leanprover-community/mathlib/commit/1ee91a5)
feat(probability_theory/stopping): define progressively measurable processes ([#11350](https://github.com/leanprover-community/mathlib/pull/11350))
* Define progressively measurable processes (`prog_measurable`), which is the correct strengthening of `adapted` to get that the stopped process is also progressively measurable.
* Prove that an adapted continuous process is progressively measurable.
For discrete time processes, progressively measurable is equivalent to `adapted` .
This PR also changes some measurable_space arguments in `measurable_space.lean` from typeclass arguments to implicit.

### [2022-03-07 18:31:04](https://github.com/leanprover-community/mathlib/commit/e871be2)
feat(data/real/nnreal): floor_semiring instance ([#12495](https://github.com/leanprover-community/mathlib/pull/12495))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60nat.2Eceil.60.20on.20.60nnreal.60.20.3F/near/274353230)

### [2022-03-07 18:31:03](https://github.com/leanprover-community/mathlib/commit/8d2ffb8)
feat(category_theory): (co)kernels of biproduct projection and inclusion ([#12394](https://github.com/leanprover-community/mathlib/pull/12394))
add kernels and cokernels of biproduct projections and inclusions

### [2022-03-07 18:01:16](https://github.com/leanprover-community/mathlib/commit/85a415e)
docs(overview): Add overview of model theory ([#12496](https://github.com/leanprover-community/mathlib/pull/12496))
Adds a subsection on model theory to the mathlib overview.

### [2022-03-07 16:01:41](https://github.com/leanprover-community/mathlib/commit/3c3c3bc)
fix(tactic/interactive): use non-interactive admit tactic ([#12489](https://github.com/leanprover-community/mathlib/pull/12489))
In a future release of Lean 3, the interactive admit tactic will take an additional argument.

### [2022-03-07 16:01:39](https://github.com/leanprover-community/mathlib/commit/5f2a6ac)
feat(measure_theory/integral/periodic): further properties of periodic integrals ([#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.

### [2022-03-07 16:01:38](https://github.com/leanprover-community/mathlib/commit/c95ce52)
fix(number_theory/modular): prefer `coe` over `coe_fn` in lemma statements ([#12445](https://github.com/leanprover-community/mathlib/pull/12445))
This file is already full of `↑ₘ`s (aka coercions to matrix), we may as well use them uniformly.

### [2022-03-07 14:11:59](https://github.com/leanprover-community/mathlib/commit/f451e09)
chore(algebra/order/{group,monoid}): trivial lemma about arithmetic on `with_top` and `with_bot` ([#12491](https://github.com/leanprover-community/mathlib/pull/12491))

### [2022-03-07 14:11:57](https://github.com/leanprover-community/mathlib/commit/65ac316)
chore(algebra/order/nonneg): add `nonneg.coe_nat_cast` ([#12490](https://github.com/leanprover-community/mathlib/pull/12490))

### [2022-03-07 14:11:56](https://github.com/leanprover-community/mathlib/commit/16b6766)
feat(analysis/normed_space): non-unital normed rings ([#12326](https://github.com/leanprover-community/mathlib/pull/12326))
On the way to allowing non-unital C^*-algebras.

### [2022-03-07 14:11:55](https://github.com/leanprover-community/mathlib/commit/9ed4366)
feat(category_theory/limits): limit preservation properties of functor.left_op and similar ([#12168](https://github.com/leanprover-community/mathlib/pull/12168))

### [2022-03-07 12:17:08](https://github.com/leanprover-community/mathlib/commit/900ce6f)
chore(data/equiv/basic): rename `involutive.to_equiv` to `to_perm` ([#12486](https://github.com/leanprover-community/mathlib/pull/12486))

### [2022-03-07 10:15:48](https://github.com/leanprover-community/mathlib/commit/eb46e7e)
feat(algebra/group/to_additive): let to_additive turn `pow` into `nsmul` ([#12477](https://github.com/leanprover-community/mathlib/pull/12477))
The naming convention for `npow` in lemma names is `pow`, so let’s teach
`to_additive` about it.
A fair number of lemmas now no longer need an explicit additive name.

### [2022-03-07 10:15:47](https://github.com/leanprover-community/mathlib/commit/d704f27)
refactor(set_theory/*): `o.out.r` → `<` ([#12468](https://github.com/leanprover-community/mathlib/pull/12468))
We declare a `linear_order` instance on `o.out.α`, for `o : ordinal`, with `<` def-eq to `o.out.r`. This will improve code clarity and will allow us to state theorems about specific ordinals as ordered structures.

### [2022-03-07 10:15:46](https://github.com/leanprover-community/mathlib/commit/9dd8ec1)
feat(analysis/normed/group/hom): add a module instance ([#12465](https://github.com/leanprover-community/mathlib/pull/12465))

### [2022-03-07 10:15:45](https://github.com/leanprover-community/mathlib/commit/0b86bb8)
feat(measure_theory/group/arithmetic): actions by int and nat are measurable ([#12464](https://github.com/leanprover-community/mathlib/pull/12464))
The `has_measurable_smul₂` proofs are essentially copied from the analogous proofs for `has_measurable_pow`, after golfing them.

### [2022-03-07 10:15:43](https://github.com/leanprover-community/mathlib/commit/3f353db)
feat(data/nat/basic): add one_le_div_iff ([#12461](https://github.com/leanprover-community/mathlib/pull/12461))
Couldn't find these.

### [2022-03-07 10:15:42](https://github.com/leanprover-community/mathlib/commit/2675b5c)
feat(measure_theory/constructions/polish): injective images of Borel sets in Polish spaces are Borel ([#12448](https://github.com/leanprover-community/mathlib/pull/12448))
We prove several fundamental results on the Borel sigma-algebra in Polish spaces, notably:
* Lusin separation theorem: disjoint analytic sets can be separated via Borel sets
* Lusin-Souslin theorem: a continuous injective image of a Borel set in a Polish space is Borel
* An injective measurable map on a Polish space is a measurable embedding, i.e., it maps measurable sets to measurable sets

### [2022-03-07 10:15:41](https://github.com/leanprover-community/mathlib/commit/3778353)
feat(set_theory/ordinal_arithmetic): `enum_ord univ = id` ([#12391](https://github.com/leanprover-community/mathlib/pull/12391))

### [2022-03-07 10:15:40](https://github.com/leanprover-community/mathlib/commit/313f405)
feat(category_theory/*): preserves biproducts implies additive ([#12014](https://github.com/leanprover-community/mathlib/pull/12014))

### [2022-03-07 10:15:38](https://github.com/leanprover-community/mathlib/commit/f063d0c)
feat(geometry/manifold/tangent_bundle): the `tangent_bundle` is a `topological_vector_bundle` ([#8295](https://github.com/leanprover-community/mathlib/pull/8295))

### [2022-03-07 08:10:23](https://github.com/leanprover-community/mathlib/commit/a19f6c6)
doc(algebra/group/to_additive): `to_additive` and docstring interaction ([#12476](https://github.com/leanprover-community/mathlib/pull/12476))

### [2022-03-06 21:54:59](https://github.com/leanprover-community/mathlib/commit/92ef3c5)
feat(ring_theory/graded_algebra/radical) : radical of homogeneous ideal is homogeneous ([#12277](https://github.com/leanprover-community/mathlib/pull/12277))
This pr contains the following results about homogeneous ideals.
* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
   `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
   homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
   `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
   radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal 𝒜`, `I.radical` is the the
   radical of `I` as a `homogeneous_ideal 𝒜`

### [2022-03-06 18:41:38](https://github.com/leanprover-community/mathlib/commit/40602e6)
chore(set_theory/cardinal_divisibility): add instance unique (units cardinal) ([#12458](https://github.com/leanprover-community/mathlib/pull/12458))

### [2022-03-06 15:36:29](https://github.com/leanprover-community/mathlib/commit/6696187)
chore(set_theory/ordinal_arithmetic): Reorder theorems ([#12475](https://github.com/leanprover-community/mathlib/pull/12475))
It makes more sense for `is_normal.bsup_eq` and `is_normal.blsub_eq` to be together.

### [2022-03-06 15:06:27](https://github.com/leanprover-community/mathlib/commit/0a6efe0)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a star normal element is its norm ([#12249](https://github.com/leanprover-community/mathlib/pull/12249))
In a C⋆-algebra over ℂ, the spectral radius of any star normal element is its norm. This extends the corresponding result for selfadjoint elements.
- [x] depends on: [#12211](https://github.com/leanprover-community/mathlib/pull/12211) 
- [x] depends on: [#11991](https://github.com/leanprover-community/mathlib/pull/11991)

### [2022-03-06 11:52:53](https://github.com/leanprover-community/mathlib/commit/28c902d)
fix(algebra/group/pi): Fix apply-simp-lemmas for monoid_hom.single ([#12474](https://github.com/leanprover-community/mathlib/pull/12474))
so that the simp-normal form really is `pi.mul_single`.
While adjusting related lemmas in `group_theory.subgroup.basic`, add a
few missing `to_additive` attributes.

### [2022-03-06 07:44:42](https://github.com/leanprover-community/mathlib/commit/64d953a)
refactor(set_theory/ordinal): `enum_lt` → `enum_lt_enum` ([#12469](https://github.com/leanprover-community/mathlib/pull/12469))
That way, the theorem name matches that of `enum_le_enum`, `typein_lt_typein`, and `typein_le_typein`.

### [2022-03-06 07:44:41](https://github.com/leanprover-community/mathlib/commit/d61ebab)
feat(category_theory/abelian): (co)kernels in terms of exact sequences ([#12460](https://github.com/leanprover-community/mathlib/pull/12460))

### [2022-03-06 07:44:40](https://github.com/leanprover-community/mathlib/commit/b7808a9)
chore(set_theory/ordinal_arithmetic): Golf `lsub_typein` and `blsub_id` ([#12203](https://github.com/leanprover-community/mathlib/pull/12203))

### [2022-03-06 07:44:39](https://github.com/leanprover-community/mathlib/commit/b4d007f)
feat(category_theory/limits): transport is_limit along F.left_op and similar ([#12166](https://github.com/leanprover-community/mathlib/pull/12166))

### [2022-03-06 07:44:38](https://github.com/leanprover-community/mathlib/commit/371b48a)
feal(category_theory/bicategory/functor): define pseudofunctors ([#11992](https://github.com/leanprover-community/mathlib/pull/11992))
This PR defines pseudofunctors between bicategories. 
We provide two constructors (`mk_of_oplax` and `mk_of_oplax'`) that construct pseudofunctors from oplax functors whose `map_id` and `map_comp` are isomorphisms. The constructor `mk_of_oplax` uses `iso` to describe isomorphisms, while `mk_of_oplax'` uses `is_iso`.

### [2022-03-06 07:11:07](https://github.com/leanprover-community/mathlib/commit/62e7d35)
feat(category_theory/limits): uniqueness of preadditive structures ([#12342](https://github.com/leanprover-community/mathlib/pull/12342))

### [2022-03-05 17:38:12](https://github.com/leanprover-community/mathlib/commit/974d23c)
feat(data/polynomial/monic): add monic_of_mul_monic_left/right ([#12446](https://github.com/leanprover-community/mathlib/pull/12446))
Also clean up variables that are defined in the section.
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60geom_sum.20.28X.20.20n.29.60.20is.20monic/near/274130839

### [2022-03-05 16:13:55](https://github.com/leanprover-community/mathlib/commit/e542154)
feat(category_theory/full_subcategory): full_subcategory.map and full_subcategory.lift ([#12335](https://github.com/leanprover-community/mathlib/pull/12335))

### [2022-03-05 16:13:54](https://github.com/leanprover-community/mathlib/commit/51adf3a)
feat(model_theory/terms_and_formulas): Using a list encoding, bounds the number of terms ([#12276](https://github.com/leanprover-community/mathlib/pull/12276))
Defines `term.list_encode` and `term.list_decode`, which turn terms into lists, and reads off lists as lists of terms.
Bounds the number of terms by the number of allowed symbols + omega.

### [2022-03-05 15:19:46](https://github.com/leanprover-community/mathlib/commit/92b27e1)
feat(category_theory/discrete_category): generalize universes for comp_nat_iso_discrete ([#12340](https://github.com/leanprover-community/mathlib/pull/12340))

### [2022-03-05 15:19:45](https://github.com/leanprover-community/mathlib/commit/4ecd92a)
feat(category_theory/abelian): faithful functors reflect exact sequences ([#12071](https://github.com/leanprover-community/mathlib/pull/12071))

### [2022-03-05 13:15:02](https://github.com/leanprover-community/mathlib/commit/fa6b16e)
feat(data/nat/prime): add nat.eq_two_pow_or_exists_odd_prime_and_dvd ([#12395](https://github.com/leanprover-community/mathlib/pull/12395))

### [2022-03-05 13:15:01](https://github.com/leanprover-community/mathlib/commit/8b91390)
feat(order/hom/basic): add `order_iso.with_{top,bot}_congr` ([#12264](https://github.com/leanprover-community/mathlib/pull/12264))
This adds:
* `with_bot.to_dual_top`
* `with_top.to_dual_bot`
* `order_iso.with_top_congr`
* `order_iso.with_bot_congr`

### [2022-03-05 12:17:39](https://github.com/leanprover-community/mathlib/commit/2840532)
doc(topology/uniform_space/cauchy): fix typo ([#12453](https://github.com/leanprover-community/mathlib/pull/12453))

### [2022-03-05 10:56:08](https://github.com/leanprover-community/mathlib/commit/bda091d)
feat(measure_theory/card_measurable_space): cardinality of generated sigma-algebras ([#12422](https://github.com/leanprover-community/mathlib/pull/12422))
If a sigma-algebra is generated by a set of sets `s` whose cardinality is at most the continuum,
then the sigma-algebra satisfies the same cardinality bound.

### [2022-03-05 09:10:31](https://github.com/leanprover-community/mathlib/commit/93451af)
feat(order/category/BoolAlg): The category of Boolean algebras ([#12452](https://github.com/leanprover-community/mathlib/pull/12452))
Define `BoolAlg`, the category of Boolean algebras with bounded lattice homs.

### [2022-03-05 09:10:30](https://github.com/leanprover-community/mathlib/commit/f5b885b)
feat(linear_algebra/clifford_algebra/conjugation): reverse and involute are grade-preserving ([#12373](https://github.com/leanprover-community/mathlib/pull/12373))
This shows that various submodules are preserved under `submodule.map` by `reverse` or `involute`.

### [2022-03-05 08:41:18](https://github.com/leanprover-community/mathlib/commit/ac28ddf)
feat(data/nat/fib): add bit0/bit1 lemmas and fast_fib ([#12444](https://github.com/leanprover-community/mathlib/pull/12444))
This provides lemmas that let `simp` calculate `fib` from the bit0/bit1 numeral representation. (This isn't intended to be for speed, although it does evaluate things reasonably quick.)
```lean
lemma foo : fib 64 = 10610209857723 :=
begin
  norm_num [fib_bit0, fib_bit1, fib_bit0_succ, fib_bit1_succ],
end
```
These are then used to show that `fast_fib` computes `fib`.

### [2022-03-05 06:05:25](https://github.com/leanprover-community/mathlib/commit/36a528d)
feat(set_theory/ordinal_arithmetic): `add_le_of_forall_add_lt` ([#12315](https://github.com/leanprover-community/mathlib/pull/12315))

### [2022-03-05 03:06:09](https://github.com/leanprover-community/mathlib/commit/b0d9462)
feat(category_theory/preadditive/injective) : more basic properties and morphisms about injective objects ([#12450](https://github.com/leanprover-community/mathlib/pull/12450))
This pr dualises the rest of `projective.lean`

### [2022-03-05 03:06:08](https://github.com/leanprover-community/mathlib/commit/fdf43f1)
feat(category_theory/closed): generalize some material from cartesian closed categories to closed monoidal categories ([#12386](https://github.com/leanprover-community/mathlib/pull/12386))
No new content, just moving some trivially generalisable material about cartesian closed categories to closed monoidal categories.
I've defined `ihom` for internal hom, and made `exp` an abbreviation for it in the cartesian closed case.
A few other definitions similarly become abbreviations.
I've left the `⟹` arrow for the internal hom in the cartesian closed case, and added `⟶[C]` for the general internal hom.

### [2022-03-05 01:51:47](https://github.com/leanprover-community/mathlib/commit/45d235e)
feat(analysis/normed_space/star/matrix): `entrywise_sup_norm_bound_of_unitary` ([#12255](https://github.com/leanprover-community/mathlib/pull/12255))
The entrywise sup norm of a unitary matrix is at most 1.
I suspect there is a simpler proof!

### [2022-03-05 01:51:46](https://github.com/leanprover-community/mathlib/commit/1755911)
feat(topology/compacts): The types of clopens and of compact opens ([#11966](https://github.com/leanprover-community/mathlib/pull/11966))
Define `clopens` and ` compact_opens`, the types of clopens and of compact open sets of a topological space.

### [2022-03-05 00:00:54](https://github.com/leanprover-community/mathlib/commit/8e1da4e)
feat(ring_theory/adjoin/basic): if a set of elements of a subobject commute, its closure/adjoin is also commutative ([#12231](https://github.com/leanprover-community/mathlib/pull/12231))
We show that if a set of elements of a subobject commute, its closure/adjoin is also commutative The subobjects include (additive) submonoids, (additive) subgroups, subsemirings, subrings, and subalgebras.

### [2022-03-04 21:44:21](https://github.com/leanprover-community/mathlib/commit/3ac971b)
feat(order/category/Frame): The category of frames ([#12363](https://github.com/leanprover-community/mathlib/pull/12363))
Define `Frame`, the category of frames with frame homomorphisms.

### [2022-03-04 21:44:20](https://github.com/leanprover-community/mathlib/commit/ee4be2d)
feat(ring_theory/simple_module): Simple modules as simple objects in the Module category ([#11927](https://github.com/leanprover-community/mathlib/pull/11927))
A simple module is a simple object in the Module category. 
From there it should be easy to write an alternative proof of Schur's lemma for modules using category theory (using the work already done in category_theory/preadditive/schur.lean).
The other direction (a simple object in the Module category is a simple module) hasn't been proved yet.

### [2022-03-04 21:44:19](https://github.com/leanprover-community/mathlib/commit/a07cf6b)
feat(ring_theory/polynomial/homogeneous) : add lemma `homogeneous_component_homogeneous_polynomial` ([#10113](https://github.com/leanprover-community/mathlib/pull/10113))
add the following lemma
```lean
lemma homogeneous_component_homogeneous_polynomial (m n : ℕ)
  (p : mv_polynomial σ R) (h : p ∈ homogeneous_submodule σ R n) :
  homogeneous_component m p = if m = n then p else 0
```

### [2022-03-04 19:43:16](https://github.com/leanprover-community/mathlib/commit/34d8ff1)
feat(topology/algebra/weak_dual): generalize to weak topologies for arbitrary dualities ([#12284](https://github.com/leanprover-community/mathlib/pull/12284))

### [2022-03-04 19:43:15](https://github.com/leanprover-community/mathlib/commit/89654c0)
feat(data/equiv/{mul_add,ring}): Coercions to types of morphisms from their `_class` ([#12243](https://github.com/leanprover-community/mathlib/pull/12243))
Add missing coercions to `α ≃+ β`, `α ≃* β`, `α ≃+* β` from `add_equiv_class`, `mul_equiv_class`, `ring_equiv_class`.

### [2022-03-04 17:34:12](https://github.com/leanprover-community/mathlib/commit/30d63cd)
feat(field_theory/cardinality): a cardinal can have a field structure iff it is a prime power ([#12442](https://github.com/leanprover-community/mathlib/pull/12442))

### [2022-03-04 17:34:11](https://github.com/leanprover-community/mathlib/commit/858002b)
feat(algebra/char_zero): cast(_pow)_eq_one ([#12429](https://github.com/leanprover-community/mathlib/pull/12429))

### [2022-03-04 17:34:10](https://github.com/leanprover-community/mathlib/commit/a54dd9e)
feat(order/category/BoundedDistribLattice): The category of bounded distributive lattices ([#12347](https://github.com/leanprover-community/mathlib/pull/12347))
Define `BoundedDistribLattice`, the category of bounded distributive lattices with bounded lattice homomorphisms.

### [2022-03-04 17:34:09](https://github.com/leanprover-community/mathlib/commit/fab59cb)
feat(set_theory/cofinality): `cof_eq_Inf_lsub` ([#12314](https://github.com/leanprover-community/mathlib/pull/12314))
This much nicer characterization of cofinality will allow us to prove various theorems relating it to `lsub` and `blsub`.

### [2022-03-04 17:34:07](https://github.com/leanprover-community/mathlib/commit/efd9a16)
refactor(group_theory/commutator): Define commutators of subgroups in terms of commutators of elements ([#12309](https://github.com/leanprover-community/mathlib/pull/12309))
This PR defines commutators of elements of groups.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)

### [2022-03-04 17:34:06](https://github.com/leanprover-community/mathlib/commit/35b835a)
feat(data/set/sigma): Indexed sum of sets ([#12305](https://github.com/leanprover-community/mathlib/pull/12305))
Define `set.sigma`, the sum of a family of sets indexed by a set.

### [2022-03-04 17:34:05](https://github.com/leanprover-community/mathlib/commit/ed63386)
feat(category_theory/preadditive/injective) : definition of injective objects in a category ([#11921](https://github.com/leanprover-community/mathlib/pull/11921))
This pr contains definition of injective objects and some useful instances.

### [2022-03-04 17:34:04](https://github.com/leanprover-community/mathlib/commit/a8629a5)
refactor(tactic/interactive): use 1-indexing in work_on_goal ([#11813](https://github.com/leanprover-community/mathlib/pull/11813))
Backporting the change in https://github.com/leanprover-community/mathlib4/pull/178 to make `work_on_goal` 1-indexed. See also: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60work_on_goal.60.20vs.20.60swap.60

### [2022-03-04 15:24:38](https://github.com/leanprover-community/mathlib/commit/0ec8e6a)
feat(algebra/algebra/operations): more lemmas about `mul_opposite` ([#12441](https://github.com/leanprover-community/mathlib/pull/12441))
Naturally the lemmas I left out of the previous PR, notably `map_unop_mul` and `map_unop_pow`, are the ones I actually needed.
This also improves the `simps` lemmas on `submodule.equiv_opposite`, which were previously garbage as `simps` didn't unfold `ring_equiv.symm` properly. At any rate, the only reason it was defined that way was because the lemmas in this PR were missing.

### [2022-03-04 15:24:37](https://github.com/leanprover-community/mathlib/commit/31cb3c1)
chore(algebra/group_with_zero/basic): generalize `units.exists_iff_ne_zero` to arbitrary propositions ([#12439](https://github.com/leanprover-community/mathlib/pull/12439))
This adds a more powerful version of this lemma that allows an existential to be replaced with one over the underlying group with zero.
The naming matches `subtype.exists` and `subtype.exists'`, while the trailing zero matches `units.mk0`.

### [2022-03-04 15:24:36](https://github.com/leanprover-community/mathlib/commit/6e94c53)
feat(complex/basic): nnnorm coercions ([#12428](https://github.com/leanprover-community/mathlib/pull/12428))

### [2022-03-04 15:24:34](https://github.com/leanprover-community/mathlib/commit/dc95d02)
feat(order/filter/archimedean): add lemmas about convergence to ±∞ for archimedean rings / groups. ([#12427](https://github.com/leanprover-community/mathlib/pull/12427))
Formalized as part of the Sphere Eversion project.

### [2022-03-04 15:24:33](https://github.com/leanprover-community/mathlib/commit/e41303d)
feat(category_theory/limits/shapes): preserving (co)kernels ([#12419](https://github.com/leanprover-community/mathlib/pull/12419))
This is work towards showing that homology is a lax monoidal functor.

### [2022-03-04 14:03:56](https://github.com/leanprover-community/mathlib/commit/2d6c52a)
feat(topology/metric_space/polish): definition and basic properties of polish spaces ([#12437](https://github.com/leanprover-community/mathlib/pull/12437))
A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this PR, we establish basic (and not so basic) properties of Polish spaces.

### [2022-03-04 14:03:54](https://github.com/leanprover-community/mathlib/commit/0a3d144)
chore(topology/algebra/uniform_mul_action): add `has_uniform_continuous_const_smul.op` ([#12434](https://github.com/leanprover-community/mathlib/pull/12434))
This matches `has_continuous_const_smul.op` and other similar lemmas.
With this in place, we can state `is_central_scalar` on `completion`s.

### [2022-03-04 14:03:53](https://github.com/leanprover-community/mathlib/commit/cac9242)
chore(analysis/complex/basic): golf `norm_rat/int/int_of_nonneg` ([#12433](https://github.com/leanprover-community/mathlib/pull/12433))
While looking at PR [#12428](https://github.com/leanprover-community/mathlib/pull/12428), I found some easy golfing of some lemmas (featuring my first-ever use of `single_pass`! :smile: ).

### [2022-03-04 14:03:51](https://github.com/leanprover-community/mathlib/commit/173f161)
feat(set_theory/ordinal_arithmetic): `bsup` / `blsub` of function composition ([#12381](https://github.com/leanprover-community/mathlib/pull/12381))

### [2022-03-04 12:39:06](https://github.com/leanprover-community/mathlib/commit/a721700)
chore(algebra/algebra/operations): add missing `@[elab_as_eliminator]` on recursors ([#12440](https://github.com/leanprover-community/mathlib/pull/12440))
`refine submodule.pow_induction_on' _ _ _ _ h` struggles without this attribute

### [2022-03-04 12:39:04](https://github.com/leanprover-community/mathlib/commit/4a416bc)
feat(set_theory/ordinal_arithmetic): `is_normal.blsub_eq` ([#12379](https://github.com/leanprover-community/mathlib/pull/12379))

### [2022-03-04 12:39:03](https://github.com/leanprover-community/mathlib/commit/b144460)
feat(number_theory/cyclotomic/primitive_roots): generalize norm_eq_one ([#12359](https://github.com/leanprover-community/mathlib/pull/12359))
We generalize `norm_eq_one`, that now computes the norm of any primitive `n`-th root of unity if `n ≠ 2`. We modify the assumption, that is still verified in the main case of interest `K = ℚ`.
From flt-regular

### [2022-03-04 12:39:02](https://github.com/leanprover-community/mathlib/commit/53dc7ca)
feat(linear_algebra/basic): some basic lemmas about dfinsupp.sum ([#12214](https://github.com/leanprover-community/mathlib/pull/12214))
Two basic lemmas about dfinsupp.sum that could be useful (I needed them for another project)

### [2022-03-04 09:26:44](https://github.com/leanprover-community/mathlib/commit/052d027)
refactor(algebra/category/Group/basic): Avoid data shuffle in `mul_equiv.to_Group_iso` ([#12407](https://github.com/leanprover-community/mathlib/pull/12407))
Change the definition of `mul_equiv.to_Group_iso` from `{X Y : Type*} [group X] [group Y] (e : X ≃* Y) : Group.of X ≅ Group.of Y` to `{X Y : Group} (e : X ≃* Y) : X ≅ Y`. Not making `X` and `Y` into `Group`s on the fly avoids rebundling them when they already are `Group`s, which breaks definitional equality.

### [2022-03-04 09:26:43](https://github.com/leanprover-community/mathlib/commit/0666dd5)
feat(order/bounded): The universal set is unbounded ([#12390](https://github.com/leanprover-community/mathlib/pull/12390))

### [2022-03-04 09:26:42](https://github.com/leanprover-community/mathlib/commit/09c66fa)
feat(counterexamples/seminorm_lattice_not_distrib): The lattice of seminorms is not distributive. ([#12099](https://github.com/leanprover-community/mathlib/pull/12099))
A counterexample showing the lattice of seminorms is not distributive

### [2022-03-04 08:56:10](https://github.com/leanprover-community/mathlib/commit/82a142d)
feat(algebra/category): Module R is monoidal closed for comm_ring R ([#12387](https://github.com/leanprover-community/mathlib/pull/12387))

### [2022-03-04 07:06:13](https://github.com/leanprover-community/mathlib/commit/e96cf5e)
feat(data/nat/gcd): add coprime_prod_left and coprime_prod_right ([#12268](https://github.com/leanprover-community/mathlib/pull/12268))

### [2022-03-03 23:56:18](https://github.com/leanprover-community/mathlib/commit/40524f1)
feat(algebra/star/self_adjoint): define normal elements of a star monoid ([#11991](https://github.com/leanprover-community/mathlib/pull/11991))
In this PR, we define the normal elements of a star monoid, i.e. those elements `x`
that commute with `star x`. This is defined as the prop type class `is_star_normal`.
This was formalized as part of the semilinear maps paper.

### [2022-03-03 23:15:44](https://github.com/leanprover-community/mathlib/commit/544f45b)
refactor(linear_algebra/bilinear_form): split off matrix part ([#12435](https://github.com/leanprover-community/mathlib/pull/12435))
The bilinear form file is way too large. The part that concerns matrices is not depended on by the general theory, and belongs in its own file.

### [2022-03-03 21:32:01](https://github.com/leanprover-community/mathlib/commit/5371338)
feat(group_theory/torsion): all torsion monoids are groups ([#12432](https://github.com/leanprover-community/mathlib/pull/12432))

### [2022-03-03 21:32:00](https://github.com/leanprover-community/mathlib/commit/1af53ff)
feat(polynomial/cyclotomic): some divisibility results ([#12426](https://github.com/leanprover-community/mathlib/pull/12426))

### [2022-03-03 21:31:59](https://github.com/leanprover-community/mathlib/commit/54c286d)
feat(data/{nat,int,rat}/cast, algebra/star/basic): lemmas about `star` on casts ([#12418](https://github.com/leanprover-community/mathlib/pull/12418))
This also includes lemmas about `mul_opposite` on casts which are used to prove the star lemmas. The new lemmas are:
* `star_nat_cast`
* `star_int_cast`
* `star_rat_cast`
* `op_nat_cast`
* `op_int_cast`
* `op_rat_cast`
* `unop_nat_cast`
* `unop_int_cast`
* `unop_rat_cast`

### [2022-03-03 21:31:57](https://github.com/leanprover-community/mathlib/commit/9deac65)
feat(ring_theory/ideal): more lemmas on ideals multiplied with submodules ([#12401](https://github.com/leanprover-community/mathlib/pull/12401))
These are, like [#12178](https://github.com/leanprover-community/mathlib/pull/12178), split off from [#12287](https://github.com/leanprover-community/mathlib/pull/12287)

### [2022-03-03 21:31:56](https://github.com/leanprover-community/mathlib/commit/2fc2d1b)
feat(linear_algebra/clifford_algebra): lemmas about mapping submodules ([#12399](https://github.com/leanprover-community/mathlib/pull/12399))

### [2022-03-03 21:31:55](https://github.com/leanprover-community/mathlib/commit/e84c1a9)
chore(linear_algebra/general_linear_group): replace coe_fn with coe in lemma statements ([#12397](https://github.com/leanprover-community/mathlib/pull/12397))
This way, all the lemmas are expressed in terms of `↑` and not `⇑`.
This matches the approach used in `special_linear_group`.

### [2022-03-03 21:31:54](https://github.com/leanprover-community/mathlib/commit/4503732)
feat(field_theory/cardinality): cardinality of fields & localizations ([#12285](https://github.com/leanprover-community/mathlib/pull/12285))

### [2022-03-03 21:31:52](https://github.com/leanprover-community/mathlib/commit/2c0fa82)
feat(group_theory/free_product): the 🏓-lemma ([#12210](https://github.com/leanprover-community/mathlib/pull/12210))
The Ping-Pong-Lemma.
If a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the free product of the `H i`.
Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group; we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be generated by the images.
Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.

### [2022-03-03 21:31:51](https://github.com/leanprover-community/mathlib/commit/f549c10)
feat(set_theory/cardinal_divisibility): add lemmas about divisibility in the cardinals ([#12197](https://github.com/leanprover-community/mathlib/pull/12197))

### [2022-03-03 21:31:50](https://github.com/leanprover-community/mathlib/commit/2a05bb3)
feat(ring_theory/witt_vector): classify 1d isocrystals ([#12041](https://github.com/leanprover-community/mathlib/pull/12041))
To show an application of semilinear maps that are not linear or conjugate-linear, we formalized the one-dimensional version of a theorem by Dieudonné and Manin classifying the isocrystals over an algebraically closed field with positive characteristic. This work is described in a recent draft from @dupuisf , @hrmacbeth , and myself: https://arxiv.org/abs/2202.05360

### [2022-03-03 19:28:04](https://github.com/leanprover-community/mathlib/commit/066ffdb)
chore(algebra/*): provide `non_assoc_ring` instances ([#12414](https://github.com/leanprover-community/mathlib/pull/12414))

### [2022-03-03 19:28:03](https://github.com/leanprover-community/mathlib/commit/5d0960b)
feat(data/int/basic): add three lemmas about ints, nats and int_nat_abs ([#12380](https://github.com/leanprover-community/mathlib/pull/12380))
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/int.2Eto_nat_eq_zero)

### [2022-03-03 19:28:02](https://github.com/leanprover-community/mathlib/commit/cdb69d5)
fix(data/set/function): do not use reducible ([#12377](https://github.com/leanprover-community/mathlib/pull/12377))
Reducible should only be used if the definition if it occurs as an explicit argument in a type class and must reduce during type class search, or if it is a type that should inherit instances.  Propositions should only be reducible if they are trivial variants (`<` and `>` for example).
These reducible attributes here will cause issues in Lean 4.  In Lean 4, the simplifier unfold reducible definitions in simp lemmas.  This means that tagging an `inj_on`-theorem with `@[simp]` creates the simp lemma `?a = ?b` (i.e. match anything).

### [2022-03-03 19:28:00](https://github.com/leanprover-community/mathlib/commit/363b7cd)
feat(algebra/ring/basic): generalize lemmas about differences of squares to non-commutative rings ([#12366](https://github.com/leanprover-community/mathlib/pull/12366))
This copies `mul_self_sub_mul_self` and `mul_self_eq_mul_self_iff` to the `commute` namespace, and reproves the existing lemmas in terms of the new commute lemmas.
As a result, the requirements on `mul_self_sub_one` and `mul_self_eq_one_iff` and `units.inv_eq_self_iff` can be weakened from `comm_ring` to `non_unital_non_assoc_ring` or `ring`.
This also replaces a few `is_domain`s with the weaker `no_zero_divisors`, since the lemmas are being moved anyway. In practice this just removes the nontriviality requirements.

### [2022-03-03 19:27:59](https://github.com/leanprover-community/mathlib/commit/e823109)
chore(algebra/{group,group_with_zero}/basic): rename `div_mul_div` and `div_mul_comm` ([#12365](https://github.com/leanprover-community/mathlib/pull/12365))
The new name, `div_mul_div_comm` is consistent with `mul_mul_mul_comm`.
Obviously this renames the additive versions too.

### [2022-03-03 19:27:58](https://github.com/leanprover-community/mathlib/commit/ca7346d)
feat(combinatorics/simple_graph/connectivity): add walk.darts ([#12360](https://github.com/leanprover-community/mathlib/pull/12360))
Darts can be more convenient than edges when working with walks since they keep track of orientation. This adds the list of darts along a walk and uses this to define and prove things about edges along a walk.

### [2022-03-03 19:27:57](https://github.com/leanprover-community/mathlib/commit/3b0111b)
feat(field_theory/minpoly): add minpoly_add_algebra_map and minpoly_sub_algebra_map ([#12357](https://github.com/leanprover-community/mathlib/pull/12357))
We add minpoly_add_algebra_map and minpoly_sub_algebra_map: the minimal polynomial of x ± a.
From flt-regular

### [2022-03-03 19:27:56](https://github.com/leanprover-community/mathlib/commit/301a266)
feat(number_theory/cyclotomic/primitive_roots): add is_primitive_root.sub_one_power_basis ([#12356](https://github.com/leanprover-community/mathlib/pull/12356))
We add `is_primitive_root.sub_one_power_basis`,  the power basis of a cyclotomic extension given by `ζ - 1`, where `ζ ` is a primitive root of unity.
From flt-regular.

### [2022-03-03 19:27:55](https://github.com/leanprover-community/mathlib/commit/78b323b)
feat(analysis/special_functions/trigonometric): inequality `tan x  > x` ([#12352](https://github.com/leanprover-community/mathlib/pull/12352))

### [2022-03-03 19:27:53](https://github.com/leanprover-community/mathlib/commit/d0816c0)
feat(analysis/calculus): support and cont_diff ([#11976](https://github.com/leanprover-community/mathlib/pull/11976))
* Add some lemmas about the support of the (f)derivative of a function
* Add some equivalences for `cont_diff`

### [2022-03-03 17:48:13](https://github.com/leanprover-community/mathlib/commit/16d48d7)
feat(algebra/star/basic + analysis/normed_space/star/basic): add two eq_zero/ne_zero lemmas ([#12412](https://github.com/leanprover-community/mathlib/pull/12412))
Added two lemmas about elements being zero or non-zero.
Golf a proof.

### [2022-03-03 17:48:12](https://github.com/leanprover-community/mathlib/commit/3fa09c2)
feat(algebra/homology/homotopy): compatibilities of null_homotopic_map with composition and additive functors ([#12392](https://github.com/leanprover-community/mathlib/pull/12392))

### [2022-03-03 17:48:10](https://github.com/leanprover-community/mathlib/commit/0da2d1d)
feat(ring_theory/polynomial/eisenstein): add mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at ([#12371](https://github.com/leanprover-community/mathlib/pull/12371))
We add `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at`: let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of `B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `p ^ n • z ∈ adjoin R {B.gen}`, then `z ∈ adjoin R {B.gen}`. Together with `algebra.discr_mul_is_integral_mem_adjoin` this result often allows to compute the ring of integers of `L`.
From flt-regular

### [2022-03-03 17:48:08](https://github.com/leanprover-community/mathlib/commit/b0cf3d7)
feat(algebra/algebra/subalgebra): add a helper to promote submodules to subalgebras ([#12368](https://github.com/leanprover-community/mathlib/pull/12368))

### [2022-03-03 17:48:05](https://github.com/leanprover-community/mathlib/commit/ba998da)
feat(algebra/order/monoid_lemmas_zero_lt): more lemmas using `pos_mul` and friends ([#12355](https://github.com/leanprover-community/mathlib/pull/12355))
This PR continues the `order` refactor.  The added lemmas are the `\le` analogues of the `<` lemmas that are already present.

### [2022-03-03 17:48:03](https://github.com/leanprover-community/mathlib/commit/5159a8f)
feat(simplex_category): various epi/mono lemmas ([#11924](https://github.com/leanprover-community/mathlib/pull/11924))

### [2022-03-03 16:19:52](https://github.com/leanprover-community/mathlib/commit/f41897d)
feat(dynamics/fixed_points/basic): Fixed points are a subset of the range ([#12423](https://github.com/leanprover-community/mathlib/pull/12423))

### [2022-03-03 16:19:50](https://github.com/leanprover-community/mathlib/commit/4edf36d)
feat(data/nat/fib): sum of initial fragment of the Fibonacci sequence is one less than a Fibonacci number ([#12416](https://github.com/leanprover-community/mathlib/pull/12416))

### [2022-03-03 16:19:49](https://github.com/leanprover-community/mathlib/commit/59bf454)
refactor(measure_theory): enable dot notation for measure.map ([#12350](https://github.com/leanprover-community/mathlib/pull/12350))
Refactor to allow for using dot notation with `measure.map` (was previously not possible because it was bundled as a linear map). Mirrors `measure.restrict` wrapper implementation for `measure.restrictₗ`.

### [2022-03-03 16:19:48](https://github.com/leanprover-community/mathlib/commit/c504585)
fix(number_theory/number_field): make ring_of_integers_algebra not an instance ([#12331](https://github.com/leanprover-community/mathlib/pull/12331))
This issue has caused problems for at least two of Kevin's PhD students; it is better to remove it for now or disable it temporarily.
c.f. https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/diamond.20for.20monoid.20instance.20on.20ideals

### [2022-03-03 16:19:47](https://github.com/leanprover-community/mathlib/commit/0ac3f9d)
feat(category_theory/preadditive): the category of additive functors ([#12330](https://github.com/leanprover-community/mathlib/pull/12330))

### [2022-03-03 16:19:46](https://github.com/leanprover-community/mathlib/commit/691722a)
feat(set_theory/ordinal): `enum` is injective ([#12319](https://github.com/leanprover-community/mathlib/pull/12319))

### [2022-03-03 16:19:45](https://github.com/leanprover-community/mathlib/commit/18f53db)
feat(topology/metric_space/pi_nat): metric structure on product spaces ([#12220](https://github.com/leanprover-community/mathlib/pull/12220))
We endow the spaces `Π (n : ℕ), E n` or `Π (i : ι), E i` with various distances (not registered as instances), and use these to show that these spaces retract on their closed subsets.

### [2022-03-03 14:50:37](https://github.com/leanprover-community/mathlib/commit/8053f56)
feat(ring_theory/dedekind_domain): strengthen `exist_integer_multiples` ([#12184](https://github.com/leanprover-community/mathlib/pull/12184))
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K` to find a collection of elements of `A` that is not completely contained in `J`.

### [2022-03-03 14:50:36](https://github.com/leanprover-community/mathlib/commit/4dec7b5)
feat(ring_theory/ideal): `(I : ideal R) • (⊤ : submodule R M)` ([#12178](https://github.com/leanprover-community/mathlib/pull/12178))
Two useful lemmas on the submodule spanned by `I`-scalar multiples.

### [2022-03-03 13:01:44](https://github.com/leanprover-community/mathlib/commit/26d9d38)
feat(number_theory): padic.complete_space instance ([#12424](https://github.com/leanprover-community/mathlib/pull/12424))

### [2022-03-03 13:01:43](https://github.com/leanprover-community/mathlib/commit/bf203b9)
docs(set_theory/cofinality): Fix cofinality definition ([#12421](https://github.com/leanprover-community/mathlib/pull/12421))
The condition is `a ≤ b`, not `¬(b > a)`.

### [2022-03-03 13:01:42](https://github.com/leanprover-community/mathlib/commit/02cad2c)
feat(data/complex/basic): add abs_hom ([#12409](https://github.com/leanprover-community/mathlib/pull/12409))

### [2022-03-03 13:01:40](https://github.com/leanprover-community/mathlib/commit/bc35902)
chore(algebra/group/hom): more generic `f x ≠ 1` lemmas ([#12404](https://github.com/leanprover-community/mathlib/pull/12404))
 * `map_ne_{one,zero}_iff` is the `not_congr` version of `map_eq_one_iff`, which was previously only available for `mul_equiv_class`
 * `ne_{one,zero}_of_map` is one direction of `map_ne_{one,zero}_iff` that doesn't assume injectivity

### [2022-03-03 13:01:39](https://github.com/leanprover-community/mathlib/commit/ca0ff3a)
feat(algebra/algebra/spectrum): show the star and spectrum operations commute ([#12351](https://github.com/leanprover-community/mathlib/pull/12351))
This establishes the identity `(σ a)⋆ = σ a⋆` for any `a : A` where `A` is a star ring and a star module over a star add monoid `R`.

### [2022-03-03 13:01:38](https://github.com/leanprover-community/mathlib/commit/f7a6fe9)
feat(set_theory/cofinality): Prove simple theorems on regular cardinals ([#12328](https://github.com/leanprover-community/mathlib/pull/12328))

### [2022-03-03 11:09:23](https://github.com/leanprover-community/mathlib/commit/16ad25c)
chore(analysis/normed_space/star/basic): golf a proof ([#12420](https://github.com/leanprover-community/mathlib/pull/12420))
Shorten a proof using ext.

### [2022-03-03 11:09:21](https://github.com/leanprover-community/mathlib/commit/228ab96)
feat(data/list/destutter): add `list.destutter` to remove chained duplicates ([#11934](https://github.com/leanprover-community/mathlib/pull/11934))

### [2022-03-03 09:29:13](https://github.com/leanprover-community/mathlib/commit/46b9d05)
feat(data/part): Lemmas for get on binary function instances ([#12194](https://github.com/leanprover-community/mathlib/pull/12194))
A variety of lemmas such as `mul_get_eq` for `part`.

### [2022-03-03 07:35:45](https://github.com/leanprover-community/mathlib/commit/9f721ba)
chore(logic/function/basic): add function.ne_iff ([#12288](https://github.com/leanprover-community/mathlib/pull/12288))

### [2022-03-03 00:08:38](https://github.com/leanprover-community/mathlib/commit/9deeddb)
feat(algebra/algebra/operations): `submodule.map_pow` and opposite lemmas ([#12374](https://github.com/leanprover-community/mathlib/pull/12374))
To prove `map_pow`, we add `submodule.map_hom` to match the very-recently-added `ideal.map_hom`. 
The opposite lemmas can be used to extend these results for maps that reverse multiplication, by factoring them into an `alg_hom` into the opposite type composed with `mul_opposite.op`.
`(↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)` is really a mouthful, but the elaborator can't seem to work out the type any other way, and `.to_linear_map` appears not to be the preferred form for `simp` lemmas.

### [2022-03-02 22:17:15](https://github.com/leanprover-community/mathlib/commit/6f74d3c)
chore(algebra/ring/basic): generalize lemmas to non-associative rings ([#12411](https://github.com/leanprover-community/mathlib/pull/12411))

### [2022-03-02 21:08:47](https://github.com/leanprover-community/mathlib/commit/ce26d75)
refactor(analysis/normed_space/basic): split into normed_space and ../normed/normed_field ([#12410](https://github.com/leanprover-community/mathlib/pull/12410))
Splits off the sections about normed rings and fields of the file `analysis/normed_space/basic` into a new file `analysis/normed/normed_field`.

### [2022-03-02 20:03:20](https://github.com/leanprover-community/mathlib/commit/423328e)
chore(probability/independence): change to set notation and `measurable_set` ([#12400](https://github.com/leanprover-community/mathlib/pull/12400))

### [2022-03-02 18:33:51](https://github.com/leanprover-community/mathlib/commit/a283e17)
feat(algebra/module/submodule_pointwise): pointwise negation ([#12405](https://github.com/leanprover-community/mathlib/pull/12405))
We already have pointwise negation on `add_submonoid`s (from [#10451](https://github.com/leanprover-community/mathlib/pull/10451)), this extends it to `submodules`.
The lemmas are all copies of the add_submonoid lemmas, except for two new lemmas:
* `submodule.neg_to_add_submonoid`
* `submodule.neg_eq_self`, which isn't true for `add_submonoid`s
Finally, we provide a `has_distrib_neg` instance; even though the negation is not cancellative, it does distribute over multiplication as expected.

### [2022-03-02 17:49:08](https://github.com/leanprover-community/mathlib/commit/90e2957)
chore(measure_theory/function/egorov): rename `uniform_integrability` file to `egorov` ([#12402](https://github.com/leanprover-community/mathlib/pull/12402))

### [2022-03-02 14:31:45](https://github.com/leanprover-community/mathlib/commit/7959d98)
feat(linear_algebra/matrix.determinant): add `matrix.det_neg` ([#12396](https://github.com/leanprover-community/mathlib/pull/12396))

### [2022-03-02 14:31:43](https://github.com/leanprover-community/mathlib/commit/c96fb62)
refactor(group_theory/*): Rename `general_commutator.lean` to `commutator.lean` ([#12388](https://github.com/leanprover-community/mathlib/pull/12388))
Followup to [#12308](https://github.com/leanprover-community/mathlib/pull/12308).

### [2022-03-02 14:31:41](https://github.com/leanprover-community/mathlib/commit/d00cbee)
feat(algebra/big_operators/basic): prod_dvd_prod_of_subset ([#12383](https://github.com/leanprover-community/mathlib/pull/12383))

### [2022-03-02 14:31:40](https://github.com/leanprover-community/mathlib/commit/22ddf9a)
feat(ring_theory/ideal): `map f (I^n) = (map f I)^n` ([#12370](https://github.com/leanprover-community/mathlib/pull/12370))

### [2022-03-02 12:52:29](https://github.com/leanprover-community/mathlib/commit/4e8d8f2)
feat(ring_theory/unique_factorization_domain): factors of `p^k` ([#12369](https://github.com/leanprover-community/mathlib/pull/12369))
This is a relatively trivial application of existing lemmas, but the result is a particularly nice shape that I felt worth to add to the library.

### [2022-03-02 12:52:28](https://github.com/leanprover-community/mathlib/commit/f191f52)
chore(algebra/big_operators): generalize `map_prod` to `monoid_hom_class` ([#12354](https://github.com/leanprover-community/mathlib/pull/12354))
This PR generalizes the following lemmas to `(add_)monoid_hom_class`:
 * `map_prod`, `map_sum`
 * `map_multiset_prod`, `map_multiset_sum`
 * `map_list_prod`, `map_list_sum`
 * `map_finsupp_prod`, `map_finsupp_sum`
I haven't removed any of the existing specialized, namespaced versions of these lemmas yet, but I have marked them as `protected` and added a docstring saying to use the generic version instead.

### [2022-03-02 10:22:02](https://github.com/leanprover-community/mathlib/commit/20d9541)
chore(ring_theory/localization): `localization_map_bijective` rename & `field` instance version ([#12375](https://github.com/leanprover-community/mathlib/pull/12375))

### [2022-03-02 09:30:27](https://github.com/leanprover-community/mathlib/commit/35086a1)
feat(probability): define conditional probability and add basic related theorems ([#12344](https://github.com/leanprover-community/mathlib/pull/12344))
Add the definition of conditional probability as a scaled restricted measure and prove Bayes' Theorem and other basic theorems.

### [2022-03-02 07:46:20](https://github.com/leanprover-community/mathlib/commit/1eebec5)
perf(data/fintype/basic): speed up mem_of_mem_perms_of_list ([#12389](https://github.com/leanprover-community/mathlib/pull/12389))
This single theorem was taking twice as long as everything else in the file put together, and it was easy to fix.

### [2022-03-02 07:46:19](https://github.com/leanprover-community/mathlib/commit/9daa233)
doc(*): fix broken markdown links ([#12385](https://github.com/leanprover-community/mathlib/pull/12385))
Some urls to nLab were also weird, so I replaced it with less weird ones.
The `MM91` reference was presumably intended to reference `MM92`.

### [2022-03-02 07:46:18](https://github.com/leanprover-community/mathlib/commit/b77ff23)
feat(algebra/ring): add non-unital and non-associative rings ([#12300](https://github.com/leanprover-community/mathlib/pull/12300))
Following up on [#11124](https://github.com/leanprover-community/mathlib/pull/11124).
The longer term goal is to develop C^* algebras, where non-unital algebras are an essential part of the theory.

### [2022-03-02 06:23:49](https://github.com/leanprover-community/mathlib/commit/fefe359)
feat(set_theory/principal): prove theorems about additive principal ordinals ([#11704](https://github.com/leanprover-community/mathlib/pull/11704))

### [2022-03-02 04:09:19](https://github.com/leanprover-community/mathlib/commit/a9902d5)
feat(algebra/divisibility): generalise basic facts to semigroups ([#12325](https://github.com/leanprover-community/mathlib/pull/12325))

### [2022-03-02 02:44:42](https://github.com/leanprover-community/mathlib/commit/cc9de07)
feat(algebra/star): replace star_monoid with star_semigroup ([#12299](https://github.com/leanprover-community/mathlib/pull/12299))
In preparation for allowing non-unital C^* algebras, replace star_monoid with star_semigroup.

### [2022-03-01 23:58:42](https://github.com/leanprover-community/mathlib/commit/4ba9098)
feat(algebra/euclidean_domain,data/int/basic): dvd_div_of_mul_dvd ([#12382](https://github.com/leanprover-community/mathlib/pull/12382))
We have a separate `int` and `euclidean_domain` version as `euclidean_domain` isn't pulled in by `int.basic`.

### [2022-03-01 22:20:43](https://github.com/leanprover-community/mathlib/commit/269280a)
feat(topology/bornology/basic): Define bornology ([#12036](https://github.com/leanprover-community/mathlib/pull/12036))
This defines bornologies and provides the basic API. A bornology on a type is a filter consisting of cobounded sets which contains the cofinite sets; bounded sets are then complements of cobounded sets. This is equivalent to the usual formulation in terms of bounded sets, but provides access to mathlib's large filter library. We provide the relevant API for bounded sets.

### [2022-03-01 20:54:12](https://github.com/leanprover-community/mathlib/commit/5c2fa35)
chore(topology/algebra/valuation): add universe ([#11962](https://github.com/leanprover-community/mathlib/pull/11962))

### [2022-03-01 19:12:01](https://github.com/leanprover-community/mathlib/commit/818c81f)
feat(ring_theory/integral_domain): finite integral domain is a field ([#12376](https://github.com/leanprover-community/mathlib/pull/12376))
We don't yet have Wedderburn's little theorem (on my todo list), so adding some weaker versions to tide us over.

### [2022-03-01 19:11:59](https://github.com/leanprover-community/mathlib/commit/130e07d)
chore(algebra/group/prod): `prod.swap` commutes with arithmetic ([#12367](https://github.com/leanprover-community/mathlib/pull/12367))
This also adds some missing `div` lemmas using `to_additive`.

### [2022-03-01 17:25:51](https://github.com/leanprover-community/mathlib/commit/5e36e12)
feat(category_theory/abelian/homology): Adds API for homology mimicking that of (co)kernels. ([#12171](https://github.com/leanprover-community/mathlib/pull/12171))

### [2022-03-01 17:25:49](https://github.com/leanprover-community/mathlib/commit/b45657f)
feat(algebra/algebra/spectrum, analysis/normed_space/spectrum): prove the spectrum of any element in a complex Banach algebra is nonempty ([#12115](https://github.com/leanprover-community/mathlib/pull/12115))
This establishes that the spectrum of any element in a (nontrivial) complex Banach algebra is nonempty. The nontrivial assumption is necessary, as otherwise the only element is invertible. In addition, we establish some properties of the resolvent function; in particular, it tends to zero at infinity.
- [x] depends on: [#12095](https://github.com/leanprover-community/mathlib/pull/12095)

### [2022-03-01 17:25:48](https://github.com/leanprover-community/mathlib/commit/29c84f7)
feat(combinatorics/set_family/lym): Lubell-Yamamoto-Meshalkin inequalities ([#11248](https://github.com/leanprover-community/mathlib/pull/11248))
This proves the two local LYM inequalities, the LYM inequality and Sperner's theorem.

### [2022-03-01 15:29:36](https://github.com/leanprover-community/mathlib/commit/3007f24)
chore(*): use `*_*_*_comm` where possible ([#12372](https://github.com/leanprover-community/mathlib/pull/12372))
These lemmas are quite helpful when proving `map_add` type statements; hopefully people will remember them more if they see them used in a few more places.

### [2022-03-01 15:29:35](https://github.com/leanprover-community/mathlib/commit/3fb051d)
feat(field_theory/krull_topology): added krull_topology_t2 ([#11973](https://github.com/leanprover-community/mathlib/pull/11973))

### [2022-03-01 14:22:58](https://github.com/leanprover-community/mathlib/commit/5a56e46)
chore(data/polynomial/monic): remove useless lemma ([#12364](https://github.com/leanprover-community/mathlib/pull/12364))
There is a `nontrivial` version of this lemma (`ne_zero_of_monic`) which actually has uses in the library, unlike this deleted lemma. We also tidy the proof of the lemma below.

### [2022-03-01 14:22:57](https://github.com/leanprover-community/mathlib/commit/a4e936c)
chore(category_theory/idempotents) replaced "idempotence" by "idem" ([#12362](https://github.com/leanprover-community/mathlib/pull/12362))

### [2022-03-01 10:36:01](https://github.com/leanprover-community/mathlib/commit/1f39ada)
feat(linear_algebra): generalize `linear_equiv.finrank_eq` to rings ([#12358](https://github.com/leanprover-community/mathlib/pull/12358))
Since `finrank` doesn't assume the module is actually a vector space, neither should the statement that linear equivalences preserve it.

### [2022-03-01 07:35:56](https://github.com/leanprover-community/mathlib/commit/c223a81)
feat(measure_theory/function/locally_integrable): define locally integrable ([#12216](https://github.com/leanprover-community/mathlib/pull/12216))
* Define the locally integrable predicate
* Move all results about integrability on compact sets to a new file
* Rename some lemmas from `integrable_on_compact` -> `locally_integrable`, if appropriate.
* Weaken some type-class assumptions (also on `is_compact_interval`)
* Simplify proof of `continuous.integrable_of_has_compact_support`
* Rename variables in moved lemmas to sensible names

### [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/cd98967)
feat(order/category/CompleteLattice): The category of complete lattices ([#12348](https://github.com/leanprover-community/mathlib/pull/12348))
Define `CompleteLattice`, the category of complete lattices with complete lattice homomorphisms.

### [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/37885e8)
feat(category_theory/idempotents): biproducts in idempotent completions ([#12333](https://github.com/leanprover-community/mathlib/pull/12333))

### [2022-03-01 01:31:29](https://github.com/leanprover-community/mathlib/commit/73dd4b5)
refactor(category_theory/functor): a folder for concepts directly related to functors ([#12346](https://github.com/leanprover-community/mathlib/pull/12346))