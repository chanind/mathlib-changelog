### [2021-01-31 18:12:02](https://github.com/leanprover-community/mathlib/commit/a15e64a)
refactor(data/polynomial/degree/definitions): rw -> exact, use term mode proof ([#5946](https://github.com/leanprover-community/mathlib/pull/5946))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-31 06:59:28](https://github.com/leanprover-community/mathlib/commit/4f4a9b5)
feat(analysis/analytic/inverse): inverse of a formal multilinear series ([#5852](https://github.com/leanprover-community/mathlib/pull/5852))
We construct the left inverse and a right inverse of a formal multilinear series with invertible first term, and we show that they coincide.

### [2021-01-31 01:46:38](https://github.com/leanprover-community/mathlib/commit/1ea538b)
chore(scripts): update nolints.txt ([#5976](https://github.com/leanprover-community/mathlib/pull/5976))
I am happy to remove some nolints for you!

### [2021-01-30 22:44:52](https://github.com/leanprover-community/mathlib/commit/ae1b530)
chore(algebra/algebra/basic): add simp lemma about `algebra_map ℚ` ([#5970](https://github.com/leanprover-community/mathlib/pull/5970))
Since there is a subsingleton instance over ring_homs, we may as well let the simplifier replace `algebra_map` with `id`.

### [2021-01-30 22:44:50](https://github.com/leanprover-community/mathlib/commit/f596077)
feat(geometry/manifold/instances): sphere is a topological manifold ([#5591](https://github.com/leanprover-community/mathlib/pull/5591))
Construct stereographic projection, as a local homeomorphism from the unit sphere in an inner product space `E` to a hyperplane in `E`.  Make a charted space instance for the sphere, with these stereographic projections as the atlas.

### [2021-01-30 20:09:59](https://github.com/leanprover-community/mathlib/commit/a6c0442)
feat(field_theory/normal): Restriction is surjective ([#5960](https://github.com/leanprover-community/mathlib/pull/5960))
Proves surjectivity of `alg_equiv.restrict_normal_hom`.
Also proves a bijectivity lemma which gives a cleaner construction of `alg_equiv.restrict_normal`.

### [2021-01-30 20:09:57](https://github.com/leanprover-community/mathlib/commit/48d0592)
feat(algebra/lie/basic): define derived length and semisimple Lie algebras ([#5930](https://github.com/leanprover-community/mathlib/pull/5930))
We also provide proofs of some basic characterisations

### [2021-01-30 18:21:17](https://github.com/leanprover-community/mathlib/commit/539550d)
feat(topology/instances/nnreal): add has_sum_nat_add_iff and module docstring ([#5716](https://github.com/leanprover-community/mathlib/pull/5716))

### [2021-01-30 14:50:34](https://github.com/leanprover-community/mathlib/commit/d6fe605)
chore(*): split some long lines ([#5959](https://github.com/leanprover-community/mathlib/pull/5959))

### [2021-01-30 10:07:38](https://github.com/leanprover-community/mathlib/commit/8069521)
feat(measure_theory): Absolute continuity ([#5948](https://github.com/leanprover-community/mathlib/pull/5948))
* Define absolute continuity between measures (@mzinkevi)
* State monotonicity of `ae_measurable` w.r.t. absolute continuity
* Weaken some `measurable` assumptions in `prod.lean` to `ae_measurable`
* Some docstring fixes
* Some cleanup

### [2021-01-30 08:05:04](https://github.com/leanprover-community/mathlib/commit/cf21863)
doc(group_theory/order_of_element): Adding doc string ([#5936](https://github.com/leanprover-community/mathlib/pull/5936))

### [2021-01-30 06:47:28](https://github.com/leanprover-community/mathlib/commit/cbcbaa0)
feat(topology/category): compact hausdorff spaces are reflective in Top ([#5955](https://github.com/leanprover-community/mathlib/pull/5955))
Show explicitly that `CompHaus_to_Top` is a reflective functor via the Stone-Cech compactification.

### [2021-01-30 01:48:52](https://github.com/leanprover-community/mathlib/commit/b44e9dd)
chore(scripts): update nolints.txt ([#5965](https://github.com/leanprover-community/mathlib/pull/5965))
I am happy to remove some nolints for you!

### [2021-01-29 21:16:04](https://github.com/leanprover-community/mathlib/commit/686d005)
chore(*): fix some "line too long" lint errors by rewriting proofs/statements ([#5958](https://github.com/leanprover-community/mathlib/pull/5958))

### [2021-01-29 19:10:11](https://github.com/leanprover-community/mathlib/commit/e8e0526)
feat(field_theory/polynomial_galois_group): New file ([#5861](https://github.com/leanprover-community/mathlib/pull/5861))
This PR adds the file `polynomial_galois_group`. It contains some of the groundwork needed for proving the Abel-Ruffini theorem.

### [2021-01-29 17:21:20](https://github.com/leanprover-community/mathlib/commit/62cf420)
ci(lint-style): adjust output to integrate with github ([#5952](https://github.com/leanprover-community/mathlib/pull/5952))

### [2021-01-29 17:21:18](https://github.com/leanprover-community/mathlib/commit/657cfeb)
doc(algebra/polynomial/big_operators): add / fix docstrings and lint ([#5950](https://github.com/leanprover-community/mathlib/pull/5950))

### [2021-01-29 17:21:16](https://github.com/leanprover-community/mathlib/commit/aabb843)
feat(analysis/normed_space/inner_product): existence of isometry to Euclidean space ([#5949](https://github.com/leanprover-community/mathlib/pull/5949))
A finite-dimensional inner product space admits an isometry (expressed using the new `linear_isometry_equiv` structure of [#5867](https://github.com/leanprover-community/mathlib/pull/5867), cc @urkud) to Euclidean space.

### [2021-01-29 17:21:14](https://github.com/leanprover-community/mathlib/commit/0d18179)
chore(analysis/normed_space/multilinear): rename variables ([#5929](https://github.com/leanprover-community/mathlib/pull/5929))
Use `E` and `E'` for indexed types and `G` and `G'` for `Type*`s.

### [2021-01-29 15:28:07](https://github.com/leanprover-community/mathlib/commit/9c5064c)
chore(linear_algebra/linear_independent): relax requirements to semiring and division_ring ([#5953](https://github.com/leanprover-community/mathlib/pull/5953))
No lemma names or proofs were changed, this just reordered some lemmas so that they could be put into sections with weaker requirements.

### [2021-01-29 14:19:09](https://github.com/leanprover-community/mathlib/commit/783e11a)
fix(scripts): fix mixing absolute and relative paths to the linter ([#5810](https://github.com/leanprover-community/mathlib/pull/5810))
Fix providing either relative or absolute paths to the linter.
Make the linter emit outputted paths corresponding to the ones passed on the command line -- relative if relative, absolute if absolute.
Also adds a short set of tests.
Reported in: https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/2013.20Q5 (and introduced in [#5721](https://github.com/leanprover-community/mathlib/pull/5721)).

### [2021-01-29 11:30:18](https://github.com/leanprover-community/mathlib/commit/41decdb)
chore(combinatorics/simple_graph/basic): remove classical locale ([#5951](https://github.com/leanprover-community/mathlib/pull/5951))
This completes the simple graph part of the refactor that removed classical fintype instances.

### [2021-01-29 11:30:16](https://github.com/leanprover-community/mathlib/commit/15217c2)
refactor(topology/local_homeomorph): simplify `prod_trans` ([#5915](https://github.com/leanprover-community/mathlib/pull/5915))
10X faster elaboration
(pretty-printed) proof term length 14637 -> 2046
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-29 09:42:09](https://github.com/leanprover-community/mathlib/commit/bbec099)
refactor(data/real/nnreal): shorter proof of `div_lt_iff` ([#5945](https://github.com/leanprover-community/mathlib/pull/5945))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-29 06:49:21](https://github.com/leanprover-community/mathlib/commit/145f127)
feat(ring_theory/polynomial/chebyshev/defs): Chebyshev polynomials of the second kind ([#5793](https://github.com/leanprover-community/mathlib/pull/5793))
This will define Chebyshev polynomials of the second kind and introduce some basic properties:
- [x] Define Chebyshev polynomials of the second kind.
- [x] Relate Chebyshev polynomials of the first and second kind through recursive formulae
- [x] Prove trigonometric identity regarding Chebyshev polynomials of the second kind
- [x] Compute the derivative of the Chebyshev polynomials of the first kind in terms of the Chebyshev polynomials of the second kind. 
- [x] Compute the derivative of the Chebyshev polynomials of the second kind in terms of the Chebyshev polynomials of the first kind.

### [2021-01-29 04:36:40](https://github.com/leanprover-community/mathlib/commit/1edd85c)
chore(scripts): update nolints.txt ([#5947](https://github.com/leanprover-community/mathlib/pull/5947))
I am happy to remove some nolints for you!

### [2021-01-29 01:34:13](https://github.com/leanprover-community/mathlib/commit/4dca6e1)
chore(data/fintype/basic): Remove duplicate instance ([#5943](https://github.com/leanprover-community/mathlib/pull/5943))
We already have `subtype.fintype`, there is no need for `fintype.subtype_of_fintype` which does the same thing

### [2021-01-28 23:59:53](https://github.com/leanprover-community/mathlib/commit/69e7f14)
chore(combinatorics/simple_graph): generalise decidability proofs ([#5938](https://github.com/leanprover-community/mathlib/pull/5938))
This generalises the decidable instances so they're more applicable, and also golfs the proofs.

### [2021-01-28 20:36:43](https://github.com/leanprover-community/mathlib/commit/2cbaa9c)
feat(data/list/basic): add diff_erase ([#5941](https://github.com/leanprover-community/mathlib/pull/5941))

### [2021-01-28 19:15:38](https://github.com/leanprover-community/mathlib/commit/2870212)
chore(data/sym2): golf decidability proofs ([#5940](https://github.com/leanprover-community/mathlib/pull/5940))
This golfs the decidable instances, and removes a redundant one (`from_rel.decidable_as_set` is automatically inferred from `from_rel.decidable_pred`)

### [2021-01-28 16:36:05](https://github.com/leanprover-community/mathlib/commit/645dc60)
refactor(analysis/calculus/inverse): inverse of C^k functions over R or C ([#5926](https://github.com/leanprover-community/mathlib/pull/5926))
Some results on the local inverse of smooth functions are currently formulated only for real functions, but they work as well for complex functions. We formulate them uniformly, assuming `is_R_or_C`.

### [2021-01-28 13:17:00](https://github.com/leanprover-community/mathlib/commit/c43c709)
fix(data/dfinsupp): fix overly strict type-class arguments ([#5935](https://github.com/leanprover-community/mathlib/pull/5935))

### [2021-01-28 08:12:08](https://github.com/leanprover-community/mathlib/commit/82481e3)
feat(analysis/normed_space/inner_product): existence of orthonormal basis ([#5734](https://github.com/leanprover-community/mathlib/pull/5734))
Define `orthonormal` sets (indexed) of vectors in an inner product space `E`.  Show that a finite-dimensional inner product space has an orthonormal basis.
Co-authored by: Busiso Chisala

### [2021-01-28 01:39:54](https://github.com/leanprover-community/mathlib/commit/9545445)
chore(scripts): update nolints.txt ([#5931](https://github.com/leanprover-community/mathlib/pull/5931))
I am happy to remove some nolints for you!

### [2021-01-27 23:19:08](https://github.com/leanprover-community/mathlib/commit/6585eff)
feat(archive/imo): formalize IMO 2013 problem Q5 ([#5787](https://github.com/leanprover-community/mathlib/pull/5787))

### [2021-01-27 21:59:34](https://github.com/leanprover-community/mathlib/commit/3e59960)
feat(ring_theory/nullstellensatz): Classical Nullstellensatz ([#5760](https://github.com/leanprover-community/mathlib/pull/5760))
This file states and proves Hilbert's classical nullstellensatz for multi-variate polynomials over an algebraically closed field.

### [2021-01-27 18:19:45](https://github.com/leanprover-community/mathlib/commit/4cc0d52)
refactor(data/set/basic): simpler proofs ([#5920](https://github.com/leanprover-community/mathlib/pull/5920))
This replaces many uses of `simp` and `finish` with direct term proofs
to speed up the overall compilation of the file.
This PR is WIP in the sense that not all of `set.basic` is converted,
but there are no dependencies between the changes so this can be merged
at any point.

### [2021-01-27 18:19:43](https://github.com/leanprover-community/mathlib/commit/8af7e08)
feat(data/fintype/basic): make subtype_of_fintype computable ([#5919](https://github.com/leanprover-community/mathlib/pull/5919))
This smokes out a few places downstream that are missing decidability hypotheses needed for the fintype instance to exist.

### [2021-01-27 18:19:41](https://github.com/leanprover-community/mathlib/commit/f45dee4)
feat(algebra/*,linear_algebra/basic,ring_theory/ideal): lemmas about span of finite subsets and nontrivial maximal ideals ([#5641](https://github.com/leanprover-community/mathlib/pull/5641))

### [2021-01-27 18:19:40](https://github.com/leanprover-community/mathlib/commit/32fdb81)
feat(data/zsqrtd/to_real): Add `to_real` ([#5640](https://github.com/leanprover-community/mathlib/pull/5640))
Also adds `norm_eq_zero`, and replaces some calls to simp with direct lemma applications

### [2021-01-27 16:19:52](https://github.com/leanprover-community/mathlib/commit/1011601)
feat(algebra/continued_fractions): add termination iff rat lemmas ([#4867](https://github.com/leanprover-community/mathlib/pull/4867))
### What
Show that the computation of a continued fraction terminates if and only if we compute the continued fraction of a rational number.
### How
1. Show that every intermediate operation involved in the computation of a continued fraction returns a value that has a rational counterpart. This then shows that a terminating continued fraction corresponds to a rational value.
2. Show that the operations involved in the computation of a continued fraction for rational numbers only return results that can be lifted to the result of the same operations done on an equal value in a suitable linear ordered, archimedean field with a floor function.
3. Show that the continued fraction of a rational number terminates.
4. Set up the needed coercions to express the results above starting from [here](https://github.com/leanprover-community/mathlib/compare/kappelmann_termination_iff_rat?expand=1#diff-1dbcf8473152b2d8fca024352bd899af37669b8af18792262c2d5d6f31148971R129). I did not know where to put these lemmas. Please let me know your opinion.
4. Extract 4 auxiliary lemmas that are not specific to continued fraction but more generally about rational numbers, integers, and natural numbers starting from [here](https://github.com/leanprover-community/mathlib/compare/kappelmann_termination_iff_rat?expand=1#diff-1dbcf8473152b2d8fca024352bd899af37669b8af18792262c2d5d6f31148971R28). Again, I did not know where to put these. Please let me know your opinion.

### [2021-01-27 12:14:38](https://github.com/leanprover-community/mathlib/commit/9adf9bb)
feat(order/ideal): add partial_order instance to order.ideal ([#5909](https://github.com/leanprover-community/mathlib/pull/5909))
Add some instances for `order.ideal`, some of them conditional on
having extra structure on the carrier preorder `P`:
* In all cases, `ideal P` is a partial order.
* If `P` has a bottom element, so does `ideal P`.
* If `P` has a top element, so does `ideal P`.
  (Although this could be weekened to `P` being directed.)
Also, add some `@[ext]`, `@[simp]`, `@[trans]` lemmas.

### [2021-01-27 12:14:36](https://github.com/leanprover-community/mathlib/commit/7244b43)
refactor(topology/local_homeomorph): simpler proof of `prod_symm` ([#5906](https://github.com/leanprover-community/mathlib/pull/5906))
17X smaller proof
co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 12:14:34](https://github.com/leanprover-community/mathlib/commit/a859f10)
refactor(computability/primrec): simpler proof of `primrec.of_equiv` ([#5905](https://github.com/leanprover-community/mathlib/pull/5905))
12X smaller proof term
co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 12:14:32](https://github.com/leanprover-community/mathlib/commit/35638ed)
refactor(data/set/basic): simpler proof of `union_subset_iff` ([#5904](https://github.com/leanprover-community/mathlib/pull/5904))
12X smaller proof term
co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 12:14:30](https://github.com/leanprover-community/mathlib/commit/c64aa13)
chore(*): bump to lean-3.26.0 ([#5895](https://github.com/leanprover-community/mathlib/pull/5895))

### [2021-01-27 12:14:28](https://github.com/leanprover-community/mathlib/commit/78a518a)
feat(measure_theory/independence): define independence of sets of sets, measurable spaces, sets, functions ([#5848](https://github.com/leanprover-community/mathlib/pull/5848))
This first PR about independence contains definitions, a few lemmas about independence of unions/intersections of sets of sets, and a proof that two measurable spaces are independent iff generating pi-systems are independent (included in this PR to demonstrate usability of the definitions).

### [2021-01-27 08:42:04](https://github.com/leanprover-community/mathlib/commit/e5f9409)
refactor(category_theory/abelian): golf `mono_of_kernel_ι_eq_zero` ([#5914](https://github.com/leanprover-community/mathlib/pull/5914))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:59](https://github.com/leanprover-community/mathlib/commit/1688b3e)
refactor(data/complex/exponential): simplify proof of `tan_eq_sin_div_cos` ([#5913](https://github.com/leanprover-community/mathlib/pull/5913))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:57](https://github.com/leanprover-community/mathlib/commit/e927930)
refactor(data/holor): simp -> refl ([#5912](https://github.com/leanprover-community/mathlib/pull/5912))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:55](https://github.com/leanprover-community/mathlib/commit/38f6e05)
refactor(algebra/category/Group/limits): simp -> refl ([#5911](https://github.com/leanprover-community/mathlib/pull/5911))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:53](https://github.com/leanprover-community/mathlib/commit/6eae630)
refactor(data/real/golden_ratio): simpler proof of `gold_pos` ([#5910](https://github.com/leanprover-community/mathlib/pull/5910))
13X smaller (pretty-printed) proof term
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:51](https://github.com/leanprover-community/mathlib/commit/e9a1e2b)
refactor(data/pequiv): simpler proof of `pequiv.of_set_univ` ([#5907](https://github.com/leanprover-community/mathlib/pull/5907))
17X smaller proof
co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 08:41:50](https://github.com/leanprover-community/mathlib/commit/fd55e57)
refactor(algebra/group/basic): simp -> rw in `sub_eq_sub_iff_sub_eq_sub` ([#5903](https://github.com/leanprover-community/mathlib/pull/5903))
co-authors: `lean-gptf`, Yuhuai Wu

### [2021-01-27 08:41:48](https://github.com/leanprover-community/mathlib/commit/1cd2286)
chore(data/finset/preimage): add missing simp lemmas ([#5902](https://github.com/leanprover-community/mathlib/pull/5902))

### [2021-01-27 08:41:46](https://github.com/leanprover-community/mathlib/commit/20d6b6a)
chore(*): add more simp lemmas, refactor theorems about `fintype.sum` ([#5888](https://github.com/leanprover-community/mathlib/pull/5888))
* `finset.prod_sum_elim`, `finset.sum_sum_elim`: use `finset.map`
  instead of `finset.image`;
* add `multilinear_map.coe_mk_continuous`,
  `finset.order_emb_of_fin_mem`, `fintype.univ_sum_type`,
  `fintype.prod_sum_elim`, `sum.update_elim_inl`,
  `sum.update_elim_inr`, `sum.update_inl_comp_inl`,
  `sum.update_inl_comp_inr`, `sum.update_inr_comp_inl`,
  `sum.update_inr_comp_inr` and `apply` versions of `sum.*_comp_*` lemmas,
* move some lemmas about `function.update` from `data.set.function` to `logic.function.basic`;
* rename `sum.elim_injective` to `function.injective.sum_elim`
* `simps` lemmas for `function.embedding.inl` and
  `function.embedding.inr`;
* for `e : α ≃o β`, simplify `e.to_equiv.symm` to `e.symm_to_equiv`;
* add `continuous_multilinear_map.to_multilinear_map_add`,
  `continuous_multilinear_map.to_multilinear_map_smul`, and `simps`
  for `continuous_multilinear_map.to_multilinear_map_linear`.

### [2021-01-27 08:41:44](https://github.com/leanprover-community/mathlib/commit/21e9d42)
feat(algebra/euclidean_domain): Unify occurences of div_add_mod and mod_add_div ([#5884](https://github.com/leanprover-community/mathlib/pull/5884))
Adding the corresponding commutative version at several places (euclidean domain, nat, pnat, int) whenever there is the other version. 
In subsequent PRs other proofs in the library which now use some version of `add_comm, exact div_add_mod` or `add_comm, exact mod_add_div` should be golfed.
Trying to address issue [#1534](https://github.com/leanprover-community/mathlib/pull/1534)

### [2021-01-27 08:41:42](https://github.com/leanprover-community/mathlib/commit/688772e)
refactor(ring_theory/ideal ring_theory/jacobson): allow `ideal` in a `comm_semiring` ([#5879](https://github.com/leanprover-community/mathlib/pull/5879))
At the moment, `ideal` requires the underlying ring to be a `comm_ring`.  This changes in this PR and the underlying ring can now be a `comm_semiring`.  There is a discussion about merits and issues in this Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/(comm_)semiring.3A.20examples.3F
At the moment, this PR changes the definition and adapts, mostly `ring_theory/jacobson`, to avoid deterministic timeouts.  In future PRs, I will start changing hypotheses on lemmas involving `ideal` to use the more general framework.
A note: the file `ring_theory/jacobson` might require further improvements.  If possible, I would like this change to push through without cluttering it with changes to that file.  If there is a way of accepting this change and then proceeding to the changes in `jacobson`, that would be ideal!  If it needs to be done at the same time, then so be it!

### [2021-01-27 08:41:40](https://github.com/leanprover-community/mathlib/commit/b2c5d9b)
feat(ring_theory/noetherian, linear_algebra/basic): Show that finitely generated submodules are the compact elements in the submodule lattice ([#5871](https://github.com/leanprover-community/mathlib/pull/5871))
Show that a submodule is finitely generated if and only if it is a compact lattice element. Add lemma showing that any submodule is the supremum of the spans of its elements.

### [2021-01-27 08:41:39](https://github.com/leanprover-community/mathlib/commit/7f04253)
feat(field_theory/adjoin): Generalize alg_hom_mk_adjoin_splits to infinite sets ([#5860](https://github.com/leanprover-community/mathlib/pull/5860))
This PR uses Zorn's lemma to generalize `alg_hom_mk_adjoin_splits` to infinite sets.
The proof is rather long, but I think that the result is worth it. It should allow me to prove that if E/F is any normal extension then any automorphism of F lifts to an automorphism of E.

### [2021-01-27 08:41:36](https://github.com/leanprover-community/mathlib/commit/e95928c)
feat(field_theory/normal): Restrict to normal subfield ([#5845](https://github.com/leanprover-community/mathlib/pull/5845))
Now that we know that splitting fields are normal, it makes sense to move the results of [#5562](https://github.com/leanprover-community/mathlib/pull/5562) to `normal.lean`.

### [2021-01-27 08:41:35](https://github.com/leanprover-community/mathlib/commit/61491ca)
feat(linear_algebra/matrix): A vector is zero iff its dot product with every vector is zero ([#5837](https://github.com/leanprover-community/mathlib/pull/5837))

### [2021-01-27 08:41:33](https://github.com/leanprover-community/mathlib/commit/31edca8)
chore(data/finsupp,data/dfinsupp,algebra/big_operators): add missing lemmas about sums of bundled functions ([#5834](https://github.com/leanprover-community/mathlib/pull/5834))
This adds missing lemmas about how `{finset,finsupp,dfinsupp}.{prod,sum}` acts on {coercion,application,evaluation} of `{add_monoid_hom,monoid_hom,linear_map}`. Specifically, it:
* adds the lemmas:
  * `monoid_hom.coe_prod`
  * `monoid_hom.map_dfinsupp_prod`
  * `monoid_hom.dfinsupp_prod_apply`
  * `monoid_hom.finsupp_prod_apply`
  * `monoid_hom.coe_dfinsupp_prod`
  * `monoid_hom.coe_finsupp_prod`
  * that are the additive versions of the above for `add_monoid_hom`.
  * `linear_map.map_dfinsupp_sum`
  * `linear_map.dfinsupp_sum_apply`
  * `linear_map.finsupp_sum_apply`
  * `linear_map.coe_dfinsupp_sum`
  * `linear_map.coe_finsupp_sum`
* Renames `linear_map.finsupp_sum` to `linear_map.map_finsupp_sum` for consistency with `linear_map.map_sum`.
* Adds a new `monoid_hom.coe_fn` definition

### [2021-01-27 08:41:30](https://github.com/leanprover-community/mathlib/commit/aa8980d)
chore(category_theory/monad): comonadic adjunction ([#5770](https://github.com/leanprover-community/mathlib/pull/5770))
Defines comonadic adjunctions dual to what's already there

### [2021-01-27 08:41:28](https://github.com/leanprover-community/mathlib/commit/3b6d6d7)
chore(data/fintype/basic): Add simp lemma about finset.univ ([#5708](https://github.com/leanprover-community/mathlib/pull/5708))

### [2021-01-27 08:41:26](https://github.com/leanprover-community/mathlib/commit/00b88eb)
feat(data/polynomial/denominators): add file denominators ([#5587](https://github.com/leanprover-community/mathlib/pull/5587))
The main goal of this PR is to establish that `b^deg(f)*f(a/b)` is an expression not involving denominators.
The first lemma, `induction_with_nat_degree_le` is an induction principle for polynomials, where the inductive hypothesis has a bound on the degree of the polynomial.  This allows to build the proof by tearing apart a polynomial into its monomials, while remembering the overall degree of the polynomial itself.  This lemma might be a better fit for the file `data.polynomial.induction`.

### [2021-01-27 05:12:41](https://github.com/leanprover-community/mathlib/commit/394d357)
refactor(data/nat/factorial): simpler proof of `mul_factorial_pred` ([#5917](https://github.com/leanprover-community/mathlib/pull/5917))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 05:12:39](https://github.com/leanprover-community/mathlib/commit/d41781c)
refactor(topology/metric_space): simplify `dist_triangle` proofs ([#5916](https://github.com/leanprover-community/mathlib/pull/5916))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-01-27 05:12:37](https://github.com/leanprover-community/mathlib/commit/4e4298e)
chore(*): split long lines ([#5908](https://github.com/leanprover-community/mathlib/pull/5908))

### [2021-01-27 05:12:35](https://github.com/leanprover-community/mathlib/commit/47e2f80)
chore(*): Replace integral_domain assumptions with no_zero_divisors ([#5877](https://github.com/leanprover-community/mathlib/pull/5877))
This removes unnecessary `nontrivial` assumptions, and reduces some `comm_ring` requirements to `comm_semiring`.
This also adds some missing `nontrivial` and `no_zero_divisors` instances.

### [2021-01-27 01:48:38](https://github.com/leanprover-community/mathlib/commit/19bb470)
chore(scripts): update nolints.txt ([#5918](https://github.com/leanprover-community/mathlib/pull/5918))
I am happy to remove some nolints for you!

### [2021-01-27 01:48:34](https://github.com/leanprover-community/mathlib/commit/9173005)
chore(tactic/finish): Remove broken ifinish ([#5897](https://github.com/leanprover-community/mathlib/pull/5897))
See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/intuitionistic.20logic/near/224013270

### [2021-01-27 01:48:32](https://github.com/leanprover-community/mathlib/commit/1ddb93a)
feat(analysis/normed_space): define linear isometries ([#5867](https://github.com/leanprover-community/mathlib/pull/5867))
* define `linear_isometry` and `linear_isometry_equiv`;
* add `linear_map.ker_eq_bot_of_inverse`;
* replace `inv_fun_apply` lemmas with `inv_fun_eq_symm`;
* golf some proofs in `linear_algebra/finite_dimensional`.

### [2021-01-27 01:48:30](https://github.com/leanprover-community/mathlib/commit/1eb1293)
feat(archive/imo): formalize IMO 2011 problem Q3 ([#5842](https://github.com/leanprover-community/mathlib/pull/5842))

### [2021-01-26 22:43:47](https://github.com/leanprover-community/mathlib/commit/531bcd8)
feat(data/real/{nnreal,ennreal}, topology/instances/ennreal): add of_real_(sum/prod/tsum) for nnreal and ennreal ([#5896](https://github.com/leanprover-community/mathlib/pull/5896))
We remark that if all terms of a real sum are nonnegative, `nnreal.of_real` of the sum is equal to the sum of the `nnreal.of_real`. Idem for `ennreal.of_real`, for products and `tsum`.

### [2021-01-26 22:43:45](https://github.com/leanprover-community/mathlib/commit/8c732b2)
feat(data/finset/basic): card_subtype simp lemma ([#5894](https://github.com/leanprover-community/mathlib/pull/5894))

### [2021-01-26 16:37:25](https://github.com/leanprover-community/mathlib/commit/547d67f)
feat(analysis/{analytic,calculus}): an analytic function is strictly differentiable ([#5878](https://github.com/leanprover-community/mathlib/pull/5878))

### [2021-01-26 04:21:27](https://github.com/leanprover-community/mathlib/commit/44fd23d)
chore(data/finset): Rename bind to bUnion ([#5813](https://github.com/leanprover-community/mathlib/pull/5813))
This commit renames `finset.bind` to `finset.bUnion`.  While this is the monadic bind operation, conceptually it's doing a bounded union of an indexed family of finite sets.  This will help with discoverability of this function.
There was a name conflict in `data.finset.lattice` due to this, since there are a number of theorems about the `set` version of `bUnion`, and for these I prefixed the lemmas with `set_`.

### [2021-01-26 01:48:59](https://github.com/leanprover-community/mathlib/commit/01a7cde)
chore(scripts): update nolints.txt ([#5892](https://github.com/leanprover-community/mathlib/pull/5892))
I am happy to remove some nolints for you!

### [2021-01-25 17:49:34](https://github.com/leanprover-community/mathlib/commit/5491c59)
feat(data/fintype/basic): add lemmas about finsets and cardinality ([#5886](https://github.com/leanprover-community/mathlib/pull/5886))
Add lemmas about finsets and cardinality. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's marriage theorem.
Coauthors: @kmill @b-mehta

### [2021-01-25 17:49:32](https://github.com/leanprover-community/mathlib/commit/7f25aa7)
chore(algebra/group_with_zero): correct instance name ([#5885](https://github.com/leanprover-community/mathlib/pull/5885))
The argument for this definition is `cancel_monoid_with_zero`, not `comm_cancel_monoid_with_zero`.

### [2021-01-25 17:49:30](https://github.com/leanprover-community/mathlib/commit/3a16e9f)
feat(data/set/finite): add to_finset lemma ([#5883](https://github.com/leanprover-community/mathlib/pull/5883))
Add lemma stating that taking to_finset of the union of two sets is the same as taking the union of to_finset of the sets.

### [2021-01-25 17:49:28](https://github.com/leanprover-community/mathlib/commit/ba87647)
feat(data/set/finite): add lemma about to_finset of complement of set ([#5881](https://github.com/leanprover-community/mathlib/pull/5881))
Add lemma stating that taking to_finset of the complement of a set is the same thing as taking the complement of to_finset of the set.

### [2021-01-25 17:49:25](https://github.com/leanprover-community/mathlib/commit/7188d80)
chore(algebra/pi_tensor_product): Replace use of classical with decidable_eq ([#5880](https://github.com/leanprover-community/mathlib/pull/5880))
This makes it consistent with `multilinear_map`, which also uses explicit decidability assumptions

### [2021-01-25 17:49:23](https://github.com/leanprover-community/mathlib/commit/1dfa81a)
feat(analysis/normed_space/inner_product): double orthogonal complement is closure ([#5876](https://github.com/leanprover-community/mathlib/pull/5876))
Put a submodule structure on the closure (as a set in a topological space) of a submodule of a topological module.  Show that in a complete inner product space, the double orthogonal complement of a submodule is its closure.

### [2021-01-25 17:49:21](https://github.com/leanprover-community/mathlib/commit/ee750e3)
chore(algebra): a few more `@[mono]` tags ([#5874](https://github.com/leanprover-community/mathlib/pull/5874))

### [2021-01-25 16:06:54](https://github.com/leanprover-community/mathlib/commit/6d80634)
feat(measure_theory/{measure_space, borel_space, integration}): prove ae_measurable for various limits ([#5849](https://github.com/leanprover-community/mathlib/pull/5849))
For a sequence of `ae_measurable` functions verifying some pointwise property almost everywhere, introduce a sequence of measurable functions verifying the same property and use it to prove ae-measurability of `is_lub`, `is_glb`, `supr`, `infi`, and almost everywhere pointwise limit.

### [2021-01-25 14:56:46](https://github.com/leanprover-community/mathlib/commit/d6d4435)
chore(archive/sensitivity): split long lines ([#5882](https://github.com/leanprover-community/mathlib/pull/5882))

### [2021-01-25 05:26:45](https://github.com/leanprover-community/mathlib/commit/9117ad7)
feat(order/atoms): define (co)atomic, (co)atomistic lattices ([#5588](https://github.com/leanprover-community/mathlib/pull/5588))
Define (co)atomic, (co)atomistic lattices
Relate these lattice definitions
Provide basic subtype instances

### [2021-01-25 04:13:48](https://github.com/leanprover-community/mathlib/commit/87202fe)
chore(scripts): update nolints.txt ([#5873](https://github.com/leanprover-community/mathlib/pull/5873))
I am happy to remove some nolints for you!

### [2021-01-25 01:08:37](https://github.com/leanprover-community/mathlib/commit/507c7ff)
feat(analysis/specific_limits): formula for `∑' n, n * r ^ n` ([#5835](https://github.com/leanprover-community/mathlib/pull/5835))
Also prove that `∑' n, n ^ k * r ^ n` is summable for any `k : ℕ`,
`∥r∥ < 1`.

### [2021-01-24 23:21:23](https://github.com/leanprover-community/mathlib/commit/5222db0)
chore(linear_algebra/multilinear): Relax ring to semiring, add_comm_group to add_comm_monoid ([#5870](https://github.com/leanprover-community/mathlib/pull/5870))

### [2021-01-24 20:25:01](https://github.com/leanprover-community/mathlib/commit/fbabe42)
feat(order/complete_well_founded, data/finset/lattice): introduce compact elements of a complete lattice and characterize compact lattices as those with all elements compact ([#5825](https://github.com/leanprover-community/mathlib/pull/5825))
Provide a definition of compact elements. Prove the equivalence of two characterizations of compact elements. Add "all elements are compact" to the equivalent characterizations of compact lattices. Introduce an auxiliary lemma about finite sups and directed sets.
<!--
A reference for the two equivalent definitions of compact element can be found [here](https://ncatlab.org/nlab/show/compact+element+in+a+lattice)
-->

### [2021-01-24 13:41:30](https://github.com/leanprover-community/mathlib/commit/5db7a18)
feat(data/nat/basic): add decidable_exists_lt deciding existence of a natural below a bound satisfying a predicate ([#5864](https://github.com/leanprover-community/mathlib/pull/5864))
Given a decidable predicate `P` on naturals it is decidable if there is a natural below any bound satisying the `P`.
closes [#5755](https://github.com/leanprover-community/mathlib/pull/5755)

### [2021-01-24 10:50:05](https://github.com/leanprover-community/mathlib/commit/49c53d4)
feat(measure_theory/lp_space): define Lp, subtype of ae_eq_fun with finite norm ([#5853](https://github.com/leanprover-community/mathlib/pull/5853))

### [2021-01-24 06:50:40](https://github.com/leanprover-community/mathlib/commit/aa744db)
feat(topology/subset_properties): a locally compact space with second countable topology is sigma compact ([#5689](https://github.com/leanprover-community/mathlib/pull/5689))
* add `set.subsingleton.induction_on`, `set.Union_eq_univ_iff`, and `set.bUnion_eq_univ_iff`;
* make `tactic.interactive.nontrivial` try `apply_instance` before
  `simp`;
* add `dense.inter_nhds_nonempty`;
* a subsingleton is compact (lemma for sets, instance for spaces);
* in a locally compact space, every point has a compact neighborhood;
* a compact space is sigma compact;
* a locally compact space with second countable topology is sigma
  compact;
* add `dense.bUnion_uniformity_ball`: the uniform neighborhoods of all
  points of a dense set cover the whole space
Some of these changes are leftovers from a failed attempt to prove a
wrong statement.

### [2021-01-24 03:45:38](https://github.com/leanprover-community/mathlib/commit/f414fca)
feat(analysis/analytic/composition): filling small holes in existing API ([#5822](https://github.com/leanprover-community/mathlib/pull/5822))
This PR expands the existing API around the composition of formal multilinear series.
Also makes the `finset` argument to `finset.prod_subtype` and `finset.add_subtype` explicit instead of implicit.

### [2021-01-24 02:20:04](https://github.com/leanprover-community/mathlib/commit/160d243)
chore(scripts): update nolints.txt ([#5865](https://github.com/leanprover-community/mathlib/pull/5865))
I am happy to remove some nolints for you!

### [2021-01-23 13:02:18](https://github.com/leanprover-community/mathlib/commit/8da574f)
feat(algebra/pointwise): a lemma about pointwise addition/multiplication of bdd_above sets ([#5859](https://github.com/leanprover-community/mathlib/pull/5859))

### [2021-01-23 13:02:16](https://github.com/leanprover-community/mathlib/commit/3a136f8)
refactor(analysis/analytic/composition): extend definition, extract a lemma from a proof ([#5850](https://github.com/leanprover-community/mathlib/pull/5850))
Extract a standalone lemma of the proof that the composition of two analytic functions is well-behaved, and extend a little bit the definition of the sets which are involved in the corresponding change of variables.

### [2021-01-23 11:06:24](https://github.com/leanprover-community/mathlib/commit/74760f2)
chore(set_theory/ordinal): use rel_iso notation in ordinal ([#5857](https://github.com/leanprover-community/mathlib/pull/5857))

### [2021-01-23 07:40:00](https://github.com/leanprover-community/mathlib/commit/013b902)
feat(order/rel_iso): generalise several lemmas to assume only has_le not preorder ([#5858](https://github.com/leanprover-community/mathlib/pull/5858))

### [2021-01-23 02:17:47](https://github.com/leanprover-community/mathlib/commit/b0e874e)
chore(scripts): update nolints.txt ([#5856](https://github.com/leanprover-community/mathlib/pull/5856))
I am happy to remove some nolints for you!

### [2021-01-22 21:50:00](https://github.com/leanprover-community/mathlib/commit/04972f6)
docs(undergrad.yaml): update with [#5724](https://github.com/leanprover-community/mathlib/pull/5724) and [#5788](https://github.com/leanprover-community/mathlib/pull/5788) ([#5855](https://github.com/leanprover-community/mathlib/pull/5855))
Add results from a couple of recent PRs.  Also correct an apparent oversight from the translation of the file.

### [2021-01-22 17:20:38](https://github.com/leanprover-community/mathlib/commit/3250fc3)
feat(analysis/mean_inequalities, measure_theory/lp_space): extend mem_Lp.add to all p in ennreal ([#5828](https://github.com/leanprover-community/mathlib/pull/5828))
Show `(a ^ q + b ^ q) ^ (1/q) ≤ (a ^ p + b ^ p) ^ (1/p)` for `a,b : ennreal` and `0 < p <= q`.
Use it to show that for `p <= 1`, if measurable functions `f` and `g` are in Lp, `f+g` is also in Lp (the case `1 <= p` is already done).

### [2021-01-22 16:01:54](https://github.com/leanprover-community/mathlib/commit/f48ce7e)
feat(algebra/lie/basic): define the radical of a Lie algebra and prove it is solvable ([#5833](https://github.com/leanprover-community/mathlib/pull/5833))

### [2021-01-22 12:52:31](https://github.com/leanprover-community/mathlib/commit/cb618e0)
feat(analysis/analytic): a continuous linear map defines an analytic function ([#5840](https://github.com/leanprover-community/mathlib/pull/5840))
Also add convenience lemmas with conclusion `radius = ⊤`.

### [2021-01-22 12:52:30](https://github.com/leanprover-community/mathlib/commit/faba9ce)
chore(algebra/group_power): generalize `semiring` version of Bernoulli's inequality ([#5831](https://github.com/leanprover-community/mathlib/pull/5831))
Now `one_add_mul_le_pow'` assumes `0 ≤ a * a`, `0 ≤ (1 + a) * (1 +
a)`, and `0 ≤ 2 + a`.
Also add a couple of convenience lemmas.

### [2021-01-22 12:52:28](https://github.com/leanprover-community/mathlib/commit/0feb1d2)
feat(measure_theory/interval_integral) : add integration by parts ([#5724](https://github.com/leanprover-community/mathlib/pull/5724))
A direct application of FTC-2 for interval_integral.

### [2021-01-22 12:52:26](https://github.com/leanprover-community/mathlib/commit/de10203)
feat(order/modular_lattice): define modular lattices ([#5564](https://github.com/leanprover-community/mathlib/pull/5564))
Defines modular lattices
Defines the diamond isomorphisms in a modular lattice
Places `is_modular_lattice` instances on a `distrib_lattice`, the lattice of `subgroup`s of a `comm_group`, and the lattice of `submodule`s of a `module`.

### [2021-01-22 09:40:49](https://github.com/leanprover-community/mathlib/commit/38ae9b3)
chore(data/nat/basic): reuse a proof, drop a duplicate ([#5836](https://github.com/leanprover-community/mathlib/pull/5836))
Drop `nat.div_mul_le_self'`, use `nat.div_mul_le_self` instead.

### [2021-01-22 07:39:51](https://github.com/leanprover-community/mathlib/commit/8b4c455)
feat(data/polynomial/algebra_map): aeval_map ([#5843](https://github.com/leanprover-community/mathlib/pull/5843))
Proves `aeval_map`, which relates `aeval` within an `is_scalar_tower`.

### [2021-01-22 06:16:16](https://github.com/leanprover-community/mathlib/commit/bef50a4)
feat(field_theory/minpoly): Minimal polynomials of degree one ([#5844](https://github.com/leanprover-community/mathlib/pull/5844))
If the minimal polynomial has degree one then the element in question lies in the base ring.

### [2021-01-22 04:19:57](https://github.com/leanprover-community/mathlib/commit/6958d8c)
feat(topology/metric_space/{basic,emetric_space}): product of balls of the same size ([#5846](https://github.com/leanprover-community/mathlib/pull/5846))

### [2021-01-22 02:55:27](https://github.com/leanprover-community/mathlib/commit/244b3ed)
chore(scripts): update nolints.txt ([#5841](https://github.com/leanprover-community/mathlib/pull/5841))
I am happy to remove some nolints for you!

### [2021-01-21 23:47:37](https://github.com/leanprover-community/mathlib/commit/c681f48)
chore(analysis/analytic/composition): minor golfing ([#5839](https://github.com/leanprover-community/mathlib/pull/5839))

### [2021-01-21 23:47:32](https://github.com/leanprover-community/mathlib/commit/228c00b)
feat(computability/language): le on languages ([#5704](https://github.com/leanprover-community/mathlib/pull/5704))

### [2021-01-21 20:47:04](https://github.com/leanprover-community/mathlib/commit/b2ca761)
chore(algebra/group_power): add `(a+b)^2=a^2+2ab+b^2` ([#5838](https://github.com/leanprover-community/mathlib/pull/5838))
Also generalize 2 lemmas from `comm_semiring` to `semiring`.

### [2021-01-21 18:59:17](https://github.com/leanprover-community/mathlib/commit/fac0f25)
fix(tactic/default): make field_simp work with import tactic ([#5832](https://github.com/leanprover-community/mathlib/pull/5832))

### [2021-01-21 14:01:20](https://github.com/leanprover-community/mathlib/commit/b52b304)
feat(algebra/lie/basic): show `I + J` is solvable if Lie ideals `I`, `J` are solvable ([#5819](https://github.com/leanprover-community/mathlib/pull/5819))
The key result is `lie_algebra.is_solvable_add`

### [2021-01-21 11:18:02](https://github.com/leanprover-community/mathlib/commit/3ef8281)
fix(group_theory/group_action/defs): fix minor typo ([#5827](https://github.com/leanprover-community/mathlib/pull/5827))
heirarchy -> hierarchy

### [2021-01-21 11:17:59](https://github.com/leanprover-community/mathlib/commit/b3a2112)
chore(algebra/group/conj): move `conj_injective` and use existing proofs ([#5798](https://github.com/leanprover-community/mathlib/pull/5798))

### [2021-01-21 11:17:58](https://github.com/leanprover-community/mathlib/commit/d66d563)
feat(measure_theory/interval_integral): FTC-2 for the open set ([#5733](https://github.com/leanprover-community/mathlib/pull/5733))
A follow-up to [#4945](https://github.com/leanprover-community/mathlib/pull/4945). I replaced `integral_eq_sub_of_has_deriv_at'` with a stronger version that holds for functions that have a derivative on an `Ioo` (as opposed to an `Ico`). Inspired by [this](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/FTC-2.20on.20open.20set/near/222177308) conversation on Zulip.
I also emended docstrings to reflect changes made in [#5647](https://github.com/leanprover-community/mathlib/pull/5647).

### [2021-01-21 08:15:25](https://github.com/leanprover-community/mathlib/commit/ce9bc68)
feat(ring_theory/polynomial): symmetric polynomials and elementary symmetric polynomials ([#5788](https://github.com/leanprover-community/mathlib/pull/5788))
Define symmetric polynomials and elementary symmetric polynomials, and prove some basic facts about them.

### [2021-01-21 02:18:43](https://github.com/leanprover-community/mathlib/commit/a19e48b)
chore(scripts): update nolints.txt ([#5826](https://github.com/leanprover-community/mathlib/pull/5826))
I am happy to remove some nolints for you!

### [2021-01-20 22:33:10](https://github.com/leanprover-community/mathlib/commit/b2d95c0)
feat(data/nat/modeq): Generalised version of the Chinese remainder theorem ([#5683](https://github.com/leanprover-community/mathlib/pull/5683))
That allows the moduli to not be coprime, assuming the necessary condition. Old crt is now in terms of this one

### [2021-01-20 19:25:37](https://github.com/leanprover-community/mathlib/commit/8b6f541)
feat(field_theory/normal): Splitting field is normal ([#5768](https://github.com/leanprover-community/mathlib/pull/5768))
Proves that splitting fields are normal.

### [2021-01-20 16:12:42](https://github.com/leanprover-community/mathlib/commit/7c89265)
chore(data/list/range): Add range_zero and rename range_concat to range_succ ([#5821](https://github.com/leanprover-community/mathlib/pull/5821))
The name `range_concat` was derived from `range'_concat`, where there are multiple possible expansions for `range' s n.succ`.
For `range` there is only one choice, and naming the lemma after the result rather than the statement makes it harder to find.

### [2021-01-20 14:40:22](https://github.com/leanprover-community/mathlib/commit/2ec396a)
chore(data/dfinsupp): add `dfinsupp.prod_comm` ([#5817](https://github.com/leanprover-community/mathlib/pull/5817))
This is the same lemma as `finsupp.prod_comm` but for dfinsupp

### [2021-01-20 11:51:00](https://github.com/leanprover-community/mathlib/commit/9cdffe9)
refactor(data/fin): shorter proof of `mk.inj_iff` ([#5811](https://github.com/leanprover-community/mathlib/pull/5811))
Co-authors: `lean-gptf`, Yuhuai Wu

### [2021-01-20 11:50:58](https://github.com/leanprover-community/mathlib/commit/c700791)
feat(data/list/range): nth_le_fin_range ([#5456](https://github.com/leanprover-community/mathlib/pull/5456))

### [2021-01-20 11:50:56](https://github.com/leanprover-community/mathlib/commit/9ae3317)
feat(data/fin): add_comm_monoid and simp lemmas ([#5010](https://github.com/leanprover-community/mathlib/pull/5010))
Provide `add_comm_monoid` for `fin (n + 1)`, which makes proofs that have to do with `bit0`, `bit1`, and `nat.cast` and related happy. Provide the specialized lemmas as simp lemmas. Also provide various simp lemmas about multiplication, but without the associated `comm_monoid`.

### [2021-01-20 09:51:08](https://github.com/leanprover-community/mathlib/commit/a7a4f34)
feat(algebraic_geometry/is_open_comap_C): add file is_open_comap_C, prove that Spec R[x] \to Spec R is an open map ([#5693](https://github.com/leanprover-community/mathlib/pull/5693))
This file is the first part of a proof of Chevalley's Theorem.  It contains a proof that the morphism Spec R[x] \to Spec R is open.  In a later PR, I hope to prove that, under the same morphism, the image of a closed set is constructible.

### [2021-01-20 08:32:57](https://github.com/leanprover-community/mathlib/commit/0c57d1e)
feat(category_theory/monad): algebras for the coproduct monad ([#5679](https://github.com/leanprover-community/mathlib/pull/5679))
WIP, I'll fix it up when the dependent PRs merge
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->
- [x] depends on: [#5674](https://github.com/leanprover-community/mathlib/pull/5674)
- [x] depends on: [#5677](https://github.com/leanprover-community/mathlib/pull/5677) 
- [x] depends on: [#5678](https://github.com/leanprover-community/mathlib/pull/5678)

### [2021-01-20 06:40:59](https://github.com/leanprover-community/mathlib/commit/e41b917)
feat(char_p/quotient): Add a lemma to inherit char_p from the underlying ring ([#5809](https://github.com/leanprover-community/mathlib/pull/5809))

### [2021-01-20 06:40:57](https://github.com/leanprover-community/mathlib/commit/385173d)
feat(ring_theory/ideal/operations): generalize quotient of algebras ([#5802](https://github.com/leanprover-community/mathlib/pull/5802))
I generalize [#5703](https://github.com/leanprover-community/mathlib/pull/5703) (that was merged earlier today... sorry for that, I should have thought more carefully about it) to be able to work with `S/I` as an `R`-algebra, where `S` is an `R`-algebra.  (In [#5703](https://github.com/leanprover-community/mathlib/pull/5703) only `R/I` was considered.) The proofs are the same.

### [2021-01-20 06:40:55](https://github.com/leanprover-community/mathlib/commit/31fd5b5)
feat(category_theory/limits): preserve monomorphisms ([#5801](https://github.com/leanprover-community/mathlib/pull/5801))
A functor which preserves pullbacks also preserves monomorphisms.

### [2021-01-20 04:42:11](https://github.com/leanprover-community/mathlib/commit/a3ef65d)
feat(algebra/lie/basic): additional lemmas concerning `lie_algebra.derived_series_of_ideal` ([#5815](https://github.com/leanprover-community/mathlib/pull/5815))

### [2021-01-20 03:20:26](https://github.com/leanprover-community/mathlib/commit/b1d5673)
chore(scripts): update nolints.txt ([#5816](https://github.com/leanprover-community/mathlib/pull/5816))
I am happy to remove some nolints for you!

### [2021-01-20 00:07:09](https://github.com/leanprover-community/mathlib/commit/d7a8709)
chore(algebra/group/hom): Add `mk_coe` lemmas ([#5812](https://github.com/leanprover-community/mathlib/pull/5812))
These are the counterparts to the `coe_mk` lemmas.

### [2021-01-19 21:59:16](https://github.com/leanprover-community/mathlib/commit/b121429)
feat(measure_theory/lp_space): extend the definition of Lp seminorm to p ennreal ([#5808](https://github.com/leanprover-community/mathlib/pull/5808))
Rename the seminorm with real exponent to `snorm'`, introduce `snorm_ess_sup` for `L\infty`, equal to the essential supremum of the norm.

### [2021-01-19 18:42:43](https://github.com/leanprover-community/mathlib/commit/9d14a5f)
chore(order/filter/basic): add `eventually_eq.rfl` and `eventually_le.rfl` ([#5805](https://github.com/leanprover-community/mathlib/pull/5805))

### [2021-01-19 18:42:41](https://github.com/leanprover-community/mathlib/commit/21b0b01)
feat(analysis/normed_space,topology/metric_space): distance between diagonal vectors ([#5803](https://github.com/leanprover-community/mathlib/pull/5803))
Add formulas for (e|nn|)dist between `λ _, a` and `λ _, b` as well
as `∥(λ _, a)∥` and `nnnorm (λ _, a)`.

### [2021-01-19 17:22:05](https://github.com/leanprover-community/mathlib/commit/da6e3c3)
feat(data/buffer/parser/numeral): numeral parser defs ([#5462](https://github.com/leanprover-community/mathlib/pull/5462))

### [2021-01-19 13:11:48](https://github.com/leanprover-community/mathlib/commit/8b47563)
chore(category_theory/adjunction): move reflective functor lemmas ([#5800](https://github.com/leanprover-community/mathlib/pull/5800))
Moves a lemma and describes a generalisation.

### [2021-01-19 13:11:46](https://github.com/leanprover-community/mathlib/commit/90763c4)
feat(algebra/lie/basic): generalise the definition of `lie_algebra.derived_series` ([#5794](https://github.com/leanprover-community/mathlib/pull/5794))
This generalisation will make it easier to relate properties of the derived
series of a Lie algebra and the derived series of its ideals (regarded as Lie
algebras in their own right).
The key definition is `lie_algebra.derived_series_of_ideal` and the key result is `lie_ideal.derived_series_eq_bot_iff`.

### [2021-01-19 13:11:44](https://github.com/leanprover-community/mathlib/commit/18841a9)
feat(data/list/basic): nth and nth_le for pmap ([#5451](https://github.com/leanprover-community/mathlib/pull/5451))

### [2021-01-19 13:11:42](https://github.com/leanprover-community/mathlib/commit/9777d1e)
feat(data/option/basic): map_bind and join_pmap lemmas ([#5445](https://github.com/leanprover-community/mathlib/pull/5445))

### [2021-01-19 11:40:25](https://github.com/leanprover-community/mathlib/commit/c37c64f)
chore(data/matrix/notation): Add some missing simp lemmas for sub, head, and tail ([#5807](https://github.com/leanprover-community/mathlib/pull/5807))

### [2021-01-19 03:39:22](https://github.com/leanprover-community/mathlib/commit/190dd10)
chore(analysis/normed_space): golf some proofs ([#5804](https://github.com/leanprover-community/mathlib/pull/5804))
* add `pi_norm_lt_iff`;
* add `has_sum.norm_le_of_bounded`;
* add `multilinear_map.bound_of_shell`;
* rename `continuous_multilinear_map.norm_image_sub_le_of_bound` to
  `continuous_multilinear_map.norm_image_sub_le`, same with prime
  version;
* golf some proofs.

### [2021-01-19 02:19:31](https://github.com/leanprover-community/mathlib/commit/c9c3b6f)
chore(scripts): update nolints.txt ([#5806](https://github.com/leanprover-community/mathlib/pull/5806))
I am happy to remove some nolints for you!

### [2021-01-18 23:02:32](https://github.com/leanprover-community/mathlib/commit/541688b)
feat(combinatorics/simple_graph/basic): add lemmas about cardinality of common neighbor set ([#5789](https://github.com/leanprover-community/mathlib/pull/5789))
Add lemmas about the cardinality of the set of common neighbors between two vertices. Add note in module docstring about naming convention. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs.

### [2021-01-18 23:02:30](https://github.com/leanprover-community/mathlib/commit/77003ce)
refactor(field_theory|ring_theory|linear_algebra): minpoly A x ([#5774](https://github.com/leanprover-community/mathlib/pull/5774))
This PR refactors the definition of `minpoly` to
```
noncomputable def minpoly (x : B) : polynomial A := if hx : is_integral
A x then well_founded.min degree_lt_wf _ hx else 0
```
The benefit is that we can write `minpoly A x` instead of
`minpoly hx` for `hx : is_integral A x`. The resulting code is more
readable, and some lemmas are true without the `hx` assumption.

### [2021-01-18 19:33:02](https://github.com/leanprover-community/mathlib/commit/725efb1)
doc(tactic/rewrite): Add an example for assoc_rw ([#5799](https://github.com/leanprover-community/mathlib/pull/5799))

### [2021-01-18 17:54:03](https://github.com/leanprover-community/mathlib/commit/b5e832e)
refactor(algebraic_geometry/prime_spectrum): simplify `comap_id`, `comap_comp` ([#5796](https://github.com/leanprover-community/mathlib/pull/5796))
faster proofs and smaller proof terms
Co-authors: `lean-gptf`, Yuhuai Wu

### [2021-01-18 15:57:43](https://github.com/leanprover-community/mathlib/commit/57bc1da)
feat(order/limsup_liminf, order/filter/ennreal): add properties of limsup for ennreal-valued functions ([#5746](https://github.com/leanprover-community/mathlib/pull/5746))

### [2021-01-18 10:20:56](https://github.com/leanprover-community/mathlib/commit/66e955e)
feat(algebra/lie/basic): results relating Lie algebra morphisms and ideal operations ([#5778](https://github.com/leanprover-community/mathlib/pull/5778))
The key results are `lie_ideal.comap_bracket_eq` and its corollary `lie_ideal.comap_bracket_incl`

### [2021-01-18 08:58:39](https://github.com/leanprover-community/mathlib/commit/9381e37)
doc(data/buffer/parser/basic): fix typo ([#5792](https://github.com/leanprover-community/mathlib/pull/5792))

### [2021-01-18 07:03:48](https://github.com/leanprover-community/mathlib/commit/8ab1a39)
chore(field_theory/minpoly): meaningful variable names ([#5773](https://github.com/leanprover-community/mathlib/pull/5773))

### [2021-01-18 07:03:45](https://github.com/leanprover-community/mathlib/commit/db617b3)
feat(ring_theory/ideal/operations): add algebra structure on quotient ([#5703](https://github.com/leanprover-community/mathlib/pull/5703))
I added very basic stuff about `R/I` as an `R`-algebra that are missing in mathlib.

### [2021-01-18 05:44:26](https://github.com/leanprover-community/mathlib/commit/f3d3d04)
chore(category_theory/monad): golf and lint monadic adjunctions ([#5769](https://github.com/leanprover-community/mathlib/pull/5769))
Some lintfixes and proof golfing using newer API

### [2021-01-18 03:26:01](https://github.com/leanprover-community/mathlib/commit/3089b16)
chore(scripts): update nolints.txt ([#5790](https://github.com/leanprover-community/mathlib/pull/5790))
I am happy to remove some nolints for you!

### [2021-01-18 00:03:46](https://github.com/leanprover-community/mathlib/commit/2f824aa)
feat(data/option/*): pmap and pbind defs and lemmas ([#5442](https://github.com/leanprover-community/mathlib/pull/5442))

### [2021-01-17 21:46:49](https://github.com/leanprover-community/mathlib/commit/c3639e9)
refactor(algebra/monoid_algebra) generalize from group to monoid algebras ([#5785](https://github.com/leanprover-community/mathlib/pull/5785))
There was a TODO in the monoid algebra file to generalize three statements from group to monoid algebras. It seemed to be solvable by just changing the assumptions, not the proofs.

### [2021-01-17 14:43:58](https://github.com/leanprover-community/mathlib/commit/f29d1c3)
refactor(analysis/calculus/deriv): simpler proof of `differentiable_at.div_const` ([#5782](https://github.com/leanprover-community/mathlib/pull/5782))
Co-authors: `lean-gptf`, Yuhuai Wu

### [2021-01-17 14:43:56](https://github.com/leanprover-community/mathlib/commit/83d44a3)
hack(manifold): disable subsingleton instances to speed up simp ([#5779](https://github.com/leanprover-community/mathlib/pull/5779))
Simp takes an enormous amount of time in manifold code looking for subsingleton instances (and in fact probably in the whole library, but manifolds are particularly simp-heavy). We disable two such instances in the `manifold` locale, to get serious speedups (for instance, `times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` goes down from 27s to 10s on my computer).
This is *not* a proper fix. But it already makes a serious difference in this part of the library..
Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.235672.20breaks.20timeout/near/223001979

### [2021-01-17 11:37:27](https://github.com/leanprover-community/mathlib/commit/bf46986)
doc(tactic/auto_cases): fix typo ([#5784](https://github.com/leanprover-community/mathlib/pull/5784))

### [2021-01-17 08:33:51](https://github.com/leanprover-community/mathlib/commit/289df3a)
feat(data/set/lattice): add lemmas set.Union_subtype and set.Union_of_singleton_coe ([#5691](https://github.com/leanprover-community/mathlib/pull/5691))
Add one simp lemma, following a suggestion on the Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/image_bUnion

### [2021-01-17 03:47:19](https://github.com/leanprover-community/mathlib/commit/2c4a516)
chore(topology/metric_space/isometry): a few more lemmas ([#5780](https://github.com/leanprover-community/mathlib/pull/5780))
Also reuse more proofs about `inducing` and `quotient_map` in
`topology/homeomorph`.
Non-bc change: rename `isometric.range_coe` to
`isometric.range_eq_univ` to match `equiv.range_eq_univ`.

### [2021-01-17 02:21:15](https://github.com/leanprover-community/mathlib/commit/00e1f4c)
chore(scripts): update nolints.txt ([#5781](https://github.com/leanprover-community/mathlib/pull/5781))
I am happy to remove some nolints for you!

### [2021-01-17 00:33:57](https://github.com/leanprover-community/mathlib/commit/dec44fe)
chore(group_theory/perm/{sign,cycles}): renaming for dot notation, linting, formatting ([#5777](https://github.com/leanprover-community/mathlib/pull/5777))
Declarations renamed in `group_theory/perm/sign.lean` (all of these are under `equiv.perm`):
- `disjoint_mul_comm` -> `disjoint.mul_comm`
- `disjoint_mul_left` -> `disjoint.mul_left`
- `disjoint_mul_right` -> `disjoint.mul_right`
- `is_swap_of_subtype` -> `is_swap.of_subtype_is_swap`
- `sign_eq_of_is_swap` -> `is_swap.sign_eq`
Declarations renamed in `group_theory/perm/cycles.lean` (all of these are under `equiv.perm`):
- `is_cycle_swap` -> `is_cycle.swap`
- `is_cycle_inv` -> `is_cycle.inv`
- `exists_gpow_eq_of_is_cycle` -> `is_cycle.exists_gpow_eq`
- `exists_pow_eq_of_is_cycle` -> `is_cycle.exists_pow_eq`
- `eq_swap_of_is_cycle_of_apply_apply_eq_self` -> `eq_swap_of_apply_apply_eq_self`
- `is_cycle_swap_mul` -> `is_cycle.swap_mul`
- `sign_cycle` -> `is_cycle.sign`
- `apply_eq_self_iff_of_same_cycle` -> `same_cycle.apply_eq_self_iff`
- `same_cycle_of_is_cycle` -> `is_cycle.same_cycle`
- `cycle_of_apply_of_same_cycle` -> `same_cycle.cycle_of_apply`
- `cycle_of_cycle` -> `is_cycle.cycle_of_eq`
I also added a basic module doc string to `group_theory/perm/cycles.lean`.

### [2021-01-17 00:33:55](https://github.com/leanprover-community/mathlib/commit/a2630fc)
chore(field_theory|ring_theory|linear_algebra): rename minimal_polynomial to minpoly ([#5771](https://github.com/leanprover-community/mathlib/pull/5771))
This PR renames:
* `minimal_polynomial` -> `minpoly`
* a similar substitution throughout the library for all names containing the substring `minimal_polynomial`
* `fixed_points.minpoly.minimal_polynomial` -> `fixed_points.minpoly_eq_minpoly`
This PR moves a file:
  src/field_theory/minimal_polynomial.lean -> src/field_theory/minpoly.lean

### [2021-01-16 23:11:28](https://github.com/leanprover-community/mathlib/commit/0cc93a1)
feat(category_theory/is_filtered): is_filtered_of_equiv ([#5485](https://github.com/leanprover-community/mathlib/pull/5485))
If `C` is filtered and there is a right adjoint functor `C => D`, then `D` is filtered. Also a category equivalent to a filtered category is filtered.

### [2021-01-16 21:37:58](https://github.com/leanprover-community/mathlib/commit/787e6b3)
feat(measure_theory/haar_measure): Prove uniqueness ([#5663](https://github.com/leanprover-community/mathlib/pull/5663))
Prove the uniqueness of Haar measure (up to a scalar) following  *Measure Theory* by Paul Halmos. This proof seems to contain an omission which we fix by adding an extra hypothesis to an intermediate lemma.
Add some lemmas about left invariant regular measures.
We add the file `measure_theory.prod_group` which contain various measure-theoretic properties of products of topological groups, needed for the uniqueness.
We add `@[to_additive]` to some declarations in `measure_theory`, but leave it out for many because of [#4210](https://github.com/leanprover-community/mathlib/pull/4210). This causes some renamings in concepts, like `is_left_invariant` -> `is_mul_left_invariant` and `measure.conj` -> `measure.inv` (though a better naming suggestion for this one is welcome).

### [2021-01-16 19:32:30](https://github.com/leanprover-community/mathlib/commit/23373d1)
chore(category_theory/limits): coproduct functor ([#5677](https://github.com/leanprover-community/mathlib/pull/5677))
Dualises a def already there.

### [2021-01-16 17:42:15](https://github.com/leanprover-community/mathlib/commit/e0f4142)
refactor(data/nat/fib): explicitly state fibonacci sequence is monotone ([#5776](https://github.com/leanprover-community/mathlib/pull/5776))
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/fib_mono

### [2021-01-16 17:42:12](https://github.com/leanprover-community/mathlib/commit/4155665)
refactor(linear_algebra/dual): replace dim<omega by finite_dimensional ([#5775](https://github.com/leanprover-community/mathlib/pull/5775))

### [2021-01-16 17:42:09](https://github.com/leanprover-community/mathlib/commit/d23dbfb)
feat(category_theory/adjunction): reflective functors ([#5680](https://github.com/leanprover-community/mathlib/pull/5680))
Extract reflective functors from monads, and show some properties of them

### [2021-01-16 17:42:07](https://github.com/leanprover-community/mathlib/commit/64abe5a)
feat(category_theory/sites): closed sieves ([#5282](https://github.com/leanprover-community/mathlib/pull/5282))
- closed sieves
- closure of a sieve
- subobject classifier in Sheaf (without proof of universal property)
- equivalent sheaf condition iff same topology
- closure operator induces topology

### [2021-01-16 15:21:08](https://github.com/leanprover-community/mathlib/commit/e076a9c)
chore(topology/metric_space/gluing): use `⨅` notation ([#5772](https://github.com/leanprover-community/mathlib/pull/5772))
Also use `exists_lt_of_cinfi_lt` to golf one proof.

### [2021-01-16 15:21:06](https://github.com/leanprover-community/mathlib/commit/ba5d1f6)
feat(linear_algebra/basic): add comap span lemmas ([#5744](https://github.com/leanprover-community/mathlib/pull/5744))
We already had `map_span` but nothing for `comap`.

### [2021-01-16 15:21:04](https://github.com/leanprover-community/mathlib/commit/bd57804)
feat(algebraic_geometry/prime_spectrum): add lemma zero_locus_bUnion ([#5692](https://github.com/leanprover-community/mathlib/pull/5692))
Add a simple extension of a lemma, to be able to work with `bUnion`, instead of only `Union`.

### [2021-01-16 11:02:21](https://github.com/leanprover-community/mathlib/commit/55d5564)
feat(ring_theory/jacobson): Generalize proofs about Jacobson rings and polynomials ([#5520](https://github.com/leanprover-community/mathlib/pull/5520))
These changes are meant to make deriving the classical nullstellensatz from the generalized version about Jacobson rings much easier and much more direct.
`is_integral_localization_map_polynomial_quotient` already exists in the proof of a previous theorem, and this just pulls it out into an independent lemma.
`polynomial.quotient_mk_comp_C_is_integral_of_jacobson` and `mv_polynomial.quotient_mk_comp_C_is_integral_of_jacobson` are the two main new statements, most of the rest of the changes are just generalizations and reorganizations of the existing theorems.

### [2021-01-16 11:02:18](https://github.com/leanprover-community/mathlib/commit/05e7be9)
feat(algebra/category/Module): direct limit is a colimit ([#4756](https://github.com/leanprover-community/mathlib/pull/4756))

### [2021-01-16 09:11:40](https://github.com/leanprover-community/mathlib/commit/f03f5a9)
feat(ring_theory/algebra_tower): Restriction of adjoin ([#5767](https://github.com/leanprover-community/mathlib/pull/5767))
Two technical lemmas about restricting `algebra.adjoin` within an `is_scalar_tower`.

### [2021-01-16 09:11:38](https://github.com/leanprover-community/mathlib/commit/e95988a)
feat(field_theory/adjoin): Inductively construct algebra homomorphism ([#5765](https://github.com/leanprover-community/mathlib/pull/5765))
The lemma `alg_hom_mk_adjoin_splits` can be viewed as lifting an embedding F -> K to an embedding F(S) -> K.

### [2021-01-16 09:11:36](https://github.com/leanprover-community/mathlib/commit/9acd349)
feat(order/closure): closure operator from galois connection ([#5764](https://github.com/leanprover-community/mathlib/pull/5764))
Construct a closure operator from a galois connection

### [2021-01-16 09:11:34](https://github.com/leanprover-community/mathlib/commit/51ffdd0)
refactor(ring_theory): change field instance on adjoin_root ([#5759](https://github.com/leanprover-community/mathlib/pull/5759))
This makes some things faster.
[Discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Slow.20instance/near/222839607)

### [2021-01-16 09:11:32](https://github.com/leanprover-community/mathlib/commit/dffb09a)
feat(linear_algebra/{clifford,exterior,tensor,free}_algebra): provide canonical images from larger algebras into smaller ones ([#5745](https://github.com/leanprover-community/mathlib/pull/5745))
This adds:
* `free_algebra.to_tensor`
* `tensor_algebra.to_exterior`
* `tensor_algebra.to_clifford`
Providing the injection in the other direction is more challenging, so is left as future work.

### [2021-01-16 09:11:30](https://github.com/leanprover-community/mathlib/commit/bea7651)
feat(category_theory/monad): construct isomorphisms of algebras ([#5678](https://github.com/leanprover-community/mathlib/pull/5678))

### [2021-01-16 03:57:08](https://github.com/leanprover-community/mathlib/commit/592edb6)
chore(scripts): update nolints.txt ([#5763](https://github.com/leanprover-community/mathlib/pull/5763))
I am happy to remove some nolints for you!

### [2021-01-16 03:57:02](https://github.com/leanprover-community/mathlib/commit/6351f01)
chore(algebra/group_with_zero): cleanup ([#5762](https://github.com/leanprover-community/mathlib/pull/5762))
* remove `classical,` from proofs: we have `open_locale classical` anyway;
* add a lemma `a / (a * a) = a⁻¹`, use it to golf some proofs in other files.

### [2021-01-16 03:57:00](https://github.com/leanprover-community/mathlib/commit/798024a)
chore(data/real/*): rename `le_of_forall_epsilon_le` to `le_of_forall_pos_le_add` ([#5761](https://github.com/leanprover-community/mathlib/pull/5761))
* generalize the `real` version to a `linear_ordered_add_comm_group`;
* rename `nnreal` and `ennreal` versions.

### [2021-01-16 00:47:54](https://github.com/leanprover-community/mathlib/commit/78493c9)
feat(data/nat/modeq): add missing lemmas for int and nat regarding dvd ([#5752](https://github.com/leanprover-community/mathlib/pull/5752))
Adding lemmas `(a+b)/c=a/c+b/c` if `c` divides `a` for `a b c : nat` and `a b c : int` after discussion on Zulip https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/nat_add_div

### [2021-01-16 00:47:52](https://github.com/leanprover-community/mathlib/commit/e4da493)
feat(group_theory/perm/sign): exists_pow_eq_of_is_cycle ([#5665](https://github.com/leanprover-community/mathlib/pull/5665))
Slight generalization of `exists_gpow_eq_of_is_cycle` in the case of a cycle on a finite set.
Also move the following from `group_theory/perm/sign.lean` to `group_theory/perm/cycles.lean`:
- is_cycle
- is_cycle_swap
- is_cycle_inv
- exists_gpow_eq_of_is_cycle
- is_cycle_swap_mul_aux₁
- is_cycle_swap_mul_aux₂
- eq_swap_of_is_cycle_of_apply_apply_eq_self
- is_cycle_swap_mul
- sign_cycle

### [2021-01-15 21:05:36](https://github.com/leanprover-community/mathlib/commit/d43f202)
feat(analysis/analytic/basic): `f (x + y) - p.partial_sum n y = O(∥y∥ⁿ)` ([#5756](https://github.com/leanprover-community/mathlib/pull/5756))
### Lemmas about analytic functions
* add `has_fpower_series_on_ball.uniform_geometric_approx'`, a more
  precise version of `has_fpower_series_on_ball.uniform_geometric_approx`;
* add `has_fpower_series_at.is_O_sub_partial_sum_pow`, a version of
  the Taylor formula for an analytic function;
### Lemmas about `homeomorph` and topological groups
* add `simp` lemmas `homeomorph.coe_mul_left` and
  `homeomorph.mul_left_symm`;
* add `map_mul_left_nhds` and `map_mul_left_nhds_one`;
* add `homeomorph.to_equiv_injective` and `homeomorph.ext`;
### Lemmas about `is_O`/`is_o`
* add `simp` lemmas `asymptotics.is_O_with_map`,
  `asymptotics.is_O_map`, and `asymptotics.is_o_map`;
* add `asymptotics.is_o_norm_pow_norm_pow` and
  `asymptotics.is_o_norm_pow_id`;
### Misc changes
* rename `div_le_iff_of_nonneg_of_le` to `div_le_of_nonneg_of_le_mul`;
* add `continuous_linear_map.op_norm_le_of_nhds_zero`;
* golf some proofs.

### [2021-01-15 21:05:34](https://github.com/leanprover-community/mathlib/commit/bc5d5c9)
feat(data/matrix/notation,data/fin): head and append simp ([#5741](https://github.com/leanprover-community/mathlib/pull/5741))

### [2021-01-15 21:05:30](https://github.com/leanprover-community/mathlib/commit/0104948)
feat(order/atoms): further facts about atoms, coatoms, and simple lattices ([#5493](https://github.com/leanprover-community/mathlib/pull/5493))
Provides possible instances of `bounded_distrib_lattice`, `boolean_algebra`, `complete_lattice`, and `complete_boolean_algebra` on a simple lattice
Relates the `is_atom` and `is_coatom` conditions to `is_simple_lattice` structures on intervals
Shows that all three conditions are preserved by `order_iso`s
Adds more instances on `bool`, including `is_simple_lattice`

### [2021-01-15 17:48:45](https://github.com/leanprover-community/mathlib/commit/bc94d05)
fix(algebra/ordered_monoid): Ensure that `ordered_cancel_comm_monoid` can provide a `cancel_comm_monoid` instance ([#5713](https://github.com/leanprover-community/mathlib/pull/5713))

### [2021-01-15 16:03:27](https://github.com/leanprover-community/mathlib/commit/8b4b941)
feat(data/mv_polynomial): stronger `degrees_X` for `nontrivial R` ([#5758](https://github.com/leanprover-community/mathlib/pull/5758))
Also rename `degrees_X` to `degrees_X'` and mark `degrees_{zero,one}` with `simp`.

### [2021-01-15 14:40:09](https://github.com/leanprover-community/mathlib/commit/c347c75)
feat(algebra/lie/basic): add a few `simp` lemmas ([#5757](https://github.com/leanprover-community/mathlib/pull/5757))

### [2021-01-15 10:58:03](https://github.com/leanprover-community/mathlib/commit/ed0ae3e)
feat(analysis/calculus/inverse): a map that has an invertible strict derivative at every point is an open map ([#5753](https://github.com/leanprover-community/mathlib/pull/5753))
More generally, the same is true for a map that is a local homeomorphism near every point.

### [2021-01-15 10:58:01](https://github.com/leanprover-community/mathlib/commit/4c1d12f)
feat(data/complex/basic): Adding `im_eq_sub_conj` ([#5750](https://github.com/leanprover-community/mathlib/pull/5750))
Adds `im_eq_sub_conj`, which I couldn't find in the library.

### [2021-01-15 09:57:54](https://github.com/leanprover-community/mathlib/commit/94f45c7)
chore(linear_algebra/quadratic_form): Add missing simp lemmas about quadratic_form.polar ([#5748](https://github.com/leanprover-community/mathlib/pull/5748))

### [2021-01-15 08:35:59](https://github.com/leanprover-community/mathlib/commit/09c2345)
feat(category_theory/over): epis and monos in the over category ([#5684](https://github.com/leanprover-community/mathlib/pull/5684))

### [2021-01-15 08:35:56](https://github.com/leanprover-community/mathlib/commit/395eb2b)
feat(category_theory): subterminal objects ([#5669](https://github.com/leanprover-community/mathlib/pull/5669))

### [2021-01-15 08:35:54](https://github.com/leanprover-community/mathlib/commit/f8db86a)
feat(category_theory/limits): finite products from binary products ([#5516](https://github.com/leanprover-community/mathlib/pull/5516))
Adds constructions for finite products from binary products and terminal object, and a preserves version

### [2021-01-15 05:41:26](https://github.com/leanprover-community/mathlib/commit/faf106a)
refactor(data/real/{e,}nnreal): reuse generic lemmas ([#5751](https://github.com/leanprover-community/mathlib/pull/5751))
* reuse `div_eq_mul_inv` and `one_div` from `div_inv_monoid`;
* reuse lemmas about `group_with_zero` instead of repeating them in the `nnreal` namespace;
* add `has_sum.div_const`.

### [2021-01-15 05:41:24](https://github.com/leanprover-community/mathlib/commit/931182e)
chore(algebra/ordered_ring): add a few simp lemmas ([#5749](https://github.com/leanprover-community/mathlib/pull/5749))
* fix misleading names `neg_lt_iff_add_nonneg` → `neg_lt_iff_pos_add`,
  `neg_lt_iff_add_nonneg'` → `neg_lt_iff_pos_add'`;
* add `@[simp]` to `abs_mul_abs_self` and `abs_mul_self`;
* add lemmas `neg_le_self_iff`, `neg_lt_self_iff`, `le_neg_self_iff`,
  `lt_neg_self_iff`, `abs_eq_self`, `abs_eq_neg_self`.

### [2021-01-15 02:19:33](https://github.com/leanprover-community/mathlib/commit/5d003d8)
chore(scripts): update nolints.txt ([#5754](https://github.com/leanprover-community/mathlib/pull/5754))
I am happy to remove some nolints for you!

### [2021-01-15 02:19:31](https://github.com/leanprover-community/mathlib/commit/7151fb7)
chore(data/equiv/basic): equiv/perm_congr simp lemmas ([#5737](https://github.com/leanprover-community/mathlib/pull/5737))

### [2021-01-14 22:10:57](https://github.com/leanprover-community/mathlib/commit/64a1b19)
feat(data/equiv/basic): subsingleton equiv and perm ([#5736](https://github.com/leanprover-community/mathlib/pull/5736))

### [2021-01-14 22:10:54](https://github.com/leanprover-community/mathlib/commit/975f41a)
feat(order): closure operators ([#5524](https://github.com/leanprover-community/mathlib/pull/5524))
Adds closure operators on a partial order, as in [wikipedia](https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets). I made them bundled for no particular reason, I don't mind unbundling.

### [2021-01-14 19:06:18](https://github.com/leanprover-community/mathlib/commit/0817e7f)
feat(measure_theory): absolute continuity of the integral ([#5743](https://github.com/leanprover-community/mathlib/pull/5743))
### API changes:
#### `ennreal`s and `nnreal`s:
* `ennreal.mul_le_mul` and `ennreal.mul_lt_mul` are now `mono` lemmas;
* rename `ennreal.sub_lt_sub_self` to `ennreal.sub_lt_self`: there is no `-` in the RHS;
* new lemmas `enrneal.mul_div_le`, `nnreal.sub_add_eq_max`, and `nnreal.add_sub_eq_max`;
* add new lemma `ennreal.bsupr_add`, use in in the proof of `ennreal.Sup_add`;
#### Complete lattice
* new lemma `supr_lt_iff`;
#### Simple functions
* new lemmas `simple_func.exists_forall_le`, `simple_func.map_add`,
  `simple_func.sub_apply`;
* weaker typeclass assumptions in `simple_func.coe_sub`;
* `monotone_eapprox` is now a `mono` lemma;
#### Integration
* new lemmas `exists_simple_func_forall_lintegral_sub_lt_of_pos`,
  `exists_pos_set_lintegral_lt_of_measure_lt`,
  `tendsto_set_lintegral_zero`, and
  `has_finite_integral.tendsto_set_integral_nhds_zero`.

### [2021-01-14 19:06:16](https://github.com/leanprover-community/mathlib/commit/3b8cfdc)
feat(linear_algebra/{exterior,tensor,free}_algebra): provide left-inverses for `algebra_map` and `ι` ([#5722](https://github.com/leanprover-community/mathlib/pull/5722))
The strategy used for `algebra_map` here can't be used on `clifford_algebra` as the zero map does not satisfy `f m * f m = Q m`.

### [2021-01-14 15:25:47](https://github.com/leanprover-community/mathlib/commit/91b099e)
chore(data/equiv/fin): simp definitional lemmas ([#5740](https://github.com/leanprover-community/mathlib/pull/5740))

### [2021-01-14 15:25:44](https://github.com/leanprover-community/mathlib/commit/7e9094b)
feat(control/equiv_functor): simp defn lemmas and injectivity ([#5739](https://github.com/leanprover-community/mathlib/pull/5739))

### [2021-01-14 15:25:42](https://github.com/leanprover-community/mathlib/commit/e3cc92e)
chore(data/equiv/basic): swap symm and trans simp lemmas ([#5738](https://github.com/leanprover-community/mathlib/pull/5738))

### [2021-01-14 15:25:40](https://github.com/leanprover-community/mathlib/commit/de8b88f)
chore(group_theory/perm/sign): trans and symm simp ([#5735](https://github.com/leanprover-community/mathlib/pull/5735))

### [2021-01-14 15:25:37](https://github.com/leanprover-community/mathlib/commit/82532c1)
chore(data/set/basic): reuse some proofs about `boolean_algebra` ([#5728](https://github.com/leanprover-community/mathlib/pull/5728))
API changes:
* merge `set.compl_compl` with `compl_compl'`;
* add `is_compl.compl_eq_iff`, `compl_eq_top`, and `compl_eq_bot`;
* add `simp` attribute to `compl_le_compl_iff_le`;
* fix misleading name in `compl_le_iff_compl_le`, add a missing
  variant;
* add `simp` attribute to `compl_empty_iff` and `compl_univ_iff`;
* add `set.subset.eventually_le`.

### [2021-01-14 11:59:28](https://github.com/leanprover-community/mathlib/commit/3b3f9a2)
refactor(measure_theory): review def&API of the `dirac` measure ([#5732](https://github.com/leanprover-community/mathlib/pull/5732))
* use `set.indicator` instead of `⨆ a ∈ s, 1` in the definition.
* rename some theorems to `thm'`, add a version assuming
  `[measurable_singleton_class α]` but not
  `is_measurable s`/`measurable f` under the old name.
* rename some lemmas from `eventually` to `ae`.

### [2021-01-14 11:59:26](https://github.com/leanprover-community/mathlib/commit/8bc26d1)
feat(algebra/order): ne_iff_lt_iff_le
 
 ([#5731](https://github.com/leanprover-community/mathlib/pull/5731))

### [2021-01-14 08:39:13](https://github.com/leanprover-community/mathlib/commit/159542a)
chore(*): split some long lines ([#5742](https://github.com/leanprover-community/mathlib/pull/5742))

### [2021-01-14 07:15:46](https://github.com/leanprover-community/mathlib/commit/1509c29)
chore(archive/100-theorems-list): 83_friendship_graphs ([#5727](https://github.com/leanprover-community/mathlib/pull/5727))
Cleaned up some lint and put it in terms of the new `simple_graph.common_neighbors`.

### [2021-01-14 03:38:41](https://github.com/leanprover-community/mathlib/commit/c8c6d2e)
feat(ci): Emit error messages in a way understood by github ([#5726](https://github.com/leanprover-community/mathlib/pull/5726))
This uses the commands described [here](https://github.com/actions/toolkit/blob/master/docs/commands.md#log-level), for which [the implementation](https://github.com/actions/toolkit/blob/af821474235d3c5e1f49cee7c6cf636abb0874c4/packages/core/src/command.ts#L36-L94) provides a slightly clearer spec.
This means github now annotates broken lines, and highlights the error in red.
Originally I tried to implement this using "problem matchers", but these do not support multi-line error messages.
Supporting this in the linter is something that I'll leave for a follow-up PR.

### [2021-01-14 03:38:39](https://github.com/leanprover-community/mathlib/commit/d11d83a)
feat(measure_theory/lebesgue_measure): volume of a box in `ℝⁿ` ([#5635](https://github.com/leanprover-community/mathlib/pull/5635))

### [2021-01-14 02:21:22](https://github.com/leanprover-community/mathlib/commit/c050452)
chore(scripts): update nolints.txt ([#5730](https://github.com/leanprover-community/mathlib/pull/5730))
I am happy to remove some nolints for you!

### [2021-01-13 21:36:30](https://github.com/leanprover-community/mathlib/commit/71a3261)
feat(logic/basic): exists_eq simp lemmas without and.comm ([#5694](https://github.com/leanprover-community/mathlib/pull/5694))

### [2021-01-13 21:36:28](https://github.com/leanprover-community/mathlib/commit/6397e14)
feat(data/nat/cast): add nat.bin_cast for faster casting ([#5664](https://github.com/leanprover-community/mathlib/pull/5664))
[As suggested](https://github.com/leanprover-community/mathlib/pull/5462#discussion_r553226279) by @gebner.

### [2021-01-13 18:52:53](https://github.com/leanprover-community/mathlib/commit/69e9344)
feat(data/set/finite): add lemma with iff statement about when finite sets can be subsets ([#5725](https://github.com/leanprover-community/mathlib/pull/5725))
Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove statements about strongly regular graphs.
Co-author: @shingtaklam1324

### [2021-01-13 18:52:51](https://github.com/leanprover-community/mathlib/commit/0b9fbc4)
feat(combinatorics/simple_graph/basic): add definition of common neighbors and lemmas ([#5718](https://github.com/leanprover-community/mathlib/pull/5718))
Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs

### [2021-01-13 18:52:49](https://github.com/leanprover-community/mathlib/commit/7ce4717)
refactor(computability/reduce): define many-one degrees without parameter ([#2630](https://github.com/leanprover-community/mathlib/pull/2630))
The file `reduce.lean` defines many-one degrees for computable reductions.  At the moment every primcodable type `α` has a separate type of degrees `many_one_degree α`.  This is completely antithetical to the notion of degrees, which are introduced to classify problems up to many-one equivalence.
This PR defines a single `many_one_degree` type that lives in `Type 0`.  We use the `ulower` infrastructure from [#2574](https://github.com/leanprover-community/mathlib/pull/2574) which shows that every type is computably equivalent to a subset of natural numbers.  The function `many_one_degree.of` which assigns to every set of a primcodable type a degree is still universe polymorphic.  In particular, we show that `of p = of q ↔ many_one_equiv p q`, etc. in maximal generality, where `p` and `q` are subsets of different types in different universes.
See previous discussion at [#1203](https://github.com/leanprover-community/mathlib/pull/1203).

### [2021-01-13 16:08:10](https://github.com/leanprover-community/mathlib/commit/d533fbb)
fix(finsupp/pointwise): Relax the ring requirement to semiring ([#5723](https://github.com/leanprover-community/mathlib/pull/5723))

### [2021-01-13 16:08:07](https://github.com/leanprover-community/mathlib/commit/340ddf8)
chore(scripts): don't assume cwd when running lint-style. ([#5721](https://github.com/leanprover-community/mathlib/pull/5721))
Allows running the linter from any ol' directory.

### [2021-01-13 16:08:04](https://github.com/leanprover-community/mathlib/commit/d351cfe)
feat(data/finset): sup_eq_bind ([#5717](https://github.com/leanprover-community/mathlib/pull/5717))
`finset.sup s f` is equal to `finset.bind s f` when `f : α → finset β` is an indexed family of finite sets.  This is a proof of that with a couple supporting lemmas.  (There might be a more direct proof through the definitions of `sup` and `bind`, which are eventually in terms of `multiset.foldr`.)
I also moved `finset.mem_sup` to `multiset.mem_sup` and gave a new `finset.mem_sup` for indexed families of `finset`, where the old one was for indexed families of `multiset`.

### [2021-01-13 16:08:02](https://github.com/leanprover-community/mathlib/commit/3ac4bb2)
feat(combinatorics/simple_graph/basic): add definition of complement of simple graph ([#5697](https://github.com/leanprover-community/mathlib/pull/5697))
Add definition of the complement of a simple graph. Part of branch [strongly_regular_graph](https://github.com/leanprover-community/mathlib/tree/strongly_regular_graph), with the goal of proving facts about strongly regular graphs.

### [2021-01-13 14:54:29](https://github.com/leanprover-community/mathlib/commit/c8574c8)
feat(analysis/special_functions/pow): add various lemmas about ennreal.rpow ([#5701](https://github.com/leanprover-community/mathlib/pull/5701))

### [2021-01-13 10:19:12](https://github.com/leanprover-community/mathlib/commit/b6cca97)
feat(linear_algebra/{exterior,tensor}_algebra): Prove that `ι` is injective ([#5712](https://github.com/leanprover-community/mathlib/pull/5712))
This strategy can't be used on `clifford_algebra`, and the obvious guess of trying to define a `less_triv_sq_quadratic_form_ext` leads to a non-associative multiplication; so for now, we just handle these two cases.

### [2021-01-13 02:51:51](https://github.com/leanprover-community/mathlib/commit/b9b6b16)
chore(scripts): update nolints.txt ([#5720](https://github.com/leanprover-community/mathlib/pull/5720))
I am happy to remove some nolints for you!

### [2021-01-13 02:51:48](https://github.com/leanprover-community/mathlib/commit/5a532ca)
fix(tactic/ring): fix loop in ring ([#5711](https://github.com/leanprover-community/mathlib/pull/5711))
This occurs because when we name the atoms in `A * B = 2`, `A` is the
first and `B` is the second, and once we put it in horner form it ends up
as `B * A = 2`; but then when we go to rewrite it again `B` is named atom
number 1 and `A` is atom number 2, so we write it the other way around
and end up back at `A * B = 2`. The solution implemented here is to
retain the atom map across calls to `ring.eval` while simp is driving
it, so we end up rewriting it to `B * A = 2` in the first place but in the
second pass we still think `B` is the second atom so we stick with the
`B * A` order.
Fixes [#2672](https://github.com/leanprover-community/mathlib/pull/2672)

### [2021-01-12 22:49:15](https://github.com/leanprover-community/mathlib/commit/fe5ec00)
doc(tactic/generalize_proofs): docs and test for generalize_proofs ([#5715](https://github.com/leanprover-community/mathlib/pull/5715))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Extracting.20un-named.20proofs.20from.20the.20goal.20state/near/222472426

### [2021-01-12 22:49:13](https://github.com/leanprover-community/mathlib/commit/a7b800e)
doc(overview): small reorganization of algebra/number theory ([#5707](https://github.com/leanprover-community/mathlib/pull/5707))
- adds Witt vectors
- adds perfection of a ring
- deduplicates Zariski topology
- moves some items to a new subsection "Number theory"

### [2021-01-12 19:31:47](https://github.com/leanprover-community/mathlib/commit/c1894c8)
chore(analysis|measure_theory|topology): give tsum notation precedence 67 ([#5709](https://github.com/leanprover-community/mathlib/pull/5709))
This saves us a lot of `()`
In particular, lean no longer thinks that `∑' i, f i = 37` is a tsum of propositions.

### [2021-01-12 19:31:44](https://github.com/leanprover-community/mathlib/commit/0e7a921)
feat(data/buffer/parser/basic): lemmas describing parsers ([#5460](https://github.com/leanprover-community/mathlib/pull/5460))

### [2021-01-12 16:10:51](https://github.com/leanprover-community/mathlib/commit/1025908)
chore(topology/algebra/infinite_sum): speedup has_sum_sum ([#5710](https://github.com/leanprover-community/mathlib/pull/5710))
this lemma was pretty slow, now it is pretty fast

### [2021-01-12 16:10:48](https://github.com/leanprover-community/mathlib/commit/73ba460)
feat(submonoid/basic): subsingleton and nontrivial instances for {add_,}submonoid ([#5690](https://github.com/leanprover-community/mathlib/pull/5690))

### [2021-01-12 16:10:46](https://github.com/leanprover-community/mathlib/commit/e76fdb9)
docs(undergrad.yaml): analysis updates ([#5675](https://github.com/leanprover-community/mathlib/pull/5675))
Updates to `undergrad.yaml` (including reverting some changes from [#5638](https://github.com/leanprover-community/mathlib/pull/5638), after further discussion), and fix a docstring typo in `measure_theory.interval_integral`.

### [2021-01-12 16:10:44](https://github.com/leanprover-community/mathlib/commit/ce6a7eb)
feat(linear_algebra/multilinear_map): Add `range` and `map` ([#5658](https://github.com/leanprover-community/mathlib/pull/5658))
Note that unlike `linear_map`, `range` cannot return a submodule, only a `sub_mul_action`.
We also can't guarantee closure under `smul` unless the map has at least one argument, as there is nothing requiring the multilinear map of no arguments to be zero.

### [2021-01-12 13:08:45](https://github.com/leanprover-community/mathlib/commit/3a3ec6c)
feat(measure_theory): each set has a measurable superset of the same measure ([#5688](https://github.com/leanprover-community/mathlib/pull/5688))
* generalize `outer_measure.exists_is_measurable_superset_of_trim_eq_zero`
  to `outer_measure.exists_is_measurable_superset_eq_trim`;
* generalize `exists_is_measurable_superset_of_null` to
  `exists_is_measurable_superset`;
* define `to_measurable mu s` to be a measurable superset `t ⊇ s`
	with `μ t = μ s`;
* prove `countable_cover_nhds`: in a `second_countable_topology`, if
  `f` sends each point `x` to a neighborhood of `x`, then some
  countable subfamily of neighborhoods `f x` cover the whole space.
* `sigma_finite_of_countable` no longer assumes that all sets `s ∈ S`
  are measurable.

### [2021-01-12 13:08:41](https://github.com/leanprover-community/mathlib/commit/2671068)
feat(data/set/intervals): add 2 Icc ssubset lemmas ([#5617](https://github.com/leanprover-community/mathlib/pull/5617))
Add two strict subset lemmas for Icc, discussed in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Icc_ssubset_Icc.

### [2021-01-12 08:26:45](https://github.com/leanprover-community/mathlib/commit/cd7a8a1)
chore(category_theory/limits): move constructions folder ([#5681](https://github.com/leanprover-community/mathlib/pull/5681))
As mentioned here: https://github.com/leanprover-community/mathlib/pull/5516#issuecomment-753450199
The linter is giving new errors, so I might as well fix them in this PR.

### [2021-01-12 08:26:43](https://github.com/leanprover-community/mathlib/commit/be75005)
fix(linear_algebra/tensor_product): Remove the priorities from the module structure ([#5667](https://github.com/leanprover-community/mathlib/pull/5667))
These were added originally so that `semimodule'` was lower priority than `semimodule`, as the `semimodule'` instance took too long to resolve.
However, this happens automatically anyway, since the former appears before the latter - the simple existence of the `semimodule` shortcut instances was enough to solve the long typeclass-resolution paths, their priority was a red herring.
The only effect of these attributes was to cause these instances to not take priority over `add_comm_monoid.nat_semimodule`, which was neither intended nor desirable.

### [2021-01-12 07:23:33](https://github.com/leanprover-community/mathlib/commit/cd0d8c0)
chore(category_theory/limits/over): generalise, golf and document over limits ([#5674](https://github.com/leanprover-community/mathlib/pull/5674))
- Show that the forgetful functor `over X => C` creates colimits, generalising what was already there
- Golf the proofs using this new instance
- Add module doc
and duals of the above

### [2021-01-12 02:03:22](https://github.com/leanprover-community/mathlib/commit/9f9f85e)
chore(scripts): update nolints.txt ([#5705](https://github.com/leanprover-community/mathlib/pull/5705))
I am happy to remove some nolints for you!

### [2021-01-11 21:22:16](https://github.com/leanprover-community/mathlib/commit/049f16a)
feat(measure_theory/pi): `ae_eq` lemmas about intervals in `Π i, α i` ([#5633](https://github.com/leanprover-community/mathlib/pull/5633))

### [2021-01-11 10:10:45](https://github.com/leanprover-community/mathlib/commit/b537cc0)
feat(algebra/splitting_field): Restrict to splitting field ([#5562](https://github.com/leanprover-community/mathlib/pull/5562))
Restrict an alg_hom or alg_equiv to an is_splitting_field.

### [2021-01-11 01:59:51](https://github.com/leanprover-community/mathlib/commit/c112ad0)
chore(scripts): update nolints.txt ([#5699](https://github.com/leanprover-community/mathlib/pull/5699))
I am happy to remove some nolints for you!

### [2021-01-10 22:38:07](https://github.com/leanprover-community/mathlib/commit/08800bb)
feat(analysis/special/functions/trigonometric): complex trig and some even/odd lemmas ([#5404](https://github.com/leanprover-community/mathlib/pull/5404))
Complex (and some real) trigonometry lemmas, parity propositions, and some field algebra.

### [2021-01-10 19:12:03](https://github.com/leanprover-community/mathlib/commit/cc6f039)
feat(equiv|set|topology): various additions ([#5656](https://github.com/leanprover-community/mathlib/pull/5656))
define sigma_compact_space
update module doc for topology/subset_properties
define shearing
some lemmas in set.basic, equiv.mul_add and topology.instances.ennreal

### [2021-01-10 19:12:01](https://github.com/leanprover-community/mathlib/commit/62c1912)
chore(measure_theory/set_integral): use weaker assumptions here and there ([#5647](https://github.com/leanprover-community/mathlib/pull/5647))
* use `ae_measurable f (μ.restrict s)` in more lemmas;
* introduce `measurable_at_filter` and use it.

### [2021-01-10 17:59:16](https://github.com/leanprover-community/mathlib/commit/3e7efd4)
feat(field_theory/separable): Remove hypothesis in irreducible.separable ([#5687](https://github.com/leanprover-community/mathlib/pull/5687))
An irreducible polynomial is nonzero, so this hypothesis is unnecessary.

### [2021-01-10 17:59:14](https://github.com/leanprover-community/mathlib/commit/b72811f)
feat(order/complete_well_founded): characterise well-foundedness for complete lattices ([#5575](https://github.com/leanprover-community/mathlib/pull/5575))

### [2021-01-10 14:47:11](https://github.com/leanprover-community/mathlib/commit/0d9cb85)
chore(order/filter): a few more lemmas about `eventually` and set operations ([#5686](https://github.com/leanprover-community/mathlib/pull/5686))

### [2021-01-10 14:47:09](https://github.com/leanprover-community/mathlib/commit/b0c35d1)
chore(order/filter/basic): a few `simp` lemmas ([#5685](https://github.com/leanprover-community/mathlib/pull/5685))
### Changes in `order/filter/basic`
* add `filter.inter_mem_sets_iff`;
* rename `filter.Inter_mem_sets` to `filter.bInter_mem_sets`, make it
  an `iff` `[simp]` lemma;
* add a version `filter.bInter_finset_mem_sets` with a protected alias
  `finset.Inter_mem_sets`;
* rename `filter.sInter_mem_sets_of_finite` to
  `filter.sInter_mem_sets`, make it an `iff` `[simp]` lemma;
* rename `filter.Inter_mem_sets_of_fintype` to
  `filter.Inter_mem_sets`, make it an `iff` `[simp]` lemma
* add `eventually` versions of the `*Inter_mem_sets` lemmas.
### New `@[mono]` attributes
* `set.union_subset_union` and `set.inter_subset_inter` instead of
  `monotone_union` and `monotone_inter`; `mono*` failed to make a
  progress with `s ∩ t ⊆ s' ∩ t'` goal.
* `set.image2_subset`
* `closure_mono`

### [2021-01-10 09:02:16](https://github.com/leanprover-community/mathlib/commit/1c4f2ae)
feat(data/equiv/basic, logic/embedding): swap commutes with injective functions ([#5636](https://github.com/leanprover-community/mathlib/pull/5636))

### [2021-01-10 01:57:53](https://github.com/leanprover-community/mathlib/commit/a28602a)
chore(scripts): update nolints.txt ([#5682](https://github.com/leanprover-community/mathlib/pull/5682))
I am happy to remove some nolints for you!

### [2021-01-09 16:50:50](https://github.com/leanprover-community/mathlib/commit/f60c184)
feat(algebra/lie/basic): Lie ideal operations are linear spans ([#5676](https://github.com/leanprover-community/mathlib/pull/5676))

### [2021-01-09 15:06:06](https://github.com/leanprover-community/mathlib/commit/5faf34c)
feat(measure_theory/lp_space): add more lemmas about snorm ([#5644](https://github.com/leanprover-community/mathlib/pull/5644))

### [2021-01-09 12:23:44](https://github.com/leanprover-community/mathlib/commit/fdec90a)
chore(data/set/lattice): add a few simp lemmas ([#5671](https://github.com/leanprover-community/mathlib/pull/5671))

### [2021-01-09 12:23:42](https://github.com/leanprover-community/mathlib/commit/3166f4e)
feat(topology/separation, topology/metric_space/basic): add lemmas on discrete subsets of a topological space ([#5523](https://github.com/leanprover-community/mathlib/pull/5523))
These lemmas form part of a simplification of the proofs of [#5361](https://github.com/leanprover-community/mathlib/pull/5361).

### [2021-01-09 10:41:15](https://github.com/leanprover-community/mathlib/commit/a161256)
feat(topology/algebra/ordered): prove `tendsto.Icc` for pi-types ([#5639](https://github.com/leanprover-community/mathlib/pull/5639))

### [2021-01-09 03:54:42](https://github.com/leanprover-community/mathlib/commit/faf1a98)
chore(scripts): update nolints.txt ([#5673](https://github.com/leanprover-community/mathlib/pull/5673))
I am happy to remove some nolints for you!

### [2021-01-09 00:41:04](https://github.com/leanprover-community/mathlib/commit/1294500)
feat(category_theory/limits): preserving pullbacks ([#5668](https://github.com/leanprover-community/mathlib/pull/5668))
This touches multiple files but it's essentially the same thing as all my other PRs for preserving limits of special shapes - I can split it up if you'd like but hopefully this is alright?

### [2021-01-09 00:41:01](https://github.com/leanprover-community/mathlib/commit/ce34ae6)
chore(linear_algebra/alternating): golf a proof ([#5666](https://github.com/leanprover-community/mathlib/pull/5666))
`sign_mul` seems to have been marked `simp` recently, making it not necessary to include in `simp` calls.

### [2021-01-09 00:40:59](https://github.com/leanprover-community/mathlib/commit/0cd70d0)
chore(algebra/group/hom): fix additive version of docstring ([#5660](https://github.com/leanprover-community/mathlib/pull/5660))

### [2021-01-08 21:30:46](https://github.com/leanprover-community/mathlib/commit/2b5344f)
chore(analysis/special_functions/trigonometric): adding `@[pp_nodot]` to complex.log ([#5670](https://github.com/leanprover-community/mathlib/pull/5670))
Added `@[pp_nodot]` to complex.log

### [2021-01-08 21:30:44](https://github.com/leanprover-community/mathlib/commit/aab5994)
feat(data/finset/intervals, data/set/intervals/basic): intersection of finset.Ico, union of intervals for sets and finsets ([#5410](https://github.com/leanprover-community/mathlib/pull/5410))

### [2021-01-08 17:23:08](https://github.com/leanprover-community/mathlib/commit/d935760)
feat(algebra/linear_ordered_comm_group_with_zero): Add linear_ordered_comm_monoid_with_zero and an instance for nat ([#5645](https://github.com/leanprover-community/mathlib/pull/5645))
This generalizes a lot of statements about `linear_ordered_comm_group_with_zero` to `linear_ordered_comm_monoid_with_zero`.

### [2021-01-08 17:23:06](https://github.com/leanprover-community/mathlib/commit/2bde21d)
feat(geometry/manifold/times_cont_mdiff): API for checking `times_cont_mdiff` ([#5631](https://github.com/leanprover-community/mathlib/pull/5631))
Two families of lemmas:
- to be `times_cont_mdiff`, it suffices to be `times_cont_mdiff` after postcomposition with any chart of the target
- projection notation to go from `times_cont_diff` (in a vector space) to `times_cont_mdiff`

### [2021-01-08 17:23:03](https://github.com/leanprover-community/mathlib/commit/bd9b03f)
feat(category_theory/closed): Frobenius reciprocity of cartesian closed categories ([#5624](https://github.com/leanprover-community/mathlib/pull/5624))
A re-do of [#4929](https://github.com/leanprover-community/mathlib/pull/4929). 
Re-defines the exponential comparison morphism (now as a natural transformation rather than a morphism with a naturality prop), and defines the Frobenius reciprocity morphism for an adjoint. In the case where the functor has a left adjoint, gives a sufficient condition for it to be cartesian closed, and a sufficient condition for a functor whose left adjoint preserves binary products to be cartesian closed (but doesn't show the necessity of this).
- [x] depends on: [#5623](https://github.com/leanprover-community/mathlib/pull/5623)

### [2021-01-08 16:06:43](https://github.com/leanprover-community/mathlib/commit/0d7ca98)
feat(measure_theory/measure_space): ae_measurable and measurable are equivalent for complete measures ([#5643](https://github.com/leanprover-community/mathlib/pull/5643))

### [2021-01-08 14:20:37](https://github.com/leanprover-community/mathlib/commit/9f066f1)
refactor(linear_algebra/alternating): Use unapplied maps when possible ([#5648](https://github.com/leanprover-community/mathlib/pull/5648))
Notably, this removes the need for a proof of `map_add` and `map_smul` in `def alternatization`, as the result is now already bundled with these proofs.
This also:
* Replaces `equiv.perm.sign p` with `p.sign` for brevity
* Makes `linear_map.comp_alternating_map` an `add_monoid_hom`

### [2021-01-08 09:47:21](https://github.com/leanprover-community/mathlib/commit/795d5ab)
chore(algebra/ordered_monoid): rename lemmas ([#5657](https://github.com/leanprover-community/mathlib/pull/5657))
I wanted to add the alias `pos_iff_ne_zero` for `zero_lt_iff_ne_zero`, but then I saw a note already in the library to do this renaming. So I went ahead.
`le_zero_iff_eq` -> `nonpos_iff_eq_zero`
`zero_lt_iff_ne_zero` -> `pos_iff_ne_zero`
`le_one_iff_eq` -> `le_one_iff_eq_one`
`measure.le_zero_iff_eq_zero'` -> `measure.nonpos_iff_eq_zero'`
There were various specific types that had their own custom `pos_iff_ne_zero`-lemma, which caused nameclashes. Therefore:
* remove `nat.pos_iff_ne_zero`
* Prove that `cardinal` forms a `canonically_ordered_semiring`, remove various special case lemmas
* There were lemmas `cardinal.le_add_[left|right]`. Generalized them to arbitrary canonically_ordered_monoids and renamed them to `self_le_add_[left|right]` (to avoid name clashes)
* I did not provide a canonically_ordered_monoid class for ordinal, since that requires quite some work (it's true, right?)
* `protect` various lemmas in `cardinal` and `ordinal` to avoid name clashes.

### [2021-01-08 07:46:54](https://github.com/leanprover-community/mathlib/commit/611bc86)
feat(measure_theory/borel_space): locally finite measure is sigma finite ([#5634](https://github.com/leanprover-community/mathlib/pull/5634))
I forgot to add this to [#5604](https://github.com/leanprover-community/mathlib/pull/5604)

### [2021-01-08 05:13:37](https://github.com/leanprover-community/mathlib/commit/efdcab1)
refactor(algebra/module/basic): Clean up all the nat/int semimodule definitions ([#5654](https://github.com/leanprover-community/mathlib/pull/5654))
These were named inconsistently, and lots of proof was duplicated.
The name changes are largely making the API for `nsmul` consistent with the one for `gsmul`:
* For `ℕ`:
  * Replaces `nat.smul_def : n • x = n •ℕ x` with `nsmul_def : n •ℕ x = n • x`
  * Renames `semimodule.nsmul_eq_smul : n •ℕ b = (n : R) • b` to `nsmul_eq_smul_cast`
  * Removes `semimodule.smul_eq_smul : n • b = (n : R) • b`
  * Adds `nsmul_eq_smul : n •ℕ b = n • b` (this is different from `nsmul_def` as described in the docstring)
  * Renames the instances to be named more consistently and all live under `add_comm_monoid.nat_*`
* For `ℤ`:
  * Renames `gsmul_eq_smul : n •ℤ x = n • x` to `gsmul_def`
  * Renames `module.gsmul_eq_smul : n •ℤ x = n • x` to `gsmul_eq_smul`
  * Renames `module.gsmul_eq_smul_cast` to `gsmul_eq_smul_cast`
  * Renames the instances to be named more consistently and all live under `add_comm_group.int_*`

### [2021-01-08 03:36:08](https://github.com/leanprover-community/mathlib/commit/d89464d)
feat(topology/algebra): add additive/multiplicative instances ([#5662](https://github.com/leanprover-community/mathlib/pull/5662))

### [2021-01-08 02:05:16](https://github.com/leanprover-community/mathlib/commit/7500b24)
chore(scripts): update nolints.txt ([#5661](https://github.com/leanprover-community/mathlib/pull/5661))
I am happy to remove some nolints for you!

### [2021-01-08 02:05:14](https://github.com/leanprover-community/mathlib/commit/4c3c8d7)
feat(measure_theory): some additions ([#5653](https://github.com/leanprover-community/mathlib/pull/5653))
rename `exists_is_measurable_superset_of_measure_eq_zero` -> `exists_is_measurable_superset_of_null`
make `measure.prod` and `measure.pi` irreducible

### [2021-01-07 23:12:07](https://github.com/leanprover-community/mathlib/commit/33a86cf)
chore(data/list/basic): tag mmap(') with simp ([#5443](https://github.com/leanprover-community/mathlib/pull/5443))

### [2021-01-07 21:43:48](https://github.com/leanprover-community/mathlib/commit/18ba69b)
feat(category_theory/sites): category of sheaves on the trivial topology  ([#5651](https://github.com/leanprover-community/mathlib/pull/5651))
Shows that the category of sheaves on the trivial topology is just the category of presheaves.

### [2021-01-07 21:43:46](https://github.com/leanprover-community/mathlib/commit/3c5d5c5)
feat(category_theory/monad): reflector preserves terminal object ([#5649](https://github.com/leanprover-community/mathlib/pull/5649))

### [2021-01-07 21:43:44](https://github.com/leanprover-community/mathlib/commit/a30c39e)
feat(measure_theory/borel_space): a compact set has finite measure ([#5628](https://github.com/leanprover-community/mathlib/pull/5628))

### [2021-01-07 21:43:41](https://github.com/leanprover-community/mathlib/commit/4da8313)
feat(category_theory/closed): golf definition and proofs ([#5623](https://github.com/leanprover-community/mathlib/pull/5623))
Using the new mates framework, simplify the definition of `pre` and shorten proofs about it. 
To be more specific,
- `pre` is now explicitly a natural transformation, rather than indexed morphisms with a naturality property
- The new definition of `pre` means things like `pre_map` which I complained about before are easier to prove, and `pre_post_comm` is automatic
- There are now more lemmas relating `pre` to `coev`, `ev` and `uncurry`: `uncurry_pre` in particular was a hole in the API.
- `internal_hom` has a shorter construction. In particular I changed the type to `Cᵒᵖ ⥤ C ⥤ C`, which I think is better since the usual external hom functor is given as `Cᵒᵖ ⥤ C ⥤ Type*`, so this is consistent with that. 
In a subsequent PR I'll do the same for `exp_comparison`, but that's a bigger change with improved API so they're separate for now.

### [2021-01-07 21:43:39](https://github.com/leanprover-community/mathlib/commit/fdbcab6)
feat(category_theory/limits): the product comparison natural transformation ([#5621](https://github.com/leanprover-community/mathlib/pull/5621))

### [2021-01-07 19:12:12](https://github.com/leanprover-community/mathlib/commit/2894260)
feat(group_theory): add lemmas on solvability ([#5646](https://github.com/leanprover-community/mathlib/pull/5646))
Proves some basic lemmas about solvable groups: the subgroup of a solvable group is solvable, a quotient of a solvable group is solvable.

### [2021-01-07 13:09:27](https://github.com/leanprover-community/mathlib/commit/66e02b3)
feat(docs/100): Add Masdeu's formalisation of Euler's Summation to 100.yaml ([#5655](https://github.com/leanprover-community/mathlib/pull/5655))

### [2021-01-07 13:09:25](https://github.com/leanprover-community/mathlib/commit/7bc2e9e)
feat(ring_theory/polynomial/cyclotomic): add cyclotomic.irreducible ([#5642](https://github.com/leanprover-community/mathlib/pull/5642))
I proved irreducibility of cyclotomic polynomials, showing that `cyclotomic n Z` is the minimal polynomial of any primitive root of unity.

### [2021-01-07 13:09:23](https://github.com/leanprover-community/mathlib/commit/b9da50a)
feat(ring_theory/*): Various lemmas used to prove classical nullstellensatz ([#5632](https://github.com/leanprover-community/mathlib/pull/5632))

### [2021-01-07 13:09:21](https://github.com/leanprover-community/mathlib/commit/3aea284)
feat(analysis/normed_space): affine map with findim domain is continuous ([#5627](https://github.com/leanprover-community/mathlib/pull/5627))

### [2021-01-07 13:09:18](https://github.com/leanprover-community/mathlib/commit/833e9a0)
chore(analysis/calculus): add `of_mem_nhds` versions of 2 lemmas ([#5626](https://github.com/leanprover-community/mathlib/pull/5626))

### [2021-01-07 13:09:16](https://github.com/leanprover-community/mathlib/commit/e14d5eb)
feat(category_theory/limits): prod map is iso if components are ([#5620](https://github.com/leanprover-community/mathlib/pull/5620))
Show that if `f` and `g` are iso, then `prod.map f g` is an iso, and the dual.

### [2021-01-07 13:09:14](https://github.com/leanprover-community/mathlib/commit/87ef7af)
feat(linear_algebra/pi_tensor_product): define the tensor product of an indexed family of semimodules ([#5311](https://github.com/leanprover-community/mathlib/pull/5311))
This PR defines the tensor product of an indexed family `s : ι → Type*` of semimodules over commutative semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (R × Π i, s i)` quotiented by the appropriate equivalence relation. The treatment follows very closely that of the binary tensor product in `linear_algebra/tensor_product.lean`.

### [2021-01-07 10:05:38](https://github.com/leanprover-community/mathlib/commit/47c6081)
chore(group_theory/perm/sign): remove classical for sign congr simp lemmas ([#5622](https://github.com/leanprover-community/mathlib/pull/5622))
Previously, some lemmas about how `perm.sign` simplifies across various congrs of permutations assumed `classical`, which prevented them from being applied by the simplifier. This makes the `decidable_eq` assumptions explicit.

### [2021-01-07 10:05:35](https://github.com/leanprover-community/mathlib/commit/9dd1496)
chore(group_theory/perm/basic): Add some missing simp lemmas ([#5614](https://github.com/leanprover-community/mathlib/pull/5614))
`simp` can't find the appropriate `equiv` lemmas as they are about `refl` not `1`, even though those are defeq.

### [2021-01-07 10:05:33](https://github.com/leanprover-community/mathlib/commit/2457287)
feat(algebra/subalgebra): Restrict injective algebra homomorphism to algebra isomorphism ([#5560](https://github.com/leanprover-community/mathlib/pull/5560))
The domain of an injective algebra homomorphism is isomorphic to its range.

### [2021-01-07 10:05:31](https://github.com/leanprover-community/mathlib/commit/2c8175f)
feat(algebra/algebra/ordered): ordered algebras ([#4683](https://github.com/leanprover-community/mathlib/pull/4683))
An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

### [2021-01-07 08:51:54](https://github.com/leanprover-community/mathlib/commit/95c7087)
chore(docs/100.yaml): Freek No. 15 ([#5638](https://github.com/leanprover-community/mathlib/pull/5638))
I've updated docs/100.yaml to reflect the fact that both FTC-1 and FTC-2 have been added to mathlib.

### [2021-01-07 05:47:19](https://github.com/leanprover-community/mathlib/commit/a32e223)
refactor(analysis/special_functions/trigonometric): redefine arcsin and arctan ([#5300](https://github.com/leanprover-community/mathlib/pull/5300))
Redefine `arcsin` and `arctan` using `order_iso`, and prove that both of them are infinitely smooth.

### [2021-01-07 02:28:43](https://github.com/leanprover-community/mathlib/commit/3f35961)
chore(scripts): update nolints.txt ([#5652](https://github.com/leanprover-community/mathlib/pull/5652))
I am happy to remove some nolints for you!

### [2021-01-06 23:23:44](https://github.com/leanprover-community/mathlib/commit/f668be0)
feat(data/list/zip): parameterize zip_append more generally ([#5650](https://github.com/leanprover-community/mathlib/pull/5650))
zip_append should only require that each pair of lists is of the same type

### [2021-01-06 16:21:02](https://github.com/leanprover-community/mathlib/commit/f4128dc)
chore(ring_theory/ideal/basic): Make an argument to mul_mem_{left,right} explicit ([#5611](https://github.com/leanprover-community/mathlib/pull/5611))
Before this change, the lemmas with result `a * b ∈ I` did not have enough explicit arguments to determine both `a` and `b`, such as `I.mul_mem_left hb`.
This resulted in callers using `show`, `@`, or sometimes ignoring the API and using `smul_mem` which does have appropriate argument explicitness. These callers have been cleaned up accordingly.

### [2021-01-06 16:21:00](https://github.com/leanprover-community/mathlib/commit/91fcb48)
feat(linear_algebra/tensor_product,algebra/module/linear_map): Made tmul_smul and map_smul_of_tower work for int over semirings ([#5430](https://github.com/leanprover-community/mathlib/pull/5430))
With this change, ` ∀ (f : M →ₗ[S] M₂) (z : int) (x : M), f (z • x) = z • f x` can be proved with `linear_map.map_smul_of_tower` even when `S` is a semiring, and `z • (m ⊗ₜ n : M ⊗[S] N) = (r • m) ⊗ₜ n` can be proved with `tmul_smul`.

### [2021-01-06 13:54:26](https://github.com/leanprover-community/mathlib/commit/eeb194d)
feat(analysis/normed_space/inner_product): facts about the span of a single vector, mostly in inner product spaces ([#5589](https://github.com/leanprover-community/mathlib/pull/5589))

### [2021-01-06 11:04:14](https://github.com/leanprover-community/mathlib/commit/186ad76)
feat(ring_theory/finiteness): add finitely presented algebra ([#5407](https://github.com/leanprover-community/mathlib/pull/5407))
This PR contains the definition of a finitely presented algebra and some very basic results. A lot of other fundamental results are missing (stability under composition, equivalence with finite type for noetherian rings ecc): I am ready to work on them, but I wanted some feedback. Feel free to convert to WIP if you think it's better to wait.

### [2021-01-06 11:04:12](https://github.com/leanprover-community/mathlib/commit/35ff043)
feat(ring_theory/fractional_ideal): move inv to dedekind_domain ([#5053](https://github.com/leanprover-community/mathlib/pull/5053))
Remove all instances of `inv` and I^{-1}. The notation (1 / I) is the one used for the old I^{-1}.

### [2021-01-06 11:04:08](https://github.com/leanprover-community/mathlib/commit/1db70a8)
feat(computability/regular_expressions): define regular expressions ([#5036](https://github.com/leanprover-community/mathlib/pull/5036))
Very basic definitions for regular expressions

### [2021-01-06 11:04:04](https://github.com/leanprover-community/mathlib/commit/137a6e0)
feat(tactic/rewrite_search): Automatically searching for chains of rewrites ([#4841](https://github.com/leanprover-community/mathlib/pull/4841))
This pull request is based on a branch originally developed by @semorrison , @khoek , and @jcommelin . The idea of rewrite_search is a tactic that will search through chains of potential rewrites to prove the goal, when the goal is an equality or iff statement. There are three key components: `discovery.lean` finds a bunch of rules that can be used to generate rewrites, `search.lean` runs a breadth-first-search algorithm on the two sides of the quality to find a path that connects them, and `explain.lean` generates Lean code from the resulting proof, so that you can replace the call to `rewrite_search` with the explicit steps for it.
I removed some functionality from the rewrite_search branch and simplified the data structures somewhat in order to get this pull request small enough to be reviewed. If there is functionality from that branch that people particularly wanted, let me know and I can either include it in this PR or in a subsequent one. In particular, most of the configuration options are omitted.
For data structures, the whole `table` data structure is gone, replaced by a `buffer` and `rb_map` for efficient lookup. Write access to the buffer is also append-only for efficiency. This seems to be a lot faster, although I haven't created specific performance benchmarks.

### [2021-01-06 08:30:32](https://github.com/leanprover-community/mathlib/commit/062f244)
feat(category_theory/monad): generalise limits lemma ([#5630](https://github.com/leanprover-community/mathlib/pull/5630))
A slight generalisation of a lemma already there.

### [2021-01-06 08:30:30](https://github.com/leanprover-community/mathlib/commit/56ed5d7)
feat(category_theory/adjunction): mates ([#5599](https://github.com/leanprover-community/mathlib/pull/5599))
Adds some results on the calculus of mates.

### [2021-01-06 08:30:28](https://github.com/leanprover-community/mathlib/commit/5f98a96)
feat(group_theory): add definition of solvable group ([#5565](https://github.com/leanprover-community/mathlib/pull/5565))
Defines solvable groups using the definition that a group is solvable if its nth commutator is eventually trivial. Defines the nth commutator of a group and provides some lemmas for working with it. More facts about solvable groups will come in future PRs.

### [2021-01-06 08:30:25](https://github.com/leanprover-community/mathlib/commit/648ff21)
feat(algebra/lie/basic): the lattice of Lie submodules of a Noetherian Lie module is well-founded ([#5557](https://github.com/leanprover-community/mathlib/pull/5557))
The key result is: `well_founded_of_noetherian`

### [2021-01-06 05:36:16](https://github.com/leanprover-community/mathlib/commit/3892155)
fix(algebra/group/pi): use correct `div`/`sub` ([#5625](https://github.com/leanprover-community/mathlib/pull/5625))
Without an explicit `div := has_div.div`, `rw [pi.sub_apply]` fails sometimes.

### [2021-01-06 05:36:13](https://github.com/leanprover-community/mathlib/commit/3d6ba9a)
feat(data/list/chain): chain pmap ([#5438](https://github.com/leanprover-community/mathlib/pull/5438))
Two chain pmap lemmas

### [2021-01-06 02:30:13](https://github.com/leanprover-community/mathlib/commit/de73912)
chore(scripts): update nolints.txt ([#5629](https://github.com/leanprover-community/mathlib/pull/5629))
I am happy to remove some nolints for you!

### [2021-01-06 02:30:10](https://github.com/leanprover-community/mathlib/commit/19d2ea7)
feat(order/atoms): Pairwise coprime ([#5596](https://github.com/leanprover-community/mathlib/pull/5596))
Don't really know what to call it, but it's the atom-level version of the statement that maximal ideals are pairwise coprime.

### [2021-01-06 02:30:08](https://github.com/leanprover-community/mathlib/commit/9fdd703)
feat(linear_algebra/affine_space/midpoint): a few more lemmas ([#5571](https://github.com/leanprover-community/mathlib/pull/5571))
* simplify expressions like `midpoint R p₁ p₂ -ᵥ p₁` and
  `p₂ - midpoint R p₁ p₂`;
* fix a typo in `data/set/intervals/surj_on`.

### [2021-01-06 02:30:06](https://github.com/leanprover-community/mathlib/commit/731c26f)
refactor(*): swap sides of `iff` in `{rel_embedding,order_embedding}.map_rel_iff` ([#5556](https://github.com/leanprover-community/mathlib/pull/5556))
This way RHS is "simpler" than LHS.
Other API changes (in `rel_embedding` and/or `ord_embedding` and/or `rel_iso` and/or `ord_iso` namespaces):
* drop `map_le_iff`, rename `apply_le_apply` to `le_iff_le`;
* drop `map_lt_iff`, rename `apply_lt_apply` to `lt_iff_lt`;
* rename `apply_eq_apply` to `eq_iff_eq`.

### [2021-01-06 00:02:09](https://github.com/leanprover-community/mathlib/commit/8f424fc)
chore(measure_theory/pi): a few more lemmas ([#5604](https://github.com/leanprover-community/mathlib/pull/5604))
Also prove that a locally finite measure in a `second_countable_topology` is `sigma_finite`.

### [2021-01-05 20:33:53](https://github.com/leanprover-community/mathlib/commit/00d8617)
feat(analysis/normed_space/inner_product): inner product is continuous, norm squared is smooth ([#5600](https://github.com/leanprover-community/mathlib/pull/5600))

### [2021-01-05 20:33:51](https://github.com/leanprover-community/mathlib/commit/0c8fffe)
fix(algebra/group/prod): fixes for [#5563](https://github.com/leanprover-community/mathlib/pull/5563) ([#5577](https://github.com/leanprover-community/mathlib/pull/5577))
* rename `prod.units` to `mul_equiv.prod_units`;
* rewrite it with better definitional equalities;
* now `@[to_additive]` works: fixes [#5566](https://github.com/leanprover-community/mathlib/pull/5566);
* make `M` and `N` implicit in `mul_equiv.prod_comm`

### [2021-01-05 20:33:49](https://github.com/leanprover-community/mathlib/commit/7cf0a29)
feat(analysis/normed_space/inner_product): consequences of characterization of orthogonal projection ([#5558](https://github.com/leanprover-community/mathlib/pull/5558))
Reverse order of equality in the lemma `eq_orthogonal_projection_of_mem_of_inner_eq_zero`.  Add some variants.  Also add three consequences:
- the orthogonal projection onto `K` of an element of `K` is itself
- the orthogonal projection onto `K` of an element of `Kᗮ` is zero
- for a submodule `K` of an inner product space, the sum of the orthogonal projections onto `K` and `Kᗮ` is the identity.
Reverse order of `iff` in the lemma `submodule.eq_top_iff_orthogonal_eq_bot`, and rename to `submodule.orthogonal_eq_bot_iff`.

### [2021-01-05 20:33:46](https://github.com/leanprover-community/mathlib/commit/82ec0cc)
feat(ring_theory/roots_of_unity): degree of minimal polynomial ([#5475](https://github.com/leanprover-community/mathlib/pull/5475))
This is the penultimate PR about roots of unity and cyclotomic polynomials: I prove that the degree of the minimal polynomial of a primitive `n`th root of unity is at least `nat.totient n`.
It's easy to prove now that it is actually `nat.totient n`, and indeed that the minimal polynomial is the cyclotomic polynomial (that it is hence irreducible). I decided to split the PR like this because I feel that it's better to put the remaining results in `ring_theory/polynomials/cyclotomic`.

### [2021-01-05 18:04:53](https://github.com/leanprover-community/mathlib/commit/d1b2d6e)
fix(linear_algebra/tensor_algebra): Correct the precedence of `⊗ₜ[R]` ([#5619](https://github.com/leanprover-community/mathlib/pull/5619))
Previously, `a ⊗ₜ[R] b = c` was interpreted as `a ⊗ₜ[R] (b = c)` which was nonsense because `eq` is not in `Type`.
I'm not sure whether `:0` is necessary, but it seems harmless.
The `:100` is the crucial bugfix here.

### [2021-01-05 18:04:51](https://github.com/leanprover-community/mathlib/commit/01e17a9)
feat(scripts/lint-style.sh): check that Lean files don't have executable bit ([#5606](https://github.com/leanprover-community/mathlib/pull/5606))

### [2021-01-05 16:18:37](https://github.com/leanprover-community/mathlib/commit/a6633e5)
feat(analysis/normed_space/inner_product): new versions of Cauchy-Schwarz equality case ([#5586](https://github.com/leanprover-community/mathlib/pull/5586))
The existing version of the Cauchy-Schwarz equality case characterizes the pairs `x`, `y` with `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`.  This PR provides a characterization, with converse, of pairs satisfying `⟪x, y⟫ = ∥x∥ * ∥y∥`, and some consequences.

### [2021-01-05 14:50:35](https://github.com/leanprover-community/mathlib/commit/1de608d)
refactor(measure_theory): integrate almost everywhere measurable functions ([#5510](https://github.com/leanprover-community/mathlib/pull/5510))
Currently, the Bochner integral is only defined for measurable functions. This means that, if `f` is continuous on an interval `[a, b]`, to be able to make sense of `∫ x in a..b, f`, one has to add a global measurability assumption, which is very much unnatural.
This PR redefines the Bochner integral so that it makes sense for functions that are almost everywhere measurable, i.e., they coincide almost everywhere with a measurable function (This is equivalent to measurability for the completed measure, but we don't state or prove this as it is not needed to develop the theory).

### [2021-01-05 10:34:59](https://github.com/leanprover-community/mathlib/commit/8f9f5ca)
chore(linear_algebra/alternating): Use `have` instead of `simp only` ([#5618](https://github.com/leanprover-community/mathlib/pull/5618))
This makes the proof easier to read and less fragile to lemma changes.

### [2021-01-05 06:08:53](https://github.com/leanprover-community/mathlib/commit/78dc23f)
chore(scripts/*): rename files of the style linter ([#5605](https://github.com/leanprover-community/mathlib/pull/5605))
The style linter has been doing a bit more than just checking for
copyright headers, module docstrings, or line lengths.
So I thought it made sense to reflect that in the filenames.

### [2021-01-05 03:19:32](https://github.com/leanprover-community/mathlib/commit/6dcfa5c)
chore(scripts): update nolints.txt ([#5615](https://github.com/leanprover-community/mathlib/pull/5615))
I am happy to remove some nolints for you!

### [2021-01-04 23:56:31](https://github.com/leanprover-community/mathlib/commit/12921e9)
feat(tactic/simps): some improvements ([#5541](https://github.com/leanprover-community/mathlib/pull/5541))
* `@[simps]` would previously fail if the definition is not a constructor application (with the suggestion to add option `{rhs_md := semireducible}` and maybe `simp_rhs := tt`). Now it automatically adds `{rhs_md := semireducible, simp_rhs := tt}` whenever it reaches this situation. 
* Remove all (now) unnecessary occurrences of `{rhs_md := semireducible}` from the library. There are still a couple left where the `simp_rhs := tt` is undesirable.
* `@[simps {simp_rhs := tt}]` now also applies `dsimp, simp` to the right-hand side of the lemmas it generates.
* Add some `@[simps]` in `category_theory/limits/cones.lean`
* `@[simps]` would not recursively apply projections of `prod` or `pprod`. This is now customizable with the `not_recursive` option.
* Add an option `trace.simps.debug` with some debugging information.

### [2021-01-04 22:10:37](https://github.com/leanprover-community/mathlib/commit/78d5bd3)
feat(analysis/normed_space/{finite_dimension, inner_product}): assorted finite-dimensionality lemmas ([#5580](https://github.com/leanprover-community/mathlib/pull/5580))
Two groups of lemmas about finite-dimensional normed spaces:
- normed spaces of the same finite dimension are continuously linearly equivalent (this is a continuation of [#5559](https://github.com/leanprover-community/mathlib/pull/5559))
- variations on the existing lemma `submodule.findim_add_inf_findim_orthogonal`, that the dimensions of a subspace and its orthogonal complement sum to the dimension of the full space.

### [2021-01-04 20:20:02](https://github.com/leanprover-community/mathlib/commit/7b825f2)
feat(linear_algebra/alternating): Add comp_alternating_map and lemmas ([#5476](https://github.com/leanprover-community/mathlib/pull/5476))
This is just `comp_multilinear_map` with the extra bundled proof

### [2021-01-04 16:47:45](https://github.com/leanprover-community/mathlib/commit/2300b47)
chore(computability/*FA): remove unnecessary type variables ([#5613](https://github.com/leanprover-community/mathlib/pull/5613))

### [2021-01-04 16:47:44](https://github.com/leanprover-community/mathlib/commit/9535f91)
feat(*): switch to lean 3.24 ([#5612](https://github.com/leanprover-community/mathlib/pull/5612))

### [2021-01-04 16:47:42](https://github.com/leanprover-community/mathlib/commit/7d0b988)
chore(data/equiv/basic): Add refl / symm / trans lemmas for equiv_congr ([#5609](https://github.com/leanprover-community/mathlib/pull/5609))
We already have this triplet of lemmas for `sum_congr` and `sigma_congr`.

### [2021-01-04 16:47:40](https://github.com/leanprover-community/mathlib/commit/50beef2)
feat(data/set/basic): more lemmas about `set.pi` ([#5603](https://github.com/leanprover-community/mathlib/pull/5603))

### [2021-01-04 12:04:36](https://github.com/leanprover-community/mathlib/commit/3669cb3)
feat(data/real/ennreal): add `ennreal.prod_lt_top` ([#5602](https://github.com/leanprover-community/mathlib/pull/5602))
Also add `with_top.can_lift`, `with_top.mul_lt_top`, and `with_top.prod_lt_top`.

### [2021-01-04 08:50:41](https://github.com/leanprover-community/mathlib/commit/4150136)
chore(logic/function): generalize `rel_update_iff` to `forall_update_iff` ([#5601](https://github.com/leanprover-community/mathlib/pull/5601))

### [2021-01-04 08:50:39](https://github.com/leanprover-community/mathlib/commit/6acf99e)
fix(data/nat/basic): fix typos in docstrings ([#5592](https://github.com/leanprover-community/mathlib/pull/5592))

### [2021-01-04 05:36:22](https://github.com/leanprover-community/mathlib/commit/afbf47d)
feat(data/*, order/*) supporting lemmas for characterising well-founded complete lattices ([#5446](https://github.com/leanprover-community/mathlib/pull/5446))

### [2021-01-04 02:31:40](https://github.com/leanprover-community/mathlib/commit/2434023)
chore(scripts): update nolints.txt ([#5598](https://github.com/leanprover-community/mathlib/pull/5598))
I am happy to remove some nolints for you!

### [2021-01-03 23:19:01](https://github.com/leanprover-community/mathlib/commit/1503cf8)
doc(overview): add dynamics and `measure.pi` ([#5597](https://github.com/leanprover-community/mathlib/pull/5597))

### [2021-01-03 23:18:59](https://github.com/leanprover-community/mathlib/commit/4fcf65c)
fix(tactic/rcases): fix rcases? goal alignment ([#5576](https://github.com/leanprover-community/mathlib/pull/5576))
This fixes a bug in which `rcases?` will not align the goals correctly
in the same manner as `rcases`, leading to a situation where the hint
produced by `rcases?` does not work in `rcases`.
Also fixes a bug where missing names will be printed as `[anonymous]`
instead of `_`.
Fixes [#2794](https://github.com/leanprover-community/mathlib/pull/2794)

### [2021-01-03 23:18:57](https://github.com/leanprover-community/mathlib/commit/96948e4)
feat(measure_theory): almost everywhere measurable functions ([#5568](https://github.com/leanprover-community/mathlib/pull/5568))
This PR introduces a notion of almost everywhere measurable function, i.e., a function which coincides almost everywhere with a measurable function, and builds a basic API around the notion. It will then be used in [#5510](https://github.com/leanprover-community/mathlib/pull/5510) to extend the Bochner integral. The main new definition in the PR is `h : ae_measurable f μ`. It comes with `h.mk f` building a measurable function that coincides almost everywhere with `f` (these assertions are respectively `h.measurable_mk` and `h.ae_eq_mk`).

### [2021-01-03 23:18:53](https://github.com/leanprover-community/mathlib/commit/2967793)
feat(data/option/basic): join and associated lemmas ([#5426](https://github.com/leanprover-community/mathlib/pull/5426))

### [2021-01-03 23:18:51](https://github.com/leanprover-community/mathlib/commit/d04e034)
feat(measure_theory/interval_integral): FTC-2 ([#4945](https://github.com/leanprover-community/mathlib/pull/4945))
The second fundamental theorem of calculus and supporting lemmas

### [2021-01-03 20:40:21](https://github.com/leanprover-community/mathlib/commit/46c35cc)
fix(algebra/module/basic): Do not attach the ℕ and ℤ `is_scalar_tower` and `smul_comm_class` instances to a specific definition of smul ([#5509](https://github.com/leanprover-community/mathlib/pull/5509))
These instances are in `Prop`, so the more the merrier.
Without this change, these instances are not available for alternative ℤ-module definitions.
An example of one of these alternate definitions is `linear_map.semimodule`, which provide a second non-defeq ℤ-module structure alongside `add_comm_group.int_module`.
With this PR, both semimodule structures are shown to satisfy `smul_comm_class` and `is_scalar_tower`; while before it, only `add_comm_group.int_module` was shown to satisfy these.
This PR makes the following work:
```lean
example {R : Type*} {M₁ M₂ M₃ : Type*}
  [comm_semiring R]
  [add_comm_monoid M₁] [semimodule R M₁]
  [add_comm_monoid M₂] [semimodule R M₂]
  [add_comm_monoid M₃] [semimodule R M₃]
(f : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (x : M₁) (n : ℕ) : f (n • x) = n • f x :=
by simp
```

### [2021-01-03 18:36:11](https://github.com/leanprover-community/mathlib/commit/e1138b0)
feat(measure_theory/lp_space): snorm is zero iff the function is zero ae ([#5595](https://github.com/leanprover-community/mathlib/pull/5595))
Adds three lemmas, one for both directions of the iff, `snorm_zero_ae` and `snorm_eq_zero`, and the iff lemma `snorm_eq_zero_iff`.

### [2021-01-03 16:58:07](https://github.com/leanprover-community/mathlib/commit/ae2c857)
feat(measure_theory/lp_space): add triangle inequality for the Lp seminorm ([#5594](https://github.com/leanprover-community/mathlib/pull/5594))

### [2021-01-03 16:58:05](https://github.com/leanprover-community/mathlib/commit/384ba88)
feat(computability/*FA): Deterministic and Nondeterministic Finite Automata ([#5038](https://github.com/leanprover-community/mathlib/pull/5038))
Definition and equivalence of NFA's and DFA's

### [2021-01-03 14:06:47](https://github.com/leanprover-community/mathlib/commit/eb6d5f1)
feat(analysis/normed_space/basic): basic facts about the sphere ([#5590](https://github.com/leanprover-community/mathlib/pull/5590))
Basic lemmas about the sphere in a normed group or normed space.

### [2021-01-03 11:59:40](https://github.com/leanprover-community/mathlib/commit/0837fc3)
feat(measure_theory/pi): finite products of measures ([#5414](https://github.com/leanprover-community/mathlib/pull/5414))
See module doc of `measure_theory/pi.lean`

### [2021-01-03 08:56:55](https://github.com/leanprover-community/mathlib/commit/e350114)
feat(data/equiv/basic): rfl lemma for equiv_congr ([#5585](https://github.com/leanprover-community/mathlib/pull/5585))

### [2021-01-03 05:59:33](https://github.com/leanprover-community/mathlib/commit/57c6d19)
feat(combinatorics/simple_graph): finitely many simple graphs on a finite type ([#5584](https://github.com/leanprover-community/mathlib/pull/5584))
Adds an `ext` lemma for simple graphs and an instance that there are finitely many if the vertex set is finite.

### [2021-01-03 05:59:31](https://github.com/leanprover-community/mathlib/commit/9fc7aa5)
feat(data/finset/basic): add `finset.piecewise_le_piecewise` ([#5572](https://github.com/leanprover-community/mathlib/pull/5572))
* add `finset.piecewise_le_piecewise` and `finset.piecewise_le_piecewise'`;
* add `finset.piecewise_compl`.

### [2021-01-03 02:24:46](https://github.com/leanprover-community/mathlib/commit/0a4fbd8)
chore(data/prod): add `prod.forall'` and `prod.exists'` ([#5570](https://github.com/leanprover-community/mathlib/pull/5570))
They work a bit better with curried functions.

### [2021-01-03 02:24:43](https://github.com/leanprover-community/mathlib/commit/0dc7a27)
feat(data/nat/fib): fib n is a strong divisibility sequence ([#5555](https://github.com/leanprover-community/mathlib/pull/5555))

### [2021-01-03 02:24:41](https://github.com/leanprover-community/mathlib/commit/9f25244)
chore(data/finset/sort): upgrade `finset.mono_of_fin` to an `order_iso` ([#5495](https://github.com/leanprover-community/mathlib/pull/5495))
* Upgrade `finset.mono_of_fin` to an `order_embedding`.
* Drop some lemmas that now immediately follow from `order_embedding.*`.
* Upgrade `finset.mono_equiv_of_fin` to `order_iso`.
* Define `list.nodup.nth_le_equiv` and `list.sorted.nth_le_iso`.
* Upgrade `mono_equiv_of_fin` to an `order_iso`, make it `computable`.

### [2021-01-03 02:24:39](https://github.com/leanprover-community/mathlib/commit/9ea7e46)
feat(linear_algebra/alternating): Show the link to linear_independent ([#5477](https://github.com/leanprover-community/mathlib/pull/5477))

### [2021-01-03 02:24:36](https://github.com/leanprover-community/mathlib/commit/04f8fd7)
feat(group_theory/dihedral): add dihedral groups ([#5171](https://github.com/leanprover-community/mathlib/pull/5171))
Contains a subset of the content of [#1076](https://github.com/leanprover-community/mathlib/pull/1076) , but implemented slightly differently.
In [#1076](https://github.com/leanprover-community/mathlib/pull/1076), finite and infinite dihedral groups are implemented separately, but a side effect of what I did was that `dihedral 0` corresponds to the infinite dihedral group.

### [2021-01-03 00:36:14](https://github.com/leanprover-community/mathlib/commit/ee2c963)
doc(overview): pluralization convention ([#5583](https://github.com/leanprover-community/mathlib/pull/5583))
Normalized pluralizations, according to the convention @PatrickMassot described

### [2021-01-03 00:36:12](https://github.com/leanprover-community/mathlib/commit/e698290)
doc(overview): Add alternating_map ([#5582](https://github.com/leanprover-community/mathlib/pull/5582))

### [2021-01-03 00:36:10](https://github.com/leanprover-community/mathlib/commit/1a39825)
doc(overview): combinatorics section ([#5581](https://github.com/leanprover-community/mathlib/pull/5581))
Added overview entries for simple graphs and some pigeonhole principles

### [2021-01-03 00:36:08](https://github.com/leanprover-community/mathlib/commit/5bff887)
doc(overview): add missing algebras to overview ([#5579](https://github.com/leanprover-community/mathlib/pull/5579))

### [2021-01-03 00:36:06](https://github.com/leanprover-community/mathlib/commit/e094606)
chore(topology/algebra/ordered,analysis/specific_limits): two more limits ([#5573](https://github.com/leanprover-community/mathlib/pull/5573))

### [2021-01-02 20:59:51](https://github.com/leanprover-community/mathlib/commit/aa88bb8)
feat(measure_theory/borel_space): the inverse of a closed embedding is measurable ([#5567](https://github.com/leanprover-community/mathlib/pull/5567))

### [2021-01-02 20:59:49](https://github.com/leanprover-community/mathlib/commit/a7d05c4)
chore(number_theory/bernoulli): refactor definition of bernoulli ([#5534](https://github.com/leanprover-community/mathlib/pull/5534))
A minor refactor of the definition of Bernoulli number, and I expanded the docstring.

### [2021-01-02 20:59:48](https://github.com/leanprover-community/mathlib/commit/12b5024)
feat(data/polynomial/erase_lead): add lemma erase_lead_card_support_eq ([#5529](https://github.com/leanprover-community/mathlib/pull/5529))
One further lemma to increase the API of `erase_lead`.  I use it to simplify the proof of the Liouville PR.  In particular, it is used in a step of the proof that you can "clear denominators" when evaluating a polynomial with integer coefficients at a rational number.

### [2021-01-02 17:53:35](https://github.com/leanprover-community/mathlib/commit/fceb7c1)
chore(algebra/group,algebra/group_with_zero): a few more injective/surjective constructors ([#5547](https://github.com/leanprover-community/mathlib/pull/5547))

### [2021-01-02 15:05:58](https://github.com/leanprover-community/mathlib/commit/e142c82)
feat(algebra/group/prod) Units of a product monoid ([#5563](https://github.com/leanprover-community/mathlib/pull/5563))
Just a simple seemingly missing def

### [2021-01-02 10:18:26](https://github.com/leanprover-community/mathlib/commit/e35a703)
feat(algebra/ordered_{group,field}): more lemmas relating inv and mul inequalities ([#5561](https://github.com/leanprover-community/mathlib/pull/5561))
I also renamed `inv_le_iff_one_le_mul` to `inv_le_iff_one_le_mul'` for consistency with `div_le_iff` and `div_le_iff'` (unprimed lemmas involve multiplication on the right and primed lemmas involve multiplication on the left).

### [2021-01-02 10:18:25](https://github.com/leanprover-community/mathlib/commit/f5f879e)
feat(linear_algebra/dimension): linear equiv iff eq dim ([#5559](https://github.com/leanprover-community/mathlib/pull/5559))
See related zulip discussion
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Classification.20of.20finite-dimensional.20vector.20spaces/near/221357275

### [2021-01-02 10:18:22](https://github.com/leanprover-community/mathlib/commit/9f6300e)
chore(data/complex/basic): upgrade `complex.norm_sq` to a `monoid_with_zero_hom` ([#5553](https://github.com/leanprover-community/mathlib/pull/5553))

### [2021-01-02 10:18:20](https://github.com/leanprover-community/mathlib/commit/9d3c05a)
feat(ring_theory/simple_module): simple modules and Schur's Lemma ([#5473](https://github.com/leanprover-community/mathlib/pull/5473))
Defines `is_simple_module` in terms of `is_simple_lattice`
Proves Schur's Lemma
Defines `division ring` structure on the endomorphism ring of a simple module

### [2021-01-02 10:18:18](https://github.com/leanprover-community/mathlib/commit/afc3f03)
feat(algebra/ordered_group): add linear_ordered_comm_group and linear_ordered_cancel_comm_monoid ([#5286](https://github.com/leanprover-community/mathlib/pull/5286))
We have `linear_ordered_add_comm_group` but we didn't have `linear_ordered_comm_group`. This PR adds it, as well as multiplicative versions of `canonically_ordered_add_monoid`, `canonically_linear_ordered_add_monoid` and `linear_ordered_cancel_add_comm_monoid`. I added multiplicative versions of the lemmas about these structures too. The motivation is that I want to slightly generalise the notion of a valuation.
[ also random other bits of tidying which I noticed along the way (docstring fixes, adding `norm_cast` attributes) ].

### [2021-01-02 07:10:53](https://github.com/leanprover-community/mathlib/commit/d94f0a2)
chore(data/list): a list sorted w.r.t. `(<)` has no duplicates ([#5550](https://github.com/leanprover-community/mathlib/pull/5550))

### [2021-01-02 00:36:58](https://github.com/leanprover-community/mathlib/commit/409ea42)
chore(algebra/*): move some lemmas to `div_inv_monoid` ([#5552](https://github.com/leanprover-community/mathlib/pull/5552))

### [2021-01-02 00:36:56](https://github.com/leanprover-community/mathlib/commit/06a11fd)
chore(data/fintype/card): generalize `equiv.prod_comp` to `function.bijective.prod_comp` ([#5551](https://github.com/leanprover-community/mathlib/pull/5551))
This way we can apply it to `add_equiv`, `mul_equiv`, `order_iso`, etc
without using `to_equiv`.

### [2021-01-02 00:36:54](https://github.com/leanprover-community/mathlib/commit/ea3815f)
feat(analysis/normed_space/inner_product): upgrade orthogonal projection to a continuous linear map ([#5543](https://github.com/leanprover-community/mathlib/pull/5543))
Upgrade the orthogonal projection, from a linear map `E →ₗ[𝕜] K` to a continuous linear map `E →L[𝕜] K`.

### [2021-01-02 00:36:53](https://github.com/leanprover-community/mathlib/commit/b57d562)
feat(algebra/big_operators/nat_antidiagonal): add prod_antidiagonal_eq_prod_range_succ ([#5528](https://github.com/leanprover-community/mathlib/pull/5528))
Sometimes summing over nat.antidiagonal is nicer than summing over range(n+1).

### [2021-01-02 00:36:49](https://github.com/leanprover-community/mathlib/commit/c32efea)
feat(data/fin): there is at most one `order_iso` from `fin n` to `α` ([#5499](https://github.com/leanprover-community/mathlib/pull/5499))
* Define a `bounded_lattice` instance on `fin (n + 1)`.
* Prove that there is at most one `order_iso` from `fin n` to `α`.

### [2021-01-01 21:26:00](https://github.com/leanprover-community/mathlib/commit/8aa2332)
chore(*): golf some proofs ([#5548](https://github.com/leanprover-community/mathlib/pull/5548))
Parts of [#5539](https://github.com/leanprover-community/mathlib/pull/5539)

### [2021-01-01 21:25:58](https://github.com/leanprover-community/mathlib/commit/e0030ff)
chore(data/real/cau_seq): golf some proofs ([#5545](https://github.com/leanprover-community/mathlib/pull/5545))

### [2021-01-01 19:02:10](https://github.com/leanprover-community/mathlib/commit/b542cfb)
chore(linear_algebra/basic): notation for span of a singleton ([#5538](https://github.com/leanprover-community/mathlib/pull/5538))
Notation `∙` (`\.`) for the span of a single element of a module, so one can write `R ∙ x` instead of `span R {x}`.  This in itself does not save so many keystrokes, but it also seems to be a bit more robust: it works in settings where previously one had to type `span R ({x} : set M)` because the type of the singleton was not recognised.
[Zulip 1](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20linear.20algebra.20notation), [Zulip 2](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20span)

### [2021-01-01 15:24:16](https://github.com/leanprover-community/mathlib/commit/fcbaf62)
doc(lint/type_classes): add has_coe_to_fun linter ([#5546](https://github.com/leanprover-community/mathlib/pull/5546))

### [2021-01-01 01:33:29](https://github.com/leanprover-community/mathlib/commit/d2bde11)
chore(scripts): update nolints.txt ([#5554](https://github.com/leanprover-community/mathlib/pull/5554))
I am happy to remove some nolints for you!