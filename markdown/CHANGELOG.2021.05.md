### [2021-05-31 21:08:06](https://github.com/leanprover-community/mathlib/commit/bec3e59)
feat(data/finset): provide the coercion `finset α → Type*` ([#7575](https://github.com/leanprover-community/mathlib/pull/7575))
There doesn't seem to be a good reason that `finset` doesn't have a `coe_to_sort` like `set` does. Before the change in this PR, we had to suffer the inconvenience of writing `(↑s : set _)` whenever we want the subtype of all elements of `s`. Now you can just write `s`.
I removed the obvious instances of the `((↑s : set _) : Type*)` pattern, although it definitely remains in some places. I'd rather do those in separate PRs since it does not really do any harm except for being annoying to type. There are also some parts of the API (`polynomial.root_set` stands out to me) that could be designed around the use of `finset`s rather than `set`s that are later proved to be finite, which I again would like to declare out of scope.

### [2021-05-31 21:08:05](https://github.com/leanprover-community/mathlib/commit/ca740b6)
feat(data/finset/powerset): ssubsets and decidability ([#7543](https://github.com/leanprover-community/mathlib/pull/7543))
A few more little additions to finset-world that I found useful.

### [2021-05-31 17:20:15](https://github.com/leanprover-community/mathlib/commit/d272343)
chore(order/lexicographic): add module docstring ([#7768](https://github.com/leanprover-community/mathlib/pull/7768))
add module docstring

### [2021-05-31 17:20:14](https://github.com/leanprover-community/mathlib/commit/033a131)
chore(order/zorn): add module docstring ([#7767](https://github.com/leanprover-community/mathlib/pull/7767))
add module docstring, tidy up notation a bit

### [2021-05-31 15:49:23](https://github.com/leanprover-community/mathlib/commit/d0ebc8e)
feat(ring_theory/laurent_series): Defines Laurent series and their localization map ([#7604](https://github.com/leanprover-community/mathlib/pull/7604))
Defines `laurent_series` as an abbreviation of `hahn_series Z`
Defines `laurent_series.power_series_part`
Shows that the map from power series to Laurent series is a `localization_map`.

### [2021-05-31 14:35:07](https://github.com/leanprover-community/mathlib/commit/4555798)
feat(topology/semicontinuous): semicontinuity of compositions ([#7763](https://github.com/leanprover-community/mathlib/pull/7763))

### [2021-05-31 13:18:14](https://github.com/leanprover-community/mathlib/commit/2af6912)
feat(linear_algebra): the determinant of an endomorphism ([#7635](https://github.com/leanprover-community/mathlib/pull/7635))
 `linear_map.det` is the determinant of an endomorphism, which is defined independent of a basis. If there is no finite basis, the determinant is defined to be equal to `1`.
This approach is inspired by `linear_map.trace`.

### [2021-05-31 13:18:13](https://github.com/leanprover-community/mathlib/commit/7fe456d)
feat(algebra/homology): projective resolutions ([#7486](https://github.com/leanprover-community/mathlib/pull/7486))
# Projective resolutions
A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.
When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory derived functors
without even assuming `C` is abelian.
(Typically, however, to show `has_projective_resolutions C`
one will assume `enough_projectives C` and `abelian C`.
This construction appears in `category_theory.abelian.projectives`.)
We show that give `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)
Moreover, we show that any two such lifts are homotopic.
As a consequence, if every object admits a projective resolution,
we can construct a functor `projective_resolutions C : C ⥤ homotopy_category C`.

### [2021-05-31 06:45:22](https://github.com/leanprover-community/mathlib/commit/1a92c0d)
feat(order/basic): add simp attribute on le_refl, zero_le_one and zero_lt_one ([#7733](https://github.com/leanprover-community/mathlib/pull/7733))
These ones show up so often that they would have deserved a simp attribute long ago.

### [2021-05-30 21:09:58](https://github.com/leanprover-community/mathlib/commit/fd48ac5)
chore(data/list): extract sublists to a separate file ([#7757](https://github.com/leanprover-community/mathlib/pull/7757))
Minor splitting in `data/list/basic`, splitting out `sublists` to its own file, thereby delaying importing `data.nat.choose` in the `list` development.

### [2021-05-30 21:09:57](https://github.com/leanprover-community/mathlib/commit/14b597c)
feat(analysis/normed_space): ∥n • a∥ ≤ n * ∥a∥ ([#7745](https://github.com/leanprover-community/mathlib/pull/7745))
From LTE.

### [2021-05-30 19:15:46](https://github.com/leanprover-community/mathlib/commit/0d842f0)
fix(order/closure): unincorporated reviewer comments from [#7446](https://github.com/leanprover-community/mathlib/pull/7446) ([#7761](https://github.com/leanprover-community/mathlib/pull/7761))

### [2021-05-30 15:26:33](https://github.com/leanprover-community/mathlib/commit/33d803a)
refactor(convex/basic): make convex_hull into a closure operator ([#7446](https://github.com/leanprover-community/mathlib/pull/7446))
Bundle convex_hull as a closure operator, simplify duplicate proofs

### [2021-05-30 09:54:50](https://github.com/leanprover-community/mathlib/commit/25e36be)
chore(data/fintype/basic): `fintype α/β` from `fintype α ⊕ β` ([#7736](https://github.com/leanprover-community/mathlib/pull/7736))
Also renaming the equivalent `α × β` versions, for consistency.

### [2021-05-30 09:54:50](https://github.com/leanprover-community/mathlib/commit/4ea253b)
feat(measure_theory/integration): in a sigma finite space, there exists an integrable positive function ([#7721](https://github.com/leanprover-community/mathlib/pull/7721))

### [2021-05-30 08:29:40](https://github.com/leanprover-community/mathlib/commit/8e25bb6)
feat(algebra/homology): complexes in functor categories ([#7744](https://github.com/leanprover-community/mathlib/pull/7744))
From LTE.

### [2021-05-30 08:29:39](https://github.com/leanprover-community/mathlib/commit/f4d145e)
feat(algebra/homology): construct isomorphisms of complexes ([#7741](https://github.com/leanprover-community/mathlib/pull/7741))
From LTE.

### [2021-05-30 08:29:38](https://github.com/leanprover-community/mathlib/commit/08bb112)
chore(ring_theory/hahn_series): extract lemmas from slow definitions ([#7737](https://github.com/leanprover-community/mathlib/pull/7737))
This doesn't make them much faster, but it makes it easier to tell which bits are slow

### [2021-05-30 04:33:33](https://github.com/leanprover-community/mathlib/commit/e2168e5)
feat(src/ring_theory/derivation): merge duplicates `derivation.comp` and `linear_map.comp_der` ([#7727](https://github.com/leanprover-community/mathlib/pull/7727))
I propose keeping the version introduced in [#7715](https://github.com/leanprover-community/mathlib/pull/7715) since it also contains
the statement that the push forward is linear, but moving it to the `linear_map`
namespace to enable dot notation.
Thanks to @Nicknamen for alerting me to the duplication: https://github.com/leanprover-community/mathlib/pull/7715#issuecomment-849192370

### [2021-05-30 04:33:32](https://github.com/leanprover-community/mathlib/commit/9d63c38)
feat(topology/continuous_function/algebra): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7720](https://github.com/leanprover-community/mathlib/pull/7720))

### [2021-05-30 01:16:52](https://github.com/leanprover-community/mathlib/commit/a3ba4d4)
feat(algebra/homology): eval and forget functors ([#7742](https://github.com/leanprover-community/mathlib/pull/7742))
From LTE.

### [2021-05-29 18:15:17](https://github.com/leanprover-community/mathlib/commit/035aa60)
feat(analysis/normed_space): SemiNormedGroup.has_zero_object ([#7740](https://github.com/leanprover-community/mathlib/pull/7740))
From LTE.

### [2021-05-29 02:32:43](https://github.com/leanprover-community/mathlib/commit/1ac49b0)
chore(category_theory): dualize filtered categories to cofiltered categories ([#7731](https://github.com/leanprover-community/mathlib/pull/7731))
Per request on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/status.20update/near/240548989).
I have not attempted to dualize "filtered colimits commute with finite limits", as I've never heard of that being used.

### [2021-05-28 19:12:47](https://github.com/leanprover-community/mathlib/commit/f74a375)
chore(linear_algebra/finsupp): remove useless lemma ([#7734](https://github.com/leanprover-community/mathlib/pull/7734))
The lemma is not used in mathlib, it's mathematically useless (you'd never have a surjective function from an indexing set to a module), and it's badly named, so I propose removing it entirely.

### [2021-05-28 15:21:27](https://github.com/leanprover-community/mathlib/commit/13746fe)
feat(group_theory/subgroup linear_algebra/prod): add ker_prod_map ([#7729](https://github.com/leanprover-community/mathlib/pull/7729))
The kernel of the product of two `group_hom` is the product of the kernels (and similarly for monoids).

### [2021-05-28 11:55:01](https://github.com/leanprover-community/mathlib/commit/5fff3b1)
feat(ring_theory/mv_polynomial/basic): add polynomial.basis_monomials ([#7728](https://github.com/leanprover-community/mathlib/pull/7728))
We add `polynomial.basis_monomials` : the monomials form a basis on `polynomial R`.
Because of the structure of the import, it seems to me a little complicated to do it directly, so I use `mv_polynomial.punit_alg_equiv`

### [2021-05-27 09:01:17](https://github.com/leanprover-community/mathlib/commit/5360e47)
feat(algebra/module/linear_map): `linear_(map|equiv).restrict_scalars` is injective ([#7725](https://github.com/leanprover-community/mathlib/pull/7725))
So as not to repeat them for the lemmas, I moved the typeclasses into a `variables` statement.

### [2021-05-27 05:47:47](https://github.com/leanprover-community/mathlib/commit/6109558)
chore(category_theory/*): provide aliases quiver.hom.le and has_le.le.hom ([#7677](https://github.com/leanprover-community/mathlib/pull/7677))

### [2021-05-27 00:46:29](https://github.com/leanprover-community/mathlib/commit/a85fbda)
feat(algebra/opposites): add units.op_equiv ([#7723](https://github.com/leanprover-community/mathlib/pull/7723))

### [2021-05-27 00:46:28](https://github.com/leanprover-community/mathlib/commit/20291d0)
feat(topology/semicontinuous): basics on lower and upper semicontinuous functions ([#7693](https://github.com/leanprover-community/mathlib/pull/7693))
We mimick the interface for continuity, by introducing predicates `lower_semicontinuous_within_at`, `lower_semicontinuous_at`, `lower_semicontinuous_on` and `lower_semicontinuous` (and similarly for upper semicontinuity).

### [2021-05-26 21:50:17](https://github.com/leanprover-community/mathlib/commit/0970fda)
feat(measure_theory/regular): more material on regular measures ([#7680](https://github.com/leanprover-community/mathlib/pull/7680))
This PR:
* defines weakly regular measures
* shows that for weakly regular measures any finite measure set can be approximated from inside by closed sets
* shows that for regular measures any finite measure set can be approximated from inside by compact sets
* shows that any finite measure on a metric space is weakly regular
* shows that any locally finite measure on a sigma compact locally compact metric space is regular

### [2021-05-26 21:50:16](https://github.com/leanprover-community/mathlib/commit/a2e8b3c)
feat(special_functions/polynomials): Generalize some polynomial asymptotics to iff statements. ([#7545](https://github.com/leanprover-community/mathlib/pull/7545))

### [2021-05-26 19:17:45](https://github.com/leanprover-community/mathlib/commit/fd43ce0)
feat(linear_algebra/matrix): generalize `basis.to_matrix_mul_to_matrix` ([#7670](https://github.com/leanprover-community/mathlib/pull/7670))
Now the second family of vectors does not have to form a basis.

### [2021-05-26 13:34:28](https://github.com/leanprover-community/mathlib/commit/fa27c0c)
feat(ring_theory/derivation): define push forward of derivations ([#7715](https://github.com/leanprover-community/mathlib/pull/7715))

### [2021-05-26 13:34:27](https://github.com/leanprover-community/mathlib/commit/b059708)
feat(data/nnreal): filling out some lemmas ([#7710](https://github.com/leanprover-community/mathlib/pull/7710))
From LTE.

### [2021-05-26 13:34:26](https://github.com/leanprover-community/mathlib/commit/273546e)
feat(group_theory/sub{group,monoid,semiring,ring}): subobjects inherit the actions of their carrier type ([#7665](https://github.com/leanprover-community/mathlib/pull/7665))
This acts as a generalization of `algebra.of_subsemiring` and `algebra.of_subring`, and transfers the weaker action structures too.

### [2021-05-26 13:34:25](https://github.com/leanprover-community/mathlib/commit/66ec15c)
feat(analysis/complex/isometry): add linear_isometry_complex ([#6923](https://github.com/leanprover-community/mathlib/pull/6923))
add proof about the isometries in the complex plane

### [2021-05-26 08:25:18](https://github.com/leanprover-community/mathlib/commit/a741f64)
docs(*): spelling ([#7719](https://github.com/leanprover-community/mathlib/pull/7719))

### [2021-05-26 08:25:17](https://github.com/leanprover-community/mathlib/commit/58c57ca)
fix(linear_algebra/tensor_product): relax from module to distrib_mul_action ([#7709](https://github.com/leanprover-community/mathlib/pull/7709))
This was an accident in [#7516](https://github.com/leanprover-community/mathlib/pull/7516) where the wrong variable was used. `R'` is the base of a distrib_mul_action, `R''`, is the base of a module.

### [2021-05-26 08:25:16](https://github.com/leanprover-community/mathlib/commit/71dcb64)
feat(order/conditionally_complete_lattice): add lemmas ([#7689](https://github.com/leanprover-community/mathlib/pull/7689))
These lemmas names match the version that already exist without the `c` prefix.
This also renames `finset.sup_eq_Sup` to `finset.sup_id_eq_Sup`, and introduces a new `finset.sup_eq_Sup_image`.

### [2021-05-26 08:25:15](https://github.com/leanprover-community/mathlib/commit/00394b7)
feat(tactic/simps): implement prefix names ([#7596](https://github.com/leanprover-community/mathlib/pull/7596))
* You can now write `initialize_simps_projections equiv (to_fun → coe as_prefix)` to add the projection name as a prefix to the simp lemmas: if you then write `@[simps coe] def foo ...` you get a lemma named `coe_foo`.
* Remove the `short_name` option from `simps_cfg`. This was unused and not that useful. 
* Refactor some tuples used in the functions into structures.
* Implements one item of [#5489](https://github.com/leanprover-community/mathlib/pull/5489).

### [2021-05-26 06:48:35](https://github.com/leanprover-community/mathlib/commit/1f566bc)
chore(scripts): update nolints.txt ([#7718](https://github.com/leanprover-community/mathlib/pull/7718))
I am happy to remove some nolints for you!

### [2021-05-26 06:48:34](https://github.com/leanprover-community/mathlib/commit/f7f0a30)
feat(scripts/lint-style.py): add linter that disables importing omega ([#7646](https://github.com/leanprover-community/mathlib/pull/7646))
* Files in mathlib are not allowed to `import tactic` or `import tactic.omega`. This adds a style linter to enforce this.
* `tactic.default` is allowed to import `tactic.omega` (other files that only import other files are excluded from these checks, so a malicious user still could get around this linter, but it's hard to imagine this happening accidentally)
* Remove `import tactic` from 3 files (in `archive/` and `test/`)

### [2021-05-26 00:55:46](https://github.com/leanprover-community/mathlib/commit/fd1c8e7)
feat(data/list/forall2): add two lemmas about forall₂ and reverse ([#7714](https://github.com/leanprover-community/mathlib/pull/7714))
rel_reverse shows that forall₂ is preserved across reversed lists,
forall₂_iff_reverse uses rel_reverse to show that it is preserved in
both directions.

### [2021-05-25 23:21:27](https://github.com/leanprover-community/mathlib/commit/360ca9c)
feat(analysis/special_functions/integrals): `interval_integrable_log` ([#7713](https://github.com/leanprover-community/mathlib/pull/7713))

### [2021-05-25 23:21:26](https://github.com/leanprover-community/mathlib/commit/f1425b6)
feat(measure_theory/interval_integral): `integral_comp_add_left` ([#7712](https://github.com/leanprover-community/mathlib/pull/7712))

### [2021-05-25 19:48:36](https://github.com/leanprover-community/mathlib/commit/82e78ce)
feat(algebra/big_operators/finprod): add lemma `finprod_mem_finset_of_product` ([#7439](https://github.com/leanprover-community/mathlib/pull/7439))

### [2021-05-25 17:19:09](https://github.com/leanprover-community/mathlib/commit/8078eca)
feat(linear_algebra): `det (M ⬝ N ⬝ M') = det N`, where `M'` is an inverse of `M` ([#7633](https://github.com/leanprover-community/mathlib/pull/7633))
This is an important step towards showing the determinant of `linear_map.to_matrix` does not depend on the choice of basis.
    
The main difficulty is allowing the two indexing types of `M` to be (a priori) different. They are in bijection though (using `basis.index_equiv` from [#7631](https://github.com/leanprover-community/mathlib/pull/7631)), so using `reindex_linear_equiv` we can turn everything into square matrices and apply the "usual" proof.

### [2021-05-25 15:58:58](https://github.com/leanprover-community/mathlib/commit/c17c738)
feat(logic/girard): move file to counterexamples ([#7706](https://github.com/leanprover-community/mathlib/pull/7706))
Since the file feels like a counterexample, I suggest putting it in that folder.

### [2021-05-25 15:58:57](https://github.com/leanprover-community/mathlib/commit/a617d0a)
feat(algebra/category/Module): R-mod has enough projectives ([#7113](https://github.com/leanprover-community/mathlib/pull/7113))
Another piece of @TwoFX's `projective` branch, lightly edited.

### [2021-05-25 11:18:58](https://github.com/leanprover-community/mathlib/commit/bbf6150)
feat(measure_theory/measurable_space): add instances for subtypes ([#7702](https://github.com/leanprover-community/mathlib/pull/7702))

### [2021-05-25 11:18:57](https://github.com/leanprover-community/mathlib/commit/75e07d1)
feat(linear_algebra/matrix/determinant): lemmas about commutativity under det ([#7685](https://github.com/leanprover-community/mathlib/pull/7685))

### [2021-05-25 11:18:56](https://github.com/leanprover-community/mathlib/commit/4abbe10)
feat(group_theory/group_action/units): group actions on and by units ([#7438](https://github.com/leanprover-community/mathlib/pull/7438))
This removes all the lemmas about `(u : α) • x` and `(↑u⁻¹ : α) • x` in favor of granting `units α` its very own `has_scalar` structure, along with providing the stronger variants to make it usable elsewhere.
This means that downstream code need only reason about `[group G] [mul_action G M]` instead of needing to handle groups and `units` separately.
The (multiplicative versions of the) removed and moved lemmas are:
* `units.inv_smul_smul` &rarr; `inv_smul_smul`
* `units.smul_inv_smul` &rarr; `smul_inv_smul`
* `units.smul_perm_hom`, `mul_action.to_perm` &rarr; `mul_action.to_perm_hom`
* `units.smul_perm` &rarr; `mul_action.to_perm`
* `units.smul_left_cancel` &rarr; `smul_left_cancel`
* `units.smul_eq_iff_eq_inv_smul` &rarr; `smul_eq_iff_eq_inv_smul`
* `units.smul_eq_zero` &rarr; `smul_eq_zero_iff_eq` (to avoid clashing with `smul_eq_zero`)
* `units.smul_ne_zero` &rarr; `smul_ne_zero_iff_ne`
* `homeomorph.smul_of_unit` &rarr; `homeomorph.smul` (the latter already existed, and the former was a special case)
* `units.measurable_const_smul_iff` &rarr; `measurable_const_smul_iff`
* `units.ae_measurable_const_smul_iff` &rarr; `ae_measurable_const_smul_iff`
The new lemmas are:
* `smul_eq_zero_iff_eq'`, a `group_with_zero` version of `smul_eq_zero_iff_eq`
* `smul_ne_zero_iff_ne'`, a `group_with_zero` version of `smul_ne_zero_iff_ne`
* `units.neg_smul`, a version of `neg_smul` for units. We don't currently have typeclasses about `neg` on objects without `+`.
We also end up needing some new typeclass instances downstream
* `units.measurable_space`
* `units.has_measurable_smul`
* `units.has_continuous_smul`
This goes on to remove lots of coercions from `alternating_map`, `matrix.det`, and some lie algebra stuff.
This makes the theorem statement cleaner, but occasionally requires rewriting through `units.smul_def` to add or remove the coercion.

### [2021-05-25 05:41:54](https://github.com/leanprover-community/mathlib/commit/d81fcda)
feat(algebra/group_with_zero): add some equational lemmas ([#7705](https://github.com/leanprover-community/mathlib/pull/7705))
Add some equations for `group_with_zero` that are direct analogues of lemmas for `group`.
Useful for [#6923](https://github.com/leanprover-community/mathlib/pull/6923).

### [2021-05-25 00:46:31](https://github.com/leanprover-community/mathlib/commit/a880ea4)
feat(ring_theory/coprime): add some lemmas ([#7650](https://github.com/leanprover-community/mathlib/pull/7650))

### [2021-05-25 00:46:30](https://github.com/leanprover-community/mathlib/commit/c3dcb7d)
feat(category_theory/limits): comma category colimit construction ([#7535](https://github.com/leanprover-community/mathlib/pull/7535))
As well as the duals. Also adds some autoparams for consistency with `has_limit` and some missing instances which are basically just versions of existing things

### [2021-05-24 19:29:16](https://github.com/leanprover-community/mathlib/commit/17f3b80)
feat(100-theorems-list/16_abel_ruffini): some simplifications ([#7699](https://github.com/leanprover-community/mathlib/pull/7699))

### [2021-05-24 19:29:15](https://github.com/leanprover-community/mathlib/commit/51526ae)
chore(topology): rename mem_nhds_sets and mem_of_nhds and mem_nhds_sets_iff ([#7690](https://github.com/leanprover-community/mathlib/pull/7690))
Rename `mem_nhds_sets` to `is_open.mem_nhds`, and `mem_nhds_sets_iff` to `mem_nhds_iff`, and `mem_of_nhds` to `mem_of_mem_nhds`.

### [2021-05-24 14:07:33](https://github.com/leanprover-community/mathlib/commit/91a547e)
feat(algebra/opposites): `(un)op_ne_zero_iff` ([#7698](https://github.com/leanprover-community/mathlib/pull/7698))

### [2021-05-24 14:07:32](https://github.com/leanprover-community/mathlib/commit/a09ddc7)
feat(measure_theory/interval_integral): `interval_integrable.mono` ([#7679](https://github.com/leanprover-community/mathlib/pull/7679))
`interval_integrable f ν a b → interval c d ⊆ interval a b → μ ≤ ν → interval_integrable f μ c d`

### [2021-05-24 11:01:13](https://github.com/leanprover-community/mathlib/commit/0b51a72)
feat(linear_algebra/determinant): specialize `is_basis.iff_det` ([#7668](https://github.com/leanprover-community/mathlib/pull/7668))
After the bundled basis refactor, applying `is_basis.iff_det` in the forward direction is slightly more involved (since defining the `iff` requires an unbundled basis), so I added a lemma that does the necessary translation between "unbundled basis" and "bundled basis" for you.

### [2021-05-24 11:01:12](https://github.com/leanprover-community/mathlib/commit/8ff2783)
feat(counterexamples/cyclotomic_105): add coeff_cyclotomic_105 ([#7648](https://github.com/leanprover-community/mathlib/pull/7648))
We show that `coeff (cyclotomic 105 ℤ) 7 = -2`, proving that not all coefficients of cyclotomic polynomials are `0`, `-1` or `1`.

### [2021-05-24 05:13:08](https://github.com/leanprover-community/mathlib/commit/16733c8)
chore(data/nat/basic): move unique {units/add_units} instances ([#7701](https://github.com/leanprover-community/mathlib/pull/7701))

### [2021-05-23 23:25:01](https://github.com/leanprover-community/mathlib/commit/2734d91)
fix(data/nat/factorial): fix factorial_zero ([#7697](https://github.com/leanprover-community/mathlib/pull/7697))

### [2021-05-23 16:33:37](https://github.com/leanprover-community/mathlib/commit/6cffc9f)
chore(logic/unique): a true prop is unique ([#7688](https://github.com/leanprover-community/mathlib/pull/7688))
I found myself needing to construct this instance by hand somewhere; since we already need it to construct `unique true`, we may as well make a def.

### [2021-05-23 13:50:13](https://github.com/leanprover-community/mathlib/commit/57cd5ef)
refactor(*): remove some uses of omega in the library ([#7700](https://github.com/leanprover-community/mathlib/pull/7700))

### [2021-05-22 21:53:35](https://github.com/leanprover-community/mathlib/commit/97a5276)
doc(number_theory/bernoulli): write statements in math mode ([#7696](https://github.com/leanprover-community/mathlib/pull/7696))
* It took me some work to see the difference between the two statements, so I added the statements in math mode.
* Change name `sum_range_pow'` -> `sum_Ico_pow`

### [2021-05-22 16:17:14](https://github.com/leanprover-community/mathlib/commit/fb95362)
fix(algebra/homology): imports ([#7655](https://github.com/leanprover-community/mathlib/pull/7655))

### [2021-05-22 12:15:37](https://github.com/leanprover-community/mathlib/commit/0e216ce)
feat(order): if s is finite then Sup s ∈ s ([#7682](https://github.com/leanprover-community/mathlib/pull/7682))

### [2021-05-22 12:15:36](https://github.com/leanprover-community/mathlib/commit/418dc04)
feat(100-theorems-list/16_abel_ruffini): The Abel-Ruffini Theorem ([#7562](https://github.com/leanprover-community/mathlib/pull/7562))
It's done!

### [2021-05-22 06:50:13](https://github.com/leanprover-community/mathlib/commit/b29d40c)
fix(algebra): change local transparency to semireducible ([#7687](https://github.com/leanprover-community/mathlib/pull/7687))
* When a type is `[irreducible]` it should locally be made `[semireducible]` and (almost) never `[reducible]`. 
* If it is made `[reducible]`, type-class inference will unfold this definition, and will apply instances that would not type-check when the definition is `[irreducible]`

### [2021-05-21 21:35:13](https://github.com/leanprover-community/mathlib/commit/f8530d5)
feat(ring_theory/ideal/operations): `ideal.span_singleton_pow` ([#7660](https://github.com/leanprover-community/mathlib/pull/7660))

### [2021-05-21 16:38:59](https://github.com/leanprover-community/mathlib/commit/f70e160)
chore(order/conditionally_complete_lattice): golf proofs with `order_dual` ([#7684](https://github.com/leanprover-community/mathlib/pull/7684))
Even in the places where this doesn't result in a shorter proof, it makes it obvious that the `inf` lemmas have a matching `sup` lemma.

### [2021-05-21 11:28:01](https://github.com/leanprover-community/mathlib/commit/233eff0)
feat(data/fintype/card_embedding): the birthday problem ([#7363](https://github.com/leanprover-community/mathlib/pull/7363))

### [2021-05-21 00:33:53](https://github.com/leanprover-community/mathlib/commit/1924742)
feat(data/set/basic): allow dot notation for trans and antisymm ([#7681](https://github.com/leanprover-community/mathlib/pull/7681))
Allow to write
```lean
example {α : Type*} {a b c : set α} (h : a ⊆ b)  (h': b ⊆ c) : a ⊆ c :=
h.trans h'
example {α : Type*} {a b : set α} (h : a ⊆ b)  (h': b ⊆ a) : 
  a = b := h.antisymm h'
example {α : Type*} {a b c : finset α} (h : a ⊆ b)  (h': b ⊆ c) : a ⊆ c :=
h.trans h'
example {α : Type*} {a b : finset α} (h : a ⊆ b)  (h': b ⊆ a) : a = b :=
h.antisymm h'
```

### [2021-05-21 00:33:52](https://github.com/leanprover-community/mathlib/commit/53e2307)
feat(ring_theory): every left-noetherian ring has invariant basis number ([#7678](https://github.com/leanprover-community/mathlib/pull/7678))
This is a lovely case where we get more for less.
By directly proving that every left-noetherian ring has invariant basis number, we don't need to import `linear_algebra.finite_dimensional` in order to do the `field` case. This means that in a future PR we can instead import `ring_theory.invariant_basis_number` in `linear_algebra.finite_dimensional`, and set up the theory of bases in greater generality.

### [2021-05-21 00:33:51](https://github.com/leanprover-community/mathlib/commit/c63c6d1)
feat(order/closure): make closure operators implementable ([#7608](https://github.com/leanprover-community/mathlib/pull/7608))
introduce `lower_adjoint` as a way to talk about closure operators whose input and output types do not match

### [2021-05-20 19:10:37](https://github.com/leanprover-community/mathlib/commit/32b433d)
refactor(*): remove some uses of omega in the library ([#7620](https://github.com/leanprover-community/mathlib/pull/7620))
In [#6129](https://github.com/leanprover-community/mathlib/pull/6129), we stopped using `omega` to avoid porting it to lean4.
Some new uses were added since then.

### [2021-05-20 15:24:52](https://github.com/leanprover-community/mathlib/commit/d47a6e3)
feat(topology): clopens form a topology basis for profinite sets ([#7671](https://github.com/leanprover-community/mathlib/pull/7671))
from LTE

### [2021-05-20 13:34:18](https://github.com/leanprover-community/mathlib/commit/d3ec77c)
feat(category_theory/limits): reflecting limits of isomorphic diagram ([#7674](https://github.com/leanprover-community/mathlib/pull/7674))

### [2021-05-20 08:06:42](https://github.com/leanprover-community/mathlib/commit/c5951f3)
feat(ring_theory/noetherian): a surjective endomorphism of a noetherian module is injective ([#7676](https://github.com/leanprover-community/mathlib/pull/7676))

### [2021-05-20 08:06:41](https://github.com/leanprover-community/mathlib/commit/ff51159)
feat(algebra/homology/*): add hypotheses to the d_comp_d' axiom ([#7673](https://github.com/leanprover-community/mathlib/pull/7673))

### [2021-05-20 08:06:40](https://github.com/leanprover-community/mathlib/commit/2d414d0)
feat(algebra/homology/homological_complex): add condition to hom.comm' ([#7666](https://github.com/leanprover-community/mathlib/pull/7666))

### [2021-05-20 08:06:39](https://github.com/leanprover-community/mathlib/commit/0cb7ecc)
fix(category_theory/limits/shapes/zero): use fully qualified names in locale ([#7619](https://github.com/leanprover-community/mathlib/pull/7619))

### [2021-05-20 02:00:39](https://github.com/leanprover-community/mathlib/commit/5a67f2c)
chore(topology): rename compact to is_compact in theorem names ([#7672](https://github.com/leanprover-community/mathlib/pull/7672))
Some time ago, we switched from `compact` to `is_compact`, for coherence with `is_open`, `is_closed` and so on. However, several lemma names were not changed at the time. This PR fixes some of them. Plus a few minor stuff (notably, introduce `le_self_add` to replace the dozen of uses of `le_add_right (le_refl _)` in the library -- and weaken some `metric` assumptions to `pseudo_metric`, without touching the proofs).

### [2021-05-20 02:00:37](https://github.com/leanprover-community/mathlib/commit/1016a14)
refactor(linear_algebra/finite_dimensional): generalize finite_dimensional.iff_fg to division rings ([#7644](https://github.com/leanprover-community/mathlib/pull/7644))
Replace `finite_dimensional.iff_fg` (working over a field) with `is_noetherian.iff_fg` (working over a division ring). Also, use the `module.finite` predicate.

### [2021-05-20 02:00:36](https://github.com/leanprover-community/mathlib/commit/641cece)
feat(algebra/homology): the homotopy category ([#7484](https://github.com/leanprover-community/mathlib/pull/7484))

### [2021-05-19 19:28:27](https://github.com/leanprover-community/mathlib/commit/116c162)
feat(algebra/opposites): `opposite` of a `group_with_zero` ([#7662](https://github.com/leanprover-community/mathlib/pull/7662))
Co-authored by @eric-wieser

### [2021-05-19 15:49:00](https://github.com/leanprover-community/mathlib/commit/ed4161c)
feat(data/polynomial/coeff): generalize polynomial.coeff_smul to match mv_polynomial.coeff_smul ([#7663](https://github.com/leanprover-community/mathlib/pull/7663))
Notably this means these lemmas cover `nat` and `int` actions.

### [2021-05-19 15:48:58](https://github.com/leanprover-community/mathlib/commit/599712f)
feat(data/int/parity, data/nat/parity): add some lemmas ([#7624](https://github.com/leanprover-community/mathlib/pull/7624))

### [2021-05-19 12:41:13](https://github.com/leanprover-community/mathlib/commit/697c8dd)
refactor(topology/basic): use dot notation in `is_open.union` and friends ([#7647](https://github.com/leanprover-community/mathlib/pull/7647))
The fact that the union of two open sets is open is called `is_open_union`. We rename it to `is_open.union` to enable dot notation. Same with `is_open_inter`, `is_closed_union` and `is_closed_inter` and `is_clopen_union` and `is_clopen_inter` and `is_clopen_diff`.

### [2021-05-19 09:57:34](https://github.com/leanprover-community/mathlib/commit/c7a5197)
feat(data/polynomial/degree/definitions): `polynomial.degree_C_mul_X_le` ([#7659](https://github.com/leanprover-community/mathlib/pull/7659))

### [2021-05-19 09:57:33](https://github.com/leanprover-community/mathlib/commit/040ebea)
fix(analysis/normed_space/normed_group_quotient): put lemmas inside namespace  ([#7653](https://github.com/leanprover-community/mathlib/pull/7653))

### [2021-05-19 08:44:51](https://github.com/leanprover-community/mathlib/commit/c1e9f94)
docs(field_theory/polynomial_galois_group): improve existing docs ([#7586](https://github.com/leanprover-community/mathlib/pull/7586))

### [2021-05-19 02:36:44](https://github.com/leanprover-community/mathlib/commit/1d4990e)
chore(scripts): update nolints.txt ([#7658](https://github.com/leanprover-community/mathlib/pull/7658))
I am happy to remove some nolints for you!

### [2021-05-19 02:36:43](https://github.com/leanprover-community/mathlib/commit/918dcc0)
chore(algebra/homology): further dualization ([#7657](https://github.com/leanprover-community/mathlib/pull/7657))

### [2021-05-19 02:36:42](https://github.com/leanprover-community/mathlib/commit/aee918b)
feat(algebraic_topology/simplicial_object): Some API for converting between simplicial and cosimplicial ([#7656](https://github.com/leanprover-community/mathlib/pull/7656))
This adds some code which is helpful to convert back and forth between simplicial and cosimplicial object.
For augmented objects, this doesn't follow directly from the existing API in `category_theory/opposite`.

### [2021-05-19 01:16:47](https://github.com/leanprover-community/mathlib/commit/24d2713)
feat(algebraic_topology/simplicial_object): Whiskering of simplicial objects. ([#7651](https://github.com/leanprover-community/mathlib/pull/7651))
This adds whiskering constructions for (truncated, augmented) (co)simplicial objects.

### [2021-05-18 22:27:07](https://github.com/leanprover-community/mathlib/commit/0bcfff9)
feat(linear_algebra/basis) remove several [nontrivial R] ([#7642](https://github.com/leanprover-community/mathlib/pull/7642))
We remove some unnecessary `nontrivial R`.

### [2021-05-18 16:02:45](https://github.com/leanprover-community/mathlib/commit/a51d1e0)
feat(algebra/homology/homological_complex): Dualizes some constructions ([#7643](https://github.com/leanprover-community/mathlib/pull/7643))
This PR adds `cochain_complex.of` and `cochain_complex.of_hom`. 
Still not done: `cochain_complex.mk`.

### [2021-05-18 16:02:44](https://github.com/leanprover-community/mathlib/commit/e275604)
chore(data/set/basic): add `set.compl_eq_compl` ([#7641](https://github.com/leanprover-community/mathlib/pull/7641))

### [2021-05-18 10:47:24](https://github.com/leanprover-community/mathlib/commit/c2114d4)
refactor(linear_algebra/dimension): generalize definition of `module.rank` ([#7634](https://github.com/leanprover-community/mathlib/pull/7634))
The main change is to generalize the definition of `module.rank`. It used to be the infimum over cardinalities of bases, and is now the supremum over cardinalities of linearly independent sets.
I have not attempted to systematically generalize  theorems about the rank; there is lots more work to be done. For now I've just made a few easy generalizations (either replacing `field` with `division_ring`, or `division_ring` with `ring`+`nontrivial`).

### [2021-05-18 10:47:23](https://github.com/leanprover-community/mathlib/commit/e6c787f)
feat(algebra/opposites): add `has_scalar (opposite α) α` instances ([#7630](https://github.com/leanprover-community/mathlib/pull/7630))
The action is defined as:
```lean
lemma op_smul_eq_mul [monoid α] {a a' : α} : op a • a' = a' * a := rfl
```
We have a few of places in the library where we prove things about `r • b`, and then extract a proof of `a * b = a • b` for free. However, we have no way to do this for `b * a` right now unless multiplication is commutative.
By adding this action, we have `b * a = op a • b` so in many cases could reuse the smul lemma.
This instance does not create a diamond:
```lean
-- the two paths to `mul_action (opposite α) (opposite α)` are defeq
example [monoid α] : monoid.to_mul_action (opposite α) = opposite.mul_action α (opposite α) := rfl
```
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Right.20multiplication.20as.20a.20mul_action/near/239012917)

### [2021-05-18 04:50:02](https://github.com/leanprover-community/mathlib/commit/1a2781a)
feat(analysis/normed_space): the category of seminormed groups ([#7617](https://github.com/leanprover-community/mathlib/pull/7617))
From LTE, along with adding `SemiNormedGroup₁`, the subcategory of norm non-increasing maps.

### [2021-05-18 04:50:01](https://github.com/leanprover-community/mathlib/commit/3694945)
feat(logic/is_empty): Add is_empty typeclass ([#7606](https://github.com/leanprover-community/mathlib/pull/7606))
* Refactor some equivalences that use `empty` or `pempty`.
* Replace `α → false` with `is_empty α` in various places (but not everywhere, we can do that in follow-up PRs).
* `infinite` is proven equivalent to `is_empty (fintype α)`. The old `not_fintype` is renamed to `fintype.false` (to allow projection notation), and there are two useful variants `infinite.false` and `not_fintype` added with different arguments explicit.
* add instance `unique true`.
* Changed the type of `fin_one_equiv` from `fin 1 ≃ punit` to `fin 1 ≃ unit` (it was used only once, where the former formulation required giving an explicit universe level).
* renamings:
`equiv.subsingleton_iff` -> `equiv.subsingleton_congr`
`finprod_of_empty` -> `finprod_of_is_empty`

### [2021-05-18 04:49:59](https://github.com/leanprover-community/mathlib/commit/1b864c0)
feat(analysis/normed_group): quotients ([#7603](https://github.com/leanprover-community/mathlib/pull/7603))
From LTE.

### [2021-05-18 02:58:27](https://github.com/leanprover-community/mathlib/commit/f900513)
feat(linear_algebra/matrix): slightly generalize `smul_left_mul_matrix` ([#7632](https://github.com/leanprover-community/mathlib/pull/7632))
Two minor changes that make `smul_left_mul_matrix` slightly easier to apply:
 * the bases `b` and `c` can now be indexed by different types
 * replace `(i, k)` on the LHS with `ik.1 ik.2` on the RHS (so you don't have to introduce the constructor with `rw ← prod.mk.eta` somewhere deep in your expression)

### [2021-05-17 23:05:07](https://github.com/leanprover-community/mathlib/commit/b8a6995)
feat(data/polynomial): the `d-1`th coefficient of `polynomial.map` ([#7639](https://github.com/leanprover-community/mathlib/pull/7639))
We prove `polynomial.next_coeff_map` just like `polynomial.leading_coeff_map'`.

### [2021-05-17 23:05:06](https://github.com/leanprover-community/mathlib/commit/ccf5188)
feat(ring_theory/power_basis): the dimension of a power basis is positive ([#7638](https://github.com/leanprover-community/mathlib/pull/7638))
We already have `pb.dim_ne_zero : pb.dim ≠ 0` (assuming nontriviality), but it's also useful to also have it in the form `0 < pb.dim`.

### [2021-05-17 18:10:36](https://github.com/leanprover-community/mathlib/commit/4ab0e35)
feat(data/multiset): the product of inverses is the inverse of the product ([#7637](https://github.com/leanprover-community/mathlib/pull/7637))
Entirely analogous to `prod_map_mul` defined above.

### [2021-05-17 12:38:51](https://github.com/leanprover-community/mathlib/commit/818dffa)
feat(linear_algebra): a finite free module has a unique findim ([#7631](https://github.com/leanprover-community/mathlib/pull/7631))
I needed this easy corollary, so I PR'd it, even though it should be generalizable once we have a better theory of e.g. Gaussian elimination. (I also tried to generalize `mk_eq_mk_of_basis`, but the current proof really requires the existence of multiplicative inverses for the coefficients.)

### [2021-05-17 12:38:50](https://github.com/leanprover-community/mathlib/commit/36e0127)
feat(linear_algebra/basic): add_monoid_hom_lequiv_int ([#7629](https://github.com/leanprover-community/mathlib/pull/7629))
From LTE.

### [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/d201a18)
refactor(algebra/homology/homotopy): avoid needing has_zero_object ([#7621](https://github.com/leanprover-community/mathlib/pull/7621))
A refactor of the definition of `homotopy`, so we don't need `has_zero_object`.

### [2021-05-17 12:38:49](https://github.com/leanprover-community/mathlib/commit/07fb3d7)
refactor(data/finsupp/antidiagonal): Make antidiagonal a finset ([#7595](https://github.com/leanprover-community/mathlib/pull/7595))
Pursuant to discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/antidiagonals.20having.20multiplicity) 
Refactoring so that `finsupp.antidiagonal` and `multiset.antidiagonal` are finsets.
~~Still TO DO: `multiset.antidiagonal`~~

### [2021-05-17 08:05:30](https://github.com/leanprover-community/mathlib/commit/8394e59)
feat(data/finset/basic): perm_of_nodup_nodup_to_finset_eq ([#7588](https://github.com/leanprover-community/mathlib/pull/7588))
Also `finset.exists_list_nodup_eq`.

### [2021-05-17 06:01:44](https://github.com/leanprover-community/mathlib/commit/739d93c)
feat(algebra/lie/weights): the zero root subalgebra is self-normalizing ([#7622](https://github.com/leanprover-community/mathlib/pull/7622))

### [2021-05-17 03:57:28](https://github.com/leanprover-community/mathlib/commit/2077c90)
doc(counterexamples/canonically_ordered_comm_semiring_two_mul): fix url ([#7625](https://github.com/leanprover-community/mathlib/pull/7625))

### [2021-05-17 02:40:40](https://github.com/leanprover-community/mathlib/commit/d40e40c)
chore(scripts): update nolints.txt ([#7627](https://github.com/leanprover-community/mathlib/pull/7627))
I am happy to remove some nolints for you!

### [2021-05-17 01:22:19](https://github.com/leanprover-community/mathlib/commit/72e4cca)
ci(.github/workflows/build.yml): check counterexamples ([#7618](https://github.com/leanprover-community/mathlib/pull/7618))
I meant to add this to [#7553](https://github.com/leanprover-community/mathlib/pull/7553) but I forgot before it got merged.
This also moves the contents of `src/counterexamples` to `counterexamples/`.

### [2021-05-17 00:02:12](https://github.com/leanprover-community/mathlib/commit/84a27d6)
feat(set_theory/game): add mul_one and mul_assoc for pgames ([#7610](https://github.com/leanprover-community/mathlib/pull/7610))
and several `simp` lemmas. I also simplified some of the existing proofs using `rw` and `simp` and made them easier to read.
This is the final PR for multiplication of pgames (hopefully)!
Next step:  prove `numeric_mul` and define multiplication for `surreal`.

### [2021-05-16 18:58:53](https://github.com/leanprover-community/mathlib/commit/aedd12d)
refactor(measure_theory/haar_measure): move general material to content.lean, make content a structure  ([#7615](https://github.com/leanprover-community/mathlib/pull/7615))
Several facts that are proved only for the Haar measure (including for instance regularity) are true for any measure constructed from a content. We move these facts to the `content.lean` file (and make `content` a structure for easier management). Also, move the notion of regular measure to its own file, and make it a class.

### [2021-05-16 18:58:52](https://github.com/leanprover-community/mathlib/commit/1b098c0)
feat(algebra/ordered_group, algebra/ordered_ring): add some lemmas about abs ([#7612](https://github.com/leanprover-community/mathlib/pull/7612))

### [2021-05-16 18:58:51](https://github.com/leanprover-community/mathlib/commit/b98d840)
feat(category_theory/category): initialize simps ([#7605](https://github.com/leanprover-community/mathlib/pull/7605))
Initialize `@[simps]` so that it works better for `category`. It just makes the names of the generated lemmas shorter.
Add `@[simps]` to product categories.

### [2021-05-16 18:58:50](https://github.com/leanprover-community/mathlib/commit/9084a3c)
chore(order/fixed_point): add docstring for Knaster-Tarski theorem ([#7589](https://github.com/leanprover-community/mathlib/pull/7589))
clarify that the def provided constitutes the Knaster-Tarski theorem

### [2021-05-16 13:18:13](https://github.com/leanprover-community/mathlib/commit/c8a2fd7)
feat(analysis/normed_space): normed_group punit ([#7616](https://github.com/leanprover-community/mathlib/pull/7616))
Minor content from LTE.

### [2021-05-16 13:18:12](https://github.com/leanprover-community/mathlib/commit/2bd4bb6)
fix(tactic/lift): elaborate the type better ([#7598](https://github.com/leanprover-community/mathlib/pull/7598))
* When writing `lift x to t` it will now elaborating `t` using that `t` must be a sort (inserting a coercion if needed).
* Generalize `Type*` to `Sort*` in the tactic

### [2021-05-16 13:18:11](https://github.com/leanprover-community/mathlib/commit/632783d)
feat(algebra/subalgebra): two equal subalgebras are equivalent ([#7590](https://github.com/leanprover-community/mathlib/pull/7590))
This extends `linear_equiv.of_eq` to an `alg_equiv` between two `subalgebra`s.
[Zulip discussion starts around here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/towers.20of.20algebras/near/238452076)

### [2021-05-16 13:18:10](https://github.com/leanprover-community/mathlib/commit/4d909f4)
feat(analysis/calculus/local_extr): A polynomial's roots are bounded by its derivative ([#7571](https://github.com/leanprover-community/mathlib/pull/7571))
An application of Rolle's theorem to polynomials.

### [2021-05-16 13:18:09](https://github.com/leanprover-community/mathlib/commit/ee6a9fa)
fix(tactic/simps): fix bug ([#7433](https://github.com/leanprover-community/mathlib/pull/7433))
* Custom projections that were compositions of multiple projections failed when the projection has additional arguments.
* Also adds an error when two projections are given the same simps-name

### [2021-05-16 13:18:08](https://github.com/leanprover-community/mathlib/commit/f1bcb90)
fix(tactic/simps): remove occurrence of mk_mapp ([#7432](https://github.com/leanprover-community/mathlib/pull/7432))
Fixes the slowdown reported on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simps.20is.20very.20slow
On my laptop, the minimized example in that topic now takes 33ms instead of ~5000ms

### [2021-05-15 21:20:58](https://github.com/leanprover-community/mathlib/commit/65e7646)
feat(algebraic_topology): cosimplicial objects ([#7614](https://github.com/leanprover-community/mathlib/pull/7614))
Dualize the existing API for `simplicial_object` to provide `cosimplicial_object`, and move the contents of LTE's `for_mathlib/simplicial/augmented.lean` to mathlib.

### [2021-05-15 21:20:57](https://github.com/leanprover-community/mathlib/commit/14802d6)
chore(ring_theory/int/basic): remove duplicate lemma nat.prime_iff_prime ([#7611](https://github.com/leanprover-community/mathlib/pull/7611))

### [2021-05-15 21:20:56](https://github.com/leanprover-community/mathlib/commit/07dcff7)
feat(logic/relation): reflexive.ne_iff_imp ([#7579](https://github.com/leanprover-community/mathlib/pull/7579))
As suggested in [#7567](https://github.com/leanprover-community/mathlib/pull/7567)

### [2021-05-15 21:20:55](https://github.com/leanprover-community/mathlib/commit/82ac80f)
feat(data/set/basic): pairwise_on.imp_on ([#7578](https://github.com/leanprover-community/mathlib/pull/7578))
Provide more helper lemmas for transferring `pairwise_on` between different relations. Provide a rephrase of `pairwise_on.mono'` as `pairwise_on.imp`.

### [2021-05-15 21:20:54](https://github.com/leanprover-community/mathlib/commit/4c2567f)
chore(group_theory/group_action/group): add `smul_inv` ([#7568](https://github.com/leanprover-community/mathlib/pull/7568))
This renames the existing `smul_inv` to `smul_inv'`, which is consistent with the name of the other lemma about `mul_semiring_action`, `smul_mul'`.

### [2021-05-15 21:20:53](https://github.com/leanprover-community/mathlib/commit/467d2b2)
feat(data/logic/basic): `em.swap` and `eq_or_ne` ([#7561](https://github.com/leanprover-community/mathlib/pull/7561))

### [2021-05-15 21:20:52](https://github.com/leanprover-community/mathlib/commit/d338ebd)
feat(counterexamples/*): add counterexamples folder ([#7558](https://github.com/leanprover-community/mathlib/pull/7558))
Several times, there has been a discussion on Zulip about the appropriateness of having counterexamples in mathlib.  This PR introduces a `counterexamples` folder, together with the first couple of counterexamples.
For the most recent discussion, see
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.237553

### [2021-05-15 21:20:51](https://github.com/leanprover-community/mathlib/commit/56442cf)
feat(data/nnreal): div and pow lemmas ([#7471](https://github.com/leanprover-community/mathlib/pull/7471))
from the liquid tensor experiment

### [2021-05-15 21:20:50](https://github.com/leanprover-community/mathlib/commit/57b0e68)
chore(*/pi): rename *_hom.apply to pi.eval_*_hom ([#5851](https://github.com/leanprover-community/mathlib/pull/5851))
These definitions state the fact that fixing an `i` and applying a function `(Π i, f i)` maintains the algebraic structure of the function. We already have a name for this operation, `function.eval`.
These isn't a statement about `monoid_hom` or `ring_hom` at all - that just happens to be their type.
For this reason, this commit moves all the definitions of this type into the `pi` namespace:
* `add_monoid_hom.apply` &rarr; `pi.eval_add_monoid_hom`
* `monoid_hom.apply` &rarr; `pi.eval_monoid_hom`
* `ring_hom.apply` &rarr; `pi.eval_ring_hom`
* `pi.alg_hom.apply` [sic] &rarr; `pi.eval_alg_hom`
This scales better, because we might want to say that applying a `linear_map` over a non-commutative ring is an `add_monoid_hom`. Using the naming convention established by this commit, that's easy; it's `linear_map.eval_add_monoid_hom` to mirror `pi.apply_add_monoid_hom`.
This partially addresses [this zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Naming.3A.20eval.20vs.20apply/near/223813950)

### [2021-05-15 16:28:06](https://github.com/leanprover-community/mathlib/commit/172195b)
feat(algebra/{ordered_monoid, ordered_monoid_lemmas}): split the `ordered_[...]` typeclasses ([#7371](https://github.com/leanprover-community/mathlib/pull/7371))
This PR tries to split the ordering assumptions from the algebraic assumptions on the operations in the `ordered_[...]` hierarchy.
The strategy is to introduce two more flexible typeclasses, `covariant_class` and `contravariant_class`.
* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.
Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.
The general approach is to formulate the lemma that you are interested in and prove it, with the `ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass, say `[ordered_cancel_monoid M]`, to three typeclasses, e.g. `[partial_order M] [left_cancel_semigroup M] [covariant_class M M (function.swap (*)) (≤)]` and have a go at seeing if the proof still works!
Note that it is possible (or even expected) to combine several `co(ntra)variant_class` assumptions together.  Indeed, the usual `ordered` typeclasses arise from assuming the pair `[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]` on top of order/algebraic assumptions.
A formal remark is that *normally* `covariant_class` uses the `(≤)`-relation, while `contravariant_class` uses the `(<)`-relation.  This need not be the case in general, but seems to be the most common usage.  In the opposite direction, the implication
`[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)]  => left_cancel_semigroup α`
holds (note the `co*ntra*` assumption and the `(≤)`-relation).
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff

### [2021-05-15 14:21:15](https://github.com/leanprover-community/mathlib/commit/738c19f)
refactor(linear_algebra/matrix): split matrix.lean into multiple files ([#7593](https://github.com/leanprover-community/mathlib/pull/7593))
The file `linear_algebra/matrix.lean` used to be very big and contain a lot of parts that did not depend on each other, so I split each of those parts into its own little file. Most of the new files ended up in `linear_algebra/matrix/`, except for `linear_algebra/trace.lean` and `linear_algebra/determinant.lean` which did not contain anything matrix-specific.
Apart from the local improvement in `matrix.lean` itself, the import graph is now also a bit cleaner.
Renames:
 * `linear_algebra/determinant.lean` -> `linear_algebra/matrix/determinant.lean`
 * `linear_algebra/nonsingular_inverse.lean` -> `linear_algebra/matrix/nonsingular_inverse.lean`
Split off from `linear_algebra/matrix.lean`:
 * `linear_algebra/matrix/basis.lean`
 * `linear_algebra/matrix/block.lean`
 * `linear_algebra/matrix/diagonal.lean`
 * `linear_algebra/matrix/dot_product.lean`
 * `linear_algebra/matrix/dual.lean`
 * `linear_algebra/matrix/finite_dimensional.lean`
 * `linear_algebra/matrix/reindex.lean`
 * `linear_algebra/matrix/to_lin.lean`
 * `linear_algebra/matrix/to_linear_equiv.lean`
 * `linear_algebra/matrix/trace.lean`
 * `linear_algebra/determinant.lean` (Unfortunately, I could not persuade `git` to remember that I moved the original `determinant.lean` to `matrix/determinant.lean`)
  * `linear_algebra/trace.lean`

### [2021-05-15 14:21:14](https://github.com/leanprover-community/mathlib/commit/3c27e2e)
feat(algebra/lie/weights): define product of root vectors and weight vectors ([#7591](https://github.com/leanprover-community/mathlib/pull/7591))
Also some related results, most notably that the zero root space is a subalgebra.

### [2021-05-15 14:21:13](https://github.com/leanprover-community/mathlib/commit/515762a)
feat(category_theory/quotient): congruence relations ([#7501](https://github.com/leanprover-community/mathlib/pull/7501))
Define congruence relations and show that when you quotient a category by a congruence relation, two morphism become equal iff they are related.

### [2021-05-15 08:16:35](https://github.com/leanprover-community/mathlib/commit/fc94b47)
feat(counterexamples): a counterexample on the Pettis integral ([#7553](https://github.com/leanprover-community/mathlib/pull/7553))
Phillips (1940) has exhibited under the continuum hypothesis a bounded weakly measurable function which is not Pettis-integrable. We formalize this counterexample.

### [2021-05-15 08:16:34](https://github.com/leanprover-community/mathlib/commit/b4b38da)
feat(category_theory/*/projective): refactor treatment of projective objects ([#7485](https://github.com/leanprover-community/mathlib/pull/7485))

### [2021-05-15 08:16:32](https://github.com/leanprover-community/mathlib/commit/c63caeb)
feat(algebra/homology): homotopies between chain maps ([#7483](https://github.com/leanprover-community/mathlib/pull/7483))

### [2021-05-15 08:16:31](https://github.com/leanprover-community/mathlib/commit/cc47aff)
feat(algebra/homology): truncation and augmentation of chain complexes ([#7480](https://github.com/leanprover-community/mathlib/pull/7480))

### [2021-05-15 08:16:30](https://github.com/leanprover-community/mathlib/commit/5da114c)
feat(algebraic_topology): the Moore complex of a simplicial object ([#6308](https://github.com/leanprover-community/mathlib/pull/6308))
## Moore complex
We construct the normalized Moore complex, as a functor
`simplicial_object C ⥤ chain_complex C ℕ`,
for any abelian category `C`.
The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.
The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### [2021-05-15 03:59:57](https://github.com/leanprover-community/mathlib/commit/94aae73)
feat(data/nat/factorial) : descending factorial ([#7527](https://github.com/leanprover-community/mathlib/pull/7527))

### [2021-05-15 02:43:25](https://github.com/leanprover-community/mathlib/commit/a648af4)
chore(scripts): update nolints.txt ([#7613](https://github.com/leanprover-community/mathlib/pull/7613))
I am happy to remove some nolints for you!

### [2021-05-14 22:42:57](https://github.com/leanprover-community/mathlib/commit/bd923f7)
chore(geometry/euclidean/triangle): minor style fixes ([#7585](https://github.com/leanprover-community/mathlib/pull/7585))

### [2021-05-14 19:19:41](https://github.com/leanprover-community/mathlib/commit/fd3d117)
feat(data/mv_polynomial/basic): Add ring section ([#7507](https://github.com/leanprover-community/mathlib/pull/7507))
A few lemmas about `monomial` analogous to those for the single-variate polynomials over rings.

### [2021-05-14 17:28:32](https://github.com/leanprover-community/mathlib/commit/a52f471)
feat(algebra/homology): chain complexes are an additive category ([#7478](https://github.com/leanprover-community/mathlib/pull/7478))

### [2021-05-14 14:25:23](https://github.com/leanprover-community/mathlib/commit/f8dc722)
refactor(topology/algebra/ordered): reduce imports ([#7601](https://github.com/leanprover-community/mathlib/pull/7601))
Renames `topology.algebra.ordered` to `topology.algebra.order`, and moves the material about `liminf/limsup` and about `extend_from` to separate files, in order to delay imports.

### [2021-05-14 14:25:22](https://github.com/leanprover-community/mathlib/commit/2373ee6)
refactor(set_theory/{surreal, game}): move `mul` from surreal to game ([#7580](https://github.com/leanprover-community/mathlib/pull/7580))
The next step is to provide several `simp` lemmas for multiplication of pgames in terms of games.
None of these statements involve surreal numbers.

### [2021-05-14 12:02:31](https://github.com/leanprover-community/mathlib/commit/87adde4)
feat(category_theory/monoidal): the monoidal opposite ([#7602](https://github.com/leanprover-community/mathlib/pull/7602))

### [2021-05-14 12:02:30](https://github.com/leanprover-community/mathlib/commit/cc1690e)
feat(analysis/calculus/parametric_integral): derivative of parametric integrals ([#7437](https://github.com/leanprover-community/mathlib/pull/7437))
from the sphere eversion project

### [2021-05-14 09:48:30](https://github.com/leanprover-community/mathlib/commit/1199a3d)
feat(analysis/special_functions/exp_log): strengthen statement of `continuous_log'` ([#7607](https://github.com/leanprover-community/mathlib/pull/7607))
The proof of `continuous (λ x : {x : ℝ // 0 < x}, log x)` also works for `continuous (λ x : {x : ℝ // x ≠ 0}, log x)`.
I keep the preexisting lemma as well since it is used in a number of places and seems generally useful.

### [2021-05-14 09:48:29](https://github.com/leanprover-community/mathlib/commit/3c77167)
feat(linear_algebra/dual): generalize from field to ring ([#7599](https://github.com/leanprover-community/mathlib/pull/7599))

### [2021-05-14 04:49:59](https://github.com/leanprover-community/mathlib/commit/840db09)
chore(category_theory/groupoid): remove unnecessary imports ([#7600](https://github.com/leanprover-community/mathlib/pull/7600))

### [2021-05-14 04:49:58](https://github.com/leanprover-community/mathlib/commit/3124e1d)
feat(data/finset/lattice): choice-free le_sup_iff and lt_sup_iff ([#7584](https://github.com/leanprover-community/mathlib/pull/7584))
Propagate to `finset` the change to `le_sup_iff [is_total α (≤)]` and `lt_sup_iff [is_total α (≤)]` made in [#7455](https://github.com/leanprover-community/mathlib/pull/7455).

### [2021-05-14 04:49:57](https://github.com/leanprover-community/mathlib/commit/bf2750e)
chore(order/atoms): ask for the correct instances ([#7582](https://github.com/leanprover-community/mathlib/pull/7582))
replace bounded_lattice by order_bot/order_top where it can

### [2021-05-14 04:49:56](https://github.com/leanprover-community/mathlib/commit/8829c0d)
feat(algebra/homology): flipping double complexes ([#7482](https://github.com/leanprover-community/mathlib/pull/7482))

### [2021-05-14 04:49:55](https://github.com/leanprover-community/mathlib/commit/722b5fc)
feat(algebra/homology): homological complexes are the same as differential objects ([#7481](https://github.com/leanprover-community/mathlib/pull/7481))

### [2021-05-14 04:49:54](https://github.com/leanprover-community/mathlib/commit/f5327c9)
feat(algebra/homology): definition of quasi_iso ([#7479](https://github.com/leanprover-community/mathlib/pull/7479))

### [2021-05-14 01:13:30](https://github.com/leanprover-community/mathlib/commit/239908e)
feat(ring_theory/ideal/operations): add apply_coe_mem_map ([#7566](https://github.com/leanprover-community/mathlib/pull/7566))
This is a continuation of [#7459](https://github.com/leanprover-community/mathlib/pull/7459). In this PR:
- We modify `ideal.mem_map_of_mem` in order to be consistent with `submonoid.mem_map_of_mem`.
- We modify `submonoid.apply_coe_mem_map` (and friends) to have the submonoid as an explicit variable. This was the case before [#7459](https://github.com/leanprover-community/mathlib/pull/7459) (but with a different, and not consistent, name). It seems to me that this version makes the code more readable.
- We add `ideal.apply_coe_mem_map` (similar to `submonoid.apply_coe_mem_map`).
Note that `mem_map_of_mem` is used in other places, for example we have `multiset.mem_map_of_mem`, but since a multiset is not a type there is no `apply_coe_mem_map` to add there.

### [2021-05-13 15:18:24](https://github.com/leanprover-community/mathlib/commit/090c9ac)
chore(scripts): update nolints.txt ([#7597](https://github.com/leanprover-community/mathlib/pull/7597))
I am happy to remove some nolints for you!

### [2021-05-13 15:18:24](https://github.com/leanprover-community/mathlib/commit/f792356)
chore(order/galois_connection): ask for the correct instances ([#7594](https://github.com/leanprover-community/mathlib/pull/7594))
replace partial_order by preorder where it can and general tidy up of this old style file

### [2021-05-13 15:18:23](https://github.com/leanprover-community/mathlib/commit/ce45594)
feat(algebra/homology/single): chain complexes supported in a single degree ([#7477](https://github.com/leanprover-community/mathlib/pull/7477))

### [2021-05-13 13:44:39](https://github.com/leanprover-community/mathlib/commit/c5faead)
feat(category_theory/preadditive/functor_category): preadditive instance for C \func D ([#7533](https://github.com/leanprover-community/mathlib/pull/7533))

### [2021-05-12 16:37:46](https://github.com/leanprover-community/mathlib/commit/43bd924)
feat(topology/category/Profinite): iso_equiv_homeo ([#7529](https://github.com/leanprover-community/mathlib/pull/7529))
From LTE

### [2021-05-12 15:10:58](https://github.com/leanprover-community/mathlib/commit/08f4404)
refactor(ring_theory/perfection): remove coercion in the definition of the type ([#7583](https://github.com/leanprover-community/mathlib/pull/7583))
Defining the type `ring.perfection R p` as a plain subtype (but inheriting the semiring or ring instances from a `subsemiring` structure) removes several coercions and helps Lean a lot when elaborating or unifying.

### [2021-05-12 10:02:56](https://github.com/leanprover-community/mathlib/commit/6b62b9f)
refactor(algebra/module): rename `smul_injective hx` to `smul_left_injective M hx` ([#7577](https://github.com/leanprover-community/mathlib/pull/7577))
This is a follow-up PR to [#7548](https://github.com/leanprover-community/mathlib/pull/7548).
 * Now that there is also a `smul_right_injective`, we should disambiguate the previous `smul_injective` to `smul_left_injective`.
 * The `M` parameter can't be inferred from arguments before the colon, so we make it explicit in `smul_left_injective` and `smul_right_injective`.

### [2021-05-12 02:19:18](https://github.com/leanprover-community/mathlib/commit/6ee8f0e)
doc(tactic/interactive): link swap and rotate to each other ([#7550](https://github.com/leanprover-community/mathlib/pull/7550))
They both do 'make a different goal the current one'.

### [2021-05-11 22:59:11](https://github.com/leanprover-community/mathlib/commit/a7e1696)
fix(tactic/derive_fintype): use correct universes ([#7581](https://github.com/leanprover-community/mathlib/pull/7581))
Reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type.20class.20error.20with.20mk_fintype_instance/near/238209823).

### [2021-05-11 22:59:10](https://github.com/leanprover-community/mathlib/commit/0538d2c)
chore(*): reducing imports ([#7573](https://github.com/leanprover-community/mathlib/pull/7573))

### [2021-05-11 18:00:40](https://github.com/leanprover-community/mathlib/commit/9cf732c)
chore(logic/nontrivial): adjust priority of `nonempty` instances ([#7563](https://github.com/leanprover-community/mathlib/pull/7563))
This makes `nontrivial.to_nonempty` and `nonempty_of_inhabited` higher priority so they are tried before things like `add_torsor.nonempty` which starts traversing the algebra heirarchy.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/char_zero/near/238103102)

### [2021-05-11 18:00:39](https://github.com/leanprover-community/mathlib/commit/3048d6b)
feat(ring_theory/localization): Define local ring hom on localization at prime ideal ([#7522](https://github.com/leanprover-community/mathlib/pull/7522))
Defines the induced ring homomorphism on the localizations at a prime ideal and proves that it is local and uniquely determined.

### [2021-05-11 14:57:06](https://github.com/leanprover-community/mathlib/commit/b746e82)
feat(linear_algebra/finsupp): adjust apply lemma for `finsupp.dom_lcongr` ([#7549](https://github.com/leanprover-community/mathlib/pull/7549))
This is a split-off dependency from [#7496](https://github.com/leanprover-community/mathlib/pull/7496).

### [2021-05-11 10:56:56](https://github.com/leanprover-community/mathlib/commit/9191a67)
perf(ci): skip linting and tests on master branch ([#7576](https://github.com/leanprover-community/mathlib/pull/7576))
Do not run lints and tests on the master branch.  These checks have already passed on the staging branch, so there should be no need to repeat them on master.

### [2021-05-11 07:41:53](https://github.com/leanprover-community/mathlib/commit/b4c7654)
feat(algebra/homology): redesign of homological complexes ([#7473](https://github.com/leanprover-community/mathlib/pull/7473))
This is a complete redesign of our library on homological complexes and homology.
This PR replaces the current definition of `chain_complex` which had proved cumbersome to work with.
The fundamental change is that chain complexes are now indexed by a type equipped with a `complex_shape`, rather than by a monoid. A `complex_shape ι` contains a relation `r`, with the intent that we will only allow a differential `X i ⟶ X j` when `r i j`. This allows, for example, complexes indexed either by `nat` or `int`, with differentials going either up or down.
We set up the initial theory without referring to "successors" and "predecessors" in the type `ι`, to ensure we can avoid dependent type theory hell issues involving arithmetic in the index of a chain group. We achieve this by having a chain complex consist of morphisms `d i j : X i ⟶ X j` for all `i j`, but with an additional axiom saying this map is zero unless `r i j`. This means we can easily talk about, e.g., morphisms from `X (i - 1 + 1)` to `X (i + 1)` when we need to.
However after not too long we also set up `option` valued `next` and `prev` functions which make an arbitrary choice of such successors and predecessors if they exist. Using these, we define morphisms `d_to j`, which lands in `X j`, and has source either `X i` for some `r i j`, or the zero object if these isn't such an `i`. These morphisms are very convenient when working "at the edge of a complex", e.g. when indexing by `nat`.

### [2021-05-11 07:41:52](https://github.com/leanprover-community/mathlib/commit/12c9ddf)
feat(set_theory/{pgame, surreal}): add `left_distrib_equiv` and `right_distrib_equiv` for pgames ([#7440](https://github.com/leanprover-community/mathlib/pull/7440))
and several other auxiliary lemmas.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers)

### [2021-05-11 05:55:39](https://github.com/leanprover-community/mathlib/commit/ca4024b)
feat(algebraic_topology/cech_nerve): Adds a definition of the Cech nerve associated to an arrow. ([#7547](https://github.com/leanprover-community/mathlib/pull/7547))
Also adds a definition of augmented simplicial objects as a comma category.

### [2021-05-11 04:39:37](https://github.com/leanprover-community/mathlib/commit/8dc848c)
feat(ring_theory/finiteness): add finite_type_iff_group_fg ([#7569](https://github.com/leanprover-community/mathlib/pull/7569))
We add here a simple modification of `monoid_algebra.fg_of_finite_type`: a group algebra is of finite type if and only if the group is finitely generated (as group opposed to as monoid).

### [2021-05-11 01:49:43](https://github.com/leanprover-community/mathlib/commit/fab4197)
chore(scripts): update nolints.txt ([#7570](https://github.com/leanprover-community/mathlib/pull/7570))
I am happy to remove some nolints for you!

### [2021-05-10 22:45:44](https://github.com/leanprover-community/mathlib/commit/3fd7cc3)
feat(ring_theory/hahn_series): extend the domain of a Hahn series by an `order_embedding` ([#7551](https://github.com/leanprover-community/mathlib/pull/7551))
Defines `hahn_series.emb_domain`, which extends the domain of a Hahn series by embedding it into a larger domain in an order-preserving way.
Bundles `hahn_series.emb_domain` with additional properties as `emb_domain_linear_map`, `emb_domain_ring_hom`, and `emb_domain_alg_hom` under additional conditions.
Defines the ring homomorphism `hahn_series.of_power_series` and the algebra homomorphism `hahn_series.of_power_series_alg`, which map power series to Hahn series over an ordered semiring using `hahn_series.emb_domain` with `nat.cast` as the embedding.

### [2021-05-10 22:45:43](https://github.com/leanprover-community/mathlib/commit/81c98d5)
feat(ring_theory/hahn_series): Hahn series form a field ([#7495](https://github.com/leanprover-community/mathlib/pull/7495))
Uses Higman's Lemma to define `summable_family.powers`, a summable family consisting of the powers of a Hahn series of positive valuation
Uses `summable_family.powers` to define inversion on Hahn series over a field and linear-ordered value group, making the type of Hahn series a field.
Shows that a Hahn series over an integral domain and linear-ordered value group  `is_unit` if and only if its lowest coefficient is.

### [2021-05-10 22:45:42](https://github.com/leanprover-community/mathlib/commit/1cbb31d)
feat(analysis/normed_space/normed_group_hom): add lemmas ([#7474](https://github.com/leanprover-community/mathlib/pull/7474))
From LTE.
Written by @PatrickMassot 
- [x] depends on: [#7459](https://github.com/leanprover-community/mathlib/pull/7459)

### [2021-05-10 16:44:24](https://github.com/leanprover-community/mathlib/commit/b7ab74a)
feat(algebra/lie/weights): add lemma `root_space_comap_eq_weight_space` ([#7565](https://github.com/leanprover-community/mathlib/pull/7565))

### [2021-05-10 16:44:23](https://github.com/leanprover-community/mathlib/commit/ac1f3df)
chore(*): remove unnecessary `import tactic` ([#7560](https://github.com/leanprover-community/mathlib/pull/7560))

### [2021-05-10 16:44:22](https://github.com/leanprover-community/mathlib/commit/17cba54)
feat(data/int/basic): sign raised to an odd power ([#7559](https://github.com/leanprover-community/mathlib/pull/7559))
Since sign is either -1, 0, or 1, it is unchanged when raised to an odd power.

### [2021-05-10 16:44:21](https://github.com/leanprover-community/mathlib/commit/3417ee0)
chore(deprecated/group): relax monoid to mul_one_class ([#7556](https://github.com/leanprover-community/mathlib/pull/7556))
This fixes an annoyance where `monoid_hom.is_monoid_hom` didn't work on non-associative monoids.

### [2021-05-10 16:44:20](https://github.com/leanprover-community/mathlib/commit/477af65)
feat(category_theory/limits/shapes/wide_pullbacks): Adds some wrappers around the (co)limit api for wide pullbacks/pushouts ([#7546](https://github.com/leanprover-community/mathlib/pull/7546))
This PR adds some wrappers (mostly abbreviations) around the (co)limit api specifically for wide pullbacks and wide pushouts.

### [2021-05-10 16:44:19](https://github.com/leanprover-community/mathlib/commit/92395fd)
feat(data/list/rotate): is_rotated ([#7299](https://github.com/leanprover-community/mathlib/pull/7299))
`is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`.

### [2021-05-10 13:15:31](https://github.com/leanprover-community/mathlib/commit/41c7b1e)
chore(category_theory/Fintype): remove redundant lemmas ([#7531](https://github.com/leanprover-community/mathlib/pull/7531))
These lemmas exist for arbitrary concrete categories.
- [x] depends on: [#7530](https://github.com/leanprover-community/mathlib/pull/7530)

### [2021-05-10 13:15:30](https://github.com/leanprover-community/mathlib/commit/b9f4420)
feat(geometry/euclidean/triangle): add Stewart's Theorem + one similarity lemma ([#7327](https://github.com/leanprover-community/mathlib/pull/7327))

### [2021-05-10 13:15:28](https://github.com/leanprover-community/mathlib/commit/03b88c1)
feat(algebra/category/Module): Free R C, the free R-linear completion of a category ([#7177](https://github.com/leanprover-community/mathlib/pull/7177))
The free R-linear completion of a category.

### [2021-05-10 07:36:17](https://github.com/leanprover-community/mathlib/commit/48104c3)
feat(data/set/lattice): (b)Union and (b)Inter lemmas ([#7557](https://github.com/leanprover-community/mathlib/pull/7557))
from LTE

### [2021-05-10 07:36:16](https://github.com/leanprover-community/mathlib/commit/b577697)
feat(data/matrix/basic): add missing smul instances, generalize lemmas to work on scalar towers ([#7544](https://github.com/leanprover-community/mathlib/pull/7544))
This also fixes the `add_monoid_hom.map_zero` etc lemmas to not require overly strong typeclasses on `α`
This removes the `matrix.smul_apply` lemma since `pi.smul_apply` and `smul_eq_mul` together replace it.

### [2021-05-10 07:36:15](https://github.com/leanprover-community/mathlib/commit/38bf2ab)
feat(field_theory/abel_ruffini): Version of solvable_by_rad.is_solvable ([#7509](https://github.com/leanprover-community/mathlib/pull/7509))
This is a version of `solvable_by_rad.is_solvable`, which will be the final step of the abel-ruffini theorem.

### [2021-05-10 07:36:14](https://github.com/leanprover-community/mathlib/commit/ef90a7a)
refactor(*): bundle `is_basis` ([#7496](https://github.com/leanprover-community/mathlib/pull/7496))
This PR replaces the definition of a basis used in mathlib and fixes the usages throughout.
Rationale: Previously, `is_basis` was a predicate on a family of vectors, saying this family is linear independent and spans the whole space. We encountered many small annoyances when working with these unbundled definitions, for example complicated `is_basis` arguments being hidden in the goal view or slow elaboration when mapping a basis to a slightly different set of basis vectors. The idea to turn `basis` into a bundled structure originated in the discussion on [#4949](https://github.com/leanprover-community/mathlib/pull/4949). @digama0 suggested on Zulip to identify these "bundled bases" with their map `repr : M ≃ₗ[R] (ι →₀ R)` that sends a vector to its coordinates. (In fact, that specific map used to be only a `linear_map` rather than an equiv.)
Overview of the changes:
 - The `is_basis` predicate has been replaced with the `basis` structure. 
 - Parameters of the form `{b : ι → M} (hb : is_basis R b)` become a single parameter `(b : basis ι R M)`.
 - Constructing a basis from a linear independent family spanning the whole space is now spelled `basis.mk hli hspan`, instead of `and.intro hli hspan`.
 -  You can also use `basis.of_repr` to construct a basis from an equivalence `e : M ≃ₗ[R] (ι →₀ R)`. If `ι` is a `fintype`, you can use `basis.of_equiv_fun (e : M ≃ₗ[R] (ι → R))` instead, saving you from having to work with `finsupp`s.
 - Most declaration names that used to contain `is_basis` are now spelled with `basis`, e.g. `pi.is_basis_fun` is now `pi.basis_fun`.
 - Theorems of the form `exists_is_basis K V : ∃ (s : set V) (b : s -> V), is_basis K b` and `finite_dimensional.exists_is_basis_finset K V : [finite_dimensional K V] -> ∃ (s : finset V) (b : s -> V), is_basis K b` have been replaced with (noncomputable) defs such as `basis.of_vector_space K V : basis (basis.of_vector_space_index K V) K V` and `finite_dimensional.finset_basis : basis (finite_dimensional.finset_basis_index K V) K V`; the indexing sets being a separate definition means we can declare a `fintype (basis.of_vector_space_index K V)` instance on finite dimensional spaces, rather than having to use `cases exists_is_basis_fintype K V with ...` each time.
 - Definitions of a `basis` are now, wherever practical, accompanied by `simp` lemmas giving the values of `coe_fn` and `repr` for that basis.
 - Some auxiliary results like `pi.is_basis_fun₀` have been removed since they are no longer needed.
Basic API overview:
* `basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`, represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b` are given by `b i` for `i : ι`
* `basis.repr` is the isomorphism sending `x : M` to its coordinates `basis.repr b x : ι →₀ R`. The inverse of `b.repr` is `finsupp.total _ _ _ b`. The converse, turning this isomorphism into a basis, is called `basis.of_repr`.
* If `ι` is finite, there is a variant of `repr` called `basis.equiv_fun b : M ≃ₗ[R] ι → R`. The converse, turning this isomorphism into a basis, is called `basis.of_equiv_fun`.
* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis (the converse consists of `basis.linear_independent` and `basis.span_eq`
* `basis.ext` states that two linear maps are equal if they coincide on a basis; similar results are available for linear equivs (if they coincide on the basis vectors), elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.
* `basis.of_vector_space` states that every vector space has a basis.
* `basis.reindex` uses an equiv to map a basis to a different indexing set, `basis.map` uses a linear equiv to map a basis to a different module
Zulip discussions:
 * https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Bundled.20basis
 * https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234949

### [2021-05-10 07:36:13](https://github.com/leanprover-community/mathlib/commit/f985e36)
feat(group_theory/subgroup): add mem_map_of_mem ([#7459](https://github.com/leanprover-community/mathlib/pull/7459))
From LTE.
Written by @PatrickMassot

### [2021-05-10 07:36:12](https://github.com/leanprover-community/mathlib/commit/4a8467a)
feat(data/equiv/basic): equiv.curry ([#7458](https://github.com/leanprover-community/mathlib/pull/7458))
This renames `equiv.arrow_arrow_equiv_prod_arrow` to `(equiv.curry _ _ _).symm` to make it easier to find and match `function.curry`.
* `cardinal.power_mul` is swapped, so that its name makes sense.
* renames `linear_equiv.uncurry` to `linear_equiv.curry` and swaps sides
Also add `@[simps]` to two equivs.

### [2021-05-10 06:01:59](https://github.com/leanprover-community/mathlib/commit/7150c90)
refactor(ring_theory/localization): Golf two proofs ([#7520](https://github.com/leanprover-community/mathlib/pull/7520))
Golfing two proofs and changing their order.

### [2021-05-09 22:18:48](https://github.com/leanprover-community/mathlib/commit/ea0043c)
feat(topology): tiny new lemmas ([#7554](https://github.com/leanprover-community/mathlib/pull/7554))
from LTE

### [2021-05-09 12:20:12](https://github.com/leanprover-community/mathlib/commit/735a26e)
chore(group_theory): some new convenience lemmas ([#7555](https://github.com/leanprover-community/mathlib/pull/7555))
from LTE

### [2021-05-09 12:20:10](https://github.com/leanprover-community/mathlib/commit/581064f)
feat(uniform_space/cauchy): cauchy_seq lemmas ([#7528](https://github.com/leanprover-community/mathlib/pull/7528))
from the Liquid Tensor Experiment

### [2021-05-09 10:00:57](https://github.com/leanprover-community/mathlib/commit/bf229dd)
feat(topology/metric_space/basic): dist_ne_zero ([#7552](https://github.com/leanprover-community/mathlib/pull/7552))

### [2021-05-08 13:26:29](https://github.com/leanprover-community/mathlib/commit/132328c)
feat(algebra/lie/weights): define weight spaces of Lie modules ([#7537](https://github.com/leanprover-community/mathlib/pull/7537))

### [2021-05-08 08:13:59](https://github.com/leanprover-community/mathlib/commit/4a8a595)
feat(topology/subset_properties, homeomorph): lemmata about embeddings ([#7431](https://github.com/leanprover-community/mathlib/pull/7431))
Two lemmata: (i) embedding to homeomorphism (ii) a closed embedding is proper
Coauthored with @hrmacbeth

### [2021-05-08 05:52:42](https://github.com/leanprover-community/mathlib/commit/583ad82)
feat(algebraic_geometry/structure_sheaf): Structure sheaf on basic opens ([#7405](https://github.com/leanprover-community/mathlib/pull/7405))
Proves that `to_basic_open` is an isomorphism of commutative rings. Also adds Hartshorne as a reference.

### [2021-05-07 22:54:26](https://github.com/leanprover-community/mathlib/commit/dbcd454)
feat(topology/category/*): Add alternative explicit limit cones for `Top`, etc. and shows `X : Profinite` is a limit of finite sets. ([#7448](https://github.com/leanprover-community/mathlib/pull/7448))
This PR redefines `Top.limit_cone`, and defines similar explicit limit cones for `CompHaus` and `Profinite`.
Using the definition with the subspace topology makes the proofs that the limit is compact, t2 and/or totally disconnected much easier.
This also expresses any `X : Profinite` as a limit of its discrete quotients, which are all finite.

### [2021-05-07 22:54:25](https://github.com/leanprover-community/mathlib/commit/515fb2f)
feat(group_theory/perm/*): lemmas about `extend_domain`, `fin_rotate`, and `fin.cycle_type` ([#7447](https://github.com/leanprover-community/mathlib/pull/7447))
Shows how `disjoint`, `support`, `is_cycle`, and `cycle_type` behave under `extend_domain`
Calculates `support` and `cycle_type` for `fin_rotate` and `fin.cycle_type`
Shows that the normal closure of `fin_rotate 5` in `alternating_group (fin 5)` is the whole alternating group.

### [2021-05-07 20:26:33](https://github.com/leanprover-community/mathlib/commit/5cfcb6a)
feat(ring_theory/hahn_series): order of a nonzero Hahn series, reindexing summable families ([#7444](https://github.com/leanprover-community/mathlib/pull/7444))
Defines `hahn_series.order`, the order of a nonzero Hahn series
Restates `add_val` in terms of `hahn_series.order`
Defines `hahn_series.summable_family.emb_domain`, reindexing a summable family using an embedding

### [2021-05-07 09:30:47](https://github.com/leanprover-community/mathlib/commit/72e151d)
feat(topology/uniform_space): is_closed_of_spread_out ([#7538](https://github.com/leanprover-community/mathlib/pull/7538))
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/integers.20are.20closed.20in.20reals)

### [2021-05-07 09:30:46](https://github.com/leanprover-community/mathlib/commit/301542a)
feat(group_theory.quotient_group): add eq_iff_div_mem ([#7523](https://github.com/leanprover-community/mathlib/pull/7523))
From LTE.
Written by @PatrickMassot

### [2021-05-07 09:30:45](https://github.com/leanprover-community/mathlib/commit/63a1782)
feat(field_theory/polynomial_galois_group): More flexible version of gal_action_hom_bijective_of_prime_degree ([#7508](https://github.com/leanprover-community/mathlib/pull/7508))
Since the number of non-real roots is even, we can make a more flexible version of `gal_action_hom_bijective_of_prime_degree`. This flexibility will be helpful when working with a specific polynomial.

### [2021-05-07 09:30:44](https://github.com/leanprover-community/mathlib/commit/565310f)
feat(data/nat/cast): pi.coe_nat and pi.nat_apply ([#7492](https://github.com/leanprover-community/mathlib/pull/7492))

### [2021-05-07 09:30:43](https://github.com/leanprover-community/mathlib/commit/190d4e2)
feat(algebra/module/basic): smul_add_hom_one ([#7461](https://github.com/leanprover-community/mathlib/pull/7461))

### [2021-05-07 09:30:42](https://github.com/leanprover-community/mathlib/commit/91d5aa6)
feat(category_theory/arrow): arrow.mk_inj ([#7456](https://github.com/leanprover-community/mathlib/pull/7456))
From LTE

### [2021-05-07 09:30:40](https://github.com/leanprover-community/mathlib/commit/6fc8b2a)
refactor(*): more choice-free proofs ([#7455](https://github.com/leanprover-community/mathlib/pull/7455))
Now that lean v3.30 has landed (and specifically leanprover-community/lean[#560](https://github.com/leanprover-community/mathlib/pull/560)), we can finally make some progress on making a significant fraction of mathlib foundations choice-free. This PR does the following:
* No existing theorem statements have changed (except `linear_nonneg_ring` as noted below).
* A number of new theorems have been added to the `decidable` namespace, proving choice-free versions of lemmas under the assumption that something is decidable. These are primarily concentrated in partial orders and ordered rings, because total orders are already decidable, but there are some interesting lemmas about partial orders that require decidability of `le`.
* `linear_nonneg_ring` was changed to include decidability of `nonneg`, for consistency with linear ordered rings. No one is using this anyway so there shouldn't be any fallout.
* A lot of the `ordered_semiring` lemmas need `decidable` versions now because one of the core axioms, `mul_le_mul_of_nonneg_left`, is derived by LEM from an equivalent statement about lt instead of being an actual axiom. If this is refactored, these theorems can be removed again.
* The main files which were scoured of choicy proofs are: `algebra.ordered_group`,  `algebra.ordered_ring`, `data.nat.basic`, `data.int.basic`, `data.list.basic`, and `computability.halting`.
* The end goal of this was to prove `computable_pred.halting_problem` without assuming choice, finally validating a claim I made more than two years ago in my [paper](https://arxiv.org/abs/1810.08380) on the formalization.
I have not yet investigated a linter for making sure that these proofs stay choice-free; this can be done in a follow-up PR.

### [2021-05-07 09:30:39](https://github.com/leanprover-community/mathlib/commit/dec29aa)
feat(group_theory/solvable): S_5 is not solvable ([#7453](https://github.com/leanprover-community/mathlib/pull/7453))
This is a rather hacky proof that S_5 is not solvable. The proper proof via the simplicity of A_5 will eventually replace this. But until then, this result is needed for abel-ruffini.
Most of the work done by Jordan Brown

### [2021-05-07 09:30:38](https://github.com/leanprover-community/mathlib/commit/95b91b3)
refactor(group_theory/perm/*): disjoint and support in own file ([#7450](https://github.com/leanprover-community/mathlib/pull/7450))
The group_theory/perm/sign file was getting large and too broad in scope. This refactor pulls out `perm.support`, `perm.is_swap`, and `perm.disjoint` into a separate file.
A simpler version of [#7118](https://github.com/leanprover-community/mathlib/pull/7118).

### [2021-05-07 09:30:37](https://github.com/leanprover-community/mathlib/commit/251a42b)
feat(ring_theory/finiteness): add monoid_algebra.ft_iff_fg ([#7445](https://github.com/leanprover-community/mathlib/pull/7445))
We prove here `add monoid_algebra.ft_iff_fg`: the monoid algebra is of finite type if and only if the monoid is finitely generated.
- [x] depends on: [#7409](https://github.com/leanprover-community/mathlib/pull/7409)

### [2021-05-07 09:30:36](https://github.com/leanprover-community/mathlib/commit/be1af7c)
feat(linear_algebra/quadratic_form): provide `distrib_mul_action S (quadratic_form M R)` when `S` has no addition. ([#7443](https://github.com/leanprover-community/mathlib/pull/7443))
The end goal here is to provide `has_scalar (units R) (quadratic_form M R)` for possible use in [#7427](https://github.com/leanprover-community/mathlib/pull/7427)

### [2021-05-07 09:30:35](https://github.com/leanprover-community/mathlib/commit/5d873a6)
feat(algebra/monoid_algebra): add add_monoid_algebra_ring_equiv_direct_sum ([#7422](https://github.com/leanprover-community/mathlib/pull/7422))
The only interesting result here is:
    add_monoid_algebra_ring_equiv_direct_sum : add_monoid_algebra M ι ≃+* ⨁ i : ι, M
The rest of the new file is just boilerplate to translate `dfinsupp.single` into `direct_sum.of`.

### [2021-05-07 09:30:34](https://github.com/leanprover-community/mathlib/commit/3a5c871)
refactor(polynomial/*): make polynomials irreducible ([#7421](https://github.com/leanprover-community/mathlib/pull/7421))
Polynomials are the most basic objects in field theory. Making them irreducible helps Lean, because it can not try to unfold things too far, and it helps the user because it forces him to use a sane API instead of mixing randomly stuff from finsupp and from polynomials, as used to be the case in mathlib before this PR.

### [2021-05-07 09:30:33](https://github.com/leanprover-community/mathlib/commit/322ccc5)
feat(finset/basic): downward induction for finsets ([#7379](https://github.com/leanprover-community/mathlib/pull/7379))

### [2021-05-07 09:30:31](https://github.com/leanprover-community/mathlib/commit/11a06de)
feat(order/closure): closure of unions and bUnions ([#7361](https://github.com/leanprover-community/mathlib/pull/7361))
prove closure_closure_union and similar

### [2021-05-07 09:30:30](https://github.com/leanprover-community/mathlib/commit/b20e664)
feat(order/well_founded_set): Higman's Lemma ([#7212](https://github.com/leanprover-community/mathlib/pull/7212))
Proves Higman's Lemma: if `r` is partially well-ordered on `s`, then `list.sublist_forall2` is partially well-ordered on the set of lists whose elements are in `s`.

### [2021-05-07 05:00:03](https://github.com/leanprover-community/mathlib/commit/cd5864f)
chore(scripts): update nolints.txt ([#7541](https://github.com/leanprover-community/mathlib/pull/7541))
I am happy to remove some nolints for you!

### [2021-05-07 05:00:02](https://github.com/leanprover-community/mathlib/commit/6a7ddcc)
ci(.github/workflows/{build,dependent-issues}.yml): auto-cancel workflows on previous commits ([#7536](https://github.com/leanprover-community/mathlib/pull/7536))
After this is merged, pushing a new commit to a branch in this repo should cancel the "continuous integration" and "dependent issues" workflows running on any older commits on that branch.

### [2021-05-07 05:00:01](https://github.com/leanprover-community/mathlib/commit/93f9b3d)
ci(.github/workflows/build.yml): switch to trepplein ([#7532](https://github.com/leanprover-community/mathlib/pull/7532))
Reduces the leanchecker time from 6+57 minutes to 6+16 minutes.

### [2021-05-07 04:59:59](https://github.com/leanprover-community/mathlib/commit/f44a5eb)
feat(category_theory/concrete_category): id_apply, comp_apply ([#7530](https://github.com/leanprover-community/mathlib/pull/7530))
This PR renames
* `category_theory.coe_id` to `category_theory.id_apply`
* `category_theory.coe_comp` to `category_theory.comp_apply`
The names that are hence free up
are then redefined for "unapplied" versions of the same lemmas.
The `elementwise` tactic uses the old lemmas (with their new names).
We need minor fixes in the rest of the library because of the name changes.

### [2021-05-07 04:59:59](https://github.com/leanprover-community/mathlib/commit/0ead8ee)
feat(ring_theory/localization): Characterize units in localization at prime ideal ([#7519](https://github.com/leanprover-community/mathlib/pull/7519))
Adds a few lemmas characterizing units and nonunits (elements of the maximal ideal) in the localization at a prime ideal.

### [2021-05-07 04:59:57](https://github.com/leanprover-community/mathlib/commit/755cb75)
feat(data/list/basic): non-meta to_chunks ([#7517](https://github.com/leanprover-community/mathlib/pull/7517))
A non-meta definition of the `list.to_chunks` method, plus some basic theorems about it.

### [2021-05-07 04:59:56](https://github.com/leanprover-community/mathlib/commit/930485c)
feat(linear_algebra/tensor_product): distrib_mul_actions are inherited ([#7516](https://github.com/leanprover-community/mathlib/pull/7516))
It turns out that `tensor_product.has_scalar` requires only `distrib_mul_action` and not `semimodule` on its components.
As a result, a tensor product can inherit the `distrib_mul_action` structure of its components too.
Notably, this would enable `has_scalar (units R) (M ⊗[R] N)` in future.

### [2021-05-07 04:59:55](https://github.com/leanprover-community/mathlib/commit/b903ea2)
chore(algebra/module/linear_map): add missing rfl lemmas ([#7515](https://github.com/leanprover-community/mathlib/pull/7515))
I've found these most useful for writing along in reverse so that I can use `linear_map.map_smul_of_tower`.

### [2021-05-07 04:59:54](https://github.com/leanprover-community/mathlib/commit/6d25f3a)
feat(category_theory/opposites): Adds equivalences for functor categories. ([#7505](https://github.com/leanprover-community/mathlib/pull/7505))
This PR adds the following equivalences for categories `C` and `D`:
1. `(C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ` induced by `op` and `unop`.
2.  `(Cᵒᵖ ⥤ D)ᵒᵖ ≌ (C ⥤ Dᵒᵖ)` induced by `left_op` and `right_op`.

### [2021-05-07 04:59:53](https://github.com/leanprover-community/mathlib/commit/efb283c)
feat(data/dfinsupp): add `finset_sum_apply` and `coe_finset_sum` ([#7499](https://github.com/leanprover-community/mathlib/pull/7499))
The names of the new`add_monoid_hom`s parallel the names in my recent `quadratic_form` PR, [#7417](https://github.com/leanprover-community/mathlib/pull/7417).

### [2021-05-07 04:59:51](https://github.com/leanprover-community/mathlib/commit/9acbe58)
feat(normed_space/normed_group_hom): add lemmas ([#7468](https://github.com/leanprover-community/mathlib/pull/7468))
From LTE.
Written by @PatrickMassot

### [2021-05-07 04:59:50](https://github.com/leanprover-community/mathlib/commit/154fda2)
feat(category_theory/subobjects): more about kernel and image subobjects ([#7467](https://github.com/leanprover-community/mathlib/pull/7467))
Lemmas about factoring through kernel subobjects, and functoriality of kernel subobjects.

### [2021-05-06 22:46:23](https://github.com/leanprover-community/mathlib/commit/bb1fb89)
feat(data/real/basic): add real.Inf_le_iff ([#7524](https://github.com/leanprover-community/mathlib/pull/7524))
From LTE.

### [2021-05-06 22:46:22](https://github.com/leanprover-community/mathlib/commit/e00d6e0)
feat(data/polynomial/*): Specific root sets ([#7510](https://github.com/leanprover-community/mathlib/pull/7510))
Adds lemmas for the root sets of a couple specific polynomials.

### [2021-05-06 22:46:21](https://github.com/leanprover-community/mathlib/commit/6f27ef7)
chore(data/equiv/basic): Show that `Pi_curry` is really just `sigma.curry` ([#7497](https://github.com/leanprover-community/mathlib/pull/7497))
Extracts some proofs to their own lemmas, and replaces definitions with existing ones.

### [2021-05-06 22:46:20](https://github.com/leanprover-community/mathlib/commit/9aed6c9)
feat(data/finsupp,linear_algebra): `finsupp.split` is an equivalence ([#7490](https://github.com/leanprover-community/mathlib/pull/7490))
This PR shows that for finite types `η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.
To be used in the `bundled-basis` refactor

### [2021-05-06 22:46:19](https://github.com/leanprover-community/mathlib/commit/48bdd1e)
feat(data/equiv,linear_algebra): `Pi_congr_right` for `mul_equiv` and `linear_equiv` ([#7489](https://github.com/leanprover-community/mathlib/pull/7489))
This PR generalizes `equiv.Pi_congr_right` to linear equivs, adding the `mul_equiv`/`add_equiv` version as well.
To be used in the `bundled-basis` refactor

### [2021-05-06 22:46:18](https://github.com/leanprover-community/mathlib/commit/652357a)
feat(data/nat/choose/sum): alternate forms of the binomial theorem ([#7415](https://github.com/leanprover-community/mathlib/pull/7415))

### [2021-05-06 10:56:24](https://github.com/leanprover-community/mathlib/commit/9c86e38)
refactor(ring_theory/ideal/operations.lean): make is_prime.comap an instance ([#7518](https://github.com/leanprover-community/mathlib/pull/7518))

### [2021-05-06 10:56:23](https://github.com/leanprover-community/mathlib/commit/13c41e1)
feat(category_theory/linear): linear functors ([#7369](https://github.com/leanprover-community/mathlib/pull/7369))

### [2021-05-06 06:18:21](https://github.com/leanprover-community/mathlib/commit/7040c50)
feat(category_theory): the opposite of an abelian category is abelian ([#7514](https://github.com/leanprover-community/mathlib/pull/7514))

### [2021-05-06 06:18:20](https://github.com/leanprover-community/mathlib/commit/c4c6cd8)
feat(linear_algebra/finsupp): linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M` ([#7472](https://github.com/leanprover-community/mathlib/pull/7472))
This PR extends the equivalence `finsupp.finsupp_prod_equiv` to a linear equivalence (to be used in the `bundled-basis` refactor).

### [2021-05-06 06:18:19](https://github.com/leanprover-community/mathlib/commit/9154a83)
feat(algebra/*, ring_theory/valuation/basic): `linear_ordered_add_comm_group_with_top`, `add_valuation.map_sub` ([#7452](https://github.com/leanprover-community/mathlib/pull/7452))
Defines `linear_ordered_add_comm_group_with_top`
Uses that to port a few more facts about `valuation`s to `add_valuation`s.

### [2021-05-06 04:31:52](https://github.com/leanprover-community/mathlib/commit/6af5fbd)
feat(category_theory/.../zero): if a zero morphism is a mono, the source is zero ([#7462](https://github.com/leanprover-community/mathlib/pull/7462))
Some simple lemmas about zero morphisms.

### [2021-05-05 23:47:55](https://github.com/leanprover-community/mathlib/commit/009be86)
feat(measure_theory/set_integral): continuous_on.measurable_at_filter ([#7511](https://github.com/leanprover-community/mathlib/pull/7511))

### [2021-05-05 23:47:54](https://github.com/leanprover-community/mathlib/commit/709c73b)
feat(category_theory/Fintype): some lemmas and `Fintype_to_Profinite`.  ([#7491](https://github.com/leanprover-community/mathlib/pull/7491))
Adding some lemmas for morphisms on `Fintype` as functions, as well as `Fintype_to_Profinite`.
Part of the LTE.

### [2021-05-05 23:47:53](https://github.com/leanprover-community/mathlib/commit/1ef04bd)
feat(data/finsupp): prove `f.curry x y = f (x, y)` ([#7475](https://github.com/leanprover-community/mathlib/pull/7475))
This was surprisingly hard to prove actually!
To be used in the `bundled-basis` refactor

### [2021-05-05 23:47:52](https://github.com/leanprover-community/mathlib/commit/d3a46a7)
feat(algebra/big_operators): telescopic sums ([#7470](https://github.com/leanprover-community/mathlib/pull/7470))
This is restating things we already have in a form which is
slightly more convenient for the liquid tensor experiment

### [2021-05-05 23:47:51](https://github.com/leanprover-community/mathlib/commit/18ada66)
feat(order/filter_at_top_bot): extraction lemmas ([#7469](https://github.com/leanprover-community/mathlib/pull/7469))
from the liquid tensor experiment

### [2021-05-05 23:47:50](https://github.com/leanprover-community/mathlib/commit/7cc367b)
feat(category_theory/subobject): minor tweaks ([#7466](https://github.com/leanprover-community/mathlib/pull/7466))
A few minor tweaks to the `subobject` API that I wanted while working on homology.

### [2021-05-05 23:47:49](https://github.com/leanprover-community/mathlib/commit/e25cbe0)
feat(category_theory/quotient): the quotient functor is full and essentially surjective ([#7465](https://github.com/leanprover-community/mathlib/pull/7465))

### [2021-05-05 23:47:48](https://github.com/leanprover-community/mathlib/commit/19b752c)
feat(category_theory/preadditive): reformulation of mono_of_kernel_zero ([#7464](https://github.com/leanprover-community/mathlib/pull/7464))

### [2021-05-05 23:47:47](https://github.com/leanprover-community/mathlib/commit/7794969)
feat(category_theory/.../additive_functor): additive functors preserve zero objects ([#7463](https://github.com/leanprover-community/mathlib/pull/7463))

### [2021-05-05 23:47:46](https://github.com/leanprover-community/mathlib/commit/25387b6)
docs(overview): Add Stone-Weierstrass ([#7449](https://github.com/leanprover-community/mathlib/pull/7449))

### [2021-05-05 23:47:45](https://github.com/leanprover-community/mathlib/commit/f6f810c)
doc(algebraic_hierarchy): advice for adding new typeclasses ([#6854](https://github.com/leanprover-community/mathlib/pull/6854))
This is not intended as document describing all the design decisions behind our algebraic hierarchy, but rather some advice for contributors adding new typeclasses.
It can hopefully serve as a checklist for instances and definitions that should be made for any new algebraic structure being added to mathlib.
Please edit as you see fit, contribute new sections, etc. I haven't written anything yet about interactions with topology or order structures. Please consider this an invitation, or otherwise we can delete those headings later.
Thanks to @eric-wieser for providing the list of instances needed for each typeclass!

### [2021-05-05 18:50:21](https://github.com/leanprover-community/mathlib/commit/6d2869c)
feat(category_theory/.../images): image.pre_comp_epi_of_epi ([#7460](https://github.com/leanprover-community/mathlib/pull/7460))
The induced map from `image (f ≫ g)` to `image g` is an epimorphism when `f` is an epimorphism.

### [2021-05-05 18:50:20](https://github.com/leanprover-community/mathlib/commit/79edde2)
feat(topology/discrete_quotient): Add a few lemmas about discrete quotients ([#7454](https://github.com/leanprover-community/mathlib/pull/7454))
This PR adds the `discrete_quotient.map` construction and generally improves on the `discrete_quotient` API.

### [2021-05-05 18:50:19](https://github.com/leanprover-community/mathlib/commit/84d27b4)
refactor(group_theory/group_action/defs): generalize smul_mul_assoc and mul_smul_comm ([#7441](https://github.com/leanprover-community/mathlib/pull/7441))
These lemmas did not need a full algebra structure; written this way, it permits usage on `has_scalar (units R) A` given `algebra R A` (in some future PR).
For now, the old algebra lemmas are left behind, to minimize the scope of this patch.

### [2021-05-05 18:50:18](https://github.com/leanprover-community/mathlib/commit/140e17b)
feat(algebra/direct_sum_graded): a direct_sum of copies of a ring is itself a ring ([#7420](https://github.com/leanprover-community/mathlib/pull/7420))
Once this is in, it's straightforward to show `add_monoid_algebra R ι ≃+* ⨁ i : ι, R`

### [2021-05-05 18:50:17](https://github.com/leanprover-community/mathlib/commit/51bc1ca)
feat(algebra/direct_sum_graded): add direct_sum.to_semiring ([#7380](https://github.com/leanprover-community/mathlib/pull/7380))
This provides a convenient way to construct ring_homs out of `direct_sum`, and is a stronger version of `direct_sum.to_add_monoid` which applies in the presence of a `direct_sum.gmonoid` typeclass.
The new `direct_sum.lift_ring_hom` can be thought of as a universal property akin to `finsupp.lift_add_hom`.

### [2021-05-05 18:50:16](https://github.com/leanprover-community/mathlib/commit/93bc7e0)
feat(order): add some missing `pi` and `Prop` instances ([#7268](https://github.com/leanprover-community/mathlib/pull/7268))

### [2021-05-05 18:50:15](https://github.com/leanprover-community/mathlib/commit/52268b8)
feat(linear_algebra): Vandermonde matrices and their determinant ([#7116](https://github.com/leanprover-community/mathlib/pull/7116))
This PR defines the `vandermonde` matrix and gives a formula for its determinant.
@paulvanwamelen: if you would like to have `det_vandermonde` in a different form (e.g. swap the order of the variables that are being summed), please let me know!

### [2021-05-05 13:56:53](https://github.com/leanprover-community/mathlib/commit/a4d5ccb)
chore(order/complete_boolean_algebra): speed up Inf_sup_Inf ([#7506](https://github.com/leanprover-community/mathlib/pull/7506))
On my machine, avoiding `finish` takes the proof from 13s to 0.3s.

### [2021-05-05 13:56:52](https://github.com/leanprover-community/mathlib/commit/94150f3)
chore(group_theory/nielsen_schreier): typos in module doc-string ([#7500](https://github.com/leanprover-community/mathlib/pull/7500))
This fixes a discrepancy between the doc-string and the rest of the file.

### [2021-05-05 13:56:51](https://github.com/leanprover-community/mathlib/commit/3a8796d)
feat(category_theory/path_category): extensionality for functors out of path category ([#7494](https://github.com/leanprover-community/mathlib/pull/7494))
This adds an extensionality lemma for functors out of a path category, which simplifies some proofs in the free-forgetful adjunction.

### [2021-05-05 13:56:50](https://github.com/leanprover-community/mathlib/commit/18af6b5)
feat(algebra/module): `linear_equiv.refl.symm = refl` ([#7493](https://github.com/leanprover-community/mathlib/pull/7493))
To be part of the `bundled_basis` refactor

### [2021-05-05 13:56:49](https://github.com/leanprover-community/mathlib/commit/1823aee)
feat(algebra/module): `S`-linear equivs are also `R`-linear equivs ([#7476](https://github.com/leanprover-community/mathlib/pull/7476))
This PR extends `linear_map.restrict_scalars` to `linear_equiv`s.
To be used in the `bundled-basis` refactor.

### [2021-05-05 13:56:48](https://github.com/leanprover-community/mathlib/commit/9b1b854)
feat(data/fintype/basic): add set.to_finset_range ([#7426](https://github.com/leanprover-community/mathlib/pull/7426))

### [2021-05-05 13:56:47](https://github.com/leanprover-community/mathlib/commit/bb9216c)
feat(category_theory/opposites): iso.unop ([#7400](https://github.com/leanprover-community/mathlib/pull/7400))

### [2021-05-05 13:56:45](https://github.com/leanprover-community/mathlib/commit/78e36a7)
feat(analysis/convex/extreme): extreme sets ([#7357](https://github.com/leanprover-community/mathlib/pull/7357))
define extreme sets

### [2021-05-05 12:20:10](https://github.com/leanprover-community/mathlib/commit/b765d4e)
Change the bors timeout to 8 hours ([#7513](https://github.com/leanprover-community/mathlib/pull/7513))
We've hit a 6 hour timeout repeatedly in the last few days, resulting in nothing getting built.

### [2021-05-04 02:29:18](https://github.com/leanprover-community/mathlib/commit/5a91d05)
feat(data/finset/lattice): add sup_image ([#7428](https://github.com/leanprover-community/mathlib/pull/7428))
This also renames `finset.map_sup` to `finset.sup_map` to match `finset.sup_insert` and `finset.sup_singleton`.
The `inf` versions are added too.

### [2021-05-03 21:31:42](https://github.com/leanprover-community/mathlib/commit/3773525)
feat(ring_theory/finiteness): add lemmas ([#7409](https://github.com/leanprover-community/mathlib/pull/7409))
I add here some preliminary lemmas to prove that a monoid is finitely generated iff the monoid algebra is.

### [2021-05-03 21:31:41](https://github.com/leanprover-community/mathlib/commit/67dad97)
chore(data/fintype): rework `fintype.equiv_fin` and dependencies ([#7136](https://github.com/leanprover-community/mathlib/pull/7136))
These changes should make the declarations `fintype.equiv_fin`, `fintype.card_eq`
and `fintype.equiv_of_card_eq` more convenient to use.
Renamed:
 * `fintype.equiv_fin` -> `fintype.trunc_equiv_fin`
Deleted:
 * `fintype.nonempty_equiv_of_card_eq` (use `fintype.equiv_of_card_eq` instead)
 * `fintype.exists_equiv_fin` (use `fintype.card` and `fintype.(trunc_)equiv_fin` instead)
Added:
 * `fintype.equiv_fin`: noncomputable, non-`trunc` version of `fintype.equiv_fin`
 * `fintype.equiv_of_card_eq`: noncomputable, non-`trunc` version of `fintype.trunc_equiv_of_card_eq`
 * `fintype.(trunc_)equiv_fin_of_card_eq` (intermediate result/specialization of `fintype.(trunc_)equiv_of_card_eq`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60fintype.2Eequiv_fin.60.20.2B.20.60fin.2Ecast.60)

### [2021-05-03 17:06:15](https://github.com/leanprover-community/mathlib/commit/048240e)
chore(*): update to lean 3.30.0c ([#7264](https://github.com/leanprover-community/mathlib/pull/7264))
There's quite a bit of breakage from no longer reducing `acc.rec` so aggressively.  That is, a well-founded definition like `nat.factors` will no longer reduce definitionally.  Where you could write `rfl` before, you might now need to write `by rw nat.factors` or `by simp [nat.factors]`.
A more inconvenient side-effect of this change is that `dec_trivial` becomes less powerful, since it also relies on the definitional reduction.  For example `nat.factors 1 = []` is no longer true by `dec_trivial` (or `rfl`).  Often you can replace `dec_trivial` by `simp` or `norm_num`.
For extremely simple definitions that only use well-founded relations of rank ω, you could consider rewriting them to use structural recursion on a fuel parameter instead.  The functions `nat.mod` and `nat.div` in core have been rewritten in this way, please consult the [corresponding Lean PR](https://github.com/leanprover-community/lean/pull/570/files) for details on the implementation.

### [2021-05-03 14:11:12](https://github.com/leanprover-community/mathlib/commit/7da8303)
feat(category_theory/preadditive): Schur's lemma ([#7366](https://github.com/leanprover-community/mathlib/pull/7366))
We prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.

### [2021-05-03 07:41:58](https://github.com/leanprover-community/mathlib/commit/62c06a5)
feat(data/finset/basic): a finset has card at most one iff it is contained in a singleton ([#7404](https://github.com/leanprover-community/mathlib/pull/7404))

### [2021-05-02 18:59:48](https://github.com/leanprover-community/mathlib/commit/0cc3cd5)
feat(topology/category): Profinite has colimits ([#7434](https://github.com/leanprover-community/mathlib/pull/7434))
Show that a reflective subcategory of a cocomplete category is cocomplete, and derive that `CompHaus` and `Profinite` have colimits.

### [2021-05-02 14:19:06](https://github.com/leanprover-community/mathlib/commit/c7ba3dd)
refactor(linear_algebra/eigenspace): refactor exists_eigenvalue ([#7345](https://github.com/leanprover-community/mathlib/pull/7345))
We replace the proof of `exists_eigenvalue` with the more general fact:
```
/--
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
lemma exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type*) [field 𝕜] [is_alg_closed 𝕜]
  {A : Type*} [nontrivial A] [ring A] [algebra 𝕜 A] [I : finite_dimensional 𝕜 A] (f : A) :
  ∃ c : 𝕜, ¬ is_unit (f - algebra_map 𝕜 A c) := ...
```
We can then use this fact to prove Schur's lemma.

### [2021-05-02 10:42:35](https://github.com/leanprover-community/mathlib/commit/58e990d)
chore(dynamics/periodic_pts): remove duplicate of nat.dvd_right_iff_eq ([#7435](https://github.com/leanprover-community/mathlib/pull/7435))

### [2021-05-02 09:28:57](https://github.com/leanprover-community/mathlib/commit/4bd1c83)
feat(topology/category/Profinite): Any continuous bijection of profinite spaces is an isomorphism. ([#7430](https://github.com/leanprover-community/mathlib/pull/7430))

### [2021-05-02 04:27:19](https://github.com/leanprover-community/mathlib/commit/30f3788)
feat(topology/discrete_quotient): Discrete quotients of topological spaces ([#7425](https://github.com/leanprover-community/mathlib/pull/7425))
This PR defines the type of discrete quotients of a topological space and provides a basic API.
In a subsequent PR, this will be used to show that a profinite space is the limit of its finite quotients, which will be needed for the liquid tensor experiment.

### [2021-05-02 04:27:18](https://github.com/leanprover-community/mathlib/commit/6d7e756)
feat(linear_algebra/char_poly): charpoly of `left_mul_matrix`  ([#7397](https://github.com/leanprover-community/mathlib/pull/7397))
This is an important ingredient for showing the field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.

### [2021-05-02 04:27:17](https://github.com/leanprover-community/mathlib/commit/cfc7415)
feat(field_theory/polynomial_galois_group): Galois group is S_p ([#7352](https://github.com/leanprover-community/mathlib/pull/7352))
Proves that a Galois group is isomorphic to S_p, under certain conditions.

### [2021-05-02 00:17:41](https://github.com/leanprover-community/mathlib/commit/6624bbe)
feat(category_theory/limits): dualizing some results ([#7391](https://github.com/leanprover-community/mathlib/pull/7391))
Requested on [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/LocallyConstant.20preserves.20colimits/near/236442281).

### [2021-05-02 00:17:39](https://github.com/leanprover-community/mathlib/commit/6e836c4)
feat(group_theory/perm/{cycles, cycle_type}): permutations are conjugate iff they have the same cycle type ([#7335](https://github.com/leanprover-community/mathlib/pull/7335))
Slightly strengthens the induction principle `equiv.perm.cycle_induction_on`
Proves that two permutations are conjugate iff they have the same cycle type: `equiv.perm.is_conj_iff_cycle_type_eq`

### [2021-05-02 00:17:38](https://github.com/leanprover-community/mathlib/commit/106ac8e)
feat(category_theory): definition of R-linear category ([#7321](https://github.com/leanprover-community/mathlib/pull/7321))

### [2021-05-02 00:17:37](https://github.com/leanprover-community/mathlib/commit/decb556)
feat(geometry/euclidean/basic): lemmas about angles and distances ([#7140](https://github.com/leanprover-community/mathlib/pull/7140))

### [2021-05-01 20:07:58](https://github.com/leanprover-community/mathlib/commit/ea379b0)
feat(topology/continuous_function): the Stone-Weierstrass theorem ([#7305](https://github.com/leanprover-community/mathlib/pull/7305))
# The Stone-Weierstrass theorem
If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact Hausdorff space,
separates points, then it is dense.
We argue as follows.
* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).
## Future work
Prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).
Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact Hausdorff spaces.

### [2021-05-01 18:03:22](https://github.com/leanprover-community/mathlib/commit/d3c565d)
feat(category_theory/monoidal): the monoidal coherence theorem ([#7324](https://github.com/leanprover-community/mathlib/pull/7324))
This PR contains a proof of the monoidal coherence theorem, stated in the following way: if `C` is any type, then the free monoidal category over `C` is a preorder.
This should immediately imply the statement needed in the `coherence` branch.

### [2021-05-01 15:16:03](https://github.com/leanprover-community/mathlib/commit/790ec6b)
feat(algebra/archimedean): rat.cast_round for non-archimedean fields ([#7424](https://github.com/leanprover-community/mathlib/pull/7424))
The theorem still applies to the non-canonical archimedean instance (at least if you use simp).  I've also added `rat.cast_ceil` because it seems to fit here.

### [2021-05-01 15:16:02](https://github.com/leanprover-community/mathlib/commit/92b9048)
chore(topology/continuous_function/algebra): put `coe_fn_monoid_hom `into the `continuous_map` namespace ([#7423](https://github.com/leanprover-community/mathlib/pull/7423))
Rather than adding `continuous_map.` to the definition, this wraps everything in a namespace to make this type of mistake unlikely to happen again.
This also adds `comp_monoid_hom'` to golf a proof.

### [2021-05-01 09:09:54](https://github.com/leanprover-community/mathlib/commit/5511275)
chore(measure_theory/ae_eq_fun_metric): remove useless file ([#7419](https://github.com/leanprover-community/mathlib/pull/7419))
The file `measure_theory/ae_eq_fun_metric.lean` used to contain an edistance on the space of equivalence classes of functions. It has been replaced by the use of the `L^1` space in [#5510](https://github.com/leanprover-community/mathlib/pull/5510), so this file is now useless and should be removed.

### [2021-05-01 09:09:53](https://github.com/leanprover-community/mathlib/commit/d04af20)
feat(linear_algebra/quadratic_form): add lemmas about sums of quadratic forms ([#7417](https://github.com/leanprover-community/mathlib/pull/7417))

### [2021-05-01 09:09:52](https://github.com/leanprover-community/mathlib/commit/bf0f15a)
chore(algebra/algebra/basic): add missing lemmas ([#7412](https://github.com/leanprover-community/mathlib/pull/7412))

### [2021-05-01 06:41:10](https://github.com/leanprover-community/mathlib/commit/e3de4e3)
fix(algebra/direct_sum_graded): replace badly-stated and slow `simps` lemmas with manual ones  ([#7403](https://github.com/leanprover-community/mathlib/pull/7403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simps.20is.20very.20slow/near/236636962). The `simps mul` attribute on `direct_sum.ghas_mul.of_add_subgroups` was taking 44s, only to produce a lemma that wasn't very useful anyway.

### [2021-05-01 06:41:09](https://github.com/leanprover-community/mathlib/commit/aa37eee)
feat(analysis/special_functions/integrals): integral of `cos x ^ n` ([#7402](https://github.com/leanprover-community/mathlib/pull/7402))
The reduction of `∫ x in a..b, cos x ^ n`, ∀ n ∈ ℕ, 2 ≤ n, as well as the integral of `cos x ^ 2` as a special case.

### [2021-05-01 06:41:08](https://github.com/leanprover-community/mathlib/commit/2cc8128)
feat(algebra/polynomial): generalize to `multiset` products ([#7399](https://github.com/leanprover-community/mathlib/pull/7399))
This PR generalizes the results in `algebra.polynomial.big_operators` to sums and products of multisets.
The new multiset results are stated for `multiset.prod t`, not `(multiset.map t f).prod`. To get the latter, you can simply rewrite with `multiset.map_map`.

### [2021-05-01 00:19:22](https://github.com/leanprover-community/mathlib/commit/d5d22c5)
feat(algebra/squarefree): add sq_mul_squarefree lemmas ([#7282](https://github.com/leanprover-community/mathlib/pull/7282))
Every positive natural number can be expressed as m^2 * n where n is square free. Used in [#7274](https://github.com/leanprover-community/mathlib/pull/7274)

### [2021-05-01 00:19:21](https://github.com/leanprover-community/mathlib/commit/b51cee2)
feat(data/polynomial/coeff): Add smul_eq_C_mul ([#7240](https://github.com/leanprover-community/mathlib/pull/7240))
Adding a lemma `polynomial.smul_eq_C_mul` for single variate polynomials analogous to `mv_polynomial.smul_eq_C_mul` for multivariate.

### [2021-05-01 00:19:20](https://github.com/leanprover-community/mathlib/commit/b88a9d1)
feat(category_theory/enriched): abstract enriched categories ([#7175](https://github.com/leanprover-community/mathlib/pull/7175))
# Enriched categories
We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.
We do not assume here that `V` is a concrete category,
so there does not need to be a "honest" underlying category!
Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.
This file contains the definitions of `V`-enriched categories and
`V`-functors.
We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.
We verify that when `V = Type v`, all these notion reduce to the usual ones.

### [2021-05-01 00:19:19](https://github.com/leanprover-community/mathlib/commit/802c5b5)
feat(linear_algebra/determinant): various operations preserve the determinant ([#7115](https://github.com/leanprover-community/mathlib/pull/7115))
These are a couple of helper lemmas for computing the determinant of a Vandermonde matrix.

### [2021-05-01 00:19:18](https://github.com/leanprover-community/mathlib/commit/6c61779)
refactor(group_theory/order_of_element): use minimal_period for the definition ([#7082](https://github.com/leanprover-community/mathlib/pull/7082))
This PR redefines `order_of_element` in terms of `function.minimal_period`. It furthermore introduces a predicate on elements of a finite group to be of finite order.
Co-authored by: Damiano Testa adomani@gmail.com