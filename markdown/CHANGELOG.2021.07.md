### [2021-07-31 21:11:47](https://github.com/leanprover-community/mathlib/commit/4c2edb0)
feat(data/equiv/mul_add): add `units.coe_inv` ([#8477](https://github.com/leanprover-community/mathlib/pull/8477))
* rename old `units.coe_inv` to `units.coe_inv''`;
* add new `@[simp, norm_cast, to_additive] lemma units.coe_inv` about
  coercion of units of a group;
* add missing `coe_to_units`.

### [2021-07-31 21:11:46](https://github.com/leanprover-community/mathlib/commit/6c6dd04)
feat(logic/relation): add `*.comap` for `reflexive`, `symmetric`, and `transitive` ([#8469](https://github.com/leanprover-community/mathlib/pull/8469))

### [2021-07-31 20:17:15](https://github.com/leanprover-community/mathlib/commit/0827f3a)
feat(topology/metric_space/holder): add `holder_on_with` ([#8454](https://github.com/leanprover-community/mathlib/pull/8454))

### [2021-07-31 18:55:07](https://github.com/leanprover-community/mathlib/commit/b3943dc)
feat(algebra/archimedean): `order_dual α` is archimedean ([#8476](https://github.com/leanprover-community/mathlib/pull/8476))

### [2021-07-31 16:29:04](https://github.com/leanprover-community/mathlib/commit/339a122)
chore(data/sym): move `data.sym` and `data.sym2` to `data.sym.basic` and `data.sym.sym2` ([#8471](https://github.com/leanprover-community/mathlib/pull/8471))

### [2021-07-31 13:15:04](https://github.com/leanprover-community/mathlib/commit/0a48016)
doc(analysis/calculus/conformal): fix a docstring ([#8479](https://github.com/leanprover-community/mathlib/pull/8479))
Fix a grammar mistake

### [2021-07-30 16:11:00](https://github.com/leanprover-community/mathlib/commit/6e400b9)
feat(data/matrix/basic): update_{column,row}_subsingleton ([#8422](https://github.com/leanprover-community/mathlib/pull/8422))

### [2021-07-30 12:33:57](https://github.com/leanprover-community/mathlib/commit/977063f)
chore(group_theory/congruence): a few `simp` lemmas ([#8452](https://github.com/leanprover-community/mathlib/pull/8452))
* add `con.comap_rel`;
* add `@[simp]` to `con.ker_rel`;
* replace `con.comp_mk'_apply` with `con.coe_mk'`;
* [unrelated] add `commute.semiconj_by`.

### [2021-07-30 07:20:29](https://github.com/leanprover-community/mathlib/commit/98b0d18)
feat(analysis/normed_space/SemiNormedGroup/kernel): Fix universes + add explicit ([#8467](https://github.com/leanprover-community/mathlib/pull/8467))
See associated discussion from [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib/near/247575730)

### [2021-07-30 02:40:20](https://github.com/leanprover-community/mathlib/commit/8c89a52)
feat(algebra/ordered_monoid_lemmas): add one `strict_mono` lemma and a few doc-strings ([#8465](https://github.com/leanprover-community/mathlib/pull/8465))
The product of strictly monotone functions is strictly monotone (and some doc-strings).
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/monotonicity.20for.20sums.20and.20products.20of.20monotone.20functions)

### [2021-07-29 15:02:31](https://github.com/leanprover-community/mathlib/commit/a4f1653)
feat(ring_theory): Dedekind domains have invertible fractional ideals  ([#8396](https://github.com/leanprover-community/mathlib/pull/8396))
This PR proves the other side of the equivalence `is_dedekind_domain → is_dedekind_domain_inv`, and uses this to provide a `comm_group_with_zero (fractional_ideal A⁰ K)` instance.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr

### [2021-07-29 13:21:06](https://github.com/leanprover-community/mathlib/commit/69e3c79)
feat(logic/unique): unique_of_subsingleton ([#8415](https://github.com/leanprover-community/mathlib/pull/8415))

### [2021-07-29 11:52:13](https://github.com/leanprover-community/mathlib/commit/7a89150)
doc(data/nat/pairing): fix ascii table markdown ([#8460](https://github.com/leanprover-community/mathlib/pull/8460))

### [2021-07-29 06:51:42](https://github.com/leanprover-community/mathlib/commit/cd6f272)
feat(order/*): a bunch of lemmas about `order_iso` ([#8451](https://github.com/leanprover-community/mathlib/pull/8451))

### [2021-07-28 22:58:41](https://github.com/leanprover-community/mathlib/commit/6d3e936)
feat(measure_theory): add @[to_additive] ([#8142](https://github.com/leanprover-community/mathlib/pull/8142))
This PR adds `@[to_additive]` to `haar_measure` and everything that depends on. This will allow us to define the Lebesgue measure on `ℝ` and `ℝ ^ n` as the Haar measure (or just show that it is equal to it).

### [2021-07-28 21:04:18](https://github.com/leanprover-community/mathlib/commit/870b9d8)
ci(bors.toml): add merge-conflict to block_labels ([#8455](https://github.com/leanprover-community/mathlib/pull/8455))

### [2021-07-28 21:04:17](https://github.com/leanprover-community/mathlib/commit/92a5be8)
feat(ring,group,monoid): map_equiv lemmas for different structures ([#8453](https://github.com/leanprover-community/mathlib/pull/8453))
There is some inconsistency in the statements of these lemmas because there is a coercion from `ring_equiv` to `ring_hom`, but not `mul_equiv` to `monoid_hom`.

### [2021-07-28 19:44:39](https://github.com/leanprover-community/mathlib/commit/7180d2f)
feat(group_theory/coset): Show that `quotient_group.left_rel` and `left_coset_equivalence` are the same thing ([#8382](https://github.com/leanprover-community/mathlib/pull/8382))

### [2021-07-28 17:10:49](https://github.com/leanprover-community/mathlib/commit/32c8227)
feat(analysis/normed_space/basic): define inclusion `locally_constant X G → C(X, G)` as various types of bundled morphism ([#8448](https://github.com/leanprover-community/mathlib/pull/8448))

### [2021-07-28 14:08:17](https://github.com/leanprover-community/mathlib/commit/b71d38c)
feat(algebra/big_operators/basic): add lemmas about prod and sum of finset.erase ([#8449](https://github.com/leanprover-community/mathlib/pull/8449))
This adds:
* `finset.prod_erase_mul`
* `finset.mul_prod_erase`
* `finset.sum_erase_add`
* `finset.add_sum_erase`

### [2021-07-28 14:08:16](https://github.com/leanprover-community/mathlib/commit/0ccd2f6)
feat(data/dfinsupp): add simp lemma `single_eq_zero` ([#8447](https://github.com/leanprover-community/mathlib/pull/8447))
This matches `finsupp.single_eq_zero`.
Also adds `dfinsupp.ext_iff`, and changes some lemma arguments to be explicit.

### [2021-07-28 11:16:48](https://github.com/leanprover-community/mathlib/commit/4acfa92)
chore(algebra/floor): add a few trivial `simp` lemmas about `floor` ([#8450](https://github.com/leanprover-community/mathlib/pull/8450))

### [2021-07-28 09:02:05](https://github.com/leanprover-community/mathlib/commit/30ff935)
feat(topology/algebra): topological fields ([#8316](https://github.com/leanprover-community/mathlib/pull/8316))
Including the completion of completeable topological fields.
From the perfectoid spaces project.

### [2021-07-28 02:23:58](https://github.com/leanprover-community/mathlib/commit/52e6e4c)
chore(scripts): update nolints.txt ([#8446](https://github.com/leanprover-community/mathlib/pull/8446))
I am happy to remove some nolints for you!

### [2021-07-28 00:40:18](https://github.com/leanprover-community/mathlib/commit/7c5fa72)
refactor(group_theory/sylow): Extract a lemma from the proof of Cauchy's theorem ([#8376](https://github.com/leanprover-community/mathlib/pull/8376))
Also added one other consequence of card_modeq_card_fixed_points.

### [2021-07-28 00:40:17](https://github.com/leanprover-community/mathlib/commit/37fc4cf)
feat(group_theory/subgroup): equiv_map_of_injective ([#8371](https://github.com/leanprover-community/mathlib/pull/8371))
Also for rings and submonoids. The version for modules, `submodule.equiv_map_of_injective`, was already there.

### [2021-07-27 23:02:33](https://github.com/leanprover-community/mathlib/commit/cc7627a)
feat(analysis/normed_space/basic): define `normed_group` structure induced by injective group homomorphism ([#8443](https://github.com/leanprover-community/mathlib/pull/8443))

### [2021-07-27 23:02:32](https://github.com/leanprover-community/mathlib/commit/1b0391a)
feat(data/nat/totient): totient_mul ([#8441](https://github.com/leanprover-community/mathlib/pull/8441))
Also made `data/nat/totient` import `data/zmod/basic` instead of the other way round because I think people are more likely to want `zmod` but not `totient` than `totient` but not `zmod`.
Also deleted the deprecated `gpowers` because it caused a name clash in `group_theory/subgroup` when the imports were changed.

### [2021-07-27 23:02:31](https://github.com/leanprover-community/mathlib/commit/a445c45)
feat(measure_theory/interval_integrable): a monotone function is interval integrable ([#8398](https://github.com/leanprover-community/mathlib/pull/8398))

### [2021-07-27 19:34:42](https://github.com/leanprover-community/mathlib/commit/9f75dc8)
feat(measure_theory/lebesgue_measure): volume s ≤ diam s ([#8437](https://github.com/leanprover-community/mathlib/pull/8437))
* for `s : set real`, `volume s ≤ diam s`;
* for `s : set (ι → real)`, `volume s ≤ ∏ i, diam (eval i '' s) ≤ diam s ^ fintype.card ι`.

### [2021-07-27 19:34:41](https://github.com/leanprover-community/mathlib/commit/5375918)
feat(topology/metric_space/antilipschitz): ediam of image/preimage ([#8435](https://github.com/leanprover-community/mathlib/pull/8435))
Also review API

### [2021-07-27 19:34:40](https://github.com/leanprover-community/mathlib/commit/d57b6f9)
chore(data/dfinsupp): add yet more map_dfinsupp_sum lemmas ([#8400](https://github.com/leanprover-community/mathlib/pull/8400))
As always, the one of quadratically many combinations of `FOO_hom.map_BAR_sum` is never there when you need it.

### [2021-07-27 19:34:39](https://github.com/leanprover-community/mathlib/commit/aea21af)
feat(ring_theory): `is_dedekind_domain_inv` implies `is_dedekind_domain` ([#8315](https://github.com/leanprover-community/mathlib/pull/8315))
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr

### [2021-07-27 19:34:38](https://github.com/leanprover-community/mathlib/commit/a052dd6)
doc(algebra/invertible): implementation notes about `invertible` instances ([#8197](https://github.com/leanprover-community/mathlib/pull/8197))
In the discussion on [#8195](https://github.com/leanprover-community/mathlib/pull/8195), I suggested to add these implementation notes. Creating a new PR should allow for a bit more direct discussion on the use of and plans for `invertible`.

### [2021-07-27 19:34:37](https://github.com/leanprover-community/mathlib/commit/2ea73d1)
feat(analysis/normed_space/SemiNormedGroup): has_cokernels ([#7628](https://github.com/leanprover-community/mathlib/pull/7628))
# Cokernels in SemiNormedGroup₁ and SemiNormedGroup
We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels.
So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

### [2021-07-27 16:37:38](https://github.com/leanprover-community/mathlib/commit/768980a)
feat(topology/locally_constant/basic): coercion of locally-constant function to continuous map ([#8444](https://github.com/leanprover-community/mathlib/pull/8444))

### [2021-07-27 16:37:36](https://github.com/leanprover-community/mathlib/commit/3faee06)
feat(algebra/order_functions): max/min commutative and other props ([#8416](https://github.com/leanprover-community/mathlib/pull/8416))
The statements of the commutivity, associativity, and left commutativity of min and max are stated only in the rewrite lemmas, and not in their "commutative" synonyms.
This prevents them from being discoverable by suggest and related tactics. We now provide the synonyms explicitly.

### [2021-07-27 16:37:35](https://github.com/leanprover-community/mathlib/commit/6c2f80c)
feat(category_theory/limits): disjoint coproducts ([#8380](https://github.com/leanprover-community/mathlib/pull/8380))
Towards a more detailed hierarchy of categorical properties.

### [2021-07-27 16:37:34](https://github.com/leanprover-community/mathlib/commit/bb44e1a)
feat(category_theory/subobject): generalise bot of subobject lattice ([#8232](https://github.com/leanprover-community/mathlib/pull/8232))

### [2021-07-27 13:18:35](https://github.com/leanprover-community/mathlib/commit/b61ce02)
feat(number_theory/padics/padic_norm): add p^v(n) | n ([#8442](https://github.com/leanprover-community/mathlib/pull/8442))
Add some API for `padic_val_nat` (a convenient function for e.g. Sylow theory).

### [2021-07-27 10:18:45](https://github.com/leanprover-community/mathlib/commit/7ae8da4)
fix(algebra/big_operators/ring): `finset.sum_mul_sum` is true in a non-assoc non-unital semiring ([#8436](https://github.com/leanprover-community/mathlib/pull/8436))

### [2021-07-27 10:18:44](https://github.com/leanprover-community/mathlib/commit/3b590f3)
feat(logic/embedding): add a coe instance from equiv to embeddings ([#8323](https://github.com/leanprover-community/mathlib/pull/8323))

### [2021-07-27 08:42:12](https://github.com/leanprover-community/mathlib/commit/23e7c84)
fix(algebra/ordered_group): add missing `to_additive`, fix `simps` ([#8429](https://github.com/leanprover-community/mathlib/pull/8429))
* Add `order_iso.add_left` and `order_iso.add_right`.
* Use `to_equiv :=` instead of `..` to ensure
  `rfl : (order_iso.mul_right a).to_equiv = equiv.mul_right a`.
* Simplify unapplied `(order_iso.mul_left a).symm` etc.

### [2021-07-27 08:42:11](https://github.com/leanprover-community/mathlib/commit/391746b)
feat(data/zmod/basic): chinese remainder theorem ([#8356](https://github.com/leanprover-community/mathlib/pull/8356))

### [2021-07-27 08:42:10](https://github.com/leanprover-community/mathlib/commit/65006d2)
feat(linear_algebra/linear_independent): finsupp.total is not equal to a vector outside the support of the coefficients ([#8338](https://github.com/leanprover-community/mathlib/pull/8338))
…

### [2021-07-27 08:42:09](https://github.com/leanprover-community/mathlib/commit/7e37f20)
feat(group_theory/perm/cycles): more lemmas ([#8175](https://github.com/leanprover-community/mathlib/pull/8175))

### [2021-07-27 07:49:28](https://github.com/leanprover-community/mathlib/commit/d99788a)
feat(measure_theory/borel_space): lemmas about `is_pi_system_Ioo` and `finite_spanning_sets_in` ([#8434](https://github.com/leanprover-community/mathlib/pull/8434))

### [2021-07-27 07:49:27](https://github.com/leanprover-community/mathlib/commit/eae3ead)
feat(topology/instances/ennreal): diameter of `s : set real` ([#8433](https://github.com/leanprover-community/mathlib/pull/8433))

### [2021-07-27 06:14:26](https://github.com/leanprover-community/mathlib/commit/fb815d7)
feat(algebra/ring/basic): coercions of ring_hom.id ([#8439](https://github.com/leanprover-community/mathlib/pull/8439))
Two basic lemmas about the identity map as a ring hom, split off from [#3292](https://github.com/leanprover-community/mathlib/pull/3292) at @eric-wieser's suggestion.

### [2021-07-26 23:52:54](https://github.com/leanprover-community/mathlib/commit/e9309e3)
chore(data/equiv/list): rename `encodable.fintype.encodable` to `fintype.encodable` ([#8428](https://github.com/leanprover-community/mathlib/pull/8428))

### [2021-07-26 22:05:39](https://github.com/leanprover-community/mathlib/commit/26528b7)
chore(data/set): add a couple of lemmas ([#8430](https://github.com/leanprover-community/mathlib/pull/8430))

### [2021-07-26 15:58:30](https://github.com/leanprover-community/mathlib/commit/0190177)
feat(group_theory/subgroup): eq_top_of_le_card and eq_bot_of_card_le ([#8414](https://github.com/leanprover-community/mathlib/pull/8414))
Slight strengthenings of the lemmas `eq_top_of_card_eq` and `eq_bot_of_card_eq`.

### [2021-07-26 15:58:29](https://github.com/leanprover-community/mathlib/commit/d8fc081)
chore(data/pnat/basic): rename `bot_eq_zero` to `bot_eq_one`, generalize from `Prop` to `Sort*` ([#8412](https://github.com/leanprover-community/mathlib/pull/8412))

### [2021-07-26 15:58:28](https://github.com/leanprover-community/mathlib/commit/1dc4bef)
feat(ring_theory): shortcut lemmas for `coe : ideal R → fractional_ideal R⁰ K` ([#8395](https://github.com/leanprover-community/mathlib/pull/8395))
These results were already available, but in a less convenient form that e.g. asked you to prove an inclusion of submonoids `S ≤ R⁰`. Specializing them to the common case where the fractional ideal is in the field of fractions should save a bit of headache in the common cases.

### [2021-07-26 15:58:27](https://github.com/leanprover-community/mathlib/commit/708b25d)
feat(ring_theory): (fractional) ideals are finitely generated if they are invertible ([#8294](https://github.com/leanprover-community/mathlib/pull/8294))
This is one of the three steps in showing `is_dedekind_domain_inv` implies `is_dedekind_domain`.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr

### [2021-07-26 14:30:57](https://github.com/leanprover-community/mathlib/commit/4ca0a8b)
feat(data/fintype/basic): provide a `fintype` instance for `sym α n` ([#8427](https://github.com/leanprover-community/mathlib/pull/8427))
This also provides `fintype (sym.sym' α n)` as an intermediate step.
Note we make `vector.perm.is_setoid` reducible as `quotient.fintype _` requires either this or `local attribute [instance] vector.perm.is_setoid` to be accepted by the elaborator.
The referenced library note suggests making it reducible is fine.

### [2021-07-26 07:37:51](https://github.com/leanprover-community/mathlib/commit/740b41b)
feat(data/fintype/basic): add `finset.(sup|inf)_univ_eq_(supr|infi)` ([#8397](https://github.com/leanprover-community/mathlib/pull/8397))

### [2021-07-25 15:51:33](https://github.com/leanprover-community/mathlib/commit/0c024a6)
chore(*): standardize Prop/Type instance names ([#8360](https://github.com/leanprover-community/mathlib/pull/8360))
autogenerated names for these instances mention `sort.` instead of `Prop.`

### [2021-07-25 15:12:53](https://github.com/leanprover-community/mathlib/commit/2440330)
feat(linear_algebra/matrix/determinant): det_pow ([#8421](https://github.com/leanprover-community/mathlib/pull/8421))

### [2021-07-25 07:06:29](https://github.com/leanprover-community/mathlib/commit/fff96e5)
feat(measure_theory/vector_measure): add partial order instance to vector measures ([#8410](https://github.com/leanprover-community/mathlib/pull/8410))

### [2021-07-24 22:55:28](https://github.com/leanprover-community/mathlib/commit/02b37b5)
feat(group_theory/subgroup): eq_bot_of_card_eq ([#8413](https://github.com/leanprover-community/mathlib/pull/8413))
Companion lemma to `eq_top_of_card_eq`.

### [2021-07-24 15:30:35](https://github.com/leanprover-community/mathlib/commit/8a0d5e0)
feat(group_theory/complement): define subgroup complement, prove Schur-Zassenhaus ([#8008](https://github.com/leanprover-community/mathlib/pull/8008))
Defines complements, and proves Schur-Zassenhaus for abelian normal subgroups.

### [2021-07-24 14:21:11](https://github.com/leanprover-community/mathlib/commit/3d11f2d)
refactor(data/set/disjointed): split into `data.set.pairwise` and `order.disjointed` ([#8411](https://github.com/leanprover-community/mathlib/pull/8411))

### [2021-07-23 17:15:08](https://github.com/leanprover-community/mathlib/commit/dfa95ab)
feat(analysis/normed_space/linear_isometry): add an upgrade from linear isometries between finite dimensional spaces of eq finrank to linear isometry equivs ([#8406](https://github.com/leanprover-community/mathlib/pull/8406))

### [2021-07-23 11:58:54](https://github.com/leanprover-community/mathlib/commit/8062521)
feat(topology/locally_constant): Adding a module structure to locally constant functions ([#8384](https://github.com/leanprover-community/mathlib/pull/8384))
We add an A-module structure to locally constant functions from a topological space to a semiring A.
This also adds the lemmas `coe_zero`, `coe_add`, `coe_neg`, `coe_sub`, `coe_one`, `coe_mul`, `coe_div`, `coe_inv` to match the new `coe_smul` lemma.

### [2021-07-23 10:09:40](https://github.com/leanprover-community/mathlib/commit/f2f6228)
feat(set/basic): range_splitting f : range f → α ([#8340](https://github.com/leanprover-community/mathlib/pull/8340))
We use choice to provide an arbitrary injective splitting `range f → α` for any `f : α → β`.

### [2021-07-23 09:02:53](https://github.com/leanprover-community/mathlib/commit/6efc3e9)
fix(data/polynomial): Resolve a has_scalar instance diamond ([#8392](https://github.com/leanprover-community/mathlib/pull/8392))
Without this change, the following fails to close the diamond between `units.distrib_mul_action` and`polynomial.distrib_mul_action`:
```lean
example (R α : Type*) (β : α → Type*) [monoid R] [semiring α] [distrib_mul_action R α] :
  (units.distrib_mul_action : distrib_mul_action (units R) (polynomial α)) =
    polynomial.distrib_mul_action :=
rfl
```
This was because both used `polynomial.smul`, which was:
* `@[irreducible]`, which means that typeclass search is unable to unfold it to see there is no diamond
* Defined using a pattern match, which means that even if it were not reducible, it does not unfold as needed.
This adds a new test file with this diamond and some other diamonds to verify they are defeq.
Unfortunately this means `simps` now aggressively unfolds `•` on polynomials into `finsupp`s, so we need to tell `simps` precisely what lemma we actually want. This only happens in one place though.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Ehas_scalar.20and.20polynomial.2Ehas_scalar.20diamond/near/246800881)

### [2021-07-23 09:02:52](https://github.com/leanprover-community/mathlib/commit/ced1f12)
feat(analysis/calculus): strictly differentiable (or C^1) map is locally Lipschitz ([#8362](https://github.com/leanprover-community/mathlib/pull/8362))

### [2021-07-23 09:02:51](https://github.com/leanprover-community/mathlib/commit/1dafd0f)
feat(measure_theory/integrable_on): a monotone function is integrable on any compact subset ([#8336](https://github.com/leanprover-community/mathlib/pull/8336))

### [2021-07-23 08:09:01](https://github.com/leanprover-community/mathlib/commit/970b17b)
refactor(topology/metric_space): move lemmas about `paracompact_space` and the shrinking lemma to separate files ([#8404](https://github.com/leanprover-community/mathlib/pull/8404))
Only a few files in `mathlib` actually depend on results about `paracompact_space`. With this refactor, only a few files depend on `topology/paracompact_space` and `topology/shrinking_lemma`. The main side effects are that `paracompact_of_emetric` and `normal_of_emetric` instances are not available without importing `topology.metric_space.emetric_paracompact` and the shrinking lemma for balls in a proper metric space is not available without `import topology.metric_space.shrinking_lemma`.

### [2021-07-23 04:48:50](https://github.com/leanprover-community/mathlib/commit/0dd81c1)
chore(topology/urysohns_lemma): use bundled `C(X, ℝ)` ([#8402](https://github.com/leanprover-community/mathlib/pull/8402))

### [2021-07-23 02:11:57](https://github.com/leanprover-community/mathlib/commit/88de9b5)
chore(scripts): update nolints.txt ([#8403](https://github.com/leanprover-community/mathlib/pull/8403))
I am happy to remove some nolints for you!

### [2021-07-23 00:02:46](https://github.com/leanprover-community/mathlib/commit/316d69f)
feat(measure_theory/measure_space): add measurable set lemma for symmetric differences ([#8401](https://github.com/leanprover-community/mathlib/pull/8401))

### [2021-07-22 21:19:37](https://github.com/leanprover-community/mathlib/commit/0cbc6f3)
feat(linear_algebra/matrix/determinant): generalize det_fin_zero to det_eq_one_of_is_empty ([#8387](https://github.com/leanprover-community/mathlib/pull/8387))
Also golfs a nearby proof

### [2021-07-22 17:40:08](https://github.com/leanprover-community/mathlib/commit/468328d)
chore(group_theory/subgroup): the range of a monoid/group/ring/module hom from a finite type is finite ([#8293](https://github.com/leanprover-community/mathlib/pull/8293))
We have this fact for maps of types, but when changing `is_group_hom` etc from classes to structures one needs it for other bundled maps. The proofs use the power of the `copy` trick.

### [2021-07-22 16:15:21](https://github.com/leanprover-community/mathlib/commit/0bc800c)
feat(algebra/algebra/basic) new bit0/1_smul_one lemmas ([#8394](https://github.com/leanprover-community/mathlib/pull/8394))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Import.20impacts.20simp.3F/near/246713984, these lemmas should result in better behaviour with numerals

### [2021-07-22 16:15:20](https://github.com/leanprover-community/mathlib/commit/7cdd702)
chore(ring_theory): `set_like` instance for fractional ideals ([#8275](https://github.com/leanprover-community/mathlib/pull/8275))
This PR does a bit of cleanup in `fractional_ideal.lean` by using `set_like` to define `has_mem` and the coe to set.
As a bonus, it removes the `namespace ring` at the top of the file, that has been bugging me ever after I added it in the original fractional ideal PR.

### [2021-07-22 14:12:58](https://github.com/leanprover-community/mathlib/commit/38ac9ba)
chore(algebra/module/submodule): add submodule.coe_sum ([#8393](https://github.com/leanprover-community/mathlib/pull/8393))

### [2021-07-22 14:12:57](https://github.com/leanprover-community/mathlib/commit/e2cda0b)
chore(*): Prevent lemmas about the injectivity of `coe_fn` introducing un-reduced lambda terms ([#8386](https://github.com/leanprover-community/mathlib/pull/8386))
This follows on from [#6344](https://github.com/leanprover-community/mathlib/pull/6344), and fixes every result for `function.injective (λ` that is about coe_fn.

### [2021-07-22 14:12:56](https://github.com/leanprover-community/mathlib/commit/54adb19)
doc(algebra/to_additive): Add troubleshooting section ([#8143](https://github.com/leanprover-community/mathlib/pull/8143))

### [2021-07-22 12:14:07](https://github.com/leanprover-community/mathlib/commit/791d51c)
feat(group_theory/group_action): a monoid action determines a monoid hom ([#8253](https://github.com/leanprover-community/mathlib/pull/8253))
Defines the monoid hom `M -> category_theory.End X` (the latter is the monoid `X -> X`) corresponding to an action `mul_action M X` and vice versa.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)

### [2021-07-22 11:40:10](https://github.com/leanprover-community/mathlib/commit/6f88eec)
feat(algebra/lie/{submodule,subalgebra}): `lie_span`, `coe` form a Galois insertion ([#8213](https://github.com/leanprover-community/mathlib/pull/8213))

### [2021-07-22 07:37:52](https://github.com/leanprover-community/mathlib/commit/c9593dc)
feat(algebra/lie/direct_sum): define `direct_sum.lie_of`, `direct_sum.to_lie_algebra`, `direct_sum.lie_algebra_is_internal` ([#8369](https://github.com/leanprover-community/mathlib/pull/8369))
Various other minor improvements.

### [2021-07-22 06:50:48](https://github.com/leanprover-community/mathlib/commit/df50b6c)
feat(category_theory/limits): strict initial objects are initial mono ([#8267](https://github.com/leanprover-community/mathlib/pull/8267))
- [x] depends on: [#8094](https://github.com/leanprover-community/mathlib/pull/8094) 
- [x] depends on: [#8099](https://github.com/leanprover-community/mathlib/pull/8099)

### [2021-07-22 02:19:36](https://github.com/leanprover-community/mathlib/commit/bc65818)
chore(scripts): update nolints.txt ([#8390](https://github.com/leanprover-community/mathlib/pull/8390))
I am happy to remove some nolints for you!

### [2021-07-21 22:22:58](https://github.com/leanprover-community/mathlib/commit/9e35530)
fix(order/lattice, tactic.simps): add missing `notation_class` attributes to `has_(bot,top,inf,sup,compl)` ([#8381](https://github.com/leanprover-community/mathlib/pull/8381))
From the docs for `simps`:
> `@[notation_class]` should be added to all classes that define notation, like `has_mul` and
> `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
> these notation classes instead of the projections of the superclasses.
> Example: if `has_mul` is tagged with `@[notation_class]` then the projection used for `semigroup`
> will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.

### [2021-07-21 22:22:56](https://github.com/leanprover-community/mathlib/commit/f118c14)
feat(order): if `f x ≤ f y → x ≤ y`, then `f` is injective ([#8373](https://github.com/leanprover-community/mathlib/pull/8373))
I couldn't find this specific result, not assuming linear orders, anywhere and [the Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/If.20.60f.20x.20.E2.89.A4.20f.20y.20.E2.86.92.20x.20.E2.89.A4.20y.60.2C.20then.20.60f.60.20is.20injective) didn't get any responses, so I decided to PR the result.

### [2021-07-21 21:31:53](https://github.com/leanprover-community/mathlib/commit/3e6c367)
chore(topology/algebra/module): harmless generalization ([#8389](https://github.com/leanprover-community/mathlib/pull/8389))

### [2021-07-21 17:32:53](https://github.com/leanprover-community/mathlib/commit/ae1c7ee)
docs(analysis/normed_space/bounded_linear_map): add module docstring ([#8263](https://github.com/leanprover-community/mathlib/pull/8263))

### [2021-07-21 15:58:51](https://github.com/leanprover-community/mathlib/commit/9fa82b0)
feat(combinatorics/colex): order is decidable ([#8378](https://github.com/leanprover-community/mathlib/pull/8378))
Show that the colex ordering is decidable.

### [2021-07-21 12:21:17](https://github.com/leanprover-community/mathlib/commit/28b8593)
feat(combinatorics/simple_graph): `boolean_algebra` for `simple_graph`s. ([#8330](https://github.com/leanprover-community/mathlib/pull/8330))

### [2021-07-21 10:58:03](https://github.com/leanprover-community/mathlib/commit/fb58e05)
refactor(measure_theory/decomposition): move `decomposition` into a folder  ([#8374](https://github.com/leanprover-community/mathlib/pull/8374))

### [2021-07-21 07:30:27](https://github.com/leanprover-community/mathlib/commit/b45acc9)
feat(combinatorics/colex): top of the colex ordering on finite types ([#8379](https://github.com/leanprover-community/mathlib/pull/8379))

### [2021-07-21 04:59:20](https://github.com/leanprover-community/mathlib/commit/02a5696)
feat(analysis/normed_space): Define conformal maps on inner product spaces; define the groupoid of conformal maps ([#8367](https://github.com/leanprover-community/mathlib/pull/8367))

### [2021-07-20 20:10:32](https://github.com/leanprover-community/mathlib/commit/899bb5f)
feat(data/multiset): `(s.erase x).map f = (s.map f).erase (f x)` ([#8375](https://github.com/leanprover-community/mathlib/pull/8375))
A little lemma that I needed for Dedekind domains.

### [2021-07-20 18:13:44](https://github.com/leanprover-community/mathlib/commit/4676b31)
feat(data/sym2): add the universal property, and make `sym2.is_diag ⟦(x, y)⟧ ↔ x = y` true definitionally ([#8358](https://github.com/leanprover-community/mathlib/pull/8358))

### [2021-07-20 16:22:25](https://github.com/leanprover-community/mathlib/commit/6ac3059)
feat(combinatorics/colex): golf and generalise ([#8301](https://github.com/leanprover-community/mathlib/pull/8301))
Miscellaneous fixes about colex: Gives `le` versions of some `lt` lemmas, fixes a TODO, restores some names etc.

### [2021-07-20 11:23:09](https://github.com/leanprover-community/mathlib/commit/ed8d597)
fix(data/matrix/basic): remove an accidental requirement for a matrix to be square ([#8372](https://github.com/leanprover-community/mathlib/pull/8372))

### [2021-07-20 10:51:34](https://github.com/leanprover-community/mathlib/commit/fce38f1)
feat(ring_theory): define `fractional_ideal.adjoin_integral` ([#8296](https://github.com/leanprover-community/mathlib/pull/8296))
This PR shows if `x` is integral over `R`, then `R[x]` is a fractional ideal, and proves some of the essential properties of this fractional ideal.
This is an important step towards showing `is_dedekind_domain_inv` implies that the ring is integrally closed.
Co-Authored-By: Ashvni ashvni.n@gmail.com
Co-Authored-By: Filippo A. E. Nuccio filippo.nuccio@univ-st-etienne.fr

### [2021-07-20 09:52:16](https://github.com/leanprover-community/mathlib/commit/c05c15f)
feat(group_theory/order_of_element): pow_eq_mod_card ([#8354](https://github.com/leanprover-community/mathlib/pull/8354))

### [2021-07-20 08:59:36](https://github.com/leanprover-community/mathlib/commit/0f9b754)
feat(measure_theory/borel_space): generalize `monotone.measurable` to monotone on set ([#8365](https://github.com/leanprover-community/mathlib/pull/8365))

### [2021-07-20 08:59:35](https://github.com/leanprover-community/mathlib/commit/1589318)
feat(topology/continuous_function/bounded): prove `norm_eq_supr_norm` ([#8288](https://github.com/leanprover-community/mathlib/pull/8288))
More precisely we prove both:
 * `bounded_continuous_function.norm_eq_supr_norm`
 * `continuous_map.norm_eq_supr_norm`
We also introduce one new definition: `bounded_continuous_function.norm_comp`.

### [2021-07-20 08:59:34](https://github.com/leanprover-community/mathlib/commit/f5d25b4)
feat(measure_theory/vector_measure): introduce vector-valued measures ([#8247](https://github.com/leanprover-community/mathlib/pull/8247))
This PR introduces vector-valued measures and provides a method of creating signed measures without the summability requirement.

### [2021-07-20 07:56:49](https://github.com/leanprover-community/mathlib/commit/0f58e13)
chore(topology/continuous_function, analysis/normed_space): use `is_empty α` instead of `¬nonempty α` ([#8352](https://github.com/leanprover-community/mathlib/pull/8352))
Two lemmas with their assumptions changed, and some proofs golfed using the new forms of these and other lemmas.

### [2021-07-20 04:14:22](https://github.com/leanprover-community/mathlib/commit/b3fbcec)
chore(.docker): add missing library ([#8370](https://github.com/leanprover-community/mathlib/pull/8370))
Something must have changed that now needs this library. It's only installed in an intemediate build, anyway.

### [2021-07-20 03:37:36](https://github.com/leanprover-community/mathlib/commit/e0467bd)
feat(algebra.homology): homology f g w ≅ cokernel (kernel.lift g f w) ([#8355](https://github.com/leanprover-community/mathlib/pull/8355))
Per [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Challenge.20with.20homology).
I'm not certain this completely resolves the issue: perhaps we should really change the definition of `homology`. But at least this bridges the gap.

### [2021-07-19 22:25:50](https://github.com/leanprover-community/mathlib/commit/11af02c)
feat(analysis/convex): convex sets with zero ([#8234](https://github.com/leanprover-community/mathlib/pull/8234))
Split off from [#7288](https://github.com/leanprover-community/mathlib/pull/7288)

### [2021-07-19 22:25:49](https://github.com/leanprover-community/mathlib/commit/0821e6e)
feat(category_theory/limits): strict initial objects ([#8094](https://github.com/leanprover-community/mathlib/pull/8094))
- [x] depends on: [#8084](https://github.com/leanprover-community/mathlib/pull/8084)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)

### [2021-07-19 19:25:13](https://github.com/leanprover-community/mathlib/commit/afd0f92)
feat(category_theory/limits/pullbacks): generalise pullback mono lemmas ([#8302](https://github.com/leanprover-community/mathlib/pull/8302))
Generalises results to use `is_limit` rather than the canonical limit.

### [2021-07-19 15:59:39](https://github.com/leanprover-community/mathlib/commit/739b353)
chore(.gitignore): ignore lock files ([#8368](https://github.com/leanprover-community/mathlib/pull/8368))
Two reasons:
1. Sometimes these accidentally make it into PRs  (e.g. [#8344](https://github.com/leanprover-community/mathlib/pull/8344))
2. Some editor plugins (like the git in vscode) update very frequently causing these files to appear and disappear quickly in the sidebar whenever lean compiles which is annoying

### [2021-07-19 14:20:44](https://github.com/leanprover-community/mathlib/commit/ad7ab8d)
feat(linear_algebra/finsupp): `span.repr` gives an arbitrarily representation of `x : span R w` as a linear combination over `w` ([#8339](https://github.com/leanprover-community/mathlib/pull/8339))
It's convenient to be able to get hold of such a representation, even when it is not unique. We prove the only lemma about this, then mark the definition is irreducible.

### [2021-07-19 13:17:09](https://github.com/leanprover-community/mathlib/commit/02ecb62)
feat(analysis/fourier): span of monomials is dense in L^p ([#8328](https://github.com/leanprover-community/mathlib/pull/8328))

### [2021-07-19 12:28:13](https://github.com/leanprover-community/mathlib/commit/5ccf2bf)
feat(topology/metric_space/basic): an order-bounded set is metric-bounded ([#8335](https://github.com/leanprover-community/mathlib/pull/8335))

### [2021-07-19 10:21:46](https://github.com/leanprover-community/mathlib/commit/3e67932)
feat(topology/algebra/ordered): an `order_closed_topology` restricted to a subset is an `order_closed_topology` ([#8364](https://github.com/leanprover-community/mathlib/pull/8364))

### [2021-07-19 07:28:12](https://github.com/leanprover-community/mathlib/commit/dd9f1c3)
chore(order/basic): whitespaces and caps ([#8359](https://github.com/leanprover-community/mathlib/pull/8359))

### [2021-07-19 02:21:30](https://github.com/leanprover-community/mathlib/commit/6a20dd6)
chore(scripts): update nolints.txt ([#8366](https://github.com/leanprover-community/mathlib/pull/8366))
I am happy to remove some nolints for you!

### [2021-07-18 22:22:27](https://github.com/leanprover-community/mathlib/commit/ee60711)
feat(data/finset/basic): product, bUnion, sdiff lemmas ([#8321](https://github.com/leanprover-community/mathlib/pull/8321))

### [2021-07-18 17:02:30](https://github.com/leanprover-community/mathlib/commit/c2d042c)
chore(analysis/*): remove unnecessary imports ([#8344](https://github.com/leanprover-community/mathlib/pull/8344))

### [2021-07-18 17:02:29](https://github.com/leanprover-community/mathlib/commit/b02b919)
feat(measure_theory): add lemmas of equality of measures under assumptions of null difference, in particular null frontier ([#8332](https://github.com/leanprover-community/mathlib/pull/8332))
Adding lemmas in `measure_theory/measure_space` and `measure_theory/borel_space` about equality of measures of sets under the assumption that the difference of the largest to the smallest has null measure.

### [2021-07-18 17:02:28](https://github.com/leanprover-community/mathlib/commit/048263d)
feat(topology/basic): add two lemmas about frontier and two lemmas about preimages under continuous maps ([#8329](https://github.com/leanprover-community/mathlib/pull/8329))
Adding four lemmas: `frontier_eq_inter_compl_interior`, `compl_frontier_eq_union_interior`, `continuous.closure_preimage_subset`, `continuous.frontier_preimage_subset` to `topology/basic`.
These were discussed on Zulip <https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Portmanteau.20theorem/near/246037950>. The formulations closely follow Patrick's suggestions.

### [2021-07-18 15:12:25](https://github.com/leanprover-community/mathlib/commit/865e36b)
chore(order/boolean_algebra) : `compl_involutive` ([#8357](https://github.com/leanprover-community/mathlib/pull/8357))

### [2021-07-17 21:38:09](https://github.com/leanprover-community/mathlib/commit/f45df47)
feat(measure_theory/hausdorff_measure): `dimH_{s,b,}Union`, `dimH_union` ([#8351](https://github.com/leanprover-community/mathlib/pull/8351))

### [2021-07-17 19:58:11](https://github.com/leanprover-community/mathlib/commit/ad5afc2)
feat(combinatorics/hales_jewett): Hales-Jewett and Van der Waerden ([#8019](https://github.com/leanprover-community/mathlib/pull/8019))
Proves the Hales-Jewett theorem (a fundamental result in Ramsey theory on combinatorial lines) and deduces (a generalised version of) Van der Waerden's theorem on arithmetic progressions.

### [2021-07-17 17:47:12](https://github.com/leanprover-community/mathlib/commit/398027d)
feat(topology/subset_properties): add `countable_cover_nhds_within_of_sigma_compact` ([#8350](https://github.com/leanprover-community/mathlib/pull/8350))
This is a version of `countable_cover_nhds_of_sigma_compact` for a
covering of a closed set instead of the whole space.

### [2021-07-17 17:47:11](https://github.com/leanprover-community/mathlib/commit/7d754e0)
chore(analysis/calculus/mean_value): use `nnnorm` in a few lemmas ([#8348](https://github.com/leanprover-community/mathlib/pull/8348))
Use `nnnorm` instead of `norm` and `C : nnreal` in lemmas about `lipschitz_on_with`. This way we can use them to prove any statement of the form `lipschitz_on_with C f s`, not only something of the form `lipschitz_on_with (real.to_nnreal C) f s`.

### [2021-07-17 16:55:13](https://github.com/leanprover-community/mathlib/commit/3782c19)
feat(topology/algebra/ordered): add `nhds_top_basis_Ici` and `nhds_bot_basis_Iic` ([#8349](https://github.com/leanprover-community/mathlib/pull/8349))
Also add `ennreal.nhds_zero_basis_Iic` and `ennreal.supr_div`.

### [2021-07-17 16:20:16](https://github.com/leanprover-community/mathlib/commit/8139d7e)
feat(measure_theory/hausdorff_measure): μH and dimH of a `subsingleton` ([#8347](https://github.com/leanprover-community/mathlib/pull/8347))

### [2021-07-17 14:00:00](https://github.com/leanprover-community/mathlib/commit/fcde3f0)
chore(data/real/ennreal): move `x ≠ 0` case of `mul_infi` to `mul_infi_of_ne` ([#8345](https://github.com/leanprover-community/mathlib/pull/8345))

### [2021-07-17 13:14:10](https://github.com/leanprover-community/mathlib/commit/bd56531)
chore(analysis/normed_space/operator_norm): use `norm_one_class` ([#8346](https://github.com/leanprover-community/mathlib/pull/8346))
* turn `continuous_linear_map.norm_id` into a `simp` lemma;
* drop its particular case `continuous_linear_map.norm_id_field`;
* replace `continuous_linear_map.norm_id_field'` with a
  `norm_one_class` instance.

### [2021-07-17 11:26:47](https://github.com/leanprover-community/mathlib/commit/93a3764)
chore(algebra/ring/basic): drop commutativity assumptions from some division lemmas ([#8334](https://github.com/leanprover-community/mathlib/pull/8334))
* Removes `dvd_neg_iff_dvd`, `neg_dvd_iff_dvd` which duplicated `dvd_neg`, `neg_dvd`.
* Generalizes `two_dvd_bit0` to non-commutative semirings.
* Generalizes a bunch of lemmas from `comm_ring` to `ring`.
* Adds `even_neg` for `ring` to replace `int.even_neg`.

### [2021-07-17 09:38:56](https://github.com/leanprover-community/mathlib/commit/d4c0a11)
refactor(analysis/analytic/basic): refactor `change_origin` ([#8282](https://github.com/leanprover-community/mathlib/pull/8282))
Now each term of `change_origin` is defined as a sum of a formal power series, so it is clear that each term is an analytic function.

### [2021-07-17 04:19:35](https://github.com/leanprover-community/mathlib/commit/0cb634f)
feat(category_theory/subobject): subobject category equivalent to mono over category ([#8304](https://github.com/leanprover-community/mathlib/pull/8304))

### [2021-07-17 02:01:37](https://github.com/leanprover-community/mathlib/commit/e67e50f)
feat(algebra/group_theory/lemmas): add int.pow_right_injective ([#8278](https://github.com/leanprover-community/mathlib/pull/8278))
Suggested here: https://github.com/leanprover-community/mathlib/pull/7843#discussion_r668167163

### [2021-07-16 22:47:45](https://github.com/leanprover-community/mathlib/commit/10975e6)
docs(measure_theory/integral_eq_improper): fix lemma names in docs ([#8333](https://github.com/leanprover-community/mathlib/pull/8333))

### [2021-07-16 17:58:03](https://github.com/leanprover-community/mathlib/commit/8e3d9ce)
feat(measure_theory/continuous_map_dense): continuous functions are dense in Lp ([#8306](https://github.com/leanprover-community/mathlib/pull/8306))

### [2021-07-16 17:58:00](https://github.com/leanprover-community/mathlib/commit/a895300)
chore(ring_theory/fractional_ideal): prefer `(⊤ : ideal R)` over `1` ([#8298](https://github.com/leanprover-community/mathlib/pull/8298))
`fractional_ideal.lean` sometimes used `1` to denote the ideal of `R` containing each element of `R`. This PR should replace all remaining usages with `⊤ : ideal R`, following the convention in the rest of mathlib.
Also a little `simp` lemma `coe_ideal_top` which was the motivation, since the proof should have been, and is now `by refl`.

### [2021-07-16 17:03:24](https://github.com/leanprover-community/mathlib/commit/42f7ca0)
chore(linear_algebra/linear_independent): use `is_empty ι` instead of `¬nonempty ι` ([#8331](https://github.com/leanprover-community/mathlib/pull/8331))

### [2021-07-16 16:03:11](https://github.com/leanprover-community/mathlib/commit/9061ecc)
feat(topology/metric_space/holder): define Hölder continuity ([#8309](https://github.com/leanprover-community/mathlib/pull/8309))
Add definitions and some basic facts about Hölder continuous functions.

### [2021-07-16 15:14:22](https://github.com/leanprover-community/mathlib/commit/35a8d93)
chore(topology/algebra/infinite_sum): relax the requirements on `has_sum.smul` ([#8312](https://github.com/leanprover-community/mathlib/pull/8312))

### [2021-07-16 13:09:51](https://github.com/leanprover-community/mathlib/commit/162221f)
chore(set_theory/*): use `is_empty α` instead of `¬nonempty α` ([#8276](https://github.com/leanprover-community/mathlib/pull/8276))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)

### [2021-07-16 11:35:29](https://github.com/leanprover-community/mathlib/commit/9a801ef)
docs(order/rel_iso): add module docstring ([#8249](https://github.com/leanprover-community/mathlib/pull/8249))

### [2021-07-16 09:16:30](https://github.com/leanprover-community/mathlib/commit/e35d976)
chore(algebra/quaternion): add `smul_mk` ([#8126](https://github.com/leanprover-community/mathlib/pull/8126))
This follows the pattern set by `mk_mul_mk` and `mk_add_mk`.

### [2021-07-16 09:16:29](https://github.com/leanprover-community/mathlib/commit/610fab7)
feat(set_theory/cofinality): more infinite pigeonhole principles ([#7879](https://github.com/leanprover-community/mathlib/pull/7879))

### [2021-07-16 07:34:18](https://github.com/leanprover-community/mathlib/commit/e6ff367)
feat(logic/embedding): simp lemma for injectivity for embeddings ([#7881](https://github.com/leanprover-community/mathlib/pull/7881))

### [2021-07-16 05:22:17](https://github.com/leanprover-community/mathlib/commit/728eefe)
docs(data/fintype/basic): add module docstring ([#8081](https://github.com/leanprover-community/mathlib/pull/8081))

### [2021-07-16 00:27:05](https://github.com/leanprover-community/mathlib/commit/4ae9792)
chore(data/matrix/basic): add lemmas about dot_product and mul_vec ([#8325](https://github.com/leanprover-community/mathlib/pull/8325))
This renames:
* `mul_vec_one` to `one_mul_vec`
* `mul_vec_zero` to `zero_mul_vec`
and adds the new lemmas:
* `sub_mul_vec`
* `mul_vec_sub`
* `zero_mul_vec`
* `mul_vec_zero`
* `sub_dot_product`
* `dot_product_sub`
Some existing lemmas have had their variables extracted to sections.

### [2021-07-15 21:23:27](https://github.com/leanprover-community/mathlib/commit/b577bb2)
feat(measure_theory/conditional_expectation): define condexp_L2, conditional expectation of L2 functions ([#8324](https://github.com/leanprover-community/mathlib/pull/8324))

### [2021-07-15 17:38:21](https://github.com/leanprover-community/mathlib/commit/79fbd46)
feat(ring_theory/ideal): generalize two results from finset to multiset ([#8320](https://github.com/leanprover-community/mathlib/pull/8320))
Nothing exciting going on here, just copied two proofs, replaced all `finset.insert` with `multiset.cons` and `finset.prod` with `(multiset.map _).prod`, and used those to show the original results.

### [2021-07-15 16:32:09](https://github.com/leanprover-community/mathlib/commit/a783a47)
feat(data/matrix/{basic, block}): missing lemmas on conj_transpose ([#8303](https://github.com/leanprover-community/mathlib/pull/8303))
This also moves some imports around to make the star operator on vectors available in matrix/basic.lean
This is a follow up to [#8291](https://github.com/leanprover-community/mathlib/pull/8291)

### [2021-07-15 16:32:08](https://github.com/leanprover-community/mathlib/commit/66055dd)
feat(algebra/lie/cartan_matrix): define the exceptional Lie algebras ([#8299](https://github.com/leanprover-community/mathlib/pull/8299))

### [2021-07-15 15:05:29](https://github.com/leanprover-community/mathlib/commit/bc1f145)
feat(data/multiset): `<` on multisets is well-founded ([#8319](https://github.com/leanprover-community/mathlib/pull/8319))
This is vaguely related to [#5783](https://github.com/leanprover-community/mathlib/pull/5783), in that it tries to solve a similar goal of finding a minimal multiset with some property.

### [2021-07-15 13:15:59](https://github.com/leanprover-community/mathlib/commit/0597b1d)
feat(analysis/normed_space/normed_group_hom): add equalizer ([#8228](https://github.com/leanprover-community/mathlib/pull/8228))
From LTE.
We add equalizer of `normed_group_homs`.

### [2021-07-15 09:20:51](https://github.com/leanprover-community/mathlib/commit/7e5be02)
chore(algebra/*): make non-instance typeclasses reducible. ([#8322](https://github.com/leanprover-community/mathlib/pull/8322))
A follow up to [#7835](https://github.com/leanprover-community/mathlib/pull/7835)

### [2021-07-15 05:43:19](https://github.com/leanprover-community/mathlib/commit/e42af8d)
refactor(topology/category/Profinite): define Profinite as a subcategory of CompHaus ([#8314](https://github.com/leanprover-community/mathlib/pull/8314))
This adjusts the definition of Profinite to explicitly be a subcategory of CompHaus rather than a subcategory of Top which embeds into CompHaus. Essentially this means it's easier to construct an element of Profinite from an element of CompHaus.

### [2021-07-14 22:10:52](https://github.com/leanprover-community/mathlib/commit/e343609)
feat(measure_theory/simple_func_dense): induction lemmas for Lp.simple_func and Lp ([#8300](https://github.com/leanprover-community/mathlib/pull/8300))
The new lemmas, `Lp.simple_func.induction`, `Lp.induction`, allow one to prove a predicate for all elements of `Lp.simple_func` / `Lp` (here p < ∞), by proving it for characteristic functions and then checking it behaves appropriately under addition, and, in the second case, taking limits.  They are modelled on existing lemmas such as `simple_func.induction`, `mem_ℒp.induction`, `integrable.induction`.

### [2021-07-14 18:22:17](https://github.com/leanprover-community/mathlib/commit/19a156a)
refactor(algebra/ordered_ring): use `mul_le_mul'` for `canonically_ordered_comm_semiring` ([#8284](https://github.com/leanprover-community/mathlib/pull/8284))
* use `canonically_ordered_comm_semiring`, not `canonically_ordered_semiring` as a namespace;
* add an instance `canonically_ordered_comm_semiring.to_covariant_mul_le`;
* drop `canonically_ordered_semiring.mul_le_mul` etc in favor of `mul_le_mul'` etc.

### [2021-07-14 17:41:56](https://github.com/leanprover-community/mathlib/commit/e9b1fbd)
feat(combinatorics/simple_graph): add maps and subgraphs ([#8223](https://github.com/leanprover-community/mathlib/pull/8223))
Add graph homomorphisms, isomorphisms, and embeddings.  Define subgraphs and supporting lemmas and definitions.  Also renamed `edge_symm` to `adj_comm`.

### [2021-07-14 15:21:29](https://github.com/leanprover-community/mathlib/commit/bcc35c7)
feat(group_theory/submonoid/operations): `add_equiv.of_left_inverse` to match `linear_equiv.of_left_inverse` ([#8279](https://github.com/leanprover-community/mathlib/pull/8279))

### [2021-07-14 13:57:59](https://github.com/leanprover-community/mathlib/commit/375dd53)
refactor(geometry/manifold): split `bump_function` into 3 files ([#8313](https://github.com/leanprover-community/mathlib/pull/8313))
This is the a part of [#8309](https://github.com/leanprover-community/mathlib/pull/8309). Both code and comments were moved with
almost no modifications: added/removed `variables`/`section`s,
slightly adjusted comments to glue them together.

### [2021-07-14 13:57:58](https://github.com/leanprover-community/mathlib/commit/5bac21a)
chore(algebra/module/pi): add `pi.smul_def` ([#8311](https://github.com/leanprover-community/mathlib/pull/8311))
Sometimes it is useful to rewrite unapplied `s • x` (I need it in a branch that is not yet ready for review).
We already have `pi.zero_def`, `pi.add_def`, etc.

### [2021-07-14 13:57:57](https://github.com/leanprover-community/mathlib/commit/7fccf40)
feat(algebraic_topology/topological_simplex): This defines the natural functor from Top to sSet. ([#8305](https://github.com/leanprover-community/mathlib/pull/8305))
This PR also provides the geometric realization functor and the associated adjunction.

### [2021-07-14 13:57:56](https://github.com/leanprover-community/mathlib/commit/7d53431)
feat(measure_theory/integration): if a function has bounded integral on all sets of finite measure, then it is integrable ([#8297](https://github.com/leanprover-community/mathlib/pull/8297))
If the measure is sigma-finite and a function has integral bounded by some C for all measurable sets with finite measure, then its integral over the whole space is bounded by that same C. This can be used to show that a function is integrable.

### [2021-07-14 12:56:52](https://github.com/leanprover-community/mathlib/commit/3b7e7bd)
feat(normed_space): controlled_sum_of_mem_closure ([#8310](https://github.com/leanprover-community/mathlib/pull/8310))
From LTE

### [2021-07-14 11:55:45](https://github.com/leanprover-community/mathlib/commit/2e9aa83)
chore(analysis/special_functions/pow): golf a few proofs ([#8308](https://github.com/leanprover-community/mathlib/pull/8308))
* add `ennreal.zero_rpow_mul_self` and `ennreal.mul_rpow_eq_ite`;
* use the latter lemma to golf other proofs about `(x * y) ^ z`;
* drop unneeded argument in `ennreal.inv_rpow_of_pos`, rename it to
  `ennreal.inv_rpow`;
* add `ennreal.strict_mono_rpow_of_pos` and
  `ennreal.monotone_rpow_of_nonneg`, use themm to golf some proofs.

### [2021-07-14 10:14:23](https://github.com/leanprover-community/mathlib/commit/743209c)
chore(algebra/big_operators/basic): spaces around binders ([#8307](https://github.com/leanprover-community/mathlib/pull/8307))

### [2021-07-14 10:14:22](https://github.com/leanprover-community/mathlib/commit/e6731de)
feat(algebra/pointwise): `smul_comm_class` instances for `set` ([#8292](https://github.com/leanprover-community/mathlib/pull/8292))
I'm not very familiar with `smul_comm_class`, so these instances might need to be tweaked slightly.

### [2021-07-14 10:14:21](https://github.com/leanprover-community/mathlib/commit/656722c)
refactor(measure_theory/measure_space): use `covariant_class` instead of `add_le_add` ([#8285](https://github.com/leanprover-community/mathlib/pull/8285))

### [2021-07-14 10:14:18](https://github.com/leanprover-community/mathlib/commit/51cc43e)
feat(measure_theory/borel_space): a monotone function is measurable ([#8045](https://github.com/leanprover-community/mathlib/pull/8045))

### [2021-07-14 08:37:24](https://github.com/leanprover-community/mathlib/commit/8e5af43)
chore(algebra/big_operators/basic): rename sum_(nat/int)_cast and (nat/int).coe_prod ([#8264](https://github.com/leanprover-community/mathlib/pull/8264))
The current names aren't great because
1. For `sum_nat_cast` and `sum_int_cast`, the LHS isn't a sum of casts but a cast of sums, and it doesn't follow any other naming convention (`nat.cast_...` or `....coe_sum`).
2. For `.coe_prod`, the coercion from `ℕ` or `ℤ` should be called `cast`.

### [2021-07-14 06:54:06](https://github.com/leanprover-community/mathlib/commit/4709e61)
doc(*): bold a few more named theorems ([#8252](https://github.com/leanprover-community/mathlib/pull/8252))

### [2021-07-13 21:48:55](https://github.com/leanprover-community/mathlib/commit/5021c1f)
feat(data/int): conditionally complete linear order ([#8149](https://github.com/leanprover-community/mathlib/pull/8149))
Prove that the integers form a conditionally complete linear order.
I do not have a specific goal in mind for this, but it would have been helpful to formulate one of the Proof Ground problems using this.

### [2021-07-13 20:14:44](https://github.com/leanprover-community/mathlib/commit/29b63a7)
feat(data/matrix/basic): add conj_transpose ([#8291](https://github.com/leanprover-community/mathlib/pull/8291))
As requested by Eric Wieser, I pulled one single change of [#8289](https://github.com/leanprover-community/mathlib/pull/8289) out into a new PR. As such, this PR will not block anything in [#8289](https://github.com/leanprover-community/mathlib/pull/8289).

### [2021-07-13 20:14:43](https://github.com/leanprover-community/mathlib/commit/63266ff)
feat(group_theory/free_product): the free product of an indexed family of monoids ([#8256](https://github.com/leanprover-community/mathlib/pull/8256))
Defines the free product (categorical coproduct) of an indexed family of monoids. Proves its universal property. The free product of groups is a group.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)

### [2021-07-13 18:51:54](https://github.com/leanprover-community/mathlib/commit/905b875)
chore(data/matrix/block): move block matrices into their own file ([#8290](https://github.com/leanprover-community/mathlib/pull/8290))
This is a straight cut-and-paste, with no reordering or renaming.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/import.20fails/near/245802618)

### [2021-07-13 18:51:53](https://github.com/leanprover-community/mathlib/commit/461130b)
feat(category_theory/monoidal): the definition of Tor ([#7512](https://github.com/leanprover-community/mathlib/pull/7512))
# Tor, the left-derived functor of tensor product
We define `tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.
For now we have almost nothing to say about it!
It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.

### [2021-07-13 17:32:47](https://github.com/leanprover-community/mathlib/commit/b091c3f)
feat(algebra/direct_sum): the submodules of an internal direct sum satisfy `supr A = ⊤` ([#8274](https://github.com/leanprover-community/mathlib/pull/8274))
The main results here are:
* `direct_sum.add_submonoid_is_internal.supr_eq_top`
* `direct_sum.submodule_is_internal.supr_eq_top`
Which we prove using the new lemmas
* `add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom`
* `submodule.supr_eq_range_dfinsupp_lsum`
There's no obvious way to reuse the proofs between the two, but thankfully all four proofs are quite short anyway.
These should aid in shortening [#8246](https://github.com/leanprover-community/mathlib/pull/8246).

### [2021-07-13 16:48:04](https://github.com/leanprover-community/mathlib/commit/3a0ef3c)
feat(ring_theory): (strict) monotonicity of `coe_submodule` ([#8273](https://github.com/leanprover-community/mathlib/pull/8273))

### [2021-07-13 16:48:02](https://github.com/leanprover-community/mathlib/commit/8be0eda)
chore(ring_theory): allow Dedekind domains to be fields ([#8271](https://github.com/leanprover-community/mathlib/pull/8271))
During the Dedekind domain project, we found that the `¬ is_field R` condition is almost never needed, and it gets in the way when proving rings of integers are Dedekind domains. This PR removes this assumption from the three definitions.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>

### [2021-07-13 15:34:19](https://github.com/leanprover-community/mathlib/commit/815e91f)
chore(data/nat/prime): fix + add missing lemmas ([#8066](https://github.com/leanprover-community/mathlib/pull/8066))
I fixed up some indents as well, as they were bothering me quite a bit. The only "new" content is 597 - 617.

### [2021-07-13 12:28:43](https://github.com/leanprover-community/mathlib/commit/bf86834)
chore(probability_theory/integration): style changes. Make arguments implicit, remove spaces, etc. ([#8286](https://github.com/leanprover-community/mathlib/pull/8286))
- make the measurable_space arguments of indep_fun implicit again. They were made explicit to accommodate the way `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun` was written, with explicit `(borel ennreal)` arguments. Those arguments are not needed and are removed.
- use `measurable_set T` instead of `M.measurable_set' T`.
- write the type of several `have` explicitly.
- remove some spaces
- ensure there is only one tactic per line
- use `exact` instead of `apply` when the tactic is finishing

### [2021-07-13 12:28:42](https://github.com/leanprover-community/mathlib/commit/f1e27d2)
feat(linear_algebra/finsupp): mem_supr_iff_exists_finset ([#8268](https://github.com/leanprover-community/mathlib/pull/8268))
This is an `iff` version of `exists_finset_of_mem_supr`

### [2021-07-13 12:28:40](https://github.com/leanprover-community/mathlib/commit/3e56439)
chore(data/set/intervals): relax linear_order to preorder in the proofs of `Ixx_eq_empty_iff` ([#8071](https://github.com/leanprover-community/mathlib/pull/8071))
The previous formulations of `Ixx_eq_empty(_iff)` are basically a chaining of this formulation plus `not_lt` or `not_le`. But `not_lt` and `not_le` require `linear_order`. Removing them allows relaxing the typeclasses assumptions on `Ixx_eq_empty_iff` and slightly generalising `Ixx_eq_empty`.

### [2021-07-13 11:23:36](https://github.com/leanprover-community/mathlib/commit/bb53a92)
chore(data/mv_polynomial/basic): use `is_empty σ` instead of `¬nonempty σ` ([#8277](https://github.com/leanprover-community/mathlib/pull/8277))
Split from [#7826](https://github.com/leanprover-community/mathlib/pull/7826)

### [2021-07-13 10:08:14](https://github.com/leanprover-community/mathlib/commit/dd9a0ea)
feat(geometry/manifold): add `charted_space` and `model_with_corners` for pi types ([#6578](https://github.com/leanprover-community/mathlib/pull/6578))
Also use `set.image2` in the `charted_space` instance for `model_prod`.

### [2021-07-13 09:28:15](https://github.com/leanprover-community/mathlib/commit/7bed785)
refactor(topology/metric/gromov_hausdorff_realized): speed up a proof ([#8287](https://github.com/leanprover-community/mathlib/pull/8287))

### [2021-07-13 07:40:48](https://github.com/leanprover-community/mathlib/commit/f1f4084)
feat(topology/algebra/ordered/basic): basis for the neighbourhoods of `top`/`bot` ([#8283](https://github.com/leanprover-community/mathlib/pull/8283))

### [2021-07-13 07:09:10](https://github.com/leanprover-community/mathlib/commit/f302c97)
feat(measure_theory/l2_space): the inner product of indicator_const_Lp and a function is the set_integral ([#8229](https://github.com/leanprover-community/mathlib/pull/8229))

### [2021-07-12 22:46:15](https://github.com/leanprover-community/mathlib/commit/9dfb9a6)
chore(topology/topological_fiber_bundle): renaming ([#8270](https://github.com/leanprover-community/mathlib/pull/8270))
In this PR I changed
- `prebundle_trivialization` to `topological_fiber_bundle.pretrivialization`
- `bundle_trivialization` to `topological_fiber_bundle.trivialization`
so to make names consistent with `vector_bundle`. I also changed the name of the file for consistency.

### [2021-07-12 22:46:14](https://github.com/leanprover-community/mathlib/commit/cde5748)
feat(measure_theory/measure_space): add `finite_measure_sub` instance ([#8239](https://github.com/leanprover-community/mathlib/pull/8239))

### [2021-07-12 21:10:34](https://github.com/leanprover-community/mathlib/commit/5ea9a07)
feat(measure_theory/integration): add `lintegral_union` ([#8238](https://github.com/leanprover-community/mathlib/pull/8238))

### [2021-07-12 21:10:33](https://github.com/leanprover-community/mathlib/commit/4cd6179)
refactor(measure_theory/simple_func_dense): generalize L1.simple_func.dense_embedding to Lp ([#8209](https://github.com/leanprover-community/mathlib/pull/8209))
This PR generalizes all the more abstract results about approximation by simple functions, from L1 to Lp (`p ≠ ∞`).  Notably, this includes 
* the definition `Lp.simple_func`, the `add_subgroup` of `Lp` of classes containing a simple representative
* the coercion `Lp.simple_func.coe_to_Lp` from this subgroup to `Lp`, as a continuous linear map
* `Lp.simple_func.dense_embedding`, this subgroup is dense in `Lp`
* `mem_ℒp.induction`, to prove a predicate holds for `mem_ℒp` functions it suffices to prove that it behaves appropriately on `mem_ℒp` simple functions
Many lemmas get renamed from `L1.simple_func.*` to `Lp.simple_func.*`, and have hypotheses or conclusions changed from `integrable` to `mem_ℒp`.
I take the opportunity to streamline the construction by deleting some instances which typeclass inference can find, and some lemmas which are re-statements of more general results about `add_subgroup`s in normed groups.  In my opinion, this extra material obscures the structure of the construction.  Here is a list of the definitions deleted:
- `instance : has_coe (α →₁ₛ[μ] E) (α →₁[μ] E)`
- `instance : has_coe_to_fun (α →₁ₛ[μ] E)`
- `instance : inhabited (α →₁ₛ[μ] E)`
- `protected def normed_group : normed_group (α →₁ₛ[μ] E)`
and lemmas deleted (in the `L1.simple_func` namespace unless specified):
- `simple_func.tendsto_approx_on_univ_L1`
- `eq`
- `eq_iff`
- `eq_iff'`
- `coe_zero`
- `coe_add`
- `coe_neg`
- `coe_sub`
- `edist_eq`
- `dist_eq`
- `norm_eq`
- `lintegral_edist_to_simple_func_lt_top`
- `dist_to_simple_func`

### [2021-07-12 18:54:39](https://github.com/leanprover-community/mathlib/commit/a9cb722)
docs(data/rel): add module docstring ([#8248](https://github.com/leanprover-community/mathlib/pull/8248))

### [2021-07-12 17:16:06](https://github.com/leanprover-community/mathlib/commit/a2b00f3)
feat(algebra/opposites): functoriality of the opposite monoid ([#8254](https://github.com/leanprover-community/mathlib/pull/8254))
A hom `α →* β` can equivalently be viewed as a hom `αᵒᵖ →* βᵒᵖ`.
Split off from [#7395](https://github.com/leanprover-community/mathlib/pull/7395)

### [2021-07-12 16:03:49](https://github.com/leanprover-community/mathlib/commit/6fa678f)
feat(ring_theory): `coe_submodule S (⊤ : ideal R) = 1` ([#8272](https://github.com/leanprover-community/mathlib/pull/8272))
A little `simp` lemma and its dependencies. As I was implementing it, I saw the definition of `has_one (submodule R A)` can be cleaned up a bit.

### [2021-07-12 14:22:14](https://github.com/leanprover-community/mathlib/commit/0a8e3ed)
feat(data/equiv/fin): fin_order_iso_subtype ([#8258](https://github.com/leanprover-community/mathlib/pull/8258))
Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`.

### [2021-07-12 14:22:13](https://github.com/leanprover-community/mathlib/commit/66cc624)
feat(data/list/basic): more lemmas about permutations_aux2 ([#8198](https://github.com/leanprover-community/mathlib/pull/8198))

### [2021-07-12 12:59:26](https://github.com/leanprover-community/mathlib/commit/695cb07)
feat({data,linear_algebra}/{finsupp,dfinsupp}): add `{add_submonoid,submodule}.[d]finsupp_sum_mem` ([#8269](https://github.com/leanprover-community/mathlib/pull/8269))
These lemmas are trivial consequences of the finset lemmas, but having them avoids having to unfold `[d]finsupp.sum`.
`dfinsupp_sum_add_hom_mem` is particularly useful because this one has some messy decidability arguments to eliminate.

### [2021-07-12 10:54:32](https://github.com/leanprover-community/mathlib/commit/40ffaa5)
feat(linear_algebra/free_module): add module.free.resolution ([#8231](https://github.com/leanprover-community/mathlib/pull/8231))
Any module is a quotient of a free module. This is stated as surjectivity of `finsupp.total M M R id : (M →₀ R) →ₗ[R] M`.

### [2021-07-12 07:00:28](https://github.com/leanprover-community/mathlib/commit/e1c649d)
feat(category_theory/abelian): the five lemma ([#8265](https://github.com/leanprover-community/mathlib/pull/8265))

### [2021-07-12 06:15:32](https://github.com/leanprover-community/mathlib/commit/92d0dd8)
feat(category_theory/limits): monomorphisms from initial ([#8099](https://github.com/leanprover-community/mathlib/pull/8099))
Defines a class for categories where every morphism from initial is a monomorphism. If the category has a terminal object, this is equivalent to saying the unique morphism from initial to terminal is a monomorphism, so this is essentially a "zero_le_one" for categories. I'm happy to change the name of this class!
This axiom does not appear to have a common name, though it is (equivalent to) the second of Freyd's AT axioms: specifically it is a property shared by abelian categories and pretoposes. The main advantage to this class is that it is the precise condition required for the subobject lattice to have a bottom element, resolving the discussion here: https://github.com/leanprover-community/mathlib/pull/6278#discussion_r577702542
I've also made some minor changes to later parts of this file, essentially de-duplicating arguments, and moving the `comparison` section up so that all the results about terminal objects in index categories of limits are together rather than split in two.

### [2021-07-12 04:01:46](https://github.com/leanprover-community/mathlib/commit/e22789e)
feat(algebra/big_operators/finprod): add a few lemmas ([#8261](https://github.com/leanprover-community/mathlib/pull/8261))
* add `finprod_eq_single` and `finsum_eq_single`;
* add `finprod_induction` and `finsum_induction`;
* add `single_le_finprod` and `single_le_finsum`;
* add `one_le_finprod'` and `finsum_nonneg`.

### [2021-07-12 01:47:08](https://github.com/leanprover-community/mathlib/commit/d5c6f61)
feat(algebra/group/hom): monoid_hom.injective_iff in iff form ([#8259](https://github.com/leanprover-community/mathlib/pull/8259))
Interpret the injectivity of a group hom as triviality of the kernel,
in iff form. This helps make explicit simp lemmas about
the application of such homs,
as in the added `extend_domain_eq_one_iff` lemma.

### [2021-07-11 20:46:12](https://github.com/leanprover-community/mathlib/commit/24d7a8c)
feat(group_theory/quotient_group): lemmas for quotients involving `subgroup_of` ([#8111](https://github.com/leanprover-community/mathlib/pull/8111))

### [2021-07-11 20:13:23](https://github.com/leanprover-community/mathlib/commit/19beb12)
feat(measure_theory/{lp_space,set_integral}): extend linear map lemmas from R to is_R_or_C ([#8210](https://github.com/leanprover-community/mathlib/pull/8210))

### [2021-07-11 19:28:27](https://github.com/leanprover-community/mathlib/commit/6d200cb)
feat(analysis/normed_space/inner_product): Bessel's inequality ([#8251](https://github.com/leanprover-community/mathlib/pull/8251))
A proof both of Bessel's inequality and that the infinite sum defined by Bessel's inequality converges.

### [2021-07-11 14:37:02](https://github.com/leanprover-community/mathlib/commit/bee165a)
feat(category_theory/abelian/opposite): Adds some op-related isomorphism for (co)kernels. ([#8255](https://github.com/leanprover-community/mathlib/pull/8255))

### [2021-07-11 13:10:23](https://github.com/leanprover-community/mathlib/commit/1e62218)
feat(data/int/gcd): norm_num extension for gcd ([#8053](https://github.com/leanprover-community/mathlib/pull/8053))
Implements a `norm_num` plugin to evaluate terms like `nat.gcd 6 8 = 2`, `nat.coprime 127 128`, and so on for `{nat, int}.{gcd, lcm, coprime}`.

### [2021-07-11 10:44:09](https://github.com/leanprover-community/mathlib/commit/14f324b)
chore(data/set/basic): remove set.decidable_mem ([#8240](https://github.com/leanprover-community/mathlib/pull/8240))
The only purpose of this instance was to enable the spelling `[decidable_pred s]` when what is actually needed is `decidable_pred (∈ s)`, which is a bad idea.
This is a follow-up to [#8211](https://github.com/leanprover-community/mathlib/pull/8211).
Only two proofs needed this instance, and both were using completely the wrong lemmas anyway.

### [2021-07-11 02:16:20](https://github.com/leanprover-community/mathlib/commit/850928d)
chore(scripts): update nolints.txt ([#8257](https://github.com/leanprover-community/mathlib/pull/8257))
I am happy to remove some nolints for you!

### [2021-07-11 01:40:33](https://github.com/leanprover-community/mathlib/commit/e627394)
feat(analysis/special_functions): limit of (1+1/x)^x ([#8243](https://github.com/leanprover-community/mathlib/pull/8243))
Resolves https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/e.20as.20limit.20of.20.281.2B1.2Fn.29.5En.

### [2021-07-10 20:40:14](https://github.com/leanprover-community/mathlib/commit/90d8d46)
feat(category_theory/monad): monad forget is monadic ([#8161](https://github.com/leanprover-community/mathlib/pull/8161))
cc @adamtopaz 
wip since I need to dualise

### [2021-07-10 18:38:10](https://github.com/leanprover-community/mathlib/commit/8b4628e)
feat(data/fintype/basic): induction principle for finite types ([#8158](https://github.com/leanprover-community/mathlib/pull/8158))
This lets us prove things about finite types by induction, analogously to proving things about natural numbers by induction. Here `pempty` plays the role of `0` and `option` plays the role of `nat.succ`. We need an extra hypothesis that our statement is invariant under equivalence of types. Used in [#8019](https://github.com/leanprover-community/mathlib/pull/8019).

### [2021-07-10 08:01:40](https://github.com/leanprover-community/mathlib/commit/aa78feb)
feat(category_theory/is_connected): constant functor is full ([#8233](https://github.com/leanprover-community/mathlib/pull/8233))
Shows the constant functor on a connected category is full.
Also golfs a later proof slightly.

### [2021-07-10 08:01:39](https://github.com/leanprover-community/mathlib/commit/b1806d1)
chore(analysis/normed_space/banach): speed up the proof ([#8230](https://github.com/leanprover-community/mathlib/pull/8230))
This proof has timed out in multiple refactor PRs I've made. This splits out an auxiliary definition.
The new definition takes about 3.5s to elaborate, and the two lemmas are <500ms each.
The old lemma took 45s.

### [2021-07-10 07:14:29](https://github.com/leanprover-community/mathlib/commit/9e0462c)
feat(topology/algebra/infinite_sum): summable_empty ([#8241](https://github.com/leanprover-community/mathlib/pull/8241))
Every function over an empty type is summable.

### [2021-07-10 04:07:29](https://github.com/leanprover-community/mathlib/commit/e18b3a8)
feat(category_theory/limits): transfer limit creation along diagram iso ([#8237](https://github.com/leanprover-community/mathlib/pull/8237))

### [2021-07-10 03:32:13](https://github.com/leanprover-community/mathlib/commit/d0e09dd)
feat(linear_algebra/matrix/nonsingular_inverse): more lemmas ([#8216](https://github.com/leanprover-community/mathlib/pull/8216))
add more defs and lemmas

### [2021-07-10 02:13:42](https://github.com/leanprover-community/mathlib/commit/b52c1f0)
chore(scripts): update nolints.txt ([#8245](https://github.com/leanprover-community/mathlib/pull/8245))
I am happy to remove some nolints for you!

### [2021-07-09 22:11:36](https://github.com/leanprover-community/mathlib/commit/70320f7)
feat(category_theory/category/Kleisli): Fix lint errors ([#8244](https://github.com/leanprover-community/mathlib/pull/8244))
Fixes some lint errors for this file: unused arguments, module doc, inhabited instances

### [2021-07-09 19:00:53](https://github.com/leanprover-community/mathlib/commit/a444e81)
feat(measure_theory/borel_space): a preconnected set is measurable ([#8044](https://github.com/leanprover-community/mathlib/pull/8044))
In a conditionally complete linear order equipped with the order topology and the corresponding borel σ-algebra, any preconnected set is measurable.

### [2021-07-09 15:19:06](https://github.com/leanprover-community/mathlib/commit/bcd61b1)
feat(algebra/category): provide right adjoint instances for forget ([#8235](https://github.com/leanprover-community/mathlib/pull/8235))
Also adds some universe variables since they weren't inferred sensibly.

### [2021-07-09 13:36:51](https://github.com/leanprover-community/mathlib/commit/ee01817)
chore(data/set/basic): use `decidable_pred (∈ s)` instead of `decidable_pred s`. ([#8211](https://github.com/leanprover-community/mathlib/pull/8211))
The latter exploits the fact that sets are functions to Prop, and is an annoying form as lemmas are never stated about it.
In future we should consider removing the `set.decidable_mem` instance which encourages this misuse.
Making this change reveals a collection of pointless decidable arguments requiring that finset membership be decidable; something which is always true anyway.
Two proofs in `data/pequiv` caused a crash inside the C++ portion of the `finish` tactic; it was easier to just write the simple proofs manually than to debug the C++ code.

### [2021-07-09 13:36:49](https://github.com/leanprover-community/mathlib/commit/a312e7e)
chore(topology/topological_fiber_bundle): reorganizing the code ([#7938](https://github.com/leanprover-community/mathlib/pull/7938))
What I do here:
 - Get rid of `local_triv`: it is not needed.
 - Change `local_triv_ext` to `local_triv`
 - Rename `local_triv'` as `local_triv_as_local_equiv` (name suggested by @sgouezel)
 - Improve type class inference by getting rid of `dsimp` in instances
 - Move results about `bundle` that do not need the topology in an appropriate file
 - Update docs accordingly.
Nothing else.

### [2021-07-09 12:52:46](https://github.com/leanprover-community/mathlib/commit/abde210)
feat(analysis/complex/isometry): restate result more abstractly ([#7908](https://github.com/leanprover-community/mathlib/pull/7908))
Define `rotation` as a group homomorphism from the circle to the isometry group of `ℂ`.  State the classification of isometries of `ℂ` more abstractly, using this construction.  Also golf some proofs.

### [2021-07-09 09:42:47](https://github.com/leanprover-community/mathlib/commit/1134865)
feat(category_theory/limits): finite products from finite limits ([#8236](https://github.com/leanprover-community/mathlib/pull/8236))
Adds instances for finite products from finite limits.

### [2021-07-08 23:05:26](https://github.com/leanprover-community/mathlib/commit/e46447b)
feat(measure_theory/measure_space): prob_le_one ([#7913](https://github.com/leanprover-community/mathlib/pull/7913))

### [2021-07-08 18:57:18](https://github.com/leanprover-community/mathlib/commit/9d40a59)
feat(group_theory,linear_algebra): third isomorphism theorem for groups and modules ([#8203](https://github.com/leanprover-community/mathlib/pull/8203))
This PR proves the third isomorphism theorem for (additive) groups and modules, and also adds a few `simp` lemmas that I needed.

### [2021-07-08 17:14:02](https://github.com/leanprover-community/mathlib/commit/a7b660e)
feat(linear_algebra/prod): add coprod_map_prod ([#8220](https://github.com/leanprover-community/mathlib/pull/8220))
This also adds `submodule.coe_sup` and `set.mem_finset_prod`. The latter was intended to be used to show `submodule.coe_supr`, but I didn't really need that and it was hard to prove.

### [2021-07-08 16:41:12](https://github.com/leanprover-community/mathlib/commit/13486fe)
chore(measure_theory/measure_space): untangle `probability_measure`, `finite_measure`, and `has_no_atoms` ([#8222](https://github.com/leanprover-community/mathlib/pull/8222))
This only moves existing lemmas around. Putting all the instance together up front seems to result in lemmas being added in adhoc places - by adding `section`s, this should guide future contributions.

### [2021-07-08 14:46:44](https://github.com/leanprover-community/mathlib/commit/b10062e)
feat(data/finset/noncomm_prod): noncomm_prod_union_of_disjoint ([#8169](https://github.com/leanprover-community/mathlib/pull/8169))

### [2021-07-08 13:06:54](https://github.com/leanprover-community/mathlib/commit/a4b0b48)
feat(data/nat/basic): lt_one_iff ([#8224](https://github.com/leanprover-community/mathlib/pull/8224))

### [2021-07-08 11:22:43](https://github.com/leanprover-community/mathlib/commit/fb22ae3)
refactor(order/rel_iso): move statements about intervals to data/set/intervals ([#8150](https://github.com/leanprover-community/mathlib/pull/8150))
This means that we can talk about `rel_iso` without needing to transitively import `ordered_group`s
This PR takes advantage of this to define `order_iso.mul_(left|right)[']` to mirror `equiv.mul_(left|right)[']`.

### [2021-07-08 09:27:54](https://github.com/leanprover-community/mathlib/commit/03e2cbd)
chore(group_theory/perm/support): support_pow_le over nat ([#8225](https://github.com/leanprover-community/mathlib/pull/8225))
Previously, both `support_pow_le` and `support_gpow_le` had the
power as an `int`. Now we properly differentiate the two and avoid
slow defeq checks.

### [2021-07-08 02:02:10](https://github.com/leanprover-community/mathlib/commit/0ee238c)
chore(scripts): update nolints.txt ([#8227](https://github.com/leanprover-community/mathlib/pull/8227))
I am happy to remove some nolints for you!

### [2021-07-07 20:50:25](https://github.com/leanprover-community/mathlib/commit/70aef28)
feat(group_theory/perm/list): concrete permutations from a list ([#7451](https://github.com/leanprover-community/mathlib/pull/7451))

### [2021-07-07 17:46:10](https://github.com/leanprover-community/mathlib/commit/5f2358c)
fix(data/complex/basic): ensure `algebra ℝ ℂ` is computable ([#8166](https://github.com/leanprover-community/mathlib/pull/8166))
Without this `complex.ring` instance, `ring ℂ` is found via `division_ring.to_ring` and `field.to_division_ring`, and `complex.field` is non-computable.
The non-computable-ness previously contaminated `distrib_mul_action R ℂ` and even some properties of `finset.sum` on complex numbers! To avoid this type of mistake again, we remove `noncomputable theory` and manually flag the parts we actually expect to be computable.

### [2021-07-07 15:54:45](https://github.com/leanprover-community/mathlib/commit/e0ca853)
feat(algebra/group/units): teach `simps` about `units` ([#8204](https://github.com/leanprover-community/mathlib/pull/8204))
This also introduces `units.copy` to match `invertible.copy`, and uses it to make some lemmas in normed_space/units true by `rfl` (and generated by `simps`).

### [2021-07-07 15:54:44](https://github.com/leanprover-community/mathlib/commit/ce3d53b)
fix(data/real/basic): provide a computable `module` instance ([#8164](https://github.com/leanprover-community/mathlib/pull/8164))
Without this instance, `normed_field.to_normed_space` and `normed_space.to_module` is tried first, but this results in a noncomputable instance.

### [2021-07-07 15:11:09](https://github.com/leanprover-community/mathlib/commit/05e8ed2)
chore(feat/algebra/lie/from_cartan_matrix): rename file ([#8219](https://github.com/leanprover-community/mathlib/pull/8219))

### [2021-07-07 15:11:08](https://github.com/leanprover-community/mathlib/commit/836c549)
docs(category_theory/limits/shapes/products): add module docstring ([#8212](https://github.com/leanprover-community/mathlib/pull/8212))
Also resolves some TODOs.

### [2021-07-07 14:30:42](https://github.com/leanprover-community/mathlib/commit/5145261)
feat(data/fintype/list): induced fintype on nodup lists ([#8171](https://github.com/leanprover-community/mathlib/pull/8171))

### [2021-07-07 13:35:19](https://github.com/leanprover-community/mathlib/commit/5796783)
chore(category_theory): homogenise usage of notation for terminal objects ([#8106](https://github.com/leanprover-community/mathlib/pull/8106))
I went with the option that is used more frequently, but I'm also happy to switch to the space-less option if people prefer it.

### [2021-07-07 12:02:07](https://github.com/leanprover-community/mathlib/commit/bb5ab1e)
chore(measure_theory/measure_space): add missing `finite_measure` instances ([#8214](https://github.com/leanprover-community/mathlib/pull/8214))

### [2021-07-07 12:02:05](https://github.com/leanprover-community/mathlib/commit/41ec92e)
feat(algebra/lie/from_cartan_matrix): construction of a Lie algebra from a Cartan matrix ([#8206](https://github.com/leanprover-community/mathlib/pull/8206))

### [2021-07-07 12:02:02](https://github.com/leanprover-community/mathlib/commit/126a7b6)
feat(data/multiset/basic): add_eq_union_iff_disjoint ([#8173](https://github.com/leanprover-community/mathlib/pull/8173))

### [2021-07-07 10:24:57](https://github.com/leanprover-community/mathlib/commit/29beb1f)
feat(analysis/normed_space/int): norms of (units of) integers ([#8136](https://github.com/leanprover-community/mathlib/pull/8136))
From LTE

### [2021-07-07 10:24:56](https://github.com/leanprover-community/mathlib/commit/89e1837)
fix(tactic/core): add subst' ([#8129](https://github.com/leanprover-community/mathlib/pull/8129))
`tactic.subst'` gives a better error message when the substituted variable is a local definition.
It is hard to fix this in core (without touching C++ code), since `tactic.is_local_def` is in mathlib

### [2021-07-07 10:24:54](https://github.com/leanprover-community/mathlib/commit/47c7c01)
feat(measure_theory/measure_space): if `f` restricted to `s` is measurable, then `f` is `ae_measurable` wrt `μ.restrict s` ([#8098](https://github.com/leanprover-community/mathlib/pull/8098))

### [2021-07-07 08:47:55](https://github.com/leanprover-community/mathlib/commit/06f0d51)
refactor(algebra/ordered_group): another step in the `order` refactor -- ordered groups ([#8060](https://github.com/leanprover-community/mathlib/pull/8060))
This PR represents another wave of generalization of proofs, following from the `order` refactor.  It is another step towards [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-07-07 02:20:39](https://github.com/leanprover-community/mathlib/commit/20d8e83)
chore(scripts): update nolints.txt ([#8217](https://github.com/leanprover-community/mathlib/pull/8217))
I am happy to remove some nolints for you!

### [2021-07-06 18:26:45](https://github.com/leanprover-community/mathlib/commit/d7653b8)
chore(category_theory/monad/algebra): lint and golf ([#8160](https://github.com/leanprover-community/mathlib/pull/8160))
Adds a module docstring and golfs some proofs, including removing `erw`.

### [2021-07-06 16:15:28](https://github.com/leanprover-community/mathlib/commit/03c8904)
doc(data/set/function): add set. prefixes for doc-gen ([#8215](https://github.com/leanprover-community/mathlib/pull/8215))
This means these names will be linked.

### [2021-07-06 14:26:27](https://github.com/leanprover-community/mathlib/commit/ec07293)
doc(*): add bold in doc strings for named theorems i.e. **mean value theorem** ([#8182](https://github.com/leanprover-community/mathlib/pull/8182))

### [2021-07-06 13:47:12](https://github.com/leanprover-community/mathlib/commit/1399997)
feat(category_theory/closed): Exponential ideals ([#4930](https://github.com/leanprover-community/mathlib/pull/4930))
Define exponential ideals.

### [2021-07-06 11:32:50](https://github.com/leanprover-community/mathlib/commit/98e8408)
feat(geometry/manifold/algebra): `left_invariant_derivation` ([#8108](https://github.com/leanprover-community/mathlib/pull/8108))
In this PR we prove that left-invariant derivations are a Lie algebra.

### [2021-07-06 10:58:03](https://github.com/leanprover-community/mathlib/commit/23d22e4)
feat(category_theory/abelian/ext): Defines Ext functors. ([#8186](https://github.com/leanprover-community/mathlib/pull/8186))
See my comment from [#7525](https://github.com/leanprover-community/mathlib/pull/7525)

### [2021-07-06 08:21:53](https://github.com/leanprover-community/mathlib/commit/2f72023)
chore(measure_theory/decomposition): change statement to use the `finite_measure` instance ([#8207](https://github.com/leanprover-community/mathlib/pull/8207))

### [2021-07-06 05:05:33](https://github.com/leanprover-community/mathlib/commit/6365c6c)
feat(algebra/invertible): construction from is_unit ([#8205](https://github.com/leanprover-community/mathlib/pull/8205))

### [2021-07-06 02:10:44](https://github.com/leanprover-community/mathlib/commit/27841bb)
chore(scripts): update nolints.txt ([#8208](https://github.com/leanprover-community/mathlib/pull/8208))
I am happy to remove some nolints for you!

### [2021-07-05 17:24:46](https://github.com/leanprover-community/mathlib/commit/77e1e3b)
feat(linear_algebra/nonsingular_inverse): add lemmas about `invertible` ([#8201](https://github.com/leanprover-community/mathlib/pull/8201))

### [2021-07-05 17:24:45](https://github.com/leanprover-community/mathlib/commit/9d99833)
feat(category_theory/linear/yoneda): A linear version of Yoneda. ([#8199](https://github.com/leanprover-community/mathlib/pull/8199))

### [2021-07-05 17:24:44](https://github.com/leanprover-community/mathlib/commit/b6bf7a3)
feat(measure_theory/lp_space): define the Lp function corresponding to the indicator of a set ([#8193](https://github.com/leanprover-community/mathlib/pull/8193))
I also moved some measurability lemmas from the integrable_on file to measure_space. I needed them and lp_space is before integrable_on in the import graph.

### [2021-07-05 17:24:43](https://github.com/leanprover-community/mathlib/commit/7eab080)
feat(topology/instances/ennreal): add tsum lemmas for ennreal.to_real ([#8184](https://github.com/leanprover-community/mathlib/pull/8184))

### [2021-07-05 15:47:16](https://github.com/leanprover-community/mathlib/commit/38a6f26)
feat(algebra/to_additive): map pow to smul ([#7888](https://github.com/leanprover-community/mathlib/pull/7888))
* Allows `@[to_additive]` to reorder consecutive arguments of specified identifiers.
* This can be specified with the attribute `@[to_additive_reorder n m ...]` to swap arguments `n` and `n+1`, arguments `m` and `m+1` etc. (start counting from 1).
* The only two attributes currently in use are:
```lean
attribute [to_additive_reorder 1] has_pow
attribute [to_additive_reorder 1 4] has_pow.pow
```
* It will  eta-expand all expressions that have as head a declaration with attribute `to_additive_reorder` until they have the required number of arguments. This is required to correctly deal with partially applied terms.
* Hack: if the first two arguments are reordered, then the first two universe variables are also reordered (this happens to be the correct behavior for `has_pow` and `has_pow.pow`). It might be cleaner to have a separate attribute for that, but that given the low amount of times that I expect that we use `to_additive_reorder`, this seems unnecessary.
* This PR also allows the user to write `@[to_additive?]` to trace the generated declaration.

### [2021-07-05 14:57:50](https://github.com/leanprover-community/mathlib/commit/f2edc5a)
feat(category_theory/preadditive/opposite): Adds some instances and lemmas ([#8202](https://github.com/leanprover-community/mathlib/pull/8202))
This PR adds some instances and lemmas related to opposites and additivity of functors.

### [2021-07-05 14:14:01](https://github.com/leanprover-community/mathlib/commit/0b0d8e7)
refactor(ring_theory): turn `localization_map` into a typeclass ([#8119](https://github.com/leanprover-community/mathlib/pull/8119))
This PR replaces the previous `localization_map (M : submodule R) Rₘ` definition (a ring hom `R →+* Rₘ` that presents `Rₘ` as the localization of `R` at `M`) with a new `is_localization M Rₘ` typeclass that puts these requirements on `algebra_map R Rₘ` instead. An important benefit is that we no longer need to mess with `localization_map.codomain` to put an `R`-algebra structure on `Rₘ`, we can just work with `Rₘ` directly.
The important API changes are in commit 0de78dc, all other commits are simply fixes to the dependent files.
Main changes:
 * `localization_map` has been replaced with `is_localization`, similarly `away_map` -> `is_localization.away`, `localization_map.at_prime` -> `is_localization.at_prime` and `fraction_map` -> `is_fraction_ring`
 * many declarations taking the `localization_map` as a parameter now take `R` and/or `M` and/or `Rₘ`, depending on what can be inferred easily
 * `localization_map.to_map` has been replaced with `algebra_map R Rₘ`
 * `localization_map.codomain` and its instances have been removed (you can now directly use `Rₘ`)
 * `is_localization.alg_equiv` generalizes `fraction_map.alg_equiv_of_quotient` (which has been renamed to `is_fraction_ring.alg_equiv`)
 * `is_localization.sec` has been introduced to replace `(to_localization_map _ _).sec`
 * `localization.of` have been replaced with `algebra` and `is_localization` instances on `localization`, similarly for `localization.away.of`, `localization.at_prime.of` and `fraction_ring.of`.
 * `int.fraction_map` is now an instance `rat.is_fraction_ring`
 * All files depending on the above definitions have had fixes. These were mostly straightforward, except:
 * [Some category-theory arrows in `algebraic_geometry/structure.sheaf` are now plain `ring_hom`s. This change was suggested by @justus-springer in order to help the elaborator figure out the arguments to  `is_localization`.](https://github.com/leanprover-community/mathlib/commit/cf3acc925467cc06237a13dbe4264529f9a58850)
 * Deleted `minpoly.over_int_eq_over_rat` and `minpoly.integer_dvd`, now you can just use `gcd_domain_eq_field_fractions` or `gcd_domain_dvd` respectively. [This removes code duplication in `minpoly.lean`](https://github.com/leanprover-community/mathlib/commit/5695924d85710f98ac60a7df91d7dbf27408ca26)
 * `fractional_ideal` does not need to assume `is_localization` everywhere, only for certain specific definitions
Things that stay the same:
 * `localization`, `localization.away`, `localization.at_prime` and `fraction_ring` are still a construction of localizations (although see above for `{localization,localization.away,localization.at_prime,fraction_ring}.of`)
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Refactoring.20.60localization_map.60

### [2021-07-05 13:27:54](https://github.com/leanprover-community/mathlib/commit/6bad4c6)
feat(ring_theory/trace): the composition of `trace`s is `trace` ([#8078](https://github.com/leanprover-community/mathlib/pull/8078))
A little group of lemmas from the Dedekind domain project.

### [2021-07-05 11:54:51](https://github.com/leanprover-community/mathlib/commit/8ba94ab)
chore(algebra/invertible): units coerced to their monoid are invertible ([#8195](https://github.com/leanprover-community/mathlib/pull/8195))

### [2021-07-05 10:29:14](https://github.com/leanprover-community/mathlib/commit/63c8d33)
feat(linear_algebra/matrix/reindex): generalize reindex_linear_equiv to operate on an arbitrary ring ([#8159](https://github.com/leanprover-community/mathlib/pull/8159))
This changes `reindex_linear_equiv eₘ eₙ : matrix m m R ≃ₗ[R] matrix n n R` to `reindex_linear_equiv R A eₘ eₙ : matrix m m A ≃ₗ[R] matrix n n A`, which both works for a larger range of types, and eliminates the need for type ascriptions that was previously caused by the implicitness of `R`.
We cannot yet make the same generalization for `reindex_alg_equiv` as the `algebra R (matrix m m A)` structure implied by `algebra R A` is not in mathlib yet.

### [2021-07-05 09:56:32](https://github.com/leanprover-community/mathlib/commit/a8f60eb)
feat(algebra/lie/free): the universal enveloping algebra of the free Lie algebra is the free associative algebra ([#8183](https://github.com/leanprover-community/mathlib/pull/8183))

### [2021-07-04 16:29:14](https://github.com/leanprover-community/mathlib/commit/4ace3b7)
feat(measure_theory/conditional_expectation): define the Lp subspace of functions measurable wrt a sigma-algebra, prove completeness ([#7945](https://github.com/leanprover-community/mathlib/pull/7945))
This is the first step towards defining the conditional expectation:
- in this PR a subspace of L^p is shown to be complete, which is necessary to define an orthogonal projection on that subspace;
- the conditional expectation of functions in L^2 will be the orthogonal projection;
- the definition will be extended to L^1 through simple functions (as is done for the integral definition).

### [2021-07-04 15:19:05](https://github.com/leanprover-community/mathlib/commit/01b062a)
chore(category_theory/abelian/diagram_lemmas/four): Make the diagram into a code block ([#8192](https://github.com/leanprover-community/mathlib/pull/8192))
Currently on mathlib docs, it looks like this
![image](https://user-images.githubusercontent.com/15098580/124386872-4c869d00-dcd4-11eb-9c5c-ce6a29e4e607.png)
Making it into a code block should mean that it will render correctly on mathlib docs

### [2021-07-04 13:54:21](https://github.com/leanprover-community/mathlib/commit/d819e36)
feat(data/finset/basic): sdiff_val, disjoint_to_finset_iff_disjoint ([#8168](https://github.com/leanprover-community/mathlib/pull/8168))

### [2021-07-04 13:20:09](https://github.com/leanprover-community/mathlib/commit/2ebd96c)
doc(measure_theory/measurable_space): correct tiny misprints in two doc-strings ([#8187](https://github.com/leanprover-community/mathlib/pull/8187))
Modifying doc-strings of `measurable_space.comap` and `measurable_space.map`: changing "measure space" to "measurable space" in both.

### [2021-07-04 11:49:30](https://github.com/leanprover-community/mathlib/commit/7135c96)
chore(data/list/perm): make `perm_nil` a simp lemma ([#8191](https://github.com/leanprover-community/mathlib/pull/8191))

### [2021-07-04 09:30:33](https://github.com/leanprover-community/mathlib/commit/a9db7ce)
chore(measure_theory/{bochner_integration, simple_func_dense}): Move construction of embedding of L1 simple funcs ([#8185](https://github.com/leanprover-community/mathlib/pull/8185))
At the moment, there is a low-level construction in `measure_theory/simple_func_dense` for the approximation of an element of L1 by simple functions, and this is generalized to a more abstract version (with a normed space `L1.simple_func` and a dense linear embedding of this into `L1`) in `measure_theory/bochner_integration`.  [#8114](https://github.com/leanprover-community/mathlib/pull/8114) generalized the low-level construction, and I am thinking of rewriting the more abstract version to apply to `Lp`, too.
But since this will all be more generally useful than in the construction of the Bochner integral, and since the Bochner integral file is very long, I propose moving all this material into `measure_theory/simple_func_dense`.  This PR shows what it would look like.  There are no mathematical changes.

### [2021-07-04 09:30:32](https://github.com/leanprover-community/mathlib/commit/180d004)
ci(.github/workflows/*): switch to self-hosted runners ([#8177](https://github.com/leanprover-community/mathlib/pull/8177))
With this PR, mathlib builds on all branches will use the self-hosted runners that have the "pr" tag. One self-hosted runner is reserved for bors staging branch builds and does not have that tag.
The `build_fork` workflow has been added for use by external forks (and other Lean projects which might want to copy mathlib's CI).

### [2021-07-04 07:58:33](https://github.com/leanprover-community/mathlib/commit/863f007)
feat(data/list/basic): map_permutations ([#8188](https://github.com/leanprover-community/mathlib/pull/8188))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/perm.20of.20permutations/near/244821779).

### [2021-07-04 02:26:45](https://github.com/leanprover-community/mathlib/commit/cdb44df)
chore(scripts): update nolints.txt ([#8189](https://github.com/leanprover-community/mathlib/pull/8189))
I am happy to remove some nolints for you!

### [2021-07-03 16:33:31](https://github.com/leanprover-community/mathlib/commit/531d850)
feat(category_theory): left-derived functors ([#7487](https://github.com/leanprover-community/mathlib/pull/7487))
# Left-derived functors
We define the left-derived functors `F.left_derived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.
The definition is
```
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.
We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.
Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.
## Implementation
We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.
It is often convenient, of course, to work with `[abelian C] [enough_projectives C] [abelian D]`
which (assuming the results from `category_theory.abelian.projective`) are enough to
provide all the typeclass hypotheses assumed here.

### [2021-07-03 13:08:36](https://github.com/leanprover-community/mathlib/commit/74a0f67)
refactor(measure_theory/simple_func_dense): generalize approximation results from L^1 to L^p ([#8114](https://github.com/leanprover-community/mathlib/pull/8114))
Simple functions are dense in L^p.  The argument for `1 ≤ p < ∞` is exactly the same as for `p = 1`, which was already in mathlib:  construct a suitable sequence of pointwise approximations and apply the Dominated Convergence Theorem.  This PR refactors to provide the general-`p` result.
The argument for `p = ∞` requires finite-dimensionality of `E` and a different approximating sequence, so is left for another PR.

### [2021-07-03 10:46:49](https://github.com/leanprover-community/mathlib/commit/a022bb7)
feat(algebra/invertible): add a missing lemma `inv_of_eq_left_inv` ([#8179](https://github.com/leanprover-community/mathlib/pull/8179))
add "inv_of_eq_left_inv"

### [2021-07-03 10:46:48](https://github.com/leanprover-community/mathlib/commit/111ac5c)
feat(group_theory/perm/basic): of_subtype_apply_of_mem ([#8174](https://github.com/leanprover-community/mathlib/pull/8174))

### [2021-07-03 10:46:47](https://github.com/leanprover-community/mathlib/commit/25d042c)
feat(algebra/periodic): a few more periodicity lemmas ([#8062](https://github.com/leanprover-community/mathlib/pull/8062))
A few more lemmas about periodic functions that I realized are useful.

### [2021-07-03 09:58:05](https://github.com/leanprover-community/mathlib/commit/915902e)
feat(topology/algebra/multilinear): add a linear_equiv version of pi ([#8064](https://github.com/leanprover-community/mathlib/pull/8064))
This is a weaker version of `continuous_multilinear_map.piₗᵢ` that requires weaker typeclasses.
Unfortunately I don't understand why the typeclass system continues not to cooperate here, but I suspect it's the same class of problem that plagues `dfinsupp`.

### [2021-07-03 03:02:44](https://github.com/leanprover-community/mathlib/commit/edb72b4)
docs(data/real/*): add module docstrings ([#8145](https://github.com/leanprover-community/mathlib/pull/8145))

### [2021-07-02 22:04:07](https://github.com/leanprover-community/mathlib/commit/10f6c2c)
feat(data/real/nnreal): cast_nat_abs_eq_nnabs_cast ([#8121](https://github.com/leanprover-community/mathlib/pull/8121))

### [2021-07-02 20:58:33](https://github.com/leanprover-community/mathlib/commit/f8ca790)
chore(group_theory/congruence): fix docstring ([#8162](https://github.com/leanprover-community/mathlib/pull/8162))
This fixes a docstring which didn't match the code.

### [2021-07-02 20:21:24](https://github.com/leanprover-community/mathlib/commit/f5a8b8a)
fix(topology/continuous_function/basic): fix `continuous_map.id_coe` ([#8180](https://github.com/leanprover-community/mathlib/pull/8180))

### [2021-07-02 19:46:00](https://github.com/leanprover-community/mathlib/commit/9e9dfc2)
feat(category_theory/adjunction/fully_faithful): Converses to `unit_is_iso_of_L_fully_faithful` and `counit_is_iso_of_R_fully_faithful` ([#8181](https://github.com/leanprover-community/mathlib/pull/8181))
Add a converse to `unit_is_iso_of_L_fully_faithful` and to `counit_is_iso_of_R_fully_faithful`

### [2021-07-02 18:29:36](https://github.com/leanprover-community/mathlib/commit/ea924e5)
feat(data/nat/choose/bounds): exponential bounds on binomial coefficients ([#8095](https://github.com/leanprover-community/mathlib/pull/8095))

### [2021-07-02 16:37:34](https://github.com/leanprover-community/mathlib/commit/67c72b4)
feat(data/list/cycle): lift next_prev to cycle ([#8172](https://github.com/leanprover-community/mathlib/pull/8172))

### [2021-07-02 10:55:24](https://github.com/leanprover-community/mathlib/commit/d6a7c3b)
chore(algebra/algebra/basic): add `alg_hom.of_linear_map` and lemmas ([#8151](https://github.com/leanprover-community/mathlib/pull/8151))
This lets me golf `complex.lift` a little

### [2021-07-02 08:19:35](https://github.com/leanprover-community/mathlib/commit/dfc42f9)
feat(data/equiv/basic): swap_apply_ne_self_iff ([#8167](https://github.com/leanprover-community/mathlib/pull/8167))

### [2021-07-02 05:56:27](https://github.com/leanprover-community/mathlib/commit/f5f8a20)
feat(analysis/calculus/fderiv_symmetric): prove that the second derivative is symmetric ([#8104](https://github.com/leanprover-community/mathlib/pull/8104))
We show that, if a function is differentiable over the reals around a point `x`, and is second-differentiable at `x`, then the second derivative is symmetric. In fact, we even prove a stronger statement for functions differentiable within a convex set, to be able to apply it for functions on the half-plane or the quadrant.

### [2021-07-01 21:10:28](https://github.com/leanprover-community/mathlib/commit/92b64a0)
feat(data/list/duplicate): prop that element is a duplicate ([#7824](https://github.com/leanprover-community/mathlib/pull/7824))
As discussed in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nodup.20and.20decidability and [#7587](https://github.com/leanprover-community/mathlib/pull/7587)

### [2021-07-01 19:34:23](https://github.com/leanprover-community/mathlib/commit/5945ca3)
chore(*): update to lean 3.31.0c ([#8122](https://github.com/leanprover-community/mathlib/pull/8122))

### [2021-07-01 18:15:23](https://github.com/leanprover-community/mathlib/commit/395d871)
chore(algebra/lie/free): tidy up after [#8153](https://github.com/leanprover-community/mathlib/pull/8153) ([#8163](https://github.com/leanprover-community/mathlib/pull/8163))
@eric-wieser had some further comments and suggestions which didn't make it into [#8153](https://github.com/leanprover-community/mathlib/pull/8153)

### [2021-07-01 16:37:06](https://github.com/leanprover-community/mathlib/commit/1571290)
feat(logic/is_empty): add some simp lemmas and unique instances ([#7832](https://github.com/leanprover-community/mathlib/pull/7832))
There are a handful of lemmas about `(h : ¬nonempty a)` that if restated in terms of `[is_empty a]` become suitable for `simp` or as `instance`s. This adjusts some of those lemmas.

### [2021-07-01 14:19:24](https://github.com/leanprover-community/mathlib/commit/3d2e5ac)
chore(linear_algebra/matrix/determinant): golf a proof ([#8157](https://github.com/leanprover-community/mathlib/pull/8157))

### [2021-07-01 14:19:23](https://github.com/leanprover-community/mathlib/commit/ca30bd2)
feat(analysis/fourier): span of monomials is dense in C^0 ([#8035](https://github.com/leanprover-community/mathlib/pull/8035))
Prove that the span of the monomials `λ z, z ^ n` is dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

### [2021-07-01 12:58:30](https://github.com/leanprover-community/mathlib/commit/3fa61ea)
feat(algebra/lie/free): construction of free Lie algebras ([#8153](https://github.com/leanprover-community/mathlib/pull/8153))

### [2021-07-01 12:58:29](https://github.com/leanprover-community/mathlib/commit/4d24172)
docs(order/zorn): explain how to use Zorn's lemma ([#8125](https://github.com/leanprover-community/mathlib/pull/8125))

### [2021-07-01 12:58:27](https://github.com/leanprover-community/mathlib/commit/7cbca35)
feat(data/fintype/intervals): fintype instances for set.{Icc,Ioc,Ioo} ([#8123](https://github.com/leanprover-community/mathlib/pull/8123))

### [2021-07-01 11:10:36](https://github.com/leanprover-community/mathlib/commit/6e0d2d3)
feat(logic/basic): add two simp lemmas ([#8148](https://github.com/leanprover-community/mathlib/pull/8148))

### [2021-07-01 07:48:35](https://github.com/leanprover-community/mathlib/commit/8986c4f)
chore(linear_algebra/matrix/determinant): squeeze some simps for speed up ([#8156](https://github.com/leanprover-community/mathlib/pull/8156))
I simply squeezed some simps in `linear_algebra/matrix/determinant` to obtain two much faster proofs.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews)

### [2021-07-01 07:48:34](https://github.com/leanprover-community/mathlib/commit/582ee9e)
feat(logic/basic): subtype.subsingleton ([#8138](https://github.com/leanprover-community/mathlib/pull/8138))

### [2021-07-01 07:48:33](https://github.com/leanprover-community/mathlib/commit/aabb900)
feat(order/preorder_hom): preorder_hom_eq_id ([#8135](https://github.com/leanprover-community/mathlib/pull/8135))
From LTE

### [2021-07-01 07:48:32](https://github.com/leanprover-community/mathlib/commit/4a75876)
feat(category_theory/limits/concrete_category): Some lemmas about limits in concrete categories ([#8130](https://github.com/leanprover-community/mathlib/pull/8130))
Generalizes some lemmas from LTE. 
See zulip discussion [here](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/for_mathlib.2Fwide_pullback/near/244298079).

### [2021-07-01 06:12:12](https://github.com/leanprover-community/mathlib/commit/2df573a)
feat(data/int/basic): int.eq_zero_of_div_eq_zero ([#8134](https://github.com/leanprover-community/mathlib/pull/8134))

### [2021-07-01 02:20:40](https://github.com/leanprover-community/mathlib/commit/b972280)
chore(scripts): update nolints.txt ([#8155](https://github.com/leanprover-community/mathlib/pull/8155))
I am happy to remove some nolints for you!