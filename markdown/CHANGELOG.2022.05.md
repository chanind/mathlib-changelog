### [2022-05-31 22:07:31](https://github.com/leanprover-community/mathlib/commit/bdf3e97)
chore(data/polynomial/laurent): remove unused case distinction ([#14490](https://github.com/leanprover-community/mathlib/pull/14490))

### [2022-05-31 20:07:53](https://github.com/leanprover-community/mathlib/commit/26a62b0)
fix(topology/algebra/module/multilinear): initialize simps projections ([#14495](https://github.com/leanprover-community/mathlib/pull/14495))
* `continuous_multilinear_map.smul_right` has a `simps` attribute, causing the generation of the simps projections for `continuous_multilinear_map`, but without specific support for apply. We now initialize the simps projections correctly.
* This fixes an error in the sphere eversion project

### [2022-05-31 20:07:51](https://github.com/leanprover-community/mathlib/commit/9dc4b8e)
feat(algebra/group_power/basic): `a^2 = b^2 ↔ a = b ∨ a = -b` ([#14431](https://github.com/leanprover-community/mathlib/pull/14431))
Generalize `a ^ 2 = 1 ↔ a = 1 ∨ a = -1` to `ring` + `no_zero_divisors` and prove `a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b` under `comm_ring` + `no_zero_divisors`.

### [2022-05-31 18:03:22](https://github.com/leanprover-community/mathlib/commit/8e522f8)
feat(algebra/order/monoid): Missing `has_exists_mul_of_le` instances ([#14476](https://github.com/leanprover-community/mathlib/pull/14476))
Add a few `has_exists_mul_of_le` instances, generalize `has_exists_mul_of_le` to `has_le` + `has_mul`.

### [2022-05-31 13:49:17](https://github.com/leanprover-community/mathlib/commit/e0b2ad8)
chore(algebra/lie/quotient): golf some instances ([#14480](https://github.com/leanprover-community/mathlib/pull/14480))

### [2022-05-31 13:49:16](https://github.com/leanprover-community/mathlib/commit/806f673)
feat(algebra/star): star_single, star_update ([#14477](https://github.com/leanprover-community/mathlib/pull/14477))

### [2022-05-31 11:57:57](https://github.com/leanprover-community/mathlib/commit/3e79ce4)
chore(combinatorics/simple_graph/basic): remove unnecessary lemma ([#14468](https://github.com/leanprover-community/mathlib/pull/14468))
This lemma was added in [#11371](https://github.com/leanprover-community/mathlib/pull/11371) for the Lean version bump, since the more powerful congr lemmas revealed a bug in fintype instances that were finally corrected in [#14136](https://github.com/leanprover-community/mathlib/pull/14136).

### [2022-05-31 11:57:56](https://github.com/leanprover-community/mathlib/commit/1eb7339)
feat(topology/algebra/group): add `continuous_of_continuous_at_one` ([#14451](https://github.com/leanprover-community/mathlib/pull/14451))
This lemma is more general than
`uniform_continuous_of_continuous_at_one` because it allows the
codomain to be a monoid.

### [2022-05-31 11:57:55](https://github.com/leanprover-community/mathlib/commit/0f3e083)
feat(algebra/algebra/basic): relax typeclass assumptions ([#14415](https://github.com/leanprover-community/mathlib/pull/14415))

### [2022-05-31 11:57:54](https://github.com/leanprover-community/mathlib/commit/346174e)
feat(data/polynomial/laurent): a Laurent polynomial can be multiplied by a power of `X` to "become" a polynomial ([#14106](https://github.com/leanprover-community/mathlib/pull/14106))
This PR proves two versions of the result mentioned in the title, one involving multiplying by a non-negative power of `T`, the other usable as an induction principle.

### [2022-05-31 09:48:05](https://github.com/leanprover-community/mathlib/commit/87fbbd1)
chore(analysis/asymptotics): golf 2 proofs ([#14473](https://github.com/leanprover-community/mathlib/pull/14473))
Don't go back and forth between `∈ l` and `∀ᶠ l`.

### [2022-05-31 09:48:04](https://github.com/leanprover-community/mathlib/commit/9e9cc57)
feat(analysis/asymptotics/asymptotics): add `is_O_const_iff` ([#14472](https://github.com/leanprover-community/mathlib/pull/14472))
* use `f =ᶠ[l] 0` instead of `∀ᶠ x in l, f x = 0` in
  `is_{O_with,O,o}_zero_right_iff`;
* generalize these lemmas from `0` in a `normed_group` to `0` in a `semi_normed_group`;
* add `is_O.is_bounded_under_le`, `is_O_const_of_ne`, and `is_O_const_iff`.

### [2022-05-31 09:48:03](https://github.com/leanprover-community/mathlib/commit/615baba)
feat(order/monotone): prove `nat.exists_strict_mono` etc ([#14435](https://github.com/leanprover-community/mathlib/pull/14435))
* add `nat.exists_strict_mono`, `nat.exists_strict_anti`, `int.exists_strict_mono`, and `int.exists_strict_anti`;
* move `set.Iic.no_min_order` and `set.Ici.no_max_order` to `data.set.intervals.basic`;
* add `set.Iio.no_min_order` and `set.Ioi.no_max_order`;
* add `no_max_order.infinite` and `no_min_order.infinite`, use them in the proofs;
* rename `set.Ixx.infinite` to `set.Ixx_infinite`;
* add `set.Ixx.infinite` - lemmas and instances about `infinite`, not `set.infinite`.

### [2022-05-31 09:48:01](https://github.com/leanprover-community/mathlib/commit/cafeaa3)
feat(data/set/lattice): add lemmas about unions over natural numbers ([#14393](https://github.com/leanprover-community/mathlib/pull/14393))
* Add `Union`/`Inter` versions of lemmas like `supr_ge_eq_supr_nat_add`.
* Make some arguments explicit.

### [2022-05-31 09:48:00](https://github.com/leanprover-community/mathlib/commit/7127048)
feat(data/polynomial/*): `support_binomial` and `support_trinomial` lemmas ([#14385](https://github.com/leanprover-community/mathlib/pull/14385))
This PR adds lemmas for the support of binomials and trinomials. The trinomial lemmas will be helpful for irreducibility of x^n-x-1.

### [2022-05-31 09:47:59](https://github.com/leanprover-community/mathlib/commit/8315ad0)
refactor(group_theory/sylow): Move basic API earlier in the file ([#14367](https://github.com/leanprover-community/mathlib/pull/14367))
This PR moves some basic sylow API to earlier in the file, so that it can be used earlier.

### [2022-05-31 09:47:58](https://github.com/leanprover-community/mathlib/commit/111ce5b)
feat(group_theory/subgroup/basic): `comap_le_comap` lemmas ([#14365](https://github.com/leanprover-community/mathlib/pull/14365))
This PR adds some `comap_le_comap` lemmas.

### [2022-05-31 09:47:57](https://github.com/leanprover-community/mathlib/commit/1b49d48)
refactor(group_theory/order_of_element): Remove coercion in `order_eq_card_zpowers` ([#14364](https://github.com/leanprover-community/mathlib/pull/14364))
This PR removes a coercion in `order_eq_card_zpowers`.

### [2022-05-31 09:47:56](https://github.com/leanprover-community/mathlib/commit/6531c72)
chore(algebra/algebra/restrict_scalars): put a right action on restricted scalars ([#13996](https://github.com/leanprover-community/mathlib/pull/13996))
This provides `module Rᵐᵒᵖ (restrict_scalars R S M)` in terms of a `module Sᵐᵒᵖ M` action, by sending `Rᵐᵒᵖ` to `Sᵐᵒᵖ` through `algebra_map R S`.
This means that `restrict_scalars R S M` now works for right-modules and bi-modules in addition to left-modules.
This will become important if we change `algebra R A` to require `A` to be an `R`-bimodule, as otherwise `restrict_scalars R S A` would no longer be an algebra.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313996.20right.20actions.20on.20restrict_scalars/near/282045994)

### [2022-05-31 08:02:43](https://github.com/leanprover-community/mathlib/commit/876cb64)
feat({group,ring}_theory/sub{monoid,group,semiring,ring}): the action by the center is commutative ([#14362](https://github.com/leanprover-community/mathlib/pull/14362))
None of these `smul_comm_class` instances carry data, so they cannot form diamonds.
This action is used to golf the proofs in `quadratic_form.associated`.

### [2022-05-30 23:53:46](https://github.com/leanprover-community/mathlib/commit/6633283)
fix(tactic/norm_num): fix ge unfolding bug ([#14425](https://github.com/leanprover-community/mathlib/pull/14425))
As reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/bug.20in.20norm_num.20handling.20of.20ge.3F).

### [2022-05-30 22:37:30](https://github.com/leanprover-community/mathlib/commit/e7cc0eb)
feat(group_theory/perm/cycle): improve doc and namespace for cauchy's theorem ([#14471](https://github.com/leanprover-community/mathlib/pull/14471))
Fix a few things in the module docstring, remove namespace, add an additive version and add docstrings for Cauchy's theorem.
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Existence.20of.20elements.20of.20order.20p.20in.20a.20group/near/284399583

### [2022-05-30 17:48:15](https://github.com/leanprover-community/mathlib/commit/ba22440)
feat(set_theory/cardinal/cofinality): use `bounded` and `unbounded` ([#14438](https://github.com/leanprover-community/mathlib/pull/14438))
We change `∀ a, ∃ b ∈ s, ¬ r b a` to its def-eq predicate `unbounded r s`, and similarly for `bounded r s`.

### [2022-05-30 17:48:15](https://github.com/leanprover-community/mathlib/commit/1de757e)
feat(data/fin/basic): add `iff`lemmas about `nontrivial`/`subsingleton` ([#14390](https://github.com/leanprover-community/mathlib/pull/14390))

### [2022-05-30 17:10:32](https://github.com/leanprover-community/mathlib/commit/1791ed3)
chore(ring_theory/polynomial/vieta): generalize universe ([#14411](https://github.com/leanprover-community/mathlib/pull/14411))

### [2022-05-30 17:10:31](https://github.com/leanprover-community/mathlib/commit/08c1412)
feat(set_theory/game/pgame): `lt_or_equiv_or_gf` ([#14407](https://github.com/leanprover-community/mathlib/pull/14407))

### [2022-05-30 16:30:46](https://github.com/leanprover-community/mathlib/commit/59a1a50)
chore(analysis/normed_space/pi_Lp): add `pi_Lp.linear_equiv` ([#14380](https://github.com/leanprover-community/mathlib/pull/14380))
This is just a more bundled version of the `pi_Lp.equiv` we already have.
Also adds two missing simp lemmas about `pi_Lp.equiv`.

### [2022-05-30 13:47:58](https://github.com/leanprover-community/mathlib/commit/01af73a)
feat(alegbra/homology/short_exact/abelian.lean): Right split exact sequences + case of modules ([#14376](https://github.com/leanprover-community/mathlib/pull/14376))
A right split short exact sequence in an abelian category is split.
Also, in the case of the Module category, a version fully expressed in terms of modules and linear maps is provided.

### [2022-05-30 12:53:32](https://github.com/leanprover-community/mathlib/commit/3641bf9)
refactor(algebraic_topology/*): use rw instead of erw where possible ([#14320](https://github.com/leanprover-community/mathlib/pull/14320))

### [2022-05-30 11:01:47](https://github.com/leanprover-community/mathlib/commit/af70f8e)
feat(number_theory/bernoulli_polynomials): Added some lemmas ([#14282](https://github.com/leanprover-community/mathlib/pull/14282))
Have added some lemmas regarding rearrangements of sums and evaluations of Bernoulli polynomials.

### [2022-05-30 04:06:04](https://github.com/leanprover-community/mathlib/commit/475f18b)
refactor(analysis/asymptotics): make `is_o`/`is_O` work with `calc` ([#14129](https://github.com/leanprover-community/mathlib/pull/14129))
Reorder arguments of `is_O_with`/`is_O`/`is_o` as well as `trans` lemmas so that they work with `calc`.
Also adds `f =O[l] g` notation.
Fixes [#2273](https://github.com/leanprover-community/mathlib/pull/2273)

### [2022-05-29 17:50:03](https://github.com/leanprover-community/mathlib/commit/55f32da)
feat(topology/vector_bundle): the pullback of a vector bundle is a vector bundle ([#8545](https://github.com/leanprover-community/mathlib/pull/8545))
We construct the pullback bundle of a vector bundle.
* Co-authored by: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
* Co-authored by: Floris van Doorn <fpvdoorn@gmail.com>
* Co-authored by: Sebastien Gouezel <sebastien.gouezel@univ-rennes1.fr>

### [2022-05-29 15:46:51](https://github.com/leanprover-community/mathlib/commit/938eeeb)
feat(algebra/group/with_one): add a recursor and a `no_zero_divisors` instance ([#14434](https://github.com/leanprover-community/mathlib/pull/14434))

### [2022-05-29 13:40:03](https://github.com/leanprover-community/mathlib/commit/b673ed8)
feat(analysis/normed_space): Geometric Hahn Banach theorems ([#7288](https://github.com/leanprover-community/mathlib/pull/7288))
This proves a range of variants of the Hahn-Banach separation theorems.

### [2022-05-29 11:50:46](https://github.com/leanprover-community/mathlib/commit/98b7637)
feat(category_theory/limits): monos have images ([#14186](https://github.com/leanprover-community/mathlib/pull/14186))
Turning on an instance for `has_image` for any monomorphism.

### [2022-05-29 11:13:23](https://github.com/leanprover-community/mathlib/commit/8d13a2d)
feat(algebra/order/rearrangement): Equality case of the Rearrangement Inequality ([#13245](https://github.com/leanprover-community/mathlib/pull/13245))
This PR deduces the cases of equality and strict inequality of the Rearrangement Inequality as a corollary to the existing statement of the rearrangement inequality.

### [2022-05-29 09:04:36](https://github.com/leanprover-community/mathlib/commit/6b936a9)
feat(data/set/basic): simp-normal form for `↥{x | p x}` ([#14441](https://github.com/leanprover-community/mathlib/pull/14441))
We make `{x // p x}` the simp-normal form for `↥{x | p x}`. We also rewrite some lemmas to use the former instead of the latter.

### [2022-05-29 01:31:29](https://github.com/leanprover-community/mathlib/commit/3e58d9c)
feat(data/nat/enat): `is_well_order` instance for `enat` ([#14416](https://github.com/leanprover-community/mathlib/pull/14416))

### [2022-05-28 20:10:48](https://github.com/leanprover-community/mathlib/commit/ad2baee)
feat(topology/separation): `t0_space` and `t1_space` for `α × β` and `Π i, α i` ([#14418](https://github.com/leanprover-community/mathlib/pull/14418))

### [2022-05-28 17:52:57](https://github.com/leanprover-community/mathlib/commit/f13e5df)
refactor(set_theory/*) rename `wf` lemmas to `lt_wf` ([#14417](https://github.com/leanprover-community/mathlib/pull/14417))
This is done for consistency with the rest of `mathlib` (`nat.lt_wf`, `enat.lt_wf`, `finset.lt_wf`, ...)

### [2022-05-28 17:52:56](https://github.com/leanprover-community/mathlib/commit/762fc15)
feat(set_theory/ordinal/arithmetic): Add missing instances for `ordinal` ([#14128](https://github.com/leanprover-community/mathlib/pull/14128))
We add the following instances:
- `monoid_with_zero ordinal`
- `no_zero_divisors ordinal`
- `is_left_distrib_class ordinal`
- `contravariant_class ordinal ordinal (swap (+)) (<)`
- `is_antisymm ordinal (∣)`

### [2022-05-28 17:52:55](https://github.com/leanprover-community/mathlib/commit/3280d00)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_class` `partial_order`, remove primes ([#14060](https://github.com/leanprover-community/mathlib/pull/14060))

### [2022-05-28 15:49:21](https://github.com/leanprover-community/mathlib/commit/1e46532)
feat(measure_theory/integral/lebesgue): `lintegral_add` holds if 1 function is measurable ([#14278](https://github.com/leanprover-community/mathlib/pull/14278))
* for any function `f` there exists a measurable function `g ≤ f` with the same Lebesgue integral;
* prove `∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ` assuming **one** of the functions is (a.e.-)measurable; split `lintegral_add` into two lemmas `lintegral_add_(left|right)`;
* prove `∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ` for any `f`, `g`;
* prove a version of Markov's inequality for `μ {x | f x + ε ≤ g x}` with possibly non-measurable `f`;
* prove `f ≤ᵐ[μ] g → ∫⁻ x, f x ∂μ ≠ ∞ → ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ → f =ᵐ[μ] g` for an a.e.-measurable function `f`;
* drop one measurability assumption in `lintegral_sub` and `lintegral_sub_le`;
* add `lintegral_strict_mono_of_ae_le_of_frequently_ae_lt`, a version of `lintegral_strict_mono_of_ae_le_of_ae_lt_on`;
* drop one measurability assumption in `lintegral_strict_mono_of_ae_le_of_ae_lt_on`, `lintegral_strict_mono`, and `set_lintegral_strict_mono`;
* prove `with_density_add` assuming measurability of one of the functions; replace it with `with_density_add_(left|right)`;
* drop measurability assumptions here and there in `mean_inequalities`.

### [2022-05-28 15:49:19](https://github.com/leanprover-community/mathlib/commit/249f107)
feat(algebra/order/monoid_lemmas): remove duplicates, add missing lemmas, fix inconsistencies ([#13494](https://github.com/leanprover-community/mathlib/pull/13494))
Changes in the order:
`mul_lt_mul'''` has asymmetric typeclass assumptions. So I did the following 3 changes.
Rename `mul_lt_mul'''` to `left.mul_lt_mul`
Make an alias `mul_lt_mul'''` of `mul_lt_mul_of_lt_of_lt`
Add `right.mul_lt_mul`
Move `le_mul_of_one_le_left'` and `mul_le_of_le_one_left'` together with similar lemmas.
Move `lt_mul_of_one_lt_left'` together with similar lemmas.
Add `mul_lt_of_lt_one_right'` and `mul_lt_of_lt_one_left'`. These are analogs of other lemmas.
Following are changes of lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`, `b ≤ c → 1 ≤ a → b ≤ c * a`, `a ≤ 1 → b ≤ c → a * b ≤ c` and `1 ≤ a → b ≤ c → b ≤ a * c`. With the following changes, these 4 sections will be very similar.
For `b ≤ c → a ≤ 1 → b * a ≤ c`:
Remove `alias mul_le_of_le_of_le_one ← mul_le_one'`. This naming is not consistent with `left.mul_lt_one`.
Add `mul_lt_of_lt_of_lt_one'`.
Add `left.mul_le_one`.
Add `left.mul_lt_one_of_le_of_lt`.
Add `left.mul_lt_one_of_lt_of_le`.
Add `left.mul_lt_one'`.
For `b ≤ c → 1 ≤ a → b ≤ c * a`:
Rename `le_mul_of_le_of_le_one` to `le_mul_of_le_of_one_le`.
Remove `lt_mul_of_lt_of_one_le'`. It's exactly the same as `lt_mul_of_lt_of_one_le`.
Rename `one_le_mul_right` to `left.one_le_mul`.
Rename `one_le_mul` to `left.one_le_mul`.
Rename `one_lt_mul_of_lt_of_le'` to `left.one_lt_mul_of_lt_of_le'`.
Add `left.one_lt_mul`.
Rename `one_lt_mul'` to `left.one_lt_mul'`.
For `a ≤ 1 → b ≤ c → a * b ≤ c`:
Add `mul_lt_of_lt_one_of_lt'`.
Add `right.mul_le_one`.
Add `right.mul_lt_one_of_lt_of_le`.
Add `right.mul_lt_one'`.
For `1 ≤ a → b ≤ c → b ≤ a * c`:
Rename `lt_mul_of_one_lt_of_lt` to `lt_mul_of_one_lt_of_lt'`.
Add `lt_mul_of_one_lt_of_lt`.
Add `right.one_lt_mul_of_lt_of_le`.
Rename `one_lt_mul_of_le_of_lt'` to `right.one_lt_mul_of_le_of_lt`.
Add `right.one_lt_mul'`.
Then create aliases for all `left` lemmas in these 4 sections.
Rename `mul_eq_mul_iff_eq_and_eq` to `left.mul_eq_mul_iff_eq_and_eq`.
Add `right.mul_eq_mul_iff_eq_and_eq`.
Make an alias `mul_eq_mul_iff_eq_and_eq` of `left.mul_eq_mul_iff_eq_and_eq`.
Same for additive version.
However, the implicit parameter inconsistency has not been resolved. It affects too many files.

### [2022-05-28 13:51:33](https://github.com/leanprover-community/mathlib/commit/2ce8482)
feat(computability/regular_expressions): add power operator ([#14261](https://github.com/leanprover-community/mathlib/pull/14261))
We can't make `regular_expression` a monoid, but we can put a power operator on it that's compatible with the power operator on languages.

### [2022-05-28 13:51:32](https://github.com/leanprover-community/mathlib/commit/8a0e712)
feat(category_theory/monoidal/discrete): simps ([#14259](https://github.com/leanprover-community/mathlib/pull/14259))
This is a minuscule change, but it appears to work both on `master` and in the [shift functor refactor](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/trouble.20in.20.60shift_functor.60.20land) I'm aspiring towards, so I'm shipping it off for CI.

### [2022-05-28 13:51:31](https://github.com/leanprover-community/mathlib/commit/dcd5ebd)
feat({data/{finset,set},order/filter}/pointwise): More lemmas ([#14216](https://github.com/leanprover-community/mathlib/pull/14216))
Lemmas about `s ^ n`, `0 * s` and `1 ∈ s / t`.
Other changes:
* `finset.mul_card_le` → `finset.card_mul_le`
* `finset.card_image_eq_iff_inj_on` → `finset.card_image_iff`.
* `zero_smul_subset` → `zero_smul_set_subset`
* Reorder lemmas slightly
* Add an explicit argument to `finset.coe_smul_finset`
* Remove an explicit argument to `set.empty`

### [2022-05-28 11:42:59](https://github.com/leanprover-community/mathlib/commit/15fe782)
doc(set_theory/lists): fix typo ([#14427](https://github.com/leanprover-community/mathlib/pull/14427))

### [2022-05-28 11:42:58](https://github.com/leanprover-community/mathlib/commit/d0efbcb)
feat(model_theory/elementary_maps): Elementary maps respect all (bounded) formulas ([#14252](https://github.com/leanprover-community/mathlib/pull/14252))
Generalizes `elementary_embedding.map_formula` to more classes of formula.

### [2022-05-28 11:42:57](https://github.com/leanprover-community/mathlib/commit/599240f)
refactor(order/bounds): general cleanup ([#14127](https://github.com/leanprover-community/mathlib/pull/14127))
Apart from golfing, this PR does the following:
Add the following theorems (which are immediate from the non-self counterparts):
- `monotone_on.mem_upper_bounds_image_self`
- `monotone_on.mem_lower_bounds_image_self`
- `antitone_on.mem_upper_bounds_image_self`
- `antitone_on.mem_lower_bounds_image_self`
Remove the following theorems (as they're just `mem_X_bounds_image` under unnecessarily stronger assumptions):
- `monotone_on.is_lub_image_le`
- `monotone_on.le_is_glb_image`
- `antitone_on.is_lub_image_le`
- `antitone_on.le_is_glb_image`
- `monotone.is_lub_image_le`
- `monotone.le_is_glb_image`
- `antitone.is_lub_image_le`
- `antitone.le_is_glb_image`
Remove a redundant argument `s ⊆ t` from the following (the old theorems follow immediately from the new ones and `monotone_on.mono`):
- `monotone_on.map_is_greatest`
- `monotone_on.map_is_least`
- `antitone_on.map_is_greatest`
- `antitone_on.map_is_least`

### [2022-05-28 10:25:26](https://github.com/leanprover-community/mathlib/commit/bb90598)
feat(set_theory/ordinal/basic): Turn various lemmas into `simp` ([#14075](https://github.com/leanprover-community/mathlib/pull/14075))

### [2022-05-28 05:34:51](https://github.com/leanprover-community/mathlib/commit/dccab1c)
feat(algebra/ring/basic): Generalize theorems on distributivity ([#14140](https://github.com/leanprover-community/mathlib/pull/14140))
Many theorems assuming full distributivity only need left or right distributivity. We remedy this by making new `left_distrib_class` and `right_distrib_class` classes.
The main motivation here is to generalize various theorems on ordinals, like [ordinal.mul_add](https://leanprover-community.github.io/mathlib_docs/set_theory/ordinal/arithmetic.html#ordinal.mul_add).

### [2022-05-28 04:03:23](https://github.com/leanprover-community/mathlib/commit/15b7e53)
refactor(set_theory/cardinal/*): `cardinal.succ` → `order.succ` ([#14273](https://github.com/leanprover-community/mathlib/pull/14273))

### [2022-05-28 00:43:54](https://github.com/leanprover-community/mathlib/commit/5eb68b5)
feat(data/polynomial/mirror): `nat_degree` and `nat_trailing_degree` of `p * p.mirror` ([#14397](https://github.com/leanprover-community/mathlib/pull/14397))
This PR adds lemmas for the `nat_degree` and `nat_trailing_degree` of `p * p.mirror`. These lemmas tell you that you can recover `p.nat_degree` and `p.nat_trailing_degree` from `p * p.mirror`, which will be useful for irreducibility of x^n-x-1.

### [2022-05-27 23:26:09](https://github.com/leanprover-community/mathlib/commit/a08d179)
refactor(set_theory/ordinal/*): `ordinal.succ` → `order.succ` ([#14243](https://github.com/leanprover-community/mathlib/pull/14243))
We inline the definition of `ordinal.succ` in the `succ_order` instance. This allows us to comfortably use all of the theorems about `order.succ` to our advantage.

### [2022-05-27 21:20:28](https://github.com/leanprover-community/mathlib/commit/9919539)
feat(category_theory): more API for isomorphisms ([#14420](https://github.com/leanprover-community/mathlib/pull/14420))

### [2022-05-27 21:20:27](https://github.com/leanprover-community/mathlib/commit/533cbf4)
feat(data/int/{cast, char_zero}): relax typeclass assumptions ([#14413](https://github.com/leanprover-community/mathlib/pull/14413))

### [2022-05-27 19:20:34](https://github.com/leanprover-community/mathlib/commit/f598e58)
feat(topology/vector_bundle): do not require topology on the fibers for topological_vector_prebundle ([#14377](https://github.com/leanprover-community/mathlib/pull/14377))
* Separated from branch `vb-hom`

### [2022-05-27 19:20:33](https://github.com/leanprover-community/mathlib/commit/a94ae0c)
feat(data/list/min_max): add le_max_of_le, min_le_of_le  ([#14340](https://github.com/leanprover-community/mathlib/pull/14340))

### [2022-05-27 19:20:32](https://github.com/leanprover-community/mathlib/commit/41ca601)
feat(analysis/convolution): The convolution of two functions ([#13540](https://github.com/leanprover-community/mathlib/pull/13540))
* Define the convolution of two functions.
* Prove that when one of the functions has compact support and is `C^n` and the other function is locally integrable, the convolution is `C^n`.
* Compute the total derivative of the convolution (when one of the functions has compact support).
* Prove that when taking the convolution with functions that "tend to the Dirac delta function", the convolution tends to the original function.
* From the sphere eversion project.

### [2022-05-27 19:20:31](https://github.com/leanprover-community/mathlib/commit/baad002)
feat(analysis/complex/phragmen_lindelof): Phragmen-Lindelöf principle for some shapes ([#13178](https://github.com/leanprover-community/mathlib/pull/13178))
Prove Phragmen-Lindelöf principle
- in a horizontal strip;
- in a vertical strip;
- in a coordinate quadrant;
- in the right half-plane (a few versions).

### [2022-05-27 17:41:19](https://github.com/leanprover-community/mathlib/commit/1ccb7f0)
feat(model_theory/syntax, semantics): Lemmas about relabeling variables ([#14225](https://github.com/leanprover-community/mathlib/pull/14225))
Proves lemmas about relabeling variables in terms and formulas
Defines `first_order.language.bounded_formula.to_formula`, which turns turns all of the extra variables of a `bounded_formula` into free variables.

### [2022-05-27 17:02:33](https://github.com/leanprover-community/mathlib/commit/4b9e57b)
feat(model_theory/satisfiability): Upward Löwenheim–Skolem ([#13982](https://github.com/leanprover-community/mathlib/pull/13982))
`first_order.language.Theory.exists_elementary_embedding_card_eq` proves the Upward Löwenheim–Skolem Theorem: every infinite `L`-structure `M` elementarily embeds into an `L`-structure of a given cardinality if that cardinality is larger than the cardinalities of `L` and `M`.

### [2022-05-27 08:53:16](https://github.com/leanprover-community/mathlib/commit/25f75c4)
chore(filter/pointwise): protect filter.has_involutive_inv ([#14398](https://github.com/leanprover-community/mathlib/pull/14398))

### [2022-05-27 08:04:40](https://github.com/leanprover-community/mathlib/commit/2a9b0f8)
chore(ring_theory/artinian): clarify left/right -ness in doc strings ([#14396](https://github.com/leanprover-community/mathlib/pull/14396))

### [2022-05-27 05:12:29](https://github.com/leanprover-community/mathlib/commit/841aef2)
feat(algebraic_topology): the nerve of a category ([#14304](https://github.com/leanprover-community/mathlib/pull/14304))

### [2022-05-27 04:25:55](https://github.com/leanprover-community/mathlib/commit/bae0229)
feat(category_theory/monoidal/subcategory): full monoidal subcategories ([#14311](https://github.com/leanprover-community/mathlib/pull/14311))
We use a type synonym for `{X : C // P X}` when `C` is a monoidal category and the property `P` is closed under the monoidal unit and tensor product so that `full_monoidal_subcategory` can be made an instance.

### [2022-05-27 02:02:29](https://github.com/leanprover-community/mathlib/commit/48d831a)
feat(order/bounded_order): define `with_bot.map` and `with_top.map` ([#14163](https://github.com/leanprover-community/mathlib/pull/14163))
Also define `monotone.with_bot` etc.

### [2022-05-26 22:13:11](https://github.com/leanprover-community/mathlib/commit/8dd4619)
feat(combinatorics/simple_graph/connectivity): deleting edges outside a walk ([#14110](https://github.com/leanprover-community/mathlib/pull/14110))

### [2022-05-26 20:25:47](https://github.com/leanprover-community/mathlib/commit/27791f9)
feat(data/real/nnreal): add mul csupr/cinfi lemmas ([#13936](https://github.com/leanprover-community/mathlib/pull/13936))

### [2022-05-26 18:17:05](https://github.com/leanprover-community/mathlib/commit/525cc65)
feat(order/rel_classes): Reflexive relation from irreflexive and viceversa ([#13411](https://github.com/leanprover-community/mathlib/pull/13411))

### [2022-05-26 15:16:47](https://github.com/leanprover-community/mathlib/commit/b2973b1)
feat(logic/function/basic): add `function.const_injective` ([#14388](https://github.com/leanprover-community/mathlib/pull/14388))
Add `function.const_injective` and `function.const_inj`.

### [2022-05-26 15:16:46](https://github.com/leanprover-community/mathlib/commit/d3b155b)
chore(data/stream/defs): add spaces around infix operators ([#14386](https://github.com/leanprover-community/mathlib/pull/14386))

### [2022-05-26 15:16:44](https://github.com/leanprover-community/mathlib/commit/034cf66)
chore(set_theory/ordinal/topology): add `variables` block ([#14369](https://github.com/leanprover-community/mathlib/pull/14369))
We rename a bunch of variables, but don't fundamentally change any proof.

### [2022-05-26 15:16:39](https://github.com/leanprover-community/mathlib/commit/be34b95)
feat(topology/separation): split some proofs ([#14337](https://github.com/leanprover-community/mathlib/pull/14337))

### [2022-05-26 13:56:36](https://github.com/leanprover-community/mathlib/commit/70e784d)
feat(data/polynomial/*): `(p * q).trailing_degree = p.trailing_degree + q.trailing_degree` ([#14384](https://github.com/leanprover-community/mathlib/pull/14384))
We already had a `nat_trailing_degree_mul` lemma, but this PR does things properly, following the analogous results for `degree`. In particular, we now have some useful intermediate results that do not assume `no_zero_divisors`.

### [2022-05-26 11:04:30](https://github.com/leanprover-community/mathlib/commit/5aeafaa)
feat(algebra/order/monoid): add `le_iff_exists_mul'` ([#14387](https://github.com/leanprover-community/mathlib/pull/14387))
Add a version of `le_iff_exists_mul'`/`le_iff_exists_add'`, versions of `le_iff_exists_mul`/`le_iff_exists_add` with multiplication on the other side.

### [2022-05-26 09:28:23](https://github.com/leanprover-community/mathlib/commit/acd0509)
feat(order/succ_pred/interval_succ): new file ([#14294](https://github.com/leanprover-community/mathlib/pull/14294))
Add 2 lemmas about `set.Ioc (f x) (f (order.succ x))`, where `f` is a
monotone function.

### [2022-05-26 05:56:29](https://github.com/leanprover-community/mathlib/commit/4bf1b02)
feat(category_theory/limits): products give pullback squares ([#14327](https://github.com/leanprover-community/mathlib/pull/14327))
Follow-up to [#14220](https://github.com/leanprover-community/mathlib/pull/14220)

### [2022-05-26 02:20:40](https://github.com/leanprover-community/mathlib/commit/634bef9)
feat(topology/continuous_function/stone_weierstrass): generalize the complex Stone-Weierstrass theorem to is_R_or_C fields ([#14374](https://github.com/leanprover-community/mathlib/pull/14374))
This PR generalizes the complex Stone-Weierstrass theorem to hold for an `is_R_or_C` field.

### [2022-05-25 20:40:47](https://github.com/leanprover-community/mathlib/commit/c5b3de8)
refactor(data/polynomial/*): Make `support_C_mul_X_pow` match `support_monomial` ([#14119](https://github.com/leanprover-community/mathlib/pull/14119))
This PR makes `support_C_mul_X_pow` match `support_monomial`.

### [2022-05-25 19:08:50](https://github.com/leanprover-community/mathlib/commit/dc0fadd)
feat(linear_algebra/prod): define the graph of a linear map ([#14266](https://github.com/leanprover-community/mathlib/pull/14266))

### [2022-05-25 19:08:49](https://github.com/leanprover-community/mathlib/commit/fae32b6)
refactor(analysis/normed_space/M_structure): generalize to arbitrary faithful actions ([#14222](https://github.com/leanprover-community/mathlib/pull/14222))
This follows up from a comment in review of [#12173](https://github.com/leanprover-community/mathlib/pull/12173)
The motivation here is to allow `X →L[𝕜] X`, `X →+ X`, and other weaker or stronger endomorphisms to also be used
This also tides up a few proof names and some poorly-rendering LaTeX

### [2022-05-25 17:33:44](https://github.com/leanprover-community/mathlib/commit/189e5d1)
feat(data/polynomial/degree/trailing_degree): The trailing degree of a product is at least the sum of the trailing degrees ([#14253](https://github.com/leanprover-community/mathlib/pull/14253))
This PR adds lemmas for `nat_trailing_degree` analogous to `degree_mul_le` and `nat_degree_mul_le`.

### [2022-05-25 14:21:08](https://github.com/leanprover-community/mathlib/commit/7e1c126)
move(group_theory/perm/cycle/*): A cycle folder ([#14285](https://github.com/leanprover-community/mathlib/pull/14285))
Move:
* `group_theory.perm.cycles` → `group_theory.perm.cycle.basic`
* `group_theory.perm.cycle_type` → `group_theory.perm.cycle.type`
* `group_theory.perm.concrete_cycle` → `group_theory.perm.cycle.concrete`

### [2022-05-25 10:28:06](https://github.com/leanprover-community/mathlib/commit/ba1c3f3)
feat(data/int/log): integer logarithms of linearly ordered fields ([#13913](https://github.com/leanprover-community/mathlib/pull/13913))
Notably, this provides a way to find the position of the most significant digit of a decimal expansion

### [2022-05-25 09:48:16](https://github.com/leanprover-community/mathlib/commit/f8d5c64)
feat(topology/vector_bundle): use trivialization.symm to simplify the product of vector bundles ([#14361](https://github.com/leanprover-community/mathlib/pull/14361))

### [2022-05-25 08:59:21](https://github.com/leanprover-community/mathlib/commit/660918b)
feat(measure_theory/function/conditional_expectation): Conditional expectation of an indicator ([#14058](https://github.com/leanprover-community/mathlib/pull/14058))
The main lemma is this:
```lean
lemma condexp_indicator (hf_int : integrable f μ) (hs : measurable_set[m] s) :
  μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m])
```
We also use it to prove that if two sigma algebras are "equal under an event", then the conditional expectations with respect to those two sigma algebras are equal under the same event.

### [2022-05-25 07:01:43](https://github.com/leanprover-community/mathlib/commit/5da3731)
feat(measure_theory/integral): add formulas for average over an interval ([#14132](https://github.com/leanprover-community/mathlib/pull/14132))

### [2022-05-25 02:04:38](https://github.com/leanprover-community/mathlib/commit/c1e2121)
feat(data/set/finite): set priority for fintype_insert' and document ([#14363](https://github.com/leanprover-community/mathlib/pull/14363))
This follows up with some review comments for [#14136](https://github.com/leanprover-community/mathlib/pull/14136).

### [2022-05-25 00:18:41](https://github.com/leanprover-community/mathlib/commit/f582298)
feat(group_theory/subgroup/basic): `zpowers_eq_bot` ([#14366](https://github.com/leanprover-community/mathlib/pull/14366))
This PR adds a lemma `zpowers_eq_bot`.

### [2022-05-24 19:56:59](https://github.com/leanprover-community/mathlib/commit/ebb5206)
chore(set_theory/surreal/basic): clarify some proofs ([#14356](https://github.com/leanprover-community/mathlib/pull/14356))

### [2022-05-24 19:56:58](https://github.com/leanprover-community/mathlib/commit/cdaa6d2)
refactor(analysis/normed_space/pi_Lp): golf some instances ([#14339](https://github.com/leanprover-community/mathlib/pull/14339))
* drop `pi_Lp.emetric_aux`;
* use `T₀` to get `(e)metric_space` from `pseudo_(e)metric_space`;
* restate `pi_Lp.(anti)lipschitz_with_equiv` with correct `pseudo_emetric_space` instances; while they're defeq, it's better not to leak auxiliary instances unless necessary.

### [2022-05-24 19:02:02](https://github.com/leanprover-community/mathlib/commit/23f30a3)
fix(topology/vector_bundle): squeeze simp, remove non-terminal simp ([#14357](https://github.com/leanprover-community/mathlib/pull/14357))
For some reason I had to mention `trivialization.coe_coe` explicitly, even though it is in `mfld_simps` (maybe because another simp lemma would otherwise apply first?)

### [2022-05-24 16:46:14](https://github.com/leanprover-community/mathlib/commit/88f8de3)
feat(topology/local_homeomorph): define helper definition ([#14360](https://github.com/leanprover-community/mathlib/pull/14360))
* Define `homeomorph.trans_local_homeomorph` and `local_homeomorph.trans_homeomorph`. They are equal to `local_homeomorph.trans`, but with better definitional behavior for `source` and `target`.
* Define similar operations for `local_equiv`.
* Use this to improve the definitional behavior of [`topological_fiber_bundle.trivialization.trans_fiber_homeomorph`](https://leanprover-community.github.io/mathlib_docs/find/topological_fiber_bundle.trivialization.trans_fiber_homeomorph)
* Also use `@[simps]` to generate a couple of extra simp-lemmas.

### [2022-05-24 16:46:12](https://github.com/leanprover-community/mathlib/commit/483b54f)
refactor(logic/equiv/set): open set namespace ([#14355](https://github.com/leanprover-community/mathlib/pull/14355))

### [2022-05-24 16:46:11](https://github.com/leanprover-community/mathlib/commit/ec8587f)
chore(data/list/forall2): fix incorrect docstring ([#14276](https://github.com/leanprover-community/mathlib/pull/14276))
The previous docstring was false, this corrects the definition.

### [2022-05-24 15:53:41](https://github.com/leanprover-community/mathlib/commit/73a6125)
feat(linear_algebra/bilinear_form): generalize scalar instances, fix diamonds ([#14358](https://github.com/leanprover-community/mathlib/pull/14358))
This fixes the zsmul and nsmul diamonds, makes sub definitionally better, and makes the scalar instance apply more generally.
This also adds `linear_map.comp_bilin_form`.
These changes bring the API more in line with `quadratic_form`.

### [2022-05-24 14:54:33](https://github.com/leanprover-community/mathlib/commit/28f7172)
refactor(algebra/direct_sum/basic): use the new polymorphic subobject API   ([#14341](https://github.com/leanprover-community/mathlib/pull/14341))
This doesn't let us deduplicate the lattice lemmas, but does eliminate the duplicate instances and definitions!
This merges:
* `direct_sum.add_submonoid_is_internal`, `direct_sum.add_subgroup_is_internal`, `direct_sum.submodule_is_internal` into `direct_sum.is_internal`
* `direct_sum.add_submonoid_coe`, `direct_sum.add_subgroup_coe` into `direct_sum.coe_add_monoid_hom`
* `direct_sum.add_submonoid_coe_ring_hom`, `direct_sum.add_subgroup_coe_ring_hom` into `direct_sum.coe_ring_hom`
* `add_submonoid.gsemiring`, `add_subgroup.gsemiring`, `submodule.gsemiring` into `set_like.gsemiring`
* `add_submonoid.gcomm_semiring`, `add_subgroup.gcomm_semiring`, `submodule.gcomm_semiring` into `set_like.gcomm_semiring`
Renames
* `direct_sum.submodule_coe` into `direct_sum.coe_linear_map`
* `direct_sum.submodule_coe_alg_hom` into `direct_sum.coe_alg_hom
And adds:
* `set_like.gnon_unital_non_assoc_semiring`, now that it doesn't need to be repeated three times!
A large number of related lemmas are also renamed to match the new definition names.
This was what originally motivated the `set_like` typeclass; thanks to @Vierkantor for doing the subobject follow up I never got around to!

### [2022-05-24 14:17:37](https://github.com/leanprover-community/mathlib/commit/a07493a)
feat(analysis/convolution): the predicate `convolution_exists` ([#13541](https://github.com/leanprover-community/mathlib/pull/13541))
* This PR defines the predicate that a convolution exists.
* This is not that interesting by itself, but it is a preparation for [#13540](https://github.com/leanprover-community/mathlib/pull/13540)
* I'm using the full module doc for the convolution file, even though not everything promised in the module doc is in this PR.
* From the sphere eversion project

### [2022-05-24 12:33:08](https://github.com/leanprover-community/mathlib/commit/dc22d65)
doc(100.yaml): add Law of Large Numbers ([#14353](https://github.com/leanprover-community/mathlib/pull/14353))

### [2022-05-24 12:33:07](https://github.com/leanprover-community/mathlib/commit/9d193c5)
feat(category_theory/comm_sq): functors mapping pullback/pushout squares ([#14351](https://github.com/leanprover-community/mathlib/pull/14351))
```
lemma map_is_pullback [preserves_limit (cospan h i) F] (s : is_pullback f g h i) :
  is_pullback (F.map f) (F.map g) (F.map h) (F.map i) := ...
```

### [2022-05-24 12:33:06](https://github.com/leanprover-community/mathlib/commit/53a70a0)
feat(linear_algebra/tensor_power): Add notation for tensor powers, and a definition of multiplication ([#14196](https://github.com/leanprover-community/mathlib/pull/14196))
This file introduces the notation `⨂[R]^n M` for `tensor_power R n M`, which in turn is an
abbreviation for `⨂[R] i : fin n, M`.
The proof that this multiplication forms a semiring will come in a later PR ([#10255](https://github.com/leanprover-community/mathlib/pull/10255)).

### [2022-05-24 12:33:05](https://github.com/leanprover-community/mathlib/commit/8e3deff)
feat(representation_theory/invariants): average_map is a projection onto the subspace of invariants ([#14167](https://github.com/leanprover-community/mathlib/pull/14167))

### [2022-05-24 10:24:08](https://github.com/leanprover-community/mathlib/commit/893f480)
feat(group_theory/index): Lemmas for when `relindex` divides `index` ([#14314](https://github.com/leanprover-community/mathlib/pull/14314))
This PR adds two lemmas for when `relindex` divides `index`.

### [2022-05-24 10:24:07](https://github.com/leanprover-community/mathlib/commit/65f1f8e)
feat(linear_algebra/quadratic_form/isometry): extract from `linear_algebra/quadratic_form/basic` ([#14305](https://github.com/leanprover-community/mathlib/pull/14305))
150 lines seems worthy of its own file, especially if this grows `fun_like` boilerplate in future.
No lemmas have been renamed or proofs changed.

### [2022-05-24 10:24:06](https://github.com/leanprover-community/mathlib/commit/9870d13)
chore(order/bounded_order): Golf `disjoint` API ([#14194](https://github.com/leanprover-community/mathlib/pull/14194))
Reorder lemmas and golf.
Lemma additions:
* `disjoint.eq_bot_of_ge`
* `is_compl.of_dual`
* `is_compl_to_dual_iff`
* `is_compl_of_dual_iff`
Lemma deletions:
* `eq_bot_of_disjoint_absorbs`: This is an unhelpful combination of `disjoint.eq_bot_of_ge` and `sup_eq_left`
* `inf_eq_bot_iff_le_compl`: This is a worse version of `is_compl.disjoint_left_iff`
Lemma renames:
* `is_compl.to_order_dual` → `is_compl.dual`

### [2022-05-24 08:19:34](https://github.com/leanprover-community/mathlib/commit/533c67b)
feat(analysis/sum_integral_comparisons): Comparison lemmas between finite sums and integrals ([#13179](https://github.com/leanprover-community/mathlib/pull/13179))
In this pull request we target the following lemmas:
```lean
lemma antitone_on.integral_le_sum {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
   (hf : antitone_on f (Icc x₀ (x₀ + a))) :
   ∫ x in x₀..(x₀ + a), f x ≤ ∑ i in finset.range a, f (x₀ + i)
lemma antitone_on.sum_le_integral
   {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
   (hf : antitone_on f (Icc x₀ (x₀ + a))) :
   ∑ i in finset.range a, f (x₀ + i + 1) ≤ ∫ x in x₀..(x₀ + a), f x :=
```
as well as their `monotone_on` equivalents.
These lemmas are critical to many analytic facts, specifically because it so often is the way that error terms end up getting computed.

### [2022-05-24 07:08:08](https://github.com/leanprover-community/mathlib/commit/93df724)
feat(measure_theory/integral/integral_eq_improper): Covering finite intervals by finite intervals ([#13514](https://github.com/leanprover-community/mathlib/pull/13514))
Currently, the ability to prove facts about improper integrals only allows for at least one infinite endpoint. However, it is a common need to work with functions that blow up at an end point (e.g., x^r on [0, 1] for r in (-1, 0)). As a step toward allowing that, we introduce `ae_cover`s that allow exhausting finite intervals by finite intervals.
Partially addresses: [#12666](https://github.com/leanprover-community/mathlib/pull/12666)

### [2022-05-24 06:28:33](https://github.com/leanprover-community/mathlib/commit/0973ad4)
feat(probability/strong_law): the strong law of large numbers ([#13690](https://github.com/leanprover-community/mathlib/pull/13690))
We prove the almost sure version of the strong law of large numbers: given an iid sequence of integrable random variables `X_i`, then `(\sum_{i < n} X_i)/n` converges almost surely to `E(X)`. We follow Etemadi's proof, which only requires pairwise independence instead of full independence.

### [2022-05-24 05:19:10](https://github.com/leanprover-community/mathlib/commit/0d14ee8)
feat(field_theory/finite/galois_field): Finite fields are Galois ([#14290](https://github.com/leanprover-community/mathlib/pull/14290))
This PR also generalizes a section of `field_theory/finite/basic` from `[char_p K p]` to `[algebra (zmod p) K]`. This is indeed a generalization, due to the presence of the instance `zmod.algebra`.

### [2022-05-24 03:06:12](https://github.com/leanprover-community/mathlib/commit/179ae9e)
feat(category_theory/preadditive): hom orthogonal families ([#13871](https://github.com/leanprover-community/mathlib/pull/13871))
A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.
We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.
When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.
If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
lemma hom_orthogonal.equiv_of_iso (o : hom_orthogonal s) {f : α → ι} {g : β → ι}
  (i : ⨁ (λ a, s (f a)) ≅ ⨁ (λ b, s (g b))) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```
This is preliminary to defining semisimple categories.

### [2022-05-24 01:48:51](https://github.com/leanprover-community/mathlib/commit/c340170)
chore(set_theory/ordinal/*): improve autogenerated instance names for `o.out.α` ([#14342](https://github.com/leanprover-community/mathlib/pull/14342))

### [2022-05-24 00:02:28](https://github.com/leanprover-community/mathlib/commit/10f415a)
feat(set_theory/game/basic): mul_cases lemmas ([#14343](https://github.com/leanprover-community/mathlib/pull/14343))
These are the multiplicative analogs for `{left/right}_moves_add_cases`.

### [2022-05-23 23:25:06](https://github.com/leanprover-community/mathlib/commit/dc36333)
feat(set_theory/surreal/basic): ordinals are numeric ([#14325](https://github.com/leanprover-community/mathlib/pull/14325))

### [2022-05-23 22:05:46](https://github.com/leanprover-community/mathlib/commit/59ef070)
feat(ring_theory/unique_factorization_domain): misc lemmas on factors ([#14333](https://github.com/leanprover-community/mathlib/pull/14333))
Two little lemmas on the set of factors which I needed for [#12287](https://github.com/leanprover-community/mathlib/pull/12287).

### [2022-05-23 20:34:27](https://github.com/leanprover-community/mathlib/commit/3f0a2bb)
feat(set_theory/cardinal/basic): Inline instances ([#14130](https://github.com/leanprover-community/mathlib/pull/14130))
We inline some instances, thus avoiding redundant lemmas. We also clean up the code somewhat.

### [2022-05-23 17:51:44](https://github.com/leanprover-community/mathlib/commit/b3ff79a)
feat(topology/uniform_space/uniform_convergence): Uniform Cauchy sequences ([#14003](https://github.com/leanprover-community/mathlib/pull/14003))
A sequence of functions `f_n` is pointwise Cauchy if `∀x ∀ε ∃N ∀(m, n) > N` we have `|f_m x - f_n x| < ε`. A sequence of functions is _uniformly_ Cauchy if `∀ε ∃N ∀(m, n) > N ∀x` we have `|f_m x - f_n x| < ε`.
As a sequence of functions is pointwise Cauchy if (and when the underlying space is complete, only if) the sequence converges, a sequence of functions is uniformly Cauchy if (and when the underlying space is complete, only if) the sequence uniformly converges. (Note that the parenthetical is not directly covered by this commit, but is an easy consequence of two of its lemmas.)
This notion is commonly used to bootstrap convergence into uniform convergence.

### [2022-05-23 16:11:41](https://github.com/leanprover-community/mathlib/commit/dab06b6)
refactor(topology/sequences): rename some `sequential_` to `seq_` ([#14318](https://github.com/leanprover-community/mathlib/pull/14318))
## Rename
* `sequential_closure` → `seq_closure`, similarly rename lemmas;
* `sequentially_continuous` → `seq_continuous`, similarly rename lemmas;
* `is_seq_closed_of_is_closed` → `is_closed.is_seq_closed`;
* `mem_of_is_seq_closed` → `is_seq_closed.mem_of_tendsto`;
* `continuous.to_sequentially_continuous` → `continuous.seq_continuous`;
## Remove
* `mem_of_is_closed_sequential`: was a weaker version of `is_closed.mem_of_tendsto`;
## Add
* `is_seq_closed.is_closed`;
* `seq_continuous.continuous`;

### [2022-05-23 16:11:40](https://github.com/leanprover-community/mathlib/commit/bbf5776)
feat(group_theory/sylow): The number of sylow subgroups is indivisible by p ([#14313](https://github.com/leanprover-community/mathlib/pull/14313))
A corollary of Sylow's third theorem is that the number of sylow subgroups is indivisible by p.

### [2022-05-23 16:11:39](https://github.com/leanprover-community/mathlib/commit/7a6d850)
feat(probability/stopping): measurability of comparisons of stopping times ([#14061](https://github.com/leanprover-community/mathlib/pull/14061))
Among other related results, prove that `{x | τ x ≤ π x}` is measurable with respect to the sigma algebras generated by each of the two stopping times involved.

### [2022-05-23 14:09:34](https://github.com/leanprover-community/mathlib/commit/8df8968)
feat(data/set/function): add `monotone_on.monotone` etc ([#14301](https://github.com/leanprover-community/mathlib/pull/14301))

### [2022-05-23 14:09:33](https://github.com/leanprover-community/mathlib/commit/33262e0)
feat(ring_theory/power_series): Added lemmas regarding rescale ([#14283](https://github.com/leanprover-community/mathlib/pull/14283))
Added lemmas `rescale_mk`, `rescale_mul` and `rescale_rescale`.

### [2022-05-23 14:09:32](https://github.com/leanprover-community/mathlib/commit/15e8bc4)
feat(topology/vector_bundle): define pretrivialization.symm ([#14192](https://github.com/leanprover-community/mathlib/pull/14192))
* Also adds some other useful lemmas about (pre)trivializations
* This splits out the part of [#8545](https://github.com/leanprover-community/mathlib/pull/8545) that is unrelated to pullbacks
- Co-authored by Nicolo Cavalleri <nico@cavalleri.net>

### [2022-05-23 12:13:01](https://github.com/leanprover-community/mathlib/commit/2b35fc7)
refactor(data/set/finite): reorganize and put emphasis on fintype instances ([#14136](https://github.com/leanprover-community/mathlib/pull/14136))
I went through `data/set/finite` and reorganized it by rough topic (and moved some lemmas to their proper homes; closes [#11177](https://github.com/leanprover-community/mathlib/pull/11177)). Two important parts of this module are (1) `fintype` instances for various set constructions and (2) ways to create `set.finite` terms. This change puts the module closer to following a design where the `set.finite` terms are created in a formulaic way from the `fintype` instances. One tool for this is a `set.finite_of_fintype` constructor, which lets typeclass inference do most of the work.
Included in this commit is changing `set.infinite` to be protected so that it does not conflict with `infinite`.

### [2022-05-23 10:20:39](https://github.com/leanprover-community/mathlib/commit/34e450b)
chore(linear_algebra/quadratic_form/basic): Reorder lemmas ([#14326](https://github.com/leanprover-community/mathlib/pull/14326))
This moves the `fun_like` lemmas up to the top of the file next to the `coe_to_fun` instance, and condenses some sections containing only one lemma.

### [2022-05-23 10:20:38](https://github.com/leanprover-community/mathlib/commit/275dd0f)
feat(algebra/ne_zero): add helper methods ([#14286](https://github.com/leanprover-community/mathlib/pull/14286))
Also golfs the inspiration for one of these, and cleans up some code around the area.

### [2022-05-23 10:20:35](https://github.com/leanprover-community/mathlib/commit/15f49ae)
feat(linear_algebra/tensor_algebra/basic): add `tensor_algebra.tprod` ([#14197](https://github.com/leanprover-community/mathlib/pull/14197))
This is related to `exterior_power.ι_multi`.
Note the new import caused a proof to time out, so I squeezed the simps into term mode.

### [2022-05-23 09:19:36](https://github.com/leanprover-community/mathlib/commit/9288a2d)
feat(linear_algebra/affine_space/affine_equiv): extra lemmas and docstrings ([#14319](https://github.com/leanprover-community/mathlib/pull/14319))
I was struggling to find this definition, so added some more lemmas and a docstring.

### [2022-05-23 08:30:52](https://github.com/leanprover-community/mathlib/commit/aa6dc57)
chore(measure_theory/function/l1_space): drop `integrable.sub'` ([#14309](https://github.com/leanprover-community/mathlib/pull/14309))
It used to have weaker TC assumptions than `integrable.sub` but now it's just a weaker version of it.

### [2022-05-23 07:50:19](https://github.com/leanprover-community/mathlib/commit/2962eab)
feat(linear_algebra/trace): trace of transpose map ([#13897](https://github.com/leanprover-community/mathlib/pull/13897))

### [2022-05-23 06:53:49](https://github.com/leanprover-community/mathlib/commit/b5128b8)
feat(category_theory/limits): pullback squares ([#14220](https://github.com/leanprover-community/mathlib/pull/14220))
Per [zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/pushout.20of.20biprod.2Efst.20and.20biprod.2Esnd.20is.20zero).

### [2022-05-23 04:06:58](https://github.com/leanprover-community/mathlib/commit/94644b7)
chore(scripts): update nolints.txt ([#14321](https://github.com/leanprover-community/mathlib/pull/14321))
I am happy to remove some nolints for you!

### [2022-05-23 01:49:47](https://github.com/leanprover-community/mathlib/commit/542d06a)
feat(measure_theory): use `pseudo_metrizable_space` instead of `metrizable_space` ([#14310](https://github.com/leanprover-community/mathlib/pull/14310))

### [2022-05-23 01:49:46](https://github.com/leanprover-community/mathlib/commit/c100004)
refactor(category_theory/shift_functor): improve defeq of inverse ([#14300](https://github.com/leanprover-community/mathlib/pull/14300))

### [2022-05-23 01:49:45](https://github.com/leanprover-community/mathlib/commit/56de25e)
chore(topology/separation): golf some proofs ([#14279](https://github.com/leanprover-community/mathlib/pull/14279))
* extract `minimal_nonempty_closed_eq_singleton` out of the proof of
  `is_closed.exists_closed_singleton`;
* replace `exists_open_singleton_of_open_finset` with
  `exists_open_singleton_of_open_finite`, extract
  `minimal_nonempty_open_eq_singleton` out of its proof.
* add `exists_is_open_xor_mem`, an alias for `t0_space.t0`.

### [2022-05-23 01:49:44](https://github.com/leanprover-community/mathlib/commit/01eda9a)
feat(topology/instances/ennreal): golf, add lemmas about `supr_add_supr` ([#14274](https://github.com/leanprover-community/mathlib/pull/14274))
* add `ennreal.bsupr_add'` etc that deal with
  `{ι : Sort*} {p : ι → Prop}` instead of `{ι : Type*} {s : set ι}`;
* golf some proofs by reusing more powerful generic lemmas;
* add `ennreal.supr_add_supr_le`, `ennreal.bsupr_add_bsupr_le`,
  and `ennreal.bsupr_add_bsupr_le'`.

### [2022-05-23 01:49:43](https://github.com/leanprover-community/mathlib/commit/9861db0)
feat(logic/hydra): termination of a hydra game ([#14190](https://github.com/leanprover-community/mathlib/pull/14190))
+ The added file logic/hydra.lean deals with the following version of the hydra game: each head of the hydra is labelled by an element in a type `α`, and when you cut off one head with label `a`, it grows back an arbitrary but finite number of heads, all labelled by elements smaller than `a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in what order) you choose cut off the heads, the game always terminates, i.e. all heads will eventually be cut off. The proof follows https://mathoverflow.net/a/229084/3332, and the notion of `fibration` and the `game_add` relation on the product of two types arise in the proof.
+ The results is used to show the well-foundedness of the intricate induction used to show that multiplication of games is well-defined on surreals, see [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Well-founded.20recursion.20for.20pgames/near/282379832).
+ One lemma `add_singleton_eq_iff` is added to data/multiset/basic.
+ `acc.trans_gen` is added, closing [a comment](https://github.com/leanprover-community/lean/pull/713/files#r867394835) at lean[#713](https://github.com/leanprover-community/mathlib/pull/713).

### [2022-05-23 01:49:42](https://github.com/leanprover-community/mathlib/commit/8304b95)
refactor(algebra/big_operators/*): Generalize to division monoids ([#14189](https://github.com/leanprover-community/mathlib/pull/14189))
Generalize big operators lemmas to `division_comm_monoid`. Rename `comm_group.inv_monoid_hom` to `inv_monoid_hom` because it is not about`comm_group` anymore and we do not use classes as namespaces.

### [2022-05-23 01:49:41](https://github.com/leanprover-community/mathlib/commit/16a5286)
feat(order/atoms): add lemmas ([#14162](https://github.com/leanprover-community/mathlib/pull/14162))

### [2022-05-22 23:41:38](https://github.com/leanprover-community/mathlib/commit/4cdde79)
chore(set_theory/game/ordinal): minor golfing ([#14317](https://github.com/leanprover-community/mathlib/pull/14317))
We open the `pgame` namespace to save a few characters. We also very slightly golf the proof of `to_pgame_le`.

### [2022-05-22 23:41:37](https://github.com/leanprover-community/mathlib/commit/005df45)
feat(topology/metric_space): use weaker TC assumptions ([#14316](https://github.com/leanprover-community/mathlib/pull/14316))
Assume `t0_space` instead of `separated_space` in `metric.of_t0_pseudo_metric_space` and `emetric.of_t0_pseudo_emetric_space` (both definition used to have `t2` in their names).

### [2022-05-22 23:41:36](https://github.com/leanprover-community/mathlib/commit/9e9a2c9)
feat(algebra/ring/basic): add `no_zero_divisors.to_cancel_comm_monoid_with_zero` ([#14302](https://github.com/leanprover-community/mathlib/pull/14302))
This already existed as `is_domain.to_cancel_comm_monoid_with_zero` with overly strong assumptions.

### [2022-05-22 23:41:35](https://github.com/leanprover-community/mathlib/commit/dcb3cb1)
chore(logic/equiv/set): golf definition ([#14284](https://github.com/leanprover-community/mathlib/pull/14284))
I've no idea which name is better; for now, let's at least not implement the same function twice.

### [2022-05-22 23:41:34](https://github.com/leanprover-community/mathlib/commit/60897e3)
refactor(set_theory/game/nim): `0 ≈ nim 0` → `nim 0 ≈ 0` ([#14270](https://github.com/leanprover-community/mathlib/pull/14270))
We invert the directions of a few simple equivalences/relabellings to a more natural order (simpler on the RHS).

### [2022-05-22 23:41:33](https://github.com/leanprover-community/mathlib/commit/5a24374)
doc(set_theory/game/basic): improve docs ([#14268](https://github.com/leanprover-community/mathlib/pull/14268))

### [2022-05-22 23:41:32](https://github.com/leanprover-community/mathlib/commit/cef5898)
chore(linear_algebra): generalize conversion between matrices and bilinear forms to semirings ([#14263](https://github.com/leanprover-community/mathlib/pull/14263))
Only one lemma was moved (`dual_distrib_apply`), none were renamed, and no proofs were meaningfully changed.
Section markers were shuffled around, and some variables exchanged for variables with weaker typeclass assumptions.
A few other things have been generalized to semiring at the same time; `linear_map.trace` and `linear_map.smul_rightₗ`

### [2022-05-22 23:41:31](https://github.com/leanprover-community/mathlib/commit/e09e877)
refactor(set_theory/cardinal/cofinality): infer arguments ([#14251](https://github.com/leanprover-community/mathlib/pull/14251))
We make one of the arguments in `cof_type_le` and `lt_cof_type` implicit.

### [2022-05-22 23:41:30](https://github.com/leanprover-community/mathlib/commit/d946573)
chore(data/matrix/basic): add `matrix.star_mul_vec` and `matrix.star_vec_mul` ([#14248](https://github.com/leanprover-community/mathlib/pull/14248))
This also generalizes some nearby typeclasses.

### [2022-05-22 23:41:29](https://github.com/leanprover-community/mathlib/commit/684587b)
feat(set_theory/game/pgame): `add_lf_add_of_lf_of_le` ([#14150](https://github.com/leanprover-community/mathlib/pull/14150))
This generalizes the previously existing `add_lf_add` on `numeric` games.

### [2022-05-22 22:57:28](https://github.com/leanprover-community/mathlib/commit/b7952ee)
refactor(category_theory/shift): remove opaque_eq_to_iso ([#14262](https://github.com/leanprover-community/mathlib/pull/14262))
It seems `opaque_eq_to_iso` was only needed because we had over-eager simp lemmas. After [#14260](https://github.com/leanprover-community/mathlib/pull/14260), it is easy to remove.

### [2022-05-22 21:01:20](https://github.com/leanprover-community/mathlib/commit/178456f)
feat(set_theory/surreal/basic): definition of `≤` and `<` on numeric games ([#14169](https://github.com/leanprover-community/mathlib/pull/14169))

### [2022-05-22 18:33:19](https://github.com/leanprover-community/mathlib/commit/fe2b5ab)
feat(set_theory/game/pgame): instances for empty moves of addition ([#14297](https://github.com/leanprover-community/mathlib/pull/14297))

### [2022-05-22 17:01:21](https://github.com/leanprover-community/mathlib/commit/1b7e918)
chore(algebra/geom_sum): rename to odd.geom_sum_pos ([#14264](https://github.com/leanprover-community/mathlib/pull/14264))
allowing dot notation :)

### [2022-05-22 16:14:11](https://github.com/leanprover-community/mathlib/commit/eb8994b)
feat(measure_theory): use more `[(pseudo_)metrizable_space]` ([#14232](https://github.com/leanprover-community/mathlib/pull/14232))
* Use `[metrizable_space α]` or `[pseudo_metrizable_space α]` assumptions in some lemmas, replace `tendsto_metric` with `tendsto_metrizable` in the names of these lemmas.
* Drop `measurable_of_tendsto_metric'` and `measurable_of_tendsto_metric` in favor of `measurable_of_tendsto_metrizable'` and `measurable_of_tendsto_metrizable`.

### [2022-05-22 14:41:20](https://github.com/leanprover-community/mathlib/commit/eae0510)
feat(category_theory/natural_isomorphism): a simp lemma cancelling inverses ([#14299](https://github.com/leanprover-community/mathlib/pull/14299))
I am not super happy to be adding lemmas like this, because it feels like better designed simp normal forms (or something else) could just avoid the need.
However my efforts to think about this keep getting stuck on the shift functor hole we're in, and this lemma is useful in the meantime to dig my way out of it. :-)

### [2022-05-22 14:41:19](https://github.com/leanprover-community/mathlib/commit/e4a8db1)
feat(data/real/ennreal): lemmas about unions and intersections ([#14296](https://github.com/leanprover-community/mathlib/pull/14296))

### [2022-05-22 14:41:17](https://github.com/leanprover-community/mathlib/commit/a836c6d)
refactor(category_theory): remove some simp lemmas about eq_to_hom ([#14260](https://github.com/leanprover-community/mathlib/pull/14260))
The simp lemma `eq_to_hom_map : F.map (eq_to_hom p) = eq_to_hom (congr_arg F.obj p)` is rather dangerous, but after it has fired it's much harder to see the functor `F` (e.g. to use naturality of a natural transformation).
This PR removes `@[simp]` from that lemma, at the expense of having a few `local attribute [simp]`s, and adding it explicitly to simp sets.
On the upside, we also get to *remove* some `simp [-eq_to_hom_map]`s. I'm hoping also to soon be able to remove `opaque_eq_to_hom`, as it was introduced to avoid the problem this simp lemma was causing.
The PR is part of an effort to solve some problems identified on [zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/trouble.20in.20.60shift_functor.60.20land).

### [2022-05-22 12:23:13](https://github.com/leanprover-community/mathlib/commit/0386c3b)
refactor(order/filter/lift): reformulate `lift_infi` etc ([#14138](https://github.com/leanprover-community/mathlib/pull/14138))
* add `monotone.of_map_inf` and `monotone.of_map_sup`;
* add `filter.lift_infi_le`: this inequality doesn't need any assumptions;
* reformulate `filter.lift_infi` and `filter.lift'_infi` using `g (s ∩ t) = g s ⊓ g t` instead of `g s ⊓ g t = g (s ∩ t)`;
* rename `filter.lift_infi'` to `filter.lift_infi_of_directed`, use `g (s ∩ t) = g s ⊓ g t`;
* add `filter.lift_infi_of_map_univ` and `filter.lift'_infi_of_map_univ`.

### [2022-05-22 11:09:06](https://github.com/leanprover-community/mathlib/commit/d036d3c)
feat(probability/stopping): prove measurability of the stopped value ([#14062](https://github.com/leanprover-community/mathlib/pull/14062))

### [2022-05-22 11:09:05](https://github.com/leanprover-community/mathlib/commit/49b68e8)
feat(analysis/convex/uniform): Uniformly convex spaces ([#13480](https://github.com/leanprover-community/mathlib/pull/13480))
Define uniformly convex spaces and prove the implications `inner_product_space ℝ E → uniform_convex_space E` and `uniform_convex_space E → strict_convex_space ℝ E`.

### [2022-05-22 09:27:57](https://github.com/leanprover-community/mathlib/commit/ac00603)
feat(measure_theory/measure/measure_space): add some `null_measurable_set` lemmas ([#14293](https://github.com/leanprover-community/mathlib/pull/14293))
Add `measure_bUnion₀`, `measure_sUnion₀`, and `measure_bUnion_finset₀`.

### [2022-05-22 09:27:56](https://github.com/leanprover-community/mathlib/commit/726b9ce)
feat(set_theory/ordinal/arithmetic): Lemmas about `bsup o.succ f` on a monotone function ([#14289](https://github.com/leanprover-community/mathlib/pull/14289))

### [2022-05-22 09:27:55](https://github.com/leanprover-community/mathlib/commit/e99ff88)
feat(measure_theory): add `restrict_inter_add_diff` and `lintegral_inter_add_diff` ([#14280](https://github.com/leanprover-community/mathlib/pull/14280))
* add `measure_theory.measure.restrict_inter_add_diff` and `measure_theory.lintegral_inter_add_diff`;
* drop one measurability assumption in `measure_theory.lintegral_union`;
* add `measure_theory.lintegral_max` and `measure_theory.set_lintegral_max`;
* drop `measure_theory.measure.lebesgue_decomposition.max_measurable_le`: use `set_lintegral_max` instead.

### [2022-05-22 09:27:53](https://github.com/leanprover-community/mathlib/commit/2d9f791)
feat(order/filter): add lemmas about filter.has_antitone_basis ([#14131](https://github.com/leanprover-community/mathlib/pull/14131))
* add `filter.has_antitone_basis.comp_mono` and
  `filter.has_antitone_basis.comp_strict_mono`;
* add `filter.has_antitone_basis.subbasis_with_rel`;
* generalize `filter.has_basis.exists_antitone_subbasis` to `ι : Sort*`.
* add a missing docstring.

### [2022-05-22 09:27:53](https://github.com/leanprover-community/mathlib/commit/52df6ab)
refactor(category_theory): remove all decidability instances ([#14046](https://github.com/leanprover-community/mathlib/pull/14046))
Make the category theory library thoroughly classical: mostly this is ceasing carrying around decidability instances for the indexing types of biproducts, and for the object and morphism types in `fin_category`.
It appears there was no real payoff: the category theory library is already extremely non-constructive.
As I was running into occasional problems providing decidability instances (when writing construction involving reindexing biproducts), it seems easiest to just remove this vestigial constructiveness from the category theory library.

### [2022-05-22 08:40:44](https://github.com/leanprover-community/mathlib/commit/37647bf)
feat(measure_theory/constructions/borel_space): add `norm_cast` lemmas ([#14295](https://github.com/leanprover-community/mathlib/pull/14295))

### [2022-05-22 06:29:42](https://github.com/leanprover-community/mathlib/commit/9b8588a)
chore(algebra/order/ring): golf `mul_le_one` ([#14245](https://github.com/leanprover-community/mathlib/pull/14245))
golf `mul_le_one`

### [2022-05-22 06:29:41](https://github.com/leanprover-community/mathlib/commit/49ce967)
feat(ring_theory/valuation/basic): notation for `with_zero (multiplicative ℤ)` ([#14064](https://github.com/leanprover-community/mathlib/pull/14064))
And likewise for `with_zero (multiplicative ℕ)`

### [2022-05-22 04:22:45](https://github.com/leanprover-community/mathlib/commit/a8a211f)
feat(order/lattice): add `left_lt_inf` etc ([#14152](https://github.com/leanprover-community/mathlib/pull/14152))
* add `left_lt_sup`, `right_lt_sup`, `left_or_right_lt_sup`, and their `inf` counterparts;
* generalize `is_top_or_exists_gt` and `is_bot_or_exists_lt` to directed orders, replacing `forall_le_or_exists_lt_inf` and `forall_le_or_exists_lt_sup`;
* generalize `exists_lt_of_sup` and `exists_lt_of_inf` to directed orders, rename them to `exists_lt_of_directed_le` and `exists_lt_of_directed_ge`.

### [2022-05-22 01:40:48](https://github.com/leanprover-community/mathlib/commit/d8b6f76)
feat(set_theory/game/birthday): More basic birthdays ([#14287](https://github.com/leanprover-community/mathlib/pull/14287))

### [2022-05-21 11:38:54](https://github.com/leanprover-community/mathlib/commit/f04684f)
chore(data/set/pointwise): Move into the `set` namespace ([#14281](https://github.com/leanprover-community/mathlib/pull/14281))
A bunch of lemmas about scalar multiplications of sets were dumped in root namespace for some reason.
The lemmas moved to `set.*` are:
* `zero_smul_set`
* `zero_smul_subset`
* `subsingleton_zero_smul_set`
* `zero_mem_smul_set`
* `zero_mem_smul_iff`
* `zero_mem_smul_set_iff`
* `smul_add_set`
* `smul_mem_smul_set_iff`
* `mem_smul_set_iff_inv_smul_mem`
* `mem_inv_smul_set_iff`
* `preimage_smul`
* `preimage_smul_inv`
* `set_smul_subset_set_smul_iff`
* `set_smul_subset_iff`
* `subset_set_smul_iff`
* `smul_mem_smul_set_iff₀`
* `mem_smul_set_iff_inv_smul_mem₀`
* `mem_inv_smul_set_iff₀`
* `preimage_smul₀`
* `preimage_smul_inv₀`
* `set_smul_subset_set_smul_iff₀`
* `set_smul_subset_iff₀`
* `subset_set_smul_iff₀`
* `smul_univ₀`
* `smul_set_univ₀`

### [2022-05-21 08:14:04](https://github.com/leanprover-community/mathlib/commit/fc19a4e)
feat({data/finset,order/filter}/pointwise): Multiplicative action on pointwise monoids ([#14214](https://github.com/leanprover-community/mathlib/pull/14214))
`mul_action`, `distrib_mul_action`, `mul_distrib_mul_action` instances for `finset` and `filter`. Also delete `set.smul_add_set` because `smul_add` proves it.

### [2022-05-21 06:32:31](https://github.com/leanprover-community/mathlib/commit/eaa771f)
chore(tactic/cancel_denoms): remove an unused have ([#14269](https://github.com/leanprover-community/mathlib/pull/14269))

### [2022-05-21 03:17:39](https://github.com/leanprover-community/mathlib/commit/d787d49)
feat(algebra/big_operators): add `finset.prod_comm'` ([#14257](https://github.com/leanprover-community/mathlib/pull/14257))
* add a "dependent" version of `finset.prod_comm`;
* use it to prove the original lemma;
* slightly generalize `exists_eq_right_right` and `exists_eq_right_right'`;
* add two `simps` attributes.

### [2022-05-21 00:59:53](https://github.com/leanprover-community/mathlib/commit/3fc6fbb)
feat(algebra/divisibility): `is_refl` and `is_trans` instances for divisibility ([#14240](https://github.com/leanprover-community/mathlib/pull/14240))

### [2022-05-21 00:22:23](https://github.com/leanprover-community/mathlib/commit/0e095f0)
feat(data/polynomial/mirror): `mirror` is injective ([#14254](https://github.com/leanprover-community/mathlib/pull/14254))
This PR adds an `inj` lemma for `mirror`.

### [2022-05-20 23:44:35](https://github.com/leanprover-community/mathlib/commit/d217e1d)
feat(set_theory/game/pgame): `sub_self_equiv` ([#14272](https://github.com/leanprover-community/mathlib/pull/14272))

### [2022-05-20 18:26:01](https://github.com/leanprover-community/mathlib/commit/a6b90be)
refactor(set_theory/cardinal/*): add `succ_order` instance, rename `succ` lemmas ([#14244](https://github.com/leanprover-community/mathlib/pull/14244))
We rename the lemmas on `cardinal.succ` to better match those from `succ_order`.
- `succ_le` → `succ_le_iff`
- `lt_succ` → `lt_succ_iff`
- `lt_succ_self` → `lt_succ`
We also add `succ_le_of_lt` and `le_of_lt_succ`.

### [2022-05-20 17:46:23](https://github.com/leanprover-community/mathlib/commit/113f7e4)
feat(linear_algebra/trace): trace of projection maps  ([#14165](https://github.com/leanprover-community/mathlib/pull/14165))
This is proved under the `field` assumption instead of the finite free module assumptions generally used to talk about the trace because we need the submodules `p` and `f.ker` to also be free and finite.
- [x] depends on: [#13872](https://github.com/leanprover-community/mathlib/pull/13872)

### [2022-05-20 16:36:21](https://github.com/leanprover-community/mathlib/commit/1983e40)
feat(data/zmod/basic): If the orbit is finite, then the minimal period is positive ([#14201](https://github.com/leanprover-community/mathlib/pull/14201))
This PR adds an instance stating that if the orbit is finite, then the minimal period is positive.
The instance is needed for an explicit computation that involves a product indexed by `zmod (minimal_period ((•) a) b)`.

### [2022-05-20 15:32:16](https://github.com/leanprover-community/mathlib/commit/846ed9f)
chore(measure_theory/integral/lebesgue): golf some proofs ([#14256](https://github.com/leanprover-community/mathlib/pull/14256))

### [2022-05-20 13:34:14](https://github.com/leanprover-community/mathlib/commit/180d975)
feat(set_theory/game/pgame): Tweak `pgame.add` API ([#13611](https://github.com/leanprover-community/mathlib/pull/13611))
We modify the API for `pgame.add` as follows: 
- `left_moves_add` and `right_moves_add` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.
We also golf a few theorems and make some parameters explicit.

### [2022-05-20 11:17:03](https://github.com/leanprover-community/mathlib/commit/1483eca)
feat(algebra/algebra/operations): add right induction principles for power membership ([#14219](https://github.com/leanprover-community/mathlib/pull/14219))
We already had the left-induction principles.
There's probably some clever trick to get these via `mul_opposite`, but I'm not sure if it's worth the effort.

### [2022-05-20 06:26:14](https://github.com/leanprover-community/mathlib/commit/1e011e3)
feat(linear_algebra/trace): trace of prod_map ([#13872](https://github.com/leanprover-community/mathlib/pull/13872))
In this PR I prove that the trace is additive under `prod_map`, i.e. that `trace (prod_map f g) = trace f + trace g`.

### [2022-05-20 04:06:08](https://github.com/leanprover-community/mathlib/commit/735fbe0)
chore(scripts): update nolints.txt ([#14255](https://github.com/leanprover-community/mathlib/pull/14255))
I am happy to remove some nolints for you!

### [2022-05-20 01:48:36](https://github.com/leanprover-community/mathlib/commit/a5878bb)
feat(data/polynomial/mirror): `mirror_eq_iff` ([#14238](https://github.com/leanprover-community/mathlib/pull/14238))
This PR adds a lemma stating that `p.mirror = q ↔ p = q.mirror`.

### [2022-05-20 00:16:04](https://github.com/leanprover-community/mathlib/commit/c9c9fa1)
refactor(category_theory/discrete): make discrete irreducible ([#13762](https://github.com/leanprover-community/mathlib/pull/13762))

### [2022-05-19 19:16:16](https://github.com/leanprover-community/mathlib/commit/5cf7a1c)
feat (algebra/group/prod): Showing that embed_product is injective ([#14247](https://github.com/leanprover-community/mathlib/pull/14247))
Proves that `embed_product` is injective.

### [2022-05-19 19:16:15](https://github.com/leanprover-community/mathlib/commit/3c6f16c)
feat(algebra/group/conj): instances + misc ([#13943](https://github.com/leanprover-community/mathlib/pull/13943))

### [2022-05-19 17:11:59](https://github.com/leanprover-community/mathlib/commit/c8f2a1f)
chore(*) : `zero_dvd_iff.1` → `eq_zero_of_zero_dvd` ([#14241](https://github.com/leanprover-community/mathlib/pull/14241))
We already had a name for this theorem, so we might as well use it.

### [2022-05-19 17:11:58](https://github.com/leanprover-community/mathlib/commit/ffe7002)
feat(topology/locally_constant): Characteristic functions on clopen sets are locally constant ([#11708](https://github.com/leanprover-community/mathlib/pull/11708))
Gives an API for characteristic functions on clopen sets, `char_fn`, which are locally constant functions.

### [2022-05-19 16:29:55](https://github.com/leanprover-community/mathlib/commit/d403cad)
chore(linear_algebra/quadratic_form/basic): remove redundant fields ([#14246](https://github.com/leanprover-community/mathlib/pull/14246))
This renames `quadratic_form.mk_left` to `quadratic_form.mk` by removing the redundant fields in the structure, as the proof of `mk_left` didn't actually use the fact the ring was commutative as it claimed to in the docstring.
The only reason we could possibly want these is if addition were non-commutative, which seems extremely unlikely.

### [2022-05-19 14:21:27](https://github.com/leanprover-community/mathlib/commit/218d66a)
doc(tactic/lint/type_classes): Fix small typo ([#14242](https://github.com/leanprover-community/mathlib/pull/14242))

### [2022-05-19 12:28:20](https://github.com/leanprover-community/mathlib/commit/e29d911)
feat(group_theory/quotient_group): properties of quotients of homomorphisms and equivalences ([#13046](https://github.com/leanprover-community/mathlib/pull/13046))
Add `id`, `comp` for quotients of homomorphisms and `refl`, `symm`, `trans` for quotients of equivalences.

### [2022-05-19 10:20:40](https://github.com/leanprover-community/mathlib/commit/18624ef)
feat(order/complete_lattice): add `Sup_diff_singleton_bot` etc ([#14205](https://github.com/leanprover-community/mathlib/pull/14205))
* add `Sup_diff_singleton_bot` and `Inf_diff_singleton_top`;
* add `set.sUnion_diff_singleton_empty` and `set.sInter_diff_singleton_univ`.

### [2022-05-19 09:41:31](https://github.com/leanprover-community/mathlib/commit/6906b6f)
feat(analysis/normed_space/pi_Lp): add missing nnnorm lemmas ([#14221](https://github.com/leanprover-community/mathlib/pull/14221))
This renames `pi_Lp.dist` to `pi_Lp.dist_eq` and `pi_Lp.edist` to `pi_Lp.edist_eq` to match `pi_Lp.norm_eq`.
The `nndist` version of these lemmas is new.
The `pi_Lp.norm_eq_of_L2` lemma was not stated at the correct generality, and has been moved to an earlier file where doing so is easier.
The `nnnorm` version of this lemma is new.
Also replaces some `∀` binders with `Π` to match the pretty-printer, and tidies some whitespace.

### [2022-05-19 05:25:12](https://github.com/leanprover-community/mathlib/commit/ea3009f)
docs(category_theory/*): the last missing module docs ([#14237](https://github.com/leanprover-community/mathlib/pull/14237))

### [2022-05-19 03:48:08](https://github.com/leanprover-community/mathlib/commit/923a14d)
chore(scripts): update nolints.txt ([#14239](https://github.com/leanprover-community/mathlib/pull/14239))
I am happy to remove some nolints for you!

### [2022-05-19 01:41:46](https://github.com/leanprover-community/mathlib/commit/83285b2)
refactor(set_theory/game/pgame): Rename `le_def_lf` → `le_iff_forall_lf` ([#14206](https://github.com/leanprover-community/mathlib/pull/14206))
One-sided variants of these have also been introduced.

### [2022-05-19 00:34:01](https://github.com/leanprover-community/mathlib/commit/cc74bcb)
feat(topology/algebra/module/basic): add `continuous_linear_map.apply_module` ([#14223](https://github.com/leanprover-community/mathlib/pull/14223))
This matches `linear_map.apply_module`, but additionally provides `has_continuous_const_smul`.
This also adds the missing `continuous_linear_map.semiring` and `continuous_linear_map.monoid_with_zero` instances.

### [2022-05-18 23:17:05](https://github.com/leanprover-community/mathlib/commit/76f9f45)
feat(category_theory/limits): (co/bi)products over types with a unique term ([#14191](https://github.com/leanprover-community/mathlib/pull/14191))

### [2022-05-18 22:19:04](https://github.com/leanprover-community/mathlib/commit/c42cff1)
doc(deprecated/*): all deprecated files now lint ([#14233](https://github.com/leanprover-community/mathlib/pull/14233))
I am happy to remove some nolints for you.

### [2022-05-18 22:19:03](https://github.com/leanprover-community/mathlib/commit/a5f4cf5)
fix(algebra/ring_quot): fix a diamond in the int-smul action ([#14226](https://github.com/leanprover-community/mathlib/pull/14226))
We already handle the `nsmul` diamond correctly in the lines above

### [2022-05-18 20:08:39](https://github.com/leanprover-community/mathlib/commit/32700f5)
refactor(*): `insert_singleton` → `pair` ([#14210](https://github.com/leanprover-community/mathlib/pull/14210))
We rename various theorems with `insert_singleton` in the name to the more sensible and searchable `pair`. We also golf `finset.pair_comm`.

### [2022-05-18 20:08:38](https://github.com/leanprover-community/mathlib/commit/5fe43a9)
feat(linear_algebra/trace): trace of tensor_products and hom_tensor_hom is an equivalence ([#13728](https://github.com/leanprover-community/mathlib/pull/13728))

### [2022-05-18 18:01:54](https://github.com/leanprover-community/mathlib/commit/259c951)
doc(src/deprecated/*): add module docstrings ([#14224](https://github.com/leanprover-community/mathlib/pull/14224))
Although we don't ever import them now, I add module docstrings for a couple of deprecated files to make the linter happier. I also attempt to unify the style in the docstrings of all the deprecated files.

### [2022-05-18 18:01:53](https://github.com/leanprover-community/mathlib/commit/4f31117)
feat(data/set/basic): add `set.subset_range_iff_exists_image_eq` and `set.range_image` ([#14203](https://github.com/leanprover-community/mathlib/pull/14203))
* add `set.subset_range_iff_exists_image_eq` and `set.range_image`;
* use the former to golf `set.can_lift` (name fixed from `set.set.can_lift`);
* golf `set.exists_eq_singleton_iff_nonempty_subsingleton`.

### [2022-05-18 16:04:05](https://github.com/leanprover-community/mathlib/commit/470ddbd)
chore(analysis,topology): add missing ulift instances ([#14217](https://github.com/leanprover-community/mathlib/pull/14217))

### [2022-05-18 16:04:04](https://github.com/leanprover-community/mathlib/commit/503970d)
chore(data/fintype/basic): Better `fin` lemmas ([#14200](https://github.com/leanprover-community/mathlib/pull/14200))
Turn `finset.image` into `finset.map` and `insert` into `finset.cons` in the three lemmas relating `univ : finset (fin (n + 1))` and `univ : finset (fin n)`. Golf proofs involving the related big operators lemmas.

### [2022-05-18 16:04:03](https://github.com/leanprover-community/mathlib/commit/c38ab35)
feat(analysis/convex/combination): The convex hull of `s + t` ([#14160](https://github.com/leanprover-community/mathlib/pull/14160))
`convex_hull` distributes over pointwise addition of sets and commutes with pointwise scalar multiplication. Also delete `linear_map.image_convex_hull` because it duplicates `linear_map.convex_hull_image`.

### [2022-05-18 14:08:52](https://github.com/leanprover-community/mathlib/commit/cfedf1d)
feat(ring_theory/ideal/operations.lean): lemmas about coprime ideals ([#14176](https://github.com/leanprover-community/mathlib/pull/14176))
Generalises some lemmas from `ring_theory/coprime/lemmas.lean` to the case of non-principal ideals.

### [2022-05-18 14:08:51](https://github.com/leanprover-community/mathlib/commit/2c2d515)
refactor(data/list/min_max): Generalise `list.argmin`/`list.argmax` to preorders ([#13221](https://github.com/leanprover-community/mathlib/pull/13221))
This PR generalises the contents of the `data/list/min_max` file from a `linear_order` down to a `preorder` with decidable `<`. Note that for this to work out, I have had to change the structure of the auxiliary function `argmax₂` to now mean `option.cases_on a (some b) (λ c, if f c < f b then some b else some c)`. This is because in the case of a preorder, `argmax₂` would perform the swap in the absence of the `≤` relation, which would result in a semi-random shuffle that doesn't look very `maximal`.

### [2022-05-18 13:10:54](https://github.com/leanprover-community/mathlib/commit/54773fc)
feat(topology/algebra/module/multilinear): add `continuous_multilinear_map.smul_right` ([#14218](https://github.com/leanprover-community/mathlib/pull/14218))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Question.20about.20.60formal_multilinear_series.60 for one use case

### [2022-05-18 12:02:21](https://github.com/leanprover-community/mathlib/commit/9dc9c3e)
feat(logic/lemmas): Distributivity of `if then else` ([#14146](https://github.com/leanprover-community/mathlib/pull/14146))
Distributivity laws for `dite` and `ite`.

### [2022-05-18 10:31:07](https://github.com/leanprover-community/mathlib/commit/ae6a7c3)
feat(linear_algebra/multilinear/finite_dimensional): generalize to finite and free ([#14199](https://github.com/leanprover-community/mathlib/pull/14199))
This also renames some `free` and `finite` instances which had garbage names.

### [2022-05-18 07:53:52](https://github.com/leanprover-community/mathlib/commit/59facea)
chore(data/multiset/basic): `∅` → `0` ([#14211](https://github.com/leanprover-community/mathlib/pull/14211))
It's preferred to use `0` instead of `∅` throughout the multiset API.

### [2022-05-18 04:57:17](https://github.com/leanprover-community/mathlib/commit/d08f734)
chore(measure_theory/function/strongly_measurable): golf some proofs ([#14209](https://github.com/leanprover-community/mathlib/pull/14209))

### [2022-05-18 02:51:15](https://github.com/leanprover-community/mathlib/commit/50696a8)
chore(data/multiset/basic): Inline instances ([#14208](https://github.com/leanprover-community/mathlib/pull/14208))
We inline various protected theorems into the `ordered_cancel_add_comm_monoid` instance. We also declare `covariant_class` and `contravariant_class` instances, which make further theorems redundant.

### [2022-05-18 02:13:32](https://github.com/leanprover-community/mathlib/commit/9f6f605)
feat(data/polynomial/mirror): Central coefficient of `p * p.mirror` ([#14096](https://github.com/leanprover-community/mathlib/pull/14096))
This PR adds a lemma `(p * p.mirror).coeff (p.nat_degree + p.nat_trailing_degree) = p.sum (λ n, (^ 2))`.
I also rearranged the file by assumptions on the ring `R`.

### [2022-05-18 01:20:31](https://github.com/leanprover-community/mathlib/commit/f48cbb1)
feat(category_theory/limits): reindexing (co/bi)products ([#14193](https://github.com/leanprover-community/mathlib/pull/14193))

### [2022-05-17 23:22:58](https://github.com/leanprover-community/mathlib/commit/ca5930d)
feat(data/multiset/basic): `pair_comm` ([#14207](https://github.com/leanprover-community/mathlib/pull/14207))

### [2022-05-17 23:22:57](https://github.com/leanprover-community/mathlib/commit/6b291d7)
feat(analysis/special_functions/trigonometric/arctan): add `real.range_arctan` ([#14204](https://github.com/leanprover-community/mathlib/pull/14204))

### [2022-05-17 23:22:56](https://github.com/leanprover-community/mathlib/commit/632fef3)
feat(analysis/normed_space/M_structure): Define L-projections, show they form a Boolean algebra ([#12173](https://github.com/leanprover-community/mathlib/pull/12173))
A continuous projection P on a normed space X is said to be an L-projection if, for all `x` in `X`,
```
∥x∥ = ∥P x∥ + ∥(1-P) x∥.
```
The range of an L-projection is said to be an L-summand of X.
A continuous projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
```
∥x∥ = max(∥P x∥,∥(1-P) x∥).
```
The range of an M-projection is said to be an M-summand of X.
The L-projections and M-projections form Boolean algebras. When X is a Banach space, the Boolean
algebra of L-projections is complete.
Let `X` be a normed space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if
the topological annihilator `M^∘` is an L-summand of `X^*`.
M-ideal, M-summands and L-summands were introduced by Alfsen and Effros to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.
This initial PR limits itself to showing that the L-projections form a Boolean algebra. The approach followed is based on that used in `measure_theory.measurable_space`. The equivalent result for M-projections can be established by a similar argument or by a duality result (to be established). However, I thought it best to seek feedback before proceeding further.

### [2022-05-17 21:17:37](https://github.com/leanprover-community/mathlib/commit/0afb90b)
refactor(algebra/parity): Generalize to division monoids ([#14187](https://github.com/leanprover-community/mathlib/pull/14187))
Generalize lemmas about `is_square`, `even` and `odd`. Improve dot notation.

### [2022-05-17 20:04:43](https://github.com/leanprover-community/mathlib/commit/2158193)
feat(topology/instances/matrix): add topological/continuous instances ([#14202](https://github.com/leanprover-community/mathlib/pull/14202))
For completeness, `has_continuous_add` and `topological_add_group`
instances are added to matrices, as pi types already have
these. Additionally, `has_continuous_const_smul` and
`has_continuous_smul` matrix instances have been made more generic,
allowing differing index types.

### [2022-05-17 18:49:25](https://github.com/leanprover-community/mathlib/commit/1f0f981)
chore(linear_algebra/multilinear/basic): move finite-dimensionality to a new file ([#14198](https://github.com/leanprover-community/mathlib/pull/14198))
`linear_algebra.matrix.to_lin` pulls in a lot of imports that appear to slow things down considerably in downstream files.
The proof is moved without modification.

### [2022-05-17 17:18:53](https://github.com/leanprover-community/mathlib/commit/ae6f59d)
feat(analysis/locally_convex/with_seminorms): pull back `with_seminorms` along a linear inducing ([#13549](https://github.com/leanprover-community/mathlib/pull/13549))
This show that, if `f : E -> F` is linear and the topology on `F` is induced by a family of seminorms `p`, then the topology induced on `E` through `f` is induced by the seminorms `(p i) ∘ f`.
- [x] depends on: [#13547](https://github.com/leanprover-community/mathlib/pull/13547)

### [2022-05-17 17:18:52](https://github.com/leanprover-community/mathlib/commit/ba38b47)
feat(group_theory/perm/list): Add missing `form_perm` lemmas ([#13218](https://github.com/leanprover-community/mathlib/pull/13218))

### [2022-05-17 15:35:00](https://github.com/leanprover-community/mathlib/commit/da201ad)
chore(set_theory/ordinal/{basic, arithmetic}): Inline instances ([#14076](https://github.com/leanprover-community/mathlib/pull/14076))
We inline various definition in the `ordinal` instances, thus avoiding protected (or unprotected!) definitions that are only used once.

### [2022-05-17 15:34:59](https://github.com/leanprover-community/mathlib/commit/600d8ea)
feat(topology/metric_space): define a pseudo metrizable space ([#14053](https://github.com/leanprover-community/mathlib/pull/14053))
* define `topological_space.pseudo_metrizable_space`;
* copy API from `topological_space.metrizable_space`;
* add `pi` instances;
* use `X`, `Y` instead of `α`, `β`.

### [2022-05-17 15:34:57](https://github.com/leanprover-community/mathlib/commit/e2eea55)
feat(algebra/homology): short exact sequences ([#14009](https://github.com/leanprover-community/mathlib/pull/14009))
Migrating from LTE. (This is all Johan and Andrew's work, I think, I just tidied up some.)
Please feel free to push changes directly without consulting me. :-)

### [2022-05-17 13:06:20](https://github.com/leanprover-community/mathlib/commit/3d27911)
feat(data/zmod/quotient): The minimal period equals the cardinality of the orbit ([#14183](https://github.com/leanprover-community/mathlib/pull/14183))
This PR adds a lemma stating that `minimal_period ((•) a) b = card (orbit (zpowers a) b)`.

### [2022-05-17 13:06:19](https://github.com/leanprover-community/mathlib/commit/3c87882)
feat(number_theory/arithmetic_function): map a multiplicative function across a product ([#14180](https://github.com/leanprover-community/mathlib/pull/14180))

### [2022-05-17 13:06:18](https://github.com/leanprover-community/mathlib/commit/beee9ec)
feat(data/complex): real part of sum ([#14177](https://github.com/leanprover-community/mathlib/pull/14177))

### [2022-05-17 13:06:17](https://github.com/leanprover-community/mathlib/commit/d3e3eb8)
chore(algebra/monoid_algebra): clean up some bad decidable arguments ([#14175](https://github.com/leanprover-community/mathlib/pull/14175))
Some of these statements contained classical decidable instances rather than generalized ones.
By removing `open_locale classical`, these become easy to find.

### [2022-05-17 13:06:16](https://github.com/leanprover-community/mathlib/commit/7db6ca9)
test({data/{finset,set},order/filter}/pointwise): Ensure priority of the `ℕ` and `ℤ` actions ([#14166](https://github.com/leanprover-community/mathlib/pull/14166))
Each of `set`, `finset`, `filter` creates (non propeq) diamonds with the fundamental `ℕ` and `ℤ` actions because of instances of the form `has_scalar α β → has_scalar α (set β)`. For example, `{2, 3}^2` could well be `{4, 9}` or `{4, 6, 9}`.
The instances involved are all too important to be discarded, so we decide to live with the diamonds but give priority to the `ℕ` and `ℤ` actions. The reasoning for the priority is that those can't easily be spelled out, while the derived actions can. For example, `s.image ((•) 2)` easily replaces `2 • s`. Incidentally, additive combinatorics uses extensively the `ℕ` action.
This PR adds both a library note and tests to ensure this stays the case. It also fixes the additive `set` and `filter` versions, which were not conforming to the test.

### [2022-05-17 13:06:14](https://github.com/leanprover-community/mathlib/commit/f33b084)
feat(topology/separation): generalize a lemma ([#14154](https://github.com/leanprover-community/mathlib/pull/14154))
* generalize `nhds_eq_nhds_iff` from a `[t1_space α]` to a `[t0_space α]`;
* relate `indistinguishable` to `nhds`.

### [2022-05-17 13:06:13](https://github.com/leanprover-community/mathlib/commit/65bf134)
split(algebra/hom/ring): Split off `algebra.ring.basic` ([#14144](https://github.com/leanprover-community/mathlib/pull/14144))
Move `non_unital_ring_hom` and `ring_hom` to a new file `algebra.hom.ring`.
Crediting
* Amelia for [#1305](https://github.com/leanprover-community/mathlib/pull/1305)
* Jireh for [#13430](https://github.com/leanprover-community/mathlib/pull/13430)

### [2022-05-17 13:06:12](https://github.com/leanprover-community/mathlib/commit/4ae5e7a)
feat(data/polynomial/laurent): laurent polynomials are a module over polynomials ([#14121](https://github.com/leanprover-community/mathlib/pull/14121))
This PR only introduces the instance `module R[X] R[T;T⁻¹]`.
I isolated it from the rest, since I want to give special attention to whether there might be any issues declaring it a global instance and whether it should be localized or even simply a def.  Edit: Eric seems happy with this instance!

### [2022-05-17 13:06:11](https://github.com/leanprover-community/mathlib/commit/46c42cc)
refactor(algebra/geom_sum): remove definition ([#14120](https://github.com/leanprover-community/mathlib/pull/14120))
There's no need to have a separate definition `geom_sum := ∑ i in range n, x ^ i`. Instead it's better to just write the lemmas about the sum itself: that way `simp` lemmas fire "in the wild", without needing to rewrite expression in terms of `geom_sum` manually.

### [2022-05-17 11:00:13](https://github.com/leanprover-community/mathlib/commit/2370d10)
chore(algebra/order/monoid): golf an instance ([#14184](https://github.com/leanprover-community/mathlib/pull/14184))
Move two instances below to reuse a proof.

### [2022-05-17 03:48:46](https://github.com/leanprover-community/mathlib/commit/f1c08cd)
chore(scripts): update nolints.txt ([#14185](https://github.com/leanprover-community/mathlib/pull/14185))
I am happy to remove some nolints for you!

### [2022-05-17 00:02:01](https://github.com/leanprover-community/mathlib/commit/737784e)
refactor(algebra/{group_power/{basic,lemmas},group_with_zero/power}): Generalize lemmas to division monoids ([#14102](https://github.com/leanprover-community/mathlib/pull/14102))
Generalize `group` and `group_with_zero` lemmas about `zpow` to `division_monoid`. Lemmas are renamed because one of the `group` or `group_with_zero` name has to go. It's just a matter of removing the suffixed `₀`.
Lemma renames

### [2022-05-16 16:38:19](https://github.com/leanprover-community/mathlib/commit/89f2760)
feat(number_theory/legendre_symbol/*): move characters on `zmod n` to new file, add API, improve a proof ([#14178](https://github.com/leanprover-community/mathlib/pull/14178))
This is another "administrative" PR with the goal to have a better file structure.
It moves the section `quad_char_mod_p` from `quadratic_char.lean` to a new file `zmod_char.lean`.
It also adds some API lemmas for `χ₈` and `χ₈'` (which will be useful when dealing with the value of quadratic characters at 2 and -2), and I have used the opportunity to shorten the proof of `χ₄_eq_neg_one_pow`.

### [2022-05-16 15:52:19](https://github.com/leanprover-community/mathlib/commit/93dca41)
chore(geometry/manifold/algebra/left_invariant_derivation): golf some proofs ([#14172](https://github.com/leanprover-community/mathlib/pull/14172))
The `simp only` had a bunch of lemmas that weren't used.

### [2022-05-16 13:42:53](https://github.com/leanprover-community/mathlib/commit/4586a97)
refactor(data/pi/lex): Use `lex`, provide notation ([#14164](https://github.com/leanprover-community/mathlib/pull/14164))
Delete `pilex ι β` in favor of `lex (Π i, β i)` which we provide `Πₗ i, β i` notation for.

### [2022-05-16 13:42:52](https://github.com/leanprover-community/mathlib/commit/009669c)
feat(data/bool/basic): Kaminski's equation ([#14159](https://github.com/leanprover-community/mathlib/pull/14159))
`bool.apply_apply_apply : ∀ (f : bool → bool) (x : bool), f (f (f x)) = f x`

### [2022-05-16 13:42:51](https://github.com/leanprover-community/mathlib/commit/909b673)
split(data/set/semiring): Split off `data.set.pointwise` ([#14145](https://github.com/leanprover-community/mathlib/pull/14145))
Move `set_semiring` to a new file `data.set.semiring`.
Crediting Floris for [#3240](https://github.com/leanprover-community/mathlib/pull/3240)

### [2022-05-16 13:42:49](https://github.com/leanprover-community/mathlib/commit/a9e74ab)
feat(order/filter/at_top_bot): use weaker TC assumptions, add lemmas ([#14105](https://github.com/leanprover-community/mathlib/pull/14105))
* add `filter.eventually_gt_of_tendsto_at_top`,
  `filter.eventually_ne_at_bot`,
  `filter.eventually_lt_of_tendsto_at_bot`;
* generalize `filter.eventually_ne_of_tendsto_at_top` and
  `filter.eventually_ne_of_tendsto_at_bot` from nontrivial ordered
  (semi)rings to preorders with no maximal/minimal elements.

### [2022-05-16 11:34:45](https://github.com/leanprover-community/mathlib/commit/844a4f7)
refactor(algebra/hom/group): Generalize `map_inv` to division monoids ([#14134](https://github.com/leanprover-community/mathlib/pull/14134))
A minor change with unexpected instance synthesis breakage. A good deal of dot notation on `monoid_hom.map_inv` breaks, along with a few uses of `map_inv`. Expliciting the type fixes them all, but this is still quite concerning.

### [2022-05-16 11:34:44](https://github.com/leanprover-community/mathlib/commit/90659cb)
fix(tactic/core): Make the `classical` tactic behave like `open_locale classical` ([#14122](https://github.com/leanprover-community/mathlib/pull/14122))
This renames the existing `classical` tactic to `classical!`, and adds a new `classical` tactic that is equivalent to `open_locale classical`.
Comparing the effects of these:
```lean
import tactic.interactive
import tactic.localized
-- this uses the noncomputable instance
noncomputable def foo : decidable_eq ℕ :=
λ m n, begin classical!, apply_instance, end
def bar : decidable_eq ℕ :=
λ m n, begin classical, apply_instance, end
section
open_locale classical
def baz : decidable_eq ℕ :=
λ m n, by apply_instance
end
example : baz = bar := rfl
```
In a few places `classical` was actually just being used as a `resetI`. Only a very small number of uses of `classical` actually needed the more aggressive `classical!` (there are roughtly 500 uses in total); while a number of `congr`s can be eliminated with this change.

### [2022-05-16 09:19:06](https://github.com/leanprover-community/mathlib/commit/df64e5e)
chore(set_theory/game/pgame): minor golf ([#14171](https://github.com/leanprover-community/mathlib/pull/14171))

### [2022-05-16 09:19:05](https://github.com/leanprover-community/mathlib/commit/f4c67ee)
chore(group_theory/specific_groups/cyclic): golf `card_order_of_eq_totient_aux₁` and `card_order_of_eq_totient_aux₂` ([#14161](https://github.com/leanprover-community/mathlib/pull/14161))
Re-writing the proofs of `card_order_of_eq_totient_aux₁` and `card_order_of_eq_totient_aux₂` to use the new `sum_totient` introduced in [#14007](https://github.com/leanprover-community/mathlib/pull/14007), and golfing them.

### [2022-05-16 09:19:04](https://github.com/leanprover-community/mathlib/commit/a5975e7)
feat(data/int/basic): add theorem `int.div_mod_unique` ([#14158](https://github.com/leanprover-community/mathlib/pull/14158))
add the `int` version of `div_mod_unique`.

### [2022-05-16 09:19:03](https://github.com/leanprover-community/mathlib/commit/f7a7c27)
chore(ring_theory/ideal/local_ring): golf some proofs, add missing lemma ([#14157](https://github.com/leanprover-community/mathlib/pull/14157))

### [2022-05-16 09:19:01](https://github.com/leanprover-community/mathlib/commit/55b31e0)
feat(data/zmod/quotient): `orbit (zpowers a) b` is a cycle of order `minimal_period ((•) a) b` ([#14124](https://github.com/leanprover-community/mathlib/pull/14124))
This PR applies the orbit-stabilizer theorem to the action of a cyclic subgroup.

### [2022-05-16 09:19:00](https://github.com/leanprover-community/mathlib/commit/bc7a201)
feat(*): Pointwise monoids have distributive negations ([#14114](https://github.com/leanprover-community/mathlib/pull/14114))
More instances of `has_distrib_neg`:
* `function.injective.has_distrib_neg`, `function.surjective.has_distrib_neg`
* `add_opposite`, `mul_opposite`
* `set`, `finset`, `filter`

### [2022-05-16 09:18:59](https://github.com/leanprover-community/mathlib/commit/f0db51d)
feat(algebra/module): morphism classes for (semi)linear maps ([#13939](https://github.com/leanprover-community/mathlib/pull/13939))
This PR introduces morphism classes corresponding to `mul_action_hom`, `distrib_mul_action_hom`, `mul_semiring_action_hom` and `linear_map`.
Most of the new generic results work smoothly, only `simp` seems to have trouble applying `map_smulₛₗ`. I expect this requires another fix in the elaborator along the lines of [lean[#659](https://github.com/leanprover-community/mathlib/pull/659)](https://github.com/leanprover-community/lean/pull/659). For now we can just keep around the specialized `simp` lemmas `linear_map.map_smulₛₗ` and `linear_equiv.map_smulₛₗ`.
The other changes are either making `map_smul` protected where it conflicts, or helping the elaborator unfold some definitions that previously were helped by the specific `map_smul` lemma suggesting the type.
Thanks to @dupuisf for updating and making this branch compile!
Co-Authored-By: Frédéric Dupuis <dupuisf@iro.umontreal.ca>

### [2022-05-16 08:42:11](https://github.com/leanprover-community/mathlib/commit/0d76285)
doc(set_theory/surreal/basic): update docs ([#14170](https://github.com/leanprover-community/mathlib/pull/14170))
We remove an incorrect remark about the order relations on `pgame`, and reference the branch on which the proof of surreal multiplication is being worked on.

### [2022-05-15 19:05:27](https://github.com/leanprover-community/mathlib/commit/4cf2016)
feat(order/cover): Covering elements are unique ([#14156](https://github.com/leanprover-community/mathlib/pull/14156))
In a linear order, there's at most one element covering `a` and at most one element being covered by `a`.

### [2022-05-15 16:12:50](https://github.com/leanprover-community/mathlib/commit/00e80a6)
feat (group_theory/perm/cycles): Add missing `is_cycle` lemma ([#13219](https://github.com/leanprover-community/mathlib/pull/13219))
Add `is_cycle.pow_eq_pow_iff`, which extends `is_cycle.pow_eq_one_iff`.

### [2022-05-15 14:04:27](https://github.com/leanprover-community/mathlib/commit/c109105)
chore(logic/equiv): golf equiv.subtype_equiv ([#14125](https://github.com/leanprover-community/mathlib/pull/14125))
The naming is a bit all over the place, but I will fix this in a later PR.

### [2022-05-15 14:04:26](https://github.com/leanprover-community/mathlib/commit/843240b)
feat(linear_algebra/matrix): invariant basis number for matrices ([#13845](https://github.com/leanprover-community/mathlib/pull/13845))
This PR shows that invertible matrices over a ring with invariant basis number are square.

### [2022-05-15 14:04:26](https://github.com/leanprover-community/mathlib/commit/f9f64f3)
move(data/prod/*): A `prod` folder ([#13771](https://github.com/leanprover-community/mathlib/pull/13771))
Create folder `data.prod.` to hold `prod` files and related types. Precisely:
* `data.prod` → `data.prod.basic`
* `data.pprod` → `data.prod.pprod`
* `data.tprod` → `data.prod.tprod`
* `order.lexicographic` → `data.prod.lex`

### [2022-05-15 11:58:06](https://github.com/leanprover-community/mathlib/commit/a74298d)
chore(order/lattice): reflow, golf ([#14151](https://github.com/leanprover-community/mathlib/pull/14151))

### [2022-05-15 08:37:51](https://github.com/leanprover-community/mathlib/commit/5c954e1)
chore(order/conditionally_complete_lattice): General cleanup ([#13319](https://github.com/leanprover-community/mathlib/pull/13319))

### [2022-05-15 01:31:14](https://github.com/leanprover-community/mathlib/commit/b8d8a5e)
refactor(set_theory/game/*): Fix bad notation `<` on (pre-)games ([#13963](https://github.com/leanprover-community/mathlib/pull/13963))
Our current definition for `<` on pre-games is, in the wider mathematical literature, referred to as `⧏` (less or fuzzy to). Conversely, what's usually referred to by `<` coincides with the relation we get from `preorder pgame` (which the current API avoids using at all).
We rename `<` to `⧏`, and add the basic API for both the new `<` and `⧏` relations. This allows us to define new instances on `pgame` and `game` that we couldn't before. We also take the opportunity to add some basic API on the fuzzy relation `∥`.
See the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/281094687).

### [2022-05-14 23:44:35](https://github.com/leanprover-community/mathlib/commit/1f00800)
feat(linear_algebra/projection) : projections are conjugate to prod_map id 0 ([#13802](https://github.com/leanprover-community/mathlib/pull/13802))

### [2022-05-14 22:46:42](https://github.com/leanprover-community/mathlib/commit/e738612)
feat(analysis/special_functions/exp_deriv): generalize some lemmas about `complex.exp`, remove `*.cexp_real` ([#13579](https://github.com/leanprover-community/mathlib/pull/13579))
Now we can use `*.cexp` instead of some previous `*.cexp_real` lemmas.
- [x] depends on: [#13575](https://github.com/leanprover-community/mathlib/pull/13575)

### [2022-05-14 17:09:34](https://github.com/leanprover-community/mathlib/commit/570db88)
feat(category_theory): missing comp_ite lemma ([#14143](https://github.com/leanprover-community/mathlib/pull/14143))
We already have `comp_dite`.

### [2022-05-14 17:09:33](https://github.com/leanprover-community/mathlib/commit/ad5edeb)
feat(algebra/big_operators): prod_ite_irrel ([#14142](https://github.com/leanprover-community/mathlib/pull/14142))
A few missing lemams in `big_operators/basic.lean`.

### [2022-05-14 17:09:32](https://github.com/leanprover-community/mathlib/commit/05997bd)
chore(set_theory/ordinal/{basic, arithmetic}): Remove redundant `function` namespace ([#14133](https://github.com/leanprover-community/mathlib/pull/14133))

### [2022-05-14 17:09:31](https://github.com/leanprover-community/mathlib/commit/9d022d7)
doc(data/real/sqrt): Fix typo in described theorem ([#14126](https://github.com/leanprover-community/mathlib/pull/14126))
The previous statement was not true. e.g. sqrt 4 <= 3 does not imply 4 * 4 <= 3

### [2022-05-14 17:09:30](https://github.com/leanprover-community/mathlib/commit/4125b9a)
chore(category_theory/*): move some elementwise lemmas earlier ([#13998](https://github.com/leanprover-community/mathlib/pull/13998))

### [2022-05-14 15:50:40](https://github.com/leanprover-community/mathlib/commit/c992b04)
feat(set_theory/cardinal/cofinality): Cofinality of `nfp` and `deriv` ([#12556](https://github.com/leanprover-community/mathlib/pull/12556))

### [2022-05-14 12:48:56](https://github.com/leanprover-community/mathlib/commit/6d4c202)
feat(analysis/specific_limits/floor_pow): auxiliary results on series involving floors of powers ([#13850](https://github.com/leanprover-community/mathlib/pull/13850))

### [2022-05-14 10:51:28](https://github.com/leanprover-community/mathlib/commit/ba9d551)
chore(algebra/invertible): minor golf ([#14141](https://github.com/leanprover-community/mathlib/pull/14141))

### [2022-05-14 08:16:18](https://github.com/leanprover-community/mathlib/commit/79bc06b)
feat(linear_algebra/matrix/to_lin): equivalence via right multiplication ([#13870](https://github.com/leanprover-community/mathlib/pull/13870))
A very partial generalization of `linear_algebra/matrix/to_lin` to non-commutative rings.
This is far from a complete refactor of the file; it just adds enough for what I need in representation theory immediately.
I've left an extensive note explaining what should be done in a later refactor, but I don't want to have to do this all at once.
See discussion on [zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/matrices).

### [2022-05-14 07:28:44](https://github.com/leanprover-community/mathlib/commit/21a71de)
chore(*): use notation instead of `set.*` ([#14139](https://github.com/leanprover-community/mathlib/pull/14139))

### [2022-05-14 05:39:32](https://github.com/leanprover-community/mathlib/commit/3824493)
refactor(group_theory/free_abelian_group): Make proofs more robust ([#14089](https://github.com/leanprover-community/mathlib/pull/14089))
Reduce the API breakage by proving `distrib (free_abelian_group α)` and `has_distrib_neg (free_abelian_group α)` earlier. Protect lemmas to avoid shadowing the root ones.

### [2022-05-14 05:02:33](https://github.com/leanprover-community/mathlib/commit/9f5b328)
feat(.github/workflows): restore merge_conflicts action, running on cron ([#14137](https://github.com/leanprover-community/mathlib/pull/14137))

### [2022-05-13 16:35:43](https://github.com/leanprover-community/mathlib/commit/b7e20ca)
feat(data/polynomial/degree/definitions): two more `nat_degree_le` lemmas ([#14098](https://github.com/leanprover-community/mathlib/pull/14098))
This PR is similar to [#14095](https://github.com/leanprover-community/mathlib/pull/14095).  It proves the `le` version of `nat_degree_X_pow` and `nat_degree_monomial`.
These lemmas are analogous to the existing `nat_degree_X_le` and `nat_degree_C_mul_X_pow_le`.

### [2022-05-13 15:42:07](https://github.com/leanprover-community/mathlib/commit/6b7fa7a)
feat(data/nat/totient): add `totient_div_of_dvd` and golf `sum_totient` ([#14007](https://github.com/leanprover-community/mathlib/pull/14007))
Add lemma `totient_div_of_dvd`: for `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d`.
Use this to golf `sum_totient`, now stated in terms of `divisors`.  This proof follows that of Theorem 2.2 in Apostol (1976) Introduction to Analytic Number Theory.
Adapt the proof of `nth_roots_one_eq_bUnion_primitive_roots'` to use the new `sum_totient`.
Re-prove the original statement of `sum_totient` for compatibility with uses in `group_theory/specific_groups/cyclic` — may delete this if those uses can be adapted to the new statement.

### [2022-05-13 13:23:57](https://github.com/leanprover-community/mathlib/commit/55cd104)
feat(archive/imo/imo1975_q1): Add the formalization of IMO 1975 Q1 ([#13047](https://github.com/leanprover-community/mathlib/pull/13047))

### [2022-05-13 09:53:49](https://github.com/leanprover-community/mathlib/commit/caa1352)
feat(data/zmod/quotient): Multiplicative version of `zmultiples_quotient_stabilizer_equiv` ([#13948](https://github.com/leanprover-community/mathlib/pull/13948))
This PR adds a multiplicative version of `zmultiples_quotient_stabilizer_equiv`.

### [2022-05-13 09:53:48](https://github.com/leanprover-community/mathlib/commit/03da681)
feat(representation_theory): fdRep k G, the category of finite dim representations of G ([#13740](https://github.com/leanprover-community/mathlib/pull/13740))
We verify that this inherits the rigid monoidal structure from `FinVect G` when `G` is a group.

### [2022-05-13 07:38:22](https://github.com/leanprover-community/mathlib/commit/6a48b38)
feat(topology/uniform_space): lemmas about `s ○ s ○ ... ○ s ⊆ t` ([#14051](https://github.com/leanprover-community/mathlib/pull/14051))

### [2022-05-13 05:13:49](https://github.com/leanprover-community/mathlib/commit/3185c25)
feat(data/list/{count,perm},data/multiset/basic): countp and count lemmas ([#14108](https://github.com/leanprover-community/mathlib/pull/14108))

### [2022-05-13 05:13:48](https://github.com/leanprover-community/mathlib/commit/23a2205)
chore(data/real/ennreal): tidy some proofs ([#14101](https://github.com/leanprover-community/mathlib/pull/14101))

### [2022-05-13 05:13:47](https://github.com/leanprover-community/mathlib/commit/7b7af48)
feat(set_theory/ordinal/basic): Order isomorphism between `o.out.α` and `set.Iio o` ([#14074](https://github.com/leanprover-community/mathlib/pull/14074))
This strengthens the previously existing equivalence.

### [2022-05-13 05:13:46](https://github.com/leanprover-community/mathlib/commit/26f4112)
feat(topology/uniform_space/separation): add `filter.has_basis.mem_separation_rel` ([#14050](https://github.com/leanprover-community/mathlib/pull/14050))
* add `filter.has_basis.mem_separation_rel`;
* add `filter.has_basis.forall_mem_mem`, use it in
  `filter.has_basis.sInter_sets`;
* replace two remaining `lift' powerset` with `small_sets`.

### [2022-05-13 05:13:45](https://github.com/leanprover-community/mathlib/commit/a2e671b)
feat(number_theory/von_mangoldt): simple bounds on von mangoldt function ([#14033](https://github.com/leanprover-community/mathlib/pull/14033))
From the unit fractions project.
More interesting bounds such as the chebyshev bounds coming soon, but for now here are some easy upper and lower bounds.

### [2022-05-13 05:13:44](https://github.com/leanprover-community/mathlib/commit/644cae5)
feat(set_theory/cardinal/cofinality): Move fundamental sequence results to namespace ([#14020](https://github.com/leanprover-community/mathlib/pull/14020))
We put most results about fundamental sequences in the `is_fundamental_sequence` namespace. We also take the opportunity to add a simple missing theorem, `ord_cof`.

### [2022-05-13 02:53:51](https://github.com/leanprover-community/mathlib/commit/c53285a)
feat(order/filter/lift): drop an unneeded assumption ([#14117](https://github.com/leanprover-community/mathlib/pull/14117))
Drop `monotone _` assumptions in `filter.comap_lift_eq` and `filter.comap_lift'_eq`.

### [2022-05-13 02:53:50](https://github.com/leanprover-community/mathlib/commit/85124af)
chore(algebra/order/field): fill in TODO for inv anti lemmas ([#14112](https://github.com/leanprover-community/mathlib/pull/14112))

### [2022-05-13 02:53:49](https://github.com/leanprover-community/mathlib/commit/462b950)
chore(algebra/order/field): fill in missing lemma ([#14111](https://github.com/leanprover-community/mathlib/pull/14111))
We had `inv_le_inv` and its backward direction, this fills in the backward direction for `inv_lt_inv`.

### [2022-05-13 02:53:48](https://github.com/leanprover-community/mathlib/commit/f617862)
feat(data/polynomial/degree/lemmas): two lemmas about `nat_degree`s of sums ([#14100](https://github.com/leanprover-community/mathlib/pull/14100))
Suppose that `f, g` are polynomials.  If both `nat_degree (f + g)` and `nat_degree` of one of them are bounded by `n`, then `nat_degree` of the other is also bounded by `n`.

### [2022-05-13 02:53:47](https://github.com/leanprover-community/mathlib/commit/de418aa)
feat(topology/basic): add lemmas like `closure s \ interior s = frontier s` ([#14086](https://github.com/leanprover-community/mathlib/pull/14086))

### [2022-05-13 02:53:46](https://github.com/leanprover-community/mathlib/commit/15f6b52)
feat(data/set/prod): add `prod_self_{s,}subset_prod_self` ([#14084](https://github.com/leanprover-community/mathlib/pull/14084))

### [2022-05-13 02:53:45](https://github.com/leanprover-community/mathlib/commit/1474996)
feat(topology/basic): add `nhds_basis_closeds` ([#14083](https://github.com/leanprover-community/mathlib/pull/14083))
* add `nhds_basis_closeds`;
* golf 2 proofs;
* move `topological_space.seq_tendsto_iff` to `topology.basic`, rename
  it to `tendsto_at_top_nhds`.

### [2022-05-13 02:53:44](https://github.com/leanprover-community/mathlib/commit/bb97a64)
feat(topology/order): add `nhds_true` and `nhds_false` ([#14082](https://github.com/leanprover-community/mathlib/pull/14082))

### [2022-05-13 02:53:43](https://github.com/leanprover-community/mathlib/commit/bd5914f)
perf(field_theory/primitive_element): declare auxiliary function `noncomputable!` ([#14071](https://github.com/leanprover-community/mathlib/pull/14071))
The declaration `roots_of_min_poly_pi_type` is computable and gets compiled by Lean. Unfortunately, compilation takes about 2-3s on my machine and times out under [#11759](https://github.com/leanprover-community/mathlib/pull/11759) (with timeouts disabled, it takes about 11s on that branch). Since the parameters are all elements of noncomputable types and its only use is a noncomputable `fintype` instance, nobody will care if we explicitly make it computable, and it saves a lot of compilation time.
See also this Zulip thread on `noncomputable!` fixing mysterious timeouts: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeout/near/278494746

### [2022-05-13 02:53:42](https://github.com/leanprover-community/mathlib/commit/c4c279e)
feat(data/real/nnreal): add `nnreal.le_infi_add_infi` and other lemmas ([#14048](https://github.com/leanprover-community/mathlib/pull/14048))
* add `nnreal.coe_two`, `nnreal.le_infi_add_infi`, `nnreal.half_le_self`;
* generalize `le_cinfi_mul_cinfi`, `csupr_mul_csupr_le`, and their
  additive versions to allow two different index types.

### [2022-05-13 01:22:31](https://github.com/leanprover-community/mathlib/commit/a945b18)
feat(linear_algebra/tensor_product): tensor_product.map is bilinear in its two arguments ([#13608](https://github.com/leanprover-community/mathlib/pull/13608))

### [2022-05-12 20:54:24](https://github.com/leanprover-community/mathlib/commit/17102ae)
feat(algebra/big_operators/basic): add `sum_erase_lt_of_pos` ([#14066](https://github.com/leanprover-community/mathlib/pull/14066))
`sum_erase_lt_of_pos (hd : d ∈ s) (hdf : 0 < f d) : ∑ (m : ℕ) in s.erase d, f m < ∑ (m : ℕ) in s, f m`

### [2022-05-12 20:54:23](https://github.com/leanprover-community/mathlib/commit/86d58ae)
feat(data/nat/factorization): three lemmas on the components of factorizations ([#14031](https://github.com/leanprover-community/mathlib/pull/14031))
`pow_factorization_le : p ^ (n.factorization) p ≤ n`
`div_pow_factorization_ne_zero : n / p ^ (n.factorization) p ≠ 0`
`not_dvd_div_pow_factorization : ¬p ∣ n / p ^ (n.factorization) p`
Prompted by [this question](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/prime.20factorisation) in Zulip

### [2022-05-12 20:54:22](https://github.com/leanprover-community/mathlib/commit/3c1ced3)
feat(data/nat/basic): four lemmas on nat and int division ([#13991](https://github.com/leanprover-community/mathlib/pull/13991))
`lt_div_iff_mul_lt (hnd : d ∣ n) : a < n / d ↔ d * a < n`
`div_left_inj (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b` (for `ℕ` and `ℤ`)
`div_lt_div_of_lt_of_dvd (hdb : d ∣ b) (h : a < b) : a / d < b / d`

### [2022-05-12 19:34:26](https://github.com/leanprover-community/mathlib/commit/4b3988a)
feat(data/sym/sym2): simp lemma for quotient.eq ([#14113](https://github.com/leanprover-community/mathlib/pull/14113))

### [2022-05-12 19:34:25](https://github.com/leanprover-community/mathlib/commit/3d03098)
doc(data/matrix/basic): Clarify docstring ([#14109](https://github.com/leanprover-community/mathlib/pull/14109))

### [2022-05-12 18:30:47](https://github.com/leanprover-community/mathlib/commit/27e7f7a)
feat(number_theory/divisors): add `filter_dvd_eq_proper_divisors` ([#14049](https://github.com/leanprover-community/mathlib/pull/14049))
Adds `filter_dvd_eq_proper_divisors` and golfs `filter_dvd_eq_divisors` and a few other lemmas

### [2022-05-12 17:54:58](https://github.com/leanprover-community/mathlib/commit/3b18573)
doc(tactic/rewrite_search/explain): Fix documentation-breaking docstring ([#14107](https://github.com/leanprover-community/mathlib/pull/14107))
This currently renders as
![image](https://user-images.githubusercontent.com/425260/168125021-06ef8851-55a6-4629-b437-7c38a1df7b05.png)

### [2022-05-12 16:23:39](https://github.com/leanprover-community/mathlib/commit/0e834df)
chore(data/nat/multiplicity): simplify proof ([#14103](https://github.com/leanprover-community/mathlib/pull/14103))

### [2022-05-12 16:23:38](https://github.com/leanprover-community/mathlib/commit/0509c9c)
fix(analysis/special_functions/pow): fix norm_num extension ([#14099](https://github.com/leanprover-community/mathlib/pull/14099))
As [reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/kernel.20slow.20to.20accept.20refl.20proof/near/282043840).

### [2022-05-12 16:23:37](https://github.com/leanprover-community/mathlib/commit/c8edd60)
chore(data/polynomial/ring_division): golf a few proofs ([#14097](https://github.com/leanprover-community/mathlib/pull/14097))
* add `polynomial.finite_set_of_is_root`;
* use it to golf a few proofs.

### [2022-05-12 16:23:36](https://github.com/leanprover-community/mathlib/commit/6cf6e8c)
chore(order/filter/basic): golf a few proofs ([#14078](https://github.com/leanprover-community/mathlib/pull/14078))
* golf the proof of `mem_generate_iff` by using `sInter_mem`;
* use `set.inj_on` in the statement of `filter.eq_of_map_eq_map_inj'`;
* golf the proofs of `filter.map_inj` and `filter.comap_ne_bot_iff`.

### [2022-05-12 14:24:07](https://github.com/leanprover-community/mathlib/commit/9b41e4e)
feat(data/polynomial/laurent): add truncation from Laurent polynomials to polynomials ([#14085](https://github.com/leanprover-community/mathlib/pull/14085))
We introduce the truncation of a Laurent polynomial `f`.  It returns a polynomial whose support is exactly the non-negative support of `f`.  We use it to prove injectivity of the inclusion of polynomials in Laurent polynomials.
I also plan to use the results in this PR to prove that any Laurent polynomials is obtain from a polynomial by dividing by a power of the variable.

### [2022-05-12 14:24:06](https://github.com/leanprover-community/mathlib/commit/fa4c036)
chore(order/complete_lattice,data/set/lattice): move `Sup_sUnion` ([#14077](https://github.com/leanprover-community/mathlib/pull/14077))
* move `Sup_sUnion` and `Inf_sUnion` to `data.set.lattice`;
* golf a few proofs.

### [2022-05-12 12:10:19](https://github.com/leanprover-community/mathlib/commit/bada932)
feat(data/multiset/basic): `erase_singleton` ([#14094](https://github.com/leanprover-community/mathlib/pull/14094))
Add `multiset.erase_singleton` which is analogous to the existing [finset.erase_singleton](https://leanprover-community.github.io/mathlib_docs/data/finset/basic.html#finset.erase_singleton).

### [2022-05-12 12:10:18](https://github.com/leanprover-community/mathlib/commit/55671be)
chore(set_theory/zfc): use `derive` for some instances ([#14079](https://github.com/leanprover-community/mathlib/pull/14079))
Also use `has_compl` instead of `has_neg`.

### [2022-05-12 12:10:17](https://github.com/leanprover-community/mathlib/commit/d9e623c)
feat(algebra/*): Division monoid instances for `with_zero` and `mul_opposite` ([#14073](https://github.com/leanprover-community/mathlib/pull/14073))
A few missing instances of `division_monoid` and friends.

### [2022-05-12 12:10:16](https://github.com/leanprover-community/mathlib/commit/c57cfc6)
feat({data/{finset,set},order/filter}/pointwise): Pointwise monoids are division monoids ([#13900](https://github.com/leanprover-community/mathlib/pull/13900))
`α` is a `division_monoid` implies that `set α`, `finset α`, `filter α` are too. The core result needed for this is that `s` is a unit in `set α`/`finset α`/`filter α` if and only if it is equal to `{u}`/`{u}`/`pure u` for some unit `u : α`.

### [2022-05-12 10:27:03](https://github.com/leanprover-community/mathlib/commit/c2e87de)
feat(data/polynomial/degree/definitions): if `r ≠ 0`, then `(monomial i r).nat_degree = i` ([#14095](https://github.com/leanprover-community/mathlib/pull/14095))
Add a lemma analogous to `nat_degree_C_mul_X_pow` and `nat_degree_C_mul_X`.

### [2022-05-12 10:27:02](https://github.com/leanprover-community/mathlib/commit/5927330)
refactor(combinatorics/simple_graph/basic): relax `edge_finset` typeclasses ([#14091](https://github.com/leanprover-community/mathlib/pull/14091))

### [2022-05-12 10:27:01](https://github.com/leanprover-community/mathlib/commit/41afd8c)
feat(analysis/special_functions/pow): asymptotics for real powers and log ([#14088](https://github.com/leanprover-community/mathlib/pull/14088))
From the unit fractions project.

### [2022-05-12 08:45:52](https://github.com/leanprover-community/mathlib/commit/1c8ce7e)
feat(data/complex): real exponential bounds ([#14087](https://github.com/leanprover-community/mathlib/pull/14087))
Bounds on the real exponential function near 1, derived from the complex versions.

### [2022-05-12 08:45:51](https://github.com/leanprover-community/mathlib/commit/b6d1028)
chore(topology/sequences): golf a few proofs ([#14081](https://github.com/leanprover-community/mathlib/pull/14081))

### [2022-05-12 08:45:50](https://github.com/leanprover-community/mathlib/commit/7c4c90f)
feat(category_theory/noetherian): nonzero artinian objects have simple subobjects ([#13972](https://github.com/leanprover-community/mathlib/pull/13972))
# Artinian and noetherian categories
An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.
A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.
We show that any nonzero artinian object has a simple subobject.
## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.

### [2022-05-12 08:45:49](https://github.com/leanprover-community/mathlib/commit/fd98cf1)
chore(ring_theory/unique_factorization_domain): golf ([#13820](https://github.com/leanprover-community/mathlib/pull/13820))
+ Shorten the proof of `exists_irreducible_factor` using `well_founded.has_min` instead of `well_founded.fix`.
+ Remove use of `simp` in `induction_on_irreducible`; now a pure term-mode proof except for the classical instance.
+ Change the proof of `not_unit_iff_exists_factors_eq` (just added in [[#13682](https://github.com/leanprover-community/mathlib/pull/13682)](https://github.com/leanprover-community/mathlib/pull/13682)) to use induction. The new proof doesn't require the `multiset.prod_erase` introduced in [[#13682](https://github.com/leanprover-community/mathlib/pull/13682)](https://github.com/leanprover-community/mathlib/pull/13682), but is about as complex as the old one, so I might change it back if reviewers prefer.

### [2022-05-12 08:45:48](https://github.com/leanprover-community/mathlib/commit/0c26348)
feat(data/finsupp/basic): `finsupp.comap_domain` is an `add_monoid_hom` ([#13783](https://github.com/leanprover-community/mathlib/pull/13783))
This is the version of `map_domain.add_monoid_hom` for `comap_domain`.
I plan to use it for the inclusion of polynomials in Laurent polynomials ([#13415](https://github.com/leanprover-community/mathlib/pull/13415)).
I also fixed a typo in a doc-string.

### [2022-05-12 07:44:21](https://github.com/leanprover-community/mathlib/commit/a966557)
chore(analysis/special_functions/pow): golf a proof ([#14093](https://github.com/leanprover-community/mathlib/pull/14093))
* move `real.abs_rpow_of_nonneg` up;
* use it to golf a line in `real.abs_rpow_le_abs_rpow`.

### [2022-05-12 00:05:58](https://github.com/leanprover-community/mathlib/commit/4977fd9)
feat(ring_theory/finiteness): tensor product of two finite modules is finite ([#13733](https://github.com/leanprover-community/mathlib/pull/13733))
Removes [finite_dimensional_tensor_product](https://leanprover-community.github.io/mathlib_docs/linear_algebra/tensor_product_basis.html#finite_dimensional_tensor_product) since it's now proved by `infer_instance`.

### [2022-05-11 20:41:58](https://github.com/leanprover-community/mathlib/commit/d4884c0)
feat(analysis/asymptotics): use weaker TC assumptions ([#14080](https://github.com/leanprover-community/mathlib/pull/14080))
Merge `is_o.trans` with `is_o.trans'`: both lemmas previously took one `semi_normed_group` argument on the primed type (corresponding to the primed function), but now only assume `has_norm` on all three types.

### [2022-05-11 18:53:31](https://github.com/leanprover-community/mathlib/commit/0302cfd)
chore(measure_theory/function/conditional_expectation): change the definition of condexp and its notation ([#14010](https://github.com/leanprover-community/mathlib/pull/14010))
Before this PR, the conditional expectation `condexp` was defined using an argument `(hm : m ≤ m0)`.
This changes the definition to take only `m`, and assigns the default value 0 if we don't have `m ≤ m0`.
The notation for `condexp m μ f` is simplified to `μ[f|m]`.
The change makes the proofs of the condexp API longer, but no change is needed to lemmas outside of that file. See the file `martingale.lean`: the notation is now simpler, but otherwise little else changes besides removing the now unused argument `[sigma_finite_filtration μ ℱ]` from many lemmas.
Also add an instance `is_finite_measure.sigma_finite_filtration`: we had a lemma with both `is_finite_measure` and `sigma_finite_filtration` arguments, but the first one implies the other.

### [2022-05-11 15:02:00](https://github.com/leanprover-community/mathlib/commit/7a3ae97)
feat(data/polynomial/laurent): add inductions for Laurent polynomials ([#14005](https://github.com/leanprover-community/mathlib/pull/14005))
This PR introduces two induction principles for Laurent polynomials and uses them to show that `T` commutes with everything.

### [2022-05-11 14:23:17](https://github.com/leanprover-community/mathlib/commit/483affa)
feat(measure_theory/integral/interval_integral): add lemma `interval_integrable.sum` ([#14069](https://github.com/leanprover-community/mathlib/pull/14069))
Formalized as part of the Sphere Eversion project.

### [2022-05-11 08:00:03](https://github.com/leanprover-community/mathlib/commit/83bc3b9)
chore(algebra/module/submodule*): replace underscores in file names with a folder ([#14063](https://github.com/leanprover-community/mathlib/pull/14063))

### [2022-05-11 08:00:02](https://github.com/leanprover-community/mathlib/commit/ba60237)
chore(field_theory/adjoin): clarify and speed up proof ([#14041](https://github.com/leanprover-community/mathlib/pull/14041))
This PR turns a couple of refls into `simp` lemmas. Apart from being clearer now, this also speeds up the proof significantly in [#11759](https://github.com/leanprover-community/mathlib/pull/11759) (where the elaborator chooses the wrong subexpression to unfold first).
Elaboration time changed stayed about the same at about 300-350ms on master, and went from timeout to about 300ms on [#11759](https://github.com/leanprover-community/mathlib/pull/11759).

### [2022-05-11 08:00:01](https://github.com/leanprover-community/mathlib/commit/b75113a)
chore(set_theory/game/ordinal): Remove redundant namespaces ([#14039](https://github.com/leanprover-community/mathlib/pull/14039))

### [2022-05-11 06:01:29](https://github.com/leanprover-community/mathlib/commit/4231b68)
feat(data/list): add a few lemmas ([#14047](https://github.com/leanprover-community/mathlib/pull/14047))
* add `list.reverse_surjective` and `list.reverse_bijective`;
* add `list.chain_iff_forall₂`,
  `list.chain_append_singleton_iff_forall₂`, and `list.all₂_zip_with`.

### [2022-05-10 19:04:38](https://github.com/leanprover-community/mathlib/commit/df9683c)
feat(topology/algebra/infinite_sum): lemmas about `mul_opposite` ([#13674](https://github.com/leanprover-community/mathlib/pull/13674))

### [2022-05-10 17:00:25](https://github.com/leanprover-community/mathlib/commit/3ea573e)
refactor(algebra/{group,group_with_zero/basic): Delete lemmas generalized to division monoids ([#14042](https://github.com/leanprover-community/mathlib/pull/14042))
Delete the `group` and `group_with_zero` lemmas which have been made one-liners in [#14000](https://github.com/leanprover-community/mathlib/pull/14000).
Lemmas are renamed because
* one of the `group` or `group_with_zero` name has to go
* the new API should have a consistent naming convention
Lemma renames

### [2022-05-10 11:03:33](https://github.com/leanprover-community/mathlib/commit/e689611)
chore({data/{finset,set},order/filter}/pointwise): Reorganize files ([#14021](https://github.com/leanprover-community/mathlib/pull/14021))
Order the three files more similarly. The idea is to order things as:
* Arithmetic notation typeclasses, and lemmas that don't depend on algebraic structure for them:
  * `0` and `1`
  * `-` and `⁻¹`
  * `+` and `*`
  * `-` and `/`
* monoid-like instances, interleaved with the corresponding lemmas (some of them are used for the instances themselves, and more will be in the future)
* `•`
* `-ᵥ`
* scalar instances

### [2022-05-10 11:03:32](https://github.com/leanprover-community/mathlib/commit/45d2b52)
chore(analysis/normed_space/basic): reorder the `restrict_scalars` definitions ([#13995](https://github.com/leanprover-community/mathlib/pull/13995))
This also update the docstrings to make `normed_space.restrict_scalars` even scarier.
The instances here themselves haven't actually changed.

### [2022-05-10 11:03:31](https://github.com/leanprover-community/mathlib/commit/91489ac)
feat(algebra/module/submodule_bilinear): add `submodule.map₂`, generalizing `submodule.has_mul` ([#13709](https://github.com/leanprover-community/mathlib/pull/13709))
The motivation here is to be able to talk about combinations of submodules under other bilinear maps, such as the tensor product. This unifies the definitions of and lemmas about `submodule.has_mul` and `submodule.has_scalar'`.
The lemmas about `submodule.map₂` are copied verbatim from those for `mul`, and then adjusted slightly replacing `mul_zero` with `linear_map.map_zero` etc. I've then replaced the lemmas about `smul` with the `map₂` proofs where possible.
The lemmas about finiteness weren't possible to copy this way, as the proofs about `finset` multiplication are not generalized in a similar way. Someone else can copy these in a future PR.
This also adds `set.image2_eq_Union` to match `set.image_eq_Union`, and removes `submodule.union_eq_smul_set` which is neither about submodules nor about `union`, and instead is really just a copy of `set.image_eq_Union`

### [2022-05-10 08:56:43](https://github.com/leanprover-community/mathlib/commit/34f29db)
feat(topology/algebra/group): Division is an open map ([#14028](https://github.com/leanprover-community/mathlib/pull/14028))
A few missing lemmas about division in topological groups.

### [2022-05-10 08:56:42](https://github.com/leanprover-community/mathlib/commit/c892622)
move(order/synonym): Group `order_dual` and `lex` ([#13769](https://github.com/leanprover-community/mathlib/pull/13769))
Move `to_dual`, `of_dual`, `to_lex`, `of_lex` to a new file `order.synonym`. This does not change the import tree, because `order.lexicographic` had slightly higher imports than `order.order_dual`, but those weren't used for `lex` itself.

### [2022-05-10 08:02:09](https://github.com/leanprover-community/mathlib/commit/37c691f)
feat(analysis/convex/*): Convexity and subtraction ([#14015](https://github.com/leanprover-community/mathlib/pull/14015))
Now that we have a fair bit more pointwise operations on `set`, a few results can be (re)written using them. For example, existing lemmas about `add` and `neg` can be combined to give lemmas about `sub`.

### [2022-05-10 05:20:28](https://github.com/leanprover-community/mathlib/commit/5650366)
chore(.github/workflows): disable merge conflicts bot for now ([#14057](https://github.com/leanprover-community/mathlib/pull/14057))

### [2022-05-10 05:20:27](https://github.com/leanprover-community/mathlib/commit/153b20f)
chore(scripts): update nolints.txt ([#14056](https://github.com/leanprover-community/mathlib/pull/14056))
I am happy to remove some nolints for you!

### [2022-05-10 05:20:26](https://github.com/leanprover-community/mathlib/commit/b17070d)
fix(data/real/ennreal): style and golfing ([#14055](https://github.com/leanprover-community/mathlib/pull/14055))

### [2022-05-10 05:20:26](https://github.com/leanprover-community/mathlib/commit/87069e9)
chore(ring_theory/hahn_series): golf a proof ([#14054](https://github.com/leanprover-community/mathlib/pull/14054))

### [2022-05-10 03:35:32](https://github.com/leanprover-community/mathlib/commit/c5e0299)
feat(group_theory/subsemigroup/{center, centralizer}): define center and centralizer as subsemigroups ([#13627](https://github.com/leanprover-community/mathlib/pull/13627))
This defines the center and centralizers for semigroups. This is necessary so that we can do the same for non-unital semirings. 
- [x] depends on: [#12112](https://github.com/leanprover-community/mathlib/pull/12112) 
- [x] depends on: [#13903](https://github.com/leanprover-community/mathlib/pull/13903)

### [2022-05-09 20:46:25](https://github.com/leanprover-community/mathlib/commit/260d5ce)
feat(model_theory/semantics): Realizing restricted terms and formulas ([#14014](https://github.com/leanprover-community/mathlib/pull/14014))
Shows that realizing a restricted term or formula gives the same value as the unrestricted version.

### [2022-05-09 16:57:31](https://github.com/leanprover-community/mathlib/commit/98f2779)
refactor(number_theory/legendre_symbol/*): move section `general` from `quadratic_char.lean` into new file `auxiliary.lean` ([#14027](https://github.com/leanprover-community/mathlib/pull/14027))
This is a purely administrative step (in preparation of adding more files that may need some of the auxiliary results).
We move the collection of auxiliary results that constitute `section general` of `quadratic_char.lean` to a new file `auxiliary.lean` (and change the `import`s of `quadratic_char.lean` accordingly).
This new file is meant as a temporary place for these auxiliary results; when the refactor of `quadratic_reciprocity` is finished, they will be moved to appropriate files in mathlib.

### [2022-05-09 14:40:50](https://github.com/leanprover-community/mathlib/commit/31af0e8)
feat(model_theory/satisfiability): Definition of categorical theories ([#14038](https://github.com/leanprover-community/mathlib/pull/14038))
Defines that a first-order theory is `κ`-categorical when all models of cardinality `κ` are isomorphic.
Shows that all theories in the empty language are `κ`-categorical for all cardinals `κ`.

### [2022-05-09 14:40:49](https://github.com/leanprover-community/mathlib/commit/5d8b432)
feat(model_theory/language_map): Cardinality of languages with constants ([#13981](https://github.com/leanprover-community/mathlib/pull/13981))
`first_order.language.card_with_constants` shows that the cardinality of `L[[A]]` is `L.card + # A`.

### [2022-05-09 14:40:47](https://github.com/leanprover-community/mathlib/commit/4eb76a7)
refactor(set_theory/ordinal/arithmetic): Rename theorems to match `nat.log` API ([#12733](https://github.com/leanprover-community/mathlib/pull/12733))
We match the API for `ordinal.log` with that of `nat.log`.

### [2022-05-09 12:58:30](https://github.com/leanprover-community/mathlib/commit/00cec55)
feat(linear_algebra/affine_space/independent): add characterisation of affine independence for modules ([#14043](https://github.com/leanprover-community/mathlib/pull/14043))

### [2022-05-09 12:58:29](https://github.com/leanprover-community/mathlib/commit/1fef515)
chore(analysis/normed_space/basic): add short-circuit instance to obtain module structure over reals ([#14013](https://github.com/leanprover-community/mathlib/pull/14013))

### [2022-05-09 12:58:28](https://github.com/leanprover-community/mathlib/commit/4da939b)
feat(probability_theory/cond_count): use the counting measure to describe probability in the elementary sense ([#13484](https://github.com/leanprover-community/mathlib/pull/13484))

### [2022-05-09 12:18:53](https://github.com/leanprover-community/mathlib/commit/5397ac0)
chore(ring_theory/hahn_series): remove redundant instances ([#14045](https://github.com/leanprover-community/mathlib/pull/14045))
Both of these instances can be proved `by apply_instance`

### [2022-05-09 11:26:03](https://github.com/leanprover-community/mathlib/commit/c43486e)
feat(category_theory/limits): allow (co)limits over lower universes in algebraic categories ([#13990](https://github.com/leanprover-community/mathlib/pull/13990))
I'm concerned about the new universe annotations required in places. It was not so impossible to add them when proofs broke, but the proofs might have been hard to construct in the first place ....

### [2022-05-09 11:25:59](https://github.com/leanprover-community/mathlib/commit/ad244dd)
feat(ring_theory/dedekind_domain/adic_valuation): extend valuation ([#13462](https://github.com/leanprover-community/mathlib/pull/13462))
We extend the `v`-adic valuation on a Dedekind domain `R` to its field of fractions `K` and prove some basic properties. We define the completion of `K` with respect to this valuation, as well as its ring of integers, and provide some topological instances.

### [2022-05-09 09:20:59](https://github.com/leanprover-community/mathlib/commit/fc64096)
feat(topology/algebra/infinite_sum): summable on subtype iff ([#14032](https://github.com/leanprover-community/mathlib/pull/14032))
A summable version of the `has_sum` lemma previously (the `tsum` version is already present)

### [2022-05-09 09:20:58](https://github.com/leanprover-community/mathlib/commit/d55a654)
feat(order/*): Order constructions under `to_dual`/`of_dual` ([#13788](https://github.com/leanprover-community/mathlib/pull/13788))
A few missing lemmas about `of_dual` and `to_dual`.

### [2022-05-09 09:20:56](https://github.com/leanprover-community/mathlib/commit/1d9d573)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `has_mul` `has_zero` `preorder` ([#13296](https://github.com/leanprover-community/mathlib/pull/13296))

### [2022-05-09 08:31:21](https://github.com/leanprover-community/mathlib/commit/b38aee4)
feat(analysis/special_functions): differentiability of Gamma function ([#13000](https://github.com/leanprover-community/mathlib/pull/13000))
Third instalment of my Gamma-function project (following [#12917](https://github.com/leanprover-community/mathlib/pull/12917) and [#13156](https://github.com/leanprover-community/mathlib/pull/13156)). This PR adds the proof that the Gamma function is complex-analytic, away from the poles at non-positive integers.

### [2022-05-09 06:03:23](https://github.com/leanprover-community/mathlib/commit/bf8db9b)
feat(analysis/normed_space/matrix_exponential): lemmas about the matrix exponential ([#13520](https://github.com/leanprover-community/mathlib/pull/13520))
This checks off "Matrix Exponential" from the undergrad TODO list, by providing the majority of the "obvious" statements about matrices over a real normed algebra. Combining this PR with what is already in mathlib, we have:
* `exp 0 = 1`
* `exp (A + B) = exp A * exp B` when `A` and `B` commute
* `exp (n • A) = exp A ^ n`
* `exp (z • A) = exp A ^ z`
* `exp (-A) = (exp A)⁻¹`
* `exp (U * D * ↑(U⁻¹)) = U * exp D * ↑(U⁻¹)`
* `exp Aᵀ = (exp A)ᵀ`
* `exp Aᴴ = (exp A)ᴴ`
* `A * exp B = exp B * A`  if `A * B = B * A`
* `exp (diagonal v) = diagonal (exp v)`
* `exp (block_diagonal v) = block_diagonal (exp v)`
* `exp (block_diagonal' v) = block_diagonal' (exp v)`
Still missing are:
* `det (exp A) = exp (trace A)`
* `exp A` can be written a weighted sum of powers of `A : matrix n n R` less than `fintype.card n` (an extension of [`matrix.pow_eq_aeval_mod_charpoly`](https://leanprover-community.github.io/mathlib_docs/linear_algebra/matrix/charpoly/coeff.html#matrix.pow_eq_aeval_mod_charpoly))
The proofs in this PR may seem small, but they had a substantial dependency chain: https://github.com/leanprover-community/mathlib/projects/16.
It turns out that there's always more missing glue than you think there is.

### [2022-05-09 02:37:50](https://github.com/leanprover-community/mathlib/commit/77c86ba)
rename(imo/imo1972_b2 → imo/imo1972_q5): Fix file name ([#14037](https://github.com/leanprover-community/mathlib/pull/14037))

### [2022-05-09 02:37:49](https://github.com/leanprover-community/mathlib/commit/8412f1f)
feat(representation_theory/invariants): invariants of `lin_hom` are representation morphisms ([#14012](https://github.com/leanprover-community/mathlib/pull/14012))

### [2022-05-09 02:37:47](https://github.com/leanprover-community/mathlib/commit/594ceda)
feat(analysis/normed_space/exponential): Generalize `field` lemmas to `division_ring` ([#13997](https://github.com/leanprover-community/mathlib/pull/13997))
This generalizes the lemmas about `exp 𝕂 𝕂` to lemmas about `exp 𝕂 𝔸` where `𝔸` is a `division_ring`.
This moves the lemmas down to the appropriate division_ring sections, and replaces the word `field` with `div` in their names, since `division_ring` is a mouthful, and really the name reflects the use of `/` in the definition.

### [2022-05-09 02:37:47](https://github.com/leanprover-community/mathlib/commit/afec1d7)
fix(tactics/alias): Make docstring calculation available to to_additive ([#13968](https://github.com/leanprover-community/mathlib/pull/13968))
PR [#13944](https://github.com/leanprover-community/mathlib/pull/13944) fixed the docstrings for iff-style aliases, but because of
code duplication I added in [#13330](https://github.com/leanprover-community/mathlib/pull/13330) this did not apply to aliases
introduced by `to_additive`. This fixes that.

### [2022-05-09 02:37:45](https://github.com/leanprover-community/mathlib/commit/34b61e3)
chore(algebra/regular/*): generalisation linter ([#13955](https://github.com/leanprover-community/mathlib/pull/13955))

### [2022-05-09 02:37:44](https://github.com/leanprover-community/mathlib/commit/5253153)
feat(algebra/category/Module/basic): `iso.hom_congr`agrees with `linear_equiv.arrow_congr` ([#13954](https://github.com/leanprover-community/mathlib/pull/13954))

### [2022-05-09 02:37:43](https://github.com/leanprover-community/mathlib/commit/4f386e6)
feat(set_theory/pgame/birthday): Birthdays of ordinals ([#13714](https://github.com/leanprover-community/mathlib/pull/13714))

### [2022-05-09 02:37:42](https://github.com/leanprover-community/mathlib/commit/1e8f381)
feat(algebraic_topology/dold_kan): defining some null homotopic maps ([#13085](https://github.com/leanprover-community/mathlib/pull/13085))

### [2022-05-09 00:34:40](https://github.com/leanprover-community/mathlib/commit/bf6e13b)
refactor(algebra/{group,group_with_zero/basic): Generalize lemmas to division monoids ([#14000](https://github.com/leanprover-community/mathlib/pull/14000))
Generalize `group` and `group_with_zero` lemmas to `division_monoid`. We do not actually delete the original lemmas but make them one-liners from the new ones. The next PR will then delete the old lemmas and perform the renames in all files.
Lemmas are renamed because
* one of the `group` or `group_with_zero` name has to go
* the new API should have a consistent naming convention
Pre-emptive lemma renames

### [2022-05-08 19:06:53](https://github.com/leanprover-community/mathlib/commit/449ba97)
refactor(data/nat/log): Golf + improved theorem names ([#14019](https://github.com/leanprover-community/mathlib/pull/14019))
Other than golfing and moving a few things around, our main changes are:
- rename `log_le_log_of_le` to `log_mono_right`, analogous renames elsewhere.
- add `lt_pow_iff_log_lt` and a `clog` analog.

### [2022-05-08 18:01:58](https://github.com/leanprover-community/mathlib/commit/163ef61)
feat(topology/algebra/infinite_sum): add `tsum_star` ([#13999](https://github.com/leanprover-community/mathlib/pull/13999))
These lemmas names are copied from `tsum_neg` and friends.
As a result, `star_exp` can be golfed and generalized.

### [2022-05-08 18:01:58](https://github.com/leanprover-community/mathlib/commit/dd16a83)
fix(topology/algebra/module/weak_dual): fix namespace issue, add a few extra lemmas ([#13407](https://github.com/leanprover-community/mathlib/pull/13407))
This PR fixes a namespace issue in `weak_dual`, to ensure lemmas with names like `eval_continuous` are appropriately namespaced. Also, lemmas about continuity of the evaluation map have been copied from `weak_bilin` to `weak_dual`.

### [2022-05-08 16:31:29](https://github.com/leanprover-community/mathlib/commit/69c07a4)
feat(linear_algebra/linear_pmap): `mk_span_singleton` of the same point ([#14029](https://github.com/leanprover-community/mathlib/pull/14029))
One more lemma about `mk_span_singleton'` and slightly better lemma names.

### [2022-05-08 16:31:28](https://github.com/leanprover-community/mathlib/commit/6a5d17e)
feat(measure_theory/integral): a few more integral lemmas ([#14025](https://github.com/leanprover-community/mathlib/pull/14025))

### [2022-05-08 15:55:36](https://github.com/leanprover-community/mathlib/commit/e330694)
feat(analysis/p_series): explicit bounds on sums of the form 1/j^2 ([#13851](https://github.com/leanprover-community/mathlib/pull/13851))

### [2022-05-08 14:02:33](https://github.com/leanprover-community/mathlib/commit/79ffb55)
chore(algebra/category/CommRing=>Ring): rename ([#14022](https://github.com/leanprover-community/mathlib/pull/14022))
This folder was originally named `algebra/category/CommRing/` because it only handled the commutative case. That's largely no longer the case, so we should rename the folder.

### [2022-05-08 12:55:28](https://github.com/leanprover-community/mathlib/commit/3478a2a)
feat(probability/ident_distrib): identically distributed random variables ([#14024](https://github.com/leanprover-community/mathlib/pull/14024))

### [2022-05-08 06:24:13](https://github.com/leanprover-community/mathlib/commit/0c64b3d)
feat(algebra/category/Module): biproducts ([#13908](https://github.com/leanprover-community/mathlib/pull/13908))
Following the same pattern for `AddCommGroup`, create the instance for biproducts in` Module R`, and check they are isomorphic to the usual construction.

### [2022-05-08 04:50:21](https://github.com/leanprover-community/mathlib/commit/ce0dc83)
feat(set_theory/ordinal/basic): Supremum indexed over an empty / unique type ([#13735](https://github.com/leanprover-community/mathlib/pull/13735))
This PR contains the following changes:
- The lemmas `sup_unique`, `bsup_one`, `lsub_unique`, `blsub_one`.
- `congr` lemmas for `bsup` and `blsub`
- Arguments like `o = 0` are removed as the `congr` lemmas now handle this.
- `a + 1` is changed to `a.succ` in some lemmas (for better rewriting).

### [2022-05-07 22:21:48](https://github.com/leanprover-community/mathlib/commit/3a0eb4b)
chore(logic/relation): Dot notation on `well_founded.trans_gen` ([#14016](https://github.com/leanprover-community/mathlib/pull/14016))

### [2022-05-07 22:21:47](https://github.com/leanprover-community/mathlib/commit/e190225)
feat(data/rat/meta_defs, meta/expr): rat.to_pexpr and int.to_pexpr ([#14002](https://github.com/leanprover-community/mathlib/pull/14002))

### [2022-05-07 20:15:08](https://github.com/leanprover-community/mathlib/commit/e0dd300)
feat(algebra/{invertible + group_power/lemmas}): taking `inv_of` (⅟_) is injective ([#14011](https://github.com/leanprover-community/mathlib/pull/14011))
Besides the lemma stated in the description, I also made explicit an argument that was implicit in a different lemma and swapped the arguments of `invertible_unique` in order to get the typeclass assumptions before some non-typeclass assumptions.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/inv_of_inj)

### [2022-05-07 15:50:10](https://github.com/leanprover-community/mathlib/commit/0e494af)
chore(order/*): Less `order_dual` abuse ([#14008](https://github.com/leanprover-community/mathlib/pull/14008))
Sanitize uses of `order_dual` by inserting the required `of_dual` and `to_dual` instead of type-ascripting. Also remove some uses which were not necessary. Those dated from the time where we did not have antitone functions.

### [2022-05-07 15:50:09](https://github.com/leanprover-community/mathlib/commit/5166765)
chore(order/filter/pointwise): Better definitional unfolding ([#13941](https://github.com/leanprover-community/mathlib/pull/13941))
Tweak pointwise operation definitions to make them easier to work with:
* `1` is now `pure 1` instead of `principal 1`. This changes defeq.
* Binary operations unfold to the set operation instead exposing a bare `set.image2` (`obtain ⟨t₁, t₂, h₁, h₂, h⟩ : s ∈ f * g` now gives `h : t₁ * t₂ ⊆ s` instead of `h : set.image2 (*) t₁ t₂ ⊆ s`. This does not change defeq.

### [2022-05-07 11:59:00](https://github.com/leanprover-community/mathlib/commit/cf65daf)
feat(probability/variance): define the variance of a random variable, prove its basic properties ([#13912](https://github.com/leanprover-community/mathlib/pull/13912))

### [2022-05-07 09:57:54](https://github.com/leanprover-community/mathlib/commit/c247622)
feat(group_theory/group_action/units): simp lemma for scalar action of `is_unit.unit h` ([#14006](https://github.com/leanprover-community/mathlib/pull/14006))

### [2022-05-07 09:57:53](https://github.com/leanprover-community/mathlib/commit/9134a8e)
feat(combinatorics/simple_graph/hasse): Hasse diagram and path graph ([#13959](https://github.com/leanprover-community/mathlib/pull/13959))
Define the Hasse diagram of an order and the path graph on `n` vertices as the Hasse diagram of `fin n`.

### [2022-05-07 09:57:51](https://github.com/leanprover-community/mathlib/commit/b2aa27e)
feat(analysis/calculus/deriv): generalize some lemmas ([#13575](https://github.com/leanprover-community/mathlib/pull/13575))
The types of scalar and codomain can be different now.
For example, these lemmas can be used for `f : ℝ → ℂ` `f' : ℝ →L[ℝ] ℂ` now.

### [2022-05-07 08:20:10](https://github.com/leanprover-community/mathlib/commit/f8bc097)
feat(algebra/module/linear_map): `Rᵐᵒᵖ` is isomorphic to `module.End R R` ([#13931](https://github.com/leanprover-community/mathlib/pull/13931))
This PR adds the canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to
`module.End R R` for a (semi)ring `R`, given by the right multiplication.

### [2022-05-07 07:07:16](https://github.com/leanprover-community/mathlib/commit/559f58b)
feat(order/filter): add a few lemmas ([#13985](https://github.com/leanprover-community/mathlib/pull/13985))
* weaken assumptions of `filter.has_antitone_basis.tendsto` from `[semilattice_sup ι] [nonempty ι]` to `[preorder ι]`;
* add `filter.has_antitone_basis.tendsto`, `filter.has_antitone_basis.mem`, `filter.has_antitone_basis.tendsto_small_sets`.

### [2022-05-07 04:45:56](https://github.com/leanprover-community/mathlib/commit/ca1375a)
refactor(algebra/order/monoid_lemmas): reorder the file ([#13492](https://github.com/leanprover-community/mathlib/pull/13492))
Just like in `algebra/order/monoid_lemmas_zero_lt`, sort by algebraic assumptions and order assumptions first, then put similar lemmas together.
It would be simpler to find duplicates, missing lemmas, and inconsistencies. (There are so many!)

### [2022-05-07 04:10:25](https://github.com/leanprover-community/mathlib/commit/5789c63)
chore(scripts): update nolints.txt ([#14004](https://github.com/leanprover-community/mathlib/pull/14004))
I am happy to remove some nolints for you!

### [2022-05-07 00:43:46](https://github.com/leanprover-community/mathlib/commit/275dabf)
feat(order/atoms): is_atomic_of_order_bot_lt_well_founded ([#13967](https://github.com/leanprover-community/mathlib/pull/13967))

### [2022-05-06 20:39:04](https://github.com/leanprover-community/mathlib/commit/dcd452d)
feat(analysis/locally_convex/with_seminorms): characterization of the topology induced by seminorms in terms of `𝓝 0` ([#13547](https://github.com/leanprover-community/mathlib/pull/13547))
This shows that a topology is induced by the family of seminorms `p` iff `𝓝 0 = ⨅ i, (𝓝 0).comap (p i)`, which allows to use the extensive filter and topology library (see e.g. [#13549](https://github.com/leanprover-community/mathlib/pull/13549)).

### [2022-05-06 19:31:54](https://github.com/leanprover-community/mathlib/commit/10721ba)
feat(topology/algebra/module/basic): basic topological properties of quotient modules ([#13433](https://github.com/leanprover-community/mathlib/pull/13433))
More precisely, we prove that : 
* if `M` is a topological module and `S` is a submodule of `M`, then `M ⧸ S` is a topological module
* furthermore, if `S` is closed, then `M ⧸ S` is regular (hence T2) 
- [x] depends on: [#13278](https://github.com/leanprover-community/mathlib/pull/13278) 
- [x] depends on: [#13401](https://github.com/leanprover-community/mathlib/pull/13401)

### [2022-05-06 18:45:20](https://github.com/leanprover-community/mathlib/commit/8f116f4)
feat(ring_theory/localization): generalize lemmas from `comm_ring` to `comm_semiring` ([#13994](https://github.com/leanprover-community/mathlib/pull/13994))
This PR does not add new stuffs, but removes several subtractions from the proofs.

### [2022-05-06 18:45:19](https://github.com/leanprover-community/mathlib/commit/27e105d)
chore(analysis/normed_space/exponential): Make the `𝔸` argument implicit ([#13986](https://github.com/leanprover-community/mathlib/pull/13986))
`exp 𝕂 𝔸` is now just `exp 𝕂`.
This also renames two lemmas that refer to this argument in their name to no longer do so.
In a few places we have to add type annotations where they weren't needed before, but nowhere do we need to resort to `@`.

### [2022-05-06 18:45:18](https://github.com/leanprover-community/mathlib/commit/eea16dc)
feat(number_theory/legendre_symbol/*): add results on value at -1 ([#13978](https://github.com/leanprover-community/mathlib/pull/13978))
This PR adds code expressing the value of the quadratic character at -1 of a finite field of odd characteristic as χ₄ applied to the cardinality of the field. This is then also done for the Legendre symbol.
Additional changes:
* two helper lemmas `odd_mod_four` and `finite_field.even_card_of_char_two` that are needed
* some API lemmas for χ₄
* write `euler_criterion` and `exists_sq_eq_neg_one_iff` in terms of `is_square`; simplify the proof of the latter using the general result for quadratic characters

### [2022-05-06 18:45:17](https://github.com/leanprover-community/mathlib/commit/dfe1897)
feat(data/polynomial/laurent): laurent polynomials -- defs and some API ([#13784](https://github.com/leanprover-community/mathlib/pull/13784))
I broke off the initial part of [#13415](https://github.com/leanprover-community/mathlib/pull/13415) into this initial segment, leaving the rest of the PR as depending on this one.

### [2022-05-06 16:39:40](https://github.com/leanprover-community/mathlib/commit/58d83ed)
feat(tactic/lint/misc): adding a linter that flags iffs with explicit variables on both sides ([#11606](https://github.com/leanprover-community/mathlib/pull/11606))

### [2022-05-06 15:42:43](https://github.com/leanprover-community/mathlib/commit/863a167)
docs(ring_theory/localization/ideal): fix an unused name ([#13992](https://github.com/leanprover-community/mathlib/pull/13992))

### [2022-05-06 15:42:42](https://github.com/leanprover-community/mathlib/commit/db5c2a6)
chore(data/zmod/basic.lean): change order of arguments of `zmod.nat_cast_mod` for consistency ([#13988](https://github.com/leanprover-community/mathlib/pull/13988))
As discussed [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60zmod.2Enat_cast_mod.60.20vs.20.60zmod.2Eint_cast_mod.60), this changes the order of arguments in `zmod.nat_cast_mod` to be compatible with `zmod.int_cast_mod`.

### [2022-05-06 15:42:40](https://github.com/leanprover-community/mathlib/commit/40bedd6)
refactor(set_theory/game/pgame): Remove `pgame.omega` ([#13960](https://github.com/leanprover-community/mathlib/pull/13960))
This barely had any API to begin with. Thanks to `ordinal.to_pgame`, it is now entirely redundant.

### [2022-05-06 15:42:39](https://github.com/leanprover-community/mathlib/commit/c9f5cee)
feat(set_theory/game/pgame): Add remark on relabelings ([#13732](https://github.com/leanprover-community/mathlib/pull/13732))

### [2022-05-06 14:58:58](https://github.com/leanprover-community/mathlib/commit/ba627bc)
feat(measure_theory/function/conditional_expectation): induction over Lp functions which are strongly measurable wrt a sub-sigma-algebra ([#13129](https://github.com/leanprover-community/mathlib/pull/13129))

### [2022-05-06 12:51:04](https://github.com/leanprover-community/mathlib/commit/fe0c4cd)
docs(data/polynomial/algebra_map): fix a typo in a doc-string ([#13989](https://github.com/leanprover-community/mathlib/pull/13989))
The doc-string talks about `comm_ring`, while the lemma uses `comm_semiring`.  I aligned the two to the weaker one!

### [2022-05-06 12:51:03](https://github.com/leanprover-community/mathlib/commit/f6c030f)
feat(linear_algebra/matrix/nonsingular_inverse): inverse of a diagonal matrix is diagonal ([#13827](https://github.com/leanprover-community/mathlib/pull/13827))
The main results are `is_unit (diagonal v) ↔ is_unit v` and `(diagonal v)⁻¹ = diagonal (ring.inverse v)`.
This also generalizes `invertible.map` to `monoid_hom_class`.

### [2022-05-06 12:03:00](https://github.com/leanprover-community/mathlib/commit/e4d3d33)
feat(probability/stopping): add properties of the measurable space generated by a stopping time ([#13909](https://github.com/leanprover-community/mathlib/pull/13909))
- add lemmas stating that various sets are measurable with respect to that space
- describe the sigma algebra generated by the minimum of two stopping times
- use the results to generalize `is_stopping_time.measurable_set_eq_const` from nat to first countable linear orders and rename it to `is_stopping_time.measurable_space_eq'` to have a name similar to `is_stopping_time.measurable_set_eq`.

### [2022-05-06 10:42:54](https://github.com/leanprover-community/mathlib/commit/f033937)
feat(topology/algebra/monoid): add missing `has_continuous_const_smul` instances ([#13987](https://github.com/leanprover-community/mathlib/pull/13987))
This makes an argument to `exp` redundant.

### [2022-05-06 10:42:53](https://github.com/leanprover-community/mathlib/commit/97c4d4e)
feat(analysis/asymptotics/asymptotics): add `is_O.exists_mem_basis` ([#13973](https://github.com/leanprover-community/mathlib/pull/13973))

### [2022-05-06 10:07:19](https://github.com/leanprover-community/mathlib/commit/d989305)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_class` `partial_order` / `linear_order` ([#13377](https://github.com/leanprover-community/mathlib/pull/13377))

### [2022-05-06 10:07:18](https://github.com/leanprover-community/mathlib/commit/1675b78)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_one_class` `partial_order` ([#13375](https://github.com/leanprover-community/mathlib/pull/13375))

### [2022-05-06 09:15:39](https://github.com/leanprover-community/mathlib/commit/95413e2)
feat(measure_theory/group/*): various lemmas about invariant measures ([#13539](https://github.com/leanprover-community/mathlib/pull/13539))
* Make the `measurable_equiv` argument to `measure_preserving.symm` explicit. This argument is cannot always be deduced from the other explicit arguments (which can be seen form the changes in `src/measure_theory/constructions/pi.lean`).
* From the sphere eversion project
* Required for convolutions

### [2022-05-06 06:39:57](https://github.com/leanprover-community/mathlib/commit/ebac9f0)
feat(analysis/special_functions/trigonometric): add a lemma ([#13975](https://github.com/leanprover-community/mathlib/pull/13975))
Add a lemma needed for [#13178](https://github.com/leanprover-community/mathlib/pull/13178)

### [2022-05-06 06:03:17](https://github.com/leanprover-community/mathlib/commit/faf1690)
feat(model_theory/*): Any theory with infinite models has arbitrarily large models ([#13980](https://github.com/leanprover-community/mathlib/pull/13980))
Defines the theory `distinct_constants_theory`, indicating that a set of constants are distinct.
Uses that theory to show that any theory with an infinite model has models of arbitrarily large cardinality.

### [2022-05-06 01:59:37](https://github.com/leanprover-community/mathlib/commit/f0eded9)
chore(algebra/ring/idempotents): golf iff_eq_zero_or_one ([#13977](https://github.com/leanprover-community/mathlib/pull/13977))

### [2022-05-05 23:51:54](https://github.com/leanprover-community/mathlib/commit/151933d)
feat(algebra/group/defs): Division monoids ([#13860](https://github.com/leanprover-community/mathlib/pull/13860))
Introduce what I call division monoids. Those are monoids `α` with a pseudo-inverse `⁻¹ : α → α ` and a pseudo-division `/ : α → α → α` respecting:
* `a / b = a * b⁻¹`
* `a⁻¹⁻¹ = a`
* `(a * b)⁻¹ = b⁻¹ * a⁻¹`
* `a * b = 1 → a⁻¹ = b`
This made-up algebraic structure has two uses:
* Deduplicate lemmas between `group` and `group_with_zero`. Almost all lemmas which are literally duplicated (same conclusion, same assumptions except for `group` vs `group_with_zero`) generalize to division monoids.
* Give access to lemmas for pointwise operations: `set α`, `finset α`, `filter α`, `submonoid α`, `subgroup α`, etc... all are division monoids when `α` is. In some sense, they are very close to being groups, the only obstruction being that `s / s ≠ 1` in general. Hence any identity which is true in a group/group with zero is also true in those pointwise monoids, if no cancellation is involved.

### [2022-05-05 22:29:30](https://github.com/leanprover-community/mathlib/commit/c62dfe6)
feat(model_theory/skolem): Downward Löwenheim–Skolem ([#13723](https://github.com/leanprover-community/mathlib/pull/13723))
Proves the Downward Löwenheim–Skolem theorem:  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of cardinality `κ`.

### [2022-05-05 20:53:20](https://github.com/leanprover-community/mathlib/commit/91cc3f0)
feat(linear_algebra/basic): ker of a linear map equals ker of the corresponding group hom ([#13858](https://github.com/leanprover-community/mathlib/pull/13858))

### [2022-05-05 19:41:55](https://github.com/leanprover-community/mathlib/commit/c12536a)
fix(gitpod): correct command name ([#13976](https://github.com/leanprover-community/mathlib/pull/13976))
`leanpkg config` doesn't exist, it's `leanpkg configure`.
@b-mehta tricked me in https://github.com/leanprover-community/mathlib/pull/13949#issuecomment-1117589670

### [2022-05-05 17:30:45](https://github.com/leanprover-community/mathlib/commit/73e5dad)
feat(analysis/special_functions/exp): add limits of `exp z` as `re z → ±∞` ([#13974](https://github.com/leanprover-community/mathlib/pull/13974))

### [2022-05-05 16:19:12](https://github.com/leanprover-community/mathlib/commit/54af9e9)
fix(topology/algebra/infinite_sum): `tsum_neg` doesn't need `summable` ([#13950](https://github.com/leanprover-community/mathlib/pull/13950))
Both sides are 0 in the not-summable case.

### [2022-05-05 14:55:41](https://github.com/leanprover-community/mathlib/commit/ec44f45)
feat(data/matrix/basic): even more lemmas about `conj_transpose` and `smul` ([#13970](https://github.com/leanprover-community/mathlib/pull/13970))
It turns out none of the lemmas in the previous [#13938](https://github.com/leanprover-community/mathlib/pull/13938) were the ones I needed.

### [2022-05-05 13:11:01](https://github.com/leanprover-community/mathlib/commit/420fabf)
chore(analysis/normed_space/exponential): replace `1/x` with `x⁻¹` ([#13971](https://github.com/leanprover-community/mathlib/pull/13971))
Note that `one_div` makes `⁻¹` the simp-normal form.

### [2022-05-05 13:11:00](https://github.com/leanprover-community/mathlib/commit/03f5ac9)
feat(category_theory/simple): simple_iff_subobject_is_simple_order ([#13969](https://github.com/leanprover-community/mathlib/pull/13969))

### [2022-05-05 13:10:59](https://github.com/leanprover-community/mathlib/commit/929c901)
refactor(ring_theory/*): Remove unnecessary commutativity assumptions ([#13966](https://github.com/leanprover-community/mathlib/pull/13966))
This replaces `[comm_ring R]` or `[comm_semiring R]` with `[ring R]` or `[semiring R]`, without changing any proofs.

### [2022-05-05 13:10:58](https://github.com/leanprover-community/mathlib/commit/8e0ab16)
feat(polynomial/cyclotomic/basic): ɸ_pⁱ irreducible → ɸ_pʲ irreducible for j ≤ i ([#13952](https://github.com/leanprover-community/mathlib/pull/13952))

### [2022-05-05 11:55:59](https://github.com/leanprover-community/mathlib/commit/057e028)
feat(linear_algebra/finite_dimensional): surjective_of_nonzero_of_finrank_eq_one ([#13961](https://github.com/leanprover-community/mathlib/pull/13961))

### [2022-05-05 11:55:58](https://github.com/leanprover-community/mathlib/commit/da06587)
feat(linear_algebra): A-linear maps between finite dimensional vector spaces over k are finite dimensional ([#13934](https://github.com/leanprover-community/mathlib/pull/13934))

### [2022-05-05 09:52:28](https://github.com/leanprover-community/mathlib/commit/4dfbcac)
feat({data/{finset,set},order/filter}/pointwise): More basic API ([#13899](https://github.com/leanprover-community/mathlib/pull/13899))
More basic lemmas about pointwise operations on `set`/`finset`/`filter`. Also make the three APIs more consistent with each other.

### [2022-05-05 07:41:38](https://github.com/leanprover-community/mathlib/commit/f820671)
ci(gitpod): do not rerun get-cache if a workspace is reloaded ([#13949](https://github.com/leanprover-community/mathlib/pull/13949))
Instead, only run it at workspace start. This prevents it clobbering local builds created with `lean --make src` or similar.
I have no idea why the `. /home/gitpod/.profile` line is there, so I've left it to run in the same phase as before.

### [2022-05-05 07:41:37](https://github.com/leanprover-community/mathlib/commit/6970129)
chore(algebra/group/units): add a lemma about is_unit on a coerced unit ([#13947](https://github.com/leanprover-community/mathlib/pull/13947))

### [2022-05-05 07:41:36](https://github.com/leanprover-community/mathlib/commit/bd944fe)
chore(linear_algebra/free_module): fix name in doc ([#13942](https://github.com/leanprover-community/mathlib/pull/13942))

### [2022-05-05 07:41:35](https://github.com/leanprover-community/mathlib/commit/4f7603c)
chore(data/matrix/basic): add more lemmas about `conj_transpose` and `smul` ([#13938](https://github.com/leanprover-community/mathlib/pull/13938))
Unfortunately the `star_module` typeclass is of no help here; see [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Is.20star_module.20sensible.20for.20non-commutative.20rings.3F/near/257272767) for some discussion.
In the meantime, this adds the lemmas for the most frequent special cases.

### [2022-05-05 07:41:33](https://github.com/leanprover-community/mathlib/commit/7eacca3)
feat(analysis/normed/normed_field): limit of `∥a * x∥` as `∥x∥ → ∞` ([#13819](https://github.com/leanprover-community/mathlib/pull/13819))
These lemmas should use `bornology.cobounded` but we don't have an instance `pseudo_metric_space α -> bornology α` yet.

### [2022-05-05 05:36:23](https://github.com/leanprover-community/mathlib/commit/03fbe7d)
Update CODE_OF_CONDUCT.md ([#13965](https://github.com/leanprover-community/mathlib/pull/13965))
deleted one character (duplicate space)

### [2022-05-05 05:36:22](https://github.com/leanprover-community/mathlib/commit/63875ea)
chore(scripts): update nolints.txt ([#13964](https://github.com/leanprover-community/mathlib/pull/13964))
I am happy to remove some nolints for you!

### [2022-05-05 05:36:21](https://github.com/leanprover-community/mathlib/commit/116435d)
feat(tactic/alias): fix alias docstrings for implications from iffs ([#13944](https://github.com/leanprover-community/mathlib/pull/13944))
Now they say for instance:
```lean
le_inv_mul_of_mul_le : ∀ {α : Type u} [_inst_1 : group α] [_inst_2 : has_le α] [_inst_3 : covariant_class α α has_mul.mul has_le.le] {a b c : α}, a * b ≤ c → b ≤ a⁻¹ * c
**Alias** of the reverse direction of `le_inv_mul_iff_mul_le`.
```
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60alias.60.20issue.20in.20algebra.2Eorder.2Egroup/near/281158569

### [2022-05-05 05:36:20](https://github.com/leanprover-community/mathlib/commit/524793d)
feat(representation_theory): Action V G is rigid whenever V is ([#13738](https://github.com/leanprover-community/mathlib/pull/13738))

### [2022-05-05 05:36:19](https://github.com/leanprover-community/mathlib/commit/b1da074)
feat(data/sum/basic): Shortcuts for the ternary sum of types ([#13678](https://github.com/leanprover-community/mathlib/pull/13678))
Define `sum3.in₀`, `sum3.in₁`, `sum3.in₂`, shortcut patterns for pattern-matching on a ternary sum of types.

### [2022-05-05 03:36:27](https://github.com/leanprover-community/mathlib/commit/0c9b726)
feat(algebra/group/{pi, opposite}): add missing pi and opposite defs for `mul_hom` ([#13956](https://github.com/leanprover-community/mathlib/pull/13956))
The declaration names and the contents of these definitions are all copied from the corresponding ones for `monoid_hom`.

### [2022-05-05 02:21:58](https://github.com/leanprover-community/mathlib/commit/5078119)
feat(data/matrix/block): add `matrix.block_diag` and `matrix.block_diag'` ([#13918](https://github.com/leanprover-community/mathlib/pull/13918))
`matrix.block_diag` is to `matrix.block_diagonal` as `matrix.diag` is to `matrix.diagonal`.
As well as the basic arithmetic lemmas and bundling, this also adds continuity lemmas.
These definitions are primarily an auxiliary construction to prove `matrix.tsum_block_diagonal`, and `matrix.tsum_block_diagonal'`, which are really the main goal of this PR.

### [2022-05-05 02:21:58](https://github.com/leanprover-community/mathlib/commit/50fd3d6)
feat(analysis/special_functions/log/monotone): add lemmas ([#13848](https://github.com/leanprover-community/mathlib/pull/13848))
Adds a few lemmas regarding tonality of `log x / x ^ a`, and puts them in a new file, along with previous results.

### [2022-05-05 00:25:32](https://github.com/leanprover-community/mathlib/commit/1e18935)
docs(algebra/ring/opposite): fix docstring for `ring_hom.from_opposite` ([#13957](https://github.com/leanprover-community/mathlib/pull/13957))

### [2022-05-05 00:25:31](https://github.com/leanprover-community/mathlib/commit/3650936)
feat(representation_theory/Action): lemma about isomorphisms in `Action G V` ([#13951](https://github.com/leanprover-community/mathlib/pull/13951))

### [2022-05-05 00:25:30](https://github.com/leanprover-community/mathlib/commit/9b245e2)
feat(analysis/convex/integral): drop an assumption, add a version ([#13920](https://github.com/leanprover-community/mathlib/pull/13920))
* add `convex.set_average_mem_closure`;
* drop `is_closed s` assumption in `convex.average_mem_interior_of_set`;
* add `ae_eq_const_or_norm_average_lt_of_norm_le_const`, a version of `ae_eq_const_or_norm_integral_lt_of_norm_le_const` for average.

### [2022-05-04 22:19:39](https://github.com/leanprover-community/mathlib/commit/f8c303e)
refactor(order/filter/pointwise): Localize instances ([#13898](https://github.com/leanprover-community/mathlib/pull/13898))
Localize pointwise `filter` instances into the `pointwise` locale, as is done for `set` and `finset`.

### [2022-05-04 22:19:38](https://github.com/leanprover-community/mathlib/commit/627f81b)
feat(group_theory/order_of_element): The index-th power lands in the subgroup ([#13890](https://github.com/leanprover-community/mathlib/pull/13890))
The PR adds a lemma stating `g ^ index H ∈ H`. I had to restate `G` to avoid the fintype assumption on `G`.

### [2022-05-04 22:19:37](https://github.com/leanprover-community/mathlib/commit/5696275)
feat(data/list/big_operators): add `list.sublist.prod_le_prod'` etc ([#13879](https://github.com/leanprover-community/mathlib/pull/13879))
* add `list.forall₂.prod_le_prod'`, `list.sublist.prod_le_prod'`, and `list.sublist_forall₂.prod_le_prod'`;
* add their additive versions;
* upgrade `list.forall₂_same` to an `iff`.

### [2022-05-04 20:04:22](https://github.com/leanprover-community/mathlib/commit/9503f73)
feat(linear_algebra/dual): dual of a finite free module is finite free ([#13896](https://github.com/leanprover-community/mathlib/pull/13896))

### [2022-05-04 20:04:21](https://github.com/leanprover-community/mathlib/commit/eb1a566)
refactor(set_theory/game/ordinal): Improve API ([#13878](https://github.com/leanprover-community/mathlib/pull/13878))
We change our former equivalence `o.out.α ≃ o.to_pgame.left_moves` to an equivalence `{o' // o' < o} ≃ o.to_pgame.left_moves`. This makes two proofs much simpler. 
We also add a simple missing lemma, `to_pgame_equiv_iff`.

### [2022-05-04 20:04:20](https://github.com/leanprover-community/mathlib/commit/28568bd)
feat(set_theory/game/nim): Add basic API ([#13857](https://github.com/leanprover-community/mathlib/pull/13857))

### [2022-05-04 20:04:19](https://github.com/leanprover-community/mathlib/commit/a80e568)
feat(logic/equiv/set): equivalences between all preimages gives an equivalence of domains ([#13853](https://github.com/leanprover-community/mathlib/pull/13853))

### [2022-05-04 20:04:18](https://github.com/leanprover-community/mathlib/commit/edf6cef)
feat(set_theory/game/nim): `nim 0` is a relabelling of `0` and `nim 1` is a relabelling of `star` ([#13846](https://github.com/leanprover-community/mathlib/pull/13846))

### [2022-05-04 20:04:17](https://github.com/leanprover-community/mathlib/commit/fd8474f)
feat(algebra/ring/idempotents): Introduce idempotents ([#13830](https://github.com/leanprover-community/mathlib/pull/13830))

### [2022-05-04 20:04:15](https://github.com/leanprover-community/mathlib/commit/91c0ef8)
feat(analysis/normed_space/weak_dual): add the rest of Banach-Alaoglu theorem ([#9862](https://github.com/leanprover-community/mathlib/pull/9862))
The second of two parts to add the Banach-Alaoglu theorem about the compactness of the closed unit ball (and more generally polar sets of neighborhoods of the origin) of the dual of a normed space in the weak-star topology.
This second half is about the embedding of the weak dual of a normed space into a (big) product of the ground fields, and the required compactness statements from Tychonoff's theorem. In particular it contains the actual Banach-Alaoglu theorem.
Co-Authored-By: Yury Kudryashov <urkud@urkud.name>

### [2022-05-04 17:58:32](https://github.com/leanprover-community/mathlib/commit/90d6f27)
ci(workflows/dependent-issues): run once every 15 mins, instead of on every merged PR ([#13940](https://github.com/leanprover-community/mathlib/pull/13940))

### [2022-05-04 17:58:30](https://github.com/leanprover-community/mathlib/commit/aabcd89)
chore(analysis/analytic_composition): weaken some typeclass arguments ([#13924](https://github.com/leanprover-community/mathlib/pull/13924))
There's no need to do a long computation to show the multilinear_map is bounded, when continuity follows directly from the definition.
This deletes `comp_along_composition_aux`, and moves the lemmas about the norm of `comp_along_composition` further down the file so as to get the lemmas with weaker typeclass requirements out of the way first.
The norm proofs are essentially unchanged.

### [2022-05-04 17:58:29](https://github.com/leanprover-community/mathlib/commit/209bb5d)
feat(set_theory/game/{pgame, basic}): Add more order lemmas ([#13807](https://github.com/leanprover-community/mathlib/pull/13807))

### [2022-05-04 17:58:28](https://github.com/leanprover-community/mathlib/commit/3152982)
feat(representation/Rep): linear structures ([#13782](https://github.com/leanprover-community/mathlib/pull/13782))
Make `Rep k G` a `k`-linear (and `k`-linear monoidal) category.

### [2022-05-04 17:58:27](https://github.com/leanprover-community/mathlib/commit/0009ffb)
refactor(linear_algebra/charpoly): split file to reduce imports ([#13778](https://github.com/leanprover-community/mathlib/pull/13778))
While working on representation theory I was annoyed to find that essentially all of field theory was being transitively imported (causing lots of unnecessary recompilation). This improves the situation slightly.

### [2022-05-04 17:58:26](https://github.com/leanprover-community/mathlib/commit/dd4590a)
refactor(algebra/restrict_scalars): remove global instance on module_orig ([#13759](https://github.com/leanprover-community/mathlib/pull/13759))
The global instance was conceptually wrong, unnecessary (after avoiding a hack in algebra/lie/base_change.lean), and wreaking havoc in [#13713](https://github.com/leanprover-community/mathlib/pull/13713).

### [2022-05-04 17:58:24](https://github.com/leanprover-community/mathlib/commit/abcd601)
fix(src/tactic/alias): Teach `get_alias_target` about `alias f ↔ a b` ([#13742](https://github.com/leanprover-community/mathlib/pull/13742))
the `get_alias_target` function in `alias.lean` is used by the
`to_additive` command to add the “Alias of …” docstring when creating an
additive version of an existing alias (this was [#13330](https://github.com/leanprover-community/mathlib/pull/13330)).
But `get_alias_target` did not work for `alias f ↔ a b`. This fixes it
by extending the `alias_attr` map to not just store whether a defintion
is an alias, but also what it is an alias of. Much more principled than
trying to reconstruct the alias target from the RHS of the alias
definition.
Note that `alias` currently says “Alias of `foo_iff`” even though it’s
really an alias of `foo_iff.mp`. This is an existing bug, not fixed in
this PR – the effect is just that this “bug” will uniformly apply to
additive lemmas as well.
Hopefully will get rid of plenty of nolint.txt entries, and create
better docs.
Also improve the test file for the linter significantly.

### [2022-05-04 15:53:31](https://github.com/leanprover-community/mathlib/commit/0038a04)
feat(data/int/cast): int cast division lemmas ([#13929](https://github.com/leanprover-community/mathlib/pull/13929))
Adds lemmas for passing int cast through division, and renames the nat versions from `nat.cast_dvd` to `nat.cast_div`. 
Also some golf.

### [2022-05-04 15:53:30](https://github.com/leanprover-community/mathlib/commit/4602370)
feat(set_theory/game/birthday): More basic lemmas on birthdays ([#13729](https://github.com/leanprover-community/mathlib/pull/13729))

### [2022-05-04 15:53:29](https://github.com/leanprover-community/mathlib/commit/60ad844)
feat(group_theory/complement): API lemmas relating `range_mem_transversals` and `to_equiv` ([#13694](https://github.com/leanprover-community/mathlib/pull/13694))
This PR adds an API lemma relating `range_mem_left_transversals` (the main way of constructing left transversals) and `mem_left_transversals.to_equiv` (one of the main constructions from left transversals), and a similar lemma relating the right versions.

### [2022-05-04 15:53:28](https://github.com/leanprover-community/mathlib/commit/923ae0b)
feat(group_theory/free_group): is_free_group via `free_group X ≃* G` ([#13633](https://github.com/leanprover-community/mathlib/pull/13633))
The previous definition of the `is_free_group` class was defined via the universal
property of free groups, which is intellectually pleasing, but
technically annoying, due to the universe problems of quantifying over
“all other groups” in the definition. To work around them, many
definitions had to be duplicated.
This changes the definition of `is_free_group` to contain an isomorphism
between the `free_group` over the generator and `G`. It also moves this
class into `free_group.lean`, so that it can be found more easily.
Relevant Zulip thread:
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universe.20levels.20for.20is_free_group>
A previous attempt at reforming `is_free_group` to unbundle the set
of generators (`is_freely_generated_by G X`) is on branch
`joachim/is_freely_generated_by`, but it wasn't very elegant to use in some places.

### [2022-05-04 15:53:27](https://github.com/leanprover-community/mathlib/commit/552a470)
feat(number_theory/cyclotomic/rat): the ring of integers of cyclotomic fields. ([#13585](https://github.com/leanprover-community/mathlib/pull/13585))
We compute the ring of integers of a `p ^ n`-th cyclotomic extension of `ℚ`.
From flt-regular

### [2022-05-04 15:53:26](https://github.com/leanprover-community/mathlib/commit/e716139)
feat(algebra/homology/Module): API for complexes of modules ([#12622](https://github.com/leanprover-community/mathlib/pull/12622))
API for homological complexes in `Module R`.

### [2022-05-04 15:53:24](https://github.com/leanprover-community/mathlib/commit/a7c5097)
feat(set_theory/cardinal/cofinality): Cofinality of normal functions ([#12384](https://github.com/leanprover-community/mathlib/pull/12384))
If `f` is normal and `a` is limit, then `cof (f a) = cof a`. We use this to golf `cof_add` from 24 lines down to 6.

### [2022-05-04 15:53:23](https://github.com/leanprover-community/mathlib/commit/d565adb)
feat(analysis/convex/topology): Separating by convex sets ([#11458](https://github.com/leanprover-community/mathlib/pull/11458))
When `s` is compact, `t` is closed and both are convex, we can find disjoint open convex sets containing `s` and `t`.

### [2022-05-04 14:57:36](https://github.com/leanprover-community/mathlib/commit/32320a1)
feat(measure_theory/integral/lebesgue): speed up a proof ([#13946](https://github.com/leanprover-community/mathlib/pull/13946))

### [2022-05-04 11:10:47](https://github.com/leanprover-community/mathlib/commit/ceca8d7)
fix(ring_theory/polynomial/basic): fix unexpected change of an implicit parameter ([#13935](https://github.com/leanprover-community/mathlib/pull/13935))
Fix unexpected change of an implicit parameter in the previous PR([#13800](https://github.com/leanprover-community/mathlib/pull/13800)).
Fix docstring.

### [2022-05-04 11:10:46](https://github.com/leanprover-community/mathlib/commit/53c79d5)
feat(linear_algebra/span): add `finite_span_is_compact_element` ([#13901](https://github.com/leanprover-community/mathlib/pull/13901))
This PR adds `finite_span_is_compact_element`, which extends `singleton_span_is_compact_element` to the spans of finite subsets.
This will be useful e.g. when proving the existence of a maximal submodule of a finitely generated module.

### [2022-05-04 11:10:45](https://github.com/leanprover-community/mathlib/commit/a057441)
feat(order/basic): Notation for `order_dual` ([#13798](https://github.com/leanprover-community/mathlib/pull/13798))
Define `αᵒᵈ` as notation for `order_dual α` and replace current uses.
[Zulip poll](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20order_dual/near/280629129)

### [2022-05-04 11:10:44](https://github.com/leanprover-community/mathlib/commit/402e564)
feat(linear_algebra/prod): linear version of prod_map ([#13751](https://github.com/leanprover-community/mathlib/pull/13751))

### [2022-05-04 11:10:43](https://github.com/leanprover-community/mathlib/commit/e1f00bc)
feat(order/well_founded): Well founded relations are asymmetric and irreflexive ([#13692](https://github.com/leanprover-community/mathlib/pull/13692))

### [2022-05-04 11:10:42](https://github.com/leanprover-community/mathlib/commit/6c7b880)
feat(algebra/module/torsion): torsion ideal, decomposition lemma ([#13414](https://github.com/leanprover-community/mathlib/pull/13414))
Defines the torsion ideal of an element in a module, and also shows a decomposition lemma for torsion modules.

### [2022-05-04 11:10:40](https://github.com/leanprover-community/mathlib/commit/e24f7f7)
move(set_theory/ordinal/{arithmetic → fixed_points}): Move `nfp` ([#13315](https://github.com/leanprover-community/mathlib/pull/13315))
That way, it belong with the other functions about fixed points.

### [2022-05-04 07:51:01](https://github.com/leanprover-community/mathlib/commit/1a86249)
feat(measure_theory/function/l1_space): add `integrable_smul_measure` ([#13922](https://github.com/leanprover-community/mathlib/pull/13922))
* add `integrable_smul_measure`, an `iff` version of
  `integrable.smul_measure`;
* add `integrable_average`, an `iff` version of `integrable.to_average`.

### [2022-05-04 07:51:00](https://github.com/leanprover-community/mathlib/commit/af4c6c8)
chore(ring_theory/polynomial/basic): golf polynomial_not_is_field ([#13919](https://github.com/leanprover-community/mathlib/pull/13919))

### [2022-05-04 07:50:59](https://github.com/leanprover-community/mathlib/commit/d0efe25)
feat(data/finset/prod): diag of union ([#13916](https://github.com/leanprover-community/mathlib/pull/13916))
Lemmas about diag and off diag in relation to simple finset constructions.

### [2022-05-04 07:50:58](https://github.com/leanprover-community/mathlib/commit/098ab17)
feat(category_theory/simple): nonzero morphisms to/from a simple are epi/mono ([#13905](https://github.com/leanprover-community/mathlib/pull/13905))

### [2022-05-04 07:50:57](https://github.com/leanprover-community/mathlib/commit/455393d)
refactor(group_theory/{submonoid, subsemigroup}/{center, centralizer}): move set.center and set.centralizer into subsemigroup ([#13903](https://github.com/leanprover-community/mathlib/pull/13903))
This moves `set.center` and `set.centralizer` (the center and centralizers for a magma) into `group_theory/subsemigroup/{center, centralizer}` so that we can define the center and centralizers for semigroups in [#13627](https://github.com/leanprover-community/mathlib/pull/13627).

### [2022-05-04 07:50:55](https://github.com/leanprover-community/mathlib/commit/e6b8499)
feat(ring_theory/valuation/valuation_subring): Adds some equivalent conditions for equivalence of valuations ([#13895](https://github.com/leanprover-community/mathlib/pull/13895))

### [2022-05-04 07:50:54](https://github.com/leanprover-community/mathlib/commit/6d37006)
feat(data/list/basic): add `list.cons_diff` ([#13892](https://github.com/leanprover-community/mathlib/pull/13892))

### [2022-05-04 07:50:53](https://github.com/leanprover-community/mathlib/commit/269bc85)
feat(analysis/matrix): add `frobenius_norm_conj_transpose` ([#13883](https://github.com/leanprover-community/mathlib/pull/13883))
This also moves the existing lemmas about the elementwise norm to the same file.

### [2022-05-04 07:50:52](https://github.com/leanprover-community/mathlib/commit/d537897)
feat(category_theory/simple): simple objects are indecomposable ([#13882](https://github.com/leanprover-community/mathlib/pull/13882))
Remarkably tedious.

### [2022-05-04 07:50:51](https://github.com/leanprover-community/mathlib/commit/1afdaf9)
feat(linear_algebra/trace): more general versions of `trace_mul_comm` and `trace_conj` ([#13874](https://github.com/leanprover-community/mathlib/pull/13874))

### [2022-05-04 07:50:50](https://github.com/leanprover-community/mathlib/commit/517aa8b)
feat(topology/algebra/star): continuity of `star` ([#13855](https://github.com/leanprover-community/mathlib/pull/13855))
This adds the obvious instances for `pi`, `prod`, `units`, `mul_opposite`, `real`, `complex`, `is_R_or_C`, and `matrix`.
We already had a `continuous_star` lemma, but it had stronger typeclass assumptions.
This resolves multiple TODO comments.

### [2022-05-04 07:50:49](https://github.com/leanprover-community/mathlib/commit/35c8980)
feat(analysis/asymptotics/specific_asymptotics): Cesaro averaging preserves convergence ([#13825](https://github.com/leanprover-community/mathlib/pull/13825))

### [2022-05-04 07:50:48](https://github.com/leanprover-community/mathlib/commit/6e00330)
feat(algebra/squarefree): relate squarefree on naturals to factorization ([#13816](https://github.com/leanprover-community/mathlib/pull/13816))
Also moves `nat.two_le_iff` higher up the hierarchy since it's an elementary lemma and give it a more appropriate type.
The lemma `squarefree_iff_prime_sq_not_dvd` has been deleted because it's a duplicate of a lemma which is already earlier in the same file.

### [2022-05-04 07:50:47](https://github.com/leanprover-community/mathlib/commit/ba4bf54)
feat(set_theory/game/pgame): Add more congr lemmas ([#13808](https://github.com/leanprover-community/mathlib/pull/13808))

### [2022-05-04 07:50:46](https://github.com/leanprover-community/mathlib/commit/85657f1)
feat(algebra/category/FinVect): has finite limits ([#13793](https://github.com/leanprover-community/mathlib/pull/13793))

### [2022-05-04 07:50:45](https://github.com/leanprover-community/mathlib/commit/e3d38ed)
feat(algebra/hom/non_unital_alg): some constructions for `prod` ([#13785](https://github.com/leanprover-community/mathlib/pull/13785))

### [2022-05-04 07:50:44](https://github.com/leanprover-community/mathlib/commit/9015d2a)
refactor(set_theory/game/pgame): Redefine `subsequent` ([#13752](https://github.com/leanprover-community/mathlib/pull/13752))
We redefine `subsequent` as `trans_gen is_option`. This gives a much nicer induction principle than the previous one, and allows us to immediately prove well-foundedness.

### [2022-05-04 07:50:43](https://github.com/leanprover-community/mathlib/commit/b337b92)
feat(model_theory/satisfiability): A union of a directed family of satisfiable theories is satisfiable ([#13750](https://github.com/leanprover-community/mathlib/pull/13750))
Proves `first_order.language.Theory.is_satisfiable_directed_union_iff` - the union of a directed family of theories is satisfiable if and only if all of the theories in the family are satisfiable.

### [2022-05-04 07:50:40](https://github.com/leanprover-community/mathlib/commit/51d8167)
feat(model_theory/elementary_maps): The elementary diagram of a structure ([#13724](https://github.com/leanprover-community/mathlib/pull/13724))
Defines the elementary diagram of a structure - the theory consisting of all sentences with parameters it satisfies.
Defines the canonical elementary embedding of a structure into any model of its elementary diagram.

### [2022-05-04 07:50:39](https://github.com/leanprover-community/mathlib/commit/319d502)
refactor(linear_algebra/*): more generalisations ([#13668](https://github.com/leanprover-community/mathlib/pull/13668))
Many further generalisations from `field` to `division_ring` in the linear algebra library.
This PR changes some proofs; it's not just relaxing hypotheses.

### [2022-05-04 07:50:38](https://github.com/leanprover-community/mathlib/commit/36c5faa)
feat(set_theory/game/pgame): Tweak `pgame.mul` API ([#13651](https://github.com/leanprover-community/mathlib/pull/13651))
We modify the API for `pgame.mul` in two ways:
- `left_moves_mul` and `right_moves_mul` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.

### [2022-05-04 07:50:37](https://github.com/leanprover-community/mathlib/commit/bd23639)
feat(topology/bornology): add more instances ([#13621](https://github.com/leanprover-community/mathlib/pull/13621))

### [2022-05-04 07:50:35](https://github.com/leanprover-community/mathlib/commit/2402b4d)
feat(set_theory/game/pgame): Tweak `pgame.neg` API ([#13617](https://github.com/leanprover-community/mathlib/pull/13617))
We modify the API for `pgame.neg` in various ways: 
- `left_moves_neg` and `right_moves_neg` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.
We also golf a few theorems.

### [2022-05-04 06:42:38](https://github.com/leanprover-community/mathlib/commit/58de2a0)
chore(analysis): use nnnorm notation everywhere ([#13930](https://github.com/leanprover-community/mathlib/pull/13930))
This was done with a series of ad-hoc regular expressions, then cleaned up by hand.

### [2022-05-04 06:42:36](https://github.com/leanprover-community/mathlib/commit/6f3426c)
chore(number_theory/legendre_symbol/quadratic_char): golf some proofs ([#13926](https://github.com/leanprover-community/mathlib/pull/13926))

### [2022-05-04 06:42:35](https://github.com/leanprover-community/mathlib/commit/171825a)
chore(algebra/order/floor): missing simp lemmas on floor of nat and int ([#13904](https://github.com/leanprover-community/mathlib/pull/13904))

### [2022-05-04 05:51:33](https://github.com/leanprover-community/mathlib/commit/4d0b630)
feat(category_theory/bicategory/coherence_tactic): coherence tactic for bicategories ([#13417](https://github.com/leanprover-community/mathlib/pull/13417))
This PR extends the coherence tactic for monoidal categories [#13125](https://github.com/leanprover-community/mathlib/pull/13125) to bicategories. The setup is the same as for monoidal case except for the following : we normalize 2-morphisms before running the coherence tactic. This normalization is achieved by the set of simp lemmas in `whisker_simps` defined in `coherence_tactic.lean`.
As a test of the tactic in the real world, I have proved several properties of adjunction in bicategories in [#13418](https://github.com/leanprover-community/mathlib/pull/13418). Unfortunately some proofs cause timeout, so it seems that we need to speed up the coherence tactic in the future.

### [2022-05-04 05:16:36](https://github.com/leanprover-community/mathlib/commit/c1f329d)
feat(data/zmod/quotient): The quotient `<a>/stab(b)` is cyclic of order `minimal_period ((+ᵥ) a) b` ([#13722](https://github.com/leanprover-community/mathlib/pull/13722))
This PR adds an isomorphism stating that the quotient `<a>/stab(b)` is cyclic of order `minimal_period ((+ᵥ) a) b`.
There is also a multiplicative version, but it is easily proved from the additive version, so I'll PR the multiplicative version afterwards.

### [2022-05-04 04:20:31](https://github.com/leanprover-community/mathlib/commit/a2a873f)
chore(scripts): update nolints.txt ([#13932](https://github.com/leanprover-community/mathlib/pull/13932))
I am happy to remove some nolints for you!

### [2022-05-04 01:08:00](https://github.com/leanprover-community/mathlib/commit/dd58438)
feat(set_theory/game/short): Birthday of short games ([#13875](https://github.com/leanprover-community/mathlib/pull/13875))
We prove that a short game has a finite birthday. We also clean up the file somewhat.

### [2022-05-04 00:13:27](https://github.com/leanprover-community/mathlib/commit/fc3de19)
feat(ring_theory/ideal/local_ring): generalize lemmas to semirings ([#13471](https://github.com/leanprover-community/mathlib/pull/13471))
What is essentially new is the proof of `local_ring.of_surjective` and `local_ring.is_unit_or_is_unit_of_is_unit_add`.
- I changed the definition of local ring to `local_ring.of_is_unit_or_is_unit_of_add_one`, which is reminiscent of the definition before the recent change in [#13341](https://github.com/leanprover-community/mathlib/pull/13341). The equivalence of the previous definition is essentially given by `local_ring.is_unit_or_is_unit_of_is_unit_add`. The choice of the definition is insignificant here because they are all equivalent, but I think the choice here is better for the default constructor because this condition is "weaker" than e.g. `local_ring.of_non_units_add` in some sense.
- The proof of `local_ring.of_surjective` needs `[is_local_ring_hom f]`, which was not necessary for commutative rings in the previous proof. So the new version here is not a genuine generalization of the previous version. The previous version was  renamed to `local_ring.of_surjective'`.

### [2022-05-03 23:37:38](https://github.com/leanprover-community/mathlib/commit/6c0580a)
fix(.docker/*): update elan URL ([#13928](https://github.com/leanprover-community/mathlib/pull/13928))
These are hopefully the last occurrences of the URL that was breaking things earlier today. cf. [#13906](https://github.com/leanprover-community/mathlib/pull/13906)

### [2022-05-03 22:34:05](https://github.com/leanprover-community/mathlib/commit/fd65159)
feat(topology/metric_space/basic): golf, avoid unfold ([#13923](https://github.com/leanprover-community/mathlib/pull/13923))
* Don't use `unfold` in `nnreal.pseudo_metric_space`.
* Golf some proofs.

### [2022-05-03 21:57:27](https://github.com/leanprover-community/mathlib/commit/de07131)
feat(measure_theory/integral/torus_integral): torus integral and its properties ([#12892](https://github.com/leanprover-community/mathlib/pull/12892))
Define a generalized torus map and prove some basic properties.
Define the torus integral and the integrability of functions on a generalized torus, and prove lemmas about them.

### [2022-05-03 20:33:18](https://github.com/leanprover-community/mathlib/commit/9c0dfcd)
doc(order/countable_dense_linear_order): Fix minor mistake ([#13921](https://github.com/leanprover-community/mathlib/pull/13921))
I wrongfully removed some instances of the word "linear" in [#12928](https://github.com/leanprover-community/mathlib/pull/12928). This is in fact used as a hypothesis.

### [2022-05-03 19:18:51](https://github.com/leanprover-community/mathlib/commit/5cfb8db)
refactor(ring_theory/jacobson_ideal): generalize lemmas to non-commutative rings ([#13865](https://github.com/leanprover-community/mathlib/pull/13865))
The main change here is that the order of multiplication has been adjusted slightly in `mem_jacobson_iff`and `exists_mul_sub_mem_of_sub_one_mem_jacobson`. In the commutative case this doesn't matter anyway.
All the other changes are just moving lemmas between sections, the statements of no lemmas other than those two have been changed. No lemmas have been added or removed.
The lemmas about `is_unit` and quotients don't generalize as easily, so I've not attempted to touch those; that would require some mathematical insight, which is out of scope for this PR!

### [2022-05-03 18:19:54](https://github.com/leanprover-community/mathlib/commit/16157f2)
chore(topology/continuous_function/bounded): generalize from `normed_*` to `semi_normed_*` ([#13915](https://github.com/leanprover-community/mathlib/pull/13915))
Every single lemma in this file generalized, apart from the ones that transferred a `normed_*` instance which obviously need the stronger assumption.
`dist_zero_of_empty` was the only lemma that actually needed reproving from scratch, all the other affected proofs are just split between two instances.

### [2022-05-03 18:19:53](https://github.com/leanprover-community/mathlib/commit/bd1d935)
feat(number_theory/legendre_symbol/): add some lemmas ([#13831](https://github.com/leanprover-community/mathlib/pull/13831))
This adds essentially two lemmas on quadratic characters:
* `quadratic_char_neg_one_iff_not_is_square`, which says that the quadratic character takes the value `-1` exactly on non-squares, and
* `quadratic_char_number_of_sqrts`. which says that the number of square roots of `a : F` is `quadratic_char F a + 1`.
It also adds the corresponding statements, `legendre_sym_eq_neg_one_iff` and `legendre_sym_number_of_sqrts`, for the Legendre symbol.

### [2022-05-03 16:29:01](https://github.com/leanprover-community/mathlib/commit/7d28753)
chore(normed_space/weak_dual): generalize `normed_group` to `semi_normed_group` ([#13914](https://github.com/leanprover-community/mathlib/pull/13914))
This almost halves the time this file takes to build, and is more general too.

### [2022-05-03 16:29:00](https://github.com/leanprover-community/mathlib/commit/8688753)
feat(set_theory/game/basic): Inline instances ([#13813](https://github.com/leanprover-community/mathlib/pull/13813))
We also add a few missing instances.

### [2022-05-03 16:28:59](https://github.com/leanprover-community/mathlib/commit/5c433d0)
feat(algebra/big_operators/basic): `prod_list_count` and `prod_list_count_of_subset` ([#13370](https://github.com/leanprover-community/mathlib/pull/13370))
Add 
`prod_list_count (l : list α) : l.prod = ∏ x in l.to_finset, (x ^ (l.count x))`
and
`prod_list_count_of_subset (l : list α) (s : finset α) (hs : l.to_finset ⊆ s) : l.prod = ∏ x in s, x ^ (l.count x)`
as counterparts of `prod_multiset_count` and `prod_multiset_count_of_subset` (whose proofs are then golfed using the new lemmas).

### [2022-05-03 14:29:31](https://github.com/leanprover-community/mathlib/commit/40b5952)
doc(analysis/matrix): fix broken LaTeX ([#13910](https://github.com/leanprover-community/mathlib/pull/13910))

### [2022-05-03 14:29:30](https://github.com/leanprover-community/mathlib/commit/1c4d2b7)
feat(linear_algebra/matrix/trace): add `trace_conj_transpose` ([#13888](https://github.com/leanprover-community/mathlib/pull/13888))

### [2022-05-03 14:29:29](https://github.com/leanprover-community/mathlib/commit/0f8d7a9)
feat(order/omega_complete_partial_order): make `continuous_hom.prod.apply` continuous ([#13833](https://github.com/leanprover-community/mathlib/pull/13833))
Previous it was defined as `apply : (α →𝒄 β) × α →o β` and the comment
said that it would make sense to define it as a continuous function, but
we need an instance for `α →𝒄 β` first. But then let’s just define that
instance first, and then define `apply : (α →𝒄 β) × α →𝒄 β` as you would
expect.
Also rephrases `lemma ωSup_ωSup` differently now that `apply` is
continuous.

### [2022-05-03 14:29:28](https://github.com/leanprover-community/mathlib/commit/475a533)
feat(topology/algebra/module/basic): A continuous linear functional is open ([#13829](https://github.com/leanprover-community/mathlib/pull/13829))

### [2022-05-03 14:29:27](https://github.com/leanprover-community/mathlib/commit/4cea0a8)
move(data/pi/*): Group `pi` files ([#13826](https://github.com/leanprover-community/mathlib/pull/13826))
Move `data.pi` to `data.pi.algebra` and `order.pilex` to `data.pi.lex`.

### [2022-05-03 14:29:25](https://github.com/leanprover-community/mathlib/commit/8a5b4a7)
feat(analysis/special_functions/complex/arg): lemmas about `arg z` and `±(π / 2)` ([#13821](https://github.com/leanprover-community/mathlib/pull/13821))

### [2022-05-03 14:29:24](https://github.com/leanprover-community/mathlib/commit/2f38ccb)
chore(data/matrix/basic): add lemmas about powers of matrices ([#13815](https://github.com/leanprover-community/mathlib/pull/13815))
Shows that:
* natural powers commute with `transpose`, `conj_transpose`, `diagonal`, `block_diagonal`, and `block_diagonal'`.
* integer powers commute with `transpose`, and `conj_transpose`.

### [2022-05-03 14:29:24](https://github.com/leanprover-community/mathlib/commit/36b5341)
feat(ring_theory/polynomial/basic): reduce assumptions, golf ([#13800](https://github.com/leanprover-community/mathlib/pull/13800))
There is some reorder, so the diff is a bit large. Sorry for that.

### [2022-05-03 14:29:22](https://github.com/leanprover-community/mathlib/commit/6d2788c)
feat(analysis/calculus/cont_diff): cont_diff_succ_iff_fderiv_apply ([#13797](https://github.com/leanprover-community/mathlib/pull/13797))
* Prove that a map is `C^(n+1)` iff it is differentiable and all its directional derivatives in all points are `C^n`. 
* Also some supporting lemmas about `continuous_linear_equiv`.
* We only manage to prove this when the domain is finite dimensional.
* Prove one direction of `cont_diff_on_succ_iff_fderiv_within` with fewer assumptions
* From the sphere eversion project
Co-authored by: Patrick Massot [patrick.massot@u-psud.fr](mailto:patrick.massot@u-psud.fr)
Co-authored by: Oliver Nash [github@olivernash.org](mailto:github@olivernash.org)

### [2022-05-03 14:29:21](https://github.com/leanprover-community/mathlib/commit/234b3df)
feat(analysis/normed_space): lemmas about continuous bilinear maps ([#13522](https://github.com/leanprover-community/mathlib/pull/13522))
* Define `continuous_linear_map.map_sub₂` and friends, similar to the lemmas for `linear_map`. 
* Rename `continuous_linear_map.map_add₂` to `continuous_linear_map.map_add_add`
* Two comments refer to `continuous.comp₂`, which will be added in [#13423](https://github.com/leanprover-community/mathlib/pull/13423) (but there is otherwise no dependency on this PR).
* Define `precompR` and `precompL`, which will be used to compute the derivative of a convolution.
* From the sphere eversion project
* Required for convolutions

### [2022-05-03 12:18:57](https://github.com/leanprover-community/mathlib/commit/3b971a7)
feat(data/zmod/basic): Add `zmod.cast_sub_one` ([#13889](https://github.com/leanprover-community/mathlib/pull/13889))
This PR adds `zmod.cast_sub_one`, an analog of `fin.coe_sub_one`. Unfortunately, the proof is a bit long. But maybe it can be golfed?

### [2022-05-03 12:18:56](https://github.com/leanprover-community/mathlib/commit/78c86e1)
chore(data/nat/totient): golf three lemmas ([#13886](https://github.com/leanprover-community/mathlib/pull/13886))
Golf the proofs of `totient_le`, `totient_lt`, and `totient_pos`

### [2022-05-03 12:18:55](https://github.com/leanprover-community/mathlib/commit/9f818ce)
feat(set_theory/ordinal_basic): `o.out.α` is equivalent to the ordinals below `o` ([#13876](https://github.com/leanprover-community/mathlib/pull/13876))

### [2022-05-03 12:18:54](https://github.com/leanprover-community/mathlib/commit/82b9c42)
feat(set_theory/game/nim): Mark many lemmas as `simp` ([#13844](https://github.com/leanprover-community/mathlib/pull/13844))

### [2022-05-03 12:18:53](https://github.com/leanprover-community/mathlib/commit/e104992)
chore(order/*): Replace total partial orders by linear orders ([#13839](https://github.com/leanprover-community/mathlib/pull/13839))
`partial_order α` + `is_total α (≤)` has no more theorems than `linear_order α`  but is nonetheless used in some places. This replaces those uses by `linear_order α` or `complete_linear_order α`. Also make implicit one argument of `finset.lt_inf'_iff` and friends.

### [2022-05-03 12:18:52](https://github.com/leanprover-community/mathlib/commit/f6cb9be)
fix(data/complex/basic): make complex addition computable again ([#13837](https://github.com/leanprover-community/mathlib/pull/13837))
This was fixed once before in [#8166](https://github.com/leanprover-community/mathlib/pull/8166) (5f2358c43b769b334f3986a96565e606fe5bccec), but a new noncomputable shortcut appears if your file has more imports.

### [2022-05-03 12:18:51](https://github.com/leanprover-community/mathlib/commit/b07c0f7)
feat(set_theory/game/basic): Add `le_rfl` on games ([#13814](https://github.com/leanprover-community/mathlib/pull/13814))

### [2022-05-03 12:18:50](https://github.com/leanprover-community/mathlib/commit/72816f9)
feat(data/real/nnreal): add `nnreal.forall` and `nnreal.exists` ([#13774](https://github.com/leanprover-community/mathlib/pull/13774))

### [2022-05-03 12:18:49](https://github.com/leanprover-community/mathlib/commit/7931ba4)
feat(order/conditionally_complete_lattice): Simp theorems ([#13756](https://github.com/leanprover-community/mathlib/pull/13756))
We remove `supr_unit` and `infi_unit` since, thanks to [#13741](https://github.com/leanprover-community/mathlib/pull/13741), they can be proven by `simp`.

### [2022-05-03 11:43:28](https://github.com/leanprover-community/mathlib/commit/65cad41)
chore(.github/workflows): use separate secret token for dependent issues ([#13902](https://github.com/leanprover-community/mathlib/pull/13902))

### [2022-05-03 11:03:24](https://github.com/leanprover-community/mathlib/commit/1c39267)
ci(elan): update dead repository URLs ([#13906](https://github.com/leanprover-community/mathlib/pull/13906))
`Kha/elan` is redirected by github to `leanprover/elan`, but seemingly with a cache that is delayed.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/install.20elan.20fails.20in.20CI/near/280981154)

### [2022-05-02 21:37:01](https://github.com/leanprover-community/mathlib/commit/ca1551c)
feat(data/finset/n_ary): Binary image of finsets ([#13718](https://github.com/leanprover-community/mathlib/pull/13718))
Define `finset.image₂`, the binary map of finsets. Golf `data.finset.pointwise` using it.

### [2022-05-02 20:22:14](https://github.com/leanprover-community/mathlib/commit/1741207)
feat(analysis/normed_space/exponential): `Aeᴮ = eᴮA` if `AB = BA` ([#13881](https://github.com/leanprover-community/mathlib/pull/13881))
This commit shows that the exponenential commutes if the exponent does.
This generalizes a previous weaker result.

### [2022-05-02 19:32:06](https://github.com/leanprover-community/mathlib/commit/c44091f)
feat(data/zmod/basic): Generalize `zmod.card` ([#13887](https://github.com/leanprover-community/mathlib/pull/13887))
This PR generalizes `zmod.card` from assuming `[fact (0 < n)]` to assuming `[fintype (zmod n)]`.
Note that the latter was already part of the statement, but was previously deduced from the instance `instance fintype : Π (n : ℕ) [fact (0 < n)], fintype (zmod n)` on line 80.

### [2022-05-02 19:32:04](https://github.com/leanprover-community/mathlib/commit/2b0aeda)
feat(measure/function/l*_space): a sample of useful lemmas on L^p spaces ([#13823](https://github.com/leanprover-community/mathlib/pull/13823))
Used in [#13690](https://github.com/leanprover-community/mathlib/pull/13690)

### [2022-05-02 17:28:50](https://github.com/leanprover-community/mathlib/commit/aa921ef)
docs(set_theory/game/pgame): Fix note on `pgame` ([#13880](https://github.com/leanprover-community/mathlib/pull/13880))
We never actually quotient by extensionality. What we quotient by is game equivalence.

### [2022-05-02 17:28:49](https://github.com/leanprover-community/mathlib/commit/0606d7c)
feat(set_theory/game/pgame): Negative of `of_lists` ([#13868](https://github.com/leanprover-community/mathlib/pull/13868))

### [2022-05-02 17:28:48](https://github.com/leanprover-community/mathlib/commit/3e2f214)
feat(logic/basic): Generalize `congr_fun_heq` ([#13867](https://github.com/leanprover-community/mathlib/pull/13867))
The lemma holds for arbitrary heterogeneous equalities, not only that given by casts.

### [2022-05-02 17:28:47](https://github.com/leanprover-community/mathlib/commit/785f62c)
feat(algebra/star/prod): elementwise `star` operator ([#13856](https://github.com/leanprover-community/mathlib/pull/13856))
The lemmas and instances this provides are inspired by `algebra/star/pi`, and appear in the same order.
We should have these instances anyway for completness, but the motivation is to make it easy to talk about the continuity of `star` on `units R` via the `units.embed_product_star` lemma.

### [2022-05-02 17:28:46](https://github.com/leanprover-community/mathlib/commit/206a5f7)
feat(measure_theory/integral/bochner): Add a rewrite lemma saying the ennreal coercion of an integral of a nonnegative function equals the lintegral of the ennreal coercion of the function. ([#13701](https://github.com/leanprover-community/mathlib/pull/13701))
This PR adds a rewrite lemma `of_real_integral_eq_lintegral_of_real` that is very similar to `lintegral_coe_eq_integral`, but for nonnegative real-valued functions instead of nnreal-valued functions.

### [2022-05-02 17:28:45](https://github.com/leanprover-community/mathlib/commit/917b527)
feat(topology/metric_space/thickened_indicator): Add definition and lemmas about thickened indicators. ([#13481](https://github.com/leanprover-community/mathlib/pull/13481))
Add thickened indicators, to be used for the proof of the portmanteau theorem.

### [2022-05-02 15:58:17](https://github.com/leanprover-community/mathlib/commit/af11e15)
feat(algebra/big_operators/finprod): add lemma `finprod_eq_prod_of_mul_support_to_finset_subset'` ([#13801](https://github.com/leanprover-community/mathlib/pull/13801))
Formalized as part of the Sphere Eversion project.

### [2022-05-02 15:58:16](https://github.com/leanprover-community/mathlib/commit/65843cd)
feat(analysis/matrix): provide a normed_algebra structure on matrices ([#13518](https://github.com/leanprover-community/mathlib/pull/13518))
This is one of the final pieces needed to defining the matrix exponential.
It would be nice to show:
```lean
lemma l1_linf_norm_to_matrix [nondiscrete_normed_field R] [decidable_eq n]
  (f : (n → R) →L[R] (m → R)) :
  ∥linear_map.to_matrix' (↑f : (n → R) →ₗ[R] (m → R))∥ = ∥f∥ :=
```
but its not clear to me under what generality it holds.

### [2022-05-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/90418df)
feat(linear_algebra/finite_dimensional): `finite_dimensional_iff_of_rank_eq_nsmul` ([#13357](https://github.com/leanprover-community/mathlib/pull/13357))
If `V` has a dimension that is a scalar multiple of the dimension of `W`, then `V` is finite dimensional iff `W` is.

### [2022-05-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/64bc02c)
feat(ring_theory/dedekind_domain): Chinese remainder theorem for Dedekind domains ([#13067](https://github.com/leanprover-community/mathlib/pull/13067))
The general Chinese remainder theorem states `R / I` is isomorphic to a product of `R / (P i ^ e i)`, where `P i` are comaximal, i.e.  `P i + P j = 1` for `i ≠ j`, and the infimum of all `P i` is `I`.
In a Dedekind domain the theorem can be stated in a more friendly way, namely that the `P i` are the factors (in the sense of a unique factorization domain) of `I`. This PR provides two ways of doing so, and includes some more lemmas on the ideals in a Dedekind domain.

### [2022-05-02 13:45:11](https://github.com/leanprover-community/mathlib/commit/384a7a3)
chore(.github/workflows/merge_conflicts.yaml): use separate token ([#13884](https://github.com/leanprover-community/mathlib/pull/13884))

### [2022-05-02 13:45:10](https://github.com/leanprover-community/mathlib/commit/ad2e936)
feat(topology/homeomorph): add `(co)map_cocompact` ([#13861](https://github.com/leanprover-community/mathlib/pull/13861))
Also rename `filter.comap_cocompact` to `filter.comap_cocompact_le`.

### [2022-05-02 13:45:09](https://github.com/leanprover-community/mathlib/commit/dbc0339)
feat(category_theory/limits/shapes/types): explicit isos ([#13854](https://github.com/leanprover-community/mathlib/pull/13854))
Requested on Zulip. https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Relating.20the.20categorical.20product.20and.20the.20normal.20product

### [2022-05-02 13:45:08](https://github.com/leanprover-community/mathlib/commit/9d3db53)
feat(category_theory/preadditive): End X is a division_ring or field when X is simple ([#13849](https://github.com/leanprover-community/mathlib/pull/13849))
Consequences of Schur's lemma

### [2022-05-02 13:45:07](https://github.com/leanprover-community/mathlib/commit/e5b48f9)
chore(model_theory/basic): golf `countable_empty` ([#13836](https://github.com/leanprover-community/mathlib/pull/13836))

### [2022-05-02 13:45:06](https://github.com/leanprover-community/mathlib/commit/4fe734d)
fix(algebra/indicator_function): add missing decidable instances to lemma statements   ([#13834](https://github.com/leanprover-community/mathlib/pull/13834))
This keeps the definition of `set.indicator` as non-computable, but ensures that when lemmas are applied they generalize to any decidable instances.

### [2022-05-02 13:45:04](https://github.com/leanprover-community/mathlib/commit/cf5fa84)
feat(analysis/normed_space/add_torsor_bases): add lemma `smooth_barycentric_coord` ([#13764](https://github.com/leanprover-community/mathlib/pull/13764))
Formalized as part of the Sphere Eversion project.

### [2022-05-02 13:45:03](https://github.com/leanprover-community/mathlib/commit/4113e00)
feat(linear_algebra/affine_space/basis): add lemma `affine_basis.linear_combination_coord_eq_self` ([#13763](https://github.com/leanprover-community/mathlib/pull/13763))
Formalized as part of the Sphere Eversion project.

### [2022-05-02 13:45:02](https://github.com/leanprover-community/mathlib/commit/b063c28)
fix(src/tactic/alias): Support `alias foo ↔ ..` as documented ([#13743](https://github.com/leanprover-community/mathlib/pull/13743))
the current code and the single(!) use of this feature work only if
you write `alias foo ↔ . .` which is very odd.

### [2022-05-02 13:45:01](https://github.com/leanprover-community/mathlib/commit/3fde082)
refactor(topology/algebra/order): reorganize, simplify proofs ([#13716](https://github.com/leanprover-community/mathlib/pull/13716))
* Prove `has_compact_mul_support.is_compact_range`
* Simplify the proof of `continuous.exists_forall_le_of_has_compact_mul_support` and `continuous.bdd_below_range_of_has_compact_mul_support` using `has_compact_mul_support.is_compact_range`.
* Reorder `topology.algebra.order.basic` so that `is_compact.bdd_below` and friends are together with all results about `order_closed_topology`.
* Move `continuous.bdd_below_range_of_has_compact_mul_support` (and dual) to `topology.algebra.order.basic`

### [2022-05-02 13:45:00](https://github.com/leanprover-community/mathlib/commit/52a454a)
feat(category_theory/limits): pushouts and pullbacks in the opposite category ([#13495](https://github.com/leanprover-community/mathlib/pull/13495))
This PR adds duality isomorphisms for the categories `wide_pushout_shape`, `wide_pullback_shape`, `walking_span`, `walking_cospan` and produce pullbacks/pushouts in the opposite category when pushouts/pullbacks exist.

### [2022-05-02 11:44:57](https://github.com/leanprover-community/mathlib/commit/61d5d30)
feat(group_theory/group_action/basic): A multiplicative action induces an additive action of the additive group ([#13780](https://github.com/leanprover-community/mathlib/pull/13780))
`mul_action M α` induces `add_action (additive M) α`.

### [2022-05-02 11:44:56](https://github.com/leanprover-community/mathlib/commit/320df45)
refactor(linear_algebra/trace): unbundle `matrix.trace` ([#13712](https://github.com/leanprover-community/mathlib/pull/13712))
These extra type arguments are annoying to work with in many cases, especially when Lean doesn't have any information to infer the mostly-irrelevant `R` argument from. This came up while trying to work with `continuous.matrix_trace`, which is annoying to use for that reason.
The old bundled version is still available as `matrix.trace_linear_map`.
The cost of this change is that we have to copy across the usual set of obvious lemmas about additive maps; but we already do this for `diagonal`, `transpose` etc anyway.

### [2022-05-02 11:44:55](https://github.com/leanprover-community/mathlib/commit/a627569)
feat(category_theory/monoidal): adjunctions in rigid categories ([#13707](https://github.com/leanprover-community/mathlib/pull/13707))
We construct the bijection on hom-sets `(Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
given by "pulling the string on the left" down or up, using right duals in a right rigid category.
As consequences, we show that a left rigid category is monoidal closed (it seems our lefts and rights have got mixed up!!), and that functors from a groupoid to a rigid category is again a rigid category.

### [2022-05-02 09:54:04](https://github.com/leanprover-community/mathlib/commit/fe44576)
feat(probability/martingale): the optional stopping theorem ([#13630](https://github.com/leanprover-community/mathlib/pull/13630))
We prove the optional stopping theorem (also known as the fair game theorem). This is number 62 on Freek 100 theorems.

### [2022-05-02 06:04:17](https://github.com/leanprover-community/mathlib/commit/db0b495)
chore(category_theory/limits/cones): avoid a timeout from @[simps] ([#13877](https://github.com/leanprover-community/mathlib/pull/13877))
This was causing a timeout on another branch.

### [2022-05-02 06:04:16](https://github.com/leanprover-community/mathlib/commit/67c0e13)
doc(data/polynomial/basic): Remove references to `polynomial.norm2` ([#13847](https://github.com/leanprover-community/mathlib/pull/13847))
`polynomial.norm2` was never added to mathlib.

### [2022-05-02 06:04:15](https://github.com/leanprover-community/mathlib/commit/03ed4c7)
move(topology/algebra/floor_ring → order/floor): Move topological properties of `⌊x⌋` and `⌈x⌉` ([#13824](https://github.com/leanprover-community/mathlib/pull/13824))
Those belong in an order folder.

### [2022-05-02 06:04:14](https://github.com/leanprover-community/mathlib/commit/aaa167c)
feat(linear_algebra/matrix/adjugate): `adjugate` of a diagonal matrix is diagonal ([#13818](https://github.com/leanprover-community/mathlib/pull/13818))
This proof is a bit ugly...

### [2022-05-02 06:04:13](https://github.com/leanprover-community/mathlib/commit/34bbec6)
feat(logic/equiv/local_equiv): add `forall_mem_target`/`exists_mem_target` ([#13805](https://github.com/leanprover-community/mathlib/pull/13805))

### [2022-05-02 06:04:12](https://github.com/leanprover-community/mathlib/commit/179b6c0)
feat(logic/equiv/local_equiv): add inhabited instances ([#13804](https://github.com/leanprover-community/mathlib/pull/13804))

### [2022-05-02 06:04:11](https://github.com/leanprover-community/mathlib/commit/c1f8ac5)
feat(order/zorn): add Zorn lemma on a preorder ([#13803](https://github.com/leanprover-community/mathlib/pull/13803))

### [2022-05-02 06:04:10](https://github.com/leanprover-community/mathlib/commit/925c473)
chore(analysis/normed_space/add_torsor): make coefficients explicit in lemmas about eventual dilations ([#13796](https://github.com/leanprover-community/mathlib/pull/13796))
For an example of why we should do this, see: https://github.com/leanprover-community/sphere-eversion/blob/19c461c9fba484090ff0af6f0c0204c623f63713/src/loops/surrounding.lean#L176

### [2022-05-02 06:04:09](https://github.com/leanprover-community/mathlib/commit/90b1ddb)
feat(linear_algebra/finite_dimensional): of_injective ([#13792](https://github.com/leanprover-community/mathlib/pull/13792))

### [2022-05-02 06:04:08](https://github.com/leanprover-community/mathlib/commit/0587eb1)
feat(data/zmod/basic): Variant of `zmod.val_int_cast` ([#13781](https://github.com/leanprover-community/mathlib/pull/13781))
This PR adds a variant of `zmod.val_int_cast` avoiding the characteristic assumption.

### [2022-05-02 06:04:07](https://github.com/leanprover-community/mathlib/commit/fd4188d)
feat(data/zmod/basic): `zmod 0` is infinite ([#13779](https://github.com/leanprover-community/mathlib/pull/13779))
This PR adds an instance stating that `zmod 0` is infinite.

### [2022-05-02 06:04:06](https://github.com/leanprover-community/mathlib/commit/5c91490)
refactor(field_theory/separable): move content about polynomial.expand earlier ([#13776](https://github.com/leanprover-community/mathlib/pull/13776))
There were some definitions about polynomial.expand buried in the middle of `field_theory.separable` for no good reason. No changes to content, just moves stuff to an earlier file.

### [2022-05-02 06:04:05](https://github.com/leanprover-community/mathlib/commit/000cae1)
feat(representation_theory): Rep k G is symmetric monoidal ([#13685](https://github.com/leanprover-community/mathlib/pull/13685))

### [2022-05-02 06:04:04](https://github.com/leanprover-community/mathlib/commit/1e38549)
feat(analysis/matrix): define the frobenius norm on matrices ([#13497](https://github.com/leanprover-community/mathlib/pull/13497))

### [2022-05-02 05:27:14](https://github.com/leanprover-community/mathlib/commit/3d946a3)
chore(algebraic_geometry/AffineScheme): Speed up `Spec` ([#13866](https://github.com/leanprover-community/mathlib/pull/13866))
`simps` take 38s in local and does not seem to generate any useful lemma.

### [2022-05-02 04:39:58](https://github.com/leanprover-community/mathlib/commit/523adb3)
feat(set_theory/game/nim): Birthday of `nim` ([#13873](https://github.com/leanprover-community/mathlib/pull/13873))

### [2022-05-02 04:39:57](https://github.com/leanprover-community/mathlib/commit/039543c)
refactor(set_theory/game/pgame): Simpler definition for `star` ([#13869](https://github.com/leanprover-community/mathlib/pull/13869))
This new definition gives marginally easier proofs for the basic lemmas, and avoids use of the quite incomplete `of_lists` API.

### [2022-05-02 04:39:56](https://github.com/leanprover-community/mathlib/commit/26e24c7)
feat(set_theory/surreal/basic): `<` is transitive on numeric games ([#13812](https://github.com/leanprover-community/mathlib/pull/13812))

### [2022-05-02 02:37:54](https://github.com/leanprover-community/mathlib/commit/922717e)
chore(logic/function/basic): don't unfold set in cantor ([#13822](https://github.com/leanprover-community/mathlib/pull/13822))
This uses `set_of` and `mem` consistently instead of using application everywhere, since `f` has type `A -> set A` instead of `A -> A -> Prop`. (Arguably, it could just be stated for `A -> A -> Prop` instead though.)

### [2022-05-02 01:07:34](https://github.com/leanprover-community/mathlib/commit/afc0700)
feat(linear_algebra/tensor_product): define tensor_tensor_tensor_assoc ([#13864](https://github.com/leanprover-community/mathlib/pull/13864))

### [2022-05-01 21:51:02](https://github.com/leanprover-community/mathlib/commit/b236cb2)
chore(set_theory/surreal/basic): Inline instances ([#13811](https://github.com/leanprover-community/mathlib/pull/13811))
We inline various definitions used only for instances. We also remove the redundant lemma `not_le` (which is more generally true on preorders).

### [2022-05-01 21:16:30](https://github.com/leanprover-community/mathlib/commit/f0930c8)
feat(set_theory/pgame/impartial): `star` is impartial ([#13842](https://github.com/leanprover-community/mathlib/pull/13842))

### [2022-05-01 18:53:38](https://github.com/leanprover-community/mathlib/commit/071cb55)
feat(data/set/function): missing mono lemmas ([#13863](https://github.com/leanprover-community/mathlib/pull/13863))

### [2022-05-01 12:36:26](https://github.com/leanprover-community/mathlib/commit/9e7c80f)
docs(*): Wrap some links in < … > ([#13852](https://github.com/leanprover-community/mathlib/pull/13852))
I noticed that many docs say
    See https://stacks.math.columbia.edu/tag/001T.
and the our documentation will include the final `.` in the URL, causing
the URL to not work.
This tries to fix some of these instances. I intentionally applied this
to some URLs ending with a space, because it does not hurt to be
explicit, and the next contributor cargo-culting the URL is more likely
to get this right.
Obligatory xkcd reference: https://xkcd.com/208/

### [2022-05-01 05:59:37](https://github.com/leanprover-community/mathlib/commit/232c15e)
feat(set_theory/game/pgame): Add missing basic API ([#13744](https://github.com/leanprover-community/mathlib/pull/13744))

### [2022-05-01 03:35:34](https://github.com/leanprover-community/mathlib/commit/51b1e11)
feat(set_theory/game/impartial): Relabelling of impartial game is impartial ([#13843](https://github.com/leanprover-community/mathlib/pull/13843))

### [2022-05-01 03:00:28](https://github.com/leanprover-community/mathlib/commit/4b92515)
chore(set_theory/game/impartial): golf ([#13841](https://github.com/leanprover-community/mathlib/pull/13841))