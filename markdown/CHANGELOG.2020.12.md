### [2020-12-31 19:17:29](https://github.com/leanprover-community/mathlib/commit/54bf708)
feat(logic/basic): exists_unique_false simp lemma ([#5544](https://github.com/leanprover-community/mathlib/pull/5544))

### [2020-12-31 16:30:28](https://github.com/leanprover-community/mathlib/commit/0830bfd)
refactor(analysis/analytic/basic): redefine `formal_multilinear_series.radius` ([#5349](https://github.com/leanprover-community/mathlib/pull/5349))
With the new definition, (a) some proofs get much shorter; (b) we
don't need `rpow` in `analytic/basic`.

### [2020-12-31 10:07:03](https://github.com/leanprover-community/mathlib/commit/10f6c15)
chore(analysis/normed_space/inner_product): notation for orthogonal complement ([#5536](https://github.com/leanprover-community/mathlib/pull/5536))
Notation for `submodule.orthogonal`, so that one can write `Kᗮ` instead of `K.orthogonal`.
Simultaneous PR
https://github.com/leanprover/vscode-lean/pull/246
adds `\perp` as vscode shorthand for this symbol.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20linear.20algebra.20notation)

### [2020-12-31 08:49:08](https://github.com/leanprover-community/mathlib/commit/cca6365)
feat(field_theory/galois): is_galois.tfae ([#5542](https://github.com/leanprover-community/mathlib/pull/5542))
This is a TFAE theorem for is_galois

### [2020-12-31 06:04:17](https://github.com/leanprover-community/mathlib/commit/b04aeb5)
chore(algebra): move lemmas from ring_theory.algebra_tower to algebra.algebra.tower ([#5506](https://github.com/leanprover-community/mathlib/pull/5506))
Moved some basic lemmas from `ring_theory.algebra_tower` to `algebra.algebra.tower`.

### [2020-12-31 02:53:26](https://github.com/leanprover-community/mathlib/commit/a40f31f)
feat(data/tprod): finite products of types ([#5385](https://github.com/leanprover-community/mathlib/pull/5385))
This PR defined `list.tprod` as a finite product of types to transfer results from binary products to finitary products.
See module doc for more info.

### [2020-12-31 01:37:37](https://github.com/leanprover-community/mathlib/commit/611b73e)
chore(scripts): update nolints.txt ([#5540](https://github.com/leanprover-community/mathlib/pull/5540))
I am happy to remove some nolints for you!

### [2020-12-30 23:15:52](https://github.com/leanprover-community/mathlib/commit/9c46cad)
feat(field_theory/algebraic_closure): algebraically closed fields have no nontrivial algebraic extensions ([#5537](https://github.com/leanprover-community/mathlib/pull/5537))

### [2020-12-30 20:43:17](https://github.com/leanprover-community/mathlib/commit/6e0d0fa)
chore(algebra/field): use `K` as a type variable ([#5535](https://github.com/leanprover-community/mathlib/pull/5535))

### [2020-12-30 20:43:15](https://github.com/leanprover-community/mathlib/commit/9988193)
feat(measure_theory): various additions ([#5389](https://github.com/leanprover-community/mathlib/pull/5389))
Some computations of measures on non-measurable sets
Some more measurability lemmas for pi-types
Cleanup in `measure_space`

### [2020-12-30 19:29:20](https://github.com/leanprover-community/mathlib/commit/f1d2bc6)
feat(order/lattice_intervals): lattice structures on intervals in lattices ([#5496](https://github.com/leanprover-community/mathlib/pull/5496))
Defines (semi-)lattice structures on intervals in lattices

### [2020-12-30 17:33:54](https://github.com/leanprover-community/mathlib/commit/16320e2)
chore(topology/algebra/infinite_sum): refactor `tsum_mul_left/right` ([#5533](https://github.com/leanprover-community/mathlib/pull/5533))
* move old lemmas to `summable` namespace;
* add new `tsum_mul_left` and `tsum_mul_right` that work in a `division_ring` without a `summable` assumption.

### [2020-12-30 17:33:52](https://github.com/leanprover-community/mathlib/commit/958c407)
chore(analysis/normed_space/basic): a few lemmas about `nnnorm` ([#5532](https://github.com/leanprover-community/mathlib/pull/5532))

### [2020-12-30 15:51:17](https://github.com/leanprover-community/mathlib/commit/b15bb06)
feat(topology/instances/ennreal): a sufficient condition for `f : (Σ i, β i) → ℝ` to be summable ([#5531](https://github.com/leanprover-community/mathlib/pull/5531))

### [2020-12-30 15:51:13](https://github.com/leanprover-community/mathlib/commit/38ba6ba)
chore(data/real/{e,}nnreal): a few lemmas ([#5530](https://github.com/leanprover-community/mathlib/pull/5530))
* Rename `nnreal.le_of_forall_lt_one_mul_lt` to
  `nnreal.le_of_forall_lt_one_mul_le`, and similarly for `ennreal`.
* Move the proof of the latter lemma to `topology/instances/ennreal`,
  prove it using continuity of multiplication.
* Add `ennreal.le_of_forall_nnreal_lt`, `nnreal.lt_div_iff`, and
  `nnreal.mul_lt_of_lt_div`.

### [2020-12-30 15:51:11](https://github.com/leanprover-community/mathlib/commit/c82be35)
feat(analysis/normed_space/inner_product): orthogonal complement lemmas ([#5474](https://github.com/leanprover-community/mathlib/pull/5474))
The orthogonal complement of a subspace is closed.  The orthogonal complement of the orthogonal complement of a complete subspace is itself.

### [2020-12-30 13:05:48](https://github.com/leanprover-community/mathlib/commit/7a03171)
chore(order/rel_iso): add some missing lemmas ([#5492](https://github.com/leanprover-community/mathlib/pull/5492))
Also define `order_iso.trans`.

### [2020-12-30 13:05:46](https://github.com/leanprover-community/mathlib/commit/8545aa6)
chore(topology/algebra/ordered): move code, add missing lemmas ([#5481](https://github.com/leanprover-community/mathlib/pull/5481))
* merge two sections about `linear_ordered_add_comm_group`;
* add missing lemmas about limits of `f * g` when one of `f`, `g` tends to `-∞`, and another tends to a positive or negative constant;
* drop `neg_preimage_closure` in favor of the new `neg_closure` in `topology/algebra/group`.

### [2020-12-30 10:07:47](https://github.com/leanprover-community/mathlib/commit/5e86589)
chore(data/nat/enat): some useful lemmas ([#5517](https://github.com/leanprover-community/mathlib/pull/5517))

### [2020-12-30 08:01:01](https://github.com/leanprover-community/mathlib/commit/1c110ad)
fix(tactic/linarith): elaborate and insert arguments before destructing hypotheses ([#5501](https://github.com/leanprover-community/mathlib/pull/5501))
closes [#5480](https://github.com/leanprover-community/mathlib/pull/5480)
Arguments to `linarith` can depend on hypotheses (e.g. conjunctions) that get destructed during preprocessing, after which the arguments will no longer elaborate or typecheck. This just moves the elaboration earlier and adds these arguments as hypotheses themselves.

### [2020-12-30 01:38:14](https://github.com/leanprover-community/mathlib/commit/7c6020f)
chore(scripts): update nolints.txt ([#5526](https://github.com/leanprover-community/mathlib/pull/5526))
I am happy to remove some nolints for you!

### [2020-12-29 19:06:07](https://github.com/leanprover-community/mathlib/commit/abffbaa)
feat(analysis/convex/specific_functions): log is concave ([#5508](https://github.com/leanprover-community/mathlib/pull/5508))
This PR proves that the real log is concave on `Ioi 0` and `Iio 0`, and adds lemmas about concavity of functions along the way.

### [2020-12-29 07:47:35](https://github.com/leanprover-community/mathlib/commit/8e413eb)
feat(order/bounded_lattice): define atoms, coatoms, and simple lattices ([#5471](https://github.com/leanprover-community/mathlib/pull/5471))
Defines `is_atom`, `is_coatom`, and `is_simple_lattice`
Refactors `ideal.is_maximal` to use `is_coatom`, the new definition is definitionally equal to the old one

### [2020-12-29 03:00:40](https://github.com/leanprover-community/mathlib/commit/15ff865)
doc(localized): update documentation ([#5519](https://github.com/leanprover-community/mathlib/pull/5519))
remove old warning
remove duplicated documentation
rename notation namespace to locale

### [2020-12-29 01:33:07](https://github.com/leanprover-community/mathlib/commit/297d97e)
chore(scripts): update nolints.txt ([#5522](https://github.com/leanprover-community/mathlib/pull/5522))
I am happy to remove some nolints for you!

### [2020-12-28 17:36:18](https://github.com/leanprover-community/mathlib/commit/41bad63)
feat(polynomial/degree/definitions): nat_degree_X_pow ([#5512](https://github.com/leanprover-community/mathlib/pull/5512))
Companion to degree_X_pow

### [2020-12-28 15:03:21](https://github.com/leanprover-community/mathlib/commit/d245c4e)
feat(polynomial/algebra_map): aeval_comp ([#5511](https://github.com/leanprover-community/mathlib/pull/5511))
Basic lemma about aeval

### [2020-12-28 13:55:13](https://github.com/leanprover-community/mathlib/commit/f1f2ca6)
feat(category_theory/limits): preserves limits of equivalent shape ([#5515](https://github.com/leanprover-community/mathlib/pull/5515))

### [2020-12-28 03:40:12](https://github.com/leanprover-community/mathlib/commit/6d1d4c1)
chore(scripts): update nolints.txt ([#5514](https://github.com/leanprover-community/mathlib/pull/5514))
I am happy to remove some nolints for you!

### [2020-12-28 00:38:46](https://github.com/leanprover-community/mathlib/commit/6d0b415)
feat(data/list/basic): nth_zero ([#5513](https://github.com/leanprover-community/mathlib/pull/5513))

### [2020-12-27 16:40:59](https://github.com/leanprover-community/mathlib/commit/5c8c122)
chore(analysis/analytic/basic): speed up slow lemmas ([#5507](https://github.com/leanprover-community/mathlib/pull/5507))
Removes slow `tidy`s from `formal_multilinear_series.change_origin_radius` and `formal_multilinear_series.change_origin_has_sum`

### [2020-12-27 04:21:55](https://github.com/leanprover-community/mathlib/commit/1e75453)
feat(data/list/basic): filter_map retains prefix ([#5453](https://github.com/leanprover-community/mathlib/pull/5453))

### [2020-12-26 22:54:39](https://github.com/leanprover-community/mathlib/commit/f7e728a)
feat(data/list/range): enum is a zip ([#5457](https://github.com/leanprover-community/mathlib/pull/5457))

### [2020-12-26 20:38:16](https://github.com/leanprover-community/mathlib/commit/ae60bb9)
chore(topology/algebra/order): add `continuous_on.surj_on_of_tendsto` ([#5502](https://github.com/leanprover-community/mathlib/pull/5502))
* rename `surjective_of_continuous` to `continuous.surjective` and `surjective_of_continuous'` to `continuous.surjective'`;
* add `continuous_on.surj_on_of_tendsto` and `continuous_on.surj_on_of_tendsto'`

### [2020-12-26 09:47:44](https://github.com/leanprover-community/mathlib/commit/add100a)
feat(ring_theory/perfection): perfection.map ([#5503](https://github.com/leanprover-community/mathlib/pull/5503))

### [2020-12-26 01:31:06](https://github.com/leanprover-community/mathlib/commit/768497c)
chore(scripts): update nolints.txt ([#5505](https://github.com/leanprover-community/mathlib/pull/5505))
I am happy to remove some nolints for you!

### [2020-12-25 21:29:27](https://github.com/leanprover-community/mathlib/commit/666035f)
fix(algebra/big_operators/basic): add docstrings for `sum_bij` and `sum_bij'` ([#5497](https://github.com/leanprover-community/mathlib/pull/5497))
They don't seem to be there.

### [2020-12-25 21:29:26](https://github.com/leanprover-community/mathlib/commit/1a526b3)
chore(topology/homeomorph): a few more lemmas, golf ([#5467](https://github.com/leanprover-community/mathlib/pull/5467))

### [2020-12-25 18:38:51](https://github.com/leanprover-community/mathlib/commit/726b7bf)
feat(analysis/specific_limits): a `tfae` about "`f` grows exponentially slower than `R ^ n`" ([#5488](https://github.com/leanprover-community/mathlib/pull/5488))
Also add supporting lemmas here and there.

### [2020-12-25 17:10:05](https://github.com/leanprover-community/mathlib/commit/d968a61)
feat(category_theory/limits): yoneda reflects limits ([#5447](https://github.com/leanprover-community/mathlib/pull/5447))
yoneda and coyoneda jointly reflect limits

### [2020-12-25 13:57:08](https://github.com/leanprover-community/mathlib/commit/f60fd08)
chore(logic/basic): +2 simp lemmas ([#5500](https://github.com/leanprover-community/mathlib/pull/5500))
* simplify `a ∨ b ↔ a` to `b → a`;
* simplify `a ∨ b ↔ b` to `a → b`.

### [2020-12-25 01:42:05](https://github.com/leanprover-community/mathlib/commit/1f0231d)
chore(scripts): update nolints.txt ([#5498](https://github.com/leanprover-community/mathlib/pull/5498))
I am happy to remove some nolints for you!

### [2020-12-24 19:51:27](https://github.com/leanprover-community/mathlib/commit/feced76)
feat(algebra/*): Noncomputable `group` structures from `is_unit` ([#5427](https://github.com/leanprover-community/mathlib/pull/5427))
Noncomputably defines the following group structures given that all (nonzero) elements are units:
- `monoid` -> `group`
- `comm_monoid` -> `comm_group`
- `monoid_with_zero` -> `comm_group_with_zero`
- `comm_monoid_with_zero` -> `comm_group_with_zero`
- `ring` -> `division_ring`
- `comm_ring` -> `field`

### [2020-12-24 16:50:39](https://github.com/leanprover-community/mathlib/commit/f300c75)
feat(data/list/basic): lemmas about reduce_option ([#5450](https://github.com/leanprover-community/mathlib/pull/5450))

### [2020-12-24 14:52:22](https://github.com/leanprover-community/mathlib/commit/3046436)
chore(linear_algebra/linear_independent): make a binding explicit in ne_zero ([#5494](https://github.com/leanprover-community/mathlib/pull/5494))
Resubmitting [#5479](https://github.com/leanprover-community/mathlib/pull/5479) from within the mathlib repo.

### [2020-12-24 08:35:35](https://github.com/leanprover-community/mathlib/commit/46614b0)
chore(ring_theory/power_series/well_known): generalize ([#5491](https://github.com/leanprover-community/mathlib/pull/5491))
* generalize `power_series.exp`, `power_series.cos`, and `power_series.sin` to a `ℚ`-algebra;
* define `alg_hom.mk'`;
* rename `alg_hom_nat` to `ring_hom.to_nat_alg_hom`;
* drop `alg_hom_int` (was equal to `ring_hom.to_int_alg_hom`);
* add `ring_hom.to_rat_alg_hom`.

### [2020-12-24 08:35:33](https://github.com/leanprover-community/mathlib/commit/8a03839)
chore(scripts): update nolints.txt ([#5490](https://github.com/leanprover-community/mathlib/pull/5490))
I am happy to remove some nolints for you!

### [2020-12-24 07:17:34](https://github.com/leanprover-community/mathlib/commit/2ae61be)
feat(field_theory/galois): is_galois.self ([#5486](https://github.com/leanprover-community/mathlib/pull/5486))
Some basic lemmas about is_separable, normal, and is_galois.

### [2020-12-23 22:08:09](https://github.com/leanprover-community/mathlib/commit/63070ed)
feat(data/list/chain): relate chain to refl trans gen ([#5437](https://github.com/leanprover-community/mathlib/pull/5437))
Some golf and a new lemma to convert a list chain to a refl trans gen

### [2020-12-23 22:08:07](https://github.com/leanprover-community/mathlib/commit/ceae529)
chore(group_theory/coset): Make `quotient_group.mk` an abbreviation ([#5377](https://github.com/leanprover-community/mathlib/pull/5377))
This allows simp lemmas about `quotient.mk'` to apply here, which currently do not apply.
The definition doesn't seem interesting enough to be semireducible.

### [2020-12-23 18:58:44](https://github.com/leanprover-community/mathlib/commit/2a5a0b0)
feat(group_theory/*): mark some lemmas as ext (about homs out of free constructions) ([#5484](https://github.com/leanprover-community/mathlib/pull/5484))

### [2020-12-23 18:58:42](https://github.com/leanprover-community/mathlib/commit/e2edba5)
chore(order/filter/basic): make `filter.univ_mem_sets` a `simp` lemma ([#5464](https://github.com/leanprover-community/mathlib/pull/5464))

### [2020-12-23 18:58:38](https://github.com/leanprover-community/mathlib/commit/d3a5e06)
feat(data/dlist/basic): dlist singleton and of_list simp lemmas ([#5461](https://github.com/leanprover-community/mathlib/pull/5461))

### [2020-12-23 16:10:29](https://github.com/leanprover-community/mathlib/commit/fd9268c)
feat(data/list/basic): lemmas about scanl ([#5454](https://github.com/leanprover-community/mathlib/pull/5454))

### [2020-12-23 12:11:42](https://github.com/leanprover-community/mathlib/commit/eb5cf25)
chore(analysis/asymptotics): a few more lemmas ([#5482](https://github.com/leanprover-community/mathlib/pull/5482))
* golf some proofs;
* `x ^ n = o (y ^ n)` as `n → ∞` provided that `0 ≤ x < y`;
* lemmas about `is_O _ _ ⊤` etc;
* if `is_O f g cofinite`, then for some `C>0` and any `x` such that `g x ≠ 0` we have `∥f x∥≤C*∥g x∥`.

### [2020-12-23 09:41:22](https://github.com/leanprover-community/mathlib/commit/435b97a)
feat(ring_theory/witt_vector): the comparison between W(F_p) and Z_p ([#5164](https://github.com/leanprover-community/mathlib/pull/5164))
This PR is the culmination of the Witt vector project. We prove that the
ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic
numbers.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-23 04:12:18](https://github.com/leanprover-community/mathlib/commit/d5adbde)
feat(data/list/basic): prefix simplifying iff lemmas ([#5452](https://github.com/leanprover-community/mathlib/pull/5452))

### [2020-12-23 01:30:34](https://github.com/leanprover-community/mathlib/commit/24f71d7)
chore(scripts): update nolints.txt ([#5483](https://github.com/leanprover-community/mathlib/pull/5483))
I am happy to remove some nolints for you!

### [2020-12-22 20:56:38](https://github.com/leanprover-community/mathlib/commit/eba2a79)
feat(data/list/zip): length of zip_with, nth_le of zip ([#5455](https://github.com/leanprover-community/mathlib/pull/5455))

### [2020-12-22 17:05:18](https://github.com/leanprover-community/mathlib/commit/3fc60fc)
fix(number_theory/bernoulli): fix docstring ([#5478](https://github.com/leanprover-community/mathlib/pull/5478))

### [2020-12-22 17:05:16](https://github.com/leanprover-community/mathlib/commit/0f1362e)
chore(analysis/calculus/mean_value): use `𝓝[Ici x] x` instead of `𝓝[Ioi x] x` ([#5472](https://github.com/leanprover-community/mathlib/pull/5472))
In many parts of the library we prefer `𝓝[Ici x] x` to `𝓝[Ioi x]
x` (e.g., in assumptions line `continuous_within_at`). Fix MVT and
Gronwall's inequality to use it if possible.
Motivated by [#4945](https://github.com/leanprover-community/mathlib/pull/4945)

### [2020-12-22 17:05:14](https://github.com/leanprover-community/mathlib/commit/fb99440)
feat(data/complex/is_R_or_C): register some instances ([#5466](https://github.com/leanprover-community/mathlib/pull/5466))
Register a couple of facts which were previously known for `ℝ` and `ℂ` individually, but not for the typeclass `[is_R_or_C K]`:
- such a field `K` is finite-dimensional as a vector space over `ℝ`
- finite-dimensional normed spaces over `K` are proper.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Instances.20for.20is_R_or_C

### [2020-12-22 17:05:12](https://github.com/leanprover-community/mathlib/commit/7c2f166)
chore(analysis/special_functions/trigonometric): review continuity of `tan` ([#5429](https://github.com/leanprover-community/mathlib/pull/5429))
* prove that `tan` is discontinuous at `x` whenever `cos x = 0`;
* turn `continuous_at_tan` and `differentiable_at_tan` into `iff` lemmas;
* reformulate various lemmas in terms of `cos x = 0` instead of `∃ k, x = ...`;

### [2020-12-22 17:05:09](https://github.com/leanprover-community/mathlib/commit/d569d63)
refactor(analysis/inner_product_space, geometry/euclidean) range of orthogonal projection ([#5408](https://github.com/leanprover-community/mathlib/pull/5408))
Previously, the orthogonal projection was defined for all subspaces of an inner product space, with the junk value `id` if the space was not complete; then all nontrivial lemmas required a hypothesis of completeness (and nonemptiness for the affine orthogonal projection).  Change this to a definition only for subspaces `K` satisfying `[complete_space K]` (and `[nonempty K]` for the affine orthogonal projection).
Previously, the orthogonal projection was a linear map from `E` to `E`.  Redefine it to be a linear map from `E` to `K`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Orthogonal.20projection)

### [2020-12-22 17:05:07](https://github.com/leanprover-community/mathlib/commit/0ff9068)
feat(data/finset/basic, topology/separation): add induction_on_union, separate, and separate_finset_of_t2 ([#5332](https://github.com/leanprover-community/mathlib/pull/5332))
prove lemma disjoint_finsets_opens_of_t2 showing that in a t2_space disjoint finsets have disjoint open neighbourhoods, using auxiliary lemma not_mem_finset_opens_of_t2.

### [2020-12-22 13:47:43](https://github.com/leanprover-community/mathlib/commit/02ab90c)
chore(*): split some long lines ([#5470](https://github.com/leanprover-community/mathlib/pull/5470))

### [2020-12-22 07:50:26](https://github.com/leanprover-community/mathlib/commit/4ddae3d)
feat(ring_theory/power_series): define power series for `exp`, `sin`, `cos`, and `1 / (u - x)`. ([#5432](https://github.com/leanprover-community/mathlib/pull/5432))
This PR defines `power_series.exp` etc to be formal power series for the corresponding functions. Once we have a bridge to `is_analytic`, we should redefine `complex.exp` etc using these power series.

### [2020-12-22 03:10:44](https://github.com/leanprover-community/mathlib/commit/92dfdbc)
chore(scripts): update nolints.txt ([#5469](https://github.com/leanprover-community/mathlib/pull/5469))
I am happy to remove some nolints for you!

### [2020-12-22 03:10:42](https://github.com/leanprover-community/mathlib/commit/3c7394f)
fix(group_theory/*, algebra/group): [to_additive, simp] doesn't work ([#5468](https://github.com/leanprover-community/mathlib/pull/5468))
As explained in `algebra/group/to_additive`, `@[to_additive, simp]` doesn't work (it doesn't attach a `simp` attribute to the additive lemma), but conversely `@[simps, to_additive]` is also wrong.
Along the way I also noticed that some `right_inv` (as in an inverse function) lemmas were being changed to `right_neg` by to_additive :D

### [2020-12-21 23:51:24](https://github.com/leanprover-community/mathlib/commit/9ec2778)
chore(data/{equiv,set}/basic): image_preimage ([#5465](https://github.com/leanprover-community/mathlib/pull/5465))
* `equiv.symm_image_image`: add `@[simp]`;
* `equiv.image_preimage`, `equiv.preimage_image`: new `simp` lemmas;
* `set.image_preimage_eq`, `set.preimage_image_eq`: make `s : set _` an explicit argument;
* `function.injective.preimage_image`, `function.surjective.image_preimage`: new aliases for `set.preimage_image_eq`
  and `set.image_preimage_eq` with arguments reversed
Also golf a proof about `separated`.

### [2020-12-21 20:56:39](https://github.com/leanprover-community/mathlib/commit/d2ae43f)
feat(data/list/basic): lemmas about nth of take and append ([#5449](https://github.com/leanprover-community/mathlib/pull/5449))

### [2020-12-21 20:56:37](https://github.com/leanprover-community/mathlib/commit/3b9cbdf)
feat(data/ordmap): Ordered maps (like rb_map but better) ([#5353](https://github.com/leanprover-community/mathlib/pull/5353))
This cleans up an old mathlib branch from 2 years ago, so it probably isn't in very modern style, but it would be best to get it merged and kept up to date rather than leaving it to rot.
It is an implementation of size balanced ordered maps based on Haskell's `Data.Map.Strict`. The `ordnode` structure can be used directly if one is only interested in using it for programming purposes, and the `ordset` structure bundles the proofs so that you can prove theorems about inserting and deleting doing what you expect.

### [2020-12-21 17:48:50](https://github.com/leanprover-community/mathlib/commit/bc3ad25)
feat(linear_algebra/tensor_algebra): Add missing lemmas about subtraction ([#5428](https://github.com/leanprover-community/mathlib/pull/5428))

### [2020-12-21 17:48:49](https://github.com/leanprover-community/mathlib/commit/34d5750)
feat(data/option/basic): lemmas on map of none and congr ([#5424](https://github.com/leanprover-community/mathlib/pull/5424))

### [2020-12-21 16:45:47](https://github.com/leanprover-community/mathlib/commit/0ed425f)
feat(ring_theory/perfection): define characteristic predicate of perfection ([#5386](https://github.com/leanprover-community/mathlib/pull/5386))
Name changes:
- `perfect_field` --> `perfect_ring` (generalization)
- `semiring.perfection` --> `ring.perfection`
- Original `ring.perfection` deleted.

### [2020-12-21 15:29:49](https://github.com/leanprover-community/mathlib/commit/96a2aa1)
feat(ring_theory/roots_of_unity): add minimal_polynomial_eq_pow ([#5444](https://github.com/leanprover-community/mathlib/pull/5444))
This is the main result about minimal polynomial of primitive roots of unity: `μ` and `μ ^ p` have the same minimal polynomial.
The proof is a little long, but I don't see how I can split it: it is entirely by contradiction, so any lemma extracted from it would start with a false assumption and at the end it would be used only in this proof.

### [2020-12-21 14:00:44](https://github.com/leanprover-community/mathlib/commit/c5c02ec)
feat(category_theory/yoneda): add iso_comp_punit ([#5448](https://github.com/leanprover-community/mathlib/pull/5448))
A presheaf P : C^{op} -> Type v is isomorphic to the composition of P with the coyoneda functor Type v -> Type v associated to `punit`.
[This is useful for developing the theory of sheaves taking values in a general category]

### [2020-12-21 09:07:54](https://github.com/leanprover-community/mathlib/commit/c98d5bb)
feat(category_theory/limits): yoneda preserves limits ([#5439](https://github.com/leanprover-community/mathlib/pull/5439))
yoneda and coyoneda preserve limits

### [2020-12-21 07:48:53](https://github.com/leanprover-community/mathlib/commit/4778e16)
chore(category_theory/sites/sheaf): rename sheaf to sheaf_of_types ([#5458](https://github.com/leanprover-community/mathlib/pull/5458))
I wanted to add sheaves with values in general categories, so I moved sheaf.lean to sheaf_of_types.lean and then added a new file sheaf.lean. Github then produced an incomprehensible diff file because sheaf.lean had completely changed. Hence I propose first moving `sheaf.lean` to `sheaf_of_types.lean` and then adding a new `sheaf.lean` later. As well as moving the file, I also slightly change it.

### [2020-12-21 01:32:14](https://github.com/leanprover-community/mathlib/commit/ca2e536)
chore(scripts): update nolints.txt ([#5459](https://github.com/leanprover-community/mathlib/pull/5459))
I am happy to remove some nolints for you!

### [2020-12-20 11:33:02](https://github.com/leanprover-community/mathlib/commit/d79105e)
feat(tactic/field_simp): let field_simp use norm_num to prove numerals are nonzero ([#5418](https://github.com/leanprover-community/mathlib/pull/5418))
As suggested by @robertylewis in https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Solving.20simple.20%28in%29equalities.20gets.20frustrating/near/220278546, change the discharger in `field_simp` to try `assumption` on  goals `x ≠ 0` and `norm_num1` on these goals when `x` is a numeral.

### [2020-12-20 09:21:32](https://github.com/leanprover-community/mathlib/commit/5010738)
feat(topology/algebra/ordered): continuity of `abs` ([#5412](https://github.com/leanprover-community/mathlib/pull/5412))

### [2020-12-20 01:39:55](https://github.com/leanprover-community/mathlib/commit/a9fb069)
chore(scripts): update nolints.txt ([#5441](https://github.com/leanprover-community/mathlib/pull/5441))
I am happy to remove some nolints for you!

### [2020-12-19 20:45:22](https://github.com/leanprover-community/mathlib/commit/1cb9727)
feat(field_theory/galois): Separable splitting field is Galois ([#5347](https://github.com/leanprover-community/mathlib/pull/5347))
Proves that a splitting field of a separable polynomial is Galois by showing that it has lots of automorphisms.

### [2020-12-19 17:55:35](https://github.com/leanprover-community/mathlib/commit/e22fb94)
chore(data/nat/cast,algebra/ordered_group): 2 trivial lemmas ([#5436](https://github.com/leanprover-community/mathlib/pull/5436))

### [2020-12-19 17:55:33](https://github.com/leanprover-community/mathlib/commit/5de6757)
chore(algebra/ordered_group): deduplicate ([#5403](https://github.com/leanprover-community/mathlib/pull/5403))
I deleted many `a_of_b` lemmas for which `a_iff_b` existed, then restored (most? all?) of them using `alias` command.

### [2020-12-19 17:55:30](https://github.com/leanprover-community/mathlib/commit/63e7fc9)
feat(topology/algebra/ordered): a linear ordered additive group with order topology is a topological group ([#5402](https://github.com/leanprover-community/mathlib/pull/5402))

### [2020-12-19 17:55:28](https://github.com/leanprover-community/mathlib/commit/154a024)
feat(measure_theory/lp_space): add lemmas about the monotonicity of the Lp seminorm ([#5395](https://github.com/leanprover-community/mathlib/pull/5395))
Also add a lemma mem_Lp.const_smul for a normed space.

### [2020-12-19 17:55:27](https://github.com/leanprover-community/mathlib/commit/ce385a0)
feat(ring_theory/roots_of_unity): lemmas about minimal polynomial ([#5393](https://github.com/leanprover-community/mathlib/pull/5393))
Three results about the minimal polynomial of `μ` and `μ ^ p`, where `μ` is a primitive root of unity. These are preparatory lemmas to prove that the two minimal polynomials are equal.

### [2020-12-19 16:17:17](https://github.com/leanprover-community/mathlib/commit/c55721d)
chore(analysis/calculus/{fderiv,deriv}): `f x ≠ f a` for `x ≈ a`, `x ≠ a` if `∥z∥ ≤ C * ∥f' z∥` ([#5420](https://github.com/leanprover-community/mathlib/pull/5420))

### [2020-12-19 14:59:26](https://github.com/leanprover-community/mathlib/commit/ff830d7)
feat(ring_theory/witt_vector): redefine subtraction using witt_sub polynomial ([#5405](https://github.com/leanprover-community/mathlib/pull/5405))

### [2020-12-19 11:05:52](https://github.com/leanprover-community/mathlib/commit/656b1bb)
feat(category_theory): essential image of a functor ([#5352](https://github.com/leanprover-community/mathlib/pull/5352))
Define essential image of a functor as a predicate and use it to re-express essential surjectivity.
Construct the essential image as a subcategory of the target and use it to factorise an arbitrary functor into a fully faithful functor and an essentially surjective functor.
Also shuffles the import hierarchy a little so that essential image can import full subcategories.

### [2020-12-19 08:21:41](https://github.com/leanprover-community/mathlib/commit/0bb665c)
chore(ring_theory/power_series): review, golf ([#5431](https://github.com/leanprover-community/mathlib/pull/5431))

### [2020-12-19 02:24:58](https://github.com/leanprover-community/mathlib/commit/53354e7)
chore(scripts): update nolints.txt ([#5433](https://github.com/leanprover-community/mathlib/pull/5433))
I am happy to remove some nolints for you!

### [2020-12-19 02:24:56](https://github.com/leanprover-community/mathlib/commit/ec1b70e)
chore(linear_algebra/multilinear): Add map_update_zero ([#5417](https://github.com/leanprover-community/mathlib/pull/5417))
`map_coord_zero` isn't in a form that can be used by simp, so this introduces a form which can.

### [2020-12-19 02:24:54](https://github.com/leanprover-community/mathlib/commit/5e057c9)
feat(data/fin): trans and id lemmas for fin.cast ([#5415](https://github.com/leanprover-community/mathlib/pull/5415))

### [2020-12-18 23:34:58](https://github.com/leanprover-community/mathlib/commit/0e9a77c)
feat(data/nat/basic): succ_lt_succ_iff ([#5422](https://github.com/leanprover-community/mathlib/pull/5422))

### [2020-12-18 20:57:15](https://github.com/leanprover-community/mathlib/commit/33483a3)
chore(analysis/special_functions/trigonometric): golf a few more proofs ([#5423](https://github.com/leanprover-community/mathlib/pull/5423))

### [2020-12-18 17:40:37](https://github.com/leanprover-community/mathlib/commit/0d140b1)
feat(data/set/basic): nonempty instances for subtypes ([#5409](https://github.com/leanprover-community/mathlib/pull/5409))
In [#5408](https://github.com/leanprover-community/mathlib/pull/5408), it is useful to be able to track the nonemptiness of a subset by typeclass inference.  These constructions allow one to do this.

### [2020-12-18 15:15:14](https://github.com/leanprover-community/mathlib/commit/775edc6)
feat(linear_algebra/tensor_product): Inherit smul through is_scalar_tower ([#5317](https://github.com/leanprover-community/mathlib/pull/5317))
Most notably, this now means that the lemmas about `smul` and `tmul` can be used to prove `∀ z : Z, (z • a) ⊗ₜ[R] b = z • (a ⊗ₜ[R] b)`.
Hopefully these instances aren't dangerous - in particular, there's now a risk of a non-defeq-but-eq diamond for the `ℤ`- and `ℕ`-module structure.
However:
* this diamond already exists in other places anyway
* the diamond if it comes up can be solved with `subsingleton.elim`, since we have a proof that all Z-module and N-module structures must be equivalent.

### [2020-12-18 12:03:56](https://github.com/leanprover-community/mathlib/commit/74b5839)
chore(topology/algebra/ordered): generalize `tendsto_at_top_add_left` etc ([#5398](https://github.com/leanprover-community/mathlib/pull/5398))
* generalize some lemmas from `linear_ordered_ring` to
  `linear_ordered_add_comm_group`;
* rename them to allow dot notation; the new names are
  `filter.tendsto.add_at_*` and `filter.tendsto.at_*_add`, where `*` is
  `top` or `bot`;
* generalize `infi_unit` and `supr_unit` to
  `conditionally_complete_lattice`, add `[unique α]` versions;
* in a `subsingleton`, both `at_top` and `at_bot` are equal to `⊤`;
  these lemmas are useful for the `nontriviality` tactic.

### [2020-12-18 09:12:03](https://github.com/leanprover-community/mathlib/commit/c4f673c)
chore(analysis/normed_space/basic): `continuous_at.norm` etc ([#5411](https://github.com/leanprover-community/mathlib/pull/5411))
Add variants of the lemma that the norm is continuous.  Also rewrite a few proofs, and rename three lemmas:
* `lim_norm` -> `tendsto_norm_sub_self`
* `lim_norm_zero` -> `tendsto_norm_zero`
* `lim_norm_zero'` -> `tendsto_norm_zero'`

### [2020-12-18 01:44:51](https://github.com/leanprover-community/mathlib/commit/a4dd9e1)
chore(scripts): update nolints.txt ([#5413](https://github.com/leanprover-community/mathlib/pull/5413))
I am happy to remove some nolints for you!

### [2020-12-18 01:44:49](https://github.com/leanprover-community/mathlib/commit/b1218f8)
chore(analysis/special_functions/trigonometric): review, golf ([#5392](https://github.com/leanprover-community/mathlib/pull/5392))

### [2020-12-17 16:32:00](https://github.com/leanprover-community/mathlib/commit/35f2789)
chore(algebra/module/basic): add `subsingleton (semimodule ℕ M)` ([#5396](https://github.com/leanprover-community/mathlib/pull/5396))
This can be used to resolve diamonds between different `semimodule ℕ` instances.
The implementation is copied from the `subsingleton (module ℤ M)` instance.

### [2020-12-17 13:27:40](https://github.com/leanprover-community/mathlib/commit/6f1351f)
chore(algebra/{group,ring}): more on pushing/pulling groups/rings along morphisms ([#5406](https://github.com/leanprover-community/mathlib/pull/5406))

### [2020-12-17 13:27:39](https://github.com/leanprover-community/mathlib/commit/ff716d2)
chore(order/bounds): golf ([#5401](https://github.com/leanprover-community/mathlib/pull/5401))

### [2020-12-17 13:27:36](https://github.com/leanprover-community/mathlib/commit/3685146)
chore(topology/algebra/ordered): deduplicate ([#5399](https://github.com/leanprover-community/mathlib/pull/5399))
* Drop `mem_nhds_unbounded` in favor of
  `mem_nhds_iff_exists_Ioo_subset'`.
* Use `(h : ∃ l, l < a)` instead of `{l} (hl : l < a)` in
  `mem_nhds_iff_exists_Ioo_subset'`. This way we can `apply` the
  theorem without generating non-`Prop` goals and we can get the
  arguments directly from `no_bot` / `no_top`.
* add `nhds_basis_Ioo'` and `nhds_basis_Ioo`.

### [2020-12-17 13:27:34](https://github.com/leanprover-community/mathlib/commit/35a16a9)
feat(algebra/module/basic): Add symmetric smul_comm_class instances for int and nat ([#5369](https://github.com/leanprover-community/mathlib/pull/5369))
These can't be added globally for all types as they cause instance resolution loops, but are safe here as these definitions do not depend on an existing `smul_comm_class`.
Note that these instances already exist via `is_scalar_tower.to_smul_comm_class'` for algebras - this just makes sure the instances are still available in the presence of weaker typeclasses. There's no diamond concern here, as `smul_comm_class` is in `Prop`.

### [2020-12-17 10:49:30](https://github.com/leanprover-community/mathlib/commit/ee6969c)
chore(linear_algebra/{alternating,multilinear}): Add a handful of trivial lemmas ([#5380](https://github.com/leanprover-community/mathlib/pull/5380))
Some of these are needed for a WIP PR, and some seem like generally nice things to have.

### [2020-12-17 08:03:51](https://github.com/leanprover-community/mathlib/commit/6a99e9e)
chore(analysis/calculus/deriv): add `iff` versions of `differentiable_const_add` etc ([#5390](https://github.com/leanprover-community/mathlib/pull/5390))
Also drop some unneeded `differentiable` assumptions in lemmas like `deriv_const_add`.

### [2020-12-17 01:31:27](https://github.com/leanprover-community/mathlib/commit/e8fc373)
chore(scripts): update nolints.txt ([#5400](https://github.com/leanprover-community/mathlib/pull/5400))
I am happy to remove some nolints for you!

### [2020-12-16 21:52:40](https://github.com/leanprover-community/mathlib/commit/01a77ad)
chore(analysis/analytic/basic.lean): fix latex in doc ([#5397](https://github.com/leanprover-community/mathlib/pull/5397))
Doc in the file `analytic/basic.lean` is broken, since I used a latex command `\choose` which doesn't exist. Replace it with `\binom`.

### [2020-12-16 21:52:38](https://github.com/leanprover-community/mathlib/commit/8fa10af)
feat(ring_theory/algebra_tower): alg_hom_equiv_sigma ([#5345](https://github.com/leanprover-community/mathlib/pull/5345))
Proves that algebra homomorphisms from the top of an is_scalar_tower are the same as a pair of algebra homomorphisms.
This is useful for counting algebra homomorphisms.

### [2020-12-16 18:35:22](https://github.com/leanprover-community/mathlib/commit/c5a2ff4)
chore(script/copy-mod-doc) Specify an encoding for files when opening ([#5394](https://github.com/leanprover-community/mathlib/pull/5394))
This was necessary for the script to run locally on windows.

### [2020-12-16 18:35:20](https://github.com/leanprover-community/mathlib/commit/9282f6c)
feat(finset): two simple lemmas ([#5387](https://github.com/leanprover-community/mathlib/pull/5387))
also open function namespace

### [2020-12-16 15:31:36](https://github.com/leanprover-community/mathlib/commit/39ecd1a)
chore(group_theory/group_action/basic): Add a simp lemma about smul on quotient groups ([#5374](https://github.com/leanprover-community/mathlib/pull/5374))
By pushing `mk` to the outside, this increases the chance they can cancel with an outer `lift`

### [2020-12-16 15:31:34](https://github.com/leanprover-community/mathlib/commit/1221ab6)
chore(*): add a `div`/`sub` field to (`add_`)`group`(`_with_zero`) ([#5303](https://github.com/leanprover-community/mathlib/pull/5303))
This PR is intended to fix the following kind of diamonds:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no `∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the `(/)` coming from `group_with_zero_has_div` cannot be defeq to the `(/)` coming from `foo.has_div`.
As a consequence of making the `has_div` instances defeq, we can no longer assume that `(div_eq_mul_inv a b : a / b = a * b⁻¹) = rfl` for all groups. The previous preparation PR [#5302](https://github.com/leanprover-community/mathlib/pull/5302) should have changed all places in mathlib that assumed defeqness, to rewrite explicitly instead.

### [2020-12-16 13:55:21](https://github.com/leanprover-community/mathlib/commit/461865b)
refactor(data/real): move `real.sqrt` to `data.real.sqrt`, more dependencies ([#5359](https://github.com/leanprover-community/mathlib/pull/5359))
* define `nnreal.sqrt`;
* use general theory to prove that the inverse exists, and is an `order_iso`;
* deduce continuity of `sqrt` from continuity of `order_iso`.

### [2020-12-16 13:55:19](https://github.com/leanprover-community/mathlib/commit/1b01068)
feat(ring_theory/witt_vector): Witt vectors are proj. limit of truncated Witt vectors ([#5163](https://github.com/leanprover-community/mathlib/pull/5163))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-16 10:00:13](https://github.com/leanprover-community/mathlib/commit/6548be4)
chore(data/quot): Add missing simp lemmas ([#5372](https://github.com/leanprover-community/mathlib/pull/5372))
These are called `lift_on'_beta` for consistency with `lift_on_beta`; even though we also have `map_mk'` etc in the same file.

### [2020-12-16 07:31:15](https://github.com/leanprover-community/mathlib/commit/78940f4)
chore(*): use notation `ℝ≥0`  ([#5391](https://github.com/leanprover-community/mathlib/pull/5391))

### [2020-12-16 07:31:13](https://github.com/leanprover-community/mathlib/commit/47b3c4b)
feat(algebra/lie/basic): nilpotent and solvable Lie algebras ([#5382](https://github.com/leanprover-community/mathlib/pull/5382))

### [2020-12-16 04:20:19](https://github.com/leanprover-community/mathlib/commit/79e9aee)
feat(equiv/basic): add true_arrow_equiv ([#5388](https://github.com/leanprover-community/mathlib/pull/5388))

### [2020-12-16 01:15:14](https://github.com/leanprover-community/mathlib/commit/26f8b28)
chore(scripts): update nolints.txt ([#5384](https://github.com/leanprover-community/mathlib/pull/5384))
I am happy to remove some nolints for you!

### [2020-12-16 01:15:12](https://github.com/leanprover-community/mathlib/commit/e264e5f)
feat(tactic/ext): `ext?` displays applied lemmas ([#5375](https://github.com/leanprover-community/mathlib/pull/5375))
refactor using `state_t` instead of state passing style

### [2020-12-15 22:23:52](https://github.com/leanprover-community/mathlib/commit/2ee0f1e)
feat(category_theory/isomorphism): is_iso versions ([#5355](https://github.com/leanprover-community/mathlib/pull/5355))
add `is_iso` versions of some existing `iso` lemmas

### [2020-12-15 22:23:50](https://github.com/leanprover-community/mathlib/commit/dbb6b04)
feat(topology/separation): add lemma connected_component_eq_clopen_Inter ([#5335](https://github.com/leanprover-community/mathlib/pull/5335))
Prove the lemma that in a t2 and compact space, the connected component of a point equals the intersection of all its clopen neighbourhoods. Will be useful for work on Profinite sets. The proof that a Profinite set is a limit of finite discrete spaces found at: https://stacks.math.columbia.edu/tag/08ZY uses this lemma. Also some proofs that the category Profinite is reflective in CompactHausdorff uses this lemma.

### [2020-12-15 21:09:34](https://github.com/leanprover-community/mathlib/commit/66eddd8)
chore(algebra/category/Module/monoidal): Speed up the elaboration ([#5383](https://github.com/leanprover-community/mathlib/pull/5383))
This takes the elaboration time from ~5s to ~2.5s for associator_naturality, from ~90s to 5s for pentagon, and from ~14s to ~8s for `triangle`.

### [2020-12-15 21:09:32](https://github.com/leanprover-community/mathlib/commit/b702408)
feat(ring_theory/roots_of_unity): add squarefreeness mod p of minimal polynomial ([#5381](https://github.com/leanprover-community/mathlib/pull/5381))
Two easy results about the reduction `mod p` of the minimal polynomial over `ℤ` of a primitive root of unity: it is separable and hence squarefree.

### [2020-12-15 17:57:30](https://github.com/leanprover-community/mathlib/commit/78e48c0)
ci(lint-copy-mod-doc.py): add reserved notation and set_option linters, enable small_alpha_vrachy_check linter ([#5330](https://github.com/leanprover-community/mathlib/pull/5330))
[As requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/the.20word.20.22to.22/near/219370843), the reserved notation linter checks for `reserve` or `precedence` at the start of a non-comment, non-string literal line in any file other than `tactic.core`.
The new set_option linter disallows `set_option pp`, `set_option profiler` and `set_option trace` at the start of a non-comment, non-string literal line.
I also noticed that the `small_alpha_vrachy_check` linter added in [#4802](https://github.com/leanprover-community/mathlib/pull/4802) wasn't actually called, so I added it to the main `lint` function.

### [2020-12-15 16:43:44](https://github.com/leanprover-community/mathlib/commit/c208a65)
feat(analysis/mean_inequalities): add Minkowski's inequality for the Lebesgue integral of ennreal functions ([#5379](https://github.com/leanprover-community/mathlib/pull/5379))

### [2020-12-15 13:31:21](https://github.com/leanprover-community/mathlib/commit/3a997b1)
fix(group_theory/subgroup): Fix doubly-namespaced instance ([#5378](https://github.com/leanprover-community/mathlib/pull/5378))
Not sure why the linter missed this.

### [2020-12-15 13:31:19](https://github.com/leanprover-community/mathlib/commit/75130b3)
feat(data/set/basic): nonempty set of nonempty subtype ([#5373](https://github.com/leanprover-community/mathlib/pull/5373))

### [2020-12-15 13:31:17](https://github.com/leanprover-community/mathlib/commit/d21d17b)
feat(ring_theory/roots_of_unity): minimal polynomial of primitive roots ([#5322](https://github.com/leanprover-community/mathlib/pull/5322))
I've added some simple results about the minimal polynomial of a primitive root of unity. The next step will be to prove that any two primitive roots have the same minimal polynomial.

### [2020-12-15 10:30:21](https://github.com/leanprover-community/mathlib/commit/0f4ac1b)
feat(category_theory/limits): product comparison simp lemmas ([#5351](https://github.com/leanprover-community/mathlib/pull/5351))
This adds two new simp lemmas to reduce the prod comparison morphism and uses them to golf some proofs

### [2020-12-15 10:30:19](https://github.com/leanprover-community/mathlib/commit/9ba9a98)
chore(category_theory/sites): improve naming ([#5350](https://github.com/leanprover-community/mathlib/pull/5350))
- Improve naming of some lemmas to be more descriptive
- Golf some proofs
- Add some convenience deconstructors which are useful in practice

### [2020-12-15 10:30:17](https://github.com/leanprover-community/mathlib/commit/dd72a98)
feat(group_theory/perm/basic): Bundle sigma_congr_right and sum_congr into monoid_homs ([#5301](https://github.com/leanprover-community/mathlib/pull/5301))
This makes the corresponding subgroups available as `monoid_hom.range`.
As a result, the old subgroup definitions can be removed.
This also adds injectivity and cardinality lemmas.

### [2020-12-15 10:30:14](https://github.com/leanprover-community/mathlib/commit/8041945)
feat(category_theory/monad): monadicity theorems ([#5137](https://github.com/leanprover-community/mathlib/pull/5137))
This is a proof of the reflexive (or crude) monadicity theorem along with a complete proof of Beck's monadicity theorem.
Also renames the prefix for special monad coequalizers to `free_coequalizer` rather than `coequalizer`, to avoid name-clashes when both `monad` and `limits` are imported.

### [2020-12-15 10:30:11](https://github.com/leanprover-community/mathlib/commit/407d138)
chore(category_theory/equivalence): weaken essential surjectivity ([#3821](https://github.com/leanprover-community/mathlib/pull/3821))
Weaken essential surjectivity to be a Prop, rather than the data of the inverse.

### [2020-12-15 07:29:57](https://github.com/leanprover-community/mathlib/commit/a1aa511)
feat(simps): interaction between simps and to_additive ([#5331](https://github.com/leanprover-community/mathlib/pull/5331))
If a definition is both marked `to_additive` and `simps` (in that order), `simps` will from also apply the `to_additive` attribute to its generated lemmas (which creates the additive counterparts of the simp-lemmas).
This also generalizes `set_attribute` to use the default parameter if possible.
This implements half of [#1639](https://github.com/leanprover-community/mathlib/pull/1639).

### [2020-12-15 03:52:57](https://github.com/leanprover-community/mathlib/commit/a959718)
chore(algebra/quadratic_discriminant): golf proofs using limits ([#5339](https://github.com/leanprover-community/mathlib/pull/5339))

### [2020-12-15 01:31:40](https://github.com/leanprover-community/mathlib/commit/ff13cde)
chore(scripts): update nolints.txt ([#5376](https://github.com/leanprover-community/mathlib/pull/5376))
I am happy to remove some nolints for you!

### [2020-12-15 01:31:38](https://github.com/leanprover-community/mathlib/commit/cadaa44)
feat(group_theory/subgroup): Add decidable_mem_range ([#5371](https://github.com/leanprover-community/mathlib/pull/5371))
This means that `fintype (quotient_group.quotient f.range)` can be found by type-class resolution.

### [2020-12-15 01:31:36](https://github.com/leanprover-community/mathlib/commit/b2ab94f)
fix(group_theory): Remove a duplicate fintype instance on quotient_group.quotient ([#5368](https://github.com/leanprover-community/mathlib/pull/5368))
This noncomputable instance was annoying, and can easy be recovered by passing in a classical decidable_pred instance instead.

### [2020-12-15 01:31:34](https://github.com/leanprover-community/mathlib/commit/b364d33)
chore(topology/instances/ennreal): remove summability assumption in tendsto_sum_nat_add ([#5366](https://github.com/leanprover-community/mathlib/pull/5366))
We have currently
```lean
lemma tendsto_sum_nat_add (f : ℕ → ℝ≥0) (hf : summable f) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0)
```
However, the summability assumption is not necessary as otherwise all sums are zero, and the statement still holds. The PR removes the assumption.

### [2020-12-15 01:31:32](https://github.com/leanprover-community/mathlib/commit/4dbb3e2)
chore(data/finsupp/basic): more lemmas about `α →₀ ℕ` ([#5362](https://github.com/leanprover-community/mathlib/pull/5362))
* define `canonically_ordered_add_monoid` instance;
* add a few simp lemmas;
* more lemmas about product over `finsupp.antidiagonal n`;
* define `finsupp.Iic_finset`, use it for `finite_le_nat`.

### [2020-12-15 01:31:30](https://github.com/leanprover-community/mathlib/commit/8de08f7)
chore(order/iterate): generalize lemmas about inequalities and iterations ([#5357](https://github.com/leanprover-community/mathlib/pull/5357))
If `f : α → α` is a monotone function and `x y : ℕ → α` are two
sequences such that `x 0 ≤ y 0`, `x (n + 1) ≤ f (x n)`, and
`f (y n) ≤ y (n + 1)`, then `x n ≤ y n`. This lemma (and its versions
for `<`) generalize `geom_le` as well as `iterate_le_of_map_le`.

### [2020-12-14 23:07:26](https://github.com/leanprover-community/mathlib/commit/d1904fc)
refactor(measure_theory/lp_space): move most of the proof of mem_Lp.add to a new lemma in analysis/mean_inequalities ([#5370](https://github.com/leanprover-community/mathlib/pull/5370))

### [2020-12-14 23:07:24](https://github.com/leanprover-community/mathlib/commit/dc719a9)
feat(algebra/lie/basic): define ideal operations for Lie modules ([#5337](https://github.com/leanprover-community/mathlib/pull/5337))

### [2020-12-14 21:52:23](https://github.com/leanprover-community/mathlib/commit/a649c59)
feat(field_theory/intermediate_field): lift2_alg_equiv ([#5344](https://github.com/leanprover-community/mathlib/pull/5344))
Proves that lift2 is isomorphic as an algebra over the base field

### [2020-12-14 19:54:21](https://github.com/leanprover-community/mathlib/commit/4415dc0)
feat(algebra/algebra/basic): arrow_congr for alg_equiv ([#5346](https://github.com/leanprover-community/mathlib/pull/5346))
This is a copy of equiv.arrow_congr

### [2020-12-14 16:39:30](https://github.com/leanprover-community/mathlib/commit/07b5618)
chore(linear_algebra/{multilinear,alternating}): Generalize smul and neg instance ([#5364](https://github.com/leanprover-community/mathlib/pull/5364))
This brings the generality in line with that of `linear_map`. Notably:
* `has_neg` now exists when only the codomain has negation
* `has_scalar` now exists for the weaker condition of `smul_comm_class` rather than `has_scalar_tower`

### [2020-12-14 16:39:28](https://github.com/leanprover-community/mathlib/commit/b1c56b1)
feat(field_theory.minimal_polynomial): add results for GCD domains ([#5336](https://github.com/leanprover-community/mathlib/pull/5336))
I have added `gcd_domain_dvd`: for GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root.
For `gcd_domain_eq_field_fractions` and `gcd_domain_dvd` I have also added explicit versions for `ℤ`. Unfortunately, it seems impossible (to me at least) to apply the general lemmas and I had to redo the proofs, see [Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Minimal.20polynomial.20over.20.E2.84.9A.20vs.20over.20.E2.84.A4) for more details. (The basic reason seems to be that it's hard to convince lean that `is_scalar_tower ℤ ℚ α` holds using the localization map).

### [2020-12-14 16:39:26](https://github.com/leanprover-community/mathlib/commit/f443792)
feat(topology/subset_properties): add instances for totally_disconnected_spaces ([#5334](https://github.com/leanprover-community/mathlib/pull/5334))
Add the instances subtype.totally_disconnected_space and pi.totally_disconnected_space.

### [2020-12-14 16:39:24](https://github.com/leanprover-community/mathlib/commit/d36af18)
feat(tactic/induction): add induction'/cases'/eliminate_hyp/eliminate_expr tactics ([#5027](https://github.com/leanprover-community/mathlib/pull/5027))
This PR adds interactive tactics `induction'` and `cases'` as well as
non-interactive variants `eliminate_hyp` and `eliminate_expr`. The tactics are
similar to standard `induction` and `cases`, but they feature several
improvements:
- `induction'` performs 'dependent induction', which means it takes the indices
  of indexed inductive types fully into account. This is convenient, for example,
  for programming language or logic formalisations, which tend to rely heavily on
  indexed types.
- `induction'` by default generalises everything that can be generalised. This
  is to support beginners, who often struggle to identify that a proof requires
  a generalised induction hypothesis. In cases where this feature hinders more
  than it helps, it can easily be turned off.
- `induction'` and `cases'` generate much more human-friendly names than their
  standard counterparts. This is, again, mostly to support beginners. Experts
  should usually supply explicit names to make proof scripts more robust.
- `cases'` works for some rare goals which `cases` does not support, but should
  otherwise be mostly a drop-in replacement (except for the generated names).

### [2020-12-14 13:16:21](https://github.com/leanprover-community/mathlib/commit/a65de99)
feat(data/equiv): Add `congr_arg`, `congr_fun`, and `ext_iff` lemmas to equivs ([#5367](https://github.com/leanprover-community/mathlib/pull/5367))
These members already exist on the corresponding homs

### [2020-12-14 13:16:18](https://github.com/leanprover-community/mathlib/commit/dad88d8)
feat(field_theory/splitting_field): add splits_X theorem ([#5343](https://github.com/leanprover-community/mathlib/pull/5343))
This is a handy result and isn't definitionally a special case of splits_X_sub_C

### [2020-12-14 13:16:15](https://github.com/leanprover-community/mathlib/commit/cf7377a)
chore(field_theory/adjoin): move dim/findim lemmas ([#5342](https://github.com/leanprover-community/mathlib/pull/5342))
adjoin.lean has some dim/findim lemmas, some of which could be moved to intermediate_field.lean

### [2020-12-14 13:16:14](https://github.com/leanprover-community/mathlib/commit/0d7ddf1)
chore(order/filter/at_top_bot): add/rename lemmas about limits like `±∞*c` ([#5333](https://github.com/leanprover-community/mathlib/pull/5333))
### New lemmas
* `filter.tendsto.nsmul_at_top` and `filter.tendsto.nsmul_at_bot`;
* `filter.tendsto_mul_self_at_top`;
* `filter.tendsto.at_top_mul_at_bot`, `filter.tendsto.at_bot_mul_at_top`,
  `filter.tendsto.at_bot_mul_at_bot`;
* `filter.tendsto.at_top_of_const_mul`, `filter.tendsto.at_top_of_mul_const`;
* `filter.tendsto.at_top_div_const`, `filter.tendsto.neg_const_mul_at_top`,
  `filter.tendsto.at_top_mul_neg_const`, `filter.tendsto.const_mul_at_bot`,
  `filter.tendsto.at_bot_mul_const`, `filer.tendsto.at_bot_div_const`,
  `filter.tendsto.neg_const_mul_at_bot`, `filter.tendsto.at_bot_mul_neg_const`.
### Renamed lemmas
* `tendsto_pow_at_top` → `filter.tendsto_pow_at_top`;
* `tendsto_at_top_mul_left` → `filter.tendsto.const_mul_at_top'`;
* `tendsto_at_top_mul_right` → `filter.tendsto.at_top_mul_const'`;
* `tendsto_at_top_mul_left'` → `filter.tendsto.const_mul_at_top`;
* `tendsto_at_top_mul_right'` → `filer.tendsto.at_top_mul_const`;
* `tendsto_mul_at_top` → `filter.tendsto.at_top_mul`;
* `tendsto_mul_at_bot` → `filter.tendsto.at_top_mul_neg`;
* `tendsto_at_top_mul_at_top` → `filter.tendsto.at_top_mul_at_top`.

### [2020-12-14 13:16:12](https://github.com/leanprover-community/mathlib/commit/1d37ff1)
feat(analysis/mean_inequalities): add weighted generalized mean inequality for ennreal ([#5316](https://github.com/leanprover-community/mathlib/pull/5316))

### [2020-12-14 13:16:10](https://github.com/leanprover-community/mathlib/commit/cecab59)
feat(group_theory/congruence): Add inv and neg ([#5304](https://github.com/leanprover-community/mathlib/pull/5304))

### [2020-12-14 13:16:08](https://github.com/leanprover-community/mathlib/commit/6dc5000)
feat(computability/language): define formal languages ([#5291](https://github.com/leanprover-community/mathlib/pull/5291))
Lifted from [#5036](https://github.com/leanprover-community/mathlib/pull/5036) in order to include in [#5038](https://github.com/leanprover-community/mathlib/pull/5038) as well.

### [2020-12-14 13:16:05](https://github.com/leanprover-community/mathlib/commit/67b5ff6)
feat(algebra/direct_sum): constructor for morphisms into direct sums ([#5204](https://github.com/leanprover-community/mathlib/pull/5204))

### [2020-12-14 11:45:59](https://github.com/leanprover-community/mathlib/commit/c722b96)
feat (topology/instances/ennreal): summability from finite sum control ([#5363](https://github.com/leanprover-community/mathlib/pull/5363))

### [2020-12-14 10:02:51](https://github.com/leanprover-community/mathlib/commit/91e5b8a)
chore(analysis/normed_space/ordered): minor golfing ([#5356](https://github.com/leanprover-community/mathlib/pull/5356))

### [2020-12-14 10:02:48](https://github.com/leanprover-community/mathlib/commit/2245cfb)
feat(measurable_space): infix notation for measurable_equiv ([#5329](https://github.com/leanprover-community/mathlib/pull/5329))
We use `≃ᵐ` as notation. Note: `≃ₘ` is already used for diffeomorphisms.

### [2020-12-14 08:35:30](https://github.com/leanprover-community/mathlib/commit/6f69741)
chore(analysis/calculus/*): rename `*.of_local_homeomorph` to `local_homeomorph.*_symm` ([#5358](https://github.com/leanprover-community/mathlib/pull/5358))
Rename some lemmas, and make `(f : local_homeomorph _ _)` an explicit argument:
* `has_fderiv_at.of_local_homeomorph` → `local_homeomorph.has_fderiv_at_symm`;
* `times_cont_diff_at.of_local_homeomorph` → `local_homeomorph.times_cont_diff_at_symm`.
If we want to apply one of these lemmas to prove smoothness of, e.g., `arctan`, `log`, or `arcsin`, then the goal
has no `local_homeomorph.symm`, and we need to explicitly supply a `local_homeomorph` with an appropriate `inv_fun`.
Also add some lemmas that help to prove that the inverse function is **not** differentiable at a point.

### [2020-12-14 02:41:32](https://github.com/leanprover-community/mathlib/commit/714bc15)
feat(category_theory/adjunction): adjoint lifting theorems ([#5118](https://github.com/leanprover-community/mathlib/pull/5118))
Proves the [adjoint lifting theorem](https://ncatlab.org/nlab/show/adjoint+lifting+theorem) and the [adjoint triangle theorem](https://ncatlab.org/nlab/show/adjoint+triangle+theorem).
The intent here is for all but the last four statements in the file to be implementation.

### [2020-12-14 01:26:51](https://github.com/leanprover-community/mathlib/commit/b7a9615)
chore(scripts): update nolints.txt ([#5360](https://github.com/leanprover-community/mathlib/pull/5360))
I am happy to remove some nolints for you!

### [2020-12-13 09:58:12](https://github.com/leanprover-community/mathlib/commit/88fb7ca)
chore(analysis/calculus): move the definition of `formal_multilinear_series` to a new file ([#5348](https://github.com/leanprover-community/mathlib/pull/5348))

### [2020-12-13 01:29:56](https://github.com/leanprover-community/mathlib/commit/36eec1a)
chore(scripts): update nolints.txt ([#5341](https://github.com/leanprover-community/mathlib/pull/5341))
I am happy to remove some nolints for you!

### [2020-12-12 23:59:14](https://github.com/leanprover-community/mathlib/commit/eb9164b)
feat(category_theory/sites): naming and attributes ([#5340](https://github.com/leanprover-community/mathlib/pull/5340))
Adds simps projections for sieve arrows and makes the names consistent (some used `mem_` and others used `_apply`, now they only use the latter).

### [2020-12-12 22:41:29](https://github.com/leanprover-community/mathlib/commit/68818b3)
feat(field_theory/galois): Is_galois iff is_galois top ([#5285](https://github.com/leanprover-community/mathlib/pull/5285))
Proves that E/F is Galois iff top/F is Galois.

### [2020-12-12 17:17:36](https://github.com/leanprover-community/mathlib/commit/5ced4dd)
feat(ring_theory/finiteness): add iff_quotient_mv_polynomial ([#5321](https://github.com/leanprover-community/mathlib/pull/5321))
Add characterizations of finite type algebra as quotient of polynomials rings. There are three version of the same lemma, using a `finset`, a `fintype` and `fin n`.

### [2020-12-12 09:03:27](https://github.com/leanprover-community/mathlib/commit/3afdf41)
chore(*): generalize some lemmas from `linear_ordered_semiring` to `ordered_semiring` ([#5327](https://github.com/leanprover-community/mathlib/pull/5327))
API changes:
* Many lemmas now have weaker typeclass assumptions. Sometimes this means that `@myname _ _ _` needs one more `_`.
* Drop `eq_one_of_mul_self_left_cancel` etc in favor of the new `mul_eq_left_iff` etc.
* A few new lemmas that state `monotone` or `strict_mono_incr_on`.

### [2020-12-12 07:17:02](https://github.com/leanprover-community/mathlib/commit/dad5aab)
refactor(ring_theory/polynomial/homogeneous): redefine `mv_polynomial.homogeneous_component` ([#5294](https://github.com/leanprover-community/mathlib/pull/5294))
* redefine `homogeneous_component` using `finsupp.restrict_dom`,
  “upgrade” it to a `linear_map`;
* add `coeff_homogeneous_component` and use it to golf some proofs.

### [2020-12-12 07:17:00](https://github.com/leanprover-community/mathlib/commit/9cc8835)
feat(group_theory/perm/subgroup): Add some simple subgroups of permutations ([#5279](https://github.com/leanprover-community/mathlib/pull/5279))

### [2020-12-12 07:16:58](https://github.com/leanprover-community/mathlib/commit/84f9938)
feat(category_theory/sites): sheaves on types ([#5259](https://github.com/leanprover-community/mathlib/pull/5259))

### [2020-12-12 07:16:56](https://github.com/leanprover-community/mathlib/commit/0344aee)
feat(ring_theory/*): various lemmas about quotients, localizations, and polynomials ([#5249](https://github.com/leanprover-community/mathlib/pull/5249))

### [2020-12-12 07:16:53](https://github.com/leanprover-community/mathlib/commit/d032380)
feat(field_theory/normal): normal_of_alg_equiv ([#5225](https://github.com/leanprover-community/mathlib/pull/5225))
Proves that normal is preserved by an alg_equiv

### [2020-12-12 04:38:13](https://github.com/leanprover-community/mathlib/commit/f51fe7b)
chore(data/fin): Improve docstrings, rename `coe_sub_nat`, add `nat_add_zero` ([#5290](https://github.com/leanprover-community/mathlib/pull/5290))
These are cherry-picked from the tuple PR, [#4406](https://github.com/leanprover-community/mathlib/pull/4406).
`coe_sub_nat` was previously named `sub_nat_coe`, but this didn't match `coe_nat_add` and `coe_add_nat`.

### [2020-12-12 01:48:20](https://github.com/leanprover-community/mathlib/commit/2609428)
chore(scripts): update nolints.txt ([#5328](https://github.com/leanprover-community/mathlib/pull/5328))
I am happy to remove some nolints for you!

### [2020-12-12 01:48:18](https://github.com/leanprover-community/mathlib/commit/b02c529)
feat(category_theory/limits): strengthen simp lemma ([#5326](https://github.com/leanprover-community/mathlib/pull/5326))
Makes a simp lemma slightly stronger

### [2020-12-12 01:48:17](https://github.com/leanprover-community/mathlib/commit/e7ca801)
feat(data/list/chain): induction up the chain ([#5325](https://github.com/leanprover-community/mathlib/pull/5325))
Slightly strengthen statements that were there before

### [2020-12-12 01:48:13](https://github.com/leanprover-community/mathlib/commit/f0c8a15)
chore(algebra/ordered_ring): golf some proofs using `strict_mono_incr_on` ([#5323](https://github.com/leanprover-community/mathlib/pull/5323))

### [2020-12-12 01:48:10](https://github.com/leanprover-community/mathlib/commit/01746f8)
feat(outer_measure): define bounded_by ([#5314](https://github.com/leanprover-community/mathlib/pull/5314))
`bounded_by` wrapper around `of_function` that drops the condition that `m ∅ = 0`. 
Refactor `Inf_gen` to use `bounded_by`.
I am also planning to use `bounded_by` for finitary products of measures.
Also add some complete lattice lemmas

### [2020-12-12 01:48:08](https://github.com/leanprover-community/mathlib/commit/3782acf)
feat(topology/algebra/*): Criterion to ensure topological monoids and groups ([#5284](https://github.com/leanprover-community/mathlib/pull/5284))
This is old stuff from the perfectoid project that was never PRed and is useful for the liquid tensor experiment.

### [2020-12-11 22:54:52](https://github.com/leanprover-community/mathlib/commit/846ee3f)
feat(data/equiv): symm_symm_apply ([#5324](https://github.com/leanprover-community/mathlib/pull/5324))
A little dsimp lemma that's often helpful

### [2020-12-11 20:26:08](https://github.com/leanprover-community/mathlib/commit/63e1ad4)
chore(group_theory/perm/basic): Add missing lemmas ([#5320](https://github.com/leanprover-community/mathlib/pull/5320))
These lemmas existed for left multiplication but not right multiplication

### [2020-12-11 20:26:06](https://github.com/leanprover-community/mathlib/commit/90aa66b)
chore(algebra/big_operators/basic): Rename hypotheses for clarity ([#5318](https://github.com/leanprover-community/mathlib/pull/5318))
This makes them somewhat more consistent with `prod_bij`

### [2020-12-11 16:44:08](https://github.com/leanprover-community/mathlib/commit/3a88a9e)
chore(data/subtype): Add coind_bijective and map_involutive ([#5319](https://github.com/leanprover-community/mathlib/pull/5319))

### [2020-12-11 16:44:06](https://github.com/leanprover-community/mathlib/commit/029b258)
chore(linear_algebra/tensor_product): Actually relax the requirements for add_comm_group ([#5315](https://github.com/leanprover-community/mathlib/pull/5315))
A previous commit ([#5305](https://github.com/leanprover-community/mathlib/pull/5305)) changed the definition to not need these, but forgot to actually change these.

### [2020-12-11 16:44:04](https://github.com/leanprover-community/mathlib/commit/db712d5)
chore(*): simp lemmas for `tendsto`, `Ixx`, and `coe` ([#5296](https://github.com/leanprover-community/mathlib/pull/5296))
* For `(f : α → β) (l : filter β)`, simplify `tendsto (λ a : Ixx*, f x) at_top l`
  to `tendsto f _ l`, and similarly for `at_bot`.
* For `(f : α → Ixx*) (l : filter α)`, simplify
  `tendsto f l at_top` to `tendsto (λ x, (f x : β)) l _`, and
  similarly for `at_bot`.
Here `Ixx*` is one of the intervals `Ici a`, `Ioi a`, `Ioo a b` etc,
and `_` is a filter that depends on the choice of `Ixx` and
`at_top`/`at_bot`.
* Drop some “nontriviality” assumptions like `no_top_order` for lemmas
about `Ioi a`.

### [2020-12-11 13:45:51](https://github.com/leanprover-community/mathlib/commit/a372dfc)
chore(*): don't assume `sub_eq_add_neg` and `div_eq_mul_inv` are defeq ([#5302](https://github.com/leanprover-community/mathlib/pull/5302))
This PR prepares for a follow-up PR ([#5303](https://github.com/leanprover-community/mathlib/pull/5303)) that adds `div` and `sub` fields to (`add_`)`group`(`_with_zero`). That follow-up PR is intended to fix the following kind of diamonds:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no `∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the `(/)` coming from `group_with_zero_has_div` cannot be defeq to the `(/)` coming from `foo.has_div`.
As a consequence of making the `has_div` instances defeq, we can no longer assume that `(div_eq_mul_inv a b : a / b = a * b⁻¹) = rfl` for all groups. This preparation PR should have changed all places in mathlib that assumed defeqness, to rewrite explicitly instead.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60div.60.20as.20a.20field.20in.20.60group(_with_zero).60

### [2020-12-11 12:35:50](https://github.com/leanprover-community/mathlib/commit/d2ae4e2)
feat(ring_theory/witt_vector): truncated Witt vectors, definition and ring structure ([#5162](https://github.com/leanprover-community/mathlib/pull/5162))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-11 10:57:57](https://github.com/leanprover-community/mathlib/commit/6288eed)
feat(linear_algebra/alternating): Add alternatization of multilinear_map ([#5187](https://github.com/leanprover-community/mathlib/pull/5187))
This adds:
* `def multilinear_map.alternatize`
* `lemma alternating_map.to_multilinear_map_alternize`

### [2020-12-11 01:46:47](https://github.com/leanprover-community/mathlib/commit/dbdba55)
chore(scripts): update nolints.txt ([#5313](https://github.com/leanprover-community/mathlib/pull/5313))
I am happy to remove some nolints for you!

### [2020-12-11 01:46:45](https://github.com/leanprover-community/mathlib/commit/8817c3e)
chore(linear_algebra/tensor_product): Relax the ring requirement to semiring for the group instance ([#5305](https://github.com/leanprover-community/mathlib/pull/5305))

### [2020-12-11 01:46:44](https://github.com/leanprover-community/mathlib/commit/9e550f2)
feat(topology/separation): finite t1 spaces are discrete ([#5298](https://github.com/leanprover-community/mathlib/pull/5298))
These lemmas should simplify the arguments of [#4301](https://github.com/leanprover-community/mathlib/pull/4301)
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/discrete_topology/near/218932564 
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->

### [2020-12-11 01:46:41](https://github.com/leanprover-community/mathlib/commit/2c0b43d)
feat(combinatorics/simple_graph/degree_sum): degree-sum formula and handshake lemma ([#5263](https://github.com/leanprover-community/mathlib/pull/5263))
Adds the theorem that the sum of the degrees of the vertices of a simple graph is twice the number of edges.  Also adds corollaries like the handshake lemma, which is that the number of odd-degree vertices is even.
The corollary `exists_ne_odd_degree_if_exists_odd` is in anticipation of Sperner's lemma.

### [2020-12-10 23:19:05](https://github.com/leanprover-community/mathlib/commit/918d5a9)
chore(data/finsupp/basic): redefine `finsupp.filter` ([#5310](https://github.com/leanprover-community/mathlib/pull/5310))
Also use lemmas about `indicator_function` and `function.update` to
golf some proofs about `finsupp.single`.

### [2020-12-10 23:19:03](https://github.com/leanprover-community/mathlib/commit/c295873)
feat(algebra/module/basic): {nat,int}_smul_apply ([#5308](https://github.com/leanprover-community/mathlib/pull/5308))

### [2020-12-10 21:44:19](https://github.com/leanprover-community/mathlib/commit/c9793b5)
chore(data/mv_polynomial): delete stray comments ([#5312](https://github.com/leanprover-community/mathlib/pull/5312))

### [2020-12-10 21:44:16](https://github.com/leanprover-community/mathlib/commit/f72734a)
chore(data/complex/exponential): add `inv_one_add_tan_sq` etc ([#5299](https://github.com/leanprover-community/mathlib/pull/5299))
* mark `cos_sq_add_sin_sq` and `sin_sq_add_cos_sq` as `@[simp]`;
* add lemmas representing `sin x` and `cos x` as functions of `tan x`.

### [2020-12-10 21:44:14](https://github.com/leanprover-community/mathlib/commit/32b2e30)
feat(category_theory/monad): special coequalizers for a monad ([#5239](https://github.com/leanprover-community/mathlib/pull/5239))
Two important coequalizer diagrams related to a monad

### [2020-12-10 18:39:41](https://github.com/leanprover-community/mathlib/commit/4e8486b)
feat(algebra/group/hom): add_monoid_hom.sub_apply ([#5307](https://github.com/leanprover-community/mathlib/pull/5307))

### [2020-12-10 18:39:39](https://github.com/leanprover-community/mathlib/commit/be6c37c)
feat(algebra/big_operators/finsupp): rename variables, and move to top of file ([#5306](https://github.com/leanprover-community/mathlib/pull/5306))

### [2020-12-10 17:02:36](https://github.com/leanprover-community/mathlib/commit/f3c9d20)
chore(linear_algebra/determinant): Golf a proof ([#5309](https://github.com/leanprover-community/mathlib/pull/5309))

### [2020-12-10 17:02:33](https://github.com/leanprover-community/mathlib/commit/cdb1398)
feat(category_theory/limits): any functor preserves split coequalizers ([#5246](https://github.com/leanprover-community/mathlib/pull/5246))
Once [#5230](https://github.com/leanprover-community/mathlib/pull/5230) merges, the only diff in this PR should be in `src/category_theory/limits/preserves/shapes/equalizers.lean`

### [2020-12-10 13:59:01](https://github.com/leanprover-community/mathlib/commit/12d097e)
feat(category_theory/sites/sieves): change presieve operation defs ([#5295](https://github.com/leanprover-community/mathlib/pull/5295))
change the definitions of operations on presieves to avoid `eq_to_hom` and use inductive types instead, which makes proofs a lot nicer

### [2020-12-10 13:58:58](https://github.com/leanprover-community/mathlib/commit/3f42fb4)
feat(group_theory/perm/sign): Add sign_sum_congr ([#5266](https://github.com/leanprover-community/mathlib/pull/5266))

### [2020-12-10 13:58:56](https://github.com/leanprover-community/mathlib/commit/90755c3)
refactor(order/filter/ultrafilter): drop `filter.is_ultrafilter` ([#5264](https://github.com/leanprover-community/mathlib/pull/5264))
Use bundled `ultrafilter`s instead.

### [2020-12-10 13:58:54](https://github.com/leanprover-community/mathlib/commit/2bf0c2e)
feat(group_theory/group_action/sub_mul_action): add a has_zero instance ([#5216](https://github.com/leanprover-community/mathlib/pull/5216))

### [2020-12-10 10:51:03](https://github.com/leanprover-community/mathlib/commit/702b1e8)
refactor(data/finsupp/basic): merge `finsupp.of_multiset` and `multiset.to_finsupp` ([#5237](https://github.com/leanprover-community/mathlib/pull/5237))
* redefine `finsupp.to_multiset` as an `add_equiv`;
* drop `finsupp.equiv_multiset` and `finsupp.of_multiset`;
* define `multiset.to_finsupp` as `finsupp.to_multiset.symm`.

### [2020-12-10 08:44:55](https://github.com/leanprover-community/mathlib/commit/ac669c7)
chore(category_theory/limits/preserves): cleanup ([#4163](https://github.com/leanprover-community/mathlib/pull/4163))
(edited to update).
This PR entirely re-does the construction of limits from products and equalizers in a shorter way. With the new preserves limits machinery this new construction also shows that a functor which preserves products and equalizers preserves all limits, which previously was *really* annoying to do

### [2020-12-10 07:39:19](https://github.com/leanprover-community/mathlib/commit/e68d2d7)
feat(category_theory/sites): category of sheaves ([#5255](https://github.com/leanprover-community/mathlib/pull/5255))
Category of sheaves on a grothendieck topology
(cc: @kckennylau)

### [2020-12-10 01:25:50](https://github.com/leanprover-community/mathlib/commit/ba568a6)
chore(scripts): update nolints.txt ([#5297](https://github.com/leanprover-community/mathlib/pull/5297))
I am happy to remove some nolints for you!

### [2020-12-09 19:09:52](https://github.com/leanprover-community/mathlib/commit/84c0132)
chore(data/indicator_function): a few more `simp` lemmas ([#5293](https://github.com/leanprover-community/mathlib/pull/5293))
* drop `indicator_of_support_subset` in favor of the new `indicator_eq_self`;
* add a few more lemmas: `indicator_apply_eq_self`,
 `indicator_apply_eq_zero`, `indicator_eq_zero`, `indicator_eq_zero'`

### [2020-12-09 17:36:09](https://github.com/leanprover-community/mathlib/commit/bf25d26)
chore(data/set/intervals/proj_Icc): add `strict_mono_incr_on` ([#5292](https://github.com/leanprover-community/mathlib/pull/5292))
* rename `set.Icc_extend_monotone` to `monotone.Icc_extend`;
* add `set.strict_mono_incr_on_proj_Icc` and `strict_mono.strict_mono_incr_on_Icc_extend`.

### [2020-12-09 17:36:06](https://github.com/leanprover-community/mathlib/commit/efe18d5)
feat(measure_theory/interval_integral): continuous implies interval_integrable ([#5288](https://github.com/leanprover-community/mathlib/pull/5288))

### [2020-12-09 17:36:04](https://github.com/leanprover-community/mathlib/commit/e357a33)
chore(linear_algebra/multilinear): Add `linear_map.comp_multilinear_map_dom_dom_congr` ([#5270](https://github.com/leanprover-community/mathlib/pull/5270))

### [2020-12-09 17:36:02](https://github.com/leanprover-community/mathlib/commit/698d6b7)
ci(.github/workflows/dependent-issues.yml): automation for "blocked-by-other-PR" label ([#5261](https://github.com/leanprover-community/mathlib/pull/5261))
When a PR or issue is updated, the [dependent-issues](https://github.com/z0al/dependent-issues) action will do the following on all PRs which are marked as dependent on it (with the text `- [ ] depends on: #blah` that we're already using):
- add / remove the "blocked-by-other-PR" label
- post / edit a comment with the current status of its dependencies (this is slightly redundant, given that we have another action which checks off the dependent PRs in the PR comments, but the extra notifications might be useful).
- it also adds a new status check which is pending (yellow) until all dependencies are closed.

### [2020-12-09 16:13:00](https://github.com/leanprover-community/mathlib/commit/a87f62b)
feat(category_theory/limits/preserves): preserving binary products ([#5061](https://github.com/leanprover-community/mathlib/pull/5061))
This moves and re-does my old file about preserving binary products to match the new API and framework for preservation of special shapes, and also cleans up some existing API. 
(I can split this up if necessary but they're all pretty minor changes, so hope this is okay!)

### [2020-12-09 09:24:04](https://github.com/leanprover-community/mathlib/commit/d12a731)
chore(data/mv_polynomial): mark `mv_polynomial.ext` as `@[ext]` ([#5289](https://github.com/leanprover-community/mathlib/pull/5289))

### [2020-12-09 04:36:44](https://github.com/leanprover-community/mathlib/commit/1f309c5)
feat(analysis/special_functions): `real.log` is infinitely smooth away from zero ([#5116](https://github.com/leanprover-community/mathlib/pull/5116))
Also redefine it using `order_iso.to_homeomorph` and prove more lemmas about limits of `exp`/`log`.

### [2020-12-09 01:42:58](https://github.com/leanprover-community/mathlib/commit/2032f7b)
chore(scripts): update nolints.txt ([#5287](https://github.com/leanprover-community/mathlib/pull/5287))
I am happy to remove some nolints for you!

### [2020-12-09 01:42:56](https://github.com/leanprover-community/mathlib/commit/7ae1165)
chore(data/pi): Express `single` in terms of `function.update` ([#5283](https://github.com/leanprover-community/mathlib/pull/5283))
These were originally introduced in [#3513](https://github.com/leanprover-community/mathlib/pull/3513).
Perhaps `function.update` wasn't as well developed back then.

### [2020-12-08 22:41:41](https://github.com/leanprover-community/mathlib/commit/1e3447b)
chore(data/equiv/mul_add): Split out the group structure on automorphisms ([#5281](https://github.com/leanprover-community/mathlib/pull/5281))
This prevents `group_theory.perm.basic` being imported into lots of files that don't care about permutations.
The argument here is that `add_aut` is to `add_equiv` as `perm` is to `equiv`: `perm` gets its group structure in a separate file to where `equiv` is defined, so `add_aut`, `mul_aut`, and `ring_aut` should too.
This adds back imports of `group_theory.perm.basic` to downstream files that inherited them through `data.equiv.mul_add`.

### [2020-12-08 18:18:54](https://github.com/leanprover-community/mathlib/commit/4c9499f)
chore(algebra/group/pi): Split into multiple files ([#5280](https://github.com/leanprover-community/mathlib/pull/5280))
This allows files that appear before `ordered_group` to still use `pi.monoid` etc.

### [2020-12-08 16:34:05](https://github.com/leanprover-community/mathlib/commit/b5ab2f7)
feat(topology/algebra/ordered): add lemmas about `map coe at_top/at_bot` ([#5238](https://github.com/leanprover-community/mathlib/pull/5238))

### [2020-12-08 15:28:08](https://github.com/leanprover-community/mathlib/commit/7f5a5dd)
feat(category_theory/limits): split coequalizers ([#5230](https://github.com/leanprover-community/mathlib/pull/5230))
Define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split coequalizer, and show that every split coequalizer is a coequalizer and absolute.
Define split pairs and `G`-split pairs.
These definitions and constructions are useful in particular for the monadicity theorems.

### [2020-12-08 13:47:48](https://github.com/leanprover-community/mathlib/commit/64ddb12)
feat(analysis/mean_inequalities): add Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions ([#5267](https://github.com/leanprover-community/mathlib/pull/5267))

### [2020-12-08 10:43:05](https://github.com/leanprover-community/mathlib/commit/3996bd4)
chore(logic/basic): add a few `simp` lemmas ([#5278](https://github.com/leanprover-community/mathlib/pull/5278))
Also add `fintype.prod_eq_single`.

### [2020-12-08 10:43:02](https://github.com/leanprover-community/mathlib/commit/d3bbaeb)
chore(combinatorics/composition): use `order_embedding` ([#5276](https://github.com/leanprover-community/mathlib/pull/5276))
* use `order_embedding` for `composition.boundary`
* use `order_embedding` for `composition.embedding`
* add `max_eq_right_iff` etc
* golf some proofs

### [2020-12-08 10:43:00](https://github.com/leanprover-community/mathlib/commit/51f5ca3)
chore(group_theory/perm): Add alternate formulation of (sum|sigma)_congr lemmas ([#5260](https://github.com/leanprover-community/mathlib/pull/5260))
These lemmas existed already for `equiv`, but not for `perm` or for `perm` via group structures.

### [2020-12-08 07:36:20](https://github.com/leanprover-community/mathlib/commit/ac6fc38)
chore(*): move/add lemmas about `disjoint` ([#5277](https://github.com/leanprover-community/mathlib/pull/5277))
* `set.disjoint_compl_left` and `set.disjoint_compl_right`:
  - generalize to any `boolean_algebra`,
  - move to `order/boolean_algebra`,
  - drop `set.` prefix,
  - make the argument implicit to follow the style of other lemmas in `order/boolean_algebra`
* add `set.disjoint_empty` and `set.empty_disjoint`
* add `disjoint_top` and `top_disjoint`, use in `set.disjoint_univ`and `set.univ_disjoint`.

### [2020-12-08 07:36:17](https://github.com/leanprover-community/mathlib/commit/ef377a9)
chore(data/list/sort): docs, add a few lemmas ([#5274](https://github.com/leanprover-community/mathlib/pull/5274))
 * Add a module docstring and section headers.
* Rename `list.eq_of_sorted_of_perm` to `list.eq_of_perm_of_sorted`;
  the new name reflects the order of arguments.
* Add a few lemmas.

### [2020-12-08 07:36:15](https://github.com/leanprover-community/mathlib/commit/aec64b1)
feat(category_theory/monad): generalise algebra colimits ([#5234](https://github.com/leanprover-community/mathlib/pull/5234))
Assumption generalisations and universe generalisations

### [2020-12-08 07:36:13](https://github.com/leanprover-community/mathlib/commit/7360178)
feat(category_theory/closed/types): presheaf category is cartesian closed ([#4897](https://github.com/leanprover-community/mathlib/pull/4897))

### [2020-12-08 05:05:55](https://github.com/leanprover-community/mathlib/commit/8f42d73)
chore(data/list/pairwise): add `list.pairwise_pmap` and `list.pairwise.pmap` ([#5273](https://github.com/leanprover-community/mathlib/pull/5273))
Also add `list.pairwise.tail` and use it in the proof of `list.sorted.tail`.

### [2020-12-08 03:20:13](https://github.com/leanprover-community/mathlib/commit/3f4829c)
chore(data/support): zero function has empty support ([#5275](https://github.com/leanprover-community/mathlib/pull/5275))

### [2020-12-08 01:21:19](https://github.com/leanprover-community/mathlib/commit/35f0862)
chore(scripts): update nolints.txt ([#5272](https://github.com/leanprover-community/mathlib/pull/5272))
I am happy to remove some nolints for you!

### [2020-12-07 20:04:10](https://github.com/leanprover-community/mathlib/commit/b173925)
refactor(data/fin): use `order_embedding` for many maps ([#5251](https://github.com/leanprover-community/mathlib/pull/5251))
Also swap `data.fin` with `order.rel_iso` in the import tree.

### [2020-12-07 20:04:08](https://github.com/leanprover-community/mathlib/commit/b9689bd)
feat(topology/algebra/infinite_sum): add lemmas about continuous linear maps ([#5243](https://github.com/leanprover-community/mathlib/pull/5243))

### [2020-12-07 17:05:50](https://github.com/leanprover-community/mathlib/commit/f730137)
chore(logic/basic): add `and.congr_left_iff` and `@[simp]` attrs ([#5268](https://github.com/leanprover-community/mathlib/pull/5268))

### [2020-12-07 10:37:13](https://github.com/leanprover-community/mathlib/commit/44400c9)
feat(dynamics/circle/rotation_number): translation numbers define a group action up to a semiconjugacy ([#5138](https://github.com/leanprover-community/mathlib/pull/5138))
Formalize a theorem by Étienne Ghys: given two lifts `f₁`, `f₂` of
actions of a group `G` on the circle by orientation preserving
homeomorphisms to the real line, assume that for each `g : G` the
translation numbers of `f₁ g` and `f₂ g` are equal. Then the actions
are semiconjugate by a (possibly discontinuous) circle map.

### [2020-12-07 08:45:14](https://github.com/leanprover-community/mathlib/commit/f0ceb6b)
feat(analysis/mean_inequalities): add young_inequality for nnreal and ennreal with real exponents ([#5242](https://github.com/leanprover-community/mathlib/pull/5242))
The existing young_inequality for nnreal has nnreal exponents. This adds a version with real exponents with the is_conjugate_exponent property, and a similar version for ennreal with real exponents.

### [2020-12-07 06:49:09](https://github.com/leanprover-community/mathlib/commit/914d2b1)
chore(topology/category/Profinite): Fix docstring ([#5265](https://github.com/leanprover-community/mathlib/pull/5265))

### [2020-12-07 03:33:52](https://github.com/leanprover-community/mathlib/commit/b2427d5)
feat(order/filter/ultrafilter): Restriction of ultrafilters along large embeddings ([#5195](https://github.com/leanprover-community/mathlib/pull/5195))
This PR adds the fact that the `comap` of an ultrafilter along a "large" embedding (meaning the image is large w.r.t. the ultrafilter) is again an ultrafilter.

### [2020-12-07 01:24:27](https://github.com/leanprover-community/mathlib/commit/67eb675)
chore(scripts): update nolints.txt ([#5262](https://github.com/leanprover-community/mathlib/pull/5262))
I am happy to remove some nolints for you!

### [2020-12-06 20:08:34](https://github.com/leanprover-community/mathlib/commit/8d54d52)
chore(topology/algebra/ordered): generalize `intermediate_value_Icc` etc ([#5235](https://github.com/leanprover-community/mathlib/pull/5235))
Several lemmas assumed that the codomain is a conditionally complete
linear order while actually the statements are true for a linear
order. Also introduce `mem_range_of_exists_le_of_exists_ge` and use it
in `surjective_of_continuous`.

### [2020-12-06 20:08:32](https://github.com/leanprover-community/mathlib/commit/9cb27c9)
chore(ring_theory/algebra_tower): generalize `is_scalar_tower.right` ([#5224](https://github.com/leanprover-community/mathlib/pull/5224))
The old instance for `[is_scalar_tower R S S]` assumed
[comm_semiring S]` instead of `[semiring S]`.

### [2020-12-06 20:08:30](https://github.com/leanprover-community/mathlib/commit/128b316)
feat(number_theory/primes_congruent_one): infinitely many primes congruent to 1 ([#5217](https://github.com/leanprover-community/mathlib/pull/5217))
I prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`.
 I am not sure that `p ≡ 1 [MOD k]` is the recommended way of stating this in mathlib (instead of using `nat.cast_ring_hom `), I can change it if needed. Also, I don't know if it is appropriate to create a new file, but I didn't see any reasonable location.

### [2020-12-06 18:56:25](https://github.com/leanprover-community/mathlib/commit/b3aa052)
feat(combinatorics/simple_graph/basic): introduce incidence sets, graph construction from relation ([#5191](https://github.com/leanprover-community/mathlib/pull/5191))
Add incidence sets and some lemmas, including a proof of equivalence between the neighbor set of a vertex and its incidence set. Add a graph construction from a given relation.
Definitions and lemmas adapted from [simple_graphs2](https://github.com/leanprover-community/mathlib/blob/simple_graphs2/src/combinatorics/simple_graph/basic.lean#L317)

### [2020-12-06 11:43:56](https://github.com/leanprover-community/mathlib/commit/c88e8f3)
refactor(*): drop `topology/instances/complex` ([#5208](https://github.com/leanprover-community/mathlib/pull/5208))
* drop `topology/instances/complex`, deduce topology from `normed_space` instead;
* generalize continuity of `polynomial.eval` to any `topological_ring`; add versions for `eval₂` and `aeval`;
* replace `polynomial.tendsto_infinity` with `tendsto_abv_at_top`, add versions for `eval₂`, `aeval`, as well as `norm` instead of `abv`.
* generalize `complex.exists_forall_abs_polynomial_eval_le` to any `[normed_ring R] [proper_space R]` such that norm
  is multiplicative, rename to `polynomial.exists_forall_norm_le`.

### [2020-12-06 10:31:29](https://github.com/leanprover-community/mathlib/commit/29a1731)
feat(ring_theory/witt_vector): common identities between operators on Witt vectors ([#5161](https://github.com/leanprover-community/mathlib/pull/5161))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-06 07:55:26](https://github.com/leanprover-community/mathlib/commit/339bd9a)
chore(*): clean up several unnecessary let statements ([#5257](https://github.com/leanprover-community/mathlib/pull/5257))
Cleans up a few `let`s and `letI`s and a `have` and a `set` that have made it into some proofs in the library but do not seem to do anything for the proof.

### [2020-12-06 07:55:24](https://github.com/leanprover-community/mathlib/commit/12a8361)
feat(data/polynomial): simp lemmas about polynomial derivatives ([#5256](https://github.com/leanprover-community/mathlib/pull/5256))
Add simp lemmas derivative_bit0 derivative_bit1 and derivative_X_pow

### [2020-12-06 07:55:21](https://github.com/leanprover-community/mathlib/commit/c6de6e4)
chore(algebra/group_power): mark `map_pow` etc as `@[simp]` ([#5253](https://github.com/leanprover-community/mathlib/pull/5253))

### [2020-12-06 04:52:54](https://github.com/leanprover-community/mathlib/commit/8538071)
doc(data/list): fix `erasep` doc string ([#5254](https://github.com/leanprover-community/mathlib/pull/5254))
closes [#5252](https://github.com/leanprover-community/mathlib/pull/5252)

### [2020-12-06 01:24:31](https://github.com/leanprover-community/mathlib/commit/065bd5f)
chore(scripts): update nolints.txt ([#5250](https://github.com/leanprover-community/mathlib/pull/5250))
I am happy to remove some nolints for you!

### [2020-12-05 20:21:10](https://github.com/leanprover-community/mathlib/commit/7e8e174)
style(combinatorics/simple_graph/basic): edit proof of lemma to match style guidelines ([#5245](https://github.com/leanprover-community/mathlib/pull/5245))
Rewrite proof of `adj_iff_exists_edge` to match style guidelines.

### [2020-12-05 20:21:06](https://github.com/leanprover-community/mathlib/commit/ae99c76)
feat(field_theory/galois): Is_galois iff is_galois bot ([#5231](https://github.com/leanprover-community/mathlib/pull/5231))
Proves that E/F is Galois iff E/bot is Galois.
This is useful in Galois theory because it gives a new way of showing that E/F is Galois:
1) Show that bot is the fixed field of some subgroup
2) Apply `is_galois.of_fixed_field`
3) Apply `is_galois_iff_is_galois_bot`
More to be added later (once [#5225](https://github.com/leanprover-community/mathlib/pull/5225) is merged): Galois is preserved by alg_equiv, is_galois_iff_galois_top

### [2020-12-05 20:21:04](https://github.com/leanprover-community/mathlib/commit/ddfba42)
chore(data/multiset/basic): make `card` a bundled `add_monoid_hom` ([#5228](https://github.com/leanprover-community/mathlib/pull/5228))
Other changes:
* use `/-! ###` in section headers;
* move `add_monoid` section above `card`;
* fix docstrings of `multiset.choose_x` and `multiset.choose`.

### [2020-12-05 20:21:02](https://github.com/leanprover-community/mathlib/commit/1f64814)
chore(data/equiv/ring): add `symm_symm` and `coe_symm_mk` ([#5227](https://github.com/leanprover-community/mathlib/pull/5227))
Also generalize `map_mul` and `map_add` to `[has_mul R] [has_add R]`
instead of `[semiring R]`.

### [2020-12-05 18:53:49](https://github.com/leanprover-community/mathlib/commit/d4bd4cd)
fix(topology/algebra/infinite_sum): fix docstring typos and add example ([#5159](https://github.com/leanprover-community/mathlib/pull/5159))

### [2020-12-05 16:59:01](https://github.com/leanprover-community/mathlib/commit/83b13d1)
feat(category_theory/limits): morphisms to equalizer ([#5233](https://github.com/leanprover-community/mathlib/pull/5233))
The natural bijection for morphisms to an equalizer and the dual.

### [2020-12-05 16:58:59](https://github.com/leanprover-community/mathlib/commit/dd11498)
chore(linear_algebra/basic): redefine `restrict` ([#5229](https://github.com/leanprover-community/mathlib/pull/5229))
Use `dom_restrict` and `cod_restrict`

### [2020-12-05 13:48:51](https://github.com/leanprover-community/mathlib/commit/481f5e0)
chore(data/prod): `prod.swap` is `bijective` ([#5226](https://github.com/leanprover-community/mathlib/pull/5226))

### [2020-12-05 09:58:53](https://github.com/leanprover-community/mathlib/commit/c5009dd)
chore(data/equiv/basic): Add missing refl/trans/symm simp lemmas ([#5223](https://github.com/leanprover-community/mathlib/pull/5223))

### [2020-12-05 07:50:28](https://github.com/leanprover-community/mathlib/commit/3972da8)
chore(category_theory/limits/preserves): make names consistent ([#5240](https://github.com/leanprover-community/mathlib/pull/5240))
adjusted names and namespaces to match [#5044](https://github.com/leanprover-community/mathlib/pull/5044)

### [2020-12-05 07:50:26](https://github.com/leanprover-community/mathlib/commit/39a3b58)
feat(order/filter/at_top_bot): `order_iso` maps `at_top` to `at_top` ([#5236](https://github.com/leanprover-community/mathlib/pull/5236))

### [2020-12-05 07:50:24](https://github.com/leanprover-community/mathlib/commit/147a81a)
chore(category_theory/limits): preserving coequalizers ([#5212](https://github.com/leanprover-community/mathlib/pull/5212))
dualise stuff from before

### [2020-12-05 07:50:22](https://github.com/leanprover-community/mathlib/commit/b82eb7a)
refactor(combinatorics/simple_graph/matching): change definition of matching ([#5210](https://github.com/leanprover-community/mathlib/pull/5210))
Refactored definition of matching per @eric-wieser's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535102524) and @kmill's [suggestion](https://github.com/leanprover-community/mathlib/pull/5156#discussion_r535745112), for the purpose of using `matching.sub_edges` instead of `matching.prop.sub_edges`

### [2020-12-05 07:50:19](https://github.com/leanprover-community/mathlib/commit/dc08f4d)
feat(analysis): define asymptotic equivalence of two functions ([#4979](https://github.com/leanprover-community/mathlib/pull/4979))
This defines the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`. It is required to state, for example, Stirling's formula, or the prime number theorem

### [2020-12-05 04:54:08](https://github.com/leanprover-community/mathlib/commit/de7dbbb)
feat(algebra/group): composition of monoid homs as "bilinear" monoid hom ([#5202](https://github.com/leanprover-community/mathlib/pull/5202))

### [2020-12-05 01:27:37](https://github.com/leanprover-community/mathlib/commit/56c4e73)
chore(scripts): update nolints.txt ([#5232](https://github.com/leanprover-community/mathlib/pull/5232))
I am happy to remove some nolints for you!

### [2020-12-04 21:26:40](https://github.com/leanprover-community/mathlib/commit/0afd3a0)
chore(data/finsupp/basic): Add single_of_single_apply ([#5219](https://github.com/leanprover-community/mathlib/pull/5219))

### [2020-12-04 21:26:38](https://github.com/leanprover-community/mathlib/commit/8a9a5d3)
feat(dynamics): (semi-)flows, omega limits ([#4843](https://github.com/leanprover-community/mathlib/pull/4843))
This code has gone through a couple of iterations since it was first written in summer, when the ambition was 'Morse decompositions in Lean' rather than 'mildly generalise some results from a first course in differential equations'. Nevertheless there's much in here I'm not confident about & would appreciate help with.

### [2020-12-04 15:57:38](https://github.com/leanprover-community/mathlib/commit/5f43079)
doc(data/quot): Fix typo ([#5221](https://github.com/leanprover-community/mathlib/pull/5221))

### [2020-12-04 15:57:35](https://github.com/leanprover-community/mathlib/commit/4ea2e68)
chore(algebra/big_operators/basic): Split prod_cancels_of_partition_cancels in two and add a docstring ([#5218](https://github.com/leanprover-community/mathlib/pull/5218))

### [2020-12-04 15:57:31](https://github.com/leanprover-community/mathlib/commit/5ea96f9)
feat(linear_algebra/multilinear): Add `multilinear_map.coprod` ([#5182](https://github.com/leanprover-community/mathlib/pull/5182))

### [2020-12-04 15:57:29](https://github.com/leanprover-community/mathlib/commit/cb7effa)
feat(ring_theory/discrete_valuation_ring): add additive valuation ([#5094](https://github.com/leanprover-community/mathlib/pull/5094))
Following the approach used for p-adic numbers, we define an additive valuation on a DVR R as a bare function v: R -> nat, with the convention that v(0)=0 instead of +infinity for convenience. Note that we have no `hom` structure (like `monoid_hom` or `add_monoid_hom`) for v(a*b)=v(a)+v(b) and anyway this doesn't even hold if ab=0. We prove all the usual axioms.

### [2020-12-04 14:48:23](https://github.com/leanprover-community/mathlib/commit/f1d30f6)
doc(data/typevec): Fix broken markdown rendering ([#5220](https://github.com/leanprover-community/mathlib/pull/5220))

### [2020-12-04 13:34:38](https://github.com/leanprover-community/mathlib/commit/54c13bd)
docs(data/fp): Move title comment so that it appears in the markdown ([#5222](https://github.com/leanprover-community/mathlib/pull/5222))

### [2020-12-04 10:35:26](https://github.com/leanprover-community/mathlib/commit/30467f4)
feat(field_theory/adjoin): induction on adjoin ([#5173](https://github.com/leanprover-community/mathlib/pull/5173))
This is another adjoin induction lemma that will be used in an upcoming PR.

### [2020-12-04 07:43:02](https://github.com/leanprover-community/mathlib/commit/7e307bc)
chore(algebra/ring): delete a duplicate instance ([#5215](https://github.com/leanprover-community/mathlib/pull/5215))
In [#3303](https://github.com/leanprover-community/mathlib/pull/3303) and [#3296](https://github.com/leanprover-community/mathlib/pull/3296) which were merged 1 day apart two versions of the instance comm_monoid_with_zero from a comm_semiring were added 5 lines apart in the file, delete one.

### [2020-12-04 07:43:00](https://github.com/leanprover-community/mathlib/commit/2d00ba4)
feat(category_theory/limits): cleanup equalizers ([#5214](https://github.com/leanprover-community/mathlib/pull/5214))
golf and make simp more powerful

### [2020-12-04 07:42:59](https://github.com/leanprover-community/mathlib/commit/b2f8c4c)
feat(category_theory/limits): reflects limit if reflects iso and preserves ([#5213](https://github.com/leanprover-community/mathlib/pull/5213))

### [2020-12-04 07:42:57](https://github.com/leanprover-community/mathlib/commit/cfd01f9)
chore(topology/continuous_on): change type of `continuous_on.comp_continuous` ([#5209](https://github.com/leanprover-community/mathlib/pull/5209))
Use `∀ x, f x ∈ s` instead of `range f ⊆ s`.

### [2020-12-04 07:42:55](https://github.com/leanprover-community/mathlib/commit/ad25cac)
refactor(data/polynomial/derivative): change `polynomial.derivative` to be a `linear_map` ([#5198](https://github.com/leanprover-community/mathlib/pull/5198))
Refactors polynomial.derivative to be a linear_map by default

### [2020-12-04 07:42:52](https://github.com/leanprover-community/mathlib/commit/240f6eb)
feat(category_theory/monad): cleanups in monad algebra ([#5193](https://github.com/leanprover-community/mathlib/pull/5193))
- Converts the simp normal form for composition of algebra homs to use category notation. 
- Adds simps where appropriate
- Golfs proofs, remove some erw and nonterminal simps
- Remove some redundant brackets

### [2020-12-04 07:42:50](https://github.com/leanprover-community/mathlib/commit/c10d1b1)
feat(ring_theory/polynomial/cyclotomic):  add  order_of_root_cyclotomic ([#5151](https://github.com/leanprover-community/mathlib/pull/5151))
Two lemmas about roots of cyclotomic polynomials modulo `p`.
`order_of_root_cyclotomic` is the main algebraic tool to prove the existence of infinitely many primes congruent to `1` modulo `n`.

### [2020-12-04 07:42:48](https://github.com/leanprover-community/mathlib/commit/c939c9e)
feat(category_theory/limits/preserves): preserving terminal objects ([#5060](https://github.com/leanprover-community/mathlib/pull/5060))
Another part of [#4716](https://github.com/leanprover-community/mathlib/pull/4716).

### [2020-12-04 06:35:18](https://github.com/leanprover-community/mathlib/commit/4f5046d)
feat(ring_theory/polynomial/cyclotomic): Möbius inversion formula for cyclotomic polynomials ([#5192](https://github.com/leanprover-community/mathlib/pull/5192))
Proves Möbius inversion for functions to a `comm_group_with_zero`
Proves the Möbius inversion formula for cyclotomic polynomials

### [2020-12-04 01:20:37](https://github.com/leanprover-community/mathlib/commit/57dd302)
chore(scripts): update nolints.txt ([#5211](https://github.com/leanprover-community/mathlib/pull/5211))
I am happy to remove some nolints for you!

### [2020-12-03 22:25:01](https://github.com/leanprover-community/mathlib/commit/20cc59d)
feat(algebra/lie/basic): define missing inclusion maps ([#5207](https://github.com/leanprover-community/mathlib/pull/5207))

### [2020-12-03 22:24:59](https://github.com/leanprover-community/mathlib/commit/ec839ef)
feat(topology/algebra/order): continuity of monotone functions ([#5199](https://github.com/leanprover-community/mathlib/pull/5199))
Add local versions of `order_iso.continuous`.

### [2020-12-03 19:30:25](https://github.com/leanprover-community/mathlib/commit/3894503)
doc(tactic/library_search): use more detailed doc string in docs ([#5206](https://github.com/leanprover-community/mathlib/pull/5206))
The doc string for `tactic.interactive.library_search` is better than the tactic doc entry.
The latter is missing details like `library_search!`

### [2020-12-03 19:30:23](https://github.com/leanprover-community/mathlib/commit/d416ad6)
feat(topology/category/Profinite): add category of profinite top. spaces ([#5147](https://github.com/leanprover-community/mathlib/pull/5147))

### [2020-12-03 19:30:20](https://github.com/leanprover-community/mathlib/commit/6f38a50)
feat(field_theory/minimal_polynomial): add algebra_map_inj ([#5062](https://github.com/leanprover-community/mathlib/pull/5062))
I have added `algebra_map_inj` that computes the minimal polynomial of an element of the base ring. It generalizes `algebra_map` that assumes the base ring to be a field. I left `algebra_map` since I think it is reasonable to have a lemma that works without proving explicitly that the algebra map is injective.

### [2020-12-03 16:31:34](https://github.com/leanprover-community/mathlib/commit/986cabf)
fix(linear_algebra/multilinear): Fix incorrect type constraints on `dom_dom_congr` ([#5203](https://github.com/leanprover-community/mathlib/pull/5203))
In the last PR, I accidentally put this in a section with `[comm_semiring R]`, but this only actually requires `[semiring R]`

### [2020-12-03 16:31:32](https://github.com/leanprover-community/mathlib/commit/5269717)
chore(linear_algebra/determinant): Move some lemmas about swaps to better files ([#5201](https://github.com/leanprover-community/mathlib/pull/5201))
These lemmas are not specific to determinants, and I need them in another file imported by `determinant`.

### [2020-12-03 16:31:30](https://github.com/leanprover-community/mathlib/commit/8ff9c0e)
feat(group_theory/order_of_element): add is_cyclic_of_prime_card ([#5172](https://github.com/leanprover-community/mathlib/pull/5172))
Add `is_cyclic_of_prime_card`, which says if a group has prime order, then it is cyclic. I also added `eq_top_of_card_eq` which says a subgroup is `top` when it has the same size as the group, not sure where that should be in the file.

### [2020-12-03 14:04:40](https://github.com/leanprover-community/mathlib/commit/f1b387f)
feat(algebra/module/basic): Add smul_comm_class instances ([#5205](https://github.com/leanprover-community/mathlib/pull/5205))

### [2020-12-03 14:04:38](https://github.com/leanprover-community/mathlib/commit/a4b6c41)
feat(field_theory/separable): is_separable_of_alg_hom_is_separable ([#5175](https://github.com/leanprover-community/mathlib/pull/5175))
Proves that is_separable pulls back along an alg_hom

### [2020-12-03 14:04:36](https://github.com/leanprover-community/mathlib/commit/b978f36)
refactor(field_theory/fixed): Generalize alg_hom lemmas ([#5174](https://github.com/leanprover-community/mathlib/pull/5174))
This PR generalizes some alg_hom lemmas to not require equality of the domain and codomain.

### [2020-12-03 14:04:33](https://github.com/leanprover-community/mathlib/commit/e7c2bba)
feat(ring_theory/witt_vector/frobenius): the frobenius endomorphism of witt vectors ([#4838](https://github.com/leanprover-community/mathlib/pull/4838))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-03 12:03:20](https://github.com/leanprover-community/mathlib/commit/f1531ea)
feat(ring_theory/witt_vector): witt_sub, a demonstration of is_poly techniques ([#5165](https://github.com/leanprover-community/mathlib/pull/5165))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>

### [2020-12-03 12:03:18](https://github.com/leanprover-community/mathlib/commit/f6273d4)
feat(group_theory/group_action/sub_mul_action): Add an object for bundled sets closed under a mul action ([#4996](https://github.com/leanprover-community/mathlib/pull/4996))
This adds `sub_mul_action` as a base class for `submodule`, and copies across the relevant lemmas.
This also weakens the type class requires for `A →[R] B`, to allow it to be used when only `has_scalar` is available.

### [2020-12-03 10:55:59](https://github.com/leanprover-community/mathlib/commit/98a20c2)
feat(combinatorics/simple_graph/matching): introduce matchings and perfect matchings of graphs ([#5156](https://github.com/leanprover-community/mathlib/pull/5156))
Introduce definitions of matchings and perfect matchings of graphs. This is with the goal of eventually proving Hall's Marriage Theorem and Tutte's Theorem.

### [2020-12-03 02:41:41](https://github.com/leanprover-community/mathlib/commit/61e76c4)
chore(scripts): update nolints.txt ([#5197](https://github.com/leanprover-community/mathlib/pull/5197))
I am happy to remove some nolints for you!

### [2020-12-03 01:03:53](https://github.com/leanprover-community/mathlib/commit/d9a7d05)
chore(topology/algebra/ordered): add `order_iso.to_homeomorph` ([#5111](https://github.com/leanprover-community/mathlib/pull/5111))
* Replace `homeomorph_of_strict_mono_surjective` with `order_iso.to_homeomorph` and `order_iso.continuous`.
* Drop `continuous_at_of_strict_mono_surjective` in favor of `order_iso.to_homeomorph`.
* Use notation for `nhds_within` here and there.

### [2020-12-02 21:22:19](https://github.com/leanprover-community/mathlib/commit/3f61e54)
feat(category_theory/monad): mark monad lemmas as reassoc ([#5190](https://github.com/leanprover-community/mathlib/pull/5190))

### [2020-12-02 21:22:16](https://github.com/leanprover-community/mathlib/commit/a84d7a7)
feat(category_theory/adjunction): adjunction to equivalence ([#5189](https://github.com/leanprover-community/mathlib/pull/5189))
Raise an adjunction to an equivalence

### [2020-12-02 21:22:13](https://github.com/leanprover-community/mathlib/commit/ed6eab0)
feat(category_theory/adjunction): simp adjunction defs ([#5188](https://github.com/leanprover-community/mathlib/pull/5188))
Mark adjunction defs as `simps` and use the new lemmas to simplify some proofs

### [2020-12-02 21:22:11](https://github.com/leanprover-community/mathlib/commit/9be829e)
feat(order/bounds): add basic lemmas about bdd_below ([#5186](https://github.com/leanprover-community/mathlib/pull/5186))
Lemmas for bounded intervals (`Icc`, `Ico`, `Ioc` and `Ioo`). There were lemmas for `bdd_above` but the ones for `bdd_below` were missing.

### [2020-12-02 21:22:09](https://github.com/leanprover-community/mathlib/commit/e5befed)
chore(data/polynomial/degree): golf some proofs, add simple lemmas ([#5185](https://github.com/leanprover-community/mathlib/pull/5185))
* drop `polynomial.nat_degree_C_mul_X_pow_of_nonzero`; was a duplicate
  of `polynomial.nat_degree_C_mul_X_pow`;
* golf the proof of `nat_degree_C_mul_X_pow_le`;
* add more `simp` lemmas.

### [2020-12-02 21:22:07](https://github.com/leanprover-community/mathlib/commit/64fd9f8)
feat(order/rel_iso): preimages of intervals under an `order_iso` ([#5183](https://github.com/leanprover-community/mathlib/pull/5183))

### [2020-12-02 21:22:05](https://github.com/leanprover-community/mathlib/commit/725fb8b)
feat(algebra/lie/basic): define `map` and `comap` for Lie ideals, submodules ([#5181](https://github.com/leanprover-community/mathlib/pull/5181))

### [2020-12-02 21:22:03](https://github.com/leanprover-community/mathlib/commit/5e93545)
feat(linear_algebra/multilinear): Generalize dom_dom_congr for equivalences between types ([#5180](https://github.com/leanprover-community/mathlib/pull/5180))
This also bundles the operation into an equivalence.

### [2020-12-02 21:22:01](https://github.com/leanprover-community/mathlib/commit/8da5f23)
feat(data/set/function): Extend `update_comp` lemmas to work on dependent functions ([#5178](https://github.com/leanprover-community/mathlib/pull/5178))
Also extends them to `Sort`

### [2020-12-02 21:21:58](https://github.com/leanprover-community/mathlib/commit/2189c7a)
feat(data/option/basic): map_map functor-like lemmas ([#5030](https://github.com/leanprover-community/mathlib/pull/5030))
New lemmas:
`map_eq_map`
`map_map`
`comp_map`
`map_comp_map`

### [2020-12-02 19:13:28](https://github.com/leanprover-community/mathlib/commit/0bb8809)
feat(category_theory/limits): left adjoint if preserves colimits ([#4942](https://github.com/leanprover-community/mathlib/pull/4942))
A slight generalisation of a construction from before. Maybe this is the dual version you were talking about @jcommelin - if so my mistake! I think the advantage of doing it this way is that you definitionally get the old version but also the new version too.

### [2020-12-02 17:38:03](https://github.com/leanprover-community/mathlib/commit/e5ea200)
chore(analysis/normed_space): golf 2 proofs ([#5184](https://github.com/leanprover-community/mathlib/pull/5184))

### [2020-12-02 15:07:43](https://github.com/leanprover-community/mathlib/commit/a8ddd7b)
feat(algebra/module/basic): generalize `is_scalar_tower` instances ([#5135](https://github.com/leanprover-community/mathlib/pull/5135))

### [2020-12-02 13:32:27](https://github.com/leanprover-community/mathlib/commit/d6241cb)
feat(linear_algebra/*): Use alternating maps for wedge and determinant ([#5124](https://github.com/leanprover-community/mathlib/pull/5124))
This :
* Adds `exterior_algebra.ι_multi`, where `ι_multi ![a, b ,c]` = `ι a * ι b * ι c`
* Makes `det_row_multilinear` an `alternating_map`
* Makes `is_basis.det` an `alternating_map`

### [2020-12-02 07:25:31](https://github.com/leanprover-community/mathlib/commit/61f6364)
feat(number_theory/arithmetic_function): Möbius inversion for `add_comm_group`s, `comm_group`s ([#5115](https://github.com/leanprover-community/mathlib/pull/5115))
Adds scalar multiplication for `arithmetic_function`s
Generalizes Möbius inversion to work with `(add_)comm_group`s

### [2020-12-02 02:00:39](https://github.com/leanprover-community/mathlib/commit/f7e1806)
chore(scripts): update nolints.txt ([#5176](https://github.com/leanprover-community/mathlib/pull/5176))
I am happy to remove some nolints for you!

### [2020-12-01 23:23:57](https://github.com/leanprover-community/mathlib/commit/c2c7afe)
feat(data/nat/sqrt): add simple inequality lemmas and "no middle square" ([#5155](https://github.com/leanprover-community/mathlib/pull/5155))
The first two theorems are useful when one needs the biggest perfect square strictly less than a number, whereas `no_middle_square` can be used to easily prove that a given number is not a square.

### [2020-12-01 23:23:54](https://github.com/leanprover-community/mathlib/commit/9a4ed2a)
refactor(*): Add `_injective` alongside `_inj` lemmas ([#5150](https://github.com/leanprover-community/mathlib/pull/5150))
This adds four new `injective` lemmas:
* `list.append_right_injective`
* `list.append_left_injective`
* `sub_right_injective`
* `sub_left_injective`
It also replaces as many `*_inj` lemmas as possible with an implementation of `*_injective.eq_iff`, to make it clear that the lemmas are just aliases of each other.

### [2020-12-01 23:23:52](https://github.com/leanprover-community/mathlib/commit/c2b7d23)
chore(category_theory/limits): separate regular and normal monos ([#5149](https://github.com/leanprover-community/mathlib/pull/5149))
This separates the file `regular_mono` into `regular_mono` and `normal_mono`: mostly this simplifies the import graph, but also this has the advantage that to use things about kernel pairs it's no longer necessary to import things about zero objects (I kept changing equalizers and using the changes in a file about monads which imported kernel pairs, and it was very slow because of zero objects)

### [2020-12-01 20:05:02](https://github.com/leanprover-community/mathlib/commit/6c456e3)
feat(linear_algebra/multilinear): Add dom_dom_congr ([#5136](https://github.com/leanprover-community/mathlib/pull/5136))

### [2020-12-01 20:05:00](https://github.com/leanprover-community/mathlib/commit/41e0903)
feat(category_theory/limits/preserves): preserving equalizers ([#5044](https://github.com/leanprover-community/mathlib/pull/5044))
Constructions and lemmas about preserving equalizers

### [2020-12-01 16:14:24](https://github.com/leanprover-community/mathlib/commit/2a68477)
chore(algebra/group/basic): Add eq_one_iff_eq_one_of_mul_eq_one ([#5169](https://github.com/leanprover-community/mathlib/pull/5169))

### [2020-12-01 16:14:22](https://github.com/leanprover-community/mathlib/commit/24596ca)
feat(tactic/ring_exp): handle `nat.succ p` as `p + 1` ([#5166](https://github.com/leanprover-community/mathlib/pull/5166))
Fixes: [#5157](https://github.com/leanprover-community/mathlib/pull/5157) 
This PR adds a `rewrite` operation to `ring_exp`, which takes a normalized `p' : ex sum` and a proof that `p = p'.orig`, and shows `p` also normalizes to `p'.pretty`. The only use currently is `nat.succ`. If we still had `nat.has_pow`, the same function could have handled rewriting from `nat.has_pow` to `monoid.has_pow`.

### [2020-12-01 16:14:20](https://github.com/leanprover-community/mathlib/commit/9e78823)
feat(ring_theory/perfection): perfection and tilt ([#5032](https://github.com/leanprover-community/mathlib/pull/5032))
- [x] depends on: [#5132](https://github.com/leanprover-community/mathlib/pull/5132)

### [2020-12-01 13:25:41](https://github.com/leanprover-community/mathlib/commit/b7649bc)
doc(linear_algebra/determinant): Add a reference to is_basis.det ([#5167](https://github.com/leanprover-community/mathlib/pull/5167))

### [2020-12-01 13:25:39](https://github.com/leanprover-community/mathlib/commit/c088f65)
chore(data/equiv/perm): Move around lemmas about perm and swap ([#5153](https://github.com/leanprover-community/mathlib/pull/5153))
Only a very small fraction of `data/equiv/basic` needs knowledge of groups, moving out `perm_group` lets us cut the dependency.
The new `perm_group` file is then a good place for some of the lemmas in `group_theory/perm/sign`, especially those which just restate `equiv` lemmas in terms of `*` and `⁻¹` instead of `.trans` and `.symm`.
This moves a few lemmas about swap out of the `equiv.perm` namespace and into `equiv`, since `equiv.swap` is also in that namespace.

### [2020-12-01 13:25:37](https://github.com/leanprover-community/mathlib/commit/7188eae)
feat(linear_algebra): Add alternating multilinear maps ([#5102](https://github.com/leanprover-community/mathlib/pull/5102))

### [2020-12-01 10:59:06](https://github.com/leanprover-community/mathlib/commit/ca3351f)
feat(rat/{basic,floor}) add floor lemmas ([#5148](https://github.com/leanprover-community/mathlib/pull/5148))

### [2020-12-01 08:49:42](https://github.com/leanprover-community/mathlib/commit/2b074be)
feat(algebra/lie/basic): Define lattice structure for `lie_submodule`s ([#5146](https://github.com/leanprover-community/mathlib/pull/5146))

### [2020-12-01 05:46:04](https://github.com/leanprover-community/mathlib/commit/a883152)
doc(data/mv_polynomial/basic): Fix documentation of mv_polynomial.monomial ([#5160](https://github.com/leanprover-community/mathlib/pull/5160))
The documenting comment for this function was obviously lifted from the single variable polynomial version, and did not make sense.
I'm not sure if this is the right comment, but it is at least better to what it was before.

### [2020-12-01 01:20:08](https://github.com/leanprover-community/mathlib/commit/b846aa5)
chore(scripts): update nolints.txt ([#5158](https://github.com/leanprover-community/mathlib/pull/5158))
I am happy to remove some nolints for you!