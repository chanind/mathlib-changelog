### [2021-06-30 21:21:07](https://github.com/leanprover-community/mathlib/commit/0faf086)
feat(data/int/cast): cast_nat_abs ([#8120](https://github.com/leanprover-community/mathlib/pull/8120))

### [2021-06-30 21:21:06](https://github.com/leanprover-community/mathlib/commit/ad00a02)
feat(topology/vector_bundle): `topological_vector_bundle_core` ([#8089](https://github.com/leanprover-community/mathlib/pull/8089))
Analogous construction to `topological_fiber_bundle_core`. This construction gives a way to construct vector bundles from a structure registering how trivialization changes act on fibers.

### [2021-06-30 20:39:41](https://github.com/leanprover-community/mathlib/commit/e70093f)
feat(algebra/free_non_unital_non_assoc_algebra): construction of the free non-unital, non-associative algebra on a type `X` with coefficients in a semiring `R` ([#8141](https://github.com/leanprover-community/mathlib/pull/8141))

### [2021-06-30 18:53:30](https://github.com/leanprover-community/mathlib/commit/e713106)
docs(data/string/*): add module docstrings ([#8144](https://github.com/leanprover-community/mathlib/pull/8144))

### [2021-06-30 18:53:29](https://github.com/leanprover-community/mathlib/commit/8ee2967)
feat(algebra/big_operators/basic): nat_abs_sum_le ([#8132](https://github.com/leanprover-community/mathlib/pull/8132))

### [2021-06-30 18:03:21](https://github.com/leanprover-community/mathlib/commit/3a5851f)
feat(data/complex/module): add complex.lift to match zsqrtd.lift ([#8107](https://github.com/leanprover-community/mathlib/pull/8107))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/The.20unique.20.60.E2.84.82.20.E2.86.92.E2.82.90.5B.E2.84.9D.5D.20A.60.20given.20a.20square.20root.20of.20-1/near/244135262)

### [2021-06-30 16:49:13](https://github.com/leanprover-community/mathlib/commit/36c90d5)
fix(algebra/algebra/subalgebra): fix incorrect namespaces and remove duplicate instance ([#8140](https://github.com/leanprover-community/mathlib/pull/8140))
We already had a `subsingleton` instance on `alg_hom`s added in [#5672](https://github.com/leanprover-community/mathlib/pull/5672), but we didn't find it [#8110](https://github.com/leanprover-community/mathlib/pull/8110) because
* gh-6025 means we can't ask `apply_instance` to find it
* it had an incorrect name in the wrong namespace
Code opting into this instance will need to change from
```lean
local attribute [instance] alg_hom.subsingleton
```
to
```lean
local attribute [instance] alg_hom.subsingleton subalgebra.subsingleton_of_subsingleton
```

### [2021-06-30 16:49:12](https://github.com/leanprover-community/mathlib/commit/d420db5)
chore(algebra/algebra): trivial lemmas for alg_equiv ([#8139](https://github.com/leanprover-community/mathlib/pull/8139))

### [2021-06-30 13:51:06](https://github.com/leanprover-community/mathlib/commit/9c03c03)
feat(data/set/basic): range_pair_subset ([#8133](https://github.com/leanprover-community/mathlib/pull/8133))
From LTE.

### [2021-06-30 12:06:40](https://github.com/leanprover-community/mathlib/commit/1de192f)
feat(algebra/ordered_ring): abs_cases lemma ([#8124](https://github.com/leanprover-community/mathlib/pull/8124))
This lemma makes the following type of argument work seamlessly:
```lean
example (h : x<-1/2) : |x + 1| < |x| := by cases abs_cases (x + 1); cases abs_cases x; linarith
```

### [2021-06-30 11:26:31](https://github.com/leanprover-community/mathlib/commit/db05900)
feat(linear_algebra/clifford_algebra): two algebras are isomorphic if their quadratic forms are equivalent ([#8128](https://github.com/leanprover-community/mathlib/pull/8128))

### [2021-06-30 08:51:20](https://github.com/leanprover-community/mathlib/commit/9a8dcb9)
docs(data/dlist/basic): add module docstring ([#8079](https://github.com/leanprover-community/mathlib/pull/8079))

### [2021-06-30 04:28:24](https://github.com/leanprover-community/mathlib/commit/eeeb223)
feat(data/int/basic): int.nat_abs_sub_le ([#8118](https://github.com/leanprover-community/mathlib/pull/8118))

### [2021-06-30 04:28:23](https://github.com/leanprover-community/mathlib/commit/af8a38f)
feat(algebra/{covariant_and_contravariant + ordered_monoid): add instance, golf, docs ([#8067](https://github.com/leanprover-community/mathlib/pull/8067))
Introduce a missing instance for `comm_semigroup`s.
Also, golf a couple of proofs and add a relevant, explicit PR to a comment.

### [2021-06-30 03:13:34](https://github.com/leanprover-community/mathlib/commit/3ee436d)
docs(data/char): add module docstring ([#8043](https://github.com/leanprover-community/mathlib/pull/8043))

### [2021-06-30 02:07:35](https://github.com/leanprover-community/mathlib/commit/8cacd99)
chore(scripts): update nolints.txt ([#8131](https://github.com/leanprover-community/mathlib/pull/8131))
I am happy to remove some nolints for you!

### [2021-06-29 23:21:40](https://github.com/leanprover-community/mathlib/commit/917bcd4)
doc(topology/separation): module + lemma docs ([#8091](https://github.com/leanprover-community/mathlib/pull/8091))

### [2021-06-29 23:21:39](https://github.com/leanprover-community/mathlib/commit/2600baf)
docs(data/list/sections): add module docstring ([#8033](https://github.com/leanprover-community/mathlib/pull/8033))

### [2021-06-29 21:36:27](https://github.com/leanprover-community/mathlib/commit/2c749b1)
feat(algebra/to_additive): do not additivize operations on constant types ([#7792](https://github.com/leanprover-community/mathlib/pull/7792))
* Fixes [#4210](https://github.com/leanprover-community/mathlib/pull/4210)
* Adds a heuristic to `@[to_additive]` that decides which multiplicative identifiers to replace with their additive counterparts. 
* See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/to_additive.20and.20fixed.20types) thread or documentation for the precise heuristic.
* We tag some types with `@[to_additive]`, so that they are handled correctly by the heurstic. These types `pempty`, `empty`, `unit` and `punit`.
* We make the following change to enable to above bullet point: you are allowed to translate a declaration to itself, only if you write its name again as argument of the attribute (if you don't specify an argument we want to raise an error, since that likely is a mistake).
* Because of this heuristic, all declarations with the `@[to_additive]` attribute should have a type with a multiplicative structure on it as its first argument. The first argument should not be an arbitrary indexing type. This means that in `finset.prod` and `finprod` we reorder the first two (implicit) arguments, so that the first argument is the codomain of the function.
* This will eliminate many (but not all) type mismatches generated by `@[to_additive]`.
* This heuristic doesn't catch all cases: for example, the declaration could have two type arguments with multiplicative structure, and the second one is `ℕ`, but the first one is a variable.

### [2021-06-29 20:21:49](https://github.com/leanprover-community/mathlib/commit/e6ec901)
feat(ring_theory/power_basis): extensionality for algebra homs ([#8110](https://github.com/leanprover-community/mathlib/pull/8110))
This PR shows two `alg_hom`s out of an algebra with a power basis are equal if the generator has the same image for both maps. It uses this result to bundle `power_basis.lift` into an equiv.

### [2021-06-29 19:37:54](https://github.com/leanprover-community/mathlib/commit/505c32f)
feat(analysis/normed_space/inner_product): the orthogonal projection is self adjoint ([#8116](https://github.com/leanprover-community/mathlib/pull/8116))

### [2021-06-29 17:54:59](https://github.com/leanprover-community/mathlib/commit/5ecd078)
feat(data/ordmap/ordset): Implement some more `ordset` functions ([#8127](https://github.com/leanprover-community/mathlib/pull/8127))
Implement (with proofs) `erase`, `map`, and `mem` for `ordset` in `src/data/ordmap` along with a few useful related proofs.

### [2021-06-29 17:54:58](https://github.com/leanprover-community/mathlib/commit/d558350)
feat(algebra/ordered_group): add a few instances, prune unneeded code ([#8075](https://github.com/leanprover-community/mathlib/pull/8075))
This PR aims at shortening the subsequent `order` refactor.
The removed lemmas can now by proven as follows:
```lean
@[to_additive ordered_add_comm_group.add_lt_add_left]
lemma ordered_comm_group.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
mul_lt_mul_left' h c
@[to_additive ordered_add_comm_group.le_of_add_le_add_left]
lemma ordered_comm_group.le_of_mul_le_mul_left (h : a * b ≤ a * c) : b ≤ c :=
le_of_mul_le_mul_left' h
@[to_additive]
lemma ordered_comm_group.lt_of_mul_lt_mul_left (h : a * b < a * c) : b < c :=
lt_of_mul_lt_mul_left' h
```
They were only used in this file and I replaced their appearances by the available proofs.

### [2021-06-29 17:54:57](https://github.com/leanprover-community/mathlib/commit/bdf2d81)
feat(topology/continuous_function/stone_weierstrass): complex Stone-Weierstrass ([#8012](https://github.com/leanprover-community/mathlib/pull/8012))

### [2021-06-29 16:11:34](https://github.com/leanprover-community/mathlib/commit/4cdfbd2)
feat(data/setoid/partition): indexed partition ([#7910](https://github.com/leanprover-community/mathlib/pull/7910))
from LTE
Note that data/setoid/partition.lean, which already existed before this
PR, is currently not imported anywhere in mathlib. But it is used in LTE
and will be used in the next PR, in relation to locally constant
functions.

### [2021-06-29 14:28:25](https://github.com/leanprover-community/mathlib/commit/23ee7ea)
feat(analysis/normed_space/basic): int.norm_eq_abs ([#8117](https://github.com/leanprover-community/mathlib/pull/8117))

### [2021-06-29 14:28:24](https://github.com/leanprover-community/mathlib/commit/d249e53)
feat(algebra/ordered_group): add instances mixing `group` and `co(ntra)variant` ([#8072](https://github.com/leanprover-community/mathlib/pull/8072))
In an attempt to break off small parts of PR [#8060](https://github.com/leanprover-community/mathlib/pull/8060), I extracted some of the instances proven there to this PR.
This is part of the `order` refactor.
~~I tried to get rid of the `@`, but failed.  If you have a trick to avoid them, I would be very happy to learn it!~~  `@`s removed!

### [2021-06-29 14:28:23](https://github.com/leanprover-community/mathlib/commit/70fcf99)
feat(group_theory/free_abelian_group_finsupp): isomorphism between `free_abelian_group` and `finsupp` ([#8046](https://github.com/leanprover-community/mathlib/pull/8046))
From LTE

### [2021-06-29 13:33:01](https://github.com/leanprover-community/mathlib/commit/68d7d00)
chore(analysis/special_functions/pow): versions of tendsto/continuous_at lemmas for (e)nnreal ([#8113](https://github.com/leanprover-community/mathlib/pull/8113))
We have the full suite of lemmas about `tendsto` and `continuous` for real powers of `real`, but apparently not for `nnreal` or `ennreal`.  I have provided a few, rather painfully -- if there is a better way, golfing is welcome!

### [2021-06-29 12:50:05](https://github.com/leanprover-community/mathlib/commit/54eccb0)
feat(measure_theory/lp_space): add snorm_eq_lintegral_rpow_nnnorm ([#8115](https://github.com/leanprover-community/mathlib/pull/8115))
Add two lemmas to go from `snorm` to integrals (through `snorm'`). The idea is that `snorm'` should then generally not be used, except in the construction of `snorm`.

### [2021-06-29 11:29:09](https://github.com/leanprover-community/mathlib/commit/90d2046)
feat(algebra/monoid_algebra): adjointness for the functor `G ↦ monoid_algebra k G` when `G` carries only `has_mul` ([#7932](https://github.com/leanprover-community/mathlib/pull/7932))

### [2021-06-29 10:46:12](https://github.com/leanprover-community/mathlib/commit/d521b2b)
feat(algebraic_topology/simplex_category): epi and monos in the simplex category ([#8101](https://github.com/leanprover-community/mathlib/pull/8101))
Characterize epimorphisms and monomorphisms in `simplex_category` in terms of the function they represent. Add lemmas about their behavior on length of objects.

### [2021-06-29 06:55:39](https://github.com/leanprover-community/mathlib/commit/07f1235)
chore(category_theory/opposites): make hom explicit in lemmas ([#8088](https://github.com/leanprover-community/mathlib/pull/8088))

### [2021-06-28 20:13:06](https://github.com/leanprover-community/mathlib/commit/ac156c1)
chore(algebra/algebra/basic): add algebra.right_comm to match left_comm ([#8109](https://github.com/leanprover-community/mathlib/pull/8109))
This also reorders the arguments to `right_comm` to match the order they appear in the LHS of the lemma.

### [2021-06-28 16:40:09](https://github.com/leanprover-community/mathlib/commit/a79df55)
chore(algebra/ordered_group): remove linear_ordered_comm_group.to_comm_group ([#7861](https://github.com/leanprover-community/mathlib/pull/7861))
This instance shortcut bypassed `ordered_comm_group`, and could easily result in computability problems since many `linear_order` instances are noncomputable due to their embedded decidable instances. This would happen when:
* Lean needs an `add_comm_group A`
* We have:
  * `noncomputable instance : linear_ordered_comm_group A`
  * `instance : ordered_comm_group A`
* Lean tries `linear_ordered_comm_group.to_comm_group` before `ordered_comm_group.to_comm_group`, and hands us back a noncomputable one, even though there is a computable one available.
There're no comments explaining why things were done this way, suggesting it was accidental, or perhaps that `ordered_comm_group` came later.
This broke one proof which somehow `simponly`ed associativity the wrong way, so I just golfed that proof and the one next to it for good measure.

### [2021-06-28 15:38:22](https://github.com/leanprover-community/mathlib/commit/1ffb5be)
feat(data/complex/module): add complex.alg_hom_ext ([#8105](https://github.com/leanprover-community/mathlib/pull/8105))

### [2021-06-28 13:54:02](https://github.com/leanprover-community/mathlib/commit/b160ac8)
chore(topology/topological_fiber_bundle): reorganizing the code ([#7989](https://github.com/leanprover-community/mathlib/pull/7989))
Mainly redesigning the `simp` strategy.

### [2021-06-28 12:36:08](https://github.com/leanprover-community/mathlib/commit/f7c1e5f)
feat(algebra/lie/nilpotent): basic lemmas about nilpotency for Lie subalgebras of associative algebras ([#8090](https://github.com/leanprover-community/mathlib/pull/8090))
The main lemma is: `lie_algebra.is_nilpotent_ad_of_is_nilpotent` which is the first step in proving Engel's theorem.

### [2021-06-28 11:54:29](https://github.com/leanprover-community/mathlib/commit/81183ea)
feat(geometry/manifold): `derivation_bundle` ([#7708](https://github.com/leanprover-community/mathlib/pull/7708))
In this PR we define the `derivation_bundle`. Note that this definition is purely algebraic and that the whole geometry/analysis is contained in the algebra structure of smooth global functions on the manifold.
I believe everything runs smoothly and elegantly and that most proofs can be naturally done by `rfl`. To anticipate some discussions that already arose on Zulip about 9 months ago, note that the content of these files is purely algebraic and that there is no intention whatsoever to replace the current tangent bundle. I prefer this definition to the one given through the adjoint representation, because algebra is more easily formalized and simp can solve most proofs with this definition. However, in the future, there will be also the adjoint representation for sure.

### [2021-06-28 10:36:19](https://github.com/leanprover-community/mathlib/commit/bfd0685)
fix(algebra/module/linear_map): do not introduce `show` ([#8102](https://github.com/leanprover-community/mathlib/pull/8102))
Without this change, `apply linear_map.coe_injective` on a goal of `f = g` introduces some unpleasant `show` terms, giving a goal of
```lean
(λ (f : M →ₗ[R] M₂), show M → M₂, from ⇑f) f = (λ (f : M →ₗ[R] M₂), show M → M₂, from ⇑f) g
```
which is then frustrating to `rw` at, instead of
```lean
⇑f = ⇑g
```

### [2021-06-28 08:51:27](https://github.com/leanprover-community/mathlib/commit/3cb247c)
chore(algebra/ordered_monoid_lemmas): change additive name `left.add_nonneg` to `right.add_nonneg` ([#8065](https://github.com/leanprover-community/mathlib/pull/8065))
A copy-paste error in the name of a lemma that has not been used yet.
Change `pos_add` to `add_pos`.
I also added some paragraph breaks in the documentation.
Co-authored by Eric Wieser.

### [2021-06-28 06:13:33](https://github.com/leanprover-community/mathlib/commit/80d0234)
fix(algebra/group_power): put opposite lemmas in the right namespace ([#8100](https://github.com/leanprover-community/mathlib/pull/8100))

### [2021-06-28 04:53:22](https://github.com/leanprover-community/mathlib/commit/7b253dd)
feat(group_theory/subgroup): lemmas for normal subgroups of subgroups ([#7271](https://github.com/leanprover-community/mathlib/pull/7271))

### [2021-06-27 15:45:05](https://github.com/leanprover-community/mathlib/commit/f8e9c17)
feat(data/nat/factorial): descending factorial ([#7759](https://github.com/leanprover-community/mathlib/pull/7759))
- rename `desc_fac` to `asc_factorial`
- define `desc_factorial`
- update `data.fintype.card_embedding` to use `desc_factorial`

### [2021-06-27 13:01:13](https://github.com/leanprover-community/mathlib/commit/2dcc307)
feat(category_theory/limits): morphism to terminal is split mono ([#8084](https://github.com/leanprover-community/mathlib/pull/8084))
A generalisation of existing results: we already have an instance `split_mono` to `mono` so this is strictly more general.

### [2021-06-27 02:15:39](https://github.com/leanprover-community/mathlib/commit/c5d17ae)
chore(scripts): update nolints.txt ([#8093](https://github.com/leanprover-community/mathlib/pull/8093))
I am happy to remove some nolints for you!

### [2021-06-26 22:33:31](https://github.com/leanprover-community/mathlib/commit/c7a35b4)
doc(topology/homeomorph): fixup glaring error ([#8092](https://github.com/leanprover-community/mathlib/pull/8092))
thanks to @kbuzzard for spotting this error in [#8086](https://github.com/leanprover-community/mathlib/pull/8086)

### [2021-06-26 20:35:05](https://github.com/leanprover-community/mathlib/commit/0817020)
doc(topology/homeomorph): module docs ([#8086](https://github.com/leanprover-community/mathlib/pull/8086))
I really wanted to write more, but there's really not much to say about something that is a stronger bijection :b

### [2021-06-26 18:57:08](https://github.com/leanprover-community/mathlib/commit/b874abc)
feat(field_theory): state primitive element theorem using `power_basis` ([#8073](https://github.com/leanprover-community/mathlib/pull/8073))
This PR adds an alternative formulation to the primitive element theorem: the original formulation was `∃ α : E, F⟮α⟯ = (⊤ : intermediate_field F E)`, which means a lot of pushing things across the equality/equiv from `F⟮α⟯` to `E` itself. I claim that working with a field `E` that has a power basis over `F` is nicer since you don't need to do a lot of transporting.

### [2021-06-26 18:15:06](https://github.com/leanprover-community/mathlib/commit/598722a)
feat(algebraic_topology/simplicial_object): Add augment construction ([#8085](https://github.com/leanprover-community/mathlib/pull/8085))
Adds the augmentation construction for (co)simplicial objects.
From LTE.

### [2021-06-26 09:25:11](https://github.com/leanprover-community/mathlib/commit/4630067)
chore(data/set/intervals): syntax clean up ([#8087](https://github.com/leanprover-community/mathlib/pull/8087))

### [2021-06-25 21:10:33](https://github.com/leanprover-community/mathlib/commit/68ec06c)
chore(analysis/analytic/composition): remove one `have` ([#8083](https://github.com/leanprover-community/mathlib/pull/8083))
A `have` in a proof is not necessary.

### [2021-06-25 20:31:41](https://github.com/leanprover-community/mathlib/commit/92a7171)
feat(measure_theory/interval_integral): generalize `add_adjacent_intervals` to n-ary sum ([#8050](https://github.com/leanprover-community/mathlib/pull/8050))

### [2021-06-25 18:48:54](https://github.com/leanprover-community/mathlib/commit/6666ba2)
fix(real/sign): make `real.sign 0 = 0` to match `int.sign 0` ([#8080](https://github.com/leanprover-community/mathlib/pull/8080))
Previously `sign 0 = 1` which is quite an unusual definition. This definition brings things in line with `int.sign`, and include a proof of this fact.
A future refactor could probably introduce a sign for all rings with a partial order

### [2021-06-25 18:48:53](https://github.com/leanprover-community/mathlib/commit/a7faaf5)
docs(data/list/chain): add module docstring ([#8041](https://github.com/leanprover-community/mathlib/pull/8041))

### [2021-06-25 18:48:52](https://github.com/leanprover-community/mathlib/commit/cf4a2df)
docs(data/list/range): add module docstring ([#8026](https://github.com/leanprover-community/mathlib/pull/8026))

### [2021-06-25 17:09:01](https://github.com/leanprover-community/mathlib/commit/9cc44ba)
feat(ring_theory/nilpotent): basic results about nilpotency in associative rings ([#8055](https://github.com/leanprover-community/mathlib/pull/8055))

### [2021-06-25 10:35:36](https://github.com/leanprover-community/mathlib/commit/1774cf9)
chore(data/complex/{module, is_R_or_C}, analysis/complex/basic): rationalize the structure provided for `conj` and `of_real` ([#8014](https://github.com/leanprover-community/mathlib/pull/8014))
We have many bundled versions of the four operations associated with the complex-real interaction (real & imaginary parts, real-to-complex coercion `of_real`, complex conjugation `conj`).
This PR adjusts the versions provided, according to the following principles:
- `conj` is always an equivalence, there is never a need for the map version
- Both `of_real` and `conj` are `ℝ`-algebra homomorphisms, and since this in typical applications requires no more imports than `ℝ`-linear maps, they can entirely supersede the `ℝ`-linear map versions.
- Name according to the base map name together with an acronym for the bundled map type, for example `conj_ae` for `conj` as an algebra-equivalence (this principle had been largely, but not entirely, followed previously).
The following specific changes result:
- `quaternion.conj_alg_equiv` renamed to `quaternion.conj_ae`, likewise for `quaternion_algebra.conj_alg_equiv`
- `complex.conj_li` upgraded from a map to an equivalence
- `complex.conj_clm` (continuous linear map) upgraded to `complex.conj_cle` (continuous linear equivalence)
- `complex.conj_alg_equiv` renamed to `complex.conj_ae`
- `complex.conj_lm` gone, use `complex.conj_ae` instead
- `complex.of_real_lm` (linear map) upgraded to `complex.of_real_am` (algebra homomorphism)
- all the same changes for `is_R_or_C.*` as for `complex.*`
Associated lemmas are also renamed.

### [2021-06-25 09:21:01](https://github.com/leanprover-community/mathlib/commit/c515346)
feat(ring_theory/power_basis): map a power basis through an alg_equiv ([#8039](https://github.com/leanprover-community/mathlib/pull/8039))
If `A` is equivalent to `A'` as an `R`-algebra and `A` has a power basis, then `A'` also has a power basis. Included are the relevant `simp` lemmas.
This needs a bit of tweaking to `basis.map` and `alg_equiv.to_linear_equiv` for getting more useful `simp` lemmas.

### [2021-06-25 07:18:41](https://github.com/leanprover-community/mathlib/commit/10cd252)
docs(overview, undergrad): add Liouville's Theorem on existence of transcendental numbers ([#8068](https://github.com/leanprover-community/mathlib/pull/8068))

### [2021-06-24 21:57:47](https://github.com/leanprover-community/mathlib/commit/2608244)
feat(data/matrix/basic): add lemma minor_map  ([#8074](https://github.com/leanprover-community/mathlib/pull/8074))
Add lemma `minor_map` proving that the operations of taking a minor and applying a map to the coefficients of a matrix commute.

### [2021-06-24 21:15:20](https://github.com/leanprover-community/mathlib/commit/e137523)
chore(algebraic_topology/simplex_category): golf proof ([#8076](https://github.com/leanprover-community/mathlib/pull/8076))
The "special case of the first simplicial identity" is a trivial consequence of the "generic case". This makes me wonder whether the special case should be there at all but I do not know the standard references for this stuff.

### [2021-06-24 19:39:06](https://github.com/leanprover-community/mathlib/commit/e605b21)
feat(linear_algebra/pi): add linear_equiv.Pi_congr_left ([#8070](https://github.com/leanprover-community/mathlib/pull/8070))
This definition was hiding inside the proof for `is_noetherian_pi`

### [2021-06-24 16:50:00](https://github.com/leanprover-community/mathlib/commit/25d8aac)
chore(field_theory): turn `intermediate_field.subalgebra.equiv_of_eq`  into `intermediate_field.equiv_of_eq` ([#8069](https://github.com/leanprover-community/mathlib/pull/8069))
I was looking for `intermediate_field.equiv_of_eq`. There was a definition of `subalgebra.equiv_of_eq` in the `intermediate_field` namespace which is equal to the original `subalgebra.equiv_of_eq` definition. Meanwhile, there was no `intermediate_field.equiv_of_eq`. So I decided to turn the duplicate into what I think was intended. (As a bonus, I added the `simp` lemmas from `subalgebra.equiv_of_eq`.)

### [2021-06-24 15:14:30](https://github.com/leanprover-community/mathlib/commit/db84f2b)
feat(data/polynomial): `aeval_alg_equiv`, like `aeval_alg_hom` ([#8038](https://github.com/leanprover-community/mathlib/pull/8038))
This PR copies `polynomial.aeval_alg_hom` and `aeval_alg_hom_apply` to `aeval_alg_equiv(_apply)`.

### [2021-06-24 15:14:29](https://github.com/leanprover-community/mathlib/commit/2a15520)
chore(data/polynomial): generalize `aeval_eq_sum_range` to `comm_semiring` ([#8037](https://github.com/leanprover-community/mathlib/pull/8037))
This pair of lemmas did not need any `comm_ring` assumptions, so I put them in a new section with weaker typeclass assumptions.

### [2021-06-24 15:14:28](https://github.com/leanprover-community/mathlib/commit/3937c1b)
docs(data/list/pairwise): add module docstring ([#8025](https://github.com/leanprover-community/mathlib/pull/8025))

### [2021-06-24 15:14:27](https://github.com/leanprover-community/mathlib/commit/520e79d)
feat(analysis/convex/exposed): introduce exposed sets ([#7928](https://github.com/leanprover-community/mathlib/pull/7928))
introduce exposed sets

### [2021-06-24 15:14:26](https://github.com/leanprover-community/mathlib/commit/4801fa6)
feat(measure_theory): the Vitali-Caratheodory theorem ([#7766](https://github.com/leanprover-community/mathlib/pull/7766))
This PR proves the Vitali-Carathéodory theorem, asserting that a measurable function can be closely approximated from above by a lower semicontinuous function, and from below by an upper semicontinuous function. 
This is the main ingredient in the proof of the general version of the fundamental theorem of calculus (when `f'` is just integrable, but not continuous).

### [2021-06-24 13:55:29](https://github.com/leanprover-community/mathlib/commit/b9bf921)
chore(linear_algebra): switch to named constructors for linear_map ([#8059](https://github.com/leanprover-community/mathlib/pull/8059))
This makes some ideas I have for future refactors easier, and generally makes things less fragile to changes such as additional fields or reordering of fields.
The extra verbosity is not really significant.
This conversion is not exhaustive, there may be anonymous constructors elsewhere that I've missed.

### [2021-06-24 12:48:16](https://github.com/leanprover-community/mathlib/commit/2a1cabe)
chore(data/polynomial/eval, ring_theory/polynomial_algebra): golfs ([#8058](https://github.com/leanprover-community/mathlib/pull/8058))
This golfs:
* `polynomial.map_nat_cast` to use `ring_hom.map_nat_cast`
* `polynomial.map.is_semiring_hom` to use `ring_hom.is_semiring_hom`
* `poly_equiv_tensor.to_fun` and `poly_equiv_tensor.to_fun_linear_right` out of existence
And adds a new (unused) lemma `polynomial.map_smul`.
All the other changes in `polynomial/eval` are just reorderings of lemmas to allow the golfing.

### [2021-06-24 11:32:46](https://github.com/leanprover-community/mathlib/commit/5352639)
feat(data/matrix/basic.lean) : added map_scalar and linear_map.map_matrix ([#8061](https://github.com/leanprover-community/mathlib/pull/8061))
Added two lemmas (`map_scalar` and `linear_map.map_matrix_apply`) and a definition (`linear_map.map_matrix`) showing that a map between coefficients induces the same type of map between matrices with those coefficients.

### [2021-06-24 09:57:32](https://github.com/leanprover-community/mathlib/commit/5bd649f)
feat(analysis/liouville/liouville_constant): transcendental Liouville numbers exist! ([#8020](https://github.com/leanprover-community/mathlib/pull/8020))
The final (hopefully!) PR in the Liouville series: there are a couple of results and the proof that Liouville numbers are transcendental.

### [2021-06-24 09:57:31](https://github.com/leanprover-community/mathlib/commit/f7f12bc)
feat(data/nat/prime): norm_num plugin for factors ([#8009](https://github.com/leanprover-community/mathlib/pull/8009))
Implements a `norm_num` plugin to evaluate terms like `nat.factors 231 = [3, 7, 11]`.

### [2021-06-24 09:57:30](https://github.com/leanprover-community/mathlib/commit/d9dcf69)
feat(topology/topological_fiber_bundle): a new standard construction for topological fiber bundles ([#7935](https://github.com/leanprover-community/mathlib/pull/7935))
In this PR we implement a new standard construction for topological fiber bundles: namely a structure that permits to define a fiber bundle when trivializations are given as local equivalences but there is not yet a topology on the total space. The total space is hence given a topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations.

### [2021-06-24 08:13:45](https://github.com/leanprover-community/mathlib/commit/2f27046)
refactor(algebra/ordered_monoid): use `covariant + contravariant` typeclasses in `algebra/ordered_monoid` ([#7999](https://github.com/leanprover-community/mathlib/pull/7999))
Another stepping stone toward [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-24 05:12:32](https://github.com/leanprover-community/mathlib/commit/5653516)
feat(data/fin): some lemmas about casts ([#8049](https://github.com/leanprover-community/mathlib/pull/8049))
From [LTE](https://github.com/leanprover-community/lean-liquid/blob/master/src/for_mathlib/fin.lean).

### [2021-06-24 04:33:52](https://github.com/leanprover-community/mathlib/commit/e07a24a)
chore(data/real/hyperreal): remove @ in a proof ([#8063](https://github.com/leanprover-community/mathlib/pull/8063))
Remove @ in a proof.  Besides its clear aesthetic value, this prevents having to touch this file when the number typeclass arguments in the intervening lemmas changes.
See PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) and [#8060](https://github.com/leanprover-community/mathlib/pull/8060).

### [2021-06-23 23:28:11](https://github.com/leanprover-community/mathlib/commit/b9ef710)
chore(linear_algebra): deduplicate `linear_equiv.{Pi_congr_right,pi}` ([#8056](https://github.com/leanprover-community/mathlib/pull/8056))
PRs [#6415](https://github.com/leanprover-community/mathlib/pull/6415) and [#7489](https://github.com/leanprover-community/mathlib/pull/7489) both added the same linear equiv between Pi types. I propose to unify them, using the name of `Pi_congr_right` (more specific, matches `equiv.Pi_congr_right`), the location of `pi` (more specific) and the implementation of `Pi_congr_right` (shorter).

### [2021-06-23 21:01:23](https://github.com/leanprover-community/mathlib/commit/3cf8039)
feat(measure_theory/set_integral): the set integral is continuous ([#7931](https://github.com/leanprover-community/mathlib/pull/7931))
Most of the code is dedicated to building a continuous linear map from Lp to the Lp space corresponding to the restriction of the measure to a set. The set integral is then continuous as composition of the integral and that map.

### [2021-06-23 19:27:20](https://github.com/leanprover-community/mathlib/commit/a31e3c3)
feat(category_theory/arrow/limit): limit cones in arrow categories ([#7457](https://github.com/leanprover-community/mathlib/pull/7457))

### [2021-06-23 17:29:28](https://github.com/leanprover-community/mathlib/commit/204ca5f)
docs(data/fin2): add module docstring ([#8047](https://github.com/leanprover-community/mathlib/pull/8047))

### [2021-06-23 17:29:27](https://github.com/leanprover-community/mathlib/commit/89b8e0b)
docs(data/option/defs): add module and def docstrings ([#8042](https://github.com/leanprover-community/mathlib/pull/8042))

### [2021-06-23 17:29:26](https://github.com/leanprover-community/mathlib/commit/431207a)
docs(data/list/bag_inter): add module docstring ([#8034](https://github.com/leanprover-community/mathlib/pull/8034))

### [2021-06-23 17:29:25](https://github.com/leanprover-community/mathlib/commit/dd5074c)
feat(analysis/normed_space/basic): add has_nnnorm ([#7986](https://github.com/leanprover-community/mathlib/pull/7986))
We create here classes `has_nndist` and `has_nnnorm` that are variants of `has_dist` and `has_norm` taking values in `ℝ≥0`.  Obvious instances are `pseudo_metric_space` and `semi_normed_group`.
These are not used that much in mathlib, but for example `has_nnnorm` is quite convenient for LTE.

### [2021-06-23 15:53:39](https://github.com/leanprover-community/mathlib/commit/a7b5237)
feat(category_theory/arrow): arrow.iso_mk ([#8057](https://github.com/leanprover-community/mathlib/pull/8057))

### [2021-06-23 15:53:38](https://github.com/leanprover-community/mathlib/commit/c841b09)
docs(data/list/tfae): add module docstring ([#8040](https://github.com/leanprover-community/mathlib/pull/8040))

### [2021-06-23 15:53:37](https://github.com/leanprover-community/mathlib/commit/5787d64)
docs(data/list/zip): add module docstring ([#8036](https://github.com/leanprover-community/mathlib/pull/8036))

### [2021-06-23 14:11:52](https://github.com/leanprover-community/mathlib/commit/97529b4)
docs(data/list/forall2): add module docstring ([#8029](https://github.com/leanprover-community/mathlib/pull/8029))

### [2021-06-23 11:50:23](https://github.com/leanprover-community/mathlib/commit/d9eed42)
feat(analysis/liouville/inequalities_and_series): two useful inequalities for Liouville ([#8001](https://github.com/leanprover-community/mathlib/pull/8001))
This PR ~~creates a file with~~ proves two very specific inequalities.  They will be useful for the Liouville PR, showing that transcendental Liouville numbers exist.
After the initial code review, I scattered an initial segment of this PR into mathlib.  What is left might only be useful in the context of proving the transcendence of Liouville's constants.
~~Given the shortness of this file, I may move it into the main `liouville_constant`, after PR [#8020](https://github.com/leanprover-community/mathlib/pull/8020)  is merged.~~

### [2021-06-23 09:25:09](https://github.com/leanprover-community/mathlib/commit/47ed97f)
feat(algebra/ordered_monoid_lemmas + fixes): consistent use of `covariant` and `contravariant` in `ordered_monoid_lemmas` ([#7876](https://github.com/leanprover-community/mathlib/pull/7876))
This PR breaks off a part of PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).  Here, I start using more consistently `covariant_class` and `contravariant_class` in the file `algebra/ordered_monoid_lemmas`.
This PR is simply intended as a stepping stone to merging the bigger one ([#7645](https://github.com/leanprover-community/mathlib/pull/7645)) and receiving "personalized comments on it!
Summary of changes:
--
New lemmas
* `@[to_additive add_nonneg] lemma one_le_mul_right`
* `@[to_additive] lemma le_mul_of_le_of_le_one`
* `@[to_additive] lemma mul_lt_mul_of_lt_of_lt`
* `@[to_additive] lemma left.mul_lt_one_of_lt_of_lt_one`
* `@[to_additive] lemma right.mul_lt_one_of_lt_of_lt_one`
* `@[to_additive] lemma left.mul_lt_one_of_lt_of_lt_one`
* `@[to_additive] lemma right.mul_lt_one_of_lt_of_lt_one`
* `@[to_additive right.add_nonneg] lemma right.one_le_mul`
* `@[to_additive right.pos_add] lemma right.one_lt_mul`
--
Lemmas that have merged with their unprimed versions due to diminished typeclass assumptions
* `@[to_additive] lemma lt_mul_of_one_le_of_lt'`
* `@[to_additive] lemma lt_mul_of_one_lt_of_lt'`
* `@[to_additive] lemma mul_le_of_le_of_le_one'`
* `@[to_additive] lemma mul_le_of_le_one_of_le'`
* `@[to_additive] lemma mul_lt_of_lt_of_le_one'`
* `@[to_additive] lemma mul_lt_of_lt_of_lt_one'`
* `@[to_additive] lemma mul_lt_of_lt_one_of_lt'`
* the three lemmas
* * `@[to_additive] lemma mul_lt_of_le_one_of_lt'`,
* * `mul_lt_one_of_le_one_of_lt_one`,
* * `mul_lt_one_of_le_one_of_lt_one'`
all merged into `mul_lt_of_le_one_of_lt`
--
Lemma `@[to_additive] lemma mul_lt_one` broke into
* `@[to_additive] lemma left.mul_lt_one`
* `@[to_additive] lemma right.mul_lt_one`
depending on typeclass assumptions
--
Lemmas that became a direct application of another lemma
* `@[to_additive] lemma mul_lt_one_of_lt_one_of_le_one` and `mul_lt_one_of_lt_one_of_le_one'` are applications of `mul_lt_of_lt_of_le_one`
* `@[to_additive] lemma mul_lt_one'` is an application of `mul_lt_of_lt_of_lt_one`
--
Lemma `@[to_additive] lemma mul_eq_one_iff_eq_one_of_one_le` changed name to `mul_eq_one_iff_eq_one_of_one_le`.
The multiplicative version is never used.
The additive version, `add_eq_zero_iff_eq_zero_of_nonneg` is used: I changed the occurrences in favour of the shorter name.
--
Lemma `@[to_additive add_nonpos] lemma mul_le_one'` continues as
```lean
alias mul_le_of_le_of_le_one ← mul_le_one'
attribute [to_additive add_nonpos] mul_le_one'
```
<!--
Name changes:
* lemma `mul_le_of_le_one_of_le'` became `mul_le_of_le_one_of_le`;
* lemma `lt_mul_of_one_le_of_lt'` became `lt_mul_of_one_le_of_lt`;
* lemma `add_eq_zero_iff_eq_zero_of_nonneg` became `add_eq_zero_iff'`.
(Really, the lemmas above are the ones that were used outside of the PR: the two `mul` ones have a corresponding `to_additive` version and the `add` one is the `to_additive` version of `mul_eq_one_iff_eq_one_of_one_le`.)
-->

### [2021-06-23 04:58:30](https://github.com/leanprover-community/mathlib/commit/168678e)
feat(analysis/liouville/liouville_constant): develop some API for Liouville ([#8005](https://github.com/leanprover-community/mathlib/pull/8005))
Proof of some inequalities for Liouville numbers.

### [2021-06-23 02:56:34](https://github.com/leanprover-community/mathlib/commit/ac2142c)
chore(scripts): update nolints.txt ([#8051](https://github.com/leanprover-community/mathlib/pull/8051))
I am happy to remove some nolints for you!

### [2021-06-23 01:21:37](https://github.com/leanprover-community/mathlib/commit/0bc09d9)
feat(algebra/ordered_field): a few monotonicity results for powers ([#8022](https://github.com/leanprover-community/mathlib/pull/8022))
This PR proves the monotonicity (strict and non-strict) of `n → 1 / a ^ n`, for a fixed `a < 1` in a linearly ordered field.  These are lemmas extracted from PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001): I moved them to a separate PR after the discussion there.

### [2021-06-22 22:06:38](https://github.com/leanprover-community/mathlib/commit/949e98e)
chore(topology/basic): add missing lemma ([#8048](https://github.com/leanprover-community/mathlib/pull/8048))
Adds `is_closed.sdiff`. From LTE.

### [2021-06-22 20:35:50](https://github.com/leanprover-community/mathlib/commit/de4a4ce)
feat(ring_theory/adjoin/basic): lemmas relating adjoin and submodule.span ([#8031](https://github.com/leanprover-community/mathlib/pull/8031))

### [2021-06-22 19:52:44](https://github.com/leanprover-community/mathlib/commit/c594196)
chore(topology/continuous_function/algebra): delete old instances, use bundled sub[monoid, group, ring]s ([#8004](https://github.com/leanprover-community/mathlib/pull/8004))
We remove the `monoid`, `group`, ... instances on `{ f : α → β | continuous f }` since `C(α, β)` should be used instead, and we replacce the `sub[monoid, group, ...]` instances on `{ f : α → β | continuous f }` by definitions of bundled subobjects with carrier `{ f : α → β | continuous f }`. We keep the `set_of` for subobjects since we need a subset to be the carrier.
Zulip : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/instances.20on.20continuous.20subtype

### [2021-06-22 16:26:58](https://github.com/leanprover-community/mathlib/commit/83bd2e6)
feat(analysis/normed_space/multilinear): add a few inequalities ([#8018](https://github.com/leanprover-community/mathlib/pull/8018))
Also add a few lemmas about `tsum` and `nnnorm`.

### [2021-06-22 16:26:57](https://github.com/leanprover-community/mathlib/commit/9c4afb1)
feat(data/zmod): equivalence between the quotient type ℤ / aℤ and `zmod a` ([#7976](https://github.com/leanprover-community/mathlib/pull/7976))
This PR defines the equivalence between `zmod a` and ℤ / aℤ, where `a : ℕ` or `a : ℤ`, and the quotient is a quotient group or quotient ring.
It also defines `zmod.lift n f hf : zmod n →+ A` induced by an additive hom `f : ℤ →+ A` such that `f n = 0`. (The latter map could be, but is no longer, defined as the composition of the equivalence with `quotient.lift f`.)
Zulip threads:
 - [`(ideal.span {d}).quotient` is `zmod d`](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60.28ideal.2Espan.20.7Bd.7D.29.2Equotient.60.20is.20.60zmod.20d.60)
 - [Homomorphism from the integers descends to $$\mathbb{Z}/n$$](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Homomorphism.20from.20the.20integers.20descends.20to.20.24.24.5Cmathbb.7BZ.7D.2Fn.24.24)
 - [ `∈ gmultiples` iff divides](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60.E2.88.88.20gmultiples.60.20iff.20divides)

### [2021-06-22 14:51:33](https://github.com/leanprover-community/mathlib/commit/f477e03)
docs(data/list/erasedup): add module docstring ([#8030](https://github.com/leanprover-community/mathlib/pull/8030))

### [2021-06-22 14:51:32](https://github.com/leanprover-community/mathlib/commit/7e20058)
feat(topology/Profinite/cofiltered_limit): Locally constant functions from cofiltered limits ([#7992](https://github.com/leanprover-community/mathlib/pull/7992))
This generalizes one of the main technical theorems from LTE about cofiltered limits of profinite sets.
This theorem should be useful for a future proof of Stone duality.

### [2021-06-22 13:52:01](https://github.com/leanprover-community/mathlib/commit/6e5de19)
feat(linear_algebra/free_module): add lemmas ([#7950](https://github.com/leanprover-community/mathlib/pull/7950))
Easy results about free modules.

### [2021-06-22 12:45:40](https://github.com/leanprover-community/mathlib/commit/cb7b6cb)
docs(data/list/rotate): add module docstring ([#8027](https://github.com/leanprover-community/mathlib/pull/8027))

### [2021-06-22 12:45:39](https://github.com/leanprover-community/mathlib/commit/94a8073)
feat(analysis/specific_limits): summability of `(λ i, 1 / m ^ f i)` ([#8023](https://github.com/leanprover-community/mathlib/pull/8023))
This PR shows the summability of the series whose `i`th term is `1 / m ^ f i`, where `1 < m` is a fixed real number and `f : ℕ → ℕ` is a function bounded below by the identity function.  While a function eventually bounded below by a constant at least equal to 2 would have been enough, this specific shape is convenient for the Liouville application.
I extracted this lemma, following the discussion in PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001).

### [2021-06-22 12:45:38](https://github.com/leanprover-community/mathlib/commit/a3699b9)
refactor(topology/sheaves/stalks): Refactor proofs about stalk map ([#8000](https://github.com/leanprover-community/mathlib/pull/8000))
Refactoring and speeding up some of my code on stalk maps from [#7092](https://github.com/leanprover-community/mathlib/pull/7092).

### [2021-06-22 12:45:37](https://github.com/leanprover-community/mathlib/commit/208d4fe)
docs(data/pnat): add module docstrings ([#7960](https://github.com/leanprover-community/mathlib/pull/7960))

### [2021-06-22 11:36:42](https://github.com/leanprover-community/mathlib/commit/4cbe7d6)
feat(group_theory/specific_groups/cyclic): A group is commutative if the quotient by the center is cyclic ([#7952](https://github.com/leanprover-community/mathlib/pull/7952))

### [2021-06-22 11:36:40](https://github.com/leanprover-community/mathlib/commit/a1a0940)
chore(ring_theory/ideal): mark `ideal.quotient` as reducible ([#7892](https://github.com/leanprover-community/mathlib/pull/7892))
I had an ideal and wanted to apply a theorem about submodule quotients to the ideal quotient. The API around ideals is designed to have most things defeq to the corresponding submodule definition. Marking this definition as reducible informs the typeclass system that it can use this defeq.
Test case:
````lean
import ring_theory.ideal.basic
/-- Typeclass instances on ideal quotients transfer to submodule quotients.
This is useful if you want to apply results that hold for general submodules
to ideals specifically.
The instance will not be found if `ideal.quotient` is not reducible,
e.g. after you uncomment the following line:
```
local attribute [semireducible] ideal.quotient
```
-/
example {R : Type*} [comm_ring R] (I : ideal R)
  [fintype (ideal.quotient I)] : fintype (submodule.quotient I) :=
infer_instance
````
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Making.20.60ideal.2Equotient.60.20reducible.20.28or.20deleted.20altogether.3F.29

### [2021-06-22 11:36:40](https://github.com/leanprover-community/mathlib/commit/96f09a6)
feat(group_theory/perm/cycles): cycle_factors_finset ([#7540](https://github.com/leanprover-community/mathlib/pull/7540))

### [2021-06-22 10:22:32](https://github.com/leanprover-community/mathlib/commit/9ca8597)
feat(linear_algebra/matrix/reindex): add some lemmas ([#7963](https://github.com/leanprover-community/mathlib/pull/7963))
From LTE
Added lemmas `reindex_linear_equiv_trans`, `reindex_linear_equiv_comp`, `reindex_linear_equiv_comp_apply`, `reindex_linear_equiv_one` and `mul_reindex_linear_equiv_mul_one` needed in LTE.

### [2021-06-22 08:42:23](https://github.com/leanprover-community/mathlib/commit/faaa0bc)
feat(algebra/ordered_field): `(1 - 1 / a)⁻¹ ≤ 2` ([#8021](https://github.com/leanprover-community/mathlib/pull/8021))
A lemma from the Liouville PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001).  I extracted this lemma, after the discussion there.

### [2021-06-22 03:06:41](https://github.com/leanprover-community/mathlib/commit/3b4d1d8)
chore(scripts): update nolints.txt ([#8032](https://github.com/leanprover-community/mathlib/pull/8032))
I am happy to remove some nolints for you!

### [2021-06-22 03:06:40](https://github.com/leanprover-community/mathlib/commit/6796bee)
chore(algebra/char_p/basic): generalize to non_assoc_semiring ([#7985](https://github.com/leanprover-community/mathlib/pull/7985))

### [2021-06-22 03:06:39](https://github.com/leanprover-community/mathlib/commit/4416eac)
feat(topology/instances/real): a continuous periodic function has compact range (and is hence bounded) ([#7968](https://github.com/leanprover-community/mathlib/pull/7968))
A few more facts about periodic functions, namely:
- If a function `f` is `periodic` with positive period `p`,
  then for all `x` there exists `y` such that `y` is an element of `[0, p)` and `f x = f y`
- A continuous, periodic function has compact range
- A continuous, periodic function is bounded

### [2021-06-22 01:52:04](https://github.com/leanprover-community/mathlib/commit/e4b9561)
feat(linear_algebra/basic): weaken typeclasses ([#8028](https://github.com/leanprover-community/mathlib/pull/8028))

### [2021-06-21 20:24:31](https://github.com/leanprover-community/mathlib/commit/80daef4)
chore(category_theory/limits): shorten some long lines ([#8007](https://github.com/leanprover-community/mathlib/pull/8007))

### [2021-06-21 19:43:14](https://github.com/leanprover-community/mathlib/commit/520bbe6)
feat(algebra/non_unital_alg_hom): define non_unital_alg_hom ([#7863](https://github.com/leanprover-community/mathlib/pull/7863))
The motivation is to be able to state the universal property for a magma algebra using bundled morphisms.

### [2021-06-21 19:43:13](https://github.com/leanprover-community/mathlib/commit/2b80d2f)
feat(geometry/euclidean/sphere): proof of Freek thm 95 - Ptolemy’s Theorem ([#7329](https://github.com/leanprover-community/mathlib/pull/7329))

### [2021-06-21 19:03:52](https://github.com/leanprover-community/mathlib/commit/2fb0842)
perf(ci): use self-hosted runner for bors ([#8024](https://github.com/leanprover-community/mathlib/pull/8024))
Run CI builds for the `staging` branch used by bors on a self-hosted github actions runner.  This runner has been graciously provided by Johan Commelin's DFG grant and is hosted at the Albert-Ludwigs-Universität Freiburg.
We need to use two github actions workflow files to use a separate runner for the `staging` branch: `build.yml` and `bors.yml`.  These are almost identical, except for the `runs-on:` property indicating which runner should be used.  The shell script `mk_build_yml.sh` is therefore used to generate both files from the common template `build.yml.in`.

### [2021-06-21 14:25:31](https://github.com/leanprover-community/mathlib/commit/eb13f6b)
feat(ring_theory/derivation): add missing dsimp lemmas, use old_structure_command, golf structure proofs ([#8013](https://github.com/leanprover-community/mathlib/pull/8013))
This adds a pile of missing coercion lemmas proved by refl, and uses them to construct the `add_comm_monoid`, `add_comm_group`, and `module` instances.
This also changes `derivation` to be an old-style structure, which is more in line with the other bundled homomorphisms.
This also removes `derivation.commutator` to avoid having two ways to spell the same thing, as this leads to lemmas being harder to apply

### [2021-06-21 14:25:28](https://github.com/leanprover-community/mathlib/commit/92263c0)
refactor(algebraic_geometry/structure_sheaf): Enclose definitions in structure_sheaf namespace ([#8010](https://github.com/leanprover-community/mathlib/pull/8010))
Moves some pretty generic names like `const` and `to_open` to the `structure_sheaf` namespace.

### [2021-06-21 14:25:27](https://github.com/leanprover-community/mathlib/commit/5bc18a9)
feat(topology/category/limits): Generalize Topological Kőnig's lemma  ([#7982](https://github.com/leanprover-community/mathlib/pull/7982))
This PR generalizes the Topological Kőnig's lemma to work with limits over cofiltered categories (as opposed to just directed orders). Along the way, we also prove some more API for the category instance on `ulift C`, and provide an  `as_small C` construction for a category `C`. 
Coauthored with @kmill

### [2021-06-21 14:25:26](https://github.com/leanprover-community/mathlib/commit/9ce032c)
feat(data/matrix/basic): generalize to non_assoc_semiring ([#7974](https://github.com/leanprover-community/mathlib/pull/7974))
Matrices with whose coefficients form a non-unital and/or non-associative ring themselves form a non-unital and non-associative ring.
This isn't a full generalization of the file, the main aim was to generalize the typeclass instances available.

### [2021-06-21 08:39:18](https://github.com/leanprover-community/mathlib/commit/3ef52f3)
chore(logic/basic): actually fixup `eq_or_ne` ([#8015](https://github.com/leanprover-community/mathlib/pull/8015))
this lemma loves being broken...

### [2021-06-21 08:39:17](https://github.com/leanprover-community/mathlib/commit/abdc316)
feat(analysis/normed_space/normed_group_hom): add lemmas ([#7875](https://github.com/leanprover-community/mathlib/pull/7875))
From LTE.

### [2021-06-21 03:37:41](https://github.com/leanprover-community/mathlib/commit/c7d094d)
chore(scripts): update nolints.txt ([#8017](https://github.com/leanprover-community/mathlib/pull/8017))
I am happy to remove some nolints for you!

### [2021-06-21 03:37:40](https://github.com/leanprover-community/mathlib/commit/3925fc0)
feat(analysis/liouville/liouville_constant.lean): create a file and introduce Liouville's constant ([#7996](https://github.com/leanprover-community/mathlib/pull/7996))
Introduce a new file and the definition of Liouville's number.  This is on the way to PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).

### [2021-06-21 03:37:39](https://github.com/leanprover-community/mathlib/commit/4d69b0f)
chore(topology/algebra/infinite_sum): small todo ([#7994](https://github.com/leanprover-community/mathlib/pull/7994))
Generalize a lemma from `f : ℕ → ℝ` to `f : β → α`, with 
```lean
[add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α] [decidable_eq β] 
```
This was marked as TODO after [#6017](https://github.com/leanprover-community/mathlib/pull/6017)/[#6096](https://github.com/leanprover-community/mathlib/pull/6096).

### [2021-06-21 03:37:38](https://github.com/leanprover-community/mathlib/commit/5cdbb4c)
feat(algebra/*/pi, topology/continuous_function/algebra): homomorphism induced by left-composition ([#7984](https://github.com/leanprover-community/mathlib/pull/7984))
Given a monoid homomorphism from `α` to `β`, there is an induced monoid homomorphism from `I → α` to `I → β`, by left-composition.
Same result for semirings, modules, algebras.
Same result for topological monoids, topological semirings, etc, and the function spaces `C(I, α)`, `C(I, β)`, if the homomorphism is continuous.
Of these eight constructions, the only one I particularly want is the last one (topological algebras).  If reviewers feel it is better not to clog mathlib up with unused constructions, I am happy to cut the other seven from this PR.

### [2021-06-21 03:37:37](https://github.com/leanprover-community/mathlib/commit/18c1c4a)
fix(tactic/linarith/preprocessing): capture result of zify_proof ([#7901](https://github.com/leanprover-community/mathlib/pull/7901))
this fixes the error encountered in the MWE in this Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/delayed_abstraction.20meta-variables/near/242376874
the `simplify` call inside of `zify_proof` does something bad to the tactic state when called in the scope of an `io.run_tactic`, not entirely sure why ¯\_(ツ)_/¯

### [2021-06-20 21:36:12](https://github.com/leanprover-community/mathlib/commit/767901a)
feat(algebra/ordered_ring): `a + 1 ≤ 2 * a` ([#7995](https://github.com/leanprover-community/mathlib/pull/7995))
Prove one lemma, useful for the Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).  The placement of the lemma will change, once the `ordered` refactor will get to  `ordered_ring`.

### [2021-06-20 17:21:15](https://github.com/leanprover-community/mathlib/commit/fae00c7)
chore(analysis/special_functions): move measurability statements to measure_theory folder ([#8006](https://github.com/leanprover-community/mathlib/pull/8006))
Make sure that measure theory is not imported in basic files defining trigonometric functions and real powers. The measurability of these functions is postponed to a new file `measure_theory.special_functions`.

### [2021-06-20 13:40:08](https://github.com/leanprover-community/mathlib/commit/547df12)
chore(analysis/liouville/liouville + data/real/liouville): create folder `analysis/liouville/`, move `data/real/liouville` into new folder ([#7998](https://github.com/leanprover-community/mathlib/pull/7998))
This PR simply creates a new folder `analysis/liouville` and moves `data/real/liouville` into the new folder.  In PR [#7996](https://github.com/leanprover-community/mathlib/pull/7996) I create a new Liouville-related file in the same folder.

### [2021-06-20 12:05:49](https://github.com/leanprover-community/mathlib/commit/3a0f282)
feat(measure_theory/interval_integral): integral of a non-integrable function ([#8011](https://github.com/leanprover-community/mathlib/pull/8011))
The `interval_integral` of a non-`interval_integrable` function is `0`.

### [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d155d9)
refactor(topology/metric_space/isometry): move material about isometries of normed spaces ([#8003](https://github.com/leanprover-community/mathlib/pull/8003))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/topology.20and.20analysis

### [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d5b50a)
feat(algebra/homology/homotopy): flesh out the api a bit, add some simps ([#7941](https://github.com/leanprover-community/mathlib/pull/7941))

### [2021-06-19 18:19:08](https://github.com/leanprover-community/mathlib/commit/63c3ab5)
chore(data/int/basic): rationalize the arguments implicitness (mostly to_nat_sub_of_le) ([#7997](https://github.com/leanprover-community/mathlib/pull/7997))

### [2021-06-19 15:31:15](https://github.com/leanprover-community/mathlib/commit/cd8f7b5)
chore(topology/metric_space/pi_Lp): move to analysis folder, import inner_product_space ([#7991](https://github.com/leanprover-community/mathlib/pull/7991))
Currently, the file `pi_Lp` (on finite products of metric spaces, with the `L^p` norm) is in the topology folder, but it imports a lot of analysis (to have real powers) and it defines a normed space structure, so it makes more sense to have it in analysis. Also, it is currently imported by `inner_product_space`, to give an explicit construction of an inner product space on `pi_Lp 2`, which means that all files importing general purposes lemmas on inner product spaces also import real powers, trigonometry, and so on. We swap the imports, letting `pi_Lp` import `inner_product_space` and moving the relevant bits from the latter file to the former. This gives a more reasonable import graph.

### [2021-06-19 15:31:14](https://github.com/leanprover-community/mathlib/commit/497b84d)
chore(analysis/mean_inequalities): split integral mean inequalities to a new file ([#7990](https://github.com/leanprover-community/mathlib/pull/7990))
Currently, `normed_space.dual` imports a bunch of integration theory for no reason other than the file `mean_inequalities` contains both inequalities for finite sums and integrals. Splitting the file into two (and moving the integral versions to `measure_theory`) gives a more reasonable import graph.

### [2021-06-19 15:31:13](https://github.com/leanprover-community/mathlib/commit/1846a1f)
feat(measure_theory/interval_integral): `abs_integral_le_integral_abs` ([#7959](https://github.com/leanprover-community/mathlib/pull/7959))
The absolute value of the integral of an integrable function is less than or equal to the integral of the absolute value that function.

### [2021-06-19 08:22:50](https://github.com/leanprover-community/mathlib/commit/2ca0452)
feat(data/{fin,nat,zmod}): prove `zmod.coe_add_eq_ite` ([#7975](https://github.com/leanprover-community/mathlib/pull/7975))
This PR adds a couple of lemmas relating addition modulo `n` (in `ℕ`, `fin n` or `zmod n`) and addition in `ℕ` or `ℤ`.
[Based on this Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Homomorphism.20from.20the.20integers.20descends.20to.20.24.24.5Cmathbb.7BZ.7D.2Fn.24.24)

### [2021-06-19 03:04:16](https://github.com/leanprover-community/mathlib/commit/28aee95)
chore(scripts): update nolints.txt ([#7993](https://github.com/leanprover-community/mathlib/pull/7993))
I am happy to remove some nolints for you!

### [2021-06-19 03:04:15](https://github.com/leanprover-community/mathlib/commit/2a48c69)
feat(category_theory/yoneda): develop API for representable functors ([#7962](https://github.com/leanprover-community/mathlib/pull/7962))
Dualises and extends API for representable functors which was previously pretty minimal

### [2021-06-18 23:32:28](https://github.com/leanprover-community/mathlib/commit/42ab44c)
feat(group_theory): computable 1st isomorphism theorem ([#7988](https://github.com/leanprover-community/mathlib/pull/7988))
This PR defines a computable version of the first isomorphism theorem for groups and monoids that takes a right inverse of the map, `quotient_ker_equiv_of_right_inverse`.

### [2021-06-18 23:32:27](https://github.com/leanprover-community/mathlib/commit/3ee6248)
feat(measure_theory): links between an integral and its improper version ([#7164](https://github.com/leanprover-community/mathlib/pull/7164))
This PR introduces ways of studying and computing `∫ x, f x ∂μ` by studying the limit of the sequence `∫ x in φ n, f x ∂μ` for an appropriate sequence `φ` of subsets of the domain of `f`.

### [2021-06-18 20:48:47](https://github.com/leanprover-community/mathlib/commit/f2f10cc)
docs(data/set/enumerate): add module and definition docstrings ([#7967](https://github.com/leanprover-community/mathlib/pull/7967))

### [2021-06-18 20:48:46](https://github.com/leanprover-community/mathlib/commit/3a0653c)
feat(data/real/ennreal): add a `algebra ℝ≥0 ℝ≥0∞` instance ([#7846](https://github.com/leanprover-community/mathlib/pull/7846))

### [2021-06-18 18:18:49](https://github.com/leanprover-community/mathlib/commit/52dbff0)
chore(topology/basic): rename compact_Icc to is_compact_Icc ([#7979](https://github.com/leanprover-community/mathlib/pull/7979))
Also rename `compact_interval` to `is_compact_interval`. And a bunch of random additions, all minor, as prerequisistes to [#7978](https://github.com/leanprover-community/mathlib/pull/7978)

### [2021-06-18 15:33:01](https://github.com/leanprover-community/mathlib/commit/29e7a8d)
feat(topology/algebra/ordered, topology/algebra/infinite_sum): bounded monotone sequences converge (variant versions) ([#7983](https://github.com/leanprover-community/mathlib/pull/7983))
A bounded monotone sequence converges to a value `a`, if and only if `a` is a least upper bound for its range.
Mathlib had several variants of this fact previously (phrased in terms of, eg, `csupr`), but not quite this version (phrased in terms of `has_lub`).  This version has a couple of advantages:
- it applies to more general typeclasses (eg, `linear_order`) where the existence of suprema is not in general known
- it applies to algebraic typeclasses (`linear_ordered_add_comm_monoid`, etc) where, since completeness of orders is not a mix-in, it is not possible to simultaneously assume `(conditionally_)complete_linear_order`
The latter point makes these lemmas useful when dealing with `tsum`.  We get: a nonnegative function `f` satisfies `has_sum f a`, if and only if `a` is a least upper bound for its partial sums.

### [2021-06-18 13:40:11](https://github.com/leanprover-community/mathlib/commit/7c9a811)
feat(analysis/convex/basic): missing lemmas ([#7946](https://github.com/leanprover-community/mathlib/pull/7946))
- the union of a set/indexed family of convex sets is convex
- `open_segment a b` is convex
- a set is nonempty iff its convex hull is

### [2021-06-18 01:58:07](https://github.com/leanprover-community/mathlib/commit/e168bf7)
chore(scripts): update nolints.txt ([#7981](https://github.com/leanprover-community/mathlib/pull/7981))
I am happy to remove some nolints for you!

### [2021-06-17 17:11:00](https://github.com/leanprover-community/mathlib/commit/49bf1fd)
chore(order/iterate): fix up the namespace ([#7977](https://github.com/leanprover-community/mathlib/pull/7977))

### [2021-06-17 17:10:59](https://github.com/leanprover-community/mathlib/commit/dc73d1b)
docs(data/*/sqrt): add one module docstring and expand the other ([#7973](https://github.com/leanprover-community/mathlib/pull/7973))

### [2021-06-17 17:10:58](https://github.com/leanprover-community/mathlib/commit/3824a43)
docs(data/list/intervals): add module docstring ([#7972](https://github.com/leanprover-community/mathlib/pull/7972))

### [2021-06-17 17:10:57](https://github.com/leanprover-community/mathlib/commit/93d7812)
docs(data/int/range): add module docstring ([#7971](https://github.com/leanprover-community/mathlib/pull/7971))

### [2021-06-17 17:10:56](https://github.com/leanprover-community/mathlib/commit/da1a32c)
docs(data/int/cast): add module docstring ([#7969](https://github.com/leanprover-community/mathlib/pull/7969))

### [2021-06-17 17:10:50](https://github.com/leanprover-community/mathlib/commit/de6d739)
docs(data/nat/dist): add module docstring ([#7966](https://github.com/leanprover-community/mathlib/pull/7966))

### [2021-06-17 17:10:49](https://github.com/leanprover-community/mathlib/commit/ce23f37)
feat(topology/locally_constant): Adds a few useful constructions ([#7954](https://github.com/leanprover-community/mathlib/pull/7954))
This PR adds a few useful constructions around locallly constant functions:
1. A locally constant function to `fin 2` associated to a clopen set.
2. Flipping a locally constant function taking values in a function type.
3. Unflipping a finite family of locally constant function.
4. Descending locally constant functions along an injective map.

### [2021-06-17 17:10:48](https://github.com/leanprover-community/mathlib/commit/e9f9f3f)
docs(data/nat/cast): add module docstring ([#7947](https://github.com/leanprover-community/mathlib/pull/7947))

### [2021-06-17 17:10:47](https://github.com/leanprover-community/mathlib/commit/9784396)
refactor(order/preorder_hom): golf and simp lemmas ([#7429](https://github.com/leanprover-community/mathlib/pull/7429))
The main change here is to adjust `simps` to generate coercion lemmas rather than `.to_fun` for `preorder_hom`, which allows us to auto-generate some simp lemmas.

### [2021-06-17 11:31:07](https://github.com/leanprover-community/mathlib/commit/cbb8f01)
feat(algebra/group/basic): prove `a / 1 = a` and remove `sub_zero` ([#7956](https://github.com/leanprover-community/mathlib/pull/7956))
Add a proof that, in a group, `a / 1 = a`.  As a consequence, `sub_zero` is the `to_additive version of this lemma and I removed it.
The name of the lemma is `div_one'`, since the unprimed version is taken by `group_with_zero`.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60div_one'.60

### [2021-06-17 11:31:06](https://github.com/leanprover-community/mathlib/commit/6578f1c)
feat(data/setoid/basic): add a computable version of quotient_ker_equiv_of_surjective ([#7930](https://github.com/leanprover-community/mathlib/pull/7930))
Perhaps more usefully, this also allows definitional control of the inverse mapping

### [2021-06-17 08:31:45](https://github.com/leanprover-community/mathlib/commit/1e43208)
refactor(ring_theory): use `x ∈ non_zero_divisors` over `x : non_zero_divisors` ([#7961](https://github.com/leanprover-community/mathlib/pull/7961))
`map_ne_zero_of_mem_non_zero_divisors` and `map_mem_non_zero_divisors` used to take `x : non_zero_divisors A` as an (implicit) argument. This is awkward if you only have `hx : x ∈ non_zero_divisors A`, requiring you to write out `@map_ne_zero_of_mem_non_zero_divisors _ _ _ _ _ _ hf ⟨x, hx⟩`. By making `x ∈ non_zero_divisors A` the explicit argument, we can avoid this annoyance.
See e.g. `ring_theory/polynomial/scale_roots.lean` for the improvement.

### [2021-06-17 02:48:11](https://github.com/leanprover-community/mathlib/commit/1a6c871)
chore(scripts): update nolints.txt ([#7965](https://github.com/leanprover-community/mathlib/pull/7965))
I am happy to remove some nolints for you!

### [2021-06-17 00:23:25](https://github.com/leanprover-community/mathlib/commit/dc5d0c1)
feat(data/matrix): `has_repr` instances for `fin` vectors and matrices ([#7953](https://github.com/leanprover-community/mathlib/pull/7953))
This PR provides `has_repr` instances for the types `fin n → α` and `matrix (fin m) (fin n) α`, displaying in the `![...]` matrix notation. This is especially useful if you want to `#eval` a calculation involving matrices.
[Based on this Zulip post.](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Matrix.20operations/near/242766110)

### [2021-06-17 00:23:24](https://github.com/leanprover-community/mathlib/commit/641a9d3)
feat(model_theory/basic): Substructures ([#7762](https://github.com/leanprover-community/mathlib/pull/7762))
Defines substructures of first-order structures

### [2021-06-16 18:44:26](https://github.com/leanprover-community/mathlib/commit/456a6d5)
docs(data/option/basic): add module docstring ([#7958](https://github.com/leanprover-community/mathlib/pull/7958))

### [2021-06-16 18:44:25](https://github.com/leanprover-community/mathlib/commit/08dfaab)
docs(data/set/disjointed): add module docstring and some whitespaces ([#7957](https://github.com/leanprover-community/mathlib/pull/7957))

### [2021-06-16 18:44:24](https://github.com/leanprover-community/mathlib/commit/49aa106)
docs(data/*/nat_antidiagonal): add one module docstring and harmonise others ([#7919](https://github.com/leanprover-community/mathlib/pull/7919))

### [2021-06-16 18:44:23](https://github.com/leanprover-community/mathlib/commit/366a449)
doc(topology/algebra/ring): add module docs + tidy ([#7893](https://github.com/leanprover-community/mathlib/pull/7893))

### [2021-06-16 15:31:34](https://github.com/leanprover-community/mathlib/commit/a564bf1)
feat(data/list/cycle): cycles as quotients of lists ([#7504](https://github.com/leanprover-community/mathlib/pull/7504))
Cycles are common structures, and we define them as a quotient of lists. This is on the route to defining concrete cyclic permutations, and could also be used for encoding properties of cycles in graphs.

### [2021-06-16 12:25:45](https://github.com/leanprover-community/mathlib/commit/0490b43)
refactor(geometry/manifold/instances/circle): split out (topological) group facts ([#7951](https://github.com/leanprover-community/mathlib/pull/7951))
Move the group and topological group facts about the unit circle in `ℂ` from `geometry.manifold.instances.circle` to a new file `analysis.complex.circle`.  Delete `geometry.manifold.instances.circle`, moving the remaining material to a section in `geometry.manifold.instances.sphere`.

### [2021-06-16 09:58:27](https://github.com/leanprover-community/mathlib/commit/95a116a)
chore(measure_theory/lp_space): simplify tendsto_Lp_iff_tendsto_\McLp by using tendsto_iff_dist_tendsto_zero ([#7942](https://github.com/leanprover-community/mathlib/pull/7942))

### [2021-06-16 06:02:08](https://github.com/leanprover-community/mathlib/commit/690ab17)
refactor(algebra/algebra/basic): replace `algebra.comap` with `restrict_scalars` ([#7949](https://github.com/leanprover-community/mathlib/pull/7949))
The constructions `algebra.comap` and `restrict_scalars` are essentially the same thing -- a type synonym to allow one to switch to a smaller scalar field.  Previously `restrict_scalars` was for modules and `algebra.comap` for algebras; I am unifying them so that `restrict_scalars` works for both.
Declaration changes:
- `algebra.comap`, `algebra.comap.inhabited`, `is_scalar_tower.comap`
Use the pre-existing (for modules) `restrict_scalars`, `restrict_scalars.inhabited`, `restrict_scalars.is_scalar_tower`
- `algebra.comap.X` for `X` in `semiring`, `ring`, `comm_semiring`, `comm_ring`, `algebra`
Replaced with `restrict_scalars.X`
- `algebra.comap.algebra'`
Replaced with `restrict_scalars.algebra_orig` (to be consistent with `restrict_scalars.module_orig`)
- `algebra.comap.to_comap` and `algebra.comap.of_comap`
Combined into an `alg_equiv` and renamed `restrict_scalars.alg_equiv` (to be consistent with `restrict_scalars.linear_equiv`)
- `subalgebra.comap`
Replaced with a generalized version, `subalgebra.restrict_scalars`, which (to be consistent with `submodule.restrict_scalars`) applies to an `is_scalar_tower`, not just to the type synonym
Deleted altogether:
- `algebra.to_comap`, `algebra.to_comap_apply`
This construction is now 
`(algebra.of_id S (restrict_scalars R S A)).restrict_scalars R`
It was only used once in mathlib, where I have replaced it by its definition
- `alg_hom.comap`, `alg_equiv.comap`
These are not currently used in mathlib but if needed one can instead use `alg_hom.restrict_scalars` and `alg_equiv.restrict_scalars`
- `is_scalar_tower.algebra_comap_eq`
The proof is now `rfl` and it was never used in mathlib.
It would then be possible, in a follow-up PR, to rename `subalgebra.comap'` to `subalgebra.comap`, although I have no immediate plans to do this.

### [2021-06-16 04:52:02](https://github.com/leanprover-community/mathlib/commit/b865892)
feat(algebraic_geometry/Spec): Make Spec a functor. ([#7790](https://github.com/leanprover-community/mathlib/pull/7790))

### [2021-06-16 02:11:41](https://github.com/leanprover-community/mathlib/commit/ba3a4b7)
chore(scripts): update nolints.txt ([#7955](https://github.com/leanprover-community/mathlib/pull/7955))
I am happy to remove some nolints for you!

### [2021-06-15 23:35:55](https://github.com/leanprover-community/mathlib/commit/30314c2)
fix(measure_theory/interval_integral): generalize some lemmas ([#7944](https://github.com/leanprover-community/mathlib/pull/7944))
The proofs of some lemmas about the integral of a function `f : ℝ → ℝ` also hold for `f : α → ℝ` (with `α` under the usual conditions).

### [2021-06-15 23:35:54](https://github.com/leanprover-community/mathlib/commit/45619c7)
feat(order/iterate): id_le lemmas ([#7943](https://github.com/leanprover-community/mathlib/pull/7943))

### [2021-06-15 23:35:52](https://github.com/leanprover-community/mathlib/commit/e5c97e1)
feat(analysis/convex/basic): a linear map is convex and concave ([#7934](https://github.com/leanprover-community/mathlib/pull/7934))

### [2021-06-15 19:56:41](https://github.com/leanprover-community/mathlib/commit/f1f4c23)
feat(analysis/convex/basic): convex_on lemmas ([#7933](https://github.com/leanprover-community/mathlib/pull/7933))

### [2021-06-15 19:56:40](https://github.com/leanprover-community/mathlib/commit/5d03dcd)
feat(analysis/normed_space/dual): add eq_zero_of_forall_dual_eq_zero ([#7929](https://github.com/leanprover-community/mathlib/pull/7929))
The variable `𝕜` is made explicit in `norm_le_dual_bound` because lean can otherwise not guess it in the proof of `eq_zero_of_forall_dual_eq_zero`.

### [2021-06-15 19:56:39](https://github.com/leanprover-community/mathlib/commit/e5ff5fb)
feat(data/finsupp/basic): equiv_congr_left ([#7755](https://github.com/leanprover-community/mathlib/pull/7755))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Group.20cohomology/near/240737546).

### [2021-06-15 14:54:47](https://github.com/leanprover-community/mathlib/commit/2f1f34a)
feat(measure_theory/lp_space): add `mem_Lp.mono_measure` ([#7927](https://github.com/leanprover-community/mathlib/pull/7927))
also add monotonicity lemmas wrt the measure for `snorm'`, `snorm_ess_sup` and `snorm`.

### [2021-06-15 14:54:46](https://github.com/leanprover-community/mathlib/commit/5f8cc8e)
docs(undergrad): mark convex, convex hull, and extreme points as done ([#7924](https://github.com/leanprover-community/mathlib/pull/7924))

### [2021-06-15 14:54:44](https://github.com/leanprover-community/mathlib/commit/e4ceee6)
feat(group_theory/order_of_element): Raising to a coprime power is a bijection ([#7923](https://github.com/leanprover-community/mathlib/pull/7923))
If `gcd(|G|,k)=1` then the `k`th power map is a bijection

### [2021-06-15 14:54:41](https://github.com/leanprover-community/mathlib/commit/f4991b9)
feat(measure_theory/bochner_integration): properties of simple functions (mem_Lp, integrable, fin_meas_supp) ([#7918](https://github.com/leanprover-community/mathlib/pull/7918))

### [2021-06-15 14:54:40](https://github.com/leanprover-community/mathlib/commit/b19c491)
chore(order/lattice): rename le_sup_left_of_le ([#7856](https://github.com/leanprover-community/mathlib/pull/7856))
rename `le_sup_left_of_le` to `le_sup_of_le_left`, and variants

### [2021-06-15 14:54:39](https://github.com/leanprover-community/mathlib/commit/8e28104)
feat(algebra/algebra/basic): define `restrict_scalars.linear_equiv` ([#7807](https://github.com/leanprover-community/mathlib/pull/7807))
Also updating some doc-strings.

### [2021-06-15 14:54:38](https://github.com/leanprover-community/mathlib/commit/a16650c)
feat(geometry/manifold/algebra/smooth_functions): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7749](https://github.com/leanprover-community/mathlib/pull/7749))
Changed names to be consistent with the topology library and proven that some coercions are morphisms.

### [2021-06-15 06:03:53](https://github.com/leanprover-community/mathlib/commit/bf83c30)
chore(algebra/{ordered_monoid_lemmas, ordered_monoid}): move two sections close together ([#7921](https://github.com/leanprover-community/mathlib/pull/7921))
This PR aims at shortening the diff between `master` and PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) of the order refactor.
I moved the `mono` section of `algebra/ordered_monoid_lemmas` to the end of the file and appended the `strict_mono` section of `algebra/ordered_monoid` after that.
Note: the hypotheses are not optimal, but, with the current `instances` in this version, I did not know how to improve this.  It will get better by the time PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) is merged.  In fact, the next PR in the sequence, [#7876](https://github.com/leanprover-community/mathlib/pull/7876), already removes the unnecessary assumptions.

### [2021-06-15 06:03:52](https://github.com/leanprover-community/mathlib/commit/d74a898)
fix(meta/expr): fix mreplace ([#7912](https://github.com/leanprover-community/mathlib/pull/7912))
Previously the function would not recurse into macros (like `have`).
Also add warning to docstring.

### [2021-06-15 03:22:09](https://github.com/leanprover-community/mathlib/commit/d960b2d)
chore(scripts): update nolints.txt ([#7939](https://github.com/leanprover-community/mathlib/pull/7939))
I am happy to remove some nolints for you!

### [2021-06-15 03:22:08](https://github.com/leanprover-community/mathlib/commit/81f29f9)
chore(topology/metric_space): cleanup Gromov-Hausdorff files ([#7936](https://github.com/leanprover-community/mathlib/pull/7936))
Rename greek type variables to meaningful uppercase letters. Lint the files. Add a header where needed. Add spaces after forall or exist to conform to current style guide. Absolutely no new mathematical content.

### [2021-06-15 03:22:07](https://github.com/leanprover-community/mathlib/commit/a83f2c2)
feat(group_theory/order_of_element): Power of subset is subgroup ([#7915](https://github.com/leanprover-community/mathlib/pull/7915))
If `S` is a nonempty subset of `G`, then `S ^ |G|` is a subgroup of `G`.

### [2021-06-15 03:22:06](https://github.com/leanprover-community/mathlib/commit/ba25bb8)
feat(measure_theory): define `measure.trim`, restriction of a measure to a sub-sigma algebra ([#7906](https://github.com/leanprover-community/mathlib/pull/7906))
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself is not a measure on `m`. For `hm : m ≤ m0`, we define the measure `μ.trim hm` on `m`.
We add lemmas relating a measure and its trimmed version, mostly about integrals of `m`-measurable functions.

### [2021-06-14 21:50:17](https://github.com/leanprover-community/mathlib/commit/8377a1f)
feat(measure_theory/lp_space): add snorm_le_snorm_mul_rpow_measure_univ ([#7926](https://github.com/leanprover-community/mathlib/pull/7926))
There were already versions of this lemma for `snorm'` and `snorm_ess_sup`. The new lemma collates these into a statement about `snorm`.

### [2021-06-14 21:50:16](https://github.com/leanprover-community/mathlib/commit/e041dbe)
chore(algebra/covariant_and_contravariant): fix typos in module doc-strings ([#7925](https://github.com/leanprover-community/mathlib/pull/7925))
This PR changes slightly the doc-strings to make the autogenerated documentation more consistent.  I also removed some unstylish double spaces.

### [2021-06-14 21:50:15](https://github.com/leanprover-community/mathlib/commit/4a8ce41)
feat(analysis/special_functions/trigonometric): facts about periodic trigonometric functions  ([#7841](https://github.com/leanprover-community/mathlib/pull/7841))
I use the periodicity API that I added in [#7572](https://github.com/leanprover-community/mathlib/pull/7572) to write lemmas about sine (real and complex), cosine (real and complex), tangent (real and complex), and the  exponential function (complex only).

### [2021-06-14 21:50:14](https://github.com/leanprover-community/mathlib/commit/fed7cf0)
fix(tactic/induction): fix multiple cases'/induction' bugs ([#7717](https://github.com/leanprover-community/mathlib/pull/7717))
* Fix generalisation in the presence of frozen local instances.
  Any time we revert a potentially frozen hypothesis, we now unfreeze local
  hypotheses during the operation. This makes sure that generalisation works
  uniformly whether or not any local instances are frozen.
* Treat local defs as fixed during auto-generalisation
  induction' gets confused if we generalise over local definitions since they
  turn into lets when reverted. Ideally, we would handle local defs
  transparently, but that would require a lot of new code. So instead, we at
  least stop auto-generalisation from generalising them (and their
  dependencies).
* Handle infinitely branching types
  induction' and cases' previously did not acknowledge the existence of
  infinitely branching types at all, leading to various internal errors.
New test cases for all these bugs, due to Patrick Massot, were added to the test
suite.

### [2021-06-14 21:50:13](https://github.com/leanprover-community/mathlib/commit/f781c47)
feat(linear_algebra/determinant): specialize `linear_equiv.is_unit_det` to automorphisms ([#7667](https://github.com/leanprover-community/mathlib/pull/7667))
`linear_equiv.is_unit_det` is defined for all equivs between equal-dimensional spaces, using `det (linear_map.to_matrix _ _ _)`, but I needed this result for `linear_map.det _` (which only exists between the exact same space). So I added the specialization `linear_equiv.is_unit_det'`.

### [2021-06-14 21:50:12](https://github.com/leanprover-community/mathlib/commit/615af75)
feat(measure_theory/interval_integral): `integral_deriv_comp_mul_deriv` ([#7141](https://github.com/leanprover-community/mathlib/pull/7141))
`∫ x in a..b, (g ∘ f) x * f' x`, where `f'` is derivative of `f` and `g` is the derivative of some function (the latter qualification allowing us to compute the integral directly by FTC-2)

### [2021-06-14 12:40:22](https://github.com/leanprover-community/mathlib/commit/386962c)
feat(algebra/char_zero): `neg_eq_self_iff` ([#7916](https://github.com/leanprover-community/mathlib/pull/7916))
`-a = a ↔ a = 0` and `a = -a ↔ a = 0`.

### [2021-06-14 07:23:15](https://github.com/leanprover-community/mathlib/commit/461b444)
docs(data/rat/denumerable): add module docstring ([#7920](https://github.com/leanprover-community/mathlib/pull/7920))

### [2021-06-14 07:23:14](https://github.com/leanprover-community/mathlib/commit/a853a6a)
feat(analysis/normed_space): nnreal.coe_nat_abs ([#7911](https://github.com/leanprover-community/mathlib/pull/7911))
from LTE

### [2021-06-14 06:07:37](https://github.com/leanprover-community/mathlib/commit/6aed9a7)
feat(analysis/convex): add dual cone ([#7738](https://github.com/leanprover-community/mathlib/pull/7738))
Add definition of the dual cone of a set in a real inner product space

### [2021-06-14 03:56:10](https://github.com/leanprover-community/mathlib/commit/fec6c8a)
chore(scripts): update nolints.txt ([#7922](https://github.com/leanprover-community/mathlib/pull/7922))
I am happy to remove some nolints for you!

### [2021-06-13 22:32:12](https://github.com/leanprover-community/mathlib/commit/3004513)
feat(measure_theory/ess_sup): monotonicity of ess_sup/ess_inf w.r.t. the measure ([#7917](https://github.com/leanprover-community/mathlib/pull/7917))

### [2021-06-13 22:32:11](https://github.com/leanprover-community/mathlib/commit/4fe7781)
chore(algebra/lie/basic + classical): golf some proofs ([#7903](https://github.com/leanprover-community/mathlib/pull/7903))
Another PR with some golfing, to get acquainted with the files!  Oliver, I really like how you set this up!
Also, feel free to say that you do not like the golfing: there is a subtle tension between proving stuff fast and making it accessible!

### [2021-06-13 22:32:10](https://github.com/leanprover-community/mathlib/commit/b324488)
docs(set_theory/schroeder_bernstein): add module docstring ([#7900](https://github.com/leanprover-community/mathlib/pull/7900))

### [2021-06-13 22:32:09](https://github.com/leanprover-community/mathlib/commit/e971eae)
docs(data/nat/totient): add module docstring ([#7899](https://github.com/leanprover-community/mathlib/pull/7899))

### [2021-06-13 22:32:08](https://github.com/leanprover-community/mathlib/commit/a359bd9)
chore(measure_theory): measurability statements for coercions, coherent naming ([#7854](https://github.com/leanprover-community/mathlib/pull/7854))
Also add a few lemmas on measure theory

### [2021-06-13 17:23:56](https://github.com/leanprover-community/mathlib/commit/5c11458)
chore(analysis/normed_space/normed_group_hom): golf proof of normed_group_hom.bounded ([#7896](https://github.com/leanprover-community/mathlib/pull/7896))

### [2021-06-13 17:23:55](https://github.com/leanprover-community/mathlib/commit/2f40f35)
feat(measure_theory): continuity of primitives ([#7864](https://github.com/leanprover-community/mathlib/pull/7864))
From the sphere eversion project
This proves some continuity of interval integrals with respect to parameters and continuity of primitives of measurable functions. The statements are a bit abstract, but they allow to have:
```lean
example {f : ℝ → E} (h_int : integrable f) (a : ℝ) :  
  continuous (λ b, ∫ x in a .. b, f x ∂ volume) :=
h_int.continuous_primitive a
```
under the usual assumptions on `E`: `normed_group E`, `second_countable_topology E`,  `normed_space ℝ E`
`complete_space E`, `measurable_space E`, `borel_space E`, say `E = ℝ` for instance. Of course global integrability is not needed, assuming integrability on all finite length intervals is enough:
```lean
example {f : ℝ → E} (h_int : ∀ a b : ℝ, interval_integrable f volume a b) (a : ℝ) :  
  continuous (λ b, ∫ x in a .. b, f x ∂ volume) :=
continuous_primitive h_int a
```

### [2021-06-13 11:45:04](https://github.com/leanprover-community/mathlib/commit/6d2a051)
feat(algebra/covariant_and_contravariant): API for covariant_and_contravariant ([#7889](https://github.com/leanprover-community/mathlib/pull/7889))
This PR introduces more API for `covariant` and `contravariant` stuff .
Besides the API, I have not actually made further use of the typeclasses or of the API.  This happens in subsequent PRs.
This is a step towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-13 06:04:53](https://github.com/leanprover-community/mathlib/commit/7c9643d)
chore(scripts): update nolints.txt ([#7914](https://github.com/leanprover-community/mathlib/pull/7914))
I am happy to remove some nolints for you!

### [2021-06-13 06:04:52](https://github.com/leanprover-community/mathlib/commit/e13fd48)
docs(data/nat/pairing): add module docstring ([#7897](https://github.com/leanprover-community/mathlib/pull/7897))

### [2021-06-13 06:04:51](https://github.com/leanprover-community/mathlib/commit/2c919b0)
chore(algebra/{ordered_group, linear_ordered_comm_group_with_zero.lean}): rename one lemma, remove more @s ([#7895](https://github.com/leanprover-community/mathlib/pull/7895))
The more substantial part of this PR is changing the name of a lemma from `div_lt_div_iff'` to `mul_inv_lt_mul_inv_iff'`: the lemma proves `a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b`.
Furthermore, in the same spirit as a couple of my recent short PRs, I am removing a few more `@`, in order to sweep under the rug, later on, a change in typeclass assumptions.  This PR only changes a name, which was used only once, and a few proofs, but no statement.
On the path towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-13 06:04:50](https://github.com/leanprover-community/mathlib/commit/add577d)
feat(group_theory/group_action/defs): add `has_mul.to_has_scalar` and relax typeclass in `smul_mul_smul` ([#7885](https://github.com/leanprover-community/mathlib/pull/7885))

### [2021-06-12 23:46:04](https://github.com/leanprover-community/mathlib/commit/e0a3303)
chore(category_theory/filtered): Adds missing instances ([#7909](https://github.com/leanprover-community/mathlib/pull/7909))

### [2021-06-12 23:46:03](https://github.com/leanprover-community/mathlib/commit/9ad8ea3)
chore(linear_algebra/quadratic_form): fix typo ([#7907](https://github.com/leanprover-community/mathlib/pull/7907))

### [2021-06-12 23:46:02](https://github.com/leanprover-community/mathlib/commit/7b7cd0a)
fix(tactic/lint): punctuation of messages ([#7869](https://github.com/leanprover-community/mathlib/pull/7869))
Previously, the linter framework would append punctuation (`.` or `:`) to the message provided by the linter, but this was confusing and lead to some double punctuation. Now all linters specify their own punctuation.

### [2021-06-12 23:46:01](https://github.com/leanprover-community/mathlib/commit/39073fa)
feat(algebra/pointwise): Dynamics of powers of a subset ([#7836](https://github.com/leanprover-community/mathlib/pull/7836))
If `S` is a subset of a group `G`, then the powers of `S` eventually stabilize in size.

### [2021-06-12 15:55:02](https://github.com/leanprover-community/mathlib/commit/ee4fe74)
feat(topology/category/Profinite/cofiltered_clopen): Theorem about clopen sets in cofiltered limits of profinite sets ([#7837](https://github.com/leanprover-community/mathlib/pull/7837))
This PR proves the theorem that any clopen set in a cofiltered limit of profinite sets arises from a clopen set in one of the factors of the limit.
This generalizes a theorem used in LTE.

### [2021-06-12 15:55:00](https://github.com/leanprover-community/mathlib/commit/06094d5)
feat(linear_algebra/free_module): add class module.free ([#7801](https://github.com/leanprover-community/mathlib/pull/7801))
We introduce here a new class `module.free`.

### [2021-06-12 15:54:59](https://github.com/leanprover-community/mathlib/commit/f9935ed)
feat(geometry/manifold): Some lemmas for smooth functions ([#7752](https://github.com/leanprover-community/mathlib/pull/7752))

### [2021-06-12 11:10:11](https://github.com/leanprover-community/mathlib/commit/b7d4996)
chore(ring_theory/adjoin_root): speedup ([#7905](https://github.com/leanprover-community/mathlib/pull/7905))
Speedup a lemma that has just timed out in bors, by removing a heavy `change`.

### [2021-06-12 11:10:10](https://github.com/leanprover-community/mathlib/commit/15b2434)
chore(data/nat/sqrt): Alternative phrasings of data.nat.sqrt lemmas ([#7748](https://github.com/leanprover-community/mathlib/pull/7748))
Add versions of the `data.nat.sqrt` lemmas to talk about `n^2` where the current versions talk about `n * n`.

### [2021-06-12 11:10:09](https://github.com/leanprover-community/mathlib/commit/841dce1)
feat(data/polynomial): generalize `polynomial.has_scalar` to require only `distrib_mul_action` instead of `semimodule` ([#7664](https://github.com/leanprover-community/mathlib/pull/7664))
Note that by generalizing this instance, we introduce a diamond with `polynomial.mul_semiring_action`, which has a definitionally different `smul`. To resolve this, we add a proof that the definitions are equivalent, and switch `polynomial.mul_semiring_action` to use the same implementation as `polynomial.has_scalar`. This allows us to generalize `smul_C` to apply to all types of action, and remove `coeff_smul'` which then duplicates the statement of `coeff_smul`.

### [2021-06-12 08:06:06](https://github.com/leanprover-community/mathlib/commit/2016a93)
feat(linear_algebra): use `finset`s to define `det` and `trace` ([#7778](https://github.com/leanprover-community/mathlib/pull/7778))
This PR replaces `∃ (s : set M) (b : basis s R M), s.finite` with `∃ (s : finset M), nonempty (basis s R M)` in the definitions in `linear_map.det` and `linear_map.trace`. This should make it much easier to unfold those definitions without having to modify the instance cache or supply implicit params.
In particular, it should help a lot with [#7667](https://github.com/leanprover-community/mathlib/pull/7667).

### [2021-06-12 08:06:04](https://github.com/leanprover-community/mathlib/commit/dabb41f)
feat(tactic/{induction,fresh_names}): improve `induction' with` ([#7726](https://github.com/leanprover-community/mathlib/pull/7726))
This commit introduces two improvements to the `with` clauses of the `cases'`
and `induction'` tactics:
- Users can now write a hyphen instead of a name in the `with` clause. This
  clears the corresponding hypothesis (and any hypotheses depending on it).
- When users give an explicit name in the `with` clause, that name is now used
  verbatim, even if it shadows an existing hypothesis.

### [2021-06-12 02:38:03](https://github.com/leanprover-community/mathlib/commit/55c9662)
chore(scripts): update nolints.txt ([#7902](https://github.com/leanprover-community/mathlib/pull/7902))
I am happy to remove some nolints for you!

### [2021-06-12 02:38:02](https://github.com/leanprover-community/mathlib/commit/2974a9f)
feat(ring_theory): every division_ring is_noetherian ([#7661](https://github.com/leanprover-community/mathlib/pull/7661))

### [2021-06-12 02:38:01](https://github.com/leanprover-community/mathlib/commit/5948cde)
feat(ring_theory): the field trace resp. norm is the sum resp. product of the conjugates ([#7640](https://github.com/leanprover-community/mathlib/pull/7640))
More precise statement of the main result: the field trace (resp. norm) of `x` in `K(x) / K`, mapped to a field `F` that contains all the conjugate roots over `K` of `x`, is equal to the sum (resp. product) of all of these conjugate roots.

### [2021-06-12 02:38:00](https://github.com/leanprover-community/mathlib/commit/4337918)
feat(analysis/special_functions/integrals): integral of `sin x ^ m * cos x ^ n` ([#7418](https://github.com/leanprover-community/mathlib/pull/7418))
The simplification of integrals of the form `∫ x in a..b, sin x ^ m * cos x ^ n` where (i) `n` is odd, (ii) `m` is odd, and (iii) `m` and `n` are both even.
The computation of the integrals of the following functions are then provided outright:
- `sin x * cos x`, given both in terms of sine and cosine
- `sin x ^ 2 * cos x ^ 2`
- `sin x ^ 2 * cos x` and `sin x * cos x ^ 2`
- `sin x ^ 3` and `cos x ^ 3`

### [2021-06-12 02:37:59](https://github.com/leanprover-community/mathlib/commit/2d175ae)
feat(topology/category/Top/limits): Kőnig's lemma for fintypes ([#6288](https://github.com/leanprover-community/mathlib/pull/6288))
Specializes `Top.nonempty_limit_cone_of_compact_t2_inverse_system` to an inverse system of nonempty fintypes.

### [2021-06-11 21:18:49](https://github.com/leanprover-community/mathlib/commit/b360611)
chore(src/algebra/lie/abelian): golf ([#7898](https://github.com/leanprover-community/mathlib/pull/7898))
I golfed some of the proofs of the file `algebra/lie/abelian`.  My main motivation was to get familiar with the file.

### [2021-06-11 21:18:48](https://github.com/leanprover-community/mathlib/commit/dd60035)
chore(algebra/{covariant_and_contravariant + ordered_monoid_lemmas}): new file covariant_and_contravariant ([#7890](https://github.com/leanprover-community/mathlib/pull/7890))
This PR creates a new file `algebra/covariant_and_contravariant` and moves the part of `algebra/ordered_monoid_lemmas` dealing exclusively with `covariant` and `contravariant` into it.
It also rearranges the documentation, with a view to the later PRs, building up to [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
The discrepancy between the added and removed lines is entirely due to longer documentation: no actual Lean code has changed, except, of course, for the `import` in `algebra/ordered_monoid_lemmas` that now uses `covariant_and_contravariant`.

### [2021-06-11 21:18:47](https://github.com/leanprover-community/mathlib/commit/538f015)
feat(data/finset/basic): `empty_product` and `product_empty` ([#7886](https://github.com/leanprover-community/mathlib/pull/7886))
add `product_empty_<left/right>`

### [2021-06-11 21:18:46](https://github.com/leanprover-community/mathlib/commit/97a7a24)
doc(data/pequiv): add module docs ([#7877](https://github.com/leanprover-community/mathlib/pull/7877))

### [2021-06-11 21:18:45](https://github.com/leanprover-community/mathlib/commit/ff44ed5)
feat({algebra/group_action_hom, data/equiv/mul_add}): add missing `inverse` defs ([#7847](https://github.com/leanprover-community/mathlib/pull/7847))

### [2021-06-11 21:18:44](https://github.com/leanprover-community/mathlib/commit/a008b33)
feat(data/finsupp/to_dfinsupp): add sigma_finsupp_lequiv_dfinsupp ([#7818](https://github.com/leanprover-community/mathlib/pull/7818))
Equivalences between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`.
- [x] depends on: [#7819](https://github.com/leanprover-community/mathlib/pull/7819)

### [2021-06-11 21:18:43](https://github.com/leanprover-community/mathlib/commit/64d453e)
feat(ring_theory/adjoin/basic): add subalgebra.fg_prod ([#7811](https://github.com/leanprover-community/mathlib/pull/7811))
We add `subalgebra.fg_prod`: the product of two finitely generated subalgebras is finitely generated.
A mathematical remark: the result is not difficult, but one needs to be careful. For example, `algebra.adjoin_eq_prod` is false without adding `(1,0)` and `(0,1)` by hand to the set of generators. Moreover, `linear_map.inl` and `linear_map.inr` are not ring homomorphisms, so it seems difficult to mimic the proof for modules. A better mathematical proof is to take surjections from two polynomial rings (in finitely many variables) and considering the tensor product of these polynomial rings, that is again a polynomial ring in finitely many variables, and build a surjection to the product of the subalgebras (using the universal property of the tensor product). The problem with this approach is that one needs to know that the tensor product of polynomial rings is again a polynomial ring, and I don't know well enough the API fort the tensor product to prove this.

### [2021-06-11 21:18:42](https://github.com/leanprover-community/mathlib/commit/61a04c5)
feat(algebraic_geometry/structure_sheaf): Define comap on structure sheaf ([#7788](https://github.com/leanprover-community/mathlib/pull/7788))
Defines the comap of a ring homomorphism on the structure sheaves of the prime spectra.

### [2021-06-11 21:18:40](https://github.com/leanprover-community/mathlib/commit/eb9bd55)
feat(linear_algebra/quadratic_form): Real version of Sylvester's law of inertia ([#7427](https://github.com/leanprover-community/mathlib/pull/7427))
We prove that every nondegenerate real quadratic form is equivalent to a weighted sum of squares with the weights being ±1.

### [2021-06-11 13:26:19](https://github.com/leanprover-community/mathlib/commit/e8add82)
chore(algebra/{ordered_monoid,linear_ordered_comm_group_with_zero}): remove some uses of @ ([#7884](https://github.com/leanprover-community/mathlib/pull/7884))
This PR replaces a couple of uses of `@` with slightly more verbose proofs that only use the given explicit arguments.
The `by apply mul_lt_mul''' hab0 hcd0` line also works with `mul_lt_mul''' hab0 hcd0` alone (at least on my machine).  The reason for the slightly more elaborate proof is that once the typeclass assumptions will change, the direct term-mode proof will break, while the `by apply` version is more stable.
Besides its aesthetic value, this is useful in PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645), as the typeclass arguments of the involved lemmas will change and this will keep the diff (slightly) shorter.

### [2021-06-11 13:26:18](https://github.com/leanprover-community/mathlib/commit/9500d95)
feat(number_theory/l_series): The L-series of an arithmetic function ([#7862](https://github.com/leanprover-community/mathlib/pull/7862))
Defines the L-series of an arithmetic function
Proves a few basic facts about convergence of L-series

### [2021-06-11 13:26:17](https://github.com/leanprover-community/mathlib/commit/e35438b)
feat(analysis): Cauchy sequence and series lemmas ([#7858](https://github.com/leanprover-community/mathlib/pull/7858))
from LTE. Mostly relaxing assumptions from metric to
pseudo-metric and proving some obvious lemmas.
eventually_constant_prod and eventually_constant_sum are duplicated by hand because `to_additive` gets confused by the appearance of `1`.
In `norm_le_zero_iff' {G : Type*} [semi_normed_group G] [separated_space G]` and the following two lemmas the type classes assumptions look silly, but those lemmas are indeed useful in some specific situation in LTE.

### [2021-06-11 13:26:16](https://github.com/leanprover-community/mathlib/commit/a421185)
feat(algebra/periodic): more periodicity lemmas ([#7853](https://github.com/leanprover-community/mathlib/pull/7853))

### [2021-06-11 13:26:15](https://github.com/leanprover-community/mathlib/commit/9228ff9)
feat(algebra/ordered_group): abs_sub ([#7850](https://github.com/leanprover-community/mathlib/pull/7850))
- rename `abs_sub` to `abs_sub_comm`
- prove `abs_sub`

### [2021-06-11 13:26:14](https://github.com/leanprover-community/mathlib/commit/4bfe8e8)
feat(algebra/order_functions): lt_max_of_lt_<left/right> ([#7849](https://github.com/leanprover-community/mathlib/pull/7849))

### [2021-06-11 13:26:12](https://github.com/leanprover-community/mathlib/commit/915a0a2)
feat(topology/algebra/ordered/basic): add a few subseq-related lemmas ([#7828](https://github.com/leanprover-community/mathlib/pull/7828))
These are lemmas I proved while working on [#7164](https://github.com/leanprover-community/mathlib/pull/7164). Some of them are actually not used anymore in that PR because I'm refactoring it, but I thought they would be useful anyway, so here there are.

### [2021-06-11 12:07:55](https://github.com/leanprover-community/mathlib/commit/51cd821)
chore(algebra/lie/classical): speed up slow proof ([#7894](https://github.com/leanprover-community/mathlib/pull/7894))
Squeeze a simp in a proof that has just timed out on bors

### [2021-06-11 02:16:14](https://github.com/leanprover-community/mathlib/commit/6eb3d97)
chore(scripts): update nolints.txt ([#7887](https://github.com/leanprover-community/mathlib/pull/7887))
I am happy to remove some nolints for you!

### [2021-06-11 02:16:13](https://github.com/leanprover-community/mathlib/commit/6f6dbad)
feat(set_theory/cardinal): missing lemma ([#7880](https://github.com/leanprover-community/mathlib/pull/7880))

### [2021-06-11 02:16:12](https://github.com/leanprover-community/mathlib/commit/e8aa984)
doc(int/modeq): add module doc and tidy ([#7878](https://github.com/leanprover-community/mathlib/pull/7878))

### [2021-06-11 02:16:11](https://github.com/leanprover-community/mathlib/commit/1b0e5ee)
chore(data/real/nnreal): avoid abusing inequalities in nnreals ([#7872](https://github.com/leanprover-community/mathlib/pull/7872))
I removed the use of `@`, so that all implicit arguments stay implicit.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645): by only having the explicit arguments, the same proof works, without having to fiddle around with underscores.

### [2021-06-11 02:16:10](https://github.com/leanprover-community/mathlib/commit/d570596)
feat(logic/function/basic): a lemma on symmetric operations and flip ([#7871](https://github.com/leanprover-community/mathlib/pull/7871))
This lemma is used to show that if multiplication is commutative, then `flip`ping the arguments returns the same function.
This is used in PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) .

### [2021-06-11 02:16:09](https://github.com/leanprover-community/mathlib/commit/9a4881d)
chore(data/real/pi, analysis/special_functions/trigonometric.lean): speed up/simplify proofs ([#7868](https://github.com/leanprover-community/mathlib/pull/7868))
These are mostly cosmetic changes, simplifying a couple of proofs.  I tried to remove the calls to `linarith` or `norm_num`, when the alternatives were either single lemmas or faster than automation.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-11 02:16:08](https://github.com/leanprover-community/mathlib/commit/f157a37)
chore(logic/basic): fixup `eq_or_ne` ([#7865](https://github.com/leanprover-community/mathlib/pull/7865))

### [2021-06-11 02:16:07](https://github.com/leanprover-community/mathlib/commit/0a80efb)
chore(analysis/normed_space/normed_group_hom): remove bound_by ([#7860](https://github.com/leanprover-community/mathlib/pull/7860))
`bound_by f C` is the same as `∥f∥ ≤ C` and it is therefore useless now that we have `∥f∥`.

### [2021-06-10 16:03:39](https://github.com/leanprover-community/mathlib/commit/0f8e79e)
feat(algebra/big_operators/finsupp): relax assumptions `semiring` to `non_unital_non_assoc_semiring` ([#7874](https://github.com/leanprover-community/mathlib/pull/7874))

### [2021-06-10 16:03:38](https://github.com/leanprover-community/mathlib/commit/3b5a44b)
chore(src/testing/slim_check/sampleable): simply add explicit namespace `nat.` ([#7873](https://github.com/leanprover-community/mathlib/pull/7873))
This PR only introduces the explicit namespace `nat.` when calling `le_div_iff_mul_le`.  The reason for doing this is that PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) introduces a lemma `le_div_iff_mul_le` in the root namespace and this one then becomes ambiguous.  Note that CI *does build* on this branch even without the explicit namespace.  The change would only become necessary once/if PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) gets merged.
I isolated this change to a separate PR to reduce the diff of [#7645](https://github.com/leanprover-community/mathlib/pull/7645) and also to bring attention to this issue, in case someone has some comment about it.

### [2021-06-10 16:03:37](https://github.com/leanprover-community/mathlib/commit/2e8ef55)
feat(algebra/floor): nat_floor ([#7855](https://github.com/leanprover-community/mathlib/pull/7855))
introduce `nat_floor`
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/nat_floor

### [2021-06-10 16:03:36](https://github.com/leanprover-community/mathlib/commit/021c859)
feat(analysis/special_functions/pow): rpow-log inequalities ([#7848](https://github.com/leanprover-community/mathlib/pull/7848))
Inequalities relating rpow and log

### [2021-06-10 16:03:35](https://github.com/leanprover-community/mathlib/commit/49f5a15)
feat(algebra/ordered_ring): more granular typeclasses for `with_top α` and `with_bot α` ([#7845](https://github.com/leanprover-community/mathlib/pull/7845))
`with_top α` and `with_bot α` now inherit the following typeclasses from `α` with suitable assumptions:
* `mul_zero_one_class`
* `semigroup_with_zero`
* `monoid_with_zero`
* `comm_monoid_with_zero`
These were all split out of the existing `canonically_ordered_comm_semiring`, with their proofs unchanged.
The same instances are added for `with_bot`.
It is not possible to split further, as `distrib'` requires `add_eq_zero_iff`, and `canonically_ordered_comm_semiring` is the smallest typeclass that provides both this lemma and `mul_zero_class`.
With these instances in place, we can now show `comm_monoid_with_zero ereal`.

### [2021-06-10 23:57:20+10:00](https://github.com/leanprover-community/mathlib/commit/079b8a1)
Revert "feat(set_theory/cofinality): more infinite pigeonhole principles"
This reverts commit c7ba50f41813718472478983370db66b06c2d33e.

### [2021-06-10 23:56:13+10:00](https://github.com/leanprover-community/mathlib/commit/c7ba50f)
feat(set_theory/cofinality): more infinite pigeonhole principles

### [2021-06-10 06:56:02](https://github.com/leanprover-community/mathlib/commit/f7e93d9)
chore(algebra/linear_ordered_comm_group_with_zero.lean): extend calc proofs ([#7870](https://github.com/leanprover-community/mathlib/pull/7870))
These are mostly cosmetic changes, simplifying a couple of calc proofs.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-10 06:56:01](https://github.com/leanprover-community/mathlib/commit/05b7b0b)
chore(scripts): update nolints.txt ([#7867](https://github.com/leanprover-community/mathlib/pull/7867))
I am happy to remove some nolints for you!

### [2021-06-10 06:56:00](https://github.com/leanprover-community/mathlib/commit/4da899c)
chore(number_theory/{fermat4, sum_four_squares, zsqrtd/basic}): simplify/rearrange proofs ([#7866](https://github.com/leanprover-community/mathlib/pull/7866))
These are mostly cosmetic changes, simplifying a couple of proofs.  I would have tagged it `easy`, but since there are three files changed, it may take just over 20'' to review!
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-10 01:51:29](https://github.com/leanprover-community/mathlib/commit/2fc66c9)
feat(algebra/group_with_zero): add units.can_lift ([#7857](https://github.com/leanprover-community/mathlib/pull/7857))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/projective.20space/near/242041169)

### [2021-06-10 01:51:28](https://github.com/leanprover-community/mathlib/commit/0a34878)
chore(topology/algebra/continuous_functions): making names consistent with the smooth library ([#7844](https://github.com/leanprover-community/mathlib/pull/7844))

### [2021-06-10 01:51:26](https://github.com/leanprover-community/mathlib/commit/06200c8)
feat(ring_theory/ideal): generalize to noncommutative rings ([#7654](https://github.com/leanprover-community/mathlib/pull/7654))
This is a minimalist generalization of existing material on ideals to the setting of noncommutative rings.
I have not attempted to decide how things should be named in the long run. For now `ideal` specifically means a left-ideal (i.e. I didn't change the definition). We can either in future add `two_sided_ideal` (or `biideal` or `ideal₂` or ...), or potentially rename `ideal` to `left_ideal` or `lideal`, etc. Future bikeshedding opportunities!
In this PR I've just left definitions alone, and relaxed `comm_ring` hypotheses to `ring` as far as I could see possible. No new theorems or mathematics, just rearranging to get things in the right order.
(As a side note, both `ring_theory.ideal.basic` and `ring_theory.ideal.operations` should be split into smaller files; I can try this after this PR.)

### [2021-06-09 20:42:50](https://github.com/leanprover-community/mathlib/commit/3870896)
doc(data/semiquot): reformat module doc properly, and add missing doc strings ([#7773](https://github.com/leanprover-community/mathlib/pull/7773))

### [2021-06-09 20:42:48](https://github.com/leanprover-community/mathlib/commit/abe25e9)
docs(data/mllist): fix module doc, and add all doc strings ([#7772](https://github.com/leanprover-community/mathlib/pull/7772))

### [2021-06-09 20:42:47](https://github.com/leanprover-community/mathlib/commit/d9b91f3)
feat(measure_theory/tactic): add measurability tactic ([#7756](https://github.com/leanprover-community/mathlib/pull/7756))
Add a measurability tactic defined in the file `measure_theory/tactic.lean`, which is heavily inspired from the continuity tactic. It proves goals of the form `measurable f`, `ae_measurable f µ` and `measurable_set s`. Some tests are provided in `tests/measurability.lean` and the tactic was used to replace a few lines in `integration.lean` and `mean_inequalities.lean`.

### [2021-06-09 15:40:05](https://github.com/leanprover-community/mathlib/commit/8e25717)
chore(geometry/euclidean/circumcenter): remove two `have`s in a proof ([#7852](https://github.com/leanprover-community/mathlib/pull/7852))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/circumcenter

### [2021-06-09 15:40:04](https://github.com/leanprover-community/mathlib/commit/d0ed2a4)
chore(measure_theory/set_integral): put the definition of integrable_on into a new file ([#7842](https://github.com/leanprover-community/mathlib/pull/7842))
The file `measure_theory.set_integral` is split into two: the `integrable_on` predicate is put into its own file, which does not import  `measure_theory.bochner_integration` (this puts the definition of that integrability property before the definition of the actual integral). The file `measure_theory.set_integral` retains all facts about `set_integral`.

### [2021-06-09 15:40:02](https://github.com/leanprover-community/mathlib/commit/764e878)
feat(algebra/ordered_group): `-abs a ≤ a` ([#7839](https://github.com/leanprover-community/mathlib/pull/7839))

### [2021-06-09 15:40:01](https://github.com/leanprover-community/mathlib/commit/a9d4f3d)
fix(*): make some non-instances reducible ([#7835](https://github.com/leanprover-community/mathlib/pull/7835))
* Definitions that involve in instances might need to be reducible, see added library note. 
* This involves the definitions `*order.lift` / `function.injective.*` and `function.surjective.*` 
* This came up in [#7645](https://github.com/leanprover-community/mathlib/pull/7645).

### [2021-06-09 15:40:00](https://github.com/leanprover-community/mathlib/commit/20efef7)
chore(algebra/field_power, data/set/intervals/basic): simpler proofs in the first file, fewer parentheses in the second one ([#7831](https://github.com/leanprover-community/mathlib/pull/7831))
This is mostly a cosmetic PR: I removed two calls to `linarith`, where a term-mode proof was very simple.
I also removed some unnecessary parentheses in a different file.

### [2021-06-09 15:39:59](https://github.com/leanprover-community/mathlib/commit/02d5370)
chore(measure_theory/outer_measure): add extend_eq_top ([#7827](https://github.com/leanprover-community/mathlib/pull/7827))

### [2021-06-09 15:39:58](https://github.com/leanprover-community/mathlib/commit/fa7c6da)
docs(order/bounded_lattice): add module docstring ([#7799](https://github.com/leanprover-community/mathlib/pull/7799))
add module docstring and some sectioning

### [2021-06-09 10:12:47](https://github.com/leanprover-community/mathlib/commit/55abf1a)
chore(scripts): update nolints.txt ([#7851](https://github.com/leanprover-community/mathlib/pull/7851))
I am happy to remove some nolints for you!

### [2021-06-09 10:12:46](https://github.com/leanprover-community/mathlib/commit/8676685)
feat(ring_theory): every left-noetherian ring satisfies the strong rank condition ([#7711](https://github.com/leanprover-community/mathlib/pull/7711))
This PR also discards the proof that every left-noetherian ring satisfies the rank condition, because we already have in [#7683](https://github.com/leanprover-community/mathlib/pull/7683) that this implies that.

### [2021-06-09 10:12:45](https://github.com/leanprover-community/mathlib/commit/47ad680)
feat(measure_theory/interval_integral): integration by substitution / change of variables ([#7273](https://github.com/leanprover-community/mathlib/pull/7273))
Given that `f` has a derivative at `f'` everywhere on `interval a b`,
`∫ x in a..b, (g ∘ f) x * f' x = ∫ x in f a..f b, g x`.
Co-authored by @ADedecker

### [2021-06-09 06:11:41](https://github.com/leanprover-community/mathlib/commit/faa58e5)
refactor(algebra/module/projective) make is_projective a class ([#7830](https://github.com/leanprover-community/mathlib/pull/7830))
Make `is_projective` a class.

### [2021-06-09 06:11:39](https://github.com/leanprover-community/mathlib/commit/c210d0f)
feat(topology/category/limits): Topological bases in cofiltered limits ([#7820](https://github.com/leanprover-community/mathlib/pull/7820))
This PR proves a theorem which provides a simple characterization of certain topological bases in a cofiltered limit of topological spaces.
Eventually I will specialize this assertion to the case where the topological spaces are profinite, and the `T i` are the topological bases given by clopen sets.
This generalizes a lemma from LTE.

### [2021-06-09 06:11:38](https://github.com/leanprover-community/mathlib/commit/34c433d)
feat(data/finsupp): generalize finsupp.has_scalar to require only distrib_mul_action instead of semimodule ([#7819](https://github.com/leanprover-community/mathlib/pull/7819))
This propagates the generalization to (add_)monoid_algebra and mv_polynomial.

### [2021-06-09 06:11:37](https://github.com/leanprover-community/mathlib/commit/393f638)
feat(ring_theory/localization): Make local_ring_hom more flexible ([#7787](https://github.com/leanprover-community/mathlib/pull/7787))
Make `localization.local_ring_hom` more flexible, by allowing two ideals `I` and `J` as arguments, with the assumption that `I` equals `ideal.comap f J`. Also add lemmas about identity and composition.

### [2021-06-08 19:13:24](https://github.com/leanprover-community/mathlib/commit/5c6d3bc)
feat(topology/instances/ereal): more on ereal, notably its topology ([#7765](https://github.com/leanprover-community/mathlib/pull/7765))

### [2021-06-08 19:13:23](https://github.com/leanprover-community/mathlib/commit/75c81de)
feat(measure_theory/integration): a measurable function is a series of simple functions ([#7764](https://github.com/leanprover-community/mathlib/pull/7764))

### [2021-06-08 19:13:22](https://github.com/leanprover-community/mathlib/commit/39406bb)
feat(model_theory/basic): First-order languages, structures, homomorphisms, embeddings, and equivs ([#7754](https://github.com/leanprover-community/mathlib/pull/7754))
Defines the following notions from first-order logic:
- languages
- structures
- homomorphisms
- embeddings
- equivalences (isomorphisms)
The definitions of languages and structures take inspiration from the Flypitch project.

### [2021-06-08 06:35:33](https://github.com/leanprover-community/mathlib/commit/42c4237)
chore(mv_polynomial/equiv): speed up elaboration by adjusting priorities ([#7840](https://github.com/leanprover-community/mathlib/pull/7840))
`option_equiv_left` timed out several times in bors, since the introduction of non-unital rings. We fix this by adjusting the priority to make sure that the problematic instance is found right away.
Also speed up circumcenter file (which also just timed out in bors) by squeezing simps.

### [2021-06-07 15:40:25](https://github.com/leanprover-community/mathlib/commit/320da57)
chore(data/fintype/basic): add fintype instance for `is_empty` ([#7692](https://github.com/leanprover-community/mathlib/pull/7692))

### [2021-06-07 15:40:24](https://github.com/leanprover-community/mathlib/commit/6e67536)
feat(category/limits): kernel.map ([#7623](https://github.com/leanprover-community/mathlib/pull/7623))
A generalization of a lemma from LTE, stated for a category with (co)kernels.

### [2021-06-07 15:40:23](https://github.com/leanprover-community/mathlib/commit/fb72599)
feat(algebra/periodic): define periodicity ([#7572](https://github.com/leanprover-community/mathlib/pull/7572))
This PR introduces a general notion of periodicity. It also includes proofs of the "usual" properties of periodic (and antiperiodic) functions.

### [2021-06-07 15:40:22](https://github.com/leanprover-community/mathlib/commit/e55d470)
feat(specific_groups/alternating_group): The alternating group on 5 elements is simple ([#7502](https://github.com/leanprover-community/mathlib/pull/7502))
Shows that `is_simple_group (alternating_group (fin 5))`

### [2021-06-07 15:40:20](https://github.com/leanprover-community/mathlib/commit/fa7b5f2)
feat(linear_algebra/quadratic_form): Complex version of Sylvester's law of inertia ([#7416](https://github.com/leanprover-community/mathlib/pull/7416))
Every nondegenerate complex quadratic form is equivalent to a quadratic form corresponding to the sum of squares.

### [2021-06-07 15:40:19](https://github.com/leanprover-community/mathlib/commit/ef7aa94)
feat(algebra/ring/basic): define non-unital, non-associative rings ([#6786](https://github.com/leanprover-community/mathlib/pull/6786))
This introduces the following typeclasses beneath `semiring`:
  * `non_unital_non_assoc_semiring`
  * `non_unital_semiring`
  * `non_assoc_semiring`
The goal is to use these to support a non-unital, non-associative
algebras.
The typeclass requirements of `subring`, `subsemiring`, and `ring_hom` are relaxed from `semiring` to `non_assoc_semiring`.
Instances of these new typeclasses are added for:
* alias types:
  * `opposite`
  * `ulift`
* convolutive types:
  * `(add_)monoid_algebra`
  * `direct_sum`
  * `set_semiring`
  * `hahn_series`
* elementwise types: 
  * `locally_constant`
  * `pi`
  * `prod`
  * `finsupp`

### [2021-06-07 15:40:18](https://github.com/leanprover-community/mathlib/commit/1eb3ae4)
feat(order/symm_diff): symmetric difference operator ([#6469](https://github.com/leanprover-community/mathlib/pull/6469))

### [2021-06-07 07:44:02](https://github.com/leanprover-community/mathlib/commit/136e0d6)
feat(data/fintype/basic): The cardinality of a set is at most the cardinality of the universe ([#7823](https://github.com/leanprover-community/mathlib/pull/7823))
I think that the hypothesis `[fintype ↥s]` can be avoided with the use of classical logic. E.g.,
`noncomputable instance set_fintype' {α : Type*} [fintype α] (s : set α) : fintype s :=by { classical, exact set_fintype s }`
Would it make sense to add this?

### [2021-06-07 07:44:01](https://github.com/leanprover-community/mathlib/commit/4f38062)
feat(algebra/lie/base_change): define extension and restriction of scalars for Lie algebras ([#7808](https://github.com/leanprover-community/mathlib/pull/7808))

### [2021-06-07 07:44:00](https://github.com/leanprover-community/mathlib/commit/f57f9c8)
feat(ring_theory): define the field/algebra norm ([#7636](https://github.com/leanprover-community/mathlib/pull/7636))
This PR defines the field norm `algebra.norm K L : L →* K`, where `L` is a finite field extension of `K`. In fact, it defines this for any `algebra R S` instance, where `R` and `S` are integral domains. (With a default value of `1` if `S` does not have a finite `R`-basis.)
The approach is to basically copy `ring_theory/trace.lean` and replace `trace` with `det` or `norm` as appropriate.

### [2021-06-07 04:52:49](https://github.com/leanprover-community/mathlib/commit/61ca31a)
chore(scripts): update nolints.txt ([#7829](https://github.com/leanprover-community/mathlib/pull/7829))
I am happy to remove some nolints for you!

### [2021-06-07 04:52:49](https://github.com/leanprover-community/mathlib/commit/7a21ae1)
chore(algebra/algebra/subalgebra): make inf and top definitionally convenient ([#7812](https://github.com/leanprover-community/mathlib/pull/7812))
This adjusts the galois insertion such that `lemma coe_inf (S T : subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl`.
It also adds lots of trivial `simp` lemmas that were missing about the interactions of various coercions and lattice operations.

### [2021-06-07 01:12:38](https://github.com/leanprover-community/mathlib/commit/685289c)
feat(algebra/pointwise): pow_mem_pow ([#7822](https://github.com/leanprover-community/mathlib/pull/7822))
If `a ∈ s` then `a ^ n ∈ s ^ n`.

### [2021-06-07 01:12:37](https://github.com/leanprover-community/mathlib/commit/29d0c63)
feat(measure_theory): add a few integration-related lemmas ([#7821](https://github.com/leanprover-community/mathlib/pull/7821))
These are lemmas I proved while working on [#7164](https://github.com/leanprover-community/mathlib/pull/7164). Some of them are actually not used anymore in that PR because I'm refactoring it, but I thought they would be useful anyway, so here there are.

### [2021-06-07 01:12:36](https://github.com/leanprover-community/mathlib/commit/ef7c335)
fix(data/mv_polynomial): add missing decidable arguments ([#7817](https://github.com/leanprover-community/mathlib/pull/7817))
This:
* fixes a doubled instance name, `finsupp.finsupp.decidable_eq`. Note the linter deliberate ignores instances, as they are often autogenerated
* generalizes `finsupp.decidable_le` to all canonically_ordered_monoids
* adds missing `decidable_eq` arguments to `mv_polynomial` and `mv_power_series` lemmas whose statement contains an `if`. These might in future be lintable.
* adds some missing lemmas about `mv_polynomial` to clean up a few proofs.

### [2021-06-07 01:12:35](https://github.com/leanprover-community/mathlib/commit/90ae36e)
docs(order/order_iso_nat): add module docstring ([#7804](https://github.com/leanprover-community/mathlib/pull/7804))
add module docstring

### [2021-06-06 19:30:18](https://github.com/leanprover-community/mathlib/commit/4c8a627)
docs(order/directed): add module docstring ([#7779](https://github.com/leanprover-community/mathlib/pull/7779))
add module docstring

### [2021-06-06 03:28:07](https://github.com/leanprover-community/mathlib/commit/e3f897c)
feat(algebra/char_p): characteristic of fraction_ring ([#7703](https://github.com/leanprover-community/mathlib/pull/7703))
Adding the characteristics of a `fraction_ring` for an integral domain.

### [2021-06-06 03:28:06](https://github.com/leanprover-community/mathlib/commit/ba2c056)
feat(data/list/nodup): nodup.pairwise_of_forall_ne ([#7587](https://github.com/leanprover-community/mathlib/pull/7587))

### [2021-06-05 09:09:15](https://github.com/leanprover-community/mathlib/commit/7021ff9)
feat(linear_algebra/basis): use is_empty instead of ¬nonempty ([#7815](https://github.com/leanprover-community/mathlib/pull/7815))
This removes the need for `basis.of_dim_eq_zero'` and `basis_of_finrank_zero'`, as these special cases are now covered by the unprimed versions and typeclass search.

### [2021-06-04 19:29:36](https://github.com/leanprover-community/mathlib/commit/a4ae4ad)
chore(order/(bounded,modular)_lattice): avoid classical.some in `is_complemented` instances ([#7814](https://github.com/leanprover-community/mathlib/pull/7814))
There's no reason to use it here.

### [2021-06-04 19:29:35](https://github.com/leanprover-community/mathlib/commit/8b5ff9c)
feat(analysis/special_functions/integrals): `integral_log` ([#7732](https://github.com/leanprover-community/mathlib/pull/7732))
The integral of the (real) logarithmic function over the interval `[a, b]`, provided that `0 ∉ interval a b`.

### [2021-06-04 16:08:36](https://github.com/leanprover-community/mathlib/commit/0b09858)
feat(linear_algebra/basic): add a unique instance for linear_equiv ([#7816](https://github.com/leanprover-community/mathlib/pull/7816))

### [2021-06-04 13:25:42](https://github.com/leanprover-community/mathlib/commit/65e3b04)
feat(linear_algebra/determinant): various `basis.det` lemmas ([#7669](https://github.com/leanprover-community/mathlib/pull/7669))
A selection of results that I needed for computing the value of `basis.det`.

### [2021-06-04 09:53:02](https://github.com/leanprover-community/mathlib/commit/1a62bb4)
feat(linear_algebra): strong rank condition implies rank condition ([#7683](https://github.com/leanprover-community/mathlib/pull/7683))

### [2021-06-04 03:56:15](https://github.com/leanprover-community/mathlib/commit/be183e2)
chore(data/finset|multiset|finsupp): reduce algebra/ imports ([#7797](https://github.com/leanprover-community/mathlib/pull/7797))

### [2021-06-03 23:23:09](https://github.com/leanprover-community/mathlib/commit/89928bc)
feat(topology): A locally compact Hausdorff space is totally disconnected if and only if it is totally separated ([#7649](https://github.com/leanprover-community/mathlib/pull/7649))
We prove that a locally compact Hausdorff space is totally disconnected if and only if it is totally separated.

### [2021-06-03 16:15:32](https://github.com/leanprover-community/mathlib/commit/685adb0)
fix(tactic/lint): allow pattern def ([#7785](https://github.com/leanprover-community/mathlib/pull/7785))
`Prop` sorted declarations are allowed to be `def` if they have the `@[pattern]` attribute

### [2021-06-03 16:15:31](https://github.com/leanprover-community/mathlib/commit/fa51468)
feat(tactic/lift): elaborate proof with the expected type ([#7739](https://github.com/leanprover-community/mathlib/pull/7739))
* also slightly refactor the corresponding function a bit
* add some tests
* move all tests to `tests/lift.lean`

### [2021-06-03 16:15:30](https://github.com/leanprover-community/mathlib/commit/05f7e8d)
feat(linear_algebra/tensor_product): define `tensor_tensor_tensor_comm` ([#7724](https://github.com/leanprover-community/mathlib/pull/7724))
The intended application is defining the bracket structure when extending the scalars of a Lie algebra.

### [2021-06-03 11:07:26](https://github.com/leanprover-community/mathlib/commit/62655a2)
chore(data/dfinsupp): add the simp lemma coe_pre_mk ([#7806](https://github.com/leanprover-community/mathlib/pull/7806))

### [2021-06-03 11:07:25](https://github.com/leanprover-community/mathlib/commit/2a93644)
chore(src/linear_algebra/free_module): rename file to free_module_pid ([#7805](https://github.com/leanprover-community/mathlib/pull/7805))
In preparation for [#7801](https://github.com/leanprover-community/mathlib/pull/7801)

### [2021-06-03 11:07:24](https://github.com/leanprover-community/mathlib/commit/fc6f967)
chore(ring_theory/hahn_series): emb_domain_add needs only add_monoid, not semiring ([#7802](https://github.com/leanprover-community/mathlib/pull/7802))
This is my fault, the lemma ended up in the wrong place in [#7737](https://github.com/leanprover-community/mathlib/pull/7737)

### [2021-06-03 11:07:23](https://github.com/leanprover-community/mathlib/commit/54d8b94)
chore(logic/basic): add simp lemmas about exist_unique to match those about exists ([#7784](https://github.com/leanprover-community/mathlib/pull/7784))
Adds:
* `exists_unique_const` to match `exists_const` (provable by simp)
* `exists_unique_prop` to match `exists_prop` (provable by simp)
* `exists_unique_prop_of_true` to match `exists_prop_of_true`

### [2021-06-03 11:07:21](https://github.com/leanprover-community/mathlib/commit/ef13938)
feat(ring_theory/tensor_product): the base change of a linear map along an algebra ([#4773](https://github.com/leanprover-community/mathlib/pull/4773))

### [2021-06-03 07:38:39](https://github.com/leanprover-community/mathlib/commit/b806fd4)
chore(scripts): update nolints.txt ([#7810](https://github.com/leanprover-community/mathlib/pull/7810))
I am happy to remove some nolints for you!

### [2021-06-03 07:38:38](https://github.com/leanprover-community/mathlib/commit/36decf5)
chore(topology/bases): Rename + unprotect some lemmas ([#7809](https://github.com/leanprover-community/mathlib/pull/7809))
@PatrickMassot Unfortunately I saw your comments after [#7753](https://github.com/leanprover-community/mathlib/pull/7753) was already merged, so here is a followup PR with the changes you requested. I also unprotected and renamed `is_topological_basis_pi` and `is_topological_basis_infi` since dot notation will also not work for those.

### [2021-06-03 07:38:37](https://github.com/leanprover-community/mathlib/commit/8422d8c)
chore(data/padics): move padics to number_theory/ ([#7771](https://github.com/leanprover-community/mathlib/pull/7771))
Per [zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics).

### [2021-06-03 07:38:36](https://github.com/leanprover-community/mathlib/commit/adae1ad)
feat(order/filter/archimedean): in an archimedean linear ordered ring, `at_top` and `at_bot` are countably generated ([#7751](https://github.com/leanprover-community/mathlib/pull/7751))

### [2021-06-03 07:38:35](https://github.com/leanprover-community/mathlib/commit/6d85ff2)
refactor(linear_algebra/finsupp): replace mem_span_iff_total ([#7735](https://github.com/leanprover-community/mathlib/pull/7735))
This PR renames the existing `mem_span_iff_total` to `mem_span_image_iff_total` and the existing `span_eq_map_total` to `span_image_eq_map_total`, and replaces them with slightly simpler lemmas about sets in the module, rather than indexed families.
As usual in the linear algebra library, there is tension between using sets and using indexed families, but as `span` is defined in terms of sets I think the new lemmas merit taking the simpler names.

### [2021-06-03 07:38:33](https://github.com/leanprover-community/mathlib/commit/6d90d35)
feat(analysis/fourier): monomials on the circle are orthonormal ([#6952](https://github.com/leanprover-community/mathlib/pull/6952))
Make the circle into a measure space, using Haar measure, and prove that the monomials `z ^ n` are orthonormal when considered as elements of L^2 on the circle.

### [2021-06-03 04:58:21](https://github.com/leanprover-community/mathlib/commit/4b31247)
chore(data/*/gcd): move data/*set/gcd to algebra/gcd_monoid/ ([#7800](https://github.com/leanprover-community/mathlib/pull/7800))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).

### [2021-06-03 04:58:20](https://github.com/leanprover-community/mathlib/commit/e591543)
chore(data/zsqrtd): move to number_theory/ ([#7796](https://github.com/leanprover-community/mathlib/pull/7796))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).

### [2021-06-03 04:58:19](https://github.com/leanprover-community/mathlib/commit/ce3ca59)
chore(data/fincard): move to set_theory/ ([#7795](https://github.com/leanprover-community/mathlib/pull/7795))
This is about cardinals, so probably belongs in `set_theory/` not `data/`. (It's also a leaf node for now, so easy to move.)

### [2021-06-02 23:53:40](https://github.com/leanprover-community/mathlib/commit/d5a635b)
chore(data/hash_map): remove duplicate imports ([#7794](https://github.com/leanprover-community/mathlib/pull/7794))

### [2021-06-02 23:53:39](https://github.com/leanprover-community/mathlib/commit/a36560c)
chore(data/quaternion): move to algebra/ ([#7793](https://github.com/leanprover-community/mathlib/pull/7793))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).

### [2021-06-02 23:53:38](https://github.com/leanprover-community/mathlib/commit/7e3e883)
chore(data/equiv): add docstrings ([#7704](https://github.com/leanprover-community/mathlib/pull/7704))
- add module docstrings
- add def docstrings
- rename `decode2` to `decode₂`
- squash some simps

### [2021-06-02 23:53:37](https://github.com/leanprover-community/mathlib/commit/29d0a4e)
feat(tactic/lint): add linter that type-checks statements  ([#7694](https://github.com/leanprover-community/mathlib/pull/7694))
* Add linter that type-checks the statements of all declarations with the default reducibility settings. A statement might not type-check if locally a declaration was made not `@[irreducible]` while globally it is.
* Fix an issue where  `with_one.monoid.to_mul_one_class` did not unify with `with_one.mul_one_class`.
* Fix some proofs in `category_theory.opposites` so that they work while keeping `quiver.opposite` irreducible.

### [2021-06-02 18:23:20](https://github.com/leanprover-community/mathlib/commit/6e5899d)
feat(measure_theory/integration): add a version of the monotone convergence theorem using `tendsto` ([#7791](https://github.com/leanprover-community/mathlib/pull/7791))

### [2021-06-02 18:23:19](https://github.com/leanprover-community/mathlib/commit/82bc3ca)
chore(logic/small): reduce imports ([#7777](https://github.com/leanprover-community/mathlib/pull/7777))
By delaying the `fintype` and `encodable` instances for `small`, I think we can now avoid importing `algebra` at all into `logic`.
~~Since some of the `is_empty` lemmas haven't been used yet,~~ I took the liberty of making some arguments explicit, as one was painful to use as is.

### [2021-06-02 18:23:18](https://github.com/leanprover-community/mathlib/commit/47dbdac)
chore(data/support): move data/(support|indicator_function) to algebra/ ([#7774](https://github.com/leanprover-community/mathlib/pull/7774))
These don't define any new structures, have not much to do with programming, and are just about basic features of algebraic gadgets, so belong better in `algebra/` than `data/`. 
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).

### [2021-06-02 13:27:48](https://github.com/leanprover-community/mathlib/commit/173bc4c)
feat(algebra/algebra/subalgebra): add subalgebra.prod ([#7782](https://github.com/leanprover-community/mathlib/pull/7782))
We add a basic API for product of subalgebras.

### [2021-06-02 10:33:05](https://github.com/leanprover-community/mathlib/commit/b231c92)
doc(data/finsupp/pointwise): update old module doc ([#7770](https://github.com/leanprover-community/mathlib/pull/7770))

### [2021-06-02 10:33:04](https://github.com/leanprover-community/mathlib/commit/b91cdb9)
refactor(data/nnreal): rename nnreal.of_real to real.to_nnreal ([#7750](https://github.com/leanprover-community/mathlib/pull/7750))
I am in the middle of a project involving reals, nnreals, ennreals and ereals. There is a maze of coercions and maps between the 4 of them, with completely incoherent naming scheme (do you think that `measurable.nnreal_coe` is speaking of the coercion from `nnreal` to `real` or to `ennreal`, or of a coercion into `nnreal`? currently, it's for the coercion from `nnreal` to `real`, and the analogous lemma for the coercion from `nnreal` to `ennreal` is called `measurable.ennreal_coe`!). I'd like to normalize all this to have something coherent:
* maps are defined from a type to another one, to be able to use dot notation.
* when there are coercions, all lemmas should be formulated in terms of the coercion, and not of the explicit map
* when there is an ambiguity, lemmas on coercions should mention both the source and the target (like in `measurable.coe_nnreal_real`, say). 
The PR is one first step in this direction, renaming `nnreal.of_real` to `real.to_nnreal` (which makes it possible to use dot notation).

### [2021-06-02 04:57:08](https://github.com/leanprover-community/mathlib/commit/832aff8)
chore(scripts): update nolints.txt ([#7798](https://github.com/leanprover-community/mathlib/pull/7798))
I am happy to remove some nolints for you!

### [2021-06-02 04:57:06](https://github.com/leanprover-community/mathlib/commit/cdf6cf0)
feat(topology/sheaves/stalks): Small lemmas about stalk pushforward and stalk map ([#7789](https://github.com/leanprover-community/mathlib/pull/7789))
`Top.presheaf.stalk_pushforward` and `PresheafedSpace.stalk_map` commute with `Top.presheaf.germ`.

### [2021-06-02 04:57:05](https://github.com/leanprover-community/mathlib/commit/2164107)
refactor(algebraic_geometry/structure_sheaf): Rename Spec.Top to prime_spectrum.Top ([#7786](https://github.com/leanprover-community/mathlib/pull/7786))
Renames `Spec.Top` to `prime_specturm.Top` to free up the namespace for the Spec functor.

### [2021-06-02 04:57:04](https://github.com/leanprover-community/mathlib/commit/2fd0ff4)
chore(order/omega_complete_partial_order): clean up references ([#7781](https://github.com/leanprover-community/mathlib/pull/7781))
fix the references rendering by adding them to the .bib

### [2021-06-02 04:57:03](https://github.com/leanprover-community/mathlib/commit/5a42f80)
chore(logic/embedding): move some algebra content ([#7776](https://github.com/leanprover-community/mathlib/pull/7776))
This moves a lemma about multiplication by an element in a left/right cancellative semigroup being an embedding out of `logic.embedding`. I didn't find a great home for it, but put it with some content about regular elements, which is at least talking about similar mathematics.
This removes the only direct import from the `logic/` directory to the `algebra/` directory. There are still indirect imports from `logic.small`, which currently brings in `fintype` and hence the whole algebra hierarchy. I'll look at that separately.

### [2021-06-02 04:57:02](https://github.com/leanprover-community/mathlib/commit/6c912de)
feat(topology/bases): Topological basis of a product. ([#7753](https://github.com/leanprover-community/mathlib/pull/7753))
Given a family of topological spaces `X_i` with topological bases `T_i`, this constructs the associated basis of the product topology. 
This also includes a construction of the tautological topological basis consisting of all open sets.
This generalizes a lemma from LTE.

### [2021-06-02 04:57:00](https://github.com/leanprover-community/mathlib/commit/4884ea5)
feat(order/[conditionally_]complete_lattice): add more intro lemmas for [c][Sup, Inf] and [c][supr, infi] ([#7730](https://github.com/leanprover-community/mathlib/pull/7730))

### [2021-06-02 04:56:59](https://github.com/leanprover-community/mathlib/commit/6b2c7a7)
feat(data/finset/noncomm_prod): finset products over monoid ([#7567](https://github.com/leanprover-community/mathlib/pull/7567))
The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

### [2021-06-01 23:18:36](https://github.com/leanprover-community/mathlib/commit/681b9c2)
feat(ring_theory/adjoin/basic): add missing lemmas ([#7780](https://github.com/leanprover-community/mathlib/pull/7780))
Two missing lemmas about `adjoin`.
These are the `subalgebra` versions of `submodule.span_eq_of_le` and `submodule.span_eq`.

### [2021-06-01 23:18:35](https://github.com/leanprover-community/mathlib/commit/76f41e7)
chore(data/nat): split out data/nat/pow ([#7758](https://github.com/leanprover-community/mathlib/pull/7758))
Split lemmas about the power operation on natural numbers into its own file; slightly reduces imports.

### [2021-06-01 23:18:35](https://github.com/leanprover-community/mathlib/commit/2689c51)
feat(category_theory/abelian): abelian categories with enough projectives have projective resolutions ([#7488](https://github.com/leanprover-community/mathlib/pull/7488))

### [2021-06-01 20:17:20](https://github.com/leanprover-community/mathlib/commit/4e7c6b2)
chore(algebra/associated): weaken some typeclass assumptions ([#7760](https://github.com/leanprover-community/mathlib/pull/7760))
Also golf ne_zero_iff_of_associated a little.

### [2021-06-01 15:40:08](https://github.com/leanprover-community/mathlib/commit/8527efd)
feat(topology/connected): prod.totally_disconnected_space ([#7747](https://github.com/leanprover-community/mathlib/pull/7747))
From LTE.

### [2021-06-01 15:40:07](https://github.com/leanprover-community/mathlib/commit/abe146f)
feat(linear_map): to_*_linear_map_injective ([#7746](https://github.com/leanprover-community/mathlib/pull/7746))
From LTE.

### [2021-06-01 12:28:58](https://github.com/leanprover-community/mathlib/commit/88685b0)
feat(linear_algebra/tensor_product): Add is_scalar_tower instances ([#6741](https://github.com/leanprover-community/mathlib/pull/6741))
If either the left- or right-hand type of a tensor product forms a scalar tower, then the tensor product forms the same tower.

### [2021-06-01 05:20:12](https://github.com/leanprover-community/mathlib/commit/31ba155)
feat(algebraic_topology/cech_nerve): The Cech nerve is a right adjoint. ([#7716](https://github.com/leanprover-community/mathlib/pull/7716))
Also fixes the namespace in the file `algebraic_topology/cech_nerve.lean`.
This is needed for LTE

### [2021-06-01 03:25:51](https://github.com/leanprover-community/mathlib/commit/272a930)
chore(scripts): update nolints.txt ([#7775](https://github.com/leanprover-community/mathlib/pull/7775))
I am happy to remove some nolints for you!

### [2021-06-01 01:52:24](https://github.com/leanprover-community/mathlib/commit/4c2bfde)
chore(order/pilex): add docstring ([#7769](https://github.com/leanprover-community/mathlib/pull/7769))
- add module docstring
- extend `ordered_add_comm_group (pilex ι β)` using `to_additive`

### [2021-06-01 01:52:23](https://github.com/leanprover-community/mathlib/commit/a8f5cc1)
feat(algebra/homology): i-th component of a chain map as a →+ ([#7743](https://github.com/leanprover-community/mathlib/pull/7743))
From LTE.