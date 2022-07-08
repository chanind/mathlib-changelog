### [2021-10-31 23:00:49](https://github.com/leanprover-community/mathlib/commit/932e954)
feat(data/finset): some simple finset lemmas ([#10079](https://github.com/leanprover-community/mathlib/pull/10079))

### [2021-10-31 23:00:48](https://github.com/leanprover-community/mathlib/commit/60cb2cf)
feat(data/list): length_filter_lt_length_iff_exists ([#10074](https://github.com/leanprover-community/mathlib/pull/10074))
Also moved a lemma about filter_map that was placed in the wrong file

### [2021-10-31 23:00:47](https://github.com/leanprover-community/mathlib/commit/af4f4df)
feat(list/init): simplifier lemmas for list.init ([#10061](https://github.com/leanprover-community/mathlib/pull/10061))

### [2021-10-31 23:00:45](https://github.com/leanprover-community/mathlib/commit/d6dd451)
chore(data/list/basic): use dot notation here and there ([#10056](https://github.com/leanprover-community/mathlib/pull/10056))
### Renamed lemmas
- `list.cons_sublist_cons` → `list.sublist.cons_cons`;
- `list.infix_of_prefix` → `list.is_prefix.is_infix`;
- `list.infix_of_suffix` → `list.is_suffix.is_infix`;
- `list.sublist_of_infix` → `list.is_infix.sublist`;
- `list.sublist_of_prefix` → `list.is_prefix.sublist`;
- `list.sublist_of_suffix` → `list.is_suffix.sublist`;
- `list.length_le_of_infix` → `list.is_infix.length_le`.
### New `simp` attrs
`list.singleton_sublist`, `list.repeat_sublist_repeat`, `list.reverse_suffix`, `list.reverse_prefix`.
### New lemmas
`list.infix_insert`, `list.sublist_insert`, `list.subset_insert`.

### [2021-10-31 23:00:44](https://github.com/leanprover-community/mathlib/commit/76f13b3)
feat(algebra/star/basic): `ring.inverse_star` ([#10039](https://github.com/leanprover-community/mathlib/pull/10039))
Also adds `is_unit.star` and `is_unit_star`.

### [2021-10-31 21:28:18](https://github.com/leanprover-community/mathlib/commit/106dc57)
chore(ring_theory/ideal/operations): generalize typeclass in map_map and comap_comap ([#10077](https://github.com/leanprover-community/mathlib/pull/10077))
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024) which is hitting timeouts somewhere more irritating.

### [2021-10-31 21:28:17](https://github.com/leanprover-community/mathlib/commit/233eb66)
feat(data/real/ennreal): more on integer powers on ennreal ([#10071](https://github.com/leanprover-community/mathlib/pull/10071))

### [2021-10-31 18:58:21](https://github.com/leanprover-community/mathlib/commit/5ca3c5e)
chore(data/set/intervals): add some lemmas ([#10062](https://github.com/leanprover-community/mathlib/pull/10062))
Add several lemma lemmas about intersection/difference of intervals.

### [2021-10-31 18:58:20](https://github.com/leanprover-community/mathlib/commit/05bd61d)
chore(analysis): move more code out of `analysis.normed_space.basic` ([#10055](https://github.com/leanprover-community/mathlib/pull/10055))

### [2021-10-31 18:58:19](https://github.com/leanprover-community/mathlib/commit/8390325)
fix(data/pequiv): fix lint ([#10043](https://github.com/leanprover-community/mathlib/pull/10043))

### [2021-10-31 18:58:18](https://github.com/leanprover-community/mathlib/commit/66f7114)
feat(measure_theory/group): add `measurable_set.const_smul` ([#10025](https://github.com/leanprover-community/mathlib/pull/10025))
Partially based on lemmas from [#2819](https://github.com/leanprover-community/mathlib/pull/2819).

### [2021-10-31 17:26:29](https://github.com/leanprover-community/mathlib/commit/f2b77d7)
refactor(set_theory/cardinal): swap sides of `simp` lemmas ([#10040](https://github.com/leanprover-community/mathlib/pull/10040))
## API changes
### Swap sides of simp lemmas
- `cardinal.add_def` is no loner a `simp` lemma, `cardinal.mk_sum` (renamed from `cardinal.add`) simplifies `#(α ⊕ β)` to `lift.{v u} (#α) + lift.{u v} (#β)`;
- `cardinal.mul_def` is no loner a `simp` lemma, `cardinal.mk_prod` (merged with `cardinal.mul`) simplifies `#(α × β)` to `lift.{v u} (#α) * lift.{u v} (#β)`;
- `cardinal.power_def` is no longer a `simp` lemma. New lemma `cardinal.mk_arrow` computes `#(α → β)`. It is not a `simp` lemma because it follows from other `simp` lemmas.
- replace `cardinal.sum_mk` with `cardinal.mk_sigma` and `cardinal.prod_mk` with `cardinal.mk_pi`;
### Other changes
- new lemmas `@[simp] cardinal.lift_uzero` and `cardinal.lift_umax'`;
- split `cardinal.linear_order` into `cardinal.preorder` (doesn't rely on `classical.choice`), `cardinal.partial_order` (needs `classical.choice`, computable), and `cardinal.linear_order` (noncomputable);
- add `cardinal.lift_order_embedding`;
- add `cardinal.mk_psum`;
- rename `cardinal.prop_eq_two` to `cardinal.mk_Prop`, drop the old `mk_Prop`;
- use local notation for natural power;
- rename old `sum_const` to `sum_const'`, the new `@[simp] lemma sum_const` is what used to be `sum_const_eq_lift_mul`;
- rename old `prod_const` to `prod_const'`, the new `@[simp] lemma prod_const` deals with types in different universes;
- add `@[simp]` to `cardinal.prod_eq_zero` and `cardinal.omega_le_mk`;
- add `@[simp]` lemmas `cardinal.mk_eq_one`, `cardinal.mk_vector`, `cardinal.omega_mul_eq`, and `cardinal.mul_omega_eq`;
- replace `mk_plift_of_true` and `mk_plift_of_false` with `mk_plift_true` and `mk_plift_false`;
- `mk_list_eq_mk` and `mk_finset_eq_mk` now assume `[infinite α]` instead of `ω ≤ #α`.

### [2021-10-31 14:01:29](https://github.com/leanprover-community/mathlib/commit/4ef3fcd)
chore(algebra/group/inj_surj): add 2 missing `def`s ([#10068](https://github.com/leanprover-community/mathlib/pull/10068))
`function.injective.right_cancel_monoid` and `function.injective.cancel_monoid` were missing.
`function.injective.sub_neg_monoid` was also misnamed `function.injective.sub_neg_add_monoid`.

### [2021-10-31 14:01:28](https://github.com/leanprover-community/mathlib/commit/36de1ef)
chore(ring_theory/noetherian): generalize to semiring ([#10032](https://github.com/leanprover-community/mathlib/pull/10032))
This weakens some typeclasses on some results about `is_noetherian` (which already permits modules over semirings), and relaxes `is_noetherian_ring` to permit semirings.
This does not actually try changing any of the proofs, it just relaxes assumptions that were stronger than what was actually used.

### [2021-10-31 13:18:04](https://github.com/leanprover-community/mathlib/commit/ca7fee8)
feat(category_theory/limits): Results about pullbacks ([#9984](https://github.com/leanprover-community/mathlib/pull/9984))
- Provided the explicit isomorphism `X ×[Z] Y ≅ Y ×[Z] X`.
- Provided the pullback of f g when either one is iso or when both are mono.

### [2021-10-31 11:57:21](https://github.com/leanprover-community/mathlib/commit/be0a4af)
chore(analysis): move `real.angle` to a dedicated file ([#10065](https://github.com/leanprover-community/mathlib/pull/10065))
We don't use this type anywhere else.

### [2021-10-31 11:57:20](https://github.com/leanprover-community/mathlib/commit/0433eb6)
doc(topology/uniform_space/uniform_embedding): add some docs ([#10045](https://github.com/leanprover-community/mathlib/pull/10045))

### [2021-10-31 11:57:19](https://github.com/leanprover-community/mathlib/commit/e5f9bec)
chore(linear_algebra/basic): relax ring to semiring ([#10030](https://github.com/leanprover-community/mathlib/pull/10030))
This relaxes a random selection of lemmas from `ring R` to `semiring R`, and cleans up some unused `variables` nearby.
Probably the most useful of these are `submodule.mem_map_equiv`, `map_subtype.rel_iso`, and `submodule.disjoint_iff_comap_eq_bot`

### [2021-10-31 11:57:18](https://github.com/leanprover-community/mathlib/commit/35cf154)
feat(linear_algebra/eigenspace): define `eigenvalues` of an endomorphism ([#10027](https://github.com/leanprover-community/mathlib/pull/10027))
Prerequisites in `linear_algebra/eigenspace` for [#9995](https://github.com/leanprover-community/mathlib/pull/9995), including a definition `module.End.eigenvalues`, the eigenvalues of an endomorphism considered as a subtype of the scalar ring.

### [2021-10-31 10:19:07](https://github.com/leanprover-community/mathlib/commit/175ac2c)
chore(algebra/group/defs): golf a proof ([#10067](https://github.com/leanprover-community/mathlib/pull/10067))
Use `monoid.ext` to golf `div_inv_monoid.ext`.

### [2021-10-31 10:19:06](https://github.com/leanprover-community/mathlib/commit/31c8aa5)
chore(algebra/group_with_zero/basic): zero, one, and pow lemmas for `ring.inverse` ([#10049](https://github.com/leanprover-community/mathlib/pull/10049))
This adds:
* `ring.inverse_zero`
* `ring.inverse_one`
* `ring.inverse_pow` (to match `inv_pow`, `inv_pow₀`)
* `commute.ring_inverse_ring_inverse` (to match `commute.inv_inv`)

### [2021-10-31 09:46:36](https://github.com/leanprover-community/mathlib/commit/43e7d1b)
feat(order/antichain): Antichains ([#9926](https://github.com/leanprover-community/mathlib/pull/9926))
This defines antichains mimicking the definition of chains.

### [2021-10-31 07:34:51](https://github.com/leanprover-community/mathlib/commit/b7f120f)
chore(*): clean up the library using to_additive ([#9790](https://github.com/leanprover-community/mathlib/pull/9790))
Since [#9138](https://github.com/leanprover-community/mathlib/pull/9138) and [#5487](https://github.com/leanprover-community/mathlib/pull/5487) to_additive got a lot better, so a lot of duplication in the library becomes unnecessary and makes maintenence a burden. So we remove a large number of copy-pasted declarations that can now be generated automatically.

### [2021-10-31 03:19:22](https://github.com/leanprover-community/mathlib/commit/236f395)
chore(topology/compacts): add a missing simp lemma ([#10063](https://github.com/leanprover-community/mathlib/pull/10063))

### [2021-10-31 01:33:41](https://github.com/leanprover-community/mathlib/commit/c952017)
chore(logic/embedding): docs, fixes ([#10047](https://github.com/leanprover-community/mathlib/pull/10047))
* generalize `function.extend` and some lemmas from `Type*` to `Sort*`.
* add missing docs in `logic.embedding`;
* swap `function.embedding.arrow_congr_left` and `function.embedding.arrow_congr_right`;
* use `function.extend` to define the new `function.embedding.arrow_congr_left`.

### [2021-10-31 00:02:40](https://github.com/leanprover-community/mathlib/commit/951c063)
chore(data/set/pairwise): rename `set.pairwise_on` to `set.pairwise` to match `list.pairwise` and `multiset.pairwise` ([#10035](https://github.com/leanprover-community/mathlib/pull/10035))

### [2021-10-30 23:31:00](https://github.com/leanprover-community/mathlib/commit/7ef3262)
ci(.github/workflows/bors.yml): "bors" label for staging builds ([#10064](https://github.com/leanprover-community/mathlib/pull/10064))

### [2021-10-30 20:45:45](https://github.com/leanprover-community/mathlib/commit/bdf38cf)
chore(*): rename int_pow to zpow ([#10058](https://github.com/leanprover-community/mathlib/pull/10058))
Leftovers of [#9989](https://github.com/leanprover-community/mathlib/pull/9989)

### [2021-10-30 09:45:40](https://github.com/leanprover-community/mathlib/commit/5ff850b)
feat(algebra/module/submodule_lattice): add `add_subgroup.to_int_submodule` ([#10051](https://github.com/leanprover-community/mathlib/pull/10051))
This converts an `add_subgroup M` to a `submodule ℤ M`. We already have the analogous construction for `add_submonoid M`.

### [2021-10-30 08:28:49](https://github.com/leanprover-community/mathlib/commit/d06bd9a)
feat(algebra/big_operators/finprod): add finprod_eq_of_bijective ([#10048](https://github.com/leanprover-community/mathlib/pull/10048))

### [2021-10-30 06:04:06](https://github.com/leanprover-community/mathlib/commit/06b1d87)
feat(algebra/group): add `commute.is_unit_mul_iff` ([#10042](https://github.com/leanprover-community/mathlib/pull/10042))

### [2021-10-30 01:45:12](https://github.com/leanprover-community/mathlib/commit/fcc158e)
chore(*): update to Lean-3.35.0c ([#9988](https://github.com/leanprover-community/mathlib/pull/9988))
Move `stream`, `rbtree`, and `rbmap` from core to `mathlib` and reflows some long lines. Rename some files to avoid name clashes.

### [2021-10-29 19:43:29](https://github.com/leanprover-community/mathlib/commit/c722dae)
chore(data/fintype/basic): add a few `infinite` instances ([#10037](https://github.com/leanprover-community/mathlib/pull/10037))

### [2021-10-29 19:43:27](https://github.com/leanprover-community/mathlib/commit/4f053a5)
feat(data/list): chain'_drop lemma ([#10028](https://github.com/leanprover-community/mathlib/pull/10028))

### [2021-10-29 17:12:04](https://github.com/leanprover-community/mathlib/commit/c545660)
chore(algebra/group_with_zero/basic): move `ring.inverse`, generalize and rename `inverse_eq_has_inv` ([#10033](https://github.com/leanprover-community/mathlib/pull/10033))
This moves `ring.inverse` earlier in the import graph, since it's not about rings at all.

### [2021-10-29 14:39:48](https://github.com/leanprover-community/mathlib/commit/e1bafaa)
feat(category_theory/limits/shapes/images): some explicit instances of has_image_map ([#9977](https://github.com/leanprover-community/mathlib/pull/9977))

### [2021-10-29 13:53:07](https://github.com/leanprover-community/mathlib/commit/4f3443a)
feat(measure_theory/group/arithmetic): add a section about `opposite` ([#10026](https://github.com/leanprover-community/mathlib/pull/10026))

### [2021-10-29 08:04:41](https://github.com/leanprover-community/mathlib/commit/3f6174b)
fix(tactic/norm_cast): make push_cast discharger match the others ([#10021](https://github.com/leanprover-community/mathlib/pull/10021))
closes [#9822](https://github.com/leanprover-community/mathlib/pull/9822)

### [2021-10-29 01:24:36](https://github.com/leanprover-community/mathlib/commit/4ce2a5f)
chore(algebra/module/submodule_lattice): lemmas about the trivial submodule ([#10022](https://github.com/leanprover-community/mathlib/pull/10022))
Lemmas about the trivial submodule.  Also move an existing lemma `exists_mem_ne_zero_of_ne_bot` about the trivial submodule from `linear_algebra/dimension` to `algebra/module/submodule_lattice`, since it doesn't use any facts about dimension.

### [2021-10-29 01:24:35](https://github.com/leanprover-community/mathlib/commit/7538f9b)
feat(data/list/defs): map_with_prefix_suffix and map_with_complement ([#10020](https://github.com/leanprover-community/mathlib/pull/10020))
Adds two list definitions: one that will be useful to me, and a generalization which may be useful to @semorrison

### [2021-10-29 01:24:33](https://github.com/leanprover-community/mathlib/commit/c7f5139)
chore(measure_theory): drop a few `measurable_set` assumptions ([#9999](https://github.com/leanprover-community/mathlib/pull/9999))
We had an extra `measurable_set` assumption in (one of the copies of) Caratheodory. Also remove `measurable f` assumption in `is_finite_measure (map f μ)` and make it an instance.

### [2021-10-29 00:33:15](https://github.com/leanprover-community/mathlib/commit/bdcb731)
feat(linear_algebra/matrix/adjugate): det_adjugate and adjugate_adjugate ([#9991](https://github.com/leanprover-community/mathlib/pull/9991))
This also adds `matrix.mv_polynomial_X`

### [2021-10-28 20:48:25](https://github.com/leanprover-community/mathlib/commit/415da22)
chore(topology,measure_theory): generalize a few instances ([#9967](https://github.com/leanprover-community/mathlib/pull/9967))
* Prove that `Π i : ι, π i` has second countable topology if `ι` is encodable and each `π i` has second countable topology.
* Similarly for `borel_space`.
* Preserve old instances about `fintype` because we don't have (and can't have) an instance `fintype ι → encodable ι`.

### [2021-10-28 20:48:24](https://github.com/leanprover-community/mathlib/commit/0cfae43)
feat(archive/imo): IMO 2021 Q1 ([#8432](https://github.com/leanprover-community/mathlib/pull/8432))
Formalised solution to IMO 2021 Q1

### [2021-10-28 18:57:48](https://github.com/leanprover-community/mathlib/commit/99a2d5b)
feat(ring_theory/adjoin_root): golf and generalize the algebra structure on `adjoin_root` ([#10019](https://github.com/leanprover-community/mathlib/pull/10019))
We already have a more general version of this instance elsewhere, lets just reuse it.

### [2021-10-28 18:57:46](https://github.com/leanprover-community/mathlib/commit/18dce13)
feat(data/finset/interval): Bounded intervals in locally finite orders are finite ([#9960](https://github.com/leanprover-community/mathlib/pull/9960))
A set which is bounded above and below is finite. A set which is bounded below in an `order_top` is finite. A set which is bounded above in an `order_bot` is finite.
Also provide the `order_dual` constructions for `bdd_stuff` and `locally_finite_order`.

### [2021-10-28 18:57:45](https://github.com/leanprover-community/mathlib/commit/1733920)
feat(list): add some lemmas ([#9873](https://github.com/leanprover-community/mathlib/pull/9873))
Add a few lemmas about lists.
These are helpful when manipulating lists.

### [2021-10-28 17:00:22](https://github.com/leanprover-community/mathlib/commit/e927aa4)
feat(data/set/function): restrict `dite/ite/piecewise/extend` ([#10017](https://github.com/leanprover-community/mathlib/pull/10017))

### [2021-10-28 17:00:20](https://github.com/leanprover-community/mathlib/commit/0d6548f)
chore(*): a few lemmas about `range_splitting ([#10016](https://github.com/leanprover-community/mathlib/pull/10016))

### [2021-10-28 17:00:18](https://github.com/leanprover-community/mathlib/commit/b9ff26b)
chore(measure_theory/measure/measure_space): reorder, golf ([#10015](https://github.com/leanprover-community/mathlib/pull/10015))
Move `restrict_apply'` up and use it to golf some proofs. Drop an unneeded `measurable_set` assumption in 1 proof.

### [2021-10-28 17:00:16](https://github.com/leanprover-community/mathlib/commit/fd6f681)
feat(order/bounded_lattice): add `is_compl.le_sup_right_iff_inf_left_le` ([#10014](https://github.com/leanprover-community/mathlib/pull/10014))
This lemma is a generalization of `is_compl.inf_left_eq_bot_iff`.
Also drop `inf_eq_bot_iff_le_compl` in favor of
`is_compl.inf_left_eq_bot_iff` and add
`set.subset_union_compl_iff_inter_subset`.

### [2021-10-28 17:00:14](https://github.com/leanprover-community/mathlib/commit/22d32dc)
fix(field_theory/intermediate_field): use a better `algebra.smul` definition, and generalize ([#10012](https://github.com/leanprover-community/mathlib/pull/10012))
Previously coe_smul was not true by `rfl`

### [2021-10-28 17:00:12](https://github.com/leanprover-community/mathlib/commit/fe76b5c)
feat(group_theory/subgroup/basic): `mul_mem_sup` ([#10007](https://github.com/leanprover-community/mathlib/pull/10007))
Adds `mul_mem_sup` and golfs a couple proofs that reprove this result.

### [2021-10-28 17:00:10](https://github.com/leanprover-community/mathlib/commit/c495ed6)
move(data/set/pairwise): Move `set.pairwise_on` ([#9986](https://github.com/leanprover-community/mathlib/pull/9986))
This moves `set.pairwise_on` to `data.set.pairwise`, where `pairwise` and `set.pairwise_disjoint` already are.

### [2021-10-28 17:00:08](https://github.com/leanprover-community/mathlib/commit/628f418)
feat(computability/tm_to_partrec): prove finiteness ([#6955](https://github.com/leanprover-community/mathlib/pull/6955))
The proof in this file was incomplete, and I finally found the time to
finish it. `tm_to_partrec.lean` constructs a turing machine that can
simulate a given partial recursive function. Previously, the functional
correctness of this machine was proven, but it uses an infinite state
space so it is not a priori obvious that it is in fact a true (finite)
turing machine, which is important for the Church-Turing theorem. This
PR adds a proof that the machine is in fact finite.

### [2021-10-28 15:13:55](https://github.com/leanprover-community/mathlib/commit/c8d1429)
feat(data/{finset,multiset}/locally_finite): Simple interval lemmas ([#9877](https://github.com/leanprover-community/mathlib/pull/9877))
`(finset/multiset).image_add_(left/right)_Ixx` and `multiset.nodup_Ixx`

### [2021-10-28 12:41:11](https://github.com/leanprover-community/mathlib/commit/acbb2a5)
feat(analysis/normed_space/pi_Lp): use typeclass inference for `1 ≤ p` ([#9922](https://github.com/leanprover-community/mathlib/pull/9922))
In `measure_theory.Lp`, the exponent `(p : ℝ≥0∞)` is an explicit hypothesis, and typeclass inference finds `[fact (1 ≤ p)]` silently (with the help of some pre-built `fact_one_le_two_ennreal` etc for specific use cases).
Currently, in `pi_Lp`, the fact that `(hp : 1 ≤ p)` must be provided explicitly.  I propose changing over to the `fact` system as used `measure_theory.Lp` -- I think it looks a bit prettier in typical use cases.

### [2021-10-28 09:24:44](https://github.com/leanprover-community/mathlib/commit/b0349aa)
chore(measure_theory): a `continuous_map` is measurable ([#9998](https://github.com/leanprover-community/mathlib/pull/9998))
Also move the proof of `homeomorph.measurable` up and use it in the
definition of `homeomorph.to_measurable_equiv`.

### [2021-10-28 09:24:43](https://github.com/leanprover-community/mathlib/commit/73423cf)
feat(measure/measurable_space): add `measurable_equiv.of_unique_of_unique` ([#9968](https://github.com/leanprover-community/mathlib/pull/9968))
Also fix a typo in a lemma name: `measurable_equiv.measurable_coe_iff` → `measurable_comp_iff`.

### [2021-10-28 09:24:41](https://github.com/leanprover-community/mathlib/commit/7f2b806)
feat(analysis/inner_product_space/dual): complex Riesz representation theorem ([#9924](https://github.com/leanprover-community/mathlib/pull/9924))
Now that we have conjugate-linear maps, the Riesz representation theorem can be stated in a form that works over both `ℝ` and `ℂ`, as the construction of a conjugate-linear isometric equivalence from a complete inner product space `E` to its dual.

### [2021-10-28 06:57:32](https://github.com/leanprover-community/mathlib/commit/f78b739)
feat(category_theory/arrow): is_iso, mono, epi instances for maps between arrows ([#9976](https://github.com/leanprover-community/mathlib/pull/9976))

### [2021-10-28 06:57:30](https://github.com/leanprover-community/mathlib/commit/8159af6)
feat(measure_theory/construction/borel_space): two measures are equal if they agree on closed-open intervals ([#9396](https://github.com/leanprover-community/mathlib/pull/9396))

### [2021-10-28 04:50:38](https://github.com/leanprover-community/mathlib/commit/468a9d5)
chore(scripts): update nolints.txt ([#10013](https://github.com/leanprover-community/mathlib/pull/10013))
I am happy to remove some nolints for you!

### [2021-10-28 04:50:37](https://github.com/leanprover-community/mathlib/commit/bcaeb57)
fix(data/equiv/encodable): turn `unique.encodable` into a `def` ([#10006](https://github.com/leanprover-community/mathlib/pull/10006))

### [2021-10-28 02:37:00](https://github.com/leanprover-community/mathlib/commit/9db7270)
chore(*): rename gsmul to zsmul and gmultiples to zmultiples ([#10010](https://github.com/leanprover-community/mathlib/pull/10010))
This is consistent with an earlier rename from `gpow` to `zpow`.

### [2021-10-27 20:21:14](https://github.com/leanprover-community/mathlib/commit/d360f3c)
feat(linear_algebra/free_module/finite/rank): add linear_algebra/free_module/finite/rank ([#9832](https://github.com/leanprover-community/mathlib/pull/9832))
A basic API for rank of free modules.
- [x] depends on: [#9821](https://github.com/leanprover-community/mathlib/pull/9821)

### [2021-10-27 17:47:32](https://github.com/leanprover-community/mathlib/commit/8ce5da4)
feat(algebra/order/archimedean): a few more lemmas ([#9997](https://github.com/leanprover-community/mathlib/pull/9997))
Prove that `a + m • b ∈ Ioc c (c + b)` for some `m : ℤ`, and similarly for `Ico`.
Also move some lemmas out of a namespace.

### [2021-10-27 17:47:31](https://github.com/leanprover-community/mathlib/commit/ec51fb7)
chore(algebra/order/floor): prove `subsingleton`s ([#9996](https://github.com/leanprover-community/mathlib/pull/9996))

### [2021-10-27 17:47:29](https://github.com/leanprover-community/mathlib/commit/eaec1da)
feat(group_theory/group_action/conj_act): A characteristic subgroup of a normal subgroup is normal ([#9992](https://github.com/leanprover-community/mathlib/pull/9992))
Uses `mul_aut.conj_normal` to prove an instance stating that a characteristic subgroup of a normal subgroup is normal.

### [2021-10-27 17:47:27](https://github.com/leanprover-community/mathlib/commit/c529711)
refactor(*): rename fpow and gpow to zpow ([#9989](https://github.com/leanprover-community/mathlib/pull/9989))
Historically, we had two notions of integer power, one on groups called `gpow` and the other one on fields called `fpow`. Since the introduction of `div_inv_monoid` and `group_with_zero`, these definitions have been merged into one, and the boundaries are not clear any more. We rename both of them to `zpow`, adding a subscript `0` to disambiguate lemma names when there is a collision, where the subscripted version is for groups with zeroes (as is already done for inv lemmas).
To limit the scope of the change. this PR does not rename `gsmul` to `zsmul` or `gmultiples` to `zmultiples`.

### [2021-10-27 17:47:26](https://github.com/leanprover-community/mathlib/commit/9e4609b)
chore(data/fintype/card): add `fin.prod_univ_{one,two}` ([#9987](https://github.com/leanprover-community/mathlib/pull/9987))
Sometimes Lean fails to simplify `(default : fin 1)` to `0` and
`0.succ` to `1` in complex expressions. These lemmas explicitly use
`f 0` and `f 1` in the output.

### [2021-10-27 17:47:25](https://github.com/leanprover-community/mathlib/commit/29079ba)
feat(tactic/lint): linter improvements ([#9901](https://github.com/leanprover-community/mathlib/pull/9901))
* Make the linter framework easier to use on projects outside mathlib with the new `lint_project` (replacing `lint_mathlib`). Also replace `lint_mathlib_decls` by `lint_project_decls`.
* Make most declarations in the frontend not-private (I want to use them in other projects)
* The unused argument linter does not report declarations that contain `sorry`. It will still report declarations that use other declarations that contain sorry. I did not add a test for this, since it's hard to do that while keeping the test suite silent (but I did test locally).
* Some minor changes in the test suite (not important, but they cannot hurt).

### [2021-10-27 15:13:53](https://github.com/leanprover-community/mathlib/commit/25718c2)
feat(data/nat/basic): Add two lemmas two nat/basic which are necessary for the count PR ([#10001](https://github.com/leanprover-community/mathlib/pull/10001))
Add two lemmas proved by refl to data/nat/basic. They are needed for the count PR, and are changing a file low enogh in the import hierarchy to be a separate PR.

### [2021-10-27 15:13:51](https://github.com/leanprover-community/mathlib/commit/4e29dc7)
chore(topology/algebra/module): add `continuous_linear_equiv.arrow_congr_equiv` ([#9982](https://github.com/leanprover-community/mathlib/pull/9982))

### [2021-10-27 15:13:50](https://github.com/leanprover-community/mathlib/commit/a3f4a02)
chore(analysis/normed_space/is_R_or_C + data/complex/is_R_or_C): make some proof steps standalone lemmas ([#9933](https://github.com/leanprover-community/mathlib/pull/9933))
Separate some proof steps from `linear_map.bound_of_sphere_bound` as standalone lemmas to golf them a little bit.

### [2021-10-27 15:13:49](https://github.com/leanprover-community/mathlib/commit/d7c689d)
feat(algebraic_geometry/prime_spectrum): Closed points in prime spectrum ([#9861](https://github.com/leanprover-community/mathlib/pull/9861))
This PR adds lemmas about the correspondence between closed points in `prime_spectrum R` and maximal ideals of `R`.
In order to import and talk about integral maps I had to move some lemmas from `noetherian.lean` to `prime_spectrum.lean` to prevent cyclic import dependencies.

### [2021-10-27 07:01:26](https://github.com/leanprover-community/mathlib/commit/d9cea39)
refactor(topology+algebraic_geometry): prove and make use of equalities to simplify definitions ([#9972](https://github.com/leanprover-community/mathlib/pull/9972))
Prove and make use of equalities whenever possible, even between functors (which is discouraged according to certain philosophy), to replace isomorphisms by equalities, to remove the need of transporting across isomorphisms in various definitions (using `eq_to_hom` directly), most notably: [simplified definition of identity morphism for PresheafedSpace](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR89), [simplified extensionality lemma for morphisms](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR68), [simplified definition of composition](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR96) and [the global section functor](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-252fb30c3a3221e6472db5ba794344dfb423898696e70299653d95f635de06adR228) (takes advantage of defeq and doesn't require proving any new equality).
Other small changes to mathlib:
- Define pushforward functor of presheaves in topology/sheaves/presheaf.lean
- Add new file functor.lean in topology/sheaves, proves the pushforward of a sheaf is a sheaf, and defines the pushforward functor of sheaves, with the expectation that pullbacks will be added later.
- Make one of the arguments in various `restrict`s implicit.
- Change statement of [`to_open_comp_comap`](https://github.com/leanprover-community/mathlib/compare/use_equality?expand=1#diff-54364470f443f847742b1c105e853afebc25da68faad63cc5a73db167bc85d06R973) in structure_sheaf.lean to be more general (the same proof works!)
The new definitions result in simplified proofs, but apart from the main files opens.lean, presheaf.lean and presheafed_space.lean where proofs are optimized, I did only the minimum changes required to fix the broken proofs, and I expect there to be large room of improvement with the new definitions especially in the files changed in this PR. I also didn't remove the old lemmas and mostly just add new ones, so subsequent cleanup may be desired.

### [2021-10-27 04:25:01](https://github.com/leanprover-community/mathlib/commit/996ece5)
feat(tactic/suggest): add a flag to disable "Try this" lines ([#9820](https://github.com/leanprover-community/mathlib/pull/9820))

### [2021-10-27 02:40:26](https://github.com/leanprover-community/mathlib/commit/62edbe5)
chore(scripts): update nolints.txt ([#9994](https://github.com/leanprover-community/mathlib/pull/9994))
I am happy to remove some nolints for you!

### [2021-10-26 22:41:21](https://github.com/leanprover-community/mathlib/commit/b592589)
refactor(order/boolean_algebra): factor out pi.sdiff and pi.compl ([#9955](https://github.com/leanprover-community/mathlib/pull/9955))
Provide definitional lemmas about sdiff and compl on pi types.
This allows usage later on even without a whole `boolean_algebra` instance.

### [2021-10-26 22:41:20](https://github.com/leanprover-community/mathlib/commit/120cf5b)
doc(topology) add a library note about continuity lemmas ([#9954](https://github.com/leanprover-community/mathlib/pull/9954))
* This is a note with some tips how to formulate a continuity (or measurability, differentiability, ...) lemma.
* I wanted to write this up after formulating `continuous.strans` in many "wrong" ways before discovering the "right" way.
* I think many lemmas are not following this principle, and could be improved in generality and/or convenience by following this advice.
* Based on experience from the sphere eversion project.
* The note mentions a lemma that will be added in [#9959](https://github.com/leanprover-community/mathlib/pull/9959), but I don't think we necessarily have to wait for that PR.

### [2021-10-26 21:02:25](https://github.com/leanprover-community/mathlib/commit/36a2015)
feat(topology/[separation, dense_embedding]): a function to a T1 space which has a limit at x is continuous at x ([#9934](https://github.com/leanprover-community/mathlib/pull/9934))
We prove that, for a function `f` with values in a T1 space, knowing that `f` admits *any* limit at `x` suffices to prove that `f` is continuous at `x`.
We then use it to give a variant of `dense_inducing.extend_eq` with the same assumption required for continuity of the extension, which makes using both `extend_eq` and `continuous_extend` easier, and also brings us closer to Bourbaki who makes no explicit continuity assumption on the function to extend.

### [2021-10-26 20:05:59](https://github.com/leanprover-community/mathlib/commit/92e9078)
fix(linear_algebra/matrix/determinant): remove coercions ([#9975](https://github.com/leanprover-community/mathlib/pull/9975))

### [2021-10-26 20:05:58](https://github.com/leanprover-community/mathlib/commit/2a32c70)
refactor(linear_algebra/matrix/nonsingular_inverse): split out files for adjugate and nondegenerate ([#9974](https://github.com/leanprover-community/mathlib/pull/9974))
This breaks the file roughly in two, and rescues lost lemmas that ended up in the wrong sections of the file.
The module docstrings have been tweaked a little, but all the lemmas have just been moved around.

### [2021-10-26 17:54:26](https://github.com/leanprover-community/mathlib/commit/ce164e2)
chore(data/{finset,multiset}/locally_finite): rename from `.interval` ([#9980](https://github.com/leanprover-community/mathlib/pull/9980))
The pattern is `data.stuff.interval` for files about `locally_finite_order stuff` and... `finset α` and `multiset α` are locally finite orders. This thus makes space for this theory.

### [2021-10-26 17:54:24](https://github.com/leanprover-community/mathlib/commit/3aa5749)
feat(group_theory/subgroup/basic): Define characteristic subgroups ([#9921](https://github.com/leanprover-community/mathlib/pull/9921))
This PR defines characteristic subgroups and builds the basic API.
Getting `@[to_additive]` to work correctly was a bit tricky, so I mostly just copied the setup for `subgroup.normal`.

### [2021-10-26 16:22:50](https://github.com/leanprover-community/mathlib/commit/50c6094)
feat(topology/uniform_space/basic): add lemma `comp_open_symm_mem_uniformity_sets` ([#9981](https://github.com/leanprover-community/mathlib/pull/9981))

### [2021-10-26 12:23:43](https://github.com/leanprover-community/mathlib/commit/d2b1221)
feat(algebra/order/group|order/filter): add two lemmas ([#9956](https://github.com/leanprover-community/mathlib/pull/9956))
* Also open `function` namespace in `order.filter.basic`
* From the sphere eversion project

### [2021-10-26 09:49:59](https://github.com/leanprover-community/mathlib/commit/41df5b3)
docs(data/sigma/basic): Add module docstring ([#9908](https://github.com/leanprover-community/mathlib/pull/9908))

### [2021-10-26 09:09:15](https://github.com/leanprover-community/mathlib/commit/6b47ccb)
feat(group_theory/p_group): Center of a p-group is nontrivial ([#9973](https://github.com/leanprover-community/mathlib/pull/9973))
The center of a p-group is nontrivial, stated in two different ways.

### [2021-10-26 07:25:48](https://github.com/leanprover-community/mathlib/commit/f229c83)
chore(*): move 2 lemmas to reorder imports ([#9969](https://github.com/leanprover-community/mathlib/pull/9969))
I want to use `measure_theory.measure_preserving` in various files, including `measure_theory.integral.lebesgue`. The file about measure preserving map had two lemmas about product measures. I move them to `measure_theory.constructions.prod`. I also golfed (and made it more readable at the same time!) the proof of `measure_theory.measure.prod_prod_le` using `to_measurable_set`.

### [2021-10-26 07:25:47](https://github.com/leanprover-community/mathlib/commit/367d71e)
chore(order/iterate): review, add docs ([#9965](https://github.com/leanprover-community/mathlib/pull/9965))
* reorder sections;
* add section docs;
* use inequalities between functions in a few statements;
* add a few lemmas about `strict_mono` functions.

### [2021-10-26 07:25:45](https://github.com/leanprover-community/mathlib/commit/717de02)
refactor(linear_algebra/free_module/pid): move lemmas ([#9962](https://github.com/leanprover-community/mathlib/pull/9962))
`linear_algebra/free_module/pid` contains several results not directly related to PID. We move them in more appropriate files.
Except for small golfing and easy generalization, the statements and the proofs are untouched.

### [2021-10-26 05:22:54](https://github.com/leanprover-community/mathlib/commit/5227f53)
chore(data/equiv/encodable): a `[unique]` type is encodable ([#9970](https://github.com/leanprover-community/mathlib/pull/9970))

### [2021-10-26 02:28:08](https://github.com/leanprover-community/mathlib/commit/a8e6442)
chore(scripts): update nolints.txt ([#9971](https://github.com/leanprover-community/mathlib/pull/9971))
I am happy to remove some nolints for you!

### [2021-10-26 01:01:18](https://github.com/leanprover-community/mathlib/commit/e88b4ed)
chore(measure_theory/constructions/pi): add `pi_of_empty` ([#9937](https://github.com/leanprover-community/mathlib/pull/9937))

### [2021-10-25 22:55:58](https://github.com/leanprover-community/mathlib/commit/56de12a)
refactor(data/mv_polynomial): upgrade `monomial` to a `linear_map` ([#9870](https://github.com/leanprover-community/mathlib/pull/9870))

### [2021-10-25 22:55:56](https://github.com/leanprover-community/mathlib/commit/34b9933)
feat(number_theory/liouville): the set of Liouville numbers has measure zero ([#9702](https://github.com/leanprover-community/mathlib/pull/9702))
As a corollary, the filters `residual ℝ` and `volume.ae` are disjoint.

### [2021-10-25 22:55:55](https://github.com/leanprover-community/mathlib/commit/c363ad6)
feat(category_theory/sites/*): Cover preserving functors ([#9691](https://github.com/leanprover-community/mathlib/pull/9691))
Split from [#9650](https://github.com/leanprover-community/mathlib/pull/9650)
- Defined `cover_preserving` functors as functors that push covering sieves to covering sieves.
- Defined `compatible_preserving` functors as functors that push compatible families to compatible families.
- Proved that functors that are both `cover_preserving` and `compatible_preserving` pulls sheaves to sheaves.

### [2021-10-25 20:31:21](https://github.com/leanprover-community/mathlib/commit/5421200)
feat(group_theory/index): Small values of `subgroup.index` ([#9893](https://github.com/leanprover-community/mathlib/pull/9893))
`H.index = 1 ↔ H = ⊤` and related results.

### [2021-10-25 20:31:20](https://github.com/leanprover-community/mathlib/commit/880c7bd)
chore(linear_algebra/matrix): add fin expansions for trace and adjugate, and some trace lemmas ([#9884](https://github.com/leanprover-community/mathlib/pull/9884))
We have these expansions for `det` already, I figured we may as well have them for these.
This adds some other trivial trace lemmas while I'm touching the same file.

### [2021-10-25 20:31:19](https://github.com/leanprover-community/mathlib/commit/e808b41)
feat(data/matrix/basic): lemmas about transpose and conj_transpose on sums and products ([#9880](https://github.com/leanprover-community/mathlib/pull/9880))
This also generalizes some previous results from `star_ring` to `star_add_monoid` now that the latter exists.
To help prove the non-commutative statements, this adds `monoid_hom.unop_map_list_prod` and similar.
This could probably used for proving `star_list_prod` in future.

### [2021-10-25 17:43:11](https://github.com/leanprover-community/mathlib/commit/87fa12a)
chore(linear_algebra/matrix/nonsingular_inverse): replace `1 < fintype.card n` with `nontrivial n` ([#9953](https://github.com/leanprover-community/mathlib/pull/9953))
This likely makes this a better simp lemma

### [2021-10-25 17:43:10](https://github.com/leanprover-community/mathlib/commit/0d131fe)
chore(group_theory/submonoid): move a lemma to reduce imports ([#9951](https://github.com/leanprover-community/mathlib/pull/9951))
Currently, `algebra.pointwise` is a relatively "heavy" import (e.g., it depends on `data.set.finite`) and I want to use submonoid closures a bit earlier than that.

### [2021-10-25 17:43:09](https://github.com/leanprover-community/mathlib/commit/374885a)
feat(linear_algebra/matrix/nonsingular_inverse): lemmas about adjugate ([#9947](https://github.com/leanprover-community/mathlib/pull/9947))

### [2021-10-25 17:43:06](https://github.com/leanprover-community/mathlib/commit/c693682)
chore(analysis/normed/group/basic): make various norm instances computable ([#9946](https://github.com/leanprover-community/mathlib/pull/9946))
Instead of defining the default `edist` as `ennreal.of_real` which introduces an `ite` on an undecidable equality, this constructs the `ennreal` directly using a proof of non-negativity.
This removes `noncomputable theory` from some files so as to make it obvious from the source alone which definitions are and are not computable.

### [2021-10-25 17:43:03](https://github.com/leanprover-community/mathlib/commit/5fcbd2b)
chore(linear_algebra/matrix/nonsingular_inverse): use pi.single instead of ite ([#9944](https://github.com/leanprover-community/mathlib/pull/9944))

### [2021-10-25 17:43:01](https://github.com/leanprover-community/mathlib/commit/5778df8)
chore(analysis/complex/circle): upgrade `exp_map_circle` to `continuous_map` ([#9942](https://github.com/leanprover-community/mathlib/pull/9942))

### [2021-10-25 17:43:00](https://github.com/leanprover-community/mathlib/commit/2026a5f)
feat(measure_theory/measure): better `measure.restrict_singleton` ([#9936](https://github.com/leanprover-community/mathlib/pull/9936))
With new `restrict_singleton`, `simp` can simplify `∫ x in {a}, f x ∂μ`
to `(μ {a}).to_real • f a`.

### [2021-10-25 17:42:59](https://github.com/leanprover-community/mathlib/commit/8eb1c02)
feat(analysis/special_functions/pow): Equivalent conditions for zero powers ([#9897](https://github.com/leanprover-community/mathlib/pull/9897))
Lemmas for 0^x in the reals and complex numbers.

### [2021-10-25 17:42:58](https://github.com/leanprover-community/mathlib/commit/312db88)
feat(*): use `ordered_sub` instead of `nat.sub` lemmas  ([#9855](https://github.com/leanprover-community/mathlib/pull/9855))
* For all `nat.sub` lemmas in core, prefer to use the `has_ordered_sub` version.
* Most lemmas have an identical version for `has_ordered_sub`. In some cases we only have the symmetric version.
* Make arguments to `tsub_add_eq_tsub_tsub` and `tsub_add_eq_tsub_tsub_swap` explicit
* Rename `add_tsub_add_right_eq_tsub -> add_tsub_add_eq_tsub_right` (for consistency with the `_left` version)
* Rename `sub_mul' -> tsub_mul` and `mul_sub' -> mul_tsub` (these were forgotten in [#9793](https://github.com/leanprover-community/mathlib/pull/9793))
* Many of the fixes are to fix the identification of `n < m` and `n.succ \le m`.
* Add projection notation `h.nat_succ_le` for `nat.succ_le_of_lt h`.

### [2021-10-25 17:42:56](https://github.com/leanprover-community/mathlib/commit/f298c55)
refactor(linear_algebra/finite_dimensional): define finite_dimensional using module.finite ([#9854](https://github.com/leanprover-community/mathlib/pull/9854))
`finite_dimensional K V` is by definition `is_noetherian K V`. We refactor this to use everywhere `finite K V` instead.
To keep the PR reasonably small, we don't delete `finite_dimension`, but we define it as `module.finite`. In a future PR we will remove it.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)

### [2021-10-25 13:43:52](https://github.com/leanprover-community/mathlib/commit/3d457a2)
chore(topology/continuous_function): review API ([#9950](https://github.com/leanprover-community/mathlib/pull/9950))
* add `simps` config for `α →ᵇ β`;
* use better variable names in `topology.continuous_function.compact`;
* weaken some TC assumptions in `topology.continuous_function.compact`;
* migrate more API from `α →ᵇ β` to `C(α, β)`.

### [2021-10-25 13:43:51](https://github.com/leanprover-community/mathlib/commit/f23354d)
feat(linear_algebra/basic, ring_theory/ideal/basic): add span_insert ([#9941](https://github.com/leanprover-community/mathlib/pull/9941))

### [2021-10-25 10:59:45](https://github.com/leanprover-community/mathlib/commit/26c838f)
refactor(data/real/ennreal): remove ordered sub simp lemmas ([#9902](https://github.com/leanprover-community/mathlib/pull/9902))
* They are now simp lemmas in `algebra/order/sub`
* Squeeze some simps

### [2021-10-25 08:37:22](https://github.com/leanprover-community/mathlib/commit/dc1484e)
feat(ring_theory/polynomial/cyclotomic): add lemmas about evaluation of cyclotomic polynomials at one ([#9910](https://github.com/leanprover-community/mathlib/pull/9910))

### [2021-10-25 06:51:07](https://github.com/leanprover-community/mathlib/commit/7e53203)
chore(group_theory/submonoid/operations): golf a few proofs ([#9948](https://github.com/leanprover-community/mathlib/pull/9948))

### [2021-10-25 06:51:05](https://github.com/leanprover-community/mathlib/commit/bfcbe68)
feat(group_theory/subgroup/basic): `normalizer_eq_top` ([#9917](https://github.com/leanprover-community/mathlib/pull/9917))
The normalizer is the whole group if and only if the subgroup is normal.

### [2021-10-25 06:51:03](https://github.com/leanprover-community/mathlib/commit/41b90d7)
feat(group_theory/index): Second isomorphism theorem in terms of `relindex` ([#9915](https://github.com/leanprover-community/mathlib/pull/9915))
Restates the second isomorphism theorem in terms of `relindex`.

### [2021-10-25 05:13:27](https://github.com/leanprover-community/mathlib/commit/b9260f2)
feat(group_theory/subgroup/basic): `map_subtype_le` ([#9916](https://github.com/leanprover-community/mathlib/pull/9916))
A subgroup of a subgroup is `≤`.

### [2021-10-25 01:28:17](https://github.com/leanprover-community/mathlib/commit/951a60e)
chore(data/list/basic): golf a proof ([#9949](https://github.com/leanprover-community/mathlib/pull/9949))
Prove `list.mem_map` directly, get `list.exists_of_mem_map` and
`list.mem_map_of_mem` as corollaries.

### [2021-10-25 01:28:16](https://github.com/leanprover-community/mathlib/commit/264d33e)
docs(control/traversable/lemmas): Add module docstring ([#9927](https://github.com/leanprover-community/mathlib/pull/9927))

### [2021-10-24 22:52:58](https://github.com/leanprover-community/mathlib/commit/c4760b9)
feat(algebra/big_operators/basic): prod/sum over an empty type ([#9939](https://github.com/leanprover-community/mathlib/pull/9939))

### [2021-10-24 22:52:57](https://github.com/leanprover-community/mathlib/commit/f9da68c)
feat(*): a few more `fun_unique`s ([#9938](https://github.com/leanprover-community/mathlib/pull/9938))

### [2021-10-24 22:52:56](https://github.com/leanprover-community/mathlib/commit/942e60f)
chore(algebra/*/pi): add missing lemmas about function.update and set.piecewise ([#9935](https://github.com/leanprover-community/mathlib/pull/9935))
This adds `function.update_{zero,one,add,mul,sub,div,neg,inv,smul,vadd}`, and moves `pi.piecewise_{sub,div,neg,inv}` into the `set` namespace to match `set.piecewise_{add,mul}`.
This also adds `finset.piecewise_erase_univ`, as this is tangentially related.

### [2021-10-24 22:52:55](https://github.com/leanprover-community/mathlib/commit/1e7f6b9)
docs(control/bitraversable/instances): Add def docstrings ([#9931](https://github.com/leanprover-community/mathlib/pull/9931))

### [2021-10-24 22:52:54](https://github.com/leanprover-community/mathlib/commit/5d1e8f7)
docs(control/applicative): Add module docstring ([#9930](https://github.com/leanprover-community/mathlib/pull/9930))

### [2021-10-24 22:52:53](https://github.com/leanprover-community/mathlib/commit/6f1d45d)
docs(control/bitraversable/basic): Add defs docstrings ([#9929](https://github.com/leanprover-community/mathlib/pull/9929))

### [2021-10-24 22:52:52](https://github.com/leanprover-community/mathlib/commit/5642c62)
docs(control/traversable/equiv): Add module docstring ([#9928](https://github.com/leanprover-community/mathlib/pull/9928))

### [2021-10-24 22:52:51](https://github.com/leanprover-community/mathlib/commit/8c0b8c7)
feat(group_theory/subgroup/basic): Contrapositive of `card_le_one_iff_eq_bot` ([#9918](https://github.com/leanprover-community/mathlib/pull/9918))
Adds contrapositive of `card_le_one_iff_eq_bot`.

### [2021-10-24 22:52:50](https://github.com/leanprover-community/mathlib/commit/4468231)
feat(data/nat/log): Equivalent conditions for logarithms to equal zero and one ([#9903](https://github.com/leanprover-community/mathlib/pull/9903))
Add equivalent conditions for a `nat.log` to equal 0 or 1.

### [2021-10-24 22:52:49](https://github.com/leanprover-community/mathlib/commit/12515db)
feat(data/list): product of list.update_nth in terms of inverses ([#9800](https://github.com/leanprover-community/mathlib/pull/9800))
Expression for the product of `l.update_nth n x` in terms of inverses instead of `take` and `drop`, assuming a group instead of a monoid.

### [2021-10-24 22:06:49](https://github.com/leanprover-community/mathlib/commit/c20f08e)
feat(dynamics/ergodic/measure_preserving): add `measure_preserving.symm` ([#9940](https://github.com/leanprover-community/mathlib/pull/9940))
Also make the proof of `measure_preserving.skew_product` a bit more readable.

### [2021-10-24 22:06:48](https://github.com/leanprover-community/mathlib/commit/4ea8de9)
feat(measure_theory/integral): Divergence theorem for Bochner integral ([#9811](https://github.com/leanprover-community/mathlib/pull/9811))

### [2021-10-24 21:16:31](https://github.com/leanprover-community/mathlib/commit/a30e190)
split(analysis/normed_space/exponential): split file to minimize dependencies ([#9932](https://github.com/leanprover-community/mathlib/pull/9932))
As suggested by @urkud, this moves all the results depending on derivatives, `complex.exp` and `real.exp` to a new file `analysis/special_function/exponential`. That way the definitions of `exp` and `[complex, real].exp` are independent, which means we could eventually redefine the latter in terms of the former without breaking the import tree.

### [2021-10-24 16:04:22](https://github.com/leanprover-community/mathlib/commit/dc6b8e1)
feat(topology): add some lemmas ([#9907](https://github.com/leanprover-community/mathlib/pull/9907))
* From the sphere eversion project
* Add compositional version `continuous.fst` of `continuous_fst`, compare `measurable.fst`.
* Add `comp_continuous_at_iff` and `comp_continuous_at_iff'` for `homeomorph` (and for `inducing`).
* Add some variants of these (requested by review).

### [2021-10-24 13:34:54](https://github.com/leanprover-community/mathlib/commit/696f07f)
split(data/list/lattice): split off `data.list.basic` ([#9906](https://github.com/leanprover-community/mathlib/pull/9906))

### [2021-10-24 13:34:52](https://github.com/leanprover-community/mathlib/commit/9dc3b4d)
feat(topology/algebra/group): continuous div lemmas ([#9905](https://github.com/leanprover-community/mathlib/pull/9905))
* From the sphere eversion project
* There were already some lemmas about `sub`, now they also have multiplicative versions
* Add more lemmas about `div` being continuous
* Add `continuous_at.inv`
* Rename `nhds_translation` -> `nhds_translation_sub`.

### [2021-10-24 10:50:08](https://github.com/leanprover-community/mathlib/commit/be94800)
feat(data/real/nnreal): use the nonneg instance ([#9701](https://github.com/leanprover-community/mathlib/pull/9701))
... to show that `nnreal` forms a conditionally complete linear order with bot.
This requires some fixes in the order hierarchy.
* orders on subtypes are now obtained by lifting `coe` instead of `subtype.val`. This has the nice side benefit that some proofs became simpler.
* `subset_conditionally_complete_linear_order` is now reducible

### [2021-10-24 08:26:39](https://github.com/leanprover-community/mathlib/commit/416edee)
feat(analysis/normed_space/is_R_or_C): add three lemmas on bounds of linear maps over is_R_or_C. ([#9827](https://github.com/leanprover-community/mathlib/pull/9827))
Adding lemmas `linear_map.bound_of_sphere_bound`, `linear_map.bound_of_ball_bound`, `continuous_linear_map.op_norm_bound_of_ball_bound` as a preparation of a PR on Banach-Alaoglu theorem.

### [2021-10-24 03:33:39](https://github.com/leanprover-community/mathlib/commit/ecc544e)
chore(scripts): update nolints.txt ([#9923](https://github.com/leanprover-community/mathlib/pull/9923))
I am happy to remove some nolints for you!

### [2021-10-24 03:33:38](https://github.com/leanprover-community/mathlib/commit/e836a72)
feat(order/galois_connection): add `exists_eq_{l,u}`, tidy up lemmas ([#9904](https://github.com/leanprover-community/mathlib/pull/9904))
This makes some arguments implicit to `compose` as these are inferrable from the other arguments, and changes `u_l_u_eq_u` and `l_u_l_eq_l` to be applied rather than unapplied, which shortens both the proof and the places where the lemma is used.

### [2021-10-24 03:33:37](https://github.com/leanprover-community/mathlib/commit/49c6841)
chore(topology): generalize `real.image_Icc` etc ([#9784](https://github.com/leanprover-community/mathlib/pull/9784))
* add lemmas about `Ici`/`Iic`/`Icc` in `α × β`;
* introduce a typeclass for `is_compact_Icc` so that the same lemma works for `ℝ` and `ℝⁿ`;
* generalize `real.image_Icc` etc to a conditionally complete linear order (e.g., now it works for `nnreal`, `ennreal`, `ereal`), move these lemmas to the `continuous_on` namespace.

### [2021-10-24 01:53:46](https://github.com/leanprover-community/mathlib/commit/55a1160)
feat(linear_algebra): add notation for star-linear maps ([#9875](https://github.com/leanprover-community/mathlib/pull/9875))
This PR adds the notation `M →ₗ⋆[R] N`, `M ≃ₗ⋆[R] N`, etc, to denote star-linear maps/equivalences, i.e. semilinear maps where the ring hom is `star`. A special case of this are conjugate-linear maps when `R = ℂ`.

### [2021-10-24 00:37:39](https://github.com/leanprover-community/mathlib/commit/5ec1572)
feat(nat/choose/central): definition of the central binomial coefficient, and bounds ([#9753](https://github.com/leanprover-community/mathlib/pull/9753))
Two exponential lower bounds on the central binomial coefficient.

### [2021-10-24 00:37:37](https://github.com/leanprover-community/mathlib/commit/d788647)
feat(ring_theory): generalize `adjoin_root.power_basis` ([#9536](https://github.com/leanprover-community/mathlib/pull/9536))
Now we only need that `g` is monic to state that `adjoin_root g` has a power basis. Note that this does not quite imply the result of [#9529](https://github.com/leanprover-community/mathlib/pull/9529): this is phrased in terms of `minpoly R (root g)` and the other PR in terms of `g` itself, so I don't have a direct use for the current PR. However, it seems useful enough to have this statement, so I PR'd it anyway.

### [2021-10-23 22:10:47](https://github.com/leanprover-community/mathlib/commit/928d0e0)
docs(data/dlist/instances): Add module docstring ([#9912](https://github.com/leanprover-community/mathlib/pull/9912))

### [2021-10-23 22:10:46](https://github.com/leanprover-community/mathlib/commit/15161e9)
docs(data/list/sigma): Add missing def dosctrings, expand module docs ([#9909](https://github.com/leanprover-community/mathlib/pull/9909))

### [2021-10-23 22:10:45](https://github.com/leanprover-community/mathlib/commit/75b1a94)
refactor(analysis/special_functions/exp_log): split into 4 files ([#9882](https://github.com/leanprover-community/mathlib/pull/9882))

### [2021-10-23 22:10:44](https://github.com/leanprover-community/mathlib/commit/59db903)
feat(topology/metric_space/lipschitz): continuity on product of continuity in 1 var and Lipschitz continuity in another ([#9758](https://github.com/leanprover-community/mathlib/pull/9758))
Also apply the new lemma to `continuous_bounded_map`s and add a few lemmas there.

### [2021-10-23 20:04:35](https://github.com/leanprover-community/mathlib/commit/939e8b9)
docs(control/traversable/instances): Add module docstring ([#9913](https://github.com/leanprover-community/mathlib/pull/9913))

### [2021-10-23 20:04:34](https://github.com/leanprover-community/mathlib/commit/14b998b)
docs(control/bifunctor): Add module and defs docstrings ([#9911](https://github.com/leanprover-community/mathlib/pull/9911))

### [2021-10-23 20:04:33](https://github.com/leanprover-community/mathlib/commit/78252a3)
chore(data/real/sqrt): A couple of lemmas about sqrt ([#9892](https://github.com/leanprover-community/mathlib/pull/9892))
Add a couple of lemmas about `sqrt x / x`.

### [2021-10-23 20:04:32](https://github.com/leanprover-community/mathlib/commit/3f58dc7)
feat(linear_algebra/free_module/pid): golf basis.card_le_card_of_linear_independent_aux ([#9813](https://github.com/leanprover-community/mathlib/pull/9813))
We go from a 70 lines proof to a one line proof.

### [2021-10-23 20:04:31](https://github.com/leanprover-community/mathlib/commit/fc3c056)
chore(data/real): make more instances on real, nnreal, and ennreal computable ([#9806](https://github.com/leanprover-community/mathlib/pull/9806))
This makes it possible to talk about the add_monoid structure of nnreal and ennreal without worrying about computability.
To make it clear exactly which operations are computable, we remove `noncomputable theory`.

### [2021-10-23 17:11:13](https://github.com/leanprover-community/mathlib/commit/5c5d818)
chore(data/fintype/basic): make units.fintype computable ([#9846](https://github.com/leanprover-community/mathlib/pull/9846))
This also:
* renames `equiv.units_equiv_ne_zero` to `units_equiv_ne_zero`, and resolves the TODO comment about generalization
* renames and generalizes `finite_field.card_units` to `fintype.card_units`, and proves it right next to the fintype instance
* generalizes some typeclass assumptions in `finite_field.basic` as the linter already required me to tweak them

### [2021-10-23 17:11:12](https://github.com/leanprover-community/mathlib/commit/36f8c1d)
refactor(order/filter/bases): turn `is_countably_generated` into a class ([#9838](https://github.com/leanprover-community/mathlib/pull/9838))
## API changes
### Filters
* turn `filter.is_countably_generated` into a class, turn some lemmas into instances;
* remove definition/lemmas (all were in the `filter.is_countably_generated` namespace): `generating_set`, `countable_generating_set`, `eq_generate`, `countable_filter_basis`, `filter_basis_filter`, `has_countable_basis`, `exists_countable_infi_principal`, `exists_seq`;
* rename `filter.is_countably_generated.exists_antitone_subbasis` to `filter.has_basis.exists_antitone_subbasis`;
* rename `filter.is_countably_generated.exists_antitone_basis` to `filter.exists_antitone_basis`;
* rename `filter.is_countably_generated.exists_antitone_seq'` to `filter.exists_antitone_seq`;
* rename `filter.is_countably_generated.exists_seq` to `filter.exists_antitone_eq_infi_principal`;
* rename `filter.is_countably_generated.tendsto_iff_seq_tendsto` to `filter.tendsto_iff_seq_tendsto`;
* rename `filter.is_countably_generated.tendsto_of_seq_tendsto` to `filter.tendsto_of_seq_tendsto`;
* slightly generalize `is_countably_generated_at_top` and `is_countably_generated_at_bot`;
* add `filter.generate_eq_binfi`;
### Topology
* merge `is_closed.is_Gδ` with `is_closed.is_Gδ'`;
* merge `is_Gδ_set_of_continuous_at_of_countably_generated_uniformity` with `is_Gδ_set_of_continuous_at`;
* merge `is_lub.exists_seq_strict_mono_tendsto_of_not_mem'` with `is_lub.exists_seq_strict_mono_tendsto_of_not_mem`;
* merge `is_lub.exists_seq_monotone_tendsto'` with `is_lub.exists_seq_monotone_tendsto`;
* merge `is_glb.exists_seq_strict_anti_tendsto_of_not_mem'` with `is_glb.exists_seq_strict_anti_tendsto_of_not_mem`;
* merge `is_glb.exists_seq_antitone_tendsto'` with `is_glb.exists_seq_antitone_tendsto`;
* drop `emetric.first_countable_topology`, turn `uniform_space.first_countable_topology` into an instance;
* drop `emetric.second_countable_of_separable`, use `uniform_space.second_countable_of_separable` instead;
* drop `metric.compact_iff_seq_compact`, use `uniform_space.compact_iff_seq_compact` instead;
* drop `metric.compact_space_iff_seq_compact_space`, use `uniform_space.compact_space_iff_seq_compact_space` instead;
## Measure theory and integrals
Various lemmas assume `[is_countably_generated l]` instead of `(h : is_countably_generated l)`.

### [2021-10-23 17:11:11](https://github.com/leanprover-community/mathlib/commit/d0d1520)
chore(ring_theory/derivation): add `leibniz_pow` and `leibniz_inv` ([#9837](https://github.com/leanprover-community/mathlib/pull/9837))

### [2021-10-23 17:11:09](https://github.com/leanprover-community/mathlib/commit/1ebea89)
feat(field_theory/finite/galois_field): finite fields with the same cardinality are isomorphic ([#9834](https://github.com/leanprover-community/mathlib/pull/9834))
Added the isomorphism of finite fields of the same cardinality.

### [2021-10-23 17:11:08](https://github.com/leanprover-community/mathlib/commit/0411b1e)
feat(ring_theory/ideal): `simp` lemmas for `ideal.quotient.mk` + `algebra_map` ([#9829](https://github.com/leanprover-community/mathlib/pull/9829))
Some `simp` lemmas I needed for combining `algebra_map` with `ideal.quotient.mk`. This also allowed me to golf two existing proofs.

### [2021-10-23 17:11:07](https://github.com/leanprover-community/mathlib/commit/44ab28e)
refactor(linear_algebra/free_module/finite): move to a new folder ([#9821](https://github.com/leanprover-community/mathlib/pull/9821))
We move `linear_algebra/free_module/finite` to `linear_algebra/free_module/finite/basic`.
We also move two lemmas from `linear_algebra/free_module/finite/basic` to `linear_algebra/free_module/basic`, since they don't need any finiteness assumption on the modules.

### [2021-10-23 14:30:44](https://github.com/leanprover-community/mathlib/commit/a58ae54)
chore(algebra/big_operators/finprod): remove outdated todo ([#9900](https://github.com/leanprover-community/mathlib/pull/9900))

### [2021-10-23 14:30:43](https://github.com/leanprover-community/mathlib/commit/bd81d55)
feat(data/finsupp): add lemmas about `single` ([#9894](https://github.com/leanprover-community/mathlib/pull/9894))
These are subset versions of the four lemmas related to `support_eq_singleton`.

### [2021-10-23 14:30:42](https://github.com/leanprover-community/mathlib/commit/95535a3)
refactor(ring_theory/unique_factorization_domain): golf some factor_set lemmas ([#9889](https://github.com/leanprover-community/mathlib/pull/9889))

### [2021-10-23 14:30:41](https://github.com/leanprover-community/mathlib/commit/e1c0dbc)
feat(set_theory/cardinal): add `add_le_omega` ([#9887](https://github.com/leanprover-community/mathlib/pull/9887))
* simplify `c₁ + c₂ ≤ ω` to `c₁ ≤ ω ∧ c₂ ≤ ω`;
* simplify `ω + ω` to `ω`;
* simplify `#s ≤ ω` to `s.countable`;
* simplify `(s ∪ t).countable` and `(insert a s).countable`.
Motivated by lemmas from flypitch.

### [2021-10-23 14:30:40](https://github.com/leanprover-community/mathlib/commit/82896b5)
feat(topology): add a few lemmas ([#9885](https://github.com/leanprover-community/mathlib/pull/9885))
Add `is_topological_basis.is_open_map_iff`,
`is_topological_basis.exists_nonempty_subset`, and
`interior_{s,b,}Inter_subset`.
Motivated by lemmas from `flypitch`.

### [2021-10-23 14:30:39](https://github.com/leanprover-community/mathlib/commit/1e0661c)
feat(ring_theory/noetherian): generalize to semiring ([#9881](https://github.com/leanprover-community/mathlib/pull/9881))
We generalize some of the results in `ring_theory/noetherian` to `semiring`.
- [x] depends on: [#9860](https://github.com/leanprover-community/mathlib/pull/9860)

### [2021-10-23 14:30:38](https://github.com/leanprover-community/mathlib/commit/bb71667)
feat(topology/instances/irrational): new file ([#9872](https://github.com/leanprover-community/mathlib/pull/9872))
* move `is_Gδ_irrational` etc to a new file `topology.instances.irrational`;
* prove that a small ball around an irrational number is disjoint with the set of rational numbers with bounded denominators;
* prove `order_topology`, `no_top_order`, `no_bot_order`, and `densely_ordered` instances for `{x // irrational x}`.

### [2021-10-23 14:30:37](https://github.com/leanprover-community/mathlib/commit/b877f6b)
chore(analysis/normed/group): generalize `cauchy_seq.add` ([#9868](https://github.com/leanprover-community/mathlib/pull/9868))
Also golf a few proofs.

### [2021-10-23 14:30:36](https://github.com/leanprover-community/mathlib/commit/29c7266)
refactor(linear_algebra/matrix/nonsingular_inverse): use ring.inverse in matrix.has_inv ([#9863](https://github.com/leanprover-community/mathlib/pull/9863))
This makes some of the proofs a little shorter.
Independently, this removes an assumption from `matrix.transpose_nonsing_inv`.
This adds the missing `units.is_unit_units_mul` to complement the existing `units.is_unit_mul_units`, even though it ultimately was not used in this PR.
This removes the def `matrix.nonsing_inv` in favor of just using `has_inv.inv` directly. Having two ways to spell the same thing isn't helpful here.

### [2021-10-23 14:30:35](https://github.com/leanprover-community/mathlib/commit/2a1f454)
refactor(algebra/algebra): choose `coe` as the normal form for the map `alg_equiv → ring_equiv` ([#9848](https://github.com/leanprover-community/mathlib/pull/9848))
We never chose a `simp`-normal form for this map, resulting in some duplicate work and annoying `show _ = _, from rfl` when rewriting. I picked this choice because it matches the convention for the map `alg_hom → ring_hom`.
Very surprisingly, there were absolutely no CI failures due to this choice.

### [2021-10-23 14:30:34](https://github.com/leanprover-community/mathlib/commit/5f11361)
refactor(algebra/continued_fractions): remove use of open ... as ([#9847](https://github.com/leanprover-community/mathlib/pull/9847))
Lean 4 doesn't support the use of `open ... as ...`, so let's get rid of the few uses from mathlib rather than automating it in mathport.

### [2021-10-23 13:13:59](https://github.com/leanprover-community/mathlib/commit/7b979aa)
move(algebra/order/*): More algebraic order files in the correct place ([#9899](https://github.com/leanprover-community/mathlib/pull/9899))
`algebra.module.ordered` and `algebra.algebra.ordered` were really continuations of `algebra.order.smul` (the first being quite literally the same with additive inverses), so it makes sense to bring them closer. `algebra.floor` and `algebra.archimedean` also perfectly qualify for the subfolder.

### [2021-10-23 08:22:49](https://github.com/leanprover-community/mathlib/commit/eb1e037)
doc(algebra/ring): correct docs for surjective pushforwards ([#9896](https://github.com/leanprover-community/mathlib/pull/9896))

### [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/a75f762)
feat(ring_theory/localization): generalize `exist_integer_multiples` to finite families ([#9859](https://github.com/leanprover-community/mathlib/pull/9859))
This PR shows we can clear denominators of finitely-indexed collections of fractions (i.e. elements of `S` where `is_localization M S`), with the existing result about finite sets of fractions as a special case.

### [2021-10-23 08:22:48](https://github.com/leanprover-community/mathlib/commit/294ce35)
fix(algebra/module/submodule): fix incorrectly generalized arguments to `smul_mem_iff'` and `smul_of_tower_mem` ([#9851](https://github.com/leanprover-community/mathlib/pull/9851))
These put unnecessary requirements on `S`.

### [2021-10-23 08:22:47](https://github.com/leanprover-community/mathlib/commit/2cbd4ba)
feat(group_theory/index): `relindex_dvd_of_le_left` ([#9835](https://github.com/leanprover-community/mathlib/pull/9835))
If `H ≤ K`, then `K.relindex L ∣ H.relindex L`.
Caution: `relindex_dvd_of_le_right` is not true. `relindex_le_of_le_right` is true, but it is harder to prove, and harder to state (because you have to be careful about `relindex = 0`).

### [2021-10-23 05:53:41](https://github.com/leanprover-community/mathlib/commit/183b8c8)
refactor(data/list/defs): move defs about rb_map ([#9844](https://github.com/leanprover-community/mathlib/pull/9844))
There is nothing intrinsically `meta` about `rb_map`, but in practice in mathlib we prove nothing about it and only use it in tactic infrastructure. This PR moves a definition involving `rb_map` out of `data.list.defs` and into `meta.rb_map` (where many others already exist).
(motivated by mathport; rb_map is of course disappearing/changing, so better to quarantine this stuff off with other things that aren't being automatically ported)
`rbmap` is not related to `rb_map`. It can likely be moved from core to mathlib entirely.

### [2021-10-23 02:55:56](https://github.com/leanprover-community/mathlib/commit/45ba2ad)
chore(scripts): update nolints.txt ([#9895](https://github.com/leanprover-community/mathlib/pull/9895))
I am happy to remove some nolints for you!

### [2021-10-22 22:06:02](https://github.com/leanprover-community/mathlib/commit/7690e0a)
chore(order/complete_lattice): add `(supr|infi)_option_elim` ([#9886](https://github.com/leanprover-community/mathlib/pull/9886))
Motivated by `supr_option'` and `infi_option'` from `flypitch`.

### [2021-10-22 20:15:57](https://github.com/leanprover-community/mathlib/commit/72c20fa)
feat(analysis/special_functions/exp_log): Classify when log is zero ([#9815](https://github.com/leanprover-community/mathlib/pull/9815))
Classify when the real `log` function is zero.

### [2021-10-22 15:58:28](https://github.com/leanprover-community/mathlib/commit/d23b833)
chore(data/set/lattice): add `@[simp]` to a few lemmas ([#9883](https://github.com/leanprover-community/mathlib/pull/9883))
Add `@[simp]` to `Union_subset_iff`, `subset_Inter_iff`,
`sUnion_subset_iff`, and `subset_sInter_iff` (new lemma).

### [2021-10-22 15:58:26](https://github.com/leanprover-community/mathlib/commit/3d237db)
feat(linear_algebra/matrix/determinant): det_conj_transpose ([#9879](https://github.com/leanprover-community/mathlib/pull/9879))
Also:
* Makes the arguments of `ring_hom.map_det` and `alg_hom.map_det` explicit, and removes them from the `matrix` namespace to enable dot notation.
* Adds `ring_equiv.map_det` and `alg_equiv.map_det`

### [2021-10-22 15:58:25](https://github.com/leanprover-community/mathlib/commit/20bb02f)
feat(data/fintype/basic): `fintype.card_pos` ([#9876](https://github.com/leanprover-community/mathlib/pull/9876))
Two lemmas `fintype.card_pos` and `fintype.card_ne_zero` that are often easier to use than `fintype.card_pos_iff`.

### [2021-10-22 15:58:24](https://github.com/leanprover-community/mathlib/commit/22c7474)
feat(algebra/module/basic): a few more instances ([#9871](https://github.com/leanprover-community/mathlib/pull/9871))
* generalize `is_scalar_tower.rat`;
* add `smul_comm_class.rat` and `smul_comm_class.rat'`;
* golf a few proofs.

### [2021-10-22 15:58:23](https://github.com/leanprover-community/mathlib/commit/87ea780)
chore(set_theory/cardinal): use `protected` instead of `private` ([#9869](https://github.com/leanprover-community/mathlib/pull/9869))
Also use `mk_congr`.

### [2021-10-22 15:58:21](https://github.com/leanprover-community/mathlib/commit/d8b9259)
feat(*): add various divisibility-related lemmas ([#9866](https://github.com/leanprover-community/mathlib/pull/9866))

### [2021-10-22 15:58:20](https://github.com/leanprover-community/mathlib/commit/2955306)
feat(ring_theory/finiteness): generalize module.finite to noncommutative setting ([#9860](https://github.com/leanprover-community/mathlib/pull/9860))
An almost for free generalization of `module.finite` to `semiring`.

### [2021-10-22 15:58:19](https://github.com/leanprover-community/mathlib/commit/0a7f448)
chore(group_theory/congruence): lower priority for `con.quotient.decidable_eq` ([#9826](https://github.com/leanprover-community/mathlib/pull/9826))
I was debugging some slow typeclass searches, and it turns out (`add_`)`con.quotient.decidable_eq` wants to be applied to all quotient types, causing a search for a `has_mul` instance before the elaborator can try unifying the `con.to_setoid` relation with the quotient type's relation, so e.g. `decidable_eq (multiset α)` first tries going all the way up to searching for a `linear_ordered_normed_etc_field (list α)` before even trying `multiset.decidable_eq`.
Another approach would be to make `multiset` and/or `con.quotient` irreducible, but that would require a lot more work to ensure we don't break the irreducibility barrier.

### [2021-10-22 15:58:17](https://github.com/leanprover-community/mathlib/commit/03ba4cc)
feat(algebra/floor): Floor semirings ([#9592](https://github.com/leanprover-community/mathlib/pull/9592))
A floor semiring is a semiring equipped with a `floor` and a `ceil` function.

### [2021-10-22 13:16:18](https://github.com/leanprover-community/mathlib/commit/bee8d4a)
chore(order/filter/basic): golf a proof ([#9874](https://github.com/leanprover-community/mathlib/pull/9874))

### [2021-10-22 13:16:16](https://github.com/leanprover-community/mathlib/commit/b812fb9)
refactor(ring_theory/ideal): split off `quotient.lean` ([#9850](https://github.com/leanprover-community/mathlib/pull/9850))
Both `ring_theory/ideal/basic.lean` and `ring_theory/ideal/operations.lean` were starting to get a bit long, so I split off the definition of `ideal.quotient` and the results that had no further dependencies.
I also went through all the imports for files depending on either `ideal/basic.lean` or `ideal/operations.lean` to check whether they shouldn't depend on `ideal/quotient.lean` instead.

### [2021-10-22 13:16:15](https://github.com/leanprover-community/mathlib/commit/e6c516d)
feat(topology/maps): Characterize open/closed maps in terms of images of interior/closure ([#9814](https://github.com/leanprover-community/mathlib/pull/9814))
Also provide the docstring for `inducing`.

### [2021-10-22 10:49:49](https://github.com/leanprover-community/mathlib/commit/43cd79f)
feat(data/finset/basic): Simple `finset.erase` lemmas ([#9878](https://github.com/leanprover-community/mathlib/pull/9878))
`finset.erase.singleton` and `finset.(map/image)_erase`

### [2021-10-22 06:47:53](https://github.com/leanprover-community/mathlib/commit/76212e6)
feat(measure_theory/integral/set_integral): integral of a `is_R_or_C` function equals integral of real part + integral of imaginary part ([#9735](https://github.com/leanprover-community/mathlib/pull/9735))

### [2021-10-22 01:15:49](https://github.com/leanprover-community/mathlib/commit/c4c71d2)
feat(topology): define class `[noncompact_space]` ([#9839](https://github.com/leanprover-community/mathlib/pull/9839))

### [2021-10-21 23:04:20](https://github.com/leanprover-community/mathlib/commit/6f837a6)
feat(data/polynomial): generalize and rename `polynomial.normalize_monic` ([#9853](https://github.com/leanprover-community/mathlib/pull/9853))
This PR renames `polynomial.normalize_monic` to `polynomial.monic.normalize_eq_self` (more dot notation!) and generalizes it from fields to `normalization_monoid`s.

### [2021-10-21 23:04:19](https://github.com/leanprover-community/mathlib/commit/16a9031)
refactor(data/complex/*): replace `complex.conj` and `is_R_or_C.conj` with star ([#9640](https://github.com/leanprover-community/mathlib/pull/9640))
This PR replaces `complex.conj` and `is_R_or_C.conj` by the star operation defined in `algebra/star`. Both of these are replaced with `star_ring_aut`, which is also made available under the notation `conj` defined in the locale `complex_conjugate`. This effectively also upgrades conj from a `ring_hom` to a `ring_aut`.
Fixes [#9421](https://github.com/leanprover-community/mathlib/pull/9421)

### [2021-10-21 20:06:24](https://github.com/leanprover-community/mathlib/commit/912039d)
feat(algebra/group_power/lemmas): Positivity of an odd/even power ([#9796](https://github.com/leanprover-community/mathlib/pull/9796))
This adds `odd.pow_nonneg` and co and `pow_right_comm`.
This also deletes `pow_odd_nonneg` and `pow_odd_pos` as they are special cases of `pow_nonneg` and `pow_pos`.
To make dot notation work, this renames `(pow/fpow)_(odd/even)_(nonneg/nonpos/pos/neg/abs)` to `(odd/even).(pow/fpow)_(nonneg/nonpos/pos/neg/abs)`

### [2021-10-21 18:28:20](https://github.com/leanprover-community/mathlib/commit/15d4e5f)
refactor(data/real/ennreal): remove sub lemmas ([#9857](https://github.com/leanprover-community/mathlib/pull/9857))
* Remove all lemmas about subtraction on `ennreal` that are special cases of `has_ordered_sub` lemmas.
* [This](https://github.com/leanprover-community/mathlib/blob/fe5ddaf42c5d61ecc740e815d63ac38f5e94a2e8/src/data/real/ennreal.lean#L734-L795) gives a list of renamings.
* The lemmas that have a `@[simp]` attribute will be done in a separate PR

### [2021-10-21 18:28:19](https://github.com/leanprover-community/mathlib/commit/5b72c4e)
feat(linear_algebra/quotient): `S.restrict_scalars.quotient` is `S.quotient` ([#9535](https://github.com/leanprover-community/mathlib/pull/9535))
This PR adds a more general module instance on submodule quotients, in order to show that `(S.restrict_scalars R).quotient` is equivalent to `S.quotient`. If we decide this instance is not a good idea, I can write it instead as `S.quotient.restrict_scalars`, but that is a bit less convenient to work with.

### [2021-10-21 15:43:25](https://github.com/leanprover-community/mathlib/commit/9be8247)
feat(logic/function/embedding): add `function.embedding.option_elim` ([#9841](https://github.com/leanprover-community/mathlib/pull/9841))
* add `option.injective_iff`;
* add `function.embedding.option_elim`;
* use it in the proof of `cardinal.add_one_le_succ`;
* add `function.embedding.cardinal_le`, `cardinal.succ_pos`;
* add `@[simp]` to `cardinal.lt_succ`.

### [2021-10-21 15:43:23](https://github.com/leanprover-community/mathlib/commit/14ec1c8)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate of a 2x2 matrix ([#9830](https://github.com/leanprover-community/mathlib/pull/9830))
Since we have `det_fin_two`, let's have `adjugate_fin_two` as well.

### [2021-10-21 15:43:20](https://github.com/leanprover-community/mathlib/commit/9c240b5)
feat(analysis/inner_product_space): define `orthogonal_family` of subspaces ([#9718](https://github.com/leanprover-community/mathlib/pull/9718))
Define `orthogonal_family` on `V : ι → submodule 𝕜 E` to mean that any two vectors from distinct subspaces are orthogonal.  Prove that an orthogonal family of subspaces is `complete_lattice.independent`.
Also prove that in finite dimension an orthogonal family `V` satisifies `direct_sum.submodule_is_internal` (i.e., it provides an internal direct sum decomposition of `E`) if and only if their joint orthogonal complement is trivial, `(supr V)ᗮ = ⊥`, and that in this case, the identification of `E` with the direct sum of `V` is an isometry.

### [2021-10-21 13:16:18](https://github.com/leanprover-community/mathlib/commit/d8096aa)
fix(ring_theory/subring): `inclusion` is a ring_hom! ([#9849](https://github.com/leanprover-community/mathlib/pull/9849))

### [2021-10-21 13:16:17](https://github.com/leanprover-community/mathlib/commit/d8b0d1a)
chore(algebra/big_operators): avoid 'abel' tactic ([#9833](https://github.com/leanprover-community/mathlib/pull/9833))
I'd like to add an import ` algebra.euclidean_domain` → `algebra.associated` in [#9606](https://github.com/leanprover-community/mathlib/pull/9606), so this removes the dependency in the other direction (`algebra.associated` → `algebra.big_operators.basic` → `tactic.abel` → `tactic.norm_num` → `data.rat.cast` → `data.rat.order` → `data.rat.basic` → ` algebra.euclidean_domain`). Fortunately, the dependency on `abel` was quite shallow here.

### [2021-10-21 13:16:16](https://github.com/leanprover-community/mathlib/commit/de13786)
chore(topology/algebra/ordered): move IVT to a new file ([#9792](https://github.com/leanprover-community/mathlib/pull/9792))

### [2021-10-21 13:16:14](https://github.com/leanprover-community/mathlib/commit/d9daf54)
feat(topology/metric_space/isometry): add simps config ([#9757](https://github.com/leanprover-community/mathlib/pull/9757))
Also make `isometric.complete_space` take `complete_space β` as an instance argument.

### [2021-10-21 11:25:37](https://github.com/leanprover-community/mathlib/commit/fe5ddaf)
feat(ring_theory/polynomial/cyclotomic): add cyclotomic_prime_pow_eq_geom_sum and supporting lemmas ([#9845](https://github.com/leanprover-community/mathlib/pull/9845))
Clean up a little bit in src/number_theory/divisors.lean using to_additive too.

### [2021-10-21 11:25:35](https://github.com/leanprover-community/mathlib/commit/edd801f)
chore(set_theory/cardinal): ensure `c ^ ↑n = c ^ n` is definitional ([#9842](https://github.com/leanprover-community/mathlib/pull/9842))

### [2021-10-21 11:25:33](https://github.com/leanprover-community/mathlib/commit/777f11c)
feat(group_theory/index): Special cases of relindex ([#9831](https://github.com/leanprover-community/mathlib/pull/9831))
Adds special cases of relindex. Also refactors the file to use `nat.card`, rather than the equivalent `(# _).to_nat`.

### [2021-10-21 11:25:32](https://github.com/leanprover-community/mathlib/commit/bfa4010)
feat(data/nat/modeq): `modeq.le_of_lt_add` ([#9816](https://github.com/leanprover-community/mathlib/pull/9816))
If `a ≡ b [MOD m]` and `a < b + m`, then `a ≤ b`.

### [2021-10-21 08:38:42](https://github.com/leanprover-community/mathlib/commit/da01792)
refactor(*): remove integral_domain, rename domain to is_domain ([#9748](https://github.com/leanprover-community/mathlib/pull/9748))

### [2021-10-21 02:55:10](https://github.com/leanprover-community/mathlib/commit/3c11bd7)
chore(*): bump to lean 3.34.0 ([#9824](https://github.com/leanprover-community/mathlib/pull/9824))
### Backport coercions from Lean 4
Now `has_coe_to_fun` and `has_coe_to_sort` take the output type as an `out_param` argument. This change comes with some changes in the elaboration order, so some proofs/definitions need more type annotations.
### Smarter `by_contra`
Now `by_contra h` does better job if the goal is a negation.
### `open` and current namespace
In
```lean
namespace A
open B _root_.C
end A
```
Lean will try to open `A.B`; if this fails, it will open `B`. It will also open `C`.
`setup_tactic_parser_cmd` command was updated to open appropriate `_root_.*` namespaces.

### [2021-10-20 19:43:22](https://github.com/leanprover-community/mathlib/commit/8366f93)
feat(ring_theory/integral_domain): finite domains are division rings ([#9823](https://github.com/leanprover-community/mathlib/pull/9823))
TODO: Prove Wedderburn's little theorem
which shows a finite domain is in fact commutative, hence a field.

### [2021-10-20 18:03:33](https://github.com/leanprover-community/mathlib/commit/4ebeb05)
chore(group_theory/submonoid/center): add decidable_mem_center ([#9825](https://github.com/leanprover-community/mathlib/pull/9825))

### [2021-10-20 18:03:31](https://github.com/leanprover-community/mathlib/commit/3d00081)
feat(group_theory/index): Index of top and bottom subgroups ([#9819](https://github.com/leanprover-community/mathlib/pull/9819))
This PR computes the index of the top and bottom subgroups.

### [2021-10-20 15:39:06](https://github.com/leanprover-community/mathlib/commit/68a674e)
refactor(algebra/order/sub): rename sub -> tsub ([#9793](https://github.com/leanprover-community/mathlib/pull/9793))
* Renames lemmas in the file `algebra/order/sub` to use `tsub` instead of `sub` in the name
* Remove primes from lemma names where possible
* [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_lt_mul'''')
* Remove `sub_mul_ge`, `mul_sub_ge` and `lt_sub_iff_lt_sub`. They were special cases of `le_sub_mul`, `le_mul_sub` and `lt_sub_comm`, respectively.

### [2021-10-20 13:23:09](https://github.com/leanprover-community/mathlib/commit/5223e26)
feat(field_theory/finite/galois_field): uniqueness of finite fields ([#9817](https://github.com/leanprover-community/mathlib/pull/9817))
Every finite field is isomorphic to some Galois field. Closes [#9599](https://github.com/leanprover-community/mathlib/pull/9599)

### [2021-10-20 11:46:43](https://github.com/leanprover-community/mathlib/commit/49ab444)
fix(algebra/module/submodule_lattice): correct bad lemma ([#9809](https://github.com/leanprover-community/mathlib/pull/9809))
This lemma was accidentally stating that inf and inter are the same on sets, and wasn't about submodule at all.
The old statement was `↑p ⊓ ↑q = ↑p ∩ ↑q`, the new one is `↑(p ⊓ q) = ↑p ∩ ↑q`

### [2021-10-20 09:53:23](https://github.com/leanprover-community/mathlib/commit/24901dd)
feat(linear_algebra/free_module/rank): rank of free modules  ([#9810](https://github.com/leanprover-community/mathlib/pull/9810))
This file contains a basic API for the rank of free modules.
We will add the results for finite free modules in a future PR.

### [2021-10-20 09:53:22](https://github.com/leanprover-community/mathlib/commit/2f54840)
refactor(*): replace comm_ring/integral_domain with ring/domain where possible ([#9739](https://github.com/leanprover-community/mathlib/pull/9739))

### [2021-10-20 08:19:58](https://github.com/leanprover-community/mathlib/commit/a6d5ba8)
chore(set_theory/cardinal): add `map`, `induction_on` etc ([#9812](https://github.com/leanprover-community/mathlib/pull/9812))

### [2021-10-20 04:15:08](https://github.com/leanprover-community/mathlib/commit/9dafdf7)
feat(group_theory/subgroup/basic): `subgroup_of_self` ([#9818](https://github.com/leanprover-community/mathlib/pull/9818))
A subgroup is the top subgroup of itself.

### [2021-10-20 04:15:07](https://github.com/leanprover-community/mathlib/commit/6898728)
feat(analysis/complex/basic): a complex-valued function `has_sum` iff its real part and imaginary part `has_sum` ([#9648](https://github.com/leanprover-community/mathlib/pull/9648))

### [2021-10-20 01:45:58](https://github.com/leanprover-community/mathlib/commit/cd34347)
chore(*): remove uses of `universe variable` ([#9794](https://github.com/leanprover-community/mathlib/pull/9794))
Most of these uses are relics of when the distinction between `universe` and `universe variable` was more significant. There is still a difference inside sections, but it's an edge case and I don't think any of these uses are consciously trying to handle the edge case.

### [2021-10-19 23:43:31](https://github.com/leanprover-community/mathlib/commit/2d17c5a)
feat(group_theory/index): Relative index ([#9780](https://github.com/leanprover-community/mathlib/pull/9780))
Defines relative index between subgroups, and proves that relative index is multiplicative in towers.

### [2021-10-19 20:59:45](https://github.com/leanprover-community/mathlib/commit/72cb2e8)
refactor(*): rename some declarations ending with '' ([#9504](https://github.com/leanprover-community/mathlib/pull/9504))

### [2021-10-19 16:49:58](https://github.com/leanprover-community/mathlib/commit/65eef74)
fix(data/int/basic): ensure the additive group structure on integers is computable ([#9803](https://github.com/leanprover-community/mathlib/pull/9803))
This prevents the following failure:
```lean
import analysis.normed_space.basic
instance whoops : add_comm_group ℤ := by apply_instance
-- definition 'whoops' is noncomputable, it depends on 'int.normed_comm_ring'
```

### [2021-10-19 15:18:56](https://github.com/leanprover-community/mathlib/commit/e61584d)
fix(topology/sheaves/*): Fix docstrings ([#9807](https://github.com/leanprover-community/mathlib/pull/9807))
As noted by @alreadydone in [#9607](https://github.com/leanprover-community/mathlib/pull/9607), I forgot propagate naming changes to docstrings. This PR fixes that.

### [2021-10-19 12:47:04](https://github.com/leanprover-community/mathlib/commit/34aa23a)
feat(ring_theory/dedekind_domain): connect (/) and (⁻¹) on fractional ideals ([#9808](https://github.com/leanprover-community/mathlib/pull/9808))
Turns out we never actually proved the `div_eq_mul_inv` lemma on fractional ideals, which motivated the entire definition of `div_inv_monoid`. So here it is, along with some useful supporting lemmas.

### [2021-10-19 11:59:41](https://github.com/leanprover-community/mathlib/commit/065a708)
refactor(analysis/inner_product_space/projection): speedup proof ([#9804](https://github.com/leanprover-community/mathlib/pull/9804))
Speed up slow proof that caused a timeout on another branch.

### [2021-10-19 09:31:15](https://github.com/leanprover-community/mathlib/commit/b961b68)
feat(topology/connected): product of connected spaces is a connected space ([#9789](https://github.com/leanprover-community/mathlib/pull/9789))
* prove more in the RHS of `filter.mem_infi'`;
* prove that the product of (pre)connected sets is a (pre)connected set;
* prove a similar statement about indexed product `set.pi set.univ _`;
* add instances for `prod.preconnected_space`, `prod.connected_space`, `pi.preconnected_space`, and `pi.connected_space`.

### [2021-10-19 09:31:13](https://github.com/leanprover-community/mathlib/commit/ff3e868)
refactor(algebra/domain): make domain and integral_domain mixins ([#9719](https://github.com/leanprover-community/mathlib/pull/9719))
This PR turns `domain` and `integral_domain` into mixins. There's quite a lot of work here, as the unused argument linter then forces us to do some generalizations! (i.e. getting rid of unnecessary `integral_domain` arguments).
This PR does the minimum possible generalization: [#9739](https://github.com/leanprover-community/mathlib/pull/9739) does some more.
In a subsequent PR we can unify `domain` and `integral_domain`, which now only differ in their typeclass requirements.
This also remove use of `old_structure_cmd` in `euclidean_domain`.
- [x] depends on: [#9725](https://github.com/leanprover-community/mathlib/pull/9725) [An RFC]
- [x] depends on: [#9736](https://github.com/leanprover-community/mathlib/pull/9736)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)

### [2021-10-19 07:46:18](https://github.com/leanprover-community/mathlib/commit/a7bc717)
feat(algebra/big_operators/order): Upper bound on the cardinality of `finset.bUnion` ([#9797](https://github.com/leanprover-community/mathlib/pull/9797))
Also fix notation in all the additivized statements docstrings.

### [2021-10-19 07:46:17](https://github.com/leanprover-community/mathlib/commit/4df649c)
feat(data/nat/modeq): Upper bound for `chinese_remainder` ([#9783](https://github.com/leanprover-community/mathlib/pull/9783))
Proves that `chinese_remainder' < lcm n m` and `chinese_remainder < n * m`, as claimed by the doc-strings.

### [2021-10-19 07:05:07](https://github.com/leanprover-community/mathlib/commit/1f8c96b)
feat(data/nat/succ_pred): `ℕ` is succ- and pred- archimedean ([#9730](https://github.com/leanprover-community/mathlib/pull/9730))
This provides the instances `succ_order ℕ`, `pred_order ℕ`, `is_succ_archimedean ℕ`, `is_pred_archimedean ℕ`.

### [2021-10-19 04:41:01](https://github.com/leanprover-community/mathlib/commit/1ec385d)
chore(scripts): update nolints.txt ([#9799](https://github.com/leanprover-community/mathlib/pull/9799))
I am happy to remove some nolints for you!

### [2021-10-19 02:24:00](https://github.com/leanprover-community/mathlib/commit/04094c4)
feat(analysis/box_integral): Divergence thm for a Henstock-style integral ([#9496](https://github.com/leanprover-community/mathlib/pull/9496))
* Define integrals of Riemann, McShane, and Henstock (plus a few
  variations).
* Prove basic properties.
* Prove a version of the divergence theorem for one of these integrals.
* Prove that a Bochner integrable function is McShane integrable.

### [2021-10-18 23:50:42](https://github.com/leanprover-community/mathlib/commit/5eee6a2)
refactor(ring_theory/adjoin/fg): replace a fragile convert with rewrites ([#9786](https://github.com/leanprover-community/mathlib/pull/9786))

### [2021-10-18 23:50:41](https://github.com/leanprover-community/mathlib/commit/98d07d3)
refactor(algebra/order): replace typeclasses with constructors ([#9725](https://github.com/leanprover-community/mathlib/pull/9725))
This RFC suggests removing some unused classes for the ordered algebra hierarchy, replacing them with constructors
We have `nonneg_add_comm_group extends add_comm_group`, and an instance from this to `ordered_add_comm_group`. The intention is to be able to construct an `ordered_add_comm_group` by specifying its positive cone, rather than directly its order.
There are then `nonneg_ring` and `linear_nonneg_ring`, similarly.
(None of these are actually used later in mathlib at this point.)

### [2021-10-18 23:50:40](https://github.com/leanprover-community/mathlib/commit/442382d)
feat(tactic/to_additive): Improvements to to_additive ([#5487](https://github.com/leanprover-community/mathlib/pull/5487))
Change a couple of things in to_additive:
- First add a `tactic.copy_attribute'` intended for user attributes with parameters very similar to `tactic.copy_attribute` that just copies the parameter over when setting the attribute. This allows to_additive after many other attributes to transfer those attributes properly (e.g. norm_cast)
- Have to additive register generated equation lemmas as such, this necessitates a bit of restructuring, first all declarations must be generated (including equational lemmas), then the equational lemmas need their attributes, then they are registered as equation lemmas, finally the attributes are added to the main declaration.
- I also fixup the library in many places to account for these changes simplifying the source files, only one new lemma was added, in src/analysis/normed/group/quotient.lean `quotient_norm_mk_le'` to replace the unprimed version in the proof of `norm_normed_mk_le` as simp got better thanks to the new simp lemmas introduced by this PR. Probably many more handwritten additive versions can now be deleted in a future PR, especially defs and instances.
- All other library changes are just simplifications by using to additive for some hand generated declarations, and many more attributes on the generated lemmas.
- The attribute mono is trickier as it contains for its parameter not actual exprs containing names but exprs making names from strings, so I don't see how to handle it right now. We now warn the user about this, and fix the library in a couple of places.

### [2021-10-18 21:08:15](https://github.com/leanprover-community/mathlib/commit/8b7e16f)
feat(tactic/lint): improve check_univs linter ([#9698](https://github.com/leanprover-community/mathlib/pull/9698))
* `check_univs` now only checks the type of `d` and ignores `d._proof_i` subterms
* move `expr.univ_params_grouped` to the linter file (it seems increasingly unlikely that this has a use in other applications)
* We now don't test automatically generated declarations anymore.

### [2021-10-18 17:55:59](https://github.com/leanprover-community/mathlib/commit/b112d4d)
refactor(ring_theory/ideal/operations): generalize various definitions to remove negation and commutativity ([#9737](https://github.com/leanprover-community/mathlib/pull/9737))
Mostly this just weakens assumptions in `variable`s lines, but occasionally this moves lemmas to a more appropriate section too.

### [2021-10-18 16:41:10](https://github.com/leanprover-community/mathlib/commit/71c203a)
feat(analysis/normed/group/SemiNormedGroup/completion): add SemiNormedGroup.Completion ([#9788](https://github.com/leanprover-community/mathlib/pull/9788))
From LTE.

### [2021-10-18 16:41:09](https://github.com/leanprover-community/mathlib/commit/80071d4)
refactor(algebra/floor): Add `ceil` as a field of `floor_ring` ([#9591](https://github.com/leanprover-community/mathlib/pull/9591))
This allows more control on definitional equality.

### [2021-10-18 14:15:51](https://github.com/leanprover-community/mathlib/commit/5ea384e)
refactor(ring_theory/finiteness): replace fragile convert with rewrites ([#9787](https://github.com/leanprover-community/mathlib/pull/9787))

### [2021-10-18 14:15:49](https://github.com/leanprover-community/mathlib/commit/6f4aea4)
feat(data/set/pairwise): Simple `pairwise_disjoint` lemmas ([#9764](https://github.com/leanprover-community/mathlib/pull/9764))

### [2021-10-18 12:53:50](https://github.com/leanprover-community/mathlib/commit/116e426)
chore(group_theory/order_of_element): order_of_units ([#9777](https://github.com/leanprover-community/mathlib/pull/9777))

### [2021-10-18 12:53:48](https://github.com/leanprover-community/mathlib/commit/a7ac699)
feat(topology/metric_space): dimH is the supr of local dimH ([#9741](https://github.com/leanprover-community/mathlib/pull/9741))

### [2021-10-18 12:53:47](https://github.com/leanprover-community/mathlib/commit/06179ca)
feat(data/real/pointwise): Inf and Sup of `a • s` for `s : set ℝ` ([#9707](https://github.com/leanprover-community/mathlib/pull/9707))
This relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.

### [2021-10-18 11:21:22](https://github.com/leanprover-community/mathlib/commit/e841325)
feat(linear_algebra/dfinsupp): cardinality lemmas for `complete_lattice.independent` ([#9705](https://github.com/leanprover-community/mathlib/pull/9705))
If `p` is a system of independent subspaces of a vector space `V`, and `v` is a system of nonzero vectors each contained in the corresponding subspace, then `v` is linearly independent.
Consequently, if `p` is a system of independent subspaces of `V`, then no more than `dim V` many can be nontrivial.

### [2021-10-18 09:32:36](https://github.com/leanprover-community/mathlib/commit/39db98c)
feat(analysis/normed_space/add_torsor_bases): the convex hull has non-empty interior iff the affine span is top ([#9727](https://github.com/leanprover-community/mathlib/pull/9727))
Formalized as part of the Sphere Eversion project.

### [2021-10-18 08:20:00](https://github.com/leanprover-community/mathlib/commit/2e62b33)
chore(field_theory/galois): speedup a slow convert ([#9782](https://github.com/leanprover-community/mathlib/pull/9782))
This was broken by a deterministic timeout in another branch. This replaces a `convert` with an explicit `simp`.

### [2021-10-18 08:19:59](https://github.com/leanprover-community/mathlib/commit/27d28a8)
feat(linear_algebra/affine_space/independent): affine equivalences preserve affine independence of sets of points ([#9776](https://github.com/leanprover-community/mathlib/pull/9776))
The key addition is `affine_equiv.affine_independent_set_of_eq_iff`.
Formalized as part of the Sphere Eversion project.

### [2021-10-18 08:19:58](https://github.com/leanprover-community/mathlib/commit/fb5c0be)
feat(topology/metric_space): closed if spaced out ([#9754](https://github.com/leanprover-community/mathlib/pull/9754))
If pairwise distances between the points of a set are bounded from below by a positive number, then the set is closed.
Also prove some theorems about `uniform_inducing` and `uniform_embedding` and show that `coe : int → real` is a closed embedding.

### [2021-10-18 05:53:11](https://github.com/leanprover-community/mathlib/commit/6cd6ff4)
split(data/list/permutation): split off `data.list.basic` ([#9749](https://github.com/leanprover-community/mathlib/pull/9749))
This moves all the `list.permutations` definitions and lemmas not involving `list.perm` to a new file.

### [2021-10-18 02:28:14](https://github.com/leanprover-community/mathlib/commit/5b527bd)
refactor(linear_algebra/quadratic_form): split file ([#9781](https://github.com/leanprover-community/mathlib/pull/9781))
The section on quadratic forms over complex numbers required pulling in the developing of the complex power function, which significantly increases the import depth. Splitting this file allows `clifford_algebra` to be compiled much earlier.

### [2021-10-17 21:55:29](https://github.com/leanprover-community/mathlib/commit/27a777b)
feat(data/nat/gcd): `coprime.lcm_eq_mul` ([#9761](https://github.com/leanprover-community/mathlib/pull/9761))
Surprisingly, this result doesn't seem to be present yet.

### [2021-10-17 20:43:58](https://github.com/leanprover-community/mathlib/commit/5dbe8c4)
feat(topology/metric_space): a map with a contracting iterate has a fixed pt ([#9760](https://github.com/leanprover-community/mathlib/pull/9760))

### [2021-10-17 18:13:16](https://github.com/leanprover-community/mathlib/commit/084702d)
chore(analysis/normed_algebra/exponential): golf, generalize ([#9740](https://github.com/leanprover-community/mathlib/pull/9740))
* move `real.summable_pow_div_factorial` to
  `analysis.specific_limits`, golf the proof;
* use recently added lemma `inv_nat_cast_smul_eq` to golf the proof of
  equality of exponentials defined using different fields and
  generalize the statement: we no longer require one field to be a
  normed algebra over another.
* rename `exp_eq_exp_of_field_extension` → `exp_eq_exp` and
  `exp_series_eq_exp_series_of_field_extension` →
  `exp_series_eq_exp_series` because we no longer require
  `[normed_algebra 𝕂 𝕂']`.

### [2021-10-17 13:18:35](https://github.com/leanprover-community/mathlib/commit/376bba8)
chore(data/finset/lattice): fix infi docstrings ([#9775](https://github.com/leanprover-community/mathlib/pull/9775))

### [2021-10-17 13:18:34](https://github.com/leanprover-community/mathlib/commit/41b5645)
chore(topology/algebra/ordered/basic): move code out of `basic` ([#9772](https://github.com/leanprover-community/mathlib/pull/9772))

### [2021-10-17 13:18:32](https://github.com/leanprover-community/mathlib/commit/1432c30)
feat(topology/algebra/mul_action): `λ x, c • x` is a closed map for all `c` ([#9756](https://github.com/leanprover-community/mathlib/pull/9756))
* rename old `is_closed_map_smul₀` to `is_closed_map_smul_of_ne_zero`;
* add a new `is_closed_map_smul₀` that assumes more about typeclasses
  but works for `c = 0`.

### [2021-10-17 13:18:31](https://github.com/leanprover-community/mathlib/commit/48dc249)
feat(measure_theory/measure): +1 version of Borel-Cantelli, drop an assumption ([#9678](https://github.com/leanprover-community/mathlib/pull/9678))
* In all versions of Borel-Cantelli lemma, do not require that the
  sets are measurable.
* Add +1 version.
* Golf proofs.

### [2021-10-17 11:01:38](https://github.com/leanprover-community/mathlib/commit/3f15148)
chore(analysis/p_series): use `lift` tactic ([#9773](https://github.com/leanprover-community/mathlib/pull/9773))

### [2021-10-17 11:01:37](https://github.com/leanprover-community/mathlib/commit/9fec8f3)
feat(group_theory/index): `index_comap_of_surjective` ([#9768](https://github.com/leanprover-community/mathlib/pull/9768))
`subgroup.index` is preserved by `subgroup.comap`, provided that the homomorphism is surjective.

### [2021-10-17 11:01:36](https://github.com/leanprover-community/mathlib/commit/85f3640)
feat(topology/instances/ennreal): `{f | lipschitz_with K f}` is a closed set ([#9766](https://github.com/leanprover-community/mathlib/pull/9766))

### [2021-10-17 11:01:35](https://github.com/leanprover-community/mathlib/commit/678d7ed)
chore(data/equiv/mul_add): add missing `to_equiv_mk` ([#9765](https://github.com/leanprover-community/mathlib/pull/9765))

### [2021-10-17 11:01:34](https://github.com/leanprover-community/mathlib/commit/24ebeec)
feat(data/nat/gcd): Add `iff` version of `coprime.dvd_of_dvd_mul` ([#9759](https://github.com/leanprover-community/mathlib/pull/9759))
Adds `iff` versions of `coprime.dvd_of_dvd_mul_right` and `coprime.dvd_of_dvd_mul_left`.

### [2021-10-17 11:01:33](https://github.com/leanprover-community/mathlib/commit/1558a76)
feat(group_theory/subgroup/basic): Special cases of `subgroup_of` ([#9755](https://github.com/leanprover-community/mathlib/pull/9755))
Add four lemmas regarding special cases of `subgroup_of`.

### [2021-10-17 11:01:31](https://github.com/leanprover-community/mathlib/commit/4b00aa2)
refactor(ring_theory/jacobson): avoid shadowing hypothesis ([#9736](https://github.com/leanprover-community/mathlib/pull/9736))
This PR postpones a `rw` in a proof, which was creating a shadowed hypothesis. At present, this shadowing was not a big deal, but in another branch it caused a hard-to-diagnose error.

### [2021-10-17 11:01:30](https://github.com/leanprover-community/mathlib/commit/5eb47c0)
feat(topology/homotopy): Define the fundamental groupoid of a topological space ([#9683](https://github.com/leanprover-community/mathlib/pull/9683))

### [2021-10-17 08:53:58](https://github.com/leanprover-community/mathlib/commit/f171c61)
feat(linear_algebra/affine_space/independent): add `exists_affine_independent` ([#9747](https://github.com/leanprover-community/mathlib/pull/9747))
Formalized as part of the Sphere Eversion project.

### [2021-10-17 06:23:24](https://github.com/leanprover-community/mathlib/commit/ff8a35d)
feat(group_theory/subgroup/basic): Kernel of `subtype` and `inclusion` ([#9763](https://github.com/leanprover-community/mathlib/pull/9763))
`subtype` and `inculusion` are injective, so they have trivial kernel.

### [2021-10-17 03:34:30](https://github.com/leanprover-community/mathlib/commit/7aa431c)
chore(group_theory/quotient_group): Tag lemmas with `@[to_additive]` ([#9771](https://github.com/leanprover-community/mathlib/pull/9771))
Adds `@[to_additive]` to a couple lemmas.

### [2021-10-17 03:34:29](https://github.com/leanprover-community/mathlib/commit/a1a05ad)
chore(measure_theory/*): don't require the codomain to be a normed group ([#9769](https://github.com/leanprover-community/mathlib/pull/9769))
Lemmas like `continuous_on.ae_measurable` are true for any codomain. Also add `continuous.integrable_on_Ioc` and `continuous.integrable_on_interval_oc`.

### [2021-10-17 03:34:28](https://github.com/leanprover-community/mathlib/commit/08a070b)
chore(topology/instances/ennreal): golf a proof ([#9767](https://github.com/leanprover-community/mathlib/pull/9767))

### [2021-10-17 02:23:49](https://github.com/leanprover-community/mathlib/commit/4a837fb)
chore(analysis/normed/group): add a few convenience lemmas ([#9770](https://github.com/leanprover-community/mathlib/pull/9770))
Add `lipschitz_on_with.norm_sub_le_of_le`,
`lipschitz_with.norm_sub_le`, and `lipschitz_with.norm_sub_le_of_le`.

### [2021-10-16 23:11:25](https://github.com/leanprover-community/mathlib/commit/cf72eff)
refactor(group_theory/quotient_group): Fix typo ([#9746](https://github.com/leanprover-community/mathlib/pull/9746))
Fix typo in `quotient_bot`.

### [2021-10-16 21:46:54](https://github.com/leanprover-community/mathlib/commit/ad7000b)
feat(set_theory/cardinal): cardinal.to_nat_congr ([#9726](https://github.com/leanprover-community/mathlib/pull/9726))
If `e : α ≃ β`, then `(cardinal.mk α).to_nat = (cardinal.mk β).to_nat`.

### [2021-10-16 20:32:52](https://github.com/leanprover-community/mathlib/commit/b97bb92)
feat(set_theory/cardinal): lemmas ([#9690](https://github.com/leanprover-community/mathlib/pull/9690))
* swap sides of `cardinal.lift_mk`, rename it to `cardinal.mk_ulift`;
* add `cardinal.out_mk_equiv`.

### [2021-10-16 18:01:16](https://github.com/leanprover-community/mathlib/commit/3fe67d6)
feat(analysis/special_functions/integrals): integral of `|x - a| ^ n` over `Ι a b` ([#9752](https://github.com/leanprover-community/mathlib/pull/9752))
Also use notation for `interval a b` and `interval_oc a b`.

### [2021-10-16 18:01:15](https://github.com/leanprover-community/mathlib/commit/54e9e12)
chore(topology/maps): add `is_closed_map.closed_range` ([#9751](https://github.com/leanprover-community/mathlib/pull/9751))

### [2021-10-16 18:01:14](https://github.com/leanprover-community/mathlib/commit/998ab78)
chore(data/list/lex): make data.list.lex not depend on data.list.basic ([#9750](https://github.com/leanprover-community/mathlib/pull/9750))
Another simplification in list related dependencies, if this commit breaks external code the fix is to add `import data.list.basic` to the broken file.

### [2021-10-16 18:01:13](https://github.com/leanprover-community/mathlib/commit/066a168)
feat(topology/G_delta): add lemmas, minor golf ([#9742](https://github.com/leanprover-community/mathlib/pull/9742))
* the complement to a countable set is a Gδ set;
* a closed set is a Gδ set;
* finite union of Gδ sets is a Gδ set;
* generalize some universe levels in `topology.basic`;
* golf a few proofs in `topology.uniform_space.basic`;
* add `filter.has_basis.bInter_bUnion_ball`.

### [2021-10-16 18:01:11](https://github.com/leanprover-community/mathlib/commit/aa0d0d4)
feat(group_theory/subgroup/basic): Range of inclusion ([#9732](https://github.com/leanprover-community/mathlib/pull/9732))
If `H ≤ K`, then the range of `inclusion : H → K` is `H` (viewed as a subgroup of `K`).

### [2021-10-16 18:01:10](https://github.com/leanprover-community/mathlib/commit/155f8e6)
feat(data/int/succ_pred): `ℤ` is succ- and pred- archimedean ([#9731](https://github.com/leanprover-community/mathlib/pull/9731))
This provides the instances `succ_order ℤ`, `pred_order ℤ`, `is_succ_archimedean ℤ`, `is_pred_archimedean ℤ`.

### [2021-10-16 18:01:09](https://github.com/leanprover-community/mathlib/commit/e744033)
feat(data/finset/basic, lattice): Simple lemmas ([#9723](https://github.com/leanprover-community/mathlib/pull/9723))
This proves lemmas about `finset.sup`/`finset.inf` and `finset.singleton`.

### [2021-10-16 18:01:08](https://github.com/leanprover-community/mathlib/commit/bf34d9b)
feat(analysis/normed/group/SemiNormedGroup/kernels): add explicit_cokernel.map ([#9712](https://github.com/leanprover-community/mathlib/pull/9712))
From LTE.

### [2021-10-16 18:01:07](https://github.com/leanprover-community/mathlib/commit/686b363)
feat(analysis/normed/group/SemiNormedGroup/kernels): add kernels ([#9711](https://github.com/leanprover-community/mathlib/pull/9711))
From LTE.

### [2021-10-16 18:01:06](https://github.com/leanprover-community/mathlib/commit/3d99926)
feat(analysis/normed/group/SemiNormedGroup): add iso_isometry_of_norm_noninc ([#9710](https://github.com/leanprover-community/mathlib/pull/9710))
From LTE.

### [2021-10-16 18:01:05](https://github.com/leanprover-community/mathlib/commit/5ac586a)
feat(algebra/group_power/order): When a power is less than one ([#9700](https://github.com/leanprover-community/mathlib/pull/9700))
This proves a bunch of simple order lemmas relating `1`, `a` and `a ^ n`. I also move `pow_le_one` upstream as it could already be proved in `algebra.group_power.order` and remove `[nontrivial R]` from `one_lt_pow`.

### [2021-10-16 16:46:55](https://github.com/leanprover-community/mathlib/commit/99b2d40)
feat(algebra/floor): Floor and ceil of `-a` ([#9715](https://github.com/leanprover-community/mathlib/pull/9715))
This proves `floor_neg : ⌊-a⌋ = -⌈a⌉` and `ceil_neg : ⌈-a⌉ = -⌊a⌋` and uses them to remove explicit dependency on the definition of `int.ceil` in prevision of [#9591](https://github.com/leanprover-community/mathlib/pull/9591). This also proves `⌊a + 1⌋ = ⌊a⌋ + 1` and variants.

### [2021-10-16 09:26:55](https://github.com/leanprover-community/mathlib/commit/9ac2aa2)
feat(topology/metric_space/lipschitz): add `lipschitz_with.min` and `lipschitz_with.max` ([#9744](https://github.com/leanprover-community/mathlib/pull/9744))
Also change assumptions in some lemmas in `algebra.order.group` from
 `[add_comm_group α] [linear_order α] [covariant_class α α (+) (≤)]`
to `[linear_ordered_add_comm_group α]`. These two sets of assumptions
are equivalent but the latter is more readable.

### [2021-10-16 09:26:54](https://github.com/leanprover-community/mathlib/commit/96ba8b6)
chore(topology/uniform_space/pi): add `uniform_continuous_pi` ([#9743](https://github.com/leanprover-community/mathlib/pull/9743))

### [2021-10-16 08:44:20](https://github.com/leanprover-community/mathlib/commit/e362293)
refactor(ring_theory/fractional_ideal): speedup a proof ([#9738](https://github.com/leanprover-community/mathlib/pull/9738))
This was timing out on another branch. Just replaces a `simp only []` with a `rw []`.

### [2021-10-16 07:32:33](https://github.com/leanprover-community/mathlib/commit/f40cd88)
chore(topology/algebra/ordered): move some lemmas to a new file ([#9745](https://github.com/leanprover-community/mathlib/pull/9745))

### [2021-10-16 04:16:34](https://github.com/leanprover-community/mathlib/commit/150bbea)
feat(group_theory/subgroup/basic): Bottom subgroup has unique element ([#9734](https://github.com/leanprover-community/mathlib/pull/9734))
Adds instance for `unique (⊥ : subgroup G)`.

### [2021-10-16 01:17:29](https://github.com/leanprover-community/mathlib/commit/1766588)
feat(measure_theory/covering/vitali): Vitali covering theorems ([#9680](https://github.com/leanprover-community/mathlib/pull/9680))
The topological and measurable Vitali covering theorems.
* topological version: if a space is covered by balls `(B (x_i, r_i))_{i \in I}`, one can extract a disjointed subfamily indexed by `J` such that the space is covered by the balls `B (x_j, 5 r_j)`.
* measurable version: if additionally the measure has a doubling-like property, and the covering contains balls of arbitrarily small radius at every point, then the disjointed subfamily one obtains above covers almost all the space.
These two statements are particular cases of more general statements that are proved in this PR.

### [2021-10-15 22:57:51](https://github.com/leanprover-community/mathlib/commit/ea22ce3)
chore(data/list): move lemmas from data.list.basic that require algebra.group_power to a new file ([#9728](https://github.com/leanprover-community/mathlib/pull/9728))
Hopefully ease the dependencies on anyone importing data.list.basic, if your code broke after this change adding `import data.list.prod_monoid` should fix it.
Lemmas moved:
- `list.prod_repeat`
- `list.sum_repeat`
- `list.prod_le_of_forall_le`
- `list.sum_le_of_forall_le`

### [2021-10-15 21:35:25](https://github.com/leanprover-community/mathlib/commit/711aa75)
refactor(algebra/gcd_monoid): remove superfluous old_structure_cmd ([#9720](https://github.com/leanprover-community/mathlib/pull/9720))

### [2021-10-15 16:38:20](https://github.com/leanprover-community/mathlib/commit/b3f602b)
feat(linear_algebra/linear_independent): add variant of `exists_linear_independent` ([#9708](https://github.com/leanprover-community/mathlib/pull/9708))
Formalized as part of the Sphere Eversion project.

### [2021-10-15 15:08:13](https://github.com/leanprover-community/mathlib/commit/d6fd5f5)
feat(linear_algebra/dimension): generalize dim_zero_iff_forall_zero ([#9713](https://github.com/leanprover-community/mathlib/pull/9713))
We generalize `dim_zero_iff_forall_zero` to `[nontrivial R] [no_zero_smul_divisors R M]`.
If you see a more general class to consider let me know.

### [2021-10-15 12:10:59](https://github.com/leanprover-community/mathlib/commit/ad6d476)
refactor(ring_theory/derivation): remove old_structure_cmd ([#9724](https://github.com/leanprover-community/mathlib/pull/9724))

### [2021-10-15 12:10:58](https://github.com/leanprover-community/mathlib/commit/a2737b4)
chore(data/set_like/basic): remove superfluous old_structure_cmd ([#9722](https://github.com/leanprover-community/mathlib/pull/9722))

### [2021-10-15 11:28:36](https://github.com/leanprover-community/mathlib/commit/6bc2a1a)
refactor(algebra/lie/basic): remove old_structure_cmd ([#9721](https://github.com/leanprover-community/mathlib/pull/9721))

### [2021-10-15 06:28:08](https://github.com/leanprover-community/mathlib/commit/7707036)
feat(tactic/by_contra): add by_contra' tactic ([#9619](https://github.com/leanprover-community/mathlib/pull/9619))

### [2021-10-15 01:06:58](https://github.com/leanprover-community/mathlib/commit/be91f69)
chore(algebra/floor): general golf ([#9716](https://github.com/leanprover-community/mathlib/pull/9716))
This cleans the file in depth:
* kill some `simp`
* use available dot notation on `≤`
* remove the `by ... ; ...` (there's one left that [#9715](https://github.com/leanprover-community/mathlib/pull/9715)) takes care of
* group definition and notation of `int.floor`,`int.ceil` and `int.fract`
* move `int.preimage_...` lemmas with the rest of the `ℤ` stuff
* homogeneize variable names

### [2021-10-14 23:10:05](https://github.com/leanprover-community/mathlib/commit/c37ea53)
feat(order/succ_pred): `succ`-Archimedean orders ([#9714](https://github.com/leanprover-community/mathlib/pull/9714))
This defines `succ`-Archimedean orders: orders in which `a ≤ b` means that `succ^[n] a = b` for some `n`.

### [2021-10-14 21:12:58](https://github.com/leanprover-community/mathlib/commit/c12aced)
feat(algebra/star): star_linear_equiv ([#9426](https://github.com/leanprover-community/mathlib/pull/9426))

### [2021-10-14 19:54:19](https://github.com/leanprover-community/mathlib/commit/158fbc5)
refactor(algebra/module/order): Make space argument explicit in the `order_iso` ([#9706](https://github.com/leanprover-community/mathlib/pull/9706))
Explicitly providing `M` in `order_iso.smul_left` and `order_iso.smul_left_dual` turns out to work much better with dot notation on `order_iso`. This allows golfing half the proofs introduced in [#9078](https://github.com/leanprover-community/mathlib/pull/9078).

### [2021-10-14 18:49:52](https://github.com/leanprover-community/mathlib/commit/72789f5)
feat(linear_algebra/affine_space/affine_subspace): add lemma `affine_equiv.span_eq_top_iff` ([#9695](https://github.com/leanprover-community/mathlib/pull/9695))
Together with supporting lemmas.
Formalized as part of the Sphere Eversion project.

### [2021-10-14 18:06:10](https://github.com/leanprover-community/mathlib/commit/cef78dd)
feat(archive/abel_ruffini): speedup by squeezing  ([#9709](https://github.com/leanprover-community/mathlib/pull/9709))
30s->9s elaboration for me, hopefully stop [#9705](https://github.com/leanprover-community/mathlib/pull/9705) timing out

### [2021-10-14 16:25:51](https://github.com/leanprover-community/mathlib/commit/393fe70)
chore(analysis/p_series): add 2 more versions ([#9703](https://github.com/leanprover-community/mathlib/pull/9703))

### [2021-10-14 13:24:56](https://github.com/leanprover-community/mathlib/commit/aff49a6)
feat(data/equiv/basic): prop_equiv_pempty ([#9689](https://github.com/leanprover-community/mathlib/pull/9689))

### [2021-10-14 13:24:54](https://github.com/leanprover-community/mathlib/commit/dc23dfa)
feat(data/equiv/basic): subtype_equiv_psigma ([#9688](https://github.com/leanprover-community/mathlib/pull/9688))
- [x] depends on: [#9687](https://github.com/leanprover-community/mathlib/pull/9687)
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)

### [2021-10-14 13:24:52](https://github.com/leanprover-community/mathlib/commit/9da33a8)
refactor(algebra/floor): Rename floor and ceil functions ([#9590](https://github.com/leanprover-community/mathlib/pull/9590))
This renames
* `floor` -> `int.floor`
* `ceil` -> `int.ceil`
* `fract` -> `int.fract`
* `nat_floor` -> `nat.floor`
* `nat_ceil` -> `nat.ceil`

### [2021-10-14 07:51:21](https://github.com/leanprover-community/mathlib/commit/264ff90)
refactor(analysis/special_functions): generalise nth-root lemmas ([#9704](https://github.com/leanprover-community/mathlib/pull/9704))
`exists_pow_nat_eq` and `exists_eq_mul_self` both hold for any algebraically closed field, so pull them out into `is_alg_closed/basic` and generalise appropriately
Closes [#4674](https://github.com/leanprover-community/mathlib/pull/4674)

### [2021-10-14 07:51:19](https://github.com/leanprover-community/mathlib/commit/8d67d9a)
chore(category_theory/sites/*): Generalize universes ([#9675](https://github.com/leanprover-community/mathlib/pull/9675))
This generalizes the universe levels for sheaves to some extent.
This will allow us to now consider sheaves on `C : Type u` (satisfying `[category.{v} C]` and endowed with a Grothendieck topology) taking values in an arbitrary category with no additional universe restrictions.
The only part of the theory which has not been generalized is the equivalence of the sheaf condition with the condition involving Yoneda. To generalize this would require composing with `ulift_functors`'s, which we may or may not want to do.

### [2021-10-14 05:36:14](https://github.com/leanprover-community/mathlib/commit/34f3494)
chore(set_theory/cardinal): rename `is_empty`/`nonempty` lemmas ([#9668](https://github.com/leanprover-community/mathlib/pull/9668))
* add `is_empty_pi`, `is_empty_prod`, `is_empty_pprod`, `is_empty_sum`;
* rename `cardinal.eq_zero_of_is_empty` to `cardinal.mk_eq_zero`, make
  the argument `α : Type u` explicit;
* rename `cardinal.eq_zero_iff_is_empty` to `cardinal.mk_eq_zero_iff`;
* rename `cardinal.ne_zero_iff_nonempty` to `cardinal.mk_ne_zero_iff`;
* add `@[simp]` lemma `cardinal.mk_ne_zero`;
* fix compile errors caused by these changes, golf a few proofs.

### [2021-10-14 04:04:03](https://github.com/leanprover-community/mathlib/commit/3340617)
feat(algebra/bounds): `smul` of upper/lower bounds ([#9078](https://github.com/leanprover-community/mathlib/pull/9078))
This relates `lower_bounds (a • s)`/`upper_bounds (a • s)` and `a • lower_bounds s`/`a • upper_bounds s`.

### [2021-10-13 21:29:32](https://github.com/leanprover-community/mathlib/commit/19da20b)
feat(combinatorics/hall): generalized Hall's Marriage Theorem ([#7825](https://github.com/leanprover-community/mathlib/pull/7825))
Used the generalized Kőnig's lemma to prove a version of Hall's Marriage Theorem with the `fintype` constraint on the index type removed.  The original `fintype` version is moved into `hall/finite.lean`, and the infinite version is put in `hall/basic.lean`.  They are in separate files because the infinite version pulls in `topology.category.Top.limits`, which is a rather large dependency.

### [2021-10-13 17:58:00](https://github.com/leanprover-community/mathlib/commit/5db83f9)
feat(set_theory/cardinal): add lemmas ([#9697](https://github.com/leanprover-community/mathlib/pull/9697))
We add three easy lemmas about cardinals living in different universes.

### [2021-10-13 17:57:59](https://github.com/leanprover-community/mathlib/commit/3faf0f5)
chore(data/real/irrational): add more lemmas ([#9684](https://github.com/leanprover-community/mathlib/pull/9684))

### [2021-10-13 17:57:58](https://github.com/leanprover-community/mathlib/commit/096923c)
feat(topology/connected.lean): add theorems about connectedness o… ([#9633](https://github.com/leanprover-community/mathlib/pull/9633))
feat(src/topology/connected.lean): add theorems about connectedness of closure
add two theorems is_preconnected.inclosure and is_connected.closure
	which formalize that if a set s is (pre)connected
	and a set t satisfies s ⊆ t ⊆ closure s,
	then t is (pre)connected as well
modify is_preconnected.closure and is_connected.closure
	to take these theorems into account
add a few comments for theorems in the code

### [2021-10-13 15:48:29](https://github.com/leanprover-community/mathlib/commit/32e1b6c)
chore(ring_theory/ideal): improve 1st isomorphism theorem docstrings ([#9699](https://github.com/leanprover-community/mathlib/pull/9699))
Fix a typo and add **bold** to the theorem names.

### [2021-10-13 15:48:28](https://github.com/leanprover-community/mathlib/commit/0ce4442)
refactor(algebra/group_power/order): relax linearity condition on `one_lt_pow` ([#9696](https://github.com/leanprover-community/mathlib/pull/9696))
`[linear_ordered_semiring R]` becomes `[ordered_semiring R] [nontrivial R]`. I also golf the proof and move ìt from `algebra.field_power` to `algebra.group_power.order`, where it belongs.

### [2021-10-13 15:48:27](https://github.com/leanprover-community/mathlib/commit/bc9e38f)
refactor(linear_algebra/dimension): remove some nontrivial assumptions ([#9693](https://github.com/leanprover-community/mathlib/pull/9693))
We remove some `nontrivial R` assumptions.

### [2021-10-13 15:48:25](https://github.com/leanprover-community/mathlib/commit/313db47)
feat(measure_theory/covering/besicovitch): remove measurability assumptions ([#9679](https://github.com/leanprover-community/mathlib/pull/9679))
For applications, it is important to allow non-measurable sets in the Besicovitch covering theorem. We tweak the proof to allow this.
Also give an improved statement that is easier to use in applications.

### [2021-10-13 15:48:24](https://github.com/leanprover-community/mathlib/commit/f29755b)
refactor(data/set/pairwise): generalize `pairwise_disjoint` to `semilattice_inf_bot` ([#9670](https://github.com/leanprover-community/mathlib/pull/9670))
`set.pairwise_disjoint` was only defined for `set (set α)`. Now, it's defined for `set α` where `semilattice_inf_bot α`. I also
* move it to `data.set.pairwise` because it's really not about `set` anymore.
* drop the `set` namespace.
* add more general elimination rules and rename the current one to `elim_set`.

### [2021-10-13 15:48:22](https://github.com/leanprover-community/mathlib/commit/9ee2a50)
fix(group_theory/group_action): `has_scalar.comp.is_scalar_tower` is a dangerous instance ([#9656](https://github.com/leanprover-community/mathlib/pull/9656))
This issue came up in the discussion of [#9535](https://github.com/leanprover-community/mathlib/pull/9535): in certain cases, the instance `has_scalar.comp.is_scalar_tower` is fed too many metavariables and starts recursing infinitely. So I believe we should demote it from being an instance. Example trace:
```plain
[class_instances] (0) ?x_0 : has_scalar S P.quotient := @quotient.has_scalar ?x_1 ?x_2 ?x_3 ?x_4 ?x_5 ?x_6 ?x_7 ?x_8 ?x_9 ?x_10
[class_instances] (1) ?x_9 : @is_scalar_tower S R M ?x_7
  (@smul_with_zero.to_has_scalar R M
     (@mul_zero_class.to_has_zero R
        (@mul_zero_one_class.to_mul_zero_class R
           (@monoid_with_zero.to_mul_zero_one_class R (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1)))))
     (@add_zero_class.to_has_zero M
        (@add_monoid.to_add_zero_class M
           (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
     (@mul_action_with_zero.to_smul_with_zero R M (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1))
        (@add_zero_class.to_has_zero M
           (@add_monoid.to_add_zero_class M
              (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
        (@module.to_mul_action_with_zero R M (@ring.to_semiring R _inst_1)
           (@add_comm_group.to_add_comm_monoid M _inst_2)
           _inst_3)))
  ?x_8 := @has_scalar.comp.is_scalar_tower ?x_11 ?x_12 ?x_13 ?x_14 ?x_15 ?x_16 ?x_17 ?x_18 ?x_19
[class_instances] (2) ?x_18 : @is_scalar_tower ?x_11 R M ?x_15
  (@smul_with_zero.to_has_scalar R M
     (@mul_zero_class.to_has_zero R
        (@mul_zero_one_class.to_mul_zero_class R
           (@monoid_with_zero.to_mul_zero_one_class R (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1)))))
     (@add_zero_class.to_has_zero M
        (@add_monoid.to_add_zero_class M
           (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
     (@mul_action_with_zero.to_smul_with_zero R M (@semiring.to_monoid_with_zero R (@ring.to_semiring R _inst_1))
        (@add_zero_class.to_has_zero M
           (@add_monoid.to_add_zero_class M
              (@add_comm_monoid.to_add_monoid M (@add_comm_group.to_add_comm_monoid M _inst_2))))
        (@module.to_mul_action_with_zero R M (@ring.to_semiring R _inst_1)
           (@add_comm_group.to_add_comm_monoid M _inst_2)
           _inst_3)))
  ?x_16 := @has_scalar.comp.is_scalar_tower ?x_20 ?x_21 ?x_22 ?x_23 ?x_24 ?x_25 ?x_26 ?x_27 ?x_28
...
```
You'll see that the places where `has_scalar.comp.is_scalar_tower` expects a `has_scalar.comp` are in fact metavariables, so they always unify.
I have included a test case where the instance looks innocuous enough in its parameters: everything is phrased in terms of either irreducible defs, implicit variables or instance implicits, to argue that the issue really lies with `has_scalar.comp.is_scalar_tower`. Moreover, I don't think we lose a lot by demoting the latter from an instance since `has_scalar.comp` isn't an instance either.

### [2021-10-13 15:48:21](https://github.com/leanprover-community/mathlib/commit/e8427b0)
feat(ring_theory/ideal/operation): add some extra definitions in the `double_quot` section ([#9649](https://github.com/leanprover-community/mathlib/pull/9649))

### [2021-10-13 15:48:20](https://github.com/leanprover-community/mathlib/commit/a7ec633)
chore(algebra/*): add missing lemmas about `copy` on subobjects ([#9624](https://github.com/leanprover-community/mathlib/pull/9624))
This adds `coe_copy` and `copy_eq` to `sub{mul_action,group,ring,semiring,field,module,algebra,lie_module}`, to match the lemmas already present on `submonoid`.

### [2021-10-13 15:48:18](https://github.com/leanprover-community/mathlib/commit/577cac1)
feat(algebra/order/nonneg): properties about the nonnegative cone ([#9598](https://github.com/leanprover-community/mathlib/pull/9598))
* Provide various classes on the type `{x : α // 0 ≤ x}` where `α` has some order (and algebraic) structure.
* Use this to automatically derive the classes on `nnreal`.
* We currently do not yet define `conditionally_complete_linear_order_bot nnreal` using nonneg, since that causes some errors (I think Lean then thinks that there are two orders that are not definitionally equal (unfolding only instances)).
* We leave a bunch of `example` lines in `nnreal` to show that `nnreal` has all the old classes. These could also be removed, if desired.
* We currently only give some instances and simp/norm_cast lemmas. This could be expanded in the future.

### [2021-10-13 13:20:49](https://github.com/leanprover-community/mathlib/commit/aa67421)
lint(tactic/lint/misc): do not lint autogenerated proofs for bad universes ([#9676](https://github.com/leanprover-community/mathlib/pull/9676))

### [2021-10-13 13:20:48](https://github.com/leanprover-community/mathlib/commit/ea360f2)
feat(group_theory/sylow): Frattini's Argument ([#9662](https://github.com/leanprover-community/mathlib/pull/9662))
Frattini's argument: If `N` is a normal subgroup of `G`, and `P` is a Sylow `p`-subgroup of `N`, then `PN=G`.
The proof is an application of Sylow's second theorem (all Sylow `p`-subgroups of `N` are conjugate).

### [2021-10-13 13:20:46](https://github.com/leanprover-community/mathlib/commit/acc1d4b)
feat(analysis/normed_space/SemiNormedGroup/kernels) : add lemmas ([#9654](https://github.com/leanprover-community/mathlib/pull/9654))
From LTE.

### [2021-10-13 13:20:45](https://github.com/leanprover-community/mathlib/commit/6ea59e3)
feat(category_theory/sites/sieves): Added functor pushforward ([#9647](https://github.com/leanprover-community/mathlib/pull/9647))
Defined `sieve.functor_pushforward`.
Proved that `sieve.functor_pushforward` and `sieve.functor_pullback` forms a Galois connection.
Provided some lemmas about `sieve.functor_pushforward`, `sieve.functor_pullback` regarding the lattice structure.

### [2021-10-13 13:20:44](https://github.com/leanprover-community/mathlib/commit/17d8928)
feat(algebra/graded_monoid,algebra/direct_sum/ring): provide lemmas about powers in graded monoids ([#9631](https://github.com/leanprover-community/mathlib/pull/9631))
The key results are `direct_sum.of_pow` and `graded_monoid.mk_pow`.

### [2021-10-13 13:20:43](https://github.com/leanprover-community/mathlib/commit/edf07cf)
feat(topology/sheaves/sheaf_condition/sites): Connect sheaves on sites to sheaves on spaces ([#9609](https://github.com/leanprover-community/mathlib/pull/9609))
Show that a sheaf on the site `opens X` is the same thing as a sheaf on the space `X`. This finally connects the theory of sheaves on sites to sheaves on spaces, which were previously independent of each other.

### [2021-10-13 13:20:41](https://github.com/leanprover-community/mathlib/commit/f238733)
feat(algebra/order/smul): Monotonicity of scalar multiplication ([#9558](https://github.com/leanprover-community/mathlib/pull/9558))
Also prove `smul_nonneg`, `smul_pos` and variants.

### [2021-10-13 12:04:30](https://github.com/leanprover-community/mathlib/commit/04ed867)
chore(topology/uniform_space/cauchy): add a few simple lemmas ([#9685](https://github.com/leanprover-community/mathlib/pull/9685))
* rename `cauchy_prod` to `cauchy.prod`;
* add `cauchy_seq.tendsto_uniformity`, `cauchy_seq.nonempty`,
  `cauchy_seq.comp_tendsto`, `cauchy_seq.prod`, `cauchy_seq.prod_map`,
  `uniform_continuous.comp_cauchy_seq`, and
  `filter.tendsto.subseq_mem_entourage`;
* drop `[nonempty _]` assumption in `cauchy_seq.mem_entourage`.

### [2021-10-13 09:37:08](https://github.com/leanprover-community/mathlib/commit/46a7014)
feat(data/equiv/basic): psigma_congr_right ([#9687](https://github.com/leanprover-community/mathlib/pull/9687))

### [2021-10-13 09:37:07](https://github.com/leanprover-community/mathlib/commit/4c1a9c4)
chore(order/filter): add 2 lemmas ([#9682](https://github.com/leanprover-community/mathlib/pull/9682))

### [2021-10-13 09:37:00](https://github.com/leanprover-community/mathlib/commit/8886386)
feat(star/basic): add a `star_monoid (units R)` instance ([#9681](https://github.com/leanprover-community/mathlib/pull/9681))
This also moves all the `opposite R` instances to be adjacent, and add some missing `star_module` definitions.

### [2021-10-13 09:36:59](https://github.com/leanprover-community/mathlib/commit/52d5fd4)
feat(linear_algebra/{dimension,affine_space/finite_dimensional}): independent subsets of finite-dimensional spaces are finite. ([#9674](https://github.com/leanprover-community/mathlib/pull/9674))
Formalized as part of the Sphere Eversion project.

### [2021-10-13 07:56:13](https://github.com/leanprover-community/mathlib/commit/2c8abe5)
feat(algebra/star): `star_gpow` and `star_fpow` ([#9661](https://github.com/leanprover-community/mathlib/pull/9661))
One unrelated proof changes as the import additions pulls in a simp lemma that was previously missing, making the call to `ring` no longer necessary.

### [2021-10-13 02:43:35](https://github.com/leanprover-community/mathlib/commit/ea70e1c)
chore(scripts): update nolints.txt ([#9686](https://github.com/leanprover-community/mathlib/pull/9686))
I am happy to remove some nolints for you!

### [2021-10-12 22:59:49](https://github.com/leanprover-community/mathlib/commit/c65de1e)
chore(data/sym/sym2): speed up some proofs ([#9677](https://github.com/leanprover-community/mathlib/pull/9677))
In one test, elaboration of sym2_ext went from 46.9s to 734ms, and of elems_iff_eq from 54.3s to 514ms.

### [2021-10-12 17:00:40](https://github.com/leanprover-community/mathlib/commit/66285c9)
feat(topology/instances/ennreal): if a tsum is finite, then the tsum over the complement of a finset tends to 0 at top ([#9665](https://github.com/leanprover-community/mathlib/pull/9665))
Together with minor tweaks of the library:
* rename `bounded.subset` to `bounded.mono`
* remove `bUnion_subset_bUnion_right`, which is exactly the same as `bUnion_mono`. Same for intersections.
* add `bUnion_congr` and `bInter_congr`
* introduce lemma `null_of_locally_null`: if a set has zero measure in a neighborhood of each of its points, then it has zero measure in a second-countable space.

### [2021-10-12 17:00:39](https://github.com/leanprover-community/mathlib/commit/817c70d)
feat(category_theory/*): Functors about comma categories. ([#9627](https://github.com/leanprover-community/mathlib/pull/9627))
Added `pre` and `post` for `comma`, `structured_arrow`, `costructured_arrow`.

### [2021-10-12 15:09:33](https://github.com/leanprover-community/mathlib/commit/f63b8f1)
feat(algebra/star/basic): add some helper lemmas about star ([#9651](https://github.com/leanprover-community/mathlib/pull/9651))
This adds the new lemmas:
* `star_pow`
* `star_nsmul`
* `star_gsmul`
* `star_prod`
* `star_div`
* `star_div'`
* `star_inv`
* `star_inv'`
* `star_mul'`
and generalizes the typeclass assumptions from `star_ring` to `star_add_monoid` on:
* `star_neg`
* `star_sub`
* `star_sum`

### [2021-10-12 11:41:14](https://github.com/leanprover-community/mathlib/commit/b486c88)
chore(analysis): fix file name ([#9673](https://github.com/leanprover-community/mathlib/pull/9673))
This file was moved since the docstring was written

### [2021-10-12 11:41:13](https://github.com/leanprover-community/mathlib/commit/bcb2943)
chore(set_theory/cardinal): move defs/lemmas about `lift` up ([#9669](https://github.com/leanprover-community/mathlib/pull/9669))

### [2021-10-12 11:41:12](https://github.com/leanprover-community/mathlib/commit/a979d15)
feat(order/filter): `∃ᶠ m in at_top, m ≡ d [MOD n]` ([#9666](https://github.com/leanprover-community/mathlib/pull/9666))

### [2021-10-12 08:59:45](https://github.com/leanprover-community/mathlib/commit/fd7da4e)
refactor(combinatorics/partition): add `nat` namespace ([#9672](https://github.com/leanprover-community/mathlib/pull/9672))
`partition` is now `nat.partition`

### [2021-10-12 08:59:43](https://github.com/leanprover-community/mathlib/commit/2e72f35)
refactor(data/opposite): Remove the `op_induction` tactic ([#9660](https://github.com/leanprover-community/mathlib/pull/9660))
The `induction` tactic is already powerful enough for this; we don't have `order_dual_induction` or `nat_induction` as tactics.
The bulk of this change is replacing `op_induction x` with `induction x using opposite.rec`.
This leaves behind the non-interactive `op_induction'` which is still needed as a `tidy` hook.
This also renames the def `opposite.op_induction` to `opposite.rec` to match `order_dual.rec` etc.

### [2021-10-12 08:59:41](https://github.com/leanprover-community/mathlib/commit/ad4040d)
feat(algebra/opposites): provide npow and gpow explicitly, prove `op_gpow` and `unop_gpow` ([#9659](https://github.com/leanprover-community/mathlib/pull/9659))
By populating the `npow` and `gpow` fields in the obvious way, `op_pow` and `unop_pow` are true definitionally.
This adds the new lemmas `op_gpow` and `unop_gpow` which works for `group`s and `division_ring`s too.
Note that we do not provide an explicit `div` in `div_inv_monoid`, because there is no "reversed division" operator to define it via.
This also reorders the lemmas so that the definitional lemmas are available before any proof obligations might appear in stronger typeclasses.

### [2021-10-12 08:59:38](https://github.com/leanprover-community/mathlib/commit/34ffb15)
feat(linear_algebra/affine_space/finite_dimensional): upgrade `affine_independent.affine_span_eq_top_of_card_eq_finrank_add_one` to an iff ([#9657](https://github.com/leanprover-community/mathlib/pull/9657))
Also including some related, but strictly speaking independent, lemmas such as `affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nontrivial`.
Formalized as part of the Sphere Eversion project.

### [2021-10-12 08:16:55](https://github.com/leanprover-community/mathlib/commit/1023d81)
chore(ring_theory/tensor_product): squeeze simps in a slow proof ([#9671](https://github.com/leanprover-community/mathlib/pull/9671))
This proof just timed out in bors. Goes from 21s to 1s on my computer just by squeezing the simps.

### [2021-10-12 06:20:54](https://github.com/leanprover-community/mathlib/commit/a132d0a)
chore(analysis): move some files to `analysis/normed/group` ([#9667](https://github.com/leanprover-community/mathlib/pull/9667))

### [2021-10-12 01:53:33](https://github.com/leanprover-community/mathlib/commit/638dd0f)
feat(data/dfinsupp, algebra/direct_sum/module): direct sum on fintype ([#9664](https://github.com/leanprover-community/mathlib/pull/9664))
Analogues for `dfinsupp`/`direct_sum` of definitions/lemmas such as `finsupp.equiv_fun_on_fintype`:  a `dfinsupp`/`direct_sum` over a finite index set is canonically equivalent to `pi` over the same index set.

### [2021-10-11 22:34:26](https://github.com/leanprover-community/mathlib/commit/c2a30be)
feat(analysis/normed_space/normed_group_hom): add norm_noninc.neg ([#9658](https://github.com/leanprover-community/mathlib/pull/9658))
From LTE.

### [2021-10-11 21:39:10](https://github.com/leanprover-community/mathlib/commit/df132fe)
feat(topology/path_connected): add `path.reparam` for reparametrising a path. ([#9643](https://github.com/leanprover-community/mathlib/pull/9643))
I've also added `simps` to some of the definitions in this file.

### [2021-10-11 20:04:44](https://github.com/leanprover-community/mathlib/commit/136d0ce)
feat(topology/homotopy/path): Add homotopy between paths ([#9141](https://github.com/leanprover-community/mathlib/pull/9141))
There is also a lemma about `path.to_continuous_map` which I needed in a prior iteration of this PR that I missed in [#9133](https://github.com/leanprover-community/mathlib/pull/9133)

### [2021-10-11 18:55:35](https://github.com/leanprover-community/mathlib/commit/6872dfb)
feat(analysis/normed/group/basic): add norm_le_add_norm_add ([#9655](https://github.com/leanprover-community/mathlib/pull/9655))
From LTE.

### [2021-10-11 15:29:09](https://github.com/leanprover-community/mathlib/commit/fa5d9d6)
feat(tactic/lint/misc): unused haves and suffices linters ([#9310](https://github.com/leanprover-community/mathlib/pull/9310))
A linter for unused term mode have and suffices statements.
Based on initial work by @robertylewis https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/linter.20for.20helping.20grading/near/209243601 but hopefully with less false positives now.

### [2021-10-11 07:59:25](https://github.com/leanprover-community/mathlib/commit/c2fde70)
feat(number_theory/liouville): Liouville numbers form a dense Gδ set ([#9646](https://github.com/leanprover-community/mathlib/pull/9646))

### [2021-10-11 07:59:24](https://github.com/leanprover-community/mathlib/commit/082aa83)
feat(data/finset): add `finset.erase_none` ([#9630](https://github.com/leanprover-community/mathlib/pull/9630))
* move `option.to_finset` and `finset.insert_none` to a new file `data.finset.option`; redefine the latter in terms of `finset.cons`;
* define `finset.erase_none`, prove lemmas about it;
* add `finset.prod_cons`, `finset.sum_cons`, `finset.coe_cons`, `finset.cons_subset_cons`, `finset.card_cons`;
* add `finset.subtype_mono` and `finset.bUnion_congr`;
* add `set.insert_subset_insert_iff`;
* add `@[simp]` to `finset.map_subset_map`;
* upgrade `finset.map_embedding` to an `order_embedding`;
* add `@[simps]` to `equiv.option_is_some_equiv` and `function.embedding.some`;
* golf some proofs.

### [2021-10-11 07:59:23](https://github.com/leanprover-community/mathlib/commit/1539ee1)
refactor(topology/sheaves/*): Make sheaf condition a Prop ([#9607](https://github.com/leanprover-community/mathlib/pull/9607))
Make `sheaf_condition` into a `Prop` and redefine the type of sheaves on a topological space `X` as a subtype of `(opens X)ᵒᵖ ⥤ C`.

### [2021-10-11 07:59:22](https://github.com/leanprover-community/mathlib/commit/4a191ad)
feat(algebra.algebra.subalgebra): add `subalgebra.gc_map_comap` ([#9435](https://github.com/leanprover-community/mathlib/pull/9435))
Other changes:
* add `linear_map.coe_inl`/`linear_map.coe_inr` and move `@[simp]` from `inl_apply`/`inr_apply` to these lemmas;
* fix a typo in the name (`adjoint` → `adjoin`);
* drop `algebra.adjoin_inl_union_inr_le_prod `: we prove an equality anyway;
* add `alg_hom.map_adjoin` (same as `(adjoin_image _ _ _).symm`) to match `monoid_hom.map_closure` etc.

### [2021-10-11 06:17:12](https://github.com/leanprover-community/mathlib/commit/30cf8b7)
feat(group_theory/subgroup/basic): apply_mem_map_injective ([#9637](https://github.com/leanprover-community/mathlib/pull/9637))
A translation of `function.injective.mem_set_image`.

### [2021-10-11 06:17:11](https://github.com/leanprover-community/mathlib/commit/957f64e)
feat(algebra/floor): When the floor is strictly positive ([#9625](https://github.com/leanprover-community/mathlib/pull/9625))
`⌊a⌋₊` and `⌊a⌋` are strictly positive iff `1 ≤ a`. We use this to slightly golf IMO 2013 P5.

### [2021-10-11 04:03:52](https://github.com/leanprover-community/mathlib/commit/bcd79a1)
chore(analysis/normed/group/basic): rename vars ([#9652](https://github.com/leanprover-community/mathlib/pull/9652))
* use `E`, `F` for (semi)normed groups and greek letters for other
  types;
* golf some proofs (`bounded_iff_forall_norm_le`, `norm_pos_iff'`);
* use `namespace lipschitz_with` and `namespace antilipschitz_with`
  instead of manual prefixes for all lemmas;
* generalize `antilipschitz_with.add_lipschitz_with` to
  `pseudo_emetric_space`;
* add `antilipschitz_with.edist_lt_top` and
  `antilipschitz_with.edist_ne_top`;
* fix a typo in `pseudo_emetric_space.to_pseudo_metric_space`.

### [2021-10-11 04:03:51](https://github.com/leanprover-community/mathlib/commit/11117ec)
feat(topology/G_delta): a finite set is a Gδ-set ([#9644](https://github.com/leanprover-community/mathlib/pull/9644))

### [2021-10-11 04:03:50](https://github.com/leanprover-community/mathlib/commit/c02a655)
feat(linear_algebra/affine_space/barycentric_coords): we can recover a point from its barycentric coordinates ([#9629](https://github.com/leanprover-community/mathlib/pull/9629))
Formalized as part of the Sphere Eversion project.

### [2021-10-11 04:03:49](https://github.com/leanprover-community/mathlib/commit/0bd14ba)
feat(category_theory/limits/lattice): Add explicit formulas for limits in lattices ([#9608](https://github.com/leanprover-community/mathlib/pull/9608))
Add explicit descriptions of finite limits and colimits in complete lattices. In particular, the product and the pullback is equal to the infimum, while coproduct and pushout is the supremum. Furthermore, `limit_iso_infi` can be strengthened to an equality, as preorder categories are skeletal.

### [2021-10-11 04:03:48](https://github.com/leanprover-community/mathlib/commit/c803c8d)
feat(algebra/gcd_monoid): trivial `gcd` on `comm_group_with_zero`s ([#9602](https://github.com/leanprover-community/mathlib/pull/9602))
This PR extends the `normalization_monoid` defined on `comm_group_with_zero`s (e.g. fields) to a `normalized_gcd_monoid`. This is useful if you need to take the gcd of two polynomials in a field.

### [2021-10-11 04:03:47](https://github.com/leanprover-community/mathlib/commit/ec5835d)
chore(order/*): use to_dual and of_dual in statements instead of implicit coercions between and `α` and  `order_dual α`  ([#9593](https://github.com/leanprover-community/mathlib/pull/9593))
Previously the meaning of the statement was hidden away in an invisible surprising typeclass argument.
Before this change, the docs suggested the nonsensical statement that `monotone f` implies `antitone f`!
![image](https://user-images.githubusercontent.com/425260/136348562-d3ecbb85-2a54-4c13-adda-806eb150b00a.png)
Most of the proof changes in this PR are a consequence of changing the interval lemmas, not the monotonicity or convexity ones.

### [2021-10-11 04:03:45](https://github.com/leanprover-community/mathlib/commit/ef46da8)
feat(category_theory/*): Curried yoneda lemma ([#9579](https://github.com/leanprover-community/mathlib/pull/9579))
Provided curried versions of the Yoneda lemma when the category is small.

### [2021-10-11 02:26:38](https://github.com/leanprover-community/mathlib/commit/e32154d)
feat(data/equiv/ring): add basic API lemmas for ring_equiv ([#9639](https://github.com/leanprover-community/mathlib/pull/9639))
This PR adds the lemmas `map_inv`, `map_div`, `map_pow` and `map_fpow` for `ring_equiv`. These lemmas were already available for `ring_hom`s. I'm very open to suggestions about where they should go; `map_fpow` in particular requires a new import in `algebra/field_power.lean`.

### [2021-10-10 21:07:28](https://github.com/leanprover-community/mathlib/commit/64255e2)
chore(analysis): move some code to `analysis.normed.group.basic` ([#9642](https://github.com/leanprover-community/mathlib/pull/9642))

### [2021-10-10 21:07:27](https://github.com/leanprover-community/mathlib/commit/fa41436)
feat(algebra/*,group_theory/*): instances/lemmas about `is_scalar_tower` and `smul_comm_class` ([#9533](https://github.com/leanprover-community/mathlib/pull/9533))

### [2021-10-10 18:58:39](https://github.com/leanprover-community/mathlib/commit/0bba837)
chore(data/nat/factorial): use `n + 1` instead of `n.succ` in `nat.factorial_succ` ([#9645](https://github.com/leanprover-community/mathlib/pull/9645))

### [2021-10-10 09:54:18](https://github.com/leanprover-community/mathlib/commit/3d438ba)
feat(probability_theory/density): add continuous uniform distribution ([#9385](https://github.com/leanprover-community/mathlib/pull/9385))

### [2021-10-09 16:48:06](https://github.com/leanprover-community/mathlib/commit/54a4c17)
feat(group_theory/sylow): `set_like` instance for `sylow` ([#9641](https://github.com/leanprover-community/mathlib/pull/9641))
Adds a `set_like` instance for `sylow p G`.
Coauthored by @jcommelin

### [2021-10-09 14:56:51](https://github.com/leanprover-community/mathlib/commit/bb98444)
refactor(group_theory/congruence): remove old_structure_cmd ([#9622](https://github.com/leanprover-community/mathlib/pull/9622))

### [2021-10-09 09:53:15](https://github.com/leanprover-community/mathlib/commit/7ed091d)
feat(group_theory/perm/concrete_cycle): computable cyclic perm notation ([#9470](https://github.com/leanprover-community/mathlib/pull/9470))

### [2021-10-09 07:26:30](https://github.com/leanprover-community/mathlib/commit/ce50450)
chore(analysis/normed_space/linear_isometry): adjust `isometry` API ([#9635](https://github.com/leanprover-community/mathlib/pull/9635))
Now that we have the `linear_isometry` definition, it is better to pass through this definition rather then using a `linear_map` satisfying the `isometry` hypothesis.  To this end, convert old lemma `linear_map.norm_apply_of_isometry` to a new definition `linear_map.to_linear_isometry`, and delete old definition `continuous_linear_equiv.of_isometry`, whose use should be replaced by the pair of definitions`linear_map.to_linear_isometry`, `linear_isometry_equiv.of_surjective`.

### [2021-10-09 07:26:28](https://github.com/leanprover-community/mathlib/commit/a9643aa)
feat(order/min_max): min_cases and max_cases lemmata ([#9632](https://github.com/leanprover-community/mathlib/pull/9632))
These lemmata make the following type of argument work seamlessly:
```lean
example (h1 : 0 ≤ x) (h2 : x ≤ 1) : min 1 x ≤ max x 0 := by cases min_cases 1 x; cases max_cases x 0; linarith
```
See similar PR [#8124](https://github.com/leanprover-community/mathlib/pull/8124)

### [2021-10-09 07:26:25](https://github.com/leanprover-community/mathlib/commit/e0f80e7)
feat(analysis/convex/quasiconvex): Quasiconvexity of functions ([#9561](https://github.com/leanprover-community/mathlib/pull/9561))
A function is quasiconvex iff all its sublevels are convex. This generalizes unimodality to non-ordered spaces.

### [2021-10-09 04:58:07](https://github.com/leanprover-community/mathlib/commit/7a7fada)
refactor(data/nat/basic): finish removing sub lemmas ([#9601](https://github.com/leanprover-community/mathlib/pull/9601))
* Follow-up of [#9544](https://github.com/leanprover-community/mathlib/pull/9544) to remove the remaining sub lemmas on `nat` that can be generalized to `has_ordered_sub`.
* The renamings of the lemmas in mathlib that occurred at least once:
```
nat.sub_eq_of_eq_add -> sub_eq_of_eq_add_rev
nat.add_sub_sub_cancel -> add_sub_sub_cancel'
nat.sub_le_self -> sub_le_self'
```

### [2021-10-09 02:44:04](https://github.com/leanprover-community/mathlib/commit/7aaa1b4)
chore(scripts): update nolints.txt ([#9636](https://github.com/leanprover-community/mathlib/pull/9636))
I am happy to remove some nolints for you!

### [2021-10-08 21:56:11](https://github.com/leanprover-community/mathlib/commit/7e3fa4c)
chore(*): fix typos ([#9634](https://github.com/leanprover-community/mathlib/pull/9634))

### [2021-10-08 21:06:41](https://github.com/leanprover-community/mathlib/commit/70a9540)
refactor(group_theory/monoid_localization) remove old_structure_cmd ([#9621](https://github.com/leanprover-community/mathlib/pull/9621))

### [2021-10-08 20:24:14](https://github.com/leanprover-community/mathlib/commit/c37e3e7)
refactor(field_theory/intermediate_field): remove old_structure_cmd ([#9620](https://github.com/leanprover-community/mathlib/pull/9620))

### [2021-10-08 20:24:12](https://github.com/leanprover-community/mathlib/commit/b39feab)
refactor(algebra/lie): reduce use of old_structure_cmd ([#9616](https://github.com/leanprover-community/mathlib/pull/9616))

### [2021-10-08 17:52:23](https://github.com/leanprover-community/mathlib/commit/91ee8f1)
chore(data/equiv/ring): add big operator lemmas for ring equivs ([#9628](https://github.com/leanprover-community/mathlib/pull/9628))
This PR adds lemmas involving big operators (such as `map_sum`, `map_prod`, etc) for `ring_equiv`s.

### [2021-10-08 16:13:52](https://github.com/leanprover-community/mathlib/commit/57cd1e9)
feat(analysis/normed_space/exponential): remove char_p assumption ([#9618](https://github.com/leanprover-community/mathlib/pull/9618))
Remove the `char_p` assumption from `exp_series_eq_exp_series_of_field_extension` as suggested by @urkud here : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Undergraduate.20math.20list/near/256679511

### [2021-10-08 14:22:17](https://github.com/leanprover-community/mathlib/commit/5fd3664)
feat(algebra/graded_monoid): Split out graded monoids from graded rings ([#9586](https://github.com/leanprover-community/mathlib/pull/9586))
This cleans up the `direct_sum.gmonoid` typeclass to not contain a bundled morphism, which allows it to be used to describe graded monoids too, via the alias for `sigma` `graded_monoid`. Essentially, this:
* Renames:
  * `direct_sum.ghas_one` to `graded_monoid.has_one`
  * `direct_sum.ghas_mul` to `direct_sum.gnon_unital_non_assoc_semiring`
  * `direct_sum.gmonoid` to `direct_sum.gsemiring`
  * `direct_sum.gcomm_monoid` to `direct_sum.gcomm_semiring`
* Introduces new typeclasses which represent what the previous names should have been:
  * `graded_monoid.ghas_mul`
  * `graded_monoid.gmonoid`
  * `graded_monoid.gcomm_monoid` 
This doesn't do as much deduplication as I'd like, but it at least manages some.
There's not much in the way of new definitions here either, and most of the names are just copied from the graded ring case.

### [2021-10-08 14:22:16](https://github.com/leanprover-community/mathlib/commit/745cbfc)
feat(data/polynomial): %ₘ as a linear map  ([#9532](https://github.com/leanprover-community/mathlib/pull/9532))
This PR bundles `(%ₘ) = polynomial.mod_by_monic` into a linear map. In a follow-up PR, I'll show this map descends to a linear map `adjoin_root q → polynomial R`, thereby (computably) assigning coefficients to each element in `adjoin_root q`.

### [2021-10-08 12:12:57](https://github.com/leanprover-community/mathlib/commit/99c3e22)
refactor(geometry/manifold): remove old_structure_cmd ([#9617](https://github.com/leanprover-community/mathlib/pull/9617))

### [2021-10-08 12:12:56](https://github.com/leanprover-community/mathlib/commit/c107549)
refactor(ring_theory/valuation): remove unnecessary old_structure_cmd ([#9615](https://github.com/leanprover-community/mathlib/pull/9615))

### [2021-10-08 12:12:55](https://github.com/leanprover-community/mathlib/commit/7bdd10e)
refactor(order/category): remove old_structure_cmd ([#9614](https://github.com/leanprover-community/mathlib/pull/9614))

### [2021-10-08 12:12:54](https://github.com/leanprover-community/mathlib/commit/af09d3f)
refactor(algebra/absolute_value): remove unnecessary old_structure_cmd ([#9613](https://github.com/leanprover-community/mathlib/pull/9613))

### [2021-10-08 12:12:52](https://github.com/leanprover-community/mathlib/commit/25a45ab)
refactor(order/omega_complete_partial_order): remove old_structure_cmd ([#9612](https://github.com/leanprover-community/mathlib/pull/9612))
Removing a use of `old_structure_cmd`.

### [2021-10-08 12:12:51](https://github.com/leanprover-community/mathlib/commit/cea97d9)
feat(*): add not_mem_of_not_mem_closure for anything with subset_closure ([#9595](https://github.com/leanprover-community/mathlib/pull/9595))
This is a goal I would expect library search to finish if I have something not in a closure and I want it not in the base set.

### [2021-10-08 10:04:44](https://github.com/leanprover-community/mathlib/commit/6c9eee4)
refactor(data/finsupp/basic): remove sub lemmas ([#9603](https://github.com/leanprover-community/mathlib/pull/9603))
* Remove the finsupp sub lemmas that are special cases of lemmas in `algebra/order/sub`, namely:
  * `finsupp.nat_zero_sub`
  * `finsupp.nat_sub_self`
  * `finsupp.nat_add_sub_of_le`
  * `finsupp.nat_sub_add_cancel`
  * `finsupp.nat_add_sub_cancel`
  * `finsupp.nat_add_sub_cancel_left`
  * `finsupp.nat_add_sub_assoc`
* Rename the remaining lemmas to use `tsub`:
  * `finsupp.coe_nat_sub` → `finsupp.coe_tsub`
  * `finsupp.nat_sub_apply` → `finsupp.tsub_apply`
  Lemmas in `algebra/order/sub` will soon also use `tsub` (see [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_lt_mul''''))

### [2021-10-08 10:04:43](https://github.com/leanprover-community/mathlib/commit/34145b7)
feat(group_theory/subgroup/basic): a new to_additive lemma, and remove a by hand proof ([#9594](https://github.com/leanprover-community/mathlib/pull/9594))
I needed `add_subgroup.smul_mem` which didn't seem to exist, and noticed that the `add_subgroup.gsmul_mem` version is proved by hand while to_additive generates it fine (now?)

### [2021-10-08 10:04:41](https://github.com/leanprover-community/mathlib/commit/d5146f4)
feat(ring_theory): `adjoin_root g ≃ S` if `S` has a power basis with the right minpoly ([#9529](https://github.com/leanprover-community/mathlib/pull/9529))
This is basically `power_basis.equiv'` with slightly different hypotheses, specialised to `adjoin_root`. It guarantees that even over non-fields, a monogenic extension of `R` can be given by the polynomials over `R` modulo the relevant minimal polynomial.

### [2021-10-08 10:04:40](https://github.com/leanprover-community/mathlib/commit/82e2b98)
feat(ring_theory): generalize `power_basis.equiv` ([#9528](https://github.com/leanprover-community/mathlib/pull/9528))
`power_basis.equiv'` is an alternate formulation of `power_basis.equiv` that is somewhat more general when not over a field: instead of requiring the minimal polynomials are equal, we only require the generators are the roots of each other's minimal polynomials.
This is not quite enough to show `adjoin_root (minpoly R (pb : power_basis R S).gen)` is isomorphic to `S`, since `minpoly R (adjoin_root.root g)` is not guaranteed to have the same exact roots as `g` itself. So in a follow-up PR I will strengthen `power_basis.equiv'` to `adjoin_root.equiv'` that requires the correct hypothesis.

### [2021-10-08 10:04:39](https://github.com/leanprover-community/mathlib/commit/179a495)
feat(algebra/star/algebra): generalize to modules ([#9484](https://github.com/leanprover-community/mathlib/pull/9484))
This means there is now a `star_module ℂ (ι → ℂ)` instance available.
This adds `star_add_monoid`, and renames `star_algebra` to `star_module` with significantly relaxed typeclass arguments.
This also uses `export` to cut away some unnecessary definitions, and adds the missing `pi.star_def` to match `pi.add_def` etc.

### [2021-10-08 07:33:10](https://github.com/leanprover-community/mathlib/commit/9ecdd38)
chore(algebra/order/sub): generalize 2 lemmas ([#9611](https://github.com/leanprover-community/mathlib/pull/9611))
* generalize `lt_sub_iff_left` and `lt_sub_iff_right`;
* use general lemmas in `data.real.ennreal`.

### [2021-10-08 07:33:09](https://github.com/leanprover-community/mathlib/commit/639a7ef)
feat(algebra/order/ring): variants of mul_sub' ([#9604](https://github.com/leanprover-community/mathlib/pull/9604))
Add some variants of `mul_sub'` and `sub_mul'` and use them in `ennreal`. (Also sneaking in a tiny stylistic change in `topology/ennreal`.)

### [2021-10-08 07:33:08](https://github.com/leanprover-community/mathlib/commit/83a07ce)
feat(data/nat/log): add antitonicity lemmas for first argument ([#9597](https://github.com/leanprover-community/mathlib/pull/9597))
`log` and `clog` are only antitone on bases >1, so we include this as an
assumption in `log_le_log_of_left_ge` (resp. `clog_le_...`) and as a
domain restriction in `log_left_gt_one_anti` (resp. `clog_left_...`).

### [2021-10-08 07:33:06](https://github.com/leanprover-community/mathlib/commit/41dd4da)
feat(data/multiset/interval): Intervals as `multiset`s ([#9588](https://github.com/leanprover-community/mathlib/pull/9588))
This provides API for `multiset.Ixx` (except `multiset.Ico`).

### [2021-10-08 07:33:05](https://github.com/leanprover-community/mathlib/commit/c3768cc)
refactor(data/multiset/basic): remove sub lemmas ([#9578](https://github.com/leanprover-community/mathlib/pull/9578))
* Remove the multiset sub lemmas that are special cases of lemmas in `algebra/order/sub`
* [This](https://github.com/leanprover-community/mathlib/blob/14c3324143beef6e538f63da9c48d45f4a949604/src/data/multiset/basic.lean#L1513-L1538) gives the list of renamings.
* Use `derive` in `pnat.factors`.

### [2021-10-08 07:33:03](https://github.com/leanprover-community/mathlib/commit/c400677)
feat(algebra/module/basic): `module rat E` is a subsingleton ([#9570](https://github.com/leanprover-community/mathlib/pull/9570))
* allow different (semi)rings in `add_monoid_hom.map_int_cast_smul` and `add_monoid_hom.map_nat_cast_smul`;
* add `add_monoid_hom.map_inv_int_cast_smul` and `add_monoid_hom.map_inv_nat_cast_smul`;
* allow different division rings in `add_monoid_hom.map_rat_cast_smul`, drop `char_zero` assumption;
* prove `subsingleton (module rat M)`;
* add a few convenience lemmas.

### [2021-10-08 07:33:02](https://github.com/leanprover-community/mathlib/commit/eb3595e)
move(order/*): move from `algebra.order.` the files that aren't about algebra ([#9562](https://github.com/leanprover-community/mathlib/pull/9562))
`algebra.order.basic` and `algebra.order.functions` never mention `+`, `-` or `*`. Thus they belong under `order`.

### [2021-10-08 07:33:00](https://github.com/leanprover-community/mathlib/commit/8aa1893)
feat(group_theory/subgroup/basic): Analog of `mul_aut.conj` for normal subgroups. ([#9552](https://github.com/leanprover-community/mathlib/pull/9552))
Analog of `mul_aut.conj` for normal subgroups (pretty much just copying the code from `data/equiv/mul_add_aut.lean`).

### [2021-10-08 07:32:59](https://github.com/leanprover-community/mathlib/commit/1390b44)
feat(analysis/convex/function): API for strict convex functions ([#9437](https://github.com/leanprover-community/mathlib/pull/9437))
This provides all the basic API for `strict_convex_on` and `strict_concave_on`.

### [2021-10-08 07:32:58](https://github.com/leanprover-community/mathlib/commit/a0504eb)
refactor(data/*/interval): generalize `finset.Ico` to locally finite orders ([#7987](https://github.com/leanprover-community/mathlib/pull/7987))
`finset.Ico` currently goes `ℕ → ℕ → finset ℕ`. This generalizes it to `α → α → finset α` where `locally_finite_order α`.
This also ports all the existing `finset.Ico` lemmas to the new API, which involves renaming and moving them to `data.finset.interval` or `data.nat.interval` depending on whether I could generalize them away from `ℕ` or not.

### [2021-10-08 06:08:46](https://github.com/leanprover-community/mathlib/commit/ba2454e)
feat(ring_theory/coprime): two lemmas prereq for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9456](https://github.com/leanprover-community/mathlib/pull/9456))
Two variants of the fact that `¬ is_coprime 0 0`.

### [2021-10-08 02:40:18](https://github.com/leanprover-community/mathlib/commit/235bfd7)
chore(scripts): update nolints.txt ([#9610](https://github.com/leanprover-community/mathlib/pull/9610))
I am happy to remove some nolints for you!

### [2021-10-08 01:32:09](https://github.com/leanprover-community/mathlib/commit/9ea4568)
fix(topology/path_connected): add `continuity` to `path.continuous_extend` ([#9605](https://github.com/leanprover-community/mathlib/pull/9605))

### [2021-10-08 00:30:16](https://github.com/leanprover-community/mathlib/commit/fa3b622)
refactor(analysis/normed_space/linear_isometry): semilinear isometries ([#9551](https://github.com/leanprover-community/mathlib/pull/9551))
Generalize the theory of linear isometries to the semilinear setting.

### [2021-10-07 21:23:16](https://github.com/leanprover-community/mathlib/commit/9518ce1)
feat(topology/algebra): valued fields ([#9589](https://github.com/leanprover-community/mathlib/pull/9589))
This is a modernized version of code from the perfectoid spaces project.

### [2021-10-07 19:09:56](https://github.com/leanprover-community/mathlib/commit/ebccce9)
feat(measure_theory/covering/besicovitch): the measurable Besicovitch covering theorem ([#9576](https://github.com/leanprover-community/mathlib/pull/9576))
The measurable Besicovitch theorem ensures that, in nice metric spaces, if at every point one considers a class of balls of arbitrarily small radii, called admissible balls, then one can cover almost all the space by a family of disjoint admissible balls. It is deduced from the topological Besicovitch theorem.

### [2021-10-07 15:09:34](https://github.com/leanprover-community/mathlib/commit/8a60fd7)
refactor(data/ennreal/basic): prove has_ordered_sub instance ([#9582](https://github.com/leanprover-community/mathlib/pull/9582))
* Give `has_sub` and `has_ordered_sub` instances on `with_top α`.
* This gives a new subtraction on `ennreal`. The lemma `ennreal.sub_eq_Inf` proves that it is equal to the old value.
* Simplify many proofs about `sub` on `ennreal` 
* Proofs that are instantiations of more general lemmas will be removed in a subsequent PR
* Many lemmas that require `add_le_cancellable` in general are reformulated using `≠ ∞`
* Lemmas are reordered, but no lemmas are renamed, removed, or have a different type. Some `@[simp]` tags are removed if a more general simp lemma applies.
* Minor: generalize `preorder` to `has_le` in `has_ordered_sub` (not necessary for this PR, but useful in another (abandoned) branch).

### [2021-10-07 13:09:23](https://github.com/leanprover-community/mathlib/commit/bf76a1f)
feat(algebra/order/with_zero): add lt_of_mul_lt_mul_of_le₀ and mul_lt_mul_of_lt_of_le₀ ([#9596](https://github.com/leanprover-community/mathlib/pull/9596))

### [2021-10-07 11:57:08](https://github.com/leanprover-community/mathlib/commit/18a42f3)
feat(src/category_theory/*): Yoneda preserves limits. ([#9580](https://github.com/leanprover-community/mathlib/pull/9580))
Shows that `yoneda` and `coyoneda` preserves and reflects limits.

### [2021-10-07 06:55:11](https://github.com/leanprover-community/mathlib/commit/f874783)
feat(data/multiset/erase_dup): Alias for `multiset.erase_dup_eq_self` ([#9587](https://github.com/leanprover-community/mathlib/pull/9587))
The new `multiset.nodup.erase_dup` allows dot notation.

### [2021-10-07 06:55:10](https://github.com/leanprover-community/mathlib/commit/cc46f31)
feat(analysis/normed_space/add_torsor_bases): the interior of the convex hull of a finite affine basis is the set of points with strictly positive barycentric coordinates ([#9583](https://github.com/leanprover-community/mathlib/pull/9583))
Formalized as part of the Sphere Eversion project.

### [2021-10-07 06:14:33](https://github.com/leanprover-community/mathlib/commit/a7784aa)
feat(category_theory/*): Yoneda extension is Kan ([#9574](https://github.com/leanprover-community/mathlib/pull/9574))
- Proved that `(F.elements)ᵒᵖ ≌ costructured_arrow yoneda F`.
- Verified that the yoneda extension is indeed the left Kan extension along the yoneda embedding.

### [2021-10-07 06:14:32](https://github.com/leanprover-community/mathlib/commit/b9097f1)
feat(analysis/asymptotics): Define superpolynomial decay of a function ([#9440](https://github.com/leanprover-community/mathlib/pull/9440))
Define superpolynomial decay of functions in terms of asymptotics.is_O.

### [2021-10-07 04:15:17](https://github.com/leanprover-community/mathlib/commit/0bc7c2d)
fix(algebra/group/{prod,pi}): fix non-defeq `has_scalar` diamonds ([#9584](https://github.com/leanprover-community/mathlib/pull/9584))
This fixes diamonds in the following instances for nat- and int- actions:
* `has_scalar ℕ (α × β)`
* `has_scalar ℤ (α × β)`
* `has_scalar ℤ (Π a, β a)`
The last one revealed a diamond caused by inconsistent use of `pi_instance_derive_field`:
```lean
-- fails before this change
example [Π a, group $ β a] : group.to_div_inv_monoid (Π a, β a) = pi.div_inv_monoid := rfl
```

### [2021-10-07 04:15:16](https://github.com/leanprover-community/mathlib/commit/cb3c844)
feat(category_theory/limits/*): Filtered colimits preserves finite limits ([#9522](https://github.com/leanprover-community/mathlib/pull/9522))
Restated `category_theory.limits.colimit_limit_to_limit_colimit_is_iso` in terms of limit preserving.

### [2021-10-07 02:14:30](https://github.com/leanprover-community/mathlib/commit/7a2696d)
feat(category_theory/limits/preserves/*): Show that whiskering left preserves limits. ([#9581](https://github.com/leanprover-community/mathlib/pull/9581))

### [2021-10-07 02:14:29](https://github.com/leanprover-community/mathlib/commit/f37aeb0)
refactor(algebra/gcd_monoid): drop nontriviality assumptions  ([#9568](https://github.com/leanprover-community/mathlib/pull/9568))

### [2021-10-06 21:14:59](https://github.com/leanprover-community/mathlib/commit/f63786b)
refactor(data/finsupp/basic): has_ordered_sub on finsupp ([#9577](https://github.com/leanprover-community/mathlib/pull/9577))
* Generalize `has_sub` and `canonically_ordered_add_monoid` instances for any finsupp with codomain a `canonically_ordered_add_monoid` & `has_ordered_sub`.
* Provide `has_ordered_sub` instance in the same situation
* Generalize lemmas about `nat` to this situation.
* Prove some lemmas as special cases of `has_ordered_sub` lemmas. These will be removed in a subsequent PR.
* Simplify some lemmas about `α →₀ ℕ` using `has_ordered_sub` lemmas.
* Prove `nat.one_le_iff_ne_zero` (it's the second time I want to use it this week)

### [2021-10-06 21:14:58](https://github.com/leanprover-community/mathlib/commit/b4a9767)
feat(data/multiset/basic): has_ordered_sub multiset ([#9566](https://github.com/leanprover-community/mathlib/pull/9566))
* Provide `instance : has_ordered_sub (multiset α)`
* Prove most multiset subtraction lemmas as special cases of `has_ordered_sub` lemmas
* In a subsequent PR I will remove the specialized multiset lemmas

### [2021-10-06 21:14:56](https://github.com/leanprover-community/mathlib/commit/845d064)
feat(algebra/big_operators/finprod): add finprod.mem_dvd ([#9549](https://github.com/leanprover-community/mathlib/pull/9549))

### [2021-10-06 19:23:08](https://github.com/leanprover-community/mathlib/commit/b2ae195)
move(data/fin/*): group `fin` files under a `fin` folder ([#9524](https://github.com/leanprover-community/mathlib/pull/9524))

### [2021-10-06 18:27:53](https://github.com/leanprover-community/mathlib/commit/5c3cdd2)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are open maps (in finite dimensions over a complete field) ([#9543](https://github.com/leanprover-community/mathlib/pull/9543))
Using the open mapping theorem with a one-dimensional codomain feels a bit ridiculous but I see no reason not to do so.
Formalized as part of the Sphere Eversion project.

### [2021-10-06 17:48:50](https://github.com/leanprover-community/mathlib/commit/a7b4e78)
fix(computability/DFA): tighten regular pumping lemma to match standard textbooks ([#9585](https://github.com/leanprover-community/mathlib/pull/9585))
This PR slightly tightens the regular pumping lemma: the current version applies only to words that are of length at least the number of states in the DFA plus one. Here we remove the plus one.

### [2021-10-06 15:46:06](https://github.com/leanprover-community/mathlib/commit/bcd13a7)
refactor(data/equiv): split out `./set` from `./basic` ([#9560](https://github.com/leanprover-community/mathlib/pull/9560))
This move all the equivalences between sets-coerced-to-types to a new file, which makes `equiv/basic` a slightly more manageable size.
The only non-move change in this PR is the rewriting of `equiv.of_bijective` to not go via `equiv.of_injective`, as we already have all the fields available directly and this allows the latter to move to a separate file.
This will allow us to import `order_dual.lean` earlier, as we no longer have to define boolean algebras before equivalences are available.
This relates to [#4758](https://github.com/leanprover-community/mathlib/pull/4758).

### [2021-10-06 15:46:04](https://github.com/leanprover-community/mathlib/commit/0b356b0)
feat(analysis/normed_space/banach): open mapping theorem for maps between affine spaces ([#9540](https://github.com/leanprover-community/mathlib/pull/9540))
Formalized as part of the Sphere Eversion project.

### [2021-10-06 15:46:03](https://github.com/leanprover-community/mathlib/commit/5773bc6)
feat(group_theory/group_action/conj_act): conjugation action of groups ([#8627](https://github.com/leanprover-community/mathlib/pull/8627))

### [2021-10-06 14:53:28](https://github.com/leanprover-community/mathlib/commit/6abd6f2)
chore(ring_theory/witt_vector): fix a docstring ([#9575](https://github.com/leanprover-community/mathlib/pull/9575))

### [2021-10-06 13:44:03](https://github.com/leanprover-community/mathlib/commit/850d5d2)
feat(analysis/convex/function): Dual lemmas ([#9571](https://github.com/leanprover-community/mathlib/pull/9571))

### [2021-10-06 10:12:02](https://github.com/leanprover-community/mathlib/commit/8c65781)
refactor(data/nat/basic): remove sub lemmas ([#9544](https://github.com/leanprover-community/mathlib/pull/9544))
* Remove the nat sub lemmas that are special cases of lemmas in `algebra/order/sub`
* This PR does 90% of the work, some lemmas require a bit more work (which will be done in a future PR)
* Protect `ordinal.add_sub_cancel_of_le`
* Most fixes in other files were abuses of the definitional equality of `n < m` and `nat.succ n \le m`.
* [This](https://github.com/leanprover-community/mathlib/blob/7a5d15a955a92a90e1d398b2281916b9c41270b2/src/data/nat/basic.lean#L498-L611) gives the list of renamings.
* The regex to find 90+% of the occurrences of removed lemmas. Some lemmas were not protected, so might not be found this way.
```
nat.(le_sub_add|add_sub_cancel'|sub_add_sub_cancel|sub_cancel|sub_sub_sub_cancel_right|sub_add_eq_add_sub|sub_sub_assoc|lt_of_sub_pos|lt_of_sub_lt_sub_right|lt_of_sub_lt_sub_left|sub_lt_self|le_sub_right_of_add_le|le_sub_left_of_add_le|lt_sub_right_of_add_lt|lt_sub_left_of_add_lt|add_lt_of_lt_sub_right|add_lt_of_lt_sub_left|le_add_of_sub_le_right|le_add_of_sub_le_left|lt_add_of_sub_lt_right|lt_add_of_sub_lt_left|sub_le_left_of_le_add|sub_le_right_of_le_add|sub_lt_left_iff_lt_add|le_sub_left_iff_add_le|le_sub_right_iff_add_le|lt_sub_left_iff_add_lt|lt_sub_right_iff_add_lt|sub_lt_right_iff_lt_add|sub_le_sub_left_iff|sub_lt_sub_right_iff|sub_lt_sub_left_iff|sub_le_iff|sub_lt_iff)[^_]
```

### [2021-10-06 10:12:00](https://github.com/leanprover-community/mathlib/commit/facc1d2)
feat(topology/algebra): topology on a linear_ordered_comm_group_with_zero ([#9537](https://github.com/leanprover-community/mathlib/pull/9537))
This is a modernized version of code from the perfectoid spaces project.

### [2021-10-06 08:03:57](https://github.com/leanprover-community/mathlib/commit/b534fed)
refactor(analysis/{normed_space, inner_product_space}/dual): redefine using `linear_isometry` ([#9569](https://github.com/leanprover-community/mathlib/pull/9569))
Linear isometric embeddings appear naturally when studying the duals of normed spaces:  the map `λ y, ⟪x, y⟫` from an inner product space to its dual is a linear isometric embedding++, and so is the canonical map from a normed space to its double dual**.
When these natural maps were defined last year, we didn't have the definition `linear_isometry` (notation: `X →ₗᵢ[R] Y`), so they were defined as continuous linear maps which satisfied the predicate `isometry`, and several lemmas were proven ad-hoc which are now available as general lemmas about  `linear_isometry`.
This PR refactors to use the `linear_isometry` structure.  Lemmas deleted (I have been enthusiastic here, and can scale back if desired ...):
normed_space.inclusion_in_double_dual_isometry
inner_product_space.to_dual_map_isometry
inner_product_space.to_dual_map_injective
inner_product_space.ker_to_dual_map
inner_product_space.to_dual_map_eq_iff_eq 
inner_product_space.range_to_dual_map
inner_product_space.isometric.to_dual
inner_product_space.to_dual_eq_iff_eq
inner_product_space.to_dual_eq_iff_eq'
inner_product_space.norm_to_dual_apply
inner_product_space.norm_to_dual_symm_apply
++ (over `ℝ` -- over `ℂ` it's conjugate-linear, which will be dealt with in future PRs)
** over `ℝ` or `ℂ`

### [2021-10-06 08:03:56](https://github.com/leanprover-community/mathlib/commit/e52e533)
feat(order/bounds): Antitone lemmas ([#9556](https://github.com/leanprover-community/mathlib/pull/9556))

### [2021-10-06 06:05:04](https://github.com/leanprover-community/mathlib/commit/f811910)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are 1 in zero dimensions ([#9564](https://github.com/leanprover-community/mathlib/pull/9564))

### [2021-10-06 01:36:04](https://github.com/leanprover-community/mathlib/commit/db5ee76)
chore(linear_algebra/quadratic_form): squeeze simps ([#9572](https://github.com/leanprover-community/mathlib/pull/9572))
[#9567](https://github.com/leanprover-community/mathlib/pull/9567) speeds up the slowest declaration in the file, but many other declarations are also slow.
This PR squeezes all simps.

### [2021-10-05 21:57:44](https://github.com/leanprover-community/mathlib/commit/fdf8a71)
feat(topology/bases): a family of nonempty disjoint open sets is countable in a separable space ([#9557](https://github.com/leanprover-community/mathlib/pull/9557))
Together with unrelated small lemmas on balls and on `pairwise_on`.

### [2021-10-05 21:57:43](https://github.com/leanprover-community/mathlib/commit/815eaca)
feat(analysis/normed_space/affine_isometry): affine maps are open iff their underlying linear maps are ([#9538](https://github.com/leanprover-community/mathlib/pull/9538))
Formalized as part of the Sphere Eversion project.

### [2021-10-05 19:53:22](https://github.com/leanprover-community/mathlib/commit/63903f2)
doc(linear_algebra/free_module/strong_rank_condition): correct a typo ([#9565](https://github.com/leanprover-community/mathlib/pull/9565))

### [2021-10-05 19:53:21](https://github.com/leanprover-community/mathlib/commit/0b57520)
feat(order/bounds): Image under an `order_iso` and `upper_bounds` commute ([#9555](https://github.com/leanprover-community/mathlib/pull/9555))

### [2021-10-05 19:53:20](https://github.com/leanprover-community/mathlib/commit/111d73b)
feat(data/int/interval): Finite intervals in ℤ ([#9526](https://github.com/leanprover-community/mathlib/pull/9526))
This proves that `ℤ` is a locally finite order.

### [2021-10-05 17:44:36](https://github.com/leanprover-community/mathlib/commit/7455f47)
chore(linear_algebra/quadratic_form): speed up quadratic_form.lin_mul_lin ([#9567](https://github.com/leanprover-community/mathlib/pull/9567))
In my single profiler run, this reduced elaboration time from 20s to 1.5s.

### [2021-10-05 11:41:22](https://github.com/leanprover-community/mathlib/commit/5926f10)
fix(data/equiv/basic): use `subtype p` not `coe_sort (set_of p)` ([#9559](https://github.com/leanprover-community/mathlib/pull/9559))
`↥{x | p x}` is just a clumsy way to write `{x // p x}`.

### [2021-10-05 10:10:30](https://github.com/leanprover-community/mathlib/commit/da4d550)
chore(measure_theory/*): better names and notations, add easy lemmas ([#9554](https://github.com/leanprover-community/mathlib/pull/9554))
* Localize notation for absolutely continuous in the `measure_theory` namespace, and add separate notations for the case of measures and of vector measures.
* Standardize some names, using `measure` instead of `meas`.
* Add two lemmas on measures with density.

### [2021-10-05 10:10:29](https://github.com/leanprover-community/mathlib/commit/e7ea02f)
feat(analysis/convex/basic): Levels of a monotone/antitone function ([#9547](https://github.com/leanprover-community/mathlib/pull/9547))
The set of points whose image under a monotone function is less than a fixed value is convex, when the space is linear.

### [2021-10-05 10:10:28](https://github.com/leanprover-community/mathlib/commit/5b79319)
feat(ring_theory/polynomial/basic): add a lemma `polynomial_quotient_equiv_quotient_polynomial_map_mk` ([#9542](https://github.com/leanprover-community/mathlib/pull/9542))

### [2021-10-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/2666033)
refactor(algebra/gcd_monoid): don't require normalization ([#9443](https://github.com/leanprover-community/mathlib/pull/9443))
This will allow us to set up a gcd_monoid instance for all euclidean_domains and generalize the results in ring_theory/euclidean_domain.lean to PIDs.

### [2021-10-05 08:58:55](https://github.com/leanprover-community/mathlib/commit/def4814)
refactor(topology/algebra/module): continuous semilinear maps ([#9539](https://github.com/leanprover-community/mathlib/pull/9539))
Generalize the theory of continuous linear maps to the semilinear setting.
We introduce a notation `∘L` for composition of continuous linear (i.e., not semilinear) maps, used sporadically to help with unification.  See [#8857](https://github.com/leanprover-community/mathlib/pull/8857) for a discussion of a related problem and fix.

### [2021-10-05 08:05:44](https://github.com/leanprover-community/mathlib/commit/fefd8a3)
refactor(analysis/convex/*): prove `convex_independent_iff_finset` without full Carathéodory ([#9550](https://github.com/leanprover-community/mathlib/pull/9550))
Also relax one `add_comm_group` to `add_comm_monoid` and two `𝕜` to `β` + `module 𝕜 β`, and simplify imports.

### [2021-10-05 08:05:43](https://github.com/leanprover-community/mathlib/commit/c42786f)
feat(topology/algebra): adic topology ([#9521](https://github.com/leanprover-community/mathlib/pull/9521))
This is a modernized version of code from the perfectoid spaces project.

### [2021-10-05 08:05:41](https://github.com/leanprover-community/mathlib/commit/61cd266)
ci(.github/workflows): automatically remove awaiting-CI label ([#9491](https://github.com/leanprover-community/mathlib/pull/9491))
This PR adds a job to our CI which removes the label "awaiting-CI" when the build finishes successfully.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/awaiting-CI.2C.20.23bors.2C.20and.20the.20PR.20.23queue/near/255754196)

### [2021-10-05 03:31:26](https://github.com/leanprover-community/mathlib/commit/1536412)
refactor(data/polynomial): use `monic.ne_zero` and `nontriviality` ([#9530](https://github.com/leanprover-community/mathlib/pull/9530))
There is a pattern in `data/polynomial` to have both `(hq : q.monic) (hq0 : q ≠ 0)` as assumptions. I found this less convenient to work with than `[nontrivial R] (hq : q.monic)` and using `monic.ne_zero` to replace `hq0`.
The `nontriviality` tactic automates all the cases where previously `nontrivial R` (or similar) was manually derived from the hypotheses.

### [2021-10-05 02:21:57](https://github.com/leanprover-community/mathlib/commit/fd18953)
chore(scripts): update nolints.txt ([#9553](https://github.com/leanprover-community/mathlib/pull/9553))
I am happy to remove some nolints for you!

### [2021-10-05 01:26:25](https://github.com/leanprover-community/mathlib/commit/0491621)
docs(ring_theory/adjoin_root): fix docstring ([#9546](https://github.com/leanprover-community/mathlib/pull/9546))

### [2021-10-05 01:26:24](https://github.com/leanprover-community/mathlib/commit/7466424)
feat(number_theory/padics): add padic_norm lemmas ([#9527](https://github.com/leanprover-community/mathlib/pull/9527))

### [2021-10-04 23:18:15](https://github.com/leanprover-community/mathlib/commit/3aac8e5)
fix(order/sub): make arguments explicit ([#9541](https://github.com/leanprover-community/mathlib/pull/9541))
* This makes some arguments of lemmas explicit.
* These lemmas were not used in places where the implicitness/explicitness of the arguments matters
* Providing the arguments is sometimes useful, especially in `rw ← ...`
* This follows the explicitness of similar lemmas (like the instantiations for `nat`).

### [2021-10-04 19:37:54](https://github.com/leanprover-community/mathlib/commit/10da8e6)
feat(set_theory/cardinal,*): assorted lemmas ([#9516](https://github.com/leanprover-community/mathlib/pull/9516))
### New instances
* a denumerable type is infinite;
* `Prop` is (noncomputably) enumerable;
* `Prop` is nontrivial;
* `cardinal.can_lift_cardinal_Type`: lift `cardinal.{u}` to `Type u`.
### New lemmas / attrs
* `quotient.out_equiv_out` : `x.out ≈ y.out ↔ x = y`;
* `quotient.out_inj` : `x.out = y.out ↔ x = y`;
* `cardinal.lift_bit0`, `cardinal.lift_bit1`, `cardinal.lift_two`, `cardinal.lift_prod` :
  new lemmas about `cardinal.lift`;
* `cardinal.omega_le_lift` and `cardinal.lift_le_omega` : simplify `ω ≤ lift c` and `lift c ≤ ω`;
* `cardinal.omega_le_add_iff`, `cardinal.encodable_iff`, `cardinal.mk_le_omega`,
  `cardinal.mk_denumerable`: new lemmas about `cardinal.omega`;
* add `@[simp]` attribute to `cardinal.mk_univ`, add `cardinal.mk_insert`;
* generalize `cardinal.nat_power_eq` to `cardinal.power_eq_two_power` and `cardinal.prod_eq_two_power`.

### [2021-10-04 19:37:52](https://github.com/leanprover-community/mathlib/commit/50b51c5)
refactor(group_theory/is_p_group): Generalize `is_p_group.comap_injective` ([#9509](https://github.com/leanprover-community/mathlib/pull/9509))
`is_p_group.comap_injective` (comap along injective preserves p-groups) can be generalized to `is_p_group.comap_ker_is_p_group` (comap with p-group kernel preserves p-groups). This also simplifies the proof of `is_p_group.to_sup_of_normal_right`

### [2021-10-04 15:09:53](https://github.com/leanprover-community/mathlib/commit/7a5d15a)
feat(data/pnat/interval): Finite intervals in ℕ+ ([#9534](https://github.com/leanprover-community/mathlib/pull/9534))
This proves that `ℕ+` is a locally finite order.

### [2021-10-04 15:09:52](https://github.com/leanprover-community/mathlib/commit/e998e4c)
feat(order/conditionally_complete_lattice): image and cSup commute ([#9510](https://github.com/leanprover-community/mathlib/pull/9510))

### [2021-10-04 15:09:51](https://github.com/leanprover-community/mathlib/commit/d8968ba)
feat(algebra/order/functions): recursors and images under monotone maps ([#9505](https://github.com/leanprover-community/mathlib/pull/9505))

### [2021-10-04 15:09:50](https://github.com/leanprover-community/mathlib/commit/fa52067)
refactor(order/fixed_points): rewrite using bundled `preorder_hom`s ([#9497](https://github.com/leanprover-community/mathlib/pull/9497))
This way `fixed_points.complete_lattice` can be an instance.

### [2021-10-04 15:09:49](https://github.com/leanprover-community/mathlib/commit/387ff6e)
feat(topology/homotopy): add `homotopy_with` ([#9252](https://github.com/leanprover-community/mathlib/pull/9252))
Added `homotopy_with` as in [`HOL-Analysis`](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html) extending `homotopy`. Furthermore, I've added `homotopy_rel`.
Also rename/moved the file. There is also some refactoring which is part of the suggestions from [#9141](https://github.com/leanprover-community/mathlib/pull/9141) .

### [2021-10-04 14:16:41](https://github.com/leanprover-community/mathlib/commit/f6c77be)
fix(ci): always use python3 executable ([#9531](https://github.com/leanprover-community/mathlib/pull/9531))
On many (particularly older) systems, the `python` command can refer to `python2` instead of `python3`.  Therefore we change all `python` calls to `python3` to prevent failures on some self-hosted runners.

### [2021-10-04 14:16:40](https://github.com/leanprover-community/mathlib/commit/a07d1de)
feat(data/fin/interval): Finite intervals in `fin n` ([#9523](https://github.com/leanprover-community/mathlib/pull/9523))

### [2021-10-04 13:23:23](https://github.com/leanprover-community/mathlib/commit/15d987a)
feat(probability_theory/notation): add notations for expected value, conditional expectation ([#9469](https://github.com/leanprover-community/mathlib/pull/9469))
When working in probability theory, the measure on the space is most often implicit. With our current notations for measure spaces, that means writing `volume` in a lot of places. To avoid that and introduce notations closer to the usual practice, this PR defines
- `𝔼[X]` for the expected value (integral) of a function `X` over the volume measure,
- `P[X]` for the expected value over the measure `P`,
- `𝔼[X | hm]` for the conditional expectation with respect to the volume,
- `X =ₐₛ Y` for `X =ᵐ[volume] Y` and similarly for `X ≤ᵐ[volume] Y`,
- `∂P/∂Q` for `P.rn_deriv Q`
All notations are localized to the `probability_theory` namespace.

### [2021-10-04 09:48:18](https://github.com/leanprover-community/mathlib/commit/ab7d251)
feat(measure_theory/covering/besicovitch_vector_space): vector spaces satisfy the assumption of Besicovitch covering theorem ([#9461](https://github.com/leanprover-community/mathlib/pull/9461))
The Besicovitch covering theorem works in any metric space subject to a technical condition: there should be no satellite configuration of `N+1` points, for some `N`. We prove that this condition is satisfied in finite-dimensional real vector spaces. Moreover, we get the optimal bound for `N`: it coincides with the maximal number of `1`-separated points that fit in a ball of radius `2`, by [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994]

### [2021-10-04 09:48:17](https://github.com/leanprover-community/mathlib/commit/b6f94a9)
feat(analysis/special_functions): real derivs of `complex.exp` and `complex.log` ([#9422](https://github.com/leanprover-community/mathlib/pull/9422))

### [2021-10-04 09:48:16](https://github.com/leanprover-community/mathlib/commit/1faf964)
feat(ring_theory/algebraic_independent): Existence of transcendence bases and rings are algebraic over transcendence basis ([#9377](https://github.com/leanprover-community/mathlib/pull/9377))

### [2021-10-04 09:48:14](https://github.com/leanprover-community/mathlib/commit/8a05dca)
feat(order/jordan_holder): Jordan Hölder theorem ([#8976](https://github.com/leanprover-community/mathlib/pull/8976))
The Jordan Hoelder theorem proved for a Jordan Hölder lattice, instances of which include submodules of a module and subgroups of a group.

### [2021-10-04 09:48:13](https://github.com/leanprover-community/mathlib/commit/abe81bc)
feat(linear_algebra/matrix/general_linear_group): GL(n, R) ([#8466](https://github.com/leanprover-community/mathlib/pull/8466))
added this file which contains definition of the general linear group as well as the subgroup of matrices with positive determinant.

### [2021-10-04 08:10:26](https://github.com/leanprover-community/mathlib/commit/edb22fe)
feat(topology/algebra): nonarchimedean filter bases ([#9511](https://github.com/leanprover-community/mathlib/pull/9511))
This is preparatory material for adic topology. It is a modernized version of code from the perfectoid spaces project.

### [2021-10-04 08:10:24](https://github.com/leanprover-community/mathlib/commit/6bd6afa)
feat(data/nat/interval): finite intervals of naturals ([#9507](https://github.com/leanprover-community/mathlib/pull/9507))
This proves that `ℕ` is a `locally_finite_order`.

### [2021-10-04 08:10:23](https://github.com/leanprover-community/mathlib/commit/dc1b045)
feat(linear_algebra/free_module/strong_rank_condition): add `comm_ring_strong_rank_condition` ([#9486](https://github.com/leanprover-community/mathlib/pull/9486))
We add `comm_ring_strong_rank_condition`: any commutative ring satisfies the strong rank condition.
Because of a circular import, this can't be in `linear_algebra.invariant_basis_number`.

### [2021-10-04 08:10:22](https://github.com/leanprover-community/mathlib/commit/6a6b4d0)
feat(category_theory/sites/*): Cover-lifting functors on sites ([#9431](https://github.com/leanprover-community/mathlib/pull/9431))
This PR defines cover-liftings functors between sites, and proves that `Ran F.op` maps sheaves to sheaves for cover-lifting functors `F`. 
This will probably be needed when we want to glue B-sheaves into sheaves.

### [2021-10-04 05:54:42](https://github.com/leanprover-community/mathlib/commit/d677c29)
feat(field_theory/algebraic_closure): versions of exists_aeval_eq_zero for rings ([#9517](https://github.com/leanprover-community/mathlib/pull/9517))

### [2021-10-03 20:33:50](https://github.com/leanprover-community/mathlib/commit/52495a0)
chore(data/set/lattice): fix name ([#9520](https://github.com/leanprover-community/mathlib/pull/9520))
`comp` is for composition, `compl` for complement. Fix names using `comp` instead of `compl`.

### [2021-10-03 20:33:49](https://github.com/leanprover-community/mathlib/commit/465508f)
split(order/monotone): split off `order.basic` ([#9518](https://github.com/leanprover-community/mathlib/pull/9518))

### [2021-10-03 20:33:48](https://github.com/leanprover-community/mathlib/commit/c0f7c56)
feat(algebra/order): exists_square_le ([#9513](https://github.com/leanprover-community/mathlib/pull/9513))
This is a modernized version of code from the perfectoid project.

### [2021-10-03 20:33:47](https://github.com/leanprover-community/mathlib/commit/bc5a081)
feat(topology/algebra): Cauchy filters on groups ([#9512](https://github.com/leanprover-community/mathlib/pull/9512))
This adds a tiny file but putting this lemma in `topology/algebra/filter_basis.lean` would make that file import a lot of uniform spaces theory. This is a modernized version of code from the perfectoid spaces project.

### [2021-10-03 20:33:46](https://github.com/leanprover-community/mathlib/commit/44f4d70)
chore(*): use dot-notation for is_conj.symm and is_conj.trans ([#9498](https://github.com/leanprover-community/mathlib/pull/9498))
renames:
* is_conj_refl -> is_conj.refl
* is_conj_symm -> is_conj.symm
* is_conj_trans -> is_conj.trans

### [2021-10-03 20:33:45](https://github.com/leanprover-community/mathlib/commit/c1936c1)
feat(order/basic): define `is_top` and `is_bot` ([#9493](https://github.com/leanprover-community/mathlib/pull/9493))
These predicates allow us to formulate & prove some theorems
simultaneously for the cases `[order_top α]` and `[no_top_order α]`.

### [2021-10-03 18:50:48](https://github.com/leanprover-community/mathlib/commit/e789ad3)
feat(group_theory/subgroup): mk lemmas ([#9514](https://github.com/leanprover-community/mathlib/pull/9514))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/set_like.20idiom

### [2021-10-03 15:22:43](https://github.com/leanprover-community/mathlib/commit/d260894)
feat(analysis/convex/combination): lemmas connecting convex hull with affine combinations and barycentric coordinates ([#9499](https://github.com/leanprover-community/mathlib/pull/9499))

### [2021-10-03 11:42:58](https://github.com/leanprover-community/mathlib/commit/cff9927)
refactor(ring_theory/unique_factorization_domain): rename unique_factorization_monoid.factors ([#9503](https://github.com/leanprover-community/mathlib/pull/9503))
This frees up the name for the non-normalizing version.

### [2021-10-03 11:42:57](https://github.com/leanprover-community/mathlib/commit/18e7f91)
feat(group_theory/quotient_group): if a quotient is trivial then the subgroup is the whole group ([#9092](https://github.com/leanprover-community/mathlib/pull/9092))

### [2021-10-03 10:10:01](https://github.com/leanprover-community/mathlib/commit/55c30c6)
feat(topology/basic): interior of finite intersection is intersection of interiors ([#9508](https://github.com/leanprover-community/mathlib/pull/9508))
And likewise for finite unions and closures.

### [2021-10-03 09:15:42](https://github.com/leanprover-community/mathlib/commit/2807d83)
feat(analysis/normed_space/add_torsor_bases): barycentric coordinates are continuous ([#9515](https://github.com/leanprover-community/mathlib/pull/9515))

### [2021-10-03 06:55:59](https://github.com/leanprover-community/mathlib/commit/7d83ff1)
feat(analysis/special_functions/exp_log): prove continuity of exp without derivatives ([#9501](https://github.com/leanprover-community/mathlib/pull/9501))
This is a first step towards making the definition of log and rpow independent of derivatives. The final goal is to avoid importing all of calculus in measure_theory/function/lp_space.lean .

### [2021-10-03 01:38:49](https://github.com/leanprover-community/mathlib/commit/5f803fa)
feat(analysis/convex/function): helper lemmas and general cleanup ([#9438](https://github.com/leanprover-community/mathlib/pull/9438))
This adds
* `convex_iff_pairwise_on_pos`
* `convex_on_iff_forall_pos`, `concave_on_iff_forall_pos`,
* `convex_on_iff_forall_pos_ne`, `concave_on_iff_forall_pos_ne`
* `convex_on.convex_strict_epigraph`, `concave_on.convex_strict_hypograph`
generalizes some instance assumptions:
* `convex_on.translate_` didn't need `module 𝕜 β` but `has_scalar 𝕜 β`.
* some proofs in `analysis.convex.exposed` were vestigially using `ℝ`.
 
and golfs proofs.

### [2021-10-02 23:49:54](https://github.com/leanprover-community/mathlib/commit/7b02277)
chore(topology/*): more lemmas about `dense`/`dense_range` ([#9492](https://github.com/leanprover-community/mathlib/pull/9492))

### [2021-10-02 17:58:29](https://github.com/leanprover-community/mathlib/commit/c46a04a)
chore(measure_theory): move, deduplicate ([#9489](https://github.com/leanprover-community/mathlib/pull/9489))
* move lemmas like `is_compact.measure_lt_top` from `measure_theory.constructions.borel` to `measure_theory.measure.measure_space`;
* drop `is_compact.is_finite_measure` etc;
* add `measure_Ixx_lt_top`.

### [2021-10-02 17:58:27](https://github.com/leanprover-community/mathlib/commit/a97e86a)
chore(ring_theory/ideal): some simp attributes ([#9487](https://github.com/leanprover-community/mathlib/pull/9487))

### [2021-10-02 16:08:36](https://github.com/leanprover-community/mathlib/commit/e60dc2b)
docs(measure_theory/integral/lebesgue): Add "Markov's inequality" to the doc string of `mul_meas_ge_le_lintegral` ([#9506](https://github.com/leanprover-community/mathlib/pull/9506))

### [2021-10-02 16:08:34](https://github.com/leanprover-community/mathlib/commit/110c740)
refactor(linear_algebra/charpoly): split in two files ([#9485](https://github.com/leanprover-community/mathlib/pull/9485))
We split `linear_algebra/charpoly` in `linear_algebra/charpoly/basic` and `linear_algebra/charpoly/to_matrix`.
Currently in `linear_algebra/charpoly/to_matrix` we only prove `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. This needs to be in a separate file then the definition of `f.charpoly` since it needs the invariant basis number property for commutative rings and in a future PR I will prove this as a special case of the fact that any commutative ring satisfies the strong rank condition, but the proof of this uses the characteristic polynomial.
We plan to add ohter results regarding the characteristic polynomial in the future.

### [2021-10-02 16:08:33](https://github.com/leanprover-community/mathlib/commit/1ceebca)
refactor(linear_algebra/free_module_pid): move linear_algebra/free_module_pid to linear_algebra/free_module/pid ([#9482](https://github.com/leanprover-community/mathlib/pull/9482))
We move `linear_algebra/free_module_pid` to `linear_algebra/free_module/pid`.

### [2021-10-02 16:08:31](https://github.com/leanprover-community/mathlib/commit/fa7fdca)
feat(measure_theory/function/ae_eq_of_integral): two ennreal-valued function are a.e. equal if their integrals agree ([#9372](https://github.com/leanprover-community/mathlib/pull/9372))

### [2021-10-02 13:51:01](https://github.com/leanprover-community/mathlib/commit/241aad7)
feat(data/finset/interval): API for `finset.Ixx` ([#9495](https://github.com/leanprover-community/mathlib/pull/9495))
This proves basic results about `finset.Ixx` & co. Lemma names (should) match their `set` counterparts.

### [2021-10-02 12:12:09](https://github.com/leanprover-community/mathlib/commit/f3746ea)
chore(src/analysis/special_functions/trigonometric/basic) : prove continuity of sin/cos/sinh/cosh without derivatives ([#9502](https://github.com/leanprover-community/mathlib/pull/9502))
In a future PR, I want to split all files in the special_functions folder to avoid importing calculus when not needed (the goal is to avoid importing it in the definition of lp_space in measure_theory). This PR changes the proofs of continuity of trigonometric functions.

### [2021-10-02 09:30:39](https://github.com/leanprover-community/mathlib/commit/e26a9e5)
feat(measure_theory/covering/besicovitch): the Besicovitch covering theorem ([#9462](https://github.com/leanprover-community/mathlib/pull/9462))
The Besicovitch covering theorem: in a nice metric space (e.g. real vector spaces), from any family of balls one can extract `N` subfamilies made of disjoint balls, covering all the centers of the balls in the family. The number `N` only depends on the metric space.

### [2021-10-02 09:30:37](https://github.com/leanprover-community/mathlib/commit/9e54ad0)
feat(ring_theory/algebraic_independent): algebraic independence ([#9229](https://github.com/leanprover-community/mathlib/pull/9229))

### [2021-10-02 07:33:19](https://github.com/leanprover-community/mathlib/commit/709b449)
chore(algebra/star/basic): provide automorphisms in commutative rings ([#9483](https://github.com/leanprover-community/mathlib/pull/9483))
This adds `star_mul_aut` and `star_ring_aut`, which are the versions of `star_mul_equiv` and `star_ring_equiv` which avoid needing `opposite` due to commutativity.

### [2021-10-02 07:33:18](https://github.com/leanprover-community/mathlib/commit/fc7f9f3)
feat(algebra/algebra): the range of `algebra_map (S : subalgebra R A) A` ([#9450](https://github.com/leanprover-community/mathlib/pull/9450))

### [2021-10-02 07:33:17](https://github.com/leanprover-community/mathlib/commit/a59876f)
feat(ring_theory): quotients of a noetherian ring are noetherian ([#9449](https://github.com/leanprover-community/mathlib/pull/9449))

### [2021-10-02 04:58:50](https://github.com/leanprover-community/mathlib/commit/37f43bf)
feat(linear_algebra/affine_space/barycentric_coords): define barycentric coordinates ([#9472](https://github.com/leanprover-community/mathlib/pull/9472))

### [2021-10-01 23:08:54](https://github.com/leanprover-community/mathlib/commit/06b184f)
refactor(analysis/convex/caratheodory): generalize ℝ to an arbitrary linearly ordered field ([#9479](https://github.com/leanprover-community/mathlib/pull/9479))
As a result; `convex_independent_iff_finset` also gets generalized.

### [2021-10-01 20:36:04](https://github.com/leanprover-community/mathlib/commit/118d45a)
doc(ring_theory/subring): fix docstring of `subring.center` ([#9494](https://github.com/leanprover-community/mathlib/pull/9494))

### [2021-10-01 20:36:02](https://github.com/leanprover-community/mathlib/commit/e6f8ad7)
refactor(analysis/convex/cone): generalize ℝ to an ordered semiring ([#9481](https://github.com/leanprover-community/mathlib/pull/9481))
Currently, `convex_cone` is only defined in ℝ-modules. This generalizes ℝ to an arbitray ordered semiring. `convex_cone E` is now spelt `convex_cone 𝕜 E`. Similarly, `positive_cone E` becomes `positive_cone 𝕜 E`.

### [2021-10-01 20:36:00](https://github.com/leanprover-community/mathlib/commit/05ee42c)
feat(order/circular): define circular orders ([#9413](https://github.com/leanprover-community/mathlib/pull/9413))
A circular order is the way to formalize positions on a circle. This is very foundational, as a good lot of the order-algebra-topology hierarchy has a circular analog.

### [2021-10-01 20:35:59](https://github.com/leanprover-community/mathlib/commit/5c92eb0)
feat(measure_theory/function/conditional_expectation): conditional expectation on real functions equal Radon-Nikodym derivative ([#9378](https://github.com/leanprover-community/mathlib/pull/9378))

### [2021-10-01 20:35:58](https://github.com/leanprover-community/mathlib/commit/75d022b)
feat(probability_theory/density): define probability density functions ([#9323](https://github.com/leanprover-community/mathlib/pull/9323))
This PR also proves some elementary properties about probability density function such as the law of the unconscious statistician.

### [2021-10-01 18:34:46](https://github.com/leanprover-community/mathlib/commit/6354fe9)
feat(topology/algebra): discrete group criterion ([#9488](https://github.com/leanprover-community/mathlib/pull/9488))

### [2021-10-01 18:34:45](https://github.com/leanprover-community/mathlib/commit/a5fc0a3)
feat(topology/algebra): filters bases for algebra ([#9480](https://github.com/leanprover-community/mathlib/pull/9480))
This is modernized version of code from the perfectoid spaces project.

### [2021-10-01 17:21:37](https://github.com/leanprover-community/mathlib/commit/db6d862)
split(analysis/convex/basic): split off `analysis.convex.hull` ([#9477](https://github.com/leanprover-community/mathlib/pull/9477))

### [2021-10-01 15:54:07](https://github.com/leanprover-community/mathlib/commit/249a015)
chore(ring_theory/coprime): split out imports into a new file so that `is_coprime` can be used earlier. ([#9403](https://github.com/leanprover-community/mathlib/pull/9403))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Use.20of.20is_coprime.20in.20rat.2Ebasic/near/254942750)

### [2021-10-01 15:54:06](https://github.com/leanprover-community/mathlib/commit/102ce30)
feat(linear_algebra/direct_sum): `submodule_is_internal_iff_independent_and_supr_eq_top` ([#9214](https://github.com/leanprover-community/mathlib/pull/9214))
This shows that a grade decomposition into submodules is bijective iff and only iff the submodules are independent and span the whole module.
The key proofs are:
* `complete_lattice.independent_of_dfinsupp_lsum_injective`
* `complete_lattice.independent.dfinsupp_lsum_injective`
Everything else is just glue.
This replaces parts of [#8246](https://github.com/leanprover-community/mathlib/pull/8246), and uses what is probably a similar proof strategy, but without unfolding down to finsets.
Unlike the proof there, this requires only `add_comm_monoid` for the `complete_lattice.independent_of_dfinsupp_lsum_injective` direction of the proof. I was not able to find a proof of `complete_lattice.independent.dfinsupp_lsum_injective` with the same weak assumptions, as it is not true! A counter-example is included,

### [2021-10-01 13:24:12](https://github.com/leanprover-community/mathlib/commit/9be12dd)
feat(order/locally_finite): introduce locally finite orders ([#9464](https://github.com/leanprover-community/mathlib/pull/9464))
The new typeclass `locally_finite_order` homogeneizes treatment of intervals as `finset`s and `multiset`s. `finset.Ico` is now available for all locally finite orders (instead of being ℕ-specialized), rendering `finset.Ico_ℤ` and `pnat.Ico` useless.
This PR also introduces the long-awaited `finset.Icc`, `finset.Ioc`, `finset.Ioo`, and `finset.Ici`, `finset.Ioi` (for `order_top`s) and `finset.Iic`, `finset.Iio` (for `order_bot`s), and the `multiset` variations thereof.

### [2021-10-01 13:24:10](https://github.com/leanprover-community/mathlib/commit/62b8c1f)
feat(order/basic): Antitone functions ([#9119](https://github.com/leanprover-community/mathlib/pull/9119))
Define `antitone` and `strict_anti`. Use them where they already were used in expanded form. Rename lemmas accordingly.
Provide a few more `order_dual` results, and rename `monotone.order_dual` to `monotone.dual`.
Restructure `order.basic`. Now, monotone stuff can easily be singled out to go in a new file `order.monotone` if wanted. It represents 587 out of the 965 lines.

### [2021-10-01 13:24:08](https://github.com/leanprover-community/mathlib/commit/d6bf2dd)
refactor(*): replace `abs` with vertical bar notation ([#8891](https://github.com/leanprover-community/mathlib/pull/8891))
The notion of an "absolute value" occurs both in algebra (e.g. lattice ordered groups) and analysis (e.g. GM and GL-spaces). I introduced a `has_abs` notation class in [#9172](https://github.com/leanprover-community/mathlib/pull/9172), along with the  conventional mathematical vertical bar notation `|.|` for `abs`.
The notation vertical bar notation was already in use in some files as a local notation. This PR replaces `abs` with the vertical bar notation throughout mathlib.

### [2021-10-01 12:27:23](https://github.com/leanprover-community/mathlib/commit/c33407a)
feat(algebraic_geometry/*): Proved Spec ⋙ Γ ≅ 𝟭 ([#9416](https://github.com/leanprover-community/mathlib/pull/9416))
- Specialied `algebraic_geometry.structure_sheaf.basic_open_iso` into global sections, proving that the map `structure_sheaf.to_open R ⊤` is an isomorphism in `algebraic_geometry.is_iso_to_global`.
- Proved that the map `R ⟶ Γ(Spec R)` is natural, and presents the fact above as an natural isomorphism `Spec.right_op ⋙ Γ ≅ 𝟭 _` in `algebraic_geometry.Spec_Γ_identity`.

### [2021-10-01 10:38:53](https://github.com/leanprover-community/mathlib/commit/38395ed)
chore(bors): bors should block on label awaiting-CI ([#9478](https://github.com/leanprover-community/mathlib/pull/9478))

### [2021-10-01 10:38:52](https://github.com/leanprover-community/mathlib/commit/5936f53)
feat(topology/maps): for a continuous open map, preimage and interior commute ([#9471](https://github.com/leanprover-community/mathlib/pull/9471))

### [2021-10-01 10:38:51](https://github.com/leanprover-community/mathlib/commit/265345c)
feat(linear_algebra/{bilinear,quadratic}_form): remove non-degeneracy requirement from `exists_orthogonal_basis` and Sylvester's law of inertia ([#9465](https://github.com/leanprover-community/mathlib/pull/9465))
This removes the `nondegenerate` hypothesis from `bilin_form.exists_orthogonal_basis`, and removes the `∀ i, B (v i) (v i) ≠ 0` statement from the goal. This property can be recovered in the case of a nondegenerate form with `is_Ortho.not_is_ortho_basis_self_of_nondegenerate`.
This also swaps the order of the binders in `is_Ortho` to make it expressible with `pairwise`.

### [2021-10-01 10:38:49](https://github.com/leanprover-community/mathlib/commit/74457cb)
feat(data/polynomial,field_theory): `(minpoly A x).map f ≠ 1` ([#9451](https://github.com/leanprover-community/mathlib/pull/9451))
We use this result to generalize `minpoly.not_is_unit` from integral domains to nontrivial `comm_ring`s.

### [2021-10-01 08:55:56](https://github.com/leanprover-community/mathlib/commit/f7d7a91)
feat(algebraic_geometry/ringed_space): Define basic opens for ringed spaces. ([#9358](https://github.com/leanprover-community/mathlib/pull/9358))
Defines the category of ringed spaces, as an alias for `SheafedSpace CommRing`. We provide basic lemmas about sections being units in the stalk and define basic opens in this context.

### [2021-10-01 08:55:55](https://github.com/leanprover-community/mathlib/commit/9235c8a)
feat(data/polynomial/basic): polynomial.update ([#9020](https://github.com/leanprover-community/mathlib/pull/9020))

### [2021-10-01 06:05:13](https://github.com/leanprover-community/mathlib/commit/e0f7d0e)
feat(group_theory/complement): is_complement_iff_card_mul_and_disjoint ([#9476](https://github.com/leanprover-community/mathlib/pull/9476))
Adds the converse to an existing lemma `is_complement_of_disjoint` (renamed `is_complement_of_card_mul_and_disjoint`).

### [2021-10-01 06:05:12](https://github.com/leanprover-community/mathlib/commit/57fa903)
refactor(group_theory/complement): Split `complement.lean` ([#9474](https://github.com/leanprover-community/mathlib/pull/9474))
Splits off Schur-Zassenhaus from `complement.lean`. In the new file, we can replace `fintype.card (quotient_group.quotient H)` with `H.index`.
Advantages: We can avoid importing `cardinal.lean` in `complement.lean`. Later (once full SZ is proved), we can avoid importing `sylow.lean` in `complement.lean`.

### [2021-10-01 06:05:11](https://github.com/leanprover-community/mathlib/commit/76ddb2b)
feat(analysis/normed_space/lattice_ordered_group): introduce normed lattice ordered groups ([#9274](https://github.com/leanprover-community/mathlib/pull/9274))
Motivated by Banach Lattices, this PR introduces normed lattice ordered groups and proves that they are topological lattices. To support this `has_continuous_inf` and `has_continuous_sup` mixin classes are also defined.

### [2021-10-01 03:25:37](https://github.com/leanprover-community/mathlib/commit/812d6bb)
chore(scripts): update nolints.txt ([#9475](https://github.com/leanprover-community/mathlib/pull/9475))
I am happy to remove some nolints for you!

### [2021-10-01 03:25:36](https://github.com/leanprover-community/mathlib/commit/125dac8)
feat(group_theory/sylow): The number of Sylow subgroups equals the index of the normalizer ([#9455](https://github.com/leanprover-community/mathlib/pull/9455))
This PR adds further consequences of Sylow's theorems (still for infinite groups, more will be PRed later).

### [2021-10-01 03:25:35](https://github.com/leanprover-community/mathlib/commit/b786443)
chore(algebra/category/*): Added `of_hom` to all of the algebraic categories. ([#9454](https://github.com/leanprover-community/mathlib/pull/9454))
As suggested in the comments of [#9416](https://github.com/leanprover-community/mathlib/pull/9416).

### [2021-10-01 03:25:34](https://github.com/leanprover-community/mathlib/commit/babca8e)
refactor(algebra/group_with_zero): rename lemmas to use ₀ instead of ' ([#9424](https://github.com/leanprover-community/mathlib/pull/9424))
We currently have lots of lemmas for `group_with_zero` that already have a corresponding lemma for `group`. We've dealt with name collisions so far just by adding a prime.
This PR renames these lemmas to use a `₀` suffix instead of a `'`.
In part this is out of desire to reduce our overuse of primes in mathlib names (putting the burden on users to know names, rather than relying on naming conventions).
But it may also help with a problem Daniel Selsam ran into at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mathport.20depending.20on.20mathlib. (Briefly, mathport is also adding primes to names when it encounters name collisions, and these particular primes were causing problems. There are are other potential fixes in the works, but everything helps.)

### [2021-10-01 01:14:03](https://github.com/leanprover-community/mathlib/commit/540fb94)
feat(data/fintype/basic): bijection preserves cardinality ([#9473](https://github.com/leanprover-community/mathlib/pull/9473))
We don't seem to have this lemma yet, so I've added it.

### [2021-10-01 01:14:02](https://github.com/leanprover-community/mathlib/commit/456db24)
feat(topology/algebra/module): has_continuous_smul ([#9468](https://github.com/leanprover-community/mathlib/pull/9468))
in terms of nice neighborhoods of zero

### [2021-10-01 01:14:00](https://github.com/leanprover-community/mathlib/commit/2b23d2e)
chore(topology/algebra): remove dead code ([#9467](https://github.com/leanprover-community/mathlib/pull/9467))
This code wasn't used and its historically intended use will soon be redone much better. The second file is only a dead import and a misleading comment (referring to the dead code of the *other* file).

### [2021-10-01 01:13:59](https://github.com/leanprover-community/mathlib/commit/5b02571)
chore(measure_theory/decomposition/lebesgue): make measurable_space implicit ([#9463](https://github.com/leanprover-community/mathlib/pull/9463))
Whenever the `measurable_space` can be inferred from a `measure` argument, it should be implicit. This PR applies that rule to the Lebesgue decomposition file.