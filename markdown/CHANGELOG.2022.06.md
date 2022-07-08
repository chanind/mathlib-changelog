### [2022-06-30 21:59:47](https://github.com/leanprover-community/mathlib/commit/9229b0e)
chore(data/nat/factorization/basic): delete `import tactic.linarith` ([#15075](https://github.com/leanprover-community/mathlib/pull/15075))
Removes the import of `tactic.linarith` that's no longer needed.

### [2022-06-30 21:59:46](https://github.com/leanprover-community/mathlib/commit/e7425e7)
feat(data/fin/basic): `induction_zero` and `induction_succ` lemmas ([#15060](https://github.com/leanprover-community/mathlib/pull/15060))
This pull request introduces `fin.induction_zero` and `fin.induction_succ` simp lemmas for `fin.induction`, similar to `fin.cases_zero` and `fin.cases_succ` for `fin.cases`.

### [2022-06-30 19:45:49](https://github.com/leanprover-community/mathlib/commit/806bbb0)
refactor(algebra/group/defs): rename has_scalar to has_smul ([#14559](https://github.com/leanprover-community/mathlib/pull/14559))
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy

### [2022-06-30 17:18:22](https://github.com/leanprover-community/mathlib/commit/c10efa6)
refactor(algebra/hom/group): generalize basic API of `monoid_hom` to `monoid_hom_class` ([#14997](https://github.com/leanprover-community/mathlib/pull/14997))
This PR generalizes part of the basic API of monoid homs to monoid_hom_class. This notably includes things like monoid_hom.mker, submonoid.map and submonoid.comap. I left the namespaces unchanged, for example `monoid_hom.mker` remains the same even though it is now defined for any `monoid_hom_class` morphism; this way dot notation still (mostly) works for actual monoid homs.

### [2022-06-30 12:40:15](https://github.com/leanprover-community/mathlib/commit/eb85260)
feat(topology/compact_open):  continuous_comp left functor C(-, γ) ([#15068](https://github.com/leanprover-community/mathlib/pull/15068))

### [2022-06-30 06:53:03](https://github.com/leanprover-community/mathlib/commit/050f9e6)
feat(number_theory/legendre_symbol/mul_character): alternative implementation ([#14768](https://github.com/leanprover-community/mathlib/pull/14768))
This is an alternative version of `number_theory/legendre_symbol/mul_character.lean`.
It defines `mul_character R R'` as a `monoid_hom` that sends non-units to zero.
This allows to define a `comm_group` structure on `mul_character R R'`.
There is an alternative implementation in [#14716](https://github.com/leanprover-community/mathlib/pull/14716) ([side by side comparison](https://github.com/leanprover-community/mathlib/compare/legendre_symbol_mul_char...variant)).
See the [discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Implementation.20of.20multiplicative.20characters).

### [2022-06-30 04:08:55](https://github.com/leanprover-community/mathlib/commit/ad154bd)
chore(scripts): update nolints.txt ([#15063](https://github.com/leanprover-community/mathlib/pull/15063))
I am happy to remove some nolints for you!

### [2022-06-29 23:58:49](https://github.com/leanprover-community/mathlib/commit/5d8810a)
feat(set_theory/cardinal/*): simp lemmas for `to_nat` and `to_enat` ([#15059](https://github.com/leanprover-community/mathlib/pull/15059))

### [2022-06-29 23:58:48](https://github.com/leanprover-community/mathlib/commit/68452ec)
feat(set_theory/game/pgame): golf `le_trans`  ([#14956](https://github.com/leanprover-community/mathlib/pull/14956))
This also adds `has_le.le.move_left_lf` and `has_le.le.lf_move_right` to enable dot notation. Note that we already have other pgame lemmas in the `has_le.le` namespace like `has_le.le.not_gf`.
To make this dot notation work even when these lemmas are partially-applied, we swap the arguments of `move_left_lf_of_le` and `lf_move_right_of_le`.

### [2022-06-29 22:22:06](https://github.com/leanprover-community/mathlib/commit/501c1d4)
feat(linear_algebra/linear_pmap): add has_smul and ext ([#14915](https://github.com/leanprover-community/mathlib/pull/14915))
Adds the type-class `has_smul` for partially defined linear maps. We proof the ext lemma.

### [2022-06-29 22:22:05](https://github.com/leanprover-community/mathlib/commit/a2a8c9b)
refactor(ring_theory/graded_algebra): use `add_submonoid_class` to generalize to graded rings ([#14583](https://github.com/leanprover-community/mathlib/pull/14583))
Now that we have `add_submonoid_class`, we don't need to consider only families of submodules.
For convenience, this keeps around `graded_algebra` as an alias for `graded_ring` over a family of submodules, as this can help with elaboration here and there.
This renames:
* `graded_algebra` to `graded_ring`
* `graded_algebra.proj_zero_ring_hom` to `graded_ring.proj_zero_ring_hom`
adds:
* `direct_sum.decompose_ring_equiv`
* `graded_ring.proj`
* `graded_algebra` (as an alias for a suitable `graded_ring`
and removes:
* `graded_algebra.is_internal`, which was just an alias anyway.

### [2022-06-29 20:39:00](https://github.com/leanprover-community/mathlib/commit/1116684)
chore(set_theory/game/pgame): golf various theorems about relabellings ([#15054](https://github.com/leanprover-community/mathlib/pull/15054))

### [2022-06-29 20:38:59](https://github.com/leanprover-community/mathlib/commit/108e3a0)
refactor(group_theory/coset): redefine quotient group to be quotient by action of subgroup ([#15045](https://github.com/leanprover-community/mathlib/pull/15045))
Given a group `α` and subgroup `s`, redefine the relation `left_rel` ("being in the same left coset") to
```lean
def left_rel : setoid α := mul_action.orbit_rel s.opposite α
```
This means that a quotient group is definitionally a quotient by a group action.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/two.20different.20quotients.20by.20subgroup)

### [2022-06-29 20:38:58](https://github.com/leanprover-community/mathlib/commit/71985dc)
feat(field_theory/minpoly): generalize statements about GCD domains ([#14979](https://github.com/leanprover-community/mathlib/pull/14979))
Currently, the statements about the minimal polynomial over a GCD domain `R` require the element to be in a `K`-algebra, where `K` is the fraction field of `R`. We remove this assumption.
From flt-regular.

### [2022-06-29 20:38:57](https://github.com/leanprover-community/mathlib/commit/6879dd0)
feat(model_theory/satisfiability): The Łoś–Vaught Test ([#14758](https://github.com/leanprover-community/mathlib/pull/14758))
Provides more API for elementary equivalence
Shows that a `κ`-categorical theory with only infinite models is complete.

### [2022-06-29 18:27:22](https://github.com/leanprover-community/mathlib/commit/397d45f)
feat(algebra/order/monoid): `a + b ≤ c → a ≤ c` ([#15033](https://github.com/leanprover-community/mathlib/pull/15033))
Generalize four lemmas that were left by previous PRs before `canonically_ordered_monoid` was a thing.

### [2022-06-29 18:27:20](https://github.com/leanprover-community/mathlib/commit/07726e2)
chore(analysis/locally_convex/balanced_core_hull): Golf ([#14987](https://github.com/leanprover-community/mathlib/pull/14987))
Golf and improve lemmas based on the naming convention:
* `balanced_mem` → `balanced_iff_smul_mem`
* `zero_singleton_balanced` → `balanced_zero`
* `balanced_core_emptyset` → `balanced_core_empty`
* `balanced_core_mem_iff` → `mem_balanced_core_iff`
* `balanced_hull_mem_iff` → `mem_balanced_hull_iff`
* `balanced_core_is_closed` → `is_closed.balanced_core`

### [2022-06-29 18:27:19](https://github.com/leanprover-community/mathlib/commit/478773b)
chore(data/nat/factorization/basic): golf rec_on_pos_prime_pos_coprime, remove import ([#14935](https://github.com/leanprover-community/mathlib/pull/14935))
Golf the proof of `rec_on_pos_prime_pos_coprime`, eliminating the need for `tactic.interval_cases`

### [2022-06-29 17:31:54](https://github.com/leanprover-community/mathlib/commit/ee8d588)
refactor(logic/hydra): use `is_irrefl` ([#15039](https://github.com/leanprover-community/mathlib/pull/15039))
`is_irrefl` seems to be the more commonly used spelling

### [2022-06-29 14:27:11](https://github.com/leanprover-community/mathlib/commit/c8ab806)
feat(tactic/alias.lean): use current namespace in alias ([#14961](https://github.com/leanprover-community/mathlib/pull/14961))
This makes `alias foo <- bar` use the current namespace to resolve the new alias name `bar`, for consistency with `def bar := foo` and leanprover-community/mathlib4[#293](https://github.com/leanprover-community/mathlib/pull/293).

### [2022-06-29 14:27:10](https://github.com/leanprover-community/mathlib/commit/5de765c)
feat(linear_algebra/linear_pmap): definition of the graph ([#14920](https://github.com/leanprover-community/mathlib/pull/14920))
Define the graph of a partial linear map as the pushforward of the graph of the underlying linear map
and prove some elementary facts.

### [2022-06-29 12:27:59](https://github.com/leanprover-community/mathlib/commit/aa812bd)
chore(group_theory/group_action/basic): split file ([#15044](https://github.com/leanprover-community/mathlib/pull/15044))
Split the file `group_theory/group_action/basic` to remove the dependency on `group_theory/quotient_group`, moving everything involving quotients to a new file `group_theory/group_action/quotient`.

### [2022-06-29 10:03:54](https://github.com/leanprover-community/mathlib/commit/ea9dae2)
refactor(topology/*): Use `disjoint` ([#14950](https://github.com/leanprover-community/mathlib/pull/14950))
Replace uses of `s ∩ t = ∅` by `disjoint s t` in the topology library. This shortens proofs.

### [2022-06-29 08:02:38](https://github.com/leanprover-community/mathlib/commit/03374ee)
feat(algebra/order/field): Linearly ordered semifields ([#15027](https://github.com/leanprover-community/mathlib/pull/15027))
Define `linear_ordered_semifield` and generalize lemmas within `algebra.order.field`.

### [2022-06-29 02:12:43](https://github.com/leanprover-community/mathlib/commit/55ec65a)
feat(topology/algebra/module/basic): define continuous_(semi)linear_map_class ([#14674](https://github.com/leanprover-community/mathlib/pull/14674))
This PR brings the morphism refactor to continuous (semi)linear maps. We define `continuous_semilinear_map_class` and `continuous_linear_map_class` in a way that parallels the non-continuous versions, along with a few extras (i.e. `add_monoid_hom_class` instance for `normed_group_hom`).
A few things I was not too sure about:
- When generalizing lemmas to a morphism class rather than a particular type of morphism, I used `𝓕` as the type (instead of just `F` as is done for most `fun_like` types) to avoid clashing with our convention of using `E`, `F`, etc for e.g. vector spaces.
- Namespacing: I placed lemmas like `isometry_of_norm`, `continuous_of_bound`, etc, under the `add_monoid_hom_class` namespace. Maybe the root namespace would make sense here.

### [2022-06-28 19:09:05](https://github.com/leanprover-community/mathlib/commit/08b07a6)
feat(order/succ_pred/basic): tag more lemmas with simp  ([#14998](https://github.com/leanprover-community/mathlib/pull/14998))

### [2022-06-28 19:09:03](https://github.com/leanprover-community/mathlib/commit/7db7667)
feat(order/boolean_algebra): Interaction of disjointness and complements ([#14925](https://github.com/leanprover-community/mathlib/pull/14925))
Prove `disjoint x yᶜ ↔ x ≤ y` and similar, transfer those results to `set`.
Lemma renames
* `subset_compl_iff_disjoint` → `subset_compl_iff_disjoint_right`
* `set.subset_compl_iff_disjoint` → `set.subset_compl_iff_disjoint_right`
* `disjoint_iff_le_compl_left` → `le_compl_iff_disjoint_left`
* `disjoint_iff_le_compl_right` → `le_compl_iff_disjoint_right`

### [2022-06-28 15:21:02](https://github.com/leanprover-community/mathlib/commit/00c17d6)
feat(algebra/ring/boolean_ring): `bool` is a Boolean ring ([#15004](https://github.com/leanprover-community/mathlib/pull/15004))
and a few `bool` lemmas.

### [2022-06-28 12:51:25](https://github.com/leanprover-community/mathlib/commit/78bc372)
feat(data/{finset, set}/basic): tweak `nonempty_coe_sort` and `is_empty_coe_sort` ([#14937](https://github.com/leanprover-community/mathlib/pull/14937))
This PR does the following:
- add lemmas `set.is_empty_coe_sort` and `finset.is_empty_coe_sort`
- made argument of both `nonempty_coe_sort` lemmas inferred
- fix some spacing

### [2022-06-28 09:03:25](https://github.com/leanprover-community/mathlib/commit/3594b63)
feat(probability_theory/independence): if a family of pi-systems is independent, then so are the generated measurable spaces ([#9387](https://github.com/leanprover-community/mathlib/pull/9387))
The main result in this PR is `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent. We already had a version of this for two pi-systems instead of a family.
In order to prove this, and as preparation for a next PR about Kolmogorov's 0-1 law, a definition `pi_Union_Inter` is introduced to build a particular pi-system from a family of pi-systems.

### [2022-06-28 08:13:29](https://github.com/leanprover-community/mathlib/commit/728e074)
feat(measure_theory/function/lp_order): prove a `normed_lattice_add_comm_group` instance for Lp ([#14999](https://github.com/leanprover-community/mathlib/pull/14999))

### [2022-06-28 03:59:01](https://github.com/leanprover-community/mathlib/commit/dcedc04)
feat(order/symm_diff): Triangle inequality for the symmetric difference ([#14847](https://github.com/leanprover-community/mathlib/pull/14847))
Prove that `a ∆ c ≤ a ∆ b ⊔ b ∆ c`.

### [2022-06-28 02:30:01](https://github.com/leanprover-community/mathlib/commit/ae3d572)
chore(topology/uniform_space/basic): Make `to_topological_space_inf` and `inf_uniformity` true by definition ([#14912](https://github.com/leanprover-community/mathlib/pull/14912))
Since the lattice API lets us provide a definition for `inf`, we may as well provide a nice one such that the obvious properties are true by rfl.

### [2022-06-28 00:05:04](https://github.com/leanprover-community/mathlib/commit/cf4d987)
chore(analysis/special_functions/trigonometric/angle): rfl lemmas for nat and int smul actions on angle ([#15003](https://github.com/leanprover-community/mathlib/pull/15003))
These can't be simp, because the simp-normal form is multiplication.

### [2022-06-28 00:05:02](https://github.com/leanprover-community/mathlib/commit/37bf8a2)
chore(topology/separation): Extract `set` product lemma ([#14958](https://github.com/leanprover-community/mathlib/pull/14958))
Move `prod_subset_compl_diagonal_iff_disjoint` to `data.set.prod`, where it belongs. Delete `diagonal_eq_range_diagonal_map` because it duplicates `set.diagonal_eq_range`. Move `set.disjoint_left`/`set.disjoint_right` to `data.set.basic` to avoid an import cycle.
Make variable semi-implicit in the RHS of `disjoint_left` and `disjoint_right`.

### [2022-06-28 00:05:01](https://github.com/leanprover-community/mathlib/commit/ee7f38c)
chore(data/set/basic): remove duplicate `nonempty_insert` in favor of `insert_nonempty` ([#14884](https://github.com/leanprover-community/mathlib/pull/14884))
This name matches e.g. `univ_nonempty` and `singleton_nonempty`.

### [2022-06-28 00:04:54](https://github.com/leanprover-community/mathlib/commit/365b2ee)
feat(data/bool): bnot_ne ([#10562](https://github.com/leanprover-community/mathlib/pull/10562))

### [2022-06-27 21:32:09](https://github.com/leanprover-community/mathlib/commit/f6b728f)
feat(data/finset/pointwise): `•` and `⊆` ([#14968](https://github.com/leanprover-community/mathlib/pull/14968))
Port `set` lemmas to `finset`. Tag a few more lemmas with `norm_cast`. Add some missing `to_additive` attributes.

### [2022-06-27 21:32:08](https://github.com/leanprover-community/mathlib/commit/7c6cd38)
chore(set_theory/game/pgame): remove weird `simp` lemma ([#14954](https://github.com/leanprover-community/mathlib/pull/14954))
I added this back before there was much API on casting natural numbers to pre-games, as a safeguard in case I used the wrong `1`. In retrospective this theorem was kind of dumb.

### [2022-06-27 21:32:07](https://github.com/leanprover-community/mathlib/commit/2cdded9)
feat(data/multiset/basic): add multiset.filter_singleton ([#14938](https://github.com/leanprover-community/mathlib/pull/14938))
Adds a lemma, similar to `finset.filter_singleton`.

### [2022-06-27 21:32:05](https://github.com/leanprover-community/mathlib/commit/927b468)
chore(data/nat/factorization/basic): golf pow_succ_factorization_not_dvd, remove import ([#14936](https://github.com/leanprover-community/mathlib/pull/14936))
Move `pow_succ_factorization_not_dvd` below `factorization_le_iff_dvd` and use this to golf it, eliminating the need for `tactic.linarith`

### [2022-06-27 21:32:04](https://github.com/leanprover-community/mathlib/commit/f51286d)
feat(analysis/locally_convex/bounded): continuous linear image of bounded set is bounded ([#14907](https://github.com/leanprover-community/mathlib/pull/14907))
This is needed to prove that the usual strong topology on continuous linear maps satisfies `has_continuous_smul`.

### [2022-06-27 21:32:03](https://github.com/leanprover-community/mathlib/commit/cf50ac1)
chore(algebra/group/units): mark some lemmas as simp ([#14871](https://github.com/leanprover-community/mathlib/pull/14871))
These seem like fairly natural candidates for simp lemmas.

### [2022-06-27 21:32:02](https://github.com/leanprover-community/mathlib/commit/cad1a6c)
feat(set_theory/cardinal/basic): lemmas about `#(finset α)` ([#14850](https://github.com/leanprover-community/mathlib/pull/14850))
This PR does the following:
- prove `mk_finset_of_fintype : #(finset α) = 2 ^ℕ fintype.card α` for `fintype α`
- rename `mk_finset_eq_mk` to `mk_finset_of_infinite` to match the former
- rename `mk_finset` to `mk_coe_finset` to avoid confusion with these two lemmas

### [2022-06-27 21:32:00](https://github.com/leanprover-community/mathlib/commit/fef4fb8)
refactor(topology/inseparable): redefine `specializes` and `inseparable` ([#14647](https://github.com/leanprover-community/mathlib/pull/14647))
* Redefine `specializes` and `inseparable` in terms of `nhds`.
* Review API.
* Define `inseparable_setoid` and `separation_quotient`.
* Add `function.surjective.subsingleton`.

### [2022-06-27 19:03:59](https://github.com/leanprover-community/mathlib/commit/1cd2bf5)
feat(analysis/special_functions/log/deriv): more power series for log ([#14881](https://github.com/leanprover-community/mathlib/pull/14881))
This adds a power series expansion for `log ((a + 1) / a)`, and two lemmas that are needed for it. It's planned to be used in the proof of the Stirling formula.

### [2022-06-27 16:25:12](https://github.com/leanprover-community/mathlib/commit/68e0160)
chore(data/int/cast): redo [#14890](https://github.com/leanprover-community/mathlib/pull/14890), moving field-specific lemmas ([#14995](https://github.com/leanprover-community/mathlib/pull/14995))
In [#14894](https://github.com/leanprover-community/mathlib/pull/14894), I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.defs`.
Apparently this dependency was re-added, so I'm going to have to split it again...

### [2022-06-27 16:25:11](https://github.com/leanprover-community/mathlib/commit/2558b3b)
feat(*): Upgrade to lean 3.44.1c ([#14984](https://github.com/leanprover-community/mathlib/pull/14984))
The changes are:
* `reflected a` is now spelt `reflected _ a`, as the argument was made explicit to resolve type resolution issues. We need to add new instances for `with_top` and `with_bot` as these are no longer found via the `option` instance. These new instances are an improvement, as they can now use `bot` and `top` instead of `none`.
* Some nat order lemmas in core have been renamed or had their argument explicitness adjusted.
* `dsimp` now applies `iff` lemmas, which means it can end up making more progress than it used to. This appears to impact `split_ifs` too.
* `opposite.op_inj_iff` shouldn't be proved until after `opposite` is irreducible (where `iff.rfl` no longer works as a proof), otherwise `dsimp` is tricked into unfolding the irreducibility which puts the goal state in a form where no further lemmas can apply.
We skip Lean 3.44.0c because the support in that version for `iff` lemmas in `dsimp` had some unintended consequences which required many undesirable changes.

### [2022-06-27 13:50:22](https://github.com/leanprover-community/mathlib/commit/05565f4)
doc(analysis/convex/uniform_convex_space): End of sentence ([#14986](https://github.com/leanprover-community/mathlib/pull/14986))
I kept the suspense for a month.

### [2022-06-27 13:50:15](https://github.com/leanprover-community/mathlib/commit/5de7c34)
feat(order/*): Miscellaneous results about the product order ([#14977](https://github.com/leanprover-community/mathlib/pull/14977))
`≤`, `<`, `⩿`, `⋖`, `is_bot`, `is_top`, `is_min`, `is_max` in `α × β`.

### [2022-06-27 13:50:14](https://github.com/leanprover-community/mathlib/commit/f5d2cc8)
feat(measure_theory/function/l1_space): add some integrability lemmas ([#14931](https://github.com/leanprover-community/mathlib/pull/14931))

### [2022-06-27 13:50:13](https://github.com/leanprover-community/mathlib/commit/cf8b46d)
feat(analysis/convex/special_functions): `sqrt * log` is strictly convex on x>1 ([#14822](https://github.com/leanprover-community/mathlib/pull/14822))
This convexity result can be used to golf the proof of the main inequality in the proof of Bertrand's postulate ([#8002](https://github.com/leanprover-community/mathlib/pull/8002)).

### [2022-06-27 13:50:12](https://github.com/leanprover-community/mathlib/commit/68d29f5)
feat(probability/stopping): measurability of sets related to stopping times, under countable/encodable assumptions ([#14750](https://github.com/leanprover-community/mathlib/pull/14750))
The file already contains similar lemmas under assumptions on the topology of the index set. The new results use countability hypotheses instead.

### [2022-06-27 11:38:35](https://github.com/leanprover-community/mathlib/commit/331df5a)
feat(probability/moments): moments and moment generating function of a real random variable ([#14755](https://github.com/leanprover-community/mathlib/pull/14755))
This PR defines moments, central moments, moment generating function and cumulant generating function.

### [2022-06-27 11:38:34](https://github.com/leanprover-community/mathlib/commit/3091b91)
feat(probability/stopping): if a filtration is sigma finite, then the measure restricted to the sigma algebra generated by a stopping time is sigma finite ([#14752](https://github.com/leanprover-community/mathlib/pull/14752))

### [2022-06-27 11:38:33](https://github.com/leanprover-community/mathlib/commit/72fbe5c)
feat(measure_theory/measure/finite_measure_weak_convergence): Characterize weak convergence of finite measures in terms of integrals of bounded continuous real-valued functions. ([#14578](https://github.com/leanprover-community/mathlib/pull/14578))
Weak convergence of measures was defined in terms of integrals of bounded continuous nnreal-valued functions. This PR shows the equivalence to the textbook condition in terms of integrals of bounded continuous real-valued functions.
Also the file `measure_theory/measure/finite_measure_weak_convergence.lean` is divided to sections with dosctrings for clarity.

### [2022-06-27 09:14:45](https://github.com/leanprover-community/mathlib/commit/cf0649c)
chore(data/sigma/basic): make `sigma.reflect` universe-polymorphic ([#14934](https://github.com/leanprover-community/mathlib/pull/14934))

### [2022-06-27 07:39:57](https://github.com/leanprover-community/mathlib/commit/671c7c0)
chore(algebra/direct_sum/ring): add new `int_cast` and `nat_cast` fields to match `ring` and `semiring` ([#14976](https://github.com/leanprover-community/mathlib/pull/14976))
This was deliberately left to a follow up in [#12182](https://github.com/leanprover-community/mathlib/pull/12182)

### [2022-06-27 07:39:56](https://github.com/leanprover-community/mathlib/commit/af8ca85)
fix(linear_algebra/{exterior,clifford}_algebra/basic): add some missing namespaces ([#14975](https://github.com/leanprover-community/mathlib/pull/14975))
These lemmas are about the auxiliary `{exterior,clifford}_algebra.graded_algebra.ι` not `{exterior,clifford}_algebra.ι`, so should have `graded_algebra` in their names.
This is a follow up to [#12182](https://github.com/leanprover-community/mathlib/pull/12182)

### [2022-06-27 04:03:50](https://github.com/leanprover-community/mathlib/commit/d4f8a45)
feat(algebra/group/units): add decidability instance for `is_unit` ([#14873](https://github.com/leanprover-community/mathlib/pull/14873))
This adds a decidability instance for the `is_unit` predicate. See [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Decidability.20of.20.60is_unit.60.20on.20finite.20rings/near/286543269).

### [2022-06-27 03:03:23](https://github.com/leanprover-community/mathlib/commit/0b18823)
feat(set_theory/game/pgame): make `lt_iff_le_and_lf` true by def-eq ([#14983](https://github.com/leanprover-community/mathlib/pull/14983))

### [2022-06-27 00:09:16](https://github.com/leanprover-community/mathlib/commit/894f92b)
refactor(order/upper_lower): Reverse the order on `upper_set` ([#14982](https://github.com/leanprover-community/mathlib/pull/14982))
Having `upper_set` being ordered by reverse inclusion makes it order-isomorphic to `lower_set` (and antichains once we have them as a type) and it matches the order on `filter`.

### [2022-06-26 23:29:19](https://github.com/leanprover-community/mathlib/commit/f63d925)
feat(combinatorics/simple_graph/clique): The set of cliques ([#14827](https://github.com/leanprover-community/mathlib/pull/14827))
Define `simple_graph.clique_set`, the `set` analogue to `simple_graph.clique_finset`.

### [2022-06-26 21:36:44](https://github.com/leanprover-community/mathlib/commit/f2b108e)
refactor(set_theory/cardinal/*): `cardinal.sup` → `supr` ([#14569](https://github.com/leanprover-community/mathlib/pull/14569))
We remove `cardinal.sup` in favor of `supr`. We tweak many other theorems relating to cardinal suprema in the process.
A noteworthy consequence is that there's no longer universe constraints on the domain and codomain of the functions one takes the supremum of. When one does still have this constraint, one can use `bdd_above_range` to immediately prove their range is bounded above.
<!-- Lemmas `lift_sup_le`, `lift_sup_le_iff`, `lift_sup_le_lift_sup`, and `lift_sup_le_lift_sup'` have been removed by virtue of being trivial consequences of basic lemmas on suprema and `lift_supr`. -->
The result of this PR is the following replacements:
* `cardinal.sup` → `supr`
* `cardinal.le_sup` → `le_csupr`
* `cardinal.sup_le` → `csupr_le'`
* `cardinal.sup_le_sup` → `csupr_mono`
* `cardinal.sup_le_sum` → `cardinal.supr_le_sum`
* `cardinal.sum_le_sup` → `cardinal.sum_le_supr`
* `cardinal.sum_le_sup_lift` → `cardinal.sum_le_supr_lift`
* `cardinal.sup_eq_zero` → `cardinal.supr_of_empty`
* `cardinal.le_sup_iff` → `le_csupr_iff'`
* `cardinal.lift_sup` → `cardinal.lift_supr`
* `cardinal.lift_sup_le` → `cardinal.lift_supr` + `csupr_le'`
* `cardinal.lift_sup_le_iff` → `cardinal.lift_supr` + `csupr_le_iff`
* `cardinal.lift_sup_le_lift_sup` → `cardinal.lift_supr` + `csupr_le_iff'`
* `cardinal.lift_sup_le_lift_sup'` → `cardinal.lift_supr` + `csupr_mono'`
* `cardinal.sup_lt_lift` → `cardinal.supr_lt_lift`
* `cardinal.sup_lt` → `cardinal.supr_lt`

### [2022-06-26 19:48:44](https://github.com/leanprover-community/mathlib/commit/33112c4)
feat(data/nat/totient): more general multiplicativity lemmas for totient ([#14842](https://github.com/leanprover-community/mathlib/pull/14842))
Adds lemmas: 
`totient_gcd_mul_totient_mul : φ (a.gcd b) * φ (a * b) = φ a * φ b * (a.gcd b)`
`totient_super_multiplicative : φ a * φ b ≤ φ (a * b)`
`totient_gcd_mul_totient_mul` is Theorem 2.5(b) in Apostol (1976) Introduction to Analytic Number Theory.
Developed while reviewing @CBirkbeck 's [#14828](https://github.com/leanprover-community/mathlib/pull/14828)

### [2022-06-26 18:50:48](https://github.com/leanprover-community/mathlib/commit/381733a)
feat(analysis/convex/stone_separation): Stone's separation theorem ([#14677](https://github.com/leanprover-community/mathlib/pull/14677))
Disjoint convexes can be separated by a convex whose complement is also convex.

### [2022-06-26 17:01:08](https://github.com/leanprover-community/mathlib/commit/4111ed9)
docs(linear_algebra/invariant_basis_number): Drop a TODO ([#14973](https://github.com/leanprover-community/mathlib/pull/14973))
This TODO was fixed some time ago by @riccardobrasca, reference the relevant instance in the docstring.

### [2022-06-26 17:01:07](https://github.com/leanprover-community/mathlib/commit/ca070dd)
feat(analysis/special_functions/trigonometric/angle): topology ([#14969](https://github.com/leanprover-community/mathlib/pull/14969))
Give `real.angle` the structure of a `topological_add_group` (rather
than just an `add_comm_group`), so that it's possible to talk about
continuity for functions involving this type, and add associated
continuity lemmas for `coe : ℝ → angle`, `real.angle.sin` and
`real.angle.cos`.

### [2022-06-26 17:01:06](https://github.com/leanprover-community/mathlib/commit/28a6f0a)
feat(set_theory/surreal/basic): add `numeric.mk` lemma, golf ([#14962](https://github.com/leanprover-community/mathlib/pull/14962))

### [2022-06-26 17:01:05](https://github.com/leanprover-community/mathlib/commit/54352be)
feat(combinatorics/catalan): definition and equality of recursive and explicit definition ([#14869](https://github.com/leanprover-community/mathlib/pull/14869))
This PR defines the Catalan numbers via the recursive definition $$C (n+1) = \sum_{i=0}^n C (i) * C (n-i)$$. 
Furthermore, it shows that $$ n+1 | \binom {2n}{n}$$ and that the alternative $$C(n)=\frac{1}{n+1} \binom{2n}{n}$$ holds. 
The proof is based on the following stackexchange answer: https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation which is quite elementary, so that the proof is relatively easy to formalise.

### [2022-06-26 14:56:15](https://github.com/leanprover-community/mathlib/commit/ee7a886)
feat({data/{finset,set},order/filter}/pointwise): Missing `smul_comm_class` instances ([#14963](https://github.com/leanprover-community/mathlib/pull/14963))
Instances of the form `smul_comm_class α β (something γ)`.

### [2022-06-26 12:02:17](https://github.com/leanprover-community/mathlib/commit/32b08ef)
feat: `add_monoid_with_one`, `add_group_with_one` ([#12182](https://github.com/leanprover-community/mathlib/pull/12182))
Adds two type classes `add_monoid_with_one R` and `add_group_with_one R` with operations for `ℕ → R` and `ℤ → R`, resp.  The type classes extend `add_monoid` and `add_group` because those seem to be the weakest type classes where such a `+₀₁`-homomorphism is guaranteed to exist.  The `nat.cast` function as well as `coe : ℕ → R` are implemented in terms of `add_monoid_with_one R`, removing the infamous `nat.cast` diamond.  Fixes [#946](https://github.com/leanprover-community/mathlib/pull/946).
Some lemmas are less general now because the algebraic hierarchy is not fine-grained enough, or because the lawful coercion only exists for monoids and above.  This generality was not used in mathlib as far as I could tell.  For example:
 - `char_p.char_p_to_char_zero` now requires a group instead of a left-cancellative monoid, because we don't have the `add_left_cancel_monoid_with_one` class
 - `nat.norm_cast_le` now requires a seminormed ring instead of a seminormed group, because we don't have `semi_normed_group_with_one`

### [2022-06-26 08:42:14](https://github.com/leanprover-community/mathlib/commit/871fcd8)
feat(data/zmod/algebra): add subsingleton instance for zmod-algebras ([#14946](https://github.com/leanprover-community/mathlib/pull/14946))
This will be used to eliminate a diamond with `galois_field.algebra` in a followup PR.

### [2022-06-26 08:01:37](https://github.com/leanprover-community/mathlib/commit/e0ecaa9)
feat(set_theory/ordinal/notation): fast growing hierarchy ([#14072](https://github.com/leanprover-community/mathlib/pull/14072))
Adds a definition `onote.fast_growing` which yields elements of the [fast-growing hierarchy](https://en.wikipedia.org/wiki/Fast-growing_hierarchy) up to and including ε₀. Because it is built on `onote` instead of `ordinal`, the definition is fully computable, and you can work out some small elements. For example `fast_growing_ε₀ 2 = 2048` and `fast_growing_ε₀ 3` is... big.

### [2022-06-26 04:37:04](https://github.com/leanprover-community/mathlib/commit/cfbb97f)
feat(data/{finset,set}/basic): More `∪`/`∩` laws ([#14952](https://github.com/leanprover-community/mathlib/pull/14952))
Specialise lattice lemmas to `set` and `finset`.

### [2022-06-26 04:37:03](https://github.com/leanprover-community/mathlib/commit/ccb1cf3)
feat(data/set/lattice): Preimages are disjoint iff the sets are disjoint ([#14951](https://github.com/leanprover-community/mathlib/pull/14951))
Prove `disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ disjoint s t` and `disjoint (f '' s) (f '' t) ↔ disjoint s t` when `f` is surjective/injective. Delete `set.disjoint_preimage` in favor of `disjoint.preimage`. Fix the statement of `set.preimage_eq_empty_iff` (the name referred to the RHS).

### [2022-06-26 03:02:54](https://github.com/leanprover-community/mathlib/commit/72cff84)
feat(order/symm_diff): The symmetric difference is involutive ([#14959](https://github.com/leanprover-community/mathlib/pull/14959))
`a ∆ (a ∆ b) = b` and `b ∆ a ∆ a = b`.

### [2022-06-26 00:12:23](https://github.com/leanprover-community/mathlib/commit/b8c3e61)
refactor(*): Use `finset.Iix`/`finset.Ixi` ([#14448](https://github.com/leanprover-community/mathlib/pull/14448))
Now that `finset.Iix`/`finset.Ixi` work for empty types, there is no need for `univ.filter (λ j, j < i)` and similar.

### [2022-06-25 21:12:47](https://github.com/leanprover-community/mathlib/commit/7ee73e4)
feat(data/fintype/basic): Constructing an equivalence from a left inverse ([#14816](https://github.com/leanprover-community/mathlib/pull/14816))
When `f : α → β`, `g : β → α` are inverses one way and `card α ≤ card β`, then they form an equivalence.

### [2022-06-25 21:12:46](https://github.com/leanprover-community/mathlib/commit/8812752)
feat(algebra/field/basic): Semifields ([#14683](https://github.com/leanprover-community/mathlib/pull/14683))
Define division semirings and semifields.

### [2022-06-25 20:02:11](https://github.com/leanprover-community/mathlib/commit/f9571f0)
feat(analysis/normed*): add instances about balls and spheres ([#14808](https://github.com/leanprover-community/mathlib/pull/14808))
Non-bc change: `has_inv.inv` on the unit circle is now defined using `has_inv.inv` instead of complex conjugation.

### [2022-06-25 13:57:10](https://github.com/leanprover-community/mathlib/commit/6f923bd)
chore(*): golf ([#14939](https://github.com/leanprover-community/mathlib/pull/14939))
Some golfs I made while working on a large refactor.

### [2022-06-25 07:57:38](https://github.com/leanprover-community/mathlib/commit/07c83c8)
feat(linear_algebra/clifford_algebra/of_alternating): extend alternating maps to the exterior algebra ([#14803](https://github.com/leanprover-community/mathlib/pull/14803))

### [2022-06-24 21:45:08](https://github.com/leanprover-community/mathlib/commit/4fd263b)
feat(representation_theory/character): characters of representations ([#14453](https://github.com/leanprover-community/mathlib/pull/14453))

### [2022-06-24 19:24:10](https://github.com/leanprover-community/mathlib/commit/8bf85d7)
feat(algebra/indicator_function): add an apply version of `mul_indicator_finset_bUnion` ([#14919](https://github.com/leanprover-community/mathlib/pull/14919))

### [2022-06-24 19:24:09](https://github.com/leanprover-community/mathlib/commit/f94a64f)
feat(probability/martingale): add some lemmas for submartingales ([#14904](https://github.com/leanprover-community/mathlib/pull/14904))

### [2022-06-24 19:24:08](https://github.com/leanprover-community/mathlib/commit/40fa2d8)
feat(topology/metric_space): a countably generated uniformity is metrizable ([#14052](https://github.com/leanprover-community/mathlib/pull/14052))

### [2022-06-24 17:15:45](https://github.com/leanprover-community/mathlib/commit/fe322e1)
refactor(algebra/order/monoid): use typeclasses instead of lemmas ([#14848](https://github.com/leanprover-community/mathlib/pull/14848))
Use `covariant_class`/`contravariant_class` instead of type-specific `mul_le_mul_left` etc lemmas. Also, rewrite some proofs to use API about inequalities on `with_top`/`with_bot` instead of the exact form of the current definition.

### [2022-06-24 15:26:20](https://github.com/leanprover-community/mathlib/commit/0e5f278)
feat(linear_algebra/{multilinear, alternating}): add `cod_restrict` and lemmas ([#14927](https://github.com/leanprover-community/mathlib/pull/14927))

### [2022-06-24 15:26:19](https://github.com/leanprover-community/mathlib/commit/3e326fc)
feat(data/finite/basic): add missing instances ([#14913](https://github.com/leanprover-community/mathlib/pull/14913))
* Add `finite` instances for `prod`, `pprod`, `sigma`, and `psigma`.
* Don't depend on `classical.choice` in `finite_iff_nonempty_fintype`.
* Move `not_finite_iff_infinite` up, use it to golf some proofs.

### [2022-06-24 15:26:17](https://github.com/leanprover-community/mathlib/commit/363bbd2)
chore(topology/basic): golf a proof ([#14911](https://github.com/leanprover-community/mathlib/pull/14911))

### [2022-06-24 15:26:16](https://github.com/leanprover-community/mathlib/commit/475cf37)
refactor(data/polynomial): extract/add lemmas and golf ([#14888](https://github.com/leanprover-community/mathlib/pull/14888))
+ Extract lemmas `roots_multiset_prod_X_sub_C`, `nat_degree_multiset_prod_X_sub_C_eq_card`, `monic_prod_multiset_X_sub_C` from the proof of `C_leading_coeff_mul_prod_multiset_X_sub_C` in *ring_division.lean*.
+ Add the lemma `exists_prod_multiset_X_sub_C_mul` in *ring_division.lean* and `roots_ne_zero_of_splits` in *splitting_field.lean* and use them to golf `nat_degree_eq_card_roots` The proof of the latter originally depends on `eq_prod_roots_of_splits`, but now the dependency reversed, with `nat_degree_eq_card_roots` now used to golf `eq_prod_roots_of_splits` (and `roots_map` as well).
+ Move `prod_multiset_root_eq_finset_root` and `prod_multiset_X_sub_C_dvd` from *field_division.lean* to *ring_division.lean* and golf the proof of the latter, generalizing `field` to `is_domain`.
+ Remove redundant imports and the lemma `exists_multiset_of_splits`, because it is just one direction of `splits_iff_exists_multiset`, and it follows trivially from `eq_prod_roots_of_splits`. It couldn't be removed before this PR because `roots_map` and `eq_prod_roots_of_splits` depended on it.
+ Golf `splits_of_exists_multiset` (independent of other changes).

### [2022-06-24 15:26:15](https://github.com/leanprover-community/mathlib/commit/dabb0c6)
feat(probability/independence): equivalent ways to check indep_fun ([#14814](https://github.com/leanprover-community/mathlib/pull/14814))
Prove:
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)`,
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → indep_set (f ⁻¹' s) (g ⁻¹' t) μ`.

### [2022-06-24 15:26:14](https://github.com/leanprover-community/mathlib/commit/7c2ad75)
feat(field_theory.intermediate_field):  intermediate_field.inclusion ([#12596](https://github.com/leanprover-community/mathlib/pull/12596))

### [2022-06-24 13:23:16](https://github.com/leanprover-community/mathlib/commit/e420232)
feat(data/int/basic): add a better `has_reflect int` instance ([#14906](https://github.com/leanprover-community/mathlib/pull/14906))
This closes a todo comment in `number_theory.lucas_lehmer`.
This also merges `rat.has_reflect` with `rat.reflect` to match `nat.reflect`.

### [2022-06-24 13:23:15](https://github.com/leanprover-community/mathlib/commit/f05c49f)
feat(meta/univs): Add a reflect_name tactic, make reflected instances universe polymorphic ([#14766](https://github.com/leanprover-community/mathlib/pull/14766))
The existing `list.reflect` instance only works for `Type 0`, this version works for `Type u` providing `u` is known.

### [2022-06-24 11:15:40](https://github.com/leanprover-community/mathlib/commit/8187142)
feat(data/finset/pointwise): `s • t` is the union of the `a • t` ([#14696](https://github.com/leanprover-community/mathlib/pull/14696))
and a few other results leading to it. Also tag `set.coe_bUnion` with `norm_cast` and rename `finset.image_mul_prod`/`finset.add_image_prod` to `finset.image_mul_product`/`finset.image_add_product`

### [2022-06-24 11:15:39](https://github.com/leanprover-community/mathlib/commit/6d00cc2)
feat(ring_theory/trace): Add `trace_eq_sum_automorphisms`, `norm_eq_prod_automorphisms`, `normal.alg_hom_equiv_aut` ([#14523](https://github.com/leanprover-community/mathlib/pull/14523))

### [2022-06-24 09:56:29](https://github.com/leanprover-community/mathlib/commit/efe794c)
chore(order/filter): turn `tendsto_id'` into an `iff` lemma ([#14791](https://github.com/leanprover-community/mathlib/pull/14791))

### [2022-06-24 09:16:09](https://github.com/leanprover-community/mathlib/commit/6cefaf4)
feat(measure_theory/function/conditional_expectation): conditional expectation w.r.t. the restriction of a measure to a set ([#14751](https://github.com/leanprover-community/mathlib/pull/14751))
We prove `(μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m]`.

### [2022-06-24 01:29:11](https://github.com/leanprover-community/mathlib/commit/ac2e9db)
feat(data/real/{e,}nnreal): add some order isomorphisms ([#14900](https://github.com/leanprover-community/mathlib/pull/14900))
* If `a` is a nonnegative real number, then
  -  `set.Icc (0 : ℝ) (a : ℝ)` is order isomorphic to `set.Iic a`;
  - `set.Iic (a : ℝ≥0∞)` is order isomorphic to `set.Iic a`;
* Also, `ℝ≥0∞` is order isomorphic both to `Iic (1 : ℝ≥0∞)` and to the unit interval in `ℝ`.
* Use the latter fact to golf `ennreal.second_countable_topology`.
* Golf `ennreal.has_continuous_inv` using `order_iso.continuous`.
* Improve definitional equalities for `equiv.subtype_subtype_equiv_subtype_exists`, `equiv.subtype_subtype_equiv_subtype_inter`, `equiv.subtype_subtype_equiv_subtype`, `equiv.set.sep`, use `simps`.

### [2022-06-24 01:29:10](https://github.com/leanprover-community/mathlib/commit/cb94893)
refactor(order/complete_lattice): `Sup` lemmas before `Inf` lemmas ([#14868](https://github.com/leanprover-community/mathlib/pull/14868))
Throughout the file, we make sure that `Sup` theorems always appear immediately before their `Inf` counterparts. This ensures consistency, and makes it much easier to golf theorems or detect missing API.
We choose to put `Sup` before `Inf` rather than the other way around, since this seems to minimize the amount of things that need to be moved around, and it matches the order that we define the two operations.
We also golf a few proofs throughout, and add some missing corresponding theorems, namely:
- `infi_extend_top`
- `infi_supr_ge_nat_add`
- `unary_relation_Inf_iff`
- `binary_relation_Inf_iff`

### [2022-06-24 01:29:09](https://github.com/leanprover-community/mathlib/commit/649ca66)
chore(*): Disparate generalizations to division monoids ([#14686](https://github.com/leanprover-community/mathlib/pull/14686))
The leftover changes from the introduction of `division_monoid`.

### [2022-06-23 23:27:42](https://github.com/leanprover-community/mathlib/commit/56185bd)
feat(data/finset): add some lemmas about `finset.disj_union` ([#14910](https://github.com/leanprover-community/mathlib/pull/14910))

### [2022-06-23 20:16:37](https://github.com/leanprover-community/mathlib/commit/198cb64)
refactor(ring_theory): generalize basic API of `ring_hom` to `ring_hom_class` ([#14756](https://github.com/leanprover-community/mathlib/pull/14756))
This PR generalizes part of the basic API of ring homs to `ring_hom_class`. This notably includes things like `ring_hom.ker`, `ideal.map` and `ideal.comap`. I left the namespaces unchanged, for example `ring_hom.ker` remains the same even though it is now defined for any `ring_hom_class` morphism; this way dot notation still (mostly) works for actual ring homs.

### [2022-06-23 16:23:10](https://github.com/leanprover-community/mathlib/commit/44d3fc0)
chore(data/nat,int): move field-specific lemmas about cast ([#14890](https://github.com/leanprover-community/mathlib/pull/14890))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is a step in rearranging those imports: remove the definition of a field from the dependencies of the casts `ℕ → α` and `ℤ → α`, where `α` is a (semi)ring.

### [2022-06-23 16:23:08](https://github.com/leanprover-community/mathlib/commit/c3e3d1a)
feat(data/set): replace `set_coe.can_lift` by `subtype.can_lift` ([#14792](https://github.com/leanprover-community/mathlib/pull/14792))

### [2022-06-23 16:23:07](https://github.com/leanprover-community/mathlib/commit/4de20c5)
feat(analysis/../log): log_nat_eq_sum_factorization ([#14782](https://github.com/leanprover-community/mathlib/pull/14782))

### [2022-06-23 16:23:06](https://github.com/leanprover-community/mathlib/commit/c2fcf9f)
feat(data/polynomial/erase_lead): Characterizations of polynomials of small support ([#14500](https://github.com/leanprover-community/mathlib/pull/14500))
This PR adds iff-lemmas `card_support_eq_one`, `card_support_eq_two`, and `card_support_eq_three`. These will be useful for irreducibility of x^n-x-1.

### [2022-06-23 14:10:06](https://github.com/leanprover-community/mathlib/commit/ef24ace)
feat(order/hom/basic): some lemmas about order homs and equivs  ([#14872](https://github.com/leanprover-community/mathlib/pull/14872))
A few lemmas from [#11053](https://github.com/leanprover-community/mathlib/pull/11053), which I have seperated from the original PR following @riccardobrasca's suggestion.

### [2022-06-23 14:10:05](https://github.com/leanprover-community/mathlib/commit/dd2e7ad)
feat(analysis/convex/strict_convex_space): isometries of strictly convex spaces are affine ([#14837](https://github.com/leanprover-community/mathlib/pull/14837))
Add the result that isometries of (affine spaces for) real normed
spaces with strictly convex codomain are affine isometries.  In
particular, this applies to isometries of Euclidean spaces (we already
have the instance that real inner product spaces are uniformly convex
and thus strictly convex).  Strict convexity means the surjectivity
requirement of Mazur-Ulam can be avoided.

### [2022-06-23 14:10:04](https://github.com/leanprover-community/mathlib/commit/966bb24)
feat(group_theory/finite_abelian): Structure of finite abelian groups ([#14736](https://github.com/leanprover-community/mathlib/pull/14736))
Any finitely generated abelian group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
Any finite abelian group is a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
(TODO : prove uniqueness of this decomposition)

### [2022-06-23 14:10:03](https://github.com/leanprover-community/mathlib/commit/cff439d)
feat(analysis/seminorm): add add_group_seminorm ([#14336](https://github.com/leanprover-community/mathlib/pull/14336))
We introduce `add_group_seminorm` and refactor `seminorm` to extend this new definition. This new `add_group_seminorm` structure will also be used in [#14115](https://github.com/leanprover-community/mathlib/pull/14115) to define `ring_seminorm`.

### [2022-06-23 14:10:01](https://github.com/leanprover-community/mathlib/commit/585a1bf)
feat(number_theory): define ramification index and inertia degree ([#14332](https://github.com/leanprover-community/mathlib/pull/14332))
We define ramification index `ramification_idx` and inertia degree `inertia_deg` for `P : ideal S` over `p : ideal R` given a ring extension `f : R →+* S`. The literature generally assumes `p` is included in `P`, both are maximal, `R` is the ring of integers of a number field `K` and `S` is the integral closure of `R` in `L`, a finite separable extension of `K`; we relax these assumptions as much as is practical.

### [2022-06-23 11:58:10](https://github.com/leanprover-community/mathlib/commit/cc4b8e5)
feat(data/sigma,data/ulift,logic/equiv): add missing lemmas ([#14903](https://github.com/leanprover-community/mathlib/pull/14903))
Add lemmas and `equiv`s about `plift`, `psigma`, and `pprod`.

### [2022-06-23 10:25:45](https://github.com/leanprover-community/mathlib/commit/cf23199)
chore(number_theory/lucas_lehmer): remove `has_to_pexpr` instances ([#14905](https://github.com/leanprover-community/mathlib/pull/14905))
These instances are sort of out-of-place, and aren't really needed anyway.
We already use the more verbose ``%%`(n)`` notation elsewhere in mathlib, which as an operation makes more conceptual sense.
Until [#14901](https://github.com/leanprover-community/mathlib/pull/14901) these two instances were just special cases of `has_reflect.has_to_pexpr`. While unlike that instance these two instances are not diamond-forming, they're unecessary special cases that make antiquoting harder to understand.

### [2022-06-22 23:55:53](https://github.com/leanprover-community/mathlib/commit/416edbd)
chore(ring_theory/polynomial/symmetric): golf proofs ([#14866](https://github.com/leanprover-community/mathlib/pull/14866))

### [2022-06-22 21:42:36](https://github.com/leanprover-community/mathlib/commit/c45e5d5)
fix(meta/expr): remove `has_reflect.has_to_pexpr` ([#14901](https://github.com/leanprover-community/mathlib/pull/14901))
This instance (introduced in [#3477](https://github.com/leanprover-community/mathlib/pull/3477)) forms a diamond with the builtin `pexpr.has_to_pexpr`:
```lean
import meta.expr
#eval show tactic unit, from do
  let i1 : has_to_pexpr pexpr := pexpr.has_to_pexpr,
  let i2 : has_to_pexpr pexpr := has_reflect.has_to_pexpr,
  let e := ``(1),
  let p1 := @to_pexpr _ i1 e,
  let p2 := @to_pexpr _ i2 e,
  guard (p1 = p2) -- fails
```
The consequence is that in cases where `bar` is not a `pexpr` or `expr` but a value to be reflected, ``` ``(foo %%bar) ``` now has to be written ``` ``(foo %%`(bar)) ```; a spelling already used in various existing files.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/Instance.20diamonds.20in.20has_to_pexpr/near/287083928)

### [2022-06-22 18:31:24](https://github.com/leanprover-community/mathlib/commit/2a732ed)
chore(analysis/special_functions/log/basic): golf a proof ([#14898](https://github.com/leanprover-community/mathlib/pull/14898))

### [2022-06-22 18:31:23](https://github.com/leanprover-community/mathlib/commit/23918a5)
feat(order/filter/basic): add some lemmas about `eventually_le` ([#14891](https://github.com/leanprover-community/mathlib/pull/14891))

### [2022-06-22 18:31:21](https://github.com/leanprover-community/mathlib/commit/12e5f2e)
refactor(data/set/countable): make `set.countable` protected ([#14886](https://github.com/leanprover-community/mathlib/pull/14886))
I'm going to add `_root_.countable` typeclass, a data-free version of `encodable`.

### [2022-06-22 18:31:20](https://github.com/leanprover-community/mathlib/commit/d8fc588)
refactor(data/finite/card): split from `basic` ([#14885](https://github.com/leanprover-community/mathlib/pull/14885))

### [2022-06-22 18:31:18](https://github.com/leanprover-community/mathlib/commit/c2719ad)
feat(topology/basic): `sum.elim` of locally finite set families is locally finite ([#14826](https://github.com/leanprover-community/mathlib/pull/14826))

### [2022-06-22 18:31:17](https://github.com/leanprover-community/mathlib/commit/44bb35e)
feat({algebra/big_operators/basic,data/rat/cast}): Missing cast lemmas ([#14824](https://github.com/leanprover-community/mathlib/pull/14824))
`rat.cast_sum`, `rat.cast_prod` and `nat`, `int` lemmas about `multiset` and `list` big operators.

### [2022-06-22 16:29:05](https://github.com/leanprover-community/mathlib/commit/38642ef)
chore(data/rat): rename `data.rat.basic` to `data.rat.defs` ([#14895](https://github.com/leanprover-community/mathlib/pull/14895))
This is a preparatory step for PR [#14893](https://github.com/leanprover-community/mathlib/pull/14893) that moves only the `field ℚ` instance (and its small set of dependencies) back to `data.rat.basic`; doing this in two moves should produce a neater set of diffs.

### [2022-06-22 16:29:04](https://github.com/leanprover-community/mathlib/commit/f57c0cd)
chore(algebra/{group_power,order}): split off field lemmas ([#14849](https://github.com/leanprover-community/mathlib/pull/14849))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is half of rearranging those imports: remove the definition of a field from the dependencies of basic lemmas about `nsmul`, `npow`, `zsmul` and `zpow`.

### [2022-06-22 13:46:51](https://github.com/leanprover-community/mathlib/commit/d939b0e)
feat(topology/vector_bundle/hom): define the vector bundle of continuous linear maps ([#14541](https://github.com/leanprover-community/mathlib/pull/14541))
* The changes in `topology/fiber_bundle` are not necessary for this PR, but perhaps nice additions
* Co-authored by: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
* Co-authored by: Patrick Massot <patrick.massot@u-psud.fr>

### [2022-06-22 08:58:26](https://github.com/leanprover-community/mathlib/commit/ad49768)
feat(set_theory/surreal/basic): define map `surreal →+o game` ([#14783](https://github.com/leanprover-community/mathlib/pull/14783))

### [2022-06-22 04:11:06](https://github.com/leanprover-community/mathlib/commit/61b837f)
feat(combinatorics/simple_graph/connectivity): Connectivity is a graph property ([#14865](https://github.com/leanprover-community/mathlib/pull/14865))
`simple_graph.preconnected` and `simple_graph.connected` are preserved under graph isomorphisms.

### [2022-06-22 02:09:00](https://github.com/leanprover-community/mathlib/commit/f3cd150)
fix(tactic/apply_fun.lean): instantiate mvars in apply_fun ([#14882](https://github.com/leanprover-community/mathlib/pull/14882))
Fixes leanprover-community/lean[#733](https://github.com/leanprover-community/mathlib/pull/733)

### [2022-06-21 16:31:41](https://github.com/leanprover-community/mathlib/commit/3b6552e)
chore(linear_algebra/alternating): more lemmas about `curry_left` ([#14844](https://github.com/leanprover-community/mathlib/pull/14844))
This follows on from [#14802](https://github.com/leanprover-community/mathlib/pull/14802)

### [2022-06-21 16:31:40](https://github.com/leanprover-community/mathlib/commit/d953773)
feat(data/finsupp/basic): make `prod_add_index_of_disjoint` to_additive ([#14786](https://github.com/leanprover-community/mathlib/pull/14786))
Adds lemma `sum_add_index_of_disjoint (h : disjoint f1.support f2.support) (g : α → M → β) : (f1 + f2).sum g = f1.sum g + f2.sum g`

### [2022-06-21 16:31:39](https://github.com/leanprover-community/mathlib/commit/3e66afe)
feat(data/sigma): add reflected instance ([#14764](https://github.com/leanprover-community/mathlib/pull/14764))

### [2022-06-21 16:31:38](https://github.com/leanprover-community/mathlib/commit/b779513)
feat(order/conditionally_complete_lattice): add `cInf_le_cInf'` ([#14719](https://github.com/leanprover-community/mathlib/pull/14719))
A version of `cInf_le_cInf` for `conditionally_complete_linear_order_bot`

### [2022-06-21 14:57:41](https://github.com/leanprover-community/mathlib/commit/2d70b94)
golf(data/polynomial): factorization into linear factors when #roots=degree  ([#14862](https://github.com/leanprover-community/mathlib/pull/14862))
+ Golf the proofs of `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` and `C_leading_coeff_mul_prod_multiset_X_sub_C` and move them from *splitting_field.lean* to *ring_division.lean*; instead of using the former to deduce the latter as is currently done in mathlib, we prove the latter first and deduce the former easily. Remove the less general auxiliary, `private` `_of_field` versions.
+ Move `pairwise_coprime_X_sub` from *field_division.lean* to *ring_division.lean*. Rename it to `pairwise_coprime_X_sub_C` to conform with existing convention. Golf its proof using the more general new lemma `is_coprime_X_sub_C_of_is_unit_sub`.
+ Golf `monic.irreducible_of_irreducible_map`, but it's essentially the same proof.

### [2022-06-21 14:57:40](https://github.com/leanprover-community/mathlib/commit/ee12362)
feat(topology/metric_space/basic): Add `ball_comm` lemmas ([#14858](https://github.com/leanprover-community/mathlib/pull/14858))
This adds `closed_ball` and `sphere` comm lemmas to go with the existing `mem_ball_comm`.

### [2022-06-21 13:23:46](https://github.com/leanprover-community/mathlib/commit/2b5a577)
doc(data/polynomial/div): fix runaway code block ([#14864](https://github.com/leanprover-community/mathlib/pull/14864))
Also use a fully-qualilfied name for linking

### [2022-06-21 13:23:45](https://github.com/leanprover-community/mathlib/commit/65031ca)
feat(ring_theory/dedekind_domain/ideal): drop an unneeded assumption ([#14444](https://github.com/leanprover-community/mathlib/pull/14444))

### [2022-06-21 11:26:39](https://github.com/leanprover-community/mathlib/commit/273986a)
fix(topology/algebra/group_completion): add lemmas about nsmul and zsmul and fix diamonds ([#14846](https://github.com/leanprover-community/mathlib/pull/14846))
This prevents a diamond forming between `uniform_space.completion.has_scalar` and the default `add_monoid.nsmul` and `sub_neg_monoid.zsmul` fields; by manually defining the latter to match the former.
To do this, we add two new instances of `has_uniform_continuous_smul` for nat- and int- actions.
To use the existing scalar actions, we had to shuffle the imports around a bit.

### [2022-06-21 11:26:38](https://github.com/leanprover-community/mathlib/commit/2a7bde0)
feat(data{finset,set}/pointwise): Pointwise monoids are domains ([#14687](https://github.com/leanprover-community/mathlib/pull/14687))
`no_zero_divisors`/`no_zero_smul_divisors` instances for `set` and `finset`.

### [2022-06-21 09:14:05](https://github.com/leanprover-community/mathlib/commit/481f991)
refactor(algebra/{hom/equiv, ring/equiv}): rename `equiv_of_unique_of_unique` to `equiv_of_unique` ([#14861](https://github.com/leanprover-community/mathlib/pull/14861))
This matches [`equiv.equiv_of_unique`](https://leanprover-community.github.io/mathlib_docs/logic/equiv/basic.html#equiv.equiv_of_unique).

### [2022-06-21 07:18:59](https://github.com/leanprover-community/mathlib/commit/e1d7cc7)
chore(set_theory/game/*): create `pgame` and `natural_ops` locales ([#14856](https://github.com/leanprover-community/mathlib/pull/14856))

### [2022-06-21 07:18:57](https://github.com/leanprover-community/mathlib/commit/67e026c)
fix(tactic/norm_num): fix bad proof / bad test ([#14852](https://github.com/leanprover-community/mathlib/pull/14852))
This is a bug in master but it was first noticed in [#14683](https://github.com/leanprover-community/mathlib/pull/14683).

### [2022-06-21 05:57:01](https://github.com/leanprover-community/mathlib/commit/8ac19d3)
chore(data/finsupp/fin): fix spacing ([#14860](https://github.com/leanprover-community/mathlib/pull/14860))

### [2022-06-21 04:38:57](https://github.com/leanprover-community/mathlib/commit/326465d)
chore(set_theory/ordinal/natural_ops): use derive ([#14859](https://github.com/leanprover-community/mathlib/pull/14859))

### [2022-06-21 01:37:43](https://github.com/leanprover-community/mathlib/commit/3b5441c)
feat(data/fintype/basic): equivalence between `finset α` and `set α` for `fintype α` ([#14840](https://github.com/leanprover-community/mathlib/pull/14840))

### [2022-06-21 00:01:30](https://github.com/leanprover-community/mathlib/commit/87f4758)
feat(polynomial/ring_division): strengthen/generalize various lemmas ([#14839](https://github.com/leanprover-community/mathlib/pull/14839))
+ Generalize the assumption `function.injective f` in `le_root_multiplicity_map` to `map f p ≠ 0`. Strictly speaking this is not a generalization because the trivial case `p = 0` is excluded. If one do want to apply the lemma without assuming `p ≠ 0`, they can use the newly introduced `eq_root_multiplicity_map`, which is a strengthening of the original lemma (with the same hypothesis `function.injective f`).
+ Extract some common `variables` from four lemmas.
+ Generalize `eq_of_monic_of_dvd_of_nat_degree_le` to `eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le`: if a polynomial `q` is divisible by a monic polynomial `p` and has degree no greater than `p`, then `q = p`. Also remove the `is_domain` hypothesis and golf the proof.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/multiplicity.20of.20root.20in.20extension.20field/near/286736361)

### [2022-06-20 22:02:23](https://github.com/leanprover-community/mathlib/commit/125055b)
refactor(data/sym/basic): change notation for sym.cons ([#14853](https://github.com/leanprover-community/mathlib/pull/14853))
Switch from `::` to `::ₛ` for `sym.cons` so that it no longer conflicts with `list.cons`. This (finally) puts it in line with other notations, like `::ₘ` for `multiset.cons`.

### [2022-06-20 16:13:29](https://github.com/leanprover-community/mathlib/commit/9df2762)
chore(data/nat/totient): golf a proof ([#14851](https://github.com/leanprover-community/mathlib/pull/14851))

### [2022-06-20 13:49:56](https://github.com/leanprover-community/mathlib/commit/f855a4b)
feat(order/monotone): Monotonicity of `prod.map` ([#14843](https://github.com/leanprover-community/mathlib/pull/14843))
If `f` and `g` are monotone/antitone, then `prod.map f g` is as well.

### [2022-06-20 13:49:55](https://github.com/leanprover-community/mathlib/commit/66d3f89)
feat(logic/unique): functions from a `unique` type is `const` ([#14823](https://github.com/leanprover-community/mathlib/pull/14823))
+ A function `f` from a `unique` type is equal to the constant function with value `f default`, and the analogous heq version for dependent functions.
+ Also changes `Π a : α, Sort v` in the file to `α → Sort v`.
Inspired by https://github.com/leanprover-community/mathlib/pull/14724#discussion_r900542203

### [2022-06-20 13:49:54](https://github.com/leanprover-community/mathlib/commit/0b806ba)
docs(linear_algebra): refer to `pi.basis_fun` in `pi.basis` ([#14505](https://github.com/leanprover-community/mathlib/pull/14505))
This is a common question so the more ways we can point to the standard basis, the better!
See also Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Standard.20basis

### [2022-06-20 11:25:39](https://github.com/leanprover-community/mathlib/commit/c781c0e)
feat(data/prod/basic): Involutivity of `prod.map` ([#14845](https://github.com/leanprover-community/mathlib/pull/14845))
If `f` and `g` are involutive, then so is `prod.map f g`.

### [2022-06-20 11:25:38](https://github.com/leanprover-community/mathlib/commit/c1abe06)
refactor(linear_algebra/exterior_algebra): redefine `exterior_algebra` as `clifford_algebra 0` ([#14819](https://github.com/leanprover-community/mathlib/pull/14819))
The motivation here is to avoid having to duplicate API between these two types, else we end up having to repeat every definition that works on `clifford_algebra Q` on `exterior_algebra` for the case when `Q = 0`. This also:
* Removes `as_exterior : clifford_algebra (0 : quadratic_form R M) ≃ₐ[R] exterior_algebra R M` as the two types are reducibly defeq.
* Removes support for working with exterior algebras over semirings; while it is entirely possible to generalize `clifford_algebra` to semirings to make this removal unnecessary, it creates difficulties with elaboration, and the support for semirings was without mathematical motivation in the first place. This is in line with a [vote on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Exterior.20algebras.20over.20semiring/near/286660821).
The consequences are:
* A bunch of redundant code can be removed
* `x.reverse` and `x.involute` should now work on `x : exterior_algebra R M`.
* Future API will extend effortlessly from one to the other

### [2022-06-20 11:25:37](https://github.com/leanprover-community/mathlib/commit/320ea39)
feat(data/dfinsupp/basic): add missing lemmas about `single` ([#14815](https://github.com/leanprover-community/mathlib/pull/14815))
These lemmas were missed in [#13076](https://github.com/leanprover-community/mathlib/pull/13076):
* `comap_domain_single`
* `comap_domain'_single`
* `sigma_curry_single`
* `sigma_uncurry_single`
* `extend_with_single_zero`
* `extend_with_zero`
These are useful since many induction principles replace a generic `dfinsupp` with `dfinsupp.single`.

### [2022-06-20 11:25:36](https://github.com/leanprover-community/mathlib/commit/c5e13ba)
feat(algebra/order/pointwise): Supremum of pointwise operations ([#13669](https://github.com/leanprover-community/mathlib/pull/13669))
Pointwise operations of sets distribute over the (conditional) supremum/infimum.

### [2022-06-20 09:15:57](https://github.com/leanprover-community/mathlib/commit/f9c339e)
feat(group_theory/group_action/sigma): Scalar action on a sigma type ([#14825](https://github.com/leanprover-community/mathlib/pull/14825))
`(Π i, has_scalar α (β i)) → has_scalar α (Σ i, β i)` and similar.

### [2022-06-20 09:15:55](https://github.com/leanprover-community/mathlib/commit/ff40b2c)
chore(algebra/group/basic): lemmas about `bit0`, `bit1`, and addition ([#14798](https://github.com/leanprover-community/mathlib/pull/14798))

### [2022-06-20 09:15:53](https://github.com/leanprover-community/mathlib/commit/df50b88)
feat(order/filter/bases): basis for directed (b)infi of filters ([#14775](https://github.com/leanprover-community/mathlib/pull/14775))

### [2022-06-20 09:15:51](https://github.com/leanprover-community/mathlib/commit/2604c04)
feat(number_theory/number_field): add definitions and results about embeddings  ([#14749](https://github.com/leanprover-community/mathlib/pull/14749))
We consider the embeddings of a number field into an algebraic closed field (of char. 0) and prove some results about those. 
We also prove the ```number_field``` instance  for ```adjoint_root``` of an irreducible polynomial of `ℚ[X]`. 
From flt-regular

### [2022-06-20 09:15:48](https://github.com/leanprover-community/mathlib/commit/8263a4b)
refactor(analysis/complex/upper_half_plane): move topology to a new file ([#14748](https://github.com/leanprover-community/mathlib/pull/14748))
Also add some instances and lemmas about topology on the upper half plane.

### [2022-06-20 09:15:46](https://github.com/leanprover-community/mathlib/commit/804afcb)
feat(geometry/manifold/diffeomorph): some additions needed for smooth vector bundles ([#14738](https://github.com/leanprover-community/mathlib/pull/14738))
* Define `diffeomorph.prod_comm`, `diffeomorph.prod_congr`, `diffeomorph.prod_assoc`
* Prove `cont_mdiff_on.comp_cont_mdiff`
* In `fiber_bundle`, define some lemmas for `local_triv_at` that were already there for `local_triv`
* Yes, this PR does a couple different things, but it is still very small
* This is part of [#14412](https://github.com/leanprover-community/mathlib/pull/14412)

### [2022-06-20 09:15:45](https://github.com/leanprover-community/mathlib/commit/04f4505)
feat(analysis/convex/join): Join of sets ([#14676](https://github.com/leanprover-community/mathlib/pull/14676))
Define the join of two sets as the union of all segments between them.

### [2022-06-20 07:16:13](https://github.com/leanprover-community/mathlib/commit/2903674)
refactor(order/conditionally_complete_lattice): tweak `well_founded.conditionally_complete_linear_order_with_bot` ([#14706](https://github.com/leanprover-community/mathlib/pull/14706))
We change the `well_founded` assumption on `well_founded.conditionally_complete_linear_order_bot` to an equivalent but more convenient `is_well_order` typeclass assumption. As such, we place it in the `is_well_order` namespace.

### [2022-06-20 04:10:04](https://github.com/leanprover-community/mathlib/commit/ae5b695)
refactor(number_theory/cyclotomic/*): refactor the definition of is_cyclotomic_extension ([#14463](https://github.com/leanprover-community/mathlib/pull/14463))
We modify the definition of `is_cyclotomic_extension`, requiring the existence of a primitive root of unity rather than a root of the cyclotomic polynomial. This removes almost all the `ne_zero` assumptions.

### [2022-06-20 00:03:55](https://github.com/leanprover-community/mathlib/commit/10a5275)
feat(analysis/normed/group/basic): `isometry.norm_map_of_map_zero` ([#14836](https://github.com/leanprover-community/mathlib/pull/14836))
Add the lemma that an isometry of `semi_normed_group`s that preserves
0 preserves the norm.

### [2022-06-19 23:24:05](https://github.com/leanprover-community/mathlib/commit/cf118ee)
feat(analysis/complex/upper_half_plane): add `upper_half_plane.mk` ([#14795](https://github.com/leanprover-community/mathlib/pull/14795))

### [2022-06-19 17:24:08](https://github.com/leanprover-community/mathlib/commit/26279c5)
chore(algebraic_geometry/function_field): fix timeout in `function_field.algebra` ([#14830](https://github.com/leanprover-community/mathlib/pull/14830))
Reduces `elaboration of function_field.algebra` from ~29.3s to ~0.4s.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/286714162)

### [2022-06-19 16:13:12](https://github.com/leanprover-community/mathlib/commit/65c9ffb)
feat(topology/algebra/infinite_sum) Sums over Z vs sums over N ([#14667](https://github.com/leanprover-community/mathlib/pull/14667))
This PR adds some functions for handling infinite sums indexed by the integers, relating them to sums over the naturals.

### [2022-06-19 12:34:38](https://github.com/leanprover-community/mathlib/commit/f460576)
feat(group_theory/group_action/sum): Scalar action on a sum of types ([#14818](https://github.com/leanprover-community/mathlib/pull/14818))
`has_scalar α β → has_scalar α γ → has_scalar α (β ⊕ γ)` and similar.

### [2022-06-19 09:55:31](https://github.com/leanprover-community/mathlib/commit/5dabef8)
feat(set_theory/game/basic): Basic lemmas on `inv` ([#13840](https://github.com/leanprover-community/mathlib/pull/13840))
Note that we've redefined `inv` so that `inv x = 0` when `x ≈ 0`. This is because, in order to lift it to an operation on surreals, we need to prove that equivalent numeric games give equivalent numeric values, and this isn't the case otherwise.

### [2022-06-19 09:12:48](https://github.com/leanprover-community/mathlib/commit/69686e7)
feat(algebra/category/Module): Tannaka duality for rings ([#14352](https://github.com/leanprover-community/mathlib/pull/14352))
Obviously this is not the most interesting statement that one might label "Tannaka duality", but perhaps it can get the ball rolling. :-)

### [2022-06-19 07:01:49](https://github.com/leanprover-community/mathlib/commit/7f358d0)
feat(category_theory/preadditive/eilenberg_moore): (Co)algebras over a (co)monad are preadditive ([#14811](https://github.com/leanprover-community/mathlib/pull/14811))
The category of algebras over an additive monad on a preadditive category is preadditive (and the dual result).

### [2022-06-18 19:10:48](https://github.com/leanprover-community/mathlib/commit/0a5b9eb)
feat(set_theory/game/pgame): tweak lemmas ([#14810](https://github.com/leanprover-community/mathlib/pull/14810))
This PR does the following:
- uncurry `le_of_forall_lf` and `le_of_forall_lt`.
- remove `lf_of_exists_le`, as it's made redundant by `lf_of_move_right_le` and `lf_of_le_move_left`.
- golfing.

### [2022-06-18 16:59:43](https://github.com/leanprover-community/mathlib/commit/4264220)
feat(analysis/asymptotics): add several lemmas ([#14805](https://github.com/leanprover-community/mathlib/pull/14805))
Also make `𝕜` explicit in `asymptotics.is_O_with_const_one` and `asymptotics.is_O_const_one`.

### [2022-06-18 16:59:42](https://github.com/leanprover-community/mathlib/commit/100975e)
feat(geometry/euclidean/inversion) new file ([#14692](https://github.com/leanprover-community/mathlib/pull/14692))
* Define `euclidean_geometry.inversion`.
* Prove Ptolemy's inequality.

### [2022-06-18 16:59:41](https://github.com/leanprover-community/mathlib/commit/92d5fdf)
feat(topology/metric_space/baire): generalize some lemmas ([#14633](https://github.com/leanprover-community/mathlib/pull/14633))
Add `is_Gδ.dense_{s,b,}Union_interior_of_closed`.

### [2022-06-18 16:59:40](https://github.com/leanprover-community/mathlib/commit/f1b0402)
feat(tactic/core + test/list_summands): a function extracting a list of summands from an expression ([#14617](https://github.com/leanprover-community/mathlib/pull/14617))
This meta def is used in [#13483](https://github.com/leanprover-community/mathlib/pull/13483), where `move_add` is defined.
A big reason for splitting these 5 lines off the main PR is that they are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.

### [2022-06-18 15:26:18](https://github.com/leanprover-community/mathlib/commit/3a8e0a1)
feat(group_theory/torsion): define the p-primary component of a group ([#14312](https://github.com/leanprover-community/mathlib/pull/14312))

### [2022-06-18 12:50:23](https://github.com/leanprover-community/mathlib/commit/3abee05)
chore(order/pfilter): more `principal` API ([#14759](https://github.com/leanprover-community/mathlib/pull/14759))
`principal` and `Inf` form a Galois coinsertion.

### [2022-06-18 09:28:02](https://github.com/leanprover-community/mathlib/commit/39986ae)
chore(data/nat/lattice): add `nat.infi_of_empty` to match `_root_.infi_of_empty` ([#14797](https://github.com/leanprover-community/mathlib/pull/14797))

### [2022-06-18 08:28:16](https://github.com/leanprover-community/mathlib/commit/7fb5ed2)
feat(data/complex/basic): add `complex.abs_le_sqrt_two_mul_max` ([#14804](https://github.com/leanprover-community/mathlib/pull/14804))

### [2022-06-17 23:41:50](https://github.com/leanprover-community/mathlib/commit/bd6b98b)
feat(linear_algebra/alternating): add more compositional API ([#14802](https://github.com/leanprover-community/mathlib/pull/14802))
These will be helpful in relating `alternating_map`s to the `exterior_algebra`.
This adds:
* `alternating_map.curry_left`
* `alternating_map.const_linear_equiv_of_is_empty`
* `alternating_map.dom_dom_congr`

### [2022-06-17 23:41:49](https://github.com/leanprover-community/mathlib/commit/0c47657)
chore(order/symm_diff): add lemma about `bxor` ([#14801](https://github.com/leanprover-community/mathlib/pull/14801))

### [2022-06-17 22:43:38](https://github.com/leanprover-community/mathlib/commit/4ff9e93)
feat(analysis/complex/basic): add a few lemmas about `dist` on `complex` ([#14796](https://github.com/leanprover-community/mathlib/pull/14796))

### [2022-06-17 20:37:43](https://github.com/leanprover-community/mathlib/commit/d2369bc)
feat(data/set/intervals): add two `ssubset` lemmas ([#14793](https://github.com/leanprover-community/mathlib/pull/14793))

### [2022-06-17 18:57:26](https://github.com/leanprover-community/mathlib/commit/e23de85)
feat(algebra/algebra/basic) : add ring_hom.equiv_rat_alg_hom ([#14772](https://github.com/leanprover-community/mathlib/pull/14772))
Proves the equivalence between `ring_hom` and `rat_alg_hom`.
From flt-regular

### [2022-06-17 17:39:07](https://github.com/leanprover-community/mathlib/commit/260d472)
feat(order/topology/**/uniform*): Lemmas about uniform convergence ([#14587](https://github.com/leanprover-community/mathlib/pull/14587))
To prove facts about uniform convergence, it is often useful to manipulate the various functions without dealing with the ε's and δ's. To do so, you need auxiliary lemmas about adding/muliplying/etc Cauchy sequences.
This commit adds several such lemmas. It supports [#14090](https://github.com/leanprover-community/mathlib/pull/14090), which we're slowly transforming to use these lemmas instead of doing direct ε/δ manipulation.

### [2022-06-17 16:27:29](https://github.com/leanprover-community/mathlib/commit/545f0fb)
feat(category_theory/monad/kleisli): dualise kleisli of monad to cokleisli of comonad ([#14799](https://github.com/leanprover-community/mathlib/pull/14799))
This PR defines the (co)Kleisli category of a comonad, defines the corresponding adjunction, and proves that it gives rise to the original comonad.

### [2022-06-17 15:08:42](https://github.com/leanprover-community/mathlib/commit/ade72ab)
refactor(linear_algebra/quadratic_form/basic): generalize to semiring ([#14303](https://github.com/leanprover-community/mathlib/pull/14303))
This uses a slightly nicer strategy than the one suggested by @adamtopaz [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Exterior.20algebras.20over.20semiring/near/282808284).
The main motivation here is to be able to talk about `0 : quadratic_form R M` even when there is no negation available, as that will let us merge `clifford_algebra`  (which currently requires negation) and `exterior_algebra` (which does not).
It's likely this generalization is broadly not very useful, so this adds a `quadratic_form.of_polar` constructor to preserve the old more convenient API.
Note the `.bib` file changed slightly as I ran the autoformatting tool.

### [2022-06-17 13:35:37](https://github.com/leanprover-community/mathlib/commit/9c2b890)
feat(group_theory/sylow): API lemmas for smul and subtype  ([#14521](https://github.com/leanprover-community/mathlib/pull/14521))
This PR adds some API lemmas for smul and subtype.

### [2022-06-17 11:03:20](https://github.com/leanprover-community/mathlib/commit/0be36f6)
feat(data/list/of_fn): Add `list.of_fn_add` and `list.of_fn_mul` ([#14370](https://github.com/leanprover-community/mathlib/pull/14370))
This adds some lemmas to split up lists generated over `fin (n + m)` and `fin (n * m)` into their constituent parts.
It also adds a congr lemma to allow `list.of_fn (λ i : fin n, _)` to be rewritten into `list.of_fn (λ i : fin m, _)` by `simp` when `h : n = m` is available.
I'll need these eventually to prove some things about products of tensor powers.

### [2022-06-17 08:38:50](https://github.com/leanprover-community/mathlib/commit/e427a0e)
feat(set/basic, order/boolean_algebra): generalized `compl_comp_compl` ([#14784](https://github.com/leanprover-community/mathlib/pull/14784))
This PR generalizes `compl_comp_compl` to apply whenever there is a `boolean_algebra` instance. We also make the set parameter of `compl_compl_image` explicit.

### [2022-06-17 01:10:15](https://github.com/leanprover-community/mathlib/commit/d21469e)
feat(set_theory/ordinal/basic): improve docs on `lift`, add `simp` lemmas ([#14599](https://github.com/leanprover-community/mathlib/pull/14599))
This is pretty much the same thing as [#14596](https://github.com/leanprover-community/mathlib/pull/14596), just on `ordinal.lift` instead of `cardinal.lift`.

### [2022-06-16 22:34:16](https://github.com/leanprover-community/mathlib/commit/d0b93fa)
feat(set_theory/{pgame, basic}): Notation for `relabelling`, golfing ([#14155](https://github.com/leanprover-community/mathlib/pull/14155))
We introduce the notation `≡r` for relabellings between two pre-games. We also golf many theorems on relabellings.

### [2022-06-16 19:20:25](https://github.com/leanprover-community/mathlib/commit/ae10dce)
feat(algebra/direct_sum/decomposition): add decompositions into a direct sum ([#14626](https://github.com/leanprover-community/mathlib/pull/14626))
This is a constructive version of `direct_sum.is_internal`, and generalizes the existing `graded_algebra`.
The main user-facing changes are:
* `graded_algebra.decompose` is now spelt `direct_sum.decompose_alg_hom`
* The simp normal form of decomposition is now `direct_sum.decompose`.
* `graded_algebra.support 𝒜 x` is now spelt `(decompose 𝒜 x).support`
* `left_inv` and `right_inv` has swapped, now with meaning "the decomposition is the (left|right) inverse of the canonical map" rather than the other way around
To keep this from growing even larger, I've left `graded_algebra.proj` alone for a future refactor.

### [2022-06-16 19:20:24](https://github.com/leanprover-community/mathlib/commit/67da272)
feat(analysis/inner_product_space): Gram-Schmidt Basis ([#14514](https://github.com/leanprover-community/mathlib/pull/14514))
When the Gram-Schmidt procedure is given a basis, it produces a basis.
This pull request also refactors the lemma `gram_schmidt_span`. The new versions of the lemmas cover the span of `Iio`, the span of `Iic` and the span of the complete set of input vectors. I was also able to remove some type classes in the process.

### [2022-06-16 15:46:22](https://github.com/leanprover-community/mathlib/commit/988f160)
fix(data/rat/basic): Remove incorrect simp attribute ([#14765](https://github.com/leanprover-community/mathlib/pull/14765))
Remove simp attribute that breaks `field_simp`.

### [2022-06-16 15:46:20](https://github.com/leanprover-community/mathlib/commit/6c46641)
feat(linear_algebra/clifford_algebra/fold): Add recursors for folding along generators ([#14619](https://github.com/leanprover-community/mathlib/pull/14619))
This adds `clifford_algebra.fold{l,r}` and `clifford_algebra.{left,right}_induction`.
The former are analogous to `list.foldl` and `list.foldr`, while the latter are two stronger variants of `clifford_algebra.induction`.
We don't bother duplicating these for the `exterior_algebra`, as a future PR will make `exterior_algebra = clifford_algebra 0` true by `rfl`.
This construction can be used to show:
* `clifford_algebra Q ≃ₗ[R] exterior_algebra R M` (when `invertible 2`)
* `clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q' Q)` (where `Q' Q` is a quadratic form over an augmented `V`)
These will follow in future PRs.

### [2022-06-16 15:46:18](https://github.com/leanprover-community/mathlib/commit/7584a10)
feat(set_theory/game/ordinal): addition of ordinals on games matches natural addition ([#14298](https://github.com/leanprover-community/mathlib/pull/14298))

### [2022-06-16 12:52:06](https://github.com/leanprover-community/mathlib/commit/b05d845)
feat(data/nat/basic): add a few lemmas ([#14718](https://github.com/leanprover-community/mathlib/pull/14718))
Add a few lemmas about sub and mod.

### [2022-06-16 11:52:28](https://github.com/leanprover-community/mathlib/commit/3feb151)
feat(algebra/homology,category_theory/abelian): exact_comp_mono_iff ([#14410](https://github.com/leanprover-community/mathlib/pull/14410))
From LTE.

### [2022-06-16 02:53:25](https://github.com/leanprover-community/mathlib/commit/6834a24)
feat(analysis/asymptotics): define `is_Theta` ([#14567](https://github.com/leanprover-community/mathlib/pull/14567))
* define `f =Θ[l] g` and prove basic properties;
* add `is_O.const_smul_left`, `is_o.const_smul_left`;
* rename `is_O_const_smul_left_iff` and `is_o_const_smul_left_iff` to
  `is_O_const_smul_left` and `is_o_const_smul_left`.

### [2022-06-16 02:00:04](https://github.com/leanprover-community/mathlib/commit/0053e3c)
feat(analysis/special_functions/arsinh): add lemmas, review API ([#14668](https://github.com/leanprover-community/mathlib/pull/14668))

### [2022-06-16 02:00:03](https://github.com/leanprover-community/mathlib/commit/22f3255)
refactor(set_theory/game/*): Delete `winner.lean` ([#14271](https://github.com/leanprover-community/mathlib/pull/14271))
The file `winner.lean` currently consists of one-line definitions and theorems, including aliases for basic inequalities. This PR removes the file, inlines all previous definitions and theorems, and golfs various proofs in the process.

### [2022-06-15 23:36:05](https://github.com/leanprover-community/mathlib/commit/f991b4d)
chore(*): Bump to Lean 3.43.0 ([#14684](https://github.com/leanprover-community/mathlib/pull/14684))
Most of the changes in this upgrade are a consequence of https://github.com/leanprover-community/lean/pull/675, which removed almost all of `init/data/set.lean` from lean core so it could be migrated to mathlib. Other relevant core changes are https://github.com/leanprover-community/lean/pull/714, which removed a few order decidability instances, and https://github.com/leanprover-community/lean/pull/711, which caused a docstring to be rejected.

### [2022-06-15 21:34:32](https://github.com/leanprover-community/mathlib/commit/c81c6c9)
feat(data/polynomial/erase_lead): `lt_nat_degree_of_mem_erase_lead_support` ([#14745](https://github.com/leanprover-community/mathlib/pull/14745))
This PR adds a lemma `lt_nat_degree_of_mem_erase_lead_support` and adds term-mode proofs of a couple related lemmas.

### [2022-06-15 21:34:31](https://github.com/leanprover-community/mathlib/commit/ea2dbcb)
feat(analysis/special_functions/integrals): Add integral_cpow ([#14491](https://github.com/leanprover-community/mathlib/pull/14491))
Also adds various helper lemmas.
The purpose of this commit is to provide a computed integral for the `cpow` function. The proof is functionally identical to that of `integral_rpow`, but places a different set of constraints on the various parameters due to different continuity constraints of the cpow function.
Some notes on future improvments:
  * The range of valid integration can be expanded using ae_covers a la [#14147](https://github.com/leanprover-community/mathlib/pull/14147)
  * We currently only contemplate a real argument. However, this should essentially work for any continuous path in the complex plane that avoids the negative real axis. That would require a lot more machinery, not currently in mathlib.
Despite these restrictions, why is this important? This, Abel summation, [#13500](https://github.com/leanprover-community/mathlib/pull/13500), and [#14090](https://github.com/leanprover-community/mathlib/pull/14090) are the key ingredients to bootstrapping Dirichlet series.

### [2022-06-15 21:34:27](https://github.com/leanprover-community/mathlib/commit/7145043)
feat(algebra/group/pi): Technical casework lemma for when two binomials are equal to each other ([#14400](https://github.com/leanprover-community/mathlib/pull/14400))
This PR adds a technical casework lemma for when two binomials are equal to each other. It will be useful for irreducibility of x^n-x-1. If anyone can see how to golf the proof further, that would be appreciated!

### [2022-06-15 18:51:17](https://github.com/leanprover-community/mathlib/commit/665cec2)
chore(data/nat/factorization/basic): delete two duplicate lemmas ([#14754](https://github.com/leanprover-community/mathlib/pull/14754))
Deleting two lemmas introduced in [#14461](https://github.com/leanprover-community/mathlib/pull/14461) that are duplicates of lemmas already present, as follows:
```
lemma div_factorization_pos {q r : ℕ} (hr : nat.prime r) (hq : q ≠ 0) :
  q / (r ^ (q.factorization r)) ≠ 0 := div_pow_factorization_ne_zero r hq
```
```
lemma ne_dvd_factorization_div {q r : ℕ} (hr : nat.prime r) (hq : q ≠ 0) :
  ¬(r ∣ (q / (r ^ (q.factorization r)))) := not_dvd_div_pow_factorization hr hq
```

### [2022-06-15 18:51:16](https://github.com/leanprover-community/mathlib/commit/a583244)
feat(representation_theory/Action): a few lemmas about the rigid structure of Action ([#14620](https://github.com/leanprover-community/mathlib/pull/14620))

### [2022-06-15 18:51:15](https://github.com/leanprover-community/mathlib/commit/c4ef20e)
feat(order/rel_classes): an irreflexive order on a subsingleton type is a well order ([#14601](https://github.com/leanprover-community/mathlib/pull/14601))
This generalizes a previously existing lemma that the empty relation on a subsingleton type is a well order.

### [2022-06-15 17:10:38](https://github.com/leanprover-community/mathlib/commit/94fa33b)
fix(tactic/congrm): support multiple binders ([#14753](https://github.com/leanprover-community/mathlib/pull/14753))

### [2022-06-15 17:10:37](https://github.com/leanprover-community/mathlib/commit/430da94)
chore(analysis/normed): move `normed.normed_field` to `normed.field.basic` ([#14747](https://github.com/leanprover-community/mathlib/pull/14747))

### [2022-06-15 17:10:36](https://github.com/leanprover-community/mathlib/commit/6a0f967)
feat(data/finite/set): `finite` instances for set constructions ([#14673](https://github.com/leanprover-community/mathlib/pull/14673))

### [2022-06-15 17:10:35](https://github.com/leanprover-community/mathlib/commit/8eaeec2)
chore(a few random files): golfing using the new tactic `congrm` ([#14593](https://github.com/leanprover-community/mathlib/pull/14593))
This PR is simply intended to showcase some possible applications of the new tactic `congrm`, introduced in [#14153](https://github.com/leanprover-community/mathlib/pull/14153).

### [2022-06-15 14:55:51](https://github.com/leanprover-community/mathlib/commit/34ce784)
refactor(algebra/group_with_zero/basic): Golf using division monoid lemmas ([#14213](https://github.com/leanprover-community/mathlib/pull/14213))
Make all eligible `group_with_zero` lemmas one-liners from `division_monoid` ones and group them within the file.

### [2022-06-15 14:55:50](https://github.com/leanprover-community/mathlib/commit/bbca289)
feat(dynamics/periodic_pts): `chain.pairwise` on orbit ([#12991](https://github.com/leanprover-community/mathlib/pull/12991))
We prove that a relation holds pairwise on an orbit iff it does for `f^[n] x` and `f^[n+1] x` for any `n`.

### [2022-06-15 13:13:12](https://github.com/leanprover-community/mathlib/commit/4661473)
chore(analysis/normed/normed_field): golf 2 proofs ([#14746](https://github.com/leanprover-community/mathlib/pull/14746))

### [2022-06-15 13:13:11](https://github.com/leanprover-community/mathlib/commit/dccdef6)
chore(set_theory/ordinal/basic): golf ordinal addition definition ([#14744](https://github.com/leanprover-community/mathlib/pull/14744))

### [2022-06-15 13:13:10](https://github.com/leanprover-community/mathlib/commit/d2bfb32)
feat(analysis/normed_space): range of `norm` ([#14740](https://github.com/leanprover-community/mathlib/pull/14740))
* Add `exists_norm_eq`, `range_norm`, `range_nnnorm`, and `nnnorm_surjective`.
* Open `set` namespace.

### [2022-06-15 13:13:09](https://github.com/leanprover-community/mathlib/commit/2aa3fd9)
feat(analysis/convex): a convex set is contractible ([#14732](https://github.com/leanprover-community/mathlib/pull/14732))

### [2022-06-15 13:13:08](https://github.com/leanprover-community/mathlib/commit/7430d2d)
feat(data/complex/exponential): more `simp` lemmas ([#14731](https://github.com/leanprover-community/mathlib/pull/14731))
Add `simp` attrs and `simp` lemmas.

### [2022-06-15 13:13:07](https://github.com/leanprover-community/mathlib/commit/fee91d7)
feat(data/fin/vec_notation): add has_reflect instance and tests ([#14670](https://github.com/leanprover-community/mathlib/pull/14670))

### [2022-06-15 13:13:06](https://github.com/leanprover-community/mathlib/commit/764d7a9)
feat(probability/stopping): first hitting time ([#14630](https://github.com/leanprover-community/mathlib/pull/14630))
This PR adds the first hitting time (before some time) and proves that it is a stopping time in the discrete case.

### [2022-06-15 13:13:04](https://github.com/leanprover-community/mathlib/commit/947c3c6)
refactor(order/locally_finite): Allow `finset.Iix`/`finset.Ixi` on empty types ([#14430](https://github.com/leanprover-community/mathlib/pull/14430))
Define `locally_finite_order_top` and `locally_finite_order_bot` are redefine `Ici`, `Ioi`, `iic`, `Iio` using them. Those new typeclasses are the same as `locally_finite_order` + `order_top`/`order_bot`, except that they allow the empty type, which is a surprisingly useful feature.

### [2022-06-15 11:13:37](https://github.com/leanprover-community/mathlib/commit/114f543)
feat(model_theory/semantics, elementary_maps): Defines elementary equivalence ([#14723](https://github.com/leanprover-community/mathlib/pull/14723))
Defines elementary equivalence of structures
Shows that the domain and codomain of an elementary map are elementarily equivalent.

### [2022-06-15 11:13:36](https://github.com/leanprover-community/mathlib/commit/9c40f30)
refactor(set_theory/game/*): fix theorem names ([#14685](https://github.com/leanprover-community/mathlib/pull/14685))
Some theorems about `exists` had `forall` in the name, other theorems about swapped `≤` or `⧏` used `le` and `lf` instead of `ge` and `gf`.
We also golf `le_of_forall_lt`.

### [2022-06-15 11:13:35](https://github.com/leanprover-community/mathlib/commit/c667723)
feat(model_theory/syntax, semantics): Mapping formulas given maps on terms and relations ([#14466](https://github.com/leanprover-community/mathlib/pull/14466))
Defines `first_order.language.bounded_formula.map_term_rel`, which maps formulas given maps on terms and maps on relations.

### [2022-06-15 11:13:33](https://github.com/leanprover-community/mathlib/commit/ea97606)
feat(tactic/ring): recursive ring_nf ([#14429](https://github.com/leanprover-community/mathlib/pull/14429))
As [reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60ring_nf.60.20not.20consistently.20normalizing.3F). This allows `ring_nf` to rewrite inside the atoms of a ring expression, meaning that things like `f (a + b) + c` can simplify in both `+` expressions.

### [2022-06-15 10:32:10](https://github.com/leanprover-community/mathlib/commit/6e0e270)
feat(linear_algebra/matrix): positive definite ([#14531](https://github.com/leanprover-community/mathlib/pull/14531))
Define positive definite matrices and connect them to positive definiteness of quadratic forms.

### [2022-06-15 09:13:28](https://github.com/leanprover-community/mathlib/commit/784c703)
docs(topology/basic): Fix typo in library note ([#14743](https://github.com/leanprover-community/mathlib/pull/14743))

### [2022-06-15 08:32:58](https://github.com/leanprover-community/mathlib/commit/1fbe118)
golf(set_theory/game/pgame): golf `neg_le_neg_iff` ([#14726](https://github.com/leanprover-community/mathlib/pull/14726))
Also in this PR:
+ slightly golf `subsequent.trans`
+ replace `->` by `→`
+ replace a nonterminal `simp` by `dsimp`

### [2022-06-15 08:32:57](https://github.com/leanprover-community/mathlib/commit/7958e7d)
chore(analysis/convex/extreme): Make arguments semi-implicit ([#14698](https://github.com/leanprover-community/mathlib/pull/14698))
Change the definition of `is_extreme` from
```
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ open_segment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
```
to
```
B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ open_segment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
```
and similar for `extreme_points`.

### [2022-06-15 07:00:25](https://github.com/leanprover-community/mathlib/commit/6b4f3f2)
feat(data/nat/prime): prime.even_iff ([#14688](https://github.com/leanprover-community/mathlib/pull/14688))
Adds a lemma saying that the only even prime is two.

### [2022-06-15 04:54:47](https://github.com/leanprover-community/mathlib/commit/e86ab0b)
refactor(src/algebra/order/monoid): make bot_eq_zero a simp lemma only when the order is linear ([#14553](https://github.com/leanprover-community/mathlib/pull/14553))

### [2022-06-15 04:54:45](https://github.com/leanprover-community/mathlib/commit/b4b816c)
feat(number_theory/cyclotomic/primitive_roots): generalize finrank lemma  ([#14550](https://github.com/leanprover-community/mathlib/pull/14550))
We generalize certain results from fields to domains.

### [2022-06-15 03:13:18](https://github.com/leanprover-community/mathlib/commit/38ad656)
chore(field_theory/intermediate_field): fix timeout ([#14725](https://github.com/leanprover-community/mathlib/pull/14725))
+ Remove `@[simps]` from `intermediate_field_map` to reduce `decl post-processing of intermediate_field_map` from 18.3s to 46.4ms (on my machine).
+ Manually provide the two `simp` lemmas previously auto-generated by `@[simps]`. Mathlib compiles even without the two simp lemmas (see commit 1f5a7f1), but I am inclined to keep them in case some other branches/projects are using them.
[Zulip reports](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/285792556) about `intermediate_field_map` causing timeout in two separate branches

### [2022-06-15 03:13:17](https://github.com/leanprover-community/mathlib/commit/dd4d8e6)
feat(logic/hydra): basic lemmas on `cut_expand` ([#14408](https://github.com/leanprover-community/mathlib/pull/14408))

### [2022-06-15 03:13:16](https://github.com/leanprover-community/mathlib/commit/a16f1cf)
feat(set_theory/game/basic): cast inequalities on `pgame` to `game` ([#14405](https://github.com/leanprover-community/mathlib/pull/14405))

### [2022-06-15 00:05:51](https://github.com/leanprover-community/mathlib/commit/bf2edb5)
feat(data/vector/basic): reflected instance for vectors ([#14669](https://github.com/leanprover-community/mathlib/pull/14669))
This means that a `vector` from a tactic block can be used in an expression.

### [2022-06-15 00:05:50](https://github.com/leanprover-community/mathlib/commit/b134b2f)
refactor(set_theory/game/state): rename `pgame.of` to `pgame.of_state` ([#14658](https://github.com/leanprover-community/mathlib/pull/14658))
This is so that we can redefine `pgame.of x y = {x | y}` in [#14659](https://github.com/leanprover-community/mathlib/pull/14659). Further, this is just a much clearer name.

### [2022-06-15 00:05:49](https://github.com/leanprover-community/mathlib/commit/7b2970f)
feat(set_theory/cardinal/basic): improve docs on `lift`, add `simp` lemmas ([#14596](https://github.com/leanprover-community/mathlib/pull/14596))
We add some much needed documentation to the `cardinal.lift` API.  We also mark a few extra lemmas with `simp`.

### [2022-06-15 00:05:48](https://github.com/leanprover-community/mathlib/commit/2e2d515)
feat(data/nat/factorization): add lemma `coprime_of_div_pow_factorization` ([#14576](https://github.com/leanprover-community/mathlib/pull/14576))
Add lemma `coprime_of_div_pow_factorization (hp : prime p) (hn : n ≠ 0) : coprime p (n / p ^ n.factorization p)`
Prompted by [this Zulip question](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/div.20by.20p_adic_val_nat.20is.20coprime).

### [2022-06-14 18:25:05](https://github.com/leanprover-community/mathlib/commit/16728b3)
feat(topology/homotopy/contractible): a few convenience lemmas ([#14710](https://github.com/leanprover-community/mathlib/pull/14710))
If `X` and `Y` are homotopy equivalent spaces, then one is
contractible if and only if the other one is contractible.

### [2022-06-14 18:25:02](https://github.com/leanprover-community/mathlib/commit/05aa960)
feat(analysis/special_functions/trigonometric/deriv): compare `sinh x` with `x` ([#14702](https://github.com/leanprover-community/mathlib/pull/14702))

### [2022-06-14 18:24:59](https://github.com/leanprover-community/mathlib/commit/d5c7260)
feat(order/monotone): add lemmas about `cmp` ([#14689](https://github.com/leanprover-community/mathlib/pull/14689))
Also replace `order_dual.cmp_le_flip` with lemmas about `to_dual` and `of_dual`.

### [2022-06-14 17:04:56](https://github.com/leanprover-community/mathlib/commit/6cdc30d)
golf(set_theory/ordinal/basic): golf theorems on `cardinal.ord` and `ordinal.card`  ([#14709](https://github.com/leanprover-community/mathlib/pull/14709))

### [2022-06-14 15:42:17](https://github.com/leanprover-community/mathlib/commit/ed033f3)
feat(linear_algebra/vandermonde): add lemmas about det equals zero ([#14695](https://github.com/leanprover-community/mathlib/pull/14695))
Adding two lemmas about when the determinant is zero.
I shortened the first with the help of some code I found in `ring_theory/trace.lean`, lemma `det_trace_matrix_ne_zero'`.

### [2022-06-14 15:42:15](https://github.com/leanprover-community/mathlib/commit/41eb958)
feat({tactic + test}/congrm, logic/basic): `congrm = congr + pattern-match` ([#14153](https://github.com/leanprover-community/mathlib/pull/14153))
This PR defines a tactic `congrm`.  If the goal is an equality, where the sides are "almost" equal, then calling `congrm <expr_with_mvars_for_differences>` will produce goals for each place where the given expression has metavariables and will try to close the goal assuming all equalities have been proven.
For instance,
```
example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  exact h,
end
```
works.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/variant.20syntax.20for.20.60congr'.60)

### [2022-06-14 13:35:08](https://github.com/leanprover-community/mathlib/commit/32d8fc4)
feat(topology/homeomorph): add `homeomorph.set.univ` ([#14730](https://github.com/leanprover-community/mathlib/pull/14730))

### [2022-06-14 13:35:07](https://github.com/leanprover-community/mathlib/commit/1c8f995)
feat(analysis/special_functions/exp): add `real.exp_half` ([#14729](https://github.com/leanprover-community/mathlib/pull/14729))

### [2022-06-14 13:35:06](https://github.com/leanprover-community/mathlib/commit/da5a737)
feat(data/complex/basic): ranges of `re`, `im`, `norm_sq`, and `abs` ([#14727](https://github.com/leanprover-community/mathlib/pull/14727))

### [2022-06-14 13:35:05](https://github.com/leanprover-community/mathlib/commit/b11f8e7)
refactor(algebra/order/group): unify instances ([#14705](https://github.com/leanprover-community/mathlib/pull/14705))
Drop `group.covariant_class_le.to_contravariant_class_le` etc in favor
of `group.covconv` (now an instance) and a new similar instance
`group.covconv_swap`.

### [2022-06-14 13:35:03](https://github.com/leanprover-community/mathlib/commit/2b46992)
feat(algebra/algebra/basic): define `alg_hom_class` and `non_unital_alg_hom_class` ([#14679](https://github.com/leanprover-community/mathlib/pull/14679))
This PR defines `alg_hom_class` and `non_unital_alg_hom_class` as part of the morphism refactor.

### [2022-06-14 13:35:02](https://github.com/leanprover-community/mathlib/commit/5d18a72)
feat(order/{conditionally_complete_lattice,galois_connection): Supremum of `set.image2` ([#14307](https://github.com/leanprover-community/mathlib/pull/14307))
`Sup` and `Inf` distribute over `set.image2` in the presence of appropriate Galois connections.

### [2022-06-14 13:35:01](https://github.com/leanprover-community/mathlib/commit/300c439)
feat(algebra/lie/weights): the zero root space is the Cartan subalgebra for a Noetherian Lie algebra ([#14174](https://github.com/leanprover-community/mathlib/pull/14174))

### [2022-06-14 11:24:09](https://github.com/leanprover-community/mathlib/commit/67dfb57)
feat(set_theory/cardinal/cofinality): lemma on subsets of strong limit cardinal ([#14442](https://github.com/leanprover-community/mathlib/pull/14442))

### [2022-06-14 01:31:50](https://github.com/leanprover-community/mathlib/commit/7fee0f1)
fix(data/list/nodup): change `Type` to `Type u` ([#14721](https://github.com/leanprover-community/mathlib/pull/14721))
Change `Type` to `Type u` in `nodup_iff_nth_ne_nth` and two other lemmas added in [#14371](https://github.com/leanprover-community/mathlib/pull/14371).

### [2022-06-14 01:31:49](https://github.com/leanprover-community/mathlib/commit/659983c)
feat(logic/equiv/basic): add `Pi_comm` aka `function.swap` as an `equiv` ([#14561](https://github.com/leanprover-community/mathlib/pull/14561))

### [2022-06-14 01:31:48](https://github.com/leanprover-community/mathlib/commit/18bf7af)
refactor(algebra/order/monoid): Split field of `canonically_ordered_...` ([#14556](https://github.com/leanprover-community/mathlib/pull/14556))
Replace
```
(le_iff_exists_add : ∀ a b : α, a ≤ b ↔ ∃ c, b = a + c)
```
by
```
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c)
(le_self_add : ∀ a b : α, a ≤ a + b)
```
This makes our life easier because
* We can use existing `has_exists_add_of_le` instances to complete the `exists_add_of_le` field, and detect the missing ones.
* No need to substitute `b = a + c` every time.

### [2022-06-13 23:08:36](https://github.com/leanprover-community/mathlib/commit/2967fae)
refactor(data/option/defs): Swap arguments to `option.elim` ([#14681](https://github.com/leanprover-community/mathlib/pull/14681))
Make `option.elim` a non-dependent version of `option.rec` rather than a non-dependent version of `option.rec_on`. Same for `option.melim`.
This replaces `option.cons`, and brings `option.elim` in line with `nat.elim`, `sum.elim`, and `iff.elim`.
It addresses the TODO comment added in 22c4291217925c6957c0f5a44551c9917b56c7cf.

### [2022-06-13 21:43:10](https://github.com/leanprover-community/mathlib/commit/425dfe7)
feat(set_theory/game/ordinal): golf `to_pgame_birthday` ([#14662](https://github.com/leanprover-community/mathlib/pull/14662))

### [2022-06-13 19:21:13](https://github.com/leanprover-community/mathlib/commit/3afafe6)
doc(ring_theory/algebraic): clarify docstring ([#14715](https://github.com/leanprover-community/mathlib/pull/14715))

### [2022-06-13 19:21:12](https://github.com/leanprover-community/mathlib/commit/b44e742)
feat(category_theory/limits): realise products as pullbacks ([#14322](https://github.com/leanprover-community/mathlib/pull/14322))
This was mostly done in [#10581](https://github.com/leanprover-community/mathlib/pull/10581), this just adds the isomorphisms between the objects produced by the `has_limit` API.

### [2022-06-13 19:21:11](https://github.com/leanprover-community/mathlib/commit/a75460f)
feat(algebra/module/pid): Classification of finitely generated torsion modules over a PID ([#13524](https://github.com/leanprover-community/mathlib/pull/13524))
A finitely generated torsion module over a PID is isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
(TODO : This part should be generalisable to a Dedekind domain, see https://en.wikipedia.org/wiki/Dedekind_domain#Finitely_generated_modules_over_a_Dedekind_domain . Part of the proof is already generalised).
More generally, a finitely generated module over a PID is isomorphic to the product of a free module and a direct sum of some
`R ⧸ R ∙ (p i ^ e i)`.
(TODO : prove this decomposition is unique.)
(TODO : deduce the structure theorem for finite(ly generated) abelian groups).
- [x] depends on: [#13414](https://github.com/leanprover-community/mathlib/pull/13414)
- [x] depends on: [#14376](https://github.com/leanprover-community/mathlib/pull/14376) 
- [x] depends on: [#14573](https://github.com/leanprover-community/mathlib/pull/14573)

### [2022-06-13 17:42:16](https://github.com/leanprover-community/mathlib/commit/3225926)
feat(category_theory/monoidal): monoidal functors `Type ⥤  C` acting on powers ([#14330](https://github.com/leanprover-community/mathlib/pull/14330))

### [2022-06-13 16:22:21](https://github.com/leanprover-community/mathlib/commit/6ad2799)
chore(analysis/locally_convex/weak_dual): golf using `seminorm.comp` ([#14699](https://github.com/leanprover-community/mathlib/pull/14699))

### [2022-06-13 15:38:03](https://github.com/leanprover-community/mathlib/commit/aae786c)
feat(data/zmod/basic): fix a diamond in comm_ring and field ([#14712](https://github.com/leanprover-community/mathlib/pull/14712))
Before this change the following diamond existed:
```lean
import data.zmod.basic
variables {p : ℕ} [fact p.prime]
example :
  @euclidean_domain.to_comm_ring _ (@field.to_euclidean_domain _ (zmod.field p)) = zmod.comm_ring p :=
rfl
```
as the eta-expanded `zmod.comm_ring` was not defeq to itself, as it is defined via cases.
We fix this by instead defining each field by cases, which looks worse but at least seems to resolve the issue.
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/zmod.20comm_ring.20field.20diamond/near/285847071 for discussion

### [2022-06-13 14:24:16](https://github.com/leanprover-community/mathlib/commit/aed7f9a)
feat(topology/uniform_space/basic): add three easy lemmas about `uniform_space.comap` ([#14678](https://github.com/leanprover-community/mathlib/pull/14678))
These are uniform spaces versions of `filter.comap_inf`, `filter.comap_infi` and `filter.comap_mono`. I split them from [#14534](https://github.com/leanprover-community/mathlib/pull/14534) which is already a quite big PR.

### [2022-06-13 13:01:51](https://github.com/leanprover-community/mathlib/commit/b7b371e)
doc(field_theory/finite/trace): fix module docstring ([#14711](https://github.com/leanprover-community/mathlib/pull/14711))
This PR just fixes the docstring in `field_theory/finite/trace.lean`. It was still mentioning a definition that was removed.

### [2022-06-13 13:01:50](https://github.com/leanprover-community/mathlib/commit/46ac3cb)
chore(analysis/complex/upper_half_plane): move to a subdirectory ([#14704](https://github.com/leanprover-community/mathlib/pull/14704))
I'm going to add more files to `analysis/complex/upper_half_plane/` soon.

### [2022-06-13 11:39:13](https://github.com/leanprover-community/mathlib/commit/04019de)
chore(algebra/big_operators/associated,ring_theory/unique_factorization_domain): golf ([#14671](https://github.com/leanprover-community/mathlib/pull/14671))

### [2022-06-13 09:39:39](https://github.com/leanprover-community/mathlib/commit/b100037)
refactor(order/conditionally_complete_lattice): use `order_bot` ([#14568](https://github.com/leanprover-community/mathlib/pull/14568))
Use `order_bot` instead of an explicit `c = ⊥` argument in
`well_founded.conditionally_complete_linear_order_with_bot`. Also
reuse `linear_order.to_lattice` and add `well_founded.min_le`.

### [2022-06-13 09:39:38](https://github.com/leanprover-community/mathlib/commit/4b67645)
chore(algebra/ring_quot): provide an explicit npow field ([#14349](https://github.com/leanprover-community/mathlib/pull/14349))
While this probably shouldn't matter since `ring_quot` is irreducible, this matches what we do for `nsmul` and `zsmul`.

### [2022-06-13 08:58:22](https://github.com/leanprover-community/mathlib/commit/716824d)
feat(set_theory/surreal/dyadic): tweak API + golf ([#14649](https://github.com/leanprover-community/mathlib/pull/14649))
This PR does the following changes:
- Get rid of `pgame.half`, as it's def-eq to `pow_half 1`, which has strictly more API.
- Fix the docstring on `pow_half`, which incorrectly stated `pow_half 0 = 0`.
- Remove `simp` from some type equality lemmas.
- Remove the redundant theorems `pow_half_move_left'` and `pow_half_move_right'`.
- Add instances for left and right moves of `pow_half`. 
- Rename `zero_lt_pow_half` to `pow_half_pos`.
- Prove `pow_half_le_one` and `pow_half_succ_lt_one`.
- Make arguments explicit throughout.
- Golf proofs throughout.

### [2022-06-13 03:45:17](https://github.com/leanprover-community/mathlib/commit/dc9eab6)
feat(tactic/lift): generalize pi.can_lift to Sort ([#14700](https://github.com/leanprover-community/mathlib/pull/14700))

### [2022-06-12 20:34:14](https://github.com/leanprover-community/mathlib/commit/8fb92bf)
feat(measure_theory/integral/circle_integral): add lemma `circle_map_nmem_ball` ([#14643](https://github.com/leanprover-community/mathlib/pull/14643))
The lemma `set.ne_of_mem_nmem` is unrelated except that both of these should be helpful for:
https://github.com/leanprover-community/mathlib/pull/13885

### [2022-06-12 16:53:57](https://github.com/leanprover-community/mathlib/commit/d6eb634)
feat(number_theory/legendre_symbol/auxiliary, *): add/move lemmas in/to various files, delete `auxiliary.lean` ([#14572](https://github.com/leanprover-community/mathlib/pull/14572))
This is the first PR in a series that will culminate in providing the proof of Quadratic Reciprocity using Gauss sums.
Here we just add some lemmas to the file `auxiliary.lean` that will be used in new code later.
We also generalize the lemmas `neg_one_ne_one_of_char_ne_two` and `neg_ne_self_of_char_ne_two` from finite fields to more general rings.
See [this Zulipt topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A/near/285053214) for more information.
**CHANGE OF PLAN:** Following the discussion on Zulip linked to above, the lemmas in `auxiliary.lean` are supposed to be moved to there proper places. I have added suggestions to each lemma or group of lemmas (or definitions) what the proper place could be (in some cases, there are alternatives). Please comment if you do not agree or to support one of the alternatives.

### [2022-06-12 16:03:11](https://github.com/leanprover-community/mathlib/commit/97c9ef8)
chore(measure_theory): use notation `measurable_set[m]` ([#14690](https://github.com/leanprover-community/mathlib/pull/14690))

### [2022-06-12 11:53:19](https://github.com/leanprover-community/mathlib/commit/8cad81a)
feat(data/{finset,set}/basic): More `insert` and `erase` lemmas ([#14675](https://github.com/leanprover-community/mathlib/pull/14675))
Also turn `finset.disjoint_iff_disjoint_coe` around and change `set.finite.to_finset_insert` take `(insert a s).finite` instead of `s.finite`.

### [2022-06-12 11:13:54](https://github.com/leanprover-community/mathlib/commit/579d6f9)
feat(data/polynomial/laurent): Laurent polynomials are a localization of polynomials ([#14489](https://github.com/leanprover-community/mathlib/pull/14489))
This PR proves the lemma `is_localization (submonoid.closure ({X} : set R[X])) R[T;T⁻¹]`.

### [2022-06-12 08:43:37](https://github.com/leanprover-community/mathlib/commit/4a3b22e)
feat(number_theory/bernoulli_polynomials): Derivative of Bernoulli polynomial ([#14625](https://github.com/leanprover-community/mathlib/pull/14625))
Add the statement that the derivative of `bernoulli k x` is `k * bernoulli (k-1) x`. This will be used in a subsequent PR to evaluate the even positive integer values of the Riemann zeta function.

### [2022-06-12 05:48:33](https://github.com/leanprover-community/mathlib/commit/0926f07)
feat(data/polynomial/eval): add some lemmas for `comp` ([#14346](https://github.com/leanprover-community/mathlib/pull/14346))

### [2022-06-12 05:09:43](https://github.com/leanprover-community/mathlib/commit/eb063e7)
feat(category_theory/Fintype): equiv_equiv_iso ([#13984](https://github.com/leanprover-community/mathlib/pull/13984))
From LTE.

### [2022-06-11 15:30:23](https://github.com/leanprover-community/mathlib/commit/053a03d)
feat(algebra/char_p): `char_p` of a local ring is zero or prime power ([#14461](https://github.com/leanprover-community/mathlib/pull/14461))
For a local commutative ring the characteristics is either zero or a prime power.

### [2022-06-11 14:33:12](https://github.com/leanprover-community/mathlib/commit/2e3a0a6)
feat(analysis/special_functions/log): add `real.log_sqrt` ([#14663](https://github.com/leanprover-community/mathlib/pull/14663))

### [2022-06-11 11:06:30](https://github.com/leanprover-community/mathlib/commit/d1a6dd2)
feat(topology/algebra/module/locally_convex): local convexity is preserved by `Inf` and `induced` ([#12118](https://github.com/leanprover-community/mathlib/pull/12118))
I also generalized slightly `locally_convex_space.of_bases` and changed a `Sort*` to `Type*` in `filter.has_basis_infi` to correctly reflect the universe constraints.

### [2022-06-11 08:59:36](https://github.com/leanprover-community/mathlib/commit/13b999c)
feat(algebra/{group,hom}/units): Units in division monoids ([#14212](https://github.com/leanprover-community/mathlib/pull/14212))
Copy over `group_with_zero` lemmas to the more general setting of `division_monoid`.

### [2022-06-11 02:10:15](https://github.com/leanprover-community/mathlib/commit/050404a)
feat(group_theory/sylow): Sylow subgroups are Hall subgroups ([#14624](https://github.com/leanprover-community/mathlib/pull/14624))
This PR adds a lemma stating that Sylow subgroups are Hall subgroups (cardinality is coprime to index).

### [2022-06-10 14:50:29](https://github.com/leanprover-community/mathlib/commit/18936e5)
feat(topology/uniform_space/equiv): define uniform isomorphisms ([#14537](https://github.com/leanprover-community/mathlib/pull/14537))
This adds a new file, mostly copy-pasted from `topology/homeomorph`, to analogously define uniform isomorphisms

### [2022-06-10 12:55:31](https://github.com/leanprover-community/mathlib/commit/8c812fd)
feat(topology/algebra/order): `coe : ℚ → 𝕜` has dense range ([#14635](https://github.com/leanprover-community/mathlib/pull/14635))
* add `rat.dense_range_cast`, use it in `rat.dense_embedding_coe_real`;
* rename `dense_iff_forall_lt_exists_mem` to `dense_iff_exists_between`;
* add `dense_of_exists_between`, use it in `dense_iff_exists_between`.

### [2022-06-10 12:55:30](https://github.com/leanprover-community/mathlib/commit/0f5a1f2)
feat(data/rat): Add some lemmas to work with num/denom ([#14456](https://github.com/leanprover-community/mathlib/pull/14456))

### [2022-06-10 10:43:10](https://github.com/leanprover-community/mathlib/commit/95da649)
feat(analysis/inner_product_space): Generalize Gram-Schmidt ([#14379](https://github.com/leanprover-community/mathlib/pull/14379))
The generalisation is to allow a family of vectors indexed by a general indexing set `ι` (carrying appropriate order typeclasses) rather than just `ℕ`.

### [2022-06-10 10:04:50](https://github.com/leanprover-community/mathlib/commit/391d178)
feat(set_theory/game/ordinal): golf `to_pgame_injective` ([#14661](https://github.com/leanprover-community/mathlib/pull/14661))
We also add the `eq_iff` version and remove an outdated todo comment.

### [2022-06-10 10:04:49](https://github.com/leanprover-community/mathlib/commit/68dc07f)
refactor(set_theory/game/pgame): rename and add theorems like `-y ≤ -x ↔ x ≤ y` ([#14653](https://github.com/leanprover-community/mathlib/pull/14653))
For `*` in `le`, `lf`, `lt`, we rename `neg_*_iff : -y * -x ↔ x * y` to `neg_*_neg_iff`, and add the theorems `neg_*_iff : -y * x ↔ x * -y`.
We further add many missing corresponding theorems for equivalence and fuzziness.

### [2022-06-10 07:36:57](https://github.com/leanprover-community/mathlib/commit/a912392)
feat(data/fintype/basic): add `card_subtype_mono` ([#14645](https://github.com/leanprover-community/mathlib/pull/14645))
This lemma naturally forms a counterpart to existing lemmas.
I've also renamed a lemma it uses that didn't seem to fit the existing naming pattern.

### [2022-06-10 07:36:56](https://github.com/leanprover-community/mathlib/commit/771f2b7)
chore(topology/metric_space/basic): add `metric_space.replace_bornology` ([#14638](https://github.com/leanprover-community/mathlib/pull/14638))
We have the `pseudo_metric_space` version from [#13927](https://github.com/leanprover-community/mathlib/pull/13927), but not the `metric_space` version.

### [2022-06-10 07:36:55](https://github.com/leanprover-community/mathlib/commit/5bccb51)
refactor(logic/equiv/basic): tweak lemmas on equivalences between `unique` types ([#14605](https://github.com/leanprover-community/mathlib/pull/14605))
This PR does various simple and highly related things:
- Rename `equiv_of_unique_of_unique` to `equiv_of_unique` and make its arguments explicit, in order to match the lemma `equiv_of_empty` added in [#14604](https://github.com/leanprover-community/mathlib/pull/14604).  
- Rename `equiv_punit_of_unique` to `equiv_punit` and make its argument explicit to match `equiv_pempty`.
- Fix their docstrings (which talked about a `subsingleton` type instead of a `unique` one).
- Move them much earlier in the file, together with the lemmas on empty types.
- Golf `prop_equiv_punit`.

### [2022-06-10 07:36:53](https://github.com/leanprover-community/mathlib/commit/7691821)
feat(data/polynomial/derivative): reduce assumptions ([#14338](https://github.com/leanprover-community/mathlib/pull/14338))
The only changes here are to relax typeclass assumptions.
Specifically these changes relax `comm_semiring` to `semiring` in:
 * polynomial.derivative_eval
 * polynomial.derivative_map
 * polynomial.iterate_derivative_map
 * polynomial.iterate_derivative_cast_nat_mul
and relax `ring` to `semiring` as well as `char_zero` + `no_zero_divisors` to `no_zero_smul_divisors ℕ` in:
 * polynomial.mem_support_derivative
 * polynomial.degree_derivative_eq

### [2022-06-10 07:36:52](https://github.com/leanprover-community/mathlib/commit/39184f4)
feat(dynamics/periodic_pts): Orbit under periodic function ([#12976](https://github.com/leanprover-community/mathlib/pull/12976))

### [2022-06-10 05:26:20](https://github.com/leanprover-community/mathlib/commit/e3dade3)
feat(data/finite/basic): `finite` predicate ([#14373](https://github.com/leanprover-community/mathlib/pull/14373))
Introduces a `Prop`-valued finiteness predicate on types and adapts some subset of the `fintype` API to get started. Uses `nat.card` as the primary cardinality function.

### [2022-06-10 04:32:43](https://github.com/leanprover-community/mathlib/commit/e9d2564)
chore(measure_theory): golf ([#14657](https://github.com/leanprover-community/mathlib/pull/14657))
Also use `@measurable_set α m s` instead of `m.measurable_set' s` in the definition of the partial order on `measurable_space`. This way we can use dot notation lemmas about measurable sets in a proof of `m₁ ≤ m₂`.

### [2022-06-10 02:04:07](https://github.com/leanprover-community/mathlib/commit/ed2cfce)
feat(set_theory/ordinal/basic): tweak theorems on order type of empty relation ([#14650](https://github.com/leanprover-community/mathlib/pull/14650))
We move the theorems on the order type of an empty relation much earlier, and golf them. We also remove other redundant theorems.
`zero_eq_type_empty` is made redundant by `type_eq_zero_of_empty`, while `zero_eq_lift_type_empty`  is made redundant by the former lemma and `lift_zero`.

### [2022-06-09 23:59:52](https://github.com/leanprover-community/mathlib/commit/2cf4746)
chore(analysis/special_functions/gamma): tidy some proofs ([#14615](https://github.com/leanprover-community/mathlib/pull/14615))

### [2022-06-09 23:59:51](https://github.com/leanprover-community/mathlib/commit/3afb1fa)
feat(ci): Add support for "notice"-level messages ([#14443](https://github.com/leanprover-community/mathlib/pull/14443))
It looks like support for this was added recently, it's now documented at the same link already in our source code.

### [2022-06-09 22:24:53](https://github.com/leanprover-community/mathlib/commit/6e13617)
feat(set_theory/ordinal/basic): better definitions for `0` and `1` ([#14651](https://github.com/leanprover-community/mathlib/pull/14651))
We define the `0` and `1` ordinals as the order types of the empty relation on `pempty` and `punit`, respectively. These definitions are definitionally equal to the previous ones, yet much clearer, for two reasons:
- They don't make use of the auxiliary `Well_order` type. 
- Much of the basic API for these ordinals uses this def-eq anyways.

### [2022-06-09 22:24:52](https://github.com/leanprover-community/mathlib/commit/c89d319)
feat(set_theory/cardinal): add `cardinal.aleph_0_le_mul_iff'` ([#14648](https://github.com/leanprover-community/mathlib/pull/14648))
This version provides a more useful `iff.mpr`. Also review 2 proofs.

### [2022-06-09 22:24:51](https://github.com/leanprover-community/mathlib/commit/405be36)
feat(data/matrix): Lemmas about `vec_mul`, `mul_vec`, `dot_product`, `inv` ([#14644](https://github.com/leanprover-community/mathlib/pull/14644))

### [2022-06-09 22:24:50](https://github.com/leanprover-community/mathlib/commit/3e458e2)
chore(topology/sequences): rename variables ([#14631](https://github.com/leanprover-community/mathlib/pull/14631))
* types `X`, `Y`;
* sequence `x : ℕ → X`;
* a point `a : X`;
* sets `s`, `t`.

### [2022-06-09 19:45:28](https://github.com/leanprover-community/mathlib/commit/81ab992)
chore(set_theory/cardinal/basic): tidy lt_wf proof ([#14574](https://github.com/leanprover-community/mathlib/pull/14574))

### [2022-06-09 19:45:27](https://github.com/leanprover-community/mathlib/commit/34a9d0d)
feat(algebra/order/ring): Binary rearrangement inequality ([#14478](https://github.com/leanprover-community/mathlib/pull/14478))
Extract the binary case of the rearrangement inequality (`a * d + b * c ≤ a * c + b * d` if `a ≤ b` and `c ≤ d`) from the general one.

### [2022-06-09 19:45:25](https://github.com/leanprover-community/mathlib/commit/7fbff0f)
feat(data/nat/choose/central): arity of primes in central binomial coefficients ([#14017](https://github.com/leanprover-community/mathlib/pull/14017))
Spun off of [#8002](https://github.com/leanprover-community/mathlib/pull/8002). Lemmas about the arity of primes in central binomial coefficients.

### [2022-06-09 18:12:47](https://github.com/leanprover-community/mathlib/commit/4d4de43)
chore(ring_theory/unique_factorization_domain): drop simp annotation for factors_pow ([#14646](https://github.com/leanprover-community/mathlib/pull/14646))
Followup to https://github.com/leanprover-community/mathlib/pull/14555.

### [2022-06-09 18:12:46](https://github.com/leanprover-community/mathlib/commit/7b4680f)
feat(analysis/inner_product_space/pi_L2): Distance formula in the euclidean space ([#14642](https://github.com/leanprover-community/mathlib/pull/14642))
A few missing results about `pi_Lp 2` and `euclidean_space`.

### [2022-06-09 18:12:45](https://github.com/leanprover-community/mathlib/commit/ac0ce64)
feat(special_functions/integrals): exponential of complex multiple of x ([#14623](https://github.com/leanprover-community/mathlib/pull/14623))
We add an integral for `exp (c * x)` for `c` complex (so this cannot be reduced to integration of `exp x` on the real line). This is useful for Fourier series.

### [2022-06-09 15:38:27](https://github.com/leanprover-community/mathlib/commit/abee649)
feat(data/set/intervals): add lemmas about unions of intervals ([#14636](https://github.com/leanprover-community/mathlib/pull/14636))

### [2022-06-09 15:38:26](https://github.com/leanprover-community/mathlib/commit/e0f3ea3)
feat(topology/constructions): add `subtype.dense_iff` ([#14632](https://github.com/leanprover-community/mathlib/pull/14632))
Also add `inducing.dense_iff`.

### [2022-06-09 15:38:25](https://github.com/leanprover-community/mathlib/commit/48f557d)
chore(analysis/convex/integral): use `variables` ([#14592](https://github.com/leanprover-community/mathlib/pull/14592))
* Move some implicit arguments to `variables`.
* Move `ae_eq_const_or_exists_average_ne_compl` to the root namespace.
* Add `ae_eq_const_or_norm_set_integral_lt_of_norm_le_const`.

### [2022-06-09 13:27:25](https://github.com/leanprover-community/mathlib/commit/c0b3ed7)
feat(number_theory/padics/padic_val): add `padic_val_nat_def'` and generalise `pow_padic_val_nat_dvd` ([#14637](https://github.com/leanprover-community/mathlib/pull/14637))
add `padic_val_nat_def' (hn : 0 < n) (hp : p ≠ 1) : ↑(padic_val_nat p n) = multiplicity p n`
`pow_padic_val_nat_dvd : p ^ (padic_val_nat p n) ∣ n` holds without the assumption that `p` is prime.

### [2022-06-09 13:27:23](https://github.com/leanprover-community/mathlib/commit/dc766dd)
refactor(group_theory/sylow): Golf proof of `pow_dvd_card_of_pow_dvd_card` ([#14622](https://github.com/leanprover-community/mathlib/pull/14622))
This PR golfs the proof of `pow_dvd_card_of_pow_dvd_card`.

### [2022-06-09 13:27:22](https://github.com/leanprover-community/mathlib/commit/cde6e63)
feat(analysis/seminorm): removed unnecessary `norm_one_class` arguments ([#14614](https://github.com/leanprover-community/mathlib/pull/14614))

### [2022-06-09 13:27:21](https://github.com/leanprover-community/mathlib/commit/d997baa)
refactor(logic/equiv/basic): remove `fin_equiv_subtype` ([#14603](https://github.com/leanprover-community/mathlib/pull/14603))
The types `fin n` and `{m // m < n}` are definitionally equal, so it doesn't make sense to have a dedicated equivalence between them (other than `equiv.refl`). We remove this equivalence and golf the places where it was used.

### [2022-06-09 13:27:20](https://github.com/leanprover-community/mathlib/commit/c2bb59e)
feat(algebra/module/torsion.lean): various lemmas about torsion modules ([#14573](https://github.com/leanprover-community/mathlib/pull/14573))
An intermediate PR for various lemmas about torsion modules needed at [#13524](https://github.com/leanprover-community/mathlib/pull/13524)

### [2022-06-09 13:27:19](https://github.com/leanprover-community/mathlib/commit/dfc54a3)
feat(combinatorics/ballot): the Ballot problem ([#13592](https://github.com/leanprover-community/mathlib/pull/13592))

### [2022-06-09 11:44:36](https://github.com/leanprover-community/mathlib/commit/d51aacb)
feat(ring_theory/unique_factorization_domain): add some lemmas about … ([#14555](https://github.com/leanprover-community/mathlib/pull/14555))

### [2022-06-09 09:58:31](https://github.com/leanprover-community/mathlib/commit/dc2f6bb)
chore(topology/metric_space): remove instances that duplicate lemmas ([#14639](https://github.com/leanprover-community/mathlib/pull/14639))
We can use the structure projections directly as instances, rather than duplicating them with primed names. This removes;
* `metric_space.to_uniform_space'` (was misnamed, now `pseudo_metric_space.to_uniform_space`)
* `pseudo_metric_space.to_bornology'` (now `pseudo_metric_space.to_bornology`)
* `pseudo_emetric_space.to_uniform_space'` (now `pseudo_metric_space.to_uniform_space`)
* `emetric_space.to_uniform_space'` (redundant)
Follows up from review comments in [#13927](https://github.com/leanprover-community/mathlib/pull/13927)

### [2022-06-09 09:58:30](https://github.com/leanprover-community/mathlib/commit/bc7b342)
feat(topology/metric_space/basic): add lemma `exists_lt_mem_ball_of_mem_ball` ([#14627](https://github.com/leanprover-community/mathlib/pull/14627))
This is apparently necessary in https://github.com/leanprover-community/mathlib/pull/13885

### [2022-06-09 09:58:29](https://github.com/leanprover-community/mathlib/commit/6a1ce4e)
feat(analysis/seminorm): add a `zero_hom_class` instance and remove `seminorm.zero` ([#14613](https://github.com/leanprover-community/mathlib/pull/14613))

### [2022-06-09 09:58:28](https://github.com/leanprover-community/mathlib/commit/6826bf0)
doc(data/vector3): improve wording ([#14610](https://github.com/leanprover-community/mathlib/pull/14610))

### [2022-06-09 09:58:27](https://github.com/leanprover-community/mathlib/commit/ab64f63)
refactor(algebra/sub{monoid,group,ring,semiring,field}): merge together the `restrict` and `cod_restrict` helpers ([#14548](https://github.com/leanprover-community/mathlib/pull/14548))
This uses the new subobject typeclasses to merge together:
* `monoid_hom.mrestrict`, `monoid_hom.restrict`
* `monoid_hom.cod_mrestrict`, `monoid_hom.cod_restrict`
* `ring_hom.srestrict`, `ring_hom.restrict`, `ring_hom.restrict_field`
* `ring_hom.cod_srestrict`, `ring_hom.cod_restrict`, `ring_hom.cod_restrict_field`
For consistency, this also removes the `m` prefix from `mul_hom.mrestrict`

### [2022-06-09 09:58:26](https://github.com/leanprover-community/mathlib/commit/732b79f)
feat(order/compactly_generated): an independent subset of a well-founded complete lattice is finite ([#14215](https://github.com/leanprover-community/mathlib/pull/14215))

### [2022-06-09 07:52:18](https://github.com/leanprover-community/mathlib/commit/3a95d1d)
feat(algebra/order/monoid): `zero_le_one_class` instances for `with_top` and `with_bot` ([#14640](https://github.com/leanprover-community/mathlib/pull/14640))

### [2022-06-09 05:43:16](https://github.com/leanprover-community/mathlib/commit/971a9b0)
feat(logic/equiv/basic): two empty types are equivalent; remove various redundant lemmas ([#14604](https://github.com/leanprover-community/mathlib/pull/14604))
We prove `equiv_of_is_empty`, which states two empty types are equivalent. This allows us to remove various redundant lemmas.
We keep `empty_equiv_empty` and `empty_equiv_pempty` as these specific instantiations of that lemma are widely used.

### [2022-06-09 04:07:37](https://github.com/leanprover-community/mathlib/commit/9f19686)
feat(logic/small): generalize + golf ([#14584](https://github.com/leanprover-community/mathlib/pull/14584))
This PR does the following:
- add a lemma `small_lift`
- generalize the lemma `small_ulift`
- golf `small_self` and `small_max`

### [2022-06-09 01:54:18](https://github.com/leanprover-community/mathlib/commit/b392bb2)
feat(data/nat/factorization/basic): two trivial simp lemmas about factorizations ([#14634](https://github.com/leanprover-community/mathlib/pull/14634))
For any `n : ℕ`, `n.factorization 0 = 0` and `n.factorization 1 = 0`

### [2022-06-09 01:54:16](https://github.com/leanprover-community/mathlib/commit/4fc3539)
refactor(data/finset/nat_antidiagonal): state lemmas with cons instead of insert ([#14533](https://github.com/leanprover-community/mathlib/pull/14533))
This puts less of a burden on the caller rewriting in the forward direction, as they don't have to prove obvious things about membership when evaluating sums.
Since this adds the missing `finset.map_cons`, a number of uses of `multiset.map_cons` now need qualified names.

### [2022-06-08 23:44:35](https://github.com/leanprover-community/mathlib/commit/0c08bd4)
chore(data/set/basic): minor style fixes ([#14628](https://github.com/leanprover-community/mathlib/pull/14628))

### [2022-06-08 20:36:43](https://github.com/leanprover-community/mathlib/commit/c1faa2e)
feat(linear_algebra/affine_space/affine_subspace/pointwise): Translations are an action on affine subspaces ([#14230](https://github.com/leanprover-community/mathlib/pull/14230))

### [2022-06-08 20:36:42](https://github.com/leanprover-community/mathlib/commit/84a1bd6)
refactor(topology/metric_space/basic): add `pseudo_metric_space.to_bornology'` ([#13927](https://github.com/leanprover-community/mathlib/pull/13927))
* add `pseudo_metric_space.to_bornology'` and `pseudo_metric_space.replace_bornology`;
* add `metric.is_bounded_iff` and a few similar lemmas;
* fix instances for `subtype`, `prod`, `pi`, and `pi_Lp` to use the correct bornology`;
* add `lipschitz_with.to_locally_bounded_map` and `lipschitz_with.comap_cobounded_le`;
* add `antilipschitz_with.tendsto_cobounded`.

### [2022-06-08 18:51:48](https://github.com/leanprover-community/mathlib/commit/61df9c6)
feat(set_theory/ordinal/basic): tweak `type_def` + golf `type_lt` ([#14611](https://github.com/leanprover-community/mathlib/pull/14611))
We replace the original, redundant `type_def'` with a new more general lemma. We keep `type_def` as it enables `dsimp`, unlike `type_def'`. We golf `type_lt` using this new lemma.

### [2022-06-08 18:51:32](https://github.com/leanprover-community/mathlib/commit/9c4a3d1)
feat(ring_theory/valuation/valuation_subring): define unit group of valuation subring and provide basic API ([#14540](https://github.com/leanprover-community/mathlib/pull/14540))
This PR defines the unit group of a valuation subring as a multiplicative subgroup of the units of the field. We show two valuation subrings are equivalent iff they have the same unit group. We show the map sending a valuation to its unit group is an order embedding.

### [2022-06-08 18:10:02](https://github.com/leanprover-community/mathlib/commit/d315666)
feat(model_theory/substructures): tweak universes for `lift_card_closure_le` ([#14597](https://github.com/leanprover-community/mathlib/pull/14597))
Since `cardinal.lift.{(max u v) u} = cardinal.lift.{v u}`, the latter form should be preferred.

### [2022-06-08 15:58:47](https://github.com/leanprover-community/mathlib/commit/8934884)
feat(set_theory/ordinal/basic): `rel_iso.ordinal_type_eq` ([#14602](https://github.com/leanprover-community/mathlib/pull/14602))

### [2022-06-08 15:58:46](https://github.com/leanprover-community/mathlib/commit/09df85f)
feat(order/rel_classes): any relation on an empty type is a well-order ([#14600](https://github.com/leanprover-community/mathlib/pull/14600))

### [2022-06-08 15:58:45](https://github.com/leanprover-community/mathlib/commit/201a3f4)
chore(*): remove extra parentheses in universe annotations ([#14595](https://github.com/leanprover-community/mathlib/pull/14595))
We change `f.{(max u v)}` to `f.{max u v}` throughout, and similarly for `imax`. This is for consistency with the rest of the code.
Note that `max` and `imax` take an arbitrary number of parameters, so if anyone wants to add a second universe parameter, they'll have to add the parentheses again.

### [2022-06-08 15:58:43](https://github.com/leanprover-community/mathlib/commit/3e4d6aa)
feat(algebra/algebra/basic): add instances `char_zero.no_zero_smul_divisors_int`, `char_zero.no_zero_smul_divisors_nat` ([#14395](https://github.com/leanprover-community/mathlib/pull/14395))
The proofs are taken from [#14338](https://github.com/leanprover-community/mathlib/pull/14338) where a specific need for these arose
Aside from the new instances, nothing else has changed; I moved the
`no_zero_smul_divisors` section lower down in the file since the new
instances need the `algebra ℤ R` structure carried by a ring `R`.

### [2022-06-08 13:42:41](https://github.com/leanprover-community/mathlib/commit/bfb8ec8)
feat(logic/basic): add lemma `pi_congr` ([#14616](https://github.com/leanprover-community/mathlib/pull/14616))
This lemma is used in [#14153](https://github.com/leanprover-community/mathlib/pull/14153), where `congrm` is defined.
A big reason for splitting these 3 lines off the main PR is that they are the only ones that are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.

### [2022-06-08 13:42:38](https://github.com/leanprover-community/mathlib/commit/700181a)
refactor(algebra/is_prime_pow): move lemmas using `factorization` to new file ([#14598](https://github.com/leanprover-community/mathlib/pull/14598))
As discussed in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization/near/285144241).

### [2022-06-08 12:10:16](https://github.com/leanprover-community/mathlib/commit/db4531f)
doc(data/qpf/multivariate/constructions/cofix): fix doc typos ([#14609](https://github.com/leanprover-community/mathlib/pull/14609))

### [2022-06-08 12:10:15](https://github.com/leanprover-community/mathlib/commit/0add876)
chore(set_theory/cardinal/basic): remove unused universe + fix spacing ([#14606](https://github.com/leanprover-community/mathlib/pull/14606))

### [2022-06-08 12:10:14](https://github.com/leanprover-community/mathlib/commit/65fba4c)
feat(algebra/lie/centralizer): define the centralizer of a Lie submodule and the upper central series ([#14173](https://github.com/leanprover-community/mathlib/pull/14173))

### [2022-06-08 09:31:34](https://github.com/leanprover-community/mathlib/commit/ffad43d)
golf(*): `λ _, default` → `default` ([#14608](https://github.com/leanprover-community/mathlib/pull/14608))

### [2022-06-08 09:31:33](https://github.com/leanprover-community/mathlib/commit/60454dd)
feat(algebra/order/monoid): `zero_le_one'` lemma with explicit type argument ([#14594](https://github.com/leanprover-community/mathlib/pull/14594))

### [2022-06-08 09:31:32](https://github.com/leanprover-community/mathlib/commit/f40cd3c)
feat(topology/algebra/order/basic): in a second-countable linear order, only countably many points are isolated to the right ([#14564](https://github.com/leanprover-community/mathlib/pull/14564))
This makes it possible to remove a useless `densely_ordered` assumption in a lemma in `borel_space`.

### [2022-06-08 09:31:31](https://github.com/leanprover-community/mathlib/commit/a20032a)
feat(group_theory/sylow): The index of a sylow subgroup is indivisible by the prime ([#14518](https://github.com/leanprover-community/mathlib/pull/14518))
This PR adds a lemma stating that the index of a sylow subgroup is indivisible by the prime.

### [2022-06-08 09:31:30](https://github.com/leanprover-community/mathlib/commit/54236f5)
feat(topology/continuous_function/compact): `cstar_ring` instance on `C(α, β)` when `α` is compact ([#14437](https://github.com/leanprover-community/mathlib/pull/14437))
We define the star operation on `C(α, β)` by applying `β`'s star operation pointwise. In the case when `α` is compact, then `C(α, β)` has a norm, and we show that it is a `cstar_ring`.

### [2022-06-08 07:33:27](https://github.com/leanprover-community/mathlib/commit/e39af18)
chore(data/finset): remove duplicated lemma ([#14607](https://github.com/leanprover-community/mathlib/pull/14607))
The lemma `ssubset_iff_exists_insert_subset` was added in [#11248](https://github.com/leanprover-community/mathlib/pull/11248) but is just a duplicate of the `ssubset_iff` lemma a few lines earlier in the file. It's only used once.

### [2022-06-08 00:23:16](https://github.com/leanprover-community/mathlib/commit/9d04844)
feat(data/int/basic): Sum of units casework lemma ([#14557](https://github.com/leanprover-community/mathlib/pull/14557))
This PR adds a casework lemma for when the sum of two units equals the sum of two units. I needed this lemma for irreducibility of x^n-x-1.

### [2022-06-07 22:31:45](https://github.com/leanprover-community/mathlib/commit/759516c)
chore(ring_theory/dedekind_domain/ideal): speed up a proof ([#14590](https://github.com/leanprover-community/mathlib/pull/14590))
... which causes recurring timeout at irrelevant places, see https://github.com/leanprover-community/mathlib/pull/14585#issuecomment-1148222373 and referenced Zulip discussion.
Feel free to push golfs that remains fast (1-2s)!

### [2022-06-07 21:09:01](https://github.com/leanprover-community/mathlib/commit/905374c)
feat(special_functions/gamma): better convergence bounds ([#14496](https://github.com/leanprover-community/mathlib/pull/14496))
Use the stronger form of FTC-2 added [#14147](https://github.com/leanprover-community/mathlib/pull/14147) to strengthen some results about the gamma function.

### [2022-06-07 17:43:24](https://github.com/leanprover-community/mathlib/commit/cfa447e)
chore(logic/hydra): tweak docs + minor golf ([#14579](https://github.com/leanprover-community/mathlib/pull/14579))

### [2022-06-07 13:32:20](https://github.com/leanprover-community/mathlib/commit/43f1af9)
refactor(topology/continuous_function/basic): rename `map_specialization` ([#14565](https://github.com/leanprover-community/mathlib/pull/14565))
Rename `continuous_map.map_specialization` to `continuous_map.map_specializes` to align with the name of the relation.

### [2022-06-07 12:37:21](https://github.com/leanprover-community/mathlib/commit/544fdc0)
chore(ring_theory/integral_closure): fix dot notation ([#14589](https://github.com/leanprover-community/mathlib/pull/14589))

### [2022-06-07 11:40:32](https://github.com/leanprover-community/mathlib/commit/6906627)
refactor(algebra/squarefree): split out `nat` part to new file `data/nat/squarefree` ([#14577](https://github.com/leanprover-community/mathlib/pull/14577))
As discussed in this Zulip [thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization)

### [2022-06-07 07:06:14](https://github.com/leanprover-community/mathlib/commit/4a4cd6d)
feat(topology/metric_space/metrizable): assume `regular_space` ([#14586](https://github.com/leanprover-community/mathlib/pull/14586))

### [2022-06-07 01:29:01](https://github.com/leanprover-community/mathlib/commit/de648fd)
chore(set_theory/game/basic): spacing tweaks + fix docstring typo ([#14580](https://github.com/leanprover-community/mathlib/pull/14580))

### [2022-06-06 22:44:27](https://github.com/leanprover-community/mathlib/commit/6ad1a55)
feat(set_theory/game/pgame): induction on left/right moves of add/mul ([#14345](https://github.com/leanprover-community/mathlib/pull/14345))

### [2022-06-06 20:46:31](https://github.com/leanprover-community/mathlib/commit/c7a1319)
feat(measure_theory/measure/measure_space): add `interval_oc_ae_eq_interval` ([#14566](https://github.com/leanprover-community/mathlib/pull/14566))

### [2022-06-06 20:46:30](https://github.com/leanprover-community/mathlib/commit/2c89306)
chore(geometry/manifold/charted_space): make `M` an explicit argument ([#14562](https://github.com/leanprover-community/mathlib/pull/14562))

### [2022-06-06 20:46:29](https://github.com/leanprover-community/mathlib/commit/d0b7ecc)
refactor(analysis/asymptotics): rename `is_O.join` to `is_O.sup` ([#14558](https://github.com/leanprover-community/mathlib/pull/14558))
* rename `is_*.join` to `is_*.sup`;
* add `iff` versions.

### [2022-06-06 20:46:28](https://github.com/leanprover-community/mathlib/commit/2b7e72b)
feat(order/liminf_limsup): add a few lemmas ([#14554](https://github.com/leanprover-community/mathlib/pull/14554))
* add `is_bounded_under.mono_le`, `is_bounded_under.mono_ge`;
* add `order_iso.is_bounded_under_le_comp`, `order_iso.is_bounded_under_ge_comp`;
* add `is_bounded_under_le_inv`, `is_bounded_under_le_inv`, and additive versions;
* rename `is_bounded_under_sup` and `is_bounded_under_inf` to `is_bounded_under.sup` and `is_bounded_under.inf`;
* add `iff` versions under names `is_bounded_under_le_sup` and `is_bounded_under_ge_inf`;
* add `is_bounded_under_le_abs`.

### [2022-06-06 20:46:27](https://github.com/leanprover-community/mathlib/commit/029a955)
refactor(../metric_space/baire): add baire_space class and instances ([#14547](https://github.com/leanprover-community/mathlib/pull/14547))
* Add a `baire_space` class containing the Baire property (a countable intersection of open dense sets is dense).
* The Baire category theorem for complete metric spaces becomes an instance of `baire_space`.
* Previous consequences of the Baire property use `baire_space` as an hypothesis, instead of `pseudo_emetric_space` `complete_space`.
* Add an instance of `baire_space` for locally compact t2 spaces, in effect extending all the consequences of the Baire property to locally compact spaces.

### [2022-06-06 20:46:26](https://github.com/leanprover-community/mathlib/commit/d28aa2c)
feat(analysis/normed_space/banach): closed graph theorem ([#14265](https://github.com/leanprover-community/mathlib/pull/14265))

### [2022-06-06 18:41:09](https://github.com/leanprover-community/mathlib/commit/7b7da89)
feat(algebra/order/*): typeclass for `0 ≤ 1` ([#14510](https://github.com/leanprover-community/mathlib/pull/14510))
With this new typeclass, lemmas such as `zero_le_two` and `one_le_two` can be generalized to require just a few typeclasses for notation, `zero_add_class`, and some `covariant` class.

### [2022-06-06 14:27:28](https://github.com/leanprover-community/mathlib/commit/abbc7f6)
feat(measure_theory/measure/finite_measure_weak_convergence): Prove one implication of portmanteau theorem, convergence implies a limsup condition for measures of closed sets. ([#14116](https://github.com/leanprover-community/mathlib/pull/14116))
This PR contains the proof of one implication of portmanteau theorem characterizing weak convergence: it is shown that weak convergence implies that for any closed set the limsup of measures is at most the limit measure.

### [2022-06-06 13:48:54](https://github.com/leanprover-community/mathlib/commit/d6477a8)
feat(analysis/convex/krein_milman): The Krein-Milman theorem ([#8112](https://github.com/leanprover-community/mathlib/pull/8112))
This PR proves the Krein-Milman lemma and the Krein-Milman theorem.

### [2022-06-06 12:19:21](https://github.com/leanprover-community/mathlib/commit/d490ad1)
move(set_theory/ordinal/cantor_normal_form): move `CNF` to a new file ([#14563](https://github.com/leanprover-community/mathlib/pull/14563))
We move the API for the Cantor Normal Form to a new file, in preparation for an API expansion.

### [2022-06-06 10:35:42](https://github.com/leanprover-community/mathlib/commit/0f5ea39)
feat(order/antichain, order/minimal): some antichain lemmas ([#14507](https://github.com/leanprover-community/mathlib/pull/14507))
This PR adds a few lemmas about antichains, including their images under complementation and order isomorphisms.

### [2022-06-06 09:16:32](https://github.com/leanprover-community/mathlib/commit/d88ecd5)
chore(linear_algebra/std_basis): minor golfs ([#14552](https://github.com/leanprover-community/mathlib/pull/14552))

### [2022-06-06 07:26:33](https://github.com/leanprover-community/mathlib/commit/789af09)
feat(algebra/char_p): add two helper lemmas about the cast of the characteristics being zero ([#14464](https://github.com/leanprover-community/mathlib/pull/14464))
- `(ring_char R : R) = 0` and
- If there exists a positive `n` lifting to zero, then the characteristics is positive.

### [2022-06-05 20:50:27](https://github.com/leanprover-community/mathlib/commit/769a934)
feat(set_theory/*) `cardinal.min` → `Inf` ([#13410](https://github.com/leanprover-community/mathlib/pull/13410))
We discard `cardinal.min` in favor of `Inf` (the original definition is really just `infi`). 
Note: `lift_min'` is renamed to `lift_min`, as the name clash no longer exists. For consistency, `lift_max'` is renamed to `lift_max` and `lift_max` is renamed to `lift_umax_eq`.

### [2022-06-05 19:28:46](https://github.com/leanprover-community/mathlib/commit/736b4e5)
feat(data/nat/factorization): Lemma on zero-ness of factorization ([#14560](https://github.com/leanprover-community/mathlib/pull/14560))
Sad naming is sad.
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)

### [2022-06-05 14:52:20](https://github.com/leanprover-community/mathlib/commit/043fa29)
feat(src/analysis/normed_space): various improvements for continuous bilinear maps ([#14539](https://github.com/leanprover-community/mathlib/pull/14539))
* Add `simps` to `arrow_congrSL`
* `continuous_linear_map.flip (compSL F E H σ₂₁ σ₁₄)` takes almost 5 seconds to elaborate, but when giving the argument `(F →SL[σ₂₄] H)` for `G` explicitly, this goes down to 1 second.
* Reorder arguments of `is_bounded_bilinear_map_comp`
* Use `continuous_linear_map` results to prove `is_bounded_bilinear_map` results.
* Make arguments to `comp_continuous_multilinear_mapL` explicit
* Add `continuous[_on].clm_comp`, `cont_diff[_on].clm_comp` and `cont_diff.comp_cont_diff_on(₂|₃)`

### [2022-06-05 12:08:46](https://github.com/leanprover-community/mathlib/commit/d9e72ff)
feat(analysis/normed_space/hahn-banach/separation): Eidelheit's theorem ([#14460](https://github.com/leanprover-community/mathlib/pull/14460))
Prove Eidelheit's theorem as a corollary to the geometric Hahn-Banach.

### [2022-06-05 07:36:59](https://github.com/leanprover-community/mathlib/commit/b6395b3)
refactor(set_theory/*): change `omega` to `aleph_0` + golf ([#14467](https://github.com/leanprover-community/mathlib/pull/14467))
This PR does two things:
- we change `cardinal.omega` to `cardinal.aleph_0` and introduce the notation `ℵ₀`.
- we golf many proofs throughout

### [2022-06-05 04:57:10](https://github.com/leanprover-community/mathlib/commit/8651b70)
chore(set_theory/cardinal/cofinality): golf + fix spacing ([#14509](https://github.com/leanprover-community/mathlib/pull/14509))

### [2022-06-05 02:47:09](https://github.com/leanprover-community/mathlib/commit/10f4572)
refactor(group_theory/group_action/defs): rename has_faithful_scalar ([#14515](https://github.com/leanprover-community/mathlib/pull/14515))
This is the first scalar -> smul renaming transition.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy

### [2022-06-05 01:29:35](https://github.com/leanprover-community/mathlib/commit/157013d)
feat(set_theory/cardinal/cofinality): weaker definition for regular cardinals ([#14433](https://github.com/leanprover-community/mathlib/pull/14433))
We weaken `c.ord.cof = c` to `c ≤ c.ord.cof` in the definition of regular cardinals, in order to slightly simplify proofs. The lemma `is_regular.cof_eq` shows that this leads to an equivalent definition.

### [2022-06-04 21:21:39](https://github.com/leanprover-community/mathlib/commit/741f4de)
feat(data/fin/tuple/monotone): new file ([#14483](https://github.com/leanprover-community/mathlib/pull/14483))

### [2022-06-04 21:21:38](https://github.com/leanprover-community/mathlib/commit/f65b160)
feat(set_theory/cardinal/cofinality): basic lemmas on limit cardinals ([#14439](https://github.com/leanprover-community/mathlib/pull/14439))

### [2022-06-04 19:44:08](https://github.com/leanprover-community/mathlib/commit/d136cd5)
chore(data/pi/lex): turn `pi.lex.linear_order` into an instance ([#14389](https://github.com/leanprover-community/mathlib/pull/14389))
* Use `[is_well_order ι (<)]` instead of `(wf : well_founded ((<) : ι → ι → Prop))`. This way `pi.lex.linear_order` can be an instance.
* Add `pi.lex.order_bot`/`pi.lex.order_top`/`pi.lex.bounded_order`.

### [2022-06-04 19:44:07](https://github.com/leanprover-community/mathlib/commit/9749297)
feat(measure_theory/integral/interval_integral): integrability of nonnegative derivatives on open intervals ([#14147](https://github.com/leanprover-community/mathlib/pull/14147))
Shows that derivatives of continuous functions are integrable when nonnegative.

### [2022-06-04 17:34:23](https://github.com/leanprover-community/mathlib/commit/93fb534)
refactor(topology/vector_bundle): split file ([#14535](https://github.com/leanprover-community/mathlib/pull/14535))
Also:
* Rename `pullback` -> `topological_vector_bundle.pullback`
* Use `delta_instance` instead of `local attribute [reducible]`
* Change module doc
* Remove transitive import

### [2022-06-04 17:34:22](https://github.com/leanprover-community/mathlib/commit/3103a89)
feat(analysis/special_functions/exp): a lemma about `exp (f x) =O[l] const _ _` ([#14524](https://github.com/leanprover-community/mathlib/pull/14524))

### [2022-06-04 17:34:21](https://github.com/leanprover-community/mathlib/commit/19b5786)
feat(tactic/set): fix a bug ([#14488](https://github.com/leanprover-community/mathlib/pull/14488))
We make the behaviour of `tactic.interactive.set` closer to that of `tactic.interactive.let`, this should fix the following issue reported in https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/set.20bug.3F/near/284471523:
```lean
import ring_theory.adjoin.basic
example {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] (x : S): false :=
begin
  let y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩, -- works
  set y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩, -- error
  sorry
end
```
This is related to [lean[#555](https://github.com/leanprover-community/mathlib/pull/555)
](https://github.com/leanprover-community/lean/pull/555)
I also fix two completely unrelated docstrings (where the list syntax created two lists instead of one) as I wouldn't want to separately add them to CI...

### [2022-06-04 17:34:20](https://github.com/leanprover-community/mathlib/commit/a869df9)
feat(analysis/asymptotics/asymptotics): generalize `is_*.inv_rev` ([#14486](https://github.com/leanprover-community/mathlib/pull/14486))
Use weaker assumption `∀ᶠ x in l, f x = 0 → g x = 0` instead of `∀ᶠ x in l, f x ≠ 0`.

### [2022-06-04 17:34:19](https://github.com/leanprover-community/mathlib/commit/8a6a793)
refactor(data/fin/basic): reformulate `fin.strict_mono_iff_lt_succ` ([#14482](https://github.com/leanprover-community/mathlib/pull/14482))
Use `fin.succ_cast` and `fin.succ`. This way we lose the case `n = 0`
but the statement looks more natural in other cases. Also add versions
for `monotone`, `antitone`, and `strict_anti`.

### [2022-06-04 17:34:18](https://github.com/leanprover-community/mathlib/commit/cab5a45)
refactor(order/directed): use `(≥)` instead of `swap (≤)` ([#14474](https://github.com/leanprover-community/mathlib/pull/14474))

### [2022-06-04 17:34:17](https://github.com/leanprover-community/mathlib/commit/b5973ba)
feat(measure_theory/measure/measure_space): there exists a ball of positive measure ([#14449](https://github.com/leanprover-community/mathlib/pull/14449))
Motivated by [#12933](https://github.com/leanprover-community/mathlib/pull/12933)

### [2022-06-04 15:25:58](https://github.com/leanprover-community/mathlib/commit/cfcc3a1)
chore(data/finsupp/basic): make arguments explicit ([#14551](https://github.com/leanprover-community/mathlib/pull/14551))
This follow the pattern that arguments to an `=` lemma should be explicit if they're not implied by other arguments.

### [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/b949240)
feat(algebra/{lie/subalgebra,module/submodule/pointwise}): submodules and lie subalgebras form canonically ordered additive monoids under addition ([#14529](https://github.com/leanprover-community/mathlib/pull/14529))
We can't actually make these instances because they result in loops for `simp`.
The `le_iff_exists_sup` lemma is probably not very useful for much beyond these new instances, but it matches `le_iff_exists_add`.

### [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/83c1cd8)
feat(set_theory/cardinal/cofinality): `ω` is a strong limit cardinal ([#14436](https://github.com/leanprover-community/mathlib/pull/14436))

### [2022-06-04 15:25:55](https://github.com/leanprover-community/mathlib/commit/0746194)
feat(set_theory/cardinal/cofinality): limit cardinal is at least `ω` ([#14432](https://github.com/leanprover-community/mathlib/pull/14432))

### [2022-06-04 15:25:54](https://github.com/leanprover-community/mathlib/commit/15726ee)
move(set_theory/{schroeder_bernstein → cardinal/schroeder_bernstein}): move file ([#14426](https://github.com/leanprover-community/mathlib/pull/14426))
Schroeder-Bernstein is ultimately the statement that cardinals are a total order, so it should go in that folder.

### [2022-06-04 15:25:53](https://github.com/leanprover-community/mathlib/commit/1f196cb)
feat(data/list/nodup): Add `list.nodup_iff` ([#14371](https://github.com/leanprover-community/mathlib/pull/14371))
Add `list.nodup_iff` and two helper lemmas `list.nth_le_eq_iff` and `list.some_nth_le_eq`

### [2022-06-04 13:17:06](https://github.com/leanprover-community/mathlib/commit/aa7d90b)
doc(set_theory/ordinal/natural_ops): mention alternate names ([#14546](https://github.com/leanprover-community/mathlib/pull/14546))

### [2022-06-04 13:17:05](https://github.com/leanprover-community/mathlib/commit/8ef2c02)
chore(order/bounded_order): move `order_dual` instances up, use them to golf lemmas ([#14544](https://github.com/leanprover-community/mathlib/pull/14544))
I only golf lemmas and `Prop`-valued instances to be sure that I don't add `order_dual`s to the statements.

### [2022-06-04 13:17:04](https://github.com/leanprover-community/mathlib/commit/5002452)
refactor(topology): move code around ([#14525](https://github.com/leanprover-community/mathlib/pull/14525))
Create a new file `topology/inseparable` and more the definitions of `specializes` and `inseparable` to this file. This is a preparation to a larger refactor of these definitions.

### [2022-06-04 13:17:03](https://github.com/leanprover-community/mathlib/commit/66b618d)
perf(measure_theory/probability_mass_function/monad): speed up proof ([#14519](https://github.com/leanprover-community/mathlib/pull/14519))
This causes a deterministic timeout in another PR.

### [2022-06-04 13:17:02](https://github.com/leanprover-community/mathlib/commit/3f26dfe)
feat(data/int/basic): Units are either equal or negatives of each other ([#14517](https://github.com/leanprover-community/mathlib/pull/14517))
This PR adds a lemma stating that units in the integers are either equal or negatives of each other. I have found this lemma to be useful for casework.

### [2022-06-04 13:17:01](https://github.com/leanprover-community/mathlib/commit/b332507)
feat(data/int/basic): Forward direction of `is_unit_iff_nat_abs_eq` ([#14516](https://github.com/leanprover-community/mathlib/pull/14516))
This PR adds the forward direction of `is_unit_iff_nat_abs_eq` as a separate lemma. This is useful since you often have `is_unit n` as a hypothesis, and `is_unit_iff_nat_abs_eq.mp hn` is a bit of a mouthful.

### [2022-06-04 13:17:00](https://github.com/leanprover-community/mathlib/commit/2a9be5b)
feat(analysis/special_functions): lemmas about filter `map`/`comap` ([#14513](https://github.com/leanprover-community/mathlib/pull/14513))
* add `comap_inf_principal_range` and `comap_nhds_within_range`;
* add `@[simp]` to `real.comap_exp_nhds_within_Ioi_zero`;
* add `real.comap_exp_nhds_zero`, `complex.comap_exp_comap_abs_at_top`, `complex.comap_exp_nhds_zero`, `complex.comap_exp_nhds_within_zero`, and `complex.tendsto_exp_nhds_zero_iff`;
* add `complex.map_exp_comap_re_at_bot` and `complex.map_exp_comap_re_at_top`;
* add `comap_norm_nhds_zero` and `complex.comap_abs_nhds_zero`.

### [2022-06-04 13:16:59](https://github.com/leanprover-community/mathlib/commit/0e943b1)
feat(order/boolean_algebra, set/basic): some compl lemmas ([#14508](https://github.com/leanprover-community/mathlib/pull/14508))
Added a few lemmas about complementation, and rephrased `compl_compl` and `mem_compl_image` to apply in `boolean_algebra` rather than `set (set _ ))`.

### [2022-06-04 13:16:58](https://github.com/leanprover-community/mathlib/commit/27c4241)
feat(set_theory/ordinal/arithmetic): `has_exists_add_of_le` instance for `ordinal` ([#14499](https://github.com/leanprover-community/mathlib/pull/14499))

### [2022-06-04 11:12:53](https://github.com/leanprover-community/mathlib/commit/7c57af9)
feat(order/bounds): Bounds on `set.image2` ([#14306](https://github.com/leanprover-community/mathlib/pull/14306))
`set.image2` analogues to the `set.image` lemmas.

### [2022-06-04 08:30:21](https://github.com/leanprover-community/mathlib/commit/85fffda)
feat(order/conditionally_complete_lattice,data/real/nnreal): add 2 lemmas ([#14545](https://github.com/leanprover-community/mathlib/pull/14545))
Add `cInf_univ` and `nnreal.Inf_empty`.

### [2022-06-04 06:32:56](https://github.com/leanprover-community/mathlib/commit/72ac40e)
feat(data/multiset/basic): add some lemmas ([#14421](https://github.com/leanprover-community/mathlib/pull/14421))

### [2022-06-04 04:55:08](https://github.com/leanprover-community/mathlib/commit/a418945)
chore(set_theory/surreal/basic): golf ([#14168](https://github.com/leanprover-community/mathlib/pull/14168))
We also add some basic lemmas for simplifying the definition of `numeric` when either a game's left or right moves are empty.

### [2022-06-04 04:16:45](https://github.com/leanprover-community/mathlib/commit/e1b3351)
feat(set_theory/game/pgame): Add dot notation on many lemmas ([#14149](https://github.com/leanprover-community/mathlib/pull/14149))

### [2022-06-03 22:33:16](https://github.com/leanprover-community/mathlib/commit/0098286)
feat(set_theory/ordinal/natural_ops): define natural addition ([#14291](https://github.com/leanprover-community/mathlib/pull/14291))
We define the natural addition operation on ordinals. We prove the basic properties, like commutativity, associativity, and cancellativity. We also provide the type synonym `nat_ordinal` for ordinals with natural operations, which allows us to take full advantage of this rich algebraic structure.

### [2022-06-03 16:16:11](https://github.com/leanprover-community/mathlib/commit/d63246c)
feat(analysis/calculus/fderiv_measurable): the right derivative is measurable ([#14527](https://github.com/leanprover-community/mathlib/pull/14527))
We already know that the full Fréchet derivative is measurable. In this PR, we follow the same proof to show that the right derivative of a function defined on the real line is also measurable (the target space may be any complete vector space).

### [2022-06-03 16:16:10](https://github.com/leanprover-community/mathlib/commit/2a21a86)
refactor(algebra/order/ring): turn `sq_le_sq` into an `iff` ([#14511](https://github.com/leanprover-community/mathlib/pull/14511))
* `sq_le_sq` and `sq_lt_sq` are now `iff` lemmas;
* drop `abs_le_abs_of_sq_le_sq` and `abs_lt_abs_of_sq_lt_sq`.

### [2022-06-03 14:08:37](https://github.com/leanprover-community/mathlib/commit/fa22603)
docs(order/boolean_algebra): typo in generalized boolean algebra doc ([#14536](https://github.com/leanprover-community/mathlib/pull/14536))

### [2022-06-03 12:27:32](https://github.com/leanprover-community/mathlib/commit/6ca5910)
feat(measure_theory/integral/lebesgue): approximate a function by a finite integral function in a sigma-finite measure space. ([#14528](https://github.com/leanprover-community/mathlib/pull/14528))
If `L < ∫⁻ x, f x ∂μ`, then there exists a measurable function `g ≤ f` (even a simple function) with finite integral and `L < ∫⁻ x, g x ∂μ`, if the measure is sigma-finite.

### [2022-06-03 10:31:17](https://github.com/leanprover-community/mathlib/commit/bec8b65)
feat(analysis/calculus/tangent_cone): unique differentiability of open interval at endpoint ([#14530](https://github.com/leanprover-community/mathlib/pull/14530))
We show that, if a point belongs to the closure of a convex set with nonempty interior, then it is a point of unique differentiability. We apply this to the specific situation of `Ioi` and `Iio`.

### [2022-06-03 10:31:16](https://github.com/leanprover-community/mathlib/commit/705160e)
feat(algebra/char_zero): add a lemma `ring_hom.injective_nat` ([#14414](https://github.com/leanprover-community/mathlib/pull/14414))
Note that there is a lemma `ring_hom.injective_int`.

### [2022-06-03 10:31:15](https://github.com/leanprover-community/mathlib/commit/d2dcb74)
feat(data/polynomial/eval): reduce assumptions, add a lemma ([#14391](https://github.com/leanprover-community/mathlib/pull/14391))
Note that there is a lemma `mv_polynomial.support_map_of_injective`.

### [2022-06-03 10:31:14](https://github.com/leanprover-community/mathlib/commit/c9d69a4)
feat(topology/algebra/module/finite_dimension): all linear maps from a finite dimensional T2 TVS are continuous ([#13460](https://github.com/leanprover-community/mathlib/pull/13460))
Summary of the changes :
- generalize a bunch of results from `analysis/normed_space/finite_dimension` (main ones are : `continuous_equiv_fun_basis`, `linear_map.continuous_of_finite_dimensional`, and related constructions like `linear_map.to_continuous_linear_map`) to arbitrary TVSs, and move them to a new file `topology/algebra/module/finite_dimension`
- generalize `linear_map.continuous_iff_is_closed_ker` to arbitrary TVSs, and move it from `analysis/normed_space/operator_norm` to the new file
- as needed by the generalizations, add lemma `unique_topology_of_t2` : if `𝕜` is a nondiscrete normed field, any T2 topology on `𝕜` which makes it a topological vector space over itself (with the norm topology) is *equal* to the norm topology
- finally, change `pi_eq_sum_univ` to take any `decidable_eq` instance (not just the classical ones), and fix later uses

### [2022-06-03 08:57:19](https://github.com/leanprover-community/mathlib/commit/31cbfbb)
feat(linear_algebra/basis): repr_support_of_mem_span ([#14504](https://github.com/leanprover-community/mathlib/pull/14504))
This lemma states that if a vector is in the span of a subset of the basis vectors, only this subset of basis vectors will be used in its `repr` representation.

### [2022-06-03 07:58:59](https://github.com/leanprover-community/mathlib/commit/2b69bb4)
feat(analysis/complex/upper_half_plane): extend action on upper half plane to GL_pos ([#12415](https://github.com/leanprover-community/mathlib/pull/12415))
This extends the action on the upper half plane from `SL_2` to `GL_pos`,

### [2022-06-02 21:38:24](https://github.com/leanprover-community/mathlib/commit/1a1895c)
feat(data/nat/basic): add lemmas about `nat.bit_cases_on` ([#14481](https://github.com/leanprover-community/mathlib/pull/14481))
Also drop `nat.bit_cases` (was the same definition with a different
order of arguments).

### [2022-06-02 19:38:29](https://github.com/leanprover-community/mathlib/commit/ade30c3)
feat(data/int/basic): Lemmas for when a square equals 1 ([#14501](https://github.com/leanprover-community/mathlib/pull/14501))
This PR adds two lemmas for when a square equals one. The `lt` lemma will be useful for irreducibility of x^n-x-1.

### [2022-06-02 19:38:28](https://github.com/leanprover-community/mathlib/commit/e443331)
refactor(field_theory/normal): generalize `lift_normal` and `restrict_normal` ([#14450](https://github.com/leanprover-community/mathlib/pull/14450))
This generalization seems useful. The example I have in mind is restricting a map `ϕ : E →ₐ[F] (algebraic_closure E)` to a map `ϕ : E →ₐ[F] E` when E/F is normal.
Coauthored by @mariainesdff

### [2022-06-02 17:31:51](https://github.com/leanprover-community/mathlib/commit/ae02583)
refactor(data/set/finite): protect `set.finite` ([#14344](https://github.com/leanprover-community/mathlib/pull/14344))
This change will make it so that it does not conflict with a top-level `finite` that will be added to complement `infinite`.

### [2022-06-02 17:31:49](https://github.com/leanprover-community/mathlib/commit/28031a8)
feat(number_theory/factorization): evaluating arithmetic functions at prime powers ([#13817](https://github.com/leanprover-community/mathlib/pull/13817))

### [2022-06-02 15:58:16](https://github.com/leanprover-community/mathlib/commit/0575db0)
feat(topology/vector_bundle): define some useful linear maps globally ([#14484](https://github.com/leanprover-community/mathlib/pull/14484))
* Define `pretrivialization.symmₗ`, `pretrivialization.linear_map_at`, `trivialization.symmL`, `trivialization.continuous_linear_map_at`
* These are globally-defined (continuous) linear maps. They are linear equivalences on `e.base_set`, but it is useful to define these globally. They are defined as `0` outside `e.base_set`
* These are convenient to define the vector bundle of continuous linear maps.

### [2022-06-02 15:58:15](https://github.com/leanprover-community/mathlib/commit/c5f8d78)
doc(set_theory/cardinal/cofinality): add myself as author ([#14469](https://github.com/leanprover-community/mathlib/pull/14469))

### [2022-06-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/4bd8c85)
feat(category_theory/limits): is_kernel_of_comp ([#14409](https://github.com/leanprover-community/mathlib/pull/14409))
From LTE.
Also rename `lift_comp_ι` to `lift_ι` for consistency with the general `has_limit` versions.

### [2022-06-02 15:58:13](https://github.com/leanprover-community/mathlib/commit/2941590)
feat(linear_algebra/matrix): Spectral theorem for matrices ([#14231](https://github.com/leanprover-community/mathlib/pull/14231))

### [2022-06-02 13:48:11](https://github.com/leanprover-community/mathlib/commit/4e1eeeb)
feat(tactic/linear_combination): allow combinations of arbitrary proofs ([#14229](https://github.com/leanprover-community/mathlib/pull/14229))
This changes the syntax of `linear_combination` so that the combination is expressed using arithmetic operation. Credit to @digama0 for the parser. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313979.20arbitrary.20proof.20terms.20in.20.60linear_combination.60) for more details.

### [2022-06-02 09:08:42](https://github.com/leanprover-community/mathlib/commit/57885b4)
feat(topological_space/vector_bundle): reformulate linearity condition ([#14485](https://github.com/leanprover-community/mathlib/pull/14485))
* Reformulate the linearity condition on (pre)trivializations of vector bundles using `total_space_mk`. Note: it is definitionally equal to the previous definition, but without using the coercion.
* Make one argument of `e.linear` implicit
* Simplify the proof of linearity of the product of vector bundles

### [2022-06-01 23:57:04](https://github.com/leanprover-community/mathlib/commit/c414df7)
feat(tactic/linear_combination): allow arbitrary proof terms ([#13979](https://github.com/leanprover-community/mathlib/pull/13979))
This extends `linear_combination` to allow arbitrary proof terms of equalities instead of just local hypotheses. 
```lean
constants (qc : ℚ) (hqc : qc = 2*qc)
example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by linear_combination (h a b, 3) (hqc)
```
This changes the syntax of `linear_combination` in the case where no coefficient is provided and it defaults to 1. A space-separated list of pexprs won't parse, since there's an ambiguity in `h1 h2` between an application or two arguments. So this case now requres parentheses around the argument:
`linear_combination (h1, 3) (h2)`
Does anyone object to this syntax change?

### [2022-06-01 20:32:56](https://github.com/leanprover-community/mathlib/commit/12ad63e)
feat(order/conditionally_complete_lattice): Map `Inf` by monotone function ([#14118](https://github.com/leanprover-community/mathlib/pull/14118))

### [2022-06-01 17:27:02](https://github.com/leanprover-community/mathlib/commit/9600f4f)
feat(order/filter/bases): view a filter as a *bundled* filter basis ([#14506](https://github.com/leanprover-community/mathlib/pull/14506))
We already have `filter.basis_sets` which says that the elements of a filter are a basis of itself (in the `has_basis` sense), but we don't have the fact that they form a filter basis (in the `filter_basis` sense), and `x ∈ f.basis_sets.is_basis.filter_basis` is not defeq to `x ∈ f`

### [2022-06-01 17:27:01](https://github.com/leanprover-community/mathlib/commit/0950ba3)
refactor(topology/separation): rename `indistinguishable` to `inseparable` ([#14401](https://github.com/leanprover-community/mathlib/pull/14401))
* Replace `indistinguishable` by `inseparable` in the definition and lemma names. The word "indistinguishable" is too generic.
* Rename `t0_space_iff_distinguishable` to `t0_space_iff_not_inseparable` because the name `t0_space_iff_separable` is misleading, slightly golf the proof.
* Add `t0_space_iff_nhds_injective`, `nhds_injective`, reorder lemmas around these two.

### [2022-06-01 17:27:00](https://github.com/leanprover-community/mathlib/commit/9b3ea03)
feat(data/bundle): make arguments to proj and total_space_mk implicit ([#14359](https://github.com/leanprover-community/mathlib/pull/14359))
I will wait for a later PR to (maybe) fix the reducibility/simp of these declarations.

### [2022-06-01 15:09:46](https://github.com/leanprover-community/mathlib/commit/dba797a)
feat(order/liminf_limsup): composition `g ∘ f` is bounded iff `f` is bounded ([#14479](https://github.com/leanprover-community/mathlib/pull/14479))
* If `g` is a monotone function that tends to infinity at infinity, then a filter is bounded from above under `g ∘ f` iff it is bounded under `f`, similarly for antitone functions and/or filter bounded from below.
* A filter is bounded from above under `real.exp ∘ f` iff it is is bounded from above under `f`.
* Use `monotone` in `real.exp_monotone`.
* Add `@[mono]` to `real.exp_strict_mono`.

### [2022-06-01 15:09:45](https://github.com/leanprover-community/mathlib/commit/047db39)
feat(algebra/char_p/basic): add lemma `ring_char.char_ne_zero_of_finite` ([#14454](https://github.com/leanprover-community/mathlib/pull/14454))
This adds the fact that a finite (not necessarily associative) ring cannot have characteristic zero.
See [this topic on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Statements.20about.20finite.20rings).

### [2022-06-01 15:09:44](https://github.com/leanprover-community/mathlib/commit/df057e3)
feat(measure_theory/integral/lebesgue): integral over finite and countable sets ([#14447](https://github.com/leanprover-community/mathlib/pull/14447))

### [2022-06-01 15:09:43](https://github.com/leanprover-community/mathlib/commit/f0216ff)
refactor(combinatorics/simple_graph/basic): rename induced embedding on complete graphs ([#14404](https://github.com/leanprover-community/mathlib/pull/14404))

### [2022-06-01 15:09:42](https://github.com/leanprover-community/mathlib/commit/0a0a60c)
feat(data/set/finite,order/*): generalize some lemmas from sets to (co)frames ([#14394](https://github.com/leanprover-community/mathlib/pull/14394))
* generalize `set.Union_inter_of_monotone` to an `order.frame`;
* add dual versions, both for `(co)frame`s and sets;
* same for `set.Union_Inter_of_monotone`.

### [2022-06-01 15:09:41](https://github.com/leanprover-community/mathlib/commit/892f889)
feat(data/matrix/basic): lemmas about mul_vec and single ([#13835](https://github.com/leanprover-community/mathlib/pull/13835))
We seem to be proving variants of the same statement over and over again; this introduces a new lemma that we can use to prove all these variants trivially in term mode. The new lemmas are:
* `matrix.mul_vec_single`
* `matrix.single_vec_mul`
* `matrix.diagonal_mul_vec_single`
* `matrix.single_vec_mul_diagonal`
A lot of the proofs got shorter by avoiding `ext` which invokes a more powerful lemma than we actually need.

### [2022-06-01 13:00:47](https://github.com/leanprover-community/mathlib/commit/f359d55)
feat(analysis/asymptotics/asymptotics): generalize `is_O.smul` etc ([#14487](https://github.com/leanprover-community/mathlib/pull/14487))
Allow `(k₁ : α → 𝕜) (k₂ : α → 𝕜')` instead of `(k₁ k₂ : α → 𝕜)`.

### [2022-06-01 13:00:46](https://github.com/leanprover-community/mathlib/commit/4f1c8cf)
feat(algebra/order/group): helper lemma `0 ≤ a + |a|` ([#14457](https://github.com/leanprover-community/mathlib/pull/14457))
Helper lemma for integers and absolute values.

### [2022-06-01 12:13:54](https://github.com/leanprover-community/mathlib/commit/f4fe790)
feat(topology/vector_bundle): redefine continuous coordinate change ([#14462](https://github.com/leanprover-community/mathlib/pull/14462))
* For any two trivializations, we define the coordinate change between the two trivializations: continous linear automorphism of `F`, defined by composing one trivialization with the inverse of the other. This is defined for any point in the intersection of their base sets, and we define it to be the identity function outside this set.
* Redefine `topological_vector_bundle`: we now require that this coordinate change between any two trivializations is continuous on the intersection of their base sets.
* Redefine `topological_vector_prebundle` with the existence of a continuous linear coordinate change function.
* Simplify the proofs that the coordinate change function is continuous for constructions on vector bundles.

### [2022-06-01 09:59:02](https://github.com/leanprover-community/mathlib/commit/60371b8)
refactor(topology/metric_space/lipschitz): use `function.End` ([#14502](https://github.com/leanprover-community/mathlib/pull/14502))
This way we avoid dependency on `category_theory`.

### [2022-06-01 09:59:01](https://github.com/leanprover-community/mathlib/commit/7d71343)
chore(topology/algebra/uniform_field): Wrap in namespace ([#14498](https://github.com/leanprover-community/mathlib/pull/14498))
Put everything in `topology.algebra.uniform_field` in the `uniform_space.completion` namespace.

### [2022-06-01 09:18:43](https://github.com/leanprover-community/mathlib/commit/2a0f474)
feat(analysis/normed_space/star/character_space): compactness of the character space of a normed algebra ([#14135](https://github.com/leanprover-community/mathlib/pull/14135))
This PR puts a `compact_space` instance on `character_space 𝕜 A` for a normed algebra `A` using the Banach-Alaoglu theorem. This is a key step in developing the continuous functional calculus.

### [2022-06-01 01:59:39](https://github.com/leanprover-community/mathlib/commit/6b18362)
feat(data/zmod/quotient): More API for `orbit_zpowers_equiv` ([#14181](https://github.com/leanprover-community/mathlib/pull/14181))
This PR adds another `symm_apply` API lemma for `orbit_zpowers_equiv`, taking `(k : ℤ)` rather than `(k : zmod (minimal_period ((•) a) b))`.