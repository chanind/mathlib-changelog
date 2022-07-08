### [2021-03-31 21:24:16](https://github.com/leanprover-community/mathlib/commit/5f1b450)
refactor(algebra/*): add new `mul_one_class` and `add_zero_class` for non-associative monoids ([#6865](https://github.com/leanprover-community/mathlib/pull/6865))
This extracts a base class from `monoid M`, `mul_one_class M`, that drops the associativity assumption.
It goes on to weaken `monoid_hom` and `submonoid` to require `mul_one_class M` instead of `monoid M`, along with weakening the typeclass requirements for other primitive constructions like `monoid_hom.fst`.
Instances of the new classes are provided on `pi`, `prod`, `finsupp`, `(add_)submonoid`, and `(add_)monoid_algebra`.
This is by no means an exhaustive relaxation across mathlib, but it aims to broadly cover the foundations.

### [2021-03-31 17:53:07](https://github.com/leanprover-community/mathlib/commit/cc99152)
feat(data/list/zip): `nth_zip_with` univ polymorphic, `zip_with_eq_nil_iff` ([#6974](https://github.com/leanprover-community/mathlib/pull/6974))

### [2021-03-31 14:28:55](https://github.com/leanprover-community/mathlib/commit/23dbb4c)
feat(tactic/elementwise): autogenerate lemmas in concrete categories ([#6941](https://github.com/leanprover-community/mathlib/pull/6941))
# The `elementwise` attribute
The `elementwise` attribute can be applied to a lemma
```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C] {X Y : C} (f g : X ⟶ Y) : f = g := ...
```
and produce
```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y : C} (f g : X ⟶ Y) (x : X) : f x = g x := ...
```
(Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f` and `g` are being coerced to functions via `concrete_category.has_coe_to_fun`.)
The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.

### [2021-03-31 13:16:42](https://github.com/leanprover-community/mathlib/commit/f29b0b4)
feat(category_theory/lifting_properties): create a new file about lifting properties ([#6852](https://github.com/leanprover-community/mathlib/pull/6852))
This file introduces lifting properties, establishes a few basic properties, and constructs a subcategory spanned by morphisms having a right lifting property.

### [2021-03-31 11:08:19](https://github.com/leanprover-community/mathlib/commit/09110f1)
feat(geometry/manifold/bump_function): define smooth bump functions, baby version of the Whitney embedding thm ([#6839](https://github.com/leanprover-community/mathlib/pull/6839))
* refactor some functions in `analysis/calculus/specific_functions` to use bundled structures;
* define `to_euclidean`, `euclidean.dist`, `euclidean.ball`, and `euclidean.closed_ball`;
* define smooth bump functions on manifolds;
* prove a baby version of the Whitney embedding theorem.

### [2021-03-31 09:30:06](https://github.com/leanprover-community/mathlib/commit/1fdce2f)
refactor(analysis/normed_space/basic): add semi_normed_ring ([#6889](https://github.com/leanprover-community/mathlib/pull/6889))
This is the natural continuation of [#6888](https://github.com/leanprover-community/mathlib/pull/6888) . We add here semi_normed_ring, semi_normed_comm_ring, semi_normed_space and semi_normed_algebra.
I didn't add `semi_normed_field`: the most important result for normed_field is `∥1∥ = 1`, that is false for `semi_normed_field`, making it a more or less useless notion. In particular a `semi_normed_space` is by definition a vector space over a `normed_field`.

### [2021-03-31 03:01:59](https://github.com/leanprover-community/mathlib/commit/85c8961)
chore(scripts): update nolints.txt ([#6970](https://github.com/leanprover-community/mathlib/pull/6970))
I am happy to remove some nolints for you!

### [2021-03-31 00:41:44](https://github.com/leanprover-community/mathlib/commit/8ed5c3c)
chore(topology/algebra/group_with_zero): continuity attributes ([#6965](https://github.com/leanprover-community/mathlib/pull/6965))
Some `@[continuity]` tags, requested at https://github.com/leanprover-community/mathlib/pull/6937#discussion_r604139611

### [2021-03-31 00:41:43](https://github.com/leanprover-community/mathlib/commit/6f6ee00)
chore(data/finsupp): add simp lemmas about dom_congr ([#6963](https://github.com/leanprover-community/mathlib/pull/6963))
Inspired by [#6905](https://github.com/leanprover-community/mathlib/pull/6905)

### [2021-03-30 20:36:57](https://github.com/leanprover-community/mathlib/commit/f2b433f)
refactor(data/equiv/basic): remove `equiv.set.range` ([#6960](https://github.com/leanprover-community/mathlib/pull/6960))
We already had `equiv.of_injective`, which duplicated the API. `of_injective` is the preferred naming, so we change all occurrences accordingly.
This also renames `equiv.set.range_of_left_inverse` to `equiv.of_left_inverse`, to match names like `linear_equiv.of_left_inverse`.
Note that the `congr` and `powerset` definitions which appear in the diff have just been reordered, and are otherwise unchanged.

### [2021-03-30 20:36:56](https://github.com/leanprover-community/mathlib/commit/cf377e2)
chore(algebra/category/*): fix some names ([#6846](https://github.com/leanprover-community/mathlib/pull/6846))

### [2021-03-30 17:12:57](https://github.com/leanprover-community/mathlib/commit/33f443f)
feat(archive/imo): add 2011 Q5 ([#6927](https://github.com/leanprover-community/mathlib/pull/6927))
proof of IMO 2011 Q5

### [2021-03-30 17:12:56](https://github.com/leanprover-community/mathlib/commit/0c0fb53)
feat(group_theory/perm/cycles): Order of is_cycle ([#6873](https://github.com/leanprover-community/mathlib/pull/6873))
The order of a cycle equals the cardinality of its support.

### [2021-03-30 14:01:24](https://github.com/leanprover-community/mathlib/commit/a192783)
chore(algebra/direct_sum_graded): relax typeclass assumptions ([#6961](https://github.com/leanprover-community/mathlib/pull/6961))

### [2021-03-30 14:01:23](https://github.com/leanprover-community/mathlib/commit/ed6d94a)
chore(group_theory/group_action/defs): combine duplicated `comp_hom` and rename derivative definitions ([#6942](https://github.com/leanprover-community/mathlib/pull/6942))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Duplicate.20mul_action.20defs/near/232246589)

### [2021-03-30 14:01:22](https://github.com/leanprover-community/mathlib/commit/e1f66f1)
feat(topology/algebra/group_with_zero): continuity of exponentiation to an integer power (`fpow`) ([#6937](https://github.com/leanprover-community/mathlib/pull/6937))
In a topological group-with-zero (more precisely, in a space with `has_continuous_inv'` and `has_continuous_mul`), the `k`-th power function is continuous for integer `k`, with the possible exception of at 0.

### [2021-03-30 14:01:21](https://github.com/leanprover-community/mathlib/commit/bcfaabf)
feat(data/set_like): remove repeated boilerplate from subobjects ([#6768](https://github.com/leanprover-community/mathlib/pull/6768))
This just scratches the surface, and removes all of the boilerplate that is just a consequence of the injective map to a `set`.
Already this trims more than 150 lines.
For every lemma of the form `set_like.*` added in this PR, the corresponding `submonoid.*`, `add_submonoid.*`, `sub_mul_action.*`, `submodule.*`, `subsemiring.*`, `subring.*`, `subfield.*`, `subalgebra.*`, and `intermediate_field.*` lemmas have been removed.
Often these lemmas only existed for one or two of these subtypes, so this means that we have lemmas for more things not fewer.
Note that while the `ext_iff`, `ext'`, and `ext'_iff` lemmas have been removed, we still need the `ext` lemma as `set_like.ext` cannot directly be tagged `@[ext]`.

### [2021-03-30 10:02:55](https://github.com/leanprover-community/mathlib/commit/b0ece6f)
chore(data/set/{basic,countable}): add, rename, golf ([#6935](https://github.com/leanprover-community/mathlib/pull/6935))
* add `set.range_prod_map` and `set.countable.image2`;
* rename `set.countable_prod` to `set.countable.prod`.

### [2021-03-30 10:02:54](https://github.com/leanprover-community/mathlib/commit/7e109c4)
feat(measure_theory/lp_space): continuous functions on compact space are in Lp ([#6919](https://github.com/leanprover-community/mathlib/pull/6919))
Continuous functions on a compact space equipped with a finite Borel measure are in Lp, and the inclusion is a bounded linear map.  This follows directly by transferring the construction in [#6878](https://github.com/leanprover-community/mathlib/pull/6878) for bounded continuous functions, using the fact that continuous function on a compact space are bounded.

### [2021-03-30 10:02:53](https://github.com/leanprover-community/mathlib/commit/3e67f50)
feat(analysis/normed_space/inner_product): isometry of ℂ with Euclidean space ([#6877](https://github.com/leanprover-community/mathlib/pull/6877))
`ℂ` is isometric to `fin 2 → ℝ` with the Euclidean inner product.  The isometry given here is that defined by the ordered basis {1, i} for `ℂ`.

### [2021-03-30 07:31:27](https://github.com/leanprover-community/mathlib/commit/877af10)
chore(algebra/big_operators/order): generalize some lemmas to `ordered_comm_semiring` ([#6950](https://github.com/leanprover-community/mathlib/pull/6950))

### [2021-03-30 07:31:27](https://github.com/leanprover-community/mathlib/commit/fe00980)
feat(topology/compact_open): β ≃ₜ C(α, β) if α has a single element ([#6946](https://github.com/leanprover-community/mathlib/pull/6946))

### [2021-03-30 03:44:59](https://github.com/leanprover-community/mathlib/commit/8d398a8)
chore(scripts): update nolints.txt ([#6957](https://github.com/leanprover-community/mathlib/pull/6957))
I am happy to remove some nolints for you!

### [2021-03-30 03:44:58](https://github.com/leanprover-community/mathlib/commit/b4ce9b7)
feat(group_theory/order_of_element): exists_pow_eq_self_of_coprime ([#6875](https://github.com/leanprover-community/mathlib/pull/6875))
If `n` is coprime to the order of `g`, then there exists an `m` such that `(g ^ n) ^ m = g`.

### [2021-03-30 03:44:57](https://github.com/leanprover-community/mathlib/commit/b449a3c)
feat(order/ideal, order/pfilter, order/prime_ideal): added `is_ideal`, `is_pfilter`, `is_prime`, `is_maximal`, `prime_pair` ([#6656](https://github.com/leanprover-community/mathlib/pull/6656))
Proved basic lemmas about them. Also extended the is_proper API.
Made the `pfilter`arguments of some lemmas explicit:
- `pfilter.nonempty`
- `pfilter.directed`

### [2021-03-29 23:43:35](https://github.com/leanprover-community/mathlib/commit/e5c112d)
feat(category_theory/arrow): simp lemmas for lifts involving arrow.mk ([#6953](https://github.com/leanprover-community/mathlib/pull/6953))
These came up during review of [#6852](https://github.com/leanprover-community/mathlib/pull/6852).

### [2021-03-29 23:43:35](https://github.com/leanprover-community/mathlib/commit/87bc893)
feat(group_theory/{subgroup, order_of_element}): refactors simple groups, classifies finite simple abelian/solvable groups ([#6926](https://github.com/leanprover-community/mathlib/pull/6926))
Refactors the deprecated `simple_group` to a new `is_simple_group`
Shows that all cyclic groups of prime order are simple
Shows that all simple `comm_group`s are cyclic
Shows that all simple finite `comm_group`s have prime order
Shows that a simple group is solvable iff it is commutative

### [2021-03-29 23:43:33](https://github.com/leanprover-community/mathlib/commit/ad4aca0)
feat(topology/local_homeomorph): add `is_image`, `piecewise`, and `disjoint_union` ([#6804](https://github.com/leanprover-community/mathlib/pull/6804))
Also add `local_equiv.copy` and `local_homeomorph.replace_equiv` and use them for `local_equiv.disjoint_union` and `local_homeomorph.disjoint_union.

### [2021-03-29 20:11:52](https://github.com/leanprover-community/mathlib/commit/50225da)
feat(data/fin): fin n.succ is an add_comm_group ([#6898](https://github.com/leanprover-community/mathlib/pull/6898))
This just moves the proof out of `data.zmod` basic.
Moving the full ring instance is left for future work, as `modeq`, used to prove left_distrib, is not available to import in `data/fin/basic`.
Note this adds an import of `data.int.basic` to `data.fin.basic`. I think this is probably acceptable?

### [2021-03-29 18:22:24](https://github.com/leanprover-community/mathlib/commit/8b7c8a4)
chore(topology/instances/real): golf ([#6945](https://github.com/leanprover-community/mathlib/pull/6945))

### [2021-03-29 18:22:23](https://github.com/leanprover-community/mathlib/commit/3fdf529)
chore(topology/instances/ennreal): golf ([#6944](https://github.com/leanprover-community/mathlib/pull/6944))

### [2021-03-29 13:12:21](https://github.com/leanprover-community/mathlib/commit/1677653)
chore(*): long lines ([#6939](https://github.com/leanprover-community/mathlib/pull/6939))
Except for URLs, references to books, and `src/tactic/*`, this should be very close to the last of our long lines.

### [2021-03-29 13:12:19](https://github.com/leanprover-community/mathlib/commit/f1fe129)
feat(category_theory/images): instance for precomposition by iso ([#6931](https://github.com/leanprover-community/mathlib/pull/6931))

### [2021-03-29 13:12:17](https://github.com/leanprover-community/mathlib/commit/d2e5976)
feat(category_theory/limits/terminal): constructor for is_terminal ([#6929](https://github.com/leanprover-community/mathlib/pull/6929))

### [2021-03-29 13:12:15](https://github.com/leanprover-community/mathlib/commit/cf56f88)
feat(category_theory/limits/zero): functor categories have zero morphisms ([#6928](https://github.com/leanprover-community/mathlib/pull/6928))

### [2021-03-29 13:12:14](https://github.com/leanprover-community/mathlib/commit/407ad21)
feat(algebra.smul_with_zero): add mul_zero_class.to_smul_with_zero ([#6911](https://github.com/leanprover-community/mathlib/pull/6911))

### [2021-03-29 13:12:12](https://github.com/leanprover-community/mathlib/commit/fe29f88)
feat(data/nat/basic):  (n+1) / 2 ≤ n ([#6863](https://github.com/leanprover-community/mathlib/pull/6863))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths

### [2021-03-29 13:12:11](https://github.com/leanprover-community/mathlib/commit/66ee65c)
feat(category): structured arrows ([#6830](https://github.com/leanprover-community/mathlib/pull/6830))
Factored out from [#6820](https://github.com/leanprover-community/mathlib/pull/6820).

### [2021-03-29 13:12:10](https://github.com/leanprover-community/mathlib/commit/318cb4b)
feat(category_theory): essentially_small categories ([#6801](https://github.com/leanprover-community/mathlib/pull/6801))
Preparation for `well_powered`, then for `complete_semilattice_Inf|Sup` on `subobject X`, then for work on chain complexes.

### [2021-03-29 13:12:08](https://github.com/leanprover-community/mathlib/commit/8d8b64e)
feat(data/equiv/mul_add_aut): adding conjugation in an additive group ([#6774](https://github.com/leanprover-community/mathlib/pull/6774))
assuming `[add_group G]` this defines `G ->+ additive (add_aut G)`

### [2021-03-29 08:42:19](https://github.com/leanprover-community/mathlib/commit/2ad4a4c)
chore(group_theory/subgroup,logic/nontrivial): golf ([#6934](https://github.com/leanprover-community/mathlib/pull/6934))

### [2021-03-29 05:18:50](https://github.com/leanprover-community/mathlib/commit/5ab177a)
chore(topology/instances/real): remove instance `real_maps_algebra` ([#6920](https://github.com/leanprover-community/mathlib/pull/6920))
Remove 
```lean
instance reals_semimodule : has_continuous_smul ℝ ℝ
instance real_maps_algebra {α : Type*} [topological_space α] : algebra ℝ C(α, ℝ)
```
These are not used explicitly anywhere in the library, I suspect because if needed they can be found by typeclass inference.  Deleting them cleans up the import hierarchy by requiring many fewer files to import `topology.continuous_function.algebra`.

### [2021-03-29 03:17:36](https://github.com/leanprover-community/mathlib/commit/cb1d1c6)
chore(scripts): update nolints.txt ([#6933](https://github.com/leanprover-community/mathlib/pull/6933))
I am happy to remove some nolints for you!

### [2021-03-29 03:17:36](https://github.com/leanprover-community/mathlib/commit/f290000)
feat(data/equiv/fin): rename sum_fin_sum_equiv to fin_sum_fin_equiv ([#6857](https://github.com/leanprover-community/mathlib/pull/6857))
Renames `sum_fin_sum_equiv` to `fin_sum_fin_equiv` (as discussed 
[on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/sum_fin_add_comm_equiv))
Introduces a version with `fin(n + m)` instead of `fin(m + n)` 
Adds a bunch of simp lemmas for applying these (and their inverses)

### [2021-03-28 19:54:49](https://github.com/leanprover-community/mathlib/commit/8e275a3)
fix(order/complete_lattice): fix typo in docstring ([#6925](https://github.com/leanprover-community/mathlib/pull/6925))

### [2021-03-28 19:54:48](https://github.com/leanprover-community/mathlib/commit/a17f38f)
feat(measure_theory/lp_space): bounded continuous functions are in Lp ([#6878](https://github.com/leanprover-community/mathlib/pull/6878))
Under appropriate conditions (finite Borel measure, second-countable), a bounded continuous function is in L^p.  The main result of this PR is `bounded_continuous_function.to_Lp`, which provides this operation as a bounded linear map.  There are also several variations.

### [2021-03-28 16:13:09](https://github.com/leanprover-community/mathlib/commit/4487e73)
feat(order/bounded_lattice): is_total, coe_sup and unique_maximal lemmas ([#6922](https://github.com/leanprover-community/mathlib/pull/6922))
A few little additions for with_top and with_bot.

### [2021-03-28 16:13:08](https://github.com/leanprover-community/mathlib/commit/7285fb6)
feat(data/complex/circle): circle is a Lie group ([#6907](https://github.com/leanprover-community/mathlib/pull/6907))
Define `circle` to be the unit circle in `ℂ` and give it the structure of a Lie group.  Also define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to `circle`, and give it (separately) the structures of a group homomorphism and a smooth map (we seem not to have the definition of a Lie group homomorphism).

### [2021-03-28 14:22:34](https://github.com/leanprover-community/mathlib/commit/accb9d2)
fix(topology/algebra/mul_action): fix typo in instance name ([#6921](https://github.com/leanprover-community/mathlib/pull/6921))

### [2021-03-28 12:00:37](https://github.com/leanprover-community/mathlib/commit/0e4760b)
refactor(measure_theory): add typeclasses for measurability of operations ([#6832](https://github.com/leanprover-community/mathlib/pull/6832))
With these typeclasses and lemmas we can use, e.g., `measurable.mul` for any type with measurable `uncurry (*)`, not only those with `has_continuous_mul`.
New typeclasses:
* `has_measurable_add`, `has_measurable_add₂`: measurable left/right addition and measurable `uncurry (+)`;
* `has_measurable_mul`, `has_measurable_mul₂`: measurable left/right multiplication and measurable `uncurry (*)`;
* `has_measurable_pow`: measurable `uncurry (^)`
* `has_measurable_sub`, `has_measurable_sub₂`: measurable left/right subtraction and measurable `λ (a, b), a - b`
* `has_measurable_div`, `has_measurable_div₂` : measurability of division as a function of numerator/denominator and measurability of `λ (a, b), a / b`;
* `has_measurable_neg`, `has_measurable_inv`: measurable negation/inverse;
* `has_measurable_const_smul`, `has_measurable_smul`: measurable `λ x, c • x` and measurable `λ (c, x), c • x`

### [2021-03-28 04:55:34](https://github.com/leanprover-community/mathlib/commit/dc34b21)
lint(*): split long lines ([#6918](https://github.com/leanprover-community/mathlib/pull/6918))

### [2021-03-28 01:36:58](https://github.com/leanprover-community/mathlib/commit/e129117)
chore(scripts): update nolints.txt ([#6917](https://github.com/leanprover-community/mathlib/pull/6917))
I am happy to remove some nolints for you!

### [2021-03-27 23:51:09](https://github.com/leanprover-community/mathlib/commit/879cb47)
feat(test/integration): add examples of computing integrals by simp ([#6859](https://github.com/leanprover-community/mathlib/pull/6859))
As suggested in [[#6216](https://github.com/leanprover-community/mathlib/pull/6216) (comment)](https://github.com/leanprover-community/mathlib/pull/6216#discussion_r580389848).
The examples added here were made possible by [#6216](https://github.com/leanprover-community/mathlib/pull/6216), [#6334](https://github.com/leanprover-community/mathlib/pull/6334), [#6357](https://github.com/leanprover-community/mathlib/pull/6357), [#6597](https://github.com/leanprover-community/mathlib/pull/6597).

### [2021-03-27 21:49:34](https://github.com/leanprover-community/mathlib/commit/06b21d0)
chore(category_theory/monads): remove empty file ([#6915](https://github.com/leanprover-community/mathlib/pull/6915))
In [#5889](https://github.com/leanprover-community/mathlib/pull/5889) I moved the contents of this file into monad/basic but I forgot to delete this file.

### [2021-03-27 18:47:28](https://github.com/leanprover-community/mathlib/commit/27c8676)
refactor(geometry/manifold/algebra/smooth_functions): make `smooth_map_group` division defeq to `pi.has_div` ([#6912](https://github.com/leanprover-community/mathlib/pull/6912))
The motivation was the fact that this allows `smooth_map.coe_div` to be `rfl` but this should be more generally useful.

### [2021-03-27 15:21:25](https://github.com/leanprover-community/mathlib/commit/d104413)
chore(topology/metric_space): golf, generalize, rename ([#6849](https://github.com/leanprover-community/mathlib/pull/6849))
### Second countable topology
* generalize `metric.second_countable_of_almost_dense_set` to a pseudo
  emetric space, see
  `emetric.subset_countable_closure_of_almost_dense_set` (for sets)
  and `emetric.second_countable_of_almost_dense_set` (for the whole space);
* use it to generalize `emetric.countable_closure_of_compact` to a
  pseudo emetric space (replacing `closure t = s` with
  `s ⊆ closure t`) and prove that a sigma compact pseudo emetric space has
  second countable topology;
* generalize `second_countable_of_proper` to a pseudo metric space;
### `emetric.diam`
* rename `emetric.diam_le_iff_forall_edist_le` to `emetric.diam_le_iff`;
* rename `emetric.diam_le_of_forall_edist_le` to `emetric.diam_le`.

### [2021-03-27 06:35:11](https://github.com/leanprover-community/mathlib/commit/cc7e722)
refactor(representation_theory/maschke): replaces `¬(ring_char k ∣ fintype.card G)` with `invertible (fintype.card G : k)` instance ([#6901](https://github.com/leanprover-community/mathlib/pull/6901))
Refactors Maschke's theorem to take an instance of `invertible (fintype.card G : k)` instead of an explicit `not_dvd : ¬(ring_char k ∣ fintype.card G)`.
Provides that instance in the context `char_zero k`.
Allows `monoid_algebra.submodule.is_complemented` to be an instance.

### [2021-03-27 06:35:10](https://github.com/leanprover-community/mathlib/commit/d32f9c7)
feat(data/nat/log): add some lemmas and monotonicity ([#6899](https://github.com/leanprover-community/mathlib/pull/6899))

### [2021-03-27 06:35:09](https://github.com/leanprover-community/mathlib/commit/5ecb1f7)
feat(group_theory/order_of_element): order_of is the same in a submonoid ([#6876](https://github.com/leanprover-community/mathlib/pull/6876))
The first lemma shows that `order_of` is the same in a submonoid, but it seems like you also need a lemma for subgroups.

### [2021-03-27 03:05:14](https://github.com/leanprover-community/mathlib/commit/5c95d48)
chore(scripts): update nolints.txt ([#6902](https://github.com/leanprover-community/mathlib/pull/6902))
I am happy to remove some nolints for you!

### [2021-03-27 03:05:12](https://github.com/leanprover-community/mathlib/commit/3fe67c8)
feat(algebra/module): pull-back module structures along homomorphisms ([#6895](https://github.com/leanprover-community/mathlib/pull/6895))

### [2021-03-27 03:05:11](https://github.com/leanprover-community/mathlib/commit/4b261a8)
chore(algebra/smul_with_zero): add missing injective / surjective transferring functions ([#6892](https://github.com/leanprover-community/mathlib/pull/6892))

### [2021-03-27 03:05:10](https://github.com/leanprover-community/mathlib/commit/832a2eb)
refactor(topology/continuous_functions): change file layout ([#6890](https://github.com/leanprover-community/mathlib/pull/6890))
Moves `topology/bounded_continuous_function.lean` to `topology/continuous_functions/bounded.lean`, splitting out the content about continuous functions on a compact space to `topology/continuous_functions/compact.lean`.
Renames `topology/continuous_map.lean` to `topology/continuous_functions/basic.lean`.
Renames `topology/algebra/continuous_functions.lean` to `topology/continuous_functions/algebra.lean`.
Also changes the direction of the equivalences, replacing `bounded_continuous_function.equiv_continuous_map_of_compact` with `continuous_map.equiv_bounded_of_compact` (and also the more structured version).
There's definitely more work to be done here, particularly giving at least some lemmas characterising the norm on `C(α, β)`, but I wanted to do a minimal PR changing the layout first.

### [2021-03-27 03:05:09](https://github.com/leanprover-community/mathlib/commit/99c23ea)
refactor(analysis/normed_space/basic): add semi_normed_group ([#6888](https://github.com/leanprover-community/mathlib/pull/6888))
This is part of a series of PR to have semi_normed_group (and related concepts) in mathlib.
 
To keep the PR as small as possibile I just added the new class `semi_normed_group`. I didn't introduce anything like `semi_normed_ring` and I didn't do anything about morphisms.

### [2021-03-27 03:05:08](https://github.com/leanprover-community/mathlib/commit/bc33f1a)
feat(group_theory/perm/cycles): is_cycle_of_is_cycle_pow ([#6871](https://github.com/leanprover-community/mathlib/pull/6871))
If `g ^ n` is a cycle, and if `g ^ n` doesn't have smaller support, then `g` is a cycle.

### [2021-03-27 03:05:07](https://github.com/leanprover-community/mathlib/commit/5eead09)
feat(algebra/big_operators/basic): add lemmas for a product with two non one factors ([#6826](https://github.com/leanprover-community/mathlib/pull/6826))
Add another version of `prod_eq_one` and 3 versions of `prod_eq_double`, a lemma that says a product with only 2 non one factors is equal to the product of the 2 factors.

### [2021-03-27 03:05:06](https://github.com/leanprover-community/mathlib/commit/cfd1a4c)
feat(linear_algebra/bilinear_form): generalize some constructions to the noncomm case ([#6824](https://github.com/leanprover-community/mathlib/pull/6824))
Introduce an operation `flip` on a bilinear form, which swaps the arguments.  Generalize the construction `bilin_form.to_lin` (which currently exists for commutative rings) to a weaker construction `bilin_form.to_lin'` for arbitrary rings.
Rename lemmas
`sesq_form.map_sum_right` -> `sesq_form.sum_right`
`sesq_form.map_sum_left` -> `sesq_form.sum_left`
`bilin_form.map_sum_right` -> `bilin_form.sum_right`
`bilin_form.map_sum_left` -> `bilin_form.sum_left`
`to_linear_map_apply` (sic, no namespace) -> `bilin_form.to_lin_apply`

### [2021-03-27 03:05:05](https://github.com/leanprover-community/mathlib/commit/ec26d96)
feat(order/lattice): add complete_semilattice_Sup/Inf ([#6797](https://github.com/leanprover-community/mathlib/pull/6797))
This adds `complete_semilattice_Sup` and `complete_semilattice_Inf` above `complete_lattice`.
This has not much effect, as in fact either implies `complete_lattice`. However it's useful at times to have these, when you can naturally define just one half of the structure at a time (e.g. the subobject lattice in a general category, where for `Sup` we need coproducts and images, while for the `Inf` we need wide pullbacks).
There are many places in mathlib that currently use `complete_lattice_of_Inf`. It might be slightly nicer to instead construct a `complete_semilattice_Inf`, and then use the new `complete_lattice_of_complete_semilattice_Inf`, but I haven't done that here.

### [2021-03-26 23:52:29](https://github.com/leanprover-community/mathlib/commit/e36656e)
chore(category_theory/monoidal): golf some proofs ([#6894](https://github.com/leanprover-community/mathlib/pull/6894))
Golfs proofs of `tensor_left_iff`, `tensor_right_iff`, `left_unitor_tensor'`, `right_unitor_tensor` and `unitors_equal` - in particular removes the file `monoidal/unitors` as all it contained was a proof of `unitors_equal` which is a two line proof.

### [2021-03-26 23:52:28](https://github.com/leanprover-community/mathlib/commit/e21b4bc)
chore(data/equiv/transfer_instance): reuse existing proofs ([#6868](https://github.com/leanprover-community/mathlib/pull/6868))
This makes all the proofs in this file identical. It's unfortunate that the `letI`s have to be written out in each case,

### [2021-03-26 23:52:27](https://github.com/leanprover-community/mathlib/commit/9e00c2b)
feat(ring_theory/int/basic): Induction, nat_abs and units ([#6733](https://github.com/leanprover-community/mathlib/pull/6733))
Proves : 
 * Induction on primes (special case for nat)
 * In `int`, a number and its `nat_abs` are associated
 * An integer is prime iff its `nat_abs` is prime
 * Two integers are associated iff they are equal or opposites
 * Classification of the units in `int` (trivial but handy lemma)

### [2021-03-26 22:21:04](https://github.com/leanprover-community/mathlib/commit/ca7dca3)
feat(geometry/manifold/algebra/smooth_functions): simp lemmas for coercions to functions ([#6893](https://github.com/leanprover-community/mathlib/pull/6893))
These came up while working on the branch `replace_algebra_def` but seem worth adding
in their own right.

### [2021-03-26 18:26:23](https://github.com/leanprover-community/mathlib/commit/902b01d)
chore(algebra/group): rename `is_unit_unit` to `units.is_unit` ([#6886](https://github.com/leanprover-community/mathlib/pull/6886))

### [2021-03-26 18:26:22](https://github.com/leanprover-community/mathlib/commit/e43d964)
chore(data/pi,algebra/group/pi): reorganize proofs ([#6869](https://github.com/leanprover-community/mathlib/pull/6869))
Add `pi.single_op` and `pi.single_binop` and use them in the proofs.

### [2021-03-26 18:26:20](https://github.com/leanprover-community/mathlib/commit/3566cbb)
feat(*): add more lemmas about `set.piecewise` ([#6862](https://github.com/leanprover-community/mathlib/pull/6862))

### [2021-03-26 18:26:19](https://github.com/leanprover-community/mathlib/commit/ef7fe6f)
feat(dynamics/ergodic/conservative): define conservative systems, formalize Poincaré recurrence thm ([#2311](https://github.com/leanprover-community/mathlib/pull/2311))

### [2021-03-26 14:24:21](https://github.com/leanprover-community/mathlib/commit/f0bfb25)
feat(geometry/manifold/mfderiv): differentiability of `f : E ≃L[𝕜] E'` ([#6850](https://github.com/leanprover-community/mathlib/pull/6850))

### [2021-03-26 14:24:20](https://github.com/leanprover-community/mathlib/commit/2b71c80)
feat(linear_algebra/dual): add the dual map ([#6807](https://github.com/leanprover-community/mathlib/pull/6807))

### [2021-03-26 14:24:19](https://github.com/leanprover-community/mathlib/commit/8addf9a)
feat(topology/bcf): better dist_lt_of_* lemmas ([#6781](https://github.com/leanprover-community/mathlib/pull/6781))

### [2021-03-26 14:24:17](https://github.com/leanprover-community/mathlib/commit/6ae9f00)
feat(ring_theory/polynomial/symmetric): degrees_esymm ([#6718](https://github.com/leanprover-community/mathlib/pull/6718))
A lot of API also added for finset, finsupp, multiset, powerset_len

### [2021-03-26 11:55:37](https://github.com/leanprover-community/mathlib/commit/34a3317)
feat(group_theory/perm/sign): power has smaller support ([#6872](https://github.com/leanprover-community/mathlib/pull/6872))
The support of `g ^ n` is contained in the support of `g`.

### [2021-03-26 11:55:36](https://github.com/leanprover-community/mathlib/commit/adc5f9d)
feat(ring_theory/ideal/operations): add an instance ([#6717](https://github.com/leanprover-community/mathlib/pull/6717))
This instance has been suggested by @eric-wieser in [#6640](https://github.com/leanprover-community/mathlib/pull/6640).
On my machine I get a deterministic timeout in `ring_theory/finiteness` at line 325, but in principle it seems a useful instance to have.

### [2021-03-26 08:06:47](https://github.com/leanprover-community/mathlib/commit/fb49529)
chore(topology/sheaves): speed up a slow proof ([#6879](https://github.com/leanprover-community/mathlib/pull/6879))
In another branch this proof mysteriously becomes slightly too slow, so I'm offering a pre-emptive speed up, just replacing `simp` with `rw`.

### [2021-03-26 08:06:45](https://github.com/leanprover-community/mathlib/commit/c658f5c)
refactor(algebra/field): allow custom `div` ([#6874](https://github.com/leanprover-community/mathlib/pull/6874))

### [2021-03-26 08:06:44](https://github.com/leanprover-community/mathlib/commit/c07c310)
feat(group_theory/perm_basic): Lemma swap_apply_apply ([#6870](https://github.com/leanprover-community/mathlib/pull/6870))
A useful rw lemma.

### [2021-03-26 08:06:42](https://github.com/leanprover-community/mathlib/commit/0977b20)
feat(measure_theory/interval_integral): weaken assumption in `integral_non_ae_measurable` ([#6858](https://github.com/leanprover-community/mathlib/pull/6858))
I don't see any reason for having a strict inequality here.

### [2021-03-26 08:06:41](https://github.com/leanprover-community/mathlib/commit/03f0bb1)
refactor(topology/algebra): define `has_continuous_smul`, use for topological semirings and algebras ([#6823](https://github.com/leanprover-community/mathlib/pull/6823))

### [2021-03-26 08:06:39](https://github.com/leanprover-community/mathlib/commit/5c93c2d)
feat(category_theory/triangulated/rotate): add definition of rotation and inverse rotation of triangles and their morphisms ([#6803](https://github.com/leanprover-community/mathlib/pull/6803))
This PR adds the definition of rotation and inverse rotation of triangles and triangle morphisms.
It also shows that rotation is an equivalence on the category of triangles in an additive category.

### [2021-03-26 08:06:38](https://github.com/leanprover-community/mathlib/commit/5c856c3)
feat(topology/vector_bundle): definition of topological vector bundle ([#4658](https://github.com/leanprover-community/mathlib/pull/4658))
# Topological vector bundles
In this file we define topological vector bundles.
Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.
To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:
* `F` should be a topological vector space over a field `𝕜`;
* There should be a topology on `bundle.total_space E`, for which the projection to `E` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `𝕜`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.
If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle 𝕜 F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.
The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `𝕜`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[𝕜] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[𝕜] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[𝕜] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.
Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.
Coauthored-by: Sebastien Gouezel  <sebastien.gouezel@univ-rennes1.fr>

### [2021-03-26 03:02:05](https://github.com/leanprover-community/mathlib/commit/b797d51)
chore(scripts): update nolints.txt ([#6885](https://github.com/leanprover-community/mathlib/pull/6885))
I am happy to remove some nolints for you!

### [2021-03-25 21:40:33](https://github.com/leanprover-community/mathlib/commit/e6d01b8)
feat(topology/bounded_continuous_function): add `coe_mul`, `mul_apply` ([#6867](https://github.com/leanprover-community/mathlib/pull/6867))
Partners of the extant `coe_smul`, `smul_apply` lemmas (see line 630).
These came up while working on the `replace_algebra_def` branch but
seem worth adding independently.

### [2021-03-25 21:40:32](https://github.com/leanprover-community/mathlib/commit/b670391)
chore(algebra/group/{pi,prod}): add missing instances ([#6866](https://github.com/leanprover-community/mathlib/pull/6866))

### [2021-03-25 21:40:31](https://github.com/leanprover-community/mathlib/commit/6e14e8f)
feat(data/equiv/mul_add): define `mul_hom.inverse` ([#6864](https://github.com/leanprover-community/mathlib/pull/6864))

### [2021-03-25 19:35:08](https://github.com/leanprover-community/mathlib/commit/e054705)
refactor(topology/metric_space/antilipschitz): generalize to pseudo_metric_space ([#6841](https://github.com/leanprover-community/mathlib/pull/6841))
This is part of a series of PR to introduce semi_normed_group in mathlib.
We introduce here anti Lipschitz maps for `pseudo_emetric_space`.

### [2021-03-25 19:35:07](https://github.com/leanprover-community/mathlib/commit/b299d14)
feat(algebra/geom_sum): rename geom_series to geom_sum, adds a lemma for the geometric sum ([#6828](https://github.com/leanprover-community/mathlib/pull/6828))
Declarations with names including `geom_series` have been renamed to use `geom_sum`, instead.
Also adds the lemma `geom_sum₂_succ_eq`: `geom_sum₂ x y (n + 1) = x ^ n + y * (geom_sum₂ x y n)`

### [2021-03-25 15:21:05](https://github.com/leanprover-community/mathlib/commit/1be91a1)
chore(order/filter/lift,topology/algebra/ordered): drop `[nonempty ι]` ([#6861](https://github.com/leanprover-community/mathlib/pull/6861))
* add `set.powerset_univ`, `filter.lift_top`, `filter.lift'_top`;
* remove `[nonempty ι]` from `filter.lift'_infi_powerset` and `tendsto_Icc_class_nhds_pi`.

### [2021-03-25 10:59:25](https://github.com/leanprover-community/mathlib/commit/879273e)
feat(logic/basic, logic/function/basic): make `cast` the simp-normal form of `eq.mp` and `eq.mpr`, add lemmas ([#6834](https://github.com/leanprover-community/mathlib/pull/6834))
This adds the fact that `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` are bijective, as well as some simp lemmas that follow from their injectivity.

### [2021-03-25 03:23:45](https://github.com/leanprover-community/mathlib/commit/81e8a13)
chore(scripts): update nolints.txt ([#6856](https://github.com/leanprover-community/mathlib/pull/6856))
I am happy to remove some nolints for you!

### [2021-03-25 03:23:44](https://github.com/leanprover-community/mathlib/commit/ec77f22)
chore(measure_theory/measure): add `exists_measurable_superset_forall_eq` ([#6853](https://github.com/leanprover-community/mathlib/pull/6853))

### [2021-03-25 03:23:43](https://github.com/leanprover-community/mathlib/commit/5a72daf)
feat(data/equiv/basic): add a computable version of equiv.set.range ([#6821](https://github.com/leanprover-community/mathlib/pull/6821))
If a left-inverse of `f` is known, it can be used to construct the equiv both computably and with control over definitional reduction.
This adds the definition `equiv.set.range_of_left_inverse` to mirror `linear_equiv.of_left_inverse` and `ring_equiv.of_left_inverse`.

### [2021-03-25 03:23:42](https://github.com/leanprover-community/mathlib/commit/c3034c2)
feat(data/indicator_function): add multiplicative version ([#6794](https://github.com/leanprover-community/mathlib/pull/6794))
We need it for `finprod`

### [2021-03-24 23:20:35](https://github.com/leanprover-community/mathlib/commit/19e214e)
feat(algebra/normed_space/basic,algebra/group_with_zero/power): real.(f)?pow_{even,bit0}_norm and field fpow lemmas ([#6757](https://github.com/leanprover-community/mathlib/pull/6757))
Simplifcation of `norm` when to an even numeral power.
Additionally, add `fpow` lemmas to match `pow` lemmas, and change `fpow_nonneg_to_nonneg` to `fpow_nonneg` to match `pow` naming.

### [2021-03-24 23:20:34](https://github.com/leanprover-community/mathlib/commit/039dfd2)
refactor(data/finsupp): add decidable_eq ([#6333](https://github.com/leanprover-community/mathlib/pull/6333))
... when the statement (not the proof) of the theorem depends on a
decidability assumption. This prevents instance mismatch issues in
downstream theorems.

### [2021-03-24 19:57:27](https://github.com/leanprover-community/mathlib/commit/77c3bfe)
chore(data/zmod/basic): make `fin.comm_ring.sub` defeq to `fin.sub` ([#6848](https://github.com/leanprover-community/mathlib/pull/6848))
This is only possible now that `fin.sub` is not saturating, and we allow `sub` and `neg` to be defined separately.

### [2021-03-24 19:57:24](https://github.com/leanprover-community/mathlib/commit/ab2c44c)
feat(algebra/big_operators/ring): add finset.prod_[one_]sub_ordered ([#6811](https://github.com/leanprover-community/mathlib/pull/6811))
Add 2 lemmas useful for partition of unity, `finset.prod_sub_ordered` and `finset.prod_one_sub_ordered`.
Also add an explicit `[decidable_eq]` assumption to `finset.induction_on_max` (without it some `rw`s failed).

### [2021-03-24 16:04:14](https://github.com/leanprover-community/mathlib/commit/b4373e5)
feat(tactic/lint): linter for @[class] def ([#6061](https://github.com/leanprover-community/mathlib/pull/6061))
Also cleaning up some uses of `@[class] def` that were missed in [#6028](https://github.com/leanprover-community/mathlib/pull/6028).

### [2021-03-24 13:49:38](https://github.com/leanprover-community/mathlib/commit/a756333)
chore(algebra/algebra/subalgebra): Add missing coe_sort for subalgebra ([#6800](https://github.com/leanprover-community/mathlib/pull/6800))
Unlike all the other subobject types, `subalgebra` does not implement `has_coe_to_sort` directly, instead going via a coercion to one of `submodule` and `subsemiring`.
This removes the `has_coe (subalgebra R A) (subsemiring A)` and `has_coe (subalgebra R A) (submodule R A)` instances; we don't have these for any other subobjects, and they cause the elaborator more difficulty than the corresponding `to_subsemiring` and `to_submodule` projections.
This changes the definition of `le` to not involve coercions, which matches `submodule` but requires a few proofs to change.
This speeds up the `lift_of_splits` proof by adding `finite_dimensional.of_subalgebra_to_submodule`.

### [2021-03-24 09:40:12](https://github.com/leanprover-community/mathlib/commit/144e9c4)
chore(*): removing some completed TODOs ([#6844](https://github.com/leanprover-community/mathlib/pull/6844))

### [2021-03-24 09:40:11](https://github.com/leanprover-community/mathlib/commit/6773016)
chore(category_theory/triangulated): cleanup ([#6827](https://github.com/leanprover-community/mathlib/pull/6827))

### [2021-03-24 05:49:35](https://github.com/leanprover-community/mathlib/commit/beb2cc9)
feat(algebra/category): subobjects in the category of R-modules ([#6842](https://github.com/leanprover-community/mathlib/pull/6842))

### [2021-03-24 05:49:34](https://github.com/leanprover-community/mathlib/commit/935003e)
chore(data/nat/basic): add @[simp] to some lemmas about numerals ([#6652](https://github.com/leanprover-community/mathlib/pull/6652))
Allows the simplifier to make more progress in equalities of numerals (both in nat, and in `[(semi)ring R] [no_zero_divisors R] [char_zero R]`). Also adds `@[simp]` to `nat.succ_ne_zero` and `nat.succ_ne_self`.

### [2021-03-24 02:11:42](https://github.com/leanprover-community/mathlib/commit/e0a7918)
chore(scripts): update nolints.txt ([#6843](https://github.com/leanprover-community/mathlib/pull/6843))
I am happy to remove some nolints for you!

### [2021-03-24 02:11:41](https://github.com/leanprover-community/mathlib/commit/94a4a95)
feat(logic/basic): `is_trans Prop iff` instance ([#6836](https://github.com/leanprover-community/mathlib/pull/6836))
If you've ever wondered why `trans h1 h2` works for `≤` but not for `↔`, this is the reason.

### [2021-03-24 02:11:40](https://github.com/leanprover-community/mathlib/commit/a008609)
doc(topology/sheaves/presheaf_of_functions): fix some documentation t… ([#6835](https://github.com/leanprover-community/mathlib/pull/6835))
makes variable names in the documentation match up with the names in the code

### [2021-03-24 02:11:39](https://github.com/leanprover-community/mathlib/commit/36fc1ca)
feat(algebraic_geometry/prime_spectrum): prime spectrum analogue of Hilberts Nullstellensatz ([#6805](https://github.com/leanprover-community/mathlib/pull/6805))
Referring to a TODO comment in `algebraic_geometry/prime_spectrum.lean`, which I presume is outdated.

### [2021-03-24 02:11:38](https://github.com/leanprover-community/mathlib/commit/12170e2)
feat(topology/algebra/continuous_functions): separates points ([#6783](https://github.com/leanprover-community/mathlib/pull/6783))

### [2021-03-23 23:08:24](https://github.com/leanprover-community/mathlib/commit/fd5f433)
fix(algebraic_topology): added FQNs to simplicial locale ([#6838](https://github.com/leanprover-community/mathlib/pull/6838))
This fix, which fully qualifies some notation, makes it so that
```
import algebraic_topology.simplicial_set
open_locale simplicial
```
works without errors.

### [2021-03-23 23:08:23](https://github.com/leanprover-community/mathlib/commit/ee5e9fb)
feat(data/indicator_function): eq_self_of_superset ([#6829](https://github.com/leanprover-community/mathlib/pull/6829))

### [2021-03-23 23:08:21](https://github.com/leanprover-community/mathlib/commit/aadd853)
feat(algebra/category): add more variants of Module.as_hom ([#6822](https://github.com/leanprover-community/mathlib/pull/6822))

### [2021-03-23 23:08:19](https://github.com/leanprover-community/mathlib/commit/b6e4d0b)
feat(combinatorics/quiver): every connected graph has a spanning tree ([#6806](https://github.com/leanprover-community/mathlib/pull/6806))
Prove a directed version of the fact that a connected graph has a
spanning tree. The subtree we use is what you would get from 'running a
DFS from the root'. This proof avoids any use of Zorn's lemma. Currently
we have no notion of undirected tree, but once that is in place, this
proof should also give undirected spanning trees.

### [2021-03-23 19:49:37](https://github.com/leanprover-community/mathlib/commit/315faac)
feat(data/multiset/basic): generalize rel.mono, rel_map ([#6771](https://github.com/leanprover-community/mathlib/pull/6771))

### [2021-03-23 19:49:36](https://github.com/leanprover-community/mathlib/commit/9cda1ff)
fix(data/complex/module): kill a non-defeq diamond  ([#6760](https://github.com/leanprover-community/mathlib/pull/6760))
`restrict_scalars.semimodule ℝ ℂ ℂ  = complex.semimodule` is currently not definitionally true. The PR tweaks the smul definition to make sure that this becomes true. This solves a diamond that appears naturally in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.60inner_product_space.20.E2.84.9D.20%28euclidean_space.20.F0.9D.95.9C.20n%29.60.3F/near/230780186

### [2021-03-23 19:49:35](https://github.com/leanprover-community/mathlib/commit/9893a26)
chore(field_theory/splitting_field): module doc and generalise one lemma ([#6739](https://github.com/leanprover-community/mathlib/pull/6739))
This PR provides a module doc for `field_theory.splitting_field`, which is the last file without module doc in `field_theory`. Furthermore, I took the opportunity of renaming the fields in that file from `\alpha`, `\beta`, `\gamma` to `K`, `L`, `F` to make it more readable for newcomers.
Moved `nat_degree_multiset_prod`, to `algebra.polynomial.big_operators`). In order to get the `no_zero_divisors` instance on `polynomial R`, I had to include `data.polynomial.ring_division` in that file. Furthermore, with the help of Damiano, generalised this lemma to `no_zero_divisors R`.
Coauthored by: Damiano Testa adomani@gmail.com

### [2021-03-23 19:49:34](https://github.com/leanprover-community/mathlib/commit/c521336)
feat(data/polynomial/bernstein): identities ([#6470](https://github.com/leanprover-community/mathlib/pull/6470))

### [2021-03-23 19:49:32](https://github.com/leanprover-community/mathlib/commit/edfe7e1)
feat(combinatorics/simple_graph): degree lemmas ([#5966](https://github.com/leanprover-community/mathlib/pull/5966))
Proves some lemmas about the minimum/maximum degree of vertices in a graph - also weakens the assumptions for the definitions, following the usual mathlib pattern of defining total functions.

### [2021-03-23 15:29:30](https://github.com/leanprover-community/mathlib/commit/61ed14e)
lint(*): split long lines ([#6833](https://github.com/leanprover-community/mathlib/pull/6833))

### [2021-03-23 15:29:29](https://github.com/leanprover-community/mathlib/commit/7803435)
refactor(topology/metric_space/lipschitz): generalize to pseudo_emetric_space ([#6831](https://github.com/leanprover-community/mathlib/pull/6831))
This is part of a series of PR to introduce `semi_normed_group` in mathlib.
We introduce here Lipschitz maps for `pseudo_emetric_space` (I also improve some theorem name in `topology/metric_space/emetric_space`).

### [2021-03-23 15:29:28](https://github.com/leanprover-community/mathlib/commit/489f522)
feat(category_theory/subobject): API for working with inequalities ([#6818](https://github.com/leanprover-community/mathlib/pull/6818))
This PR adds two types of declarations:
* Helper functions for showing that two subobjects are equal by giving a compatible isomorphism, and
* functions `of_le`/`of_le_mk`/`of_mk_le`/`of_mk_le_mk` that produce a morphism between the underlying objects from a proof of `X ≤ Y`. These are in essence just thin wrappers around `underlying.map`.

### [2021-03-23 15:29:25](https://github.com/leanprover-community/mathlib/commit/736b1e8)
feat(data/fintype/basic): add decidable_mem_range_fintype ([#6817](https://github.com/leanprover-community/mathlib/pull/6817))

### [2021-03-23 15:29:24](https://github.com/leanprover-community/mathlib/commit/c2e9ec0)
feat(group_theory/subgroup): add {monoid,add_monoid,ring}_hom.lift_of_right_inverse ([#6814](https://github.com/leanprover-community/mathlib/pull/6814))
This provides a computable alternative to `lift_of_surjective`.

### [2021-03-23 15:29:23](https://github.com/leanprover-community/mathlib/commit/5cafdff)
chore(algebra/group/basic): dedup, add a lemma ([#6810](https://github.com/leanprover-community/mathlib/pull/6810))
* drop `sub_eq_zero_iff_eq`, was a duplicate of `sub_eq_zero`;
* add a `simp` lemma `sub_eq_self : a - b = a ↔ b = 0`.

### [2021-03-23 06:50:41](https://github.com/leanprover-community/mathlib/commit/94f59d8)
feat(ring_theory/polynomial/homogenous): add a `direct_sum.gcomm_monoid` instance ([#6825](https://github.com/leanprover-community/mathlib/pull/6825))
This also corrects a stupid typo I made in `direct_sum.comm_ring` which was previously declared a `ring`!

### [2021-03-22 23:38:18](https://github.com/leanprover-community/mathlib/commit/9f56a0b)
refactor(tactic/ring): split off `ring_nf` tactic ([#6792](https://github.com/leanprover-community/mathlib/pull/6792))
[As requested on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring.20not.20idempotent/near/231178246) This splits the current behavior of `ring` into two tactics:
* `ring1`: closing tactic which solves equations in the goal only
* `ring_nf mode? (at h)?`: simplification tactic which puts ring expressions into normal form
The `ring` tactic will still call `ring1` with `ring_nf` as fallback, as it does currently, but in the latter case it will print a message telling the user to use `ring_nf` instead. The form `ring at h` is removed, because this never uses `ring1` so you should just call `ring_nf` directly.

### [2021-03-22 19:59:29](https://github.com/leanprover-community/mathlib/commit/a0a2177)
feat(data/support): add `function.mul_support` ([#6791](https://github.com/leanprover-community/mathlib/pull/6791))
This will help us add `finprod` in [#6355](https://github.com/leanprover-community/mathlib/pull/6355)

### [2021-03-22 16:18:52](https://github.com/leanprover-community/mathlib/commit/ffca31a)
feat(linear_algebra): composing with a linear equivalence does not change the image ([#6816](https://github.com/leanprover-community/mathlib/pull/6816))
I also did some minor reorganisation in order to relax some typeclass arguments.

### [2021-03-22 16:18:51](https://github.com/leanprover-community/mathlib/commit/e54f633)
feat(data/finsupp/basic): add `can_lift (α → M₀) (α →₀ M₀)` ([#6777](https://github.com/leanprover-community/mathlib/pull/6777))
Also add a few missing `simp`/`norm_cast` lemmas.

### [2021-03-22 16:18:49](https://github.com/leanprover-community/mathlib/commit/480b00c)
feat(algebra/group/type_tags): adding function coercion for `additive` and `multiplicative` ([#6657](https://github.com/leanprover-community/mathlib/pull/6657))
[As on zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/to_additive.20mismatch/near/230042978)

### [2021-03-22 10:12:29](https://github.com/leanprover-community/mathlib/commit/0b543c3)
feat(linear_algebra/dual): add dual_annihilator_sup_eq_inf_dual_annihilator ([#6808](https://github.com/leanprover-community/mathlib/pull/6808))

### [2021-03-22 10:12:28](https://github.com/leanprover-community/mathlib/commit/f3a4c48)
feat(algebra/subalgebra): missing norm_cast lemmas about operations ([#6790](https://github.com/leanprover-community/mathlib/pull/6790))

### [2021-03-22 07:20:26](https://github.com/leanprover-community/mathlib/commit/e7d74ba)
feat(algebra/smul_regular): add `M`-regular elements ([#6659](https://github.com/leanprover-community/mathlib/pull/6659))
This PR extends PR [#6590](https://github.com/leanprover-community/mathlib/pull/6590), that is now merged.  The current PR contains the actual API to work with `M`-regular elements `r : R`, called `is_smul_regular M r`.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews
From the doc-string:
### Action of regular elements on a module
We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `is_smul_regular`.
There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting an a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Smultiplications involving `0` are, of course, all trivial.
The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.
This property is the direct generalization to modules of the property `is_left_regular` defined in
`algebra/regular`.  Lemma `is_smul_regular.is_left_regular_iff` shows that indeed the two notions
coincide.

### [2021-03-22 01:19:20](https://github.com/leanprover-community/mathlib/commit/5be0b0c)
feat(data/finset/basic): add strong_induction and strong_induction_eq ([#6682](https://github.com/leanprover-community/mathlib/pull/6682))
An alternative to `finset.strong_induction_on` that has an associated equation lemma.

### [2021-03-21 20:45:07](https://github.com/leanprover-community/mathlib/commit/3f74b10)
chore(order/filter/bases): a few more constructors ([#6798](https://github.com/leanprover-community/mathlib/pull/6798))

### [2021-03-21 15:58:36](https://github.com/leanprover-community/mathlib/commit/852064a)
refactor(category_theory/subobject): split into smaller files ([#6796](https://github.com/leanprover-community/mathlib/pull/6796))
No change in content, just splitting into four files.

### [2021-03-21 11:05:45](https://github.com/leanprover-community/mathlib/commit/5d67033)
feat(topology/algebra/continuous_functions): missing lemmas ([#6782](https://github.com/leanprover-community/mathlib/pull/6782))

### [2021-03-21 03:36:01](https://github.com/leanprover-community/mathlib/commit/a22df99)
chore(scripts): update nolints.txt ([#6793](https://github.com/leanprover-community/mathlib/pull/6793))
I am happy to remove some nolints for you!

### [2021-03-21 03:36:00](https://github.com/leanprover-community/mathlib/commit/f331648)
feat(analysis/normed_space): normed_algebra.to_topological_algebra ([#6779](https://github.com/leanprover-community/mathlib/pull/6779))

### [2021-03-21 03:35:59](https://github.com/leanprover-community/mathlib/commit/abfddbf)
feat(ring_theory): define `left_mul_matrix` and `algebra.trace` ([#6653](https://github.com/leanprover-community/mathlib/pull/6653))
This PR defines the algebra trace, and the bilinear trace form, for an algebra `S` over a ring `R`, for example a field extension `L / K`.
Follow-up PRs will prove that `algebra.trace K L x` is the sum of the conjugate roots of `x` in `L`, that `trace_form` is nondegenerate and that `trace K L x` is integral over `K`. Then we'll use this to find an integral basis for field extensions, and then we can prove that the integral closure of a Dedekind domain is again a Dedekind domain.

### [2021-03-21 03:35:58](https://github.com/leanprover-community/mathlib/commit/b75ec5c)
feat(data/polynomial): Bernstein polynomials ([#6465](https://github.com/leanprover-community/mathlib/pull/6465))
The definition of the Bernstein polynomials
`bernstein_polynomial (R : Type*) [ring R] (n ν : ℕ) : polynomial R := (choose n ν) * X^ν * (1 - X)^(n - ν)`
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.
(Future work: use these to prove Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`.

### [2021-03-21 03:35:57](https://github.com/leanprover-community/mathlib/commit/4cc4207)
feat(algebra/module/linear_map): Add linear_map.iterate ([#6377](https://github.com/leanprover-community/mathlib/pull/6377))

### [2021-03-20 23:19:57](https://github.com/leanprover-community/mathlib/commit/e20c730)
feat(topology/continuous_map): formulas for sup and inf in terms of abs ([#6720](https://github.com/leanprover-community/mathlib/pull/6720))

### [2021-03-20 21:36:26](https://github.com/leanprover-community/mathlib/commit/3153153)
feat(measure_theory/interval_integral): add `integral_comp_mul_left` ([#6787](https://github.com/leanprover-community/mathlib/pull/6787))
I need this lemma for my work toward making integrals computable by `norm_num`.

### [2021-03-20 19:58:20](https://github.com/leanprover-community/mathlib/commit/240836a)
feat(analysis/normed_space/basic): generalize submodule.normed_space ([#6766](https://github.com/leanprover-community/mathlib/pull/6766))
This means that a ℂ-submodule of an ℝ-normed space is still an ℝ-normed space.
There's too much randomness in the profiling for me to tell if this speeds up or slows down `exists_extension_norm_eq`; but it does at least save a line there.

### [2021-03-20 17:42:10](https://github.com/leanprover-community/mathlib/commit/d650674)
feat(category_theory/subterminal): subterminal category equiv subobjects of terminal ([#6755](https://github.com/leanprover-community/mathlib/pull/6755))

### [2021-03-20 16:28:06](https://github.com/leanprover-community/mathlib/commit/86b8f39)
doc(docs/overview): Update overview ([#6772](https://github.com/leanprover-community/mathlib/pull/6772))
Update the overview to mention Abel-Ruffini.

### [2021-03-20 16:28:05](https://github.com/leanprover-community/mathlib/commit/5d7efa0)
feat(combinatorics/quiver): define quivers ([#6680](https://github.com/leanprover-community/mathlib/pull/6680))
Define quivers (a very permissive notion of graph), subquivers, paths
and arborescences, which are like rooted trees.
This PR comes from https://github.com/dwarn/nielsen-schreier-2 .

### [2021-03-20 15:04:09](https://github.com/leanprover-community/mathlib/commit/df4c9c9)
chore(ring_theory/adjoin/basic): golf some proofs about algebra.adjoin ([#6784](https://github.com/leanprover-community/mathlib/pull/6784))

### [2021-03-20 13:24:55](https://github.com/leanprover-community/mathlib/commit/9f77db2)
chore(topology/metric_space): add '@[continuity]' attributes ([#6780](https://github.com/leanprover-community/mathlib/pull/6780))

### [2021-03-20 10:08:03](https://github.com/leanprover-community/mathlib/commit/695d7f4)
refactor(algebraic_topology/simplex_category): Make simplex_category universe polymorphic. ([#6761](https://github.com/leanprover-community/mathlib/pull/6761))
This PR changes the definition of `simplex_category` so that it becomes universe polymorphic.
This is useful when we want to take (co)limits of simplicial objects indexed by categories constructed out of `simplex_category`.
This PR also makes a small wrapper around morphisms in `simplex_category` for hygiene purposes, and introduces a notation `X _[n]` for the n-th term of a simplicial object X.
Note: this PR makes `simplex_category` and `simplex_category.hom` irreducible.

### [2021-03-20 10:08:02](https://github.com/leanprover-community/mathlib/commit/4db82a4)
refactor(category_theory/cones): golf and cleanup cones ([#6756](https://github.com/leanprover-community/mathlib/pull/6756))
No mathematical content here, basically just golfing and tidying in preparation for future PRs.

### [2021-03-20 10:08:00](https://github.com/leanprover-community/mathlib/commit/56e5aa7)
feat(category_theory/closed): currying rfl lemmas ([#6754](https://github.com/leanprover-community/mathlib/pull/6754))
Add `rfl` lemmas for currying

### [2021-03-20 09:08:36](https://github.com/leanprover-community/mathlib/commit/b0150a5)
fix(analysis/special_functions/integrals): move lemmas out of namespace ([#6778](https://github.com/leanprover-community/mathlib/pull/6778))
Some lemmas should not have been moved into a namespace, so I fix that here.

### [2021-03-20 03:08:13](https://github.com/leanprover-community/mathlib/commit/26fcfbc)
feat(topology): continuous_pi_iff pi.has_continuous_mul pi.topological_group ([#6689](https://github.com/leanprover-community/mathlib/pull/6689))

### [2021-03-20 01:57:36](https://github.com/leanprover-community/mathlib/commit/07282da)
chore(scripts): update nolints.txt ([#6776](https://github.com/leanprover-community/mathlib/pull/6776))
I am happy to remove some nolints for you!

### [2021-03-19 22:17:14](https://github.com/leanprover-community/mathlib/commit/b4a2991)
feat(dynamics/ergodic): define measure preserving maps ([#6764](https://github.com/leanprover-community/mathlib/pull/6764))
Also prove some missing lemmas about measures.

### [2021-03-19 22:17:13](https://github.com/leanprover-community/mathlib/commit/eba4829)
feat(data/real/pi): Wallis product for pi ([#6568](https://github.com/leanprover-community/mathlib/pull/6568))

### [2021-03-19 19:07:52](https://github.com/leanprover-community/mathlib/commit/c65146d)
chore(data/finset/basic): erase_inj_on ([#6769](https://github.com/leanprover-community/mathlib/pull/6769))
Quick follow-up to [#6737](https://github.com/leanprover-community/mathlib/pull/6737)

### [2021-03-19 19:07:51](https://github.com/leanprover-community/mathlib/commit/2d2929f)
feat(measure_theory): define Hausdorff measure and Hausdorff dimension ([#6710](https://github.com/leanprover-community/mathlib/pull/6710))

### [2021-03-19 17:15:52](https://github.com/leanprover-community/mathlib/commit/152412f)
feat(analysis/special_functions/exp_log): log_nonzero_of_ne_one and log_inj_pos ([#6734](https://github.com/leanprover-community/mathlib/pull/6734))
log_nonzero_of_ne_one and log_inj_pos
Proves : 
 * When `x > 0`, `log(x)` is `0` iff `x = 1`
 * The real logarithm is injective (when restraining the domain to the positive reals)

### [2021-03-19 17:15:51](https://github.com/leanprover-community/mathlib/commit/6f3e0ad)
feat(ring_theory/multiplicity): Multiplicity with units ([#6729](https://github.com/leanprover-community/mathlib/pull/6729))
Renames `multiplicity.multiplicity_unit` into `multiplicity.is_unit_left`.
Adds : 
 * `multiplicity.is_unit_right`
 * `multiplicity.unit_left`
 * `multiplicity.unit_right`

### [2021-03-19 14:35:20](https://github.com/leanprover-community/mathlib/commit/591c34b)
refactor(linear_algebra/basic): move the lattice structure to its own file ([#6767](https://github.com/leanprover-community/mathlib/pull/6767))
The entire lattice structure is thoroughly uninteresting.
By moving it to its own shorter file, it should be easier to unify with the lattice of `submonoid`
I'd hope in future we can generate this automatically for any `subobject A` with an injection into `set A`.

### [2021-03-19 12:51:59](https://github.com/leanprover-community/mathlib/commit/ce107da)
feat(analysis/special_functions/integrals): integrating linear combinations of functions ([#6597](https://github.com/leanprover-community/mathlib/pull/6597))
Together with [#6357](https://github.com/leanprover-community/mathlib/pull/6357), this PR makes it possible to compute integrals of the form `∫ x in a..b, c * f x + d * g x` by `simp` (where `c` and `d` are constants and `f` and `g` are functions that are `interval_integrable` on `interval a b`.
Notably, this allows us to compute the integrals of polynomials by `norm_num`. Here's an example, followed by an example of a more random linear combination of `interval_integrable` functions:
```
import analysis.special_functions.integrals
open interval_integral real
open_locale real
example : ∫ x:ℝ in 0..2, 6*x^5 + 3*x^4 + x^3 - 2*x^2 + x - 7 = 1048 / 15 := by norm_num
example : ∫ x:ℝ in 0..1, exp x + 9 * x^8 + x^3 - x/2 + (1 + x^2)⁻¹ = exp 1 + π/4 := by norm_num
```

### [2021-03-19 09:01:18](https://github.com/leanprover-community/mathlib/commit/590f43d)
docs(category_theory): missing module docs ([#6752](https://github.com/leanprover-community/mathlib/pull/6752))
Module docs for a number of files under `category_theory/`.
This is largely a "low hanging fruit" selection; none of the files are particularly complicated.

### [2021-03-19 09:01:17](https://github.com/leanprover-community/mathlib/commit/c170128)
feat(number_theory/bernoulli): faulhaber' ([#6684](https://github.com/leanprover-community/mathlib/pull/6684))
This deduces an alternative form `faulhaber'` of Faulhaber's theorem from `faulhaber`. In this version, we 
1. sum over `1` to `n` instead of `0` to `n - 1` and
2. use `bernoulli'` instead of `bernoulli`.
Arguably, this is the more common form one finds Faulhaber's theorem in the literature.

### [2021-03-19 09:01:16](https://github.com/leanprover-community/mathlib/commit/86e1b17)
feat(field_theory/abel_ruffini): solvable by radicals implies solvable Galois group ([#6631](https://github.com/leanprover-community/mathlib/pull/6631))
Proves the theoretical part of insolvability of the quintic. We still need to exhibit a specific polynomial with non-solvable Galois group

### [2021-03-19 06:00:11](https://github.com/leanprover-community/mathlib/commit/62d532a)
feat(data/finset): erase is partially injective ([#6737](https://github.com/leanprover-community/mathlib/pull/6737))
Show that erase is partially injective, ie that if `s.erase x = s.erase y` and `x` is in `s`, then `x = y`.

### [2021-03-19 03:43:24](https://github.com/leanprover-community/mathlib/commit/a1305be)
chore(scripts): update nolints.txt ([#6763](https://github.com/leanprover-community/mathlib/pull/6763))
I am happy to remove some nolints for you!

### [2021-03-18 23:42:19](https://github.com/leanprover-community/mathlib/commit/cc11e44)
ci(*): lint 'Authors: ' line ([#6750](https://github.com/leanprover-community/mathlib/pull/6750))

### [2021-03-18 23:42:17](https://github.com/leanprover-community/mathlib/commit/c3e40be)
feat(data/equiv/local_equiv): define `piecewise` and `disjoint_union` ([#6700](https://github.com/leanprover-community/mathlib/pull/6700))
Also change some lemmas to use `set.ite`.

### [2021-03-18 19:27:39](https://github.com/leanprover-community/mathlib/commit/02f77ab)
doc(field_theory/normal): Add authors ([#6759](https://github.com/leanprover-community/mathlib/pull/6759))
Adds Patrick Lutz and I as authors to normal.lean. The last three-quarters of the file are from our work on Abel-Ruffini.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Author.20on.20normal.2Elean.3F

### [2021-03-18 19:27:37](https://github.com/leanprover-community/mathlib/commit/aea7dfb)
chore(algebra/char_p/basic): weaken assumptions integral_domain --> semiring+ ([#6753](https://github.com/leanprover-community/mathlib/pull/6753))
Taking advantage of the `no_zero_divisors` typeclass, the assumptions on some of the results can be weakened.

### [2021-03-18 19:27:36](https://github.com/leanprover-community/mathlib/commit/a10bc3d)
feat(normed_space/inner_product): euclidean_space.norm_eq ([#6744](https://github.com/leanprover-community/mathlib/pull/6744))

### [2021-03-18 19:27:35](https://github.com/leanprover-community/mathlib/commit/e1ff2df)
chore(*): update `injective` lemma names to match the naming guide ([#6740](https://github.com/leanprover-community/mathlib/pull/6740))
In `src/algebra/group_ring_action.lean`:
- `injective_to_semiring_hom` -> `to_semiring_hom_injective`
In `src/algebra/module/linear_map.lean`:
- `linear_equiv.injective_to_equiv` -> `linear_equiv.to_equiv_injective`
- `linear_equiv.injective_to_linear_map` -> `linear_equiv.to_linear_map_injective`
In `src/analysis/normed_space/enorm.lean`:
- `enorm.injective_coe_fn` -> `enorm.coe_fn_injective`
In `src/data/equiv/basic.lean`:
- `equiv.injective_coe_fn` -> `equiv.coe_fn_injective`
In `src/data/real/nnreal.lean`:
- `nnreal.injective_coe` -> `nnreal.coe_injective`
In `src/data/sum.lean`:
- `sum.injective_inl` -> `sum.inl_injective`
- `sum.injective_inr` -> `sum.inr_injective`
In `src/linear_algebra/affine_space/affine_equiv.lean`:
- `affine_equiv.injective_to_affine_map` -> `affine_equiv.to_affine_map_injective`
- `affine_equiv.injective_coe_fn` -> `affine_equiv.coe_fn_injective`
- `affine_equiv.injective_to_equiv` -> `affine_equiv.to_equiv_injective`
In `src/linear_algebra/affine_space/affine_map.lean`:
- `affine_map.injective_coe_fn` -> `affine_map.coe_fn_injective`
In `src/measure_theory/outer_measure.lean`:
- `measure_theory.outer_measure.injective_coe_fn` -> `measure_theory.outer_measure.coe_fn_injective`
In `src/order/rel_iso.lean`:
- `rel_iso.injective_to_equiv` -> `rel_iso.to_equiv_injective`
- `rel_iso.injective_coe_fn` -> `rel_iso.coe_fn_injective`
In `src/topology/algebra/module.lean`:
- `continuous_linear_map.injective_coe_fn` -> `continuous_linear_map.coe_fn_injective`

### [2021-03-18 19:27:33](https://github.com/leanprover-community/mathlib/commit/83b0981)
feat(ring_theory/polynomial): the symmetric and homogenous polynomials form a subalgebra and submodules, respectively ([#6666](https://github.com/leanprover-community/mathlib/pull/6666))
This adds:
* the new definitions:
  * `mv_polynomial.homogeneous_submodule σ R n`, defined as the `{ x | x.is_homogeneous n }`
  * `mv_polynomial.symmetric_subalgebra σ R`, defined as the `{ x | x.is_symmetric }`
* simp lemmas to reduce membership of the above to the `.is_*` form
* `mv_polynomial.homogenous_submodule_mul` a statement about the product of homogenous submodules
* `mv_polynomial.homogenous_submodule_eq_finsupp_supported` a statement that we already have a different definition of homogenous submodules elsewhere
All the other proofs have just been moved around the files.

### [2021-03-18 13:48:35](https://github.com/leanprover-community/mathlib/commit/744d59a)
refactor(category_theory/limits): split file ([#6751](https://github.com/leanprover-community/mathlib/pull/6751))
This splits `category_theory.limits.limits` into
`category_theory.limits.is_limit` and `category_theory.limits.has_limits`.
It doesn't meaningfully reduce imports, as everything imports `has_limits`, but in principle it could, and hopefully it makes the content slightly easier to understand when separated.
In any case, the file was certainly too large.

### [2021-03-18 13:48:34](https://github.com/leanprover-community/mathlib/commit/58581d0)
chore(*): normalize Authors: line ([#6749](https://github.com/leanprover-community/mathlib/pull/6749))

### [2021-03-18 13:48:33](https://github.com/leanprover-community/mathlib/commit/542ff6a)
refactor(algebra/algebra/basic): change submodule.restrict_scalars to use is_scalar_tower ([#6745](https://github.com/leanprover-community/mathlib/pull/6745))

### [2021-03-18 13:48:32](https://github.com/leanprover-community/mathlib/commit/59cda3b)
feat(algebra/associated): Primes that divide each other are associated ([#6732](https://github.com/leanprover-community/mathlib/pull/6732))
Primes that divide each other are associated

### [2021-03-18 13:48:31](https://github.com/leanprover-community/mathlib/commit/db2a972)
feat(ring_theory/principal_ideal_domain): The generator of a principal prime ideal is a prime ([#6731](https://github.com/leanprover-community/mathlib/pull/6731))
The generator of a principal prime ideal is a prime

### [2021-03-18 13:48:30](https://github.com/leanprover-community/mathlib/commit/b4afd64)
feat(data/padics/padic_norm): p-adic norm of primes other than p ([#6730](https://github.com/leanprover-community/mathlib/pull/6730))
The p-adic norm of `q` is `1` if `q` is another prime than `p`.

### [2021-03-18 09:41:26](https://github.com/leanprover-community/mathlib/commit/216aecd)
feat(group_theory/quaternion_group): define the (generalised) quaternion groups ([#6683](https://github.com/leanprover-community/mathlib/pull/6683))
This PR introduces the generalised quaternion groups and determines the orders of its elements.

### [2021-03-18 06:07:05](https://github.com/leanprover-community/mathlib/commit/8116851)
doc(category_theory): convert comments about universes to library note ([#6748](https://github.com/leanprover-community/mathlib/pull/6748))

### [2021-03-18 04:45:13](https://github.com/leanprover-community/mathlib/commit/e955a6b)
chore(scripts): update nolints.txt ([#6747](https://github.com/leanprover-community/mathlib/pull/6747))
I am happy to remove some nolints for you!

### [2021-03-18 03:01:54](https://github.com/leanprover-community/mathlib/commit/9b8d41a)
feat(ring_theory/finiteness): add transitivity of finite presentation ([#6640](https://github.com/leanprover-community/mathlib/pull/6640))
This adds transitivity of finite presentation (for rings). I think we now have a basic API for finitely presented algebras.

### [2021-03-17 23:52:47](https://github.com/leanprover-community/mathlib/commit/804b0ed)
chore(data/mv_polynomial/basic): add coeff_smul to match coeff_add etc ([#6742](https://github.com/leanprover-community/mathlib/pull/6742))

### [2021-03-17 22:49:08](https://github.com/leanprover-community/mathlib/commit/30b3455)
feat(ring_theory/roots_of_unity): Restrict ring homomorphism to roots of unity ([#6646](https://github.com/leanprover-community/mathlib/pull/6646))
Restrict a ring homomorphism to roots of unity.

### [2021-03-17 19:18:34](https://github.com/leanprover-community/mathlib/commit/9507a34)
chore(category_theory/limits/creates): fix typo in docstring ([#6738](https://github.com/leanprover-community/mathlib/pull/6738))

### [2021-03-17 19:18:33](https://github.com/leanprover-community/mathlib/commit/6e1143a)
chore(combinatorics/simple_graph): remove bad simp attribute ([#6736](https://github.com/leanprover-community/mathlib/pull/6736))
As in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/symmetry.20fails.20if.20simple.20graph.20is.20imported.

### [2021-03-17 19:18:32](https://github.com/leanprover-community/mathlib/commit/ce8a6ca)
refactor(data/multiset/basic): consistently use 'nsmul' in names ([#6735](https://github.com/leanprover-community/mathlib/pull/6735))

### [2021-03-17 19:18:31](https://github.com/leanprover-community/mathlib/commit/7e82bba)
feat(algebra/module/submodule): add `smul_of_tower_mem` ([#6712](https://github.com/leanprover-community/mathlib/pull/6712))
This adds the lemmas:
* `sub_mul_action.smul_of_tower_mem`
* `submodule.smul_of_tower_mem`
And uses them to construct the new scalar actions:
* `sub_mul_action.mul_action'`
* `sub_mul_action.is_scalar_tower`
* `submodule.semimodule'`
* `submodule.is_scalar_tower`
With associated lemmas
* `sub_mul_action.coe_smul_of_tower`
* `submodule.coe_smul_of_tower`
The unprimed instance continue to hold their old values, and exist to speed up typeclass search; the same pattern we use for `tensor_product.semimodule` vs `tensor_product.semimodule`.

### [2021-03-17 19:18:29](https://github.com/leanprover-community/mathlib/commit/4ae81c2)
feat(bounded_continuous_function): transport structure to C(α, β) when α compact ([#6701](https://github.com/leanprover-community/mathlib/pull/6701))

### [2021-03-17 19:18:25](https://github.com/leanprover-community/mathlib/commit/0b0fd52)
chore(analysis/normed_space/extend): provide a version without restrict_scalars ([#6693](https://github.com/leanprover-community/mathlib/pull/6693))
This is some pre-work to try and speed up the proof in `hahn_banach`, which as I understand it is super slow because it has to work very hard to unify typeclass which keep switching back and forth between `F` and `restrict_scalars ℝ 𝕜 F`. 
This PR is unlikely to have changed the speed of that proof, but I suspect these definitions might help in a future PR - and it pushes `restrict_scalars` out of the interesting bit of the proof.

### [2021-03-17 19:18:22](https://github.com/leanprover-community/mathlib/commit/6db70c9)
refactor(linear_algebra/determinant): refactor proof of upper_two_block_triangular_det ([#6690](https://github.com/leanprover-community/mathlib/pull/6690))
Refactored the proof of upper_two_block_triangular_det (to use sum_congr_hom.range) following a suggestion from Eric Wieser (during PR review of [#6050](https://github.com/leanprover-community/mathlib/pull/6050)).

### [2021-03-17 19:18:19](https://github.com/leanprover-community/mathlib/commit/4119181)
feat(measure_theory/l2_space): L2 is an inner product space ([#6596](https://github.com/leanprover-community/mathlib/pull/6596))
If `E` is an inner product space, then so is `Lp E 2 µ`, with inner product being the integral of the inner products between function values.

### [2021-03-17 19:18:17](https://github.com/leanprover-community/mathlib/commit/fb28eac)
feat(number_theory/bernoulli): Faulhaber's theorem ([#6409](https://github.com/leanprover-community/mathlib/pull/6409))
Co-authored-by Fabian Kruse

### [2021-03-17 16:20:31](https://github.com/leanprover-community/mathlib/commit/83a4b8b)
chore(group_theory/subgroup): fix typo in docstring ([#6722](https://github.com/leanprover-community/mathlib/pull/6722))

### [2021-03-17 16:20:30](https://github.com/leanprover-community/mathlib/commit/73922b5)
feat(data/zsqrtd/basic): add some lemmas about conj, norm ([#6715](https://github.com/leanprover-community/mathlib/pull/6715))

### [2021-03-17 12:41:30](https://github.com/leanprover-community/mathlib/commit/1f50530)
feat(data/set/intervals/image_preimage, algebra/ordered_monoid): new typeclass for interval bijection lemmas ([#6629](https://github.com/leanprover-community/mathlib/pull/6629))
This commit introduces a ``has_exists_add_of_le`` typeclass extending ``ordered_add_comm_monoid``; is the assumption needed so that additively translating an interval gives a bijection. We then prove this fact for all flavours of interval. 
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Correct.20setting.20for.20positive.20shifts.20of.20intervals

### [2021-03-17 10:17:23](https://github.com/leanprover-community/mathlib/commit/1345319)
feat(ring_theory/algebraic data/real/irrational): add a proof that a transcendental real number is irrational ([#6721](https://github.com/leanprover-community/mathlib/pull/6721))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/263328-triage

### [2021-03-17 10:17:22](https://github.com/leanprover-community/mathlib/commit/4b1d588)
chore(linear_algebra/determinant): redefine det using multilinear_map.alternatization ([#6708](https://github.com/leanprover-community/mathlib/pull/6708))
This slightly changes the definitional unfolding of `matrix.det` (moving a function application outside a sum and adjusting the version of int-multiplication used).
By doing this, a large number of proofs become a trivial application of a more general statement about alternating maps.
`det_row_multilinear` already existed prior to this commit, but now `det` is defined in terms of it instead of the other way around.
We still need both, as otherwise we would break `M.det` dot notation, as `det_row_multilinear` does not have its argument expressed as a matrix.

### [2021-03-17 10:17:21](https://github.com/leanprover-community/mathlib/commit/84933f1)
feat(ring_theory/polynomial): Pochhammer polynomials ([#6598](https://github.com/leanprover-community/mathlib/pull/6598))
# The Pochhammer polynomials
We define and prove some basic relations about
`pochhammer S n : polynomial S = X * (X+1) * ... * (X + n - 1)`
which is also known as the rising factorial.

### [2021-03-17 08:30:54](https://github.com/leanprover-community/mathlib/commit/861f594)
feat(field_theory/normal): Tower of solvable extensions is solvable ([#6643](https://github.com/leanprover-community/mathlib/pull/6643))
This is the key lemma that makes Abel-Ruffini work.

### [2021-03-17 08:30:53](https://github.com/leanprover-community/mathlib/commit/6f6b548)
refactor(group_theory/order_of_element): now makes sense for infinite monoids ([#6587](https://github.com/leanprover-community/mathlib/pull/6587))
This PR generalises `order_of` from finite groups to (potentially infinite) monoids. By convention, the value of `order_of` for an element of infinite order is `0`. This is non-standard for the order of an element, but agrees with the convention that the characteristic of a field is `0` if `1` has infinite additive order. It also enables to remove the assumption `0<n` for some lemmas about orders of elements of the dihedral group, which by convention is also the infinite dihedral group for `n=0`.
The whole file has been restructured to take into account that `order_of` now makes sense for monoids. There is still an open issue about adding [to_additive], but this should be done in a seperate PR. Also, some results could be generalised with assumption `0 < order_of a` instead of finiteness of the whole group.

### [2021-03-17 05:36:54](https://github.com/leanprover-community/mathlib/commit/3e7a56e)
feat(tactic/norm_num): support for nat.cast + int constructors ([#6235](https://github.com/leanprover-community/mathlib/pull/6235))
This adds support for the functions `nat.cast`, `int.cast`, `rat.cast`
as well as `int.to_nat`, `int.nat_abs` and the constructors of int
 `int.of_nat` and `int.neg_succ_of_nat`, at least in their simp-normal
 forms.

### [2021-03-17 03:47:21](https://github.com/leanprover-community/mathlib/commit/d292fd7)
refactor(topology/metric_space/basic): add pseudo_metric ([#6716](https://github.com/leanprover-community/mathlib/pull/6716))
This is the natural continuation of [#6694](https://github.com/leanprover-community/mathlib/pull/6694): we introduce here `pseudo_metric_space`.
Note that I didn't do anything fancy, I only generalize the results that work out of the box for pseudometric spaces (quite a lot indeed).
It's possible that there is some duplicate code, especially in the section about products.

### [2021-03-17 02:56:43](https://github.com/leanprover-community/mathlib/commit/3936f5f)
chore(scripts): update nolints.txt ([#6719](https://github.com/leanprover-community/mathlib/pull/6719))
I am happy to remove some nolints for you!

### [2021-03-17 01:14:27](https://github.com/leanprover-community/mathlib/commit/b9ccb8f)
feat(algebraic_topology/simplicial_objects + ...): Truncated simplicial objects + skeleton ([#6711](https://github.com/leanprover-community/mathlib/pull/6711))
This PR adds truncated simplicial objects and the skeleton functor (aka the truncation functor).

### [2021-03-17 01:14:26](https://github.com/leanprover-community/mathlib/commit/87c12ab)
feat(topology/continuous_map): lattice structures ([#6706](https://github.com/leanprover-community/mathlib/pull/6706))

### [2021-03-16 21:43:26](https://github.com/leanprover-community/mathlib/commit/40a0ac7)
chore(linear_algebra/finite_dimensional): change instance ([#6713](https://github.com/leanprover-community/mathlib/pull/6713))
With the new instance `finite_dimensional K K` Lean can deduce the old instance automatically. I don not completely understand why it needs the new instance (`apply_instance` proves it), probably this is related to the order of unfolding `finite_dimensional` and applying `is_noetherian` instances.

### [2021-03-16 21:43:25](https://github.com/leanprover-community/mathlib/commit/177020e)
feat(topology/separation): `(closure s).subsingleton ↔ s.subsingleton` ([#6707](https://github.com/leanprover-community/mathlib/pull/6707))
Also migrate `set.subsingleton_of_image` to `set.subsingleton`.

### [2021-03-16 21:43:23](https://github.com/leanprover-community/mathlib/commit/890066a)
feat(measure_theory/measure_space): define `quasi_measure_preserving` ([#6699](https://github.com/leanprover-community/mathlib/pull/6699))
* add `measurable.iterate`
* move section about `measure_space` up to make `volume_tac` available
  much earlier;
* add `map_of_not_measurable`;
* drop assumption `measurable f` in `map_mono`;
* add `tendsto_ae_map`;
* more API about `absolutely_continuous`;
* define `quasi_measure_preserving` and prove some properties.

### [2021-03-16 21:43:22](https://github.com/leanprover-community/mathlib/commit/f5f42bc)
chore(*): update to Lean 3.28.0c ([#6691](https://github.com/leanprover-community/mathlib/pull/6691))

### [2021-03-16 21:43:21](https://github.com/leanprover-community/mathlib/commit/a116025)
feat(geometry/manifold/mfderiv): more lemmas ([#6679](https://github.com/leanprover-community/mathlib/pull/6679))
* move section `mfderiv_fderiv` up, add aliases;
* rename old `unique_mdiff_on.unique_diff_on` to `unique_mdiff_on.unique_diff_on_target_inter`;
* add a section about `continuous_linear_map`;
* more lemmas about `model_with_corners`;
* add lemmas about `ext_chart_at`.

### [2021-03-16 21:43:20](https://github.com/leanprover-community/mathlib/commit/214b8e8)
feat(topology/algebra): more on closure ([#6675](https://github.com/leanprover-community/mathlib/pull/6675))

### [2021-03-16 19:18:11](https://github.com/leanprover-community/mathlib/commit/8d8c356)
chore(ring_theory/noetherian): add `fg_span` and `fg_span_singleton` ([#6709](https://github.com/leanprover-community/mathlib/pull/6709))

### [2021-03-16 19:18:09](https://github.com/leanprover-community/mathlib/commit/f221bfd)
feat(data/polynomial/degree/definitions): leading_coeff_X_pow_sub_C ([#6633](https://github.com/leanprover-community/mathlib/pull/6633))
Lemma for the leading coefficient of `X ^ n - C r`.

### [2021-03-16 19:18:08](https://github.com/leanprover-community/mathlib/commit/81dabda)
feat(data/buffer/parser/*): expand parser properties ([#6339](https://github.com/leanprover-community/mathlib/pull/6339))
Add several new properties to parsers:
`static`
`err_static`
`step`
`prog`
`bounded`
`unfailing`
`conditionally_unfailing`.
Most of these properties hold cleanly for existing core parsers, and are provided as classes. This allows nice derivation for any parsers that are made using parser combinators.
This PR is towards proving that the `nat` parser provides the maximal possible natural.
Other API lemmas are introduced for `string`, `buffer`, `char`, and `array`.

### [2021-03-16 16:06:27](https://github.com/leanprover-community/mathlib/commit/03a6c95)
chore(ring_theory/ideal): use `ideal.mul_mem_left` instead of `ideal.smul_mem` ([#6704](https://github.com/leanprover-community/mathlib/pull/6704))
Lots of proofs are relying on the fact that mul and smul are defeq, but this makes them hard to follow, as the goal state never contains the smul referenced by these lemmas.

### [2021-03-16 16:06:26](https://github.com/leanprover-community/mathlib/commit/d9fbe9d)
chore(geometry/manifold/times_cont_mdiff_map): add `times_cont_mdiff_map.mdifferentiable` ([#6703](https://github.com/leanprover-community/mathlib/pull/6703))

### [2021-03-16 16:06:25](https://github.com/leanprover-community/mathlib/commit/ffacd12)
feat(algebra/iterate_hom): add `equiv.perm.coe_pow` ([#6698](https://github.com/leanprover-community/mathlib/pull/6698))
Also rewrite `equiv.perm.perm_group` in a more explicit manner.

### [2021-03-16 16:06:23](https://github.com/leanprover-community/mathlib/commit/900963c)
refactor(topology/metric_space/emetric_space): add pseudo_emetric ([#6694](https://github.com/leanprover-community/mathlib/pull/6694))
Working on the Liquid Tensor Experiment, we realize we need seminorms ~~pseudonorms~~ (meaning we don't require `∥x∥ = 0 → x = 0`). For this reason I would like to include seminorms, pseudometric and pseudoemetric to mathlib. (We currently have `premetric_space`, my plan is to change the name to `pseudometric_space`, that seems to be the standard terminology.)
I started modifying `emetric_space` since it seems the more fundamental (looking at the structure of the imports). What I did here is to define a new class `pseudo_emetric_space`, generalize almost all the results about `emetric_space` to this case (I mean, all the results that are actually true) and at the end of the file I defined `emetric_space` and prove the remaining results. It is the first time I did a refactor like this, so I probably did something wrong, but at least it compiles on my computer.
I don't know why one proof in `measure_theory/ae_eq_fun_metric.lean` stopped working, the same proof in tactic mode works.

### [2021-03-16 10:12:38](https://github.com/leanprover-community/mathlib/commit/22eba86)
feat(*): add some missing `coe_*` lemmas ([#6697](https://github.com/leanprover-community/mathlib/pull/6697))
* add `submonoid.coe_pow`, `submonoid.coe_list_prod`,
  `submonoid.coe_multiset_prod`, `submonoid.coe_finset_prod`,
  `subring.coe_pow`, `subring.coe_nat_cast`, `subring.coe_int_cast`;
* add `rat.num_div_denom`;
* add `inv_of_pow`.

### [2021-03-16 10:12:37](https://github.com/leanprover-community/mathlib/commit/57de126)
refactor(category_theory/limits): use auto_param ([#6696](https://github.com/leanprover-community/mathlib/pull/6696))
Add an `auto_param`, making it slightly more convenient when build limits of particular shapes first, then all limits.

### [2021-03-16 10:12:36](https://github.com/leanprover-community/mathlib/commit/c0036af)
feat(category/is_iso): make is_iso a Prop ([#6662](https://github.com/leanprover-community/mathlib/pull/6662))
Perhaps long overdue, this makes `is_iso` into a Prop.
It hasn't been a big deal, as it was always a subsingleton. Nevertheless this is probably safer than carrying data around in the typeclass inference system. 
As a side effect `simple` is now a Prop as well.

### [2021-03-16 06:30:41](https://github.com/leanprover-community/mathlib/commit/6669a28)
feat(algebraic_topology/simplicial_object + ...): Add has_limits + has_colimits instances ([#6695](https://github.com/leanprover-community/mathlib/pull/6695))
This PR adds `has_limits` and `has_colimits` instances for the category of simplicial objects (assuming the existence of such an instance for the base category). The category of simplicial sets now has both limits and colimits, and we include a small example of a simplicial set (the circle) constructed as a colimit.
This PR also includes the following two components, which were required for the above:
1. A basic API for working with `ulift C` where `C` is a category. This was required to avoid some annoying universe issues in the definitions of `has_colimits` and `has_limits`.
2. A small shim that transports a `has_(co)limit` instance along an equivalence of categories.

### [2021-03-16 06:30:40](https://github.com/leanprover-community/mathlib/commit/6d7d169)
feat(topology): More lemmas from LTE, refactor `is_totally_disconnected` to use `set.subsingleton` ([#6673](https://github.com/leanprover-community/mathlib/pull/6673))
From the liquid tensor experiment

### [2021-03-16 04:37:30](https://github.com/leanprover-community/mathlib/commit/0176b42)
feat(ring_theory/finiteness): add `mv_polynomial_of_finite_presentation` ([#6512](https://github.com/leanprover-community/mathlib/pull/6512))
Add `mv_polynomial_of_finite_presentation`: the polynomial ring over a finitely presented algebra is finitely presented.

### [2021-03-16 03:41:52](https://github.com/leanprover-community/mathlib/commit/afe38ca)
chore(scripts): update nolints.txt ([#6702](https://github.com/leanprover-community/mathlib/pull/6702))
I am happy to remove some nolints for you!

### [2021-03-15 22:29:25](https://github.com/leanprover-community/mathlib/commit/f1b69a1)
feat(linear_algebra/quadratic_form): add nondegenerate_of_anisotropic ([#6692](https://github.com/leanprover-community/mathlib/pull/6692))

### [2021-03-15 22:29:23](https://github.com/leanprover-community/mathlib/commit/ddb4617)
refactor(topology/metric_space/isometry): move Kuratowski embedding to another file ([#6678](https://github.com/leanprover-community/mathlib/pull/6678))
This reduces the import dependencies of `topology.metric_space.isometry`.

### [2021-03-15 22:29:22](https://github.com/leanprover-community/mathlib/commit/cc48a5a)
feat(geometry/manifold/diffeomorph): expand API ([#6668](https://github.com/leanprover-community/mathlib/pull/6668))

### [2021-03-15 22:29:21](https://github.com/leanprover-community/mathlib/commit/bd386a8)
feat(measure_theory/outer_measure): golf, add lemmas ([#6664](https://github.com/leanprover-community/mathlib/pull/6664))
* `Union_of_tendsto_zero`, `Union_nat_of_monotone_of_tsum_ne_top`, `of_function_union_of_separated`:
  supporting lemmas for the upcoming definition of the Hausdorff
  measure (and more generally metric outer measures).
* `ext_nonempty`, `smul_supr`, `map_sup`, `map_supr`, `comap_supr`,
  `restrict_univ`, `restrict_empty`, `restrict_supr`, `map_comap`,
  `map_comap_le`, `map_comap_of_surjective`, `restrict_le_self`,
  `map_le_restrict_range`, `le_comap_map`, `comap_map`, `comap_top`,
  `top_apply'`, `map_top`, `map_top_of_surjective`: new API lemmas
  about `map`/`comap`/`restrict` and `sup`/`supr`/`top`;
* `is_greatest_of_function`, `of_function_eq_Sup`,
`comap_of_function`, `map_of_function_le`, `map_of_function`,
restrict_of_function`, `smul_of_function`: new lemmas about
`of_function`;
* `Inf_apply'`: a version of `Inf_apply` that assumes that another set
is nonempty;
* `infi_apply`, `infi_apply'`, `binfi_apply`, `binfi_apply'`,
`map_infi_le`, `comap_infi`, `map_infi`, `map_infi_comap`,
`map_binfi_comap`, `restrict_infi_restrict`, `restrict_infi`,
`restrict_binfi`: new lemmas about `map`/`comap`/`restrict` and
`Inf`/`infi`;
* `extend_congr`: `infi_congr_Prop` specialized for `extend`; why this
is not a `congr` lemma?
* `le_induced_outer_measure`: `le_of_function` for
`induced_outer_measure`;
* `trim_le_trim` → `trim_mono`: rename, use `monotone`;
* `exists_measurable_superset_forall_eq_trim`: a version of
`exists_measurable_superset_eq_trim` that works for countable families
of measures;
* `trim_binop`, `trim_op`: new helper lemmas to golf `trim_add` etc;
* `trim_sup`, `trim_supr`: new lemmas about `trim`.
* `map_mono`, `comap_mono`, `mono''`, `restrict_mono`, `trim_mono`:
`@[mono]` lemmas.

### [2021-03-15 18:15:30](https://github.com/leanprover-community/mathlib/commit/c358676)
feat(meta/expr): monadic analogue of expr.replace ([#6661](https://github.com/leanprover-community/mathlib/pull/6661))

### [2021-03-15 18:15:29](https://github.com/leanprover-community/mathlib/commit/3ec8c1d)
feat(algebra/direct_sum_graded): a direct_sum formed of powers of a submodule of an algebra inherits a ring structure ([#6550](https://github.com/leanprover-community/mathlib/pull/6550))
This also fixes some incorrect universe parameters to the `of_submodules` constructors.

### [2021-03-15 17:06:11](https://github.com/leanprover-community/mathlib/commit/d9dc30e)
feat(algebra/free): turn `free_magma.lift` into an equivalence ([#6672](https://github.com/leanprover-community/mathlib/pull/6672))
This will be convenient for some work I have in mind and is more consistent with the pattern used elsewhere, such as:
- [`free_algebra.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/free_algebra.html#free_algebra.lift)
- [`monoid_algebra.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/monoid_algebra.html#monoid_algebra.lift)
- [`universal_enveloping.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/lie/universal_enveloping.html#universal_enveloping_algebra.lift)
- ...

### [2021-03-15 15:39:13](https://github.com/leanprover-community/mathlib/commit/ae77628)
chore(geometry/manifold/times_cont_mdiff): add `prod_mk_space` versions of `prod_mk` lemmas ([#6681](https://github.com/leanprover-community/mathlib/pull/6681))
These lemmas are useful when dealing with maps `f : M → E' × F'` where
`E'` and `F'` are normed spaces. This means some code duplication with
`prod_mk` lemmas but I see no way to avoid this without making proofs
about `M → E' × F'` longer/harder.

### [2021-03-15 12:40:53](https://github.com/leanprover-community/mathlib/commit/e16ae24)
doc(readme): add Eric Wieser to maintainer list ([#6688](https://github.com/leanprover-community/mathlib/pull/6688))

### [2021-03-15 12:40:52](https://github.com/leanprover-community/mathlib/commit/b5f3832)
feat(topology/metric_space): introduce `is_metric_separated` ([#6685](https://github.com/leanprover-community/mathlib/pull/6685))

### [2021-03-15 12:40:51](https://github.com/leanprover-community/mathlib/commit/90db6fc)
feat(analysis/calculus/times_cont_diff): smoothness of `f : E → Π i, F i` ([#6674](https://github.com/leanprover-community/mathlib/pull/6674))
Also add helper lemmas/definitions about multilinear maps.

### [2021-03-15 09:03:13](https://github.com/leanprover-community/mathlib/commit/1f47833)
feat(algebra/*, * : [regular, smul_with_zero, module/basic]): introduce `mul_action_with_zero` and `M`-regular elements ([#6590](https://github.com/leanprover-community/mathlib/pull/6590))
This PR has been split and there are now two separate PRs.
* [#6590](https://github.com/leanprover-community/mathlib/pull/6590), this one, introducing `smul_with_zero` and `mul_action_with_zero`: two typeclasses to deal with multiplicative actions of `monoid_with_zero`, without the need to assume the presence of an addition!
* [#6659](https://github.com/leanprover-community/mathlib/pull/6659), introducing `M`-regular elements, called `smul_regular`: the analogue of `is_left_regular`, but defined for an action of `monoid_with_zero` on a module `M`.
This PR is a preparation for introducing `M`-regular elements.
From the doc-string:
### Introduce `smul_with_zero`
In analogy with the usual monoid action on a Type `M`, we introduce an action of a `monoid_with_zero` on a Type with `0`.
In particular, for Types `R` and `M`, both containing `0`, we define `smul_with_zero R M` to be the typeclass where the products `r • 0` and `0 • m` vanish for all `r ∈ R` and all `m ∈ M`.
Moreover, in the case in which `R` is a `monoid_with_zero`, we introduce the typeclass `mul_action_with_zero R M`, mimicking group actions and having an absorbing `0` in `R`.  Thus, the action is required to be compatible with
* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.
Next, in a separate file, I introduce `M`-regular elements for a `monoid_with_zero R` with a `mul_action_with_zero` on a module `M`.  The definition is simply to require that an element `a : R` is `M`-regular if the smultiplication `M → M`, given by `m ↦ a • m` is injective.
We also prove some basic facts about `M`-regular elements.
The PR further changes three further the files
* `data/polynomial/coeffs`;
* `topology/algebra/module.lean`;
* `analysis/normed_space/bounded_linear_maps`.
The changes are prompted by a failure in CI.  In each case, the change was tiny, mostly having to do with an exchange of a multiplication by a smultiplication or vice-versa.

### [2021-03-15 09:03:12](https://github.com/leanprover-community/mathlib/commit/abf2ab4)
feat(linear_algebra/quadratic_form): associated bilinear form over noncommutative rings ([#6585](https://github.com/leanprover-community/mathlib/pull/6585))
The `associated` bilinear form to a quadratic form is currently constructed for commutative rings, but nearly the same construction works without a commutativity hypothesis (the only part that fails is that the operation of performing the construction is now an `add_monoid_hom` rather than a `linear_map`.  I provide this construction, naming it `associated'`.
Needed for [#5814](https://github.com/leanprover-community/mathlib/pull/5814) (not exactly a dependency since we can merge a non-optimal version of that PR before this one is merged).

### [2021-03-15 07:04:07](https://github.com/leanprover-community/mathlib/commit/249fd4f)
refactor(data/polynomial,ring_theory): use big operators for polynomials ([#6616](https://github.com/leanprover-community/mathlib/pull/6616))
This untangles some more definitions on polynomials from finsupp.  This uses the same approach as in [#6605](https://github.com/leanprover-community/mathlib/pull/6605).

### [2021-03-15 01:08:57](https://github.com/leanprover-community/mathlib/commit/c5796c7)
chore(scripts): update nolints.txt ([#6686](https://github.com/leanprover-community/mathlib/pull/6686))
I am happy to remove some nolints for you!

### [2021-03-14 15:45:18](https://github.com/leanprover-community/mathlib/commit/0a16148)
feat(measure_theory/lp_space): add snorm_norm_rpow ([#6619](https://github.com/leanprover-community/mathlib/pull/6619))
The lemma `snorm_norm_rpow` states `snorm (λ x, ∥f x∥ ^ q) p μ = (snorm f (p * ennreal.of_real q) μ) ^ q`.
Also add measurability lemmas about pow/rpow.

### [2021-03-14 12:22:07](https://github.com/leanprover-community/mathlib/commit/feab14b)
fix(algebra/continued_fractions): fix import ([#6677](https://github.com/leanprover-community/mathlib/pull/6677))
Just fix an import

### [2021-03-14 10:50:39](https://github.com/leanprover-community/mathlib/commit/b48cf17)
feat(linear_algebra/alternating): Add dom_coprod ([#5269](https://github.com/leanprover-community/mathlib/pull/5269))
This implements a variant of the multiplication defined in the second half of [Proposition 22.24 of "Notes on Differential Geometry and Lie Groups" (Jean Gallier)](https://www.cis.upenn.edu/~cis610/diffgeom-n.pdf):
![image](https://user-images.githubusercontent.com/425260/104042315-3dfe7380-51d2-11eb-9b3a-bbbb52d180f0.png)

### [2021-03-14 06:52:22](https://github.com/leanprover-community/mathlib/commit/b52337a)
feat(topology/algebra/group): Add two easy lemmas ([#6669](https://github.com/leanprover-community/mathlib/pull/6669))
A topological group is discrete as soon as {1} is open.
The closure of a subgroup is a subgroup.
From the liquid tensor experiment.

### [2021-03-14 03:22:20](https://github.com/leanprover-community/mathlib/commit/464d04a)
feat(data/nat/fincard): introduce `nat.card`, `enat.card` ([#6670](https://github.com/leanprover-community/mathlib/pull/6670))
Defines `nat`- and `enat`-valued cardinality functions.

### [2021-03-14 03:22:18](https://github.com/leanprover-community/mathlib/commit/70662e1)
chore(data/rat/basic): a few trivial lemmas about `rat.denom` ([#6667](https://github.com/leanprover-community/mathlib/pull/6667))

### [2021-03-14 03:22:18](https://github.com/leanprover-community/mathlib/commit/69d7134)
feat(topology/basic): `f =ᶠ[𝓝 a] 0` iff `a ∉ closure (support f)` ([#6665](https://github.com/leanprover-community/mathlib/pull/6665))
Also add `equiv.image_symm_image` and `function.compl_support`.

### [2021-03-14 03:22:17](https://github.com/leanprover-community/mathlib/commit/c928e34)
feat(data/real/ennreal,topology/*): assorted lemmas ([#6663](https://github.com/leanprover-community/mathlib/pull/6663))
* add `@[simp]` to `ennreal.coe_nat_lt_coe_nat` and `ennreal.coe_nat_le_coe_nat`;
* add `ennreal.le_of_add_le_add_right`;
* add `set.nonempty.preimage`;
* add `ennreal.infi_mul_left'` and `ennreal.infi_mul_right'`;
* add `ennreal.tsum_top`;
* add `emetric.diam_closure`;
* add `edist_pos`;
* add `isometric.bijective`, `isometric.injective`, and `isometric.surjective`.

### [2021-03-14 03:22:15](https://github.com/leanprover-community/mathlib/commit/1e9f664)
refactor(ring_theory/discrete_valuation_ring): `discrete_valuation_ring.add_val` as an `add_valuation` ([#6660](https://github.com/leanprover-community/mathlib/pull/6660))
Refactors `discrete_valuation_ring.add_val` to be an `enat`-valued `add_valuation`.

### [2021-03-14 03:22:14](https://github.com/leanprover-community/mathlib/commit/d61d8bf)
feat(measure_theory/bochner_integration): extend the integral_smul lemmas ([#6654](https://github.com/leanprover-community/mathlib/pull/6654))
Extend the `integral_smul` lemmas to multiplication of a function `f : α → E` with scalars in `𝕜` with `[nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]` instead of only `ℝ`.

### [2021-03-14 03:22:13](https://github.com/leanprover-community/mathlib/commit/a8af8e8)
feat(polynomial/algebra_map): aeval_algebra_map_apply ([#6649](https://github.com/leanprover-community/mathlib/pull/6649))

### [2021-03-14 03:22:12](https://github.com/leanprover-community/mathlib/commit/3e011d6)
chore(equiv/*): add missing lemmas to traverse coercion diamonds ([#6648](https://github.com/leanprover-community/mathlib/pull/6648))
These don't have a preferred direction, but there are cases when they are definitely needed.
The conversion paths commute as squares:
```
`→+` <-- `→+*` <-- `→ₐ[R]`
 ^         ^          ^
 |         |          |
`≃+` <-- `≃+*` <-- `≃ₐ[R]`
```
so we only need lemmas to swap within each square.

### [2021-03-14 03:22:11](https://github.com/leanprover-community/mathlib/commit/a3050f4)
feat(group_theory/order_of_element): Endomorphisms of cyclic groups ([#6645](https://github.com/leanprover-community/mathlib/pull/6645))
If G is cyclic then every group homomorphism G -> G is a power map.

### [2021-03-14 03:22:10](https://github.com/leanprover-community/mathlib/commit/b23e14d)
feat(data/polynomial/eval): prod_comp ([#6644](https://github.com/leanprover-community/mathlib/pull/6644))
Extend `mul_comp` to `multiset.prod`

### [2021-03-14 03:22:09](https://github.com/leanprover-community/mathlib/commit/d5563ae)
feat(group_theory/solvable): Solvability preserved by short exact sequences ([#6632](https://github.com/leanprover-community/mathlib/pull/6632))
Proves that if 0 -> A -> B -> C -> 0 is a short exact sequence of groups, and if A and C are both solvable, then so is B.

### [2021-03-14 03:22:08](https://github.com/leanprover-community/mathlib/commit/ade8889)
feat(algebra/algebra/basic): An algebra isomorphism induces a group isomorphism between automorphism groups ([#6622](https://github.com/leanprover-community/mathlib/pull/6622))
Constructs the group isomorphism induced from an algebra isomorphism.

### [2021-03-14 00:42:57](https://github.com/leanprover-community/mathlib/commit/552ebeb)
feat(algebra/continued_fractions): add convergence theorem  ([#6607](https://github.com/leanprover-community/mathlib/pull/6607))
1. Add convergence theorem for continued fractions, i.e. `(gcf.of v).convergents` converges to `v`. 
2. Add some simple corollaries following from the already existing approximation lemmas for continued fractions, e.g. the equivalence of the convergent computations for continued fractions computed by `gcf.of` (`(gcf.of v).convergents` and `(gcf.of v).convergents'`).

### [2021-03-14 00:42:55](https://github.com/leanprover-community/mathlib/commit/a7410df)
feat(analysis/calculus/tangent_cone): add `unique_diff_on.pi` ([#6577](https://github.com/leanprover-community/mathlib/pull/6577))

### [2021-03-14 00:42:54](https://github.com/leanprover-community/mathlib/commit/1b0db8e)
feat(order/well_founded_set, ring_theory/hahn_series): `hahn_series.add_val` ([#6564](https://github.com/leanprover-community/mathlib/pull/6564))
Defines `set.is_wf.min` in terms of `well_founded.min`
Places an `add_valuation`, `hahn_series.add_val`, on `hahn_series`

### [2021-03-14 00:42:53](https://github.com/leanprover-community/mathlib/commit/0c26cea)
feat(order/filter/cofinite): a growing function has a minimum ([#6556](https://github.com/leanprover-community/mathlib/pull/6556))
If `tendsto f cofinite at_top`, then `f` has a minimal element.

### [2021-03-14 00:42:52](https://github.com/leanprover-community/mathlib/commit/19ecff8)
feat(topology/algebra/nonarchimedean): added nonarchimedean groups and rings ([#6551](https://github.com/leanprover-community/mathlib/pull/6551))
Adding nonarchimedean topological groups and rings.

### [2021-03-14 00:42:51](https://github.com/leanprover-community/mathlib/commit/ae33fb0)
feat(group_theory/submonoid/operations): add eq_top_iff' ([#6536](https://github.com/leanprover-community/mathlib/pull/6536))

### [2021-03-14 00:42:50](https://github.com/leanprover-community/mathlib/commit/f4c4d10)
feat(probability_theory/independence): prove equivalences for indep_set ([#6242](https://github.com/leanprover-community/mathlib/pull/6242))
Prove the following equivalences on `indep_set`, for measurable sets `s,t` and a probability measure `µ` :
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
In `indep_sets.indep_set_of_mem`, we use those equivalences to obtain `indep_set s t µ` from `indep_sets S T µ` and `s ∈ S`, `t ∈ T`.

### [2021-03-13 21:18:31](https://github.com/leanprover-community/mathlib/commit/c277752)
feat(algebra/group/defs, data/nat/basic): some `ne` lemmas ([#6637](https://github.com/leanprover-community/mathlib/pull/6637))
`≠` versions of `mul_left_inj`, `mul_right_inj`, and `succ_inj`, as well as the lemma `succ_succ_ne_one`.

### [2021-03-13 21:18:30](https://github.com/leanprover-community/mathlib/commit/468b8ff)
feat(field_theory/polynomial_galois_group): instances of trivial Galois group ([#6634](https://github.com/leanprover-community/mathlib/pull/6634))
This PR adds a bunch of instances where the Galois group of a polynomial is trivial.

### [2021-03-13 21:18:29](https://github.com/leanprover-community/mathlib/commit/ba6b689)
feat(field_theory/intermediate_field): coe_pow ([#6626](https://github.com/leanprover-community/mathlib/pull/6626))

### [2021-03-13 15:08:17](https://github.com/leanprover-community/mathlib/commit/e6819d3)
feat(algebra/group_power/lemmas): add invertible_of_pow_eq_one ([#6658](https://github.com/leanprover-community/mathlib/pull/6658))

### [2021-03-13 01:18:53](https://github.com/leanprover-community/mathlib/commit/ff8c8f5)
fix(tactic/norm_num): perform cleanup even if norm_num fails ([#6655](https://github.com/leanprover-community/mathlib/pull/6655))
[As reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/norm_num.20fails.20when.20simp.20is.20too.20effective/near/230004826).

### [2021-03-12 14:44:38](https://github.com/leanprover-community/mathlib/commit/f54f81c)
refactor(algebra/invertible): push deeper into the import graph ([#6650](https://github.com/leanprover-community/mathlib/pull/6650))
I want to be able to import this in files where we use `is_unit`, to remove a few unecessary non-computables.
This moves all the lemmas about `char_p` and `char_zero` from `algebra.invertible` to `algebra.char_p.invertible`. This means that we can talk about `invertible` elements without having to build up the theory in `order_of_element` first.
This doesn't change any lemma statements or proofs, but it does move some type arguments into `variables` statements.

### [2021-03-12 08:19:11](https://github.com/leanprover-community/mathlib/commit/85c6a79)
feat(measure_theory/lp_space): Lp is complete ([#6563](https://github.com/leanprover-community/mathlib/pull/6563))
Prove the completeness of `Lp` by showing that Cauchy sequences of `ℒp` have a limit.

### [2021-03-12 04:45:09](https://github.com/leanprover-community/mathlib/commit/dae047e)
feat(data/polynomial/*): more lemmas, especially for noncommutative rings ([#6599](https://github.com/leanprover-community/mathlib/pull/6599))

### [2021-03-12 01:21:10](https://github.com/leanprover-community/mathlib/commit/b852648)
chore(scripts): update nolints.txt ([#6651](https://github.com/leanprover-community/mathlib/pull/6651))
I am happy to remove some nolints for you!

### [2021-03-12 00:18:01](https://github.com/leanprover-community/mathlib/commit/2dabe5a)
feat(.docker): Docker containers for debian, alpine, and gitpod ([#6515](https://github.com/leanprover-community/mathlib/pull/6515))
# Docker containers
The `.docker` directory contains instructions for building Docker containers
with Lean and mathlib.
## Build
You can build these containers using `scripts/docker_build.sh`.
This will result in the creation of two containers:
* `leanprovercommunity/lean` - contains elan, lean, and leanproject
* `leanprovercommunity/mathlib` - additionally contains a copy of mathlib, with oleans
In fact, for each container you'll get three different tags, `:debian`, `:alpine` and `:latest`.
`:debian` and `:alpine` use those respective distributions, and `:latest` just points at `:debian`.
Finally, there is also a `leanprovercommunity/mathlib:gitpod` for use at
[https://gitpod.io/](https://gitpod.io/).
## Usage
### gitpod.io
There is a container based on `gitpod/workspace-base`
enabling [https://gitpod.io/](https://gitpod.io/) to create in-browser VSCode sessions
with elan/lean/leanproject/mathlib already set up.
Either prepend `https://gitpod.io/#` to basically any URL at github, e.g.
[https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker](https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker),
or install a [gitpod browser extension](https://www.gitpod.io/docs/browser-extension/)
which will add buttons directly on github.
### Command line
You can use these containers as virtual machines:
```sh
docker run -it leanprovercommunity/mathlib
```
### Docker registry
These containers are deployed to the Docker registry, so anyone can just
`docker run -it leanprovercommunity/mathlib` to get a local lean+mathlib environment.
There is a local script in `scripts/docker_push.sh` for deployment,
but I have also set up `hub.docker.com` to watch the `docker` branch for updates
and automatically rebuild.
If this PR is merged to master we should change that to watch `master`.
### Remote containers for VSCode
Installing the `Remote - Containers` VSCode extension
will allow you to open a project inside the `leanprovercommunity/mathlib` container
(meaning you don't even need a local copy of lean installed).
The file `/.devcontainer/devcontainer.json` sets this up:
if you have the extension installed, you'll be prompted to ask if you'd like to run inside the
container, no configuration necessary.

### [2021-03-11 22:32:31](https://github.com/leanprover-community/mathlib/commit/b1aafb2)
fix (topology/algebra/basic): fix universe issue with of_nhds_one ([#6647](https://github.com/leanprover-community/mathlib/pull/6647))
Everything had type max{u v} before.

### [2021-03-11 17:09:38](https://github.com/leanprover-community/mathlib/commit/4d8d344)
feat(data/multiset/basic): Multiset induction lemma ([#6623](https://github.com/leanprover-community/mathlib/pull/6623))
This is the multiset analog of `finset.induction_on'`

### [2021-03-11 17:09:36](https://github.com/leanprover-community/mathlib/commit/bd3695a)
feat(data/complex/is_R_or_C): add linear maps for is_R_or_C.re, im, conj and of_real ([#6621](https://github.com/leanprover-community/mathlib/pull/6621))
Add continuous linear maps and linear isometries (when applicable) for the following `is_R_or_C` functions: `re`, `im`, `conj` and `of_real`.
Rename the existing continuous linear maps defined in complex.basic to adopt the naming convention of is_R_or_C.

### [2021-03-11 17:09:35](https://github.com/leanprover-community/mathlib/commit/998a382)
feat(topology/algebra/infinite_sum): add `tsum_even_add_odd` ([#6620](https://github.com/leanprover-community/mathlib/pull/6620))
Prove `∑' i, f (2 * i) + ∑' i, f (2 * i + 1) = ∑' i, f i` and some
supporting lemmas.

### [2021-03-11 17:09:34](https://github.com/leanprover-community/mathlib/commit/95a8e95)
refactor(data/{,mv_}polynomial): support function ([#6615](https://github.com/leanprover-community/mathlib/pull/6615))
With polynomials, we try to avoid the function coercion in favor of the `coeff` functions.  However the coercion easily leaks through the abstraction because of the `finsupp.mem_support_iff` lemma.
This PR adds the `polynomial.support` and `mv_polynomial.support` functions.  This allows us to define the `polynomial.mem_support_iff` and `mv_polynomial.mem_support_iff` lemmas that are stated in terms of `coeff`.

### [2021-03-11 17:09:33](https://github.com/leanprover-community/mathlib/commit/f5c9d0f)
feat(topology/algebra/ordered): generalize `real.compact_Icc` ([#6602](https://github.com/leanprover-community/mathlib/pull/6602))

### [2021-03-11 13:28:38](https://github.com/leanprover-community/mathlib/commit/3b3a8b5)
fix(normed_space/multilinear): speed up slow proof ([#6639](https://github.com/leanprover-community/mathlib/pull/6639))
This proof seems to be right on the edge of timing out and has been causing CI issues.
I'm not sure if this is the only culprit. This whole file is very slow. Is this because of recent changes, or has it always been like this?

### [2021-03-11 13:28:36](https://github.com/leanprover-community/mathlib/commit/3d451c7)
chore(tactic/interactive): propagate tags in `substs` ([#6638](https://github.com/leanprover-community/mathlib/pull/6638))
Before this change, the `case left` tactic here did not work:
```lean
example {α : Type*} (a b c : α) (h : a = b) : (a = b ∨ a = c) ∧ true :=
begin
  with_cases {apply and.intro},
  substs' h,
  case left : { exact or.inl rfl },
  case right : { trivial }
end
```

### [2021-03-11 13:28:35](https://github.com/leanprover-community/mathlib/commit/9beec03)
feat(group_theory/subgroup): le_ker_iff ([#6630](https://github.com/leanprover-community/mathlib/pull/6630))
A subgroup is contained in the kernel iff it is mapped to the trivial subgroup.

### [2021-03-11 13:28:33](https://github.com/leanprover-community/mathlib/commit/57fda28)
refactor(data/polynomial/degree/definitions): Remove hypothesis of nat_degree_X_pow_sub_C ([#6628](https://github.com/leanprover-community/mathlib/pull/6628))
The lemma `nat_degree_X_pow_sub_C ` had an unnecessary hypothesis.

### [2021-03-11 13:28:32](https://github.com/leanprover-community/mathlib/commit/41f1196)
feat(field_theory/polynomial_galois_group): ext lemma ([#6627](https://github.com/leanprover-community/mathlib/pull/6627))
Two elements of `gal p` are equal if they agree on all roots of `p`

### [2021-03-11 13:28:31](https://github.com/leanprover-community/mathlib/commit/3dd1257)
feat(group_theory/solvable): Commutative groups are solvable ([#6625](https://github.com/leanprover-community/mathlib/pull/6625))
In practice, `is_solvable_of_comm` is hard to use, since you often aren't working with a `comm_group`. Instead, it is much nicer to be able to write:
`apply is_solvable_of_comm'`
`intros g h`

### [2021-03-11 13:28:30](https://github.com/leanprover-community/mathlib/commit/2c4a985)
feat(field_theory/splitting_field): splits_pow ([#6624](https://github.com/leanprover-community/mathlib/pull/6624))
If a polynomial splits then so do its powers.

### [2021-03-11 13:28:29](https://github.com/leanprover-community/mathlib/commit/653fd29)
refactor(topology): make is_closed a class ([#6552](https://github.com/leanprover-community/mathlib/pull/6552))
In `lean-liquid`, it would be useful that `is_closed` would be a class, to be able to infer a normed space structure on `E/F` when `F` is a closed subspace of a normed space `E`. This is implemented in this PR. This is mostly straightforward: the only proofs that need fixing are those abusing defeqness, so the new version makes them clearer IMHO.

### [2021-03-11 11:19:18](https://github.com/leanprover-community/mathlib/commit/56065f7)
feat(measure_theory/pi_system) lemmas for pi_system, useful for independence. ([#6353](https://github.com/leanprover-community/mathlib/pull/6353))
The goal here is to prove that the expectation of a product of an finite number of independent random variables equals the production of the expectations.
See https://github.com/leanprover-community/mathlib/tree/mzinkevi_independent_finite_alt

### [2021-03-11 06:05:43](https://github.com/leanprover-community/mathlib/commit/925ea07)
feat(linear_algebra/basic): add missing lemma finsupp.sum_smul_index_linear_map' ([#6565](https://github.com/leanprover-community/mathlib/pull/6565))
See also [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Sum.20is.20linear/near/229021943). cc @eric-wieser

### [2021-03-11 05:06:41](https://github.com/leanprover-community/mathlib/commit/b7c5709)
chore(geometry/manifold): use notation `𝓘(𝕜, E)` ([#6636](https://github.com/leanprover-community/mathlib/pull/6636))

### [2021-03-11 02:48:51](https://github.com/leanprover-community/mathlib/commit/514973a)
chore(scripts): update nolints.txt ([#6635](https://github.com/leanprover-community/mathlib/pull/6635))
I am happy to remove some nolints for you!

### [2021-03-11 02:48:49](https://github.com/leanprover-community/mathlib/commit/0e32116)
feat(data/dfinsupp): add is_scalar_tower and smul_comm_class ([#6614](https://github.com/leanprover-community/mathlib/pull/6614))
This also weakens the requirements for the `has_scalar` instance

### [2021-03-11 02:48:47](https://github.com/leanprover-community/mathlib/commit/a814e18)
ci(.github/workflows/build.yml): do not install azcopy, change upload logic ([#6613](https://github.com/leanprover-community/mathlib/pull/6613))
The "install azcopy" step has been [failing](https://github.com/leanprover-community/mathlib/runs/2070026978) from time to time, probably due to failed downloads. As it turns out, the GitHub-hosted actions runner [comes with it installed](https://github.com/actions/virtual-environments/blob/main/images/linux/Ubuntu2004-README.md#tools), so I've removed that step entirely.
I also made two other changes:
- The "push release to azure" step now only runs if the build actually started. The idea is that if the build never even starts due to e.g. `elan` temporarily failing to install, then we should be able to restart the build on GitHub and get `.olean`s for that commit without having to push another dummy commit. Currently we can't do this because we push an empty archive to Azure no matter what.
- We now upload artifacts if the build fails. This gives us an alternative way to get `.olean`s in case something goes wrong with Azure, and might make working with forks of mathlib slightly easier.

### [2021-03-11 00:47:49](https://github.com/leanprover-community/mathlib/commit/c5c97f2)
chore(ring_theory/polynomial/basic): remove a use of comap ([#6612](https://github.com/leanprover-community/mathlib/pull/6612))
This merges together `quotient_equiv_quotient_mv_polynomial` and `quotient_alg_equiv_quotient_mv_polynomial`, since the two now have the same domain and codomain.
`comap` was previously needed here to provide a wrapper type with an R-algebra structure on `mv_polynomial σ (I.quotient)`.
The updated `mv_polynomial.algebra` in [#6533](https://github.com/leanprover-community/mathlib/pull/6533) transfers the `algebra R I.quotient` structure directly to `mv_polynomial σ I.quotient`, eliminating the need for this wrapper type.

### [2021-03-11 00:47:48](https://github.com/leanprover-community/mathlib/commit/590444c)
chore(topology/metric/hausdorff_distance): use `infi`/`supr` ([#6611](https://github.com/leanprover-community/mathlib/pull/6611))

### [2021-03-10 20:43:06](https://github.com/leanprover-community/mathlib/commit/5be9cea)
chore(linear_algebra/quadratic_form): clean up universe collisions, generalize smul lemmas ([#6609](https://github.com/leanprover-community/mathlib/pull/6609))

### [2021-03-10 20:43:05](https://github.com/leanprover-community/mathlib/commit/547bf55)
feat(data/complex/module): transfer all `has_scalar ℝ` structures to `ℂ` ([#6562](https://github.com/leanprover-community/mathlib/pull/6562))
This provides (for an `R` with the same instance on `ℝ`) the instances:
* `has_scalar R ℂ`
* `is_scalar_tower R S ℂ`
* `smul_comm_class R S ℂ`
* `mul_action R ℂ`
* `distrib_mul_action R ℂ`
* `semimodule R ℂ`
* `algebra R ℂ`
* `normed_algebra R ℂ`
This has the downside that `smul_coe` is no longer a `rfl` lemma, but means that `ℂ` is automatically an algebra over `ℝ≥0`.
It renames `smul_re` and `smul_im` to `of_real_mul_re` and `of_real_mul_im`, since the previous statements did not use `smul` at all, and renaming frees up these names for lemmas which _do_ use `smul`.
This removes `normed_space.restrict_scalars_real E` (implemented as `normed_space.restrict_scalars ℝ ℂ E`) as:
* As an instance, it now causes unwanted diamonds
* After downgrading to a def, it is never used
* The docs for `normed_space.restrict_scalars` suggest judicious use, and that if you want this instance you should use the type synonym `semimodule.restrict_scalars ℝ ℂ E` which will have this instance for free.

### [2021-03-10 20:43:04](https://github.com/leanprover-community/mathlib/commit/60e2579)
feat(ring_theory/valuation/basic): additive valuations ([#6559](https://github.com/leanprover-community/mathlib/pull/6559))
Introduces `add_valuation`, a version of `valuation` that takes values in a `linear_ordered_add_comm_monoid_with_top`.
As an example, defines `multiplicity.add_valuation`

### [2021-03-10 20:43:02](https://github.com/leanprover-community/mathlib/commit/e62a406)
feat(linear_algebra/determinant): determinant of a block triangular matrix ([#6050](https://github.com/leanprover-community/mathlib/pull/6050))
Add lemmas for determinants of block triangular matrices.

### [2021-03-10 17:05:28](https://github.com/leanprover-community/mathlib/commit/664feed)
chore(topology/algebra/ordered): add some `at_bot` versions of lemmas ([#6618](https://github.com/leanprover-community/mathlib/pull/6618))

### [2021-03-10 17:05:27](https://github.com/leanprover-community/mathlib/commit/f675a86)
feat(data/real/{nnreal,ennreal}): add (e)nnreal.of_real_bit0/bit1 ([#6617](https://github.com/leanprover-community/mathlib/pull/6617))
Add bit0/bit1 lemmas for `nnreal.of_real`, `ennreal.of_real` and `ennreal.to_nnreal`.
With these additions, it is for example possible to prove `h : ennreal.of_real (2 : ℝ) = 2 := by simp`.

### [2021-03-10 17:05:26](https://github.com/leanprover-community/mathlib/commit/df1337e)
feat(data/local_equiv,topology/local_homeomorph): add `local_equiv.pi` and `local_homeomorph.pi` ([#6574](https://github.com/leanprover-community/mathlib/pull/6574))

### [2021-03-10 11:57:13](https://github.com/leanprover-community/mathlib/commit/e221dc9)
feat(ring_theory/hahn_series): algebra structure, equivalences with power series ([#6540](https://github.com/leanprover-community/mathlib/pull/6540))
Places an `algebra` structure on `hahn_series`
Defines a `ring_equiv` and when relevant an `alg_equiv` between `hahn_series nat R` and `power_series R`.

### [2021-03-10 11:57:12](https://github.com/leanprover-community/mathlib/commit/eaa0218)
feat(category_theory/triangulated/basic): add definitions of additive category and triangle ([#6539](https://github.com/leanprover-community/mathlib/pull/6539))
This PR adds the definition of an additive category and the definition of a triangle in an additive category with an additive shift.

### [2021-03-10 11:57:10](https://github.com/leanprover-community/mathlib/commit/a7f1e3c)
feat(normed_group): tendsto_at_top ([#6525](https://github.com/leanprover-community/mathlib/pull/6525))

### [2021-03-10 11:57:09](https://github.com/leanprover-community/mathlib/commit/ccd35db)
feat(linear_algebra/matrix): to_matrix and to_lin as alg_equiv ([#6496](https://github.com/leanprover-community/mathlib/pull/6496))
The existing `linear_map.to_matrix` and `matrix.to_lin` can be upgraded to an `alg_equiv` if working on linear endomorphisms or square matrices. The API is copied over in rote fashion.

### [2021-03-10 08:51:55](https://github.com/leanprover-community/mathlib/commit/b1ecc98)
feat(nat/digits): natural basis representation using list sum and map ([#5975](https://github.com/leanprover-community/mathlib/pull/5975))

### [2021-03-10 02:23:34](https://github.com/leanprover-community/mathlib/commit/fad44b9)
feat(ring_theory/ideal/operations): add quotient_equiv ([#6492](https://github.com/leanprover-community/mathlib/pull/6492))
The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`,  where `J = f(I)`, and similarly for algebras.

### [2021-03-10 02:23:33](https://github.com/leanprover-community/mathlib/commit/4e370b5)
feat(topology): shrinking lemma ([#6478](https://github.com/leanprover-community/mathlib/pull/6478))
### Add a few versions of the shrinking lemma:
* `exists_subset_Union_closure_subset` and `exists_Union_eq_closure_subset`: shrinking lemma for general normal spaces;
* `exists_subset_Union_ball_radius_lt`, `exists_Union_ball_eq_radius_lt`, `exists_subset_Union_ball_radius_pos_lt`, `exists_Union_ball_eq_radius_pos_lt`: shrinking lemma for coverings by open balls in a proper metric space;
* `exists_locally_finite_subset_Union_ball_radius_lt`, `exists_locally_finite_Union_eq_ball_radius_lt`: given a positive function `R : X → ℝ`, finds a locally finite covering by open balls `ball (c i) (r' i)`, `r' i < R` and a subcovering by balls of strictly smaller radius `ball (c i) (r i)`, `0 < r i < r' i`.
### Other API changes
* add `@[simp]` to `set.compl_subset_compl`;
* add `is_closed_bInter` and `locally_finite.point_finite`;
* add `metric.closed_ball_subset_closed_ball`, `metric.uniformity_basis_dist_lt`, `exists_pos_lt_subset_ball`, and `exists_lt_subset_ball`;
* generalize `refinement_of_locally_compact_sigma_compact_of_nhds_basis` to `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set`, replace arguments `(s : X → set X) (hs : ∀ x, s x ∈ 𝓝 x)` with a hint to use `filter.has_basis.restrict_subset` if needed.
* make `s` and `t` arguments of `normal_separation` implicit;
* add `normal_exists_closure_subset`;
* turn `sigma_compact_space_of_locally_compact_second_countable` into an `instance`.

### [2021-03-10 02:23:32](https://github.com/leanprover-community/mathlib/commit/05d3955)
feat(number_theory/bernoulli): bernoulli_power_series ([#6456](https://github.com/leanprover-community/mathlib/pull/6456))
Co-authored-by Ashvni Narayanan

### [2021-03-10 02:23:31](https://github.com/leanprover-community/mathlib/commit/c962871)
feat(linear_algebra): linear_independent_fin_snoc ([#6455](https://github.com/leanprover-community/mathlib/pull/6455))
A slight variation on the existing `linear_independent_fin_cons`.

### [2021-03-09 21:43:56](https://github.com/leanprover-community/mathlib/commit/b697e52)
refactor(ring_theory/power_series/basic): simplify truncation ([#6605](https://github.com/leanprover-community/mathlib/pull/6605))
I'm trying to reduce how much finsupp leaks through the polynomial API, in this case it works quite nicely.

### [2021-03-09 21:43:55](https://github.com/leanprover-community/mathlib/commit/09a505a)
feat(ring_theory/witt_vector): use structure instead of irreducible ([#6604](https://github.com/leanprover-community/mathlib/pull/6604))

### [2021-03-09 21:43:53](https://github.com/leanprover-community/mathlib/commit/18d4e51)
chore(algebra/ring/basic): weaken ring.inverse to only require monoid_with_zero ([#6603](https://github.com/leanprover-community/mathlib/pull/6603))
Split from [#5539](https://github.com/leanprover-community/mathlib/pull/5539) because I actually want to use this, and the PR is large and stalled.

### [2021-03-09 21:43:52](https://github.com/leanprover-community/mathlib/commit/fb674e1)
feat(data/finset/lattice): map_sup, map_inf ([#6601](https://github.com/leanprover-community/mathlib/pull/6601))

### [2021-03-09 21:43:51](https://github.com/leanprover-community/mathlib/commit/be6753c)
feat(data/{list,multiset,finset}): map_filter ([#6600](https://github.com/leanprover-community/mathlib/pull/6600))
This renames `list.filter_of_map` to `list.map_filter`, which unifies the name of the `map_filter` lemmas for lists and finsets, and adds a corresponding lemma for multisets.
Unfortunately, the name `list.filter_map` is already used for a definition.

### [2021-03-09 21:43:50](https://github.com/leanprover-community/mathlib/commit/366a23f)
feat(topology/constructions): frontier/interior/closure in `X × Y` ([#6594](https://github.com/leanprover-community/mathlib/pull/6594))

### [2021-03-09 21:43:49](https://github.com/leanprover-community/mathlib/commit/9ff7458)
feat(algebra/group_power/basic): add abs_add_eq_add_abs_iff ([#6593](https://github.com/leanprover-community/mathlib/pull/6593))
I've added
```
lemma abs_add_eq_add_abs_iff {α : Type*} [linear_ordered_add_comm_group α]  (a b : α) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)
```
from `lean-liquid`. For some reasons I am not able to use `wlog hle : a ≤ b using [a b, b a]` at the beginning of the proof, Lean says `unknown identifier 'wlog'` and if I try to import `tactic.wlog` I have tons of errors.

### [2021-03-09 21:43:47](https://github.com/leanprover-community/mathlib/commit/8e246cb)
refactor(data/mv_polynomial): cleanup equivs ([#6589](https://github.com/leanprover-community/mathlib/pull/6589))
This:
* Replaces `alg_equiv_congr_left` with `rename_equiv` (to match `rename`)
* Removes `ring_equiv_congr_left` (it's now `rename_equiv.to_ring_equiv`)
* Renames `alg_equiv_congr_right` to `map_alg_equiv` (to match `map`) and removes the `comap` from the definition
* Renames `ring_equiv_congr_right` to `map_equiv` (to match `map`)
* Removes `alg_equiv_congr` (it's now `(map_alg_equiv R e).trans $ (rename_equiv e_var).restrict_scalars _`, which while longer is never used anyway)
* Removes `ring_equiv_congr` (it's now `(map_equiv R e).trans $ (rename_equiv e_var).to_ring_equiv`, which while longer is never used anyway)
* Replaces `punit_ring_equiv` with `punit_alg_equiv`
* Removes `comap` from the definition of `sum_alg_equiv`
* Promotes `option_equiv_left`, `option_equiv_right`, and `fin_succ_equiv` to `alg_equiv`s
This is a follow-up to [#6420](https://github.com/leanprover-community/mathlib/pull/6420)

### [2021-03-09 21:43:46](https://github.com/leanprover-community/mathlib/commit/5d82d1d)
feat(algebra,linear_algebra): `{smul,lmul,lsmul}_injective` ([#6588](https://github.com/leanprover-community/mathlib/pull/6588))
This PR proves a few injectivity results for (scalar) multiplication in the setting of modules and algebras over a ring.

### [2021-03-09 21:43:45](https://github.com/leanprover-community/mathlib/commit/3d75242)
chore(data/equiv/local_equiv,topology/local_homeomorph): put `source`/`target` to the left in `∩` ([#6583](https://github.com/leanprover-community/mathlib/pull/6583))

### [2021-03-09 21:43:44](https://github.com/leanprover-community/mathlib/commit/78af5b1)
feat(topology): closure in a `pi` space ([#6575](https://github.com/leanprover-community/mathlib/pull/6575))
Also add `can_lift` instances that lift `f : subtype p → β` to `f : α → β` and a version of `filter.mem_infi_iff` that uses a globally defined function.

### [2021-03-09 21:43:43](https://github.com/leanprover-community/mathlib/commit/792e492)
feat(topology/separation): add API for interaction between discrete topology and subsets ([#6570](https://github.com/leanprover-community/mathlib/pull/6570))
The final result:
Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.
The proofs are by Patrick Massot.

### [2021-03-09 16:22:20](https://github.com/leanprover-community/mathlib/commit/8713c0b)
feat(measure/pi): prove extensionality for `measure.pi` ([#6304](https://github.com/leanprover-community/mathlib/pull/6304))
* If two measures in a finitary product are equal on cubes with measurable sides (or with sides in a set generating the corresponding sigma-algebra), then the measures are equal.
* Add `sigma_finite` instance for `measure.pi`
* Some basic lemmas about sets (more specifically `Union` and `set.pi`)
* rename `measurable_set.pi_univ` -> `measurable_set.univ_pi` (`pi univ t` is called `univ_pi` consistently in `set/basic`, but it's not always consistent elsewhere)
* rename `[bs]?Union_prod` -> `[bs]?Union_prod_const`

### [2021-03-09 11:19:52](https://github.com/leanprover-community/mathlib/commit/c1a7c19)
chore(data/polynomial/basic): add missing is_scalar_tower and smul_comm_class instances ([#6592](https://github.com/leanprover-community/mathlib/pull/6592))
These already exist for `mv_polynomial`, but the PR that I added them in forgot to add them for `polynomial`.
Notably, this provides the instance `is_scalar_tower R (mv_polynomial S₁ R) (polynomial (mv_polynomial S₁ R))`.

### [2021-03-09 11:19:51](https://github.com/leanprover-community/mathlib/commit/fa28a8c)
feat(data/nat/parity): even/odd.mul_even/odd ([#6584](https://github.com/leanprover-community/mathlib/pull/6584))
Lemmas pertaining to the multiplication of even and odd natural numbers.

### [2021-03-09 11:19:50](https://github.com/leanprover-community/mathlib/commit/49afae5)
feat(number_theory/bernoulli): bernoulli_poly_eval_one ([#6581](https://github.com/leanprover-community/mathlib/pull/6581))

### [2021-03-09 11:19:49](https://github.com/leanprover-community/mathlib/commit/9889502)
feat(linear_algebra/pi): add `submodule.pi` ([#6576](https://github.com/leanprover-community/mathlib/pull/6576))

### [2021-03-09 11:19:47](https://github.com/leanprover-community/mathlib/commit/a331113)
feat(analysis/normed_space/normed_group_hom): bounded homs between normed groups ([#6375](https://github.com/leanprover-community/mathlib/pull/6375))
From `lean-liquid`

### [2021-03-09 08:12:31](https://github.com/leanprover-community/mathlib/commit/6dec23b)
chore(topology/algebra/ordered): use dot notation, golf some proofs ([#6595](https://github.com/leanprover-community/mathlib/pull/6595))
Use more precise typeclass arguments here and there, golf some proofs, use dot notation.
### Renamed lemmas
* `is_lub_of_is_lub_of_tendsto` → `is_lub.is_lub_of_tendsto`;
* `is_glb_of_is_glb_of_tendsto` → `is_glb.is_glb_of_tendsto`;
* `is_glb_of_is_lub_of_tendsto` → `is_lub.is_glb_of_tendsto`;
* `is_lub_of_is_glb_of_tendsto` → `is_glb.is_lub_of_tendsto`;
* `mem_closure_of_is_lub` → `is_lub.mem_closure`;
* `mem_of_is_lub_of_is_closed` → `is_lub.mem_of_is_closed`, `is_closed.is_lub_mem`;
* `mem_closure_of_is_glb` → `is_glb.mem_closure`;
* `mem_of_is_glb_of_is_closed` → `is_glb.mem_of_is_closed`, `is_closed.is_glb_mem`;
### New lemmas
* `is_lub.inter_Ici_of_mem`
* `is_glb.inter_Iic_of_mem`
* `frequently.filter_mono`
* `is_lub.frequently_mem`
* `is_lub.frequently_nhds_mem`
* `is_glb.frequently_mem`
* `is_glb.frequently_nhds_mem`
* `is_lub.mem_upper_bounds_of_tendsto`
* `is_glb.mem_lower_bounds_of_tendsto`
* `is_lub.mem_lower_bounds_of_tendsto`
* `is_glb.mem_upper_bounds_of_tendsto`
* `diff_subset_closure_iff`

### [2021-03-09 02:15:11](https://github.com/leanprover-community/mathlib/commit/32bd00f)
refactor(topology/bounded_continuous_function): structure extending continuous_map ([#6521](https://github.com/leanprover-community/mathlib/pull/6521))
Convert `bounded_continuous_function` from a subtype to a structure extending `continuous_map`, and some minor improvements to `@[simp]` lemmas.

### [2021-03-08 19:42:23](https://github.com/leanprover-community/mathlib/commit/3e5d90d)
feat(algebra/continued_fractions) add determinant formula and approximations for error term ([#6461](https://github.com/leanprover-community/mathlib/pull/6461))

### [2021-03-08 19:42:22](https://github.com/leanprover-community/mathlib/commit/0afdaab)
feat(linear_algebra): submodules of f.g. free modules are free ([#6178](https://github.com/leanprover-community/mathlib/pull/6178))
This PR proves the first half of the structure theorem for modules over a PID: if `R` is a principal ideal domain and `M` an `R`-module which is free and finitely generated (expressed by `is_basis R (b : ι → M)`, for a `[fintype ι]`), then all submodules of `M` are also free and finitely generated.
This result requires some lemmas about the rank of (free) modules (which in that case is basically the same as `fintype.card ι`). If `M` were a vector space, this could just be expressed as `findim R M`, but it isn't necessarily, so it can't be.

### [2021-03-08 17:02:28](https://github.com/leanprover-community/mathlib/commit/cdc222d)
chore(topology): add a few simple lemmas ([#6580](https://github.com/leanprover-community/mathlib/pull/6580))

### [2021-03-08 17:02:27](https://github.com/leanprover-community/mathlib/commit/87eec0b)
feat(linear_algebra/bilinear_form): Existence of orthogonal basis with respect to a bilinear form ([#5814](https://github.com/leanprover-community/mathlib/pull/5814))
We state and prove the result that there exists an orthogonal basis with respect to a symmetric nondegenerate.

### [2021-03-08 14:38:24](https://github.com/leanprover-community/mathlib/commit/6791ed9)
chore(algebra/module/linear_map): add linear_map.to_distrib_mul_action_hom ([#6573](https://github.com/leanprover-community/mathlib/pull/6573))
My aim in adding this is primarily to give the reader a hint that `distrib_mul_action_hom` exists.
The only difference between the two is that `linear_map` can infer `map_zero'` from its typeclass arguments.

### [2021-03-08 14:38:23](https://github.com/leanprover-community/mathlib/commit/13d86df)
chore(algebra/monoid_algebra): provide finer-grained levels of structure for less-structured `G`. ([#6572](https://github.com/leanprover-community/mathlib/pull/6572))
This provides `distrib` and `mul_zero_class` for when `G` is just `has_mul`, and `semigroup` for when `G` is just `semigroup`.
It also weakens the typeclass assumptions on some correspondings lemmas.

### [2021-03-08 12:32:37](https://github.com/leanprover-community/mathlib/commit/7058fa6)
feat(linear_algebra/{bilinear,quadratic}_form): inherit scalar actions from algebras ([#6586](https://github.com/leanprover-community/mathlib/pull/6586))
For example, this means a quadratic form over the quaternions inherits an `ℝ` action.

### [2021-03-08 12:32:35](https://github.com/leanprover-community/mathlib/commit/5d0a40f)
feat(algebra/algebra/{basic,tower}): add alg_equiv.comap and alg_equiv.restrict_scalars ([#6548](https://github.com/leanprover-community/mathlib/pull/6548))
This also renames `is_scalar_tower.restrict_base` to `alg_hom.restrict_scalars`, to enable dot notation and match `linear_map.restrict_scalars`.

### [2021-03-08 11:35:06](https://github.com/leanprover-community/mathlib/commit/b6ed62c)
feat(algebraic_topology): simplicial objects and simplicial types ([#6195](https://github.com/leanprover-community/mathlib/pull/6195))

### [2021-03-08 10:21:12](https://github.com/leanprover-community/mathlib/commit/f3dbe9f)
feat(bounded_continuous_function): coe_sum ([#6522](https://github.com/leanprover-community/mathlib/pull/6522))

### [2021-03-08 02:11:14](https://github.com/leanprover-community/mathlib/commit/98c6bbc)
feat(data/set/function): three lemmas about maps_to ([#6518](https://github.com/leanprover-community/mathlib/pull/6518))

### [2021-03-08 01:18:53](https://github.com/leanprover-community/mathlib/commit/5b61f07)
chore(scripts): update nolints.txt ([#6582](https://github.com/leanprover-community/mathlib/pull/6582))
I am happy to remove some nolints for you!

### [2021-03-07 22:03:50](https://github.com/leanprover-community/mathlib/commit/2d3c522)
feat(order/ideal): added proper ideal typeclass and lemmas to order_top ([#6566](https://github.com/leanprover-community/mathlib/pull/6566))
Defined `proper` and proved basic lemmas about proper ideals.
Also turned `order_top` into a section.

### [2021-03-07 21:14:26](https://github.com/leanprover-community/mathlib/commit/79be90a)
feat(algebra/regular): add lemmas about regularity of non-zero elements ([#6579](https://github.com/leanprover-community/mathlib/pull/6579))
More API, to deal with cases in which a regular element is non-zero.

### [2021-03-07 17:19:18](https://github.com/leanprover-community/mathlib/commit/b25994d)
feat(number_theory/bernoulli): definition and properties of Bernoulli polynomials ([#6309](https://github.com/leanprover-community/mathlib/pull/6309))
The Bernoulli polynomials and its properties are defined.

### [2021-03-07 14:37:15](https://github.com/leanprover-community/mathlib/commit/d9370e0)
fead(data/support): add `support_smul` ([#6569](https://github.com/leanprover-community/mathlib/pull/6569))
* add `smul_ne_zero`;
* rename `support_smul_subset` to `support_smul_subset_right`;
* add `support_smul_subset_left` and `support_smul`.

### [2021-03-07 10:18:36](https://github.com/leanprover-community/mathlib/commit/02251b1)
refactor(geometry/manifold): drop some unused arguments ([#6545](https://github.com/leanprover-community/mathlib/pull/6545))
API changes:
* add lemmas about `map (ext_chart_at I x) (𝓝[s] x')`;
* prove `times_cont_mdiff_within_at.comp` directly without using other charts; the new proof does not need a `smooth_manifold_with_corners` instance;
* add aliases `times_cont_mdiff.times_cont_diff` etc;
* `times_cont_mdiff_map` no longer needs a `smooth_manifold_with_corners` instance;
* `has_smooth_mul` no longer extends `smooth_manifold_with_corners` and no longer takes `has_continuous_mul` as an argument;
* `has_smooth_mul_core` is gone in favor of `has_continuous_mul_of_smooth`;
* `smooth_monoid_morphism` now works with any model space (needed, e.g., to define `smooth_monoid_morphism.prod`);
* `lie_group_morphism` is gone: we use `M →* N` both for monoids and groups, no reason to have two structures in this case;
* `lie_group` no longer extends `smooth_manifold_with_corners` and no longer takes `topological_group` as an argument;
* `lie_group_core` is gone in favor of `topological_group_of_lie_group`;
* the `I : model_with_corners 𝕜 E H` argument of `smooth_mul` and `smooth_inv` is now explicit.

### [2021-03-07 04:25:18](https://github.com/leanprover-community/mathlib/commit/ebe2c61)
feat(analysis/normed_space/multilinear): a few more bundled (bi)linear maps ([#6546](https://github.com/leanprover-community/mathlib/pull/6546))

### [2021-03-07 03:26:19](https://github.com/leanprover-community/mathlib/commit/9f17db5)
feat(analysis/special_functions/integrals): mul/div by a const ([#6357](https://github.com/leanprover-community/mathlib/pull/6357))
This PR, together with [#6216](https://github.com/leanprover-community/mathlib/pull/6216), makes the following possible:
```
import analysis.special_functions.integrals
open real interval_integral
open_locale real
example : ∫ x in 0..π, 2 * sin x = 4 := by norm_num
example : ∫ x:ℝ in 4..5, x * 2 = 9 := by norm_num
example : ∫ x in 0..π/2, cos x / 2 = 1 / 2 := by simp
```

### [2021-03-07 01:15:46](https://github.com/leanprover-community/mathlib/commit/07fc982)
chore(scripts): update nolints.txt ([#6567](https://github.com/leanprover-community/mathlib/pull/6567))
I am happy to remove some nolints for you!

### [2021-03-06 21:16:19](https://github.com/leanprover-community/mathlib/commit/df1e6f9)
refactor(data/{finset,multiset}): move inductions proofs on sum/prod from finset to multiset, add more induction lemmas ([#6561](https://github.com/leanprover-community/mathlib/pull/6561))
The starting point is `finset.le_sum_of_subadditive`, which is extended in several ways:
* It is written in multiplicative form, and a `[to_additive]` attribute generates the additive version,
* It is proven for multiset, which is then used for the proof of the finset case.
* For multiset, some lemmas are written for foldr/foldl (and prod is a foldr).
* Versions of these lemmas specialized to nonempty sets are provided. These don't need the initial hypothesis `f 1 = 1`/`f 0 = 0`.
* The new `..._on_pred` lemmas like `finset.le_sum_of_subadditive_on_pred` apply to functions that are only sub-additive for arguments that verify some property. I included an application of this with `snorm_sum_le`, which uses that the Lp seminorm is subadditive on a.e.-measurable functions. Those `on_pred` lemmas could be avoided by constructing the submonoid given by the predicate, then using the standard subadditive result, but I find convenient to be able to use them directly.

### [2021-03-06 21:16:18](https://github.com/leanprover-community/mathlib/commit/b280b00)
feat(data/set/basic): add `set.set_ite` ([#6557](https://github.com/leanprover-community/mathlib/pull/6557))
I'm going to use it as `source` and `target` in
`local_equiv.piecewise` and `local_homeomorph.piecewise`. There are
many non-defeq ways to define this set and I think that it's better to
have a name than to ensure that we always use the same formula.

### [2021-03-06 19:15:21](https://github.com/leanprover-community/mathlib/commit/ac8a119)
chore(geometry/manifold): use `namespace`, rename `image` to `image_eq` ([#6517](https://github.com/leanprover-community/mathlib/pull/6517))
* use `namespace` command in
  `geometry/manifold/smooth_manifold_with_corners`;
* rename `model_with_corners.image` to `model_with_corners.image_eq`
  to match `source_eq` etc;
* replace `homeomorph.coe_eq_to_equiv` with
  `@[simp] lemma coe_to_equiv`;
* add `continuous_linear_map.symm_image_image` and
  `continuous_linear_map.image_symm_image`;
* add `unique_diff_on.image`,
  `continuous_linear_equiv.unique_diff_on_image_iff`.

### [2021-03-06 17:06:17](https://github.com/leanprover-community/mathlib/commit/16ef291)
feat(order/filter/*, topology/subset_properties): define "coproduct" of two filters ([#6372](https://github.com/leanprover-community/mathlib/pull/6372))
Define the "coproduct" of two filters (unclear if this is really a categorical coproduct) as
```lean
protected def coprod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊔ g.comap prod.snd
```
and prove the three lemmas which motivated this construction ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Filter.20golf)):  coproduct of cofinite filters is the cofinite filter, coproduct of cocompact filters is the cocompact filter, and
```lean
(tendsto f a c) → (tendsto g b d) → (tendsto (prod.map f g) (a.coprod b) (c.coprod d))
```
Co-authored by: Kevin Buzzard <k.buzzard@imperial.ac.uk>
Co-authored by: Patrick Massot <patrickmassot@free.fr>

### [2021-03-06 11:31:49](https://github.com/leanprover-community/mathlib/commit/0fa0d61)
feat(topology/paracompact): define paracompact spaces ([#6395](https://github.com/leanprover-community/mathlib/pull/6395))
Fixes [#6391](https://github.com/leanprover-community/mathlib/pull/6391)

### [2021-03-06 07:42:55](https://github.com/leanprover-community/mathlib/commit/126cebc)
feat(data/real/nnreal): ℝ is an ℝ≥0-algebra ([#6560](https://github.com/leanprover-community/mathlib/pull/6560))
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/rings.20from.20subtype

### [2021-03-06 07:42:54](https://github.com/leanprover-community/mathlib/commit/a05b35c)
doc(*): wrap raw URLs containing parentheses with angle brackets ([#6554](https://github.com/leanprover-community/mathlib/pull/6554))
Raw URLs with parentheses in them are tricky for `doc-gen` to parse, so this commit wraps them in angle brackets.

### [2021-03-06 07:42:53](https://github.com/leanprover-community/mathlib/commit/3e5643e)
feat(category_theory/opposites): use simps everywhere ([#6553](https://github.com/leanprover-community/mathlib/pull/6553))
This is possible after leanprover-community/lean[#538](https://github.com/leanprover-community/mathlib/pull/538)

### [2021-03-06 07:42:52](https://github.com/leanprover-community/mathlib/commit/5962c76)
feat(algebra/ring/boolean_ring): Boolean rings ([#6464](https://github.com/leanprover-community/mathlib/pull/6464))
`boolean_ring.to_boolean_algebra` is the Boolean algebra structure on a Boolean ring.

### [2021-03-06 02:14:45](https://github.com/leanprover-community/mathlib/commit/32547fc)
chore(scripts): update nolints.txt ([#6558](https://github.com/leanprover-community/mathlib/pull/6558))
I am happy to remove some nolints for you!

### [2021-03-06 01:08:46](https://github.com/leanprover-community/mathlib/commit/4428243)
chore(polynomial/chebyshev): changes names of chebyshev₁ to chebyshev.T and chebyshev₂ to chebyshev.U ([#6519](https://github.com/leanprover-community/mathlib/pull/6519))
Still have to write here what was changed (will be a long list). More or less this is just search and replace `chebyshev₁` for `chebyshev.T` and `chebyshev₂` for `chebyshev.U`.
* `polynomial.chebyshev₁` is now `polynomial.chebyshev.T`
* `polynomial.chebyshev₁_zero` is now `polynomial.chebyshev.T_zero`
* `polynomial.chebyshev₁_one` is now `polynomial.chebyshev.T_one`
* `polynomial.chebyshev₁_two` is now `polynomial.chebyshev.T_two`
* `polynomial.chebyshev₁_add_two` is now `polynomial.chebyshev.T_add_two`
* `polynomial.chebyshev₁_of_two_le` is now `polynomial.chebyshev.T_of_two_le`
* `polynomial.map_chebyshev₁` is now `polynomial.chebyshev.map_T`
* `polynomial.chebyshev₂` is now `polynomial.chebyshev.U`
* `polynomial.chebyshev₂_zero` is now `polynomial.chebyshev.U_zero`
* `polynomial.chebyshev₂_one` is now `polynomial.chebyshev.U_one`
* `polynomial.chebyshev₂_two` is now `polynomial.chebyshev.U_two`
* `polynomial.chebyshev₂_add_two` is now `polynomial.chebyshev.U_add_two`
* `polynomial.chebyshev₂_of_two_le` is now `polynomial.chebyshev.U_of_two_le`
* `polynomial.chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁` is now `polynomial.chebyshev.U_eq_X_mul_U_add_T`
* `polynomial.chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂` is now `polynomial.chebyshev.T_eq_U_sub_X_mul_U`
* `polynomial.chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂` is now `polynomial.chebyshev.T_eq_X_mul_T_sub_pol_U`
* `polynomial.one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁` is now `polynomial.chebyshev.one_sub_X_pow_two_mul_U_eq_pol_in_T`
* `polynomial.map_chebyshev₂` is now `polynomial.chebyshev.map_U`
* `polynomial.chebyshev₁_derivative_eq_chebyshev₂` is now `polynomial.chebyshev.T_derivative_eq_U`
* `polynomial.one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁` is now `polynomial.chebyshev.one_sub_X_pow_two_mul_derivative_T_eq_poly_in_T`
* `polynomial.add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂` is now `polynomial.chebyshev.add_one_mul_T_eq_poly_in_U`
* `polynomial.mul_chebyshev₁` is now `polynomial.chebyshev.mul_T`
* `polynomial.chebyshev₁_mul` is now `polynomial.chebyshev.T_mul`
* `polynomial.dickson_one_one_eq_chebyshev₁` is now `polynomial.dickson_one_one_eq_chebyshev_T`
* `polynomial.chebyshev₁_eq_dickson_one_one` is now `polynomial.chebyshev_T_eq_dickson_one_one`
* `chebyshev₁_complex_cos` is now `polynomial.chebyshev.T_complex_cos`
* `cos_nat_mul` is now `polynomial.chebyshev.cos_nat_mul`
* `chebyshev₂_complex_cos` is now `polynomial.chebyshev.U_complex_cos`
* `sin_nat_succ_mul` is now `polynomial.chebyshev.sin_nat_succ_mul`

### [2021-03-05 21:45:36](https://github.com/leanprover-community/mathlib/commit/4bc6707)
feat(topology/local_homeomorph): preimage of `closure` and `frontier` ([#6547](https://github.com/leanprover-community/mathlib/pull/6547))

### [2021-03-05 21:45:35](https://github.com/leanprover-community/mathlib/commit/cbcbe24)
feat(algebra/ordered_monoid): linear_ordered_add_comm_monoid(_with_top) ([#6520](https://github.com/leanprover-community/mathlib/pull/6520))
Separates out classes for `linear_ordered_(add_)comm_monoid`
Creates `linear_ordered_add_comm_monoid_with_top`, an additive and order-reversed version of `linear_ordered_comm_monoid_with_zero`.
Puts an instance of `linear_ordered_add_comm_monoid_with_top` on `with_top` of any `linear_ordered_add_comm_monoid` and also on `enat`

### [2021-03-05 20:52:35](https://github.com/leanprover-community/mathlib/commit/626cb42)
feat(data/polynomial/mirror): new file ([#6426](https://github.com/leanprover-community/mathlib/pull/6426))
This files defines an alternate version of `polynomial.reverse`. This version is often nicer to work with since it preserves `nat_degree` and `nat_trailing_degree` and is always an involution.
(this PR is part of the irreducibility saga)

### [2021-03-05 16:16:24](https://github.com/leanprover-community/mathlib/commit/913950e)
feat(group_theory/subgroup): add monoid_hom.restrict ([#6537](https://github.com/leanprover-community/mathlib/pull/6537))

### [2021-03-05 15:05:25](https://github.com/leanprover-community/mathlib/commit/d40487b)
feat(measure_theory/[set_integral, interval_integral]): mono and nonneg lemmas ([#6292](https://github.com/leanprover-community/mathlib/pull/6292))
See https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60integral_restrict.60/near/226274072

### [2021-03-05 13:04:47](https://github.com/leanprover-community/mathlib/commit/97d13d7)
feat(algebra/lie/subalgebra): define the Lie subalgebra generated by a subset ([#6549](https://github.com/leanprover-community/mathlib/pull/6549))
The work here is a lightly-edited copy-paste of the corresponding results for Lie submodules

### [2021-03-05 11:27:59](https://github.com/leanprover-community/mathlib/commit/d90448c)
chore(linear_algebra/*): changes to finsupp_vectorspaces and move module doc dual ([#6516](https://github.com/leanprover-community/mathlib/pull/6516))
This PR does the following:
- move the module doc of `linear_algebra.dual` so that it is recognised by the linter.
- add `ker_eq_bot_iff_range_eq_top_of_findim_eq_findim` to `linear_algebra.finite_dimensional`, this replaces `injective_of_surjective` in `linear_algebra.finsupp_vectorspaces`
- remove `eq_bot_iff_dim_eq_zero` from `linear_algebra.finsupp_vectorspaces`, this already exists as `dim_eq_zero` in `linear_algebra.finite_dimensional`
- changed `cardinal_mk_eq_cardinal_mk_field_pow_dim` and `cardinal_lt_omega_of_dim_lt_omega` to assume `finite_dimensional K V` instead of `dim < omega`.
- renamed `cardinal_lt_omega_of_dim_lt_omega` to `cardinal_lt_omega_of_finite_dimensional` since the assumption changed.
- provided a module doc for `linear_algebra.finsupp_vectorspaces` which should remove `linear_algebra.*` from the style exceptions file.
This file should probably be looked at again by someone more experienced in the linear_algebra part of the library. It seems to me that most of the statements in this file in fact would better fit in other files.

### [2021-03-05 08:42:35](https://github.com/leanprover-community/mathlib/commit/c782e28)
chore(analysis/normed_space/units): add `protected`, minor review ([#6544](https://github.com/leanprover-community/mathlib/pull/6544))

### [2021-03-05 08:42:34](https://github.com/leanprover-community/mathlib/commit/f158f25)
feat(data/mv_polynomial/basic): add is_scalar_tower and smul_comm_class instances ([#6542](https://github.com/leanprover-community/mathlib/pull/6542))
This also fixes the `semimodule` instance to not require `comm_semiring R`

### [2021-03-05 05:37:32](https://github.com/leanprover-community/mathlib/commit/340dd69)
fix(*): remove some simp lemmas ([#6541](https://github.com/leanprover-community/mathlib/pull/6541))
All of these simp lemmas are also declared in core. 
Maybe one of the copies can be removed in a future PR, but this PR is just to remove the duplicate simp attributes.
This is part of fixing linting problems in core, done in leanprover-community/lean[#545](https://github.com/leanprover-community/mathlib/pull/545). 
Most of the duplicate simp lemmas are fixed in `core`, but I prefer to remove the simp attribute here in mathlib if the simp lemmas were already used in core.

### [2021-03-05 04:34:20](https://github.com/leanprover-community/mathlib/commit/990a5bb)
chore(analysis/normed_space/extend): remove unnecessary imports ([#6538](https://github.com/leanprover-community/mathlib/pull/6538))
Remove two imports.  `import analysis.complex.basic` is actually unnecessary, `import analysis.normed_space.operator_norm` is indirectly imported via `data.complex.is_R_or_C`.

### [2021-03-05 02:26:15](https://github.com/leanprover-community/mathlib/commit/10aaddd)
chore(scripts): update nolints.txt ([#6543](https://github.com/leanprover-community/mathlib/pull/6543))
I am happy to remove some nolints for you!

### [2021-03-05 00:23:57](https://github.com/leanprover-community/mathlib/commit/d2cc044)
chore(algebra/algebra/basic): add a missing coe lemma ([#6535](https://github.com/leanprover-community/mathlib/pull/6535))
This is just to stop the terrible pain of having to work with `⇑(e.to_ring_equiv) x` in goals.
In the long run, we should sort out the simp normal form, but for now I just want to stop the pain.

### [2021-03-04 21:18:05](https://github.com/leanprover-community/mathlib/commit/ef1a00b)
feat(data/finsupp, algebra/monoid_algebra): add is_scalar_tower and smul_comm_class ([#6534](https://github.com/leanprover-community/mathlib/pull/6534))
This stops just short of transferring these instances to `polynomial` and `mv_polynomial`.

### [2021-03-04 21:18:04](https://github.com/leanprover-community/mathlib/commit/0dfba50)
feat(algebra/algebra/basic): alg_equiv.of_linear_equiv ([#6495](https://github.com/leanprover-community/mathlib/pull/6495))

### [2021-03-04 21:18:02](https://github.com/leanprover-community/mathlib/commit/744e79c)
feat(algebra/ordered_*, */sub{monoid,group,ring,semiring,field,algebra}): pullback of ordered algebraic structures under an injective map ([#6489](https://github.com/leanprover-community/mathlib/pull/6489))
Prove that the following 14 order typeclasses can be pulled back via an injective map (`function.injective.*`), and use them to attach 30 new instances to sub-objects:
* `ordered_comm_monoid` (and the implied `ordered_add_comm_monoid`)
  * `submonoid.to_ordered_comm_monoid`
  * `submodule.to_ordered_add_comm_monoid`
* `ordered_comm_group` (and the implied `ordered_add_comm_group`)
  * `subgroup.to_ordered_comm_group`
  * `submodule.to_ordered_add_comm_group`
* `ordered_cancel_comm_monoid` (and the implied `ordered_cancel_add_comm_monoid`)
  * `submonoid.to_ordered_cancel_comm_monoid`
  * `submodule.to_ordered_cancel_add_comm_monoid`
* `linear_ordered_cancel_comm_monoid` (and the implied `linear_ordered_cancel_add_comm_monoid`)
  * `submonoid.to_linear_ordered_cancel_comm_monoid`
  *  `submodule.to_linear_ordered_cancel_add_comm_monoid`
* `linear_ordered_comm_monoid_with_zero`
  * (no suitable subobject exists for monoid_with_zero)
* `linear_ordered_comm_group` (and the implied `linear_ordered_add_comm_group`)
  * `subgroup.to_linear_ordered_comm_group`
  * `submodule.to_linear_ordered_add_comm_group`
* `ordered_semiring`
  * `subsemiring.to_ordered_semiring`
  * `subalgebra.to_ordered_semiring`
* `ordered_comm_semiring`
  * `subsemiring.to_ordered_comm_semiring`
  * `subalgebra.to_ordered_comm_semiring`
* `ordered_ring`
  * `subring.to_ordered_ring`
  * `subalgebra.to_ordered_ring`
* `ordered_comm_ring`
  * `subring.to_ordered_comm_ring`
  * `subalgebra.to_ordered_comm_ring`
* `linear_ordered_semiring`
  * `subring.to_linear_ordered_semiring`
  * `subalgebra.to_linear_ordered_semiring`
* `linear_ordered_ring`
  * `subring.to_linear_ordered_ring`
  * `subalgebra.to_linear_ordered_ring`
* `linear_ordered_comm_ring`
  * `subring.to_linear_ordered_comm_ring`
  * `subalgebra.to_linear_ordered_comm_ring`
* `linear_ordered_field`
  * `subfield.to_linear_ordered_field`
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/rings.20from.20subtype

### [2021-03-04 21:18:00](https://github.com/leanprover-community/mathlib/commit/09273ae)
feat(measure_theory/probability_mass_function): Generalize bind on pmfs to binding on the support ([#6210](https://github.com/leanprover-community/mathlib/pull/6210))

### [2021-03-04 17:49:12](https://github.com/leanprover-community/mathlib/commit/8c72ca3)
feat(data/mv_polynomial/basic): a polynomial ring over an R-algebra is also an R-algebra ([#6533](https://github.com/leanprover-community/mathlib/pull/6533))

### [2021-03-04 17:49:11](https://github.com/leanprover-community/mathlib/commit/84f4d5c)
feat(order/zorn): nonempty formulation of Zorn's lemma ([#6532](https://github.com/leanprover-community/mathlib/pull/6532))
In practice it's often helpful to have this alternate formulation of Zorn's lemma

### [2021-03-04 17:49:10](https://github.com/leanprover-community/mathlib/commit/dbddee6)
feat(topology/continuous_on): add `set.left_inv_on.map_nhds_within_eq` ([#6529](https://github.com/leanprover-community/mathlib/pull/6529))
Also add some trivial lemmas to `data/set/function` and
`order/filter/basic`.

### [2021-03-04 17:49:09](https://github.com/leanprover-community/mathlib/commit/0690d97)
feat(bounded_continuous_function): norm_lt_of_compact ([#6524](https://github.com/leanprover-community/mathlib/pull/6524))

### [2021-03-04 17:49:08](https://github.com/leanprover-community/mathlib/commit/10d2e70)
feat(order/lattice): "algebraic" constructors for (semi-)lattices ([#6460](https://github.com/leanprover-community/mathlib/pull/6460))
I also added a module doc string for `order/lattice.lean`.

### [2021-03-04 16:01:55](https://github.com/leanprover-community/mathlib/commit/1cc59b9)
feat(set_theory/cardinal, data/nat/fincard): Define `nat`- and `enat`-valued cardinalities ([#6494](https://github.com/leanprover-community/mathlib/pull/6494))
Defines `cardinal.to_nat` and `cardinal.to_enat`
Uses those to define `nat.card` and `enat.card`

### [2021-03-04 14:43:48](https://github.com/leanprover-community/mathlib/commit/9607dbd)
feat(analysis/convex): linear image of segment ([#6531](https://github.com/leanprover-community/mathlib/pull/6531))

### [2021-03-04 14:43:47](https://github.com/leanprover-community/mathlib/commit/a8d285c)
feat(algebra/direct_sum_graded): endow `direct_sum` with a ring structure ([#6053](https://github.com/leanprover-community/mathlib/pull/6053))
To quote the module docstring
> This module provides a set of heterogenous typeclasses for defining a multiplicative structure
> over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
> additively-graded ring. The typeclasses are:
> 
> * `direct_sum.ghas_one A`
> * `direct_sum.ghas_mul A`
> * `direct_sum.gmonoid A`
> * `direct_sum.gcomm_monoid A`
> 
> Respectively, these imbue the direct sum `⨁ i, A i` with:
> 
> * `has_one`
> * `mul_zero_class`, `distrib`
> * `semiring`, `ring`
> * `comm_semiring`, `comm_ring`
>
> Additionally, this module provides helper functions to construct `gmonoid` and `gcomm_monoid`
> instances for:
> 
> * `A : ι → submonoid S`: `direct_sum.ghas_one.of_submonoids`, `direct_sum.ghas_mul.of_submonoids`,
>   `direct_sum.gmonoid.of_submonoids`, `direct_sum.gcomm_monoid.of_submonoids`
> * `A : ι → submonoid S`: `direct_sum.ghas_one.of_subgroups`, `direct_sum.ghas_mul.of_subgroups`,
>   `direct_sum.gmonoid.of_subgroups`, `direct_sum.gcomm_monoid.of_subgroups`
> 
> If the `A i` are disjoint, these provide a gradation of `⨆ i, A i`, and the mapping
> `⨁ i, A i →+ ⨆ i, A i` can be obtained as
> `direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

### [2021-03-04 13:58:56](https://github.com/leanprover-community/mathlib/commit/edbbecb)
doc(group_theory/sylow): module doc ([#6477](https://github.com/leanprover-community/mathlib/pull/6477))
This PR provides the last module doc which was missing from `group_theory`, namely that for `sylow`.

### [2021-03-04 11:33:23](https://github.com/leanprover-community/mathlib/commit/d32bb6e)
feat(data/finsupp/basic): add support_nonempty_iff and nonzero_iff_exists ([#6530](https://github.com/leanprover-community/mathlib/pull/6530))
Add two lemmas to work with `finsupp`s with non-empty support.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/finsupp.2Enonzero_iff_exists

### [2021-03-04 11:33:22](https://github.com/leanprover-community/mathlib/commit/ca96bfb)
feat(linear_algebra/clifford_algebra): add definitions of the conjugation operators and some API ([#6491](https://github.com/leanprover-community/mathlib/pull/6491))
This also replaces the file with a directory, to avoid monstrous files from developing.

### [2021-03-04 11:33:21](https://github.com/leanprover-community/mathlib/commit/deb3d45)
feat(data/mv_polynomial/equiv): generalize ring_equiv_congr ([#6420](https://github.com/leanprover-community/mathlib/pull/6420))
Following the discussion in [#6324](https://github.com/leanprover-community/mathlib/pull/6324), I have modified `mv_polynomial.ring_equiv_of_equiv` and `mv_polynomial.ring_equiv_congr`, that are now called `ring_equiv_congr_left` and `ring_equiv_congr_left`: both are proved as special cases of `ring_equiv_congr` (the situation for algebras is exactly the same).
This has the side effect that the lemmas automatically generated by `@[simps]` are not in a good form (see for example the lemma `mv_polynomial.alg_equiv_congr_left_apply ` in the current mathlib, where there is an unwanted `alg_equiv.refl.to_ring_equiv`). To avoid this I deleted the `@[simps]` and I wrote the lemmas by hand (also correcting the problem with `mv_polynomial.alg_equiv_congr_left_apply`). I probably don't understand completely `@[simps]`, since I had to manually modified some other proofs that no longer worked (I mean, I had to do something more that just using the new names).
If there is some `simp` lemma I forgot I would be happy to write it.

### [2021-03-04 08:43:30](https://github.com/leanprover-community/mathlib/commit/3329ec4)
chore(topology/algebra/*): tendsto namespacing ([#6528](https://github.com/leanprover-community/mathlib/pull/6528))
Correct a few lemmas which I noticed were namespaced as `tendsto.***` rather than `filter.tendsto.***`, and thus couldn't be used with projection notation.
Also use the projection notation, where now permitted.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Search.20for.20all.20declarations.20in.20a.20namespace)

### [2021-03-04 08:43:29](https://github.com/leanprover-community/mathlib/commit/76aee25)
refactor(big_operators/basic): move prod_mul_prod_compl ([#6526](https://github.com/leanprover-community/mathlib/pull/6526))
Several lemmas were unnecessarily in `src/data/fintype/card.lean`, and I've relocated them to `src/algebra/big_operators/basic.lean`.

### [2021-03-04 08:43:28](https://github.com/leanprover-community/mathlib/commit/d7fa1bc)
feat(topology/instances/real): generalize 'compact_space I' to 'compact_space (Icc a b)' ([#6523](https://github.com/leanprover-community/mathlib/pull/6523))

### [2021-03-04 08:43:27](https://github.com/leanprover-community/mathlib/commit/2f35779)
chore(*/sub*): tidy up inherited algebraic structures from parent objects ([#6509](https://github.com/leanprover-community/mathlib/pull/6509))
This changes `subfield.to_field` to ensure that division is defeq.
It also removes `subring.subset_comm_ring` which was identical to `subring.to_comm_ring`, renames some `subalgebra` instances to match those of `subring`s, and cleans up a few related proofs that relied on the old names.
These are cleanups split from [#6489](https://github.com/leanprover-community/mathlib/pull/6489), which failed CI but was otherwise approved

### [2021-03-04 07:49:34](https://github.com/leanprover-community/mathlib/commit/f4db322)
feat(category_theory/subobject): factoring morphisms through subobjects ([#6302](https://github.com/leanprover-community/mathlib/pull/6302))
The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.
We provide conditions for `P.factors f`, when `P` is a kernel/equalizer/image/inf/sup subobject.

### [2021-03-04 02:11:25](https://github.com/leanprover-community/mathlib/commit/8289518)
feat(algebra/star): the Bell/CHSH/Tsirelson inequalities ([#4687](https://github.com/leanprover-community/mathlib/pull/4687))

### [2021-03-04 01:15:55](https://github.com/leanprover-community/mathlib/commit/2837807)
chore(scripts): update nolints.txt ([#6527](https://github.com/leanprover-community/mathlib/pull/6527))
I am happy to remove some nolints for you!

### [2021-03-03 13:41:37](https://github.com/leanprover-community/mathlib/commit/3c9399d)
chore(algebra/ordered_group): put to_additive on lemmas about linear_ordered_comm_group ([#6506](https://github.com/leanprover-community/mathlib/pull/6506))
No lemmas are added or renamed for the additive version, this just adds lemmas (and more importantly instances) for the multiplicative version.
This:
* Adds missing `ancestor` attributes to `linear_ordered_add_comm_group` and `linear_ordered_comm_group`, which are needed to make `to_additive` work correctly on `to_add_comm_group` and `to_comm_group`
* Adds multiplicative versions of:
  * `sub_le_self_iff` (`div_le_self_iff`)
  * `sub_lt_self_iff` (`div_lt_self_iff `)
  * `linear_ordered_add_comm_group.to_linear_ordered_cancel_add_comm_monoid` (`linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid`)
  * `linear_ordered_add_comm_group.add_lt_add_left` (`linear_ordered_comm_group.mul_lt_mul_left'`)
  * `min_neg_neg` (`min_inv_inv'`)
  * `max_neg_neg` (`max_inv_inv'`)
  * `min_sub_sub_right` (`min_div_div_right'`)
  * `min_sub_sub_left` (`min_div_div_left'`)
  * `max_sub_sub_right` (`max_div_div_right'`)
  * `max_sub_sub_left` (`max_div_div_left'`)
  * `max_zero_sub_eq_self` (`max_one_div_eq_self'`)
  * `eq_zero_of_neg_eq` (`eq_one_of_inv_eq'`)
  * `exists_zero_lt` (`exists_one_lt'`)

### [2021-03-03 13:41:37](https://github.com/leanprover-community/mathlib/commit/d4ac4c3)
feat(data/list/basic): add `list.prod_eq_zero(_iff)` ([#6504](https://github.com/leanprover-community/mathlib/pull/6504))
API changes:
* add `list.prod_eq_zero`, `list.prod_eq_zero_iff`, ;
* lemmas `list.prod_ne_zero`, `multiset.prod_ne_zero`, `polynomial.root_list_prod`, `polynomial.roots_multiset_prod`, `polynomial.nat_degree_multiset_prod`,  now assume `0 ∉ L` (or `0 ∉ m`/`0 ∉ s`) instead of `∀ x ∈ L, x ≠ 0`

### [2021-03-03 13:41:36](https://github.com/leanprover-community/mathlib/commit/a852bf4)
feat(data/equiv/fin): fin_add_flip and fin_rotate ([#6454](https://github.com/leanprover-community/mathlib/pull/6454))
Add
* `fin_add_flip : fin (m + n) ≃ fin (n + m)`
* `fin_rotate : Π n, fin n ≃ fin n` (acts by +1 mod n)
and simp lemmas, and shows `fin.snoc` is a rotation of `fin.cons`.

### [2021-03-03 10:36:54](https://github.com/leanprover-community/mathlib/commit/9c48eb1)
chore(ring_theory/{subring,integral_closure}): simplify a proof, remove redundant instances ([#6513](https://github.com/leanprover-community/mathlib/pull/6513))

### [2021-03-03 10:36:53](https://github.com/leanprover-community/mathlib/commit/eec54d0)
feat(algebra/field): add function.injective.field ([#6511](https://github.com/leanprover-community/mathlib/pull/6511))
We already have defs of this style for all sorts of algebraic constructions, why not one more.

### [2021-03-03 10:36:52](https://github.com/leanprover-community/mathlib/commit/3309ce2)
refactor(ring_theory/polynomial/chebyshev): move lemmas around ([#6510](https://github.com/leanprover-community/mathlib/pull/6510))
As discussed in [#6501](https://github.com/leanprover-community/mathlib/pull/6501), split up the old file `ring_theory.polynomial.chebyshev.basic`, moving half its contents to `ring_theory.polynomial.chebyshev.defs` and the other half to `ring_theory.polynomial.chebyshev.dickson`.

### [2021-03-03 07:35:46](https://github.com/leanprover-community/mathlib/commit/383dd2b)
chore(data/equiv): add missing simp lemmas about mk ([#6505](https://github.com/leanprover-community/mathlib/pull/6505))
This adds missing `mk_coe` lemmas, and new `symm_mk`, `symm_bijective`, and `mk_coe'` lemmas.

### [2021-03-02 23:24:10](https://github.com/leanprover-community/mathlib/commit/22e3437)
feat(algebra/big_operators/basic): lemmas prod_range_add, sum_range_add ([#6484](https://github.com/leanprover-community/mathlib/pull/6484))

### [2021-03-02 22:25:31](https://github.com/leanprover-community/mathlib/commit/19ed0f8)
refactor(ring_theory/valuation): valuations in `linear_ordered_comm_monoid_with_zero` ([#6500](https://github.com/leanprover-community/mathlib/pull/6500))
Generalizes the value group in a `valuation` to a `linear_ordered_comm_monoid_with_zero`

### [2021-03-02 19:27:12](https://github.com/leanprover-community/mathlib/commit/0c5b517)
feat(ring_theory/polynomial/chebyshev/basic): multiplication of Chebyshev polynomials ([#6501](https://github.com/leanprover-community/mathlib/pull/6501))
Add the identity for multiplication of Chebyshev polynomials,
```lean
2 * chebyshev₁ R m * chebyshev₁ R (m + k) = chebyshev₁ R (2 * m + k) + chebyshev₁ R k
```
Use this to give a direct proof of the identity `chebyshev₁_mul` for composition of Chebyshev polynomials, replacing the current proof using trig functions.  This means that the import `import analysis.special_functions.trigonometric` to the Chebyshev file can be removed.

### [2021-03-02 19:27:11](https://github.com/leanprover-community/mathlib/commit/0c863e9)
refactor(data/set/finite): change type of `set.finite.dependent_image` ([#6475](https://github.com/leanprover-community/mathlib/pull/6475))
The old lemma combined a statement similar to `set.finite.image` with
`set.finite.subset`. The new statement is a direct generalization of
`set.finite.image`.

### [2021-03-02 16:36:18](https://github.com/leanprover-community/mathlib/commit/c087011)
refactor(data/set/finite): make `finite` argument of `set.finite.mem_to_finset` explicit ([#6508](https://github.com/leanprover-community/mathlib/pull/6508))
This way we can use dot notation.

### [2021-03-02 15:26:34](https://github.com/leanprover-community/mathlib/commit/9f0f05e)
feat(data/{nat,int}/parity): even_mul_succ_self ([#6507](https://github.com/leanprover-community/mathlib/pull/6507))

### [2021-03-02 08:23:47](https://github.com/leanprover-community/mathlib/commit/6b5e48d)
feat(data/finset/lattice): +2 induction principles for `finset`s ([#6502](https://github.com/leanprover-community/mathlib/pull/6502))

### [2021-03-02 06:06:52](https://github.com/leanprover-community/mathlib/commit/572f727)
chore(algebra/big_operators): use weaker typeclass assumptions ([#6503](https://github.com/leanprover-community/mathlib/pull/6503))

### [2021-03-02 04:20:01](https://github.com/leanprover-community/mathlib/commit/c69c8a9)
chore(scripts): update nolints.txt ([#6499](https://github.com/leanprover-community/mathlib/pull/6499))
I am happy to remove some nolints for you!

### [2021-03-02 02:22:47](https://github.com/leanprover-community/mathlib/commit/f63069f)
feat(linear_algebra/basic): simp lemmas about endomorphisms ([#6452](https://github.com/leanprover-community/mathlib/pull/6452))
Also renames some lemmas:
* `linear_map.one_app` has been renamed to `linear_map.one_apply`
* `linear_map.mul_app` has been removed in favour of the existing `linear_map.mul_app`.

### [2021-03-02 02:22:45](https://github.com/leanprover-community/mathlib/commit/5c01613)
feat(analysis/special_functions/integrals): some simple integration lemmas ([#6216](https://github.com/leanprover-community/mathlib/pull/6216))
Integration of some simple functions, including `sin`, `cos`, `pow`, and `inv`. @ADedecker and I are working on the integrals of some more intricate functions, which we hope to add in a subsequent (series of) PR(s).
With this PR, simple integrals are now computable by `norm_num`. Here are some examples:
```
import analysis.special_functions.integrals
open real interval_integral
open_locale real
example : ∫ x in 0..π, sin x = 2 := by norm_num
example : ∫ x in 0..π/4, cos x = sqrt 2 / 2 := by simp
example : ∫ x:ℝ in 2..4, x^(3:ℕ) = 60 := by norm_num
example : ∫ x in 0..2, -exp x = 1 - exp 2 := by simp
example : ∫ x:ℝ in (-1)..4, x = 15/2 := by norm_num
example : ∫ x:ℝ in 8..11, (1:ℝ) = 3 := by norm_num
example : ∫ x:ℝ in 2..3, x⁻¹ = log (3/2) := by norm_num
example : ∫ x:ℝ in 0..1, 1 / (1 + x^2) = π/4 := by simp
```
`integral_deriv_eq_sub'` courtesy of @gebner.

### [2021-03-02 00:24:51](https://github.com/leanprover-community/mathlib/commit/5eb7ebb)
feat(data/polynomial): lemmas about polynomial derivative ([#6433](https://github.com/leanprover-community/mathlib/pull/6433))

### [2021-03-01 21:31:43](https://github.com/leanprover-community/mathlib/commit/0334475)
ci(scripts/detect_errors): try to show info messages in a way github understands ([#6493](https://github.com/leanprover-community/mathlib/pull/6493))
I don't actually know if this works, but I know that the previous code was not working:
https://github.com/leanprover-community/mathlib/pull/6485/checks?check_run_id=2006396264#step:7:7

### [2021-03-01 21:31:42](https://github.com/leanprover-community/mathlib/commit/0a5f69c)
feat(src/order/basic): show injectivity of order conversions, and tag lemmas with ext ([#6490](https://github.com/leanprover-community/mathlib/pull/6490))
Stating these as `function.injective` provides slightly more API, especially since before only the composition was proven as injective.
For convenience, this leaves behind `preorder.ext`, `partial_order.ext`, and `linear_order.ext`, although these are now provable with trivial applications of `ext`.

### [2021-03-01 21:31:41](https://github.com/leanprover-community/mathlib/commit/cc57915)
chore(data/equiv/basic): add simp lemmas about subtype_equiv ([#6479](https://github.com/leanprover-community/mathlib/pull/6479))

### [2021-03-01 21:31:40](https://github.com/leanprover-community/mathlib/commit/354fda0)
feat(linear_algebra/finsupp): add mem_span_set ([#6457](https://github.com/leanprover-community/mathlib/pull/6457))
From the doc-string:
If `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, then we can write
`m` as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`.
The initial proof was a substantial simplification of mine, due to Kevin Buzzard.  The final one is due to Eric Wieser.
Zulip discussion for the proof:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/submodule.2Espan.20as_sum
Zulip discussion for the universe issue:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universe.20issue.20with.20.60Type*.60

### [2021-03-01 21:31:39](https://github.com/leanprover-community/mathlib/commit/e0a4dd8)
feat(ring_theory/finiteness): improve API for finite presentation ([#6382](https://github.com/leanprover-community/mathlib/pull/6382))
Improve the API for finitely presented morphism. I changed the name from `algebra.finitely_presented` to `algebra.finite_presentation` that seems more coherent with the other names.
Coming soon: transitivity of finite presentation.

### [2021-03-01 18:58:11](https://github.com/leanprover-community/mathlib/commit/0faa788)
feat(ring_theory/hahn_series): introduce ring of Hahn series ([#6237](https://github.com/leanprover-community/mathlib/pull/6237))
Defines Hahn series
Provides basic algebraic structure on Hahn series, up to `comm_ring`.

### [2021-03-01 15:40:36](https://github.com/leanprover-community/mathlib/commit/e77f071)
feat(linear_algebra/{clifford,exterior,tensor}_algebra): add induction principles ([#6416](https://github.com/leanprover-community/mathlib/pull/6416))
These are closely derived from the induction principle for the free algebra.
I can't think of a good way to deduplicate them, so for now I've added comments making it clear to the reader that the code is largely copied.

### [2021-03-01 10:35:11](https://github.com/leanprover-community/mathlib/commit/aff6bd1)
fix(group_action/defs): make mul_action.regular an instance ([#6241](https://github.com/leanprover-community/mathlib/pull/6241))
This is essentially already an instance via `semiring.to_semimodule.to_distrib_mul_action.to_mul_action`, but with an unecessary `semiring R` constraint.
I can't remember the details, but I've run into multiple instance resolution issues in the past that were resolved with `local attribute [instance] mul_action.regular`.
This also renames the instance to `monoid.to_mul_action` for consistency with `semiring.to_semimodule`.

### [2021-03-01 04:31:52](https://github.com/leanprover-community/mathlib/commit/6ac19b4)
doc(algebra/ring/basic): change pullback and injective to pushforward and surjective ([#6487](https://github.com/leanprover-community/mathlib/pull/6487))
Zulip reference:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/pullback.20vs.20pushforward

### [2021-03-01 01:14:26](https://github.com/leanprover-community/mathlib/commit/9ad469d)
chore(scripts): update nolints.txt ([#6486](https://github.com/leanprover-community/mathlib/pull/6486))
I am happy to remove some nolints for you!