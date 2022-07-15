## [2020-05-31 20:01:07](https://github.com/leanprover-community/mathlib/commit/d3fc918)
chore(scripts): update nolints.txt ([#2892](https://github.com/leanprover-community/mathlib/pull/2892))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-31 18:58:17](https://github.com/leanprover-community/mathlib/commit/1fd5195)
chore(data/equiv/mul_add): review ([#2874](https://github.com/leanprover-community/mathlib/pull/2874))
* make `mul_aut` and `add_aut` reducible to get `coe_fn`
* add some `coe_*` lemmas
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* add_aut.coe_mul
- \+ *lemma* add_aut.coe_one
- \+ *lemma* equiv.coe_inv
- \+ *lemma* equiv.coe_mul_left
- \+ *lemma* equiv.coe_mul_right
- \+ *lemma* equiv.inv_symm
- \+ *lemma* equiv.mul_left_symm
- \+ *lemma* equiv.mul_right_symm
- \+ *lemma* mul_aut.coe_mul
- \+ *lemma* mul_aut.coe_one



## [2020-05-31 17:05:57](https://github.com/leanprover-community/mathlib/commit/7c7e866)
chore(*): update to lean 3.15.0 ([#2851](https://github.com/leanprover-community/mathlib/pull/2851))
The main effect for mathlib comes from https://github.com/leanprover-community/lean/pull/282, which changes the elaboration strategy for structure instance literals (`{ foo := 42 }`).  There are two points where we need to pay attention:
1. Avoid sourcing (`{ ..e }` where e.g. `e : euclidean_domain α`) for fields like `add`, `mul`, `zero`, etc.  Instead write `{ add := (+), mul := (*), zero := 0, ..e }`.  The reason is that `{ ..e }` is equivalent to `{ mul := euclidean_domain.mul, ..e }`.  And `euclidean_domain.mul` should never be mentioned.
I'm not completely sure if this issue remains visible once the structure literal has been elaborated, but this hasn't changed since 3.14.  For now, my advice is: if you get weird errors like "cannot unify `a * b` and `?m_1 * ?m_2` in a structure literal, add `mul := (*)`.
2. `refine { le := (≤), .. }; simp` is slower.  This is because references to `(≤)` are no longer reduced to `le` in the subgoals.  If a subgoal like `a ≤ b → b ≤ a → a = b` was stated for preorders (because `partial_order` extends `preorder`), then the `(≤)` will contain a `preorder` subterm.  This subterm also contains other subgoals (proofs of reflexivity and transitivity).  Therefore the goals are larger than you might expect:
```
∀ (a b : α),
    @has_le.le.{u} α
      (@preorder.to_has_le.{u} α
         (@preorder.mk.{u} α le (@lattice.lt._default.{u} α le)
            (@conditionally_complete_lattice.copy._aux_1.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (@conditionally_complete_lattice.copy._aux_2.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (λ (a b : α), iff.refl (@has_lt.lt.{u} α (@has_lt.mk.{u} α (@lattice.lt._default.{u} α le)) a b))))
      a
      b →
    @has_le.le.{u} α
      (@preorder.to_has_le.{u} α
         (@preorder.mk.{u} α le (@lattice.lt._default.{u} α le)
            (@conditionally_complete_lattice.copy._aux_1.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (@conditionally_complete_lattice.copy._aux_2.{u} α c le eq_le sup eq_sup inf eq_inf Sup eq_Sup Inf eq_Inf)
            (λ (a b : α), iff.refl (@has_lt.lt.{u} α (@has_lt.mk.{u} α (@lattice.lt._default.{u} α le)) a b))))
      b
      a →
    @eq.{u+1} α a b
```
Advice: in cases such as this, try `refine { le := (≤), .. }; abstract { simp }` to reduce the size of the (dependent) subgoals.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Lean.203.2E15.2E0).
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/free.lean


Modified src/category_theory/elements.lean
- \+ *lemma* category_theory.category_of_elements.comp_val
- \+ *lemma* category_theory.category_of_elements.ext
- \+ *lemma* category_theory.category_of_elements.id_val

Modified src/category_theory/endomorphism.lean


Modified src/category_theory/types.lean


Modified src/control/applicative.lean


Modified src/control/fold.lean


Modified src/control/traversable/instances.lean


Modified src/data/erased.lean
- \+ *lemma* erased.bind_def
- \+ *def* erased.map
- \+ *lemma* erased.map_def
- \+ *theorem* erased.map_out
- \+/\- *theorem* erased.nonempty_iff
- \+ *lemma* erased.out_inj
- \+/\- *def* erased.out_type
- \+ *lemma* erased.pure_def
- \+/\- *def* erased

Modified src/data/list/defs.lean
- \- *def* list.map_with_index
- \- *def* list.map_with_index_core

Modified src/data/multiset.lean
- \+ *lemma* multiset.bind_def
- \+ *lemma* multiset.fmap_def
- \+ *lemma* multiset.pure_def

Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \- *def* padic_int.add
- \- *lemma* padic_int.add_def
- \+/\- *lemma* padic_int.coe_add
- \+/\- *lemma* padic_int.coe_coe
- \+/\- *lemma* padic_int.coe_mul
- \+/\- *lemma* padic_int.coe_neg
- \+/\- *lemma* padic_int.coe_one
- \+/\- *lemma* padic_int.coe_zero
- \+ *lemma* padic_int.ext
- \+/\- *lemma* padic_int.mk_coe
- \- *def* padic_int.mul
- \- *lemma* padic_int.mul_def
- \- *def* padic_int.neg
- \+/\- *lemma* padic_int.val_eq_coe
- \- *lemma* padic_int.zero_def
- \+ *lemma* padic_norm_z
- \- *def* padic_norm_z

Modified src/data/semiquot.lean
- \+ *lemma* semiquot.bind_def
- \+ *lemma* semiquot.map_def

Modified src/data/set/lattice.lean


Modified src/data/string/basic.lean


Modified src/group_theory/submonoid.lean
- \+ *lemma* submonoid.coe_eq_coe

Modified src/linear_algebra/dual.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/order/copy.lean


Modified src/tactic/doc_commands.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/category/UniformSpace.lean




## [2020-05-31 15:03:10](https://github.com/leanprover-community/mathlib/commit/25fc0a8)
feat(field_theory/splitting_field): lemmas ([#2887](https://github.com/leanprover-community/mathlib/pull/2887))
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *theorem* polynomial.splits_X_sub_C
- \+ *theorem* polynomial.splits_id_iff_splits
- \+ *theorem* polynomial.splits_mul_iff
- \+ *theorem* polynomial.splits_one
- \+ *theorem* polynomial.splits_prod
- \+ *theorem* polynomial.splits_prod_iff



## [2020-05-31 06:22:54](https://github.com/leanprover-community/mathlib/commit/13b34b3)
chore(*): split long lines ([#2883](https://github.com/leanprover-community/mathlib/pull/2883))
Also move docs for `control/fold` from a comment to a module docstring.
#### Estimated changes
Modified src/algebra/commute.lean


Modified src/algebra/free.lean
- \+/\- *def* free_add_semigroup.lift'
- \+/\- *lemma* free_semigroup.traverse_pure'
- \+/\- *lemma* free_semigroup.traverse_pure

Modified src/algebra/pi_instances.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/connected.lean
- \+/\- *lemma* category_theory.constant_of_preserves_morphisms

Modified src/category_theory/endomorphism.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* category_theory.nat_iso.hom_inv_id_app
- \+/\- *lemma* category_theory.nat_iso.inv_hom_id_app

Modified src/category_theory/products/basic.lean


Modified src/control/fold.lean
- \+/\- *def* monoid.mfoldl
- \+/\- *lemma* traversable.foldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* traversable.foldr.of_free_monoid_comp_free_mk
- \+/\- *lemma* traversable.mfoldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* traversable.mfoldr.of_free_monoid_comp_free_mk

Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.prod_comm

Modified src/data/list/pairwise.lean


Modified src/data/option/basic.lean
- \+/\- *theorem* option.bind_eq_some'
- \+/\- *theorem* option.bind_eq_some
- \+/\- *theorem* option.map_eq_some'
- \+/\- *theorem* option.map_eq_some

Modified src/group_theory/subgroup.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* sesq_form.ext

Modified src/measure_theory/measurable_space.lean


Modified src/meta/expr.lean


Modified src/topology/basic.lean


Modified src/topology/category/Top/opens.lean
- \+/\- *lemma* topological_space.opens.map_comp_hom_app
- \+/\- *lemma* topological_space.opens.map_comp_inv_app
- \+/\- *lemma* topological_space.opens.map_comp_obj'
- \+/\- *lemma* topological_space.opens.map_comp_obj
- \+/\- *lemma* topological_space.opens.map_comp_obj_unop
- \+/\- *lemma* topological_space.opens.op_map_comp_obj

Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/order.lean
- \+/\- *lemma* continuous_of_discrete_topology

Modified src/topology/uniform_space/basic.lean




## [2020-05-31 04:59:04](https://github.com/leanprover-community/mathlib/commit/a285049)
chore(algebra/group_hom): rename `add_monoid.smul` to `nsmul` ([#2861](https://github.com/leanprover-community/mathlib/pull/2861))
Also drop `•` as a notation for two `smul`s  declared in this file,
use `•ℕ` and `•ℤ` instead.
This way one can immediately see that a lemma uses `nsmul`/`gsmul`, not `has_scalar.smul`.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_nsmul
- \- *lemma* finset.sum_smul'

Modified src/algebra/commute.lean
- \+ *theorem* commute.nsmul_left
- \+ *theorem* commute.nsmul_nsmul
- \+ *theorem* commute.nsmul_right
- \+ *theorem* commute.nsmul_self
- \+ *theorem* commute.self_nsmul
- \+ *theorem* commute.self_nsmul_nsmul
- \- *theorem* commute.self_smul
- \- *theorem* commute.self_smul_smul
- \- *theorem* commute.smul_left
- \- *theorem* commute.smul_right
- \- *theorem* commute.smul_self
- \- *theorem* commute.smul_smul

Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power.lean
- \+/\- *theorem* add_gsmul
- \- *theorem* add_monoid.add_smul
- \- *theorem* add_monoid.mul_smul'
- \- *theorem* add_monoid.mul_smul
- \- *theorem* add_monoid.mul_smul_assoc
- \- *theorem* add_monoid.mul_smul_left
- \- *theorem* add_monoid.neg_smul
- \- *theorem* add_monoid.one_smul
- \- *def* add_monoid.smul
- \- *theorem* add_monoid.smul_add
- \- *theorem* add_monoid.smul_eq_mul'
- \- *theorem* add_monoid.smul_eq_mul
- \- *theorem* add_monoid.smul_le_smul
- \- *lemma* add_monoid.smul_le_smul_of_le_right
- \- *theorem* add_monoid.smul_neg_comm
- \- *theorem* add_monoid.smul_nonneg
- \- *theorem* add_monoid.smul_one
- \- *theorem* add_monoid.smul_sub
- \- *theorem* add_monoid.smul_zero
- \- *theorem* add_monoid.zero_smul
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+ *theorem* add_monoid_hom.map_nsmul
- \- *theorem* add_monoid_hom.map_smul
- \+ *theorem* add_nsmul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* bit0_gsmul
- \+ *theorem* bit0_nsmul
- \- *theorem* bit0_smul
- \+/\- *theorem* bit1_gsmul
- \+ *theorem* bit1_nsmul
- \- *theorem* bit1_smul
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* gsmul_zero
- \+ *theorem* is_add_monoid_hom.map_nsmul
- \- *theorem* is_add_monoid_hom.map_smul
- \+/\- *theorem* list.sum_repeat
- \+ *theorem* mul_nsmul'
- \+ *theorem* mul_nsmul
- \+ *theorem* mul_nsmul_assoc
- \+ *theorem* mul_nsmul_left
- \+ *theorem* nat.nsmul_eq_mul
- \- *theorem* nat.smul_eq_mul
- \+/\- *theorem* neg_gsmul
- \+ *theorem* neg_nsmul
- \+/\- *theorem* neg_one_gsmul
- \+ *def* nsmul
- \+ *theorem* nsmul_add
- \+ *theorem* nsmul_add_comm'
- \+ *theorem* nsmul_add_comm
- \+ *theorem* nsmul_eq_mul'
- \+ *theorem* nsmul_eq_mul
- \+ *theorem* nsmul_le_nsmul
- \+ *lemma* nsmul_le_nsmul_of_le_right
- \+ *theorem* nsmul_neg_comm
- \+ *theorem* nsmul_nonneg
- \+ *theorem* nsmul_one
- \+ *theorem* nsmul_sub
- \+ *theorem* nsmul_zero
- \+ *lemma* of_add_nsmul
- \- *lemma* of_add_smul
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* one_gsmul
- \+ *theorem* one_nsmul
- \- *theorem* smul_add_comm'
- \- *theorem* smul_add_comm
- \+ *theorem* succ_nsmul'
- \+ *theorem* succ_nsmul
- \- *theorem* succ_smul'
- \- *theorem* succ_smul
- \+ *theorem* two_nsmul
- \- *theorem* two_smul'
- \+ *lemma* with_bot.coe_nsmul
- \- *lemma* with_bot.coe_smul
- \+/\- *theorem* zero_gsmul
- \+ *theorem* zero_nsmul

Modified src/algebra/iterate_hom.lean


Modified src/algebra/module.lean
- \- *lemma* semimodule.add_monoid_smul_eq_smul
- \+ *lemma* semimodule.nsmul_eq_smul

Modified src/algebra/semiconj.lean
- \+ *lemma* semiconj_by.nsmul_left
- \+ *lemma* semiconj_by.nsmul_nsmul
- \+ *lemma* semiconj_by.nsmul_right
- \- *lemma* semiconj_by.smul_left
- \- *lemma* semiconj_by.smul_right
- \- *lemma* semiconj_by.smul_smul

Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset.lean
- \+ *lemma* multiset.to_finset_nsmul
- \- *lemma* multiset.to_finset_smul

Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.to_multiset_single

Modified src/data/multiset.lean
- \+/\- *theorem* multiset.count_smul
- \+/\- *theorem* multiset.sum_repeat

Modified src/data/mv_polynomial.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/pnat/factors.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.degree_pow_le

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.nsmul_coe
- \- *lemma* nnreal.smul_coe

Modified src/field_theory/finite.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/submonoid.lean
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* multiples.zero_mem
- \+/\- *def* multiples

Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/multilinear.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/subsemiring.lean


Modified src/tactic/abel.lean
- \+/\- *def* tactic.abel.smul
- \+/\- *def* tactic.abel.smulg
- \+/\- *def* tactic.abel.term
- \+/\- *def* tactic.abel.termg



## [2020-05-31 01:56:14](https://github.com/leanprover-community/mathlib/commit/28e79d4)
chore(data/set/basic): add some lemmas to `function.surjective` ([#2876](https://github.com/leanprover-community/mathlib/pull/2876))
This way they can be used with dot notation. Also rename
`set.surjective_preimage` to
`function.surjective.injective_preimage`. I think that the old name
was misleading.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* function.surjective.injective_preimage
- \+ *lemma* function.surjective.range_comp
- \+ *lemma* function.surjective.range_eq
- \- *lemma* set.surjective_preimage



## [2020-05-31 01:56:12](https://github.com/leanprover-community/mathlib/commit/297806e)
feat(topology/homeomorph): sum_prod_distrib ([#2870](https://github.com/leanprover-community/mathlib/pull/2870))
Also modify the `inv_fun` of `equiv.sum_prod_distrib` to have
more useful definitional behavior. This also simplifies
`measurable_equiv.sum_prod_distrib`.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/measure_theory/measurable_space.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* continuous_inl
- \+/\- *lemma* continuous_inr
- \+/\- *lemma* embedding_inl
- \+/\- *lemma* embedding_inr
- \+ *lemma* is_open_map_sum
- \+ *lemma* is_open_sum_iff
- \+ *lemma* open_embedding_inl
- \+ *lemma* open_embedding_inr

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.prod_sum_distrib
- \+ *def* homeomorph.sum_congr
- \+ *def* homeomorph.sum_prod_distrib



## [2020-05-30 22:43:58](https://github.com/leanprover-community/mathlib/commit/0827a30)
feat(tactic/noncomm_ring): add noncomm_ring tactic ([#2858](https://github.com/leanprover-community/mathlib/pull/2858))
Fixes https://github.com/leanprover-community/mathlib/issues/2727
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean


Modified src/algebra/group_power.lean
- \+ *lemma* bit0_mul
- \+ *lemma* bit1_mul
- \+ *lemma* mul_bit0
- \+ *lemma* mul_bit1

Modified src/algebra/lie_algebra.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/tactic/default.lean


Added src/tactic/noncomm_ring.lean


Added test/noncomm_ring.lean




## [2020-05-30 21:15:08](https://github.com/leanprover-community/mathlib/commit/6e581ef)
chore(scripts): update nolints.txt ([#2878](https://github.com/leanprover-community/mathlib/pull/2878))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-30 19:55:19](https://github.com/leanprover-community/mathlib/commit/c034b4c)
chore(order/bounds): +2 lemmas, fix a name ([#2877](https://github.com/leanprover-community/mathlib/pull/2877))
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* mem_lower_bounds
- \+ *lemma* mem_upper_bounds
- \+ *lemma* monotone.le_is_glb_image
- \- *lemma* monotone.le_is_glb_image_le



## [2020-05-30 19:08:27](https://github.com/leanprover-community/mathlib/commit/9d76ac2)
chore(scripts): update nolints.txt ([#2873](https://github.com/leanprover-community/mathlib/pull/2873))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-30 18:01:32](https://github.com/leanprover-community/mathlib/commit/f05acc8)
feat(group_theory/group_action): orbit_equiv_quotient_stabilizer_symm_apply and docs ([#2864](https://github.com/leanprover-community/mathlib/pull/2864))
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+ *theorem* mul_action.orbit_equiv_quotient_stabilizer_symm_apply



## [2020-05-30 16:24:08](https://github.com/leanprover-community/mathlib/commit/67f1951)
refactor(algebra/module): change module into an abbreviation for semimodule ([#2848](https://github.com/leanprover-community/mathlib/pull/2848))
The file `algebra/module.lean` contains the lines
```
There were several attempts to make `module` an abbreviation of `semimodule` but this makes
  class instance search too hard for Lean 3.
```
It turns out that this was too hard for Lean 3 until recently, but this is not too hard for Lean 3.14. This PR removes these two lines, and changes the files accordingly.
This means that the basic objects of linear algebra are now semimodules over semiring, making it possible to talk about matrices with natural number coefficients or apply general results on multilinear maps to get the binomial or the multinomial formula.
A linear map is now defined over semirings, between semimodules which are `add_comm_monoid`s. For some statements, you need to have an `add_comm_group`, and a `ring` or a `comm_semiring` or a `comm_ring`. I have not tried to lower the possible typeclass assumptions like this in all files, but I have done it carefully in the following files:
* `algebra/module`
* `linear_algebra/basic`
* `linear_algebra/multilinear`
* `topology/algebra/module`
* `topology/algebra/multilinear`
Other files can be optimised later in the same way when needed, but this PR is already big enough.
I have also fixed the breakage in all the other files. It was sometimes completely mysterious (in tensor products, I had to replace several times `linear_map.id.flip` with `linear_map.flip linear_map.id`), but globally all right. I have tweaked a few instance priorities to make sure that things don't go too bad: there are often additional steps in typeclass inference, going from `ring` to `semiring` and from `add_comm_group` to `add_comm_monoid`, so I have increased their priority (putting it strictly between 100 and 1000), and adjusted some other priorities to get more canonical instance paths, fixing some preexisting weirdnesses (notably in multilinear maps). One place where I really had to help Lean is with normed spaces of continuous multilinear maps, where instance search is just too big.
I am aware that this will be a nightmare to refer, but as often with big refactor it's an "all or nothing" PR, impossible to split in tiny pieces.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean
- \+/\- *lemma* is_linear_map.is_linear_map_neg
- \+/\- *lemma* is_linear_map.is_linear_map_smul'
- \+/\- *lemma* is_linear_map.is_linear_map_smul
- \+/\- *lemma* is_linear_map.map_neg
- \+/\- *def* linear_map.id
- \+/\- *lemma* linear_map.id_apply
- \+/\- *lemma* linear_map.map_sum
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \- *def* module.of_core
- \- *def* ring_hom.to_module
- \+ *def* semimodule.of_core
- \+/\- *theorem* smul_neg
- \+/\- *lemma* submodule.add_mem_iff_left
- \+/\- *lemma* submodule.add_mem_iff_right
- \+/\- *lemma* submodule.neg_mem_iff
- \- *def* subspace

Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.smul_apply
- \+/\- *def* dfinsupp.to_has_scalar
- \- *def* dfinsupp.to_module
- \+ *def* dfinsupp.to_semimodule

Modified src/data/finsupp.lean
- \+/\- *def* finsupp.restrict_support_equiv

Modified src/data/holor.lean


Modified src/data/matrix/basic.lean


Modified src/field_theory/finite.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* is_linear_map.is_linear_map_add
- \+/\- *lemma* is_linear_map.is_linear_map_sub
- \+/\- *lemma* linear_equiv.eq_bot_of_equiv
- \+/\- *def* linear_equiv.refl
- \+/\- *lemma* linear_equiv.refl_apply
- \+/\- *lemma* linear_map.finsupp_sum
- \+ *theorem* linear_map.ker_eq_bot_of_injective
- \+/\- *lemma* linear_map.range_range_restrict
- \+/\- *lemma* submodule.mem_span_insert'
- \+/\- *lemma* submodule.sup_eq_range

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/contraction.lean
- \+/\- *def* contract_right

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/dual.lean
- \+/\- *def* module.dual.eval

Modified src/linear_algebra/finsupp.lean
- \+/\- *def* finsupp.supported_equiv_finsupp

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.diagonal_to_lin
- \+/\- *lemma* matrix.to_lin_neg

Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *def* linear_map.flip
- \+/\- *def* linear_map.lcomp
- \+/\- *def* tensor_product.uncurry

Modified src/measure_theory/bochner_integration.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.add_comp
- \+/\- *lemma* continuous_linear_map.comp_add
- \+/\- *lemma* continuous_linear_map.is_complete_ker
- \+/\- *lemma* continuous_linear_map.smul_right_comp
- \+/\- *lemma* continuous_linear_map.smul_right_one_pow

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* continuous_multilinear_map.coe_coe
- \+/\- *def* continuous_multilinear_map.to_multilinear_map_linear

Modified src/topology/basic.lean


Modified src/topology/bounded_continuous_function.lean




## [2020-05-30 15:05:49](https://github.com/leanprover-community/mathlib/commit/cc06d53)
feat(algebra/big_operators): prod_ne_zero ([#2863](https://github.com/leanprover-community/mathlib/pull/2863))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *theorem* finset.prod_ne_zero_iff



## [2020-05-30 13:12:33](https://github.com/leanprover-community/mathlib/commit/b40ac2a)
chore(topology): make topological_space fields protected ([#2867](https://github.com/leanprover-community/mathlib/pull/2867))
This uses the recent `protect_proj` attribute ([#2855](https://github.com/leanprover-community/mathlib/pull/2855)).
#### Estimated changes
Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/opens.lean
- \+/\- *def* topological_space.opens

Modified src/topology/order.lean




## [2020-05-30 07:33:44](https://github.com/leanprover-community/mathlib/commit/62cb7f2)
feat(geometry/euclidean): Euclidean space ([#2852](https://github.com/leanprover-community/mathlib/pull/2852))
Define Euclidean affine spaces (not necessarily finite-dimensional),
and a corresponding instance for the standard Euclidean space `fin n → ℝ`.
This just defines the type class and the instance, with some other
basic geometric definitions and results to be added separately once
this is in.
I haven't attempted to do anything about the `euclidean_space`
definition in geometry/manifold/real_instances.lean that comes with a
comment that it uses the wrong norm.  That might better be refactored
by someone familiar with the manifold code.
By defining Euclidean spaces such that they are defined to be metric
spaces, and providing an instance, this probably implicitly gives item
91 "The Triangle Inequality" from the 100-theorems list, if that's
taken to have a geometric interpretation as in the Coq version, but
it's not very clear how something implicit like that from various
different pieces of the library, and where the item on the list could
be interpreted in several different ways anyway, should be entered in
100.yaml.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* euclidean_space.inner_def
- \+ *def* euclidean_space
- \+/\- *lemma* inner_self_eq_norm_square
- \+/\- *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_nonpos
- \+ *def* pi.inner_product_space
- \+ *def* real.inner_product_space

Added src/geometry/euclidean.lean


Modified src/geometry/manifold/real_instances.lean
- \+/\- *def* euclidean_quadrant
- \+ *def* euclidean_space2
- \- *def* euclidean_space
- \+/\- *lemma* findim_euclidean_space



## [2020-05-30 06:12:38](https://github.com/leanprover-community/mathlib/commit/74d446d)
feat(order/iterate): some inequalities on `f^[n] x` and `g^[n] x` ([#2859](https://github.com/leanprover-community/mathlib/pull/2859))
#### Estimated changes
Added src/order/iterate.lean
- \+ *lemma* function.commute.iterate_le_of_map_le
- \+ *lemma* function.commute.iterate_pos_lt_iff_map_lt'
- \+ *lemma* function.commute.iterate_pos_lt_iff_map_lt
- \+ *lemma* function.commute.iterate_pos_lt_of_map_lt'
- \+ *lemma* function.commute.iterate_pos_lt_of_map_lt



## [2020-05-30 04:46:16](https://github.com/leanprover-community/mathlib/commit/aa47bba)
feat(data/equiv): equiv_of_subsingleton_of_subsingleton ([#2856](https://github.com/leanprover-community/mathlib/pull/2856))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv_of_subsingleton_of_subsingleton



## [2020-05-30 00:45:00](https://github.com/leanprover-community/mathlib/commit/5455fe1)
chore(scripts): update nolints.txt ([#2862](https://github.com/leanprover-community/mathlib/pull/2862))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-29 22:20:28](https://github.com/leanprover-community/mathlib/commit/f95e809)
chore(algebra): displace zero_ne_one_class with nonzero and make no_zero_divisors a Prop ([#2847](https://github.com/leanprover-community/mathlib/pull/2847))
- `[nonzero_semiring α]` becomes `[semiring α] [nonzero α]`
- `[nonzero_comm_semiring α]` becomes `[comm_semiring α] [nonzero α]`
- `[nonzero_comm_ring α]` becomes `[comm_ring α] [nonzero α]`
- `no_zero_divisors` is now a `Prop`
- `units.ne_zero` (originally for `domain`) merges into `units.coe_ne_zero` (originally for `nonzero_comm_semiring`)
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *theorem* not_is_unit_zero

Modified src/algebra/char_p.lean
- \+/\- *lemma* char_p.false_of_nonzero_of_char_one
- \+/\- *lemma* char_p.ring_char_ne_one

Modified src/algebra/classical_lie_algebras.lean
- \+/\- *lemma* lie_algebra.special_linear.sl_non_abelian

Modified src/algebra/direct_limit.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/gcd_domain.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/opposites.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* eq_zero_of_mul_self_eq_zero
- \+/\- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *theorem* nonzero.of_ne
- \- *def* nonzero_comm_ring.of_ne
- \- *def* nonzero_comm_semiring.of_ne
- \+/\- *lemma* one_ne_zero
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* succ_ne_self
- \+/\- *lemma* units.coe_ne_zero
- \- *theorem* units.ne_zero
- \+/\- *lemma* zero_ne_one

Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/exponential.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* pequiv.to_matrix_injective

Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.total_degree_X

Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.monic.ne_zero
- \+ *theorem* polynomial.nonzero.of_polynomial_ne
- \- *def* polynomial.nonzero_comm_ring.of_polynomial_ne
- \- *def* polynomial.nonzero_comm_semiring.of_polynomial_ne

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/nnreal.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/subfield.lean


Modified src/init_/data/int/basic.lean


Modified src/init_/data/nat/lemmas.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/lagrange.lean


Modified src/order/filter/filter_product.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/fintype.lean
- \+/\- *lemma* card_units_lt

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* ring_hom.not_one_mem_ker

Modified src/ring_theory/ideals.lean


Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent

Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/prod.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/ordinal.lean


Modified test/lint.lean




## [2020-05-29 20:46:37](https://github.com/leanprover-community/mathlib/commit/b2f643e)
feat(dynamics/fixed_points): define `is_fixed_pt` ([#2857](https://github.com/leanprover-community/mathlib/pull/2857))
Define `function.is_fixed_pt` and prove some basic properties.
#### Estimated changes
Modified src/analysis/calculus/inverse.lean


Added src/dynamics/fixed_points.lean
- \+ *lemma* function.bij_on_fixed_pts_comp
- \+ *lemma* function.commute.inv_on_fixed_pts_comp
- \+ *lemma* function.commute.left_bij_on_fixed_pts_comp
- \+ *lemma* function.commute.right_bij_on_fixed_pts_comp
- \+ *def* function.fixed_points
- \+ *lemma* function.inv_on_fixed_pts_comp
- \+ *lemma* function.is_fixed_pt.left_of_comp
- \+ *lemma* function.is_fixed_pt.to_left_inverse
- \+ *def* function.is_fixed_pt
- \+ *lemma* function.is_fixed_pt_id
- \+ *lemma* function.maps_to_fixed_pts_comp
- \+ *lemma* function.mem_fixed_points
- \+ *lemma* function.semiconj.maps_to_fixed_pts

Modified src/logic/function/iterate.lean
- \+ *lemma* function.commute.comp_iterate
- \+ *lemma* function.commute.iterate_iterate_self
- \+ *lemma* function.commute.iterate_self
- \+ *lemma* function.commute.self_iterate
- \+ *theorem* function.comp_iterate_pred_of_pos
- \+ *theorem* function.iterate_pred_comp_of_pos

Modified src/order/fixed_points.lean
- \- *def* fixed_points

Modified src/topology/metric_space/contracting.lean
- \+/\- *lemma* contracting_with.dist_le_of_fixed_point
- \- *lemma* contracting_with.efixed_point_is_fixed'
- \- *lemma* contracting_with.efixed_point_is_fixed
- \+ *lemma* contracting_with.efixed_point_is_fixed_pt'
- \+ *lemma* contracting_with.efixed_point_is_fixed_pt
- \- *lemma* contracting_with.fixed_point_is_fixed
- \+ *lemma* contracting_with.fixed_point_is_fixed_pt
- \+/\- *theorem* contracting_with.fixed_point_unique'
- \+/\- *lemma* contracting_with.fixed_point_unique
- \- *lemma* fixed_point_of_tendsto_iterate
- \+ *lemma* is_fixed_pt_of_tendsto_iterate



## [2020-05-29 16:24:04](https://github.com/leanprover-community/mathlib/commit/836184a)
feat(tactic/protect_proj): protect_proj attribute for structures ([#2855](https://github.com/leanprover-community/mathlib/pull/2855))
This attribute protect the projections of a structure that is being defined. 
There were some errors in Euclidean domain caused by `rw` using `euclidean_domain.mul_assoc` instead of `mul_assoc` because the `euclidean_domain` namespace was open. This fixes this problem, and makes the `group` and `ring` etc. namespaces more usable.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/gcd_domain.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring.lean


Modified src/group_theory/subgroup.lean


Modified src/tactic/core.lean


Added src/tactic/protected.lean


Added test/protec_proj.lean




## [2020-05-29 16:24:02](https://github.com/leanprover-community/mathlib/commit/77674a0)
chore(category_theory): T50000 challenge ([#2840](https://github.com/leanprover-community/mathlib/pull/2840))
A lame effort at making something compile with `-T50000`. No actual speed improvement, just split up a definition into pieces.
#### Estimated changes
Modified src/category_theory/limits/over.lean
- \+ *def* category_theory.over.construct_products.cones_equiv_counit_iso
- \+ *def* category_theory.over.construct_products.cones_equiv_inverse_obj
- \+ *def* category_theory.over.construct_products.cones_equiv_unit_iso

Modified src/category_theory/limits/shapes/binary_products.lean




## [2020-05-29 16:24:00](https://github.com/leanprover-community/mathlib/commit/07cdafe)
feat(tactic/with_local_reducibility): alter reducibility attributes locally ([#2820](https://github.com/leanprover-community/mathlib/pull/2820))
#### Estimated changes
Modified src/tactic/core.lean


Added src/tactic/with_local_reducibility.lean
- \+ *def* tactic.decl_reducibility.to_attribute

Added test/with_local_reducibility.lean
- \+ *def* test.wlr_irred
- \+ *def* test.wlr_red
- \+ *def* test.wlr_semired



## [2020-05-29 14:48:35](https://github.com/leanprover-community/mathlib/commit/4a5799e)
feat(data/equiv/basic): subtype_prod_equiv_prod ([#2717](https://github.com/leanprover-community/mathlib/pull/2717))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_prod_equiv_prod



## [2020-05-29 06:50:56](https://github.com/leanprover-community/mathlib/commit/b013b2d)
feat(ring_theory): define subsemirings ([#2837](https://github.com/leanprover-community/mathlib/pull/2837))
~~Depends on [#2836](https://github.com/leanprover-community/mathlib/pull/2836),~~ needs a better module docstring.
Some lemmas are missing, most notably `(subsemiring.closure s : set R) = add_submonoid.closure (submonoid.closure s)`.
#### Estimated changes
Modified src/group_theory/congruence.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/submonoid.lean
- \- *lemma* monoid_hom.closure_preimage_le
- \+ *def* monoid_hom.cod_mrestrict
- \- *def* monoid_hom.cod_restrict
- \+ *lemma* monoid_hom.coe_mrange_restrict
- \- *lemma* monoid_hom.coe_range_restrict
- \+ *lemma* monoid_hom.mclosure_preimage_le
- \+ *def* monoid_hom.mrange_restrict
- \+ *def* monoid_hom.mrestrict
- \+ *lemma* monoid_hom.mrestrict_apply
- \- *def* monoid_hom.range_restrict
- \- *def* monoid_hom.restrict
- \- *lemma* monoid_hom.restrict_apply
- \- *lemma* monoid_hom.restrict_eq
- \+ *lemma* submonoid.coe_Sup_of_directed_on
- \+ *lemma* submonoid.coe_supr_of_directed

Modified src/ring_theory/localization.lean


Added src/ring_theory/subsemiring.lean
- \+ *def* ring_equiv.subsemiring_congr
- \+ *def* ring_hom.cod_srestrict
- \+ *lemma* ring_hom.coe_srange
- \+ *lemma* ring_hom.coe_srange_restrict
- \+ *lemma* ring_hom.eq_of_eq_on_sdense
- \+ *lemma* ring_hom.eq_of_eq_on_stop
- \+ *lemma* ring_hom.eq_on_sclosure
- \+ *def* ring_hom.eq_slocus
- \+ *lemma* ring_hom.map_sclosure
- \+ *lemma* ring_hom.map_srange
- \+ *lemma* ring_hom.mem_srange
- \+ *lemma* ring_hom.sclosure_preimage_le
- \+ *def* ring_hom.srange
- \+ *def* ring_hom.srange_restrict
- \+ *lemma* ring_hom.srange_top_iff_surjective
- \+ *lemma* ring_hom.srange_top_of_surjective
- \+ *def* ring_hom.srestrict
- \+ *lemma* ring_hom.srestrict_apply
- \+ *lemma* subsemiring.Inf_to_add_submonoid
- \+ *lemma* subsemiring.Inf_to_submonoid
- \+ *theorem* subsemiring.add_mem
- \+ *def* subsemiring.closure
- \+ *lemma* subsemiring.closure_Union
- \+ *lemma* subsemiring.closure_empty
- \+ *lemma* subsemiring.closure_eq
- \+ *lemma* subsemiring.closure_eq_of_le
- \+ *lemma* subsemiring.closure_induction
- \+ *lemma* subsemiring.closure_le
- \+ *lemma* subsemiring.closure_mono
- \+ *lemma* subsemiring.closure_sUnion
- \+ *lemma* subsemiring.closure_union
- \+ *lemma* subsemiring.closure_univ
- \+ *lemma* subsemiring.coe_Inf
- \+ *lemma* subsemiring.coe_Sup_of_directed_on
- \+ *lemma* subsemiring.coe_bot
- \+ *lemma* subsemiring.coe_coe
- \+ *lemma* subsemiring.coe_comap
- \+ *lemma* subsemiring.coe_inf
- \+ *lemma* subsemiring.coe_map
- \+ *lemma* subsemiring.coe_mk'
- \+ *lemma* subsemiring.coe_mul
- \+ *lemma* subsemiring.coe_nat_mem
- \+ *lemma* subsemiring.coe_one
- \+ *lemma* subsemiring.coe_prod
- \+ *lemma* subsemiring.coe_ssubset_coe
- \+ *lemma* subsemiring.coe_subset_coe
- \+ *theorem* subsemiring.coe_subtype
- \+ *lemma* subsemiring.coe_supr_of_directed
- \+ *lemma* subsemiring.coe_to_add_submonoid
- \+ *lemma* subsemiring.coe_to_submonoid
- \+ *lemma* subsemiring.coe_top
- \+ *def* subsemiring.comap
- \+ *lemma* subsemiring.comap_comap
- \+ *lemma* subsemiring.comap_inf
- \+ *lemma* subsemiring.comap_infi
- \+ *lemma* subsemiring.comap_top
- \+ *theorem* subsemiring.ext'
- \+ *theorem* subsemiring.ext
- \+ *lemma* subsemiring.gc_map_comap
- \+ *def* subsemiring.inclusion
- \+ *lemma* subsemiring.le_def
- \+ *lemma* subsemiring.list_prod_mem
- \+ *lemma* subsemiring.list_sum_mem
- \+ *def* subsemiring.map
- \+ *lemma* subsemiring.map_bot
- \+ *lemma* subsemiring.map_le_iff_le_comap
- \+ *lemma* subsemiring.map_map
- \+ *lemma* subsemiring.map_sup
- \+ *lemma* subsemiring.map_supr
- \+ *lemma* subsemiring.mem_Inf
- \+ *lemma* subsemiring.mem_Sup_of_directed_on
- \+ *lemma* subsemiring.mem_bot
- \+ *lemma* subsemiring.mem_closure
- \+ *lemma* subsemiring.mem_coe
- \+ *lemma* subsemiring.mem_comap
- \+ *lemma* subsemiring.mem_inf
- \+ *lemma* subsemiring.mem_map
- \+ *lemma* subsemiring.mem_mk'
- \+ *lemma* subsemiring.mem_prod
- \+ *lemma* subsemiring.mem_supr_of_directed
- \+ *lemma* subsemiring.mem_to_add_submonoid
- \+ *lemma* subsemiring.mem_to_submonoid
- \+ *lemma* subsemiring.mem_top
- \+ *lemma* subsemiring.mk'_to_add_submonoid
- \+ *lemma* subsemiring.mk'_to_submonoid
- \+ *theorem* subsemiring.mul_mem
- \+ *lemma* subsemiring.multiset_prod_mem
- \+ *lemma* subsemiring.multiset_sum_mem
- \+ *theorem* subsemiring.one_mem
- \+ *lemma* subsemiring.pow_mem
- \+ *def* subsemiring.prod
- \+ *lemma* subsemiring.prod_bot_sup_bot_prod
- \+ *def* subsemiring.prod_equiv
- \+ *lemma* subsemiring.prod_mem
- \+ *lemma* subsemiring.prod_mono
- \+ *lemma* subsemiring.prod_mono_left
- \+ *lemma* subsemiring.prod_mono_right
- \+ *lemma* subsemiring.prod_top
- \+ *lemma* subsemiring.range_fst
- \+ *lemma* subsemiring.range_snd
- \+ *lemma* subsemiring.smul_mem
- \+ *lemma* subsemiring.srange_subtype
- \+ *lemma* subsemiring.subset_closure
- \+ *def* subsemiring.subtype
- \+ *lemma* subsemiring.sum_mem
- \+ *lemma* subsemiring.top_prod
- \+ *lemma* subsemiring.top_prod_top
- \+ *theorem* subsemiring.zero_mem



## [2020-05-29 05:57:08](https://github.com/leanprover-community/mathlib/commit/6c046c7)
chore(data/setoid): split into `basic` and `partition` ([#2853](https://github.com/leanprover-community/mathlib/pull/2853))
The `basic` part has slightly fewer dependencies and `partition` part
is never used in `mathlib`.
#### Estimated changes
Renamed src/data/setoid.lean to src/data/setoid/basic.lean
- \- *def* setoid.classes
- \- *lemma* setoid.classes_eqv_classes
- \- *lemma* setoid.classes_inj
- \- *theorem* setoid.classes_mk_classes
- \+/\- *def* setoid.correspondence
- \- *lemma* setoid.empty_not_mem_classes
- \- *lemma* setoid.eq_eqv_class_of_mem
- \- *lemma* setoid.eq_iff_classes_eq
- \- *lemma* setoid.eq_of_mem_classes
- \- *lemma* setoid.eq_of_mem_eqv_class
- \- *lemma* setoid.eqv_class_mem
- \- *lemma* setoid.eqv_classes_disjoint
- \- *lemma* setoid.eqv_classes_of_disjoint_union
- \- *lemma* setoid.exists_of_mem_partition
- \- *def* setoid.is_partition
- \- *lemma* setoid.ker_apply_eq_preimage
- \+ *lemma* setoid.ker_def
- \+ *lemma* setoid.ker_iff_mem_preimage
- \+ *def* setoid.lift_equiv
- \- *lemma* setoid.mem_classes
- \- *def* setoid.mk_classes
- \- *theorem* setoid.mk_classes_classes
- \- *lemma* setoid.nonempty_of_mem_partition
- \- *def* setoid.partition.order_iso
- \- *lemma* setoid.rel_iff_exists_classes
- \- *def* setoid.setoid_of_disjoint_union

Added src/data/setoid/partition.lean
- \+ *def* setoid.classes
- \+ *lemma* setoid.classes_eqv_classes
- \+ *lemma* setoid.classes_inj
- \+ *theorem* setoid.classes_mk_classes
- \+ *lemma* setoid.empty_not_mem_classes
- \+ *lemma* setoid.eq_eqv_class_of_mem
- \+ *lemma* setoid.eq_iff_classes_eq
- \+ *lemma* setoid.eq_of_mem_classes
- \+ *lemma* setoid.eq_of_mem_eqv_class
- \+ *lemma* setoid.eqv_class_mem
- \+ *lemma* setoid.eqv_classes_disjoint
- \+ *lemma* setoid.eqv_classes_of_disjoint_union
- \+ *lemma* setoid.exists_of_mem_partition
- \+ *def* setoid.is_partition
- \+ *lemma* setoid.mem_classes
- \+ *def* setoid.mk_classes
- \+ *theorem* setoid.mk_classes_classes
- \+ *lemma* setoid.nonempty_of_mem_partition
- \+ *def* setoid.partition.order_iso
- \+ *lemma* setoid.rel_iff_exists_classes
- \+ *def* setoid.setoid_of_disjoint_union

Modified src/group_theory/congruence.lean


Modified src/topology/metric_space/contracting.lean




## [2020-05-28 23:10:08](https://github.com/leanprover-community/mathlib/commit/543ae52)
feat(analysis/normed_space/add_torsor): normed_add_torsor ([#2814](https://github.com/leanprover-community/mathlib/pull/2814))
Define the metric space structure on torsors of additive normed group
actions.  The motivating case is Euclidean affine spaces.
See
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations
for the discussion leading to this particular handling of the
distance.
Note: I'm not sure what the right way is to address the
dangerous_instance linter error "The following arguments become
metavariables. argument 1: (V : Type u_1)".
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_eq_add
- \+ *lemma* vsub_eq_sub

Added src/analysis/normed_space/add_torsor.lean
- \+ *lemma* add_torsor.dist_eq_norm
- \+ *def* metric_space_of_normed_group_of_add_torsor

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_eq_zero



## [2020-05-28 13:26:09](https://github.com/leanprover-community/mathlib/commit/e9ba32d)
chore(scripts): update nolints.txt ([#2849](https://github.com/leanprover-community/mathlib/pull/2849))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-28 11:54:54](https://github.com/leanprover-community/mathlib/commit/ca95726)
feat(algebra/free) additive versions, docs. ([#2755](https://github.com/leanprover-community/mathlib/pull/2755))
https://github.com/leanprover-community/mathlib/issues/930
#### Estimated changes
Modified src/algebra/free.lean
- \+ *def* free_add_magma.length
- \+ *def* free_add_magma.lift
- \+ *def* free_add_magma.map
- \+ *def* free_add_semigroup.lift'
- \+/\- *def* free_magma.length
- \+/\- *def* free_magma.lift
- \+/\- *lemma* free_magma.lift_mul
- \+/\- *lemma* free_magma.lift_of
- \+/\- *def* free_magma.map
- \+/\- *lemma* free_magma.map_mul'
- \+/\- *lemma* free_magma.map_mul
- \+/\- *lemma* free_magma.map_of
- \+/\- *lemma* free_magma.map_pure
- \+/\- *lemma* free_magma.mul_bind
- \+ *theorem* free_magma.mul_eq
- \+/\- *lemma* free_magma.mul_map_seq
- \+/\- *lemma* free_magma.mul_seq
- \+/\- *lemma* free_magma.pure_bind
- \+/\- *lemma* free_magma.pure_seq
- \+ *def* free_magma.rec_on'
- \- *def* free_magma.repr'
- \+/\- *lemma* free_magma.traverse_eq
- \+/\- *lemma* free_magma.traverse_mul'
- \+/\- *lemma* free_magma.traverse_mul
- \+/\- *lemma* free_magma.traverse_pure'
- \+/\- *lemma* free_magma.traverse_pure
- \+/\- *def* free_semigroup.lift'
- \+/\- *lemma* free_semigroup.lift_mul
- \+/\- *lemma* free_semigroup.lift_of
- \+/\- *lemma* free_semigroup.lift_of_mul
- \+/\- *lemma* free_semigroup.map_mul'
- \+/\- *lemma* free_semigroup.map_mul
- \+/\- *lemma* free_semigroup.map_of
- \+/\- *lemma* free_semigroup.map_pure
- \+/\- *lemma* free_semigroup.mul_bind
- \+/\- *lemma* free_semigroup.mul_map_seq
- \+/\- *lemma* free_semigroup.mul_seq
- \+/\- *lemma* free_semigroup.pure_bind
- \+/\- *lemma* free_semigroup.pure_seq
- \+ *def* free_semigroup.rec_on'
- \- *def* free_semigroup.traverse'
- \+/\- *lemma* free_semigroup.traverse_eq
- \+/\- *lemma* free_semigroup.traverse_mul'
- \+/\- *lemma* free_semigroup.traverse_mul
- \+/\- *lemma* free_semigroup.traverse_pure'
- \+/\- *lemma* free_semigroup.traverse_pure
- \+/\- *lemma* free_semigroup_free_magma_mul
- \+/\- *lemma* magma.free_semigroup.lift_mul
- \+/\- *lemma* magma.free_semigroup.lift_of
- \+/\- *lemma* magma.free_semigroup.map_mul
- \+/\- *lemma* magma.free_semigroup.map_of
- \+/\- *theorem* magma.free_semigroup.of_mul_assoc



## [2020-05-28 08:37:23](https://github.com/leanprover-community/mathlib/commit/cbf4740)
refactor(data/equiv/local_equiv): use dot notation for `eq_on_source` ([#2830](https://github.com/leanprover-community/mathlib/pull/2830))
Also reuse more lemmas from `data/set/function`.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \- *lemma* local_equiv.apply_eq_of_eq_on_source
- \+ *lemma* local_equiv.eq_on_source.eq_on
- \+ *lemma* local_equiv.eq_on_source.restr
- \+ *lemma* local_equiv.eq_on_source.source_eq
- \+ *lemma* local_equiv.eq_on_source.source_inter_preimage_eq
- \+ *lemma* local_equiv.eq_on_source.symm'
- \+ *lemma* local_equiv.eq_on_source.symm_eq_on
- \+ *lemma* local_equiv.eq_on_source.target_eq
- \+ *lemma* local_equiv.eq_on_source.trans'
- \- *lemma* local_equiv.eq_on_source_preimage
- \- *lemma* local_equiv.eq_on_source_restr
- \- *lemma* local_equiv.eq_on_source_symm
- \- *lemma* local_equiv.eq_on_source_trans
- \- *lemma* local_equiv.inv_apply_eq_of_eq_on_source
- \- *lemma* local_equiv.source_eq_of_eq_on_source
- \+ *lemma* local_equiv.symm_maps_to
- \- *lemma* local_equiv.target_eq_of_eq_on_source

Modified src/data/set/function.lean
- \- *theorem* set.eq_on_of_left_inv_of_right_inv
- \+ *theorem* set.eq_on_of_left_inv_on_of_right_inv_on

Modified src/geometry/manifold/manifold.lean


Modified src/topology/local_homeomorph.lean
- \- *lemma* local_homeomorph.apply_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.eq_on_source.eq_on
- \+ *lemma* local_homeomorph.eq_on_source.restr
- \+ *lemma* local_homeomorph.eq_on_source.source_eq
- \+ *lemma* local_homeomorph.eq_on_source.symm'
- \+ *lemma* local_homeomorph.eq_on_source.symm_eq_on_target
- \+ *lemma* local_homeomorph.eq_on_source.target_eq
- \+ *lemma* local_homeomorph.eq_on_source.trans'
- \- *lemma* local_homeomorph.eq_on_source_restr
- \- *lemma* local_homeomorph.eq_on_source_symm
- \- *lemma* local_homeomorph.eq_on_source_trans
- \- *lemma* local_homeomorph.inv_apply_eq_of_eq_on_source
- \- *lemma* local_homeomorph.source_eq_of_eq_on_source
- \- *lemma* local_homeomorph.target_eq_of_eq_on_source

Modified src/topology/topological_fiber_bundle.lean




## [2020-05-28 08:37:21](https://github.com/leanprover-community/mathlib/commit/28dc2ed)
fix(tactic/suggest): normalize synonyms uniformly in goal and lemma ([#2829](https://github.com/leanprover-community/mathlib/pull/2829))
This change is intended to make `library_search` and `suggest` a bit more robust in unfolding the types of the goal and lemma in order to determine which lemmas it will try to apply.
Before, there were two ad-hoc systems to map a head symbol to the name(s) that it should match, now there is only one ad-hoc function that does so.  As a consequence, `library_search` should be able to use a lemma with return type `a > b` to close the goal `b < a`, and use `lemma foo : p → false` to close the goal `¬ p`.
(The `>` normalization shouldn't "really" be needed if we all strictly followed the `gt_or_ge` linter but we don't and the failure has already caused confusion.)
[Discussion on Zulip starts here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198746479)
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean
- \+ *lemma* test.library_search.lemma_with_false_in_head
- \+ *lemma* test.library_search.lemma_with_gt_in_head



## [2020-05-28 07:50:25](https://github.com/leanprover-community/mathlib/commit/005763e)
feat(linear_algebra/lagrange): Lagrange interpolation ([#2764](https://github.com/leanprover-community/mathlib/pull/2764))
Fixes [#2600](https://github.com/leanprover-community/mathlib/pull/2600).
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_sub_le

Added src/linear_algebra/lagrange.lean
- \+ *def* lagrange.basis
- \+ *theorem* lagrange.basis_empty
- \+ *theorem* lagrange.degree_interpolate_lt
- \+ *theorem* lagrange.eq_interpolate
- \+ *theorem* lagrange.eq_of_eval_eq
- \+ *theorem* lagrange.eq_zero_of_eval_eq_zero
- \+ *theorem* lagrange.eval_basis
- \+ *theorem* lagrange.eval_basis_ne
- \+ *theorem* lagrange.eval_basis_self
- \+ *theorem* lagrange.eval_interpolate
- \+ *def* lagrange.fun_equiv_degree_lt
- \+ *def* lagrange.interpolate
- \+ *lemma* lagrange.interpolate_add
- \+ *theorem* lagrange.interpolate_empty
- \+ *lemma* lagrange.interpolate_neg
- \+ *lemma* lagrange.interpolate_smul
- \+ *lemma* lagrange.interpolate_sub
- \+ *lemma* lagrange.interpolate_zero
- \+ *def* lagrange.linterpolate
- \+ *theorem* lagrange.nat_degree_basis

Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* polynomial.degree_le_mono
- \+ *def* polynomial.degree_lt
- \+ *theorem* polynomial.degree_lt_eq_span_X_pow
- \+ *theorem* polynomial.degree_lt_mono
- \+ *theorem* polynomial.mem_degree_lt



## [2020-05-28 07:50:22](https://github.com/leanprover-community/mathlib/commit/fa371f7)
feat(linear_algebra/bilinear_form): introduce adjoints of linear maps ([#2746](https://github.com/leanprover-community/mathlib/pull/2746))
We also use this to define the Lie algebra structure on skew-adjoint
endomorphisms / matrices. The motivation is to enable us to define the
classical Lie algebras.
#### Estimated changes
Modified src/algebra/classical_lie_algebras.lean


Modified src/algebra/lie_algebra.lean
- \+ *lemma* bilin_form.is_skew_adjoint_bracket
- \+ *def* bilin_form.skew_adjoint_lie_subalgebra
- \+ *def* bilin_form.skew_adjoint_matrices_lie_embedding
- \+ *def* bilin_form.skew_adjoint_matrices_lie_subalgebra
- \+ *def* lie_algebra.morphism.range
- \+ *def* lie_equiv_matrix'
- \+ *def* lie_subalgebra.incl
- \+/\- *def* matrix.lie_algebra
- \+/\- *def* matrix.lie_ring

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.is_adjoint_pair.add
- \+ *lemma* bilin_form.is_adjoint_pair.comp
- \+ *lemma* bilin_form.is_adjoint_pair.eq
- \+ *lemma* bilin_form.is_adjoint_pair.mul
- \+ *lemma* bilin_form.is_adjoint_pair.smul
- \+ *lemma* bilin_form.is_adjoint_pair.sub
- \+ *def* bilin_form.is_adjoint_pair
- \+ *lemma* bilin_form.is_adjoint_pair_id
- \+ *lemma* bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right
- \+ *lemma* bilin_form.is_adjoint_pair_zero
- \+ *def* bilin_form.is_pair_self_adjoint
- \+ *def* bilin_form.is_pair_self_adjoint_submodule
- \+ *def* bilin_form.is_self_adjoint
- \+ *def* bilin_form.is_skew_adjoint
- \+ *lemma* bilin_form.is_skew_adjoint_iff_neg_self_adjoint
- \+ *lemma* bilin_form.mem_self_adjoint_submodule
- \+ *lemma* bilin_form.mem_skew_adjoint_submodule
- \+ *lemma* bilin_form.neg_apply
- \+ *def* bilin_form.self_adjoint_submodule
- \+ *def* bilin_form.skew_adjoint_submodule
- \+ *def* matrix.is_adjoint_pair
- \+ *def* matrix.is_self_adjoint
- \+ *def* matrix.is_skew_adjoint
- \+ *lemma* matrix_is_adjoint_pair_bilin_form
- \+ *lemma* mem_pair_self_adjoint_matrices_submodule
- \+ *def* pair_self_adjoint_matrices_linear_embedding
- \+ *lemma* pair_self_adjoint_matrices_linear_embedding_apply
- \+ *lemma* pair_self_adjoint_matrices_linear_embedding_injective
- \+ *def* pair_self_adjoint_matrices_submodule
- \+ *def* self_adjoint_matrices_submodule
- \+ *def* skew_adjoint_matrices_submodule
- \+ *lemma* to_bilin_form_to_matrix
- \+ *lemma* to_matrix_to_bilin_form

Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.comp_to_matrix_mul
- \+ *lemma* matrix.to_lin_neg



## [2020-05-28 07:02:07](https://github.com/leanprover-community/mathlib/commit/315ba3e)
feat(category_theory): show an epi regular mono is an iso ([#2781](https://github.com/leanprover-community/mathlib/pull/2781))
a really minor proof to show that a regular mono which is epi is an iso
#### Estimated changes
Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* category_theory.is_iso_of_regular_epi_of_mono
- \+ *def* category_theory.is_iso_of_regular_mono_of_epi



## [2020-05-27 21:30:17](https://github.com/leanprover-community/mathlib/commit/efb4e95)
refactor(*iterate*): move to `function`; renamings ([#2832](https://github.com/leanprover-community/mathlib/pull/2832))
* move lemmas about `iterate` from `data.nat.basic` to `logic.function.iterate`;
* move lemmas like `nat.iterate_succ` to `function` namespace;
* rename some lemmas:
  - `iterate₀` to `iterate_fixed`,
  - `iterate₁` to `semiconj.iterate_right`, see also `commute.iterate_left` and `commute.iterate_right`;
  - `iterate₂` to `semiconj₂.iterate`;
  - `iterate_cancel` to `left_inverse.iterate` and `right_inverse.iterate`;
* move lemmas `*_hom.iterate_map_*` to `algebra/iterate_hom`.
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/algebra/group_power.lean
- \- *theorem* add_monoid_hom.iterate_map_smul
- \- *theorem* monoid_hom.iterate_map_pow
- \- *lemma* ring_hom.coe_pow
- \- *lemma* ring_hom.iterate_map_pow
- \- *lemma* ring_hom.iterate_map_smul

Added src/algebra/iterate_hom.lean
- \+ *theorem* add_monoid_hom.iterate_map_gsmul
- \+ *theorem* add_monoid_hom.iterate_map_smul
- \+ *theorem* add_monoid_hom.iterate_map_sub
- \+ *theorem* monoid_hom.iterate_map_gpow
- \+ *theorem* monoid_hom.iterate_map_inv
- \+ *theorem* monoid_hom.iterate_map_mul
- \+ *theorem* monoid_hom.iterate_map_one
- \+ *theorem* monoid_hom.iterate_map_pow
- \+ *lemma* ring_hom.coe_pow
- \+ *theorem* ring_hom.iterate_map_add
- \+ *theorem* ring_hom.iterate_map_gsmul
- \+ *theorem* ring_hom.iterate_map_mul
- \+ *theorem* ring_hom.iterate_map_neg
- \+ *theorem* ring_hom.iterate_map_one
- \+ *theorem* ring_hom.iterate_map_pow
- \+ *theorem* ring_hom.iterate_map_smul
- \+ *theorem* ring_hom.iterate_map_sub
- \+ *theorem* ring_hom.iterate_map_zero

Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/iterated_deriv.lean
- \+/\- *lemma* iterated_deriv_eq_iterate

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/nat/basic.lean
- \- *theorem* function.bijective.iterate
- \- *theorem* function.injective.iterate
- \- *theorem* function.surjective.iterate
- \- *theorem* monoid_hom.iterate_map_inv
- \- *theorem* monoid_hom.iterate_map_mul
- \- *theorem* monoid_hom.iterate_map_one
- \- *theorem* monoid_hom.iterate_map_sub
- \- *theorem* nat.iterate_add
- \- *theorem* nat.iterate_add_apply
- \- *theorem* nat.iterate_cancel
- \- *theorem* nat.iterate_ind
- \- *lemma* nat.iterate_mul
- \- *theorem* nat.iterate_one
- \- *theorem* nat.iterate_succ'
- \- *theorem* nat.iterate_succ
- \- *theorem* nat.iterate_succ_apply'
- \- *theorem* nat.iterate_succ_apply
- \- *theorem* nat.iterate_zero
- \- *theorem* nat.iterate_zero_apply
- \- *theorem* nat.iterate₀
- \- *theorem* nat.iterate₁
- \- *theorem* nat.iterate₂
- \- *theorem* ring_hom.iterate_map_add
- \- *theorem* ring_hom.iterate_map_mul
- \- *theorem* ring_hom.iterate_map_neg
- \- *theorem* ring_hom.iterate_map_one
- \- *theorem* ring_hom.iterate_map_sub
- \- *theorem* ring_hom.iterate_map_zero

Modified src/field_theory/perfect_closure.lean
- \+ *theorem* left_inverse_pth_root_frobenius

Added src/logic/function/iterate.lean
- \+ *theorem* function.bijective.iterate
- \+ *lemma* function.commute.iterate_eq_of_map_eq
- \+ *lemma* function.commute.iterate_iterate
- \+ *lemma* function.commute.iterate_left
- \+ *lemma* function.commute.iterate_right
- \+ *theorem* function.injective.iterate
- \+ *theorem* function.iterate_add
- \+ *theorem* function.iterate_add_apply
- \+ *theorem* function.iterate_fixed
- \+ *theorem* function.iterate_id
- \+ *lemma* function.iterate_mul
- \+ *theorem* function.iterate_one
- \+ *theorem* function.iterate_succ'
- \+ *theorem* function.iterate_succ
- \+ *theorem* function.iterate_succ_apply'
- \+ *theorem* function.iterate_succ_apply
- \+ *theorem* function.iterate_zero
- \+ *theorem* function.iterate_zero_apply
- \+ *theorem* function.left_inverse.iterate
- \+ *theorem* function.right_inverse.iterate
- \+ *lemma* function.semiconj.iterate_left
- \+ *lemma* function.semiconj.iterate_right
- \+ *lemma* function.semiconj₂.iterate
- \+ *theorem* function.surjective.iterate

Modified src/order/order_iso.lean


Modified src/set_theory/ordinal.lean
- \+/\- *theorem* initial_seg.eq_or_principal
- \+/\- *theorem* ordinal.lift_lift
- \+/\- *theorem* principal_seg.cod_restrict_apply
- \+/\- *theorem* principal_seg.cod_restrict_top
- \+/\- *theorem* principal_seg.init_iff
- \+/\- *theorem* principal_seg.trans_apply
- \+/\- *theorem* principal_seg.trans_top

Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/lipschitz.lean




## [2020-05-27 18:57:00](https://github.com/leanprover-community/mathlib/commit/1988364)
feat(src/ring_theory): in a PID, all fractional ideals are invertible ([#2826](https://github.com/leanprover-community/mathlib/pull/2826))
This would show that all PIDs are Dedekind domains, once we have a definition of Dedekind domain (we could define it right now, but it would depend on the choice of field of fractions).
In `localization.lean`, I added a few small lemmas on localizations (`localization.exists_integer_multiple` and `fraction_map.to_map_eq_zero_iff`). @101damnations, are these additions compatible with your branches? I'm happy to change them if not.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.coe_span_singleton
- \+ *lemma* ring.fractional_ideal.eq_span_singleton_of_principal
- \+ *lemma* ring.fractional_ideal.exists_eq_span_singleton_mul
- \+ *lemma* ring.fractional_ideal.invertible_of_principal
- \+ *lemma* ring.fractional_ideal.mem_coe
- \+ *lemma* ring.fractional_ideal.mem_singleton_mul
- \+ *theorem* ring.fractional_ideal.mul_inv_cancel_iff
- \+ *lemma* ring.fractional_ideal.one_mem_one
- \+ *lemma* ring.fractional_ideal.span_fractional_iff
- \+ *def* ring.fractional_ideal.span_singleton
- \+ *lemma* ring.fractional_ideal.span_singleton_fractional
- \+ *lemma* ring.fractional_ideal.span_singleton_mul_span_singleton
- \+ *lemma* ring.fractional_ideal.span_singleton_one
- \+ *lemma* ring.fractional_ideal.span_singleton_zero
- \+ *lemma* ring.fractional_ideal.val_coe_ideal
- \+ *lemma* ring.fractional_ideal.val_inv_of_nonzero
- \+ *lemma* ring.fractional_ideal.val_one
- \+ *lemma* ring.fractional_ideal.val_span_singleton

Modified src/ring_theory/localization.lean
- \+ *lemma* fraction_map.to_map_eq_zero_iff
- \+ *lemma* localization.exists_integer_multiple'
- \+ *lemma* localization.exists_integer_multiple
- \+ *lemma* localization.lin_coe_apply



## [2020-05-27 13:41:59](https://github.com/leanprover-community/mathlib/commit/c812ebe)
feat(category_theory/abelian): abelian categories ([#2817](https://github.com/leanprover-community/mathlib/pull/2817))
~~Depends on [#2779](https://github.com/leanprover-community/mathlib/pull/2779).~~ Closes [#2178](https://github.com/leanprover-community/mathlib/pull/2178). I will give instances for `AddCommGroup` and `Module`, but since this PR is large already, I'll wait until the next PR with that.
#### Estimated changes
Modified docs/references.bib


Added src/category_theory/abelian/basic.lean
- \+ *def* category_theory.abelian.biproduct_to_pushout_is_cokernel.is_colimit_biproduct_to_pushout
- \+ *def* category_theory.abelian.coimage_strong_epi_mono_factorisation
- \+ *def* category_theory.abelian.epi_is_cokernel_of_kernel
- \+ *lemma* category_theory.abelian.full_image_factorisation
- \+ *def* category_theory.abelian.has_pullbacks
- \+ *def* category_theory.abelian.has_pushouts
- \+ *lemma* category_theory.abelian.image_eq_image
- \+ *def* category_theory.abelian.image_strong_epi_mono_factorisation
- \+ *def* category_theory.abelian.is_iso_of_mono_of_epi
- \+ *def* category_theory.abelian.mono_is_kernel_of_cokernel
- \+ *def* category_theory.abelian.pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct
- \+ *def* category_theory.abelian.strong_epi_of_epi

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* category_theory.limits.biprod.hom_ext'
- \+ *lemma* category_theory.limits.biprod.hom_ext

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cofork.π_eq_app_one
- \+ *lemma* category_theory.limits.fork.ι_eq_app_zero

Modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *def* category_theory.is_iso_of_mono_of_strong_epi
- \- *def* category_theory.mono_strong_epi_is_iso

Modified src/category_theory/preadditive.lean
- \+/\- *lemma* category_theory.preadditive.comp_neg
- \+/\- *lemma* category_theory.preadditive.comp_sub
- \+/\- *lemma* category_theory.preadditive.neg_comp
- \+/\- *lemma* category_theory.preadditive.neg_comp_neg
- \+/\- *lemma* category_theory.preadditive.sub_comp



## [2020-05-27 12:11:16](https://github.com/leanprover-community/mathlib/commit/2deb6b4)
feat(algebra/continued_fractions): add computation definitions and basic translation lemmas ([#2797](https://github.com/leanprover-community/mathlib/pull/2797))
### What
- add definitions of the computation of a continued fraction for a given value (in a given floor field)
- add very basic, mostly technical lemmas to convert between the different structures used by the computation
### Why
- I want to be able to compute the continued fraction of a value. I next will add termination, approximation, and correctness lemmas for the definitions in this commit (I already have them lying around on my PC for ages :cold_sweat: )
- The technical lemmas are needed for the next bunch of commits.
### How
- Follow the straightforward approach as described, for example, on [Wikipedia](https://en.wikipedia.org/wiki/Continued_fraction#Calculating_continued_fraction_representations)
#### Estimated changes
Added src/algebra/continued_fractions/computation/basic.lean
- \+ *lemma* generalized_continued_fraction.int_fract_pair.coe_to_int_fract_pair
- \+ *lemma* generalized_continued_fraction.int_fract_pair.stream_is_seq

Added src/algebra/continued_fractions/computation/default.lean


Added src/algebra/continued_fractions/computation/translations.lean
- \+ *lemma* generalized_continued_fraction.int_fract_pair.nth_seq1_eq_succ_nth_stream
- \+ *lemma* generalized_continued_fraction.int_fract_pair.obtain_succ_nth_stream_of_fr_zero
- \+ *lemma* generalized_continued_fraction.int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some
- \+ *lemma* generalized_continued_fraction.int_fract_pair.seq1_fst_eq_of
- \+ *lemma* generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero
- \+ *lemma* generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff
- \+ *lemma* generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff
- \+ *lemma* generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero
- \+ *lemma* generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream
- \+ *lemma* generalized_continued_fraction.of_h_eq_floor
- \+ *lemma* generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b
- \+ *lemma* generalized_continued_fraction.of_terminated_at_iff_int_fract_pair_seq1_terminated_at
- \+ *lemma* generalized_continued_fraction.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none

Modified src/algebra/continued_fractions/default.lean




## [2020-05-27 12:11:14](https://github.com/leanprover-community/mathlib/commit/798c61b)
feat(data/nat/prime): eq_prime_pow_of_dvd_least_prime_pow ([#2791](https://github.com/leanprover-community/mathlib/pull/2791))
Proves
```lean
lemma eq_prime_pow_of_dvd_least_prime_pow
  (a p k : ℕ) (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) :
  a = p^(k+1)
```
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.pow_dvd_pow_iff_le_right'
- \+ *lemma* nat.pow_dvd_pow_iff_le_right
- \+ *lemma* nat.pow_dvd_pow_iff_pow_le_pow

Modified src/data/nat/prime.lean
- \+ *lemma* nat.eq_prime_pow_of_dvd_least_prime_pow



## [2020-05-27 12:11:12](https://github.com/leanprover-community/mathlib/commit/85f08ec)
feat(CI): add -T100000 to the build step in CI ([#2276](https://github.com/leanprover-community/mathlib/pull/2276))
This PR adds `-T100000` to CI. This is the default timeout setting in the VS Code extension and emacs.
With some exceptions, noted with `FIXME` comments mentioning `-T50000`, the library now compiles with `-T50000`:
- [ ] `has_sum.has_sum_ne_zero` in `src/topology/algebra/infinite_sum.lean`, where I don't really understand why it is slow.
- [ ] `exists_norm_eq_infi_of_complete_convex` in `src/analysis/normed_space/real_inner_product.lean`, which has a giant proof which should be rewritten in several steps.
- [ ] `tangent_bundle_core.coord_change_comp` in `src/geometry/manifold/basic_smooth_bundle.lean`.
- [ ] `change_origin_radius` in `src/analysis/analytic/basic.lean`
There are 3 `def`s related to category theory which also don't compile:
- [ ] `adj₁` in `src/topology/category/Top/adjunctions.lean`
- [x] `cones_equiv_inverse` in `src/category_theory/limits/over.lean` (addressed in [#2840](https://github.com/leanprover-community/mathlib/pull/2840))
- [ ] `prod_functor` in `src/category_theory/limits/shapes/binary_products.lean`
This proof no longer causes problems with `-T50000`, but it should still be broken up at some point.
- [ ] `simple_func_sequence_tendsto` in `src/measure_theory/simple_func_dense.lean`, which has a giant proof which should be rewritten in several steps. ~~This one is really bad, and doesn't even compile with `-T100000`.~~ 
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge).
#### Estimated changes
Modified .github/workflows/build.yml


Modified src/analysis/analytic/basic.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/category/Top/adjunctions.lean




## [2020-05-27 11:24:35](https://github.com/leanprover-community/mathlib/commit/7c5eab3)
chore(scripts): update nolints.txt ([#2841](https://github.com/leanprover-community/mathlib/pull/2841))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-27 08:57:27](https://github.com/leanprover-community/mathlib/commit/a7063ec)
feat(ring_theory/prod): ring homs to/from `R × S` ([#2836](https://github.com/leanprover-community/mathlib/pull/2836))
* move some instances from `algebra/pi_instances`;
* add `prod.comm_semiring`;
* define `ring_hom.fst`, `ring_hom.snd`, `ring_hom.prod`, and
  `ring_hom.prod_map`.
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+/\- *lemma* monoid_hom.coe_prod_map

Modified src/algebra/pi_instances.lean


Added src/ring_theory/prod.lean
- \+ *lemma* ring_hom.coe_fst
- \+ *lemma* ring_hom.coe_prod_map
- \+ *lemma* ring_hom.coe_snd
- \+ *def* ring_hom.fst
- \+ *lemma* ring_hom.fst_comp_prod
- \+ *lemma* ring_hom.prod_apply
- \+ *lemma* ring_hom.prod_comp_prod_map
- \+ *def* ring_hom.prod_map
- \+ *lemma* ring_hom.prod_map_def
- \+ *lemma* ring_hom.prod_unique
- \+ *def* ring_hom.snd
- \+ *lemma* ring_hom.snd_comp_prod



## [2020-05-27 08:57:25](https://github.com/leanprover-community/mathlib/commit/6ee3a47)
chore(data/equiv/basic): simplify some defs, add `coe` lemmas ([#2835](https://github.com/leanprover-community/mathlib/pull/2835))
Use functions like `prod.map`, `curry`, `uncurry`, `sum.elim`, `sum.map` to define equivalences.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.apply_symm_apply
- \+ *lemma* equiv.coe_prod_comm
- \+ *theorem* equiv.coe_prod_congr
- \+ *theorem* equiv.coe_refl
- \+ *theorem* equiv.coe_trans
- \+/\- *def* equiv.empty_prod
- \+/\- *theorem* equiv.of_bijective_to_fun
- \+/\- *def* equiv.pempty_prod
- \+ *theorem* equiv.prod_assoc_sym_apply
- \+/\- *def* equiv.prod_comm
- \- *lemma* equiv.prod_comm_apply
- \+ *lemma* equiv.prod_comm_symm
- \+/\- *def* equiv.prod_congr
- \- *theorem* equiv.prod_congr_apply
- \+ *theorem* equiv.prod_congr_symm
- \+/\- *def* equiv.prod_empty
- \+/\- *def* equiv.prod_pempty
- \+/\- *def* equiv.prod_punit
- \+/\- *def* equiv.psum_equiv_sum
- \+/\- *def* equiv.punit_prod
- \+/\- *theorem* equiv.punit_prod_apply
- \+/\- *theorem* equiv.refl_apply
- \+ *theorem* equiv.self_comp_symm
- \+/\- *def* equiv.sigma_congr
- \+/\- *def* equiv.sigma_congr_left'
- \+ *lemma* equiv.sum_comm_apply
- \- *lemma* equiv.sum_comm_apply_inl
- \- *lemma* equiv.sum_comm_apply_inr
- \+/\- *lemma* equiv.sum_comm_symm
- \+/\- *def* equiv.sum_congr
- \+ *theorem* equiv.sum_congr_apply
- \- *theorem* equiv.sum_congr_apply_inl
- \- *theorem* equiv.sum_congr_apply_inr
- \+/\- *lemma* equiv.sum_congr_symm
- \+/\- *def* equiv.sum_empty
- \+/\- *def* equiv.sum_pempty
- \+/\- *theorem* equiv.symm_apply_apply
- \+ *theorem* equiv.symm_comp_self
- \+/\- *theorem* equiv.trans_apply

Modified src/data/equiv/functor.lean


Modified src/data/polynomial.lean


Modified src/data/sum.lean
- \+ *lemma* sum.map_comp_map
- \+ *lemma* sum.map_id_id
- \+ *lemma* sum.map_inl
- \+ *lemma* sum.map_inr
- \+ *lemma* sum.map_map



## [2020-05-27 08:57:23](https://github.com/leanprover-community/mathlib/commit/2a48225)
feat(computability/tm_to_partrec): partrec functions are TM-computable ([#2792](https://github.com/leanprover-community/mathlib/pull/2792))
A construction of a Turing machine that can evaluate any partial recursive function. This PR contains the bulk of the work but the end to end theorem (which asserts that any `computable` function can be evaluated by a Turing machine) has not yet been stated.
#### Estimated changes
Added src/computability/tm_to_partrec.lean
- \+ *def* turing.partrec_to_TM2.K'.elim
- \+ *theorem* turing.partrec_to_TM2.K'.elim_update_aux
- \+ *theorem* turing.partrec_to_TM2.K'.elim_update_main
- \+ *theorem* turing.partrec_to_TM2.K'.elim_update_rev
- \+ *theorem* turing.partrec_to_TM2.K'.elim_update_stack
- \+ *def* turing.partrec_to_TM2.cfg'
- \+ *theorem* turing.partrec_to_TM2.clear_ok
- \+ *def* turing.partrec_to_TM2.cont_stack
- \+ *theorem* turing.partrec_to_TM2.copy_ok
- \+ *def* turing.partrec_to_TM2.halt
- \+ *def* turing.partrec_to_TM2.head
- \+ *theorem* turing.partrec_to_TM2.head_main_ok
- \+ *theorem* turing.partrec_to_TM2.head_stack_ok
- \+ *def* turing.partrec_to_TM2.init
- \+ *def* turing.partrec_to_TM2.move_excl
- \+ *theorem* turing.partrec_to_TM2.move_ok
- \+ *def* turing.partrec_to_TM2.move₂
- \+ *theorem* turing.partrec_to_TM2.move₂_ok
- \+ *def* turing.partrec_to_TM2.nat_end
- \+ *def* turing.partrec_to_TM2.peek'
- \+ *def* turing.partrec_to_TM2.pop'
- \+ *theorem* turing.partrec_to_TM2.pred_ok
- \+ *def* turing.partrec_to_TM2.push'
- \+ *def* turing.partrec_to_TM2.split_at_pred
- \+ *theorem* turing.partrec_to_TM2.split_at_pred_eq
- \+ *theorem* turing.partrec_to_TM2.split_at_pred_ff
- \+ *def* turing.partrec_to_TM2.stmt'
- \+ *theorem* turing.partrec_to_TM2.succ_ok
- \+ *def* turing.partrec_to_TM2.tr
- \+ *def* turing.partrec_to_TM2.tr_cfg
- \+ *def* turing.partrec_to_TM2.tr_cont
- \+ *def* turing.partrec_to_TM2.tr_cont_stack
- \+ *theorem* turing.partrec_to_TM2.tr_eval
- \+ *theorem* turing.partrec_to_TM2.tr_init
- \+ *def* turing.partrec_to_TM2.tr_list
- \+ *theorem* turing.partrec_to_TM2.tr_list_ne_Cons
- \+ *def* turing.partrec_to_TM2.tr_llist
- \+ *def* turing.partrec_to_TM2.tr_nat
- \+ *theorem* turing.partrec_to_TM2.tr_nat_nat_end
- \+ *theorem* turing.partrec_to_TM2.tr_nat_zero
- \+ *def* turing.partrec_to_TM2.tr_normal
- \+ *theorem* turing.partrec_to_TM2.tr_normal_respects
- \+ *def* turing.partrec_to_TM2.tr_num
- \+ *theorem* turing.partrec_to_TM2.tr_num_nat_end
- \+ *def* turing.partrec_to_TM2.tr_pos_num
- \+ *theorem* turing.partrec_to_TM2.tr_pos_num_nat_end
- \+ *theorem* turing.partrec_to_TM2.tr_respects
- \+ *theorem* turing.partrec_to_TM2.tr_ret_respects
- \+ *def* turing.partrec_to_TM2.unrev
- \+ *theorem* turing.partrec_to_TM2.unrev_ok
- \+ *def* turing.to_partrec.cfg.then
- \+ *def* turing.to_partrec.code.eval
- \+ *theorem* turing.to_partrec.code.exists_code.comp
- \+ *theorem* turing.to_partrec.code.exists_code
- \+ *def* turing.to_partrec.code.head
- \+ *theorem* turing.to_partrec.code.head_eval
- \+ *def* turing.to_partrec.code.id
- \+ *theorem* turing.to_partrec.code.id_eval
- \+ *def* turing.to_partrec.code.nil
- \+ *theorem* turing.to_partrec.code.nil_eval
- \+ *theorem* turing.to_partrec.code.ok.zero
- \+ *def* turing.to_partrec.code.ok
- \+ *def* turing.to_partrec.code.prec
- \+ *def* turing.to_partrec.code.pred
- \+ *theorem* turing.to_partrec.code.pred_eval
- \+ *def* turing.to_partrec.code.rfind
- \+ *def* turing.to_partrec.code.zero
- \+ *theorem* turing.to_partrec.code.zero_eval
- \+ *theorem* turing.to_partrec.code_is_ok
- \+ *def* turing.to_partrec.cont.eval
- \+ *def* turing.to_partrec.cont.then
- \+ *theorem* turing.to_partrec.cont.then_eval
- \+ *theorem* turing.to_partrec.cont_eval_fix
- \+ *def* turing.to_partrec.step
- \+ *theorem* turing.to_partrec.step_normal.is_ret
- \+ *def* turing.to_partrec.step_normal
- \+ *theorem* turing.to_partrec.step_normal_eval
- \+ *theorem* turing.to_partrec.step_normal_then
- \+ *def* turing.to_partrec.step_ret
- \+ *theorem* turing.to_partrec.step_ret_eval
- \+ *theorem* turing.to_partrec.step_ret_then

Modified src/computability/turing_machine.lean
- \+/\- *def* turing.TM2.step
- \+/\- *def* turing.TM2.step_aux
- \+ *def* turing.eval_induction

Modified src/data/list/basic.lean
- \+ *theorem* list.tail_subset
- \+ *theorem* list.tail_suffix

Modified src/data/option/defs.lean


Modified src/data/pfun.lean
- \+ *theorem* roption.pure_eq_some

Modified src/data/vector2.lean
- \+ *theorem* vector.cons_head
- \+ *theorem* vector.cons_tail
- \+ *theorem* vector.cons_val
- \+ *theorem* vector.tail_val

Modified src/logic/function/basic.lean
- \+ *theorem* function.update_comm
- \+ *theorem* function.update_idem

Modified src/logic/relation.lean


Modified src/topology/list.lean
- \- *lemma* vector.cons_val



## [2020-05-27 07:09:31](https://github.com/leanprover-community/mathlib/commit/0d6d0b0)
chore(*): split long lines, unindent in namespaces ([#2834](https://github.com/leanprover-community/mathlib/pull/2834))
The diff is large but here is the word diff (search for `[-` or `[+`):
``` shellsession
$ git diff --word-diff=plain --ignore-all-space master | grep '(^---|\[-|\[\+)'
--- a/src/algebra/big_operators.lean
[-λ l, @is_group_anti_hom.map_prod _ _ _ _ _ inv_is_group_anti_hom l-]-- TODO there is probably a cleaner proof of this
        { have : [-(to_finset s).sum (λx,-]{+∑ x in s.to_finset,+} ite (x = a) 1 [-0)-]{+0+} = [-({a} : finset α).sum (λx,-]{+∑ x in {a},+} ite (x = a) 1 [-0),-]
[-          { apply (finset.sum_subset _ _).symm,-]{+0,+}
          { [-intros _ H, rwa mem_singleton.1 H },-]
[-            { exact λ _ _ H, if_neg (mt finset.mem_singleton.2 H) }-]{+rw [finset.sum_ite_eq', if_pos h, finset.sum_singleton, if_pos rfl],+} },
--- a/src/algebra/category/Group/basic.lean
[-a-]{+an+} `add_equiv` between `add_group`s."]
--- a/src/algebra/category/Group/colimits.lean
--- a/src/algebra/category/Mon/basic.lean
[-a-]{+an+} `add_equiv` between `add_monoid`s."]
[-a-]{+an+} `add_equiv` between `add_comm_monoid`s."]
--- a/src/algebra/free.lean
--- a/src/algebra/group/units.lean
--- a/src/algebra/group/units_hom.lean
--- a/src/category_theory/category/default.lean
[-universes v u-]-- The order in this declaration matters: v often needs to be explicitly specified while u often
--- a/src/control/monad/cont.lean
    simp [-[call_cc,except_t.call_cc,call_cc_bind_right,except_t.goto_mk_label,map_eq_bind_pure_comp,bind_assoc,@call_cc_bind_left-]{+[call_cc,except_t.call_cc,call_cc_bind_right,except_t.goto_mk_label,map_eq_bind_pure_comp,+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,option_t.call_cc,call_cc_bind_right,option_t.goto_mk_label,map_eq_bind_pure_comp,bind_assoc,@call_cc_bind_left-]{+[call_cc,option_t.call_cc,call_cc_bind_right,+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,state_t.call_cc,call_cc_bind_left,(>>=),state_t.bind,state_t.goto_mk_label],-]{+[call_cc,state_t.call_cc,call_cc_bind_left,(>>=),+}
  call_cc_dummy := by { intros, simp [-[call_cc,state_t.call_cc,call_cc_bind_right,(>>=),state_t.bind,@call_cc_dummy-]{+[call_cc,state_t.call_cc,call_cc_bind_right,(>>=),+}
  call_cc_bind_left  := by { intros, simp [-[call_cc,reader_t.call_cc,call_cc_bind_left,reader_t.goto_mk_label],-]{+[call_cc,reader_t.call_cc,call_cc_bind_left,+}
--- a/src/control/monad/writer.lean
--- a/src/control/traversable/basic.lean
   online at <http://arxiv.org/pdf/1202.2919>[-Synopsis-]
--- a/src/data/analysis/filter.lean
--- a/src/data/equiv/basic.lean
--- a/src/data/fin.lean
--- a/src/data/finset.lean
  [-by-]{+{+} rw [-[eq],-]{+[eq] },+}
--- a/src/data/hash_map.lean
--- a/src/data/int/basic.lean
--- a/src/data/list/basic.lean
--- a/src/data/list/tfae.lean
--- a/src/data/num/lemmas.lean
[-Properties of the binary representation of integers.-]
--- a/src/data/zsqrtd/basic.lean
--- a/src/group_theory/congruence.lean
with [-a-]{+an+} addition."]
@[to_additive Sup_eq_add_con_gen "The supremum of a set of additive congruence relations [-S-]{+`S`+} equals
--- a/src/group_theory/monoid_localization.lean
--- a/src/group_theory/submonoid.lean
--- a/src/number_theory/dioph.lean
--- a/src/set_theory/ordinal.lean
--- a/src/tactic/apply.lean
--- a/src/tactic/lean_core_docs.lean
--- a/src/tactic/lint/type_classes.lean
--- a/src/tactic/omega/main.lean
--- a/test/coinductive.lean
--- a/test/localized/import3.lean
--- a/test/norm_num.lean
--- a/test/tidy.lean
--- a/test/where.lean
```
P.S.: I don't know how to make `git diff` hide all non-interesting chunks.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/category/Group/basic.lean
- \+/\- *def* mul_equiv.to_CommGroup_iso

Modified src/algebra/category/Group/colimits.lean
- \+/\- *lemma* AddCommGroup.colimits.quot_add
- \+/\- *lemma* AddCommGroup.colimits.quot_neg

Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/free.lean
- \+/\- *lemma* free_magma.map_mul'
- \+/\- *lemma* free_magma.mul_bind
- \+/\- *lemma* free_magma.mul_map_seq
- \+/\- *lemma* free_magma.mul_seq
- \+/\- *lemma* free_magma.traverse_mul'
- \+/\- *lemma* free_magma.traverse_mul
- \+/\- *lemma* free_semigroup.map_mul'
- \+/\- *lemma* free_semigroup.map_pure
- \+/\- *lemma* free_semigroup.mul_bind
- \+/\- *lemma* free_semigroup.mul_map_seq
- \+/\- *lemma* free_semigroup.mul_seq
- \+/\- *lemma* free_semigroup.pure_seq
- \+/\- *def* free_semigroup.traverse'
- \+/\- *lemma* free_semigroup.traverse_mul'
- \+/\- *lemma* free_semigroup.traverse_mul
- \+/\- *def* free_semigroup_free_magma
- \+/\- *theorem* magma.free_semigroup.of_mul_assoc_left

Modified src/algebra/group/units.lean


Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* units.map_comp

Modified src/category_theory/category/default.lean
- \+/\- *lemma* category_theory.epi_of_epi_fac
- \+/\- *lemma* category_theory.eq_of_comp_left_eq'
- \+/\- *lemma* category_theory.eq_of_comp_right_eq'
- \+/\- *lemma* category_theory.mono_of_mono_fac

Modified src/control/monad/cont.lean
- \+/\- *def* option_t.call_cc
- \+/\- *def* reader_t.call_cc
- \+/\- *def* state_t.call_cc
- \+/\- *def* writer_t.call_cc

Modified src/control/monad/writer.lean


Modified src/control/traversable/basic.lean


Modified src/data/analysis/filter.lean
- \+/\- *theorem* filter.realizer.map_F

Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.Pi_curry
- \+/\- *lemma* equiv.swap_apply_self

Modified src/data/fin.lean
- \+/\- *lemma* fin.succ_above_descend

Modified src/data/finset.lean
- \+/\- *theorem* finset.image_inter
- \+/\- *theorem* finset.image_union

Modified src/data/hash_map.lean
- \+/\- *theorem* hash_map.append_of_modify
- \+/\- *theorem* hash_map.contains_aux_iff
- \+/\- *theorem* hash_map.find_aux_iff
- \+/\- *theorem* hash_map.valid.as_list_nodup
- \+/\- *theorem* hash_map.valid.contains_aux_iff
- \+/\- *theorem* hash_map.valid.find_aux_iff
- \+/\- *def* mk_hash_map

Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_neg_of_nat
- \+/\- *theorem* int.cast_one
- \+/\- *theorem* int.cast_sub_nat_nat

Modified src/data/list/basic.lean
- \+/\- *theorem* list.all_cons
- \+/\- *theorem* list.any_cons
- \+/\- *theorem* list.append_inj'
- \+/\- *theorem* list.append_inj
- \+/\- *theorem* list.append_inj_left'
- \+/\- *theorem* list.append_inj_left
- \+/\- *theorem* list.append_inj_right'
- \+/\- *theorem* list.append_inj_right
- \+/\- *theorem* list.count_erase_of_ne
- \+/\- *theorem* list.count_erase_self
- \+/\- *theorem* list.disjoint_of_disjoint_append_left_left
- \+/\- *theorem* list.disjoint_of_disjoint_append_left_right
- \+/\- *theorem* list.disjoint_of_disjoint_append_right_left
- \+/\- *theorem* list.disjoint_of_disjoint_append_right_right
- \+/\- *theorem* list.disjoint_of_subset_left
- \+/\- *theorem* list.disjoint_of_subset_right
- \+/\- *theorem* list.eq_of_infix_of_length_eq
- \+/\- *theorem* list.eq_of_mem_map_const
- \+/\- *theorem* list.eq_of_prefix_of_length_eq
- \+/\- *theorem* list.eq_of_sublist_of_length_le
- \+/\- *theorem* list.eq_of_suffix_of_length_eq
- \+/\- *theorem* list.erase_cons
- \+/\- *theorem* list.erase_cons_tail
- \+/\- *theorem* list.erasep_append_right
- \+/\- *theorem* list.erasep_cons
- \+/\- *theorem* list.erasep_cons_of_neg
- \+/\- *theorem* list.exists_of_mem_bind
- \+/\- *theorem* list.ext_le
- \+/\- *lemma* list.filter_false
- \+/\- *lemma* list.filter_true
- \+/\- *theorem* list.foldl1_eq_foldr1
- \+/\- *theorem* list.foldl_eq_foldr'
- \+/\- *theorem* list.foldl_eq_foldr
- \+/\- *theorem* list.foldl_eq_of_comm'
- \+/\- *theorem* list.foldl_eq_of_comm_of_assoc
- \+/\- *theorem* list.foldl_reverse
- \+/\- *theorem* list.foldr_eq_of_comm'
- \+/\- *theorem* list.foldr_reverse
- \+/\- *theorem* list.head_append
- \+/\- *lemma* list.head_mul_tail_prod'
- \+/\- *theorem* list.index_of_cons
- \+/\- *theorem* list.index_of_nth
- \+/\- *theorem* list.index_of_nth_le
- \+/\- *theorem* list.le_count_iff_repeat_sublist
- \+/\- *theorem* list.length_bind
- \+/\- *theorem* list.length_erase_of_mem
- \+/\- *theorem* list.mem_bind
- \+/\- *theorem* list.mem_bind_of_mem
- \+/\- *theorem* list.nth_le_reverse_aux1
- \+/\- *theorem* list.sublist_or_mem_of_sublist
- \+/\- *theorem* list.suffix_iff_eq_append

Modified src/data/list/tfae.lean


Modified src/data/num/lemmas.lean
- \+/\- *def* int.of_snum
- \+/\- *theorem* num.add_of_nat
- \+/\- *theorem* num.add_one
- \+/\- *theorem* num.add_succ
- \+/\- *theorem* num.add_to_nat
- \+/\- *theorem* num.add_to_znum
- \+/\- *theorem* num.add_zero
- \+/\- *theorem* num.bit0_of_bit0
- \+/\- *theorem* num.bit1_of_bit1
- \+/\- *theorem* num.bit_to_nat
- \+/\- *theorem* num.bitwise_to_nat
- \+/\- *theorem* num.cast_add
- \+/\- *theorem* num.cast_bit0
- \+/\- *theorem* num.cast_bit1
- \+/\- *theorem* num.cast_inj
- \+/\- *theorem* num.cast_le
- \+/\- *theorem* num.cast_lt
- \+/\- *theorem* num.cast_mul
- \+/\- *theorem* num.cast_of_znum
- \+/\- *theorem* num.cast_one
- \+/\- *theorem* num.cast_pos
- \+/\- *theorem* num.cast_sub'
- \+/\- *theorem* num.cast_succ'
- \+/\- *theorem* num.cast_succ
- \+/\- *theorem* num.cast_to_int
- \+/\- *theorem* num.cast_to_nat
- \+/\- *theorem* num.cast_to_znum
- \+/\- *theorem* num.cast_to_znum_neg
- \+/\- *theorem* num.cast_zero'
- \+/\- *theorem* num.cast_zero
- \+/\- *theorem* num.cmp_eq
- \+/\- *theorem* num.cmp_swap
- \+/\- *theorem* num.cmp_to_nat
- \+/\- *theorem* num.div_to_nat
- \+/\- *theorem* num.dvd_iff_mod_eq_zero
- \+/\- *theorem* num.dvd_to_nat
- \+/\- *theorem* num.gcd_to_nat
- \+/\- *theorem* num.gcd_to_nat_aux
- \+/\- *theorem* num.land_to_nat
- \+/\- *theorem* num.ldiff_to_nat
- \+/\- *theorem* num.le_iff_cmp
- \+/\- *theorem* num.le_to_nat
- \+/\- *theorem* num.lor_to_nat
- \+/\- *theorem* num.lt_iff_cmp
- \+/\- *theorem* num.lt_to_nat
- \+/\- *theorem* num.lxor_to_nat
- \+/\- *theorem* num.mem_of_znum'
- \+/\- *theorem* num.mod_to_nat
- \+/\- *theorem* num.mul_to_nat
- \+/\- *theorem* num.nat_size_to_nat
- \+/\- *theorem* num.of_nat'_eq
- \+/\- *theorem* num.of_nat_cast
- \+/\- *theorem* num.of_nat_inj
- \+/\- *theorem* num.of_nat_to_znum
- \+/\- *theorem* num.of_nat_to_znum_neg
- \+/\- *theorem* num.of_to_nat
- \+/\- *theorem* num.of_znum'_to_nat
- \+/\- *theorem* num.of_znum_to_nat
- \+/\- *theorem* num.ppred_to_nat
- \+/\- *theorem* num.pred_to_nat
- \+/\- *theorem* num.shiftl_to_nat
- \+/\- *theorem* num.shiftr_to_nat
- \+/\- *theorem* num.size_eq_nat_size
- \+/\- *theorem* num.size_to_nat
- \+/\- *theorem* num.sub_to_nat
- \+/\- *theorem* num.succ'_to_nat
- \+/\- *theorem* num.succ_to_nat
- \+/\- *theorem* num.test_bit_to_nat
- \+/\- *theorem* num.to_nat_inj
- \+/\- *theorem* num.to_nat_to_int
- \+/\- *theorem* num.to_of_nat
- \+/\- *theorem* num.to_znum_inj
- \+/\- *theorem* num.zero_add
- \+/\- *theorem* num.zneg_to_znum
- \+/\- *theorem* num.zneg_to_znum_neg
- \+/\- *theorem* pos_num.add_one
- \+/\- *theorem* pos_num.add_succ
- \+/\- *theorem* pos_num.add_to_nat
- \+/\- *theorem* pos_num.bit0_of_bit0
- \+/\- *theorem* pos_num.bit1_of_bit1
- \+/\- *theorem* pos_num.bit_to_nat
- \+/\- *theorem* pos_num.cast_add
- \+/\- *theorem* pos_num.cast_bit0
- \+/\- *theorem* pos_num.cast_bit1
- \+/\- *theorem* pos_num.cast_inj
- \+/\- *theorem* pos_num.cast_le
- \+/\- *theorem* pos_num.cast_lt
- \+/\- *theorem* pos_num.cast_mul
- \+/\- *theorem* pos_num.cast_one'
- \+/\- *theorem* pos_num.cast_one
- \+/\- *theorem* pos_num.cast_pos
- \+/\- *theorem* pos_num.cast_sub'
- \+/\- *theorem* pos_num.cast_succ
- \+/\- *theorem* pos_num.cast_to_int
- \+/\- *theorem* pos_num.cast_to_nat
- \+/\- *theorem* pos_num.cast_to_num
- \+/\- *theorem* pos_num.cast_to_znum
- \+/\- *theorem* pos_num.cmp_eq
- \+/\- *theorem* pos_num.cmp_swap
- \+/\- *theorem* pos_num.cmp_to_nat
- \+/\- *theorem* pos_num.cmp_to_nat_lemma
- \+/\- *theorem* pos_num.div'_to_nat
- \+/\- *theorem* pos_num.divmod_to_nat
- \+/\- *theorem* pos_num.divmod_to_nat_aux
- \+/\- *theorem* pos_num.le_iff_cmp
- \+/\- *theorem* pos_num.le_to_nat
- \+/\- *theorem* pos_num.lt_iff_cmp
- \+/\- *theorem* pos_num.lt_to_nat
- \+/\- *theorem* pos_num.mod'_to_nat
- \+/\- *theorem* pos_num.mul_to_nat
- \+/\- *theorem* pos_num.nat_size_pos
- \+/\- *theorem* pos_num.nat_size_to_nat
- \+/\- *theorem* pos_num.of_to_nat
- \+/\- *theorem* pos_num.one_add
- \+/\- *theorem* pos_num.one_le_cast
- \+/\- *theorem* pos_num.one_sub'
- \+/\- *theorem* pos_num.pred'_succ'
- \+/\- *theorem* pos_num.pred'_to_nat
- \+/\- *theorem* pos_num.pred_to_nat
- \+/\- *theorem* pos_num.size_eq_nat_size
- \+/\- *theorem* pos_num.size_to_nat
- \+/\- *theorem* pos_num.sub'_one
- \+/\- *theorem* pos_num.succ'_pred'
- \+/\- *theorem* pos_num.succ_to_nat
- \+/\- *theorem* pos_num.to_int_eq_succ_pred
- \+/\- *theorem* pos_num.to_nat_eq_succ_pred
- \+/\- *theorem* pos_num.to_nat_inj
- \+/\- *theorem* pos_num.to_nat_pos
- \+/\- *theorem* pos_num.to_nat_to_int
- \+/\- *theorem* znum.abs_to_nat
- \+/\- *theorem* znum.abs_to_znum
- \+/\- *theorem* znum.add_one
- \+/\- *theorem* znum.add_zero
- \+/\- *theorem* znum.bit0_of_bit0
- \+/\- *theorem* znum.bit1_of_bit1
- \+/\- *theorem* znum.cast_add
- \+/\- *theorem* znum.cast_bit0
- \+/\- *theorem* znum.cast_bit1
- \+/\- *theorem* znum.cast_bitm1
- \+/\- *theorem* znum.cast_inj
- \+/\- *theorem* znum.cast_le
- \+/\- *theorem* znum.cast_lt
- \+/\- *theorem* znum.cast_mul
- \+/\- *theorem* znum.cast_neg
- \+/\- *theorem* znum.cast_one
- \+/\- *theorem* znum.cast_pos
- \+/\- *theorem* znum.cast_succ
- \+/\- *theorem* znum.cast_to_int
- \+/\- *theorem* znum.cast_zero'
- \+/\- *theorem* znum.cast_zero
- \+/\- *theorem* znum.cast_zneg
- \+/\- *theorem* znum.cmp_to_int
- \+/\- *theorem* znum.div_to_int
- \+/\- *theorem* znum.dvd_iff_mod_eq_zero
- \+/\- *theorem* znum.dvd_to_int
- \+/\- *theorem* znum.gcd_to_nat
- \+/\- *theorem* znum.le_to_int
- \+/\- *theorem* znum.lt_to_int
- \+/\- *theorem* znum.mod_to_int
- \+/\- *theorem* znum.mul_to_int
- \+/\- *theorem* znum.neg_of_int
- \+/\- *theorem* znum.neg_zero
- \+/\- *theorem* znum.of_int'_eq
- \+/\- *theorem* znum.of_int_cast
- \+/\- *theorem* znum.of_nat_cast
- \+/\- *theorem* znum.of_to_int
- \+/\- *theorem* znum.to_int_inj
- \+/\- *theorem* znum.to_of_int
- \+/\- *theorem* znum.zero_add
- \+/\- *theorem* znum.zneg_bit1
- \+/\- *theorem* znum.zneg_bitm1
- \+/\- *theorem* znum.zneg_neg
- \+/\- *theorem* znum.zneg_pos
- \+/\- *theorem* znum.zneg_pred
- \+/\- *theorem* znum.zneg_succ
- \+/\- *theorem* znum.zneg_zneg

Modified src/data/zsqrtd/basic.lean
- \+/\- *def* zsqrtd.add
- \+/\- *theorem* zsqrtd.add_def
- \+/\- *theorem* zsqrtd.add_im
- \+/\- *theorem* zsqrtd.add_re
- \+/\- *theorem* zsqrtd.bit0_im
- \+/\- *theorem* zsqrtd.bit0_re
- \+/\- *theorem* zsqrtd.bit1_im
- \+/\- *theorem* zsqrtd.bit1_re
- \+/\- *theorem* zsqrtd.coe_int_im
- \+/\- *theorem* zsqrtd.coe_int_re
- \+/\- *theorem* zsqrtd.coe_int_val
- \+/\- *theorem* zsqrtd.coe_nat_im
- \+/\- *theorem* zsqrtd.coe_nat_re
- \+/\- *theorem* zsqrtd.coe_nat_val
- \+/\- *def* zsqrtd.conj
- \+/\- *theorem* zsqrtd.conj_im
- \+/\- *theorem* zsqrtd.conj_mul
- \+/\- *theorem* zsqrtd.conj_re
- \+/\- *theorem* zsqrtd.d_pos
- \+/\- *theorem* zsqrtd.decompose
- \+/\- *theorem* zsqrtd.divides_sq_eq_zero
- \+/\- *theorem* zsqrtd.divides_sq_eq_zero_z
- \+/\- *theorem* zsqrtd.ext
- \+/\- *theorem* zsqrtd.le_antisymm
- \+/\- *theorem* zsqrtd.le_arch
- \+/\- *theorem* zsqrtd.le_of_le_le
- \+/\- *theorem* zsqrtd.le_refl
- \+/\- *def* zsqrtd.mul
- \+/\- *theorem* zsqrtd.mul_conj
- \+/\- *theorem* zsqrtd.mul_im
- \+/\- *theorem* zsqrtd.mul_re
- \+/\- *theorem* zsqrtd.muld_val
- \+/\- *def* zsqrtd.neg
- \+/\- *theorem* zsqrtd.neg_im
- \+/\- *theorem* zsqrtd.neg_re
- \+/\- *def* zsqrtd.nonneg
- \+/\- *theorem* zsqrtd.nonneg_add
- \+/\- *lemma* zsqrtd.nonneg_add_lem
- \+/\- *theorem* zsqrtd.nonneg_antisymm
- \+/\- *theorem* zsqrtd.nonneg_cases
- \+/\- *theorem* zsqrtd.nonneg_iff_zero_le
- \+/\- *theorem* zsqrtd.nonneg_mul
- \+/\- *theorem* zsqrtd.nonneg_mul_lem
- \+/\- *theorem* zsqrtd.nonneg_muld
- \+/\- *theorem* zsqrtd.nonneg_smul
- \+/\- *def* zsqrtd.nonnegg
- \+/\- *theorem* zsqrtd.nonnegg_cases_left
- \+/\- *theorem* zsqrtd.nonnegg_cases_right
- \+/\- *theorem* zsqrtd.nonnegg_comm
- \+/\- *theorem* zsqrtd.nonnegg_neg_pos
- \+/\- *theorem* zsqrtd.nonnegg_pos_neg
- \+/\- *theorem* zsqrtd.not_divides_square
- \+/\- *theorem* zsqrtd.not_sq_le_succ
- \+/\- *def* zsqrtd.of_int
- \+/\- *theorem* zsqrtd.of_int_eq_coe
- \+/\- *theorem* zsqrtd.of_int_im
- \+/\- *theorem* zsqrtd.of_int_re
- \+/\- *def* zsqrtd.one
- \+/\- *theorem* zsqrtd.one_im
- \+/\- *theorem* zsqrtd.one_re
- \+/\- *theorem* zsqrtd.smul_val
- \+/\- *theorem* zsqrtd.smuld_val
- \+/\- *def* zsqrtd.sq_le
- \+/\- *theorem* zsqrtd.sq_le_add
- \+/\- *theorem* zsqrtd.sq_le_add_mixed
- \+/\- *theorem* zsqrtd.sq_le_cancel
- \+/\- *theorem* zsqrtd.sq_le_mul
- \+/\- *theorem* zsqrtd.sq_le_of_le
- \+/\- *theorem* zsqrtd.sq_le_smul
- \+/\- *def* zsqrtd.sqrtd
- \+/\- *theorem* zsqrtd.sqrtd_im
- \+/\- *theorem* zsqrtd.sqrtd_re
- \+/\- *def* zsqrtd.zero
- \+/\- *theorem* zsqrtd.zero_im
- \+/\- *theorem* zsqrtd.zero_re

Modified src/group_theory/congruence.lean
- \+/\- *def* con.correspondence

Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/submonoid.lean
- \+/\- *lemma* add_submonoid.mem_closure_singleton

Modified src/number_theory/dioph.lean
- \+/\- *theorem* dioph.abs_poly_dioph
- \+/\- *theorem* dioph.add_dioph
- \+/\- *theorem* dioph.and_dioph
- \+/\- *theorem* dioph.const_dioph
- \+/\- *theorem* dioph.dioph_comp2
- \+/\- *theorem* dioph.dioph_comp
- \+/\- *def* dioph.dioph_fn
- \+/\- *theorem* dioph.dioph_fn_comp1
- \+/\- *theorem* dioph.dioph_fn_comp2
- \+/\- *theorem* dioph.dioph_fn_comp
- \+/\- *theorem* dioph.dioph_fn_compn
- \+/\- *theorem* dioph.dioph_fn_iff_pfun
- \+/\- *theorem* dioph.dioph_fn_vec
- \+/\- *theorem* dioph.dioph_fn_vec_comp1
- \+/\- *theorem* dioph.dioph_list_all
- \+/\- *def* dioph.dioph_pfun
- \+/\- *theorem* dioph.dioph_pfun_comp1
- \+/\- *theorem* dioph.dioph_pfun_vec
- \+/\- *theorem* dioph.div_dioph
- \+/\- *theorem* dioph.dom_dioph
- \+/\- *theorem* dioph.dvd_dioph
- \+/\- *theorem* dioph.eq_dioph
- \+/\- *theorem* dioph.ex1_dioph
- \+/\- *theorem* dioph.ex_dioph
- \+/\- *theorem* dioph.ext
- \+/\- *theorem* dioph.inject_dummies
- \+/\- *lemma* dioph.inject_dummies_lem
- \+/\- *theorem* dioph.le_dioph
- \+/\- *theorem* dioph.lt_dioph
- \+/\- *theorem* dioph.mod_dioph
- \+/\- *theorem* dioph.modeq_dioph
- \+/\- *theorem* dioph.mul_dioph
- \+/\- *theorem* dioph.ne_dioph
- \+/\- *theorem* dioph.of_no_dummies
- \+/\- *theorem* dioph.or_dioph
- \+/\- *theorem* dioph.pell_dioph
- \+/\- *theorem* dioph.pow_dioph
- \+/\- *theorem* dioph.proj_dioph
- \+/\- *theorem* dioph.proj_dioph_of_nat
- \+/\- *theorem* dioph.reindex_dioph
- \+/\- *theorem* dioph.reindex_dioph_fn
- \+/\- *theorem* dioph.sub_dioph
- \+/\- *theorem* dioph.vec_ex1_dioph
- \+/\- *theorem* dioph.xn_dioph
- \+/\- *theorem* list_all.imp
- \+/\- *theorem* list_all_congr
- \+/\- *theorem* list_all_cons
- \+/\- *theorem* list_all_map
- \+/\- *theorem* vector3.append_insert
- \+/\- *theorem* vector_allp_iff_forall

Modified src/set_theory/ordinal.lean


Modified src/tactic/apply.lean


Modified src/tactic/lean_core_docs.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/omega/main.lean


Modified test/coinductive.lean


Modified test/localized/import3.lean


Modified test/norm_num.lean


Modified test/tidy.lean


Modified test/where.lean




## [2020-05-27 01:18:54](https://github.com/leanprover-community/mathlib/commit/2792c93)
feat(ring_theory/fintype): in a finite nonzero_semiring, fintype.card (units R) < fintype.card R ([#2793](https://github.com/leanprover-community/mathlib/pull/2793))
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *theorem* not_is_unit_zero

Modified src/algebra/gcd_domain.lean


Modified src/algebra/group/units.lean
- \+/\- *def* is_unit

Modified src/algebra/group/units_hom.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/ring.lean


Modified src/analysis/asymptotics.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* card_lt_card_of_injective_of_not_mem
- \+ *lemma* mem_image_univ_iff_mem_range

Modified src/group_theory/group_action.lean


Modified src/group_theory/monoid_localization.lean


Added src/ring_theory/fintype.lean
- \+ *lemma* card_units_lt

Modified src/ring_theory/ideals.lean


Modified src/ring_theory/power_series.lean




## [2020-05-26 17:35:27](https://github.com/leanprover-community/mathlib/commit/63b8c52)
chore(scripts): update nolints.txt ([#2833](https://github.com/leanprover-community/mathlib/pull/2833))
I am happy to remove some nolints for you!
#### Estimated changes



## [2020-05-26 16:47:21](https://github.com/leanprover-community/mathlib/commit/4dfd706)
chore(scripts): update nolints.txt ([#2831](https://github.com/leanprover-community/mathlib/pull/2831))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-26 16:47:19](https://github.com/leanprover-community/mathlib/commit/4ca776e)
feat(linear_algebra/quadratic_form): equivalence of quadratic forms ([#2769](https://github.com/leanprover-community/mathlib/pull/2769))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.equivalent.refl
- \+ *lemma* quadratic_form.equivalent.symm
- \+ *lemma* quadratic_form.equivalent.trans
- \+ *def* quadratic_form.equivalent
- \+ *lemma* quadratic_form.isometry.map_app
- \+ *def* quadratic_form.isometry.refl
- \+ *def* quadratic_form.isometry.symm
- \+ *def* quadratic_form.isometry.trans



## [2020-05-26 15:15:29](https://github.com/leanprover-community/mathlib/commit/9630eca)
feat(data/nat/primes): lemmas about min_fac ([#2790](https://github.com/leanprover-community/mathlib/pull/2790))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.min_fac_eq_one_iff
- \+ *lemma* nat.min_fac_eq_two_iff
- \+ *lemma* nat.min_fac_sq_le_self



## [2020-05-26 13:30:46](https://github.com/leanprover-community/mathlib/commit/895f568)
perf(tactic/lint): speed up nolint attribute ([#2828](https://github.com/leanprover-community/mathlib/pull/2828))
Looking up the nolint attribute only takes 15 seconds out of the 45 minutes, so speeding up this part has little effect.  More importantly, this PR removes one branch from the mathlib repository.
#### Estimated changes
Modified src/tactic/lint/basic.lean




## [2020-05-26 13:30:44](https://github.com/leanprover-community/mathlib/commit/1cf59fc)
chore(src/algebra/ordered_ring.lean): fix linting errors ([#2827](https://github.com/leanprover-community/mathlib/pull/2827))
[Mentioned, but not really discussed, in this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198747067).
This PR also removes `mul_pos'` and `mul_nonneg'` lemmas because they are now identical to the improved `mul_pos` and `mul_nonneg`.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* four_pos
- \+/\- *lemma* gt_of_mul_lt_mul_neg_left
- \- *lemma* mul_nonneg'
- \+/\- *lemma* mul_nonneg
- \- *lemma* mul_pos'
- \+/\- *lemma* mul_pos
- \+/\- *lemma* mul_self_nonneg
- \+/\- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+/\- *lemma* two_ge_one
- \+/\- *lemma* two_gt_one
- \+/\- *theorem* with_top.coe_eq_zero
- \+/\- *theorem* with_top.coe_zero
- \+/\- *theorem* with_top.top_ne_zero
- \+/\- *theorem* with_top.zero_eq_coe
- \+/\- *theorem* with_top.zero_ne_top

Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/rat/order.lean


Modified src/geometry/manifold/real_instances.lean




## [2020-05-26 13:30:42](https://github.com/leanprover-community/mathlib/commit/7d86475)
feat(data/polynomial): eq_one_of_is_unit_of_monic ([#2823](https://github.com/leanprover-community/mathlib/pull/2823))
~~Depends on [#2822](https://github.com/leanprover-community/mathlib/pull/2822) ~~
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_nonneg_iff_ne_zero
- \+ *lemma* polynomial.eq_one_of_is_unit_of_monic
- \+ *lemma* polynomial.nat_degree_eq_zero_iff_degree_le_zero



## [2020-05-26 13:30:40](https://github.com/leanprover-community/mathlib/commit/099ffd3)
chore(algebra/free_monoid): use implicit args in `lift` ([#2821](https://github.com/leanprover-community/mathlib/pull/2821))
#### Estimated changes
Modified src/algebra/free_monoid.lean
- \+/\- *lemma* free_monoid.comp_lift
- \+ *lemma* free_monoid.hom_map_lift
- \+/\- *lemma* free_monoid.lift_apply
- \+/\- *lemma* free_monoid.lift_comp_of
- \+/\- *lemma* free_monoid.lift_eval_of
- \+/\- *lemma* free_monoid.lift_restrict
- \+ *lemma* free_monoid.lift_symm_apply

Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.coe_mk'

Modified src/group_theory/submonoid.lean
- \+/\- *lemma* submonoid.closure_eq_mrange



## [2020-05-26 13:30:38](https://github.com/leanprover-community/mathlib/commit/fc79089)
feat(number_theory/primorial): Bound on the primorial function ([#2701](https://github.com/leanprover-community/mathlib/pull/2701))
This lemma is needed for Erdös's proof of Bertrand's postulate, but it may be of independent interest.
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.self_mem_range_succ

Modified src/data/list/range.lean
- \+ *theorem* list.self_mem_range_succ

Modified src/data/multiset.lean
- \+ *theorem* multiset.self_mem_range_succ

Modified src/data/nat/basic.lean
- \+ *lemma* nat.choose_symm_half

Modified src/data/nat/choose.lean
- \+/\- *lemma* choose_le_middle
- \+ *lemma* choose_middle_le_pow

Added src/number_theory/primorial.lean
- \+ *lemma* dvd_choose_of_middling_prime
- \+ *def* primorial
- \+ *lemma* primorial_le_4_pow
- \+ *lemma* primorial_succ
- \+ *lemma* prod_primes_dvd



## [2020-05-26 11:43:31](https://github.com/leanprover-community/mathlib/commit/2c40bd3)
feat(tactic/push_cast): take list of extra simp lemmas ([#2825](https://github.com/leanprover-community/mathlib/pull/2825))
closes [#2783](https://github.com/leanprover-community/mathlib/pull/2783)
#### Estimated changes
Modified src/tactic/norm_cast.lean


Modified test/norm_cast.lean




## [2020-05-26 10:40:07](https://github.com/leanprover-community/mathlib/commit/ab2e52e)
feat(order/filter/basic): a local left inverse locally equals a local right inverse ([#2808](https://github.com/leanprover-community/mathlib/pull/2808))
#### Estimated changes
Modified src/analysis/calculus/inverse.lean
- \+ *lemma* has_strict_fderiv_at.local_inverse_tendsto
- \+ *lemma* has_strict_fderiv_at.local_inverse_unique

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq_of_left_inv_of_right_inv



## [2020-05-26 10:40:05](https://github.com/leanprover-community/mathlib/commit/8c36b32)
feat(order/filter/basic): add `eventually.curry` ([#2807](https://github.com/leanprover-community/mathlib/pull/2807))
I'm not sure that this is a good name. Suggestions of better names are welcome.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.curry
- \+ *lemma* filter.eventually_prod_iff

Modified src/topology/constructions.lean
- \+ *lemma* filter.eventually.curry_nhds



## [2020-05-26 10:40:03](https://github.com/leanprover-community/mathlib/commit/597946d)
feat(analysis/calculus/implicit): Implicit function theorem ([#2749](https://github.com/leanprover-community/mathlib/pull/2749))
Fixes [#1849](https://github.com/leanprover-community/mathlib/pull/1849)
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/2749.20Implicit.20function.20theorem).
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \- *lemma* has_strict_fderiv_at.has_strict_deriv_at

Added src/analysis/calculus/implicit.lean
- \+ *lemma* has_strict_fderiv_at.eq_implicit_function
- \+ *lemma* has_strict_fderiv_at.eq_implicit_function_of_complemented
- \+ *def* has_strict_fderiv_at.implicit_function
- \+ *def* has_strict_fderiv_at.implicit_function_data_of_complemented
- \+ *def* has_strict_fderiv_at.implicit_function_of_complemented
- \+ *def* has_strict_fderiv_at.implicit_to_local_homeomorph
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_apply_ker
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_fst
- \+ *def* has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply_ker
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_fst
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_self
- \+ *lemma* has_strict_fderiv_at.implicit_to_local_homeomorph_self
- \+ *lemma* has_strict_fderiv_at.map_implicit_function_eq
- \+ *lemma* has_strict_fderiv_at.map_implicit_function_of_complemented_eq
- \+ *lemma* has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_source
- \+ *lemma* has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_target
- \+ *lemma* has_strict_fderiv_at.mem_implicit_to_local_homeomorph_source
- \+ *lemma* has_strict_fderiv_at.mem_implicit_to_local_homeomorph_target
- \+ *lemma* has_strict_fderiv_at.to_implicit_function
- \+ *lemma* has_strict_fderiv_at.to_implicit_function_of_complemented
- \+ *def* implicit_function_data.implicit_function
- \+ *lemma* implicit_function_data.implicit_function_apply_image
- \+ *lemma* implicit_function_data.implicit_function_has_strict_fderiv_at
- \+ *lemma* implicit_function_data.left_map_implicit_function
- \+ *lemma* implicit_function_data.map_pt_mem_to_local_homeomorph_target
- \+ *def* implicit_function_data.prod_fun
- \+ *lemma* implicit_function_data.prod_fun_apply
- \+ *lemma* implicit_function_data.prod_map_implicit_function
- \+ *lemma* implicit_function_data.pt_mem_to_local_homeomorph_source
- \+ *lemma* implicit_function_data.right_map_implicit_function
- \+ *def* implicit_function_data.to_local_homeomorph
- \+ *lemma* implicit_function_data.to_local_homeomorph_apply
- \+ *lemma* implicit_function_data.to_local_homeomorph_coe

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* continuous_linear_map.is_O_comp

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.is_complete_ker



## [2020-05-26 09:33:44](https://github.com/leanprover-community/mathlib/commit/b4d4d9a)
feat(ring_theory/algebra): more on restrict_scalars ([#2445](https://github.com/leanprover-community/mathlib/pull/2445))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/data/complex/module.lean


Modified src/ring_theory/algebra.lean
- \+ *def* algebra.restrict_scalars_equiv
- \+ *lemma* algebra.restrict_scalars_equiv_apply
- \+ *lemma* algebra.restrict_scalars_equiv_symm_apply
- \+/\- *def* linear_map.restrict_scalars
- \+ *lemma* linear_map_algebra_module.smul_apply
- \+ *def* module.restrict_scalars'
- \+/\- *def* module.restrict_scalars
- \+ *lemma* module.restrict_scalars_smul_def
- \+ *lemma* restrict_scalars_ker
- \+ *def* submodule.restrict_scalars
- \+ *lemma* submodule.restrict_scalars_bot
- \+ *lemma* submodule.restrict_scalars_mem
- \+ *lemma* submodule.restrict_scalars_top



## [2020-05-26 08:11:51](https://github.com/leanprover-community/mathlib/commit/ea403b3)
feat(algebra/group_with_zero): mul_self_mul_inv ([#2795](https://github.com/leanprover-community/mathlib/pull/2795))
I found this lemma was useful for simplifying some expressions without
needing to split into cases or provide a proof that the denominator is
nonzero, and it doesn't show up with library_search.
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \+ *lemma* div_div_self
- \+ *lemma* div_self_mul_self
- \+ *lemma* inv_mul_mul_self
- \+ *lemma* mul_inv_mul_self
- \+ *lemma* mul_self_div_self
- \+ *lemma* mul_self_mul_inv



## [2020-05-26 06:41:18](https://github.com/leanprover-community/mathlib/commit/1c265e2)
feat(data/nat/basic): with_bot lemmas ([#2822](https://github.com/leanprover-community/mathlib/pull/2822))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.with_bot.coe_nonneg
- \+ *lemma* nat.with_bot.lt_zero_iff



## [2020-05-26 05:06:40](https://github.com/leanprover-community/mathlib/commit/9bb9956)
feat(data/nat/basic): inequalities ([#2801](https://github.com/leanprover-community/mathlib/pull/2801))
Adds some simple inequalities about `nat.pow`.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_two_pow
- \+ *lemma* nat.one_le_pow'
- \+ *lemma* nat.one_le_pow
- \+ *lemma* nat.one_le_two_pow
- \+ *lemma* nat.one_lt_pow'
- \+ *lemma* nat.one_lt_pow
- \+ *lemma* nat.one_lt_two_pow'
- \+ *lemma* nat.one_lt_two_pow



## [2020-05-26 00:59:03](https://github.com/leanprover-community/mathlib/commit/4b616e6)
feat(category_theory/limits): transport lemmas for kernels ([#2779](https://github.com/leanprover-community/mathlib/pull/2779))
#### Estimated changes
Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel.cokernel_iso
- \+ *def* category_theory.limits.cokernel.of_iso_comp
- \+ *def* category_theory.limits.is_cokernel.cokernel_iso
- \+ *def* category_theory.limits.is_cokernel.of_iso_comp
- \+ *def* category_theory.limits.is_kernel.iso_kernel
- \+ *def* category_theory.limits.is_kernel.of_comp_iso
- \+ *def* category_theory.limits.kernel.iso_kernel
- \+ *def* category_theory.limits.kernel.of_comp_iso



## [2020-05-25 20:20:32](https://github.com/leanprover-community/mathlib/commit/aad2dfc)
fix(group_with_zero): fix definition of comm_monoid_with_zero ([#2818](https://github.com/leanprover-community/mathlib/pull/2818))
Also generate instance comm_group_with_zero -> comm_monoid_with_zero.
#### Estimated changes
Modified src/algebra/group_with_zero.lean




## [2020-05-25 15:03:03](https://github.com/leanprover-community/mathlib/commit/ae5b55b)
feat(algebra/ring): ring_hom.map_dvd ([#2813](https://github.com/leanprover-community/mathlib/pull/2813))
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* ring_hom.map_dvd



## [2020-05-25 12:50:28](https://github.com/leanprover-community/mathlib/commit/52b839f)
feat(data/polynomial): is_unit_C ([#2812](https://github.com/leanprover-community/mathlib/pull/2812))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.is_unit_C



## [2020-05-25 12:50:26](https://github.com/leanprover-community/mathlib/commit/3e0668e)
feat(linear_algebra/projection): add `equiv_prod_of_surjective_of_is_compl` ([#2787](https://github.com/leanprover-community/mathlib/pull/2787))
If kernels of two surjective linear maps `f`, `g` are complement subspaces,
then `x ↦ (f x, g x)` defines a  linear equivalence.
I also add a version of this equivalence for continuous maps.
Depends on [#2785](https://github.com/leanprover-community/mathlib/pull/2785)
#### Estimated changes
Modified src/analysis/normed_space/complemented.lean
- \+ *lemma* continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl
- \+ *def* continuous_linear_map.equiv_prod_of_surjective_of_is_compl
- \+ *lemma* continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply
- \+ *lemma* continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/projection.lean
- \+ *lemma* linear_map.coe_equiv_prod_of_surjective_of_is_compl
- \+ *def* linear_map.equiv_prod_of_surjective_of_is_compl
- \+ *lemma* linear_map.equiv_prod_of_surjective_of_is_compl_apply
- \+/\- *lemma* linear_map.is_compl_of_proj
- \+/\- *lemma* linear_map.ker_id_sub_eq_of_proj
- \+ *lemma* linear_map.range_eq_of_proj

Modified src/topology/algebra/module.lean




## [2020-05-25 12:07:49](https://github.com/leanprover-community/mathlib/commit/60f0b01)
feat(logic/function): define `semiconj` and `commute` ([#2788](https://github.com/leanprover-community/mathlib/pull/2788))
#### Estimated changes
Added src/logic/function/conjugate.lean
- \+ *lemma* function.commute.comp_left
- \+ *lemma* function.commute.comp_right
- \+ *lemma* function.commute.id_left
- \+ *lemma* function.commute.id_right
- \+ *lemma* function.commute.refl
- \+ *lemma* function.commute.symm
- \+ *def* function.commute
- \+ *lemma* function.semiconj.commute
- \+ *lemma* function.semiconj.comp_left
- \+ *lemma* function.semiconj.comp_right
- \+ *lemma* function.semiconj.id_left
- \+ *lemma* function.semiconj.id_right
- \+ *lemma* function.semiconj.inverses_right
- \+ *def* function.semiconj
- \+ *lemma* function.semiconj₂.comp
- \+ *lemma* function.semiconj₂.id_left
- \+ *def* function.semiconj₂



## [2020-05-25 10:18:13](https://github.com/leanprover-community/mathlib/commit/96f318c)
feat(algebra/group_power): int.nat_abs_pow_two ([#2811](https://github.com/leanprover-community/mathlib/pull/2811))
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* int.nat_abs_pow_two

Modified src/number_theory/sum_four_squares.lean




## [2020-05-25 10:18:11](https://github.com/leanprover-community/mathlib/commit/9da47ad)
feat(data/zmod): lemmas about coercions to zmod ([#2802](https://github.com/leanprover-community/mathlib/pull/2802))
I'm not particularly happy with the location of these new lemmas within the file `data.zmod`. If anyone has a suggestion that they should be some particular place higher or lower in the file, that would be welcome.
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.int_coe_eq_int_coe_iff

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_mod_int
- \+ *lemma* zmod.int_coe_eq_int_coe_iff
- \+ *lemma* zmod.int_coe_zmod_eq_zero_iff_dvd
- \+ *lemma* zmod.nat_coe_eq_nat_coe_iff
- \+ *lemma* zmod.nat_coe_zmod_eq_zero_iff_dvd



## [2020-05-25 08:49:00](https://github.com/leanprover-community/mathlib/commit/dd062f0)
feat(data/nat/prime): pow_not_prime ([#2810](https://github.com/leanprover-community/mathlib/pull/2810))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.pow_not_prime



## [2020-05-25 07:24:08](https://github.com/leanprover-community/mathlib/commit/a2d5007)
chore(topology/algebra/module): prove `fst.prod snd = id` ([#2806](https://github.com/leanprover-community/mathlib/pull/2806))
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.fst_prod_snd



## [2020-05-25 07:24:07](https://github.com/leanprover-community/mathlib/commit/ccf646d)
chore(set_theory/ordinal): use a `protected lemma` to drop a `nolint` ([#2805](https://github.com/leanprover-community/mathlib/pull/2805))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *lemma* ordinal.div_def
- \- *def* ordinal.div_def



## [2020-05-25 07:24:05](https://github.com/leanprover-community/mathlib/commit/a3b3aa6)
fix(tactic/norm_num): workaround int.sub unfolding bug ([#2804](https://github.com/leanprover-community/mathlib/pull/2804))
Fixes https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/certificates.20for.20calculations/near/198631936 . Or rather, it works around an issue in how the kernel unfolds applications. The real fix is probably to adjust the definitional height or other heuristics around `add_group_has_sub` and `int.sub` so that tries to prove that they are defeq that way rather than unfolding `bit0` and `bit1`. Here is a MWE for the issue:
```lean
example : int.has_sub = add_group_has_sub := rfl
example :
  (@has_sub.sub ℤ int.has_sub 5000 2 : ℤ) =
  (@has_sub.sub ℤ add_group_has_sub 5000 2) := rfl -- deep recursion
```
#### Estimated changes
Modified src/tactic/norm_num.lean
- \+ *theorem* norm_num.int_sub_hack

Modified test/norm_num.lean




## [2020-05-25 06:35:44](https://github.com/leanprover-community/mathlib/commit/6552f21)
feat(algebra/add_torsor): torsors of additive group actions ([#2720](https://github.com/leanprover-community/mathlib/pull/2720))
Define torsors of additive group actions, to the extent needed for
(and with notation motivated by) affine spaces, to the extent needed
for Euclidean spaces.  See
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations
for the discussion leading to this particular structure.
#### Estimated changes
Added src/algebra/add_torsor.lean
- \+ *lemma* add_action.vadd_assoc
- \+ *lemma* add_action.vadd_comm
- \+ *lemma* add_action.vadd_left_cancel
- \+ *lemma* add_action.zero_vadd
- \+ *lemma* add_torsor.eq_of_vsub_eq_zero
- \+ *lemma* add_torsor.neg_vsub_eq_vsub_rev
- \+ *lemma* add_torsor.vadd_right_cancel
- \+ *lemma* add_torsor.vadd_vsub
- \+ *lemma* add_torsor.vadd_vsub_assoc
- \+ *lemma* add_torsor.vsub_add_vsub_cancel
- \+ *lemma* add_torsor.vsub_eq_zero_iff_eq
- \+ *lemma* add_torsor.vsub_self
- \+ *def* add_torsor.vsub_set
- \+ *lemma* add_torsor.vsub_sub_vsub_left_cancel
- \+ *lemma* add_torsor.vsub_sub_vsub_right_cancel
- \+ *lemma* add_torsor.vsub_vadd
- \+ *lemma* add_torsor.vsub_vadd_eq_vsub_sub



## [2020-05-25 05:05:19](https://github.com/leanprover-community/mathlib/commit/518d0fd)
feat(data/int/basic): eq_zero_of_dvd_of_nonneg_of_lt ([#2803](https://github.com/leanprover-community/mathlib/pull/2803))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.eq_zero_of_dvd_of_nonneg_of_lt
- \+ *lemma* int.nat_abs_lt_nat_abs_of_nonneg_of_lt



## [2020-05-24 19:02:14](https://github.com/leanprover-community/mathlib/commit/8d352b2)
feat(char_p): generalize zmod.neg_one_ne_one ([#2796](https://github.com/leanprover-community/mathlib/pull/2796))
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.neg_one_ne_one

Modified src/data/zmod/basic.lean




## [2020-05-24 17:52:18](https://github.com/leanprover-community/mathlib/commit/61b57cd)
chore(scripts): update nolints.txt ([#2799](https://github.com/leanprover-community/mathlib/pull/2799))
I am happy to remove some nolints for you!
#### Estimated changes



## [2020-05-24 17:03:59](https://github.com/leanprover-community/mathlib/commit/1445e08)
chore(scripts): update nolints.txt ([#2798](https://github.com/leanprover-community/mathlib/pull/2798))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-24 16:14:04](https://github.com/leanprover-community/mathlib/commit/8590081)
feat(category_theory): Product comparison ([#2753](https://github.com/leanprover-community/mathlib/pull/2753))
Construct the product comparison morphism, and show it's an iso iff F preserves binary products.
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.prod_comparison
- \+ *lemma* category_theory.limits.prod_comparison_natural

Added src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \+ *def* category_theory.limits.alternative_cone
- \+ *def* category_theory.limits.alternative_cone_is_limit
- \+ *def* category_theory.limits.preserves_binary_prod_of_prod_comparison_iso



## [2020-05-24 15:07:07](https://github.com/leanprover-community/mathlib/commit/292fc04)
feat(category_theory): adjunction convenience defs ([#2754](https://github.com/leanprover-community/mathlib/pull/2754))
Transport adjunctions along natural isomorphisms, and `is_left_adjoint` or `is_right_adjoint` versions of existing adjunction properties.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *def* category_theory.adjunction.equiv_homset_left_of_nat_iso
- \+ *lemma* category_theory.adjunction.equiv_homset_left_of_nat_iso_apply
- \+ *lemma* category_theory.adjunction.equiv_homset_left_of_nat_iso_symm_apply
- \+ *def* category_theory.adjunction.equiv_homset_right_of_nat_iso
- \+ *lemma* category_theory.adjunction.equiv_homset_right_of_nat_iso_apply
- \+ *lemma* category_theory.adjunction.equiv_homset_right_of_nat_iso_symm_apply
- \+ *def* category_theory.adjunction.left_adjoint_of_nat_iso
- \+ *def* category_theory.adjunction.of_nat_iso_left
- \+ *def* category_theory.adjunction.of_nat_iso_right
- \+ *def* category_theory.adjunction.right_adjoint_of_nat_iso



## [2020-05-24 09:09:11](https://github.com/leanprover-community/mathlib/commit/2ef444a)
feat(linear_algebra/basic): range of `linear_map.prod` ([#2785](https://github.com/leanprover-community/mathlib/pull/2785))
Also make `ker_prod` a `simp` lemma.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.ker_prod
- \+ *lemma* linear_map.range_prod_eq
- \+ *lemma* linear_map.range_prod_le

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.eq_symm_apply
- \+ *lemma* continuous_linear_equiv.symm_apply_eq
- \+ *lemma* continuous_linear_map.ker_prod
- \+ *lemma* continuous_linear_map.range_prod_eq
- \+ *lemma* continuous_linear_map.range_prod_le



## [2020-05-24 07:37:41](https://github.com/leanprover-community/mathlib/commit/5449203)
chore(order/basic): change "minimum" in descriptions to "minimal" ([#2789](https://github.com/leanprover-community/mathlib/pull/2789))
#### Estimated changes
Modified src/order/basic.lean




## [2020-05-23 13:13:15](https://github.com/leanprover-community/mathlib/commit/79e296b)
doc(archive/100-theorems-list): Update README.md ([#2750](https://github.com/leanprover-community/mathlib/pull/2750))
Making the 100.yaml file more discoverable.
#### Estimated changes
Modified archive/100-theorems-list/README.md




## [2020-05-23 12:26:58](https://github.com/leanprover-community/mathlib/commit/2a3f59a)
chore(scripts): update nolints.txt ([#2782](https://github.com/leanprover-community/mathlib/pull/2782))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-23 11:01:14](https://github.com/leanprover-community/mathlib/commit/2b79f1d)
feat(ring_theory/ideal_operations): lemmas about ideals and galois connections ([#2767](https://github.com/leanprover-community/mathlib/pull/2767))
depends on [#2766](https://github.com/leanprover-community/mathlib/pull/2766)
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *lemma* monotone.le_map_Sup
- \+ *lemma* monotone.map_Inf_le

Modified src/order/galois_connection.lean
- \+ *lemma* galois_connection.l_unique
- \+ *lemma* galois_connection.u_unique

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* ideal.comap_Inf
- \+ *lemma* ideal.comap_comap
- \+ *lemma* ideal.comap_id
- \+ *lemma* ideal.comap_infi
- \+ *lemma* ideal.comap_injective_of_surjective
- \+ *lemma* ideal.comap_map_comap
- \+ *lemma* ideal.comap_top
- \- *theorem* ideal.comap_top
- \+ *lemma* ideal.gc_map_comap
- \+ *def* ideal.gi_map_comap
- \+ *lemma* ideal.le_comap_map
- \+ *lemma* ideal.le_comap_of_map_le
- \+ *lemma* ideal.map_Sup
- \+ *lemma* ideal.map_bot
- \- *theorem* ideal.map_bot
- \+ *lemma* ideal.map_comap_le
- \+ *lemma* ideal.map_comap_map
- \+ *lemma* ideal.map_eq_bot_iff_le_ker
- \+ *lemma* ideal.map_id
- \+ *lemma* ideal.map_inf_comap_of_surjective
- \+ *lemma* ideal.map_infi_comap_of_surjective
- \+ *lemma* ideal.map_le_of_le_comap
- \+ *lemma* ideal.map_map
- \+ *lemma* ideal.map_sup
- \- *theorem* ideal.map_sup
- \+ *lemma* ideal.map_sup_comap_of_surjective
- \+ *lemma* ideal.map_supr
- \+ *lemma* ideal.map_supr_comap_of_surjective
- \+ *lemma* ideal.map_surjective_of_surjective
- \+ *lemma* ideal.mul_le_left
- \+ *lemma* ideal.mul_le_right
- \+ *lemma* ideal.mul_left_self_sup
- \+ *lemma* ideal.mul_right_self_sup
- \+ *lemma* ideal.sup_mul_left_self
- \+ *lemma* ideal.sup_mul_right_self
- \+/\- *theorem* submodule.annihilator_supr
- \+/\- *theorem* submodule.infi_colon_supr



## [2020-05-23 09:33:06](https://github.com/leanprover-community/mathlib/commit/ceb13ba)
chore(order/basic): add `monotone.order_dual`, `strict_mono.order_dual` ([#2778](https://github.com/leanprover-community/mathlib/pull/2778))
Also split long lines and lint.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/order/basic.lean
- \+/\- *def* decidable_linear_order_of_STO'
- \+/\- *theorem* is_strict_total_order'.swap
- \+/\- *lemma* le_of_forall_ge_of_dense
- \+/\- *lemma* le_of_forall_le_of_dense
- \+ *theorem* monotone.order_dual
- \+ *theorem* strict_mono.order_dual



## [2020-05-23 09:33:05](https://github.com/leanprover-community/mathlib/commit/90abd3b)
feat(data/fintype): finset.univ_map_embedding ([#2765](https://github.com/leanprover-community/mathlib/pull/2765))
Adds the lemma
```
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  (finset.univ).map e = finset.univ :=
```
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_map_embedding
- \+ *lemma* finset.univ_map_equiv_to_embedding
- \+ *lemma* function.embedding.equiv_of_fintype_self_embedding_to_embedding



## [2020-05-23 09:33:02](https://github.com/leanprover-community/mathlib/commit/6948505)
feat(data/polynomial): prime_of_degree_eq_one_of_monic ([#2745](https://github.com/leanprover-community/mathlib/pull/2745))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_normalize
- \+ *lemma* polynomial.irreducible_of_degree_eq_one_of_monic
- \+ *lemma* polynomial.prime_of_degree_eq_one
- \+ *lemma* polynomial.prime_of_degree_eq_one_of_monic



## [2020-05-23 07:44:20](https://github.com/leanprover-community/mathlib/commit/8c1793f)
chore(data/equiv): make `equiv.ext` args use { } ([#2776](https://github.com/leanprover-community/mathlib/pull/2776))
Other changes:
* rename lemmas `eq_of_to_fun_eq` to `coe_fn_injective`;
* add `left_inverse.eq_right_inverse` and use it to prove `equiv.ext`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.coe_fn_injective
- \- *theorem* equiv.eq_of_to_fun_eq
- \+/\- *lemma* equiv.ext
- \+/\- *lemma* equiv.perm.ext
- \+/\- *theorem* equiv.symm_trans
- \+/\- *theorem* equiv.trans_symm

Modified src/data/equiv/local_equiv.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/ring.lean


Modified src/data/fintype/basic.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_equiv.ext

Modified src/linear_algebra/determinant.lean


Modified src/logic/function/basic.lean
- \+ *theorem* function.left_inverse.eq_right_inverse

Modified src/order/order_iso.lean
- \+ *theorem* order_embedding.coe_fn_injective
- \- *theorem* order_embedding.eq_of_to_fun_eq
- \+ *theorem* order_iso.coe_fn_injective
- \- *theorem* order_iso.eq_of_to_fun_eq

Modified src/set_theory/ordinal.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/isometry.lean




## [2020-05-22 09:41:03](https://github.com/leanprover-community/mathlib/commit/f66caaa)
chore(scripts): update nolints.txt ([#2777](https://github.com/leanprover-community/mathlib/pull/2777))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-22 08:09:58](https://github.com/leanprover-community/mathlib/commit/c6aab26)
feat(algebra/invertible): invertible_of_ring_char_not_dvd ([#2775](https://github.com/leanprover-community/mathlib/pull/2775))
```
def invertible_of_ring_char_not_dvd {R : Type*} [field R] {t : ℕ} (not_dvd : ¬(ring_char R ∣ t)) :
  invertible (t : R)
```
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *def* invertible_of_char_p_not_dvd
- \+ *def* invertible_of_ring_char_not_dvd



## [2020-05-22 08:09:56](https://github.com/leanprover-community/mathlib/commit/58789f7)
feat(analysis/normed_space/banach): add `continuous_linear_equiv.of_bijective` ([#2774](https://github.com/leanprover-community/mathlib/pull/2774))
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* continuous_linear_equiv.coe_fn_of_bijective
- \+ *lemma* continuous_linear_equiv.of_bijective_apply_symm_apply
- \+ *lemma* continuous_linear_equiv.of_bijective_symm_apply_apply



## [2020-05-22 07:28:22](https://github.com/leanprover-community/mathlib/commit/80ad9ed)
refactor(ring_theory/localization): characterise ring localizations up to isomorphism ([#2714](https://github.com/leanprover-community/mathlib/pull/2714))
Beginnings of ```ring_theory/localization``` refactor from [#2675](https://github.com/leanprover-community/mathlib/pull/2675).
It's a bit sad that using the characteristic predicate means Lean can't infer the R-algebra structure of the localization. I've tried to get round this, but I'm not using •, and I've duplicated some fairly random lemmas about modules & algebras to take ```f``` as an explicit argument - mostly just what I needed to make ```fractional_ideal``` work. Should I duplicate more?
My comments in the ```fractional_ideal``` docs about 'preserving definitional equalities' wrt getting an R-module structure from an R-algebra structure: do they make sense? I had some errors about definitional equality of instances which I *think* I fixed after making sure the R-module structure always came from the R-algebra structure, as well as doing a few other things. I never chased up exactly what the errors were or how they went away, so I'm just guessing at my explanation.
Things I've got left to PR to ```ring_theory/localization``` after this: 
- ```away``` (localization at submonoid generated by one element)
- localization as a quotient type & proof it satisfies the char pred
- localization at the complement of a prime ideal and the fact this is a local ring
- more lemmas about fields of fractions
- the order embedding for ideals of the localization vs. ideals of the original ring
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ring.fractional_ideal.bot_eq_zero
- \+/\- *lemma* ring.fractional_ideal.coe_mem_one
- \+/\- *lemma* ring.fractional_ideal.div_nonzero
- \+/\- *lemma* ring.fractional_ideal.div_one
- \+/\- *lemma* ring.fractional_ideal.eq_zero_iff
- \+/\- *lemma* ring.fractional_ideal.ext
- \+/\- *lemma* ring.fractional_ideal.fractional_div_of_nonzero
- \+/\- *lemma* ring.fractional_ideal.fractional_inf
- \+/\- *lemma* ring.fractional_ideal.fractional_mul
- \+/\- *lemma* ring.fractional_ideal.fractional_of_subset_one
- \+/\- *lemma* ring.fractional_ideal.fractional_sup
- \+/\- *lemma* ring.fractional_ideal.inv_nonzero
- \+/\- *lemma* ring.fractional_ideal.le_iff
- \+/\- *lemma* ring.fractional_ideal.mem_one_iff
- \+/\- *lemma* ring.fractional_ideal.mem_zero_iff
- \+/\- *lemma* ring.fractional_ideal.mul_left_mono
- \+/\- *lemma* ring.fractional_ideal.mul_right_mono
- \+/\- *lemma* ring.fractional_ideal.ne_zero_of_mul_eq_one
- \+/\- *lemma* ring.fractional_ideal.nonzero_iff_val_nonzero
- \+/\- *theorem* ring.fractional_ideal.right_inverse_eq
- \+/\- *lemma* ring.fractional_ideal.sup_eq_add
- \+/\- *lemma* ring.fractional_ideal.val_add
- \+/\- *lemma* ring.fractional_ideal.val_mul
- \+/\- *lemma* ring.fractional_ideal.val_zero
- \+/\- *lemma* ring.fractional_ideal.zero_le
- \+/\- *def* ring.fractional_ideal
- \+/\- *def* ring.is_fractional

Modified src/ring_theory/localization.lean
- \+ *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *def* fraction_map.to_integral_domain
- \+ *def* fraction_map
- \- *def* localization.at_prime
- \- *def* localization.away.inv_self
- \- *lemma* localization.away.lift_coe
- \- *lemma* localization.away.lift_comp_of
- \- *lemma* localization.away.lift_of
- \- *def* localization.away
- \+ *def* localization.codomain
- \- *lemma* localization.coe_add
- \- *lemma* localization.coe_is_unit'
- \- *lemma* localization.coe_is_unit
- \- *lemma* localization.coe_mul
- \- *lemma* localization.coe_mul_eq_smul
- \- *lemma* localization.coe_mul_mk
- \- *lemma* localization.coe_neg
- \- *lemma* localization.coe_one
- \- *lemma* localization.coe_pow
- \- *lemma* localization.coe_smul
- \- *lemma* localization.coe_sub
- \- *lemma* localization.coe_zero
- \+ *lemma* localization.epic_of_localization_map
- \+ *lemma* localization.eq_iff_eq
- \+ *lemma* localization.eq_iff_exists
- \+ *theorem* localization.eq_mk'_iff_mul_eq
- \+ *lemma* localization.eq_of_eq
- \+ *lemma* localization.eq_zero_of_fst_eq_zero
- \- *def* localization.equiv_of_equiv
- \+ *lemma* localization.ext
- \+ *lemma* localization.ext_iff
- \- *lemma* localization.fraction_ring.eq_zero_of
- \- *lemma* localization.fraction_ring.eq_zero_of_ne_zero_of_mul_eq_zero
- \- *def* localization.fraction_ring.equiv_of_equiv
- \- *def* localization.fraction_ring.inv_aux
- \- *def* localization.fraction_ring.map
- \- *lemma* localization.fraction_ring.map_coe
- \- *lemma* localization.fraction_ring.map_comp_of
- \- *lemma* localization.fraction_ring.map_of
- \- *lemma* localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero
- \- *lemma* localization.fraction_ring.mk_eq_div'
- \- *lemma* localization.fraction_ring.mk_eq_div
- \- *lemma* localization.fraction_ring.mk_inv'
- \- *lemma* localization.fraction_ring.mk_inv
- \- *lemma* localization.fraction_ring.of.injective
- \- *def* localization.fraction_ring
- \+/\- *def* localization.is_integer
- \+/\- *lemma* localization.is_integer_add
- \- *lemma* localization.is_integer_coe
- \+/\- *lemma* localization.is_integer_mul
- \+/\- *lemma* localization.is_integer_smul
- \+ *lemma* localization.is_unit_comp
- \- *def* localization.le_order_embedding
- \- *def* localization.lift'
- \- *lemma* localization.lift'_apply_coe
- \- *lemma* localization.lift'_coe
- \- *lemma* localization.lift'_comp_of
- \- *lemma* localization.lift'_mk
- \- *lemma* localization.lift'_of
- \- *lemma* localization.lift_apply_coe
- \- *lemma* localization.lift_coe
- \+ *lemma* localization.lift_comp
- \- *lemma* localization.lift_comp_of
- \+ *lemma* localization.lift_eq
- \+ *lemma* localization.lift_eq_iff
- \+ *lemma* localization.lift_id
- \+ *lemma* localization.lift_injective_iff
- \+ *lemma* localization.lift_left_inverse
- \+ *lemma* localization.lift_mk'
- \+ *lemma* localization.lift_mk'_spec
- \- *lemma* localization.lift_of
- \+ *lemma* localization.lift_of_comp
- \+ *lemma* localization.lift_surjective_iff
- \+ *lemma* localization.lift_unique
- \+/\- *def* localization.lin_coe
- \- *lemma* localization.lin_coe_apply
- \- *def* localization.map
- \- *lemma* localization.map_coe
- \- *theorem* localization.map_comap
- \+ *lemma* localization.map_comp
- \+/\- *lemma* localization.map_comp_map
- \- *lemma* localization.map_comp_of
- \+ *lemma* localization.map_eq
- \+/\- *lemma* localization.map_id
- \+ *lemma* localization.map_left_cancel
- \+/\- *lemma* localization.map_map
- \+ *lemma* localization.map_mk'
- \- *lemma* localization.map_of
- \+ *lemma* localization.map_right_cancel
- \+ *lemma* localization.map_units
- \+ *lemma* localization.mem_coe
- \+ *lemma* localization.mk'_add
- \+ *lemma* localization.mk'_eq_iff_eq
- \+ *theorem* localization.mk'_eq_iff_eq_mul
- \+ *lemma* localization.mk'_eq_iff_mk'_eq
- \+ *lemma* localization.mk'_eq_mul_mk'_one
- \+ *lemma* localization.mk'_eq_of_eq
- \+ *lemma* localization.mk'_mul
- \+ *lemma* localization.mk'_mul_cancel_left
- \+ *lemma* localization.mk'_mul_cancel_right
- \+ *lemma* localization.mk'_one
- \+ *lemma* localization.mk'_sec
- \+ *lemma* localization.mk'_self''
- \+ *lemma* localization.mk'_self'
- \+ *lemma* localization.mk'_self
- \+ *lemma* localization.mk'_spec'
- \+ *lemma* localization.mk'_spec
- \- *def* localization.mk
- \- *lemma* localization.mk_eq
- \- *lemma* localization.mk_eq_mul_mk_one
- \- *lemma* localization.mk_mul_cancel_left
- \- *lemma* localization.mk_mul_cancel_right
- \- *lemma* localization.mk_mul_mk
- \- *lemma* localization.mk_self''
- \- *lemma* localization.mk_self'
- \- *lemma* localization.mk_self
- \- *lemma* localization.mul_coe_eq_smul
- \+ *lemma* localization.mul_mk'_eq_mk'_of_mul
- \- *def* localization.non_zero_divisors
- \- *lemma* localization.non_zero_divisors_one_val
- \- *def* localization.of
- \- *lemma* localization.of_add
- \+/\- *lemma* localization.of_id
- \- *lemma* localization.of_is_unit'
- \- *lemma* localization.of_is_unit
- \- *lemma* localization.of_mul
- \- *lemma* localization.of_neg
- \- *lemma* localization.of_one
- \- *lemma* localization.of_pow
- \- *lemma* localization.of_smul
- \- *lemma* localization.of_sub
- \- *lemma* localization.of_zero
- \- *def* localization.r
- \- *theorem* localization.r_of_eq
- \- *theorem* localization.refl
- \+ *lemma* localization.ring_equiv_of_ring_equiv_eq
- \+ *lemma* localization.ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* localization.ring_equiv_of_ring_equiv_eq_map_apply
- \+ *lemma* localization.ring_equiv_of_ring_equiv_mk'
- \+ *lemma* localization.sec_spec'
- \+ *lemma* localization.sec_spec
- \+ *lemma* localization.surj
- \- *theorem* localization.symm
- \+ *lemma* localization.to_map_injective
- \- *def* localization.to_units
- \- *lemma* localization.to_units_coe
- \- *theorem* localization.trans
- \- *def* localization
- \+ *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *def* non_zero_divisors
- \+ *def* ring_hom.to_localization



## [2020-05-22 06:26:36](https://github.com/leanprover-community/mathlib/commit/a012d76)
chore(linear_algebra/projection): use implicit args in lemmas ([#2773](https://github.com/leanprover-community/mathlib/pull/2773))
#### Estimated changes
Modified src/analysis/normed_space/complemented.lean


Modified src/linear_algebra/projection.lean
- \+ *lemma* submodule.linear_proj_of_is_compl_comp_subtype



## [2020-05-22 06:26:34](https://github.com/leanprover-community/mathlib/commit/749e39f)
feat(category_theory): preadditive binary biproducts ([#2747](https://github.com/leanprover-community/mathlib/pull/2747))
This PR introduces "preadditive binary biproducts", which correspond to the second definition of biproducts given in [#2177](https://github.com/leanprover-community/mathlib/pull/2177).
* Preadditive binary biproducts are binary biproducts.
* In a preadditive category, a binary product is a preadditive binary biproduct.
* This directly implies that `AddCommGroup` has preadditive binary biproducts. The existence of binary coproducts in `AddCommGroup` is then a consequence of abstract nonsense.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* category_theory.limits.biprod.fst_add_snd
- \+ *lemma* category_theory.limits.biprod.inl_add_inr
- \+ *lemma* category_theory.limits.biprod.inl_fst
- \+ *lemma* category_theory.limits.biprod.inl_snd
- \+ *lemma* category_theory.limits.biprod.inr_fst
- \+ *lemma* category_theory.limits.biprod.inr_snd
- \+ *lemma* category_theory.limits.biprod.lift_desc
- \+ *lemma* category_theory.limits.biprod.total
- \+ *def* category_theory.limits.has_preadditive_binary_biproduct.of_has_colimit_pair
- \+ *def* category_theory.limits.has_preadditive_binary_biproduct.of_has_limit_pair
- \+ *def* category_theory.limits.has_preadditive_binary_biproducts_of_has_binary_coproducts
- \+ *def* category_theory.limits.has_preadditive_binary_biproducts_of_has_binary_products



## [2020-05-22 05:08:46](https://github.com/leanprover-community/mathlib/commit/5585e3c)
chore(linear_algebra/basic): redefine le on submodule ([#2766](https://github.com/leanprover-community/mathlib/pull/2766))
Previously, to prove an `S \le T`, there would be a coercion in the statement after `intro x`. This fixes that.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/projection.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean




## [2020-05-21 22:53:42](https://github.com/leanprover-community/mathlib/commit/a9960ce)
chore(scripts): update nolints.txt ([#2771](https://github.com/leanprover-community/mathlib/pull/2771))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-21 20:35:43](https://github.com/leanprover-community/mathlib/commit/6c71874)
feat(analysis/normed_space): complemented subspaces ([#2738](https://github.com/leanprover-community/mathlib/pull/2738))
Define complemented subspaces and prove some basic facts.
#### Estimated changes
Added src/analysis/normed_space/complemented.lean
- \+ *lemma* continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range
- \+ *lemma* subspace.closed_complemented_iff_has_closed_compl
- \+ *lemma* subspace.closed_complemented_of_closed_compl
- \+ *lemma* subspace.closed_complemented_of_quotient_finite_dimensional
- \+ *lemma* subspace.coe_continuous_linear_proj_of_closed_compl'
- \+ *lemma* subspace.coe_continuous_linear_proj_of_closed_compl
- \+ *lemma* subspace.coe_prod_equiv_of_closed_compl
- \+ *lemma* subspace.coe_prod_equiv_of_closed_compl_symm
- \+ *def* subspace.linear_proj_of_closed_compl
- \+ *def* subspace.prod_equiv_of_closed_compl

Modified src/linear_algebra/projection.lean
- \+ *lemma* linear_map.ker_id_sub_eq_of_proj

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.closed_complemented_ker_of_right_inverse
- \+ *lemma* continuous_linear_map.ker_cod_restrict
- \+ *lemma* submodule.closed_complemented.has_closed_complement
- \+ *def* submodule.closed_complemented
- \+ *lemma* submodule.closed_complemented_bot
- \+ *lemma* submodule.closed_complemented_top



## [2020-05-21 20:35:41](https://github.com/leanprover-community/mathlib/commit/fd45e28)
fix(*): do not nolint simp_nf ([#2734](https://github.com/leanprover-community/mathlib/pull/2734))
The `nolint simp_nf` for `subgroup.coe_coe` was hiding an actual nontermination issue.  Please just ping me if you're unsure about the `simp_nf` linter.
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* div_zero
- \- *lemma* inv_zero

Modified src/algebra/group_with_zero.lean
- \- *lemma* div_zero'
- \+ *lemma* div_zero
- \- *lemma* inv_zero'
- \+ *lemma* inv_zero

Modified src/group_theory/bundled_subgroup.lean




## [2020-05-21 18:58:04](https://github.com/leanprover-community/mathlib/commit/ec01a0d)
perf(tactic/lint/simp): speed up `simp_comm` linter ([#2760](https://github.com/leanprover-community/mathlib/pull/2760))
This is a fairly unimportant linter, but takes 35% of the linting runtime in my unscientific small-case profiling run.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+/\- *theorem* euclidean_domain.xgcd_aux_rec

Modified src/data/int/gcd.lean
- \+/\- *theorem* nat.xgcd_aux_rec

Modified src/tactic/lint/simp.lean




## [2020-05-21 15:42:46](https://github.com/leanprover-community/mathlib/commit/d532eb6)
feat(order/lattice): sup_left_idem and similar ([#2768](https://github.com/leanprover-community/mathlib/pull/2768))
#### Estimated changes
Modified src/order/lattice.lean
- \+ *lemma* inf_left_idem
- \+ *lemma* inf_right_idem
- \+ *lemma* sup_left_idem
- \+ *lemma* sup_right_idem



## [2020-05-21 07:51:07](https://github.com/leanprover-community/mathlib/commit/951b967)
refactor(data/nat/basic): use function equality for `iterate` lemmas ([#2748](https://github.com/leanprover-community/mathlib/pull/2748))
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/computability/turing_machine.lean


Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.iterate_add
- \+ *theorem* nat.iterate_add_apply
- \+/\- *theorem* nat.iterate_succ'
- \+/\- *theorem* nat.iterate_succ
- \+ *theorem* nat.iterate_succ_apply'
- \+ *theorem* nat.iterate_succ_apply
- \+/\- *theorem* nat.iterate_zero
- \+ *theorem* nat.iterate_zero_apply

Modified src/field_theory/perfect_closure.lean


Modified src/topology/metric_space/contracting.lean




## [2020-05-20 19:37:56](https://github.com/leanprover-community/mathlib/commit/a540d79)
chore(archive/sensitivity): Clean up function coercion in sensitivity proof (depends on [#2756](https://github.com/leanprover-community/mathlib/pull/2756)) ([#2758](https://github.com/leanprover-community/mathlib/pull/2758))
This formalizes the proof of an old conjecture: `is_awesome Gabriel`. I also took the opportunity to remove type class struggling, which I think is related to the proof of `is_awesome Floris`.
I think @jcommelin should also update this sensitivity file to use his sum notations if applicable.
#### Estimated changes
Modified archive/sensitivity.lean
- \- *def* V.add_comm_monoid
- \- *def* V.add_comm_semigroup
- \- *def* V.has_add
- \- *def* V.has_scalar
- \- *def* V.module



## [2020-05-20 18:10:11](https://github.com/leanprover-community/mathlib/commit/3c9bf6b)
chore(scripts): update nolints.txt ([#2763](https://github.com/leanprover-community/mathlib/pull/2763))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-20 15:35:04](https://github.com/leanprover-community/mathlib/commit/d6420bd)
feat(ring_theory/principal_ideal_domain): definition of principal submodule ([#2761](https://github.com/leanprover-community/mathlib/pull/2761))
This PR generalizes the definition of principal ideals to principal submodules. It turns out that it's essentially enough to replace `ideal R` with `submodule R M` in the relevant places. With this change, it's possible to talk about principal fractional ideals (although that development will have to wait [#2714](https://github.com/leanprover-community/mathlib/pull/2714) gets merged).
Since the PR already changes the variables used in this file, I took the opportunity to rename them so `[ring α]` becomes `[ring R]`.
#### Estimated changes
Modified src/ring_theory/principal_ideal_domain.lean
- \- *lemma* ideal.is_principal.eq_bot_iff_generator_eq_zero
- \- *lemma* ideal.is_principal.generator_mem
- \- *lemma* ideal.is_principal.mem_iff_generator_dvd
- \- *lemma* ideal.is_principal.span_singleton_generator
- \+/\- *lemma* is_prime.to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+/\- *lemma* principal_ideal_domain.associates_irreducible_iff_prime
- \+/\- *lemma* principal_ideal_domain.factors_decreasing
- \+/\- *lemma* principal_ideal_domain.factors_spec
- \+/\- *lemma* principal_ideal_domain.irreducible_iff_prime
- \+/\- *lemma* principal_ideal_domain.is_maximal_of_irreducible
- \+ *lemma* submodule.is_principal.eq_bot_iff_generator_eq_zero
- \+ *lemma* submodule.is_principal.generator_mem
- \+ *lemma* submodule.is_principal.mem_iff_eq_smul_generator
- \+ *lemma* submodule.is_principal.mem_iff_generator_dvd
- \+ *lemma* submodule.is_principal.span_singleton_generator



## [2020-05-20 15:35:02](https://github.com/leanprover-community/mathlib/commit/4c3e1a9)
feat(algebra): the R-module structure on S-linear maps, for S an R-algebra ([#2759](https://github.com/leanprover-community/mathlib/pull/2759))
I couldn't find this already in mathlib, but perhaps I've missed it.
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *def* linear_map_algebra_has_scalar
- \+ *def* linear_map_algebra_module



## [2020-05-20 15:34:59](https://github.com/leanprover-community/mathlib/commit/6df77a6)
chore(*): update to Lean 3.14.0 ([#2756](https://github.com/leanprover-community/mathlib/pull/2756))
This is an optimistic PR, betting *nothing* will break when moving to Lean 3.14.0.
#### Estimated changes
Modified leanpkg.toml




## [2020-05-20 15:34:58](https://github.com/leanprover-community/mathlib/commit/164c2e3)
chore(category_theory): attributes and a transport proof ([#2751](https://github.com/leanprover-community/mathlib/pull/2751))
A couple of cleanups, modified a proof or two so that `@[simps]` can be used, which let me clean up some other proofs. Also a proof that we can transfer that `F` preserves the limit `K` along an isomorphism in `K`.
(Preparation for some PRs from my topos project)
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+/\- *def* category_theory.equivalence.refl
- \+/\- *def* category_theory.equivalence.symm

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/preserves.lean
- \+ *def* category_theory.limits.preserves_limit_of_iso

Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* category_theory.nat_iso.hom_inv_id_app
- \+/\- *lemma* category_theory.nat_iso.inv_hom_id_app
- \+/\- *lemma* category_theory.nat_iso.of_components.app
- \+/\- *lemma* category_theory.nat_iso.of_components.hom_app
- \+/\- *lemma* category_theory.nat_iso.of_components.inv_app
- \+/\- *def* category_theory.nat_iso.of_components



## [2020-05-20 12:01:53](https://github.com/leanprover-community/mathlib/commit/ab5d0f1)
feat(category_theory/binary_products): some product lemmas and their dual ([#2752](https://github.com/leanprover-community/mathlib/pull/2752))
A bunch of lemmas about binary products.
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.braid_natural
- \+/\- *lemma* category_theory.limits.coprod.inl_map
- \+/\- *lemma* category_theory.limits.coprod.inr_map
- \+ *lemma* category_theory.limits.coprod.map_desc
- \+ *lemma* category_theory.limits.coprod_desc_inl_inr
- \+ *lemma* category_theory.limits.coprod_map_comp_id
- \+ *lemma* category_theory.limits.coprod_map_id_comp
- \+ *lemma* category_theory.limits.coprod_map_id_id
- \+ *lemma* category_theory.limits.coprod_map_map
- \+ *lemma* category_theory.limits.prod.lift_map
- \+/\- *lemma* category_theory.limits.prod.map_fst
- \+/\- *lemma* category_theory.limits.prod.map_snd
- \+/\- *lemma* category_theory.limits.prod.symmetry'
- \+/\- *lemma* category_theory.limits.prod.symmetry
- \+ *def* category_theory.limits.prod_functor_left_comp
- \+ *lemma* category_theory.limits.prod_left_unitor_hom_naturality
- \+ *lemma* category_theory.limits.prod_left_unitor_inv_naturality
- \+ *lemma* category_theory.limits.prod_lift_fst_snd
- \+ *lemma* category_theory.limits.prod_map_comp_id
- \+ *lemma* category_theory.limits.prod_map_id_comp
- \+ *lemma* category_theory.limits.prod_map_id_id
- \+ *lemma* category_theory.limits.prod_map_map
- \+ *lemma* category_theory.limits.prod_right_unitor_hom_naturality
- \+ *lemma* category_theory.limits.prod_right_unitor_inv_naturality



## [2020-05-20 11:03:44](https://github.com/leanprover-community/mathlib/commit/1f00282)
docs(linear_algebra/sesquilinear_form): correct module docs ([#2757](https://github.com/leanprover-community/mathlib/pull/2757))
@PatrickMassot mentioned that the docs for `sesquilinear_form` mention bilinear forms instead in a few places. This PR corrects them to use "sesquilinear form" everywhere.
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean




## [2020-05-20 06:18:22](https://github.com/leanprover-community/mathlib/commit/cbe80ed)
feat(linear_algebra/projection): projection to a subspace ([#2739](https://github.com/leanprover-community/mathlib/pull/2739))
Define equivalence between complement subspaces and projections.
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* submodule.add_mem_iff_left
- \+/\- *lemma* submodule.add_mem_iff_right

Modified src/data/prod.lean
- \+ *lemma* prod.fst_eq_iff
- \+ *lemma* prod.snd_eq_iff

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_of_eq_apply
- \+ *theorem* linear_equiv.coe_of_top_symm_apply
- \+ *def* linear_equiv.of_eq
- \+ *lemma* linear_equiv.of_eq_symm
- \+/\- *theorem* linear_equiv.of_top_symm_apply
- \+ *lemma* linear_map.coe_quotient_inf_to_sup_quotient
- \+ *theorem* linear_map.map_eq_top_iff
- \+ *theorem* linear_map.map_le_map_iff'
- \+/\- *theorem* linear_map.map_le_map_iff
- \+ *lemma* linear_map.quot_ker_equiv_range_apply_mk
- \+ *lemma* linear_map.quot_ker_equiv_range_symm_apply_image
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_apply_mk
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left
- \+ *lemma* linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right
- \+ *lemma* linear_map.range_range_restrict
- \+ *lemma* submodule.coe_quot_equiv_of_eq_bot_symm
- \+ *theorem* submodule.map_mkq_eq_top
- \+ *theorem* submodule.mem_left_iff_eq_zero_of_disjoint
- \+ *theorem* submodule.mem_right_iff_eq_zero_of_disjoint
- \+ *def* submodule.quot_equiv_of_eq_bot
- \+ *lemma* submodule.quot_equiv_of_eq_bot_apply_mk
- \+ *lemma* submodule.quot_equiv_of_eq_bot_symm_apply
- \- *lemma* submodule.range_range_restrict

Modified src/linear_algebra/basis.lean
- \+ *lemma* submodule.exists_is_compl

Modified src/linear_algebra/dimension.lean


Added src/linear_algebra/projection.lean
- \+ *lemma* linear_map.is_compl_of_proj
- \+ *lemma* linear_map.linear_proj_of_is_compl_of_proj
- \+ *lemma* submodule.coe_is_compl_equiv_proj_apply
- \+ *lemma* submodule.coe_is_compl_equiv_proj_symm_apply
- \+ *lemma* submodule.coe_prod_equiv_of_is_compl'
- \+ *lemma* submodule.coe_prod_equiv_of_is_compl
- \+ *def* submodule.is_compl_equiv_proj
- \+ *def* submodule.linear_proj_of_is_compl
- \+ *lemma* submodule.linear_proj_of_is_compl_apply_eq_zero_iff
- \+ *lemma* submodule.linear_proj_of_is_compl_apply_left
- \+ *lemma* submodule.linear_proj_of_is_compl_apply_right'
- \+ *lemma* submodule.linear_proj_of_is_compl_apply_right
- \+ *lemma* submodule.linear_proj_of_is_compl_idempotent
- \+ *lemma* submodule.linear_proj_of_is_compl_ker
- \+ *lemma* submodule.linear_proj_of_is_compl_range
- \+ *lemma* submodule.mk_quotient_equiv_of_is_compl_apply
- \+ *def* submodule.prod_equiv_of_is_compl
- \+ *lemma* submodule.prod_equiv_of_is_compl_symm_apply_fst_eq_zero
- \+ *lemma* submodule.prod_equiv_of_is_compl_symm_apply_left
- \+ *lemma* submodule.prod_equiv_of_is_compl_symm_apply_right
- \+ *lemma* submodule.prod_equiv_of_is_compl_symm_apply_snd_eq_zero
- \+ *def* submodule.quotient_equiv_of_is_compl
- \+ *lemma* submodule.quotient_equiv_of_is_compl_apply_mk_coe
- \+ *lemma* submodule.quotient_equiv_of_is_compl_symm_apply



## [2020-05-19 22:34:25](https://github.com/leanprover-community/mathlib/commit/3c1f9f9)
feat(data/nat/choose): sum_range_choose_halfway ([#2688](https://github.com/leanprover-community/mathlib/pull/2688))
This is a lemma on the way to proving that the product of primes less than `n` is less than `4 ^ n`, which is itself a lemma in Bertrand's postulate.
The lemma itself is of dubious significance, but it will eventually be necessary for Bertrand, and I want to commit early and often. Brief discussion of this decision at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619722 .
This is my second PR to mathlib; the code is definitely verbose and poorly structured, but I don't know how to fix it. I'm expecting almost no lines of the original to remain by the end of this!
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/nat/choose.lean
- \+ *lemma* sum_range_choose_halfway



## [2020-05-19 18:38:27](https://github.com/leanprover-community/mathlib/commit/e3aca90)
feat(logic/basic): spaces with a zero or a one are nonempty ([#2743](https://github.com/leanprover-community/mathlib/pull/2743))
Register instances that a space with a zero or a one is not empty, with low priority as we don't want to embark on a search for a zero or a one if this is not necessary.
Discussion on Zulip at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/inhabited.20and.20nonempty.20instances/near/198030072
#### Estimated changes
Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed_space/banach.lean


Modified src/group_theory/bundled_subgroup.lean


Modified src/group_theory/sylow.lean


Modified src/logic/basic.lean




## [2020-05-19 17:00:43](https://github.com/leanprover-community/mathlib/commit/607767e)
feat(algebra/big_operators): reversing an interval doesn't change the product ([#2740](https://github.com/leanprover-community/mathlib/pull/2740))
Also use Gauss summation in the Gauss summation formula.
Inspired by [#2688](https://github.com/leanprover-community/mathlib/pull/2688)
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_Ico_reflect
- \+ *lemma* finset.prod_range_reflect
- \+ *lemma* finset.sum_Ico_reflect
- \+ *lemma* finset.sum_range_reflect

Modified src/data/finset.lean
- \+ *lemma* finset.Ico.image_const_sub
- \+ *lemma* finset.range_image_pred_top_sub



## [2020-05-19 15:54:58](https://github.com/leanprover-community/mathlib/commit/62c22da)
fix(ci): replace 2 old secret names ([#2744](https://github.com/leanprover-community/mathlib/pull/2744))
[`lean-3.13.2`](https://github.com/leanprover-community/mathlib/tree/lean-3.13.2) is out of date, since I missed two instances of `DEPLOY_NIGHTLY_GITHUB_TOKEN` in [#2737](https://github.com/leanprover-community/mathlib/pull/2737).
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-05-19 11:50:10](https://github.com/leanprover-community/mathlib/commit/1e18512)
chore(*): remove non-canonical `option.decidable_eq_none` instance ([#2741](https://github.com/leanprover-community/mathlib/pull/2741))
I also removed the hack in `ulower.primcodable` where I had to use `none = o` instead of `o = none`.
#### Estimated changes
Modified src/computability/primrec.lean


Modified src/data/list/sigma.lean


Modified src/data/option/defs.lean
- \+ *def* option.decidable_eq_none

Modified src/data/seq/seq.lean




## [2020-05-19 09:58:39](https://github.com/leanprover-community/mathlib/commit/93b41e5)
fix(*): put headings in multiline module docs on their own lines ([#2742](https://github.com/leanprover-community/mathlib/pull/2742))
found using regex: `/-! #([^-/])*$`.
These don't render correctly in the mathlib docs. Module doc strings that consist of a heading on its own line are OK so I haven't changed them.
I also moved some descriptive text from copyright headers to module docs, or removed such text if there was already a module doc string.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/category_theory/shift.lean


Modified src/computability/turing_machine.lean


Modified src/data/matrix/basic.lean


Modified src/data/set/basic.lean


Modified src/data/set/function.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/extr.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/core.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/local_extr.lean


Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/uniform_space/cauchy.lean




## [2020-05-19 09:58:37](https://github.com/leanprover-community/mathlib/commit/3d948bf)
feat(analysis/normed_space): interior of `closed_ball` etc ([#2723](https://github.com/leanprover-community/mathlib/pull/2723))
* define `sphere x r`
* prove formulas for `interior`, `closure`, and `frontier` of open and closed balls in real normed vector spaces.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *theorem* closure_ball
- \+ *theorem* frontier_ball
- \+ *theorem* frontier_closed_ball'
- \+ *theorem* frontier_closed_ball
- \+ *theorem* interior_closed_ball'
- \+ *theorem* interior_closed_ball
- \+/\- *lemma* submodule.eq_top_of_nonempty_interior

Modified src/topology/basic.lean
- \+ *lemma* preimage_interior_subset_interior_preimage

Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.ball_eq_empty_iff_nonpos
- \+ *theorem* metric.ball_subset_interior_closed_ball
- \+ *theorem* metric.ball_union_sphere
- \+ *theorem* metric.closed_ball_diff_ball
- \+ *theorem* metric.closed_ball_diff_sphere
- \+ *theorem* metric.closed_ball_eq_empty_iff_neg
- \+ *lemma* metric.closed_ball_zero
- \+ *theorem* metric.closure_ball_subset_closed_ball
- \+ *theorem* metric.frontier_ball_subset_sphere
- \+ *theorem* metric.frontier_closed_ball_subset_sphere
- \+ *def* metric.sphere
- \+ *theorem* metric.sphere_disjoint_ball
- \+ *theorem* metric.sphere_subset_closed_ball
- \+ *theorem* metric.sphere_union_ball

Modified src/topology/metric_space/closeds.lean




## [2020-05-19 08:28:09](https://github.com/leanprover-community/mathlib/commit/f2cb546)
fix(ci): setup git before nolints, rename secret ([#2737](https://github.com/leanprover-community/mathlib/pull/2737))
Oops, I broke the update nolints step on master. This should fix it.
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/deploy_docs.sh


Modified scripts/update_nolints.sh




## [2020-05-19 08:28:08](https://github.com/leanprover-community/mathlib/commit/3968f7f)
feat(linear_algebra): equiv_of_is_basis' and module.fintype_of_fintype ([#2735](https://github.com/leanprover-community/mathlib/pull/2735))
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *def* equiv_of_is_basis'
- \+/\- *def* equiv_of_is_basis
- \+ *def* module.fintype_of_fintype



## [2020-05-19 08:28:05](https://github.com/leanprover-community/mathlib/commit/80b7f97)
feat(tactic/localized): fail if unused locale is open ([#2718](https://github.com/leanprover-community/mathlib/pull/2718))
This is more in line with the behavior of `open`.
Closes [#2702](https://github.com/leanprover-community/mathlib/pull/2702)
#### Estimated changes
Modified src/measure_theory/simple_func_dense.lean


Modified src/tactic/localized.lean


Modified test/localized/localized.lean




## [2020-05-19 08:28:03](https://github.com/leanprover-community/mathlib/commit/3ba7d12)
feat(algebra): obtaining algebraic classes through in/surjective maps ([#2638](https://github.com/leanprover-community/mathlib/pull/2638))
This is needed for the definition of Witt vectors.
#### Estimated changes
Added src/algebra/inj_surj.lean
- \+ *def* comm_group_of_injective
- \+ *def* comm_group_of_surjective
- \+ *def* comm_monoid_of_injective
- \+ *def* comm_monoid_of_surjective
- \+ *def* comm_ring_of_injective
- \+ *def* comm_ring_of_surjective
- \+ *def* comm_semigroup_of_injective
- \+ *def* comm_semigroup_of_surjective
- \+ *def* comm_semiring_of_injective
- \+ *def* comm_semiring_of_surjective
- \+ *def* group_of_injective
- \+ *def* group_of_surjective
- \+ *def* monoid_of_injective
- \+ *def* monoid_of_surjective
- \+ *def* ring_of_injective
- \+ *def* ring_of_surjective
- \+ *def* semigroup_of_injective
- \+ *def* semigroup_of_surjective
- \+ *def* semiring_of_injective
- \+ *def* semiring_of_surjective



## [2020-05-19 07:10:15](https://github.com/leanprover-community/mathlib/commit/52aa128)
feat(data/equiv): add add_equiv.to_multiplicative ([#2732](https://github.com/leanprover-community/mathlib/pull/2732))
We already have `add_monoid_hom.to_multiplicative`. This adds `add_equiv.to_multiplicative`.
It is placed in `data/equiv/mul_add.lean` because `data/equiv/mul_add.lean` already imports `algebra/group/type_tags.lean`.
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *def* add_equiv.to_multiplicative
- \+ *def* mul_equiv.to_additive



## [2020-05-19 06:13:04](https://github.com/leanprover-community/mathlib/commit/906220c)
feat(topology/bounded_continuous_function): Normed algebra of bounded continuous functions ([#2722](https://github.com/leanprover-community/mathlib/pull/2722))
The space `C(α, γ)` of bounded continuous functions into a normed algebra γ is a normed algebra.  The space of bounded continuous functions into a normed 𝕜-space is a `C(α, 𝕜)`-module.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/topology/bounded_continuous_function.lean
- \+ *def* bounded_continuous_function.C
- \+ *lemma* bounded_continuous_function.norm_smul_le



## [2020-05-19 03:26:24](https://github.com/leanprover-community/mathlib/commit/01efaeb)
feat(ci): run lint and tests in parallel ([#2736](https://github.com/leanprover-community/mathlib/pull/2736))
Actions doesn't let us run *steps* in parallel, but we can run *jobs* in parallel. The lint and test jobs are part of the same *workflow*. Understanding Actions terminology is half the battle.
#### Estimated changes
Modified .github/workflows/build.yml


Modified bors.toml


Modified scripts/deploy_docs.sh




## [2020-05-18 18:12:30](https://github.com/leanprover-community/mathlib/commit/f01260a)
feat(algebra/char_p): eq_iff_modeq_int ([#2731](https://github.com/leanprover-community/mathlib/pull/2731))
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* eq_iff_modeq_int



## [2020-05-18 16:18:17](https://github.com/leanprover-community/mathlib/commit/9d762df)
chore(scripts): update nolints.txt ([#2733](https://github.com/leanprover-community/mathlib/pull/2733))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-18 13:38:47](https://github.com/leanprover-community/mathlib/commit/ff3130d)
feat(topology/constructions): topology on ulift ([#2716](https://github.com/leanprover-community/mathlib/pull/2716))
#### Estimated changes
Modified src/topology/constructions.lean
- \+ *lemma* continuous_ulift_down
- \+ *lemma* continuous_ulift_up

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.{u



## [2020-05-18 13:38:45](https://github.com/leanprover-community/mathlib/commit/4026bd8)
feat(category_theory/full_subcategory): induced category from a groupoid is a groupoid ([#2715](https://github.com/leanprover-community/mathlib/pull/2715))
Also some minor cleanup to the same file.
#### Estimated changes
Modified src/category_theory/full_subcategory.lean
- \- *lemma* category_theory.induced_functor.hom
- \- *lemma* category_theory.induced_functor.obj
- \+/\- *def* category_theory.induced_functor



## [2020-05-18 13:38:43](https://github.com/leanprover-community/mathlib/commit/2fa1d7c)
Revert "fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))" ([#2713](https://github.com/leanprover-community/mathlib/pull/2713))
These are good simp lemmas: they push things into a proof-irrelevant position.
This reverts commit 5a309a3aa30fcec122a26f379f05b466ee46fc7a.
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.eq_to_hom_app
- \+/\- *lemma* category_theory.eq_to_hom_map
- \+/\- *lemma* category_theory.eq_to_iso_map



## [2020-05-18 13:38:41](https://github.com/leanprover-community/mathlib/commit/8b42245)
refactor(algebra): merge init_.algebra into algebra ([#2707](https://github.com/leanprover-community/mathlib/pull/2707))
This is a big refactor PR. It depends on [#2697](https://github.com/leanprover-community/mathlib/pull/2697), which brings in the algebra hierarchy without any change to the file structure. This PR merges `init_.algebra.group` into `algebra.group` and so on for the rest of the algebraic hierarchy.
#### Estimated changes
Modified archive/100-theorems-list/42_inverse_triangle_sum.lean


Modified archive/sensitivity.lean


Modified scripts/nolints.txt


Modified src/algebra/char_zero.lean


Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/field.lean
- \+/\- *lemma* add_div'
- \+ *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* div_add'
- \+ *lemma* div_add_div
- \+ *lemma* div_add_div_same
- \+ *lemma* div_div_div_div_eq
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* div_eq_one_iff_eq
- \+ *lemma* div_helper
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_mul_div
- \+ *lemma* div_mul_eq_div_mul_one_div
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* div_mul_eq_mul_div_comm
- \+ *lemma* div_mul_left
- \+ *lemma* div_mul_right
- \+ *lemma* div_neg_eq_neg_div
- \+ *lemma* div_one
- \+ *lemma* div_self
- \+/\- *lemma* div_sub'
- \+ *lemma* div_sub_div
- \+ *lemma* div_sub_div_same
- \+ *lemma* div_zero
- \+ *lemma* division_def
- \+ *lemma* division_ring.mul_ne_zero
- \+ *lemma* division_ring.one_div_mul_one_div
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* eq_div_of_mul_eq
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* eq_one_div_of_mul_eq_one
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \+ *lemma* inv_eq_one_div
- \+ *lemma* inv_inv'
- \+ *lemma* inv_mul_cancel
- \+ *lemma* inv_ne_zero
- \+/\- *theorem* inv_one
- \+ *lemma* inv_zero
- \- *lemma* is_ring_hom.injective
- \- *lemma* is_ring_hom.map_div
- \- *lemma* is_ring_hom.map_eq_zero
- \- *lemma* is_ring_hom.map_inv
- \- *lemma* is_ring_hom.map_ne_zero
- \+/\- *lemma* mul_div_assoc'
- \+ *lemma* mul_div_assoc
- \+ *lemma* mul_div_cancel'
- \+ *lemma* mul_div_cancel
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_mul_left
- \+ *lemma* mul_div_mul_right
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \+ *lemma* mul_eq_of_eq_div
- \+ *lemma* mul_inv'
- \+ *lemma* mul_inv_cancel
- \+ *lemma* mul_mul_div
- \+ *lemma* mul_ne_zero_comm
- \+ *lemma* mul_one_div_cancel
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \+/\- *lemma* neg_div'
- \+ *lemma* neg_div
- \+ *lemma* neg_div_neg_eq
- \+ *lemma* one_div_add_one_div
- \+ *lemma* one_div_div
- \+ *lemma* one_div_eq_inv
- \+ *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_mul_cancel
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_ne_zero
- \+ *lemma* one_div_neg_eq_neg_one_div
- \+ *lemma* one_div_neg_one_eq_neg_one
- \+ *lemma* one_div_one
- \+ *lemma* one_div_one_div
- \+ *lemma* one_inv_eq
- \+/\- *lemma* sub_div'
- \+ *lemma* zero_div

Modified src/algebra/floor.lean


Modified src/algebra/free.lean


Modified src/algebra/gcd_domain.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* add_add_sub_cancel
- \+ *lemma* add_eq_of_eq_sub'
- \+ *lemma* add_eq_of_eq_sub
- \+ *lemma* add_sub
- \+ *lemma* add_sub_add_left_eq_sub
- \+ *lemma* add_sub_add_right_eq_sub
- \+ *lemma* add_sub_assoc
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* add_sub_cancel'_right
- \+ *lemma* add_sub_cancel
- \+ *lemma* add_sub_comm
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* bit0_zero
- \+/\- *lemma* bit1_zero
- \+ *lemma* eq_add_of_sub_eq'
- \+ *lemma* eq_add_of_sub_eq
- \+ *lemma* eq_inv_mul_of_mul_eq
- \+ *lemma* eq_inv_of_eq_inv
- \+ *lemma* eq_inv_of_mul_eq_one
- \+ *lemma* eq_mul_inv_of_mul_eq
- \+ *lemma* eq_mul_of_inv_mul_eq
- \+ *lemma* eq_mul_of_mul_inv_eq
- \+ *def* eq_of_add_eq_add_left
- \+ *def* eq_of_add_eq_add_right
- \+ *lemma* eq_of_sub_eq_zero
- \+ *lemma* eq_sub_of_add_eq'
- \+ *lemma* eq_sub_of_add_eq
- \+ *lemma* group.mul_left_cancel
- \+ *lemma* group.mul_right_cancel
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* inv_inj
- \+ *lemma* inv_inv
- \+/\- *lemma* inv_involutive
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_cancel_right
- \+ *lemma* inv_mul_eq_of_eq_mul
- \+ *def* inv_mul_self
- \+/\- *lemma* inv_unique
- \+/\- *theorem* left_inverse_add_left_sub
- \+/\- *theorem* left_inverse_add_right_neg_add
- \+/\- *theorem* left_inverse_neg_add_add_right
- \+/\- *theorem* left_inverse_sub_add_left
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_eq_of_eq_inv_mul
- \+ *lemma* mul_eq_of_eq_mul_inv
- \+ *lemma* mul_inv
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_eq_of_eq_mul
- \+ *lemma* mul_inv_rev
- \+ *def* mul_inv_self
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *lemma* mul_left_comm
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_left_injective
- \+ *lemma* mul_left_inv
- \+/\- *theorem* mul_mul_mul_comm
- \+ *lemma* mul_one
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_right_cancel_iff
- \+ *lemma* mul_right_comm
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_right_injective
- \+ *lemma* mul_right_inv
- \+/\- *theorem* neg_add'
- \+ *lemma* neg_add_eq_sub
- \+ *lemma* neg_neg_sub_neg
- \+ *lemma* neg_sub
- \+/\- *lemma* neg_sub_neg
- \+ *lemma* one_inv
- \+ *lemma* one_mul
- \+ *lemma* sub_add
- \+/\- *lemma* sub_add_add_cancel
- \+ *lemma* sub_add_cancel
- \+ *lemma* sub_add_eq_add_sub
- \+ *lemma* sub_add_eq_sub_sub
- \+ *lemma* sub_add_eq_sub_sub_swap
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* sub_add_sub_cancel
- \+ *lemma* sub_eq_add_neg
- \+/\- *lemma* sub_eq_neg_add
- \+ *lemma* sub_eq_of_eq_add'
- \+ *lemma* sub_eq_of_eq_add
- \+ *lemma* sub_eq_sub_add_sub
- \+/\- *lemma* sub_eq_sub_iff_add_eq_add
- \+/\- *lemma* sub_eq_sub_iff_sub_eq_sub
- \+ *lemma* sub_eq_zero_iff_eq
- \+ *lemma* sub_eq_zero_of_eq
- \+ *lemma* sub_ne_zero_of_ne
- \+ *lemma* sub_neg_eq_add
- \+/\- *lemma* sub_right_comm
- \+ *lemma* sub_self
- \+ *lemma* sub_sub
- \+/\- *lemma* sub_sub_cancel
- \+ *lemma* sub_sub_self
- \+/\- *lemma* sub_sub_sub_cancel_left
- \+/\- *lemma* sub_sub_sub_cancel_right
- \+ *lemma* sub_zero
- \+ *lemma* zero_sub

Modified src/algebra/group/conj.lean


Modified src/algebra/group/default.lean


Modified src/algebra/group/hom.lean
- \- *lemma* add_monoid_hom.coe_mul_left
- \- *def* add_monoid_hom.mul_left
- \- *def* add_monoid_hom.mul_right
- \- *lemma* add_monoid_hom.mul_right_apply

Deleted src/algebra/group/is_unit.lean
- \- *lemma* is_unit.coe_lift_right
- \- *lemma* is_unit.lift_right_inv_mul
- \- *lemma* is_unit.map
- \- *theorem* is_unit.mul_left_inj
- \- *lemma* is_unit.mul_lift_right_inv
- \- *theorem* is_unit.mul_right_inj
- \- *def* is_unit
- \- *theorem* is_unit_iff_exists_inv'
- \- *theorem* is_unit_iff_exists_inv
- \- *theorem* is_unit_nat
- \- *theorem* is_unit_of_mul_eq_one
- \- *theorem* is_unit_of_mul_is_unit_left
- \- *theorem* is_unit_of_mul_is_unit_right
- \- *theorem* is_unit_one
- \- *lemma* is_unit_unit
- \- *theorem* units.is_unit_mul_units

Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean
- \+/\- *def* divp
- \+/\- *theorem* divp_assoc
- \+/\- *theorem* divp_divp_eq_divp_mul
- \+/\- *theorem* divp_eq_iff_mul_eq
- \+/\- *theorem* divp_eq_one_iff_eq
- \+/\- *theorem* divp_inv
- \+/\- *theorem* divp_left_inj
- \+/\- *theorem* divp_mul_cancel
- \+/\- *theorem* divp_one
- \+/\- *theorem* divp_self
- \+ *theorem* is_unit.mul_left_inj
- \+ *theorem* is_unit.mul_right_inj
- \+ *def* is_unit
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_of_mul_eq_one
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* is_unit_one
- \+ *lemma* is_unit_unit
- \+/\- *theorem* mul_divp_cancel
- \- *theorem* nat.add_units_eq_zero
- \- *theorem* nat.units_eq_one
- \+/\- *theorem* one_divp
- \- *lemma* units.coe_val_hom
- \+ *theorem* units.is_unit_mul_units
- \- *def* units.val_hom

Modified src/algebra/group/units_hom.lean
- \+ *lemma* is_unit.coe_lift_right
- \+ *lemma* is_unit.lift_right_inv_mul
- \+ *lemma* is_unit.map
- \+ *lemma* is_unit.mul_lift_right_inv

Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power.lean


Modified src/algebra/group_ring_action.lean


Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* div_eq_div_iff
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff

Modified src/algebra/lie_algebra.lean


Modified src/algebra/opposites.lean


Modified src/algebra/ordered_field.lean
- \+ *lemma* abs_div
- \+/\- *lemma* abs_inv
- \+ *lemma* abs_one_div
- \+ *lemma* add_halves
- \+ *lemma* add_midpoint
- \+ *lemma* add_self_div_two
- \+/\- *lemma* div_le_div_of_le_left
- \+ *lemma* div_le_div_of_le_of_neg
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \+ *lemma* div_le_div_of_le_of_pos
- \+ *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* div_le_of_mul_le_of_neg
- \+ *lemma* div_lt_div_of_lt_of_neg
- \+ *lemma* div_lt_div_of_lt_of_pos
- \+ *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \+ *lemma* div_lt_div_of_pos_of_lt_of_pos
- \+ *lemma* div_lt_of_mul_gt_of_neg
- \+ *lemma* div_lt_of_mul_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \+ *lemma* div_neg_of_neg_of_pos
- \+ *lemma* div_neg_of_pos_of_neg
- \+/\- *lemma* div_nonneg'
- \+ *lemma* div_nonneg_of_nonneg_of_pos
- \+ *lemma* div_nonneg_of_nonpos_of_neg
- \+ *lemma* div_nonpos_of_nonneg_of_neg
- \+ *lemma* div_nonpos_of_nonpos_of_pos
- \+ *lemma* div_pos_of_neg_of_neg
- \+ *lemma* div_pos_of_pos_of_pos
- \+ *lemma* div_two_lt_of_pos
- \+ *lemma* div_two_sub_self
- \+ *lemma* exists_add_lt_and_pos_of_lt
- \+ *lemma* ge_of_forall_ge_sub
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* inv_le_one
- \+/\- *lemma* inv_lt_one
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+ *lemma* le_div_of_mul_le
- \+ *lemma* le_mul_of_div_le
- \+ *lemma* le_mul_of_ge_one_left
- \+ *lemma* le_mul_of_ge_one_right
- \+ *lemma* le_of_one_div_le_one_div
- \+ *lemma* le_of_one_div_le_one_div_of_neg
- \+ *lemma* le_of_one_le_div
- \+ *lemma* lt_div_of_mul_lt
- \+ *lemma* lt_mul_of_gt_one_right
- \+ *lemma* lt_of_one_div_lt_one_div
- \+ *lemma* lt_of_one_div_lt_one_div_of_neg
- \+ *lemma* lt_of_one_lt_div
- \+ *lemma* mul_le_mul_of_mul_div_le
- \+ *lemma* mul_le_of_div_le_of_neg
- \+ *lemma* mul_le_of_le_div
- \+ *lemma* mul_lt_of_gt_div_of_neg
- \+ *lemma* mul_lt_of_lt_div
- \+/\- *lemma* mul_self_inj_of_nonneg
- \+ *lemma* mul_sub_mul_div_mul_neg
- \+ *lemma* mul_sub_mul_div_mul_nonpos
- \+ *lemma* mul_zero_lt_mul_inv_of_neg
- \+ *lemma* mul_zero_lt_mul_inv_of_pos
- \- *lemma* nat.inv_pos_of_nat
- \- *lemma* nat.one_div_le_one_div
- \- *lemma* nat.one_div_lt_one_div
- \- *lemma* nat.one_div_pos_of_nat
- \+ *lemma* neg_of_one_div_neg
- \+ *lemma* one_div_le_neg_one
- \+ *lemma* one_div_le_of_one_div_le_of_neg
- \+ *lemma* one_div_le_of_one_div_le_of_pos
- \+ *lemma* one_div_le_one_div_of_le
- \+ *lemma* one_div_le_one_div_of_le_of_neg
- \+ *lemma* one_div_lt_neg_one
- \+ *lemma* one_div_lt_one_div_of_lt
- \+ *lemma* one_div_lt_one_div_of_lt_of_neg
- \+ *lemma* one_div_neg_of_neg
- \+ *lemma* one_div_pos_of_pos
- \+ *lemma* one_le_div_of_le
- \+/\- *lemma* one_le_inv
- \+ *lemma* one_le_one_div
- \+ *lemma* one_lt_div_of_lt
- \+ *lemma* one_lt_one_div
- \+ *lemma* pos_of_one_div_pos
- \+ *lemma* sub_self_div_two

Modified src/algebra/ordered_group.lean
- \+ *def* abs
- \+ *lemma* abs_abs
- \+ *lemma* abs_add_le_abs_add_abs
- \+ *lemma* abs_add_three
- \+ *lemma* abs_by_cases
- \+ *lemma* abs_le_of_le_of_neg_le
- \+ *lemma* abs_lt_of_lt_of_neg_lt
- \+ *lemma* abs_neg
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_of_neg
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_of_nonpos
- \+ *lemma* abs_of_pos
- \+ *lemma* abs_pos_of_ne_zero
- \+ *lemma* abs_pos_of_neg
- \+ *lemma* abs_pos_of_pos
- \+ *lemma* abs_sub
- \+ *lemma* abs_sub_abs_le_abs_sub
- \+ *lemma* abs_sub_le
- \+ *lemma* abs_zero
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \+ *lemma* add_le_add
- \+ *lemma* add_le_add_left
- \+ *lemma* add_le_add_right
- \+ *lemma* add_le_add_three
- \+/\- *lemma* add_le_iff_nonpos_left
- \+/\- *lemma* add_le_iff_nonpos_right
- \+ *lemma* add_le_of_le_neg_add
- \+ *lemma* add_le_of_le_of_nonpos
- \+ *lemma* add_le_of_le_sub_left
- \+ *lemma* add_le_of_le_sub_right
- \+ *lemma* add_le_of_nonpos_of_le
- \+ *lemma* add_lt_add
- \+ *lemma* add_lt_add_left
- \+ *lemma* add_lt_add_of_le_of_lt
- \+ *lemma* add_lt_add_of_lt_of_le
- \+ *theorem* add_lt_add_right
- \+/\- *lemma* add_lt_iff_neg_left
- \+/\- *lemma* add_lt_iff_neg_right
- \+ *lemma* add_lt_of_le_of_neg
- \+ *lemma* add_lt_of_lt_neg_add
- \+ *lemma* add_lt_of_lt_of_neg
- \+ *lemma* add_lt_of_lt_of_nonpos
- \+ *lemma* add_lt_of_lt_sub_left
- \+ *lemma* add_lt_of_lt_sub_right
- \+ *lemma* add_lt_of_neg_of_le
- \+ *lemma* add_lt_of_neg_of_lt
- \+ *lemma* add_lt_of_nonpos_of_lt
- \+ *lemma* add_neg
- \+ *lemma* add_neg_of_neg_of_nonpos
- \+ *lemma* add_neg_of_nonpos_of_neg
- \+ *lemma* add_nonneg
- \+ *lemma* add_nonpos
- \+ *lemma* add_pos
- \+ *lemma* add_pos_of_nonneg_of_pos
- \+ *lemma* add_pos_of_pos_of_nonneg
- \+ *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+/\- *lemma* decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
- \+ *lemma* dist_bdd_within_interval
- \+ *lemma* eq_of_abs_sub_eq_zero
- \+ *lemma* eq_zero_of_abs_eq_zero
- \+ *lemma* eq_zero_of_neg_eq
- \+ *lemma* le_abs_self
- \+ *lemma* le_add_of_le_of_nonneg
- \+ *lemma* le_add_of_neg_add_le
- \+ *lemma* le_add_of_neg_add_le_left
- \+ *lemma* le_add_of_neg_add_le_right
- \+ *lemma* le_add_of_neg_le_sub_left
- \+ *lemma* le_add_of_neg_le_sub_right
- \+ *lemma* le_add_of_nonneg_left
- \+ *lemma* le_add_of_nonneg_of_le
- \+ *lemma* le_add_of_nonneg_right
- \+ *lemma* le_add_of_sub_left_le
- \+ *lemma* le_add_of_sub_right_le
- \+ *lemma* le_neg_add_of_add_le
- \+ *lemma* le_neg_of_le_neg
- \+ *lemma* le_of_add_le_add_left
- \+ *lemma* le_of_add_le_add_right
- \+ *lemma* le_of_neg_le_neg
- \+ *lemma* le_of_sub_nonneg
- \+ *lemma* le_of_sub_nonpos
- \+ *lemma* le_sub_left_of_add_le
- \+ *lemma* le_sub_right_of_add_le
- \+ *lemma* lt_add_of_le_of_pos
- \+ *lemma* lt_add_of_lt_of_nonneg
- \+ *lemma* lt_add_of_lt_of_pos
- \+ *lemma* lt_add_of_neg_add_lt
- \+ *lemma* lt_add_of_neg_add_lt_left
- \+ *lemma* lt_add_of_neg_add_lt_right
- \+ *lemma* lt_add_of_neg_lt_sub_left
- \+ *lemma* lt_add_of_neg_lt_sub_right
- \+ *lemma* lt_add_of_nonneg_of_lt
- \+ *lemma* lt_add_of_pos_left
- \+ *lemma* lt_add_of_pos_of_le
- \+ *lemma* lt_add_of_pos_of_lt
- \+ *lemma* lt_add_of_pos_right
- \+ *lemma* lt_add_of_sub_left_lt
- \+ *lemma* lt_add_of_sub_right_lt
- \+ *lemma* lt_neg_add_of_add_lt
- \+ *lemma* lt_neg_of_lt_neg
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* lt_of_add_lt_add_right
- \+ *lemma* lt_of_neg_lt_neg
- \+ *lemma* lt_of_sub_neg
- \+ *lemma* lt_of_sub_pos
- \+ *lemma* lt_sub_left_of_add_lt
- \+ *lemma* lt_sub_right_of_add_lt
- \+ *lemma* max_add_add_left
- \+ *lemma* max_add_add_right
- \+ *lemma* max_eq_neg_min_neg_neg
- \+ *lemma* max_neg_neg
- \+ *lemma* min_add_add_left
- \+ *lemma* min_add_add_right
- \+ *lemma* min_eq_neg_max_neg_neg
- \+ *lemma* min_neg_neg
- \+ *lemma* ne_zero_of_abs_ne_zero
- \+ *lemma* neg_add_le_left_of_le_add
- \+ *lemma* neg_add_le_of_le_add
- \+ *lemma* neg_add_le_right_of_le_add
- \+ *lemma* neg_add_lt_left_of_lt_add
- \+ *lemma* neg_add_lt_of_lt_add
- \+ *lemma* neg_add_lt_right_of_lt_add
- \+ *lemma* neg_le_abs_self
- \+ *lemma* neg_le_neg
- \+ *lemma* neg_le_of_neg_le
- \+ *lemma* neg_le_sub_left_of_le_add
- \+ *lemma* neg_le_sub_right_of_le_add
- \+ *lemma* neg_lt_neg
- \+ *lemma* neg_lt_of_neg_lt
- \+ *lemma* neg_lt_sub_left_of_lt_add
- \+ *lemma* neg_lt_sub_right_of_lt_add
- \+ *lemma* neg_neg_of_pos
- \+ *lemma* neg_nonneg_of_nonpos
- \+ *lemma* neg_nonpos_of_nonneg
- \+ *lemma* neg_of_neg_pos
- \+ *lemma* neg_pos_of_neg
- \+ *lemma* nonneg_of_neg_nonpos
- \+ *lemma* nonpos_of_neg_nonneg
- \+ *lemma* ordered_add_comm_group.add_lt_add_left
- \+ *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \+ *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \+ *lemma* pos_of_neg_neg
- \+ *lemma* sub_le_of_sub_le
- \+ *lemma* sub_le_self
- \+ *lemma* sub_le_sub
- \+ *lemma* sub_le_sub_left
- \+ *lemma* sub_le_sub_right
- \+ *lemma* sub_left_le_of_le_add
- \+ *lemma* sub_left_lt_of_lt_add
- \+ *lemma* sub_lt_of_sub_lt
- \+ *lemma* sub_lt_self
- \+ *lemma* sub_lt_sub
- \+ *lemma* sub_lt_sub_left
- \+ *lemma* sub_lt_sub_of_le_of_lt
- \+ *lemma* sub_lt_sub_of_lt_of_le
- \+ *lemma* sub_lt_sub_right
- \+ *lemma* sub_neg_of_lt
- \+ *lemma* sub_nonneg_of_le
- \+ *lemma* sub_nonpos_of_le
- \+ *lemma* sub_pos_of_lt
- \+ *lemma* sub_right_le_of_le_add
- \+ *lemma* sub_right_lt_of_lt_add

Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *lemma* abs_mul
- \+ *lemma* abs_mul_abs_self
- \+ *lemma* abs_mul_self
- \+ *lemma* abs_sub_square
- \+/\- *lemma* abs_two
- \+/\- *lemma* bit0_le_bit0
- \+/\- *lemma* bit0_lt_bit0
- \+/\- *lemma* bit1_le_bit1
- \+/\- *lemma* bit1_lt_bit1
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* bit1_pos
- \+/\- *lemma* canonically_ordered_semiring.mul_pos
- \+/\- *lemma* decidable.mul_le_mul_left
- \+/\- *lemma* decidable.mul_le_mul_right
- \+ *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+ *lemma* four_pos
- \+ *lemma* gt_of_mul_lt_mul_neg_left
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \+/\- *lemma* le_mul_of_one_le_left'
- \+/\- *lemma* le_mul_of_one_le_right'
- \+ *lemma* le_of_mul_le_mul_left
- \+ *lemma* le_of_mul_le_mul_right
- \+ *lemma* le_of_mul_le_of_ge_one
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \+ *lemma* lt_of_mul_lt_mul_left
- \+ *lemma* lt_of_mul_lt_mul_right
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+ *lemma* mul_le_mul
- \+/\- *lemma* mul_le_mul_left
- \+ *lemma* mul_le_mul_of_nonneg_left
- \+ *lemma* mul_le_mul_of_nonneg_right
- \+ *lemma* mul_le_mul_of_nonpos_left
- \+ *lemma* mul_le_mul_of_nonpos_right
- \+/\- *lemma* mul_le_mul_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_right
- \+/\- *lemma* mul_lt_mul''
- \+ *lemma* mul_lt_mul'
- \+ *lemma* mul_lt_mul
- \+/\- *lemma* mul_lt_mul_left
- \+ *lemma* mul_lt_mul_of_neg_left
- \+ *lemma* mul_lt_mul_of_neg_right
- \+ *lemma* mul_lt_mul_of_pos_left
- \+ *lemma* mul_lt_mul_of_pos_right
- \+/\- *lemma* mul_lt_mul_right
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+ *lemma* mul_neg_of_neg_of_pos
- \+ *lemma* mul_neg_of_pos_of_neg
- \+/\- *lemma* mul_nonneg'
- \+ *lemma* mul_nonneg
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+ *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+/\- *lemma* mul_pos'
- \+ *lemma* mul_pos
- \+ *lemma* mul_pos_of_neg_of_neg
- \+ *lemma* mul_self_le_mul_self
- \+ *lemma* mul_self_le_mul_self_iff
- \+ *lemma* mul_self_lt_mul_self
- \+ *lemma* mul_self_lt_mul_self_iff
- \+ *lemma* mul_self_nonneg
- \+ *lemma* neg_of_mul_neg_left
- \+ *lemma* neg_of_mul_neg_right
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+ *lemma* nonneg_le_nonneg_of_squares_le
- \+ *lemma* nonneg_of_mul_nonneg_left
- \+ *lemma* nonneg_of_mul_nonneg_right
- \+/\- *lemma* nonpos_of_mul_nonneg_left
- \+/\- *lemma* nonpos_of_mul_nonneg_right
- \+ *lemma* nonpos_of_mul_nonpos_left
- \+ *lemma* nonpos_of_mul_nonpos_right
- \+/\- *lemma* one_le_bit1
- \+/\- *lemma* one_lt_bit1
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \+ *lemma* ordered_ring.mul_nonneg
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \+ *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* pos_of_mul_pos_left
- \+ *lemma* pos_of_mul_pos_right
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right
- \+ *lemma* two_ge_one
- \+ *lemma* two_gt_one
- \+ *lemma* two_ne_zero
- \+ *lemma* two_pos
- \- *lemma* with_top.add_one_le_of_lt
- \- *lemma* with_top.coe_nat
- \- *lemma* with_top.nat_induction
- \- *lemma* with_top.nat_ne_top
- \- *lemma* with_top.top_ne_nat
- \+ *lemma* zero_gt_neg_one
- \+/\- *lemma* zero_le_bit0
- \+/\- *lemma* zero_le_mul_left
- \+/\- *lemma* zero_le_mul_right
- \+ *lemma* zero_le_one
- \+/\- *lemma* zero_lt_bit0
- \+/\- *lemma* zero_lt_mul_left
- \+/\- *lemma* zero_lt_mul_right
- \+ *lemma* zero_lt_one

Modified src/algebra/ring.lean
- \+ *lemma* add_monoid_hom.coe_mul_left
- \+ *def* add_monoid_hom.mul_left
- \+ *def* add_monoid_hom.mul_right
- \+ *lemma* add_monoid_hom.mul_right_apply
- \+ *def* add_mul
- \+ *lemma* add_mul_self_eq
- \+ *lemma* distrib_three_right
- \+/\- *theorem* domain.mul_left_inj
- \+/\- *theorem* domain.mul_right_inj
- \+ *theorem* dvd.elim
- \+ *theorem* dvd.elim_left
- \+ *theorem* dvd.intro
- \+ *theorem* dvd.intro_left
- \+ *def* dvd.trans
- \+ *theorem* dvd_add
- \+ *theorem* dvd_add_iff_left
- \+ *theorem* dvd_add_iff_right
- \+/\- *theorem* dvd_add_left
- \+/\- *theorem* dvd_add_right
- \+/\- *lemma* dvd_add_self_left
- \+/\- *lemma* dvd_add_self_right
- \+ *theorem* dvd_mul_left
- \+ *theorem* dvd_mul_of_dvd_left
- \+ *theorem* dvd_mul_of_dvd_right
- \+ *theorem* dvd_mul_right
- \+/\- *lemma* dvd_neg
- \+ *theorem* dvd_neg_iff_dvd
- \+ *theorem* dvd_neg_of_dvd
- \+ *theorem* dvd_of_dvd_neg
- \+ *theorem* dvd_of_mul_left_dvd
- \+ *def* dvd_of_mul_left_eq
- \+ *theorem* dvd_of_mul_right_dvd
- \+ *def* dvd_of_mul_right_eq
- \+ *theorem* dvd_of_neg_dvd
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_sub
- \+ *theorem* dvd_trans
- \+ *theorem* dvd_zero
- \+ *lemma* eq_of_mul_eq_mul_left
- \+/\- *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \+ *lemma* eq_of_mul_eq_mul_right
- \+/\- *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \+/\- *theorem* eq_zero_of_mul_eq_self_left'
- \+ *lemma* eq_zero_of_mul_eq_self_left
- \+/\- *theorem* eq_zero_of_mul_eq_self_right'
- \+ *lemma* eq_zero_of_mul_eq_self_right
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *theorem* eq_zero_of_zero_dvd
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *theorem* exists_eq_mul_left_of_dvd
- \+ *theorem* exists_eq_mul_right_of_dvd
- \- *lemma* is_ring_hom.comp
- \- *lemma* is_ring_hom.map_neg
- \- *lemma* is_ring_hom.map_sub
- \- *lemma* is_ring_hom.map_zero
- \- *lemma* is_ring_hom.of_semiring
- \- *lemma* is_semiring_hom.comp
- \+ *lemma* left_distrib
- \+ *def* mul_add
- \+/\- *theorem* mul_add_eq_mul_add_iff_sub_mul_add_eq
- \+ *theorem* mul_dvd_mul
- \+/\- *theorem* mul_dvd_mul_iff_left
- \+/\- *theorem* mul_dvd_mul_iff_right
- \+ *theorem* mul_dvd_mul_left
- \+ *theorem* mul_dvd_mul_right
- \+/\- *theorem* mul_eq_zero
- \+ *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero
- \+/\- *theorem* mul_ne_zero'
- \+ *lemma* mul_ne_zero
- \+/\- *theorem* mul_ne_zero_comm'
- \+ *lemma* mul_neg_eq_neg_mul_symm
- \+/\- *lemma* mul_neg_one
- \+ *lemma* mul_self_eq_mul_self_iff
- \+ *lemma* mul_self_eq_one_iff
- \+/\- *lemma* mul_self_eq_zero
- \+/\- *theorem* mul_self_sub_mul_self
- \+ *lemma* mul_self_sub_mul_self_eq
- \+ *lemma* mul_self_sub_one_eq
- \+ *def* mul_sub
- \+ *lemma* mul_sub_left_distrib
- \+ *lemma* mul_sub_right_distrib
- \+ *lemma* mul_zero
- \+/\- *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \+ *lemma* ne_zero_of_mul_ne_zero_left
- \+ *lemma* ne_zero_of_mul_ne_zero_right
- \+/\- *lemma* neg_dvd
- \+ *theorem* neg_dvd_iff_dvd
- \+ *theorem* neg_dvd_of_dvd
- \+ *theorem* neg_eq_neg_one_mul
- \+ *lemma* neg_mul_comm
- \+ *lemma* neg_mul_eq_mul_neg
- \+ *lemma* neg_mul_eq_neg_mul
- \+ *lemma* neg_mul_eq_neg_mul_symm
- \+ *lemma* neg_mul_neg
- \+/\- *lemma* neg_one_mul
- \+ *lemma* one_add_one_eq_two
- \+ *theorem* one_dvd
- \+ *lemma* one_ne_zero
- \+ *lemma* right_distrib
- \+ *lemma* ring.mul_zero
- \+ *lemma* ring.zero_mul
- \- *lemma* ring_hom.coe_of
- \+/\- *lemma* ring_hom.id_apply
- \- *def* ring_hom.of
- \+ *def* sub_mul
- \+/\- *theorem* sub_mul_add_eq_of_mul_add_eq_mul_add
- \+ *theorem* two_mul
- \+/\- *lemma* units.inv_eq_self_iff
- \+/\- *lemma* zero_dvd_iff
- \+/\- *theorem* zero_eq_mul
- \+/\- *lemma* zero_eq_mul_self
- \+ *lemma* zero_mul
- \+ *lemma* zero_ne_one

Modified src/analysis/analytic/basic.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/control/applicative.lean
- \- *theorem* comp.applicative_comp_id
- \- *theorem* comp.applicative_id_comp
- \- *lemma* comp.map_pure
- \- *lemma* comp.pure_seq_eq_map
- \- *lemma* comp.seq_assoc
- \- *lemma* comp.seq_pure
- \+ *theorem* functor.comp.applicative_comp_id
- \+ *theorem* functor.comp.applicative_id_comp
- \+ *lemma* functor.comp.map_pure
- \+ *lemma* functor.comp.pure_seq_eq_map
- \+ *lemma* functor.comp.seq_assoc
- \+ *lemma* functor.comp.seq_pure

Modified src/control/functor.lean


Modified src/control/monad/writer.lean


Modified src/control/traversable/basic.lean


Modified src/control/traversable/instances.lean


Modified src/control/traversable/lemmas.lean


Modified src/data/array/lemmas.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/fin.lean


Modified src/data/hash_map.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean


Modified src/data/monoid_algebra.lean


Modified src/data/multiset.lean


Modified src/data/nat/basic.lean
- \+ *theorem* nat.add_units_eq_zero
- \+ *theorem* nat.units_eq_one

Modified src/data/nat/cast.lean
- \+ *lemma* nat.inv_pos_of_nat
- \+ *lemma* nat.one_div_le_one_div
- \+ *lemma* nat.one_div_lt_one_div
- \+ *lemma* nat.one_div_pos_of_nat
- \+ *lemma* with_top.add_one_le_of_lt
- \+ *lemma* with_top.coe_nat
- \+ *lemma* with_top.nat_induction
- \+ *lemma* with_top.nat_ne_top
- \+ *lemma* with_top.top_ne_nat

Modified src/data/nat/multiplicity.lean


Modified src/data/nat/pairing.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pnat/basic.lean
- \- *theorem* pnat.dvd_trans

Modified src/data/pnat/xgcd.lean
- \+/\- *theorem* pnat.gcd_eq

Modified src/data/polynomial.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/meta_defs.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean
- \- *theorem* cau_seq.mul_pos

Modified src/data/real/cau_seq_completion.lean


Modified src/data/seq/computation.lean


Modified src/data/vector2.lean


Modified src/data/zsqrtd/basic.lean


Added src/deprecated/field.lean
- \+ *lemma* is_ring_hom.injective
- \+ *lemma* is_ring_hom.map_div
- \+ *lemma* is_ring_hom.map_eq_zero
- \+ *lemma* is_ring_hom.map_inv
- \+ *lemma* is_ring_hom.map_ne_zero

Modified src/deprecated/group.lean


Added src/deprecated/ring.lean
- \+ *lemma* is_ring_hom.comp
- \+ *lemma* is_ring_hom.map_neg
- \+ *lemma* is_ring_hom.map_sub
- \+ *lemma* is_ring_hom.map_zero
- \+ *lemma* is_ring_hom.of_semiring
- \+ *lemma* is_semiring_hom.comp
- \+ *lemma* ring_hom.coe_of
- \+ *def* ring_hom.of

Modified src/group_theory/eckmann_hilton.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/monoid_localization.lean


Modified src/init_/algebra/default.lean


Deleted src/init_/algebra/field.lean
- \- *lemma* add_div_eq_mul_add_div
- \- *lemma* div_add_div
- \- *lemma* div_add_div_same
- \- *lemma* div_div_div_div_eq
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_eq_mul_one_div
- \- *lemma* div_eq_one_iff_eq
- \- *lemma* div_helper
- \- *lemma* div_mul_cancel
- \- *lemma* div_mul_div
- \- *lemma* div_mul_eq_div_mul_one_div
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm
- \- *lemma* div_mul_left
- \- *lemma* div_mul_right
- \- *lemma* div_neg_eq_neg_div
- \- *lemma* div_one
- \- *lemma* div_self
- \- *lemma* div_sub_div
- \- *lemma* div_sub_div_same
- \- *lemma* div_zero
- \- *lemma* division_def
- \- *lemma* division_ring.mul_ne_zero
- \- *lemma* division_ring.one_div_mul_one_div
- \- *lemma* eq_div_iff_mul_eq
- \- *lemma* eq_div_of_mul_eq
- \- *lemma* eq_of_div_eq_one
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* eq_of_one_div_eq_one_div
- \- *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left
- \- *lemma* eq_zero_of_one_div_eq_zero
- \- *lemma* inv_eq_one_div
- \- *lemma* inv_inv'
- \- *lemma* inv_mul_cancel
- \- *lemma* inv_ne_zero
- \- *lemma* inv_zero
- \- *lemma* mul_div_assoc
- \- *lemma* mul_div_cancel'
- \- *lemma* mul_div_cancel
- \- *lemma* mul_div_cancel_left
- \- *lemma* mul_div_mul_left
- \- *lemma* mul_div_mul_right
- \- *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* mul_eq_of_eq_div
- \- *lemma* mul_inv'
- \- *lemma* mul_inv_cancel
- \- *lemma* mul_mul_div
- \- *lemma* mul_ne_zero_comm
- \- *lemma* mul_one_div_cancel
- \- *lemma* ne_zero_of_one_div_ne_zero
- \- *lemma* neg_div
- \- *lemma* neg_div_neg_eq
- \- *lemma* one_div_add_one_div
- \- *lemma* one_div_div
- \- *lemma* one_div_eq_inv
- \- *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \- *lemma* one_div_mul_cancel
- \- *lemma* one_div_mul_one_div
- \- *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \- *lemma* one_div_ne_zero
- \- *lemma* one_div_neg_eq_neg_one_div
- \- *lemma* one_div_neg_one_eq_neg_one
- \- *lemma* one_div_one
- \- *lemma* one_div_one_div
- \- *lemma* one_inv_eq
- \- *lemma* zero_div

Deleted src/init_/algebra/functions.lean
- \- *lemma* abs_abs
- \- *lemma* abs_abs_sub_abs_le_abs_sub
- \- *lemma* abs_add_le_abs_add_abs
- \- *lemma* abs_add_three
- \- *lemma* abs_by_cases
- \- *lemma* abs_div
- \- *lemma* abs_le_of_le_of_neg_le
- \- *lemma* abs_lt_of_lt_of_neg_lt
- \- *lemma* abs_mul
- \- *lemma* abs_mul_abs_self
- \- *lemma* abs_mul_self
- \- *lemma* abs_neg
- \- *lemma* abs_nonneg
- \- *lemma* abs_of_neg
- \- *lemma* abs_of_nonneg
- \- *lemma* abs_of_nonpos
- \- *lemma* abs_of_pos
- \- *lemma* abs_one_div
- \- *lemma* abs_pos_of_ne_zero
- \- *lemma* abs_pos_of_neg
- \- *lemma* abs_pos_of_pos
- \- *lemma* abs_sub
- \- *lemma* abs_sub_abs_le_abs_sub
- \- *lemma* abs_sub_le
- \- *lemma* abs_sub_square
- \- *lemma* abs_zero
- \- *lemma* dist_bdd_within_interval
- \- *lemma* eq_of_abs_sub_eq_zero
- \- *lemma* eq_zero_of_abs_eq_zero
- \- *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \- *lemma* eq_zero_of_neg_eq
- \- *lemma* le_abs_self
- \- *lemma* max_add_add_left
- \- *lemma* max_add_add_right
- \- *lemma* max_eq_neg_min_neg_neg
- \- *lemma* max_neg_neg
- \- *lemma* min_add_add_left
- \- *lemma* min_add_add_right
- \- *lemma* min_eq_neg_max_neg_neg
- \- *lemma* min_neg_neg
- \- *lemma* ne_zero_of_abs_ne_zero
- \- *lemma* neg_le_abs_self
- \- *lemma* sub_le_of_abs_sub_le_left
- \- *lemma* sub_le_of_abs_sub_le_right
- \- *lemma* sub_lt_of_abs_sub_lt_left
- \- *lemma* sub_lt_of_abs_sub_lt_right

Deleted src/init_/algebra/group.lean
- \- *lemma* add_eq_of_eq_sub'
- \- *lemma* add_eq_of_eq_sub
- \- *def* add_neg_self
- \- *lemma* add_sub
- \- *lemma* add_sub_add_left_eq_sub
- \- *lemma* add_sub_add_right_eq_sub
- \- *lemma* add_sub_assoc
- \- *lemma* add_sub_cancel
- \- *lemma* add_sub_comm
- \- *lemma* eq_add_of_sub_eq'
- \- *lemma* eq_add_of_sub_eq
- \- *lemma* eq_inv_mul_of_mul_eq
- \- *lemma* eq_inv_of_eq_inv
- \- *lemma* eq_inv_of_mul_eq_one
- \- *lemma* eq_mul_inv_of_mul_eq
- \- *lemma* eq_mul_of_inv_mul_eq
- \- *lemma* eq_mul_of_mul_inv_eq
- \- *def* eq_of_add_eq_add_left
- \- *def* eq_of_add_eq_add_right
- \- *lemma* eq_of_sub_eq_zero
- \- *lemma* eq_sub_of_add_eq'
- \- *lemma* eq_sub_of_add_eq
- \- *lemma* group.mul_left_cancel
- \- *lemma* group.mul_right_cancel
- \- *lemma* inv_eq_of_mul_eq_one
- \- *lemma* inv_inj
- \- *lemma* inv_inv
- \- *lemma* inv_mul_cancel_left
- \- *lemma* inv_mul_cancel_right
- \- *lemma* inv_mul_eq_of_eq_mul
- \- *def* inv_mul_self
- \- *lemma* mul_assoc
- \- *lemma* mul_comm
- \- *lemma* mul_eq_of_eq_inv_mul
- \- *lemma* mul_eq_of_eq_mul_inv
- \- *lemma* mul_inv
- \- *lemma* mul_inv_cancel_left
- \- *lemma* mul_inv_cancel_right
- \- *lemma* mul_inv_eq_of_eq_mul
- \- *lemma* mul_inv_rev
- \- *def* mul_inv_self
- \- *lemma* mul_left_cancel
- \- *lemma* mul_left_cancel_iff
- \- *lemma* mul_left_comm
- \- *lemma* mul_left_inv
- \- *lemma* mul_one
- \- *lemma* mul_right_cancel
- \- *lemma* mul_right_cancel_iff
- \- *lemma* mul_right_comm
- \- *lemma* mul_right_inv
- \- *lemma* neg_add_eq_sub
- \- *def* neg_add_self
- \- *lemma* neg_neg_sub_neg
- \- *lemma* neg_sub
- \- *lemma* one_inv
- \- *lemma* one_mul
- \- *lemma* sub_add
- \- *lemma* sub_add_cancel
- \- *lemma* sub_add_eq_add_sub
- \- *lemma* sub_add_eq_sub_sub
- \- *lemma* sub_add_eq_sub_sub_swap
- \- *lemma* sub_eq_add_neg
- \- *lemma* sub_eq_of_eq_add'
- \- *lemma* sub_eq_of_eq_add
- \- *lemma* sub_eq_sub_add_sub
- \- *lemma* sub_eq_zero_iff_eq
- \- *lemma* sub_eq_zero_of_eq
- \- *lemma* sub_ne_zero_of_ne
- \- *lemma* sub_neg_eq_add
- \- *lemma* sub_self
- \- *lemma* sub_sub
- \- *lemma* sub_sub_self
- \- *lemma* sub_zero
- \- *lemma* zero_sub

Modified src/init_/algebra/norm_num.lean


Deleted src/init_/algebra/ordered_field.lean
- \- *lemma* add_halves
- \- *lemma* add_midpoint
- \- *lemma* add_self_div_two
- \- *lemma* div_le_div_of_le_of_neg
- \- *lemma* div_le_div_of_le_of_pos
- \- *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \- *lemma* div_le_of_le_mul
- \- *lemma* div_le_of_mul_le_of_neg
- \- *lemma* div_lt_div_of_lt_of_neg
- \- *lemma* div_lt_div_of_lt_of_pos
- \- *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \- *lemma* div_lt_div_of_pos_of_lt_of_pos
- \- *lemma* div_lt_of_mul_gt_of_neg
- \- *lemma* div_lt_of_mul_lt_of_pos
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \- *lemma* div_neg_of_neg_of_pos
- \- *lemma* div_neg_of_pos_of_neg
- \- *lemma* div_nonneg_of_nonneg_of_pos
- \- *lemma* div_nonneg_of_nonpos_of_neg
- \- *lemma* div_nonpos_of_nonneg_of_neg
- \- *lemma* div_nonpos_of_nonpos_of_pos
- \- *lemma* div_pos_of_neg_of_neg
- \- *lemma* div_pos_of_pos_of_pos
- \- *lemma* div_two_lt_of_pos
- \- *lemma* div_two_sub_self
- \- *lemma* exists_add_lt_and_pos_of_lt
- \- *lemma* ge_of_forall_ge_sub
- \- *lemma* le_div_of_mul_le
- \- *lemma* le_mul_of_div_le
- \- *lemma* le_mul_of_ge_one_left
- \- *lemma* le_mul_of_ge_one_right
- \- *lemma* le_of_one_div_le_one_div
- \- *lemma* le_of_one_div_le_one_div_of_neg
- \- *lemma* le_of_one_le_div
- \- *lemma* lt_div_of_mul_lt
- \- *lemma* lt_mul_of_gt_one_right
- \- *lemma* lt_of_one_div_lt_one_div
- \- *lemma* lt_of_one_div_lt_one_div_of_neg
- \- *lemma* lt_of_one_lt_div
- \- *lemma* mul_le_mul_of_mul_div_le
- \- *lemma* mul_le_of_div_le_of_neg
- \- *lemma* mul_le_of_le_div
- \- *lemma* mul_lt_of_gt_div_of_neg
- \- *lemma* mul_lt_of_lt_div
- \- *lemma* mul_sub_mul_div_mul_neg
- \- *lemma* mul_sub_mul_div_mul_nonpos
- \- *lemma* mul_zero_lt_mul_inv_of_neg
- \- *lemma* mul_zero_lt_mul_inv_of_pos
- \- *lemma* neg_of_one_div_neg
- \- *lemma* one_div_le_neg_one
- \- *lemma* one_div_le_of_one_div_le_of_neg
- \- *lemma* one_div_le_of_one_div_le_of_pos
- \- *lemma* one_div_le_one_div_of_le
- \- *lemma* one_div_le_one_div_of_le_of_neg
- \- *lemma* one_div_lt_neg_one
- \- *lemma* one_div_lt_one_div_of_lt
- \- *lemma* one_div_lt_one_div_of_lt_of_neg
- \- *lemma* one_div_neg_of_neg
- \- *lemma* one_div_pos_of_pos
- \- *lemma* one_le_div_of_le
- \- *lemma* one_le_one_div
- \- *lemma* one_lt_div_of_lt
- \- *lemma* one_lt_one_div
- \- *lemma* pos_of_one_div_pos
- \- *lemma* sub_self_div_two

Deleted src/init_/algebra/ordered_group.lean
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \- *lemma* add_le_add
- \- *lemma* add_le_add_left
- \- *lemma* add_le_add_right
- \- *lemma* add_le_add_three
- \- *lemma* add_le_of_le_neg_add
- \- *lemma* add_le_of_le_of_nonpos
- \- *lemma* add_le_of_le_sub_left
- \- *lemma* add_le_of_le_sub_right
- \- *lemma* add_le_of_nonpos_of_le
- \- *lemma* add_lt_add
- \- *lemma* add_lt_add_left
- \- *lemma* add_lt_add_of_le_of_lt
- \- *lemma* add_lt_add_of_lt_of_le
- \- *theorem* add_lt_add_right
- \- *lemma* add_lt_of_le_of_neg
- \- *lemma* add_lt_of_lt_neg_add
- \- *lemma* add_lt_of_lt_of_neg
- \- *lemma* add_lt_of_lt_of_nonpos
- \- *lemma* add_lt_of_lt_sub_left
- \- *lemma* add_lt_of_lt_sub_right
- \- *lemma* add_lt_of_neg_of_le
- \- *lemma* add_lt_of_neg_of_lt
- \- *lemma* add_lt_of_nonpos_of_lt
- \- *lemma* add_neg
- \- *lemma* add_neg_of_neg_of_nonpos
- \- *lemma* add_neg_of_nonpos_of_neg
- \- *lemma* add_nonneg
- \- *lemma* add_nonpos
- \- *lemma* add_pos
- \- *lemma* add_pos_of_nonneg_of_pos
- \- *lemma* add_pos_of_pos_of_nonneg
- \- *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \- *lemma* le_add_of_le_of_nonneg
- \- *lemma* le_add_of_neg_add_le
- \- *lemma* le_add_of_neg_add_le_left
- \- *lemma* le_add_of_neg_add_le_right
- \- *lemma* le_add_of_neg_le_sub_left
- \- *lemma* le_add_of_neg_le_sub_right
- \- *lemma* le_add_of_nonneg_left
- \- *lemma* le_add_of_nonneg_of_le
- \- *lemma* le_add_of_nonneg_right
- \- *lemma* le_add_of_sub_left_le
- \- *lemma* le_add_of_sub_right_le
- \- *lemma* le_neg_add_of_add_le
- \- *lemma* le_neg_of_le_neg
- \- *lemma* le_of_add_le_add_left
- \- *lemma* le_of_add_le_add_right
- \- *lemma* le_of_neg_le_neg
- \- *lemma* le_of_sub_nonneg
- \- *lemma* le_of_sub_nonpos
- \- *lemma* le_sub_left_of_add_le
- \- *lemma* le_sub_right_of_add_le
- \- *lemma* lt_add_of_le_of_pos
- \- *lemma* lt_add_of_lt_of_nonneg
- \- *lemma* lt_add_of_lt_of_pos
- \- *lemma* lt_add_of_neg_add_lt
- \- *lemma* lt_add_of_neg_add_lt_left
- \- *lemma* lt_add_of_neg_add_lt_right
- \- *lemma* lt_add_of_neg_lt_sub_left
- \- *lemma* lt_add_of_neg_lt_sub_right
- \- *lemma* lt_add_of_nonneg_of_lt
- \- *lemma* lt_add_of_pos_left
- \- *lemma* lt_add_of_pos_of_le
- \- *lemma* lt_add_of_pos_of_lt
- \- *lemma* lt_add_of_pos_right
- \- *lemma* lt_add_of_sub_left_lt
- \- *lemma* lt_add_of_sub_right_lt
- \- *lemma* lt_neg_add_of_add_lt
- \- *lemma* lt_neg_of_lt_neg
- \- *lemma* lt_of_add_lt_add_left
- \- *lemma* lt_of_add_lt_add_right
- \- *lemma* lt_of_neg_lt_neg
- \- *lemma* lt_of_sub_neg
- \- *lemma* lt_of_sub_pos
- \- *lemma* lt_sub_left_of_add_lt
- \- *lemma* lt_sub_right_of_add_lt
- \- *lemma* neg_add_le_left_of_le_add
- \- *lemma* neg_add_le_of_le_add
- \- *lemma* neg_add_le_right_of_le_add
- \- *lemma* neg_add_lt_left_of_lt_add
- \- *lemma* neg_add_lt_of_lt_add
- \- *lemma* neg_add_lt_right_of_lt_add
- \- *lemma* neg_le_neg
- \- *lemma* neg_le_of_neg_le
- \- *lemma* neg_le_sub_left_of_le_add
- \- *lemma* neg_le_sub_right_of_le_add
- \- *lemma* neg_lt_neg
- \- *lemma* neg_lt_of_neg_lt
- \- *lemma* neg_lt_sub_left_of_lt_add
- \- *lemma* neg_lt_sub_right_of_lt_add
- \- *lemma* neg_neg_of_pos
- \- *lemma* neg_nonneg_of_nonpos
- \- *lemma* neg_nonpos_of_nonneg
- \- *lemma* neg_of_neg_pos
- \- *lemma* neg_pos_of_neg
- \- *lemma* nonneg_of_neg_nonpos
- \- *lemma* nonpos_of_neg_nonneg
- \- *lemma* ordered_add_comm_group.add_lt_add_left
- \- *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \- *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \- *lemma* pos_of_neg_neg
- \- *lemma* sub_le_of_sub_le
- \- *lemma* sub_le_self
- \- *lemma* sub_le_sub
- \- *lemma* sub_le_sub_left
- \- *lemma* sub_le_sub_right
- \- *lemma* sub_left_le_of_le_add
- \- *lemma* sub_left_lt_of_lt_add
- \- *lemma* sub_lt_of_sub_lt
- \- *lemma* sub_lt_self
- \- *lemma* sub_lt_sub
- \- *lemma* sub_lt_sub_left
- \- *lemma* sub_lt_sub_of_le_of_lt
- \- *lemma* sub_lt_sub_of_lt_of_le
- \- *lemma* sub_lt_sub_right
- \- *lemma* sub_neg_of_lt
- \- *lemma* sub_nonneg_of_le
- \- *lemma* sub_nonpos_of_le
- \- *lemma* sub_pos_of_lt
- \- *lemma* sub_right_le_of_le_add
- \- *lemma* sub_right_lt_of_lt_add

Deleted src/init_/algebra/ordered_ring.lean
- \- *lemma* four_pos
- \- *lemma* gt_of_mul_lt_mul_neg_left
- \- *lemma* le_of_mul_le_mul_left
- \- *lemma* le_of_mul_le_mul_right
- \- *lemma* le_of_mul_le_of_ge_one
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \- *lemma* lt_of_mul_lt_mul_left
- \- *lemma* lt_of_mul_lt_mul_right
- \- *lemma* mul_le_mul
- \- *lemma* mul_le_mul_of_nonneg_left
- \- *lemma* mul_le_mul_of_nonneg_right
- \- *lemma* mul_le_mul_of_nonpos_left
- \- *lemma* mul_le_mul_of_nonpos_right
- \- *lemma* mul_lt_mul'
- \- *lemma* mul_lt_mul
- \- *lemma* mul_lt_mul_of_neg_left
- \- *lemma* mul_lt_mul_of_neg_right
- \- *lemma* mul_lt_mul_of_pos_left
- \- *lemma* mul_lt_mul_of_pos_right
- \- *lemma* mul_neg_of_neg_of_pos
- \- *lemma* mul_neg_of_pos_of_neg
- \- *lemma* mul_nonneg
- \- *lemma* mul_nonneg_of_nonpos_of_nonpos
- \- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \- *lemma* mul_pos
- \- *lemma* mul_pos_of_neg_of_neg
- \- *lemma* mul_self_le_mul_self
- \- *lemma* mul_self_le_mul_self_iff
- \- *lemma* mul_self_lt_mul_self
- \- *lemma* mul_self_lt_mul_self_iff
- \- *lemma* mul_self_nonneg
- \- *lemma* neg_of_mul_neg_left
- \- *lemma* neg_of_mul_neg_right
- \- *lemma* nonneg_le_nonneg_of_squares_le
- \- *lemma* nonneg_of_mul_nonneg_left
- \- *lemma* nonneg_of_mul_nonneg_right
- \- *lemma* nonpos_of_mul_nonpos_left
- \- *lemma* nonpos_of_mul_nonpos_right
- \- *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \- *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \- *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \- *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \- *lemma* ordered_ring.mul_nonneg
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \- *lemma* pos_of_mul_pos_left
- \- *lemma* pos_of_mul_pos_right
- \- *lemma* two_ge_one
- \- *lemma* two_gt_one
- \- *lemma* two_ne_zero
- \- *lemma* two_pos
- \- *lemma* zero_gt_neg_one
- \- *lemma* zero_le_one
- \- *lemma* zero_lt_one

Deleted src/init_/algebra/ring.lean
- \- *def* add_mul
- \- *lemma* add_mul_self_eq
- \- *lemma* distrib_three_right
- \- *theorem* dvd.elim
- \- *theorem* dvd.elim_left
- \- *theorem* dvd.intro
- \- *theorem* dvd.intro_left
- \- *def* dvd.trans
- \- *theorem* dvd_add
- \- *theorem* dvd_add_iff_left
- \- *theorem* dvd_add_iff_right
- \- *theorem* dvd_mul_left
- \- *theorem* dvd_mul_of_dvd_left
- \- *theorem* dvd_mul_of_dvd_right
- \- *theorem* dvd_mul_right
- \- *theorem* dvd_neg_iff_dvd
- \- *theorem* dvd_neg_of_dvd
- \- *theorem* dvd_of_dvd_neg
- \- *theorem* dvd_of_mul_left_dvd
- \- *def* dvd_of_mul_left_eq
- \- *theorem* dvd_of_mul_right_dvd
- \- *def* dvd_of_mul_right_eq
- \- *theorem* dvd_of_neg_dvd
- \- *theorem* dvd_refl
- \- *theorem* dvd_sub
- \- *theorem* dvd_trans
- \- *theorem* dvd_zero
- \- *lemma* eq_of_mul_eq_mul_left
- \- *lemma* eq_of_mul_eq_mul_right
- \- *lemma* eq_zero_of_mul_eq_self_left
- \- *lemma* eq_zero_of_mul_eq_self_right
- \- *lemma* eq_zero_of_mul_self_eq_zero
- \- *theorem* eq_zero_of_zero_dvd
- \- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \- *theorem* exists_eq_mul_left_of_dvd
- \- *theorem* exists_eq_mul_right_of_dvd
- \- *lemma* left_distrib
- \- *def* mul_add
- \- *theorem* mul_dvd_mul
- \- *theorem* mul_dvd_mul_left
- \- *theorem* mul_dvd_mul_right
- \- *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero
- \- *lemma* mul_ne_zero
- \- *lemma* mul_neg_eq_neg_mul_symm
- \- *lemma* mul_self_eq_mul_self_iff
- \- *lemma* mul_self_eq_one_iff
- \- *lemma* mul_self_sub_mul_self_eq
- \- *lemma* mul_self_sub_one_eq
- \- *def* mul_sub
- \- *lemma* mul_sub_left_distrib
- \- *lemma* mul_sub_right_distrib
- \- *lemma* mul_zero
- \- *lemma* ne_zero_of_mul_ne_zero_left
- \- *lemma* ne_zero_of_mul_ne_zero_right
- \- *theorem* neg_dvd_iff_dvd
- \- *theorem* neg_dvd_of_dvd
- \- *theorem* neg_eq_neg_one_mul
- \- *lemma* neg_mul_comm
- \- *lemma* neg_mul_eq_mul_neg
- \- *lemma* neg_mul_eq_neg_mul
- \- *lemma* neg_mul_eq_neg_mul_symm
- \- *lemma* neg_mul_neg
- \- *lemma* one_add_one_eq_two
- \- *theorem* one_dvd
- \- *lemma* one_ne_zero
- \- *lemma* right_distrib
- \- *lemma* ring.mul_zero
- \- *lemma* ring.zero_mul
- \- *def* sub_mul
- \- *theorem* two_mul
- \- *lemma* zero_mul
- \- *lemma* zero_ne_one

Modified src/init_/data/int/basic.lean


Modified src/init_/data/int/order.lean


Modified src/init_/data/nat/lemmas.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dual.lean
- \+/\- *def* is_basis.coord_fun

Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/logic/basic.lean


Modified src/measure_theory/outer_measure.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/filter/filter_product.lean


Modified src/ring_theory/integral_domain.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/tactic/abel.lean


Modified src/tactic/algebra.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/norm_num.lean
- \+ *lemma* norm_num.subst_into_add
- \+ *lemma* norm_num.subst_into_mul

Modified src/tactic/ring.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified test/coinductive.lean


Modified test/finish4.lean
- \+/\- *def* append1

Modified test/library_search/ordered_ring.lean


Modified test/lint.lean


Modified test/lint_simp_comm.lean


Modified test/mk_iff_of_inductive.lean


Modified test/monotonicity.lean


Modified test/norm_cast_int.lean


Modified test/norm_cast_lemma_order.lean


Modified test/norm_num.lean


Modified test/nth_rewrite.lean


Modified test/push_neg.lean


Modified test/refine_struct.lean


Modified test/rewrite.lean


Modified test/ring.lean


Modified test/simp_rw.lean


Modified test/tactics.lean




## [2020-05-18 13:38:39](https://github.com/leanprover-community/mathlib/commit/18217e9)
feat(nat/choose): Generalise nat.dvd_choose ([#2703](https://github.com/leanprover-community/mathlib/pull/2703))
Spin-off from [#2701](https://github.com/leanprover-community/mathlib/pull/2701).
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/data/nat/choose.lean
- \- *lemma* nat.prime.dvd_choose
- \+ *lemma* nat.prime.dvd_choose_add
- \+ *lemma* nat.prime.dvd_choose_self
- \+/\- *theorem* sum_range_choose



## [2020-05-18 11:24:28](https://github.com/leanprover-community/mathlib/commit/434e6a6)
chore(*): update to lean 3.13.2 ([#2728](https://github.com/leanprover-community/mathlib/pull/2728))
This should fix the bug with the missing module doc strings in the documentation.
#### Estimated changes
Modified leanpkg.toml




## [2020-05-17 23:39:12](https://github.com/leanprover-community/mathlib/commit/93119dd)
chore(scripts): update nolints.txt ([#2721](https://github.com/leanprover-community/mathlib/pull/2721))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-17 22:37:56](https://github.com/leanprover-community/mathlib/commit/7325104)
feat(ci): store xz archives ([#2719](https://github.com/leanprover-community/mathlib/pull/2719))
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/olean.20cache
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-05-17 20:01:37](https://github.com/leanprover-community/mathlib/commit/cdf97dc)
refactor(field_theory): preparations for Chevalley–Warning ([#2590](https://github.com/leanprover-community/mathlib/pull/2590))
This PR adds some preparations for the Chevalley–Warning theorem.
depends on: ~[#2606](https://github.com/leanprover-community/mathlib/pull/2606), [#2607](https://github.com/leanprover-community/mathlib/pull/2607), [#2623](https://github.com/leanprover-community/mathlib/pull/2623)~
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_val_hom
- \+ *def* units.val_hom

Modified src/field_theory/finite.lean
- \+/\- *theorem* finite_field.card'
- \+/\- *theorem* finite_field.card
- \+/\- *lemma* finite_field.card_image_polynomial_eval
- \+ *lemma* finite_field.cast_card_eq_zero
- \+/\- *lemma* finite_field.exists_root_sum_quadratic
- \- *def* finite_field.field_of_integral_domain
- \+ *lemma* finite_field.forall_pow_eq_one_iff
- \+/\- *lemma* finite_field.pow_card_sub_one_eq_one
- \+ *lemma* finite_field.sum_pow_lt_card_sub_one
- \+ *lemma* finite_field.sum_pow_units

Modified src/ring_theory/integral_domain.lean
- \+/\- *lemma* card_fiber_eq_of_mem_range
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+ *def* field_of_integral_domain
- \+ *lemma* is_cyclic_of_subgroup_integral_domain



## [2020-05-17 17:58:04](https://github.com/leanprover-community/mathlib/commit/f23c361)
chore(*): bump to lean-3.13.1 ([#2697](https://github.com/leanprover-community/mathlib/pull/2697))
## Move algebra to mathlib
The algebraic hierarchy has moved from the core library to `init_`. In later PRs this can be integrated into the existing directory structure of mathlib.
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified leanpkg.toml


Modified scripts/nolints.txt


Modified src/data/int/gcd.lean


Added src/init_/algebra/default.lean


Added src/init_/algebra/field.lean
- \+ *lemma* add_div_eq_mul_add_div
- \+ *lemma* div_add_div
- \+ *lemma* div_add_div_same
- \+ *lemma* div_div_div_div_eq
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* div_eq_one_iff_eq
- \+ *lemma* div_helper
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_mul_div
- \+ *lemma* div_mul_eq_div_mul_one_div
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* div_mul_eq_mul_div_comm
- \+ *lemma* div_mul_left
- \+ *lemma* div_mul_right
- \+ *lemma* div_neg_eq_neg_div
- \+ *lemma* div_one
- \+ *lemma* div_self
- \+ *lemma* div_sub_div
- \+ *lemma* div_sub_div_same
- \+ *lemma* div_zero
- \+ *lemma* division_def
- \+ *lemma* division_ring.mul_ne_zero
- \+ *lemma* division_ring.one_div_mul_one_div
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* eq_div_of_mul_eq
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* eq_one_div_of_mul_eq_one
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \+ *lemma* inv_eq_one_div
- \+ *lemma* inv_inv'
- \+ *lemma* inv_mul_cancel
- \+ *lemma* inv_ne_zero
- \+ *lemma* inv_zero
- \+ *lemma* mul_div_assoc
- \+ *lemma* mul_div_cancel'
- \+ *lemma* mul_div_cancel
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_mul_left
- \+ *lemma* mul_div_mul_right
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \+ *lemma* mul_eq_of_eq_div
- \+ *lemma* mul_inv'
- \+ *lemma* mul_inv_cancel
- \+ *lemma* mul_mul_div
- \+ *lemma* mul_ne_zero_comm
- \+ *lemma* mul_one_div_cancel
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \+ *lemma* neg_div
- \+ *lemma* neg_div_neg_eq
- \+ *lemma* one_div_add_one_div
- \+ *lemma* one_div_div
- \+ *lemma* one_div_eq_inv
- \+ *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_mul_cancel
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_ne_zero
- \+ *lemma* one_div_neg_eq_neg_one_div
- \+ *lemma* one_div_neg_one_eq_neg_one
- \+ *lemma* one_div_one
- \+ *lemma* one_div_one_div
- \+ *lemma* one_inv_eq
- \+ *lemma* zero_div

Added src/init_/algebra/functions.lean
- \+ *lemma* abs_abs
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *lemma* abs_add_le_abs_add_abs
- \+ *lemma* abs_add_three
- \+ *lemma* abs_by_cases
- \+ *lemma* abs_div
- \+ *lemma* abs_le_of_le_of_neg_le
- \+ *lemma* abs_lt_of_lt_of_neg_lt
- \+ *lemma* abs_mul
- \+ *lemma* abs_mul_abs_self
- \+ *lemma* abs_mul_self
- \+ *lemma* abs_neg
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_of_neg
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_of_nonpos
- \+ *lemma* abs_of_pos
- \+ *lemma* abs_one_div
- \+ *lemma* abs_pos_of_ne_zero
- \+ *lemma* abs_pos_of_neg
- \+ *lemma* abs_pos_of_pos
- \+ *lemma* abs_sub
- \+ *lemma* abs_sub_abs_le_abs_sub
- \+ *lemma* abs_sub_le
- \+ *lemma* abs_sub_square
- \+ *lemma* abs_zero
- \+ *lemma* dist_bdd_within_interval
- \+ *lemma* eq_of_abs_sub_eq_zero
- \+ *lemma* eq_zero_of_abs_eq_zero
- \+ *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+ *lemma* eq_zero_of_neg_eq
- \+ *lemma* le_abs_self
- \+ *lemma* max_add_add_left
- \+ *lemma* max_add_add_right
- \+ *lemma* max_eq_neg_min_neg_neg
- \+ *lemma* max_neg_neg
- \+ *lemma* min_add_add_left
- \+ *lemma* min_add_add_right
- \+ *lemma* min_eq_neg_max_neg_neg
- \+ *lemma* min_neg_neg
- \+ *lemma* ne_zero_of_abs_ne_zero
- \+ *lemma* neg_le_abs_self
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right

Added src/init_/algebra/group.lean
- \+ *lemma* add_eq_of_eq_sub'
- \+ *lemma* add_eq_of_eq_sub
- \+ *def* add_neg_self
- \+ *lemma* add_sub
- \+ *lemma* add_sub_add_left_eq_sub
- \+ *lemma* add_sub_add_right_eq_sub
- \+ *lemma* add_sub_assoc
- \+ *lemma* add_sub_cancel
- \+ *lemma* add_sub_comm
- \+ *lemma* eq_add_of_sub_eq'
- \+ *lemma* eq_add_of_sub_eq
- \+ *lemma* eq_inv_mul_of_mul_eq
- \+ *lemma* eq_inv_of_eq_inv
- \+ *lemma* eq_inv_of_mul_eq_one
- \+ *lemma* eq_mul_inv_of_mul_eq
- \+ *lemma* eq_mul_of_inv_mul_eq
- \+ *lemma* eq_mul_of_mul_inv_eq
- \+ *def* eq_of_add_eq_add_left
- \+ *def* eq_of_add_eq_add_right
- \+ *lemma* eq_of_sub_eq_zero
- \+ *lemma* eq_sub_of_add_eq'
- \+ *lemma* eq_sub_of_add_eq
- \+ *lemma* group.mul_left_cancel
- \+ *lemma* group.mul_right_cancel
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* inv_inj
- \+ *lemma* inv_inv
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_cancel_right
- \+ *lemma* inv_mul_eq_of_eq_mul
- \+ *def* inv_mul_self
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_eq_of_eq_inv_mul
- \+ *lemma* mul_eq_of_eq_mul_inv
- \+ *lemma* mul_inv
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_eq_of_eq_mul
- \+ *lemma* mul_inv_rev
- \+ *def* mul_inv_self
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *lemma* mul_left_comm
- \+ *lemma* mul_left_inv
- \+ *lemma* mul_one
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_right_cancel_iff
- \+ *lemma* mul_right_comm
- \+ *lemma* mul_right_inv
- \+ *lemma* neg_add_eq_sub
- \+ *def* neg_add_self
- \+ *lemma* neg_neg_sub_neg
- \+ *lemma* neg_sub
- \+ *lemma* one_inv
- \+ *lemma* one_mul
- \+ *lemma* sub_add
- \+ *lemma* sub_add_cancel
- \+ *lemma* sub_add_eq_add_sub
- \+ *lemma* sub_add_eq_sub_sub
- \+ *lemma* sub_add_eq_sub_sub_swap
- \+ *lemma* sub_eq_add_neg
- \+ *lemma* sub_eq_of_eq_add'
- \+ *lemma* sub_eq_of_eq_add
- \+ *lemma* sub_eq_sub_add_sub
- \+ *lemma* sub_eq_zero_iff_eq
- \+ *lemma* sub_eq_zero_of_eq
- \+ *lemma* sub_ne_zero_of_ne
- \+ *lemma* sub_neg_eq_add
- \+ *lemma* sub_self
- \+ *lemma* sub_sub
- \+ *lemma* sub_sub_self
- \+ *lemma* sub_zero
- \+ *lemma* zero_sub

Added src/init_/algebra/norm_num.lean
- \+ *def* norm_num.add1
- \+ *lemma* norm_num.add1_bit0
- \+ *lemma* norm_num.add1_bit1
- \+ *lemma* norm_num.add1_bit1_helper
- \+ *lemma* norm_num.add1_one
- \+ *lemma* norm_num.add1_zero
- \+ *lemma* norm_num.add_comm_four
- \+ *lemma* norm_num.add_comm_middle
- \+ *lemma* norm_num.add_div_helper
- \+ *lemma* norm_num.bin_add_zero
- \+ *lemma* norm_num.bin_zero_add
- \+ *lemma* norm_num.bit0_add_bit0
- \+ *lemma* norm_num.bit0_add_bit0_helper
- \+ *lemma* norm_num.bit0_add_bit1
- \+ *lemma* norm_num.bit0_add_bit1_helper
- \+ *lemma* norm_num.bit0_add_one
- \+ *lemma* norm_num.bit1_add_bit0
- \+ *lemma* norm_num.bit1_add_bit0_helper
- \+ *lemma* norm_num.bit1_add_bit1
- \+ *lemma* norm_num.bit1_add_bit1_helper
- \+ *lemma* norm_num.bit1_add_one
- \+ *lemma* norm_num.bit1_add_one_helper
- \+ *lemma* norm_num.div_add_helper
- \+ *lemma* norm_num.div_eq_div_helper
- \+ *lemma* norm_num.div_helper
- \+ *lemma* norm_num.div_mul_helper
- \+ *lemma* norm_num.mk_cong
- \+ *lemma* norm_num.mul_bit0
- \+ *lemma* norm_num.mul_bit0_helper
- \+ *lemma* norm_num.mul_bit1
- \+ *lemma* norm_num.mul_bit1_helper
- \+ *lemma* norm_num.mul_div_helper
- \+ *lemma* norm_num.mul_one
- \+ *lemma* norm_num.mul_zero
- \+ *lemma* norm_num.neg_add_neg_eq_of_add_add_eq_zero
- \+ *lemma* norm_num.neg_add_neg_helper
- \+ *lemma* norm_num.neg_add_pos_eq_of_eq_add
- \+ *lemma* norm_num.neg_add_pos_helper1
- \+ *lemma* norm_num.neg_add_pos_helper2
- \+ *lemma* norm_num.neg_mul_neg_helper
- \+ *lemma* norm_num.neg_mul_pos_helper
- \+ *lemma* norm_num.neg_neg_helper
- \+ *lemma* norm_num.neg_zero_helper
- \+ *lemma* norm_num.nonneg_bit0_helper
- \+ *lemma* norm_num.nonneg_bit1_helper
- \+ *lemma* norm_num.nonzero_of_div_helper
- \+ *lemma* norm_num.nonzero_of_neg_helper
- \+ *lemma* norm_num.nonzero_of_pos_helper
- \+ *lemma* norm_num.one_add_bit0
- \+ *lemma* norm_num.one_add_bit1
- \+ *lemma* norm_num.one_add_bit1_helper
- \+ *lemma* norm_num.one_add_one
- \+ *lemma* norm_num.pos_add_neg_helper
- \+ *lemma* norm_num.pos_bit0_helper
- \+ *lemma* norm_num.pos_bit1_helper
- \+ *lemma* norm_num.pos_mul_neg_helper
- \+ *lemma* norm_num.sub_nat_pos_helper
- \+ *lemma* norm_num.sub_nat_zero_helper
- \+ *lemma* norm_num.subst_into_div
- \+ *lemma* norm_num.subst_into_prod
- \+ *lemma* norm_num.subst_into_subtr
- \+ *lemma* norm_num.subst_into_sum
- \+ *lemma* norm_num.zero_mul

Added src/init_/algebra/ordered_field.lean
- \+ *lemma* add_halves
- \+ *lemma* add_midpoint
- \+ *lemma* add_self_div_two
- \+ *lemma* div_le_div_of_le_of_neg
- \+ *lemma* div_le_div_of_le_of_pos
- \+ *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* div_le_of_mul_le_of_neg
- \+ *lemma* div_lt_div_of_lt_of_neg
- \+ *lemma* div_lt_div_of_lt_of_pos
- \+ *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \+ *lemma* div_lt_div_of_pos_of_lt_of_pos
- \+ *lemma* div_lt_of_mul_gt_of_neg
- \+ *lemma* div_lt_of_mul_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \+ *lemma* div_neg_of_neg_of_pos
- \+ *lemma* div_neg_of_pos_of_neg
- \+ *lemma* div_nonneg_of_nonneg_of_pos
- \+ *lemma* div_nonneg_of_nonpos_of_neg
- \+ *lemma* div_nonpos_of_nonneg_of_neg
- \+ *lemma* div_nonpos_of_nonpos_of_pos
- \+ *lemma* div_pos_of_neg_of_neg
- \+ *lemma* div_pos_of_pos_of_pos
- \+ *lemma* div_two_lt_of_pos
- \+ *lemma* div_two_sub_self
- \+ *lemma* exists_add_lt_and_pos_of_lt
- \+ *lemma* ge_of_forall_ge_sub
- \+ *lemma* le_div_of_mul_le
- \+ *lemma* le_mul_of_div_le
- \+ *lemma* le_mul_of_ge_one_left
- \+ *lemma* le_mul_of_ge_one_right
- \+ *lemma* le_of_one_div_le_one_div
- \+ *lemma* le_of_one_div_le_one_div_of_neg
- \+ *lemma* le_of_one_le_div
- \+ *lemma* lt_div_of_mul_lt
- \+ *lemma* lt_mul_of_gt_one_right
- \+ *lemma* lt_of_one_div_lt_one_div
- \+ *lemma* lt_of_one_div_lt_one_div_of_neg
- \+ *lemma* lt_of_one_lt_div
- \+ *lemma* mul_le_mul_of_mul_div_le
- \+ *lemma* mul_le_of_div_le_of_neg
- \+ *lemma* mul_le_of_le_div
- \+ *lemma* mul_lt_of_gt_div_of_neg
- \+ *lemma* mul_lt_of_lt_div
- \+ *lemma* mul_sub_mul_div_mul_neg
- \+ *lemma* mul_sub_mul_div_mul_nonpos
- \+ *lemma* mul_zero_lt_mul_inv_of_neg
- \+ *lemma* mul_zero_lt_mul_inv_of_pos
- \+ *lemma* neg_of_one_div_neg
- \+ *lemma* one_div_le_neg_one
- \+ *lemma* one_div_le_of_one_div_le_of_neg
- \+ *lemma* one_div_le_of_one_div_le_of_pos
- \+ *lemma* one_div_le_one_div_of_le
- \+ *lemma* one_div_le_one_div_of_le_of_neg
- \+ *lemma* one_div_lt_neg_one
- \+ *lemma* one_div_lt_one_div_of_lt
- \+ *lemma* one_div_lt_one_div_of_lt_of_neg
- \+ *lemma* one_div_neg_of_neg
- \+ *lemma* one_div_pos_of_pos
- \+ *lemma* one_le_div_of_le
- \+ *lemma* one_le_one_div
- \+ *lemma* one_lt_div_of_lt
- \+ *lemma* one_lt_one_div
- \+ *lemma* pos_of_one_div_pos
- \+ *lemma* sub_self_div_two

Added src/init_/algebra/ordered_group.lean
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \+ *lemma* add_le_add
- \+ *lemma* add_le_add_left
- \+ *lemma* add_le_add_right
- \+ *lemma* add_le_add_three
- \+ *lemma* add_le_of_le_neg_add
- \+ *lemma* add_le_of_le_of_nonpos
- \+ *lemma* add_le_of_le_sub_left
- \+ *lemma* add_le_of_le_sub_right
- \+ *lemma* add_le_of_nonpos_of_le
- \+ *lemma* add_lt_add
- \+ *lemma* add_lt_add_left
- \+ *lemma* add_lt_add_of_le_of_lt
- \+ *lemma* add_lt_add_of_lt_of_le
- \+ *theorem* add_lt_add_right
- \+ *lemma* add_lt_of_le_of_neg
- \+ *lemma* add_lt_of_lt_neg_add
- \+ *lemma* add_lt_of_lt_of_neg
- \+ *lemma* add_lt_of_lt_of_nonpos
- \+ *lemma* add_lt_of_lt_sub_left
- \+ *lemma* add_lt_of_lt_sub_right
- \+ *lemma* add_lt_of_neg_of_le
- \+ *lemma* add_lt_of_neg_of_lt
- \+ *lemma* add_lt_of_nonpos_of_lt
- \+ *lemma* add_neg
- \+ *lemma* add_neg_of_neg_of_nonpos
- \+ *lemma* add_neg_of_nonpos_of_neg
- \+ *lemma* add_nonneg
- \+ *lemma* add_nonpos
- \+ *lemma* add_pos
- \+ *lemma* add_pos_of_nonneg_of_pos
- \+ *lemma* add_pos_of_pos_of_nonneg
- \+ *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+ *lemma* le_add_of_le_of_nonneg
- \+ *lemma* le_add_of_neg_add_le
- \+ *lemma* le_add_of_neg_add_le_left
- \+ *lemma* le_add_of_neg_add_le_right
- \+ *lemma* le_add_of_neg_le_sub_left
- \+ *lemma* le_add_of_neg_le_sub_right
- \+ *lemma* le_add_of_nonneg_left
- \+ *lemma* le_add_of_nonneg_of_le
- \+ *lemma* le_add_of_nonneg_right
- \+ *lemma* le_add_of_sub_left_le
- \+ *lemma* le_add_of_sub_right_le
- \+ *lemma* le_neg_add_of_add_le
- \+ *lemma* le_neg_of_le_neg
- \+ *lemma* le_of_add_le_add_left
- \+ *lemma* le_of_add_le_add_right
- \+ *lemma* le_of_neg_le_neg
- \+ *lemma* le_of_sub_nonneg
- \+ *lemma* le_of_sub_nonpos
- \+ *lemma* le_sub_left_of_add_le
- \+ *lemma* le_sub_right_of_add_le
- \+ *lemma* lt_add_of_le_of_pos
- \+ *lemma* lt_add_of_lt_of_nonneg
- \+ *lemma* lt_add_of_lt_of_pos
- \+ *lemma* lt_add_of_neg_add_lt
- \+ *lemma* lt_add_of_neg_add_lt_left
- \+ *lemma* lt_add_of_neg_add_lt_right
- \+ *lemma* lt_add_of_neg_lt_sub_left
- \+ *lemma* lt_add_of_neg_lt_sub_right
- \+ *lemma* lt_add_of_nonneg_of_lt
- \+ *lemma* lt_add_of_pos_left
- \+ *lemma* lt_add_of_pos_of_le
- \+ *lemma* lt_add_of_pos_of_lt
- \+ *lemma* lt_add_of_pos_right
- \+ *lemma* lt_add_of_sub_left_lt
- \+ *lemma* lt_add_of_sub_right_lt
- \+ *lemma* lt_neg_add_of_add_lt
- \+ *lemma* lt_neg_of_lt_neg
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* lt_of_add_lt_add_right
- \+ *lemma* lt_of_neg_lt_neg
- \+ *lemma* lt_of_sub_neg
- \+ *lemma* lt_of_sub_pos
- \+ *lemma* lt_sub_left_of_add_lt
- \+ *lemma* lt_sub_right_of_add_lt
- \+ *lemma* neg_add_le_left_of_le_add
- \+ *lemma* neg_add_le_of_le_add
- \+ *lemma* neg_add_le_right_of_le_add
- \+ *lemma* neg_add_lt_left_of_lt_add
- \+ *lemma* neg_add_lt_of_lt_add
- \+ *lemma* neg_add_lt_right_of_lt_add
- \+ *lemma* neg_le_neg
- \+ *lemma* neg_le_of_neg_le
- \+ *lemma* neg_le_sub_left_of_le_add
- \+ *lemma* neg_le_sub_right_of_le_add
- \+ *lemma* neg_lt_neg
- \+ *lemma* neg_lt_of_neg_lt
- \+ *lemma* neg_lt_sub_left_of_lt_add
- \+ *lemma* neg_lt_sub_right_of_lt_add
- \+ *lemma* neg_neg_of_pos
- \+ *lemma* neg_nonneg_of_nonpos
- \+ *lemma* neg_nonpos_of_nonneg
- \+ *lemma* neg_of_neg_pos
- \+ *lemma* neg_pos_of_neg
- \+ *lemma* nonneg_of_neg_nonpos
- \+ *lemma* nonpos_of_neg_nonneg
- \+ *lemma* ordered_add_comm_group.add_lt_add_left
- \+ *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \+ *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \+ *lemma* pos_of_neg_neg
- \+ *lemma* sub_le_of_sub_le
- \+ *lemma* sub_le_self
- \+ *lemma* sub_le_sub
- \+ *lemma* sub_le_sub_left
- \+ *lemma* sub_le_sub_right
- \+ *lemma* sub_left_le_of_le_add
- \+ *lemma* sub_left_lt_of_lt_add
- \+ *lemma* sub_lt_of_sub_lt
- \+ *lemma* sub_lt_self
- \+ *lemma* sub_lt_sub
- \+ *lemma* sub_lt_sub_left
- \+ *lemma* sub_lt_sub_of_le_of_lt
- \+ *lemma* sub_lt_sub_of_lt_of_le
- \+ *lemma* sub_lt_sub_right
- \+ *lemma* sub_neg_of_lt
- \+ *lemma* sub_nonneg_of_le
- \+ *lemma* sub_nonpos_of_le
- \+ *lemma* sub_pos_of_lt
- \+ *lemma* sub_right_le_of_le_add
- \+ *lemma* sub_right_lt_of_lt_add

Added src/init_/algebra/ordered_ring.lean
- \+ *lemma* four_pos
- \+ *lemma* gt_of_mul_lt_mul_neg_left
- \+ *lemma* le_of_mul_le_mul_left
- \+ *lemma* le_of_mul_le_mul_right
- \+ *lemma* le_of_mul_le_of_ge_one
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* lt_of_mul_lt_mul_left
- \+ *lemma* lt_of_mul_lt_mul_right
- \+ *lemma* mul_le_mul
- \+ *lemma* mul_le_mul_of_nonneg_left
- \+ *lemma* mul_le_mul_of_nonneg_right
- \+ *lemma* mul_le_mul_of_nonpos_left
- \+ *lemma* mul_le_mul_of_nonpos_right
- \+ *lemma* mul_lt_mul'
- \+ *lemma* mul_lt_mul
- \+ *lemma* mul_lt_mul_of_neg_left
- \+ *lemma* mul_lt_mul_of_neg_right
- \+ *lemma* mul_lt_mul_of_pos_left
- \+ *lemma* mul_lt_mul_of_pos_right
- \+ *lemma* mul_neg_of_neg_of_pos
- \+ *lemma* mul_neg_of_pos_of_neg
- \+ *lemma* mul_nonneg
- \+ *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* mul_pos
- \+ *lemma* mul_pos_of_neg_of_neg
- \+ *lemma* mul_self_le_mul_self
- \+ *lemma* mul_self_le_mul_self_iff
- \+ *lemma* mul_self_lt_mul_self
- \+ *lemma* mul_self_lt_mul_self_iff
- \+ *lemma* mul_self_nonneg
- \+ *lemma* neg_of_mul_neg_left
- \+ *lemma* neg_of_mul_neg_right
- \+ *lemma* nonneg_le_nonneg_of_squares_le
- \+ *lemma* nonneg_of_mul_nonneg_left
- \+ *lemma* nonneg_of_mul_nonneg_right
- \+ *lemma* nonpos_of_mul_nonpos_left
- \+ *lemma* nonpos_of_mul_nonpos_right
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \+ *lemma* ordered_ring.mul_nonneg
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \+ *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* pos_of_mul_pos_left
- \+ *lemma* pos_of_mul_pos_right
- \+ *lemma* two_ge_one
- \+ *lemma* two_gt_one
- \+ *lemma* two_ne_zero
- \+ *lemma* two_pos
- \+ *lemma* zero_gt_neg_one
- \+ *lemma* zero_le_one
- \+ *lemma* zero_lt_one

Added src/init_/algebra/ring.lean
- \+ *def* add_mul
- \+ *lemma* add_mul_self_eq
- \+ *lemma* distrib_three_right
- \+ *theorem* dvd.elim
- \+ *theorem* dvd.elim_left
- \+ *theorem* dvd.intro
- \+ *theorem* dvd.intro_left
- \+ *def* dvd.trans
- \+ *theorem* dvd_add
- \+ *theorem* dvd_add_iff_left
- \+ *theorem* dvd_add_iff_right
- \+ *theorem* dvd_mul_left
- \+ *theorem* dvd_mul_of_dvd_left
- \+ *theorem* dvd_mul_of_dvd_right
- \+ *theorem* dvd_mul_right
- \+ *theorem* dvd_neg_iff_dvd
- \+ *theorem* dvd_neg_of_dvd
- \+ *theorem* dvd_of_dvd_neg
- \+ *theorem* dvd_of_mul_left_dvd
- \+ *def* dvd_of_mul_left_eq
- \+ *theorem* dvd_of_mul_right_dvd
- \+ *def* dvd_of_mul_right_eq
- \+ *theorem* dvd_of_neg_dvd
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_sub
- \+ *theorem* dvd_trans
- \+ *theorem* dvd_zero
- \+ *lemma* eq_of_mul_eq_mul_left
- \+ *lemma* eq_of_mul_eq_mul_right
- \+ *lemma* eq_zero_of_mul_eq_self_left
- \+ *lemma* eq_zero_of_mul_eq_self_right
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *theorem* eq_zero_of_zero_dvd
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *theorem* exists_eq_mul_left_of_dvd
- \+ *theorem* exists_eq_mul_right_of_dvd
- \+ *lemma* left_distrib
- \+ *def* mul_add
- \+ *theorem* mul_dvd_mul
- \+ *theorem* mul_dvd_mul_left
- \+ *theorem* mul_dvd_mul_right
- \+ *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero
- \+ *lemma* mul_ne_zero
- \+ *lemma* mul_neg_eq_neg_mul_symm
- \+ *lemma* mul_self_eq_mul_self_iff
- \+ *lemma* mul_self_eq_one_iff
- \+ *lemma* mul_self_sub_mul_self_eq
- \+ *lemma* mul_self_sub_one_eq
- \+ *def* mul_sub
- \+ *lemma* mul_sub_left_distrib
- \+ *lemma* mul_sub_right_distrib
- \+ *lemma* mul_zero
- \+ *lemma* ne_zero_of_mul_ne_zero_left
- \+ *lemma* ne_zero_of_mul_ne_zero_right
- \+ *theorem* neg_dvd_iff_dvd
- \+ *theorem* neg_dvd_of_dvd
- \+ *theorem* neg_eq_neg_one_mul
- \+ *lemma* neg_mul_comm
- \+ *lemma* neg_mul_eq_mul_neg
- \+ *lemma* neg_mul_eq_neg_mul
- \+ *lemma* neg_mul_eq_neg_mul_symm
- \+ *lemma* neg_mul_neg
- \+ *lemma* one_add_one_eq_two
- \+ *theorem* one_dvd
- \+ *lemma* one_ne_zero
- \+ *lemma* right_distrib
- \+ *lemma* ring.mul_zero
- \+ *lemma* ring.zero_mul
- \+ *def* sub_mul
- \+ *theorem* two_mul
- \+ *lemma* zero_mul
- \+ *lemma* zero_ne_one

Added src/init_/data/int/basic.lean


Added src/init_/data/int/order.lean
- \+ *theorem* int.abs_eq_nat_abs
- \+ *theorem* int.nat_abs_abs
- \+ *theorem* int.sign_mul_abs

Added src/init_/data/nat/lemmas.lean
- \+ *theorem* nat.eq_of_mul_eq_mul_right
- \+ *theorem* nat.le_mul_self
- \+ *theorem* nat.mul_self_le_mul_self
- \+ *theorem* nat.mul_self_le_mul_self_iff
- \+ *theorem* nat.mul_self_lt_mul_self
- \+ *theorem* nat.mul_self_lt_mul_self_iff
- \+ *theorem* nat.one_add

Added src/init_/default.lean


Modified src/logic/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/simps.lean


Modified test/doc_commands.lean




## [2020-05-17 15:08:29](https://github.com/leanprover-community/mathlib/commit/3449510)
feat(algebra/big_operators): Alternative phrasing of prod-bij ([#2709](https://github.com/leanprover-community/mathlib/pull/2709))
Requested by @ChrisHughes24 in https://github.com/leanprover-community/mathlib/pull/2688/files#r426184248
A repaired version of [#2708](https://github.com/leanprover-community/mathlib/pull/2708).
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_bij'



## [2020-05-17 12:00:04](https://github.com/leanprover-community/mathlib/commit/a206df1)
chore(scripts): update nolints.txt ([#2711](https://github.com/leanprover-community/mathlib/pull/2711))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-17 07:42:04](https://github.com/leanprover-community/mathlib/commit/b530cdb)
refactor(normed_space): require `norm_smul_le` instead of `norm_smul` ([#2693](https://github.com/leanprover-community/mathlib/pull/2693))
While in many cases we can prove `norm_smul` directly, in some cases (e.g., for the operator norm) it's easier to prove `norm_smul_le`. Redefine `normed_space` to avoid repeating the same trick over and over.
#### Estimated changes
Modified src/algebra/module.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* prod.norm_def

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.norm_def
- \+/\- *lemma* continuous_multilinear_map.op_norm_neg
- \- *lemma* continuous_multilinear_map.op_norm_smul
- \+ *lemma* continuous_multilinear_map.op_norm_smul_le

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.norm_def
- \+/\- *def* continuous_linear_map.op_norm
- \+/\- *lemma* continuous_linear_map.op_norm_neg
- \- *lemma* continuous_linear_map.op_norm_smul
- \+ *lemma* continuous_linear_map.op_norm_smul_le

Modified src/analysis/normed_space/real_inner_product.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* inv_smul_smul'
- \+ *theorem* is_unit.smul_eq_zero
- \+ *lemma* mul_action.inv_smul_smul
- \+ *lemma* mul_action.smul_inv_smul
- \+ *lemma* smul_inv_smul'
- \+ *lemma* units.inv_smul_smul
- \+ *theorem* units.smul_eq_zero
- \+ *lemma* units.smul_inv_smul
- \+ *theorem* units.smul_ne_zero

Modified src/measure_theory/l1_space.lean


Modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* bounded_continuous_function.abs_diff_coe_le_dist
- \+ *lemma* bounded_continuous_function.add_apply
- \+/\- *lemma* bounded_continuous_function.coe_add
- \+ *lemma* bounded_continuous_function.coe_const
- \- *lemma* bounded_continuous_function.coe_diff
- \+/\- *lemma* bounded_continuous_function.coe_neg
- \+ *lemma* bounded_continuous_function.coe_smul
- \+ *lemma* bounded_continuous_function.coe_sub
- \+ *lemma* bounded_continuous_function.const_apply
- \+ *lemma* bounded_continuous_function.dist_le_two_norm'
- \+/\- *lemma* bounded_continuous_function.dist_le_two_norm
- \+ *lemma* bounded_continuous_function.ext_iff
- \+ *lemma* bounded_continuous_function.neg_apply
- \+ *lemma* bounded_continuous_function.norm_const_eq
- \+ *lemma* bounded_continuous_function.norm_const_le
- \+ *lemma* bounded_continuous_function.norm_of_normed_group_le
- \- *lemma* bounded_continuous_function.norm_smul
- \- *lemma* bounded_continuous_function.norm_smul_le
- \+ *lemma* bounded_continuous_function.smul_apply
- \+ *lemma* bounded_continuous_function.sub_apply

Modified src/topology/metric_space/isometry.lean




## [2020-05-17 04:33:06](https://github.com/leanprover-community/mathlib/commit/39af0f6)
chore(algebra/ring): drop an unneeded instance ([#2705](https://github.com/leanprover-community/mathlib/pull/2705))
We're incompatible with Lean 3.4.2 for a long time.
#### Estimated changes
Modified src/algebra/ring.lean
- \- *def* has_div_of_division_ring

Modified src/order/filter/filter_product.lean




## [2020-05-17 02:07:24](https://github.com/leanprover-community/mathlib/commit/1580cd8)
fix(algebra/big_operators): typo fix ([#2704](https://github.com/leanprover-community/mathlib/pull/2704))
Fix cut-and-paste typos in the doc string for `∑ x, f x`.
#### Estimated changes
Modified src/algebra/big_operators.lean




## [2020-05-17 02:07:22](https://github.com/leanprover-community/mathlib/commit/4f484a1)
feat(archive/100-theorems-list): Sum of the Reciprocals of the Triangular Numbers ([#2692](https://github.com/leanprover-community/mathlib/pull/2692))
Adds a folder `archive/100-theorems-list`, moves our proof of 82 into it, and provides a proof of 42. There's a readme, I haven't really thought about what should go in there.
#### Estimated changes
Added archive/100-theorems-list/42_inverse_triangle_sum.lean
- \+ *lemma* inverse_triangle_sum

Renamed archive/cubing_a_cube.lean to archive/100-theorems-list/82_cubing_a_cube.lean


Added archive/100-theorems-list/README.md


Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_range_induction
- \+/\- *lemma* finset.sum_range_id_mul_two
- \+ *lemma* finset.sum_range_induction



## [2020-05-17 00:07:54](https://github.com/leanprover-community/mathlib/commit/21bdb78)
feat(ring_theory/ideal_operations): jacobson radical, is_local, and primary ideals ([#768](https://github.com/leanprover-community/mathlib/pull/768))
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean
- \+ *theorem* ideal.is_local.le_jacobson
- \+ *theorem* ideal.is_local.mem_jacobson_or_exists_inv
- \+ *def* ideal.is_local
- \+ *theorem* ideal.is_local_of_is_maximal_radical
- \+ *theorem* ideal.is_primary.to_is_prime
- \+ *def* ideal.is_primary
- \+ *theorem* ideal.is_primary_inf
- \+ *theorem* ideal.is_primary_of_is_maximal_radical
- \+ *theorem* ideal.is_prime.comap
- \+ *theorem* ideal.is_prime_radical
- \+ *def* ideal.jacobson
- \+ *theorem* ideal.jacobson_eq_top_iff
- \+ *theorem* ideal.mem_jacobson_iff
- \+ *theorem* ideal.mem_radical_of_pow_mem

Modified src/ring_theory/ideals.lean
- \+ *theorem* ideal.mem_Inf



## [2020-05-16 21:18:08](https://github.com/leanprover-community/mathlib/commit/00024db)
refactor(group_theory/monoid_localization): use old_structure_cmd ([#2683](https://github.com/leanprover-community/mathlib/pull/2683))
Second bit of [#2675](https://github.com/leanprover-community/mathlib/pull/2675).
The change to ```old_structure_cmd``` is so ring localizations can use this file more easily.
I've not made sure the map ```f``` is implicit when it can be because ```f.foo``` notation means it doesn't make much difference, but I'll change this if needed.*
I have changed some of the bad names at the end; they are still not great.  Does anyone have any
alternative suggestions?
Things to come in future PRs: the group completion of a comm monoid and some examples, ```away``` (localization at a submonoid generated by one element), more stuff on the localization as a quotient type & the fact it satisfies the char pred.
I think I've learnt some stuff about the ```@[simp]``` linter today. Hopefully I'll be making fewer commits trying and failing to appease it.
*edit: I mean I haven't checked how many places I can make ```f``` implicit & remove the appropriate ```f.```'s.
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *def* monoid_hom.to_localization_map
- \- *lemma* submonoid.localization_map.comp_mul_equiv_symm_comap_apply
- \- *lemma* submonoid.localization_map.comp_mul_equiv_symm_map_apply
- \+ *lemma* submonoid.localization_map.eq_iff_exists
- \+/\- *lemma* submonoid.localization_map.eq_of_eq
- \+/\- *lemma* submonoid.localization_map.ext
- \+/\- *lemma* submonoid.localization_map.ext_iff
- \+/\- *lemma* submonoid.localization_map.lift_comp
- \+/\- *lemma* submonoid.localization_map.lift_id
- \+ *lemma* submonoid.localization_map.map_left_cancel
- \+ *lemma* submonoid.localization_map.map_right_cancel
- \+ *lemma* submonoid.localization_map.map_units
- \+/\- *lemma* submonoid.localization_map.mk'_mul_cancel_right
- \+/\- *lemma* submonoid.localization_map.mk'_one
- \+/\- *lemma* submonoid.localization_map.mk'_sec
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_left_inv
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_left_inv_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_right_inv
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_right_inv_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_symm_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_symm_eq_mul_equiv_of_localizations
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_mk'
- \- *lemma* submonoid.localization_map.mul_equiv_of_to_mul_equiv
- \- *lemma* submonoid.localization_map.mul_equiv_of_to_mul_equiv_apply
- \- *def* submonoid.localization_map.of_mul_equiv
- \- *lemma* submonoid.localization_map.of_mul_equiv_eq
- \- *lemma* submonoid.localization_map.of_mul_equiv_id
- \+ *def* submonoid.localization_map.of_mul_equiv_of_dom
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_dom_apply
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_dom_comp
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_dom_comp_symm
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_dom_eq
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_dom_id
- \+ *def* submonoid.localization_map.of_mul_equiv_of_localizations
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_apply
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_comp
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_eq
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_eq_iff_eq
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_localizations_id
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_mul_equiv
- \+ *lemma* submonoid.localization_map.of_mul_equiv_of_mul_equiv_apply
- \+/\- *lemma* submonoid.localization_map.sec_spec'
- \+/\- *lemma* submonoid.localization_map.sec_spec
- \+ *lemma* submonoid.localization_map.surj
- \+ *lemma* submonoid.localization_map.symm_comp_of_mul_equiv_of_localizations_apply'
- \+ *lemma* submonoid.localization_map.symm_comp_of_mul_equiv_of_localizations_apply
- \- *lemma* submonoid.localization_map.symm_of_mul_equiv_apply
- \- *lemma* submonoid.localization_map.symm_to_mul_equiv_apply
- \- *lemma* submonoid.localization_map.to_fun_inj
- \+ *lemma* submonoid.localization_map.to_map_injective
- \- *def* submonoid.localization_map.to_mul_equiv
- \- *lemma* submonoid.localization_map.to_mul_equiv_comp
- \- *lemma* submonoid.localization_map.to_mul_equiv_eq
- \- *lemma* submonoid.localization_map.to_mul_equiv_eq_iff_eq
- \- *lemma* submonoid.localization_map.to_mul_equiv_id
- \- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv
- \- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_apply
- \- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv
- \- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv_apply



## [2020-05-16 17:50:21](https://github.com/leanprover-community/mathlib/commit/a7b17cd)
feat(data/finset): remove uses of choice for infima ([#2699](https://github.com/leanprover-community/mathlib/pull/2699))
This PR removes the dependence of many lemmas about inf of finset sets on the axiom of choice. The motivation for this is to make `category_theory.limits.has_finite_limits_of_semilattice_inf_top` not depend on choice, which I would like so that I can prove independence results about topos models of set theory from the axiom of choice.
This does make the decidable_classical linter fail.
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *lemma* finset.inf_mono_fun
- \+/\- *lemma* finset.le_inf_iff
- \+/\- *lemma* finset.sup_mono_fun



## [2020-05-16 14:49:11](https://github.com/leanprover-community/mathlib/commit/c81be77)
feat(data/finset) Another finset disjointness lemma ([#2698](https://github.com/leanprover-community/mathlib/pull/2698))
I couldn't find this anywhere, and I wanted it.
Naming question: this is "obviously" called `disjoint_filter`, except there's already a lemma with that name.
I know I've broken one of the rules of using `simp` here ("don't do it at the beginning"), but this proof is much longer than I'd have thought would be necessary so I'm rather expecting someone to hop in with a one-liner.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.disjoint_filter_filter



## [2020-05-16 07:36:54](https://github.com/leanprover-community/mathlib/commit/4b71428)
doc(tactic/solve_by_elim): improve docs ([#2696](https://github.com/leanprover-community/mathlib/pull/2696))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/solve_by_elim.lean




## [2020-05-16 02:47:42](https://github.com/leanprover-community/mathlib/commit/74286f5)
feat(category_theory/limits/shapes): avoid choice for binary products ([#2695](https://github.com/leanprover-community/mathlib/pull/2695))
A tiny change to liberate binary products from the axiom of choice
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean




## [2020-05-15 21:05:48](https://github.com/leanprover-community/mathlib/commit/1b85e3c)
chore(*): bump to lean-3.12.0 ([#2681](https://github.com/leanprover-community/mathlib/pull/2681))
## Changes to bracket notation
* `{a}` now requires an instance `has_singleton`;
* `insert a ∅ = {a}` is called `insert_emptyc_eq`, provided by an `is_lawful_singleton` instance;
* `a ∈ ({b} : set α)` is now defeq `a = b`, not `a = b ∨ false`;
* `({a} : set α)` is no longer defeq `insert a ∅`;
* `({a} : finset α)` now means `⟨⟨[a]⟩, _⟩` (used to be called `finset.singleton a`), not `insert a ∅`;
* removed `finset.singleton`;
* `{a, b}` is now `insert a {b}`, not `insert b {a}`.
* `finset.univ : finset bool` is now `{tt, ff}`;
* `(({a} : finset α) : set α)` is no longer defeq `{a}`.
## Tactic `norm_num`
The interactive tactic `norm_num` was recently rewritten in Lean. The non-interactive `tactic.norm_num` has been removed in Lean 3.12 so that we can migrate the algebraic hierarchy to mathlib in 3.13.
## Tactic combinators
https://github.com/leanprover-community/lean/pull/212 renames a bunch of tactic combinators. We change to using the new names.
## Tactic `case`
https://github.com/leanprover-community/lean/pull/228 slightly changes the semantics of the `case` tactic. We fix the resulting breakage to be conform the new semantics.
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/big_operators.lean


Modified src/algebra/classical_lie_algebras.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* finset.center_mass_singleton

Modified src/analysis/special_functions/trigonometric.lean


Modified src/computability/reduce.lean


Modified src/computability/turing_machine.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.apply_eq_iff_eq

Modified src/data/equiv/mul_add.lean


Modified src/data/fin_enum.lean


Modified src/data/finmap.lean


Modified src/data/finset.lean
- \+/\- *theorem* finset.card_eq_one
- \+/\- *theorem* finset.card_erase_le
- \+/\- *theorem* finset.card_erase_lt_of_mem
- \+/\- *theorem* finset.card_erase_of_mem
- \+/\- *theorem* finset.card_singleton
- \+/\- *lemma* finset.coe_singleton
- \+/\- *theorem* finset.fold_singleton
- \+/\- *theorem* finset.image_singleton
- \- *lemma* finset.inf_singleton'
- \+/\- *lemma* finset.inf_singleton
- \+ *lemma* finset.infi_coe
- \- *theorem* finset.insert_empty_eq_singleton
- \- *theorem* finset.insert_singleton_self_eq'
- \+/\- *theorem* finset.insert_singleton_self_eq
- \+/\- *theorem* finset.inter_singleton_of_mem
- \+/\- *theorem* finset.inter_singleton_of_not_mem
- \+/\- *theorem* finset.map_singleton
- \- *theorem* finset.max_singleton'
- \+/\- *theorem* finset.max_singleton
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.mem_singleton_self
- \- *theorem* finset.min_singleton'
- \+/\- *theorem* finset.min_singleton
- \+/\- *theorem* finset.ne_empty_of_mem
- \+ *theorem* finset.nonempty.ne_empty
- \+/\- *theorem* finset.not_mem_singleton
- \+/\- *lemma* finset.powerset_empty
- \- *def* finset.singleton
- \+/\- *lemma* finset.singleton_bind
- \- *theorem* finset.singleton_eq_singleton
- \+/\- *lemma* finset.singleton_iff_unique_mem
- \+/\- *theorem* finset.singleton_inj
- \+/\- *theorem* finset.singleton_inter_of_mem
- \+/\- *theorem* finset.singleton_inter_of_not_mem
- \+/\- *theorem* finset.singleton_ne_empty
- \+ *theorem* finset.singleton_nonempty
- \+ *lemma* finset.singleton_subset_set_iff
- \+/\- *theorem* finset.singleton_val
- \- *lemma* finset.sup_singleton'
- \+/\- *lemma* finset.sup_singleton
- \+ *lemma* finset.supr_coe
- \+/\- *lemma* infi_eq_infi_finset
- \+/\- *theorem* option.to_finset_some
- \+/\- *lemma* supr_eq_supr_finset

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean
- \+/\- *theorem* fintype.univ_bool

Modified src/data/fintype/card.lean


Modified src/data/list/antidiagonal.lean


Modified src/data/list/basic.lean
- \+/\- *lemma* list.doubleton_eq
- \+/\- *lemma* list.singleton_eq

Modified src/data/list/nodup.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/gcd.lean


Modified src/data/num/lemmas.lean


Modified src/data/pequiv.lean


Modified src/data/polynomial.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* set.singleton_def
- \+/\- *theorem* set.singleton_nonempty

Modified src/data/set/finite.lean


Modified src/data/subtype.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/geometry/manifold/manifold.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/logic/embedding.lean


Modified src/logic/function/basic.lean
- \+ *theorem* function.left_inverse.right_inverse
- \+ *theorem* function.left_inverse.surjective
- \+ *theorem* function.right_inverse.injective
- \+ *theorem* function.right_inverse.left_inverse

Modified src/logic/relation.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/integration.lean


Modified src/meta/coinductive_predicates.lean


Modified src/order/bounds.lean


Modified src/order/complete_lattice.lean


Modified src/order/zorn.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/zfc.lean
- \- *theorem* Set.mem_singleton'
- \+/\- *theorem* Set.mem_singleton

Modified src/tactic/abel.lean


Modified src/tactic/converter/apply_congr.lean


Modified src/tactic/core.lean


Modified src/tactic/derive_inhabited.lean


Modified src/tactic/finish.lean


Modified src/tactic/linarith.lean


Modified src/tactic/mk_iff_of_inductive_prop.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/slice.lean


Modified src/tactic/tauto.lean


Modified src/tactic/transport.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* emetric.diam_insert

Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-05-15 21:05:46](https://github.com/leanprover-community/mathlib/commit/f5f7a3c)
feat(analysis/special_functions/exp_log): power series for log around 1 ([#2646](https://github.com/leanprover-community/mathlib/pull/2646))
This PR adds the power series expansion for the real logarithm around `1`, in the form
```lean
has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x))
```
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_div

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/mean_value.lean
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_deriv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_deriv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.norm_id_field'
- \+ *lemma* continuous_linear_map.norm_id_field

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.abs_log_sub_add_sum_range_le
- \+ *theorem* real.has_sum_pow_div_log_of_abs_lt_1



## [2020-05-15 18:16:25](https://github.com/leanprover-community/mathlib/commit/14a82b3)
fix(tactic/norm_num): div/mod with negative first arg ([#2689](https://github.com/leanprover-community/mathlib/pull/2689))
bugfix from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/norm_num.20doesn't.20prove/near/197674516
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2020-05-15 16:34:16](https://github.com/leanprover-community/mathlib/commit/a4266a0)
chore(scripts): update nolints.txt ([#2690](https://github.com/leanprover-community/mathlib/pull/2690))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-15 13:15:27](https://github.com/leanprover-community/mathlib/commit/471d29e)
perf(tactic/ring): use new norm_num, avoid mk_app ([#2685](https://github.com/leanprover-community/mathlib/pull/2685))
Remove `tactic.norm_num` from `ring`, and do some performance upgrades borrowed from the `norm_num` overhaul while I'm at it.
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified src/tactic/ring.lean
- \+/\- *theorem* tactic.ring.horner_pow
- \+ *theorem* tactic.ring.pow_succ

Modified test/ring.lean




## [2020-05-15 07:57:55](https://github.com/leanprover-community/mathlib/commit/b44fa3c)
chore(data/int/basic): mark cast_sub with simp attribute ([#2687](https://github.com/leanprover-community/mathlib/pull/2687))
I think the reason this didn't have the `simp` attribute already was from the time when `sub_eq_add_neg` was a `simp` lemma, so it wasn't necessary. I'm adding the `simp` attribute back now that `sub_eq_add_neg` is not a `simp` lemma.
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_sub



## [2020-05-15 04:51:31](https://github.com/leanprover-community/mathlib/commit/f07ac36)
feat(category_theory/limits/lattice): finite limits in a semilattice ([#2665](https://github.com/leanprover-community/mathlib/pull/2665))
Construct finite limits in a semilattice_inf_top category, and finite colimits in a semilattice_sup_bot category.
#### Estimated changes
Modified src/category_theory/limits/lattice.lean




## [2020-05-15 03:11:30](https://github.com/leanprover-community/mathlib/commit/378aa0d)
feat(data/nat/choose): Sum a row of Pascal's triangle ([#2684](https://github.com/leanprover-community/mathlib/pull/2684))
Add the "sum of the nth row of Pascal's triangle" theorem.
Naming is hard, of course, and this is my first PR to mathlib, so naming suggestions are welcome.
Briefly discussed at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619403 .
#### Estimated changes
Modified src/data/nat/choose.lean
- \+ *theorem* sum_range_choose



## [2020-05-14 18:21:52](https://github.com/leanprover-community/mathlib/commit/be03a3d)
chore(scripts): update nolints.txt ([#2682](https://github.com/leanprover-community/mathlib/pull/2682))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-14 18:21:50](https://github.com/leanprover-community/mathlib/commit/606be81)
perf(tactic/ext): NEVER USE `user_attribute.get_param` ([#2674](https://github.com/leanprover-community/mathlib/pull/2674))
Refactor the extensionality attribute a bit so that it avoids `get_param`, which is a performance nightmare because it uses `eval_expr`.
```lean
import all
set_option profiler true
example (f g : bool → bool → set bool) : f = g :=
by ext
-- before: tactic execution took 2.19s
-- after: tactic execution took 33ms
```
#### Estimated changes
Modified src/tactic/ext.lean


Modified src/tactic/lint/basic.lean


Modified src/tactic/norm_cast.lean




## [2020-05-14 18:21:48](https://github.com/leanprover-community/mathlib/commit/7427f8e)
feat(topology): a few properties of `tendsto _ _ (𝓤 α)` ([#2645](https://github.com/leanprover-community/mathlib/pull/2645))
- prove that `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is an equivalence realtion;
- in case of a metric space, restate this relation as `tendsto (λ x, dist (f x) (g x)) l (𝓝 0)`;
- prove that `tendsto f l (𝓝 a) ↔ tendsto g l (𝓝 b)` provided that
  `tendsto (λ x, (f x, g x)) l (𝓤 α)`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* filter.tendsto.congr_dist
- \+ *lemma* tendsto_iff_of_dist
- \+ *lemma* tendsto_uniformity_iff_dist_tendsto_zero

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.tendsto.congr_uniformity
- \+ *lemma* filter.tendsto.uniformity_symm
- \+ *lemma* filter.tendsto.uniformity_trans
- \+ *lemma* tendsto_diag_uniformity
- \+ *lemma* uniform.tendsto_congr



## [2020-05-14 15:22:51](https://github.com/leanprover-community/mathlib/commit/d412cfd)
chore(algebra/ring): lemmas about units in a semiring ([#2680](https://github.com/leanprover-community/mathlib/pull/2680))
The lemmas in non-localization files from [#2675](https://github.com/leanprover-community/mathlib/pull/2675). (Apart from one, which wasn't relevant to [#2675](https://github.com/leanprover-community/mathlib/pull/2675)).
(Edit: I am bad at git. I was hoping there would only be 1 commit here. I hope whatever I'm doing wrong is inconsequential...)
#### Estimated changes
Modified src/algebra/group/is_unit.lean
- \+ *theorem* is_unit.mul_left_inj
- \+ *theorem* is_unit.mul_right_inj

Modified src/algebra/ring.lean
- \+ *theorem* is_unit.mul_left_eq_zero_iff_eq_zero
- \+ *theorem* is_unit.mul_right_eq_zero_iff_eq_zero
- \+ *theorem* units.mul_left_eq_zero_iff_eq_zero
- \+ *theorem* units.mul_right_eq_zero_iff_eq_zero



## [2020-05-14 11:14:27](https://github.com/leanprover-community/mathlib/commit/03c272e)
chore(scripts): update nolints.txt ([#2679](https://github.com/leanprover-community/mathlib/pull/2679))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-14 11:14:24](https://github.com/leanprover-community/mathlib/commit/2871bd1)
chore(logic/function): drop `function.uncurry'` ([#2678](https://github.com/leanprover-community/mathlib/pull/2678))
See [lean[#161](https://github.com/leanprover-community/mathlib/pull/161)](https://github.com/leanprover-community/lean/pull/161/files#diff-42c23da308a4d5900f9f3244953701daR132)
Also add `uniform_continuous.prod_map` and `uniform_continuous₂.bicompl`
#### Estimated changes
Modified src/logic/function/basic.lean
- \- *lemma* function.curry_uncurry'
- \- *def* function.uncurry'
- \- *lemma* function.uncurry'_bicompr
- \- *lemma* function.uncurry'_curry
- \+ *lemma* function.uncurry_bicompl

Modified src/order/filter/extr.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/uniform_space/abstract_completion.lean
- \+/\- *lemma* abstract_completion.extension₂_coe_coe
- \+/\- *lemma* abstract_completion.uniform_continuous_map₂

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous.prod_map
- \+ *lemma* uniform_continuous₂.bicompl
- \+ *lemma* uniform_continuous₂.uniform_continuous
- \+/\- *def* uniform_continuous₂
- \+/\- *lemma* uniform_continuous₂_curry
- \+/\- *lemma* uniform_continuous₂_def

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* uniform_space.completion.extension₂_coe_coe
- \+/\- *lemma* uniform_space.completion.map₂_coe_coe
- \+/\- *lemma* uniform_space.completion.uniform_continuous_map₂



## [2020-05-14 11:14:19](https://github.com/leanprover-community/mathlib/commit/3da777a)
chore(linear_algebra/basis): use dot notation, simplify some proofs ([#2671](https://github.com/leanprover-community/mathlib/pull/2671))
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *lemma* continuous_equiv_fun_basis
- \+ *lemma* continuous_linear_map.exists_right_inverse_of_surjective

Modified src/linear_algebra/basis.lean
- \+/\- *lemma* constr_basis
- \+/\- *lemma* exists_is_basis
- \- *lemma* exists_left_inverse_linear_map_of_injective
- \- *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *lemma* linear_independent.inl_union_inr
- \+ *lemma* linear_independent.ne_zero
- \+ *lemma* linear_independent.union
- \- *lemma* linear_independent_inl_union_inr
- \- *lemma* linear_independent_union
- \+ *lemma* linear_map.exists_left_inverse_of_injective
- \+ *lemma* linear_map.exists_right_inverse_of_surjective
- \- *lemma* ne_zero_of_linear_independent

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2020-05-14 07:53:24](https://github.com/leanprover-community/mathlib/commit/d0beb49)
doc(*): move most docs to website, update links ([#2676](https://github.com/leanprover-community/mathlib/pull/2676))
The relaunched https://leanprover-community.github.io now contains copies of most of the doc files. This PR replaces the corresponding markdown files on mathlib with pointers to their new locations so that they only need to be maintained in one place.
The two remaining markdown files are `docs/contribute/bors.md` and `docs/contribute/code-review.md`.
Fixes [#2168](https://github.com/leanprover-community/mathlib/pull/2168).
#### Estimated changes
Modified .github/CONTRIBUTING.md


Modified README.md


Modified archive/README.md


Modified docs/contribute/doc.md


Modified docs/contribute/index.md


Modified docs/contribute/naming.md


Modified docs/contribute/style.md


Modified docs/extras.md


Modified docs/extras/calc.md


Modified docs/extras/conv.md


Modified docs/extras/simp.md


Modified docs/extras/tactic_writing.md


Modified docs/extras/well_founded_recursion.md


Modified docs/install/debian.md


Modified docs/install/debian_details.md


Deleted docs/install/extensions-icon.png


Modified docs/install/linux.md


Modified docs/install/macos.md


Deleted docs/install/new-extensions-icon.png


Modified docs/install/project.md


Modified docs/install/windows.md


Modified docs/mathlib-overview.md


Modified docs/theories.md


Modified docs/theories/category_theory.md


Modified docs/theories/naturals.md


Modified docs/theories/padics.md


Modified docs/theories/sets.md


Modified docs/theories/topology.md


Modified src/tactic/doc_commands.lean


Modified src/topology/basic.lean




## [2020-05-14 04:40:05](https://github.com/leanprover-community/mathlib/commit/7077b58)
chore(logic/function): move to `logic/function/basic` ([#2677](https://github.com/leanprover-community/mathlib/pull/2677))
Also add some docstrings.
I'm going to add more `logic.function.*` files with theorems that can't go to `basic` because of imports.
#### Estimated changes
Modified src/algebra/group/basic.lean


Modified src/algebra/group/units.lean


Modified src/category_theory/fully_faithful.lean


Modified src/control/bifunctor.lean


Modified src/data/set/function.lean


Renamed src/logic/function.lean to src/logic/function/basic.lean
- \+/\- *theorem* function.cantor_injective
- \+/\- *theorem* function.cantor_surjective

Modified src/order/boolean_algebra.lean




## [2020-05-14 04:40:03](https://github.com/leanprover-community/mathlib/commit/6ffb613)
chore(algebra/free_monoid): add a custom `rec_on` ([#2670](https://github.com/leanprover-community/mathlib/pull/2670))
#### Estimated changes
Modified src/algebra/free_monoid.lean
- \+/\- *lemma* free_monoid.mul_def
- \+ *lemma* free_monoid.of_def
- \- *lemma* free_monoid.of_mul_eq_cons
- \+/\- *lemma* free_monoid.one_def
- \+ *def* free_monoid.rec_on

Modified src/group_theory/submonoid.lean




## [2020-05-14 00:19:02](https://github.com/leanprover-community/mathlib/commit/f7cb363)
refactor(order/lattice): adjust proofs to avoid choice ([#2666](https://github.com/leanprover-community/mathlib/pull/2666))
For foundational category theoretic reasons, I'd like these lattice properties to avoid choice.
In particular, I'd like the proof here: https://github.com/leanprover-community/mathlib/pull/2665 to be intuitionistic.
 For most of them it was very easy, eg changing `finish` to `simp`. For `sup_assoc` and `inf_assoc` it's a bit more complex though - for `inf_assoc` I wrote out a term mode proof, and for `sup_assoc` I used `ifinish`. I realise `ifinish` is deprecated because it isn't always intuitionistic, but in this case it did give an intuitionistic proof. I think both should be proved the same way, but I'm including one of each to see which is preferred.
#### Estimated changes
Modified src/order/lattice.lean
- \+/\- *lemma* inf_le_inf_left
- \+/\- *lemma* inf_le_inf_right



## [2020-05-13 18:31:18](https://github.com/leanprover-community/mathlib/commit/fc0c025)
refactor(scripts/mk_all): generate a single deterministic all.lean file ([#2673](https://github.com/leanprover-community/mathlib/pull/2673))
The current `mk_all.sh` script is non-deterministic, and creates invalid Lean code for the `data.matrix.notation` import.  The generated `all.lean` files are also slow: they take two minutes to compile on my machine.
The new script fixes all of that.  The single generated `all.lean` file takes only 27 seconds to compile now.
#### Estimated changes
Modified scripts/mk_all.sh




## [2020-05-13 12:20:02](https://github.com/leanprover-community/mathlib/commit/9f16f86)
feat(topology/algebra/infinite_sum): sums on subtypes ([#2659](https://github.com/leanprover-community/mathlib/pull/2659))
For `f` a summable function defined on the integers, we prove the formula
```
(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)
```
This is deduced from a general version on subtypes of the form `univ - s` where `s` is a finset.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* coe_not_mem_range_equiv
- \+ *lemma* coe_not_mem_range_equiv_symm
- \+ *def* not_mem_range_equiv

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable
- \+ *lemma* has_sum_nat_add_iff'
- \+ *lemma* has_sum_nat_add_iff
- \+ *lemma* has_sum_subtype_iff'
- \+ *lemma* has_sum_subtype_iff
- \+ *lemma* has_sum_subtype_iff_of_eq_zero
- \+ *lemma* sum_add_tsum_nat_add
- \+ *lemma* sum_add_tsum_subtype
- \+ *lemma* summable_nat_add_iff
- \+ *lemma* summable_subtype_iff



## [2020-05-13 10:27:15](https://github.com/leanprover-community/mathlib/commit/c9f2cbc)
chore(scripts): update nolints.txt ([#2669](https://github.com/leanprover-community/mathlib/pull/2669))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-13 10:27:13](https://github.com/leanprover-community/mathlib/commit/506a71f)
feat(category_theory): preadditive categories ([#2663](https://github.com/leanprover-community/mathlib/pull/2663))
[As discussed](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Lean.20in.20the.20wild/near/197168926), here is the pedestrian definition of preadditive categories. Hopefully, it is not here to stay, but it will allow me to start PRing abelian categories.
#### Estimated changes
Modified src/algebra/category/Group/default.lean


Added src/algebra/category/Group/preadditive.lean


Modified src/algebra/category/Group/zero.lean


Modified src/algebra/category/Module/basic.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cofork.π_of_π
- \+ *lemma* category_theory.limits.fork.ι_of_ι

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/zero.lean
- \- *lemma* category_theory.limits.zero_of_comp_epi
- \+/\- *lemma* category_theory.limits.zero_of_comp_mono
- \+ *lemma* category_theory.limits.zero_of_epi_comp

Added src/category_theory/preadditive.lean
- \+ *lemma* category_theory.preadditive.comp_neg
- \+ *lemma* category_theory.preadditive.comp_sub
- \+ *lemma* category_theory.preadditive.epi_iff_cancel_zero
- \+ *lemma* category_theory.preadditive.epi_of_cancel_zero
- \+ *def* category_theory.preadditive.has_coequalizers_of_has_cokernels
- \+ *def* category_theory.preadditive.has_colimit_parallel_pair
- \+ *def* category_theory.preadditive.has_equalizers_of_has_kernels
- \+ *def* category_theory.preadditive.has_limit_parallel_pair
- \+ *def* category_theory.preadditive.left_comp
- \+ *lemma* category_theory.preadditive.mono_iff_cancel_zero
- \+ *lemma* category_theory.preadditive.mono_of_cancel_zero
- \+ *lemma* category_theory.preadditive.neg_comp
- \+ *lemma* category_theory.preadditive.neg_comp_neg
- \+ *def* category_theory.preadditive.right_comp
- \+ *lemma* category_theory.preadditive.sub_comp



## [2020-05-13 10:27:11](https://github.com/leanprover-community/mathlib/commit/ce86d33)
feat(analysis/calculus/(f)deriv): differentiability of a finite sum of functions ([#2657](https://github.com/leanprover-community/mathlib/pull/2657))
We show that, if each `f i` is differentiable, then `λ y, ∑ i in s, f i y` is also differentiable when `s` is a finset, and give the lemmas around this for `fderiv` and `deriv`.
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *theorem* asymptotics.is_O.sum
- \+ *theorem* asymptotics.is_O_with.sum
- \+ *theorem* asymptotics.is_O_with_zero'
- \+/\- *theorem* asymptotics.is_O_with_zero
- \+/\- *theorem* asymptotics.is_O_zero
- \+ *theorem* asymptotics.is_o.sum

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_div_const
- \+ *lemma* deriv_sum
- \+ *lemma* deriv_within_div_const
- \+ *lemma* deriv_within_sum
- \+ *lemma* differentiable.div_const
- \+ *lemma* differentiable_at.div_const
- \+ *lemma* differentiable_on.div_const
- \+ *lemma* differentiable_within_at.div_const
- \+ *theorem* has_deriv_at.sum
- \+ *theorem* has_deriv_at_filter.sum
- \+ *lemma* has_deriv_within_at.has_fderiv_within_at
- \+ *theorem* has_deriv_within_at.sum
- \+ *theorem* has_strict_deriv_at.sum

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* differentiable.sum
- \+ *theorem* differentiable_at.sum
- \+ *theorem* differentiable_on.sum
- \+ *theorem* differentiable_within_at.sum
- \+ *theorem* fderiv_sum
- \+ *theorem* fderiv_within_sum
- \+ *theorem* has_fderiv_at.sum
- \+ *theorem* has_fderiv_at_filter.sum
- \+ *theorem* has_fderiv_within_at.sum
- \+ *theorem* has_strict_fderiv_at.sum

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.sum_apply



## [2020-05-13 07:01:46](https://github.com/leanprover-community/mathlib/commit/ed183f9)
chore(group_theory/submonoid): use `complete_lattice_of_Inf` ([#2661](https://github.com/leanprover-community/mathlib/pull/2661))
* Use `complete_lattice_of_Inf` for `submonoid` and `subgroup` lattices.
* Add `sub*.copy`.
* Add a few `@[simp]` lemmas.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.to_fun_eq_coe

Modified src/group_theory/bundled_subgroup.lean
- \+/\- *lemma* subgroup.closure_empty
- \+/\- *lemma* subgroup.closure_eq
- \- *lemma* subgroup.coe_ssubset_coe
- \+ *lemma* subgroup.coe_to_submonoid

Modified src/group_theory/submonoid.lean
- \+ *lemma* submonoid.coe_copy
- \+ *lemma* submonoid.coe_infi
- \+ *def* submonoid.copy
- \+ *lemma* submonoid.copy_eq
- \+/\- *theorem* submonoid.ext'
- \+ *lemma* submonoid.mem_carrier
- \+ *lemma* submonoid.mem_infi

Modified src/order/bounds.lean
- \+ *lemma* is_glb.of_image
- \+ *lemma* is_lub.of_image

Modified src/order/complete_lattice.lean
- \+ *lemma* is_glb_binfi
- \+ *lemma* is_lub_bsupr



## [2020-05-13 03:44:20](https://github.com/leanprover-community/mathlib/commit/51e2b4c)
feat(topology/separation): add `subtype.t1_space` and `subtype.regular` ([#2667](https://github.com/leanprover-community/mathlib/pull/2667))
Also simplify the proof of `exists_open_singleton_of_fintype`
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.filter_ssubset

Modified src/topology/separation.lean
- \+ *theorem* exists_open_singleton_of_open_finset



## [2020-05-13 03:44:18](https://github.com/leanprover-community/mathlib/commit/4857284)
feat(topology/bounded_continuous_function): the normed space C^0 ([#2660](https://github.com/leanprover-community/mathlib/pull/2660))
For β a normed (vector) space over a nondiscrete normed field 𝕜, we construct the normed 𝕜-space structure on the set of bounded continuous functions from a topological space into β.
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* bounded_continuous_function.dist_eq
- \+/\- *lemma* bounded_continuous_function.dist_set_exists
- \+ *lemma* bounded_continuous_function.norm_eq
- \+ *lemma* bounded_continuous_function.norm_smul
- \+ *lemma* bounded_continuous_function.norm_smul_le



## [2020-05-13 01:57:37](https://github.com/leanprover-community/mathlib/commit/cbffb34)
feat(analysis/specific_limits): more geometric series ([#2658](https://github.com/leanprover-community/mathlib/pull/2658))
Currently, the sum of a geometric series is only known for real numbers in `[0,1)`. We prove it for any element of a normed field with norm `< 1`, and specialize it to real numbers in `(-1, 1)`.
Some lemmas in `analysis/specific_limits` are also moved around (but their content is not changed) to get a better organization of this file.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.tendsto.div_const
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable_norm

Modified src/analysis/specific_limits.lean
- \- *lemma* has_sum_geometric
- \+ *lemma* has_sum_geometric_of_abs_lt_1
- \+ *lemma* has_sum_geometric_of_lt_1
- \+ *lemma* has_sum_geometric_of_norm_lt_1
- \- *lemma* summable_geometric
- \+ *lemma* summable_geometric_of_abs_lt_1
- \+ *lemma* summable_geometric_of_lt_1
- \+ *lemma* summable_geometric_of_norm_lt_1
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_abs_lt_1
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1_normed_field
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_norm_lt_1
- \- *lemma* tsum_geometric
- \+ *lemma* tsum_geometric_of_abs_lt_1
- \+ *lemma* tsum_geometric_of_lt_1
- \+ *lemma* tsum_geometric_of_norm_lt_1

Modified src/data/real/cardinality.lean




## [2020-05-12 18:35:33](https://github.com/leanprover-community/mathlib/commit/437fdaf)
feat(category_theory/creates): creates limits => preserves limits ([#2639](https://github.com/leanprover-community/mathlib/pull/2639))
Show that `F` preserves limits if it creates them and the target category has them.
#### Estimated changes
Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso
- \- *def* category_theory.limits.is_colimit.cone_point_unique_up_to_iso

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/equalizers.lean




## [2020-05-12 15:37:33](https://github.com/leanprover-community/mathlib/commit/1141533)
feat(data/matrix): matrix and vector notation ([#2656](https://github.com/leanprover-community/mathlib/pull/2656))
This PR adds notation for matrices and vectors [as discussed on Zulip a couple of months ago](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20matrices.20and.20vectors), so that `![![a, b], ![c, d]]` constructs a 2x2 matrix with rows `![a, b] : fin 2 -> α` and `![c, d]`. It also adds corresponding `simp` lemmas for all matrix operations defined in `data.matrix.basic`. These lemmas should apply only when the input already contains `![...]`.
To express the `simp` lemmas nicely, I defined a function `dot_product : (v w : n -> α) -> α` which returns the sum of the entrywise product of two vectors. IMO, this makes the definitions of `matrix.mul`, `matrix.mul_vec` and `matrix.vec_mul` clearer, and it allows us to share some proofs. I could also inline `dot_product` (restoring the old situation) if the reviewers prefer.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.add_dot_product
- \+ *lemma* matrix.diagonal_dot_product
- \+ *lemma* matrix.diagonal_transpose
- \+ *def* matrix.dot_product
- \+ *lemma* matrix.dot_product_add
- \+ *lemma* matrix.dot_product_assoc
- \+ *lemma* matrix.dot_product_comm
- \+ *lemma* matrix.dot_product_diagonal'
- \+ *lemma* matrix.dot_product_diagonal
- \+ *lemma* matrix.dot_product_neg
- \+ *lemma* matrix.dot_product_punit
- \+ *lemma* matrix.dot_product_smul
- \+ *lemma* matrix.dot_product_zero'
- \+ *lemma* matrix.dot_product_zero
- \+ *lemma* matrix.mul_vec_neg
- \+ *lemma* matrix.neg_dot_product
- \+ *lemma* matrix.neg_mul_vec
- \+ *lemma* matrix.neg_vec_mul
- \+ *lemma* matrix.row_mul_col_val
- \+ *lemma* matrix.smul_dot_product
- \+ *lemma* matrix.vec_mul_neg
- \+ *lemma* matrix.zero_dot_product'
- \+ *lemma* matrix.zero_dot_product

Added src/data/matrix/notation.lean
- \+ *lemma* matrix.add_cons
- \+ *lemma* matrix.col_cons
- \+ *lemma* matrix.col_empty
- \+ *lemma* matrix.cons_add
- \+ *lemma* matrix.cons_dot_product
- \+ *lemma* matrix.cons_eq_zero_iff
- \+ *lemma* matrix.cons_head_tail
- \+ *lemma* matrix.cons_mul
- \+ *lemma* matrix.cons_mul_vec
- \+ *lemma* matrix.cons_nonzero_iff
- \+ *lemma* matrix.cons_transpose
- \+ *lemma* matrix.cons_val'
- \+ *lemma* matrix.cons_val_fin_one
- \+ *lemma* matrix.cons_val_one
- \+ *lemma* matrix.cons_val_succ'
- \+ *lemma* matrix.cons_val_succ
- \+ *lemma* matrix.cons_val_zero'
- \+ *lemma* matrix.cons_val_zero
- \+ *lemma* matrix.cons_vec_mul
- \+ *lemma* matrix.cons_vec_mul_vec
- \+ *lemma* matrix.cons_zero_zero
- \+ *lemma* matrix.dot_product_cons
- \+ *lemma* matrix.dot_product_empty
- \+ *lemma* matrix.empty_add_empty
- \+ *lemma* matrix.empty_eq
- \+ *lemma* matrix.empty_mul
- \+ *lemma* matrix.empty_mul_empty
- \+ *lemma* matrix.empty_mul_vec
- \+ *lemma* matrix.empty_val'
- \+ *lemma* matrix.empty_vec_mul
- \+ *lemma* matrix.empty_vec_mul_vec
- \+ *lemma* matrix.head_cons
- \+ *lemma* matrix.head_transpose
- \+ *lemma* matrix.head_val'
- \+ *lemma* matrix.head_zero
- \+ *lemma* matrix.minor_cons_row
- \+ *lemma* matrix.minor_empty
- \+ *lemma* matrix.mul_empty
- \+ *lemma* matrix.mul_val_succ
- \+ *lemma* matrix.mul_vec_cons
- \+ *lemma* matrix.mul_vec_empty
- \+ *lemma* matrix.neg_cons
- \+ *lemma* matrix.neg_empty
- \+ *lemma* matrix.row_cons
- \+ *lemma* matrix.row_empty
- \+ *lemma* matrix.smul_cons
- \+ *lemma* matrix.smul_empty
- \+ *lemma* matrix.tail_cons
- \+ *lemma* matrix.tail_transpose
- \+ *lemma* matrix.tail_val'
- \+ *lemma* matrix.tail_zero
- \+ *lemma* matrix.transpose_empty_cols
- \+ *lemma* matrix.transpose_empty_rows
- \+ *def* matrix.vec_cons
- \+ *def* matrix.vec_empty
- \+ *def* matrix.vec_head
- \+ *lemma* matrix.vec_mul_cons
- \+ *lemma* matrix.vec_mul_empty
- \+ *lemma* matrix.vec_mul_vec_cons
- \+ *lemma* matrix.vec_mul_vec_empty
- \+ *def* matrix.vec_tail
- \+ *lemma* matrix.zero_empty

Modified src/data/matrix/pequiv.lean


Added test/matrix.lean




## [2020-05-12 15:37:31](https://github.com/leanprover-community/mathlib/commit/34a0c8c)
chore(*): unify use of left and right for injectivity lemmas ([#2655](https://github.com/leanprover-community/mathlib/pull/2655))
This is the evil twin of [#2652](https://github.com/leanprover-community/mathlib/pull/2652) using the opposite convention: the name of a lemma stating that a function in two arguments is injective in one of the arguments refers to the argument that changes. Example:
```lean
lemma sub_right_inj : a - b = a - c ↔ b = c
```
See also the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/pow_(left.7Cright)_inj(ective)).
This PR renames lemmas following the other convention. The following lemmas were renamed:
`algebra/group/basic.lean`:
* `mul_left_injective` ↔ `mul_right_injective`
* `mul_left_inj` ↔ `mul_right_inj`
* `sub_left_inj` ↔ `sub_right_inj`
`algebra/goup/units.lean`:
* `mul_left_inj` ↔ `mul_right_inj`
* `divp_right_inj` → `divp_left_inj`
`algebra/group_power.lean`:
* `pow_right_inj` → `pow_left_inj`
`algebra/group_with_zero.lean`:
* `div_right_inj'` → ` div_left_inj'`
* `mul_right_inj'` → `mul_left_inj'`
`algebra/ring.lean`:
* `domain.mul_right_inj` ↔ `domain.mul_left_inj`
`data/finsupp.lean`:
* `single_right_inj` → `single_left_inj`
`data/list/basic.lean`:
* `append_inj_left` ↔ `append_inj_right`
* `append_inj_left'` ↔ `append_inj_right'`
* `append_left_inj` ↔ `append_right_inj`
* `prefix_append_left_inj` → `prefix_append_right_inj`
`data/nat/basic.lean`:
* `mul_left_inj` ↔ `mul_right_inj`
`data/real/ennreal.lean`:
* `add_left_inj` ↔ `add_right_inj`
* `sub_left_inj` → `sub_right_inj`
`set_theory/ordinal.lean`:
* `mul_left_inj` → `mul_right_inj`
#### Estimated changes
Modified docs/contribute/naming.md


Modified src/algebra/associated.lean


Modified src/algebra/char_p.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/gcd_domain.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_right_injective
- \+/\- *lemma* sub_left_inj
- \+/\- *lemma* sub_right_inj

Modified src/algebra/group/units.lean
- \+ *theorem* divp_left_inj
- \- *theorem* divp_right_inj
- \+/\- *theorem* units.mul_left_inj
- \+/\- *theorem* units.mul_right_inj

Modified src/algebra/group_power.lean
- \+ *theorem* pow_left_inj
- \- *theorem* pow_right_inj

Modified src/algebra/group_with_zero.lean
- \+ *lemma* div_left_inj'
- \- *lemma* div_right_inj'
- \+ *lemma* mul_left_inj'
- \- *lemma* mul_right_inj'

Modified src/algebra/ring.lean
- \+/\- *theorem* domain.mul_left_inj
- \+/\- *theorem* domain.mul_right_inj

Modified src/analysis/convex/basic.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/combinatorics/composition.lean


Modified src/data/complex/exponential.lean


Modified src/data/finsupp.lean
- \+ *lemma* finsupp.single_left_inj
- \- *lemma* finsupp.single_right_inj

Modified src/data/fintype/basic.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.append_inj_left'
- \+/\- *theorem* list.append_inj_left
- \+/\- *theorem* list.append_inj_right'
- \+/\- *theorem* list.append_inj_right
- \+/\- *theorem* list.append_left_inj
- \+/\- *theorem* list.append_right_inj
- \- *theorem* list.prefix_append_left_inj
- \+ *theorem* list.prefix_append_right_inj

Modified src/data/nat/basic.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/totient.lean


Modified src/data/pnat/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_left_inj
- \+/\- *lemma* ennreal.add_right_inj
- \- *lemma* ennreal.sub_left_inj
- \+ *lemma* ennreal.sub_right_inj

Modified src/field_theory/finite.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/determinant.lean


Modified src/measure_theory/integration.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/game/domineering.lean


Modified src/set_theory/ordinal.lean
- \- *theorem* ordinal.mul_left_inj
- \+ *theorem* ordinal.mul_right_inj

Modified src/tactic/omega/eq_elim.lean


Modified src/topology/algebra/infinite_sum.lean




## [2020-05-12 15:37:29](https://github.com/leanprover-community/mathlib/commit/77b3d50)
chore(topology/instances/ennreal): add +1 version of `tsum_eq_supr_sum` ([#2633](https://github.com/leanprover-community/mathlib/pull/2633))
Also add a few lemmas about `supr` and monotone functions.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_mono_set
- \+ *lemma* finset.sum_mono_set_of_nonneg

Modified src/measure_theory/integration.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* le_infi_comp
- \+ *lemma* monotone.infi_comp_eq
- \+ *lemma* monotone.le_map_supr2
- \+ *lemma* monotone.le_map_supr
- \- *lemma* monotone.map_supr2_ge
- \- *lemma* monotone.map_supr_ge
- \+ *lemma* monotone.supr_comp_eq
- \+ *lemma* supr_comp_le

Modified src/topology/instances/ennreal.lean




## [2020-05-12 15:37:27](https://github.com/leanprover-community/mathlib/commit/ff184e6)
feat(analysis/normed_space): add Mazur-Ulam theorem ([#2214](https://github.com/leanprover-community/mathlib/pull/2214))
Based on a proof by Jussi Väisälä, see [journal version](https://www.jstor.org/stable/3647749) or [preprint on web.archive](https://web.archive.org/web/20180516125105/http://www.helsinki.fi/~jvaisala/mazurulam.pdf).
Also rename `reflection` to `point_reflection` as was suggested by @rwbarton and @PatrickMassot
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/midpoint.lean
- \+ *lemma* equiv.point_reflection_midpoint_left
- \+ *lemma* equiv.point_reflection_midpoint_right
- \- *lemma* equiv.reflection_midpoint_left
- \- *lemma* equiv.reflection_midpoint_right

Added src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* isometric.coe_to_real_linear_equiv_of_map_zero
- \+ *lemma* isometric.coe_to_real_linear_equiv_of_map_zero_symm
- \+ *lemma* isometric.map_midpoint
- \+ *lemma* isometric.midpoint_fixed
- \+ *def* isometric.to_real_linear_equiv
- \+ *lemma* isometric.to_real_linear_equiv_apply
- \+ *def* isometric.to_real_linear_equiv_of_map_zero
- \+ *lemma* isometric.to_real_linear_equiv_symm_apply

Added src/analysis/normed_space/point_reflection.lean
- \+ *lemma* equiv.point_reflection_fixed_iff_of_module
- \+ *def* isometric.point_reflection
- \+ *lemma* isometric.point_reflection_apply
- \+ *lemma* isometric.point_reflection_dist_fixed
- \+ *lemma* isometric.point_reflection_dist_self'
- \+ *lemma* isometric.point_reflection_dist_self
- \+ *lemma* isometric.point_reflection_dist_self_real
- \+ *lemma* isometric.point_reflection_fixed_iff
- \+ *lemma* isometric.point_reflection_involutive
- \+ *lemma* isometric.point_reflection_midpoint_left
- \+ *lemma* isometric.point_reflection_midpoint_right
- \+ *lemma* isometric.point_reflection_self
- \+ *lemma* isometric.point_reflection_symm
- \+ *lemma* isometric.point_reflection_to_equiv

Modified src/analysis/normed_space/real_inner_product.lean


Deleted src/analysis/normed_space/reflection.lean
- \- *lemma* equiv.reflection_fixed_iff_of_module
- \- *def* isometric.reflection
- \- *lemma* isometric.reflection_apply
- \- *lemma* isometric.reflection_dist_fixed
- \- *lemma* isometric.reflection_dist_self'
- \- *lemma* isometric.reflection_dist_self
- \- *lemma* isometric.reflection_dist_self_real
- \- *lemma* isometric.reflection_fixed_iff
- \- *lemma* isometric.reflection_involutive
- \- *lemma* isometric.reflection_midpoint_left
- \- *lemma* isometric.reflection_midpoint_right
- \- *lemma* isometric.reflection_self
- \- *lemma* isometric.reflection_symm
- \- *lemma* isometric.reflection_to_equiv

Modified src/data/equiv/mul_add.lean
- \+ *def* equiv.point_reflection
- \+ *lemma* equiv.point_reflection_apply
- \+ *lemma* equiv.point_reflection_fixed_iff_of_bit0_inj
- \+ *lemma* equiv.point_reflection_involutive
- \+ *lemma* equiv.point_reflection_self
- \+ *lemma* equiv.point_reflection_symm
- \- *def* equiv.reflection
- \- *lemma* equiv.reflection_apply
- \- *lemma* equiv.reflection_fixed_iff_of_bit0_inj
- \- *lemma* equiv.reflection_involutive
- \- *lemma* equiv.reflection_self
- \- *lemma* equiv.reflection_symm

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* cinfi_le
- \+/\- *lemma* le_csupr

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.add_left_symm
- \+ *lemma* isometric.add_left_to_equiv
- \+ *lemma* isometric.add_right_apply
- \+ *lemma* isometric.add_right_symm
- \+ *lemma* isometric.add_right_to_equiv
- \+ *lemma* isometric.coe_add_left
- \+ *lemma* isometric.coe_add_right
- \+ *lemma* isometric.coe_neg
- \+ *lemma* isometric.neg_symm
- \+ *lemma* isometric.neg_to_equiv
- \+ *lemma* isometric.symm_symm
- \+ *lemma* isometric.symm_trans_apply



## [2020-05-12 13:39:55](https://github.com/leanprover-community/mathlib/commit/3f216bc)
feat(number_theory/basic): dvd_sub_pow_of_dvd_sub ([#2640](https://github.com/leanprover-community/mathlib/pull/2640))
Co-authored with: Kenny Lau <kc_kennylau@yahoo.com.hk>
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \+ *theorem* geom_series₂_self
- \+ *theorem* ring_hom.map_geom_series
- \+ *theorem* ring_hom.map_geom_series₂

Added src/number_theory/basic.lean
- \+ *lemma* dvd_sub_pow_of_dvd_sub

Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.quotient.mk_eq_mk_hom



## [2020-05-12 11:31:31](https://github.com/leanprover-community/mathlib/commit/61b59ec)
fix(order/filter/basic): markdown error in module doc ([#2664](https://github.com/leanprover-community/mathlib/pull/2664))
#### Estimated changes
Modified src/order/filter/basic.lean




## [2020-05-12 06:37:08](https://github.com/leanprover-community/mathlib/commit/295b87e)
feat(ring_theory/integral_domain): sum in integral domain indexed by finite group ([#2623](https://github.com/leanprover-community/mathlib/pull/2623))
In other words: nontrivial sums are trivial
Moved from `field_theory.finite` to the new `ring_theory.integral_domain`:
- `card_nth_roots_subgroup_units`
- `subgroup_units_cyclic`
#### Estimated changes
Modified src/algebra/group/units_hom.lean
- \+ *lemma* monoid_hom.coe_to_hom_units
- \+ *def* monoid_hom.to_hom_units

Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_subtype

Modified src/field_theory/finite.lean
- \- *lemma* card_nth_roots_subgroup_units

Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_cyclic.exists_monoid_generator

Added src/ring_theory/integral_domain.lean
- \+ *lemma* card_fiber_eq_of_mem_range
- \+ *lemma* card_nth_roots_subgroup_units
- \+ *lemma* sum_hom_units
- \+ *lemma* sum_hom_units_eq_zero



## [2020-05-12 05:22:17](https://github.com/leanprover-community/mathlib/commit/f0e7817)
chore(scripts): update nolints.txt ([#2662](https://github.com/leanprover-community/mathlib/pull/2662))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-12 01:24:40](https://github.com/leanprover-community/mathlib/commit/8c88721)
feat(data/list): assorted lemmas ([#2651](https://github.com/leanprover-community/mathlib/pull/2651))
Some lemmas I found useful for [#2578](https://github.com/leanprover-community/mathlib/pull/2578)
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.cons_head'_tail
- \+ *theorem* list.head_mem_head'
- \+ *theorem* list.ilast_eq_last'
- \+ *theorem* list.init_append_last'
- \+ *lemma* list.is_nil_iff_eq_nil
- \+ *theorem* list.last'_append_cons
- \+ *theorem* list.last'_append_of_ne_nil
- \+ *theorem* list.last'_is_none
- \+ *theorem* list.last'_is_some
- \+/\- *theorem* list.last_cons
- \+ *theorem* list.last_mem
- \+ *theorem* list.mem_last'_eq_last
- \+ *theorem* list.mem_of_mem_head'
- \+ *theorem* list.mem_of_mem_last'
- \+ *theorem* list.prod_eq_foldr

Modified src/data/list/chain.lean
- \+ *theorem* list.chain'.append
- \+ *theorem* list.chain'.cons'
- \+ *theorem* list.chain'.imp_head
- \+ *theorem* list.chain'.rel_head'
- \+ *theorem* list.chain'.rel_head
- \+ *theorem* list.chain'_cons'

Modified src/data/list/defs.lean




## [2020-05-11 13:23:56](https://github.com/leanprover-community/mathlib/commit/eb9e382)
test(tactic/norm_num): import tests from lean core ([#2654](https://github.com/leanprover-community/mathlib/pull/2654))
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2020-05-11 11:46:09](https://github.com/leanprover-community/mathlib/commit/a87f326)
chore(scripts): update nolints.txt ([#2653](https://github.com/leanprover-community/mathlib/pull/2653))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-11 09:42:50](https://github.com/leanprover-community/mathlib/commit/e777d0b)
refactor(data/real/pi): add tactics for pi computation ([#2641](https://github.com/leanprover-community/mathlib/pull/2641))
Depends on [#2589](https://github.com/leanprover-community/mathlib/pull/2589). Moves pi bounds from @fpvandoorn's gist to mathlib, and also adds a small tactic to uniformize the proofs (and also skip some unsqueezed proofs), making the compilation even faster (just around 1 second for the longest proofs).
#### Estimated changes
Modified src/data/real/pi.lean
- \+ *lemma* real.pi_gt_3141592
- \+ *lemma* real.pi_gt_31415
- \+/\- *lemma* real.pi_gt_314
- \+/\- *lemma* real.pi_gt_three
- \+ *theorem* real.pi_lower_bound_start
- \+ *lemma* real.pi_lt_3141593
- \+ *lemma* real.pi_lt_31416
- \+/\- *lemma* real.pi_lt_315
- \+ *theorem* real.pi_upper_bound_start
- \+/\- *lemma* real.sqrt_two_add_series_step_down
- \+/\- *lemma* real.sqrt_two_add_series_step_up



## [2020-05-11 06:32:55](https://github.com/leanprover-community/mathlib/commit/ff37fb8)
feat(algebra/ring): monoid structure on `R →+* R` ([#2649](https://github.com/leanprover-community/mathlib/pull/2649))
Also add `comp_id` and `id_comp`
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* ring_hom.coe_pow

Modified src/algebra/ring.lean
- \+ *lemma* ring_hom.coe_mul
- \+ *lemma* ring_hom.coe_one
- \+ *lemma* ring_hom.comp_id
- \+ *lemma* ring_hom.id_comp
- \+/\- *def* ring_hom.mk'
- \+ *lemma* ring_hom.mul_def
- \+ *lemma* ring_hom.one_def



## [2020-05-11 03:53:42](https://github.com/leanprover-community/mathlib/commit/7146082)
refactor(data/fintype/basic): weaken assumptions of set.fintype ([#2650](https://github.com/leanprover-community/mathlib/pull/2650))
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2020-05-10 20:24:02](https://github.com/leanprover-community/mathlib/commit/b9bdc67)
feat(*): prove some `*.iterate` theorems ([#2647](https://github.com/leanprover-community/mathlib/pull/2647))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/order/basic.lean
- \+ *lemma* strict_mono_id

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.coe_mul
- \+/\- *lemma* continuous_linear_map.mul_apply
- \+ *lemma* continuous_linear_map.mul_def
- \+ *lemma* continuous_linear_map.smul_right_one_pow

Modified src/topology/basic.lean
- \+ *lemma* continuous.iterate
- \+ *lemma* continuous_at.iterate



## [2020-05-10 17:09:22](https://github.com/leanprover-community/mathlib/commit/8c6b14e)
fix(library_search): use custom apply tactic for the main goal, as well as subgoals ([#2648](https://github.com/leanprover-community/mathlib/pull/2648))
cf https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/List.20lemmas
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean
- \+ *lemma* test.library_search.bind_singleton



## [2020-05-10 07:14:07](https://github.com/leanprover-community/mathlib/commit/3710744)
feat(meta/uchange): universe lifting and lowering in meta ([#2627](https://github.com/leanprover-community/mathlib/pull/2627))
We define the meta type `uchange (α : Type v) : Type u`, which permits us to change the universe of a type analogously to `ulift`.  However since `uchange` is meta, it can both lift and lower the universe.
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/widget/near/196808542
#### Estimated changes
Added src/meta/uchange.lean




## [2020-05-10 04:05:15](https://github.com/leanprover-community/mathlib/commit/b248481)
chore(algebra/char_zero): add `∀ n : ℕ, (n + 1 : α) ≠ 0` ([#2644](https://github.com/leanprover-community/mathlib/pull/2644))
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* nat.cast_add_one_ne_zero



## [2020-05-10 04:05:14](https://github.com/leanprover-community/mathlib/commit/7590090)
chore(scripts): update nolints.txt ([#2643](https://github.com/leanprover-community/mathlib/pull/2643))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-10 00:45:41](https://github.com/leanprover-community/mathlib/commit/81f97bd)
chore(*): move to lean-3.11.0 ([#2632](https://github.com/leanprover-community/mathlib/pull/2632))
Related Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/lean.23211.20don't.20unfold.20irred.20defs
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/opposites.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/yoneda.lean


Modified src/data/array/lemmas.lean


Modified src/data/complex/basic.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pfun.lean


Modified src/data/polynomial.lean
- \+/\- *def* polynomial.pow_sub_pow_factor

Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.infinitesimal_add
- \+/\- *lemma* hyperreal.infinitesimal_mul
- \+/\- *lemma* hyperreal.infinitesimal_neg

Modified src/geometry/manifold/real_instances.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/set_theory/cofinality.lean


Modified src/topology/metric_space/emetric_space.lean




## [2020-05-09 23:30:16](https://github.com/leanprover-community/mathlib/commit/a584d52)
chore(scripts): update nolints.txt ([#2642](https://github.com/leanprover-community/mathlib/pull/2642))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-09 20:30:31](https://github.com/leanprover-community/mathlib/commit/9f33b7d)
feat(algebra/ordered_*): arithmetic operations on monotone functions ([#2634](https://github.com/leanprover-community/mathlib/pull/2634))
Also move `strict_mono` to `order/basic` and add a module docstring.
#### Estimated changes
Modified src/algebra/order_functions.lean
- \- *lemma* monotone_mul_left_of_nonneg
- \- *lemma* monotone_mul_right_of_nonneg
- \- *theorem* strict_mono.compares
- \- *lemma* strict_mono.injective
- \- *lemma* strict_mono.le_iff_le
- \- *lemma* strict_mono.lt_iff_lt
- \- *lemma* strict_mono.monotone
- \- *def* strict_mono
- \- *lemma* strict_mono_of_monotone_of_injective

Modified src/algebra/ordered_field.lean
- \+ *lemma* monotone.div_const
- \+ *lemma* strict_mono.div_const

Modified src/algebra/ordered_group.lean
- \+ *lemma* monotone.add
- \+ *lemma* monotone.add_const
- \+ *lemma* monotone.add_strict_mono
- \+ *lemma* monotone.const_add
- \+ *lemma* strict_mono.add_monotone

Modified src/algebra/ordered_ring.lean
- \+ *lemma* monotone.const_mul
- \+ *lemma* monotone.mul
- \+ *lemma* monotone.mul_const
- \+ *lemma* monotone.mul_strict_mono
- \+ *lemma* monotone_mul_left_of_nonneg
- \+ *lemma* monotone_mul_right_of_nonneg
- \+ *lemma* strict_mono.const_mul
- \+ *lemma* strict_mono.mul
- \+ *lemma* strict_mono.mul_const
- \+ *lemma* strict_mono.mul_monotone
- \+ *lemma* strict_mono_mul_left_of_pos
- \+ *lemma* strict_mono_mul_right_of_pos

Modified src/order/basic.lean
- \+ *lemma* strict_mono.comp
- \+ *theorem* strict_mono.compares
- \+ *lemma* strict_mono.injective
- \+ *lemma* strict_mono.le_iff_le
- \+ *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_mono.monotone
- \+ *def* strict_mono
- \+ *lemma* strict_mono_of_monotone_of_injective



## [2020-05-09 20:30:29](https://github.com/leanprover-community/mathlib/commit/d04429f)
chore(logic/embedding,order/order_iso): review ([#2618](https://github.com/leanprover-community/mathlib/pull/2618))
* swap `inj` with `inj'` to match other bundled homomorphisms;
* make some arguments explicit to avoid `embedding.of_surjective _`
  in the pretty printer output;
* make `set_value` computable.
#### Estimated changes
Modified src/computability/turing_machine.lean


Modified src/data/finset.lean


Modified src/data/finsupp.lean


Modified src/data/pnat/intervals.lean


Modified src/data/set/countable.lean


Modified src/data/setoid.lean


Modified src/group_theory/congruence.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/dimension.lean


Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.coe_image
- \- *theorem* function.embedding.inj'
- \+ *theorem* function.embedding.inj
- \+ *def* function.embedding.set_value
- \+/\- *theorem* function.embedding.set_value_eq
- \+ *lemma* set.coe_embedding_of_subset_apply
- \+/\- *def* set.embedding_of_subset
- \+ *lemma* set.embedding_of_subset_apply_mk

Modified src/order/galois_connection.lean


Modified src/order/order_iso.lean
- \+ *theorem* order_embedding.inj
- \- *theorem* order_embedding.ord'
- \+ *theorem* order_embedding.ord
- \- *theorem* order_iso.ord'
- \+ *theorem* order_iso.ord
- \+ *lemma* order_iso.to_order_embedding_eq_coe

Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean




## [2020-05-09 20:30:27](https://github.com/leanprover-community/mathlib/commit/08d4316)
refactor(computability/turing_machine): add list_blank ([#2605](https://github.com/leanprover-community/mathlib/pull/2605))
This ended up being a major refactor of `computability.turing_machine`. It started as a change of the definition of turing machine so that the tape is a quotient of lists up to the relation "ends with blanks", but the file is quite old and I updated it to pass the linter as well. I'm not up to speed on the new documentation requirements, but now is a good time to request them for this file. This doesn't add many new theorems, it's mostly just fixes to make it compile again after the change. (Some of the turing machine constructions are also simplified.)
#### Estimated changes
Modified src/computability/turing_machine.lean
- \+/\- *def* turing.TM0.cfg.map
- \+/\- *def* turing.TM0.eval
- \+/\- *theorem* turing.TM0.machine.map_respects
- \+/\- *theorem* turing.TM0.machine.map_step
- \+/\- *theorem* turing.TM0.map_init
- \+/\- *def* turing.TM0.stmt.map
- \+/\- *def* turing.TM1.eval
- \+/\- *def* turing.TM1to1.tr_tape'
- \+/\- *def* turing.TM1to1.tr_tape
- \- *theorem* turing.TM1to1.tr_tape_drop_right
- \+ *theorem* turing.TM1to1.tr_tape_mk'
- \- *theorem* turing.TM1to1.tr_tape_take_right
- \+ *def* turing.TM2to1.add_bottom
- \+ *theorem* turing.TM2to1.add_bottom_head_fst
- \+ *theorem* turing.TM2to1.add_bottom_map
- \+ *theorem* turing.TM2to1.add_bottom_modify_nth
- \+ *theorem* turing.TM2to1.add_bottom_nth_snd
- \+ *theorem* turing.TM2to1.add_bottom_nth_succ_fst
- \- *def* turing.TM2to1.stackel.get
- \- *def* turing.TM2to1.stackel.is_bottom
- \- *def* turing.TM2to1.stackel.is_top
- \- *def* turing.TM2to1.stackel_equiv
- \+ *theorem* turing.TM2to1.stk_nth_val
- \+/\- *theorem* turing.TM2to1.supports_run
- \+/\- *theorem* turing.TM2to1.tr_normal_run
- \+/\- *theorem* turing.TM2to1.tr_respects_aux₁
- \+/\- *theorem* turing.TM2to1.tr_respects_aux₃
- \- *def* turing.TM2to1.tr_stk
- \+/\- *theorem* turing.TM2to1.tr_stmts₁_run
- \+/\- *def* turing.TM2to1.Γ'
- \+ *def* turing.blank_extends.above
- \+ *theorem* turing.blank_extends.above_of_le
- \+ *theorem* turing.blank_extends.below_of_le
- \+ *theorem* turing.blank_extends.refl
- \+ *theorem* turing.blank_extends.trans
- \+ *def* turing.blank_extends
- \+ *def* turing.blank_rel.above
- \+ *def* turing.blank_rel.below
- \+ *theorem* turing.blank_rel.equivalence
- \+ *theorem* turing.blank_rel.refl
- \+ *def* turing.blank_rel.setoid
- \+ *theorem* turing.blank_rel.symm
- \+ *theorem* turing.blank_rel.trans
- \+ *def* turing.blank_rel
- \- *def* turing.dwrite
- \- *theorem* turing.dwrite_eq
- \- *theorem* turing.dwrite_ne
- \- *theorem* turing.dwrite_self
- \+ *def* turing.list_blank.append
- \+ *theorem* turing.list_blank.append_assoc
- \+ *theorem* turing.list_blank.append_mk
- \+ *def* turing.list_blank.bind
- \+ *lemma* turing.list_blank.bind_mk
- \+ *def* turing.list_blank.cons
- \+ *lemma* turing.list_blank.cons_bind
- \+ *theorem* turing.list_blank.cons_head_tail
- \+ *theorem* turing.list_blank.cons_mk
- \+ *theorem* turing.list_blank.exists_cons
- \+ *theorem* turing.list_blank.ext
- \+ *def* turing.list_blank.head
- \+ *theorem* turing.list_blank.head_cons
- \+ *theorem* turing.list_blank.head_map
- \+ *theorem* turing.list_blank.head_mk
- \+ *def* turing.list_blank.map
- \+ *theorem* turing.list_blank.map_cons
- \+ *theorem* turing.list_blank.map_mk
- \+ *theorem* turing.list_blank.map_modify_nth
- \+ *def* turing.list_blank.mk
- \+ *def* turing.list_blank.modify_nth
- \+ *def* turing.list_blank.nth
- \+ *theorem* turing.list_blank.nth_map
- \+ *theorem* turing.list_blank.nth_mk
- \+ *theorem* turing.list_blank.nth_modify_nth
- \+ *theorem* turing.list_blank.nth_succ
- \+ *theorem* turing.list_blank.nth_zero
- \+ *def* turing.list_blank.tail
- \+ *theorem* turing.list_blank.tail_cons
- \+ *theorem* turing.list_blank.tail_map
- \+ *theorem* turing.list_blank.tail_mk
- \+ *def* turing.list_blank
- \+ *theorem* turing.pointed_map.head_map
- \+ *theorem* turing.pointed_map.map_pt
- \+ *theorem* turing.pointed_map.mk_val
- \- *def* turing.pointed_map
- \+ *def* turing.proj
- \+ *theorem* turing.proj_map_nth
- \+ *theorem* turing.tape.exists_mk'
- \+ *def* turing.tape.left₀
- \+/\- *def* turing.tape.map
- \+/\- *theorem* turing.tape.map_fst
- \+ *theorem* turing.tape.map_mk'
- \- *theorem* turing.tape.map_mk
- \+ *theorem* turing.tape.map_mk₁
- \+ *theorem* turing.tape.map_mk₂
- \+/\- *theorem* turing.tape.map_write
- \+/\- *def* turing.tape.mk'
- \+ *theorem* turing.tape.mk'_head
- \+ *theorem* turing.tape.mk'_left
- \+ *theorem* turing.tape.mk'_left_right₀
- \+ *theorem* turing.tape.mk'_nth_nat
- \+ *theorem* turing.tape.mk'_right
- \+ *theorem* turing.tape.mk'_right₀
- \- *def* turing.tape.mk
- \+ *def* turing.tape.mk₁
- \+ *def* turing.tape.mk₂
- \+ *theorem* turing.tape.move_left_mk'
- \+ *theorem* turing.tape.move_left_right
- \+ *theorem* turing.tape.move_right_left
- \+ *theorem* turing.tape.move_right_mk'
- \+ *theorem* turing.tape.move_right_n_head
- \+/\- *theorem* turing.tape.move_right_nth
- \+/\- *def* turing.tape.nth
- \+/\- *theorem* turing.tape.nth_zero
- \+ *def* turing.tape.right₀
- \+ *theorem* turing.tape.right₀_nth
- \+/\- *def* turing.tape.write
- \+ *theorem* turing.tape.write_mk'
- \+ *theorem* turing.tape.write_move_right_n
- \+/\- *theorem* turing.tape.write_self
- \- *def* turing.tape

Modified src/data/list/basic.lean
- \+ *theorem* list.head'_map
- \- *lemma* list.nth_concat_length:
- \+ *lemma* list.nth_concat_length

Modified src/data/nat/basic.lean
- \+ *theorem* nat.add_sub_eq_max



## [2020-05-09 20:30:25](https://github.com/leanprover-community/mathlib/commit/b769846)
feat(tactic/norm_num): new all-lean norm_num ([#2589](https://github.com/leanprover-community/mathlib/pull/2589))
This is a first draft of the lean replacement for `tactic.norm_num` in core. This isn't completely polished yet; the rest of `norm_num` can now be a little less "global-recursive" since the primitives for e.g. adding and multiplying natural numbers are exposed.
I'm also trying out a new approach using functions like `match_neg` and `match_numeral` instead of directly pattern matching on exprs, because this generates smaller (and hopefully more efficient) code. (Without this, some of the matches were hitting the equation compiler depth limit.)
I'm open to new feature suggestions as well here. `nat.succ` and coercions seem useful to support in the core part, and additional flexibility using `def_replacer` is also on the agenda.
#### Estimated changes
Modified src/analysis/specific_limits.lean


Modified src/data/rat/meta_defs.lean


Modified src/tactic/core.lean


Modified src/tactic/norm_num.lean
- \+ *theorem* norm_num.adc_bit0_bit0
- \+ *theorem* norm_num.adc_bit0_bit1
- \+ *theorem* norm_num.adc_bit0_one
- \+ *theorem* norm_num.adc_bit1_bit0
- \+ *theorem* norm_num.adc_bit1_bit1
- \+ *theorem* norm_num.adc_bit1_one
- \+ *theorem* norm_num.adc_one_bit0
- \+ *theorem* norm_num.adc_one_bit1
- \+ *theorem* norm_num.adc_one_one
- \+ *theorem* norm_num.adc_zero
- \+ *theorem* norm_num.add_bit0_bit0
- \+ *theorem* norm_num.add_bit0_bit1
- \+ *theorem* norm_num.add_bit1_bit0
- \+ *theorem* norm_num.add_bit1_bit1
- \+ *theorem* norm_num.add_neg_neg
- \+ *theorem* norm_num.add_neg_pos_neg
- \+ *theorem* norm_num.add_neg_pos_pos
- \+ *theorem* norm_num.add_pos_neg_neg
- \+ *theorem* norm_num.add_pos_neg_pos
- \+ *theorem* norm_num.bit0_mul
- \+ *theorem* norm_num.bit0_succ
- \- *theorem* norm_num.bit0_zero
- \+ *theorem* norm_num.bit1_succ
- \- *theorem* norm_num.bit1_zero
- \+ *theorem* norm_num.clear_denom_add
- \+ *theorem* norm_num.clear_denom_div
- \+ *theorem* norm_num.clear_denom_le
- \+ *theorem* norm_num.clear_denom_lt
- \+ *theorem* norm_num.clear_denom_mul
- \+ *theorem* norm_num.clear_denom_simple_div
- \+ *theorem* norm_num.clear_denom_simple_nat
- \+ *theorem* norm_num.div_eq
- \+ *theorem* norm_num.dvd_eq_int
- \+ *theorem* norm_num.dvd_eq_nat
- \+ *lemma* norm_num.from_nat_pow
- \+ *theorem* norm_num.int_cast_bit0
- \+ *theorem* norm_num.int_cast_bit1
- \+ *theorem* norm_num.int_cast_ne
- \+ *theorem* norm_num.int_cast_neg
- \+ *theorem* norm_num.int_cast_one
- \+ *theorem* norm_num.int_cast_zero
- \+ *lemma* norm_num.int_div
- \- *lemma* norm_num.int_div_helper
- \+ *lemma* norm_num.int_div_neg
- \+ *lemma* norm_num.int_mod
- \- *lemma* norm_num.int_mod_helper
- \+ *lemma* norm_num.int_mod_neg
- \+ *theorem* norm_num.inv_div
- \+ *theorem* norm_num.inv_div_one
- \+ *theorem* norm_num.inv_neg
- \+ *theorem* norm_num.inv_one
- \+ *theorem* norm_num.inv_one_div
- \+ *theorem* norm_num.le_bit0_bit0
- \+ *theorem* norm_num.le_bit0_bit1
- \+ *theorem* norm_num.le_bit1_bit0
- \+ *theorem* norm_num.le_bit1_bit1
- \+ *lemma* norm_num.le_neg_pos
- \+ *theorem* norm_num.le_one_bit0
- \+ *theorem* norm_num.le_one_bit1
- \- *lemma* norm_num.lt_add_of_pos_helper
- \+ *theorem* norm_num.lt_bit0_bit0
- \+ *theorem* norm_num.lt_bit0_bit1
- \+ *theorem* norm_num.lt_bit1_bit0
- \+ *theorem* norm_num.lt_bit1_bit1
- \+ *lemma* norm_num.lt_neg_pos
- \+ *theorem* norm_num.lt_one_bit0
- \+ *theorem* norm_num.lt_one_bit1
- \+/\- *lemma* norm_num.min_fac_helper_3
- \+/\- *lemma* norm_num.min_fac_helper_4
- \+ *theorem* norm_num.mul_bit0'
- \+ *theorem* norm_num.mul_bit0_bit0
- \+ *theorem* norm_num.mul_bit1_bit1
- \+ *theorem* norm_num.mul_neg_neg
- \+ *theorem* norm_num.mul_neg_pos
- \+ *theorem* norm_num.mul_pos_neg
- \+ *theorem* norm_num.nat_cast_bit0
- \+ *theorem* norm_num.nat_cast_bit1
- \+ *theorem* norm_num.nat_cast_ne
- \+ *theorem* norm_num.nat_cast_one
- \+ *theorem* norm_num.nat_cast_zero
- \+ *lemma* norm_num.nat_div
- \- *lemma* norm_num.nat_div_helper
- \+ *lemma* norm_num.nat_mod
- \- *lemma* norm_num.nat_mod_helper
- \+ *theorem* norm_num.nat_succ_eq
- \+ *theorem* norm_num.ne_zero_neg
- \+ *theorem* norm_num.ne_zero_of_pos
- \+ *theorem* norm_num.nonneg_pos
- \+ *theorem* norm_num.not_refl_false_intro
- \+ *theorem* norm_num.one_add
- \+ *theorem* norm_num.one_succ
- \+ *lemma* norm_num.pow_bit0
- \- *lemma* norm_num.pow_bit0_helper
- \+ *lemma* norm_num.pow_bit1
- \- *lemma* norm_num.pow_bit1_helper
- \+ *theorem* norm_num.rat_cast_bit0
- \+ *theorem* norm_num.rat_cast_bit1
- \+ *theorem* norm_num.rat_cast_div
- \+ *theorem* norm_num.rat_cast_ne
- \+ *theorem* norm_num.rat_cast_neg
- \+ *theorem* norm_num.sle_bit0_bit0
- \+ *theorem* norm_num.sle_bit0_bit1
- \+ *theorem* norm_num.sle_bit1_bit0
- \+ *theorem* norm_num.sle_bit1_bit1
- \+ *theorem* norm_num.sle_one_bit0
- \+ *theorem* norm_num.sle_one_bit1
- \+ *theorem* norm_num.sub_nat_neg
- \+ *theorem* norm_num.sub_nat_pos
- \+ *theorem* norm_num.sub_neg
- \+ *theorem* norm_num.sub_pos
- \+ *theorem* norm_num.zero_adc
- \+ *theorem* norm_num.zero_succ

Modified test/norm_num.lean




## [2020-05-09 17:40:41](https://github.com/leanprover-community/mathlib/commit/20c7418)
chore(data/finset): drop `to_set`, use `has_lift` instead ([#2629](https://github.com/leanprover-community/mathlib/pull/2629))
Also cleanup `coe_to_finset` lemmas. Now we have `set.finite.coe_to_finset` and `set.coe_to_finset`.
#### Estimated changes
Modified src/algebra/direct_sum.lean


Modified src/data/finset.lean
- \+ *lemma* finset.coe_injective
- \- *def* finset.to_set
- \- *lemma* finset.to_set_injective
- \- *lemma* finset.to_set_sdiff

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean
- \+ *theorem* set.coe_to_finset

Modified src/data/set/finite.lean
- \+/\- *lemma* finset.coe_preimage
- \- *lemma* finset.coe_to_finset'
- \- *lemma* finset.coe_to_finset
- \+/\- *lemma* set.finite.coe_to_finset

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/noetherian.lean


Modified src/set_theory/ordinal.lean




## [2020-05-09 14:34:49](https://github.com/leanprover-community/mathlib/commit/e1192f3)
feat(data/nat/basic): add `mod_add_mod` and `add_mod_mod` ([#2635](https://github.com/leanprover-community/mathlib/pull/2635))
Added the `mod_add_mod` and `add_mod_mod` lemmas for `data.nat.basic`. I copied them from `data.int.basic`, and just changed the data type. Would there be issues with it being labelled `@[simp]`?
Also, would it make sense to refactor `add_mod` above it to use `mod_add_mod` and `add_mod_mod`? It'd make it considerably shorter.
(Tangential note, there's a disparity between the `mod` lemmas for `nat` and the `mod` lemmas for `int`, for example `int` doesn't have `add_mod`, should that be added in a separate PR?)
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.add_mod
- \+ *lemma* int.mul_mod

Modified src/data/nat/basic.lean
- \+ *theorem* nat.add_mod_eq_add_mod_left
- \+ *theorem* nat.add_mod_eq_add_mod_right
- \+ *theorem* nat.add_mod_mod
- \+ *theorem* nat.mod_add_mod



## [2020-05-09 08:33:21](https://github.com/leanprover-community/mathlib/commit/96efc22)
feat(data/nat/cast): nat.cast_with_bot ([#2636](https://github.com/leanprover-community/mathlib/pull/2636))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/with_bot/near/196979007
#### Estimated changes
Modified src/data/nat/cast.lean
- \+ *theorem* nat.cast_with_bot



## [2020-05-08 21:01:31](https://github.com/leanprover-community/mathlib/commit/67e19cd)
feat(src/ring_theory/algebra): define equivalence of algebras ([#2625](https://github.com/leanprover-community/mathlib/pull/2625))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.apply_symm_apply
- \+ *lemma* alg_equiv.bijective
- \+ *lemma* alg_equiv.coe_ring_equiv
- \+ *lemma* alg_equiv.coe_to_alg_equiv
- \+ *lemma* alg_equiv.commutes
- \+ *lemma* alg_equiv.injective
- \+ *lemma* alg_equiv.map_add
- \+ *lemma* alg_equiv.map_mul
- \+ *lemma* alg_equiv.map_neg
- \+ *lemma* alg_equiv.map_one
- \+ *lemma* alg_equiv.map_sub
- \+ *lemma* alg_equiv.map_zero
- \+ *def* alg_equiv.refl
- \+ *lemma* alg_equiv.surjective
- \+ *def* alg_equiv.symm
- \+ *lemma* alg_equiv.symm_apply_apply
- \+ *def* alg_equiv.trans



## [2020-05-08 16:39:26](https://github.com/leanprover-community/mathlib/commit/fc8c4b9)
chore(`analysis/normed_space/banach`): minor review ([#2631](https://github.com/leanprover-community/mathlib/pull/2631))
* move comment to module docstring;
* don't import `bounded_linear_maps`;
* reuse `open_mapping` in `linear_equiv.continuous_symm`;
* add a few `simp` lemmas.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean
- \+ *lemma* linear_equiv.coe_fn_to_continuous_linear_equiv_of_continuous
- \+ *lemma* linear_equiv.coe_fn_to_continuous_linear_equiv_of_continuous_symm
- \+/\- *theorem* linear_equiv.continuous_symm
- \+/\- *def* linear_equiv.to_continuous_linear_equiv_of_continuous



## [2020-05-08 01:30:44](https://github.com/leanprover-community/mathlib/commit/ac3fb4e)
chore(scripts): update nolints.txt ([#2628](https://github.com/leanprover-community/mathlib/pull/2628))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-07 22:43:02](https://github.com/leanprover-community/mathlib/commit/a7e8039)
feat(data/equiv/encodable): `ulower` lowers countable types to `Type 0` ([#2574](https://github.com/leanprover-community/mathlib/pull/2574))
Given a type `α : Type u`, we can lift it into a higher universe using `ulift α : Type (max u v)`.  This PR introduces an analogous construction going in the other direction.  Given an encodable (= countable) type `α : Type u`, we can lower it to the very bottom using `ulower α : Type 0`.  The equivalence is primitive recursive if the type is primcodable.
The definition of the equivalence was already present as `encodable.equiv_range_encode`.  However it is very inconvenient to use since it requires decidability instances (`encodable.decidable_range_encode`) that are not enabled by default because they would introduce overlapping instances that are not definitionally equal.
#### Estimated changes
Modified src/computability/primrec.lean
- \+ *theorem* primrec.option_get
- \+ *theorem* primrec.option_get_or_else
- \+ *theorem* primrec.subtype_mk
- \+ *theorem* primrec.ulower_down
- \+ *theorem* primrec.ulower_up

Modified src/data/equiv/encodable.lean
- \+ *lemma* encodable.subtype.encode_eq
- \+ *def* ulower.down
- \+ *lemma* ulower.down_eq_down
- \+ *lemma* ulower.down_up
- \+ *def* ulower.equiv
- \+ *def* ulower.up
- \+ *lemma* ulower.up_down
- \+ *lemma* ulower.up_eq_up
- \+ *def* ulower



## [2020-05-07 21:02:37](https://github.com/leanprover-community/mathlib/commit/ed453c7)
chore(data/polynomial): remove unused argument ([#2626](https://github.com/leanprover-community/mathlib/pull/2626))
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.map_injective



## [2020-05-07 18:46:03](https://github.com/leanprover-community/mathlib/commit/bdce195)
chore(linear_algebra/basic): review ([#2616](https://github.com/leanprover-community/mathlib/pull/2616))
* several new `simp` lemmas;
* use `linear_equiv.coe_coe` instead of `coe_apply`;
* rename `sup_quotient_to_quotient_inf` to `quotient_inf_to_sup_quotient` because it better reflects the definition; similarly for `equiv`.
* make `general_linear_group` reducible.
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* submodule.coe_eq_coe
- \+ *lemma* submodule.coe_eq_zero
- \+ *lemma* submodule.coe_mem
- \+/\- *lemma* submodule.mk_eq_zero
- \+/\- *lemma* submodule.neg_mem_iff
- \+/\- *lemma* submodule.smul_mem_iff'

Modified src/analysis/convex/cone.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/basic.lean
- \- *theorem* linear_equiv.coe_apply
- \+ *theorem* linear_equiv.coe_coe
- \+ *lemma* linear_equiv.coe_to_add_equiv
- \+ *lemma* linear_equiv.coe_to_equiv
- \+ *lemma* linear_equiv.eq_symm_apply
- \+ *lemma* linear_equiv.map_eq_comap
- \+ *lemma* linear_equiv.refl_trans
- \+ *lemma* linear_equiv.symm_apply_eq
- \+ *lemma* linear_equiv.trans_refl
- \+/\- *def* linear_map.general_linear_group
- \+ *theorem* linear_map.map_coe_ker
- \+ *theorem* linear_map.mem_range_self
- \+ *def* linear_map.quotient_inf_to_sup_quotient
- \+ *lemma* linear_map.range_coprod
- \+ *def* linear_map.range_restrict
- \- *def* linear_map.sup_quotient_to_quotient_inf
- \+ *lemma* submodule.comap_subtype_eq_top
- \+ *lemma* submodule.comap_subtype_self
- \+/\- *lemma* submodule.disjoint_iff_comap_eq_bot
- \+/\- *lemma* submodule.map_coe
- \+ *lemma* submodule.mem_sup'
- \+ *lemma* submodule.quot_hom_ext
- \+ *lemma* submodule.range_range_restrict
- \+ *lemma* submodule.sup_eq_range



## [2020-05-07 15:51:38](https://github.com/leanprover-community/mathlib/commit/5d3b830)
refactor(order/lattice): add `sup/inf_eq_*`, rename `inf_le_inf_*` ([#2624](https://github.com/leanprover-community/mathlib/pull/2624))
## New lemmas:
* `sup_eq_right : a ⊔ b = b ↔a ≤ b`, and similarly for `sup_eq_left`, `left_eq_sup`, `right_eq_sup`,
  `inf_eq_right`, `inf_eq_left`, `left_eq_inf`, and `right_eq_inf`; all these lemmas are `@[simp]`;
* `sup_elim` and `inf_elim`: if `(≤)` is a total order, then `p a → p b → p (a ⊔ b)`, and similarly for `inf`.
## Renamed
* `inf_le_inf_right` is now `inf_le_inf_left` and vice versa. This agrees with `sup_le_sup_left`/`sup_le_sup_right`, and the rest of the library.
* `ord_continuous_sup` -> `ord_continuous.sup`;
* `ord_continuous_mono` -> `ord_continuous.mono`.
#### Estimated changes
Modified src/data/set/intervals/basic.lean


Modified src/linear_algebra/basic.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* ord_continuous.mono
- \+ *lemma* ord_continuous.sup
- \- *lemma* ord_continuous_mono
- \- *lemma* ord_continuous_sup

Modified src/order/filter/basic.lean


Modified src/order/filter/lift.lean


Modified src/order/fixed_points.lean


Modified src/order/lattice.lean
- \+ *theorem* inf_eq_left
- \+ *theorem* inf_eq_right
- \+ *lemma* inf_ind
- \+/\- *lemma* inf_le_inf_left
- \+/\- *lemma* inf_le_inf_right
- \+ *theorem* left_eq_inf
- \+ *theorem* left_eq_sup
- \+ *theorem* right_eq_inf
- \+ *theorem* right_eq_sup
- \+ *theorem* sup_eq_left
- \+ *theorem* sup_eq_right
- \+ *lemma* sup_ind

Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-05-07 13:09:37](https://github.com/leanprover-community/mathlib/commit/6c48444)
feat(algebra/lie_algebra): `lie_algebra.of_associative_algebra` is functorial ([#2620](https://github.com/leanprover-community/mathlib/pull/2620))
More precisely we:
  * define the Lie algebra homomorphism associated to a morphism of associative algebras
  * prove that the correspondence is functorial
  * prove that subalgebras and Lie subalgebras correspond
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *def* lie_algebra.of_associative_algebra_hom
- \+ *lemma* lie_algebra.of_associative_algebra_hom_comp
- \+ *lemma* lie_algebra.of_associative_algebra_hom_id
- \+ *def* lie_subalgebra_of_subalgebra

Modified src/ring_theory/algebra.lean
- \+ *lemma* subalgebra.mul_mem



## [2020-05-07 10:25:22](https://github.com/leanprover-community/mathlib/commit/da10afc)
feat(*): define `equiv.reflection` and `isometry.reflection` ([#2609](https://github.com/leanprover-community/mathlib/pull/2609))
Define reflection in a point and prove basic properties.
It is defined both as an `equiv.perm` of an `add_comm_group` and
as an `isometric` of a `normed_group`.
Other changes:
* rename `two_smul` to `two_smul'`, add `two_smul` using `semimodule`
  instead of `add_monoid.smul`;
* minor review of `algebra.midpoint`;
* arguments of `isometry.dist_eq` and `isometry.edist_eq` are now explicit;
* rename `isometry.inv` to `isometry.right_inv`; now it takes `right_inverse`
  instead of `equiv`;
* drop `isometry_inv_fun`: use `h.symm.isometry` instead;
* pull a few more lemmas about `equiv` and `isometry` to the `isometric` namespace.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* two_smul'
- \- *theorem* two_smul

Modified src/algebra/midpoint.lean
- \+ *lemma* add_monoid_hom.coe_of_map_midpoint
- \+ *def* add_monoid_hom.of_map_midpoint
- \+ *lemma* equiv.reflection_midpoint_left
- \+ *lemma* equiv.reflection_midpoint_right
- \+ *lemma* midpoint_add_self
- \+ *lemma* midpoint_zero_add

Modified src/algebra/module.lean
- \+ *theorem* two_smul

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.norm_two

Added src/analysis/normed_space/reflection.lean
- \+ *lemma* equiv.reflection_fixed_iff_of_module
- \+ *def* isometric.reflection
- \+ *lemma* isometric.reflection_apply
- \+ *lemma* isometric.reflection_dist_fixed
- \+ *lemma* isometric.reflection_dist_self'
- \+ *lemma* isometric.reflection_dist_self
- \+ *lemma* isometric.reflection_dist_self_real
- \+ *lemma* isometric.reflection_fixed_iff
- \+ *lemma* isometric.reflection_involutive
- \+ *lemma* isometric.reflection_midpoint_left
- \+ *lemma* isometric.reflection_midpoint_right
- \+ *lemma* isometric.reflection_self
- \+ *lemma* isometric.reflection_symm
- \+ *lemma* isometric.reflection_to_equiv

Modified src/data/equiv/mul_add.lean
- \+ *def* equiv.reflection
- \+ *lemma* equiv.reflection_apply
- \+ *lemma* equiv.reflection_fixed_iff_of_bit0_inj
- \+ *lemma* equiv.reflection_involutive
- \+ *lemma* equiv.reflection_self
- \+ *lemma* equiv.reflection_symm

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \- *lemma* isometric.coe_eq_to_homeomorph
- \+ *lemma* isometric.coe_to_homeomorph
- \+/\- *lemma* isometric.ext
- \- *lemma* isometric.isometry_inv_fun
- \+ *lemma* isometric.to_equiv_inj
- \+/\- *lemma* isometric.to_homeomorph_to_equiv
- \+/\- *theorem* isometry.dist_eq
- \+/\- *theorem* isometry.edist_eq
- \- *lemma* isometry.inv
- \+/\- *lemma* isometry.isometric_on_range_apply
- \+ *lemma* isometry.right_inv



## [2020-05-07 07:12:04](https://github.com/leanprover-community/mathlib/commit/a6415d7)
chore(data/set/basic): use implicit args in `set.ext_iff` ([#2619](https://github.com/leanprover-community/mathlib/pull/2619))
Most other `ext_iff` lemmas use implicit arguments, let `set.ext_iff` use them too.
#### Estimated changes
Modified src/data/finset.lean


Modified src/data/semiquot.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* set.ext_iff

Modified src/data/setoid.lean


Modified src/linear_algebra/basic.lean


Modified src/set_theory/zfc.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean




## [2020-05-07 02:39:51](https://github.com/leanprover-community/mathlib/commit/f6edeba)
chore(scripts): update nolints.txt ([#2622](https://github.com/leanprover-community/mathlib/pull/2622))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-07 00:42:46](https://github.com/leanprover-community/mathlib/commit/a8eafb6)
chore(scripts): update nolints.txt ([#2621](https://github.com/leanprover-community/mathlib/pull/2621))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-06 22:41:38](https://github.com/leanprover-community/mathlib/commit/0c8d2e2)
chore(data/set/countable): use dot syntax here and there ([#2617](https://github.com/leanprover-community/mathlib/pull/2617))
Renamed:
* `exists_surjective_of_countable` -> `countable.exists_surjective`;
* `countable_subset` -> `countable.mono`;
* `countable_image` -> `countable.image`;
* `countable_bUnion` -> `countable.bUnion`;
* `countable_sUnion` -> `countable.sUnion`;
* `countable_union` -> `countable.union`;
* `countable_insert` -> `countable.insert`;
* `countable_finite` -> `finite.countable`;
Add:
* `finset.countable_to_set`
#### Estimated changes
Modified src/data/set/countable.lean
- \+ *lemma* finset.countable_to_set
- \+ *lemma* set.countable.bUnion
- \+ *lemma* set.countable.exists_surjective
- \+ *lemma* set.countable.image
- \+ *lemma* set.countable.insert
- \+ *lemma* set.countable.mono
- \+ *lemma* set.countable.sUnion
- \+ *lemma* set.countable.union
- \- *lemma* set.countable_bUnion
- \- *lemma* set.countable_finite
- \- *lemma* set.countable_image
- \- *lemma* set.countable_insert
- \- *lemma* set.countable_sUnion
- \- *lemma* set.countable_subset
- \- *lemma* set.countable_union
- \- *lemma* set.exists_surjective_of_countable
- \+ *lemma* set.finite.countable

Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.range_const

Modified src/measure_theory/measure_space.lean


Modified src/order/filter/bases.lean
- \+/\- *def* filter.is_countably_generated.countable_filter_basis

Modified src/topology/bases.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean




## [2020-05-06 19:39:53](https://github.com/leanprover-community/mathlib/commit/c3d76d0)
chore(*): a few missing `simp` lemmas ([#2615](https://github.com/leanprover-community/mathlib/pull/2615))
Also replaces `monoid_hom.exists_inv_of_comp_exists_inv` with `monoid_hom.map_exists_right_inv` and adds `monoid_hom.map_exists_left_inv`.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \- *lemma* monoid_hom.exists_inv_of_comp_exists_inv
- \+ *lemma* monoid_hom.id_apply
- \+ *lemma* monoid_hom.map_exists_left_inv
- \+ *lemma* monoid_hom.map_exists_right_inv
- \+ *lemma* monoid_hom.map_mul_eq_one

Modified src/data/equiv/mul_add.lean
- \+ *theorem* mul_equiv.coe_mk
- \+ *theorem* mul_equiv.coe_symm_mk

Modified src/data/sigma/basic.lean
- \+ *theorem* sigma.eta



## [2020-05-06 19:39:51](https://github.com/leanprover-community/mathlib/commit/460d9d4)
refactor(data/equiv/local_equiv, topology/local_homeomorph): use coercions ([#2603](https://github.com/leanprover-community/mathlib/pull/2603))
Local equivs and local homeomorphisms use `e.to_fun x` and `e.inv_fun x`, instead of coercions as in most of mathlib, as there were problems with coercions that made them unusable in manifolds. These problems have been fixed in Lean 3.10, so we switch to coercions for them also.
This is 95% a refactor PR, erasing `.to_fun` and replacing `.inv_fun` with `.symm` in several files, and fixing proofs. Plus a few simp lemmas on the coercions to let things go smoothly. I have also linted all the files I have touched.
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/inverse.lean
- \+ *lemma* approximates_linear_on.to_local_homeomorph_coe
- \- *lemma* approximates_linear_on.to_local_homeomorph_to_fun
- \+ *lemma* has_strict_fderiv_at.to_local_homeomorph_coe
- \- *lemma* has_strict_fderiv_at.to_local_homeomorph_to_fun

Modified src/data/equiv/local_equiv.lean
- \+ *lemma* equiv.to_local_equiv_coe
- \- *lemma* equiv.to_local_equiv_inv_fun
- \+ *lemma* equiv.to_local_equiv_symm_coe
- \- *lemma* equiv.to_local_equiv_to_fun
- \+/\- *lemma* local_equiv.bij_on_source
- \+ *theorem* local_equiv.coe_mk
- \+ *theorem* local_equiv.coe_symm_mk
- \+ *lemma* local_equiv.coe_trans
- \+ *lemma* local_equiv.coe_trans_symm
- \+/\- *lemma* local_equiv.image_source_eq_target
- \+/\- *lemma* local_equiv.image_trans_source
- \+ *lemma* local_equiv.inv_fun_as_coe
- \+/\- *lemma* local_equiv.inv_image_target_eq_source
- \+/\- *lemma* local_equiv.inv_image_trans_target
- \+ *lemma* local_equiv.left_inv
- \+ *lemma* local_equiv.map_source
- \+ *lemma* local_equiv.map_target
- \+ *lemma* local_equiv.of_set_coe
- \- *lemma* local_equiv.of_set_inv_fun
- \- *lemma* local_equiv.of_set_to_fun
- \+ *lemma* local_equiv.prod_coe
- \+ *lemma* local_equiv.prod_coe_symm
- \- *lemma* local_equiv.prod_inv_fun
- \- *lemma* local_equiv.prod_to_fun
- \+ *lemma* local_equiv.refl_coe
- \- *lemma* local_equiv.refl_inv_fun
- \- *lemma* local_equiv.refl_to_fun
- \+ *lemma* local_equiv.restr_coe
- \+ *lemma* local_equiv.restr_coe_symm
- \- *lemma* local_equiv.restr_inv_fun
- \+/\- *lemma* local_equiv.restr_target
- \- *lemma* local_equiv.restr_to_fun
- \+ *lemma* local_equiv.right_inv
- \+/\- *lemma* local_equiv.source_subset_preimage_target
- \- *lemma* local_equiv.symm_inv_fun
- \- *lemma* local_equiv.symm_to_fun
- \+/\- *lemma* local_equiv.target_subset_preimage_source
- \+ *lemma* local_equiv.to_fun_as_coe
- \- *lemma* local_equiv.trans_apply
- \- *lemma* local_equiv.trans_inv_apply
- \- *lemma* local_equiv.trans_inv_fun
- \+/\- *lemma* local_equiv.trans_source''
- \+/\- *lemma* local_equiv.trans_source'
- \+/\- *lemma* local_equiv.trans_source
- \+/\- *lemma* local_equiv.trans_target''
- \+/\- *lemma* local_equiv.trans_target'
- \+/\- *lemma* local_equiv.trans_target
- \- *lemma* local_equiv.trans_to_fun

Modified src/geometry/manifold/basic_smooth_bundle.lean
- \- *lemma* basic_smooth_bundle_core.chart_at_inv_fun_fst
- \- *lemma* basic_smooth_bundle_core.chart_at_to_fun_fst
- \+ *lemma* basic_smooth_bundle_core.coe_chart_at_fst
- \+ *lemma* basic_smooth_bundle_core.coe_chart_at_symm_fst
- \+ *lemma* tangent_bundle_model_space_coe_chart_at
- \+ *lemma* tangent_bundle_model_space_coe_chart_at_symm
- \+ *def* trivial_basic_smooth_bundle_core

Modified src/geometry/manifold/manifold.lean
- \+ *def* continuous_pregroupoid

Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* bundle_mfderiv_chart
- \- *lemma* bundle_mfderiv_chart_inv_fun
- \+ *lemma* bundle_mfderiv_chart_symm
- \- *lemma* bundle_mfderiv_chart_to_fun
- \+ *lemma* local_homeomorph.mdifferentiable.comp_symm_deriv
- \- *lemma* local_homeomorph.mdifferentiable.inv_fun_to_fun_deriv
- \- *lemma* local_homeomorph.mdifferentiable.mdifferentiable_at_inv_fun
- \+ *lemma* local_homeomorph.mdifferentiable.mdifferentiable_at_symm
- \- *lemma* local_homeomorph.mdifferentiable.mdifferentiable_at_to_fun
- \+ *lemma* local_homeomorph.mdifferentiable.symm_comp_deriv
- \- *lemma* local_homeomorph.mdifferentiable.to_fun_inv_fun_deriv
- \+ *lemma* mdifferentiable_at_atlas
- \- *lemma* mdifferentiable_at_atlas_inv_fun
- \+ *lemma* mdifferentiable_at_atlas_symm
- \- *lemma* mdifferentiable_at_atlas_to_fun
- \+ *lemma* mdifferentiable_on_atlas
- \- *lemma* mdifferentiable_on_atlas_inv_fun
- \+ *lemma* mdifferentiable_on_atlas_symm
- \- *lemma* mdifferentiable_on_atlas_to_fun
- \+ *lemma* model_with_corners.mdifferentiable
- \+ *lemma* model_with_corners.mdifferentiable_on_symm
- \- *lemma* model_with_corners_mdifferentiable_on_inv_fun
- \- *lemma* model_with_corners_mdifferentiable_on_to_fun

Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* ext_chart_at_coe
- \+ *lemma* ext_chart_at_coe_symm
- \+ *lemma* ext_chart_at_continuous_at
- \- *lemma* ext_chart_at_continuous_at_to_fun
- \+ *lemma* ext_chart_at_continuous_on
- \- *lemma* ext_chart_at_continuous_on_inv_fun
- \+ *lemma* ext_chart_at_continuous_on_symm
- \- *lemma* ext_chart_at_continuous_on_to_fun
- \- *lemma* ext_chart_continuous_at_inv_fun'
- \- *lemma* ext_chart_continuous_at_inv_fun
- \+ *lemma* ext_chart_continuous_at_symm'
- \+ *lemma* ext_chart_continuous_at_symm
- \+/\- *lemma* ext_chart_preimage_inter_eq
- \+ *lemma* model_with_corners.continuous_symm
- \+ *lemma* model_with_corners.left_inv'
- \+ *lemma* model_with_corners.left_inv
- \+ *lemma* model_with_corners.mk_coe
- \+ *lemma* model_with_corners.mk_coe_symm
- \+ *lemma* model_with_corners.right_inv
- \+ *lemma* model_with_corners.target
- \+ *lemma* model_with_corners.to_local_equiv_coe
- \+ *lemma* model_with_corners.to_local_equiv_coe_symm
- \+ *lemma* model_with_corners.unique_diff
- \+ *lemma* model_with_corners.unique_diff_at_image
- \+ *lemma* model_with_corners.unique_diff_preimage
- \+ *lemma* model_with_corners.unique_diff_preimage_source
- \- *lemma* model_with_corners_inv_fun_comp
- \- *lemma* model_with_corners_left_inv
- \- *lemma* model_with_corners_right_inv
- \+ *lemma* model_with_corners_self_coe
- \+ *lemma* model_with_corners_self_coe_symm
- \+/\- *lemma* model_with_corners_self_local_equiv
- \- *lemma* model_with_corners_target

Modified src/topology/local_homeomorph.lean
- \+ *lemma* homeomorph.to_local_homeomorph_coe
- \+ *lemma* homeomorph.to_local_homeomorph_coe_symm
- \- *lemma* homeomorph.to_local_homeomorph_inv_fun
- \+/\- *lemma* homeomorph.to_local_homeomorph_source
- \+/\- *lemma* homeomorph.to_local_homeomorph_target
- \- *lemma* homeomorph.to_local_homeomorph_to_fun
- \+/\- *lemma* local_homeomorph.apply_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.coe_coe
- \+ *lemma* local_homeomorph.coe_coe_symm
- \+ *lemma* local_homeomorph.coe_trans
- \+ *lemma* local_homeomorph.coe_trans_symm
- \- *lemma* local_homeomorph.continuous_at_inv_fun
- \+ *lemma* local_homeomorph.continuous_at_symm
- \- *lemma* local_homeomorph.continuous_at_to_fun
- \+ *lemma* local_homeomorph.continuous_on_symm
- \+/\- *lemma* local_homeomorph.image_open_of_open
- \+/\- *lemma* local_homeomorph.image_trans_source
- \+/\- *lemma* local_homeomorph.inv_apply_eq_of_eq_on_source
- \+ *lemma* local_homeomorph.inv_fun_eq_coe
- \- *lemma* local_homeomorph.inv_fun_tendsto
- \+/\- *lemma* local_homeomorph.inv_image_trans_target
- \+ *lemma* local_homeomorph.left_inv
- \+ *lemma* local_homeomorph.map_source
- \+ *lemma* local_homeomorph.map_target
- \+ *lemma* local_homeomorph.mk_coe
- \+ *lemma* local_homeomorph.mk_coe_symm
- \+ *lemma* local_homeomorph.of_set_coe
- \- *lemma* local_homeomorph.of_set_inv_fun
- \+/\- *lemma* local_homeomorph.of_set_source
- \+/\- *lemma* local_homeomorph.of_set_symm
- \+/\- *lemma* local_homeomorph.of_set_target
- \- *lemma* local_homeomorph.of_set_to_fun
- \+ *lemma* local_homeomorph.prod_coe
- \+ *lemma* local_homeomorph.prod_coe_symm
- \- *lemma* local_homeomorph.prod_inv_fun
- \- *lemma* local_homeomorph.prod_to_fun
- \+ *lemma* local_homeomorph.refl_coe
- \- *lemma* local_homeomorph.refl_inv_fun
- \+/\- *lemma* local_homeomorph.refl_source
- \+/\- *lemma* local_homeomorph.refl_symm
- \+/\- *lemma* local_homeomorph.refl_target
- \- *lemma* local_homeomorph.refl_to_fun
- \+ *lemma* local_homeomorph.restr_coe
- \+ *lemma* local_homeomorph.restr_coe_symm
- \- *lemma* local_homeomorph.restr_inv_fun
- \- *lemma* local_homeomorph.restr_to_fun
- \+ *lemma* local_homeomorph.right_inv
- \- *lemma* local_homeomorph.symm_inv_fun
- \- *lemma* local_homeomorph.symm_to_fun
- \+ *lemma* local_homeomorph.tendsto_symm
- \+ *lemma* local_homeomorph.to_fun_eq_coe
- \+ *lemma* local_homeomorph.to_homeomorph_coe
- \- *lemma* local_homeomorph.to_homeomorph_inv_fun
- \+ *lemma* local_homeomorph.to_homeomorph_symm_coe
- \- *lemma* local_homeomorph.to_homeomorph_to_fun
- \- *lemma* local_homeomorph.trans_inv_fun
- \+/\- *lemma* local_homeomorph.trans_source''
- \+/\- *lemma* local_homeomorph.trans_source'
- \+/\- *lemma* local_homeomorph.trans_source
- \+/\- *lemma* local_homeomorph.trans_target''
- \+/\- *lemma* local_homeomorph.trans_target'
- \+/\- *lemma* local_homeomorph.trans_target
- \- *lemma* local_homeomorph.trans_to_fun

Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.coe_coe
- \+ *lemma* bundle_trivialization.coe_fst
- \+ *lemma* bundle_trivialization.coe_mk



## [2020-05-06 19:39:49](https://github.com/leanprover-community/mathlib/commit/b1c0398)
feat(analysis/analytic/composition): the composition of formal series is associative ([#2513](https://github.com/leanprover-community/mathlib/pull/2513))
The composition of formal multilinear series is associative. I will need this when doing the analytic local inverse theorem, and I was surprised by how nontrivial this is: one should show that two double sums coincide by reindexing, but the reindexing is combinatorially tricky (it involves joining and splitting lists carefully). 
Preliminary material on lists, sums and compositions is done in [#2501](https://github.com/leanprover-community/mathlib/pull/2501) and [#2554](https://github.com/leanprover-community/mathlib/pull/2554), and the proof is in this PR.
#### Estimated changes
Modified src/analysis/analytic/composition.lean
- \+ *lemma* composition.blocks_fun_sigma_composition_aux
- \+ *def* composition.gather
- \+ *lemma* composition.length_gather
- \+ *lemma* composition.length_sigma_composition_aux
- \+ *def* composition.sigma_composition_aux
- \+ *lemma* composition.sigma_composition_eq_iff
- \+ *def* composition.sigma_equiv_sigma_pi
- \+ *lemma* composition.sigma_pi_composition_eq_iff
- \+ *lemma* composition.size_up_to_size_up_to_add
- \+ *lemma* formal_multilinear_series.apply_composition_ones
- \+ *lemma* formal_multilinear_series.comp_along_composition_apply
- \+ *theorem* formal_multilinear_series.comp_assoc
- \+ *lemma* formal_multilinear_series.comp_coeff_zero''
- \+ *lemma* formal_multilinear_series.comp_coeff_zero'
- \+ *lemma* formal_multilinear_series.comp_coeff_zero
- \+ *theorem* formal_multilinear_series.comp_id
- \+ *def* formal_multilinear_series.id
- \+ *lemma* formal_multilinear_series.id_apply_ne_one
- \+ *lemma* formal_multilinear_series.id_apply_one'
- \+ *lemma* formal_multilinear_series.id_apply_one
- \+ *theorem* formal_multilinear_series.id_comp

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* formal_multilinear_series.congr

Modified src/combinatorics/composition.lean
- \+ *def* composition.blocks_fin_equiv
- \+ *lemma* composition.blocks_fun_congr
- \+ *lemma* composition.index_embedding
- \+ *lemma* composition.inv_embedding_comp
- \+ *lemma* list.nth_le_split_wrt_composition
- \+ *lemma* list.nth_le_split_wrt_composition_aux



## [2020-05-06 16:31:27](https://github.com/leanprover-community/mathlib/commit/0a7ff10)
feat(algebra/units): some norm_cast attributes ([#2612](https://github.com/leanprover-community/mathlib/pull/2612))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+/\- *lemma* units.coe_inv
- \+/\- *lemma* units.coe_mul
- \+/\- *lemma* units.coe_one

Modified src/algebra/group_power.lean
- \+/\- *lemma* units.coe_pow

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* is_add_subgroup.gsmul_coe
- \+/\- *lemma* is_subgroup.coe_gpow

Modified src/group_theory/submonoid.lean
- \+/\- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* is_submonoid.coe_pow



## [2020-05-06 14:05:37](https://github.com/leanprover-community/mathlib/commit/93a64da)
chore(data/pnat/basic): add `mk_le_mk`, `mk_lt_mk`, `coe_le_coe`, `coe_lt_coe` ([#2613](https://github.com/leanprover-community/mathlib/pull/2613))
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.coe_le_coe
- \+ *lemma* pnat.coe_lt_coe
- \+ *lemma* pnat.mk_le_mk
- \+ *lemma* pnat.mk_lt_mk

Modified src/data/pnat/intervals.lean
- \+/\- *lemma* pnat.Ico.mem



## [2020-05-06 09:03:06](https://github.com/leanprover-community/mathlib/commit/5593155)
feat(*): lemmas on sums and products over fintypes ([#2598](https://github.com/leanprover-community/mathlib/pull/2598))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.prod_pow

Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_fiberwise
- \+/\- *lemma* fintype.card_eq_sum_ones
- \+ *lemma* fintype.prod_congr
- \+ *lemma* fintype.prod_eq_one
- \+ *lemma* fintype.prod_fiberwise
- \+ *lemma* fintype.prod_sum_type
- \+ *lemma* fintype.prod_unique



## [2020-05-06 02:11:34](https://github.com/leanprover-community/mathlib/commit/4503f8f)
chore(scripts): update nolints.txt ([#2610](https://github.com/leanprover-community/mathlib/pull/2610))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-05 22:33:19](https://github.com/leanprover-community/mathlib/commit/c7593cc)
refactor(field_theory): move finite_card.lean into finite.lean ([#2607](https://github.com/leanprover-community/mathlib/pull/2607))
#### Estimated changes
Modified src/field_theory/finite.lean
- \+ *theorem* finite_field.card'
- \+ *theorem* finite_field.card

Deleted src/field_theory/finite_card.lean
- \- *theorem* finite_field.card'
- \- *theorem* finite_field.card



## [2020-05-05 22:33:16](https://github.com/leanprover-community/mathlib/commit/0db59db)
feat(data/equiv/basic): some elementary equivs ([#2602](https://github.com/leanprover-community/mathlib/pull/2602))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.fun_unique
- \+ *lemma* equiv.fun_unique_apply
- \+ *lemma* equiv.fun_unique_symm_apply
- \+ *lemma* equiv.sigma_preimage_equiv_apply
- \+ *lemma* equiv.sigma_preimage_equiv_symm_apply_fst
- \+ *lemma* equiv.sigma_preimage_equiv_symm_apply_snd_fst
- \+ *def* equiv.subtype_preimage
- \+ *lemma* equiv.subtype_preimage_apply
- \+ *lemma* equiv.subtype_preimage_symm_apply_coe
- \+ *lemma* equiv.subtype_preimage_symm_apply_coe_neg
- \+ *lemma* equiv.subtype_preimage_symm_apply_coe_pos
- \+ *def* equiv.sum_compl
- \+ *lemma* equiv.sum_compl_apply_inl
- \+ *lemma* equiv.sum_compl_apply_inr
- \+ *lemma* equiv.sum_compl_apply_symm_of_neg
- \+ *lemma* equiv.sum_compl_apply_symm_of_pos



## [2020-05-05 20:16:28](https://github.com/leanprover-community/mathlib/commit/359031f)
refactor(*): remove instance max depth ([#2608](https://github.com/leanprover-community/mathlib/pull/2608))
With current Lean, all the manual increases of the maximum instance depth have become unnecessary. This PR removes them all.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/data/padics/padic_numbers.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/ring.lean


Modified src/topology/algebra/module.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2020-05-05 19:08:14](https://github.com/leanprover-community/mathlib/commit/a66d0a8)
chore(field_theory/finite): meaningful variable names ([#2606](https://github.com/leanprover-community/mathlib/pull/2606))
#### Estimated changes
Modified src/field_theory/finite.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* finite_field.card_image_polynomial_eval
- \+/\- *lemma* finite_field.card_units
- \+/\- *lemma* finite_field.exists_root_sum_quadratic
- \+/\- *def* finite_field.field_of_integral_domain
- \+/\- *lemma* finite_field.pow_card_sub_one_eq_one



## [2020-05-05 14:29:27](https://github.com/leanprover-community/mathlib/commit/0c1b60b)
feat(group_theory/order_of_element): order_of_eq_prime ([#2604](https://github.com/leanprover-community/mathlib/pull/2604))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_prime



## [2020-05-05 08:02:15](https://github.com/leanprover-community/mathlib/commit/7a367f3)
feat(algebra/char_p): add lemma ring_char_ne_one ([#2595](https://github.com/leanprover-community/mathlib/pull/2595))
This lemma is more useful than the extant `false_of_nonzero_of_char_one`
when we are working with the function `ring_char` rather than the `char_p`
Prop.
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.ring_char_ne_one

Modified src/algebra/ring.lean




## [2020-05-05 06:09:07](https://github.com/leanprover-community/mathlib/commit/91b3906)
feat(data/polynomial): misc on derivatives of polynomials ([#2596](https://github.com/leanprover-community/mathlib/pull/2596))
Co-authored by: @alexjbest
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *def* polynomial.derivative_hom
- \+ *def* polynomial.derivative_lhom
- \+ *lemma* polynomial.derivative_neg
- \+ *lemma* polynomial.derivative_smul
- \+ *lemma* polynomial.derivative_sub
- \+ *lemma* polynomial.is_coprime_of_is_root_of_eval_derivative_ne_zero



## [2020-05-05 04:42:12](https://github.com/leanprover-community/mathlib/commit/d6ddfd2)
feat(algebra/midpoint): define `midpoint`, prove basic properties ([#2599](https://github.com/leanprover-community/mathlib/pull/2599))
Part of [#2214](https://github.com/leanprover-community/mathlib/pull/2214)
#### Estimated changes
Added src/algebra/midpoint.lean
- \+ *def* midpoint
- \+ *lemma* midpoint_add_add
- \+ *lemma* midpoint_add_left
- \+ *lemma* midpoint_add_right
- \+ *lemma* midpoint_comm
- \+ *lemma* midpoint_def
- \+ *lemma* midpoint_eq_iff
- \+ *lemma* midpoint_neg_neg
- \+ *lemma* midpoint_self
- \+ *lemma* midpoint_smul_smul
- \+ *lemma* midpoint_sub_left
- \+ *lemma* midpoint_sub_right
- \+ *lemma* midpoint_sub_sub
- \+ *lemma* midpoint_unique



## [2020-05-04 22:27:29](https://github.com/leanprover-community/mathlib/commit/1c4b5ec)
feat(ring_theory/ideals): quotient map to residue field as ring hom ([#2597](https://github.com/leanprover-community/mathlib/pull/2597))
#### Estimated changes
Modified src/ring_theory/ideals.lean
- \+ *def* local_ring.residue



## [2020-05-04 10:57:29](https://github.com/leanprover-community/mathlib/commit/14aa1f7)
feat(combinatorics/composition): refactor compositions, split a list wrt a composition ([#2554](https://github.com/leanprover-community/mathlib/pull/2554))
Refactor `composition`, replacing in its definition a list of positive integers with a list of integers which are positive. This avoids going back and forth all the time between `nat` and `pnat`.
Also introduce the ability to split a list of length `n` with respect to a composition `c` of `n`, giving rise to a list of `c.length` sublists whose join is the original list.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean
- \- *def* composition.blocks
- \+/\- *lemma* composition.blocks_length
- \- *lemma* composition.blocks_pnat_length
- \- *lemma* composition.blocks_pos
- \- *lemma* composition.blocks_sum
- \+ *lemma* composition.eq_ones_iff
- \+ *lemma* composition.eq_single_iff
- \+/\- *def* composition.length
- \+ *lemma* composition.monotone_size_up_to
- \+ *lemma* composition.ne_ones_iff
- \+ *lemma* composition.of_fn_blocks_fun
- \+ *def* composition.ones
- \+ *lemma* composition.ones_blocks
- \+ *lemma* composition.ones_blocks_fun
- \+ *lemma* composition.ones_embedding
- \+ *lemma* composition.ones_length
- \+ *lemma* composition.ones_size_up_to
- \- *lemma* composition.sigma_eq_iff_blocks_pnat_eq
- \+ *def* composition.single
- \+ *lemma* composition.single_blocks
- \+ *lemma* composition.single_blocks_fun
- \+ *lemma* composition.single_embedding
- \+ *lemma* composition.single_length
- \- *lemma* composition.to_composition_as_set_blocks_pnat
- \- *def* composition_as_set.blocks_pnat
- \- *lemma* composition_as_set.blocks_pnat_length
- \- *lemma* composition_as_set.coe_blocks_pnat_eq_blocks
- \- *lemma* composition_as_set.to_composition_blocks_pnat
- \+ *theorem* list.join_split_wrt_composition
- \+ *theorem* list.join_split_wrt_composition_aux
- \+ *lemma* list.length_pos_of_mem_split_wrt_composition
- \+ *lemma* list.length_split_wrt_composition
- \+ *lemma* list.length_split_wrt_composition_aux
- \+ *lemma* list.map_length_split_wrt_composition
- \+ *lemma* list.map_length_split_wrt_composition_aux
- \+ *def* list.split_wrt_composition
- \+ *def* list.split_wrt_composition_aux
- \+ *lemma* list.split_wrt_composition_aux_cons
- \+ *theorem* list.split_wrt_composition_join
- \+ *lemma* list.sum_take_map_length_split_wrt_composition



## [2020-05-04 05:40:22](https://github.com/leanprover-community/mathlib/commit/70245f4)
feat(algebra/big_operators): prod_comp ([#2594](https://github.com/leanprover-community/mathlib/pull/2594))
This is a lemma that @jcommelin looks like he could have used in Chevalley Warning, and is probably useful elsewhere.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_comp
- \+ *lemma* finset.sum_comp



## [2020-05-03 12:27:43](https://github.com/leanprover-community/mathlib/commit/08a17d6)
chore(scripts): update nolints.txt ([#2593](https://github.com/leanprover-community/mathlib/pull/2593))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-05-03 08:34:26](https://github.com/leanprover-community/mathlib/commit/a223bbb)
chore(*): switch to lean 3.10.0 ([#2587](https://github.com/leanprover-community/mathlib/pull/2587))
There have been two changes in Lean 3.10 that have a significant effect on mathlib:
 - `rename'` has been moved to core.  Therefore `rename'` has been removed.
 - Given a term `⇑f x`, the simplifier can now rewrite in both `f` and `x`.  In many cases we had both `⇑f = ⇑f'` and `⇑f x = ⇑f' x` as simp lemmas; the latter is redundant now and has been removed (or just not marked simp anymore).  The new and improved congruence lemmas are also used by `convert` and `congr`, these tactics have become more powerful as well.
I've also sneaked in two related changes that I noticed while fixing the proofs affected by the changes above:
 - `@[to_additive, simp]` has been replaced by `@[simp, to_additive]` in the monoid localization file.  The difference is that `@[to_additive, simp]` only marks the multiplicative lemma as simp.
 - `def prod_comm : α × β ≃ β × α` (etc.) is no longer marked `@[simp]`.  Marking this kind of lemmas as simp causes the simplifier to unfold the definition of `prod_comm` (instead of just rewriting `α × β` to `β × α` in the `≃` simp relation).  This has become a bigger issue now since the simplifier can rewrite the `f` in `⇑f x`.
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.arrow_punit_equiv_punit
- \+/\- *def* equiv.empty_arrow_equiv_punit
- \+/\- *def* equiv.empty_prod
- \+/\- *def* equiv.empty_sum
- \+ *lemma* equiv.empty_sum_apply_inr
- \+/\- *def* equiv.false_arrow_equiv_punit
- \+/\- *def* equiv.nat_sum_punit_equiv_nat
- \+/\- *def* equiv.option_equiv_sum_punit
- \+ *lemma* equiv.option_equiv_sum_punit_none
- \+ *lemma* equiv.option_equiv_sum_punit_some
- \+/\- *def* equiv.pempty_arrow_equiv_punit
- \+/\- *def* equiv.pempty_prod
- \+/\- *def* equiv.pempty_sum
- \+ *lemma* equiv.pempty_sum_apply_inr
- \+/\- *def* equiv.prod_assoc
- \+/\- *def* equiv.prod_comm
- \+ *lemma* equiv.prod_comm_apply
- \+/\- *def* equiv.prod_empty
- \+/\- *def* equiv.prod_pempty
- \+/\- *def* equiv.prod_punit
- \+/\- *def* equiv.punit_arrow_equiv
- \+/\- *def* equiv.punit_prod
- \+/\- *def* equiv.sum_assoc
- \+/\- *def* equiv.sum_comm
- \+ *lemma* equiv.sum_comm_apply_inl
- \+ *lemma* equiv.sum_comm_apply_inr
- \+ *lemma* equiv.sum_comm_symm
- \+/\- *def* equiv.sum_empty
- \+ *lemma* equiv.sum_empty_apply_inl
- \+/\- *def* equiv.sum_pempty
- \+ *lemma* equiv.sum_pempty_apply_inl
- \- *theorem* equiv.symm_symm_apply

Modified src/data/finsupp.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/list/defs.lean
- \- *def* list.after

Modified src/data/list/sigma.lean


Modified src/data/pequiv.lean
- \- *lemma* pequiv.refl_trans_apply
- \- *lemma* pequiv.symm_refl_apply
- \- *lemma* pequiv.symm_single_apply
- \- *lemma* pequiv.symm_symm_apply
- \- *lemma* pequiv.trans_refl_apply

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* submonoid.localization_map.comp_mul_equiv_symm_comap_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_localizations_symm_apply
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map_apply
- \- *lemma* submonoid.localization_map.of_mul_equiv_apply
- \+/\- *lemma* submonoid.localization_map.of_mul_equiv_eq
- \- *lemma* submonoid.localization_map.to_mul_equiv_apply
- \+/\- *lemma* submonoid.localization_map.to_mul_equiv_eq
- \+/\- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv
- \+/\- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv
- \+/\- *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv_apply

Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basic.lean
- \- *theorem* linear_equiv.symm_symm_apply

Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/algebra.lean
- \+/\- *lemma* alg_hom.coe_to_add_monoid_hom
- \+/\- *lemma* alg_hom.coe_to_monoid_hom

Modified src/ring_theory/power_series.lean
- \+/\- *lemma* mv_power_series.coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* mv_power_series.coeff_zero_one
- \+/\- *lemma* mv_power_series.monomial_zero_eq_C_apply
- \+/\- *lemma* power_series.coeff_zero_C
- \+/\- *lemma* power_series.coeff_zero_X
- \+/\- *lemma* power_series.coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* power_series.coeff_zero_mul_X
- \+/\- *lemma* power_series.coeff_zero_one
- \+/\- *def* power_series.mk
- \+/\- *lemma* power_series.monomial_zero_eq_C_apply

Modified src/set_theory/ordinal.lean


Modified src/set_theory/pgame.lean


Modified src/tactic/basic.lean


Deleted src/tactic/rename.lean


Modified src/topology/algebra/module.lean
- \+/\- *theorem* continuous_linear_equiv.symm_symm_apply

Modified test/tactics.lean




## [2020-05-02 22:38:27](https://github.com/leanprover-community/mathlib/commit/d1eae21)
chore(build.yml): Don't build nolints branch ([#2591](https://github.com/leanprover-community/mathlib/pull/2591))
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-05-02 15:22:25](https://github.com/leanprover-community/mathlib/commit/a99f9b5)
refactor(algebra/big_operators): introduce notation for finset.prod and finset.sum ([#2582](https://github.com/leanprover-community/mathlib/pull/2582))
I have not gone through all of mathlib to use this notation everywhere. I think we can maybe transition naturally.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.card_eq_sum_ones
- \+/\- *theorem* finset.exists_le_of_sum_le
- \+/\- *lemma* finset.exists_ne_one_of_prod_ne_one
- \+/\- *lemma* finset.mul_sum
- \+/\- *lemma* finset.nonempty_of_prod_ne_one
- \- *lemma* finset.prod_Ico_eq_div
- \+ *lemma* finset.prod_Ico_eq_mul_inv
- \+/\- *lemma* finset.prod_Ico_id_eq_fact
- \+/\- *lemma* finset.prod_attach
- \+/\- *lemma* finset.prod_const
- \+/\- *lemma* finset.prod_const_one
- \+/\- *lemma* finset.prod_empty
- \+/\- *theorem* finset.prod_eq_fold
- \+/\- *lemma* finset.prod_eq_one
- \+/\- *lemma* finset.prod_eq_zero
- \+/\- *lemma* finset.prod_eq_zero_iff
- \+/\- *lemma* finset.prod_filter_ne_one
- \+/\- *lemma* finset.prod_insert
- \+/\- *lemma* finset.prod_inv_distrib
- \+/\- *lemma* finset.prod_mul_distrib
- \+/\- *lemma* finset.prod_pos
- \+/\- *lemma* finset.prod_sdiff
- \+/\- *lemma* finset.prod_singleton
- \+/\- *lemma* finset.prod_subset
- \+/\- *lemma* finset.prod_union
- \+/\- *lemma* finset.single_le_sum
- \+/\- *lemma* finset.sum_eq_zero_iff_of_nonneg
- \+/\- *lemma* finset.sum_eq_zero_iff_of_nonpos
- \+/\- *lemma* finset.sum_le_sum
- \+/\- *lemma* finset.sum_le_sum_of_subset
- \+/\- *lemma* finset.sum_mul
- \+/\- *lemma* finset.sum_nonneg
- \+/\- *lemma* finset.sum_nonpos
- \+/\- *lemma* finset.sum_range_id
- \+ *lemma* finset.sum_range_succ
- \+/\- *lemma* finset.sum_sub_distrib

Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/geom_sum.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/choose.lean


Modified src/group_theory/order_of_element.lean


Modified src/ring_theory/power_series.lean




## [2020-05-02 12:33:54](https://github.com/leanprover-community/mathlib/commit/1cc83e9)
chore(algebra/ordered_field): move inv_neg to field and prove for division ring ([#2588](https://github.com/leanprover-community/mathlib/pull/2588))
`neg_inv` this lemma with the equality swapped was already in the library, so maybe we should just get rid of this or `neg_inv`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/inv_neg/near/196042954)
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* inv_neg

Modified src/algebra/ordered_field.lean
- \- *lemma* inv_neg



## [2020-05-02 09:41:43](https://github.com/leanprover-community/mathlib/commit/b902f6e)
feat(*): several `@[simp]` lemmas ([#2579](https://github.com/leanprover-community/mathlib/pull/2579))
Also add an explicit instance for `submodule.has_coe_to_sort`.
This way `rintro ⟨x, hx⟩` results in `(hx : x ∈ p)`.
Also fixes some timeouts introduced by [#2363](https://github.com/leanprover-community/mathlib/pull/2363). See Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/partrec_code
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *lemma* prod.mk_eq_one

Modified src/algebra/module.lean
- \+ *lemma* submodule.mk_eq_zero

Modified src/analysis/convex/cone.lean


Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean


Modified src/data/finset.lean


Modified src/data/set/basic.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/logic/basic.lean
- \+ *theorem* exists_comm
- \+ *theorem* exists_exists_and_eq_and
- \+ *theorem* exists_exists_eq_and

Modified src/set_theory/cofinality.lean


Modified src/tactic/converter/binders.lean
- \+/\- *theorem* {u



## [2020-05-02 09:41:41](https://github.com/leanprover-community/mathlib/commit/06bae3e)
fix(data/int/basic): use has_coe_t to prevent looping ([#2573](https://github.com/leanprover-community/mathlib/pull/2573))
The file `src/computability/partrec.lean` no longer opens in vscode because type-class search times out.  This happens because we have the instance `has_coe ℤ α` which causes non-termination because coercions are chained transitively (`has_coe ℤ ℤ`, `has_coe ℤ ℤ`, ...).  Even if the coercions would not apply to integers (and maybe avoid non-termination), it would still enumerate all `0,1,+,-` structures, of which there are unfortunately very many.
This PR therefore downgrades such instances to `has_coe_t` to prevent non-termination due to transitivity.  It also adds a linter to prevent this kind of error in the future.
#### Estimated changes
Modified src/data/fp/basic.lean


Modified src/data/int/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/num/basic.lean


Modified src/data/rat/cast.lean


Modified src/data/zmod/basic.lean


Modified src/group_theory/coset.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/norm_cast.lean
- \+/\- *lemma* ite_cast

Modified test/lint.lean
- \- *def* foo_instance

Added test/lint_coe_t.lean
- \+ *def* a_to_quot
- \+ *def* int_to_a



## [2020-05-02 09:41:39](https://github.com/leanprover-community/mathlib/commit/9d57f68)
feat(order/bounded_lattice): introduce `is_compl` predicate ([#2569](https://github.com/leanprover-community/mathlib/pull/2569))
Also move `disjoint` from `data/set/lattice`
#### Estimated changes
Modified src/combinatorics/composition.lean


Modified src/data/set/lattice.lean
- \- *theorem* disjoint.comm
- \- *theorem* disjoint.eq_bot
- \- *theorem* disjoint.mono
- \- *theorem* disjoint.mono_left
- \- *theorem* disjoint.mono_right
- \- *lemma* disjoint.ne
- \- *theorem* disjoint.symm
- \- *def* disjoint
- \- *theorem* disjoint_bot_left
- \- *theorem* disjoint_bot_right
- \- *theorem* disjoint_iff
- \- *lemma* disjoint_self

Modified src/order/boolean_algebra.lean
- \+ *theorem* is_compl.neg_eq
- \+ *theorem* is_compl_neg

Modified src/order/bounded_lattice.lean
- \+ *theorem* disjoint.comm
- \+ *theorem* disjoint.eq_bot
- \+ *theorem* disjoint.mono
- \+ *theorem* disjoint.mono_left
- \+ *theorem* disjoint.mono_right
- \+ *lemma* disjoint.ne
- \+ *theorem* disjoint.symm
- \+ *def* disjoint
- \+ *theorem* disjoint_bot_left
- \+ *theorem* disjoint_bot_right
- \+ *theorem* disjoint_iff
- \+ *lemma* disjoint_self
- \+ *lemma* is_compl.antimono
- \+ *lemma* is_compl.inf_eq_bot
- \+ *lemma* is_compl.inf_sup
- \+ *lemma* is_compl.le_left_iff
- \+ *lemma* is_compl.le_right_iff
- \+ *lemma* is_compl.left_le_iff
- \+ *lemma* is_compl.left_unique
- \+ *lemma* is_compl.of_eq
- \+ *lemma* is_compl.right_le_iff
- \+ *lemma* is_compl.right_unique
- \+ *lemma* is_compl.sup_eq_top
- \+ *lemma* is_compl.sup_inf
- \+ *lemma* is_compl.to_order_dual
- \+ *lemma* is_compl_bot_top
- \+ *lemma* is_compl_top_bot

Modified src/order/filter/basic.lean
- \+ *lemma* filter.is_compl_principal
- \+/\- *lemma* filter.map_at_top_eq_of_gc

Modified src/order/lattice.lean
- \+ *lemma* eq_of_inf_eq_sup_eq
- \- *lemma* eq_of_sup_eq_inf_eq
- \+ *lemma* le_of_inf_le_sup_le



## [2020-05-02 08:31:10](https://github.com/leanprover-community/mathlib/commit/738bbae)
feat(algebra/group_ring_action): action on polynomials ([#2586](https://github.com/leanprover-community/mathlib/pull/2586))
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \+ *lemma* polynomial.coeff_smul'
- \+ *lemma* polynomial.smul_C
- \+ *lemma* polynomial.smul_X



## [2020-05-02 06:01:16](https://github.com/leanprover-community/mathlib/commit/d0a1d77)
doc(tactic/rcases): mention the "rfl" pattern ([#2585](https://github.com/leanprover-community/mathlib/pull/2585))
Edited from @jcommelin's answer on Zulip here: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/noob.20question%28s%29/near/184491982
#### Estimated changes
Modified src/tactic/rcases.lean




## [2020-05-01 21:31:28](https://github.com/leanprover-community/mathlib/commit/eb383b1)
chore(group_theory/perm): delete duplicate lemmas ([#2584](https://github.com/leanprover-community/mathlib/pull/2584))
`sum_univ_perm` is a special case of `sum_equiv`, so it's not necessary. 
I also moved `sum_equiv` into the `finset` namespace.
#### Estimated changes
Modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_equiv
- \- *lemma* prod_equiv

Modified src/group_theory/perm/sign.lean
- \- *lemma* finset.prod_univ_perm
- \- *lemma* finset.sum_univ_perm

Modified src/linear_algebra/determinant.lean


Modified src/number_theory/sum_four_squares.lean




## [2020-05-01 15:51:57](https://github.com/leanprover-community/mathlib/commit/4daa7e8)
feat(algebra/lie_algebra): define simple Lie algebras and define classical Lie algebra, slₙ ([#2567](https://github.com/leanprover-community/mathlib/pull/2567))
The changes here introduce a few important properties of Lie algebras and also begin providing definitions of the classical Lie algebras. The key changes are the following definitions:
 * `lie_algebra.is_abelian`
 * `lie_module.is_irreducible`
 * `lie_algebra.is_simple`
 * `lie_algebra.special_linear.sl`
Some simple related proofs are also included such as:
 * `commutative_ring_iff_abelian_lie_ring`
 * `lie_algebra.special_linear.sl_non_abelian`
#### Estimated changes
Added src/algebra/classical_lie_algebras.lean
- \+ *lemma* lie_algebra.matrix_trace_commutator_zero
- \+ *lemma* lie_algebra.special_linear.E_apply_one
- \+ *lemma* lie_algebra.special_linear.E_apply_zero
- \+ *lemma* lie_algebra.special_linear.E_diag_zero
- \+ *lemma* lie_algebra.special_linear.E_trace_zero
- \+ *def* lie_algebra.special_linear.Eb
- \+ *lemma* lie_algebra.special_linear.Eb_val
- \+ *def* lie_algebra.special_linear.sl
- \+ *lemma* lie_algebra.special_linear.sl_bracket
- \+ *lemma* lie_algebra.special_linear.sl_non_abelian

Modified src/algebra/lie_algebra.lean
- \+ *lemma* commutative_ring_iff_abelian_lie_ring
- \+ *lemma* lie_ring.of_associative_ring_bracket
- \- *def* lie_subalgebra_lie_algebra
- \- *def* lie_subalgebra_lie_ring

Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.exists_pair_of_one_lt_card

Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.diag_apply
- \+ *lemma* matrix.trace_diag



## [2020-05-01 12:56:42](https://github.com/leanprover-community/mathlib/commit/6a2559a)
chore(algebra/group_with_zero): rename div_eq_inv_mul' to div_eq_inv_mul ([#2583](https://github.com/leanprover-community/mathlib/pull/2583))
There are no occurrences of the name without ' in either core or mathlib
so this change in name (from [#2242](https://github.com/leanprover-community/mathlib/pull/2242)) seems to have been unnecessary.
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \- *lemma* div_eq_inv_mul'
- \+ *lemma* div_eq_inv_mul

Modified src/algebra/ordered_field.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/topology/metric_space/antilipschitz.lean




## [2020-05-01 10:09:30](https://github.com/leanprover-community/mathlib/commit/ee488b2)
fix(tactic/lint/basic): remove default argument for auto_decl and enable more linters ([#2580](https://github.com/leanprover-community/mathlib/pull/2580))
Run more linters on automatically-generated declarations.  Quite a few linters should have been run on them, but I forgot about it because the `auto_decls` flag is optional and off by default.  I've made it non-optional so that you don't forget about it when defining a linter.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simp.20linter.20and.20structure.20fields/near/195810856
#### Estimated changes
Modified src/data/list/forall2.lean
- \+/\- *lemma* list.forall₂_nil_left_iff
- \+/\- *lemma* list.forall₂_nil_right_iff

Modified src/tactic/lint/basic.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/lint/type_classes.lean


Modified test/lint.lean




## [2020-05-01 07:42:20](https://github.com/leanprover-community/mathlib/commit/67f3fde)
feat(algebra/group_ring_action) define group actions on rings ([#2566](https://github.com/leanprover-community/mathlib/pull/2566))
Define group action on rings.
Related Zulip discussions: 
- https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232566.20group.20actions.20on.20ring 
- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_action
#### Estimated changes
Added src/algebra/group_ring_action.lean
- \+ *def* add_monoid.End
- \+ *def* distrib_mul_action.hom_add_monoid_hom
- \+ *def* distrib_mul_action.to_add_equiv
- \+ *def* distrib_mul_action.to_add_monoid_hom
- \+ *def* monoid.End
- \+ *def* mul_semiring_action.to_semiring_equiv
- \+ *def* mul_semiring_action.to_semiring_hom
- \+ *lemma* smul_inv
- \+ *lemma* smul_mul'
- \+ *lemma* smul_pow

Modified src/group_theory/group_action.lean




## [2020-05-01 05:59:47](https://github.com/leanprover-community/mathlib/commit/74d24ab)
feat(topology/instances/real_vector_space): `E →+ F` to `E →L[ℝ] F` ([#2577](https://github.com/leanprover-community/mathlib/pull/2577))
A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear.
#### Estimated changes
Added src/topology/instances/real_vector_space.lean
- \+ *lemma* add_monoid_hom.coe_to_real_linear_map
- \+ *lemma* add_monoid_hom.map_real_smul
- \+ *def* add_monoid_hom.to_real_linear_map



## [2020-05-01 04:49:00](https://github.com/leanprover-community/mathlib/commit/d3140fb)
feat(data/mv_polynomial): lemmas on total_degree ([#2575](https://github.com/leanprover-community/mathlib/pull/2575))
This is a small preparation for the Chevalley–Warning theorem.
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.eval_one
- \+ *lemma* mv_polynomial.eval_pow
- \+/\- *lemma* mv_polynomial.total_degree_C
- \+ *lemma* mv_polynomial.total_degree_X
- \+ *lemma* mv_polynomial.total_degree_neg
- \+/\- *lemma* mv_polynomial.total_degree_one
- \+ *lemma* mv_polynomial.total_degree_pow
- \+ *lemma* mv_polynomial.total_degree_sub
- \+/\- *lemma* mv_polynomial.total_degree_zero

