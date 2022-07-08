## [2020-05-31 20:01:07](https://github.com/leanprover-community/mathlib/commit/d3fc918)
chore(scripts): update nolints.txt ([#2892](https://github.com/leanprover-community/mathlib/pull/2892))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-31 18:58:17](https://github.com/leanprover-community/mathlib/commit/1fd5195)
chore(data/equiv/mul_add): review ([#2874](https://github.com/leanprover-community/mathlib/pull/2874))
* make `mul_aut` and `add_aut` reducible to get `coe_fn`
* add some `coe_*` lemmas
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_mul_left
- \+ *lemma* mul_left_symm
- \+ *lemma* coe_mul_right
- \+ *lemma* mul_right_symm
- \+ *lemma* coe_inv
- \+ *lemma* inv_symm



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
modified leanpkg.toml

modified src/algebra/category/CommRing/adjunctions.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/free.lean

modified src/category_theory/elements.lean
- \+ *lemma* ext
- \+ *lemma* comp_val
- \+ *lemma* id_val

modified src/category_theory/endomorphism.lean

modified src/category_theory/types.lean

modified src/control/applicative.lean

modified src/control/fold.lean

modified src/control/traversable/instances.lean

modified src/data/erased.lean
- \+ *lemma* out_inj
- \+ *lemma* pure_def
- \+ *lemma* bind_def
- \+ *lemma* map_def
- \+/\- *theorem* nonempty_iff
- \+ *theorem* map_out
- \+/\- *theorem* nonempty_iff
- \+/\- *def* erased
- \+/\- *def* out_type
- \+ *def* map
- \+/\- *def* erased
- \+/\- *def* out_type

modified src/data/list/defs.lean
- \- *def* map_with_index_core
- \- *def* map_with_index

modified src/data/multiset.lean
- \+ *lemma* fmap_def
- \+ *lemma* pure_def
- \+ *lemma* bind_def

modified src/data/padics/hensel.lean

modified src/data/padics/padic_integers.lean
- \+ *lemma* ext
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_sub
- \+/\- *lemma* mk_coe
- \+ *lemma* padic_norm_z
- \- *lemma* zero_def
- \- *lemma* add_def
- \- *lemma* mul_def
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* mk_coe
- \- *def* add
- \- *def* mul
- \- *def* neg
- \- *def* padic_norm_z

modified src/data/semiquot.lean
- \+ *lemma* map_def
- \+ *lemma* bind_def

modified src/data/set/lattice.lean

modified src/data/string/basic.lean

modified src/group_theory/submonoid.lean
- \+ *lemma* coe_eq_coe

modified src/linear_algebra/dual.lean

modified src/measure_theory/measure_space.lean

modified src/measure_theory/outer_measure.lean

modified src/order/copy.lean

modified src/tactic/doc_commands.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/category/UniformSpace.lean



## [2020-05-31 15:03:10](https://github.com/leanprover-community/mathlib/commit/25fc0a8)
feat(field_theory/splitting_field): lemmas ([#2887](https://github.com/leanprover-community/mathlib/pull/2887))
#### Estimated changes
modified src/field_theory/splitting_field.lean
- \+ *theorem* splits_one
- \+ *theorem* splits_X_sub_C
- \+ *theorem* splits_id_iff_splits
- \+ *theorem* splits_mul_iff
- \+ *theorem* splits_prod
- \+ *theorem* splits_prod_iff



## [2020-05-31 06:22:54](https://github.com/leanprover-community/mathlib/commit/13b34b3)
chore(*): split long lines ([#2883](https://github.com/leanprover-community/mathlib/pull/2883))
Also move docs for `control/fold` from a comment to a module docstring.
#### Estimated changes
modified src/algebra/commute.lean

modified src/algebra/free.lean
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *def* free_add_semigroup.lift'
- \+/\- *def* free_add_semigroup.lift'

modified src/algebra/pi_instances.lean

modified src/algebraic_geometry/presheafed_space.lean

modified src/category_theory/connected.lean
- \+/\- *lemma* constant_of_preserves_morphisms
- \+/\- *lemma* constant_of_preserves_morphisms

modified src/category_theory/endomorphism.lean

modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* hom_inv_id_app
- \+/\- *lemma* inv_hom_id_app
- \+/\- *lemma* hom_inv_id_app
- \+/\- *lemma* inv_hom_id_app

modified src/category_theory/products/basic.lean

modified src/control/fold.lean
- \+/\- *lemma* foldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* foldr.of_free_monoid_comp_free_mk
- \+/\- *lemma* mfoldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* mfoldr.of_free_monoid_comp_free_mk
- \+/\- *lemma* foldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* foldr.of_free_monoid_comp_free_mk
- \+/\- *lemma* mfoldl.of_free_monoid_comp_free_mk
- \+/\- *lemma* mfoldr.of_free_monoid_comp_free_mk
- \+/\- *def* mfoldl
- \+/\- *def* mfoldl

modified src/data/finsupp.lean
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_comm

modified src/data/list/pairwise.lean

modified src/data/option/basic.lean
- \+/\- *theorem* bind_eq_some
- \+/\- *theorem* bind_eq_some'
- \+/\- *theorem* map_eq_some
- \+/\- *theorem* map_eq_some'
- \+/\- *theorem* bind_eq_some
- \+/\- *theorem* bind_eq_some'
- \+/\- *theorem* map_eq_some
- \+/\- *theorem* map_eq_some'

modified src/group_theory/subgroup.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

modified src/measure_theory/measurable_space.lean

modified src/meta/expr.lean

modified src/topology/basic.lean

modified src/topology/category/Top/opens.lean
- \+/\- *lemma* map_comp_obj
- \+/\- *lemma* map_comp_obj'
- \+/\- *lemma* map_comp_obj_unop
- \+/\- *lemma* op_map_comp_obj
- \+/\- *lemma* map_comp_hom_app
- \+/\- *lemma* map_comp_inv_app
- \+/\- *lemma* map_comp_obj
- \+/\- *lemma* map_comp_obj'
- \+/\- *lemma* map_comp_obj_unop
- \+/\- *lemma* op_map_comp_obj
- \+/\- *lemma* map_comp_hom_app
- \+/\- *lemma* map_comp_inv_app

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/order.lean
- \+/\- *lemma* continuous_of_discrete_topology
- \+/\- *lemma* continuous_of_discrete_topology

modified src/topology/uniform_space/basic.lean



## [2020-05-31 04:59:04](https://github.com/leanprover-community/mathlib/commit/a285049)
chore(algebra/group_hom): rename `add_monoid.smul` to `nsmul` ([#2861](https://github.com/leanprover-community/mathlib/pull/2861))
Also drop `•` as a notation for two `smul`s  declared in this file,
use `•ℕ` and `•ℤ` instead.
This way one can immediately see that a lemma uses `nsmul`/`gsmul`, not `has_scalar.smul`.
#### Estimated changes
modified src/algebra/archimedean.lean

modified src/algebra/big_operators.lean
- \+ *lemma* sum_nsmul
- \- *lemma* sum_smul'

modified src/algebra/commute.lean
- \+ *theorem* nsmul_right
- \+ *theorem* nsmul_left
- \+ *theorem* nsmul_nsmul
- \+ *theorem* self_nsmul
- \+ *theorem* nsmul_self
- \+ *theorem* self_nsmul_nsmul
- \- *theorem* smul_right
- \- *theorem* smul_left
- \- *theorem* smul_smul
- \- *theorem* self_smul
- \- *theorem* smul_self
- \- *theorem* self_smul_smul

modified src/algebra/geom_sum.lean

modified src/algebra/group_power.lean
- \+ *lemma* with_bot.coe_nsmul
- \+ *lemma* nsmul_le_nsmul_of_le_right
- \+ *lemma* of_add_nsmul
- \- *lemma* with_bot.coe_smul
- \- *lemma* smul_le_smul_of_le_right
- \- *lemma* of_add_smul
- \+ *theorem* zero_nsmul
- \+ *theorem* succ_nsmul
- \+ *theorem* one_nsmul
- \+ *theorem* nsmul_add_comm'
- \+ *theorem* succ_nsmul'
- \+ *theorem* two_nsmul
- \+ *theorem* add_nsmul
- \+ *theorem* nsmul_zero
- \+ *theorem* mul_nsmul'
- \+ *theorem* mul_nsmul
- \+ *theorem* nsmul_one
- \+ *theorem* bit0_nsmul
- \+ *theorem* bit1_nsmul
- \+ *theorem* nsmul_add_comm
- \+/\- *theorem* list.sum_repeat
- \+ *theorem* add_monoid_hom.map_nsmul
- \+ *theorem* is_add_monoid_hom.map_nsmul
- \+ *theorem* nat.nsmul_eq_mul
- \+ *theorem* nsmul_add
- \+ *theorem* neg_nsmul
- \+ *theorem* nsmul_sub
- \+ *theorem* nsmul_neg_comm
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* zero_gsmul
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* bit0_gsmul
- \+/\- *theorem* bit1_gsmul
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \+ *theorem* nsmul_eq_mul'
- \+ *theorem* nsmul_eq_mul
- \+ *theorem* mul_nsmul_left
- \+ *theorem* mul_nsmul_assoc
- \+ *theorem* nsmul_nonneg
- \+ *theorem* nsmul_le_nsmul
- \- *theorem* add_monoid.zero_smul
- \- *theorem* succ_smul
- \- *theorem* add_monoid.one_smul
- \- *theorem* smul_add_comm'
- \- *theorem* succ_smul'
- \- *theorem* two_smul'
- \- *theorem* add_monoid.add_smul
- \- *theorem* add_monoid.smul_zero
- \- *theorem* add_monoid.mul_smul'
- \- *theorem* add_monoid.mul_smul
- \- *theorem* add_monoid.smul_one
- \- *theorem* bit0_smul
- \- *theorem* bit1_smul
- \- *theorem* smul_add_comm
- \+/\- *theorem* list.sum_repeat
- \- *theorem* add_monoid_hom.map_smul
- \- *theorem* is_add_monoid_hom.map_smul
- \- *theorem* nat.smul_eq_mul
- \- *theorem* add_monoid.smul_add
- \- *theorem* add_monoid.neg_smul
- \- *theorem* add_monoid.smul_sub
- \- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* zero_gsmul
- \+/\- *theorem* one_gsmul
- \+/\- *theorem* gsmul_zero
- \+/\- *theorem* neg_gsmul
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* gsmul_one
- \+/\- *theorem* add_gsmul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* one_add_gsmul
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* bit0_gsmul
- \+/\- *theorem* bit1_gsmul
- \+/\- *theorem* add_monoid_hom.map_gsmul
- \- *theorem* add_monoid.smul_eq_mul'
- \- *theorem* add_monoid.smul_eq_mul
- \- *theorem* add_monoid.mul_smul_left
- \- *theorem* add_monoid.mul_smul_assoc
- \- *theorem* add_monoid.smul_nonneg
- \- *theorem* smul_le_smul
- \+ *def* nsmul
- \- *def* add_monoid.smul

modified src/algebra/iterate_hom.lean

modified src/algebra/module.lean
- \+ *lemma* semimodule.nsmul_eq_smul
- \- *lemma* semimodule.add_monoid_smul_eq_smul

modified src/algebra/semiconj.lean
- \+ *lemma* nsmul_right
- \+ *lemma* nsmul_left
- \+ *lemma* nsmul_nsmul
- \- *lemma* smul_right
- \- *lemma* smul_left
- \- *lemma* smul_smul

modified src/analysis/analytic/composition.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/special_functions/trigonometric.lean

modified src/analysis/specific_limits.lean

modified src/data/complex/exponential.lean

modified src/data/finset.lean
- \+ *lemma* to_finset_nsmul
- \- *lemma* to_finset_smul

modified src/data/finsupp.lean
- \+/\- *lemma* to_multiset_single
- \+/\- *lemma* to_multiset_single

modified src/data/multiset.lean
- \+/\- *theorem* sum_repeat
- \+/\- *theorem* count_smul
- \+/\- *theorem* sum_repeat
- \+/\- *theorem* count_smul

modified src/data/mv_polynomial.lean

modified src/data/nat/multiplicity.lean

modified src/data/pnat/factors.lean

modified src/data/polynomial.lean
- \+/\- *lemma* degree_pow_le
- \+/\- *lemma* degree_pow_le

modified src/data/real/nnreal.lean
- \+ *lemma* nsmul_coe
- \- *lemma* smul_coe

modified src/field_theory/finite.lean

modified src/field_theory/mv_polynomial.lean

modified src/group_theory/submonoid.lean
- \+/\- *lemma* multiples.zero_mem
- \+/\- *lemma* multiples.self_mem
- \+/\- *lemma* multiples.zero_mem
- \+/\- *lemma* multiples.self_mem
- \+/\- *def* multiples
- \+/\- *def* multiples

modified src/linear_algebra/matrix.lean

modified src/linear_algebra/multilinear.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/subsemiring.lean

modified src/tactic/abel.lean
- \+/\- *def* term
- \+/\- *def* termg
- \+/\- *def* smul
- \+/\- *def* smulg
- \+/\- *def* term
- \+/\- *def* termg
- \+/\- *def* smul
- \+/\- *def* smulg



## [2020-05-31 01:56:14](https://github.com/leanprover-community/mathlib/commit/28e79d4)
chore(data/set/basic): add some lemmas to `function.surjective` ([#2876](https://github.com/leanprover-community/mathlib/pull/2876))
This way they can be used with dot notation. Also rename
`set.surjective_preimage` to
`function.surjective.injective_preimage`. I think that the old name
was misleading.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* surjective.injective_preimage
- \+ *lemma* surjective.range_eq
- \+ *lemma* surjective.range_comp
- \- *lemma* surjective_preimage



## [2020-05-31 01:56:12](https://github.com/leanprover-community/mathlib/commit/297806e)
feat(topology/homeomorph): sum_prod_distrib ([#2870](https://github.com/leanprover-community/mathlib/pull/2870))
Also modify the `inv_fun` of `equiv.sum_prod_distrib` to have
more useful definitional behavior. This also simplifies
`measurable_equiv.sum_prod_distrib`.
#### Estimated changes
modified src/data/equiv/basic.lean

modified src/measure_theory/measurable_space.lean

modified src/topology/constructions.lean
- \+/\- *lemma* continuous_inl
- \+/\- *lemma* continuous_inr
- \+ *lemma* is_open_sum_iff
- \+ *lemma* is_open_map_sum
- \+/\- *lemma* embedding_inl
- \+/\- *lemma* embedding_inr
- \+ *lemma* open_embedding_inl
- \+ *lemma* open_embedding_inr
- \+/\- *lemma* continuous_inl
- \+/\- *lemma* continuous_inr
- \+/\- *lemma* embedding_inl
- \+/\- *lemma* embedding_inr

modified src/topology/homeomorph.lean
- \+ *def* sum_congr
- \+ *def* sum_prod_distrib
- \+ *def* prod_sum_distrib



## [2020-05-30 22:43:58](https://github.com/leanprover-community/mathlib/commit/0827a30)
feat(tactic/noncomm_ring): add noncomm_ring tactic ([#2858](https://github.com/leanprover-community/mathlib/pull/2858))
Fixes https://github.com/leanprover-community/mathlib/issues/2727
#### Estimated changes
modified src/algebra/classical_lie_algebras.lean

modified src/algebra/group_power.lean
- \+ *lemma* bit0_mul
- \+ *lemma* mul_bit0
- \+ *lemma* bit1_mul
- \+ *lemma* mul_bit1

modified src/algebra/lie_algebra.lean

modified src/linear_algebra/bilinear_form.lean

modified src/tactic/default.lean

created src/tactic/noncomm_ring.lean

created test/noncomm_ring.lean



## [2020-05-30 21:15:08](https://github.com/leanprover-community/mathlib/commit/6e581ef)
chore(scripts): update nolints.txt ([#2878](https://github.com/leanprover-community/mathlib/pull/2878))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-30 19:55:19](https://github.com/leanprover-community/mathlib/commit/c034b4c)
chore(order/bounds): +2 lemmas, fix a name ([#2877](https://github.com/leanprover-community/mathlib/pull/2877))
#### Estimated changes
modified src/order/bounds.lean
- \+ *lemma* mem_upper_bounds
- \+ *lemma* mem_lower_bounds
- \+ *lemma* le_is_glb_image
- \- *lemma* le_is_glb_image_le



## [2020-05-30 19:08:27](https://github.com/leanprover-community/mathlib/commit/9d76ac2)
chore(scripts): update nolints.txt ([#2873](https://github.com/leanprover-community/mathlib/pull/2873))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-30 18:01:32](https://github.com/leanprover-community/mathlib/commit/f05acc8)
feat(group_theory/group_action): orbit_equiv_quotient_stabilizer_symm_apply and docs ([#2864](https://github.com/leanprover-community/mathlib/pull/2864))
#### Estimated changes
modified src/group_theory/group_action.lean
- \+ *theorem* orbit_equiv_quotient_stabilizer_symm_apply



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
modified src/algebra/direct_limit.lean

modified src/algebra/group/basic.lean

modified src/algebra/lie_algebra.lean

modified src/algebra/module.lean
- \+/\- *lemma* id_apply
- \+/\- *lemma* map_sum
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* is_linear_map_smul
- \+/\- *lemma* is_linear_map_smul'
- \+/\- *lemma* map_smul
- \+/\- *lemma* is_linear_map_neg
- \+/\- *lemma* map_neg
- \+/\- *lemma* neg_mem
- \+/\- *lemma* sub_mem
- \+/\- *lemma* neg_mem_iff
- \+/\- *lemma* add_mem_iff_left
- \+/\- *lemma* add_mem_iff_right
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_sum
- \+/\- *lemma* id_apply
- \+/\- *lemma* is_linear_map_neg
- \+/\- *lemma* is_linear_map_smul
- \+/\- *lemma* is_linear_map_smul'
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_smul
- \+/\- *lemma* neg_mem
- \+/\- *lemma* sub_mem
- \+/\- *lemma* neg_mem_iff
- \+/\- *lemma* add_mem_iff_left
- \+/\- *lemma* add_mem_iff_right
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* module.gsmul_eq_smul_cast
- \+/\- *theorem* smul_neg
- \+/\- *theorem* smul_sub
- \+/\- *theorem* smul_neg
- \+/\- *theorem* smul_sub
- \+ *def* semimodule.of_core
- \+/\- *def* id
- \- *def* module.of_core
- \- *def* ring_hom.to_module
- \+/\- *def* id
- \- *def* subspace

modified src/algebra/pi_instances.lean

modified src/algebra/punit_instances.lean

modified src/algebra/ring.lean

modified src/analysis/calculus/darboux.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/convex/basic.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/data/dfinsupp.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply
- \+/\- *def* to_has_scalar
- \+ *def* to_semimodule
- \+/\- *def* to_has_scalar
- \- *def* to_module

modified src/data/finsupp.lean
- \+/\- *def* restrict_support_equiv
- \+/\- *def* restrict_support_equiv

modified src/data/holor.lean

modified src/data/matrix/basic.lean

modified src/field_theory/finite.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* mem_span_insert'
- \+/\- *lemma* finsupp_sum
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* comap_map_eq_self
- \+/\- *lemma* submodule.sup_eq_range
- \+/\- *lemma* is_linear_map_add
- \+/\- *lemma* is_linear_map_sub
- \+/\- *lemma* disjoint_iff_comap_eq_bot
- \+/\- *lemma* map_subtype_embedding_eq
- \+/\- *lemma* linear_map.range_range_restrict
- \+/\- *lemma* refl_apply
- \+/\- *lemma* eq_bot_of_equiv
- \+/\- *lemma* skew_prod_apply
- \+/\- *lemma* skew_prod_symm_apply
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* mem_span_insert'
- \+/\- *lemma* finsupp_sum
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* comap_map_eq_self
- \+/\- *lemma* submodule.sup_eq_range
- \+/\- *lemma* is_linear_map_add
- \+/\- *lemma* is_linear_map_sub
- \+/\- *lemma* disjoint_iff_comap_eq_bot
- \+/\- *lemma* map_subtype_embedding_eq
- \+/\- *lemma* linear_map.range_range_restrict
- \+/\- *lemma* refl_apply
- \+/\- *lemma* skew_prod_apply
- \+/\- *lemma* skew_prod_symm_apply
- \+/\- *lemma* eq_bot_of_equiv
- \+ *theorem* ker_eq_bot_of_injective
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* map_le_map_iff'
- \+/\- *theorem* map_injective
- \+/\- *theorem* map_eq_top_iff
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot
- \+/\- *theorem* map_neg
- \+/\- *theorem* map_sub
- \+/\- *theorem* of_bijective_apply
- \+/\- *theorem* sub_mem_ker_iff
- \+/\- *theorem* disjoint_ker'
- \+/\- *theorem* inj_of_disjoint_ker
- \+/\- *theorem* ker_eq_bot
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* map_le_map_iff'
- \+/\- *theorem* map_injective
- \+/\- *theorem* map_eq_top_iff
- \+/\- *theorem* map_neg
- \+/\- *theorem* map_sub
- \+/\- *theorem* of_bijective_apply
- \+/\- *def* map_subtype.order_iso
- \+/\- *def* map_subtype.le_order_embedding
- \+/\- *def* map_subtype.lt_order_embedding
- \+/\- *def* refl
- \+/\- *def* map_subtype.order_iso
- \+/\- *def* map_subtype.le_order_embedding
- \+/\- *def* map_subtype.lt_order_embedding
- \+/\- *def* refl

modified src/linear_algebra/basis.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/contraction.lean
- \+/\- *def* contract_right
- \+/\- *def* contract_right

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/direct_sum_module.lean

modified src/linear_algebra/dual.lean
- \+/\- *def* eval
- \+/\- *def* eval

modified src/linear_algebra/finsupp.lean
- \+/\- *def* supported_equiv_finsupp
- \+/\- *def* supported_equiv_finsupp

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/matrix.lean
- \+/\- *lemma* to_lin_neg
- \+/\- *lemma* diagonal_to_lin
- \+/\- *lemma* to_lin_neg
- \+/\- *lemma* diagonal_to_lin

modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* map_sub
- \+/\- *lemma* neg_apply
- \+/\- *lemma* map_sub
- \+/\- *lemma* neg_apply

modified src/linear_algebra/tensor_product.lean
- \+/\- *def* flip
- \+/\- *def* lcomp
- \+/\- *def* uncurry
- \+/\- *def* flip
- \+/\- *def* lcomp
- \+/\- *def* uncurry

modified src/measure_theory/bochner_integration.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/algebra_operations.lean

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/topology/algebra/module.lean
- \+/\- *lemma* comp_add
- \+/\- *lemma* add_comp
- \+/\- *lemma* is_complete_ker
- \+/\- *lemma* smul_right_comp
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* smul_right_one_pow
- \+/\- *lemma* coe_proj_ker_of_right_inverse_apply
- \+/\- *lemma* proj_ker_of_right_inverse_apply_idem
- \+/\- *lemma* proj_ker_of_right_inverse_comp_inv
- \+/\- *lemma* skew_prod_apply
- \+/\- *lemma* skew_prod_symm_apply
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* comp_add
- \+/\- *lemma* add_comp
- \+/\- *lemma* is_complete_ker
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* coe_proj_ker_of_right_inverse_apply
- \+/\- *lemma* proj_ker_of_right_inverse_apply_idem
- \+/\- *lemma* proj_ker_of_right_inverse_comp_inv
- \+/\- *lemma* smul_right_comp
- \+/\- *lemma* smul_right_one_pow
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* skew_prod_apply
- \+/\- *lemma* skew_prod_symm_apply
- \+/\- *def* proj_ker_of_right_inverse
- \+/\- *def* skew_prod
- \+/\- *def* proj_ker_of_right_inverse
- \+/\- *def* skew_prod

modified src/topology/algebra/multilinear.lean
- \+ *lemma* coe_coe
- \+/\- *lemma* map_sub
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* map_sub
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *def* to_multilinear_map_linear
- \+/\- *def* to_multilinear_map_linear

modified src/topology/basic.lean

modified src/topology/bounded_continuous_function.lean



## [2020-05-30 15:05:49](https://github.com/leanprover-community/mathlib/commit/cc06d53)
feat(algebra/big_operators): prod_ne_zero ([#2863](https://github.com/leanprover-community/mathlib/pull/2863))
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *theorem* prod_ne_zero_iff



## [2020-05-30 13:12:33](https://github.com/leanprover-community/mathlib/commit/b40ac2a)
chore(topology): make topological_space fields protected ([#2867](https://github.com/leanprover-community/mathlib/pull/2867))
This uses the recent `protect_proj` attribute ([#2855](https://github.com/leanprover-community/mathlib/pull/2855)).
#### Estimated changes
modified src/topology/bases.lean

modified src/topology/basic.lean

modified src/topology/opens.lean
- \+/\- *def* opens
- \+/\- *def* opens

modified src/topology/order.lean



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
modified src/analysis/normed_space/real_inner_product.lean
- \+/\- *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_nonpos
- \+/\- *lemma* inner_self_eq_norm_square
- \+ *lemma* euclidean_space.inner_def
- \+/\- *lemma* inner_self_eq_zero
- \+/\- *lemma* inner_self_eq_norm_square
- \+ *def* pi.inner_product_space
- \+ *def* real.inner_product_space
- \+ *def* euclidean_space

created src/geometry/euclidean.lean

modified src/geometry/manifold/real_instances.lean
- \+/\- *lemma* findim_euclidean_space
- \+/\- *lemma* findim_euclidean_space
- \+ *def* euclidean_space2
- \+/\- *def* euclidean_quadrant
- \- *def* euclidean_space
- \+/\- *def* euclidean_quadrant



## [2020-05-30 06:12:38](https://github.com/leanprover-community/mathlib/commit/74d446d)
feat(order/iterate): some inequalities on `f^[n] x` and `g^[n] x` ([#2859](https://github.com/leanprover-community/mathlib/pull/2859))
#### Estimated changes
created src/order/iterate.lean
- \+ *lemma* iterate_le_of_map_le
- \+ *lemma* iterate_pos_lt_of_map_lt
- \+ *lemma* iterate_pos_lt_of_map_lt'
- \+ *lemma* iterate_pos_lt_iff_map_lt
- \+ *lemma* iterate_pos_lt_iff_map_lt'



## [2020-05-30 04:46:16](https://github.com/leanprover-community/mathlib/commit/aa47bba)
feat(data/equiv): equiv_of_subsingleton_of_subsingleton ([#2856](https://github.com/leanprover-community/mathlib/pull/2856))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* equiv_of_subsingleton_of_subsingleton



## [2020-05-30 00:45:00](https://github.com/leanprover-community/mathlib/commit/5455fe1)
chore(scripts): update nolints.txt ([#2862](https://github.com/leanprover-community/mathlib/pull/2862))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-29 22:20:28](https://github.com/leanprover-community/mathlib/commit/f95e809)
chore(algebra): displace zero_ne_one_class with nonzero and make no_zero_divisors a Prop ([#2847](https://github.com/leanprover-community/mathlib/pull/2847))
- `[nonzero_semiring α]` becomes `[semiring α] [nonzero α]`
- `[nonzero_comm_semiring α]` becomes `[comm_semiring α] [nonzero α]`
- `[nonzero_comm_ring α]` becomes `[comm_ring α] [nonzero α]`
- `no_zero_divisors` is now a `Prop`
- `units.ne_zero` (originally for `domain`) merges into `units.coe_ne_zero` (originally for `nonzero_comm_semiring`)
#### Estimated changes
modified src/algebra/associated.lean
- \+/\- *theorem* not_is_unit_zero
- \+/\- *theorem* not_is_unit_zero

modified src/algebra/char_p.lean
- \+/\- *lemma* false_of_nonzero_of_char_one
- \+/\- *lemma* ring_char_ne_one
- \+/\- *lemma* false_of_nonzero_of_char_one
- \+/\- *lemma* ring_char_ne_one

modified src/algebra/classical_lie_algebras.lean
- \+/\- *lemma* sl_non_abelian
- \+/\- *lemma* sl_non_abelian

modified src/algebra/direct_limit.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/field.lean

modified src/algebra/gcd_domain.lean

modified src/algebra/group/with_one.lean

modified src/algebra/group_with_zero.lean

modified src/algebra/opposites.lean

modified src/algebra/ordered_ring.lean

modified src/algebra/ring.lean
- \+/\- *lemma* zero_ne_one
- \+/\- *lemma* one_ne_zero
- \+/\- *lemma* succ_ne_self
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* units.coe_ne_zero
- \+/\- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* eq_zero_of_mul_self_eq_zero
- \+/\- *lemma* zero_ne_one
- \+/\- *lemma* one_ne_zero
- \+/\- *lemma* succ_ne_self
- \+/\- *lemma* pred_ne_self
- \+/\- *lemma* units.coe_ne_zero
- \+/\- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* eq_zero_of_mul_self_eq_zero
- \+ *theorem* nonzero.of_ne
- \- *theorem* ne_zero
- \- *def* nonzero_comm_ring.of_ne
- \- *def* nonzero_comm_semiring.of_ne

modified src/analysis/special_functions/pow.lean

modified src/data/complex/exponential.lean

modified src/data/equiv/ring.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/matrix/pequiv.lean
- \+/\- *lemma* to_matrix_injective
- \+/\- *lemma* to_matrix_injective

modified src/data/mv_polynomial.lean
- \+/\- *lemma* total_degree_X
- \+/\- *lemma* total_degree_X

modified src/data/padics/padic_integers.lean

modified src/data/polynomial.lean
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* monic.ne_zero
- \+ *theorem* nonzero.of_polynomial_ne
- \- *def* nonzero_comm_semiring.of_polynomial_ne
- \- *def* nonzero_comm_ring.of_polynomial_ne

modified src/data/rat/basic.lean

modified src/data/real/basic.lean

modified src/data/real/nnreal.lean

modified src/data/zmod/basic.lean

modified src/data/zsqrtd/basic.lean

modified src/data/zsqrtd/gaussian_int.lean

modified src/field_theory/subfield.lean

modified src/init_/data/int/basic.lean

modified src/init_/data/nat/lemmas.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/lagrange.lean

modified src/order/filter/filter_product.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/fintype.lean
- \+/\- *lemma* card_units_lt
- \+/\- *lemma* card_units_lt

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/ideal_operations.lean
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* not_one_mem_ker

modified src/ring_theory/ideals.lean

modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *lemma* finite_of_linear_independent

modified src/ring_theory/polynomial.lean

modified src/ring_theory/power_series.lean

modified src/ring_theory/prod.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/ordinal.lean

modified test/lint.lean



## [2020-05-29 20:46:37](https://github.com/leanprover-community/mathlib/commit/b2f643e)
feat(dynamics/fixed_points): define `is_fixed_pt` ([#2857](https://github.com/leanprover-community/mathlib/pull/2857))
Define `function.is_fixed_pt` and prove some basic properties.
#### Estimated changes
modified src/analysis/calculus/inverse.lean

created src/dynamics/fixed_points.lean
- \+ *lemma* is_fixed_pt_id
- \+ *lemma* left_of_comp
- \+ *lemma* to_left_inverse
- \+ *lemma* mem_fixed_points
- \+ *lemma* semiconj.maps_to_fixed_pts
- \+ *lemma* inv_on_fixed_pts_comp
- \+ *lemma* maps_to_fixed_pts_comp
- \+ *lemma* bij_on_fixed_pts_comp
- \+ *lemma* commute.inv_on_fixed_pts_comp
- \+ *lemma* commute.left_bij_on_fixed_pts_comp
- \+ *lemma* commute.right_bij_on_fixed_pts_comp
- \+ *def* is_fixed_pt
- \+ *def* fixed_points

modified src/logic/function/iterate.lean
- \+ *lemma* comp_iterate
- \+ *lemma* iterate_self
- \+ *lemma* self_iterate
- \+ *lemma* iterate_iterate_self
- \+ *theorem* iterate_pred_comp_of_pos
- \+ *theorem* comp_iterate_pred_of_pos

modified src/order/fixed_points.lean
- \- *def* fixed_points

modified src/topology/metric_space/contracting.lean
- \+ *lemma* is_fixed_pt_of_tendsto_iterate
- \+ *lemma* efixed_point_is_fixed_pt
- \+ *lemma* efixed_point_is_fixed_pt'
- \+/\- *lemma* dist_le_of_fixed_point
- \+ *lemma* fixed_point_is_fixed_pt
- \+/\- *lemma* fixed_point_unique
- \- *lemma* fixed_point_of_tendsto_iterate
- \- *lemma* efixed_point_is_fixed
- \- *lemma* efixed_point_is_fixed'
- \+/\- *lemma* dist_le_of_fixed_point
- \- *lemma* fixed_point_is_fixed
- \+/\- *lemma* fixed_point_unique
- \+/\- *theorem* fixed_point_unique'
- \+/\- *theorem* fixed_point_unique'



## [2020-05-29 16:24:04](https://github.com/leanprover-community/mathlib/commit/836184a)
feat(tactic/protect_proj): protect_proj attribute for structures ([#2855](https://github.com/leanprover-community/mathlib/pull/2855))
This attribute protect the projections of a structure that is being defined. 
There were some errors in Euclidean domain caused by `rw` using `euclidean_domain.mul_assoc` instead of `mul_assoc` because the `euclidean_domain` namespace was open. This fixes this problem, and makes the `group` and `ring` etc. namespaces more usable.
#### Estimated changes
modified src/algebra/euclidean_domain.lean

modified src/algebra/field.lean

modified src/algebra/gcd_domain.lean

modified src/algebra/group/basic.lean

modified src/algebra/group_with_zero.lean

modified src/algebra/lie_algebra.lean

modified src/algebra/module.lean

modified src/algebra/ordered_field.lean

modified src/algebra/ordered_group.lean

modified src/algebra/ordered_ring.lean

modified src/algebra/ring.lean

modified src/group_theory/subgroup.lean

modified src/tactic/core.lean

created src/tactic/protected.lean

created test/protec_proj.lean



## [2020-05-29 16:24:02](https://github.com/leanprover-community/mathlib/commit/77674a0)
chore(category_theory): T50000 challenge ([#2840](https://github.com/leanprover-community/mathlib/pull/2840))
A lame effort at making something compile with `-T50000`. No actual speed improvement, just split up a definition into pieces.
#### Estimated changes
modified src/category_theory/limits/over.lean
- \+ *def* cones_equiv_inverse_obj
- \+ *def* cones_equiv_unit_iso
- \+ *def* cones_equiv_counit_iso

modified src/category_theory/limits/shapes/binary_products.lean



## [2020-05-29 16:24:00](https://github.com/leanprover-community/mathlib/commit/07cdafe)
feat(tactic/with_local_reducibility): alter reducibility attributes locally ([#2820](https://github.com/leanprover-community/mathlib/pull/2820))
#### Estimated changes
modified src/tactic/core.lean

created src/tactic/with_local_reducibility.lean
- \+ *def* decl_reducibility.to_attribute

created test/with_local_reducibility.lean
- \+ *def* wlr_irred
- \+ *def* wlr_semired
- \+ *def* wlr_red



## [2020-05-29 14:48:35](https://github.com/leanprover-community/mathlib/commit/4a5799e)
feat(data/equiv/basic): subtype_prod_equiv_prod ([#2717](https://github.com/leanprover-community/mathlib/pull/2717))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* subtype_prod_equiv_prod



## [2020-05-29 06:50:56](https://github.com/leanprover-community/mathlib/commit/b013b2d)
feat(ring_theory): define subsemirings ([#2837](https://github.com/leanprover-community/mathlib/pull/2837))
~~Depends on [#2836](https://github.com/leanprover-community/mathlib/pull/2836),~~ needs a better module docstring.
Some lemmas are missing, most notably `(subsemiring.closure s : set R) = add_submonoid.closure (submonoid.closure s)`.
#### Estimated changes
modified src/group_theory/congruence.lean

modified src/group_theory/monoid_localization.lean

modified src/group_theory/submonoid.lean
- \+ *lemma* coe_supr_of_directed
- \+ *lemma* coe_Sup_of_directed_on
- \+ *lemma* mrestrict_apply
- \+ *lemma* coe_mrange_restrict
- \+ *lemma* mclosure_preimage_le
- \- *lemma* restrict_apply
- \- *lemma* restrict_eq
- \- *lemma* coe_range_restrict
- \- *lemma* closure_preimage_le
- \+ *def* mrestrict
- \+ *def* cod_mrestrict
- \+ *def* mrange_restrict
- \- *def* restrict
- \- *def* cod_restrict
- \- *def* range_restrict

modified src/ring_theory/localization.lean

created src/ring_theory/subsemiring.lean
- \+ *lemma* coe_mk'
- \+ *lemma* mem_mk'
- \+ *lemma* mk'_to_submonoid
- \+ *lemma* mk'_to_add_submonoid
- \+ *lemma* list_prod_mem
- \+ *lemma* list_sum_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* multiset_sum_mem
- \+ *lemma* prod_mem
- \+ *lemma* sum_mem
- \+ *lemma* pow_mem
- \+ *lemma* smul_mem
- \+ *lemma* coe_nat_mem
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* mem_to_submonoid
- \+ *lemma* coe_to_submonoid
- \+ *lemma* mem_to_add_submonoid
- \+ *lemma* coe_to_add_submonoid
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* coe_srange
- \+ *lemma* mem_srange
- \+ *lemma* map_srange
- \+ *lemma* coe_bot
- \+ *lemma* mem_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* Inf_to_submonoid
- \+ *lemma* Inf_to_add_submonoid
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* closure_sUnion
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_mono_right
- \+ *lemma* prod_mono_left
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* coe_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_Sup_of_directed_on
- \+ *lemma* srestrict_apply
- \+ *lemma* coe_srange_restrict
- \+ *lemma* srange_top_iff_surjective
- \+ *lemma* srange_top_of_surjective
- \+ *lemma* eq_on_sclosure
- \+ *lemma* eq_of_eq_on_stop
- \+ *lemma* eq_of_eq_on_sdense
- \+ *lemma* sclosure_preimage_le
- \+ *lemma* map_sclosure
- \+ *lemma* srange_subtype
- \+ *lemma* range_fst
- \+ *lemma* range_snd
- \+ *lemma* prod_bot_sup_bot_prod
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* zero_mem
- \+ *theorem* mul_mem
- \+ *theorem* add_mem
- \+ *theorem* coe_subtype
- \+ *def* subtype
- \+ *def* comap
- \+ *def* map
- \+ *def* srange
- \+ *def* closure
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* srestrict
- \+ *def* cod_srestrict
- \+ *def* srange_restrict
- \+ *def* eq_slocus
- \+ *def* inclusion
- \+ *def* subsemiring_congr



## [2020-05-29 05:57:08](https://github.com/leanprover-community/mathlib/commit/6c046c7)
chore(data/setoid): split into `basic` and `partition` ([#2853](https://github.com/leanprover-community/mathlib/pull/2853))
The `basic` part has slightly fewer dependencies and `partition` part
is never used in `mathlib`.
#### Estimated changes
renamed src/data/setoid.lean to src/data/setoid/basic.lean
- \+ *lemma* ker_def
- \+ *lemma* ker_iff_mem_preimage
- \- *lemma* ker_apply_eq_preimage
- \- *lemma* eq_of_mem_eqv_class
- \- *lemma* mem_classes
- \- *lemma* eq_iff_classes_eq
- \- *lemma* rel_iff_exists_classes
- \- *lemma* classes_inj
- \- *lemma* empty_not_mem_classes
- \- *lemma* classes_eqv_classes
- \- *lemma* eq_of_mem_classes
- \- *lemma* eq_eqv_class_of_mem
- \- *lemma* eqv_class_mem
- \- *lemma* eqv_classes_disjoint
- \- *lemma* eqv_classes_of_disjoint_union
- \- *lemma* nonempty_of_mem_partition
- \- *lemma* exists_of_mem_partition
- \- *theorem* mk_classes_classes
- \- *theorem* classes_mk_classes
- \+ *def* lift_equiv
- \+ *def* correspondence
- \- *def* mk_classes
- \- *def* classes
- \- *def* setoid_of_disjoint_union
- \- *def* is_partition
- \- *def* partition.order_iso

created src/data/setoid/partition.lean
- \+ *lemma* eq_of_mem_eqv_class
- \+ *lemma* mem_classes
- \+ *lemma* eq_iff_classes_eq
- \+ *lemma* rel_iff_exists_classes
- \+ *lemma* classes_inj
- \+ *lemma* empty_not_mem_classes
- \+ *lemma* classes_eqv_classes
- \+ *lemma* eq_of_mem_classes
- \+ *lemma* eq_eqv_class_of_mem
- \+ *lemma* eqv_class_mem
- \+ *lemma* eqv_classes_disjoint
- \+ *lemma* eqv_classes_of_disjoint_union
- \+ *lemma* nonempty_of_mem_partition
- \+ *lemma* exists_of_mem_partition
- \+ *theorem* mk_classes_classes
- \+ *theorem* classes_mk_classes
- \+ *def* mk_classes
- \+ *def* classes
- \+ *def* setoid_of_disjoint_union
- \+ *def* is_partition
- \+ *def* partition.order_iso

modified src/group_theory/congruence.lean

modified src/topology/metric_space/contracting.lean



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
modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_eq_add
- \+ *lemma* vsub_eq_sub

created src/analysis/normed_space/add_torsor.lean
- \+ *lemma* add_torsor.dist_eq_norm
- \+ *def* metric_space_of_normed_group_of_add_torsor

modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_eq_zero
- \+/\- *lemma* norm_eq_zero



## [2020-05-28 13:26:09](https://github.com/leanprover-community/mathlib/commit/e9ba32d)
chore(scripts): update nolints.txt ([#2849](https://github.com/leanprover-community/mathlib/pull/2849))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-28 11:54:54](https://github.com/leanprover-community/mathlib/commit/ca95726)
feat(algebra/free) additive versions, docs. ([#2755](https://github.com/leanprover-community/mathlib/pull/2755))
https://github.com/leanprover-community/mathlib/issues/930
#### Estimated changes
modified src/algebra/free.lean
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* pure_bind
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* traverse_eq
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_of_mul
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* pure_bind
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* traverse_eq
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* free_semigroup_free_magma_mul
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* pure_bind
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* traverse_eq
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_of_mul
- \+/\- *lemma* lift_mul
- \+/\- *lemma* map_of
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* pure_bind
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_pure
- \+/\- *lemma* traverse_pure'
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* traverse_eq
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* free_semigroup_free_magma_mul
- \+ *theorem* mul_eq
- \+/\- *theorem* of_mul_assoc
- \+/\- *theorem* of_mul_assoc
- \+ *def* rec_on'
- \+ *def* free_magma.lift
- \+ *def* free_add_magma.lift
- \+ *def* free_magma.map
- \+ *def* free_add_magma.map
- \+ *def* free_magma.length
- \+ *def* free_add_magma.length
- \+ *def* free_semigroup.lift'
- \+ *def* free_add_semigroup.lift'
- \+ *def* rec_on'
- \- *def* lift
- \- *def* map
- \- *def* repr'
- \- *def* length
- \- *def* lift'
- \- *def* traverse'



## [2020-05-28 08:37:23](https://github.com/leanprover-community/mathlib/commit/cbf4740)
refactor(data/equiv/local_equiv): use dot notation for `eq_on_source` ([#2830](https://github.com/leanprover-community/mathlib/pull/2830))
Also reuse more lemmas from `data/set/function`.
#### Estimated changes
modified src/data/equiv/local_equiv.lean
- \+ *lemma* symm_maps_to
- \+ *lemma* eq_on_source.source_eq
- \+ *lemma* eq_on_source.eq_on
- \+ *lemma* eq_on_source.target_eq
- \+ *lemma* eq_on_source.symm'
- \+ *lemma* eq_on_source.symm_eq_on
- \+ *lemma* eq_on_source.trans'
- \+ *lemma* eq_on_source.restr
- \+ *lemma* eq_on_source.source_inter_preimage_eq
- \- *lemma* eq_on_source_symm
- \- *lemma* source_eq_of_eq_on_source
- \- *lemma* target_eq_of_eq_on_source
- \- *lemma* apply_eq_of_eq_on_source
- \- *lemma* inv_apply_eq_of_eq_on_source
- \- *lemma* eq_on_source_trans
- \- *lemma* eq_on_source_restr
- \- *lemma* eq_on_source_preimage

modified src/data/set/function.lean
- \+ *theorem* eq_on_of_left_inv_on_of_right_inv_on
- \- *theorem* eq_on_of_left_inv_of_right_inv

modified src/geometry/manifold/manifold.lean

modified src/topology/local_homeomorph.lean
- \+ *lemma* eq_on_source.symm'
- \+ *lemma* eq_on_source.source_eq
- \+ *lemma* eq_on_source.target_eq
- \+ *lemma* eq_on_source.eq_on
- \+ *lemma* eq_on_source.symm_eq_on_target
- \+ *lemma* eq_on_source.trans'
- \+ *lemma* eq_on_source.restr
- \- *lemma* eq_on_source_symm
- \- *lemma* source_eq_of_eq_on_source
- \- *lemma* target_eq_of_eq_on_source
- \- *lemma* apply_eq_of_eq_on_source
- \- *lemma* inv_apply_eq_of_eq_on_source
- \- *lemma* eq_on_source_trans
- \- *lemma* eq_on_source_restr

modified src/topology/topological_fiber_bundle.lean



## [2020-05-28 08:37:21](https://github.com/leanprover-community/mathlib/commit/28dc2ed)
fix(tactic/suggest): normalize synonyms uniformly in goal and lemma ([#2829](https://github.com/leanprover-community/mathlib/pull/2829))
This change is intended to make `library_search` and `suggest` a bit more robust in unfolding the types of the goal and lemma in order to determine which lemmas it will try to apply.
Before, there were two ad-hoc systems to map a head symbol to the name(s) that it should match, now there is only one ad-hoc function that does so.  As a consequence, `library_search` should be able to use a lemma with return type `a > b` to close the goal `b < a`, and use `lemma foo : p → false` to close the goal `¬ p`.
(The `>` normalization shouldn't "really" be needed if we all strictly followed the `gt_or_ge` linter but we don't and the failure has already caused confusion.)
[Discussion on Zulip starts here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198746479)
#### Estimated changes
modified src/tactic/suggest.lean

modified test/library_search/basic.lean
- \+ *lemma* lemma_with_gt_in_head
- \+ *lemma* lemma_with_false_in_head



## [2020-05-28 07:50:25](https://github.com/leanprover-community/mathlib/commit/005763e)
feat(linear_algebra/lagrange): Lagrange interpolation ([#2764](https://github.com/leanprover-community/mathlib/pull/2764))
Fixes [#2600](https://github.com/leanprover-community/mathlib/pull/2600).
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* degree_sub_le

created src/linear_algebra/lagrange.lean
- \+ *lemma* interpolate_add
- \+ *lemma* interpolate_zero
- \+ *lemma* interpolate_neg
- \+ *lemma* interpolate_sub
- \+ *lemma* interpolate_smul
- \+ *theorem* basis_empty
- \+ *theorem* eval_basis_self
- \+ *theorem* eval_basis_ne
- \+ *theorem* eval_basis
- \+ *theorem* nat_degree_basis
- \+ *theorem* interpolate_empty
- \+ *theorem* eval_interpolate
- \+ *theorem* degree_interpolate_lt
- \+ *theorem* eq_zero_of_eval_eq_zero
- \+ *theorem* eq_of_eval_eq
- \+ *theorem* eq_interpolate
- \+ *def* basis
- \+ *def* interpolate
- \+ *def* linterpolate
- \+ *def* fun_equiv_degree_lt

modified src/ring_theory/polynomial.lean
- \+/\- *theorem* degree_le_mono
- \+ *theorem* mem_degree_lt
- \+ *theorem* degree_lt_mono
- \+ *theorem* degree_lt_eq_span_X_pow
- \+/\- *theorem* degree_le_mono
- \+ *def* degree_lt



## [2020-05-28 07:50:22](https://github.com/leanprover-community/mathlib/commit/fa371f7)
feat(linear_algebra/bilinear_form): introduce adjoints of linear maps ([#2746](https://github.com/leanprover-community/mathlib/pull/2746))
We also use this to define the Lie algebra structure on skew-adjoint
endomorphisms / matrices. The motivation is to enable us to define the
classical Lie algebras.
#### Estimated changes
modified src/algebra/classical_lie_algebras.lean

modified src/algebra/lie_algebra.lean
- \+ *lemma* is_skew_adjoint_bracket
- \+ *def* lie_subalgebra.incl
- \+ *def* lie_algebra.morphism.range
- \+/\- *def* matrix.lie_ring
- \+/\- *def* matrix.lie_algebra
- \+ *def* lie_equiv_matrix'
- \+ *def* skew_adjoint_lie_subalgebra
- \+ *def* skew_adjoint_matrices_lie_embedding
- \+ *def* skew_adjoint_matrices_lie_subalgebra
- \+/\- *def* matrix.lie_ring
- \+/\- *def* matrix.lie_algebra

modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* neg_apply
- \+ *lemma* to_matrix_to_bilin_form
- \+ *lemma* to_bilin_form_to_matrix
- \+ *lemma* is_adjoint_pair.eq
- \+ *lemma* is_adjoint_pair_iff_comp_left_eq_comp_right
- \+ *lemma* is_adjoint_pair_zero
- \+ *lemma* is_adjoint_pair_id
- \+ *lemma* is_adjoint_pair.add
- \+ *lemma* is_adjoint_pair.sub
- \+ *lemma* is_adjoint_pair.smul
- \+ *lemma* is_adjoint_pair.comp
- \+ *lemma* is_adjoint_pair.mul
- \+ *lemma* is_skew_adjoint_iff_neg_self_adjoint
- \+ *lemma* mem_self_adjoint_submodule
- \+ *lemma* mem_skew_adjoint_submodule
- \+ *lemma* matrix_is_adjoint_pair_bilin_form
- \+ *lemma* pair_self_adjoint_matrices_linear_embedding_apply
- \+ *lemma* pair_self_adjoint_matrices_linear_embedding_injective
- \+ *lemma* mem_pair_self_adjoint_matrices_submodule
- \+ *def* is_adjoint_pair
- \+ *def* is_pair_self_adjoint
- \+ *def* is_pair_self_adjoint_submodule
- \+ *def* is_self_adjoint
- \+ *def* is_skew_adjoint
- \+ *def* self_adjoint_submodule
- \+ *def* skew_adjoint_submodule
- \+ *def* matrix.is_adjoint_pair
- \+ *def* matrix.is_self_adjoint
- \+ *def* matrix.is_skew_adjoint
- \+ *def* pair_self_adjoint_matrices_linear_embedding
- \+ *def* pair_self_adjoint_matrices_submodule
- \+ *def* self_adjoint_matrices_submodule
- \+ *def* skew_adjoint_matrices_submodule

modified src/linear_algebra/matrix.lean
- \+ *lemma* to_lin_neg
- \+ *lemma* comp_to_matrix_mul



## [2020-05-28 07:02:07](https://github.com/leanprover-community/mathlib/commit/315ba3e)
feat(category_theory): show an epi regular mono is an iso ([#2781](https://github.com/leanprover-community/mathlib/pull/2781))
a really minor proof to show that a regular mono which is epi is an iso
#### Estimated changes
modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* is_iso_of_regular_mono_of_epi
- \+ *def* is_iso_of_regular_epi_of_mono



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
modified src/algebra/char_p.lean

modified src/algebra/group_power.lean
- \- *lemma* coe_pow
- \- *lemma* iterate_map_pow
- \- *lemma* iterate_map_smul
- \- *theorem* monoid_hom.iterate_map_pow
- \- *theorem* add_monoid_hom.iterate_map_smul

created src/algebra/iterate_hom.lean
- \+ *lemma* coe_pow
- \+ *theorem* iterate_map_one
- \+ *theorem* iterate_map_mul
- \+ *theorem* iterate_map_inv
- \+ *theorem* iterate_map_pow
- \+ *theorem* iterate_map_gpow
- \+ *theorem* iterate_map_sub
- \+ *theorem* iterate_map_smul
- \+ *theorem* iterate_map_gsmul
- \+ *theorem* iterate_map_one
- \+ *theorem* iterate_map_zero
- \+ *theorem* iterate_map_add
- \+ *theorem* iterate_map_mul
- \+ *theorem* iterate_map_pow
- \+ *theorem* iterate_map_smul
- \+ *theorem* iterate_map_sub
- \+ *theorem* iterate_map_neg
- \+ *theorem* iterate_map_gsmul

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/iterated_deriv.lean
- \+/\- *lemma* iterated_deriv_eq_iterate
- \+/\- *lemma* iterated_deriv_eq_iterate

modified src/analysis/normed_space/banach.lean

modified src/analysis/special_functions/exp_log.lean

modified src/computability/partrec_code.lean

modified src/computability/primrec.lean

modified src/computability/turing_machine.lean

modified src/data/nat/basic.lean
- \- *lemma* iterate_mul
- \- *theorem* iterate_zero
- \- *theorem* iterate_zero_apply
- \- *theorem* iterate_succ
- \- *theorem* iterate_succ_apply
- \- *theorem* iterate_add
- \- *theorem* iterate_add_apply
- \- *theorem* iterate_one
- \- *theorem* iterate_succ'
- \- *theorem* iterate_succ_apply'
- \- *theorem* iterate_ind
- \- *theorem* iterate₀
- \- *theorem* iterate₁
- \- *theorem* iterate₂
- \- *theorem* iterate_cancel
- \- *theorem* injective.iterate
- \- *theorem* surjective.iterate
- \- *theorem* bijective.iterate
- \- *theorem* iterate_map_one
- \- *theorem* iterate_map_mul
- \- *theorem* iterate_map_inv
- \- *theorem* iterate_map_sub
- \- *theorem* iterate_map_one
- \- *theorem* iterate_map_zero
- \- *theorem* iterate_map_mul
- \- *theorem* iterate_map_add
- \- *theorem* iterate_map_neg
- \- *theorem* iterate_map_sub

modified src/field_theory/perfect_closure.lean
- \+ *theorem* left_inverse_pth_root_frobenius

created src/logic/function/iterate.lean
- \+ *lemma* iterate_mul
- \+ *lemma* iterate_right
- \+ *lemma* iterate_left
- \+ *lemma* iterate_right
- \+ *lemma* iterate_left
- \+ *lemma* iterate_iterate
- \+ *lemma* iterate_eq_of_map_eq
- \+ *lemma* semiconj₂.iterate
- \+ *theorem* iterate_zero
- \+ *theorem* iterate_zero_apply
- \+ *theorem* iterate_succ
- \+ *theorem* iterate_succ_apply
- \+ *theorem* iterate_id
- \+ *theorem* iterate_add
- \+ *theorem* iterate_add_apply
- \+ *theorem* iterate_one
- \+ *theorem* iterate_fixed
- \+ *theorem* injective.iterate
- \+ *theorem* surjective.iterate
- \+ *theorem* bijective.iterate
- \+ *theorem* iterate_succ'
- \+ *theorem* iterate_succ_apply'
- \+ *theorem* left_inverse.iterate
- \+ *theorem* right_inverse.iterate

modified src/order/order_iso.lean

modified src/set_theory/ordinal.lean
- \+/\- *theorem* eq_or_principal
- \+/\- *theorem* init_iff
- \+/\- *theorem* trans_apply
- \+/\- *theorem* trans_top
- \+/\- *theorem* cod_restrict_apply
- \+/\- *theorem* cod_restrict_top
- \+/\- *theorem* lift_lift
- \+/\- *theorem* eq_or_principal
- \+/\- *theorem* init_iff
- \+/\- *theorem* trans_apply
- \+/\- *theorem* trans_top
- \+/\- *theorem* cod_restrict_apply
- \+/\- *theorem* cod_restrict_top
- \+/\- *theorem* lift_lift

modified src/topology/metric_space/contracting.lean

modified src/topology/metric_space/lipschitz.lean



## [2020-05-27 18:57:00](https://github.com/leanprover-community/mathlib/commit/1988364)
feat(src/ring_theory): in a PID, all fractional ideals are invertible ([#2826](https://github.com/leanprover-community/mathlib/pull/2826))
This would show that all PIDs are Dedekind domains, once we have a definition of Dedekind domain (we could define it right now, but it would depend on the choice of field of fractions).
In `localization.lean`, I added a few small lemmas on localizations (`localization.exists_integer_multiple` and `fraction_map.to_map_eq_zero_iff`). @101damnations, are these additions compatible with your branches? I'm happy to change them if not.
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* val_coe_ideal
- \+ *lemma* mem_coe
- \+ *lemma* one_mem_one
- \+ *lemma* val_one
- \+ *lemma* val_inv_of_nonzero
- \+ *lemma* span_fractional_iff
- \+ *lemma* span_singleton_fractional
- \+ *lemma* val_span_singleton
- \+ *lemma* eq_span_singleton_of_principal
- \+ *lemma* span_singleton_zero
- \+ *lemma* span_singleton_one
- \+ *lemma* span_singleton_mul_span_singleton
- \+ *lemma* coe_span_singleton
- \+ *lemma* mem_singleton_mul
- \+ *lemma* invertible_of_principal
- \+ *lemma* exists_eq_span_singleton_mul
- \+ *theorem* mul_inv_cancel_iff
- \+ *def* span_singleton

modified src/ring_theory/localization.lean
- \+ *lemma* exists_integer_multiple'
- \+ *lemma* exists_integer_multiple
- \+ *lemma* lin_coe_apply
- \+ *lemma* to_map_eq_zero_iff



## [2020-05-27 13:41:59](https://github.com/leanprover-community/mathlib/commit/c812ebe)
feat(category_theory/abelian): abelian categories ([#2817](https://github.com/leanprover-community/mathlib/pull/2817))
~~Depends on [#2779](https://github.com/leanprover-community/mathlib/pull/2779).~~ Closes [#2178](https://github.com/leanprover-community/mathlib/pull/2178). I will give instances for `AddCommGroup` and `Module`, but since this PR is large already, I'll wait until the next PR with that.
#### Estimated changes
modified docs/references.bib

created src/category_theory/abelian/basic.lean
- \+ *lemma* image_eq_image
- \+ *lemma* full_image_factorisation
- \+ *def* strong_epi_of_epi
- \+ *def* is_iso_of_mono_of_epi
- \+ *def* image_strong_epi_mono_factorisation
- \+ *def* coimage_strong_epi_mono_factorisation
- \+ *def* epi_is_cokernel_of_kernel
- \+ *def* mono_is_kernel_of_cokernel
- \+ *def* has_pullbacks
- \+ *def* has_pushouts
- \+ *def* is_limit_pullback_to_biproduct
- \+ *def* is_colimit_biproduct_to_pushout

modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* biprod.hom_ext
- \+ *lemma* biprod.hom_ext'

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.ι_eq_app_zero
- \+ *lemma* cofork.π_eq_app_one

modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *def* is_iso_of_mono_of_strong_epi
- \- *def* mono_strong_epi_is_iso

modified src/category_theory/preadditive.lean
- \+/\- *lemma* sub_comp
- \+/\- *lemma* comp_sub
- \+/\- *lemma* neg_comp
- \+/\- *lemma* comp_neg
- \+/\- *lemma* neg_comp_neg
- \+/\- *lemma* sub_comp
- \+/\- *lemma* comp_sub
- \+/\- *lemma* neg_comp
- \+/\- *lemma* comp_neg
- \+/\- *lemma* neg_comp_neg



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
created src/algebra/continued_fractions/computation/basic.lean
- \+ *lemma* coe_to_int_fract_pair
- \+ *lemma* stream_is_seq

created src/algebra/continued_fractions/computation/default.lean

created src/algebra/continued_fractions/computation/translations.lean
- \+ *lemma* stream_eq_none_of_fr_eq_zero
- \+ *lemma* succ_nth_stream_eq_none_iff
- \+ *lemma* succ_nth_stream_eq_some_iff
- \+ *lemma* obtain_succ_nth_stream_of_fr_zero
- \+ *lemma* int_fract_pair.seq1_fst_eq_of
- \+ *lemma* of_h_eq_int_fract_pair_seq1_fst_b
- \+ *lemma* of_h_eq_floor
- \+ *lemma* int_fract_pair.nth_seq1_eq_succ_nth_stream
- \+ *lemma* of_terminated_at_iff_int_fract_pair_seq1_terminated_at
- \+ *lemma* of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none
- \+ *lemma* int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some
- \+ *lemma* nth_of_eq_some_of_succ_nth_int_fract_pair_stream
- \+ *lemma* nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero

modified src/algebra/continued_fractions/default.lean



## [2020-05-27 12:11:14](https://github.com/leanprover-community/mathlib/commit/798c61b)
feat(data/nat/prime): eq_prime_pow_of_dvd_least_prime_pow ([#2791](https://github.com/leanprover-community/mathlib/pull/2791))
Proves
```lean
lemma eq_prime_pow_of_dvd_least_prime_pow
  (a p k : ℕ) (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) :
  a = p^(k+1)
```
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* pow_dvd_pow_iff_pow_le_pow
- \+ *lemma* pow_dvd_pow_iff_le_right
- \+ *lemma* pow_dvd_pow_iff_le_right'

modified src/data/nat/prime.lean
- \+ *lemma* eq_prime_pow_of_dvd_least_prime_pow



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
modified .github/workflows/build.yml

modified src/analysis/analytic/basic.lean

modified src/category_theory/limits/over.lean

modified src/category_theory/limits/shapes/binary_products.lean

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/measure_theory/simple_func_dense.lean

modified src/topology/category/Top/adjunctions.lean



## [2020-05-27 11:24:35](https://github.com/leanprover-community/mathlib/commit/7c5eab3)
chore(scripts): update nolints.txt ([#2841](https://github.com/leanprover-community/mathlib/pull/2841))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-27 08:57:27](https://github.com/leanprover-community/mathlib/commit/a7063ec)
feat(ring_theory/prod): ring homs to/from `R × S` ([#2836](https://github.com/leanprover-community/mathlib/pull/2836))
* move some instances from `algebra/pi_instances`;
* add `prod.comm_semiring`;
* define `ring_hom.fst`, `ring_hom.snd`, `ring_hom.prod`, and
  `ring_hom.prod_map`.
#### Estimated changes
modified src/algebra/group/prod.lean
- \+/\- *lemma* coe_prod_map
- \+/\- *lemma* coe_prod_map

modified src/algebra/pi_instances.lean

created src/ring_theory/prod.lean
- \+ *lemma* coe_fst
- \+ *lemma* coe_snd
- \+ *lemma* prod_apply
- \+ *lemma* fst_comp_prod
- \+ *lemma* snd_comp_prod
- \+ *lemma* prod_unique
- \+ *lemma* prod_map_def
- \+ *lemma* coe_prod_map
- \+ *lemma* prod_comp_prod_map
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod_map



## [2020-05-27 08:57:25](https://github.com/leanprover-community/mathlib/commit/6ee3a47)
chore(data/equiv/basic): simplify some defs, add `coe` lemmas ([#2835](https://github.com/leanprover-community/mathlib/pull/2835))
Use functions like `prod.map`, `curry`, `uncurry`, `sum.elim`, `sum.map` to define equivalences.
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* coe_prod_comm
- \+ *lemma* prod_comm_symm
- \+/\- *lemma* sum_congr_symm
- \+ *lemma* sum_comm_apply
- \+/\- *lemma* sum_comm_symm
- \- *lemma* prod_comm_apply
- \+/\- *lemma* sum_congr_symm
- \- *lemma* sum_comm_apply_inl
- \- *lemma* sum_comm_apply_inr
- \+/\- *lemma* sum_comm_symm
- \+ *theorem* coe_refl
- \+/\- *theorem* refl_apply
- \+ *theorem* coe_trans
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+ *theorem* symm_comp_self
- \+ *theorem* self_comp_symm
- \+ *theorem* coe_prod_congr
- \+ *theorem* prod_congr_symm
- \+ *theorem* prod_assoc_sym_apply
- \+/\- *theorem* punit_prod_apply
- \+ *theorem* sum_congr_apply
- \+/\- *theorem* of_bijective_to_fun
- \+/\- *theorem* refl_apply
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \- *theorem* prod_congr_apply
- \+/\- *theorem* punit_prod_apply
- \- *theorem* sum_congr_apply_inl
- \- *theorem* sum_congr_apply_inr
- \+/\- *theorem* of_bijective_to_fun
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \+/\- *def* prod_empty
- \+/\- *def* empty_prod
- \+/\- *def* prod_pempty
- \+/\- *def* pempty_prod
- \+/\- *def* psum_equiv_sum
- \+/\- *def* sum_congr
- \+/\- *def* sum_empty
- \+/\- *def* sum_pempty
- \+/\- *def* sigma_congr_left'
- \+/\- *def* sigma_congr
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \+/\- *def* prod_empty
- \+/\- *def* empty_prod
- \+/\- *def* prod_pempty
- \+/\- *def* pempty_prod
- \+/\- *def* psum_equiv_sum
- \+/\- *def* sum_congr
- \+/\- *def* sum_empty
- \+/\- *def* sum_pempty
- \+/\- *def* sigma_congr_left'
- \+/\- *def* sigma_congr

modified src/data/equiv/functor.lean

modified src/data/polynomial.lean

modified src/data/sum.lean
- \+ *lemma* map_inl
- \+ *lemma* map_inr
- \+ *lemma* map_map
- \+ *lemma* map_comp_map
- \+ *lemma* map_id_id



## [2020-05-27 08:57:23](https://github.com/leanprover-community/mathlib/commit/2a48225)
feat(computability/tm_to_partrec): partrec functions are TM-computable ([#2792](https://github.com/leanprover-community/mathlib/pull/2792))
A construction of a Turing machine that can evaluate any partial recursive function. This PR contains the bulk of the work but the end to end theorem (which asserts that any `computable` function can be evaluated by a Turing machine) has not yet been stated.
#### Estimated changes
created src/computability/tm_to_partrec.lean
- \+ *theorem* nil_eval
- \+ *theorem* id_eval
- \+ *theorem* head_eval
- \+ *theorem* zero_eval
- \+ *theorem* pred_eval
- \+ *theorem* exists_code.comp
- \+ *theorem* exists_code
- \+ *theorem* cont.then_eval
- \+ *theorem* step_normal_then
- \+ *theorem* step_ret_then
- \+ *theorem* code.ok.zero
- \+ *theorem* step_normal.is_ret
- \+ *theorem* cont_eval_fix
- \+ *theorem* code_is_ok
- \+ *theorem* step_normal_eval
- \+ *theorem* step_ret_eval
- \+ *theorem* tr_nat_zero
- \+ *theorem* K'.elim_update_main
- \+ *theorem* K'.elim_update_rev
- \+ *theorem* K'.elim_update_aux
- \+ *theorem* K'.elim_update_stack
- \+ *theorem* split_at_pred_eq
- \+ *theorem* split_at_pred_ff
- \+ *theorem* move_ok
- \+ *theorem* unrev_ok
- \+ *theorem* move₂_ok
- \+ *theorem* clear_ok
- \+ *theorem* copy_ok
- \+ *theorem* tr_pos_num_nat_end
- \+ *theorem* tr_num_nat_end
- \+ *theorem* tr_nat_nat_end
- \+ *theorem* tr_list_ne_Cons
- \+ *theorem* head_main_ok
- \+ *theorem* head_stack_ok
- \+ *theorem* succ_ok
- \+ *theorem* pred_ok
- \+ *theorem* tr_normal_respects
- \+ *theorem* tr_ret_respects
- \+ *theorem* tr_respects
- \+ *theorem* tr_init
- \+ *theorem* tr_eval
- \+ *def* code.eval
- \+ *def* nil
- \+ *def* id
- \+ *def* head
- \+ *def* zero
- \+ *def* pred
- \+ *def* rfind
- \+ *def* prec
- \+ *def* cont.eval
- \+ *def* step_normal
- \+ *def* step_ret
- \+ *def* step
- \+ *def* cont.then
- \+ *def* cfg.then
- \+ *def* code.ok
- \+ *def* stmt'
- \+ *def* cfg'
- \+ *def* nat_end
- \+ *def* pop'
- \+ *def* peek'
- \+ *def* push'
- \+ *def* unrev
- \+ *def* move_excl
- \+ *def* move₂
- \+ *def* head
- \+ *def* tr_normal
- \+ *def* tr
- \+ *def* tr_cont
- \+ *def* tr_pos_num
- \+ *def* tr_num
- \+ *def* tr_nat
- \+ *def* tr_list
- \+ *def* tr_llist
- \+ *def* cont_stack
- \+ *def* tr_cont_stack
- \+ *def* K'.elim
- \+ *def* halt
- \+ *def* tr_cfg
- \+ *def* split_at_pred
- \+ *def* init

modified src/computability/turing_machine.lean
- \+ *def* eval_induction
- \+/\- *def* step_aux
- \+/\- *def* step
- \+/\- *def* step_aux
- \+/\- *def* step

modified src/data/list/basic.lean
- \+ *theorem* tail_suffix
- \+ *theorem* tail_subset

modified src/data/option/defs.lean

modified src/data/pfun.lean
- \+ *theorem* pure_eq_some

modified src/data/vector2.lean
- \+ *theorem* cons_val
- \+ *theorem* cons_head
- \+ *theorem* cons_tail
- \+ *theorem* tail_val

modified src/logic/function/basic.lean
- \+ *theorem* update_comm
- \+ *theorem* update_idem

modified src/logic/relation.lean

modified src/topology/list.lean
- \- *lemma* cons_val



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
modified src/algebra/big_operators.lean

modified src/algebra/category/Group/basic.lean
- \+/\- *def* mul_equiv.to_CommGroup_iso
- \+/\- *def* mul_equiv.to_CommGroup_iso

modified src/algebra/category/Group/colimits.lean
- \+/\- *lemma* quot_neg
- \+/\- *lemma* quot_add
- \+/\- *lemma* quot_neg
- \+/\- *lemma* quot_add

modified src/algebra/category/Mon/basic.lean

modified src/algebra/free.lean
- \+/\- *lemma* map_mul'
- \+/\- *lemma* mul_bind
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* map_mul'
- \+/\- *lemma* mul_bind
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* mul_map_seq
- \+/\- *lemma* map_pure
- \+/\- *lemma* map_mul'
- \+/\- *lemma* mul_bind
- \+/\- *lemma* pure_seq
- \+/\- *lemma* mul_seq
- \+/\- *lemma* traverse_mul
- \+/\- *lemma* traverse_mul'
- \+/\- *lemma* mul_map_seq
- \+/\- *theorem* of_mul_assoc_left
- \+/\- *theorem* of_mul_assoc_left
- \+/\- *def* traverse'
- \+/\- *def* free_semigroup_free_magma
- \+/\- *def* traverse'
- \+/\- *def* free_semigroup_free_magma

modified src/algebra/group/units.lean

modified src/algebra/group/units_hom.lean
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_comp

modified src/category_theory/category/default.lean
- \+/\- *lemma* eq_of_comp_left_eq'
- \+/\- *lemma* eq_of_comp_right_eq'
- \+/\- *lemma* mono_of_mono_fac
- \+/\- *lemma* epi_of_epi_fac
- \+/\- *lemma* eq_of_comp_left_eq'
- \+/\- *lemma* eq_of_comp_right_eq'
- \+/\- *lemma* mono_of_mono_fac
- \+/\- *lemma* epi_of_epi_fac

modified src/control/monad/cont.lean
- \+/\- *def* option_t.call_cc
- \+/\- *def* writer_t.call_cc
- \+/\- *def* state_t.call_cc
- \+/\- *def* reader_t.call_cc
- \+/\- *def* option_t.call_cc
- \+/\- *def* writer_t.call_cc
- \+/\- *def* state_t.call_cc
- \+/\- *def* reader_t.call_cc

modified src/control/monad/writer.lean

modified src/control/traversable/basic.lean

modified src/data/analysis/filter.lean
- \+/\- *theorem* map_F
- \+/\- *theorem* map_F

modified src/data/equiv/basic.lean
- \+/\- *lemma* swap_apply_self
- \+/\- *lemma* swap_apply_self
- \+/\- *def* Pi_curry
- \+/\- *def* Pi_curry

modified src/data/fin.lean
- \+/\- *lemma* succ_above_descend
- \+/\- *lemma* succ_above_descend

modified src/data/finset.lean
- \+/\- *theorem* image_union
- \+/\- *theorem* image_inter
- \+/\- *theorem* image_union
- \+/\- *theorem* image_inter

modified src/data/hash_map.lean
- \+/\- *theorem* find_aux_iff
- \+/\- *theorem* contains_aux_iff
- \+/\- *theorem* valid.as_list_nodup
- \+/\- *theorem* valid.find_aux_iff
- \+/\- *theorem* valid.contains_aux_iff
- \+/\- *theorem* find_aux_iff
- \+/\- *theorem* contains_aux_iff
- \+/\- *theorem* valid.as_list_nodup
- \+/\- *theorem* valid.find_aux_iff
- \+/\- *theorem* valid.contains_aux_iff
- \+/\- *def* mk_hash_map
- \+/\- *def* mk_hash_map

modified src/data/int/basic.lean
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_sub_nat_nat
- \+/\- *theorem* cast_neg_of_nat
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_sub_nat_nat
- \+/\- *theorem* cast_neg_of_nat

modified src/data/list/basic.lean
- \+/\- *lemma* head_mul_tail_prod'
- \+/\- *lemma* filter_true
- \+/\- *lemma* filter_false
- \+/\- *lemma* head_mul_tail_prod'
- \+/\- *lemma* filter_true
- \+/\- *lemma* filter_false
- \+/\- *theorem* mem_bind
- \+/\- *theorem* exists_of_mem_bind
- \+/\- *theorem* mem_bind_of_mem
- \+/\- *theorem* append_inj
- \+/\- *theorem* append_inj_right
- \+/\- *theorem* append_inj_left
- \+/\- *theorem* append_inj'
- \+/\- *theorem* append_inj_right'
- \+/\- *theorem* append_inj_left'
- \+/\- *theorem* eq_of_mem_map_const
- \+/\- *theorem* head_append
- \+/\- *theorem* sublist_or_mem_of_sublist
- \+/\- *theorem* eq_of_sublist_of_length_le
- \+/\- *theorem* index_of_cons
- \+/\- *theorem* ext_le
- \+/\- *theorem* index_of_nth_le
- \+/\- *theorem* index_of_nth
- \+/\- *theorem* nth_le_reverse_aux1
- \+/\- *theorem* foldl_reverse
- \+/\- *theorem* foldr_reverse
- \+ *theorem* foldl1_eq_foldr1
- \+ *theorem* foldl_eq_of_comm_of_assoc
- \+ *theorem* foldl_eq_foldr
- \+ *theorem* foldl_eq_of_comm'
- \+ *theorem* foldl_eq_foldr'
- \+ *theorem* foldr_eq_of_comm'
- \+/\- *theorem* length_bind
- \+/\- *theorem* all_cons
- \+/\- *theorem* any_cons
- \+/\- *theorem* le_count_iff_repeat_sublist
- \+/\- *theorem* eq_of_infix_of_length_eq
- \+/\- *theorem* eq_of_prefix_of_length_eq
- \+/\- *theorem* eq_of_suffix_of_length_eq
- \+/\- *theorem* suffix_iff_eq_append
- \+/\- *theorem* erasep_cons
- \+/\- *theorem* erasep_cons_of_neg
- \+/\- *theorem* erasep_append_right
- \+/\- *theorem* erase_cons
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* length_erase_of_mem
- \+/\- *theorem* count_erase_self
- \+/\- *theorem* count_erase_of_ne
- \+/\- *theorem* disjoint_of_subset_left
- \+/\- *theorem* disjoint_of_subset_right
- \+/\- *theorem* disjoint_of_disjoint_append_left_left
- \+/\- *theorem* disjoint_of_disjoint_append_left_right
- \+/\- *theorem* disjoint_of_disjoint_append_right_left
- \+/\- *theorem* disjoint_of_disjoint_append_right_right
- \+/\- *theorem* mem_bind
- \+/\- *theorem* exists_of_mem_bind
- \+/\- *theorem* mem_bind_of_mem
- \+/\- *theorem* append_inj
- \+/\- *theorem* append_inj_right
- \+/\- *theorem* append_inj_left
- \+/\- *theorem* append_inj'
- \+/\- *theorem* append_inj_right'
- \+/\- *theorem* append_inj_left'
- \+/\- *theorem* eq_of_mem_map_const
- \+/\- *theorem* head_append
- \+/\- *theorem* sublist_or_mem_of_sublist
- \+/\- *theorem* eq_of_sublist_of_length_le
- \+/\- *theorem* index_of_cons
- \+/\- *theorem* ext_le
- \+/\- *theorem* index_of_nth_le
- \+/\- *theorem* index_of_nth
- \+/\- *theorem* nth_le_reverse_aux1
- \+/\- *theorem* foldl_reverse
- \+/\- *theorem* foldr_reverse
- \+/\- *theorem* length_bind
- \+/\- *theorem* all_cons
- \+/\- *theorem* any_cons
- \+/\- *theorem* le_count_iff_repeat_sublist
- \+/\- *theorem* eq_of_infix_of_length_eq
- \+/\- *theorem* eq_of_prefix_of_length_eq
- \+/\- *theorem* eq_of_suffix_of_length_eq
- \+/\- *theorem* suffix_iff_eq_append
- \+/\- *theorem* erasep_cons
- \+/\- *theorem* erasep_cons_of_neg
- \+/\- *theorem* erasep_append_right
- \+/\- *theorem* erase_cons
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* length_erase_of_mem
- \+/\- *theorem* count_erase_self
- \+/\- *theorem* count_erase_of_ne
- \+/\- *theorem* disjoint_of_subset_left
- \+/\- *theorem* disjoint_of_subset_right
- \+/\- *theorem* disjoint_of_disjoint_append_left_left
- \+/\- *theorem* disjoint_of_disjoint_append_left_right
- \+/\- *theorem* disjoint_of_disjoint_append_right_left
- \+/\- *theorem* disjoint_of_disjoint_append_right_right

modified src/data/list/tfae.lean

modified src/data/num/lemmas.lean
- \+ *theorem* cast_one
- \+ *theorem* cast_one'
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_to_nat
- \+ *theorem* to_nat_to_int
- \+ *theorem* cast_to_int
- \+ *theorem* succ_to_nat
- \+ *theorem* one_add
- \+ *theorem* add_one
- \+ *theorem* add_to_nat
- \+ *theorem* add_succ
- \+ *theorem* bit0_of_bit0
- \+ *theorem* bit1_of_bit1
- \+ *theorem* mul_to_nat
- \+ *theorem* to_nat_pos
- \+ *theorem* cmp_to_nat_lemma
- \+ *theorem* cmp_swap
- \+ *theorem* cmp_to_nat
- \+ *theorem* lt_to_nat
- \+ *theorem* le_to_nat
- \+ *theorem* add_zero
- \+ *theorem* zero_add
- \+ *theorem* add_one
- \+ *theorem* add_succ
- \+ *theorem* add_of_nat
- \+ *theorem* bit0_of_bit0
- \+ *theorem* bit1_of_bit1
- \+ *theorem* cast_zero
- \+ *theorem* cast_zero'
- \+ *theorem* cast_one
- \+ *theorem* cast_pos
- \+ *theorem* succ'_to_nat
- \+ *theorem* succ_to_nat
- \+ *theorem* cast_to_nat
- \+ *theorem* to_nat_to_int
- \+ *theorem* cast_to_int
- \+ *theorem* to_of_nat
- \+ *theorem* of_nat_cast
- \+ *theorem* of_nat_inj
- \+ *theorem* add_to_nat
- \+ *theorem* mul_to_nat
- \+ *theorem* cmp_to_nat
- \+ *theorem* lt_to_nat
- \+ *theorem* le_to_nat
- \+ *theorem* of_to_nat
- \+ *theorem* of_to_nat
- \+ *theorem* to_nat_inj
- \+ *theorem* dvd_to_nat
- \+ *theorem* to_nat_inj
- \+ *theorem* pred'_to_nat
- \+ *theorem* pred'_succ'
- \+ *theorem* succ'_pred'
- \+ *theorem* size_to_nat
- \+ *theorem* size_eq_nat_size
- \+ *theorem* nat_size_to_nat
- \+ *theorem* nat_size_pos
- \+ *theorem* cast_to_num
- \+ *theorem* bit_to_nat
- \+ *theorem* cast_add
- \+ *theorem* cast_succ
- \+ *theorem* cast_inj
- \+ *theorem* one_le_cast
- \+ *theorem* cast_pos
- \+ *theorem* cast_mul
- \+ *theorem* cmp_eq
- \+ *theorem* cast_lt
- \+ *theorem* cast_le
- \+ *theorem* bit_to_nat
- \+ *theorem* cast_succ'
- \+ *theorem* cast_succ
- \+ *theorem* cast_add
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_mul
- \+ *theorem* size_to_nat
- \+ *theorem* size_eq_nat_size
- \+ *theorem* nat_size_to_nat
- \+ *theorem* of_nat'_eq
- \+ *theorem* zneg_to_znum
- \+ *theorem* zneg_to_znum_neg
- \+ *theorem* to_znum_inj
- \+ *theorem* cast_to_znum
- \+ *theorem* cast_to_znum_neg
- \+ *theorem* add_to_znum
- \+ *theorem* pred_to_nat
- \+ *theorem* sub'_one
- \+ *theorem* one_sub'
- \+ *theorem* lt_iff_cmp
- \+ *theorem* le_iff_cmp
- \+ *theorem* pred_to_nat
- \+ *theorem* ppred_to_nat
- \+ *theorem* cmp_swap
- \+ *theorem* cmp_eq
- \+ *theorem* cast_lt
- \+ *theorem* cast_le
- \+ *theorem* cast_inj
- \+ *theorem* lt_iff_cmp
- \+ *theorem* le_iff_cmp
- \+ *theorem* bitwise_to_nat
- \+ *theorem* lor_to_nat
- \+ *theorem* land_to_nat
- \+ *theorem* ldiff_to_nat
- \+ *theorem* lxor_to_nat
- \+ *theorem* shiftl_to_nat
- \+ *theorem* shiftr_to_nat
- \+ *theorem* test_bit_to_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_zero'
- \+ *theorem* cast_one
- \+ *theorem* cast_pos
- \+ *theorem* cast_neg
- \+ *theorem* cast_zneg
- \+ *theorem* neg_zero
- \+ *theorem* zneg_pos
- \+ *theorem* zneg_neg
- \+ *theorem* zneg_zneg
- \+ *theorem* zneg_bit1
- \+ *theorem* zneg_bitm1
- \+ *theorem* zneg_succ
- \+ *theorem* zneg_pred
- \+ *theorem* neg_of_int
- \+ *theorem* abs_to_nat
- \+ *theorem* abs_to_znum
- \+ *theorem* cast_to_int
- \+ *theorem* bit0_of_bit0
- \+ *theorem* bit1_of_bit1
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_bitm1
- \+ *theorem* add_zero
- \+ *theorem* zero_add
- \+ *theorem* add_one
- \+ *theorem* cast_to_znum
- \+ *theorem* cast_sub'
- \+ *theorem* to_nat_eq_succ_pred
- \+ *theorem* to_int_eq_succ_pred
- \+ *theorem* cast_sub'
- \+ *theorem* of_nat_to_znum
- \+ *theorem* of_nat_to_znum_neg
- \+ *theorem* mem_of_znum'
- \+ *theorem* of_znum'_to_nat
- \+ *theorem* of_znum_to_nat
- \+ *theorem* cast_of_znum
- \+ *theorem* sub_to_nat
- \+ *theorem* cast_add
- \+ *theorem* cast_succ
- \+ *theorem* mul_to_int
- \+ *theorem* cast_mul
- \+ *theorem* of_to_int
- \+ *theorem* to_of_int
- \+ *theorem* to_int_inj
- \+ *theorem* of_int_cast
- \+ *theorem* of_nat_cast
- \+ *theorem* of_int'_eq
- \+ *theorem* cmp_to_int
- \+ *theorem* lt_to_int
- \+ *theorem* le_to_int
- \+ *theorem* cast_lt
- \+ *theorem* cast_le
- \+ *theorem* cast_inj
- \+ *theorem* dvd_to_int
- \+ *theorem* divmod_to_nat_aux
- \+ *theorem* divmod_to_nat
- \+ *theorem* div'_to_nat
- \+ *theorem* mod'_to_nat
- \+ *theorem* div_to_nat
- \+ *theorem* mod_to_nat
- \+ *theorem* gcd_to_nat_aux
- \+ *theorem* gcd_to_nat
- \+ *theorem* dvd_iff_mod_eq_zero
- \+ *theorem* div_to_int
- \+ *theorem* mod_to_int
- \+ *theorem* gcd_to_nat
- \+ *theorem* dvd_iff_mod_eq_zero
- \+ *def* of_snum

modified src/data/zsqrtd/basic.lean
- \+ *lemma* nonneg_add_lem
- \+ *theorem* ext
- \+ *theorem* of_int_re
- \+ *theorem* of_int_im
- \+ *theorem* zero_re
- \+ *theorem* zero_im
- \+ *theorem* one_re
- \+ *theorem* one_im
- \+ *theorem* sqrtd_re
- \+ *theorem* sqrtd_im
- \+ *theorem* add_def
- \+ *theorem* add_re
- \+ *theorem* add_im
- \+ *theorem* bit0_re
- \+ *theorem* bit0_im
- \+ *theorem* bit1_re
- \+ *theorem* bit1_im
- \+ *theorem* neg_re
- \+ *theorem* neg_im
- \+ *theorem* conj_re
- \+ *theorem* conj_im
- \+ *theorem* mul_re
- \+ *theorem* mul_im
- \+ *theorem* coe_nat_re
- \+ *theorem* coe_nat_im
- \+ *theorem* coe_nat_val
- \+ *theorem* coe_int_re
- \+ *theorem* coe_int_im
- \+ *theorem* coe_int_val
- \+ *theorem* of_int_eq_coe
- \+ *theorem* smul_val
- \+ *theorem* muld_val
- \+ *theorem* smuld_val
- \+ *theorem* decompose
- \+ *theorem* mul_conj
- \+ *theorem* conj_mul
- \+ *theorem* sq_le_of_le
- \+ *theorem* sq_le_add_mixed
- \+ *theorem* sq_le_add
- \+ *theorem* sq_le_cancel
- \+ *theorem* sq_le_smul
- \+ *theorem* sq_le_mul
- \+ *theorem* nonnegg_comm
- \+ *theorem* nonnegg_neg_pos
- \+ *theorem* nonnegg_pos_neg
- \+ *theorem* nonnegg_cases_right
- \+ *theorem* nonnegg_cases_left
- \+ *theorem* nonneg_cases
- \+ *theorem* nonneg_add
- \+ *theorem* le_refl
- \+ *theorem* nonneg_iff_zero_le
- \+ *theorem* le_of_le_le
- \+ *theorem* le_arch
- \+ *theorem* nonneg_smul
- \+ *theorem* nonneg_muld
- \+ *theorem* nonneg_mul_lem
- \+ *theorem* nonneg_mul
- \+ *theorem* not_sq_le_succ
- \+ *theorem* d_pos
- \+ *theorem* divides_sq_eq_zero
- \+ *theorem* divides_sq_eq_zero_z
- \+ *theorem* not_divides_square
- \+ *theorem* nonneg_antisymm
- \+ *theorem* le_antisymm
- \+ *def* of_int
- \+ *def* zero
- \+ *def* one
- \+ *def* sqrtd
- \+ *def* add
- \+ *def* neg
- \+ *def* conj
- \+ *def* mul
- \+ *def* sq_le
- \+ *def* nonnegg
- \+ *def* nonneg

modified src/group_theory/congruence.lean
- \+ *def* correspondence

modified src/group_theory/monoid_localization.lean

modified src/group_theory/submonoid.lean
- \+/\- *lemma* mem_closure_singleton
- \+/\- *lemma* mem_closure_singleton

modified src/number_theory/dioph.lean
- \+ *lemma* inject_dummies_lem
- \+/\- *theorem* append_insert
- \+/\- *theorem* vector_allp_iff_forall
- \+/\- *theorem* list_all_cons
- \+/\- *theorem* list_all.imp
- \+/\- *theorem* list_all_map
- \+/\- *theorem* list_all_congr
- \+ *theorem* ext
- \+ *theorem* of_no_dummies
- \+ *theorem* inject_dummies
- \+ *theorem* reindex_dioph
- \+ *theorem* dioph_list_all
- \+ *theorem* and_dioph
- \+ *theorem* or_dioph
- \+ *theorem* reindex_dioph_fn
- \+ *theorem* ex_dioph
- \+ *theorem* ex1_dioph
- \+ *theorem* dom_dioph
- \+ *theorem* dioph_fn_iff_pfun
- \+ *theorem* abs_poly_dioph
- \+ *theorem* proj_dioph
- \+ *theorem* dioph_pfun_comp1
- \+ *theorem* dioph_fn_comp1
- \+ *theorem* dioph_fn_vec_comp1
- \+ *theorem* vec_ex1_dioph
- \+ *theorem* dioph_fn_vec
- \+ *theorem* dioph_pfun_vec
- \+ *theorem* dioph_fn_compn
- \+ *theorem* dioph_comp
- \+ *theorem* dioph_fn_comp
- \+ *theorem* proj_dioph_of_nat
- \+ *theorem* const_dioph
- \+ *theorem* dioph_comp2
- \+ *theorem* dioph_fn_comp2
- \+ *theorem* eq_dioph
- \+ *theorem* add_dioph
- \+ *theorem* mul_dioph
- \+ *theorem* le_dioph
- \+ *theorem* lt_dioph
- \+ *theorem* ne_dioph
- \+ *theorem* sub_dioph
- \+ *theorem* dvd_dioph
- \+ *theorem* mod_dioph
- \+ *theorem* modeq_dioph
- \+ *theorem* div_dioph
- \+ *theorem* pell_dioph
- \+ *theorem* xn_dioph
- \+ *theorem* pow_dioph
- \+/\- *theorem* append_insert
- \+/\- *theorem* vector_allp_iff_forall
- \+/\- *theorem* list_all_cons
- \+/\- *theorem* list_all.imp
- \+/\- *theorem* list_all_map
- \+/\- *theorem* list_all_congr
- \+ *def* dioph_pfun
- \+ *def* dioph_fn

modified src/set_theory/ordinal.lean

modified src/tactic/apply.lean

modified src/tactic/lean_core_docs.lean

modified src/tactic/lint/type_classes.lean

modified src/tactic/omega/main.lean

modified test/coinductive.lean

modified test/localized/import3.lean

modified test/norm_num.lean

modified test/tidy.lean

modified test/where.lean



## [2020-05-27 01:18:54](https://github.com/leanprover-community/mathlib/commit/2792c93)
feat(ring_theory/fintype): in a finite nonzero_semiring, fintype.card (units R) < fintype.card R ([#2793](https://github.com/leanprover-community/mathlib/pull/2793))
#### Estimated changes
modified src/algebra/associated.lean
- \+/\- *theorem* not_is_unit_zero
- \+/\- *theorem* not_is_unit_zero

modified src/algebra/gcd_domain.lean

modified src/algebra/group/units.lean
- \+/\- *def* is_unit
- \+/\- *def* is_unit

modified src/algebra/group/units_hom.lean

modified src/algebra/group_with_zero.lean

modified src/algebra/ring.lean

modified src/analysis/asymptotics.lean

modified src/data/fintype/basic.lean
- \+ *lemma* mem_image_univ_iff_mem_range
- \+ *lemma* card_lt_card_of_injective_of_not_mem

modified src/group_theory/group_action.lean

modified src/group_theory/monoid_localization.lean

created src/ring_theory/fintype.lean
- \+ *lemma* card_units_lt

modified src/ring_theory/ideals.lean

modified src/ring_theory/power_series.lean



## [2020-05-26 17:35:27](https://github.com/leanprover-community/mathlib/commit/63b8c52)
chore(scripts): update nolints.txt ([#2833](https://github.com/leanprover-community/mathlib/pull/2833))
I am happy to remove some nolints for you!
#### Estimated changes



## [2020-05-26 16:47:21](https://github.com/leanprover-community/mathlib/commit/4dfd706)
chore(scripts): update nolints.txt ([#2831](https://github.com/leanprover-community/mathlib/pull/2831))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-26 16:47:19](https://github.com/leanprover-community/mathlib/commit/4ca776e)
feat(linear_algebra/quadratic_form): equivalence of quadratic forms ([#2769](https://github.com/leanprover-community/mathlib/pull/2769))
#### Estimated changes
modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* map_app
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *def* equivalent
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans



## [2020-05-26 15:15:29](https://github.com/leanprover-community/mathlib/commit/9630eca)
feat(data/nat/primes): lemmas about min_fac ([#2790](https://github.com/leanprover-community/mathlib/pull/2790))
#### Estimated changes
modified src/data/nat/prime.lean



## [2020-05-26 13:30:46](https://github.com/leanprover-community/mathlib/commit/895f568)
perf(tactic/lint): speed up nolint attribute ([#2828](https://github.com/leanprover-community/mathlib/pull/2828))
Looking up the nolint attribute only takes 15 seconds out of the 45 minutes, so speeding up this part has little effect.  More importantly, this PR removes one branch from the mathlib repository.
#### Estimated changes
modified src/tactic/lint/basic.lean



## [2020-05-26 13:30:44](https://github.com/leanprover-community/mathlib/commit/1cf59fc)
chore(src/algebra/ordered_ring.lean): fix linting errors ([#2827](https://github.com/leanprover-community/mathlib/pull/2827))
[Mentioned, but not really discussed, in this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20get.20familiar.20enough.20with.20Mathlib.20to.20use.20it/near/198747067).
This PR also removes `mul_pos'` and `mul_nonneg'` lemmas because they are now identical to the improved `mul_pos` and `mul_nonneg`.
#### Estimated changes
modified src/algebra/ordered_ring.lean
- \+/\- *lemma* mul_nonneg
- \+/\- *lemma* mul_pos
- \+/\- *lemma* two_gt_one
- \+/\- *lemma* two_ge_one
- \+/\- *lemma* four_pos
- \+/\- *lemma* mul_self_nonneg
- \+/\- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+/\- *lemma* gt_of_mul_lt_mul_neg_left
- \+/\- *lemma* mul_def
- \+/\- *lemma* mul_nonneg
- \- *lemma* mul_nonneg'
- \+/\- *lemma* mul_pos
- \- *lemma* mul_pos'
- \+/\- *lemma* two_gt_one
- \+/\- *lemma* two_ge_one
- \+/\- *lemma* four_pos
- \+/\- *lemma* mul_self_nonneg
- \+/\- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+/\- *lemma* gt_of_mul_lt_mul_neg_left
- \+/\- *lemma* mul_def
- \+/\- *theorem* top_ne_zero
- \+/\- *theorem* zero_ne_top
- \+/\- *theorem* coe_eq_zero
- \+/\- *theorem* zero_eq_coe
- \+/\- *theorem* coe_zero
- \+/\- *theorem* top_ne_zero
- \+/\- *theorem* zero_ne_top
- \+/\- *theorem* coe_eq_zero
- \+/\- *theorem* zero_eq_coe
- \+/\- *theorem* coe_zero

modified src/analysis/analytic/basic.lean

modified src/analysis/analytic/composition.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/data/rat/order.lean

modified src/geometry/manifold/real_instances.lean



## [2020-05-26 13:30:42](https://github.com/leanprover-community/mathlib/commit/7d86475)
feat(data/polynomial): eq_one_of_is_unit_of_monic ([#2823](https://github.com/leanprover-community/mathlib/pull/2823))
~~Depends on [#2822](https://github.com/leanprover-community/mathlib/pull/2822) ~~
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* degree_nonneg_iff_ne_zero
- \+ *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \+ *lemma* eq_one_of_is_unit_of_monic



## [2020-05-26 13:30:40](https://github.com/leanprover-community/mathlib/commit/099ffd3)
chore(algebra/free_monoid): use implicit args in `lift` ([#2821](https://github.com/leanprover-community/mathlib/pull/2821))
#### Estimated changes
modified src/algebra/free_monoid.lean
- \+ *lemma* lift_symm_apply
- \+/\- *lemma* lift_apply
- \+/\- *lemma* lift_comp_of
- \+/\- *lemma* lift_eval_of
- \+/\- *lemma* lift_restrict
- \+/\- *lemma* comp_lift
- \+ *lemma* hom_map_lift
- \+/\- *lemma* lift_apply
- \+/\- *lemma* lift_comp_of
- \+/\- *lemma* lift_eval_of
- \+/\- *lemma* lift_restrict
- \+/\- *lemma* comp_lift

modified src/algebra/group/hom.lean
- \+ *lemma* coe_mk'

modified src/group_theory/submonoid.lean
- \+/\- *lemma* closure_eq_mrange
- \+/\- *lemma* closure_eq_mrange



## [2020-05-26 13:30:38](https://github.com/leanprover-community/mathlib/commit/fc79089)
feat(number_theory/primorial): Bound on the primorial function ([#2701](https://github.com/leanprover-community/mathlib/pull/2701))
This lemma is needed for Erdös's proof of Bertrand's postulate, but it may be of independent interest.
#### Estimated changes
modified src/data/finset.lean
- \+ *theorem* self_mem_range_succ

modified src/data/list/range.lean
- \+ *theorem* self_mem_range_succ

modified src/data/multiset.lean
- \+ *theorem* self_mem_range_succ

modified src/data/nat/basic.lean
- \+ *lemma* choose_symm_half

modified src/data/nat/choose.lean
- \+/\- *lemma* choose_le_middle
- \+ *lemma* choose_middle_le_pow
- \+/\- *lemma* choose_le_middle

created src/number_theory/primorial.lean
- \+ *lemma* primorial_succ
- \+ *lemma* dvd_choose_of_middling_prime
- \+ *lemma* prod_primes_dvd
- \+ *lemma* primorial_le_4_pow
- \+ *def* primorial



## [2020-05-26 11:43:31](https://github.com/leanprover-community/mathlib/commit/2c40bd3)
feat(tactic/push_cast): take list of extra simp lemmas ([#2825](https://github.com/leanprover-community/mathlib/pull/2825))
closes [#2783](https://github.com/leanprover-community/mathlib/pull/2783)
#### Estimated changes
modified src/tactic/norm_cast.lean

modified test/norm_cast.lean



## [2020-05-26 10:40:07](https://github.com/leanprover-community/mathlib/commit/ab2e52e)
feat(order/filter/basic): a local left inverse locally equals a local right inverse ([#2808](https://github.com/leanprover-community/mathlib/pull/2808))
#### Estimated changes
modified src/analysis/calculus/inverse.lean
- \+ *lemma* local_inverse_tendsto
- \+ *lemma* local_inverse_unique

modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq_of_left_inv_of_right_inv



## [2020-05-26 10:40:05](https://github.com/leanprover-community/mathlib/commit/8c36b32)
feat(order/filter/basic): add `eventually.curry` ([#2807](https://github.com/leanprover-community/mathlib/pull/2807))
I'm not sure that this is a good name. Suggestions of better names are welcome.
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eventually_prod_iff
- \+ *lemma* eventually.curry

modified src/topology/constructions.lean
- \+ *lemma* filter.eventually.curry_nhds



## [2020-05-26 10:40:03](https://github.com/leanprover-community/mathlib/commit/597946d)
feat(analysis/calculus/implicit): Implicit function theorem ([#2749](https://github.com/leanprover-community/mathlib/pull/2749))
Fixes [#1849](https://github.com/leanprover-community/mathlib/pull/1849)
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/2749.20Implicit.20function.20theorem).
#### Estimated changes
modified src/analysis/calculus/deriv.lean
- \- *lemma* has_strict_fderiv_at.has_strict_deriv_at

created src/analysis/calculus/implicit.lean
- \+ *lemma* prod_fun_apply
- \+ *lemma* to_local_homeomorph_coe
- \+ *lemma* to_local_homeomorph_apply
- \+ *lemma* pt_mem_to_local_homeomorph_source
- \+ *lemma* map_pt_mem_to_local_homeomorph_target
- \+ *lemma* prod_map_implicit_function
- \+ *lemma* left_map_implicit_function
- \+ *lemma* right_map_implicit_function
- \+ *lemma* implicit_function_apply_image
- \+ *lemma* implicit_function_has_strict_fderiv_at
- \+ *lemma* implicit_to_local_homeomorph_of_complemented_fst
- \+ *lemma* implicit_to_local_homeomorph_of_complemented_apply
- \+ *lemma* implicit_to_local_homeomorph_of_complemented_apply_ker
- \+ *lemma* implicit_to_local_homeomorph_of_complemented_self
- \+ *lemma* mem_implicit_to_local_homeomorph_of_complemented_source
- \+ *lemma* mem_implicit_to_local_homeomorph_of_complemented_target
- \+ *lemma* map_implicit_function_of_complemented_eq
- \+ *lemma* eq_implicit_function_of_complemented
- \+ *lemma* to_implicit_function_of_complemented
- \+ *lemma* implicit_to_local_homeomorph_fst
- \+ *lemma* implicit_to_local_homeomorph_apply_ker
- \+ *lemma* implicit_to_local_homeomorph_self
- \+ *lemma* mem_implicit_to_local_homeomorph_source
- \+ *lemma* mem_implicit_to_local_homeomorph_target
- \+ *lemma* map_implicit_function_eq
- \+ *lemma* eq_implicit_function
- \+ *lemma* to_implicit_function
- \+ *def* prod_fun
- \+ *def* to_local_homeomorph
- \+ *def* implicit_function
- \+ *def* implicit_function_data_of_complemented
- \+ *def* implicit_to_local_homeomorph_of_complemented
- \+ *def* implicit_function_of_complemented
- \+ *def* implicit_to_local_homeomorph
- \+ *def* implicit_function

modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_comp

modified src/topology/algebra/module.lean
- \+ *lemma* is_complete_ker



## [2020-05-26 09:33:44](https://github.com/leanprover-community/mathlib/commit/b4d4d9a)
feat(ring_theory/algebra): more on restrict_scalars ([#2445](https://github.com/leanprover-community/mathlib/pull/2445))
#### Estimated changes
modified src/analysis/normed_space/basic.lean

modified src/data/complex/module.lean

modified src/ring_theory/algebra.lean
- \+ *lemma* module.restrict_scalars_smul_def
- \+ *lemma* algebra.restrict_scalars_equiv_apply
- \+ *lemma* algebra.restrict_scalars_equiv_symm_apply
- \+ *lemma* submodule.restrict_scalars_mem
- \+ *lemma* submodule.restrict_scalars_bot
- \+ *lemma* submodule.restrict_scalars_top
- \+ *lemma* restrict_scalars_ker
- \+ *lemma* linear_map_algebra_module.smul_apply
- \+ *def* module.restrict_scalars'
- \+/\- *def* module.restrict_scalars
- \+ *def* algebra.restrict_scalars_equiv
- \+ *def* submodule.restrict_scalars
- \+/\- *def* linear_map.restrict_scalars
- \+/\- *def* module.restrict_scalars
- \+/\- *def* linear_map.restrict_scalars



## [2020-05-26 08:11:51](https://github.com/leanprover-community/mathlib/commit/ea403b3)
feat(algebra/group_with_zero): mul_self_mul_inv ([#2795](https://github.com/leanprover-community/mathlib/pull/2795))
I found this lemma was useful for simplifying some expressions without
needing to split into cases or provide a proof that the denominator is
nonzero, and it doesn't show up with library_search.
#### Estimated changes
modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_self_mul_inv
- \+ *lemma* mul_inv_mul_self
- \+ *lemma* inv_mul_mul_self
- \+ *lemma* mul_self_div_self
- \+ *lemma* div_self_mul_self
- \+ *lemma* div_div_self



## [2020-05-26 06:41:18](https://github.com/leanprover-community/mathlib/commit/1c265e2)
feat(data/nat/basic): with_bot lemmas ([#2822](https://github.com/leanprover-community/mathlib/pull/2822))
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* with_bot.coe_nonneg
- \+ *lemma* with_bot.lt_zero_iff



## [2020-05-26 05:06:40](https://github.com/leanprover-community/mathlib/commit/9bb9956)
feat(data/nat/basic): inequalities ([#2801](https://github.com/leanprover-community/mathlib/pull/2801))
Adds some simple inequalities about `nat.pow`.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* lt_two_pow
- \+ *lemma* one_le_pow
- \+ *lemma* one_le_pow'
- \+ *lemma* one_le_two_pow
- \+ *lemma* one_lt_pow
- \+ *lemma* one_lt_pow'
- \+ *lemma* one_lt_two_pow
- \+ *lemma* one_lt_two_pow'



## [2020-05-26 00:59:03](https://github.com/leanprover-community/mathlib/commit/4b616e6)
feat(category_theory/limits): transport lemmas for kernels ([#2779](https://github.com/leanprover-community/mathlib/pull/2779))
#### Estimated changes
modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* is_kernel.of_comp_iso
- \+ *def* kernel.of_comp_iso
- \+ *def* is_kernel.iso_kernel
- \+ *def* kernel.iso_kernel
- \+ *def* is_cokernel.of_iso_comp
- \+ *def* cokernel.of_iso_comp
- \+ *def* is_cokernel.cokernel_iso
- \+ *def* cokernel.cokernel_iso



## [2020-05-25 20:20:32](https://github.com/leanprover-community/mathlib/commit/aad2dfc)
fix(group_with_zero): fix definition of comm_monoid_with_zero ([#2818](https://github.com/leanprover-community/mathlib/pull/2818))
Also generate instance comm_group_with_zero -> comm_monoid_with_zero.
#### Estimated changes
modified src/algebra/group_with_zero.lean



## [2020-05-25 15:03:03](https://github.com/leanprover-community/mathlib/commit/ae5b55b)
feat(algebra/ring): ring_hom.map_dvd ([#2813](https://github.com/leanprover-community/mathlib/pull/2813))
#### Estimated changes
modified src/algebra/ring.lean
- \+ *lemma* ring_hom.map_dvd



## [2020-05-25 12:50:28](https://github.com/leanprover-community/mathlib/commit/52b839f)
feat(data/polynomial): is_unit_C ([#2812](https://github.com/leanprover-community/mathlib/pull/2812))
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* is_unit_C



## [2020-05-25 12:50:26](https://github.com/leanprover-community/mathlib/commit/3e0668e)
feat(linear_algebra/projection): add `equiv_prod_of_surjective_of_is_compl` ([#2787](https://github.com/leanprover-community/mathlib/pull/2787))
If kernels of two surjective linear maps `f`, `g` are complement subspaces,
then `x ↦ (f x, g x)` defines a  linear equivalence.
I also add a version of this equivalence for continuous maps.
Depends on [#2785](https://github.com/leanprover-community/mathlib/pull/2785)
#### Estimated changes
modified src/analysis/normed_space/complemented.lean
- \+ *lemma* coe_equiv_prod_of_surjective_of_is_compl
- \+ *lemma* equiv_prod_of_surjective_of_is_compl_to_linear_equiv
- \+ *lemma* equiv_prod_of_surjective_of_is_compl_apply
- \+ *def* equiv_prod_of_surjective_of_is_compl

modified src/linear_algebra/basis.lean

modified src/linear_algebra/projection.lean
- \+/\- *lemma* ker_id_sub_eq_of_proj
- \+ *lemma* range_eq_of_proj
- \+/\- *lemma* is_compl_of_proj
- \+ *lemma* coe_equiv_prod_of_surjective_of_is_compl
- \+ *lemma* equiv_prod_of_surjective_of_is_compl_apply
- \+/\- *lemma* ker_id_sub_eq_of_proj
- \+/\- *lemma* is_compl_of_proj
- \+ *def* equiv_prod_of_surjective_of_is_compl

modified src/topology/algebra/module.lean



## [2020-05-25 12:07:49](https://github.com/leanprover-community/mathlib/commit/60f0b01)
feat(logic/function): define `semiconj` and `commute` ([#2788](https://github.com/leanprover-community/mathlib/pull/2788))
#### Estimated changes
created src/logic/function/conjugate.lean
- \+ *lemma* comp_right
- \+ *lemma* comp_left
- \+ *lemma* id_right
- \+ *lemma* id_left
- \+ *lemma* inverses_right
- \+ *lemma* semiconj.commute
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* comp_right
- \+ *lemma* comp_left
- \+ *lemma* id_right
- \+ *lemma* id_left
- \+ *lemma* id_left
- \+ *lemma* comp
- \+ *def* semiconj
- \+ *def* commute
- \+ *def* semiconj₂



## [2020-05-25 10:18:13](https://github.com/leanprover-community/mathlib/commit/96f318c)
feat(algebra/group_power): int.nat_abs_pow_two ([#2811](https://github.com/leanprover-community/mathlib/pull/2811))
#### Estimated changes
modified src/algebra/group_power.lean
- \+ *lemma* nat_abs_pow_two

modified src/number_theory/sum_four_squares.lean



## [2020-05-25 10:18:11](https://github.com/leanprover-community/mathlib/commit/9da47ad)
feat(data/zmod): lemmas about coercions to zmod ([#2802](https://github.com/leanprover-community/mathlib/pull/2802))
I'm not particularly happy with the location of these new lemmas within the file `data.zmod`. If anyone has a suggestion that they should be some particular place higher or lower in the file, that would be welcome.
#### Estimated changes
modified src/algebra/char_p.lean
- \+ *lemma* char_p.int_coe_eq_int_coe_iff

modified src/data/zmod/basic.lean
- \+ *lemma* int_coe_eq_int_coe_iff
- \+ *lemma* nat_coe_eq_nat_coe_iff
- \+ *lemma* int_coe_zmod_eq_zero_iff_dvd
- \+ *lemma* nat_coe_zmod_eq_zero_iff_dvd
- \+ *lemma* cast_mod_int



## [2020-05-25 08:49:00](https://github.com/leanprover-community/mathlib/commit/dd062f0)
feat(data/nat/prime): pow_not_prime ([#2810](https://github.com/leanprover-community/mathlib/pull/2810))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* prime.pow_not_prime



## [2020-05-25 07:24:08](https://github.com/leanprover-community/mathlib/commit/a2d5007)
chore(topology/algebra/module): prove `fst.prod snd = id` ([#2806](https://github.com/leanprover-community/mathlib/pull/2806))
#### Estimated changes
modified src/topology/algebra/module.lean
- \+ *lemma* fst_prod_snd



## [2020-05-25 07:24:07](https://github.com/leanprover-community/mathlib/commit/ccf646d)
chore(set_theory/ordinal): use a `protected lemma` to drop a `nolint` ([#2805](https://github.com/leanprover-community/mathlib/pull/2805))
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *lemma* div_def
- \- *def* div_def



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
modified src/tactic/norm_num.lean
- \+ *theorem* int_sub_hack

modified test/norm_num.lean



## [2020-05-25 06:35:44](https://github.com/leanprover-community/mathlib/commit/6552f21)
feat(algebra/add_torsor): torsors of additive group actions ([#2720](https://github.com/leanprover-community/mathlib/pull/2720))
Define torsors of additive group actions, to the extent needed for
(and with notation motivated by) affine spaces, to the extent needed
for Euclidean spaces.  See
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations
for the discussion leading to this particular structure.
#### Estimated changes
created src/algebra/add_torsor.lean
- \+ *lemma* zero_vadd
- \+ *lemma* vadd_assoc
- \+ *lemma* vadd_comm
- \+ *lemma* vadd_left_cancel
- \+ *lemma* vsub_vadd
- \+ *lemma* vadd_vsub
- \+ *lemma* vadd_right_cancel
- \+ *lemma* vadd_vsub_assoc
- \+ *lemma* vsub_self
- \+ *lemma* eq_of_vsub_eq_zero
- \+ *lemma* vsub_eq_zero_iff_eq
- \+ *lemma* neg_vsub_eq_vsub_rev
- \+ *lemma* vsub_add_vsub_cancel
- \+ *lemma* vsub_vadd_eq_vsub_sub
- \+ *lemma* vsub_sub_vsub_right_cancel
- \+ *lemma* vsub_sub_vsub_left_cancel
- \+ *def* vsub_set



## [2020-05-25 05:05:19](https://github.com/leanprover-community/mathlib/commit/518d0fd)
feat(data/int/basic): eq_zero_of_dvd_of_nonneg_of_lt ([#2803](https://github.com/leanprover-community/mathlib/pull/2803))
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* nat_abs_lt_nat_abs_of_nonneg_of_lt
- \+ *lemma* eq_zero_of_dvd_of_nonneg_of_lt



## [2020-05-24 19:02:14](https://github.com/leanprover-community/mathlib/commit/8d352b2)
feat(char_p): generalize zmod.neg_one_ne_one ([#2796](https://github.com/leanprover-community/mathlib/pull/2796))
#### Estimated changes
modified src/algebra/char_p.lean
- \+ *lemma* char_p.neg_one_ne_one

modified src/data/zmod/basic.lean



## [2020-05-24 17:52:18](https://github.com/leanprover-community/mathlib/commit/61b57cd)
chore(scripts): update nolints.txt ([#2799](https://github.com/leanprover-community/mathlib/pull/2799))
I am happy to remove some nolints for you!
#### Estimated changes



## [2020-05-24 17:03:59](https://github.com/leanprover-community/mathlib/commit/1445e08)
chore(scripts): update nolints.txt ([#2798](https://github.com/leanprover-community/mathlib/pull/2798))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-24 16:14:04](https://github.com/leanprover-community/mathlib/commit/8590081)
feat(category_theory): Product comparison ([#2753](https://github.com/leanprover-community/mathlib/pull/2753))
Construct the product comparison morphism, and show it's an iso iff F preserves binary products.
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod_comparison_natural
- \+ *def* prod_comparison

created src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \+ *def* alternative_cone
- \+ *def* alternative_cone_is_limit
- \+ *def* preserves_binary_prod_of_prod_comparison_iso



## [2020-05-24 15:07:07](https://github.com/leanprover-community/mathlib/commit/292fc04)
feat(category_theory): adjunction convenience defs ([#2754](https://github.com/leanprover-community/mathlib/pull/2754))
Transport adjunctions along natural isomorphisms, and `is_left_adjoint` or `is_right_adjoint` versions of existing adjunction properties.
#### Estimated changes
modified src/category_theory/adjunction/basic.lean
- \+ *lemma* equiv_homset_left_of_nat_iso_apply
- \+ *lemma* equiv_homset_left_of_nat_iso_symm_apply
- \+ *lemma* equiv_homset_right_of_nat_iso_apply
- \+ *lemma* equiv_homset_right_of_nat_iso_symm_apply
- \+ *def* equiv_homset_left_of_nat_iso
- \+ *def* equiv_homset_right_of_nat_iso
- \+ *def* of_nat_iso_left
- \+ *def* of_nat_iso_right
- \+ *def* right_adjoint_of_nat_iso
- \+ *def* left_adjoint_of_nat_iso



## [2020-05-24 09:09:11](https://github.com/leanprover-community/mathlib/commit/2ef444a)
feat(linear_algebra/basic): range of `linear_map.prod` ([#2785](https://github.com/leanprover-community/mathlib/pull/2785))
Also make `ker_prod` a `simp` lemma.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+/\- *lemma* ker_prod
- \+ *lemma* range_prod_le
- \+ *lemma* range_prod_eq
- \+/\- *lemma* ker_prod

modified src/topology/algebra/module.lean
- \+ *lemma* ker_prod
- \+ *lemma* range_prod_le
- \+ *lemma* range_prod_eq
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply



## [2020-05-24 07:37:41](https://github.com/leanprover-community/mathlib/commit/5449203)
chore(order/basic): change "minimum" in descriptions to "minimal" ([#2789](https://github.com/leanprover-community/mathlib/pull/2789))
#### Estimated changes
modified src/order/basic.lean



## [2020-05-23 13:13:15](https://github.com/leanprover-community/mathlib/commit/79e296b)
doc(archive/100-theorems-list): Update README.md ([#2750](https://github.com/leanprover-community/mathlib/pull/2750))
Making the 100.yaml file more discoverable.
#### Estimated changes
modified archive/100-theorems-list/README.md



## [2020-05-23 12:26:58](https://github.com/leanprover-community/mathlib/commit/2a3f59a)
chore(scripts): update nolints.txt ([#2782](https://github.com/leanprover-community/mathlib/pull/2782))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-23 11:01:14](https://github.com/leanprover-community/mathlib/commit/2b79f1d)
feat(ring_theory/ideal_operations): lemmas about ideals and galois connections ([#2767](https://github.com/leanprover-community/mathlib/pull/2767))
depends on [#2766](https://github.com/leanprover-community/mathlib/pull/2766)
#### Estimated changes
modified src/order/complete_lattice.lean
- \+ *lemma* monotone.le_map_Sup
- \+ *lemma* monotone.map_Inf_le
- \+/\- *theorem* Sup_eq_supr
- \+/\- *theorem* Inf_eq_infi
- \+/\- *theorem* Inf_eq_infi
- \+/\- *theorem* Sup_eq_supr

modified src/order/galois_connection.lean
- \+ *lemma* l_unique
- \+ *lemma* u_unique

modified src/ring_theory/ideal_operations.lean
- \+ *lemma* mul_le_left
- \+ *lemma* mul_le_right
- \+ *lemma* sup_mul_right_self
- \+ *lemma* sup_mul_left_self
- \+ *lemma* mul_right_self_sup
- \+ *lemma* mul_left_self_sup
- \+ *lemma* gc_map_comap
- \+ *lemma* comap_id
- \+ *lemma* map_id
- \+ *lemma* comap_comap
- \+ *lemma* map_map
- \+ *lemma* map_le_of_le_comap
- \+ *lemma* le_comap_of_map_le
- \+ *lemma* le_comap_map
- \+ *lemma* map_comap_le
- \+ *lemma* comap_top
- \+ *lemma* map_bot
- \+ *lemma* map_comap_map
- \+ *lemma* comap_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_infi
- \+ *lemma* map_Sup
- \+ *lemma* comap_Inf
- \+ *lemma* map_surjective_of_surjective
- \+ *lemma* comap_injective_of_surjective
- \+ *lemma* map_sup_comap_of_surjective
- \+ *lemma* map_supr_comap_of_surjective
- \+ *lemma* map_inf_comap_of_surjective
- \+ *lemma* map_infi_comap_of_surjective
- \+ *lemma* map_eq_bot_iff_le_ker
- \+/\- *theorem* annihilator_supr
- \+/\- *theorem* infi_colon_supr
- \+/\- *theorem* annihilator_supr
- \+/\- *theorem* infi_colon_supr
- \- *theorem* map_bot
- \- *theorem* comap_top
- \- *theorem* map_sup
- \+ *def* gi_map_comap



## [2020-05-23 09:33:06](https://github.com/leanprover-community/mathlib/commit/ceb13ba)
chore(order/basic): add `monotone.order_dual`, `strict_mono.order_dual` ([#2778](https://github.com/leanprover-community/mathlib/pull/2778))
Also split long lines and lint.
#### Estimated changes
modified scripts/nolints.txt

modified src/order/basic.lean
- \+/\- *lemma* le_of_forall_le_of_dense
- \+/\- *lemma* le_of_forall_ge_of_dense
- \+/\- *lemma* le_of_forall_le_of_dense
- \+/\- *lemma* le_of_forall_ge_of_dense
- \+ *theorem* monotone.order_dual
- \+ *theorem* strict_mono.order_dual
- \+/\- *theorem* is_strict_total_order'.swap
- \+/\- *theorem* is_strict_total_order'.swap
- \+/\- *def* decidable_linear_order_of_STO'
- \+/\- *def* decidable_linear_order_of_STO'



## [2020-05-23 09:33:05](https://github.com/leanprover-community/mathlib/commit/90abd3b)
feat(data/fintype): finset.univ_map_embedding ([#2765](https://github.com/leanprover-community/mathlib/pull/2765))
Adds the lemma
```
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  (finset.univ).map e = finset.univ :=
```
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* univ_map_equiv_to_embedding
- \+ *lemma* equiv_of_fintype_self_embedding_to_embedding
- \+ *lemma* finset.univ_map_embedding



## [2020-05-23 09:33:02](https://github.com/leanprover-community/mathlib/commit/6948505)
feat(data/polynomial): prime_of_degree_eq_one_of_monic ([#2745](https://github.com/leanprover-community/mathlib/pull/2745))
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* prime_of_degree_eq_one_of_monic
- \+ *lemma* irreducible_of_degree_eq_one_of_monic
- \+ *lemma* degree_normalize
- \+ *lemma* prime_of_degree_eq_one
- \+/\- *lemma* irreducible_of_degree_eq_one
- \+/\- *lemma* irreducible_of_degree_eq_one



## [2020-05-23 07:44:20](https://github.com/leanprover-community/mathlib/commit/8c1793f)
chore(data/equiv): make `equiv.ext` args use { } ([#2776](https://github.com/leanprover-community/mathlib/pull/2776))
Other changes:
* rename lemmas `eq_of_to_fun_eq` to `coe_fn_injective`;
* add `left_inverse.eq_right_inverse` and use it to prove `equiv.ext`.
#### Estimated changes
modified src/data/equiv/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* perm.ext
- \+/\- *lemma* ext
- \+/\- *lemma* perm.ext
- \+ *theorem* coe_fn_injective
- \+/\- *theorem* symm_trans
- \+/\- *theorem* trans_symm
- \- *theorem* eq_of_to_fun_eq
- \+/\- *theorem* symm_trans
- \+/\- *theorem* trans_symm

modified src/data/equiv/local_equiv.lean

modified src/data/equiv/mul_add.lean

modified src/data/equiv/ring.lean

modified src/data/fintype/basic.lean

modified src/group_theory/group_action.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

modified src/linear_algebra/determinant.lean

modified src/logic/function/basic.lean
- \+ *theorem* left_inverse.eq_right_inverse

modified src/order/order_iso.lean
- \+ *theorem* coe_fn_injective
- \+ *theorem* coe_fn_injective
- \- *theorem* eq_of_to_fun_eq
- \- *theorem* eq_of_to_fun_eq

modified src/set_theory/ordinal.lean

modified src/topology/local_homeomorph.lean

modified src/topology/metric_space/isometry.lean



## [2020-05-22 09:41:03](https://github.com/leanprover-community/mathlib/commit/f66caaa)
chore(scripts): update nolints.txt ([#2777](https://github.com/leanprover-community/mathlib/pull/2777))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-22 08:09:58](https://github.com/leanprover-community/mathlib/commit/c6aab26)
feat(algebra/invertible): invertible_of_ring_char_not_dvd ([#2775](https://github.com/leanprover-community/mathlib/pull/2775))
```
def invertible_of_ring_char_not_dvd {R : Type*} [field R] {t : ℕ} (not_dvd : ¬(ring_char R ∣ t)) :
  invertible (t : R)
```
#### Estimated changes
modified src/algebra/invertible.lean
- \+ *def* invertible_of_ring_char_not_dvd
- \+ *def* invertible_of_char_p_not_dvd



## [2020-05-22 08:09:56](https://github.com/leanprover-community/mathlib/commit/58789f7)
feat(analysis/normed_space/banach): add `continuous_linear_equiv.of_bijective` ([#2774](https://github.com/leanprover-community/mathlib/pull/2774))
#### Estimated changes
modified src/analysis/normed_space/banach.lean
- \+ *lemma* coe_fn_of_bijective
- \+ *lemma* of_bijective_symm_apply_apply
- \+ *lemma* of_bijective_apply_symm_apply



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
modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* ext
- \+/\- *lemma* fractional_of_subset_one
- \+/\- *lemma* mem_zero_iff
- \+/\- *lemma* val_zero
- \+/\- *lemma* nonzero_iff_val_nonzero
- \+/\- *lemma* mem_one_iff
- \+/\- *lemma* coe_mem_one
- \+/\- *lemma* le_iff
- \+/\- *lemma* zero_le
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* eq_zero_iff
- \+/\- *lemma* fractional_sup
- \+/\- *lemma* fractional_inf
- \+/\- *lemma* sup_eq_add
- \+/\- *lemma* val_add
- \+/\- *lemma* fractional_mul
- \+/\- *lemma* val_mul
- \+/\- *lemma* mul_left_mono
- \+/\- *lemma* mul_right_mono
- \+/\- *lemma* fractional_div_of_nonzero
- \+/\- *lemma* div_nonzero
- \+/\- *lemma* inv_nonzero
- \+/\- *lemma* div_one
- \+/\- *lemma* ne_zero_of_mul_eq_one
- \+/\- *lemma* ext
- \+/\- *lemma* fractional_of_subset_one
- \+/\- *lemma* mem_zero_iff
- \+/\- *lemma* val_zero
- \+/\- *lemma* nonzero_iff_val_nonzero
- \+/\- *lemma* mem_one_iff
- \+/\- *lemma* coe_mem_one
- \+/\- *lemma* le_iff
- \+/\- *lemma* zero_le
- \+/\- *lemma* bot_eq_zero
- \+/\- *lemma* eq_zero_iff
- \+/\- *lemma* fractional_sup
- \+/\- *lemma* fractional_inf
- \+/\- *lemma* sup_eq_add
- \+/\- *lemma* val_add
- \+/\- *lemma* fractional_mul
- \+/\- *lemma* val_mul
- \+/\- *lemma* mul_left_mono
- \+/\- *lemma* mul_right_mono
- \+/\- *lemma* fractional_div_of_nonzero
- \+/\- *lemma* div_nonzero
- \+/\- *lemma* inv_nonzero
- \+/\- *lemma* div_one
- \+/\- *lemma* ne_zero_of_mul_eq_one
- \+/\- *theorem* right_inverse_eq
- \+/\- *theorem* right_inverse_eq
- \+/\- *def* is_fractional
- \+/\- *def* fractional_ideal
- \+/\- *def* is_fractional
- \+/\- *def* fractional_ideal

modified src/ring_theory/localization.lean
- \+ *lemma* map_units
- \+ *lemma* surj
- \+ *lemma* eq_iff_exists
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* to_map_injective
- \+/\- *lemma* is_integer_add
- \+/\- *lemma* is_integer_mul
- \+/\- *lemma* is_integer_smul
- \+ *lemma* sec_spec
- \+ *lemma* sec_spec'
- \+ *lemma* map_right_cancel
- \+ *lemma* map_left_cancel
- \+ *lemma* eq_zero_of_fst_eq_zero
- \+ *lemma* mk'_sec
- \+ *lemma* mk'_mul
- \+ *lemma* mk'_one
- \+ *lemma* mk'_spec
- \+ *lemma* mk'_spec'
- \+ *lemma* mk'_eq_iff_eq
- \+ *lemma* eq_iff_eq
- \+ *lemma* mk'_eq_iff_mk'_eq
- \+ *lemma* mk'_eq_of_eq
- \+ *lemma* mk'_self
- \+ *lemma* mk'_self'
- \+ *lemma* mk'_self''
- \+ *lemma* mul_mk'_eq_mk'_of_mul
- \+ *lemma* mk'_eq_mul_mk'_one
- \+ *lemma* mk'_mul_cancel_left
- \+ *lemma* mk'_mul_cancel_right
- \+ *lemma* is_unit_comp
- \+ *lemma* eq_of_eq
- \+ *lemma* mk'_add
- \+ *lemma* lift_mk'
- \+ *lemma* lift_mk'_spec
- \+ *lemma* lift_eq
- \+ *lemma* lift_eq_iff
- \+ *lemma* lift_comp
- \+ *lemma* lift_of_comp
- \+ *lemma* epic_of_localization_map
- \+ *lemma* lift_unique
- \+ *lemma* lift_id
- \+ *lemma* lift_left_inverse
- \+ *lemma* lift_surjective_iff
- \+ *lemma* lift_injective_iff
- \+ *lemma* map_eq
- \+ *lemma* map_comp
- \+ *lemma* map_mk'
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp_map
- \+/\- *lemma* map_map
- \+ *lemma* ring_equiv_of_ring_equiv_eq_map_apply
- \+ *lemma* ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* ring_equiv_of_ring_equiv_eq
- \+ *lemma* ring_equiv_of_ring_equiv_mk'
- \+/\- *lemma* of_id
- \+ *lemma* mem_coe
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+/\- *lemma* mem_non_zero_divisors_iff_ne_zero
- \- *lemma* to_units_coe
- \- *lemma* of_zero
- \- *lemma* of_one
- \- *lemma* of_add
- \- *lemma* of_sub
- \- *lemma* of_mul
- \- *lemma* of_neg
- \- *lemma* of_pow
- \- *lemma* of_is_unit'
- \- *lemma* of_is_unit
- \- *lemma* coe_zero
- \- *lemma* coe_one
- \- *lemma* coe_add
- \- *lemma* coe_sub
- \- *lemma* coe_mul
- \- *lemma* coe_neg
- \- *lemma* coe_pow
- \- *lemma* coe_is_unit'
- \- *lemma* coe_is_unit
- \- *lemma* mk_self
- \- *lemma* mk_self'
- \- *lemma* mk_self''
- \- *lemma* coe_mul_mk
- \- *lemma* mk_eq_mul_mk_one
- \- *lemma* mk_mul_mk
- \- *lemma* mk_mul_cancel_left
- \- *lemma* mk_mul_cancel_right
- \- *lemma* mk_eq
- \- *lemma* lift'_mk
- \- *lemma* lift'_of
- \- *lemma* lift'_coe
- \- *lemma* lift_of
- \- *lemma* lift_coe
- \- *lemma* lift'_comp_of
- \- *lemma* lift_comp_of
- \- *lemma* lift'_apply_coe
- \- *lemma* lift_apply_coe
- \- *lemma* map_of
- \- *lemma* map_coe
- \- *lemma* map_comp_of
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp_map
- \+/\- *lemma* map_map
- \- *lemma* away.lift_of
- \- *lemma* away.lift_coe
- \- *lemma* away.lift_comp_of
- \- *lemma* non_zero_divisors_one_val
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+/\- *lemma* mem_non_zero_divisors_iff_ne_zero
- \- *lemma* mk_inv
- \- *lemma* mk_inv'
- \- *lemma* mk_eq_div
- \- *lemma* mk_eq_div'
- \- *lemma* eq_zero_of
- \- *lemma* of.injective
- \- *lemma* map_of
- \- *lemma* map_coe
- \- *lemma* map_comp_of
- \- *lemma* of_smul
- \- *lemma* coe_smul
- \- *lemma* coe_mul_eq_smul
- \- *lemma* mul_coe_eq_smul
- \- *lemma* lin_coe_apply
- \+/\- *lemma* of_id
- \- *lemma* is_integer_coe
- \+/\- *lemma* is_integer_add
- \+/\- *lemma* is_integer_mul
- \+/\- *lemma* is_integer_smul
- \+ *theorem* eq_mk'_iff_mul_eq
- \+ *theorem* mk'_eq_iff_eq_mul
- \- *theorem* symm
- \- *theorem* r_of_eq
- \- *theorem* refl
- \- *theorem* trans
- \- *theorem* map_comap
- \+ *def* to_localization
- \+/\- *def* is_integer
- \+ *def* codomain
- \+/\- *def* lin_coe
- \+/\- *def* non_zero_divisors
- \+ *def* fraction_map
- \+ *def* to_integral_domain
- \- *def* r
- \- *def* localization
- \- *def* mk
- \- *def* of
- \- *def* to_units
- \- *def* lift'
- \- *def* map
- \- *def* equiv_of_equiv
- \- *def* away
- \- *def* away.inv_self
- \- *def* at_prime
- \+/\- *def* non_zero_divisors
- \- *def* fraction_ring
- \- *def* inv_aux
- \- *def* map
- \- *def* equiv_of_equiv
- \- *def* le_order_embedding
- \+/\- *def* lin_coe
- \+/\- *def* is_integer



## [2020-05-22 06:26:36](https://github.com/leanprover-community/mathlib/commit/a012d76)
chore(linear_algebra/projection): use implicit args in lemmas ([#2773](https://github.com/leanprover-community/mathlib/pull/2773))
#### Estimated changes
modified src/analysis/normed_space/complemented.lean

modified src/linear_algebra/projection.lean
- \+ *lemma* linear_proj_of_is_compl_comp_subtype



## [2020-05-22 06:26:34](https://github.com/leanprover-community/mathlib/commit/749e39f)
feat(category_theory): preadditive binary biproducts ([#2747](https://github.com/leanprover-community/mathlib/pull/2747))
This PR introduces "preadditive binary biproducts", which correspond to the second definition of biproducts given in [#2177](https://github.com/leanprover-community/mathlib/pull/2177).
* Preadditive binary biproducts are binary biproducts.
* In a preadditive category, a binary product is a preadditive binary biproduct.
* This directly implies that `AddCommGroup` has preadditive binary biproducts. The existence of binary coproducts in `AddCommGroup` is then a consequence of abstract nonsense.
#### Estimated changes
modified src/algebra/category/Group/biproducts.lean

modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* biprod.inl_fst
- \+ *lemma* biprod.inr_snd
- \+ *lemma* biprod.inr_fst
- \+ *lemma* biprod.inl_snd
- \+ *lemma* biprod.total
- \+ *lemma* biprod.inl_add_inr
- \+ *lemma* biprod.fst_add_snd
- \+ *lemma* biprod.lift_desc
- \+ *def* has_preadditive_binary_biproduct.of_has_limit_pair
- \+ *def* has_preadditive_binary_biproduct.of_has_colimit_pair
- \+ *def* has_preadditive_binary_biproducts_of_has_binary_products
- \+ *def* has_preadditive_binary_biproducts_of_has_binary_coproducts



## [2020-05-22 05:08:46](https://github.com/leanprover-community/mathlib/commit/5585e3c)
chore(linear_algebra/basic): redefine le on submodule ([#2766](https://github.com/leanprover-community/mathlib/pull/2766))
Previously, to prove an `S \le T`, there would be a coercion in the statement after `intro x`. This fixes that.
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/projection.lean

modified src/ring_theory/adjoin.lean

modified src/ring_theory/euclidean_domain.lean

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/polynomial.lean



## [2020-05-21 22:53:42](https://github.com/leanprover-community/mathlib/commit/a9960ce)
chore(scripts): update nolints.txt ([#2771](https://github.com/leanprover-community/mathlib/pull/2771))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-21 20:35:43](https://github.com/leanprover-community/mathlib/commit/6c71874)
feat(analysis/normed_space): complemented subspaces ([#2738](https://github.com/leanprover-community/mathlib/pull/2738))
Define complemented subspaces and prove some basic facts.
#### Estimated changes
created src/analysis/normed_space/complemented.lean
- \+ *lemma* ker_closed_complemented_of_finite_dimensional_range
- \+ *lemma* coe_prod_equiv_of_closed_compl
- \+ *lemma* coe_prod_equiv_of_closed_compl_symm
- \+ *lemma* coe_continuous_linear_proj_of_closed_compl
- \+ *lemma* coe_continuous_linear_proj_of_closed_compl'
- \+ *lemma* closed_complemented_of_closed_compl
- \+ *lemma* closed_complemented_iff_has_closed_compl
- \+ *lemma* closed_complemented_of_quotient_finite_dimensional
- \+ *def* prod_equiv_of_closed_compl
- \+ *def* linear_proj_of_closed_compl

modified src/linear_algebra/projection.lean
- \+ *lemma* ker_id_sub_eq_of_proj

modified src/topology/algebra/module.lean
- \+ *lemma* ker_cod_restrict
- \+ *lemma* closed_complemented.has_closed_complement
- \+ *lemma* closed_complemented_bot
- \+ *lemma* closed_complemented_top
- \+ *lemma* continuous_linear_map.closed_complemented_ker_of_right_inverse
- \+ *def* closed_complemented



## [2020-05-21 20:35:41](https://github.com/leanprover-community/mathlib/commit/fd45e28)
fix(*): do not nolint simp_nf ([#2734](https://github.com/leanprover-community/mathlib/pull/2734))
The `nolint simp_nf` for `subgroup.coe_coe` was hiding an actual nontermination issue.  Please just ping me if you're unsure about the `simp_nf` linter.
#### Estimated changes
modified src/algebra/field.lean
- \- *lemma* inv_zero
- \- *lemma* div_zero

modified src/algebra/group_with_zero.lean
- \+ *lemma* inv_zero
- \+ *lemma* div_zero
- \- *lemma* inv_zero'
- \- *lemma* div_zero'

modified src/group_theory/bundled_subgroup.lean



## [2020-05-21 18:58:04](https://github.com/leanprover-community/mathlib/commit/ec01a0d)
perf(tactic/lint/simp): speed up `simp_comm` linter ([#2760](https://github.com/leanprover-community/mathlib/pull/2760))
This is a fairly unimportant linter, but takes 35% of the linting runtime in my unscientific small-case profiling run.
#### Estimated changes
modified src/algebra/euclidean_domain.lean
- \+/\- *theorem* xgcd_aux_rec
- \+/\- *theorem* xgcd_aux_rec

modified src/data/int/gcd.lean
- \+/\- *theorem* xgcd_aux_rec
- \+/\- *theorem* xgcd_aux_rec

modified src/tactic/lint/simp.lean



## [2020-05-21 15:42:46](https://github.com/leanprover-community/mathlib/commit/d532eb6)
feat(order/lattice): sup_left_idem and similar ([#2768](https://github.com/leanprover-community/mathlib/pull/2768))
#### Estimated changes
modified src/order/lattice.lean
- \+ *lemma* sup_left_idem
- \+ *lemma* sup_right_idem
- \+ *lemma* inf_left_idem
- \+ *lemma* inf_right_idem



## [2020-05-21 07:51:07](https://github.com/leanprover-community/mathlib/commit/951b967)
refactor(data/nat/basic): use function equality for `iterate` lemmas ([#2748](https://github.com/leanprover-community/mathlib/pull/2748))
#### Estimated changes
modified src/algebra/group_power.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/special_functions/exp_log.lean

modified src/computability/turing_machine.lean

modified src/data/nat/basic.lean
- \+/\- *theorem* iterate_zero
- \+ *theorem* iterate_zero_apply
- \+/\- *theorem* iterate_succ
- \+ *theorem* iterate_succ_apply
- \+/\- *theorem* iterate_add
- \+ *theorem* iterate_add_apply
- \+/\- *theorem* iterate_succ'
- \+ *theorem* iterate_succ_apply'
- \+/\- *theorem* iterate_zero
- \+/\- *theorem* iterate_succ
- \+/\- *theorem* iterate_add
- \+/\- *theorem* iterate_succ'

modified src/field_theory/perfect_closure.lean

modified src/topology/metric_space/contracting.lean



## [2020-05-20 19:37:56](https://github.com/leanprover-community/mathlib/commit/a540d79)
chore(archive/sensitivity): Clean up function coercion in sensitivity proof (depends on [#2756](https://github.com/leanprover-community/mathlib/pull/2756)) ([#2758](https://github.com/leanprover-community/mathlib/pull/2758))
This formalizes the proof of an old conjecture: `is_awesome Gabriel`. I also took the opportunity to remove type class struggling, which I think is related to the proof of `is_awesome Floris`.
I think @jcommelin should also update this sensitivity file to use his sum notations if applicable.
#### Estimated changes
modified archive/sensitivity.lean
- \- *def* module
- \- *def* add_comm_semigroup
- \- *def* add_comm_monoid
- \- *def* has_scalar
- \- *def* has_add



## [2020-05-20 18:10:11](https://github.com/leanprover-community/mathlib/commit/3c9bf6b)
chore(scripts): update nolints.txt ([#2763](https://github.com/leanprover-community/mathlib/pull/2763))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-20 15:35:04](https://github.com/leanprover-community/mathlib/commit/d6420bd)
feat(ring_theory/principal_ideal_domain): definition of principal submodule ([#2761](https://github.com/leanprover-community/mathlib/pull/2761))
This PR generalizes the definition of principal ideals to principal submodules. It turns out that it's essentially enough to replace `ideal R` with `submodule R M` in the relevant places. With this change, it's possible to talk about principal fractional ideals (although that development will have to wait [#2714](https://github.com/leanprover-community/mathlib/pull/2714) gets merged).
Since the PR already changes the variables used in this file, I took the opportunity to rename them so `[ring α]` becomes `[ring R]`.
#### Estimated changes
modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* span_singleton_generator
- \+/\- *lemma* generator_mem
- \+ *lemma* mem_iff_eq_smul_generator
- \+/\- *lemma* mem_iff_generator_dvd
- \+/\- *lemma* eq_bot_iff_generator_eq_zero
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+/\- *lemma* factors_decreasing
- \+/\- *lemma* is_maximal_of_irreducible
- \+/\- *lemma* irreducible_iff_prime
- \+/\- *lemma* associates_irreducible_iff_prime
- \+/\- *lemma* factors_spec
- \+/\- *lemma* span_singleton_generator
- \+/\- *lemma* generator_mem
- \+/\- *lemma* mem_iff_generator_dvd
- \+/\- *lemma* eq_bot_iff_generator_eq_zero
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+/\- *lemma* factors_decreasing
- \+/\- *lemma* is_maximal_of_irreducible
- \+/\- *lemma* irreducible_iff_prime
- \+/\- *lemma* associates_irreducible_iff_prime
- \+/\- *lemma* factors_spec



## [2020-05-20 15:35:02](https://github.com/leanprover-community/mathlib/commit/4c3e1a9)
feat(algebra): the R-module structure on S-linear maps, for S an R-algebra ([#2759](https://github.com/leanprover-community/mathlib/pull/2759))
I couldn't find this already in mathlib, but perhaps I've missed it.
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+ *def* linear_map_algebra_has_scalar
- \+ *def* linear_map_algebra_module



## [2020-05-20 15:34:59](https://github.com/leanprover-community/mathlib/commit/6df77a6)
chore(*): update to Lean 3.14.0 ([#2756](https://github.com/leanprover-community/mathlib/pull/2756))
This is an optimistic PR, betting *nothing* will break when moving to Lean 3.14.0.
#### Estimated changes
modified leanpkg.toml



## [2020-05-20 15:34:58](https://github.com/leanprover-community/mathlib/commit/164c2e3)
chore(category_theory): attributes and a transport proof ([#2751](https://github.com/leanprover-community/mathlib/pull/2751))
A couple of cleanups, modified a proof or two so that `@[simps]` can be used, which let me clean up some other proofs. Also a proof that we can transfer that `F` preserves the limit `K` along an isomorphism in `K`.
(Preparation for some PRs from my topos project)
#### Estimated changes
modified src/category_theory/equivalence.lean
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* refl
- \+/\- *def* symm

modified src/category_theory/limits/cones.lean

modified src/category_theory/limits/preserves.lean
- \+ *def* preserves_limit_of_iso

modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* hom_inv_id_app
- \+/\- *lemma* inv_hom_id_app
- \+/\- *lemma* of_components.app
- \+/\- *lemma* of_components.hom_app
- \+/\- *lemma* of_components.inv_app
- \+/\- *lemma* hom_inv_id_app
- \+/\- *lemma* inv_hom_id_app
- \+/\- *lemma* of_components.app
- \+/\- *lemma* of_components.hom_app
- \+/\- *lemma* of_components.inv_app
- \+/\- *def* of_components
- \+/\- *def* of_components



## [2020-05-20 12:01:53](https://github.com/leanprover-community/mathlib/commit/ab5d0f1)
feat(category_theory/binary_products): some product lemmas and their dual ([#2752](https://github.com/leanprover-community/mathlib/pull/2752))
A bunch of lemmas about binary products.
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *lemma* prod.map_fst
- \+/\- *lemma* prod.map_snd
- \+ *lemma* prod_map_id_id
- \+ *lemma* prod_lift_fst_snd
- \+ *lemma* prod_map_map
- \+ *lemma* prod_map_comp_id
- \+ *lemma* prod_map_id_comp
- \+ *lemma* prod.lift_map
- \+/\- *lemma* coprod.inl_map
- \+/\- *lemma* coprod.inr_map
- \+ *lemma* coprod_map_id_id
- \+ *lemma* coprod_desc_inl_inr
- \+ *lemma* coprod_map_map
- \+ *lemma* coprod_map_comp_id
- \+ *lemma* coprod_map_id_comp
- \+ *lemma* coprod.map_desc
- \+ *lemma* braid_natural
- \+/\- *lemma* prod.symmetry'
- \+/\- *lemma* prod.symmetry
- \+ *lemma* prod_left_unitor_hom_naturality
- \+ *lemma* prod_left_unitor_inv_naturality
- \+ *lemma* prod_right_unitor_hom_naturality
- \+ *lemma* prod_right_unitor_inv_naturality
- \+/\- *lemma* prod.map_fst
- \+/\- *lemma* prod.map_snd
- \+/\- *lemma* coprod.inl_map
- \+/\- *lemma* coprod.inr_map
- \+/\- *lemma* prod.symmetry'
- \+/\- *lemma* prod.symmetry
- \+ *def* prod_functor_left_comp



## [2020-05-20 11:03:44](https://github.com/leanprover-community/mathlib/commit/1f00282)
docs(linear_algebra/sesquilinear_form): correct module docs ([#2757](https://github.com/leanprover-community/mathlib/pull/2757))
@PatrickMassot mentioned that the docs for `sesquilinear_form` mention bilinear forms instead in a few places. This PR corrects them to use "sesquilinear form" everywhere.
#### Estimated changes
modified src/linear_algebra/sesquilinear_form.lean



## [2020-05-20 06:18:22](https://github.com/leanprover-community/mathlib/commit/cbe80ed)
feat(linear_algebra/projection): projection to a subspace ([#2739](https://github.com/leanprover-community/mathlib/pull/2739))
Define equivalence between complement subspaces and projections.
#### Estimated changes
modified src/algebra/module.lean
- \+/\- *lemma* add_mem_iff_left
- \+/\- *lemma* add_mem_iff_right
- \+/\- *lemma* add_mem_iff_left
- \+/\- *lemma* add_mem_iff_right

modified src/data/prod.lean
- \+ *lemma* fst_eq_iff
- \+ *lemma* snd_eq_iff

modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.range_range_restrict
- \+ *lemma* coe_of_eq_apply
- \+ *lemma* of_eq_symm
- \+ *lemma* quot_equiv_of_eq_bot_apply_mk
- \+ *lemma* quot_equiv_of_eq_bot_symm_apply
- \+ *lemma* coe_quot_equiv_of_eq_bot_symm
- \+ *lemma* quot_ker_equiv_range_apply_mk
- \+ *lemma* quot_ker_equiv_range_symm_apply_image
- \+ *lemma* coe_quotient_inf_to_sup_quotient
- \+ *lemma* quotient_inf_equiv_sup_quotient_apply_mk
- \+ *lemma* quotient_inf_equiv_sup_quotient_symm_apply_left
- \+ *lemma* quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff
- \+ *lemma* quotient_inf_equiv_sup_quotient_symm_apply_right
- \- *lemma* range_range_restrict
- \+ *theorem* mem_right_iff_eq_zero_of_disjoint
- \+ *theorem* mem_left_iff_eq_zero_of_disjoint
- \+/\- *theorem* map_le_map_iff
- \+ *theorem* map_le_map_iff'
- \+ *theorem* map_eq_top_iff
- \+ *theorem* map_mkq_eq_top
- \+/\- *theorem* of_top_apply
- \+ *theorem* coe_of_top_symm_apply
- \+/\- *theorem* of_top_symm_apply
- \+/\- *theorem* map_le_map_iff
- \+/\- *theorem* of_top_apply
- \+/\- *theorem* of_top_symm_apply
- \+ *def* of_eq
- \+/\- *def* of_top
- \+ *def* quot_equiv_of_eq_bot
- \+/\- *def* of_top

modified src/linear_algebra/basis.lean
- \+ *lemma* submodule.exists_is_compl

modified src/linear_algebra/dimension.lean

created src/linear_algebra/projection.lean
- \+ *lemma* quotient_equiv_of_is_compl_symm_apply
- \+ *lemma* quotient_equiv_of_is_compl_apply_mk_coe
- \+ *lemma* mk_quotient_equiv_of_is_compl_apply
- \+ *lemma* coe_prod_equiv_of_is_compl
- \+ *lemma* coe_prod_equiv_of_is_compl'
- \+ *lemma* prod_equiv_of_is_compl_symm_apply_left
- \+ *lemma* prod_equiv_of_is_compl_symm_apply_right
- \+ *lemma* prod_equiv_of_is_compl_symm_apply_fst_eq_zero
- \+ *lemma* prod_equiv_of_is_compl_symm_apply_snd_eq_zero
- \+ *lemma* linear_proj_of_is_compl_apply_left
- \+ *lemma* linear_proj_of_is_compl_range
- \+ *lemma* linear_proj_of_is_compl_apply_eq_zero_iff
- \+ *lemma* linear_proj_of_is_compl_apply_right'
- \+ *lemma* linear_proj_of_is_compl_apply_right
- \+ *lemma* linear_proj_of_is_compl_ker
- \+ *lemma* linear_proj_of_is_compl_idempotent
- \+ *lemma* is_compl_of_proj
- \+ *lemma* linear_proj_of_is_compl_of_proj
- \+ *lemma* coe_is_compl_equiv_proj_apply
- \+ *lemma* coe_is_compl_equiv_proj_symm_apply
- \+ *def* quotient_equiv_of_is_compl
- \+ *def* prod_equiv_of_is_compl
- \+ *def* linear_proj_of_is_compl
- \+ *def* is_compl_equiv_proj



## [2020-05-19 22:34:25](https://github.com/leanprover-community/mathlib/commit/3c1f9f9)
feat(data/nat/choose): sum_range_choose_halfway ([#2688](https://github.com/leanprover-community/mathlib/pull/2688))
This is a lemma on the way to proving that the product of primes less than `n` is less than `4 ^ n`, which is itself a lemma in Bertrand's postulate.
The lemma itself is of dubious significance, but it will eventually be necessary for Bertrand, and I want to commit early and often. Brief discussion of this decision at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619722 .
This is my second PR to mathlib; the code is definitely verbose and poorly structured, but I don't know how to fix it. I'm expecting almost no lines of the original to remain by the end of this!
#### Estimated changes
modified src/algebra/big_operators.lean

modified src/data/nat/choose.lean
- \+ *lemma* sum_range_choose_halfway



## [2020-05-19 18:38:27](https://github.com/leanprover-community/mathlib/commit/e3aca90)
feat(logic/basic): spaces with a zero or a one are nonempty ([#2743](https://github.com/leanprover-community/mathlib/pull/2743))
Register instances that a space with a zero or a one is not empty, with low priority as we don't want to embark on a search for a zero or a one if this is not necessary.
Discussion on Zulip at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/inhabited.20and.20nonempty.20instances/near/198030072
#### Estimated changes
modified src/analysis/calculus/inverse.lean

modified src/analysis/normed_space/banach.lean

modified src/group_theory/bundled_subgroup.lean

modified src/group_theory/sylow.lean

modified src/logic/basic.lean



## [2020-05-19 17:00:43](https://github.com/leanprover-community/mathlib/commit/607767e)
feat(algebra/big_operators): reversing an interval doesn't change the product ([#2740](https://github.com/leanprover-community/mathlib/pull/2740))
Also use Gauss summation in the Gauss summation formula.
Inspired by [#2688](https://github.com/leanprover-community/mathlib/pull/2688)
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* prod_Ico_reflect
- \+ *lemma* sum_Ico_reflect
- \+ *lemma* prod_range_reflect
- \+ *lemma* sum_range_reflect

modified src/data/finset.lean
- \+ *lemma* image_const_sub
- \+ *lemma* range_image_pred_top_sub



## [2020-05-19 15:54:58](https://github.com/leanprover-community/mathlib/commit/62c22da)
fix(ci): replace 2 old secret names ([#2744](https://github.com/leanprover-community/mathlib/pull/2744))
[`lean-3.13.2`](https://github.com/leanprover-community/mathlib/tree/lean-3.13.2) is out of date, since I missed two instances of `DEPLOY_NIGHTLY_GITHUB_TOKEN` in [#2737](https://github.com/leanprover-community/mathlib/pull/2737).
#### Estimated changes
modified .github/workflows/build.yml



## [2020-05-19 11:50:10](https://github.com/leanprover-community/mathlib/commit/1e18512)
chore(*): remove non-canonical `option.decidable_eq_none` instance ([#2741](https://github.com/leanprover-community/mathlib/pull/2741))
I also removed the hack in `ulower.primcodable` where I had to use `none = o` instead of `o = none`.
#### Estimated changes
modified src/computability/primrec.lean

modified src/data/list/sigma.lean

modified src/data/option/defs.lean
- \+ *def* decidable_eq_none

modified src/data/seq/seq.lean



## [2020-05-19 09:58:39](https://github.com/leanprover-community/mathlib/commit/93b41e5)
fix(*): put headings in multiline module docs on their own lines ([#2742](https://github.com/leanprover-community/mathlib/pull/2742))
found using regex: `/-! #([^-/])*$`.
These don't render correctly in the mathlib docs. Module doc strings that consist of a heading on its own line are OK so I haven't changed them.
I also moved some descriptive text from copyright headers to module docs, or removed such text if there was already a module doc string.
#### Estimated changes
modified archive/sensitivity.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/calculus/local_extr.lean

modified src/category_theory/shift.lean

modified src/computability/turing_machine.lean

modified src/data/matrix/basic.lean

modified src/data/set/basic.lean

modified src/data/set/function.lean

modified src/data/set/intervals/disjoint.lean

modified src/geometry/manifold/mfderiv.lean

modified src/linear_algebra/determinant.lean

modified src/linear_algebra/nonsingular_inverse.lean

modified src/linear_algebra/quadratic_form.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/bases.lean

modified src/order/filter/extr.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/localization.lean

modified src/tactic/core.lean

modified src/topology/algebra/ordered.lean

modified src/topology/local_extr.lean

modified src/topology/metric_space/cau_seq_filter.lean

modified src/topology/uniform_space/cauchy.lean



## [2020-05-19 09:58:37](https://github.com/leanprover-community/mathlib/commit/3d948bf)
feat(analysis/normed_space): interior of `closed_ball` etc ([#2723](https://github.com/leanprover-community/mathlib/pull/2723))
* define `sphere x r`
* prove formulas for `interior`, `closure`, and `frontier` of open and closed balls in real normed vector spaces.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* submodule.eq_top_of_nonempty_interior
- \+/\- *lemma* submodule.eq_top_of_nonempty_interior
- \+ *theorem* closure_ball
- \+ *theorem* frontier_ball
- \+ *theorem* interior_closed_ball
- \+ *theorem* interior_closed_ball'
- \+ *theorem* frontier_closed_ball
- \+ *theorem* frontier_closed_ball'

modified src/topology/basic.lean
- \+ *lemma* preimage_interior_subset_interior_preimage

modified src/topology/continuous_on.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* closed_ball_zero
- \+ *theorem* sphere_subset_closed_ball
- \+ *theorem* sphere_disjoint_ball
- \+ *theorem* ball_union_sphere
- \+ *theorem* sphere_union_ball
- \+ *theorem* closed_ball_diff_sphere
- \+ *theorem* closed_ball_diff_ball
- \+/\- *theorem* ball_eq_empty_iff_nonpos
- \+ *theorem* closed_ball_eq_empty_iff_neg
- \+ *theorem* closure_ball_subset_closed_ball
- \+ *theorem* frontier_ball_subset_sphere
- \+ *theorem* frontier_closed_ball_subset_sphere
- \+ *theorem* ball_subset_interior_closed_ball
- \+/\- *theorem* ball_eq_empty_iff_nonpos
- \+ *def* sphere

modified src/topology/metric_space/closeds.lean



## [2020-05-19 08:28:09](https://github.com/leanprover-community/mathlib/commit/f2cb546)
fix(ci): setup git before nolints, rename secret ([#2737](https://github.com/leanprover-community/mathlib/pull/2737))
Oops, I broke the update nolints step on master. This should fix it.
#### Estimated changes
modified .github/workflows/build.yml

modified scripts/deploy_docs.sh

modified scripts/update_nolints.sh



## [2020-05-19 08:28:08](https://github.com/leanprover-community/mathlib/commit/3968f7f)
feat(linear_algebra): equiv_of_is_basis' and module.fintype_of_fintype ([#2735](https://github.com/leanprover-community/mathlib/pull/2735))
#### Estimated changes
modified src/linear_algebra/basis.lean
- \+/\- *def* equiv_of_is_basis
- \+ *def* equiv_of_is_basis'
- \+ *def* module.fintype_of_fintype
- \+/\- *def* equiv_of_is_basis



## [2020-05-19 08:28:05](https://github.com/leanprover-community/mathlib/commit/80b7f97)
feat(tactic/localized): fail if unused locale is open ([#2718](https://github.com/leanprover-community/mathlib/pull/2718))
This is more in line with the behavior of `open`.
Closes [#2702](https://github.com/leanprover-community/mathlib/pull/2702)
#### Estimated changes
modified src/measure_theory/simple_func_dense.lean

modified src/tactic/localized.lean

modified test/localized/localized.lean



## [2020-05-19 08:28:03](https://github.com/leanprover-community/mathlib/commit/3ba7d12)
feat(algebra): obtaining algebraic classes through in/surjective maps ([#2638](https://github.com/leanprover-community/mathlib/pull/2638))
This is needed for the definition of Witt vectors.
#### Estimated changes
created src/algebra/inj_surj.lean
- \+ *def* semigroup_of_injective
- \+ *def* comm_semigroup_of_injective
- \+ *def* semigroup_of_surjective
- \+ *def* comm_semigroup_of_surjective
- \+ *def* monoid_of_injective
- \+ *def* comm_monoid_of_injective
- \+ *def* group_of_injective
- \+ *def* comm_group_of_injective
- \+ *def* monoid_of_surjective
- \+ *def* comm_monoid_of_surjective
- \+ *def* group_of_surjective
- \+ *def* comm_group_of_surjective
- \+ *def* semiring_of_injective
- \+ *def* comm_semiring_of_injective
- \+ *def* ring_of_injective
- \+ *def* comm_ring_of_injective
- \+ *def* semiring_of_surjective
- \+ *def* comm_semiring_of_surjective
- \+ *def* ring_of_surjective
- \+ *def* comm_ring_of_surjective



## [2020-05-19 07:10:15](https://github.com/leanprover-community/mathlib/commit/52aa128)
feat(data/equiv): add add_equiv.to_multiplicative ([#2732](https://github.com/leanprover-community/mathlib/pull/2732))
We already have `add_monoid_hom.to_multiplicative`. This adds `add_equiv.to_multiplicative`.
It is placed in `data/equiv/mul_add.lean` because `data/equiv/mul_add.lean` already imports `algebra/group/type_tags.lean`.
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *def* add_equiv.to_multiplicative
- \+ *def* mul_equiv.to_additive



## [2020-05-19 06:13:04](https://github.com/leanprover-community/mathlib/commit/906220c)
feat(topology/bounded_continuous_function): Normed algebra of bounded continuous functions ([#2722](https://github.com/leanprover-community/mathlib/pull/2722))
The space `C(α, γ)` of bounded continuous functions into a normed algebra γ is a normed algebra.  The space of bounded continuous functions into a normed 𝕜-space is a `C(α, 𝕜)`-module.
#### Estimated changes
modified src/analysis/normed_space/basic.lean

modified src/topology/bounded_continuous_function.lean
- \+ *lemma* norm_smul_le
- \+ *def* C



## [2020-05-19 03:26:24](https://github.com/leanprover-community/mathlib/commit/01efaeb)
feat(ci): run lint and tests in parallel ([#2736](https://github.com/leanprover-community/mathlib/pull/2736))
Actions doesn't let us run *steps* in parallel, but we can run *jobs* in parallel. The lint and test jobs are part of the same *workflow*. Understanding Actions terminology is half the battle.
#### Estimated changes
modified .github/workflows/build.yml

modified bors.toml

modified scripts/deploy_docs.sh



## [2020-05-18 18:12:30](https://github.com/leanprover-community/mathlib/commit/f01260a)
feat(algebra/char_p): eq_iff_modeq_int ([#2731](https://github.com/leanprover-community/mathlib/pull/2731))
#### Estimated changes
modified src/algebra/char_p.lean
- \+ *lemma* eq_iff_modeq_int



## [2020-05-18 16:18:17](https://github.com/leanprover-community/mathlib/commit/9d762df)
chore(scripts): update nolints.txt ([#2733](https://github.com/leanprover-community/mathlib/pull/2733))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-18 13:38:47](https://github.com/leanprover-community/mathlib/commit/ff3130d)
feat(topology/constructions): topology on ulift ([#2716](https://github.com/leanprover-community/mathlib/pull/2716))
#### Estimated changes
modified src/topology/constructions.lean
- \+ *lemma* continuous_ulift_down
- \+ *lemma* continuous_ulift_up

modified src/topology/homeomorph.lean
- \+ *def* {u



## [2020-05-18 13:38:45](https://github.com/leanprover-community/mathlib/commit/4026bd8)
feat(category_theory/full_subcategory): induced category from a groupoid is a groupoid ([#2715](https://github.com/leanprover-community/mathlib/pull/2715))
Also some minor cleanup to the same file.
#### Estimated changes
modified src/category_theory/full_subcategory.lean
- \- *lemma* induced_functor.obj
- \- *lemma* induced_functor.hom
- \+/\- *def* induced_functor
- \+/\- *def* induced_functor



## [2020-05-18 13:38:43](https://github.com/leanprover-community/mathlib/commit/2fa1d7c)
Revert "fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))" ([#2713](https://github.com/leanprover-community/mathlib/pull/2713))
These are good simp lemmas: they push things into a proof-irrelevant position.
This reverts commit 5a309a3aa30fcec122a26f379f05b466ee46fc7a.
#### Estimated changes
modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* eq_to_hom_map
- \+/\- *lemma* eq_to_iso_map
- \+/\- *lemma* eq_to_hom_app
- \+/\- *lemma* eq_to_hom_map
- \+/\- *lemma* eq_to_iso_map
- \+/\- *lemma* eq_to_hom_app



## [2020-05-18 13:38:41](https://github.com/leanprover-community/mathlib/commit/8b42245)
refactor(algebra): merge init_.algebra into algebra ([#2707](https://github.com/leanprover-community/mathlib/pull/2707))
This is a big refactor PR. It depends on [#2697](https://github.com/leanprover-community/mathlib/pull/2697), which brings in the algebra hierarchy without any change to the file structure. This PR merges `init_.algebra.group` into `algebra.group` and so on for the rest of the algebraic hierarchy.
#### Estimated changes
modified archive/100-theorems-list/42_inverse_triangle_sum.lean

modified archive/sensitivity.lean

modified scripts/nolints.txt

modified src/algebra/char_zero.lean

modified src/algebra/continued_fractions/basic.lean

modified src/algebra/continued_fractions/convergents_equiv.lean

modified src/algebra/field.lean
- \+ *lemma* division_def
- \+ *lemma* inv_zero
- \+ *lemma* div_zero
- \+ *lemma* mul_inv_cancel
- \+ *lemma* inv_mul_cancel
- \+ *lemma* one_div_eq_inv
- \+ *lemma* inv_eq_one_div
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* mul_one_div_cancel
- \+ *lemma* one_div_mul_cancel
- \+ *lemma* div_self
- \+ *lemma* one_div_one
- \+ *lemma* mul_div_assoc
- \+/\- *lemma* mul_div_assoc'
- \+ *lemma* one_div_ne_zero
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \+ *lemma* inv_ne_zero
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \+ *lemma* one_inv_eq
- \+ *lemma* div_one
- \+ *lemma* zero_div
- \+ *lemma* division_ring.mul_ne_zero
- \+ *lemma* mul_ne_zero_comm
- \+ *lemma* eq_one_div_of_mul_eq_one
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* division_ring.one_div_mul_one_div
- \+ *lemma* one_div_neg_one_eq_neg_one
- \+ *lemma* one_div_neg_eq_neg_one_div
- \+ *lemma* div_neg_eq_neg_div
- \+ *lemma* neg_div
- \+/\- *lemma* neg_div'
- \+ *lemma* neg_div_neg_eq
- \+ *lemma* one_div_one_div
- \+ *lemma* inv_inv'
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* mul_inv'
- \+ *lemma* one_div_div
- \+ *lemma* div_helper
- \+ *lemma* mul_div_cancel
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_mul_left
- \+ *lemma* mul_div_mul_right
- \+ *lemma* div_add_div_same
- \+ *lemma* div_sub_div_same
- \+ *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* div_eq_one_iff_eq
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* eq_div_of_mul_eq
- \+ *lemma* mul_eq_of_eq_div
- \+ *lemma* add_div_eq_mul_add_div
- \+ *lemma* mul_mul_div
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* div_mul_right
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_cancel'
- \+ *lemma* one_div_add_one_div
- \+ *lemma* div_mul_div
- \+ *lemma* mul_div_mul_left
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* div_mul_eq_mul_div_comm
- \+ *lemma* div_add_div
- \+ *lemma* div_sub_div
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_div_div_div_eq
- \+ *lemma* div_mul_eq_div_mul_one_div
- \+/\- *lemma* add_div'
- \+/\- *lemma* sub_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_sub'
- \+/\- *lemma* add_div'
- \+/\- *lemma* sub_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_sub'
- \- *lemma* map_ne_zero
- \- *lemma* map_eq_zero
- \- *lemma* map_inv
- \- *lemma* map_div
- \- *lemma* injective
- \+/\- *lemma* mul_div_assoc'
- \+/\- *lemma* neg_div'
- \+/\- *theorem* inv_one
- \+/\- *theorem* inv_one

modified src/algebra/floor.lean

modified src/algebra/free.lean

modified src/algebra/gcd_domain.lean

modified src/algebra/group/basic.lean
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_left_comm
- \+ *lemma* mul_right_comm
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_right_cancel_iff
- \+ *lemma* one_mul
- \+ *lemma* mul_one
- \+/\- *lemma* left_inv_eq_right_inv
- \+/\- *lemma* bit0_zero
- \+/\- *lemma* bit1_zero
- \+/\- *lemma* inv_unique
- \+ *lemma* mul_left_inv
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_cancel_right
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* one_inv
- \+ *lemma* inv_inv
- \+ *lemma* mul_right_inv
- \+ *lemma* inv_inj
- \+ *lemma* group.mul_left_cancel
- \+ *lemma* group.mul_right_cancel
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_rev
- \+ *lemma* eq_inv_of_eq_inv
- \+ *lemma* eq_inv_of_mul_eq_one
- \+ *lemma* eq_mul_inv_of_mul_eq
- \+ *lemma* eq_inv_mul_of_mul_eq
- \+ *lemma* inv_mul_eq_of_eq_mul
- \+ *lemma* mul_inv_eq_of_eq_mul
- \+ *lemma* eq_mul_of_mul_inv_eq
- \+ *lemma* eq_mul_of_inv_mul_eq
- \+ *lemma* mul_eq_of_eq_inv_mul
- \+ *lemma* mul_eq_of_eq_mul_inv
- \+/\- *lemma* inv_involutive
- \+ *lemma* sub_eq_add_neg
- \+ *lemma* sub_self
- \+ *lemma* sub_add_cancel
- \+ *lemma* add_sub_cancel
- \+ *lemma* add_sub_assoc
- \+ *lemma* eq_of_sub_eq_zero
- \+ *lemma* sub_eq_zero_of_eq
- \+ *lemma* sub_eq_zero_iff_eq
- \+ *lemma* zero_sub
- \+ *lemma* sub_zero
- \+ *lemma* sub_ne_zero_of_ne
- \+ *lemma* sub_neg_eq_add
- \+ *lemma* neg_sub
- \+ *lemma* add_sub
- \+ *lemma* sub_add_eq_sub_sub_swap
- \+ *lemma* add_sub_add_right_eq_sub
- \+ *lemma* eq_sub_of_add_eq
- \+ *lemma* sub_eq_of_eq_add
- \+ *lemma* eq_add_of_sub_eq
- \+ *lemma* add_eq_of_eq_sub
- \+/\- *lemma* sub_add_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_right
- \+ *lemma* mul_inv
- \+ *lemma* sub_add_eq_sub_sub
- \+ *lemma* neg_add_eq_sub
- \+ *lemma* sub_add_eq_add_sub
- \+ *lemma* sub_sub
- \+ *lemma* sub_add
- \+ *lemma* add_sub_add_left_eq_sub
- \+ *lemma* eq_sub_of_add_eq'
- \+ *lemma* sub_eq_of_eq_add'
- \+ *lemma* eq_add_of_sub_eq'
- \+ *lemma* add_eq_of_eq_sub'
- \+ *lemma* sub_sub_self
- \+ *lemma* add_sub_comm
- \+ *lemma* sub_eq_sub_add_sub
- \+ *lemma* neg_neg_sub_neg
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* sub_eq_neg_add
- \+/\- *lemma* neg_sub_neg
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* add_sub_cancel'_right
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* sub_right_comm
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left
- \+/\- *lemma* sub_eq_sub_iff_add_eq_add
- \+/\- *lemma* sub_eq_sub_iff_sub_eq_sub
- \+/\- *lemma* sub_add_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_right
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* sub_eq_neg_add
- \+/\- *lemma* neg_sub_neg
- \+/\- *lemma* add_sub_cancel'
- \+/\- *lemma* add_sub_cancel'_right
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* sub_right_comm
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left
- \+/\- *lemma* sub_eq_sub_iff_add_eq_add
- \+/\- *lemma* sub_eq_sub_iff_sub_eq_sub
- \+/\- *lemma* bit0_zero
- \+/\- *lemma* bit1_zero
- \+/\- *lemma* left_inv_eq_right_inv
- \+/\- *lemma* inv_unique
- \+/\- *lemma* inv_involutive
- \+/\- *theorem* mul_mul_mul_comm
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* left_inverse_inv
- \+/\- *theorem* eq_of_inv_eq_inv
- \+/\- *theorem* left_inverse_sub_add_left
- \+/\- *theorem* left_inverse_add_left_sub
- \+/\- *theorem* left_inverse_add_right_neg_add
- \+/\- *theorem* left_inverse_neg_add_add_right
- \+/\- *theorem* neg_add'
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_mul_mul_comm
- \+/\- *theorem* eq_of_inv_eq_inv
- \+/\- *theorem* left_inverse_inv
- \+/\- *theorem* left_inverse_sub_add_left
- \+/\- *theorem* left_inverse_add_left_sub
- \+/\- *theorem* left_inverse_add_right_neg_add
- \+/\- *theorem* left_inverse_neg_add_add_right
- \+/\- *theorem* neg_add'
- \+ *def* eq_of_add_eq_add_left
- \+ *def* eq_of_add_eq_add_right
- \+ *def* inv_mul_self
- \+ *def* mul_inv_self

modified src/algebra/group/conj.lean

modified src/algebra/group/default.lean

modified src/algebra/group/hom.lean
- \- *lemma* coe_mul_left
- \- *lemma* mul_right_apply
- \- *def* mul_left
- \- *def* mul_right

deleted src/algebra/group/is_unit.lean
- \- *lemma* is_unit_unit
- \- *lemma* is_unit.map
- \- *lemma* is_unit.coe_lift_right
- \- *lemma* is_unit.mul_lift_right_inv
- \- *lemma* is_unit.lift_right_inv_mul
- \- *theorem* is_unit_one
- \- *theorem* is_unit_of_mul_eq_one
- \- *theorem* is_unit_iff_exists_inv
- \- *theorem* is_unit_iff_exists_inv'
- \- *theorem* units.is_unit_mul_units
- \- *theorem* is_unit_of_mul_is_unit_left
- \- *theorem* is_unit_of_mul_is_unit_right
- \- *theorem* is_unit_nat
- \- *theorem* is_unit.mul_right_inj
- \- *theorem* is_unit.mul_left_inj
- \- *def* is_unit

modified src/algebra/group/to_additive.lean

modified src/algebra/group/units.lean
- \+ *lemma* is_unit_unit
- \- *lemma* coe_val_hom
- \+ *theorem* divp_self
- \+ *theorem* divp_one
- \+ *theorem* divp_assoc
- \+ *theorem* divp_inv
- \+ *theorem* divp_mul_cancel
- \+ *theorem* mul_divp_cancel
- \+ *theorem* divp_left_inj
- \+ *theorem* divp_divp_eq_divp_mul
- \+ *theorem* divp_eq_iff_mul_eq
- \+ *theorem* divp_eq_one_iff_eq
- \+ *theorem* one_divp
- \+ *theorem* is_unit_one
- \+ *theorem* is_unit_of_mul_eq_one
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* units.is_unit_mul_units
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* is_unit.mul_right_inj
- \+ *theorem* is_unit.mul_left_inj
- \- *theorem* nat.units_eq_one
- \- *theorem* nat.add_units_eq_zero
- \+ *def* divp
- \+ *def* is_unit
- \- *def* val_hom

modified src/algebra/group/units_hom.lean
- \+ *lemma* is_unit.map
- \+ *lemma* is_unit.coe_lift_right
- \+ *lemma* is_unit.mul_lift_right_inv
- \+ *lemma* is_unit.lift_right_inv_mul

modified src/algebra/group/with_one.lean

modified src/algebra/group_power.lean

modified src/algebra/group_ring_action.lean

modified src/algebra/group_with_zero.lean
- \+/\- *lemma* div_eq_div_iff
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff
- \+/\- *lemma* div_eq_div_iff
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff

modified src/algebra/lie_algebra.lean

modified src/algebra/opposites.lean

modified src/algebra/ordered_field.lean
- \+ *lemma* mul_zero_lt_mul_inv_of_pos
- \+ *lemma* mul_zero_lt_mul_inv_of_neg
- \+ *lemma* one_div_pos_of_pos
- \+ *lemma* pos_of_one_div_pos
- \+ *lemma* one_div_neg_of_neg
- \+ *lemma* neg_of_one_div_neg
- \+ *lemma* le_mul_of_ge_one_right
- \+ *lemma* le_mul_of_ge_one_left
- \+ *lemma* lt_mul_of_gt_one_right
- \+ *lemma* one_le_div_of_le
- \+ *lemma* le_of_one_le_div
- \+ *lemma* one_lt_div_of_lt
- \+ *lemma* lt_of_one_lt_div
- \+ *lemma* mul_le_of_le_div
- \+ *lemma* le_div_of_mul_le
- \+ *lemma* mul_lt_of_lt_div
- \+ *lemma* lt_div_of_mul_lt
- \+ *lemma* mul_le_of_div_le_of_neg
- \+ *lemma* div_le_of_mul_le_of_neg
- \+ *lemma* mul_lt_of_gt_div_of_neg
- \+ *lemma* div_lt_of_mul_lt_of_pos
- \+ *lemma* div_lt_of_mul_gt_of_neg
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* le_mul_of_div_le
- \+ *lemma* mul_sub_mul_div_mul_neg
- \+ *lemma* mul_sub_mul_div_mul_nonpos
- \+ *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \+ *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \+ *lemma* div_pos_of_pos_of_pos
- \+ *lemma* div_nonneg_of_nonneg_of_pos
- \+ *lemma* div_neg_of_neg_of_pos
- \+ *lemma* div_nonpos_of_nonpos_of_pos
- \+ *lemma* div_neg_of_pos_of_neg
- \+ *lemma* div_nonpos_of_nonneg_of_neg
- \+ *lemma* div_pos_of_neg_of_neg
- \+ *lemma* div_nonneg_of_nonpos_of_neg
- \+ *lemma* div_lt_div_of_lt_of_pos
- \+ *lemma* div_le_div_of_le_of_pos
- \+ *lemma* div_lt_div_of_lt_of_neg
- \+ *lemma* div_le_div_of_le_of_neg
- \+ *lemma* add_halves
- \+ *lemma* sub_self_div_two
- \+ *lemma* add_midpoint
- \+ *lemma* div_two_sub_self
- \+ *lemma* add_self_div_two
- \+ *lemma* mul_le_mul_of_mul_div_le
- \+ *lemma* div_two_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \+ *lemma* exists_add_lt_and_pos_of_lt
- \+ *lemma* ge_of_forall_ge_sub
- \+ *lemma* one_div_lt_one_div_of_lt
- \+ *lemma* one_div_le_one_div_of_le
- \+ *lemma* one_div_lt_one_div_of_lt_of_neg
- \+ *lemma* one_div_le_one_div_of_le_of_neg
- \+ *lemma* le_of_one_div_le_one_div
- \+ *lemma* le_of_one_div_le_one_div_of_neg
- \+ *lemma* lt_of_one_div_lt_one_div
- \+ *lemma* lt_of_one_div_lt_one_div_of_neg
- \+ *lemma* one_div_le_of_one_div_le_of_pos
- \+ *lemma* one_div_le_of_one_div_le_of_neg
- \+ *lemma* one_lt_one_div
- \+ *lemma* one_le_one_div
- \+ *lemma* one_div_lt_neg_one
- \+ *lemma* one_div_le_neg_one
- \+ *lemma* div_lt_div_of_pos_of_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos'
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_lt_one
- \+/\- *lemma* inv_le_one
- \+/\- *lemma* one_le_inv
- \+/\- *lemma* mul_self_inj_of_nonneg
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* div_nonneg'
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \+ *lemma* abs_div
- \+ *lemma* abs_one_div
- \+/\- *lemma* abs_inv
- \+/\- *lemma* inv_nonneg
- \+/\- *lemma* inv_nonpos
- \+/\- *lemma* inv_lt_one
- \+/\- *lemma* inv_le_one
- \+/\- *lemma* one_le_inv
- \+/\- *lemma* mul_self_inj_of_nonneg
- \+/\- *lemma* div_le_div_of_le_left
- \+/\- *lemma* inv_le_inv_of_le
- \+/\- *lemma* div_nonneg'
- \+/\- *lemma* div_le_div_of_le_of_nonneg
- \- *lemma* inv_pos_of_nat
- \- *lemma* one_div_pos_of_nat
- \- *lemma* one_div_le_one_div
- \- *lemma* one_div_lt_one_div
- \+/\- *lemma* abs_inv

modified src/algebra/ordered_group.lean
- \+ *lemma* add_le_add_left
- \+ *lemma* le_of_add_le_add_left
- \+ *lemma* add_lt_add_left
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* add_le_add_right
- \+ *lemma* add_le_add
- \+ *lemma* le_add_of_nonneg_right
- \+ *lemma* le_add_of_nonneg_left
- \+ *lemma* add_lt_add
- \+ *lemma* add_lt_add_of_le_of_lt
- \+ *lemma* add_lt_add_of_lt_of_le
- \+ *lemma* lt_add_of_pos_right
- \+ *lemma* lt_add_of_pos_left
- \+ *lemma* le_of_add_le_add_right
- \+ *lemma* lt_of_add_lt_add_right
- \+ *lemma* add_nonneg
- \+ *lemma* add_pos
- \+ *lemma* add_pos_of_pos_of_nonneg
- \+ *lemma* add_pos_of_nonneg_of_pos
- \+ *lemma* add_nonpos
- \+ *lemma* add_neg
- \+ *lemma* add_neg_of_neg_of_nonpos
- \+ *lemma* add_neg_of_nonpos_of_neg
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \+ *lemma* le_add_of_nonneg_of_le
- \+ *lemma* le_add_of_le_of_nonneg
- \+ *lemma* lt_add_of_pos_of_le
- \+ *lemma* lt_add_of_le_of_pos
- \+ *lemma* add_le_of_nonpos_of_le
- \+ *lemma* add_le_of_le_of_nonpos
- \+ *lemma* add_lt_of_neg_of_le
- \+ *lemma* add_lt_of_le_of_neg
- \+ *lemma* lt_add_of_nonneg_of_lt
- \+ *lemma* lt_add_of_lt_of_nonneg
- \+ *lemma* lt_add_of_pos_of_lt
- \+ *lemma* lt_add_of_lt_of_pos
- \+ *lemma* add_lt_of_nonpos_of_lt
- \+ *lemma* add_lt_of_lt_of_nonpos
- \+ *lemma* add_lt_of_neg_of_lt
- \+ *lemma* add_lt_of_lt_of_neg
- \+/\- *lemma* add_le_iff_nonpos_left
- \+/\- *lemma* add_le_iff_nonpos_right
- \+/\- *lemma* add_lt_iff_neg_right
- \+/\- *lemma* add_lt_iff_neg_left
- \+ *lemma* ordered_add_comm_group.add_lt_add_left
- \+ *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \+ *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \+ *lemma* neg_le_neg
- \+ *lemma* le_of_neg_le_neg
- \+ *lemma* nonneg_of_neg_nonpos
- \+ *lemma* neg_nonpos_of_nonneg
- \+ *lemma* nonpos_of_neg_nonneg
- \+ *lemma* neg_nonneg_of_nonpos
- \+ *lemma* neg_lt_neg
- \+ *lemma* lt_of_neg_lt_neg
- \+ *lemma* pos_of_neg_neg
- \+ *lemma* neg_neg_of_pos
- \+ *lemma* neg_of_neg_pos
- \+ *lemma* neg_pos_of_neg
- \+ *lemma* le_neg_of_le_neg
- \+ *lemma* neg_le_of_neg_le
- \+ *lemma* lt_neg_of_lt_neg
- \+ *lemma* neg_lt_of_neg_lt
- \+ *lemma* sub_nonneg_of_le
- \+ *lemma* le_of_sub_nonneg
- \+ *lemma* sub_nonpos_of_le
- \+ *lemma* le_of_sub_nonpos
- \+ *lemma* sub_pos_of_lt
- \+ *lemma* lt_of_sub_pos
- \+ *lemma* sub_neg_of_lt
- \+ *lemma* lt_of_sub_neg
- \+ *lemma* add_le_of_le_neg_add
- \+ *lemma* le_neg_add_of_add_le
- \+ *lemma* add_le_of_le_sub_left
- \+ *lemma* le_sub_left_of_add_le
- \+ *lemma* add_le_of_le_sub_right
- \+ *lemma* le_sub_right_of_add_le
- \+ *lemma* le_add_of_neg_add_le
- \+ *lemma* neg_add_le_of_le_add
- \+ *lemma* le_add_of_sub_left_le
- \+ *lemma* sub_left_le_of_le_add
- \+ *lemma* le_add_of_sub_right_le
- \+ *lemma* sub_right_le_of_le_add
- \+ *lemma* le_add_of_neg_add_le_left
- \+ *lemma* neg_add_le_left_of_le_add
- \+ *lemma* le_add_of_neg_add_le_right
- \+ *lemma* neg_add_le_right_of_le_add
- \+ *lemma* le_add_of_neg_le_sub_left
- \+ *lemma* neg_le_sub_left_of_le_add
- \+ *lemma* le_add_of_neg_le_sub_right
- \+ *lemma* neg_le_sub_right_of_le_add
- \+ *lemma* sub_le_of_sub_le
- \+ *lemma* sub_le_sub_left
- \+ *lemma* sub_le_sub_right
- \+ *lemma* sub_le_sub
- \+ *lemma* add_lt_of_lt_neg_add
- \+ *lemma* lt_neg_add_of_add_lt
- \+ *lemma* add_lt_of_lt_sub_left
- \+ *lemma* lt_sub_left_of_add_lt
- \+ *lemma* add_lt_of_lt_sub_right
- \+ *lemma* lt_sub_right_of_add_lt
- \+ *lemma* lt_add_of_neg_add_lt
- \+ *lemma* neg_add_lt_of_lt_add
- \+ *lemma* lt_add_of_sub_left_lt
- \+ *lemma* sub_left_lt_of_lt_add
- \+ *lemma* lt_add_of_sub_right_lt
- \+ *lemma* sub_right_lt_of_lt_add
- \+ *lemma* lt_add_of_neg_add_lt_left
- \+ *lemma* neg_add_lt_left_of_lt_add
- \+ *lemma* lt_add_of_neg_add_lt_right
- \+ *lemma* neg_add_lt_right_of_lt_add
- \+ *lemma* lt_add_of_neg_lt_sub_left
- \+ *lemma* neg_lt_sub_left_of_lt_add
- \+ *lemma* lt_add_of_neg_lt_sub_right
- \+ *lemma* neg_lt_sub_right_of_lt_add
- \+ *lemma* sub_lt_of_sub_lt
- \+ *lemma* sub_lt_sub_left
- \+ *lemma* sub_lt_sub_right
- \+ *lemma* sub_lt_sub
- \+ *lemma* sub_lt_sub_of_le_of_lt
- \+ *lemma* sub_lt_sub_of_lt_of_le
- \+ *lemma* sub_le_self
- \+ *lemma* sub_lt_self
- \+ *lemma* add_le_add_three
- \+ *lemma* min_add_add_left
- \+ *lemma* min_add_add_right
- \+ *lemma* max_add_add_left
- \+ *lemma* max_add_add_right
- \+ *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+ *lemma* max_neg_neg
- \+ *lemma* min_eq_neg_max_neg_neg
- \+ *lemma* min_neg_neg
- \+ *lemma* max_eq_neg_min_neg_neg
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_of_pos
- \+ *lemma* abs_of_nonpos
- \+ *lemma* abs_of_neg
- \+ *lemma* abs_zero
- \+ *lemma* abs_neg
- \+ *lemma* abs_pos_of_pos
- \+ *lemma* abs_pos_of_neg
- \+ *lemma* abs_sub
- \+ *lemma* ne_zero_of_abs_ne_zero
- \+ *lemma* eq_zero_of_neg_eq
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_abs
- \+ *lemma* le_abs_self
- \+ *lemma* neg_le_abs_self
- \+ *lemma* eq_zero_of_abs_eq_zero
- \+ *lemma* eq_of_abs_sub_eq_zero
- \+ *lemma* abs_pos_of_ne_zero
- \+ *lemma* abs_by_cases
- \+ *lemma* abs_le_of_le_of_neg_le
- \+ *lemma* abs_lt_of_lt_of_neg_lt
- \+ *lemma* abs_add_le_abs_add_abs
- \+ *lemma* abs_sub_abs_le_abs_sub
- \+ *lemma* abs_sub_le
- \+ *lemma* abs_add_three
- \+ *lemma* dist_bdd_within_interval
- \+ *lemma* decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
- \+/\- *lemma* add_le_iff_nonpos_left
- \+/\- *lemma* add_le_iff_nonpos_right
- \+/\- *lemma* add_lt_iff_neg_right
- \+/\- *lemma* add_lt_iff_neg_left
- \- *lemma* eq_of_abs_sub_nonpos
- \+ *theorem* add_lt_add_right
- \+/\- *def* ordered_add_comm_group.mk'
- \+ *def* abs
- \+/\- *def* ordered_add_comm_group.mk'

modified src/algebra/ordered_ring.lean
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \+ *lemma* mul_le_mul_of_nonneg_left
- \+ *lemma* mul_le_mul_of_nonneg_right
- \+ *lemma* mul_lt_mul_of_pos_left
- \+ *lemma* mul_lt_mul_of_pos_right
- \+ *lemma* mul_le_mul
- \+ *lemma* mul_nonneg
- \+/\- *lemma* mul_nonneg'
- \+ *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* mul_lt_mul
- \+ *lemma* mul_lt_mul'
- \+/\- *lemma* mul_pos
- \+/\- *lemma* mul_pos'
- \+ *lemma* mul_neg_of_pos_of_neg
- \+ *lemma* mul_neg_of_neg_of_pos
- \+ *lemma* mul_self_le_mul_self
- \+ *lemma* mul_self_lt_mul_self
- \+ *lemma* zero_lt_one
- \+ *lemma* zero_le_one
- \+ *lemma* two_pos
- \+ *lemma* two_ne_zero
- \+ *lemma* two_gt_one
- \+ *lemma* two_ge_one
- \+ *lemma* four_pos
- \+ *lemma* lt_of_mul_lt_mul_left
- \+ *lemma* lt_of_mul_lt_mul_right
- \+ *lemma* le_of_mul_le_mul_left
- \+ *lemma* le_of_mul_le_mul_right
- \+ *lemma* pos_of_mul_pos_left
- \+ *lemma* pos_of_mul_pos_right
- \+ *lemma* nonneg_of_mul_nonneg_left
- \+ *lemma* nonneg_of_mul_nonneg_right
- \+ *lemma* neg_of_mul_neg_left
- \+ *lemma* neg_of_mul_neg_right
- \+ *lemma* nonpos_of_mul_nonpos_left
- \+ *lemma* nonpos_of_mul_nonpos_right
- \+/\- *lemma* mul_le_mul_left
- \+/\- *lemma* mul_le_mul_right
- \+/\- *lemma* mul_lt_mul_left
- \+/\- *lemma* mul_lt_mul_right
- \+/\- *lemma* zero_le_mul_left
- \+/\- *lemma* zero_le_mul_right
- \+/\- *lemma* zero_lt_mul_left
- \+/\- *lemma* zero_lt_mul_right
- \+/\- *lemma* bit0_le_bit0
- \+/\- *lemma* bit0_lt_bit0
- \+/\- *lemma* bit1_le_bit1
- \+/\- *lemma* bit1_lt_bit1
- \+/\- *lemma* one_le_bit1
- \+/\- *lemma* one_lt_bit1
- \+/\- *lemma* zero_le_bit0
- \+/\- *lemma* zero_lt_bit0
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \+/\- *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* le_mul_of_one_le_left'
- \+/\- *lemma* bit1_pos
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+/\- *lemma* mul_lt_iff_lt_one_right
- \+/\- *lemma* nonpos_of_mul_nonneg_left
- \+/\- *lemma* nonpos_of_mul_nonneg_right
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+/\- *lemma* decidable.mul_le_mul_left
- \+/\- *lemma* decidable.mul_le_mul_right
- \+ *lemma* ordered_ring.mul_nonneg
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \+ *lemma* mul_le_mul_of_nonpos_left
- \+ *lemma* mul_le_mul_of_nonpos_right
- \+ *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* mul_lt_mul_of_neg_left
- \+ *lemma* mul_lt_mul_of_neg_right
- \+ *lemma* mul_pos_of_neg_of_neg
- \+ *lemma* mul_self_nonneg
- \+ *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* gt_of_mul_lt_mul_neg_left
- \+ *lemma* zero_gt_neg_one
- \+ *lemma* le_of_mul_le_of_ge_one
- \+ *lemma* nonneg_le_nonneg_of_squares_le
- \+ *lemma* mul_self_le_mul_self_iff
- \+ *lemma* mul_self_lt_mul_self_iff
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* abs_mul
- \+ *lemma* abs_mul_abs_self
- \+ *lemma* abs_mul_self
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right
- \+ *lemma* abs_sub_square
- \+ *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+/\- *lemma* abs_two
- \+/\- *lemma* mul_pos
- \+/\- *lemma* mul_nonneg'
- \+/\- *lemma* mul_pos'
- \+/\- *lemma* mul_le_mul_left
- \+/\- *lemma* mul_le_mul_right
- \+/\- *lemma* mul_lt_mul_left
- \+/\- *lemma* mul_lt_mul_right
- \+/\- *lemma* zero_le_mul_left
- \+/\- *lemma* zero_le_mul_right
- \+/\- *lemma* zero_lt_mul_left
- \+/\- *lemma* zero_lt_mul_right
- \+/\- *lemma* bit0_le_bit0
- \+/\- *lemma* bit0_lt_bit0
- \+/\- *lemma* bit1_le_bit1
- \+/\- *lemma* bit1_lt_bit1
- \+/\- *lemma* one_le_bit1
- \+/\- *lemma* one_lt_bit1
- \+/\- *lemma* zero_le_bit0
- \+/\- *lemma* zero_lt_bit0
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* le_mul_iff_one_le_left
- \+/\- *lemma* lt_mul_iff_one_lt_left
- \+/\- *lemma* le_mul_iff_one_le_right
- \+/\- *lemma* lt_mul_iff_one_lt_right
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \+/\- *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* le_mul_of_one_le_left'
- \+/\- *lemma* bit1_pos
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+/\- *lemma* mul_le_iff_le_one_left
- \+/\- *lemma* mul_lt_iff_lt_one_left
- \+/\- *lemma* mul_le_iff_le_one_right
- \+/\- *lemma* mul_lt_iff_lt_one_right
- \+/\- *lemma* nonpos_of_mul_nonneg_left
- \+/\- *lemma* nonpos_of_mul_nonneg_right
- \+/\- *lemma* neg_of_mul_pos_left
- \+/\- *lemma* neg_of_mul_pos_right
- \+/\- *lemma* decidable.mul_le_mul_left
- \+/\- *lemma* decidable.mul_le_mul_right
- \+/\- *lemma* abs_two
- \+/\- *lemma* mul_pos
- \- *lemma* coe_nat
- \- *lemma* nat_ne_top
- \- *lemma* top_ne_nat
- \- *lemma* add_one_le_of_lt
- \- *lemma* nat_induction
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos
- \+/\- *theorem* mul_nonneg_iff_right_nonneg_of_pos

modified src/algebra/ring.lean
- \+ *lemma* left_distrib
- \+ *lemma* right_distrib
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* zero_ne_one
- \+ *lemma* one_ne_zero
- \+ *lemma* one_add_one_eq_two
- \+ *lemma* ne_zero_of_mul_ne_zero_right
- \+ *lemma* ne_zero_of_mul_ne_zero_left
- \+ *lemma* distrib_three_right
- \+ *lemma* coe_mul_left
- \+ *lemma* mul_right_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* zero_dvd_iff
- \+ *lemma* ring.mul_zero
- \+ *lemma* ring.zero_mul
- \+ *lemma* neg_mul_eq_neg_mul
- \+ *lemma* neg_mul_eq_mul_neg
- \+ *lemma* neg_mul_eq_neg_mul_symm
- \+ *lemma* mul_neg_eq_neg_mul_symm
- \+ *lemma* neg_mul_neg
- \+ *lemma* neg_mul_comm
- \+ *lemma* mul_sub_left_distrib
- \+ *lemma* mul_sub_right_distrib
- \+ *lemma* mul_neg_one
- \+ *lemma* neg_one_mul
- \+ *lemma* mul_self_sub_mul_self_eq
- \+ *lemma* mul_self_sub_one_eq
- \+ *lemma* add_mul_self_eq
- \+ *lemma* dvd_neg
- \+ *lemma* neg_dvd
- \+/\- *lemma* dvd_add_self_left
- \+/\- *lemma* dvd_add_self_right
- \+/\- *lemma* Vieta_formula_quadratic
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *lemma* mul_self_eq_zero
- \+ *lemma* zero_eq_mul_self
- \+ *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero
- \+ *lemma* mul_ne_zero
- \+ *lemma* eq_of_mul_eq_mul_right
- \+ *lemma* eq_of_mul_eq_mul_left
- \+ *lemma* eq_zero_of_mul_eq_self_right
- \+ *lemma* eq_zero_of_mul_eq_self_left
- \+ *lemma* mul_self_eq_mul_self_iff
- \+ *lemma* mul_self_eq_one_iff
- \+ *lemma* units.inv_eq_self_iff
- \- *lemma* comp
- \+/\- *lemma* zero_dvd_iff
- \+/\- *lemma* dvd_add_self_left
- \+/\- *lemma* dvd_add_self_right
- \+/\- *lemma* Vieta_formula_quadratic
- \- *lemma* of_semiring
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* comp
- \- *lemma* coe_of
- \+/\- *lemma* id_apply
- \+ *theorem* two_mul
- \+ *theorem* dvd.intro
- \+ *theorem* dvd.intro_left
- \+ *theorem* exists_eq_mul_right_of_dvd
- \+ *theorem* dvd.elim
- \+ *theorem* exists_eq_mul_left_of_dvd
- \+ *theorem* dvd.elim_left
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_trans
- \+ *theorem* eq_zero_of_zero_dvd
- \+ *theorem* dvd_zero
- \+ *theorem* one_dvd
- \+ *theorem* dvd_mul_right
- \+ *theorem* dvd_mul_left
- \+ *theorem* dvd_mul_of_dvd_left
- \+ *theorem* dvd_mul_of_dvd_right
- \+ *theorem* mul_dvd_mul
- \+ *theorem* mul_dvd_mul_left
- \+ *theorem* mul_dvd_mul_right
- \+ *theorem* dvd_add
- \+ *theorem* dvd_of_mul_right_dvd
- \+ *theorem* dvd_of_mul_left_dvd
- \+ *theorem* neg_eq_neg_one_mul
- \+ *theorem* mul_add_eq_mul_add_iff_sub_mul_add_eq
- \+ *theorem* sub_mul_add_eq_of_mul_add_eq_mul_add
- \+ *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \+ *theorem* dvd_neg_of_dvd
- \+ *theorem* dvd_of_dvd_neg
- \+ *theorem* dvd_neg_iff_dvd
- \+ *theorem* neg_dvd_of_dvd
- \+ *theorem* dvd_of_neg_dvd
- \+ *theorem* neg_dvd_iff_dvd
- \+ *theorem* dvd_sub
- \+ *theorem* dvd_add_iff_left
- \+ *theorem* dvd_add_iff_right
- \+ *theorem* mul_self_sub_mul_self
- \+ *theorem* dvd_add_left
- \+ *theorem* dvd_add_right
- \+ *theorem* mul_eq_zero
- \+ *theorem* zero_eq_mul
- \+ *theorem* mul_ne_zero'
- \+ *theorem* domain.mul_left_inj
- \+ *theorem* domain.mul_right_inj
- \+ *theorem* eq_zero_of_mul_eq_self_right'
- \+ *theorem* eq_zero_of_mul_eq_self_left'
- \+ *theorem* mul_ne_zero_comm'
- \+ *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \+ *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \+ *theorem* mul_dvd_mul_iff_left
- \+ *theorem* mul_dvd_mul_iff_right
- \+ *def* mul_add
- \+ *def* add_mul
- \+ *def* mul_left
- \+ *def* mul_right
- \+ *def* dvd_of_mul_right_eq
- \+ *def* dvd_of_mul_left_eq
- \+ *def* dvd.trans
- \+ *def* mul_sub
- \+ *def* sub_mul
- \- *def* of

modified src/analysis/analytic/basic.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/convex/basic.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/control/applicative.lean

modified src/control/functor.lean

modified src/control/monad/writer.lean

modified src/control/traversable/basic.lean

modified src/control/traversable/instances.lean

modified src/control/traversable/lemmas.lean

modified src/data/array/lemmas.lean

modified src/data/complex/basic.lean

modified src/data/complex/exponential.lean

modified src/data/complex/module.lean

modified src/data/equiv/basic.lean

modified src/data/equiv/ring.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/fin.lean

modified src/data/hash_map.lean

modified src/data/int/basic.lean

modified src/data/list/basic.lean

modified src/data/list/defs.lean

modified src/data/monoid_algebra.lean

modified src/data/multiset.lean

modified src/data/nat/basic.lean
- \+ *theorem* units_eq_one
- \+ *theorem* add_units_eq_zero

modified src/data/nat/cast.lean
- \+ *lemma* inv_pos_of_nat
- \+ *lemma* one_div_pos_of_nat
- \+ *lemma* one_div_le_one_div
- \+ *lemma* one_div_lt_one_div
- \+ *lemma* coe_nat
- \+ *lemma* nat_ne_top
- \+ *lemma* top_ne_nat
- \+ *lemma* add_one_le_of_lt
- \+ *lemma* nat_induction

modified src/data/nat/multiplicity.lean

modified src/data/nat/pairing.lean

modified src/data/nat/sqrt.lean

modified src/data/num/lemmas.lean

modified src/data/padics/hensel.lean

modified src/data/padics/padic_numbers.lean

modified src/data/pnat/basic.lean
- \- *theorem* dvd_trans

modified src/data/pnat/xgcd.lean
- \+/\- *theorem* gcd_eq
- \+/\- *theorem* gcd_eq

modified src/data/polynomial.lean

modified src/data/rat/basic.lean

modified src/data/rat/meta_defs.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean
- \- *theorem* mul_pos

modified src/data/real/cau_seq_completion.lean

modified src/data/seq/computation.lean

modified src/data/vector2.lean

modified src/data/zsqrtd/basic.lean

created src/deprecated/field.lean
- \+ *lemma* map_ne_zero
- \+ *lemma* map_eq_zero
- \+ *lemma* map_inv
- \+ *lemma* map_div
- \+ *lemma* injective

modified src/deprecated/group.lean

created src/deprecated/ring.lean
- \+ *lemma* comp
- \+ *lemma* of_semiring
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* comp
- \+ *lemma* coe_of
- \+ *def* of

modified src/group_theory/eckmann_hilton.lean

modified src/group_theory/free_group.lean

modified src/group_theory/monoid_localization.lean

modified src/init_/algebra/default.lean

deleted src/init_/algebra/field.lean
- \- *lemma* division_def
- \- *lemma* inv_zero
- \- *lemma* div_zero
- \- *lemma* mul_inv_cancel
- \- *lemma* inv_mul_cancel
- \- *lemma* one_div_eq_inv
- \- *lemma* inv_eq_one_div
- \- *lemma* div_eq_mul_one_div
- \- *lemma* mul_one_div_cancel
- \- *lemma* one_div_mul_cancel
- \- *lemma* div_self
- \- *lemma* one_div_one
- \- *lemma* mul_div_assoc
- \- *lemma* one_div_ne_zero
- \- *lemma* ne_zero_of_one_div_ne_zero
- \- *lemma* inv_ne_zero
- \- *lemma* eq_zero_of_one_div_eq_zero
- \- *lemma* one_inv_eq
- \- *lemma* div_one
- \- *lemma* zero_div
- \- *lemma* division_ring.mul_ne_zero
- \- *lemma* mul_ne_zero_comm
- \- *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left
- \- *lemma* division_ring.one_div_mul_one_div
- \- *lemma* one_div_neg_one_eq_neg_one
- \- *lemma* one_div_neg_eq_neg_one_div
- \- *lemma* div_neg_eq_neg_div
- \- *lemma* neg_div
- \- *lemma* neg_div_neg_eq
- \- *lemma* one_div_one_div
- \- *lemma* inv_inv'
- \- *lemma* eq_of_one_div_eq_one_div
- \- *lemma* mul_inv'
- \- *lemma* one_div_div
- \- *lemma* div_helper
- \- *lemma* mul_div_cancel
- \- *lemma* div_mul_cancel
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_mul_left
- \- *lemma* mul_div_mul_right
- \- *lemma* div_add_div_same
- \- *lemma* div_sub_div_same
- \- *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \- *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \- *lemma* div_eq_one_iff_eq
- \- *lemma* eq_of_div_eq_one
- \- *lemma* eq_div_iff_mul_eq
- \- *lemma* eq_div_of_mul_eq
- \- *lemma* mul_eq_of_eq_div
- \- *lemma* add_div_eq_mul_add_div
- \- *lemma* mul_mul_div
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* one_div_mul_one_div
- \- *lemma* div_mul_right
- \- *lemma* mul_div_cancel_left
- \- *lemma* mul_div_cancel'
- \- *lemma* one_div_add_one_div
- \- *lemma* div_mul_div
- \- *lemma* mul_div_mul_left
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm
- \- *lemma* div_add_div
- \- *lemma* div_sub_div
- \- *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_div_div_div_eq
- \- *lemma* div_mul_eq_div_mul_one_div

deleted src/init_/algebra/functions.lean
- \- *lemma* min_add_add_left
- \- *lemma* min_add_add_right
- \- *lemma* max_add_add_left
- \- *lemma* max_add_add_right
- \- *lemma* max_neg_neg
- \- *lemma* min_eq_neg_max_neg_neg
- \- *lemma* min_neg_neg
- \- *lemma* max_eq_neg_min_neg_neg
- \- *lemma* abs_of_nonneg
- \- *lemma* abs_of_pos
- \- *lemma* abs_of_nonpos
- \- *lemma* abs_of_neg
- \- *lemma* abs_zero
- \- *lemma* abs_neg
- \- *lemma* abs_pos_of_pos
- \- *lemma* abs_pos_of_neg
- \- *lemma* abs_sub
- \- *lemma* ne_zero_of_abs_ne_zero
- \- *lemma* eq_zero_of_neg_eq
- \- *lemma* abs_nonneg
- \- *lemma* abs_abs
- \- *lemma* le_abs_self
- \- *lemma* neg_le_abs_self
- \- *lemma* eq_zero_of_abs_eq_zero
- \- *lemma* eq_of_abs_sub_eq_zero
- \- *lemma* abs_pos_of_ne_zero
- \- *lemma* abs_by_cases
- \- *lemma* abs_le_of_le_of_neg_le
- \- *lemma* abs_lt_of_lt_of_neg_lt
- \- *lemma* abs_add_le_abs_add_abs
- \- *lemma* abs_sub_abs_le_abs_sub
- \- *lemma* abs_sub_le
- \- *lemma* abs_add_three
- \- *lemma* dist_bdd_within_interval
- \- *lemma* abs_mul
- \- *lemma* abs_mul_abs_self
- \- *lemma* abs_mul_self
- \- *lemma* sub_le_of_abs_sub_le_left
- \- *lemma* sub_le_of_abs_sub_le_right
- \- *lemma* sub_lt_of_abs_sub_lt_left
- \- *lemma* sub_lt_of_abs_sub_lt_right
- \- *lemma* abs_sub_square
- \- *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \- *lemma* abs_abs_sub_abs_le_abs_sub
- \- *lemma* abs_div
- \- *lemma* abs_one_div

deleted src/init_/algebra/group.lean
- \- *lemma* mul_assoc
- \- *lemma* mul_comm
- \- *lemma* mul_left_comm
- \- *lemma* mul_right_comm
- \- *lemma* mul_left_cancel
- \- *lemma* mul_right_cancel
- \- *lemma* mul_left_cancel_iff
- \- *lemma* mul_right_cancel_iff
- \- *lemma* one_mul
- \- *lemma* mul_one
- \- *lemma* mul_left_inv
- \- *lemma* inv_mul_cancel_left
- \- *lemma* inv_mul_cancel_right
- \- *lemma* inv_eq_of_mul_eq_one
- \- *lemma* one_inv
- \- *lemma* inv_inv
- \- *lemma* mul_right_inv
- \- *lemma* inv_inj
- \- *lemma* group.mul_left_cancel
- \- *lemma* group.mul_right_cancel
- \- *lemma* mul_inv_cancel_left
- \- *lemma* mul_inv_cancel_right
- \- *lemma* mul_inv_rev
- \- *lemma* eq_inv_of_eq_inv
- \- *lemma* eq_inv_of_mul_eq_one
- \- *lemma* eq_mul_inv_of_mul_eq
- \- *lemma* eq_inv_mul_of_mul_eq
- \- *lemma* inv_mul_eq_of_eq_mul
- \- *lemma* mul_inv_eq_of_eq_mul
- \- *lemma* eq_mul_of_mul_inv_eq
- \- *lemma* eq_mul_of_inv_mul_eq
- \- *lemma* mul_eq_of_eq_inv_mul
- \- *lemma* mul_eq_of_eq_mul_inv
- \- *lemma* mul_inv
- \- *lemma* sub_eq_add_neg
- \- *lemma* sub_self
- \- *lemma* sub_add_cancel
- \- *lemma* add_sub_cancel
- \- *lemma* add_sub_assoc
- \- *lemma* eq_of_sub_eq_zero
- \- *lemma* sub_eq_zero_of_eq
- \- *lemma* sub_eq_zero_iff_eq
- \- *lemma* zero_sub
- \- *lemma* sub_zero
- \- *lemma* sub_ne_zero_of_ne
- \- *lemma* sub_neg_eq_add
- \- *lemma* neg_sub
- \- *lemma* add_sub
- \- *lemma* sub_add_eq_sub_sub_swap
- \- *lemma* add_sub_add_right_eq_sub
- \- *lemma* eq_sub_of_add_eq
- \- *lemma* sub_eq_of_eq_add
- \- *lemma* eq_add_of_sub_eq
- \- *lemma* add_eq_of_eq_sub
- \- *lemma* sub_add_eq_sub_sub
- \- *lemma* neg_add_eq_sub
- \- *lemma* sub_add_eq_add_sub
- \- *lemma* sub_sub
- \- *lemma* sub_add
- \- *lemma* add_sub_add_left_eq_sub
- \- *lemma* eq_sub_of_add_eq'
- \- *lemma* sub_eq_of_eq_add'
- \- *lemma* eq_add_of_sub_eq'
- \- *lemma* add_eq_of_eq_sub'
- \- *lemma* sub_sub_self
- \- *lemma* add_sub_comm
- \- *lemma* sub_eq_sub_add_sub
- \- *lemma* neg_neg_sub_neg
- \- *def* inv_mul_self
- \- *def* mul_inv_self
- \- *def* neg_add_self
- \- *def* add_neg_self
- \- *def* eq_of_add_eq_add_left
- \- *def* eq_of_add_eq_add_right

modified src/init_/algebra/norm_num.lean

deleted src/init_/algebra/ordered_field.lean
- \- *lemma* mul_zero_lt_mul_inv_of_pos
- \- *lemma* mul_zero_lt_mul_inv_of_neg
- \- *lemma* one_div_pos_of_pos
- \- *lemma* pos_of_one_div_pos
- \- *lemma* one_div_neg_of_neg
- \- *lemma* neg_of_one_div_neg
- \- *lemma* le_mul_of_ge_one_right
- \- *lemma* le_mul_of_ge_one_left
- \- *lemma* lt_mul_of_gt_one_right
- \- *lemma* one_le_div_of_le
- \- *lemma* le_of_one_le_div
- \- *lemma* one_lt_div_of_lt
- \- *lemma* lt_of_one_lt_div
- \- *lemma* mul_le_of_le_div
- \- *lemma* le_div_of_mul_le
- \- *lemma* mul_lt_of_lt_div
- \- *lemma* lt_div_of_mul_lt
- \- *lemma* mul_le_of_div_le_of_neg
- \- *lemma* div_le_of_mul_le_of_neg
- \- *lemma* mul_lt_of_gt_div_of_neg
- \- *lemma* div_lt_of_mul_lt_of_pos
- \- *lemma* div_lt_of_mul_gt_of_neg
- \- *lemma* div_le_of_le_mul
- \- *lemma* le_mul_of_div_le
- \- *lemma* mul_sub_mul_div_mul_neg
- \- *lemma* mul_sub_mul_div_mul_nonpos
- \- *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \- *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \- *lemma* div_pos_of_pos_of_pos
- \- *lemma* div_nonneg_of_nonneg_of_pos
- \- *lemma* div_neg_of_neg_of_pos
- \- *lemma* div_nonpos_of_nonpos_of_pos
- \- *lemma* div_neg_of_pos_of_neg
- \- *lemma* div_nonpos_of_nonneg_of_neg
- \- *lemma* div_pos_of_neg_of_neg
- \- *lemma* div_nonneg_of_nonpos_of_neg
- \- *lemma* div_lt_div_of_lt_of_pos
- \- *lemma* div_le_div_of_le_of_pos
- \- *lemma* div_lt_div_of_lt_of_neg
- \- *lemma* div_le_div_of_le_of_neg
- \- *lemma* add_halves
- \- *lemma* sub_self_div_two
- \- *lemma* add_midpoint
- \- *lemma* div_two_sub_self
- \- *lemma* add_self_div_two
- \- *lemma* mul_le_mul_of_mul_div_le
- \- *lemma* div_two_lt_of_pos
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \- *lemma* exists_add_lt_and_pos_of_lt
- \- *lemma* ge_of_forall_ge_sub
- \- *lemma* one_div_lt_one_div_of_lt
- \- *lemma* one_div_le_one_div_of_le
- \- *lemma* one_div_lt_one_div_of_lt_of_neg
- \- *lemma* one_div_le_one_div_of_le_of_neg
- \- *lemma* le_of_one_div_le_one_div
- \- *lemma* le_of_one_div_le_one_div_of_neg
- \- *lemma* lt_of_one_div_lt_one_div
- \- *lemma* lt_of_one_div_lt_one_div_of_neg
- \- *lemma* one_div_le_of_one_div_le_of_pos
- \- *lemma* one_div_le_of_one_div_le_of_neg
- \- *lemma* one_lt_one_div
- \- *lemma* one_le_one_div
- \- *lemma* one_div_lt_neg_one
- \- *lemma* one_div_le_neg_one
- \- *lemma* div_lt_div_of_pos_of_lt_of_pos
- \- *lemma* div_mul_le_div_mul_of_div_le_div_pos'

deleted src/init_/algebra/ordered_group.lean
- \- *lemma* add_le_add_left
- \- *lemma* le_of_add_le_add_left
- \- *lemma* add_lt_add_left
- \- *lemma* lt_of_add_lt_add_left
- \- *lemma* add_le_add_right
- \- *lemma* add_le_add
- \- *lemma* le_add_of_nonneg_right
- \- *lemma* le_add_of_nonneg_left
- \- *lemma* add_lt_add
- \- *lemma* add_lt_add_of_le_of_lt
- \- *lemma* add_lt_add_of_lt_of_le
- \- *lemma* lt_add_of_pos_right
- \- *lemma* lt_add_of_pos_left
- \- *lemma* le_of_add_le_add_right
- \- *lemma* lt_of_add_lt_add_right
- \- *lemma* add_nonneg
- \- *lemma* add_pos
- \- *lemma* add_pos_of_pos_of_nonneg
- \- *lemma* add_pos_of_nonneg_of_pos
- \- *lemma* add_nonpos
- \- *lemma* add_neg
- \- *lemma* add_neg_of_neg_of_nonpos
- \- *lemma* add_neg_of_nonpos_of_neg
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \- *lemma* le_add_of_nonneg_of_le
- \- *lemma* le_add_of_le_of_nonneg
- \- *lemma* lt_add_of_pos_of_le
- \- *lemma* lt_add_of_le_of_pos
- \- *lemma* add_le_of_nonpos_of_le
- \- *lemma* add_le_of_le_of_nonpos
- \- *lemma* add_lt_of_neg_of_le
- \- *lemma* add_lt_of_le_of_neg
- \- *lemma* lt_add_of_nonneg_of_lt
- \- *lemma* lt_add_of_lt_of_nonneg
- \- *lemma* lt_add_of_pos_of_lt
- \- *lemma* lt_add_of_lt_of_pos
- \- *lemma* add_lt_of_nonpos_of_lt
- \- *lemma* add_lt_of_lt_of_nonpos
- \- *lemma* add_lt_of_neg_of_lt
- \- *lemma* add_lt_of_lt_of_neg
- \- *lemma* ordered_add_comm_group.add_lt_add_left
- \- *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \- *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \- *lemma* neg_le_neg
- \- *lemma* le_of_neg_le_neg
- \- *lemma* nonneg_of_neg_nonpos
- \- *lemma* neg_nonpos_of_nonneg
- \- *lemma* nonpos_of_neg_nonneg
- \- *lemma* neg_nonneg_of_nonpos
- \- *lemma* neg_lt_neg
- \- *lemma* lt_of_neg_lt_neg
- \- *lemma* pos_of_neg_neg
- \- *lemma* neg_neg_of_pos
- \- *lemma* neg_of_neg_pos
- \- *lemma* neg_pos_of_neg
- \- *lemma* le_neg_of_le_neg
- \- *lemma* neg_le_of_neg_le
- \- *lemma* lt_neg_of_lt_neg
- \- *lemma* neg_lt_of_neg_lt
- \- *lemma* sub_nonneg_of_le
- \- *lemma* le_of_sub_nonneg
- \- *lemma* sub_nonpos_of_le
- \- *lemma* le_of_sub_nonpos
- \- *lemma* sub_pos_of_lt
- \- *lemma* lt_of_sub_pos
- \- *lemma* sub_neg_of_lt
- \- *lemma* lt_of_sub_neg
- \- *lemma* add_le_of_le_neg_add
- \- *lemma* le_neg_add_of_add_le
- \- *lemma* add_le_of_le_sub_left
- \- *lemma* le_sub_left_of_add_le
- \- *lemma* add_le_of_le_sub_right
- \- *lemma* le_sub_right_of_add_le
- \- *lemma* le_add_of_neg_add_le
- \- *lemma* neg_add_le_of_le_add
- \- *lemma* le_add_of_sub_left_le
- \- *lemma* sub_left_le_of_le_add
- \- *lemma* le_add_of_sub_right_le
- \- *lemma* sub_right_le_of_le_add
- \- *lemma* le_add_of_neg_add_le_left
- \- *lemma* neg_add_le_left_of_le_add
- \- *lemma* le_add_of_neg_add_le_right
- \- *lemma* neg_add_le_right_of_le_add
- \- *lemma* le_add_of_neg_le_sub_left
- \- *lemma* neg_le_sub_left_of_le_add
- \- *lemma* le_add_of_neg_le_sub_right
- \- *lemma* neg_le_sub_right_of_le_add
- \- *lemma* sub_le_of_sub_le
- \- *lemma* sub_le_sub_left
- \- *lemma* sub_le_sub_right
- \- *lemma* sub_le_sub
- \- *lemma* add_lt_of_lt_neg_add
- \- *lemma* lt_neg_add_of_add_lt
- \- *lemma* add_lt_of_lt_sub_left
- \- *lemma* lt_sub_left_of_add_lt
- \- *lemma* add_lt_of_lt_sub_right
- \- *lemma* lt_sub_right_of_add_lt
- \- *lemma* lt_add_of_neg_add_lt
- \- *lemma* neg_add_lt_of_lt_add
- \- *lemma* lt_add_of_sub_left_lt
- \- *lemma* sub_left_lt_of_lt_add
- \- *lemma* lt_add_of_sub_right_lt
- \- *lemma* sub_right_lt_of_lt_add
- \- *lemma* lt_add_of_neg_add_lt_left
- \- *lemma* neg_add_lt_left_of_lt_add
- \- *lemma* lt_add_of_neg_add_lt_right
- \- *lemma* neg_add_lt_right_of_lt_add
- \- *lemma* lt_add_of_neg_lt_sub_left
- \- *lemma* neg_lt_sub_left_of_lt_add
- \- *lemma* lt_add_of_neg_lt_sub_right
- \- *lemma* neg_lt_sub_right_of_lt_add
- \- *lemma* sub_lt_of_sub_lt
- \- *lemma* sub_lt_sub_left
- \- *lemma* sub_lt_sub_right
- \- *lemma* sub_lt_sub
- \- *lemma* sub_lt_sub_of_le_of_lt
- \- *lemma* sub_lt_sub_of_lt_of_le
- \- *lemma* sub_le_self
- \- *lemma* sub_lt_self
- \- *lemma* add_le_add_three
- \- *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \- *theorem* add_lt_add_right

deleted src/init_/algebra/ordered_ring.lean
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \- *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \- *lemma* mul_le_mul_of_nonneg_left
- \- *lemma* mul_le_mul_of_nonneg_right
- \- *lemma* mul_lt_mul_of_pos_left
- \- *lemma* mul_lt_mul_of_pos_right
- \- *lemma* mul_le_mul
- \- *lemma* mul_nonneg
- \- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \- *lemma* mul_lt_mul
- \- *lemma* mul_lt_mul'
- \- *lemma* mul_pos
- \- *lemma* mul_neg_of_pos_of_neg
- \- *lemma* mul_neg_of_neg_of_pos
- \- *lemma* mul_self_le_mul_self
- \- *lemma* mul_self_lt_mul_self
- \- *lemma* zero_lt_one
- \- *lemma* zero_le_one
- \- *lemma* two_pos
- \- *lemma* two_ne_zero
- \- *lemma* two_gt_one
- \- *lemma* two_ge_one
- \- *lemma* four_pos
- \- *lemma* lt_of_mul_lt_mul_left
- \- *lemma* lt_of_mul_lt_mul_right
- \- *lemma* le_of_mul_le_mul_left
- \- *lemma* le_of_mul_le_mul_right
- \- *lemma* pos_of_mul_pos_left
- \- *lemma* pos_of_mul_pos_right
- \- *lemma* nonneg_of_mul_nonneg_left
- \- *lemma* nonneg_of_mul_nonneg_right
- \- *lemma* neg_of_mul_neg_left
- \- *lemma* neg_of_mul_neg_right
- \- *lemma* nonpos_of_mul_nonpos_left
- \- *lemma* nonpos_of_mul_nonpos_right
- \- *lemma* ordered_ring.mul_nonneg
- \- *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \- *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \- *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \- *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \- *lemma* mul_le_mul_of_nonpos_left
- \- *lemma* mul_le_mul_of_nonpos_right
- \- *lemma* mul_nonneg_of_nonpos_of_nonpos
- \- *lemma* mul_lt_mul_of_neg_left
- \- *lemma* mul_lt_mul_of_neg_right
- \- *lemma* mul_pos_of_neg_of_neg
- \- *lemma* mul_self_nonneg
- \- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \- *lemma* gt_of_mul_lt_mul_neg_left
- \- *lemma* zero_gt_neg_one
- \- *lemma* le_of_mul_le_of_ge_one
- \- *lemma* nonneg_le_nonneg_of_squares_le
- \- *lemma* mul_self_le_mul_self_iff
- \- *lemma* mul_self_lt_mul_self_iff
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero

deleted src/init_/algebra/ring.lean
- \- *lemma* left_distrib
- \- *lemma* right_distrib
- \- *lemma* zero_mul
- \- *lemma* mul_zero
- \- *lemma* zero_ne_one
- \- *lemma* one_ne_zero
- \- *lemma* ring.mul_zero
- \- *lemma* ring.zero_mul
- \- *lemma* neg_mul_eq_neg_mul
- \- *lemma* neg_mul_eq_mul_neg
- \- *lemma* neg_mul_eq_neg_mul_symm
- \- *lemma* mul_neg_eq_neg_mul_symm
- \- *lemma* neg_mul_neg
- \- *lemma* neg_mul_comm
- \- *lemma* mul_sub_left_distrib
- \- *lemma* mul_sub_right_distrib
- \- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \- *lemma* eq_zero_of_mul_self_eq_zero
- \- *theorem* neg_eq_neg_one_mul
- \- *def* mul_add
- \- *def* add_mul
- \- *def* mul_sub
- \- *def* sub_mul

modified src/init_/data/int/basic.lean

modified src/init_/data/int/order.lean

modified src/init_/data/nat/lemmas.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/dual.lean
- \+/\- *def* coord_fun
- \+/\- *def* coord_fun

modified src/linear_algebra/multilinear.lean

modified src/linear_algebra/quadratic_form.lean

modified src/logic/basic.lean

modified src/measure_theory/outer_measure.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/number_theory/sum_four_squares.lean

modified src/order/filter/filter_product.lean

modified src/ring_theory/integral_domain.lean

modified src/set_theory/ordinal_notation.lean

modified src/tactic/abel.lean

modified src/tactic/algebra.lean

modified src/tactic/monotonicity/lemmas.lean

modified src/tactic/norm_num.lean
- \+ *lemma* subst_into_add
- \+ *lemma* subst_into_mul

modified src/tactic/ring.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/bounded_continuous_function.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/hausdorff_distance.lean

modified src/topology/metric_space/isometry.lean

modified test/coinductive.lean

modified test/finish4.lean
- \+/\- *def* append1
- \+/\- *def* append1

modified test/library_search/ordered_ring.lean

modified test/lint.lean

modified test/lint_simp_comm.lean

modified test/mk_iff_of_inductive.lean

modified test/monotonicity.lean

modified test/norm_cast_int.lean

modified test/norm_cast_lemma_order.lean

modified test/norm_num.lean

modified test/nth_rewrite.lean

modified test/push_neg.lean

modified test/refine_struct.lean

modified test/rewrite.lean

modified test/ring.lean

modified test/simp_rw.lean

modified test/tactics.lean



## [2020-05-18 13:38:39](https://github.com/leanprover-community/mathlib/commit/18217e9)
feat(nat/choose): Generalise nat.dvd_choose ([#2703](https://github.com/leanprover-community/mathlib/pull/2703))
Spin-off from [#2701](https://github.com/leanprover-community/mathlib/pull/2701).
#### Estimated changes
modified src/algebra/char_p.lean

modified src/data/nat/choose.lean
- \+ *lemma* nat.prime.dvd_choose_add
- \+ *lemma* nat.prime.dvd_choose_self
- \- *lemma* nat.prime.dvd_choose
- \+/\- *theorem* sum_range_choose
- \+/\- *theorem* sum_range_choose



## [2020-05-18 11:24:28](https://github.com/leanprover-community/mathlib/commit/434e6a6)
chore(*): update to lean 3.13.2 ([#2728](https://github.com/leanprover-community/mathlib/pull/2728))
This should fix the bug with the missing module doc strings in the documentation.
#### Estimated changes
modified leanpkg.toml



## [2020-05-17 23:39:12](https://github.com/leanprover-community/mathlib/commit/93119dd)
chore(scripts): update nolints.txt ([#2721](https://github.com/leanprover-community/mathlib/pull/2721))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-17 22:37:56](https://github.com/leanprover-community/mathlib/commit/7325104)
feat(ci): store xz archives ([#2719](https://github.com/leanprover-community/mathlib/pull/2719))
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/olean.20cache
#### Estimated changes
modified .github/workflows/build.yml



## [2020-05-17 20:01:37](https://github.com/leanprover-community/mathlib/commit/cdf97dc)
refactor(field_theory): preparations for Chevalley–Warning ([#2590](https://github.com/leanprover-community/mathlib/pull/2590))
This PR adds some preparations for the Chevalley–Warning theorem.
depends on: ~[#2606](https://github.com/leanprover-community/mathlib/pull/2606), [#2607](https://github.com/leanprover-community/mathlib/pull/2607), [#2623](https://github.com/leanprover-community/mathlib/pull/2623)~
#### Estimated changes
modified src/algebra/group/units.lean
- \+ *lemma* coe_val_hom
- \+ *def* val_hom

modified src/field_theory/finite.lean
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+ *lemma* cast_card_eq_zero
- \+ *lemma* forall_pow_eq_one_iff
- \+ *lemma* sum_pow_units
- \+ *lemma* sum_pow_lt_card_sub_one
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+/\- *theorem* card
- \+/\- *theorem* card'
- \+/\- *theorem* card
- \+/\- *theorem* card'
- \- *def* field_of_integral_domain

modified src/ring_theory/integral_domain.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+ *lemma* is_cyclic_of_subgroup_integral_domain
- \+/\- *lemma* card_fiber_eq_of_mem_range
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_fiber_eq_of_mem_range
- \+ *def* field_of_integral_domain



## [2020-05-17 17:58:04](https://github.com/leanprover-community/mathlib/commit/f23c361)
chore(*): bump to lean-3.13.1 ([#2697](https://github.com/leanprover-community/mathlib/pull/2697))
## Move algebra to mathlib
The algebraic hierarchy has moved from the core library to `init_`. In later PRs this can be integrated into the existing directory structure of mathlib.
#### Estimated changes
modified archive/imo1988_q6.lean

modified leanpkg.toml

modified scripts/nolints.txt

modified src/data/int/gcd.lean

created src/init_/algebra/default.lean

created src/init_/algebra/field.lean
- \+ *lemma* division_def
- \+ *lemma* inv_zero
- \+ *lemma* div_zero
- \+ *lemma* mul_inv_cancel
- \+ *lemma* inv_mul_cancel
- \+ *lemma* one_div_eq_inv
- \+ *lemma* inv_eq_one_div
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* mul_one_div_cancel
- \+ *lemma* one_div_mul_cancel
- \+ *lemma* div_self
- \+ *lemma* one_div_one
- \+ *lemma* mul_div_assoc
- \+ *lemma* one_div_ne_zero
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \+ *lemma* inv_ne_zero
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \+ *lemma* one_inv_eq
- \+ *lemma* div_one
- \+ *lemma* zero_div
- \+ *lemma* division_ring.mul_ne_zero
- \+ *lemma* mul_ne_zero_comm
- \+ *lemma* eq_one_div_of_mul_eq_one
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* division_ring.one_div_mul_one_div
- \+ *lemma* one_div_neg_one_eq_neg_one
- \+ *lemma* one_div_neg_eq_neg_one_div
- \+ *lemma* div_neg_eq_neg_div
- \+ *lemma* neg_div
- \+ *lemma* neg_div_neg_eq
- \+ *lemma* one_div_one_div
- \+ *lemma* inv_inv'
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* mul_inv'
- \+ *lemma* one_div_div
- \+ *lemma* div_helper
- \+ *lemma* mul_div_cancel
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_mul_left
- \+ *lemma* mul_div_mul_right
- \+ *lemma* div_add_div_same
- \+ *lemma* div_sub_div_same
- \+ *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
- \+ *lemma* div_eq_one_iff_eq
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* eq_div_iff_mul_eq
- \+ *lemma* eq_div_of_mul_eq
- \+ *lemma* mul_eq_of_eq_div
- \+ *lemma* add_div_eq_mul_add_div
- \+ *lemma* mul_mul_div
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* div_mul_right
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_cancel'
- \+ *lemma* one_div_add_one_div
- \+ *lemma* div_mul_div
- \+ *lemma* mul_div_mul_left
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* div_mul_eq_mul_div_comm
- \+ *lemma* div_add_div
- \+ *lemma* div_sub_div
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_div_div_div_eq
- \+ *lemma* div_mul_eq_div_mul_one_div

created src/init_/algebra/functions.lean
- \+ *lemma* min_add_add_left
- \+ *lemma* min_add_add_right
- \+ *lemma* max_add_add_left
- \+ *lemma* max_add_add_right
- \+ *lemma* max_neg_neg
- \+ *lemma* min_eq_neg_max_neg_neg
- \+ *lemma* min_neg_neg
- \+ *lemma* max_eq_neg_min_neg_neg
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_of_pos
- \+ *lemma* abs_of_nonpos
- \+ *lemma* abs_of_neg
- \+ *lemma* abs_zero
- \+ *lemma* abs_neg
- \+ *lemma* abs_pos_of_pos
- \+ *lemma* abs_pos_of_neg
- \+ *lemma* abs_sub
- \+ *lemma* ne_zero_of_abs_ne_zero
- \+ *lemma* eq_zero_of_neg_eq
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_abs
- \+ *lemma* le_abs_self
- \+ *lemma* neg_le_abs_self
- \+ *lemma* eq_zero_of_abs_eq_zero
- \+ *lemma* eq_of_abs_sub_eq_zero
- \+ *lemma* abs_pos_of_ne_zero
- \+ *lemma* abs_by_cases
- \+ *lemma* abs_le_of_le_of_neg_le
- \+ *lemma* abs_lt_of_lt_of_neg_lt
- \+ *lemma* abs_add_le_abs_add_abs
- \+ *lemma* abs_sub_abs_le_abs_sub
- \+ *lemma* abs_sub_le
- \+ *lemma* abs_add_three
- \+ *lemma* dist_bdd_within_interval
- \+ *lemma* abs_mul
- \+ *lemma* abs_mul_abs_self
- \+ *lemma* abs_mul_self
- \+ *lemma* sub_le_of_abs_sub_le_left
- \+ *lemma* sub_le_of_abs_sub_le_right
- \+ *lemma* sub_lt_of_abs_sub_lt_left
- \+ *lemma* sub_lt_of_abs_sub_lt_right
- \+ *lemma* abs_sub_square
- \+ *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *lemma* abs_div
- \+ *lemma* abs_one_div

created src/init_/algebra/group.lean
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_left_comm
- \+ *lemma* mul_right_comm
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *lemma* mul_right_cancel_iff
- \+ *lemma* one_mul
- \+ *lemma* mul_one
- \+ *lemma* mul_left_inv
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_cancel_right
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* one_inv
- \+ *lemma* inv_inv
- \+ *lemma* mul_right_inv
- \+ *lemma* inv_inj
- \+ *lemma* group.mul_left_cancel
- \+ *lemma* group.mul_right_cancel
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_rev
- \+ *lemma* eq_inv_of_eq_inv
- \+ *lemma* eq_inv_of_mul_eq_one
- \+ *lemma* eq_mul_inv_of_mul_eq
- \+ *lemma* eq_inv_mul_of_mul_eq
- \+ *lemma* inv_mul_eq_of_eq_mul
- \+ *lemma* mul_inv_eq_of_eq_mul
- \+ *lemma* eq_mul_of_mul_inv_eq
- \+ *lemma* eq_mul_of_inv_mul_eq
- \+ *lemma* mul_eq_of_eq_inv_mul
- \+ *lemma* mul_eq_of_eq_mul_inv
- \+ *lemma* mul_inv
- \+ *lemma* sub_eq_add_neg
- \+ *lemma* sub_self
- \+ *lemma* sub_add_cancel
- \+ *lemma* add_sub_cancel
- \+ *lemma* add_sub_assoc
- \+ *lemma* eq_of_sub_eq_zero
- \+ *lemma* sub_eq_zero_of_eq
- \+ *lemma* sub_eq_zero_iff_eq
- \+ *lemma* zero_sub
- \+ *lemma* sub_zero
- \+ *lemma* sub_ne_zero_of_ne
- \+ *lemma* sub_neg_eq_add
- \+ *lemma* neg_sub
- \+ *lemma* add_sub
- \+ *lemma* sub_add_eq_sub_sub_swap
- \+ *lemma* add_sub_add_right_eq_sub
- \+ *lemma* eq_sub_of_add_eq
- \+ *lemma* sub_eq_of_eq_add
- \+ *lemma* eq_add_of_sub_eq
- \+ *lemma* add_eq_of_eq_sub
- \+ *lemma* sub_add_eq_sub_sub
- \+ *lemma* neg_add_eq_sub
- \+ *lemma* sub_add_eq_add_sub
- \+ *lemma* sub_sub
- \+ *lemma* sub_add
- \+ *lemma* add_sub_add_left_eq_sub
- \+ *lemma* eq_sub_of_add_eq'
- \+ *lemma* sub_eq_of_eq_add'
- \+ *lemma* eq_add_of_sub_eq'
- \+ *lemma* add_eq_of_eq_sub'
- \+ *lemma* sub_sub_self
- \+ *lemma* add_sub_comm
- \+ *lemma* sub_eq_sub_add_sub
- \+ *lemma* neg_neg_sub_neg
- \+ *def* inv_mul_self
- \+ *def* mul_inv_self
- \+ *def* neg_add_self
- \+ *def* add_neg_self
- \+ *def* eq_of_add_eq_add_left
- \+ *def* eq_of_add_eq_add_right

created src/init_/algebra/norm_num.lean
- \+ *lemma* mul_zero
- \+ *lemma* zero_mul
- \+ *lemma* mul_one
- \+ *lemma* mul_bit0
- \+ *lemma* mul_bit0_helper
- \+ *lemma* mul_bit1
- \+ *lemma* mul_bit1_helper
- \+ *lemma* subst_into_prod
- \+ *lemma* mk_cong
- \+ *lemma* neg_add_neg_eq_of_add_add_eq_zero
- \+ *lemma* neg_add_neg_helper
- \+ *lemma* neg_add_pos_eq_of_eq_add
- \+ *lemma* neg_add_pos_helper1
- \+ *lemma* neg_add_pos_helper2
- \+ *lemma* pos_add_neg_helper
- \+ *lemma* subst_into_subtr
- \+ *lemma* neg_neg_helper
- \+ *lemma* neg_mul_neg_helper
- \+ *lemma* neg_mul_pos_helper
- \+ *lemma* pos_mul_neg_helper
- \+ *lemma* div_add_helper
- \+ *lemma* add_div_helper
- \+ *lemma* div_mul_helper
- \+ *lemma* mul_div_helper
- \+ *lemma* nonzero_of_div_helper
- \+ *lemma* div_helper
- \+ *lemma* div_eq_div_helper
- \+ *lemma* subst_into_div
- \+ *lemma* add_comm_four
- \+ *lemma* add_comm_middle
- \+ *lemma* bit0_add_bit0
- \+ *lemma* bit0_add_bit0_helper
- \+ *lemma* bit1_add_bit0
- \+ *lemma* bit1_add_bit0_helper
- \+ *lemma* bit0_add_bit1
- \+ *lemma* bit0_add_bit1_helper
- \+ *lemma* bit1_add_bit1
- \+ *lemma* bit1_add_bit1_helper
- \+ *lemma* bin_add_zero
- \+ *lemma* bin_zero_add
- \+ *lemma* one_add_bit0
- \+ *lemma* bit0_add_one
- \+ *lemma* bit1_add_one
- \+ *lemma* bit1_add_one_helper
- \+ *lemma* one_add_bit1
- \+ *lemma* one_add_bit1_helper
- \+ *lemma* add1_bit0
- \+ *lemma* add1_bit1
- \+ *lemma* add1_bit1_helper
- \+ *lemma* add1_one
- \+ *lemma* add1_zero
- \+ *lemma* one_add_one
- \+ *lemma* subst_into_sum
- \+ *lemma* neg_zero_helper
- \+ *lemma* pos_bit0_helper
- \+ *lemma* nonneg_bit0_helper
- \+ *lemma* pos_bit1_helper
- \+ *lemma* nonneg_bit1_helper
- \+ *lemma* nonzero_of_pos_helper
- \+ *lemma* nonzero_of_neg_helper
- \+ *lemma* sub_nat_zero_helper
- \+ *lemma* sub_nat_pos_helper
- \+ *def* add1

created src/init_/algebra/ordered_field.lean
- \+ *lemma* mul_zero_lt_mul_inv_of_pos
- \+ *lemma* mul_zero_lt_mul_inv_of_neg
- \+ *lemma* one_div_pos_of_pos
- \+ *lemma* pos_of_one_div_pos
- \+ *lemma* one_div_neg_of_neg
- \+ *lemma* neg_of_one_div_neg
- \+ *lemma* le_mul_of_ge_one_right
- \+ *lemma* le_mul_of_ge_one_left
- \+ *lemma* lt_mul_of_gt_one_right
- \+ *lemma* one_le_div_of_le
- \+ *lemma* le_of_one_le_div
- \+ *lemma* one_lt_div_of_lt
- \+ *lemma* lt_of_one_lt_div
- \+ *lemma* mul_le_of_le_div
- \+ *lemma* le_div_of_mul_le
- \+ *lemma* mul_lt_of_lt_div
- \+ *lemma* lt_div_of_mul_lt
- \+ *lemma* mul_le_of_div_le_of_neg
- \+ *lemma* div_le_of_mul_le_of_neg
- \+ *lemma* mul_lt_of_gt_div_of_neg
- \+ *lemma* div_lt_of_mul_lt_of_pos
- \+ *lemma* div_lt_of_mul_gt_of_neg
- \+ *lemma* div_le_of_le_mul
- \+ *lemma* le_mul_of_div_le
- \+ *lemma* mul_sub_mul_div_mul_neg
- \+ *lemma* mul_sub_mul_div_mul_nonpos
- \+ *lemma* div_lt_div_of_mul_sub_mul_div_neg
- \+ *lemma* div_le_div_of_mul_sub_mul_div_nonpos
- \+ *lemma* div_pos_of_pos_of_pos
- \+ *lemma* div_nonneg_of_nonneg_of_pos
- \+ *lemma* div_neg_of_neg_of_pos
- \+ *lemma* div_nonpos_of_nonpos_of_pos
- \+ *lemma* div_neg_of_pos_of_neg
- \+ *lemma* div_nonpos_of_nonneg_of_neg
- \+ *lemma* div_pos_of_neg_of_neg
- \+ *lemma* div_nonneg_of_nonpos_of_neg
- \+ *lemma* div_lt_div_of_lt_of_pos
- \+ *lemma* div_le_div_of_le_of_pos
- \+ *lemma* div_lt_div_of_lt_of_neg
- \+ *lemma* div_le_div_of_le_of_neg
- \+ *lemma* add_halves
- \+ *lemma* sub_self_div_two
- \+ *lemma* add_midpoint
- \+ *lemma* div_two_sub_self
- \+ *lemma* add_self_div_two
- \+ *lemma* mul_le_mul_of_mul_div_le
- \+ *lemma* div_two_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos
- \+ *lemma* exists_add_lt_and_pos_of_lt
- \+ *lemma* ge_of_forall_ge_sub
- \+ *lemma* one_div_lt_one_div_of_lt
- \+ *lemma* one_div_le_one_div_of_le
- \+ *lemma* one_div_lt_one_div_of_lt_of_neg
- \+ *lemma* one_div_le_one_div_of_le_of_neg
- \+ *lemma* le_of_one_div_le_one_div
- \+ *lemma* le_of_one_div_le_one_div_of_neg
- \+ *lemma* lt_of_one_div_lt_one_div
- \+ *lemma* lt_of_one_div_lt_one_div_of_neg
- \+ *lemma* one_div_le_of_one_div_le_of_pos
- \+ *lemma* one_div_le_of_one_div_le_of_neg
- \+ *lemma* one_lt_one_div
- \+ *lemma* one_le_one_div
- \+ *lemma* one_div_lt_neg_one
- \+ *lemma* one_div_le_neg_one
- \+ *lemma* div_lt_div_of_pos_of_lt_of_pos
- \+ *lemma* div_mul_le_div_mul_of_div_le_div_pos'

created src/init_/algebra/ordered_group.lean
- \+ *lemma* add_le_add_left
- \+ *lemma* le_of_add_le_add_left
- \+ *lemma* add_lt_add_left
- \+ *lemma* lt_of_add_lt_add_left
- \+ *lemma* add_le_add_right
- \+ *lemma* add_le_add
- \+ *lemma* le_add_of_nonneg_right
- \+ *lemma* le_add_of_nonneg_left
- \+ *lemma* add_lt_add
- \+ *lemma* add_lt_add_of_le_of_lt
- \+ *lemma* add_lt_add_of_lt_of_le
- \+ *lemma* lt_add_of_pos_right
- \+ *lemma* lt_add_of_pos_left
- \+ *lemma* le_of_add_le_add_right
- \+ *lemma* lt_of_add_lt_add_right
- \+ *lemma* add_nonneg
- \+ *lemma* add_pos
- \+ *lemma* add_pos_of_pos_of_nonneg
- \+ *lemma* add_pos_of_nonneg_of_pos
- \+ *lemma* add_nonpos
- \+ *lemma* add_neg
- \+ *lemma* add_neg_of_neg_of_nonpos
- \+ *lemma* add_neg_of_nonpos_of_neg
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \+ *lemma* le_add_of_nonneg_of_le
- \+ *lemma* le_add_of_le_of_nonneg
- \+ *lemma* lt_add_of_pos_of_le
- \+ *lemma* lt_add_of_le_of_pos
- \+ *lemma* add_le_of_nonpos_of_le
- \+ *lemma* add_le_of_le_of_nonpos
- \+ *lemma* add_lt_of_neg_of_le
- \+ *lemma* add_lt_of_le_of_neg
- \+ *lemma* lt_add_of_nonneg_of_lt
- \+ *lemma* lt_add_of_lt_of_nonneg
- \+ *lemma* lt_add_of_pos_of_lt
- \+ *lemma* lt_add_of_lt_of_pos
- \+ *lemma* add_lt_of_nonpos_of_lt
- \+ *lemma* add_lt_of_lt_of_nonpos
- \+ *lemma* add_lt_of_neg_of_lt
- \+ *lemma* add_lt_of_lt_of_neg
- \+ *lemma* ordered_add_comm_group.add_lt_add_left
- \+ *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \+ *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \+ *lemma* neg_le_neg
- \+ *lemma* le_of_neg_le_neg
- \+ *lemma* nonneg_of_neg_nonpos
- \+ *lemma* neg_nonpos_of_nonneg
- \+ *lemma* nonpos_of_neg_nonneg
- \+ *lemma* neg_nonneg_of_nonpos
- \+ *lemma* neg_lt_neg
- \+ *lemma* lt_of_neg_lt_neg
- \+ *lemma* pos_of_neg_neg
- \+ *lemma* neg_neg_of_pos
- \+ *lemma* neg_of_neg_pos
- \+ *lemma* neg_pos_of_neg
- \+ *lemma* le_neg_of_le_neg
- \+ *lemma* neg_le_of_neg_le
- \+ *lemma* lt_neg_of_lt_neg
- \+ *lemma* neg_lt_of_neg_lt
- \+ *lemma* sub_nonneg_of_le
- \+ *lemma* le_of_sub_nonneg
- \+ *lemma* sub_nonpos_of_le
- \+ *lemma* le_of_sub_nonpos
- \+ *lemma* sub_pos_of_lt
- \+ *lemma* lt_of_sub_pos
- \+ *lemma* sub_neg_of_lt
- \+ *lemma* lt_of_sub_neg
- \+ *lemma* add_le_of_le_neg_add
- \+ *lemma* le_neg_add_of_add_le
- \+ *lemma* add_le_of_le_sub_left
- \+ *lemma* le_sub_left_of_add_le
- \+ *lemma* add_le_of_le_sub_right
- \+ *lemma* le_sub_right_of_add_le
- \+ *lemma* le_add_of_neg_add_le
- \+ *lemma* neg_add_le_of_le_add
- \+ *lemma* le_add_of_sub_left_le
- \+ *lemma* sub_left_le_of_le_add
- \+ *lemma* le_add_of_sub_right_le
- \+ *lemma* sub_right_le_of_le_add
- \+ *lemma* le_add_of_neg_add_le_left
- \+ *lemma* neg_add_le_left_of_le_add
- \+ *lemma* le_add_of_neg_add_le_right
- \+ *lemma* neg_add_le_right_of_le_add
- \+ *lemma* le_add_of_neg_le_sub_left
- \+ *lemma* neg_le_sub_left_of_le_add
- \+ *lemma* le_add_of_neg_le_sub_right
- \+ *lemma* neg_le_sub_right_of_le_add
- \+ *lemma* sub_le_of_sub_le
- \+ *lemma* sub_le_sub_left
- \+ *lemma* sub_le_sub_right
- \+ *lemma* sub_le_sub
- \+ *lemma* add_lt_of_lt_neg_add
- \+ *lemma* lt_neg_add_of_add_lt
- \+ *lemma* add_lt_of_lt_sub_left
- \+ *lemma* lt_sub_left_of_add_lt
- \+ *lemma* add_lt_of_lt_sub_right
- \+ *lemma* lt_sub_right_of_add_lt
- \+ *lemma* lt_add_of_neg_add_lt
- \+ *lemma* neg_add_lt_of_lt_add
- \+ *lemma* lt_add_of_sub_left_lt
- \+ *lemma* sub_left_lt_of_lt_add
- \+ *lemma* lt_add_of_sub_right_lt
- \+ *lemma* sub_right_lt_of_lt_add
- \+ *lemma* lt_add_of_neg_add_lt_left
- \+ *lemma* neg_add_lt_left_of_lt_add
- \+ *lemma* lt_add_of_neg_add_lt_right
- \+ *lemma* neg_add_lt_right_of_lt_add
- \+ *lemma* lt_add_of_neg_lt_sub_left
- \+ *lemma* neg_lt_sub_left_of_lt_add
- \+ *lemma* lt_add_of_neg_lt_sub_right
- \+ *lemma* neg_lt_sub_right_of_lt_add
- \+ *lemma* sub_lt_of_sub_lt
- \+ *lemma* sub_lt_sub_left
- \+ *lemma* sub_lt_sub_right
- \+ *lemma* sub_lt_sub
- \+ *lemma* sub_lt_sub_of_le_of_lt
- \+ *lemma* sub_lt_sub_of_lt_of_le
- \+ *lemma* sub_le_self
- \+ *lemma* sub_lt_self
- \+ *lemma* add_le_add_three
- \+ *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+ *theorem* add_lt_add_right

created src/init_/algebra/ordered_ring.lean
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_semiring.mul_le_mul_of_nonneg_right
- \+ *lemma* mul_le_mul_of_nonneg_left
- \+ *lemma* mul_le_mul_of_nonneg_right
- \+ *lemma* mul_lt_mul_of_pos_left
- \+ *lemma* mul_lt_mul_of_pos_right
- \+ *lemma* mul_le_mul
- \+ *lemma* mul_nonneg
- \+ *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* mul_lt_mul
- \+ *lemma* mul_lt_mul'
- \+ *lemma* mul_pos
- \+ *lemma* mul_neg_of_pos_of_neg
- \+ *lemma* mul_neg_of_neg_of_pos
- \+ *lemma* mul_self_le_mul_self
- \+ *lemma* mul_self_lt_mul_self
- \+ *lemma* zero_lt_one
- \+ *lemma* zero_le_one
- \+ *lemma* two_pos
- \+ *lemma* two_ne_zero
- \+ *lemma* two_gt_one
- \+ *lemma* two_ge_one
- \+ *lemma* four_pos
- \+ *lemma* lt_of_mul_lt_mul_left
- \+ *lemma* lt_of_mul_lt_mul_right
- \+ *lemma* le_of_mul_le_mul_left
- \+ *lemma* le_of_mul_le_mul_right
- \+ *lemma* pos_of_mul_pos_left
- \+ *lemma* pos_of_mul_pos_right
- \+ *lemma* nonneg_of_mul_nonneg_left
- \+ *lemma* nonneg_of_mul_nonneg_right
- \+ *lemma* neg_of_mul_neg_left
- \+ *lemma* neg_of_mul_neg_right
- \+ *lemma* nonpos_of_mul_nonpos_left
- \+ *lemma* nonpos_of_mul_nonpos_right
- \+ *lemma* ordered_ring.mul_nonneg
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_left
- \+ *lemma* ordered_ring.mul_le_mul_of_nonneg_right
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_left
- \+ *lemma* ordered_ring.mul_lt_mul_of_pos_right
- \+ *lemma* mul_le_mul_of_nonpos_left
- \+ *lemma* mul_le_mul_of_nonpos_right
- \+ *lemma* mul_nonneg_of_nonpos_of_nonpos
- \+ *lemma* mul_lt_mul_of_neg_left
- \+ *lemma* mul_lt_mul_of_neg_right
- \+ *lemma* mul_pos_of_neg_of_neg
- \+ *lemma* mul_self_nonneg
- \+ *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* gt_of_mul_lt_mul_neg_left
- \+ *lemma* zero_gt_neg_one
- \+ *lemma* le_of_mul_le_of_ge_one
- \+ *lemma* nonneg_le_nonneg_of_squares_le
- \+ *lemma* mul_self_le_mul_self_iff
- \+ *lemma* mul_self_lt_mul_self_iff
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero

created src/init_/algebra/ring.lean
- \+ *lemma* left_distrib
- \+ *lemma* right_distrib
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* zero_ne_one
- \+ *lemma* one_ne_zero
- \+ *lemma* ring.mul_zero
- \+ *lemma* ring.zero_mul
- \+ *lemma* neg_mul_eq_neg_mul
- \+ *lemma* neg_mul_eq_mul_neg
- \+ *lemma* neg_mul_eq_neg_mul_symm
- \+ *lemma* mul_neg_eq_neg_mul_symm
- \+ *lemma* neg_mul_neg
- \+ *lemma* neg_mul_comm
- \+ *lemma* mul_sub_left_distrib
- \+ *lemma* mul_sub_right_distrib
- \+ *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *theorem* neg_eq_neg_one_mul
- \+ *def* mul_add
- \+ *def* add_mul
- \+ *def* mul_sub
- \+ *def* sub_mul

created src/init_/data/int/basic.lean

created src/init_/data/int/order.lean
- \+ *theorem* abs_eq_nat_abs
- \+ *theorem* nat_abs_abs
- \+ *theorem* sign_mul_abs

created src/init_/data/nat/lemmas.lean
- \+ *theorem* mul_self_le_mul_self
- \+ *theorem* mul_self_lt_mul_self
- \+ *theorem* mul_self_le_mul_self_iff
- \+ *theorem* mul_self_lt_mul_self_iff
- \+ *theorem* le_mul_self
- \+ *theorem* eq_of_mul_eq_mul_right
- \+ *theorem* one_add

created src/init_/default.lean

modified src/logic/basic.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/simps.lean

modified test/doc_commands.lean



## [2020-05-17 15:08:29](https://github.com/leanprover-community/mathlib/commit/3449510)
feat(algebra/big_operators): Alternative phrasing of prod-bij ([#2709](https://github.com/leanprover-community/mathlib/pull/2709))
Requested by @ChrisHughes24 in https://github.com/leanprover-community/mathlib/pull/2688/files#r426184248
A repaired version of [#2708](https://github.com/leanprover-community/mathlib/pull/2708).
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* prod_bij'



## [2020-05-17 12:00:04](https://github.com/leanprover-community/mathlib/commit/a206df1)
chore(scripts): update nolints.txt ([#2711](https://github.com/leanprover-community/mathlib/pull/2711))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-17 07:42:04](https://github.com/leanprover-community/mathlib/commit/b530cdb)
refactor(normed_space): require `norm_smul_le` instead of `norm_smul` ([#2693](https://github.com/leanprover-community/mathlib/pull/2693))
While in many cases we can prove `norm_smul` directly, in some cases (e.g., for the operator norm) it's easier to prove `norm_smul_le`. Redefine `normed_space` to avoid repeating the same trick over and over.
#### Estimated changes
modified src/algebra/module.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* prod.norm_def

modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* norm_def
- \+ *lemma* op_norm_smul_le
- \+/\- *lemma* op_norm_neg
- \- *lemma* op_norm_smul
- \+/\- *lemma* op_norm_neg

modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* norm_def
- \+ *lemma* op_norm_smul_le
- \+/\- *lemma* op_norm_neg
- \- *lemma* op_norm_smul
- \+/\- *lemma* op_norm_neg
- \+/\- *def* op_norm
- \+/\- *def* op_norm

modified src/analysis/normed_space/real_inner_product.lean

modified src/group_theory/group_action.lean
- \+ *lemma* units.inv_smul_smul
- \+ *lemma* units.smul_inv_smul
- \+ *lemma* inv_smul_smul'
- \+ *lemma* smul_inv_smul'
- \+ *lemma* inv_smul_smul
- \+ *lemma* smul_inv_smul
- \+ *theorem* units.smul_eq_zero
- \+ *theorem* units.smul_ne_zero
- \+ *theorem* is_unit.smul_eq_zero

modified src/measure_theory/l1_space.lean

modified src/topology/bounded_continuous_function.lean
- \+ *lemma* ext_iff
- \+ *lemma* coe_const
- \+ *lemma* const_apply
- \+/\- *lemma* norm_eq
- \+ *lemma* dist_le_two_norm'
- \+/\- *lemma* dist_le_two_norm
- \+ *lemma* norm_const_le
- \+ *lemma* norm_const_eq
- \+ *lemma* norm_of_normed_group_le
- \+/\- *lemma* coe_add
- \+ *lemma* add_apply
- \+/\- *lemma* coe_neg
- \+ *lemma* neg_apply
- \+ *lemma* coe_sub
- \+ *lemma* sub_apply
- \+/\- *lemma* abs_diff_coe_le_dist
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+/\- *lemma* dist_le_two_norm
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \- *lemma* coe_diff
- \+/\- *lemma* abs_diff_coe_le_dist
- \+/\- *lemma* norm_eq
- \- *lemma* norm_smul_le
- \- *lemma* norm_smul
- \+/\- *def* of_normed_group
- \+/\- *def* of_normed_group_discrete
- \+/\- *def* of_normed_group
- \+/\- *def* of_normed_group_discrete

modified src/topology/metric_space/isometry.lean



## [2020-05-17 04:33:06](https://github.com/leanprover-community/mathlib/commit/39af0f6)
chore(algebra/ring): drop an unneeded instance ([#2705](https://github.com/leanprover-community/mathlib/pull/2705))
We're incompatible with Lean 3.4.2 for a long time.
#### Estimated changes
modified src/algebra/ring.lean
- \- *def* has_div_of_division_ring

modified src/order/filter/filter_product.lean



## [2020-05-17 02:07:24](https://github.com/leanprover-community/mathlib/commit/1580cd8)
fix(algebra/big_operators): typo fix ([#2704](https://github.com/leanprover-community/mathlib/pull/2704))
Fix cut-and-paste typos in the doc string for `∑ x, f x`.
#### Estimated changes
modified src/algebra/big_operators.lean



## [2020-05-17 02:07:22](https://github.com/leanprover-community/mathlib/commit/4f484a1)
feat(archive/100-theorems-list): Sum of the Reciprocals of the Triangular Numbers ([#2692](https://github.com/leanprover-community/mathlib/pull/2692))
Adds a folder `archive/100-theorems-list`, moves our proof of 82 into it, and provides a proof of 42. There's a readme, I haven't really thought about what should go in there.
#### Estimated changes
created archive/100-theorems-list/42_inverse_triangle_sum.lean
- \+ *lemma* inverse_triangle_sum

renamed archive/cubing_a_cube.lean to archive/100-theorems-list/82_cubing_a_cube.lean

created archive/100-theorems-list/README.md

modified src/algebra/big_operators.lean
- \+ *lemma* prod_range_induction
- \+ *lemma* sum_range_induction
- \+/\- *lemma* sum_range_sub_of_monotone
- \+/\- *lemma* sum_range_id_mul_two
- \+/\- *lemma* sum_range_sub_of_monotone
- \+/\- *lemma* sum_range_id_mul_two



## [2020-05-17 00:07:54](https://github.com/leanprover-community/mathlib/commit/21bdb78)
feat(ring_theory/ideal_operations): jacobson radical, is_local, and primary ideals ([#768](https://github.com/leanprover-community/mathlib/pull/768))
#### Estimated changes
modified src/ring_theory/ideal_operations.lean
- \+ *theorem* is_prime.comap
- \+ *theorem* jacobson_eq_top_iff
- \+ *theorem* mem_jacobson_iff
- \+ *theorem* is_local_of_is_maximal_radical
- \+ *theorem* is_local.le_jacobson
- \+ *theorem* is_local.mem_jacobson_or_exists_inv
- \+ *theorem* is_primary.to_is_prime
- \+ *theorem* mem_radical_of_pow_mem
- \+ *theorem* is_prime_radical
- \+ *theorem* is_primary_inf
- \+ *theorem* is_primary_of_is_maximal_radical
- \+ *def* jacobson
- \+ *def* is_local
- \+ *def* is_primary

modified src/ring_theory/ideals.lean
- \+ *theorem* mem_Inf



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
modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+ *lemma* to_map_injective
- \+ *lemma* map_units
- \+ *lemma* surj
- \+ *lemma* eq_iff_exists
- \+/\- *lemma* sec_spec
- \+/\- *lemma* sec_spec'
- \+ *lemma* map_right_cancel
- \+ *lemma* map_left_cancel
- \+/\- *lemma* mk'_one
- \+/\- *lemma* mk'_sec
- \+/\- *lemma* mk'_mul_cancel_right
- \+/\- *lemma* eq_of_eq
- \+/\- *lemma* lift_id
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \+ *lemma* mul_equiv_of_localizations_symm_eq_mul_equiv_of_localizations
- \+ *lemma* of_mul_equiv_of_localizations_apply
- \+ *lemma* of_mul_equiv_of_localizations_eq
- \+ *lemma* symm_comp_of_mul_equiv_of_localizations_apply
- \+ *lemma* symm_comp_of_mul_equiv_of_localizations_apply'
- \+ *lemma* of_mul_equiv_of_localizations_eq_iff_eq
- \+ *lemma* mul_equiv_of_localizations_right_inv
- \+ *lemma* mul_equiv_of_localizations_right_inv_apply
- \+ *lemma* mul_equiv_of_localizations_left_inv
- \+ *lemma* mul_equiv_of_localizations_left_inv_apply
- \+ *lemma* of_mul_equiv_of_localizations_id
- \+ *lemma* of_mul_equiv_of_localizations_comp
- \+ *lemma* of_mul_equiv_of_dom_apply
- \+ *lemma* of_mul_equiv_of_dom_eq
- \+ *lemma* of_mul_equiv_of_dom_comp_symm
- \+ *lemma* of_mul_equiv_of_dom_comp
- \+ *lemma* of_mul_equiv_of_dom_id
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* mul_equiv_of_mul_equiv_mk'
- \+ *lemma* of_mul_equiv_of_mul_equiv_apply
- \+ *lemma* of_mul_equiv_of_mul_equiv
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \- *lemma* to_fun_inj
- \+/\- *lemma* sec_spec
- \+/\- *lemma* sec_spec'
- \+/\- *lemma* mk'_one
- \+/\- *lemma* mk'_sec
- \+/\- *lemma* mk'_mul_cancel_right
- \+/\- *lemma* eq_of_eq
- \+/\- *lemma* lift_id
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \- *lemma* to_mul_equiv_eq
- \- *lemma* symm_to_mul_equiv_apply
- \- *lemma* comp_mul_equiv_symm_map_apply
- \- *lemma* to_mul_equiv_eq_iff_eq
- \- *lemma* mul_equiv_of_to_mul_equiv
- \- *lemma* mul_equiv_of_to_mul_equiv_apply
- \- *lemma* to_mul_equiv_of_mul_equiv
- \- *lemma* to_mul_equiv_of_mul_equiv_apply
- \- *lemma* to_mul_equiv_id
- \- *lemma* to_mul_equiv_comp
- \- *lemma* of_mul_equiv_eq
- \- *lemma* symm_of_mul_equiv_apply
- \- *lemma* comp_mul_equiv_symm_comap_apply
- \- *lemma* of_mul_equiv_id
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* mul_equiv_of_mul_equiv_mk'
- \- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv_apply
- \- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv
- \+ *def* to_localization_map
- \+ *def* of_mul_equiv_of_localizations
- \+ *def* of_mul_equiv_of_dom
- \- *def* to_mul_equiv
- \- *def* of_mul_equiv



## [2020-05-16 17:50:21](https://github.com/leanprover-community/mathlib/commit/a7b17cd)
feat(data/finset): remove uses of choice for infima ([#2699](https://github.com/leanprover-community/mathlib/pull/2699))
This PR removes the dependence of many lemmas about inf of finset sets on the axiom of choice. The motivation for this is to make `category_theory.limits.has_finite_limits_of_semilattice_inf_top` not depend on choice, which I would like so that I can prove independence results about topos models of set theory from the axiom of choice.
This does make the decidable_classical linter fail.
#### Estimated changes
modified src/data/finset.lean
- \+/\- *lemma* sup_le_iff
- \+/\- *lemma* le_sup
- \+/\- *lemma* sup_mono_fun
- \+/\- *lemma* le_inf_iff
- \+/\- *lemma* inf_mono_fun
- \+/\- *lemma* sup_mono_fun
- \+/\- *lemma* le_sup
- \+/\- *lemma* sup_le_iff
- \+/\- *lemma* inf_mono_fun
- \+/\- *lemma* le_inf_iff



## [2020-05-16 14:49:11](https://github.com/leanprover-community/mathlib/commit/c81be77)
feat(data/finset) Another finset disjointness lemma ([#2698](https://github.com/leanprover-community/mathlib/pull/2698))
I couldn't find this anywhere, and I wanted it.
Naming question: this is "obviously" called `disjoint_filter`, except there's already a lemma with that name.
I know I've broken one of the rules of using `simp` here ("don't do it at the beginning"), but this proof is much longer than I'd have thought would be necessary so I'm rather expecting someone to hop in with a one-liner.
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* disjoint_filter_filter



## [2020-05-16 07:36:54](https://github.com/leanprover-community/mathlib/commit/4b71428)
doc(tactic/solve_by_elim): improve docs ([#2696](https://github.com/leanprover-community/mathlib/pull/2696))
#### Estimated changes
modified src/tactic/core.lean

modified src/tactic/solve_by_elim.lean



## [2020-05-16 02:47:42](https://github.com/leanprover-community/mathlib/commit/74286f5)
feat(category_theory/limits/shapes): avoid choice for binary products ([#2695](https://github.com/leanprover-community/mathlib/pull/2695))
A tiny change to liberate binary products from the axiom of choice
#### Estimated changes
modified src/category_theory/limits/shapes/binary_products.lean



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
modified leanpkg.toml

modified src/algebra/big_operators.lean

modified src/algebra/classical_lie_algebras.lean

modified src/algebra/direct_limit.lean

modified src/algebra/direct_sum.lean

modified src/analysis/analytic/composition.lean

modified src/analysis/convex/basic.lean
- \+/\- *lemma* finset.center_mass_singleton
- \+/\- *lemma* finset.center_mass_singleton

modified src/analysis/special_functions/trigonometric.lean

modified src/computability/reduce.lean

modified src/computability/turing_machine.lean

modified src/data/dfinsupp.lean

modified src/data/equiv/basic.lean
- \+/\- *theorem* apply_eq_iff_eq
- \+/\- *theorem* apply_eq_iff_eq

modified src/data/equiv/mul_add.lean

modified src/data/fin_enum.lean

modified src/data/finmap.lean

modified src/data/finset.lean
- \+/\- *lemma* coe_singleton
- \+/\- *lemma* singleton_iff_unique_mem
- \+ *lemma* singleton_subset_set_iff
- \+/\- *lemma* singleton_bind
- \+/\- *lemma* powerset_empty
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* inf_singleton
- \+ *lemma* supr_coe
- \+ *lemma* infi_coe
- \+/\- *lemma* supr_eq_supr_finset
- \+/\- *lemma* infi_eq_infi_finset
- \+/\- *lemma* coe_singleton
- \+/\- *lemma* singleton_iff_unique_mem
- \+/\- *lemma* singleton_bind
- \+/\- *lemma* powerset_empty
- \- *lemma* sup_singleton'
- \+/\- *lemma* sup_singleton
- \- *lemma* inf_singleton'
- \+/\- *lemma* inf_singleton
- \+/\- *lemma* supr_eq_supr_finset
- \+/\- *lemma* infi_eq_infi_finset
- \+/\- *theorem* ne_empty_of_mem
- \+ *theorem* nonempty.ne_empty
- \+/\- *theorem* singleton_val
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* not_mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+ *theorem* singleton_nonempty
- \+/\- *theorem* singleton_ne_empty
- \+/\- *theorem* insert_singleton_self_eq
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+/\- *theorem* inter_singleton_of_mem
- \+/\- *theorem* inter_singleton_of_not_mem
- \+/\- *theorem* to_finset_some
- \+/\- *theorem* map_singleton
- \+/\- *theorem* image_singleton
- \+/\- *theorem* card_eq_one
- \+/\- *theorem* card_singleton
- \+/\- *theorem* card_erase_of_mem
- \+/\- *theorem* card_erase_lt_of_mem
- \+/\- *theorem* card_erase_le
- \+/\- *theorem* fold_singleton
- \+/\- *theorem* max_singleton
- \+/\- *theorem* min_singleton
- \+/\- *theorem* ne_empty_of_mem
- \+/\- *theorem* singleton_val
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* not_mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_empty
- \- *theorem* singleton_eq_singleton
- \- *theorem* insert_empty_eq_singleton
- \+/\- *theorem* insert_singleton_self_eq
- \- *theorem* insert_singleton_self_eq'
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+/\- *theorem* inter_singleton_of_mem
- \+/\- *theorem* inter_singleton_of_not_mem
- \+/\- *theorem* to_finset_some
- \+/\- *theorem* map_singleton
- \+/\- *theorem* image_singleton
- \+/\- *theorem* card_eq_one
- \+/\- *theorem* card_singleton
- \+/\- *theorem* card_erase_of_mem
- \+/\- *theorem* card_erase_lt_of_mem
- \+/\- *theorem* card_erase_le
- \+/\- *theorem* fold_singleton
- \+/\- *theorem* max_singleton
- \- *theorem* max_singleton'
- \+/\- *theorem* min_singleton
- \- *theorem* min_singleton'
- \- *def* singleton

modified src/data/finsupp.lean

modified src/data/fintype/basic.lean
- \+/\- *theorem* fintype.univ_bool
- \+/\- *theorem* fintype.univ_bool

modified src/data/fintype/card.lean

modified src/data/list/antidiagonal.lean

modified src/data/list/basic.lean
- \+/\- *lemma* singleton_eq
- \+/\- *lemma* doubleton_eq
- \+/\- *lemma* singleton_eq
- \+/\- *lemma* doubleton_eq

modified src/data/list/nodup.lean

modified src/data/multiset.lean

modified src/data/mv_polynomial.lean

modified src/data/nat/basic.lean

modified src/data/nat/gcd.lean

modified src/data/num/lemmas.lean

modified src/data/pequiv.lean

modified src/data/polynomial.lean

modified src/data/set/basic.lean
- \+/\- *theorem* singleton_def
- \+/\- *theorem* singleton_nonempty
- \+/\- *theorem* union_singleton
- \+/\- *theorem* singleton_def
- \+/\- *theorem* singleton_nonempty
- \+/\- *theorem* union_singleton

modified src/data/set/finite.lean

modified src/data/subtype.lean

modified src/field_theory/minimal_polynomial.lean

modified src/geometry/manifold/manifold.lean

modified src/geometry/manifold/real_instances.lean

modified src/group_theory/congruence.lean

modified src/group_theory/perm/sign.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/determinant.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/matrix.lean

modified src/linear_algebra/multilinear.lean

modified src/linear_algebra/nonsingular_inverse.lean

modified src/logic/embedding.lean

modified src/logic/function/basic.lean
- \+ *theorem* left_inverse.right_inverse
- \+ *theorem* right_inverse.left_inverse
- \+ *theorem* left_inverse.surjective
- \+ *theorem* right_inverse.injective

modified src/logic/relation.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/integration.lean

modified src/meta/coinductive_predicates.lean

modified src/order/bounds.lean

modified src/order/complete_lattice.lean

modified src/order/zorn.lean

modified src/ring_theory/adjoin.lean

modified src/ring_theory/algebra.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/ideals.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/polynomial.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/zfc.lean
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton
- \- *theorem* mem_singleton'

modified src/tactic/abel.lean

modified src/tactic/converter/apply_congr.lean

modified src/tactic/core.lean

modified src/tactic/derive_inhabited.lean

modified src/tactic/finish.lean

modified src/tactic/linarith.lean

modified src/tactic/mk_iff_of_inductive_prop.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/ring_exp.lean

modified src/tactic/slice.lean

modified src/tactic/tauto.lean

modified src/tactic/transport.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/instances/ennreal.lean

modified src/topology/maps.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* diam_insert
- \+/\- *lemma* diam_insert

modified src/topology/separation.lean

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/uniform_embedding.lean



## [2020-05-15 21:05:46](https://github.com/leanprover-community/mathlib/commit/f5f7a3c)
feat(analysis/special_functions/exp_log): power series for log around 1 ([#2646](https://github.com/leanprover-community/mathlib/pull/2646))
This PR adds the power series expansion for the real logarithm around `1`, in the form
```lean
has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x))
```
#### Estimated changes
modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_div

modified src/analysis/calculus/extend_deriv.lean

modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_deriv_within_le
- \+ *theorem* convex.norm_image_sub_le_of_norm_deriv_within_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_deriv_le
- \+/\- *theorem* convex.norm_image_sub_le_of_norm_deriv_le

modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* norm_id_field
- \+ *lemma* norm_id_field'

modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* abs_log_sub_add_sum_range_le
- \+ *theorem* has_sum_pow_div_log_of_abs_lt_1



## [2020-05-15 18:16:25](https://github.com/leanprover-community/mathlib/commit/14a82b3)
fix(tactic/norm_num): div/mod with negative first arg ([#2689](https://github.com/leanprover-community/mathlib/pull/2689))
bugfix from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/norm_num.20doesn't.20prove/near/197674516
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



## [2020-05-15 16:34:16](https://github.com/leanprover-community/mathlib/commit/a4266a0)
chore(scripts): update nolints.txt ([#2690](https://github.com/leanprover-community/mathlib/pull/2690))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-15 13:15:27](https://github.com/leanprover-community/mathlib/commit/471d29e)
perf(tactic/ring): use new norm_num, avoid mk_app ([#2685](https://github.com/leanprover-community/mathlib/pull/2685))
Remove `tactic.norm_num` from `ring`, and do some performance upgrades borrowed from the `norm_num` overhaul while I'm at it.
#### Estimated changes
modified src/tactic/norm_num.lean

modified src/tactic/ring.lean
- \+/\- *theorem* horner_pow
- \+ *theorem* pow_succ
- \+/\- *theorem* horner_pow

modified test/ring.lean



## [2020-05-15 07:57:55](https://github.com/leanprover-community/mathlib/commit/b44fa3c)
chore(data/int/basic): mark cast_sub with simp attribute ([#2687](https://github.com/leanprover-community/mathlib/pull/2687))
I think the reason this didn't have the `simp` attribute already was from the time when `sub_eq_add_neg` was a `simp` lemma, so it wasn't necessary. I'm adding the `simp` attribute back now that `sub_eq_add_neg` is not a `simp` lemma.
#### Estimated changes
modified src/data/int/basic.lean
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_sub



## [2020-05-15 04:51:31](https://github.com/leanprover-community/mathlib/commit/f07ac36)
feat(category_theory/limits/lattice): finite limits in a semilattice ([#2665](https://github.com/leanprover-community/mathlib/pull/2665))
Construct finite limits in a semilattice_inf_top category, and finite colimits in a semilattice_sup_bot category.
#### Estimated changes
modified src/category_theory/limits/lattice.lean



## [2020-05-15 03:11:30](https://github.com/leanprover-community/mathlib/commit/378aa0d)
feat(data/nat/choose): Sum a row of Pascal's triangle ([#2684](https://github.com/leanprover-community/mathlib/pull/2684))
Add the "sum of the nth row of Pascal's triangle" theorem.
Naming is hard, of course, and this is my first PR to mathlib, so naming suggestions are welcome.
Briefly discussed at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Candidate.20for.20inclusion.20in.20mathlib/near/197619403 .
#### Estimated changes
modified src/data/nat/choose.lean
- \+ *theorem* sum_range_choose



## [2020-05-14 18:21:52](https://github.com/leanprover-community/mathlib/commit/be03a3d)
chore(scripts): update nolints.txt ([#2682](https://github.com/leanprover-community/mathlib/pull/2682))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



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
modified src/tactic/ext.lean

modified src/tactic/lint/basic.lean

modified src/tactic/norm_cast.lean



## [2020-05-14 18:21:48](https://github.com/leanprover-community/mathlib/commit/7427f8e)
feat(topology): a few properties of `tendsto _ _ (𝓤 α)` ([#2645](https://github.com/leanprover-community/mathlib/pull/2645))
- prove that `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is an equivalence realtion;
- in case of a metric space, restate this relation as `tendsto (λ x, dist (f x) (g x)) l (𝓝 0)`;
- prove that `tendsto f l (𝓝 a) ↔ tendsto g l (𝓝 b)` provided that
  `tendsto (λ x, (f x, g x)) l (𝓤 α)`.
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+ *lemma* tendsto_uniformity_iff_dist_tendsto_zero
- \+ *lemma* filter.tendsto.congr_dist
- \+ *lemma* tendsto_iff_of_dist

modified src/topology/uniform_space/basic.lean
- \+ *lemma* filter.tendsto.uniformity_trans
- \+ *lemma* filter.tendsto.uniformity_symm
- \+ *lemma* tendsto_diag_uniformity
- \+/\- *lemma* tendsto_const_uniformity
- \+ *lemma* filter.tendsto.congr_uniformity
- \+ *lemma* uniform.tendsto_congr
- \+/\- *lemma* tendsto_const_uniformity



## [2020-05-14 15:22:51](https://github.com/leanprover-community/mathlib/commit/d412cfd)
chore(algebra/ring): lemmas about units in a semiring ([#2680](https://github.com/leanprover-community/mathlib/pull/2680))
The lemmas in non-localization files from [#2675](https://github.com/leanprover-community/mathlib/pull/2675). (Apart from one, which wasn't relevant to [#2675](https://github.com/leanprover-community/mathlib/pull/2675)).
(Edit: I am bad at git. I was hoping there would only be 1 commit here. I hope whatever I'm doing wrong is inconsequential...)
#### Estimated changes
modified src/algebra/group/is_unit.lean
- \+ *theorem* is_unit.mul_right_inj
- \+ *theorem* is_unit.mul_left_inj

modified src/algebra/ring.lean
- \+ *theorem* mul_left_eq_zero_iff_eq_zero
- \+ *theorem* mul_right_eq_zero_iff_eq_zero
- \+ *theorem* mul_left_eq_zero_iff_eq_zero
- \+ *theorem* mul_right_eq_zero_iff_eq_zero



## [2020-05-14 11:14:27](https://github.com/leanprover-community/mathlib/commit/03c272e)
chore(scripts): update nolints.txt ([#2679](https://github.com/leanprover-community/mathlib/pull/2679))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-14 11:14:24](https://github.com/leanprover-community/mathlib/commit/2871bd1)
chore(logic/function): drop `function.uncurry'` ([#2678](https://github.com/leanprover-community/mathlib/pull/2678))
See [lean[#161](https://github.com/leanprover-community/mathlib/pull/161)](https://github.com/leanprover-community/lean/pull/161/files#diff-42c23da308a4d5900f9f3244953701daR132)
Also add `uniform_continuous.prod_map` and `uniform_continuous₂.bicompl`
#### Estimated changes
modified src/logic/function/basic.lean
- \+ *lemma* uncurry_bicompl
- \- *lemma* curry_uncurry'
- \- *lemma* uncurry'_curry
- \- *lemma* uncurry'_bicompr
- \- *def* uncurry'

modified src/order/filter/extr.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/lipschitz.lean

modified src/topology/uniform_space/abstract_completion.lean
- \+/\- *lemma* extension₂_coe_coe
- \+/\- *lemma* uniform_continuous_map₂
- \+/\- *lemma* extension₂_coe_coe
- \+/\- *lemma* uniform_continuous_map₂

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous.prod_map
- \+/\- *lemma* uniform_continuous₂_def
- \+ *lemma* uniform_continuous₂.uniform_continuous
- \+/\- *lemma* uniform_continuous₂_curry
- \+ *lemma* uniform_continuous₂.bicompl
- \+/\- *lemma* uniform_continuous₂_def
- \+/\- *lemma* uniform_continuous₂_curry
- \+/\- *def* uniform_continuous₂
- \+/\- *def* uniform_continuous₂

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* extension₂_coe_coe
- \+/\- *lemma* uniform_continuous_map₂
- \+/\- *lemma* map₂_coe_coe
- \+/\- *lemma* extension₂_coe_coe
- \+/\- *lemma* uniform_continuous_map₂
- \+/\- *lemma* map₂_coe_coe



## [2020-05-14 11:14:19](https://github.com/leanprover-community/mathlib/commit/3da777a)
chore(linear_algebra/basis): use dot notation, simplify some proofs ([#2671](https://github.com/leanprover-community/mathlib/pull/2671))
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *lemma* continuous_equiv_fun_basis
- \+ *lemma* continuous_linear_map.exists_right_inverse_of_surjective
- \+/\- *lemma* continuous_equiv_fun_basis

modified src/linear_algebra/basis.lean
- \+ *lemma* linear_independent.ne_zero
- \+ *lemma* linear_independent.union
- \+ *lemma* linear_independent.inl_union_inr
- \+/\- *lemma* constr_basis
- \+/\- *lemma* exists_is_basis
- \+ *lemma* linear_map.exists_left_inverse_of_injective
- \+ *lemma* linear_map.exists_right_inverse_of_surjective
- \- *lemma* ne_zero_of_linear_independent
- \- *lemma* linear_independent_union
- \- *lemma* linear_independent_inl_union_inr
- \+/\- *lemma* constr_basis
- \+/\- *lemma* exists_is_basis
- \- *lemma* exists_left_inverse_linear_map_of_injective
- \- *lemma* exists_right_inverse_linear_map_of_surjective

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finite_dimensional.lean



## [2020-05-14 07:53:24](https://github.com/leanprover-community/mathlib/commit/d0beb49)
doc(*): move most docs to website, update links ([#2676](https://github.com/leanprover-community/mathlib/pull/2676))
The relaunched https://leanprover-community.github.io now contains copies of most of the doc files. This PR replaces the corresponding markdown files on mathlib with pointers to their new locations so that they only need to be maintained in one place.
The two remaining markdown files are `docs/contribute/bors.md` and `docs/contribute/code-review.md`.
Fixes [#2168](https://github.com/leanprover-community/mathlib/pull/2168).
#### Estimated changes
modified .github/CONTRIBUTING.md

modified README.md

modified archive/README.md

modified docs/contribute/doc.md
- \- *def* padic_norm
- \- *def* padic_val_rat
- \- *def* brackets
- \- *def* map_prefix

modified docs/contribute/index.md

modified docs/contribute/naming.md

modified docs/contribute/style.md
- \- *lemma* div_self
- \- *lemma* nhds_supr
- \- *lemma* mem_nhds_of_is_topological_basis
- \- *theorem* two_step_induction_on
- \- *theorem* two_step_induction_on
- \- *theorem* nat_case
- \- *theorem* nat_discriminate
- \- *theorem* mem_split
- \- *theorem* add_right_inj
- \- *theorem* sub_eq_zero_iff_le
- \- *theorem* reverse_reverse
- \- *theorem* reverse_reverse

modified docs/extras.md

modified docs/extras/calc.md
- \- *lemma* lt_of_lt_of_le
- \- *lemma* lt_trans
- \- *theorem* r_trans
- \- *theorem* T2
- \- *theorem* rst_trans

modified docs/extras/conv.md

modified docs/extras/simp.md
- \- *lemma* my_lemma
- \- *theorem* cong_refl
- \- *theorem* ne_zero

modified docs/extras/tactic_writing.md

modified docs/extras/well_founded_recursion.md
- \- *lemma* prod_factors
- \- *lemma* prod_factors
- \- *lemma* strong_induction_on
- \- *def* gcd
- \- *def* gcd
- \- *def* gcd
- \- *def* gcd
- \- *def* gcd
- \- *def* gcd

modified docs/install/debian.md

modified docs/install/debian_details.md

deleted docs/install/extensions-icon.png

modified docs/install/linux.md

modified docs/install/macos.md

deleted docs/install/new-extensions-icon.png

modified docs/install/project.md

modified docs/install/windows.md

modified docs/mathlib-overview.md

modified docs/theories.md

modified docs/theories/category_theory.md

modified docs/theories/naturals.md

modified docs/theories/padics.md

modified docs/theories/sets.md
- \- *def* x
- \- *def* S
- \- *def* finite

modified docs/theories/topology.md
- \- *lemma* is_open_Union
- \- *lemma* is_open_union
- \- *lemma* tendsto_nhds_unique
- \- *def* compact

modified src/tactic/doc_commands.lean

modified src/topology/basic.lean



## [2020-05-14 04:40:05](https://github.com/leanprover-community/mathlib/commit/7077b58)
chore(logic/function): move to `logic/function/basic` ([#2677](https://github.com/leanprover-community/mathlib/pull/2677))
Also add some docstrings.
I'm going to add more `logic.function.*` files with theorems that can't go to `basic` because of imports.
#### Estimated changes
modified src/algebra/group/basic.lean

modified src/algebra/group/units.lean

modified src/category_theory/fully_faithful.lean

modified src/control/bifunctor.lean

modified src/data/set/function.lean

renamed src/logic/function.lean to src/logic/function/basic.lean
- \+/\- *theorem* cantor_surjective
- \+/\- *theorem* cantor_injective
- \+/\- *theorem* cantor_surjective
- \+/\- *theorem* cantor_injective

modified src/order/boolean_algebra.lean



## [2020-05-14 04:40:03](https://github.com/leanprover-community/mathlib/commit/6ffb613)
chore(algebra/free_monoid): add a custom `rec_on` ([#2670](https://github.com/leanprover-community/mathlib/pull/2670))
#### Estimated changes
modified src/algebra/free_monoid.lean
- \+/\- *lemma* one_def
- \+/\- *lemma* mul_def
- \+ *lemma* of_def
- \+/\- *lemma* one_def
- \+/\- *lemma* mul_def
- \- *lemma* of_mul_eq_cons
- \+ *def* rec_on

modified src/group_theory/submonoid.lean



## [2020-05-14 00:19:02](https://github.com/leanprover-community/mathlib/commit/f7cb363)
refactor(order/lattice): adjust proofs to avoid choice ([#2666](https://github.com/leanprover-community/mathlib/pull/2666))
For foundational category theoretic reasons, I'd like these lattice properties to avoid choice.
In particular, I'd like the proof here: https://github.com/leanprover-community/mathlib/pull/2665 to be intuitionistic.
 For most of them it was very easy, eg changing `finish` to `simp`. For `sup_assoc` and `inf_assoc` it's a bit more complex though - for `inf_assoc` I wrote out a term mode proof, and for `sup_assoc` I used `ifinish`. I realise `ifinish` is deprecated because it isn't always intuitionistic, but in this case it did give an intuitionistic proof. I think both should be proved the same way, but I'm including one of each to see which is preferred.
#### Estimated changes
modified src/order/lattice.lean
- \+/\- *lemma* inf_le_inf_right
- \+/\- *lemma* inf_le_inf_left
- \+/\- *lemma* inf_le_inf_right
- \+/\- *lemma* inf_le_inf_left



## [2020-05-13 18:31:18](https://github.com/leanprover-community/mathlib/commit/fc0c025)
refactor(scripts/mk_all): generate a single deterministic all.lean file ([#2673](https://github.com/leanprover-community/mathlib/pull/2673))
The current `mk_all.sh` script is non-deterministic, and creates invalid Lean code for the `data.matrix.notation` import.  The generated `all.lean` files are also slow: they take two minutes to compile on my machine.
The new script fixes all of that.  The single generated `all.lean` file takes only 27 seconds to compile now.
#### Estimated changes
modified scripts/mk_all.sh



## [2020-05-13 12:20:02](https://github.com/leanprover-community/mathlib/commit/9f16f86)
feat(topology/algebra/infinite_sum): sums on subtypes ([#2659](https://github.com/leanprover-community/mathlib/pull/2659))
For `f` a summable function defined on the integers, we prove the formula
```
(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)
```
This is deduced from a general version on subtypes of the form `univ - s` where `s` is a finset.
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* coe_not_mem_range_equiv
- \+ *lemma* coe_not_mem_range_equiv_symm
- \+ *def* not_mem_range_equiv

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable
- \+ *lemma* has_sum_subtype_iff_of_eq_zero
- \+ *lemma* has_sum_subtype_iff
- \+ *lemma* has_sum_subtype_iff'
- \+ *lemma* summable_subtype_iff
- \+ *lemma* sum_add_tsum_subtype
- \+ *lemma* summable_nat_add_iff
- \+ *lemma* has_sum_nat_add_iff
- \+ *lemma* has_sum_nat_add_iff'
- \+ *lemma* sum_add_tsum_nat_add



## [2020-05-13 10:27:15](https://github.com/leanprover-community/mathlib/commit/c9f2cbc)
chore(scripts): update nolints.txt ([#2669](https://github.com/leanprover-community/mathlib/pull/2669))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-13 10:27:13](https://github.com/leanprover-community/mathlib/commit/506a71f)
feat(category_theory): preadditive categories ([#2663](https://github.com/leanprover-community/mathlib/pull/2663))
[As discussed](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Lean.20in.20the.20wild/near/197168926), here is the pedestrian definition of preadditive categories. Hopefully, it is not here to stay, but it will allow me to start PRing abelian categories.
#### Estimated changes
modified src/algebra/category/Group/default.lean

created src/algebra/category/Group/preadditive.lean

modified src/algebra/category/Group/zero.lean

modified src/algebra/category/Module/basic.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.ι_of_ι
- \+ *lemma* cofork.π_of_π

modified src/category_theory/limits/shapes/kernels.lean

modified src/category_theory/limits/shapes/zero.lean
- \+/\- *lemma* zero_of_comp_mono
- \+ *lemma* zero_of_epi_comp
- \+/\- *lemma* zero_of_comp_mono
- \- *lemma* zero_of_comp_epi

created src/category_theory/preadditive.lean
- \+ *lemma* sub_comp
- \+ *lemma* comp_sub
- \+ *lemma* neg_comp
- \+ *lemma* comp_neg
- \+ *lemma* neg_comp_neg
- \+ *lemma* mono_of_cancel_zero
- \+ *lemma* mono_iff_cancel_zero
- \+ *lemma* epi_of_cancel_zero
- \+ *lemma* epi_iff_cancel_zero
- \+ *def* left_comp
- \+ *def* right_comp
- \+ *def* has_limit_parallel_pair
- \+ *def* has_equalizers_of_has_kernels
- \+ *def* has_colimit_parallel_pair
- \+ *def* has_coequalizers_of_has_cokernels



## [2020-05-13 10:27:11](https://github.com/leanprover-community/mathlib/commit/ce86d33)
feat(analysis/calculus/(f)deriv): differentiability of a finite sum of functions ([#2657](https://github.com/leanprover-community/mathlib/pull/2657))
We show that, if each `f i` is differentiable, then `λ y, ∑ i in s, f i y` is also differentiable when `s` is a finset, and give the lemmas around this for `fderiv` and `deriv`.
#### Estimated changes
modified src/analysis/asymptotics.lean
- \+/\- *theorem* is_O_with_zero
- \+ *theorem* is_O_with_zero'
- \+/\- *theorem* is_O_zero
- \+ *theorem* is_O_with.sum
- \+ *theorem* is_O.sum
- \+ *theorem* is_o.sum
- \+/\- *theorem* is_O_with_zero
- \+/\- *theorem* is_O_zero

modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_deriv_within_at.has_fderiv_within_at
- \+ *lemma* deriv_within_sum
- \+ *lemma* deriv_sum
- \+ *lemma* differentiable_within_at.div_const
- \+ *lemma* differentiable_at.div_const
- \+ *lemma* differentiable_on.div_const
- \+ *lemma* differentiable.div_const
- \+ *lemma* deriv_within_div_const
- \+ *lemma* deriv_div_const
- \+ *theorem* has_deriv_at_filter.sum
- \+ *theorem* has_strict_deriv_at.sum
- \+ *theorem* has_deriv_within_at.sum
- \+ *theorem* has_deriv_at.sum

modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_strict_fderiv_at.sum
- \+ *theorem* has_fderiv_at_filter.sum
- \+ *theorem* has_fderiv_within_at.sum
- \+ *theorem* has_fderiv_at.sum
- \+ *theorem* differentiable_within_at.sum
- \+ *theorem* differentiable_at.sum
- \+ *theorem* differentiable_on.sum
- \+ *theorem* differentiable.sum
- \+ *theorem* fderiv_within_sum
- \+ *theorem* fderiv_sum

modified src/topology/algebra/module.lean
- \+ *lemma* sum_apply



## [2020-05-13 07:01:46](https://github.com/leanprover-community/mathlib/commit/ed183f9)
chore(group_theory/submonoid): use `complete_lattice_of_Inf` ([#2661](https://github.com/leanprover-community/mathlib/pull/2661))
* Use `complete_lattice_of_Inf` for `submonoid` and `subgroup` lattices.
* Add `sub*.copy`.
* Add a few `@[simp]` lemmas.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* to_fun_eq_coe

modified src/group_theory/bundled_subgroup.lean
- \+ *lemma* coe_to_submonoid
- \+/\- *lemma* closure_mono
- \+/\- *lemma* closure_eq
- \+/\- *lemma* closure_empty
- \- *lemma* coe_ssubset_coe
- \+/\- *lemma* closure_mono
- \+/\- *lemma* closure_eq
- \+/\- *lemma* closure_empty

modified src/group_theory/submonoid.lean
- \+ *lemma* mem_carrier
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi
- \+/\- *theorem* ext'
- \+/\- *theorem* ext'
- \+ *def* copy

modified src/order/bounds.lean
- \+ *lemma* is_glb.of_image
- \+ *lemma* is_lub.of_image

modified src/order/complete_lattice.lean
- \+ *lemma* is_glb_binfi
- \+ *lemma* is_lub_bsupr



## [2020-05-13 03:44:20](https://github.com/leanprover-community/mathlib/commit/51e2b4c)
feat(topology/separation): add `subtype.t1_space` and `subtype.regular` ([#2667](https://github.com/leanprover-community/mathlib/pull/2667))
Also simplify the proof of `exists_open_singleton_of_fintype`
#### Estimated changes
modified src/data/finset.lean
- \+ *theorem* filter_ssubset

modified src/topology/separation.lean
- \+ *theorem* exists_open_singleton_of_open_finset



## [2020-05-13 03:44:18](https://github.com/leanprover-community/mathlib/commit/4857284)
feat(topology/bounded_continuous_function): the normed space C^0 ([#2660](https://github.com/leanprover-community/mathlib/pull/2660))
For β a normed (vector) space over a nondiscrete normed field 𝕜, we construct the normed 𝕜-space structure on the set of bounded continuous functions from a topological space into β.
#### Estimated changes
modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* dist_eq
- \+/\- *lemma* dist_set_exists
- \+ *lemma* norm_eq
- \+ *lemma* norm_smul_le
- \+ *lemma* norm_smul
- \+/\- *lemma* dist_eq
- \+/\- *lemma* dist_set_exists



## [2020-05-13 01:57:37](https://github.com/leanprover-community/mathlib/commit/cbffb34)
feat(analysis/specific_limits): more geometric series ([#2658](https://github.com/leanprover-community/mathlib/pull/2658))
Currently, the sum of a geometric series is only known for real numbers in `[0,1)`. We prove it for any element of a normed field with norm `< 1`, and specialize it to real numbers in `(-1, 1)`.
Some lemmas in `analysis/specific_limits` are also moved around (but their content is not changed) to get a better organization of this file.
#### Estimated changes
modified src/analysis/analytic/basic.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* filter.tendsto.div_const
- \+ *lemma* has_sum_iff_tendsto_nat_of_summable_norm

modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_norm_lt_1
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_abs_lt_1
- \+ *lemma* has_sum_geometric_of_lt_1
- \+ *lemma* summable_geometric_of_lt_1
- \+ *lemma* tsum_geometric_of_lt_1
- \+ *lemma* has_sum_geometric_of_norm_lt_1
- \+ *lemma* summable_geometric_of_norm_lt_1
- \+ *lemma* tsum_geometric_of_norm_lt_1
- \+ *lemma* has_sum_geometric_of_abs_lt_1
- \+ *lemma* summable_geometric_of_abs_lt_1
- \+ *lemma* tsum_geometric_of_abs_lt_1
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1_normed_field
- \+/\- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+/\- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \- *lemma* has_sum_geometric
- \- *lemma* summable_geometric
- \- *lemma* tsum_geometric
- \+/\- *def* pos_sum_of_encodable
- \+/\- *def* pos_sum_of_encodable

modified src/data/real/cardinality.lean



## [2020-05-12 18:35:33](https://github.com/leanprover-community/mathlib/commit/437fdaf)
feat(category_theory/creates): creates limits => preserves limits ([#2639](https://github.com/leanprover-community/mathlib/pull/2639))
Show that `F` preserves limits if it creates them and the target category has them.
#### Estimated changes
modified src/category_theory/limits/creates.lean

modified src/category_theory/limits/limits.lean
- \+ *def* cocone_point_unique_up_to_iso
- \- *def* cone_point_unique_up_to_iso

modified src/category_theory/limits/preserves.lean

modified src/category_theory/limits/shapes/equalizers.lean



## [2020-05-12 15:37:33](https://github.com/leanprover-community/mathlib/commit/1141533)
feat(data/matrix): matrix and vector notation ([#2656](https://github.com/leanprover-community/mathlib/pull/2656))
This PR adds notation for matrices and vectors [as discussed on Zulip a couple of months ago](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20matrices.20and.20vectors), so that `![![a, b], ![c, d]]` constructs a 2x2 matrix with rows `![a, b] : fin 2 -> α` and `![c, d]`. It also adds corresponding `simp` lemmas for all matrix operations defined in `data.matrix.basic`. These lemmas should apply only when the input already contains `![...]`.
To express the `simp` lemmas nicely, I defined a function `dot_product : (v w : n -> α) -> α` which returns the sum of the entrywise product of two vectors. IMO, this makes the definitions of `matrix.mul`, `matrix.mul_vec` and `matrix.vec_mul` clearer, and it allows us to share some proofs. I could also inline `dot_product` (restoring the old situation) if the reviewers prefer.
#### Estimated changes
modified src/data/matrix/basic.lean
- \+ *lemma* diagonal_transpose
- \+ *lemma* dot_product_assoc
- \+ *lemma* dot_product_comm
- \+ *lemma* dot_product_punit
- \+ *lemma* dot_product_zero
- \+ *lemma* dot_product_zero'
- \+ *lemma* zero_dot_product
- \+ *lemma* zero_dot_product'
- \+ *lemma* add_dot_product
- \+ *lemma* dot_product_add
- \+ *lemma* diagonal_dot_product
- \+ *lemma* dot_product_diagonal
- \+ *lemma* dot_product_diagonal'
- \+ *lemma* neg_dot_product
- \+ *lemma* dot_product_neg
- \+ *lemma* smul_dot_product
- \+ *lemma* dot_product_smul
- \+ *lemma* row_mul_col_val
- \+ *lemma* neg_vec_mul
- \+ *lemma* vec_mul_neg
- \+ *lemma* neg_mul_vec
- \+ *lemma* mul_vec_neg
- \+ *def* dot_product

created src/data/matrix/notation.lean
- \+ *lemma* empty_eq
- \+ *lemma* cons_val_zero
- \+ *lemma* cons_val_zero'
- \+ *lemma* cons_val_succ
- \+ *lemma* cons_val_succ'
- \+ *lemma* head_cons
- \+ *lemma* tail_cons
- \+ *lemma* empty_val'
- \+ *lemma* cons_val'
- \+ *lemma* head_val'
- \+ *lemma* tail_val'
- \+ *lemma* cons_head_tail
- \+ *lemma* cons_val_one
- \+ *lemma* cons_val_fin_one
- \+ *lemma* dot_product_empty
- \+ *lemma* cons_dot_product
- \+ *lemma* dot_product_cons
- \+ *lemma* col_empty
- \+ *lemma* col_cons
- \+ *lemma* row_empty
- \+ *lemma* row_cons
- \+ *lemma* transpose_empty_rows
- \+ *lemma* transpose_empty_cols
- \+ *lemma* cons_transpose
- \+ *lemma* head_transpose
- \+ *lemma* tail_transpose
- \+ *lemma* empty_mul
- \+ *lemma* empty_mul_empty
- \+ *lemma* mul_empty
- \+ *lemma* mul_val_succ
- \+ *lemma* cons_mul
- \+ *lemma* empty_vec_mul
- \+ *lemma* vec_mul_empty
- \+ *lemma* cons_vec_mul
- \+ *lemma* vec_mul_cons
- \+ *lemma* empty_mul_vec
- \+ *lemma* mul_vec_empty
- \+ *lemma* cons_mul_vec
- \+ *lemma* mul_vec_cons
- \+ *lemma* empty_vec_mul_vec
- \+ *lemma* vec_mul_vec_empty
- \+ *lemma* cons_vec_mul_vec
- \+ *lemma* vec_mul_vec_cons
- \+ *lemma* smul_empty
- \+ *lemma* smul_cons
- \+ *lemma* empty_add_empty
- \+ *lemma* cons_add
- \+ *lemma* add_cons
- \+ *lemma* zero_empty
- \+ *lemma* cons_zero_zero
- \+ *lemma* head_zero
- \+ *lemma* tail_zero
- \+ *lemma* cons_eq_zero_iff
- \+ *lemma* cons_nonzero_iff
- \+ *lemma* neg_empty
- \+ *lemma* neg_cons
- \+ *lemma* minor_empty
- \+ *lemma* minor_cons_row
- \+ *def* vec_empty
- \+ *def* vec_cons
- \+ *def* vec_head
- \+ *def* vec_tail

modified src/data/matrix/pequiv.lean

created test/matrix.lean



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
modified docs/contribute/naming.md

modified src/algebra/associated.lean

modified src/algebra/char_p.lean

modified src/algebra/euclidean_domain.lean

modified src/algebra/field.lean

modified src/algebra/gcd_domain.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group/basic.lean
- \+/\- *lemma* sub_right_inj
- \+/\- *lemma* sub_left_inj
- \+/\- *lemma* sub_left_inj
- \+/\- *lemma* sub_right_inj
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_left_injective
- \+/\- *theorem* mul_right_injective
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj

modified src/algebra/group/units.lean
- \+/\- *theorem* mul_right_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj

modified src/algebra/group_power.lean
- \+ *theorem* pow_left_inj
- \- *theorem* pow_right_inj

modified src/algebra/group_with_zero.lean
- \+ *lemma* div_left_inj'
- \+ *lemma* mul_left_inj'
- \- *lemma* div_right_inj'
- \- *lemma* mul_right_inj'

modified src/algebra/ring.lean

modified src/analysis/convex/basic.lean

modified src/analysis/special_functions/trigonometric.lean

modified src/combinatorics/composition.lean

modified src/data/complex/exponential.lean

modified src/data/finsupp.lean
- \+ *lemma* single_left_inj
- \- *lemma* single_right_inj

modified src/data/fintype/basic.lean

modified src/data/list/basic.lean
- \+/\- *theorem* append_inj_right
- \+/\- *theorem* append_inj_left
- \+/\- *theorem* append_inj_right'
- \+/\- *theorem* append_inj_left'
- \+/\- *theorem* append_right_inj
- \+/\- *theorem* append_left_inj
- \+ *theorem* prefix_append_right_inj
- \+/\- *theorem* append_inj_left
- \+/\- *theorem* append_inj_right
- \+/\- *theorem* append_inj_left'
- \+/\- *theorem* append_inj_right'
- \+/\- *theorem* append_left_inj
- \+/\- *theorem* append_right_inj
- \- *theorem* prefix_append_left_inj

modified src/data/nat/basic.lean

modified src/data/nat/modeq.lean

modified src/data/nat/prime.lean

modified src/data/nat/totient.lean

modified src/data/pnat/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* add_right_inj
- \+/\- *lemma* add_left_inj
- \+ *lemma* sub_right_inj
- \+/\- *lemma* add_left_inj
- \+/\- *lemma* add_right_inj
- \- *lemma* sub_left_inj

modified src/field_theory/finite.lean

modified src/field_theory/splitting_field.lean

modified src/group_theory/order_of_element.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/determinant.lean

modified src/measure_theory/integration.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/number_theory/sum_four_squares.lean

modified src/ring_theory/integral_domain.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/power_series.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/set_theory/game/domineering.lean

modified src/set_theory/ordinal.lean
- \+ *theorem* mul_right_inj
- \- *theorem* mul_left_inj

modified src/tactic/omega/eq_elim.lean

modified src/topology/algebra/infinite_sum.lean



## [2020-05-12 15:37:29](https://github.com/leanprover-community/mathlib/commit/77b3d50)
chore(topology/instances/ennreal): add +1 version of `tsum_eq_supr_sum` ([#2633](https://github.com/leanprover-community/mathlib/pull/2633))
Also add a few lemmas about `supr` and monotone functions.
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* sum_mono_set_of_nonneg
- \+ *lemma* sum_mono_set

modified src/measure_theory/integration.lean

modified src/order/complete_lattice.lean
- \+ *lemma* monotone.le_map_supr
- \+ *lemma* monotone.le_map_supr2
- \+ *lemma* supr_comp_le
- \+ *lemma* monotone.supr_comp_eq
- \+ *lemma* le_infi_comp
- \+ *lemma* monotone.infi_comp_eq
- \- *lemma* monotone.map_supr_ge
- \- *lemma* monotone.map_supr2_ge

modified src/topology/instances/ennreal.lean



## [2020-05-12 15:37:27](https://github.com/leanprover-community/mathlib/commit/ff184e6)
feat(analysis/normed_space): add Mazur-Ulam theorem ([#2214](https://github.com/leanprover-community/mathlib/pull/2214))
Based on a proof by Jussi Väisälä, see [journal version](https://www.jstor.org/stable/3647749) or [preprint on web.archive](https://web.archive.org/web/20180516125105/http://www.helsinki.fi/~jvaisala/mazurulam.pdf).
Also rename `reflection` to `point_reflection` as was suggested by @rwbarton and @PatrickMassot
#### Estimated changes
modified docs/references.bib

modified src/algebra/midpoint.lean
- \+ *lemma* point_reflection_midpoint_left
- \+ *lemma* point_reflection_midpoint_right
- \- *lemma* reflection_midpoint_left
- \- *lemma* reflection_midpoint_right

created src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* midpoint_fixed
- \+ *lemma* map_midpoint
- \+ *lemma* coe_to_real_linear_equiv_of_map_zero
- \+ *lemma* coe_to_real_linear_equiv_of_map_zero_symm
- \+ *lemma* to_real_linear_equiv_apply
- \+ *lemma* to_real_linear_equiv_symm_apply
- \+ *def* to_real_linear_equiv_of_map_zero
- \+ *def* to_real_linear_equiv

created src/analysis/normed_space/point_reflection.lean
- \+ *lemma* equiv.point_reflection_fixed_iff_of_module
- \+ *lemma* point_reflection_apply
- \+ *lemma* point_reflection_to_equiv
- \+ *lemma* point_reflection_self
- \+ *lemma* point_reflection_involutive
- \+ *lemma* point_reflection_symm
- \+ *lemma* point_reflection_dist_fixed
- \+ *lemma* point_reflection_dist_self'
- \+ *lemma* point_reflection_midpoint_left
- \+ *lemma* point_reflection_midpoint_right
- \+ *lemma* point_reflection_fixed_iff
- \+ *lemma* point_reflection_dist_self
- \+ *lemma* point_reflection_dist_self_real
- \+ *def* point_reflection

modified src/analysis/normed_space/real_inner_product.lean

deleted src/analysis/normed_space/reflection.lean
- \- *lemma* equiv.reflection_fixed_iff_of_module
- \- *lemma* reflection_apply
- \- *lemma* reflection_to_equiv
- \- *lemma* reflection_self
- \- *lemma* reflection_involutive
- \- *lemma* reflection_symm
- \- *lemma* reflection_dist_fixed
- \- *lemma* reflection_dist_self'
- \- *lemma* reflection_midpoint_left
- \- *lemma* reflection_midpoint_right
- \- *lemma* reflection_fixed_iff
- \- *lemma* reflection_dist_self
- \- *lemma* reflection_dist_self_real
- \- *def* reflection

modified src/data/equiv/mul_add.lean
- \+ *lemma* point_reflection_apply
- \+ *lemma* point_reflection_self
- \+ *lemma* point_reflection_involutive
- \+ *lemma* point_reflection_symm
- \+ *lemma* point_reflection_fixed_iff_of_bit0_inj
- \- *lemma* reflection_apply
- \- *lemma* reflection_self
- \- *lemma* reflection_involutive
- \- *lemma* reflection_symm
- \- *lemma* reflection_fixed_iff_of_bit0_inj
- \+ *def* point_reflection
- \- *def* reflection

modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le
- \+/\- *lemma* le_csupr
- \+/\- *lemma* cinfi_le

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/isometry.lean
- \+ *lemma* symm_symm
- \+ *lemma* symm_trans_apply
- \+ *lemma* add_right_to_equiv
- \+ *lemma* coe_add_right
- \+ *lemma* add_right_apply
- \+ *lemma* add_right_symm
- \+ *lemma* add_left_to_equiv
- \+ *lemma* coe_add_left
- \+ *lemma* add_left_symm
- \+ *lemma* neg_symm
- \+ *lemma* neg_to_equiv
- \+ *lemma* coe_neg



## [2020-05-12 13:39:55](https://github.com/leanprover-community/mathlib/commit/3f216bc)
feat(number_theory/basic): dvd_sub_pow_of_dvd_sub ([#2640](https://github.com/leanprover-community/mathlib/pull/2640))
Co-authored with: Kenny Lau <kc_kennylau@yahoo.com.hk>
#### Estimated changes
modified src/algebra/geom_sum.lean
- \+ *theorem* geom_series₂_self
- \+ *theorem* ring_hom.map_geom_series
- \+ *theorem* ring_hom.map_geom_series₂

created src/number_theory/basic.lean
- \+ *lemma* dvd_sub_pow_of_dvd_sub

modified src/ring_theory/ideals.lean
- \+ *lemma* mk_eq_mk_hom



## [2020-05-12 11:31:31](https://github.com/leanprover-community/mathlib/commit/61b59ec)
fix(order/filter/basic): markdown error in module doc ([#2664](https://github.com/leanprover-community/mathlib/pull/2664))
#### Estimated changes
modified src/order/filter/basic.lean



## [2020-05-12 06:37:08](https://github.com/leanprover-community/mathlib/commit/295b87e)
feat(ring_theory/integral_domain): sum in integral domain indexed by finite group ([#2623](https://github.com/leanprover-community/mathlib/pull/2623))
In other words: nontrivial sums are trivial
Moved from `field_theory.finite` to the new `ring_theory.integral_domain`:
- `card_nth_roots_subgroup_units`
- `subgroup_units_cyclic`
#### Estimated changes
modified src/algebra/group/units_hom.lean
- \+ *lemma* coe_to_hom_units
- \+ *def* to_hom_units

modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_subtype

modified src/field_theory/finite.lean
- \- *lemma* card_nth_roots_subgroup_units

modified src/group_theory/order_of_element.lean
- \+ *lemma* is_cyclic.exists_monoid_generator

created src/ring_theory/integral_domain.lean
- \+ *lemma* card_nth_roots_subgroup_units
- \+ *lemma* card_fiber_eq_of_mem_range
- \+ *lemma* sum_hom_units_eq_zero
- \+ *lemma* sum_hom_units



## [2020-05-12 05:22:17](https://github.com/leanprover-community/mathlib/commit/f0e7817)
chore(scripts): update nolints.txt ([#2662](https://github.com/leanprover-community/mathlib/pull/2662))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-12 01:24:40](https://github.com/leanprover-community/mathlib/commit/8c88721)
feat(data/list): assorted lemmas ([#2651](https://github.com/leanprover-community/mathlib/pull/2651))
Some lemmas I found useful for [#2578](https://github.com/leanprover-community/mathlib/pull/2578)
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* is_nil_iff_eq_nil
- \+/\- *theorem* last_cons
- \+ *theorem* last_mem
- \+ *theorem* last'_is_none
- \+ *theorem* last'_is_some
- \+ *theorem* mem_last'_eq_last
- \+ *theorem* mem_of_mem_last'
- \+ *theorem* init_append_last'
- \+ *theorem* ilast_eq_last'
- \+ *theorem* last'_append_cons
- \+ *theorem* last'_append_of_ne_nil
- \+ *theorem* mem_of_mem_head'
- \+ *theorem* cons_head'_tail
- \+ *theorem* head_mem_head'
- \+ *theorem* prod_eq_foldr
- \+/\- *theorem* last_cons

modified src/data/list/chain.lean
- \+ *theorem* chain'.rel_head
- \+ *theorem* chain'.rel_head'
- \+ *theorem* chain'.cons'
- \+ *theorem* chain'_cons'
- \+ *theorem* chain'.append
- \+ *theorem* chain'.imp_head

modified src/data/list/defs.lean



## [2020-05-11 13:23:56](https://github.com/leanprover-community/mathlib/commit/eb9e382)
test(tactic/norm_num): import tests from lean core ([#2654](https://github.com/leanprover-community/mathlib/pull/2654))
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



## [2020-05-11 11:46:09](https://github.com/leanprover-community/mathlib/commit/a87f326)
chore(scripts): update nolints.txt ([#2653](https://github.com/leanprover-community/mathlib/pull/2653))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-11 09:42:50](https://github.com/leanprover-community/mathlib/commit/e777d0b)
refactor(data/real/pi): add tactics for pi computation ([#2641](https://github.com/leanprover-community/mathlib/pull/2641))
Depends on [#2589](https://github.com/leanprover-community/mathlib/pull/2589). Moves pi bounds from @fpvandoorn's gist to mathlib, and also adds a small tactic to uniformize the proofs (and also skip some unsqueezed proofs), making the compilation even faster (just around 1 second for the longest proofs).
#### Estimated changes
modified src/data/real/pi.lean
- \+/\- *lemma* sqrt_two_add_series_step_up
- \+/\- *lemma* sqrt_two_add_series_step_down
- \+/\- *lemma* pi_gt_three
- \+/\- *lemma* pi_gt_314
- \+/\- *lemma* pi_lt_315
- \+ *lemma* pi_gt_31415
- \+ *lemma* pi_lt_31416
- \+ *lemma* pi_gt_3141592
- \+ *lemma* pi_lt_3141593
- \+/\- *lemma* sqrt_two_add_series_step_up
- \+/\- *lemma* sqrt_two_add_series_step_down
- \+/\- *lemma* pi_gt_three
- \+/\- *lemma* pi_gt_314
- \+/\- *lemma* pi_lt_315
- \+ *theorem* pi_lower_bound_start
- \+ *theorem* pi_upper_bound_start



## [2020-05-11 06:32:55](https://github.com/leanprover-community/mathlib/commit/ff37fb8)
feat(algebra/ring): monoid structure on `R →+* R` ([#2649](https://github.com/leanprover-community/mathlib/pull/2649))
Also add `comp_id` and `id_comp`
#### Estimated changes
modified src/algebra/group_power.lean
- \+ *lemma* coe_pow

modified src/algebra/ring.lean
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* one_def
- \+ *lemma* coe_one
- \+ *lemma* mul_def
- \+ *lemma* coe_mul
- \+/\- *def* mk'
- \+/\- *def* mk'



## [2020-05-11 03:53:42](https://github.com/leanprover-community/mathlib/commit/7146082)
refactor(data/fintype/basic): weaken assumptions of set.fintype ([#2650](https://github.com/leanprover-community/mathlib/pull/2650))
#### Estimated changes
modified src/data/fintype/basic.lean



## [2020-05-10 20:24:02](https://github.com/leanprover-community/mathlib/commit/b9bdc67)
feat(*): prove some `*.iterate` theorems ([#2647](https://github.com/leanprover-community/mathlib/pull/2647))
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/order/basic.lean
- \+ *lemma* strict_mono_id

modified src/topology/algebra/module.lean
- \+ *lemma* mul_def
- \+ *lemma* coe_mul
- \+/\- *lemma* mul_apply
- \+ *lemma* smul_right_one_pow
- \+/\- *lemma* mul_apply

modified src/topology/basic.lean
- \+ *lemma* continuous.iterate
- \+ *lemma* continuous_at.iterate



## [2020-05-10 17:09:22](https://github.com/leanprover-community/mathlib/commit/8c6b14e)
fix(library_search): use custom apply tactic for the main goal, as well as subgoals ([#2648](https://github.com/leanprover-community/mathlib/pull/2648))
cf https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/List.20lemmas
#### Estimated changes
modified src/tactic/suggest.lean

modified test/library_search/basic.lean
- \+ *lemma* bind_singleton



## [2020-05-10 07:14:07](https://github.com/leanprover-community/mathlib/commit/3710744)
feat(meta/uchange): universe lifting and lowering in meta ([#2627](https://github.com/leanprover-community/mathlib/pull/2627))
We define the meta type `uchange (α : Type v) : Type u`, which permits us to change the universe of a type analogously to `ulift`.  However since `uchange` is meta, it can both lift and lower the universe.
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/widget/near/196808542
#### Estimated changes
created src/meta/uchange.lean



## [2020-05-10 04:05:15](https://github.com/leanprover-community/mathlib/commit/b248481)
chore(algebra/char_zero): add `∀ n : ℕ, (n + 1 : α) ≠ 0` ([#2644](https://github.com/leanprover-community/mathlib/pull/2644))
#### Estimated changes
modified src/algebra/char_zero.lean
- \+ *lemma* cast_add_one_ne_zero



## [2020-05-10 04:05:14](https://github.com/leanprover-community/mathlib/commit/7590090)
chore(scripts): update nolints.txt ([#2643](https://github.com/leanprover-community/mathlib/pull/2643))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-10 00:45:41](https://github.com/leanprover-community/mathlib/commit/81f97bd)
chore(*): move to lean-3.11.0 ([#2632](https://github.com/leanprover-community/mathlib/pull/2632))
Related Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/lean.23211.20don't.20unfold.20irred.20defs
#### Estimated changes
modified leanpkg.toml

modified src/algebra/opposites.lean

modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean

modified src/category_theory/opposites.lean

modified src/category_theory/yoneda.lean

modified src/data/array/lemmas.lean

modified src/data/complex/basic.lean

modified src/data/padics/padic_norm.lean

modified src/data/pfun.lean

modified src/data/polynomial.lean
- \+/\- *def* pow_sub_pow_factor
- \+/\- *def* pow_sub_pow_factor

modified src/data/real/hyperreal.lean
- \+/\- *lemma* infinitesimal_add
- \+/\- *lemma* infinitesimal_neg
- \+/\- *lemma* infinitesimal_mul
- \+/\- *lemma* infinitesimal_add
- \+/\- *lemma* infinitesimal_neg
- \+/\- *lemma* infinitesimal_mul

modified src/geometry/manifold/real_instances.lean

modified src/measure_theory/bochner_integration.lean

modified src/set_theory/cofinality.lean

modified src/topology/metric_space/emetric_space.lean



## [2020-05-09 23:30:16](https://github.com/leanprover-community/mathlib/commit/a584d52)
chore(scripts): update nolints.txt ([#2642](https://github.com/leanprover-community/mathlib/pull/2642))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-09 20:30:31](https://github.com/leanprover-community/mathlib/commit/9f33b7d)
feat(algebra/ordered_*): arithmetic operations on monotone functions ([#2634](https://github.com/leanprover-community/mathlib/pull/2634))
Also move `strict_mono` to `order/basic` and add a module docstring.
#### Estimated changes
modified src/algebra/order_functions.lean
- \- *lemma* lt_iff_lt
- \- *lemma* injective
- \- *lemma* le_iff_le
- \- *lemma* monotone
- \- *lemma* strict_mono_of_monotone_of_injective
- \- *lemma* monotone_mul_left_of_nonneg
- \- *lemma* monotone_mul_right_of_nonneg
- \- *theorem* compares
- \- *def* strict_mono

modified src/algebra/ordered_field.lean
- \+ *lemma* monotone.div_const
- \+ *lemma* strict_mono.div_const

modified src/algebra/ordered_group.lean
- \+ *lemma* monotone.add
- \+ *lemma* monotone.add_const
- \+ *lemma* monotone.const_add
- \+ *lemma* monotone.add_strict_mono
- \+ *lemma* strict_mono.add_monotone

modified src/algebra/ordered_ring.lean
- \+ *lemma* monotone_mul_left_of_nonneg
- \+ *lemma* monotone_mul_right_of_nonneg
- \+ *lemma* monotone.mul_const
- \+ *lemma* monotone.const_mul
- \+ *lemma* monotone.mul
- \+ *lemma* strict_mono_mul_left_of_pos
- \+ *lemma* strict_mono_mul_right_of_pos
- \+ *lemma* strict_mono.mul_const
- \+ *lemma* strict_mono.const_mul
- \+ *lemma* strict_mono.mul_monotone
- \+ *lemma* monotone.mul_strict_mono
- \+ *lemma* strict_mono.mul

modified src/order/basic.lean
- \+ *lemma* comp
- \+ *lemma* lt_iff_lt
- \+ *lemma* injective
- \+ *lemma* le_iff_le
- \+ *lemma* monotone
- \+ *lemma* strict_mono_of_monotone_of_injective
- \+ *theorem* compares
- \+ *def* strict_mono



## [2020-05-09 20:30:29](https://github.com/leanprover-community/mathlib/commit/d04429f)
chore(logic/embedding,order/order_iso): review ([#2618](https://github.com/leanprover-community/mathlib/pull/2618))
* swap `inj` with `inj'` to match other bundled homomorphisms;
* make some arguments explicit to avoid `embedding.of_surjective _`
  in the pretty printer output;
* make `set_value` computable.
#### Estimated changes
modified src/computability/turing_machine.lean

modified src/data/finset.lean

modified src/data/finsupp.lean

modified src/data/pnat/intervals.lean

modified src/data/set/countable.lean

modified src/data/setoid.lean

modified src/group_theory/congruence.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/dimension.lean

modified src/logic/embedding.lean
- \+ *lemma* coe_image
- \+ *lemma* embedding_of_subset_apply_mk
- \+ *lemma* coe_embedding_of_subset_apply
- \+ *theorem* inj
- \+/\- *theorem* set_value_eq
- \- *theorem* inj'
- \+/\- *theorem* set_value_eq
- \+ *def* set_value
- \+/\- *def* embedding_of_subset
- \+/\- *def* embedding_of_subset

modified src/order/galois_connection.lean

modified src/order/order_iso.lean
- \+ *lemma* to_order_embedding_eq_coe
- \+ *theorem* inj
- \+ *theorem* ord
- \+ *theorem* ord
- \- *theorem* ord'
- \- *theorem* ord'

modified src/ring_theory/ideal_operations.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/noetherian.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal.lean



## [2020-05-09 20:30:27](https://github.com/leanprover-community/mathlib/commit/08d4316)
refactor(computability/turing_machine): add list_blank ([#2605](https://github.com/leanprover-community/mathlib/pull/2605))
This ended up being a major refactor of `computability.turing_machine`. It started as a change of the definition of turing machine so that the tape is a quotient of lists up to the relation "ends with blanks", but the file is quite old and I updated it to pass the linter as well. I'm not up to speed on the new documentation requirements, but now is a good time to request them for this file. This doesn't add many new theorems, it's mostly just fixes to make it compile again after the change. (Some of the turing machine constructions are also simplified.)
#### Estimated changes
modified src/computability/turing_machine.lean
- \+ *lemma* list_blank.bind_mk
- \+ *lemma* list_blank.cons_bind
- \+ *theorem* blank_extends.refl
- \+ *theorem* blank_extends.trans
- \+ *theorem* blank_extends.below_of_le
- \+ *theorem* blank_extends.above_of_le
- \+ *theorem* blank_rel.refl
- \+ *theorem* blank_rel.symm
- \+ *theorem* blank_rel.trans
- \+ *theorem* blank_rel.equivalence
- \+ *theorem* list_blank.head_mk
- \+ *theorem* list_blank.tail_mk
- \+ *theorem* list_blank.cons_mk
- \+ *theorem* list_blank.head_cons
- \+ *theorem* list_blank.tail_cons
- \+ *theorem* list_blank.cons_head_tail
- \+ *theorem* list_blank.exists_cons
- \+ *theorem* list_blank.nth_mk
- \+ *theorem* list_blank.nth_zero
- \+ *theorem* list_blank.nth_succ
- \+ *theorem* list_blank.ext
- \+ *theorem* list_blank.nth_modify_nth
- \+ *theorem* pointed_map.mk_val
- \+ *theorem* pointed_map.map_pt
- \+ *theorem* pointed_map.head_map
- \+ *theorem* list_blank.map_mk
- \+ *theorem* list_blank.head_map
- \+ *theorem* list_blank.tail_map
- \+ *theorem* list_blank.map_cons
- \+ *theorem* list_blank.nth_map
- \+ *theorem* proj_map_nth
- \+ *theorem* list_blank.map_modify_nth
- \+ *theorem* list_blank.append_mk
- \+ *theorem* list_blank.append_assoc
- \+ *theorem* tape.move_left_right
- \+ *theorem* tape.move_right_left
- \+ *theorem* tape.mk'_left
- \+ *theorem* tape.mk'_head
- \+ *theorem* tape.mk'_right
- \+ *theorem* tape.mk'_right₀
- \+ *theorem* tape.mk'_left_right₀
- \+ *theorem* tape.exists_mk'
- \+ *theorem* tape.move_left_mk'
- \+ *theorem* tape.move_right_mk'
- \+/\- *theorem* tape.nth_zero
- \+ *theorem* tape.right₀_nth
- \+ *theorem* tape.mk'_nth_nat
- \+/\- *theorem* tape.move_right_nth
- \+ *theorem* tape.move_right_n_head
- \+/\- *theorem* tape.write_self
- \+ *theorem* tape.write_mk'
- \+/\- *theorem* tape.map_fst
- \+/\- *theorem* tape.map_write
- \+ *theorem* tape.write_move_right_n
- \+/\- *theorem* tape.map_move
- \+ *theorem* tape.map_mk'
- \+ *theorem* tape.map_mk₂
- \+ *theorem* tape.map_mk₁
- \+/\- *theorem* machine.map_step
- \+/\- *theorem* map_init
- \+/\- *theorem* machine.map_respects
- \+/\- *theorem* tr_eval
- \+/\- *theorem* step_aux_move
- \+/\- *theorem* supports_stmt_move
- \+/\- *theorem* supports_stmt_write
- \+/\- *theorem* supports_stmt_read
- \+ *theorem* tr_tape_mk'
- \+/\- *theorem* step_aux_write
- \+ *theorem* stk_nth_val
- \+ *theorem* add_bottom_map
- \+ *theorem* add_bottom_modify_nth
- \+ *theorem* add_bottom_nth_snd
- \+ *theorem* add_bottom_nth_succ_fst
- \+ *theorem* add_bottom_head_fst
- \+/\- *theorem* supports_run
- \+/\- *theorem* tr_normal_run
- \+/\- *theorem* tr_stmts₁_run
- \+/\- *theorem* tr_respects_aux₂
- \+/\- *theorem* tr_respects_aux₁
- \+/\- *theorem* tr_respects_aux₃
- \+/\- *theorem* tape.nth_zero
- \+/\- *theorem* tape.move_right_nth
- \+/\- *theorem* tape.write_self
- \+/\- *theorem* tape.map_fst
- \+/\- *theorem* tape.map_write
- \+/\- *theorem* tape.map_move
- \- *theorem* tape.map_mk
- \- *theorem* dwrite_eq
- \- *theorem* dwrite_ne
- \- *theorem* dwrite_self
- \+/\- *theorem* machine.map_step
- \+/\- *theorem* map_init
- \+/\- *theorem* machine.map_respects
- \+/\- *theorem* tr_eval
- \- *theorem* tr_tape_drop_right
- \- *theorem* tr_tape_take_right
- \+/\- *theorem* step_aux_move
- \+/\- *theorem* step_aux_write
- \+/\- *theorem* supports_stmt_move
- \+/\- *theorem* supports_stmt_write
- \+/\- *theorem* supports_stmt_read
- \+/\- *theorem* supports_run
- \+/\- *theorem* tr_normal_run
- \+/\- *theorem* tr_respects_aux₁
- \+/\- *theorem* tr_respects_aux₂
- \+/\- *theorem* tr_respects_aux₃
- \+/\- *theorem* tr_stmts₁_run
- \+ *def* blank_extends
- \+ *def* blank_extends.above
- \+ *def* blank_rel
- \+ *def* blank_rel.above
- \+ *def* blank_rel.below
- \+ *def* blank_rel.setoid
- \+ *def* list_blank
- \+ *def* list_blank.mk
- \+ *def* list_blank.head
- \+ *def* list_blank.tail
- \+ *def* list_blank.cons
- \+ *def* list_blank.nth
- \+ *def* list_blank.modify_nth
- \+ *def* list_blank.map
- \+ *def* proj
- \+ *def* list_blank.append
- \+ *def* list_blank.bind
- \+ *def* tape.left₀
- \+ *def* tape.right₀
- \+/\- *def* tape.move
- \+/\- *def* tape.mk'
- \+ *def* tape.mk₂
- \+ *def* tape.mk₁
- \+/\- *def* tape.nth
- \+/\- *def* tape.write
- \+/\- *def* tape.map
- \+/\- *def* eval
- \+/\- *def* stmt.map
- \+/\- *def* cfg.map
- \+/\- *def* supports
- \+/\- *def* init
- \+/\- *def* eval
- \+/\- *def* tr_tape'
- \+/\- *def* tr_tape
- \+/\- *def* supports
- \+/\- *def* init
- \+/\- *def* eval
- \+/\- *def* Γ'
- \+ *def* add_bottom
- \- *def* tape
- \- *def* tape.mk
- \+/\- *def* tape.mk'
- \+/\- *def* tape.move
- \+/\- *def* tape.nth
- \+/\- *def* tape.write
- \+/\- *def* tape.map
- \- *def* pointed_map
- \- *def* dwrite
- \+/\- *def* eval
- \+/\- *def* stmt.map
- \+/\- *def* cfg.map
- \+/\- *def* init
- \+/\- *def* eval
- \+/\- *def* supports
- \+/\- *def* tr_tape'
- \+/\- *def* tr_tape
- \+/\- *def* init
- \+/\- *def* eval
- \+/\- *def* supports
- \- *def* stackel.is_bottom
- \- *def* stackel.is_top
- \- *def* stackel.get
- \- *def* stackel_equiv
- \+/\- *def* Γ'
- \- *def* tr_stk

modified src/data/list/basic.lean
- \+ *lemma* nth_concat_length
- \- *lemma* nth_concat_length:
- \+ *theorem* head'_map

modified src/data/nat/basic.lean
- \+ *theorem* add_sub_eq_max



## [2020-05-09 20:30:25](https://github.com/leanprover-community/mathlib/commit/b769846)
feat(tactic/norm_num): new all-lean norm_num ([#2589](https://github.com/leanprover-community/mathlib/pull/2589))
This is a first draft of the lean replacement for `tactic.norm_num` in core. This isn't completely polished yet; the rest of `norm_num` can now be a little less "global-recursive" since the primitives for e.g. adding and multiplying natural numbers are exposed.
I'm also trying out a new approach using functions like `match_neg` and `match_numeral` instead of directly pattern matching on exprs, because this generates smaller (and hopefully more efficient) code. (Without this, some of the matches were hitting the equation compiler depth limit.)
I'm open to new feature suggestions as well here. `nat.succ` and coercions seem useful to support in the core part, and additional flexibility using `def_replacer` is also on the agenda.
#### Estimated changes
modified src/analysis/specific_limits.lean

modified src/data/rat/meta_defs.lean

modified src/tactic/core.lean

modified src/tactic/norm_num.lean
- \+ *lemma* pow_bit0
- \+ *lemma* pow_bit1
- \+ *lemma* from_nat_pow
- \+ *lemma* lt_neg_pos
- \+ *lemma* le_neg_pos
- \+ *lemma* nat_div
- \+ *lemma* int_div
- \+ *lemma* nat_mod
- \+ *lemma* int_mod
- \+ *lemma* int_div_neg
- \+ *lemma* int_mod_neg
- \+/\- *lemma* min_fac_helper_3
- \+/\- *lemma* min_fac_helper_4
- \- *lemma* pow_bit0_helper
- \- *lemma* pow_bit1_helper
- \- *lemma* lt_add_of_pos_helper
- \- *lemma* nat_div_helper
- \- *lemma* int_div_helper
- \- *lemma* nat_mod_helper
- \- *lemma* int_mod_helper
- \+/\- *lemma* min_fac_helper_3
- \+/\- *lemma* min_fac_helper_4
- \+ *theorem* zero_succ
- \+ *theorem* one_succ
- \+ *theorem* bit0_succ
- \+ *theorem* bit1_succ
- \+ *theorem* zero_adc
- \+ *theorem* adc_zero
- \+ *theorem* one_add
- \+ *theorem* add_bit0_bit0
- \+ *theorem* add_bit0_bit1
- \+ *theorem* add_bit1_bit0
- \+ *theorem* add_bit1_bit1
- \+ *theorem* adc_one_one
- \+ *theorem* adc_bit0_one
- \+ *theorem* adc_one_bit0
- \+ *theorem* adc_bit1_one
- \+ *theorem* adc_one_bit1
- \+ *theorem* adc_bit0_bit0
- \+ *theorem* adc_bit1_bit0
- \+ *theorem* adc_bit0_bit1
- \+ *theorem* adc_bit1_bit1
- \+ *theorem* bit0_mul
- \+ *theorem* mul_bit0'
- \+ *theorem* mul_bit0_bit0
- \+ *theorem* mul_bit1_bit1
- \+ *theorem* ne_zero_of_pos
- \+ *theorem* ne_zero_neg
- \+ *theorem* clear_denom_div
- \+ *theorem* clear_denom_add
- \+ *theorem* add_pos_neg_pos
- \+ *theorem* add_pos_neg_neg
- \+ *theorem* add_neg_pos_pos
- \+ *theorem* add_neg_pos_neg
- \+ *theorem* add_neg_neg
- \+ *theorem* clear_denom_simple_nat
- \+ *theorem* clear_denom_simple_div
- \+ *theorem* clear_denom_mul
- \+ *theorem* mul_neg_pos
- \+ *theorem* mul_pos_neg
- \+ *theorem* mul_neg_neg
- \+ *theorem* inv_neg
- \+ *theorem* inv_one
- \+ *theorem* inv_one_div
- \+ *theorem* inv_div_one
- \+ *theorem* inv_div
- \+ *theorem* div_eq
- \+ *theorem* sub_pos
- \+ *theorem* sub_neg
- \+ *theorem* sub_nat_pos
- \+ *theorem* sub_nat_neg
- \+ *theorem* nonneg_pos
- \+ *theorem* lt_one_bit0
- \+ *theorem* lt_one_bit1
- \+ *theorem* lt_bit0_bit0
- \+ *theorem* lt_bit0_bit1
- \+ *theorem* lt_bit1_bit0
- \+ *theorem* lt_bit1_bit1
- \+ *theorem* le_one_bit0
- \+ *theorem* le_one_bit1
- \+ *theorem* le_bit0_bit0
- \+ *theorem* le_bit0_bit1
- \+ *theorem* le_bit1_bit0
- \+ *theorem* le_bit1_bit1
- \+ *theorem* sle_one_bit0
- \+ *theorem* sle_one_bit1
- \+ *theorem* sle_bit0_bit0
- \+ *theorem* sle_bit0_bit1
- \+ *theorem* sle_bit1_bit0
- \+ *theorem* sle_bit1_bit1
- \+ *theorem* clear_denom_lt
- \+ *theorem* clear_denom_le
- \+ *theorem* nat_cast_zero
- \+ *theorem* nat_cast_one
- \+ *theorem* nat_cast_bit0
- \+ *theorem* nat_cast_bit1
- \+ *theorem* int_cast_zero
- \+ *theorem* int_cast_one
- \+ *theorem* int_cast_bit0
- \+ *theorem* int_cast_bit1
- \+ *theorem* rat_cast_bit0
- \+ *theorem* rat_cast_bit1
- \+ *theorem* rat_cast_div
- \+ *theorem* int_cast_neg
- \+ *theorem* rat_cast_neg
- \+ *theorem* nat_cast_ne
- \+ *theorem* int_cast_ne
- \+ *theorem* rat_cast_ne
- \+ *theorem* not_refl_false_intro
- \+ *theorem* nat_succ_eq
- \+ *theorem* dvd_eq_nat
- \+ *theorem* dvd_eq_int
- \- *theorem* bit0_zero
- \- *theorem* bit1_zero

modified test/norm_num.lean



## [2020-05-09 17:40:41](https://github.com/leanprover-community/mathlib/commit/20c7418)
chore(data/finset): drop `to_set`, use `has_lift` instead ([#2629](https://github.com/leanprover-community/mathlib/pull/2629))
Also cleanup `coe_to_finset` lemmas. Now we have `set.finite.coe_to_finset` and `set.coe_to_finset`.
#### Estimated changes
modified src/algebra/direct_sum.lean

modified src/data/finset.lean
- \+ *lemma* coe_injective
- \- *lemma* to_set_injective
- \- *lemma* to_set_sdiff
- \- *def* to_set

modified src/data/finsupp.lean

modified src/data/fintype/basic.lean
- \+ *theorem* coe_to_finset

modified src/data/set/finite.lean
- \+/\- *lemma* finite.coe_to_finset
- \+/\- *lemma* coe_preimage
- \+/\- *lemma* finite.coe_to_finset
- \- *lemma* coe_to_finset
- \- *lemma* coe_to_finset'
- \+/\- *lemma* coe_preimage

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finsupp.lean

modified src/ring_theory/adjoin.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/noetherian.lean

modified src/set_theory/ordinal.lean



## [2020-05-09 14:34:49](https://github.com/leanprover-community/mathlib/commit/e1192f3)
feat(data/nat/basic): add `mod_add_mod` and `add_mod_mod` ([#2635](https://github.com/leanprover-community/mathlib/pull/2635))
Added the `mod_add_mod` and `add_mod_mod` lemmas for `data.nat.basic`. I copied them from `data.int.basic`, and just changed the data type. Would there be issues with it being labelled `@[simp]`?
Also, would it make sense to refactor `add_mod` above it to use `mod_add_mod` and `add_mod_mod`? It'd make it considerably shorter.
(Tangential note, there's a disparity between the `mod` lemmas for `nat` and the `mod` lemmas for `int`, for example `int` doesn't have `add_mod`, should that be added in a separate PR?)
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* add_mod
- \+ *lemma* mul_mod

modified src/data/nat/basic.lean
- \+ *theorem* mod_add_mod
- \+ *theorem* add_mod_mod
- \+ *theorem* add_mod_eq_add_mod_right
- \+ *theorem* add_mod_eq_add_mod_left



## [2020-05-09 08:33:21](https://github.com/leanprover-community/mathlib/commit/96efc22)
feat(data/nat/cast): nat.cast_with_bot ([#2636](https://github.com/leanprover-community/mathlib/pull/2636))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/with_bot/near/196979007
#### Estimated changes
modified src/data/nat/cast.lean
- \+ *theorem* nat.cast_with_bot



## [2020-05-08 21:01:31](https://github.com/leanprover-community/mathlib/commit/67e19cd)
feat(src/ring_theory/algebra): define equivalence of algebras ([#2625](https://github.com/leanprover-community/mathlib/pull/2625))
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+ *lemma* coe_ring_equiv
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* commutes
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* coe_to_alg_equiv
- \+ *lemma* injective
- \+ *lemma* surjective
- \+ *lemma* bijective
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans



## [2020-05-08 16:39:26](https://github.com/leanprover-community/mathlib/commit/fc8c4b9)
chore(`analysis/normed_space/banach`): minor review ([#2631](https://github.com/leanprover-community/mathlib/pull/2631))
* move comment to module docstring;
* don't import `bounded_linear_maps`;
* reuse `open_mapping` in `linear_equiv.continuous_symm`;
* add a few `simp` lemmas.
#### Estimated changes
modified src/analysis/normed_space/banach.lean
- \+ *lemma* coe_fn_to_continuous_linear_equiv_of_continuous
- \+ *lemma* coe_fn_to_continuous_linear_equiv_of_continuous_symm
- \+ *theorem* continuous_symm
- \- *theorem* linear_equiv.continuous_symm
- \+ *def* to_continuous_linear_equiv_of_continuous
- \- *def* linear_equiv.to_continuous_linear_equiv_of_continuous



## [2020-05-08 01:30:44](https://github.com/leanprover-community/mathlib/commit/ac3fb4e)
chore(scripts): update nolints.txt ([#2628](https://github.com/leanprover-community/mathlib/pull/2628))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-07 22:43:02](https://github.com/leanprover-community/mathlib/commit/a7e8039)
feat(data/equiv/encodable): `ulower` lowers countable types to `Type 0` ([#2574](https://github.com/leanprover-community/mathlib/pull/2574))
Given a type `α : Type u`, we can lift it into a higher universe using `ulift α : Type (max u v)`.  This PR introduces an analogous construction going in the other direction.  Given an encodable (= countable) type `α : Type u`, we can lower it to the very bottom using `ulower α : Type 0`.  The equivalence is primitive recursive if the type is primcodable.
The definition of the equivalence was already present as `encodable.equiv_range_encode`.  However it is very inconvenient to use since it requires decidability instances (`encodable.decidable_range_encode`) that are not enabled by default because they would introduce overlapping instances that are not definitionally equal.
#### Estimated changes
modified src/computability/primrec.lean
- \+ *theorem* option_get_or_else
- \+ *theorem* subtype_mk
- \+ *theorem* option_get
- \+ *theorem* ulower_down
- \+ *theorem* ulower_up

modified src/data/equiv/encodable.lean
- \+ *lemma* subtype.encode_eq
- \+ *lemma* down_up
- \+ *lemma* up_down
- \+ *lemma* up_eq_up
- \+ *lemma* down_eq_down
- \+ *def* ulower
- \+ *def* equiv
- \+ *def* down
- \+ *def* up



## [2020-05-07 21:02:37](https://github.com/leanprover-community/mathlib/commit/ed453c7)
chore(data/polynomial): remove unused argument ([#2626](https://github.com/leanprover-community/mathlib/pull/2626))
#### Estimated changes
modified src/data/polynomial.lean
- \+/\- *lemma* map_injective
- \+/\- *lemma* map_injective



## [2020-05-07 18:46:03](https://github.com/leanprover-community/mathlib/commit/bdce195)
chore(linear_algebra/basic): review ([#2616](https://github.com/leanprover-community/mathlib/pull/2616))
* several new `simp` lemmas;
* use `linear_equiv.coe_coe` instead of `coe_apply`;
* rename `sup_quotient_to_quotient_inf` to `quotient_inf_to_sup_quotient` because it better reflects the definition; similarly for `equiv`.
* make `general_linear_group` reducible.
#### Estimated changes
modified src/algebra/module.lean
- \+/\- *lemma* neg_mem_iff
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* mk_eq_zero
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_eq_zero
- \+ *lemma* coe_mem
- \+/\- *lemma* neg_mem_iff
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* mk_eq_zero

modified src/analysis/convex/cone.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* map_coe
- \+ *lemma* mem_sup'
- \+ *lemma* quot_hom_ext
- \+ *lemma* range_coprod
- \+ *lemma* submodule.sup_eq_range
- \+ *lemma* comap_subtype_eq_top
- \+ *lemma* comap_subtype_self
- \+ *lemma* range_range_restrict
- \+/\- *lemma* disjoint_iff_comap_eq_bot
- \+ *lemma* coe_to_equiv
- \+ *lemma* coe_to_add_equiv
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply
- \+ *lemma* map_eq_comap
- \+/\- *lemma* map_coe
- \+/\- *lemma* disjoint_iff_comap_eq_bot
- \+ *theorem* mem_range_self
- \+ *theorem* map_coe_ker
- \+ *theorem* coe_coe
- \- *theorem* coe_apply
- \+ *def* range_restrict
- \+ *def* quotient_inf_to_sup_quotient
- \+/\- *def* general_linear_group
- \- *def* sup_quotient_to_quotient_inf
- \+/\- *def* general_linear_group



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
modified src/data/set/intervals/basic.lean

modified src/linear_algebra/basic.lean

modified src/order/boolean_algebra.lean

modified src/order/bounded_lattice.lean

modified src/order/complete_boolean_algebra.lean

modified src/order/complete_lattice.lean
- \+ *lemma* ord_continuous.sup
- \+ *lemma* ord_continuous.mono
- \- *lemma* ord_continuous_sup
- \- *lemma* ord_continuous_mono

modified src/order/filter/basic.lean

modified src/order/filter/lift.lean

modified src/order/fixed_points.lean

modified src/order/lattice.lean
- \+ *lemma* sup_ind
- \+/\- *lemma* inf_le_inf_right
- \+/\- *lemma* inf_le_inf_left
- \+ *lemma* inf_ind
- \+/\- *lemma* inf_le_inf_left
- \+/\- *lemma* inf_le_inf_right
- \+ *theorem* sup_eq_left
- \+ *theorem* left_eq_sup
- \+ *theorem* sup_eq_right
- \+ *theorem* right_eq_sup
- \+ *theorem* inf_eq_left
- \+ *theorem* left_eq_inf
- \+ *theorem* inf_eq_right
- \+ *theorem* right_eq_inf

modified src/topology/basic.lean

modified src/topology/continuous_on.lean

modified src/topology/dense_embedding.lean

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/uniform_embedding.lean



## [2020-05-07 13:09:37](https://github.com/leanprover-community/mathlib/commit/6c48444)
feat(algebra/lie_algebra): `lie_algebra.of_associative_algebra` is functorial ([#2620](https://github.com/leanprover-community/mathlib/pull/2620))
More precisely we:
  * define the Lie algebra homomorphism associated to a morphism of associative algebras
  * prove that the correspondence is functorial
  * prove that subalgebras and Lie subalgebras correspond
#### Estimated changes
modified src/algebra/lie_algebra.lean
- \+ *lemma* of_associative_algebra_hom_id
- \+ *lemma* of_associative_algebra_hom_comp
- \+ *def* of_associative_algebra_hom
- \+ *def* lie_subalgebra_of_subalgebra

modified src/ring_theory/algebra.lean
- \+ *lemma* mul_mem



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
modified src/algebra/group_power.lean
- \+ *theorem* two_smul'
- \- *theorem* two_smul

modified src/algebra/midpoint.lean
- \+ *lemma* midpoint_add_self
- \+/\- *lemma* midpoint_def
- \+ *lemma* midpoint_zero_add
- \+ *lemma* coe_of_map_midpoint
- \+ *lemma* reflection_midpoint_left
- \+ *lemma* reflection_midpoint_right
- \+/\- *lemma* midpoint_def
- \+ *def* of_map_midpoint

modified src/algebra/module.lean
- \+ *theorem* two_smul

modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.norm_two

created src/analysis/normed_space/reflection.lean
- \+ *lemma* equiv.reflection_fixed_iff_of_module
- \+ *lemma* reflection_apply
- \+ *lemma* reflection_to_equiv
- \+ *lemma* reflection_self
- \+ *lemma* reflection_involutive
- \+ *lemma* reflection_symm
- \+ *lemma* reflection_dist_fixed
- \+ *lemma* reflection_dist_self'
- \+ *lemma* reflection_midpoint_left
- \+ *lemma* reflection_midpoint_right
- \+ *lemma* reflection_fixed_iff
- \+ *lemma* reflection_dist_self
- \+ *lemma* reflection_dist_self_real
- \+ *def* reflection

modified src/data/equiv/mul_add.lean
- \+ *lemma* reflection_apply
- \+ *lemma* reflection_self
- \+ *lemma* reflection_involutive
- \+ *lemma* reflection_symm
- \+ *lemma* reflection_fixed_iff_of_bit0_inj
- \+ *def* reflection

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry.right_inv
- \+ *lemma* to_equiv_inj
- \+/\- *lemma* ext
- \+ *lemma* coe_to_homeomorph
- \+/\- *lemma* to_homeomorph_to_equiv
- \+/\- *lemma* isometry.isometric_on_range_apply
- \- *lemma* isometry.inv
- \- *lemma* isometry_inv_fun
- \+/\- *lemma* ext
- \- *lemma* coe_eq_to_homeomorph
- \+/\- *lemma* to_homeomorph_to_equiv
- \+/\- *lemma* isometry.isometric_on_range_apply
- \+/\- *theorem* isometry.edist_eq
- \+/\- *theorem* isometry.dist_eq
- \+/\- *theorem* isometry.edist_eq
- \+/\- *theorem* isometry.dist_eq



## [2020-05-07 07:12:04](https://github.com/leanprover-community/mathlib/commit/a6415d7)
chore(data/set/basic): use implicit args in `set.ext_iff` ([#2619](https://github.com/leanprover-community/mathlib/pull/2619))
Most other `ext_iff` lemmas use implicit arguments, let `set.ext_iff` use them too.
#### Estimated changes
modified src/data/finset.lean

modified src/data/semiquot.lean

modified src/data/set/basic.lean
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext_iff

modified src/data/setoid.lean

modified src/linear_algebra/basic.lean

modified src/set_theory/zfc.lean

modified src/topology/separation.lean

modified src/topology/subset_properties.lean



## [2020-05-07 02:39:51](https://github.com/leanprover-community/mathlib/commit/f6edeba)
chore(scripts): update nolints.txt ([#2622](https://github.com/leanprover-community/mathlib/pull/2622))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-07 00:42:46](https://github.com/leanprover-community/mathlib/commit/a8eafb6)
chore(scripts): update nolints.txt ([#2621](https://github.com/leanprover-community/mathlib/pull/2621))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



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
modified src/data/set/countable.lean
- \+ *lemma* countable.exists_surjective
- \+ *lemma* countable.mono
- \+ *lemma* countable.image
- \+ *lemma* countable.bUnion
- \+ *lemma* countable.sUnion
- \+ *lemma* countable.union
- \+ *lemma* countable.insert
- \+ *lemma* finite.countable
- \+ *lemma* finset.countable_to_set
- \- *lemma* exists_surjective_of_countable
- \- *lemma* countable_subset
- \- *lemma* countable_image
- \- *lemma* countable_bUnion
- \- *lemma* countable_sUnion
- \- *lemma* countable_union
- \- *lemma* countable_insert
- \- *lemma* countable_finite

modified src/measure_theory/integration.lean
- \+/\- *lemma* range_const
- \+/\- *lemma* range_const

modified src/measure_theory/measure_space.lean

modified src/order/filter/bases.lean
- \+/\- *def* countable_filter_basis
- \+/\- *def* countable_filter_basis

modified src/topology/bases.lean

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/baire.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean



## [2020-05-06 19:39:53](https://github.com/leanprover-community/mathlib/commit/c3d76d0)
chore(*): a few missing `simp` lemmas ([#2615](https://github.com/leanprover-community/mathlib/pull/2615))
Also replaces `monoid_hom.exists_inv_of_comp_exists_inv` with `monoid_hom.map_exists_right_inv` and adds `monoid_hom.map_exists_left_inv`.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* map_mul_eq_one
- \+ *lemma* map_exists_right_inv
- \+ *lemma* map_exists_left_inv
- \+ *lemma* id_apply
- \- *lemma* exists_inv_of_comp_exists_inv

modified src/data/equiv/mul_add.lean
- \+ *theorem* coe_mk
- \+ *theorem* coe_symm_mk

modified src/data/sigma/basic.lean
- \+ *theorem* sigma.eta



## [2020-05-06 19:39:51](https://github.com/leanprover-community/mathlib/commit/460d9d4)
refactor(data/equiv/local_equiv, topology/local_homeomorph): use coercions ([#2603](https://github.com/leanprover-community/mathlib/pull/2603))
Local equivs and local homeomorphisms use `e.to_fun x` and `e.inv_fun x`, instead of coercions as in most of mathlib, as there were problems with coercions that made them unusable in manifolds. These problems have been fixed in Lean 3.10, so we switch to coercions for them also.
This is 95% a refactor PR, erasing `.to_fun` and replacing `.inv_fun` with `.symm` in several files, and fixing proofs. Plus a few simp lemmas on the coercions to let things go smoothly. I have also linted all the files I have touched.
#### Estimated changes
modified src/analysis/asymptotics.lean

modified src/analysis/calculus/inverse.lean
- \+ *lemma* to_local_homeomorph_coe
- \+ *lemma* to_local_homeomorph_coe
- \- *lemma* to_local_homeomorph_to_fun
- \- *lemma* to_local_homeomorph_to_fun

modified src/data/equiv/local_equiv.lean
- \+ *lemma* to_fun_as_coe
- \+ *lemma* inv_fun_as_coe
- \+ *lemma* map_source
- \+ *lemma* map_target
- \+ *lemma* left_inv
- \+ *lemma* right_inv
- \+/\- *lemma* bij_on_source
- \+/\- *lemma* image_source_eq_target
- \+/\- *lemma* source_subset_preimage_target
- \+/\- *lemma* inv_image_target_eq_source
- \+/\- *lemma* target_subset_preimage_source
- \+ *lemma* restr_coe
- \+ *lemma* restr_coe_symm
- \+/\- *lemma* restr_target
- \+ *lemma* refl_coe
- \+ *lemma* of_set_coe
- \+ *lemma* coe_trans
- \+ *lemma* coe_trans_symm
- \+/\- *lemma* trans_source
- \+/\- *lemma* trans_source'
- \+/\- *lemma* trans_source''
- \+/\- *lemma* image_trans_source
- \+/\- *lemma* trans_target
- \+/\- *lemma* trans_target'
- \+/\- *lemma* trans_target''
- \+/\- *lemma* inv_image_trans_target
- \+ *lemma* prod_coe
- \+ *lemma* prod_coe_symm
- \+ *lemma* to_local_equiv_coe
- \+ *lemma* to_local_equiv_symm_coe
- \- *lemma* symm_to_fun
- \- *lemma* symm_inv_fun
- \+/\- *lemma* bij_on_source
- \+/\- *lemma* image_source_eq_target
- \+/\- *lemma* source_subset_preimage_target
- \+/\- *lemma* inv_image_target_eq_source
- \+/\- *lemma* target_subset_preimage_source
- \- *lemma* restr_to_fun
- \- *lemma* restr_inv_fun
- \+/\- *lemma* restr_target
- \- *lemma* refl_to_fun
- \- *lemma* refl_inv_fun
- \- *lemma* of_set_to_fun
- \- *lemma* of_set_inv_fun
- \- *lemma* trans_to_fun
- \- *lemma* trans_apply
- \- *lemma* trans_inv_fun
- \- *lemma* trans_inv_apply
- \+/\- *lemma* trans_source
- \+/\- *lemma* trans_source'
- \+/\- *lemma* trans_source''
- \+/\- *lemma* image_trans_source
- \+/\- *lemma* trans_target
- \+/\- *lemma* trans_target'
- \+/\- *lemma* trans_target''
- \+/\- *lemma* inv_image_trans_target
- \- *lemma* prod_to_fun
- \- *lemma* prod_inv_fun
- \- *lemma* to_local_equiv_to_fun
- \- *lemma* to_local_equiv_inv_fun
- \+ *theorem* coe_mk
- \+ *theorem* coe_symm_mk

modified src/geometry/manifold/basic_smooth_bundle.lean
- \+ *lemma* coe_chart_at_fst
- \+ *lemma* coe_chart_at_symm_fst
- \+ *lemma* tangent_bundle_model_space_coe_chart_at
- \+ *lemma* tangent_bundle_model_space_coe_chart_at_symm
- \- *lemma* chart_at_to_fun_fst
- \- *lemma* chart_at_inv_fun_fst
- \+ *def* trivial_basic_smooth_bundle_core

modified src/geometry/manifold/manifold.lean
- \+ *def* continuous_pregroupoid
- \+/\- *def* continuous_groupoid
- \+/\- *def* continuous_groupoid

modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* model_with_corners.mdifferentiable
- \+ *lemma* model_with_corners.mdifferentiable_on_symm
- \+ *lemma* mdifferentiable_at_atlas
- \+ *lemma* mdifferentiable_on_atlas
- \+ *lemma* mdifferentiable_at_atlas_symm
- \+ *lemma* mdifferentiable_on_atlas_symm
- \+ *lemma* bundle_mfderiv_chart
- \+ *lemma* bundle_mfderiv_chart_symm
- \+ *lemma* mdifferentiable_at_symm
- \+ *lemma* symm_comp_deriv
- \+ *lemma* comp_symm_deriv
- \- *lemma* model_with_corners_mdifferentiable_on_to_fun
- \- *lemma* model_with_corners_mdifferentiable_on_inv_fun
- \- *lemma* mdifferentiable_at_atlas_to_fun
- \- *lemma* mdifferentiable_on_atlas_to_fun
- \- *lemma* mdifferentiable_at_atlas_inv_fun
- \- *lemma* mdifferentiable_on_atlas_inv_fun
- \- *lemma* bundle_mfderiv_chart_to_fun
- \- *lemma* bundle_mfderiv_chart_inv_fun
- \- *lemma* mdifferentiable_at_to_fun
- \- *lemma* mdifferentiable_at_inv_fun
- \- *lemma* inv_fun_to_fun_deriv
- \- *lemma* to_fun_inv_fun_deriv

modified src/geometry/manifold/real_instances.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners.to_local_equiv_coe
- \+ *lemma* model_with_corners.mk_coe
- \+ *lemma* model_with_corners.to_local_equiv_coe_symm
- \+ *lemma* model_with_corners.mk_coe_symm
- \+ *lemma* model_with_corners.unique_diff
- \+ *lemma* model_with_corners.continuous_symm
- \+/\- *lemma* model_with_corners_self_local_equiv
- \+ *lemma* model_with_corners_self_coe
- \+ *lemma* model_with_corners_self_coe_symm
- \+ *lemma* model_with_corners.target
- \+ *lemma* model_with_corners.left_inv
- \+ *lemma* model_with_corners.left_inv'
- \+ *lemma* model_with_corners.right_inv
- \+ *lemma* model_with_corners.unique_diff_preimage
- \+ *lemma* model_with_corners.unique_diff_preimage_source
- \+ *lemma* model_with_corners.unique_diff_at_image
- \+ *lemma* ext_chart_at_continuous_on
- \+ *lemma* ext_chart_at_continuous_at
- \+ *lemma* ext_chart_at_continuous_on_symm
- \+ *lemma* ext_chart_at_coe
- \+ *lemma* ext_chart_at_coe_symm
- \+ *lemma* ext_chart_continuous_at_symm'
- \+ *lemma* ext_chart_continuous_at_symm
- \+/\- *lemma* ext_chart_preimage_inter_eq
- \+/\- *lemma* model_with_corners_self_local_equiv
- \- *lemma* model_with_corners_target
- \- *lemma* model_with_corners_left_inv
- \- *lemma* model_with_corners_inv_fun_comp
- \- *lemma* model_with_corners_right_inv
- \- *lemma* ext_chart_at_continuous_on_to_fun
- \- *lemma* ext_chart_at_continuous_at_to_fun
- \- *lemma* ext_chart_at_continuous_on_inv_fun
- \- *lemma* ext_chart_continuous_at_inv_fun'
- \- *lemma* ext_chart_continuous_at_inv_fun
- \+/\- *lemma* ext_chart_preimage_inter_eq

modified src/topology/local_homeomorph.lean
- \+ *lemma* continuous_on_symm
- \+ *lemma* mk_coe
- \+ *lemma* mk_coe_symm
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* inv_fun_eq_coe
- \+ *lemma* coe_coe
- \+ *lemma* coe_coe_symm
- \+ *lemma* map_source
- \+ *lemma* map_target
- \+ *lemma* left_inv
- \+ *lemma* right_inv
- \+ *lemma* continuous_at_symm
- \+ *lemma* tendsto_symm
- \+/\- *lemma* image_open_of_open
- \+ *lemma* restr_coe
- \+ *lemma* restr_coe_symm
- \+/\- *lemma* refl_source
- \+/\- *lemma* refl_target
- \+/\- *lemma* refl_symm
- \+ *lemma* refl_coe
- \+/\- *lemma* of_set_source
- \+/\- *lemma* of_set_target
- \+ *lemma* of_set_coe
- \+/\- *lemma* of_set_symm
- \+ *lemma* coe_trans
- \+ *lemma* coe_trans_symm
- \+/\- *lemma* trans_source
- \+/\- *lemma* trans_source'
- \+/\- *lemma* trans_source''
- \+/\- *lemma* image_trans_source
- \+/\- *lemma* trans_target
- \+/\- *lemma* trans_target'
- \+/\- *lemma* trans_target''
- \+/\- *lemma* inv_image_trans_target
- \+/\- *lemma* apply_eq_of_eq_on_source
- \+/\- *lemma* inv_apply_eq_of_eq_on_source
- \+ *lemma* prod_coe
- \+ *lemma* prod_coe_symm
- \+ *lemma* to_homeomorph_coe
- \+ *lemma* to_homeomorph_symm_coe
- \+/\- *lemma* to_local_homeomorph_source
- \+/\- *lemma* to_local_homeomorph_target
- \+ *lemma* to_local_homeomorph_coe
- \+ *lemma* to_local_homeomorph_coe_symm
- \- *lemma* symm_to_fun
- \- *lemma* symm_inv_fun
- \- *lemma* continuous_at_to_fun
- \- *lemma* continuous_at_inv_fun
- \- *lemma* inv_fun_tendsto
- \+/\- *lemma* image_open_of_open
- \- *lemma* restr_to_fun
- \- *lemma* restr_inv_fun
- \+/\- *lemma* refl_source
- \+/\- *lemma* refl_target
- \+/\- *lemma* refl_symm
- \- *lemma* refl_to_fun
- \- *lemma* refl_inv_fun
- \+/\- *lemma* of_set_source
- \+/\- *lemma* of_set_target
- \- *lemma* of_set_to_fun
- \- *lemma* of_set_inv_fun
- \+/\- *lemma* of_set_symm
- \- *lemma* trans_to_fun
- \- *lemma* trans_inv_fun
- \+/\- *lemma* trans_source
- \+/\- *lemma* trans_source'
- \+/\- *lemma* trans_source''
- \+/\- *lemma* image_trans_source
- \+/\- *lemma* trans_target
- \+/\- *lemma* trans_target'
- \+/\- *lemma* trans_target''
- \+/\- *lemma* inv_image_trans_target
- \+/\- *lemma* apply_eq_of_eq_on_source
- \+/\- *lemma* inv_apply_eq_of_eq_on_source
- \- *lemma* prod_to_fun
- \- *lemma* prod_inv_fun
- \- *lemma* to_homeomorph_to_fun
- \- *lemma* to_homeomorph_inv_fun
- \+/\- *lemma* to_local_homeomorph_source
- \+/\- *lemma* to_local_homeomorph_target
- \- *lemma* to_local_homeomorph_to_fun
- \- *lemma* to_local_homeomorph_inv_fun

modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle_trivialization.coe_coe
- \+ *lemma* bundle_trivialization.coe_mk
- \+ *lemma* bundle_trivialization.coe_fst



## [2020-05-06 19:39:49](https://github.com/leanprover-community/mathlib/commit/b1c0398)
feat(analysis/analytic/composition): the composition of formal series is associative ([#2513](https://github.com/leanprover-community/mathlib/pull/2513))
The composition of formal multilinear series is associative. I will need this when doing the analytic local inverse theorem, and I was surprised by how nontrivial this is: one should show that two double sums coincide by reindexing, but the reindexing is combinatorially tricky (it involves joining and splitting lists carefully). 
Preliminary material on lists, sums and compositions is done in [#2501](https://github.com/leanprover-community/mathlib/pull/2501) and [#2554](https://github.com/leanprover-community/mathlib/pull/2554), and the proof is in this PR.
#### Estimated changes
modified src/analysis/analytic/composition.lean
- \+ *lemma* apply_composition_ones
- \+ *lemma* comp_along_composition_apply
- \+ *lemma* comp_coeff_zero
- \+ *lemma* comp_coeff_zero'
- \+ *lemma* comp_coeff_zero''
- \+ *lemma* id_apply_one
- \+ *lemma* id_apply_one'
- \+ *lemma* id_apply_ne_one
- \+ *lemma* sigma_composition_eq_iff
- \+ *lemma* sigma_pi_composition_eq_iff
- \+ *lemma* length_gather
- \+ *lemma* length_sigma_composition_aux
- \+ *lemma* blocks_fun_sigma_composition_aux
- \+ *lemma* size_up_to_size_up_to_add
- \+ *theorem* comp_id
- \+ *theorem* id_comp
- \+ *theorem* comp_assoc
- \+ *def* id
- \+ *def* gather
- \+ *def* sigma_composition_aux
- \+ *def* sigma_equiv_sigma_pi

modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* congr

modified src/combinatorics/composition.lean
- \+ *lemma* index_embedding
- \+ *lemma* inv_embedding_comp
- \+ *lemma* blocks_fun_congr
- \+ *lemma* nth_le_split_wrt_composition_aux
- \+ *lemma* nth_le_split_wrt_composition
- \+ *def* blocks_fin_equiv



## [2020-05-06 16:31:27](https://github.com/leanprover-community/mathlib/commit/0a7ff10)
feat(algebra/units): some norm_cast attributes ([#2612](https://github.com/leanprover-community/mathlib/pull/2612))
#### Estimated changes
modified src/algebra/group/units.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_inv

modified src/algebra/group_power.lean
- \+/\- *lemma* units.coe_pow
- \+/\- *lemma* units.coe_pow

modified src/group_theory/subgroup.lean
- \+/\- *lemma* is_subgroup.coe_gpow
- \+/\- *lemma* is_add_subgroup.gsmul_coe
- \+/\- *lemma* is_subgroup.coe_gpow
- \+/\- *lemma* is_add_subgroup.gsmul_coe

modified src/group_theory/submonoid.lean
- \+/\- *lemma* is_submonoid.coe_pow
- \+/\- *lemma* is_add_submonoid.smul_coe
- \+/\- *lemma* is_submonoid.coe_pow
- \+/\- *lemma* is_add_submonoid.smul_coe



## [2020-05-06 14:05:37](https://github.com/leanprover-community/mathlib/commit/93a64da)
chore(data/pnat/basic): add `mk_le_mk`, `mk_lt_mk`, `coe_le_coe`, `coe_lt_coe` ([#2613](https://github.com/leanprover-community/mathlib/pull/2613))
#### Estimated changes
modified src/data/pnat/basic.lean
- \+ *lemma* mk_le_mk
- \+ *lemma* mk_lt_mk
- \+ *lemma* coe_le_coe
- \+ *lemma* coe_lt_coe

modified src/data/pnat/intervals.lean
- \+/\- *lemma* Ico.mem
- \+/\- *lemma* Ico.mem



## [2020-05-06 09:03:06](https://github.com/leanprover-community/mathlib/commit/5593155)
feat(*): lemmas on sums and products over fintypes ([#2598](https://github.com/leanprover-community/mathlib/pull/2598))
#### Estimated changes
modified src/data/finsupp.lean
- \+ *lemma* prod_pow

modified src/data/fintype/card.lean
- \+/\- *lemma* card_eq_sum_ones
- \+ *lemma* prod_eq_one
- \+ *lemma* prod_congr
- \+ *lemma* prod_unique
- \+ *lemma* finset.prod_fiberwise
- \+ *lemma* fintype.prod_fiberwise
- \+ *lemma* fintype.prod_sum_type
- \+/\- *lemma* card_eq_sum_ones



## [2020-05-06 02:11:34](https://github.com/leanprover-community/mathlib/commit/4503f8f)
chore(scripts): update nolints.txt ([#2610](https://github.com/leanprover-community/mathlib/pull/2610))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-05 22:33:19](https://github.com/leanprover-community/mathlib/commit/c7593cc)
refactor(field_theory): move finite_card.lean into finite.lean ([#2607](https://github.com/leanprover-community/mathlib/pull/2607))
#### Estimated changes
modified src/field_theory/finite.lean
- \+ *theorem* card
- \+ *theorem* card'

deleted src/field_theory/finite_card.lean
- \- *theorem* card
- \- *theorem* card'



## [2020-05-05 22:33:16](https://github.com/leanprover-community/mathlib/commit/0db59db)
feat(data/equiv/basic): some elementary equivs ([#2602](https://github.com/leanprover-community/mathlib/pull/2602))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* sigma_preimage_equiv_apply
- \+ *lemma* sigma_preimage_equiv_symm_apply_fst
- \+ *lemma* sigma_preimage_equiv_symm_apply_snd_fst
- \+ *lemma* sum_compl_apply_inl
- \+ *lemma* sum_compl_apply_inr
- \+ *lemma* sum_compl_apply_symm_of_pos
- \+ *lemma* sum_compl_apply_symm_of_neg
- \+ *lemma* subtype_preimage_apply
- \+ *lemma* subtype_preimage_symm_apply_coe
- \+ *lemma* subtype_preimage_symm_apply_coe_pos
- \+ *lemma* subtype_preimage_symm_apply_coe_neg
- \+ *lemma* fun_unique_apply
- \+ *lemma* fun_unique_symm_apply
- \+ *def* sum_compl
- \+ *def* subtype_preimage
- \+ *def* fun_unique



## [2020-05-05 20:16:28](https://github.com/leanprover-community/mathlib/commit/359031f)
refactor(*): remove instance max depth ([#2608](https://github.com/leanprover-community/mathlib/pull/2608))
With current Lean, all the manual increases of the maximum instance depth have become unnecessary. This PR removes them all.
#### Estimated changes
modified src/algebra/direct_limit.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/extend_deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/calculus/iterated_deriv.lean

modified src/analysis/calculus/mean_value.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/complex/basic.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/real_inner_product.lean

modified src/data/padics/padic_numbers.lean

modified src/field_theory/mv_polynomial.lean

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/mfderiv.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/contraction.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/dual.lean

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/matrix.lean

modified src/linear_algebra/nonsingular_inverse.lean

modified src/linear_algebra/special_linear_group.lean

modified src/linear_algebra/tensor_product.lean

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/l1_space.lean

modified src/ring_theory/algebra_operations.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization.lean

modified src/tactic/ring.lean

modified src/topology/algebra/module.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean



## [2020-05-05 19:08:14](https://github.com/leanprover-community/mathlib/commit/a66d0a8)
chore(field_theory/finite): meaningful variable names ([#2606](https://github.com/leanprover-community/mathlib/pull/2606))
#### Estimated changes
modified src/field_theory/finite.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* card_units
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* card_units
- \+/\- *lemma* pow_card_sub_one_eq_one
- \+/\- *def* field_of_integral_domain
- \+/\- *def* field_of_integral_domain



## [2020-05-05 14:29:27](https://github.com/leanprover-community/mathlib/commit/0c1b60b)
feat(group_theory/order_of_element): order_of_eq_prime ([#2604](https://github.com/leanprover-community/mathlib/pull/2604))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_prime



## [2020-05-05 08:02:15](https://github.com/leanprover-community/mathlib/commit/7a367f3)
feat(algebra/char_p): add lemma ring_char_ne_one ([#2595](https://github.com/leanprover-community/mathlib/pull/2595))
This lemma is more useful than the extant `false_of_nonzero_of_char_one`
when we are working with the function `ring_char` rather than the `char_p`
Prop.
#### Estimated changes
modified src/algebra/char_p.lean
- \+ *lemma* ring_char_ne_one

modified src/algebra/ring.lean



## [2020-05-05 06:09:07](https://github.com/leanprover-community/mathlib/commit/91b3906)
feat(data/polynomial): misc on derivatives of polynomials ([#2596](https://github.com/leanprover-community/mathlib/pull/2596))
Co-authored by: @alexjbest
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* derivative_neg
- \+ *lemma* derivative_sub
- \+ *lemma* derivative_smul
- \+ *lemma* is_coprime_of_is_root_of_eval_derivative_ne_zero
- \+ *def* derivative_hom
- \+ *def* derivative_lhom



## [2020-05-05 04:42:12](https://github.com/leanprover-community/mathlib/commit/d6ddfd2)
feat(algebra/midpoint): define `midpoint`, prove basic properties ([#2599](https://github.com/leanprover-community/mathlib/pull/2599))
Part of [#2214](https://github.com/leanprover-community/mathlib/pull/2214)
#### Estimated changes
created src/algebra/midpoint.lean
- \+ *lemma* midpoint_eq_iff
- \+ *lemma* midpoint_def
- \+ *lemma* midpoint_unique
- \+ *lemma* midpoint_self
- \+ *lemma* midpoint_comm
- \+ *lemma* midpoint_add_add
- \+ *lemma* midpoint_add_right
- \+ *lemma* midpoint_add_left
- \+ *lemma* midpoint_smul_smul
- \+ *lemma* midpoint_neg_neg
- \+ *lemma* midpoint_sub_sub
- \+ *lemma* midpoint_sub_right
- \+ *lemma* midpoint_sub_left
- \+ *def* midpoint



## [2020-05-04 22:27:29](https://github.com/leanprover-community/mathlib/commit/1c4b5ec)
feat(ring_theory/ideals): quotient map to residue field as ring hom ([#2597](https://github.com/leanprover-community/mathlib/pull/2597))
#### Estimated changes
modified src/ring_theory/ideals.lean
- \+ *def* residue



## [2020-05-04 10:57:29](https://github.com/leanprover-community/mathlib/commit/14aa1f7)
feat(combinatorics/composition): refactor compositions, split a list wrt a composition ([#2554](https://github.com/leanprover-community/mathlib/pull/2554))
Refactor `composition`, replacing in its definition a list of positive integers with a list of integers which are positive. This avoids going back and forth all the time between `nat` and `pnat`.
Also introduce the ability to split a list of length `n` with respect to a composition `c` of `n`, giving rise to a list of `c.length` sublists whose join is the original list.
#### Estimated changes
modified src/analysis/analytic/composition.lean

modified src/combinatorics/composition.lean
- \+/\- *lemma* blocks_length
- \+ *lemma* of_fn_blocks_fun
- \+ *lemma* monotone_size_up_to
- \+/\- *lemma* sigma_eq_iff_blocks_eq
- \+ *lemma* ones_length
- \+ *lemma* ones_blocks
- \+ *lemma* ones_blocks_fun
- \+ *lemma* ones_size_up_to
- \+ *lemma* ones_embedding
- \+ *lemma* eq_ones_iff
- \+ *lemma* ne_ones_iff
- \+ *lemma* single_length
- \+ *lemma* single_blocks
- \+ *lemma* single_blocks_fun
- \+ *lemma* single_embedding
- \+ *lemma* eq_single_iff
- \+ *lemma* split_wrt_composition_aux_cons
- \+ *lemma* length_split_wrt_composition_aux
- \+ *lemma* length_split_wrt_composition
- \+ *lemma* map_length_split_wrt_composition_aux
- \+ *lemma* map_length_split_wrt_composition
- \+ *lemma* length_pos_of_mem_split_wrt_composition
- \+ *lemma* sum_take_map_length_split_wrt_composition
- \- *lemma* blocks_sum
- \+/\- *lemma* blocks_length
- \- *lemma* blocks_pnat_length
- \- *lemma* blocks_pos
- \- *lemma* sigma_eq_iff_blocks_pnat_eq
- \+/\- *lemma* sigma_eq_iff_blocks_eq
- \- *lemma* coe_blocks_pnat_eq_blocks
- \- *lemma* blocks_pnat_length
- \- *lemma* composition.to_composition_as_set_blocks_pnat
- \- *lemma* composition_as_set.to_composition_blocks_pnat
- \+ *theorem* join_split_wrt_composition_aux
- \+ *theorem* join_split_wrt_composition
- \+ *theorem* split_wrt_composition_join
- \+/\- *def* length
- \+ *def* ones
- \+ *def* single
- \+ *def* split_wrt_composition_aux
- \+ *def* split_wrt_composition
- \- *def* blocks
- \+/\- *def* length
- \- *def* blocks_pnat



## [2020-05-04 05:40:22](https://github.com/leanprover-community/mathlib/commit/70245f4)
feat(algebra/big_operators): prod_comp ([#2594](https://github.com/leanprover-community/mathlib/pull/2594))
This is a lemma that @jcommelin looks like he could have used in Chevalley Warning, and is probably useful elsewhere.
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* prod_comp
- \+ *lemma* sum_comp



## [2020-05-03 12:27:43](https://github.com/leanprover-community/mathlib/commit/08a17d6)
chore(scripts): update nolints.txt ([#2593](https://github.com/leanprover-community/mathlib/pull/2593))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-05-03 08:34:26](https://github.com/leanprover-community/mathlib/commit/a223bbb)
chore(*): switch to lean 3.10.0 ([#2587](https://github.com/leanprover-community/mathlib/pull/2587))
There have been two changes in Lean 3.10 that have a significant effect on mathlib:
 - `rename'` has been moved to core.  Therefore `rename'` has been removed.
 - Given a term `⇑f x`, the simplifier can now rewrite in both `f` and `x`.  In many cases we had both `⇑f = ⇑f'` and `⇑f x = ⇑f' x` as simp lemmas; the latter is redundant now and has been removed (or just not marked simp anymore).  The new and improved congruence lemmas are also used by `convert` and `congr`, these tactics have become more powerful as well.
I've also sneaked in two related changes that I noticed while fixing the proofs affected by the changes above:
 - `@[to_additive, simp]` has been replaced by `@[simp, to_additive]` in the monoid localization file.  The difference is that `@[to_additive, simp]` only marks the multiplicative lemma as simp.
 - `def prod_comm : α × β ≃ β × α` (etc.) is no longer marked `@[simp]`.  Marking this kind of lemmas as simp causes the simplifier to unfold the definition of `prod_comm` (instead of just rewriting `α × β` to `β × α` in the `≃` simp relation).  This has become a bigger issue now since the simplifier can rewrite the `f` in `⇑f x`.
#### Estimated changes
modified leanpkg.toml

modified src/algebra/category/Group/Z_Module_equivalence.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/normed_space/multilinear.lean

modified src/category_theory/limits/concrete_category.lean

modified src/data/equiv/basic.lean
- \+ *lemma* prod_comm_apply
- \+ *lemma* sum_comm_apply_inl
- \+ *lemma* sum_comm_apply_inr
- \+ *lemma* sum_comm_symm
- \+ *lemma* sum_empty_apply_inl
- \+ *lemma* empty_sum_apply_inr
- \+ *lemma* sum_pempty_apply_inl
- \+ *lemma* pempty_sum_apply_inr
- \+ *lemma* option_equiv_sum_punit_none
- \+ *lemma* option_equiv_sum_punit_some
- \- *theorem* symm_symm_apply
- \+/\- *def* arrow_punit_equiv_punit
- \+/\- *def* punit_arrow_equiv
- \+/\- *def* empty_arrow_equiv_punit
- \+/\- *def* pempty_arrow_equiv_punit
- \+/\- *def* false_arrow_equiv_punit
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \+/\- *def* prod_empty
- \+/\- *def* empty_prod
- \+/\- *def* prod_pempty
- \+/\- *def* pempty_prod
- \+/\- *def* sum_comm
- \+/\- *def* sum_assoc
- \+/\- *def* sum_empty
- \+/\- *def* empty_sum
- \+/\- *def* sum_pempty
- \+/\- *def* pempty_sum
- \+/\- *def* option_equiv_sum_punit
- \+/\- *def* nat_sum_punit_equiv_nat
- \+/\- *def* arrow_punit_equiv_punit
- \+/\- *def* punit_arrow_equiv
- \+/\- *def* empty_arrow_equiv_punit
- \+/\- *def* pempty_arrow_equiv_punit
- \+/\- *def* false_arrow_equiv_punit
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* prod_punit
- \+/\- *def* punit_prod
- \+/\- *def* prod_empty
- \+/\- *def* empty_prod
- \+/\- *def* prod_pempty
- \+/\- *def* pempty_prod
- \+/\- *def* sum_comm
- \+/\- *def* sum_assoc
- \+/\- *def* sum_empty
- \+/\- *def* empty_sum
- \+/\- *def* sum_pempty
- \+/\- *def* pempty_sum
- \+/\- *def* option_equiv_sum_punit
- \+/\- *def* nat_sum_punit_equiv_nat

modified src/data/finsupp.lean

modified src/data/finsupp/pointwise.lean

modified src/data/list/defs.lean
- \- *def* after

modified src/data/list/sigma.lean

modified src/data/pequiv.lean
- \- *lemma* symm_refl_apply
- \- *lemma* symm_symm_apply
- \- *lemma* refl_trans_apply
- \- *lemma* trans_refl_apply
- \- *lemma* symm_single_apply

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/mfderiv.lean

modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \+/\- *lemma* to_mul_equiv_eq
- \+/\- *lemma* to_mul_equiv_of_mul_equiv
- \+/\- *lemma* of_mul_equiv_eq
- \+/\- *lemma* comp_mul_equiv_symm_comap_apply
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map_apply
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq
- \+/\- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv_apply
- \+/\- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv
- \+/\- *lemma* mul_equiv_of_localizations_apply
- \+/\- *lemma* mul_equiv_of_localizations_symm_apply
- \- *lemma* to_mul_equiv_apply
- \+/\- *lemma* to_mul_equiv_eq
- \+/\- *lemma* to_mul_equiv_of_mul_equiv
- \- *lemma* of_mul_equiv_apply
- \+/\- *lemma* of_mul_equiv_eq
- \+/\- *lemma* comp_mul_equiv_symm_comap_apply
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map_apply
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq_map
- \+/\- *lemma* mul_equiv_of_mul_equiv_eq
- \+/\- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv_apply
- \+/\- *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv

modified src/group_theory/perm/sign.lean

modified src/linear_algebra/basic.lean
- \- *theorem* symm_symm_apply

modified src/linear_algebra/matrix.lean

modified src/ring_theory/algebra.lean
- \+/\- *lemma* coe_to_monoid_hom
- \+/\- *lemma* coe_to_add_monoid_hom
- \+/\- *lemma* coe_to_monoid_hom
- \+/\- *lemma* coe_to_add_monoid_hom

modified src/ring_theory/power_series.lean
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *def* mk
- \+/\- *def* mk

modified src/set_theory/ordinal.lean

modified src/set_theory/pgame.lean

modified src/tactic/basic.lean

deleted src/tactic/rename.lean

modified src/topology/algebra/module.lean
- \+/\- *theorem* symm_symm_apply
- \+/\- *theorem* symm_symm_apply

modified test/tactics.lean



## [2020-05-02 22:38:27](https://github.com/leanprover-community/mathlib/commit/d1eae21)
chore(build.yml): Don't build nolints branch ([#2591](https://github.com/leanprover-community/mathlib/pull/2591))
#### Estimated changes
modified .github/workflows/build.yml



## [2020-05-02 15:22:25](https://github.com/leanprover-community/mathlib/commit/a99f9b5)
refactor(algebra/big_operators): introduce notation for finset.prod and finset.sum ([#2582](https://github.com/leanprover-community/mathlib/pull/2582))
I have not gone through all of mathlib to use this notation everywhere. I think we can maybe transition naturally.
#### Estimated changes
modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_empty
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* prod_const_one
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_sdiff
- \+/\- *lemma* prod_mul_distrib
- \+/\- *lemma* prod_subset
- \+/\- *lemma* prod_filter_ne_one
- \+/\- *lemma* prod_attach
- \+/\- *lemma* nonempty_of_prod_ne_one
- \+/\- *lemma* exists_ne_one_of_prod_ne_one
- \+ *lemma* sum_range_succ
- \+ *lemma* prod_Ico_eq_mul_inv
- \+/\- *lemma* prod_const
- \+/\- *lemma* prod_eq_one
- \+/\- *lemma* prod_inv_distrib
- \+/\- *lemma* sum_sub_distrib
- \+/\- *lemma* sum_mul
- \+/\- *lemma* mul_sum
- \+/\- *lemma* prod_eq_zero
- \+/\- *lemma* prod_eq_zero_iff
- \+/\- *lemma* sum_le_sum
- \+/\- *lemma* sum_nonneg
- \+/\- *lemma* sum_nonpos
- \+/\- *lemma* sum_eq_zero_iff_of_nonneg
- \+/\- *lemma* sum_eq_zero_iff_of_nonpos
- \+/\- *lemma* single_le_sum
- \+/\- *lemma* sum_le_sum_of_subset
- \+/\- *lemma* prod_pos
- \+/\- *lemma* prod_Ico_id_eq_fact
- \+/\- *lemma* sum_range_id
- \+/\- *lemma* card_eq_sum_ones
- \+/\- *lemma* prod_empty
- \+/\- *lemma* prod_insert
- \+/\- *lemma* prod_singleton
- \+/\- *lemma* prod_const_one
- \+/\- *lemma* prod_union
- \+/\- *lemma* prod_sdiff
- \+/\- *lemma* prod_mul_distrib
- \+/\- *lemma* prod_subset
- \+/\- *lemma* prod_filter_ne_one
- \+/\- *lemma* prod_attach
- \+/\- *lemma* nonempty_of_prod_ne_one
- \+/\- *lemma* exists_ne_one_of_prod_ne_one
- \- *lemma* prod_Ico_eq_div
- \+/\- *lemma* prod_const
- \+/\- *lemma* prod_eq_one
- \+/\- *lemma* prod_inv_distrib
- \+/\- *lemma* sum_sub_distrib
- \+/\- *lemma* sum_mul
- \+/\- *lemma* mul_sum
- \+/\- *lemma* prod_eq_zero
- \+/\- *lemma* prod_eq_zero_iff
- \+/\- *lemma* sum_le_sum
- \+/\- *lemma* sum_nonneg
- \+/\- *lemma* sum_nonpos
- \+/\- *lemma* sum_eq_zero_iff_of_nonneg
- \+/\- *lemma* sum_eq_zero_iff_of_nonpos
- \+/\- *lemma* single_le_sum
- \+/\- *lemma* sum_le_sum_of_subset
- \+/\- *lemma* prod_pos
- \+/\- *lemma* prod_Ico_id_eq_fact
- \+/\- *lemma* sum_range_id
- \+/\- *lemma* card_eq_sum_ones
- \+/\- *theorem* prod_eq_fold
- \+/\- *theorem* exists_le_of_sum_le
- \+/\- *theorem* prod_eq_fold
- \+/\- *theorem* exists_le_of_sum_le

modified src/algebra/category/Group/biproducts.lean

modified src/algebra/geom_sum.lean

modified src/analysis/specific_limits.lean

modified src/data/complex/exponential.lean

modified src/data/mv_polynomial.lean

modified src/data/nat/choose.lean

modified src/group_theory/order_of_element.lean

modified src/ring_theory/power_series.lean



## [2020-05-02 12:33:54](https://github.com/leanprover-community/mathlib/commit/1cc83e9)
chore(algebra/ordered_field): move inv_neg to field and prove for division ring ([#2588](https://github.com/leanprover-community/mathlib/pull/2588))
`neg_inv` this lemma with the equality swapped was already in the library, so maybe we should just get rid of this or `neg_inv`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/inv_neg/near/196042954)
#### Estimated changes
modified src/algebra/field.lean
- \+ *lemma* inv_neg

modified src/algebra/ordered_field.lean
- \- *lemma* inv_neg



## [2020-05-02 09:41:43](https://github.com/leanprover-community/mathlib/commit/b902f6e)
feat(*): several `@[simp]` lemmas ([#2579](https://github.com/leanprover-community/mathlib/pull/2579))
Also add an explicit instance for `submodule.has_coe_to_sort`.
This way `rintro ⟨x, hx⟩` results in `(hx : x ∈ p)`.
Also fixes some timeouts introduced by [#2363](https://github.com/leanprover-community/mathlib/pull/2363). See Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/partrec_code
#### Estimated changes
modified src/algebra/group/prod.lean
- \+ *lemma* mk_eq_one

modified src/algebra/module.lean
- \+ *lemma* mk_eq_zero

modified src/analysis/convex/cone.lean

modified src/computability/partrec.lean

modified src/computability/partrec_code.lean

modified src/data/finset.lean

modified src/data/set/basic.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/linear_pmap.lean

modified src/logic/basic.lean
- \+ *theorem* exists_exists_and_eq_and
- \+ *theorem* exists_exists_eq_and
- \+ *theorem* exists_comm

modified src/set_theory/cofinality.lean

modified src/tactic/converter/binders.lean
- \- *theorem* {u



## [2020-05-02 09:41:41](https://github.com/leanprover-community/mathlib/commit/06bae3e)
fix(data/int/basic): use has_coe_t to prevent looping ([#2573](https://github.com/leanprover-community/mathlib/pull/2573))
The file `src/computability/partrec.lean` no longer opens in vscode because type-class search times out.  This happens because we have the instance `has_coe ℤ α` which causes non-termination because coercions are chained transitively (`has_coe ℤ ℤ`, `has_coe ℤ ℤ`, ...).  Even if the coercions would not apply to integers (and maybe avoid non-termination), it would still enumerate all `0,1,+,-` structures, of which there are unfortunately very many.
This PR therefore downgrades such instances to `has_coe_t` to prevent non-termination due to transitivity.  It also adds a linter to prevent this kind of error in the future.
#### Estimated changes
modified src/data/fp/basic.lean

modified src/data/int/basic.lean

modified src/data/nat/cast.lean

modified src/data/num/basic.lean

modified src/data/rat/cast.lean

modified src/data/zmod/basic.lean

modified src/group_theory/coset.lean

modified src/tactic/lint/type_classes.lean

modified src/tactic/norm_cast.lean
- \+/\- *lemma* ite_cast
- \+/\- *lemma* ite_cast

modified test/lint.lean
- \- *def* foo_instance

created test/lint_coe_t.lean
- \+ *def* a_to_quot
- \+ *def* int_to_a



## [2020-05-02 09:41:39](https://github.com/leanprover-community/mathlib/commit/9d57f68)
feat(order/bounded_lattice): introduce `is_compl` predicate ([#2569](https://github.com/leanprover-community/mathlib/pull/2569))
Also move `disjoint` from `data/set/lattice`
#### Estimated changes
modified src/combinatorics/composition.lean

modified src/data/set/lattice.lean
- \- *lemma* disjoint_self
- \- *lemma* disjoint.ne
- \- *theorem* disjoint.eq_bot
- \- *theorem* disjoint_iff
- \- *theorem* disjoint.comm
- \- *theorem* disjoint.symm
- \- *theorem* disjoint_bot_left
- \- *theorem* disjoint_bot_right
- \- *theorem* disjoint.mono
- \- *theorem* disjoint.mono_left
- \- *theorem* disjoint.mono_right
- \- *def* disjoint

modified src/order/boolean_algebra.lean
- \+ *theorem* is_compl_neg
- \+ *theorem* is_compl.neg_eq

modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint_self
- \+ *lemma* disjoint.ne
- \+ *lemma* of_eq
- \+ *lemma* inf_eq_bot
- \+ *lemma* sup_eq_top
- \+ *lemma* to_order_dual
- \+ *lemma* le_left_iff
- \+ *lemma* le_right_iff
- \+ *lemma* left_le_iff
- \+ *lemma* right_le_iff
- \+ *lemma* antimono
- \+ *lemma* right_unique
- \+ *lemma* left_unique
- \+ *lemma* sup_inf
- \+ *lemma* inf_sup
- \+ *lemma* is_compl_bot_top
- \+ *lemma* is_compl_top_bot
- \+ *theorem* disjoint.eq_bot
- \+ *theorem* disjoint_iff
- \+ *theorem* disjoint.comm
- \+ *theorem* disjoint.symm
- \+ *theorem* disjoint_bot_left
- \+ *theorem* disjoint_bot_right
- \+ *theorem* disjoint.mono
- \+ *theorem* disjoint.mono_left
- \+ *theorem* disjoint.mono_right
- \+ *def* disjoint

modified src/order/filter/basic.lean
- \+ *lemma* is_compl_principal
- \+/\- *lemma* map_at_top_eq_of_gc
- \+/\- *lemma* map_at_top_eq_of_gc

modified src/order/lattice.lean
- \+ *lemma* le_of_inf_le_sup_le
- \+ *lemma* eq_of_inf_eq_sup_eq
- \- *lemma* eq_of_sup_eq_inf_eq



## [2020-05-02 08:31:10](https://github.com/leanprover-community/mathlib/commit/738bbae)
feat(algebra/group_ring_action): action on polynomials ([#2586](https://github.com/leanprover-community/mathlib/pull/2586))
#### Estimated changes
modified src/algebra/group_ring_action.lean
- \+ *lemma* polynomial.coeff_smul'
- \+ *lemma* polynomial.smul_C
- \+ *lemma* polynomial.smul_X



## [2020-05-02 06:01:16](https://github.com/leanprover-community/mathlib/commit/d0a1d77)
doc(tactic/rcases): mention the "rfl" pattern ([#2585](https://github.com/leanprover-community/mathlib/pull/2585))
Edited from @jcommelin's answer on Zulip here: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/noob.20question%28s%29/near/184491982
#### Estimated changes
modified src/tactic/rcases.lean



## [2020-05-01 21:31:28](https://github.com/leanprover-community/mathlib/commit/eb383b1)
chore(group_theory/perm): delete duplicate lemmas ([#2584](https://github.com/leanprover-community/mathlib/pull/2584))
`sum_univ_perm` is a special case of `sum_equiv`, so it's not necessary. 
I also moved `sum_equiv` into the `finset` namespace.
#### Estimated changes
modified src/data/fintype/card.lean
- \+ *lemma* finset.prod_equiv
- \- *lemma* prod_equiv

modified src/group_theory/perm/sign.lean
- \- *lemma* finset.prod_univ_perm
- \- *lemma* finset.sum_univ_perm

modified src/linear_algebra/determinant.lean

modified src/number_theory/sum_four_squares.lean



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
created src/algebra/classical_lie_algebras.lean
- \+ *lemma* matrix_trace_commutator_zero
- \+ *lemma* sl_bracket
- \+ *lemma* E_apply_one
- \+ *lemma* E_apply_zero
- \+ *lemma* E_diag_zero
- \+ *lemma* E_trace_zero
- \+ *lemma* Eb_val
- \+ *lemma* sl_non_abelian
- \+ *def* sl
- \+ *def* Eb

modified src/algebra/lie_algebra.lean
- \+ *lemma* lie_ring.of_associative_ring_bracket
- \+ *lemma* commutative_ring_iff_abelian_lie_ring
- \- *def* lie_subalgebra_lie_ring
- \- *def* lie_subalgebra_lie_algebra

modified src/data/fintype/basic.lean
- \+ *lemma* fintype.exists_pair_of_one_lt_card

modified src/linear_algebra/matrix.lean
- \+ *lemma* diag_apply
- \+ *lemma* trace_diag



## [2020-05-01 12:56:42](https://github.com/leanprover-community/mathlib/commit/6a2559a)
chore(algebra/group_with_zero): rename div_eq_inv_mul' to div_eq_inv_mul ([#2583](https://github.com/leanprover-community/mathlib/pull/2583))
There are no occurrences of the name without ' in either core or mathlib
so this change in name (from [#2242](https://github.com/leanprover-community/mathlib/pull/2242)) seems to have been unnecessary.
#### Estimated changes
modified src/algebra/group_with_zero.lean
- \+ *lemma* div_eq_inv_mul
- \- *lemma* div_eq_inv_mul'

modified src/algebra/ordered_field.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/convex/basic.lean

modified src/analysis/normed_space/basic.lean

modified src/data/real/cau_seq_completion.lean

modified src/measure_theory/probability_mass_function.lean

modified src/topology/metric_space/antilipschitz.lean



## [2020-05-01 10:09:30](https://github.com/leanprover-community/mathlib/commit/ee488b2)
fix(tactic/lint/basic): remove default argument for auto_decl and enable more linters ([#2580](https://github.com/leanprover-community/mathlib/pull/2580))
Run more linters on automatically-generated declarations.  Quite a few linters should have been run on them, but I forgot about it because the `auto_decls` flag is optional and off by default.  I've made it non-optional so that you don't forget about it when defining a linter.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/simp.20linter.20and.20structure.20fields/near/195810856
#### Estimated changes
modified src/data/list/forall2.lean
- \+/\- *lemma* forall₂_nil_left_iff
- \+/\- *lemma* forall₂_nil_right_iff
- \+/\- *lemma* forall₂_nil_left_iff
- \+/\- *lemma* forall₂_nil_right_iff

modified src/tactic/lint/basic.lean

modified src/tactic/lint/misc.lean

modified src/tactic/lint/simp.lean

modified src/tactic/lint/type_classes.lean

modified test/lint.lean



## [2020-05-01 07:42:20](https://github.com/leanprover-community/mathlib/commit/67f3fde)
feat(algebra/group_ring_action) define group actions on rings ([#2566](https://github.com/leanprover-community/mathlib/pull/2566))
Define group action on rings.
Related Zulip discussions: 
- https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232566.20group.20actions.20on.20ring 
- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mul_action
#### Estimated changes
created src/algebra/group_ring_action.lean
- \+ *lemma* smul_mul'
- \+ *lemma* smul_inv
- \+ *lemma* smul_pow
- \+ *def* distrib_mul_action.to_add_monoid_hom
- \+ *def* distrib_mul_action.to_add_equiv
- \+ *def* monoid.End
- \+ *def* add_monoid.End
- \+ *def* distrib_mul_action.hom_add_monoid_hom
- \+ *def* mul_semiring_action.to_semiring_hom
- \+ *def* mul_semiring_action.to_semiring_equiv

modified src/group_theory/group_action.lean



## [2020-05-01 05:59:47](https://github.com/leanprover-community/mathlib/commit/74d24ab)
feat(topology/instances/real_vector_space): `E →+ F` to `E →L[ℝ] F` ([#2577](https://github.com/leanprover-community/mathlib/pull/2577))
A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear.
#### Estimated changes
created src/topology/instances/real_vector_space.lean
- \+ *lemma* map_real_smul
- \+ *lemma* coe_to_real_linear_map
- \+ *def* to_real_linear_map



## [2020-05-01 04:49:00](https://github.com/leanprover-community/mathlib/commit/d3140fb)
feat(data/mv_polynomial): lemmas on total_degree ([#2575](https://github.com/leanprover-community/mathlib/pull/2575))
This is a small preparation for the Chevalley–Warning theorem.
#### Estimated changes
modified src/data/mv_polynomial.lean
- \+ *lemma* eval_one
- \+ *lemma* eval_pow
- \+/\- *lemma* total_degree_C
- \+/\- *lemma* total_degree_zero
- \+/\- *lemma* total_degree_one
- \+ *lemma* total_degree_X
- \+ *lemma* total_degree_pow
- \+ *lemma* total_degree_neg
- \+ *lemma* total_degree_sub
- \+/\- *lemma* total_degree_C
- \+/\- *lemma* total_degree_zero
- \+/\- *lemma* total_degree_one

