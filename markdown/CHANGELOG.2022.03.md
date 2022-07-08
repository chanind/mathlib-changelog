## [2022-03-31 23:56:26](https://github.com/leanprover-community/mathlib/commit/2b92d08)
feat(model_theory/elementary_maps): The Tarski-Vaught test ([#12919](https://github.com/leanprover-community/mathlib/pull/12919))
Proves the Tarski-Vaught test for elementary embeddings and substructures.
#### Estimated changes
modified src/data/fin/basic.lean
- \+ *lemma* cast_add_zero

modified src/model_theory/elementary_maps.lean
- \+ *theorem* is_elementary_of_exists
- \+ *theorem* is_elementary_of_exists
- \+ *def* to_elementary_embedding
- \+ *def* to_elementary_substructure

modified src/model_theory/semantics.lean
- \+ *lemma* realize_relabel_sum_inr



## [2022-03-31 17:21:48](https://github.com/leanprover-community/mathlib/commit/de50389)
split(order/chain): Split off `order.zorn` ([#13060](https://github.com/leanprover-community/mathlib/pull/13060))
Split `order.zorn` into two files, one about chains, the other one about Zorn's lemma.
#### Estimated changes
created src/order/chain.lean
- \+ *lemma* is_chain_empty
- \+ *lemma* set.subsingleton.is_chain
- \+ *lemma* is_chain.mono
- \+ *lemma* is_chain.symm
- \+ *lemma* is_chain_of_trichotomous
- \+ *lemma* is_chain.insert
- \+ *lemma* is_chain_univ_iff
- \+ *lemma* is_chain.image
- \+ *lemma* is_chain.total
- \+ *lemma* is_chain.directed_on
- \+ *lemma* is_max_chain.is_chain
- \+ *lemma* is_max_chain.not_super_chain
- \+ *lemma* succ_chain_spec
- \+ *lemma* is_chain.succ
- \+ *lemma* is_chain.super_chain_succ_chain
- \+ *lemma* subset_succ_chain
- \+ *lemma* chain_closure_empty
- \+ *lemma* chain_closure_max_chain
- \+ *lemma* chain_closure.total
- \+ *lemma* chain_closure.succ_fixpoint
- \+ *lemma* chain_closure.succ_fixpoint_iff
- \+ *lemma* chain_closure.is_chain
- \+ *lemma* max_chain_spec
- \+ *def* is_chain
- \+ *def* super_chain
- \+ *def* is_max_chain
- \+ *def* succ_chain
- \+ *def* max_chain

modified src/order/zorn.lean
- \- *lemma* is_chain_empty
- \- *lemma* set.subsingleton.is_chain
- \- *lemma* is_chain.mono
- \- *lemma* is_chain.total
- \- *lemma* is_chain.symm
- \- *lemma* is_chain_of_trichotomous
- \- *lemma* is_chain.insert
- \- *lemma* is_chain_univ_iff
- \- *lemma* is_chain.image
- \- *lemma* is_chain.directed_on
- \- *lemma* is_chain.directed
- \- *lemma* is_max_chain.is_chain
- \- *lemma* is_max_chain.not_super_chain
- \- *lemma* succ_spec
- \- *lemma* is_chain.succ
- \- *lemma* is_chain.super_chain_succ_chain
- \- *lemma* succ_increasing
- \- *lemma* chain_closure_empty
- \- *lemma* chain_closure_max_chain
- \- *lemma* chain_closure_total
- \- *lemma* chain_closure.succ_fixpoint
- \- *lemma* chain_closure.succ_fixpoint_iff
- \- *lemma* chain_closure.is_chain
- \- *lemma* max_chain_spec
- \- *def* is_chain
- \- *def* super_chain
- \- *def* is_max_chain
- \- *def* succ_chain
- \- *def* max_chain



## [2022-03-31 16:09:24](https://github.com/leanprover-community/mathlib/commit/13e08bf)
feat(model_theory/*): Constructors for low-arity languages and structures ([#12960](https://github.com/leanprover-community/mathlib/pull/12960))
Defines `first_order.language.mk₂` to make it easier to define a language with at-most-binary symbols.
Defines `first_order.language.Structure.mk₂` to make it easier to define a structure in a language defined with `first_order.language₂`.
Defines `first_order.language.functions.apply₁` and `first_order.language.functions.apply₂` to make it easier to construct terms using low-arity function symbols.
Defines `first_order.language.relations.formula₁` and `first_order.language.relations.formula₂` to make it easier to construct formulas using low-arity relation symbols.
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* fun_map_apply₀
- \+ *lemma* fun_map_apply₁
- \+ *lemma* fun_map_apply₂
- \+ *lemma* rel_map_apply₁
- \+ *lemma* rel_map_apply₂
- \+ *def* sequence₂
- \+ *def* fun_map₂
- \+ *def* rel_map₂

modified src/model_theory/semantics.lean
- \+ *lemma* realize_functions_apply₁
- \+ *lemma* realize_functions_apply₂
- \+ *lemma* realize_rel₁
- \+ *lemma* realize_rel₂
- \+ *lemma* realize_rel₁
- \+ *lemma* realize_rel₂

modified src/model_theory/syntax.lean
- \+ *def* functions.apply₁
- \+ *def* functions.apply₂
- \+ *def* relations.bounded_formula₁
- \+ *def* relations.bounded_formula₂
- \+ *def* relations.formula₁
- \+ *def* relations.formula₂



## [2022-03-31 16:09:23](https://github.com/leanprover-community/mathlib/commit/f1ae620)
feat(model_theory/bundled, satisfiability): Bundled models ([#12945](https://github.com/leanprover-community/mathlib/pull/12945))
Defines `Theory.Model`, a type of nonempty bundled models of a particular theory.
Refactors satisfiability in terms of bundled models.
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *def* trivial_unit_structure

modified src/model_theory/bundled.lean
- \+ *lemma* coe_of
- \+ *lemma* coe_of
- \+ *def* of
- \+ *def* model.bundled

modified src/model_theory/satisfiability.lean
- \- *lemma* semantically_equivalent.some_model_realize_bd_iff
- \- *lemma* semantically_equivalent.some_model_realize_iff
- \+/\- *def* is_satisfiable
- \+/\- *def* is_satisfiable
- \- *def* is_satisfiable.some_model

modified src/model_theory/semantics.lean

modified src/model_theory/ultraproducts.lean



## [2022-03-31 15:26:34](https://github.com/leanprover-community/mathlib/commit/2861d4e)
feat(combinatorics/simple_graph/connectivity): walk constructor patterns with explicit vertices ([#13078](https://github.com/leanprover-community/mathlib/pull/13078))
This saves a couple underscores, letting you write `walk.cons' _ v _ h p` instead of `@walk.cons _ _ _ v _ h p` when you want that middle vertex in a pattern.
#### Estimated changes
modified src/combinatorics/simple_graph/connectivity.lean



## [2022-03-31 14:15:57](https://github.com/leanprover-community/mathlib/commit/25ef4f0)
feat(topology/algebra/matrix): more continuity lemmas for matrices ([#13009](https://github.com/leanprover-community/mathlib/pull/13009))
This should cover all the definitions in `data/matrix/basic`, and also picks out a few notable definitions (`det`, `trace`, `adjugate`, `cramer`, `inv`) from other files.
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean

modified src/topology/algebra/matrix.lean
- \+ *lemma* continuous_matrix
- \+ *lemma* continuous.matrix_elem
- \+ *lemma* continuous.matrix_map
- \+ *lemma* continuous.matrix_transpose
- \+ *lemma* continuous.matrix.conj_transpose
- \+ *lemma* continuous.matrix_col
- \+ *lemma* continuous.matrix_row
- \+ *lemma* continuous_matrix.diagonal
- \+ *lemma* continuous.matrix_dot_product
- \+ *lemma* continuous.matrix_mul
- \+ *lemma* continuous.matrix_vec_mul_vec
- \+ *lemma* continuous.matrix_mul_vec
- \+ *lemma* continuous.matrix_vec_mul
- \+ *lemma* continuous.matrix_minor
- \+ *lemma* continuous.matrix_reindex
- \+ *lemma* continuous.matrix_diag
- \+ *lemma* continuous.matrix_trace
- \+ *lemma* continuous.matrix_det
- \+ *lemma* continuous.matrix_update_column
- \+ *lemma* continuous.matrix_update_row
- \+ *lemma* continuous.matrix_cramer
- \+ *lemma* continuous.matrix_adjugate
- \+ *lemma* continuous_at_matrix_inv
- \- *lemma* continuous_det

modified src/topology/continuous_on.lean
- \+ *lemma* continuous.if_const



## [2022-03-31 13:42:09](https://github.com/leanprover-community/mathlib/commit/0f6eec6)
feat(ring_theory/polynomial/pochhammer): generalize a proof from `comm_semiring` to `semiring` ([#13024](https://github.com/leanprover-community/mathlib/pull/13024))
This PR is similar to [#13018](https://github.com/leanprover-community/mathlib/pull/13018).  Lemma `pochhammer_succ_eval` was already proven with a commutativity assumption.  I generalized the proof to `semiring` by introducing a helper lemma.
I still feel that this is harder than I would like it to be: `pochhammer` "is" a polynomial in `ℕ[X]` and all these commutativity assumptions are satisfied, since `ℕ[X]` is commutative.
#### Estimated changes
modified src/ring_theory/polynomial/pochhammer.lean
- \+/\- *lemma* pochhammer_succ_eval
- \+/\- *lemma* pochhammer_succ_eval



## [2022-03-31 13:00:33](https://github.com/leanprover-community/mathlib/commit/1b42223)
feat(analysis/locally_convex): the topology of weak duals is locally convex ([#12623](https://github.com/leanprover-community/mathlib/pull/12623))
#### Estimated changes
created src/analysis/locally_convex/weak_dual.lean
- \+ *lemma* coe_to_seminorm
- \+ *lemma* to_seminorm_apply
- \+ *lemma* to_seminorm_ball_zero
- \+ *lemma* to_seminorm_comp
- \+ *lemma* to_seminorm_family_apply
- \+ *lemma* linear_map.has_basis_weak_bilin
- \+ *def* to_seminorm
- \+ *def* to_seminorm_family

modified src/topology/algebra/module/weak_dual.lean



## [2022-03-31 12:28:09](https://github.com/leanprover-community/mathlib/commit/6405a6a)
feat(analysis/locally_convex): closed balanced sets are a basis of the topology ([#12786](https://github.com/leanprover-community/mathlib/pull/12786))
We prove some topological properties of the balanced core.
#### Estimated changes
modified src/analysis/locally_convex/balanced_core_hull.lean
- \+ *lemma* balanced_core_emptyset
- \+ *lemma* subset_balanced_core
- \+ *lemma* balanced_core_is_closed
- \+ *lemma* balanced_core_mem_nhds_zero
- \+ *lemma* nhds_basis_closed_balanced



## [2022-03-31 10:35:37](https://github.com/leanprover-community/mathlib/commit/7833dbe)
lint(algebra/*): fix some lint errors ([#13058](https://github.com/leanprover-community/mathlib/pull/13058))
* add some docstrings to additive versions;
* make `with_zero.ordered_add_comm_monoid` reducible.
#### Estimated changes
modified src/algebra/group/semiconj.lean

modified src/algebra/hom/equiv.lean
- \+/\- *lemma* apply_symm_apply
- \+/\- *lemma* symm_apply_apply
- \+/\- *lemma* apply_symm_apply
- \+/\- *lemma* symm_apply_apply

modified src/algebra/order/monoid.lean

modified src/topology/metric_space/emetric_space.lean



## [2022-03-31 08:43:56](https://github.com/leanprover-community/mathlib/commit/ba9ead0)
feat(order/sup_indep): lemmas about `pairwise` and `set.pairwise` ([#12590](https://github.com/leanprover-community/mathlib/pull/12590))
The `disjoint` lemmas can now be stated in terms of these two `pairwise` definitions.
This wasn't previously possible as these definitions were not yet imported.
This also adds the `iff` versions of these lemmas, and a docstring tying them all together.
#### Estimated changes
modified src/algebra/direct_sum/module.lean

modified src/order/complete_boolean_algebra.lean
- \+ *lemma* Sup_disjoint_iff
- \+ *lemma* disjoint_Sup_iff

modified src/order/sup_indep.lean
- \+ *lemma* set_independent.pairwise_disjoint
- \+ *lemma* independent.pairwise_disjoint
- \+ *lemma* set_independent_iff_pairwise_disjoint
- \+ *lemma* independent_iff_pairwise_disjoint
- \- *lemma* set_independent.disjoint
- \- *lemma* independent.disjoint



## [2022-03-31 06:51:20](https://github.com/leanprover-community/mathlib/commit/81c5d17)
chore(algebra/order/monoid_lemmas): remove exactly same lemmas ([#13068](https://github.com/leanprover-community/mathlib/pull/13068))
#### Estimated changes
modified src/algebra/order/monoid_lemmas.lean
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \- *lemma* left.mul_lt_one_of_lt_of_lt_one
- \- *lemma* right.mul_lt_one_of_lt_of_lt_one
- \- *theorem* mul_lt_of_lt_of_lt_one
- \- *theorem* mul_lt_of_lt_one_of_lt



## [2022-03-31 06:51:19](https://github.com/leanprover-community/mathlib/commit/7a37490)
feat(ring_theory/polynomial/pochhammer): add a binomial like recursion for pochhammer ([#13018](https://github.com/leanprover-community/mathlib/pull/13018))
This PR proves the identity
`pochhammer R n + n * (pochhammer R (n - 1)).comp (X + 1) = (pochhammer R n).comp (X + 1)`
analogous to the additive recursion for binomial coefficients.
For the proof, first we prove the result for a `comm_semiring` as `pochhammer_add_pochhammer_aux`.  Next, we apply this identity in the general case.
If someone has any idea of how to make the maths statement: it suffices to show this identity for pochhammer symbols in the commutative case, I would be *very* happy to know!
#### Estimated changes
modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_succ_comp_X_add_one



## [2022-03-31 06:51:18](https://github.com/leanprover-community/mathlib/commit/290f440)
feat(order/category/Semilattice): The categories of semilattices ([#12890](https://github.com/leanprover-community/mathlib/pull/12890))
Define `SemilatticeSup` and `SemilatticeInf`, the categories of finitary supremum lattices and finitary infimum lattices.
#### Estimated changes
modified src/order/category/BoundedLattice.lean
- \+ *lemma* coe_forget_to_BoundedOrder
- \+ *lemma* coe_forget_to_Lattice
- \+ *lemma* coe_forget_to_SemilatticeSup
- \+ *lemma* coe_forget_to_SemilatticeInf
- \+ *lemma* forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+ *lemma* forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+/\- *lemma* BoundedLattice_dual_comp_forget_to_BoundedOrder
- \+ *lemma* BoundedLattice_dual_comp_forget_to_SemilatticeSup
- \+ *lemma* BoundedLattice_dual_comp_forget_to_SemilatticeInf
- \+/\- *lemma* BoundedLattice_dual_comp_forget_to_BoundedOrder

created src/order/category/Semilattice.lean
- \+ *lemma* coe_of
- \+ *lemma* coe_forget_to_PartialOrder
- \+ *lemma* coe_of
- \+ *lemma* coe_forget_to_PartialOrder
- \+ *lemma* SemilatticeSup_dual_comp_forget_to_PartialOrder
- \+ *lemma* SemilatticeInf_dual_comp_forget_to_PartialOrder
- \+ *def* of
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* SemilatticeSup_equiv_SemilatticeInf



## [2022-03-31 06:51:17](https://github.com/leanprover-community/mathlib/commit/760f1b2)
refactor(*): rename `topological_ring` to `topological_semiring` and introduce a new `topological_ring` extending `has_continuous_neg` ([#12864](https://github.com/leanprover-community/mathlib/pull/12864))
Following the discussion in this [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity/near/275553306), this renames `topological_ring` to `topological_semiring` throughout the library and weakens the typeclass assumptions from `semiring` to `non_unital_non_assoc_semiring`. Moreover, it introduces a new `topological_ring` class which takes a type class parameter of `non_unital_non_assoc_ring` and extends `topological_semiring` and `has_continuous_neg`.
In the case of *unital* (semi)rings (even non-associative), the type class `topological_semiring` is sufficient to capture the notion of `topological_ring` because negation is just multiplication by `-1`. Therefore, those working with unital (semi)rings can proceed with the small change of using `topological_semiring` instead of `topological_ring`.
The primary reason for the distinction is to weaken the type class assumptions to allow for non-unital rings, in which case `has_continuous_neg` must be explicitly assumed.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)
#### Estimated changes
modified src/analysis/normed/normed_field.lean

modified src/geometry/manifold/algebra/structures.lean
- \+ *lemma* topological_semiring_of_smooth
- \- *lemma* topological_ring_of_smooth

modified src/topology/algebra/algebra.lean
- \+/\- *lemma* continuous_algebra_map_iff_smul
- \+/\- *lemma* continuous_algebra_map
- \+/\- *lemma* has_continuous_smul_of_algebra_map
- \+/\- *lemma* continuous_algebra_map_iff_smul
- \+/\- *lemma* continuous_algebra_map
- \+/\- *lemma* has_continuous_smul_of_algebra_map

modified src/topology/algebra/field.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/module/basic.lean

modified src/topology/algebra/polynomial.lean

modified src/topology/algebra/ring.lean
- \+ *lemma* topological_semiring.has_continuous_neg_of_mul
- \+ *lemma* topological_semiring.to_topological_ring

modified src/topology/continuous_function/algebra.lean

modified src/topology/continuous_function/locally_constant.lean

modified src/topology/continuous_function/polynomial.lean

modified src/topology/instances/nnreal.lean



## [2022-03-31 06:19:33](https://github.com/leanprover-community/mathlib/commit/c2339ca)
feat(algebraic_topology): map_alternating_face_map_complex ([#13028](https://github.com/leanprover-community/mathlib/pull/13028))
In this PR, we obtain a compatibility `map_alternating_face_map_complex` of the construction of the alternating face map complex functor with respect to additive functors between preadditive categories.
#### Estimated changes
modified src/algebraic_topology/alternating_face_map_complex.lean
- \+ *lemma* map_alternating_face_map_complex



## [2022-03-31 02:41:53](https://github.com/leanprover-community/mathlib/commit/8a21316)
feat(combinatorics/simple_graph/regularity/bound): Numerical bounds for Szemerédi's regularity lemma ([#12962](https://github.com/leanprover-community/mathlib/pull/12962))
Define the constants appearing in Szemerédi's regularity lemma and prove a bunch of numerical facts about them.
#### Estimated changes
modified src/algebra/order/field.lean
- \+ *lemma* le_div_self

created src/combinatorics/simple_graph/regularity/bound.lean
- \+ *lemma* le_step_bound
- \+ *lemma* step_bound_mono
- \+ *lemma* step_bound_pos_iff
- \+ *lemma* m_pos
- \+ *lemma* m_coe_pos
- \+ *lemma* coe_m_add_one_pos
- \+ *lemma* one_le_m_coe
- \+ *lemma* eps_pow_five_pos
- \+ *lemma* eps_pos
- \+ *lemma* four_pow_pos
- \+ *lemma* hundred_div_ε_pow_five_le_m
- \+ *lemma* hundred_le_m
- \+ *lemma* a_add_one_le_four_pow_parts_card
- \+ *lemma* card_aux₁
- \+ *lemma* card_aux₂
- \+ *lemma* pow_mul_m_le_card_part
- \+ *lemma* le_initial_bound
- \+ *lemma* seven_le_initial_bound
- \+ *lemma* initial_bound_pos
- \+ *lemma* hundred_lt_pow_initial_bound_mul
- \+ *lemma* initial_bound_le_bound
- \+ *lemma* le_bound
- \+ *lemma* bound_pos
- \+ *def* step_bound

modified src/order/partition/equipartition.lean
- \+ *lemma* is_equipartition.card_parts_eq_average



## [2022-03-31 02:10:17](https://github.com/leanprover-community/mathlib/commit/299984b)
feat(combinatorics/simple_graph/uniform): Graph uniformity and uniform partitions ([#12957](https://github.com/leanprover-community/mathlib/pull/12957))
Define uniformity of a pair of vertices in a graph and uniformity of a partition of vertices of a graph.
#### Estimated changes
created src/combinatorics/simple_graph/regularity/uniform.lean
- \+ *lemma* is_uniform.mono
- \+ *lemma* is_uniform.symm
- \+ *lemma* is_uniform_comm
- \+ *lemma* is_uniform_singleton
- \+ *lemma* not_is_uniform_zero
- \+ *lemma* is_uniform_one
- \+ *lemma* mk_mem_non_uniforms_iff
- \+ *lemma* non_uniforms_bot
- \+ *lemma* bot_is_uniform
- \+ *lemma* is_uniform_one
- \+ *lemma* is_uniform_of_empty
- \+ *lemma* nonempty_of_not_uniform
- \+ *def* is_uniform
- \+ *def* is_uniform



## [2022-03-31 00:12:51](https://github.com/leanprover-community/mathlib/commit/47b1d78)
feat(linear_algebra/matrix): any matrix power can be expressed as sums of powers `0 ≤ k < fintype.card n` ([#12983](https://github.com/leanprover-community/mathlib/pull/12983))
I'm not familiar enough with the polynomial API to know if we can neatly state a similar result for negative powers.
#### Estimated changes
modified src/data/polynomial/ring_division.lean

modified src/linear_algebra/charpoly/basic.lean
- \+ *lemma* aeval_eq_aeval_mod_charpoly
- \+ *lemma* pow_eq_aeval_mod_charpoly

modified src/linear_algebra/matrix/charpoly/basic.lean

modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+ *lemma* aeval_eq_aeval_mod_charpoly
- \+ *lemma* pow_eq_aeval_mod_charpoly



## [2022-03-30 17:30:25](https://github.com/leanprover-community/mathlib/commit/fc35cb3)
chore(data/finset/card): add `card_disj_union` ([#13061](https://github.com/leanprover-community/mathlib/pull/13061))
#### Estimated changes
modified src/data/finset/card.lean
- \+ *lemma* card_disj_union



## [2022-03-30 16:05:51](https://github.com/leanprover-community/mathlib/commit/7f450cb)
feat(topology/sets/order): Clopen upper sets ([#12670](https://github.com/leanprover-community/mathlib/pull/12670))
Define `clopen_upper_set`, the type of clopen upper sets of an ordered topological space.
#### Estimated changes
created src/topology/sets/order.lean
- \+ *lemma* upper
- \+ *lemma* clopen
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *def* to_upper_set



## [2022-03-30 13:52:41](https://github.com/leanprover-community/mathlib/commit/518e81a)
feat(topology): add lemmas about `frontier` ([#13054](https://github.com/leanprover-community/mathlib/pull/13054))
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* frontier_closure_subset
- \+ *lemma* frontier_interior_subset

modified src/topology/connected.lean
- \+ *lemma* frontier_eq_empty_iff
- \+ *lemma* nonempty_frontier_iff

modified src/topology/subset_properties.lean
- \+ *lemma* is_clopen_iff_frontier_eq_empty



## [2022-03-30 13:52:39](https://github.com/leanprover-community/mathlib/commit/de62b06)
chore(data/set/pointwise): Golf using `set.image2` API ([#13051](https://github.com/leanprover-community/mathlib/pull/13051))
Add some more `set.image2` API and demonstrate use by golfing all relevant `data.set.pointwise` declarations.
Other additions
#### Estimated changes
modified src/algebra/add_torsor.lean

modified src/algebra/opposites.lean

modified src/data/set/basic.lean
- \+ *lemma* image_comm
- \+/\- *lemma* image2_assoc
- \+/\- *lemma* image2_left_comm
- \+/\- *lemma* image2_right_comm
- \+/\- *lemma* image_image2_distrib
- \+/\- *lemma* image_image2_distrib_left
- \+/\- *lemma* image_image2_distrib_right
- \+ *lemma* image2_image_left_comm
- \+ *lemma* image_image2_right_comm
- \+ *lemma* image_image2_antidistrib
- \+ *lemma* image_image2_antidistrib_left
- \+ *lemma* image_image2_antidistrib_right
- \+ *lemma* image2_image_left_anticomm
- \+ *lemma* image_image2_right_anticomm
- \+/\- *lemma* image2_assoc
- \+/\- *lemma* image2_left_comm
- \+/\- *lemma* image2_right_comm
- \+/\- *lemma* image_image2_distrib
- \+/\- *lemma* image_image2_distrib_left
- \+/\- *lemma* image_image2_distrib_right

modified src/data/set/pointwise.lean
- \+/\- *lemma* nonempty.mul
- \+/\- *lemma* finite.mul
- \+/\- *lemma* image_op_mul
- \+/\- *lemma* inv_empty
- \+/\- *lemma* inv_univ
- \+/\- *lemma* mem_inv
- \+/\- *lemma* inv_preimage
- \+/\- *lemma* inter_inv
- \+/\- *lemma* union_inv
- \+/\- *lemma* Inter_inv
- \+/\- *lemma* Union_inv
- \+/\- *lemma* compl_inv
- \+/\- *lemma* inv_mem_inv
- \+/\- *lemma* nonempty_inv
- \+/\- *lemma* nonempty.inv
- \+/\- *lemma* finite.inv
- \+/\- *lemma* image_inv
- \+/\- *lemma* inv_subset_inv
- \+/\- *lemma* inv_subset
- \+/\- *lemma* inv_singleton
- \+ *lemma* image_op_inv
- \+ *lemma* nonempty.smul
- \+ *lemma* finite.smul
- \+ *lemma* nonempty.smul_set
- \+/\- *lemma* finite.smul_set
- \+ *lemma* nonempty.vsub
- \+/\- *lemma* image_mul
- \+/\- *lemma* nonempty.mul
- \+/\- *lemma* finite.mul
- \+/\- *lemma* image_op_mul
- \+/\- *lemma* inv_empty
- \+/\- *lemma* inv_univ
- \+/\- *lemma* nonempty_inv
- \+/\- *lemma* nonempty.inv
- \+/\- *lemma* mem_inv
- \+/\- *lemma* inv_mem_inv
- \+/\- *lemma* inv_preimage
- \+/\- *lemma* image_inv
- \+/\- *lemma* inter_inv
- \+/\- *lemma* union_inv
- \+/\- *lemma* Inter_inv
- \+/\- *lemma* Union_inv
- \+/\- *lemma* compl_inv
- \+/\- *lemma* inv_subset_inv
- \+/\- *lemma* inv_subset
- \+/\- *lemma* finite.inv
- \+/\- *lemma* inv_singleton
- \+/\- *lemma* finite.smul_set
- \+/\- *lemma* image_mul



## [2022-03-30 13:52:38](https://github.com/leanprover-community/mathlib/commit/25e8730)
feat(analysis/special_functions/pow): abs value of real to complex power ([#13048](https://github.com/leanprover-community/mathlib/pull/13048))
#### Estimated changes
modified src/analysis/special_functions/pow.lean
- \+ *lemma* abs_cpow_eq_rpow_re_of_pos
- \+ *lemma* abs_cpow_eq_rpow_re_of_nonneg



## [2022-03-30 13:52:37](https://github.com/leanprover-community/mathlib/commit/33a323c)
feat(data/fin): lemmas about ordering and cons ([#13044](https://github.com/leanprover-community/mathlib/pull/13044))
This marks a few extra facts `simp`, since the analogous facts are `simp` for `nat`.
#### Estimated changes
modified archive/imo/imo1994_q1.lean

modified src/data/fin/basic.lean
- \+/\- *lemma* zero_le
- \+ *lemma* not_lt_zero
- \+/\- *lemma* zero_le

modified src/data/fin/tuple/basic.lean
- \+ *lemma* cons_le_cons
- \+ *lemma* pi_lex_lt_cons_cons



## [2022-03-30 13:52:33](https://github.com/leanprover-community/mathlib/commit/644a848)
fix(tactic/generalize_proofs): instantiate mvars ([#13025](https://github.com/leanprover-community/mathlib/pull/13025))
Reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/generalize_proofs.20failed/near/276965359).
#### Estimated changes
modified src/tactic/generalize_proofs.lean

modified test/generalize_proofs.lean



## [2022-03-30 13:52:32](https://github.com/leanprover-community/mathlib/commit/af3911c)
feat(data/polynomial/erase_lead): add two erase_lead lemmas ([#12910](https://github.com/leanprover-community/mathlib/pull/12910))
The two lemmas show that removing the leading term from the sum of two polynomials of unequal `nat_degree` is the same as removing the leading term of the one of larger `nat_degree` and adding.
The second lemma could be proved with `by rw [add_comm, erase_lead_add_of_nat_degree_lt_left pq, add_comm]`, but I preferred copying the same strategy as the previous one, to avoid interdependencies.
#### Estimated changes
modified src/data/polynomial/erase_lead.lean
- \+ *lemma* erase_lead_add_of_nat_degree_lt_left
- \+ *lemma* erase_lead_add_of_nat_degree_lt_right



## [2022-03-30 13:52:30](https://github.com/leanprover-community/mathlib/commit/e31f031)
feat(analysis/locally_convex): polar sets for dualities ([#12849](https://github.com/leanprover-community/mathlib/pull/12849))
Define the absolute polar for a duality and prove easy properties such as
* `linear_map.polar_eq_Inter`: The polar as an intersection.
* `linear_map.subset_bipolar`: The polar is a subset of the bipolar.
* `linear_map.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.
Moreover, the corresponding lemmas are removed in the normed space setting as they all follow directly from the general case.
#### Estimated changes
created src/analysis/locally_convex/polar.lean
- \+ *lemma* polar_mem_iff
- \+ *lemma* polar_mem
- \+ *lemma* zero_mem_polar
- \+ *lemma* polar_eq_Inter
- \+ *lemma* polar_gc
- \+ *lemma* polar_Union
- \+ *lemma* polar_union
- \+ *lemma* polar_antitone
- \+ *lemma* polar_empty
- \+ *lemma* polar_zero
- \+ *lemma* subset_bipolar
- \+ *lemma* tripolar_eq_polar
- \+ *lemma* polar_weak_closed
- \+ *lemma* polar_univ
- \+ *def* polar

modified src/analysis/normed_space/dual.lean
- \+ *lemma* dual_pairing_apply
- \+ *lemma* dual_pairing_separating_left
- \+ *lemma* mem_polar_iff
- \- *lemma* zero_mem_polar
- \- *lemma* polar_eq_Inter
- \- *lemma* polar_gc
- \- *lemma* polar_Union
- \- *lemma* polar_union
- \- *lemma* polar_antitone
- \- *lemma* polar_empty
- \- *lemma* polar_zero
- \+ *def* dual_pairing

modified src/analysis/normed_space/weak_dual.lean
- \- *lemma* weak_dual.is_closed_polar
- \- *def* polar



## [2022-03-30 11:47:45](https://github.com/leanprover-community/mathlib/commit/f13ee54)
chore(*): sort out some to_additive and simp orderings ([#13038](https://github.com/leanprover-community/mathlib/pull/13038))
- To additive should always come after simp, unless the linter complains.
- Also make to_additive transfer the `protected` attribute for consistency.
#### Estimated changes
modified src/algebra/group/pi.lean

modified src/algebra/group/to_additive.lean

modified src/data/finset/noncomm_prod.lean

modified src/data/part.lean



## [2022-03-30 11:47:44](https://github.com/leanprover-community/mathlib/commit/37a8a0b)
feat(ring_theory/graded_algebra): define homogeneous localisation ([#12784](https://github.com/leanprover-community/mathlib/pull/12784))
This pr defines `homogeneous_localization`. For `x` in projective spectrum of `A`, homogeneous localisation at `x` is the subring of $$A_x$$ containing `a/b` where `a` and `b` have the same degree. This construction is mainly used in constructing structure sheaf of Proj of a graded ring
#### Estimated changes
created src/ring_theory/graded_algebra/homogeneous_localization.lean
- \+ *lemma* ext
- \+ *lemma* deg_one
- \+ *lemma* num_one
- \+ *lemma* denom_one
- \+ *lemma* deg_zero
- \+ *lemma* num_zero
- \+ *lemma* denom_zero
- \+ *lemma* deg_mul
- \+ *lemma* num_mul
- \+ *lemma* denom_mul
- \+ *lemma* deg_add
- \+ *lemma* num_add
- \+ *lemma* denom_add
- \+ *lemma* deg_neg
- \+ *lemma* num_neg
- \+ *lemma* denom_neg
- \+ *lemma* deg_pow
- \+ *lemma* num_pow
- \+ *lemma* denom_pow
- \+ *lemma* deg_smul
- \+ *lemma* num_smul
- \+ *lemma* denom_smul
- \+ *lemma* val_injective
- \+ *lemma* smul_val
- \+ *lemma* zero_eq
- \+ *lemma* one_eq
- \+ *lemma* zero_val
- \+ *lemma* one_val
- \+ *lemma* add_val
- \+ *lemma* mul_val
- \+ *lemma* neg_val
- \+ *lemma* sub_val
- \+ *lemma* pow_val
- \+ *lemma* denom_not_mem
- \+ *lemma* num_mem
- \+ *lemma* denom_mem
- \+ *lemma* eq_num_div_denom
- \+ *lemma* ext_iff_val
- \+ *def* embedding
- \+ *def* homogeneous_localization
- \+ *def* val
- \+ *def* num
- \+ *def* denom
- \+ *def* deg



## [2022-03-30 09:48:05](https://github.com/leanprover-community/mathlib/commit/cdd1703)
feat(algebra/associates): add two instances and a lemma about the order on the monoid of associates of a monoid ([#12863](https://github.com/leanprover-community/mathlib/pull/12863))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* is_unit_iff_eq_bot



## [2022-03-30 03:51:16](https://github.com/leanprover-community/mathlib/commit/cd51f0d)
fix(data/fintype/basic): generalize fintype instance for fintype.card_coe ([#13055](https://github.com/leanprover-community/mathlib/pull/13055))
#### Estimated changes
modified src/combinatorics/hall/finite.lean

modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_coe
- \+/\- *lemma* fintype.card_coe



## [2022-03-30 03:51:14](https://github.com/leanprover-community/mathlib/commit/f2fd6db)
chore(*): removing some `by { dunfold .., apply_instance }` proofs ([#13050](https://github.com/leanprover-community/mathlib/pull/13050))
Replaces the proofs `by { dunfold .., apply_instance }` by the exact term that is outputted by `show_term`.
#### Estimated changes
modified src/linear_algebra/dual.lean

modified src/topology/sheaves/limits.lean

modified src/topology/uniform_space/completion.lean

modified src/topology/uniform_space/separation.lean



## [2022-03-30 03:19:42](https://github.com/leanprover-community/mathlib/commit/ca3bb9e)
chore(scripts): update nolints.txt ([#13057](https://github.com/leanprover-community/mathlib/pull/13057))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-30 02:20:22](https://github.com/leanprover-community/mathlib/commit/fc75855)
feat(measure_theory/*): refactor integral to allow non second-countable target space ([#12942](https://github.com/leanprover-community/mathlib/pull/12942))
Currently, the Bochner integral in mathlib only allows second-countable target spaces. This is an issue, since many constructions in spectral theory require integrals, and spaces of operators are typically not second-countable. The most general definition of the Bochner integral requires functions that may take values in non second-countable spaces, but which are still pointwise limits of a sequence of simple functions (so-called strongly measurable functions) -- equivalently, they are measurable and with second-countable range.
This PR refactors the Bochner integral, working with strongly measurable functions (or rather, almost everywhere strongly measurable functions, i.e., functions which coincide almost everywhere with a strongly measurable function). There are some prerequisistes (topological facts, and a good enough theory of almost everywhere strongly measurable functions) that have been PRed separately, but the remaining part of the change has to be done in one PR, as once one changes the basic definition of the integral one has to change all the files that depend on it.
Once the change is done, in many files the fix is just to remove `[measurable_space E] [borel_space E] [second_countable_topology E]` to make the linter happy, and see that everything still compiles. (Well, sometimes it is also much more painful, of course :-). For end users using `integrable`, nothing has to be changed, but if you need to prove integrability by hand, instead of checking `ae_measurable` you need to check `ae_strongly_measurable`. In second-countable spaces, the two of them are equivalent (and you can use `ae_strongly_measurable.ae_measurable` and `ae_measurable.ae_strongly_measurable` to go between the two of them).
The main changes are the following:
* change `ae_eq_fun` to base it on equivalence classes of ae strongly measurable functions
* fix everything that depends on this definition, including lp_space, set_to_L1, the Bochner integral and conditional expectation
* fix everything that depends on these, notably complex analysis (removing second-countability and measurability assumptions all over the place)
* A notion that involves a measurable function taking values in a normed space should probably better be rephrased in terms of strongly_measurable or ae_strongly_measurable. So, change a few definitions like `measurable_at_filter` (to `strongly_measurable_at_filter`) or `martingale`.
#### Estimated changes
modified counterexamples/phillips.lean

modified src/analysis/ODE/picard_lindelof.lean

modified src/analysis/box_integral/integrability.lean
- \+/\- *lemma* integrable_on.has_box_integral
- \+/\- *lemma* integrable_on.has_box_integral

modified src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* strongly_measurable_deriv
- \+ *lemma* ae_strongly_measurable_deriv

modified src/analysis/calculus/parametric_integral.lean

modified src/analysis/calculus/parametric_interval_integral.lean

modified src/analysis/complex/abs_max.lean

modified src/analysis/complex/cauchy_integral.lean

modified src/analysis/complex/liouville.lean
- \+/\- *lemma* deriv_eq_smul_circle_integral
- \+/\- *lemma* deriv_eq_smul_circle_integral

modified src/analysis/complex/removable_singularity.lean

modified src/analysis/convex/integral.lean

modified src/analysis/fourier.lean

modified src/analysis/normed_space/spectrum.lean

modified src/analysis/normed_space/star/spectrum.lean
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal

modified src/analysis/special_functions/non_integrable.lean

modified src/measure_theory/constructions/prod.lean
- \+/\- *lemma* measurable_set_integrable
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_right
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_right'
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_left
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_left'
- \+ *lemma* measure_theory.ae_strongly_measurable.prod_swap
- \+ *lemma* measure_theory.ae_strongly_measurable.integral_prod_right'
- \+ *lemma* measure_theory.ae_strongly_measurable.prod_mk_left
- \+/\- *lemma* has_finite_integral_prod_iff
- \+/\- *lemma* has_finite_integral_prod_iff'
- \+/\- *lemma* integrable_prod_iff
- \+/\- *lemma* integrable_prod_iff'
- \+/\- *lemma* measurable_set_integrable
- \- *lemma* measurable.integral_prod_right
- \- *lemma* measurable.integral_prod_right'
- \- *lemma* measurable.integral_prod_left
- \- *lemma* measurable.integral_prod_left'
- \- *lemma* ae_measurable.integral_prod_right'
- \- *lemma* ae_measurable.prod_mk_left
- \+/\- *lemma* has_finite_integral_prod_iff
- \+/\- *lemma* has_finite_integral_prod_iff'
- \+/\- *lemma* integrable_prod_iff
- \+/\- *lemma* integrable_prod_iff'

modified src/measure_theory/covering/besicovitch_vector_space.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/decomposition/radon_nikodym.lean

modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* mk_coe_fn
- \+/\- *lemma* induction_on₂
- \+/\- *lemma* induction_on₃
- \+/\- *lemma* comp_mk
- \+/\- *lemma* comp_eq_mk
- \+/\- *lemma* coe_fn_comp
- \+ *lemma* comp_measurable_mk
- \+ *lemma* comp_measurable_eq_mk
- \+ *lemma* coe_fn_comp_measurable
- \+/\- *lemma* comp₂_mk_mk
- \+/\- *lemma* comp₂_eq_pair
- \+/\- *lemma* comp₂_eq_mk
- \+/\- *lemma* coe_fn_comp₂
- \+ *lemma* comp₂_measurable_mk_mk
- \+ *lemma* comp₂_measurable_eq_pair
- \+ *lemma* comp₂_measurable_eq_mk
- \+ *lemma* coe_fn_comp₂_measurable
- \+/\- *lemma* comp_to_germ
- \+ *lemma* comp_measurable_to_germ
- \+/\- *lemma* comp₂_to_germ
- \+ *lemma* comp₂_measurable_to_germ
- \+/\- *lemma* coe_fn_sup
- \+/\- *lemma* coe_fn_inf
- \+/\- *lemma* smul_mk
- \+/\- *lemma* mk_mul_mk
- \+/\- *lemma* mk_div
- \+/\- *lemma* mk_coe_fn
- \+/\- *lemma* induction_on₂
- \+/\- *lemma* induction_on₃
- \+/\- *lemma* comp_mk
- \+/\- *lemma* comp_eq_mk
- \+/\- *lemma* coe_fn_comp
- \+/\- *lemma* comp₂_mk_mk
- \+/\- *lemma* comp₂_eq_pair
- \+/\- *lemma* comp₂_eq_mk
- \+/\- *lemma* coe_fn_comp₂
- \+/\- *lemma* comp_to_germ
- \+/\- *lemma* comp₂_to_germ
- \+/\- *lemma* coe_fn_sup
- \+/\- *lemma* coe_fn_inf
- \+/\- *lemma* smul_mk
- \+/\- *lemma* mk_mul_mk
- \+/\- *lemma* mk_div
- \+/\- *def* measure.ae_eq_setoid
- \+/\- *def* mk
- \+/\- *def* comp
- \+ *def* comp_measurable
- \+/\- *def* comp₂
- \+ *def* comp₂_measurable
- \+/\- *def* const
- \+/\- *def* measure.ae_eq_setoid
- \+/\- *def* mk
- \+/\- *def* comp
- \+/\- *def* comp₂
- \+/\- *def* const

modified src/measure_theory/function/ae_eq_of_integral.lean
- \+ *lemma* ae_eq_zero_of_forall_dual_of_is_separable
- \+/\- *lemma* ae_eq_zero_of_forall_dual
- \+ *lemma* ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable
- \+/\- *lemma* ae_eq_zero_of_forall_dual
- \- *lemma* ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable

modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* congr
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* sub
- \+/\- *lemma* const_smul
- \+/\- *lemma* const_inner
- \+ *lemma* strongly_measurable_mk
- \+/\- *lemma* ae_eq_mk
- \+ *lemma* continuous_comp
- \+ *lemma* ae_strongly_measurable'_of_ae_strongly_measurable'_trim
- \+ *lemma* strongly_measurable.ae_strongly_measurable'
- \+ *lemma* ae_eq_trim_iff_of_ae_strongly_measurable'
- \+ *lemma* mem_Lp_meas_subgroup_iff_ae_strongly_measurable'
- \+ *lemma* mem_Lp_meas_iff_ae_strongly_measurable'
- \+ *lemma* Lp_meas.ae_strongly_measurable'
- \+/\- *lemma* mem_Lp_meas_self
- \+ *lemma* is_complete_ae_strongly_measurable'
- \+ *lemma* is_closed_ae_strongly_measurable'
- \+ *lemma* ae_strongly_measurable'_condexp_L2
- \+/\- *lemma* norm_condexp_L2_le_one
- \+/\- *lemma* inner_condexp_L2_eq_inner_fun
- \+ *lemma* ae_strongly_measurable'_condexp_ind_smul
- \+ *lemma* ae_strongly_measurable'_condexp_ind
- \+ *lemma* ae_strongly_measurable'_condexp_L1_clm
- \+ *lemma* condexp_L1_clm_of_ae_strongly_measurable'
- \+ *lemma* ae_strongly_measurable'_condexp_L1
- \+ *lemma* condexp_L1_of_ae_strongly_measurable'
- \+ *lemma* condexp_of_strongly_measurable
- \+ *lemma* strongly_measurable_condexp
- \+/\- *lemma* congr
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* sub
- \+/\- *lemma* const_smul
- \+/\- *lemma* const_inner
- \- *lemma* measurable_mk
- \+/\- *lemma* ae_eq_mk
- \- *lemma* measurable_comp
- \- *lemma* ae_measurable'_of_ae_measurable'_trim
- \- *lemma* measurable.ae_measurable'
- \- *lemma* ae_eq_trim_iff_of_ae_measurable'
- \- *lemma* mem_Lp_meas_subgroup_iff_ae_measurable'
- \- *lemma* mem_Lp_meas_iff_ae_measurable'
- \- *lemma* Lp_meas.ae_measurable'
- \+/\- *lemma* mem_Lp_meas_self
- \- *lemma* is_complete_ae_measurable'
- \- *lemma* is_closed_ae_measurable'
- \- *lemma* ae_measurable'_condexp_L2
- \+/\- *lemma* norm_condexp_L2_le_one
- \+/\- *lemma* inner_condexp_L2_eq_inner_fun
- \- *lemma* ae_measurable'_condexp_ind_smul
- \- *lemma* ae_measurable'_condexp_ind
- \- *lemma* ae_measurable'_condexp_L1_clm
- \- *lemma* condexp_L1_clm_of_ae_measurable'
- \- *lemma* ae_measurable'_condexp_L1
- \- *lemma* condexp_L1_of_ae_measurable'
- \- *lemma* condexp_of_measurable
- \- *lemma* measurable_condexp
- \+ *def* ae_strongly_measurable'
- \+/\- *def* mk
- \+/\- *def* Lp_meas
- \- *def* ae_measurable'
- \+/\- *def* mk
- \+/\- *def* Lp_meas

modified src/measure_theory/function/continuous_map_dense.lean

modified src/measure_theory/function/convergence_in_measure.lean
- \+ *lemma* tendsto_in_measure_of_tendsto_ae_of_strongly_measurable
- \+/\- *lemma* tendsto_in_measure_of_tendsto_ae
- \+ *lemma* tendsto_in_measure_of_tendsto_snorm_of_strongly_measurable
- \+/\- *lemma* tendsto_in_measure_of_tendsto_snorm
- \+/\- *lemma* tendsto_in_measure_of_tendsto_Lp
- \- *lemma* tendsto_in_measure_of_tendsto_ae_of_measurable
- \+/\- *lemma* tendsto_in_measure_of_tendsto_ae
- \- *lemma* tendsto_in_measure_of_tendsto_snorm_of_measurable
- \+/\- *lemma* tendsto_in_measure_of_tendsto_snorm
- \+/\- *lemma* tendsto_in_measure_of_tendsto_Lp

modified src/measure_theory/function/egorov.lean

modified src/measure_theory/function/jacobian.lean

modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* lintegral_edist_triangle
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* tendsto_lintegral_norm_of_dominated_convergence
- \+ *lemma* integrable.ae_strongly_measurable
- \+/\- *lemma* integrable.ae_measurable
- \+/\- *lemma* integrable.mono
- \+/\- *lemma* integrable.mono'
- \+/\- *lemma* integrable.congr'
- \+/\- *lemma* integrable_congr'
- \+/\- *lemma* integrable_map_measure
- \+/\- *lemma* integrable.comp_measurable
- \+/\- *lemma* _root_.measurable_embedding.integrable_map_iff
- \+/\- *lemma* measure_preserving.integrable_comp
- \+/\- *lemma* lintegral_edist_lt_top
- \+/\- *lemma* integrable.add'
- \+/\- *lemma* integrable.add
- \+/\- *lemma* integrable_finset_sum
- \+/\- *lemma* integrable.neg
- \+/\- *lemma* integrable_neg_iff
- \+/\- *lemma* integrable.sub'
- \+/\- *lemma* integrable.sub
- \+/\- *lemma* integrable.norm
- \+/\- *lemma* integrable_norm_iff
- \+/\- *lemma* integrable_of_norm_sub_le
- \+/\- *lemma* integrable.prod_mk
- \+/\- *lemma* mem_ℒp.integrable
- \+/\- *lemma* lipschitz_with.integrable_comp_iff_of_antilipschitz
- \+/\- *lemma* integrable.max_zero
- \+/\- *lemma* integrable.min_zero
- \+/\- *lemma* integrable.smul
- \+/\- *lemma* integrable_smul_iff
- \+/\- *lemma* integrable.trim
- \+/\- *lemma* integrable_of_forall_fin_meas_le'
- \+/\- *lemma* integrable_mk
- \+ *lemma* strongly_measurable_coe_fn
- \+/\- *lemma* measurable_coe_fn
- \+ *lemma* ae_strongly_measurable_coe_fn
- \+/\- *lemma* ae_measurable_coe_fn
- \+/\- *lemma* lintegral_edist_triangle
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* tendsto_lintegral_norm_of_dominated_convergence
- \+/\- *lemma* integrable.ae_measurable
- \+/\- *lemma* integrable.mono
- \+/\- *lemma* integrable.mono'
- \+/\- *lemma* integrable.congr'
- \+/\- *lemma* integrable_congr'
- \+/\- *lemma* integrable_map_measure
- \+/\- *lemma* integrable.comp_measurable
- \+/\- *lemma* _root_.measurable_embedding.integrable_map_iff
- \+/\- *lemma* measure_preserving.integrable_comp
- \+/\- *lemma* lintegral_edist_lt_top
- \+/\- *lemma* integrable.add'
- \+/\- *lemma* integrable.add
- \+/\- *lemma* integrable_finset_sum
- \+/\- *lemma* integrable.neg
- \+/\- *lemma* integrable_neg_iff
- \+/\- *lemma* integrable.sub'
- \+/\- *lemma* integrable.sub
- \+/\- *lemma* integrable.norm
- \+/\- *lemma* integrable_norm_iff
- \+/\- *lemma* integrable_of_norm_sub_le
- \+/\- *lemma* integrable.prod_mk
- \+/\- *lemma* mem_ℒp.integrable
- \+/\- *lemma* lipschitz_with.integrable_comp_iff_of_antilipschitz
- \+/\- *lemma* integrable.max_zero
- \+/\- *lemma* integrable.min_zero
- \+/\- *lemma* integrable.smul
- \+/\- *lemma* integrable_smul_iff
- \+/\- *lemma* integrable.trim
- \+/\- *lemma* integrable_of_forall_fin_meas_le'
- \+/\- *lemma* integrable_mk
- \+/\- *lemma* measurable_coe_fn
- \+/\- *lemma* ae_measurable_coe_fn

modified src/measure_theory/function/l2_space.lean

modified src/measure_theory/function/locally_integrable.lean

modified src/measure_theory/function/lp_order.lean

modified src/measure_theory/function/lp_space.lean
- \+ *lemma* mem_ℒp.ae_strongly_measurable
- \+ *lemma* mem_ℒp_zero_iff_ae_strongly_measurable
- \+/\- *lemma* mem_ℒp.of_le
- \+/\- *lemma* mem_ℒp.congr_norm
- \+/\- *lemma* mem_ℒp_congr_norm
- \+/\- *lemma* mem_ℒp_top_of_bound
- \+/\- *lemma* mem_ℒp.of_bound
- \+/\- *lemma* mem_ℒp_norm_iff
- \+/\- *lemma* ae_eq_zero_of_snorm'_eq_zero
- \+/\- *lemma* snorm'_eq_zero_iff
- \+/\- *lemma* snorm_eq_zero_iff
- \+/\- *lemma* snorm'_add_le
- \+/\- *lemma* snorm_add_le
- \+/\- *lemma* snorm_sub_le
- \+/\- *lemma* snorm'_add_lt_top_of_le_one
- \+/\- *lemma* snorm_ess_sup_map_measure
- \+/\- *lemma* snorm_map_measure
- \+/\- *lemma* mem_ℒp_map_measure_iff
- \+/\- *lemma* _root_.measurable_embedding.mem_ℒp_map_measure_iff
- \+/\- *lemma* _root_.measurable_equiv.mem_ℒp_map_measure_iff
- \+/\- *lemma* snorm'_trim
- \+/\- *lemma* limsup_trim
- \+/\- *lemma* ess_sup_trim
- \+/\- *lemma* snorm_ess_sup_trim
- \+/\- *lemma* snorm_trim
- \+/\- *lemma* snorm_trim_ae
- \+/\- *lemma* meas_ge_le_mul_pow_snorm
- \+/\- *lemma* mem_ℒp.const_smul
- \+/\- *lemma* mem_ℒp.const_mul
- \+/\- *lemma* snorm'_smul_le_mul_snorm'
- \+/\- *lemma* mem_ℒp.of_le_mul
- \+/\- *lemma* norm_le_mul_norm_of_ae_le_mul
- \+/\- *lemma* norm_le_norm_of_ae_le
- \+/\- *lemma* mem_Lp_of_ae_le_mul
- \+/\- *lemma* mem_Lp_of_ae_le
- \+/\- *lemma* mem_ℒp.norm_rpow
- \+/\- *lemma* smul_comp_Lp
- \+/\- *lemma* smul_comp_LpL_apply
- \+/\- *lemma* snorm'_lim_le_liminf_snorm'
- \+/\- *lemma* snorm_lim_le_liminf_snorm
- \+/\- *lemma* cauchy_tendsto_of_tendsto
- \+/\- *lemma* range_to_Lp
- \+/\- *lemma* coe_fn_to_Lp
- \+/\- *lemma* to_Lp_norm_le
- \+/\- *lemma* range_to_Lp
- \+/\- *lemma* coe_fn_to_Lp
- \+/\- *lemma* to_Lp_def
- \+/\- *lemma* to_Lp_comp_to_continuous_map
- \+/\- *lemma* coe_to_Lp
- \- *lemma* mem_ℒp.ae_measurable
- \- *lemma* mem_ℒp_zero_iff_ae_measurable
- \+/\- *lemma* mem_ℒp.of_le
- \+/\- *lemma* mem_ℒp.congr_norm
- \+/\- *lemma* mem_ℒp_congr_norm
- \+/\- *lemma* mem_ℒp_top_of_bound
- \+/\- *lemma* mem_ℒp.of_bound
- \+/\- *lemma* mem_ℒp_norm_iff
- \+/\- *lemma* ae_eq_zero_of_snorm'_eq_zero
- \+/\- *lemma* snorm'_eq_zero_iff
- \+/\- *lemma* snorm_eq_zero_iff
- \+/\- *lemma* snorm'_add_le
- \+/\- *lemma* snorm_add_le
- \+/\- *lemma* snorm_sub_le
- \+/\- *lemma* snorm'_add_lt_top_of_le_one
- \+/\- *lemma* snorm_ess_sup_map_measure
- \+/\- *lemma* snorm_map_measure
- \+/\- *lemma* mem_ℒp_map_measure_iff
- \+/\- *lemma* _root_.measurable_embedding.mem_ℒp_map_measure_iff
- \+/\- *lemma* _root_.measurable_equiv.mem_ℒp_map_measure_iff
- \+/\- *lemma* snorm'_trim
- \+/\- *lemma* limsup_trim
- \+/\- *lemma* ess_sup_trim
- \+/\- *lemma* snorm_ess_sup_trim
- \+/\- *lemma* snorm_trim
- \+/\- *lemma* snorm_trim_ae
- \+/\- *lemma* meas_ge_le_mul_pow_snorm
- \+/\- *lemma* mem_ℒp.const_smul
- \+/\- *lemma* mem_ℒp.const_mul
- \+/\- *lemma* snorm'_smul_le_mul_snorm'
- \+/\- *lemma* mem_ℒp.of_le_mul
- \+/\- *lemma* norm_le_mul_norm_of_ae_le_mul
- \+/\- *lemma* norm_le_norm_of_ae_le
- \+/\- *lemma* mem_Lp_of_ae_le_mul
- \+/\- *lemma* mem_Lp_of_ae_le
- \+/\- *lemma* mem_ℒp.norm_rpow
- \+/\- *lemma* smul_comp_Lp
- \+/\- *lemma* smul_comp_LpL_apply
- \+/\- *lemma* snorm'_lim_le_liminf_snorm'
- \+/\- *lemma* snorm_lim_le_liminf_snorm
- \+/\- *lemma* cauchy_tendsto_of_tendsto
- \+/\- *lemma* range_to_Lp
- \+/\- *lemma* coe_fn_to_Lp
- \+/\- *lemma* to_Lp_norm_le
- \+/\- *lemma* range_to_Lp
- \+/\- *lemma* coe_fn_to_Lp
- \+/\- *lemma* to_Lp_def
- \+/\- *lemma* to_Lp_comp_to_continuous_map
- \+/\- *lemma* coe_to_Lp
- \+/\- *def* Lp
- \+/\- *def* to_Lp
- \+/\- *def* to_Lp
- \+/\- *def* Lp
- \+/\- *def* to_Lp
- \+/\- *def* to_Lp

modified src/measure_theory/function/simple_func_dense.lean

modified src/measure_theory/function/simple_func_dense_lp.lean
- \+ *lemma* tendsto_approx_on_range_Lp_snorm
- \+ *lemma* mem_ℒp_approx_on_range
- \+ *lemma* tendsto_approx_on_range_Lp
- \+ *lemma* tendsto_approx_on_range_L1_nnnorm
- \+ *lemma* integrable_approx_on_range
- \+/\- *lemma* integrable_pair
- \- *lemma* tendsto_approx_on_univ_Lp_snorm
- \- *lemma* mem_ℒp_approx_on_univ
- \- *lemma* tendsto_approx_on_univ_Lp
- \- *lemma* tendsto_approx_on_univ_L1_nnnorm
- \- *lemma* integrable_approx_on_univ
- \+/\- *lemma* integrable_pair

modified src/measure_theory/function/strongly_measurable.lean

modified src/measure_theory/function/strongly_measurable_lp.lean
- \+ *lemma* mem_ℒp.fin_strongly_measurable_of_strongly_measurable
- \- *lemma* mem_ℒp.fin_strongly_measurable_of_measurable

modified src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* uniform_integrable.strongly_measurable
- \+/\- *lemma* uniform_integrable.unif_integrable
- \+/\- *lemma* uniform_integrable.mem_ℒp
- \+/\- *lemma* tendsto_Lp_of_tendsto_ae_of_meas
- \+/\- *lemma* tendsto_Lp_of_tendsto_ae
- \+/\- *lemma* unif_integrable_of_tendsto_Lp
- \+/\- *lemma* tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* tendsto_in_measure_iff_tendsto_Lp
- \+/\- *lemma* unif_integrable_of'
- \+/\- *lemma* unif_integrable_of
- \+/\- *lemma* uniform_integrable_zero_meas
- \- *lemma* uniform_integrable.measurable
- \+/\- *lemma* uniform_integrable.unif_integrable
- \+/\- *lemma* uniform_integrable.mem_ℒp
- \+/\- *lemma* tendsto_Lp_of_tendsto_ae_of_meas
- \+/\- *lemma* tendsto_Lp_of_tendsto_ae
- \+/\- *lemma* unif_integrable_of_tendsto_Lp
- \+/\- *lemma* tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* tendsto_in_measure_iff_tendsto_Lp
- \+/\- *lemma* unif_integrable_of'
- \+/\- *lemma* unif_integrable_of
- \+/\- *lemma* uniform_integrable_zero_meas
- \+/\- *def* uniform_integrable
- \+/\- *def* uniform_integrable

modified src/measure_theory/group/fundamental_domain.lean

modified src/measure_theory/group/integration.lean

modified src/measure_theory/integral/average.lean

modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* integral_smul
- \+ *lemma* integral_non_ae_strongly_measurable
- \+/\- *lemma* integral_smul
- \+/\- *lemma* integral_eq_lintegral_of_nonneg_ae
- \+/\- *lemma* integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* of_real_integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* tendsto_integral_approx_on_of_measurable
- \+ *lemma* tendsto_integral_approx_on_of_measurable_of_range_subset
- \+ *lemma* integral_map_of_strongly_measurable
- \+/\- *lemma* integral_dirac'
- \+/\- *lemma* integral_trim
- \+/\- *lemma* integral_trim_ae
- \+ *lemma* ae_eq_trim_of_strongly_measurable
- \+/\- *lemma* ae_eq_trim_iff
- \+/\- *lemma* integral_smul
- \- *lemma* integral_non_ae_measurable
- \+/\- *lemma* integral_smul
- \+/\- *lemma* integral_eq_lintegral_of_nonneg_ae
- \+/\- *lemma* integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* of_real_integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* tendsto_integral_approx_on_of_measurable
- \- *lemma* tendsto_integral_approx_on_univ_of_measurable
- \- *lemma* integral_map_of_measurable
- \+/\- *lemma* integral_dirac'
- \+/\- *lemma* integral_trim
- \+/\- *lemma* integral_trim_ae
- \- *lemma* ae_eq_trim_of_measurable
- \+/\- *lemma* ae_eq_trim_iff

modified src/measure_theory/integral/circle_integral.lean
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* out
- \+/\- *lemma* circle_integrable_iff
- \+/\- *lemma* continuous_on.circle_integrable'
- \+/\- *lemma* continuous_on.circle_integrable
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* out
- \+/\- *lemma* circle_integrable_iff
- \+/\- *lemma* continuous_on.circle_integrable'
- \+/\- *lemma* continuous_on.circle_integrable

modified src/measure_theory/integral/divergence_theorem.lean

modified src/measure_theory/integral/exp_decay.lean
- \+/\- *lemma* exp_neg_integrable_on_Ioi
- \+/\- *lemma* exp_neg_integrable_on_Ioi

modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* strongly_measurable_at_bot
- \+ *lemma* ae_strongly_measurable.strongly_measurable_at_filter_of_mem
- \+/\- *lemma* integrable_on_singleton_iff
- \+/\- *lemma* integrable_indicator_const_Lp
- \+/\- *lemma* integrable_on_Lp_of_measure_ne_top
- \+ *lemma* continuous_on.ae_strongly_measurable_of_is_separable
- \+ *lemma* continuous_on.ae_strongly_measurable
- \+ *lemma* continuous_on.integrable_at_nhds_within_of_is_separable
- \+ *lemma* continuous_on.strongly_measurable_at_filter
- \+ *lemma* continuous_at.strongly_measurable_at_filter
- \+ *lemma* continuous.strongly_measurable_at_filter
- \+ *lemma* continuous_on.strongly_measurable_at_filter_nhds_within
- \- *lemma* measurable_at_bot
- \- *lemma* ae_measurable.measurable_at_filter_of_mem
- \+/\- *lemma* integrable_on_singleton_iff
- \+/\- *lemma* integrable_indicator_const_Lp
- \+/\- *lemma* integrable_on_Lp_of_measure_ne_top
- \+ *def* strongly_measurable_at_filter
- \- *def* measurable_at_filter

modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* ae_cover.ae_strongly_measurable

modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* neg
- \+/\- *lemma* norm
- \+/\- *lemma* mono_fun
- \+/\- *lemma* smul
- \+/\- *lemma* add
- \+/\- *lemma* sub
- \+/\- *lemma* continuous_on.interval_integrable
- \+/\- *lemma* continuous_on.interval_integrable_of_Icc
- \+/\- *lemma* continuous.interval_integrable
- \+ *lemma* integral_non_ae_strongly_measurable
- \+ *lemma* integral_non_ae_strongly_measurable_of_le
- \+/\- *lemma* interval_integrable_iff_integrable_Icc_of_le
- \+/\- *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae
- \+/\- *lemma* neg
- \+/\- *lemma* norm
- \+/\- *lemma* mono_fun
- \+/\- *lemma* smul
- \+/\- *lemma* add
- \+/\- *lemma* sub
- \+/\- *lemma* continuous_on.interval_integrable
- \+/\- *lemma* continuous_on.interval_integrable_of_Icc
- \+/\- *lemma* continuous.interval_integrable
- \- *lemma* integral_non_ae_measurable
- \- *lemma* integral_non_ae_measurable_of_le
- \+/\- *lemma* interval_integrable_iff_integrable_Icc_of_le
- \+/\- *lemma* measure_integral_sub_linear_is_o_of_tendsto_ae

modified src/measure_theory/integral/periodic.lean

modified src/measure_theory/integral/set_integral.lean
- \+/\- *lemma* set_integral_eq_zero_of_forall_eq_zero
- \+/\- *lemma* set_integral_union_eq_left
- \+/\- *lemma* integral_norm_eq_pos_sub_neg
- \+/\- *lemma* set_integral_le_nonneg
- \+/\- *lemma* set_integral_nonpos_le
- \+/\- *lemma* set_integral_eq_zero_of_forall_eq_zero
- \+/\- *lemma* set_integral_union_eq_left
- \+/\- *lemma* integral_norm_eq_pos_sub_neg
- \+/\- *lemma* set_integral_le_nonneg
- \+/\- *lemma* set_integral_nonpos_le
- \- *lemma* continuous_on.measurable_at_filter
- \- *lemma* continuous_at.measurable_at_filter
- \- *lemma* continuous.measurable_at_filter
- \- *lemma* continuous_on.measurable_at_filter_nhds_within

modified src/measure_theory/integral/set_to_l1.lean
- \+/\- *lemma* set_to_simple_func_smul
- \+/\- *lemma* set_to_simple_func_nonneg'
- \+/\- *lemma* set_to_simple_func_mono
- \+/\- *lemma* norm_eq_sum_mul
- \+/\- *lemma* set_to_L1s_smul
- \+ *lemma* set_to_fun_non_ae_strongly_measurable
- \+/\- *lemma* set_to_fun_smul
- \+/\- *lemma* continuous_L1_to_L1
- \+/\- *lemma* set_to_simple_func_smul
- \+/\- *lemma* set_to_simple_func_nonneg'
- \+/\- *lemma* set_to_simple_func_mono
- \+/\- *lemma* norm_eq_sum_mul
- \+/\- *lemma* set_to_L1s_smul
- \- *lemma* set_to_fun_non_ae_measurable
- \+/\- *lemma* set_to_fun_smul
- \+/\- *lemma* continuous_L1_to_L1

modified src/measure_theory/integral/vitali_caratheodory.lean

modified src/measure_theory/measure/with_density_vector_measure.lean

modified src/probability/density.lean

modified src/probability/martingale.lean
- \+ *lemma* strongly_measurable
- \+ *lemma* strongly_measurable
- \+ *lemma* strongly_measurable
- \- *lemma* measurable
- \- *lemma* measurable
- \- *lemma* measurable

modified src/probability/stopping.lean
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* smul
- \+/\- *lemma* prog_measurable_of_tendsto'
- \+/\- *lemma* prog_measurable_of_tendsto
- \+/\- *lemma* adapted_natural
- \+/\- *lemma* adapted.prog_measurable_of_nat
- \+/\- *lemma* adapted.stopped_process_of_nat
- \+/\- *lemma* adapted.measurable_stopped_process_of_nat
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* smul
- \+/\- *lemma* prog_measurable_of_tendsto'
- \+/\- *lemma* prog_measurable_of_tendsto
- \+/\- *lemma* adapted_natural
- \+/\- *lemma* adapted.prog_measurable_of_nat
- \+/\- *lemma* adapted.stopped_process_of_nat
- \+/\- *lemma* adapted.measurable_stopped_process_of_nat
- \+/\- *theorem* adapted.prog_measurable_of_continuous
- \+/\- *theorem* adapted.prog_measurable_of_continuous
- \+/\- *def* natural
- \+/\- *def* natural

modified src/topology/metric_space/basic.lean



## [2022-03-30 02:20:21](https://github.com/leanprover-community/mathlib/commit/d28a163)
feat(linear_algebra/dual): define the algebraic dual pairing ([#12827](https://github.com/leanprover-community/mathlib/pull/12827))
We define the pairing of algebraic dual and show that it is nondegenerate.
#### Estimated changes
modified src/linear_algebra/dual.lean
- \+ *lemma* dual_pairing_apply
- \+ *lemma* dual_pairing_nondegenerate
- \+ *def* dual_pairing

modified src/linear_algebra/sesquilinear_form.lean



## [2022-03-30 00:29:28](https://github.com/leanprover-community/mathlib/commit/c594e2b)
feat(algebra/ring/basic): neg_zero for distrib_neg ([#13049](https://github.com/leanprover-community/mathlib/pull/13049))
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+ *lemma* neg_zero'



## [2022-03-30 00:29:27](https://github.com/leanprover-community/mathlib/commit/b446c49)
feat(set_theory/cardinal): bit lemmas for exponentiation ([#13010](https://github.com/leanprover-community/mathlib/pull/13010))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *theorem* power_bit0
- \+ *theorem* power_bit1



## [2022-03-30 00:29:26](https://github.com/leanprover-community/mathlib/commit/92b29c7)
fix(tactic/norm_num): make norm_num user command match norm_num better ([#12667](https://github.com/leanprover-community/mathlib/pull/12667))
Corrects some issues with the `#norm_num` user command that prevented it from fully normalizing expressions. Also, adds `expr.norm_num`.
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



## [2022-03-29 23:57:24](https://github.com/leanprover-community/mathlib/commit/523d177)
feat(combinatorics/simple_graph/regularity/energy): Energy of a partition ([#12958](https://github.com/leanprover-community/mathlib/pull/12958))
Define the energy of a partition.
#### Estimated changes
created src/combinatorics/simple_graph/regularity/energy.lean
- \+ *lemma* energy_nonneg
- \+ *lemma* energy_le_one
- \+ *def* energy



## [2022-03-29 23:24:55](https://github.com/leanprover-community/mathlib/commit/50903f0)
feat(algebra/algebra/unitization): define unitization of a non-unital algebra ([#12601](https://github.com/leanprover-community/mathlib/pull/12601))
Given a non-unital `R`-algebra `A` (given via the type classes `[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct the minimal unital `R`-algebra containing `A` as an ideal. This object `unitization R A` is a type synonym for `R × A` on which we place a different multiplicative structure, namely, `(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity is `(1, 0)`.
#### Estimated changes
created src/algebra/algebra/unitization.lean
- \+ *lemma* ext
- \+ *lemma* fst_inl
- \+ *lemma* snd_inl
- \+ *lemma* fst_coe
- \+ *lemma* snd_coe
- \+ *lemma* inl_injective
- \+ *lemma* coe_injective
- \+ *lemma* fst_zero
- \+ *lemma* snd_zero
- \+ *lemma* fst_add
- \+ *lemma* snd_add
- \+ *lemma* fst_neg
- \+ *lemma* snd_neg
- \+ *lemma* fst_smul
- \+ *lemma* snd_smul
- \+ *lemma* inl_zero
- \+ *lemma* inl_add
- \+ *lemma* inl_neg
- \+ *lemma* inl_smul
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_smul
- \+ *lemma* inl_fst_add_coe_snd_eq
- \+ *lemma* ind
- \+ *lemma* linear_map_ext
- \+ *lemma* fst_one
- \+ *lemma* snd_one
- \+ *lemma* fst_mul
- \+ *lemma* snd_mul
- \+ *lemma* inl_one
- \+ *lemma* inl_mul
- \+ *lemma* inl_mul_inl
- \+ *lemma* coe_mul
- \+ *lemma* inl_mul_coe
- \+ *lemma* coe_mul_inl
- \+ *lemma* algebra_map_eq_inl_comp
- \+ *lemma* algebra_map_eq_inl_ring_hom_comp
- \+ *lemma* algebra_map_eq_inl
- \+ *lemma* algebra_map_eq_inl_hom
- \+ *lemma* alg_hom_ext
- \+ *lemma* alg_hom_ext'
- \+ *lemma* lift_symm_apply
- \+ *def* unitization
- \+ *def* inl
- \+ *def* fst
- \+ *def* snd
- \+ *def* coe_hom
- \+ *def* snd_hom
- \+ *def* inl_ring_hom
- \+ *def* fst_hom
- \+ *def* coe_non_unital_alg_hom
- \+ *def* lift



## [2022-03-29 20:37:44](https://github.com/leanprover-community/mathlib/commit/119eb05)
chore(ring_theory/valuation/basic): fix valuation_apply ([#13045](https://github.com/leanprover-community/mathlib/pull/13045))
Follow-up to [#12914](https://github.com/leanprover-community/mathlib/pull/12914).
#### Estimated changes
modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* valuation_apply
- \+/\- *lemma* valuation_apply



## [2022-03-29 20:37:43](https://github.com/leanprover-community/mathlib/commit/e4c6449)
feat(algebra/module): `sub_mem_iff_left` and `sub_mem_iff_right` ([#13043](https://github.com/leanprover-community/mathlib/pull/13043))
Since it's a bit of a hassle to rewrite `add_mem_iff_left` and `add_mem_iff_right` to subtraction, I made a new pair of lemmas.
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+ *lemma* sub_mem_iff_left
- \+ *lemma* sub_mem_iff_right



## [2022-03-29 20:37:42](https://github.com/leanprover-community/mathlib/commit/9aec6df)
feat(algebra/algebra/tower): `span A s = span R s` if `R → A` is surjective ([#13042](https://github.com/leanprover-community/mathlib/pull/13042))
#### Estimated changes
modified src/algebra/algebra/tower.lean
- \+ *lemma* span_restrict_scalars_eq_span_of_surjective
- \+ *lemma* coe_span_eq_span_of_surjective



## [2022-03-29 18:32:04](https://github.com/leanprover-community/mathlib/commit/d3684bc)
feat(category_theory/abelian): constructor in terms of coimage-image comparison ([#12972](https://github.com/leanprover-community/mathlib/pull/12972))
The "stacks constructor" for an abelian category, following https://stacks.math.columbia.edu/tag/0109.
I also factored out the canonical morphism from the abelian coimage to the abelian image (which exists whether or not the category is abelian), and reformulated `abelian.coimage_iso_image` in terms of an `is_iso` instance for this morphism.
#### Estimated changes
modified src/category_theory/abelian/basic.lean
- \+ *lemma* image_mono_factorisation_e'
- \+ *lemma* has_images
- \- *lemma* full_image_factorisation
- \+ *def* image_mono_factorisation
- \+ *def* image_factorisation
- \+ *def* normal_mono_category
- \+ *def* normal_epi_category
- \+ *def* of_coimage_image_comparison_is_iso

modified src/category_theory/abelian/exact.lean

modified src/category_theory/abelian/images.lean
- \+ *lemma* coimage_image_comparison_eq_coimage_image_comparison'
- \+ *lemma* coimage_image_factorisation
- \+ *def* coimage_image_comparison
- \+ *def* coimage_image_comparison'

modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* has_zero_object_of_has_finite_biproducts

modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* mono_factorisation.kernel_ι_comp

modified src/data/fin/basic.lean
- \+ *def* elim0'



## [2022-03-29 17:44:57](https://github.com/leanprover-community/mathlib/commit/e92ecff)
feat(algebra/direct_sum/module): link `direct_sum.submodule_is_internal` to `is_compl` ([#12671](https://github.com/leanprover-community/mathlib/pull/12671))
This is then used to show the even and odd components of a clifford algebra are complementary.
#### Estimated changes
modified src/algebra/direct_sum/module.lean
- \+ *lemma* submodule_is_internal.is_compl
- \+ *lemma* submodule_is_internal_iff_is_compl

modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* even_odd_is_compl



## [2022-03-29 17:11:21](https://github.com/leanprover-community/mathlib/commit/90f0bee)
chore(analysis/normed_space/exponential): fix lemma names in docstrings ([#13032](https://github.com/leanprover-community/mathlib/pull/13032))
#### Estimated changes
modified src/analysis/normed_space/exponential.lean



## [2022-03-29 14:38:00](https://github.com/leanprover-community/mathlib/commit/993d576)
chore(data/list/pairwise): add `pairwise_bind` ([#13030](https://github.com/leanprover-community/mathlib/pull/13030))
#### Estimated changes
modified src/data/list/pairwise.lean
- \+ *lemma* pairwise_bind



## [2022-03-29 14:37:59](https://github.com/leanprover-community/mathlib/commit/8999813)
chore(data/list): two lemmas about bind ([#13029](https://github.com/leanprover-community/mathlib/pull/13029))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* bind_congr

modified src/data/list/join.lean
- \+ *lemma* bind_eq_nil



## [2022-03-29 14:37:58](https://github.com/leanprover-community/mathlib/commit/cedf022)
feat(ring_theory/valuation/basic): add add_valuation.valuation ([#12914](https://github.com/leanprover-community/mathlib/pull/12914))
#### Estimated changes
modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation_apply
- \+ *def* valuation



## [2022-03-29 13:10:46](https://github.com/leanprover-community/mathlib/commit/84b8b0d)
chore(topology/vector_bundle): fix timeout by optimizing proof ([#13026](https://github.com/leanprover-community/mathlib/pull/13026))
This PR speeds up a big and slow definition using `simp only` and `convert` → `refine`. This declaration seems to be on the edge of timing out and some other changes like [#11750](https://github.com/leanprover-community/mathlib/pull/11750) tripped it up.
Time saved if I run it with timeouts disabled:
 * master 14.8s → 6.3s
 * [#11750](https://github.com/leanprover-community/mathlib/pull/11750) 14.2s → 6.12s
#### Estimated changes
modified src/topology/vector_bundle.lean



## [2022-03-29 13:10:45](https://github.com/leanprover-community/mathlib/commit/d5fee32)
chore(algebra/field_power): slightly simplify proof of min_le_of_zpow_le_max ([#13023](https://github.com/leanprover-community/mathlib/pull/13023))
#### Estimated changes
modified src/algebra/field_power.lean



## [2022-03-29 13:10:44](https://github.com/leanprover-community/mathlib/commit/541c80d)
feat(group_theory/index): Golf proof of `relindex_eq_zero_of_le_left` ([#13014](https://github.com/leanprover-community/mathlib/pull/13014))
This PR uses `relindex_dvd_of_le_left` to golf the proof of `relindex_eq_zero_of_le_left`.
#### Estimated changes
modified src/group_theory/index.lean



## [2022-03-29 13:10:43](https://github.com/leanprover-community/mathlib/commit/e109c8f)
feat(topology): basis for `𝓤 C(α, β)` and convergence of a series of `f : C(α, β)` ([#11229](https://github.com/leanprover-community/mathlib/pull/11229))
* add `filter.has_basis.compact_convergence_uniformity`;
* add a few facts about `compacts X`;
* add `summable_of_locally_summable_norm`.
#### Estimated changes
modified src/topology/continuous_function/compact.lean
- \+ *lemma* summable_of_locally_summable_norm

modified src/topology/sets/compacts.lean

modified src/topology/uniform_space/compact_convergence.lean
- \+ *lemma* has_basis_compact_convergence_uniformity_aux
- \+ *lemma* _root_.filter.has_basis.compact_convergence_uniformity



## [2022-03-29 11:26:23](https://github.com/leanprover-community/mathlib/commit/66509e1)
feat(data/polynomial/div): `a - b ∣ p.eval a - p.eval b` ([#13021](https://github.com/leanprover-community/mathlib/pull/13021))
#### Estimated changes
modified src/data/polynomial/div.lean
- \+ *lemma* sub_dvd_eval_sub



## [2022-03-29 11:26:22](https://github.com/leanprover-community/mathlib/commit/111d3a4)
chore(data/polynomial/eval): golf two proofs involving evals ([#13020](https://github.com/leanprover-community/mathlib/pull/13020))
I shortened two proofs involving `eval/eval₂/comp`.
#### Estimated changes
modified src/data/polynomial/eval.lean



## [2022-03-29 11:26:21](https://github.com/leanprover-community/mathlib/commit/b87c267)
feat(topology/algebra/group): add small topology lemma ([#12931](https://github.com/leanprover-community/mathlib/pull/12931))
Adds a small topology lemma by splitting `compact_open_separated_mul` into `compact_open_separated_mul_left/right`, which was useful in my proof of `Steinhaus theorem` (see [#12932](https://github.com/leanprover-community/mathlib/pull/12932)), as in a non-abelian group, the current version was not sufficient.
#### Estimated changes
modified src/algebra/ring/opposite.lean

modified src/data/set/pointwise.lean
- \+ *lemma* image_op_mul

modified src/measure_theory/measure/haar.lean

modified src/topology/algebra/group.lean
- \+ *lemma* compact_open_separated_mul_right
- \+ *lemma* compact_open_separated_mul_left
- \- *lemma* compact_open_separated_mul

modified src/topology/algebra/ring.lean



## [2022-03-29 09:36:12](https://github.com/leanprover-community/mathlib/commit/89c8112)
feat(topology/algebra/monoid): `finprod` is eventually equal to `finset.prod` ([#13013](https://github.com/leanprover-community/mathlib/pull/13013))
Motivated by https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Using.20partitions.20of.20unity
#### Estimated changes
modified src/geometry/manifold/algebra/monoid.lean

modified src/topology/algebra/monoid.lean
- \+ *lemma* locally_finite.exists_finset_mul_support
- \+ *lemma* finprod_eventually_eq_prod



## [2022-03-29 09:36:11](https://github.com/leanprover-community/mathlib/commit/545c265)
feat(data/polynomial/derivative): if `p` is a polynomial, then `p.derivative.nat_degree ≤ p.nat_degree - 1` ([#12948](https://github.com/leanprover-community/mathlib/pull/12948))
I also golfed the proof that `p.derivative.nat_degree ≤ p.nat_degree`.
#### Estimated changes
modified src/data/polynomial/derivative.lean
- \+ *lemma* nat_degree_derivative_le
- \- *theorem* nat_degree_derivative_le



## [2022-03-29 09:36:10](https://github.com/leanprover-community/mathlib/commit/4bf4d9d)
feat(ring_theory/dedekind_domain/adic_valuation): add adic valuation on a Dedekind domain ([#12712](https://github.com/leanprover-community/mathlib/pull/12712))
Given a Dedekind domain R of Krull dimension 1 and a maximal ideal v of R, we define the
v-adic valuation on R and prove some of its properties, including the existence of uniformizers.
#### Estimated changes
modified src/algebra/order/monoid.lean
- \+ *lemma* le_max_iff
- \+ *lemma* min_le_iff

created src/ring_theory/dedekind_domain/adic_valuation.lean
- \+ *lemma* int_valuation_def_if_pos
- \+ *lemma* int_valuation_def_if_neg
- \+ *lemma* int_valuation_ne_zero
- \+ *lemma* int_valuation_ne_zero'
- \+ *lemma* int_valuation_zero_le
- \+ *lemma* int_valuation_le_one
- \+ *lemma* int_valuation_lt_one_iff_dvd
- \+ *lemma* int_valuation_le_pow_iff_dvd
- \+ *lemma* int_valuation.map_zero'
- \+ *lemma* int_valuation.map_one'
- \+ *lemma* int_valuation.map_mul'
- \+ *lemma* int_valuation.le_max_iff_min_le
- \+ *lemma* int_valuation.map_add_le_max'
- \+ *lemma* int_valuation_exists_uniformizer
- \+ *def* int_valuation_def
- \+ *def* int_valuation

modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* associates.le_singleton_iff
- \+ *lemma* height_one_spectrum.associates_irreducible
- \- *lemma* height_one_spectrum.associates.irreducible

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* associates.mk_ne_zero'



## [2022-03-29 09:36:08](https://github.com/leanprover-community/mathlib/commit/1ffd04c)
feat(analysis/locally_convex): add balanced hull and core ([#12537](https://github.com/leanprover-community/mathlib/pull/12537))
#### Estimated changes
created src/analysis/locally_convex/balanced_core_hull.lean
- \+ *lemma* balanced_core_subset
- \+ *lemma* balanced_core_mem_iff
- \+ *lemma* smul_balanced_core_subset
- \+ *lemma* balanced_core_balanced
- \+ *lemma* balanced.subset_core_of_subset
- \+ *lemma* balanced_core_aux_mem_iff
- \+ *lemma* balanced_hull_mem_iff
- \+ *lemma* balanced.hull_subset_of_subset
- \+ *lemma* balanced_core_nonempty_iff
- \+ *lemma* balanced_core_zero_mem
- \+ *lemma* subset_balanced_hull
- \+ *lemma* balanced_hull.balanced
- \+ *lemma* balanced_core_aux_empty
- \+ *lemma* balanced_core_aux_subset
- \+ *lemma* balanced_core_aux_balanced
- \+ *lemma* balanced_core_aux_maximal
- \+ *lemma* balanced_core_subset_balanced_core_aux
- \+ *lemma* balanced_core_eq_Inter
- \+ *def* balanced_core
- \+ *def* balanced_core_aux
- \+ *def* balanced_hull



## [2022-03-29 07:35:13](https://github.com/leanprover-community/mathlib/commit/0f92307)
feat(data/list/chain): Simp lemma for `chain r a (l ++ b :: c :: m)` ([#12969](https://github.com/leanprover-community/mathlib/pull/12969))
#### Estimated changes
modified src/data/list/chain.lean
- \+ *theorem* chain_append_cons_cons



## [2022-03-29 07:35:12](https://github.com/leanprover-community/mathlib/commit/1cdbc35)
feat(order/hom/bounded): an order_iso maps top to top and bot to bot ([#12862](https://github.com/leanprover-community/mathlib/pull/12862))
#### Estimated changes
modified src/order/hom/bounded.lean
- \+ *lemma* map_eq_top_iff
- \+ *lemma* map_eq_bot_iff



## [2022-03-29 07:35:11](https://github.com/leanprover-community/mathlib/commit/b535c2d)
feat(algebra/homology): three lemmas on homological complexes ([#12742](https://github.com/leanprover-community/mathlib/pull/12742))
#### Estimated changes
modified src/algebra/homology/additive.lean
- \+ *lemma* map_chain_complex_of

modified src/algebra/homology/differential_object.lean
- \+ *lemma* eq_to_hom_f'
- \- *lemma* eq_to_hom_f

modified src/algebra/homology/homological_complex.lean
- \+ *lemma* ext
- \+ *lemma* eq_to_hom_f



## [2022-03-29 07:35:09](https://github.com/leanprover-community/mathlib/commit/1084cee)
feat(category_theory/bicategory/coherence): prove the coherence theorem for bicategories ([#12155](https://github.com/leanprover-community/mathlib/pull/12155))
#### Estimated changes
created src/category_theory/bicategory/coherence.lean
- \+ *lemma* normalize_aux_congr
- \+ *lemma* normalize_naturality
- \+ *lemma* normalize_aux_nil_comp
- \+ *theorem* follows
- \+ *def* inclusion_path_aux
- \+ *def* inclusion_path
- \+ *def* preinclusion
- \+ *def* normalize_aux
- \+ *def* normalize_aux'
- \+ *def* normalize_iso
- \+ *def* normalize
- \+ *def* normalize_unit_iso
- \+ *def* normalize_equiv
- \+ *def* inclusion_map_comp_aux
- \+ *def* inclusion

modified src/category_theory/bicategory/free.lean
- \+/\- *lemma* id_def
- \+/\- *lemma* comp_def
- \+/\- *lemma* id_def
- \+/\- *lemma* comp_def

modified src/category_theory/bicategory/locally_discrete.lean

modified src/category_theory/eq_to_hom.lean
- \+ *lemma* dcongr_arg



## [2022-03-29 07:35:08](https://github.com/leanprover-community/mathlib/commit/7b8b8f1)
feat(set_theory/ordinal_arithmetic): Characterize principal multiplicative ordinals ([#11701](https://github.com/leanprover-community/mathlib/pull/11701))
Two lemmas were renamed in the process:
- `mul_lt_omega` → `principal_mul_omega`
- `opow_omega` → `principal_opow_omega`
Various others were moved to `principal.lean`.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* mul_two
- \+/\- *theorem* sup_opow_nat
- \- *theorem* mul_lt_omega
- \- *theorem* opow_lt_omega
- \- *theorem* mul_omega
- \- *theorem* mul_lt_omega_opow
- \- *theorem* mul_omega_dvd
- \- *theorem* mul_omega_opow_opow
- \- *theorem* opow_omega
- \+/\- *theorem* sup_opow_nat

modified src/set_theory/ordinal_notation.lean

modified src/set_theory/principal.lean
- \+ *theorem* principal_add_iff_zero_or_omega_opow
- \+ *theorem* opow_principal_add_of_principal_add
- \+ *theorem* principal_mul_one
- \+ *theorem* principal_mul_two
- \+ *theorem* principal_mul_of_le_two
- \+ *theorem* principal_add_of_principal_mul
- \+ *theorem* principal_mul_is_limit
- \+ *theorem* principal_mul_iff_mul_left_eq
- \+ *theorem* principal_mul_omega
- \+ *theorem* mul_omega
- \+ *theorem* mul_lt_omega_opow
- \+ *theorem* mul_omega_opow_opow
- \+ *theorem* principal_mul_omega_opow_opow
- \+ *theorem* principal_add_of_principal_mul_opow
- \+ *theorem* principal_mul_iff_le_two_or_omega_opow_opow
- \+ *theorem* mul_omega_dvd
- \+ *theorem* mul_eq_opow_log_succ
- \+ *theorem* principal_opow_omega
- \+ *theorem* opow_omega
- \- *theorem* principal_add_iff_zero_or_omega_power
- \- *theorem* opow_principal_add_is_principal_add



## [2022-03-29 05:57:42](https://github.com/leanprover-community/mathlib/commit/ce3cece)
feat(measure_theory/constructions/borel_space): add `borelize` tactic ([#12844](https://github.com/leanprover-community/mathlib/pull/12844))
#### Estimated changes
modified src/analysis/ODE/picard_lindelof.lean

modified src/analysis/box_integral/integrability.lean

modified src/analysis/complex/abs_max.lean

modified src/analysis/complex/liouville.lean

modified src/analysis/complex/removable_singularity.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/metric_space/hausdorff_dimension.lean



## [2022-03-29 05:57:41](https://github.com/leanprover-community/mathlib/commit/5fb7b7b)
feat(set_theory/{ordinal_arithmetic, game/nim}): Minimum excluded ordinal ([#12659](https://github.com/leanprover-community/mathlib/pull/12659))
We define `mex` and `bmex`, and use the former to golf the proof of Sprague-Grundy.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \- *theorem* mk_ordinal_out

modified src/set_theory/game/nim.lean
- \+/\- *lemma* grundy_value_nim_add_nim
- \- *lemma* nonmoves_nonempty
- \+/\- *lemma* grundy_value_nim_add_nim
- \- *def* nonmoves

modified src/set_theory/ordinal.lean
- \+ *theorem* mk_ordinal_out

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* lsub_not_mem_range
- \+ *theorem* nonempty_compl_range
- \+ *theorem* mex_not_mem_range
- \+ *theorem* ne_mex
- \+ *theorem* mex_le_of_ne
- \+ *theorem* exists_of_lt_mex
- \+ *theorem* mex_le_lsub
- \+ *theorem* mex_monotone
- \+ *theorem* mex_lt_ord_succ_mk
- \+ *theorem* bmex_not_mem_brange
- \+ *theorem* ne_bmex
- \+ *theorem* bmex_le_of_ne
- \+ *theorem* exists_of_lt_bmex
- \+ *theorem* bmex_le_blsub
- \+ *theorem* bmex_monotone
- \+ *theorem* bmex_lt_ord_succ_card
- \- *theorem* lsub_nmem_range
- \+ *def* mex
- \+ *def* bmex



## [2022-03-29 04:19:18](https://github.com/leanprover-community/mathlib/commit/5fcad21)
feat(number_theory/frobenius_number): Frobenius numbers ([#9729](https://github.com/leanprover-community/mathlib/pull/9729))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mem_closure_pair

modified src/group_theory/submonoid/membership.lean
- \+ *lemma* mem_closure_pair

created src/number_theory/frobenius_number.lean
- \+ *lemma* nat.coprime.mul_add_mul_ne_mul
- \+ *theorem* is_frobenius_number_pair
- \+ *def* is_frobenius_number



## [2022-03-28 23:54:09](https://github.com/leanprover-community/mathlib/commit/7fea719)
feat(data/set/basic): Laws for n-ary image ([#13011](https://github.com/leanprover-community/mathlib/pull/13011))
Prove left/right commutativity, distributivity of `set.image2` in the style of `set.image2_assoc`. Also add `forall₃_imp` and `Exists₃.imp`.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *lemma* nonempty.image2
- \+ *lemma* image2_nonempty_iff
- \+ *lemma* image2_eq_empty_iff
- \+ *lemma* image3_mono
- \+/\- *lemma* image2_assoc
- \+ *lemma* image2_comm
- \+ *lemma* image2_left_comm
- \+ *lemma* image2_right_comm
- \+ *lemma* image_image2_distrib
- \+ *lemma* image_image2_distrib_left
- \+ *lemma* image_image2_distrib_right
- \+/\- *lemma* image2_assoc
- \+/\- *lemma* nonempty.image2

modified src/logic/basic.lean
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* forall_imp
- \+/\- *lemma* forall₂_imp
- \+ *lemma* forall₃_imp
- \+/\- *lemma* Exists.imp
- \+/\- *lemma* Exists₂.imp
- \+ *lemma* Exists₃.imp
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* forall_imp
- \+/\- *lemma* forall₂_imp
- \+/\- *lemma* Exists.imp
- \+/\- *lemma* Exists₂.imp



## [2022-03-28 23:54:08](https://github.com/leanprover-community/mathlib/commit/9480029)
chore(data/{nat,int,rat}/cast): add bundled version of `cast_id` lemmas ([#13001](https://github.com/leanprover-community/mathlib/pull/13001))
#### Estimated changes
modified src/data/int/cast.lean
- \+ *lemma* int.cast_add_hom_int
- \+ *lemma* int.cast_ring_hom_int

modified src/data/nat/cast.lean
- \+ *lemma* eq_nat_cast'
- \+ *lemma* nat.cast_ring_hom_nat

modified src/data/rat/cast.lean
- \+ *lemma* cast_hom_rat



## [2022-03-28 23:54:07](https://github.com/leanprover-community/mathlib/commit/8c9dee1)
feat(algebra/field_power): add min_le_of_zpow_le_max ([#12915](https://github.com/leanprover-community/mathlib/pull/12915))
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* min_le_of_zpow_le_max



## [2022-03-28 22:26:18](https://github.com/leanprover-community/mathlib/commit/223d9a1)
feat(group_theory/quotient_group): maps of quotients by powers of integers induced by group homomorphisms ([#12811](https://github.com/leanprover-community/mathlib/pull/12811))
#### Estimated changes
modified src/group_theory/quotient_group.lean
- \+ *lemma* hom_quotient_zpow_of_hom_right_inverse
- \+ *def* hom_quotient_zpow_of_hom
- \+ *def* equiv_quotient_zpow_of_equiv



## [2022-03-28 22:26:16](https://github.com/leanprover-community/mathlib/commit/1a2182c)
feat(group_theory/complement): Transversals as functions ([#12732](https://github.com/leanprover-community/mathlib/pull/12732))
This PR adds interpretations of transversals as functions mapping elements of `G` to the chosen coset representative.
#### Estimated changes
modified src/group_theory/complement.lean
- \+ *lemma* mk'_to_equiv
- \+ *lemma* inv_to_fun_mul_mem
- \+ *lemma* inv_mul_to_fun_mem
- \+ *lemma* mk'_to_equiv
- \+ *lemma* mul_inv_to_fun_mem
- \+ *lemma* to_fun_mul_inv_mem



## [2022-03-28 20:38:27](https://github.com/leanprover-community/mathlib/commit/40b142e)
chore(analysis/*): move matrix definitions into their own file and generalize ([#13007](https://github.com/leanprover-community/mathlib/pull/13007))
This makes it much easier to relax the typeclasses as needed.
`norm_matrix_le_iff` has been renamed to `matrix.norm_le_iff`, the rest of the lemmas have just had their typeclass arguments weakened. No proofs have changed.
The `matrix.normed_space` instance is now of the form `normed_space R (matrix n m α)` instead of `normed_space α (matrix n m α)`.
#### Estimated changes
created src/analysis/matrix.lean
- \+ *lemma* norm_le_iff
- \+ *lemma* norm_lt_iff
- \+ *lemma* norm_entry_le_entrywise_sup_norm

modified src/analysis/normed/normed_field.lean
- \- *lemma* norm_matrix_le_iff
- \- *lemma* norm_matrix_lt_iff
- \- *def* matrix.semi_normed_group
- \- *def* matrix.normed_group

modified src/analysis/normed_space/basic.lean
- \- *lemma* matrix.norm_entry_le_entrywise_sup_norm
- \- *def* matrix.normed_space

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/star/basic.lean
- \- *lemma* matrix.entrywise_sup_norm_star_eq_norm

modified src/analysis/normed_space/star/matrix.lean
- \+ *lemma* entrywise_sup_norm_star_eq_norm

modified src/number_theory/modular.lean



## [2022-03-28 20:38:26](https://github.com/leanprover-community/mathlib/commit/ea97ca6)
feat(group_theory/group_action): add `commute.smul_{left,right}[_iff]` lemmas ([#13003](https://github.com/leanprover-community/mathlib/pull/13003))
`(r • a) * b = b * (r • a)` follows trivially from `smul_mul_assoc` and `mul_smul_comm`
#### Estimated changes
modified src/group_theory/group_action/defs.lean
- \+ *lemma* commute.smul_right
- \+ *lemma* commute.smul_left

modified src/group_theory/group_action/group.lean
- \+ *lemma* commute.smul_right_iff
- \+ *lemma* commute.smul_left_iff
- \+ *lemma* commute.smul_right_iff₀
- \+ *lemma* commute.smul_left_iff₀



## [2022-03-28 20:38:25](https://github.com/leanprover-community/mathlib/commit/261a195)
feat(group_theory/group_action/opposite): Add `smul_eq_mul_unop` ([#12995](https://github.com/leanprover-community/mathlib/pull/12995))
This PR adds a simp-lemma `smul_eq_mul_unop`, similar to `op_smul_eq_mul` and `smul_eq_mul`.
#### Estimated changes
modified src/group_theory/group_action/opposite.lean
- \+/\- *lemma* op_smul_eq_mul
- \+ *lemma* mul_opposite.smul_eq_mul_unop
- \+/\- *lemma* op_smul_eq_mul



## [2022-03-28 16:49:23](https://github.com/leanprover-community/mathlib/commit/6fe0c3b)
refactor(algebra/group/to_additive + files containing even/odd): move many lemmas involving even/odd to the same file ([#12882](https://github.com/leanprover-community/mathlib/pull/12882))
This is the first step in refactoring the definition of `even` to be the `to_additive` of `square`.
This PR simply gathers together many (though not all) lemmas that involve `even` or `odd` in their assumptions.  The choice of which lemmas to migrate to the file `algebra.parity` was dictated mostly by whether importing `algebra.parity` in the current home would create a cyclic import.
The only change that is not a simple shift from a file to another one is the addition in `to_additive` for support to change `square` in a multiplicative name to `even` in an additive name.
The change to the test file `test.ring` is due to the fact that the definition of `odd` was no longer imported by the file.
#### Estimated changes
modified src/algebra/field_power.lean
- \- *lemma* even.zpow_neg
- \- *lemma* even.zpow_nonneg
- \- *lemma* even.zpow_abs
- \- *lemma* zpow_bit0_abs
- \- *lemma* even.abs_zpow
- \- *lemma* abs_zpow_bit0
- \- *theorem* even.zpow_pos
- \- *theorem* odd.zpow_nonneg
- \- *theorem* odd.zpow_pos
- \- *theorem* odd.zpow_nonpos
- \- *theorem* odd.zpow_neg

modified src/algebra/group/to_additive.lean

modified src/algebra/group_power/lemmas.lean
- \- *lemma* even.pow_nonneg
- \- *lemma* even.pow_pos
- \- *lemma* odd.pow_nonpos
- \- *lemma* odd.pow_neg
- \- *lemma* odd.pow_nonneg_iff
- \- *lemma* odd.pow_nonpos_iff
- \- *lemma* odd.pow_pos_iff
- \- *lemma* odd.pow_neg_iff
- \- *lemma* even.pow_pos_iff
- \- *lemma* even.pow_abs
- \- *lemma* pow_bit0_abs
- \- *lemma* odd.strict_mono_pow

modified src/algebra/order/ring.lean
- \- *lemma* even_abs
- \- *lemma* odd_abs

modified src/algebra/parity.lean
- \+/\- *lemma* even_zero
- \+/\- *lemma* even_two_mul
- \+/\- *lemma* add_monoid_hom.even
- \+ *lemma* even_iff_two_dvd
- \+ *lemma* range_two_mul
- \+ *lemma* even_bit0
- \+/\- *lemma* even_two
- \+/\- *lemma* even.mul_right
- \+/\- *lemma* even.mul_left
- \+/\- *lemma* even.pow_of_ne_zero
- \+ *lemma* odd_bit1
- \+ *lemma* range_two_mul_add_one
- \+ *lemma* odd.neg
- \+ *lemma* odd_neg
- \+/\- *lemma* odd_neg_one
- \+ *lemma* even_abs
- \+ *lemma* odd_abs
- \+ *lemma* even.pow_nonneg
- \+ *lemma* even.pow_pos
- \+ *lemma* odd.pow_nonpos
- \+ *lemma* odd.pow_neg
- \+ *lemma* odd.pow_nonneg_iff
- \+ *lemma* odd.pow_nonpos_iff
- \+ *lemma* odd.pow_pos_iff
- \+ *lemma* odd.pow_neg_iff
- \+ *lemma* even.pow_pos_iff
- \+ *lemma* even.pow_abs
- \+ *lemma* pow_bit0_abs
- \+ *lemma* odd.strict_mono_pow
- \+ *lemma* fintype.card_fin_even
- \+ *lemma* even.zpow_neg
- \+ *lemma* even.zpow_nonneg
- \+ *lemma* even.zpow_abs
- \+ *lemma* zpow_bit0_abs
- \+ *lemma* even.abs_zpow
- \+ *lemma* abs_zpow_bit0
- \+/\- *lemma* even_zero
- \+/\- *lemma* even_two
- \+/\- *lemma* even_two_mul
- \+/\- *lemma* add_monoid_hom.even
- \+/\- *lemma* even.mul_right
- \+/\- *lemma* even.mul_left
- \+/\- *lemma* even.pow_of_ne_zero
- \+/\- *lemma* odd_neg_one
- \+ *theorem* even_neg
- \+ *theorem* even.zpow_pos
- \+ *theorem* odd.zpow_nonneg
- \+ *theorem* odd.zpow_pos
- \+ *theorem* odd.zpow_nonpos
- \+ *theorem* odd.zpow_neg
- \+ *def* even
- \+ *def* odd

modified src/algebra/ring/basic.lean
- \- *lemma* even_iff_two_dvd
- \- *lemma* range_two_mul
- \- *lemma* even_bit0
- \- *lemma* odd_bit1
- \- *lemma* range_two_mul_add_one
- \- *lemma* odd.neg
- \- *lemma* odd_neg
- \- *theorem* even_neg
- \- *def* even
- \- *def* odd

modified src/data/fintype/basic.lean
- \- *lemma* fintype.card_fin_even

modified src/data/nat/prime.lean

modified test/ring.lean



## [2022-03-28 16:49:22](https://github.com/leanprover-community/mathlib/commit/958f6b0)
refactor(measure_theory/group/fundamental_domain): allow `null_measurable_set`s ([#12005](https://github.com/leanprover-community/mathlib/pull/12005))
#### Estimated changes
modified src/measure_theory/group/fundamental_domain.lean
- \+/\- *lemma* mk'
- \+/\- *lemma* null_measurable_set_smul
- \+ *lemma* restrict_restrict
- \+/\- *lemma* pairwise_ae_disjoint_of_ac
- \+ *lemma* preimage_of_equiv
- \+ *lemma* image_of_equiv
- \+ *lemma* smul
- \+ *lemma* smul_of_comm
- \+ *lemma* sum_restrict
- \+ *lemma* lintegral_eq_tsum
- \+/\- *lemma* mk'
- \- *lemma* measurable_set_smul
- \+/\- *lemma* null_measurable_set_smul
- \+/\- *lemma* pairwise_ae_disjoint_of_ac

modified src/measure_theory/integral/periodic.lean

modified src/measure_theory/measure/haar_quotient.lean
- \- *lemma* measure_theory.is_fundamental_domain.smul



## [2022-03-28 15:03:16](https://github.com/leanprover-community/mathlib/commit/abaabc8)
chore(algebra/group_power/lemmas): turn `[zn]smul` lemmas into instances ([#13002](https://github.com/leanprover-community/mathlib/pull/13002))
This adds new instances such that:
* `mul_[zn]smul_assoc` is `←smul_mul_assoc`
* `mul_[zn]smul_left` is `←mul_smul_comm`
This also makes `noncomm_ring` slightly smarter, and able to handle scalar actions by `nat`.
Thanks to Christopher, this generalizes these instances to non-associative and non-unital rings.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \- *theorem* mul_nsmul_left
- \- *theorem* mul_nsmul_assoc
- \- *theorem* mul_zsmul_left
- \- *theorem* mul_zsmul_assoc

modified src/tactic/noncomm_ring.lean

modified test/noncomm_ring.lean



## [2022-03-28 15:03:14](https://github.com/leanprover-community/mathlib/commit/0e1387b)
feat(category_theory): the category of small categories has all small limits ([#12979](https://github.com/leanprover-community/mathlib/pull/12979))
#### Estimated changes
modified src/category_theory/category/Cat.lean
- \+ *lemma* id_map
- \+ *lemma* comp_obj
- \+ *lemma* comp_map

created src/category_theory/category/Cat/limit.lean
- \+ *lemma* limit_π_hom_diagram_eq_to_hom
- \+ *def* hom_diagram
- \+ *def* limit_cone_X
- \+ *def* limit_cone
- \+ *def* limit_cone_lift
- \+ *def* limit_cone_is_limit

modified src/category_theory/grothendieck.lean



## [2022-03-28 15:03:13](https://github.com/leanprover-community/mathlib/commit/31e5ae2)
feat(data/list/cycle): Define the empty cycle ([#12967](https://github.com/leanprover-community/mathlib/pull/12967))
Also clean the file up somewhat, and add various `simp` lemmas.
#### Estimated changes
modified src/data/list/cycle.lean
- \+/\- *lemma* mk_eq_coe
- \+/\- *lemma* mk'_eq_coe
- \+ *lemma* coe_nil
- \+ *lemma* coe_eq_nil
- \+ *lemma* empty_eq
- \+ *lemma* induction_on
- \+/\- *lemma* mem_coe_iff
- \+ *lemma* not_mem_nil
- \+/\- *lemma* reverse_coe
- \+/\- *lemma* mem_reverse_iff
- \+/\- *lemma* reverse_reverse
- \+ *lemma* reverse_nil
- \+/\- *lemma* length_coe
- \+ *lemma* length_nil
- \+/\- *lemma* length_reverse
- \+ *lemma* subsingleton_nil
- \+/\- *lemma* length_subsingleton_iff
- \+/\- *lemma* subsingleton_reverse_iff
- \+/\- *lemma* nontrivial_reverse_iff
- \+/\- *lemma* length_nontrivial
- \+ *lemma* nodup_nil
- \+/\- *lemma* nodup_coe_iff
- \+/\- *lemma* nodup_reverse_iff
- \+/\- *lemma* subsingleton.nodup
- \+/\- *lemma* nodup.nontrivial_iff
- \+ *lemma* coe_to_multiset
- \+ *lemma* nil_to_multiset
- \+ *lemma* map_nil
- \+ *lemma* map_coe
- \+ *lemma* map_eq_nil
- \+ *lemma* lists_coe
- \+/\- *lemma* mem_lists_iff_coe_eq
- \+ *lemma* lists_nil
- \+ *lemma* nil_to_finset
- \+/\- *lemma* next_mem
- \+/\- *lemma* prev_mem
- \+/\- *lemma* mk_eq_coe
- \+/\- *lemma* mk'_eq_coe
- \+/\- *lemma* mem_coe_iff
- \+/\- *lemma* reverse_coe
- \+/\- *lemma* mem_reverse_iff
- \+/\- *lemma* reverse_reverse
- \+/\- *lemma* length_coe
- \+/\- *lemma* length_reverse
- \+/\- *lemma* length_subsingleton_iff
- \+/\- *lemma* subsingleton_reverse_iff
- \+/\- *lemma* nontrivial_reverse_iff
- \+/\- *lemma* length_nontrivial
- \+/\- *lemma* nodup_coe_iff
- \+/\- *lemma* nodup_reverse_iff
- \+/\- *lemma* subsingleton.nodup
- \+/\- *lemma* nodup.nontrivial_iff
- \+/\- *lemma* mem_lists_iff_coe_eq
- \+/\- *lemma* next_mem
- \+/\- *lemma* prev_mem
- \+ *def* nil



## [2022-03-28 14:30:41](https://github.com/leanprover-community/mathlib/commit/0c6f0c2)
feat(ring_theory/dedekind_domain/ideal): add lemmas about sup of ideal with irreducible ([#12859](https://github.com/leanprover-community/mathlib/pull/12859))
These results were originally in [#9345](https://github.com/leanprover-community/mathlib/pull/9345).
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean
- \+/\- *lemma* prod_normalized_factors_eq_self
- \+ *lemma* irreducible_pow_sup
- \+ *lemma* irreducible_pow_sup_of_le
- \+ *lemma* irreducible_pow_sup_of_ge
- \+/\- *lemma* prod_normalized_factors_eq_self



## [2022-03-28 11:39:00](https://github.com/leanprover-community/mathlib/commit/4ee988d)
chore(algebra/homology/homotopy): cleanup ([#12998](https://github.com/leanprover-community/mathlib/pull/12998))
Correcting a name and some whitespace.
#### Estimated changes
modified src/algebra/homology/homotopy.lean
- \+ *lemma* prev_d_comp_right
- \- *lemma* to_prev'_comp_right
- \+/\- *def* add
- \+/\- *def* add



## [2022-03-28 11:38:59](https://github.com/leanprover-community/mathlib/commit/eba31b5)
feat(algebra/homology): some elementwise lemmas ([#12997](https://github.com/leanprover-community/mathlib/pull/12997))
#### Estimated changes
modified src/algebra/homology/homological_complex.lean

modified src/algebra/homology/image_to_kernel.lean

modified src/category_theory/concrete_category/elementwise.lean

modified src/category_theory/subobject/basic.lean

modified src/category_theory/subobject/limits.lean



## [2022-03-28 11:38:58](https://github.com/leanprover-community/mathlib/commit/dacf049)
feat(algebra/*): coe_to_equiv_symm simp lemmas ([#12996](https://github.com/leanprover-community/mathlib/pull/12996))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* to_equiv_eq_coe

modified src/algebra/hom/equiv.lean
- \+ *lemma* to_equiv_eq_coe
- \+/\- *lemma* coe_to_equiv
- \+/\- *lemma* coe_to_equiv

modified src/algebra/module/equiv.lean
- \+ *lemma* coe_to_equiv_symm

modified src/group_theory/commensurable.lean



## [2022-03-28 11:38:57](https://github.com/leanprover-community/mathlib/commit/f0c15be)
feat(measure_theory/functions/strongly_measurable): almost everywhere strongly measurable functions ([#12985](https://github.com/leanprover-community/mathlib/pull/12985))
A function is almost everywhere strongly measurable if it is almost everywhere the pointwise limit of a sequence of simple functions. These are the functions that can be integrated in the most general version of the Bochner integral. As a prerequisite for the refactor of the Bochner integral, we define almost strongly measurable functions and build a comprehensive API for them, gathering in the file `strongly_measurable.lean` all facts that will be needed for the refactor. The API does not claim to be complete, but it is already pretty big.
#### Estimated changes
modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* strongly_measurable.ae_strongly_measurable
- \+/\- *lemma* subsingleton.strongly_measurable
- \+ *lemma* strongly_measurable_of_is_empty
- \+ *lemma* strongly_measurable_one
- \+ *lemma* strongly_measurable_const'
- \+ *lemma* subsingleton.strongly_measurable'
- \+ *lemma* _root_.continuous.comp_strongly_measurable
- \+ *lemma* measurable_set_mul_support
- \+ *lemma* comp_measurable
- \+ *lemma* of_uncurry_left
- \+ *lemma* of_uncurry_right
- \+ *lemma* mul_const
- \+ *lemma* const_mul
- \+ *lemma* _root_.strongly_measurable_const_smul_iff
- \+ *lemma* _root_.strongly_measurable_const_smul_iff₀
- \+ *lemma* _root_.list.strongly_measurable_prod'
- \+ *lemma* _root_.list.strongly_measurable_prod
- \+ *lemma* _root_.multiset.strongly_measurable_prod'
- \+ *lemma* _root_.multiset.strongly_measurable_prod
- \+ *lemma* _root_.finset.strongly_measurable_prod'
- \+ *lemma* _root_.finset.strongly_measurable_prod
- \+ *lemma* is_separable_range
- \+ *lemma* separable_space_range_union_singleton
- \+/\- *lemma* _root_.measurable.strongly_measurable
- \+ *lemma* _root_.strongly_measurable_iff_measurable
- \+ *lemma* _root_.strongly_measurable_id
- \+ *lemma* _root_.continuous.strongly_measurable
- \+ *lemma* _root_.embedding.comp_strongly_measurable_iff
- \+ *lemma* _root_.strongly_measurable_of_tendsto
- \+ *lemma* _root_.strongly_measurable_of_strongly_measurable_union_cover
- \+ *lemma* _root_.strongly_measurable_of_restrict_of_restrict_compl
- \+ *lemma* _root_.measurable_embedding.strongly_measurable_extend
- \+ *lemma* _root_.measurable_embedding.exists_strongly_measurable_extend
- \+ *lemma* measurable_set_eq_fun
- \+ *lemma* measurable_set_lt
- \+ *lemma* measurable_set_le
- \+ *lemma* ae_strongly_measurable_const
- \+ *lemma* ae_strongly_measurable_one
- \+ *lemma* subsingleton.ae_strongly_measurable
- \+ *lemma* subsingleton.ae_strongly_measurable'
- \+ *lemma* ae_measurable_zero_measure
- \+ *lemma* simple_func.ae_strongly_measurable
- \+ *lemma* strongly_measurable_mk
- \+ *lemma* measurable_mk
- \+ *lemma* ae_eq_mk
- \+ *lemma* congr
- \+ *lemma* _root_.ae_strongly_measurable_congr
- \+ *lemma* mono_measure
- \+ *lemma* mono_set
- \+ *lemma* ae_mem_imp_eq_mk
- \+ *lemma* _root_.continuous.comp_ae_strongly_measurable
- \+ *lemma* _root_.continuous.ae_strongly_measurable
- \+ *lemma* _root_.measurable.ae_strongly_measurable
- \+ *lemma* _root_.list.ae_strongly_measurable_prod'
- \+ *lemma* _root_.list.ae_strongly_measurable_prod
- \+ *lemma* _root_.multiset.ae_strongly_measurable_prod'
- \+ *lemma* _root_.multiset.ae_strongly_measurable_prod
- \+ *lemma* _root_.finset.ae_strongly_measurable_prod'
- \+ *lemma* _root_.finset.ae_strongly_measurable_prod
- \+ *lemma* _root_.ae_measurable.ae_strongly_measurable
- \+ *lemma* _root_.ae_strongly_measurable_id
- \+ *lemma* _root_.ae_strongly_measurable_iff_ae_measurable
- \+ *lemma* _root_.ae_strongly_measurable_indicator_iff
- \+ *lemma* _root_.ae_strongly_measurable_of_ae_strongly_measurable_trim
- \+ *lemma* comp_measurable
- \+ *lemma* is_separable_ae_range
- \+ *lemma* _root_.measurable_embedding.ae_strongly_measurable_map_iff
- \+ *lemma* _root_.embedding.ae_strongly_measurable_comp_iff
- \+ *lemma* _root_.measure_theory.measure_preserving.ae_strongly_measurable_comp_iff
- \+ *lemma* _root_.ae_strongly_measurable_of_tendsto_ae
- \+ *lemma* _root_.exists_strongly_measurable_limit_of_tendsto_ae
- \+ *lemma* sum_measure
- \+ *lemma* _root_.ae_strongly_measurable_sum_measure_iff
- \+ *lemma* _root_.ae_strongly_measurable_add_measure_iff
- \+ *lemma* add_measure
- \+ *lemma* _root_.ae_strongly_measurable_Union_iff
- \+ *lemma* _root_.ae_strongly_measurable_union_iff
- \+ *lemma* smul_measure
- \+ *lemma* _root_.ae_strongly_measurable_smul_const_iff
- \+ *lemma* _root_.ae_strongly_measurable_const_smul_iff
- \+ *lemma* _root_.ae_strongly_measurable_const_smul_iff₀
- \+ *lemma* _root_.strongly_measurable.apply_continuous_linear_map
- \+ *lemma* apply_continuous_linear_map
- \+ *lemma* _root_.ae_strongly_measurable_with_density_iff
- \+/\- *lemma* measurable_uncurry_of_continuous_of_measurable
- \+ *lemma* strongly_measurable_uncurry_of_continuous_of_strongly_measurable
- \+/\- *lemma* subsingleton.strongly_measurable
- \+/\- *lemma* _root_.measurable.strongly_measurable
- \- *lemma* strongly_measurable_id
- \- *lemma* strongly_measurable_iff_measurable
- \+/\- *lemma* measurable_uncurry_of_continuous_of_measurable
- \+ *theorem* _root_.strongly_measurable_iff_measurable_separable
- \+ *theorem* _root_.ae_strongly_measurable_iff_ae_measurable_separable
- \+ *def* ae_strongly_measurable

modified src/probability/stopping.lean
- \+/\- *theorem* adapted.prog_measurable_of_continuous
- \+/\- *theorem* adapted.prog_measurable_of_continuous



## [2022-03-28 11:38:56](https://github.com/leanprover-community/mathlib/commit/fd2c6c4)
chore(data/polynomial/ring_division): remove nontrivial assumptions ([#12984](https://github.com/leanprover-community/mathlib/pull/12984))
Additionally, this removes:
* some `polynomial.monic` assumptions that can be handled by casing instead
* the explicit `R` argument from `is_field.to_field R hR`
#### Estimated changes
modified src/algebra/field/basic.lean
- \+ *lemma* is_field.nontrivial
- \+ *lemma* not_is_field_of_subsingleton

modified src/algebraic_geometry/prime_spectrum/basic.lean

modified src/data/polynomial/basic.lean
- \+ *lemma* nontrivial_iff

modified src/data/polynomial/div.lean
- \+/\- *lemma* sum_mod_by_monic_coeff
- \+/\- *lemma* not_is_field
- \+/\- *lemma* sum_mod_by_monic_coeff
- \+/\- *lemma* not_is_field

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* mod_by_monic_eq_of_dvd_sub
- \+/\- *lemma* add_mod_by_monic
- \+/\- *lemma* smul_mod_by_monic
- \+/\- *lemma* mod_by_monic_eq_of_dvd_sub
- \+/\- *lemma* add_mod_by_monic
- \+/\- *lemma* smul_mod_by_monic
- \+/\- *def* mod_by_monic_hom
- \+/\- *def* mod_by_monic_hom

modified src/field_theory/cardinality.lean

modified src/field_theory/is_alg_closed/basic.lean

modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* mod_by_monic_hom_mk
- \+/\- *lemma* mk_left_inverse
- \+/\- *lemma* mk_surjective
- \+/\- *lemma* mod_by_monic_hom_mk
- \+/\- *lemma* mk_left_inverse
- \+/\- *lemma* mk_surjective
- \+/\- *def* mod_by_monic_hom
- \+/\- *def* power_basis_aux'
- \+/\- *def* power_basis'
- \+/\- *def* mod_by_monic_hom
- \+/\- *def* power_basis_aux'
- \+/\- *def* power_basis'

modified src/ring_theory/dedekind_domain/ideal.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization/basic.lean

modified src/ring_theory/polynomial/basic.lean
- \+/\- *lemma* mem_ker_mod_by_monic
- \+/\- *lemma* ker_mod_by_monic_hom
- \+/\- *lemma* mem_ker_mod_by_monic
- \+/\- *lemma* ker_mod_by_monic_hom

modified src/ring_theory/principal_ideal_domain.lean



## [2022-03-28 11:38:55](https://github.com/leanprover-community/mathlib/commit/c0421e7)
feat({ring_theory,group_theory}/localization): add some small lemmas for localisation API ([#12861](https://github.com/leanprover-community/mathlib/pull/12861))
Add the following:
* `sub_mk`: a/b - c/d = (ad - bc)/(bd)
* `mk_pow`: (a/b)^n = a^n/b^n
* `mk_int_cast`, `mk_nat_cast`: m = m/1 for integer/natural number m.
#### Estimated changes
modified src/group_theory/monoid_localization.lean
- \+ *lemma* mk_pow

modified src/ring_theory/localization/basic.lean
- \+ *lemma* sub_mk
- \+ *lemma* mk_algebra_map
- \+ *lemma* mk_int_cast
- \+ *lemma* mk_nat_cast



## [2022-03-28 11:38:54](https://github.com/leanprover-community/mathlib/commit/1ebb206)
feat(ring_theory/localization): lemmas about `Frac(R)`-spans ([#12425](https://github.com/leanprover-community/mathlib/pull/12425))
A couple of lemmas relating spans in the localization of `R` to spans in `R` itself.
#### Estimated changes
modified src/algebra/algebra/tower.lean
- \+ *lemma* span_algebra_map_image
- \+ *lemma* span_algebra_map_image_of_tower
- \+ *lemma* map_mem_span_algebra_map_image

modified src/ring_theory/localization/integral.lean
- \+ *lemma* ideal_span_singleton_map_subset

modified src/ring_theory/localization/submodule.lean
- \+ *lemma* mem_span_iff
- \+ *lemma* mem_span_map



## [2022-03-28 09:53:37](https://github.com/leanprover-community/mathlib/commit/e48f2e8)
doc(data/polynomial/field_division): fix broken docstring links ([#12981](https://github.com/leanprover-community/mathlib/pull/12981))
#### Estimated changes
modified src/data/polynomial/field_division.lean



## [2022-03-28 09:53:36](https://github.com/leanprover-community/mathlib/commit/d31410a)
doc({linear_algebra,matrix}/charpoly): add crosslinks ([#12980](https://github.com/leanprover-community/mathlib/pull/12980))
This way someone coming from `undergrad.yaml` has an easy way to jump between the two statements.
#### Estimated changes
modified src/linear_algebra/charpoly/basic.lean

modified src/linear_algebra/matrix/charpoly/basic.lean



## [2022-03-28 09:53:35](https://github.com/leanprover-community/mathlib/commit/597cbf1)
feat(topology/continuous_on): add `set.maps_to.closure_of_continuous_on` ([#12975](https://github.com/leanprover-community/mathlib/pull/12975))
#### Estimated changes
modified src/topology/continuous_on.lean
- \+ *lemma* set.maps_to.closure_of_continuous_within_at
- \+ *lemma* set.maps_to.closure_of_continuous_on



## [2022-03-28 09:53:34](https://github.com/leanprover-community/mathlib/commit/ff72aa2)
feat(data/list/big_operators): add multiplicative versions ([#12966](https://github.com/leanprover-community/mathlib/pull/12966))
* add `list.length_pos_of_one_lt_prod`, generate
  `list.length_pos_of_sum_pos` using `to_additive`;
* add `list.length_pos_of_prod_lt_one` and its additive version.
#### Estimated changes
modified src/data/list/big_operators.lean
- \+ *lemma* length_pos_of_one_lt_prod
- \+ *lemma* length_pos_of_prod_lt_one
- \- *lemma* length_pos_of_sum_pos



## [2022-03-28 09:53:33](https://github.com/leanprover-community/mathlib/commit/443c239)
feat(data/polynomial/ring_division): `mem_root_set_iff` ([#12963](https://github.com/leanprover-community/mathlib/pull/12963))
#### Estimated changes
modified src/data/polynomial/ring_division.lean
- \+ *theorem* mem_root_set_iff'
- \+ *theorem* mem_root_set_iff



## [2022-03-28 09:53:31](https://github.com/leanprover-community/mathlib/commit/162d83f)
chore(data/matrix/basic): square matrices over a non-unital ring form a non-unital ring ([#12913](https://github.com/leanprover-community/mathlib/pull/12913))
#### Estimated changes
modified src/data/matrix/basic.lean
- \+/\- *lemma* conj_transpose_neg
- \+/\- *lemma* conj_transpose_neg



## [2022-03-28 09:53:30](https://github.com/leanprover-community/mathlib/commit/c030dd2)
feat(set_theory/cardinal): `cardinal.to_nat` is order-preserving on finite cardinals ([#12763](https://github.com/leanprover-community/mathlib/pull/12763))
This PR proves that `cardinal.to_nat` is order-preserving on finite cardinals.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *lemma* to_nat_le_iff_le_of_lt_omega
- \+ *lemma* to_nat_lt_iff_lt_of_lt_omega
- \+ *lemma* to_nat_le_of_le_of_lt_omega
- \+ *lemma* to_nat_lt_of_lt_of_lt_omega



## [2022-03-28 09:53:29](https://github.com/leanprover-community/mathlib/commit/2873b7a)
feat(set_theory/cofinality): Lemmas relating `cof` to `lsub` and `blsub` ([#12316](https://github.com/leanprover-community/mathlib/pull/12316))
#### Estimated changes
modified src/set_theory/cofinality.lean
- \+ *theorem* ord_cof_le
- \+ *theorem* exists_lsub_cof
- \+ *theorem* cof_lsub_le
- \+ *theorem* le_cof_iff_lsub
- \+ *theorem* exists_blsub_cof
- \+ *theorem* cof_blsub_le
- \+ *theorem* le_cof_iff_blsub



## [2022-03-28 09:53:28](https://github.com/leanprover-community/mathlib/commit/b7d6b3a)
feat(topology/continuous/algebra) : giving `C(α, M)` a `has_continuous_mul` and a `has_continuous_smul` structure ([#11261](https://github.com/leanprover-community/mathlib/pull/11261))
Here, `α` is a locally compact space.
#### Estimated changes
modified src/topology/continuous_function/algebra.lean



## [2022-03-28 08:03:19](https://github.com/leanprover-community/mathlib/commit/7711012)
feat(order/hom/*): equivalences mapping morphisms to their dual ([#12888](https://github.com/leanprover-community/mathlib/pull/12888))
Add missing `whatever_hom.dual` equivalences.
#### Estimated changes
modified src/order/hom/basic.lean
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp

modified src/order/hom/bounded.lean
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp

modified src/order/hom/complete_lattice.lean
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp

modified src/order/hom/lattice.lean
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *lemma* dual_id
- \+ *lemma* dual_comp
- \+ *lemma* symm_dual_id
- \+ *lemma* symm_dual_comp
- \+ *def* dual



## [2022-03-28 06:13:19](https://github.com/leanprover-community/mathlib/commit/587af99)
chore(test/matrix): clean up an unused argument ([#12986](https://github.com/leanprover-community/mathlib/pull/12986))
these aren't caught by linters as examples don't generate declarations
#### Estimated changes
modified test/matrix.lean



## [2022-03-28 06:13:17](https://github.com/leanprover-community/mathlib/commit/562bbf5)
feat(measure_theory/measure): add some simp lemmas, golf ([#12974](https://github.com/leanprover-community/mathlib/pull/12974))
* add `top_add`, `add_top`, `sub_top`, `zero_sub`, `sub_self`;
* golf the proof of `restrict_sub_eq_restrict_sub_restrict`.
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* top_add
- \+ *lemma* add_top

modified src/measure_theory/measure/sub.lean
- \+ *lemma* sub_le_of_le_add
- \+/\- *lemma* sub_le
- \+ *lemma* sub_top
- \+ *lemma* zero_sub
- \+ *lemma* sub_self
- \+/\- *lemma* sub_le



## [2022-03-28 06:13:16](https://github.com/leanprover-community/mathlib/commit/4b05a42)
feat(data/list/pairwise): `pairwise_of_forall_mem_list` ([#12968](https://github.com/leanprover-community/mathlib/pull/12968))
A relation holds pairwise on a list when it does on any two of its elements.
#### Estimated changes
modified src/data/list/pairwise.lean
- \+ *lemma* pairwise_of_forall_mem_list
- \+/\- *lemma* pairwise_of_reflexive_of_forall_ne
- \+/\- *lemma* pairwise_of_reflexive_of_forall_ne



## [2022-03-28 06:13:15](https://github.com/leanprover-community/mathlib/commit/73a9c27)
chore(analysis/analytic/basic): golf ([#12965](https://github.com/leanprover-community/mathlib/pull/12965))
Golf a 1-line proof, drop an unneeded assumption.
#### Estimated changes
modified src/analysis/analytic/basic.lean
- \+/\- *lemma* has_fpower_series_on_ball.sum
- \+/\- *lemma* has_fpower_series_on_ball.sum



## [2022-03-28 06:13:14](https://github.com/leanprover-community/mathlib/commit/33afea8)
feat(analysis/normed_space): generalize some lemmas ([#12959](https://github.com/leanprover-community/mathlib/pull/12959))
* add `metric.closed_ball_zero'`, a version of `metric.closed_ball_zero` for a pseudo metric space;
* merge `metric.closed_ball_inf_dist_compl_subset_closure'` with `metric.closed_ball_inf_dist_compl_subset_closure`, drop an unneeded assumption `s ≠ univ`;
* assume `r ≠ 0` instead of `0 < r` in `closure_ball`, `frontier_ball`, and `euclidean.closure_ball`.
#### Estimated changes
modified src/analysis/calculus/specific_functions.lean

modified src/analysis/complex/abs_max.lean

modified src/analysis/inner_product_space/euclidean_dist.lean
- \+/\- *lemma* closure_ball
- \+/\- *lemma* closure_ball

modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* closure_ball
- \+/\- *theorem* frontier_ball
- \+/\- *theorem* closure_ball
- \+/\- *theorem* frontier_ball

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/riesz_lemma.lean
- \+/\- *lemma* metric.closed_ball_inf_dist_compl_subset_closure
- \- *lemma* metric.closed_ball_inf_dist_compl_subset_closure'
- \+/\- *lemma* metric.closed_ball_inf_dist_compl_subset_closure

modified src/topology/metric_space/basic.lean
- \+ *lemma* closed_ball_zero'
- \+/\- *theorem* mem_of_closed'
- \+/\- *theorem* mem_of_closed'



## [2022-03-28 06:13:12](https://github.com/leanprover-community/mathlib/commit/c65d807)
feat(data/polynomial/erase_lead + data/polynomial/reverse): rename an old lemma, add a stronger one ([#12909](https://github.com/leanprover-community/mathlib/pull/12909))
Taking advantage of nat-subtraction in edge cases, a lemma that previously proved `x ≤ y` actually holds with `x ≤ y - 1`.
Thus, I renamed the old lemma to `original_name_aux` and `original_name` is now the name of the new lemma.  Since this lemma was used in a different file, I used the `_aux` name in the other file.
Note that the `_aux` lemma is currently an ingredient in the proof of the stronger lemma.  It may be possible to have a simple direct proof of the stronger one that avoids using the `_aux` lemma, but I have not given this any thought.
#### Estimated changes
modified src/data/polynomial/erase_lead.lean
- \+ *lemma* erase_lead_nat_degree_le_aux
- \+/\- *lemma* erase_lead_nat_degree_le
- \+/\- *lemma* erase_lead_nat_degree_le

modified src/data/polynomial/reverse.lean



## [2022-03-28 06:13:11](https://github.com/leanprover-community/mathlib/commit/7a1e0f2)
feat(analysis/inner_product_space): an inner product space is strictly convex ([#12790](https://github.com/leanprover-community/mathlib/pull/12790))
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean



## [2022-03-28 05:04:36](https://github.com/leanprover-community/mathlib/commit/1e72d86)
chore(data/polynomial/degree/lemmas + data/polynomial/ring_division): move lemmas, reduce assumptions, golf ([#12858](https://github.com/leanprover-community/mathlib/pull/12858))
This PR takes advantage of the reduced assumptions that are a consequence of [#12854](https://github.com/leanprover-community/mathlib/pull/12854).  Again, I moved two lemmas from their current location to a different file, where the typeclass assumptions make more sense,
#### Estimated changes
modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* nat_degree_comp
- \+ *lemma* leading_coeff_comp

modified src/data/polynomial/eval.lean

modified src/data/polynomial/ring_division.lean
- \- *lemma* nat_degree_comp
- \- *lemma* leading_coeff_comp



## [2022-03-27 19:56:25](https://github.com/leanprover-community/mathlib/commit/e5cd2ea)
feat(analysis/von_neumann): concrete and abstract definitions of a von Neumann algebra ([#12329](https://github.com/leanprover-community/mathlib/pull/12329))
#### Estimated changes
modified src/algebra/algebra/subalgebra/basic.lean
- \+ *lemma* _root_.set.algebra_map_mem_centralizer
- \+ *lemma* coe_centralizer
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* centralizer_le
- \+ *lemma* centralizer_univ
- \+ *def* centralizer

created src/algebra/star/subalgebra.lean
- \+ *lemma* coe_centralizer
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* centralizer_le
- \+ *def* centralizer

modified src/analysis/inner_product_space/adjoint.lean

created src/analysis/von_neumann_algebra/basic.lean

modified src/group_theory/submonoid/basic.lean

modified src/group_theory/submonoid/centralizer.lean
- \+/\- *lemma* coe_centralizer
- \+ *lemma* centralizer_le
- \+/\- *lemma* coe_centralizer
- \- *lemma* centralizer_subset

modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* coe_centralizer
- \+ *lemma* centralizer_to_submonoid
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* centralizer_le
- \+ *lemma* centralizer_univ
- \+ *def* centralizer



## [2022-03-27 15:52:15](https://github.com/leanprover-community/mathlib/commit/1494a9b)
feat(data/zmod/basic): add `int_coe_eq_int_coe_iff_dvd_sub` ([#12944](https://github.com/leanprover-community/mathlib/pull/12944))
This adds the following API lemma.
```
lemma int_coe_eq_int_coe_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : zmod c) = ↑b ↔ ↑c ∣ b-a
```
extending the already present version with b = 0. [(Zulip discussion)](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Missing.20zmod.20lemma.3F)
#### Estimated changes
modified src/data/zmod/basic.lean
- \+ *lemma* int_coe_eq_int_coe_iff_dvd_sub



## [2022-03-27 10:05:55](https://github.com/leanprover-community/mathlib/commit/d620ad3)
feat(measure_theory/measure/measure_space): remove measurable_set assumption in ae_measurable.subtype_mk ([#12978](https://github.com/leanprover-community/mathlib/pull/12978))
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* exists_ae_eq_range_subset
- \+/\- *lemma* subtype_mk
- \+/\- *lemma* subtype_mk



## [2022-03-27 04:09:23](https://github.com/leanprover-community/mathlib/commit/2c6df07)
chore(model_theory/*): Split up big model theory files ([#12918](https://github.com/leanprover-community/mathlib/pull/12918))
Splits up `model_theory/basic` into `model_theory/basic`, `model_theory/language_maps`, and `model_theory/bundled`.
Splits up `model_theory/terms_and_formulas` into `model_theory/syntax`, `model_theory/semantics`, and `model_theory/satisfiability`.
Adds to the module docs of these files.
#### Estimated changes
modified src/model_theory/basic.lean
- \- *lemma* id_comp
- \- *lemma* comp_id
- \- *lemma* comp_assoc
- \- *lemma* sum_elim_comp_inl
- \- *lemma* sum_elim_comp_inr
- \- *lemma* sum_map_comp_inl
- \- *lemma* sum_map_comp_inr
- \- *lemma* constants_on_constants
- \- *lemma* constants_on_map_is_expansion_on
- \- *lemma* Lhom.map_constants_comp_sum_inl
- \- *lemma* coe_con
- \- *theorem* sum_elim_inl_inr
- \- *theorem* comp_sum_elim
- \- *def* comp
- \- *def* sum_map
- \- *def* constants_on_functions
- \- *def* constants_on
- \- *def* constants_on.Structure
- \- *def* Lhom.constants_on_map
- \- *def* with_constants
- \- *def* Lhom_with_constants
- \- *def* Lhom.add_constants
- \- *def* Lequiv.add_empty_constants
- \- *def* Lhom_with_constants_map

created src/model_theory/bundled.lean

modified src/model_theory/definability.lean

modified src/model_theory/elementary_maps.lean

modified src/model_theory/fraisse.lean

created src/model_theory/language_map.lean
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* comp_assoc
- \+ *lemma* sum_elim_comp_inl
- \+ *lemma* sum_elim_comp_inr
- \+ *lemma* sum_map_comp_inl
- \+ *lemma* sum_map_comp_inr
- \+ *lemma* constants_on_constants
- \+ *lemma* constants_on_map_is_expansion_on
- \+ *lemma* Lhom.map_constants_comp_sum_inl
- \+ *lemma* coe_con
- \+ *theorem* sum_elim_inl_inr
- \+ *theorem* comp_sum_elim
- \+ *def* comp
- \+ *def* sum_map
- \+ *def* constants_on_functions
- \+ *def* constants_on
- \+ *def* constants_on.Structure
- \+ *def* Lhom.constants_on_map
- \+ *def* with_constants
- \+ *def* Lhom_with_constants
- \+ *def* Lhom.add_constants
- \+ *def* Lequiv.add_empty_constants
- \+ *def* Lhom_with_constants_map

modified src/model_theory/quotients.lean

created src/model_theory/satisfiability.lean
- \+ *lemma* model.is_satisfiable
- \+ *lemma* is_satisfiable.mono
- \+ *lemma* is_satisfiable.is_finitely_satisfiable
- \+ *lemma* models_formula_iff
- \+ *lemma* models_sentence_iff
- \+ *lemma* semantically_equivalent.refl
- \+ *lemma* semantically_equivalent.symm
- \+ *lemma* semantically_equivalent.trans
- \+ *lemma* semantically_equivalent.realize_bd_iff
- \+ *lemma* semantically_equivalent.some_model_realize_bd_iff
- \+ *lemma* semantically_equivalent.realize_iff
- \+ *lemma* semantically_equivalent.some_model_realize_iff
- \+ *lemma* semantically_equivalent_not_not
- \+ *lemma* imp_semantically_equivalent_not_sup
- \+ *lemma* sup_semantically_equivalent_not_inf_not
- \+ *lemma* inf_semantically_equivalent_not_sup_not
- \+ *lemma* all_semantically_equivalent_not_ex_not
- \+ *lemma* ex_semantically_equivalent_not_all_not
- \+ *lemma* semantically_equivalent_all_lift_at
- \+ *lemma* semantically_equivalent_not_not
- \+ *lemma* imp_semantically_equivalent_not_sup
- \+ *lemma* sup_semantically_equivalent_not_inf_not
- \+ *lemma* inf_semantically_equivalent_not_sup_not
- \+ *lemma* is_qf.induction_on_sup_not
- \+ *lemma* is_qf.induction_on_inf_not
- \+ *lemma* semantically_equivalent_to_prenex
- \+ *lemma* induction_on_all_ex
- \+ *lemma* induction_on_exists_not
- \+ *theorem* is_satisfiable_iff_is_finitely_satisfiable
- \+ *def* is_satisfiable
- \+ *def* is_finitely_satisfiable
- \+ *def* is_satisfiable.some_model
- \+ *def* models_bounded_formula
- \+ *def* semantically_equivalent
- \+ *def* semantically_equivalent_setoid

created src/model_theory/semantics.lean
- \+ *lemma* realize_relabel
- \+ *lemma* realize_lift_at
- \+ *lemma* realize_constants
- \+ *lemma* realize_con
- \+ *lemma* realize_on_term
- \+ *lemma* hom.realize_term
- \+ *lemma* embedding.realize_term
- \+ *lemma* equiv.realize_term
- \+ *lemma* realize_bot
- \+ *lemma* realize_not
- \+ *lemma* realize_bd_equal
- \+ *lemma* realize_top
- \+ *lemma* realize_inf
- \+ *lemma* realize_imp
- \+ *lemma* realize_rel
- \+ *lemma* realize_sup
- \+ *lemma* realize_all
- \+ *lemma* realize_ex
- \+ *lemma* realize_iff
- \+ *lemma* realize_cast_le_of_eq
- \+ *lemma* realize_relabel
- \+ *lemma* realize_lift_at
- \+ *lemma* realize_lift_at_one
- \+ *lemma* realize_lift_at_one_self
- \+ *lemma* realize_all_lift_at_one_self
- \+ *lemma* realize_to_prenex_imp_right
- \+ *lemma* realize_to_prenex_imp
- \+ *lemma* realize_to_prenex
- \+ *lemma* realize_on_bounded_formula
- \+ *lemma* realize_not
- \+ *lemma* realize_bot
- \+ *lemma* realize_top
- \+ *lemma* realize_inf
- \+ *lemma* realize_imp
- \+ *lemma* realize_rel
- \+ *lemma* realize_sup
- \+ *lemma* realize_iff
- \+ *lemma* realize_relabel
- \+ *lemma* realize_equal
- \+ *lemma* realize_graph
- \+ *lemma* Lhom.realize_on_formula
- \+ *lemma* Lhom.set_of_realize_on_formula
- \+ *lemma* Lhom.realize_on_sentence
- \+ *lemma* Theory.realize_sentence_of_mem
- \+ *lemma* Lhom.on_Theory_model
- \+ *lemma* Theory.model.mono
- \+ *lemma* realize_alls
- \+ *lemma* realize_exs
- \+ *lemma* equiv.realize_bounded_formula
- \+ *lemma* equiv.realize_formula
- \+ *def* realize
- \+ *def* realize
- \+ *def* realize
- \+ *def* sentence.realize

modified src/model_theory/substructures.lean

created src/model_theory/syntax.lean
- \+ *lemma* list_encode_injective
- \+ *lemma* card_le_omega
- \+ *lemma* id_on_term
- \+ *lemma* comp_on_term
- \+ *lemma* sum_elim_comp_relabel_aux
- \+ *lemma* not_all_is_atomic
- \+ *lemma* not_ex_is_atomic
- \+ *lemma* is_atomic.relabel
- \+ *lemma* is_atomic.lift_at
- \+ *lemma* is_atomic.cast_le
- \+ *lemma* is_atomic.is_qf
- \+ *lemma* is_qf_bot
- \+ *lemma* is_qf.not
- \+ *lemma* is_qf.relabel
- \+ *lemma* is_qf.lift_at
- \+ *lemma* is_qf.cast_le
- \+ *lemma* not_all_is_qf
- \+ *lemma* not_ex_is_qf
- \+ *lemma* is_qf.is_prenex
- \+ *lemma* is_atomic.is_prenex
- \+ *lemma* is_prenex.induction_on_all_not
- \+ *lemma* is_prenex.relabel
- \+ *lemma* is_prenex.cast_le
- \+ *lemma* is_prenex.lift_at
- \+ *lemma* is_qf.to_prenex_imp_right
- \+ *lemma* is_prenex_to_prenex_imp_right
- \+ *lemma* is_qf.to_prenex_imp
- \+ *lemma* is_prenex_to_prenex_imp
- \+ *lemma* to_prenex_is_prenex
- \+ *lemma* id_on_bounded_formula
- \+ *lemma* comp_on_bounded_formula
- \+ *lemma* mem_on_Theory
- \+ *lemma* on_bounded_formula_symm
- \+ *lemma* on_formula_apply
- \+ *lemma* on_formula_symm
- \+ *lemma* is_atomic_graph
- \+ *theorem* list_decode_encode_list
- \+ *theorem* card_le
- \+ *def* relabel
- \+ *def* list_encode
- \+ *def* list_decode
- \+ *def* constants.term
- \+ *def* lift_at
- \+ *def* on_term
- \+ *def* Lequiv.on_term
- \+ *def* formula
- \+ *def* sentence
- \+ *def* Theory
- \+ *def* relations.bounded_formula
- \+ *def* term.bd_equal
- \+ *def* relations.formula
- \+ *def* term.equal
- \+ *def* cast_le
- \+ *def* relabel_aux
- \+ *def* relabel
- \+ *def* alls
- \+ *def* exs
- \+ *def* lift_at
- \+ *def* to_prenex_imp_right
- \+ *def* to_prenex_imp
- \+ *def* to_prenex
- \+ *def* on_bounded_formula
- \+ *def* on_formula
- \+ *def* on_sentence
- \+ *def* on_Theory
- \+ *def* on_bounded_formula
- \+ *def* on_formula
- \+ *def* on_sentence
- \+ *def* relabel
- \+ *def* graph

deleted src/model_theory/terms_and_formulas.lean
- \- *lemma* list_encode_injective
- \- *lemma* card_le_omega
- \- *lemma* realize_relabel
- \- *lemma* realize_lift_at
- \- *lemma* realize_constants
- \- *lemma* realize_con
- \- *lemma* id_on_term
- \- *lemma* comp_on_term
- \- *lemma* realize_on_term
- \- *lemma* hom.realize_term
- \- *lemma* embedding.realize_term
- \- *lemma* equiv.realize_term
- \- *lemma* sum_elim_comp_relabel_aux
- \- *lemma* realize_bot
- \- *lemma* realize_not
- \- *lemma* realize_bd_equal
- \- *lemma* realize_top
- \- *lemma* realize_inf
- \- *lemma* realize_imp
- \- *lemma* realize_rel
- \- *lemma* realize_sup
- \- *lemma* realize_all
- \- *lemma* realize_ex
- \- *lemma* realize_iff
- \- *lemma* realize_cast_le_of_eq
- \- *lemma* realize_relabel
- \- *lemma* realize_lift_at
- \- *lemma* realize_lift_at_one
- \- *lemma* realize_lift_at_one_self
- \- *lemma* realize_all_lift_at_one_self
- \- *lemma* not_all_is_atomic
- \- *lemma* not_ex_is_atomic
- \- *lemma* is_atomic.relabel
- \- *lemma* is_atomic.lift_at
- \- *lemma* is_atomic.cast_le
- \- *lemma* is_atomic.is_qf
- \- *lemma* is_qf_bot
- \- *lemma* is_qf.not
- \- *lemma* is_qf.relabel
- \- *lemma* is_qf.lift_at
- \- *lemma* is_qf.cast_le
- \- *lemma* not_all_is_qf
- \- *lemma* not_ex_is_qf
- \- *lemma* is_qf.is_prenex
- \- *lemma* is_atomic.is_prenex
- \- *lemma* is_prenex.induction_on_all_not
- \- *lemma* is_prenex.relabel
- \- *lemma* is_prenex.cast_le
- \- *lemma* is_prenex.lift_at
- \- *lemma* is_qf.to_prenex_imp_right
- \- *lemma* is_prenex_to_prenex_imp_right
- \- *lemma* is_qf.to_prenex_imp
- \- *lemma* is_prenex_to_prenex_imp
- \- *lemma* to_prenex_is_prenex
- \- *lemma* realize_to_prenex_imp_right
- \- *lemma* realize_to_prenex_imp
- \- *lemma* realize_to_prenex
- \- *lemma* id_on_bounded_formula
- \- *lemma* comp_on_bounded_formula
- \- *lemma* mem_on_Theory
- \- *lemma* realize_on_bounded_formula
- \- *lemma* on_bounded_formula_symm
- \- *lemma* on_formula_apply
- \- *lemma* on_formula_symm
- \- *lemma* realize_not
- \- *lemma* realize_bot
- \- *lemma* realize_top
- \- *lemma* realize_inf
- \- *lemma* realize_imp
- \- *lemma* realize_rel
- \- *lemma* realize_sup
- \- *lemma* realize_iff
- \- *lemma* realize_relabel
- \- *lemma* realize_equal
- \- *lemma* realize_graph
- \- *lemma* is_atomic_graph
- \- *lemma* Lhom.realize_on_formula
- \- *lemma* Lhom.set_of_realize_on_formula
- \- *lemma* Lhom.realize_on_sentence
- \- *lemma* Theory.realize_sentence_of_mem
- \- *lemma* Lhom.on_Theory_model
- \- *lemma* Theory.model.mono
- \- *lemma* realize_alls
- \- *lemma* realize_exs
- \- *lemma* equiv.realize_bounded_formula
- \- *lemma* equiv.realize_formula
- \- *lemma* model.is_satisfiable
- \- *lemma* is_satisfiable.mono
- \- *lemma* is_satisfiable.is_finitely_satisfiable
- \- *lemma* models_formula_iff
- \- *lemma* models_sentence_iff
- \- *lemma* semantically_equivalent.refl
- \- *lemma* semantically_equivalent.symm
- \- *lemma* semantically_equivalent.trans
- \- *lemma* semantically_equivalent.realize_bd_iff
- \- *lemma* semantically_equivalent.some_model_realize_bd_iff
- \- *lemma* semantically_equivalent.realize_iff
- \- *lemma* semantically_equivalent.some_model_realize_iff
- \- *lemma* semantically_equivalent_not_not
- \- *lemma* imp_semantically_equivalent_not_sup
- \- *lemma* sup_semantically_equivalent_not_inf_not
- \- *lemma* inf_semantically_equivalent_not_sup_not
- \- *lemma* all_semantically_equivalent_not_ex_not
- \- *lemma* ex_semantically_equivalent_not_all_not
- \- *lemma* semantically_equivalent_all_lift_at
- \- *lemma* semantically_equivalent_not_not
- \- *lemma* imp_semantically_equivalent_not_sup
- \- *lemma* sup_semantically_equivalent_not_inf_not
- \- *lemma* inf_semantically_equivalent_not_sup_not
- \- *lemma* is_qf.induction_on_sup_not
- \- *lemma* is_qf.induction_on_inf_not
- \- *lemma* semantically_equivalent_to_prenex
- \- *lemma* induction_on_all_ex
- \- *lemma* induction_on_exists_not
- \- *theorem* list_decode_encode_list
- \- *theorem* card_le
- \- *def* relabel
- \- *def* list_encode
- \- *def* list_decode
- \- *def* constants.term
- \- *def* realize
- \- *def* lift_at
- \- *def* on_term
- \- *def* Lequiv.on_term
- \- *def* formula
- \- *def* sentence
- \- *def* Theory
- \- *def* relations.bounded_formula
- \- *def* term.bd_equal
- \- *def* relations.formula
- \- *def* term.equal
- \- *def* cast_le
- \- *def* relabel_aux
- \- *def* relabel
- \- *def* alls
- \- *def* exs
- \- *def* lift_at
- \- *def* realize
- \- *def* to_prenex_imp_right
- \- *def* to_prenex_imp
- \- *def* to_prenex
- \- *def* on_bounded_formula
- \- *def* on_formula
- \- *def* on_sentence
- \- *def* on_Theory
- \- *def* on_bounded_formula
- \- *def* on_formula
- \- *def* on_sentence
- \- *def* relabel
- \- *def* graph
- \- *def* realize
- \- *def* sentence.realize
- \- *def* is_satisfiable
- \- *def* is_finitely_satisfiable
- \- *def* is_satisfiable.some_model
- \- *def* models_bounded_formula
- \- *def* semantically_equivalent
- \- *def* semantically_equivalent_setoid

modified src/model_theory/ultraproducts.lean
- \- *theorem* is_satisfiable_iff_is_finitely_satisfiable



## [2022-03-27 03:34:03](https://github.com/leanprover-community/mathlib/commit/57a5fd7)
chore(scripts): update nolints.txt ([#12971](https://github.com/leanprover-community/mathlib/pull/12971))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-27 00:27:34](https://github.com/leanprover-community/mathlib/commit/664247f)
chore(data/set/intervals/ord_connected): Golf proof ([#12923](https://github.com/leanprover-community/mathlib/pull/12923))
#### Estimated changes
modified src/data/set/intervals/ord_connected.lean



## [2022-03-27 00:27:33](https://github.com/leanprover-community/mathlib/commit/05ef694)
refactor(topology/instances/ennreal): make `ennreal` an instance of `has_continuous_inv` ([#12806](https://github.com/leanprover-community/mathlib/pull/12806))
Prior to the type class `has_continuous_inv`, `ennreal` had to have it's own hand-rolled `ennreal.continuous_inv` statement. This replaces it with a `has_continuous_inv` instance.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)
#### Estimated changes
modified src/analysis/special_functions/pow.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/instances/ennreal.lean



## [2022-03-26 23:54:12](https://github.com/leanprover-community/mathlib/commit/caf6f19)
refactor(category_theory/abelian): deduplicate definitions of (co)image ([#12902](https://github.com/leanprover-community/mathlib/pull/12902))
Previously we made two separate definitions of the abelian (co)image, as `kernel (cokernel.π f)` / `cokernel (kernel.ι f)`,
once for `non_preadditive_abelian C` and once for `abelian C`.
This duplication wasn't really necessary, and this PR unifies them.
#### Estimated changes
modified src/category_theory/abelian/basic.lean
- \+/\- *lemma* image_ι_comp_eq_zero
- \+/\- *lemma* comp_coimage_π_eq_zero
- \+/\- *lemma* full_image_factorisation
- \+/\- *lemma* image_ι_comp_eq_zero
- \+/\- *lemma* comp_coimage_π_eq_zero
- \+/\- *lemma* full_image_factorisation

modified src/category_theory/abelian/exact.lean
- \+/\- *def* is_colimit_coimage
- \+/\- *def* is_colimit_image
- \+/\- *def* is_colimit_coimage
- \+/\- *def* is_colimit_image

created src/category_theory/abelian/images.lean

modified src/category_theory/abelian/non_preadditive.lean

modified src/category_theory/abelian/pseudoelements.lean



## [2022-03-26 23:17:46](https://github.com/leanprover-community/mathlib/commit/f5a9d0a)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at ([#12707](https://github.com/leanprover-community/mathlib/pull/12707))
We add `cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at`.
From flt-regular
#### Estimated changes
modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* _root_.polynomial.monic.leading_coeff_not_mem
- \+ *lemma* _root_.polynomial.monic.is_eisenstein_at_of_mem_of_not_mem
- \+ *lemma* cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at



## [2022-03-26 21:16:08](https://github.com/leanprover-community/mathlib/commit/7b93889)
refactor(data/list/basic): Remove many redundant hypotheses ([#12950](https://github.com/leanprover-community/mathlib/pull/12950))
Many theorems about `last` required arguments proving that certain things were not equal to `nil`, when in fact this was always the case. These hypotheses have been removed and replaced with the corresponding proofs.
#### Estimated changes
modified src/data/list/basic.lean
- \+/\- *theorem* last_append
- \+/\- *theorem* last_concat
- \+/\- *theorem* last_singleton
- \+/\- *theorem* last_cons_cons
- \+/\- *theorem* last_append
- \+/\- *theorem* last_concat
- \+/\- *theorem* last_singleton
- \+/\- *theorem* last_cons_cons

modified src/data/nat/digits.lean



## [2022-03-26 21:16:07](https://github.com/leanprover-community/mathlib/commit/e63e332)
feat(algebra/ring/basic): all non-zero elements in a non-trivial ring with no non-zero zero divisors are regular ([#12947](https://github.com/leanprover-community/mathlib/pull/12947))
Besides what the PR description says, I also golfed two earlier proofs.
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+ *lemma* is_regular_iff_ne_zero'



## [2022-03-26 21:16:06](https://github.com/leanprover-community/mathlib/commit/b30f25c)
fix(data/set/prod): fix the way `×ˢ` associates ([#12943](https://github.com/leanprover-community/mathlib/pull/12943))
Previously `s ×ˢ t ×ˢ u` was an element of `set ((α × β) × γ)` instead of `set (α × β × γ) = set (α × (β × γ))`.
#### Estimated changes
modified src/data/set/prod.lean



## [2022-03-26 21:16:05](https://github.com/leanprover-community/mathlib/commit/cc8c90d)
chore(data/equiv): split and move to `logic/equiv` ([#12929](https://github.com/leanprover-community/mathlib/pull/12929))
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rearranging.20files.20in.20.60data.2F.60
This PR rearranges files in `data/equiv/` by 1) moving bundled isomorphisms to a relevant subfolder of `algebra/`; 2) moving `denumerable` and `encodable` to `logic/`; 3) moving the remainder of `data/equiv/` to `logic/equiv/`. The commits of this PR correspond to those steps.
In particular, the following files were moved:
 * `data/equiv/module.lean` → `algebra/module/equiv.lean`
 * `data/equiv/mul_add.lean` → `algebra/hom/equiv.lean`
 * `data/equiv/mul_add_aut.lean` → `algebra/hom/aut.lean`
 * `data/equiv/ring.lean` → `algebra/ring/equiv.lean`
 * `data/equiv/ring_aut.lean` → `algebra/ring/aut.lean`
 * `data/equiv/denumerable.lean` → `logic/denumerable.lean`
 * `data/equiv/encodable/*.lean` → `logic/encodable/basic.lean logic/encodable/lattice.lean logic/encodable/small.lean`
 * `data/equiv/*.lean` to: `logic/equiv/basic.lean logic/equiv/fin.lean logic/equiv/functor.lean logic/equiv/local_equiv.lean logic/equiv/option.lean logic/equiv/transfer_instance.lean logic/equiv/embedding.lean logic/equiv/fintype.lean logic/equiv/list.lean logic/equiv/nat.lean logic/equiv/set.lean`
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/big_operators/basic.lean

modified src/algebra/category/CommRing/basic.lean

modified src/algebra/field_power.lean

modified src/algebra/free.lean

modified src/algebra/group/conj.lean

modified src/algebra/group/opposite.lean

modified src/algebra/group/type_tags.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group/with_one.lean

modified src/algebra/group_ring_action.lean

renamed src/data/equiv/mul_add_aut.lean to src/algebra/hom/aut.lean

renamed src/data/equiv/mul_add.lean to src/algebra/hom/equiv.lean

modified src/algebra/lie/basic.lean

renamed src/data/equiv/module.lean to src/algebra/module/equiv.lean

modified src/algebra/module/opposites.lean

modified src/algebra/module/submodule.lean

modified src/algebra/module/ulift.lean

modified src/algebra/opposites.lean

modified src/algebra/order/hom/ring.lean

modified src/algebra/order/monoid.lean

modified src/algebra/quandle.lean

modified src/algebra/quaternion.lean

renamed src/data/equiv/ring_aut.lean to src/algebra/ring/aut.lean

modified src/algebra/ring/comp_typeclasses.lean

renamed src/data/equiv/ring.lean to src/algebra/ring/equiv.lean

modified src/algebra/ring/prod.lean

modified src/algebra/ring/ulift.lean

modified src/algebra/star/basic.lean

modified src/algebra/star/module.lean

modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/locally_ringed_space.lean

modified src/analysis/analytic/basic.lean

modified src/category_theory/endomorphism.lean

modified src/category_theory/functor/fully_faithful.lean

modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean

modified src/category_theory/preadditive/opposite.lean

modified src/category_theory/types.lean

modified src/combinatorics/derangements/basic.lean

modified src/computability/primrec.lean

modified src/control/equiv_functor.lean

modified src/control/monad/basic.lean

modified src/control/monad/writer.lean

modified src/control/traversable/equiv.lean

modified src/control/uliftable.lean

modified src/data/W/basic.lean

modified src/data/erased.lean

modified src/data/finsupp/to_dfinsupp.lean

modified src/data/fintype/card_embedding.lean

modified src/data/matrix/basic.lean

modified src/data/mv_polynomial/equiv.lean

modified src/data/nat/enat.lean

modified src/data/opposite.lean

modified src/data/part.lean

modified src/data/rat/basic.lean

modified src/data/set/countable.lean

modified src/data/ulift.lean

modified src/deprecated/group.lean

modified src/field_theory/cardinality.lean

modified src/field_theory/finite/basic.lean

modified src/field_theory/perfect_closure.lean

modified src/group_theory/congruence.lean

modified src/group_theory/free_abelian_group_finsupp.lean

modified src/group_theory/group_action/group.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/fin.lean

modified src/group_theory/perm/option.lean

modified src/group_theory/semidirect_product.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/linear_independent.lean

modified src/linear_algebra/pi.lean

renamed src/data/equiv/denumerable.lean to src/logic/denumerable.lean

modified src/logic/embedding.lean

renamed src/data/equiv/encodable/basic.lean to src/logic/encodable/basic.lean

renamed src/data/equiv/encodable/lattice.lean to src/logic/encodable/lattice.lean

renamed src/data/equiv/encodable/small.lean to src/logic/encodable/small.lean

renamed src/data/equiv/basic.lean to src/logic/equiv/basic.lean

renamed src/data/equiv/embedding.lean to src/logic/equiv/embedding.lean

renamed src/data/equiv/fin.lean to src/logic/equiv/fin.lean

renamed src/data/equiv/fintype.lean to src/logic/equiv/fintype.lean

renamed src/data/equiv/functor.lean to src/logic/equiv/functor.lean

renamed src/data/equiv/list.lean to src/logic/equiv/list.lean

renamed src/data/equiv/local_equiv.lean to src/logic/equiv/local_equiv.lean

renamed src/data/equiv/nat.lean to src/logic/equiv/nat.lean

renamed src/data/equiv/option.lean to src/logic/equiv/option.lean

renamed src/data/equiv/set.lean to src/logic/equiv/set.lean

renamed src/data/equiv/transfer_instance.lean to src/logic/equiv/transfer_instance.lean

modified src/logic/small.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measurable_space_def.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/measure_theory/pi_system.lean

modified src/model_theory/basic.lean

modified src/model_theory/definability.lean

modified src/model_theory/terms_and_formulas.lean

modified src/order/hom/basic.lean

modified src/order/ideal.lean

modified src/order/jordan_holder.lean

modified src/order/lexicographic.lean

modified src/order/order_dual.lean

modified src/order/order_iso_nat.lean

modified src/order/rel_iso.lean

modified src/order/semiconj_Sup.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/local_properties.lean

modified src/ring_theory/localization/basic.lean

modified src/ring_theory/localization/integral.lean

modified src/ring_theory/ring_invo.lean

modified src/ring_theory/subsemiring/basic.lean

modified src/tactic/equiv_rw.lean

modified src/tactic/norm_swap.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/homeomorph.lean

modified src/topology/local_homeomorph.lean

modified test/norm_swap.lean

modified test/semilinear.lean

modified test/simp_result.lean



## [2022-03-26 20:22:51](https://github.com/leanprover-community/mathlib/commit/434a938)
feat(analysis/convex/strict_convex_space): Strictly convex spaces ([#11794](https://github.com/leanprover-community/mathlib/pull/11794))
Define `strictly_convex_space`, a `Prop`-valued mixin to state that a normed space is strictly convex.
#### Estimated changes
modified src/analysis/convex/integral.lean
- \+ *lemma* ae_eq_const_or_norm_integral_lt_of_norm_le_const
- \- *lemma* strict_convex.ae_eq_const_or_norm_integral_lt_of_norm_le_const

modified src/analysis/convex/strict.lean

created src/analysis/convex/strict_convex_space.lean
- \+ *lemma* strict_convex_closed_ball
- \+ *lemma* strict_convex_space.of_strict_convex_closed_unit_ball
- \+ *lemma* strict_convex_space.of_norm_add
- \+ *lemma* combo_mem_ball_of_ne
- \+ *lemma* open_segment_subset_ball_of_ne
- \+ *lemma* norm_combo_lt_of_ne
- \+ *lemma* norm_add_lt_of_not_same_ray
- \+ *lemma* same_ray_iff_norm_add
- \+ *lemma* dist_add_dist_eq_iff

modified src/analysis/convex/topology.lean
- \+ *lemma* dist_add_dist_of_mem_segment

modified src/analysis/inner_product_space/basic.lean

modified src/analysis/normed_space/basic.lean
- \+ *lemma* inv_norm_smul_mem_closed_unit_ball



## [2022-03-26 19:19:53](https://github.com/leanprover-community/mathlib/commit/1f11f3f)
chore(order/filter/basic): rename using the zero subscript convention for groups with zero ([#12952](https://github.com/leanprover-community/mathlib/pull/12952))
#### Estimated changes
modified src/order/filter/basic.lean
- \+/\- *lemma* eventually_eq.div
- \+/\- *lemma* eventually_eq.div
- \- *lemma* eventually_eq.div'
- \- *lemma* eventually_eq.sub



## [2022-03-26 18:24:35](https://github.com/leanprover-community/mathlib/commit/a491055)
chore(measure_theory/integral/lebesgue): extend to ae_measurable ([#12953](https://github.com/leanprover-community/mathlib/pull/12953))
#### Estimated changes
modified src/measure_theory/group/arithmetic.lean

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* apply_mk
- \+ *lemma* extend_apply'
- \+ *lemma* mul_meas_ge_le_lintegral₀
- \+/\- *lemma* lintegral_eq_top_of_measure_eq_top_pos
- \+/\- *lemma* meas_ge_le_lintegral_div
- \+/\- *lemma* lintegral_trim
- \+/\- *lemma* univ_le_of_forall_fin_meas_le
- \+/\- *lemma* lintegral_eq_top_of_measure_eq_top_pos
- \+/\- *lemma* meas_ge_le_lintegral_div
- \+/\- *lemma* lintegral_trim
- \+/\- *lemma* univ_le_of_forall_fin_meas_le
- \+ *def* of_is_empty



## [2022-03-26 14:15:19](https://github.com/leanprover-community/mathlib/commit/cb2797e)
feat(measure_theory/constructions/borel_space): drop a countability assumption ([#12954](https://github.com/leanprover-community/mathlib/pull/12954))
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_of_tendsto_metrizable'
- \+ *lemma* measurable_of_tendsto_metrizable
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae



## [2022-03-26 12:20:15](https://github.com/leanprover-community/mathlib/commit/b7d9166)
chore(measure_theory/measure/lebesgue): delete leftovers ([#12951](https://github.com/leanprover-community/mathlib/pull/12951))
#### Estimated changes
modified src/measure_theory/measure/lebesgue.lean
- \- *theorem* vitali_aux_mem
- \- *theorem* vitali_aux_rel
- \- *theorem* vitali_nonmeasurable
- \- *def* vitali_aux_h
- \- *def* vitali_aux
- \- *def* vitali



## [2022-03-26 12:20:14](https://github.com/leanprover-community/mathlib/commit/1111482)
feat(topology/bases): separable subsets of topological spaces ([#12936](https://github.com/leanprover-community/mathlib/pull/12936))
#### Estimated changes
modified src/topology/bases.lean
- \+ *lemma* separable_space_of_dense_range
- \+ *lemma* is_separable.mono
- \+ *lemma* is_separable.union
- \+ *lemma* is_separable.closure
- \+ *lemma* is_separable_Union
- \+ *lemma* _root_.set.countable.is_separable
- \+ *lemma* _root_.set.finite.is_separable
- \+ *lemma* is_separable_univ_iff
- \+ *lemma* is_separable_of_separable_space
- \+ *lemma* is_separable.image
- \+ *lemma* is_separable_of_separable_space_subtype
- \+ *def* is_separable

modified src/topology/constructions.lean
- \+ *lemma* inducing.cod_restrict
- \+ *lemma* embedding.cod_restrict

modified src/topology/metric_space/basic.lean
- \+/\- *lemma* mem_closure_range_iff
- \+/\- *lemma* mem_closure_range_iff_nat
- \+ *lemma* dense_iff
- \+ *lemma* dense_range_iff
- \+ *lemma* _root_.topological_space.is_separable.separable_space
- \+ *lemma* _root_.continuous_on.is_separable_image
- \+ *lemma* is_compact.is_separable
- \+/\- *lemma* mem_closure_range_iff
- \+/\- *lemma* mem_closure_range_iff_nat
- \+/\- *theorem* mem_closure_iff
- \+/\- *theorem* mem_of_closed'
- \+/\- *theorem* mem_closure_iff
- \+/\- *theorem* mem_of_closed'



## [2022-03-26 12:20:13](https://github.com/leanprover-community/mathlib/commit/f68536e)
feat(topology/constructions): continuity of uncurried functions when the first factor is discrete ([#12935](https://github.com/leanprover-community/mathlib/pull/12935))
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* map_pure_prod

modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean

modified src/topology/constructions.lean
- \+ *lemma* continuous_uncurry_of_discrete_topology



## [2022-03-26 12:20:12](https://github.com/leanprover-community/mathlib/commit/5e449c2)
feat(algebra/is_prime_pow): add `is_prime_pow_iff_factorization_single` ([#12167](https://github.com/leanprover-community/mathlib/pull/12167))
Adds lemma `is_prime_pow_iff_factorization_single : is_prime_pow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = finsupp.single p k`
Also adds `pow_of_factorization_single` to `data/nat/factorization`
#### Estimated changes
modified src/algebra/is_prime_pow.lean
- \+ *lemma* is_prime_pow_iff_factorization_eq_single
- \+ *lemma* is_prime_pow_iff_card_support_factorization_eq_one

modified src/data/nat/factorization.lean
- \+ *lemma* eq_pow_of_factorization_eq_single



## [2022-03-26 10:30:31](https://github.com/leanprover-community/mathlib/commit/023a783)
feat(logic/nontrivial): `exists_pair_lt` ([#12925](https://github.com/leanprover-community/mathlib/pull/12925))
#### Estimated changes
modified src/logic/nontrivial.lean
- \+ *lemma* exists_pair_lt
- \+ *lemma* nontrivial_iff_lt



## [2022-03-26 10:30:30](https://github.com/leanprover-community/mathlib/commit/c51f4f1)
feat(set_theory/cardinal_ordinal): `κ ^ n = κ` for infinite cardinals ([#12922](https://github.com/leanprover-community/mathlib/pull/12922))
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+/\- *lemma* power_nat_le
- \+ *lemma* power_nat_eq
- \+/\- *lemma* power_nat_le
- \+ *theorem* pow_eq



## [2022-03-26 09:35:33](https://github.com/leanprover-community/mathlib/commit/9d26041)
feat(topology/instances/ennreal): add `ennreal.has_sum_to_real` ([#12926](https://github.com/leanprover-community/mathlib/pull/12926))
#### Estimated changes
modified src/topology/instances/ennreal.lean
- \+ *lemma* has_sum_to_real
- \+/\- *lemma* summable_to_real
- \+/\- *lemma* summable_to_real



## [2022-03-26 03:28:38](https://github.com/leanprover-community/mathlib/commit/b83bd25)
feat(linear_algebra/sesquilinear_form): add nondegenerate ([#12683](https://github.com/leanprover-community/mathlib/pull/12683))
Defines nondegenerate sesquilinear forms as left and right separating sesquilinear forms.
#### Estimated changes
modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* flip_separating_right
- \+ *lemma* flip_separating_left
- \+ *lemma* flip_nondegenerate
- \+ *lemma* separating_left_iff_linear_nontrivial
- \+ *lemma* separating_right_iff_linear_flip_nontrivial
- \+ *lemma* is_symm.nondegenerate_of_separating_left
- \+ *lemma* is_symm.nondegenerate_of_separating_right
- \+ *lemma* nondegenerate_restrict_of_disjoint_orthogonal
- \+ *lemma* is_Ortho.not_is_ortho_basis_self_of_separating_left
- \+ *lemma* is_Ortho.not_is_ortho_basis_self_of_separating_right
- \+ *lemma* is_Ortho.separating_left_of_not_is_ortho_basis_self
- \+ *lemma* is_Ortho.separating_right_iff_not_is_ortho_basis_self
- \+ *lemma* is_Ortho.nondegenerate_of_not_is_ortho_basis_self
- \+ *theorem* separating_left_iff_ker_eq_bot
- \+ *theorem* separating_right_iff_flip_ker_eq_bot
- \+ *def* separating_left
- \+ *def* separating_right
- \+ *def* nondegenerate



## [2022-03-26 02:58:15](https://github.com/leanprover-community/mathlib/commit/17b621c)
chore(scripts): update nolints.txt ([#12946](https://github.com/leanprover-community/mathlib/pull/12946))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-25 19:43:25](https://github.com/leanprover-community/mathlib/commit/b6d246a)
feat(topology/continuous_function/cocompact_maps): add the type of cocompact continuous maps ([#12938](https://github.com/leanprover-community/mathlib/pull/12938))
This adds the type of cocompact continuous maps, which are those functions `f : α → β` for which `tendsto f (cocompact α) (cocompact β)`. These maps are of interest primarily because of their connection with continuous functions vanishing at infinity ([#12907](https://github.com/leanprover-community/mathlib/pull/12907)). In particular, if `f : α → β` is a cocompact continuous map and `g : β →C₀ γ` is a continuous function which vanishes at infinity, then `g ∘ f : α →C₀ γ`.
These are also related to quasi-compact maps (continuous maps for which preimages of compact sets are compact) and proper maps (continuous maps which are universally closed), neither of which are currently defined in mathlib. In particular, quasi-compact maps are cocompact continuous maps, and when the codomain is Hausdorff the converse holds also. Under some additional assumptions, both of these are also equivalent to being a proper map.
#### Estimated changes
created src/topology/continuous_function/cocompact_map.lean
- \+ *lemma* coe_to_continuous_fun
- \+ *lemma* ext
- \+ *lemma* coe_mk
- \+ *lemma* coe_id
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* tendsto_of_forall_preimage
- \+ *lemma* compact_preimage
- \+ *def* comp



## [2022-03-25 18:48:49](https://github.com/leanprover-community/mathlib/commit/221796a)
feat(topology/metric_space/metrizable): define and use a metrizable typeclass ([#12934](https://github.com/leanprover-community/mathlib/pull/12934))
#### Estimated changes
modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/metrizable.lean
- \+ *lemma* _root_.embedding.metrizable_space
- \+ *lemma* metrizable_space_of_normal_second_countable



## [2022-03-25 17:53:43](https://github.com/leanprover-community/mathlib/commit/5925650)
chore(nnreal): rename lemmas based on real.to_nnreal when they mention of_real ([#12937](https://github.com/leanprover-community/mathlib/pull/12937))
Many lemma using `real.to_nnreal` mention `of_real` in their names. This PR tries to make things more coherent.
#### Estimated changes
modified src/analysis/special_functions/pow.lean

modified src/data/real/sqrt.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean
- \+ *lemma* _root_.continuous_real_to_nnreal
- \+ *lemma* tendsto_real_to_nnreal
- \+ *lemma* has_sum_real_to_nnreal_of_nonneg
- \- *lemma* continuous_of_real
- \- *lemma* tendsto_of_real
- \- *lemma* has_sum_of_real_of_nonneg



## [2022-03-25 11:39:22](https://github.com/leanprover-community/mathlib/commit/2143571)
feat(topology/category/Born): The category of bornologies ([#12045](https://github.com/leanprover-community/mathlib/pull/12045))
Define `Born`, the category of bornological spaces with bounded maps.
#### Estimated changes
created src/topology/category/Born.lean
- \+ *def* Born
- \+ *def* of



## [2022-03-25 09:33:50](https://github.com/leanprover-community/mathlib/commit/172f317)
move(algebra/hom/*): Move group hom files together ([#12647](https://github.com/leanprover-community/mathlib/pull/12647))
Move
* `algebra.group.freiman` to `algebra.hom.freiman`
* `algebra.group.hom` to `algebra.hom.basic`
* `algebra.group.hom_instances` to `algebra.hom.instances`
* `algebra.group.units_hom` to `algebra.hom.units`
* `algebra.group_action_hom` to `algebra.hom.group_action`
* `algebra.iterate_hom` to `algebra.hom.iterate`
* `algebra.non_unital_alg_hom` to `algebra.hom.non_unital_alg`
#### Estimated changes
modified src/algebra/algebra/bilinear.lean

modified src/algebra/char_p/basic.lean

modified src/algebra/free.lean

modified src/algebra/group/conj.lean

modified src/algebra/group/default.lean

modified src/algebra/group/ext.lean

modified src/algebra/group/pi.lean

modified src/algebra/group/type_tags.lean

modified src/algebra/group_with_zero/basic.lean

renamed src/algebra/group/freiman.lean to src/algebra/hom/freiman.lean

renamed src/algebra/group/hom.lean to src/algebra/hom/group.lean

renamed src/algebra/group_action_hom.lean to src/algebra/hom/group_action.lean

renamed src/algebra/group/hom_instances.lean to src/algebra/hom/group_instances.lean

renamed src/algebra/iterate_hom.lean to src/algebra/hom/iterate.lean

renamed src/algebra/non_unital_alg_hom.lean to src/algebra/hom/non_unital_alg.lean

renamed src/algebra/group/units_hom.lean to src/algebra/hom/units.lean

modified src/algebra/lie/non_unital_non_assoc_algebra.lean

modified src/algebra/module/linear_map.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/order/hom/monoid.lean

modified src/algebra/polynomial/group_ring_action.lean

modified src/algebra/regular/pow.lean

modified src/category_theory/monoidal/discrete.lean

modified src/category_theory/preadditive/default.lean

modified src/data/finsupp/basic.lean

modified src/data/polynomial/derivative.lean

modified src/deprecated/group.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/field_theory/perfect_closure.lean

modified src/group_theory/group_action/defs.lean

modified src/group_theory/group_action/sub_mul_action.lean

modified src/group_theory/order_of_element.lean

modified src/topology/algebra/group_completion.lean

modified test/simps.lean



## [2022-03-25 09:03:06](https://github.com/leanprover-community/mathlib/commit/351c32f)
docs(docs/undergrad): Update TODO list ([#12752](https://github.com/leanprover-community/mathlib/pull/12752))
Update `undergrad` with the latest additions to mathlib.
#### Estimated changes
modified docs/undergrad.yaml



## [2022-03-25 02:56:04](https://github.com/leanprover-community/mathlib/commit/9ee02c6)
feat(data/pfun): Remove unneeded assumption from pfun.fix_induction ([#12920](https://github.com/leanprover-community/mathlib/pull/12920))
Removed a hypothesis from `pfun.fix_induction`. Note that it was two "layers" deep, so this is actually a strengthening. The original can be recovered by
```lean
/-- A recursion principle for `pfun.fix`. -/
@[elab_as_eliminator] def fix_induction_original
  {f : α →. β ⊕ α} {b : β} {C : α → Sort*} {a : α} (h : b ∈ f.fix a)
  (H : ∀ a', b ∈ f.fix a' →
    (∀ a'', /- this hypothesis was removed -/ b ∈ f.fix a'' → sum.inr a'' ∈ f a' → C a'') → C a') : C a :=
by { apply fix_induction h, intros, apply H; tauto, }
```
Note that `eval_induction` copies this syntax, so the same argument was removed there as well.
This allows for some simplifications of other parts of the code. Unfortunately, it was hard to figure out what was going on in the very dense parts of `tm_to_partrec.lean` and `partrec.lean`. I mostly just mechanically removed the hypotheses that were unnecessarily being supplied, and then checked if that caused some variable to be unused and removed that etc. But I cannot tell if this allows for greater simplifications.
I also extracted two lemmas `fix_fwd` and `fix_stop` that I thought would be useful on their own.
#### Estimated changes
modified src/computability/partrec.lean

modified src/computability/tm_to_partrec.lean

modified src/computability/turing_machine.lean

modified src/data/pfun.lean
- \+ *theorem* fix_stop
- \+ *theorem* fix_fwd



## [2022-03-25 00:37:21](https://github.com/leanprover-community/mathlib/commit/3dd8e4d)
feat(order/category/FinBoolAlg): The category of finite Boolean algebras ([#12906](https://github.com/leanprover-community/mathlib/pull/12906))
Define `FinBoolAlg`, the category of finite Boolean algebras.
#### Estimated changes
modified src/data/set/lattice.lean
- \+ *lemma* preimage_sInter

modified src/order/category/BoolAlg.lean
- \+ *lemma* coe_to_BoundedDistribLattice

created src/order/category/FinBoolAlg.lean
- \+ *lemma* coe_to_BoolAlg
- \+ *lemma* coe_of
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv
- \+ *def* Fintype_to_FinBoolAlg_op

modified src/order/category/FinPartialOrder.lean
- \+ *lemma* coe_to_PartialOrder

modified src/order/hom/complete_lattice.lean
- \+ *lemma* coe_set_preimage
- \+ *lemma* set_preimage_apply
- \+ *lemma* set_preimage_id
- \+ *lemma* set_preimage_comp
- \+ *def* set_preimage



## [2022-03-25 00:06:09](https://github.com/leanprover-community/mathlib/commit/7ec1a31)
fix(combinatorics/simple_graph/density): correct name in docstring ([#12921](https://github.com/leanprover-community/mathlib/pull/12921))
#### Estimated changes
modified src/combinatorics/simple_graph/density.lean



## [2022-03-24 22:53:04](https://github.com/leanprover-community/mathlib/commit/352ecfe)
feat(combinatorics/simple_graph/{connectivity,metric}): `connected` and `dist` ([#12574](https://github.com/leanprover-community/mathlib/pull/12574))
#### Estimated changes
modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* eq_of_length_eq_zero
- \+ *lemma* exists_length_eq_zero_iff
- \+/\- *lemma* is_cycle_def
- \+ *lemma* reachable_iff_nonempty_univ
- \+ *lemma* reachable_iff_refl_trans_gen
- \+ *lemma* reachable_is_equivalence
- \+ *lemma* preconnected.set_univ_walk_nonempty
- \+ *lemma* connected.set_univ_walk_nonempty
- \+/\- *lemma* is_cycle_def
- \+ *def* reachable
- \+ *def* reachable_setoid
- \+ *def* preconnected

created src/combinatorics/simple_graph/metric.lean
- \+ *lemma* reachable.exists_walk_of_dist
- \+ *lemma* connected.exists_walk_of_dist
- \+ *lemma* dist_le
- \+ *lemma* dist_eq_zero_iff_eq_or_not_reachable
- \+ *lemma* dist_self
- \+ *lemma* reachable.dist_eq_zero_iff
- \+ *lemma* reachable.pos_dist_of_ne
- \+ *lemma* connected.dist_eq_zero_iff
- \+ *lemma* connected.pos_dist_of_ne
- \+ *lemma* dist_eq_zero_of_not_reachable
- \+ *lemma* nonempty_of_pos_dist
- \+ *lemma* connected.dist_triangle
- \+ *lemma* dist_comm_aux
- \+ *lemma* dist_comm
- \+ *def* dist



## [2022-03-24 17:30:47](https://github.com/leanprover-community/mathlib/commit/2891e1b)
feat(algebra/category/BoolRing): The category of Boolean rings ([#12905](https://github.com/leanprover-community/mathlib/pull/12905))
Define `BoolRing`, the category of Boolean rings.
#### Estimated changes
created src/algebra/category/BoolRing.lean
- \+ *lemma* coe_of
- \+ *def* BoolRing
- \+ *def* of
- \+ *def* iso.mk

modified src/algebra/punit_instances.lean
- \+/\- *lemma* div_eq
- \+/\- *lemma* inv_eq
- \+/\- *lemma* div_eq
- \+/\- *lemma* inv_eq

modified src/algebra/ring/boolean_ring.lean
- \+ *lemma* to_boolalg_symm_eq
- \+ *lemma* of_boolalg_symm_eq
- \+ *lemma* to_boolalg_of_boolalg
- \+ *lemma* of_boolalg_to_boolalg
- \+ *lemma* to_boolalg_inj
- \+ *lemma* of_boolalg_inj
- \+ *lemma* of_boolalg_top
- \+ *lemma* of_boolalg_bot
- \+ *lemma* of_boolalg_sup
- \+ *lemma* of_boolalg_inf
- \+ *lemma* to_boolalg_zero
- \+ *lemma* to_boolalg_one
- \+ *lemma* to_boolalg_mul
- \+ *lemma* to_boolalg_add_add_mul
- \+ *lemma* ring_hom.as_boolalg_id
- \+ *lemma* ring_hom.as_boolalg_comp
- \- *lemma* sup_inf_sdiff
- \- *lemma* inf_inf_sdiff
- \+ *def* as_boolalg
- \+ *def* to_boolalg
- \+ *def* of_boolalg
- \+/\- *def* has_sup
- \+/\- *def* has_sup
- \- *def* has_sdiff
- \- *def* has_bot



## [2022-03-24 17:30:46](https://github.com/leanprover-community/mathlib/commit/f53b239)
feat(model_theory/fraisse): Construct Fraïssé limits ([#12138](https://github.com/leanprover-community/mathlib/pull/12138))
Constructs Fraïssé limits (nonuniquely)
#### Estimated changes
modified docs/references.bib

modified src/model_theory/direct_limit.lean
- \+ *lemma* coe_nat_le_rec
- \+ *theorem* cg
- \+ *def* nat_le_rec

modified src/model_theory/finitely_generated.lean

modified src/model_theory/fraisse.lean
- \+ *lemma* embedding.age_subset_age
- \+ *lemma* equiv.age_eq_age
- \+ *lemma* Structure.fg.mem_age_of_equiv
- \+ *lemma* hereditary.is_equiv_invariant_of_fg
- \+ *theorem* age_direct_limit
- \+ *theorem* exists_cg_is_age_of
- \+ *theorem* age_fraisse_limit



## [2022-03-24 16:39:34](https://github.com/leanprover-community/mathlib/commit/6ac7c18)
feat(combinatorics/simple_graph/density): Edge density ([#12431](https://github.com/leanprover-community/mathlib/pull/12431))
Define the number and density of edges of a relation and of a simple graph between two finsets.
#### Estimated changes
created src/combinatorics/simple_graph/density.lean
- \+ *lemma* mem_interedges_iff
- \+ *lemma* mk_mem_interedges_iff
- \+ *lemma* interedges_empty_left
- \+ *lemma* interedges_mono
- \+ *lemma* card_interedges_add_card_interedges_compl
- \+ *lemma* interedges_disjoint_left
- \+ *lemma* interedges_disjoint_right
- \+ *lemma* interedges_bUnion_left
- \+ *lemma* interedges_bUnion_right
- \+ *lemma* interedges_bUnion
- \+ *lemma* card_interedges_le_mul
- \+ *lemma* edge_density_nonneg
- \+ *lemma* edge_density_le_one
- \+ *lemma* edge_density_add_edge_density_compl
- \+ *lemma* edge_density_empty_left
- \+ *lemma* edge_density_empty_right
- \+ *lemma* swap_mem_interedges_iff
- \+ *lemma* mk_mem_interedges_comm
- \+ *lemma* card_interedges_comm
- \+ *lemma* edge_density_comm
- \+ *lemma* interedges_def
- \+ *lemma* edge_density_def
- \+ *lemma* card_interedges_div_card
- \+ *lemma* mem_interedges_iff
- \+ *lemma* mk_mem_interedges_iff
- \+ *lemma* interedges_empty_left
- \+ *lemma* interedges_mono
- \+ *lemma* interedges_disjoint_left
- \+ *lemma* interedges_disjoint_right
- \+ *lemma* interedges_bUnion_left
- \+ *lemma* interedges_bUnion_right
- \+ *lemma* interedges_bUnion
- \+ *lemma* card_interedges_add_card_interedges_compl
- \+ *lemma* edge_density_add_edge_density_compl
- \+ *lemma* card_interedges_le_mul
- \+ *lemma* edge_density_nonneg
- \+ *lemma* edge_density_le_one
- \+ *lemma* edge_density_empty_left
- \+ *lemma* edge_density_empty_right
- \+ *lemma* swap_mem_interedges_iff
- \+ *lemma* mk_mem_interedges_comm
- \+ *lemma* edge_density_comm
- \+ *def* interedges
- \+ *def* edge_density
- \+ *def* interedges
- \+ *def* edge_density



## [2022-03-24 14:49:21](https://github.com/leanprover-community/mathlib/commit/7302e11)
feat(algebra/module/torsion): define torsion submodules ([#12027](https://github.com/leanprover-community/mathlib/pull/12027))
This file defines the a-torsion and torsion submodules for a R-module M and gives some basic properties. (The ultimate goal I'm working on is to classify the finitely-generated modules over a PID).
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* exists_npow_eq_one_of_zpow_eq_one

created src/algebra/module/torsion.lean
- \+ *lemma* smul_torsion_by
- \+ *lemma* smul_coe_torsion_by
- \+ *lemma* mem_torsion_by_iff
- \+ *lemma* is_torsion_by_iff_torsion_by_eq_top
- \+ *lemma* torsion_by_is_torsion_by
- \+ *lemma* torsion_by_torsion_by_eq_top
- \+ *lemma* torsion_by.mk_smul
- \+ *lemma* mem_torsion'_iff
- \+ *lemma* mem_torsion_iff
- \+ *lemma* is_torsion'_iff_torsion'_eq_top
- \+ *lemma* torsion'_is_torsion'
- \+ *lemma* torsion'_torsion'_eq_top
- \+ *lemma* torsion_torsion_eq_top
- \+ *lemma* torsion_is_torsion
- \+ *lemma* coe_torsion_eq_annihilator_ne_bot
- \+ *lemma* no_zero_smul_divisors_iff_torsion_eq_bot
- \+ *lemma* torsion_eq_bot
- \+ *theorem* is_torsion_iff_is_torsion_nat
- \+ *theorem* is_torsion_iff_is_torsion_int
- \+ *def* torsion_by
- \+ *def* torsion'
- \+ *def* torsion
- \+ *def* is_torsion_by
- \+ *def* is_torsion'
- \+ *def* is_torsion



## [2022-03-24 13:01:54](https://github.com/leanprover-community/mathlib/commit/c7745b3)
chore(order/zorn): Review ([#12175](https://github.com/leanprover-community/mathlib/pull/12175))
Lemma renames
#### Estimated changes
modified src/analysis/convex/basic.lean

modified src/analysis/convex/cone.lean

modified src/analysis/inner_product_space/basic.lean

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise.insert
- \+ *lemma* pairwise.insert_of_symmetric

modified src/field_theory/adjoin.lean
- \+/\- *lemma* lifts.exists_max_two
- \+/\- *lemma* lifts.exists_max_three
- \+/\- *lemma* lifts.exists_upper_bound
- \+/\- *lemma* lifts.exists_max_two
- \+/\- *lemma* lifts.exists_max_three
- \+/\- *lemma* lifts.exists_upper_bound
- \+/\- *def* lifts.upper_bound_intermediate_field
- \+/\- *def* lifts.upper_bound_intermediate_field

modified src/field_theory/is_alg_closed/basic.lean

modified src/group_theory/sylow.lean

modified src/linear_algebra/linear_independent.lean

modified src/measure_theory/covering/vitali.lean

modified src/order/compactly_generated.lean

modified src/order/extension.lean

modified src/order/filter/ultrafilter.lean

modified src/order/zorn.lean
- \+ *lemma* is_chain_empty
- \+ *lemma* set.subsingleton.is_chain
- \+ *lemma* is_chain.mono
- \+ *lemma* is_chain.total
- \+ *lemma* is_chain.symm
- \+ *lemma* is_chain_of_trichotomous
- \+ *lemma* is_chain.insert
- \+ *lemma* is_chain_univ_iff
- \+ *lemma* is_chain.image
- \+ *lemma* is_chain.directed_on
- \+ *lemma* is_chain.directed
- \+ *lemma* is_max_chain.is_chain
- \+ *lemma* is_max_chain.not_super_chain
- \+/\- *lemma* succ_spec
- \+ *lemma* is_chain.succ
- \+ *lemma* is_chain.super_chain_succ_chain
- \+/\- *lemma* succ_increasing
- \+/\- *lemma* chain_closure_empty
- \+ *lemma* chain_closure_max_chain
- \+/\- *lemma* chain_closure_total
- \+ *lemma* chain_closure.succ_fixpoint
- \+ *lemma* chain_closure.succ_fixpoint_iff
- \+ *lemma* chain_closure.is_chain
- \+ *lemma* max_chain_spec
- \+ *lemma* exists_maximal_of_chains_bounded
- \+ *lemma* zorn_partial_order
- \+ *lemma* zorn_nonempty_partial_order
- \+ *lemma* zorn_partial_order₀
- \+ *lemma* zorn_nonempty_partial_order₀
- \+ *lemma* zorn_subset
- \+ *lemma* zorn_subset_nonempty
- \+ *lemma* zorn_superset
- \+ *lemma* zorn_superset_nonempty
- \+ *lemma* is_chain.exists_max_chain
- \- *lemma* chain.total_of_refl
- \- *lemma* chain.mono
- \- *lemma* chain_of_trichotomous
- \- *lemma* chain_univ_iff
- \- *lemma* chain.directed_on
- \- *lemma* chain_insert
- \+/\- *lemma* succ_spec
- \- *lemma* chain_succ
- \- *lemma* super_of_not_max
- \+/\- *lemma* succ_increasing
- \+/\- *lemma* chain_closure_empty
- \- *lemma* chain_closure_closure
- \+/\- *lemma* chain_closure_total
- \- *lemma* chain_closure_succ_fixpoint
- \- *lemma* chain_closure_succ_fixpoint_iff
- \- *lemma* chain_chain_closure
- \- *lemma* chain_empty
- \- *lemma* _root_.set.subsingleton.chain
- \- *lemma* chain.symm
- \- *lemma* chain.total
- \- *lemma* chain.image
- \- *lemma* directed_of_chain
- \- *theorem* max_chain_spec
- \- *theorem* exists_maximal_of_chains_bounded
- \- *theorem* zorn_partial_order
- \- *theorem* zorn_nonempty_partial_order
- \- *theorem* zorn_partial_order₀
- \- *theorem* zorn_nonempty_partial_order₀
- \- *theorem* zorn_subset
- \- *theorem* zorn_subset_nonempty
- \- *theorem* zorn_superset
- \- *theorem* zorn_superset_nonempty
- \- *theorem* chain.max_chain_of_chain
- \+ *def* is_chain
- \+/\- *def* super_chain
- \+/\- *def* is_max_chain
- \+/\- *def* succ_chain
- \+/\- *def* max_chain
- \- *def* chain
- \+/\- *def* super_chain
- \+/\- *def* is_max_chain
- \+/\- *def* succ_chain
- \+/\- *def* max_chain

modified src/ring_theory/algebraic_independent.lean

modified src/ring_theory/ideal/operations.lean

modified src/set_theory/schroeder_bernstein.lean

modified src/topology/algebra/semigroup.lean

modified src/topology/shrinking_lemma.lean
- \+/\- *lemma* apply_eq_of_chain
- \+/\- *lemma* find_apply_of_mem
- \+/\- *lemma* le_chain_Sup
- \+/\- *lemma* apply_eq_of_chain
- \+/\- *lemma* find_apply_of_mem
- \+/\- *lemma* le_chain_Sup
- \+/\- *def* chain_Sup
- \+/\- *def* chain_Sup

modified src/topology/subset_properties.lean



## [2022-03-24 12:01:35](https://github.com/leanprover-community/mathlib/commit/7c48d65)
feat(topology/algebra/group): define `has_continuous_inv` and `has_continuous_neg` type classes ([#12748](https://github.com/leanprover-community/mathlib/pull/12748))
This creates the `has_continuous_inv` and `has_continuous_neg` type classes. The `has_continuous_neg` class will be helpful for generalizing `topological_ring` to the setting of `non_unital_non_assoc_semiring`s (see [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity)). In addition, `ennreal` can have a `has_continuous_inv` instance.
#### Estimated changes
modified src/topology/algebra/field.lean

modified src/topology/algebra/group.lean
- \+ *lemma* is_closed_set_of_map_inv
- \+/\- *lemma* is_compact.inv
- \+ *lemma* has_continuous_inv_Inf
- \+ *lemma* has_continuous_inv_infi
- \+ *lemma* has_continuous_inv_inf
- \+ *lemma* topological_group.continuous_conj_prod
- \+/\- *lemma* topological_group.continuous_conj
- \+ *lemma* topological_group.continuous_conj'
- \+/\- *lemma* topological_group.continuous_conj
- \+/\- *lemma* is_compact.inv

modified src/topology/continuous_function/algebra.lean



## [2022-03-24 10:12:39](https://github.com/leanprover-community/mathlib/commit/eabc619)
feat(ring_theory/polynomial): mv_polynomial over UFD is UFD ([#12866](https://github.com/leanprover-community/mathlib/pull/12866))
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/algebra/associated.lean
- \+ *lemma* comap_prime
- \+ *lemma* mul_equiv.prime_iff

modified src/algebra/divisibility.lean
- \+ *lemma* map_dvd
- \+/\- *lemma* mul_hom.map_dvd
- \+/\- *lemma* monoid_hom.map_dvd
- \+/\- *lemma* mul_hom.map_dvd
- \+/\- *lemma* monoid_hom.map_dvd

modified src/algebra/ring/basic.lean
- \+/\- *lemma* ring_hom.map_dvd
- \+/\- *lemma* ring_hom.map_dvd

modified src/data/mv_polynomial/rename.lean
- \+ *lemma* kill_compl_comp_rename
- \+ *lemma* kill_compl_rename_app
- \+ *lemma* exists_finset_rename₂
- \+ *def* kill_compl

modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* prime_C_iff
- \+ *lemma* prime_C_iff
- \+ *lemma* prime_rename_iff

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* mul_equiv.unique_factorization_monoid
- \+ *lemma* mul_equiv.unique_factorization_monoid_iff



## [2022-03-24 10:12:38](https://github.com/leanprover-community/mathlib/commit/db76064)
feat(*): facts about degrees/multiplicites of derivatives ([#12856](https://github.com/leanprover-community/mathlib/pull/12856))
For `t` an `n`th repeated root of `p`, we prove that it is an `n-1`th repeated root of `p'` (and tidy the section around this). We also sharpen the theorem stating that `deg p' < deg p`.
#### Estimated changes
modified src/data/polynomial/derivative.lean
- \+ *lemma* derivative_of_nat_degree_zero
- \+/\- *theorem* nat_degree_derivative_lt
- \+/\- *theorem* nat_degree_derivative_lt

modified src/data/polynomial/field_division.lean
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+ *lemma* derivative_root_multiplicity_of_root
- \+ *lemma* root_multiplicity_sub_one_le_derivative_root_multiplicity
- \+/\- *lemma* roots_normalize
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize

modified src/field_theory/separable.lean



## [2022-03-24 10:12:37](https://github.com/leanprover-community/mathlib/commit/355645e)
chore(data/polynomial/*): delete, rename and move lemmas ([#12852](https://github.com/leanprover-community/mathlib/pull/12852))
- Replace `eval_eq_finset_sum` and `eval_eq_finset_sum'` with `eval_eq_sum_range` and `eval_eq_sum_range'` which are consistent with `eval₂_eq_sum_range`, `eval₂_eq_sum_range'` `eval_eq_finset_sum`, `eval_eq_finset_sum'`. Notice that the type of `eval_eq_sum_range'` is different, but this lemma has not been used anywhere in mathlib.
- Move the lemma `C_eq_int_cast` from `data/polynomial/degree/definitions.lean` to `data/polynomial/basic.lean`. `C_eq_nat_cast` was already here.
#### Estimated changes
modified src/analysis/special_functions/polynomials.lean

modified src/data/polynomial/algebra_map.lean

modified src/data/polynomial/basic.lean
- \+ *lemma* C_eq_int_cast

modified src/data/polynomial/degree/definitions.lean
- \- *lemma* C_eq_int_cast

modified src/data/polynomial/eval.lean
- \+ *lemma* eval_eq_sum_range
- \+ *lemma* eval_eq_sum_range'
- \- *lemma* eval_eq_finset_sum
- \- *lemma* eval_eq_finset_sum'

modified src/data/polynomial/mirror.lean

modified src/ring_theory/polynomial/eisenstein.lean



## [2022-03-24 10:12:36](https://github.com/leanprover-community/mathlib/commit/c1fb0ed)
feat(algebra/associated): generalize nat.prime_mul_iff ([#12850](https://github.com/leanprover-community/mathlib/pull/12850))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* irreducible_units_mul
- \+ *lemma* irreducible_is_unit_mul
- \+ *lemma* irreducible_mul_units
- \+ *lemma* irreducible_mul_is_unit
- \+ *lemma* irreducible_mul_iff

modified src/data/nat/prime.lean



## [2022-03-24 10:12:35](https://github.com/leanprover-community/mathlib/commit/a5a0d23)
feat(data/list/basic): nth_le+filter lemmas ([#12836](https://github.com/leanprover-community/mathlib/pull/12836))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* nth_le_cons_aux
- \+ *lemma* nth_le_cons
- \+ *lemma* filter_singleton



## [2022-03-24 10:12:34](https://github.com/leanprover-community/mathlib/commit/892e611)
feat(model_theory/*): Facts about countability of first-order structures ([#12819](https://github.com/leanprover-community/mathlib/pull/12819))
Shows that in a countable language, a structure is countably generated if and only if it is countable.
#### Estimated changes
modified src/data/equiv/encodable/basic.lean

modified src/model_theory/basic.lean
- \+ *lemma* card_le_omega
- \+ *lemma* card_functions_le_omega
- \+ *lemma* card_eq_card_functions_add_card_relations
- \+ *lemma* encodable.countable
- \+ *lemma* encodable.countable_functions
- \+ *def* card

modified src/model_theory/finitely_generated.lean
- \+ *lemma* cg_iff_countable
- \+/\- *theorem* cg_closure
- \+ *theorem* cg_iff_countable
- \+/\- *theorem* cg_closure

modified src/model_theory/substructures.lean
- \+ *lemma* _root_.set.countable.substructure_closure

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* card_le_omega



## [2022-03-24 10:12:32](https://github.com/leanprover-community/mathlib/commit/e6c6f00)
feat(number_theory/arithmetic_function): The moebius function is multiplicative ([#12796](https://github.com/leanprover-community/mathlib/pull/12796))
A fundamental property of the moebius function is that it is
multiplicative, which allows many facts about Euler products to be
expressed
#### Estimated changes
modified src/algebra/squarefree.lean
- \+ *lemma* squarefree.ne_zero
- \+ *lemma* squarefree.of_mul_left
- \+ *lemma* squarefree.of_mul_right
- \+ *lemma* squarefree_mul

modified src/number_theory/arithmetic_function.lean
- \+ *lemma* iff_ne_zero
- \+ *lemma* is_multiplicative_moebius



## [2022-03-24 10:12:31](https://github.com/leanprover-community/mathlib/commit/0faebd2)
chore(fintype/card_embedding): generalize instances ([#12775](https://github.com/leanprover-community/mathlib/pull/12775))
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_compl_set
- \+ *lemma* card_range
- \+ *theorem* to_finset_compl

modified src/data/fintype/card_embedding.lean
- \+/\- *lemma* card_embedding_eq_of_unique
- \+/\- *lemma* card_embedding_eq_of_infinite
- \+/\- *lemma* card_embedding_eq_of_unique
- \+/\- *lemma* card_embedding_eq_of_infinite
- \+/\- *theorem* card_embedding_eq
- \+/\- *theorem* card_embedding_eq

modified src/data/set/finite.lean
- \- *lemma* to_finset_compl

modified src/logic/embedding.lean
- \+ *def* option_embedding_equiv



## [2022-03-24 10:12:30](https://github.com/leanprover-community/mathlib/commit/0427430)
feat(number_theory/function_field): add completion with respect to place at infinity ([#12715](https://github.com/leanprover-community/mathlib/pull/12715))
#### Estimated changes
modified src/number_theory/function_field.lean
- \+ *lemma* infty_valued_Fqt.def
- \+ *lemma* topological_division_ring
- \+ *lemma* uniform_add_group
- \+ *lemma* completable_top_field
- \+ *lemma* separated_space
- \+ *lemma* valued_Fqt_infty.def
- \+ *def* infty_valued_Fqt
- \+ *def* topological_space
- \+ *def* uniform_space
- \+ *def* Fqt_infty



## [2022-03-24 09:09:50](https://github.com/leanprover-community/mathlib/commit/ca93096)
feat(topology/nhds_set): add `has_basis_nhds_set` ([#12908](https://github.com/leanprover-community/mathlib/pull/12908))
Also add `nhds_set_union`.
#### Estimated changes
modified src/topology/nhds_set.lean
- \+ *lemma* has_basis_nhds_set
- \+ *lemma* nhds_set_union



## [2022-03-24 07:09:35](https://github.com/leanprover-community/mathlib/commit/399ce38)
feat(measure_theory/integral): continuous functions with exponential decay are integrable ([#12539](https://github.com/leanprover-community/mathlib/pull/12539))
#### Estimated changes
created src/measure_theory/integral/exp_decay.lean
- \+ *lemma* integral_exp_neg_le
- \+ *lemma* exp_neg_integrable_on_Ioi
- \+ *lemma* integrable_of_is_O_exp_neg



## [2022-03-24 05:18:39](https://github.com/leanprover-community/mathlib/commit/df34816)
feat(ring_theory/principal_ideal_domain): add some irreducible lemmas ([#12903](https://github.com/leanprover-community/mathlib/pull/12903))
#### Estimated changes
modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* irreducible.dvd_iff_not_coprime
- \+ *theorem* irreducible.coprime_pow_of_not_dvd
- \+ *theorem* irreducible.coprime_or_dvd



## [2022-03-24 05:18:38](https://github.com/leanprover-community/mathlib/commit/a978115)
refactor(category_theory/abelian): trivial generalisations ([#12897](https://github.com/leanprover-community/mathlib/pull/12897))
Trivial generalisations of some facts in `category_theory/abelian/non_preadditive.lean`.
They are true more generally, and this refactor will make it easier to do some other clean-up I'd like to perform on abelian categories.
#### Estimated changes
modified src/category_theory/abelian/basic.lean
- \- *lemma* mono_of_zero_kernel
- \- *lemma* epi_of_zero_cokernel

modified src/category_theory/abelian/non_preadditive.lean
- \- *lemma* pullback_of_mono
- \- *lemma* pushout_of_epi
- \- *lemma* has_limit_parallel_pair
- \- *lemma* has_colimit_parallel_pair
- \- *lemma* mono_of_zero_kernel
- \- *lemma* epi_of_zero_cokernel
- \- *lemma* mono_of_cancel_zero
- \- *lemma* epi_of_zero_cancel
- \- *def* zero_kernel_of_cancel_zero
- \- *def* zero_cokernel_of_zero_cancel

modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* zero_kernel_of_cancel_zero
- \+ *def* zero_cokernel_of_zero_cancel

renamed src/category_theory/limits/shapes/normal_mono.lean to src/category_theory/limits/shapes/normal_mono/basic.lean

created src/category_theory/limits/shapes/normal_mono/equalizers.lean
- \+ *lemma* pullback_of_mono
- \+ *lemma* has_limit_parallel_pair
- \+ *lemma* epi_of_zero_cokernel
- \+ *lemma* epi_of_zero_cancel
- \+ *lemma* pushout_of_epi
- \+ *lemma* has_colimit_parallel_pair
- \+ *lemma* mono_of_zero_kernel
- \+ *lemma* mono_of_cancel_zero



## [2022-03-24 05:18:37](https://github.com/leanprover-community/mathlib/commit/d4e27d0)
chore(topology/separation): move a lemma, golf ([#12896](https://github.com/leanprover-community/mathlib/pull/12896))
* move `t0_space_of_injective_of_continuous` up;
* add `embedding.t0_space`, use it for `subtype.t0_space`.
#### Estimated changes
modified src/topology/separation.lean
- \+/\- *lemma* t0_space_of_injective_of_continuous
- \+/\- *lemma* t0_space_of_injective_of_continuous



## [2022-03-24 05:18:35](https://github.com/leanprover-community/mathlib/commit/e968b6d)
feat(topology/continuous_function/bounded): add `bounded_continuous_function.tendsto_iff_tendsto_uniformly` ([#12894](https://github.com/leanprover-community/mathlib/pull/12894))
This establishes that convergence in the metric on bounded continuous functions is equivalent to uniform convergence of the respective functions.
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *lemma* tendsto_iff_tendsto_uniformly



## [2022-03-24 05:18:34](https://github.com/leanprover-community/mathlib/commit/a370cf0)
chore(data/set/intervals): golf, rename ([#12893](https://github.com/leanprover-community/mathlib/pull/12893))
* rename `set.mem_Ioo_or_eq_endpoints_of_mem_Icc` →
  `set.eq_endpoints_or_mem_Ioo_of_mem_Icc`;
* rename `set.mem_Ioo_or_eq_left_of_mem_Ico` →
  `set.eq_left_or_mem_Ioo_of_mem_Ico`;
* rename `set.mem_Ioo_or_eq_right_of_mem_Ioc` →
  `set.eq_right_or_mem_Ioo_of_mem_Ioc`;
* golf the proofs of these lemmas.
The new names better reflect the order of terms in `or`.
#### Estimated changes
modified src/data/set/intervals/basic.lean
- \+ *lemma* eq_left_or_mem_Ioo_of_mem_Ico
- \+ *lemma* eq_right_or_mem_Ioo_of_mem_Ioc
- \+ *lemma* eq_endpoints_or_mem_Ioo_of_mem_Icc
- \- *lemma* mem_Ioo_or_eq_endpoints_of_mem_Icc
- \- *lemma* mem_Ioo_or_eq_left_of_mem_Ico
- \- *lemma* mem_Ioo_or_eq_right_of_mem_Ioc

modified src/data/set/intervals/surj_on.lean

modified src/topology/algebra/order/extend_from.lean



## [2022-03-24 05:18:33](https://github.com/leanprover-community/mathlib/commit/5ef365a)
feat(topology/separation): generalize tendsto_const_nhds_iff to t1_space ([#12883](https://github.com/leanprover-community/mathlib/pull/12883))
I noticed this when working on the sphere eversion project
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean

modified src/order/filter/basic.lean
- \+ *lemma* map_const

modified src/topology/separation.lean
- \+ *lemma* pure_le_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff
- \+/\- *lemma* tendsto_const_nhds_iff
- \+/\- *lemma* nhds_le_nhds_iff
- \+/\- *lemma* tendsto_const_nhds_iff



## [2022-03-24 05:18:32](https://github.com/leanprover-community/mathlib/commit/6696bdd)
docs(data/set/pairwise): Explain preference for `s.pairwise_disjoint id` ([#12878](https://github.com/leanprover-community/mathlib/pull/12878))
... over `s.pairwise disjoint`.
#### Estimated changes
modified src/data/set/pairwise.lean



## [2022-03-24 05:18:31](https://github.com/leanprover-community/mathlib/commit/30449be)
feat(data/complex/is_R_or_C): generalize `is_R_or_C.proper_space_span_singleton` to all finite dimensional submodules ([#12877](https://github.com/leanprover-community/mathlib/pull/12877))
Also goes on to show that finite supremums of finite_dimensional submodules are finite-dimensional.
#### Estimated changes
modified src/data/complex/is_R_or_C.lean

modified src/linear_algebra/finite_dimensional.lean



## [2022-03-24 05:18:30](https://github.com/leanprover-community/mathlib/commit/debdd90)
feat(tactic/ext): support rintro patterns in `ext` ([#12875](https://github.com/leanprover-community/mathlib/pull/12875))
The change is actually quite simple, since `rintro_pat*` has approximately the same type as `rcases_pat*`.
#### Estimated changes
modified src/tactic/congr.lean

modified src/tactic/ext.lean

modified test/ext.lean



## [2022-03-24 05:18:29](https://github.com/leanprover-community/mathlib/commit/8e50164)
chore(data/int/basic): remove some `eq.mpr`s from `int.induction_on'` ([#12873](https://github.com/leanprover-community/mathlib/pull/12873))
#### Estimated changes
modified src/data/int/basic.lean



## [2022-03-24 05:18:27](https://github.com/leanprover-community/mathlib/commit/ae69578)
fix(ring_theory/algebraic): Make `is_transcendental_of_subsingleton` fully general ([#12870](https://github.com/leanprover-community/mathlib/pull/12870))
I mistyped a single letter.
#### Estimated changes
modified src/ring_theory/algebraic.lean
- \+/\- *lemma* is_transcendental_of_subsingleton
- \+/\- *lemma* is_transcendental_of_subsingleton



## [2022-03-24 05:18:26](https://github.com/leanprover-community/mathlib/commit/706a824)
feat(data/{nat, real}/sqrt): Some simple facts about square roots ([#12851](https://github.com/leanprover-community/mathlib/pull/12851))
Prove that sqrt 1 = 1 in the natural numbers and an order relationship between real and natural square roots.
#### Estimated changes
modified src/data/nat/sqrt.lean
- \+ *lemma* sqrt_one

modified src/data/real/sqrt.lean
- \+ *lemma* nat_sqrt_le_real_sqrt
- \+ *lemma* real_sqrt_le_nat_sqrt_succ



## [2022-03-24 05:18:25](https://github.com/leanprover-community/mathlib/commit/ec434b7)
feat(group_theory/order_of_element): finite orderness is closed under mul ([#12750](https://github.com/leanprover-community/mathlib/pull/12750))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_pos_iff
- \+ *lemma* commute.is_of_fin_order_mul
- \+ *lemma* is_of_fin_order.inv
- \+ *lemma* is_of_fin_order.mul
- \- *lemma* is_of_fin_order_inv



## [2022-03-24 05:18:24](https://github.com/leanprover-community/mathlib/commit/c705d41)
feat(analysis/locally_convex): characterize the natural bornology in terms of seminorms ([#12721](https://github.com/leanprover-community/mathlib/pull/12721))
Add four lemmas:
* `is_vonN_bounded_basis_iff`: it suffices to check boundedness for a basis
* `seminorm_family.has_basis`: the basis sets form a basis of the topology
* `is_bounded_iff_finset_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for all finite suprema of seminorms
* `is_bounded_iff_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for each seminorm
Also make the set argument in `seminorm_family.basis_sets_iff` implicit.
#### Estimated changes
modified src/analysis/locally_convex/bounded.lean
- \+ *lemma* _root_.filter.has_basis.is_vonN_bounded_basis_iff

modified src/analysis/locally_convex/with_seminorms.lean
- \+/\- *lemma* basis_sets_iff
- \+ *lemma* seminorm_family.has_basis
- \+ *lemma* bornology.is_vonN_bounded_iff_finset_seminorm_bounded
- \+ *lemma* bornology.is_vonN_bounded_iff_seminorm_bounded
- \+/\- *lemma* basis_sets_iff



## [2022-03-24 05:18:23](https://github.com/leanprover-community/mathlib/commit/cbd1e98)
chore(algebra/category/*): simp lemmas for of_hom ([#12638](https://github.com/leanprover-community/mathlib/pull/12638))
#### Estimated changes
modified src/algebra/category/Algebra/basic.lean
- \+ *lemma* of_hom_apply

modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* of_hom_apply
- \+ *lemma* of_hom_apply
- \+ *lemma* of_hom_apply
- \+ *lemma* of_hom_apply

modified src/algebra/category/Group/basic.lean
- \+ *lemma* of_hom_apply
- \+ *lemma* of_hom_apply

modified src/algebra/category/Module/basic.lean
- \+ *lemma* of_hom_apply

modified src/algebra/category/Mon/basic.lean
- \+ *lemma* of_hom_apply

modified src/algebra/category/Semigroup/basic.lean
- \+ *lemma* of_hom_apply
- \+ *lemma* of_hom_apply



## [2022-03-24 04:46:31](https://github.com/leanprover-community/mathlib/commit/7967128)
feat(data/complex/basic): `#ℂ = 𝔠` ([#12871](https://github.com/leanprover-community/mathlib/pull/12871))
#### Estimated changes
created src/data/complex/cardinality.lean
- \+ *lemma* mk_univ_complex
- \+ *lemma* not_countable_complex
- \+ *theorem* mk_complex



## [2022-03-23 23:02:08](https://github.com/leanprover-community/mathlib/commit/584ae9d)
chore(data/{lists,multiset}/*): More dot notation ([#12876](https://github.com/leanprover-community/mathlib/pull/12876))
Rename many `list` and `multiset` lemmas to make them eligible to dot notation. Also add a few aliases to `↔` lemmas for even more dot notation.
Renames
#### Estimated changes
modified src/algebra/squarefree.lean

modified src/combinatorics/simple_graph/connectivity.lean

modified src/data/equiv/list.lean

modified src/data/fin_enum.lean

modified src/data/finset/basic.lean
- \+ *lemma* insert_def
- \+ *lemma* not_mem_erase
- \+ *lemma* image_val_of_inj_on
- \- *theorem* insert_def
- \- *theorem* not_mem_erase
- \- *theorem* image_val_of_inj_on
- \+/\- *def* erase
- \+/\- *def* filter
- \+/\- *def* map
- \+/\- *def* erase
- \+/\- *def* filter
- \+/\- *def* map

modified src/data/finset/fin.lean

modified src/data/finset/noncomm_prod.lean

modified src/data/finset/option.lean

modified src/data/finset/pi.lean

modified src/data/finset/powerset.lean

modified src/data/finset/prod.lean

modified src/data/finset/sigma.lean

modified src/data/fintype/basic.lean

modified src/data/hash_map.lean

modified src/data/list/alist.lean
- \+ *lemma* keys_erase
- \- *theorem* keys_erase
- \+/\- *def* erase
- \+/\- *def* erase

modified src/data/list/cycle.lean

modified src/data/list/nat_antidiagonal.lean

modified src/data/list/nodup.lean
- \+ *lemma* nodup_singleton
- \+ *lemma* nodup.of_cons
- \+ *lemma* nodup.not_mem
- \+ *lemma* not_nodup_cons_of_mem
- \+ *lemma* nodup.of_append_left
- \+ *lemma* nodup.of_append_right
- \+ *lemma* nodup.append
- \+ *lemma* nodup.of_map
- \+ *lemma* nodup.map_on
- \+ *lemma* nodup.pmap
- \+ *lemma* nodup.filter
- \+ *lemma* nodup.erase_eq_filter
- \+ *lemma* nodup.erase
- \+ *lemma* nodup.diff
- \+ *lemma* nodup.mem_erase_iff
- \+ *lemma* nodup.not_mem_erase
- \+ *lemma* nodup.sigma
- \+ *lemma* nodup.insert
- \+ *lemma* nodup.union
- \+ *lemma* nodup.inter
- \+/\- *lemma* nodup_sublists_len
- \+ *lemma* nodup.diff_eq_filter
- \+ *lemma* nodup.mem_diff_iff
- \+/\- *lemma* nodup_sublists_len
- \- *lemma* diff_eq_filter_of_nodup
- \- *lemma* mem_diff_iff_of_nodup
- \- *lemma* nodup_update_nth
- \- *theorem* nodup_cons_of_nodup
- \- *theorem* nodup_singleton
- \- *theorem* nodup_of_nodup_cons
- \- *theorem* not_mem_of_nodup_cons
- \- *theorem* not_nodup_cons_of_mem
- \- *theorem* nodup_of_sublist
- \- *theorem* nodup_of_nodup_append_left
- \- *theorem* nodup_of_nodup_append_right
- \- *theorem* nodup_append_of_nodup
- \- *theorem* nodup_of_nodup_map
- \- *theorem* nodup_map_on
- \- *theorem* nodup_map
- \- *theorem* nodup_pmap
- \- *theorem* nodup_filter
- \- *theorem* nodup_erase_eq_filter
- \- *theorem* nodup_erase_of_nodup
- \- *theorem* nodup_diff
- \- *theorem* mem_erase_iff_of_nodup
- \- *theorem* mem_erase_of_nodup
- \- *theorem* nodup_product
- \- *theorem* nodup_sigma
- \- *theorem* nodup_filter_map
- \- *theorem* nodup_concat
- \- *theorem* nodup_insert
- \- *theorem* nodup_union
- \- *theorem* nodup_inter_of_nodup

modified src/data/list/pairwise.lean
- \+ *lemma* rel_of_pairwise_cons
- \+ *lemma* pairwise.of_cons
- \+ *lemma* pairwise.imp
- \+ *lemma* pairwise_and_iff
- \+ *lemma* pairwise.and
- \+ *lemma* pairwise.imp₂
- \+ *lemma* pairwise.forall_of_forall
- \+ *lemma* pairwise.forall
- \+/\- *lemma* pairwise.set_pairwise
- \+ *lemma* pairwise.of_map
- \+ *lemma* pairwise.map
- \+ *lemma* pairwise.filter
- \+ *lemma* pw_filter_idempotent
- \- *lemma* forall_of_pairwise
- \+/\- *lemma* pairwise.set_pairwise
- \+ *theorem* pairwise.filter_map
- \+ *theorem* pairwise.sublists'
- \- *theorem* rel_of_pairwise_cons
- \- *theorem* pairwise_of_pairwise_cons
- \- *theorem* pairwise.imp
- \- *theorem* pairwise.and
- \- *theorem* pairwise.imp₂
- \- *theorem* pairwise_of_sublist
- \- *theorem* forall_of_forall_of_pairwise
- \- *theorem* pairwise_of_pairwise_map
- \- *theorem* pairwise_map_of_pairwise
- \- *theorem* pairwise_filter_map_of_pairwise
- \- *theorem* pairwise_filter_of_pairwise
- \- *theorem* pairwise_sublists'
- \- *theorem* pw_filter_idempotent

modified src/data/list/perm.lean
- \- *theorem* subperm_of_subset_nodup

modified src/data/list/range.lean

modified src/data/list/sigma.lean
- \+ *lemma* nodupkeys.kerase
- \+ *lemma* nodupkeys.kunion
- \+ *theorem* nodupkeys.sublist
- \- *theorem* nodupkeys_of_sublist
- \- *theorem* nodup_of_nodupkeys
- \- *theorem* kerase_nodupkeys
- \- *theorem* kunion_nodupkeys

modified src/data/list/sort.lean
- \+ *lemma* sorted.of_cons
- \- *theorem* sorted_of_sorted_cons

modified src/data/multiset/dedup.lean

modified src/data/multiset/finset_ops.lean
- \+ *lemma* nodup.ndinsert
- \+ *lemma* nodup.ndunion
- \+ *lemma* nodup.ndinter
- \- *theorem* nodup_ndinsert
- \- *theorem* nodup_ndunion
- \- *theorem* nodup_ndinter

modified src/data/multiset/locally_finite.lean

modified src/data/multiset/nodup.lean
- \+ *lemma* nodup.cons
- \+ *lemma* nodup.of_cons
- \+ *lemma* pairwise.forall
- \+ *lemma* nodup.add_iff
- \+ *lemma* nodup.of_map
- \+ *lemma* nodup.map_on
- \+ *lemma* nodup.map
- \+ *lemma* nodup.filter
- \+ *lemma* nodup.pmap
- \+ *lemma* nodup.erase_eq_filter
- \+ *lemma* nodup.erase
- \+ *lemma* nodup.mem_erase_iff
- \+ *lemma* nodup.not_mem_erase
- \+ *lemma* nodup.inter_left
- \+ *lemma* nodup.inter_right
- \+ *lemma* nodup.ext
- \- *lemma* pairwise_of_nodup
- \- *lemma* forall_of_pairwise
- \+ *theorem* nodup.not_mem
- \- *theorem* nodup_cons_of_nodup
- \- *theorem* nodup_of_nodup_cons
- \- *theorem* not_mem_of_nodup_cons
- \- *theorem* nodup_add_of_nodup
- \- *theorem* nodup_of_nodup_map
- \- *theorem* nodup_map_on
- \- *theorem* nodup_map
- \- *theorem* nodup_filter
- \- *theorem* nodup_pmap
- \- *theorem* nodup_erase_eq_filter
- \- *theorem* nodup_erase_of_nodup
- \- *theorem* mem_erase_iff_of_nodup
- \- *theorem* mem_erase_of_nodup
- \- *theorem* nodup_product
- \- *theorem* nodup_sigma
- \- *theorem* nodup_filter_map
- \- *theorem* nodup_inter_left
- \- *theorem* nodup_inter_right
- \- *theorem* nodup_powerset_len
- \- *theorem* nodup_ext

modified src/data/multiset/pi.lean
- \- *lemma* nodup_pi

modified src/data/multiset/sum.lean

modified src/data/set/finite.lean

modified src/data/tprod.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/list.lean

modified src/ring_theory/discriminant.lean

modified src/testing/slim_check/functions.lean



## [2022-03-23 21:13:19](https://github.com/leanprover-community/mathlib/commit/e620519)
feat(order/hom/*): more superclass instances for `order_iso_class` ([#12889](https://github.com/leanprover-community/mathlib/pull/12889))
 * Weaken hypotheses on `order_hom_class` and some subclasses
 * Add more instances deriving specific order hom classes from `order_iso_class`
#### Estimated changes
modified src/order/hom/basic.lean

modified src/order/hom/bounded.lean

modified src/order/hom/complete_lattice.lean

modified src/order/hom/lattice.lean



## [2022-03-23 21:13:18](https://github.com/leanprover-community/mathlib/commit/3b8d217)
refactor(order/upper_lower): Use `⨆` rather than `Sup` ([#12644](https://github.com/leanprover-community/mathlib/pull/12644))
Turn `Sup (coe '' S)` into  `⋃ s ∈ S, ↑s` and other similar changes. This greatly simplifies the proofs.
#### Estimated changes
modified src/order/complete_boolean_algebra.lean

modified src/order/complete_lattice.lean

modified src/order/upper_lower.lean
- \+ *lemma* carrier_eq_coe
- \+ *lemma* carrier_eq_coe
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂
- \+ *lemma* mem_compl_iff
- \+ *lemma* mem_compl_iff
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂

modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* supr₂
- \+ *lemma* infi₂
- \+/\- *lemma* Sup
- \+/\- *lemma* Inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+/\- *lemma* to_ideal_bot
- \+/\- *lemma* to_ideal_sup
- \+/\- *lemma* to_ideal_Sup
- \+ *lemma* to_ideal_supr
- \+/\- *lemma* to_ideal_infi
- \+ *lemma* to_ideal_supr₂
- \+ *lemma* to_ideal_infi₂
- \+/\- *lemma* eq_top_iff
- \+/\- *lemma* eq_bot_iff
- \+/\- *lemma* Inf
- \+/\- *lemma* Sup
- \+/\- *lemma* to_ideal_bot
- \+/\- *lemma* eq_bot_iff
- \+/\- *lemma* eq_top_iff
- \+/\- *lemma* to_ideal_infi
- \+/\- *lemma* to_ideal_sup
- \+/\- *lemma* to_ideal_Sup
- \- *lemma* coe_supr

modified src/ring_theory/graded_algebra/radical.lean



## [2022-03-23 20:36:51](https://github.com/leanprover-community/mathlib/commit/cd94287)
feat(category_theory/abelian): right derived functor in abelian category with enough injectives ([#12810](https://github.com/leanprover-community/mathlib/pull/12810))
This pr shows that in an abelian category with enough injectives, if a functor preserves finite limits, then the zeroth right derived functor is naturally isomorphic to itself.  Dual to [#12403](https://github.com/leanprover-community/mathlib/pull/12403) ↔️
#### Estimated changes
modified src/category_theory/abelian/right_derived.lean
- \+ *lemma* preserves_exact_of_preserves_finite_limits_of_mono
- \+ *lemma* exact_of_map_injective_resolution
- \+ *lemma* right_derived_zero_to_self_app_comp_inv
- \+ *lemma* right_derived_zero_to_self_app_inv_comp
- \+ *lemma* right_derived_zero_to_self_natural
- \+ *def* right_derived_zero_to_self_app
- \+ *def* right_derived_zero_to_self_app_inv
- \+ *def* right_derived_zero_to_self_app_iso
- \+ *def* right_derived_zero_iso_self



## [2022-03-23 20:36:49](https://github.com/leanprover-community/mathlib/commit/84a438e)
refactor(algebraic_geometry/*): rename structure sheaf to `Spec.structure_sheaf` ([#12785](https://github.com/leanprover-community/mathlib/pull/12785))
Following [this Zulip message](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rename.20.60structure_sheaf.60.20to.20.60Spec.2Estructure_sheaf.60/near/275649595), this pr renames `structure_sheaf` to `Spec.structure_sheaf`
#### Estimated changes
modified src/algebraic_geometry/AffineScheme.lean

modified src/algebraic_geometry/Gamma_Spec_adjunction.lean

modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/structure_sheaf.lean
- \+ *def* Spec.structure_sheaf
- \- *def* structure_sheaf



## [2022-03-23 12:35:46](https://github.com/leanprover-community/mathlib/commit/16fb8e2)
chore(model_theory/terms_and_formulas): `realize_to_prenex` ([#12884](https://github.com/leanprover-community/mathlib/pull/12884))
Proves that `phi.to_prenex` has the same realization in a nonempty structure as the original formula `phi` directly, rather than using `semantically_equivalent`.
#### Estimated changes
modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_to_prenex_imp_right
- \+ *lemma* realize_to_prenex_imp
- \+ *lemma* realize_to_prenex
- \- *lemma* imp_semantically_equivalent_to_prenex_imp_right
- \- *lemma* imp_semantically_equivalent_to_prenex_imp



## [2022-03-23 12:35:45](https://github.com/leanprover-community/mathlib/commit/64472d7)
feat(ring_theory/polynomial/basic): the isomorphism between `R[a]/I[a]` and `(R/I[X])/(f mod I)` for `a` a root of polynomial `f` and `I` and ideal of `R` ([#12646](https://github.com/leanprover-community/mathlib/pull/12646))
This PR defines the isomorphism between the ring `R[a]/I[a]` and the ring `(R/I[X])/(f mod I)` for `a` a root of the polynomial `f` with coefficients in `R` and `I` an ideal of `R`. This is useful for proving the Dedekind-Kummer Theorem.
#### Estimated changes
modified src/ring_theory/adjoin_root.lean
- \+ *lemma* quot_map_of_equiv_quot_map_C_map_span_mk_mk
- \+ *lemma* quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_mk
- \+ *lemma* polynomial.quot_quot_equiv_comm_mk_mk
- \+ *lemma* quot_adjoin_root_equiv_quot_polynomial_quot_mk_of
- \+ *def* quot_map_of_equiv_quot_map_C_map_span_mk
- \+ *def* quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk
- \+ *def* polynomial.quot_quot_equiv_comm
- \+ *def* quot_map_of_equiv

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* quotient_equiv_mk
- \+ *lemma* quotient_equiv_symm_mk



## [2022-03-23 10:41:04](https://github.com/leanprover-community/mathlib/commit/9126310)
chore(docs/references): Remove duplicate key ([#12901](https://github.com/leanprover-community/mathlib/pull/12901))
and clean up the rest while I'm at it.
#### Estimated changes
modified docs/references.bib



## [2022-03-23 10:41:02](https://github.com/leanprover-community/mathlib/commit/2308b53)
feat(model_theory/terms_and_formulas): Make `Theory.model` a class ([#12867](https://github.com/leanprover-community/mathlib/pull/12867))
Makes `Theory.model` a class
#### Estimated changes
modified src/model_theory/elementary_maps.lean

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* Theory.realize_sentence_of_mem
- \+/\- *lemma* Theory.model.mono
- \+/\- *lemma* models_formula_iff
- \+/\- *lemma* models_sentence_iff
- \+/\- *lemma* semantically_equivalent.refl
- \+/\- *lemma* semantically_equivalent.symm
- \+/\- *lemma* semantically_equivalent.trans
- \+/\- *lemma* Theory.model.mono
- \- *lemma* is_satisfiable.some_model_models
- \+/\- *lemma* models_formula_iff
- \+/\- *lemma* models_sentence_iff
- \+/\- *lemma* semantically_equivalent.refl
- \+/\- *lemma* semantically_equivalent.symm
- \+/\- *lemma* semantically_equivalent.trans
- \+/\- *def* models_bounded_formula
- \- *def* Theory.model
- \+/\- *def* models_bounded_formula

modified src/model_theory/ultraproducts.lean



## [2022-03-23 10:08:10](https://github.com/leanprover-community/mathlib/commit/92f2669)
feat(algebra/homology/quasi_iso): 2-out-of-3 property ([#12898](https://github.com/leanprover-community/mathlib/pull/12898))
#### Estimated changes
modified src/algebra/homology/quasi_iso.lean
- \+ *lemma* quasi_iso_of_comp_left
- \+ *lemma* quasi_iso_of_comp_right



## [2022-03-23 08:42:10](https://github.com/leanprover-community/mathlib/commit/11a365d)
feat(linear_algebra/matrix): add variants of the existing `det_units_conj` lemmas ([#12881](https://github.com/leanprover-community/mathlib/pull/12881))
#### Estimated changes
modified src/linear_algebra/determinant.lean
- \+ *lemma* det_conj_of_mul_eq_one
- \- *lemma* det_conj

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* coe_units_inv
- \+ *lemma* det_conj
- \+ *lemma* det_conj'

modified src/linear_algebra/matrix/zpow.lean
- \+ *lemma* coe_units_zpow
- \- *lemma* units.coe_inv''
- \- *lemma* units.coe_zpow



## [2022-03-23 00:37:13](https://github.com/leanprover-community/mathlib/commit/c60bfca)
chore(data/nat/prime): golf nat.dvd_prime_pow ([#12886](https://github.com/leanprover-community/mathlib/pull/12886))
#### Estimated changes
modified src/data/nat/prime.lean



## [2022-03-22 22:13:57](https://github.com/leanprover-community/mathlib/commit/d711d2a)
feat(set_theory/ordinal): Small iff cardinality less than `cardinal.univ` ([#12887](https://github.com/leanprover-community/mathlib/pull/12887))
Characterizes when a type is small in terms of its cardinality
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* small_iff_lift_mk_lt_univ

modified src/set_theory/ordinal_arithmetic.lean



## [2022-03-22 20:22:10](https://github.com/leanprover-community/mathlib/commit/3838b85)
feat(model_theory/*): Language equivalences ([#12837](https://github.com/leanprover-community/mathlib/pull/12837))
Defines equivalences between first-order languages
#### Estimated changes
modified src/model_theory/basic.lean
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \+ *lemma* comp_assoc
- \+ *lemma* sum_elim_comp_inl
- \+ *lemma* sum_elim_comp_inr
- \+ *lemma* sum_map_comp_inl
- \+ *lemma* sum_map_comp_inr
- \+ *lemma* Lhom.map_constants_comp_sum_inl
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \- *lemma* Lhom.map_constants_comp_with_constants
- \+ *theorem* sum_elim_inl_inr
- \+ *theorem* comp_sum_elim
- \+/\- *def* comp
- \+/\- *def* sum_map
- \+/\- *def* Lhom_with_constants
- \+ *def* Lequiv.add_empty_constants
- \+/\- *def* comp
- \- *def* sum_elim
- \+/\- *def* sum_map
- \+/\- *def* Lhom_with_constants
- \- *def* Lhom_trim_empty_constants

modified src/model_theory/definability.lean

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* id_on_term
- \+ *lemma* comp_on_term
- \+ *lemma* realize_on_term
- \+ *lemma* id_on_bounded_formula
- \+ *lemma* comp_on_bounded_formula
- \+ *lemma* on_bounded_formula_symm
- \+ *lemma* on_formula_apply
- \+ *lemma* on_formula_symm
- \+ *lemma* Lhom.set_of_realize_on_formula
- \- *lemma* Lhom.realize_on_term
- \+ *def* on_term
- \+ *def* Lequiv.on_term
- \+/\- *def* on_bounded_formula
- \+/\- *def* on_formula
- \+/\- *def* on_bounded_formula
- \+/\- *def* on_formula
- \+ *def* on_sentence
- \- *def* Lhom.on_term
- \+/\- *def* on_bounded_formula
- \+/\- *def* on_formula



## [2022-03-22 20:22:09](https://github.com/leanprover-community/mathlib/commit/f7905f0)
feat(order/concept): Concept lattices ([#12286](https://github.com/leanprover-community/mathlib/pull/12286))
Define `concept`, the type of concepts of a relation, and prove it forms a complete lattice.
#### Estimated changes
modified docs/references.bib

created src/order/concept.lean
- \+ *lemma* subset_intent_closure_iff_subset_extent_closure
- \+ *lemma* gc_intent_closure_extent_closure
- \+ *lemma* intent_closure_swap
- \+ *lemma* extent_closure_swap
- \+ *lemma* intent_closure_empty
- \+ *lemma* extent_closure_empty
- \+ *lemma* intent_closure_union
- \+ *lemma* extent_closure_union
- \+ *lemma* intent_closure_Union
- \+ *lemma* extent_closure_Union
- \+ *lemma* intent_closure_Union₂
- \+ *lemma* extent_closure_Union₂
- \+ *lemma* subset_extent_closure_intent_closure
- \+ *lemma* subset_intent_closure_extent_closure
- \+ *lemma* intent_closure_extent_closure_intent_closure
- \+ *lemma* extent_closure_intent_closure_extent_closure
- \+ *lemma* intent_closure_anti
- \+ *lemma* extent_closure_anti
- \+ *lemma* ext
- \+ *lemma* ext'
- \+ *lemma* fst_injective
- \+ *lemma* snd_injective
- \+ *lemma* fst_subset_fst_iff
- \+ *lemma* fst_ssubset_fst_iff
- \+ *lemma* snd_subset_snd_iff
- \+ *lemma* snd_ssubset_snd_iff
- \+ *lemma* strict_mono_fst
- \+ *lemma* strict_anti_snd
- \+ *lemma* top_fst
- \+ *lemma* top_snd
- \+ *lemma* bot_fst
- \+ *lemma* bot_snd
- \+ *lemma* sup_fst
- \+ *lemma* sup_snd
- \+ *lemma* inf_fst
- \+ *lemma* inf_snd
- \+ *lemma* Sup_fst
- \+ *lemma* Sup_snd
- \+ *lemma* Inf_fst
- \+ *lemma* Inf_snd
- \+ *lemma* swap_swap
- \+ *lemma* swap_le_swap_iff
- \+ *lemma* swap_lt_swap_iff
- \+ *def* intent_closure
- \+ *def* extent_closure
- \+ *def* swap
- \+ *def* swap_equiv



## [2022-03-22 20:22:08](https://github.com/leanprover-community/mathlib/commit/b226b4b)
feat(*): `has_repr` instances for `option`-like types ([#11282](https://github.com/leanprover-community/mathlib/pull/11282))
This provides the `has_repr` instance for `with_bot α`, `with_top α`, `with_zero α`, `with_one α`, `alexandroff α`.
#### Estimated changes
modified src/algebra/group/with_one.lean

modified src/order/bounded_order.lean

modified src/topology/alexandroff.lean



## [2022-03-22 19:50:36](https://github.com/leanprover-community/mathlib/commit/980185a)
feat(algebra/{group,module}/ulift): Missing `ulift` instances ([#12879](https://github.com/leanprover-community/mathlib/pull/12879))
Add a few missing algebraic instances for `ulift` and golf a few existing ones.
#### Estimated changes
modified src/algebra/group/ulift.lean

modified src/algebra/module/ulift.lean



## [2022-03-22 14:24:51](https://github.com/leanprover-community/mathlib/commit/6a55ba8)
feat(algebra/subalgebra/basic): Missing scalar instances ([#12874](https://github.com/leanprover-community/mathlib/pull/12874))
Add missing scalar instances for `submonoid`, `subsemiring`, `subring`, `subalgebra`.
#### Estimated changes
modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def



## [2022-03-22 14:24:49](https://github.com/leanprover-community/mathlib/commit/5215940)
feat(order/filter/basic): `filter` is a `coframe` ([#12872](https://github.com/leanprover-community/mathlib/pull/12872))
Provide the `coframe (filter α)` instance and remove now duplicated lemmas.
#### Estimated changes
modified src/order/complete_boolean_algebra.lean

modified src/order/filter/basic.lean
- \- *lemma* infi_sup_left
- \- *lemma* infi_sup_right
- \- *lemma* binfi_sup_right
- \- *lemma* binfi_sup_left



## [2022-03-22 14:24:48](https://github.com/leanprover-community/mathlib/commit/1f47016)
refactor(order/hom/complete_lattice): Fix the definition of `frame_hom` ([#12855](https://github.com/leanprover-community/mathlib/pull/12855))
I misread "preserves finite meet" as "preserves binary meet", meaning that currently a `frame_hom` does not have to preserve `⊤` (subtly, preserving arbitrary join does not imply that either). This fixes my mistake.
#### Estimated changes
modified src/order/hom/complete_lattice.lean
- \- *lemma* coe_bot
- \- *lemma* bot_apply
- \+/\- *def* to_lattice_hom
- \+ *def* to_Sup_hom
- \+/\- *def* to_lattice_hom
- \- *def* to_Inf_hom

modified src/topology/sets/opens.lean



## [2022-03-22 12:35:31](https://github.com/leanprover-community/mathlib/commit/d586195)
feat(data/finset/pointwise): Missing operations ([#12865](https://github.com/leanprover-community/mathlib/pull/12865))
Define `-s`, `s⁻¹`, `s - t`, `s / t`, `s +ᵥ t`, `s • t`, `s -ᵥ t`, `a • s`, `a +ᵥ s` for `s`, `t` finsets, `a` scalar. Provide a bare API following what is already there for `s + t`, `s * t`.
#### Estimated changes
modified src/data/finset/pointwise.lean
- \+ *lemma* inv_def
- \+ *lemma* image_inv
- \+ *lemma* mem_inv
- \+ *lemma* inv_mem_inv
- \+ *lemma* card_inv_le
- \+ *lemma* inv_empty
- \+ *lemma* inv_nonempty_iff
- \+ *lemma* inv_subset_inv
- \+ *lemma* inv_singleton
- \+ *lemma* coe_inv
- \+ *lemma* card_inv
- \+ *lemma* preimage_inv
- \+/\- *lemma* mul_card_le
- \+ *lemma* div_def
- \+ *lemma* image_div_prod
- \+ *lemma* mem_div
- \+ *lemma* coe_div
- \+ *lemma* div_mem_div
- \+ *lemma* div_card_le
- \+ *lemma* empty_div
- \+ *lemma* div_empty
- \+ *lemma* div_nonempty_iff
- \+ *lemma* div_subset_div
- \+ *lemma* div_singleton
- \+ *lemma* singleton_div
- \+ *lemma* singleton_div_singleton
- \+ *lemma* subset_div
- \+ *lemma* div_zero_subset
- \+ *lemma* zero_div_subset
- \+ *lemma* nonempty.div_zero
- \+ *lemma* nonempty.zero_div
- \+/\- *lemma* coe_pow
- \+ *lemma* coe_zpow
- \+ *lemma* coe_zpow'
- \+ *lemma* smul_def
- \+ *lemma* image_smul_product
- \+ *lemma* mem_smul
- \+ *lemma* coe_smul
- \+ *lemma* smul_mem_smul
- \+ *lemma* smul_card_le
- \+ *lemma* empty_smul
- \+ *lemma* smul_empty
- \+ *lemma* smul_nonempty_iff
- \+ *lemma* nonempty.smul
- \+ *lemma* smul_subset_smul
- \+ *lemma* smul_singleton
- \+ *lemma* singleton_smul
- \+ *lemma* singleton_smul_singleton
- \+ *lemma* subset_smul
- \+ *lemma* vsub_def
- \+ *lemma* image_vsub_product
- \+ *lemma* mem_vsub
- \+ *lemma* coe_vsub
- \+ *lemma* vsub_mem_vsub
- \+ *lemma* vsub_card_le
- \+ *lemma* empty_vsub
- \+ *lemma* vsub_empty
- \+ *lemma* vsub_nonempty_iff
- \+ *lemma* nonempty.vsub
- \+ *lemma* vsub_subset_vsub
- \+ *lemma* vsub_singleton
- \+ *lemma* singleton_vsub
- \+ *lemma* singleton_vsub_singleton
- \+ *lemma* subset_vsub
- \+ *lemma* smul_finset_def
- \+ *lemma* image_smul
- \+ *lemma* mem_smul_finset
- \+ *lemma* coe_smul_finset
- \+ *lemma* smul_finset_mem_smul_finset
- \+ *lemma* smul_finset_card_le
- \+ *lemma* smul_finset_empty
- \+ *lemma* smul_finset_nonempty_iff
- \+ *lemma* nonempty.smul_finset
- \+ *lemma* smul_finset_subset_smul_finset
- \+ *lemma* smul_finset_singleton
- \+/\- *lemma* mul_card_le
- \+/\- *lemma* coe_pow

modified src/data/set/pointwise.lean

modified src/measure_theory/integral/set_to_l1.lean

modified src/ring_theory/polynomial/eisenstein.lean



## [2022-03-22 09:42:58](https://github.com/leanprover-community/mathlib/commit/28eb06f)
feat(analysis/calculus): define `diff_on_int_cont` ([#12688](https://github.com/leanprover-community/mathlib/pull/12688))
#### Estimated changes
created src/analysis/calculus/diff_on_int_cont.lean
- \+ *lemma* differentiable_on.diff_on_int_cont
- \+ *lemma* differentiable.diff_on_int_cont
- \+ *lemma* diff_on_int_cont_open
- \+ *lemma* diff_on_int_cont_univ
- \+ *lemma* diff_on_int_cont_const
- \+ *lemma* differentiable_on.comp_diff_on_int_cont
- \+ *lemma* differentiable.comp_diff_on_int_cont
- \+ *lemma* comp
- \+ *lemma* differentiable_on_ball
- \+ *lemma* mk_ball
- \+ *lemma* differentiable_at'
- \+ *lemma* add
- \+ *lemma* add_const
- \+ *lemma* const_add
- \+ *lemma* neg
- \+ *lemma* sub
- \+ *lemma* sub_const
- \+ *lemma* const_sub
- \+ *lemma* const_smul
- \+ *lemma* smul
- \+ *lemma* smul_const
- \+ *lemma* inv

modified src/analysis/complex/abs_max.lean
- \+/\- *lemma* norm_max_aux₂
- \+/\- *lemma* norm_max_aux₂

modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* _root_.diff_on_int_cont.circle_integral_sub_inv_smul
- \+ *lemma* _root_.differentiable_on.circle_integral_sub_inv_smul
- \+ *lemma* _root_.diff_on_int_cont.has_fpower_series_on_ball
- \- *lemma* circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on
- \- *lemma* circle_integral_sub_inv_smul_of_differentiable_on
- \- *lemma* has_fpower_series_on_ball_of_continuous_on_of_differentiable_on

modified src/analysis/complex/liouville.lean

modified src/analysis/complex/schwarz.lean



## [2022-03-22 09:42:57](https://github.com/leanprover-community/mathlib/commit/5826b2f)
feat(topology/order/hom/esakia): Esakia morphisms ([#12241](https://github.com/leanprover-community/mathlib/pull/12241))
Define pseudo-epimorphisms and Esakia morphisms following the hom refactor.
#### Estimated changes
modified src/order/hom/lattice.lean

created src/topology/order/hom/esakia.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* coe_id_order_hom
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* coe_comp_order_hom
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* coe_id_continuous_order_hom
- \+ *lemma* coe_id_pseudo_epimorphism
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_continuous_order_hom
- \+ *lemma* coe_comp_pseudo_epimorphism
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* comp
- \+ *def* to_pseudo_epimorphism
- \+ *def* comp



## [2022-03-22 08:35:26](https://github.com/leanprover-community/mathlib/commit/41d291c)
feat(algebra/big_operators/associated): generalize prod_primes_dvd ([#12740](https://github.com/leanprover-community/mathlib/pull/12740))
#### Estimated changes
modified src/algebra/big_operators/associated.lean
- \+ *lemma* multiset.prod_primes_dvd
- \+ *lemma* finset.prod_primes_dvd

modified src/number_theory/primorial.lean
- \- *lemma* prod_primes_dvd



## [2022-03-22 08:03:55](https://github.com/leanprover-community/mathlib/commit/3ce4161)
refactor(measure_theory/integral): restrict interval integrals to real intervals ([#12754](https://github.com/leanprover-community/mathlib/pull/12754))
This way `∫ x in 0 .. 1, (1 : real)` means what it should, not `∫ x : nat in 0 .. 1, (1 : real)`.
#### Estimated changes
modified src/analysis/calculus/parametric_interval_integral.lean
- \+/\- *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* has_fderiv_at_integral_of_dominated_of_fderiv_le
- \+/\- *lemma* has_deriv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* has_deriv_at_integral_of_dominated_loc_of_deriv_le
- \+/\- *lemma* has_fderiv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* has_fderiv_at_integral_of_dominated_of_fderiv_le
- \+/\- *lemma* has_deriv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* has_deriv_at_integral_of_dominated_loc_of_deriv_le

modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* integrable_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+/\- *lemma* interval_integral_tendsto_integral
- \+/\- *lemma* interval_integral_tendsto_integral_Iic
- \+/\- *lemma* interval_integral_tendsto_integral_Ioi
- \+/\- *lemma* integrable_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_bounded
- \+/\- *lemma* integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+/\- *lemma* interval_integral_tendsto_integral
- \+/\- *lemma* interval_integral_tendsto_integral_Iic
- \+/\- *lemma* interval_integral_tendsto_integral_Ioi

modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* interval_integrable_iff
- \+/\- *lemma* interval_integrable.def
- \+/\- *lemma* interval_integrable_iff_integrable_Ioc_of_le
- \+/\- *lemma* measure_theory.integrable.interval_integrable
- \+/\- *lemma* measure_theory.integrable_on.interval_integrable
- \+/\- *lemma* interval_integrable_const_iff
- \+/\- *lemma* interval_integrable_const
- \+/\- *lemma* trans_iterate
- \+/\- *lemma* abs
- \+/\- *lemma* mono
- \+/\- *lemma* mono_set
- \+/\- *lemma* mono_measure
- \+/\- *lemma* mono_set_ae
- \+/\- *lemma* mono_fun
- \+/\- *lemma* mono_fun'
- \+/\- *lemma* mul_continuous_on
- \+/\- *lemma* continuous_on_mul
- \+/\- *lemma* monotone_on.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* monotone.interval_integrable
- \+/\- *lemma* antitone.interval_integrable
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+/\- *lemma* interval_integral_eq_integral_interval_oc
- \+/\- *lemma* integral_cases
- \+/\- *lemma* norm_integral_min_max
- \+/\- *lemma* norm_integral_eq_norm_integral_Ioc
- \+/\- *lemma* abs_integral_eq_abs_integral_interval_oc
- \+/\- *lemma* integral_finset_sum
- \+/\- *lemma* integral_smul_const
- \+/\- *lemma* integral_const_mul
- \+/\- *lemma* integral_mul_const
- \+/\- *lemma* integral_div
- \+/\- *lemma* integral_const
- \+/\- *lemma* integral_congr
- \+/\- *lemma* sum_integral_adjacent_intervals
- \+/\- *lemma* integral_eq_integral_of_support_subset
- \+/\- *lemma* integral_congr_ae'
- \+/\- *lemma* integral_congr_ae
- \+/\- *lemma* integral_zero_ae
- \+/\- *lemma* integral_indicator
- \+/\- *lemma* continuous_of_dominated_interval
- \+/\- *lemma* continuous_within_at_primitive
- \+/\- *lemma* continuous_on_primitive
- \+/\- *lemma* continuous_on_primitive_Icc
- \+/\- *lemma* continuous_on_primitive_interval'
- \+/\- *lemma* continuous_on_primitive_interval
- \+/\- *lemma* continuous_on_primitive_interval_left
- \+/\- *lemma* continuous_primitive
- \+/\- *lemma* _root_.measure_theory.integrable.continuous_primitive
- \+/\- *lemma* integral_nonneg
- \+/\- *lemma* integral_mono_on
- \+/\- *lemma* finite_at_inner
- \+/\- *lemma* sub_le_integral_of_has_deriv_right_of_le
- \+/\- *lemma* interval_integrable_iff
- \+/\- *lemma* interval_integrable.def
- \+/\- *lemma* interval_integrable_iff_integrable_Ioc_of_le
- \+/\- *lemma* measure_theory.integrable.interval_integrable
- \+/\- *lemma* measure_theory.integrable_on.interval_integrable
- \+/\- *lemma* interval_integrable_const_iff
- \+/\- *lemma* interval_integrable_const
- \+/\- *lemma* trans_iterate
- \+/\- *lemma* abs
- \+/\- *lemma* mono
- \+/\- *lemma* mono_set
- \+/\- *lemma* mono_measure
- \+/\- *lemma* mono_set_ae
- \+/\- *lemma* mono_fun
- \+/\- *lemma* mono_fun'
- \+/\- *lemma* mul_continuous_on
- \+/\- *lemma* continuous_on_mul
- \+/\- *lemma* monotone_on.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* monotone.interval_integrable
- \+/\- *lemma* antitone.interval_integrable
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+/\- *lemma* interval_integral_eq_integral_interval_oc
- \+/\- *lemma* integral_cases
- \+/\- *lemma* norm_integral_min_max
- \+/\- *lemma* norm_integral_eq_norm_integral_Ioc
- \+/\- *lemma* abs_integral_eq_abs_integral_interval_oc
- \+/\- *lemma* integral_finset_sum
- \+/\- *lemma* integral_smul_const
- \+/\- *lemma* integral_const_mul
- \+/\- *lemma* integral_mul_const
- \+/\- *lemma* integral_div
- \+/\- *lemma* integral_const
- \+/\- *lemma* integral_congr
- \+/\- *lemma* sum_integral_adjacent_intervals
- \+/\- *lemma* integral_eq_integral_of_support_subset
- \+/\- *lemma* integral_congr_ae'
- \+/\- *lemma* integral_congr_ae
- \+/\- *lemma* integral_zero_ae
- \+/\- *lemma* integral_indicator
- \+/\- *lemma* continuous_of_dominated_interval
- \+/\- *lemma* continuous_within_at_primitive
- \+/\- *lemma* continuous_on_primitive
- \+/\- *lemma* continuous_on_primitive_Icc
- \+/\- *lemma* continuous_on_primitive_interval'
- \+/\- *lemma* continuous_on_primitive_interval
- \+/\- *lemma* continuous_on_primitive_interval_left
- \+/\- *lemma* continuous_primitive
- \+/\- *lemma* _root_.measure_theory.integrable.continuous_primitive
- \+/\- *lemma* integral_nonneg
- \+/\- *lemma* integral_mono_on
- \+/\- *lemma* finite_at_inner
- \+/\- *lemma* sub_le_integral_of_has_deriv_right_of_le
- \+/\- *def* interval_integrable
- \+/\- *def* interval_integral
- \+/\- *def* interval_integrable
- \+/\- *def* interval_integral



## [2022-03-22 06:15:55](https://github.com/leanprover-community/mathlib/commit/b0f585c)
feat(combinatorics/simple_graph/inc_matrix): Incidence matrix ([#10867](https://github.com/leanprover-community/mathlib/pull/10867))
Define the incidence matrix of a simple graph and prove the basics, including some stuff about matrix multiplication.
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+ *lemma* ite_and_mul_zero

modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* incidence_set_inter_incidence_set_of_adj
- \+ *lemma* incidence_set_inter_incidence_set_of_not_adj
- \+ *lemma* card_incidence_finset_eq_degree
- \- *lemma* incidence_set_inter_incidence_set

created src/combinatorics/simple_graph/inc_matrix.lean
- \+ *lemma* inc_matrix_apply
- \+ *lemma* inc_matrix_apply'
- \+ *lemma* inc_matrix_apply_mul_inc_matrix_apply
- \+ *lemma* inc_matrix_apply_mul_inc_matrix_apply_of_not_adj
- \+ *lemma* inc_matrix_of_not_mem_incidence_set
- \+ *lemma* inc_matrix_of_mem_incidence_set
- \+ *lemma* inc_matrix_apply_eq_zero_iff
- \+ *lemma* inc_matrix_apply_eq_one_iff
- \+ *lemma* sum_inc_matrix_apply
- \+ *lemma* inc_matrix_mul_transpose_diag
- \+ *lemma* sum_inc_matrix_apply_of_mem_edge_set
- \+ *lemma* sum_inc_matrix_apply_of_not_mem_edge_set
- \+ *lemma* inc_matrix_transpose_mul_diag
- \+ *lemma* inc_matrix_mul_transpose_apply_of_adj
- \+ *lemma* inc_matrix_mul_transpose
- \+ *def* inc_matrix

modified src/data/finset/card.lean
- \+ *lemma* card_doubleton

modified src/data/fintype/basic.lean
- \+ *lemma* coe_filter_univ
- \+ *lemma* filter_mem_univ_eq_to_finset

modified src/linear_algebra/affine_space/combination.lean



## [2022-03-22 03:26:17](https://github.com/leanprover-community/mathlib/commit/01eb653)
chore(scripts): update nolints.txt ([#12868](https://github.com/leanprover-community/mathlib/pull/12868))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-22 01:36:27](https://github.com/leanprover-community/mathlib/commit/e51377f)
feat(logic/basic): `ulift.down` is injective ([#12824](https://github.com/leanprover-community/mathlib/pull/12824))
We also make the arguments to `plift.down_inj` inferred.
#### Estimated changes
modified src/logic/basic.lean
- \+ *lemma* ulift.down_injective
- \+ *lemma* ulift.down_inj
- \+ *lemma* plift.down_injective
- \+/\- *lemma* plift.down_inj
- \+/\- *lemma* plift.down_inj



## [2022-03-22 00:37:25](https://github.com/leanprover-community/mathlib/commit/d71e06c)
feat(topology/algebra/monoid): construct a unit from limits of units and their inverses ([#12760](https://github.com/leanprover-community/mathlib/pull/12760))
#### Estimated changes
modified src/topology/algebra/monoid.lean
- \+ *def* filter.tendsto.units



## [2022-03-21 20:08:03](https://github.com/leanprover-community/mathlib/commit/f9dc84e)
feat(topology/continuous_function/units): basic results about units in `C(α, β)` ([#12687](https://github.com/leanprover-community/mathlib/pull/12687))
This establishes a few facts about units in `C(α, β)` including the equivalence `C(α, βˣ) ≃ C(α, β)ˣ`. Moreover, when `β` is a complete normed field, we show that the spectrum of `f : C(α, β)` is precisely `set.range f`.
#### Estimated changes
created src/topology/continuous_function/units.lean
- \+ *lemma* _root_.normed_ring.is_unit_unit_continuous
- \+ *lemma* is_unit_iff_forall_is_unit
- \+ *lemma* is_unit_iff_forall_ne_zero
- \+ *lemma* spectrum_eq_range
- \+ *def* units_lift



## [2022-03-21 19:25:50](https://github.com/leanprover-community/mathlib/commit/8001ea5)
feat(category_theory/abelian): right derived functor ([#12841](https://github.com/leanprover-community/mathlib/pull/12841))
This pr dualises derived.lean. Right derived functor and natural transformation between right derived functors and related lemmas are formalised. 
The docs string currently contains more than what is in this file, but everything else will come shortly after.
#### Estimated changes
modified src/category_theory/abelian/ext.lean

renamed src/category_theory/abelian/derived.lean to src/category_theory/abelian/left_derived.lean

created src/category_theory/abelian/right_derived.lean
- \+ *lemma* functor.right_derived_map_eq
- \+ *lemma* nat_trans.right_derived_id
- \+ *lemma* nat_trans.right_derived_comp
- \+ *lemma* nat_trans.right_derived_eq
- \+ *def* functor.right_derived
- \+ *def* functor.right_derived_obj_iso
- \+ *def* functor.right_derived_obj_injective_zero
- \+ *def* functor.right_derived_obj_injective_succ
- \+ *def* nat_trans.right_derived

renamed src/category_theory/functor/derived.lean to src/category_theory/functor/left_derived.lean

modified src/category_theory/monoidal/tor.lean



## [2022-03-21 18:05:19](https://github.com/leanprover-community/mathlib/commit/25ec622)
feat(data/polynomial/eval + data/polynomial/ring_division): move a lemma and remove assumptions ([#12854](https://github.com/leanprover-community/mathlib/pull/12854))
A lemma about composition of polynomials assumed `comm_ring` and `is_domain`.  The new version assumes `semiring`.
I golfed slightly the original proof: it may very well be that a shorter proof is available!
I also moved the lemma, since it seems better for this lemma to appear in the file where the definition of `comp` appears.
#### Estimated changes
modified src/data/polynomial/eval.lean
- \+ *lemma* coeff_comp_degree_mul_degree

modified src/data/polynomial/ring_division.lean
- \- *lemma* coeff_comp_degree_mul_degree



## [2022-03-21 18:05:18](https://github.com/leanprover-community/mathlib/commit/fd4a034)
refactor(analysis/locally_convex/with_seminorms): use abbreviations to allow for dot notation ([#12846](https://github.com/leanprover-community/mathlib/pull/12846))
#### Estimated changes
modified src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* basis_sets_iff
- \+ *lemma* basis_sets_mem
- \+ *lemma* basis_sets_singleton_mem
- \+ *lemma* basis_sets_nonempty
- \+ *lemma* basis_sets_intersect
- \+ *lemma* basis_sets_zero
- \+ *lemma* basis_sets_add
- \+ *lemma* basis_sets_neg
- \+ *lemma* basis_sets_smul_right
- \+ *lemma* basis_sets_smul
- \+ *lemma* basis_sets_smul_left
- \+ *lemma* seminorm_family.with_seminorms_eq
- \+ *lemma* seminorm_family.with_seminorms_of_nhds
- \+ *lemma* seminorm_family.with_seminorms_of_has_basis
- \+/\- *lemma* continuous_from_bounded
- \+ *lemma* seminorm_family.to_locally_convex_space
- \- *lemma* seminorm_basis_zero_iff
- \- *lemma* seminorm_basis_zero_mem
- \- *lemma* seminorm_basis_zero_singleton_mem
- \- *lemma* seminorm_basis_zero_nonempty
- \- *lemma* seminorm_basis_zero_intersect
- \- *lemma* seminorm_basis_zero_zero
- \- *lemma* seminorm_basis_zero_add
- \- *lemma* seminorm_basis_zero_neg
- \- *lemma* seminorm_basis_zero_smul_right
- \- *lemma* seminorm_basis_zero_smul
- \- *lemma* seminorm_basis_zero_smul_left
- \- *lemma* with_seminorms_eq
- \- *lemma* with_seminorms_of_nhds
- \- *lemma* with_seminorms_of_has_basis
- \+/\- *lemma* continuous_from_bounded
- \- *lemma* with_seminorms.to_locally_convex_space
- \+ *def* basis_sets
- \- *def* seminorm_basis_zero
- \- *def* seminorm_add_group_filter_basis
- \- *def* seminorm_module_filter_basis



## [2022-03-21 16:35:37](https://github.com/leanprover-community/mathlib/commit/a2e4802)
feat(model_theory/fraisse): Defines Fraïssé classes ([#12817](https://github.com/leanprover-community/mathlib/pull/12817))
Defines the age of a structure
(Mostly) characterizes the ages of countable structures
Defines Fraïssé classes
#### Estimated changes
modified src/model_theory/basic.lean

modified src/model_theory/finitely_generated.lean
- \+ *lemma* fg.cg
- \+ *theorem* fg.sup
- \+ *theorem* cg.sup
- \- *theorem* fg_sup
- \- *theorem* cg_sup

created src/model_theory/fraisse.lean
- \+ *lemma* age.is_equiv_invariant
- \+ *lemma* age.hereditary
- \+ *lemma* age.joint_embedding
- \+ *lemma* age.countable_quotient
- \+ *def* age
- \+ *def* hereditary
- \+ *def* joint_embedding
- \+ *def* amalgamation



## [2022-03-21 16:35:35](https://github.com/leanprover-community/mathlib/commit/1b787d6)
feat(linear_algebra/span): generalize span_singleton_smul_eq ([#12736](https://github.com/leanprover-community/mathlib/pull/12736))
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/projective_space/basic.lean

modified src/linear_algebra/span.lean
- \+/\- *lemma* span_singleton_smul_le
- \+ *lemma* span_singleton_group_smul_eq
- \+/\- *lemma* span_singleton_smul_eq
- \+/\- *lemma* span_singleton_smul_le
- \+/\- *lemma* span_singleton_smul_eq



## [2022-03-21 16:35:34](https://github.com/leanprover-community/mathlib/commit/df299a1)
docs(order/filter/basic): fix docstring of generate ([#12734](https://github.com/leanprover-community/mathlib/pull/12734))
#### Estimated changes
modified src/order/filter/basic.lean



## [2022-03-21 16:35:33](https://github.com/leanprover-community/mathlib/commit/09750eb)
feat(measure_theory/function/uniform_integrable): add API for uniform integrability in the probability sense ([#12678](https://github.com/leanprover-community/mathlib/pull/12678))
Uniform integrability in probability theory is commonly defined as the uniform existence of a number for which the expectation of the random variables restricted on the set for which they are greater than said number is arbitrarily small. We have defined it 
in mathlib, on the other hand, as uniform integrability in the measure theory sense + existence of a uniform bound of the Lp norms. 
This PR proves the first definition implies the second while a later PR will deal with the reverse direction.
#### Estimated changes
modified src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* unif_integrable_zero_meas
- \+/\- *lemma* unif_integrable_congr_ae
- \+/\- *lemma* unif_integrable_of_tendsto_Lp
- \+/\- *lemma* tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* tendsto_in_measure_iff_tendsto_Lp
- \+ *lemma* unif_integrable_of'
- \+ *lemma* unif_integrable_of
- \+ *lemma* uniform_integrable_zero_meas
- \+ *lemma* uniform_integrable.ae_eq
- \+ *lemma* uniform_integrable_congr_ae
- \+ *lemma* uniform_integrable_fintype
- \+ *lemma* uniform_integrable_subsingleton
- \+ *lemma* uniform_integrable_const
- \+ *lemma* uniform_integrable_of
- \+/\- *lemma* unif_integrable_congr_ae
- \+/\- *lemma* unif_integrable_of_tendsto_Lp
- \+/\- *lemma* tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* tendsto_in_measure_iff_tendsto_Lp

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* indicator_meas_zero



## [2022-03-21 16:35:32](https://github.com/leanprover-community/mathlib/commit/715f984)
feat(model_theory/terms_and_formulas): Prenex Normal Form ([#12558](https://github.com/leanprover-community/mathlib/pull/12558))
Defines `first_order.language.bounded_formula.to_prenex`, a function which takes a formula and outputs an equivalent formula in prenex normal form.
Proves inductive principles based on the fact that every formula is equivalent to one in prenex normal form.
#### Estimated changes
modified src/data/fin/tuple/basic.lean
- \+ *lemma* snoc_comp_cast_succ

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* not_all_is_atomic
- \+ *lemma* not_ex_is_atomic
- \+ *lemma* is_atomic.lift_at
- \+ *lemma* is_atomic.cast_le
- \+ *lemma* is_qf.lift_at
- \+ *lemma* is_qf.cast_le
- \+ *lemma* not_all_is_qf
- \+ *lemma* not_ex_is_qf
- \+ *lemma* is_prenex.cast_le
- \+ *lemma* is_prenex.lift_at
- \+ *lemma* is_qf.to_prenex_imp_right
- \+ *lemma* is_prenex_to_prenex_imp_right
- \+ *lemma* is_qf.to_prenex_imp
- \+ *lemma* is_prenex_to_prenex_imp
- \+ *lemma* to_prenex_is_prenex
- \+ *lemma* is_atomic_graph
- \+ *lemma* semantically_equivalent.refl
- \+ *lemma* semantically_equivalent.symm
- \+ *lemma* semantically_equivalent.trans
- \+ *lemma* all_semantically_equivalent_not_ex_not
- \+ *lemma* ex_semantically_equivalent_not_all_not
- \+ *lemma* imp_semantically_equivalent_to_prenex_imp_right
- \+ *lemma* imp_semantically_equivalent_to_prenex_imp
- \+ *lemma* semantically_equivalent_to_prenex
- \+ *lemma* induction_on_all_ex
- \+ *lemma* induction_on_exists_not
- \+ *def* to_prenex_imp_right
- \+ *def* to_prenex_imp
- \+ *def* to_prenex



## [2022-03-21 14:42:55](https://github.com/leanprover-community/mathlib/commit/091f27e)
chore(order/{complete_lattice,sup_indep}): move `complete_lattice.independent` ([#12588](https://github.com/leanprover-community/mathlib/pull/12588))
Putting this here means that in future we can talk about `pairwise_disjoint` at the same time, which was previously defined downstream of `complete_lattice.independent`.
This commit only moves existing declarations and adjusts module docstrings.
The new authorship comes from [#5971](https://github.com/leanprover-community/mathlib/pull/5971) and [#7199](https://github.com/leanprover-community/mathlib/pull/7199), which predate this file.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean

modified src/order/compactly_generated.lean

modified src/order/complete_lattice.lean
- \- *lemma* set_independent_empty
- \- *lemma* set_independent.disjoint
- \- *lemma* set_independent_pair
- \- *lemma* set_independent.disjoint_Sup
- \- *lemma* set_independent_iff
- \- *lemma* independent_empty
- \- *lemma* independent_pempty
- \- *lemma* independent.disjoint
- \- *lemma* independent.mono
- \- *lemma* independent.comp
- \- *lemma* independent_pair
- \- *lemma* independent.map_order_iso
- \- *lemma* independent_map_order_iso_iff
- \- *lemma* independent.disjoint_bsupr
- \- *theorem* set_independent.mono
- \- *theorem* independent_def
- \- *theorem* independent_def'
- \- *theorem* independent_def''
- \- *def* set_independent
- \- *def* independent

modified src/order/sup_indep.lean
- \+ *lemma* set_independent_empty
- \+ *lemma* set_independent.disjoint
- \+ *lemma* set_independent_pair
- \+ *lemma* set_independent.disjoint_Sup
- \+ *lemma* set_independent_iff
- \+ *lemma* independent_empty
- \+ *lemma* independent_pempty
- \+ *lemma* independent.disjoint
- \+ *lemma* independent.mono
- \+ *lemma* independent.comp
- \+ *lemma* independent_pair
- \+ *lemma* independent.map_order_iso
- \+ *lemma* independent_map_order_iso_iff
- \+ *lemma* independent.disjoint_bsupr
- \+ *theorem* set_independent.mono
- \+ *theorem* independent_def
- \+ *theorem* independent_def'
- \+ *theorem* independent_def''
- \+ *def* set_independent
- \+ *def* independent



## [2022-03-21 12:46:46](https://github.com/leanprover-community/mathlib/commit/135c574)
feat(model_theory/definability): Definability lemmas ([#12262](https://github.com/leanprover-community/mathlib/pull/12262))
Proves several lemmas to work with definability over different parameter sets.
Shows that definability is closed under projection.
#### Estimated changes
modified src/model_theory/definability.lean
- \+ *lemma* definable.map_expansion
- \+ *lemma* empty_definable_iff
- \+ *lemma* definable_iff_empty_definable_with_params
- \+ *lemma* definable.mono
- \+ *lemma* fin.coe_cast_add_zero
- \+ *lemma* definable.image_comp_sum_inl_fin
- \+ *lemma* definable.image_comp_embedding
- \+ *lemma* definable.image_comp

modified src/model_theory/terms_and_formulas.lean
- \+/\- *def* Lhom.on_term
- \+/\- *def* on_bounded_formula
- \+/\- *def* on_formula
- \+/\- *def* Lhom.on_term
- \+/\- *def* on_bounded_formula
- \+/\- *def* on_formula



## [2022-03-21 11:08:42](https://github.com/leanprover-community/mathlib/commit/86055c5)
split(data/{finset,set}/pointwise): Split off `algebra.pointwise` ([#12831](https://github.com/leanprover-community/mathlib/pull/12831))
Split `algebra.pointwise` into
* `data.set.pointwise`: Pointwise operations on `set`
* `data.finset.pointwise`: Pointwise operations on `finset`
I'm crediting
* The same people for `data.set.pointwise`
* Floris for [#3541](https://github.com/leanprover-community/mathlib/pull/3541)
#### Estimated changes
modified src/algebra/add_torsor.lean

modified src/algebra/algebra/operations.lean

modified src/algebra/bounds.lean

modified src/algebra/module/pointwise_pi.lean

modified src/algebra/order/module.lean

modified src/algebra/star/pointwise.lean

modified src/data/dfinsupp/interval.lean

modified src/data/finset/finsupp.lean

created src/data/finset/pointwise.lean
- \+ *lemma* mem_one
- \+ *lemma* coe_one
- \+ *lemma* one_subset
- \+ *lemma* singleton_one
- \+ *lemma* one_mem_one
- \+ *lemma* one_nonempty
- \+ *lemma* image_one
- \+ *lemma* mul_def
- \+ *lemma* image_mul_prod
- \+ *lemma* mem_mul
- \+ *lemma* coe_mul
- \+ *lemma* mul_mem_mul
- \+ *lemma* mul_card_le
- \+ *lemma* empty_mul
- \+ *lemma* mul_empty
- \+ *lemma* mul_nonempty_iff
- \+ *lemma* mul_subset_mul
- \+ *lemma* mul_singleton
- \+ *lemma* singleton_mul
- \+ *lemma* singleton_mul_singleton
- \+ *lemma* subset_mul
- \+ *lemma* mul_zero_subset
- \+ *lemma* zero_mul_subset
- \+ *lemma* nonempty.mul_zero
- \+ *lemma* nonempty.zero_mul
- \+ *lemma* image_mul_left
- \+ *lemma* image_mul_right
- \+ *lemma* image_mul_left'
- \+ *lemma* image_mul_right'
- \+ *lemma* preimage_mul_left_singleton
- \+ *lemma* preimage_mul_right_singleton
- \+ *lemma* preimage_mul_left_one
- \+ *lemma* preimage_mul_right_one
- \+ *lemma* preimage_mul_left_one'
- \+ *lemma* preimage_mul_right_one'
- \+ *lemma* coe_pow

modified src/data/real/pointwise.lean

modified src/data/set/intervals/image_preimage.lean

renamed src/algebra/pointwise.lean to src/data/set/pointwise.lean
- \- *lemma* mem_one
- \- *lemma* coe_one
- \- *lemma* mul_def
- \- *lemma* mem_mul
- \- *lemma* coe_mul
- \- *lemma* mul_mem_mul
- \- *lemma* mul_card_le
- \- *lemma* empty_mul
- \- *lemma* mul_empty
- \- *lemma* mul_nonempty_iff
- \- *lemma* mul_subset_mul
- \- *lemma* mul_singleton
- \- *lemma* singleton_mul
- \- *lemma* singleton_mul_singleton
- \- *lemma* mul_zero_subset
- \- *lemma* zero_mul_subset
- \- *lemma* nonempty.mul_zero
- \- *lemma* nonempty.zero_mul
- \- *lemma* singleton_zero_mul
- \- *lemma* singleton_one
- \- *lemma* one_mem_one
- \- *lemma* image_mul_prod
- \- *lemma* image_mul_left
- \- *lemma* image_mul_right
- \- *lemma* image_mul_left'
- \- *lemma* image_mul_right'
- \- *lemma* preimage_mul_left_singleton
- \- *lemma* preimage_mul_right_singleton
- \- *lemma* preimage_mul_left_one
- \- *lemma* preimage_mul_right_one
- \- *lemma* preimage_mul_left_one'
- \- *lemma* preimage_mul_right_one'
- \- *lemma* coe_pow
- \- *lemma* subset_mul
- \- *theorem* one_subset
- \- *theorem* one_nonempty
- \- *theorem* image_one

modified src/group_theory/order_of_element.lean

modified src/group_theory/submonoid/pointwise.lean

modified src/order/filter/pointwise.lean

modified src/order/well_founded_set.lean

modified src/ring_theory/subsemiring/pointwise.lean

modified src/topology/algebra/monoid.lean



## [2022-03-21 09:13:23](https://github.com/leanprover-community/mathlib/commit/8161ba2)
feat(model_theory/ultraproducts): Ultraproducts and the Compactness Theorem ([#12531](https://github.com/leanprover-community/mathlib/pull/12531))
Defines `filter.product`, a dependent version of `filter.germ`.
Defines a structure on an ultraproduct (a `filter.product` with respect to an ultrafilter).
Proves Łoś's Theorem, characterizing when an ultraproduct realizes a formula.
Proves the Compactness theorem with ultraproducts.
#### Estimated changes
modified docs/overview.yaml

modified src/model_theory/quotients.lean

modified src/model_theory/terms_and_formulas.lean
- \+ *def* sentence.realize
- \- *def* realize_sentence

created src/model_theory/ultraproducts.lean
- \+ *lemma* fun_map_cast
- \+ *lemma* term_realize_cast
- \+ *theorem* bounded_formula_realize_cast
- \+ *theorem* realize_formula_cast
- \+ *theorem* sentence_realize
- \+ *theorem* is_satisfiable_iff_is_finitely_satisfiable

modified src/order/filter/germ.lean
- \+ *def* product_setoid
- \+ *def* product



## [2022-03-21 07:40:25](https://github.com/leanprover-community/mathlib/commit/8e9abe3)
feat(measure_theory/constructions/borel_space): generalize a lemma ([#12843](https://github.com/leanprover-community/mathlib/pull/12843))
Generalize `measurable_limit_of_tendsto_metric_ae` from
`at_top : filter ℕ` to any countably generated filter on a nonempty type.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_limit_of_tendsto_metric_ae
- \+/\- *lemma* measurable_limit_of_tendsto_metric_ae



## [2022-03-21 05:51:55](https://github.com/leanprover-community/mathlib/commit/d902c22)
chore(category/abelian/derived): shorten proof ([#12847](https://github.com/leanprover-community/mathlib/pull/12847))
#### Estimated changes
modified src/category_theory/abelian/derived.lean



## [2022-03-21 05:51:54](https://github.com/leanprover-community/mathlib/commit/395019e)
feat(algebra/homology/additive): dualise statement of chain complex to cochain complex ([#12840](https://github.com/leanprover-community/mathlib/pull/12840))
#### Estimated changes
modified src/algebra/homology/additive.lean
- \+ *lemma* single₀_map_homological_complex_hom_app_zero
- \+ *lemma* single₀_map_homological_complex_hom_app_succ
- \+ *lemma* single₀_map_homological_complex_inv_app_zero
- \+ *lemma* single₀_map_homological_complex_inv_app_succ
- \+ *def* single₀_map_homological_complex



## [2022-03-21 05:51:53](https://github.com/leanprover-community/mathlib/commit/69d3d16)
feat(polynomial/derivative): tidy+new theorems ([#12833](https://github.com/leanprover-community/mathlib/pull/12833))
Adds `iterate_derivative_eq_zero` and strengthens other results.
New theorems: `iterate_derivative_eq_zero`, `nat_degree_derivative_le`
Deleted: `derivative_lhom` - it is one already.
Misc: Turn a docstring into a comment
Everything else only got moved around + golfed, in order to weaken assumptions.
#### Estimated changes
modified src/data/polynomial/derivative.lean
- \+/\- *lemma* derivative_cast_nat
- \+ *lemma* iterate_derivative_eq_zero
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *lemma* derivative_neg
- \+/\- *lemma* iterate_derivative_neg
- \+/\- *lemma* derivative_sub
- \+/\- *lemma* iterate_derivative_sub
- \+/\- *lemma* derivative_neg
- \+/\- *lemma* iterate_derivative_neg
- \+/\- *lemma* derivative_sub
- \+/\- *lemma* iterate_derivative_sub
- \- *lemma* derivative_lhom_coe
- \+/\- *lemma* derivative_cast_nat
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *theorem* of_mem_support_derivative
- \+/\- *theorem* degree_derivative_lt
- \+/\- *theorem* degree_derivative_le
- \+/\- *theorem* nat_degree_derivative_lt
- \+ *theorem* nat_degree_derivative_le
- \+/\- *theorem* nat_degree_eq_zero_of_derivative_eq_zero
- \+/\- *theorem* of_mem_support_derivative
- \+/\- *theorem* degree_derivative_lt
- \+/\- *theorem* nat_degree_derivative_lt
- \+/\- *theorem* degree_derivative_le
- \+/\- *theorem* nat_degree_eq_zero_of_derivative_eq_zero
- \- *def* derivative_lhom

modified src/ring_theory/polynomial/bernstein.lean



## [2022-03-21 05:51:52](https://github.com/leanprover-community/mathlib/commit/06017e0)
feat(order/compare): add 4 dot notation lemmas ([#12832](https://github.com/leanprover-community/mathlib/pull/12832))
#### Estimated changes
modified src/order/compare.lean
- \+ *lemma* has_lt.lt.cmp_eq_lt
- \+ *lemma* has_lt.lt.cmp_eq_gt
- \+ *lemma* eq.cmp_eq_eq
- \+ *lemma* eq.cmp_eq_eq'



## [2022-03-21 05:51:51](https://github.com/leanprover-community/mathlib/commit/f5987b2)
chore(data/real/basic): tweak lemmas about `of_cauchy` ([#12829](https://github.com/leanprover-community/mathlib/pull/12829))
These lemmas are about `real.of_cauchy` not `real.cauchy`, as their name suggests.
This also flips the direction of some of the lemmas to be consistent with the zero and one lemmas.
Finally, this adds the lemmas about `real.cauchy` that are missing.
#### Estimated changes
modified src/data/real/basic.lean
- \+ *lemma* of_cauchy_zero
- \+ *lemma* of_cauchy_one
- \+ *lemma* of_cauchy_add
- \+ *lemma* of_cauchy_neg
- \+ *lemma* of_cauchy_mul
- \+ *lemma* cauchy_zero
- \+ *lemma* cauchy_one
- \+ *lemma* cauchy_add
- \+ *lemma* cauchy_neg
- \+ *lemma* cauchy_mul
- \+/\- *lemma* mk_zero
- \+/\- *lemma* mk_one
- \+/\- *lemma* mk_add
- \+/\- *lemma* mk_mul
- \+/\- *lemma* mk_neg
- \+ *lemma* of_cauchy_inv
- \+ *lemma* cauchy_inv
- \- *lemma* zero_cauchy
- \- *lemma* one_cauchy
- \- *lemma* add_cauchy
- \- *lemma* neg_cauchy
- \- *lemma* mul_cauchy
- \+/\- *lemma* mk_zero
- \+/\- *lemma* mk_one
- \+/\- *lemma* mk_add
- \+/\- *lemma* mk_mul
- \+/\- *lemma* mk_neg
- \- *lemma* inv_cauchy



## [2022-03-21 05:51:50](https://github.com/leanprover-community/mathlib/commit/772c776)
feat(ring_theory/algebraic): Added basic lemmas + golf ([#12820](https://github.com/leanprover-community/mathlib/pull/12820))
#### Estimated changes
modified src/ring_theory/algebraic.lean
- \+ *lemma* is_transcendental_of_subsingleton
- \+/\- *lemma* is_integral.is_algebraic
- \+ *lemma* is_algebraic_zero
- \+/\- *lemma* is_algebraic_algebra_map
- \+ *lemma* is_algebraic_one
- \+ *lemma* is_algebraic_nat
- \+/\- *lemma* is_algebraic_algebra_map_of_is_algebraic
- \+/\- *lemma* is_integral.is_algebraic
- \+/\- *lemma* is_algebraic_algebra_map
- \+/\- *lemma* is_algebraic_algebra_map_of_is_algebraic



## [2022-03-21 05:20:44](https://github.com/leanprover-community/mathlib/commit/60af3bd)
feat(data/rat/denumerable): Make `mk_rat` into a simp lemma ([#12821](https://github.com/leanprover-community/mathlib/pull/12821))
#### Estimated changes
modified src/data/rat/denumerable.lean
- \+/\- *lemma* mk_rat
- \+/\- *lemma* mk_rat



## [2022-03-20 20:14:43](https://github.com/leanprover-community/mathlib/commit/656f749)
feat(analysis/locally_convex): define von Neumann boundedness ([#12449](https://github.com/leanprover-community/mathlib/pull/12449))
Define the von Neumann boundedness and show elementary properties, including that it defines a bornology.
#### Estimated changes
created src/analysis/locally_convex/bounded.lean
- \+ *lemma* is_vonN_bounded_empty
- \+ *lemma* is_vonN_bounded_iff
- \+ *lemma* is_vonN_bounded.subset
- \+ *lemma* is_vonN_bounded.union
- \+ *lemma* is_vonN_bounded.of_topological_space_le
- \+ *lemma* is_vonN_bounded_singleton
- \+ *lemma* is_vonN_bounded_covers
- \+ *lemma* is_bounded_iff_is_vonN_bounded
- \+ *def* is_vonN_bounded
- \+ *def* vonN_bornology

modified src/topology/bornology/basic.lean
- \+ *lemma* is_cobounded_of_bounded_iff
- \+ *lemma* is_bounded_of_bounded_iff



## [2022-03-20 15:25:50](https://github.com/leanprover-community/mathlib/commit/9502db1)
refactor(group_theory/group_action/basic): Golf definition of action on cosets ([#12823](https://github.com/leanprover-community/mathlib/pull/12823))
This PR golfs the definition of the left-multiplication action on left cosets.
I deleted `mul_left_cosets` since it's the same as `•` and has no API.
#### Estimated changes
modified src/group_theory/group_action/basic.lean
- \- *def* mul_left_cosets



## [2022-03-20 12:26:39](https://github.com/leanprover-community/mathlib/commit/f2fa1cf)
feat(category_theory/abelian/*): add some missing lemmas ([#12839](https://github.com/leanprover-community/mathlib/pull/12839))
#### Estimated changes
modified src/category_theory/abelian/exact.lean
- \+ *lemma* kernel.lift.inv

modified src/category_theory/abelian/homology.lean
- \+ *lemma* map_ι



## [2022-03-20 00:39:53](https://github.com/leanprover-community/mathlib/commit/cdd0572)
chore(ring_theory/algebraic): fix typo + golf ([#12834](https://github.com/leanprover-community/mathlib/pull/12834))
#### Estimated changes
modified src/ring_theory/algebraic.lean



## [2022-03-19 23:35:59](https://github.com/leanprover-community/mathlib/commit/6abfb1d)
feat(analysis/normed_space/spectrum): Prove the Gelfand-Mazur theorem ([#12787](https://github.com/leanprover-community/mathlib/pull/12787))
**Gelfand-Mazur theorem** For a complex Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse is given by selecting the (unique) element of `spectrum ℂ a`.
- [x] depends on: [#12132](https://github.com/leanprover-community/mathlib/pull/12132)
#### Estimated changes
modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* algebra_map_eq_of_mem



## [2022-03-19 21:04:04](https://github.com/leanprover-community/mathlib/commit/cd012fb)
chore(ring_theory/ideal): use `ideal.mul_mem_left` instead of `submodule.smul_mem` ([#12830](https://github.com/leanprover-community/mathlib/pull/12830))
In one place this saves one rewrite.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/polynomial/basic.lean



## [2022-03-19 19:33:01](https://github.com/leanprover-community/mathlib/commit/f120076)
feat(category_theory): (co)equalizers and (co)kernels when composing with monos/epis ([#12828](https://github.com/leanprover-community/mathlib/pull/12828))
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* has_equalizer_comp_mono
- \+ *lemma* has_coequalizer_epi_comp
- \+ *def* is_equalizer_comp_mono
- \+ *def* is_coequalizer_epi_comp

modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* is_kernel_comp_mono
- \+ *def* is_cokernel_epi_comp



## [2022-03-19 19:33:00](https://github.com/leanprover-community/mathlib/commit/49cd1cc)
refactor(analysis/seminorm): move topology induced by seminorms to its own file ([#12826](https://github.com/leanprover-community/mathlib/pull/12826))
Besides the copy and paste I removed the namespace `seminorm` from most parts (it is still there for the boundedness definitions and statements) and updated the module docstrings. No real code has changed.
#### Estimated changes
created src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* seminorm_basis_zero_iff
- \+ *lemma* seminorm_basis_zero_mem
- \+ *lemma* seminorm_basis_zero_singleton_mem
- \+ *lemma* seminorm_basis_zero_nonempty
- \+ *lemma* seminorm_basis_zero_intersect
- \+ *lemma* seminorm_basis_zero_zero
- \+ *lemma* seminorm_basis_zero_add
- \+ *lemma* seminorm_basis_zero_neg
- \+ *lemma* seminorm_basis_zero_smul_right
- \+ *lemma* seminorm_basis_zero_smul
- \+ *lemma* seminorm_basis_zero_smul_left
- \+ *lemma* is_bounded_const
- \+ *lemma* const_is_bounded
- \+ *lemma* is_bounded_sup
- \+ *lemma* with_seminorms_eq
- \+ *lemma* with_seminorms_of_nhds
- \+ *lemma* with_seminorms_of_has_basis
- \+ *lemma* continuous_from_bounded
- \+ *lemma* cont_with_seminorms_normed_space
- \+ *lemma* cont_normed_space_to_with_seminorms
- \+ *lemma* with_seminorms.to_locally_convex_space
- \+ *lemma* normed_space.to_locally_convex_space'
- \+ *def* seminorm_basis_zero
- \+ *def* seminorm_add_group_filter_basis
- \+ *def* seminorm_module_filter_basis
- \+ *def* is_bounded

modified src/analysis/seminorm.lean
- \- *lemma* seminorm_basis_zero_iff
- \- *lemma* seminorm_basis_zero_mem
- \- *lemma* seminorm_basis_zero_singleton_mem
- \- *lemma* seminorm_basis_zero_nonempty
- \- *lemma* seminorm_basis_zero_intersect
- \- *lemma* seminorm_basis_zero_zero
- \- *lemma* seminorm_basis_zero_add
- \- *lemma* seminorm_basis_zero_neg
- \- *lemma* seminorm_basis_zero_smul_right
- \- *lemma* seminorm_basis_zero_smul
- \- *lemma* seminorm_basis_zero_smul_left
- \- *lemma* is_bounded_const
- \- *lemma* const_is_bounded
- \- *lemma* is_bounded_sup
- \- *lemma* with_seminorms_eq
- \- *lemma* with_seminorms_of_nhds
- \- *lemma* with_seminorms_of_has_basis
- \- *lemma* continuous_from_bounded
- \- *lemma* cont_with_seminorms_normed_space
- \- *lemma* cont_normed_space_to_with_seminorms
- \- *lemma* with_seminorms.to_locally_convex_space
- \- *lemma* normed_space.to_locally_convex_space'
- \- *def* seminorm_basis_zero
- \- *def* seminorm_add_group_filter_basis
- \- *def* seminorm_module_filter_basis
- \- *def* is_bounded



## [2022-03-19 19:32:59](https://github.com/leanprover-community/mathlib/commit/2660d16)
feat(group_theory/group_action/basic): Right action of normalizer on left cosets ([#12822](https://github.com/leanprover-community/mathlib/pull/12822))
This PR adds the right action of the normalizer on left cosets.
#### Estimated changes
modified src/group_theory/group_action/basic.lean
- \+ *lemma* quotient'.smul_mk
- \+ *lemma* quotient'.smul_coe



## [2022-03-19 17:43:23](https://github.com/leanprover-community/mathlib/commit/48eacc6)
chore(*): update to lean 3.42.0c ([#12818](https://github.com/leanprover-community/mathlib/pull/12818))
#### Estimated changes
modified leanpkg.toml

modified src/tactic/interactive.lean

modified test/induction.lean
- \- *lemma* lt_lte
- \+ *def* lt_lte

modified test/lint.lean
- \- *lemma* foo3

modified test/lint_to_additive_doc.lean
- \- *lemma* foo
- \- *lemma* bar
- \- *lemma* baz
- \- *lemma* quux
- \- *lemma* no_to_additive
- \+ *def* foo
- \+ *def* bar
- \+ *def* baz
- \+ *def* quux
- \+ *def* no_to_additive

modified test/local_cache.lean



## [2022-03-19 14:49:29](https://github.com/leanprover-community/mathlib/commit/42dcf35)
chore(algebra/char_p/exp_char): golf char_eq_exp_char_iff ([#12825](https://github.com/leanprover-community/mathlib/pull/12825))
#### Estimated changes
modified src/algebra/char_p/exp_char.lean



## [2022-03-19 11:33:35](https://github.com/leanprover-community/mathlib/commit/3ba1c02)
feat(group_theory/subgroup/basic): Alternate version of `mem_normalizer_iff` ([#12814](https://github.com/leanprover-community/mathlib/pull/12814))
This PR adds an alternate version of `mem_normalizer_iff`, in terms of commuting rather than conjugation.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mem_normalizer_iff'



## [2022-03-19 11:33:34](https://github.com/leanprover-community/mathlib/commit/52b9b36)
feat(ring_theory/fractional_ideal): fractional ideal is one if and only if ideal is one ([#12813](https://github.com/leanprover-community/mathlib/pull/12813))
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean
- \+/\- *lemma* coe_ideal_injective
- \+/\- *lemma* coe_ideal_eq_zero_iff
- \+/\- *lemma* coe_ideal_ne_zero_iff
- \+/\- *lemma* coe_ideal_ne_zero
- \+ *lemma* coe_ideal_eq_one_iff
- \+/\- *lemma* coe_ideal_injective
- \+/\- *lemma* coe_ideal_eq_zero_iff
- \+/\- *lemma* coe_ideal_ne_zero_iff
- \+/\- *lemma* coe_ideal_ne_zero



## [2022-03-19 11:33:33](https://github.com/leanprover-community/mathlib/commit/245b614)
chore(measure_theory/measure): move subtraction to a new file ([#12809](https://github.com/leanprover-community/mathlib/pull/12809))
#### Estimated changes
modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \- *lemma* sub_def
- \- *lemma* sub_eq_zero_of_le
- \- *lemma* sub_apply
- \- *lemma* sub_add_cancel_of_le
- \- *lemma* sub_le
- \- *lemma* restrict_sub_eq_restrict_sub_restrict
- \- *lemma* sub_apply_eq_zero_of_restrict_le_restrict

created src/measure_theory/measure/sub.lean
- \+ *lemma* sub_def
- \+ *lemma* sub_eq_zero_of_le
- \+ *lemma* sub_apply
- \+ *lemma* sub_add_cancel_of_le
- \+ *lemma* sub_le
- \+ *lemma* restrict_sub_eq_restrict_sub_restrict
- \+ *lemma* sub_apply_eq_zero_of_restrict_le_restrict



## [2022-03-19 11:33:32](https://github.com/leanprover-community/mathlib/commit/dae6155)
chore(number_theory/primorial): golf a proof ([#12807](https://github.com/leanprover-community/mathlib/pull/12807))
Use a new lemma to golf a proof.
#### Estimated changes
modified src/number_theory/primorial.lean



## [2022-03-19 11:33:31](https://github.com/leanprover-community/mathlib/commit/1d18309)
feat(linear_algebra/determinant): no need for `is_domain` ([#12805](https://github.com/leanprover-community/mathlib/pull/12805))
Nontriviality is all that was actually used, and in some cases the statement is already vacuous in the trivial case.
#### Estimated changes
modified src/linear_algebra/determinant.lean
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* is_unit_det
- \+/\- *lemma* linear_equiv.det_mul_det_symm
- \+/\- *lemma* linear_equiv.det_symm_mul_det
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* det_comm'
- \+/\- *lemma* det_conj
- \+/\- *lemma* is_unit_det
- \+/\- *lemma* linear_equiv.det_mul_det_symm
- \+/\- *lemma* linear_equiv.det_symm_mul_det
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *def* index_equiv_of_inv

modified src/linear_algebra/matrix/to_linear_equiv.lean

modified src/linear_algebra/orientation.lean
- \+/\- *lemma* map_orientation_eq_det_inv_smul
- \+/\- *lemma* map_orientation_eq_det_inv_smul

modified src/ring_theory/norm.lean
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis
- \+/\- *lemma* norm_eq_zero_iff_of_basis
- \+/\- *lemma* norm_ne_zero_iff_of_basis

modified src/topology/algebra/module/basic.lean



## [2022-03-19 11:33:30](https://github.com/leanprover-community/mathlib/commit/ef69547)
feat(group_theory/finiteness): Define the minimum number of generators ([#12765](https://github.com/leanprover-community/mathlib/pull/12765))
The PR adds a definition of the minimum number of generators, which will be needed for a statement of Schreier's lemma.
#### Estimated changes
modified src/group_theory/finiteness.lean
- \+ *lemma* group.fg_iff'
- \+ *lemma* group.rank_spec
- \+ *lemma* group.rank_le
- \+ *def* group.rank



## [2022-03-19 09:56:20](https://github.com/leanprover-community/mathlib/commit/ee4472b)
feat(group_theory/group_action/embedding): group actions apply on the codomain of embeddings ([#12798](https://github.com/leanprover-community/mathlib/pull/12798))
#### Estimated changes
created src/group_theory/group_action/embedding.lean
- \+ *lemma* smul_def
- \+ *lemma* smul_apply
- \+ *lemma* coe_smul



## [2022-03-19 09:56:19](https://github.com/leanprover-community/mathlib/commit/c9fc9bf)
refactor(order/filter/pointwise): Cleanup ([#12789](https://github.com/leanprover-community/mathlib/pull/12789))
* Reduce typeclass assumptions from `monoid` to `has_mul`
* Turn lemmas into instances
* Use hom classes rather than concrete hom types
* Golf
#### Estimated changes
modified src/algebra/pointwise.lean
- \+/\- *lemma* image_mul
- \+/\- *lemma* preimage_mul_preimage_subset
- \+/\- *lemma* image_mul
- \+/\- *lemma* preimage_mul_preimage_subset

modified src/order/filter/pointwise.lean
- \+/\- *lemma* mem_one
- \+ *lemma* one_mem_one
- \+/\- *lemma* mem_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* ne_bot.mul
- \+/\- *lemma* comap_mul_comap_le
- \+/\- *lemma* tendsto.mul_mul
- \+/\- *lemma* mem_one
- \+/\- *lemma* mem_mul
- \+/\- *lemma* mul_mem_mul
- \+/\- *lemma* ne_bot.mul
- \+/\- *lemma* comap_mul_comap_le
- \+/\- *lemma* tendsto.mul_mul
- \+/\- *def* map_monoid_hom
- \+/\- *def* map_monoid_hom

modified src/ring_theory/graded_algebra/homogeneous_ideal.lean



## [2022-03-19 09:56:18](https://github.com/leanprover-community/mathlib/commit/2b6b9ff)
feat(category_theory/abelian/derived): add left_derived_zero_iso_self ([#12403](https://github.com/leanprover-community/mathlib/pull/12403))
We add `left_derived_zero_iso_self`: the natural isomorphism `(F.left_derived 0) ≅ F` if `preserves_finite_colimits F`.
From lean-liquid
#### Estimated changes
modified src/algebra/homology/exact.lean
- \+ *lemma* preadditive.exact_of_iso_of_exact'

created src/category_theory/abelian/derived.lean
- \+ *lemma* preserves_exact_of_preserves_finite_colimits_of_epi
- \+ *lemma* exact_of_map_projective_resolution
- \+ *lemma* left_derived_zero_to_self_app_comp_inv
- \+ *lemma* left_derived_zero_to_self_app_inv_comp
- \+ *lemma* left_derived_zero_to_self_natural
- \+ *def* left_derived_zero_to_self_app
- \+ *def* left_derived_zero_to_self_app_inv
- \+ *def* left_derived_zero_to_self_app_iso
- \+ *def* left_derived_zero_iso_self

modified src/category_theory/abelian/exact.lean
- \+ *lemma* cokernel.desc.inv



## [2022-03-19 08:22:18](https://github.com/leanprover-community/mathlib/commit/4c60258)
chore(ring_theory/dedekind_domain/ideal): golf ([#12737](https://github.com/leanprover-community/mathlib/pull/12737))
#### Estimated changes
modified src/data/equiv/ring.lean
- \+ *lemma* to_equiv_eq_coe
- \+ *lemma* coe_to_equiv

modified src/ring_theory/dedekind_domain/ideal.lean



## [2022-03-19 03:04:31](https://github.com/leanprover-community/mathlib/commit/128c096)
chore(scripts): update nolints.txt ([#12816](https://github.com/leanprover-community/mathlib/pull/12816))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-19 01:22:50](https://github.com/leanprover-community/mathlib/commit/7764c60)
feat(*/sort): sorting empty sets/singletons ([#12801](https://github.com/leanprover-community/mathlib/pull/12801))
#### Estimated changes
modified src/data/finset/sort.lean
- \+ *theorem* sort_empty
- \+ *theorem* sort_singleton

modified src/data/list/sort.lean
- \+ *theorem* merge_sort_nil
- \+ *theorem* merge_sort_singleton

modified src/data/multiset/sort.lean
- \+ *theorem* sort_zero
- \+ *theorem* sort_singleton



## [2022-03-18 21:54:51](https://github.com/leanprover-community/mathlib/commit/d04fff9)
feat(topology/{order,separation}): several lemmas from an old branch ([#12794](https://github.com/leanprover-community/mathlib/pull/12794))
* add `mem_nhds_discrete`;
* replace the proof of `is_open_implies_is_open_iff` by `iff.rfl`;
* add lemmas about `separated`.
#### Estimated changes
modified src/topology/order.lean
- \+ *lemma* mem_nhds_discrete

modified src/topology/separation.lean
- \+ *lemma* preimage
- \+ *lemma* disjoint_closure_left
- \+ *lemma* disjoint_closure_right
- \+ *lemma* mono



## [2022-03-18 20:21:42](https://github.com/leanprover-community/mathlib/commit/7f1ba1a)
feat(algebra/char_p/two): add `simp` attribute to some lemmas involving characteristic two identities ([#12800](https://github.com/leanprover-community/mathlib/pull/12800))
I hope that these `simp` attributes will make working with `char_p R 2` smooth!
I felt clumsy with this section, so hopefully this is an improvement.
#### Estimated changes
modified src/algebra/char_p/two.lean
- \+/\- *lemma* add_self_eq_zero
- \+/\- *lemma* bit0_eq_zero
- \+ *lemma* bit0_apply_eq_zero
- \+/\- *lemma* bit1_eq_one
- \+ *lemma* bit1_apply_eq_one
- \+/\- *lemma* neg_eq
- \+/\- *lemma* sub_eq_add
- \+/\- *lemma* add_self_eq_zero
- \+/\- *lemma* bit0_eq_zero
- \+/\- *lemma* bit1_eq_one
- \+/\- *lemma* neg_eq
- \+/\- *lemma* sub_eq_add



## [2022-03-18 20:21:41](https://github.com/leanprover-community/mathlib/commit/e282089)
feat(linear_algebra/sesquilinear_form): preliminary results for nondegeneracy ([#12269](https://github.com/leanprover-community/mathlib/pull/12269))
Several lemmas needed to define nondegenerate bilinear forms and show that the canonical pairing of the algebraic dual is nondegenerate.
Add domain restriction of bilinear maps in the second component and in both compenents.
Some type-class generalizations for symmetric, alternating, and reflexive sesquilinear forms.
#### Estimated changes
modified src/algebra/quandle.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/bilinear_map.lean
- \+ *lemma* congr_fun₂
- \+ *lemma* flip_flip
- \+ *lemma* dom_restrict₂_apply
- \+ *lemma* dom_restrict₁₂_apply
- \+ *lemma* ext_basis
- \+ *lemma* sum_repr_mul_repr_mul
- \+ *def* dom_restrict₂
- \+ *def* dom_restrict₁₂

modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* mk_span_singleton_apply'

modified src/linear_algebra/matrix/bilinear_form.lean

modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* is_ortho_def
- \+ *lemma* is_ortho_flip
- \+/\- *lemma* is_Ortho_def
- \+ *lemma* is_Ortho_flip
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+ *lemma* dom_restrict_symm
- \+ *lemma* is_symm_iff_eq_flip
- \+ *lemma* is_alt_iff_eq_neg_flip
- \+/\- *lemma* is_ortho_def
- \+/\- *lemma* is_Ortho_def
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+/\- *def* is_Ortho
- \+/\- *def* is_symm
- \+/\- *def* is_Ortho
- \+/\- *def* is_symm



## [2022-03-18 20:21:40](https://github.com/leanprover-community/mathlib/commit/076490a)
feat(group_theory/nilpotent): the is_nilpotent_of_finite_tfae theorem ([#11835](https://github.com/leanprover-community/mathlib/pull/11835))
#### Estimated changes
modified src/group_theory/nilpotent.lean
- \+ *theorem* is_nilpotent_of_finite_tfae



## [2022-03-18 20:21:38](https://github.com/leanprover-community/mathlib/commit/8c89ae6)
feat(ring_theory/unique_factorization_domain): some lemmas relating shapes of factorisations ([#9345](https://github.com/leanprover-community/mathlib/pull/9345))
Given elements `a`, `b` in a `unique_factorization_monoid`, if there is an order-preserving bijection between the sets of factors of `associates.mk a` and `associates.mk b` then the prime factorisations of `a` and `b` have the same shape.
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* associates.is_atom_iff
- \+ *lemma* dvd_prime_pow

modified src/algebra/squarefree.lean
- \+ *lemma* finite_prime_left

created src/ring_theory/chain_of_divisors.lean
- \+ *lemma* exists_chain_of_prime_pow
- \+ *lemma* element_of_chain_not_is_unit_of_index_ne_zero
- \+ *lemma* first_of_chain_is_unit
- \+ *lemma* second_of_chain_is_irreducible
- \+ *lemma* eq_second_of_chain_of_prime_dvd
- \+ *lemma* card_subset_divisors_le_length_of_chain
- \+ *lemma* element_of_chain_eq_pow_second_of_chain
- \+ *lemma* eq_pow_second_of_chain_of_has_chain
- \+ *lemma* is_prime_pow_of_has_chain
- \+ *lemma* pow_image_of_prime_by_factor_order_iso_dvd
- \+ *lemma* multiplicity_prime_le_multiplicity_image_by_factor_order_iso

modified src/ring_theory/ideal/operations.lean
- \+ *theorem* comap_le_comap_iff_of_surjective

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* exists_associated_prime_pow_of_unique_normalized_factor
- \+ *theorem* normalized_factors_of_irreducible_pow



## [2022-03-18 18:32:32](https://github.com/leanprover-community/mathlib/commit/0c52d3b)
doc(src/tactic/doc_commands): typo “between” → “better” ([#12804](https://github.com/leanprover-community/mathlib/pull/12804))
#### Estimated changes
modified src/tactic/doc_commands.lean



## [2022-03-18 18:32:31](https://github.com/leanprover-community/mathlib/commit/d3703fe)
doc(archive/100-theorems-list/9_area_of_a_circle): fix `×` ([#12803](https://github.com/leanprover-community/mathlib/pull/12803))
this file used to have the category theory `\cross` as opposed to `\x`
#### Estimated changes
modified archive/100-theorems-list/9_area_of_a_circle.lean



## [2022-03-18 18:32:30](https://github.com/leanprover-community/mathlib/commit/f4e7f82)
chore(model_theory/definability): Change variable order in definability ([#12802](https://github.com/leanprover-community/mathlib/pull/12802))
Changes `first_order.language.definable` and `first_order.language.definable_set` to `set.definable` and `set.definable_set`.
Makes `set.definable` a `def` rather than a `structure`.
#### Estimated changes
modified docs/overview.yaml

modified src/model_theory/definability.lean
- \+/\- *lemma* definable_empty
- \+/\- *lemma* definable_univ
- \+/\- *lemma* definable.inter
- \+/\- *lemma* definable.union
- \+/\- *lemma* definable.compl
- \+/\- *lemma* definable.sdiff
- \+/\- *lemma* definable_empty
- \+/\- *lemma* definable_univ
- \+/\- *lemma* definable.inter
- \+/\- *lemma* definable.union
- \+/\- *lemma* definable.compl
- \+/\- *lemma* definable.sdiff
- \+ *def* definable
- \+/\- *def* definable₁
- \+/\- *def* definable₂
- \+/\- *def* definable_set
- \+/\- *def* definable₁
- \+/\- *def* definable₂
- \+/\- *def* definable_set



## [2022-03-18 18:32:29](https://github.com/leanprover-community/mathlib/commit/f6e85fc)
feat(order/rel_iso): Add `subrel` instances ([#12758](https://github.com/leanprover-community/mathlib/pull/12758))
#### Estimated changes
modified src/order/rel_iso.lean



## [2022-03-18 18:32:28](https://github.com/leanprover-community/mathlib/commit/fdd7e98)
feat(set_theory/*): Redefine `sup f` as `supr f` ([#12657](https://github.com/leanprover-community/mathlib/pull/12657))
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/linear_algebra/dimension.lean

modified src/measure_theory/card_measurable_space.lean

modified src/set_theory/cardinal.lean
- \+ *theorem* bdd_above_range
- \+ *theorem* sup_le_iff
- \+/\- *theorem* sup_le
- \- *theorem* nonempty_sup
- \+/\- *theorem* sup_le

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* Sup_eq_sup
- \+ *theorem* bdd_above_range
- \+ *theorem* sup_le_iff
- \+/\- *theorem* sup_le
- \+ *theorem* ne_sup_iff_lt_sup
- \+ *theorem* Sup_eq_bsup
- \+ *theorem* bsup_le_iff
- \+/\- *theorem* bsup_le
- \+ *theorem* lsub_le_iff
- \+/\- *theorem* lsub_le
- \+ *theorem* blsub_le_iff
- \+/\- *theorem* blsub_le
- \+ *theorem* nfp_le_iff
- \+/\- *theorem* nfp_le
- \- *theorem* sup_nonempty
- \+/\- *theorem* sup_le
- \- *theorem* lt_sup_of_ne_sup
- \+/\- *theorem* bsup_le
- \+/\- *theorem* lsub_le
- \+/\- *theorem* blsub_le
- \+/\- *theorem* nfp_le

modified src/set_theory/ordinal_topology.lean

modified src/set_theory/principal.lean



## [2022-03-18 18:32:27](https://github.com/leanprover-community/mathlib/commit/290ad75)
feat(model_theory/terms_and_formulas): Atomic, Quantifier-Free, and Prenex Formulas ([#12557](https://github.com/leanprover-community/mathlib/pull/12557))
Provides a few induction principles for formulas
Defines atomic formulas with `first_order.language.bounded_formula.is_atomic`
Defines quantifier-free formulas with `first_order.language.bounded_formula.is_qf`
Defines `first_order.language.bounded_formula.is_prenex` indicating that a formula is in prenex normal form.
#### Estimated changes
modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* is_atomic.relabel
- \+ *lemma* is_atomic.is_qf
- \+ *lemma* is_qf_bot
- \+ *lemma* is_qf.not
- \+ *lemma* is_qf.relabel
- \+ *lemma* is_qf.is_prenex
- \+ *lemma* is_atomic.is_prenex
- \+ *lemma* is_prenex.induction_on_all_not
- \+ *lemma* is_prenex.relabel
- \+ *lemma* is_qf.induction_on_sup_not
- \+ *lemma* is_qf.induction_on_inf_not



## [2022-03-18 18:32:25](https://github.com/leanprover-community/mathlib/commit/d17ecf9)
feat(category_theory/abelian) : injective resolutions of an object in a category with enough injectives ([#12545](https://github.com/leanprover-community/mathlib/pull/12545))
This pr dualises `src/category_theory/preadditive/projective_resolution.lean`. But since half of the file requires `abelian` assumption, I moved it to `src/category_theory/abelian/*`. The reason it needs `abelian` assumption is because I want class inference to deduce `exact f g` from `exact g.op f.op`.
#### Estimated changes
modified src/category_theory/abelian/injective_resolution.lean
- \+ *lemma* exact_f_d
- \+ *def* injective_resolutions
- \+ *def* of_cocomplex
- \+ *def* of



## [2022-03-18 16:51:05](https://github.com/leanprover-community/mathlib/commit/80b8d19)
feat(model_theory/terms_and_formulas): Language maps act on terms, formulas, sentences, and theories ([#12609](https://github.com/leanprover-community/mathlib/pull/12609))
Defines the action of language maps on terms, formulas, sentences, and theories
Shows that said action commutes with realization
#### Estimated changes
modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* Lhom.realize_on_term
- \+ *lemma* mem_on_Theory
- \+ *lemma* realize_on_bounded_formula
- \+ *lemma* Lhom.realize_on_formula
- \+ *lemma* Lhom.realize_on_sentence
- \+ *lemma* Lhom.on_Theory_model
- \+ *def* Lhom.on_term
- \+ *def* on_bounded_formula
- \+ *def* on_formula
- \+ *def* on_sentence
- \+ *def* on_Theory



## [2022-03-18 16:51:04](https://github.com/leanprover-community/mathlib/commit/bf690dd)
feat(archive/100-theorems-list): add proof of thm 81 ([#7274](https://github.com/leanprover-community/mathlib/pull/7274))
#### Estimated changes
created archive/100-theorems-list/81_sum_of_prime_reciprocals_diverges.lean
- \+ *lemma* sum_lt_half_of_not_tendsto
- \+ *lemma* range_sdiff_eq_bUnion
- \+ *lemma* card_le_mul_sum
- \+ *lemma* card_le_two_pow
- \+ *lemma* card_le_two_pow_mul_sqrt
- \+ *theorem* real.tendsto_sum_one_div_prime_at_top

modified docs/100.yaml

modified src/data/finset/card.lean
- \+ *lemma* card_sdiff_add_card_eq_card



## [2022-03-18 15:25:55](https://github.com/leanprover-community/mathlib/commit/b49bc77)
feat(data/nat/prime): add two lemmas with nat.primes, mul and dvd ([#12780](https://github.com/leanprover-community/mathlib/pull/12780))
These lemmas are close to available lemmas, but I could not actually find them.
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* prime_mul_iff
- \+ *lemma* prime.dvd_iff_eq



## [2022-03-18 14:52:26](https://github.com/leanprover-community/mathlib/commit/5a547aa)
fix(ring_theory/power_series/basic): remove duplicate instance ([#12744](https://github.com/leanprover-community/mathlib/pull/12744))
#### Estimated changes
modified src/ring_theory/power_series/basic.lean



## [2022-03-18 14:52:25](https://github.com/leanprover-community/mathlib/commit/14ee5e0)
feat(number_theory/arithmetic_function): add eq of multiplicative functions ([#12689](https://github.com/leanprover-community/mathlib/pull/12689))
To show that two multiplicative functions are equal, it suffices to show
that they are equal on prime powers. This is a commonly used strategy
when two functions are known to be multiplicative (e.g., they're both
Dirichlet convolutions of simpler multiplicative functions).
This will be used in several ongoing commits to prove asymptotics for
squarefree numbers.
#### Estimated changes
modified src/number_theory/arithmetic_function.lean
- \+ *lemma* eq_iff_eq_on_prime_powers



## [2022-03-18 13:10:58](https://github.com/leanprover-community/mathlib/commit/ee8db20)
feat(measure_theory/group/action): add `null_measurable_set.smul` ([#12793](https://github.com/leanprover-community/mathlib/pull/12793))
Also add `null_measurable_set.preimage` and `ae_disjoint.preimage`.
#### Estimated changes
modified src/measure_theory/group/action.lean
- \+ *lemma* null_measurable_set.smul

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* null_measurable_set.preimage
- \+ *lemma* ae_disjoint.preimage



## [2022-03-18 13:10:57](https://github.com/leanprover-community/mathlib/commit/2541387)
refactor(data/list/big_operators): review API ([#12782](https://github.com/leanprover-community/mathlib/pull/12782))
* merge `prod_monoid` into `big_operators`;
* review typeclass assumptions in some lemmas;
* use `to_additive` in more lemmas.
#### Estimated changes
modified src/algebra/big_operators/multiset.lean

modified src/algebra/graded_monoid.lean

modified src/data/list/big_operators.lean
- \+ *lemma* prod_eq_pow_card
- \+ *lemma* prod_commute
- \+ *lemma* prod_le_prod'
- \+ *lemma* prod_lt_prod'
- \+ *lemma* prod_lt_prod_of_ne_nil
- \+ *lemma* prod_le_pow_card
- \+ *lemma* pow_card_le_prod
- \+ *lemma* exists_lt_of_prod_lt'
- \+ *lemma* exists_le_of_prod_le'
- \+/\- *lemma* one_le_prod_of_one_le
- \+ *lemma* eq_of_prod_take_eq
- \+ *lemma* monotone_prod_take
- \+/\- *lemma* prod_eq_one_iff
- \+/\- *lemma* sum_map_mul_left
- \+/\- *lemma* sum_map_mul_right
- \- *lemma* eq_of_sum_take_eq
- \- *lemma* monotone_sum_take
- \+/\- *lemma* one_le_prod_of_one_le
- \+/\- *lemma* prod_eq_one_iff
- \- *lemma* exists_lt_of_sum_lt
- \- *lemma* exists_le_of_sum_le
- \+/\- *lemma* sum_map_mul_left
- \+/\- *lemma* sum_map_mul_right
- \+ *theorem* prod_repeat

deleted src/data/list/prod_monoid.lean
- \- *lemma* prod_eq_pow_card
- \- *lemma* prod_le_pow_card
- \- *lemma* prod_commute
- \- *theorem* prod_repeat



## [2022-03-18 13:10:56](https://github.com/leanprover-community/mathlib/commit/241d63d)
chore(algebraic_geometry/prime_spectrum/basic): remove TODO ([#12768](https://github.com/leanprover-community/mathlib/pull/12768))
Sober topological spaces has been defined and it has been proven (in this file) that prime spectrum is sober
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum/basic.lean



## [2022-03-18 12:36:36](https://github.com/leanprover-community/mathlib/commit/cfa7f6a)
feat(group_theory/index): Intersection of finite index subgroups ([#12776](https://github.com/leanprover-community/mathlib/pull/12776))
This PR proves that if `H` and `K` are of finite index in `L`, then so is `H ⊓ K`.
#### Estimated changes
modified src/group_theory/index.lean
- \+ *lemma* relindex_inf_ne_zero
- \+ *lemma* index_inf_ne_zero



## [2022-03-18 10:11:28](https://github.com/leanprover-community/mathlib/commit/5ecd27a)
refactor(topology/algebra/field): make `topological_division_ring` extend `has_continuous_inv₀` ([#12778](https://github.com/leanprover-community/mathlib/pull/12778))
Topological division ring had been rolling its own `continuous_inv` field which was almost identical to the `continuous_at_inv₀` field of `has_continuous_inv₀`. Here we refactor so that `topological_division_ring` extends `has_continuous_inv₀` instead.
- [x] depends on: [#12770](https://github.com/leanprover-community/mathlib/pull/12770)
#### Estimated changes
modified src/topology/algebra/field.lean

modified src/topology/algebra/uniform_field.lean

modified src/topology/algebra/valued_field.lean



## [2022-03-18 01:33:57](https://github.com/leanprover-community/mathlib/commit/a7cad67)
doc(overview): some additions to the Analysis section ([#12791](https://github.com/leanprover-community/mathlib/pull/12791))
#### Estimated changes
modified docs/overview.yaml



## [2022-03-18 00:28:28](https://github.com/leanprover-community/mathlib/commit/a32d58b)
feat(analysis/*): generalize `set_smul_mem_nhds_zero` to topological vector spaces ([#12779](https://github.com/leanprover-community/mathlib/pull/12779))
The lemma holds for arbitrary topological vector spaces and has nothing to do with normed spaces.
#### Estimated changes
modified src/analysis/normed_space/pointwise.lean
- \- *lemma* set_smul_mem_nhds_zero
- \- *lemma* set_smul_mem_nhds_zero_iff

modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* set_smul_mem_nhds_smul
- \+ *lemma* set_smul_mem_nhds_smul_iff
- \+ *lemma* set_smul_mem_nhds_zero_iff



## [2022-03-18 00:28:27](https://github.com/leanprover-community/mathlib/commit/adcfc58)
chore(data/matrix/block): Do not print `matrix.from_blocks` with dot notation ([#12774](https://github.com/leanprover-community/mathlib/pull/12774))
`A.from_blocks B C D` is weird and asymmetric compared to `from_blocks A B C D`. In future we might want to introduce notation.
#### Estimated changes
modified src/data/matrix/block.lean



## [2022-03-17 22:40:49](https://github.com/leanprover-community/mathlib/commit/cf8c5ff)
feat(algebra/pointwise): Subtraction/division of sets ([#12694](https://github.com/leanprover-community/mathlib/pull/12694))
Define pointwise subtraction/division on `set`.
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* image2_div
- \+ *lemma* mem_div
- \+ *lemma* div_mem_div
- \+ *lemma* div_subset_div
- \+ *lemma* image_div_prod
- \+ *lemma* empty_div
- \+ *lemma* div_empty
- \+ *lemma* div_singleton
- \+ *lemma* singleton_div
- \+ *lemma* singleton_div_singleton
- \+ *lemma* div_subset_div_left
- \+ *lemma* div_subset_div_right
- \+ *lemma* union_div
- \+ *lemma* div_union
- \+ *lemma* inter_div_subset
- \+ *lemma* div_inter_subset
- \+ *lemma* Union_div_left_image
- \+ *lemma* Union_div_right_image
- \+ *lemma* Union_div
- \+ *lemma* div_Union
- \+ *lemma* Union₂_div
- \+ *lemma* div_Union₂
- \+ *lemma* Inter_div_subset
- \+ *lemma* div_Inter_subset
- \+ *lemma* Inter₂_div_subset
- \+ *lemma* div_Inter₂_subset



## [2022-03-17 22:40:48](https://github.com/leanprover-community/mathlib/commit/32e5b6b)
feat(model_theory/terms_and_formulas): Casting and lifting terms and formulas ([#12467](https://github.com/leanprover-community/mathlib/pull/12467))
Defines `bounded_formula.cast_le`, which maps the `fin`-indexed variables with `fin.cast_le`
Defines `term.lift_at` and `bounded_formula.lift_at`, which raise `fin`-indexed variables above a certain threshold
#### Estimated changes
modified src/data/fin/basic.lean
- \+ *lemma* cast_zero
- \+ *lemma* cast_last
- \+ *lemma* cast_le_of_eq
- \+ *lemma* cast_cast_succ
- \+ *lemma* add_nat_one

modified src/data/sum/basic.lean
- \+ *lemma* elim_comp_map

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_lift_at
- \+ *lemma* realize_cast_le_of_eq
- \+ *lemma* realize_lift_at
- \+ *lemma* realize_lift_at_one
- \+ *lemma* realize_lift_at_one_self
- \+ *lemma* realize_all_lift_at_one_self
- \+ *lemma* semantically_equivalent_all_lift_at
- \+ *def* lift_at
- \+ *def* cast_le
- \+ *def* lift_at



## [2022-03-17 22:40:47](https://github.com/leanprover-community/mathlib/commit/a26dfc4)
feat(analysis/normed_space/basic): add `normed_division_ring` ([#12132](https://github.com/leanprover-community/mathlib/pull/12132))
This defines normed division rings and generalizes some of the lemmas that applied to normed fields instead to normed division rings.
This breaks one `ac_refl`; although this could be resolved by using `simp only {canonize_instances := tt}` first, it's easier to just tweak the proof.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/normed/normed_field.lean
- \+/\- *lemma* norm_prod
- \+/\- *lemma* nnnorm_prod
- \+/\- *lemma* norm_prod
- \+/\- *lemma* nnnorm_prod

modified src/analysis/quaternion.lean
- \- *lemma* norm_mul



## [2022-03-17 18:31:29](https://github.com/leanprover-community/mathlib/commit/2cb5edb)
chore(topology/algebra/group_with_zero): mark `has_continuous_inv₀` as a `Prop` ([#12770](https://github.com/leanprover-community/mathlib/pull/12770))
Since the type was not explicitly given, Lean marked this as a `Type`.
#### Estimated changes
modified src/topology/algebra/group_with_zero.lean



## [2022-03-17 18:31:28](https://github.com/leanprover-community/mathlib/commit/3e6e34e)
feat(linear_algebra/matrix): The Weinstein–Aronszajn identity ([#12767](https://github.com/leanprover-community/mathlib/pull/12767))
Notably this includes the proof of the determinant of a block matrix, which we didn't seem to have in the general case.
This also renames some of the lemmas about determinants of block matrices, and adds some missing API for `inv_of` on matrices.
There's some discussion at https://math.stackexchange.com/q/4105846/1896 about whether this name is appropriate, and whether it should be called "Sylvester's determinant theorem" instead.
#### Estimated changes
modified src/linear_algebra/matrix/block.lean

modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* det_from_blocks_zero₂₁
- \+ *lemma* det_from_blocks_zero₁₂
- \- *lemma* upper_two_block_triangular_det
- \- *lemma* lower_two_block_triangular_det
- \- *lemma* det_one_add_col_mul_row

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* det_from_blocks₁₁
- \+ *lemma* det_from_blocks_one₁₁
- \+ *lemma* det_from_blocks₂₂
- \+ *lemma* det_from_blocks_one₂₂
- \+ *lemma* det_one_add_mul_comm
- \+ *lemma* det_mul_add_one_comm
- \+ *lemma* det_one_sub_mul_comm
- \+ *lemma* det_one_add_col_mul_row



## [2022-03-17 18:31:27](https://github.com/leanprover-community/mathlib/commit/6bfbb49)
docs(algebra/order/floor): Update floor_semiring docs to reflect it's just an ordered_semiring ([#12756](https://github.com/leanprover-community/mathlib/pull/12756))
The docs say that `floor_semiring` is a linear ordered semiring, but it is only an `ordered_semiring` in the code. Change the docs to reflect this fact.
#### Estimated changes
modified src/algebra/order/floor.lean



## [2022-03-17 18:31:26](https://github.com/leanprover-community/mathlib/commit/ca80c8b)
feat(data/nat/sqrt_norm_num): norm_num extension for sqrt ([#12735](https://github.com/leanprover-community/mathlib/pull/12735))
Inspired by https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/2.20is.20not.20a.20square . The norm_num extension has to go in a separate file from `data.nat.sqrt` because `data.nat.sqrt` is a dependency of `norm_num`.
#### Estimated changes
modified src/data/nat/prime.lean

created src/data/nat/sqrt_norm_num.lean
- \+ *lemma* is_sqrt

modified test/norm_num_ext.lean



## [2022-03-17 18:31:25](https://github.com/leanprover-community/mathlib/commit/e944a99)
feat(algebraic_geometry/projective_spectrum) : lemmas about `vanishing_ideal` and `zero_locus` ([#12730](https://github.com/leanprover-community/mathlib/pull/12730))
This pr mimics the corresponding construction in `Spec`; other than `projective_spectrum.basic_open_eq_union_of_projection` everything else is a direct copy.
#### Estimated changes
modified src/algebraic_geometry/projective_spectrum/topology.lean
- \+ *lemma* gc_ideal
- \+ *lemma* gc_set
- \+ *lemma* gc_homogeneous_ideal
- \+ *lemma* subset_zero_locus_iff_subset_vanishing_ideal
- \+ *lemma* subset_vanishing_ideal_zero_locus
- \+ *lemma* ideal_le_vanishing_ideal_zero_locus
- \+ *lemma* homogeneous_ideal_le_vanishing_ideal_zero_locus
- \+ *lemma* subset_zero_locus_vanishing_ideal
- \+ *lemma* zero_locus_anti_mono
- \+ *lemma* zero_locus_anti_mono_ideal
- \+ *lemma* zero_locus_anti_mono_homogeneous_ideal
- \+ *lemma* vanishing_ideal_anti_mono
- \+ *lemma* zero_locus_bot
- \+ *lemma* zero_locus_singleton_zero
- \+ *lemma* zero_locus_empty
- \+ *lemma* vanishing_ideal_univ
- \+ *lemma* zero_locus_empty_of_one_mem
- \+ *lemma* zero_locus_singleton_one
- \+ *lemma* zero_locus_univ
- \+ *lemma* zero_locus_sup_ideal
- \+ *lemma* zero_locus_sup_homogeneous_ideal
- \+ *lemma* zero_locus_union
- \+ *lemma* vanishing_ideal_union
- \+ *lemma* zero_locus_supr_ideal
- \+ *lemma* zero_locus_supr_homogeneous_ideal
- \+ *lemma* zero_locus_Union
- \+ *lemma* zero_locus_bUnion
- \+ *lemma* vanishing_ideal_Union
- \+ *lemma* zero_locus_inf
- \+ *lemma* union_zero_locus
- \+ *lemma* zero_locus_mul_ideal
- \+ *lemma* zero_locus_mul_homogeneous_ideal
- \+ *lemma* zero_locus_singleton_mul
- \+ *lemma* zero_locus_singleton_pow
- \+ *lemma* sup_vanishing_ideal_le
- \+ *lemma* mem_compl_zero_locus_iff_not_mem
- \+ *lemma* is_open_iff
- \+ *lemma* is_closed_iff_zero_locus
- \+ *lemma* is_closed_zero_locus
- \+ *lemma* zero_locus_vanishing_ideal_eq_closure
- \+ *lemma* vanishing_ideal_closure
- \+ *lemma* mem_basic_open
- \+ *lemma* mem_coe_basic_open
- \+ *lemma* is_open_basic_open
- \+ *lemma* basic_open_eq_zero_locus_compl
- \+ *lemma* basic_open_one
- \+ *lemma* basic_open_zero
- \+ *lemma* basic_open_mul
- \+ *lemma* basic_open_mul_le_left
- \+ *lemma* basic_open_mul_le_right
- \+ *lemma* basic_open_pow
- \+ *lemma* basic_open_eq_union_of_projection
- \+ *lemma* is_topological_basis_basic_opens
- \+ *lemma* as_ideal_le_as_ideal
- \+ *lemma* as_ideal_lt_as_ideal
- \+ *lemma* le_iff_mem_closure
- \+ *def* basic_open



## [2022-03-17 17:30:04](https://github.com/leanprover-community/mathlib/commit/a1bdadd)
chore(topology/metric_space/hausdorff_distance): move two lemmas ([#12771](https://github.com/leanprover-community/mathlib/pull/12771))
Remove the dependence of `topology/metric_space/hausdorff_distance` on `analysis.normed_space.basic`, by moving out two lemmas.
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/riesz_lemma.lean
- \+ *lemma* metric.closed_ball_inf_dist_compl_subset_closure'
- \+ *lemma* metric.closed_ball_inf_dist_compl_subset_closure

modified src/topology/metric_space/hausdorff_distance.lean
- \- *lemma* closed_ball_inf_dist_compl_subset_closure'
- \- *lemma* closed_ball_inf_dist_compl_subset_closure

modified src/topology/metric_space/pi_nat.lean

modified src/topology/metric_space/polish.lean



## [2022-03-17 11:06:31](https://github.com/leanprover-community/mathlib/commit/11b2f36)
feat(algebraic_topology/fundamental_groupoid): Fundamental groupoid of punit ([#12757](https://github.com/leanprover-community/mathlib/pull/12757))
Proves the equivalence of the fundamental groupoid of punit and punit
#### Estimated changes
created src/algebraic_topology/fundamental_groupoid/punit.lean
- \+ *def* punit_equiv_discrete_punit



## [2022-03-17 11:06:30](https://github.com/leanprover-community/mathlib/commit/cd196a8)
feat(group_theory/order_of_element): 1 is finite order, as is g⁻¹ ([#12749](https://github.com/leanprover-community/mathlib/pull/12749))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* is_of_fin_order_one
- \+ *lemma* is_of_fin_order_inv
- \+ *lemma* is_of_fin_order_inv_iff



## [2022-03-17 11:06:29](https://github.com/leanprover-community/mathlib/commit/c9c4f40)
chore(topology/compact_open): remove `continuous_map.ev`, and rename related lemmas to `eval'` ([#12738](https://github.com/leanprover-community/mathlib/pull/12738))
This:
* Eliminates `continuous_map.ev α β` in favor of `(λ p : C(α, β) × α, p.1 p.2)`, as this unifies better and does not require lean to unfold `ev` at the right time.
* Renames `continuous_map.continuous_evalx` to `continuous_map.continuous_eval_const` to match the `smul_const`-style names.
* Renames `continuous_map.continuous_ev` to `continuous_map.continuous_eval'` to match `continuous_map.continuous_eval`.
* Renames `continuous_map.continuous_ev₁` to `continuous_map.continuous_eval_const'`.
* Adds `continuous_map.continuous_coe'` to match `continuous_map.continuous_coe`.
* Golfs some nearby lemmas.
The unprimed lemma names have the same statement but different typeclasses, so the `ev` lemmas have taken the primed name. See [this zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Evaluation.20of.20continuous.20functions.20is.20continuous/near/275502201) for discussion about whether one set of lemmas can be removed.
#### Estimated changes
modified src/analysis/ODE/picard_lindelof.lean

modified src/topology/compact_open.lean
- \+ *lemma* continuous_eval'
- \+ *lemma* continuous_eval_const'
- \+ *lemma* continuous_coe'
- \- *lemma* continuous_ev
- \- *lemma* continuous_ev₁
- \+/\- *def* coev
- \- *def* ev
- \+/\- *def* coev

modified src/topology/continuous_function/bounded.lean
- \+ *theorem* continuous_eval_const
- \- *theorem* continuous_evalx

modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_eval_const
- \- *lemma* continuous_evalx

modified src/topology/metric_space/gromov_hausdorff_realized.lean



## [2022-03-17 11:06:28](https://github.com/leanprover-community/mathlib/commit/a6158f1)
feat(group_theory/subgroup/basic): One-sided closure induction lemmas ([#12725](https://github.com/leanprover-community/mathlib/pull/12725))
This PR adds one-sided closure induction lemmas, which I will need for Schreier's lemma.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* closure_induction_left
- \+ *lemma* closure_induction_right

modified src/group_theory/submonoid/membership.lean
- \+ *lemma* closure_induction_left
- \+ *lemma* closure_induction_right



## [2022-03-17 11:06:27](https://github.com/leanprover-community/mathlib/commit/b1bf390)
feat(number_theory/function_field): the ring of integers of a function field is not a field ([#12705](https://github.com/leanprover-community/mathlib/pull/12705))
#### Estimated changes
modified src/data/polynomial/div.lean
- \+ *lemma* not_is_field

modified src/number_theory/function_field.lean
- \+ *lemma* algebra_map_injective
- \+ *lemma* algebra_map_injective
- \+ *lemma* not_is_field



## [2022-03-17 10:35:37](https://github.com/leanprover-community/mathlib/commit/c3ecf00)
feat(group_theory/sylow): direct product of sylow groups if all normal ([#11778](https://github.com/leanprover-community/mathlib/pull/11778))
#### Estimated changes
modified src/group_theory/noncomm_pi_coprod.lean

modified src/group_theory/sylow.lean
- \+ *def* direct_product_of_normal



## [2022-03-17 09:56:23](https://github.com/leanprover-community/mathlib/commit/31391dc)
feat(model_theory/basic, elementary_maps): Uses `fun_like` approach for first-order maps ([#12755](https://github.com/leanprover-community/mathlib/pull/12755))
Introduces classes `hom_class`, `strong_hom_class` to describe classes of first-order maps.
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* hom_class.map_constants
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* coe_injective
- \+ *lemma* bijective
- \+/\- *lemma* injective
- \+ *lemma* surjective
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* coe_injective
- \+/\- *lemma* coe_injective
- \+/\- *lemma* injective
- \+ *def* hom_class.strong_hom_class_of_is_algebraic

modified src/model_theory/elementary_maps.lean
- \+/\- *lemma* injective
- \+/\- *lemma* map_constants
- \+/\- *lemma* coe_injective
- \+/\- *lemma* map_constants
- \+/\- *lemma* injective
- \+/\- *lemma* coe_injective



## [2022-03-17 08:18:32](https://github.com/leanprover-community/mathlib/commit/9d7a664)
feat(algebra/parity + *): generalize lemmas about parity ([#12761](https://github.com/leanprover-community/mathlib/pull/12761))
I moved more even/odd lemmas from nat/int to general semirings/rings.
Some files that explicitly used the nat/int namespace were changed along the way.
#### Estimated changes
modified src/algebra/geom_sum.lean

modified src/algebra/parity.lean
- \+ *lemma* even.add_even
- \+ *lemma* even.add_odd
- \+ *lemma* odd.add_even
- \+ *lemma* odd.add_odd
- \+ *lemma* even_zero
- \+ *lemma* odd_one
- \+ *lemma* even_two
- \+ *lemma* even_two_mul
- \+ *lemma* odd_two_mul_add_one
- \+ *lemma* add_monoid_hom.even
- \+ *lemma* ring_hom.odd
- \+ *lemma* even.mul_right
- \+ *lemma* even.mul_left
- \+ *lemma* odd.mul_odd
- \+ *lemma* even.pow_of_ne_zero
- \+ *lemma* odd.pow
- \+ *lemma* odd_neg_one
- \+ *lemma* even_neg_two
- \+ *lemma* even.sub_even
- \+ *lemma* odd.sub_odd
- \+ *theorem* odd.sub_even
- \+ *theorem* even.sub_odd
- \- *theorem* even.add_even
- \- *theorem* even.add_odd
- \- *theorem* odd.add_even
- \- *theorem* odd.add_odd

modified src/analysis/convex/specific_functions.lean

modified src/data/int/parity.lean
- \- *theorem* even_zero
- \- *theorem* even_bit0
- \- *theorem* even.sub_even
- \- *theorem* odd.sub_odd
- \- *theorem* even.mul_left
- \- *theorem* even.mul_right
- \- *theorem* odd.mul
- \- *theorem* odd.sub_even
- \- *theorem* even.sub_odd

modified src/data/nat/parity.lean
- \- *theorem* even_zero
- \- *theorem* even_bit0
- \- *theorem* even.mul_left
- \- *theorem* even.mul_right
- \- *theorem* odd.mul

modified src/number_theory/cyclotomic/discriminant.lean



## [2022-03-17 07:17:48](https://github.com/leanprover-community/mathlib/commit/3ba25ea)
feat(topology/algebra/const_mul_action): add is_closed smul lemmas ([#12747](https://github.com/leanprover-community/mathlib/pull/12747))
#### Estimated changes
modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* is_closed.smul_of_ne_zero
- \+ *lemma* is_closed.smul₀



## [2022-03-17 07:17:46](https://github.com/leanprover-community/mathlib/commit/87ab09c)
feat(category_theory/abelian/injective_resolution): homotopy between descents of morphism and two injective resolutions ([#12743](https://github.com/leanprover-community/mathlib/pull/12743))
This pr contains the following
* `category_theory.InjectiveResolution.desc_homotopy`: Any two descents of the same morphism are homotopic.
* `category_theory.InjectiveResolution.homotopy_equiv`: Any two injective resolutions of the same
  object are homotopically equivalent.
#### Estimated changes
modified src/category_theory/abelian/injective_resolution.lean
- \+ *lemma* homotopy_equiv_hom_ι
- \+ *lemma* homotopy_equiv_inv_ι
- \+ *def* desc_homotopy_zero_zero
- \+ *def* desc_homotopy_zero_one
- \+ *def* desc_homotopy_zero_succ
- \+ *def* desc_homotopy_zero
- \+ *def* desc_homotopy
- \+ *def* desc_id_homotopy
- \+ *def* desc_comp_homotopy
- \+ *def* homotopy_equiv



## [2022-03-17 06:22:26](https://github.com/leanprover-community/mathlib/commit/7000efb)
refactor(analysis/specific_limits): split into two files ([#12759](https://github.com/leanprover-community/mathlib/pull/12759))
Split the 1200-line file `analysis.specific_limits` into two:
- `analysis.specific_limits.normed` imports `normed_space` and covers limits in normed rings/fields
- `analysis.specific_limits.basic` imports only topology, and is still a bit of a grab-bag, covering limits in metric spaces, ordered rings, `ennreal`, etc.
#### Estimated changes
modified src/analysis/analytic/basic.lean

modified src/analysis/box_integral/box/subbox_induction.lean

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/hofer.lean

modified src/analysis/normed/group/hom.lean

modified src/analysis/normed_space/exponential.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/units.lean

created src/analysis/specific_limits/basic.lean
- \+ *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \+ *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \+ *lemma* tendsto_pow_at_top_at_top_of_one_lt
- \+ *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* tendsto_pow_at_top_nhds_within_0_of_lt_1
- \+ *lemma* uniformity_basis_dist_pow_of_lt_1
- \+ *lemma* geom_lt
- \+ *lemma* geom_le
- \+ *lemma* lt_geom
- \+ *lemma* le_geom
- \+ *lemma* tendsto_at_top_of_geom_le
- \+ *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* has_sum_geometric_of_lt_1
- \+ *lemma* summable_geometric_of_lt_1
- \+ *lemma* tsum_geometric_of_lt_1
- \+ *lemma* has_sum_geometric_two
- \+ *lemma* summable_geometric_two
- \+ *lemma* summable_geometric_two_encode
- \+ *lemma* tsum_geometric_two
- \+ *lemma* sum_geometric_two_le
- \+ *lemma* tsum_geometric_inv_two
- \+ *lemma* tsum_geometric_inv_two_ge
- \+ *lemma* has_sum_geometric_two'
- \+ *lemma* summable_geometric_two'
- \+ *lemma* tsum_geometric_two'
- \+ *lemma* nnreal.has_sum_geometric
- \+ *lemma* nnreal.summable_geometric
- \+ *lemma* tsum_geometric_nnreal
- \+ *lemma* ennreal.tsum_geometric
- \+ *lemma* cauchy_seq_of_edist_le_geometric
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto₀
- \+ *lemma* cauchy_seq_of_edist_le_geometric_two
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \+ *lemma* aux_has_sum_of_le_geometric
- \+ *lemma* cauchy_seq_of_le_geometric
- \+ *lemma* dist_le_of_le_geometric_of_tendsto₀
- \+ *lemma* dist_le_of_le_geometric_of_tendsto
- \+ *lemma* cauchy_seq_of_le_geometric_two
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto₀
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto
- \+ *lemma* summable_one_div_pow_of_le
- \+ *lemma* set.countable.exists_pos_has_sum_le
- \+ *lemma* set.countable.exists_pos_forall_sum_le
- \+ *lemma* factorial_tendsto_at_top
- \+ *lemma* tendsto_factorial_div_pow_self_at_top
- \+ *lemma* tendsto_nat_floor_mul_div_at_top
- \+ *lemma* tendsto_nat_ceil_mul_div_at_top
- \+ *theorem* exists_pos_sum_of_encodable
- \+ *theorem* exists_pos_sum_of_encodable
- \+ *theorem* exists_pos_sum_of_encodable'
- \+ *theorem* exists_pos_tsum_mul_lt_of_encodable
- \+ *def* pos_sum_of_encodable

renamed src/analysis/specific_limits.lean to src/analysis/specific_limits/normed.lean
- \- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \- *lemma* tendsto_const_div_at_top_nhds_0_nat
- \- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \- *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \- *lemma* tendsto_pow_at_top_at_top_of_one_lt
- \- *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* tendsto_pow_at_top_nhds_within_0_of_lt_1
- \- *lemma* uniformity_basis_dist_pow_of_lt_1
- \- *lemma* geom_lt
- \- *lemma* geom_le
- \- *lemma* lt_geom
- \- *lemma* le_geom
- \- *lemma* tendsto_at_top_of_geom_le
- \- *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* has_sum_geometric_of_lt_1
- \- *lemma* summable_geometric_of_lt_1
- \- *lemma* tsum_geometric_of_lt_1
- \- *lemma* has_sum_geometric_two
- \- *lemma* summable_geometric_two
- \- *lemma* summable_geometric_two_encode
- \- *lemma* tsum_geometric_two
- \- *lemma* sum_geometric_two_le
- \- *lemma* tsum_geometric_inv_two
- \- *lemma* tsum_geometric_inv_two_ge
- \- *lemma* has_sum_geometric_two'
- \- *lemma* summable_geometric_two'
- \- *lemma* tsum_geometric_two'
- \- *lemma* nnreal.has_sum_geometric
- \- *lemma* nnreal.summable_geometric
- \- *lemma* tsum_geometric_nnreal
- \- *lemma* ennreal.tsum_geometric
- \- *lemma* cauchy_seq_of_edist_le_geometric
- \- *lemma* edist_le_of_edist_le_geometric_of_tendsto
- \- *lemma* edist_le_of_edist_le_geometric_of_tendsto₀
- \- *lemma* cauchy_seq_of_edist_le_geometric_two
- \- *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \- *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \- *lemma* aux_has_sum_of_le_geometric
- \- *lemma* cauchy_seq_of_le_geometric
- \- *lemma* dist_le_of_le_geometric_of_tendsto₀
- \- *lemma* dist_le_of_le_geometric_of_tendsto
- \- *lemma* cauchy_seq_of_le_geometric_two
- \- *lemma* dist_le_of_le_geometric_two_of_tendsto₀
- \- *lemma* dist_le_of_le_geometric_two_of_tendsto
- \- *lemma* summable_one_div_pow_of_le
- \- *lemma* set.countable.exists_pos_has_sum_le
- \- *lemma* set.countable.exists_pos_forall_sum_le
- \- *lemma* factorial_tendsto_at_top
- \- *lemma* tendsto_factorial_div_pow_self_at_top
- \- *lemma* tendsto_nat_floor_mul_div_at_top
- \- *lemma* tendsto_nat_ceil_mul_div_at_top
- \- *theorem* exists_pos_sum_of_encodable
- \- *theorem* exists_pos_sum_of_encodable
- \- *theorem* exists_pos_sum_of_encodable'
- \- *theorem* exists_pos_tsum_mul_lt_of_encodable
- \- *def* pos_sum_of_encodable

modified src/data/real/cardinality.lean

modified src/data/real/hyperreal.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/number_theory/padics/hensel.lean

modified src/topology/instances/rat_lemmas.lean

modified src/topology/metric_space/baire.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/contracting.lean

modified src/topology/metric_space/hausdorff_distance.lean



## [2022-03-17 05:18:53](https://github.com/leanprover-community/mathlib/commit/877f2e7)
refactor(linear_algebra/ray): redefine `same_ray` to allow zero vectors ([#12618](https://github.com/leanprover-community/mathlib/pull/12618))
In a strictly convex space, the new definition is equivalent to the fact that the triangle inequality becomes an equality. The old definition was only used for nonzero vectors in `mathlib`. Also make the definition of `ray_vector` semireducible so that `ray_vector.setoid` can be an instance.
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+/\- *lemma* segment_eq_image₂
- \+/\- *lemma* open_segment_eq_image₂
- \+/\- *lemma* segment_same
- \+ *lemma* same_ray_of_mem_segment
- \+ *lemma* mem_segment_iff_same_ray
- \+/\- *lemma* segment_same
- \+/\- *lemma* segment_eq_image₂
- \+/\- *lemma* open_segment_eq_image₂

created src/analysis/normed_space/ray.lean
- \+ *lemma* norm_add
- \+ *lemma* norm_sub
- \+ *lemma* norm_smul_eq
- \+ *lemma* same_ray_iff_norm_smul_eq
- \+ *lemma* same_ray_iff_inv_norm_smul_eq_of_ne
- \+ *lemma* same_ray_iff_inv_norm_smul_eq

modified src/linear_algebra/orientation.lean
- \+/\- *lemma* orientation.map_apply
- \+/\- *lemma* orientation.map_refl
- \+/\- *lemma* orientation.map_symm
- \+/\- *lemma* map_orientation_eq_det_inv_smul
- \+/\- *lemma* orientation.map_apply
- \+/\- *lemma* orientation.map_refl
- \+/\- *lemma* orientation.map_symm
- \+/\- *lemma* map_orientation_eq_det_inv_smul
- \+/\- *def* orientation.map
- \+/\- *def* orientation.map

modified src/linear_algebra/ray.lean
- \+ *lemma* zero_left
- \+ *lemma* zero_right
- \+ *lemma* of_subsingleton
- \+ *lemma* of_subsingleton'
- \+ *lemma* refl
- \+ *lemma* symm
- \+ *lemma* exists_pos
- \+ *lemma* _root_.same_ray_comm
- \+ *lemma* trans
- \+ *lemma* _root_.same_ray_nonneg_smul_right
- \+ *lemma* _root_.same_ray_pos_smul_right
- \+ *lemma* nonneg_smul_right
- \+ *lemma* pos_smul_right
- \+ *lemma* _root_.same_ray_nonneg_smul_left
- \+ *lemma* _root_.same_ray_pos_smul_left
- \+ *lemma* nonneg_smul_left
- \+ *lemma* pos_smul_left
- \+ *lemma* map
- \+ *lemma* _root_.same_ray_map_iff
- \+ *lemma* smul
- \+ *lemma* add_left
- \+ *lemma* add_right
- \+/\- *lemma* equiv_iff_same_ray
- \+/\- *lemma* module.ray.ind
- \+/\- *lemma* ray_eq_iff
- \+/\- *lemma* ray_pos_smul
- \+/\- *lemma* module.ray.map_apply
- \+/\- *lemma* module.ray.map_refl
- \+/\- *lemma* module.ray.map_symm
- \+/\- *lemma* units_smul_of_pos
- \+/\- *lemma* some_ray_vector_ray
- \+/\- *lemma* some_vector_ne_zero
- \+/\- *lemma* some_vector_ray
- \+/\- *lemma* same_ray_neg_iff
- \+/\- *lemma* same_ray_neg_swap
- \+ *lemma* eq_zero_of_same_ray_neg_smul_right
- \+/\- *lemma* eq_zero_of_same_ray_self_neg
- \+/\- *lemma* coe_neg
- \+/\- *lemma* equiv_neg_iff
- \+ *lemma* neg_ray_of_ne_zero
- \+/\- *lemma* ne_neg_self
- \+ *lemma* neg_units_smul
- \+/\- *lemma* units_smul_of_neg
- \+/\- *lemma* same_ray_smul_right_iff
- \+ *lemma* same_ray_smul_right_iff_of_ne
- \+/\- *lemma* same_ray_smul_left_iff
- \+ *lemma* same_ray_smul_left_iff_of_ne
- \+/\- *lemma* same_ray_neg_smul_right_iff
- \+ *lemma* same_ray_neg_smul_right_iff_of_ne
- \+/\- *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* same_ray_neg_smul_left_iff_of_ne
- \+ *lemma* exists_right_eq_smul
- \+ *lemma* exists_left_eq_smul
- \+ *lemma* exists_eq_smul_add
- \+ *lemma* exists_eq_smul
- \- *lemma* same_ray.refl
- \- *lemma* same_ray.symm
- \- *lemma* same_ray.trans
- \- *lemma* same_ray_comm
- \- *lemma* equivalence_same_ray
- \- *lemma* same_ray_pos_smul_right
- \- *lemma* same_ray.pos_smul_right
- \- *lemma* same_ray_pos_smul_left
- \- *lemma* same_ray.pos_smul_left
- \- *lemma* same_ray.map
- \- *lemma* same_ray_map_iff
- \- *lemma* same_ray.smul
- \+/\- *lemma* equiv_iff_same_ray
- \+/\- *lemma* module.ray.ind
- \+/\- *lemma* ray_eq_iff
- \+/\- *lemma* ray_pos_smul
- \+/\- *lemma* module.ray.map_apply
- \+/\- *lemma* module.ray.map_refl
- \+/\- *lemma* module.ray.map_symm
- \+/\- *lemma* units_smul_of_pos
- \+/\- *lemma* some_ray_vector_ray
- \+/\- *lemma* some_vector_ne_zero
- \+/\- *lemma* some_vector_ray
- \- *lemma* same_ray.neg
- \+/\- *lemma* same_ray_neg_iff
- \+/\- *lemma* same_ray_neg_swap
- \+/\- *lemma* eq_zero_of_same_ray_self_neg
- \+/\- *lemma* coe_neg
- \+/\- *lemma* equiv_neg_iff
- \- *lemma* ray_neg
- \+/\- *lemma* ne_neg_self
- \+/\- *lemma* units_smul_of_neg
- \+/\- *lemma* same_ray_smul_right_iff
- \+/\- *lemma* same_ray_smul_left_iff
- \+/\- *lemma* same_ray_neg_smul_right_iff
- \+/\- *lemma* same_ray_neg_smul_left_iff
- \- *lemma* same_ray_iff_mem_orbit
- \- *lemma* same_ray_setoid_eq_orbit_rel
- \+/\- *def* ray_vector
- \+/\- *def* module.ray
- \+/\- *def* ray_vector.map_linear_equiv
- \+/\- *def* module.ray.map
- \+/\- *def* some_ray_vector
- \+/\- *def* some_vector
- \- *def* same_ray_setoid
- \+/\- *def* ray_vector
- \- *def* ray_vector.same_ray_setoid
- \+/\- *def* module.ray
- \+/\- *def* ray_vector.map_linear_equiv
- \+/\- *def* module.ray.map
- \+/\- *def* some_ray_vector
- \+/\- *def* some_vector



## [2022-03-17 04:20:16](https://github.com/leanprover-community/mathlib/commit/e547058)
docs(algebraic_topology/fundamental_groupoid/induced_maps): fix diagram rendering ([#12745](https://github.com/leanprover-community/mathlib/pull/12745))
#### Estimated changes
modified src/algebraic_topology/fundamental_groupoid/induced_maps.lean



## [2022-03-17 03:03:56](https://github.com/leanprover-community/mathlib/commit/d1e1304)
feat(combinatorics/simple_graph/connectivity): API for get_vert ([#12604](https://github.com/leanprover-community/mathlib/pull/12604))
From my Formalising Mathematics 2022 course.
#### Estimated changes
modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* get_vert_zero
- \+ *lemma* get_vert_of_length_le
- \+ *lemma* get_vert_length
- \+ *lemma* adj_get_vert_succ



## [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/192819b)
feat(category_theory/punit): A groupoid is equivalent to punit iff it has a unique arrow between any two objects ([#12726](https://github.com/leanprover-community/mathlib/pull/12726))
In terms of topology, when this is used with the fundamental groupoid, it means that a space is simply connected (we still need to define this) if and only if any two paths between the same points are homotopic, and contractible spaces are simply connected.
#### Estimated changes
modified src/category_theory/groupoid.lean
- \+ *def* groupoid.of_hom_unique

modified src/category_theory/punit.lean
- \+ *theorem* equiv_punit_iff_unique



## [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/3a0532a)
feat(topology/homotopy/fundamental_group): prove fundamental group is independent of basepoint in path-connected spaces ([#12234](https://github.com/leanprover-community/mathlib/pull/12234))
Adds definition of fundamental group and proves fundamental group independent of basepoint choice in path-connected spaces.
#### Estimated changes
created src/algebraic_topology/fundamental_groupoid/fundamental_group.lean
- \+ *def* fundamental_group
- \+ *def* fundamental_group_mul_equiv_of_path
- \+ *def* fundamental_group_mul_equiv_of_path_connected

modified src/category_theory/endomorphism.lean
- \+ *lemma* Aut_mul_def
- \+ *def* Aut_mul_equiv_of_iso



## [2022-03-16 23:51:43](https://github.com/leanprover-community/mathlib/commit/4d350b9)
chore(*): move code, golf ([#12753](https://github.com/leanprover-community/mathlib/pull/12753))
* move `pow_pos` and `pow_nonneg` to `algebra.order.ring`;
* use the former to golf `has_pos pnat nat`;
* fix formatting.
#### Estimated changes
modified src/algebra/group_power/order.lean
- \- *theorem* pow_pos
- \- *theorem* pow_nonneg

modified src/algebra/group_with_zero/basic.lean

modified src/algebra/order/group.lean

modified src/algebra/order/ring.lean
- \+ *theorem* pow_nonneg
- \+ *theorem* pow_pos

modified src/data/pnat/basic.lean



## [2022-03-16 21:17:30](https://github.com/leanprover-community/mathlib/commit/b3abae5)
chore(category_theory/preadditive/projective_resolution): some minor golf ([#12739](https://github.com/leanprover-community/mathlib/pull/12739))
#### Estimated changes
modified src/category_theory/preadditive/projective_resolution.lean



## [2022-03-16 21:17:29](https://github.com/leanprover-community/mathlib/commit/b24372f)
feat(model_theory/basic, terms_and_formulas): Helper functions for constant symbols ([#12722](https://github.com/leanprover-community/mathlib/pull/12722))
Defines a function `language.con` from `A` to constants of the language `L[[A]]`.
Changes the coercion of a constant to a term to a function `language.constants.term`.
Proves `simp` lemmas for interpretation of constant symbols and realization of constant terms.
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* coe_con

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_constants
- \+ *lemma* realize_con
- \+ *def* constants.term



## [2022-03-16 21:17:26](https://github.com/leanprover-community/mathlib/commit/3b91c32)
feat(group_theory/subgroup/basic): `map_le_map_iff_of_injective` for `subtype` ([#12713](https://github.com/leanprover-community/mathlib/pull/12713))
This PR adds the special case of `map_le_map_iff_of_injective` when the group homomorphism is `subtype`. This is useful when working with nested subgroups.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* map_subtype_le_map_subtype



## [2022-03-16 19:40:36](https://github.com/leanprover-community/mathlib/commit/c459d2b)
feat(algebra/algebra/basic,data/matrix/basic): resolve a TODO about `alg_hom.map_smul_of_tower` ([#12684](https://github.com/leanprover-community/mathlib/pull/12684))
It turns out that this lemma doesn't actually help in the place I claimed it would, so I added the lemma that does help too.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* map_smul_of_tower

modified src/data/matrix/basic.lean
- \+ *lemma* map_smul'
- \+ *lemma* map_op_smul'

modified src/linear_algebra/matrix/adjugate.lean



## [2022-03-16 19:40:35](https://github.com/leanprover-community/mathlib/commit/6a71007)
feat(group_theory/quotient_group) finiteness of groups for sequences of homomorphisms ([#12660](https://github.com/leanprover-community/mathlib/pull/12660))
#### Estimated changes
modified src/group_theory/quotient_group.lean

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* inclusion_injective



## [2022-03-16 18:34:52](https://github.com/leanprover-community/mathlib/commit/2e9985e)
feat(topology/algebra/order/basic): f ≤ᶠ[l] g implies limit of f ≤ limit of g ([#12727](https://github.com/leanprover-community/mathlib/pull/12727))
There are several implications of the form `eventually_*_of_tendsto_*`,
which involve the order relationships between the limit of a function
and other constants. What appears to be missing are reverse
implications: If two functions are eventually ordered, then their limits
respect the order.
This is lemma will be used in further work on the asymptotics of
squarefree numbers
#### Estimated changes
modified src/topology/algebra/order/basic.lean



## [2022-03-16 15:39:29](https://github.com/leanprover-community/mathlib/commit/693a3ac)
feat(number_theory/cyclotomic/basic): add is_primitive_root.adjoin ([#12716](https://github.com/leanprover-community/mathlib/pull/12716))
We add `is_cyclotomic_extension.is_primitive_root.adjoin`.
From flt-regular
#### Estimated changes
modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* _root_.is_primitive_root.adjoin_is_cyclotomic_extension

modified src/number_theory/cyclotomic/primitive_roots.lean



## [2022-03-16 13:40:39](https://github.com/leanprover-community/mathlib/commit/b8faf13)
feat(data/finset/basic): add finset.filter_eq_self ([#12717](https://github.com/leanprover-community/mathlib/pull/12717))
and an epsilon of cleanup
from flt-regular
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* filter_eq_self
- \+/\- *lemma* filter_eq_empty_iff
- \+/\- *lemma* monotone_filter_left
- \+/\- *lemma* filter_eq_empty_iff
- \+/\- *lemma* monotone_filter_left



## [2022-03-16 13:40:38](https://github.com/leanprover-community/mathlib/commit/d495afd)
feat(category_theory/abelian/injective_resolution): descents of a morphism ([#12703](https://github.com/leanprover-community/mathlib/pull/12703))
This pr dualise `src/category_theory/preadditive/projective_resolution.lean`. The reason that it is moved to `abelian` folder is because we want `exact f g` from `exact g.op f.op` instance.
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the following:
Given `I : InjectiveResolution X` and  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a chain map `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwine the descent and the original morphism, see `category_theory.InjectiveResolution.desc_commutes`.
(Docstring contains more than what is currently in the file, but everything else will come soon)
#### Estimated changes
created src/category_theory/abelian/injective_resolution.lean
- \+ *lemma* desc_f_one_zero_comm
- \+ *lemma* desc_commutes
- \+ *def* desc_f_zero
- \+ *def* desc_f_one
- \+ *def* desc_f_succ
- \+ *def* desc



## [2022-03-16 13:40:36](https://github.com/leanprover-community/mathlib/commit/f21a760)
feat(measure_theory/function/jacobian): change of variable formula in integrals in higher dimension ([#12492](https://github.com/leanprover-community/mathlib/pull/12492))
Let `μ` be a Lebesgue measure on a finite-dimensional real vector space, `s` a measurable set, and `f` a function which is differentiable and injective on `s`. Then `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`. (There is also a version for the Lebesgue integral, i.e., for `ennreal`-valued functions).
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* coe_to_continuous_linear_equiv_of_det_ne_zero
- \+ *lemma* to_continuous_linear_equiv_of_det_ne_zero_apply
- \+ *def* to_continuous_linear_equiv_of_det_ne_zero

created src/measure_theory/function/jacobian.lean
- \+ *lemma* exists_closed_cover_approximates_linear_on_of_has_fderiv_within_at
- \+ *lemma* exists_partition_approximates_linear_on_of_has_fderiv_within_at
- \+ *lemma* add_haar_image_le_mul_of_det_lt
- \+ *lemma* mul_le_add_haar_image_of_lt_det
- \+ *lemma* _root_.approximates_linear_on.norm_fderiv_sub_le
- \+ *lemma* add_haar_image_eq_zero_of_differentiable_on_of_add_haar_eq_zero
- \+ *lemma* add_haar_image_eq_zero_of_det_fderiv_within_eq_zero_aux
- \+ *lemma* add_haar_image_eq_zero_of_det_fderiv_within_eq_zero
- \+ *lemma* ae_measurable_fderiv_within
- \+ *lemma* ae_measurable_of_real_abs_det_fderiv_within
- \+ *lemma* ae_measurable_to_nnreal_abs_det_fderiv_within
- \+ *lemma* measurable_image_of_fderiv_within
- \+ *lemma* measurable_embedding_of_fderiv_within
- \+ *lemma* add_haar_image_le_lintegral_abs_det_fderiv_aux1
- \+ *lemma* add_haar_image_le_lintegral_abs_det_fderiv_aux2
- \+ *lemma* add_haar_image_le_lintegral_abs_det_fderiv
- \+ *lemma* lintegral_abs_det_fderiv_le_add_haar_image_aux1
- \+ *lemma* lintegral_abs_det_fderiv_le_add_haar_image_aux2
- \+ *lemma* lintegral_abs_det_fderiv_le_add_haar_image
- \+ *theorem* lintegral_abs_det_fderiv_eq_add_haar_image
- \+ *theorem* map_with_density_abs_det_fderiv_eq_add_haar
- \+ *theorem* restrict_map_with_density_abs_det_fderiv_eq_add_haar
- \+ *theorem* lintegral_image_eq_lintegral_abs_det_fderiv_mul
- \+ *theorem* integrable_on_image_iff_integrable_on_abs_det_fderiv_smul
- \+ *theorem* integral_image_eq_integral_abs_det_fderiv_smul

modified src/topology/algebra/module/basic.lean
- \+ *lemma* det_coe_symm



## [2022-03-16 11:53:36](https://github.com/leanprover-community/mathlib/commit/0964573)
feat(set_theory/cardinal): Lift `min` and `max` ([#12518](https://github.com/leanprover-community/mathlib/pull/12518))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *theorem* lift_min'
- \+ *theorem* lift_max'



## [2022-03-16 11:53:35](https://github.com/leanprover-community/mathlib/commit/717b11e)
feat(group_theory/noncomm_pi_coprod): homomorphism from pi monoids or groups ([#11744](https://github.com/leanprover-community/mathlib/pull/11744))
#### Estimated changes
created src/group_theory/noncomm_pi_coprod.lean
- \+ *lemma* noncomm_pi_coprod_mul_single
- \+ *lemma* noncomm_pi_coprod_mrange
- \+ *lemma* noncomm_pi_coprod_range
- \+ *lemma* injective_noncomm_pi_coprod_of_independent
- \+ *lemma* independent_range_of_coprime_order
- \+ *lemma* commute_subtype_of_commute
- \+ *lemma* noncomm_pi_coprod_mul_single
- \+ *lemma* noncomm_pi_coprod_range
- \+ *lemma* injective_noncomm_pi_coprod_of_independent
- \+ *lemma* independent_of_coprime_order
- \+ *def* noncomm_pi_coprod
- \+ *def* noncomm_pi_coprod_equiv
- \+ *def* noncomm_pi_coprod

modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_map_dvd
- \+ *lemma* order_of_inv

modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* eq_one_of_noncomm_prod_eq_one_of_independent
- \+/\- *lemma* eq_one_of_noncomm_prod_eq_one_of_independent



## [2022-03-16 10:05:27](https://github.com/leanprover-community/mathlib/commit/a50de33)
docs(algebra/group/hom): fix typo ([#12723](https://github.com/leanprover-community/mathlib/pull/12723))
#### Estimated changes
modified src/algebra/group/hom.lean



## [2022-03-16 10:05:26](https://github.com/leanprover-community/mathlib/commit/35bb571)
chore(number_theory/primorial): speed up some proofs ([#12714](https://github.com/leanprover-community/mathlib/pull/12714))
#### Estimated changes
modified src/number_theory/primorial.lean



## [2022-03-16 10:05:25](https://github.com/leanprover-community/mathlib/commit/a8bfcfe)
feat(algebraic_geometry/projective_spectrum): basic definitions of projective spectrum ([#12635](https://github.com/leanprover-community/mathlib/pull/12635))
This pr contains the basic definitions of projective spectrum of a graded ring:
- projective spectrum
- zero locus
- vanishing ideal
#### Estimated changes
created src/algebraic_geometry/projective_spectrum/topology.lean
- \+ *lemma* as_homogeneous_ideal_def
- \+ *lemma* ext
- \+ *lemma* mem_zero_locus
- \+ *lemma* zero_locus_span
- \+ *lemma* coe_vanishing_ideal
- \+ *lemma* mem_vanishing_ideal
- \+ *lemma* vanishing_ideal_singleton
- \+ *lemma* subset_zero_locus_iff_le_vanishing_ideal
- \+ *def* projective_spectrum
- \+ *def* zero_locus
- \+ *def* vanishing_ideal



## [2022-03-16 10:05:24](https://github.com/leanprover-community/mathlib/commit/a7a2f9d)
feat(data/nat/fib): norm_num plugin for fib ([#12463](https://github.com/leanprover-community/mathlib/pull/12463))
#### Estimated changes
modified src/data/nat/fib.lean
- \+ *lemma* is_fib_aux_one
- \+ *lemma* is_fib_aux_bit0
- \+ *lemma* is_fib_aux_bit1
- \+ *lemma* is_fib_aux_bit0_done
- \+ *lemma* is_fib_aux_bit1_done
- \+ *def* is_fib_aux

modified test/norm_num_ext.lean



## [2022-03-16 10:05:23](https://github.com/leanprover-community/mathlib/commit/500a1d3)
feat(data/pnat/find): port over `nat.find` API ([#12413](https://github.com/leanprover-community/mathlib/pull/12413))
Didn't port `pnat.find_add` because I got lost in the proof.
#### Estimated changes
modified src/data/pnat/basic.lean
- \+ *lemma* not_lt_one
- \+ *lemma* le_one_iff
- \+ *lemma* lt_add_left
- \+ *lemma* lt_add_right

created src/data/pnat/find.lean
- \+ *lemma* find_eq_iff
- \+ *lemma* find_lt_iff
- \+ *lemma* find_le_iff
- \+ *lemma* le_find_iff
- \+ *lemma* lt_find_iff
- \+ *lemma* find_eq_one
- \+ *lemma* one_le_find
- \+ *lemma* find_le
- \+ *lemma* find_comp_succ
- \+ *theorem* find_mono



## [2022-03-16 10:05:22](https://github.com/leanprover-community/mathlib/commit/bbc66b5)
feat(group_theory/subsemigroup/basic): subsemigroups ([#12111](https://github.com/leanprover-community/mathlib/pull/12111))
Port over submonoid implementation to a generalization: subsemigroups.
Implement submonoids via extends using old_structure_cmd, since that is
what subsemirings do.
Copy over the attribution from submonoids because the content is almost
unchanged.
The submonoid file hasn't been changed, so no proofs rely on the
subsemigroups proofs.
#### Estimated changes
modified src/algebra/algebra/subalgebra/basic.lean

modified src/deprecated/submonoid.lean
- \+/\- *lemma* submonoid.is_submonoid
- \+/\- *lemma* submonoid.is_submonoid
- \+/\- *def* submonoid.of
- \+/\- *def* submonoid.of

modified src/field_theory/subfield.lean

modified src/group_theory/free_product.lean

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/basic.lean

modified src/group_theory/submonoid/pointwise.lean

created src/group_theory/subsemigroup/basic.lean
- \+ *lemma* mem_carrier
- \+ *lemma* mem_mk
- \+ *lemma* coe_set_mk
- \+ *lemma* mk_le_mk
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+ *lemma* not_mem_bot
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi
- \+ *lemma* subsingleton_of_subsingleton
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* not_mem_of_not_mem_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_induction'
- \+ *lemma* dense_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* closure_singleton_le_iff_mem
- \+ *lemma* mem_supr
- \+ *lemma* supr_eq_closure
- \+ *lemma* eq_on_mclosure
- \+ *lemma* eq_of_eq_on_mtop
- \+ *lemma* eq_of_eq_on_mdense
- \+ *lemma* coe_of_mdense
- \+ *theorem* ext
- \+ *theorem* mul_mem
- \+ *def* simps.coe
- \+ *def* closure
- \+ *def* eq_mlocus
- \+ *def* of_mdense

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/span.lean

modified src/ring_theory/class_group.lean

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/subring/basic.lean

modified src/ring_theory/subsemiring/basic.lean



## [2022-03-16 08:21:55](https://github.com/leanprover-community/mathlib/commit/50691e5)
chore(measure_theory/function): split files strongly_measurable and simple_func_dense ([#12711](https://github.com/leanprover-community/mathlib/pull/12711))
The files `strongly_measurable` and `simple_func_dense` contain general results, and results pertaining to the `L^p` space. We move the results regarding `L^p` to new files, to make sure that the main parts of the files can be imported earlier in the hierarchy. This is needed for a forthcoming integral refactor.
#### Estimated changes
modified src/measure_theory/function/ae_eq_of_integral.lean

modified src/measure_theory/function/continuous_map_dense.lean

modified src/measure_theory/function/simple_func_dense.lean
- \- *lemma* nnnorm_approx_on_le
- \- *lemma* norm_approx_on_y₀_le
- \- *lemma* norm_approx_on_zero_le
- \- *lemma* tendsto_approx_on_Lp_snorm
- \- *lemma* mem_ℒp_approx_on
- \- *lemma* tendsto_approx_on_univ_Lp_snorm
- \- *lemma* mem_ℒp_approx_on_univ
- \- *lemma* tendsto_approx_on_univ_Lp
- \- *lemma* tendsto_approx_on_L1_nnnorm
- \- *lemma* integrable_approx_on
- \- *lemma* tendsto_approx_on_univ_L1_nnnorm
- \- *lemma* integrable_approx_on_univ
- \- *lemma* exists_forall_norm_le
- \- *lemma* mem_ℒp_zero
- \- *lemma* mem_ℒp_top
- \- *lemma* measure_preimage_lt_top_of_mem_ℒp
- \- *lemma* mem_ℒp_of_finite_measure_preimage
- \- *lemma* mem_ℒp_iff
- \- *lemma* integrable_iff
- \- *lemma* mem_ℒp_iff_integrable
- \- *lemma* mem_ℒp_iff_fin_meas_supp
- \- *lemma* integrable_iff_fin_meas_supp
- \- *lemma* fin_meas_supp.integrable
- \- *lemma* integrable_pair
- \- *lemma* mem_ℒp_of_is_finite_measure
- \- *lemma* integrable_of_is_finite_measure
- \- *lemma* measure_preimage_lt_top_of_integrable
- \- *lemma* measure_support_lt_top
- \- *lemma* measure_support_lt_top_of_mem_ℒp
- \- *lemma* measure_support_lt_top_of_integrable
- \- *lemma* measure_lt_top_of_mem_ℒp_indicator
- \- *lemma* coe_coe
- \- *lemma* coe_smul
- \- *lemma* to_Lp_eq_to_Lp
- \- *lemma* to_Lp_eq_mk
- \- *lemma* to_Lp_zero
- \- *lemma* to_Lp_add
- \- *lemma* to_Lp_neg
- \- *lemma* to_Lp_sub
- \- *lemma* to_Lp_smul
- \- *lemma* norm_to_Lp
- \- *lemma* to_simple_func_eq_to_fun
- \- *lemma* to_Lp_to_simple_func
- \- *lemma* to_simple_func_to_Lp
- \- *lemma* zero_to_simple_func
- \- *lemma* add_to_simple_func
- \- *lemma* neg_to_simple_func
- \- *lemma* sub_to_simple_func
- \- *lemma* smul_to_simple_func
- \- *lemma* norm_to_simple_func
- \- *lemma* coe_indicator_const
- \- *lemma* to_simple_func_indicator_const
- \- *lemma* coe_fn_le
- \- *lemma* coe_fn_zero
- \- *lemma* coe_fn_nonneg
- \- *lemma* exists_simple_func_nonneg_ae_eq
- \- *lemma* dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \- *lemma* Lp.induction
- \- *lemma* mem_ℒp.induction
- \- *lemma* L1.simple_func.to_Lp_one_eq_to_L1
- \- *lemma* integrable.induction
- \- *def* simple_func
- \- *def* to_Lp
- \- *def* to_simple_func
- \- *def* indicator_const
- \- *def* coe_to_Lp
- \- *def* coe_simple_func_nonneg_to_Lp_nonneg

created src/measure_theory/function/simple_func_dense_lp.lean
- \+ *lemma* nnnorm_approx_on_le
- \+ *lemma* norm_approx_on_y₀_le
- \+ *lemma* norm_approx_on_zero_le
- \+ *lemma* tendsto_approx_on_Lp_snorm
- \+ *lemma* mem_ℒp_approx_on
- \+ *lemma* tendsto_approx_on_univ_Lp_snorm
- \+ *lemma* mem_ℒp_approx_on_univ
- \+ *lemma* tendsto_approx_on_univ_Lp
- \+ *lemma* tendsto_approx_on_L1_nnnorm
- \+ *lemma* integrable_approx_on
- \+ *lemma* tendsto_approx_on_univ_L1_nnnorm
- \+ *lemma* integrable_approx_on_univ
- \+ *lemma* exists_forall_norm_le
- \+ *lemma* mem_ℒp_zero
- \+ *lemma* mem_ℒp_top
- \+ *lemma* measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* mem_ℒp_of_finite_measure_preimage
- \+ *lemma* mem_ℒp_iff
- \+ *lemma* integrable_iff
- \+ *lemma* mem_ℒp_iff_integrable
- \+ *lemma* mem_ℒp_iff_fin_meas_supp
- \+ *lemma* integrable_iff_fin_meas_supp
- \+ *lemma* fin_meas_supp.integrable
- \+ *lemma* integrable_pair
- \+ *lemma* mem_ℒp_of_is_finite_measure
- \+ *lemma* integrable_of_is_finite_measure
- \+ *lemma* measure_preimage_lt_top_of_integrable
- \+ *lemma* measure_support_lt_top
- \+ *lemma* measure_support_lt_top_of_mem_ℒp
- \+ *lemma* measure_support_lt_top_of_integrable
- \+ *lemma* measure_lt_top_of_mem_ℒp_indicator
- \+ *lemma* coe_coe
- \+ *lemma* coe_smul
- \+ *lemma* to_Lp_eq_to_Lp
- \+ *lemma* to_Lp_eq_mk
- \+ *lemma* to_Lp_zero
- \+ *lemma* to_Lp_add
- \+ *lemma* to_Lp_neg
- \+ *lemma* to_Lp_sub
- \+ *lemma* to_Lp_smul
- \+ *lemma* norm_to_Lp
- \+ *lemma* to_simple_func_eq_to_fun
- \+ *lemma* to_Lp_to_simple_func
- \+ *lemma* to_simple_func_to_Lp
- \+ *lemma* zero_to_simple_func
- \+ *lemma* add_to_simple_func
- \+ *lemma* neg_to_simple_func
- \+ *lemma* sub_to_simple_func
- \+ *lemma* smul_to_simple_func
- \+ *lemma* norm_to_simple_func
- \+ *lemma* coe_indicator_const
- \+ *lemma* to_simple_func_indicator_const
- \+ *lemma* coe_fn_le
- \+ *lemma* coe_fn_zero
- \+ *lemma* coe_fn_nonneg
- \+ *lemma* exists_simple_func_nonneg_ae_eq
- \+ *lemma* dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \+ *lemma* Lp.induction
- \+ *lemma* mem_ℒp.induction
- \+ *lemma* L1.simple_func.to_Lp_one_eq_to_L1
- \+ *lemma* integrable.induction
- \+ *def* simple_func
- \+ *def* to_Lp
- \+ *def* to_simple_func
- \+ *def* indicator_const
- \+ *def* coe_to_Lp
- \+ *def* coe_simple_func_nonneg_to_Lp_nonneg

modified src/measure_theory/function/strongly_measurable.lean
- \- *lemma* mem_ℒp.fin_strongly_measurable_of_measurable
- \- *lemma* mem_ℒp.ae_fin_strongly_measurable
- \- *lemma* integrable.ae_fin_strongly_measurable
- \- *lemma* Lp.fin_strongly_measurable

created src/measure_theory/function/strongly_measurable_lp.lean
- \+ *lemma* mem_ℒp.fin_strongly_measurable_of_measurable
- \+ *lemma* mem_ℒp.ae_fin_strongly_measurable
- \+ *lemma* integrable.ae_fin_strongly_measurable
- \+ *lemma* Lp.fin_strongly_measurable

modified src/measure_theory/integral/set_to_l1.lean



## [2022-03-16 08:21:54](https://github.com/leanprover-community/mathlib/commit/ba6c84d)
feat(ring_theory/fractional_ideal): two span_singleton lemmas ([#12656](https://github.com/leanprover-community/mathlib/pull/12656))
#### Estimated changes
modified src/linear_algebra/span.lean
- \+ *lemma* span_singleton_eq_span_singleton

modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* span_singleton_eq_span_singleton
- \+ *lemma* span_singleton_pow



## [2022-03-16 08:21:53](https://github.com/leanprover-community/mathlib/commit/17c74f1)
feat(algebra/group_power/order): add le_pow ([#12436](https://github.com/leanprover-community/mathlib/pull/12436))
Added a new theorem so that library search will find it.
#### Estimated changes
modified src/algebra/group_power/order.lean
- \+ *theorem* le_self_pow



## [2022-03-16 08:21:52](https://github.com/leanprover-community/mathlib/commit/91f98e8)
feat(topology/bornology/hom): Locally bounded maps ([#12046](https://github.com/leanprover-community/mathlib/pull/12046))
Define `locally_bounded_map`, the type of locally bounded maps between two bornologies.
#### Estimated changes
modified src/topology/bornology/basic.lean
- \+/\- *lemma* is_bounded_compl_iff
- \+ *lemma* is_cobounded_compl_iff
- \+/\- *lemma* is_bounded_empty
- \+ *lemma* comap_cobounded_le_iff
- \+/\- *lemma* is_bounded_compl_iff
- \+/\- *lemma* is_bounded_empty

created src/topology/bornology/hom.lean
- \+ *lemma* is_bounded.image
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_of_map_bounded
- \+ *lemma* of_map_bounded_apply
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* of_map_bounded
- \+ *def* comp



## [2022-03-16 08:21:51](https://github.com/leanprover-community/mathlib/commit/68033a2)
feat(set_theory/ordinal_arithmetic): A set of ordinals is bounded above iff it's small ([#11870](https://github.com/leanprover-community/mathlib/pull/11870))
#### Estimated changes
modified src/logic/small.lean
- \+ *theorem* small_subset

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* le_sup_shrink_equiv
- \+ *theorem* small_Iio
- \+ *theorem* bdd_above_iff_small
- \+ *theorem* sup_eq_Sup



## [2022-03-16 07:51:24](https://github.com/leanprover-community/mathlib/commit/a452bfa)
feat(analysis/seminorm): three simple lemmas about balls ([#12720](https://github.com/leanprover-community/mathlib/pull/12720))
The lemmas are in preparation to characterize the natural bornology in terms of seminorms in LCTVSs.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* ball_eq_emptyset
- \+ *lemma* smul_ball_zero
- \+ *lemma* ball_zero_absorbs_ball_zero



## [2022-03-16 05:24:58](https://github.com/leanprover-community/mathlib/commit/1f1289f)
feat(algebra/parity + data/{int, nat}/parity): parity lemmas for general semirings ([#12718](https://github.com/leanprover-community/mathlib/pull/12718))
This PR proves some general facts about adding even/odd elements in a semiring, thus removing the need to proving the same results for `nat` and `int`.
#### Estimated changes
created src/algebra/parity.lean
- \+ *theorem* even.add_even
- \+ *theorem* even.add_odd
- \+ *theorem* odd.add_even
- \+ *theorem* odd.add_odd

modified src/data/int/parity.lean
- \- *theorem* even.add_even
- \- *theorem* odd.add_odd
- \- *theorem* odd.add_even
- \- *theorem* even.add_odd

modified src/data/nat/parity.lean
- \- *theorem* even.add_even
- \- *theorem* odd.add_odd
- \- *theorem* odd.add_even
- \- *theorem* even.add_odd



## [2022-03-16 03:13:34](https://github.com/leanprover-community/mathlib/commit/cbd6173)
chore(scripts): update nolints.txt ([#12728](https://github.com/leanprover-community/mathlib/pull/12728))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-16 00:32:33](https://github.com/leanprover-community/mathlib/commit/45061f3)
chore(data/equiv/basic): use `option.elim` and `sum.elim` ([#12724](https://github.com/leanprover-community/mathlib/pull/12724))
We have these functions, why not use them?
#### Estimated changes
modified src/data/equiv/basic.lean



## [2022-03-15 18:38:06](https://github.com/leanprover-community/mathlib/commit/b622d4d)
chore(algebra/associated): move prime_dvd_prime_iff_eq ([#12706](https://github.com/leanprover-community/mathlib/pull/12706))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* prime_dvd_prime_iff_eq

modified src/data/list/prime.lean
- \- *lemma* prime_dvd_prime_iff_eq



## [2022-03-15 16:38:31](https://github.com/leanprover-community/mathlib/commit/7ed4f2c)
feat(group_theory/submonoid/operations): monoids are isomorphic to themselves as submonoids ([#12658](https://github.com/leanprover-community/mathlib/pull/12658))
#### Estimated changes
modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *def* top_equiv
- \+/\- *def* top_equiv

modified src/algebra/lie/nilpotent.lean

modified src/algebra/lie/semisimple.lean

modified src/algebra/lie/solvable.lean

modified src/algebra/lie/submodule.lean
- \+ *lemma* lie_subalgebra.top_equiv_apply
- \+ *lemma* lie_ideal.top_equiv_apply
- \- *lemma* lie_subalgebra.top_equiv_self_apply
- \- *lemma* lie_ideal.top_equiv_self_apply
- \+ *def* lie_subalgebra.top_equiv
- \+ *def* lie_ideal.top_equiv
- \- *def* lie_subalgebra.top_equiv_self
- \- *def* lie_ideal.top_equiv_self

modified src/algebra/module/submodule_lattice.lean
- \+ *def* top_equiv
- \- *def* top_equiv_self

modified src/field_theory/adjoin.lean

modified src/group_theory/subgroup/basic.lean
- \+ *def* top_equiv

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* top_equiv_to_monoid_hom
- \+ *def* top_equiv

modified src/number_theory/cyclotomic/primitive_roots.lean

modified src/ring_theory/adjoin/power_basis.lean



## [2022-03-15 15:20:21](https://github.com/leanprover-community/mathlib/commit/375419f)
feat(algebra/algebra/subalgebra/pointwise): lemmas about `*` and `to_submodule` ([#12695](https://github.com/leanprover-community/mathlib/pull/12695))
#### Estimated changes
modified src/algebra/algebra/subalgebra/pointwise.lean
- \+ *theorem* mul_to_submodule_le
- \+/\- *theorem* mul_self
- \+ *theorem* mul_to_submodule
- \+/\- *theorem* mul_self



## [2022-03-15 14:10:30](https://github.com/leanprover-community/mathlib/commit/7582e14)
feat(linear_algebra/matrix/determinant): special case of the matrix determinant lemma ([#12682](https://github.com/leanprover-community/mathlib/pull/12682))
#### Estimated changes
modified src/linear_algebra/matrix/determinant.lean
- \+/\- *lemma* upper_two_block_triangular_det
- \+ *lemma* lower_two_block_triangular_det
- \+ *lemma* det_one_add_col_mul_row
- \+/\- *lemma* upper_two_block_triangular_det



## [2022-03-15 14:10:28](https://github.com/leanprover-community/mathlib/commit/9c09965)
feat(algebra/big_operators/finprod): finite product of power is power of finite product ([#12655](https://github.com/leanprover-community/mathlib/pull/12655))
#### Estimated changes
modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_pow



## [2022-03-15 13:39:45](https://github.com/leanprover-community/mathlib/commit/88a5978)
doc(algebra/hierarchy_design): fix my name ([#12674](https://github.com/leanprover-community/mathlib/pull/12674))
#### Estimated changes
modified src/algebra/hierarchy_design.lean



## [2022-03-15 11:51:47](https://github.com/leanprover-community/mathlib/commit/530f008)
feat(linear_algebra/matrix/nonsingular_inverse): Add `matrix.list_prod_inv_reverse` ([#12691](https://github.com/leanprover-community/mathlib/pull/12691))
#### Estimated changes
modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* list_prod_inv_reverse



## [2022-03-15 11:51:46](https://github.com/leanprover-community/mathlib/commit/7a02c9e)
fix(set_theory/ordinal_arithmetic): remove redundant hypothesis from `CNF_rec` ([#12680](https://github.com/leanprover-community/mathlib/pull/12680))
The hypothesis in question was a theorem that could be deduced.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* mod_opow_log_lt_self
- \+/\- *theorem* one_CNF
- \+/\- *theorem* CNF_pairwise
- \+/\- *theorem* CNF_fst_le_log
- \+/\- *theorem* CNF_snd_lt
- \+/\- *theorem* CNF_sorted
- \- *theorem* CNF_aux
- \+/\- *theorem* one_CNF
- \+/\- *theorem* CNF_pairwise
- \+/\- *theorem* CNF_fst_le_log
- \+/\- *theorem* CNF_snd_lt
- \+/\- *theorem* CNF_sorted



## [2022-03-15 11:51:45](https://github.com/leanprover-community/mathlib/commit/a3b39c6)
feat(linear_algebra/clifford_algebra/conjugation): add lemmas showing interaction between `involute` and `even_odd` ([#12672](https://github.com/leanprover-community/mathlib/pull/12672))
Often the even and odd submodules are defined in terms of involution, but this strategy doesn't actually work in characteristic two.
#### Estimated changes
modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.has_graded_one.algebra_map_mem

modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *lemma* involute_eq_of_mem_even
- \+ *lemma* involute_eq_of_mem_odd

modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* ι_mul_ι_mem_even_odd_zero
- \+ *lemma* even_odd_induction
- \+ *lemma* even_induction
- \+ *lemma* odd_induction



## [2022-03-15 11:51:44](https://github.com/leanprover-community/mathlib/commit/48ffeb7)
feat(group_theory/finiteness): quotient of fg is fg ([#12652](https://github.com/leanprover-community/mathlib/pull/12652))
#### Estimated changes
modified src/group_theory/coset.lean
- \+ *lemma* mk_surjective

modified src/group_theory/finiteness.lean
- \+ *lemma* group.fg_of_surjective

modified src/group_theory/quotient_group.lean
- \+ *lemma* mk'_surjective
- \+/\- *lemma* subgroup_eq_top_of_subsingleton
- \+/\- *lemma* subgroup_eq_top_of_subsingleton

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* mrange_restrict_surjective
- \+/\- *lemma* bot_or_nontrivial
- \+/\- *lemma* bot_or_exists_ne_one
- \+/\- *lemma* bot_or_nontrivial
- \+/\- *lemma* bot_or_exists_ne_one



## [2022-03-15 11:10:28](https://github.com/leanprover-community/mathlib/commit/a98202b)
chore(category_theory/preadditive/projective_resolution): typo ([#12702](https://github.com/leanprover-community/mathlib/pull/12702))
#### Estimated changes
modified src/category_theory/preadditive/projective_resolution.lean



## [2022-03-15 11:10:27](https://github.com/leanprover-community/mathlib/commit/eefa425)
perf(analysis/convec/topology): remove topological_add_group.path_connected instance ([#12675](https://github.com/leanprover-community/mathlib/pull/12675))
The linter was right in [#10011](https://github.com/leanprover-community/mathlib/pull/10011) and `topological_add_group.path_connected` should not be an instance, because it creates enormous TC subproblems (turn on `pp.all` to get an idea of what's going on).
Apparently the instance isn't even used in mathlib.
#### Estimated changes
modified src/analysis/convex/topology.lean
- \+ *lemma* topological_add_group.path_connected



## [2022-03-15 11:10:26](https://github.com/leanprover-community/mathlib/commit/5b90340)
feat(model_theory/terms_and_formulas): Notation for terms and formulas from Flypitch ([#12630](https://github.com/leanprover-community/mathlib/pull/12630))
Introduces some notation, localized to `first_order`, to make typing explicit terms and formulas easier.
#### Estimated changes
modified src/model_theory/terms_and_formulas.lean



## [2022-03-15 10:32:43](https://github.com/leanprover-community/mathlib/commit/d199eb9)
feat(ring_theory/graded_algebra/homogeneous_ideal): refactor `homogeneous_ideal` as a structure extending ideals ([#12673](https://github.com/leanprover-community/mathlib/pull/12673))
We refactored `homogeneous_ideal` as a structure extending ideals so that we can define a `set_like (homogeneous_ideal \McA) A` instance.
#### Estimated changes
modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* homogeneous_ideal.is_homogeneous
- \+ *lemma* homogeneous_ideal.to_ideal_injective
- \+ *lemma* homogeneous_ideal.ext
- \+ *lemma* homogeneous_ideal.mem_iff
- \+ *lemma* ideal.to_ideal_homogeneous_core_le
- \+ *lemma* ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self
- \+ *lemma* homogeneous_ideal.to_ideal_homogeneous_core_eq_self
- \+/\- *lemma* ideal.is_homogeneous.iff_eq
- \+ *lemma* to_ideal_bot
- \+/\- *lemma* eq_bot_iff
- \+ *lemma* to_ideal_top
- \+/\- *lemma* eq_top_iff
- \+ *lemma* to_ideal_inf
- \+ *lemma* to_ideal_Inf
- \+ *lemma* to_ideal_infi
- \+ *lemma* to_ideal_sup
- \+ *lemma* to_ideal_Sup
- \+ *lemma* to_ideal_add
- \+ *lemma* homogeneous_ideal.to_ideal_mul
- \+/\- *lemma* ideal.homogeneous_core.gc
- \+ *lemma* ideal.le_to_ideal_homogeneous_hull
- \+ *lemma* ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self
- \+ *lemma* homogeneous_ideal.homogeneous_hull_to_ideal_eq_self
- \+ *lemma* ideal.to_ideal_homogeneous_hull_eq_supr
- \+/\- *lemma* ideal.homogeneous_hull.gc
- \+ *lemma* homogeneous_ideal.to_ideal_irrelevant
- \- *lemma* ideal.coe_homogeneous_core_le
- \- *lemma* ideal.is_homogeneous.coe_homogeneous_core_eq_self
- \- *lemma* homogeneous_ideal.homogeneous_core_coe_eq_self
- \+/\- *lemma* ideal.is_homogeneous.iff_eq
- \- *lemma* coe_bot
- \+/\- *lemma* eq_bot_iff
- \- *lemma* coe_top
- \+/\- *lemma* eq_top_iff
- \- *lemma* coe_inf
- \- *lemma* coe_Inf
- \- *lemma* coe_infi
- \- *lemma* coe_sup
- \- *lemma* coe_Sup
- \- *lemma* coe_add
- \- *lemma* homogeneous_ideal.coe_mul
- \+/\- *lemma* ideal.homogeneous_core.gc
- \- *lemma* ideal.le_coe_homogeneous_hull
- \- *lemma* ideal.is_homogeneous.homogeneous_hull_eq_self
- \- *lemma* homogeneous_ideal.homogeneous_hull_coe_eq_self
- \- *lemma* ideal.coe_homogeneous_hull_eq_supr
- \+/\- *lemma* ideal.homogeneous_hull.gc
- \- *lemma* homogeneous_ideal.coe_irrelevant
- \+ *def* homogeneous_ideal.to_ideal
- \+/\- *def* ideal.homogeneous_core.gi
- \+/\- *def* ideal.homogeneous_hull.gi
- \+/\- *def* ideal.homogeneous_core.gi
- \+/\- *def* ideal.homogeneous_hull.gi

modified src/ring_theory/graded_algebra/radical.lean



## [2022-03-15 10:32:41](https://github.com/leanprover-community/mathlib/commit/061d04b)
feat(category_theory/monoidal): distribute tensor over direct sum ([#12626](https://github.com/leanprover-community/mathlib/pull/12626))
This is preliminary to the monoidal structure on chain complexes.
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* is_bilimit.total
- \+ *lemma* is_bilimit.binary_total

modified src/category_theory/monoidal/category.lean
- \+ *lemma* tensor_dite
- \+ *lemma* dite_tensor

modified src/category_theory/monoidal/preadditive.lean
- \+ *lemma* tensor_sum
- \+ *lemma* sum_tensor
- \+ *lemma* left_distributor_hom
- \+ *lemma* left_distributor_inv
- \+ *lemma* left_distributor_assoc
- \+ *lemma* right_distributor_hom
- \+ *lemma* right_distributor_inv
- \+ *lemma* right_distributor_assoc
- \+ *lemma* left_distributor_right_distributor_assoc
- \+ *def* left_distributor
- \+ *def* right_distributor



## [2022-03-15 10:02:26](https://github.com/leanprover-community/mathlib/commit/078b213)
chore(category_theory/abelian/projective): fix typo ([#12701](https://github.com/leanprover-community/mathlib/pull/12701))
#### Estimated changes
modified src/category_theory/abelian/projective.lean



## [2022-03-15 08:11:54](https://github.com/leanprover-community/mathlib/commit/92e6759)
fix(category_theory/bicategory): remove spaces before closing parentheses ([#12700](https://github.com/leanprover-community/mathlib/pull/12700))
#### Estimated changes
modified src/category_theory/bicategory/basic.lean



## [2022-03-15 08:11:53](https://github.com/leanprover-community/mathlib/commit/0bd6dc2)
chore(measure_theory): move and rename some lemmas ([#12699](https://github.com/leanprover-community/mathlib/pull/12699))
* move `ae_interval_oc_iff`, `ae_measurable_interval_oc_iff`, and `ae_interval_oc_iff'` to `measure_theory.measure.measure_space`, rename `ae_interval_oc_iff'` to `ae_restrict_interval_oc_iff`;
* add lemmas about `ae` and union of sets.
#### Estimated changes
modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* interval_oc_eq_union

modified src/measure_theory/integral/interval_integral.lean
- \- *lemma* ae_interval_oc_iff
- \- *lemma* ae_measurable_interval_oc_iff
- \- *lemma* ae_interval_oc_iff'

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_interval_oc_iff
- \+ *lemma* ae_restrict_Union_eq
- \+ *lemma* ae_restrict_union_eq
- \+ *lemma* ae_restrict_interval_oc_eq
- \+ *lemma* ae_restrict_interval_oc_iff
- \+ *lemma* _root_.ae_measurable_union_iff
- \+ *lemma* ae_measurable_interval_oc_iff



## [2022-03-15 08:11:52](https://github.com/leanprover-community/mathlib/commit/4b562f8)
doc(data/equiv/encodable): +2 docstrings ([#12698](https://github.com/leanprover-community/mathlib/pull/12698))
#### Estimated changes
modified src/data/equiv/encodable/basic.lean



## [2022-03-15 08:11:51](https://github.com/leanprover-community/mathlib/commit/a3e0c85)
chore(cyclotomic/gal): update todo ([#12693](https://github.com/leanprover-community/mathlib/pull/12693))
this mentioned a non-existing old solution which got superseded by `is_primitive_root.power_basis`, but is still not the right solution in the long term
#### Estimated changes
modified src/number_theory/cyclotomic/gal.lean



## [2022-03-15 08:11:50](https://github.com/leanprover-community/mathlib/commit/77395f1)
chore(algebra/module/basic): Move the scalar action earlier ([#12690](https://github.com/leanprover-community/mathlib/pull/12690))
This is prep work for golfing some of the instances.
This also adjust the variables slightly to be in a more sensible order.
#### Estimated changes
modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'



## [2022-03-15 08:11:49](https://github.com/leanprover-community/mathlib/commit/025fe7c)
feat(group_theory/abelianization): An application of the three subgroups lemma ([#12677](https://github.com/leanprover-community/mathlib/pull/12677))
This PR uses the three subgroups lemma to prove that `⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G`.
#### Estimated changes
modified src/group_theory/abelianization.lean
- \+ *lemma* commutator_centralizer_commutator_le_center



## [2022-03-15 08:11:48](https://github.com/leanprover-community/mathlib/commit/b7978f3)
chore(analysis/seminorm): Weaken typeclasses on `convex` and `locally_convex` lemmas ([#12645](https://github.com/leanprover-community/mathlib/pull/12645))
Generalize type-classes `normed_linearly_ordered_field` to `normed_field` (otherwise it would not work over complex numbers).
#### Estimated changes
modified src/analysis/seminorm.lean



## [2022-03-15 08:11:47](https://github.com/leanprover-community/mathlib/commit/53f6d68)
feat(category_theory/preadditive) : definition of injective resolution ([#12641](https://github.com/leanprover-community/mathlib/pull/12641))
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the definition of:
- `InjectiveResolution`;
- `has_injective_resolution` and `has_injective_resolutions`;
- injective object has injective resolution.
#### Estimated changes
created src/category_theory/preadditive/injective_resolution.lean
- \+ *lemma* ι_f_succ
- \+ *def* self



## [2022-03-15 08:11:46](https://github.com/leanprover-community/mathlib/commit/585d641)
refactor(linear_algebra/basic): split file ([#12637](https://github.com/leanprover-community/mathlib/pull/12637))
`linear_algebra.basic` has become a 2800 line monster, with lots of imports.
This is some further work on splitting it into smaller pieces, by extracting everything about (or needing) `span` to `linear_algebra.span`.
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/module/submodule_pointwise.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/linear_algebra/basic.lean
- \- *lemma* mem_span
- \- *lemma* subset_span
- \- *lemma* span_le
- \- *lemma* span_mono
- \- *lemma* span_eq_of_le
- \- *lemma* span_eq
- \- *lemma* span_coe_eq_restrict_scalars
- \- *lemma* map_span
- \- *lemma* map_span_le
- \- *lemma* span_insert_zero
- \- *lemma* span_preimage_le
- \- *lemma* span_induction
- \- *lemma* span_induction'
- \- *lemma* span_span_coe_preimage
- \- *lemma* span_nat_eq_add_submonoid_closure
- \- *lemma* span_nat_eq
- \- *lemma* span_int_eq_add_subgroup_closure
- \- *lemma* span_int_eq
- \- *lemma* span_empty
- \- *lemma* span_univ
- \- *lemma* span_union
- \- *lemma* span_Union
- \- *lemma* span_attach_bUnion
- \- *lemma* sup_span
- \- *lemma* span_sup
- \- *lemma* span_eq_supr_of_singleton_spans
- \- *lemma* span_smul_le
- \- *lemma* subset_span_trans
- \- *lemma* span_smul_eq_of_is_unit
- \- *lemma* coe_supr_of_chain
- \- *lemma* coe_scott_continuous
- \- *lemma* mem_supr_of_chain
- \- *lemma* mem_sup
- \- *lemma* mem_sup'
- \- *lemma* coe_sup
- \- *lemma* sup_to_add_submonoid
- \- *lemma* sup_to_add_subgroup
- \- *lemma* mem_span_singleton_self
- \- *lemma* nontrivial_span_singleton
- \- *lemma* mem_span_singleton
- \- *lemma* le_span_singleton_iff
- \- *lemma* span_singleton_eq_top_iff
- \- *lemma* span_zero_singleton
- \- *lemma* span_singleton_eq_range
- \- *lemma* span_singleton_smul_le
- \- *lemma* span_singleton_smul_eq
- \- *lemma* disjoint_span_singleton
- \- *lemma* disjoint_span_singleton'
- \- *lemma* mem_span_singleton_trans
- \- *lemma* mem_span_insert
- \- *lemma* span_insert
- \- *lemma* span_insert_eq_span
- \- *lemma* span_span
- \- *lemma* span_le_restrict_scalars
- \- *lemma* span_subset_span
- \- *lemma* span_span_of_tower
- \- *lemma* span_eq_bot
- \- *lemma* span_singleton_eq_bot
- \- *lemma* span_zero
- \- *lemma* span_image
- \- *lemma* apply_mem_span_image_of_mem_span
- \- *lemma* map_subtype_span_singleton
- \- *lemma* not_mem_span_of_apply_not_mem_span_image
- \- *lemma* supr_eq_span
- \- *lemma* supr_to_add_submonoid
- \- *lemma* supr_induction
- \- *lemma* supr_induction'
- \- *lemma* span_singleton_le_iff_mem
- \- *lemma* singleton_span_is_compact_element
- \- *lemma* lt_sup_iff_not_mem
- \- *lemma* mem_supr
- \- *lemma* mem_span_finite_of_mem_span
- \- *lemma* prod_coe
- \- *lemma* mem_prod
- \- *lemma* span_prod_le
- \- *lemma* prod_top
- \- *lemma* prod_bot
- \- *lemma* prod_mono
- \- *lemma* prod_inf_prod
- \- *lemma* prod_sup_prod
- \- *lemma* span_neg
- \- *lemma* mem_span_insert'
- \- *lemma* eq_on_span
- \- *lemma* eq_on_span'
- \- *lemma* ext_on
- \- *lemma* ext_on_range
- \- *lemma* span_singleton_eq_range
- \- *lemma* to_span_singleton_one
- \- *lemma* _root_.submodule.comap_map_eq
- \- *lemma* _root_.submodule.comap_map_eq_self
- \- *lemma* span_singleton_sup_ker_eq_top
- \- *lemma* ker_to_span_singleton
- \- *lemma* to_span_nonzero_singleton_one
- \- *lemma* coord_self
- \- *theorem* coe_supr_of_directed
- \- *theorem* mem_supr_of_directed
- \- *theorem* mem_Sup_of_directed
- \- *theorem* map_le_map_iff'
- \- *theorem* map_injective
- \- *theorem* map_eq_top_iff
- \- *def* span
- \- *def* prod
- \- *def* to_span_singleton
- \- *def* to_span_nonzero_singleton

modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/prod.lean

modified src/linear_algebra/quotient.lean

created src/linear_algebra/span.lean
- \+ *lemma* mem_span
- \+ *lemma* subset_span
- \+ *lemma* span_le
- \+ *lemma* span_mono
- \+ *lemma* span_eq_of_le
- \+ *lemma* span_eq
- \+ *lemma* span_coe_eq_restrict_scalars
- \+ *lemma* map_span
- \+ *lemma* map_span_le
- \+ *lemma* span_insert_zero
- \+ *lemma* span_preimage_le
- \+ *lemma* span_induction
- \+ *lemma* span_induction'
- \+ *lemma* span_span_coe_preimage
- \+ *lemma* span_nat_eq_add_submonoid_closure
- \+ *lemma* span_nat_eq
- \+ *lemma* span_int_eq_add_subgroup_closure
- \+ *lemma* span_int_eq
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* span_union
- \+ *lemma* span_Union
- \+ *lemma* span_attach_bUnion
- \+ *lemma* sup_span
- \+ *lemma* span_sup
- \+ *lemma* span_eq_supr_of_singleton_spans
- \+ *lemma* span_smul_le
- \+ *lemma* subset_span_trans
- \+ *lemma* span_smul_eq_of_is_unit
- \+ *lemma* coe_supr_of_chain
- \+ *lemma* coe_scott_continuous
- \+ *lemma* mem_supr_of_chain
- \+ *lemma* mem_sup
- \+ *lemma* mem_sup'
- \+ *lemma* coe_sup
- \+ *lemma* sup_to_add_submonoid
- \+ *lemma* sup_to_add_subgroup
- \+ *lemma* mem_span_singleton_self
- \+ *lemma* nontrivial_span_singleton
- \+ *lemma* mem_span_singleton
- \+ *lemma* le_span_singleton_iff
- \+ *lemma* span_singleton_eq_top_iff
- \+ *lemma* span_zero_singleton
- \+ *lemma* span_singleton_eq_range
- \+ *lemma* span_singleton_smul_le
- \+ *lemma* span_singleton_smul_eq
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* disjoint_span_singleton'
- \+ *lemma* mem_span_singleton_trans
- \+ *lemma* mem_span_insert
- \+ *lemma* span_insert
- \+ *lemma* span_insert_eq_span
- \+ *lemma* span_span
- \+ *lemma* span_le_restrict_scalars
- \+ *lemma* span_subset_span
- \+ *lemma* span_span_of_tower
- \+ *lemma* span_eq_bot
- \+ *lemma* span_singleton_eq_bot
- \+ *lemma* span_zero
- \+ *lemma* span_image
- \+ *lemma* apply_mem_span_image_of_mem_span
- \+ *lemma* map_subtype_span_singleton
- \+ *lemma* not_mem_span_of_apply_not_mem_span_image
- \+ *lemma* supr_eq_span
- \+ *lemma* supr_to_add_submonoid
- \+ *lemma* supr_induction
- \+ *lemma* supr_induction'
- \+ *lemma* span_singleton_le_iff_mem
- \+ *lemma* singleton_span_is_compact_element
- \+ *lemma* lt_sup_iff_not_mem
- \+ *lemma* mem_supr
- \+ *lemma* mem_span_finite_of_mem_span
- \+ *lemma* prod_coe
- \+ *lemma* mem_prod
- \+ *lemma* span_prod_le
- \+ *lemma* prod_top
- \+ *lemma* prod_bot
- \+ *lemma* prod_mono
- \+ *lemma* prod_inf_prod
- \+ *lemma* prod_sup_prod
- \+ *lemma* span_neg
- \+ *lemma* mem_span_insert'
- \+ *lemma* comap_map_eq
- \+ *lemma* comap_map_eq_self
- \+ *lemma* span_singleton_eq_range
- \+ *lemma* to_span_singleton_one
- \+ *lemma* eq_on_span
- \+ *lemma* eq_on_span'
- \+ *lemma* ext_on
- \+ *lemma* ext_on_range
- \+ *lemma* span_singleton_sup_ker_eq_top
- \+ *lemma* ker_to_span_singleton
- \+ *lemma* to_span_nonzero_singleton_one
- \+ *lemma* coord_self
- \+ *theorem* coe_supr_of_directed
- \+ *theorem* mem_supr_of_directed
- \+ *theorem* mem_Sup_of_directed
- \+ *theorem* map_le_map_iff'
- \+ *theorem* map_injective
- \+ *theorem* map_eq_top_iff
- \+ *def* span
- \+ *def* prod
- \+ *def* to_span_singleton
- \+ *def* to_span_nonzero_singleton

modified src/linear_algebra/tensor_product.lean

modified src/ring_theory/simple_module.lean

modified src/ring_theory/witt_vector/isocrystal.lean



## [2022-03-15 06:38:19](https://github.com/leanprover-community/mathlib/commit/2ad9b39)
feat(algebra/associated): add irreducible.not_dvd_one ([#12686](https://github.com/leanprover-community/mathlib/pull/12686))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* not_dvd_one

modified src/data/nat/prime.lean
- \+/\- *theorem* prime.not_dvd_one
- \+/\- *theorem* prime.not_dvd_one



## [2022-03-15 03:40:54](https://github.com/leanprover-community/mathlib/commit/6d63c9b)
chore(scripts): update nolints.txt ([#12696](https://github.com/leanprover-community/mathlib/pull/12696))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-03-15 03:40:53](https://github.com/leanprover-community/mathlib/commit/0fd9e30)
feat(set_theory/ordinal_arithmetic): `smul` coincides with `mul` ([#12692](https://github.com/leanprover-community/mathlib/pull/12692))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* smul_eq_mul



## [2022-03-15 03:05:43](https://github.com/leanprover-community/mathlib/commit/f337856)
feat(algebra/category): show categorical image in Module agrees with range ([#12605](https://github.com/leanprover-community/mathlib/pull/12605))
This just follows the existing code for the same fact in `AddCommGroup`.
This PR is preparing for a better API for homological calculations in `Module R`.
#### Estimated changes
created src/algebra/category/Module/images.lean
- \+ *lemma* image.fac
- \+ *lemma* image.lift_fac
- \+ *lemma* image_iso_range_inv_image_ι
- \+ *lemma* image_iso_range_hom_subtype
- \+ *def* image
- \+ *def* image.ι
- \+ *def* factor_thru_image
- \+ *def* mono_factorisation



## [2022-03-15 00:51:24](https://github.com/leanprover-community/mathlib/commit/1148717)
chore(set_theory/ordinal_arithmetic): `well_founded` → `wf` ([#12615](https://github.com/leanprover-community/mathlib/pull/12615))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean



## [2022-03-14 20:38:51](https://github.com/leanprover-community/mathlib/commit/8d2e887)
feat(number_theory/function_field): add place at infinity  ([#12245](https://github.com/leanprover-community/mathlib/pull/12245))
#### Estimated changes
modified src/data/polynomial/ring_division.lean
- \+ *lemma* nat_degree_sub_eq_of_prod_eq

modified src/field_theory/ratfunc.lean
- \+ *lemma* num_denom_neg
- \+ *lemma* num_mul_denom_add_denom_mul_num_ne_zero
- \+ *lemma* X_ne_zero
- \+ *lemma* int_degree_zero
- \+ *lemma* int_degree_one
- \+ *lemma* int_degree_C
- \+ *lemma* int_degree_X
- \+ *lemma* int_degree_polynomial
- \+ *lemma* int_degree_mul
- \+ *lemma* int_degree_neg
- \+ *lemma* int_degree_add
- \+ *lemma* nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree
- \+ *lemma* int_degree_add_le
- \+ *def* int_degree

modified src/number_theory/function_field.lean
- \+ *lemma* infty_valuation.map_zero'
- \+ *lemma* infty_valuation.map_one'
- \+ *lemma* infty_valuation.map_mul'
- \+ *lemma* infty_valuation.map_add_le_max'
- \+ *lemma* infty_valuation_of_nonzero
- \+ *lemma* infty_valuation_apply
- \+ *lemma* infty_valuation.C
- \+ *lemma* infty_valuation.X
- \+ *lemma* infty_valuation.polynomial
- \+ *def* infty_valuation_def
- \+ *def* infty_valuation



## [2022-03-14 18:58:33](https://github.com/leanprover-community/mathlib/commit/c1c61d4)
feat(data/W/constructions): add constructions of W types ([#12292](https://github.com/leanprover-community/mathlib/pull/12292))
Here I write the naturals and lists as W-types and show that the definitions are equivalent. Any other interesting examples I should add?
#### Estimated changes
modified src/data/W/basic.lean

created src/data/W/constructions.lean
- \+ *lemma* left_inv_nat
- \+ *lemma* right_inv_nat
- \+ *lemma* left_inv_list
- \+ *lemma* right_inv_list
- \+ *def* nat_β
- \+ *def* of_nat
- \+ *def* to_nat
- \+ *def* equiv_nat
- \+ *def* nat_α_equiv_punit_sum_punit
- \+ *def* list_β
- \+ *def* of_list
- \+ *def* to_list
- \+ *def* equiv_list
- \+ *def* list_α_equiv_punit_sum



## [2022-03-14 17:36:38](https://github.com/leanprover-community/mathlib/commit/2e56210)
chore(analysis/complex/upper_half_plane): don't use `abbreviation` ([#12679](https://github.com/leanprover-community/mathlib/pull/12679))
Some day we should add Poincaré metric as a `metric_space` instance on `upper_half_plane`.
In the meantime, make sure that Lean doesn't use `subtype` instances for `uniform_space` and/or `metric_space`.
#### Estimated changes
modified src/analysis/complex/upper_half_plane.lean
- \+ *def* upper_half_plane



## [2022-03-14 15:48:03](https://github.com/leanprover-community/mathlib/commit/28775ce)
feat(tactic/interactive): guard_{hyp,target}_mod_implicit ([#12668](https://github.com/leanprover-community/mathlib/pull/12668))
This adds two new tactics `guard_hyp_mod_implicit` and `guard_target_mod_implicit`, with the same syntax as `guard_hyp` and `guard_target`.  While the `guard_*` tactics check for syntax equality, the `guard_*_mod_implicit` tactics check for definitional equality with the `none` transparency
#### Estimated changes
modified src/tactic/interactive.lean

created test/mod_implicit.lean



## [2022-03-14 13:59:47](https://github.com/leanprover-community/mathlib/commit/d8ef1de)
feat(topology/separation): add t2_space_iff ([#12628](https://github.com/leanprover-community/mathlib/pull/12628))
From my formalising mathematics 22 course
#### Estimated changes
modified src/topology/separation.lean



## [2022-03-14 13:59:46](https://github.com/leanprover-community/mathlib/commit/5242a7f)
feat(data/list/infix): add lemmas and instances ([#12511](https://github.com/leanprover-community/mathlib/pull/12511))
#### Estimated changes
modified src/data/list/infix.lean
- \+ *lemma* reverse_infix
- \+ *lemma* is_infix.length_le
- \+ *lemma* is_prefix.length_le
- \+ *lemma* is_suffix.length_le
- \+ *lemma* infix_cons_iff
- \- *lemma* infix.length_le



## [2022-03-14 13:59:45](https://github.com/leanprover-community/mathlib/commit/df3792f)
refactor(data/set): generalize `set.restrict` and take set argument first in both `set.restrict` and `subtype.restrict` ([#12510](https://github.com/leanprover-community/mathlib/pull/12510))
Generalizes `set.restrict` to Pi types and makes both this function and `subtype.restrict` take the restricting index set before the Pi type to restrict, which makes taking the image/preimage of a set of Pi types easier (`s.restrict '' pis` is shorter than `(λ p, set.restrict p s) '' pis` -- I'd argue that this is the more common case than taking the image of a set of restricting sets on a single Pi type). Changed uses of `set.restrict` to use dot notation where possible.
#### Estimated changes
modified archive/sensitivity.lean

modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* biproduct.from_subtype
- \+/\- *def* biproduct.to_subtype
- \+/\- *def* biproduct.from_subtype
- \+/\- *def* biproduct.to_subtype

modified src/data/set/function.lean
- \+/\- *lemma* restrict_apply
- \+/\- *lemma* range_restrict
- \+/\- *lemma* inj_on_iff_injective
- \+/\- *lemma* surj_on_iff_surjective
- \+/\- *lemma* restrict_apply
- \+/\- *lemma* range_restrict
- \+/\- *lemma* inj_on_iff_injective
- \+/\- *lemma* surj_on_iff_surjective
- \+/\- *def* restrict
- \+/\- *def* restrict

modified src/data/subtype.lean
- \+/\- *lemma* restrict_def
- \+/\- *lemma* restrict_def
- \+/\- *def* restrict
- \+/\- *def* restrict

modified src/group_theory/complement.lean

modified src/measure_theory/measurable_space.lean

modified src/topology/fiber_bundle.lean
- \+/\- *def* set_symm
- \+/\- *def* set_symm

modified src/topology/local_homeomorph.lean



## [2022-03-14 13:59:43](https://github.com/leanprover-community/mathlib/commit/c1edbec)
feat(set_theory/ordinal_topology): Basic results on the order topology of ordinals ([#11861](https://github.com/leanprover-community/mathlib/pull/11861))
We link together various notions about ordinals to their topological counterparts.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* is_normal.sup
- \+/\- *theorem* is_normal.sup

created src/set_theory/ordinal_topology.lean
- \+ *theorem* is_open_singleton_iff
- \+ *theorem* is_open_iff
- \+ *theorem* mem_closure_iff_sup
- \+ *theorem* mem_closed_iff_sup
- \+ *theorem* mem_closure_iff_bsup
- \+ *theorem* mem_closed_iff_bsup
- \+ *theorem* is_closed_iff_sup
- \+ *theorem* is_closed_iff_bsup
- \+ *theorem* is_limit_of_mem_frontier
- \+ *theorem* is_normal_iff_strict_mono_and_continuous
- \+ *theorem* enum_ord_is_normal_iff_is_closed



## [2022-03-14 12:19:21](https://github.com/leanprover-community/mathlib/commit/09ea7fb)
feat(data/finset/noncomm_prod): finite pi lemmas ([#12291](https://github.com/leanprover-community/mathlib/pull/12291))
including a few helpers
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* pi.mul_single_commute
- \+ *lemma* pi.mul_single_apply_commute

modified src/data/finset/noncomm_prod.lean
- \+ *lemma* nocomm_prod_map_aux
- \+ *lemma* noncomm_prod_map
- \+ *lemma* noncomm_prod_eq_pow_card
- \+ *lemma* noncomm_prod_map
- \+ *lemma* noncomm_prod_eq_pow_card
- \+ *lemma* noncomm_prod_mul_single
- \+ *lemma* _root_.monoid_hom.pi_ext



## [2022-03-14 11:12:21](https://github.com/leanprover-community/mathlib/commit/fc882ff)
chore(ci): update trepplein to version 1.1 ([#12669](https://github.com/leanprover-community/mathlib/pull/12669))
New upstream release, fixing some performance issues.
#### Estimated changes
modified .github/workflows/bors.yml

modified .github/workflows/build.yml

modified .github/workflows/build.yml.in

modified .github/workflows/build_fork.yml



## [2022-03-14 11:12:20](https://github.com/leanprover-community/mathlib/commit/abb8e5d)
feat(set_theory/principal): If `a` isn't additive principal, it's the sum of two smaller ordinals ([#12664](https://github.com/leanprover-community/mathlib/pull/12664))
#### Estimated changes
modified src/set_theory/principal.lean
- \+ *theorem* exists_lt_add_of_not_principal_add
- \+ *theorem* principal_add_iff_add_lt_ne_self



## [2022-03-14 11:12:19](https://github.com/leanprover-community/mathlib/commit/cc6e2eb)
feat(group_theory/commutator): The three subgroups lemma ([#12634](https://github.com/leanprover-community/mathlib/pull/12634))
This PR proves the three subgroups lemma: If `⁅⁅H₂, H₃⁆, H₁⁆ = ⊥` and `⁅⁅H₃, H₁⁆, H₂⁆ = ⊥`, then `⁅⁅H₁, H₂⁆, H₃⁆ = ⊥`.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+ *lemma* commutator_commutator_eq_bot_of_rotate



## [2022-03-14 11:12:18](https://github.com/leanprover-community/mathlib/commit/6a51706)
chore(topology/homotopy): Move more algebraic-flavored content about fundamental groupoid to algebraic_topology folder ([#12631](https://github.com/leanprover-community/mathlib/pull/12631))
Moved:
  - `topology/homotopy/fundamental_groupoid.lean` to `algebraic_topology/fundamental_groupoid/basic.lean`
  - the second half of `topology/homotopy/product.lean`, dealing with `fundamental_groupoid_functor` preserving products, to `algebraic_topology/fundamental_groupoid/product.lean`
  - `topology/homotopy/induced_maps.lean` to `algebraic_topology/fundamental_groupoid/induced_maps.lean`
#### Estimated changes
renamed src/topology/homotopy/fundamental_groupoid.lean to src/algebraic_topology/fundamental_groupoid/basic.lean

renamed src/topology/homotopy/induced_maps.lean to src/algebraic_topology/fundamental_groupoid/induced_maps.lean

created src/algebraic_topology/fundamental_groupoid/product.lean
- \+ *lemma* proj_map
- \+ *lemma* cone_discrete_comp_obj_map_cone
- \+ *lemma* proj_left_map
- \+ *lemma* proj_right_map
- \+ *lemma* prod_to_prod_Top_map
- \+ *def* proj
- \+ *def* pi_to_pi_Top
- \+ *def* pi_iso
- \+ *def* cone_discrete_comp
- \+ *def* pi_Top_to_pi_cone
- \+ *def* preserves_product
- \+ *def* proj_left
- \+ *def* proj_right
- \+ *def* prod_to_prod_Top
- \+ *def* prod_iso

modified src/topology/homotopy/product.lean
- \- *lemma* proj_map
- \- *lemma* cone_discrete_comp_obj_map_cone
- \- *lemma* proj_left_map
- \- *lemma* proj_right_map
- \- *lemma* prod_to_prod_Top_map
- \- *def* proj
- \- *def* pi_to_pi_Top
- \- *def* pi_iso
- \- *def* cone_discrete_comp
- \- *def* pi_Top_to_pi_cone
- \- *def* preserves_product
- \- *def* proj_left
- \- *def* proj_right
- \- *def* prod_to_prod_Top
- \- *def* prod_iso



## [2022-03-14 09:29:31](https://github.com/leanprover-community/mathlib/commit/a2544de)
chore(algebra/category/Module): simp lemmas for monoidal closed ([#12608](https://github.com/leanprover-community/mathlib/pull/12608))
I'm worried by the fact that I can't express the coercions here without using `@`. They do turn up in the wild, however!
#### Estimated changes
modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* monoidal_closed_curry
- \+ *lemma* monoidal_closed_uncurry



## [2022-03-14 09:29:29](https://github.com/leanprover-community/mathlib/commit/31e60c8)
feat(set_theory/{ordinal, ordinal_arithmetic}): Add various instances for `o.out.α` ([#12508](https://github.com/leanprover-community/mathlib/pull/12508))
#### Estimated changes
modified src/measure_theory/card_measurable_space.lean

modified src/set_theory/cardinal_ordinal.lean

modified src/set_theory/ordinal.lean
- \+ *lemma* typein_le_typein'
- \+ *lemma* enum_le_enum'
- \+ *theorem* lt_succ
- \+ *theorem* enum_zero_le
- \+ *theorem* enum_zero_le'
- \+ *theorem* le_enum_succ
- \+ *theorem* enum_zero_eq_bot
- \+ *def* out_order_bot_of_pos

modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* has_succ_of_type_succ_lt
- \- *lemma* has_succ_of_is_limit
- \+ *theorem* enum_succ_eq_top
- \+ *theorem* out_no_max_of_succ_lt
- \- *theorem* lt_succ



## [2022-03-14 09:29:27](https://github.com/leanprover-community/mathlib/commit/1f428f3)
feat(data/list/basic): Split and intercalate are inverses ([#12466](https://github.com/leanprover-community/mathlib/pull/12466))
Show that split and intercalate are inverses of each other (under suitable conditions)
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* modify_head_modify_head
- \+ *lemma* split_on_p_nil
- \+/\- *lemma* split_on_p_aux_eq
- \+/\- *lemma* split_on_p_aux_nil
- \+/\- *lemma* split_on_p_spec
- \+ *lemma* split_on_p_aux_ne_nil
- \+ *lemma* split_on_p_aux_spec
- \+ *lemma* split_on_p_ne_nil
- \+ *lemma* split_on_p_cons
- \+ *lemma* split_on_p_eq_single
- \+ *lemma* split_on_p_first
- \+ *lemma* intercalate_split_on
- \+ *lemma* split_on_intercalate
- \+/\- *lemma* split_on_p_aux_eq
- \+/\- *lemma* split_on_p_aux_nil
- \+/\- *lemma* split_on_p_spec



## [2022-03-14 09:29:26](https://github.com/leanprover-community/mathlib/commit/cd001b2)
feat(category_theory/bicategory/free): define free bicategories ([#11998](https://github.com/leanprover-community/mathlib/pull/11998))
#### Estimated changes
created src/category_theory/bicategory/free.lean
- \+ *lemma* mk_vcomp
- \+ *lemma* mk_whisker_left
- \+ *lemma* mk_whisker_right
- \+ *lemma* id_def
- \+ *lemma* comp_def
- \+ *lemma* mk_id
- \+ *lemma* mk_associator_hom
- \+ *lemma* mk_associator_inv
- \+ *lemma* mk_left_unitor_hom
- \+ *lemma* mk_left_unitor_inv
- \+ *lemma* mk_right_unitor_hom
- \+ *lemma* mk_right_unitor_inv
- \+ *lemma* lift_hom_id
- \+ *lemma* lift_hom_comp
- \+ *lemma* lift_hom₂_congr
- \+ *def* free_bicategory
- \+ *def* of
- \+ *def* lift_hom
- \+ *def* lift_hom₂
- \+ *def* lift



## [2022-03-14 08:31:44](https://github.com/leanprover-community/mathlib/commit/520f204)
feat(analysis/seminorm): add lemmas for inequalities and `finset.sup` ([#12650](https://github.com/leanprover-community/mathlib/pull/12650))
These lemmas are not lean-trivial since seminorms map to the `real` and not to `nnreal`.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* finset_sup_apply_le
- \+ *lemma* finset_sup_apply_lt



## [2022-03-14 08:31:43](https://github.com/leanprover-community/mathlib/commit/0f3bfda)
feat(analysis/complex/schwarz): some versions of the Schwarz lemma ([#12633](https://github.com/leanprover-community/mathlib/pull/12633))
#### Estimated changes
modified src/analysis/calculus/dslope.lean
- \+ *lemma* continuous_linear_map.dslope_comp

modified src/analysis/complex/removable_singularity.lean

created src/analysis/complex/schwarz.lean
- \+ *lemma* schwarz_aux
- \+ *lemma* norm_dslope_le_div_of_maps_to_ball
- \+ *lemma* norm_deriv_le_div_of_maps_to_ball
- \+ *lemma* dist_le_div_mul_dist_of_maps_to_ball
- \+ *lemma* abs_deriv_le_div_of_maps_to_ball
- \+ *lemma* abs_deriv_le_one_of_maps_to_ball
- \+ *lemma* dist_le_dist_of_maps_to_ball_self
- \+ *lemma* abs_le_abs_of_maps_to_ball_self

modified src/linear_algebra/affine_space/slope.lean
- \+ *lemma* affine_map.slope_comp
- \+ *lemma* linear_map.slope_comp



## [2022-03-14 08:31:42](https://github.com/leanprover-community/mathlib/commit/c2368be)
feat(topology/hom/open): Continuous open maps ([#12406](https://github.com/leanprover-community/mathlib/pull/12406))
Define `continuous_open_map`, the type of continuous opens maps between two topological spaces, and `continuous_open_map_class`, its companion hom class.
#### Estimated changes
created src/topology/hom/open.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* comp



## [2022-03-14 07:05:57](https://github.com/leanprover-community/mathlib/commit/7b7fea5)
refactor(set_theory/cardinal_ordinal): `aleph_is_principal_aleph` → `principal_add_aleph` ([#12663](https://github.com/leanprover-community/mathlib/pull/12663))
This matches the naming scheme used throughout `set_theory/principal.lean`.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* principal_add_ord
- \+ *theorem* principal_add_aleph
- \- *theorem* ord_is_principal_add
- \- *theorem* aleph_is_principal_add



## [2022-03-14 07:05:56](https://github.com/leanprover-community/mathlib/commit/6ebb378)
feat(set_theory/ordinal): `ord 1 = 1` ([#12662](https://github.com/leanprover-community/mathlib/pull/12662))
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* ord_one



## [2022-03-14 07:05:55](https://github.com/leanprover-community/mathlib/commit/18ba395)
feat(algebra/support) support of power is subset of support ([#12654](https://github.com/leanprover-community/mathlib/pull/12654))
#### Estimated changes
modified src/algebra/support.lean
- \+ *lemma* mul_support_pow



## [2022-03-14 07:05:54](https://github.com/leanprover-community/mathlib/commit/6b3b567)
chore(topology/algebra/group_with_zero): fix docstring for has_continuous_inv0 ([#12653](https://github.com/leanprover-community/mathlib/pull/12653))
#### Estimated changes
modified src/topology/algebra/group_with_zero.lean

modified src/topology/instances/nnreal.lean



## [2022-03-14 07:05:53](https://github.com/leanprover-community/mathlib/commit/1f5950a)
feat(analysis/seminorm): add lemmas for `with_seminorms` ([#12649](https://github.com/leanprover-community/mathlib/pull/12649))
Two helper lemmas that make it easier to generate an instance for `with_seminorms`.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* with_seminorms_of_nhds
- \+ *lemma* with_seminorms_of_has_basis



## [2022-03-14 07:05:51](https://github.com/leanprover-community/mathlib/commit/b6fa3be)
move(topology/sets/*): Move topological types of sets together ([#12648](https://github.com/leanprover-community/mathlib/pull/12648))
Move
* `topology.opens` to `topology.sets.opens`
* `topology.compacts` to `topology.sets.closeds` and `topology.sets.compacts`
`closeds` and `clopens` go into `topology.sets.closeds` and `compacts`, `nonempty_compacts`, `positive_compacts` and `compact_opens` go into `topology.sets.compacts`.
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum/basic.lean

modified src/category_theory/sites/spaces.lean

modified src/measure_theory/measure/content.lean

modified src/order/category/Frame.lean

modified src/topology/alexandroff.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/category/Top/opens.lean

modified src/topology/local_homeomorph.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/kuratowski.lean

created src/topology/sets/closeds.lean
- \+ *lemma* closed
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* clopen
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_compl
- \+ *def* to_opens

renamed src/topology/compacts.lean to src/topology/sets/compacts.lean
- \- *lemma* closed
- \- *lemma* coe_mk
- \- *lemma* coe_sup
- \- *lemma* coe_inf
- \- *lemma* coe_top
- \- *lemma* coe_bot
- \- *lemma* clopen
- \- *lemma* coe_mk
- \- *lemma* coe_sup
- \- *lemma* coe_inf
- \- *lemma* coe_top
- \- *lemma* coe_bot
- \- *lemma* coe_sdiff
- \- *lemma* coe_compl
- \- *def* to_opens

renamed src/topology/opens.lean to src/topology/sets/opens.lean



## [2022-03-14 07:05:50](https://github.com/leanprover-community/mathlib/commit/778dfd5)
chore(analysis/locally_convex/basic): generalize lemmas and add simple lemmas  ([#12643](https://github.com/leanprover-community/mathlib/pull/12643))
Gerenalize all 'simple' lemmas for `absorb` and `absorbent` to the type-class `[semi_normed_ring 𝕜] [has_scalar 𝕜 E]`.
Additionally, add the lemmas `absorbs_empty`, `balanced_mem` and `zero_singleton_balanced`.
#### Estimated changes
modified src/analysis/locally_convex/basic.lean
- \+ *lemma* absorbs_empty
- \+ *lemma* balanced_mem
- \+/\- *lemma* balanced_univ
- \+/\- *lemma* balanced.union
- \+/\- *lemma* balanced.inter
- \+/\- *lemma* balanced.add
- \+ *lemma* zero_singleton_balanced
- \+/\- *lemma* balanced_univ
- \+/\- *lemma* balanced.union
- \+/\- *lemma* balanced.inter
- \+/\- *lemma* balanced.add
- \+/\- *def* absorbent
- \+/\- *def* balanced
- \+/\- *def* absorbent
- \+/\- *def* balanced



## [2022-03-14 07:05:49](https://github.com/leanprover-community/mathlib/commit/f8d947c)
add endofunctor.algebra ([#12642](https://github.com/leanprover-community/mathlib/pull/12642))
This is the second attempt at the following outdated pull request: https://github.com/leanprover-community/mathlib/pull/12295
The original post:
In this PR I define algebras of endofunctors, make the forgetful functor to the ambient category, and show that initial algebras have isomorphisms as their structure maps. This is mostly taken from `monad.algebra`.
#### Estimated changes
created src/category_theory/endofunctor/algebra.lean
- \+ *lemma* id_eq_id
- \+ *lemma* id_f
- \+ *lemma* comp_eq_comp
- \+ *lemma* comp_f
- \+ *lemma* iso_of_iso
- \+ *lemma* left_inv'
- \+ *lemma* left_inv
- \+ *lemma* right_inv
- \+ *lemma* str_is_iso
- \+ *def* id
- \+ *def* comp
- \+ *def* iso_mk
- \+ *def* forget
- \+ *def* functor_of_nat_trans
- \+ *def* functor_of_nat_trans_id
- \+ *def* functor_of_nat_trans_comp
- \+ *def* functor_of_nat_trans_eq
- \+ *def* equiv_of_nat_iso
- \+ *def* str_inv



## [2022-03-14 05:19:50](https://github.com/leanprover-community/mathlib/commit/174f1da)
refactor(set_theory/ordinal_arithmetic): Turn various results into simp lemmas ([#12661](https://github.com/leanprover-community/mathlib/pull/12661))
In order to do this, we had to change the direction of various equalities.
#### Estimated changes
modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* sup_eq_bsup
- \+/\- *theorem* sup_eq_bsup'
- \+/\- *theorem* bsup_eq_sup'
- \+/\- *theorem* bsup_eq_sup
- \+ *theorem* sup_eq_lsub
- \+ *theorem* bsup_eq_blsub
- \+/\- *theorem* lsub_eq_blsub'
- \+/\- *theorem* lsub_eq_blsub
- \+/\- *theorem* blsub_eq_lsub'
- \+/\- *theorem* blsub_eq_lsub
- \+/\- *theorem* bsup_eq_sup
- \+/\- *theorem* bsup_eq_sup'
- \+/\- *theorem* sup_eq_bsup'
- \+/\- *theorem* sup_eq_bsup
- \+/\- *theorem* blsub_eq_lsub'
- \+/\- *theorem* blsub_eq_lsub
- \+/\- *theorem* lsub_eq_blsub'
- \+/\- *theorem* lsub_eq_blsub



## [2022-03-14 05:19:49](https://github.com/leanprover-community/mathlib/commit/ad0988b)
docs(algebra/*): Add docstrings to additive lemmas ([#12578](https://github.com/leanprover-community/mathlib/pull/12578))
Many additive lemmas had no docstrings while their multiplicative counterparts had. This adds them in all files under `algebra`.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_ite_eq'
- \+/\- *lemma* prod_ite_eq'
- \- *lemma* sum_comp

modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_induction
- \+/\- *lemma* finsum_smul
- \+/\- *lemma* finprod_mul_distrib
- \+/\- *lemma* finprod_div_distrib
- \+/\- *lemma* finprod_mem_mul_distrib'
- \+/\- *lemma* finprod_mem_one
- \+/\- *lemma* finprod_mem_of_eq_on_one
- \+/\- *lemma* exists_ne_one_of_finprod_mem_ne_one
- \+/\- *lemma* finprod_mem_mul_distrib
- \+/\- *lemma* monoid_hom.map_finprod_mem'
- \+/\- *lemma* monoid_hom.map_finprod_mem
- \+/\- *lemma* finprod_mem_div_distrib
- \+/\- *lemma* finprod_mem_empty
- \+/\- *lemma* nonempty_of_finprod_mem_ne_one
- \+/\- *lemma* finprod_mem_union_inter
- \+/\- *lemma* finprod_mem_union_inter'
- \+/\- *lemma* finprod_mem_union'
- \+/\- *lemma* finprod_mem_union
- \+/\- *lemma* finprod_mem_union''
- \+/\- *lemma* finprod_mem_singleton
- \+/\- *lemma* finprod_mem_insert'
- \+/\- *lemma* finprod_mem_insert
- \+/\- *lemma* finprod_mem_insert_of_eq_one_if_not_mem
- \+/\- *lemma* finprod_mem_insert_one
- \+/\- *lemma* finprod_mem_dvd
- \+/\- *lemma* finprod_mem_pair
- \+/\- *lemma* finprod_mem_image'
- \+/\- *lemma* finprod_mem_image
- \+/\- *lemma* finprod_mem_range'
- \+/\- *lemma* finprod_mem_range
- \+/\- *lemma* finprod_mem_eq_of_bij_on
- \+/\- *lemma* finprod_eq_of_bijective
- \+/\- *lemma* finprod_comp
- \+/\- *lemma* finprod_mem_mul_diff'
- \+/\- *lemma* finprod_mem_mul_diff
- \+/\- *lemma* finprod_mem_Union
- \+/\- *lemma* finprod_mem_bUnion
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_comm
- \+/\- *lemma* finprod_mem_induction
- \+/\- *lemma* mul_finsum
- \+/\- *lemma* finsum_mul
- \+/\- *lemma* finprod_mem_finset_product'
- \+/\- *lemma* finprod_mem_finset_product
- \+/\- *lemma* finprod_emb_domain'
- \+/\- *lemma* finprod_induction
- \+/\- *lemma* finsum_smul
- \+/\- *lemma* finprod_mul_distrib
- \+/\- *lemma* finprod_div_distrib
- \+/\- *lemma* finprod_mem_mul_distrib'
- \+/\- *lemma* finprod_mem_one
- \+/\- *lemma* finprod_mem_of_eq_on_one
- \+/\- *lemma* exists_ne_one_of_finprod_mem_ne_one
- \+/\- *lemma* finprod_mem_mul_distrib
- \+/\- *lemma* monoid_hom.map_finprod_mem'
- \+/\- *lemma* monoid_hom.map_finprod_mem
- \+/\- *lemma* finprod_mem_div_distrib
- \+/\- *lemma* finprod_mem_empty
- \+/\- *lemma* nonempty_of_finprod_mem_ne_one
- \+/\- *lemma* finprod_mem_union_inter
- \+/\- *lemma* finprod_mem_union_inter'
- \+/\- *lemma* finprod_mem_union'
- \+/\- *lemma* finprod_mem_union
- \+/\- *lemma* finprod_mem_union''
- \+/\- *lemma* finprod_mem_singleton
- \+/\- *lemma* finprod_mem_insert'
- \+/\- *lemma* finprod_mem_insert
- \+/\- *lemma* finprod_mem_insert_of_eq_one_if_not_mem
- \+/\- *lemma* finprod_mem_insert_one
- \+/\- *lemma* finprod_mem_dvd
- \+/\- *lemma* finprod_mem_pair
- \+/\- *lemma* finprod_mem_image'
- \+/\- *lemma* finprod_mem_image
- \+/\- *lemma* finprod_mem_range'
- \+/\- *lemma* finprod_mem_range
- \+/\- *lemma* finprod_mem_eq_of_bij_on
- \+/\- *lemma* finprod_eq_of_bijective
- \+/\- *lemma* finprod_comp
- \+/\- *lemma* finprod_mem_mul_diff'
- \+/\- *lemma* finprod_mem_mul_diff
- \+/\- *lemma* finprod_mem_Union
- \+/\- *lemma* finprod_mem_bUnion
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_comm
- \+/\- *lemma* finprod_mem_induction
- \+/\- *lemma* mul_finsum
- \+/\- *lemma* finsum_mul
- \+/\- *lemma* finprod_mem_finset_product'
- \+/\- *lemma* finprod_mem_finset_product
- \+/\- *lemma* finprod_emb_domain'

modified src/algebra/big_operators/nat_antidiagonal.lean

modified src/algebra/big_operators/ring.lean

modified src/algebra/category/Group/limits.lean

modified src/algebra/category/Mon/limits.lean

modified src/algebra/group/commute.lean
- \+ *lemma* mul_right
- \+ *lemma* mul_left
- \- *theorem* mul_right
- \- *theorem* mul_left

modified src/algebra/group/freiman.lean

modified src/algebra/group/hom.lean
- \+/\- *lemma* map_div
- \+/\- *lemma* map_div

modified src/algebra/group/semiconj.lean
- \+/\- *lemma* mul_right
- \+/\- *lemma* mul_left
- \+/\- *lemma* units_inv_right
- \+/\- *lemma* units_inv_symm_left
- \+/\- *lemma* conj_mk
- \+/\- *lemma* mul_right
- \+/\- *lemma* mul_left
- \+/\- *lemma* units_inv_right
- \+/\- *lemma* units_inv_symm_left
- \+/\- *lemma* conj_mk

modified src/algebra/group/units.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/indicator_function.lean
- \+/\- *lemma* mem_of_mul_indicator_ne_one
- \+/\- *lemma* prod_mul_indicator_subset
- \+/\- *lemma* mem_of_mul_indicator_ne_one
- \+/\- *lemma* prod_mul_indicator_subset

modified src/algebra/order/group.lean
- \+/\- *lemma* abs_eq_sup_inv
- \+/\- *lemma* abs_eq_sup_inv

modified src/algebra/order/hom/monoid.lean

modified src/algebra/order/lattice_group.lean
- \+ *lemma* mabs_mabs
- \- *lemma* m_abs_abs

modified src/algebra/order/monoid_lemmas.lean

modified src/algebra/pointwise.lean



## [2022-03-14 04:48:58](https://github.com/leanprover-community/mathlib/commit/580e1d9)
feat(analysis/inner_product_space/pi_L2): `linear_isometry.extend` ([#12192](https://github.com/leanprover-community/mathlib/pull/12192))
Let `S` be a subspace of a finite-dimensional inner product
space `V`.  A linear isometry mapping `S` into `V` can be extended to a
full isometry of `V`.  Note that this is false if we remove the
finite-dimensional hypothesis; consider the shift operator
(0, x_2, x_3, ...) to (x_2, x_3, x_4, ...).
I hope that the naming choice is consistent.  Combining the two
`simp only` blocks in `linear_isometry.extend_apply` results in a
timeout, but they seem to work okay split up.
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* linear_isometry.extend_apply



## [2022-03-14 02:40:00](https://github.com/leanprover-community/mathlib/commit/3751ec6)
feat(measure_theory/group/fundamental_domain): ess_sup_measure_restrict ([#12603](https://github.com/leanprover-community/mathlib/pull/12603))
If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as that of `f` on all of its domain.
#### Estimated changes
modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_eq_Inf
- \+ *lemma* ess_sup_mono_measure'

modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_zero_of_invariant
- \+ *lemma* ess_sup_measure_restrict



## [2022-03-13 14:52:04](https://github.com/leanprover-community/mathlib/commit/223e742)
feat(analysis/*/{exponential, spectrum}): spectrum of a selfadjoint element is real ([#12417](https://github.com/leanprover-community/mathlib/pull/12417))
This provides several properties of the exponential function and uses it to prove that for `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜 𝕜` maps the spectrum of `a : A` (where `A` is a `𝕜`-algebra) into the spectrum of `exp 𝕜 A a`. In addition, `exp ℂ A (I • a)` is unitary when `a` is selfadjoint. Consequently, the spectrum of a selfadjoint element is real.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* algebra_map_clm_coe
- \+ *lemma* algebra_map_clm_to_linear_map
- \+ *def* algebra_map_clm

modified src/analysis/normed_space/exponential.lean
- \+ *lemma* algebra_map_exp_comm_of_mem_ball
- \+ *lemma* algebra_map_exp_comm
- \+ *lemma* star_exp

modified src/analysis/normed_space/spectrum.lean
- \+ *theorem* exp_mem_exp

created src/analysis/normed_space/star/exponential.lean
- \+ *lemma* self_adjoint.exp_i_smul_unitary
- \+ *lemma* commute.exp_unitary_add
- \+ *lemma* commute.exp_unitary

modified src/analysis/normed_space/star/spectrum.lean
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal
- \+ *theorem* self_adjoint.mem_spectrum_eq_re
- \+ *theorem* self_adjoint.mem_spectrum_eq_re'
- \+ *theorem* self_adjoint.coe_re_map_spectrum
- \+ *theorem* self_adjoint.coe_re_map_spectrum'



## [2022-03-13 13:32:14](https://github.com/leanprover-community/mathlib/commit/7d34f78)
chore(algebra/algebra/subalgebra): reduce imports ([#12636](https://github.com/leanprover-community/mathlib/pull/12636))
Splitting a file, and reducing imports. No change in contents.
#### Estimated changes
renamed src/algebra/algebra/subalgebra.lean to src/algebra/algebra/subalgebra/basic.lean
- \- *lemma* coe_pointwise_smul
- \- *lemma* pointwise_smul_to_subsemiring
- \- *lemma* pointwise_smul_to_submodule
- \- *lemma* pointwise_smul_to_subring
- \- *lemma* smul_mem_pointwise_smul
- \- *theorem* mul_self

created src/algebra/algebra/subalgebra/pointwise.lean
- \+ *lemma* coe_pointwise_smul
- \+ *lemma* pointwise_smul_to_subsemiring
- \+ *lemma* pointwise_smul_to_submodule
- \+ *lemma* pointwise_smul_to_subring
- \+ *lemma* smul_mem_pointwise_smul
- \+ *theorem* mul_self

modified src/algebra/algebra/tower.lean

modified src/algebra/category/Algebra/basic.lean

modified src/algebra/direct_sum/internal.lean

modified src/algebra/free_algebra.lean

modified src/algebra/lie/of_associative.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/tensor_algebra/basic.lean

modified src/ring_theory/adjoin/basic.lean

modified src/ring_theory/dedekind_domain/ideal.lean

modified src/ring_theory/polynomial/symmetric.lean

modified src/topology/algebra/algebra.lean

modified src/topology/continuous_function/algebra.lean



## [2022-03-13 07:59:44](https://github.com/leanprover-community/mathlib/commit/daa257f)
feat(analysis/normed_space/star/basic): `matrix.entrywise_sup_norm_star_eq_norm` ([#12201](https://github.com/leanprover-community/mathlib/pull/12201))
This is precisely the statement needed for a `normed_star_monoid`
instance on matrices using the entrywise sup norm.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* matrix.norm_entry_le_entrywise_sup_norm
- \+/\- *lemma* matrix.norm_entry_le_entrywise_sup_norm

modified src/analysis/normed_space/star/basic.lean
- \+ *lemma* matrix.entrywise_sup_norm_star_eq_norm



## [2022-03-13 04:14:17](https://github.com/leanprover-community/mathlib/commit/73530b5)
feat(algebra/algebra/spectrum): prove spectral inclusion for algebra homomorphisms ([#12573](https://github.com/leanprover-community/mathlib/pull/12573))
If `φ : A →ₐ[R] B` is an `R`-algebra homomorphism, then for any `a : A`, `spectrum R (φ a) ⊆ spectrum R a`.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \+ *lemma* mem_resolvent_set_apply
- \+ *lemma* spectrum_apply_subset



## [2022-03-13 00:04:24](https://github.com/leanprover-community/mathlib/commit/9f1f8c1)
feat(ring_theory/graded_algebra/homogeneous_ideal): definition of irrelevant ideal of a graded algebra ([#12548](https://github.com/leanprover-community/mathlib/pull/12548))
For an `ℕ`-graded ring `⨁ᵢ 𝒜ᵢ`, the irrelevant ideal refers to `⨁_{i>0} 𝒜ᵢ`.
This construction is used in the Proj construction in algebraic geometry.
#### Estimated changes
modified src/ring_theory/graded_algebra/basic.lean
- \+ *def* graded_algebra.proj_zero_ring_hom

modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* homogeneous_ideal.mem_irrelevant_iff
- \+ *lemma* homogeneous_ideal.coe_irrelevant
- \+ *def* homogeneous_ideal.irrelevant



## [2022-03-12 21:08:56](https://github.com/leanprover-community/mathlib/commit/5b36941)
feat(data/list/basic): Stronger form of `fold_fixed` ([#12613](https://github.com/leanprover-community/mathlib/pull/12613))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* foldl_fixed'
- \+ *theorem* foldr_fixed'
- \+/\- *theorem* foldl_fixed
- \+/\- *theorem* foldr_fixed
- \+/\- *theorem* foldl_fixed
- \+/\- *theorem* foldr_fixed



## [2022-03-12 19:48:16](https://github.com/leanprover-community/mathlib/commit/3da03b9)
refactor(group_theory/commutator): Use variables and rearrange lemmas ([#12629](https://github.com/leanprover-community/mathlib/pull/12629))
This PR adds variables, and rearranges some of the lemmas (moving the lemmas about normal subgroups to a separate section).
#### Estimated changes
modified src/group_theory/commutator.lean
- \+/\- *lemma* commutator_mem_commutator
- \+/\- *lemma* commutator_le
- \+/\- *lemma* commutator_mono
- \+/\- *lemma* commutator_eq_bot_iff_le_centralizer
- \+/\- *lemma* commutator_comm_le
- \+/\- *lemma* commutator_comm
- \+/\- *lemma* commutator_def'
- \+/\- *lemma* commutator_le_right
- \+/\- *lemma* commutator_le_left
- \+/\- *lemma* commutator_bot_left
- \+/\- *lemma* commutator_bot_right
- \+/\- *lemma* commutator_le_inf
- \+/\- *lemma* map_commutator
- \+/\- *lemma* commutator_prod_prod
- \+/\- *lemma* commutator_mem_commutator
- \+/\- *lemma* commutator_le
- \+/\- *lemma* commutator_mono
- \+/\- *lemma* commutator_def'
- \+/\- *lemma* commutator_comm_le
- \+/\- *lemma* commutator_comm
- \+/\- *lemma* commutator_eq_bot_iff_le_centralizer
- \+/\- *lemma* commutator_le_right
- \+/\- *lemma* commutator_le_left
- \+/\- *lemma* commutator_bot_left
- \+/\- *lemma* commutator_bot_right
- \+/\- *lemma* commutator_le_inf
- \+/\- *lemma* map_commutator
- \+/\- *lemma* commutator_prod_prod



## [2022-03-12 18:01:22](https://github.com/leanprover-community/mathlib/commit/23269bf)
feat(category_theory/preadditive/Mat): ring version ([#12617](https://github.com/leanprover-community/mathlib/pull/12617))
#### Estimated changes
modified src/category_theory/preadditive/Mat.lean
- \+ *lemma* id_def
- \+ *lemma* id_apply
- \+ *lemma* id_apply_self
- \+ *lemma* id_apply_of_ne
- \+ *lemma* comp_def
- \+ *lemma* comp_apply
- \+ *def* Mat
- \+ *def* equivalence_single_obj_inverse
- \+ *def* equivalence_single_obj



## [2022-03-12 18:01:21](https://github.com/leanprover-community/mathlib/commit/707df2c)
feat(model_theory/definability): Definability with parameters ([#12611](https://github.com/leanprover-community/mathlib/pull/12611))
Extends the definition of definable sets to include a parameter set.
Defines shorthands is_definable₁ and is_definable₂ for 1- and 2-dimensional definable sets.
#### Estimated changes
modified src/model_theory/definability.lean
- \+ *lemma* definable_empty
- \+ *lemma* definable_univ
- \+ *lemma* definable.inter
- \+ *lemma* definable.union
- \+ *lemma* definable_finset_inf
- \+ *lemma* definable_finset_sup
- \+ *lemma* definable_finset_bInter
- \+ *lemma* definable_finset_bUnion
- \+ *lemma* definable.compl
- \+ *lemma* definable.sdiff
- \+ *lemma* definable.preimage_comp
- \+ *lemma* definable.image_comp_equiv
- \+/\- *lemma* mem_top
- \+/\- *lemma* coe_top
- \+/\- *lemma* not_mem_bot
- \+/\- *lemma* coe_bot
- \+/\- *lemma* le_iff
- \+/\- *lemma* coe_sup
- \+/\- *lemma* mem_sup
- \+/\- *lemma* coe_inf
- \+/\- *lemma* mem_inf
- \+/\- *lemma* mem_compl
- \+/\- *lemma* coe_compl
- \- *lemma* is_definable_empty
- \- *lemma* is_definable_univ
- \- *lemma* is_definable.inter
- \- *lemma* is_definable.union
- \- *lemma* is_definable.compl
- \- *lemma* is_definable.sdiff
- \+/\- *lemma* mem_top
- \+/\- *lemma* coe_top
- \+/\- *lemma* not_mem_bot
- \+/\- *lemma* coe_bot
- \+/\- *lemma* le_iff
- \+/\- *lemma* coe_sup
- \+/\- *lemma* mem_sup
- \+/\- *lemma* coe_inf
- \+/\- *lemma* mem_inf
- \+/\- *lemma* mem_compl
- \+/\- *lemma* coe_compl
- \+ *def* definable₁
- \+ *def* definable₂
- \+/\- *def* definable_set
- \+/\- *def* definable_set



## [2022-03-12 18:01:20](https://github.com/leanprover-community/mathlib/commit/9293174)
feat(algebra/category/Module): monoidal_preadditive ([#12607](https://github.com/leanprover-community/mathlib/pull/12607))
#### Estimated changes
modified src/algebra/category/Module/monoidal.lean

modified src/category_theory/monoidal/preadditive.lean



## [2022-03-12 18:01:19](https://github.com/leanprover-community/mathlib/commit/e4ea2bc)
feat(topology/algebra/continuous_monoid_hom): Define the Pontryagin dual ([#12602](https://github.com/leanprover-community/mathlib/pull/12602))
This PR adds the definition of the Pontryagin dual.
We're still missing the locally compact instance. I thought I could get it from `closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B))`, but actually `C(A, B)` is almost never locally compact.
#### Estimated changes
modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *def* pontryagin_dual



## [2022-03-12 18:01:18](https://github.com/leanprover-community/mathlib/commit/5a9fb92)
feat(topology/category/Locale): The category of locales ([#12580](https://github.com/leanprover-community/mathlib/pull/12580))
Define `Locale`, the category of locales, as the opposite of `Frame`.
#### Estimated changes
modified src/order/category/Frame.lean
- \+ *def* Top_op_to_Frame

created src/topology/category/Locale.lean
- \+ *lemma* coe_of
- \+ *def* Locale
- \+ *def* of
- \+ *def* Top_to_Locale

modified src/topology/opens.lean
- \+ *lemma* comap_injective



## [2022-03-12 18:01:17](https://github.com/leanprover-community/mathlib/commit/96bae07)
feat(order/complete_lattice): add `complete_lattice.independent_pair` ([#12565](https://github.com/leanprover-community/mathlib/pull/12565))
This makes `complete_lattice.independent` easier to work with in the degenerate case.
#### Estimated changes
modified counterexamples/direct_sum_is_internal.lean

modified src/data/set/basic.lean
- \+ *lemma* insert_diff_eq_singleton

modified src/order/complete_lattice.lean
- \+ *lemma* set_independent_pair
- \+ *lemma* independent_pair



## [2022-03-12 16:17:42](https://github.com/leanprover-community/mathlib/commit/7e5ac6a)
chore(analysis/convex/strict): Reduce typeclass assumptions, golf ([#12627](https://github.com/leanprover-community/mathlib/pull/12627))
Move lemmas around so they are stated with the correct generality. Restate theorems using pointwise operations. Golf proofs. Fix typos in docstrings.
#### Estimated changes
modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex.linear_image
- \+/\- *lemma* strict_convex.add
- \+/\- *lemma* strict_convex.add_left
- \+/\- *lemma* strict_convex.add_right
- \+ *lemma* strict_convex.vadd
- \+/\- *lemma* strict_convex.smul
- \+/\- *lemma* strict_convex.affinity
- \+/\- *lemma* strict_convex.linear_image
- \+/\- *lemma* strict_convex.add_left
- \+/\- *lemma* strict_convex.add_right
- \+/\- *lemma* strict_convex.add
- \+/\- *lemma* strict_convex.smul
- \+/\- *lemma* strict_convex.affinity



## [2022-03-12 16:17:41](https://github.com/leanprover-community/mathlib/commit/22bdc8e)
feat(order/upper_lower): Upper/lower sets ([#12189](https://github.com/leanprover-community/mathlib/pull/12189))
Define upper and lower sets both as unbundled predicates and as bundled types.
#### Estimated changes
modified src/order/complete_boolean_algebra.lean
- \+ *lemma* compl_Inf
- \+ *lemma* compl_Sup
- \+ *lemma* compl_Inf'
- \+ *lemma* compl_Sup'
- \- *theorem* compl_Inf
- \- *theorem* compl_Sup

created src/order/upper_lower.lean
- \+ *lemma* is_upper_set_empty
- \+ *lemma* is_lower_set_empty
- \+ *lemma* is_upper_set_univ
- \+ *lemma* is_lower_set_univ
- \+ *lemma* is_upper_set.compl
- \+ *lemma* is_lower_set.compl
- \+ *lemma* is_upper_set.union
- \+ *lemma* is_lower_set.union
- \+ *lemma* is_upper_set.inter
- \+ *lemma* is_lower_set.inter
- \+ *lemma* is_upper_set_Union
- \+ *lemma* is_lower_set_Union
- \+ *lemma* is_upper_set_Union₂
- \+ *lemma* is_lower_set_Union₂
- \+ *lemma* is_upper_set_sUnion
- \+ *lemma* is_lower_set_sUnion
- \+ *lemma* is_upper_set_Inter
- \+ *lemma* is_lower_set_Inter
- \+ *lemma* is_upper_set_Inter₂
- \+ *lemma* is_lower_set_Inter₂
- \+ *lemma* is_upper_set_sInter
- \+ *lemma* is_lower_set_sInter
- \+ *lemma* is_lower_set_preimage_of_dual_iff
- \+ *lemma* is_upper_set_preimage_of_dual_iff
- \+ *lemma* is_lower_set_preimage_to_dual_iff
- \+ *lemma* is_upper_set_preimage_to_dual_iff
- \+ *lemma* ext
- \+ *lemma* ext
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_Sup
- \+ *lemma* coe_Inf
- \+ *lemma* coe_supr
- \+ *lemma* coe_infi
- \+ *lemma* coe_supr₂
- \+ *lemma* coe_infi₂
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_Sup
- \+ *lemma* coe_Inf
- \+ *lemma* coe_supr
- \+ *lemma* coe_infi
- \+ *lemma* coe_supr₂
- \+ *lemma* coe_infi₂
- \+ *lemma* coe_compl
- \+ *lemma* compl_compl
- \+ *lemma* compl_supr₂
- \+ *lemma* compl_infi₂
- \+ *lemma* coe_compl
- \+ *lemma* compl_compl
- \+ *lemma* compl_supr₂
- \+ *lemma* compl_infi₂
- \+ *def* is_upper_set
- \+ *def* is_lower_set
- \+ *def* upper_set.compl
- \+ *def* lower_set.compl



## [2022-03-12 15:43:41](https://github.com/leanprover-community/mathlib/commit/dc4e5cb)
chore(analysis): move lemmas around ([#12621](https://github.com/leanprover-community/mathlib/pull/12621))
* move `smul_unit_ball` to `analysis.normed_space.pointwise`, rename it to `smul_unit_ball_of_pos`;
* reorder lemmas in `analysis.normed_space.pointwise`;
* add `vadd_ball_zero`, `vadd_closed_ball_zero`, `smul_unit`, `affinity_unit_ball`, `affinity_unit_closed_ball`.
#### Estimated changes
modified src/analysis/convex/gauge.lean
- \- *lemma* smul_unit_ball

modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* smul_unit_ball
- \+ *lemma* vadd_ball_zero
- \+ *lemma* vadd_closed_ball_zero
- \+ *lemma* smul_unit_ball_of_pos
- \+ *lemma* smul_closed_unit_ball
- \+ *lemma* smul_closed_unit_ball_of_nonneg
- \+ *lemma* normed_space.sphere_nonempty
- \+ *lemma* smul_sphere
- \+ *lemma* affinity_unit_ball
- \+ *lemma* affinity_unit_closed_ball
- \- *theorem* normed_space.sphere_nonempty
- \- *theorem* smul_sphere



## [2022-03-12 14:08:13](https://github.com/leanprover-community/mathlib/commit/7257ee7)
chore(data/nat/prime): restate card_multiples without finset.sep ([#12625](https://github.com/leanprover-community/mathlib/pull/12625))
As suggested by Eric Wieser in [#12592](https://github.com/leanprover-community/mathlib/pull/12592).
#### Estimated changes
modified src/data/nat/prime.lean
- \+/\- *lemma* card_multiples
- \+/\- *lemma* card_multiples



## [2022-03-12 14:08:12](https://github.com/leanprover-community/mathlib/commit/a63b99c)
chore(category_theory/closed/monoidal): fix notation ([#12612](https://github.com/leanprover-community/mathlib/pull/12612))
Previously the `C` in the internal hom arrow ` ⟶[C] ` was hardcoded, which wasn't very useful!
I've also reduced the precedence slightly, so we now require more parentheses, but I think these are less confusing rather than more so it is a good side effect?
#### Estimated changes
modified src/category_theory/closed/monoidal.lean
- \+/\- *lemma* hom_equiv_symm_apply_eq
- \+/\- *lemma* uncurry_natural_right
- \+/\- *lemma* uncurry_natural_left
- \+/\- *lemma* curry_uncurry
- \+/\- *lemma* curry_eq_iff
- \+/\- *lemma* eq_curry_iff
- \+/\- *lemma* uncurry_eq
- \+/\- *lemma* curry_injective
- \+/\- *lemma* uncurry_injective
- \+/\- *lemma* hom_equiv_symm_apply_eq
- \+/\- *lemma* uncurry_natural_right
- \+/\- *lemma* uncurry_natural_left
- \+/\- *lemma* curry_uncurry
- \+/\- *lemma* curry_eq_iff
- \+/\- *lemma* eq_curry_iff
- \+/\- *lemma* uncurry_eq
- \+/\- *lemma* curry_injective
- \+/\- *lemma* uncurry_injective
- \+/\- *def* curry
- \+/\- *def* uncurry
- \+/\- *def* curry
- \+/\- *def* uncurry



## [2022-03-12 14:08:11](https://github.com/leanprover-community/mathlib/commit/956f3db)
chore(category_theory/limits): correct lemma names ([#12606](https://github.com/leanprover-community/mathlib/pull/12606))
#### Estimated changes
modified src/category_theory/abelian/exact.lean

modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_comparison_comp_ι
- \+ *lemma* π_comp_cokernel_comparison
- \- *lemma* kernel_comparison_comp_π
- \- *lemma* ι_comp_cokernel_comparison



## [2022-03-12 14:08:10](https://github.com/leanprover-community/mathlib/commit/9456a74)
feat(group_theory/commutator): Prove `commutator_eq_bot_iff_le_centralizer` ([#12598](https://github.com/leanprover-community/mathlib/pull/12598))
This lemma is needed for the three subgroups lemma.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+ *lemma* commutator_eq_bot_iff_le_centralizer



## [2022-03-12 14:08:09](https://github.com/leanprover-community/mathlib/commit/b9ab27b)
feat(group_theory/subgroup/basic): add eq_one_of_noncomm_prod_eq_one_of_independent ([#12525](https://github.com/leanprover-community/mathlib/pull/12525))
`finset.noncomm_prod` is “injective” in `f` if `f` maps into independent subgroups.  It
generalizes (one direction of) `subgroup.disjoint_iff_mul_eq_one`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* eq_one_of_noncomm_prod_eq_one_of_independent



## [2022-03-12 13:35:45](https://github.com/leanprover-community/mathlib/commit/b21c1c9)
split(analysis/locally_convex/basic): Split off `analysis.seminorm` ([#12624](https://github.com/leanprover-community/mathlib/pull/12624))
Move `balanced`, `absorbs`, `absorbent` to a new file.
For `analysis.seminorm`, I'm crediting
* Jean for [#4827](https://github.com/leanprover-community/mathlib/pull/4827)
* myself for
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
  * [#11487](https://github.com/leanprover-community/mathlib/pull/11487)
* Moritz for
  * [#11329](https://github.com/leanprover-community/mathlib/pull/11329)
  * [#11414](https://github.com/leanprover-community/mathlib/pull/11414)
  * [#11477](https://github.com/leanprover-community/mathlib/pull/11477)
For `analysis.locally_convex.basic`, I'm crediting
* Jean for [#4827](https://github.com/leanprover-community/mathlib/pull/4827)
* Bhavik for
  * [#7358](https://github.com/leanprover-community/mathlib/pull/7358)
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
* myself for
  * [#9097](https://github.com/leanprover-community/mathlib/pull/9097)
  * [#10999](https://github.com/leanprover-community/mathlib/pull/10999)
  * [#11487](https://github.com/leanprover-community/mathlib/pull/11487)
#### Estimated changes
created src/analysis/locally_convex/basic.lean
- \+ *lemma* balanced_univ
- \+ *lemma* balanced.union
- \+ *lemma* balanced.inter
- \+ *lemma* balanced.add
- \+ *lemma* absorbs.mono
- \+ *lemma* absorbs.mono_left
- \+ *lemma* absorbs.mono_right
- \+ *lemma* absorbs.union
- \+ *lemma* absorbs_union
- \+ *lemma* absorbent.subset
- \+ *lemma* absorbent_iff_forall_absorbs_singleton
- \+ *lemma* absorbent.absorbs
- \+ *lemma* absorbent_iff_nonneg_lt
- \+ *lemma* balanced.smul
- \+ *lemma* balanced.smul_mono
- \+ *lemma* balanced.absorbs_self
- \+ *lemma* balanced.subset_smul
- \+ *lemma* balanced.smul_eq
- \+ *lemma* absorbs.inter
- \+ *lemma* absorbs_inter
- \+ *lemma* absorbent_univ
- \+ *lemma* absorbent_nhds_zero
- \+ *lemma* balanced_zero_union_interior
- \+ *lemma* balanced.interior
- \+ *lemma* balanced.closure
- \+ *lemma* absorbs_zero_iff
- \+ *lemma* absorbent.zero_mem
- \+ *def* absorbs
- \+ *def* absorbent
- \+ *def* balanced

modified src/analysis/seminorm.lean
- \- *lemma* balanced_univ
- \- *lemma* balanced.union
- \- *lemma* balanced.inter
- \- *lemma* balanced.add
- \- *lemma* absorbs.mono
- \- *lemma* absorbs.mono_left
- \- *lemma* absorbs.mono_right
- \- *lemma* absorbs.union
- \- *lemma* absorbs_union
- \- *lemma* absorbent.subset
- \- *lemma* absorbent_iff_forall_absorbs_singleton
- \- *lemma* absorbent.absorbs
- \- *lemma* absorbent_iff_nonneg_lt
- \- *lemma* balanced.smul
- \- *lemma* balanced.smul_mono
- \- *lemma* balanced.absorbs_self
- \- *lemma* balanced.subset_smul
- \- *lemma* balanced.smul_eq
- \- *lemma* absorbs.inter
- \- *lemma* absorbs_inter
- \- *lemma* absorbent_univ
- \- *lemma* absorbent_nhds_zero
- \- *lemma* balanced_zero_union_interior
- \- *lemma* balanced.interior
- \- *lemma* balanced.closure
- \- *lemma* absorbs_zero_iff
- \- *lemma* absorbent.zero_mem
- \- *def* absorbs
- \- *def* absorbent
- \- *def* balanced



## [2022-03-12 11:37:20](https://github.com/leanprover-community/mathlib/commit/a4187fe)
chore(algebra/category/Module): remove unnecessary universe restriction ([#12610](https://github.com/leanprover-community/mathlib/pull/12610))
#### Estimated changes
modified src/algebra/category/Module/basic.lean
- \+/\- *def* of_hom
- \+/\- *def* of_hom



## [2022-03-12 11:37:19](https://github.com/leanprover-community/mathlib/commit/31d28c6)
fix(src/algebra/big_operators/multiset): unify prod_le_pow_card and prod_le_of_forall_le ([#12589](https://github.com/leanprover-community/mathlib/pull/12589))
using the name `prod_le_pow_card` as per https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/duplicate.20lemmas
but use the phrasing of prod_le_of_forall_le with non-implicit
`multiset`, as that is how it is used.
#### Estimated changes
modified src/algebra/big_operators/multiset.lean
- \+/\- *lemma* prod_le_pow_card
- \- *lemma* prod_le_of_forall_le
- \+/\- *lemma* prod_le_pow_card

modified src/algebra/big_operators/order.lean
- \+ *lemma* prod_le_pow_card
- \+ *lemma* pow_card_le_prod
- \- *lemma* prod_le_of_forall_le
- \- *lemma* le_prod_of_forall_le

modified src/algebra/polynomial/big_operators.lean

modified src/combinatorics/double_counting.lean

modified src/data/list/prod_monoid.lean
- \+ *lemma* prod_le_pow_card
- \- *lemma* prod_le_of_forall_le

modified src/linear_algebra/matrix/polynomial.lean



## [2022-03-12 11:06:34](https://github.com/leanprover-community/mathlib/commit/2241588)
feat(topology/homotopy): Homotopic maps induce naturally isomorphic functors between fundamental groupoid ([#11595](https://github.com/leanprover-community/mathlib/pull/11595))
#### Estimated changes
modified src/category_theory/category/Groupoid.lean
- \+ *lemma* id_to_functor

modified src/topology/homotopy/fundamental_groupoid.lean
- \+ *lemma* map_eq

created src/topology/homotopy/induced_maps.lean
- \+ *lemma* hcast_def
- \+ *lemma* heq_path_of_eq_image
- \+ *lemma* eq_path_of_eq_image
- \+ *lemma* ulift_apply
- \+ *lemma* apply_zero_path
- \+ *lemma* apply_one_path
- \+ *lemma* eval_at_eq
- \+ *lemma* eq_diag_path
- \+ *def* path01
- \+ *def* upath01
- \+ *def* uhpath01
- \+ *def* ulift_map
- \+ *def* diagonal_path
- \+ *def* diagonal_path'
- \+ *def* homotopic_maps_nat_iso
- \+ *def* equiv_of_homotopy_equiv

modified src/topology/homotopy/path.lean
- \+ *lemma* hpath_hext
- \+ *def* eval_at

modified src/topology/homotopy/product.lean
- \+ *lemma* prod_to_prod_Top_map



## [2022-03-12 09:57:54](https://github.com/leanprover-community/mathlib/commit/5f3f70f)
doc(category_theory/monoidal/rigid): noting future work ([#12620](https://github.com/leanprover-community/mathlib/pull/12620))
#### Estimated changes
modified src/category_theory/monoidal/rigid.lean



## [2022-03-12 09:57:53](https://github.com/leanprover-community/mathlib/commit/3d41a5b)
refactor(group_theory/commutator): Golf proof of `commutator_mono` ([#12619](https://github.com/leanprover-community/mathlib/pull/12619))
This PR golfs the proof of `commutator_mono` by using `commutator_le` rather than `closure_mono`.
#### Estimated changes
modified src/group_theory/commutator.lean



## [2022-03-12 09:57:52](https://github.com/leanprover-community/mathlib/commit/72c6979)
refactor(set_theory/ordinal_arithmetic): remove dot notation ([#12614](https://github.com/leanprover-community/mathlib/pull/12614))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* enum_ord_strict_mono
- \- *theorem* enum_ord.strict_mono



## [2022-03-12 08:36:18](https://github.com/leanprover-community/mathlib/commit/3aaa564)
refactor(group_theory/commutator): Golf proof of `commutator_comm` ([#12600](https://github.com/leanprover-community/mathlib/pull/12600))
This PR golfs the proof of `commutator_comm`.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+ *lemma* commutator_comm_le



## [2022-03-12 05:57:32](https://github.com/leanprover-community/mathlib/commit/1463f59)
fix(tactic/suggest): fixing `library_search` ([#12616](https://github.com/leanprover-community/mathlib/pull/12616))
Further enhancing `library_search` search possibilities for 'ne' and 'not eq'
Related: https://github.com/leanprover-community/mathlib/pull/11742
#### Estimated changes
modified src/tactic/suggest.lean

modified test/library_search/basic.lean



## [2022-03-12 05:57:31](https://github.com/leanprover-community/mathlib/commit/e8d0cac)
feat(analysis/inner_product_space/adjoint): gram lemmas ([#12139](https://github.com/leanprover-community/mathlib/pull/12139))
The gram operator is a self-adjoint, positive operator.
#### Estimated changes
modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* is_self_adjoint_adjoint_mul_self
- \+ *lemma* re_inner_adjoint_mul_self_nonneg
- \+ *lemma* im_inner_adjoint_mul_self_eq_zero



## [2022-03-12 04:22:20](https://github.com/leanprover-community/mathlib/commit/1eaf499)
feat(group_theory/subgroup/basic): {multiset_,}noncomm_prod_mem ([#12523](https://github.com/leanprover-community/mathlib/pull/12523))
and same for submonoids.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* multiset_noncomm_prod_mem
- \+ *lemma* noncomm_prod_mem

modified src/group_theory/submonoid/membership.lean
- \+ *lemma* multiset_noncomm_prod_mem
- \+ *lemma* noncomm_prod_mem



## [2022-03-12 04:22:19](https://github.com/leanprover-community/mathlib/commit/6ee6203)
feat(counterexample) : a homogeneous ideal that is not prime but homogeneously prime ([#12485](https://github.com/leanprover-community/mathlib/pull/12485))
For graded rings, if the indexing set is nice, then a homogeneous ideal `I` is prime if and only if it is homogeneously prime, i.e. product of two homogeneous elements being in `I` implying at least one of them is in `I`. This fact is in `src/ring_theory/graded_algebra/radical.lean`. This counter example is meant to show that "nice condition" at least needs to include cancellation property by exhibiting an ideal in Zmod4^2 graded by a two element set being homogeneously prime but not prime. In [#12277](https://github.com/leanprover-community/mathlib/pull/12277), Eric suggests that this counter example is worth pr-ing, so here is the pr.
#### Estimated changes
created counterexamples/homogeneous_prime_not_prime.lean
- \+ *lemma* grading.one_mem
- \+ *lemma* grading.mul_mem
- \+ *lemma* grading.left_inv
- \+ *lemma* grading.right_inv
- \+ *lemma* I_not_prime
- \+ *lemma* I_is_homogeneous
- \+ *lemma* homogeneous_mem_or_mem
- \+ *def* submodule_z
- \+ *def* submodule_o
- \+ *def* grading
- \+ *def* grading.decompose
- \+ *def* I

modified src/ring_theory/graded_algebra/radical.lean



## [2022-03-12 02:28:54](https://github.com/leanprover-community/mathlib/commit/2e7483d)
refactor(group_theory/commutator): Move and golf `commutator_le` ([#12599](https://github.com/leanprover-community/mathlib/pull/12599))
This PR golfs `commutator_le` and moves it earlier in the file so that it can be used earlier.
This PR will conflict with [#12600](https://github.com/leanprover-community/mathlib/pull/12600), so don't merge them simultaneously (bors d+ might be better).
#### Estimated changes
modified src/group_theory/commutator.lean
- \+/\- *lemma* commutator_le
- \+/\- *lemma* commutator_le

modified src/group_theory/nilpotent.lean



## [2022-03-12 02:28:53](https://github.com/leanprover-community/mathlib/commit/09d0f02)
chore({category_theory,order}/category/*): Missing `dsimp` lemmas ([#12593](https://github.com/leanprover-community/mathlib/pull/12593))
Add the `dsimp` lemmas stating `↥(of α) = α `. Also rename the few `to_dual` functors to `dual` to match the other files.
#### Estimated changes
modified src/category_theory/category/Bipointed.lean
- \+ *lemma* coe_of

modified src/category_theory/category/PartialFun.lean
- \+ *lemma* coe_of

modified src/category_theory/category/Pointed.lean
- \+ *lemma* coe_of

modified src/category_theory/category/Twop.lean
- \+ *lemma* coe_of
- \+ *lemma* coe_to_Bipointed

modified src/order/category/BoolAlg.lean
- \+ *lemma* coe_of

modified src/order/category/BoundedLattice.lean
- \+ *lemma* coe_of

modified src/order/category/BoundedOrder.lean
- \+ *lemma* coe_of

modified src/order/category/CompleteLattice.lean
- \+ *lemma* coe_of

modified src/order/category/DistribLattice.lean
- \+ *lemma* coe_of

modified src/order/category/FinPartialOrder.lean
- \+ *lemma* coe_of

modified src/order/category/Frame.lean
- \+ *lemma* coe_of

modified src/order/category/Lattice.lean
- \+ *lemma* coe_of

modified src/order/category/LinearOrder.lean
- \+ *lemma* coe_of

modified src/order/category/NonemptyFinLinOrd.lean
- \+ *lemma* coe_of
- \+ *lemma* NonemptyFinLinOrd_dual_comp_forget_to_LinearOrder
- \- *lemma* NonemptyFinLinOrd_dual_equiv_comp_forget_to_LinearOrder
- \+ *def* dual
- \- *def* to_dual

modified src/order/category/PartialOrder.lean
- \+ *lemma* coe_of
- \+ *lemma* PartialOrder_dual_comp_forget_to_Preorder
- \- *lemma* PartialOrder_to_dual_comp_forget_to_Preorder
- \+ *def* dual
- \- *def* to_dual

modified src/order/category/Preorder.lean
- \+ *lemma* coe_of
- \+ *def* dual
- \- *def* to_dual

modified src/order/category/omega_complete_partial_order.lean
- \+ *lemma* coe_of



## [2022-03-12 02:28:52](https://github.com/leanprover-community/mathlib/commit/4e302f5)
feat(data/nat): add card_multiples ([#12592](https://github.com/leanprover-community/mathlib/pull/12592))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* card_multiples



## [2022-03-12 02:28:51](https://github.com/leanprover-community/mathlib/commit/222faed)
feat(algebra/group/units_hom): make `is_unit.map` work on `monoid_hom_class` ([#12577](https://github.com/leanprover-community/mathlib/pull/12577))
`ring_hom.is_unit_map` and `mv_power_series.is_unit_constant_coeff` are now redundant, but to keep this diff small I've left them around.
#### Estimated changes
modified src/algebra/group/units_hom.lean
- \+/\- *lemma* is_unit.map
- \+/\- *lemma* is_unit.map

modified src/algebra/ring/basic.lean

modified src/algebraic_geometry/Gamma_Spec_adjunction.lean

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/ring_division.lean

modified src/group_theory/monoid_localization.lean

modified src/ring_theory/ideal/local_ring.lean

modified src/ring_theory/localization/away.lean

modified src/ring_theory/localization/localization_localization.lean

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/power_series/basic.lean



## [2022-03-12 02:28:50](https://github.com/leanprover-community/mathlib/commit/8364980)
feat(category_theory): interderivability of kernel and equalizers in preadditive cats ([#12576](https://github.com/leanprover-community/mathlib/pull/12576))
#### Estimated changes
modified src/category_theory/idempotents/basic.lean

modified src/category_theory/preadditive/default.lean
- \+ *lemma* has_equalizer_of_has_kernel
- \+/\- *lemma* has_kernel_of_has_equalizer
- \+ *lemma* has_coequalizer_of_has_cokernel
- \+ *lemma* has_cokernel_of_has_coequalizer
- \+/\- *lemma* has_equalizers_of_has_kernels
- \- *lemma* has_limit_parallel_pair
- \+/\- *lemma* has_kernel_of_has_equalizer
- \+/\- *lemma* has_equalizers_of_has_kernels
- \- *lemma* has_colimit_parallel_pair
- \+ *def* fork_of_kernel_fork
- \+ *def* kernel_fork_of_fork
- \+ *def* is_limit_fork_of_kernel_fork
- \+ *def* is_limit_kernel_fork_of_fork
- \+ *def* cofork_of_cokernel_cofork
- \+ *def* cokernel_cofork_of_cofork
- \+ *def* is_colimit_cofork_of_cokernel_cofork
- \+ *def* is_colimit_cokernel_cofork_of_cofork



## [2022-03-11 23:40:59](https://github.com/leanprover-community/mathlib/commit/c0a51cf)
chore(*): update to 3.41.0c ([#12591](https://github.com/leanprover-community/mathlib/pull/12591))
#### Estimated changes
modified leanpkg.toml

modified src/algebra/monoid_algebra/to_direct_sum.lean
- \+ *def* add_monoid_algebra_add_equiv_direct_sum
- \+ *def* add_monoid_algebra_ring_equiv_direct_sum
- \+ *def* add_monoid_algebra_alg_equiv_direct_sum

modified src/analysis/convex/cone.lean
- \+ *def* set.inner_dual_cone

modified src/analysis/normed_space/continuous_affine_map.lean
- \+ *def* to_const_prod_continuous_linear_map

modified src/analysis/normed_space/linear_isometry.lean
- \+ *def* prod_assoc

modified src/control/lawful_fix.lean

modified src/data/complex/is_R_or_C.lean
- \+ *def* re_lm
- \+ *def* im_lm
- \+ *def* conj_ae

modified src/data/finsupp/to_dfinsupp.lean
- \+ *def* finsupp_add_equiv_dfinsupp
- \+ *def* finsupp_lequiv_dfinsupp

modified src/data/real/ennreal.lean
- \+ *def* of_nnreal_hom

modified src/measure_theory/constructions/pi.lean

modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *def* topological_space.positive_compacts.Icc01
- \+ *def* topological_space.positive_compacts.pi_Icc01

modified src/model_theory/direct_limit.lean
- \+ *def* of
- \+ *def* lift

modified src/ring_theory/polynomial/homogeneous.lean
- \+ *def* homogeneous_submodule

modified src/ring_theory/witt_vector/teichmuller.lean
- \+ *def* teichmuller

modified src/tactic/slim_check.lean

modified src/topology/category/Compactum.lean
- \+ *def* iso_of_topological_space



## [2022-03-11 21:59:23](https://github.com/leanprover-community/mathlib/commit/e7db193)
feat(algebra/module): add `module.nontrivial` ([#12594](https://github.com/leanprover-community/mathlib/pull/12594))
#### Estimated changes
modified src/algebra/module/basic.lean
- \- *theorem* module.subsingleton



## [2022-03-11 19:18:32](https://github.com/leanprover-community/mathlib/commit/5856c0c)
feat(data/finset/noncomm_prod): add noncomm_prod_mul_distrib ([#12524](https://github.com/leanprover-community/mathlib/pull/12524))
The non-commutative version of `finset.sum_union`.
#### Estimated changes
modified src/data/finset/noncomm_prod.lean
- \+ *lemma* noncomm_prod_mul_distrib_aux
- \+ *lemma* noncomm_prod_mul_distrib



## [2022-03-11 19:18:31](https://github.com/leanprover-community/mathlib/commit/dc5f7fb)
feat(set_theory/ordinal_arithmetic): Further theorems on normal functions ([#12484](https://github.com/leanprover-community/mathlib/pull/12484))
We prove various theorems giving more convenient characterizations of normal functions.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal_iff_strict_mono_limit
- \+ *theorem* bsup_eq_blsub_of_lt_succ_limit
- \+ *theorem* is_normal_iff_lt_succ_and_bsup_eq
- \+ *theorem* is_normal_iff_lt_succ_and_blsub_eq



## [2022-03-11 19:18:30](https://github.com/leanprover-community/mathlib/commit/e3ad468)
feat(data/list/prod_monoid): add prod_eq_pow_card ([#12473](https://github.com/leanprover-community/mathlib/pull/12473))
#### Estimated changes
modified src/data/list/prod_monoid.lean
- \+ *lemma* prod_eq_pow_card



## [2022-03-11 17:31:10](https://github.com/leanprover-community/mathlib/commit/7dcba96)
feat(order/monotone): Folds of monotone functions are monotone ([#12581](https://github.com/leanprover-community/mathlib/pull/12581))
#### Estimated changes
modified src/order/monotone.lean
- \+ *theorem* foldl_monotone
- \+ *theorem* foldr_monotone
- \+ *theorem* foldl_strict_mono
- \+ *theorem* foldr_strict_mono



## [2022-03-11 17:31:09](https://github.com/leanprover-community/mathlib/commit/3dcc168)
feat(linear_algebra/projective_space/basic): The projectivization of a vector space. ([#12438](https://github.com/leanprover-community/mathlib/pull/12438))
This provides the initial definitions for the projective space associated to a vector space.
Future work:
- Linear subspaces of projective spaces, connection with subspaces of the vector space, etc.
- The incidence geometry structure of a projective space.
- The fundamental theorem of projective geometry.
I will tag this PR as RFC for now. If you see something missing from this *initial* PR, please let me know!
#### Estimated changes
created src/linear_algebra/projective_space/basic.lean
- \+ *lemma* mk'_eq_mk
- \+ *lemma* rep_nonzero
- \+ *lemma* mk_rep
- \+ *lemma* mk_eq_mk_iff
- \+ *lemma* exists_smul_eq_mk_rep
- \+ *lemma* ind
- \+ *lemma* submodule_mk
- \+ *lemma* submodule_eq
- \+ *lemma* finrank_submodule
- \+ *lemma* submodule_injective
- \+ *lemma* submodule_mk''
- \+ *lemma* mk''_submodule
- \+ *lemma* map_injective
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *def* projectivization_setoid
- \+ *def* projectivization
- \+ *def* mk
- \+ *def* mk'
- \+ *def* equiv_submodule
- \+ *def* mk''
- \+ *def* map



## [2022-03-11 16:25:21](https://github.com/leanprover-community/mathlib/commit/003701f)
feat(model_theory/substructures): Facts about substructures ([#12258](https://github.com/leanprover-community/mathlib/pull/12258))
Shows that `closure L s` can be viewed as the set of realizations of terms over `s`.
Bounds the cardinality of `closure L s` by the cardinality of the type of terms.
Characterizes `closure L[[A]] s`.
#### Estimated changes
modified src/model_theory/substructures.lean
- \+ *lemma* term.realize_mem
- \+/\- *lemma* constants_mem
- \+ *lemma* coe_closure_eq_range_term_realize
- \+ *lemma* mem_closure_iff_exists_term
- \+ *lemma* lift_card_closure_le_card_term
- \+ *lemma* mem_substructure_reduct
- \+ *lemma* coe_substructure_reduct
- \+ *lemma* mem_with_constants
- \+ *lemma* coe_with_constants
- \+ *lemma* reduct_with_constants
- \+ *lemma* subset_closure_with_constants
- \+ *lemma* closure_with_constants_eq
- \+/\- *lemma* constants_mem
- \+ *theorem* lift_card_closure_le
- \+ *def* substructure_reduct
- \+ *def* with_constants



## [2022-03-11 16:25:19](https://github.com/leanprover-community/mathlib/commit/d6f337d)
feat(set_theory/ordinal_arithmetic): The derivative of multiplication ([#12202](https://github.com/leanprover-community/mathlib/pull/12202))
We prove that for `0 < a`, `deriv ((*) a) b = a ^ ω * b`.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* left_le_opow
- \+ *theorem* right_le_opow
- \+ *theorem* opow_one_add
- \+ *theorem* deriv_eq_id_of_nfp_eq_id
- \+ *theorem* nfp_mul_one
- \+ *theorem* nfp_mul_zero
- \+ *theorem* nfp_zero_mul
- \+ *theorem* deriv_mul_zero
- \+ *theorem* nfp_mul_eq_opow_omega
- \+ *theorem* eq_zero_or_opow_omega_le_of_mul_eq_right
- \+ *theorem* mul_eq_right_iff_opow_omega_dvd
- \+ *theorem* mul_le_right_iff_opow_omega_dvd
- \+ *theorem* nfp_mul_opow_omega_add
- \+ *theorem* deriv_mul_eq_opow_omega_mul
- \- *theorem* le_opow_self



## [2022-03-11 13:44:08](https://github.com/leanprover-community/mathlib/commit/e6fef39)
feat(algebra/order/monoid): add `with_zero.canonically_linear_ordered_add_monoid` ([#12568](https://github.com/leanprover-community/mathlib/pull/12568))
This also removes some non-terminal `simp`s in nearby proofs
#### Estimated changes
modified src/algebra/order/monoid.lean



## [2022-03-11 13:44:07](https://github.com/leanprover-community/mathlib/commit/12786d0)
feat(order/sup_indep): add `finset.sup_indep_pair` ([#12549](https://github.com/leanprover-community/mathlib/pull/12549))
This is used to provide simp lemmas about `sup_indep` on `bool` and `fin 2`.
#### Estimated changes
modified src/order/sup_indep.lean
- \+ *lemma* sup_indep_pair
- \+ *lemma* sup_indep_univ_bool
- \+ *lemma* sup_indep_univ_fin_two
- \+ *lemma* complete_lattice.independent_iff_sup_indep_univ



## [2022-03-11 13:44:06](https://github.com/leanprover-community/mathlib/commit/4dc4dc8)
chore(topology/algebra/module/basic): cleanup variables and coercions ([#12542](https://github.com/leanprover-community/mathlib/pull/12542))
Having the "simple" variables in the lemmas statements rather than globally makes it easier to move lemmas around in future.
This also mean lemmas like `coe_comp` can have their arguments in a better order, as it's easier to customize the argument order at the declaration.
This also replaces a lot of `(_ : M₁ → M₂)`s with `⇑_` for brevity in lemma statements.
No lemmas statements (other than argument reorders) or proofs have changed.
#### Estimated changes
modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* map_smulₛₗ
- \+/\- *lemma* coe_coe
- \+/\- *lemma* zero_apply
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id'
- \+/\- *lemma* one_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* ker_coe
- \+/\- *lemma* is_closed_ker
- \+/\- *lemma* apply_ker
- \+/\- *lemma* range_coe
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+/\- *lemma* image_smul_setₛₗ
- \+/\- *lemma* image_smul_set
- \+/\- *lemma* preimage_smul_setₛₗ
- \+/\- *lemma* preimage_smul_set
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* smul_comp
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* comp_smul
- \+/\- *lemma* comp_smulₛₗ
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_refl'
- \+/\- *lemma* map_smulₛₗ
- \+/\- *lemma* coe_coe
- \+/\- *lemma* zero_apply
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id'
- \+/\- *lemma* one_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* ker_coe
- \+/\- *lemma* is_closed_ker
- \+/\- *lemma* apply_ker
- \+/\- *lemma* range_coe
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+/\- *lemma* image_smul_setₛₗ
- \+/\- *lemma* image_smul_set
- \+/\- *lemma* preimage_smul_setₛₗ
- \+/\- *lemma* preimage_smul_set
- \+/\- *lemma* sub_apply'
- \+/\- *lemma* range_prod_eq
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* smul_comp
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* comp_smul
- \+/\- *lemma* comp_smulₛₗ
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_refl'
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* zero_comp
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+/\- *theorem* zero_comp



## [2022-03-11 10:13:17](https://github.com/leanprover-community/mathlib/commit/02e0ab2)
refactor(group_theory/commutator): Golf some proofs ([#12586](https://github.com/leanprover-community/mathlib/pull/12586))
This PR golfs the proofs of some lemmas in `commutator.lean`.
I also renamed `bot_commutator` and `commutator_bot` to `commutator_bot_left` and `commutator_bot_right`, since "bot_commutator" didn't sound right to me (you would say "the commutator of H and K", not "H commutator K"), but I can revert to the old name if you want.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+/\- *lemma* commutator_le_right
- \+/\- *lemma* commutator_le_left
- \+ *lemma* commutator_bot_left
- \+ *lemma* commutator_bot_right
- \+/\- *lemma* commutator_le_inf
- \+/\- *lemma* commutator_le_right
- \+/\- *lemma* commutator_le_left
- \- *lemma* commutator_bot
- \- *lemma* bot_commutator
- \+/\- *lemma* commutator_le_inf

modified src/group_theory/solvable.lean



## [2022-03-11 10:13:16](https://github.com/leanprover-community/mathlib/commit/d9a774e)
feat(order/hom): `prod.swap` as an `order_iso` ([#12585](https://github.com/leanprover-community/mathlib/pull/12585))
#### Estimated changes
modified src/order/basic.lean
- \+ *lemma* swap_le_swap
- \+ *lemma* swap_lt_swap

modified src/order/hom/basic.lean
- \+ *lemma* coe_prod_comm
- \+ *lemma* prod_comm_symm
- \+ *def* prod_comm



## [2022-03-11 08:22:26](https://github.com/leanprover-community/mathlib/commit/840a042)
feat(data/list/basic): Miscellaneous `fold` lemmas ([#12579](https://github.com/leanprover-community/mathlib/pull/12579))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* foldl_fixed
- \+ *theorem* foldr_fixed
- \+ *theorem* foldl_combinator_K

modified src/logic/function/iterate.lean
- \+ *theorem* foldl_const
- \+ *theorem* foldr_const



## [2022-03-11 08:22:25](https://github.com/leanprover-community/mathlib/commit/1a581ed)
refactor(group_theory/solvable): Golf proof ([#12552](https://github.com/leanprover-community/mathlib/pull/12552))
This PR golfs the proof of insolvability of S_5, using the new commutator notation.
#### Estimated changes
modified src/group_theory/solvable.lean



## [2022-03-11 08:22:24](https://github.com/leanprover-community/mathlib/commit/1326aa7)
feat(analysis/special_functions): limit of x^s * exp(-x) for s real ([#12540](https://github.com/leanprover-community/mathlib/pull/12540))
#### Estimated changes
modified src/analysis/special_functions/pow.lean
- \+ *lemma* tendsto_exp_div_rpow_at_top
- \+ *lemma* tendsto_exp_mul_div_rpow_at_top
- \+ *lemma* tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0



## [2022-03-11 08:22:23](https://github.com/leanprover-community/mathlib/commit/e553f8a)
refactor(algebra/group/to_additive): monadic code cosmetics ([#12527](https://github.com/leanprover-community/mathlib/pull/12527))
as suggested by @kmill and @eric-wieser, but the merge was faster
Also improve test file.
#### Estimated changes
modified src/algebra/group/to_additive.lean

modified test/lint_to_additive_doc.lean
- \+ *lemma* no_to_additive



## [2022-03-11 08:22:22](https://github.com/leanprover-community/mathlib/commit/47b1ddf)
feat(data/setoid/partition): Relate `setoid.is_partition` and `finpartition` ([#12459](https://github.com/leanprover-community/mathlib/pull/12459))
Add two functions that relate `setoid.is_partition` and `finpartition`:
* `setoid.is_partition.partition` 
* `finpartition.is_partition_parts`
Meanwhile add some lemmas related to `finset.sup` and `finset.inf` in data/finset/lattice.
#### Estimated changes
modified src/data/finset/lattice.lean
- \+ *lemma* sup_id_set_eq_sUnion
- \+ *lemma* sup_set_eq_bUnion
- \+ *lemma* inf_id_set_eq_sInter
- \+ *lemma* inf_set_eq_bInter

modified src/data/setoid/partition.lean
- \+ *theorem* finpartition.is_partition_parts
- \+ *def* is_partition.finpartition

modified src/order/well_founded_set.lean



## [2022-03-11 06:44:16](https://github.com/leanprover-community/mathlib/commit/115f8c7)
fix(probability): remove unused argument from `cond_cond_eq_cond_inter` ([#12583](https://github.com/leanprover-community/mathlib/pull/12583))
This was a property that we already derived within the proof itself from conditionable intersection (I think I forgot to remove this when I made the PR).
#### Estimated changes
modified src/probability/conditional.lean



## [2022-03-11 06:44:15](https://github.com/leanprover-community/mathlib/commit/3061d18)
feat(data/nat/{nth,prime}): add facts about primes ([#12560](https://github.com/leanprover-community/mathlib/pull/12560))
Gives `{p | prime p}.infinite` as well as `infinite_of_not_bdd_above` lemma. Also gives simp lemmas for `prime_counting'`.
#### Estimated changes
modified src/data/nat/nth.lean
- \+ *lemma* nth_injective_of_infinite

modified src/data/nat/prime.lean
- \+ *lemma* not_bdd_above_set_of_prime
- \+ *lemma* infinite_set_of_prime

modified src/data/set/finite.lean
- \+ *lemma* infinite_of_not_bdd_above
- \+ *lemma* infinite_of_not_bdd_below

modified src/number_theory/prime_counting.lean
- \+ *lemma* prime_counting'_nth_eq
- \+ *lemma* prime_nth_prime



## [2022-03-11 06:44:14](https://github.com/leanprover-community/mathlib/commit/de4d14c)
feat(group_theory/commutator): Add some basic lemmas ([#12554](https://github.com/leanprover-community/mathlib/pull/12554))
This PR adds lemmas adds some basic lemmas about when the commutator is trivial.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+ *lemma* commutator_element_eq_one_iff_mul_comm
- \+ *lemma* commutator_element_eq_one_iff_commute
- \+ *lemma* commute.commutator_eq
- \+ *lemma* commutator_element_one_right
- \+ *lemma* commutator_element_one_left



## [2022-03-11 06:12:11](https://github.com/leanprover-community/mathlib/commit/355472d)
refactor(group_theory/commutator): Golf proof of `commutator_mem_commutator` ([#12584](https://github.com/leanprover-community/mathlib/pull/12584))
This PR golfs the proof of `commutator_mem_commutator`, and moves it earlier in the file so that it can be used earlier.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+/\- *lemma* commutator_mem_commutator
- \+/\- *lemma* commutator_mem_commutator



## [2022-03-11 02:38:57](https://github.com/leanprover-community/mathlib/commit/b5a26d0)
feat(data/list/basic): Lists over empty type are `unique` ([#12582](https://github.com/leanprover-community/mathlib/pull/12582))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *def* unique_of_is_empty



## [2022-03-10 23:44:36](https://github.com/leanprover-community/mathlib/commit/f0dd6e9)
refactor(group_theory/commutator): Use commutators in `commutator_le` ([#12572](https://github.com/leanprover-community/mathlib/pull/12572))
This PR golfs the proof of `commutator_le`, and uses the new commutator notation.
#### Estimated changes
modified src/group_theory/commutator.lean



## [2022-03-10 23:12:24](https://github.com/leanprover-community/mathlib/commit/6c04fcf)
refactor(group_theory/commutator): Use commutator notation in `commutator_normal` ([#12575](https://github.com/leanprover-community/mathlib/pull/12575))
This PR uses the new commutator notation in the proof of `commutator_normal`.
#### Estimated changes
modified src/group_theory/commutator.lean



## [2022-03-10 21:17:59](https://github.com/leanprover-community/mathlib/commit/84cbbc9)
feat(algebra/group/to_additive + a few more files): make `to_additive` convert `unit` to `add_unit` ([#12564](https://github.com/leanprover-community/mathlib/pull/12564))
This likely involves removing names that match autogenerated names.
#### Estimated changes
modified src/algebra/group/to_additive.lean

modified src/algebra/group/units.lean
- \+/\- *theorem* is_unit_of_mul_eq_one
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* is_unit_of_mul_eq_one
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_iff_exists_inv'

modified src/data/equiv/mul_add.lean
- \+/\- *lemma* coe_to_units
- \+/\- *lemma* coe_to_units

modified src/group_theory/congruence.lean
- \+/\- *def* lift_on_units
- \+/\- *def* lift_on_units

modified src/group_theory/order_of_element.lean



## [2022-03-10 19:33:06](https://github.com/leanprover-community/mathlib/commit/869ef84)
feat(data/zmod/basic): some lemmas about coercions ([#12571](https://github.com/leanprover-community/mathlib/pull/12571))
The names here are in line with `zmod.nat_coe_zmod_eq_zero_iff_dvd` and `zmod.int_coe_zmod_eq_zero_iff_dvd` a few lines above.
#### Estimated changes
modified src/data/zmod/basic.lean
- \+ *lemma* val_int_cast
- \+ *lemma* nat_coe_zmod_eq_iff
- \+ *lemma* int_coe_zmod_eq_iff



## [2022-03-10 19:33:05](https://github.com/leanprover-community/mathlib/commit/6fdb1d5)
chore(*): clear up some excessive by statements ([#12570](https://github.com/leanprover-community/mathlib/pull/12570))
Delete some `by` (and similar commands that do nothing, such as
- `by by blah`
- `by begin blah end`
- `{ by blah }`
- `begin { blah } end`
Also clean up the proof of `monic.map` and `nat_degree_div_by_monic` a bit.
#### Estimated changes
modified archive/100-theorems-list/82_cubing_a_cube.lean

modified src/algebra/lie/nilpotent.lean

modified src/category_theory/adjunction/whiskering.lean

modified src/data/polynomial/div.lean

modified src/data/polynomial/monic.lean

modified src/field_theory/separable.lean

modified src/group_theory/exponent.lean
- \+/\- *lemma* exponent_eq_zero_iff
- \+/\- *lemma* exponent_eq_zero_iff

modified src/linear_algebra/affine_space/affine_subspace.lean

modified src/linear_algebra/affine_space/independent.lean

modified src/measure_theory/function/simple_func_dense.lean

modified src/number_theory/padics/padic_norm.lean

modified src/order/filter/ennreal.lean

modified src/order/jordan_holder.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean



## [2022-03-10 19:33:04](https://github.com/leanprover-community/mathlib/commit/45c22c0)
feat(field_theory/is_alg_closed/basic): add `is_alg_closed.infinite` ([#12566](https://github.com/leanprover-community/mathlib/pull/12566))
An algebraically closed field is infinite, because if it is finite then `x^(n+1) - 1` is a separable polynomial (where `n` is the cardinality of the field).
#### Estimated changes
modified src/field_theory/is_alg_closed/basic.lean



## [2022-03-10 19:33:02](https://github.com/leanprover-community/mathlib/commit/0e93816)
feat(tactic/norm_num_command): add user command to run norm_num on an expression ([#12550](https://github.com/leanprover-community/mathlib/pull/12550))
For example,
```
#norm_num 2^100 % 10
-- 6
```
#### Estimated changes
modified src/tactic/norm_num.lean



## [2022-03-10 17:46:10](https://github.com/leanprover-community/mathlib/commit/f654a86)
chore(*): remove lines claiming to introduce variables ([#12569](https://github.com/leanprover-community/mathlib/pull/12569))
They don't.
#### Estimated changes
modified src/analysis/complex/real_deriv.lean

modified src/data/equiv/option.lean

modified src/group_theory/order_of_element.lean

modified src/order/antisymmetrization.lean



## [2022-03-10 15:58:20](https://github.com/leanprover-community/mathlib/commit/4a59a4d)
chore(order/galois_connection): Make lifting instances reducible ([#12559](https://github.com/leanprover-community/mathlib/pull/12559))
and provide `infi₂` and `supr₂` versions of the lemmas.
#### Estimated changes
modified src/order/galois_connection.lean
- \+/\- *lemma* l_supr
- \+ *lemma* l_supr₂
- \+/\- *lemma* u_infi
- \+ *lemma* u_infi₂
- \+/\- *lemma* l_Sup
- \+/\- *lemma* u_Inf
- \+/\- *lemma* l_supr
- \+/\- *lemma* u_infi
- \+/\- *lemma* l_Sup
- \+/\- *lemma* u_Inf



## [2022-03-10 15:28:09](https://github.com/leanprover-community/mathlib/commit/788ccf0)
chore(cardinal_divisibility): tiny golf ([#12567](https://github.com/leanprover-community/mathlib/pull/12567))
#### Estimated changes
modified src/set_theory/cardinal_divisibility.lean



## [2022-03-10 13:16:05](https://github.com/leanprover-community/mathlib/commit/cd111e9)
feat(data/equiv/mul_add): add to_additive attribute to `group.is_unit` ([#12563](https://github.com/leanprover-community/mathlib/pull/12563))
Unless something breaks, this PR does nothing else!
#### Estimated changes
modified src/data/equiv/mul_add.lean



## [2022-03-10 10:38:55](https://github.com/leanprover-community/mathlib/commit/41f5c17)
chore(set_theory/ordinal_arithmetic): Make auxiliary result private ([#12562](https://github.com/leanprover-community/mathlib/pull/12562))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* CNF_pairwise_aux



## [2022-03-10 10:08:31](https://github.com/leanprover-community/mathlib/commit/4048a9b)
chore(measure_theory/function/convergence_in_measure): golf proof with Borel-Cantelli ([#12551](https://github.com/leanprover-community/mathlib/pull/12551))
#### Estimated changes
modified src/measure_theory/function/convergence_in_measure.lean



## [2022-03-10 09:02:58](https://github.com/leanprover-community/mathlib/commit/d56a9bc)
feat(set_theory/ordinal_arithmetic): `add_eq_zero_iff`, `mul_eq_zero_iff` ([#12561](https://github.com/leanprover-community/mathlib/pull/12561))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* add_eq_zero_iff
- \+ *theorem* left_eq_zero_of_add_eq_zero
- \+ *theorem* right_eq_zero_of_add_eq_zero
- \+ *theorem* mul_eq_zero_iff



## [2022-03-10 09:02:56](https://github.com/leanprover-community/mathlib/commit/1e560a6)
refactor(group_theory/commutator): Generalize `map_commutator_element` ([#12555](https://github.com/leanprover-community/mathlib/pull/12555))
This PR generalizes `map_commutator_element` from `monoid_hom_class F G G` to `monoid_hom_class F G G'`.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+/\- *lemma* map_commutator_element
- \+/\- *lemma* map_commutator_element



## [2022-03-10 07:37:11](https://github.com/leanprover-community/mathlib/commit/24e3b5f)
refactor(topology/opens): Turn `opens.gi` into a Galois coinsertion ([#12547](https://github.com/leanprover-community/mathlib/pull/12547))
`topological_space.opens.gi` is currently a `galois_insertion` between `order_dual (opens α)` and `order_dual (set α)`. This turns it into the sensible thing, namely a `galois_coinsertion` between `opens α` and `set α`.
#### Estimated changes
modified src/topology/opens.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* le_def
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \- *lemma* gi_choice_val
- \+/\- *lemma* le_def
- \+/\- *def* gi
- \+/\- *def* gi



## [2022-03-10 07:37:10](https://github.com/leanprover-community/mathlib/commit/0fd9929)
feat(group_theory/double_cosets): definition of double cosets and some basic lemmas. ([#9490](https://github.com/leanprover-community/mathlib/pull/9490))
This contains the definition of double cosets and some basic lemmas about them, such as "the whole group is the disjoint union of its double cosets" and relationship to usual group quotients.
#### Estimated changes
created src/group_theory/double_coset.lean
- \+ *lemma* mem_doset
- \+ *lemma* mem_doset_self
- \+ *lemma* doset_eq_of_mem
- \+ *lemma* mem_doset_of_not_disjoint
- \+ *lemma* eq_of_not_disjoint
- \+ *lemma* rel_iff
- \+ *lemma* bot_rel_eq_left_rel
- \+ *lemma* rel_bot_eq_right_group_rel
- \+ *lemma* eq
- \+ *lemma* out_eq'
- \+ *lemma* mk_out'_eq_mul
- \+ *lemma* mk_eq_of_doset_eq
- \+ *lemma* disjoint_out'
- \+ *lemma* union_quot_to_doset
- \+ *lemma* doset_union_right_coset
- \+ *lemma* doset_union_left_coset
- \+ *lemma* left_bot_eq_left_quot
- \+ *lemma* right_bot_eq_right_quot
- \+ *def* _root_.doset
- \+ *def* setoid
- \+ *def* quotient
- \+ *def* quot_to_doset

modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* subgroup_mul_singleton
- \+ *lemma* singleton_mul_subgroup



## [2022-03-10 06:34:47](https://github.com/leanprover-community/mathlib/commit/750ca95)
chore(linear_algebra/affine_space/affine_map): golf using the injective APIs ([#12543](https://github.com/leanprover-community/mathlib/pull/12543))
The extra whitespace means this isn't actually any shorter by number of lines, but it does eliminate 12 trivial proofs.
Again, the `has_scalar` instance has been hoisted from lower down the file, so that we have the `nat` and `int` actions available when we create the `add_comm_group` structure. Previously we just built the same `has_scalar` structure three times.
#### Estimated changes
modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_linear
- \+/\- *lemma* zero_linear
- \+/\- *lemma* zero_linear
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_linear



## [2022-03-10 06:34:46](https://github.com/leanprover-community/mathlib/commit/8836a42)
fix(linear_algebra/quadratic_form/basic): align diamonds in the nat- and int- action ([#12541](https://github.com/leanprover-community/mathlib/pull/12541))
This also provides `fun_like` and `zero_hom_class` instances.
The `has_scalar` code has been moved unchanged from further down in the file.
This change makes `coe_fn_sub` eligible for `dsimp`, since it can now be proved by `rfl`.
#### Estimated changes
modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+/\- *lemma* ext
- \+/\- *lemma* congr_fun
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_fn_sub
- \+/\- *lemma* sub_apply
- \- *lemma* to_fun_eq_apply
- \+/\- *lemma* ext
- \+/\- *lemma* congr_fun
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_fn_sub
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* smul_apply



## [2022-03-10 06:34:44](https://github.com/leanprover-community/mathlib/commit/9e28852)
feat(field_theory/krull_topology): added krull_topology_totally_disconnected ([#12398](https://github.com/leanprover-community/mathlib/pull/12398))
#### Estimated changes
modified src/field_theory/krull_topology.lean
- \+ *lemma* intermediate_field.fixing_subgroup_is_closed
- \+/\- *lemma* krull_topology_t2
- \+ *lemma* krull_topology_totally_disconnected
- \- *lemma* subgroup.is_open_of_one_mem_interior
- \+/\- *lemma* krull_topology_t2

modified src/topology/algebra/open_subgroup.lean
- \+ *lemma* is_open_of_one_mem_interior
- \+/\- *lemma* is_open_mono
- \+/\- *lemma* is_open_mono

modified src/topology/connected.lean
- \+ *lemma* is_totally_disconnected_of_clopen_set



## [2022-03-10 05:29:37](https://github.com/leanprover-community/mathlib/commit/bab039f)
feat(topology/opens): The frame of opens of a topological space ([#12546](https://github.com/leanprover-community/mathlib/pull/12546))
Provide the `frame` instance for `opens α` and strengthen `opens.comap` from `order_hom` to `frame_hom`.
#### Estimated changes
modified src/topology/algebra/order/basic.lean

modified src/topology/opens.lean
- \+/\- *lemma* coe_inf
- \+ *lemma* coe_Sup
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_mono
- \+/\- *lemma* coe_inf
- \- *lemma* Sup_s
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_mono
- \+/\- *def* comap
- \+/\- *def* comap



## [2022-03-10 05:29:36](https://github.com/leanprover-community/mathlib/commit/9c2f6eb)
feat(category_theory/abelian/exact): `exact g.op f.op` ([#12456](https://github.com/leanprover-community/mathlib/pull/12456))
This pr is about `exact g.op f.op` from `exact f g` in an abelian category; this pr is taken from liquid tensor experiment. I believe the original author is @adamtopaz.
#### Estimated changes
modified src/category_theory/abelian/exact.lean
- \+ *lemma* is_equivalence.exact_iff
- \+ *lemma* exact.op_iff
- \+ *lemma* exact.unop_iff

modified src/category_theory/abelian/opposite.lean
- \+ *lemma* cokernel.π_op
- \+ *lemma* kernel.ι_op
- \+ *lemma* kernel.ι_unop
- \+ *lemma* cokernel.π_unop

modified src/category_theory/preadditive/default.lean
- \+ *lemma* comp_left_eq_zero
- \+ *lemma* comp_right_eq_zero



## [2022-03-10 04:56:21](https://github.com/leanprover-community/mathlib/commit/ef25c4c)
refactor(group_theory/commutator): Rename `commutator_containment` to `commutator_mem_commutator` ([#12553](https://github.com/leanprover-community/mathlib/pull/12553))
This PR renames `commutator_containment` to `commutator_mem_commutator`, uses the new commutator notation, and makes the subgroups implicit.
#### Estimated changes
modified src/group_theory/commutator.lean
- \+ *lemma* commutator_mem_commutator
- \- *lemma* commutator_containment

modified src/group_theory/nilpotent.lean

modified src/group_theory/solvable.lean



## [2022-03-09 13:59:57](https://github.com/leanprover-community/mathlib/commit/9facd19)
doc(combinatorics/simple_graph/basic): fix typo ([#12544](https://github.com/leanprover-community/mathlib/pull/12544))
#### Estimated changes
modified src/combinatorics/simple_graph/basic.lean



## [2022-03-09 11:28:18](https://github.com/leanprover-community/mathlib/commit/0d6fb8a)
chore(analysis/complex/upper_half_plane): use `coe` instead of `coe_fn` ([#12532](https://github.com/leanprover-community/mathlib/pull/12532))
This matches the approach used by other files working with `special_linear_group`.
#### Estimated changes
modified src/analysis/complex/upper_half_plane.lean
- \+/\- *def* num
- \+/\- *def* denom
- \+/\- *def* num
- \+/\- *def* denom



## [2022-03-09 11:28:17](https://github.com/leanprover-community/mathlib/commit/c4a3413)
chore(data/polynomial): use dot notation for monic lemmas ([#12530](https://github.com/leanprover-community/mathlib/pull/12530))
As discussed in [#12447](https://github.com/leanprover-community/mathlib/pull/12447)
- Use the notation throughout the library
- Also deleted `ne_zero_of_monic` as it was a duplicate of `monic.ne_zero` it seems.
- Cleaned up a small proof here and there too.
#### Estimated changes
modified src/data/polynomial/div.lean

modified src/data/polynomial/lifts.lean
- \+/\- *lemma* lifts_and_degree_eq_and_monic
- \+/\- *lemma* lifts_and_degree_eq_and_monic

modified src/data/polynomial/monic.lean
- \+ *lemma* monic.map
- \+/\- *lemma* monic_C_mul_of_mul_leading_coeff_eq_one
- \+/\- *lemma* monic_mul_C_of_leading_coeff_mul_eq_one
- \+ *lemma* monic.mul
- \+ *lemma* monic.pow
- \+ *lemma* monic.add_of_left
- \+ *lemma* monic.add_of_right
- \+ *lemma* monic.nat_degree_map
- \+ *lemma* monic.degree_map
- \- *lemma* monic_map
- \+/\- *lemma* monic_C_mul_of_mul_leading_coeff_eq_one
- \+/\- *lemma* monic_mul_C_of_leading_coeff_mul_eq_one
- \- *lemma* monic_mul
- \- *lemma* monic_pow
- \- *lemma* monic_add_of_left
- \- *lemma* monic_add_of_right
- \- *lemma* nat_degree_map_of_monic
- \- *lemma* degree_map_of_monic
- \- *lemma* ne_zero_of_monic

modified src/data/polynomial/ring_division.lean

modified src/field_theory/minpoly.lean

modified src/field_theory/splitting_field.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/norm.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/cyclotomic/basic.lean

modified src/ring_theory/polynomial/eisenstein.lean

modified src/ring_theory/power_basis.lean

modified src/ring_theory/trace.lean



## [2022-03-09 09:05:27](https://github.com/leanprover-community/mathlib/commit/55d1f3e)
chore(set_theory/cardinal): `min` → `Inf` ([#12517](https://github.com/leanprover-community/mathlib/pull/12517))
Various definitions are awkwardly stated in terms of minima of subtypes. We instead rewrite them as infima and golf them. Further, we protect `cardinal.min` to avoid confusion with `linear_order.min`.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+/\- *theorem* min_eq
- \+/\- *theorem* min_le
- \+/\- *theorem* le_min
- \+ *theorem* succ_nonempty
- \+ *theorem* nonempty_sup
- \+/\- *theorem* le_sup
- \+/\- *theorem* lift_min
- \+/\- *theorem* min_eq
- \+/\- *theorem* min_le
- \+/\- *theorem* le_min
- \+/\- *theorem* le_sup
- \+/\- *theorem* lift_min
- \+/\- *def* sup
- \- *def* min
- \+/\- *def* sup



## [2022-03-09 05:46:45](https://github.com/leanprover-community/mathlib/commit/5d405e2)
chore(linear_algebra/alternating): golf using injective APIs ([#12536](https://github.com/leanprover-community/mathlib/pull/12536))
To do this, we have to move the has_scalar instance higher up in the file.
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_fn_smul



## [2022-03-09 05:46:44](https://github.com/leanprover-community/mathlib/commit/bc9dda8)
chore(algebra/module/linear_map): golf using injective APIs ([#12535](https://github.com/leanprover-community/mathlib/pull/12535))
To do this, we have to move the `has_scalar` instance higher up in the file.
#### Estimated changes
modified src/algebra/module/linear_map.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul



## [2022-03-09 05:46:43](https://github.com/leanprover-community/mathlib/commit/94e9bb5)
chore(data/{finsupp,dfinsupp}/basic): use the injective APIs ([#12534](https://github.com/leanprover-community/mathlib/pull/12534))
This also fixes a scalar diamond in the `nat` and `int` actions on `dfinsupp`.
The diamond did not exist for `finsupp`.
#### Estimated changes
modified src/data/dfinsupp/basic.lean
- \+ *lemma* nsmul_apply
- \+ *lemma* coe_nsmul
- \+ *lemma* zsmul_apply
- \+ *lemma* coe_zsmul

modified src/data/finsupp/basic.lean
- \+/\- *lemma* coe_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* sub_apply
- \+/\- *lemma* coe_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_sub
- \+/\- *lemma* sub_apply

modified src/data/finsupp/pointwise.lean



## [2022-03-09 05:46:41](https://github.com/leanprover-community/mathlib/commit/b8d176e)
chore(real/cau_seq_completion): put class in Prop ([#12533](https://github.com/leanprover-community/mathlib/pull/12533))
#### Estimated changes
modified src/data/complex/basic.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq_completion.lean



## [2022-03-09 04:04:18](https://github.com/leanprover-community/mathlib/commit/1f6a2e9)
chore(scripts): update nolints.txt ([#12538](https://github.com/leanprover-community/mathlib/pull/12538))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/style-exceptions.txt



## [2022-03-09 00:50:46](https://github.com/leanprover-community/mathlib/commit/2a3ecad)
feat(data/equiv/basic): lemmas about composition with equivalences ([#10693](https://github.com/leanprover-community/mathlib/pull/10693))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* eq_comp_symm
- \+ *lemma* comp_symm_eq
- \+ *lemma* eq_symm_comp
- \+ *lemma* symm_comp_eq

modified src/data/equiv/module.lean
- \+ *lemma* eq_comp_symm
- \+ *lemma* comp_symm_eq
- \+ *lemma* eq_symm_comp
- \+ *lemma* symm_comp_eq
- \+ *lemma* eq_comp_to_linear_map_symm
- \+ *lemma* comp_to_linear_map_symm_eq
- \+ *lemma* eq_to_linear_map_symm_comp
- \+ *lemma* to_linear_map_symm_comp_eq

modified src/data/equiv/mul_add.lean
- \+ *lemma* eq_comp_symm
- \+ *lemma* comp_symm_eq
- \+ *lemma* eq_symm_comp
- \+ *lemma* symm_comp_eq



## [2022-03-08 21:42:52](https://github.com/leanprover-community/mathlib/commit/d69cda1)
chore(order/well_founded_set): golf two proofs ([#12529](https://github.com/leanprover-community/mathlib/pull/12529))
#### Estimated changes
modified src/order/well_founded_set.lean



## [2022-03-08 21:42:51](https://github.com/leanprover-community/mathlib/commit/709a3b7)
feat(set_theory/cardinal_ordinal): `#(list α) ≤ max ω (#α)` ([#12519](https://github.com/leanprover-community/mathlib/pull/12519))
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* mk_list_eq_omega
- \+ *theorem* mk_list_le_max



## [2022-03-08 17:53:50](https://github.com/leanprover-community/mathlib/commit/feb24fb)
feat(topology/vector_bundle): direct sum of topological vector bundles ([#12512](https://github.com/leanprover-community/mathlib/pull/12512))
#### Estimated changes
modified src/data/bundle.lean

modified src/topology/maps.lean

modified src/topology/vector_bundle.lean
- \+ *lemma* apply_eq_prod_continuous_linear_equiv_at
- \+ *lemma* symm_apply_eq_mk_continuous_linear_equiv_at_symm
- \+ *lemma* continuous_proj
- \+ *lemma* prod.inducing_diag
- \+ *lemma* prod.inv_fun'_apply
- \+ *lemma* base_set_prod
- \+ *lemma* prod_apply
- \+ *lemma* prod_symm_apply
- \+ *lemma* trivialization.continuous_linear_equiv_at_prod
- \+ *def* prod.to_fun'
- \+ *def* prod.inv_fun'
- \+ *def* prod



## [2022-03-08 17:53:49](https://github.com/leanprover-community/mathlib/commit/1d67b07)
feat(category_theory): cases in which (co)equalizers are split monos (epis) ([#12498](https://github.com/leanprover-community/mathlib/pull/12498))
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.is_limit.lift_of_ι_ι
- \+ *lemma* cofork.is_colimit.π_desc_of_π
- \+ *def* split_mono_of_equalizer
- \+ *def* split_mono_of_idempotent_of_is_limit_fork
- \+ *def* split_mono_of_idempotent_equalizer
- \+ *def* split_epi_of_coequalizer
- \+ *def* split_epi_of_idempotent_of_is_colimit_cofork
- \+ *def* split_epi_of_idempotent_coequalizer



## [2022-03-08 17:53:47](https://github.com/leanprover-community/mathlib/commit/b4572d1)
feat(algebra/order/hom/ring): Ordered ring isomorphisms ([#12158](https://github.com/leanprover-community/mathlib/pull/12158))
Define `order_ring_iso`, the type of ordered ring isomorphisms, along with its typeclass `order_ring_iso_class`.
#### Estimated changes
modified src/algebra/order/hom/ring.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* to_ring_equiv_eq_coe
- \+ *lemma* to_order_iso_eq_coe
- \+ *lemma* coe_to_ring_equiv
- \+ *lemma* coe_to_order_iso
- \+ *lemma* refl_apply
- \+ *lemma* coe_ring_equiv_refl
- \+ *lemma* coe_order_iso_refl
- \+ *lemma* symm_symm
- \+ *lemma* trans_apply
- \+ *lemma* self_trans_symm
- \+ *lemma* symm_trans_self
- \+ *lemma* to_order_ring_hom_eq_coe
- \+ *lemma* coe_to_order_ring_hom
- \+ *lemma* coe_to_order_ring_hom_refl
- \+ *def* to_order_iso
- \+ *def* simps.symm_apply
- \+ *def* to_order_ring_hom

modified src/order/hom/basic.lean
- \+ *lemma* map_inv_le_iff
- \+ *lemma* le_map_inv_iff
- \+ *lemma* map_lt_map_iff
- \+ *lemma* map_inv_lt_iff
- \+ *lemma* lt_map_inv_iff



## [2022-03-08 15:58:18](https://github.com/leanprover-community/mathlib/commit/4ad5c5a)
feat(data/finset/noncomm_prod): add noncomm_prod_commute ([#12521](https://github.com/leanprover-community/mathlib/pull/12521))
adding `list.prod_commute`, `multiset.noncomm_prod_commute` and
`finset.noncomm_prod_commute`.
#### Estimated changes
modified src/data/finset/noncomm_prod.lean
- \+ *lemma* noncomm_prod_commute
- \+ *lemma* noncomm_prod_commute

modified src/data/list/prod_monoid.lean
- \+ *lemma* prod_commute



## [2022-03-08 15:58:16](https://github.com/leanprover-community/mathlib/commit/fac5ffe)
feat(group_theory/subgroup/basic): disjoint_iff_mul_eq_one ([#12505](https://github.com/leanprover-community/mathlib/pull/12505))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* disjoint_def
- \+ *lemma* disjoint_def'
- \+ *lemma* disjoint_iff_mul_eq_one

modified src/group_theory/submonoid/basic.lean
- \+ *lemma* disjoint_def
- \+ *lemma* disjoint_def'



## [2022-03-08 15:58:15](https://github.com/leanprover-community/mathlib/commit/1597e9a)
feat(set_theory/ordinal_arithmetic): prove `enum_ord_le_of_subset` ([#12199](https://github.com/leanprover-community/mathlib/pull/12199))
I also used this as an excuse to remove a trivial theorem and some awkward dot notation.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* enum_ord_le_of_subset
- \+ *theorem* enum_ord_surjective
- \- *theorem* enum_ord_zero_le
- \- *theorem* enum_ord.surjective
- \+ *def* enum_ord_order_iso
- \- *def* enum_ord.order_iso



## [2022-03-08 14:29:38](https://github.com/leanprover-community/mathlib/commit/ab6a892)
feat(data/finset/noncomm_prod): add noncomm_prod_congr ([#12520](https://github.com/leanprover-community/mathlib/pull/12520))
#### Estimated changes
modified src/data/finset/noncomm_prod.lean
- \+ *lemma* noncomm_prod_congr



## [2022-03-08 14:29:36](https://github.com/leanprover-community/mathlib/commit/c0ba4d6)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_comp_X_add_one_is_eisenstein_at ([#12447](https://github.com/leanprover-community/mathlib/pull/12447))
We add `cyclotomic_comp_X_add_one_is_eisenstein_at`: `(cyclotomic p ℤ).comp (X + 1)` is Eisenstein at `p`.
From flt-regular
#### Estimated changes
modified src/data/polynomial/coeff.lean
- \+ *lemma* mul_X_pow_injective
- \+ *lemma* mul_X_injective

modified src/field_theory/minpoly.lean
- \+ *lemma* add_algebra_map
- \+ *lemma* sub_algebra_map
- \- *lemma* minpoly_add_algebra_map
- \- *lemma* minpoly_sub_algebra_map

modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* minpoly_sub_one_eq_cyclotomic_comp

modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* geom_sum_X_comp_X_add_one_eq_sum
- \+ *lemma* monic.geom_sum
- \+ *lemma* monic.geom_sum'
- \+ *lemma* monic_geom_sum_X

modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* cyclotomic_comp_X_add_one_is_eisenstein_at



## [2022-03-08 12:44:00](https://github.com/leanprover-community/mathlib/commit/94cbfad)
chore(algebra/*): move some lemmas about is_unit from associated.lean ([#12526](https://github.com/leanprover-community/mathlib/pull/12526))
There doesn't seem to be any reason for them to live there.
#### Estimated changes
modified src/algebra/associated.lean
- \- *lemma* is_unit_of_dvd_one
- \- *lemma* not_is_unit_of_not_is_unit_dvd
- \- *lemma* dvd_and_not_dvd_iff
- \- *lemma* pow_dvd_pow_iff
- \- *theorem* is_unit_iff_dvd_one
- \- *theorem* is_unit_iff_forall_dvd
- \- *theorem* is_unit_of_dvd_unit

modified src/algebra/divisibility.lean
- \+ *lemma* is_unit_of_dvd_one
- \+ *lemma* not_is_unit_of_not_is_unit_dvd
- \+ *lemma* dvd_and_not_dvd_iff
- \+ *theorem* is_unit_iff_dvd_one
- \+ *theorem* is_unit_iff_forall_dvd
- \+ *theorem* is_unit_of_dvd_unit

modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_dvd_pow_iff



## [2022-03-08 12:43:59](https://github.com/leanprover-community/mathlib/commit/9c13d62)
feat(data/int/gcd): add gcd_pos_iff ([#12522](https://github.com/leanprover-community/mathlib/pull/12522))
#### Estimated changes
modified src/data/int/gcd.lean
- \+ *theorem* gcd_pos_iff



## [2022-03-08 12:43:58](https://github.com/leanprover-community/mathlib/commit/6dd3249)
feat(set_theory/ordinal_arithmetic): `brange_const` ([#12483](https://github.com/leanprover-community/mathlib/pull/12483))
This is the `brange` analog to `set.range_const`.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* brange_const



## [2022-03-08 10:54:20](https://github.com/leanprover-community/mathlib/commit/0798037)
refactor(algebra/group/inj_surj): add npow and zpow to all definitions ([#12126](https://github.com/leanprover-community/mathlib/pull/12126))
Currently, we have a small handful of helpers to construct algebraic structures via pushforwards and pullbacks that preserve `has_pow` and `has_scalar` instances (added in [#10152](https://github.com/leanprover-community/mathlib/pull/10152) and [#10832](https://github.com/leanprover-community/mathlib/pull/10832)):
* `function.{inj,surj}ective.add_monoid_smul`
* `function.{inj,surj}ective.monoid_pow`
* `function.{inj,surj}ective.sub_neg_monoid_smul`
* `function.{inj,surj}ective.div_inv_monoid_smul`
* `function.{inj,surj}ective.add_group_smul`
* `function.{inj,surj}ective.group_pow`
Predating these, we have a very large collection of helpers that construct new `has_pow` and `has_scalar` instances, for all the above and also for every other one-argument algebraic structure (`comm_monoid`, `ring`, `linear_ordered_field`, ...).
This puts the user in an awkward position; either:
1. They are unaware of the complexity here, and use `add_monoid_smul` and `add_comm_monoid` within the same file, which create two nonequal scalar instances.
2. They use only the large collection, and don't get definitional control of `has_scalar` and `has_pow`, which can cause typeclass diamonds with generic `has_scalar` instances.
3. They use only the small handful of helpers (which requires remembering which ones are safe to use), and have to remember to manually construct `add_comm_monoid` as `{..add_comm_semigroup, ..add_monoid}`. If they screw up and construct it as `{..add_comm_semigroup, ..add_zero_class}`, then they're in the same position as (1) without knowing it.
This change converts every helper in the large collection to _also_ preserve scalar and power instances; as a result, these pullback and pushforward helpers once again no longer construct any new data.
As a result, all these helpers now take `nsmul`, `zsmul`, `npow`, and `zpow` arguments as necessary, to indicate that these operations are preserved by the function in question.
As a result of this change, all existing callers are now expected to have a `has_pow` or `has_scalar` implementation available ahead of time. In many cases the `has_scalar` instances already exist as a more general case, and maybe just need reordering within the file. Sometimes the general case of `has_scalar` is stated in a way that isn't general enough to describe `int` and `nat`. In these cases and the `has_pow` cases, we define new instance manually. Grepping reveals a rough summary of the new instances:
```lean
instance : has_pow (A 0) ℕ
instance has_nsmul : has_scalar ℕ (C ⟶ D)
instance has_zsmul : has_scalar ℤ (C ⟶ D)
instance has_nsmul : has_scalar ℕ (M →ₗ⁅R,L⁆ N)
instance has_zsmul : has_scalar ℤ (M →ₗ⁅R,L⁆ N)
instance has_nsmul : has_scalar ℕ {x : α // 0 ≤ x}
instance has_pow : α // 0 ≤ x} ℕ
instance : has_scalar R (ι →ᵇᵃ[I₀] M)
instance has_nat_scalar : has_scalar ℕ (normed_group_hom V₁ V₂)
instance has_int_scalar : has_scalar ℤ (normed_group_hom V₁ V₂)
instance : has_pow ℕ+ ℕ
instance subfield.has_zpow : has_pow s ℤ
instance has_nat_scalar : has_scalar ℕ (left_invariant_derivation I G)
instance has_int_scalar : has_scalar ℤ (left_invariant_derivation I G)
instance add_subgroup.has_nsmul : has_scalar ℕ H
instance subgroup.has_npow : has_pow H ℕ
instance add_subgroup.has_zsmul : has_scalar ℤ H
instance subgroup.has_zpow : has_pow H ℤ
instance add_submonoid.has_nsmul : has_scalar ℕ S
instance submonoid.has_pow : has_pow S ℕ
instance : has_pow (special_linear_group n R) ℕ
instance : has_pow (α →ₘ[μ] γ) ℕ
instance has_int_pow : has_pow (α →ₘ[μ] γ) ℤ
instance : div_inv_monoid (α →ₘ[μ] γ)
instance has_nat_pow : has_pow (α →ₛ β) ℕ
instance has_int_pow : has_pow (α →ₛ β) ℤ
instance has_nat_pow : has_pow (germ l G) ℕ
instance has_int_pow : has_pow (germ l G) ℤ
instance : has_scalar ℕ (fractional_ideal S P)
instance has_nat_scalar : has_scalar ℕ (𝕎 R)
instance has_int_scalar : has_scalar ℤ (𝕎 R)
instance has_nat_pow : has_pow (𝕎 R) ℕ
instance has_nat_scalar : has_scalar ℕ (truncated_witt_vector p n R)
instance has_int_scalar : has_scalar ℤ (truncated_witt_vector p n R)
instance has_nat_pow : has_pow (truncated_witt_vector p n R) ℕ
instance has_nat_scalar : has_scalar ℕ (α →ᵇ β)
instance has_int_scalar : has_scalar ℤ (α →ᵇ β)
instance has_nat_pow : has_pow (α →ᵇ R) ℕ
```
#### Estimated changes
modified src/algebra/direct_sum/ring.lean
- \+ *lemma* of_zero_pow

modified src/algebra/field/basic.lean

modified src/algebra/graded_monoid.lean
- \+ *lemma* mk_zero_pow

modified src/algebra/group/inj_surj.lean

modified src/algebra/group/opposite.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group_with_zero/basic.lean

modified src/algebra/homology/additive.lean
- \+ *lemma* nsmul_f_apply
- \+ *lemma* zsmul_f_apply

modified src/algebra/lie/basic.lean
- \+ *lemma* coe_nsmul
- \+ *lemma* nsmul_apply
- \+ *lemma* coe_zsmul
- \+ *lemma* zsmul_apply

modified src/algebra/lie/free.lean

modified src/algebra/module/submodule.lean

modified src/algebra/order/field.lean

modified src/algebra/order/group.lean

modified src/algebra/order/monoid.lean

modified src/algebra/order/nonneg.lean
- \+ *lemma* nsmul_mk
- \+ *lemma* mk_pow

modified src/algebra/order/ring.lean

modified src/algebra/order/with_zero.lean

modified src/algebra/pointwise.lean
- \+ *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+ *lemma* coe_pow
- \+/\- *lemma* coe_mul

modified src/algebra/ring/basic.lean

modified src/algebra/star/self_adjoint.lean

modified src/algebra/symmetrized.lean

modified src/analysis/box_integral/partition/additive.lean

modified src/analysis/normed/group/hom.lean
- \+ *lemma* coe_nsmul
- \+ *lemma* nsmul_apply
- \+ *lemma* coe_zsmul
- \+ *lemma* zsmul_apply

modified src/analysis/seminorm.lean

modified src/data/equiv/transfer_instance.lean
- \+ *lemma* pow_def

modified src/data/pnat/basic.lean

modified src/data/pnat/prime.lean

modified src/data/real/nnreal.lean

modified src/field_theory/subfield.lean
- \+ *lemma* zpow_mem

modified src/geometry/manifold/algebra/left_invariant_derivation.lean

modified src/group_theory/congruence.lean

modified src/group_theory/specific_groups/cyclic.lean

modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_zpow

modified src/group_theory/submonoid/membership.lean
- \- *lemma* pow_mem
- \- *theorem* coe_pow

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* pow_mem
- \+ *theorem* coe_pow

modified src/linear_algebra/multilinear/basic.lean

modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* coe_pow

modified src/measure_theory/function/ae_eq_fun.lean
- \+ *lemma* mk_pow
- \+ *lemma* coe_fn_pow
- \+ *lemma* pow_to_germ
- \+ *lemma* mk_zpow
- \+ *lemma* coe_fn_zpow
- \+ *lemma* zpow_to_germ

modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+ *lemma* coe_pow
- \+ *lemma* pow_apply
- \+ *lemma* coe_zpow
- \+ *lemma* zpow_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply

modified src/measure_theory/measure/finite_measure_weak_convergence.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* add_apply
- \+/\- *lemma* add_apply

modified src/number_theory/cyclotomic/gal.lean

modified src/order/filter/germ.lean
- \+ *lemma* coe_pow
- \+ *lemma* coe_zpow
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul

modified src/ring_theory/dedekind_domain/ideal.lean

modified src/ring_theory/derivation.lean
- \+/\- *def* coe_fn_add_monoid_hom
- \+/\- *def* coe_fn_add_monoid_hom

modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* _root_.is_fractional.nsmul
- \+ *lemma* coe_nsmul

modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_pow

modified src/ring_theory/subsemiring/basic.lean

modified src/ring_theory/witt_vector/basic.lean
- \+ *lemma* nsmul
- \+ *lemma* zsmul
- \+ *lemma* pow

modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* constant_coeff_witt_nsmul
- \+ *lemma* constant_coeff_witt_zsmul
- \+ *lemma* nsmul_coeff
- \+ *lemma* zsmul_coeff
- \+ *lemma* pow_coeff
- \+ *lemma* witt_nsmul_vars
- \+ *lemma* witt_zsmul_vars
- \+ *lemma* witt_pow_vars
- \+ *def* witt_nsmul
- \+ *def* witt_zsmul
- \+ *def* witt_pow

modified src/ring_theory/witt_vector/identities.lean

modified src/ring_theory/witt_vector/init_tail.lean
- \+ *lemma* init_nsmul
- \+ *lemma* init_zsmul
- \+ *lemma* init_pow

modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* truncate_fun_nsmul
- \+ *lemma* truncate_fun_zsmul
- \+ *lemma* truncate_fun_pow

modified src/topology/algebra/continuous_affine_map.lean

modified src/topology/algebra/module/multilinear.lean

modified src/topology/continuous_function/algebra.lean

modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_nsmul_rec
- \+ *lemma* coe_nsmul
- \+ *lemma* nsmul_apply
- \+ *lemma* coe_zsmul_rec
- \+ *lemma* coe_zsmul
- \+ *lemma* zsmul_apply
- \+ *lemma* coe_npow_rec
- \+ *lemma* coe_pow
- \+ *lemma* pow_apply



## [2022-03-08 08:31:06](https://github.com/leanprover-community/mathlib/commit/b4a7ad6)
chore(field_theory/laurent): drop unused 'have'. ([#12516](https://github.com/leanprover-community/mathlib/pull/12516))
#### Estimated changes
modified src/field_theory/laurent.lean



## [2022-03-08 08:31:05](https://github.com/leanprover-community/mathlib/commit/dc093e9)
chore(combinatorics/configuration): don't use classical.some in a proof ([#12515](https://github.com/leanprover-community/mathlib/pull/12515))
#### Estimated changes
modified src/combinatorics/configuration.lean



## [2022-03-08 08:31:04](https://github.com/leanprover-community/mathlib/commit/ffa6e6d)
feat(set_theory/cardinal): `sum_le_sup_lift` ([#12513](https://github.com/leanprover-community/mathlib/pull/12513))
This is a universe-polymorphic version of `sum_le_sup`.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *theorem* sum_le_sup_lift



## [2022-03-08 08:31:03](https://github.com/leanprover-community/mathlib/commit/43cb3ff)
fix(ring_theory/ideal/operations): fix a name and dot notation ([#12507](https://github.com/leanprover-community/mathlib/pull/12507))
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *theorem* is_prime.is_primary
- \- *theorem* is_primary.to_is_prime



## [2022-03-08 08:31:02](https://github.com/leanprover-community/mathlib/commit/b2377ea)
feat(measure_theory/measure/finite_measure_weak_convergence): generalize scalar action ([#12503](https://github.com/leanprover-community/mathlib/pull/12503))
This means the smul lemmas also work for `nsmul`.
#### Estimated changes
modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* test_against_nn_smul
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* test_against_nn_smul



## [2022-03-08 08:31:00](https://github.com/leanprover-community/mathlib/commit/65095fe)
doc(order/succ_pred/basic): fix typo ([#12501](https://github.com/leanprover-community/mathlib/pull/12501))
#### Estimated changes
modified src/order/succ_pred/basic.lean



## [2022-03-08 08:30:59](https://github.com/leanprover-community/mathlib/commit/47182da)
feat(algebra/group/to_additive): add to_additive doc string linter ([#12487](https://github.com/leanprover-community/mathlib/pull/12487))
it is an easy mistake to add a docstring to a lemma with `to_additive`
without also passing a string to `to_additive`. This linter checks for
that, and suggests to add a doc string when needed.
#### Estimated changes
modified scripts/nolints.txt

modified src/algebra/group/to_additive.lean

modified src/tactic/lint/default.lean

created test/lint_to_additive_doc.lean
- \+ *lemma* foo
- \+ *lemma* bar
- \+ *lemma* baz
- \+ *lemma* quux



## [2022-03-08 08:30:58](https://github.com/leanprover-community/mathlib/commit/ccdcce1)
chore(set_theory/game/nim): General golfing ([#12471](https://github.com/leanprover-community/mathlib/pull/12471))
We make use of various relatively new theorems on ordinals to simplify various proofs, or otherwise clean up the file.
#### Estimated changes
modified src/set_theory/game/nim.lean
- \+/\- *lemma* exists_move_left_eq
- \+/\- *lemma* non_zero_first_wins
- \+/\- *lemma* nonmoves_nonempty
- \- *lemma* nim_wf_lemma
- \+/\- *lemma* exists_move_left_eq
- \+/\- *lemma* non_zero_first_wins
- \+/\- *lemma* nonmoves_nonempty

modified src/set_theory/ordinal.lean



## [2022-03-08 08:30:57](https://github.com/leanprover-community/mathlib/commit/b3fba03)
feat(algebra/homology/homotopy) : `mk_coinductive` ([#12457](https://github.com/leanprover-community/mathlib/pull/12457))
`mk_coinductive` is the dual version of `mk_inductive` in the same file. `mk_inductive` is to build homotopy of chain complexes inductively and `mk_coinductive` is to build homotopy of cochain complexes inductively.
#### Estimated changes
modified src/algebra/homology/homotopy.lean
- \+ *lemma* d_next_cochain_complex
- \+ *lemma* prev_d_succ_cochain_complex
- \+ *lemma* prev_d_zero_cochain_complex
- \+ *lemma* mk_coinductive_aux₃
- \+ *def* mk_coinductive_aux₁
- \+ *def* mk_coinductive_aux₂
- \+ *def* mk_coinductive



## [2022-03-08 07:26:43](https://github.com/leanprover-community/mathlib/commit/14997d0)
feat(analysis/normed_space): allow non-unital C^* rings ([#12327](https://github.com/leanprover-community/mathlib/pull/12327))
#### Estimated changes
modified src/analysis/normed_space/star/basic.lean

modified src/topology/continuous_function/bounded.lean



## [2022-03-08 06:08:39](https://github.com/leanprover-community/mathlib/commit/74746bd)
chore(counterexamples/canonically_ordered_comm_semiring_two_mul): golf ([#12504](https://github.com/leanprover-community/mathlib/pull/12504))
#### Estimated changes
modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *def* L_subsemiring



## [2022-03-07 22:59:51](https://github.com/leanprover-community/mathlib/commit/5f6d30e)
chore(*): move `has_scalar` instances before `add_comm_monoid` instances ([#12502](https://github.com/leanprover-community/mathlib/pull/12502))
This makes it easier for us to set `nsmul` and `zsmul` in future.
#### Estimated changes
modified src/linear_algebra/multilinear/basic.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul

modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *def* smul
- \+/\- *def* smul

modified src/topology/algebra/module/multilinear.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* to_multilinear_map_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* to_multilinear_map_smul



## [2022-03-07 21:31:06](https://github.com/leanprover-community/mathlib/commit/e409a90)
feat(measure_theory/integral/periodic.lean): add lemma `function.periodic.tendsto_at_bot_interval_integral_of_pos'` ([#12500](https://github.com/leanprover-community/mathlib/pull/12500))
Partner of `function.periodic.tendsto_at_top_interval_integral_of_pos'` (I probably should have included this in [#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/algebra/order/floor.lean

modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral_pos_of_pos

modified src/measure_theory/integral/periodic.lean
- \+ *lemma* integral_le_Sup_add_zsmul_of_pos
- \+ *lemma* tendsto_at_bot_interval_integral_of_pos
- \+ *lemma* tendsto_at_bot_interval_integral_of_pos'



## [2022-03-07 21:31:04](https://github.com/leanprover-community/mathlib/commit/390554d)
feat(ring_theory/coprime/basic): lemmas about multiplying by units ([#12480](https://github.com/leanprover-community/mathlib/pull/12480))
#### Estimated changes
modified src/ring_theory/coprime/basic.lean
- \+ *lemma* is_coprime_group_smul_left
- \+ *lemma* is_coprime_group_smul_right
- \+ *lemma* is_coprime_group_smul
- \+ *lemma* is_coprime_mul_unit_left_left
- \+ *lemma* is_coprime_mul_unit_left_right
- \+ *lemma* is_coprime_mul_unit_left
- \+ *lemma* is_coprime_mul_unit_right_left
- \+ *lemma* is_coprime_mul_unit_right_right
- \+ *lemma* is_coprime_mul_unit_right



## [2022-03-07 21:31:03](https://github.com/leanprover-community/mathlib/commit/9728bd2)
chore(number_theory/number_field): golf `int.not_is_field` ([#12451](https://github.com/leanprover-community/mathlib/pull/12451))
Golfed proof of number_theory.number_field.int.not_is_field
Co-authored by: David Ang <dka31@cantab.ac.uk>
Co-authored by: Eric Rodriguez <ericrboidi@gmail.com>
Co-authored by: Violeta Hernández <vi.hdz.p@gmail.com>
#### Estimated changes
modified src/number_theory/number_field.lean
- \+/\- *lemma* int.not_is_field
- \+/\- *lemma* int.not_is_field



## [2022-03-07 19:47:38](https://github.com/leanprover-community/mathlib/commit/1b4ee53)
feat(algebra/associated): add pow_not_prime ([#12493](https://github.com/leanprover-community/mathlib/pull/12493))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* pow_not_prime
- \+ *theorem* of_irreducible_pow



## [2022-03-07 19:47:36](https://github.com/leanprover-community/mathlib/commit/f28023e)
feat(measure_theory/function/uniform_integrable): Uniform integrability and Vitali convergence theorem ([#12408](https://github.com/leanprover-community/mathlib/pull/12408))
This PR defines uniform integrability (both in the measure theory sense as well as the probability theory sense) and proves the Vitali convergence theorem which establishes a relation between convergence in measure and uniform integrability with convergence in Lp.
#### Estimated changes
modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_one_div_le_iff

modified src/measure_theory/function/lp_space.lean
- \+ *lemma* mem_ℒp.norm_rpow

created src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* uniform_integrable.measurable
- \+ *lemma* uniform_integrable.unif_integrable
- \+ *lemma* uniform_integrable.mem_ℒp
- \+ *lemma* unif_integrable_congr_ae
- \+ *lemma* tendsto_indicator_ge
- \+ *lemma* mem_ℒp.integral_indicator_norm_ge_le
- \+ *lemma* mem_ℒp.integral_indicator_norm_ge_nonneg_le_of_meas
- \+ *lemma* mem_ℒp.integral_indicator_norm_ge_nonneg_le
- \+ *lemma* mem_ℒp.snorm_ess_sup_indicator_norm_ge_eq_zero
- \+ *lemma* mem_ℒp.snorm_indicator_norm_ge_le
- \+ *lemma* mem_ℒp.snorm_indicator_norm_ge_pos_le
- \+ *lemma* snorm_indicator_le_of_bound
- \+ *lemma* mem_ℒp.snorm_indicator_le'
- \+ *lemma* mem_ℒp.snorm_indicator_le_of_meas
- \+ *lemma* mem_ℒp.snorm_indicator_le
- \+ *lemma* unif_integrable_const
- \+ *lemma* unif_integrable_subsingleton
- \+ *lemma* unif_integrable_fin
- \+ *lemma* unif_integrable_fintype
- \+ *lemma* snorm_sub_le_of_dist_bdd
- \+ *lemma* tendsto_Lp_of_tendsto_ae_of_meas
- \+ *lemma* tendsto_Lp_of_tendsto_ae
- \+ *lemma* unif_integrable_of_tendsto_Lp_zero
- \+ *lemma* unif_integrable_of_tendsto_Lp
- \+ *lemma* tendsto_Lp_of_tendsto_in_measure
- \+ *lemma* tendsto_in_measure_iff_tendsto_Lp
- \+ *def* unif_integrable
- \+ *def* uniform_integrable

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* _root_.filter.eventually_eq.restrict

modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_iff_forall_eventually_mem
- \+ *lemma* not_tendsto_iff_exists_frequently_nmem
- \+ *lemma* frequently_iff_seq_frequently
- \+ *lemma* subseq_forall_of_frequently
- \+ *lemma* exists_seq_forall_of_frequently
- \+ *lemma* tendsto_of_subseq_tendsto



## [2022-03-07 19:47:34](https://github.com/leanprover-community/mathlib/commit/1ee91a5)
feat(probability_theory/stopping): define progressively measurable processes ([#11350](https://github.com/leanprover-community/mathlib/pull/11350))
* Define progressively measurable processes (`prog_measurable`), which is the correct strengthening of `adapted` to get that the stopped process is also progressively measurable.
* Prove that an adapted continuous process is progressively measurable.
For discrete time processes, progressively measurable is equivalent to `adapted` .
This PR also changes some measurable_space arguments in `measurable_space.lean` from typeclass arguments to implicit.
#### Estimated changes
modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measurable_uncurry_of_continuous_of_measurable

modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable.iterate
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_set.subtype_image
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable.prod_mk
- \+/\- *lemma* measurable.prod_map
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_from_prod_encodable
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_sum
- \+/\- *lemma* measurable.sum_elim
- \+/\- *lemma* measurable.iterate
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_set.subtype_image
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable.prod_mk
- \+/\- *lemma* measurable.prod_map
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_from_prod_encodable
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_sum
- \+/\- *lemma* measurable.sum_elim
- \+ *def* measurable_space.prod

modified src/probability/stopping.lean
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* smul
- \+ *lemma* prog_measurable_const
- \+ *lemma* prog_measurable_of_tendsto'
- \+ *lemma* prog_measurable_of_tendsto
- \+ *lemma* prog_measurable_min_stopping_time
- \+ *lemma* prog_measurable.stopped_process
- \+ *lemma* prog_measurable.adapted_stopped_process
- \+ *lemma* prog_measurable.measurable_stopped_process
- \+ *lemma* adapted.prog_measurable_of_nat
- \+ *lemma* adapted.stopped_process_of_nat
- \+ *lemma* adapted.measurable_stopped_process_of_nat
- \+/\- *lemma* mem_ℒp_stopped_process
- \+/\- *lemma* integrable_stopped_process
- \+/\- *lemma* mem_ℒp_stopped_value
- \+/\- *lemma* integrable_stopped_value
- \+/\- *lemma* add
- \+/\- *lemma* neg
- \+/\- *lemma* smul
- \- *lemma* max
- \- *lemma* min
- \- *lemma* adapted.stopped_process
- \- *lemma* measurable_stopped_process
- \+/\- *lemma* mem_ℒp_stopped_process
- \+/\- *lemma* integrable_stopped_process
- \+/\- *lemma* mem_ℒp_stopped_value
- \+/\- *lemma* integrable_stopped_value
- \+ *theorem* adapted.prog_measurable_of_continuous
- \+ *def* prog_measurable



## [2022-03-07 18:31:04](https://github.com/leanprover-community/mathlib/commit/e871be2)
feat(data/real/nnreal): floor_semiring instance ([#12495](https://github.com/leanprover-community/mathlib/pull/12495))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60nat.2Eceil.60.20on.20.60nnreal.60.20.3F/near/274353230)
#### Estimated changes
modified src/algebra/order/floor.lean

modified src/algebra/order/nonneg.lean
- \+ *lemma* nat_floor_coe
- \+ *lemma* nat_ceil_coe

modified src/data/real/nnreal.lean



## [2022-03-07 18:31:03](https://github.com/leanprover-community/mathlib/commit/8d2ffb8)
feat(category_theory): (co)kernels of biproduct projection and inclusion ([#12394](https://github.com/leanprover-community/mathlib/pull/12394))
add kernels and cokernels of biproduct projections and inclusions
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* biproduct.map_eq_map'
- \+/\- *lemma* biproduct.map_π
- \+/\- *lemma* biproduct.ι_map
- \+/\- *lemma* biproduct.map_desc
- \+/\- *lemma* biproduct.lift_map
- \+ *lemma* biproduct.from_subtype_π
- \+ *lemma* biproduct.from_subtype_eq_lift
- \+ *lemma* biproduct.from_subtype_π_subtype
- \+ *lemma* biproduct.to_subtype_π
- \+ *lemma* biproduct.ι_to_subtype
- \+ *lemma* biproduct.to_subtype_eq_desc
- \+ *lemma* biproduct.ι_to_subtype_subtype
- \+ *lemma* biproduct.ι_from_subtype
- \+ *lemma* biproduct.from_subtype_to_subtype
- \+ *lemma* biproduct.to_subtype_from_subtype
- \+ *lemma* biprod.fst_kernel_fork_ι
- \+ *lemma* biprod.snd_kernel_fork_ι
- \+ *lemma* biprod.inl_cokernel_fork_π
- \+ *lemma* biprod.inr_cokernel_fork_π
- \+/\- *lemma* biproduct.map_eq_map'
- \+/\- *lemma* biproduct.map_π
- \+/\- *lemma* biproduct.ι_map
- \+/\- *lemma* biproduct.map_desc
- \+/\- *lemma* biproduct.lift_map
- \+/\- *def* biproduct.map_iso
- \+ *def* biproduct.from_subtype
- \+ *def* biproduct.to_subtype
- \+ *def* biproduct.is_limit_from_subtype
- \+ *def* biproduct.is_colimit_to_subtype
- \+ *def* biprod.fst_kernel_fork
- \+ *def* biprod.is_kernel_fst_kernel_fork
- \+ *def* biprod.snd_kernel_fork
- \+ *def* biprod.is_kernel_snd_kernel_fork
- \+ *def* biprod.inl_cokernel_fork
- \+ *def* biprod.is_cokernel_inl_cokernel_fork
- \+ *def* biprod.inr_cokernel_fork
- \+ *def* biprod.is_cokernel_inr_cokernel_fork
- \+/\- *def* biproduct.map_iso



## [2022-03-07 18:01:16](https://github.com/leanprover-community/mathlib/commit/85a415e)
docs(overview): Add overview of model theory ([#12496](https://github.com/leanprover-community/mathlib/pull/12496))
Adds a subsection on model theory to the mathlib overview.
#### Estimated changes
modified docs/overview.yaml



## [2022-03-07 16:01:41](https://github.com/leanprover-community/mathlib/commit/3c3c3bc)
fix(tactic/interactive): use non-interactive admit tactic ([#12489](https://github.com/leanprover-community/mathlib/pull/12489))
In a future release of Lean 3, the interactive admit tactic will take an additional argument.
#### Estimated changes
modified src/tactic/interactive.lean



## [2022-03-07 16:01:39](https://github.com/leanprover-community/mathlib/commit/5f2a6ac)
feat(measure_theory/integral/periodic): further properties of periodic integrals ([#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/algebra/order/floor.lean
- \+ *lemma* fract_div_mul_self_mem_Ico
- \+ *lemma* fract_div_mul_self_add_zsmul_eq

modified src/measure_theory/integral/periodic.lean
- \+/\- *lemma* is_add_fundamental_domain_Ioc
- \+/\- *lemma* interval_integral_add_eq_of_pos
- \+/\- *lemma* interval_integral_add_eq
- \+ *lemma* interval_integral_add_eq_add
- \+ *lemma* interval_integral_add_zsmul_eq
- \+ *lemma* Inf_add_zsmul_le_integral_of_pos
- \+ *lemma* tendsto_at_top_interval_integral_of_pos
- \+ *lemma* tendsto_at_top_interval_integral_of_pos'
- \+/\- *lemma* is_add_fundamental_domain_Ioc
- \+/\- *lemma* interval_integral_add_eq_of_pos
- \+/\- *lemma* interval_integral_add_eq

modified src/topology/algebra/order/compact.lean
- \+ *lemma* image_Icc
- \+ *lemma* image_interval_eq_Icc
- \+ *lemma* image_interval
- \+ *lemma* Inf_image_Icc_le
- \+ *lemma* le_Sup_image_Icc
- \- *lemma* continuous_on.image_Icc
- \- *lemma* continuous_on.image_interval_eq_Icc
- \- *lemma* continuous_on.image_interval



## [2022-03-07 16:01:38](https://github.com/leanprover-community/mathlib/commit/c95ce52)
fix(number_theory/modular): prefer `coe` over `coe_fn` in lemma statements ([#12445](https://github.com/leanprover-community/mathlib/pull/12445))
This file is already full of `↑ₘ`s (aka coercions to matrix), we may as well use them uniformly.
#### Estimated changes
modified src/number_theory/modular.lean



## [2022-03-07 14:11:59](https://github.com/leanprover-community/mathlib/commit/f451e09)
chore(algebra/order/{group,monoid}): trivial lemma about arithmetic on `with_top` and `with_bot` ([#12491](https://github.com/leanprover-community/mathlib/pull/12491))
#### Estimated changes
modified src/algebra/order/group.lean
- \+ *lemma* with_top.coe_neg

modified src/algebra/order/monoid.lean
- \+ *lemma* coe_eq_one
- \- *lemma* coe_zero
- \- *lemma* coe_eq_zero



## [2022-03-07 14:11:57](https://github.com/leanprover-community/mathlib/commit/65ac316)
chore(algebra/order/nonneg): add `nonneg.coe_nat_cast` ([#12490](https://github.com/leanprover-community/mathlib/pull/12490))
#### Estimated changes
modified src/algebra/order/nonneg.lean



## [2022-03-07 14:11:56](https://github.com/leanprover-community/mathlib/commit/16b6766)
feat(analysis/normed_space): non-unital normed rings ([#12326](https://github.com/leanprover-community/mathlib/pull/12326))
On the way to allowing non-unital C^*-algebras.
#### Estimated changes
modified src/analysis/calculus/extend_deriv.lean

modified src/analysis/normed/normed_field.lean
- \+/\- *lemma* mul_left_bound
- \+/\- *lemma* mul_right_bound
- \+/\- *lemma* norm_matrix_le_iff
- \+/\- *lemma* norm_matrix_lt_iff
- \+/\- *lemma* mul_left_bound
- \+/\- *lemma* mul_right_bound
- \+/\- *lemma* norm_matrix_le_iff
- \+/\- *lemma* norm_matrix_lt_iff
- \+/\- *def* matrix.semi_normed_group
- \+/\- *def* matrix.normed_group
- \+/\- *def* matrix.semi_normed_group
- \+/\- *def* matrix.normed_group



## [2022-03-07 14:11:55](https://github.com/leanprover-community/mathlib/commit/9ed4366)
feat(category_theory/limits): limit preservation properties of functor.left_op and similar ([#12168](https://github.com/leanprover-community/mathlib/pull/12168))
#### Estimated changes
created src/category_theory/limits/preserves/opposites.lean
- \+ *def* preserves_limit_op
- \+ *def* preserves_limit_left_op
- \+ *def* preserves_limit_right_op
- \+ *def* preserves_limit_unop
- \+ *def* preserves_colimit_op
- \+ *def* preserves_colimit_left_op
- \+ *def* preserves_colimit_right_op
- \+ *def* preserves_colimit_unop
- \+ *def* preserves_limits_of_shape_op
- \+ *def* preserves_limits_of_shape_left_op
- \+ *def* preserves_limits_of_shape_right_op
- \+ *def* preserves_limits_of_shape_unop
- \+ *def* preserves_colimits_of_shape_op
- \+ *def* preserves_colimits_of_shape_left_op
- \+ *def* preserves_colimits_of_shape_right_op
- \+ *def* preserves_colimits_of_shape_unop
- \+ *def* preserves_limits_op
- \+ *def* preserves_limits_left_op
- \+ *def* preserves_limits_right_op
- \+ *def* preserves_limits_unop
- \+ *def* perserves_colimits_op
- \+ *def* preserves_colimits_left_op
- \+ *def* preserves_colimits_right_op
- \+ *def* preserves_colimits_unop
- \+ *def* preserves_finite_limits_op
- \+ *def* preserves_finite_limits_left_op
- \+ *def* preserves_finite_limits_right_op
- \+ *def* preserves_finite_limits_unop
- \+ *def* preserves_finite_colimits_op
- \+ *def* preserves_finite_colimits_left_op
- \+ *def* preserves_finite_colimits_right_op
- \+ *def* preserves_finite_colimits_unop



## [2022-03-07 12:17:08](https://github.com/leanprover-community/mathlib/commit/900ce6f)
chore(data/equiv/basic): rename `involutive.to_equiv` to `to_perm` ([#12486](https://github.com/leanprover-community/mathlib/pull/12486))
#### Estimated changes
modified src/algebra/quandle.lean

modified src/algebra/star/basic.lean

modified src/data/equiv/basic.lean
- \+ *lemma* coe_to_perm
- \+ *lemma* to_perm_symm
- \+ *lemma* to_perm_involutive
- \+ *def* equiv.perm
- \+ *def* to_perm
- \- *def* function.involutive.to_equiv
- \- *def* perm

modified src/data/equiv/module.lean

modified src/data/equiv/mul_add.lean



## [2022-03-07 10:15:48](https://github.com/leanprover-community/mathlib/commit/eb46e7e)
feat(algebra/group/to_additive): let to_additive turn `pow` into `nsmul` ([#12477](https://github.com/leanprover-community/mathlib/pull/12477))
The naming convention for `npow` in lemma names is `pow`, so let’s teach
`to_additive` about it.
A fair number of lemmas now no longer need an explicit additive name.
#### Estimated changes
modified src/algebra/big_operators/basic.lean

modified src/algebra/big_operators/multiset.lean

modified src/algebra/group/hom.lean
- \+/\- *theorem* map_pow
- \+/\- *theorem* map_pow

modified src/algebra/group/pi.lean

modified src/algebra/group/to_additive.lean

modified src/algebra/group_power/basic.lean
- \+/\- *theorem* inv_pow
- \+/\- *theorem* inv_pow

modified src/algebra/group_power/order.lean

modified src/algebra/iterate_hom.lean

modified src/algebra/pointwise.lean

modified src/group_theory/exponent.lean

modified src/group_theory/order_of_element.lean
- \+/\- *lemma* pow_eq_mod_card
- \+/\- *lemma* pow_eq_mod_card

modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* pow_mem
- \+/\- *lemma* pow_mem
- \+/\- *theorem* coe_pow
- \+/\- *theorem* coe_pow

modified src/number_theory/divisors.lean

modified src/topology/algebra/monoid.lean

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* pow_comp
- \+/\- *lemma* pow_comp



## [2022-03-07 10:15:47](https://github.com/leanprover-community/mathlib/commit/d704f27)
refactor(set_theory/*): `o.out.r` → `<` ([#12468](https://github.com/leanprover-community/mathlib/pull/12468))
We declare a `linear_order` instance on `o.out.α`, for `o : ordinal`, with `<` def-eq to `o.out.r`. This will improve code clarity and will allow us to state theorems about specific ordinals as ordered structures.
#### Estimated changes
modified src/measure_theory/card_measurable_space.lean

modified src/set_theory/cardinal_ordinal.lean

modified src/set_theory/cofinality.lean

modified src/set_theory/game/nim.lean
- \+/\- *lemma* nim_wf_lemma
- \+/\- *lemma* nim_wf_lemma
- \- *theorem* ordinal.type_out'
- \+ *def* ordinal.out'
- \- *def* ordinal.out

modified src/set_theory/ordinal.lean
- \+ *lemma* type_lt
- \+/\- *lemma* card_typein_out_lt
- \- *lemma* type_out
- \+/\- *lemma* card_typein_out_lt
- \+ *theorem* type_lt_iff
- \+/\- *theorem* typein_lt_self
- \- *theorem* type_lt
- \+/\- *theorem* typein_lt_self
- \+/\- *def* initial_seg_out
- \+/\- *def* principal_seg_out
- \+/\- *def* rel_iso_out
- \+/\- *def* initial_seg_out
- \+/\- *def* principal_seg_out
- \+/\- *def* rel_iso_out

modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* lsub_typein
- \+/\- *theorem* sup_typein_succ
- \+/\- *theorem* lsub_typein
- \+/\- *theorem* sup_typein_succ

modified src/set_theory/principal.lean



## [2022-03-07 10:15:46](https://github.com/leanprover-community/mathlib/commit/9dd8ec1)
feat(analysis/normed/group/hom): add a module instance ([#12465](https://github.com/leanprover-community/mathlib/pull/12465))
#### Estimated changes
modified src/analysis/normed/group/hom.lean
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply



## [2022-03-07 10:15:45](https://github.com/leanprover-community/mathlib/commit/0b86bb8)
feat(measure_theory/group/arithmetic): actions by int and nat are measurable ([#12464](https://github.com/leanprover-community/mathlib/pull/12464))
The `has_measurable_smul₂` proofs are essentially copied from the analogous proofs for `has_measurable_pow`, after golfing them.
#### Estimated changes
modified src/measure_theory/group/arithmetic.lean



## [2022-03-07 10:15:43](https://github.com/leanprover-community/mathlib/commit/3f353db)
feat(data/nat/basic): add one_le_div_iff ([#12461](https://github.com/leanprover-community/mathlib/pull/12461))
Couldn't find these.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* one_le_div_iff
- \+ *lemma* div_lt_one_iff



## [2022-03-07 10:15:42](https://github.com/leanprover-community/mathlib/commit/2675b5c)
feat(measure_theory/constructions/polish): injective images of Borel sets in Polish spaces are Borel ([#12448](https://github.com/leanprover-community/mathlib/pull/12448))
We prove several fundamental results on the Borel sigma-algebra in Polish spaces, notably:
* Lusin separation theorem: disjoint analytic sets can be separated via Borel sets
* Lusin-Souslin theorem: a continuous injective image of a Borel set in a Polish space is Borel
* An injective measurable map on a Polish space is a measurable embedding, i.e., it maps measurable sets to measurable sets
#### Estimated changes
modified docs/references.bib

created src/measure_theory/constructions/polish.lean
- \+ *lemma* analytic_set_empty
- \+ *lemma* analytic_set_range_of_polish_space
- \+ *lemma* _root_.is_open.analytic_set_image
- \+ *lemma* analytic_set.image_of_continuous_on
- \+ *lemma* analytic_set.image_of_continuous
- \+ *lemma* _root_.measurable_set.is_clopenable
- \+ *lemma* _root_.measurable.exists_continuous
- \+ *lemma* measurably_separable.Union
- \+ *lemma* measurably_separable_range_of_disjoint
- \+ *lemma* is_clopenable_iff_measurable_set
- \+ *theorem* analytic_set_iff_exists_polish_space_range
- \+ *theorem* analytic_set.Inter
- \+ *theorem* analytic_set.Union
- \+ *theorem* _root_.is_closed.analytic_set
- \+ *theorem* _root_.measurable_set.analytic_set
- \+ *theorem* analytic_set.measurably_separable
- \+ *theorem* measurable_set_range_of_continuous_injective
- \+ *theorem* _root_.is_closed.measurable_set_image_of_continuous_on_inj_on
- \+ *theorem* _root_.measurable_set.image_of_continuous_on_inj_on
- \+ *theorem* _root_.measurable_set.image_of_measurable_inj_on
- \+ *theorem* _root_.continuous.measurable_embedding
- \+ *theorem* _root_.continuous_on.measurable_embedding
- \+ *theorem* _root_.measurable.measurable_embedding
- \+ *def* analytic_set
- \+ *def* measurably_separable



## [2022-03-07 10:15:41](https://github.com/leanprover-community/mathlib/commit/3778353)
feat(set_theory/ordinal_arithmetic): `enum_ord univ = id` ([#12391](https://github.com/leanprover-community/mathlib/pull/12391))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* enum_ord_range
- \+ *theorem* enum_ord_univ
- \+ *theorem* range_enum_ord
- \+/\- *theorem* enum_ord_range



## [2022-03-07 10:15:40](https://github.com/leanprover-community/mathlib/commit/313f405)
feat(category_theory/*): preserves biproducts implies additive ([#12014](https://github.com/leanprover-community/mathlib/pull/12014))
#### Estimated changes
created src/category_theory/limits/preserves/shapes/biproducts.lean
- \+ *lemma* map_biproduct_hom
- \+ *lemma* map_biproduct_inv
- \+ *lemma* map_biprod_hom
- \+ *lemma* map_biprod_inv
- \+ *lemma* biproduct.map_lift_map_biprod
- \+ *lemma* biproduct.map_biproduct_inv_map_desc
- \+ *lemma* biproduct.map_biproduct_hom_desc
- \+ *lemma* biprod.map_lift_map_biprod
- \+ *lemma* biprod.lift_map_biprod
- \+ *lemma* biprod.map_biprod_inv_map_desc
- \+ *lemma* biprod.map_biprod_hom_desc
- \+ *def* map_bicone
- \+ *def* map_binary_bicone
- \+ *def* is_bilimit_of_preserves
- \+ *def* is_binary_bilimit_of_preserves
- \+ *def* preserves_binary_biproduct_of_preserves_biproduct
- \+ *def* preserves_binary_biproducts_of_preserves_biproducts
- \+ *def* map_biproduct
- \+ *def* map_biprod
- \+ *def* preserves_product_of_preserves_biproduct
- \+ *def* preserves_products_of_shape_of_preserves_biproducts_of_shape
- \+ *def* preserves_biproduct_of_preserves_product
- \+ *def* preserves_biproducts_of_shape_of_preserves_products_of_shape
- \+ *def* preserves_coproduct_of_preserves_biproduct
- \+ *def* preserves_coproducts_of_shape_of_preserves_biproducts_of_shape
- \+ *def* preserves_biproduct_of_preserves_coproduct
- \+ *def* preserves_biproducts_of_shape_of_preserves_coproducts_of_shape
- \+ *def* preserves_binary_product_of_preserves_binary_biproduct
- \+ *def* preserves_binary_products_of_preserves_binary_biproducts
- \+ *def* preserves_binary_biproduct_of_preserves_binary_product
- \+ *def* preserves_binary_biproducts_of_preserves_binary_products
- \+ *def* preserves_binary_coproduct_of_preserves_binary_biproduct
- \+ *def* preserves_binary_coproducts_of_preserves_binary_biproducts
- \+ *def* preserves_binary_biproduct_of_preserves_binary_coproduct
- \+ *def* preserves_binary_biproducts_of_preserves_binary_coproducts

modified src/category_theory/limits/shapes/biproducts.lean

modified src/category_theory/preadditive/Mat.lean

modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* additive_of_preserves_binary_biproducts
- \- *def* map_biproduct



## [2022-03-07 10:15:38](https://github.com/leanprover-community/mathlib/commit/f063d0c)
feat(geometry/manifold/tangent_bundle): the `tangent_bundle` is a `topological_vector_bundle` ([#8295](https://github.com/leanprover-community/mathlib/pull/8295))
#### Estimated changes
modified src/geometry/manifold/cont_mdiff.lean
- \+/\- *lemma* cont_mdiff_on_proj
- \+/\- *lemma* smooth_on_proj
- \+/\- *lemma* cont_mdiff_at_proj
- \+/\- *lemma* smooth_at_proj
- \+/\- *lemma* cont_mdiff_on_proj
- \+/\- *lemma* smooth_on_proj
- \+/\- *lemma* cont_mdiff_at_proj
- \+/\- *lemma* smooth_at_proj
- \- *def* zero_section

modified src/geometry/manifold/mfderiv.lean

renamed src/geometry/manifold/basic_smooth_bundle.lean to src/geometry/manifold/tangent_bundle.lean
- \+ *lemma* target
- \+/\- *lemma* coe_chart_at_fst
- \+/\- *lemma* coe_chart_at_fst
- \+ *def* trivial_basic_smooth_vector_bundle_core
- \+ *def* to_topological_vector_bundle_core
- \+/\- *def* tangent_bundle_core
- \+/\- *def* tangent_space
- \+/\- *def* tangent_bundle
- \- *def* trivial_basic_smooth_bundle_core
- \- *def* to_topological_fiber_bundle_core
- \+/\- *def* tangent_bundle_core
- \+/\- *def* tangent_space
- \+/\- *def* tangent_bundle

modified src/topology/vector_bundle.lean
- \+/\- *lemma* mem_local_triv_source
- \+ *lemma* base_set_at
- \+ *lemma* local_triv_apply
- \+ *lemma* mem_local_triv_target
- \+ *lemma* local_triv_symm_fst
- \+ *lemma* local_triv_at_def
- \+/\- *lemma* mem_source_at
- \+ *lemma* mem_local_triv_at_base_set
- \+/\- *lemma* mem_local_triv_source
- \+/\- *lemma* mem_source_at
- \+ *def* trivial_topological_vector_bundle_core
- \+ *def* total_space



## [2022-03-07 08:10:23](https://github.com/leanprover-community/mathlib/commit/a19f6c6)
doc(algebra/group/to_additive): `to_additive` and docstring interaction ([#12476](https://github.com/leanprover-community/mathlib/pull/12476))
#### Estimated changes
modified src/algebra/group/to_additive.lean
- \+ *theorem* mul_comm'



## [2022-03-06 21:54:59](https://github.com/leanprover-community/mathlib/commit/92ef3c5)
feat(ring_theory/graded_algebra/radical) : radical of homogeneous ideal is homogeneous ([#12277](https://github.com/leanprover-community/mathlib/pull/12277))
This pr contains the following results about homogeneous ideals.
* `ideal.is_homogeneous.is_prime_iff`: for any `I : ideal A`, if `I` is homogeneous, then
   `I` is prime if and only if `I` is homogeneously prime, i.e. `I ≠ ⊤` and if `x, y` are
   homogeneous elements such that `x * y ∈ I`, then at least one of `x,y` is in `I`.
* `ideal.is_prime.homogeneous_core`: for any `I : ideal A`, if `I` is prime, then
   `I.homogeneous_core 𝒜` (i.e. the largest homogeneous ideal contained in `I`) is also prime.
* `ideal.is_homogeneous.radical`: for any `I : ideal A`, if `I` is homogeneous, then the
   radical of `I` is homogeneous as well.
* `homogeneous_ideal.radical`: for any `I : homogeneous_ideal 𝒜`, `I.radical` is the the
   radical of `I` as a `homogeneous_ideal 𝒜`
#### Estimated changes
modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* ideal.mem_homogeneous_core_of_is_homogeneous_of_mem

created src/ring_theory/graded_algebra/radical.lean
- \+ *lemma* ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem
- \+ *lemma* ideal.is_homogeneous.is_prime_iff
- \+ *lemma* ideal.is_prime.homogeneous_core
- \+ *lemma* ideal.is_homogeneous.radical_eq
- \+ *lemma* ideal.is_homogeneous.radical
- \+ *lemma* homogeneous_ideal.coe_radical
- \+ *def* homogeneous_ideal.radical



## [2022-03-06 18:41:38](https://github.com/leanprover-community/mathlib/commit/40602e6)
chore(set_theory/cardinal_divisibility): add instance unique (units cardinal) ([#12458](https://github.com/leanprover-community/mathlib/pull/12458))
#### Estimated changes
modified src/set_theory/cardinal_divisibility.lean



## [2022-03-06 15:36:29](https://github.com/leanprover-community/mathlib/commit/6696187)
chore(set_theory/ordinal_arithmetic): Reorder theorems ([#12475](https://github.com/leanprover-community/mathlib/pull/12475))
It makes more sense for `is_normal.bsup_eq` and `is_normal.blsub_eq` to be together.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* is_normal.blsub_eq
- \+/\- *theorem* is_normal.blsub_eq



## [2022-03-06 15:06:27](https://github.com/leanprover-community/mathlib/commit/0a6efe0)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a star normal element is its norm ([#12249](https://github.com/leanprover-community/mathlib/pull/12249))
In a C⋆-algebra over ℂ, the spectral radius of any star normal element is its norm. This extends the corresponding result for selfadjoint elements.
- [x] depends on: [#12211](https://github.com/leanprover-community/mathlib/pull/12211) 
- [x] depends on: [#11991](https://github.com/leanprover-community/mathlib/pull/11991)
#### Estimated changes
modified src/analysis/normed_space/star/spectrum.lean
- \+ *lemma* spectral_radius_eq_nnnorm_of_star_normal
- \- *lemma* self_adjoint.coe_spectral_radius_eq_nnnorm



## [2022-03-06 11:52:53](https://github.com/leanprover-community/mathlib/commit/28c902d)
fix(algebra/group/pi): Fix apply-simp-lemmas for monoid_hom.single ([#12474](https://github.com/leanprover-community/mathlib/pull/12474))
so that the simp-normal form really is `pi.mul_single`.
While adjusting related lemmas in `group_theory.subgroup.basic`, add a
few missing `to_additive` attributes.
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* one_hom.single_apply
- \+ *lemma* monoid_hom.single_apply

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mul_single_mem_pi
- \+ *lemma* pi_mem_of_mul_single_mem_aux
- \+ *lemma* pi_mem_of_mul_single_mem
- \- *lemma* single_mem_pi
- \- *lemma* pi_mem_of_single_mem_aux
- \- *lemma* pi_mem_of_single_mem



## [2022-03-06 07:44:42](https://github.com/leanprover-community/mathlib/commit/64d953a)
refactor(set_theory/ordinal): `enum_lt` → `enum_lt_enum` ([#12469](https://github.com/leanprover-community/mathlib/pull/12469))
That way, the theorem name matches that of `enum_le_enum`, `typein_lt_typein`, and `typein_le_typein`.
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* enum_lt_enum
- \- *theorem* enum_lt

modified src/set_theory/ordinal_arithmetic.lean



## [2022-03-06 07:44:41](https://github.com/leanprover-community/mathlib/commit/d61ebab)
feat(category_theory/abelian): (co)kernels in terms of exact sequences ([#12460](https://github.com/leanprover-community/mathlib/pull/12460))
#### Estimated changes
modified src/category_theory/abelian/basic.lean
- \+ *lemma* comp_epi_desc
- \+ *lemma* mono_lift_comp
- \+ *def* epi_desc
- \+ *def* mono_lift

modified src/category_theory/abelian/exact.lean
- \+ *lemma* exact_of_is_cokernel
- \+ *lemma* exact_of_is_kernel
- \+ *def* is_colimit_of_exact_of_epi
- \+ *def* is_limit_of_exact_of_mono



## [2022-03-06 07:44:40](https://github.com/leanprover-community/mathlib/commit/b7808a9)
chore(set_theory/ordinal_arithmetic): Golf `lsub_typein` and `blsub_id` ([#12203](https://github.com/leanprover-community/mathlib/pull/12203))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* lsub_typein
- \+/\- *theorem* sup_typein_limit
- \+/\- *theorem* sup_typein_succ
- \+/\- *theorem* blsub_id
- \+/\- *theorem* bsup_id_limit
- \+/\- *theorem* bsup_id_succ
- \+/\- *theorem* is_normal.bsup_eq
- \+/\- *theorem* is_normal.eq_iff_zero_and_succ
- \+/\- *theorem* is_normal.blsub_eq
- \+/\- *theorem* bsup_id_limit
- \+/\- *theorem* bsup_id_succ
- \+/\- *theorem* is_normal.bsup_eq
- \+/\- *theorem* is_normal.eq_iff_zero_and_succ
- \+/\- *theorem* blsub_id
- \+/\- *theorem* is_normal.blsub_eq
- \+/\- *theorem* lsub_typein
- \+/\- *theorem* sup_typein_limit
- \+/\- *theorem* sup_typein_succ



## [2022-03-06 07:44:39](https://github.com/leanprover-community/mathlib/commit/b4d007f)
feat(category_theory/limits): transport is_limit along F.left_op and similar ([#12166](https://github.com/leanprover-community/mathlib/pull/12166))
#### Estimated changes
modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* has_limit_of_has_colimit_left_op
- \+/\- *lemma* has_colimit_of_has_limit_left_op
- \+/\- *lemma* has_limit_of_has_colimit_left_op
- \+/\- *lemma* has_colimit_of_has_limit_left_op
- \+ *def* is_limit_cocone_op
- \+ *def* is_colimit_cone_op
- \+ *def* is_limit_cone_left_op_of_cocone
- \+ *def* is_colimit_cocone_left_op_of_cone
- \+ *def* is_limit_cone_right_op_of_cocone
- \+ *def* is_colimit_cocone_right_op_of_cone
- \+ *def* is_limit_cone_unop_of_cocone
- \+ *def* is_colimit_cocone_unop_of_cone
- \+ *def* is_limit_cocone_unop
- \+ *def* is_colimit_cone_unop
- \+ *def* is_limit_cone_of_cocone_left_op
- \+ *def* is_colimit_cocone_of_cone_left_op
- \+ *def* is_limit_cone_of_cocone_right_op
- \+ *def* is_colimit_cocone_of_cone_right_op
- \+ *def* is_limit_cone_of_cocone_unop
- \+ *def* is_colimit_cone_of_cocone_unop



## [2022-03-06 07:44:38](https://github.com/leanprover-community/mathlib/commit/371b48a)
feal(category_theory/bicategory/functor): define pseudofunctors ([#11992](https://github.com/leanprover-community/mathlib/pull/11992))
This PR defines pseudofunctors between bicategories. 
We provide two constructors (`mk_of_oplax` and `mk_of_oplax'`) that construct pseudofunctors from oplax functors whose `map_id` and `map_comp` are isomorphisms. The constructor `mk_of_oplax` uses `iso` to describe isomorphisms, while `mk_of_oplax'` uses `is_iso`.
#### Estimated changes
modified src/category_theory/bicategory/functor.lean
- \+ *lemma* to_prefunctor_eq_coe
- \+/\- *lemma* to_prefunctor_obj
- \+/\- *lemma* to_prefunctor_map
- \+ *lemma* to_prelax_eq_coe
- \+/\- *lemma* to_prelax_functor_obj
- \+/\- *lemma* to_prelax_functor_map
- \+/\- *lemma* to_prelax_functor_map₂
- \+ *lemma* to_prelax_functor_eq_coe
- \+/\- *lemma* to_prelax_functor_obj
- \+/\- *lemma* to_prelax_functor_map
- \+/\- *lemma* to_prelax_functor_map₂
- \+ *lemma* to_oplax_eq_coe
- \+ *lemma* to_oplax_obj
- \+ *lemma* to_oplax_map
- \+ *lemma* to_oplax_map₂
- \+ *lemma* to_oplax_map_id
- \+ *lemma* to_oplax_map_comp
- \+/\- *lemma* to_prefunctor_obj
- \+/\- *lemma* to_prefunctor_map
- \+/\- *lemma* to_prelax_functor_obj
- \+/\- *lemma* to_prelax_functor_map
- \+/\- *lemma* to_prelax_functor_map₂
- \+ *def* pseudofunctor.comp
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* comp
- \+ *def* pseudofunctor.map₂_associator_aux
- \+ *def* to_oplax
- \+ *def* map_functor
- \+/\- *def* id
- \+/\- *def* comp
- \+ *def* mk_of_oplax
- \+ *def* mk_of_oplax'
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* comp



## [2022-03-06 07:11:07](https://github.com/leanprover-community/mathlib/commit/62e7d35)
feat(category_theory/limits): uniqueness of preadditive structures ([#12342](https://github.com/leanprover-community/mathlib/pull/12342))
#### Estimated changes
modified src/category_theory/abelian/non_preadditive.lean

modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* bicone_ι_π_self
- \+ *lemma* biprod.add_eq_lift_id_desc
- \+ *lemma* biprod.add_eq_lift_desc_id
- \+/\- *lemma* bicone_ι_π_self



## [2022-03-05 17:38:12](https://github.com/leanprover-community/mathlib/commit/974d23c)
feat(data/polynomial/monic): add monic_of_mul_monic_left/right ([#12446](https://github.com/leanprover-community/mathlib/pull/12446))
Also clean up variables that are defined in the section.
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60geom_sum.20.28X.20.20n.29.60.20is.20monic/near/274130839
#### Estimated changes
modified src/data/polynomial/monic.lean
- \+/\- *lemma* monic.as_sum
- \+/\- *lemma* monic_add_of_left
- \+/\- *lemma* monic_add_of_right
- \+ *lemma* monic.of_mul_monic_left
- \+ *lemma* monic.of_mul_monic_right
- \+/\- *lemma* monic.as_sum
- \+/\- *lemma* monic_add_of_left
- \+/\- *lemma* monic_add_of_right



## [2022-03-05 16:13:55](https://github.com/leanprover-community/mathlib/commit/e542154)
feat(category_theory/full_subcategory): full_subcategory.map and full_subcategory.lift ([#12335](https://github.com/leanprover-community/mathlib/pull/12335))
#### Estimated changes
modified src/category_theory/full_subcategory.lean
- \+ *lemma* full_subcategory.map_inclusion
- \+ *lemma* full_subcategory.inclusion_obj_lift_obj
- \+ *lemma* full_subcategory.inclusion_map_lift_map
- \+ *lemma* full_subcategory.lift_comp_map
- \+ *def* full_subcategory.map
- \+ *def* full_subcategory.lift
- \+ *def* full_subcategory.lift_comp_inclusion

modified src/category_theory/functor/fully_faithful.lean
- \+ *def* full.of_comp_faithful_iso



## [2022-03-05 16:13:54](https://github.com/leanprover-community/mathlib/commit/51adf3a)
feat(model_theory/terms_and_formulas): Using a list encoding, bounds the number of terms ([#12276](https://github.com/leanprover-community/mathlib/pull/12276))
Defines `term.list_encode` and `term.list_decode`, which turn terms into lists, and reads off lists as lists of terms.
Bounds the number of terms by the number of allowed symbols + omega.
#### Estimated changes
modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* list_encode_injective
- \+ *theorem* list_decode_encode_list
- \+ *theorem* card_le
- \+ *def* list_encode
- \+ *def* list_decode



## [2022-03-05 15:19:46](https://github.com/leanprover-community/mathlib/commit/92b27e1)
feat(category_theory/discrete_category): generalize universes for comp_nat_iso_discrete ([#12340](https://github.com/leanprover-community/mathlib/pull/12340))
#### Estimated changes
modified src/category_theory/discrete_category.lean
- \+/\- *def* comp_nat_iso_discrete
- \+/\- *def* comp_nat_iso_discrete



## [2022-03-05 15:19:45](https://github.com/leanprover-community/mathlib/commit/4ecd92a)
feat(category_theory/abelian): faithful functors reflect exact sequences ([#12071](https://github.com/leanprover-community/mathlib/pull/12071))
#### Estimated changes
modified src/algebra/homology/exact.lean
- \+/\- *lemma* mono_iff_exact_zero_left
- \+ *lemma* exact_of_exact_map
- \+ *lemma* exact_of_exact_map'
- \+/\- *lemma* mono_iff_exact_zero_left

modified src/category_theory/abelian/exact.lean

modified src/category_theory/limits/preserves/shapes/zero.lean
- \+ *lemma* zero_of_map_zero
- \+ *lemma* map_eq_zero_iff



## [2022-03-05 13:15:02](https://github.com/leanprover-community/mathlib/commit/fa6b16e)
feat(data/nat/prime): add nat.eq_two_pow_or_exists_odd_prime_and_dvd ([#12395](https://github.com/leanprover-community/mathlib/pull/12395))
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* prime.eq_two_or_odd'
- \+ *lemma* eq_prime_pow_of_unique_prime_dvd
- \+ *lemma* eq_two_pow_or_exists_odd_prime_and_dvd



## [2022-03-05 13:15:01](https://github.com/leanprover-community/mathlib/commit/8b91390)
feat(order/hom/basic): add `order_iso.with_{top,bot}_congr` ([#12264](https://github.com/leanprover-community/mathlib/pull/12264))
This adds:
* `with_bot.to_dual_top`
* `with_top.to_dual_bot`
* `order_iso.with_top_congr`
* `order_iso.with_bot_congr`
#### Estimated changes
modified src/data/option/basic.lean
- \+ *theorem* map_coe
- \+ *theorem* map_coe'

modified src/order/bounded_order.lean
- \+ *lemma* map_bot
- \+ *lemma* map_coe
- \+ *lemma* map_top
- \+ *lemma* map_coe

modified src/order/hom/basic.lean
- \+ *lemma* to_dual_top_coe
- \+ *lemma* to_dual_top_symm_coe
- \+ *lemma* to_dual_bot_coe
- \+ *lemma* to_dual_bot_symm_coe
- \+ *lemma* with_top_congr_refl
- \+ *lemma* with_top_congr_symm
- \+ *lemma* with_top_congr_trans
- \+ *lemma* with_bot_congr_refl
- \+ *lemma* with_bot_congr_symm
- \+ *lemma* with_bot_congr_trans
- \+ *def* with_top_congr
- \+ *def* with_bot_congr



## [2022-03-05 12:17:39](https://github.com/leanprover-community/mathlib/commit/2840532)
doc(topology/uniform_space/cauchy): fix typo ([#12453](https://github.com/leanprover-community/mathlib/pull/12453))
#### Estimated changes
modified src/topology/uniform_space/cauchy.lean



## [2022-03-05 10:56:08](https://github.com/leanprover-community/mathlib/commit/bda091d)
feat(measure_theory/card_measurable_space): cardinality of generated sigma-algebras ([#12422](https://github.com/leanprover-community/mathlib/pull/12422))
If a sigma-algebra is generated by a set of sets `s` whose cardinality is at most the continuum,
then the sigma-algebra satisfies the same cardinality bound.
#### Estimated changes
created src/measure_theory/card_measurable_space.lean
- \+ *lemma* cardinal_generate_measurable_rec_le
- \+ *lemma* cardinal_Union_generate_measurable_rec_le
- \+ *theorem* generate_measurable_subset_rec
- \+ *theorem* cardinal_generate_measurable_le
- \+ *theorem* cardinal_measurable_set_le
- \+ *theorem* cardinal_generate_measurable_le_continuum
- \+ *theorem* cardinal_measurable_set_le_continuum
- \+ *def* generate_measurable_rec

modified src/set_theory/cardinal.lean
- \+/\- *theorem* power_le_power_left
- \+ *theorem* self_le_power
- \+/\- *theorem* power_le_power_left

modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* omega_lt_aleph_one
- \+ *theorem* add_le_of_le

modified src/set_theory/cofinality.lean
- \+ *theorem* is_regular_aleph_one

modified src/set_theory/continuum.lean
- \+ *lemma* aleph_one_le_continuum

modified src/set_theory/ordinal.lean



## [2022-03-05 09:10:31](https://github.com/leanprover-community/mathlib/commit/93451af)
feat(order/category/BoolAlg): The category of Boolean algebras ([#12452](https://github.com/leanprover-community/mathlib/pull/12452))
Define `BoolAlg`, the category of Boolean algebras with bounded lattice homs.
#### Estimated changes
modified src/order/boolean_algebra.lean

created src/order/category/BoolAlg.lean
- \+ *lemma* BoolAlg_dual_comp_forget_to_BoundedDistribLattice
- \+ *def* BoolAlg
- \+ *def* of
- \+ *def* to_BoundedDistribLattice
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv



## [2022-03-05 09:10:30](https://github.com/leanprover-community/mathlib/commit/f5b885b)
feat(linear_algebra/clifford_algebra/conjugation): reverse and involute are grade-preserving ([#12373](https://github.com/leanprover-community/mathlib/pull/12373))
This shows that various submodules are preserved under `submodule.map` by `reverse` or `involute`.
#### Estimated changes
modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *lemma* submodule_map_involute_eq_comap
- \+/\- *lemma* ι_range_map_involute
- \+/\- *lemma* ι_range_comap_involute
- \+ *lemma* even_odd_map_involute
- \+ *lemma* even_odd_comap_involute
- \+ *lemma* submodule_map_reverse_eq_comap
- \+/\- *lemma* ι_range_map_reverse
- \+/\- *lemma* ι_range_comap_reverse
- \+ *lemma* submodule_map_mul_reverse
- \+ *lemma* submodule_comap_mul_reverse
- \+ *lemma* submodule_map_pow_reverse
- \+ *lemma* submodule_comap_pow_reverse
- \+ *lemma* even_odd_map_reverse
- \+ *lemma* even_odd_comap_reverse
- \+ *lemma* involute_mem_even_odd_iff
- \+ *lemma* reverse_mem_even_odd_iff
- \+/\- *lemma* ι_range_map_involute
- \+/\- *lemma* ι_range_comap_involute
- \+/\- *lemma* ι_range_map_reverse
- \+/\- *lemma* ι_range_comap_reverse

modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* ι_mem_even_odd_one



## [2022-03-05 08:41:18](https://github.com/leanprover-community/mathlib/commit/ac28ddf)
feat(data/nat/fib): add bit0/bit1 lemmas and fast_fib ([#12444](https://github.com/leanprover-community/mathlib/pull/12444))
This provides lemmas that let `simp` calculate `fib` from the bit0/bit1 numeral representation. (This isn't intended to be for speed, although it does evaluate things reasonably quick.)
```lean
lemma foo : fib 64 = 10610209857723 :=
begin
  norm_num [fib_bit0, fib_bit1, fib_bit0_succ, fib_bit1_succ],
end
```
These are then used to show that `fast_fib` computes `fib`.
#### Estimated changes
modified src/data/nat/fib.lean
- \+ *lemma* fib_add_two_sub_fib_add_one
- \+ *lemma* fib_two_mul
- \+ *lemma* fib_two_mul_add_one
- \+ *lemma* fib_bit0
- \+ *lemma* fib_bit1
- \+ *lemma* fib_bit0_succ
- \+ *lemma* fib_bit1_succ
- \+ *lemma* fast_fib_aux_bit_ff
- \+ *lemma* fast_fib_aux_bit_tt
- \+ *lemma* fast_fib_aux_eq
- \+ *lemma* fast_fib_eq
- \+ *def* fast_fib_aux
- \+ *def* fast_fib



## [2022-03-05 06:05:25](https://github.com/leanprover-community/mathlib/commit/36a528d)
feat(set_theory/ordinal_arithmetic): `add_le_of_forall_add_lt` ([#12315](https://github.com/leanprover-community/mathlib/pull/12315))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* add_le_of_forall_add_lt



## [2022-03-05 03:06:09](https://github.com/leanprover-community/mathlib/commit/b0d9462)
feat(category_theory/preadditive/injective) : more basic properties and morphisms about injective objects ([#12450](https://github.com/leanprover-community/mathlib/pull/12450))
This pr dualises the rest of `projective.lean`
#### Estimated changes
modified src/category_theory/preadditive/injective.lean
- \+ *lemma* exact.comp_desc
- \+ *def* under
- \+ *def* ι
- \+ *def* syzygies
- \+ *def* exact.desc



## [2022-03-05 03:06:08](https://github.com/leanprover-community/mathlib/commit/fdf43f1)
feat(category_theory/closed): generalize some material from cartesian closed categories to closed monoidal categories ([#12386](https://github.com/leanprover-community/mathlib/pull/12386))
No new content, just moving some trivially generalisable material about cartesian closed categories to closed monoidal categories.
I've defined `ihom` for internal hom, and made `exp` an abbreviation for it in the cartesian closed case.
A few other definitions similarly become abbreviations.
I've left the `⟹` arrow for the internal hom in the cartesian closed case, and added `⟶[C]` for the general internal hom.
#### Estimated changes
modified src/algebra/category/Module/monoidal.lean

modified src/category_theory/closed/cartesian.lean
- \+/\- *lemma* coev_ev
- \+/\- *lemma* uncurry_eq
- \+/\- *lemma* curry_eq
- \+/\- *lemma* uncurry_id_eq_ev
- \+/\- *lemma* curry_id_eq_coev
- \- *lemma* exp_adjunction_counit
- \- *lemma* exp_adjunction_unit
- \- *lemma* ev_naturality
- \- *lemma* coev_naturality
- \+/\- *lemma* coev_ev
- \+/\- *lemma* uncurry_eq
- \+/\- *lemma* curry_eq
- \+/\- *lemma* uncurry_id_eq_ev
- \+/\- *lemma* curry_id_eq_coev
- \- *def* exp
- \- *def* exp.adjunction
- \- *def* ev
- \- *def* coev

modified src/category_theory/closed/functor.lean

modified src/category_theory/closed/ideal.lean

modified src/category_theory/closed/monoidal.lean
- \+ *lemma* ihom_adjunction_counit
- \+ *lemma* ihom_adjunction_unit
- \+ *lemma* ev_naturality
- \+ *lemma* coev_naturality
- \+ *lemma* ev_coev
- \+ *lemma* coev_ev
- \+ *lemma* hom_equiv_apply_eq
- \+ *lemma* hom_equiv_symm_apply_eq
- \+ *lemma* curry_natural_left
- \+ *lemma* curry_natural_right
- \+ *lemma* uncurry_natural_right
- \+ *lemma* uncurry_natural_left
- \+ *lemma* uncurry_curry
- \+ *lemma* curry_uncurry
- \+ *lemma* curry_eq_iff
- \+ *lemma* eq_curry_iff
- \+ *lemma* uncurry_eq
- \+ *lemma* curry_eq
- \+ *lemma* curry_injective
- \+ *lemma* uncurry_injective
- \+ *lemma* uncurry_id_eq_ev
- \+ *lemma* curry_id_eq_coev
- \+ *lemma* id_tensor_pre_app_comp_ev
- \+ *lemma* uncurry_pre
- \+ *lemma* coev_app_comp_pre_app
- \+ *lemma* pre_id
- \+ *lemma* pre_map
- \+ *def* tensor_closed
- \+/\- *def* unit_closed
- \+ *def* ihom
- \+ *def* adjunction
- \+ *def* ev
- \+ *def* coev
- \+ *def* curry
- \+ *def* uncurry
- \+ *def* pre
- \+ *def* internal_hom
- \+/\- *def* unit_closed

modified src/category_theory/closed/types.lean



## [2022-03-05 01:51:47](https://github.com/leanprover-community/mathlib/commit/45d235e)
feat(analysis/normed_space/star/matrix): `entrywise_sup_norm_bound_of_unitary` ([#12255](https://github.com/leanprover-community/mathlib/pull/12255))
The entrywise sup norm of a unitary matrix is at most 1.
I suspect there is a simpler proof!
#### Estimated changes
created src/analysis/normed_space/star/matrix.lean
- \+ *lemma* entry_norm_bound_of_unitary
- \+ *lemma* entrywise_sup_norm_bound_of_unitary



## [2022-03-05 01:51:46](https://github.com/leanprover-community/mathlib/commit/1755911)
feat(topology/compacts): The types of clopens and of compact opens ([#11966](https://github.com/leanprover-community/mathlib/pull/11966))
Define `clopens` and ` compact_opens`, the types of clopens and of compact open sets of a topological space.
#### Estimated changes
modified src/topology/compacts.lean
- \+ *lemma* clopen
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_compl
- \+ *lemma* compact
- \+ *lemma* «open»
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_compl
- \+ *lemma* coe_map
- \+ *def* to_opens
- \+ *def* to_opens
- \+ *def* to_clopens
- \+ *def* map



## [2022-03-05 00:00:54](https://github.com/leanprover-community/mathlib/commit/8e1da4e)
feat(ring_theory/adjoin/basic): if a set of elements of a subobject commute, its closure/adjoin is also commutative ([#12231](https://github.com/leanprover-community/mathlib/pull/12231))
We show that if a set of elements of a subobject commute, its closure/adjoin is also commutative The subobjects include (additive) submonoids, (additive) subgroups, subsemirings, subrings, and subalgebras.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* closure_induction₂
- \+ *def* closure_comm_group_of_comm

modified src/group_theory/submonoid/basic.lean
- \+ *lemma* closure_induction₂

modified src/group_theory/submonoid/membership.lean
- \+ *def* closure_comm_monoid_of_comm

modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_induction₂
- \+ *def* adjoin_comm_semiring_of_comm
- \+ *def* adjoin_comm_ring_of_comm

modified src/ring_theory/subring/basic.lean
- \+ *lemma* closure_induction₂
- \+ *def* closure_comm_ring_of_comm

modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* closure_induction₂
- \+ *def* closure_comm_semiring_of_comm



## [2022-03-04 21:44:21](https://github.com/leanprover-community/mathlib/commit/3ac971b)
feat(order/category/Frame): The category of frames ([#12363](https://github.com/leanprover-community/mathlib/pull/12363))
Define `Frame`, the category of frames with frame homomorphisms.
#### Estimated changes
created src/order/category/Frame.lean
- \+ *def* Frame
- \+ *def* of
- \+ *def* iso.mk



## [2022-03-04 21:44:20](https://github.com/leanprover-community/mathlib/commit/ee4be2d)
feat(ring_theory/simple_module): Simple modules as simple objects in the Module category ([#11927](https://github.com/leanprover-community/mathlib/pull/11927))
A simple module is a simple object in the Module category. 
From there it should be easy to write an alternative proof of Schur's lemma for modules using category theory (using the work already done in category_theory/preadditive/schur.lean).
The other direction (a simple object in the Module category is a simple module) hasn't been proved yet.
#### Estimated changes
modified src/algebra/category/Module/epi_mono.lean
- \+ *def* unique_of_epi_zero

created src/algebra/category/Module/simple.lean

modified src/data/pi.lean
- \+ *def* unique_of_surjective_one

modified src/logic/unique.lean
- \+ *def* surjective.unique_of_surjective_const



## [2022-03-04 21:44:19](https://github.com/leanprover-community/mathlib/commit/a07cf6b)
feat(ring_theory/polynomial/homogeneous) : add lemma `homogeneous_component_homogeneous_polynomial` ([#10113](https://github.com/leanprover-community/mathlib/pull/10113))
add the following lemma
```lean
lemma homogeneous_component_homogeneous_polynomial (m n : ℕ)
  (p : mv_polynomial σ R) (h : p ∈ homogeneous_submodule σ R n) :
  homogeneous_component m p = if m = n then p else 0
```
#### Estimated changes
modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* homogeneous_component_homogeneous_polynomial



## [2022-03-04 19:43:16](https://github.com/leanprover-community/mathlib/commit/34d8ff1)
feat(topology/algebra/weak_dual): generalize to weak topologies for arbitrary dualities ([#12284](https://github.com/leanprover-community/mathlib/pull/12284))
#### Estimated changes
modified src/analysis/normed_space/weak_dual.lean

modified src/topology/algebra/module/weak_dual.lean
- \+/\- *lemma* coe_fn_continuous
- \+/\- *lemma* eval_continuous
- \+/\- *lemma* continuous_of_continuous_eval
- \+ *lemma* bilin_embedding
- \+ *lemma* dual_pairing_apply
- \- *lemma* coe_fn_embedding
- \+/\- *lemma* coe_fn_continuous
- \+/\- *lemma* eval_continuous
- \+/\- *lemma* continuous_of_continuous_eval
- \+/\- *theorem* tendsto_iff_forall_eval_tendsto
- \+/\- *theorem* tendsto_iff_forall_eval_tendsto
- \+ *def* weak_bilin
- \+ *def* top_dual_pairing
- \+/\- *def* weak_dual
- \+ *def* weak_space
- \+/\- *def* weak_dual



## [2022-03-04 19:43:15](https://github.com/leanprover-community/mathlib/commit/89654c0)
feat(data/equiv/{mul_add,ring}): Coercions to types of morphisms from their `_class` ([#12243](https://github.com/leanprover-community/mathlib/pull/12243))
Add missing coercions to `α ≃+ β`, `α ≃* β`, `α ≃+* β` from `add_equiv_class`, `mul_equiv_class`, `ring_equiv_class`.
#### Estimated changes
modified src/data/equiv/mul_add.lean

modified src/data/equiv/ring.lean



## [2022-03-04 17:34:12](https://github.com/leanprover-community/mathlib/commit/30d63cd)
feat(field_theory/cardinality): a cardinal can have a field structure iff it is a prime power ([#12442](https://github.com/leanprover-community/mathlib/pull/12442))
#### Estimated changes
modified src/field_theory/cardinality.lean
- \+ *lemma* field.nonempty_iff



## [2022-03-04 17:34:11](https://github.com/leanprover-community/mathlib/commit/858002b)
feat(algebra/char_zero): cast(_pow)_eq_one ([#12429](https://github.com/leanprover-community/mathlib/pull/12429))
#### Estimated changes
modified src/algebra/char_zero.lean
- \+ *lemma* cast_pow_eq_one
- \+ *theorem* cast_eq_one
- \+ *theorem* cast_ne_one



## [2022-03-04 17:34:10](https://github.com/leanprover-community/mathlib/commit/a54dd9e)
feat(order/category/BoundedDistribLattice): The category of bounded distributive lattices ([#12347](https://github.com/leanprover-community/mathlib/pull/12347))
Define `BoundedDistribLattice`, the category of bounded distributive lattices with bounded lattice homomorphisms.
#### Estimated changes
created src/order/category/BoundedDistribLattice.lean
- \+ *lemma* coe_of
- \+ *lemma* coe_to_BoundedLattice
- \+ *lemma* forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice
- \+ *lemma* BoundedDistribLattice_dual_comp_forget_to_DistribLattice
- \+ *def* of
- \+ *def* to_BoundedLattice
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv

modified src/order/category/DistribLattice.lean



## [2022-03-04 17:34:09](https://github.com/leanprover-community/mathlib/commit/fab59cb)
feat(set_theory/cofinality): `cof_eq_Inf_lsub` ([#12314](https://github.com/leanprover-community/mathlib/pull/12314))
This much nicer characterization of cofinality will allow us to prove various theorems relating it to `lsub` and `blsub`.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* mk_ordinal_out

modified src/set_theory/cofinality.lean
- \+ *theorem* cof_lsub_def_nonempty
- \+ *theorem* cof_eq_Inf_lsub



## [2022-03-04 17:34:07](https://github.com/leanprover-community/mathlib/commit/efd9a16)
refactor(group_theory/commutator): Define commutators of subgroups in terms of commutators of elements ([#12309](https://github.com/leanprover-community/mathlib/pull/12309))
This PR defines commutators of elements of groups.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* commutator_element_def

modified src/group_theory/abelianization.lean
- \+/\- *lemma* commutator_eq_closure
- \+/\- *lemma* commutator_eq_closure

modified src/group_theory/commutator.lean
- \+ *lemma* commutator_element_inv
- \+ *lemma* map_commutator_element
- \+ *lemma* conjugate_commutator_element

modified src/group_theory/nilpotent.lean

modified src/tactic/group.lean

modified test/group.lean
- \- *def* commutator
- \- *def* commutator3



## [2022-03-04 17:34:06](https://github.com/leanprover-community/mathlib/commit/35b835a)
feat(data/set/sigma): Indexed sum of sets ([#12305](https://github.com/leanprover-community/mathlib/pull/12305))
Define `set.sigma`, the sum of a family of sets indexed by a set.
#### Estimated changes
modified src/data/finset/sigma.lean
- \+ *lemma* coe_sigma

created src/data/set/sigma.lean
- \+ *lemma* mem_sigma_iff
- \+ *lemma* mk_sigma_iff
- \+ *lemma* mk_mem_sigma
- \+ *lemma* sigma_mono
- \+ *lemma* sigma_subset_iff
- \+ *lemma* forall_sigma_iff
- \+ *lemma* exists_sigma_iff
- \+ *lemma* sigma_empty
- \+ *lemma* empty_sigma
- \+ *lemma* univ_sigma_univ
- \+ *lemma* sigma_univ
- \+ *lemma* singleton_sigma
- \+ *lemma* sigma_singleton
- \+ *lemma* singleton_sigma_singleton
- \+ *lemma* union_sigma
- \+ *lemma* sigma_union
- \+ *lemma* sigma_inter_sigma
- \+ *lemma* insert_sigma
- \+ *lemma* sigma_insert
- \+ *lemma* sigma_preimage_eq
- \+ *lemma* sigma_preimage_left
- \+ *lemma* sigma_preimage_right
- \+ *lemma* preimage_sigma_map_sigma
- \+ *lemma* mk_preimage_sigma
- \+ *lemma* mk_preimage_sigma_eq_empty
- \+ *lemma* mk_preimage_sigma_eq_if
- \+ *lemma* mk_preimage_sigma_fn_eq_if
- \+ *lemma* sigma_univ_range_eq
- \+ *lemma* nonempty.sigma_fst
- \+ *lemma* nonempty.sigma_snd
- \+ *lemma* sigma_nonempty_iff
- \+ *lemma* sigma_eq_empty_iff
- \+ *lemma* image_sigma_mk_subset_sigma_left
- \+ *lemma* image_sigma_mk_subset_sigma_right
- \+ *lemma* sigma_subset_preimage_fst
- \+ *lemma* fst_image_sigma_subset
- \+ *lemma* fst_image_sigma
- \+ *lemma* sigma_diff_sigma

modified src/logic/basic.lean
- \+ *lemma* not_or_of_imp
- \+ *lemma* or_not_of_imp
- \+ *lemma* imp_iff_not_or
- \+ *lemma* imp_iff_or_not
- \- *theorem* not_or_of_imp
- \- *theorem* imp_iff_not_or



## [2022-03-04 17:34:05](https://github.com/leanprover-community/mathlib/commit/ed63386)
feat(category_theory/preadditive/injective) : definition of injective objects in a category ([#11921](https://github.com/leanprover-community/mathlib/pull/11921))
This pr contains definition of injective objects and some useful instances.
#### Estimated changes
created src/category_theory/preadditive/injective.lean
- \+ *lemma* comp_factor_thru
- \+ *lemma* of_iso
- \+ *lemma* iso_iff
- \+ *def* factor_thru



## [2022-03-04 17:34:04](https://github.com/leanprover-community/mathlib/commit/a8629a5)
refactor(tactic/interactive): use 1-indexing in work_on_goal ([#11813](https://github.com/leanprover-community/mathlib/pull/11813))
Backporting the change in https://github.com/leanprover-community/mathlib4/pull/178 to make `work_on_goal` 1-indexed. See also: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60work_on_goal.60.20vs.20.60swap.60
#### Estimated changes
modified archive/100-theorems-list/73_ascending_descending_sequences.lean

modified src/algebra/algebra/operations.lean

modified src/combinatorics/hales_jewett.lean

modified src/data/mv_polynomial/variables.lean

modified src/group_theory/submonoid/pointwise.lean

modified src/linear_algebra/alternating.lean

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/tactic/chain.lean

modified src/tactic/interactive.lean

modified test/swap_var.lean

modified test/tidy.lean



## [2022-03-04 15:24:38](https://github.com/leanprover-community/mathlib/commit/0ec8e6a)
feat(algebra/algebra/operations): more lemmas about `mul_opposite` ([#12441](https://github.com/leanprover-community/mathlib/pull/12441))
Naturally the lemmas I left out of the previous PR, notably `map_unop_mul` and `map_unop_pow`, are the ones I actually needed.
This also improves the `simps` lemmas on `submodule.equiv_opposite`, which were previously garbage as `simps` didn't unfold `ring_equiv.symm` properly. At any rate, the only reason it was defined that way was because the lemmas in this PR were missing.
#### Estimated changes
modified src/algebra/algebra/operations.lean
- \+ *lemma* map_unop_mul
- \+ *lemma* comap_op_mul
- \+ *lemma* comap_op_pow
- \+/\- *lemma* map_op_pow
- \+ *lemma* map_unop_pow
- \+/\- *lemma* map_op_pow



## [2022-03-04 15:24:37](https://github.com/leanprover-community/mathlib/commit/31cb3c1)
chore(algebra/group_with_zero/basic): generalize `units.exists_iff_ne_zero` to arbitrary propositions ([#12439](https://github.com/leanprover-community/mathlib/pull/12439))
This adds a more powerful version of this lemma that allows an existential to be replaced with one over the underlying group with zero.
The naming matches `subtype.exists` and `subtype.exists'`, while the trailing zero matches `units.mk0`.
#### Estimated changes
modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* exists0
- \+ *lemma* exists0'



## [2022-03-04 15:24:36](https://github.com/leanprover-community/mathlib/commit/6e94c53)
feat(complex/basic): nnnorm coercions ([#12428](https://github.com/leanprover-community/mathlib/pull/12428))
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* nnnorm_real
- \+ *lemma* nnnorm_nat
- \+ *lemma* nnnorm_int
- \+ *lemma* nnnorm_eq_one_of_pow_eq_one
- \+ *lemma* norm_eq_one_of_pow_eq_one

modified src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root.nnnorm_eq_one



## [2022-03-04 15:24:34](https://github.com/leanprover-community/mathlib/commit/dc95d02)
feat(order/filter/archimedean): add lemmas about convergence to ±∞ for archimedean rings / groups. ([#12427](https://github.com/leanprover-community/mathlib/pull/12427))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
modified src/order/filter/archimedean.lean
- \+ *lemma* tendsto.const_mul_at_top'
- \+ *lemma* tendsto.at_top_mul_const'
- \+ *lemma* tendsto.at_top_mul_neg_const'
- \+ *lemma* tendsto.at_bot_mul_const'
- \+ *lemma* tendsto.at_bot_mul_neg_const'
- \+ *lemma* tendsto.at_top_nsmul_const
- \+ *lemma* tendsto.at_top_nsmul_neg_const
- \+ *lemma* tendsto.at_top_zsmul_const
- \+ *lemma* tendsto.at_top_zsmul_neg_const
- \+ *lemma* tendsto.at_bot_zsmul_const
- \+ *lemma* tendsto.at_bot_zsmul_neg_const
- \- *lemma* filter.tendsto.const_mul_at_top'
- \- *lemma* filter.tendsto.at_top_mul_const'

modified src/order/filter/at_top_bot.lean
- \+ *lemma* tendsto_at_top_iff_tends_to_neg_at_bot
- \+ *lemma* tendsto_at_bot_iff_tends_to_neg_at_top



## [2022-03-04 15:24:33](https://github.com/leanprover-community/mathlib/commit/e41303d)
feat(category_theory/limits/shapes): preserving (co)kernels ([#12419](https://github.com/leanprover-community/mathlib/pull/12419))
This is work towards showing that homology is a lax monoidal functor.
#### Estimated changes
modified src/category_theory/limits/is_limit.lean
- \+ *def* equiv_of_nat_iso_of_iso
- \+ *def* equiv_of_nat_iso_of_iso

modified src/category_theory/limits/preserves/shapes/equalizers.lean

created src/category_theory/limits/preserves/shapes/kernels.lean
- \+ *lemma* preserves_kernel.iso_hom
- \+ *lemma* preserves_cokernel.iso_hom
- \+ *def* is_limit_map_cone_fork_equiv'
- \+ *def* is_limit_fork_map_of_is_limit'
- \+ *def* is_limit_of_has_kernel_of_preserves_limit
- \+ *def* preserves_kernel.of_iso_comparison
- \+ *def* preserves_kernel.iso
- \+ *def* is_colimit_map_cocone_cofork_equiv'
- \+ *def* is_colimit_cofork_map_of_is_colimit'
- \+ *def* is_colimit_of_has_cokernel_of_preserves_colimit
- \+ *def* preserves_cokernel.of_iso_comparison
- \+ *def* preserves_cokernel.iso

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* parallel_pair.ext

modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_comparison_comp_π
- \+ *lemma* map_lift_kernel_comparison
- \+ *lemma* ι_comp_cokernel_comparison
- \+ *lemma* cokernel_comparison_map_desc
- \+ *def* kernel_is_kernel
- \+ *def* cokernel_is_cokernel
- \+ *def* kernel_comparison
- \+ *def* cokernel_comparison



## [2022-03-04 14:03:56](https://github.com/leanprover-community/mathlib/commit/2d6c52a)
feat(topology/metric_space/polish): definition and basic properties of polish spaces ([#12437](https://github.com/leanprover-community/mathlib/pull/12437))
A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this PR, we establish basic (and not so basic) properties of Polish spaces.
#### Estimated changes
modified src/topology/metric_space/isometry.lean
- \+ *lemma* uniform_embedding.to_isometry
- \+ *lemma* embedding.to_isometry

created src/topology/metric_space/polish.lean
- \+ *lemma* complete_polish_space_metric
- \+ *lemma* exists_nat_nat_continuous_surjective
- \+ *lemma* _root_.closed_embedding.polish_space
- \+ *lemma* _root_.equiv.polish_space_induced
- \+ *lemma* _root_.is_closed.polish_space
- \+ *lemma* exists_polish_space_forall_le
- \+ *lemma* dist_complete_copy_eq
- \+ *lemma* dist_le_dist_complete_copy
- \+ *lemma* complete_space_complete_copy
- \+ *lemma* _root_.is_open.polish_space
- \+ *lemma* _root_.is_closed.is_clopenable
- \+ *lemma* is_clopenable.compl
- \+ *lemma* _root_.is_open.is_clopenable
- \+ *lemma* is_clopenable.Union
- \+ *def* polish_space_metric
- \+ *def* upgrade_polish_space
- \+ *def* aux_copy
- \+ *def* complete_copy
- \+ *def* has_dist_complete_copy
- \+ *def* complete_copy_metric_space
- \+ *def* complete_copy_id_homeo
- \+ *def* is_clopenable



## [2022-03-04 14:03:54](https://github.com/leanprover-community/mathlib/commit/0a3d144)
chore(topology/algebra/uniform_mul_action): add `has_uniform_continuous_const_smul.op` ([#12434](https://github.com/leanprover-community/mathlib/pull/12434))
This matches `has_continuous_const_smul.op` and other similar lemmas.
With this in place, we can state `is_central_scalar` on `completion`s.
#### Estimated changes
modified src/topology/algebra/uniform_mul_action.lean



## [2022-03-04 14:03:53](https://github.com/leanprover-community/mathlib/commit/cac9242)
chore(analysis/complex/basic): golf `norm_rat/int/int_of_nonneg` ([#12433](https://github.com/leanprover-community/mathlib/pull/12433))
While looking at PR [#12428](https://github.com/leanprover-community/mathlib/pull/12428), I found some easy golfing of some lemmas (featuring my first-ever use of `single_pass`! :smile: ).
#### Estimated changes
modified src/analysis/complex/basic.lean



## [2022-03-04 14:03:51](https://github.com/leanprover-community/mathlib/commit/173f161)
feat(set_theory/ordinal_arithmetic): `bsup` / `blsub` of function composition ([#12381](https://github.com/leanprover-community/mathlib/pull/12381))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* bsup_comp
- \+ *theorem* blsub_comp



## [2022-03-04 12:39:06](https://github.com/leanprover-community/mathlib/commit/a721700)
chore(algebra/algebra/operations): add missing `@[elab_as_eliminator]` on recursors ([#12440](https://github.com/leanprover-community/mathlib/pull/12440))
`refine submodule.pow_induction_on' _ _ _ _ h` struggles without this attribute
#### Estimated changes
modified src/algebra/algebra/operations.lean

modified src/linear_algebra/exterior_algebra/grading.lean

modified src/linear_algebra/tensor_algebra/grading.lean



## [2022-03-04 12:39:04](https://github.com/leanprover-community/mathlib/commit/4a416bc)
feat(set_theory/ordinal_arithmetic): `is_normal.blsub_eq` ([#12379](https://github.com/leanprover-community/mathlib/pull/12379))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal.blsub_eq



## [2022-03-04 12:39:03](https://github.com/leanprover-community/mathlib/commit/b144460)
feat(number_theory/cyclotomic/primitive_roots): generalize norm_eq_one ([#12359](https://github.com/leanprover-community/mathlib/pull/12359))
We generalize `norm_eq_one`, that now computes the norm of any primitive `n`-th root of unity if `n ≠ 2`. We modify the assumption, that is still verified in the main case of interest `K = ℚ`.
From flt-regular
#### Estimated changes
modified src/number_theory/cyclotomic/discriminant.lean

modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* norm_eq_neg_one_pow
- \+/\- *lemma* norm_eq_one
- \+ *lemma* norm_eq_one_of_linearly_ordered
- \+ *lemma* norm_of_cyclotomic_irreducible
- \+ *lemma* sub_one_norm_prime_ne_two
- \+/\- *lemma* sub_one_norm_pow_two
- \+/\- *lemma* norm_zeta_eq_one
- \+/\- *lemma* norm_eq_one
- \- *lemma* prime_ne_two_pow_sub_one_norm
- \+/\- *lemma* sub_one_norm_pow_two
- \+/\- *lemma* norm_zeta_eq_one



## [2022-03-04 12:39:02](https://github.com/leanprover-community/mathlib/commit/53dc7ca)
feat(linear_algebra/basic): some basic lemmas about dfinsupp.sum ([#12214](https://github.com/leanprover-community/mathlib/pull/12214))
Two basic lemmas about dfinsupp.sum that could be useful (I needed them for another project)
#### Estimated changes
modified src/data/dfinsupp/basic.lean
- \+ *lemma* prod_eq_one
- \+ *lemma* smul_sum



## [2022-03-04 09:26:44](https://github.com/leanprover-community/mathlib/commit/052d027)
refactor(algebra/category/Group/basic): Avoid data shuffle in `mul_equiv.to_Group_iso` ([#12407](https://github.com/leanprover-community/mathlib/pull/12407))
Change the definition of `mul_equiv.to_Group_iso` from `{X Y : Type*} [group X] [group Y] (e : X ≃* Y) : Group.of X ≅ Group.of Y` to `{X Y : Group} (e : X ≃* Y) : X ≅ Y`. Not making `X` and `Y` into `Group`s on the fly avoids rebundling them when they already are `Group`s, which breaks definitional equality.
#### Estimated changes
modified src/algebra/category/Group/basic.lean
- \+/\- *def* mul_equiv.to_Group_iso
- \+/\- *def* mul_equiv.to_CommGroup_iso
- \+/\- *def* mul_equiv_iso_Group_iso
- \+/\- *def* mul_equiv_iso_CommGroup_iso
- \+/\- *def* mul_equiv.to_Group_iso
- \+/\- *def* mul_equiv.to_CommGroup_iso
- \+/\- *def* mul_equiv_iso_Group_iso
- \+/\- *def* mul_equiv_iso_CommGroup_iso



## [2022-03-04 09:26:43](https://github.com/leanprover-community/mathlib/commit/0666dd5)
feat(order/bounded): The universal set is unbounded ([#12390](https://github.com/leanprover-community/mathlib/pull/12390))
#### Estimated changes
modified src/order/bounded.lean
- \+ *theorem* unbounded_le_univ
- \+ *theorem* unbounded_lt_univ
- \+ *theorem* unbounded_ge_univ
- \+ *theorem* unbounded_gt_univ



## [2022-03-04 09:26:42](https://github.com/leanprover-community/mathlib/commit/09c66fa)
feat(counterexamples/seminorm_lattice_not_distrib): The lattice of seminorms is not distributive. ([#12099](https://github.com/leanprover-community/mathlib/pull/12099))
A counterexample showing the lattice of seminorms is not distributive
#### Estimated changes
created counterexamples/seminorm_lattice_not_distrib.lean
- \+ *lemma* eq_one
- \+ *lemma* not_distrib



## [2022-03-04 08:56:10](https://github.com/leanprover-community/mathlib/commit/82a142d)
feat(algebra/category): Module R is monoidal closed for comm_ring R ([#12387](https://github.com/leanprover-community/mathlib/pull/12387))
#### Estimated changes
modified src/algebra/category/Module/monoidal.lean
- \+ *def* monoidal_closed_hom_equiv



## [2022-03-04 07:06:13](https://github.com/leanprover-community/mathlib/commit/e96cf5e)
feat(data/nat/gcd): add coprime_prod_left and coprime_prod_right ([#12268](https://github.com/leanprover-community/mathlib/pull/12268))
#### Estimated changes
modified src/data/nat/gcd.lean
- \+ *lemma* coprime_prod_left
- \+ *lemma* coprime_prod_right



## [2022-03-03 23:56:18](https://github.com/leanprover-community/mathlib/commit/40524f1)
feat(algebra/star/self_adjoint): define normal elements of a star monoid ([#11991](https://github.com/leanprover-community/mathlib/pull/11991))
In this PR, we define the normal elements of a star monoid, i.e. those elements `x`
that commute with `star x`. This is defined as the prop type class `is_star_normal`.
This was formalized as part of the semilinear maps paper.
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+ *lemma* star_comm_self'
- \+ *lemma* is_star_normal_of_mem
- \+ *lemma* is_star_normal_of_mem



## [2022-03-03 23:15:44](https://github.com/leanprover-community/mathlib/commit/544f45b)
refactor(linear_algebra/bilinear_form): split off matrix part ([#12435](https://github.com/leanprover-community/mathlib/pull/12435))
The bilinear form file is way too large. The part that concerns matrices is not depended on by the general theory, and belongs in its own file.
#### Estimated changes
modified src/algebra/lie/skew_adjoint.lean

modified src/linear_algebra/bilinear_form.lean
- \- *lemma* matrix.to_bilin'_aux_std_basis
- \- *lemma* to_bilin'_aux_to_matrix_aux
- \- *lemma* bilin_form.to_matrix_aux_std_basis
- \- *lemma* matrix.to_bilin'_aux_eq
- \- *lemma* matrix.to_bilin'_apply
- \- *lemma* matrix.to_bilin'_apply'
- \- *lemma* matrix.to_bilin'_std_basis
- \- *lemma* bilin_form.to_matrix'_symm
- \- *lemma* matrix.to_bilin'_symm
- \- *lemma* matrix.to_bilin'_to_matrix'
- \- *lemma* bilin_form.to_matrix'_to_bilin'
- \- *lemma* bilin_form.to_matrix'_apply
- \- *lemma* bilin_form.to_matrix'_comp
- \- *lemma* bilin_form.to_matrix'_comp_left
- \- *lemma* bilin_form.to_matrix'_comp_right
- \- *lemma* bilin_form.mul_to_matrix'_mul
- \- *lemma* bilin_form.mul_to_matrix'
- \- *lemma* bilin_form.to_matrix'_mul
- \- *lemma* matrix.to_bilin'_comp
- \- *lemma* basis.equiv_fun_symm_std_basis
- \- *lemma* bilin_form.to_matrix_apply
- \- *lemma* matrix.to_bilin_apply
- \- *lemma* bilinear_form.to_matrix_aux_eq
- \- *lemma* bilin_form.to_matrix_symm
- \- *lemma* matrix.to_bilin_symm
- \- *lemma* matrix.to_bilin_basis_fun
- \- *lemma* bilin_form.to_matrix_basis_fun
- \- *lemma* matrix.to_bilin_to_matrix
- \- *lemma* bilin_form.to_matrix_to_bilin
- \- *lemma* bilin_form.to_matrix_comp
- \- *lemma* bilin_form.to_matrix_comp_left
- \- *lemma* bilin_form.to_matrix_comp_right
- \- *lemma* bilin_form.to_matrix_mul_basis_to_matrix
- \- *lemma* bilin_form.mul_to_matrix_mul
- \- *lemma* bilin_form.mul_to_matrix
- \- *lemma* bilin_form.to_matrix_mul
- \- *lemma* matrix.to_bilin_comp
- \- *lemma* is_adjoint_pair_to_bilin'
- \- *lemma* is_adjoint_pair_to_bilin
- \- *lemma* matrix.is_adjoint_pair_equiv
- \- *lemma* mem_pair_self_adjoint_matrices_submodule
- \- *lemma* mem_self_adjoint_matrices_submodule
- \- *lemma* mem_skew_adjoint_matrices_submodule
- \- *lemma* _root_.matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \- *lemma* _root_.matrix.nondegenerate_to_bilin'_iff
- \- *lemma* _root_.matrix.nondegenerate_to_bilin_iff
- \- *lemma* nondegenerate_to_bilin'_iff_det_ne_zero
- \- *lemma* nondegenerate_iff_det_ne_zero
- \- *theorem* _root_.matrix.nondegenerate.to_bilin'
- \- *theorem* _root_.matrix.nondegenerate.to_bilin
- \- *theorem* nondegenerate_to_matrix'_iff
- \- *theorem* nondegenerate.to_matrix'
- \- *theorem* nondegenerate_to_matrix_iff
- \- *theorem* nondegenerate.to_matrix
- \- *theorem* nondegenerate_to_bilin'_of_det_ne_zero'
- \- *theorem* nondegenerate_of_det_ne_zero
- \- *def* matrix.to_bilin'_aux
- \- *def* bilin_form.to_matrix_aux
- \- *def* bilin_form.to_matrix'
- \- *def* matrix.to_bilin'
- \- *def* matrix.is_adjoint_pair
- \- *def* matrix.is_self_adjoint
- \- *def* matrix.is_skew_adjoint
- \- *def* pair_self_adjoint_matrices_submodule
- \- *def* self_adjoint_matrices_submodule
- \- *def* skew_adjoint_matrices_submodule

created src/linear_algebra/matrix/bilinear_form.lean
- \+ *lemma* matrix.to_bilin'_aux_std_basis
- \+ *lemma* to_bilin'_aux_to_matrix_aux
- \+ *lemma* bilin_form.to_matrix_aux_std_basis
- \+ *lemma* matrix.to_bilin'_aux_eq
- \+ *lemma* matrix.to_bilin'_apply
- \+ *lemma* matrix.to_bilin'_apply'
- \+ *lemma* matrix.to_bilin'_std_basis
- \+ *lemma* bilin_form.to_matrix'_symm
- \+ *lemma* matrix.to_bilin'_symm
- \+ *lemma* matrix.to_bilin'_to_matrix'
- \+ *lemma* bilin_form.to_matrix'_to_bilin'
- \+ *lemma* bilin_form.to_matrix'_apply
- \+ *lemma* bilin_form.to_matrix'_comp
- \+ *lemma* bilin_form.to_matrix'_comp_left
- \+ *lemma* bilin_form.to_matrix'_comp_right
- \+ *lemma* bilin_form.mul_to_matrix'_mul
- \+ *lemma* bilin_form.mul_to_matrix'
- \+ *lemma* bilin_form.to_matrix'_mul
- \+ *lemma* matrix.to_bilin'_comp
- \+ *lemma* basis.equiv_fun_symm_std_basis
- \+ *lemma* bilin_form.to_matrix_apply
- \+ *lemma* matrix.to_bilin_apply
- \+ *lemma* bilinear_form.to_matrix_aux_eq
- \+ *lemma* bilin_form.to_matrix_symm
- \+ *lemma* matrix.to_bilin_symm
- \+ *lemma* matrix.to_bilin_basis_fun
- \+ *lemma* bilin_form.to_matrix_basis_fun
- \+ *lemma* matrix.to_bilin_to_matrix
- \+ *lemma* bilin_form.to_matrix_to_bilin
- \+ *lemma* bilin_form.to_matrix_comp
- \+ *lemma* bilin_form.to_matrix_comp_left
- \+ *lemma* bilin_form.to_matrix_comp_right
- \+ *lemma* bilin_form.to_matrix_mul_basis_to_matrix
- \+ *lemma* bilin_form.mul_to_matrix_mul
- \+ *lemma* bilin_form.mul_to_matrix
- \+ *lemma* bilin_form.to_matrix_mul
- \+ *lemma* matrix.to_bilin_comp
- \+ *lemma* is_adjoint_pair_to_bilin'
- \+ *lemma* is_adjoint_pair_to_bilin
- \+ *lemma* matrix.is_adjoint_pair_equiv
- \+ *lemma* mem_pair_self_adjoint_matrices_submodule
- \+ *lemma* mem_self_adjoint_matrices_submodule
- \+ *lemma* mem_skew_adjoint_matrices_submodule
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin'_iff
- \+ *lemma* _root_.matrix.nondegenerate_to_bilin_iff
- \+ *lemma* nondegenerate_to_bilin'_iff_det_ne_zero
- \+ *lemma* nondegenerate_iff_det_ne_zero
- \+ *theorem* _root_.matrix.nondegenerate.to_bilin'
- \+ *theorem* _root_.matrix.nondegenerate.to_bilin
- \+ *theorem* nondegenerate_to_matrix'_iff
- \+ *theorem* nondegenerate.to_matrix'
- \+ *theorem* nondegenerate_to_matrix_iff
- \+ *theorem* nondegenerate.to_matrix
- \+ *theorem* nondegenerate_to_bilin'_of_det_ne_zero'
- \+ *theorem* nondegenerate_of_det_ne_zero
- \+ *def* matrix.to_bilin'_aux
- \+ *def* bilin_form.to_matrix_aux
- \+ *def* bilin_form.to_matrix'
- \+ *def* matrix.to_bilin'
- \+ *def* matrix.is_adjoint_pair
- \+ *def* matrix.is_self_adjoint
- \+ *def* matrix.is_skew_adjoint
- \+ *def* pair_self_adjoint_matrices_submodule
- \+ *def* self_adjoint_matrices_submodule
- \+ *def* skew_adjoint_matrices_submodule

modified src/linear_algebra/quadratic_form/basic.lean

modified src/ring_theory/trace.lean



## [2022-03-03 21:32:01](https://github.com/leanprover-community/mathlib/commit/5371338)
feat(group_theory/torsion): all torsion monoids are groups ([#12432](https://github.com/leanprover-community/mathlib/pull/12432))
#### Estimated changes
modified src/group_theory/torsion.lean



## [2022-03-03 21:32:00](https://github.com/leanprover-community/mathlib/commit/1af53ff)
feat(polynomial/cyclotomic): some divisibility results ([#12426](https://github.com/leanprover-community/mathlib/pull/12426))
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* not_mem_sdiff_of_not_mem_left

modified src/data/polynomial/eval.lean
- \+ *lemma* map_dvd

modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic_dvd_geom_sum_of_dvd
- \+ *lemma* X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
- \+ *lemma* X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd



## [2022-03-03 21:31:59](https://github.com/leanprover-community/mathlib/commit/54c286d)
feat(data/{nat,int,rat}/cast, algebra/star/basic): lemmas about `star` on casts ([#12418](https://github.com/leanprover-community/mathlib/pull/12418))
This also includes lemmas about `mul_opposite` on casts which are used to prove the star lemmas. The new lemmas are:
* `star_nat_cast`
* `star_int_cast`
* `star_rat_cast`
* `op_nat_cast`
* `op_int_cast`
* `op_rat_cast`
* `unop_nat_cast`
* `unop_int_cast`
* `unop_rat_cast`
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* star_nat_cast
- \+ *lemma* star_int_cast
- \+ *lemma* star_rat_cast

modified src/data/int/cast.lean
- \+ *lemma* op_int_cast
- \+ *lemma* unop_int_cast

modified src/data/nat/cast.lean
- \+ *lemma* op_nat_cast
- \+ *lemma* unop_nat_cast

modified src/data/rat/cast.lean
- \+ *lemma* op_rat_cast
- \+ *lemma* unop_rat_cast



## [2022-03-03 21:31:57](https://github.com/leanprover-community/mathlib/commit/9deac65)
feat(ring_theory/ideal): more lemmas on ideals multiplied with submodules ([#12401](https://github.com/leanprover-community/mathlib/pull/12401))
These are, like [#12178](https://github.com/leanprover-community/mathlib/pull/12178), split off from [#12287](https://github.com/leanprover-community/mathlib/pull/12287)
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *lemma* mem_smul_span
- \+ *lemma* exists_sum_of_mem_ideal_smul_span
- \+ *lemma* smul_comap_le_comap_smul



## [2022-03-03 21:31:56](https://github.com/leanprover-community/mathlib/commit/2fc2d1b)
feat(linear_algebra/clifford_algebra): lemmas about mapping submodules ([#12399](https://github.com/leanprover-community/mathlib/pull/12399))
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* range_neg

modified src/linear_algebra/clifford_algebra/basic.lean
- \+ *lemma* ι_range_map_lift
- \+ *lemma* ι_range_map_map

modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *lemma* ι_range_map_involute
- \+ *lemma* ι_range_comap_involute
- \+ *lemma* ι_range_map_reverse
- \+ *lemma* ι_range_comap_reverse
- \+ *def* involute_equiv
- \+ *def* reverse_equiv



## [2022-03-03 21:31:55](https://github.com/leanprover-community/mathlib/commit/e84c1a9)
chore(linear_algebra/general_linear_group): replace coe_fn with coe in lemma statements ([#12397](https://github.com/leanprover-community/mathlib/pull/12397))
This way, all the lemmas are expressed in terms of `↑` and not `⇑`.
This matches the approach used in `special_linear_group`.
#### Estimated changes
modified src/linear_algebra/general_linear_group.lean
- \+ *lemma* GL_pos.coe_neg
- \+ *lemma* GL_pos.coe_neg_apply
- \+/\- *lemma* coe_fn_eq_coe
- \+/\- *lemma* coe_fn_eq_coe
- \- *lemma* GL_pos_coe_neg
- \- *lemma* GL_pos_neg_elt



## [2022-03-03 21:31:54](https://github.com/leanprover-community/mathlib/commit/4503732)
feat(field_theory/cardinality): cardinality of fields & localizations ([#12285](https://github.com/leanprover-community/mathlib/pull/12285))
#### Estimated changes
created src/field_theory/cardinality.lean
- \+ *lemma* fintype.is_prime_pow_card_of_field
- \+ *lemma* fintype.nonempty_field_iff
- \+ *lemma* fintype.not_is_field_of_card_not_prime_pow
- \+ *lemma* infinite.nonempty_field

modified src/ring_theory/localization/basic.lean
- \+ *def* unique_of_zero_mem

created src/ring_theory/localization/cardinality.lean
- \+ *lemma* algebra_map_surjective_of_fintype
- \+ *lemma* card_le
- \+ *lemma* card



## [2022-03-03 21:31:52](https://github.com/leanprover-community/mathlib/commit/2c0fa82)
feat(group_theory/free_product): the 🏓-lemma ([#12210](https://github.com/leanprover-community/mathlib/pull/12210))
The Ping-Pong-Lemma.
If a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the free product of the `H i`.
Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group; we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be generated by the images.
Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.
#### Estimated changes
modified src/group_theory/free_product.lean
- \+ *lemma* prod_empty
- \+ *lemma* to_list_ne_nil
- \+ *lemma* to_list_head'
- \+ *lemma* to_list_last'
- \+ *lemma* of_word
- \+ *lemma* singleton_head
- \+ *lemma* singleton_last
- \+ *lemma* prod_singleton
- \+ *lemma* append_head
- \+ *lemma* append_last
- \+ *lemma* append_prod
- \+ *lemma* replace_head_head
- \+ *lemma* mul_head_head
- \+ *lemma* mul_head_prod
- \+ *lemma* inv_prod
- \+ *lemma* inv_head
- \+ *lemma* inv_last
- \+ *lemma* lift_word_ping_pong
- \+ *lemma* lift_word_prod_nontrivial_of_other_i
- \+ *lemma* lift_word_prod_nontrivial_of_head_eq_last
- \+ *lemma* lift_word_prod_nontrivial_of_head_card
- \+ *lemma* lift_word_prod_nontrivial_of_not_empty
- \+ *lemma* empty_of_word_prod_eq_one
- \- *lemma* prod_nil
- \+ *theorem* lift_injective_of_ping_pong:
- \+ *def* to_list
- \+ *def* head
- \+ *def* last
- \+ *def* to_word
- \+ *def* prod
- \+ *def* replace_head
- \+ *def* mul_head
- \+ *def* inv



## [2022-03-03 21:31:51](https://github.com/leanprover-community/mathlib/commit/f549c10)
feat(set_theory/cardinal_divisibility): add lemmas about divisibility in the cardinals ([#12197](https://github.com/leanprover-community/mathlib/pull/12197))
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *lemma* omega_le_mul_iff

created src/set_theory/cardinal_divisibility.lean
- \+ *lemma* is_unit_iff
- \+ *lemma* dvd_of_le_of_omega_le
- \+ *lemma* prime_of_omega_le
- \+ *lemma* not_irreducible_of_omega_le
- \+ *lemma* nat_coe_dvd_iff
- \+ *lemma* nat_is_prime_iff
- \+ *lemma* is_prime_iff
- \+ *lemma* is_prime_pow_iff
- \+ *theorem* le_of_dvd

modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* mul_eq_max'



## [2022-03-03 21:31:50](https://github.com/leanprover-community/mathlib/commit/2a05bb3)
feat(ring_theory/witt_vector): classify 1d isocrystals ([#12041](https://github.com/leanprover-community/mathlib/pull/12041))
To show an application of semilinear maps that are not linear or conjugate-linear, we formalized the one-dimensional version of a theorem by Dieudonné and Manin classifying the isocrystals over an algebraically closed field with positive characteristic. This work is described in a recent draft from @dupuisf , @hrmacbeth , and myself: https://arxiv.org/abs/2202.05360
#### Estimated changes
modified docs/references.bib

modified src/linear_algebra/basic.lean
- \+/\- *def* smul_of_ne_zero
- \+/\- *def* smul_of_ne_zero

created src/ring_theory/witt_vector/frobenius_fraction_field.lean
- \+ *lemma* succ_nth_defining_poly_degree
- \+ *lemma* root_exists
- \+ *lemma* succ_nth_val_spec
- \+ *lemma* succ_nth_val_spec'
- \+ *lemma* solution_pow
- \+ *lemma* solution_spec
- \+ *lemma* solution_nonzero
- \+ *lemma* solution_spec'
- \+ *lemma* frobenius_rotation_nonzero
- \+ *lemma* frobenius_frobenius_rotation
- \+ *lemma* exists_frobenius_solution_fraction_ring
- \+ *def* succ_nth_defining_poly
- \+ *def* succ_nth_val
- \+ *def* solution
- \+ *def* frobenius_rotation

created src/ring_theory/witt_vector/isocrystal.lean
- \+ *lemma* standard_one_dim_isocrystal.frobenius_apply
- \+ *theorem* isocrystal_classification
- \+ *def* fraction_ring.frobenius
- \+ *def* fraction_ring.frobenius_ring_hom
- \+ *def* isocrystal.frobenius
- \+ *def* fraction_ring.module
- \+ *def* standard_one_dim_isocrystal



## [2022-03-03 19:28:04](https://github.com/leanprover-community/mathlib/commit/066ffdb)
chore(algebra/*): provide `non_assoc_ring` instances ([#12414](https://github.com/leanprover-community/mathlib/pull/12414))
#### Estimated changes
modified src/algebra/direct_sum/ring.lean

modified src/algebra/graded_monoid.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/symmetrized.lean



## [2022-03-03 19:28:03](https://github.com/leanprover-community/mathlib/commit/5d0960b)
feat(data/int/basic): add three lemmas about ints, nats and int_nat_abs ([#12380](https://github.com/leanprover-community/mathlib/pull/12380))
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/int.2Eto_nat_eq_zero)
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* coe_nat_nonpos_iff
- \+ *lemma* to_nat_neg_nat
- \+ *lemma* to_nat_eq_zero



## [2022-03-03 19:28:02](https://github.com/leanprover-community/mathlib/commit/cdb69d5)
fix(data/set/function): do not use reducible ([#12377](https://github.com/leanprover-community/mathlib/pull/12377))
Reducible should only be used if the definition if it occurs as an explicit argument in a type class and must reduce during type class search, or if it is a type that should inherit instances.  Propositions should only be reducible if they are trivial variants (`<` and `>` for example).
These reducible attributes here will cause issues in Lean 4.  In Lean 4, the simplifier unfold reducible definitions in simp lemmas.  This means that tagging an `inj_on`-theorem with `@[simp]` creates the simp lemma `?a = ?b` (i.e. match anything).
#### Estimated changes
modified src/data/set/function.lean
- \+/\- *def* maps_to
- \+/\- *def* inj_on
- \+/\- *def* surj_on
- \+/\- *def* bij_on
- \+/\- *def* left_inv_on
- \+/\- *def* inv_on
- \+/\- *def* maps_to
- \+/\- *def* inj_on
- \+/\- *def* surj_on
- \+/\- *def* bij_on
- \+/\- *def* left_inv_on
- \+/\- *def* inv_on

modified src/logic/function/basic.lean
- \+/\- *def* injective2
- \+/\- *def* injective2



## [2022-03-03 19:28:00](https://github.com/leanprover-community/mathlib/commit/363b7cd)
feat(algebra/ring/basic): generalize lemmas about differences of squares to non-commutative rings ([#12366](https://github.com/leanprover-community/mathlib/pull/12366))
This copies `mul_self_sub_mul_self` and `mul_self_eq_mul_self_iff` to the `commute` namespace, and reproves the existing lemmas in terms of the new commute lemmas.
As a result, the requirements on `mul_self_sub_one` and `mul_self_eq_one_iff` and `units.inv_eq_self_iff` can be weakened from `comm_ring` to `non_unital_non_assoc_ring` or `ring`.
This also replaces a few `is_domain`s with the weaker `no_zero_divisors`, since the lemmas are being moved anyway. In practice this just removes the nontriviality requirements.
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+ *lemma* mul_self_sub_mul_self_eq
- \+ *lemma* mul_self_sub_mul_self_eq'
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_sub_one
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_eq_one_iff
- \+/\- *lemma* units.inv_eq_self_iff
- \+/\- *lemma* mul_self_sub_one
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_eq_one_iff
- \+/\- *lemma* units.inv_eq_self_iff
- \+/\- *theorem* mul_self_sub_mul_self
- \+/\- *theorem* mul_self_sub_mul_self



## [2022-03-03 19:27:59](https://github.com/leanprover-community/mathlib/commit/e823109)
chore(algebra/{group,group_with_zero}/basic): rename `div_mul_div` and `div_mul_comm` ([#12365](https://github.com/leanprover-community/mathlib/pull/12365))
The new name, `div_mul_div_comm` is consistent with `mul_mul_mul_comm`.
Obviously this renames the additive versions too.
#### Estimated changes
modified src/algebra/big_operators/multiset.lean

modified src/algebra/group/basic.lean
- \+ *lemma* div_mul_div_comm
- \- *lemma* div_mul_comm

modified src/algebra/group/prod.lean

modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* div_mul_div_comm₀
- \- *lemma* div_mul_div

modified src/algebra/order/lattice_group.lean

modified src/analysis/box_integral/partition/additive.lean

modified src/analysis/mean_inequalities.lean

modified src/analysis/special_functions/polynomials.lean

modified src/analysis/special_functions/trigonometric/complex.lean

modified src/analysis/specific_limits.lean

modified src/data/nat/basic.lean
- \+ *lemma* div_mul_div_comm
- \- *lemma* div_mul_div

modified src/data/nat/prime.lean

modified src/deprecated/subfield.lean

modified src/field_theory/ratfunc.lean

modified src/field_theory/subfield.lean

modified src/linear_algebra/affine_space/affine_map.lean

modified src/measure_theory/integral/mean_inequalities.lean

modified src/number_theory/cyclotomic/discriminant.lean

modified src/number_theory/liouville/liouville_with.lean



## [2022-03-03 19:27:58](https://github.com/leanprover-community/mathlib/commit/ca7346d)
feat(combinatorics/simple_graph/connectivity): add walk.darts ([#12360](https://github.com/leanprover-community/mathlib/pull/12360))
Darts can be more convenient than edges when working with walks since they keep track of orientation. This adds the list of darts along a walk and uses this to define and prove things about edges along a walk.
#### Estimated changes
modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* dart.edge_comp_symm
- \+ *lemma* dart_edge_eq_mk_iff
- \+ *lemma* dart_edge_eq_mk_iff'
- \+ *def* dart_adj

modified src/combinatorics/simple_graph/connectivity.lean
- \+/\- *lemma* chain_adj_support
- \+ *lemma* chain'_adj_support
- \+ *lemma* chain_dart_adj_darts
- \+ *lemma* chain'_dart_adj_darts
- \+/\- *lemma* edges_subset_edge_set
- \+ *lemma* darts_nil
- \+ *lemma* darts_cons
- \+ *lemma* darts_append
- \+ *lemma* darts_reverse
- \+ *lemma* cons_map_snd_darts
- \+ *lemma* map_snd_darts
- \+ *lemma* map_fst_darts_append
- \+ *lemma* map_fst_darts
- \+ *lemma* length_darts
- \+/\- *lemma* length_edges
- \+ *lemma* dart_fst_mem_support_of_mem_darts
- \+ *lemma* dart_snd_mem_support_of_mem_darts
- \+/\- *lemma* mem_support_of_mem_edges
- \+ *lemma* darts_nodup_of_support_nodup
- \+ *lemma* darts_take_until_subset
- \+ *lemma* darts_drop_until_subset
- \+ *lemma* rotate_darts
- \+/\- *lemma* rotate_edges
- \+ *lemma* darts_bypass_subset
- \+/\- *lemma* edges_bypass_subset
- \+ *lemma* darts_to_path_subset
- \- *lemma* chain_adj_support_aux
- \+/\- *lemma* chain_adj_support
- \+/\- *lemma* edges_subset_edge_set
- \+/\- *lemma* length_edges
- \+/\- *lemma* mem_support_of_mem_edges
- \+/\- *lemma* rotate_edges
- \+/\- *lemma* edges_bypass_subset
- \+ *def* darts
- \+/\- *def* edges
- \+/\- *def* edges



## [2022-03-03 19:27:57](https://github.com/leanprover-community/mathlib/commit/3b0111b)
feat(field_theory/minpoly): add minpoly_add_algebra_map and minpoly_sub_algebra_map ([#12357](https://github.com/leanprover-community/mathlib/pull/12357))
We add minpoly_add_algebra_map and minpoly_sub_algebra_map: the minimal polynomial of x ± a.
From flt-regular
#### Estimated changes
modified src/data/polynomial/ring_division.lean
- \+ *lemma* monic.comp
- \+ *lemma* monic.comp_X_add_C
- \+ *lemma* monic.comp_X_sub_C

modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly_add_algebra_map
- \+ *lemma* minpoly_sub_algebra_map



## [2022-03-03 19:27:56](https://github.com/leanprover-community/mathlib/commit/301a266)
feat(number_theory/cyclotomic/primitive_roots): add is_primitive_root.sub_one_power_basis ([#12356](https://github.com/leanprover-community/mathlib/pull/12356))
We add `is_primitive_root.sub_one_power_basis`,  the power basis of a cyclotomic extension given by `ζ - 1`, where `ζ ` is a primitive root of unity.
From flt-regular.
#### Estimated changes
modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* power_basis_gen_mem_adjoin_zeta_sub_one

modified src/ring_theory/adjoin/power_basis.lean

modified src/ring_theory/power_basis.lean
- \+ *lemma* adjoin_gen_eq_top
- \+ *lemma* adjoin_eq_top_of_gen_mem_adjoin



## [2022-03-03 19:27:55](https://github.com/leanprover-community/mathlib/commit/78b323b)
feat(analysis/special_functions/trigonometric): inequality `tan x  > x` ([#12352](https://github.com/leanprover-community/mathlib/pull/12352))
#### Estimated changes
modified src/analysis/special_functions/trigonometric/arctan_deriv.lean

modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* sin_lt
- \- *lemma* sin_gt_sub_cube

created src/analysis/special_functions/trigonometric/bounds.lean
- \+ *lemma* sin_lt
- \+ *lemma* sin_gt_sub_cube
- \+ *lemma* deriv_tan_sub_id
- \+ *theorem* lt_tan

modified src/data/real/pi/bounds.lean



## [2022-03-03 19:27:53](https://github.com/leanprover-community/mathlib/commit/d0816c0)
feat(analysis/calculus): support and cont_diff ([#11976](https://github.com/leanprover-community/mathlib/pull/11976))
* Add some lemmas about the support of the (f)derivative of a function
* Add some equivalences for `cont_diff`
#### Estimated changes
modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff.continuous_deriv
- \+ *theorem* cont_diff_at_one_iff
- \+ *theorem* cont_diff_one_iff_fderiv
- \+ *theorem* cont_diff_one_iff_deriv
- \+ *theorem* cont_diff_top_iff_deriv

modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_eq
- \+ *lemma* support_deriv_subset
- \+ *lemma* has_compact_support.deriv

modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_eq
- \+ *lemma* support_fderiv_subset
- \+ *lemma* has_compact_support.fderiv

modified src/data/set/lattice.lean
- \+ *lemma* antitone_bforall



## [2022-03-03 17:48:13](https://github.com/leanprover-community/mathlib/commit/16d48d7)
feat(algebra/star/basic + analysis/normed_space/star/basic): add two eq_zero/ne_zero lemmas ([#12412](https://github.com/leanprover-community/mathlib/pull/12412))
Added two lemmas about elements being zero or non-zero.
Golf a proof.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+/\- *lemma* star_div
- \+ *lemma* star_eq_zero
- \+ *lemma* star_ne_zero
- \+/\- *lemma* star_div

modified src/analysis/normed_space/star/basic.lean



## [2022-03-03 17:48:12](https://github.com/leanprover-community/mathlib/commit/3fa09c2)
feat(algebra/homology/homotopy): compatibilities of null_homotopic_map with composition and additive functors ([#12392](https://github.com/leanprover-community/mathlib/pull/12392))
#### Estimated changes
modified src/algebra/homology/homotopy.lean
- \+ *lemma* null_homotopic_map_comp
- \+ *lemma* null_homotopic_map'_comp
- \+ *lemma* comp_null_homotopic_map
- \+ *lemma* comp_null_homotopic_map'
- \+ *lemma* map_null_homotopic_map
- \+ *lemma* map_null_homotopic_map'
- \+/\- *lemma* null_homotopic_map_f_eq_zero
- \+/\- *lemma* null_homotopic_map'_f_eq_zero
- \+/\- *lemma* null_homotopic_map_f_eq_zero
- \+/\- *lemma* null_homotopic_map'_f_eq_zero



## [2022-03-03 17:48:10](https://github.com/leanprover-community/mathlib/commit/0da2d1d)
feat(ring_theory/polynomial/eisenstein): add mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at ([#12371](https://github.com/leanprover-community/mathlib/pull/12371))
We add `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at`: let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of `B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `p ^ n • z ∈ adjoin R {B.gen}`, then `z ∈ adjoin R {B.gen}`. Together with `algebra.discr_mul_is_integral_mem_adjoin` this result often allows to compute the ring of integers of `L`.
From flt-regular
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* no_zero_smul_divisors.trans

modified src/data/finset/basic.lean
- \+ *lemma* disjoint_range_add_left_embedding
- \+ *lemma* disjoint_range_add_right_embedding

modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* mem_adjoin_of_dvd_coeff_of_dvd_aeval
- \+ *lemma* mem_adjoin_of_smul_prime_smul_of_minpoly_is_eiseinstein_at
- \+ *lemma* mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at



## [2022-03-03 17:48:08](https://github.com/leanprover-community/mathlib/commit/b0cf3d7)
feat(algebra/algebra/subalgebra): add a helper to promote submodules to subalgebras ([#12368](https://github.com/leanprover-community/mathlib/pull/12368))
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* mem_to_subalgebra
- \+ *lemma* coe_to_subalgebra
- \+ *lemma* to_subalgebra_mk
- \+ *lemma* to_subalgebra_to_submodule
- \+ *lemma* _root_.subalgebra.to_submodule_to_subalgebra
- \+ *def* to_subalgebra



## [2022-03-03 17:48:05](https://github.com/leanprover-community/mathlib/commit/ba998da)
feat(algebra/order/monoid_lemmas_zero_lt): more lemmas using `pos_mul` and friends ([#12355](https://github.com/leanprover-community/mathlib/pull/12355))
This PR continues the `order` refactor.  The added lemmas are the `\le` analogues of the `<` lemmas that are already present.
#### Estimated changes
modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* le_of_mul_le_mul_right'
- \+ *lemma* mul_le_mul_iff_left
- \+ *lemma* mul_le_mul_iff_right
- \+ *lemma* lt_of_mul_lt_mul_left''
- \+ *lemma* lt_of_mul_lt_mul_right''



## [2022-03-03 17:48:03](https://github.com/leanprover-community/mathlib/commit/5159a8f)
feat(simplex_category): various epi/mono lemmas ([#11924](https://github.com/leanprover-community/mathlib/pull/11924))
#### Estimated changes
modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* is_iso_of_bijective
- \+ *lemma* iso_eq_iso_refl
- \+ *lemma* eq_id_of_is_iso
- \+ *lemma* eq_σ_comp_of_not_injective'
- \+ *lemma* eq_σ_comp_of_not_injective
- \+ *lemma* eq_comp_δ_of_not_surjective'
- \+ *lemma* eq_comp_δ_of_not_surjective
- \+ *lemma* eq_id_of_mono
- \+ *lemma* eq_id_of_epi
- \+ *lemma* eq_σ_of_epi
- \+ *lemma* eq_δ_of_mono
- \+ *def* order_iso_of_iso

modified src/data/fin/basic.lean
- \+ *lemma* cast_succ_lt_iff_succ_le



## [2022-03-03 16:19:52](https://github.com/leanprover-community/mathlib/commit/f41897d)
feat(dynamics/fixed_points/basic): Fixed points are a subset of the range ([#12423](https://github.com/leanprover-community/mathlib/pull/12423))
#### Estimated changes
modified src/dynamics/fixed_points/basic.lean
- \+ *lemma* fixed_points_subset_range



## [2022-03-03 16:19:50](https://github.com/leanprover-community/mathlib/commit/4edf36d)
feat(data/nat/fib): sum of initial fragment of the Fibonacci sequence is one less than a Fibonacci number ([#12416](https://github.com/leanprover-community/mathlib/pull/12416))
#### Estimated changes
modified src/data/nat/fib.lean
- \+ *lemma* fib_succ_eq_succ_sum



## [2022-03-03 16:19:49](https://github.com/leanprover-community/mathlib/commit/59bf454)
refactor(measure_theory): enable dot notation for measure.map ([#12350](https://github.com/leanprover-community/mathlib/pull/12350))
Refactor to allow for using dot notation with `measure.map` (was previously not possible because it was bundled as a linear map). Mirrors `measure.restrict` wrapper implementation for `measure.restrictₗ`.
#### Estimated changes
modified src/measure_theory/constructions/prod.lean

modified src/measure_theory/group/measure.lean

modified src/measure_theory/measure/haar.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* mapₗ_apply
- \+ *lemma* map_add
- \+ *lemma* map_zero
- \+ *lemma* map_smul
- \+/\- *lemma* map_mono
- \+/\- *lemma* tendsto_ae_map
- \+/\- *lemma* ae_map_le
- \+/\- *lemma* mem_ae_of_mem_ae_map
- \+/\- *lemma* ae_of_ae_map
- \+/\- *lemma* map_comap
- \+/\- *lemma* ae_map_iff
- \+/\- *lemma* map_symm_map
- \+/\- *lemma* map_map_symm
- \+/\- *lemma* map_apply_eq_iff_map_symm_apply_eq
- \+/\- *lemma* restrict_map
- \+/\- *lemma* map_mono
- \+/\- *lemma* tendsto_ae_map
- \+/\- *lemma* ae_map_le
- \+/\- *lemma* mem_ae_of_mem_ae_map
- \+/\- *lemma* ae_of_ae_map
- \+/\- *lemma* map_comap
- \+/\- *lemma* ae_map_iff
- \+/\- *lemma* map_symm_map
- \+/\- *lemma* map_map_symm
- \+/\- *lemma* map_apply_eq_iff_map_symm_apply_eq
- \+/\- *lemma* restrict_map
- \+/\- *theorem* le_map_apply
- \+/\- *theorem* map_apply
- \+/\- *theorem* le_map_apply
- \+/\- *theorem* map_apply
- \+ *def* mapₗ
- \+/\- *def* map
- \+/\- *def* map



## [2022-03-03 16:19:48](https://github.com/leanprover-community/mathlib/commit/c504585)
fix(number_theory/number_field): make ring_of_integers_algebra not an instance ([#12331](https://github.com/leanprover-community/mathlib/pull/12331))
This issue has caused problems for at least two of Kevin's PhD students; it is better to remove it for now or disable it temporarily.
c.f. https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/diamond.20for.20monoid.20instance.20on.20ideals
#### Estimated changes
modified src/number_theory/number_field.lean
- \+ *def* ring_of_integers_algebra



## [2022-03-03 16:19:47](https://github.com/leanprover-community/mathlib/commit/0ac3f9d)
feat(category_theory/preadditive): the category of additive functors ([#12330](https://github.com/leanprover-community/mathlib/pull/12330))
#### Estimated changes
modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* AdditiveFunctor.of_fst
- \+ *lemma* AdditiveFunctor.forget_obj
- \+ *lemma* AdditiveFunctor.forget_obj_of
- \+ *lemma* AdditiveFunctor.forget_map
- \+ *def* AdditiveFunctor
- \+ *def* AdditiveFunctor.forget
- \+ *def* AdditiveFunctor.of



## [2022-03-03 16:19:46](https://github.com/leanprover-community/mathlib/commit/691722a)
feat(set_theory/ordinal): `enum` is injective ([#12319](https://github.com/leanprover-community/mathlib/pull/12319))
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* enum_inj



## [2022-03-03 16:19:45](https://github.com/leanprover-community/mathlib/commit/18f53db)
feat(topology/metric_space/pi_nat): metric structure on product spaces ([#12220](https://github.com/leanprover-community/mathlib/pull/12220))
We endow the spaces `Π (n : ℕ), E n` or `Π (i : ι), E i` with various distances (not registered as instances), and use these to show that these spaces retract on their closed subsets.
#### Estimated changes
created src/topology/metric_space/pi_nat.lean
- \+ *lemma* apply_first_diff_ne
- \+ *lemma* apply_eq_of_lt_first_diff
- \+ *lemma* first_diff_comm
- \+ *lemma* min_first_diff_le
- \+ *lemma* cylinder_eq_pi
- \+ *lemma* cylinder_zero
- \+ *lemma* cylinder_anti
- \+ *lemma* mem_cylinder_iff
- \+ *lemma* self_mem_cylinder
- \+ *lemma* mem_cylinder_iff_eq
- \+ *lemma* mem_cylinder_comm
- \+ *lemma* mem_cylinder_iff_le_first_diff
- \+ *lemma* mem_cylinder_first_diff
- \+ *lemma* cylinder_eq_cylinder_of_le_first_diff
- \+ *lemma* Union_cylinder_update
- \+ *lemma* update_mem_cylinder
- \+ *lemma* dist_eq_of_ne
- \+ *lemma* dist_triangle_nonarch
- \+ *lemma* mem_cylinder_iff_dist_le
- \+ *lemma* apply_eq_of_dist_lt
- \+ *lemma* lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder
- \+ *lemma* is_topological_basis_cylinders
- \+ *lemma* is_open_iff_dist
- \+ *lemma* exists_disjoint_cylinder
- \+ *lemma* first_diff_lt_shortest_prefix_diff
- \+ *lemma* shortest_prefix_diff_pos
- \+ *lemma* first_diff_le_longest_prefix
- \+ *lemma* inter_cylinder_longest_prefix_nonempty
- \+ *lemma* disjoint_cylinder_of_longest_prefix_lt
- \+ *lemma* cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff
- \+ *lemma* exists_nat_nat_continuous_surjective_of_complete_space
- \+ *lemma* dist_eq_tsum
- \+ *lemma* dist_summable
- \+ *lemma* min_dist_le_dist_pi
- \+ *lemma* dist_le_dist_pi_of_dist_lt
- \+ *theorem* exists_lipschitz_retraction_of_is_closed
- \+ *theorem* exists_retraction_of_is_closed
- \+ *theorem* exists_retraction_subtype_of_is_closed
- \+ *def* first_diff
- \+ *def* cylinder
- \+ *def* metric_space_nat_nat
- \+ *def* shortest_prefix_diff
- \+ *def* longest_prefix



## [2022-03-03 14:50:37](https://github.com/leanprover-community/mathlib/commit/8053f56)
feat(ring_theory/dedekind_domain): strengthen `exist_integer_multiples` ([#12184](https://github.com/leanprover-community/mathlib/pull/12184))
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K` to find a collection of elements of `A` that is not completely contained in `J`.
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal.exist_integer_multiples_not_mem

modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* span_finset_eq_zero
- \+ *lemma* span_finset_ne_zero
- \+ *def* span_finset



## [2022-03-03 14:50:36](https://github.com/leanprover-community/mathlib/commit/4dec7b5)
feat(ring_theory/ideal): `(I : ideal R) • (⊤ : submodule R M)` ([#12178](https://github.com/leanprover-community/mathlib/pull/12178))
Two useful lemmas on the submodule spanned by `I`-scalar multiples.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *lemma* map_le_smul_top
- \+ *lemma* smul_top_eq_map



## [2022-03-03 13:01:44](https://github.com/leanprover-community/mathlib/commit/26d9d38)
feat(number_theory): padic.complete_space instance ([#12424](https://github.com/leanprover-community/mathlib/pull/12424))
#### Estimated changes
modified src/number_theory/padics/padic_numbers.lean



## [2022-03-03 13:01:43](https://github.com/leanprover-community/mathlib/commit/bf203b9)
docs(set_theory/cofinality): Fix cofinality definition ([#12421](https://github.com/leanprover-community/mathlib/pull/12421))
The condition is `a ≤ b`, not `¬(b > a)`.
#### Estimated changes
modified src/set_theory/cofinality.lean



## [2022-03-03 13:01:42](https://github.com/leanprover-community/mathlib/commit/02cad2c)
feat(data/complex/basic): add abs_hom ([#12409](https://github.com/leanprover-community/mathlib/pull/12409))
#### Estimated changes
modified src/data/complex/basic.lean
- \+ *lemma* abs_prod



## [2022-03-03 13:01:40](https://github.com/leanprover-community/mathlib/commit/bc35902)
chore(algebra/group/hom): more generic `f x ≠ 1` lemmas ([#12404](https://github.com/leanprover-community/mathlib/pull/12404))
 * `map_ne_{one,zero}_iff` is the `not_congr` version of `map_eq_one_iff`, which was previously only available for `mul_equiv_class`
 * `ne_{one,zero}_of_map` is one direction of `map_ne_{one,zero}_iff` that doesn't assume injectivity
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* map_ne_one_iff
- \+ *lemma* ne_one_of_map

modified src/data/equiv/mul_add.lean



## [2022-03-03 13:01:39](https://github.com/leanprover-community/mathlib/commit/ca0ff3a)
feat(algebra/algebra/spectrum): show the star and spectrum operations commute ([#12351](https://github.com/leanprover-community/mathlib/pull/12351))
This establishes the identity `(σ a)⋆ = σ a⋆` for any `a : A` where `A` is a star ring and a star module over a star add monoid `R`.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \+ *lemma* star_mem_resolvent_set_iff



## [2022-03-03 13:01:38](https://github.com/leanprover-community/mathlib/commit/f7a6fe9)
feat(set_theory/cofinality): Prove simple theorems on regular cardinals ([#12328](https://github.com/leanprover-community/mathlib/pull/12328))
#### Estimated changes
modified src/set_theory/cofinality.lean
- \+ *lemma* is_regular.omega_le
- \+ *lemma* is_regular.cof_eq
- \+ *theorem* aleph'_succ_is_regular
- \+ *theorem* aleph_succ_is_regular



## [2022-03-03 11:09:23](https://github.com/leanprover-community/mathlib/commit/16ad25c)
chore(analysis/normed_space/star/basic): golf a proof ([#12420](https://github.com/leanprover-community/mathlib/pull/12420))
Shorten a proof using ext.
#### Estimated changes
modified src/analysis/normed_space/star/basic.lean



## [2022-03-03 11:09:21](https://github.com/leanprover-community/mathlib/commit/228ab96)
feat(data/list/destutter): add `list.destutter` to remove chained duplicates ([#11934](https://github.com/leanprover-community/mathlib/pull/11934))
#### Estimated changes
modified src/data/list/defs.lean
- \+ *def* destutter'
- \+ *def* destutter

created src/data/list/destutter.lean
- \+ *lemma* destutter'_nil
- \+ *lemma* destutter'_cons
- \+ *lemma* destutter'_cons_pos
- \+ *lemma* destutter'_cons_neg
- \+ *lemma* destutter'_singleton
- \+ *lemma* destutter'_sublist
- \+ *lemma* mem_destutter'
- \+ *lemma* destutter'_is_chain
- \+ *lemma* destutter'_is_chain'
- \+ *lemma* destutter'_of_chain
- \+ *lemma* destutter'_eq_self_iff
- \+ *lemma* destutter'_ne_nil
- \+ *lemma* destutter_nil
- \+ *lemma* destutter_cons'
- \+ *lemma* destutter_cons_cons
- \+ *lemma* destutter_singleton
- \+ *lemma* destutter_pair
- \+ *lemma* destutter_sublist
- \+ *lemma* destutter_is_chain'
- \+ *lemma* destutter_of_chain'
- \+ *lemma* destutter_eq_self_iff
- \+ *lemma* destutter_idem
- \+ *lemma* destutter_eq_nil



## [2022-03-03 09:29:13](https://github.com/leanprover-community/mathlib/commit/46b9d05)
feat(data/part): Lemmas for get on binary function instances ([#12194](https://github.com/leanprover-community/mathlib/pull/12194))
A variety of lemmas such as `mul_get_eq` for `part`.
#### Estimated changes
modified src/data/part.lean
- \+ *lemma* left_dom_of_mul_dom
- \+ *lemma* right_dom_of_mul_dom
- \+ *lemma* mul_get_eq
- \+ *lemma* left_dom_of_div_dom
- \+ *lemma* right_dom_of_div_dom
- \+ *lemma* div_get_eq
- \+ *lemma* left_dom_of_mod_dom
- \+ *lemma* right_dom_of_mod_dom
- \+ *lemma* mod_get_eq
- \+ *lemma* left_dom_of_append_dom
- \+ *lemma* right_dom_of_append_dom
- \+ *lemma* append_get_eq
- \+ *lemma* left_dom_of_inter_dom
- \+ *lemma* right_dom_of_inter_dom
- \+ *lemma* inter_get_eq
- \+ *lemma* left_dom_of_union_dom
- \+ *lemma* right_dom_of_union_dom
- \+ *lemma* union_get_eq
- \+ *lemma* left_dom_of_sdiff_dom
- \+ *lemma* right_dom_of_sdiff_dom
- \+ *lemma* sdiff_get_eq



## [2022-03-03 07:35:45](https://github.com/leanprover-community/mathlib/commit/9f721ba)
chore(logic/function/basic): add function.ne_iff ([#12288](https://github.com/leanprover-community/mathlib/pull/12288))
#### Estimated changes
modified src/data/fun_like/basic.lean
- \+ *lemma* ne_iff

modified src/logic/function/basic.lean
- \+/\- *lemma* funext_iff
- \+ *lemma* ne_iff
- \+/\- *lemma* funext_iff



## [2022-03-03 00:08:38](https://github.com/leanprover-community/mathlib/commit/9deeddb)
feat(algebra/algebra/operations): `submodule.map_pow` and opposite lemmas ([#12374](https://github.com/leanprover-community/mathlib/pull/12374))
To prove `map_pow`, we add `submodule.map_hom` to match the very-recently-added `ideal.map_hom`. 
The opposite lemmas can be used to extend these results for maps that reverse multiplication, by factoring them into an `alg_hom` into the opposite type composed with `mul_opposite.op`.
`(↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)` is really a mouthful, but the elaborator can't seem to work out the type any other way, and `.to_linear_map` appears not to be the preferred form for `simp` lemmas.
#### Estimated changes
modified src/algebra/algebra/operations.lean
- \+ *lemma* map_op_one
- \+ *lemma* comap_op_one
- \+ *lemma* map_unop_one
- \+ *lemma* comap_unop_one
- \+ *lemma* map_op_mul
- \+ *lemma* comap_unop_mul
- \+ *lemma* map_op_pow
- \+ *lemma* comap_unop_pow
- \- *lemma* map_mul
- \- *lemma* map_div
- \+ *def* map_hom
- \+ *def* equiv_opposite



## [2022-03-02 22:17:15](https://github.com/leanprover-community/mathlib/commit/6f74d3c)
chore(algebra/ring/basic): generalize lemmas to non-associative rings ([#12411](https://github.com/leanprover-community/mathlib/pull/12411))
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+/\- *lemma* mul_sub_left_distrib
- \+/\- *lemma* mul_sub_right_distrib
- \+/\- *lemma* mul_sub_left_distrib
- \+/\- *lemma* mul_sub_right_distrib
- \+/\- *theorem* mul_add_eq_mul_add_iff_sub_mul_add_eq
- \+/\- *theorem* sub_mul_add_eq_of_mul_add_eq_mul_add
- \+/\- *theorem* injective_iff
- \+/\- *theorem* injective_iff'
- \+/\- *theorem* mul_add_eq_mul_add_iff_sub_mul_add_eq
- \+/\- *theorem* sub_mul_add_eq_of_mul_add_eq_mul_add
- \+/\- *theorem* injective_iff
- \+/\- *theorem* injective_iff'
- \+/\- *def* mk'
- \+/\- *def* mk'



## [2022-03-02 21:08:47](https://github.com/leanprover-community/mathlib/commit/ce26d75)
refactor(analysis/normed_space/basic): split into normed_space and ../normed/normed_field ([#12410](https://github.com/leanprover-community/mathlib/pull/12410))
Splits off the sections about normed rings and fields of the file `analysis/normed_space/basic` into a new file `analysis/normed/normed_field`.
#### Estimated changes
created src/analysis/normed/normed_field.lean
- \+ *lemma* nnnorm_one
- \+ *lemma* norm_mul_le
- \+ *lemma* nnnorm_mul_le
- \+ *lemma* list.norm_prod_le'
- \+ *lemma* list.norm_prod_le
- \+ *lemma* finset.norm_prod_le'
- \+ *lemma* finset.norm_prod_le
- \+ *lemma* nnnorm_pow_le'
- \+ *lemma* nnnorm_pow_le
- \+ *lemma* norm_pow_le'
- \+ *lemma* norm_pow_le
- \+ *lemma* eventually_norm_pow_le
- \+ *lemma* mul_left_bound
- \+ *lemma* mul_right_bound
- \+ *lemma* norm_matrix_le_iff
- \+ *lemma* norm_matrix_lt_iff
- \+ *lemma* units.norm_pos
- \+ *lemma* norm_mul
- \+ *lemma* nnnorm_mul
- \+ *lemma* norm_pow
- \+ *lemma* nnnorm_pow
- \+ *lemma* norm_prod
- \+ *lemma* nnnorm_prod
- \+ *lemma* norm_div
- \+ *lemma* nnnorm_div
- \+ *lemma* norm_inv
- \+ *lemma* nnnorm_inv
- \+ *lemma* norm_zpow
- \+ *lemma* nnnorm_zpow
- \+ *lemma* exists_one_lt_norm
- \+ *lemma* exists_norm_lt_one
- \+ *lemma* exists_lt_norm
- \+ *lemma* exists_norm_lt
- \+ *lemma* punctured_nhds_ne_bot
- \+ *lemma* nhds_within_is_unit_ne_bot
- \+ *lemma* norm_of_nonneg
- \+ *lemma* norm_of_nonpos
- \+ *lemma* norm_coe_nat
- \+ *lemma* nnnorm_coe_nat
- \+ *lemma* norm_two
- \+ *lemma* nnnorm_two
- \+ *lemma* nnnorm_of_nonneg
- \+ *lemma* ennnorm_eq_of_real
- \+ *lemma* of_real_le_ennnorm
- \+ *lemma* norm_eq
- \+ *lemma* nnnorm_eq
- \+ *lemma* norm_norm
- \+ *lemma* nnnorm_norm
- \+ *lemma* normed_group.tendsto_at_top
- \+ *lemma* normed_group.tendsto_at_top'
- \+ *lemma* int.norm_cast_real
- \+ *lemma* int.norm_eq_abs
- \+ *lemma* nnreal.coe_nat_abs
- \+ *lemma* rat.norm_cast_real
- \+ *lemma* int.norm_cast_rat
- \+ *lemma* norm_nsmul_le
- \+ *lemma* norm_zsmul_le
- \+ *lemma* nnnorm_nsmul_le
- \+ *lemma* nnnorm_zsmul_le
- \+ *lemma* summable.mul_of_nonneg
- \+ *lemma* summable.mul_norm
- \+ *lemma* summable_mul_of_summable_norm
- \+ *lemma* tsum_mul_tsum_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_antidiagonal_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_range_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
- \+ *def* matrix.semi_normed_group
- \+ *def* matrix.normed_group
- \+ *def* norm_hom
- \+ *def* nnnorm_hom

modified src/analysis/normed_space/basic.lean
- \- *lemma* nnnorm_one
- \- *lemma* norm_mul_le
- \- *lemma* nnnorm_mul_le
- \- *lemma* list.norm_prod_le'
- \- *lemma* list.norm_prod_le
- \- *lemma* finset.norm_prod_le'
- \- *lemma* finset.norm_prod_le
- \- *lemma* nnnorm_pow_le'
- \- *lemma* nnnorm_pow_le
- \- *lemma* norm_pow_le'
- \- *lemma* norm_pow_le
- \- *lemma* eventually_norm_pow_le
- \- *lemma* mul_left_bound
- \- *lemma* mul_right_bound
- \- *lemma* norm_matrix_le_iff
- \- *lemma* norm_matrix_lt_iff
- \- *lemma* units.norm_pos
- \- *lemma* norm_mul
- \- *lemma* nnnorm_mul
- \- *lemma* norm_pow
- \- *lemma* nnnorm_pow
- \- *lemma* norm_prod
- \- *lemma* nnnorm_prod
- \- *lemma* norm_div
- \- *lemma* nnnorm_div
- \- *lemma* norm_inv
- \- *lemma* nnnorm_inv
- \- *lemma* norm_zpow
- \- *lemma* nnnorm_zpow
- \- *lemma* exists_one_lt_norm
- \- *lemma* exists_norm_lt_one
- \- *lemma* exists_lt_norm
- \- *lemma* exists_norm_lt
- \- *lemma* punctured_nhds_ne_bot
- \- *lemma* nhds_within_is_unit_ne_bot
- \- *lemma* norm_of_nonneg
- \- *lemma* norm_of_nonpos
- \- *lemma* norm_coe_nat
- \- *lemma* nnnorm_coe_nat
- \- *lemma* norm_two
- \- *lemma* nnnorm_two
- \- *lemma* nnnorm_of_nonneg
- \- *lemma* ennnorm_eq_of_real
- \- *lemma* of_real_le_ennnorm
- \- *lemma* norm_eq
- \- *lemma* nnnorm_eq
- \- *lemma* norm_norm
- \- *lemma* nnnorm_norm
- \- *lemma* normed_group.tendsto_at_top
- \- *lemma* normed_group.tendsto_at_top'
- \- *lemma* int.norm_cast_real
- \- *lemma* int.norm_eq_abs
- \- *lemma* nnreal.coe_nat_abs
- \- *lemma* rat.norm_cast_real
- \- *lemma* int.norm_cast_rat
- \- *lemma* norm_nsmul_le
- \- *lemma* norm_zsmul_le
- \- *lemma* nnnorm_nsmul_le
- \- *lemma* nnnorm_zsmul_le
- \- *lemma* summable.mul_of_nonneg
- \- *lemma* summable.mul_norm
- \- *lemma* summable_mul_of_summable_norm
- \- *lemma* tsum_mul_tsum_of_summable_norm
- \- *lemma* summable_norm_sum_mul_antidiagonal_of_summable_norm
- \- *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
- \- *lemma* summable_norm_sum_mul_range_of_summable_norm
- \- *lemma* tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
- \- *def* matrix.semi_normed_group
- \- *def* matrix.normed_group
- \- *def* norm_hom
- \- *def* nnnorm_hom



## [2022-03-02 20:03:20](https://github.com/leanprover-community/mathlib/commit/423328e)
chore(probability/independence): change to set notation and `measurable_set` ([#12400](https://github.com/leanprover-community/mathlib/pull/12400))
#### Estimated changes
modified src/measure_theory/measurable_space_def.lean

modified src/probability/independence.lean



## [2022-03-02 18:33:51](https://github.com/leanprover-community/mathlib/commit/a283e17)
feat(algebra/module/submodule_pointwise): pointwise negation ([#12405](https://github.com/leanprover-community/mathlib/pull/12405))
We already have pointwise negation on `add_submonoid`s (from [#10451](https://github.com/leanprover-community/mathlib/pull/10451)), this extends it to `submodules`.
The lemmas are all copies of the add_submonoid lemmas, except for two new lemmas:
* `submodule.neg_to_add_submonoid`
* `submodule.neg_eq_self`, which isn't true for `add_submonoid`s
Finally, we provide a `has_distrib_neg` instance; even though the negation is not cancellative, it does distribute over multiplication as expected.
#### Estimated changes
modified src/algebra/algebra/operations.lean

modified src/algebra/module/submodule_pointwise.lean
- \+ *lemma* coe_set_neg
- \+ *lemma* neg_to_add_submonoid
- \+ *lemma* mem_neg
- \+ *lemma* neg_le_neg
- \+ *lemma* neg_le
- \+ *lemma* closure_neg
- \+ *lemma* neg_inf
- \+ *lemma* neg_sup
- \+ *lemma* neg_bot
- \+ *lemma* neg_top
- \+ *lemma* neg_infi
- \+ *lemma* neg_supr
- \+ *lemma* neg_eq_self
- \+ *def* neg_order_iso



## [2022-03-02 17:49:08](https://github.com/leanprover-community/mathlib/commit/90e2957)
chore(measure_theory/function/egorov): rename `uniform_integrability` file to `egorov` ([#12402](https://github.com/leanprover-community/mathlib/pull/12402))
#### Estimated changes
modified src/measure_theory/function/convergence_in_measure.lean

renamed src/measure_theory/function/uniform_integrable.lean to src/measure_theory/function/egorov.lean



## [2022-03-02 14:31:45](https://github.com/leanprover-community/mathlib/commit/7959d98)
feat(linear_algebra/matrix.determinant): add `matrix.det_neg` ([#12396](https://github.com/leanprover-community/mathlib/pull/12396))
#### Estimated changes
modified src/linear_algebra/general_linear_group.lean

modified src/linear_algebra/matrix/determinant.lean
- \+/\- *lemma* det_smul
- \+ *lemma* det_smul_of_tower
- \+ *lemma* det_neg
- \+ *lemma* det_neg_eq_smul
- \+/\- *lemma* det_smul



## [2022-03-02 14:31:43](https://github.com/leanprover-community/mathlib/commit/c96fb62)
refactor(group_theory/*): Rename `general_commutator.lean` to `commutator.lean` ([#12388](https://github.com/leanprover-community/mathlib/pull/12388))
Followup to [#12308](https://github.com/leanprover-community/mathlib/pull/12308).
#### Estimated changes
modified src/group_theory/abelianization.lean

renamed src/group_theory/general_commutator.lean to src/group_theory/commutator.lean

modified src/group_theory/nilpotent.lean

modified src/group_theory/solvable.lean



## [2022-03-02 14:31:41](https://github.com/leanprover-community/mathlib/commit/d00cbee)
feat(algebra/big_operators/basic): prod_dvd_prod_of_subset ([#12383](https://github.com/leanprover-community/mathlib/pull/12383))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_dvd_prod_of_subset



## [2022-03-02 14:31:40](https://github.com/leanprover-community/mathlib/commit/22ddf9a)
feat(ring_theory/ideal): `map f (I^n) = (map f I)^n` ([#12370](https://github.com/leanprover-community/mathlib/pull/12370))
#### Estimated changes
modified src/ring_theory/ideal/operations.lean
- \+ *def* map_hom



## [2022-03-02 12:52:29](https://github.com/leanprover-community/mathlib/commit/4e8d8f2)
feat(ring_theory/unique_factorization_domain): factors of `p^k` ([#12369](https://github.com/leanprover-community/mathlib/pull/12369))
This is a relatively trivial application of existing lemmas, but the result is a particularly nice shape that I felt worth to add to the library.
#### Estimated changes
modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* _root_.irreducible.normalized_factors_pow



## [2022-03-02 12:52:28](https://github.com/leanprover-community/mathlib/commit/f191f52)
chore(algebra/big_operators): generalize `map_prod` to `monoid_hom_class` ([#12354](https://github.com/leanprover-community/mathlib/pull/12354))
This PR generalizes the following lemmas to `(add_)monoid_hom_class`:
 * `map_prod`, `map_sum`
 * `map_multiset_prod`, `map_multiset_sum`
 * `map_list_prod`, `map_list_sum`
 * `map_finsupp_prod`, `map_finsupp_sum`
I haven't removed any of the existing specialized, namespaced versions of these lemmas yet, but I have marked them as `protected` and added a docstring saying to use the generic version instead.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* map_prod
- \- *lemma* monoid_hom.map_prod
- \- *lemma* mul_equiv.map_prod
- \- *lemma* ring_hom.map_list_prod
- \- *lemma* ring_hom.map_list_sum
- \- *lemma* ring_hom.unop_map_list_prod
- \- *lemma* ring_hom.map_multiset_prod
- \- *lemma* ring_hom.map_multiset_sum
- \- *lemma* ring_hom.map_prod
- \- *lemma* ring_hom.map_sum

modified src/algebra/big_operators/multiset.lean
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_hom'
- \+ *lemma* map_multiset_prod
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_hom'
- \- *lemma* monoid_hom.map_multiset_prod

modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* multiset_prod_X_sub_C_next_coeff
- \+/\- *lemma* prod_X_sub_C_next_coeff
- \+/\- *lemma* multiset_prod_X_sub_C_next_coeff
- \+/\- *lemma* prod_X_sub_C_next_coeff

modified src/data/finsupp/basic.lean
- \+ *lemma* map_finsupp_prod
- \- *lemma* mul_equiv.map_finsupp_prod
- \- *lemma* monoid_hom.map_finsupp_prod
- \- *lemma* ring_hom.map_finsupp_sum
- \- *lemma* ring_hom.map_finsupp_prod

modified src/data/list/big_operators.lean
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_map_hom
- \+/\- *lemma* map_list_prod
- \+/\- *lemma* unop_map_list_prod
- \+/\- *lemma* prod_hom
- \+/\- *lemma* prod_map_hom
- \+/\- *lemma* map_list_prod
- \+/\- *lemma* unop_map_list_prod

modified src/data/polynomial/eval.lean
- \- *lemma* map_sum
- \- *lemma* map_multiset_prod
- \- *lemma* map_prod

modified src/field_theory/splitting_field.lean

modified src/order/filter/basic.lean
- \- *lemma* map_prod

modified src/ring_theory/polynomial/cyclotomic/basic.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/topology/list.lean



## [2022-03-02 10:22:02](https://github.com/leanprover-community/mathlib/commit/20d9541)
chore(ring_theory/localization): `localization_map_bijective` rename & `field` instance version ([#12375](https://github.com/leanprover-community/mathlib/pull/12375))
#### Estimated changes
modified src/ring_theory/jacobson.lean

modified src/ring_theory/localization/basic.lean
- \+ *lemma* is_field.localization_map_bijective
- \+ *lemma* field.localization_map_bijective
- \- *lemma* localization_map_bijective_of_field



## [2022-03-02 09:30:27](https://github.com/leanprover-community/mathlib/commit/35086a1)
feat(probability): define conditional probability and add basic related theorems ([#12344](https://github.com/leanprover-community/mathlib/pull/12344))
Add the definition of conditional probability as a scaled restricted measure and prove Bayes' Theorem and other basic theorems.
#### Estimated changes
modified src/measure_theory/measure/outer_measure.lean
- \+ *lemma* pos_of_subset_ne_zero

created src/probability/conditional.lean
- \+ *lemma* cond_is_probability_measure
- \+ *lemma* cond_univ
- \+ *lemma* cond_apply
- \+ *lemma* inter_pos_of_cond_ne_zero
- \+ *lemma* cond_pos_of_inter_ne_zero
- \+ *lemma* cond_cond_eq_cond_inter
- \+ *lemma* cond_mul_eq_inter
- \+ *theorem* cond_eq_inv_mul_cond_mul
- \+ *def* cond



## [2022-03-02 07:46:20](https://github.com/leanprover-community/mathlib/commit/1eebec5)
perf(data/fintype/basic): speed up mem_of_mem_perms_of_list ([#12389](https://github.com/leanprover-community/mathlib/pull/12389))
This single theorem was taking twice as long as everything else in the file put together, and it was easy to fix.
#### Estimated changes
modified src/data/fintype/basic.lean



## [2022-03-02 07:46:19](https://github.com/leanprover-community/mathlib/commit/9daa233)
doc(*): fix broken markdown links ([#12385](https://github.com/leanprover-community/mathlib/pull/12385))
Some urls to nLab were also weird, so I replaced it with less weird ones.
The `MM91` reference was presumably intended to reference `MM92`.
#### Estimated changes
modified src/algebra/group/freiman.lean

modified src/category_theory/category/PartialFun.lean

modified src/category_theory/category/Twop.lean

modified src/category_theory/sites/grothendieck.lean

modified src/category_theory/sites/pretopology.lean

modified src/category_theory/sites/spaces.lean

modified src/data/nat/sqrt.lean

modified src/data/two_pointing.lean

modified src/order/category/DistribLattice.lean

modified src/order/category/Lattice.lean

modified src/order/complete_boolean_algebra.lean



## [2022-03-02 07:46:18](https://github.com/leanprover-community/mathlib/commit/b77ff23)
feat(algebra/ring): add non-unital and non-associative rings ([#12300](https://github.com/leanprover-community/mathlib/pull/12300))
Following up on [#11124](https://github.com/leanprover-community/mathlib/pull/11124).
The longer term goal is to develop C^* algebras, where non-unital algebras are an essential part of the theory.
#### Estimated changes
modified src/algebra/ring/basic.lean

modified src/algebra/ring/opposite.lean

modified src/algebra/ring/pi.lean

modified src/algebra/ring/prod.lean

modified src/algebra/ring/ulift.lean

modified src/algebraic_geometry/prime_spectrum/basic.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/finsupp/pointwise.lean

modified src/data/zmod/basic.lean

modified src/field_theory/finite/basic.lean

modified src/field_theory/splitting_field.lean

modified src/number_theory/padics/padic_integers.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/witt_vector/discrete_valuation_ring.lean



## [2022-03-02 06:23:49](https://github.com/leanprover-community/mathlib/commit/fefe359)
feat(set_theory/principal): prove theorems about additive principal ordinals ([#11704](https://github.com/leanprover-community/mathlib/pull/11704))
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* ord_is_principal_add
- \+ *theorem* aleph_is_principal_add

modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* add_omega
- \- *theorem* add_lt_omega
- \- *theorem* add_omega_opow
- \- *theorem* add_lt_omega_opow
- \- *theorem* add_absorp
- \- *theorem* add_absorp_iff

modified src/set_theory/ordinal_notation.lean

modified src/set_theory/principal.lean
- \+ *theorem* principal_add_one
- \+ *theorem* principal_add_of_le_one
- \+ *theorem* principal_add_is_limit
- \+ *theorem* principal_add_iff_add_left_eq_self
- \+ *theorem* add_omega
- \+ *theorem* principal_add_omega
- \+ *theorem* add_omega_opow
- \+ *theorem* principal_add_omega_opow
- \+ *theorem* principal_add_iff_zero_or_omega_power
- \+ *theorem* add_absorp
- \+ *theorem* mul_principal_add_is_principal_add
- \+ *theorem* opow_principal_add_is_principal_add



## [2022-03-02 04:09:19](https://github.com/leanprover-community/mathlib/commit/a9902d5)
feat(algebra/divisibility): generalise basic facts to semigroups ([#12325](https://github.com/leanprover-community/mathlib/pull/12325))
#### Estimated changes
modified src/algebra/divisibility.lean
- \+/\- *lemma* dvd_rfl
- \+/\- *lemma* dvd_rfl
- \+/\- *theorem* dvd_refl
- \+/\- *theorem* one_dvd
- \+/\- *theorem* dvd_of_mul_left_dvd
- \+/\- *theorem* dvd_refl
- \+/\- *theorem* one_dvd
- \+/\- *theorem* dvd_of_mul_left_dvd

modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right

modified src/number_theory/padics/ring_homs.lean



## [2022-03-02 02:44:42](https://github.com/leanprover-community/mathlib/commit/cc9de07)
feat(algebra/star): replace star_monoid with star_semigroup ([#12299](https://github.com/leanprover-community/mathlib/pull/12299))
In preparation for allowing non-unital C^* algebras, replace star_monoid with star_semigroup.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+/\- *lemma* star_mul'
- \+/\- *lemma* star_one
- \+/\- *lemma* star_pow
- \+/\- *lemma* star_inv
- \+/\- *lemma* star_zpow
- \+/\- *lemma* star_div
- \+/\- *lemma* star_prod
- \+/\- *lemma* star_mul_self_nonneg
- \+/\- *lemma* star_mul_self_nonneg'
- \+/\- *lemma* is_unit.star
- \+/\- *lemma* is_unit_star
- \+/\- *lemma* star_inv_of
- \+/\- *lemma* star_mul'
- \+/\- *lemma* star_one
- \+/\- *lemma* star_pow
- \+/\- *lemma* star_inv
- \+/\- *lemma* star_zpow
- \+/\- *lemma* star_div
- \+/\- *lemma* star_prod
- \+/\- *lemma* star_mul_self_nonneg
- \+/\- *lemma* star_mul_self_nonneg'
- \+/\- *lemma* is_unit.star
- \+/\- *lemma* is_unit_star
- \+/\- *lemma* star_inv_of
- \+/\- *def* star_mul_equiv
- \+/\- *def* star_mul_aut
- \+ *def* star_semigroup_of_comm
- \+/\- *def* star_ring_equiv
- \+/\- *def* star_mul_equiv
- \+/\- *def* star_mul_aut
- \- *def* star_monoid_of_comm
- \+/\- *def* star_ring_equiv

modified src/algebra/star/chsh.lean

modified src/algebra/star/free.lean

modified src/algebra/star/module.lean

modified src/algebra/star/pi.lean

modified src/algebra/star/pointwise.lean

modified src/algebra/star/unitary.lean
- \+/\- *def* unitary
- \+/\- *def* unitary

modified src/analysis/inner_product_space/adjoint.lean

modified src/data/matrix/basic.lean
- \+/\- *lemma* conj_transpose_smul
- \+/\- *lemma* conj_transpose_smul



## [2022-03-01 23:58:42](https://github.com/leanprover-community/mathlib/commit/4ba9098)
feat(algebra/euclidean_domain,data/int/basic): dvd_div_of_mul_dvd ([#12382](https://github.com/leanprover-community/mathlib/pull/12382))
We have a separate `int` and `euclidean_domain` version as `euclidean_domain` isn't pulled in by `int.basic`.
#### Estimated changes
modified src/algebra/euclidean_domain.lean
- \+ *lemma* dvd_div_of_mul_dvd

modified src/data/int/basic.lean
- \+ *lemma* div_dvd_of_dvd
- \+ *lemma* dvd_div_of_mul_dvd
- \- *lemma* div_dvd_of_ne_zero_dvd



## [2022-03-01 22:20:43](https://github.com/leanprover-community/mathlib/commit/269280a)
feat(topology/bornology/basic): Define bornology ([#12036](https://github.com/leanprover-community/mathlib/pull/12036))
This defines bornologies and provides the basic API. A bornology on a type is a filter consisting of cobounded sets which contains the cofinite sets; bounded sets are then complements of cobounded sets. This is equivalent to the usual formulation in terms of bounded sets, but provides access to mathlib's large filter library. We provide the relevant API for bounded sets.
#### Estimated changes
modified docs/references.bib

created src/topology/bornology/basic.lean
- \+ *lemma* is_cobounded_def
- \+ *lemma* is_bounded_def
- \+ *lemma* is_bounded_compl_iff
- \+ *lemma* is_bounded_empty
- \+ *lemma* is_bounded.union
- \+ *lemma* is_bounded.subset
- \+ *lemma* sUnion_bounded_univ
- \+ *lemma* ext_iff'
- \+ *lemma* ext_iff_is_bounded
- \+ *lemma* is_bounded_sUnion
- \+ *lemma* is_bounded_bUnion
- \+ *lemma* is_bounded_Union
- \+ *def* bornology.of_bounded
- \+ *def* is_cobounded
- \+ *def* is_bounded
- \+ *def* bornology.cofinite



## [2022-03-01 20:54:12](https://github.com/leanprover-community/mathlib/commit/5c2fa35)
chore(topology/algebra/valuation): add universe ([#11962](https://github.com/leanprover-community/mathlib/pull/11962))
#### Estimated changes
modified src/topology/algebra/valuation.lean
- \+/\- *lemma* subgroups_basis
- \+/\- *lemma* loc_const
- \+/\- *lemma* subgroups_basis
- \+/\- *lemma* loc_const

modified src/topology/algebra/valued_field.lean
- \+/\- *lemma* valued.continuous_valuation
- \+/\- *lemma* valued.continuous_extension
- \+/\- *lemma* valued.extension_extends
- \+/\- *lemma* valued.continuous_valuation
- \+/\- *lemma* valued.continuous_extension
- \+/\- *lemma* valued.extension_extends



## [2022-03-01 19:12:01](https://github.com/leanprover-community/mathlib/commit/818c81f)
feat(ring_theory/integral_domain): finite integral domain is a field ([#12376](https://github.com/leanprover-community/mathlib/pull/12376))
We don't yet have Wedderburn's little theorem (on my todo list), so adding some weaker versions to tide us over.
#### Estimated changes
modified src/ring_theory/integral_domain.lean
- \+ *lemma* fintype.is_field_of_domain
- \+ *def* fintype.group_with_zero_of_cancel
- \+ *def* fintype.division_ring_of_is_domain
- \+ *def* fintype.field_of_domain
- \- *def* group_with_zero_of_fintype
- \- *def* division_ring_of_is_domain



## [2022-03-01 19:11:59](https://github.com/leanprover-community/mathlib/commit/130e07d)
chore(algebra/group/prod): `prod.swap` commutes with arithmetic ([#12367](https://github.com/leanprover-community/mathlib/pull/12367))
This also adds some missing `div` lemmas using `to_additive`.
#### Estimated changes
modified src/algebra/group/prod.lean
- \+ *lemma* swap_mul
- \+ *lemma* swap_one
- \+ *lemma* swap_inv
- \+ *lemma* fst_div
- \+ *lemma* snd_div
- \+ *lemma* mk_div_mk
- \+ *lemma* swap_div
- \- *lemma* fst_sub
- \- *lemma* snd_sub
- \- *lemma* mk_sub_mk

modified src/group_theory/group_action/prod.lean
- \+ *theorem* smul_swap



## [2022-03-01 17:25:51](https://github.com/leanprover-community/mathlib/commit/5e36e12)
feat(category_theory/abelian/homology): Adds API for homology mimicking that of (co)kernels. ([#12171](https://github.com/leanprover-community/mathlib/pull/12171))
#### Estimated changes
created src/category_theory/abelian/homology.lean
- \+ *lemma* π'_desc'
- \+ *lemma* lift_ι
- \+ *lemma* condition_π'
- \+ *lemma* condition_ι
- \+ *lemma* hom_from_ext
- \+ *lemma* hom_to_ext
- \+ *lemma* π'_ι
- \+ *lemma* π'_eq_π
- \+ *lemma* π'_map
- \+ *lemma* map_eq_desc'_lift_left
- \+ *lemma* map_eq_lift_desc'_left
- \+ *lemma* map_eq_desc'_lift_right
- \+ *lemma* map_eq_lift_desc'_right
- \+ *def* homology_iso_kernel_desc
- \+ *def* π'
- \+ *def* ι
- \+ *def* desc'
- \+ *def* lift

modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel_iso_of_eq_hom_comp_ι
- \+ *lemma* kernel_iso_of_eq_inv_comp_ι
- \+ *lemma* lift_comp_kernel_iso_of_eq_hom
- \+ *lemma* lift_comp_kernel_iso_of_eq_inv
- \+ *lemma* π_comp_cokernel_iso_of_eq_hom
- \+ *lemma* π_comp_cokernel_iso_of_eq_inv
- \+ *lemma* cokernel_iso_of_eq_hom_comp_desc
- \+ *lemma* cokernel_iso_of_eq_inv_comp_desc



## [2022-03-01 17:25:49](https://github.com/leanprover-community/mathlib/commit/b45657f)
feat(algebra/algebra/spectrum, analysis/normed_space/spectrum): prove the spectrum of any element in a complex Banach algebra is nonempty ([#12115](https://github.com/leanprover-community/mathlib/pull/12115))
This establishes that the spectrum of any element in a (nontrivial) complex Banach algebra is nonempty. The nontrivial assumption is necessary, as otherwise the only element is invertible. In addition, we establish some properties of the resolvent function; in particular, it tends to zero at infinity.
- [x] depends on: [#12095](https://github.com/leanprover-community/mathlib/pull/12095)
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *lemma* units_smul_resolvent
- \+ *lemma* units_smul_resolvent_self
- \+ *lemma* is_unit_resolvent
- \+/\- *lemma* is_unit.smul_sub_iff_sub_inv_smul

modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* norm_resolvent_le_forall
- \+ *theorem* nonempty



## [2022-03-01 17:25:48](https://github.com/leanprover-community/mathlib/commit/29c84f7)
feat(combinatorics/set_family/lym): Lubell-Yamamoto-Meshalkin inequalities ([#11248](https://github.com/leanprover-community/mathlib/pull/11248))
This proves the two local LYM inequalities, the LYM inequality and Sperner's theorem.
#### Estimated changes
created src/combinatorics/set_family/lym.lean
- \+ *lemma* card_mul_le_card_shadow_mul
- \+ *lemma* card_div_choose_le_card_shadow_div_choose
- \+ *lemma* mem_falling
- \+ *lemma* sized_falling
- \+ *lemma* slice_subset_falling
- \+ *lemma* falling_zero_subset
- \+ *lemma* slice_union_shadow_falling_succ
- \+ *lemma* _root_.is_antichain.disjoint_slice_shadow_falling
- \+ *lemma* le_card_falling_div_choose
- \+ *lemma* sum_card_slice_div_choose_le_one
- \+ *lemma* _root_.is_antichain.sperner
- \+ *def* falling

modified src/combinatorics/set_family/shadow.lean
- \+ *lemma* shadow_singleton_empty
- \+ *lemma* sized_shadow_iff

modified src/data/finset/basic.lean
- \+ *lemma* ssubset_iff_exists_insert_subset
- \+ *lemma* ssubset_iff_exists_subset_erase

modified src/data/fintype/basic.lean
- \+ *lemma* insert_inj_on'



## [2022-03-01 15:29:36](https://github.com/leanprover-community/mathlib/commit/3007f24)
chore(*): use `*_*_*_comm` where possible ([#12372](https://github.com/leanprover-community/mathlib/pull/12372))
These lemmas are quite helpful when proving `map_add` type statements; hopefully people will remember them more if they see them used in a few more places.
#### Estimated changes
modified src/data/num/lemmas.lean

modified src/group_theory/free_abelian_group.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/matrix/determinant.lean

modified src/linear_algebra/prod.lean

modified src/tactic/omega/eq_elim.lean



## [2022-03-01 15:29:35](https://github.com/leanprover-community/mathlib/commit/3fb051d)
feat(field_theory/krull_topology): added krull_topology_t2 ([#11973](https://github.com/leanprover-community/mathlib/pull/11973))
#### Estimated changes
modified src/data/fun_like/basic.lean
- \+ *lemma* exists_ne

modified src/field_theory/krull_topology.lean
- \+ *lemma* subgroup.is_open_of_one_mem_interior
- \+ *lemma* intermediate_field.fixing_subgroup_is_open
- \+ *lemma* krull_topology_t2



## [2022-03-01 14:22:58](https://github.com/leanprover-community/mathlib/commit/5a56e46)
chore(data/polynomial/monic): remove useless lemma ([#12364](https://github.com/leanprover-community/mathlib/pull/12364))
There is a `nontrivial` version of this lemma (`ne_zero_of_monic`) which actually has uses in the library, unlike this deleted lemma. We also tidy the proof of the lemma below.
#### Estimated changes
modified src/data/polynomial/monic.lean
- \- *lemma* ne_zero_of_monic_of_zero_ne_one



## [2022-03-01 14:22:57](https://github.com/leanprover-community/mathlib/commit/a4e936c)
chore(category_theory/idempotents) replaced "idempotence" by "idem" ([#12362](https://github.com/leanprover-community/mathlib/pull/12362))
#### Estimated changes
modified src/category_theory/idempotents/basic.lean
- \+ *lemma* idem_of_id_sub_idem
- \- *lemma* idempotence_of_id_sub_idempotent

modified src/category_theory/idempotents/biproducts.lean

modified src/category_theory/idempotents/functor_categories.lean

modified src/category_theory/idempotents/karoubi.lean
- \+/\- *lemma* id_eq
- \+/\- *lemma* id_eq
- \+/\- *def* decomp_id_i
- \+/\- *def* decomp_id_i

modified src/category_theory/idempotents/karoubi_karoubi.lean



## [2022-03-01 10:36:01](https://github.com/leanprover-community/mathlib/commit/1f39ada)
feat(linear_algebra): generalize `linear_equiv.finrank_eq` to rings ([#12358](https://github.com/leanprover-community/mathlib/pull/12358))
Since `finrank` doesn't assume the module is actually a vector space, neither should the statement that linear equivalences preserve it.
#### Estimated changes
modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finrank_map_eq
- \+/\- *lemma* finrank_map_eq
- \+/\- *theorem* finrank_eq
- \+/\- *theorem* finrank_eq



## [2022-03-01 07:35:56](https://github.com/leanprover-community/mathlib/commit/c223a81)
feat(measure_theory/function/locally_integrable): define locally integrable ([#12216](https://github.com/leanprover-community/mathlib/pull/12216))
* Define the locally integrable predicate
* Move all results about integrability on compact sets to a new file
* Rename some lemmas from `integrable_on_compact` -> `locally_integrable`, if appropriate.
* Weaken some type-class assumptions (also on `is_compact_interval`)
* Simplify proof of `continuous.integrable_of_has_compact_support`
* Rename variables in moved lemmas to sensible names
#### Estimated changes
created src/measure_theory/function/locally_integrable.lean
- \+ *lemma* integrable.locally_integrable
- \+ *lemma* locally_integrable.ae_measurable
- \+ *lemma* locally_integrable_iff
- \+ *lemma* integrable_on.mul_continuous_on_of_subset
- \+ *lemma* integrable_on.mul_continuous_on
- \+ *lemma* integrable_on.continuous_on_mul_of_subset
- \+ *lemma* integrable_on.continuous_on_mul
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* continuous.locally_integrable
- \+ *lemma* continuous_on.integrable_on_Icc
- \+ *lemma* continuous.integrable_on_Icc
- \+ *lemma* continuous.integrable_on_Ioc
- \+ *lemma* continuous_on.integrable_on_interval
- \+ *lemma* continuous.integrable_on_interval
- \+ *lemma* continuous.integrable_on_interval_oc
- \+ *lemma* continuous.integrable_of_has_compact_support
- \+ *lemma* monotone_on.integrable_on_compact
- \+ *lemma* antitone_on.integrable_on_compact
- \+ *lemma* monotone.locally_integrable
- \+ *lemma* antitone.locally_integrable
- \+ *def* locally_integrable

modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* integrable_on_iff_integable_of_support_subset
- \- *lemma* is_compact.integrable_on_of_nhds_within
- \- *lemma* continuous_on.integrable_on_compact
- \- *lemma* continuous_on.integrable_on_Icc
- \- *lemma* continuous_on.integrable_on_interval
- \- *lemma* continuous.integrable_on_compact
- \- *lemma* continuous.integrable_on_Icc
- \- *lemma* continuous.integrable_on_Ioc
- \- *lemma* continuous.integrable_on_interval
- \- *lemma* continuous.integrable_on_interval_oc
- \- *lemma* continuous.integrable_of_has_compact_support
- \- *lemma* measure_theory.integrable_on.mul_continuous_on_of_subset
- \- *lemma* measure_theory.integrable_on.mul_continuous_on
- \- *lemma* measure_theory.integrable_on.continuous_on_mul_of_subset
- \- *lemma* measure_theory.integrable_on.continuous_on_mul
- \- *lemma* monotone_on.integrable_on_compact
- \- *lemma* antitone_on.integrable_on_compact
- \- *lemma* monotone.integrable_on_compact
- \- *lemma* antitone.integrable_on_compact

modified src/measure_theory/integral/interval_integral.lean

modified src/topology/algebra/order/compact.lean
- \+/\- *lemma* is_compact_interval
- \+/\- *lemma* is_compact_interval

modified test/monotonicity.lean



## [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/cd98967)
feat(order/category/CompleteLattice): The category of complete lattices ([#12348](https://github.com/leanprover-community/mathlib/pull/12348))
Define `CompleteLattice`, the category of complete lattices with complete lattice homomorphisms.
#### Estimated changes
created src/order/category/CompleteLattice.lean
- \+ *lemma* CompleteLattice_dual_comp_forget_to_BoundedLattice
- \+ *def* CompleteLattice
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv

modified src/order/hom/complete_lattice.lean
- \+ *def* to_bounded_lattice_hom



## [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/37885e8)
feat(category_theory/idempotents): biproducts in idempotent completions ([#12333](https://github.com/leanprover-community/mathlib/pull/12333))
#### Estimated changes
created src/category_theory/idempotents/biproducts.lean
- \+ *lemma* karoubi_has_finite_biproducts
- \+ *def* bicone
- \+ *def* complement
- \+ *def* decomposition



## [2022-03-01 01:31:29](https://github.com/leanprover-community/mathlib/commit/73dd4b5)
refactor(category_theory/functor): a folder for concepts directly related to functors ([#12346](https://github.com/leanprover-community/mathlib/pull/12346))
#### Estimated changes
modified docs/tutorial/category_theory/intro.lean

modified src/algebra/category/Mon/basic.lean

modified src/algebra/category/Semigroup/basic.lean

modified src/category_theory/abelian/ext.lean

modified src/category_theory/adjunction/reflective.lean

modified src/category_theory/comma.lean

modified src/category_theory/concrete_category/reflects_isomorphisms.lean

modified src/category_theory/equivalence.lean

modified src/category_theory/full_subcategory.lean

renamed src/category_theory/functor.lean to src/category_theory/functor/basic.lean

renamed src/category_theory/functor_category.lean to src/category_theory/functor/category.lean

renamed src/category_theory/const.lean to src/category_theory/functor/const.lean

renamed src/category_theory/currying.lean to src/category_theory/functor/currying.lean

created src/category_theory/functor/default.lean

renamed src/category_theory/derived.lean to src/category_theory/functor/derived.lean

renamed src/category_theory/flat_functors.lean to src/category_theory/functor/flat.lean

renamed src/category_theory/fully_faithful.lean to src/category_theory/functor/fully_faithful.lean

renamed src/category_theory/functorial.lean to src/category_theory/functor/functorial.lean

renamed src/category_theory/hom_functor.lean to src/category_theory/functor/hom.lean

renamed src/category_theory/reflects_isomorphisms.lean to src/category_theory/functor/reflects_isomorphisms.lean

modified src/category_theory/limits/colimit_limit.lean

modified src/category_theory/limits/cones.lean

modified src/category_theory/limits/fubini.lean

modified src/category_theory/limits/is_limit.lean

modified src/category_theory/monad/algebra.lean

modified src/category_theory/monad/basic.lean

modified src/category_theory/monoidal/center.lean

modified src/category_theory/monoidal/functor_category.lean

modified src/category_theory/monoidal/functorial.lean

modified src/category_theory/monoidal/tor.lean

modified src/category_theory/natural_isomorphism.lean

modified src/category_theory/over.lean

modified src/category_theory/punit.lean

modified src/category_theory/sigma/basic.lean

modified src/category_theory/sites/cover_preserving.lean

modified src/category_theory/subobject/mono_over.lean

modified src/category_theory/thin.lean

modified src/category_theory/types.lean

modified src/category_theory/whiskering.lean

modified src/category_theory/yoneda.lean

