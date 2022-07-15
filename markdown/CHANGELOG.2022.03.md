## [2022-03-31 23:56:26](https://github.com/leanprover-community/mathlib/commit/2b92d08)
feat(model_theory/elementary_maps): The Tarski-Vaught test ([#12919](https://github.com/leanprover-community/mathlib/pull/12919))
Proves the Tarski-Vaught test for elementary embeddings and substructures.
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.cast_add_zero

Modified src/model_theory/elementary_maps.lean
- \+ *theorem* first_order.language.embedding.is_elementary_of_exists
- \+ *def* first_order.language.embedding.to_elementary_embedding
- \+ *theorem* first_order.language.substructure.is_elementary_of_exists
- \+ *def* first_order.language.substructure.to_elementary_substructure

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.formula.realize_relabel_sum_inr



## [2022-03-31 17:21:48](https://github.com/leanprover-community/mathlib/commit/de50389)
split(order/chain): Split off `order.zorn` ([#13060](https://github.com/leanprover-community/mathlib/pull/13060))
Split `order.zorn` into two files, one about chains, the other one about Zorn's lemma.
#### Estimated changes
Added src/order/chain.lean
- \+ *lemma* chain_closure.is_chain
- \+ *lemma* chain_closure.succ_fixpoint
- \+ *lemma* chain_closure.succ_fixpoint_iff
- \+ *lemma* chain_closure.total
- \+ *inductive* chain_closure
- \+ *lemma* chain_closure_empty
- \+ *lemma* chain_closure_max_chain
- \+ *lemma* is_chain.directed_on
- \+ *lemma* is_chain.image
- \+ *lemma* is_chain.insert
- \+ *lemma* is_chain.mono
- \+ *lemma* is_chain.succ
- \+ *lemma* is_chain.super_chain_succ_chain
- \+ *lemma* is_chain.symm
- \+ *lemma* is_chain.total
- \+ *def* is_chain
- \+ *lemma* is_chain_empty
- \+ *lemma* is_chain_of_trichotomous
- \+ *lemma* is_chain_univ_iff
- \+ *lemma* is_max_chain.is_chain
- \+ *lemma* is_max_chain.not_super_chain
- \+ *def* is_max_chain
- \+ *def* max_chain
- \+ *lemma* max_chain_spec
- \+ *lemma* set.subsingleton.is_chain
- \+ *lemma* subset_succ_chain
- \+ *def* succ_chain
- \+ *lemma* succ_chain_spec
- \+ *def* super_chain

Modified src/order/zorn.lean
- \- *lemma* chain_closure.is_chain
- \- *lemma* chain_closure.succ_fixpoint
- \- *lemma* chain_closure.succ_fixpoint_iff
- \- *inductive* chain_closure
- \- *lemma* chain_closure_empty
- \- *lemma* chain_closure_max_chain
- \- *lemma* chain_closure_total
- \- *lemma* is_chain.directed
- \- *lemma* is_chain.directed_on
- \- *lemma* is_chain.image
- \- *lemma* is_chain.insert
- \- *lemma* is_chain.mono
- \- *lemma* is_chain.succ
- \- *lemma* is_chain.super_chain_succ_chain
- \- *lemma* is_chain.symm
- \- *lemma* is_chain.total
- \- *def* is_chain
- \- *lemma* is_chain_empty
- \- *lemma* is_chain_of_trichotomous
- \- *lemma* is_chain_univ_iff
- \- *lemma* is_max_chain.is_chain
- \- *lemma* is_max_chain.not_super_chain
- \- *def* is_max_chain
- \- *def* max_chain
- \- *lemma* max_chain_spec
- \- *lemma* set.subsingleton.is_chain
- \- *def* succ_chain
- \- *lemma* succ_increasing
- \- *lemma* succ_spec
- \- *def* super_chain



## [2022-03-31 16:09:24](https://github.com/leanprover-community/mathlib/commit/13e08bf)
feat(model_theory/*): Constructors for low-arity languages and structures ([#12960](https://github.com/leanprover-community/mathlib/pull/12960))
Defines `first_order.language.mk₂` to make it easier to define a language with at-most-binary symbols.
Defines `first_order.language.Structure.mk₂` to make it easier to define a structure in a language defined with `first_order.language₂`.
Defines `first_order.language.functions.apply₁` and `first_order.language.functions.apply₂` to make it easier to construct terms using low-arity function symbols.
Defines `first_order.language.relations.formula₁` and `first_order.language.relations.formula₂` to make it easier to construct formulas using low-arity relation symbols.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.Structure.fun_map_apply₀
- \+ *lemma* first_order.language.Structure.fun_map_apply₁
- \+ *lemma* first_order.language.Structure.fun_map_apply₂
- \+ *lemma* first_order.language.Structure.rel_map_apply₁
- \+ *lemma* first_order.language.Structure.rel_map_apply₂
- \+ *def* first_order.language.fun_map₂
- \+ *def* first_order.language.rel_map₂
- \+ *def* first_order.sequence₂

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.bounded_formula.realize_rel₁
- \+ *lemma* first_order.language.bounded_formula.realize_rel₂
- \+ *lemma* first_order.language.formula.realize_rel₁
- \+ *lemma* first_order.language.formula.realize_rel₂
- \+ *lemma* first_order.language.term.realize_functions_apply₁
- \+ *lemma* first_order.language.term.realize_functions_apply₂

Modified src/model_theory/syntax.lean
- \+ *def* first_order.language.functions.apply₁
- \+ *def* first_order.language.functions.apply₂
- \+ *def* first_order.language.relations.bounded_formula₁
- \+ *def* first_order.language.relations.bounded_formula₂
- \+ *def* first_order.language.relations.formula₁
- \+ *def* first_order.language.relations.formula₂



## [2022-03-31 16:09:23](https://github.com/leanprover-community/mathlib/commit/f1ae620)
feat(model_theory/bundled, satisfiability): Bundled models ([#12945](https://github.com/leanprover-community/mathlib/pull/12945))
Defines `Theory.Model`, a type of nonempty bundled models of a particular theory.
Refactors satisfiability in terms of bundled models.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* first_order.language.trivial_unit_structure

Modified src/model_theory/bundled.lean
- \+ *lemma* first_order.language.Theory.Model.coe_of
- \+ *def* first_order.language.Theory.Model.of
- \+ *structure* first_order.language.Theory.Model
- \+ *lemma* first_order.language.Theory.coe_of
- \+ *def* first_order.language.Theory.model.bundled

Modified src/model_theory/satisfiability.lean
- \- *def* first_order.language.Theory.is_satisfiable.some_model
- \+/\- *def* first_order.language.Theory.is_satisfiable
- \- *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_bd_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_iff

Modified src/model_theory/semantics.lean


Modified src/model_theory/ultraproducts.lean




## [2022-03-31 15:26:34](https://github.com/leanprover-community/mathlib/commit/2861d4e)
feat(combinatorics/simple_graph/connectivity): walk constructor patterns with explicit vertices ([#13078](https://github.com/leanprover-community/mathlib/pull/13078))
This saves a couple underscores, letting you write `walk.cons' _ v _ h p` instead of `@walk.cons _ _ _ v _ h p` when you want that middle vertex in a pattern.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *abbreviation* simple_graph.walk.cons'
- \+ *abbreviation* simple_graph.walk.nil'



## [2022-03-31 14:15:57](https://github.com/leanprover-community/mathlib/commit/25ef4f0)
feat(topology/algebra/matrix): more continuity lemmas for matrices ([#13009](https://github.com/leanprover-community/mathlib/pull/13009))
This should cover all the definitions in `data/matrix/basic`, and also picks out a few notable definitions (`det`, `trace`, `adjugate`, `cramer`, `inv`) from other files.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/topology/algebra/matrix.lean
- \+ *lemma* continuous.matrix_adjugate
- \+ *lemma* continuous.matrix_col
- \+ *lemma* continuous.matrix_cramer
- \+ *lemma* continuous.matrix_det
- \+ *lemma* continuous.matrix_diag
- \+ *lemma* continuous.matrix_dot_product
- \+ *lemma* continuous.matrix_elem
- \+ *lemma* continuous.matrix_map
- \+ *lemma* continuous.matrix_minor
- \+ *lemma* continuous.matrix_mul
- \+ *lemma* continuous.matrix_mul_vec
- \+ *lemma* continuous.matrix_reindex
- \+ *lemma* continuous.matrix_row
- \+ *lemma* continuous.matrix_trace
- \+ *lemma* continuous.matrix_transpose
- \+ *lemma* continuous.matrix_update_column
- \+ *lemma* continuous.matrix_update_row
- \+ *lemma* continuous.matrix_vec_mul
- \+ *lemma* continuous.matrix_vec_mul_vec
- \+ *lemma* continuous_at_matrix_inv
- \- *lemma* continuous_det
- \+ *lemma* continuous_matrix.diagonal
- \+ *lemma* continuous_matrix

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous.if_const



## [2022-03-31 13:42:09](https://github.com/leanprover-community/mathlib/commit/0f6eec6)
feat(ring_theory/polynomial/pochhammer): generalize a proof from `comm_semiring` to `semiring` ([#13024](https://github.com/leanprover-community/mathlib/pull/13024))
This PR is similar to [#13018](https://github.com/leanprover-community/mathlib/pull/13018).  Lemma `pochhammer_succ_eval` was already proven with a commutativity assumption.  I generalized the proof to `semiring` by introducing a helper lemma.
I still feel that this is harder than I would like it to be: `pochhammer` "is" a polynomial in `ℕ[X]` and all these commutativity assumptions are satisfied, since `ℕ[X]` is commutative.
#### Estimated changes
Modified src/ring_theory/polynomial/pochhammer.lean




## [2022-03-31 13:00:33](https://github.com/leanprover-community/mathlib/commit/1b42223)
feat(analysis/locally_convex): the topology of weak duals is locally convex ([#12623](https://github.com/leanprover-community/mathlib/pull/12623))
#### Estimated changes
Added src/analysis/locally_convex/weak_dual.lean
- \+ *lemma* linear_map.coe_to_seminorm
- \+ *lemma* linear_map.has_basis_weak_bilin
- \+ *def* linear_map.to_seminorm
- \+ *lemma* linear_map.to_seminorm_apply
- \+ *lemma* linear_map.to_seminorm_ball_zero
- \+ *lemma* linear_map.to_seminorm_comp
- \+ *def* linear_map.to_seminorm_family
- \+ *lemma* linear_map.to_seminorm_family_apply

Modified src/topology/algebra/module/weak_dual.lean




## [2022-03-31 12:28:09](https://github.com/leanprover-community/mathlib/commit/6405a6a)
feat(analysis/locally_convex): closed balanced sets are a basis of the topology ([#12786](https://github.com/leanprover-community/mathlib/pull/12786))
We prove some topological properties of the balanced core.
#### Estimated changes
Modified src/analysis/locally_convex/balanced_core_hull.lean
- \+ *lemma* balanced_core_emptyset
- \+ *lemma* balanced_core_is_closed
- \+ *lemma* balanced_core_mem_nhds_zero
- \+ *lemma* nhds_basis_closed_balanced
- \+ *lemma* subset_balanced_core



## [2022-03-31 10:35:37](https://github.com/leanprover-community/mathlib/commit/7833dbe)
lint(algebra/*): fix some lint errors ([#13058](https://github.com/leanprover-community/mathlib/pull/13058))
* add some docstrings to additive versions;
* make `with_zero.ordered_add_comm_monoid` reducible.
#### Estimated changes
Modified src/algebra/group/semiconj.lean


Modified src/algebra/hom/equiv.lean
- \+/\- *lemma* mul_equiv.apply_symm_apply
- \+/\- *lemma* mul_equiv.symm_apply_apply

Modified src/algebra/order/monoid.lean


Modified src/topology/metric_space/emetric_space.lean




## [2022-03-31 08:43:56](https://github.com/leanprover-community/mathlib/commit/ba9ead0)
feat(order/sup_indep): lemmas about `pairwise` and `set.pairwise` ([#12590](https://github.com/leanprover-community/mathlib/pull/12590))
The `disjoint` lemmas can now be stated in terms of these two `pairwise` definitions.
This wasn't previously possible as these definitions were not yet imported.
This also adds the `iff` versions of these lemmas, and a docstring tying them all together.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean


Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* Sup_disjoint_iff
- \+ *lemma* disjoint_Sup_iff

Modified src/order/sup_indep.lean
- \- *lemma* complete_lattice.independent.disjoint
- \+ *lemma* complete_lattice.independent.pairwise_disjoint
- \+ *lemma* complete_lattice.independent_iff_pairwise_disjoint
- \- *lemma* complete_lattice.set_independent.disjoint
- \+ *lemma* complete_lattice.set_independent.pairwise_disjoint
- \+ *lemma* complete_lattice.set_independent_iff_pairwise_disjoint



## [2022-03-31 06:51:20](https://github.com/leanprover-community/mathlib/commit/81c5d17)
chore(algebra/order/monoid_lemmas): remove exactly same lemmas ([#13068](https://github.com/leanprover-community/mathlib/pull/13068))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas.lean
- \- *lemma* left.mul_lt_one_of_lt_of_lt_one
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \- *theorem* mul_lt_of_lt_of_lt_one
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \- *theorem* mul_lt_of_lt_one_of_lt
- \- *lemma* right.mul_lt_one_of_lt_of_lt_one



## [2022-03-31 06:51:19](https://github.com/leanprover-community/mathlib/commit/7a37490)
feat(ring_theory/polynomial/pochhammer): add a binomial like recursion for pochhammer ([#13018](https://github.com/leanprover-community/mathlib/pull/13018))
This PR proves the identity
`pochhammer R n + n * (pochhammer R (n - 1)).comp (X + 1) = (pochhammer R n).comp (X + 1)`
analogous to the additive recursion for binomial coefficients.
For the proof, first we prove the result for a `comm_semiring` as `pochhammer_add_pochhammer_aux`.  Next, we apply this identity in the general case.
If someone has any idea of how to make the maths statement: it suffices to show this identity for pochhammer symbols in the commutative case, I would be *very* happy to know!
#### Estimated changes
Modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_succ_comp_X_add_one



## [2022-03-31 06:51:18](https://github.com/leanprover-community/mathlib/commit/290f440)
feat(order/category/Semilattice): The categories of semilattices ([#12890](https://github.com/leanprover-community/mathlib/pull/12890))
Define `SemilatticeSup` and `SemilatticeInf`, the categories of finitary supremum lattices and finitary infimum lattices.
#### Estimated changes
Modified src/order/category/BoundedLattice.lean
- \+ *lemma* BoundedLattice.coe_forget_to_BoundedOrder
- \+ *lemma* BoundedLattice.coe_forget_to_Lattice
- \+ *lemma* BoundedLattice.coe_forget_to_SemilatticeInf
- \+ *lemma* BoundedLattice.coe_forget_to_SemilatticeSup
- \+ *lemma* BoundedLattice.forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+ *lemma* BoundedLattice.forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+ *lemma* BoundedLattice_dual_comp_forget_to_SemilatticeInf
- \+ *lemma* BoundedLattice_dual_comp_forget_to_SemilatticeSup

Added src/order/category/Semilattice.lean
- \+ *lemma* SemilatticeInf.coe_forget_to_PartialOrder
- \+ *lemma* SemilatticeInf.coe_of
- \+ *def* SemilatticeInf.dual
- \+ *def* SemilatticeInf.iso.mk
- \+ *def* SemilatticeInf.of
- \+ *structure* SemilatticeInf
- \+ *lemma* SemilatticeInf_dual_comp_forget_to_PartialOrder
- \+ *lemma* SemilatticeSup.coe_forget_to_PartialOrder
- \+ *lemma* SemilatticeSup.coe_of
- \+ *def* SemilatticeSup.dual
- \+ *def* SemilatticeSup.iso.mk
- \+ *def* SemilatticeSup.of
- \+ *structure* SemilatticeSup
- \+ *lemma* SemilatticeSup_dual_comp_forget_to_PartialOrder
- \+ *def* SemilatticeSup_equiv_SemilatticeInf



## [2022-03-31 06:51:17](https://github.com/leanprover-community/mathlib/commit/760f1b2)
refactor(*): rename `topological_ring` to `topological_semiring` and introduce a new `topological_ring` extending `has_continuous_neg` ([#12864](https://github.com/leanprover-community/mathlib/pull/12864))
Following the discussion in this [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity/near/275553306), this renames `topological_ring` to `topological_semiring` throughout the library and weakens the typeclass assumptions from `semiring` to `non_unital_non_assoc_semiring`. Moreover, it introduces a new `topological_ring` class which takes a type class parameter of `non_unital_non_assoc_ring` and extends `topological_semiring` and `has_continuous_neg`.
In the case of *unital* (semi)rings (even non-associative), the type class `topological_semiring` is sufficient to capture the notion of `topological_ring` because negation is just multiplication by `-1`. Therefore, those working with unital (semi)rings can proceed with the small change of using `topological_semiring` instead of `topological_ring`.
The primary reason for the distinction is to weaken the type class assumptions to allow for non-unital rings, in which case `has_continuous_neg` must be explicitly assumed.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)
#### Estimated changes
Modified src/analysis/normed/normed_field.lean


Modified src/geometry/manifold/algebra/structures.lean
- \- *lemma* topological_ring_of_smooth
- \+ *lemma* topological_semiring_of_smooth

Modified src/topology/algebra/algebra.lean
- \+/\- *lemma* continuous_algebra_map
- \+/\- *lemma* continuous_algebra_map_iff_smul
- \+/\- *lemma* has_continuous_smul_of_algebra_map

Modified src/topology/algebra/field.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module/basic.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/algebra/ring.lean
- \+ *lemma* topological_semiring.has_continuous_neg_of_mul
- \+ *lemma* topological_semiring.to_topological_ring

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/locally_constant.lean


Modified src/topology/continuous_function/polynomial.lean


Modified src/topology/instances/nnreal.lean




## [2022-03-31 06:19:33](https://github.com/leanprover-community/mathlib/commit/c2339ca)
feat(algebraic_topology): map_alternating_face_map_complex ([#13028](https://github.com/leanprover-community/mathlib/pull/13028))
In this PR, we obtain a compatibility `map_alternating_face_map_complex` of the construction of the alternating face map complex functor with respect to additive functors between preadditive categories.
#### Estimated changes
Modified src/algebraic_topology/alternating_face_map_complex.lean
- \+ *lemma* algebraic_topology.map_alternating_face_map_complex



## [2022-03-31 02:41:53](https://github.com/leanprover-community/mathlib/commit/8a21316)
feat(combinatorics/simple_graph/regularity/bound): Numerical bounds for Szemerédi's regularity lemma ([#12962](https://github.com/leanprover-community/mathlib/pull/12962))
Define the constants appearing in Szemerédi's regularity lemma and prove a bunch of numerical facts about them.
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* le_div_self

Added src/combinatorics/simple_graph/regularity/bound.lean
- \+ *lemma* szemeredi_regularity.a_add_one_le_four_pow_parts_card
- \+ *lemma* szemeredi_regularity.bound_pos
- \+ *lemma* szemeredi_regularity.card_aux₁
- \+ *lemma* szemeredi_regularity.card_aux₂
- \+ *lemma* szemeredi_regularity.coe_m_add_one_pos
- \+ *lemma* szemeredi_regularity.eps_pos
- \+ *lemma* szemeredi_regularity.eps_pow_five_pos
- \+ *lemma* szemeredi_regularity.four_pow_pos
- \+ *lemma* szemeredi_regularity.hundred_div_ε_pow_five_le_m
- \+ *lemma* szemeredi_regularity.hundred_le_m
- \+ *lemma* szemeredi_regularity.hundred_lt_pow_initial_bound_mul
- \+ *lemma* szemeredi_regularity.initial_bound_le_bound
- \+ *lemma* szemeredi_regularity.initial_bound_pos
- \+ *lemma* szemeredi_regularity.le_bound
- \+ *lemma* szemeredi_regularity.le_initial_bound
- \+ *lemma* szemeredi_regularity.le_step_bound
- \+ *lemma* szemeredi_regularity.m_coe_pos
- \+ *lemma* szemeredi_regularity.m_pos
- \+ *lemma* szemeredi_regularity.one_le_m_coe
- \+ *lemma* szemeredi_regularity.pow_mul_m_le_card_part
- \+ *lemma* szemeredi_regularity.seven_le_initial_bound
- \+ *def* szemeredi_regularity.step_bound
- \+ *lemma* szemeredi_regularity.step_bound_mono
- \+ *lemma* szemeredi_regularity.step_bound_pos_iff

Modified src/order/partition/equipartition.lean
- \+ *lemma* finpartition.is_equipartition.card_parts_eq_average



## [2022-03-31 02:10:17](https://github.com/leanprover-community/mathlib/commit/299984b)
feat(combinatorics/simple_graph/uniform): Graph uniformity and uniform partitions ([#12957](https://github.com/leanprover-community/mathlib/pull/12957))
Define uniformity of a pair of vertices in a graph and uniformity of a partition of vertices of a graph.
#### Estimated changes
Added src/combinatorics/simple_graph/regularity/uniform.lean
- \+ *lemma* finpartition.bot_is_uniform
- \+ *def* finpartition.is_uniform
- \+ *lemma* finpartition.is_uniform_of_empty
- \+ *lemma* finpartition.is_uniform_one
- \+ *lemma* finpartition.mk_mem_non_uniforms_iff
- \+ *lemma* finpartition.non_uniforms_bot
- \+ *lemma* finpartition.nonempty_of_not_uniform
- \+ *lemma* simple_graph.is_uniform.mono
- \+ *lemma* simple_graph.is_uniform.symm
- \+ *def* simple_graph.is_uniform
- \+ *lemma* simple_graph.is_uniform_comm
- \+ *lemma* simple_graph.is_uniform_one
- \+ *lemma* simple_graph.is_uniform_singleton
- \+ *lemma* simple_graph.not_is_uniform_zero



## [2022-03-31 00:12:51](https://github.com/leanprover-community/mathlib/commit/47b1d78)
feat(linear_algebra/matrix): any matrix power can be expressed as sums of powers `0 ≤ k < fintype.card n` ([#12983](https://github.com/leanprover-community/mathlib/pull/12983))
I'm not familiar enough with the polynomial API to know if we can neatly state a similar result for negative powers.
#### Estimated changes
Modified src/data/polynomial/ring_division.lean


Modified src/linear_algebra/charpoly/basic.lean
- \+ *lemma* linear_map.aeval_eq_aeval_mod_charpoly
- \+ *lemma* linear_map.pow_eq_aeval_mod_charpoly

Modified src/linear_algebra/matrix/charpoly/basic.lean


Modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+ *lemma* matrix.aeval_eq_aeval_mod_charpoly
- \+ *lemma* matrix.pow_eq_aeval_mod_charpoly



## [2022-03-30 17:30:25](https://github.com/leanprover-community/mathlib/commit/fc35cb3)
chore(data/finset/card): add `card_disj_union` ([#13061](https://github.com/leanprover-community/mathlib/pull/13061))
#### Estimated changes
Modified src/data/finset/card.lean
- \+ *lemma* finset.card_disj_union



## [2022-03-30 16:05:51](https://github.com/leanprover-community/mathlib/commit/7f450cb)
feat(topology/sets/order): Clopen upper sets ([#12670](https://github.com/leanprover-community/mathlib/pull/12670))
Define `clopen_upper_set`, the type of clopen upper sets of an ordered topological space.
#### Estimated changes
Added src/topology/sets/order.lean
- \+ *lemma* clopen_upper_set.clopen
- \+ *lemma* clopen_upper_set.coe_bot
- \+ *lemma* clopen_upper_set.coe_inf
- \+ *lemma* clopen_upper_set.coe_mk
- \+ *lemma* clopen_upper_set.coe_sup
- \+ *lemma* clopen_upper_set.coe_top
- \+ *def* clopen_upper_set.to_upper_set
- \+ *lemma* clopen_upper_set.upper
- \+ *structure* clopen_upper_set



## [2022-03-30 13:52:41](https://github.com/leanprover-community/mathlib/commit/518e81a)
feat(topology): add lemmas about `frontier` ([#13054](https://github.com/leanprover-community/mathlib/pull/13054))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* frontier_closure_subset
- \+ *lemma* frontier_interior_subset

Modified src/topology/connected.lean
- \+ *lemma* frontier_eq_empty_iff
- \+ *lemma* nonempty_frontier_iff

Modified src/topology/subset_properties.lean
- \+ *lemma* is_clopen_iff_frontier_eq_empty



## [2022-03-30 13:52:39](https://github.com/leanprover-community/mathlib/commit/de62b06)
chore(data/set/pointwise): Golf using `set.image2` API ([#13051](https://github.com/leanprover-community/mathlib/pull/13051))
Add some more `set.image2` API and demonstrate use by golfing all relevant `data.set.pointwise` declarations.
Other additions
#### Estimated changes
Modified src/algebra/add_torsor.lean


Modified src/algebra/opposites.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* set.image2_assoc
- \+ *lemma* set.image2_image_left_anticomm
- \+ *lemma* set.image2_image_left_comm
- \+/\- *lemma* set.image2_left_comm
- \+/\- *lemma* set.image2_right_comm
- \+ *lemma* set.image_comm
- \+ *lemma* set.image_image2_antidistrib
- \+ *lemma* set.image_image2_antidistrib_left
- \+ *lemma* set.image_image2_antidistrib_right
- \+/\- *lemma* set.image_image2_distrib
- \+/\- *lemma* set.image_image2_distrib_left
- \+/\- *lemma* set.image_image2_distrib_right
- \+ *lemma* set.image_image2_right_anticomm
- \+ *lemma* set.image_image2_right_comm

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.Inter_inv
- \+/\- *lemma* set.Union_inv
- \+/\- *lemma* set.compl_inv
- \+/\- *lemma* set.finite.inv
- \+/\- *lemma* set.finite.mul
- \+ *lemma* set.finite.smul
- \+/\- *lemma* set.finite.smul_set
- \+/\- *lemma* set.image_inv
- \+/\- *lemma* set.image_mul
- \+ *lemma* set.image_op_inv
- \+/\- *lemma* set.image_op_mul
- \+/\- *lemma* set.inter_inv
- \+/\- *lemma* set.inv_empty
- \+/\- *lemma* set.inv_mem_inv
- \+/\- *lemma* set.inv_preimage
- \+/\- *lemma* set.inv_singleton
- \+/\- *lemma* set.inv_subset
- \+/\- *lemma* set.inv_subset_inv
- \+/\- *lemma* set.inv_univ
- \+/\- *lemma* set.mem_inv
- \+/\- *lemma* set.nonempty.inv
- \+/\- *lemma* set.nonempty.mul
- \+ *lemma* set.nonempty.smul
- \+ *lemma* set.nonempty.smul_set
- \+ *lemma* set.nonempty.vsub
- \+/\- *lemma* set.nonempty_inv
- \+/\- *lemma* set.union_inv



## [2022-03-30 13:52:38](https://github.com/leanprover-community/mathlib/commit/25e8730)
feat(analysis/special_functions/pow): abs value of real to complex power ([#13048](https://github.com/leanprover-community/mathlib/pull/13048))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.abs_cpow_eq_rpow_re_of_nonneg
- \+ *lemma* complex.abs_cpow_eq_rpow_re_of_pos



## [2022-03-30 13:52:37](https://github.com/leanprover-community/mathlib/commit/33a323c)
feat(data/fin): lemmas about ordering and cons ([#13044](https://github.com/leanprover-community/mathlib/pull/13044))
This marks a few extra facts `simp`, since the analogous facts are `simp` for `nat`.
#### Estimated changes
Modified archive/imo/imo1994_q1.lean


Modified src/data/fin/basic.lean
- \+ *lemma* fin.not_lt_zero
- \+/\- *lemma* fin.zero_le

Modified src/data/fin/tuple/basic.lean
- \+ *lemma* fin.cons_le_cons
- \+ *lemma* fin.pi_lex_lt_cons_cons



## [2022-03-30 13:52:33](https://github.com/leanprover-community/mathlib/commit/644a848)
fix(tactic/generalize_proofs): instantiate mvars ([#13025](https://github.com/leanprover-community/mathlib/pull/13025))
Reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/generalize_proofs.20failed/near/276965359).
#### Estimated changes
Modified src/tactic/generalize_proofs.lean


Modified test/generalize_proofs.lean




## [2022-03-30 13:52:32](https://github.com/leanprover-community/mathlib/commit/af3911c)
feat(data/polynomial/erase_lead): add two erase_lead lemmas ([#12910](https://github.com/leanprover-community/mathlib/pull/12910))
The two lemmas show that removing the leading term from the sum of two polynomials of unequal `nat_degree` is the same as removing the leading term of the one of larger `nat_degree` and adding.
The second lemma could be proved with `by rw [add_comm, erase_lead_add_of_nat_degree_lt_left pq, add_comm]`, but I preferred copying the same strategy as the previous one, to avoid interdependencies.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.erase_lead_add_of_nat_degree_lt_left
- \+ *lemma* polynomial.erase_lead_add_of_nat_degree_lt_right



## [2022-03-30 13:52:30](https://github.com/leanprover-community/mathlib/commit/e31f031)
feat(analysis/locally_convex): polar sets for dualities ([#12849](https://github.com/leanprover-community/mathlib/pull/12849))
Define the absolute polar for a duality and prove easy properties such as
* `linear_map.polar_eq_Inter`: The polar as an intersection.
* `linear_map.subset_bipolar`: The polar is a subset of the bipolar.
* `linear_map.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.
Moreover, the corresponding lemmas are removed in the normed space setting as they all follow directly from the general case.
#### Estimated changes
Added src/analysis/locally_convex/polar.lean
- \+ *def* linear_map.polar
- \+ *lemma* linear_map.polar_Union
- \+ *lemma* linear_map.polar_antitone
- \+ *lemma* linear_map.polar_empty
- \+ *lemma* linear_map.polar_eq_Inter
- \+ *lemma* linear_map.polar_gc
- \+ *lemma* linear_map.polar_mem
- \+ *lemma* linear_map.polar_mem_iff
- \+ *lemma* linear_map.polar_union
- \+ *lemma* linear_map.polar_univ
- \+ *lemma* linear_map.polar_weak_closed
- \+ *lemma* linear_map.polar_zero
- \+ *lemma* linear_map.subset_bipolar
- \+ *lemma* linear_map.tripolar_eq_polar
- \+ *lemma* linear_map.zero_mem_polar

Modified src/analysis/normed_space/dual.lean
- \- *lemma* bounded_polar_of_mem_nhds_zero
- \- *lemma* closed_ball_inv_subset_polar_closed_ball
- \- *lemma* is_closed_polar
- \+ *lemma* normed_space.bounded_polar_of_mem_nhds_zero
- \+ *lemma* normed_space.closed_ball_inv_subset_polar_closed_ball
- \+ *def* normed_space.dual_pairing
- \+ *lemma* normed_space.dual_pairing_apply
- \+ *lemma* normed_space.dual_pairing_separating_left
- \+ *lemma* normed_space.is_closed_polar
- \+ *lemma* normed_space.mem_polar_iff
- \+ *def* normed_space.polar
- \+ *lemma* normed_space.polar_ball_subset_closed_ball_div
- \+ *lemma* normed_space.polar_closed_ball
- \+ *lemma* normed_space.polar_closure
- \+ *lemma* normed_space.polar_univ
- \+ *lemma* normed_space.smul_mem_polar
- \- *def* polar
- \- *lemma* polar_Union
- \- *lemma* polar_antitone
- \- *lemma* polar_ball_subset_closed_ball_div
- \- *lemma* polar_closed_ball
- \- *lemma* polar_closure
- \- *lemma* polar_empty
- \- *lemma* polar_eq_Inter
- \- *lemma* polar_gc
- \- *lemma* polar_union
- \- *lemma* polar_univ
- \- *lemma* polar_zero
- \- *lemma* smul_mem_polar
- \- *lemma* zero_mem_polar

Modified src/analysis/normed_space/weak_dual.lean
- \- *lemma* weak_dual.is_closed_polar
- \- *def* weak_dual.polar



## [2022-03-30 11:47:45](https://github.com/leanprover-community/mathlib/commit/f13ee54)
chore(*): sort out some to_additive and simp orderings ([#13038](https://github.com/leanprover-community/mathlib/pull/13038))
- To additive should always come after simp, unless the linter complains.
- Also make to_additive transfer the `protected` attribute for consistency.
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/group/to_additive.lean


Modified src/data/finset/noncomm_prod.lean


Modified src/data/part.lean




## [2022-03-30 11:47:44](https://github.com/leanprover-community/mathlib/commit/37a8a0b)
feat(ring_theory/graded_algebra): define homogeneous localisation ([#12784](https://github.com/leanprover-community/mathlib/pull/12784))
This pr defines `homogeneous_localization`. For `x` in projective spectrum of `A`, homogeneous localisation at `x` is the subring of $$A_x$$ containing `a/b` where `a` and `b` have the same degree. This construction is mainly used in constructing structure sheaf of Proj of a graded ring
#### Estimated changes
Added src/ring_theory/graded_algebra/homogeneous_localization.lean
- \+ *lemma* homogeneous_localization.add_val
- \+ *def* homogeneous_localization.deg
- \+ *def* homogeneous_localization.denom
- \+ *lemma* homogeneous_localization.denom_mem
- \+ *lemma* homogeneous_localization.denom_not_mem
- \+ *lemma* homogeneous_localization.eq_num_div_denom
- \+ *lemma* homogeneous_localization.ext_iff_val
- \+ *lemma* homogeneous_localization.mul_val
- \+ *lemma* homogeneous_localization.neg_val
- \+ *def* homogeneous_localization.num
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_add
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_mul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_neg
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_one
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_pow
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_smul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.deg_zero
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_add
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_mul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_neg
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_one
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_pow
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_smul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.denom_zero
- \+ *def* homogeneous_localization.num_denom_same_deg.embedding
- \+ *lemma* homogeneous_localization.num_denom_same_deg.ext
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_add
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_mul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_neg
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_one
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_pow
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_smul
- \+ *lemma* homogeneous_localization.num_denom_same_deg.num_zero
- \+ *structure* homogeneous_localization.num_denom_same_deg
- \+ *lemma* homogeneous_localization.num_mem
- \+ *lemma* homogeneous_localization.one_eq
- \+ *lemma* homogeneous_localization.one_val
- \+ *lemma* homogeneous_localization.pow_val
- \+ *lemma* homogeneous_localization.smul_val
- \+ *lemma* homogeneous_localization.sub_val
- \+ *def* homogeneous_localization.val
- \+ *lemma* homogeneous_localization.val_injective
- \+ *lemma* homogeneous_localization.zero_eq
- \+ *lemma* homogeneous_localization.zero_val
- \+ *def* homogeneous_localization



## [2022-03-30 09:48:05](https://github.com/leanprover-community/mathlib/commit/cdd1703)
feat(algebra/associates): add two instances and a lemma about the order on the monoid of associates of a monoid ([#12863](https://github.com/leanprover-community/mathlib/pull/12863))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.is_unit_iff_eq_bot



## [2022-03-30 03:51:16](https://github.com/leanprover-community/mathlib/commit/cd51f0d)
fix(data/fintype/basic): generalize fintype instance for fintype.card_coe ([#13055](https://github.com/leanprover-community/mathlib/pull/13055))
#### Estimated changes
Modified src/combinatorics/hall/finite.lean


Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_coe



## [2022-03-30 03:51:14](https://github.com/leanprover-community/mathlib/commit/f2fd6db)
chore(*): removing some `by { dunfold .., apply_instance }` proofs ([#13050](https://github.com/leanprover-community/mathlib/pull/13050))
Replaces the proofs `by { dunfold .., apply_instance }` by the exact term that is outputted by `show_term`.
#### Estimated changes
Modified src/linear_algebra/dual.lean


Modified src/topology/sheaves/limits.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean




## [2022-03-30 03:19:42](https://github.com/leanprover-community/mathlib/commit/ca3bb9e)
chore(scripts): update nolints.txt ([#13057](https://github.com/leanprover-community/mathlib/pull/13057))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




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
Modified counterexamples/phillips.lean


Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/box_integral/integrability.lean
- \+/\- *lemma* measure_theory.integrable_on.has_box_integral

Modified src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* ae_strongly_measurable_deriv
- \+ *lemma* strongly_measurable_deriv

Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/calculus/parametric_interval_integral.lean


Modified src/analysis/complex/abs_max.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/complex/liouville.lean
- \+/\- *lemma* complex.deriv_eq_smul_circle_integral

Modified src/analysis/complex/removable_singularity.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/fourier.lean


Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/normed_space/star/spectrum.lean
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal

Modified src/analysis/special_functions/non_integrable.lean


Modified src/measure_theory/constructions/prod.lean
- \- *lemma* ae_measurable.integral_prod_right'
- \- *lemma* ae_measurable.prod_mk_left
- \- *lemma* measurable.integral_prod_left'
- \- *lemma* measurable.integral_prod_left
- \- *lemma* measurable.integral_prod_right'
- \- *lemma* measurable.integral_prod_right
- \+/\- *lemma* measurable_set_integrable
- \+ *lemma* measure_theory.ae_strongly_measurable.integral_prod_right'
- \+ *lemma* measure_theory.ae_strongly_measurable.prod_mk_left
- \+ *lemma* measure_theory.ae_strongly_measurable.prod_swap
- \+/\- *lemma* measure_theory.has_finite_integral_prod_iff'
- \+/\- *lemma* measure_theory.has_finite_integral_prod_iff
- \+/\- *lemma* measure_theory.integrable_prod_iff'
- \+/\- *lemma* measure_theory.integrable_prod_iff
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_left'
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_left
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_right'
- \+ *lemma* measure_theory.strongly_measurable.integral_prod_right

Modified src/measure_theory/covering/besicovitch_vector_space.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/decomposition/radon_nikodym.lean


Modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.coe_fn_comp
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_comp_measurable
- \+/\- *lemma* measure_theory.ae_eq_fun.coe_fn_comp₂
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_comp₂_measurable
- \+/\- *lemma* measure_theory.ae_eq_fun.coe_fn_inf
- \+/\- *lemma* measure_theory.ae_eq_fun.coe_fn_sup
- \+/\- *def* measure_theory.ae_eq_fun.comp
- \+/\- *lemma* measure_theory.ae_eq_fun.comp_eq_mk
- \+ *def* measure_theory.ae_eq_fun.comp_measurable
- \+ *lemma* measure_theory.ae_eq_fun.comp_measurable_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.comp_measurable_mk
- \+ *lemma* measure_theory.ae_eq_fun.comp_measurable_to_germ
- \+/\- *lemma* measure_theory.ae_eq_fun.comp_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.comp_to_germ
- \+/\- *def* measure_theory.ae_eq_fun.comp₂
- \+/\- *lemma* measure_theory.ae_eq_fun.comp₂_eq_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.comp₂_eq_pair
- \+ *def* measure_theory.ae_eq_fun.comp₂_measurable
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_measurable_eq_mk
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_measurable_eq_pair
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_measurable_mk_mk
- \+ *lemma* measure_theory.ae_eq_fun.comp₂_measurable_to_germ
- \+/\- *lemma* measure_theory.ae_eq_fun.comp₂_mk_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.comp₂_to_germ
- \+/\- *def* measure_theory.ae_eq_fun.const
- \+/\- *lemma* measure_theory.ae_eq_fun.induction_on₂
- \+/\- *lemma* measure_theory.ae_eq_fun.induction_on₃
- \+/\- *def* measure_theory.ae_eq_fun.mk
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_coe_fn
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_div
- \+/\- *lemma* measure_theory.ae_eq_fun.mk_mul_mk
- \+/\- *lemma* measure_theory.ae_eq_fun.smul_mk
- \+/\- *def* measure_theory.measure.ae_eq_setoid

Modified src/measure_theory/function/ae_eq_of_integral.lean
- \+/\- *lemma* measure_theory.ae_eq_zero_of_forall_dual
- \+ *lemma* measure_theory.ae_eq_zero_of_forall_dual_of_is_separable
- \- *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable
- \+ *lemma* measure_theory.ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_strongly_measurable

Modified src/measure_theory/function/conditional_expectation.lean
- \- *lemma* measure_theory.Lp_meas.ae_measurable'
- \+ *lemma* measure_theory.Lp_meas.ae_strongly_measurable'
- \+/\- *def* measure_theory.Lp_meas
- \- *lemma* measure_theory.ae_eq_trim_iff_of_ae_measurable'
- \+ *lemma* measure_theory.ae_eq_trim_iff_of_ae_strongly_measurable'
- \- *lemma* measure_theory.ae_measurable'.add
- \- *lemma* measure_theory.ae_measurable'.ae_eq_mk
- \- *lemma* measure_theory.ae_measurable'.congr
- \- *lemma* measure_theory.ae_measurable'.const_inner
- \- *lemma* measure_theory.ae_measurable'.const_smul
- \- *lemma* measure_theory.ae_measurable'.measurable_comp
- \- *lemma* measure_theory.ae_measurable'.measurable_mk
- \- *def* measure_theory.ae_measurable'.mk
- \- *lemma* measure_theory.ae_measurable'.neg
- \- *lemma* measure_theory.ae_measurable'.sub
- \- *def* measure_theory.ae_measurable'
- \- *lemma* measure_theory.ae_measurable'_condexp_L1
- \- *lemma* measure_theory.ae_measurable'_condexp_L1_clm
- \- *lemma* measure_theory.ae_measurable'_condexp_L2
- \- *lemma* measure_theory.ae_measurable'_condexp_ind
- \- *lemma* measure_theory.ae_measurable'_condexp_ind_smul
- \- *lemma* measure_theory.ae_measurable'_of_ae_measurable'_trim
- \+ *lemma* measure_theory.ae_strongly_measurable'.add
- \+ *lemma* measure_theory.ae_strongly_measurable'.ae_eq_mk
- \+ *lemma* measure_theory.ae_strongly_measurable'.congr
- \+ *lemma* measure_theory.ae_strongly_measurable'.const_inner
- \+ *lemma* measure_theory.ae_strongly_measurable'.const_smul
- \+ *lemma* measure_theory.ae_strongly_measurable'.continuous_comp
- \+ *def* measure_theory.ae_strongly_measurable'.mk
- \+ *lemma* measure_theory.ae_strongly_measurable'.neg
- \+ *lemma* measure_theory.ae_strongly_measurable'.strongly_measurable_mk
- \+ *lemma* measure_theory.ae_strongly_measurable'.sub
- \+ *def* measure_theory.ae_strongly_measurable'
- \+ *lemma* measure_theory.ae_strongly_measurable'_condexp_L1
- \+ *lemma* measure_theory.ae_strongly_measurable'_condexp_L1_clm
- \+ *lemma* measure_theory.ae_strongly_measurable'_condexp_L2
- \+ *lemma* measure_theory.ae_strongly_measurable'_condexp_ind
- \+ *lemma* measure_theory.ae_strongly_measurable'_condexp_ind_smul
- \+ *lemma* measure_theory.ae_strongly_measurable'_of_ae_strongly_measurable'_trim
- \- *lemma* measure_theory.condexp_L1_clm_of_ae_measurable'
- \+ *lemma* measure_theory.condexp_L1_clm_of_ae_strongly_measurable'
- \- *lemma* measure_theory.condexp_L1_of_ae_measurable'
- \+ *lemma* measure_theory.condexp_L1_of_ae_strongly_measurable'
- \- *lemma* measure_theory.condexp_of_measurable
- \+ *lemma* measure_theory.condexp_of_strongly_measurable
- \+/\- *lemma* measure_theory.inner_condexp_L2_eq_inner_fun
- \- *lemma* measure_theory.is_closed_ae_measurable'
- \+ *lemma* measure_theory.is_closed_ae_strongly_measurable'
- \- *lemma* measure_theory.is_complete_ae_measurable'
- \+ *lemma* measure_theory.is_complete_ae_strongly_measurable'
- \- *lemma* measure_theory.measurable.ae_measurable'
- \- *lemma* measure_theory.measurable_condexp
- \- *lemma* measure_theory.mem_Lp_meas_iff_ae_measurable'
- \+ *lemma* measure_theory.mem_Lp_meas_iff_ae_strongly_measurable'
- \+/\- *lemma* measure_theory.mem_Lp_meas_self
- \- *lemma* measure_theory.mem_Lp_meas_subgroup_iff_ae_measurable'
- \+ *lemma* measure_theory.mem_Lp_meas_subgroup_iff_ae_strongly_measurable'
- \+/\- *lemma* measure_theory.norm_condexp_L2_le_one
- \+ *lemma* measure_theory.strongly_measurable.ae_strongly_measurable'
- \+ *lemma* measure_theory.strongly_measurable_condexp

Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/function/convergence_in_measure.lean
- \+/\- *lemma* measure_theory.tendsto_in_measure_of_tendsto_Lp
- \+/\- *lemma* measure_theory.tendsto_in_measure_of_tendsto_ae
- \- *lemma* measure_theory.tendsto_in_measure_of_tendsto_ae_of_measurable
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_ae_of_strongly_measurable
- \+/\- *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm
- \- *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm_of_measurable
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm_of_strongly_measurable

Modified src/measure_theory/function/egorov.lean


Modified src/measure_theory/function/jacobian.lean


Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measurable_embedding.integrable_map_iff
- \+/\- *lemma* measure_theory.L1.ae_measurable_coe_fn
- \+ *lemma* measure_theory.L1.ae_strongly_measurable_coe_fn
- \+/\- *lemma* measure_theory.L1.measurable_coe_fn
- \+ *lemma* measure_theory.L1.strongly_measurable_coe_fn
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable_mk
- \+/\- *lemma* measure_theory.integrable.add'
- \+/\- *lemma* measure_theory.integrable.add
- \+/\- *lemma* measure_theory.integrable.ae_measurable
- \+ *lemma* measure_theory.integrable.ae_strongly_measurable
- \+/\- *lemma* measure_theory.integrable.comp_measurable
- \+/\- *lemma* measure_theory.integrable.congr'
- \+/\- *lemma* measure_theory.integrable.max_zero
- \+/\- *lemma* measure_theory.integrable.min_zero
- \+/\- *lemma* measure_theory.integrable.mono'
- \+/\- *lemma* measure_theory.integrable.mono
- \+/\- *lemma* measure_theory.integrable.neg
- \+/\- *lemma* measure_theory.integrable.norm
- \+/\- *lemma* measure_theory.integrable.prod_mk
- \+/\- *lemma* measure_theory.integrable.smul
- \+/\- *lemma* measure_theory.integrable.sub'
- \+/\- *lemma* measure_theory.integrable.sub
- \+/\- *lemma* measure_theory.integrable.trim
- \+/\- *lemma* measure_theory.integrable_congr'
- \+/\- *lemma* measure_theory.integrable_finset_sum
- \+/\- *lemma* measure_theory.integrable_map_measure
- \+/\- *lemma* measure_theory.integrable_neg_iff
- \+/\- *lemma* measure_theory.integrable_norm_iff
- \+/\- *lemma* measure_theory.integrable_of_forall_fin_meas_le'
- \+/\- *lemma* measure_theory.integrable_of_norm_sub_le
- \+/\- *lemma* measure_theory.integrable_smul_iff
- \+/\- *lemma* measure_theory.lintegral_edist_lt_top
- \+/\- *lemma* measure_theory.lintegral_edist_triangle
- \+/\- *lemma* measure_theory.lintegral_nnnorm_add
- \+/\- *lemma* measure_theory.lipschitz_with.integrable_comp_iff_of_antilipschitz
- \+/\- *lemma* measure_theory.measure_preserving.integrable_comp
- \+/\- *lemma* measure_theory.mem_ℒp.integrable
- \+/\- *lemma* measure_theory.tendsto_lintegral_norm_of_dominated_convergence

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/locally_integrable.lean


Modified src/measure_theory/function/lp_order.lean


Modified src/measure_theory/function/lp_space.lean
- \+/\- *lemma* bounded_continuous_function.coe_fn_to_Lp
- \+/\- *lemma* bounded_continuous_function.range_to_Lp
- \+/\- *def* bounded_continuous_function.to_Lp
- \+/\- *lemma* bounded_continuous_function.to_Lp_norm_le
- \+/\- *lemma* continuous_linear_map.smul_comp_Lp
- \+/\- *lemma* continuous_linear_map.smul_comp_LpL_apply
- \+/\- *lemma* continuous_map.coe_fn_to_Lp
- \+/\- *lemma* continuous_map.coe_to_Lp
- \+/\- *lemma* continuous_map.range_to_Lp
- \+/\- *def* continuous_map.to_Lp
- \+/\- *lemma* continuous_map.to_Lp_comp_to_continuous_map
- \+/\- *lemma* continuous_map.to_Lp_def
- \+/\- *lemma* measurable_embedding.mem_ℒp_map_measure_iff
- \+/\- *lemma* measurable_equiv.mem_ℒp_map_measure_iff
- \+/\- *lemma* measure_theory.Lp.cauchy_tendsto_of_tendsto
- \+/\- *lemma* measure_theory.Lp.mem_Lp_of_ae_le
- \+/\- *lemma* measure_theory.Lp.mem_Lp_of_ae_le_mul
- \+/\- *lemma* measure_theory.Lp.norm_le_mul_norm_of_ae_le_mul
- \+/\- *lemma* measure_theory.Lp.norm_le_norm_of_ae_le
- \+/\- *lemma* measure_theory.Lp.snorm'_lim_le_liminf_snorm'
- \+/\- *lemma* measure_theory.Lp.snorm_lim_le_liminf_snorm
- \+/\- *def* measure_theory.Lp
- \+/\- *lemma* measure_theory.ae_eq_zero_of_snorm'_eq_zero
- \+/\- *lemma* measure_theory.ess_sup_trim
- \+/\- *lemma* measure_theory.limsup_trim
- \+/\- *lemma* measure_theory.meas_ge_le_mul_pow_snorm
- \- *lemma* measure_theory.mem_ℒp.ae_measurable
- \+ *lemma* measure_theory.mem_ℒp.ae_strongly_measurable
- \+/\- *lemma* measure_theory.mem_ℒp.congr_norm
- \+/\- *lemma* measure_theory.mem_ℒp.const_mul
- \+/\- *lemma* measure_theory.mem_ℒp.const_smul
- \+/\- *lemma* measure_theory.mem_ℒp.norm_rpow
- \+/\- *lemma* measure_theory.mem_ℒp.of_bound
- \+/\- *lemma* measure_theory.mem_ℒp.of_le
- \+/\- *lemma* measure_theory.mem_ℒp.of_le_mul
- \+/\- *lemma* measure_theory.mem_ℒp_congr_norm
- \+/\- *lemma* measure_theory.mem_ℒp_map_measure_iff
- \+/\- *lemma* measure_theory.mem_ℒp_norm_iff
- \+/\- *lemma* measure_theory.mem_ℒp_top_of_bound
- \- *lemma* measure_theory.mem_ℒp_zero_iff_ae_measurable
- \+ *lemma* measure_theory.mem_ℒp_zero_iff_ae_strongly_measurable
- \+/\- *lemma* measure_theory.snorm'_add_le
- \+/\- *lemma* measure_theory.snorm'_add_lt_top_of_le_one
- \+/\- *lemma* measure_theory.snorm'_eq_zero_iff
- \+/\- *lemma* measure_theory.snorm'_smul_le_mul_snorm'
- \+/\- *lemma* measure_theory.snorm'_trim
- \+/\- *lemma* measure_theory.snorm_add_le
- \+/\- *lemma* measure_theory.snorm_eq_zero_iff
- \+/\- *lemma* measure_theory.snorm_ess_sup_map_measure
- \+/\- *lemma* measure_theory.snorm_ess_sup_trim
- \+/\- *lemma* measure_theory.snorm_map_measure
- \+/\- *lemma* measure_theory.snorm_sub_le
- \+/\- *lemma* measure_theory.snorm_trim
- \+/\- *lemma* measure_theory.snorm_trim_ae

Modified src/measure_theory/function/simple_func_dense.lean


Modified src/measure_theory/function/simple_func_dense_lp.lean
- \+ *lemma* measure_theory.simple_func.integrable_approx_on_range
- \- *lemma* measure_theory.simple_func.integrable_approx_on_univ
- \+/\- *lemma* measure_theory.simple_func.integrable_pair
- \+ *lemma* measure_theory.simple_func.mem_ℒp_approx_on_range
- \- *lemma* measure_theory.simple_func.mem_ℒp_approx_on_univ
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_range_L1_nnnorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_range_Lp
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_range_Lp_snorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_nnnorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp_snorm

Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/function/strongly_measurable_lp.lean
- \- *lemma* measure_theory.mem_ℒp.fin_strongly_measurable_of_measurable
- \+ *lemma* measure_theory.mem_ℒp.fin_strongly_measurable_of_strongly_measurable

Modified src/measure_theory/function/uniform_integrable.lean
- \+/\- *lemma* measure_theory.tendsto_Lp_of_tendsto_ae
- \+/\- *lemma* measure_theory.tendsto_Lp_of_tendsto_ae_of_meas
- \+/\- *lemma* measure_theory.tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* measure_theory.tendsto_in_measure_iff_tendsto_Lp
- \+/\- *lemma* measure_theory.unif_integrable_of'
- \+/\- *lemma* measure_theory.unif_integrable_of
- \+/\- *lemma* measure_theory.unif_integrable_of_tendsto_Lp
- \- *lemma* measure_theory.uniform_integrable.measurable
- \+/\- *lemma* measure_theory.uniform_integrable.mem_ℒp
- \+ *lemma* measure_theory.uniform_integrable.strongly_measurable
- \+/\- *lemma* measure_theory.uniform_integrable.unif_integrable
- \+/\- *def* measure_theory.uniform_integrable
- \+/\- *lemma* measure_theory.uniform_integrable_zero_meas

Modified src/measure_theory/group/fundamental_domain.lean


Modified src/measure_theory/group/integration.lean


Modified src/measure_theory/integral/average.lean


Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.L1.simple_func.integral_smul
- \+/\- *lemma* measure_theory.ae_eq_trim_iff
- \- *lemma* measure_theory.ae_eq_trim_of_measurable
- \+ *lemma* measure_theory.ae_eq_trim_of_strongly_measurable
- \+/\- *lemma* measure_theory.integral_dirac'
- \+/\- *lemma* measure_theory.integral_eq_lintegral_of_nonneg_ae
- \- *lemma* measure_theory.integral_map_of_measurable
- \+ *lemma* measure_theory.integral_map_of_strongly_measurable
- \- *lemma* measure_theory.integral_non_ae_measurable
- \+ *lemma* measure_theory.integral_non_ae_strongly_measurable
- \+/\- *lemma* measure_theory.integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* measure_theory.integral_smul
- \+/\- *lemma* measure_theory.integral_trim
- \+/\- *lemma* measure_theory.integral_trim_ae
- \+/\- *lemma* measure_theory.of_real_integral_norm_eq_lintegral_nnnorm
- \+/\- *lemma* measure_theory.tendsto_integral_approx_on_of_measurable
- \+ *lemma* measure_theory.tendsto_integral_approx_on_of_measurable_of_range_subset
- \- *lemma* measure_theory.tendsto_integral_approx_on_univ_of_measurable

Modified src/measure_theory/integral/circle_integral.lean
- \+/\- *lemma* circle_integrable.add
- \+/\- *lemma* circle_integrable.neg
- \+/\- *lemma* circle_integrable.out
- \+/\- *lemma* circle_integrable_iff
- \+/\- *lemma* continuous_on.circle_integrable'
- \+/\- *lemma* continuous_on.circle_integrable

Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/exp_decay.lean
- \+/\- *lemma* exp_neg_integrable_on_Ioi

Modified src/measure_theory/integral/integrable_on.lean
- \- *lemma* ae_measurable.measurable_at_filter_of_mem
- \+ *lemma* ae_strongly_measurable.strongly_measurable_at_filter_of_mem
- \+ *lemma* continuous.strongly_measurable_at_filter
- \+ *lemma* continuous_at.strongly_measurable_at_filter
- \+ *lemma* continuous_on.ae_strongly_measurable
- \+ *lemma* continuous_on.ae_strongly_measurable_of_is_separable
- \+ *lemma* continuous_on.integrable_at_nhds_within_of_is_separable
- \+ *lemma* continuous_on.strongly_measurable_at_filter
- \+ *lemma* continuous_on.strongly_measurable_at_filter_nhds_within
- \- *lemma* measurable_at_bot
- \- *def* measurable_at_filter
- \+/\- *lemma* measure_theory.integrable_indicator_const_Lp
- \+/\- *lemma* measure_theory.integrable_on_Lp_of_measure_ne_top
- \+/\- *lemma* measure_theory.integrable_on_singleton_iff
- \+ *lemma* strongly_measurable_at_bot
- \+ *def* strongly_measurable_at_filter

Modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* measure_theory.ae_cover.ae_strongly_measurable

Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* continuous.interval_integrable
- \+/\- *lemma* continuous_on.interval_integrable
- \+/\- *lemma* continuous_on.interval_integrable_of_Icc
- \+/\- *lemma* interval_integrable.add
- \+/\- *lemma* interval_integrable.mono_fun
- \+/\- *lemma* interval_integrable.neg
- \+/\- *lemma* interval_integrable.norm
- \+/\- *lemma* interval_integrable.smul
- \+/\- *lemma* interval_integrable.sub
- \- *lemma* interval_integral.integral_non_ae_measurable
- \- *lemma* interval_integral.integral_non_ae_measurable_of_le
- \+ *lemma* interval_integral.integral_non_ae_strongly_measurable
- \+ *lemma* interval_integral.integral_non_ae_strongly_measurable_of_le
- \+/\- *lemma* interval_integral.interval_integrable_iff_integrable_Icc_of_le
- \+/\- *lemma* interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae

Modified src/measure_theory/integral/periodic.lean


Modified src/measure_theory/integral/set_integral.lean
- \- *lemma* continuous.measurable_at_filter
- \- *lemma* continuous_at.measurable_at_filter
- \- *lemma* continuous_on.measurable_at_filter
- \- *lemma* continuous_on.measurable_at_filter_nhds_within
- \+/\- *lemma* measure_theory.integral_norm_eq_pos_sub_neg
- \+/\- *lemma* measure_theory.set_integral_eq_zero_of_forall_eq_zero
- \+/\- *lemma* measure_theory.set_integral_le_nonneg
- \+/\- *lemma* measure_theory.set_integral_nonpos_le
- \+/\- *lemma* measure_theory.set_integral_union_eq_left

Modified src/measure_theory/integral/set_to_l1.lean
- \+/\- *lemma* measure_theory.L1.simple_func.norm_eq_sum_mul
- \+/\- *lemma* measure_theory.L1.simple_func.set_to_L1s_smul
- \+/\- *lemma* measure_theory.continuous_L1_to_L1
- \- *lemma* measure_theory.set_to_fun_non_ae_measurable
- \+ *lemma* measure_theory.set_to_fun_non_ae_strongly_measurable
- \+/\- *lemma* measure_theory.set_to_fun_smul
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_mono
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_nonneg'
- \+/\- *lemma* measure_theory.simple_func.set_to_simple_func_smul

Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measure/with_density_vector_measure.lean


Modified src/probability/density.lean


Modified src/probability/martingale.lean
- \- *lemma* measure_theory.martingale.measurable
- \+ *lemma* measure_theory.martingale.strongly_measurable
- \- *lemma* measure_theory.submartingale.measurable
- \+ *lemma* measure_theory.submartingale.strongly_measurable
- \- *lemma* measure_theory.supermartingale.measurable
- \+ *lemma* measure_theory.supermartingale.strongly_measurable

Modified src/probability/stopping.lean
- \+/\- *lemma* measure_theory.adapted.add
- \+/\- *lemma* measure_theory.adapted.measurable_stopped_process_of_nat
- \+/\- *lemma* measure_theory.adapted.neg
- \+/\- *theorem* measure_theory.adapted.prog_measurable_of_continuous
- \+/\- *lemma* measure_theory.adapted.prog_measurable_of_nat
- \+/\- *lemma* measure_theory.adapted.smul
- \+/\- *lemma* measure_theory.adapted.stopped_process_of_nat
- \+/\- *lemma* measure_theory.filtration.adapted_natural
- \+/\- *def* measure_theory.filtration.natural
- \+/\- *lemma* measure_theory.prog_measurable_of_tendsto'
- \+/\- *lemma* measure_theory.prog_measurable_of_tendsto

Modified src/topology/metric_space/basic.lean




## [2022-03-30 02:20:21](https://github.com/leanprover-community/mathlib/commit/d28a163)
feat(linear_algebra/dual): define the algebraic dual pairing ([#12827](https://github.com/leanprover-community/mathlib/pull/12827))
We define the pairing of algebraic dual and show that it is nondegenerate.
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+ *lemma* linear_map.dual_pairing_nondegenerate
- \+ *def* module.dual_pairing
- \+ *lemma* module.dual_pairing_apply

Modified src/linear_algebra/sesquilinear_form.lean




## [2022-03-30 00:29:28](https://github.com/leanprover-community/mathlib/commit/c594e2b)
feat(algebra/ring/basic): neg_zero for distrib_neg ([#13049](https://github.com/leanprover-community/mathlib/pull/13049))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* neg_zero'



## [2022-03-30 00:29:27](https://github.com/leanprover-community/mathlib/commit/b446c49)
feat(set_theory/cardinal): bit lemmas for exponentiation ([#13010](https://github.com/leanprover-community/mathlib/pull/13010))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.power_bit0
- \+ *theorem* cardinal.power_bit1



## [2022-03-30 00:29:26](https://github.com/leanprover-community/mathlib/commit/92b29c7)
fix(tactic/norm_num): make norm_num user command match norm_num better ([#12667](https://github.com/leanprover-community/mathlib/pull/12667))
Corrects some issues with the `#norm_num` user command that prevented it from fully normalizing expressions. Also, adds `expr.norm_num`.
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2022-03-29 23:57:24](https://github.com/leanprover-community/mathlib/commit/523d177)
feat(combinatorics/simple_graph/regularity/energy): Energy of a partition ([#12958](https://github.com/leanprover-community/mathlib/pull/12958))
Define the energy of a partition.
#### Estimated changes
Added src/combinatorics/simple_graph/regularity/energy.lean
- \+ *def* finpartition.energy
- \+ *lemma* finpartition.energy_le_one
- \+ *lemma* finpartition.energy_nonneg



## [2022-03-29 23:24:55](https://github.com/leanprover-community/mathlib/commit/50903f0)
feat(algebra/algebra/unitization): define unitization of a non-unital algebra ([#12601](https://github.com/leanprover-community/mathlib/pull/12601))
Given a non-unital `R`-algebra `A` (given via the type classes `[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct the minimal unital `R`-algebra containing `A` as an ideal. This object `unitization R A` is a type synonym for `R × A` on which we place a different multiplicative structure, namely, `(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity is `(1, 0)`.
#### Estimated changes
Added src/algebra/algebra/unitization.lean
- \+ *lemma* unitization.alg_hom_ext'
- \+ *lemma* unitization.alg_hom_ext
- \+ *lemma* unitization.algebra_map_eq_inl
- \+ *lemma* unitization.algebra_map_eq_inl_comp
- \+ *lemma* unitization.algebra_map_eq_inl_hom
- \+ *lemma* unitization.algebra_map_eq_inl_ring_hom_comp
- \+ *lemma* unitization.coe_add
- \+ *def* unitization.coe_hom
- \+ *lemma* unitization.coe_injective
- \+ *lemma* unitization.coe_mul
- \+ *lemma* unitization.coe_mul_inl
- \+ *lemma* unitization.coe_neg
- \+ *def* unitization.coe_non_unital_alg_hom
- \+ *lemma* unitization.coe_smul
- \+ *lemma* unitization.coe_zero
- \+ *lemma* unitization.ext
- \+ *def* unitization.fst
- \+ *lemma* unitization.fst_add
- \+ *lemma* unitization.fst_coe
- \+ *def* unitization.fst_hom
- \+ *lemma* unitization.fst_inl
- \+ *lemma* unitization.fst_mul
- \+ *lemma* unitization.fst_neg
- \+ *lemma* unitization.fst_one
- \+ *lemma* unitization.fst_smul
- \+ *lemma* unitization.fst_zero
- \+ *lemma* unitization.ind
- \+ *def* unitization.inl
- \+ *lemma* unitization.inl_add
- \+ *lemma* unitization.inl_fst_add_coe_snd_eq
- \+ *lemma* unitization.inl_injective
- \+ *lemma* unitization.inl_mul
- \+ *lemma* unitization.inl_mul_coe
- \+ *lemma* unitization.inl_mul_inl
- \+ *lemma* unitization.inl_neg
- \+ *lemma* unitization.inl_one
- \+ *def* unitization.inl_ring_hom
- \+ *lemma* unitization.inl_smul
- \+ *lemma* unitization.inl_zero
- \+ *def* unitization.lift
- \+ *lemma* unitization.lift_symm_apply
- \+ *lemma* unitization.linear_map_ext
- \+ *def* unitization.snd
- \+ *lemma* unitization.snd_add
- \+ *lemma* unitization.snd_coe
- \+ *def* unitization.snd_hom
- \+ *lemma* unitization.snd_inl
- \+ *lemma* unitization.snd_mul
- \+ *lemma* unitization.snd_neg
- \+ *lemma* unitization.snd_one
- \+ *lemma* unitization.snd_smul
- \+ *lemma* unitization.snd_zero
- \+ *def* unitization



## [2022-03-29 20:37:44](https://github.com/leanprover-community/mathlib/commit/119eb05)
chore(ring_theory/valuation/basic): fix valuation_apply ([#13045](https://github.com/leanprover-community/mathlib/pull/13045))
Follow-up to [#12914](https://github.com/leanprover-community/mathlib/pull/12914).
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* add_valuation.valuation_apply



## [2022-03-29 20:37:43](https://github.com/leanprover-community/mathlib/commit/e4c6449)
feat(algebra/module): `sub_mem_iff_left` and `sub_mem_iff_right` ([#13043](https://github.com/leanprover-community/mathlib/pull/13043))
Since it's a bit of a hassle to rewrite `add_mem_iff_left` and `add_mem_iff_right` to subtraction, I made a new pair of lemmas.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.sub_mem_iff_left
- \+ *lemma* submodule.sub_mem_iff_right



## [2022-03-29 20:37:42](https://github.com/leanprover-community/mathlib/commit/9aec6df)
feat(algebra/algebra/tower): `span A s = span R s` if `R → A` is surjective ([#13042](https://github.com/leanprover-community/mathlib/pull/13042))
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* algebra.coe_span_eq_span_of_surjective
- \+ *lemma* algebra.span_restrict_scalars_eq_span_of_surjective



## [2022-03-29 18:32:04](https://github.com/leanprover-community/mathlib/commit/d3684bc)
feat(category_theory/abelian): constructor in terms of coimage-image comparison ([#12972](https://github.com/leanprover-community/mathlib/pull/12972))
The "stacks constructor" for an abelian category, following https://stacks.math.columbia.edu/tag/0109.
I also factored out the canonical morphism from the abelian coimage to the abelian image (which exists whether or not the category is abelian), and reformulated `abelian.coimage_iso_image` in terms of an `is_iso` instance for this morphism.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \- *lemma* category_theory.abelian.full_image_factorisation
- \+ *lemma* category_theory.abelian.of_coimage_image_comparison_is_iso.has_images
- \+ *def* category_theory.abelian.of_coimage_image_comparison_is_iso.image_factorisation
- \+ *def* category_theory.abelian.of_coimage_image_comparison_is_iso.image_mono_factorisation
- \+ *lemma* category_theory.abelian.of_coimage_image_comparison_is_iso.image_mono_factorisation_e'
- \+ *def* category_theory.abelian.of_coimage_image_comparison_is_iso.normal_epi_category
- \+ *def* category_theory.abelian.of_coimage_image_comparison_is_iso.normal_mono_category
- \+ *def* category_theory.abelian.of_coimage_image_comparison_is_iso

Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/abelian/images.lean
- \+ *def* category_theory.abelian.coimage_image_comparison'
- \+ *def* category_theory.abelian.coimage_image_comparison
- \+ *lemma* category_theory.abelian.coimage_image_comparison_eq_coimage_image_comparison'
- \+ *lemma* category_theory.abelian.coimage_image_factorisation

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.has_zero_object_of_has_finite_biproducts

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.mono_factorisation.kernel_ι_comp

Modified src/data/fin/basic.lean
- \+ *def* fin.elim0'



## [2022-03-29 17:44:57](https://github.com/leanprover-community/mathlib/commit/e92ecff)
feat(algebra/direct_sum/module): link `direct_sum.submodule_is_internal` to `is_compl` ([#12671](https://github.com/leanprover-community/mathlib/pull/12671))
This is then used to show the even and odd components of a clifford algebra are complementary.
#### Estimated changes
Modified src/algebra/direct_sum/module.lean
- \+ *lemma* direct_sum.submodule_is_internal.is_compl
- \+ *lemma* direct_sum.submodule_is_internal_iff_is_compl

Modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* clifford_algebra.even_odd_is_compl



## [2022-03-29 17:11:21](https://github.com/leanprover-community/mathlib/commit/90f0bee)
chore(analysis/normed_space/exponential): fix lemma names in docstrings ([#13032](https://github.com/leanprover-community/mathlib/pull/13032))
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean




## [2022-03-29 14:38:00](https://github.com/leanprover-community/mathlib/commit/993d576)
chore(data/list/pairwise): add `pairwise_bind` ([#13030](https://github.com/leanprover-community/mathlib/pull/13030))
#### Estimated changes
Modified src/data/list/pairwise.lean
- \+ *lemma* list.pairwise_bind



## [2022-03-29 14:37:59](https://github.com/leanprover-community/mathlib/commit/8999813)
chore(data/list): two lemmas about bind ([#13029](https://github.com/leanprover-community/mathlib/pull/13029))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.bind_congr

Modified src/data/list/join.lean
- \+ *lemma* list.bind_eq_nil



## [2022-03-29 14:37:58](https://github.com/leanprover-community/mathlib/commit/cedf022)
feat(ring_theory/valuation/basic): add add_valuation.valuation ([#12914](https://github.com/leanprover-community/mathlib/pull/12914))
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+ *def* add_valuation.valuation
- \+ *lemma* add_valuation.valuation_apply



## [2022-03-29 13:10:46](https://github.com/leanprover-community/mathlib/commit/84b8b0d)
chore(topology/vector_bundle): fix timeout by optimizing proof ([#13026](https://github.com/leanprover-community/mathlib/pull/13026))
This PR speeds up a big and slow definition using `simp only` and `convert` → `refine`. This declaration seems to be on the edge of timing out and some other changes like [#11750](https://github.com/leanprover-community/mathlib/pull/11750) tripped it up.
Time saved if I run it with timeouts disabled:
 * master 14.8s → 6.3s
 * [#11750](https://github.com/leanprover-community/mathlib/pull/11750) 14.2s → 6.12s
#### Estimated changes
Modified src/topology/vector_bundle.lean




## [2022-03-29 13:10:45](https://github.com/leanprover-community/mathlib/commit/d5fee32)
chore(algebra/field_power): slightly simplify proof of min_le_of_zpow_le_max ([#13023](https://github.com/leanprover-community/mathlib/pull/13023))
#### Estimated changes
Modified src/algebra/field_power.lean




## [2022-03-29 13:10:44](https://github.com/leanprover-community/mathlib/commit/541c80d)
feat(group_theory/index): Golf proof of `relindex_eq_zero_of_le_left` ([#13014](https://github.com/leanprover-community/mathlib/pull/13014))
This PR uses `relindex_dvd_of_le_left` to golf the proof of `relindex_eq_zero_of_le_left`.
#### Estimated changes
Modified src/group_theory/index.lean




## [2022-03-29 13:10:43](https://github.com/leanprover-community/mathlib/commit/e109c8f)
feat(topology): basis for `𝓤 C(α, β)` and convergence of a series of `f : C(α, β)` ([#11229](https://github.com/leanprover-community/mathlib/pull/11229))
* add `filter.has_basis.compact_convergence_uniformity`;
* add a few facts about `compacts X`;
* add `summable_of_locally_summable_norm`.
#### Estimated changes
Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_map.summable_of_locally_summable_norm

Modified src/topology/sets/compacts.lean


Modified src/topology/uniform_space/compact_convergence.lean
- \+ *lemma* continuous_map.has_basis_compact_convergence_uniformity_aux
- \+ *lemma* filter.has_basis.compact_convergence_uniformity



## [2022-03-29 11:26:23](https://github.com/leanprover-community/mathlib/commit/66509e1)
feat(data/polynomial/div): `a - b ∣ p.eval a - p.eval b` ([#13021](https://github.com/leanprover-community/mathlib/pull/13021))
#### Estimated changes
Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.sub_dvd_eval_sub



## [2022-03-29 11:26:22](https://github.com/leanprover-community/mathlib/commit/111d3a4)
chore(data/polynomial/eval): golf two proofs involving evals ([#13020](https://github.com/leanprover-community/mathlib/pull/13020))
I shortened two proofs involving `eval/eval₂/comp`.
#### Estimated changes
Modified src/data/polynomial/eval.lean




## [2022-03-29 11:26:21](https://github.com/leanprover-community/mathlib/commit/b87c267)
feat(topology/algebra/group): add small topology lemma ([#12931](https://github.com/leanprover-community/mathlib/pull/12931))
Adds a small topology lemma by splitting `compact_open_separated_mul` into `compact_open_separated_mul_left/right`, which was useful in my proof of `Steinhaus theorem` (see [#12932](https://github.com/leanprover-community/mathlib/pull/12932)), as in a non-abelian group, the current version was not sufficient.
#### Estimated changes
Modified src/algebra/ring/opposite.lean


Modified src/data/set/pointwise.lean
- \+ *lemma* set.image_op_mul

Modified src/measure_theory/measure/haar.lean


Modified src/topology/algebra/group.lean
- \- *lemma* compact_open_separated_mul
- \+ *lemma* compact_open_separated_mul_left
- \+ *lemma* compact_open_separated_mul_right

Modified src/topology/algebra/ring.lean




## [2022-03-29 09:36:12](https://github.com/leanprover-community/mathlib/commit/89c8112)
feat(topology/algebra/monoid): `finprod` is eventually equal to `finset.prod` ([#13013](https://github.com/leanprover-community/mathlib/pull/13013))
Motivated by https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Using.20partitions.20of.20unity
#### Estimated changes
Modified src/geometry/manifold/algebra/monoid.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* finprod_eventually_eq_prod
- \+ *lemma* locally_finite.exists_finset_mul_support



## [2022-03-29 09:36:11](https://github.com/leanprover-community/mathlib/commit/545c265)
feat(data/polynomial/derivative): if `p` is a polynomial, then `p.derivative.nat_degree ≤ p.nat_degree - 1` ([#12948](https://github.com/leanprover-community/mathlib/pull/12948))
I also golfed the proof that `p.derivative.nat_degree ≤ p.nat_degree`.
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.nat_degree_derivative_le
- \- *theorem* polynomial.nat_degree_derivative_le



## [2022-03-29 09:36:10](https://github.com/leanprover-community/mathlib/commit/4bf4d9d)
feat(ring_theory/dedekind_domain/adic_valuation): add adic valuation on a Dedekind domain ([#12712](https://github.com/leanprover-community/mathlib/pull/12712))
Given a Dedekind domain R of Krull dimension 1 and a maximal ideal v of R, we define the
v-adic valuation on R and prove some of its properties, including the existence of uniformizers.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* with_zero.le_max_iff
- \+ *lemma* with_zero.min_le_iff

Added src/ring_theory/dedekind_domain/adic_valuation.lean
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation.le_max_iff_min_le
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation.map_add_le_max'
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation.map_mul'
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation.map_one'
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation.map_zero'
- \+ *def* is_dedekind_domain.height_one_spectrum.int_valuation
- \+ *def* is_dedekind_domain.height_one_spectrum.int_valuation_def
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_def_if_neg
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_def_if_pos
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_le_one
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_le_pow_iff_dvd
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_lt_one_iff_dvd
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_ne_zero'
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_ne_zero
- \+ *lemma* is_dedekind_domain.height_one_spectrum.int_valuation_zero_le

Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* associates.le_singleton_iff
- \- *lemma* is_dedekind_domain.height_one_spectrum.associates.irreducible
- \+ *lemma* is_dedekind_domain.height_one_spectrum.associates_irreducible

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* associates.mk_ne_zero'



## [2022-03-29 09:36:08](https://github.com/leanprover-community/mathlib/commit/1ffd04c)
feat(analysis/locally_convex): add balanced hull and core ([#12537](https://github.com/leanprover-community/mathlib/pull/12537))
#### Estimated changes
Added src/analysis/locally_convex/balanced_core_hull.lean
- \+ *lemma* balanced.hull_subset_of_subset
- \+ *lemma* balanced.subset_core_of_subset
- \+ *def* balanced_core
- \+ *def* balanced_core_aux
- \+ *lemma* balanced_core_aux_balanced
- \+ *lemma* balanced_core_aux_empty
- \+ *lemma* balanced_core_aux_maximal
- \+ *lemma* balanced_core_aux_mem_iff
- \+ *lemma* balanced_core_aux_subset
- \+ *lemma* balanced_core_balanced
- \+ *lemma* balanced_core_eq_Inter
- \+ *lemma* balanced_core_mem_iff
- \+ *lemma* balanced_core_nonempty_iff
- \+ *lemma* balanced_core_subset
- \+ *lemma* balanced_core_subset_balanced_core_aux
- \+ *lemma* balanced_core_zero_mem
- \+ *lemma* balanced_hull.balanced
- \+ *def* balanced_hull
- \+ *lemma* balanced_hull_mem_iff
- \+ *lemma* smul_balanced_core_subset
- \+ *lemma* subset_balanced_hull



## [2022-03-29 07:35:13](https://github.com/leanprover-community/mathlib/commit/0f92307)
feat(data/list/chain): Simp lemma for `chain r a (l ++ b :: c :: m)` ([#12969](https://github.com/leanprover-community/mathlib/pull/12969))
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* list.chain_append_cons_cons



## [2022-03-29 07:35:12](https://github.com/leanprover-community/mathlib/commit/1cdbc35)
feat(order/hom/bounded): an order_iso maps top to top and bot to bot ([#12862](https://github.com/leanprover-community/mathlib/pull/12862))
#### Estimated changes
Modified src/order/hom/bounded.lean
- \+ *lemma* map_eq_bot_iff
- \+ *lemma* map_eq_top_iff



## [2022-03-29 07:35:11](https://github.com/leanprover-community/mathlib/commit/b535c2d)
feat(algebra/homology): three lemmas on homological complexes ([#12742](https://github.com/leanprover-community/mathlib/pull/12742))
#### Estimated changes
Modified src/algebra/homology/additive.lean
- \+ *lemma* chain_complex.map_chain_complex_of

Modified src/algebra/homology/differential_object.lean
- \+ *lemma* homological_complex.eq_to_hom_f'
- \- *lemma* homological_complex.eq_to_hom_f

Modified src/algebra/homology/homological_complex.lean
- \+ *lemma* homological_complex.eq_to_hom_f
- \+ *lemma* homological_complex.ext



## [2022-03-29 07:35:09](https://github.com/leanprover-community/mathlib/commit/1084cee)
feat(category_theory/bicategory/coherence): prove the coherence theorem for bicategories ([#12155](https://github.com/leanprover-community/mathlib/pull/12155))
#### Estimated changes
Added src/category_theory/bicategory/coherence.lean
- \+ *def* category_theory.free_bicategory.inclusion
- \+ *def* category_theory.free_bicategory.inclusion_map_comp_aux
- \+ *def* category_theory.free_bicategory.inclusion_path
- \+ *def* category_theory.free_bicategory.inclusion_path_aux
- \+ *def* category_theory.free_bicategory.normalize
- \+ *def* category_theory.free_bicategory.normalize_aux
- \+ *lemma* category_theory.free_bicategory.normalize_aux_congr
- \+ *lemma* category_theory.free_bicategory.normalize_aux_nil_comp
- \+ *def* category_theory.free_bicategory.normalize_equiv
- \+ *def* category_theory.free_bicategory.normalize_iso
- \+ *lemma* category_theory.free_bicategory.normalize_naturality
- \+ *def* category_theory.free_bicategory.normalize_unit_iso
- \+ *def* category_theory.free_bicategory.preinclusion

Modified src/category_theory/bicategory/free.lean
- \+/\- *lemma* category_theory.free_bicategory.comp_def
- \+/\- *lemma* category_theory.free_bicategory.id_def

Modified src/category_theory/bicategory/locally_discrete.lean


Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.dcongr_arg



## [2022-03-29 07:35:08](https://github.com/leanprover-community/mathlib/commit/7b8b8f1)
feat(set_theory/ordinal_arithmetic): Characterize principal multiplicative ordinals ([#11701](https://github.com/leanprover-community/mathlib/pull/11701))
Two lemmas were renamed in the process:
- `mul_lt_omega` → `principal_mul_omega`
- `opow_omega` → `principal_opow_omega`
Various others were moved to `principal.lean`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.mul_lt_omega
- \- *theorem* ordinal.mul_lt_omega_opow
- \- *theorem* ordinal.mul_omega
- \- *theorem* ordinal.mul_omega_dvd
- \+ *theorem* ordinal.mul_two
- \- *theorem* ordinal.opow_lt_omega
- \- *theorem* ordinal.opow_omega
- \+/\- *theorem* ordinal.sup_opow_nat

Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/principal.lean
- \+ *theorem* ordinal.mul_eq_opow_log_succ
- \+ *theorem* ordinal.mul_lt_omega_opow
- \+ *theorem* ordinal.mul_omega
- \+ *theorem* ordinal.mul_omega_dvd
- \+ *theorem* ordinal.mul_omega_opow_opow
- \+ *theorem* ordinal.opow_omega
- \- *theorem* ordinal.opow_principal_add_is_principal_add
- \+ *theorem* ordinal.opow_principal_add_of_principal_add
- \+ *theorem* ordinal.principal_add_iff_zero_or_omega_opow
- \- *theorem* ordinal.principal_add_iff_zero_or_omega_power
- \+ *theorem* ordinal.principal_add_of_principal_mul
- \+ *theorem* ordinal.principal_add_of_principal_mul_opow
- \+ *theorem* ordinal.principal_mul_iff_le_two_or_omega_opow_opow
- \+ *theorem* ordinal.principal_mul_iff_mul_left_eq
- \+ *theorem* ordinal.principal_mul_is_limit
- \+ *theorem* ordinal.principal_mul_of_le_two
- \+ *theorem* ordinal.principal_mul_omega
- \+ *theorem* ordinal.principal_mul_omega_opow_opow
- \+ *theorem* ordinal.principal_mul_one
- \+ *theorem* ordinal.principal_mul_two
- \+ *theorem* ordinal.principal_opow_omega



## [2022-03-29 05:57:42](https://github.com/leanprover-community/mathlib/commit/ce3cece)
feat(measure_theory/constructions/borel_space): add `borelize` tactic ([#12844](https://github.com/leanprover-community/mathlib/pull/12844))
#### Estimated changes
Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/box_integral/integrability.lean


Modified src/analysis/complex/abs_max.lean


Modified src/analysis/complex/liouville.lean


Modified src/analysis/complex/removable_singularity.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/metric_space/hausdorff_dimension.lean




## [2022-03-29 05:57:41](https://github.com/leanprover-community/mathlib/commit/5fb7b7b)
feat(set_theory/{ordinal_arithmetic, game/nim}): Minimum excluded ordinal ([#12659](https://github.com/leanprover-community/mathlib/pull/12659))
We define `mex` and `bmex`, and use the former to golf the proof of Sprague-Grundy.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \- *theorem* cardinal.mk_ordinal_out

Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.grundy_value_nim_add_nim
- \- *def* pgame.nonmoves
- \- *lemma* pgame.nonmoves_nonempty

Modified src/set_theory/ordinal.lean
- \+ *theorem* cardinal.mk_ordinal_out

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *def* ordinal.bmex
- \+ *theorem* ordinal.bmex_le_blsub
- \+ *theorem* ordinal.bmex_le_of_ne
- \+ *theorem* ordinal.bmex_lt_ord_succ_card
- \+ *theorem* ordinal.bmex_monotone
- \+ *theorem* ordinal.bmex_not_mem_brange
- \+ *theorem* ordinal.exists_of_lt_bmex
- \+ *theorem* ordinal.exists_of_lt_mex
- \- *theorem* ordinal.lsub_nmem_range
- \+ *theorem* ordinal.lsub_not_mem_range
- \+ *def* ordinal.mex
- \+ *theorem* ordinal.mex_le_lsub
- \+ *theorem* ordinal.mex_le_of_ne
- \+ *theorem* ordinal.mex_lt_ord_succ_mk
- \+ *theorem* ordinal.mex_monotone
- \+ *theorem* ordinal.mex_not_mem_range
- \+ *theorem* ordinal.ne_bmex
- \+ *theorem* ordinal.ne_mex
- \+ *theorem* ordinal.nonempty_compl_range



## [2022-03-29 04:19:18](https://github.com/leanprover-community/mathlib/commit/5fcad21)
feat(number_theory/frobenius_number): Frobenius numbers ([#9729](https://github.com/leanprover-community/mathlib/pull/9729))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mem_closure_pair

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.mem_closure_pair

Added src/number_theory/frobenius_number.lean
- \+ *def* is_frobenius_number
- \+ *theorem* is_frobenius_number_pair
- \+ *lemma* nat.coprime.mul_add_mul_ne_mul



## [2022-03-28 23:54:09](https://github.com/leanprover-community/mathlib/commit/7fea719)
feat(data/set/basic): Laws for n-ary image ([#13011](https://github.com/leanprover-community/mathlib/pull/13011))
Prove left/right commutativity, distributivity of `set.image2` in the style of `set.image2_assoc`. Also add `forall₃_imp` and `Exists₃.imp`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.image2_comm
- \+ *lemma* set.image2_eq_empty_iff
- \+ *lemma* set.image2_left_comm
- \+ *lemma* set.image2_nonempty_iff
- \+ *lemma* set.image2_right_comm
- \+ *lemma* set.image3_mono
- \+ *lemma* set.image_image2_distrib
- \+ *lemma* set.image_image2_distrib_left
- \+ *lemma* set.image_image2_distrib_right
- \+/\- *lemma* set.nonempty.image2

Modified src/logic/basic.lean
- \+/\- *lemma* Exists.imp
- \+/\- *lemma* Exists₂.imp
- \+ *lemma* Exists₃.imp
- \+/\- *lemma* exists₂_congr
- \+/\- *lemma* forall_imp
- \+/\- *lemma* forall₂_imp
- \+ *lemma* forall₃_imp



## [2022-03-28 23:54:08](https://github.com/leanprover-community/mathlib/commit/9480029)
chore(data/{nat,int,rat}/cast): add bundled version of `cast_id` lemmas ([#13001](https://github.com/leanprover-community/mathlib/pull/13001))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* int.cast_add_hom_int
- \+ *lemma* int.cast_ring_hom_int

Modified src/data/nat/cast.lean
- \+ *lemma* nat.cast_ring_hom_nat
- \+ *lemma* ring_hom.eq_nat_cast'

Modified src/data/rat/cast.lean
- \+ *lemma* rat.cast_hom_rat



## [2022-03-28 23:54:07](https://github.com/leanprover-community/mathlib/commit/8c9dee1)
feat(algebra/field_power): add min_le_of_zpow_le_max ([#12915](https://github.com/leanprover-community/mathlib/pull/12915))
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* min_le_of_zpow_le_max



## [2022-03-28 22:26:18](https://github.com/leanprover-community/mathlib/commit/223d9a1)
feat(group_theory/quotient_group): maps of quotients by powers of integers induced by group homomorphisms ([#12811](https://github.com/leanprover-community/mathlib/pull/12811))
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_group.equiv_quotient_zpow_of_equiv
- \+ *def* quotient_group.hom_quotient_zpow_of_hom
- \+ *lemma* quotient_group.hom_quotient_zpow_of_hom_right_inverse



## [2022-03-28 22:26:16](https://github.com/leanprover-community/mathlib/commit/1a2182c)
feat(group_theory/complement): Transversals as functions ([#12732](https://github.com/leanprover-community/mathlib/pull/12732))
This PR adds interpretations of transversals as functions mapping elements of `G` to the chosen coset representative.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.mem_left_transversals.inv_mul_to_fun_mem
- \+ *lemma* subgroup.mem_left_transversals.inv_to_fun_mul_mem
- \+ *lemma* subgroup.mem_left_transversals.mk'_to_equiv
- \+ *lemma* subgroup.mem_right_transversals.mk'_to_equiv
- \+ *lemma* subgroup.mem_right_transversals.mul_inv_to_fun_mem
- \+ *lemma* subgroup.mem_right_transversals.to_fun_mul_inv_mem



## [2022-03-28 20:38:27](https://github.com/leanprover-community/mathlib/commit/40b142e)
chore(analysis/*): move matrix definitions into their own file and generalize ([#13007](https://github.com/leanprover-community/mathlib/pull/13007))
This makes it much easier to relax the typeclasses as needed.
`norm_matrix_le_iff` has been renamed to `matrix.norm_le_iff`, the rest of the lemmas have just had their typeclass arguments weakened. No proofs have changed.
The `matrix.normed_space` instance is now of the form `normed_space R (matrix n m α)` instead of `normed_space α (matrix n m α)`.
#### Estimated changes
Added src/analysis/matrix.lean
- \+ *lemma* matrix.norm_entry_le_entrywise_sup_norm
- \+ *lemma* matrix.norm_le_iff
- \+ *lemma* matrix.norm_lt_iff

Modified src/analysis/normed/normed_field.lean
- \- *def* matrix.normed_group
- \- *def* matrix.semi_normed_group
- \- *lemma* norm_matrix_le_iff
- \- *lemma* norm_matrix_lt_iff

Modified src/analysis/normed_space/basic.lean
- \- *lemma* matrix.norm_entry_le_entrywise_sup_norm
- \- *def* matrix.normed_space

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/star/basic.lean
- \- *lemma* matrix.entrywise_sup_norm_star_eq_norm

Modified src/analysis/normed_space/star/matrix.lean
- \+ *lemma* matrix.entrywise_sup_norm_star_eq_norm

Modified src/number_theory/modular.lean




## [2022-03-28 20:38:26](https://github.com/leanprover-community/mathlib/commit/ea97ca6)
feat(group_theory/group_action): add `commute.smul_{left,right}[_iff]` lemmas ([#13003](https://github.com/leanprover-community/mathlib/pull/13003))
`(r • a) * b = b * (r • a)` follows trivially from `smul_mul_assoc` and `mul_smul_comm`
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* commute.smul_left
- \+ *lemma* commute.smul_right

Modified src/group_theory/group_action/group.lean
- \+ *lemma* commute.smul_left_iff
- \+ *lemma* commute.smul_left_iff₀
- \+ *lemma* commute.smul_right_iff
- \+ *lemma* commute.smul_right_iff₀



## [2022-03-28 20:38:25](https://github.com/leanprover-community/mathlib/commit/261a195)
feat(group_theory/group_action/opposite): Add `smul_eq_mul_unop` ([#12995](https://github.com/leanprover-community/mathlib/pull/12995))
This PR adds a simp-lemma `smul_eq_mul_unop`, similar to `op_smul_eq_mul` and `smul_eq_mul`.
#### Estimated changes
Modified src/group_theory/group_action/opposite.lean
- \+ *lemma* mul_opposite.smul_eq_mul_unop
- \+/\- *lemma* op_smul_eq_mul



## [2022-03-28 16:49:23](https://github.com/leanprover-community/mathlib/commit/6fe0c3b)
refactor(algebra/group/to_additive + files containing even/odd): move many lemmas involving even/odd to the same file ([#12882](https://github.com/leanprover-community/mathlib/pull/12882))
This is the first step in refactoring the definition of `even` to be the `to_additive` of `square`.
This PR simply gathers together many (though not all) lemmas that involve `even` or `odd` in their assumptions.  The choice of which lemmas to migrate to the file `algebra.parity` was dictated mostly by whether importing `algebra.parity` in the current home would create a cyclic import.
The only change that is not a simple shift from a file to another one is the addition in `to_additive` for support to change `square` in a multiplicative name to `even` in an additive name.
The change to the test file `test.ring` is due to the fact that the definition of `odd` was no longer imported by the file.
#### Estimated changes
Modified src/algebra/field_power.lean
- \- *lemma* abs_zpow_bit0
- \- *lemma* even.abs_zpow
- \- *lemma* even.zpow_abs
- \- *lemma* even.zpow_neg
- \- *lemma* even.zpow_nonneg
- \- *theorem* even.zpow_pos
- \- *theorem* odd.zpow_neg
- \- *theorem* odd.zpow_nonneg
- \- *theorem* odd.zpow_nonpos
- \- *theorem* odd.zpow_pos
- \- *lemma* zpow_bit0_abs

Modified src/algebra/group/to_additive.lean


Modified src/algebra/group_power/lemmas.lean
- \- *lemma* even.pow_abs
- \- *lemma* even.pow_nonneg
- \- *lemma* even.pow_pos
- \- *lemma* even.pow_pos_iff
- \- *lemma* odd.pow_neg
- \- *lemma* odd.pow_neg_iff
- \- *lemma* odd.pow_nonneg_iff
- \- *lemma* odd.pow_nonpos
- \- *lemma* odd.pow_nonpos_iff
- \- *lemma* odd.pow_pos_iff
- \- *lemma* odd.strict_mono_pow
- \- *lemma* pow_bit0_abs

Modified src/algebra/order/ring.lean
- \- *lemma* even_abs
- \- *lemma* odd_abs

Modified src/algebra/parity.lean
- \+ *lemma* abs_zpow_bit0
- \+ *lemma* even.abs_zpow
- \+ *lemma* even.pow_abs
- \+ *lemma* even.pow_nonneg
- \+ *lemma* even.pow_pos
- \+ *lemma* even.pow_pos_iff
- \+ *lemma* even.zpow_abs
- \+ *lemma* even.zpow_neg
- \+ *lemma* even.zpow_nonneg
- \+ *theorem* even.zpow_pos
- \+ *def* even
- \+ *lemma* even_abs
- \+ *lemma* even_bit0
- \+ *lemma* even_iff_two_dvd
- \+ *theorem* even_neg
- \+ *lemma* fintype.card_fin_even
- \+ *lemma* odd.neg
- \+ *lemma* odd.pow_neg
- \+ *lemma* odd.pow_neg_iff
- \+ *lemma* odd.pow_nonneg_iff
- \+ *lemma* odd.pow_nonpos
- \+ *lemma* odd.pow_nonpos_iff
- \+ *lemma* odd.pow_pos_iff
- \+ *lemma* odd.strict_mono_pow
- \+ *theorem* odd.zpow_neg
- \+ *theorem* odd.zpow_nonneg
- \+ *theorem* odd.zpow_nonpos
- \+ *theorem* odd.zpow_pos
- \+ *def* odd
- \+ *lemma* odd_abs
- \+ *lemma* odd_bit1
- \+ *lemma* odd_neg
- \+ *lemma* pow_bit0_abs
- \+ *lemma* range_two_mul
- \+ *lemma* range_two_mul_add_one
- \+ *lemma* zpow_bit0_abs

Modified src/algebra/ring/basic.lean
- \- *def* even
- \- *lemma* even_bit0
- \- *lemma* even_iff_two_dvd
- \- *theorem* even_neg
- \- *lemma* odd.neg
- \- *def* odd
- \- *lemma* odd_bit1
- \- *lemma* odd_neg
- \- *lemma* range_two_mul
- \- *lemma* range_two_mul_add_one

Modified src/data/fintype/basic.lean
- \- *lemma* fintype.card_fin_even

Modified src/data/nat/prime.lean


Modified test/ring.lean




## [2022-03-28 16:49:22](https://github.com/leanprover-community/mathlib/commit/958f6b0)
refactor(measure_theory/group/fundamental_domain): allow `null_measurable_set`s ([#12005](https://github.com/leanprover-community/mathlib/pull/12005))
#### Estimated changes
Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.image_of_equiv
- \+ *lemma* measure_theory.is_fundamental_domain.lintegral_eq_tsum
- \- *lemma* measure_theory.is_fundamental_domain.measurable_set_smul
- \+/\- *lemma* measure_theory.is_fundamental_domain.mk'
- \+/\- *lemma* measure_theory.is_fundamental_domain.null_measurable_set_smul
- \+/\- *lemma* measure_theory.is_fundamental_domain.pairwise_ae_disjoint_of_ac
- \+ *lemma* measure_theory.is_fundamental_domain.preimage_of_equiv
- \+ *lemma* measure_theory.is_fundamental_domain.restrict_restrict
- \+ *lemma* measure_theory.is_fundamental_domain.smul
- \+ *lemma* measure_theory.is_fundamental_domain.smul_of_comm
- \+ *lemma* measure_theory.is_fundamental_domain.sum_restrict

Modified src/measure_theory/integral/periodic.lean


Modified src/measure_theory/measure/haar_quotient.lean
- \- *lemma* measure_theory.is_fundamental_domain.smul



## [2022-03-28 15:03:16](https://github.com/leanprover-community/mathlib/commit/abaabc8)
chore(algebra/group_power/lemmas): turn `[zn]smul` lemmas into instances ([#13002](https://github.com/leanprover-community/mathlib/pull/13002))
This adds new instances such that:
* `mul_[zn]smul_assoc` is `←smul_mul_assoc`
* `mul_[zn]smul_left` is `←mul_smul_comm`
This also makes `noncomm_ring` slightly smarter, and able to handle scalar actions by `nat`.
Thanks to Christopher, this generalizes these instances to non-associative and non-unital rings.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \- *theorem* mul_nsmul_assoc
- \- *theorem* mul_nsmul_left
- \- *theorem* mul_zsmul_assoc
- \- *theorem* mul_zsmul_left

Modified src/tactic/noncomm_ring.lean


Modified test/noncomm_ring.lean




## [2022-03-28 15:03:14](https://github.com/leanprover-community/mathlib/commit/0e1387b)
feat(category_theory): the category of small categories has all small limits ([#12979](https://github.com/leanprover-community/mathlib/pull/12979))
#### Estimated changes
Modified src/category_theory/category/Cat.lean
- \+ *lemma* category_theory.Cat.comp_map
- \+ *lemma* category_theory.Cat.comp_obj
- \+ *lemma* category_theory.Cat.id_map

Added src/category_theory/category/Cat/limit.lean
- \+ *def* category_theory.Cat.has_limits.hom_diagram
- \+ *def* category_theory.Cat.has_limits.limit_cone
- \+ *def* category_theory.Cat.has_limits.limit_cone_X
- \+ *def* category_theory.Cat.has_limits.limit_cone_is_limit
- \+ *def* category_theory.Cat.has_limits.limit_cone_lift
- \+ *lemma* category_theory.Cat.has_limits.limit_π_hom_diagram_eq_to_hom

Modified src/category_theory/grothendieck.lean




## [2022-03-28 15:03:13](https://github.com/leanprover-community/mathlib/commit/31e5ae2)
feat(data/list/cycle): Define the empty cycle ([#12967](https://github.com/leanprover-community/mathlib/pull/12967))
Also clean the file up somewhat, and add various `simp` lemmas.
#### Estimated changes
Modified src/data/list/cycle.lean
- \+ *lemma* cycle.coe_eq_nil
- \+ *lemma* cycle.coe_nil
- \+ *lemma* cycle.coe_to_multiset
- \+ *lemma* cycle.empty_eq
- \+ *lemma* cycle.induction_on
- \+/\- *lemma* cycle.length_coe
- \+ *lemma* cycle.length_nil
- \+/\- *lemma* cycle.length_nontrivial
- \+/\- *lemma* cycle.length_reverse
- \+/\- *lemma* cycle.length_subsingleton_iff
- \+ *lemma* cycle.lists_coe
- \+ *lemma* cycle.lists_nil
- \+ *lemma* cycle.map_coe
- \+ *lemma* cycle.map_eq_nil
- \+ *lemma* cycle.map_nil
- \+/\- *lemma* cycle.mem_coe_iff
- \+/\- *lemma* cycle.mem_lists_iff_coe_eq
- \+/\- *lemma* cycle.mem_reverse_iff
- \+/\- *lemma* cycle.mk'_eq_coe
- \+/\- *lemma* cycle.mk_eq_coe
- \+/\- *lemma* cycle.next_mem
- \+ *def* cycle.nil
- \+ *lemma* cycle.nil_to_finset
- \+ *lemma* cycle.nil_to_multiset
- \+/\- *lemma* cycle.nodup.nontrivial_iff
- \+/\- *lemma* cycle.nodup_coe_iff
- \+ *lemma* cycle.nodup_nil
- \+/\- *lemma* cycle.nodup_reverse_iff
- \+/\- *lemma* cycle.nontrivial_reverse_iff
- \+ *lemma* cycle.not_mem_nil
- \+/\- *lemma* cycle.prev_mem
- \+/\- *lemma* cycle.reverse_coe
- \+ *lemma* cycle.reverse_nil
- \+/\- *lemma* cycle.reverse_reverse
- \+/\- *lemma* cycle.subsingleton.nodup
- \+ *lemma* cycle.subsingleton_nil
- \+/\- *lemma* cycle.subsingleton_reverse_iff



## [2022-03-28 14:30:41](https://github.com/leanprover-community/mathlib/commit/0c6f0c2)
feat(ring_theory/dedekind_domain/ideal): add lemmas about sup of ideal with irreducible ([#12859](https://github.com/leanprover-community/mathlib/pull/12859))
These results were originally in [#9345](https://github.com/leanprover-community/mathlib/pull/9345).
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* irreducible_pow_sup
- \+ *lemma* irreducible_pow_sup_of_ge
- \+ *lemma* irreducible_pow_sup_of_le
- \+/\- *lemma* prod_normalized_factors_eq_self



## [2022-03-28 11:39:00](https://github.com/leanprover-community/mathlib/commit/4ee988d)
chore(algebra/homology/homotopy): cleanup ([#12998](https://github.com/leanprover-community/mathlib/pull/12998))
Correcting a name and some whitespace.
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+/\- *def* homotopy.add
- \+ *lemma* prev_d_comp_right
- \- *lemma* to_prev'_comp_right



## [2022-03-28 11:38:59](https://github.com/leanprover-community/mathlib/commit/eba31b5)
feat(algebra/homology): some elementwise lemmas ([#12997](https://github.com/leanprover-community/mathlib/pull/12997))
#### Estimated changes
Modified src/algebra/homology/homological_complex.lean


Modified src/algebra/homology/image_to_kernel.lean


Modified src/category_theory/concrete_category/elementwise.lean


Modified src/category_theory/subobject/basic.lean


Modified src/category_theory/subobject/limits.lean




## [2022-03-28 11:38:58](https://github.com/leanprover-community/mathlib/commit/dacf049)
feat(algebra/*): coe_to_equiv_symm simp lemmas ([#12996](https://github.com/leanprover-community/mathlib/pull/12996))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.to_equiv_eq_coe

Modified src/algebra/hom/equiv.lean
- \+/\- *lemma* mul_equiv.coe_to_equiv
- \+ *lemma* mul_equiv.to_equiv_eq_coe

Modified src/algebra/module/equiv.lean
- \+ *lemma* linear_equiv.coe_to_equiv_symm

Modified src/group_theory/commensurable.lean




## [2022-03-28 11:38:57](https://github.com/leanprover-community/mathlib/commit/f0c15be)
feat(measure_theory/functions/strongly_measurable): almost everywhere strongly measurable functions ([#12985](https://github.com/leanprover-community/mathlib/pull/12985))
A function is almost everywhere strongly measurable if it is almost everywhere the pointwise limit of a sequence of simple functions. These are the functions that can be integrated in the most general version of the Bochner integral. As a prerequisite for the refactor of the Bochner integral, we define almost strongly measurable functions and build a comprehensive API for them, gathering in the file `strongly_measurable.lean` all facts that will be needed for the refactor. The API does not claim to be complete, but it is already pretty big.
#### Estimated changes
Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* ae_measurable.ae_strongly_measurable
- \+ *lemma* ae_strongly_measurable_Union_iff
- \+ *lemma* ae_strongly_measurable_add_measure_iff
- \+ *lemma* ae_strongly_measurable_congr
- \+ *lemma* ae_strongly_measurable_const_smul_iff
- \+ *lemma* ae_strongly_measurable_const_smul_iff₀
- \+ *lemma* ae_strongly_measurable_id
- \+ *lemma* ae_strongly_measurable_iff_ae_measurable
- \+ *theorem* ae_strongly_measurable_iff_ae_measurable_separable
- \+ *lemma* ae_strongly_measurable_indicator_iff
- \+ *lemma* ae_strongly_measurable_of_ae_strongly_measurable_trim
- \+ *lemma* ae_strongly_measurable_of_tendsto_ae
- \+ *lemma* ae_strongly_measurable_smul_const_iff
- \+ *lemma* ae_strongly_measurable_sum_measure_iff
- \+ *lemma* ae_strongly_measurable_union_iff
- \+ *lemma* ae_strongly_measurable_with_density_iff
- \+ *lemma* continuous.ae_strongly_measurable
- \+ *lemma* continuous.comp_ae_strongly_measurable
- \+ *lemma* continuous.comp_strongly_measurable
- \+ *lemma* continuous.strongly_measurable
- \+ *lemma* embedding.ae_strongly_measurable_comp_iff
- \+ *lemma* embedding.comp_strongly_measurable_iff
- \+ *lemma* exists_strongly_measurable_limit_of_tendsto_ae
- \+ *lemma* finset.ae_strongly_measurable_prod'
- \+ *lemma* finset.ae_strongly_measurable_prod
- \+ *lemma* finset.strongly_measurable_prod'
- \+ *lemma* finset.strongly_measurable_prod
- \+ *lemma* list.ae_strongly_measurable_prod'
- \+ *lemma* list.ae_strongly_measurable_prod
- \+ *lemma* list.strongly_measurable_prod'
- \+ *lemma* list.strongly_measurable_prod
- \+ *lemma* measurable.ae_strongly_measurable
- \+/\- *lemma* measurable.strongly_measurable
- \+ *lemma* measurable_embedding.ae_strongly_measurable_map_iff
- \+ *lemma* measurable_embedding.exists_strongly_measurable_extend
- \+ *lemma* measurable_embedding.strongly_measurable_extend
- \+ *lemma* measure_theory.ae_measurable_zero_measure
- \+ *lemma* measure_theory.ae_strongly_measurable.add_measure
- \+ *lemma* measure_theory.ae_strongly_measurable.ae_eq_mk
- \+ *lemma* measure_theory.ae_strongly_measurable.ae_mem_imp_eq_mk
- \+ *lemma* measure_theory.ae_strongly_measurable.apply_continuous_linear_map
- \+ *lemma* measure_theory.ae_strongly_measurable.comp_measurable
- \+ *lemma* measure_theory.ae_strongly_measurable.congr
- \+ *lemma* measure_theory.ae_strongly_measurable.is_separable_ae_range
- \+ *lemma* measure_theory.ae_strongly_measurable.measurable_mk
- \+ *lemma* measure_theory.ae_strongly_measurable.mono_measure
- \+ *lemma* measure_theory.ae_strongly_measurable.mono_set
- \+ *lemma* measure_theory.ae_strongly_measurable.smul_measure
- \+ *lemma* measure_theory.ae_strongly_measurable.strongly_measurable_mk
- \+ *lemma* measure_theory.ae_strongly_measurable.sum_measure
- \+ *def* measure_theory.ae_strongly_measurable
- \+ *lemma* measure_theory.ae_strongly_measurable_const
- \+ *lemma* measure_theory.ae_strongly_measurable_one
- \+/\- *lemma* measure_theory.measurable_uncurry_of_continuous_of_measurable
- \+ *lemma* measure_theory.measure_preserving.ae_strongly_measurable_comp_iff
- \+ *lemma* measure_theory.simple_func.ae_strongly_measurable
- \+ *lemma* measure_theory.strongly_measurable.ae_strongly_measurable
- \+ *lemma* measure_theory.strongly_measurable.comp_measurable
- \+ *lemma* measure_theory.strongly_measurable.const_mul
- \+ *lemma* measure_theory.strongly_measurable.is_separable_range
- \+ *lemma* measure_theory.strongly_measurable.measurable_set_eq_fun
- \+ *lemma* measure_theory.strongly_measurable.measurable_set_le
- \+ *lemma* measure_theory.strongly_measurable.measurable_set_lt
- \+ *lemma* measure_theory.strongly_measurable.measurable_set_mul_support
- \+ *lemma* measure_theory.strongly_measurable.mul_const
- \+ *lemma* measure_theory.strongly_measurable.of_uncurry_left
- \+ *lemma* measure_theory.strongly_measurable.of_uncurry_right
- \+ *lemma* measure_theory.strongly_measurable.separable_space_range_union_singleton
- \+ *lemma* measure_theory.strongly_measurable_const'
- \- *lemma* measure_theory.strongly_measurable_id
- \- *lemma* measure_theory.strongly_measurable_iff_measurable
- \+ *lemma* measure_theory.strongly_measurable_of_is_empty
- \+ *lemma* measure_theory.strongly_measurable_one
- \+ *lemma* measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable
- \+ *lemma* measure_theory.subsingleton.ae_strongly_measurable'
- \+ *lemma* measure_theory.subsingleton.ae_strongly_measurable
- \+ *lemma* measure_theory.subsingleton.strongly_measurable'
- \+/\- *lemma* measure_theory.subsingleton.strongly_measurable
- \+ *lemma* multiset.ae_strongly_measurable_prod'
- \+ *lemma* multiset.ae_strongly_measurable_prod
- \+ *lemma* multiset.strongly_measurable_prod'
- \+ *lemma* multiset.strongly_measurable_prod
- \+ *lemma* strongly_measurable.apply_continuous_linear_map
- \+ *lemma* strongly_measurable_const_smul_iff
- \+ *lemma* strongly_measurable_const_smul_iff₀
- \+ *lemma* strongly_measurable_id
- \+ *lemma* strongly_measurable_iff_measurable
- \+ *theorem* strongly_measurable_iff_measurable_separable
- \+ *lemma* strongly_measurable_of_restrict_of_restrict_compl
- \+ *lemma* strongly_measurable_of_strongly_measurable_union_cover
- \+ *lemma* strongly_measurable_of_tendsto

Modified src/probability/stopping.lean
- \+/\- *theorem* measure_theory.adapted.prog_measurable_of_continuous



## [2022-03-28 11:38:56](https://github.com/leanprover-community/mathlib/commit/fd2c6c4)
chore(data/polynomial/ring_division): remove nontrivial assumptions ([#12984](https://github.com/leanprover-community/mathlib/pull/12984))
Additionally, this removes:
* some `polynomial.monic` assumptions that can be handled by casing instead
* the explicit `R` argument from `is_field.to_field R hR`
#### Estimated changes
Modified src/algebra/field/basic.lean
- \+ *lemma* is_field.nontrivial
- \+ *lemma* not_is_field_of_subsingleton

Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.nontrivial_iff

Modified src/data/polynomial/div.lean
- \+/\- *lemma* polynomial.not_is_field
- \+/\- *lemma* polynomial.sum_mod_by_monic_coeff

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.add_mod_by_monic
- \+/\- *lemma* polynomial.mod_by_monic_eq_of_dvd_sub
- \+/\- *def* polynomial.mod_by_monic_hom
- \+/\- *lemma* polynomial.smul_mod_by_monic

Modified src/field_theory/cardinality.lean


Modified src/field_theory/is_alg_closed/basic.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.mk_left_inverse
- \+/\- *lemma* adjoin_root.mk_surjective
- \+/\- *def* adjoin_root.mod_by_monic_hom
- \+/\- *lemma* adjoin_root.mod_by_monic_hom_mk
- \+/\- *def* adjoin_root.power_basis'
- \+/\- *def* adjoin_root.power_basis_aux'

Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization/basic.lean


Modified src/ring_theory/polynomial/basic.lean
- \+/\- *lemma* polynomial.ker_mod_by_monic_hom
- \+/\- *lemma* polynomial.mem_ker_mod_by_monic

Modified src/ring_theory/principal_ideal_domain.lean




## [2022-03-28 11:38:55](https://github.com/leanprover-community/mathlib/commit/c0421e7)
feat({ring_theory,group_theory}/localization): add some small lemmas for localisation API ([#12861](https://github.com/leanprover-community/mathlib/pull/12861))
Add the following:
* `sub_mk`: a/b - c/d = (ad - bc)/(bd)
* `mk_pow`: (a/b)^n = a^n/b^n
* `mk_int_cast`, `mk_nat_cast`: m = m/1 for integer/natural number m.
#### Estimated changes
Modified src/group_theory/monoid_localization.lean
- \+ *lemma* localization.mk_pow

Modified src/ring_theory/localization/basic.lean
- \+ *lemma* localization.mk_algebra_map
- \+ *lemma* localization.mk_int_cast
- \+ *lemma* localization.mk_nat_cast
- \+ *lemma* localization.sub_mk



## [2022-03-28 11:38:54](https://github.com/leanprover-community/mathlib/commit/1ebb206)
feat(ring_theory/localization): lemmas about `Frac(R)`-spans ([#12425](https://github.com/leanprover-community/mathlib/pull/12425))
A couple of lemmas relating spans in the localization of `R` to spans in `R` itself.
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* submodule.map_mem_span_algebra_map_image
- \+ *lemma* submodule.span_algebra_map_image
- \+ *lemma* submodule.span_algebra_map_image_of_tower

Modified src/ring_theory/localization/integral.lean
- \+ *lemma* is_fraction_ring.ideal_span_singleton_map_subset

Modified src/ring_theory/localization/submodule.lean
- \+ *lemma* is_localization.mem_span_iff
- \+ *lemma* is_localization.mem_span_map



## [2022-03-28 09:53:37](https://github.com/leanprover-community/mathlib/commit/e48f2e8)
doc(data/polynomial/field_division): fix broken docstring links ([#12981](https://github.com/leanprover-community/mathlib/pull/12981))
#### Estimated changes
Modified src/data/polynomial/field_division.lean




## [2022-03-28 09:53:36](https://github.com/leanprover-community/mathlib/commit/d31410a)
doc({linear_algebra,matrix}/charpoly): add crosslinks ([#12980](https://github.com/leanprover-community/mathlib/pull/12980))
This way someone coming from `undergrad.yaml` has an easy way to jump between the two statements.
#### Estimated changes
Modified src/linear_algebra/charpoly/basic.lean


Modified src/linear_algebra/matrix/charpoly/basic.lean




## [2022-03-28 09:53:35](https://github.com/leanprover-community/mathlib/commit/597cbf1)
feat(topology/continuous_on): add `set.maps_to.closure_of_continuous_on` ([#12975](https://github.com/leanprover-community/mathlib/pull/12975))
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+ *lemma* set.maps_to.closure_of_continuous_on
- \+ *lemma* set.maps_to.closure_of_continuous_within_at



## [2022-03-28 09:53:34](https://github.com/leanprover-community/mathlib/commit/ff72aa2)
feat(data/list/big_operators): add multiplicative versions ([#12966](https://github.com/leanprover-community/mathlib/pull/12966))
* add `list.length_pos_of_one_lt_prod`, generate
  `list.length_pos_of_sum_pos` using `to_additive`;
* add `list.length_pos_of_prod_lt_one` and its additive version.
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+ *lemma* list.length_pos_of_one_lt_prod
- \+ *lemma* list.length_pos_of_prod_lt_one
- \- *lemma* list.length_pos_of_sum_pos



## [2022-03-28 09:53:33](https://github.com/leanprover-community/mathlib/commit/443c239)
feat(data/polynomial/ring_division): `mem_root_set_iff` ([#12963](https://github.com/leanprover-community/mathlib/pull/12963))
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *theorem* polynomial.mem_root_set_iff'
- \+ *theorem* polynomial.mem_root_set_iff



## [2022-03-28 09:53:31](https://github.com/leanprover-community/mathlib/commit/162d83f)
chore(data/matrix/basic): square matrices over a non-unital ring form a non-unital ring ([#12913](https://github.com/leanprover-community/mathlib/pull/12913))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.conj_transpose_neg



## [2022-03-28 09:53:30](https://github.com/leanprover-community/mathlib/commit/c030dd2)
feat(set_theory/cardinal): `cardinal.to_nat` is order-preserving on finite cardinals ([#12763](https://github.com/leanprover-community/mathlib/pull/12763))
This PR proves that `cardinal.to_nat` is order-preserving on finite cardinals.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.to_nat_le_iff_le_of_lt_omega
- \+ *lemma* cardinal.to_nat_le_of_le_of_lt_omega
- \+ *lemma* cardinal.to_nat_lt_iff_lt_of_lt_omega
- \+ *lemma* cardinal.to_nat_lt_of_lt_of_lt_omega



## [2022-03-28 09:53:29](https://github.com/leanprover-community/mathlib/commit/2873b7a)
feat(set_theory/cofinality): Lemmas relating `cof` to `lsub` and `blsub` ([#12316](https://github.com/leanprover-community/mathlib/pull/12316))
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+ *theorem* ordinal.cof_blsub_le
- \+ *theorem* ordinal.cof_lsub_le
- \+ *theorem* ordinal.exists_blsub_cof
- \+ *theorem* ordinal.exists_lsub_cof
- \+ *theorem* ordinal.le_cof_iff_blsub
- \+ *theorem* ordinal.le_cof_iff_lsub
- \+ *theorem* ordinal.ord_cof_le



## [2022-03-28 09:53:28](https://github.com/leanprover-community/mathlib/commit/b7d6b3a)
feat(topology/continuous/algebra) : giving `C(α, M)` a `has_continuous_mul` and a `has_continuous_smul` structure ([#11261](https://github.com/leanprover-community/mathlib/pull/11261))
Here, `α` is a locally compact space.
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean




## [2022-03-28 08:03:19](https://github.com/leanprover-community/mathlib/commit/7711012)
feat(order/hom/*): equivalences mapping morphisms to their dual ([#12888](https://github.com/leanprover-community/mathlib/pull/12888))
Add missing `whatever_hom.dual` equivalences.
#### Estimated changes
Modified src/order/hom/basic.lean
- \+ *lemma* order_hom.dual_comp
- \+ *lemma* order_hom.dual_id
- \+ *lemma* order_hom.symm_dual_comp
- \+ *lemma* order_hom.symm_dual_id

Modified src/order/hom/bounded.lean
- \+ *lemma* bot_hom.dual_comp
- \+ *lemma* bot_hom.dual_id
- \+ *lemma* bot_hom.symm_dual_comp
- \+ *lemma* bot_hom.symm_dual_id
- \+ *lemma* bounded_order_hom.dual_comp
- \+ *lemma* bounded_order_hom.dual_id
- \+ *lemma* bounded_order_hom.symm_dual_comp
- \+ *lemma* bounded_order_hom.symm_dual_id
- \+ *lemma* top_hom.dual_comp
- \+ *lemma* top_hom.dual_id
- \+ *lemma* top_hom.symm_dual_comp
- \+ *lemma* top_hom.symm_dual_id

Modified src/order/hom/complete_lattice.lean
- \+ *lemma* Inf_hom.dual_comp
- \+ *lemma* Inf_hom.dual_id
- \+ *lemma* Inf_hom.symm_dual_comp
- \+ *lemma* Inf_hom.symm_dual_id
- \+ *lemma* Sup_hom.dual_comp
- \+ *lemma* Sup_hom.dual_id
- \+ *lemma* Sup_hom.symm_dual_comp
- \+ *lemma* Sup_hom.symm_dual_id
- \+ *lemma* complete_lattice_hom.dual_comp
- \+ *lemma* complete_lattice_hom.dual_id
- \+ *lemma* complete_lattice_hom.symm_dual_comp
- \+ *lemma* complete_lattice_hom.symm_dual_id

Modified src/order/hom/lattice.lean
- \+ *lemma* bounded_lattice_hom.dual_comp
- \+ *lemma* bounded_lattice_hom.dual_id
- \+ *lemma* bounded_lattice_hom.symm_dual_comp
- \+ *lemma* bounded_lattice_hom.symm_dual_id
- \+ *lemma* inf_hom.dual_comp
- \+ *lemma* inf_hom.dual_id
- \+ *lemma* inf_hom.symm_dual_comp
- \+ *lemma* inf_hom.symm_dual_id
- \+ *lemma* inf_top_hom.dual_comp
- \+ *lemma* inf_top_hom.dual_id
- \+ *lemma* inf_top_hom.symm_dual_comp
- \+ *lemma* inf_top_hom.symm_dual_id
- \+ *lemma* lattice_hom.dual_comp
- \+ *lemma* lattice_hom.dual_id
- \+ *lemma* lattice_hom.symm_dual_comp
- \+ *lemma* lattice_hom.symm_dual_id
- \+ *def* sup_bot_hom.dual
- \+ *lemma* sup_bot_hom.dual_comp
- \+ *lemma* sup_bot_hom.dual_id
- \+ *lemma* sup_bot_hom.symm_dual_comp
- \+ *lemma* sup_bot_hom.symm_dual_id
- \+ *lemma* sup_hom.dual_comp
- \+ *lemma* sup_hom.dual_id
- \+ *lemma* sup_hom.symm_dual_comp
- \+ *lemma* sup_hom.symm_dual_id



## [2022-03-28 06:13:19](https://github.com/leanprover-community/mathlib/commit/587af99)
chore(test/matrix): clean up an unused argument ([#12986](https://github.com/leanprover-community/mathlib/pull/12986))
these aren't caught by linters as examples don't generate declarations
#### Estimated changes
Modified test/matrix.lean




## [2022-03-28 06:13:17](https://github.com/leanprover-community/mathlib/commit/562bbf5)
feat(measure_theory/measure): add some simp lemmas, golf ([#12974](https://github.com/leanprover-community/mathlib/pull/12974))
* add `top_add`, `add_top`, `sub_top`, `zero_sub`, `sub_self`;
* golf the proof of `restrict_sub_eq_restrict_sub_restrict`.
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.add_top
- \+ *lemma* measure_theory.measure.top_add

Modified src/measure_theory/measure/sub.lean
- \+ *lemma* measure_theory.measure.sub_le_of_le_add
- \+ *lemma* measure_theory.measure.sub_self
- \+ *lemma* measure_theory.measure.sub_top
- \+ *lemma* measure_theory.measure.zero_sub



## [2022-03-28 06:13:16](https://github.com/leanprover-community/mathlib/commit/4b05a42)
feat(data/list/pairwise): `pairwise_of_forall_mem_list` ([#12968](https://github.com/leanprover-community/mathlib/pull/12968))
A relation holds pairwise on a list when it does on any two of its elements.
#### Estimated changes
Modified src/data/list/pairwise.lean
- \+ *lemma* list.pairwise_of_forall_mem_list



## [2022-03-28 06:13:15](https://github.com/leanprover-community/mathlib/commit/73a9c27)
chore(analysis/analytic/basic): golf ([#12965](https://github.com/leanprover-community/mathlib/pull/12965))
Golf a 1-line proof, drop an unneeded assumption.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* has_fpower_series_on_ball.sum



## [2022-03-28 06:13:14](https://github.com/leanprover-community/mathlib/commit/33afea8)
feat(analysis/normed_space): generalize some lemmas ([#12959](https://github.com/leanprover-community/mathlib/pull/12959))
* add `metric.closed_ball_zero'`, a version of `metric.closed_ball_zero` for a pseudo metric space;
* merge `metric.closed_ball_inf_dist_compl_subset_closure'` with `metric.closed_ball_inf_dist_compl_subset_closure`, drop an unneeded assumption `s ≠ univ`;
* assume `r ≠ 0` instead of `0 < r` in `closure_ball`, `frontier_ball`, and `euclidean.closure_ball`.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/complex/abs_max.lean


Modified src/analysis/inner_product_space/euclidean_dist.lean
- \+/\- *lemma* euclidean.closure_ball

Modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* closure_ball
- \+/\- *theorem* frontier_ball

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/riesz_lemma.lean
- \- *lemma* metric.closed_ball_inf_dist_compl_subset_closure'
- \+/\- *lemma* metric.closed_ball_inf_dist_compl_subset_closure

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.closed_ball_zero'
- \+/\- *theorem* metric.mem_of_closed'



## [2022-03-28 06:13:12](https://github.com/leanprover-community/mathlib/commit/c65d807)
feat(data/polynomial/erase_lead + data/polynomial/reverse): rename an old lemma, add a stronger one ([#12909](https://github.com/leanprover-community/mathlib/pull/12909))
Taking advantage of nat-subtraction in edge cases, a lemma that previously proved `x ≤ y` actually holds with `x ≤ y - 1`.
Thus, I renamed the old lemma to `original_name_aux` and `original_name` is now the name of the new lemma.  Since this lemma was used in a different file, I used the `_aux` name in the other file.
Note that the `_aux` lemma is currently an ingredient in the proof of the stronger lemma.  It may be possible to have a simple direct proof of the stronger one that avoids using the `_aux` lemma, but I have not given this any thought.
#### Estimated changes
Modified src/data/polynomial/erase_lead.lean
- \+/\- *lemma* polynomial.erase_lead_nat_degree_le
- \+ *lemma* polynomial.erase_lead_nat_degree_le_aux

Modified src/data/polynomial/reverse.lean




## [2022-03-28 06:13:11](https://github.com/leanprover-community/mathlib/commit/7a1e0f2)
feat(analysis/inner_product_space): an inner product space is strictly convex ([#12790](https://github.com/leanprover-community/mathlib/pull/12790))
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean




## [2022-03-28 05:04:36](https://github.com/leanprover-community/mathlib/commit/1e72d86)
chore(data/polynomial/degree/lemmas + data/polynomial/ring_division): move lemmas, reduce assumptions, golf ([#12858](https://github.com/leanprover-community/mathlib/pull/12858))
This PR takes advantage of the reduced assumptions that are a consequence of [#12854](https://github.com/leanprover-community/mathlib/pull/12854).  Again, I moved two lemmas from their current location to a different file, where the typeclass assumptions make more sense,
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.leading_coeff_comp
- \+ *lemma* polynomial.nat_degree_comp

Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/ring_division.lean
- \- *lemma* polynomial.leading_coeff_comp
- \- *lemma* polynomial.nat_degree_comp



## [2022-03-27 19:56:25](https://github.com/leanprover-community/mathlib/commit/e5cd2ea)
feat(analysis/von_neumann): concrete and abstract definitions of a von Neumann algebra ([#12329](https://github.com/leanprover-community/mathlib/pull/12329))
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean
- \+ *lemma* set.algebra_map_mem_centralizer
- \+ *def* subalgebra.centralizer
- \+ *lemma* subalgebra.centralizer_le
- \+ *lemma* subalgebra.centralizer_univ
- \+ *lemma* subalgebra.coe_centralizer
- \+ *lemma* subalgebra.mem_centralizer_iff

Added src/algebra/star/subalgebra.lean
- \+ *def* star_subalgebra.centralizer
- \+ *lemma* star_subalgebra.centralizer_le
- \+ *lemma* star_subalgebra.coe_centralizer
- \+ *lemma* star_subalgebra.mem_centralizer_iff
- \+ *structure* star_subalgebra

Modified src/analysis/inner_product_space/adjoint.lean


Added src/analysis/von_neumann_algebra/basic.lean
- \+ *structure* von_neumann_algebra

Modified src/group_theory/submonoid/basic.lean


Modified src/group_theory/submonoid/centralizer.lean
- \+ *lemma* submonoid.centralizer_le
- \- *lemma* submonoid.centralizer_subset
- \+/\- *lemma* submonoid.coe_centralizer

Modified src/ring_theory/subsemiring/basic.lean
- \+ *def* subsemiring.centralizer
- \+ *lemma* subsemiring.centralizer_le
- \+ *lemma* subsemiring.centralizer_to_submonoid
- \+ *lemma* subsemiring.centralizer_univ
- \+ *lemma* subsemiring.coe_centralizer
- \+ *lemma* subsemiring.mem_centralizer_iff



## [2022-03-27 15:52:15](https://github.com/leanprover-community/mathlib/commit/1494a9b)
feat(data/zmod/basic): add `int_coe_eq_int_coe_iff_dvd_sub` ([#12944](https://github.com/leanprover-community/mathlib/pull/12944))
This adds the following API lemma.
```
lemma int_coe_eq_int_coe_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : zmod c) = ↑b ↔ ↑c ∣ b-a
```
extending the already present version with b = 0. [(Zulip discussion)](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Missing.20zmod.20lemma.3F)
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.int_coe_eq_int_coe_iff_dvd_sub



## [2022-03-27 10:05:55](https://github.com/leanprover-community/mathlib/commit/d620ad3)
feat(measure_theory/measure/measure_space): remove measurable_set assumption in ae_measurable.subtype_mk ([#12978](https://github.com/leanprover-community/mathlib/pull/12978))
#### Estimated changes
Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_measurable.exists_ae_eq_range_subset
- \+/\- *lemma* ae_measurable.subtype_mk



## [2022-03-27 04:09:23](https://github.com/leanprover-community/mathlib/commit/2c6df07)
chore(model_theory/*): Split up big model theory files ([#12918](https://github.com/leanprover-community/mathlib/pull/12918))
Splits up `model_theory/basic` into `model_theory/basic`, `model_theory/language_maps`, and `model_theory/bundled`.
Splits up `model_theory/terms_and_formulas` into `model_theory/syntax`, `model_theory/semantics`, and `model_theory/satisfiability`.
Adds to the module docs of these files.
#### Estimated changes
Modified src/model_theory/basic.lean
- \- *def* first_order.language.Lequiv.add_empty_constants
- \- *structure* first_order.language.Lequiv
- \- *def* first_order.language.Lhom.add_constants
- \- *def* first_order.language.Lhom.comp
- \- *lemma* first_order.language.Lhom.comp_assoc
- \- *lemma* first_order.language.Lhom.comp_id
- \- *theorem* first_order.language.Lhom.comp_sum_elim
- \- *def* first_order.language.Lhom.constants_on_map
- \- *lemma* first_order.language.Lhom.id_comp
- \- *lemma* first_order.language.Lhom.map_constants_comp_sum_inl
- \- *lemma* first_order.language.Lhom.sum_elim_comp_inl
- \- *lemma* first_order.language.Lhom.sum_elim_comp_inr
- \- *theorem* first_order.language.Lhom.sum_elim_inl_inr
- \- *def* first_order.language.Lhom.sum_map
- \- *lemma* first_order.language.Lhom.sum_map_comp_inl
- \- *lemma* first_order.language.Lhom.sum_map_comp_inr
- \- *structure* first_order.language.Lhom
- \- *def* first_order.language.Lhom_with_constants
- \- *def* first_order.language.Lhom_with_constants_map
- \- *lemma* first_order.language.coe_con
- \- *def* first_order.language.constants_on.Structure
- \- *def* first_order.language.constants_on
- \- *lemma* first_order.language.constants_on_constants
- \- *def* first_order.language.constants_on_functions
- \- *lemma* first_order.language.constants_on_map_is_expansion_on
- \- *def* first_order.language.with_constants

Added src/model_theory/bundled.lean


Modified src/model_theory/definability.lean


Modified src/model_theory/elementary_maps.lean


Modified src/model_theory/fraisse.lean


Added src/model_theory/language_map.lean
- \+ *def* first_order.language.Lequiv.add_empty_constants
- \+ *structure* first_order.language.Lequiv
- \+ *def* first_order.language.Lhom.add_constants
- \+ *def* first_order.language.Lhom.comp
- \+ *lemma* first_order.language.Lhom.comp_assoc
- \+ *lemma* first_order.language.Lhom.comp_id
- \+ *theorem* first_order.language.Lhom.comp_sum_elim
- \+ *def* first_order.language.Lhom.constants_on_map
- \+ *lemma* first_order.language.Lhom.id_comp
- \+ *lemma* first_order.language.Lhom.map_constants_comp_sum_inl
- \+ *lemma* first_order.language.Lhom.sum_elim_comp_inl
- \+ *lemma* first_order.language.Lhom.sum_elim_comp_inr
- \+ *theorem* first_order.language.Lhom.sum_elim_inl_inr
- \+ *def* first_order.language.Lhom.sum_map
- \+ *lemma* first_order.language.Lhom.sum_map_comp_inl
- \+ *lemma* first_order.language.Lhom.sum_map_comp_inr
- \+ *structure* first_order.language.Lhom
- \+ *def* first_order.language.Lhom_with_constants
- \+ *def* first_order.language.Lhom_with_constants_map
- \+ *lemma* first_order.language.coe_con
- \+ *def* first_order.language.constants_on.Structure
- \+ *def* first_order.language.constants_on
- \+ *lemma* first_order.language.constants_on_constants
- \+ *def* first_order.language.constants_on_functions
- \+ *lemma* first_order.language.constants_on_map_is_expansion_on
- \+ *def* first_order.language.with_constants

Modified src/model_theory/quotients.lean


Added src/model_theory/satisfiability.lean
- \+ *def* first_order.language.Theory.is_finitely_satisfiable
- \+ *lemma* first_order.language.Theory.is_satisfiable.is_finitely_satisfiable
- \+ *lemma* first_order.language.Theory.is_satisfiable.mono
- \+ *def* first_order.language.Theory.is_satisfiable.some_model
- \+ *def* first_order.language.Theory.is_satisfiable
- \+ *theorem* first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable
- \+ *lemma* first_order.language.Theory.model.is_satisfiable
- \+ *def* first_order.language.Theory.models_bounded_formula
- \+ *lemma* first_order.language.Theory.models_formula_iff
- \+ *lemma* first_order.language.Theory.models_sentence_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.realize_bd_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.realize_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.refl
- \+ *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_bd_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.symm
- \+ *lemma* first_order.language.Theory.semantically_equivalent.trans
- \+ *def* first_order.language.Theory.semantically_equivalent
- \+ *def* first_order.language.Theory.semantically_equivalent_setoid
- \+ *lemma* first_order.language.bounded_formula.all_semantically_equivalent_not_ex_not
- \+ *lemma* first_order.language.bounded_formula.ex_semantically_equivalent_not_all_not
- \+ *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_not_sup
- \+ *lemma* first_order.language.bounded_formula.induction_on_all_ex
- \+ *lemma* first_order.language.bounded_formula.induction_on_exists_not
- \+ *lemma* first_order.language.bounded_formula.inf_semantically_equivalent_not_sup_not
- \+ *lemma* first_order.language.bounded_formula.is_qf.induction_on_inf_not
- \+ *lemma* first_order.language.bounded_formula.is_qf.induction_on_sup_not
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_all_lift_at
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_not_not
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_to_prenex
- \+ *lemma* first_order.language.bounded_formula.sup_semantically_equivalent_not_inf_not
- \+ *lemma* first_order.language.formula.imp_semantically_equivalent_not_sup
- \+ *lemma* first_order.language.formula.inf_semantically_equivalent_not_sup_not
- \+ *lemma* first_order.language.formula.semantically_equivalent_not_not
- \+ *lemma* first_order.language.formula.sup_semantically_equivalent_not_inf_not

Added src/model_theory/semantics.lean
- \+ *lemma* first_order.language.Lhom.on_Theory_model
- \+ *lemma* first_order.language.Lhom.realize_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.realize_on_formula
- \+ *lemma* first_order.language.Lhom.realize_on_sentence
- \+ *lemma* first_order.language.Lhom.realize_on_term
- \+ *lemma* first_order.language.Lhom.set_of_realize_on_formula
- \+ *lemma* first_order.language.Theory.model.mono
- \+ *lemma* first_order.language.Theory.realize_sentence_of_mem
- \+ *def* first_order.language.bounded_formula.realize
- \+ *lemma* first_order.language.bounded_formula.realize_all
- \+ *lemma* first_order.language.bounded_formula.realize_all_lift_at_one_self
- \+ *lemma* first_order.language.bounded_formula.realize_alls
- \+ *lemma* first_order.language.bounded_formula.realize_bd_equal
- \+ *lemma* first_order.language.bounded_formula.realize_bot
- \+ *lemma* first_order.language.bounded_formula.realize_cast_le_of_eq
- \+ *lemma* first_order.language.bounded_formula.realize_ex
- \+ *lemma* first_order.language.bounded_formula.realize_exs
- \+ *lemma* first_order.language.bounded_formula.realize_iff
- \+ *lemma* first_order.language.bounded_formula.realize_imp
- \+ *lemma* first_order.language.bounded_formula.realize_inf
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at_one
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at_one_self
- \+ *lemma* first_order.language.bounded_formula.realize_not
- \+ *lemma* first_order.language.bounded_formula.realize_rel
- \+ *lemma* first_order.language.bounded_formula.realize_relabel
- \+ *lemma* first_order.language.bounded_formula.realize_sup
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.realize_top
- \+ *lemma* first_order.language.embedding.realize_term
- \+ *lemma* first_order.language.equiv.realize_bounded_formula
- \+ *lemma* first_order.language.equiv.realize_formula
- \+ *lemma* first_order.language.equiv.realize_term
- \+ *def* first_order.language.formula.realize
- \+ *lemma* first_order.language.formula.realize_bot
- \+ *lemma* first_order.language.formula.realize_equal
- \+ *lemma* first_order.language.formula.realize_graph
- \+ *lemma* first_order.language.formula.realize_iff
- \+ *lemma* first_order.language.formula.realize_imp
- \+ *lemma* first_order.language.formula.realize_inf
- \+ *lemma* first_order.language.formula.realize_not
- \+ *lemma* first_order.language.formula.realize_rel
- \+ *lemma* first_order.language.formula.realize_relabel
- \+ *lemma* first_order.language.formula.realize_sup
- \+ *lemma* first_order.language.formula.realize_top
- \+ *lemma* first_order.language.hom.realize_term
- \+ *def* first_order.language.sentence.realize
- \+ *def* first_order.language.term.realize
- \+ *lemma* first_order.language.term.realize_con
- \+ *lemma* first_order.language.term.realize_constants
- \+ *lemma* first_order.language.term.realize_lift_at
- \+ *lemma* first_order.language.term.realize_relabel

Modified src/model_theory/substructures.lean


Added src/model_theory/syntax.lean
- \+ *def* first_order.language.Lequiv.on_bounded_formula
- \+ *lemma* first_order.language.Lequiv.on_bounded_formula_symm
- \+ *def* first_order.language.Lequiv.on_formula
- \+ *lemma* first_order.language.Lequiv.on_formula_apply
- \+ *lemma* first_order.language.Lequiv.on_formula_symm
- \+ *def* first_order.language.Lequiv.on_sentence
- \+ *def* first_order.language.Lequiv.on_term
- \+ *lemma* first_order.language.Lhom.comp_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.comp_on_term
- \+ *lemma* first_order.language.Lhom.id_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.id_on_term
- \+ *lemma* first_order.language.Lhom.mem_on_Theory
- \+ *def* first_order.language.Lhom.on_Theory
- \+ *def* first_order.language.Lhom.on_bounded_formula
- \+ *def* first_order.language.Lhom.on_formula
- \+ *def* first_order.language.Lhom.on_sentence
- \+ *def* first_order.language.Lhom.on_term
- \+ *def* first_order.language.Theory
- \+ *def* first_order.language.bounded_formula.alls
- \+ *def* first_order.language.bounded_formula.cast_le
- \+ *def* first_order.language.bounded_formula.exs
- \+ *lemma* first_order.language.bounded_formula.is_atomic.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_atomic.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_atomic.is_qf
- \+ *lemma* first_order.language.bounded_formula.is_atomic.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_atomic.relabel
- \+ *inductive* first_order.language.bounded_formula.is_atomic
- \+ *lemma* first_order.language.bounded_formula.is_prenex.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_prenex.induction_on_all_not
- \+ *lemma* first_order.language.bounded_formula.is_prenex.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_prenex.relabel
- \+ *inductive* first_order.language.bounded_formula.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.is_qf.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_qf.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_qf.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_qf.not
- \+ *lemma* first_order.language.bounded_formula.is_qf.relabel
- \+ *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp_right
- \+ *inductive* first_order.language.bounded_formula.is_qf
- \+ *lemma* first_order.language.bounded_formula.is_qf_bot
- \+ *def* first_order.language.bounded_formula.lift_at
- \+ *lemma* first_order.language.bounded_formula.not_all_is_atomic
- \+ *lemma* first_order.language.bounded_formula.not_all_is_qf
- \+ *lemma* first_order.language.bounded_formula.not_ex_is_atomic
- \+ *lemma* first_order.language.bounded_formula.not_ex_is_qf
- \+ *def* first_order.language.bounded_formula.relabel
- \+ *def* first_order.language.bounded_formula.relabel_aux
- \+ *lemma* first_order.language.bounded_formula.sum_elim_comp_relabel_aux
- \+ *def* first_order.language.bounded_formula.to_prenex
- \+ *def* first_order.language.bounded_formula.to_prenex_imp
- \+ *def* first_order.language.bounded_formula.to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.to_prenex_is_prenex
- \+ *inductive* first_order.language.bounded_formula
- \+ *def* first_order.language.constants.term
- \+ *def* first_order.language.formula.graph
- \+ *lemma* first_order.language.formula.is_atomic_graph
- \+ *def* first_order.language.formula.relabel
- \+ *def* first_order.language.formula
- \+ *def* first_order.language.relations.bounded_formula
- \+ *def* first_order.language.relations.formula
- \+ *def* first_order.language.sentence
- \+ *def* first_order.language.term.bd_equal
- \+ *theorem* first_order.language.term.card_le
- \+ *lemma* first_order.language.term.card_le_omega
- \+ *def* first_order.language.term.equal
- \+ *def* first_order.language.term.lift_at
- \+ *def* first_order.language.term.list_decode
- \+ *theorem* first_order.language.term.list_decode_encode_list
- \+ *def* first_order.language.term.list_encode
- \+ *lemma* first_order.language.term.list_encode_injective
- \+ *def* first_order.language.term.relabel
- \+ *inductive* first_order.language.term

Deleted src/model_theory/terms_and_formulas.lean
- \- *def* first_order.language.Lequiv.on_bounded_formula
- \- *lemma* first_order.language.Lequiv.on_bounded_formula_symm
- \- *def* first_order.language.Lequiv.on_formula
- \- *lemma* first_order.language.Lequiv.on_formula_apply
- \- *lemma* first_order.language.Lequiv.on_formula_symm
- \- *def* first_order.language.Lequiv.on_sentence
- \- *def* first_order.language.Lequiv.on_term
- \- *lemma* first_order.language.Lhom.comp_on_bounded_formula
- \- *lemma* first_order.language.Lhom.comp_on_term
- \- *lemma* first_order.language.Lhom.id_on_bounded_formula
- \- *lemma* first_order.language.Lhom.id_on_term
- \- *lemma* first_order.language.Lhom.mem_on_Theory
- \- *def* first_order.language.Lhom.on_Theory
- \- *lemma* first_order.language.Lhom.on_Theory_model
- \- *def* first_order.language.Lhom.on_bounded_formula
- \- *def* first_order.language.Lhom.on_formula
- \- *def* first_order.language.Lhom.on_sentence
- \- *def* first_order.language.Lhom.on_term
- \- *lemma* first_order.language.Lhom.realize_on_bounded_formula
- \- *lemma* first_order.language.Lhom.realize_on_formula
- \- *lemma* first_order.language.Lhom.realize_on_sentence
- \- *lemma* first_order.language.Lhom.realize_on_term
- \- *lemma* first_order.language.Lhom.set_of_realize_on_formula
- \- *def* first_order.language.Theory.is_finitely_satisfiable
- \- *lemma* first_order.language.Theory.is_satisfiable.is_finitely_satisfiable
- \- *lemma* first_order.language.Theory.is_satisfiable.mono
- \- *def* first_order.language.Theory.is_satisfiable.some_model
- \- *def* first_order.language.Theory.is_satisfiable
- \- *lemma* first_order.language.Theory.model.is_satisfiable
- \- *lemma* first_order.language.Theory.model.mono
- \- *def* first_order.language.Theory.models_bounded_formula
- \- *lemma* first_order.language.Theory.models_formula_iff
- \- *lemma* first_order.language.Theory.models_sentence_iff
- \- *lemma* first_order.language.Theory.realize_sentence_of_mem
- \- *lemma* first_order.language.Theory.semantically_equivalent.realize_bd_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.realize_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.refl
- \- *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_bd_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.symm
- \- *lemma* first_order.language.Theory.semantically_equivalent.trans
- \- *def* first_order.language.Theory.semantically_equivalent
- \- *def* first_order.language.Theory.semantically_equivalent_setoid
- \- *def* first_order.language.Theory
- \- *lemma* first_order.language.bounded_formula.all_semantically_equivalent_not_ex_not
- \- *def* first_order.language.bounded_formula.alls
- \- *def* first_order.language.bounded_formula.cast_le
- \- *lemma* first_order.language.bounded_formula.ex_semantically_equivalent_not_all_not
- \- *def* first_order.language.bounded_formula.exs
- \- *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_not_sup
- \- *lemma* first_order.language.bounded_formula.induction_on_all_ex
- \- *lemma* first_order.language.bounded_formula.induction_on_exists_not
- \- *lemma* first_order.language.bounded_formula.inf_semantically_equivalent_not_sup_not
- \- *lemma* first_order.language.bounded_formula.is_atomic.cast_le
- \- *lemma* first_order.language.bounded_formula.is_atomic.is_prenex
- \- *lemma* first_order.language.bounded_formula.is_atomic.is_qf
- \- *lemma* first_order.language.bounded_formula.is_atomic.lift_at
- \- *lemma* first_order.language.bounded_formula.is_atomic.relabel
- \- *inductive* first_order.language.bounded_formula.is_atomic
- \- *lemma* first_order.language.bounded_formula.is_prenex.cast_le
- \- *lemma* first_order.language.bounded_formula.is_prenex.induction_on_all_not
- \- *lemma* first_order.language.bounded_formula.is_prenex.lift_at
- \- *lemma* first_order.language.bounded_formula.is_prenex.relabel
- \- *inductive* first_order.language.bounded_formula.is_prenex
- \- *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp
- \- *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp_right
- \- *lemma* first_order.language.bounded_formula.is_qf.cast_le
- \- *lemma* first_order.language.bounded_formula.is_qf.induction_on_inf_not
- \- *lemma* first_order.language.bounded_formula.is_qf.induction_on_sup_not
- \- *lemma* first_order.language.bounded_formula.is_qf.is_prenex
- \- *lemma* first_order.language.bounded_formula.is_qf.lift_at
- \- *lemma* first_order.language.bounded_formula.is_qf.not
- \- *lemma* first_order.language.bounded_formula.is_qf.relabel
- \- *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp
- \- *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp_right
- \- *inductive* first_order.language.bounded_formula.is_qf
- \- *lemma* first_order.language.bounded_formula.is_qf_bot
- \- *def* first_order.language.bounded_formula.lift_at
- \- *lemma* first_order.language.bounded_formula.not_all_is_atomic
- \- *lemma* first_order.language.bounded_formula.not_all_is_qf
- \- *lemma* first_order.language.bounded_formula.not_ex_is_atomic
- \- *lemma* first_order.language.bounded_formula.not_ex_is_qf
- \- *def* first_order.language.bounded_formula.realize
- \- *lemma* first_order.language.bounded_formula.realize_all
- \- *lemma* first_order.language.bounded_formula.realize_all_lift_at_one_self
- \- *lemma* first_order.language.bounded_formula.realize_alls
- \- *lemma* first_order.language.bounded_formula.realize_bd_equal
- \- *lemma* first_order.language.bounded_formula.realize_bot
- \- *lemma* first_order.language.bounded_formula.realize_cast_le_of_eq
- \- *lemma* first_order.language.bounded_formula.realize_ex
- \- *lemma* first_order.language.bounded_formula.realize_exs
- \- *lemma* first_order.language.bounded_formula.realize_iff
- \- *lemma* first_order.language.bounded_formula.realize_imp
- \- *lemma* first_order.language.bounded_formula.realize_inf
- \- *lemma* first_order.language.bounded_formula.realize_lift_at
- \- *lemma* first_order.language.bounded_formula.realize_lift_at_one
- \- *lemma* first_order.language.bounded_formula.realize_lift_at_one_self
- \- *lemma* first_order.language.bounded_formula.realize_not
- \- *lemma* first_order.language.bounded_formula.realize_rel
- \- *lemma* first_order.language.bounded_formula.realize_relabel
- \- *lemma* first_order.language.bounded_formula.realize_sup
- \- *lemma* first_order.language.bounded_formula.realize_to_prenex
- \- *lemma* first_order.language.bounded_formula.realize_to_prenex_imp
- \- *lemma* first_order.language.bounded_formula.realize_to_prenex_imp_right
- \- *lemma* first_order.language.bounded_formula.realize_top
- \- *def* first_order.language.bounded_formula.relabel
- \- *def* first_order.language.bounded_formula.relabel_aux
- \- *lemma* first_order.language.bounded_formula.semantically_equivalent_all_lift_at
- \- *lemma* first_order.language.bounded_formula.semantically_equivalent_not_not
- \- *lemma* first_order.language.bounded_formula.semantically_equivalent_to_prenex
- \- *lemma* first_order.language.bounded_formula.sum_elim_comp_relabel_aux
- \- *lemma* first_order.language.bounded_formula.sup_semantically_equivalent_not_inf_not
- \- *def* first_order.language.bounded_formula.to_prenex
- \- *def* first_order.language.bounded_formula.to_prenex_imp
- \- *def* first_order.language.bounded_formula.to_prenex_imp_right
- \- *lemma* first_order.language.bounded_formula.to_prenex_is_prenex
- \- *inductive* first_order.language.bounded_formula
- \- *def* first_order.language.constants.term
- \- *lemma* first_order.language.embedding.realize_term
- \- *lemma* first_order.language.equiv.realize_bounded_formula
- \- *lemma* first_order.language.equiv.realize_formula
- \- *lemma* first_order.language.equiv.realize_term
- \- *def* first_order.language.formula.graph
- \- *lemma* first_order.language.formula.imp_semantically_equivalent_not_sup
- \- *lemma* first_order.language.formula.inf_semantically_equivalent_not_sup_not
- \- *lemma* first_order.language.formula.is_atomic_graph
- \- *def* first_order.language.formula.realize
- \- *lemma* first_order.language.formula.realize_bot
- \- *lemma* first_order.language.formula.realize_equal
- \- *lemma* first_order.language.formula.realize_graph
- \- *lemma* first_order.language.formula.realize_iff
- \- *lemma* first_order.language.formula.realize_imp
- \- *lemma* first_order.language.formula.realize_inf
- \- *lemma* first_order.language.formula.realize_not
- \- *lemma* first_order.language.formula.realize_rel
- \- *lemma* first_order.language.formula.realize_relabel
- \- *lemma* first_order.language.formula.realize_sup
- \- *lemma* first_order.language.formula.realize_top
- \- *def* first_order.language.formula.relabel
- \- *lemma* first_order.language.formula.semantically_equivalent_not_not
- \- *lemma* first_order.language.formula.sup_semantically_equivalent_not_inf_not
- \- *def* first_order.language.formula
- \- *lemma* first_order.language.hom.realize_term
- \- *def* first_order.language.relations.bounded_formula
- \- *def* first_order.language.relations.formula
- \- *def* first_order.language.sentence.realize
- \- *def* first_order.language.sentence
- \- *def* first_order.language.term.bd_equal
- \- *theorem* first_order.language.term.card_le
- \- *lemma* first_order.language.term.card_le_omega
- \- *def* first_order.language.term.equal
- \- *def* first_order.language.term.lift_at
- \- *def* first_order.language.term.list_decode
- \- *theorem* first_order.language.term.list_decode_encode_list
- \- *def* first_order.language.term.list_encode
- \- *lemma* first_order.language.term.list_encode_injective
- \- *def* first_order.language.term.realize
- \- *lemma* first_order.language.term.realize_con
- \- *lemma* first_order.language.term.realize_constants
- \- *lemma* first_order.language.term.realize_lift_at
- \- *lemma* first_order.language.term.realize_relabel
- \- *def* first_order.language.term.relabel
- \- *inductive* first_order.language.term

Modified src/model_theory/ultraproducts.lean
- \- *theorem* first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable



## [2022-03-27 03:34:03](https://github.com/leanprover-community/mathlib/commit/57a5fd7)
chore(scripts): update nolints.txt ([#12971](https://github.com/leanprover-community/mathlib/pull/12971))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-27 00:27:34](https://github.com/leanprover-community/mathlib/commit/664247f)
chore(data/set/intervals/ord_connected): Golf proof ([#12923](https://github.com/leanprover-community/mathlib/pull/12923))
#### Estimated changes
Modified src/data/set/intervals/ord_connected.lean




## [2022-03-27 00:27:33](https://github.com/leanprover-community/mathlib/commit/05ef694)
refactor(topology/instances/ennreal): make `ennreal` an instance of `has_continuous_inv` ([#12806](https://github.com/leanprover-community/mathlib/pull/12806))
Prior to the type class `has_continuous_inv`, `ennreal` had to have it's own hand-rolled `ennreal.continuous_inv` statement. This replaces it with a `has_continuous_inv` instance.
- [x] depends on: [#12748](https://github.com/leanprover-community/mathlib/pull/12748)
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/instances/ennreal.lean




## [2022-03-26 23:54:12](https://github.com/leanprover-community/mathlib/commit/caf6f19)
refactor(category_theory/abelian): deduplicate definitions of (co)image ([#12902](https://github.com/leanprover-community/mathlib/pull/12902))
Previously we made two separate definitions of the abelian (co)image, as `kernel (cokernel.π f)` / `cokernel (kernel.ι f)`,
once for `non_preadditive_abelian C` and once for `abelian C`.
This duplication wasn't really necessary, and this PR unifies them.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+/\- *abbreviation* category_theory.abelian.coimage_iso_image'
- \+/\- *abbreviation* category_theory.abelian.coimage_iso_image
- \+ *def* category_theory.abelian.coimage_strong_epi_mono_factorisation
- \- *def* category_theory.abelian.coimages.coimage_strong_epi_mono_factorisation
- \- *lemma* category_theory.abelian.coimages.comp_coimage_π_eq_zero
- \+ *lemma* category_theory.abelian.comp_coimage_π_eq_zero
- \+/\- *lemma* category_theory.abelian.full_image_factorisation
- \+/\- *abbreviation* category_theory.abelian.image_iso_image
- \+ *def* category_theory.abelian.image_strong_epi_mono_factorisation
- \+ *lemma* category_theory.abelian.image_ι_comp_eq_zero
- \- *def* category_theory.abelian.images.image_strong_epi_mono_factorisation
- \- *lemma* category_theory.abelian.images.image_ι_comp_eq_zero

Modified src/category_theory/abelian/exact.lean
- \+/\- *def* category_theory.abelian.is_colimit_coimage
- \+/\- *def* category_theory.abelian.is_colimit_image

Added src/category_theory/abelian/images.lean


Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/abelian/pseudoelements.lean




## [2022-03-26 23:17:46](https://github.com/leanprover-community/mathlib/commit/f5a9d0a)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at ([#12707](https://github.com/leanprover-community/mathlib/pull/12707))
We add `cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at`.
From flt-regular
#### Estimated changes
Modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at
- \+ *lemma* polynomial.monic.is_eisenstein_at_of_mem_of_not_mem
- \+ *lemma* polynomial.monic.leading_coeff_not_mem



## [2022-03-26 21:16:08](https://github.com/leanprover-community/mathlib/commit/7b93889)
refactor(data/list/basic): Remove many redundant hypotheses ([#12950](https://github.com/leanprover-community/mathlib/pull/12950))
Many theorems about `last` required arguments proving that certain things were not equal to `nil`, when in fact this was always the case. These hypotheses have been removed and replaced with the corresponding proofs.
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.last_append
- \+/\- *theorem* list.last_concat
- \+/\- *theorem* list.last_cons_cons
- \+/\- *theorem* list.last_singleton

Modified src/data/nat/digits.lean




## [2022-03-26 21:16:07](https://github.com/leanprover-community/mathlib/commit/e63e332)
feat(algebra/ring/basic): all non-zero elements in a non-trivial ring with no non-zero zero divisors are regular ([#12947](https://github.com/leanprover-community/mathlib/pull/12947))
Besides what the PR description says, I also golfed two earlier proofs.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* is_regular_iff_ne_zero'



## [2022-03-26 21:16:06](https://github.com/leanprover-community/mathlib/commit/b30f25c)
fix(data/set/prod): fix the way `×ˢ` associates ([#12943](https://github.com/leanprover-community/mathlib/pull/12943))
Previously `s ×ˢ t ×ˢ u` was an element of `set ((α × β) × γ)` instead of `set (α × β × γ) = set (α × (β × γ))`.
#### Estimated changes
Modified src/data/set/prod.lean




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
Modified src/algebra/algebra/basic.lean


Modified src/algebra/big_operators/basic.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/field_power.lean


Modified src/algebra/free.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/opposite.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_ring_action.lean


Renamed src/data/equiv/mul_add_aut.lean to src/algebra/hom/aut.lean


Renamed src/data/equiv/mul_add.lean to src/algebra/hom/equiv.lean


Modified src/algebra/lie/basic.lean


Renamed src/data/equiv/module.lean to src/algebra/module/equiv.lean


Modified src/algebra/module/opposites.lean


Modified src/algebra/module/submodule.lean


Modified src/algebra/module/ulift.lean


Modified src/algebra/opposites.lean


Modified src/algebra/order/hom/ring.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/quandle.lean


Modified src/algebra/quaternion.lean


Renamed src/data/equiv/ring_aut.lean to src/algebra/ring/aut.lean


Modified src/algebra/ring/comp_typeclasses.lean


Renamed src/data/equiv/ring.lean to src/algebra/ring/equiv.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebra/star/basic.lean


Modified src/algebra/star/module.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/locally_ringed_space.lean


Modified src/analysis/analytic/basic.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/functor/fully_faithful.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/preadditive/opposite.lean


Modified src/category_theory/types.lean


Modified src/combinatorics/derangements/basic.lean


Modified src/computability/primrec.lean


Modified src/control/equiv_functor.lean


Modified src/control/monad/basic.lean


Modified src/control/monad/writer.lean


Modified src/control/traversable/equiv.lean


Modified src/control/uliftable.lean


Modified src/data/W/basic.lean


Modified src/data/erased.lean


Modified src/data/finsupp/to_dfinsupp.lean


Modified src/data/fintype/card_embedding.lean


Modified src/data/matrix/basic.lean


Modified src/data/mv_polynomial/equiv.lean


Modified src/data/nat/enat.lean


Modified src/data/opposite.lean


Modified src/data/part.lean


Modified src/data/rat/basic.lean


Modified src/data/set/countable.lean


Modified src/data/ulift.lean


Modified src/deprecated/group.lean


Modified src/field_theory/cardinality.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/free_abelian_group_finsupp.lean


Modified src/group_theory/group_action/group.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/fin.lean


Modified src/group_theory/perm/option.lean


Modified src/group_theory/semidirect_product.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/pi.lean


Renamed src/data/equiv/denumerable.lean to src/logic/denumerable.lean


Modified src/logic/embedding.lean


Renamed src/data/equiv/encodable/basic.lean to src/logic/encodable/basic.lean


Renamed src/data/equiv/encodable/lattice.lean to src/logic/encodable/lattice.lean


Renamed src/data/equiv/encodable/small.lean to src/logic/encodable/small.lean


Renamed src/data/equiv/basic.lean to src/logic/equiv/basic.lean


Renamed src/data/equiv/embedding.lean to src/logic/equiv/embedding.lean


Renamed src/data/equiv/fin.lean to src/logic/equiv/fin.lean


Renamed src/data/equiv/fintype.lean to src/logic/equiv/fintype.lean


Renamed src/data/equiv/functor.lean to src/logic/equiv/functor.lean


Renamed src/data/equiv/list.lean to src/logic/equiv/list.lean


Renamed src/data/equiv/local_equiv.lean to src/logic/equiv/local_equiv.lean


Renamed src/data/equiv/nat.lean to src/logic/equiv/nat.lean


Renamed src/data/equiv/option.lean to src/logic/equiv/option.lean


Renamed src/data/equiv/set.lean to src/logic/equiv/set.lean


Renamed src/data/equiv/transfer_instance.lean to src/logic/equiv/transfer_instance.lean


Modified src/logic/small.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/pi_system.lean


Modified src/model_theory/basic.lean


Modified src/model_theory/definability.lean


Modified src/model_theory/terms_and_formulas.lean


Modified src/order/hom/basic.lean


Modified src/order/ideal.lean


Modified src/order/jordan_holder.lean


Modified src/order/lexicographic.lean


Modified src/order/order_dual.lean


Modified src/order/order_iso_nat.lean


Modified src/order/rel_iso.lean


Modified src/order/semiconj_Sup.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/local_properties.lean


Modified src/ring_theory/localization/basic.lean


Modified src/ring_theory/localization/integral.lean


Modified src/ring_theory/ring_invo.lean


Modified src/ring_theory/subsemiring/basic.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/norm_swap.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/homeomorph.lean


Modified src/topology/local_homeomorph.lean


Modified test/norm_swap.lean


Modified test/semilinear.lean


Modified test/simp_result.lean




## [2022-03-26 20:22:51](https://github.com/leanprover-community/mathlib/commit/434a938)
feat(analysis/convex/strict_convex_space): Strictly convex spaces ([#11794](https://github.com/leanprover-community/mathlib/pull/11794))
Define `strictly_convex_space`, a `Prop`-valued mixin to state that a normed space is strictly convex.
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+ *lemma* ae_eq_const_or_norm_integral_lt_of_norm_le_const
- \- *lemma* strict_convex.ae_eq_const_or_norm_integral_lt_of_norm_le_const

Modified src/analysis/convex/strict.lean


Added src/analysis/convex/strict_convex_space.lean
- \+ *lemma* combo_mem_ball_of_ne
- \+ *lemma* dist_add_dist_eq_iff
- \+ *lemma* norm_add_lt_of_not_same_ray
- \+ *lemma* norm_combo_lt_of_ne
- \+ *lemma* open_segment_subset_ball_of_ne
- \+ *lemma* same_ray_iff_norm_add
- \+ *lemma* strict_convex_closed_ball
- \+ *lemma* strict_convex_space.of_norm_add
- \+ *lemma* strict_convex_space.of_strict_convex_closed_unit_ball

Modified src/analysis/convex/topology.lean
- \+ *lemma* dist_add_dist_of_mem_segment

Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* inv_norm_smul_mem_closed_unit_ball



## [2022-03-26 19:19:53](https://github.com/leanprover-community/mathlib/commit/1f11f3f)
chore(order/filter/basic): rename using the zero subscript convention for groups with zero ([#12952](https://github.com/leanprover-community/mathlib/pull/12952))
#### Estimated changes
Modified src/order/filter/basic.lean
- \- *lemma* filter.eventually_eq.div'
- \+/\- *lemma* filter.eventually_eq.div
- \- *lemma* filter.eventually_eq.sub



## [2022-03-26 18:24:35](https://github.com/leanprover-community/mathlib/commit/a491055)
chore(measure_theory/integral/lebesgue): extend to ae_measurable ([#12953](https://github.com/leanprover-community/mathlib/pull/12953))
#### Estimated changes
Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* measure_theory.lintegral_eq_top_of_measure_eq_top_pos
- \+/\- *lemma* measure_theory.lintegral_trim
- \+/\- *lemma* measure_theory.meas_ge_le_lintegral_div
- \+ *lemma* measure_theory.mul_meas_ge_le_lintegral₀
- \+ *lemma* measure_theory.simple_func.apply_mk
- \+ *lemma* measure_theory.simple_func.extend_apply'
- \+ *def* measure_theory.simple_func.of_is_empty
- \+/\- *lemma* measure_theory.univ_le_of_forall_fin_meas_le



## [2022-03-26 14:15:19](https://github.com/leanprover-community/mathlib/commit/cb2797e)
feat(measure_theory/constructions/borel_space): drop a countability assumption ([#12954](https://github.com/leanprover-community/mathlib/pull/12954))
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae
- \+ *lemma* measurable_of_tendsto_metrizable'
- \+ *lemma* measurable_of_tendsto_metrizable



## [2022-03-26 12:20:15](https://github.com/leanprover-community/mathlib/commit/b7d9166)
chore(measure_theory/measure/lebesgue): delete leftovers ([#12951](https://github.com/leanprover-community/mathlib/pull/12951))
#### Estimated changes
Modified src/measure_theory/measure/lebesgue.lean




## [2022-03-26 12:20:14](https://github.com/leanprover-community/mathlib/commit/1111482)
feat(topology/bases): separable subsets of topological spaces ([#12936](https://github.com/leanprover-community/mathlib/pull/12936))
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* set.countable.is_separable
- \+ *lemma* set.finite.is_separable
- \+ *lemma* topological_space.is_separable.closure
- \+ *lemma* topological_space.is_separable.image
- \+ *lemma* topological_space.is_separable.mono
- \+ *lemma* topological_space.is_separable.union
- \+ *def* topological_space.is_separable
- \+ *lemma* topological_space.is_separable_Union
- \+ *lemma* topological_space.is_separable_of_separable_space
- \+ *lemma* topological_space.is_separable_of_separable_space_subtype
- \+ *lemma* topological_space.is_separable_univ_iff
- \+ *lemma* topological_space.separable_space_of_dense_range

Modified src/topology/constructions.lean
- \+ *lemma* embedding.cod_restrict
- \+ *lemma* inducing.cod_restrict

Modified src/topology/metric_space/basic.lean
- \+ *lemma* continuous_on.is_separable_image
- \+ *lemma* is_compact.is_separable
- \+ *lemma* metric.dense_iff
- \+ *lemma* metric.dense_range_iff
- \+/\- *theorem* metric.mem_closure_iff
- \+/\- *lemma* metric.mem_closure_range_iff
- \+/\- *lemma* metric.mem_closure_range_iff_nat
- \+/\- *theorem* metric.mem_of_closed'
- \+ *lemma* topological_space.is_separable.separable_space



## [2022-03-26 12:20:13](https://github.com/leanprover-community/mathlib/commit/f68536e)
feat(topology/constructions): continuity of uncurried functions when the first factor is discrete ([#12935](https://github.com/leanprover-community/mathlib/pull/12935))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.map_pure_prod

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous_uncurry_of_discrete_topology



## [2022-03-26 12:20:12](https://github.com/leanprover-community/mathlib/commit/5e449c2)
feat(algebra/is_prime_pow): add `is_prime_pow_iff_factorization_single` ([#12167](https://github.com/leanprover-community/mathlib/pull/12167))
Adds lemma `is_prime_pow_iff_factorization_single : is_prime_pow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = finsupp.single p k`
Also adds `pow_of_factorization_single` to `data/nat/factorization`
#### Estimated changes
Modified src/algebra/is_prime_pow.lean
- \+ *lemma* is_prime_pow_iff_card_support_factorization_eq_one
- \+ *lemma* is_prime_pow_iff_factorization_eq_single

Modified src/data/nat/factorization.lean
- \+ *lemma* nat.eq_pow_of_factorization_eq_single



## [2022-03-26 10:30:31](https://github.com/leanprover-community/mathlib/commit/023a783)
feat(logic/nontrivial): `exists_pair_lt` ([#12925](https://github.com/leanprover-community/mathlib/pull/12925))
#### Estimated changes
Modified src/logic/nontrivial.lean
- \+ *lemma* exists_pair_lt
- \+ *lemma* nontrivial_iff_lt



## [2022-03-26 10:30:30](https://github.com/leanprover-community/mathlib/commit/c51f4f1)
feat(set_theory/cardinal_ordinal): `κ ^ n = κ` for infinite cardinals ([#12922](https://github.com/leanprover-community/mathlib/pull/12922))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.pow_eq
- \+ *lemma* cardinal.power_nat_eq
- \+/\- *lemma* cardinal.power_nat_le



## [2022-03-26 09:35:33](https://github.com/leanprover-community/mathlib/commit/9d26041)
feat(topology/instances/ennreal): add `ennreal.has_sum_to_real` ([#12926](https://github.com/leanprover-community/mathlib/pull/12926))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.has_sum_to_real



## [2022-03-26 03:28:38](https://github.com/leanprover-community/mathlib/commit/b83bd25)
feat(linear_algebra/sesquilinear_form): add nondegenerate ([#12683](https://github.com/leanprover-community/mathlib/pull/12683))
Defines nondegenerate sesquilinear forms as left and right separating sesquilinear forms.
#### Estimated changes
Modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* linear_map.flip_nondegenerate
- \+ *lemma* linear_map.flip_separating_left
- \+ *lemma* linear_map.flip_separating_right
- \+ *lemma* linear_map.is_Ortho.nondegenerate_of_not_is_ortho_basis_self
- \+ *lemma* linear_map.is_Ortho.not_is_ortho_basis_self_of_separating_left
- \+ *lemma* linear_map.is_Ortho.not_is_ortho_basis_self_of_separating_right
- \+ *lemma* linear_map.is_Ortho.separating_left_of_not_is_ortho_basis_self
- \+ *lemma* linear_map.is_Ortho.separating_right_iff_not_is_ortho_basis_self
- \+ *lemma* linear_map.is_symm.nondegenerate_of_separating_left
- \+ *lemma* linear_map.is_symm.nondegenerate_of_separating_right
- \+ *def* linear_map.nondegenerate
- \+ *lemma* linear_map.nondegenerate_restrict_of_disjoint_orthogonal
- \+ *def* linear_map.separating_left
- \+ *theorem* linear_map.separating_left_iff_ker_eq_bot
- \+ *lemma* linear_map.separating_left_iff_linear_nontrivial
- \+ *def* linear_map.separating_right
- \+ *theorem* linear_map.separating_right_iff_flip_ker_eq_bot
- \+ *lemma* linear_map.separating_right_iff_linear_flip_nontrivial



## [2022-03-26 02:58:15](https://github.com/leanprover-community/mathlib/commit/17b621c)
chore(scripts): update nolints.txt ([#12946](https://github.com/leanprover-community/mathlib/pull/12946))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-25 19:43:25](https://github.com/leanprover-community/mathlib/commit/b6d246a)
feat(topology/continuous_function/cocompact_maps): add the type of cocompact continuous maps ([#12938](https://github.com/leanprover-community/mathlib/pull/12938))
This adds the type of cocompact continuous maps, which are those functions `f : α → β` for which `tendsto f (cocompact α) (cocompact β)`. These maps are of interest primarily because of their connection with continuous functions vanishing at infinity ([#12907](https://github.com/leanprover-community/mathlib/pull/12907)). In particular, if `f : α → β` is a cocompact continuous map and `g : β →C₀ γ` is a continuous function which vanishes at infinity, then `g ∘ f : α →C₀ γ`.
These are also related to quasi-compact maps (continuous maps for which preimages of compact sets are compact) and proper maps (continuous maps which are universally closed), neither of which are currently defined in mathlib. In particular, quasi-compact maps are cocompact continuous maps, and when the codomain is Hausdorff the converse holds also. Under some additional assumptions, both of these are also equivalent to being a proper map.
#### Estimated changes
Added src/topology/continuous_function/cocompact_map.lean
- \+ *lemma* cocompact_map.coe_comp
- \+ *lemma* cocompact_map.coe_id
- \+ *lemma* cocompact_map.coe_mk
- \+ *lemma* cocompact_map.coe_to_continuous_fun
- \+ *def* cocompact_map.comp
- \+ *lemma* cocompact_map.comp_apply
- \+ *lemma* cocompact_map.comp_assoc
- \+ *lemma* cocompact_map.comp_id
- \+ *lemma* cocompact_map.compact_preimage
- \+ *lemma* cocompact_map.ext
- \+ *lemma* cocompact_map.id_comp
- \+ *lemma* cocompact_map.tendsto_of_forall_preimage
- \+ *structure* cocompact_map



## [2022-03-25 18:48:49](https://github.com/leanprover-community/mathlib/commit/221796a)
feat(topology/metric_space/metrizable): define and use a metrizable typeclass ([#12934](https://github.com/leanprover-community/mathlib/pull/12934))
#### Estimated changes
Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/metrizable.lean
- \+ *lemma* embedding.metrizable_space
- \+ *lemma* topological_space.metrizable_space_of_normal_second_countable



## [2022-03-25 17:53:43](https://github.com/leanprover-community/mathlib/commit/5925650)
chore(nnreal): rename lemmas based on real.to_nnreal when they mention of_real ([#12937](https://github.com/leanprover-community/mathlib/pull/12937))
Many lemma using `real.to_nnreal` mention `of_real` in their names. This PR tries to make things more coherent.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean


Modified src/data/real/sqrt.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+ *lemma* continuous_real_to_nnreal
- \- *lemma* nnreal.continuous_of_real
- \- *lemma* nnreal.has_sum_of_real_of_nonneg
- \+ *lemma* nnreal.has_sum_real_to_nnreal_of_nonneg
- \- *lemma* nnreal.tendsto_of_real
- \+ *lemma* nnreal.tendsto_real_to_nnreal



## [2022-03-25 11:39:22](https://github.com/leanprover-community/mathlib/commit/2143571)
feat(topology/category/Born): The category of bornologies ([#12045](https://github.com/leanprover-community/mathlib/pull/12045))
Define `Born`, the category of bornological spaces with bounded maps.
#### Estimated changes
Added src/topology/category/Born.lean
- \+ *def* Born.of
- \+ *def* Born



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
Modified src/algebra/algebra/bilinear.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/free.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/default.lean


Modified src/algebra/group/ext.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group_with_zero/basic.lean


Renamed src/algebra/group/freiman.lean to src/algebra/hom/freiman.lean


Renamed src/algebra/group/hom.lean to src/algebra/hom/group.lean


Renamed src/algebra/group_action_hom.lean to src/algebra/hom/group_action.lean


Renamed src/algebra/group/hom_instances.lean to src/algebra/hom/group_instances.lean


Renamed src/algebra/iterate_hom.lean to src/algebra/hom/iterate.lean


Renamed src/algebra/non_unital_alg_hom.lean to src/algebra/hom/non_unital_alg.lean


Renamed src/algebra/group/units_hom.lean to src/algebra/hom/units.lean


Modified src/algebra/lie/non_unital_non_assoc_algebra.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/order/hom/monoid.lean


Modified src/algebra/polynomial/group_ring_action.lean


Modified src/algebra/regular/pow.lean


Modified src/category_theory/monoidal/discrete.lean


Modified src/category_theory/preadditive/default.lean


Modified src/data/finsupp/basic.lean


Modified src/data/polynomial/derivative.lean


Modified src/deprecated/group.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/group_action/defs.lean


Modified src/group_theory/group_action/sub_mul_action.lean


Modified src/group_theory/order_of_element.lean


Modified src/topology/algebra/group_completion.lean


Modified test/simps.lean




## [2022-03-25 09:03:06](https://github.com/leanprover-community/mathlib/commit/351c32f)
docs(docs/undergrad): Update TODO list ([#12752](https://github.com/leanprover-community/mathlib/pull/12752))
Update `undergrad` with the latest additions to mathlib.
#### Estimated changes
Modified docs/undergrad.yaml




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
Modified src/computability/partrec.lean


Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/pfun.lean
- \+ *theorem* pfun.fix_fwd
- \+ *theorem* pfun.fix_stop



## [2022-03-25 00:37:21](https://github.com/leanprover-community/mathlib/commit/3dd8e4d)
feat(order/category/FinBoolAlg): The category of finite Boolean algebras ([#12906](https://github.com/leanprover-community/mathlib/pull/12906))
Define `FinBoolAlg`, the category of finite Boolean algebras.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.preimage_sInter

Modified src/order/category/BoolAlg.lean
- \+ *lemma* BoolAlg.coe_to_BoundedDistribLattice

Added src/order/category/FinBoolAlg.lean
- \+ *lemma* FinBoolAlg.coe_of
- \+ *lemma* FinBoolAlg.coe_to_BoolAlg
- \+ *def* FinBoolAlg.dual
- \+ *def* FinBoolAlg.dual_equiv
- \+ *def* FinBoolAlg.iso.mk
- \+ *def* FinBoolAlg.of
- \+ *structure* FinBoolAlg
- \+ *def* Fintype_to_FinBoolAlg_op

Modified src/order/category/FinPartialOrder.lean
- \+ *lemma* FinPartialOrder.coe_to_PartialOrder

Modified src/order/hom/complete_lattice.lean
- \+ *lemma* complete_lattice_hom.coe_set_preimage
- \+ *def* complete_lattice_hom.set_preimage
- \+ *lemma* complete_lattice_hom.set_preimage_apply
- \+ *lemma* complete_lattice_hom.set_preimage_comp
- \+ *lemma* complete_lattice_hom.set_preimage_id



## [2022-03-25 00:06:09](https://github.com/leanprover-community/mathlib/commit/7ec1a31)
fix(combinatorics/simple_graph/density): correct name in docstring ([#12921](https://github.com/leanprover-community/mathlib/pull/12921))
#### Estimated changes
Modified src/combinatorics/simple_graph/density.lean




## [2022-03-24 22:53:04](https://github.com/leanprover-community/mathlib/commit/352ecfe)
feat(combinatorics/simple_graph/{connectivity,metric}): `connected` and `dist` ([#12574](https://github.com/leanprover-community/mathlib/pull/12574))
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.connected.set_univ_walk_nonempty
- \+ *structure* simple_graph.connected
- \+ *lemma* simple_graph.preconnected.set_univ_walk_nonempty
- \+ *def* simple_graph.preconnected
- \+ *def* simple_graph.reachable
- \+ *lemma* simple_graph.reachable_iff_nonempty_univ
- \+ *lemma* simple_graph.reachable_iff_refl_trans_gen
- \+ *lemma* simple_graph.reachable_is_equivalence
- \+ *def* simple_graph.reachable_setoid
- \+ *abbreviation* simple_graph.subgraph.connected
- \+ *lemma* simple_graph.walk.eq_of_length_eq_zero
- \+ *lemma* simple_graph.walk.exists_length_eq_zero_iff
- \+/\- *structure* simple_graph.walk.is_cycle
- \+/\- *lemma* simple_graph.walk.is_cycle_def

Added src/combinatorics/simple_graph/metric.lean
- \+ *lemma* simple_graph.connected.dist_eq_zero_iff
- \+ *lemma* simple_graph.connected.dist_triangle
- \+ *lemma* simple_graph.connected.exists_walk_of_dist
- \+ *lemma* simple_graph.connected.pos_dist_of_ne
- \+ *def* simple_graph.dist
- \+ *lemma* simple_graph.dist_comm
- \+ *lemma* simple_graph.dist_comm_aux
- \+ *lemma* simple_graph.dist_eq_zero_iff_eq_or_not_reachable
- \+ *lemma* simple_graph.dist_eq_zero_of_not_reachable
- \+ *lemma* simple_graph.dist_le
- \+ *lemma* simple_graph.dist_self
- \+ *lemma* simple_graph.nonempty_of_pos_dist
- \+ *lemma* simple_graph.reachable.dist_eq_zero_iff
- \+ *lemma* simple_graph.reachable.exists_walk_of_dist
- \+ *lemma* simple_graph.reachable.pos_dist_of_ne



## [2022-03-24 17:30:47](https://github.com/leanprover-community/mathlib/commit/2891e1b)
feat(algebra/category/BoolRing): The category of Boolean rings ([#12905](https://github.com/leanprover-community/mathlib/pull/12905))
Define `BoolRing`, the category of Boolean rings.
#### Estimated changes
Added src/algebra/category/BoolRing.lean
- \+ *lemma* BoolRing.coe_of
- \+ *def* BoolRing.iso.mk
- \+ *def* BoolRing.of
- \+ *def* BoolRing

Modified src/algebra/punit_instances.lean
- \+/\- *lemma* punit.div_eq
- \+/\- *lemma* punit.inv_eq

Modified src/algebra/ring/boolean_ring.lean
- \+ *def* as_boolalg
- \- *def* boolean_ring.has_bot
- \- *def* boolean_ring.has_sdiff
- \+/\- *def* boolean_ring.has_sup
- \- *lemma* boolean_ring.inf_inf_sdiff
- \- *lemma* boolean_ring.sup_inf_sdiff
- \+ *def* of_boolalg
- \+ *lemma* of_boolalg_bot
- \+ *lemma* of_boolalg_inf
- \+ *lemma* of_boolalg_inj
- \+ *lemma* of_boolalg_sup
- \+ *lemma* of_boolalg_symm_eq
- \+ *lemma* of_boolalg_to_boolalg
- \+ *lemma* of_boolalg_top
- \+ *lemma* ring_hom.as_boolalg_comp
- \+ *lemma* ring_hom.as_boolalg_id
- \+ *def* to_boolalg
- \+ *lemma* to_boolalg_add_add_mul
- \+ *lemma* to_boolalg_inj
- \+ *lemma* to_boolalg_mul
- \+ *lemma* to_boolalg_of_boolalg
- \+ *lemma* to_boolalg_one
- \+ *lemma* to_boolalg_symm_eq
- \+ *lemma* to_boolalg_zero



## [2022-03-24 17:30:46](https://github.com/leanprover-community/mathlib/commit/f53b239)
feat(model_theory/fraisse): Construct Fraïssé limits ([#12138](https://github.com/leanprover-community/mathlib/pull/12138))
Constructs Fraïssé limits (nonuniquely)
#### Estimated changes
Modified docs/references.bib


Modified src/model_theory/direct_limit.lean
- \+ *theorem* first_order.language.direct_limit.cg
- \+ *lemma* first_order.language.directed_system.coe_nat_le_rec
- \+ *def* first_order.language.directed_system.nat_le_rec

Modified src/model_theory/finitely_generated.lean


Modified src/model_theory/fraisse.lean
- \+ *lemma* first_order.language.Structure.fg.mem_age_of_equiv
- \+ *theorem* first_order.language.age_direct_limit
- \+ *theorem* first_order.language.age_fraisse_limit
- \+ *lemma* first_order.language.embedding.age_subset_age
- \+ *lemma* first_order.language.equiv.age_eq_age
- \+ *theorem* first_order.language.exists_cg_is_age_of
- \+ *lemma* first_order.language.hereditary.is_equiv_invariant_of_fg



## [2022-03-24 16:39:34](https://github.com/leanprover-community/mathlib/commit/6ac7c18)
feat(combinatorics/simple_graph/density): Edge density ([#12431](https://github.com/leanprover-community/mathlib/pull/12431))
Define the number and density of edges of a relation and of a simple graph between two finsets.
#### Estimated changes
Added src/combinatorics/simple_graph/density.lean
- \+ *lemma* rel.card_interedges_add_card_interedges_compl
- \+ *lemma* rel.card_interedges_comm
- \+ *lemma* rel.card_interedges_le_mul
- \+ *def* rel.edge_density
- \+ *lemma* rel.edge_density_add_edge_density_compl
- \+ *lemma* rel.edge_density_comm
- \+ *lemma* rel.edge_density_empty_left
- \+ *lemma* rel.edge_density_empty_right
- \+ *lemma* rel.edge_density_le_one
- \+ *lemma* rel.edge_density_nonneg
- \+ *def* rel.interedges
- \+ *lemma* rel.interedges_bUnion
- \+ *lemma* rel.interedges_bUnion_left
- \+ *lemma* rel.interedges_bUnion_right
- \+ *lemma* rel.interedges_disjoint_left
- \+ *lemma* rel.interedges_disjoint_right
- \+ *lemma* rel.interedges_empty_left
- \+ *lemma* rel.interedges_mono
- \+ *lemma* rel.mem_interedges_iff
- \+ *lemma* rel.mk_mem_interedges_comm
- \+ *lemma* rel.mk_mem_interedges_iff
- \+ *lemma* rel.swap_mem_interedges_iff
- \+ *lemma* simple_graph.card_interedges_add_card_interedges_compl
- \+ *lemma* simple_graph.card_interedges_div_card
- \+ *lemma* simple_graph.card_interedges_le_mul
- \+ *def* simple_graph.edge_density
- \+ *lemma* simple_graph.edge_density_add_edge_density_compl
- \+ *lemma* simple_graph.edge_density_comm
- \+ *lemma* simple_graph.edge_density_def
- \+ *lemma* simple_graph.edge_density_empty_left
- \+ *lemma* simple_graph.edge_density_empty_right
- \+ *lemma* simple_graph.edge_density_le_one
- \+ *lemma* simple_graph.edge_density_nonneg
- \+ *def* simple_graph.interedges
- \+ *lemma* simple_graph.interedges_bUnion
- \+ *lemma* simple_graph.interedges_bUnion_left
- \+ *lemma* simple_graph.interedges_bUnion_right
- \+ *lemma* simple_graph.interedges_def
- \+ *lemma* simple_graph.interedges_disjoint_left
- \+ *lemma* simple_graph.interedges_disjoint_right
- \+ *lemma* simple_graph.interedges_empty_left
- \+ *lemma* simple_graph.interedges_mono
- \+ *lemma* simple_graph.mem_interedges_iff
- \+ *lemma* simple_graph.mk_mem_interedges_comm
- \+ *lemma* simple_graph.mk_mem_interedges_iff
- \+ *lemma* simple_graph.swap_mem_interedges_iff



## [2022-03-24 14:49:21](https://github.com/leanprover-community/mathlib/commit/7302e11)
feat(algebra/module/torsion): define torsion submodules ([#12027](https://github.com/leanprover-community/mathlib/pull/12027))
This file defines the a-torsion and torsion submodules for a R-module M and gives some basic properties. (The ultimate goal I'm working on is to classify the finitely-generated modules over a PID).
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* exists_npow_eq_one_of_zpow_eq_one

Added src/algebra/module/torsion.lean
- \+ *theorem* add_monoid.is_torsion_iff_is_torsion_int
- \+ *theorem* add_monoid.is_torsion_iff_is_torsion_nat
- \+ *def* module.is_torsion'
- \+ *def* module.is_torsion
- \+ *def* module.is_torsion_by
- \+ *lemma* submodule.coe_torsion_eq_annihilator_ne_bot
- \+ *lemma* submodule.is_torsion'_iff_torsion'_eq_top
- \+ *lemma* submodule.is_torsion_by_iff_torsion_by_eq_top
- \+ *lemma* submodule.mem_torsion'_iff
- \+ *lemma* submodule.mem_torsion_by_iff
- \+ *lemma* submodule.mem_torsion_iff
- \+ *lemma* submodule.no_zero_smul_divisors_iff_torsion_eq_bot
- \+ *lemma* submodule.quotient_torsion.torsion_eq_bot
- \+ *lemma* submodule.smul_coe_torsion_by
- \+ *lemma* submodule.smul_torsion_by
- \+ *def* submodule.torsion'
- \+ *lemma* submodule.torsion'_is_torsion'
- \+ *lemma* submodule.torsion'_torsion'_eq_top
- \+ *def* submodule.torsion
- \+ *lemma* submodule.torsion_by.mk_smul
- \+ *def* submodule.torsion_by
- \+ *lemma* submodule.torsion_by_is_torsion_by
- \+ *lemma* submodule.torsion_by_torsion_by_eq_top
- \+ *lemma* submodule.torsion_is_torsion
- \+ *lemma* submodule.torsion_torsion_eq_top



## [2022-03-24 13:01:54](https://github.com/leanprover-community/mathlib/commit/c7745b3)
chore(order/zorn): Review ([#12175](https://github.com/leanprover-community/mathlib/pull/12175))
Lemma renames
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise.insert
- \+ *lemma* set.pairwise.insert_of_symmetric

Modified src/field_theory/adjoin.lean
- \+/\- *lemma* intermediate_field.lifts.exists_max_three
- \+/\- *lemma* intermediate_field.lifts.exists_max_two
- \+/\- *lemma* intermediate_field.lifts.exists_upper_bound
- \+/\- *def* intermediate_field.lifts.upper_bound_intermediate_field

Modified src/field_theory/is_alg_closed/basic.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/covering/vitali.lean


Modified src/order/compactly_generated.lean


Modified src/order/extension.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/zorn.lean
- \+ *lemma* chain_closure.is_chain
- \+ *lemma* chain_closure.succ_fixpoint
- \+ *lemma* chain_closure.succ_fixpoint_iff
- \+ *inductive* chain_closure
- \+ *lemma* chain_closure_empty
- \+ *lemma* chain_closure_max_chain
- \+ *lemma* chain_closure_total
- \- *lemma* directed_of_chain
- \+ *lemma* exists_maximal_of_chains_bounded
- \+ *theorem* exists_maximal_of_nonempty_chains_bounded
- \+ *lemma* is_chain.directed
- \+ *lemma* is_chain.directed_on
- \+ *lemma* is_chain.exists_max_chain
- \+ *lemma* is_chain.image
- \+ *lemma* is_chain.insert
- \+ *lemma* is_chain.mono
- \+ *lemma* is_chain.succ
- \+ *lemma* is_chain.super_chain_succ_chain
- \+ *lemma* is_chain.symm
- \+ *lemma* is_chain.total
- \+ *def* is_chain
- \+ *lemma* is_chain_empty
- \+ *lemma* is_chain_of_trichotomous
- \+ *lemma* is_chain_univ_iff
- \+ *lemma* is_max_chain.is_chain
- \+ *lemma* is_max_chain.not_super_chain
- \+ *def* is_max_chain
- \+ *def* max_chain
- \+ *lemma* max_chain_spec
- \- *lemma* set.subsingleton.chain
- \+ *lemma* set.subsingleton.is_chain
- \+ *def* succ_chain
- \+ *lemma* succ_increasing
- \+ *lemma* succ_spec
- \+ *def* super_chain
- \- *lemma* zorn.chain.directed_on
- \- *lemma* zorn.chain.image
- \- *theorem* zorn.chain.max_chain_of_chain
- \- *lemma* zorn.chain.mono
- \- *lemma* zorn.chain.symm
- \- *lemma* zorn.chain.total
- \- *lemma* zorn.chain.total_of_refl
- \- *def* zorn.chain
- \- *lemma* zorn.chain_chain_closure
- \- *inductive* zorn.chain_closure
- \- *lemma* zorn.chain_closure_closure
- \- *lemma* zorn.chain_closure_empty
- \- *lemma* zorn.chain_closure_succ_fixpoint
- \- *lemma* zorn.chain_closure_succ_fixpoint_iff
- \- *lemma* zorn.chain_closure_total
- \- *lemma* zorn.chain_empty
- \- *lemma* zorn.chain_insert
- \- *lemma* zorn.chain_of_trichotomous
- \- *lemma* zorn.chain_succ
- \- *lemma* zorn.chain_univ_iff
- \- *theorem* zorn.exists_maximal_of_chains_bounded
- \- *theorem* zorn.exists_maximal_of_nonempty_chains_bounded
- \- *def* zorn.is_max_chain
- \- *def* zorn.max_chain
- \- *theorem* zorn.max_chain_spec
- \- *def* zorn.succ_chain
- \- *lemma* zorn.succ_increasing
- \- *lemma* zorn.succ_spec
- \- *def* zorn.super_chain
- \- *lemma* zorn.super_of_not_max
- \- *theorem* zorn.zorn_nonempty_partial_order
- \- *theorem* zorn.zorn_nonempty_partial_order₀
- \- *theorem* zorn.zorn_partial_order
- \- *theorem* zorn.zorn_partial_order₀
- \- *theorem* zorn.zorn_subset
- \- *theorem* zorn.zorn_subset_nonempty
- \- *theorem* zorn.zorn_superset
- \- *theorem* zorn.zorn_superset_nonempty
- \+ *lemma* zorn_nonempty_partial_order
- \+ *lemma* zorn_nonempty_partial_order₀
- \+ *lemma* zorn_partial_order
- \+ *lemma* zorn_partial_order₀
- \+ *lemma* zorn_subset
- \+ *lemma* zorn_subset_nonempty
- \+ *lemma* zorn_superset
- \+ *lemma* zorn_superset_nonempty

Modified src/ring_theory/algebraic_independent.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/topology/algebra/semigroup.lean


Modified src/topology/shrinking_lemma.lean
- \+/\- *lemma* shrinking_lemma.partial_refinement.apply_eq_of_chain
- \+/\- *def* shrinking_lemma.partial_refinement.chain_Sup
- \+/\- *lemma* shrinking_lemma.partial_refinement.find_apply_of_mem
- \+/\- *lemma* shrinking_lemma.partial_refinement.le_chain_Sup

Modified src/topology/subset_properties.lean




## [2022-03-24 12:01:35](https://github.com/leanprover-community/mathlib/commit/7c48d65)
feat(topology/algebra/group): define `has_continuous_inv` and `has_continuous_neg` type classes ([#12748](https://github.com/leanprover-community/mathlib/pull/12748))
This creates the `has_continuous_inv` and `has_continuous_neg` type classes. The `has_continuous_neg` class will be helpful for generalizing `topological_ring` to the setting of `non_unital_non_assoc_semiring`s (see [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/continuous.20maps.20vanishing.20at.20infinity)). In addition, `ennreal` can have a `has_continuous_inv` instance.
#### Estimated changes
Modified src/topology/algebra/field.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* has_continuous_inv_Inf
- \+ *lemma* has_continuous_inv_inf
- \+ *lemma* has_continuous_inv_infi
- \+ *lemma* is_closed_set_of_map_inv
- \+/\- *lemma* is_compact.inv
- \+ *lemma* topological_group.continuous_conj'
- \+ *lemma* topological_group.continuous_conj_prod

Modified src/topology/continuous_function/algebra.lean




## [2022-03-24 10:12:39](https://github.com/leanprover-community/mathlib/commit/eabc619)
feat(ring_theory/polynomial): mv_polynomial over UFD is UFD ([#12866](https://github.com/leanprover-community/mathlib/pull/12866))
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/associated.lean
- \+ *lemma* comap_prime
- \+ *lemma* mul_equiv.prime_iff

Modified src/algebra/divisibility.lean
- \+ *lemma* map_dvd
- \+/\- *lemma* monoid_hom.map_dvd
- \+/\- *lemma* mul_hom.map_dvd

Modified src/algebra/ring/basic.lean
- \+/\- *lemma* ring_hom.map_dvd

Modified src/data/mv_polynomial/rename.lean
- \+ *lemma* mv_polynomial.exists_finset_rename₂
- \+ *def* mv_polynomial.kill_compl
- \+ *lemma* mv_polynomial.kill_compl_comp_rename
- \+ *lemma* mv_polynomial.kill_compl_rename_app

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* mv_polynomial.prime_C_iff
- \+ *lemma* mv_polynomial.prime_rename_iff
- \+ *lemma* polynomial.prime_C_iff

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* mul_equiv.unique_factorization_monoid
- \+ *lemma* mul_equiv.unique_factorization_monoid_iff



## [2022-03-24 10:12:38](https://github.com/leanprover-community/mathlib/commit/db76064)
feat(*): facts about degrees/multiplicites of derivatives ([#12856](https://github.com/leanprover-community/mathlib/pull/12856))
For `t` an `n`th repeated root of `p`, we prove that it is an `n-1`th repeated root of `p'` (and tidy the section around this). We also sharpen the theorem stating that `deg p' < deg p`.
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.derivative_of_nat_degree_zero
- \+/\- *theorem* polynomial.nat_degree_derivative_lt

Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.derivative_root_multiplicity_of_root
- \+ *lemma* polynomial.root_multiplicity_sub_one_le_derivative_root_multiplicity
- \+/\- *lemma* polynomial.roots_normalize

Modified src/field_theory/separable.lean




## [2022-03-24 10:12:37](https://github.com/leanprover-community/mathlib/commit/355645e)
chore(data/polynomial/*): delete, rename and move lemmas ([#12852](https://github.com/leanprover-community/mathlib/pull/12852))
- Replace `eval_eq_finset_sum` and `eval_eq_finset_sum'` with `eval_eq_sum_range` and `eval_eq_sum_range'` which are consistent with `eval₂_eq_sum_range`, `eval₂_eq_sum_range'` `eval_eq_finset_sum`, `eval_eq_finset_sum'`. Notice that the type of `eval_eq_sum_range'` is different, but this lemma has not been used anywhere in mathlib.
- Move the lemma `C_eq_int_cast` from `data/polynomial/degree/definitions.lean` to `data/polynomial/basic.lean`. `C_eq_nat_cast` was already here.
#### Estimated changes
Modified src/analysis/special_functions/polynomials.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.C_eq_int_cast

Modified src/data/polynomial/degree/definitions.lean
- \- *lemma* polynomial.C_eq_int_cast

Modified src/data/polynomial/eval.lean
- \- *lemma* polynomial.eval_eq_finset_sum'
- \- *lemma* polynomial.eval_eq_finset_sum
- \+ *lemma* polynomial.eval_eq_sum_range'
- \+ *lemma* polynomial.eval_eq_sum_range

Modified src/data/polynomial/mirror.lean


Modified src/ring_theory/polynomial/eisenstein.lean




## [2022-03-24 10:12:36](https://github.com/leanprover-community/mathlib/commit/c1fb0ed)
feat(algebra/associated): generalize nat.prime_mul_iff ([#12850](https://github.com/leanprover-community/mathlib/pull/12850))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* irreducible_is_unit_mul
- \+ *lemma* irreducible_mul_iff
- \+ *lemma* irreducible_mul_is_unit
- \+ *lemma* irreducible_mul_units
- \+ *lemma* irreducible_units_mul

Modified src/data/nat/prime.lean




## [2022-03-24 10:12:35](https://github.com/leanprover-community/mathlib/commit/a5a0d23)
feat(data/list/basic): nth_le+filter lemmas ([#12836](https://github.com/leanprover-community/mathlib/pull/12836))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.filter_singleton
- \+ *lemma* list.nth_le_cons
- \+ *lemma* list.nth_le_cons_aux



## [2022-03-24 10:12:34](https://github.com/leanprover-community/mathlib/commit/892e611)
feat(model_theory/*): Facts about countability of first-order structures ([#12819](https://github.com/leanprover-community/mathlib/pull/12819))
Shows that in a countable language, a structure is countably generated if and only if it is countable.
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean


Modified src/model_theory/basic.lean
- \+ *def* first_order.language.card
- \+ *lemma* first_order.language.card_eq_card_functions_add_card_relations
- \+ *lemma* first_order.language.card_functions_le_omega
- \+ *lemma* first_order.language.card_le_omega
- \+ *lemma* first_order.language.encodable.countable
- \+ *lemma* first_order.language.encodable.countable_functions

Modified src/model_theory/finitely_generated.lean
- \+ *lemma* first_order.language.Structure.cg_iff_countable
- \+/\- *theorem* first_order.language.substructure.cg_closure
- \+ *theorem* first_order.language.substructure.cg_iff_countable

Modified src/model_theory/substructures.lean
- \+ *lemma* set.countable.substructure_closure

Modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* first_order.language.term.card_le_omega



## [2022-03-24 10:12:32](https://github.com/leanprover-community/mathlib/commit/e6c6f00)
feat(number_theory/arithmetic_function): The moebius function is multiplicative ([#12796](https://github.com/leanprover-community/mathlib/pull/12796))
A fundamental property of the moebius function is that it is
multiplicative, which allows many facts about Euler products to be
expressed
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* nat.squarefree_mul
- \+ *lemma* squarefree.ne_zero
- \+ *lemma* squarefree.of_mul_left
- \+ *lemma* squarefree.of_mul_right

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.is_multiplicative.iff_ne_zero
- \+ *lemma* nat.arithmetic_function.is_multiplicative_moebius



## [2022-03-24 10:12:31](https://github.com/leanprover-community/mathlib/commit/0faebd2)
chore(fintype/card_embedding): generalize instances ([#12775](https://github.com/leanprover-community/mathlib/pull/12775))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_compl_set
- \+ *lemma* fintype.card_range
- \+ *theorem* set.to_finset_compl

Modified src/data/fintype/card_embedding.lean
- \+/\- *theorem* fintype.card_embedding_eq
- \+/\- *lemma* fintype.card_embedding_eq_of_infinite
- \+/\- *lemma* fintype.card_embedding_eq_of_unique

Modified src/data/set/finite.lean
- \- *lemma* set.to_finset_compl

Modified src/logic/embedding.lean
- \+ *def* function.embedding.option_embedding_equiv



## [2022-03-24 10:12:30](https://github.com/leanprover-community/mathlib/commit/0427430)
feat(number_theory/function_field): add completion with respect to place at infinity ([#12715](https://github.com/leanprover-community/mathlib/pull/12715))
#### Estimated changes
Modified src/number_theory/function_field.lean
- \+ *def* function_field.Fqt_infty
- \+ *lemma* function_field.infty_valued_Fqt.completable_top_field
- \+ *lemma* function_field.infty_valued_Fqt.def
- \+ *lemma* function_field.infty_valued_Fqt.separated_space
- \+ *lemma* function_field.infty_valued_Fqt.topological_division_ring
- \+ *def* function_field.infty_valued_Fqt.topological_space
- \+ *lemma* function_field.infty_valued_Fqt.uniform_add_group
- \+ *def* function_field.infty_valued_Fqt.uniform_space
- \+ *def* function_field.infty_valued_Fqt
- \+ *lemma* function_field.valued_Fqt_infty.def



## [2022-03-24 09:09:50](https://github.com/leanprover-community/mathlib/commit/ca93096)
feat(topology/nhds_set): add `has_basis_nhds_set` ([#12908](https://github.com/leanprover-community/mathlib/pull/12908))
Also add `nhds_set_union`.
#### Estimated changes
Modified src/topology/nhds_set.lean
- \+ *lemma* has_basis_nhds_set
- \+ *lemma* nhds_set_union



## [2022-03-24 07:09:35](https://github.com/leanprover-community/mathlib/commit/399ce38)
feat(measure_theory/integral): continuous functions with exponential decay are integrable ([#12539](https://github.com/leanprover-community/mathlib/pull/12539))
#### Estimated changes
Added src/measure_theory/integral/exp_decay.lean
- \+ *lemma* exp_neg_integrable_on_Ioi
- \+ *lemma* integrable_of_is_O_exp_neg
- \+ *lemma* integral_exp_neg_le



## [2022-03-24 05:18:39](https://github.com/leanprover-community/mathlib/commit/df34816)
feat(ring_theory/principal_ideal_domain): add some irreducible lemmas ([#12903](https://github.com/leanprover-community/mathlib/pull/12903))
#### Estimated changes
Modified src/ring_theory/principal_ideal_domain.lean
- \+ *theorem* irreducible.coprime_or_dvd
- \+ *theorem* irreducible.coprime_pow_of_not_dvd
- \+ *theorem* irreducible.dvd_iff_not_coprime



## [2022-03-24 05:18:38](https://github.com/leanprover-community/mathlib/commit/a978115)
refactor(category_theory/abelian): trivial generalisations ([#12897](https://github.com/leanprover-community/mathlib/pull/12897))
Trivial generalisations of some facts in `category_theory/abelian/non_preadditive.lean`.
They are true more generally, and this refactor will make it easier to do some other clean-up I'd like to perform on abelian categories.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \- *lemma* category_theory.abelian.epi_of_zero_cokernel
- \- *lemma* category_theory.abelian.mono_of_zero_kernel

Modified src/category_theory/abelian/non_preadditive.lean
- \- *lemma* category_theory.non_preadditive_abelian.epi_of_zero_cancel
- \- *lemma* category_theory.non_preadditive_abelian.epi_of_zero_cokernel
- \- *lemma* category_theory.non_preadditive_abelian.has_colimit_parallel_pair
- \- *lemma* category_theory.non_preadditive_abelian.has_limit_parallel_pair
- \- *lemma* category_theory.non_preadditive_abelian.mono_of_cancel_zero
- \- *lemma* category_theory.non_preadditive_abelian.mono_of_zero_kernel
- \- *lemma* category_theory.non_preadditive_abelian.pullback_of_mono
- \- *lemma* category_theory.non_preadditive_abelian.pushout_of_epi
- \- *def* category_theory.non_preadditive_abelian.zero_cokernel_of_zero_cancel
- \- *def* category_theory.non_preadditive_abelian.zero_kernel_of_cancel_zero

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.zero_cokernel_of_zero_cancel
- \+ *def* category_theory.limits.zero_kernel_of_cancel_zero

Renamed src/category_theory/limits/shapes/normal_mono.lean to src/category_theory/limits/shapes/normal_mono/basic.lean


Added src/category_theory/limits/shapes/normal_mono/equalizers.lean
- \+ *lemma* category_theory.normal_epi_category.has_colimit_parallel_pair
- \+ *lemma* category_theory.normal_epi_category.mono_of_cancel_zero
- \+ *lemma* category_theory.normal_epi_category.mono_of_zero_kernel
- \+ *lemma* category_theory.normal_epi_category.pushout_of_epi
- \+ *lemma* category_theory.normal_mono_category.epi_of_zero_cancel
- \+ *lemma* category_theory.normal_mono_category.epi_of_zero_cokernel
- \+ *lemma* category_theory.normal_mono_category.has_limit_parallel_pair
- \+ *lemma* category_theory.normal_mono_category.pullback_of_mono



## [2022-03-24 05:18:37](https://github.com/leanprover-community/mathlib/commit/d4e27d0)
chore(topology/separation): move a lemma, golf ([#12896](https://github.com/leanprover-community/mathlib/pull/12896))
* move `t0_space_of_injective_of_continuous` up;
* add `embedding.t0_space`, use it for `subtype.t0_space`.
#### Estimated changes
Modified src/topology/separation.lean
- \+/\- *lemma* t0_space_of_injective_of_continuous



## [2022-03-24 05:18:35](https://github.com/leanprover-community/mathlib/commit/e968b6d)
feat(topology/continuous_function/bounded): add `bounded_continuous_function.tendsto_iff_tendsto_uniformly` ([#12894](https://github.com/leanprover-community/mathlib/pull/12894))
This establishes that convergence in the metric on bounded continuous functions is equivalent to uniform convergence of the respective functions.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.tendsto_iff_tendsto_uniformly



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
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.eq_endpoints_or_mem_Ioo_of_mem_Icc
- \+ *lemma* set.eq_left_or_mem_Ioo_of_mem_Ico
- \+ *lemma* set.eq_right_or_mem_Ioo_of_mem_Ioc
- \- *lemma* set.mem_Ioo_or_eq_endpoints_of_mem_Icc
- \- *lemma* set.mem_Ioo_or_eq_left_of_mem_Ico
- \- *lemma* set.mem_Ioo_or_eq_right_of_mem_Ioc

Modified src/data/set/intervals/surj_on.lean


Modified src/topology/algebra/order/extend_from.lean




## [2022-03-24 05:18:33](https://github.com/leanprover-community/mathlib/commit/5ef365a)
feat(topology/separation): generalize tendsto_const_nhds_iff to t1_space ([#12883](https://github.com/leanprover-community/mathlib/pull/12883))
I noticed this when working on the sphere eversion project
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.map_const

Modified src/topology/separation.lean
- \+ *lemma* pure_le_nhds_iff
- \+/\- *lemma* tendsto_const_nhds_iff



## [2022-03-24 05:18:32](https://github.com/leanprover-community/mathlib/commit/6696bdd)
docs(data/set/pairwise): Explain preference for `s.pairwise_disjoint id` ([#12878](https://github.com/leanprover-community/mathlib/pull/12878))
... over `s.pairwise disjoint`.
#### Estimated changes
Modified src/data/set/pairwise.lean




## [2022-03-24 05:18:31](https://github.com/leanprover-community/mathlib/commit/30449be)
feat(data/complex/is_R_or_C): generalize `is_R_or_C.proper_space_span_singleton` to all finite dimensional submodules ([#12877](https://github.com/leanprover-community/mathlib/pull/12877))
Also goes on to show that finite supremums of finite_dimensional submodules are finite-dimensional.
#### Estimated changes
Modified src/data/complex/is_R_or_C.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2022-03-24 05:18:30](https://github.com/leanprover-community/mathlib/commit/debdd90)
feat(tactic/ext): support rintro patterns in `ext` ([#12875](https://github.com/leanprover-community/mathlib/pull/12875))
The change is actually quite simple, since `rintro_pat*` has approximately the same type as `rcases_pat*`.
#### Estimated changes
Modified src/tactic/congr.lean


Modified src/tactic/ext.lean


Modified test/ext.lean




## [2022-03-24 05:18:29](https://github.com/leanprover-community/mathlib/commit/8e50164)
chore(data/int/basic): remove some `eq.mpr`s from `int.induction_on'` ([#12873](https://github.com/leanprover-community/mathlib/pull/12873))
#### Estimated changes
Modified src/data/int/basic.lean




## [2022-03-24 05:18:27](https://github.com/leanprover-community/mathlib/commit/ae69578)
fix(ring_theory/algebraic): Make `is_transcendental_of_subsingleton` fully general ([#12870](https://github.com/leanprover-community/mathlib/pull/12870))
I mistyped a single letter.
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+/\- *lemma* is_transcendental_of_subsingleton



## [2022-03-24 05:18:26](https://github.com/leanprover-community/mathlib/commit/706a824)
feat(data/{nat, real}/sqrt): Some simple facts about square roots ([#12851](https://github.com/leanprover-community/mathlib/pull/12851))
Prove that sqrt 1 = 1 in the natural numbers and an order relationship between real and natural square roots.
#### Estimated changes
Modified src/data/nat/sqrt.lean
- \+ *lemma* nat.sqrt_one

Modified src/data/real/sqrt.lean
- \+ *lemma* real.nat_sqrt_le_real_sqrt
- \+ *lemma* real.real_sqrt_le_nat_sqrt_succ



## [2022-03-24 05:18:25](https://github.com/leanprover-community/mathlib/commit/ec434b7)
feat(group_theory/order_of_element): finite orderness is closed under mul ([#12750](https://github.com/leanprover-community/mathlib/pull/12750))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* commute.is_of_fin_order_mul
- \+ *lemma* is_of_fin_order.inv
- \+ *lemma* is_of_fin_order.mul
- \- *lemma* is_of_fin_order_inv
- \+ *lemma* order_of_pos_iff



## [2022-03-24 05:18:24](https://github.com/leanprover-community/mathlib/commit/c705d41)
feat(analysis/locally_convex): characterize the natural bornology in terms of seminorms ([#12721](https://github.com/leanprover-community/mathlib/pull/12721))
Add four lemmas:
* `is_vonN_bounded_basis_iff`: it suffices to check boundedness for a basis
* `seminorm_family.has_basis`: the basis sets form a basis of the topology
* `is_bounded_iff_finset_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for all finite suprema of seminorms
* `is_bounded_iff_seminorm_bounded`: a set is von Neumann bounded iff it is bounded for each seminorm
Also make the set argument in `seminorm_family.basis_sets_iff` implicit.
#### Estimated changes
Modified src/analysis/locally_convex/bounded.lean
- \+ *lemma* filter.has_basis.is_vonN_bounded_basis_iff

Modified src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* bornology.is_vonN_bounded_iff_finset_seminorm_bounded
- \+ *lemma* bornology.is_vonN_bounded_iff_seminorm_bounded
- \+/\- *lemma* seminorm_family.basis_sets_iff
- \+ *lemma* seminorm_family.has_basis



## [2022-03-24 05:18:23](https://github.com/leanprover-community/mathlib/commit/cbd1e98)
chore(algebra/category/*): simp lemmas for of_hom ([#12638](https://github.com/leanprover-community/mathlib/pull/12638))
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+ *lemma* Algebra.of_hom_apply

Modified src/algebra/category/CommRing/basic.lean
- \+ *lemma* CommRing.of_hom_apply
- \+ *lemma* CommSemiRing.of_hom_apply
- \+ *lemma* Ring.of_hom_apply
- \+ *lemma* SemiRing.of_hom_apply

Modified src/algebra/category/Group/basic.lean
- \+ *lemma* CommGroup.of_hom_apply
- \+ *lemma* Group.of_hom_apply

Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.of_hom_apply

Modified src/algebra/category/Mon/basic.lean
- \+ *lemma* Mon.of_hom_apply

Modified src/algebra/category/Semigroup/basic.lean
- \+ *lemma* Magma.of_hom_apply
- \+ *lemma* Semigroup.of_hom_apply



## [2022-03-24 04:46:31](https://github.com/leanprover-community/mathlib/commit/7967128)
feat(data/complex/basic): `#ℂ = 𝔠` ([#12871](https://github.com/leanprover-community/mathlib/pull/12871))
#### Estimated changes
Added src/data/complex/cardinality.lean
- \+ *theorem* mk_complex
- \+ *lemma* mk_univ_complex
- \+ *lemma* not_countable_complex



## [2022-03-23 23:02:08](https://github.com/leanprover-community/mathlib/commit/584ae9d)
chore(data/{lists,multiset}/*): More dot notation ([#12876](https://github.com/leanprover-community/mathlib/pull/12876))
Rename many `list` and `multiset` lemmas to make them eligible to dot notation. Also add a few aliases to `↔` lemmas for even more dot notation.
Renames
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/combinatorics/simple_graph/connectivity.lean


Modified src/data/equiv/list.lean


Modified src/data/fin_enum.lean


Modified src/data/finset/basic.lean
- \+/\- *def* finset.erase
- \+/\- *def* finset.filter
- \+ *lemma* finset.image_val_of_inj_on
- \- *theorem* finset.image_val_of_inj_on
- \+ *lemma* finset.insert_def
- \- *theorem* finset.insert_def
- \+/\- *def* finset.map
- \+ *lemma* finset.not_mem_erase
- \- *theorem* finset.not_mem_erase

Modified src/data/finset/fin.lean


Modified src/data/finset/noncomm_prod.lean


Modified src/data/finset/option.lean


Modified src/data/finset/pi.lean


Modified src/data/finset/powerset.lean


Modified src/data/finset/prod.lean


Modified src/data/finset/sigma.lean


Modified src/data/fintype/basic.lean


Modified src/data/hash_map.lean


Modified src/data/list/alist.lean
- \+/\- *def* alist.erase
- \+ *lemma* alist.keys_erase
- \- *theorem* alist.keys_erase

Modified src/data/list/cycle.lean


Modified src/data/list/nat_antidiagonal.lean


Modified src/data/list/nodup.lean
- \- *lemma* list.diff_eq_filter_of_nodup
- \- *lemma* list.mem_diff_iff_of_nodup
- \- *theorem* list.mem_erase_iff_of_nodup
- \- *theorem* list.mem_erase_of_nodup
- \+ *lemma* list.nodup.append
- \+ *lemma* list.nodup.diff
- \+ *lemma* list.nodup.diff_eq_filter
- \+ *lemma* list.nodup.erase
- \+ *lemma* list.nodup.erase_eq_filter
- \+ *lemma* list.nodup.filter
- \+ *lemma* list.nodup.insert
- \+ *lemma* list.nodup.inter
- \+ *lemma* list.nodup.map_on
- \+ *lemma* list.nodup.mem_diff_iff
- \+ *lemma* list.nodup.mem_erase_iff
- \+ *lemma* list.nodup.not_mem
- \+ *lemma* list.nodup.not_mem_erase
- \+ *lemma* list.nodup.of_append_left
- \+ *lemma* list.nodup.of_append_right
- \+ *lemma* list.nodup.of_cons
- \+ *lemma* list.nodup.of_map
- \+ *lemma* list.nodup.pmap
- \+ *lemma* list.nodup.sigma
- \+ *lemma* list.nodup.union
- \- *theorem* list.nodup_append_of_nodup
- \- *theorem* list.nodup_concat
- \- *theorem* list.nodup_cons_of_nodup
- \- *theorem* list.nodup_diff
- \- *theorem* list.nodup_erase_eq_filter
- \- *theorem* list.nodup_erase_of_nodup
- \- *theorem* list.nodup_filter
- \- *theorem* list.nodup_filter_map
- \- *theorem* list.nodup_insert
- \- *theorem* list.nodup_inter_of_nodup
- \- *theorem* list.nodup_map
- \- *theorem* list.nodup_map_on
- \- *theorem* list.nodup_of_nodup_append_left
- \- *theorem* list.nodup_of_nodup_append_right
- \- *theorem* list.nodup_of_nodup_cons
- \- *theorem* list.nodup_of_nodup_map
- \- *theorem* list.nodup_of_sublist
- \- *theorem* list.nodup_pmap
- \- *theorem* list.nodup_product
- \- *theorem* list.nodup_sigma
- \+ *lemma* list.nodup_singleton
- \- *theorem* list.nodup_singleton
- \+/\- *lemma* list.nodup_sublists_len
- \- *theorem* list.nodup_union
- \- *lemma* list.nodup_update_nth
- \- *theorem* list.not_mem_of_nodup_cons
- \+ *lemma* list.not_nodup_cons_of_mem
- \- *theorem* list.not_nodup_cons_of_mem

Modified src/data/list/pairwise.lean
- \- *theorem* list.forall_of_forall_of_pairwise
- \- *lemma* list.forall_of_pairwise
- \+ *lemma* list.pairwise.and
- \- *theorem* list.pairwise.and
- \+ *lemma* list.pairwise.filter
- \+ *theorem* list.pairwise.filter_map
- \+ *lemma* list.pairwise.forall
- \+ *lemma* list.pairwise.forall_of_forall
- \+ *lemma* list.pairwise.imp
- \- *theorem* list.pairwise.imp
- \+ *lemma* list.pairwise.imp₂
- \- *theorem* list.pairwise.imp₂
- \+ *lemma* list.pairwise.map
- \+ *lemma* list.pairwise.of_cons
- \+ *lemma* list.pairwise.of_map
- \+/\- *lemma* list.pairwise.set_pairwise
- \+ *theorem* list.pairwise.sublists'
- \+ *lemma* list.pairwise_and_iff
- \- *theorem* list.pairwise_filter_map_of_pairwise
- \- *theorem* list.pairwise_filter_of_pairwise
- \- *theorem* list.pairwise_map_of_pairwise
- \- *theorem* list.pairwise_of_pairwise_cons
- \- *theorem* list.pairwise_of_pairwise_map
- \- *theorem* list.pairwise_of_sublist
- \- *theorem* list.pairwise_sublists'
- \+ *lemma* list.pw_filter_idempotent
- \- *theorem* list.pw_filter_idempotent
- \+ *lemma* list.rel_of_pairwise_cons
- \- *theorem* list.rel_of_pairwise_cons

Modified src/data/list/perm.lean
- \- *theorem* list.subperm_of_subset_nodup

Modified src/data/list/range.lean


Modified src/data/list/sigma.lean
- \- *theorem* list.kerase_nodupkeys
- \- *theorem* list.kunion_nodupkeys
- \- *theorem* list.nodup_of_nodupkeys
- \+ *lemma* list.nodupkeys.kerase
- \+ *lemma* list.nodupkeys.kunion
- \+ *theorem* list.nodupkeys.sublist
- \- *theorem* list.nodupkeys_of_sublist

Modified src/data/list/sort.lean
- \+ *lemma* list.sorted.of_cons
- \- *theorem* list.sorted_of_sorted_cons

Modified src/data/multiset/dedup.lean


Modified src/data/multiset/finset_ops.lean
- \+ *lemma* multiset.nodup.ndinsert
- \+ *lemma* multiset.nodup.ndinter
- \+ *lemma* multiset.nodup.ndunion
- \- *theorem* multiset.nodup_ndinsert
- \- *theorem* multiset.nodup_ndinter
- \- *theorem* multiset.nodup_ndunion

Modified src/data/multiset/locally_finite.lean


Modified src/data/multiset/nodup.lean
- \- *lemma* multiset.forall_of_pairwise
- \- *theorem* multiset.mem_erase_iff_of_nodup
- \- *theorem* multiset.mem_erase_of_nodup
- \+ *lemma* multiset.nodup.add_iff
- \+ *lemma* multiset.nodup.cons
- \+ *lemma* multiset.nodup.erase
- \+ *lemma* multiset.nodup.erase_eq_filter
- \+ *lemma* multiset.nodup.ext
- \+ *lemma* multiset.nodup.filter
- \+ *lemma* multiset.nodup.inter_left
- \+ *lemma* multiset.nodup.inter_right
- \+ *lemma* multiset.nodup.map
- \+ *lemma* multiset.nodup.map_on
- \+ *lemma* multiset.nodup.mem_erase_iff
- \+ *theorem* multiset.nodup.not_mem
- \+ *lemma* multiset.nodup.not_mem_erase
- \+ *lemma* multiset.nodup.of_cons
- \+ *lemma* multiset.nodup.of_map
- \+ *lemma* multiset.nodup.pmap
- \- *theorem* multiset.nodup_add_of_nodup
- \- *theorem* multiset.nodup_cons_of_nodup
- \- *theorem* multiset.nodup_erase_eq_filter
- \- *theorem* multiset.nodup_erase_of_nodup
- \- *theorem* multiset.nodup_ext
- \- *theorem* multiset.nodup_filter
- \- *theorem* multiset.nodup_filter_map
- \- *theorem* multiset.nodup_inter_left
- \- *theorem* multiset.nodup_inter_right
- \- *theorem* multiset.nodup_map
- \- *theorem* multiset.nodup_map_on
- \- *theorem* multiset.nodup_of_nodup_cons
- \- *theorem* multiset.nodup_of_nodup_map
- \- *theorem* multiset.nodup_pmap
- \- *theorem* multiset.nodup_powerset_len
- \- *theorem* multiset.nodup_product
- \- *theorem* multiset.nodup_sigma
- \- *theorem* multiset.not_mem_of_nodup_cons
- \+ *lemma* multiset.pairwise.forall
- \- *lemma* multiset.pairwise_of_nodup

Modified src/data/multiset/pi.lean
- \- *lemma* multiset.nodup_pi

Modified src/data/multiset/sum.lean


Modified src/data/set/finite.lean


Modified src/data/tprod.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/list.lean


Modified src/ring_theory/discriminant.lean


Modified src/testing/slim_check/functions.lean




## [2022-03-23 21:13:19](https://github.com/leanprover-community/mathlib/commit/e620519)
feat(order/hom/*): more superclass instances for `order_iso_class` ([#12889](https://github.com/leanprover-community/mathlib/pull/12889))
 * Weaken hypotheses on `order_hom_class` and some subclasses
 * Add more instances deriving specific order hom classes from `order_iso_class`
#### Estimated changes
Modified src/order/hom/basic.lean
- \+/\- *abbreviation* order_hom_class

Modified src/order/hom/bounded.lean


Modified src/order/hom/complete_lattice.lean


Modified src/order/hom/lattice.lean




## [2022-03-23 21:13:18](https://github.com/leanprover-community/mathlib/commit/3b8d217)
refactor(order/upper_lower): Use `⨆` rather than `Sup` ([#12644](https://github.com/leanprover-community/mathlib/pull/12644))
Turn `Sup (coe '' S)` into  `⋃ s ∈ S, ↑s` and other similar changes. This greatly simplifies the proofs.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/order/upper_lower.lean
- \+ *lemma* lower_set.carrier_eq_coe
- \+/\- *lemma* lower_set.coe_Inf
- \+/\- *lemma* lower_set.coe_Sup
- \+/\- *lemma* lower_set.coe_infi
- \+/\- *lemma* lower_set.coe_infi₂
- \+/\- *lemma* lower_set.coe_supr
- \+/\- *lemma* lower_set.coe_supr₂
- \+ *lemma* lower_set.mem_compl_iff
- \+ *lemma* upper_set.carrier_eq_coe
- \+/\- *lemma* upper_set.coe_Inf
- \+/\- *lemma* upper_set.coe_Sup
- \+/\- *lemma* upper_set.coe_infi
- \+/\- *lemma* upper_set.coe_infi₂
- \+/\- *lemma* upper_set.coe_supr
- \+/\- *lemma* upper_set.coe_supr₂
- \+ *lemma* upper_set.mem_compl_iff

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* homogeneous_ideal.coe_bot
- \+ *lemma* homogeneous_ideal.coe_inf
- \+ *lemma* homogeneous_ideal.coe_sup
- \- *lemma* homogeneous_ideal.coe_supr
- \+ *lemma* homogeneous_ideal.coe_top
- \+/\- *lemma* homogeneous_ideal.to_ideal_infi
- \+ *lemma* homogeneous_ideal.to_ideal_infi₂
- \+ *lemma* homogeneous_ideal.to_ideal_supr
- \+ *lemma* homogeneous_ideal.to_ideal_supr₂
- \+/\- *lemma* ideal.is_homogeneous.Sup
- \+ *lemma* ideal.is_homogeneous.infi₂
- \+ *lemma* ideal.is_homogeneous.supr₂

Modified src/ring_theory/graded_algebra/radical.lean




## [2022-03-23 20:36:51](https://github.com/leanprover-community/mathlib/commit/cd94287)
feat(category_theory/abelian): right derived functor in abelian category with enough injectives ([#12810](https://github.com/leanprover-community/mathlib/pull/12810))
This pr shows that in an abelian category with enough injectives, if a functor preserves finite limits, then the zeroth right derived functor is naturally isomorphic to itself.  Dual to [#12403](https://github.com/leanprover-community/mathlib/pull/12403) ↔️
#### Estimated changes
Modified src/category_theory/abelian/right_derived.lean
- \+ *lemma* category_theory.abelian.functor.exact_of_map_injective_resolution
- \+ *lemma* category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono
- \+ *def* category_theory.abelian.functor.right_derived_zero_iso_self
- \+ *def* category_theory.abelian.functor.right_derived_zero_to_self_app
- \+ *lemma* category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv
- \+ *def* category_theory.abelian.functor.right_derived_zero_to_self_app_inv
- \+ *lemma* category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp
- \+ *def* category_theory.abelian.functor.right_derived_zero_to_self_app_iso
- \+ *lemma* category_theory.abelian.functor.right_derived_zero_to_self_natural



## [2022-03-23 20:36:49](https://github.com/leanprover-community/mathlib/commit/84a438e)
refactor(algebraic_geometry/*): rename structure sheaf to `Spec.structure_sheaf` ([#12785](https://github.com/leanprover-community/mathlib/pull/12785))
Following [this Zulip message](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rename.20.60structure_sheaf.60.20to.20.60Spec.2Estructure_sheaf.60/near/275649595), this pr renames `structure_sheaf` to `Spec.structure_sheaf`
#### Estimated changes
Modified src/algebraic_geometry/AffineScheme.lean


Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *def* algebraic_geometry.Spec.structure_sheaf
- \- *def* algebraic_geometry.structure_sheaf



## [2022-03-23 12:35:46](https://github.com/leanprover-community/mathlib/commit/16fb8e2)
chore(model_theory/terms_and_formulas): `realize_to_prenex` ([#12884](https://github.com/leanprover-community/mathlib/pull/12884))
Proves that `phi.to_prenex` has the same realization in a nonempty structure as the original formula `phi` directly, rather than using `semantically_equivalent`.
#### Estimated changes
Modified src/model_theory/terms_and_formulas.lean
- \- *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_to_prenex_imp
- \- *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.realize_to_prenex_imp_right



## [2022-03-23 12:35:45](https://github.com/leanprover-community/mathlib/commit/64472d7)
feat(ring_theory/polynomial/basic): the isomorphism between `R[a]/I[a]` and `(R/I[X])/(f mod I)` for `a` a root of polynomial `f` and `I` and ideal of `R` ([#12646](https://github.com/leanprover-community/mathlib/pull/12646))
This PR defines the isomorphism between the ring `R[a]/I[a]` and the ring `(R/I[X])/(f mod I)` for `a` a root of the polynomial `f` with coefficients in `R` and `I` an ideal of `R`. This is useful for proving the Dedekind-Kummer Theorem.
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean
- \+ *def* adjoin_root.polynomial.quot_quot_equiv_comm
- \+ *lemma* adjoin_root.polynomial.quot_quot_equiv_comm_mk_mk
- \+ *lemma* adjoin_root.quot_adjoin_root_equiv_quot_polynomial_quot_mk_of
- \+ *def* adjoin_root.quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk
- \+ *lemma* adjoin_root.quot_map_C_map_span_mk_equiv_quot_map_C_quot_map_span_mk_mk
- \+ *def* adjoin_root.quot_map_of_equiv
- \+ *def* adjoin_root.quot_map_of_equiv_quot_map_C_map_span_mk
- \+ *lemma* adjoin_root.quot_map_of_equiv_quot_map_C_map_span_mk_mk

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.quotient_equiv_mk
- \+ *lemma* ideal.quotient_equiv_symm_mk



## [2022-03-23 10:41:04](https://github.com/leanprover-community/mathlib/commit/9126310)
chore(docs/references): Remove duplicate key ([#12901](https://github.com/leanprover-community/mathlib/pull/12901))
and clean up the rest while I'm at it.
#### Estimated changes
Modified docs/references.bib




## [2022-03-23 10:41:02](https://github.com/leanprover-community/mathlib/commit/2308b53)
feat(model_theory/terms_and_formulas): Make `Theory.model` a class ([#12867](https://github.com/leanprover-community/mathlib/pull/12867))
Makes `Theory.model` a class
#### Estimated changes
Modified src/model_theory/elementary_maps.lean


Modified src/model_theory/terms_and_formulas.lean
- \- *lemma* first_order.language.Theory.is_satisfiable.some_model_models
- \+/\- *lemma* first_order.language.Theory.model.mono
- \- *def* first_order.language.Theory.model
- \+/\- *def* first_order.language.Theory.models_bounded_formula
- \+/\- *lemma* first_order.language.Theory.models_formula_iff
- \+/\- *lemma* first_order.language.Theory.models_sentence_iff
- \+ *lemma* first_order.language.Theory.realize_sentence_of_mem
- \+/\- *lemma* first_order.language.Theory.semantically_equivalent.refl
- \+/\- *lemma* first_order.language.Theory.semantically_equivalent.symm
- \+/\- *lemma* first_order.language.Theory.semantically_equivalent.trans

Modified src/model_theory/ultraproducts.lean




## [2022-03-23 10:08:10](https://github.com/leanprover-community/mathlib/commit/92f2669)
feat(algebra/homology/quasi_iso): 2-out-of-3 property ([#12898](https://github.com/leanprover-community/mathlib/pull/12898))
#### Estimated changes
Modified src/algebra/homology/quasi_iso.lean
- \+ *lemma* quasi_iso_of_comp_left
- \+ *lemma* quasi_iso_of_comp_right



## [2022-03-23 08:42:10](https://github.com/leanprover-community/mathlib/commit/11a365d)
feat(linear_algebra/matrix): add variants of the existing `det_units_conj` lemmas ([#12881](https://github.com/leanprover-community/mathlib/pull/12881))
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \- *lemma* matrix.det_conj
- \+ *lemma* matrix.det_conj_of_mul_eq_one

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.coe_units_inv
- \+ *lemma* matrix.det_conj'
- \+ *lemma* matrix.det_conj

Modified src/linear_algebra/matrix/zpow.lean
- \+ *lemma* matrix.coe_units_zpow
- \- *lemma* matrix.units.coe_inv''
- \- *lemma* matrix.units.coe_zpow



## [2022-03-23 00:37:13](https://github.com/leanprover-community/mathlib/commit/c60bfca)
chore(data/nat/prime): golf nat.dvd_prime_pow ([#12886](https://github.com/leanprover-community/mathlib/pull/12886))
#### Estimated changes
Modified src/data/nat/prime.lean




## [2022-03-22 22:13:57](https://github.com/leanprover-community/mathlib/commit/d711d2a)
feat(set_theory/ordinal): Small iff cardinality less than `cardinal.univ` ([#12887](https://github.com/leanprover-community/mathlib/pull/12887))
Characterizes when a type is small in terms of its cardinality
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* cardinal.small_iff_lift_mk_lt_univ

Modified src/set_theory/ordinal_arithmetic.lean




## [2022-03-22 20:22:10](https://github.com/leanprover-community/mathlib/commit/3838b85)
feat(model_theory/*): Language equivalences ([#12837](https://github.com/leanprover-community/mathlib/pull/12837))
Defines equivalences between first-order languages
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* first_order.language.Lequiv.add_empty_constants
- \+ *structure* first_order.language.Lequiv
- \+/\- *def* first_order.language.Lhom.comp
- \+ *lemma* first_order.language.Lhom.comp_assoc
- \+/\- *lemma* first_order.language.Lhom.comp_id
- \+ *theorem* first_order.language.Lhom.comp_sum_elim
- \+/\- *lemma* first_order.language.Lhom.id_comp
- \+ *lemma* first_order.language.Lhom.map_constants_comp_sum_inl
- \- *lemma* first_order.language.Lhom.map_constants_comp_with_constants
- \- *def* first_order.language.Lhom.sum_elim
- \+ *lemma* first_order.language.Lhom.sum_elim_comp_inl
- \+ *lemma* first_order.language.Lhom.sum_elim_comp_inr
- \+ *theorem* first_order.language.Lhom.sum_elim_inl_inr
- \+/\- *def* first_order.language.Lhom.sum_map
- \+ *lemma* first_order.language.Lhom.sum_map_comp_inl
- \+ *lemma* first_order.language.Lhom.sum_map_comp_inr
- \- *def* first_order.language.Lhom_trim_empty_constants
- \+/\- *def* first_order.language.Lhom_with_constants

Modified src/model_theory/definability.lean


Modified src/model_theory/terms_and_formulas.lean
- \+ *def* first_order.language.Lequiv.on_bounded_formula
- \+ *lemma* first_order.language.Lequiv.on_bounded_formula_symm
- \+ *def* first_order.language.Lequiv.on_formula
- \+ *lemma* first_order.language.Lequiv.on_formula_apply
- \+ *lemma* first_order.language.Lequiv.on_formula_symm
- \+ *def* first_order.language.Lequiv.on_sentence
- \+ *def* first_order.language.Lequiv.on_term
- \+ *lemma* first_order.language.Lhom.comp_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.comp_on_term
- \+ *lemma* first_order.language.Lhom.id_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.id_on_term
- \+/\- *def* first_order.language.Lhom.on_bounded_formula
- \+/\- *def* first_order.language.Lhom.on_formula
- \+/\- *def* first_order.language.Lhom.on_term
- \+/\- *lemma* first_order.language.Lhom.realize_on_term
- \+ *lemma* first_order.language.Lhom.set_of_realize_on_formula



## [2022-03-22 20:22:09](https://github.com/leanprover-community/mathlib/commit/f7905f0)
feat(order/concept): Concept lattices ([#12286](https://github.com/leanprover-community/mathlib/pull/12286))
Define `concept`, the type of concepts of a relation, and prove it forms a complete lattice.
#### Estimated changes
Modified docs/references.bib


Added src/order/concept.lean
- \+ *lemma* concept.Inf_fst
- \+ *lemma* concept.Inf_snd
- \+ *lemma* concept.Sup_fst
- \+ *lemma* concept.Sup_snd
- \+ *lemma* concept.bot_fst
- \+ *lemma* concept.bot_snd
- \+ *lemma* concept.ext'
- \+ *lemma* concept.ext
- \+ *lemma* concept.fst_injective
- \+ *lemma* concept.fst_ssubset_fst_iff
- \+ *lemma* concept.fst_subset_fst_iff
- \+ *lemma* concept.inf_fst
- \+ *lemma* concept.inf_snd
- \+ *lemma* concept.snd_injective
- \+ *lemma* concept.snd_ssubset_snd_iff
- \+ *lemma* concept.snd_subset_snd_iff
- \+ *lemma* concept.strict_anti_snd
- \+ *lemma* concept.strict_mono_fst
- \+ *lemma* concept.sup_fst
- \+ *lemma* concept.sup_snd
- \+ *def* concept.swap
- \+ *def* concept.swap_equiv
- \+ *lemma* concept.swap_le_swap_iff
- \+ *lemma* concept.swap_lt_swap_iff
- \+ *lemma* concept.swap_swap
- \+ *lemma* concept.top_fst
- \+ *lemma* concept.top_snd
- \+ *structure* concept
- \+ *def* extent_closure
- \+ *lemma* extent_closure_Union
- \+ *lemma* extent_closure_Union₂
- \+ *lemma* extent_closure_anti
- \+ *lemma* extent_closure_empty
- \+ *lemma* extent_closure_intent_closure_extent_closure
- \+ *lemma* extent_closure_swap
- \+ *lemma* extent_closure_union
- \+ *lemma* gc_intent_closure_extent_closure
- \+ *def* intent_closure
- \+ *lemma* intent_closure_Union
- \+ *lemma* intent_closure_Union₂
- \+ *lemma* intent_closure_anti
- \+ *lemma* intent_closure_empty
- \+ *lemma* intent_closure_extent_closure_intent_closure
- \+ *lemma* intent_closure_swap
- \+ *lemma* intent_closure_union
- \+ *lemma* subset_extent_closure_intent_closure
- \+ *lemma* subset_intent_closure_extent_closure
- \+ *lemma* subset_intent_closure_iff_subset_extent_closure



## [2022-03-22 20:22:08](https://github.com/leanprover-community/mathlib/commit/b226b4b)
feat(*): `has_repr` instances for `option`-like types ([#11282](https://github.com/leanprover-community/mathlib/pull/11282))
This provides the `has_repr` instance for `with_bot α`, `with_top α`, `with_zero α`, `with_one α`, `alexandroff α`.
#### Estimated changes
Modified src/algebra/group/with_one.lean


Modified src/order/bounded_order.lean


Modified src/topology/alexandroff.lean




## [2022-03-22 19:50:36](https://github.com/leanprover-community/mathlib/commit/980185a)
feat(algebra/{group,module}/ulift): Missing `ulift` instances ([#12879](https://github.com/leanprover-community/mathlib/pull/12879))
Add a few missing algebraic instances for `ulift` and golf a few existing ones.
#### Estimated changes
Modified src/algebra/group/ulift.lean


Modified src/algebra/module/ulift.lean




## [2022-03-22 14:24:51](https://github.com/leanprover-community/mathlib/commit/6a55ba8)
feat(algebra/subalgebra/basic): Missing scalar instances ([#12874](https://github.com/leanprover-community/mathlib/pull/12874))
Add missing scalar instances for `submonoid`, `subsemiring`, `subring`, `subalgebra`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *lemma* subalgebra.smul_def

Modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* submonoid.smul_def

Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* subring.smul_def

Modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* subsemiring.smul_def



## [2022-03-22 14:24:49](https://github.com/leanprover-community/mathlib/commit/5215940)
feat(order/filter/basic): `filter` is a `coframe` ([#12872](https://github.com/leanprover-community/mathlib/pull/12872))
Provide the `coframe (filter α)` instance and remove now duplicated lemmas.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.binfi_sup_left
- \- *lemma* filter.binfi_sup_right
- \- *lemma* filter.infi_sup_left
- \- *lemma* filter.infi_sup_right



## [2022-03-22 14:24:48](https://github.com/leanprover-community/mathlib/commit/1f47016)
refactor(order/hom/complete_lattice): Fix the definition of `frame_hom` ([#12855](https://github.com/leanprover-community/mathlib/pull/12855))
I misread "preserves finite meet" as "preserves binary meet", meaning that currently a `frame_hom` does not have to preserve `⊤` (subtly, preserving arbitrary join does not imply that either). This fixes my mistake.
#### Estimated changes
Modified src/order/hom/complete_lattice.lean
- \- *def* complete_lattice_hom.to_Inf_hom
- \+ *def* complete_lattice_hom.to_Sup_hom
- \- *lemma* frame_hom.bot_apply
- \- *lemma* frame_hom.coe_bot
- \+/\- *def* frame_hom.to_lattice_hom
- \+/\- *structure* frame_hom

Modified src/topology/sets/opens.lean




## [2022-03-22 12:35:31](https://github.com/leanprover-community/mathlib/commit/d586195)
feat(data/finset/pointwise): Missing operations ([#12865](https://github.com/leanprover-community/mathlib/pull/12865))
Define `-s`, `s⁻¹`, `s - t`, `s / t`, `s +ᵥ t`, `s • t`, `s -ᵥ t`, `a • s`, `a +ᵥ s` for `s`, `t` finsets, `a` scalar. Provide a bare API following what is already there for `s + t`, `s * t`.
#### Estimated changes
Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.card_inv
- \+ *lemma* finset.card_inv_le
- \+ *lemma* finset.coe_div
- \+ *lemma* finset.coe_inv
- \+/\- *lemma* finset.coe_pow
- \+ *lemma* finset.coe_smul
- \+ *lemma* finset.coe_smul_finset
- \+ *lemma* finset.coe_vsub
- \+ *lemma* finset.coe_zpow'
- \+ *lemma* finset.coe_zpow
- \+ *lemma* finset.div_card_le
- \+ *lemma* finset.div_def
- \+ *lemma* finset.div_empty
- \+ *lemma* finset.div_mem_div
- \+ *lemma* finset.div_nonempty_iff
- \+ *lemma* finset.div_singleton
- \+ *lemma* finset.div_subset_div
- \+ *lemma* finset.div_zero_subset
- \+ *lemma* finset.empty_div
- \+ *lemma* finset.empty_smul
- \+ *lemma* finset.empty_vsub
- \+ *lemma* finset.image_div_prod
- \+ *lemma* finset.image_inv
- \+ *lemma* finset.image_smul
- \+ *lemma* finset.image_smul_product
- \+ *lemma* finset.image_vsub_product
- \+ *lemma* finset.inv_def
- \+ *lemma* finset.inv_empty
- \+ *lemma* finset.inv_mem_inv
- \+ *lemma* finset.inv_nonempty_iff
- \+ *lemma* finset.inv_singleton
- \+ *lemma* finset.inv_subset_inv
- \+ *lemma* finset.mem_div
- \+ *lemma* finset.mem_inv
- \+ *lemma* finset.mem_smul
- \+ *lemma* finset.mem_smul_finset
- \+ *lemma* finset.mem_vsub
- \+/\- *lemma* finset.mul_card_le
- \+ *lemma* finset.nonempty.div_zero
- \+ *lemma* finset.nonempty.smul
- \+ *lemma* finset.nonempty.smul_finset
- \+ *lemma* finset.nonempty.vsub
- \+ *lemma* finset.nonempty.zero_div
- \+ *lemma* finset.preimage_inv
- \+ *lemma* finset.singleton_div
- \+ *lemma* finset.singleton_div_singleton
- \+ *lemma* finset.singleton_smul
- \+ *lemma* finset.singleton_smul_singleton
- \+ *lemma* finset.singleton_vsub
- \+ *lemma* finset.singleton_vsub_singleton
- \+ *lemma* finset.smul_card_le
- \+ *lemma* finset.smul_def
- \+ *lemma* finset.smul_empty
- \+ *lemma* finset.smul_finset_card_le
- \+ *lemma* finset.smul_finset_def
- \+ *lemma* finset.smul_finset_empty
- \+ *lemma* finset.smul_finset_mem_smul_finset
- \+ *lemma* finset.smul_finset_nonempty_iff
- \+ *lemma* finset.smul_finset_singleton
- \+ *lemma* finset.smul_finset_subset_smul_finset
- \+ *lemma* finset.smul_mem_smul
- \+ *lemma* finset.smul_nonempty_iff
- \+ *lemma* finset.smul_singleton
- \+ *lemma* finset.smul_subset_smul
- \+ *lemma* finset.subset_div
- \+ *lemma* finset.subset_smul
- \+ *lemma* finset.subset_vsub
- \+ *lemma* finset.vsub_card_le
- \+ *lemma* finset.vsub_def
- \+ *lemma* finset.vsub_empty
- \+ *lemma* finset.vsub_mem_vsub
- \+ *lemma* finset.vsub_nonempty_iff
- \+ *lemma* finset.vsub_singleton
- \+ *lemma* finset.vsub_subset_vsub
- \+ *lemma* finset.zero_div_subset

Modified src/data/set/pointwise.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/ring_theory/polynomial/eisenstein.lean




## [2022-03-22 09:42:58](https://github.com/leanprover-community/mathlib/commit/28eb06f)
feat(analysis/calculus): define `diff_on_int_cont` ([#12688](https://github.com/leanprover-community/mathlib/pull/12688))
#### Estimated changes
Added src/analysis/calculus/diff_on_int_cont.lean
- \+ *lemma* diff_on_int_cont.add
- \+ *lemma* diff_on_int_cont.add_const
- \+ *lemma* diff_on_int_cont.comp
- \+ *lemma* diff_on_int_cont.const_add
- \+ *lemma* diff_on_int_cont.const_smul
- \+ *lemma* diff_on_int_cont.const_sub
- \+ *lemma* diff_on_int_cont.differentiable_at'
- \+ *lemma* diff_on_int_cont.differentiable_on_ball
- \+ *lemma* diff_on_int_cont.inv
- \+ *lemma* diff_on_int_cont.mk_ball
- \+ *lemma* diff_on_int_cont.neg
- \+ *lemma* diff_on_int_cont.smul
- \+ *lemma* diff_on_int_cont.smul_const
- \+ *lemma* diff_on_int_cont.sub
- \+ *lemma* diff_on_int_cont.sub_const
- \+ *structure* diff_on_int_cont
- \+ *lemma* diff_on_int_cont_const
- \+ *lemma* diff_on_int_cont_open
- \+ *lemma* diff_on_int_cont_univ
- \+ *lemma* differentiable.comp_diff_on_int_cont
- \+ *lemma* differentiable.diff_on_int_cont
- \+ *lemma* differentiable_on.comp_diff_on_int_cont
- \+ *lemma* differentiable_on.diff_on_int_cont

Modified src/analysis/complex/abs_max.lean
- \+/\- *lemma* complex.norm_max_aux₂

Modified src/analysis/complex/cauchy_integral.lean
- \- *lemma* complex.circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on
- \- *lemma* complex.circle_integral_sub_inv_smul_of_differentiable_on
- \- *lemma* complex.has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
- \+ *lemma* diff_on_int_cont.circle_integral_sub_inv_smul
- \+ *lemma* diff_on_int_cont.has_fpower_series_on_ball
- \+ *lemma* differentiable_on.circle_integral_sub_inv_smul

Modified src/analysis/complex/liouville.lean


Modified src/analysis/complex/schwarz.lean




## [2022-03-22 09:42:57](https://github.com/leanprover-community/mathlib/commit/5826b2f)
feat(topology/order/hom/esakia): Esakia morphisms ([#12241](https://github.com/leanprover-community/mathlib/pull/12241))
Define pseudo-epimorphisms and Esakia morphisms following the hom refactor.
#### Estimated changes
Modified src/order/hom/lattice.lean


Added src/topology/order/hom/esakia.lean
- \+ *lemma* esakia_hom.cancel_left
- \+ *lemma* esakia_hom.cancel_right
- \+ *lemma* esakia_hom.coe_comp
- \+ *lemma* esakia_hom.coe_comp_continuous_order_hom
- \+ *lemma* esakia_hom.coe_comp_pseudo_epimorphism
- \+ *lemma* esakia_hom.coe_id
- \+ *lemma* esakia_hom.coe_id_continuous_order_hom
- \+ *lemma* esakia_hom.coe_id_pseudo_epimorphism
- \+ *def* esakia_hom.comp
- \+ *lemma* esakia_hom.comp_apply
- \+ *lemma* esakia_hom.comp_assoc
- \+ *lemma* esakia_hom.comp_id
- \+ *lemma* esakia_hom.ext
- \+ *lemma* esakia_hom.id_apply
- \+ *lemma* esakia_hom.id_comp
- \+ *lemma* esakia_hom.to_fun_eq_coe
- \+ *def* esakia_hom.to_pseudo_epimorphism
- \+ *structure* esakia_hom
- \+ *lemma* pseudo_epimorphism.cancel_left
- \+ *lemma* pseudo_epimorphism.cancel_right
- \+ *lemma* pseudo_epimorphism.coe_comp
- \+ *lemma* pseudo_epimorphism.coe_comp_order_hom
- \+ *lemma* pseudo_epimorphism.coe_id
- \+ *lemma* pseudo_epimorphism.coe_id_order_hom
- \+ *def* pseudo_epimorphism.comp
- \+ *lemma* pseudo_epimorphism.comp_apply
- \+ *lemma* pseudo_epimorphism.comp_assoc
- \+ *lemma* pseudo_epimorphism.comp_id
- \+ *lemma* pseudo_epimorphism.ext
- \+ *lemma* pseudo_epimorphism.id_apply
- \+ *lemma* pseudo_epimorphism.id_comp
- \+ *lemma* pseudo_epimorphism.to_fun_eq_coe
- \+ *structure* pseudo_epimorphism



## [2022-03-22 08:35:26](https://github.com/leanprover-community/mathlib/commit/41d291c)
feat(algebra/big_operators/associated): generalize prod_primes_dvd ([#12740](https://github.com/leanprover-community/mathlib/pull/12740))
#### Estimated changes
Modified src/algebra/big_operators/associated.lean
- \+ *lemma* finset.prod_primes_dvd
- \+ *lemma* multiset.prod_primes_dvd

Modified src/number_theory/primorial.lean
- \- *lemma* prod_primes_dvd



## [2022-03-22 08:03:55](https://github.com/leanprover-community/mathlib/commit/3ce4161)
refactor(measure_theory/integral): restrict interval integrals to real intervals ([#12754](https://github.com/leanprover-community/mathlib/pull/12754))
This way `∫ x in 0 .. 1, (1 : real)` means what it should, not `∫ x : nat in 0 .. 1, (1 : real)`.
#### Estimated changes
Modified src/analysis/calculus/parametric_interval_integral.lean
- \+/\- *lemma* interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le
- \+/\- *lemma* interval_integral.has_deriv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* interval_integral.has_fderiv_at_integral_of_dominated_loc_of_lip
- \+/\- *lemma* interval_integral.has_fderiv_at_integral_of_dominated_of_fderiv_le

Modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* measure_theory.integrable_of_interval_integral_norm_bounded
- \+/\- *lemma* measure_theory.integrable_of_interval_integral_norm_tendsto
- \+/\- *lemma* measure_theory.integrable_on_Iic_of_interval_integral_norm_bounded
- \+/\- *lemma* measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto
- \+/\- *lemma* measure_theory.integrable_on_Ioi_of_interval_integral_norm_bounded
- \+/\- *lemma* measure_theory.integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+/\- *lemma* measure_theory.interval_integral_tendsto_integral
- \+/\- *lemma* measure_theory.interval_integral_tendsto_integral_Iic
- \+/\- *lemma* measure_theory.interval_integral_tendsto_integral_Ioi

Modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* antitone.interval_integrable
- \+/\- *lemma* antitone_on.interval_integrable
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable
- \+/\- *lemma* filter.tendsto.eventually_interval_integrable_ae
- \+/\- *lemma* interval_integrable.abs
- \+/\- *lemma* interval_integrable.continuous_on_mul
- \+/\- *lemma* interval_integrable.def
- \+/\- *lemma* interval_integrable.mono
- \+/\- *lemma* interval_integrable.mono_fun'
- \+/\- *lemma* interval_integrable.mono_fun
- \+/\- *lemma* interval_integrable.mono_measure
- \+/\- *lemma* interval_integrable.mono_set
- \+/\- *lemma* interval_integrable.mono_set_ae
- \+/\- *lemma* interval_integrable.mul_continuous_on
- \+/\- *lemma* interval_integrable.trans_iterate
- \+/\- *def* interval_integrable
- \+/\- *lemma* interval_integrable_const
- \+/\- *lemma* interval_integrable_const_iff
- \+/\- *lemma* interval_integrable_iff
- \+/\- *lemma* interval_integrable_iff_integrable_Ioc_of_le
- \+/\- *lemma* interval_integral.FTC_filter.finite_at_inner
- \+/\- *lemma* interval_integral.abs_integral_eq_abs_integral_interval_oc
- \+/\- *lemma* interval_integral.continuous_of_dominated_interval
- \+/\- *lemma* interval_integral.continuous_on_primitive
- \+/\- *lemma* interval_integral.continuous_on_primitive_Icc
- \+/\- *lemma* interval_integral.continuous_on_primitive_interval'
- \+/\- *lemma* interval_integral.continuous_on_primitive_interval
- \+/\- *lemma* interval_integral.continuous_on_primitive_interval_left
- \+/\- *lemma* interval_integral.continuous_primitive
- \+/\- *lemma* interval_integral.continuous_within_at_primitive
- \+/\- *lemma* interval_integral.integral_cases
- \+/\- *lemma* interval_integral.integral_congr
- \+/\- *lemma* interval_integral.integral_congr_ae'
- \+/\- *lemma* interval_integral.integral_congr_ae
- \+/\- *lemma* interval_integral.integral_const
- \+/\- *lemma* interval_integral.integral_const_mul
- \+/\- *lemma* interval_integral.integral_div
- \+/\- *lemma* interval_integral.integral_eq_integral_of_support_subset
- \+/\- *lemma* interval_integral.integral_finset_sum
- \+/\- *lemma* interval_integral.integral_indicator
- \+/\- *lemma* interval_integral.integral_mono_on
- \+/\- *lemma* interval_integral.integral_mul_const
- \+/\- *lemma* interval_integral.integral_nonneg
- \+/\- *lemma* interval_integral.integral_smul_const
- \+/\- *lemma* interval_integral.integral_zero_ae
- \+/\- *lemma* interval_integral.interval_integral_eq_integral_interval_oc
- \+/\- *lemma* interval_integral.norm_integral_eq_norm_integral_Ioc
- \+/\- *lemma* interval_integral.norm_integral_min_max
- \+/\- *lemma* interval_integral.sub_le_integral_of_has_deriv_right_of_le
- \+/\- *lemma* interval_integral.sum_integral_adjacent_intervals
- \+/\- *def* interval_integral
- \+/\- *lemma* measure_theory.integrable.continuous_primitive
- \+/\- *lemma* measure_theory.integrable.interval_integrable
- \+/\- *lemma* measure_theory.integrable_on.interval_integrable
- \+/\- *lemma* monotone.interval_integrable
- \+/\- *lemma* monotone_on.interval_integrable



## [2022-03-22 06:15:55](https://github.com/leanprover-community/mathlib/commit/b0f585c)
feat(combinatorics/simple_graph/inc_matrix): Incidence matrix ([#10867](https://github.com/leanprover-community/mathlib/pull/10867))
Define the incidence matrix of a simple graph and prove the basics, including some stuff about matrix multiplication.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* ite_and_mul_zero

Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.card_incidence_finset_eq_degree
- \- *lemma* simple_graph.incidence_set_inter_incidence_set
- \+ *lemma* simple_graph.incidence_set_inter_incidence_set_of_adj
- \+ *lemma* simple_graph.incidence_set_inter_incidence_set_of_not_adj

Added src/combinatorics/simple_graph/inc_matrix.lean
- \+ *def* simple_graph.inc_matrix
- \+ *lemma* simple_graph.inc_matrix_apply'
- \+ *lemma* simple_graph.inc_matrix_apply
- \+ *lemma* simple_graph.inc_matrix_apply_eq_one_iff
- \+ *lemma* simple_graph.inc_matrix_apply_eq_zero_iff
- \+ *lemma* simple_graph.inc_matrix_apply_mul_inc_matrix_apply
- \+ *lemma* simple_graph.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj
- \+ *lemma* simple_graph.inc_matrix_mul_transpose
- \+ *lemma* simple_graph.inc_matrix_mul_transpose_apply_of_adj
- \+ *lemma* simple_graph.inc_matrix_mul_transpose_diag
- \+ *lemma* simple_graph.inc_matrix_of_mem_incidence_set
- \+ *lemma* simple_graph.inc_matrix_of_not_mem_incidence_set
- \+ *lemma* simple_graph.inc_matrix_transpose_mul_diag
- \+ *lemma* simple_graph.sum_inc_matrix_apply
- \+ *lemma* simple_graph.sum_inc_matrix_apply_of_mem_edge_set
- \+ *lemma* simple_graph.sum_inc_matrix_apply_of_not_mem_edge_set

Modified src/data/finset/card.lean
- \+ *lemma* finset.card_doubleton

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.coe_filter_univ
- \+ *lemma* set.filter_mem_univ_eq_to_finset

Modified src/linear_algebra/affine_space/combination.lean




## [2022-03-22 03:26:17](https://github.com/leanprover-community/mathlib/commit/01eb653)
chore(scripts): update nolints.txt ([#12868](https://github.com/leanprover-community/mathlib/pull/12868))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-22 01:36:27](https://github.com/leanprover-community/mathlib/commit/e51377f)
feat(logic/basic): `ulift.down` is injective ([#12824](https://github.com/leanprover-community/mathlib/pull/12824))
We also make the arguments to `plift.down_inj` inferred.
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* plift.down_inj
- \+ *lemma* plift.down_injective
- \+ *lemma* ulift.down_inj
- \+ *lemma* ulift.down_injective



## [2022-03-22 00:37:25](https://github.com/leanprover-community/mathlib/commit/d71e06c)
feat(topology/algebra/monoid): construct a unit from limits of units and their inverses ([#12760](https://github.com/leanprover-community/mathlib/pull/12760))
#### Estimated changes
Modified src/topology/algebra/monoid.lean
- \+ *def* filter.tendsto.units



## [2022-03-21 20:08:03](https://github.com/leanprover-community/mathlib/commit/f9dc84e)
feat(topology/continuous_function/units): basic results about units in `C(α, β)` ([#12687](https://github.com/leanprover-community/mathlib/pull/12687))
This establishes a few facts about units in `C(α, β)` including the equivalence `C(α, βˣ) ≃ C(α, β)ˣ`. Moreover, when `β` is a complete normed field, we show that the spectrum of `f : C(α, β)` is precisely `set.range f`.
#### Estimated changes
Added src/topology/continuous_function/units.lean
- \+ *lemma* continuous_map.is_unit_iff_forall_is_unit
- \+ *lemma* continuous_map.is_unit_iff_forall_ne_zero
- \+ *lemma* continuous_map.spectrum_eq_range
- \+ *def* continuous_map.units_lift
- \+ *lemma* normed_ring.is_unit_unit_continuous



## [2022-03-21 19:25:50](https://github.com/leanprover-community/mathlib/commit/8001ea5)
feat(category_theory/abelian): right derived functor ([#12841](https://github.com/leanprover-community/mathlib/pull/12841))
This pr dualises derived.lean. Right derived functor and natural transformation between right derived functors and related lemmas are formalised. 
The docs string currently contains more than what is in this file, but everything else will come shortly after.
#### Estimated changes
Modified src/category_theory/abelian/ext.lean


Renamed src/category_theory/abelian/derived.lean to src/category_theory/abelian/left_derived.lean


Added src/category_theory/abelian/right_derived.lean
- \+ *def* category_theory.functor.right_derived
- \+ *lemma* category_theory.functor.right_derived_map_eq
- \+ *def* category_theory.functor.right_derived_obj_injective_succ
- \+ *def* category_theory.functor.right_derived_obj_injective_zero
- \+ *def* category_theory.functor.right_derived_obj_iso
- \+ *def* category_theory.nat_trans.right_derived
- \+ *lemma* category_theory.nat_trans.right_derived_comp
- \+ *lemma* category_theory.nat_trans.right_derived_eq
- \+ *lemma* category_theory.nat_trans.right_derived_id

Renamed src/category_theory/functor/derived.lean to src/category_theory/functor/left_derived.lean


Modified src/category_theory/monoidal/tor.lean




## [2022-03-21 18:05:19](https://github.com/leanprover-community/mathlib/commit/25ec622)
feat(data/polynomial/eval + data/polynomial/ring_division): move a lemma and remove assumptions ([#12854](https://github.com/leanprover-community/mathlib/pull/12854))
A lemma about composition of polynomials assumed `comm_ring` and `is_domain`.  The new version assumes `semiring`.
I golfed slightly the original proof: it may very well be that a shorter proof is available!
I also moved the lemma, since it seems better for this lemma to appear in the file where the definition of `comp` appears.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.coeff_comp_degree_mul_degree

Modified src/data/polynomial/ring_division.lean
- \- *lemma* polynomial.coeff_comp_degree_mul_degree



## [2022-03-21 18:05:18](https://github.com/leanprover-community/mathlib/commit/fd4a034)
refactor(analysis/locally_convex/with_seminorms): use abbreviations to allow for dot notation ([#12846](https://github.com/leanprover-community/mathlib/pull/12846))
#### Estimated changes
Modified src/analysis/locally_convex/with_seminorms.lean
- \+/\- *lemma* seminorm.continuous_from_bounded
- \- *def* seminorm_add_group_filter_basis
- \- *def* seminorm_basis_zero
- \- *lemma* seminorm_basis_zero_add
- \- *lemma* seminorm_basis_zero_iff
- \- *lemma* seminorm_basis_zero_intersect
- \- *lemma* seminorm_basis_zero_mem
- \- *lemma* seminorm_basis_zero_neg
- \- *lemma* seminorm_basis_zero_nonempty
- \- *lemma* seminorm_basis_zero_singleton_mem
- \- *lemma* seminorm_basis_zero_smul
- \- *lemma* seminorm_basis_zero_smul_left
- \- *lemma* seminorm_basis_zero_smul_right
- \- *lemma* seminorm_basis_zero_zero
- \+ *def* seminorm_family.basis_sets
- \+ *lemma* seminorm_family.basis_sets_add
- \+ *lemma* seminorm_family.basis_sets_iff
- \+ *lemma* seminorm_family.basis_sets_intersect
- \+ *lemma* seminorm_family.basis_sets_mem
- \+ *lemma* seminorm_family.basis_sets_neg
- \+ *lemma* seminorm_family.basis_sets_nonempty
- \+ *lemma* seminorm_family.basis_sets_singleton_mem
- \+ *lemma* seminorm_family.basis_sets_smul
- \+ *lemma* seminorm_family.basis_sets_smul_left
- \+ *lemma* seminorm_family.basis_sets_smul_right
- \+ *lemma* seminorm_family.basis_sets_zero
- \+ *lemma* seminorm_family.to_locally_convex_space
- \+ *lemma* seminorm_family.with_seminorms_eq
- \+ *lemma* seminorm_family.with_seminorms_of_has_basis
- \+ *lemma* seminorm_family.with_seminorms_of_nhds
- \+ *abbreviation* seminorm_family
- \- *def* seminorm_module_filter_basis
- \- *lemma* with_seminorms.to_locally_convex_space
- \- *lemma* with_seminorms_eq
- \- *lemma* with_seminorms_of_has_basis
- \- *lemma* with_seminorms_of_nhds



## [2022-03-21 16:35:37](https://github.com/leanprover-community/mathlib/commit/a2e4802)
feat(model_theory/fraisse): Defines Fraïssé classes ([#12817](https://github.com/leanprover-community/mathlib/pull/12817))
Defines the age of a structure
(Mostly) characterizes the ages of countable structures
Defines Fraïssé classes
#### Estimated changes
Modified src/model_theory/basic.lean


Modified src/model_theory/finitely_generated.lean
- \+ *lemma* first_order.language.Structure.fg.cg
- \+ *theorem* first_order.language.substructure.cg.sup
- \- *theorem* first_order.language.substructure.cg_sup
- \+ *theorem* first_order.language.substructure.fg.sup
- \- *theorem* first_order.language.substructure.fg_sup

Added src/model_theory/fraisse.lean
- \+ *lemma* first_order.language.age.countable_quotient
- \+ *lemma* first_order.language.age.hereditary
- \+ *lemma* first_order.language.age.is_equiv_invariant
- \+ *lemma* first_order.language.age.joint_embedding
- \+ *def* first_order.language.age
- \+ *def* first_order.language.amalgamation
- \+ *def* first_order.language.hereditary
- \+ *def* first_order.language.joint_embedding



## [2022-03-21 16:35:35](https://github.com/leanprover-community/mathlib/commit/1b787d6)
feat(linear_algebra/span): generalize span_singleton_smul_eq ([#12736](https://github.com/leanprover-community/mathlib/pull/12736))
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/projective_space/basic.lean


Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.span_singleton_group_smul_eq
- \+/\- *lemma* submodule.span_singleton_smul_eq
- \+/\- *lemma* submodule.span_singleton_smul_le



## [2022-03-21 16:35:34](https://github.com/leanprover-community/mathlib/commit/df299a1)
docs(order/filter/basic): fix docstring of generate ([#12734](https://github.com/leanprover-community/mathlib/pull/12734))
#### Estimated changes
Modified src/order/filter/basic.lean




## [2022-03-21 16:35:33](https://github.com/leanprover-community/mathlib/commit/09750eb)
feat(measure_theory/function/uniform_integrable): add API for uniform integrability in the probability sense ([#12678](https://github.com/leanprover-community/mathlib/pull/12678))
Uniform integrability in probability theory is commonly defined as the uniform existence of a number for which the expectation of the random variables restricted on the set for which they are greater than said number is arbitrarily small. We have defined it 
in mathlib, on the other hand, as uniform integrability in the measure theory sense + existence of a uniform bound of the Lp norms. 
This PR proves the first definition implies the second while a later PR will deal with the reverse direction.
#### Estimated changes
Modified src/measure_theory/function/uniform_integrable.lean
- \+/\- *lemma* measure_theory.tendsto_Lp_of_tendsto_in_measure
- \+/\- *lemma* measure_theory.tendsto_in_measure_iff_tendsto_Lp
- \+/\- *lemma* measure_theory.unif_integrable_congr_ae
- \+ *lemma* measure_theory.unif_integrable_of'
- \+ *lemma* measure_theory.unif_integrable_of
- \+/\- *lemma* measure_theory.unif_integrable_of_tendsto_Lp
- \+ *lemma* measure_theory.unif_integrable_zero_meas
- \+ *lemma* measure_theory.uniform_integrable.ae_eq
- \+ *lemma* measure_theory.uniform_integrable_congr_ae
- \+ *lemma* measure_theory.uniform_integrable_const
- \+ *lemma* measure_theory.uniform_integrable_fintype
- \+ *lemma* measure_theory.uniform_integrable_of
- \+ *lemma* measure_theory.uniform_integrable_subsingleton
- \+ *lemma* measure_theory.uniform_integrable_zero_meas

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* indicator_meas_zero



## [2022-03-21 16:35:32](https://github.com/leanprover-community/mathlib/commit/715f984)
feat(model_theory/terms_and_formulas): Prenex Normal Form ([#12558](https://github.com/leanprover-community/mathlib/pull/12558))
Defines `first_order.language.bounded_formula.to_prenex`, a function which takes a formula and outputs an equivalent formula in prenex normal form.
Proves inductive principles based on the fact that every formula is equivalent to one in prenex normal form.
#### Estimated changes
Modified src/data/fin/tuple/basic.lean
- \+ *lemma* fin.snoc_comp_cast_succ

Modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* first_order.language.Theory.semantically_equivalent.refl
- \+ *lemma* first_order.language.Theory.semantically_equivalent.symm
- \+ *lemma* first_order.language.Theory.semantically_equivalent.trans
- \+ *lemma* first_order.language.bounded_formula.all_semantically_equivalent_not_ex_not
- \+ *lemma* first_order.language.bounded_formula.ex_semantically_equivalent_not_all_not
- \+ *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.induction_on_all_ex
- \+ *lemma* first_order.language.bounded_formula.induction_on_exists_not
- \+ *lemma* first_order.language.bounded_formula.is_atomic.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_atomic.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_prenex.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_prenex.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.is_prenex_to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.is_qf.cast_le
- \+ *lemma* first_order.language.bounded_formula.is_qf.lift_at
- \+ *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp
- \+ *lemma* first_order.language.bounded_formula.is_qf.to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.not_all_is_atomic
- \+ *lemma* first_order.language.bounded_formula.not_all_is_qf
- \+ *lemma* first_order.language.bounded_formula.not_ex_is_atomic
- \+ *lemma* first_order.language.bounded_formula.not_ex_is_qf
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_to_prenex
- \+ *def* first_order.language.bounded_formula.to_prenex
- \+ *def* first_order.language.bounded_formula.to_prenex_imp
- \+ *def* first_order.language.bounded_formula.to_prenex_imp_right
- \+ *lemma* first_order.language.bounded_formula.to_prenex_is_prenex
- \+ *lemma* first_order.language.formula.is_atomic_graph



## [2022-03-21 14:42:55](https://github.com/leanprover-community/mathlib/commit/091f27e)
chore(order/{complete_lattice,sup_indep}): move `complete_lattice.independent` ([#12588](https://github.com/leanprover-community/mathlib/pull/12588))
Putting this here means that in future we can talk about `pairwise_disjoint` at the same time, which was previously defined downstream of `complete_lattice.independent`.
This commit only moves existing declarations and adjusts module docstrings.
The new authorship comes from [#5971](https://github.com/leanprover-community/mathlib/pull/5971) and [#7199](https://github.com/leanprover-community/mathlib/pull/7199), which predate this file.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean


Modified src/order/compactly_generated.lean


Modified src/order/complete_lattice.lean
- \- *lemma* complete_lattice.independent.comp
- \- *lemma* complete_lattice.independent.disjoint
- \- *lemma* complete_lattice.independent.disjoint_bsupr
- \- *lemma* complete_lattice.independent.map_order_iso
- \- *lemma* complete_lattice.independent.mono
- \- *def* complete_lattice.independent
- \- *theorem* complete_lattice.independent_def''
- \- *theorem* complete_lattice.independent_def'
- \- *theorem* complete_lattice.independent_def
- \- *lemma* complete_lattice.independent_empty
- \- *lemma* complete_lattice.independent_map_order_iso_iff
- \- *lemma* complete_lattice.independent_pair
- \- *lemma* complete_lattice.independent_pempty
- \- *lemma* complete_lattice.set_independent.disjoint
- \- *lemma* complete_lattice.set_independent.disjoint_Sup
- \- *theorem* complete_lattice.set_independent.mono
- \- *def* complete_lattice.set_independent
- \- *lemma* complete_lattice.set_independent_empty
- \- *lemma* complete_lattice.set_independent_iff
- \- *lemma* complete_lattice.set_independent_pair

Modified src/order/sup_indep.lean
- \+ *lemma* complete_lattice.independent.comp
- \+ *lemma* complete_lattice.independent.disjoint
- \+ *lemma* complete_lattice.independent.disjoint_bsupr
- \+ *lemma* complete_lattice.independent.map_order_iso
- \+ *lemma* complete_lattice.independent.mono
- \+ *def* complete_lattice.independent
- \+ *theorem* complete_lattice.independent_def''
- \+ *theorem* complete_lattice.independent_def'
- \+ *theorem* complete_lattice.independent_def
- \+ *lemma* complete_lattice.independent_empty
- \+ *lemma* complete_lattice.independent_map_order_iso_iff
- \+ *lemma* complete_lattice.independent_pair
- \+ *lemma* complete_lattice.independent_pempty
- \+ *lemma* complete_lattice.set_independent.disjoint
- \+ *lemma* complete_lattice.set_independent.disjoint_Sup
- \+ *theorem* complete_lattice.set_independent.mono
- \+ *def* complete_lattice.set_independent
- \+ *lemma* complete_lattice.set_independent_empty
- \+ *lemma* complete_lattice.set_independent_iff
- \+ *lemma* complete_lattice.set_independent_pair



## [2022-03-21 12:46:46](https://github.com/leanprover-community/mathlib/commit/135c574)
feat(model_theory/definability): Definability lemmas ([#12262](https://github.com/leanprover-community/mathlib/pull/12262))
Proves several lemmas to work with definability over different parameter sets.
Shows that definability is closed under projection.
#### Estimated changes
Modified src/model_theory/definability.lean
- \+ *lemma* set.definable.image_comp
- \+ *lemma* set.definable.image_comp_embedding
- \+ *lemma* set.definable.image_comp_sum_inl_fin
- \+ *lemma* set.definable.map_expansion
- \+ *lemma* set.definable.mono
- \+ *lemma* set.definable_iff_empty_definable_with_params
- \+ *lemma* set.empty_definable_iff
- \+ *lemma* set.fin.coe_cast_add_zero

Modified src/model_theory/terms_and_formulas.lean
- \+/\- *def* first_order.language.Lhom.on_bounded_formula
- \+/\- *def* first_order.language.Lhom.on_formula
- \+/\- *def* first_order.language.Lhom.on_term



## [2022-03-21 11:08:42](https://github.com/leanprover-community/mathlib/commit/86055c5)
split(data/{finset,set}/pointwise): Split off `algebra.pointwise` ([#12831](https://github.com/leanprover-community/mathlib/pull/12831))
Split `algebra.pointwise` into
* `data.set.pointwise`: Pointwise operations on `set`
* `data.finset.pointwise`: Pointwise operations on `finset`
I'm crediting
* The same people for `data.set.pointwise`
* Floris for [#3541](https://github.com/leanprover-community/mathlib/pull/3541)
#### Estimated changes
Modified src/algebra/add_torsor.lean


Modified src/algebra/algebra/operations.lean


Modified src/algebra/bounds.lean


Modified src/algebra/module/pointwise_pi.lean


Modified src/algebra/order/module.lean


Modified src/algebra/star/pointwise.lean


Modified src/data/dfinsupp/interval.lean


Modified src/data/finset/finsupp.lean


Added src/data/finset/pointwise.lean
- \+ *lemma* finset.coe_mul
- \+ *lemma* finset.coe_one
- \+ *lemma* finset.coe_pow
- \+ *lemma* finset.empty_mul
- \+ *lemma* finset.image_mul_left'
- \+ *lemma* finset.image_mul_left
- \+ *lemma* finset.image_mul_prod
- \+ *lemma* finset.image_mul_right'
- \+ *lemma* finset.image_mul_right
- \+ *lemma* finset.image_one
- \+ *lemma* finset.mem_mul
- \+ *lemma* finset.mem_one
- \+ *lemma* finset.mul_card_le
- \+ *lemma* finset.mul_def
- \+ *lemma* finset.mul_empty
- \+ *lemma* finset.mul_mem_mul
- \+ *lemma* finset.mul_nonempty_iff
- \+ *lemma* finset.mul_singleton
- \+ *lemma* finset.mul_subset_mul
- \+ *lemma* finset.mul_zero_subset
- \+ *lemma* finset.nonempty.mul_zero
- \+ *lemma* finset.nonempty.zero_mul
- \+ *lemma* finset.one_mem_one
- \+ *lemma* finset.one_nonempty
- \+ *lemma* finset.one_subset
- \+ *lemma* finset.preimage_mul_left_one'
- \+ *lemma* finset.preimage_mul_left_one
- \+ *lemma* finset.preimage_mul_left_singleton
- \+ *lemma* finset.preimage_mul_right_one'
- \+ *lemma* finset.preimage_mul_right_one
- \+ *lemma* finset.preimage_mul_right_singleton
- \+ *lemma* finset.singleton_mul
- \+ *lemma* finset.singleton_mul_singleton
- \+ *lemma* finset.singleton_one
- \+ *lemma* finset.subset_mul
- \+ *lemma* finset.zero_mul_subset

Modified src/data/real/pointwise.lean


Modified src/data/set/intervals/image_preimage.lean


Renamed src/algebra/pointwise.lean to src/data/set/pointwise.lean
- \- *lemma* finset.coe_mul
- \- *lemma* finset.coe_one
- \- *lemma* finset.coe_pow
- \- *lemma* finset.empty_mul
- \- *lemma* finset.image_mul_left'
- \- *lemma* finset.image_mul_left
- \- *lemma* finset.image_mul_prod
- \- *lemma* finset.image_mul_right'
- \- *lemma* finset.image_mul_right
- \- *theorem* finset.image_one
- \- *lemma* finset.mem_mul
- \- *lemma* finset.mem_one
- \- *lemma* finset.mul_card_le
- \- *lemma* finset.mul_def
- \- *lemma* finset.mul_empty
- \- *lemma* finset.mul_mem_mul
- \- *lemma* finset.mul_nonempty_iff
- \- *lemma* finset.mul_singleton
- \- *lemma* finset.mul_subset_mul
- \- *lemma* finset.mul_zero_subset
- \- *lemma* finset.nonempty.mul_zero
- \- *lemma* finset.nonempty.zero_mul
- \- *lemma* finset.one_mem_one
- \- *theorem* finset.one_nonempty
- \- *theorem* finset.one_subset
- \- *lemma* finset.preimage_mul_left_one'
- \- *lemma* finset.preimage_mul_left_one
- \- *lemma* finset.preimage_mul_left_singleton
- \- *lemma* finset.preimage_mul_right_one'
- \- *lemma* finset.preimage_mul_right_one
- \- *lemma* finset.preimage_mul_right_singleton
- \- *lemma* finset.singleton_mul
- \- *lemma* finset.singleton_mul_singleton
- \- *lemma* finset.singleton_one
- \- *lemma* finset.singleton_zero_mul
- \- *lemma* finset.subset_mul
- \- *lemma* finset.zero_mul_subset

Modified src/group_theory/order_of_element.lean


Modified src/group_theory/submonoid/pointwise.lean


Modified src/order/filter/pointwise.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/subsemiring/pointwise.lean


Modified src/topology/algebra/monoid.lean




## [2022-03-21 09:13:23](https://github.com/leanprover-community/mathlib/commit/8161ba2)
feat(model_theory/ultraproducts): Ultraproducts and the Compactness Theorem ([#12531](https://github.com/leanprover-community/mathlib/pull/12531))
Defines `filter.product`, a dependent version of `filter.germ`.
Defines a structure on an ultraproduct (a `filter.product` with respect to an ultrafilter).
Proves Łoś's Theorem, characterizing when an ultraproduct realizes a formula.
Proves the Compactness theorem with ultraproducts.
#### Estimated changes
Modified docs/overview.yaml


Modified src/model_theory/quotients.lean


Modified src/model_theory/terms_and_formulas.lean
- \- *def* first_order.language.realize_sentence
- \+ *def* first_order.language.sentence.realize

Added src/model_theory/ultraproducts.lean
- \+ *theorem* first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable
- \+ *theorem* first_order.language.ultraproduct.bounded_formula_realize_cast
- \+ *lemma* first_order.language.ultraproduct.fun_map_cast
- \+ *theorem* first_order.language.ultraproduct.realize_formula_cast
- \+ *theorem* first_order.language.ultraproduct.sentence_realize
- \+ *lemma* first_order.language.ultraproduct.term_realize_cast

Modified src/order/filter/germ.lean
- \+ *def* filter.product
- \+ *def* filter.product_setoid



## [2022-03-21 07:40:25](https://github.com/leanprover-community/mathlib/commit/8e9abe3)
feat(measure_theory/constructions/borel_space): generalize a lemma ([#12843](https://github.com/leanprover-community/mathlib/pull/12843))
Generalize `measurable_limit_of_tendsto_metric_ae` from
`at_top : filter ℕ` to any countably generated filter on a nonempty type.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_limit_of_tendsto_metric_ae



## [2022-03-21 05:51:55](https://github.com/leanprover-community/mathlib/commit/d902c22)
chore(category/abelian/derived): shorten proof ([#12847](https://github.com/leanprover-community/mathlib/pull/12847))
#### Estimated changes
Modified src/category_theory/abelian/derived.lean




## [2022-03-21 05:51:54](https://github.com/leanprover-community/mathlib/commit/395019e)
feat(algebra/homology/additive): dualise statement of chain complex to cochain complex ([#12840](https://github.com/leanprover-community/mathlib/pull/12840))
#### Estimated changes
Modified src/algebra/homology/additive.lean
- \+ *def* cochain_complex.single₀_map_homological_complex
- \+ *lemma* cochain_complex.single₀_map_homological_complex_hom_app_succ
- \+ *lemma* cochain_complex.single₀_map_homological_complex_hom_app_zero
- \+ *lemma* cochain_complex.single₀_map_homological_complex_inv_app_succ
- \+ *lemma* cochain_complex.single₀_map_homological_complex_inv_app_zero



## [2022-03-21 05:51:53](https://github.com/leanprover-community/mathlib/commit/69d3d16)
feat(polynomial/derivative): tidy+new theorems ([#12833](https://github.com/leanprover-community/mathlib/pull/12833))
Adds `iterate_derivative_eq_zero` and strengthens other results.
New theorems: `iterate_derivative_eq_zero`, `nat_degree_derivative_le`
Deleted: `derivative_lhom` - it is one already.
Misc: Turn a docstring into a comment
Everything else only got moved around + golfed, in order to weaken assumptions.
#### Estimated changes
Modified src/data/polynomial/derivative.lean
- \- *def* polynomial.derivative_lhom
- \- *lemma* polynomial.derivative_lhom_coe
- \+/\- *lemma* polynomial.derivative_neg
- \+/\- *lemma* polynomial.derivative_sub
- \+ *lemma* polynomial.iterate_derivative_eq_zero
- \+/\- *lemma* polynomial.iterate_derivative_neg
- \+/\- *lemma* polynomial.iterate_derivative_sub
- \+ *theorem* polynomial.nat_degree_derivative_le
- \+/\- *theorem* polynomial.nat_degree_eq_zero_of_derivative_eq_zero

Modified src/ring_theory/polynomial/bernstein.lean




## [2022-03-21 05:51:52](https://github.com/leanprover-community/mathlib/commit/06017e0)
feat(order/compare): add 4 dot notation lemmas ([#12832](https://github.com/leanprover-community/mathlib/pull/12832))
#### Estimated changes
Modified src/order/compare.lean
- \+ *lemma* eq.cmp_eq_eq'
- \+ *lemma* eq.cmp_eq_eq
- \+ *lemma* has_lt.lt.cmp_eq_gt
- \+ *lemma* has_lt.lt.cmp_eq_lt



## [2022-03-21 05:51:51](https://github.com/leanprover-community/mathlib/commit/f5987b2)
chore(data/real/basic): tweak lemmas about `of_cauchy` ([#12829](https://github.com/leanprover-community/mathlib/pull/12829))
These lemmas are about `real.of_cauchy` not `real.cauchy`, as their name suggests.
This also flips the direction of some of the lemmas to be consistent with the zero and one lemmas.
Finally, this adds the lemmas about `real.cauchy` that are missing.
#### Estimated changes
Modified src/data/real/basic.lean
- \- *lemma* real.add_cauchy
- \+ *lemma* real.cauchy_add
- \+ *lemma* real.cauchy_inv
- \+ *lemma* real.cauchy_mul
- \+ *lemma* real.cauchy_neg
- \+ *lemma* real.cauchy_one
- \+ *lemma* real.cauchy_zero
- \- *lemma* real.inv_cauchy
- \+/\- *lemma* real.mk_add
- \+/\- *lemma* real.mk_mul
- \+/\- *lemma* real.mk_neg
- \+/\- *lemma* real.mk_one
- \+/\- *lemma* real.mk_zero
- \- *lemma* real.mul_cauchy
- \- *lemma* real.neg_cauchy
- \+ *lemma* real.of_cauchy_add
- \+ *lemma* real.of_cauchy_inv
- \+ *lemma* real.of_cauchy_mul
- \+ *lemma* real.of_cauchy_neg
- \+ *lemma* real.of_cauchy_one
- \+ *lemma* real.of_cauchy_zero
- \- *lemma* real.one_cauchy
- \- *lemma* real.zero_cauchy



## [2022-03-21 05:51:50](https://github.com/leanprover-community/mathlib/commit/772c776)
feat(ring_theory/algebraic): Added basic lemmas + golf ([#12820](https://github.com/leanprover-community/mathlib/pull/12820))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+/\- *lemma* is_algebraic_algebra_map
- \+/\- *lemma* is_algebraic_algebra_map_of_is_algebraic
- \+ *lemma* is_algebraic_nat
- \+ *lemma* is_algebraic_one
- \+ *lemma* is_algebraic_zero
- \+/\- *lemma* is_integral.is_algebraic
- \+ *lemma* is_transcendental_of_subsingleton



## [2022-03-21 05:20:44](https://github.com/leanprover-community/mathlib/commit/60af3bd)
feat(data/rat/denumerable): Make `mk_rat` into a simp lemma ([#12821](https://github.com/leanprover-community/mathlib/pull/12821))
#### Estimated changes
Modified src/data/rat/denumerable.lean
- \+/\- *lemma* cardinal.mk_rat



## [2022-03-20 20:14:43](https://github.com/leanprover-community/mathlib/commit/656f749)
feat(analysis/locally_convex): define von Neumann boundedness ([#12449](https://github.com/leanprover-community/mathlib/pull/12449))
Define the von Neumann boundedness and show elementary properties, including that it defines a bornology.
#### Estimated changes
Added src/analysis/locally_convex/bounded.lean
- \+ *lemma* bornology.is_bounded_iff_is_vonN_bounded
- \+ *lemma* bornology.is_vonN_bounded.of_topological_space_le
- \+ *lemma* bornology.is_vonN_bounded.subset
- \+ *lemma* bornology.is_vonN_bounded.union
- \+ *def* bornology.is_vonN_bounded
- \+ *lemma* bornology.is_vonN_bounded_covers
- \+ *lemma* bornology.is_vonN_bounded_empty
- \+ *lemma* bornology.is_vonN_bounded_iff
- \+ *lemma* bornology.is_vonN_bounded_singleton
- \+ *def* bornology.vonN_bornology

Modified src/topology/bornology/basic.lean
- \+ *lemma* bornology.is_bounded_of_bounded_iff
- \+ *lemma* bornology.is_cobounded_of_bounded_iff



## [2022-03-20 15:25:50](https://github.com/leanprover-community/mathlib/commit/9502db1)
refactor(group_theory/group_action/basic): Golf definition of action on cosets ([#12823](https://github.com/leanprover-community/mathlib/pull/12823))
This PR golfs the definition of the left-multiplication action on left cosets.
I deleted `mul_left_cosets` since it's the same as `•` and has no API.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \- *def* mul_action.mul_left_cosets



## [2022-03-20 12:26:39](https://github.com/leanprover-community/mathlib/commit/f2fa1cf)
feat(category_theory/abelian/*): add some missing lemmas ([#12839](https://github.com/leanprover-community/mathlib/pull/12839))
#### Estimated changes
Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.kernel.lift.inv

Modified src/category_theory/abelian/homology.lean
- \+ *lemma* homology.map_ι



## [2022-03-20 00:39:53](https://github.com/leanprover-community/mathlib/commit/cdd0572)
chore(ring_theory/algebraic): fix typo + golf ([#12834](https://github.com/leanprover-community/mathlib/pull/12834))
#### Estimated changes
Modified src/ring_theory/algebraic.lean




## [2022-03-19 23:35:59](https://github.com/leanprover-community/mathlib/commit/6abfb1d)
feat(analysis/normed_space/spectrum): Prove the Gelfand-Mazur theorem ([#12787](https://github.com/leanprover-community/mathlib/pull/12787))
**Gelfand-Mazur theorem** For a complex Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse is given by selecting the (unique) element of `spectrum ℂ a`.
- [x] depends on: [#12132](https://github.com/leanprover-community/mathlib/pull/12132)
#### Estimated changes
Modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* spectrum.algebra_map_eq_of_mem



## [2022-03-19 21:04:04](https://github.com/leanprover-community/mathlib/commit/cd012fb)
chore(ring_theory/ideal): use `ideal.mul_mem_left` instead of `submodule.smul_mem` ([#12830](https://github.com/leanprover-community/mathlib/pull/12830))
In one place this saves one rewrite.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/basic.lean




## [2022-03-19 19:33:01](https://github.com/leanprover-community/mathlib/commit/f120076)
feat(category_theory): (co)equalizers and (co)kernels when composing with monos/epis ([#12828](https://github.com/leanprover-community/mathlib/pull/12828))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.has_coequalizer_epi_comp
- \+ *lemma* category_theory.limits.has_equalizer_comp_mono
- \+ *def* category_theory.limits.is_coequalizer_epi_comp
- \+ *def* category_theory.limits.is_equalizer_comp_mono

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.is_cokernel_epi_comp
- \+ *def* category_theory.limits.is_kernel_comp_mono



## [2022-03-19 19:33:00](https://github.com/leanprover-community/mathlib/commit/49cd1cc)
refactor(analysis/seminorm): move topology induced by seminorms to its own file ([#12826](https://github.com/leanprover-community/mathlib/pull/12826))
Besides the copy and paste I removed the namespace `seminorm` from most parts (it is still there for the boundedness definitions and statements) and updated the module docstrings. No real code has changed.
#### Estimated changes
Added src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* normed_space.to_locally_convex_space'
- \+ *lemma* seminorm.const_is_bounded
- \+ *lemma* seminorm.cont_normed_space_to_with_seminorms
- \+ *lemma* seminorm.cont_with_seminorms_normed_space
- \+ *lemma* seminorm.continuous_from_bounded
- \+ *def* seminorm.is_bounded
- \+ *lemma* seminorm.is_bounded_const
- \+ *lemma* seminorm.is_bounded_sup
- \+ *def* seminorm_add_group_filter_basis
- \+ *def* seminorm_basis_zero
- \+ *lemma* seminorm_basis_zero_add
- \+ *lemma* seminorm_basis_zero_iff
- \+ *lemma* seminorm_basis_zero_intersect
- \+ *lemma* seminorm_basis_zero_mem
- \+ *lemma* seminorm_basis_zero_neg
- \+ *lemma* seminorm_basis_zero_nonempty
- \+ *lemma* seminorm_basis_zero_singleton_mem
- \+ *lemma* seminorm_basis_zero_smul
- \+ *lemma* seminorm_basis_zero_smul_left
- \+ *lemma* seminorm_basis_zero_smul_right
- \+ *lemma* seminorm_basis_zero_zero
- \+ *def* seminorm_module_filter_basis
- \+ *lemma* with_seminorms.to_locally_convex_space
- \+ *lemma* with_seminorms_eq
- \+ *lemma* with_seminorms_of_has_basis
- \+ *lemma* with_seminorms_of_nhds

Modified src/analysis/seminorm.lean
- \- *lemma* normed_space.to_locally_convex_space'
- \- *lemma* seminorm.const_is_bounded
- \- *lemma* seminorm.cont_normed_space_to_with_seminorms
- \- *lemma* seminorm.cont_with_seminorms_normed_space
- \- *lemma* seminorm.continuous_from_bounded
- \- *def* seminorm.is_bounded
- \- *lemma* seminorm.is_bounded_const
- \- *lemma* seminorm.is_bounded_sup
- \- *def* seminorm.seminorm_add_group_filter_basis
- \- *def* seminorm.seminorm_basis_zero
- \- *lemma* seminorm.seminorm_basis_zero_add
- \- *lemma* seminorm.seminorm_basis_zero_iff
- \- *lemma* seminorm.seminorm_basis_zero_intersect
- \- *lemma* seminorm.seminorm_basis_zero_mem
- \- *lemma* seminorm.seminorm_basis_zero_neg
- \- *lemma* seminorm.seminorm_basis_zero_nonempty
- \- *lemma* seminorm.seminorm_basis_zero_singleton_mem
- \- *lemma* seminorm.seminorm_basis_zero_smul
- \- *lemma* seminorm.seminorm_basis_zero_smul_left
- \- *lemma* seminorm.seminorm_basis_zero_smul_right
- \- *lemma* seminorm.seminorm_basis_zero_zero
- \- *def* seminorm.seminorm_module_filter_basis
- \- *lemma* seminorm.with_seminorms.to_locally_convex_space
- \- *lemma* seminorm.with_seminorms_eq
- \- *lemma* seminorm.with_seminorms_of_has_basis
- \- *lemma* seminorm.with_seminorms_of_nhds



## [2022-03-19 19:32:59](https://github.com/leanprover-community/mathlib/commit/2660d16)
feat(group_theory/group_action/basic): Right action of normalizer on left cosets ([#12822](https://github.com/leanprover-community/mathlib/pull/12822))
This PR adds the right action of the normalizer on left cosets.
#### Estimated changes
Modified src/group_theory/group_action/basic.lean
- \+ *lemma* mul_action.quotient'.smul_coe
- \+ *lemma* mul_action.quotient'.smul_mk



## [2022-03-19 17:43:23](https://github.com/leanprover-community/mathlib/commit/48eacc6)
chore(*): update to lean 3.42.0c ([#12818](https://github.com/leanprover-community/mathlib/pull/12818))
#### Estimated changes
Modified leanpkg.toml


Modified src/tactic/interactive.lean


Modified test/induction.lean
- \+ *def* less_than.lt_lte
- \- *lemma* less_than.lt_lte

Modified test/lint.lean
- \- *lemma* foo3

Modified test/lint_to_additive_doc.lean
- \+ *def* bar
- \- *lemma* bar
- \+ *def* baz
- \- *lemma* baz
- \+ *def* foo
- \- *lemma* foo
- \+ *def* no_to_additive
- \- *lemma* no_to_additive
- \+ *def* quux
- \- *lemma* quux

Modified test/local_cache.lean




## [2022-03-19 14:49:29](https://github.com/leanprover-community/mathlib/commit/42dcf35)
chore(algebra/char_p/exp_char): golf char_eq_exp_char_iff ([#12825](https://github.com/leanprover-community/mathlib/pull/12825))
#### Estimated changes
Modified src/algebra/char_p/exp_char.lean




## [2022-03-19 11:33:35](https://github.com/leanprover-community/mathlib/commit/3ba1c02)
feat(group_theory/subgroup/basic): Alternate version of `mem_normalizer_iff` ([#12814](https://github.com/leanprover-community/mathlib/pull/12814))
This PR adds an alternate version of `mem_normalizer_iff`, in terms of commuting rather than conjugation.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mem_normalizer_iff'



## [2022-03-19 11:33:34](https://github.com/leanprover-community/mathlib/commit/52b9b36)
feat(ring_theory/fractional_ideal): fractional ideal is one if and only if ideal is one ([#12813](https://github.com/leanprover-community/mathlib/pull/12813))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_ideal_eq_one_iff
- \+/\- *lemma* fractional_ideal.coe_ideal_eq_zero_iff
- \+/\- *lemma* fractional_ideal.coe_ideal_injective
- \+/\- *lemma* fractional_ideal.coe_ideal_ne_zero
- \+/\- *lemma* fractional_ideal.coe_ideal_ne_zero_iff



## [2022-03-19 11:33:33](https://github.com/leanprover-community/mathlib/commit/245b614)
chore(measure_theory/measure): move subtraction to a new file ([#12809](https://github.com/leanprover-community/mathlib/pull/12809))
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.measure.restrict_sub_eq_restrict_sub_restrict
- \- *lemma* measure_theory.measure.sub_add_cancel_of_le
- \- *lemma* measure_theory.measure.sub_apply
- \- *lemma* measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict
- \- *lemma* measure_theory.measure.sub_def
- \- *lemma* measure_theory.measure.sub_eq_zero_of_le
- \- *lemma* measure_theory.measure.sub_le

Added src/measure_theory/measure/sub.lean
- \+ *lemma* measure_theory.measure.restrict_sub_eq_restrict_sub_restrict
- \+ *lemma* measure_theory.measure.sub_add_cancel_of_le
- \+ *lemma* measure_theory.measure.sub_apply
- \+ *lemma* measure_theory.measure.sub_apply_eq_zero_of_restrict_le_restrict
- \+ *lemma* measure_theory.measure.sub_def
- \+ *lemma* measure_theory.measure.sub_eq_zero_of_le
- \+ *lemma* measure_theory.measure.sub_le



## [2022-03-19 11:33:32](https://github.com/leanprover-community/mathlib/commit/dae6155)
chore(number_theory/primorial): golf a proof ([#12807](https://github.com/leanprover-community/mathlib/pull/12807))
Use a new lemma to golf a proof.
#### Estimated changes
Modified src/number_theory/primorial.lean




## [2022-03-19 11:33:31](https://github.com/leanprover-community/mathlib/commit/1d18309)
feat(linear_algebra/determinant): no need for `is_domain` ([#12805](https://github.com/leanprover-community/mathlib/pull/12805))
Nontriviality is all that was actually used, and in some cases the statement is already vacuous in the trivial case.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+/\- *def* equiv_of_pi_lequiv_pi
- \+/\- *lemma* linear_equiv.det_mul_det_symm
- \+/\- *lemma* linear_equiv.det_symm_mul_det
- \+/\- *lemma* linear_equiv.is_unit_det'
- \+/\- *lemma* linear_map.is_unit_det
- \+/\- *lemma* matrix.det_comm'
- \+/\- *lemma* matrix.det_conj
- \+/\- *def* matrix.index_equiv_of_inv

Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/orientation.lean
- \+/\- *lemma* basis.map_orientation_eq_det_inv_smul

Modified src/ring_theory/norm.lean
- \+/\- *lemma* algebra.norm_eq_zero_iff_of_basis
- \+/\- *lemma* algebra.norm_ne_zero_iff_of_basis

Modified src/topology/algebra/module/basic.lean




## [2022-03-19 11:33:30](https://github.com/leanprover-community/mathlib/commit/ef69547)
feat(group_theory/finiteness): Define the minimum number of generators ([#12765](https://github.com/leanprover-community/mathlib/pull/12765))
The PR adds a definition of the minimum number of generators, which will be needed for a statement of Schreier's lemma.
#### Estimated changes
Modified src/group_theory/finiteness.lean
- \+ *lemma* group.fg_iff'
- \+ *def* group.rank
- \+ *lemma* group.rank_le
- \+ *lemma* group.rank_spec



## [2022-03-19 09:56:20](https://github.com/leanprover-community/mathlib/commit/ee4472b)
feat(group_theory/group_action/embedding): group actions apply on the codomain of embeddings ([#12798](https://github.com/leanprover-community/mathlib/pull/12798))
#### Estimated changes
Added src/group_theory/group_action/embedding.lean
- \+ *lemma* function.embedding.coe_smul
- \+ *lemma* function.embedding.smul_apply
- \+ *lemma* function.embedding.smul_def



## [2022-03-19 09:56:19](https://github.com/leanprover-community/mathlib/commit/c9fc9bf)
refactor(order/filter/pointwise): Cleanup ([#12789](https://github.com/leanprover-community/mathlib/pull/12789))
* Reduce typeclass assumptions from `monoid` to `has_mul`
* Turn lemmas into instances
* Use hom classes rather than concrete hom types
* Golf
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+/\- *lemma* set.image_mul
- \+/\- *lemma* set.preimage_mul_preimage_subset

Modified src/order/filter/pointwise.lean
- \+/\- *lemma* filter.comap_mul_comap_le
- \+/\- *def* filter.map_monoid_hom
- \+/\- *lemma* filter.mem_mul
- \+/\- *lemma* filter.mem_one
- \+/\- *lemma* filter.mul_mem_mul
- \+/\- *lemma* filter.ne_bot.mul
- \+ *lemma* filter.one_mem_one
- \+/\- *lemma* filter.tendsto.mul_mul

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean




## [2022-03-19 09:56:18](https://github.com/leanprover-community/mathlib/commit/2b6b9ff)
feat(category_theory/abelian/derived): add left_derived_zero_iso_self ([#12403](https://github.com/leanprover-community/mathlib/pull/12403))
We add `left_derived_zero_iso_self`: the natural isomorphism `(F.left_derived 0) ≅ F` if `preserves_finite_colimits F`.
From lean-liquid
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.preadditive.exact_of_iso_of_exact'

Added src/category_theory/abelian/derived.lean
- \+ *lemma* category_theory.abelian.functor.exact_of_map_projective_resolution
- \+ *def* category_theory.abelian.functor.left_derived_zero_iso_self
- \+ *def* category_theory.abelian.functor.left_derived_zero_to_self_app
- \+ *lemma* category_theory.abelian.functor.left_derived_zero_to_self_app_comp_inv
- \+ *def* category_theory.abelian.functor.left_derived_zero_to_self_app_inv
- \+ *lemma* category_theory.abelian.functor.left_derived_zero_to_self_app_inv_comp
- \+ *def* category_theory.abelian.functor.left_derived_zero_to_self_app_iso
- \+ *lemma* category_theory.abelian.functor.left_derived_zero_to_self_natural
- \+ *lemma* category_theory.abelian.functor.preserves_exact_of_preserves_finite_colimits_of_epi

Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.cokernel.desc.inv



## [2022-03-19 08:22:18](https://github.com/leanprover-community/mathlib/commit/4c60258)
chore(ring_theory/dedekind_domain/ideal): golf ([#12737](https://github.com/leanprover-community/mathlib/pull/12737))
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_to_equiv
- \+ *lemma* ring_equiv.to_equiv_eq_coe

Modified src/ring_theory/dedekind_domain/ideal.lean




## [2022-03-19 03:04:31](https://github.com/leanprover-community/mathlib/commit/128c096)
chore(scripts): update nolints.txt ([#12816](https://github.com/leanprover-community/mathlib/pull/12816))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-19 01:22:50](https://github.com/leanprover-community/mathlib/commit/7764c60)
feat(*/sort): sorting empty sets/singletons ([#12801](https://github.com/leanprover-community/mathlib/pull/12801))
#### Estimated changes
Modified src/data/finset/sort.lean
- \+ *theorem* finset.sort_empty
- \+ *theorem* finset.sort_singleton

Modified src/data/list/sort.lean
- \+ *theorem* list.merge_sort_nil
- \+ *theorem* list.merge_sort_singleton

Modified src/data/multiset/sort.lean
- \+ *theorem* multiset.sort_singleton
- \+ *theorem* multiset.sort_zero



## [2022-03-18 21:54:51](https://github.com/leanprover-community/mathlib/commit/d04fff9)
feat(topology/{order,separation}): several lemmas from an old branch ([#12794](https://github.com/leanprover-community/mathlib/pull/12794))
* add `mem_nhds_discrete`;
* replace the proof of `is_open_implies_is_open_iff` by `iff.rfl`;
* add lemmas about `separated`.
#### Estimated changes
Modified src/topology/order.lean
- \+ *lemma* mem_nhds_discrete

Modified src/topology/separation.lean
- \+ *lemma* separated.disjoint_closure_left
- \+ *lemma* separated.disjoint_closure_right
- \+ *lemma* separated.mono
- \+ *lemma* separated.preimage



## [2022-03-18 20:21:42](https://github.com/leanprover-community/mathlib/commit/7f1ba1a)
feat(algebra/char_p/two): add `simp` attribute to some lemmas involving characteristic two identities ([#12800](https://github.com/leanprover-community/mathlib/pull/12800))
I hope that these `simp` attributes will make working with `char_p R 2` smooth!
I felt clumsy with this section, so hopefully this is an improvement.
#### Estimated changes
Modified src/algebra/char_p/two.lean
- \+/\- *lemma* char_two.add_self_eq_zero
- \+ *lemma* char_two.bit0_apply_eq_zero
- \+/\- *lemma* char_two.bit0_eq_zero
- \+ *lemma* char_two.bit1_apply_eq_one
- \+/\- *lemma* char_two.bit1_eq_one
- \+/\- *lemma* char_two.neg_eq
- \+/\- *lemma* char_two.sub_eq_add



## [2022-03-18 20:21:41](https://github.com/leanprover-community/mathlib/commit/e282089)
feat(linear_algebra/sesquilinear_form): preliminary results for nondegeneracy ([#12269](https://github.com/leanprover-community/mathlib/pull/12269))
Several lemmas needed to define nondegenerate bilinear forms and show that the canonical pairing of the algebraic dual is nondegenerate.
Add domain restriction of bilinear maps in the second component and in both compenents.
Some type-class generalizations for symmetric, alternating, and reflexive sesquilinear forms.
#### Estimated changes
Modified src/algebra/quandle.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/bilinear_map.lean
- \+ *lemma* linear_map.congr_fun₂
- \+ *def* linear_map.dom_restrict₁₂
- \+ *lemma* linear_map.dom_restrict₁₂_apply
- \+ *def* linear_map.dom_restrict₂
- \+ *lemma* linear_map.dom_restrict₂_apply
- \+ *lemma* linear_map.ext_basis
- \+ *lemma* linear_map.flip_flip
- \+ *lemma* linear_map.sum_repr_mul_repr_mul

Modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* linear_pmap.mk_span_singleton_apply'

Modified src/linear_algebra/matrix/bilinear_form.lean


Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *def* linear_map.is_Ortho
- \+/\- *lemma* linear_map.is_Ortho_def
- \+ *lemma* linear_map.is_Ortho_flip
- \+ *lemma* linear_map.is_alt_iff_eq_neg_flip
- \+/\- *lemma* linear_map.is_ortho_def
- \+ *lemma* linear_map.is_ortho_flip
- \+ *lemma* linear_map.is_symm.dom_restrict_symm
- \+/\- *lemma* linear_map.is_symm.is_refl
- \+/\- *lemma* linear_map.is_symm.ortho_comm
- \+/\- *def* linear_map.is_symm
- \+ *lemma* linear_map.is_symm_iff_eq_flip



## [2022-03-18 20:21:40](https://github.com/leanprover-community/mathlib/commit/076490a)
feat(group_theory/nilpotent): the is_nilpotent_of_finite_tfae theorem ([#11835](https://github.com/leanprover-community/mathlib/pull/11835))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *theorem* is_nilpotent_of_finite_tfae



## [2022-03-18 20:21:38](https://github.com/leanprover-community/mathlib/commit/8c89ae6)
feat(ring_theory/unique_factorization_domain): some lemmas relating shapes of factorisations ([#9345](https://github.com/leanprover-community/mathlib/pull/9345))
Given elements `a`, `b` in a `unique_factorization_monoid`, if there is an order-preserving bijection between the sets of factors of `associates.mk a` and `associates.mk b` then the prime factorisations of `a` and `b` have the same shape.
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.is_atom_iff
- \+ *lemma* dvd_prime_pow

Modified src/algebra/squarefree.lean
- \+ *lemma* multiplicity.finite_prime_left

Added src/ring_theory/chain_of_divisors.lean
- \+ *lemma* divisor_chain.card_subset_divisors_le_length_of_chain
- \+ *lemma* divisor_chain.element_of_chain_eq_pow_second_of_chain
- \+ *lemma* divisor_chain.element_of_chain_not_is_unit_of_index_ne_zero
- \+ *lemma* divisor_chain.eq_pow_second_of_chain_of_has_chain
- \+ *lemma* divisor_chain.eq_second_of_chain_of_prime_dvd
- \+ *lemma* divisor_chain.exists_chain_of_prime_pow
- \+ *lemma* divisor_chain.first_of_chain_is_unit
- \+ *lemma* divisor_chain.is_prime_pow_of_has_chain
- \+ *lemma* divisor_chain.second_of_chain_is_irreducible
- \+ *lemma* multiplicity_prime_le_multiplicity_image_by_factor_order_iso
- \+ *lemma* pow_image_of_prime_by_factor_order_iso_dvd

Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* ideal.comap_le_comap_iff_of_surjective

Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.exists_associated_prime_pow_of_unique_normalized_factor
- \+ *theorem* unique_factorization_monoid.normalized_factors_of_irreducible_pow



## [2022-03-18 18:32:32](https://github.com/leanprover-community/mathlib/commit/0c52d3b)
doc(src/tactic/doc_commands): typo “between” → “better” ([#12804](https://github.com/leanprover-community/mathlib/pull/12804))
#### Estimated changes
Modified src/tactic/doc_commands.lean




## [2022-03-18 18:32:31](https://github.com/leanprover-community/mathlib/commit/d3703fe)
doc(archive/100-theorems-list/9_area_of_a_circle): fix `×` ([#12803](https://github.com/leanprover-community/mathlib/pull/12803))
this file used to have the category theory `\cross` as opposed to `\x`
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean




## [2022-03-18 18:32:30](https://github.com/leanprover-community/mathlib/commit/f4e7f82)
chore(model_theory/definability): Change variable order in definability ([#12802](https://github.com/leanprover-community/mathlib/pull/12802))
Changes `first_order.language.definable` and `first_order.language.definable_set` to `set.definable` and `set.definable_set`.
Makes `set.definable` a `def` rather than a `structure`.
#### Estimated changes
Modified docs/overview.yaml


Modified src/model_theory/definability.lean
- \- *lemma* first_order.language.definable.compl
- \- *lemma* first_order.language.definable.image_comp_equiv
- \- *lemma* first_order.language.definable.inter
- \- *lemma* first_order.language.definable.preimage_comp
- \- *lemma* first_order.language.definable.sdiff
- \- *lemma* first_order.language.definable.union
- \- *structure* first_order.language.definable
- \- *lemma* first_order.language.definable_empty
- \- *lemma* first_order.language.definable_finset_bInter
- \- *lemma* first_order.language.definable_finset_bUnion
- \- *lemma* first_order.language.definable_finset_inf
- \- *lemma* first_order.language.definable_finset_sup
- \+/\- *def* first_order.language.definable_set
- \- *lemma* first_order.language.definable_univ
- \- *def* first_order.language.definable₁
- \- *def* first_order.language.definable₂
- \+ *lemma* set.definable.compl
- \+ *lemma* set.definable.image_comp_equiv
- \+ *lemma* set.definable.inter
- \+ *lemma* set.definable.preimage_comp
- \+ *lemma* set.definable.sdiff
- \+ *lemma* set.definable.union
- \+ *def* set.definable
- \+ *lemma* set.definable_empty
- \+ *lemma* set.definable_finset_bInter
- \+ *lemma* set.definable_finset_bUnion
- \+ *lemma* set.definable_finset_inf
- \+ *lemma* set.definable_finset_sup
- \+ *lemma* set.definable_univ
- \+ *def* set.definable₁
- \+ *def* set.definable₂



## [2022-03-18 18:32:29](https://github.com/leanprover-community/mathlib/commit/f6e85fc)
feat(order/rel_iso): Add `subrel` instances ([#12758](https://github.com/leanprover-community/mathlib/pull/12758))
#### Estimated changes
Modified src/order/rel_iso.lean




## [2022-03-18 18:32:28](https://github.com/leanprover-community/mathlib/commit/fdd7e98)
feat(set_theory/*): Redefine `sup f` as `supr f` ([#12657](https://github.com/leanprover-community/mathlib/pull/12657))
#### Estimated changes
Modified src/data/W/cardinal.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/card_measurable_space.lean


Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.bdd_above_range
- \- *theorem* cardinal.nonempty_sup
- \+/\- *theorem* cardinal.sup_le
- \+ *theorem* cardinal.sup_le_iff

Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.Sup_eq_bsup
- \+ *theorem* ordinal.Sup_eq_sup
- \+ *theorem* ordinal.bdd_above_range
- \+/\- *theorem* ordinal.blsub_le
- \+ *theorem* ordinal.blsub_le_iff
- \+/\- *theorem* ordinal.bsup_le
- \+ *theorem* ordinal.bsup_le_iff
- \+/\- *theorem* ordinal.lsub_le
- \+ *theorem* ordinal.lsub_le_iff
- \- *theorem* ordinal.lt_sup_of_ne_sup
- \+ *theorem* ordinal.ne_sup_iff_lt_sup
- \+/\- *theorem* ordinal.nfp_le
- \+ *theorem* ordinal.nfp_le_iff
- \+/\- *theorem* ordinal.sup_le
- \+ *theorem* ordinal.sup_le_iff
- \- *theorem* ordinal.sup_nonempty

Modified src/set_theory/ordinal_topology.lean


Modified src/set_theory/principal.lean




## [2022-03-18 18:32:27](https://github.com/leanprover-community/mathlib/commit/290ad75)
feat(model_theory/terms_and_formulas): Atomic, Quantifier-Free, and Prenex Formulas ([#12557](https://github.com/leanprover-community/mathlib/pull/12557))
Provides a few induction principles for formulas
Defines atomic formulas with `first_order.language.bounded_formula.is_atomic`
Defines quantifier-free formulas with `first_order.language.bounded_formula.is_qf`
Defines `first_order.language.bounded_formula.is_prenex` indicating that a formula is in prenex normal form.
#### Estimated changes
Modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* first_order.language.bounded_formula.is_atomic.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_atomic.is_qf
- \+ *lemma* first_order.language.bounded_formula.is_atomic.relabel
- \+ *inductive* first_order.language.bounded_formula.is_atomic
- \+ *lemma* first_order.language.bounded_formula.is_prenex.induction_on_all_not
- \+ *lemma* first_order.language.bounded_formula.is_prenex.relabel
- \+ *inductive* first_order.language.bounded_formula.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_qf.induction_on_inf_not
- \+ *lemma* first_order.language.bounded_formula.is_qf.induction_on_sup_not
- \+ *lemma* first_order.language.bounded_formula.is_qf.is_prenex
- \+ *lemma* first_order.language.bounded_formula.is_qf.not
- \+ *lemma* first_order.language.bounded_formula.is_qf.relabel
- \+ *inductive* first_order.language.bounded_formula.is_qf
- \+ *lemma* first_order.language.bounded_formula.is_qf_bot



## [2022-03-18 18:32:25](https://github.com/leanprover-community/mathlib/commit/d17ecf9)
feat(category_theory/abelian) : injective resolutions of an object in a category with enough injectives ([#12545](https://github.com/leanprover-community/mathlib/pull/12545))
This pr dualises `src/category_theory/preadditive/projective_resolution.lean`. But since half of the file requires `abelian` assumption, I moved it to `src/category_theory/abelian/*`. The reason it needs `abelian` assumption is because I want class inference to deduce `exact f g` from `exact g.op f.op`.
#### Estimated changes
Modified src/category_theory/abelian/injective_resolution.lean
- \+ *def* category_theory.InjectiveResolution.of
- \+ *def* category_theory.InjectiveResolution.of_cocomplex
- \+ *lemma* category_theory.exact_f_d
- \+ *abbreviation* category_theory.injective_resolution.desc
- \+ *abbreviation* category_theory.injective_resolution.ι
- \+ *abbreviation* category_theory.injective_resolution
- \+ *def* category_theory.injective_resolutions



## [2022-03-18 16:51:05](https://github.com/leanprover-community/mathlib/commit/80b8d19)
feat(model_theory/terms_and_formulas): Language maps act on terms, formulas, sentences, and theories ([#12609](https://github.com/leanprover-community/mathlib/pull/12609))
Defines the action of language maps on terms, formulas, sentences, and theories
Shows that said action commutes with realization
#### Estimated changes
Modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* first_order.language.Lhom.mem_on_Theory
- \+ *def* first_order.language.Lhom.on_Theory
- \+ *lemma* first_order.language.Lhom.on_Theory_model
- \+ *def* first_order.language.Lhom.on_bounded_formula
- \+ *def* first_order.language.Lhom.on_formula
- \+ *def* first_order.language.Lhom.on_sentence
- \+ *def* first_order.language.Lhom.on_term
- \+ *lemma* first_order.language.Lhom.realize_on_bounded_formula
- \+ *lemma* first_order.language.Lhom.realize_on_formula
- \+ *lemma* first_order.language.Lhom.realize_on_sentence
- \+ *lemma* first_order.language.Lhom.realize_on_term



## [2022-03-18 16:51:04](https://github.com/leanprover-community/mathlib/commit/bf690dd)
feat(archive/100-theorems-list): add proof of thm 81 ([#7274](https://github.com/leanprover-community/mathlib/pull/7274))
#### Estimated changes
Added archive/100-theorems-list/81_sum_of_prime_reciprocals_diverges.lean
- \+ *lemma* card_le_mul_sum
- \+ *lemma* card_le_two_pow
- \+ *lemma* card_le_two_pow_mul_sqrt
- \+ *lemma* range_sdiff_eq_bUnion
- \+ *theorem* real.tendsto_sum_one_div_prime_at_top
- \+ *lemma* sum_lt_half_of_not_tendsto

Modified docs/100.yaml


Modified src/data/finset/card.lean
- \+ *lemma* finset.card_sdiff_add_card_eq_card



## [2022-03-18 15:25:55](https://github.com/leanprover-community/mathlib/commit/b49bc77)
feat(data/nat/prime): add two lemmas with nat.primes, mul and dvd ([#12780](https://github.com/leanprover-community/mathlib/pull/12780))
These lemmas are close to available lemmas, but I could not actually find them.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.prime.dvd_iff_eq
- \+ *lemma* nat.prime_mul_iff



## [2022-03-18 14:52:26](https://github.com/leanprover-community/mathlib/commit/5a547aa)
fix(ring_theory/power_series/basic): remove duplicate instance ([#12744](https://github.com/leanprover-community/mathlib/pull/12744))
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean




## [2022-03-18 14:52:25](https://github.com/leanprover-community/mathlib/commit/14ee5e0)
feat(number_theory/arithmetic_function): add eq of multiplicative functions ([#12689](https://github.com/leanprover-community/mathlib/pull/12689))
To show that two multiplicative functions are equal, it suffices to show
that they are equal on prime powers. This is a commonly used strategy
when two functions are known to be multiplicative (e.g., they're both
Dirichlet convolutions of simpler multiplicative functions).
This will be used in several ongoing commits to prove asymptotics for
squarefree numbers.
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.is_multiplicative.eq_iff_eq_on_prime_powers



## [2022-03-18 13:10:58](https://github.com/leanprover-community/mathlib/commit/ee8db20)
feat(measure_theory/group/action): add `null_measurable_set.smul` ([#12793](https://github.com/leanprover-community/mathlib/pull/12793))
Also add `null_measurable_set.preimage` and `ae_disjoint.preimage`.
#### Estimated changes
Modified src/measure_theory/group/action.lean
- \+ *lemma* measure_theory.null_measurable_set.smul

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_disjoint.preimage
- \+ *lemma* measure_theory.null_measurable_set.preimage



## [2022-03-18 13:10:57](https://github.com/leanprover-community/mathlib/commit/2541387)
refactor(data/list/big_operators): review API ([#12782](https://github.com/leanprover-community/mathlib/pull/12782))
* merge `prod_monoid` into `big_operators`;
* review typeclass assumptions in some lemmas;
* use `to_additive` in more lemmas.
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/graded_monoid.lean


Modified src/data/list/big_operators.lean
- \+ *lemma* list.eq_of_prod_take_eq
- \- *lemma* list.eq_of_sum_take_eq
- \+ *lemma* list.exists_le_of_prod_le'
- \- *lemma* list.exists_le_of_sum_le
- \+ *lemma* list.exists_lt_of_prod_lt'
- \- *lemma* list.exists_lt_of_sum_lt
- \+ *lemma* list.monotone_prod_take
- \- *lemma* list.monotone_sum_take
- \+/\- *lemma* list.one_le_prod_of_one_le
- \+ *lemma* list.pow_card_le_prod
- \+ *lemma* list.prod_commute
- \+/\- *lemma* list.prod_eq_one_iff
- \+ *lemma* list.prod_eq_pow_card
- \+ *lemma* list.prod_le_pow_card
- \+ *lemma* list.prod_le_prod'
- \+ *lemma* list.prod_lt_prod'
- \+ *lemma* list.prod_lt_prod_of_ne_nil
- \+ *theorem* list.prod_repeat
- \+/\- *lemma* list.sum_map_mul_left
- \+/\- *lemma* list.sum_map_mul_right

Deleted src/data/list/prod_monoid.lean
- \- *lemma* list.prod_commute
- \- *lemma* list.prod_eq_pow_card
- \- *lemma* list.prod_le_pow_card
- \- *theorem* list.prod_repeat



## [2022-03-18 13:10:56](https://github.com/leanprover-community/mathlib/commit/241d63d)
chore(algebraic_geometry/prime_spectrum/basic): remove TODO ([#12768](https://github.com/leanprover-community/mathlib/pull/12768))
Sober topological spaces has been defined and it has been proven (in this file) that prime spectrum is sober
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean




## [2022-03-18 12:36:36](https://github.com/leanprover-community/mathlib/commit/cfa7f6a)
feat(group_theory/index): Intersection of finite index subgroups ([#12776](https://github.com/leanprover-community/mathlib/pull/12776))
This PR proves that if `H` and `K` are of finite index in `L`, then so is `H ⊓ K`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.index_inf_ne_zero
- \+ *lemma* subgroup.relindex_inf_ne_zero



## [2022-03-18 10:11:28](https://github.com/leanprover-community/mathlib/commit/5ecd27a)
refactor(topology/algebra/field): make `topological_division_ring` extend `has_continuous_inv₀` ([#12778](https://github.com/leanprover-community/mathlib/pull/12778))
Topological division ring had been rolling its own `continuous_inv` field which was almost identical to the `continuous_at_inv₀` field of `has_continuous_inv₀`. Here we refactor so that `topological_division_ring` extends `has_continuous_inv₀` instead.
- [x] depends on: [#12770](https://github.com/leanprover-community/mathlib/pull/12770)
#### Estimated changes
Modified src/topology/algebra/field.lean


Modified src/topology/algebra/uniform_field.lean


Modified src/topology/algebra/valued_field.lean




## [2022-03-18 01:33:57](https://github.com/leanprover-community/mathlib/commit/a7cad67)
doc(overview): some additions to the Analysis section ([#12791](https://github.com/leanprover-community/mathlib/pull/12791))
#### Estimated changes
Modified docs/overview.yaml




## [2022-03-18 00:28:28](https://github.com/leanprover-community/mathlib/commit/a32d58b)
feat(analysis/*): generalize `set_smul_mem_nhds_zero` to topological vector spaces ([#12779](https://github.com/leanprover-community/mathlib/pull/12779))
The lemma holds for arbitrary topological vector spaces and has nothing to do with normed spaces.
#### Estimated changes
Modified src/analysis/normed_space/pointwise.lean
- \- *lemma* set_smul_mem_nhds_zero
- \- *lemma* set_smul_mem_nhds_zero_iff

Modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* set_smul_mem_nhds_smul
- \+ *lemma* set_smul_mem_nhds_smul_iff
- \+ *lemma* set_smul_mem_nhds_zero_iff



## [2022-03-18 00:28:27](https://github.com/leanprover-community/mathlib/commit/adcfc58)
chore(data/matrix/block): Do not print `matrix.from_blocks` with dot notation ([#12774](https://github.com/leanprover-community/mathlib/pull/12774))
`A.from_blocks B C D` is weird and asymmetric compared to `from_blocks A B C D`. In future we might want to introduce notation.
#### Estimated changes
Modified src/data/matrix/block.lean




## [2022-03-17 22:40:49](https://github.com/leanprover-community/mathlib/commit/cf8c5ff)
feat(algebra/pointwise): Subtraction/division of sets ([#12694](https://github.com/leanprover-community/mathlib/pull/12694))
Define pointwise subtraction/division on `set`.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.Inter_div_subset
- \+ *lemma* set.Inter₂_div_subset
- \+ *lemma* set.Union_div
- \+ *lemma* set.Union_div_left_image
- \+ *lemma* set.Union_div_right_image
- \+ *lemma* set.Union₂_div
- \+ *lemma* set.div_Inter_subset
- \+ *lemma* set.div_Inter₂_subset
- \+ *lemma* set.div_Union
- \+ *lemma* set.div_Union₂
- \+ *lemma* set.div_empty
- \+ *lemma* set.div_inter_subset
- \+ *lemma* set.div_mem_div
- \+ *lemma* set.div_singleton
- \+ *lemma* set.div_subset_div
- \+ *lemma* set.div_subset_div_left
- \+ *lemma* set.div_subset_div_right
- \+ *lemma* set.div_union
- \+ *lemma* set.empty_div
- \+ *lemma* set.image2_div
- \+ *lemma* set.image_div_prod
- \+ *lemma* set.inter_div_subset
- \+ *lemma* set.mem_div
- \+ *lemma* set.singleton_div
- \+ *lemma* set.singleton_div_singleton
- \+ *lemma* set.union_div



## [2022-03-17 22:40:48](https://github.com/leanprover-community/mathlib/commit/32e5b6b)
feat(model_theory/terms_and_formulas): Casting and lifting terms and formulas ([#12467](https://github.com/leanprover-community/mathlib/pull/12467))
Defines `bounded_formula.cast_le`, which maps the `fin`-indexed variables with `fin.cast_le`
Defines `term.lift_at` and `bounded_formula.lift_at`, which raise `fin`-indexed variables above a certain threshold
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.add_nat_one
- \+ *lemma* fin.cast_cast_succ
- \+ *lemma* fin.cast_last
- \+ *lemma* fin.cast_le_of_eq
- \+ *lemma* fin.cast_zero

Modified src/data/sum/basic.lean
- \+ *lemma* sum.elim_comp_map

Modified src/model_theory/terms_and_formulas.lean
- \+ *def* first_order.language.bounded_formula.cast_le
- \+ *def* first_order.language.bounded_formula.lift_at
- \+ *lemma* first_order.language.bounded_formula.realize_all_lift_at_one_self
- \+ *lemma* first_order.language.bounded_formula.realize_cast_le_of_eq
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at_one
- \+ *lemma* first_order.language.bounded_formula.realize_lift_at_one_self
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_all_lift_at
- \+ *def* first_order.language.term.lift_at
- \+ *lemma* first_order.language.term.realize_lift_at



## [2022-03-17 22:40:47](https://github.com/leanprover-community/mathlib/commit/a26dfc4)
feat(analysis/normed_space/basic): add `normed_division_ring` ([#12132](https://github.com/leanprover-community/mathlib/pull/12132))
This defines normed division rings and generalizes some of the lemmas that applied to normed fields instead to normed division rings.
This breaks one `ac_refl`; although this could be resolved by using `simp only {canonize_instances := tt}` first, it's easier to just tweak the proof.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/normed/normed_field.lean


Modified src/analysis/quaternion.lean
- \- *lemma* quaternion.norm_mul



## [2022-03-17 18:31:29](https://github.com/leanprover-community/mathlib/commit/2cb5edb)
chore(topology/algebra/group_with_zero): mark `has_continuous_inv₀` as a `Prop` ([#12770](https://github.com/leanprover-community/mathlib/pull/12770))
Since the type was not explicitly given, Lean marked this as a `Type`.
#### Estimated changes
Modified src/topology/algebra/group_with_zero.lean




## [2022-03-17 18:31:28](https://github.com/leanprover-community/mathlib/commit/3e6e34e)
feat(linear_algebra/matrix): The Weinstein–Aronszajn identity ([#12767](https://github.com/leanprover-community/mathlib/pull/12767))
Notably this includes the proof of the determinant of a block matrix, which we didn't seem to have in the general case.
This also renames some of the lemmas about determinants of block matrices, and adds some missing API for `inv_of` on matrices.
There's some discussion at https://math.stackexchange.com/q/4105846/1896 about whether this name is appropriate, and whether it should be called "Sylvester's determinant theorem" instead.
#### Estimated changes
Modified src/linear_algebra/matrix/block.lean


Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_from_blocks_zero₁₂
- \+ *lemma* matrix.det_from_blocks_zero₂₁
- \- *lemma* matrix.det_one_add_col_mul_row
- \- *lemma* matrix.lower_two_block_triangular_det
- \- *lemma* matrix.upper_two_block_triangular_det

Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.det_from_blocks_one₁₁
- \+ *lemma* matrix.det_from_blocks_one₂₂
- \+ *lemma* matrix.det_from_blocks₁₁
- \+ *lemma* matrix.det_from_blocks₂₂
- \+ *lemma* matrix.det_mul_add_one_comm
- \+ *lemma* matrix.det_one_add_col_mul_row
- \+ *lemma* matrix.det_one_add_mul_comm
- \+ *lemma* matrix.det_one_sub_mul_comm



## [2022-03-17 18:31:27](https://github.com/leanprover-community/mathlib/commit/6bfbb49)
docs(algebra/order/floor): Update floor_semiring docs to reflect it's just an ordered_semiring ([#12756](https://github.com/leanprover-community/mathlib/pull/12756))
The docs say that `floor_semiring` is a linear ordered semiring, but it is only an `ordered_semiring` in the code. Change the docs to reflect this fact.
#### Estimated changes
Modified src/algebra/order/floor.lean




## [2022-03-17 18:31:26](https://github.com/leanprover-community/mathlib/commit/ca80c8b)
feat(data/nat/sqrt_norm_num): norm_num extension for sqrt ([#12735](https://github.com/leanprover-community/mathlib/pull/12735))
Inspired by https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/2.20is.20not.20a.20square . The norm_num extension has to go in a separate file from `data.nat.sqrt` because `data.nat.sqrt` is a dependency of `norm_num`.
#### Estimated changes
Modified src/data/nat/prime.lean


Added src/data/nat/sqrt_norm_num.lean
- \+ *lemma* norm_num.is_sqrt

Modified test/norm_num_ext.lean




## [2022-03-17 18:31:25](https://github.com/leanprover-community/mathlib/commit/e944a99)
feat(algebraic_geometry/projective_spectrum) : lemmas about `vanishing_ideal` and `zero_locus` ([#12730](https://github.com/leanprover-community/mathlib/pull/12730))
This pr mimics the corresponding construction in `Spec`; other than `projective_spectrum.basic_open_eq_union_of_projection` everything else is a direct copy.
#### Estimated changes
Modified src/algebraic_geometry/projective_spectrum/topology.lean
- \+ *lemma* projective_spectrum.as_ideal_le_as_ideal
- \+ *lemma* projective_spectrum.as_ideal_lt_as_ideal
- \+ *def* projective_spectrum.basic_open
- \+ *lemma* projective_spectrum.basic_open_eq_union_of_projection
- \+ *lemma* projective_spectrum.basic_open_eq_zero_locus_compl
- \+ *lemma* projective_spectrum.basic_open_mul
- \+ *lemma* projective_spectrum.basic_open_mul_le_left
- \+ *lemma* projective_spectrum.basic_open_mul_le_right
- \+ *lemma* projective_spectrum.basic_open_one
- \+ *lemma* projective_spectrum.basic_open_pow
- \+ *lemma* projective_spectrum.basic_open_zero
- \+ *lemma* projective_spectrum.gc_homogeneous_ideal
- \+ *lemma* projective_spectrum.gc_ideal
- \+ *lemma* projective_spectrum.gc_set
- \+ *lemma* projective_spectrum.homogeneous_ideal_le_vanishing_ideal_zero_locus
- \+ *lemma* projective_spectrum.ideal_le_vanishing_ideal_zero_locus
- \+ *lemma* projective_spectrum.is_closed_iff_zero_locus
- \+ *lemma* projective_spectrum.is_closed_zero_locus
- \+ *lemma* projective_spectrum.is_open_basic_open
- \+ *lemma* projective_spectrum.is_open_iff
- \+ *lemma* projective_spectrum.is_topological_basis_basic_opens
- \+ *lemma* projective_spectrum.le_iff_mem_closure
- \+ *lemma* projective_spectrum.mem_basic_open
- \+ *lemma* projective_spectrum.mem_coe_basic_open
- \+ *lemma* projective_spectrum.mem_compl_zero_locus_iff_not_mem
- \+ *lemma* projective_spectrum.subset_vanishing_ideal_zero_locus
- \+ *lemma* projective_spectrum.subset_zero_locus_iff_subset_vanishing_ideal
- \+ *lemma* projective_spectrum.subset_zero_locus_vanishing_ideal
- \+ *lemma* projective_spectrum.sup_vanishing_ideal_le
- \+ *lemma* projective_spectrum.union_zero_locus
- \+ *lemma* projective_spectrum.vanishing_ideal_Union
- \+ *lemma* projective_spectrum.vanishing_ideal_anti_mono
- \+ *lemma* projective_spectrum.vanishing_ideal_closure
- \+ *lemma* projective_spectrum.vanishing_ideal_union
- \+ *lemma* projective_spectrum.vanishing_ideal_univ
- \+ *lemma* projective_spectrum.zero_locus_Union
- \+ *lemma* projective_spectrum.zero_locus_anti_mono
- \+ *lemma* projective_spectrum.zero_locus_anti_mono_homogeneous_ideal
- \+ *lemma* projective_spectrum.zero_locus_anti_mono_ideal
- \+ *lemma* projective_spectrum.zero_locus_bUnion
- \+ *lemma* projective_spectrum.zero_locus_bot
- \+ *lemma* projective_spectrum.zero_locus_empty
- \+ *lemma* projective_spectrum.zero_locus_empty_of_one_mem
- \+ *lemma* projective_spectrum.zero_locus_inf
- \+ *lemma* projective_spectrum.zero_locus_mul_homogeneous_ideal
- \+ *lemma* projective_spectrum.zero_locus_mul_ideal
- \+ *lemma* projective_spectrum.zero_locus_singleton_mul
- \+ *lemma* projective_spectrum.zero_locus_singleton_one
- \+ *lemma* projective_spectrum.zero_locus_singleton_pow
- \+ *lemma* projective_spectrum.zero_locus_singleton_zero
- \+ *lemma* projective_spectrum.zero_locus_sup_homogeneous_ideal
- \+ *lemma* projective_spectrum.zero_locus_sup_ideal
- \+ *lemma* projective_spectrum.zero_locus_supr_homogeneous_ideal
- \+ *lemma* projective_spectrum.zero_locus_supr_ideal
- \+ *lemma* projective_spectrum.zero_locus_union
- \+ *lemma* projective_spectrum.zero_locus_univ
- \+ *lemma* projective_spectrum.zero_locus_vanishing_ideal_eq_closure



## [2022-03-17 17:30:04](https://github.com/leanprover-community/mathlib/commit/a1bdadd)
chore(topology/metric_space/hausdorff_distance): move two lemmas ([#12771](https://github.com/leanprover-community/mathlib/pull/12771))
Remove the dependence of `topology/metric_space/hausdorff_distance` on `analysis.normed_space.basic`, by moving out two lemmas.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/riesz_lemma.lean
- \+ *lemma* metric.closed_ball_inf_dist_compl_subset_closure'
- \+ *lemma* metric.closed_ball_inf_dist_compl_subset_closure

Modified src/topology/metric_space/hausdorff_distance.lean
- \- *lemma* metric.closed_ball_inf_dist_compl_subset_closure'
- \- *lemma* metric.closed_ball_inf_dist_compl_subset_closure

Modified src/topology/metric_space/pi_nat.lean


Modified src/topology/metric_space/polish.lean




## [2022-03-17 11:06:31](https://github.com/leanprover-community/mathlib/commit/11b2f36)
feat(algebraic_topology/fundamental_groupoid): Fundamental groupoid of punit ([#12757](https://github.com/leanprover-community/mathlib/pull/12757))
Proves the equivalence of the fundamental groupoid of punit and punit
#### Estimated changes
Added src/algebraic_topology/fundamental_groupoid/punit.lean
- \+ *def* fundamental_groupoid.punit_equiv_discrete_punit



## [2022-03-17 11:06:30](https://github.com/leanprover-community/mathlib/commit/cd196a8)
feat(group_theory/order_of_element): 1 is finite order, as is g⁻¹ ([#12749](https://github.com/leanprover-community/mathlib/pull/12749))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_of_fin_order_inv
- \+ *lemma* is_of_fin_order_inv_iff
- \+ *lemma* is_of_fin_order_one



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
Modified src/analysis/ODE/picard_lindelof.lean


Modified src/topology/compact_open.lean
- \+/\- *def* continuous_map.coev
- \+ *lemma* continuous_map.continuous_coe'
- \- *lemma* continuous_map.continuous_ev
- \+ *lemma* continuous_map.continuous_eval'
- \+ *lemma* continuous_map.continuous_eval_const'
- \- *lemma* continuous_map.continuous_ev₁
- \- *def* continuous_map.ev

Modified src/topology/continuous_function/bounded.lean
- \+ *theorem* bounded_continuous_function.continuous_eval_const
- \- *theorem* bounded_continuous_function.continuous_evalx

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_map.continuous_eval_const
- \- *lemma* continuous_map.continuous_evalx

Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2022-03-17 11:06:28](https://github.com/leanprover-community/mathlib/commit/a6158f1)
feat(group_theory/subgroup/basic): One-sided closure induction lemmas ([#12725](https://github.com/leanprover-community/mathlib/pull/12725))
This PR adds one-sided closure induction lemmas, which I will need for Schreier's lemma.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.closure_induction_left
- \+ *lemma* subgroup.closure_induction_right

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.closure_induction_left
- \+ *lemma* submonoid.closure_induction_right



## [2022-03-17 11:06:27](https://github.com/leanprover-community/mathlib/commit/b1bf390)
feat(number_theory/function_field): the ring of integers of a function field is not a field ([#12705](https://github.com/leanprover-community/mathlib/pull/12705))
#### Estimated changes
Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.not_is_field

Modified src/number_theory/function_field.lean
- \+ *lemma* algebra_map_injective
- \+ *lemma* function_field.ring_of_integers.algebra_map_injective
- \+ *lemma* function_field.ring_of_integers.not_is_field



## [2022-03-17 10:35:37](https://github.com/leanprover-community/mathlib/commit/c3ecf00)
feat(group_theory/sylow): direct product of sylow groups if all normal ([#11778](https://github.com/leanprover-community/mathlib/pull/11778))
#### Estimated changes
Modified src/group_theory/noncomm_pi_coprod.lean


Modified src/group_theory/sylow.lean
- \+ *def* sylow.direct_product_of_normal



## [2022-03-17 09:56:23](https://github.com/leanprover-community/mathlib/commit/31391dc)
feat(model_theory/basic, elementary_maps): Uses `fun_like` approach for first-order maps ([#12755](https://github.com/leanprover-community/mathlib/pull/12755))
Introduces classes `hom_class`, `strong_hom_class` to describe classes of first-order maps.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+/\- *structure* first_order.language.embedding
- \+ *lemma* first_order.language.equiv.bijective
- \+/\- *lemma* first_order.language.equiv.coe_injective
- \+/\- *lemma* first_order.language.equiv.injective
- \+ *lemma* first_order.language.equiv.surjective
- \- *lemma* first_order.language.hom.coe_injective
- \+ *lemma* first_order.language.hom_class.map_constants
- \+ *def* first_order.language.hom_class.strong_hom_class_of_is_algebraic

Modified src/model_theory/elementary_maps.lean
- \+/\- *lemma* first_order.language.elementary_embedding.coe_injective



## [2022-03-17 08:18:32](https://github.com/leanprover-community/mathlib/commit/9d7a664)
feat(algebra/parity + *): generalize lemmas about parity ([#12761](https://github.com/leanprover-community/mathlib/pull/12761))
I moved more even/odd lemmas from nat/int to general semirings/rings.
Some files that explicitly used the nat/int namespace were changed along the way.
#### Estimated changes
Modified src/algebra/geom_sum.lean


Modified src/algebra/parity.lean
- \+ *lemma* add_monoid_hom.even
- \+ *lemma* even.add_even
- \- *theorem* even.add_even
- \+ *lemma* even.add_odd
- \- *theorem* even.add_odd
- \+ *lemma* even.mul_left
- \+ *lemma* even.mul_right
- \+ *lemma* even.pow_of_ne_zero
- \+ *lemma* even.sub_even
- \+ *theorem* even.sub_odd
- \+ *lemma* even_neg_two
- \+ *lemma* even_two
- \+ *lemma* even_two_mul
- \+ *lemma* even_zero
- \+ *lemma* odd.add_even
- \- *theorem* odd.add_even
- \+ *lemma* odd.add_odd
- \- *theorem* odd.add_odd
- \+ *lemma* odd.mul_odd
- \+ *lemma* odd.pow
- \+ *theorem* odd.sub_even
- \+ *lemma* odd.sub_odd
- \+ *lemma* odd_neg_one
- \+ *lemma* odd_one
- \+ *lemma* odd_two_mul_add_one
- \+ *lemma* ring_hom.odd

Modified src/analysis/convex/specific_functions.lean


Modified src/data/int/parity.lean
- \- *theorem* int.even.mul_left
- \- *theorem* int.even.mul_right
- \- *theorem* int.even.sub_even
- \- *theorem* int.even.sub_odd
- \- *theorem* int.even_bit0
- \- *theorem* int.even_zero
- \- *theorem* int.odd.mul
- \- *theorem* int.odd.sub_even
- \- *theorem* int.odd.sub_odd

Modified src/data/nat/parity.lean
- \- *theorem* nat.even.mul_left
- \- *theorem* nat.even.mul_right
- \- *theorem* nat.even_bit0
- \- *theorem* nat.even_zero
- \- *theorem* nat.odd.mul

Modified src/number_theory/cyclotomic/discriminant.lean




## [2022-03-17 07:17:48](https://github.com/leanprover-community/mathlib/commit/3ba25ea)
feat(topology/algebra/const_mul_action): add is_closed smul lemmas ([#12747](https://github.com/leanprover-community/mathlib/pull/12747))
#### Estimated changes
Modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* is_closed.smul_of_ne_zero
- \+ *lemma* is_closed.smul₀



## [2022-03-17 07:17:46](https://github.com/leanprover-community/mathlib/commit/87ab09c)
feat(category_theory/abelian/injective_resolution): homotopy between descents of morphism and two injective resolutions ([#12743](https://github.com/leanprover-community/mathlib/pull/12743))
This pr contains the following
* `category_theory.InjectiveResolution.desc_homotopy`: Any two descents of the same morphism are homotopic.
* `category_theory.InjectiveResolution.homotopy_equiv`: Any two injective resolutions of the same
  object are homotopically equivalent.
#### Estimated changes
Modified src/category_theory/abelian/injective_resolution.lean
- \+ *def* category_theory.InjectiveResolution.desc_comp_homotopy
- \+ *def* category_theory.InjectiveResolution.desc_homotopy
- \+ *def* category_theory.InjectiveResolution.desc_homotopy_zero
- \+ *def* category_theory.InjectiveResolution.desc_homotopy_zero_one
- \+ *def* category_theory.InjectiveResolution.desc_homotopy_zero_succ
- \+ *def* category_theory.InjectiveResolution.desc_homotopy_zero_zero
- \+ *def* category_theory.InjectiveResolution.desc_id_homotopy
- \+ *def* category_theory.InjectiveResolution.homotopy_equiv
- \+ *lemma* category_theory.InjectiveResolution.homotopy_equiv_hom_ι
- \+ *lemma* category_theory.InjectiveResolution.homotopy_equiv_inv_ι



## [2022-03-17 06:22:26](https://github.com/leanprover-community/mathlib/commit/7000efb)
refactor(analysis/specific_limits): split into two files ([#12759](https://github.com/leanprover-community/mathlib/pull/12759))
Split the 1200-line file `analysis.specific_limits` into two:
- `analysis.specific_limits.normed` imports `normed_space` and covers limits in normed rings/fields
- `analysis.specific_limits.basic` imports only topology, and is still a bit of a grab-bag, covering limits in metric spaces, ordered rings, `ennreal`, etc.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/box_integral/box/subbox_induction.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed/group/hom.lean


Modified src/analysis/normed_space/exponential.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/units.lean


Added src/analysis/specific_limits/basic.lean
- \+ *lemma* aux_has_sum_of_le_geometric
- \+ *lemma* cauchy_seq_of_edist_le_geometric
- \+ *lemma* cauchy_seq_of_edist_le_geometric_two
- \+ *lemma* cauchy_seq_of_le_geometric
- \+ *lemma* cauchy_seq_of_le_geometric_two
- \+ *lemma* dist_le_of_le_geometric_of_tendsto
- \+ *lemma* dist_le_of_le_geometric_of_tendsto₀
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto
- \+ *lemma* dist_le_of_le_geometric_two_of_tendsto₀
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_of_tendsto₀
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \+ *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \+ *theorem* ennreal.exists_pos_sum_of_encodable'
- \+ *theorem* ennreal.exists_pos_sum_of_encodable
- \+ *theorem* ennreal.exists_pos_tsum_mul_lt_of_encodable
- \+ *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* ennreal.tsum_geometric
- \+ *lemma* factorial_tendsto_at_top
- \+ *lemma* geom_le
- \+ *lemma* geom_lt
- \+ *lemma* has_sum_geometric_of_lt_1
- \+ *lemma* has_sum_geometric_two'
- \+ *lemma* has_sum_geometric_two
- \+ *lemma* le_geom
- \+ *lemma* lt_geom
- \+ *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \+ *theorem* nnreal.exists_pos_sum_of_encodable
- \+ *lemma* nnreal.has_sum_geometric
- \+ *lemma* nnreal.summable_geometric
- \+ *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *def* pos_sum_of_encodable
- \+ *lemma* set.countable.exists_pos_forall_sum_le
- \+ *lemma* set.countable.exists_pos_has_sum_le
- \+ *lemma* sum_geometric_two_le
- \+ *lemma* summable_geometric_of_lt_1
- \+ *lemma* summable_geometric_two'
- \+ *lemma* summable_geometric_two
- \+ *lemma* summable_geometric_two_encode
- \+ *lemma* summable_one_div_pow_of_le
- \+ *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \+ *lemma* tendsto_at_top_of_geom_le
- \+ *lemma* tendsto_const_div_at_top_nhds_0_nat
- \+ *lemma* tendsto_factorial_div_pow_self_at_top
- \+ *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* tendsto_nat_ceil_mul_div_at_top
- \+ *lemma* tendsto_nat_floor_mul_div_at_top
- \+ *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \+ *lemma* tendsto_pow_at_top_at_top_of_one_lt
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* tendsto_pow_at_top_nhds_within_0_of_lt_1
- \+ *lemma* tsum_geometric_inv_two
- \+ *lemma* tsum_geometric_inv_two_ge
- \+ *lemma* tsum_geometric_nnreal
- \+ *lemma* tsum_geometric_of_lt_1
- \+ *lemma* tsum_geometric_two'
- \+ *lemma* tsum_geometric_two
- \+ *lemma* uniformity_basis_dist_pow_of_lt_1

Renamed src/analysis/specific_limits.lean to src/analysis/specific_limits/normed.lean
- \- *lemma* aux_has_sum_of_le_geometric
- \- *lemma* cauchy_seq_of_edist_le_geometric
- \- *lemma* cauchy_seq_of_edist_le_geometric_two
- \- *lemma* cauchy_seq_of_le_geometric
- \- *lemma* cauchy_seq_of_le_geometric_two
- \- *lemma* dist_le_of_le_geometric_of_tendsto
- \- *lemma* dist_le_of_le_geometric_of_tendsto₀
- \- *lemma* dist_le_of_le_geometric_two_of_tendsto
- \- *lemma* dist_le_of_le_geometric_two_of_tendsto₀
- \- *lemma* edist_le_of_edist_le_geometric_of_tendsto
- \- *lemma* edist_le_of_edist_le_geometric_of_tendsto₀
- \- *lemma* edist_le_of_edist_le_geometric_two_of_tendsto
- \- *lemma* edist_le_of_edist_le_geometric_two_of_tendsto₀:
- \- *theorem* ennreal.exists_pos_sum_of_encodable'
- \- *theorem* ennreal.exists_pos_sum_of_encodable
- \- *theorem* ennreal.exists_pos_tsum_mul_lt_of_encodable
- \- *lemma* ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* ennreal.tsum_geometric
- \- *lemma* factorial_tendsto_at_top
- \- *lemma* geom_le
- \- *lemma* geom_lt
- \- *lemma* has_sum_geometric_of_lt_1
- \- *lemma* has_sum_geometric_two'
- \- *lemma* has_sum_geometric_two
- \- *lemma* le_geom
- \- *lemma* lt_geom
- \- *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \- *theorem* nnreal.exists_pos_sum_of_encodable
- \- *lemma* nnreal.has_sum_geometric
- \- *lemma* nnreal.summable_geometric
- \- *lemma* nnreal.tendsto_const_div_at_top_nhds_0_nat
- \- *lemma* nnreal.tendsto_inverse_at_top_nhds_0_nat
- \- *lemma* nnreal.tendsto_pow_at_top_nhds_0_of_lt_1
- \- *def* pos_sum_of_encodable
- \- *lemma* set.countable.exists_pos_forall_sum_le
- \- *lemma* set.countable.exists_pos_has_sum_le
- \- *lemma* sum_geometric_two_le
- \- *lemma* summable_geometric_of_lt_1
- \- *lemma* summable_geometric_two'
- \- *lemma* summable_geometric_two
- \- *lemma* summable_geometric_two_encode
- \- *lemma* summable_one_div_pow_of_le
- \- *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \- *lemma* tendsto_at_top_of_geom_le
- \- *lemma* tendsto_const_div_at_top_nhds_0_nat
- \- *lemma* tendsto_factorial_div_pow_self_at_top
- \- *lemma* tendsto_inverse_at_top_nhds_0_nat
- \- *lemma* tendsto_nat_ceil_mul_div_at_top
- \- *lemma* tendsto_nat_floor_mul_div_at_top
- \- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \- *lemma* tendsto_pow_at_top_at_top_of_one_lt
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* tendsto_pow_at_top_nhds_within_0_of_lt_1
- \- *lemma* tsum_geometric_inv_two
- \- *lemma* tsum_geometric_inv_two_ge
- \- *lemma* tsum_geometric_nnreal
- \- *lemma* tsum_geometric_of_lt_1
- \- *lemma* tsum_geometric_two'
- \- *lemma* tsum_geometric_two
- \- *lemma* uniformity_basis_dist_pow_of_lt_1

Modified src/data/real/cardinality.lean


Modified src/data/real/hyperreal.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/number_theory/padics/hensel.lean


Modified src/topology/instances/rat_lemmas.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/hausdorff_distance.lean




## [2022-03-17 05:18:53](https://github.com/leanprover-community/mathlib/commit/877f2e7)
refactor(linear_algebra/ray): redefine `same_ray` to allow zero vectors ([#12618](https://github.com/leanprover-community/mathlib/pull/12618))
In a strictly convex space, the new definition is equivalent to the fact that the triangle inequality becomes an equality. The old definition was only used for nonzero vectors in `mathlib`. Also make the definition of `ray_vector` semireducible so that `ray_vector.setoid` can be an instance.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* mem_segment_iff_same_ray
- \+ *lemma* same_ray_of_mem_segment
- \+/\- *lemma* segment_same

Added src/analysis/normed_space/ray.lean
- \+ *lemma* same_ray.norm_add
- \+ *lemma* same_ray.norm_smul_eq
- \+ *lemma* same_ray.norm_sub
- \+ *lemma* same_ray_iff_inv_norm_smul_eq
- \+ *lemma* same_ray_iff_inv_norm_smul_eq_of_ne
- \+ *lemma* same_ray_iff_norm_smul_eq

Modified src/linear_algebra/orientation.lean
- \+/\- *lemma* basis.map_orientation_eq_det_inv_smul
- \+/\- *def* orientation.map
- \+/\- *lemma* orientation.map_apply
- \+/\- *lemma* orientation.map_refl
- \+/\- *lemma* orientation.map_symm
- \+/\- *abbreviation* orientation

Modified src/linear_algebra/ray.lean
- \+ *lemma* eq_zero_of_same_ray_neg_smul_right
- \+/\- *lemma* eq_zero_of_same_ray_self_neg
- \+/\- *lemma* equiv_iff_same_ray
- \- *lemma* equivalence_same_ray
- \+/\- *lemma* module.ray.ind
- \+/\- *def* module.ray.map
- \+/\- *lemma* module.ray.map_apply
- \+/\- *lemma* module.ray.map_refl
- \+/\- *lemma* module.ray.map_symm
- \+/\- *lemma* module.ray.ne_neg_self
- \+ *lemma* module.ray.neg_units_smul
- \+/\- *def* module.ray.some_ray_vector
- \+/\- *lemma* module.ray.some_ray_vector_ray
- \+/\- *def* module.ray.some_vector
- \+/\- *lemma* module.ray.some_vector_ne_zero
- \+/\- *lemma* module.ray.some_vector_ray
- \+/\- *lemma* module.ray.units_smul_of_neg
- \+/\- *lemma* module.ray.units_smul_of_pos
- \+/\- *def* module.ray
- \+ *lemma* neg_ray_of_ne_zero
- \+/\- *lemma* ray_eq_iff
- \- *lemma* ray_neg
- \+/\- *lemma* ray_pos_smul
- \+/\- *lemma* ray_vector.coe_neg
- \+/\- *lemma* ray_vector.equiv_neg_iff
- \+/\- *def* ray_vector.map_linear_equiv
- \- *def* ray_vector.same_ray_setoid
- \+/\- *def* ray_vector
- \+ *lemma* same_ray.add_left
- \+ *lemma* same_ray.add_right
- \+ *lemma* same_ray.exists_eq_smul
- \+ *lemma* same_ray.exists_eq_smul_add
- \+ *lemma* same_ray.exists_left_eq_smul
- \+ *lemma* same_ray.exists_pos
- \+ *lemma* same_ray.exists_right_eq_smul
- \+/\- *lemma* same_ray.map
- \- *lemma* same_ray.neg
- \+ *lemma* same_ray.nonneg_smul_left
- \+ *lemma* same_ray.nonneg_smul_right
- \+ *lemma* same_ray.of_subsingleton'
- \+ *lemma* same_ray.of_subsingleton
- \+/\- *lemma* same_ray.pos_smul_left
- \+/\- *lemma* same_ray.pos_smul_right
- \+/\- *lemma* same_ray.refl
- \+/\- *lemma* same_ray.smul
- \+/\- *lemma* same_ray.symm
- \+/\- *lemma* same_ray.trans
- \+ *lemma* same_ray.zero_left
- \+ *lemma* same_ray.zero_right
- \+/\- *lemma* same_ray_comm
- \- *lemma* same_ray_iff_mem_orbit
- \+/\- *lemma* same_ray_map_iff
- \+/\- *lemma* same_ray_neg_iff
- \+/\- *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* same_ray_neg_smul_left_iff_of_ne
- \+/\- *lemma* same_ray_neg_smul_right_iff
- \+ *lemma* same_ray_neg_smul_right_iff_of_ne
- \+/\- *lemma* same_ray_neg_swap
- \+ *lemma* same_ray_nonneg_smul_left
- \+ *lemma* same_ray_nonneg_smul_right
- \+/\- *lemma* same_ray_pos_smul_left
- \+/\- *lemma* same_ray_pos_smul_right
- \- *def* same_ray_setoid
- \- *lemma* same_ray_setoid_eq_orbit_rel
- \+/\- *lemma* same_ray_smul_left_iff
- \+ *lemma* same_ray_smul_left_iff_of_ne
- \+/\- *lemma* same_ray_smul_right_iff
- \+ *lemma* same_ray_smul_right_iff_of_ne



## [2022-03-17 04:20:16](https://github.com/leanprover-community/mathlib/commit/e547058)
docs(algebraic_topology/fundamental_groupoid/induced_maps): fix diagram rendering ([#12745](https://github.com/leanprover-community/mathlib/pull/12745))
#### Estimated changes
Modified src/algebraic_topology/fundamental_groupoid/induced_maps.lean




## [2022-03-17 03:03:56](https://github.com/leanprover-community/mathlib/commit/d1e1304)
feat(combinatorics/simple_graph/connectivity): API for get_vert ([#12604](https://github.com/leanprover-community/mathlib/pull/12604))
From my Formalising Mathematics 2022 course.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.walk.adj_get_vert_succ
- \+ *lemma* simple_graph.walk.get_vert_length
- \+ *lemma* simple_graph.walk.get_vert_of_length_le
- \+ *lemma* simple_graph.walk.get_vert_zero



## [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/192819b)
feat(category_theory/punit): A groupoid is equivalent to punit iff it has a unique arrow between any two objects ([#12726](https://github.com/leanprover-community/mathlib/pull/12726))
In terms of topology, when this is used with the fundamental groupoid, it means that a space is simply connected (we still need to define this) if and only if any two paths between the same points are homotopic, and contractible spaces are simply connected.
#### Estimated changes
Modified src/category_theory/groupoid.lean
- \+ *def* category_theory.groupoid.of_hom_unique

Modified src/category_theory/punit.lean
- \+ *theorem* category_theory.equiv_punit_iff_unique



## [2022-03-17 01:38:15](https://github.com/leanprover-community/mathlib/commit/3a0532a)
feat(topology/homotopy/fundamental_group): prove fundamental group is independent of basepoint in path-connected spaces ([#12234](https://github.com/leanprover-community/mathlib/pull/12234))
Adds definition of fundamental group and proves fundamental group independent of basepoint choice in path-connected spaces.
#### Estimated changes
Added src/algebraic_topology/fundamental_groupoid/fundamental_group.lean
- \+ *def* fundamental_group.fundamental_group_mul_equiv_of_path
- \+ *def* fundamental_group.fundamental_group_mul_equiv_of_path_connected
- \+ *def* fundamental_group

Modified src/category_theory/endomorphism.lean
- \+ *lemma* category_theory.Aut.Aut_mul_def
- \+ *def* category_theory.Aut.Aut_mul_equiv_of_iso



## [2022-03-16 23:51:43](https://github.com/leanprover-community/mathlib/commit/4d350b9)
chore(*): move code, golf ([#12753](https://github.com/leanprover-community/mathlib/pull/12753))
* move `pow_pos` and `pow_nonneg` to `algebra.order.ring`;
* use the former to golf `has_pos pnat nat`;
* fix formatting.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \- *theorem* pow_nonneg
- \- *theorem* pow_pos

Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/ring.lean
- \+ *theorem* pow_nonneg
- \+ *theorem* pow_pos

Modified src/data/pnat/basic.lean




## [2022-03-16 21:17:30](https://github.com/leanprover-community/mathlib/commit/b3abae5)
chore(category_theory/preadditive/projective_resolution): some minor golf ([#12739](https://github.com/leanprover-community/mathlib/pull/12739))
#### Estimated changes
Modified src/category_theory/preadditive/projective_resolution.lean




## [2022-03-16 21:17:29](https://github.com/leanprover-community/mathlib/commit/b24372f)
feat(model_theory/basic, terms_and_formulas): Helper functions for constant symbols ([#12722](https://github.com/leanprover-community/mathlib/pull/12722))
Defines a function `language.con` from `A` to constants of the language `L[[A]]`.
Changes the coercion of a constant to a term to a function `language.constants.term`.
Proves `simp` lemmas for interpretation of constant symbols and realization of constant terms.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.coe_con

Modified src/model_theory/terms_and_formulas.lean
- \+ *def* first_order.language.constants.term
- \+ *lemma* first_order.language.term.realize_con
- \+ *lemma* first_order.language.term.realize_constants



## [2022-03-16 21:17:26](https://github.com/leanprover-community/mathlib/commit/3b91c32)
feat(group_theory/subgroup/basic): `map_le_map_iff_of_injective` for `subtype` ([#12713](https://github.com/leanprover-community/mathlib/pull/12713))
This PR adds the special case of `map_le_map_iff_of_injective` when the group homomorphism is `subtype`. This is useful when working with nested subgroups.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.map_subtype_le_map_subtype



## [2022-03-16 19:40:36](https://github.com/leanprover-community/mathlib/commit/c459d2b)
feat(algebra/algebra/basic,data/matrix/basic): resolve a TODO about `alg_hom.map_smul_of_tower` ([#12684](https://github.com/leanprover-community/mathlib/pull/12684))
It turns out that this lemma doesn't actually help in the place I claimed it would, so I added the lemma that does help too.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom.map_smul_of_tower

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.map_op_smul'
- \+ *lemma* matrix.map_smul'

Modified src/linear_algebra/matrix/adjugate.lean




## [2022-03-16 19:40:35](https://github.com/leanprover-community/mathlib/commit/6a71007)
feat(group_theory/quotient_group) finiteness of groups for sequences of homomorphisms ([#12660](https://github.com/leanprover-community/mathlib/pull/12660))
#### Estimated changes
Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.inclusion_injective



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
Modified src/topology/algebra/order/basic.lean




## [2022-03-16 15:39:29](https://github.com/leanprover-community/mathlib/commit/693a3ac)
feat(number_theory/cyclotomic/basic): add is_primitive_root.adjoin ([#12716](https://github.com/leanprover-community/mathlib/pull/12716))
We add `is_cyclotomic_extension.is_primitive_root.adjoin`.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* is_primitive_root.adjoin_is_cyclotomic_extension

Modified src/number_theory/cyclotomic/primitive_roots.lean




## [2022-03-16 13:40:39](https://github.com/leanprover-community/mathlib/commit/b8faf13)
feat(data/finset/basic): add finset.filter_eq_self ([#12717](https://github.com/leanprover-community/mathlib/pull/12717))
and an epsilon of cleanup
from flt-regular
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.filter_eq_empty_iff
- \+ *lemma* finset.filter_eq_self
- \+/\- *lemma* finset.monotone_filter_left



## [2022-03-16 13:40:38](https://github.com/leanprover-community/mathlib/commit/d495afd)
feat(category_theory/abelian/injective_resolution): descents of a morphism ([#12703](https://github.com/leanprover-community/mathlib/pull/12703))
This pr dualise `src/category_theory/preadditive/projective_resolution.lean`. The reason that it is moved to `abelian` folder is because we want `exact f g` from `exact g.op f.op` instance.
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the following:
Given `I : InjectiveResolution X` and  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a chain map `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwine the descent and the original morphism, see `category_theory.InjectiveResolution.desc_commutes`.
(Docstring contains more than what is currently in the file, but everything else will come soon)
#### Estimated changes
Added src/category_theory/abelian/injective_resolution.lean
- \+ *def* category_theory.InjectiveResolution.desc
- \+ *lemma* category_theory.InjectiveResolution.desc_commutes
- \+ *def* category_theory.InjectiveResolution.desc_f_one
- \+ *lemma* category_theory.InjectiveResolution.desc_f_one_zero_comm
- \+ *def* category_theory.InjectiveResolution.desc_f_succ
- \+ *def* category_theory.InjectiveResolution.desc_f_zero



## [2022-03-16 13:40:36](https://github.com/leanprover-community/mathlib/commit/f21a760)
feat(measure_theory/function/jacobian): change of variable formula in integrals in higher dimension ([#12492](https://github.com/leanprover-community/mathlib/pull/12492))
Let `μ` be a Lebesgue measure on a finite-dimensional real vector space, `s` a measurable set, and `f` a function which is differentiable and injective on `s`. Then `∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ`. (There is also a version for the Lebesgue integral, i.e., for `ennreal`-valued functions).
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* continuous_linear_map.coe_to_continuous_linear_equiv_of_det_ne_zero
- \+ *def* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero
- \+ *lemma* continuous_linear_map.to_continuous_linear_equiv_of_det_ne_zero_apply

Added src/measure_theory/function/jacobian.lean
- \+ *lemma* approximates_linear_on.norm_fderiv_sub_le
- \+ *lemma* exists_closed_cover_approximates_linear_on_of_has_fderiv_within_at
- \+ *lemma* exists_partition_approximates_linear_on_of_has_fderiv_within_at
- \+ *lemma* measure_theory.add_haar_image_eq_zero_of_det_fderiv_within_eq_zero
- \+ *lemma* measure_theory.add_haar_image_eq_zero_of_det_fderiv_within_eq_zero_aux
- \+ *lemma* measure_theory.add_haar_image_eq_zero_of_differentiable_on_of_add_haar_eq_zero
- \+ *lemma* measure_theory.add_haar_image_le_lintegral_abs_det_fderiv
- \+ *lemma* measure_theory.add_haar_image_le_lintegral_abs_det_fderiv_aux1
- \+ *lemma* measure_theory.add_haar_image_le_lintegral_abs_det_fderiv_aux2
- \+ *lemma* measure_theory.add_haar_image_le_mul_of_det_lt
- \+ *lemma* measure_theory.ae_measurable_fderiv_within
- \+ *lemma* measure_theory.ae_measurable_of_real_abs_det_fderiv_within
- \+ *lemma* measure_theory.ae_measurable_to_nnreal_abs_det_fderiv_within
- \+ *theorem* measure_theory.integrable_on_image_iff_integrable_on_abs_det_fderiv_smul
- \+ *theorem* measure_theory.integral_image_eq_integral_abs_det_fderiv_smul
- \+ *theorem* measure_theory.lintegral_abs_det_fderiv_eq_add_haar_image
- \+ *lemma* measure_theory.lintegral_abs_det_fderiv_le_add_haar_image
- \+ *lemma* measure_theory.lintegral_abs_det_fderiv_le_add_haar_image_aux1
- \+ *lemma* measure_theory.lintegral_abs_det_fderiv_le_add_haar_image_aux2
- \+ *theorem* measure_theory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
- \+ *theorem* measure_theory.map_with_density_abs_det_fderiv_eq_add_haar
- \+ *lemma* measure_theory.measurable_embedding_of_fderiv_within
- \+ *lemma* measure_theory.measurable_image_of_fderiv_within
- \+ *lemma* measure_theory.mul_le_add_haar_image_of_lt_det
- \+ *theorem* measure_theory.restrict_map_with_density_abs_det_fderiv_eq_add_haar

Modified src/topology/algebra/module/basic.lean
- \+ *lemma* continuous_linear_equiv.det_coe_symm



## [2022-03-16 11:53:36](https://github.com/leanprover-community/mathlib/commit/0964573)
feat(set_theory/cardinal): Lift `min` and `max` ([#12518](https://github.com/leanprover-community/mathlib/pull/12518))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.lift_max'
- \+ *theorem* cardinal.lift_min'



## [2022-03-16 11:53:35](https://github.com/leanprover-community/mathlib/commit/717b11e)
feat(group_theory/noncomm_pi_coprod): homomorphism from pi monoids or groups ([#11744](https://github.com/leanprover-community/mathlib/pull/11744))
#### Estimated changes
Added src/group_theory/noncomm_pi_coprod.lean
- \+ *lemma* monoid_hom.independent_range_of_coprime_order
- \+ *lemma* monoid_hom.injective_noncomm_pi_coprod_of_independent
- \+ *def* monoid_hom.noncomm_pi_coprod
- \+ *def* monoid_hom.noncomm_pi_coprod_equiv
- \+ *lemma* monoid_hom.noncomm_pi_coprod_mrange
- \+ *lemma* monoid_hom.noncomm_pi_coprod_mul_single
- \+ *lemma* monoid_hom.noncomm_pi_coprod_range
- \+ *lemma* subgroup.commute_subtype_of_commute
- \+ *lemma* subgroup.independent_of_coprime_order
- \+ *lemma* subgroup.injective_noncomm_pi_coprod_of_independent
- \+ *def* subgroup.noncomm_pi_coprod
- \+ *lemma* subgroup.noncomm_pi_coprod_mul_single
- \+ *lemma* subgroup.noncomm_pi_coprod_range

Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_inv
- \+ *lemma* order_of_map_dvd

Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.eq_one_of_noncomm_prod_eq_one_of_independent



## [2022-03-16 10:05:27](https://github.com/leanprover-community/mathlib/commit/a50de33)
docs(algebra/group/hom): fix typo ([#12723](https://github.com/leanprover-community/mathlib/pull/12723))
#### Estimated changes
Modified src/algebra/group/hom.lean




## [2022-03-16 10:05:26](https://github.com/leanprover-community/mathlib/commit/35bb571)
chore(number_theory/primorial): speed up some proofs ([#12714](https://github.com/leanprover-community/mathlib/pull/12714))
#### Estimated changes
Modified src/number_theory/primorial.lean




## [2022-03-16 10:05:25](https://github.com/leanprover-community/mathlib/commit/a8bfcfe)
feat(algebraic_geometry/projective_spectrum): basic definitions of projective spectrum ([#12635](https://github.com/leanprover-community/mathlib/pull/12635))
This pr contains the basic definitions of projective spectrum of a graded ring:
- projective spectrum
- zero locus
- vanishing ideal
#### Estimated changes
Added src/algebraic_geometry/projective_spectrum/topology.lean
- \+ *abbreviation* projective_spectrum.as_homogeneous_ideal
- \+ *lemma* projective_spectrum.as_homogeneous_ideal_def
- \+ *lemma* projective_spectrum.coe_vanishing_ideal
- \+ *lemma* projective_spectrum.ext
- \+ *lemma* projective_spectrum.mem_vanishing_ideal
- \+ *lemma* projective_spectrum.mem_zero_locus
- \+ *lemma* projective_spectrum.subset_zero_locus_iff_le_vanishing_ideal
- \+ *def* projective_spectrum.vanishing_ideal
- \+ *lemma* projective_spectrum.vanishing_ideal_singleton
- \+ *def* projective_spectrum.zero_locus
- \+ *lemma* projective_spectrum.zero_locus_span
- \+ *def* projective_spectrum



## [2022-03-16 10:05:24](https://github.com/leanprover-community/mathlib/commit/a7a2f9d)
feat(data/nat/fib): norm_num plugin for fib ([#12463](https://github.com/leanprover-community/mathlib/pull/12463))
#### Estimated changes
Modified src/data/nat/fib.lean
- \+ *def* norm_num.is_fib_aux
- \+ *lemma* norm_num.is_fib_aux_bit0
- \+ *lemma* norm_num.is_fib_aux_bit0_done
- \+ *lemma* norm_num.is_fib_aux_bit1
- \+ *lemma* norm_num.is_fib_aux_bit1_done
- \+ *lemma* norm_num.is_fib_aux_one

Modified test/norm_num_ext.lean




## [2022-03-16 10:05:23](https://github.com/leanprover-community/mathlib/commit/500a1d3)
feat(data/pnat/find): port over `nat.find` API ([#12413](https://github.com/leanprover-community/mathlib/pull/12413))
Didn't port `pnat.find_add` because I got lost in the proof.
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.le_one_iff
- \+ *lemma* pnat.lt_add_left
- \+ *lemma* pnat.lt_add_right
- \+ *lemma* pnat.not_lt_one

Added src/data/pnat/find.lean
- \+ *lemma* pnat.find_comp_succ
- \+ *lemma* pnat.find_eq_iff
- \+ *lemma* pnat.find_eq_one
- \+ *lemma* pnat.find_le
- \+ *lemma* pnat.find_le_iff
- \+ *lemma* pnat.find_lt_iff
- \+ *theorem* pnat.find_mono
- \+ *lemma* pnat.le_find_iff
- \+ *lemma* pnat.lt_find_iff
- \+ *lemma* pnat.one_le_find



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
Modified src/algebra/algebra/subalgebra/basic.lean


Modified src/deprecated/submonoid.lean
- \+/\- *lemma* submonoid.is_submonoid
- \+/\- *def* submonoid.of

Modified src/field_theory/subfield.lean


Modified src/group_theory/free_product.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/basic.lean
- \+/\- *structure* add_submonoid
- \+/\- *structure* submonoid

Modified src/group_theory/submonoid/pointwise.lean


Added src/group_theory/subsemigroup/basic.lean
- \+ *structure* add_subsemigroup
- \+ *lemma* mul_hom.coe_of_mdense
- \+ *def* mul_hom.eq_mlocus
- \+ *lemma* mul_hom.eq_of_eq_on_mdense
- \+ *lemma* mul_hom.eq_of_eq_on_mtop
- \+ *lemma* mul_hom.eq_on_mclosure
- \+ *def* mul_hom.of_mdense
- \+ *def* subsemigroup.closure
- \+ *lemma* subsemigroup.closure_Union
- \+ *lemma* subsemigroup.closure_empty
- \+ *lemma* subsemigroup.closure_eq
- \+ *lemma* subsemigroup.closure_eq_of_le
- \+ *lemma* subsemigroup.closure_induction'
- \+ *lemma* subsemigroup.closure_induction
- \+ *lemma* subsemigroup.closure_le
- \+ *lemma* subsemigroup.closure_mono
- \+ *lemma* subsemigroup.closure_singleton_le_iff_mem
- \+ *lemma* subsemigroup.closure_union
- \+ *lemma* subsemigroup.closure_univ
- \+ *lemma* subsemigroup.coe_Inf
- \+ *lemma* subsemigroup.coe_bot
- \+ *lemma* subsemigroup.coe_copy
- \+ *lemma* subsemigroup.coe_inf
- \+ *lemma* subsemigroup.coe_infi
- \+ *lemma* subsemigroup.coe_set_mk
- \+ *lemma* subsemigroup.coe_top
- \+ *lemma* subsemigroup.copy_eq
- \+ *lemma* subsemigroup.dense_induction
- \+ *theorem* subsemigroup.ext
- \+ *lemma* subsemigroup.mem_Inf
- \+ *lemma* subsemigroup.mem_carrier
- \+ *lemma* subsemigroup.mem_closure
- \+ *lemma* subsemigroup.mem_inf
- \+ *lemma* subsemigroup.mem_infi
- \+ *lemma* subsemigroup.mem_mk
- \+ *lemma* subsemigroup.mem_supr
- \+ *lemma* subsemigroup.mem_top
- \+ *lemma* subsemigroup.mk_le_mk
- \+ *theorem* subsemigroup.mul_mem
- \+ *lemma* subsemigroup.not_mem_bot
- \+ *lemma* subsemigroup.not_mem_of_not_mem_closure
- \+ *def* subsemigroup.simps.coe
- \+ *lemma* subsemigroup.subset_closure
- \+ *lemma* subsemigroup.subsingleton_of_subsingleton
- \+ *lemma* subsemigroup.supr_eq_closure
- \+ *structure* subsemigroup

Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/span.lean


Modified src/ring_theory/class_group.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean




## [2022-03-16 08:21:55](https://github.com/leanprover-community/mathlib/commit/50691e5)
chore(measure_theory/function): split files strongly_measurable and simple_func_dense ([#12711](https://github.com/leanprover-community/mathlib/pull/12711))
The files `strongly_measurable` and `simple_func_dense` contain general results, and results pertaining to the `L^p` space. We move the results regarding `L^p` to new files, to make sure that the main parts of the files can be imported earlier in the hierarchy. This is needed for a forthcoming integral refactor.
#### Estimated changes
Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/function/continuous_map_dense.lean


Modified src/measure_theory/function/simple_func_dense.lean
- \- *lemma* measure_theory.L1.simple_func.to_Lp_one_eq_to_L1
- \- *lemma* measure_theory.Lp.induction
- \- *lemma* measure_theory.Lp.simple_func.add_to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.coe_coe
- \- *lemma* measure_theory.Lp.simple_func.coe_fn_le
- \- *lemma* measure_theory.Lp.simple_func.coe_fn_nonneg
- \- *lemma* measure_theory.Lp.simple_func.coe_fn_zero
- \- *lemma* measure_theory.Lp.simple_func.coe_indicator_const
- \- *def* measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg
- \- *lemma* measure_theory.Lp.simple_func.coe_smul
- \- *def* measure_theory.Lp.simple_func.coe_to_Lp
- \- *lemma* measure_theory.Lp.simple_func.dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \- *lemma* measure_theory.Lp.simple_func.exists_simple_func_nonneg_ae_eq
- \- *def* measure_theory.Lp.simple_func.indicator_const
- \- *lemma* measure_theory.Lp.simple_func.neg_to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.norm_to_Lp
- \- *lemma* measure_theory.Lp.simple_func.norm_to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.smul_to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.sub_to_simple_func
- \- *def* measure_theory.Lp.simple_func.to_Lp
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_add
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_eq_mk
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_eq_to_Lp
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_neg
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_smul
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_sub
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.to_Lp_zero
- \- *def* measure_theory.Lp.simple_func.to_simple_func
- \- *lemma* measure_theory.Lp.simple_func.to_simple_func_eq_to_fun
- \- *lemma* measure_theory.Lp.simple_func.to_simple_func_indicator_const
- \- *lemma* measure_theory.Lp.simple_func.to_simple_func_to_Lp
- \- *lemma* measure_theory.Lp.simple_func.zero_to_simple_func
- \- *def* measure_theory.Lp.simple_func
- \- *lemma* measure_theory.integrable.induction
- \- *lemma* measure_theory.mem_ℒp.induction
- \- *lemma* measure_theory.simple_func.exists_forall_norm_le
- \- *lemma* measure_theory.simple_func.fin_meas_supp.integrable
- \- *lemma* measure_theory.simple_func.integrable_approx_on
- \- *lemma* measure_theory.simple_func.integrable_approx_on_univ
- \- *lemma* measure_theory.simple_func.integrable_iff
- \- *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \- *lemma* measure_theory.simple_func.integrable_of_is_finite_measure
- \- *lemma* measure_theory.simple_func.integrable_pair
- \- *lemma* measure_theory.simple_func.measure_lt_top_of_mem_ℒp_indicator
- \- *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_integrable
- \- *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp
- \- *lemma* measure_theory.simple_func.measure_support_lt_top
- \- *lemma* measure_theory.simple_func.measure_support_lt_top_of_integrable
- \- *lemma* measure_theory.simple_func.measure_support_lt_top_of_mem_ℒp
- \- *lemma* measure_theory.simple_func.mem_ℒp_approx_on
- \- *lemma* measure_theory.simple_func.mem_ℒp_approx_on_univ
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp
- \- *lemma* measure_theory.simple_func.mem_ℒp_iff_integrable
- \- *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage
- \- *lemma* measure_theory.simple_func.mem_ℒp_of_is_finite_measure
- \- *lemma* measure_theory.simple_func.mem_ℒp_top
- \- *lemma* measure_theory.simple_func.mem_ℒp_zero
- \- *lemma* measure_theory.simple_func.nnnorm_approx_on_le
- \- *lemma* measure_theory.simple_func.norm_approx_on_y₀_le
- \- *lemma* measure_theory.simple_func.norm_approx_on_zero_le
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_L1_nnnorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_Lp_snorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_nnnorm
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp
- \- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp_snorm

Added src/measure_theory/function/simple_func_dense_lp.lean
- \+ *lemma* measure_theory.L1.simple_func.to_Lp_one_eq_to_L1
- \+ *lemma* measure_theory.Lp.induction
- \+ *lemma* measure_theory.Lp.simple_func.add_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.coe_coe
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_le
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.coe_fn_zero
- \+ *lemma* measure_theory.Lp.simple_func.coe_indicator_const
- \+ *def* measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.coe_smul
- \+ *def* measure_theory.Lp.simple_func.coe_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.dense_range_coe_simple_func_nonneg_to_Lp_nonneg
- \+ *lemma* measure_theory.Lp.simple_func.exists_simple_func_nonneg_ae_eq
- \+ *def* measure_theory.Lp.simple_func.indicator_const
- \+ *lemma* measure_theory.Lp.simple_func.neg_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.norm_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.norm_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.smul_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.sub_to_simple_func
- \+ *def* measure_theory.Lp.simple_func.to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_add
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_eq_mk
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_eq_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_neg
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_smul
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_sub
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.to_Lp_zero
- \+ *def* measure_theory.Lp.simple_func.to_simple_func
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_eq_to_fun
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_indicator_const
- \+ *lemma* measure_theory.Lp.simple_func.to_simple_func_to_Lp
- \+ *lemma* measure_theory.Lp.simple_func.zero_to_simple_func
- \+ *def* measure_theory.Lp.simple_func
- \+ *lemma* measure_theory.integrable.induction
- \+ *lemma* measure_theory.mem_ℒp.induction
- \+ *lemma* measure_theory.simple_func.exists_forall_norm_le
- \+ *lemma* measure_theory.simple_func.fin_meas_supp.integrable
- \+ *lemma* measure_theory.simple_func.integrable_approx_on
- \+ *lemma* measure_theory.simple_func.integrable_approx_on_univ
- \+ *lemma* measure_theory.simple_func.integrable_iff
- \+ *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.integrable_of_is_finite_measure
- \+ *lemma* measure_theory.simple_func.integrable_pair
- \+ *lemma* measure_theory.simple_func.measure_lt_top_of_mem_ℒp_indicator
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_integrable
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top_of_integrable
- \+ *lemma* measure_theory.simple_func.measure_support_lt_top_of_mem_ℒp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_approx_on
- \+ *lemma* measure_theory.simple_func.mem_ℒp_approx_on_univ
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_integrable
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_is_finite_measure
- \+ *lemma* measure_theory.simple_func.mem_ℒp_top
- \+ *lemma* measure_theory.simple_func.mem_ℒp_zero
- \+ *lemma* measure_theory.simple_func.nnnorm_approx_on_le
- \+ *lemma* measure_theory.simple_func.norm_approx_on_y₀_le
- \+ *lemma* measure_theory.simple_func.norm_approx_on_zero_le
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_L1_nnnorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_Lp_snorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_L1_nnnorm
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp
- \+ *lemma* measure_theory.simple_func.tendsto_approx_on_univ_Lp_snorm

Modified src/measure_theory/function/strongly_measurable.lean
- \- *lemma* measure_theory.Lp.fin_strongly_measurable
- \- *lemma* measure_theory.integrable.ae_fin_strongly_measurable
- \- *lemma* measure_theory.mem_ℒp.ae_fin_strongly_measurable
- \- *lemma* measure_theory.mem_ℒp.fin_strongly_measurable_of_measurable

Added src/measure_theory/function/strongly_measurable_lp.lean
- \+ *lemma* measure_theory.Lp.fin_strongly_measurable
- \+ *lemma* measure_theory.integrable.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.mem_ℒp.ae_fin_strongly_measurable
- \+ *lemma* measure_theory.mem_ℒp.fin_strongly_measurable_of_measurable

Modified src/measure_theory/integral/set_to_l1.lean




## [2022-03-16 08:21:54](https://github.com/leanprover-community/mathlib/commit/ba6c84d)
feat(ring_theory/fractional_ideal): two span_singleton lemmas ([#12656](https://github.com/leanprover-community/mathlib/pull/12656))
#### Estimated changes
Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.span_singleton_eq_span_singleton

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.span_singleton_eq_span_singleton
- \+ *lemma* fractional_ideal.span_singleton_pow



## [2022-03-16 08:21:53](https://github.com/leanprover-community/mathlib/commit/17c74f1)
feat(algebra/group_power/order): add le_pow ([#12436](https://github.com/leanprover-community/mathlib/pull/12436))
Added a new theorem so that library search will find it.
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *theorem* le_self_pow



## [2022-03-16 08:21:52](https://github.com/leanprover-community/mathlib/commit/91f98e8)
feat(topology/bornology/hom): Locally bounded maps ([#12046](https://github.com/leanprover-community/mathlib/pull/12046))
Define `locally_bounded_map`, the type of locally bounded maps between two bornologies.
#### Estimated changes
Modified src/topology/bornology/basic.lean
- \+ *lemma* bornology.comap_cobounded_le_iff
- \+/\- *lemma* bornology.is_bounded_compl_iff
- \+/\- *lemma* bornology.is_bounded_empty
- \+ *lemma* bornology.is_cobounded_compl_iff

Added src/topology/bornology/hom.lean
- \+ *lemma* is_bounded.image
- \+ *lemma* locally_bounded_map.cancel_left
- \+ *lemma* locally_bounded_map.cancel_right
- \+ *lemma* locally_bounded_map.coe_comp
- \+ *lemma* locally_bounded_map.coe_id
- \+ *lemma* locally_bounded_map.coe_of_map_bounded
- \+ *def* locally_bounded_map.comp
- \+ *lemma* locally_bounded_map.comp_apply
- \+ *lemma* locally_bounded_map.comp_assoc
- \+ *lemma* locally_bounded_map.comp_id
- \+ *lemma* locally_bounded_map.ext
- \+ *lemma* locally_bounded_map.id_apply
- \+ *lemma* locally_bounded_map.id_comp
- \+ *def* locally_bounded_map.of_map_bounded
- \+ *lemma* locally_bounded_map.of_map_bounded_apply
- \+ *lemma* locally_bounded_map.to_fun_eq_coe
- \+ *structure* locally_bounded_map



## [2022-03-16 08:21:51](https://github.com/leanprover-community/mathlib/commit/68033a2)
feat(set_theory/ordinal_arithmetic): A set of ordinals is bounded above iff it's small ([#11870](https://github.com/leanprover-community/mathlib/pull/11870))
#### Estimated changes
Modified src/logic/small.lean
- \+ *theorem* small_subset

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.bdd_above_iff_small
- \+ *theorem* ordinal.le_sup_shrink_equiv
- \+ *theorem* ordinal.small_Iio
- \+ *theorem* ordinal.sup_eq_Sup



## [2022-03-16 07:51:24](https://github.com/leanprover-community/mathlib/commit/a452bfa)
feat(analysis/seminorm): three simple lemmas about balls ([#12720](https://github.com/leanprover-community/mathlib/pull/12720))
The lemmas are in preparation to characterize the natural bornology in terms of seminorms in LCTVSs.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.ball_eq_emptyset
- \+ *lemma* seminorm.ball_zero_absorbs_ball_zero
- \+ *lemma* seminorm.smul_ball_zero



## [2022-03-16 05:24:58](https://github.com/leanprover-community/mathlib/commit/1f1289f)
feat(algebra/parity + data/{int, nat}/parity): parity lemmas for general semirings ([#12718](https://github.com/leanprover-community/mathlib/pull/12718))
This PR proves some general facts about adding even/odd elements in a semiring, thus removing the need to proving the same results for `nat` and `int`.
#### Estimated changes
Added src/algebra/parity.lean
- \+ *theorem* even.add_even
- \+ *theorem* even.add_odd
- \+ *theorem* odd.add_even
- \+ *theorem* odd.add_odd

Modified src/data/int/parity.lean
- \- *theorem* int.even.add_even
- \- *theorem* int.even.add_odd
- \- *theorem* int.odd.add_even
- \- *theorem* int.odd.add_odd

Modified src/data/nat/parity.lean
- \- *theorem* nat.even.add_even
- \- *theorem* nat.even.add_odd
- \- *theorem* nat.odd.add_even
- \- *theorem* nat.odd.add_odd



## [2022-03-16 03:13:34](https://github.com/leanprover-community/mathlib/commit/cbd6173)
chore(scripts): update nolints.txt ([#12728](https://github.com/leanprover-community/mathlib/pull/12728))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-16 00:32:33](https://github.com/leanprover-community/mathlib/commit/45061f3)
chore(data/equiv/basic): use `option.elim` and `sum.elim` ([#12724](https://github.com/leanprover-community/mathlib/pull/12724))
We have these functions, why not use them?
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2022-03-15 18:38:06](https://github.com/leanprover-community/mathlib/commit/b622d4d)
chore(algebra/associated): move prime_dvd_prime_iff_eq ([#12706](https://github.com/leanprover-community/mathlib/pull/12706))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* prime_dvd_prime_iff_eq

Modified src/data/list/prime.lean
- \- *lemma* prime_dvd_prime_iff_eq



## [2022-03-15 16:38:31](https://github.com/leanprover-community/mathlib/commit/7ed4f2c)
feat(group_theory/submonoid/operations): monoids are isomorphic to themselves as submonoids ([#12658](https://github.com/leanprover-community/mathlib/pull/12658))
#### Estimated changes
Modified src/algebra/algebra/subalgebra/basic.lean
- \- *def* algebra.top_equiv
- \+ *def* subalgebra.top_equiv

Modified src/algebra/lie/nilpotent.lean


Modified src/algebra/lie/semisimple.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/lie/submodule.lean
- \+ *def* lie_ideal.top_equiv
- \+ *lemma* lie_ideal.top_equiv_apply
- \- *def* lie_ideal.top_equiv_self
- \- *lemma* lie_ideal.top_equiv_self_apply
- \+ *def* lie_subalgebra.top_equiv
- \+ *lemma* lie_subalgebra.top_equiv_apply
- \- *def* lie_subalgebra.top_equiv_self
- \- *lemma* lie_subalgebra.top_equiv_self_apply

Modified src/algebra/module/submodule_lattice.lean
- \+ *def* submodule.top_equiv
- \- *def* submodule.top_equiv_self

Modified src/field_theory/adjoin.lean


Modified src/group_theory/subgroup/basic.lean
- \+ *def* subgroup.top_equiv

Modified src/group_theory/submonoid/operations.lean
- \+ *def* submonoid.top_equiv
- \+ *lemma* submonoid.top_equiv_to_monoid_hom

Modified src/number_theory/cyclotomic/primitive_roots.lean


Modified src/ring_theory/adjoin/power_basis.lean




## [2022-03-15 15:20:21](https://github.com/leanprover-community/mathlib/commit/375419f)
feat(algebra/algebra/subalgebra/pointwise): lemmas about `*` and `to_submodule` ([#12695](https://github.com/leanprover-community/mathlib/pull/12695))
#### Estimated changes
Modified src/algebra/algebra/subalgebra/pointwise.lean
- \+/\- *theorem* subalgebra.mul_self
- \+ *theorem* subalgebra.mul_to_submodule
- \+ *theorem* subalgebra.mul_to_submodule_le



## [2022-03-15 14:10:30](https://github.com/leanprover-community/mathlib/commit/7582e14)
feat(linear_algebra/matrix/determinant): special case of the matrix determinant lemma ([#12682](https://github.com/leanprover-community/mathlib/pull/12682))
#### Estimated changes
Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_one_add_col_mul_row
- \+ *lemma* matrix.lower_two_block_triangular_det
- \+/\- *lemma* matrix.upper_two_block_triangular_det



## [2022-03-15 14:10:28](https://github.com/leanprover-community/mathlib/commit/9c09965)
feat(algebra/big_operators/finprod): finite product of power is power of finite product ([#12655](https://github.com/leanprover-community/mathlib/pull/12655))
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_pow



## [2022-03-15 13:39:45](https://github.com/leanprover-community/mathlib/commit/88a5978)
doc(algebra/hierarchy_design): fix my name ([#12674](https://github.com/leanprover-community/mathlib/pull/12674))
#### Estimated changes
Modified src/algebra/hierarchy_design.lean




## [2022-03-15 11:51:47](https://github.com/leanprover-community/mathlib/commit/530f008)
feat(linear_algebra/matrix/nonsingular_inverse): Add `matrix.list_prod_inv_reverse` ([#12691](https://github.com/leanprover-community/mathlib/pull/12691))
#### Estimated changes
Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* matrix.list_prod_inv_reverse



## [2022-03-15 11:51:46](https://github.com/leanprover-community/mathlib/commit/7a02c9e)
fix(set_theory/ordinal_arithmetic): remove redundant hypothesis from `CNF_rec` ([#12680](https://github.com/leanprover-community/mathlib/pull/12680))
The hypothesis in question was a theorem that could be deduced.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.CNF_aux
- \+/\- *theorem* ordinal.CNF_fst_le_log
- \+/\- *theorem* ordinal.CNF_pairwise
- \+/\- *theorem* ordinal.CNF_snd_lt
- \+/\- *theorem* ordinal.CNF_sorted
- \+ *theorem* ordinal.mod_opow_log_lt_self
- \+/\- *theorem* ordinal.one_CNF



## [2022-03-15 11:51:45](https://github.com/leanprover-community/mathlib/commit/a3b39c6)
feat(linear_algebra/clifford_algebra/conjugation): add lemmas showing interaction between `involute` and `even_odd` ([#12672](https://github.com/leanprover-community/mathlib/pull/12672))
Often the even and odd submodules are defined in terms of involution, but this strategy doesn't actually work in characteristic two.
#### Estimated changes
Modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.has_graded_one.algebra_map_mem

Modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *lemma* clifford_algebra.involute_eq_of_mem_even
- \+ *lemma* clifford_algebra.involute_eq_of_mem_odd

Modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* clifford_algebra.even_induction
- \+ *lemma* clifford_algebra.even_odd_induction
- \+ *lemma* clifford_algebra.odd_induction
- \+ *lemma* clifford_algebra.ι_mul_ι_mem_even_odd_zero



## [2022-03-15 11:51:44](https://github.com/leanprover-community/mathlib/commit/48ffeb7)
feat(group_theory/finiteness): quotient of fg is fg ([#12652](https://github.com/leanprover-community/mathlib/pull/12652))
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.mk_surjective

Modified src/group_theory/finiteness.lean
- \+ *lemma* group.fg_of_surjective

Modified src/group_theory/quotient_group.lean
- \+ *lemma* quotient_group.mk'_surjective
- \- *lemma* quotient_group.subgroup_eq_top_of_subsingleton

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* monoid_hom.mrange_restrict_surjective
- \+/\- *lemma* submonoid.bot_or_exists_ne_one
- \+/\- *lemma* submonoid.bot_or_nontrivial



## [2022-03-15 11:10:28](https://github.com/leanprover-community/mathlib/commit/a98202b)
chore(category_theory/preadditive/projective_resolution): typo ([#12702](https://github.com/leanprover-community/mathlib/pull/12702))
#### Estimated changes
Modified src/category_theory/preadditive/projective_resolution.lean




## [2022-03-15 11:10:27](https://github.com/leanprover-community/mathlib/commit/eefa425)
perf(analysis/convec/topology): remove topological_add_group.path_connected instance ([#12675](https://github.com/leanprover-community/mathlib/pull/12675))
The linter was right in [#10011](https://github.com/leanprover-community/mathlib/pull/10011) and `topological_add_group.path_connected` should not be an instance, because it creates enormous TC subproblems (turn on `pp.all` to get an idea of what's going on).
Apparently the instance isn't even used in mathlib.
#### Estimated changes
Modified src/analysis/convex/topology.lean
- \+ *lemma* topological_add_group.path_connected



## [2022-03-15 11:10:26](https://github.com/leanprover-community/mathlib/commit/5b90340)
feat(model_theory/terms_and_formulas): Notation for terms and formulas from Flypitch ([#12630](https://github.com/leanprover-community/mathlib/pull/12630))
Introduces some notation, localized to `first_order`, to make typing explicit terms and formulas easier.
#### Estimated changes
Modified src/model_theory/terms_and_formulas.lean




## [2022-03-15 10:32:43](https://github.com/leanprover-community/mathlib/commit/d199eb9)
feat(ring_theory/graded_algebra/homogeneous_ideal): refactor `homogeneous_ideal` as a structure extending ideals ([#12673](https://github.com/leanprover-community/mathlib/pull/12673))
We refactored `homogeneous_ideal` as a structure extending ideals so that we can define a `set_like (homogeneous_ideal \McA) A` instance.
#### Estimated changes
Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \- *lemma* homogeneous_ideal.coe_Inf
- \- *lemma* homogeneous_ideal.coe_Sup
- \- *lemma* homogeneous_ideal.coe_add
- \- *lemma* homogeneous_ideal.coe_bot
- \- *lemma* homogeneous_ideal.coe_inf
- \- *lemma* homogeneous_ideal.coe_infi
- \- *lemma* homogeneous_ideal.coe_irrelevant
- \- *lemma* homogeneous_ideal.coe_mul
- \- *lemma* homogeneous_ideal.coe_sup
- \- *lemma* homogeneous_ideal.coe_top
- \+/\- *lemma* homogeneous_ideal.eq_bot_iff
- \+/\- *lemma* homogeneous_ideal.eq_top_iff
- \+ *lemma* homogeneous_ideal.ext
- \- *lemma* homogeneous_ideal.homogeneous_core_coe_eq_self
- \- *lemma* homogeneous_ideal.homogeneous_hull_coe_eq_self
- \+ *lemma* homogeneous_ideal.homogeneous_hull_to_ideal_eq_self
- \+ *lemma* homogeneous_ideal.is_homogeneous
- \+ *lemma* homogeneous_ideal.mem_iff
- \+ *def* homogeneous_ideal.to_ideal
- \+ *lemma* homogeneous_ideal.to_ideal_Inf
- \+ *lemma* homogeneous_ideal.to_ideal_Sup
- \+ *lemma* homogeneous_ideal.to_ideal_add
- \+ *lemma* homogeneous_ideal.to_ideal_bot
- \+ *lemma* homogeneous_ideal.to_ideal_homogeneous_core_eq_self
- \+ *lemma* homogeneous_ideal.to_ideal_inf
- \+ *lemma* homogeneous_ideal.to_ideal_infi
- \+ *lemma* homogeneous_ideal.to_ideal_injective
- \+ *lemma* homogeneous_ideal.to_ideal_irrelevant
- \+ *lemma* homogeneous_ideal.to_ideal_mul
- \+ *lemma* homogeneous_ideal.to_ideal_sup
- \+ *lemma* homogeneous_ideal.to_ideal_top
- \+ *structure* homogeneous_ideal
- \- *abbreviation* homogeneous_ideal
- \- *lemma* ideal.coe_homogeneous_core_le
- \- *lemma* ideal.coe_homogeneous_hull_eq_supr
- \+/\- *lemma* ideal.homogeneous_core.gc
- \+/\- *def* ideal.homogeneous_core.gi
- \+/\- *lemma* ideal.homogeneous_hull.gc
- \+/\- *def* ideal.homogeneous_hull.gi
- \- *lemma* ideal.is_homogeneous.coe_homogeneous_core_eq_self
- \- *lemma* ideal.is_homogeneous.homogeneous_hull_eq_self
- \+/\- *lemma* ideal.is_homogeneous.iff_eq
- \+ *lemma* ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self
- \+ *lemma* ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self
- \- *lemma* ideal.le_coe_homogeneous_hull
- \+ *lemma* ideal.le_to_ideal_homogeneous_hull
- \+ *lemma* ideal.to_ideal_homogeneous_core_le
- \+ *lemma* ideal.to_ideal_homogeneous_hull_eq_supr

Modified src/ring_theory/graded_algebra/radical.lean




## [2022-03-15 10:32:41](https://github.com/leanprover-community/mathlib/commit/061d04b)
feat(category_theory/monoidal): distribute tensor over direct sum ([#12626](https://github.com/leanprover-community/mathlib/pull/12626))
This is preliminary to the monoidal structure on chain complexes.
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* category_theory.limits.is_bilimit.binary_total
- \+ *lemma* category_theory.limits.is_bilimit.total

Modified src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.dite_tensor
- \+ *lemma* category_theory.monoidal_category.tensor_dite

Modified src/category_theory/monoidal/preadditive.lean
- \+ *def* category_theory.left_distributor
- \+ *lemma* category_theory.left_distributor_assoc
- \+ *lemma* category_theory.left_distributor_hom
- \+ *lemma* category_theory.left_distributor_inv
- \+ *lemma* category_theory.left_distributor_right_distributor_assoc
- \+ *def* category_theory.right_distributor
- \+ *lemma* category_theory.right_distributor_assoc
- \+ *lemma* category_theory.right_distributor_hom
- \+ *lemma* category_theory.right_distributor_inv
- \+ *lemma* category_theory.sum_tensor
- \+ *lemma* category_theory.tensor_sum



## [2022-03-15 10:02:26](https://github.com/leanprover-community/mathlib/commit/078b213)
chore(category_theory/abelian/projective): fix typo ([#12701](https://github.com/leanprover-community/mathlib/pull/12701))
#### Estimated changes
Modified src/category_theory/abelian/projective.lean




## [2022-03-15 08:11:54](https://github.com/leanprover-community/mathlib/commit/92e6759)
fix(category_theory/bicategory): remove spaces before closing parentheses ([#12700](https://github.com/leanprover-community/mathlib/pull/12700))
#### Estimated changes
Modified src/category_theory/bicategory/basic.lean




## [2022-03-15 08:11:53](https://github.com/leanprover-community/mathlib/commit/0bd6dc2)
chore(measure_theory): move and rename some lemmas ([#12699](https://github.com/leanprover-community/mathlib/pull/12699))
* move `ae_interval_oc_iff`, `ae_measurable_interval_oc_iff`, and `ae_interval_oc_iff'` to `measure_theory.measure.measure_space`, rename `ae_interval_oc_iff'` to `ae_restrict_interval_oc_iff`;
* add lemmas about `ae` and union of sets.
#### Estimated changes
Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.interval_oc_eq_union

Modified src/measure_theory/integral/interval_integral.lean
- \- *lemma* ae_interval_oc_iff'
- \- *lemma* ae_interval_oc_iff
- \- *lemma* ae_measurable_interval_oc_iff

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_measurable_interval_oc_iff
- \+ *lemma* ae_measurable_union_iff
- \+ *lemma* measure_theory.ae_interval_oc_iff
- \+ *lemma* measure_theory.ae_restrict_Union_eq
- \+ *lemma* measure_theory.ae_restrict_interval_oc_eq
- \+ *lemma* measure_theory.ae_restrict_interval_oc_iff
- \+ *lemma* measure_theory.ae_restrict_union_eq



## [2022-03-15 08:11:52](https://github.com/leanprover-community/mathlib/commit/4b562f8)
doc(data/equiv/encodable): +2 docstrings ([#12698](https://github.com/leanprover-community/mathlib/pull/12698))
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean




## [2022-03-15 08:11:51](https://github.com/leanprover-community/mathlib/commit/a3e0c85)
chore(cyclotomic/gal): update todo ([#12693](https://github.com/leanprover-community/mathlib/pull/12693))
this mentioned a non-existing old solution which got superseded by `is_primitive_root.power_basis`, but is still not the right solution in the long term
#### Estimated changes
Modified src/number_theory/cyclotomic/gal.lean




## [2022-03-15 08:11:50](https://github.com/leanprover-community/mathlib/commit/77395f1)
chore(algebra/module/basic): Move the scalar action earlier ([#12690](https://github.com/leanprover-community/mathlib/pull/12690))
This is prep work for golfing some of the instances.
This also adjust the variables slightly to be in a more sensible order.
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* continuous_linear_map.coe_smul'
- \+/\- *lemma* continuous_linear_map.coe_smul
- \+/\- *lemma* continuous_linear_map.smul_apply



## [2022-03-15 08:11:49](https://github.com/leanprover-community/mathlib/commit/025fe7c)
feat(group_theory/abelianization): An application of the three subgroups lemma ([#12677](https://github.com/leanprover-community/mathlib/pull/12677))
This PR uses the three subgroups lemma to prove that `⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G`.
#### Estimated changes
Modified src/group_theory/abelianization.lean
- \+ *lemma* commutator_centralizer_commutator_le_center



## [2022-03-15 08:11:48](https://github.com/leanprover-community/mathlib/commit/b7978f3)
chore(analysis/seminorm): Weaken typeclasses on `convex` and `locally_convex` lemmas ([#12645](https://github.com/leanprover-community/mathlib/pull/12645))
Generalize type-classes `normed_linearly_ordered_field` to `normed_field` (otherwise it would not work over complex numbers).
#### Estimated changes
Modified src/analysis/seminorm.lean




## [2022-03-15 08:11:47](https://github.com/leanprover-community/mathlib/commit/53f6d68)
feat(category_theory/preadditive) : definition of injective resolution ([#12641](https://github.com/leanprover-community/mathlib/pull/12641))
This pr is splitted from [#12545](https://github.com/leanprover-community/mathlib/pull/12545). This pr contains the definition of:
- `InjectiveResolution`;
- `has_injective_resolution` and `has_injective_resolutions`;
- injective object has injective resolution.
#### Estimated changes
Added src/category_theory/preadditive/injective_resolution.lean
- \+ *def* category_theory.InjectiveResolution.self
- \+ *lemma* category_theory.InjectiveResolution.ι_f_succ
- \+ *structure* category_theory.InjectiveResolution



## [2022-03-15 08:11:46](https://github.com/leanprover-community/mathlib/commit/585d641)
refactor(linear_algebra/basic): split file ([#12637](https://github.com/leanprover-community/mathlib/pull/12637))
`linear_algebra.basic` has become a 2800 line monster, with lots of imports.
This is some further work on splitting it into smaller pieces, by extracting everything about (or needing) `span` to `linear_algebra.span`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/submodule_pointwise.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/basic.lean
- \- *abbreviation* linear_equiv.coord
- \- *lemma* linear_equiv.coord_self
- \- *lemma* linear_equiv.ker_to_span_singleton
- \- *def* linear_equiv.to_span_nonzero_singleton
- \- *lemma* linear_equiv.to_span_nonzero_singleton_one
- \- *lemma* linear_map.eq_on_span'
- \- *lemma* linear_map.eq_on_span
- \- *lemma* linear_map.ext_on
- \- *lemma* linear_map.ext_on_range
- \- *theorem* linear_map.map_eq_top_iff
- \- *theorem* linear_map.map_injective
- \- *theorem* linear_map.map_le_map_iff'
- \- *lemma* linear_map.span_singleton_eq_range
- \- *lemma* linear_map.span_singleton_sup_ker_eq_top
- \- *def* linear_map.to_span_singleton
- \- *lemma* linear_map.to_span_singleton_one
- \- *lemma* submodule.apply_mem_span_image_of_mem_span
- \- *lemma* submodule.coe_scott_continuous
- \- *lemma* submodule.coe_sup
- \- *lemma* submodule.coe_supr_of_chain
- \- *theorem* submodule.coe_supr_of_directed
- \- *lemma* submodule.comap_map_eq
- \- *lemma* submodule.comap_map_eq_self
- \- *lemma* submodule.disjoint_span_singleton'
- \- *lemma* submodule.disjoint_span_singleton
- \- *lemma* submodule.le_span_singleton_iff
- \- *lemma* submodule.lt_sup_iff_not_mem
- \- *lemma* submodule.map_span
- \- *lemma* submodule.map_span_le
- \- *lemma* submodule.map_subtype_span_singleton
- \- *theorem* submodule.mem_Sup_of_directed
- \- *lemma* submodule.mem_prod
- \- *lemma* submodule.mem_span
- \- *lemma* submodule.mem_span_finite_of_mem_span
- \- *lemma* submodule.mem_span_insert'
- \- *lemma* submodule.mem_span_insert
- \- *lemma* submodule.mem_span_singleton
- \- *lemma* submodule.mem_span_singleton_self
- \- *lemma* submodule.mem_span_singleton_trans
- \- *lemma* submodule.mem_sup'
- \- *lemma* submodule.mem_sup
- \- *lemma* submodule.mem_supr
- \- *lemma* submodule.mem_supr_of_chain
- \- *theorem* submodule.mem_supr_of_directed
- \- *lemma* submodule.nontrivial_span_singleton
- \- *lemma* submodule.not_mem_span_of_apply_not_mem_span_image
- \- *def* submodule.prod
- \- *lemma* submodule.prod_bot
- \- *lemma* submodule.prod_coe
- \- *lemma* submodule.prod_inf_prod
- \- *lemma* submodule.prod_mono
- \- *lemma* submodule.prod_sup_prod
- \- *lemma* submodule.prod_top
- \- *lemma* submodule.singleton_span_is_compact_element
- \- *def* submodule.span
- \- *lemma* submodule.span_Union
- \- *lemma* submodule.span_attach_bUnion
- \- *lemma* submodule.span_coe_eq_restrict_scalars
- \- *lemma* submodule.span_empty
- \- *lemma* submodule.span_eq
- \- *lemma* submodule.span_eq_bot
- \- *lemma* submodule.span_eq_of_le
- \- *lemma* submodule.span_eq_supr_of_singleton_spans
- \- *lemma* submodule.span_image
- \- *lemma* submodule.span_induction'
- \- *lemma* submodule.span_induction
- \- *lemma* submodule.span_insert
- \- *lemma* submodule.span_insert_eq_span
- \- *lemma* submodule.span_insert_zero
- \- *lemma* submodule.span_int_eq
- \- *lemma* submodule.span_int_eq_add_subgroup_closure
- \- *lemma* submodule.span_le
- \- *lemma* submodule.span_le_restrict_scalars
- \- *lemma* submodule.span_mono
- \- *lemma* submodule.span_nat_eq
- \- *lemma* submodule.span_nat_eq_add_submonoid_closure
- \- *lemma* submodule.span_neg
- \- *lemma* submodule.span_preimage_le
- \- *lemma* submodule.span_prod_le
- \- *lemma* submodule.span_singleton_eq_bot
- \- *lemma* submodule.span_singleton_eq_range
- \- *lemma* submodule.span_singleton_eq_top_iff
- \- *lemma* submodule.span_singleton_le_iff_mem
- \- *lemma* submodule.span_singleton_smul_eq
- \- *lemma* submodule.span_singleton_smul_le
- \- *lemma* submodule.span_smul_eq_of_is_unit
- \- *lemma* submodule.span_smul_le
- \- *lemma* submodule.span_span
- \- *lemma* submodule.span_span_coe_preimage
- \- *lemma* submodule.span_span_of_tower
- \- *lemma* submodule.span_subset_span
- \- *lemma* submodule.span_sup
- \- *lemma* submodule.span_union
- \- *lemma* submodule.span_univ
- \- *lemma* submodule.span_zero
- \- *lemma* submodule.span_zero_singleton
- \- *lemma* submodule.subset_span
- \- *lemma* submodule.subset_span_trans
- \- *lemma* submodule.sup_span
- \- *lemma* submodule.sup_to_add_subgroup
- \- *lemma* submodule.sup_to_add_submonoid
- \- *lemma* submodule.supr_eq_span
- \- *lemma* submodule.supr_induction'
- \- *lemma* submodule.supr_induction
- \- *lemma* submodule.supr_to_add_submonoid

Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/prod.lean


Modified src/linear_algebra/quotient.lean


Added src/linear_algebra/span.lean
- \+ *abbreviation* linear_equiv.coord
- \+ *lemma* linear_equiv.coord_self
- \+ *def* linear_equiv.to_span_nonzero_singleton
- \+ *lemma* linear_equiv.to_span_nonzero_singleton_one
- \+ *lemma* linear_map.eq_on_span'
- \+ *lemma* linear_map.eq_on_span
- \+ *lemma* linear_map.ext_on
- \+ *lemma* linear_map.ext_on_range
- \+ *lemma* linear_map.ker_to_span_singleton
- \+ *theorem* linear_map.map_eq_top_iff
- \+ *theorem* linear_map.map_injective
- \+ *theorem* linear_map.map_le_map_iff'
- \+ *lemma* linear_map.span_singleton_eq_range
- \+ *lemma* linear_map.span_singleton_sup_ker_eq_top
- \+ *def* linear_map.to_span_singleton
- \+ *lemma* linear_map.to_span_singleton_one
- \+ *lemma* submodule.apply_mem_span_image_of_mem_span
- \+ *lemma* submodule.coe_scott_continuous
- \+ *lemma* submodule.coe_sup
- \+ *lemma* submodule.coe_supr_of_chain
- \+ *theorem* submodule.coe_supr_of_directed
- \+ *lemma* submodule.comap_map_eq
- \+ *lemma* submodule.comap_map_eq_self
- \+ *lemma* submodule.disjoint_span_singleton'
- \+ *lemma* submodule.disjoint_span_singleton
- \+ *lemma* submodule.le_span_singleton_iff
- \+ *lemma* submodule.lt_sup_iff_not_mem
- \+ *lemma* submodule.map_span
- \+ *lemma* submodule.map_span_le
- \+ *lemma* submodule.map_subtype_span_singleton
- \+ *theorem* submodule.mem_Sup_of_directed
- \+ *lemma* submodule.mem_prod
- \+ *lemma* submodule.mem_span
- \+ *lemma* submodule.mem_span_finite_of_mem_span
- \+ *lemma* submodule.mem_span_insert'
- \+ *lemma* submodule.mem_span_insert
- \+ *lemma* submodule.mem_span_singleton
- \+ *lemma* submodule.mem_span_singleton_self
- \+ *lemma* submodule.mem_span_singleton_trans
- \+ *lemma* submodule.mem_sup'
- \+ *lemma* submodule.mem_sup
- \+ *lemma* submodule.mem_supr
- \+ *lemma* submodule.mem_supr_of_chain
- \+ *theorem* submodule.mem_supr_of_directed
- \+ *lemma* submodule.nontrivial_span_singleton
- \+ *lemma* submodule.not_mem_span_of_apply_not_mem_span_image
- \+ *def* submodule.prod
- \+ *lemma* submodule.prod_bot
- \+ *lemma* submodule.prod_coe
- \+ *lemma* submodule.prod_inf_prod
- \+ *lemma* submodule.prod_mono
- \+ *lemma* submodule.prod_sup_prod
- \+ *lemma* submodule.prod_top
- \+ *lemma* submodule.singleton_span_is_compact_element
- \+ *def* submodule.span
- \+ *lemma* submodule.span_Union
- \+ *lemma* submodule.span_attach_bUnion
- \+ *lemma* submodule.span_coe_eq_restrict_scalars
- \+ *lemma* submodule.span_empty
- \+ *lemma* submodule.span_eq
- \+ *lemma* submodule.span_eq_bot
- \+ *lemma* submodule.span_eq_of_le
- \+ *lemma* submodule.span_eq_supr_of_singleton_spans
- \+ *lemma* submodule.span_image
- \+ *lemma* submodule.span_induction'
- \+ *lemma* submodule.span_induction
- \+ *lemma* submodule.span_insert
- \+ *lemma* submodule.span_insert_eq_span
- \+ *lemma* submodule.span_insert_zero
- \+ *lemma* submodule.span_int_eq
- \+ *lemma* submodule.span_int_eq_add_subgroup_closure
- \+ *lemma* submodule.span_le
- \+ *lemma* submodule.span_le_restrict_scalars
- \+ *lemma* submodule.span_mono
- \+ *lemma* submodule.span_nat_eq
- \+ *lemma* submodule.span_nat_eq_add_submonoid_closure
- \+ *lemma* submodule.span_neg
- \+ *lemma* submodule.span_preimage_le
- \+ *lemma* submodule.span_prod_le
- \+ *lemma* submodule.span_singleton_eq_bot
- \+ *lemma* submodule.span_singleton_eq_range
- \+ *lemma* submodule.span_singleton_eq_top_iff
- \+ *lemma* submodule.span_singleton_le_iff_mem
- \+ *lemma* submodule.span_singleton_smul_eq
- \+ *lemma* submodule.span_singleton_smul_le
- \+ *lemma* submodule.span_smul_eq_of_is_unit
- \+ *lemma* submodule.span_smul_le
- \+ *lemma* submodule.span_span
- \+ *lemma* submodule.span_span_coe_preimage
- \+ *lemma* submodule.span_span_of_tower
- \+ *lemma* submodule.span_subset_span
- \+ *lemma* submodule.span_sup
- \+ *lemma* submodule.span_union
- \+ *lemma* submodule.span_univ
- \+ *lemma* submodule.span_zero
- \+ *lemma* submodule.span_zero_singleton
- \+ *lemma* submodule.subset_span
- \+ *lemma* submodule.subset_span_trans
- \+ *lemma* submodule.sup_span
- \+ *lemma* submodule.sup_to_add_subgroup
- \+ *lemma* submodule.sup_to_add_submonoid
- \+ *lemma* submodule.supr_eq_span
- \+ *lemma* submodule.supr_induction'
- \+ *lemma* submodule.supr_induction
- \+ *lemma* submodule.supr_to_add_submonoid

Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/simple_module.lean


Modified src/ring_theory/witt_vector/isocrystal.lean




## [2022-03-15 06:38:19](https://github.com/leanprover-community/mathlib/commit/2ad9b39)
feat(algebra/associated): add irreducible.not_dvd_one ([#12686](https://github.com/leanprover-community/mathlib/pull/12686))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* irreducible.not_dvd_one

Modified src/data/nat/prime.lean
- \+/\- *theorem* nat.prime.not_dvd_one



## [2022-03-15 03:40:54](https://github.com/leanprover-community/mathlib/commit/6d63c9b)
chore(scripts): update nolints.txt ([#12696](https://github.com/leanprover-community/mathlib/pull/12696))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-03-15 03:40:53](https://github.com/leanprover-community/mathlib/commit/0fd9e30)
feat(set_theory/ordinal_arithmetic): `smul` coincides with `mul` ([#12692](https://github.com/leanprover-community/mathlib/pull/12692))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.smul_eq_mul



## [2022-03-15 03:05:43](https://github.com/leanprover-community/mathlib/commit/f337856)
feat(algebra/category): show categorical image in Module agrees with range ([#12605](https://github.com/leanprover-community/mathlib/pull/12605))
This just follows the existing code for the same fact in `AddCommGroup`.
This PR is preparing for a better API for homological calculations in `Module R`.
#### Estimated changes
Added src/algebra/category/Module/images.lean
- \+ *def* Module.factor_thru_image
- \+ *lemma* Module.image.fac
- \+ *lemma* Module.image.lift_fac
- \+ *def* Module.image.ι
- \+ *def* Module.image
- \+ *lemma* Module.image_iso_range_hom_subtype
- \+ *lemma* Module.image_iso_range_inv_image_ι
- \+ *def* Module.mono_factorisation



## [2022-03-15 00:51:24](https://github.com/leanprover-community/mathlib/commit/1148717)
chore(set_theory/ordinal_arithmetic): `well_founded` → `wf` ([#12615](https://github.com/leanprover-community/mathlib/pull/12615))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-03-14 20:38:51](https://github.com/leanprover-community/mathlib/commit/8d2e887)
feat(number_theory/function_field): add place at infinity  ([#12245](https://github.com/leanprover-community/mathlib/pull/12245))
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.nat_degree_sub_eq_of_prod_eq

Modified src/field_theory/ratfunc.lean
- \+ *lemma* ratfunc.X_ne_zero
- \+ *def* ratfunc.int_degree
- \+ *lemma* ratfunc.int_degree_C
- \+ *lemma* ratfunc.int_degree_X
- \+ *lemma* ratfunc.int_degree_add
- \+ *lemma* ratfunc.int_degree_add_le
- \+ *lemma* ratfunc.int_degree_mul
- \+ *lemma* ratfunc.int_degree_neg
- \+ *lemma* ratfunc.int_degree_one
- \+ *lemma* ratfunc.int_degree_polynomial
- \+ *lemma* ratfunc.int_degree_zero
- \+ *lemma* ratfunc.nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree
- \+ *lemma* ratfunc.num_denom_neg
- \+ *lemma* ratfunc.num_mul_denom_add_denom_mul_num_ne_zero

Modified src/number_theory/function_field.lean
- \+ *lemma* function_field.infty_valuation.C
- \+ *lemma* function_field.infty_valuation.X
- \+ *lemma* function_field.infty_valuation.map_add_le_max'
- \+ *lemma* function_field.infty_valuation.map_mul'
- \+ *lemma* function_field.infty_valuation.map_one'
- \+ *lemma* function_field.infty_valuation.map_zero'
- \+ *lemma* function_field.infty_valuation.polynomial
- \+ *def* function_field.infty_valuation
- \+ *lemma* function_field.infty_valuation_apply
- \+ *def* function_field.infty_valuation_def
- \+ *lemma* function_field.infty_valuation_of_nonzero



## [2022-03-14 18:58:33](https://github.com/leanprover-community/mathlib/commit/c1c61d4)
feat(data/W/constructions): add constructions of W types ([#12292](https://github.com/leanprover-community/mathlib/pull/12292))
Here I write the naturals and lists as W-types and show that the definitions are equivalent. Any other interesting examples I should add?
#### Estimated changes
Modified src/data/W/basic.lean


Added src/data/W/constructions.lean
- \+ *def* W_type.equiv_list
- \+ *def* W_type.equiv_nat
- \+ *lemma* W_type.left_inv_list
- \+ *lemma* W_type.left_inv_nat
- \+ *inductive* W_type.list_α
- \+ *def* W_type.list_α_equiv_punit_sum
- \+ *def* W_type.list_β
- \+ *inductive* W_type.nat_α
- \+ *def* W_type.nat_α_equiv_punit_sum_punit
- \+ *def* W_type.nat_β
- \+ *def* W_type.of_list
- \+ *def* W_type.of_nat
- \+ *lemma* W_type.right_inv_list
- \+ *lemma* W_type.right_inv_nat
- \+ *def* W_type.to_list
- \+ *def* W_type.to_nat



## [2022-03-14 17:36:38](https://github.com/leanprover-community/mathlib/commit/2e56210)
chore(analysis/complex/upper_half_plane): don't use `abbreviation` ([#12679](https://github.com/leanprover-community/mathlib/pull/12679))
Some day we should add Poincaré metric as a `metric_space` instance on `upper_half_plane`.
In the meantime, make sure that Lean doesn't use `subtype` instances for `uniform_space` and/or `metric_space`.
#### Estimated changes
Modified src/analysis/complex/upper_half_plane.lean
- \+ *def* upper_half_plane
- \- *abbreviation* upper_half_plane



## [2022-03-14 15:48:03](https://github.com/leanprover-community/mathlib/commit/28775ce)
feat(tactic/interactive): guard_{hyp,target}_mod_implicit ([#12668](https://github.com/leanprover-community/mathlib/pull/12668))
This adds two new tactics `guard_hyp_mod_implicit` and `guard_target_mod_implicit`, with the same syntax as `guard_hyp` and `guard_target`.  While the `guard_*` tactics check for syntax equality, the `guard_*_mod_implicit` tactics check for definitional equality with the `none` transparency
#### Estimated changes
Modified src/tactic/interactive.lean


Added test/mod_implicit.lean




## [2022-03-14 13:59:47](https://github.com/leanprover-community/mathlib/commit/d8ef1de)
feat(topology/separation): add t2_space_iff ([#12628](https://github.com/leanprover-community/mathlib/pull/12628))
From my formalising mathematics 22 course
#### Estimated changes
Modified src/topology/separation.lean




## [2022-03-14 13:59:46](https://github.com/leanprover-community/mathlib/commit/5242a7f)
feat(data/list/infix): add lemmas and instances ([#12511](https://github.com/leanprover-community/mathlib/pull/12511))
#### Estimated changes
Modified src/data/list/infix.lean
- \- *lemma* list.infix.length_le
- \+ *lemma* list.infix_cons_iff
- \+ *lemma* list.is_infix.length_le
- \+ *lemma* list.is_prefix.length_le
- \+ *lemma* list.is_suffix.length_le
- \+ *lemma* list.reverse_infix



## [2022-03-14 13:59:45](https://github.com/leanprover-community/mathlib/commit/df3792f)
refactor(data/set): generalize `set.restrict` and take set argument first in both `set.restrict` and `subtype.restrict` ([#12510](https://github.com/leanprover-community/mathlib/pull/12510))
Generalizes `set.restrict` to Pi types and makes both this function and `subtype.restrict` take the restricting index set before the Pi type to restrict, which makes taking the image/preimage of a set of Pi types easier (`s.restrict '' pis` is shorter than `(λ p, set.restrict p s) '' pis` -- I'd argue that this is the more common case than taking the image of a set of restricting sets on a single Pi type). Changed uses of `set.restrict` to use dot notation where possible.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* category_theory.limits.biproduct.from_subtype
- \+/\- *def* category_theory.limits.biproduct.to_subtype

Modified src/data/set/function.lean
- \+/\- *lemma* set.inj_on_iff_injective
- \+/\- *lemma* set.range_restrict
- \+/\- *def* set.restrict
- \+/\- *lemma* set.restrict_apply
- \+/\- *lemma* set.surj_on_iff_surjective

Modified src/data/subtype.lean
- \+/\- *def* subtype.restrict
- \+/\- *lemma* subtype.restrict_def

Modified src/group_theory/complement.lean


Modified src/measure_theory/measurable_space.lean


Modified src/topology/fiber_bundle.lean
- \+/\- *def* topological_fiber_bundle.pretrivialization.set_symm

Modified src/topology/local_homeomorph.lean




## [2022-03-14 13:59:43](https://github.com/leanprover-community/mathlib/commit/c1edbec)
feat(set_theory/ordinal_topology): Basic results on the order topology of ordinals ([#11861](https://github.com/leanprover-community/mathlib/pull/11861))
We link together various notions about ordinals to their topological counterparts.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.is_normal.sup

Added src/set_theory/ordinal_topology.lean
- \+ *theorem* ordinal.enum_ord_is_normal_iff_is_closed
- \+ *theorem* ordinal.is_closed_iff_bsup
- \+ *theorem* ordinal.is_closed_iff_sup
- \+ *theorem* ordinal.is_limit_of_mem_frontier
- \+ *theorem* ordinal.is_normal_iff_strict_mono_and_continuous
- \+ *theorem* ordinal.is_open_iff
- \+ *theorem* ordinal.is_open_singleton_iff
- \+ *theorem* ordinal.mem_closed_iff_bsup
- \+ *theorem* ordinal.mem_closed_iff_sup
- \+ *theorem* ordinal.mem_closure_iff_bsup
- \+ *theorem* ordinal.mem_closure_iff_sup



## [2022-03-14 12:19:21](https://github.com/leanprover-community/mathlib/commit/09ea7fb)
feat(data/finset/noncomm_prod): finite pi lemmas ([#12291](https://github.com/leanprover-community/mathlib/pull/12291))
including a few helpers
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.mul_single_apply_commute
- \+ *lemma* pi.mul_single_commute

Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_eq_pow_card
- \+ *lemma* finset.noncomm_prod_map
- \+ *lemma* finset.noncomm_prod_mul_single
- \+ *lemma* monoid_hom.pi_ext
- \+ *lemma* multiset.nocomm_prod_map_aux
- \+ *lemma* multiset.noncomm_prod_eq_pow_card
- \+ *lemma* multiset.noncomm_prod_map



## [2022-03-14 11:12:21](https://github.com/leanprover-community/mathlib/commit/fc882ff)
chore(ci): update trepplein to version 1.1 ([#12669](https://github.com/leanprover-community/mathlib/pull/12669))
New upstream release, fixing some performance issues.
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2022-03-14 11:12:20](https://github.com/leanprover-community/mathlib/commit/abb8e5d)
feat(set_theory/principal): If `a` isn't additive principal, it's the sum of two smaller ordinals ([#12664](https://github.com/leanprover-community/mathlib/pull/12664))
#### Estimated changes
Modified src/set_theory/principal.lean
- \+ *theorem* ordinal.exists_lt_add_of_not_principal_add
- \+ *theorem* ordinal.principal_add_iff_add_lt_ne_self



## [2022-03-14 11:12:19](https://github.com/leanprover-community/mathlib/commit/cc6e2eb)
feat(group_theory/commutator): The three subgroups lemma ([#12634](https://github.com/leanprover-community/mathlib/pull/12634))
This PR proves the three subgroups lemma: If `⁅⁅H₂, H₃⁆, H₁⁆ = ⊥` and `⁅⁅H₃, H₁⁆, H₂⁆ = ⊥`, then `⁅⁅H₁, H₂⁆, H₃⁆ = ⊥`.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+ *lemma* subgroup.commutator_commutator_eq_bot_of_rotate



## [2022-03-14 11:12:18](https://github.com/leanprover-community/mathlib/commit/6a51706)
chore(topology/homotopy): Move more algebraic-flavored content about fundamental groupoid to algebraic_topology folder ([#12631](https://github.com/leanprover-community/mathlib/pull/12631))
Moved:
  - `topology/homotopy/fundamental_groupoid.lean` to `algebraic_topology/fundamental_groupoid/basic.lean`
  - the second half of `topology/homotopy/product.lean`, dealing with `fundamental_groupoid_functor` preserving products, to `algebraic_topology/fundamental_groupoid/product.lean`
  - `topology/homotopy/induced_maps.lean` to `algebraic_topology/fundamental_groupoid/induced_maps.lean`
#### Estimated changes
Renamed src/topology/homotopy/fundamental_groupoid.lean to src/algebraic_topology/fundamental_groupoid/basic.lean


Renamed src/topology/homotopy/induced_maps.lean to src/algebraic_topology/fundamental_groupoid/induced_maps.lean


Added src/algebraic_topology/fundamental_groupoid/product.lean
- \+ *def* fundamental_groupoid_functor.cone_discrete_comp
- \+ *lemma* fundamental_groupoid_functor.cone_discrete_comp_obj_map_cone
- \+ *def* fundamental_groupoid_functor.pi_Top_to_pi_cone
- \+ *def* fundamental_groupoid_functor.pi_iso
- \+ *def* fundamental_groupoid_functor.pi_to_pi_Top
- \+ *def* fundamental_groupoid_functor.preserves_product
- \+ *def* fundamental_groupoid_functor.prod_iso
- \+ *def* fundamental_groupoid_functor.prod_to_prod_Top
- \+ *lemma* fundamental_groupoid_functor.prod_to_prod_Top_map
- \+ *def* fundamental_groupoid_functor.proj
- \+ *def* fundamental_groupoid_functor.proj_left
- \+ *lemma* fundamental_groupoid_functor.proj_left_map
- \+ *lemma* fundamental_groupoid_functor.proj_map
- \+ *def* fundamental_groupoid_functor.proj_right
- \+ *lemma* fundamental_groupoid_functor.proj_right_map

Modified src/topology/homotopy/product.lean
- \- *def* fundamental_groupoid_functor.cone_discrete_comp
- \- *lemma* fundamental_groupoid_functor.cone_discrete_comp_obj_map_cone
- \- *def* fundamental_groupoid_functor.pi_Top_to_pi_cone
- \- *def* fundamental_groupoid_functor.pi_iso
- \- *def* fundamental_groupoid_functor.pi_to_pi_Top
- \- *def* fundamental_groupoid_functor.preserves_product
- \- *def* fundamental_groupoid_functor.prod_iso
- \- *def* fundamental_groupoid_functor.prod_to_prod_Top
- \- *lemma* fundamental_groupoid_functor.prod_to_prod_Top_map
- \- *def* fundamental_groupoid_functor.proj
- \- *def* fundamental_groupoid_functor.proj_left
- \- *lemma* fundamental_groupoid_functor.proj_left_map
- \- *lemma* fundamental_groupoid_functor.proj_map
- \- *def* fundamental_groupoid_functor.proj_right
- \- *lemma* fundamental_groupoid_functor.proj_right_map



## [2022-03-14 09:29:31](https://github.com/leanprover-community/mathlib/commit/a2544de)
chore(algebra/category/Module): simp lemmas for monoidal closed ([#12608](https://github.com/leanprover-community/mathlib/pull/12608))
I'm worried by the fact that I can't express the coercions here without using `@`. They do turn up in the wild, however!
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+ *lemma* Module.monoidal_closed_curry
- \+ *lemma* Module.monoidal_closed_uncurry



## [2022-03-14 09:29:29](https://github.com/leanprover-community/mathlib/commit/31e60c8)
feat(set_theory/{ordinal, ordinal_arithmetic}): Add various instances for `o.out.α` ([#12508](https://github.com/leanprover-community/mathlib/pull/12508))
#### Estimated changes
Modified src/measure_theory/card_measurable_space.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/ordinal.lean
- \+ *lemma* ordinal.enum_le_enum'
- \+ *theorem* ordinal.enum_zero_eq_bot
- \+ *theorem* ordinal.enum_zero_le'
- \+ *theorem* ordinal.enum_zero_le
- \+ *theorem* ordinal.le_enum_succ
- \+ *theorem* ordinal.lt_succ
- \+ *def* ordinal.out_order_bot_of_pos
- \+ *lemma* ordinal.typein_le_typein'

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.enum_succ_eq_top
- \- *lemma* ordinal.has_succ_of_is_limit
- \+ *lemma* ordinal.has_succ_of_type_succ_lt
- \- *theorem* ordinal.lt_succ
- \+ *theorem* ordinal.out_no_max_of_succ_lt



## [2022-03-14 09:29:27](https://github.com/leanprover-community/mathlib/commit/1f428f3)
feat(data/list/basic): Split and intercalate are inverses ([#12466](https://github.com/leanprover-community/mathlib/pull/12466))
Show that split and intercalate are inverses of each other (under suitable conditions)
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.intercalate_split_on
- \+ *lemma* list.modify_head_modify_head
- \+ *lemma* list.split_on_intercalate
- \+/\- *lemma* list.split_on_p_aux_eq
- \+ *lemma* list.split_on_p_aux_ne_nil
- \+/\- *lemma* list.split_on_p_aux_nil
- \+ *lemma* list.split_on_p_aux_spec
- \+ *lemma* list.split_on_p_cons
- \+ *lemma* list.split_on_p_eq_single
- \+ *lemma* list.split_on_p_first
- \+ *lemma* list.split_on_p_ne_nil
- \+ *lemma* list.split_on_p_nil
- \+/\- *lemma* list.split_on_p_spec



## [2022-03-14 09:29:26](https://github.com/leanprover-community/mathlib/commit/cd001b2)
feat(category_theory/bicategory/free): define free bicategories ([#11998](https://github.com/leanprover-community/mathlib/pull/11998))
#### Estimated changes
Added src/category_theory/bicategory/free.lean
- \+ *lemma* category_theory.free_bicategory.comp_def
- \+ *inductive* category_theory.free_bicategory.hom
- \+ *inductive* category_theory.free_bicategory.hom₂
- \+ *lemma* category_theory.free_bicategory.id_def
- \+ *def* category_theory.free_bicategory.lift
- \+ *def* category_theory.free_bicategory.lift_hom
- \+ *lemma* category_theory.free_bicategory.lift_hom_comp
- \+ *lemma* category_theory.free_bicategory.lift_hom_id
- \+ *def* category_theory.free_bicategory.lift_hom₂
- \+ *lemma* category_theory.free_bicategory.lift_hom₂_congr
- \+ *lemma* category_theory.free_bicategory.mk_associator_hom
- \+ *lemma* category_theory.free_bicategory.mk_associator_inv
- \+ *lemma* category_theory.free_bicategory.mk_id
- \+ *lemma* category_theory.free_bicategory.mk_left_unitor_hom
- \+ *lemma* category_theory.free_bicategory.mk_left_unitor_inv
- \+ *lemma* category_theory.free_bicategory.mk_right_unitor_hom
- \+ *lemma* category_theory.free_bicategory.mk_right_unitor_inv
- \+ *lemma* category_theory.free_bicategory.mk_vcomp
- \+ *lemma* category_theory.free_bicategory.mk_whisker_left
- \+ *lemma* category_theory.free_bicategory.mk_whisker_right
- \+ *def* category_theory.free_bicategory.of
- \+ *inductive* category_theory.free_bicategory.rel
- \+ *def* category_theory.free_bicategory



## [2022-03-14 08:31:44](https://github.com/leanprover-community/mathlib/commit/520f204)
feat(analysis/seminorm): add lemmas for inequalities and `finset.sup` ([#12650](https://github.com/leanprover-community/mathlib/pull/12650))
These lemmas are not lean-trivial since seminorms map to the `real` and not to `nnreal`.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.finset_sup_apply_le
- \+ *lemma* seminorm.finset_sup_apply_lt



## [2022-03-14 08:31:43](https://github.com/leanprover-community/mathlib/commit/0f3bfda)
feat(analysis/complex/schwarz): some versions of the Schwarz lemma ([#12633](https://github.com/leanprover-community/mathlib/pull/12633))
#### Estimated changes
Modified src/analysis/calculus/dslope.lean
- \+ *lemma* continuous_linear_map.dslope_comp

Modified src/analysis/complex/removable_singularity.lean


Added src/analysis/complex/schwarz.lean
- \+ *lemma* complex.abs_deriv_le_div_of_maps_to_ball
- \+ *lemma* complex.abs_deriv_le_one_of_maps_to_ball
- \+ *lemma* complex.abs_le_abs_of_maps_to_ball_self
- \+ *lemma* complex.dist_le_dist_of_maps_to_ball_self
- \+ *lemma* complex.dist_le_div_mul_dist_of_maps_to_ball
- \+ *lemma* complex.norm_deriv_le_div_of_maps_to_ball
- \+ *lemma* complex.norm_dslope_le_div_of_maps_to_ball
- \+ *lemma* complex.schwarz_aux

Modified src/linear_algebra/affine_space/slope.lean
- \+ *lemma* affine_map.slope_comp
- \+ *lemma* linear_map.slope_comp



## [2022-03-14 08:31:42](https://github.com/leanprover-community/mathlib/commit/c2368be)
feat(topology/hom/open): Continuous open maps ([#12406](https://github.com/leanprover-community/mathlib/pull/12406))
Define `continuous_open_map`, the type of continuous opens maps between two topological spaces, and `continuous_open_map_class`, its companion hom class.
#### Estimated changes
Added src/topology/hom/open.lean
- \+ *lemma* continuous_open_map.cancel_left
- \+ *lemma* continuous_open_map.cancel_right
- \+ *lemma* continuous_open_map.coe_comp
- \+ *lemma* continuous_open_map.coe_id
- \+ *def* continuous_open_map.comp
- \+ *lemma* continuous_open_map.comp_apply
- \+ *lemma* continuous_open_map.comp_assoc
- \+ *lemma* continuous_open_map.comp_id
- \+ *lemma* continuous_open_map.ext
- \+ *lemma* continuous_open_map.id_apply
- \+ *lemma* continuous_open_map.id_comp
- \+ *lemma* continuous_open_map.to_fun_eq_coe
- \+ *structure* continuous_open_map



## [2022-03-14 07:05:57](https://github.com/leanprover-community/mathlib/commit/7b7fea5)
refactor(set_theory/cardinal_ordinal): `aleph_is_principal_aleph` → `principal_add_aleph` ([#12663](https://github.com/leanprover-community/mathlib/pull/12663))
This matches the naming scheme used throughout `set_theory/principal.lean`.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \- *theorem* cardinal.aleph_is_principal_add
- \- *theorem* cardinal.ord_is_principal_add
- \+ *theorem* cardinal.principal_add_aleph
- \+ *theorem* cardinal.principal_add_ord



## [2022-03-14 07:05:56](https://github.com/leanprover-community/mathlib/commit/6ebb378)
feat(set_theory/ordinal): `ord 1 = 1` ([#12662](https://github.com/leanprover-community/mathlib/pull/12662))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* cardinal.ord_one



## [2022-03-14 07:05:55](https://github.com/leanprover-community/mathlib/commit/18ba395)
feat(algebra/support) support of power is subset of support ([#12654](https://github.com/leanprover-community/mathlib/pull/12654))
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.mul_support_pow



## [2022-03-14 07:05:54](https://github.com/leanprover-community/mathlib/commit/6b3b567)
chore(topology/algebra/group_with_zero): fix docstring for has_continuous_inv0 ([#12653](https://github.com/leanprover-community/mathlib/pull/12653))
#### Estimated changes
Modified src/topology/algebra/group_with_zero.lean


Modified src/topology/instances/nnreal.lean




## [2022-03-14 07:05:53](https://github.com/leanprover-community/mathlib/commit/1f5950a)
feat(analysis/seminorm): add lemmas for `with_seminorms` ([#12649](https://github.com/leanprover-community/mathlib/pull/12649))
Two helper lemmas that make it easier to generate an instance for `with_seminorms`.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.with_seminorms_of_has_basis
- \+ *lemma* seminorm.with_seminorms_of_nhds



## [2022-03-14 07:05:51](https://github.com/leanprover-community/mathlib/commit/b6fa3be)
move(topology/sets/*): Move topological types of sets together ([#12648](https://github.com/leanprover-community/mathlib/pull/12648))
Move
* `topology.opens` to `topology.sets.opens`
* `topology.compacts` to `topology.sets.closeds` and `topology.sets.compacts`
`closeds` and `clopens` go into `topology.sets.closeds` and `compacts`, `nonempty_compacts`, `positive_compacts` and `compact_opens` go into `topology.sets.compacts`.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/category_theory/sites/spaces.lean


Modified src/measure_theory/measure/content.lean


Modified src/order/category/Frame.lean


Modified src/topology/alexandroff.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/kuratowski.lean


Added src/topology/sets/closeds.lean
- \+ *lemma* topological_space.clopens.clopen
- \+ *lemma* topological_space.clopens.coe_bot
- \+ *lemma* topological_space.clopens.coe_compl
- \+ *lemma* topological_space.clopens.coe_inf
- \+ *lemma* topological_space.clopens.coe_mk
- \+ *lemma* topological_space.clopens.coe_sdiff
- \+ *lemma* topological_space.clopens.coe_sup
- \+ *lemma* topological_space.clopens.coe_top
- \+ *def* topological_space.clopens.to_opens
- \+ *structure* topological_space.clopens
- \+ *lemma* topological_space.closeds.closed
- \+ *lemma* topological_space.closeds.coe_bot
- \+ *lemma* topological_space.closeds.coe_inf
- \+ *lemma* topological_space.closeds.coe_mk
- \+ *lemma* topological_space.closeds.coe_sup
- \+ *lemma* topological_space.closeds.coe_top
- \+ *structure* topological_space.closeds

Renamed src/topology/compacts.lean to src/topology/sets/compacts.lean
- \- *lemma* topological_space.clopens.clopen
- \- *lemma* topological_space.clopens.coe_bot
- \- *lemma* topological_space.clopens.coe_compl
- \- *lemma* topological_space.clopens.coe_inf
- \- *lemma* topological_space.clopens.coe_mk
- \- *lemma* topological_space.clopens.coe_sdiff
- \- *lemma* topological_space.clopens.coe_sup
- \- *lemma* topological_space.clopens.coe_top
- \- *def* topological_space.clopens.to_opens
- \- *structure* topological_space.clopens
- \- *lemma* topological_space.closeds.closed
- \- *lemma* topological_space.closeds.coe_bot
- \- *lemma* topological_space.closeds.coe_inf
- \- *lemma* topological_space.closeds.coe_mk
- \- *lemma* topological_space.closeds.coe_sup
- \- *lemma* topological_space.closeds.coe_top
- \- *structure* topological_space.closeds

Renamed src/topology/opens.lean to src/topology/sets/opens.lean




## [2022-03-14 07:05:50](https://github.com/leanprover-community/mathlib/commit/778dfd5)
chore(analysis/locally_convex/basic): generalize lemmas and add simple lemmas  ([#12643](https://github.com/leanprover-community/mathlib/pull/12643))
Gerenalize all 'simple' lemmas for `absorb` and `absorbent` to the type-class `[semi_normed_ring 𝕜] [has_scalar 𝕜 E]`.
Additionally, add the lemmas `absorbs_empty`, `balanced_mem` and `zero_singleton_balanced`.
#### Estimated changes
Modified src/analysis/locally_convex/basic.lean
- \+ *lemma* absorbs_empty
- \+ *lemma* balanced_mem
- \+ *lemma* zero_singleton_balanced



## [2022-03-14 07:05:49](https://github.com/leanprover-community/mathlib/commit/f8d947c)
add endofunctor.algebra ([#12642](https://github.com/leanprover-community/mathlib/pull/12642))
This is the second attempt at the following outdated pull request: https://github.com/leanprover-community/mathlib/pull/12295
The original post:
In this PR I define algebras of endofunctors, make the forgetful functor to the ambient category, and show that initial algebras have isomorphisms as their structure maps. This is mostly taken from `monad.algebra`.
#### Estimated changes
Added src/category_theory/endofunctor/algebra.lean
- \+ *lemma* category_theory.endofunctor.algebra.comp_eq_comp
- \+ *lemma* category_theory.endofunctor.algebra.comp_f
- \+ *def* category_theory.endofunctor.algebra.equiv_of_nat_iso
- \+ *def* category_theory.endofunctor.algebra.forget
- \+ *def* category_theory.endofunctor.algebra.functor_of_nat_trans
- \+ *def* category_theory.endofunctor.algebra.functor_of_nat_trans_comp
- \+ *def* category_theory.endofunctor.algebra.functor_of_nat_trans_eq
- \+ *def* category_theory.endofunctor.algebra.functor_of_nat_trans_id
- \+ *def* category_theory.endofunctor.algebra.hom.comp
- \+ *def* category_theory.endofunctor.algebra.hom.id
- \+ *structure* category_theory.endofunctor.algebra.hom
- \+ *lemma* category_theory.endofunctor.algebra.id_eq_id
- \+ *lemma* category_theory.endofunctor.algebra.id_f
- \+ *lemma* category_theory.endofunctor.algebra.initial.left_inv'
- \+ *lemma* category_theory.endofunctor.algebra.initial.left_inv
- \+ *lemma* category_theory.endofunctor.algebra.initial.right_inv
- \+ *def* category_theory.endofunctor.algebra.initial.str_inv
- \+ *lemma* category_theory.endofunctor.algebra.initial.str_is_iso
- \+ *def* category_theory.endofunctor.algebra.iso_mk
- \+ *lemma* category_theory.endofunctor.algebra.iso_of_iso
- \+ *structure* category_theory.endofunctor.algebra



## [2022-03-14 05:19:50](https://github.com/leanprover-community/mathlib/commit/174f1da)
refactor(set_theory/ordinal_arithmetic): Turn various results into simp lemmas ([#12661](https://github.com/leanprover-community/mathlib/pull/12661))
In order to do this, we had to change the direction of various equalities.
#### Estimated changes
Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.blsub_eq_lsub'
- \+/\- *theorem* ordinal.blsub_eq_lsub
- \+ *theorem* ordinal.bsup_eq_blsub
- \+/\- *theorem* ordinal.bsup_eq_sup'
- \+/\- *theorem* ordinal.bsup_eq_sup
- \+/\- *theorem* ordinal.lsub_eq_blsub'
- \+/\- *theorem* ordinal.lsub_eq_blsub
- \+/\- *theorem* ordinal.sup_eq_bsup'
- \+/\- *theorem* ordinal.sup_eq_bsup
- \+ *theorem* ordinal.sup_eq_lsub



## [2022-03-14 05:19:49](https://github.com/leanprover-community/mathlib/commit/ad0988b)
docs(algebra/*): Add docstrings to additive lemmas ([#12578](https://github.com/leanprover-community/mathlib/pull/12578))
Many additive lemmas had no docstrings while their multiplicative counterparts had. This adds them in all files under `algebra`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_ite_eq'
- \- *lemma* finset.sum_comp

Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* exists_ne_one_of_finprod_mem_ne_one
- \+/\- *lemma* finprod_comp
- \+/\- *lemma* finprod_div_distrib
- \+/\- *lemma* finprod_emb_domain'
- \+/\- *lemma* finprod_eq_of_bijective
- \+/\- *lemma* finprod_induction
- \+/\- *lemma* finprod_mem_Union
- \+/\- *lemma* finprod_mem_bUnion
- \+/\- *lemma* finprod_mem_comm
- \+/\- *lemma* finprod_mem_div_distrib
- \+/\- *lemma* finprod_mem_dvd
- \+/\- *lemma* finprod_mem_empty
- \+/\- *lemma* finprod_mem_eq_of_bij_on
- \+/\- *lemma* finprod_mem_finset_product'
- \+/\- *lemma* finprod_mem_finset_product
- \+/\- *lemma* finprod_mem_image'
- \+/\- *lemma* finprod_mem_image
- \- *lemma* finprod_mem_induction
- \+/\- *lemma* finprod_mem_insert'
- \+/\- *lemma* finprod_mem_insert
- \+/\- *lemma* finprod_mem_insert_of_eq_one_if_not_mem
- \+/\- *lemma* finprod_mem_insert_one
- \+/\- *lemma* finprod_mem_mul_diff'
- \+/\- *lemma* finprod_mem_mul_diff
- \+/\- *lemma* finprod_mem_mul_distrib'
- \+/\- *lemma* finprod_mem_mul_distrib
- \+/\- *lemma* finprod_mem_of_eq_on_one
- \+/\- *lemma* finprod_mem_one
- \+/\- *lemma* finprod_mem_pair
- \+/\- *lemma* finprod_mem_range'
- \+/\- *lemma* finprod_mem_range
- \+/\- *lemma* finprod_mem_sUnion
- \+/\- *lemma* finprod_mem_singleton
- \+/\- *lemma* finprod_mem_union''
- \+/\- *lemma* finprod_mem_union'
- \+/\- *lemma* finprod_mem_union
- \- *lemma* finprod_mem_union_inter'
- \+/\- *lemma* finprod_mem_union_inter
- \+/\- *lemma* finprod_mul_distrib
- \+/\- *lemma* finsum_mul
- \+/\- *lemma* finsum_smul
- \+/\- *lemma* monoid_hom.map_finprod_mem'
- \+/\- *lemma* monoid_hom.map_finprod_mem
- \+/\- *lemma* mul_finsum
- \+/\- *lemma* nonempty_of_finprod_mem_ne_one

Modified src/algebra/big_operators/nat_antidiagonal.lean


Modified src/algebra/big_operators/ring.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Mon/limits.lean


Modified src/algebra/group/commute.lean
- \+ *lemma* commute.mul_left
- \- *theorem* commute.mul_left
- \+ *lemma* commute.mul_right
- \- *theorem* commute.mul_right

Modified src/algebra/group/freiman.lean


Modified src/algebra/group/hom.lean
- \+/\- *lemma* map_div

Modified src/algebra/group/semiconj.lean
- \+/\- *lemma* semiconj_by.conj_mk
- \+/\- *lemma* semiconj_by.mul_left
- \+/\- *lemma* semiconj_by.mul_right
- \+/\- *lemma* semiconj_by.units_inv_right
- \+/\- *lemma* semiconj_by.units_inv_symm_left

Modified src/algebra/group/units.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/indicator_function.lean
- \+/\- *lemma* set.mem_of_mul_indicator_ne_one
- \+/\- *lemma* set.prod_mul_indicator_subset

Modified src/algebra/order/group.lean
- \+/\- *lemma* abs_eq_sup_inv

Modified src/algebra/order/hom/monoid.lean


Modified src/algebra/order/lattice_group.lean
- \- *lemma* lattice_ordered_comm_group.m_abs_abs
- \+ *lemma* lattice_ordered_comm_group.mabs_mabs

Modified src/algebra/order/monoid_lemmas.lean


Modified src/algebra/pointwise.lean




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
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* linear_isometry.extend_apply



## [2022-03-14 02:40:00](https://github.com/leanprover-community/mathlib/commit/3751ec6)
feat(measure_theory/group/fundamental_domain): ess_sup_measure_restrict ([#12603](https://github.com/leanprover-community/mathlib/pull/12603))
If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as that of `f` on all of its domain.
#### Estimated changes
Modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_eq_Inf
- \+ *lemma* ess_sup_mono_measure'

Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.ess_sup_measure_restrict
- \+ *lemma* measure_theory.is_fundamental_domain.measure_zero_of_invariant



## [2022-03-13 14:52:04](https://github.com/leanprover-community/mathlib/commit/223e742)
feat(analysis/*/{exponential, spectrum}): spectrum of a selfadjoint element is real ([#12417](https://github.com/leanprover-community/mathlib/pull/12417))
This provides several properties of the exponential function and uses it to prove that for `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜 𝕜` maps the spectrum of `a : A` (where `A` is a `𝕜`-algebra) into the spectrum of `exp 𝕜 A a`. In addition, `exp ℂ A (I • a)` is unitary when `a` is selfadjoint. Consequently, the spectrum of a selfadjoint element is real.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *def* algebra_map_clm
- \+ *lemma* algebra_map_clm_coe
- \+ *lemma* algebra_map_clm_to_linear_map

Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* algebra_map_exp_comm
- \+ *lemma* algebra_map_exp_comm_of_mem_ball
- \+ *lemma* star_exp

Modified src/analysis/normed_space/spectrum.lean
- \+ *theorem* spectrum.exp_mem_exp

Added src/analysis/normed_space/star/exponential.lean
- \+ *lemma* commute.exp_unitary
- \+ *lemma* commute.exp_unitary_add
- \+ *lemma* self_adjoint.exp_i_smul_unitary

Modified src/analysis/normed_space/star/spectrum.lean
- \+ *theorem* self_adjoint.coe_re_map_spectrum'
- \+ *theorem* self_adjoint.coe_re_map_spectrum
- \+ *theorem* self_adjoint.mem_spectrum_eq_re'
- \+ *theorem* self_adjoint.mem_spectrum_eq_re
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+/\- *lemma* spectral_radius_eq_nnnorm_of_star_normal



## [2022-03-13 13:32:14](https://github.com/leanprover-community/mathlib/commit/7d34f78)
chore(algebra/algebra/subalgebra): reduce imports ([#12636](https://github.com/leanprover-community/mathlib/pull/12636))
Splitting a file, and reducing imports. No change in contents.
#### Estimated changes
Renamed src/algebra/algebra/subalgebra.lean to src/algebra/algebra/subalgebra/basic.lean
- \- *lemma* subalgebra.coe_pointwise_smul
- \- *theorem* subalgebra.mul_self
- \- *lemma* subalgebra.pointwise_smul_to_submodule
- \- *lemma* subalgebra.pointwise_smul_to_subring
- \- *lemma* subalgebra.pointwise_smul_to_subsemiring
- \- *lemma* subalgebra.smul_mem_pointwise_smul

Added src/algebra/algebra/subalgebra/pointwise.lean
- \+ *lemma* subalgebra.coe_pointwise_smul
- \+ *theorem* subalgebra.mul_self
- \+ *lemma* subalgebra.pointwise_smul_to_submodule
- \+ *lemma* subalgebra.pointwise_smul_to_subring
- \+ *lemma* subalgebra.pointwise_smul_to_subsemiring
- \+ *lemma* subalgebra.smul_mem_pointwise_smul

Modified src/algebra/algebra/tower.lean


Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/direct_sum/internal.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/lie/of_associative.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/tensor_algebra/basic.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/polynomial/symmetric.lean


Modified src/topology/algebra/algebra.lean


Modified src/topology/continuous_function/algebra.lean




## [2022-03-13 07:59:44](https://github.com/leanprover-community/mathlib/commit/daa257f)
feat(analysis/normed_space/star/basic): `matrix.entrywise_sup_norm_star_eq_norm` ([#12201](https://github.com/leanprover-community/mathlib/pull/12201))
This is precisely the statement needed for a `normed_star_monoid`
instance on matrices using the entrywise sup norm.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* matrix.norm_entry_le_entrywise_sup_norm

Modified src/analysis/normed_space/star/basic.lean
- \+ *lemma* matrix.entrywise_sup_norm_star_eq_norm



## [2022-03-13 04:14:17](https://github.com/leanprover-community/mathlib/commit/73530b5)
feat(algebra/algebra/spectrum): prove spectral inclusion for algebra homomorphisms ([#12573](https://github.com/leanprover-community/mathlib/pull/12573))
If `φ : A →ₐ[R] B` is an `R`-algebra homomorphism, then for any `a : A`, `spectrum R (φ a) ⊆ spectrum R a`.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* alg_hom.mem_resolvent_set_apply
- \+ *lemma* alg_hom.spectrum_apply_subset



## [2022-03-13 00:04:24](https://github.com/leanprover-community/mathlib/commit/9f1f8c1)
feat(ring_theory/graded_algebra/homogeneous_ideal): definition of irrelevant ideal of a graded algebra ([#12548](https://github.com/leanprover-community/mathlib/pull/12548))
For an `ℕ`-graded ring `⨁ᵢ 𝒜ᵢ`, the irrelevant ideal refers to `⨁_{i>0} 𝒜ᵢ`.
This construction is used in the Proj construction in algebraic geometry.
#### Estimated changes
Modified src/ring_theory/graded_algebra/basic.lean
- \+ *def* graded_algebra.proj_zero_ring_hom

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* homogeneous_ideal.coe_irrelevant
- \+ *def* homogeneous_ideal.irrelevant
- \+ *lemma* homogeneous_ideal.mem_irrelevant_iff



## [2022-03-12 21:08:56](https://github.com/leanprover-community/mathlib/commit/5b36941)
feat(data/list/basic): Stronger form of `fold_fixed` ([#12613](https://github.com/leanprover-community/mathlib/pull/12613))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.foldl_fixed'
- \+/\- *theorem* list.foldl_fixed
- \+ *theorem* list.foldr_fixed'
- \+/\- *theorem* list.foldr_fixed



## [2022-03-12 19:48:16](https://github.com/leanprover-community/mathlib/commit/3da03b9)
refactor(group_theory/commutator): Use variables and rearrange lemmas ([#12629](https://github.com/leanprover-community/mathlib/pull/12629))
This PR adds variables, and rearranges some of the lemmas (moving the lemmas about normal subgroups to a separate section).
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+/\- *lemma* subgroup.commutator_bot_left
- \+/\- *lemma* subgroup.commutator_bot_right
- \+/\- *lemma* subgroup.commutator_comm
- \+/\- *lemma* subgroup.commutator_comm_le
- \+/\- *lemma* subgroup.commutator_def'
- \+/\- *lemma* subgroup.commutator_eq_bot_iff_le_centralizer
- \+/\- *lemma* subgroup.commutator_le
- \+/\- *lemma* subgroup.commutator_le_inf
- \+/\- *lemma* subgroup.commutator_le_left
- \+/\- *lemma* subgroup.commutator_le_right
- \+/\- *lemma* subgroup.commutator_mem_commutator
- \+/\- *lemma* subgroup.commutator_mono
- \+/\- *lemma* subgroup.commutator_prod_prod
- \+/\- *lemma* subgroup.map_commutator



## [2022-03-12 18:01:22](https://github.com/leanprover-community/mathlib/commit/23269bf)
feat(category_theory/preadditive/Mat): ring version ([#12617](https://github.com/leanprover-community/mathlib/pull/12617))
#### Estimated changes
Modified src/category_theory/preadditive/Mat.lean
- \+ *lemma* category_theory.Mat.comp_apply
- \+ *lemma* category_theory.Mat.comp_def
- \+ *def* category_theory.Mat.equivalence_single_obj
- \+ *def* category_theory.Mat.equivalence_single_obj_inverse
- \+ *lemma* category_theory.Mat.id_apply
- \+ *lemma* category_theory.Mat.id_apply_of_ne
- \+ *lemma* category_theory.Mat.id_apply_self
- \+ *lemma* category_theory.Mat.id_def
- \+ *def* category_theory.Mat



## [2022-03-12 18:01:21](https://github.com/leanprover-community/mathlib/commit/707df2c)
feat(model_theory/definability): Definability with parameters ([#12611](https://github.com/leanprover-community/mathlib/pull/12611))
Extends the definition of definable sets to include a parameter set.
Defines shorthands is_definable₁ and is_definable₂ for 1- and 2-dimensional definable sets.
#### Estimated changes
Modified src/model_theory/definability.lean
- \+ *lemma* first_order.language.definable.compl
- \+ *lemma* first_order.language.definable.image_comp_equiv
- \+ *lemma* first_order.language.definable.inter
- \+ *lemma* first_order.language.definable.preimage_comp
- \+ *lemma* first_order.language.definable.sdiff
- \+ *lemma* first_order.language.definable.union
- \+ *structure* first_order.language.definable
- \+ *lemma* first_order.language.definable_empty
- \+ *lemma* first_order.language.definable_finset_bInter
- \+ *lemma* first_order.language.definable_finset_bUnion
- \+ *lemma* first_order.language.definable_finset_inf
- \+ *lemma* first_order.language.definable_finset_sup
- \+/\- *lemma* first_order.language.definable_set.coe_bot
- \+/\- *lemma* first_order.language.definable_set.coe_compl
- \+/\- *lemma* first_order.language.definable_set.coe_inf
- \+/\- *lemma* first_order.language.definable_set.coe_sup
- \+/\- *lemma* first_order.language.definable_set.coe_top
- \+/\- *lemma* first_order.language.definable_set.le_iff
- \+/\- *lemma* first_order.language.definable_set.mem_compl
- \+/\- *lemma* first_order.language.definable_set.mem_inf
- \+/\- *lemma* first_order.language.definable_set.mem_sup
- \+/\- *lemma* first_order.language.definable_set.mem_top
- \+/\- *lemma* first_order.language.definable_set.not_mem_bot
- \+/\- *def* first_order.language.definable_set
- \+ *lemma* first_order.language.definable_univ
- \+ *def* first_order.language.definable₁
- \+ *def* first_order.language.definable₂
- \- *lemma* first_order.language.is_definable.compl
- \- *lemma* first_order.language.is_definable.inter
- \- *lemma* first_order.language.is_definable.sdiff
- \- *lemma* first_order.language.is_definable.union
- \- *structure* first_order.language.is_definable
- \- *lemma* first_order.language.is_definable_empty
- \- *lemma* first_order.language.is_definable_univ



## [2022-03-12 18:01:20](https://github.com/leanprover-community/mathlib/commit/9293174)
feat(algebra/category/Module): monoidal_preadditive ([#12607](https://github.com/leanprover-community/mathlib/pull/12607))
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean


Modified src/category_theory/monoidal/preadditive.lean




## [2022-03-12 18:01:19](https://github.com/leanprover-community/mathlib/commit/e4ea2bc)
feat(topology/algebra/continuous_monoid_hom): Define the Pontryagin dual ([#12602](https://github.com/leanprover-community/mathlib/pull/12602))
This PR adds the definition of the Pontryagin dual.
We're still missing the locally compact instance. I thought I could get it from `closed_embedding (to_continuous_map : continuous_monoid_hom A B → C(A, B))`, but actually `C(A, B)` is almost never locally compact.
#### Estimated changes
Modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *def* pontryagin_dual



## [2022-03-12 18:01:18](https://github.com/leanprover-community/mathlib/commit/5a9fb92)
feat(topology/category/Locale): The category of locales ([#12580](https://github.com/leanprover-community/mathlib/pull/12580))
Define `Locale`, the category of locales, as the opposite of `Frame`.
#### Estimated changes
Modified src/order/category/Frame.lean
- \+ *def* Top_op_to_Frame

Added src/topology/category/Locale.lean
- \+ *lemma* Locale.coe_of
- \+ *def* Locale.of
- \+ *def* Locale
- \+ *def* Top_to_Locale

Modified src/topology/opens.lean
- \+ *lemma* topological_space.opens.comap_injective



## [2022-03-12 18:01:17](https://github.com/leanprover-community/mathlib/commit/96bae07)
feat(order/complete_lattice): add `complete_lattice.independent_pair` ([#12565](https://github.com/leanprover-community/mathlib/pull/12565))
This makes `complete_lattice.independent` easier to work with in the degenerate case.
#### Estimated changes
Modified counterexamples/direct_sum_is_internal.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.insert_diff_eq_singleton

Modified src/order/complete_lattice.lean
- \+ *lemma* complete_lattice.independent_pair
- \+ *lemma* complete_lattice.set_independent_pair



## [2022-03-12 16:17:42](https://github.com/leanprover-community/mathlib/commit/7e5ac6a)
chore(analysis/convex/strict): Reduce typeclass assumptions, golf ([#12627](https://github.com/leanprover-community/mathlib/pull/12627))
Move lemmas around so they are stated with the correct generality. Restate theorems using pointwise operations. Golf proofs. Fix typos in docstrings.
#### Estimated changes
Modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex.add
- \+/\- *lemma* strict_convex.add_left
- \+/\- *lemma* strict_convex.add_right
- \+/\- *lemma* strict_convex.affinity
- \+/\- *lemma* strict_convex.linear_image
- \+/\- *lemma* strict_convex.smul
- \+ *lemma* strict_convex.vadd



## [2022-03-12 16:17:41](https://github.com/leanprover-community/mathlib/commit/22bdc8e)
feat(order/upper_lower): Upper/lower sets ([#12189](https://github.com/leanprover-community/mathlib/pull/12189))
Define upper and lower sets both as unbundled predicates and as bundled types.
#### Estimated changes
Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* compl_Inf'
- \+ *lemma* compl_Inf
- \- *theorem* compl_Inf
- \+ *lemma* compl_Sup'
- \+ *lemma* compl_Sup
- \- *theorem* compl_Sup

Added src/order/upper_lower.lean
- \+ *lemma* is_lower_set.compl
- \+ *lemma* is_lower_set.inter
- \+ *lemma* is_lower_set.union
- \+ *def* is_lower_set
- \+ *lemma* is_lower_set_Inter
- \+ *lemma* is_lower_set_Inter₂
- \+ *lemma* is_lower_set_Union
- \+ *lemma* is_lower_set_Union₂
- \+ *lemma* is_lower_set_empty
- \+ *lemma* is_lower_set_preimage_of_dual_iff
- \+ *lemma* is_lower_set_preimage_to_dual_iff
- \+ *lemma* is_lower_set_sInter
- \+ *lemma* is_lower_set_sUnion
- \+ *lemma* is_lower_set_univ
- \+ *lemma* is_upper_set.compl
- \+ *lemma* is_upper_set.inter
- \+ *lemma* is_upper_set.union
- \+ *def* is_upper_set
- \+ *lemma* is_upper_set_Inter
- \+ *lemma* is_upper_set_Inter₂
- \+ *lemma* is_upper_set_Union
- \+ *lemma* is_upper_set_Union₂
- \+ *lemma* is_upper_set_empty
- \+ *lemma* is_upper_set_preimage_of_dual_iff
- \+ *lemma* is_upper_set_preimage_to_dual_iff
- \+ *lemma* is_upper_set_sInter
- \+ *lemma* is_upper_set_sUnion
- \+ *lemma* is_upper_set_univ
- \+ *lemma* lower_set.coe_Inf
- \+ *lemma* lower_set.coe_Sup
- \+ *lemma* lower_set.coe_bot
- \+ *lemma* lower_set.coe_compl
- \+ *lemma* lower_set.coe_inf
- \+ *lemma* lower_set.coe_infi
- \+ *lemma* lower_set.coe_infi₂
- \+ *lemma* lower_set.coe_sup
- \+ *lemma* lower_set.coe_supr
- \+ *lemma* lower_set.coe_supr₂
- \+ *lemma* lower_set.coe_top
- \+ *def* lower_set.compl
- \+ *lemma* lower_set.compl_compl
- \+ *lemma* lower_set.compl_infi₂
- \+ *lemma* lower_set.compl_supr₂
- \+ *lemma* lower_set.ext
- \+ *structure* lower_set
- \+ *lemma* upper_set.coe_Inf
- \+ *lemma* upper_set.coe_Sup
- \+ *lemma* upper_set.coe_bot
- \+ *lemma* upper_set.coe_compl
- \+ *lemma* upper_set.coe_inf
- \+ *lemma* upper_set.coe_infi
- \+ *lemma* upper_set.coe_infi₂
- \+ *lemma* upper_set.coe_sup
- \+ *lemma* upper_set.coe_supr
- \+ *lemma* upper_set.coe_supr₂
- \+ *lemma* upper_set.coe_top
- \+ *def* upper_set.compl
- \+ *lemma* upper_set.compl_compl
- \+ *lemma* upper_set.compl_infi₂
- \+ *lemma* upper_set.compl_supr₂
- \+ *lemma* upper_set.ext
- \+ *structure* upper_set



## [2022-03-12 15:43:41](https://github.com/leanprover-community/mathlib/commit/dc4e5cb)
chore(analysis): move lemmas around ([#12621](https://github.com/leanprover-community/mathlib/pull/12621))
* move `smul_unit_ball` to `analysis.normed_space.pointwise`, rename it to `smul_unit_ball_of_pos`;
* reorder lemmas in `analysis.normed_space.pointwise`;
* add `vadd_ball_zero`, `vadd_closed_ball_zero`, `smul_unit`, `affinity_unit_ball`, `affinity_unit_closed_ball`.
#### Estimated changes
Modified src/analysis/convex/gauge.lean
- \- *lemma* smul_unit_ball

Modified src/analysis/normed_space/pointwise.lean
- \+ *lemma* affinity_unit_ball
- \+ *lemma* affinity_unit_closed_ball
- \+ *lemma* normed_space.sphere_nonempty
- \- *theorem* normed_space.sphere_nonempty
- \+ *lemma* smul_closed_unit_ball
- \+ *lemma* smul_closed_unit_ball_of_nonneg
- \+ *lemma* smul_sphere
- \- *theorem* smul_sphere
- \+ *lemma* smul_unit_ball
- \+ *lemma* smul_unit_ball_of_pos
- \+ *lemma* vadd_ball_zero
- \+ *lemma* vadd_closed_ball_zero



## [2022-03-12 14:08:13](https://github.com/leanprover-community/mathlib/commit/7257ee7)
chore(data/nat/prime): restate card_multiples without finset.sep ([#12625](https://github.com/leanprover-community/mathlib/pull/12625))
As suggested by Eric Wieser in [#12592](https://github.com/leanprover-community/mathlib/pull/12592).
#### Estimated changes
Modified src/data/nat/prime.lean
- \+/\- *lemma* card_multiples



## [2022-03-12 14:08:12](https://github.com/leanprover-community/mathlib/commit/a63b99c)
chore(category_theory/closed/monoidal): fix notation ([#12612](https://github.com/leanprover-community/mathlib/pull/12612))
Previously the `C` in the internal hom arrow ` ⟶[C] ` was hardcoded, which wasn't very useful!
I've also reduced the precedence slightly, so we now require more parentheses, but I think these are less confusing rather than more so it is a good side effect?
#### Estimated changes
Modified src/category_theory/closed/monoidal.lean
- \+/\- *def* category_theory.monoidal_closed.curry
- \+/\- *lemma* category_theory.monoidal_closed.curry_eq_iff
- \+/\- *lemma* category_theory.monoidal_closed.curry_injective
- \+/\- *lemma* category_theory.monoidal_closed.curry_uncurry
- \+/\- *lemma* category_theory.monoidal_closed.eq_curry_iff
- \+/\- *lemma* category_theory.monoidal_closed.hom_equiv_symm_apply_eq
- \+/\- *def* category_theory.monoidal_closed.uncurry
- \+/\- *lemma* category_theory.monoidal_closed.uncurry_eq
- \+/\- *lemma* category_theory.monoidal_closed.uncurry_injective
- \+/\- *lemma* category_theory.monoidal_closed.uncurry_natural_left
- \+/\- *lemma* category_theory.monoidal_closed.uncurry_natural_right



## [2022-03-12 14:08:11](https://github.com/leanprover-community/mathlib/commit/956f3db)
chore(category_theory/limits): correct lemma names ([#12606](https://github.com/leanprover-community/mathlib/pull/12606))
#### Estimated changes
Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.kernel_comparison_comp_ι
- \- *lemma* category_theory.limits.kernel_comparison_comp_π
- \- *lemma* category_theory.limits.ι_comp_cokernel_comparison
- \+ *lemma* category_theory.limits.π_comp_cokernel_comparison



## [2022-03-12 14:08:10](https://github.com/leanprover-community/mathlib/commit/9456a74)
feat(group_theory/commutator): Prove `commutator_eq_bot_iff_le_centralizer` ([#12598](https://github.com/leanprover-community/mathlib/pull/12598))
This lemma is needed for the three subgroups lemma.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+ *lemma* subgroup.commutator_eq_bot_iff_le_centralizer



## [2022-03-12 14:08:09](https://github.com/leanprover-community/mathlib/commit/b9ab27b)
feat(group_theory/subgroup/basic): add eq_one_of_noncomm_prod_eq_one_of_independent ([#12525](https://github.com/leanprover-community/mathlib/pull/12525))
`finset.noncomm_prod` is “injective” in `f` if `f` maps into independent subgroups.  It
generalizes (one direction of) `subgroup.disjoint_iff_mul_eq_one`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.eq_one_of_noncomm_prod_eq_one_of_independent



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
Added src/analysis/locally_convex/basic.lean
- \+ *lemma* absorbent.absorbs
- \+ *lemma* absorbent.subset
- \+ *lemma* absorbent.zero_mem
- \+ *def* absorbent
- \+ *lemma* absorbent_iff_forall_absorbs_singleton
- \+ *lemma* absorbent_iff_nonneg_lt
- \+ *lemma* absorbent_nhds_zero
- \+ *lemma* absorbent_univ
- \+ *lemma* absorbs.inter
- \+ *lemma* absorbs.mono
- \+ *lemma* absorbs.mono_left
- \+ *lemma* absorbs.mono_right
- \+ *lemma* absorbs.union
- \+ *def* absorbs
- \+ *lemma* absorbs_inter
- \+ *lemma* absorbs_union
- \+ *lemma* absorbs_zero_iff
- \+ *lemma* balanced.absorbs_self
- \+ *lemma* balanced.add
- \+ *lemma* balanced.closure
- \+ *lemma* balanced.inter
- \+ *lemma* balanced.interior
- \+ *lemma* balanced.smul
- \+ *lemma* balanced.smul_eq
- \+ *lemma* balanced.smul_mono
- \+ *lemma* balanced.subset_smul
- \+ *lemma* balanced.union
- \+ *def* balanced
- \+ *lemma* balanced_univ
- \+ *lemma* balanced_zero_union_interior

Modified src/analysis/seminorm.lean
- \- *lemma* absorbent.absorbs
- \- *lemma* absorbent.subset
- \- *lemma* absorbent.zero_mem
- \- *def* absorbent
- \- *lemma* absorbent_iff_forall_absorbs_singleton
- \- *lemma* absorbent_iff_nonneg_lt
- \- *lemma* absorbent_nhds_zero
- \- *lemma* absorbent_univ
- \- *lemma* absorbs.inter
- \- *lemma* absorbs.mono
- \- *lemma* absorbs.mono_left
- \- *lemma* absorbs.mono_right
- \- *lemma* absorbs.union
- \- *def* absorbs
- \- *lemma* absorbs_inter
- \- *lemma* absorbs_union
- \- *lemma* absorbs_zero_iff
- \- *lemma* balanced.absorbs_self
- \- *lemma* balanced.add
- \- *lemma* balanced.closure
- \- *lemma* balanced.inter
- \- *lemma* balanced.interior
- \- *lemma* balanced.smul
- \- *lemma* balanced.smul_eq
- \- *lemma* balanced.smul_mono
- \- *lemma* balanced.subset_smul
- \- *lemma* balanced.union
- \- *def* balanced
- \- *lemma* balanced_univ
- \- *lemma* balanced_zero_union_interior



## [2022-03-12 11:37:20](https://github.com/leanprover-community/mathlib/commit/a4187fe)
chore(algebra/category/Module): remove unnecessary universe restriction ([#12610](https://github.com/leanprover-community/mathlib/pull/12610))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+/\- *def* Module.of_hom



## [2022-03-12 11:37:19](https://github.com/leanprover-community/mathlib/commit/31d28c6)
fix(src/algebra/big_operators/multiset): unify prod_le_pow_card and prod_le_of_forall_le ([#12589](https://github.com/leanprover-community/mathlib/pull/12589))
using the name `prod_le_pow_card` as per https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/duplicate.20lemmas
but use the phrasing of prod_le_of_forall_le with non-implicit
`multiset`, as that is how it is used.
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean
- \- *lemma* multiset.prod_le_of_forall_le
- \+/\- *lemma* multiset.prod_le_pow_card

Modified src/algebra/big_operators/order.lean
- \- *lemma* finset.le_prod_of_forall_le
- \+ *lemma* finset.pow_card_le_prod
- \- *lemma* finset.prod_le_of_forall_le
- \+ *lemma* finset.prod_le_pow_card

Modified src/algebra/polynomial/big_operators.lean


Modified src/combinatorics/double_counting.lean


Modified src/data/list/prod_monoid.lean
- \- *lemma* list.prod_le_of_forall_le
- \+ *lemma* list.prod_le_pow_card

Modified src/linear_algebra/matrix/polynomial.lean




## [2022-03-12 11:06:34](https://github.com/leanprover-community/mathlib/commit/2241588)
feat(topology/homotopy): Homotopic maps induce naturally isomorphic functors between fundamental groupoid ([#11595](https://github.com/leanprover-community/mathlib/pull/11595))
#### Estimated changes
Modified src/category_theory/category/Groupoid.lean
- \+ *lemma* category_theory.Groupoid.id_to_functor

Modified src/topology/homotopy/fundamental_groupoid.lean
- \+ *lemma* fundamental_groupoid.map_eq

Added src/topology/homotopy/induced_maps.lean
- \+ *lemma* continuous_map.homotopy.apply_one_path
- \+ *lemma* continuous_map.homotopy.apply_zero_path
- \+ *def* continuous_map.homotopy.diagonal_path'
- \+ *def* continuous_map.homotopy.diagonal_path
- \+ *lemma* continuous_map.homotopy.eq_diag_path
- \+ *lemma* continuous_map.homotopy.eq_path_of_eq_image
- \+ *lemma* continuous_map.homotopy.eval_at_eq
- \+ *abbreviation* continuous_map.homotopy.hcast
- \+ *lemma* continuous_map.homotopy.hcast_def
- \+ *lemma* continuous_map.homotopy.heq_path_of_eq_image
- \+ *abbreviation* continuous_map.homotopy.prod_to_prod_Top_I
- \+ *lemma* continuous_map.homotopy.ulift_apply
- \+ *def* continuous_map.homotopy.ulift_map
- \+ *def* fundamental_groupoid_functor.equiv_of_homotopy_equiv
- \+ *def* fundamental_groupoid_functor.homotopic_maps_nat_iso
- \+ *def* unit_interval.path01
- \+ *def* unit_interval.uhpath01
- \+ *def* unit_interval.upath01

Modified src/topology/homotopy/path.lean
- \+ *def* continuous_map.homotopy.eval_at
- \+ *lemma* path.homotopic.hpath_hext

Modified src/topology/homotopy/product.lean
- \+ *lemma* fundamental_groupoid_functor.prod_to_prod_Top_map



## [2022-03-12 09:57:54](https://github.com/leanprover-community/mathlib/commit/5f3f70f)
doc(category_theory/monoidal/rigid): noting future work ([#12620](https://github.com/leanprover-community/mathlib/pull/12620))
#### Estimated changes
Modified src/category_theory/monoidal/rigid.lean




## [2022-03-12 09:57:53](https://github.com/leanprover-community/mathlib/commit/3d41a5b)
refactor(group_theory/commutator): Golf proof of `commutator_mono` ([#12619](https://github.com/leanprover-community/mathlib/pull/12619))
This PR golfs the proof of `commutator_mono` by using `commutator_le` rather than `closure_mono`.
#### Estimated changes
Modified src/group_theory/commutator.lean




## [2022-03-12 09:57:52](https://github.com/leanprover-community/mathlib/commit/72c6979)
refactor(set_theory/ordinal_arithmetic): remove dot notation ([#12614](https://github.com/leanprover-community/mathlib/pull/12614))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.enum_ord.strict_mono
- \+ *theorem* ordinal.enum_ord_strict_mono



## [2022-03-12 08:36:18](https://github.com/leanprover-community/mathlib/commit/3aaa564)
refactor(group_theory/commutator): Golf proof of `commutator_comm` ([#12600](https://github.com/leanprover-community/mathlib/pull/12600))
This PR golfs the proof of `commutator_comm`.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+ *lemma* subgroup.commutator_comm_le



## [2022-03-12 05:57:32](https://github.com/leanprover-community/mathlib/commit/1463f59)
fix(tactic/suggest): fixing `library_search` ([#12616](https://github.com/leanprover-community/mathlib/pull/12616))
Further enhancing `library_search` search possibilities for 'ne' and 'not eq'
Related: https://github.com/leanprover-community/mathlib/pull/11742
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean
- \+ *structure* test.library_search.foo



## [2022-03-12 05:57:31](https://github.com/leanprover-community/mathlib/commit/e8d0cac)
feat(analysis/inner_product_space/adjoint): gram lemmas ([#12139](https://github.com/leanprover-community/mathlib/pull/12139))
The gram operator is a self-adjoint, positive operator.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* linear_map.im_inner_adjoint_mul_self_eq_zero
- \+ *lemma* linear_map.is_self_adjoint_adjoint_mul_self
- \+ *lemma* linear_map.re_inner_adjoint_mul_self_nonneg



## [2022-03-12 04:22:20](https://github.com/leanprover-community/mathlib/commit/1eaf499)
feat(group_theory/subgroup/basic): {multiset_,}noncomm_prod_mem ([#12523](https://github.com/leanprover-community/mathlib/pull/12523))
and same for submonoids.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.multiset_noncomm_prod_mem
- \+ *lemma* subgroup.noncomm_prod_mem

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* submonoid.multiset_noncomm_prod_mem
- \+ *lemma* submonoid.noncomm_prod_mem



## [2022-03-12 04:22:19](https://github.com/leanprover-community/mathlib/commit/6ee6203)
feat(counterexample) : a homogeneous ideal that is not prime but homogeneously prime ([#12485](https://github.com/leanprover-community/mathlib/pull/12485))
For graded rings, if the indexing set is nice, then a homogeneous ideal `I` is prime if and only if it is homogeneously prime, i.e. product of two homogeneous elements being in `I` implying at least one of them is in `I`. This fact is in `src/ring_theory/graded_algebra/radical.lean`. This counter example is meant to show that "nice condition" at least needs to include cancellation property by exhibiting an ideal in Zmod4^2 graded by a two element set being homogeneously prime but not prime. In [#12277](https://github.com/leanprover-community/mathlib/pull/12277), Eric suggests that this counter example is worth pr-ing, so here is the pr.
#### Estimated changes
Added counterexamples/homogeneous_prime_not_prime.lean
- \+ *def* counterexample_not_prime_but_homogeneous_prime.I
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.I_is_homogeneous
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.I_not_prime
- \+ *def* counterexample_not_prime_but_homogeneous_prime.grading.decompose
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.grading.left_inv
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.grading.mul_mem
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.grading.one_mem
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.grading.right_inv
- \+ *def* counterexample_not_prime_but_homogeneous_prime.grading
- \+ *lemma* counterexample_not_prime_but_homogeneous_prime.homogeneous_mem_or_mem
- \+ *def* counterexample_not_prime_but_homogeneous_prime.submodule_o
- \+ *def* counterexample_not_prime_but_homogeneous_prime.submodule_z
- \+ *abbreviation* counterexample_not_prime_but_homogeneous_prime.two

Modified src/ring_theory/graded_algebra/radical.lean




## [2022-03-12 02:28:54](https://github.com/leanprover-community/mathlib/commit/2e7483d)
refactor(group_theory/commutator): Move and golf `commutator_le` ([#12599](https://github.com/leanprover-community/mathlib/pull/12599))
This PR golfs `commutator_le` and moves it earlier in the file so that it can be used earlier.
This PR will conflict with [#12600](https://github.com/leanprover-community/mathlib/pull/12600), so don't merge them simultaneously (bors d+ might be better).
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+/\- *lemma* subgroup.commutator_le

Modified src/group_theory/nilpotent.lean




## [2022-03-12 02:28:53](https://github.com/leanprover-community/mathlib/commit/09d0f02)
chore({category_theory,order}/category/*): Missing `dsimp` lemmas ([#12593](https://github.com/leanprover-community/mathlib/pull/12593))
Add the `dsimp` lemmas stating `↥(of α) = α `. Also rename the few `to_dual` functors to `dual` to match the other files.
#### Estimated changes
Modified src/category_theory/category/Bipointed.lean
- \+ *lemma* Bipointed.coe_of

Modified src/category_theory/category/PartialFun.lean
- \+ *lemma* PartialFun.coe_of

Modified src/category_theory/category/Pointed.lean
- \+ *lemma* Pointed.coe_of

Modified src/category_theory/category/Twop.lean
- \+ *lemma* Twop.coe_of
- \+ *lemma* Twop.coe_to_Bipointed

Modified src/order/category/BoolAlg.lean
- \+ *lemma* BoolAlg.coe_of

Modified src/order/category/BoundedLattice.lean
- \+ *lemma* BoundedLattice.coe_of

Modified src/order/category/BoundedOrder.lean
- \+ *lemma* BoundedOrder.coe_of

Modified src/order/category/CompleteLattice.lean
- \+ *lemma* CompleteLattice.coe_of

Modified src/order/category/DistribLattice.lean
- \+ *lemma* DistribLattice.coe_of

Modified src/order/category/FinPartialOrder.lean
- \+ *lemma* FinPartialOrder.coe_of

Modified src/order/category/Frame.lean
- \+ *lemma* Frame.coe_of

Modified src/order/category/Lattice.lean
- \+ *lemma* Lattice.coe_of

Modified src/order/category/LinearOrder.lean
- \+ *lemma* LinearOrder.coe_of

Modified src/order/category/NonemptyFinLinOrd.lean
- \+ *lemma* NonemptyFinLinOrd.coe_of
- \+ *def* NonemptyFinLinOrd.dual
- \- *def* NonemptyFinLinOrd.to_dual
- \+ *lemma* NonemptyFinLinOrd_dual_comp_forget_to_LinearOrder
- \- *lemma* NonemptyFinLinOrd_dual_equiv_comp_forget_to_LinearOrder

Modified src/order/category/PartialOrder.lean
- \+ *lemma* PartialOrder.coe_of
- \+ *def* PartialOrder.dual
- \- *def* PartialOrder.to_dual
- \+ *lemma* PartialOrder_dual_comp_forget_to_Preorder
- \- *lemma* PartialOrder_to_dual_comp_forget_to_Preorder

Modified src/order/category/Preorder.lean
- \+ *lemma* Preorder.coe_of
- \+ *def* Preorder.dual
- \- *def* Preorder.to_dual

Modified src/order/category/omega_complete_partial_order.lean
- \+ *lemma* ωCPO.coe_of



## [2022-03-12 02:28:52](https://github.com/leanprover-community/mathlib/commit/4e302f5)
feat(data/nat): add card_multiples ([#12592](https://github.com/leanprover-community/mathlib/pull/12592))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* card_multiples



## [2022-03-12 02:28:51](https://github.com/leanprover-community/mathlib/commit/222faed)
feat(algebra/group/units_hom): make `is_unit.map` work on `monoid_hom_class` ([#12577](https://github.com/leanprover-community/mathlib/pull/12577))
`ring_hom.is_unit_map` and `mv_power_series.is_unit_constant_coeff` are now redundant, but to keep this diff small I've left them around.
#### Estimated changes
Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* is_unit.map

Modified src/algebra/ring/basic.lean


Modified src/algebraic_geometry/Gamma_Spec_adjunction.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/ring_division.lean


Modified src/group_theory/monoid_localization.lean


Modified src/ring_theory/ideal/local_ring.lean


Modified src/ring_theory/localization/away.lean


Modified src/ring_theory/localization/localization_localization.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/power_series/basic.lean




## [2022-03-12 02:28:50](https://github.com/leanprover-community/mathlib/commit/8364980)
feat(category_theory): interderivability of kernel and equalizers in preadditive cats ([#12576](https://github.com/leanprover-community/mathlib/pull/12576))
#### Estimated changes
Modified src/category_theory/idempotents/basic.lean


Modified src/category_theory/preadditive/default.lean
- \+ *def* category_theory.preadditive.cofork_of_cokernel_cofork
- \+ *def* category_theory.preadditive.cokernel_cofork_of_cofork
- \+ *def* category_theory.preadditive.fork_of_kernel_fork
- \+ *lemma* category_theory.preadditive.has_coequalizer_of_has_cokernel
- \+ *lemma* category_theory.preadditive.has_cokernel_of_has_coequalizer
- \- *lemma* category_theory.preadditive.has_colimit_parallel_pair
- \+ *lemma* category_theory.preadditive.has_equalizer_of_has_kernel
- \+/\- *lemma* category_theory.preadditive.has_kernel_of_has_equalizer
- \- *lemma* category_theory.preadditive.has_limit_parallel_pair
- \+ *def* category_theory.preadditive.is_colimit_cofork_of_cokernel_cofork
- \+ *def* category_theory.preadditive.is_colimit_cokernel_cofork_of_cofork
- \+ *def* category_theory.preadditive.is_limit_fork_of_kernel_fork
- \+ *def* category_theory.preadditive.is_limit_kernel_fork_of_fork
- \+ *def* category_theory.preadditive.kernel_fork_of_fork



## [2022-03-11 23:40:59](https://github.com/leanprover-community/mathlib/commit/c0a51cf)
chore(*): update to 3.41.0c ([#12591](https://github.com/leanprover-community/mathlib/pull/12591))
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/monoid_algebra/to_direct_sum.lean
- \+ *def* add_monoid_algebra_add_equiv_direct_sum
- \+ *def* add_monoid_algebra_alg_equiv_direct_sum
- \+ *def* add_monoid_algebra_ring_equiv_direct_sum

Modified src/analysis/convex/cone.lean
- \+ *def* set.inner_dual_cone

Modified src/analysis/normed_space/continuous_affine_map.lean
- \+ *def* continuous_affine_map.to_const_prod_continuous_linear_map

Modified src/analysis/normed_space/linear_isometry.lean
- \+ *def* linear_isometry_equiv.prod_assoc

Modified src/control/lawful_fix.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *def* is_R_or_C.conj_ae
- \+ *def* is_R_or_C.im_lm
- \+ *def* is_R_or_C.re_lm

Modified src/data/finsupp/to_dfinsupp.lean
- \+ *def* finsupp_add_equiv_dfinsupp
- \+ *def* finsupp_lequiv_dfinsupp

Modified src/data/real/ennreal.lean
- \+ *def* ennreal.of_nnreal_hom

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/measure/haar_lebesgue.lean
- \+ *def* topological_space.positive_compacts.Icc01
- \+ *def* topological_space.positive_compacts.pi_Icc01

Modified src/model_theory/direct_limit.lean
- \+ *def* first_order.language.direct_limit.lift
- \+ *def* first_order.language.direct_limit.of

Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *def* mv_polynomial.homogeneous_submodule

Modified src/ring_theory/witt_vector/teichmuller.lean
- \+ *def* witt_vector.teichmuller

Modified src/tactic/slim_check.lean


Modified src/topology/category/Compactum.lean
- \+ *def* Compactum_to_CompHaus.iso_of_topological_space



## [2022-03-11 21:59:23](https://github.com/leanprover-community/mathlib/commit/e7db193)
feat(algebra/module): add `module.nontrivial` ([#12594](https://github.com/leanprover-community/mathlib/pull/12594))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *theorem* module.subsingleton



## [2022-03-11 19:18:32](https://github.com/leanprover-community/mathlib/commit/5856c0c)
feat(data/finset/noncomm_prod): add noncomm_prod_mul_distrib ([#12524](https://github.com/leanprover-community/mathlib/pull/12524))
The non-commutative version of `finset.sum_union`.
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_mul_distrib
- \+ *lemma* finset.noncomm_prod_mul_distrib_aux



## [2022-03-11 19:18:31](https://github.com/leanprover-community/mathlib/commit/dc5f7fb)
feat(set_theory/ordinal_arithmetic): Further theorems on normal functions ([#12484](https://github.com/leanprover-community/mathlib/pull/12484))
We prove various theorems giving more convenient characterizations of normal functions.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.bsup_eq_blsub_of_lt_succ_limit
- \+ *theorem* ordinal.is_normal_iff_lt_succ_and_blsub_eq
- \+ *theorem* ordinal.is_normal_iff_lt_succ_and_bsup_eq
- \+ *theorem* ordinal.is_normal_iff_strict_mono_limit



## [2022-03-11 19:18:30](https://github.com/leanprover-community/mathlib/commit/e3ad468)
feat(data/list/prod_monoid): add prod_eq_pow_card ([#12473](https://github.com/leanprover-community/mathlib/pull/12473))
#### Estimated changes
Modified src/data/list/prod_monoid.lean
- \+ *lemma* list.prod_eq_pow_card



## [2022-03-11 17:31:10](https://github.com/leanprover-community/mathlib/commit/7dcba96)
feat(order/monotone): Folds of monotone functions are monotone ([#12581](https://github.com/leanprover-community/mathlib/pull/12581))
#### Estimated changes
Modified src/order/monotone.lean
- \+ *theorem* list.foldl_monotone
- \+ *theorem* list.foldl_strict_mono
- \+ *theorem* list.foldr_monotone
- \+ *theorem* list.foldr_strict_mono



## [2022-03-11 17:31:09](https://github.com/leanprover-community/mathlib/commit/3dcc168)
feat(linear_algebra/projective_space/basic): The projectivization of a vector space. ([#12438](https://github.com/leanprover-community/mathlib/pull/12438))
This provides the initial definitions for the projective space associated to a vector space.
Future work:
- Linear subspaces of projective spaces, connection with subspaces of the vector space, etc.
- The incidence geometry structure of a projective space.
- The fundamental theorem of projective geometry.
I will tag this PR as RFC for now. If you see something missing from this *initial* PR, please let me know!
#### Estimated changes
Added src/linear_algebra/projective_space/basic.lean
- \+ *def* projectivization.equiv_submodule
- \+ *lemma* projectivization.exists_smul_eq_mk_rep
- \+ *lemma* projectivization.finrank_submodule
- \+ *lemma* projectivization.ind
- \+ *def* projectivization.map
- \+ *lemma* projectivization.map_comp
- \+ *lemma* projectivization.map_id
- \+ *lemma* projectivization.map_injective
- \+ *def* projectivization.mk''
- \+ *lemma* projectivization.mk''_submodule
- \+ *def* projectivization.mk'
- \+ *lemma* projectivization.mk'_eq_mk
- \+ *def* projectivization.mk
- \+ *lemma* projectivization.mk_eq_mk_iff
- \+ *lemma* projectivization.mk_rep
- \+ *lemma* projectivization.rep_nonzero
- \+ *lemma* projectivization.submodule_eq
- \+ *lemma* projectivization.submodule_injective
- \+ *lemma* projectivization.submodule_mk''
- \+ *lemma* projectivization.submodule_mk
- \+ *def* projectivization
- \+ *def* projectivization_setoid



## [2022-03-11 16:25:21](https://github.com/leanprover-community/mathlib/commit/003701f)
feat(model_theory/substructures): Facts about substructures ([#12258](https://github.com/leanprover-community/mathlib/pull/12258))
Shows that `closure L s` can be viewed as the set of realizations of terms over `s`.
Bounds the cardinality of `closure L s` by the cardinality of the type of terms.
Characterizes `closure L[[A]] s`.
#### Estimated changes
Modified src/model_theory/substructures.lean
- \+ *lemma* first_order.language.Lhom.coe_substructure_reduct
- \+ *lemma* first_order.language.Lhom.mem_substructure_reduct
- \+ *def* first_order.language.Lhom.substructure_reduct
- \+ *lemma* first_order.language.substructure.closure_with_constants_eq
- \+ *lemma* first_order.language.substructure.coe_closure_eq_range_term_realize
- \+ *lemma* first_order.language.substructure.coe_with_constants
- \+/\- *lemma* first_order.language.substructure.constants_mem
- \+ *theorem* first_order.language.substructure.lift_card_closure_le
- \+ *lemma* first_order.language.substructure.lift_card_closure_le_card_term
- \+ *lemma* first_order.language.substructure.mem_closure_iff_exists_term
- \+ *lemma* first_order.language.substructure.mem_with_constants
- \+ *lemma* first_order.language.substructure.reduct_with_constants
- \+ *lemma* first_order.language.substructure.subset_closure_with_constants
- \+ *def* first_order.language.substructure.with_constants
- \+ *lemma* first_order.language.term.realize_mem



## [2022-03-11 16:25:19](https://github.com/leanprover-community/mathlib/commit/d6f337d)
feat(set_theory/ordinal_arithmetic): The derivative of multiplication ([#12202](https://github.com/leanprover-community/mathlib/pull/12202))
We prove that for `0 < a`, `deriv ((*) a) b = a ^ ω * b`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.deriv_eq_id_of_nfp_eq_id
- \+ *theorem* ordinal.deriv_mul_eq_opow_omega_mul
- \+ *theorem* ordinal.deriv_mul_zero
- \+ *theorem* ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right
- \- *theorem* ordinal.le_opow_self
- \+ *theorem* ordinal.left_le_opow
- \+ *theorem* ordinal.mul_eq_right_iff_opow_omega_dvd
- \+ *theorem* ordinal.mul_le_right_iff_opow_omega_dvd
- \+ *theorem* ordinal.nfp_mul_eq_opow_omega
- \+ *theorem* ordinal.nfp_mul_one
- \+ *theorem* ordinal.nfp_mul_opow_omega_add
- \+ *theorem* ordinal.nfp_mul_zero
- \+ *theorem* ordinal.nfp_zero_mul
- \+ *theorem* ordinal.opow_one_add
- \+ *theorem* ordinal.right_le_opow



## [2022-03-11 13:44:08](https://github.com/leanprover-community/mathlib/commit/e6fef39)
feat(algebra/order/monoid): add `with_zero.canonically_linear_ordered_add_monoid` ([#12568](https://github.com/leanprover-community/mathlib/pull/12568))
This also removes some non-terminal `simp`s in nearby proofs
#### Estimated changes
Modified src/algebra/order/monoid.lean




## [2022-03-11 13:44:07](https://github.com/leanprover-community/mathlib/commit/12786d0)
feat(order/sup_indep): add `finset.sup_indep_pair` ([#12549](https://github.com/leanprover-community/mathlib/pull/12549))
This is used to provide simp lemmas about `sup_indep` on `bool` and `fin 2`.
#### Estimated changes
Modified src/order/sup_indep.lean
- \+ *lemma* complete_lattice.independent_iff_sup_indep_univ
- \+ *lemma* finset.sup_indep_pair
- \+ *lemma* finset.sup_indep_univ_bool
- \+ *lemma* finset.sup_indep_univ_fin_two



## [2022-03-11 13:44:06](https://github.com/leanprover-community/mathlib/commit/4dc4dc8)
chore(topology/algebra/module/basic): cleanup variables and coercions ([#12542](https://github.com/leanprover-community/mathlib/pull/12542))
Having the "simple" variables in the lemmas statements rather than globally makes it easier to move lemmas around in future.
This also mean lemmas like `coe_comp` can have their arguments in a better order, as it's easier to customize the argument order at the declaration.
This also replaces a lot of `(_ : M₁ → M₂)`s with `⇑_` for brevity in lemma statements.
No lemmas statements (other than argument reorders) or proofs have changed.
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* continuous_linear_equiv.coe_coe
- \+/\- *lemma* continuous_linear_equiv.coe_refl'
- \+/\- *lemma* continuous_linear_map.add_apply
- \+/\- *lemma* continuous_linear_map.apply_ker
- \+/\- *lemma* continuous_linear_map.coe_add'
- \+/\- *lemma* continuous_linear_map.coe_add
- \+/\- *lemma* continuous_linear_map.coe_coe
- \+/\- *lemma* continuous_linear_map.coe_comp'
- \+/\- *lemma* continuous_linear_map.coe_comp
- \+/\- *lemma* continuous_linear_map.coe_fst'
- \+/\- *lemma* continuous_linear_map.coe_fst
- \+/\- *lemma* continuous_linear_map.coe_id'
- \+/\- *lemma* continuous_linear_map.coe_neg'
- \+/\- *lemma* continuous_linear_map.coe_neg
- \+/\- *lemma* continuous_linear_map.coe_smul'
- \+/\- *lemma* continuous_linear_map.coe_smul
- \+/\- *lemma* continuous_linear_map.coe_snd'
- \+/\- *lemma* continuous_linear_map.coe_snd
- \+/\- *lemma* continuous_linear_map.coe_sub'
- \+/\- *lemma* continuous_linear_map.coe_sub
- \+/\- *lemma* continuous_linear_map.coe_zero'
- \+/\- *theorem* continuous_linear_map.comp_id
- \+/\- *lemma* continuous_linear_map.comp_smul
- \+/\- *lemma* continuous_linear_map.comp_smulₛₗ
- \+/\- *lemma* continuous_linear_map.id_apply
- \+/\- *theorem* continuous_linear_map.id_comp
- \+/\- *lemma* continuous_linear_map.image_smul_set
- \+/\- *lemma* continuous_linear_map.image_smul_setₛₗ
- \+/\- *lemma* continuous_linear_map.is_closed_ker
- \+/\- *lemma* continuous_linear_map.ker_coe
- \+/\- *lemma* continuous_linear_map.map_smulₛₗ
- \+/\- *lemma* continuous_linear_map.neg_apply
- \+/\- *lemma* continuous_linear_map.one_apply
- \+/\- *lemma* continuous_linear_map.preimage_smul_set
- \+/\- *lemma* continuous_linear_map.preimage_smul_setₛₗ
- \+/\- *lemma* continuous_linear_map.range_coe
- \+/\- *lemma* continuous_linear_map.range_prod_eq
- \+/\- *lemma* continuous_linear_map.smul_apply
- \+/\- *lemma* continuous_linear_map.smul_comp
- \+/\- *lemma* continuous_linear_map.sub_apply'
- \+/\- *lemma* continuous_linear_map.sub_apply
- \+/\- *lemma* continuous_linear_map.zero_apply
- \+/\- *theorem* continuous_linear_map.zero_comp



## [2022-03-11 10:13:17](https://github.com/leanprover-community/mathlib/commit/02e0ab2)
refactor(group_theory/commutator): Golf some proofs ([#12586](https://github.com/leanprover-community/mathlib/pull/12586))
This PR golfs the proofs of some lemmas in `commutator.lean`.
I also renamed `bot_commutator` and `commutator_bot` to `commutator_bot_left` and `commutator_bot_right`, since "bot_commutator" didn't sound right to me (you would say "the commutator of H and K", not "H commutator K"), but I can revert to the old name if you want.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \- *lemma* subgroup.bot_commutator
- \- *lemma* subgroup.commutator_bot
- \+ *lemma* subgroup.commutator_bot_left
- \+ *lemma* subgroup.commutator_bot_right
- \+/\- *lemma* subgroup.commutator_le_inf
- \+/\- *lemma* subgroup.commutator_le_left
- \+/\- *lemma* subgroup.commutator_le_right

Modified src/group_theory/solvable.lean




## [2022-03-11 10:13:16](https://github.com/leanprover-community/mathlib/commit/d9a774e)
feat(order/hom): `prod.swap` as an `order_iso` ([#12585](https://github.com/leanprover-community/mathlib/pull/12585))
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* prod.swap_le_swap
- \+ *lemma* prod.swap_lt_swap

Modified src/order/hom/basic.lean
- \+ *lemma* order_iso.coe_prod_comm
- \+ *def* order_iso.prod_comm
- \+ *lemma* order_iso.prod_comm_symm



## [2022-03-11 08:22:26](https://github.com/leanprover-community/mathlib/commit/840a042)
feat(data/list/basic): Miscellaneous `fold` lemmas ([#12579](https://github.com/leanprover-community/mathlib/pull/12579))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.foldl_combinator_K
- \+ *theorem* list.foldl_fixed
- \+ *theorem* list.foldr_fixed

Modified src/logic/function/iterate.lean
- \+ *theorem* list.foldl_const
- \+ *theorem* list.foldr_const



## [2022-03-11 08:22:25](https://github.com/leanprover-community/mathlib/commit/1a581ed)
refactor(group_theory/solvable): Golf proof ([#12552](https://github.com/leanprover-community/mathlib/pull/12552))
This PR golfs the proof of insolvability of S_5, using the new commutator notation.
#### Estimated changes
Modified src/group_theory/solvable.lean




## [2022-03-11 08:22:24](https://github.com/leanprover-community/mathlib/commit/1326aa7)
feat(analysis/special_functions): limit of x^s * exp(-x) for s real ([#12540](https://github.com/leanprover-community/mathlib/pull/12540))
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* tendsto_exp_div_rpow_at_top
- \+ *lemma* tendsto_exp_mul_div_rpow_at_top
- \+ *lemma* tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0



## [2022-03-11 08:22:23](https://github.com/leanprover-community/mathlib/commit/e553f8a)
refactor(algebra/group/to_additive): monadic code cosmetics ([#12527](https://github.com/leanprover-community/mathlib/pull/12527))
as suggested by @kmill and @eric-wieser, but the merge was faster
Also improve test file.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified test/lint_to_additive_doc.lean
- \+ *lemma* no_to_additive



## [2022-03-11 08:22:22](https://github.com/leanprover-community/mathlib/commit/47b1ddf)
feat(data/setoid/partition): Relate `setoid.is_partition` and `finpartition` ([#12459](https://github.com/leanprover-community/mathlib/pull/12459))
Add two functions that relate `setoid.is_partition` and `finpartition`:
* `setoid.is_partition.partition` 
* `finpartition.is_partition_parts`
Meanwhile add some lemmas related to `finset.sup` and `finset.inf` in data/finset/lattice.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.inf_id_set_eq_sInter
- \+ *lemma* finset.inf_set_eq_bInter
- \+ *lemma* finset.sup_id_set_eq_sUnion
- \+ *lemma* finset.sup_set_eq_bUnion

Modified src/data/setoid/partition.lean
- \+ *theorem* finpartition.is_partition_parts
- \+ *def* setoid.is_partition.finpartition

Modified src/order/well_founded_set.lean




## [2022-03-11 06:44:16](https://github.com/leanprover-community/mathlib/commit/115f8c7)
fix(probability): remove unused argument from `cond_cond_eq_cond_inter` ([#12583](https://github.com/leanprover-community/mathlib/pull/12583))
This was a property that we already derived within the proof itself from conditionable intersection (I think I forgot to remove this when I made the PR).
#### Estimated changes
Modified src/probability/conditional.lean




## [2022-03-11 06:44:15](https://github.com/leanprover-community/mathlib/commit/3061d18)
feat(data/nat/{nth,prime}): add facts about primes ([#12560](https://github.com/leanprover-community/mathlib/pull/12560))
Gives `{p | prime p}.infinite` as well as `infinite_of_not_bdd_above` lemma. Also gives simp lemmas for `prime_counting'`.
#### Estimated changes
Modified src/data/nat/nth.lean
- \+ *lemma* nat.nth_injective_of_infinite

Modified src/data/nat/prime.lean
- \+ *lemma* nat.infinite_set_of_prime
- \+ *lemma* nat.not_bdd_above_set_of_prime

Modified src/data/set/finite.lean
- \+ *lemma* set.infinite_of_not_bdd_above
- \+ *lemma* set.infinite_of_not_bdd_below

Modified src/number_theory/prime_counting.lean
- \+ *lemma* nat.prime_counting'_nth_eq
- \+ *lemma* nat.prime_nth_prime



## [2022-03-11 06:44:14](https://github.com/leanprover-community/mathlib/commit/de4d14c)
feat(group_theory/commutator): Add some basic lemmas ([#12554](https://github.com/leanprover-community/mathlib/pull/12554))
This PR adds lemmas adds some basic lemmas about when the commutator is trivial.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+ *lemma* commutator_element_eq_one_iff_commute
- \+ *lemma* commutator_element_eq_one_iff_mul_comm
- \+ *lemma* commutator_element_one_left
- \+ *lemma* commutator_element_one_right
- \+ *lemma* commute.commutator_eq



## [2022-03-11 06:12:11](https://github.com/leanprover-community/mathlib/commit/355472d)
refactor(group_theory/commutator): Golf proof of `commutator_mem_commutator` ([#12584](https://github.com/leanprover-community/mathlib/pull/12584))
This PR golfs the proof of `commutator_mem_commutator`, and moves it earlier in the file so that it can be used earlier.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+/\- *lemma* subgroup.commutator_mem_commutator



## [2022-03-11 02:38:57](https://github.com/leanprover-community/mathlib/commit/b5a26d0)
feat(data/list/basic): Lists over empty type are `unique` ([#12582](https://github.com/leanprover-community/mathlib/pull/12582))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *def* list.unique_of_is_empty



## [2022-03-10 23:44:36](https://github.com/leanprover-community/mathlib/commit/f0dd6e9)
refactor(group_theory/commutator): Use commutators in `commutator_le` ([#12572](https://github.com/leanprover-community/mathlib/pull/12572))
This PR golfs the proof of `commutator_le`, and uses the new commutator notation.
#### Estimated changes
Modified src/group_theory/commutator.lean




## [2022-03-10 23:12:24](https://github.com/leanprover-community/mathlib/commit/6c04fcf)
refactor(group_theory/commutator): Use commutator notation in `commutator_normal` ([#12575](https://github.com/leanprover-community/mathlib/pull/12575))
This PR uses the new commutator notation in the proof of `commutator_normal`.
#### Estimated changes
Modified src/group_theory/commutator.lean




## [2022-03-10 21:17:59](https://github.com/leanprover-community/mathlib/commit/84cbbc9)
feat(algebra/group/to_additive + a few more files): make `to_additive` convert `unit` to `add_unit` ([#12564](https://github.com/leanprover-community/mathlib/pull/12564))
This likely involves removing names that match autogenerated names.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_of_mul_eq_one

Modified src/data/equiv/mul_add.lean
- \+/\- *lemma* coe_to_units

Modified src/group_theory/congruence.lean
- \+/\- *def* con.lift_on_units

Modified src/group_theory/order_of_element.lean




## [2022-03-10 19:33:06](https://github.com/leanprover-community/mathlib/commit/869ef84)
feat(data/zmod/basic): some lemmas about coercions ([#12571](https://github.com/leanprover-community/mathlib/pull/12571))
The names here are in line with `zmod.nat_coe_zmod_eq_zero_iff_dvd` and `zmod.int_coe_zmod_eq_zero_iff_dvd` a few lines above.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.int_coe_zmod_eq_iff
- \+ *lemma* zmod.nat_coe_zmod_eq_iff
- \+ *lemma* zmod.val_int_cast



## [2022-03-10 19:33:05](https://github.com/leanprover-community/mathlib/commit/6fdb1d5)
chore(*): clear up some excessive by statements ([#12570](https://github.com/leanprover-community/mathlib/pull/12570))
Delete some `by` (and similar commands that do nothing, such as
- `by by blah`
- `by begin blah end`
- `{ by blah }`
- `begin { blah } end`
Also clean up the proof of `monic.map` and `nat_degree_div_by_monic` a bit.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/lie/nilpotent.lean


Modified src/category_theory/adjunction/whiskering.lean


Modified src/data/polynomial/div.lean


Modified src/data/polynomial/monic.lean


Modified src/field_theory/separable.lean


Modified src/group_theory/exponent.lean
- \+/\- *lemma* monoid.exponent_eq_zero_iff

Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/measure_theory/function/simple_func_dense.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/order/filter/ennreal.lean


Modified src/order/jordan_holder.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2022-03-10 19:33:04](https://github.com/leanprover-community/mathlib/commit/45c22c0)
feat(field_theory/is_alg_closed/basic): add `is_alg_closed.infinite` ([#12566](https://github.com/leanprover-community/mathlib/pull/12566))
An algebraically closed field is infinite, because if it is finite then `x^(n+1) - 1` is a separable polynomial (where `n` is the cardinality of the field).
#### Estimated changes
Modified src/field_theory/is_alg_closed/basic.lean




## [2022-03-10 19:33:02](https://github.com/leanprover-community/mathlib/commit/0e93816)
feat(tactic/norm_num_command): add user command to run norm_num on an expression ([#12550](https://github.com/leanprover-community/mathlib/pull/12550))
For example,
```
#norm_num 2^100 % 10
-- 6
```
#### Estimated changes
Modified src/tactic/norm_num.lean




## [2022-03-10 17:46:10](https://github.com/leanprover-community/mathlib/commit/f654a86)
chore(*): remove lines claiming to introduce variables ([#12569](https://github.com/leanprover-community/mathlib/pull/12569))
They don't.
#### Estimated changes
Modified src/analysis/complex/real_deriv.lean


Modified src/data/equiv/option.lean


Modified src/group_theory/order_of_element.lean


Modified src/order/antisymmetrization.lean




## [2022-03-10 15:58:20](https://github.com/leanprover-community/mathlib/commit/4a59a4d)
chore(order/galois_connection): Make lifting instances reducible ([#12559](https://github.com/leanprover-community/mathlib/pull/12559))
and provide `infi₂` and `supr₂` versions of the lemmas.
#### Estimated changes
Modified src/order/galois_connection.lean
- \+/\- *lemma* galois_connection.l_Sup
- \+/\- *lemma* galois_connection.l_supr
- \+ *lemma* galois_connection.l_supr₂
- \+/\- *lemma* galois_connection.u_Inf
- \+/\- *lemma* galois_connection.u_infi
- \+ *lemma* galois_connection.u_infi₂



## [2022-03-10 15:28:09](https://github.com/leanprover-community/mathlib/commit/788ccf0)
chore(cardinal_divisibility): tiny golf ([#12567](https://github.com/leanprover-community/mathlib/pull/12567))
#### Estimated changes
Modified src/set_theory/cardinal_divisibility.lean




## [2022-03-10 13:16:05](https://github.com/leanprover-community/mathlib/commit/cd111e9)
feat(data/equiv/mul_add): add to_additive attribute to `group.is_unit` ([#12563](https://github.com/leanprover-community/mathlib/pull/12563))
Unless something breaks, this PR does nothing else!
#### Estimated changes
Modified src/data/equiv/mul_add.lean




## [2022-03-10 10:38:55](https://github.com/leanprover-community/mathlib/commit/41f5c17)
chore(set_theory/ordinal_arithmetic): Make auxiliary result private ([#12562](https://github.com/leanprover-community/mathlib/pull/12562))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.CNF_pairwise_aux



## [2022-03-10 10:08:31](https://github.com/leanprover-community/mathlib/commit/4048a9b)
chore(measure_theory/function/convergence_in_measure): golf proof with Borel-Cantelli ([#12551](https://github.com/leanprover-community/mathlib/pull/12551))
#### Estimated changes
Modified src/measure_theory/function/convergence_in_measure.lean




## [2022-03-10 09:02:58](https://github.com/leanprover-community/mathlib/commit/d56a9bc)
feat(set_theory/ordinal_arithmetic): `add_eq_zero_iff`, `mul_eq_zero_iff` ([#12561](https://github.com/leanprover-community/mathlib/pull/12561))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.add_eq_zero_iff
- \+ *theorem* ordinal.left_eq_zero_of_add_eq_zero
- \+ *theorem* ordinal.mul_eq_zero_iff
- \+ *theorem* ordinal.right_eq_zero_of_add_eq_zero



## [2022-03-10 09:02:56](https://github.com/leanprover-community/mathlib/commit/1e560a6)
refactor(group_theory/commutator): Generalize `map_commutator_element` ([#12555](https://github.com/leanprover-community/mathlib/pull/12555))
This PR generalizes `map_commutator_element` from `monoid_hom_class F G G` to `monoid_hom_class F G G'`.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \+/\- *lemma* map_commutator_element



## [2022-03-10 07:37:11](https://github.com/leanprover-community/mathlib/commit/24e3b5f)
refactor(topology/opens): Turn `opens.gi` into a Galois coinsertion ([#12547](https://github.com/leanprover-community/mathlib/pull/12547))
`topological_space.opens.gi` is currently a `galois_insertion` between `order_dual (opens α)` and `order_dual (set α)`. This turns it into the sensible thing, namely a `galois_coinsertion` between `opens α` and `set α`.
#### Estimated changes
Modified src/topology/opens.lean
- \+/\- *lemma* topological_space.opens.ext
- \+/\- *lemma* topological_space.opens.ext_iff
- \+/\- *def* topological_space.opens.gi
- \- *lemma* topological_space.opens.gi_choice_val
- \+/\- *lemma* topological_space.opens.le_def



## [2022-03-10 07:37:10](https://github.com/leanprover-community/mathlib/commit/0fd9929)
feat(group_theory/double_cosets): definition of double cosets and some basic lemmas. ([#9490](https://github.com/leanprover-community/mathlib/pull/9490))
This contains the definition of double cosets and some basic lemmas about them, such as "the whole group is the disjoint union of its double cosets" and relationship to usual group quotients.
#### Estimated changes
Added src/group_theory/double_coset.lean
- \+ *lemma* doset.bot_rel_eq_left_rel
- \+ *lemma* doset.disjoint_out'
- \+ *lemma* doset.doset_eq_of_mem
- \+ *lemma* doset.doset_union_left_coset
- \+ *lemma* doset.doset_union_right_coset
- \+ *lemma* doset.eq
- \+ *lemma* doset.eq_of_not_disjoint
- \+ *lemma* doset.left_bot_eq_left_quot
- \+ *lemma* doset.mem_doset
- \+ *lemma* doset.mem_doset_of_not_disjoint
- \+ *lemma* doset.mem_doset_self
- \+ *abbreviation* doset.mk
- \+ *lemma* doset.mk_eq_of_doset_eq
- \+ *lemma* doset.mk_out'_eq_mul
- \+ *lemma* doset.out_eq'
- \+ *def* doset.quot_to_doset
- \+ *def* doset.quotient
- \+ *lemma* doset.rel_bot_eq_right_group_rel
- \+ *lemma* doset.rel_iff
- \+ *lemma* doset.right_bot_eq_right_quot
- \+ *def* doset.setoid
- \+ *lemma* doset.union_quot_to_doset
- \+ *def* doset

Modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* subgroup.singleton_mul_subgroup
- \+ *lemma* subgroup.subgroup_mul_singleton



## [2022-03-10 06:34:47](https://github.com/leanprover-community/mathlib/commit/750ca95)
chore(linear_algebra/affine_space/affine_map): golf using the injective APIs ([#12543](https://github.com/leanprover-community/mathlib/pull/12543))
The extra whitespace means this isn't actually any shorter by number of lines, but it does eliminate 12 trivial proofs.
Again, the `has_scalar` instance has been hoisted from lower down the file, so that we have the `nat` and `int` actions available when we create the `add_comm_group` structure. Previously we just built the same `has_scalar` structure three times.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* affine_map.coe_smul



## [2022-03-10 06:34:46](https://github.com/leanprover-community/mathlib/commit/8836a42)
fix(linear_algebra/quadratic_form/basic): align diamonds in the nat- and int- action ([#12541](https://github.com/leanprover-community/mathlib/pull/12541))
This also provides `fun_like` and `zero_hom_class` instances.
The `has_scalar` code has been moved unchanged from further down in the file.
This change makes `coe_fn_sub` eligible for `dsimp`, since it can now be proved by `rfl`.
#### Estimated changes
Modified src/linear_algebra/quadratic_form/basic.lean
- \+/\- *lemma* quadratic_form.coe_fn_sub
- \+/\- *lemma* quadratic_form.congr_fun
- \+/\- *lemma* quadratic_form.ext
- \+/\- *lemma* quadratic_form.ext_iff
- \+/\- *lemma* quadratic_form.sub_apply
- \- *lemma* quadratic_form.to_fun_eq_apply
- \+ *lemma* quadratic_form.to_fun_eq_coe



## [2022-03-10 06:34:44](https://github.com/leanprover-community/mathlib/commit/9e28852)
feat(field_theory/krull_topology): added krull_topology_totally_disconnected ([#12398](https://github.com/leanprover-community/mathlib/pull/12398))
#### Estimated changes
Modified src/field_theory/krull_topology.lean
- \+ *lemma* intermediate_field.fixing_subgroup_is_closed
- \+/\- *lemma* krull_topology_t2
- \+ *lemma* krull_topology_totally_disconnected
- \- *lemma* subgroup.is_open_of_one_mem_interior

Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* subgroup.is_open_mono
- \+ *lemma* subgroup.is_open_of_one_mem_interior

Modified src/topology/connected.lean
- \+ *lemma* is_totally_disconnected_of_clopen_set



## [2022-03-10 05:29:37](https://github.com/leanprover-community/mathlib/commit/bab039f)
feat(topology/opens): The frame of opens of a topological space ([#12546](https://github.com/leanprover-community/mathlib/pull/12546))
Provide the `frame` instance for `opens α` and strengthen `opens.comap` from `order_hom` to `frame_hom`.
#### Estimated changes
Modified src/topology/algebra/order/basic.lean


Modified src/topology/opens.lean
- \- *lemma* topological_space.opens.Sup_s
- \+ *lemma* topological_space.opens.coe_Sup
- \+/\- *lemma* topological_space.opens.coe_inf
- \+/\- *def* topological_space.opens.comap
- \+/\- *lemma* topological_space.opens.comap_id
- \+/\- *lemma* topological_space.opens.comap_mono



## [2022-03-10 05:29:36](https://github.com/leanprover-community/mathlib/commit/9c2f6eb)
feat(category_theory/abelian/exact): `exact g.op f.op` ([#12456](https://github.com/leanprover-community/mathlib/pull/12456))
This pr is about `exact g.op f.op` from `exact f g` in an abelian category; this pr is taken from liquid tensor experiment. I believe the original author is @adamtopaz.
#### Estimated changes
Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.exact.op_iff
- \+ *lemma* category_theory.abelian.exact.unop_iff
- \+ *lemma* category_theory.abelian.is_equivalence.exact_iff

Modified src/category_theory/abelian/opposite.lean
- \+ *lemma* category_theory.cokernel.π_op
- \+ *lemma* category_theory.cokernel.π_unop
- \+ *lemma* category_theory.kernel.ι_op
- \+ *lemma* category_theory.kernel.ι_unop

Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.is_iso.comp_left_eq_zero
- \+ *lemma* category_theory.preadditive.is_iso.comp_right_eq_zero



## [2022-03-10 04:56:21](https://github.com/leanprover-community/mathlib/commit/ef25c4c)
refactor(group_theory/commutator): Rename `commutator_containment` to `commutator_mem_commutator` ([#12553](https://github.com/leanprover-community/mathlib/pull/12553))
This PR renames `commutator_containment` to `commutator_mem_commutator`, uses the new commutator notation, and makes the subgroups implicit.
#### Estimated changes
Modified src/group_theory/commutator.lean
- \- *lemma* subgroup.commutator_containment
- \+ *lemma* subgroup.commutator_mem_commutator

Modified src/group_theory/nilpotent.lean


Modified src/group_theory/solvable.lean




## [2022-03-09 13:59:57](https://github.com/leanprover-community/mathlib/commit/9facd19)
doc(combinatorics/simple_graph/basic): fix typo ([#12544](https://github.com/leanprover-community/mathlib/pull/12544))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean




## [2022-03-09 11:28:18](https://github.com/leanprover-community/mathlib/commit/0d6fb8a)
chore(analysis/complex/upper_half_plane): use `coe` instead of `coe_fn` ([#12532](https://github.com/leanprover-community/mathlib/pull/12532))
This matches the approach used by other files working with `special_linear_group`.
#### Estimated changes
Modified src/analysis/complex/upper_half_plane.lean
- \+/\- *def* upper_half_plane.denom
- \+/\- *def* upper_half_plane.num



## [2022-03-09 11:28:17](https://github.com/leanprover-community/mathlib/commit/c4a3413)
chore(data/polynomial): use dot notation for monic lemmas ([#12530](https://github.com/leanprover-community/mathlib/pull/12530))
As discussed in [#12447](https://github.com/leanprover-community/mathlib/pull/12447)
- Use the notation throughout the library
- Also deleted `ne_zero_of_monic` as it was a duplicate of `monic.ne_zero` it seems.
- Cleaned up a small proof here and there too.
#### Estimated changes
Modified src/data/polynomial/div.lean


Modified src/data/polynomial/lifts.lean
- \+/\- *lemma* polynomial.lifts_and_degree_eq_and_monic

Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.degree_map_of_monic
- \+ *lemma* polynomial.monic.add_of_left
- \+ *lemma* polynomial.monic.add_of_right
- \+ *lemma* polynomial.monic.degree_map
- \+ *lemma* polynomial.monic.map
- \+ *lemma* polynomial.monic.mul
- \+ *lemma* polynomial.monic.nat_degree_map
- \+ *lemma* polynomial.monic.pow
- \+/\- *lemma* polynomial.monic_C_mul_of_mul_leading_coeff_eq_one
- \- *lemma* polynomial.monic_add_of_left
- \- *lemma* polynomial.monic_add_of_right
- \- *lemma* polynomial.monic_map
- \- *lemma* polynomial.monic_mul
- \+/\- *lemma* polynomial.monic_mul_C_of_leading_coeff_mul_eq_one
- \- *lemma* polynomial.monic_pow
- \- *lemma* polynomial.nat_degree_map_of_monic
- \- *lemma* polynomial.ne_zero_of_monic

Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/norm.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/ring_theory/power_basis.lean


Modified src/ring_theory/trace.lean




## [2022-03-09 09:05:27](https://github.com/leanprover-community/mathlib/commit/55d1f3e)
chore(set_theory/cardinal): `min` → `Inf` ([#12517](https://github.com/leanprover-community/mathlib/pull/12517))
Various definitions are awkwardly stated in terms of minima of subtypes. We instead rewrite them as infima and golf them. Further, we protect `cardinal.min` to avoid confusion with `linear_order.min`.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.le_min
- \+/\- *theorem* cardinal.le_sup
- \+/\- *theorem* cardinal.lift_min
- \- *def* cardinal.min
- \+/\- *theorem* cardinal.min_eq
- \+/\- *theorem* cardinal.min_le
- \+ *theorem* cardinal.nonempty_sup
- \+ *theorem* cardinal.succ_nonempty
- \+/\- *def* cardinal.sup



## [2022-03-09 05:46:45](https://github.com/leanprover-community/mathlib/commit/5d405e2)
chore(linear_algebra/alternating): golf using injective APIs ([#12536](https://github.com/leanprover-community/mathlib/pull/12536))
To do this, we have to move the has_scalar instance higher up in the file.
#### Estimated changes
Modified src/linear_algebra/alternating.lean




## [2022-03-09 05:46:44](https://github.com/leanprover-community/mathlib/commit/bc9dda8)
chore(algebra/module/linear_map): golf using injective APIs ([#12535](https://github.com/leanprover-community/mathlib/pull/12535))
To do this, we have to move the `has_scalar` instance higher up in the file.
#### Estimated changes
Modified src/algebra/module/linear_map.lean




## [2022-03-09 05:46:43](https://github.com/leanprover-community/mathlib/commit/94e9bb5)
chore(data/{finsupp,dfinsupp}/basic): use the injective APIs ([#12534](https://github.com/leanprover-community/mathlib/pull/12534))
This also fixes a scalar diamond in the `nat` and `int` actions on `dfinsupp`.
The diamond did not exist for `finsupp`.
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+ *lemma* dfinsupp.coe_nsmul
- \+ *lemma* dfinsupp.coe_zsmul
- \+ *lemma* dfinsupp.nsmul_apply
- \+ *lemma* dfinsupp.zsmul_apply

Modified src/data/finsupp/basic.lean


Modified src/data/finsupp/pointwise.lean




## [2022-03-09 05:46:41](https://github.com/leanprover-community/mathlib/commit/b8d176e)
chore(real/cau_seq_completion): put class in Prop ([#12533](https://github.com/leanprover-community/mathlib/pull/12533))
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean




## [2022-03-09 04:04:18](https://github.com/leanprover-community/mathlib/commit/1f6a2e9)
chore(scripts): update nolints.txt ([#12538](https://github.com/leanprover-community/mathlib/pull/12538))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2022-03-09 00:50:46](https://github.com/leanprover-community/mathlib/commit/2a3ecad)
feat(data/equiv/basic): lemmas about composition with equivalences ([#10693](https://github.com/leanprover-community/mathlib/pull/10693))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.comp_symm_eq
- \+ *lemma* equiv.eq_comp_symm
- \+ *lemma* equiv.eq_symm_comp
- \+ *lemma* equiv.symm_comp_eq

Modified src/data/equiv/module.lean
- \+ *lemma* linear_equiv.comp_symm_eq
- \+ *lemma* linear_equiv.comp_to_linear_map_symm_eq
- \+ *lemma* linear_equiv.eq_comp_symm
- \+ *lemma* linear_equiv.eq_comp_to_linear_map_symm
- \+ *lemma* linear_equiv.eq_symm_comp
- \+ *lemma* linear_equiv.eq_to_linear_map_symm_comp
- \+ *lemma* linear_equiv.symm_comp_eq
- \+ *lemma* linear_equiv.to_linear_map_symm_comp_eq

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.comp_symm_eq
- \+ *lemma* mul_equiv.eq_comp_symm
- \+ *lemma* mul_equiv.eq_symm_comp
- \+ *lemma* mul_equiv.symm_comp_eq



## [2022-03-08 21:42:52](https://github.com/leanprover-community/mathlib/commit/d69cda1)
chore(order/well_founded_set): golf two proofs ([#12529](https://github.com/leanprover-community/mathlib/pull/12529))
#### Estimated changes
Modified src/order/well_founded_set.lean




## [2022-03-08 21:42:51](https://github.com/leanprover-community/mathlib/commit/709a3b7)
feat(set_theory/cardinal_ordinal): `#(list α) ≤ max ω (#α)` ([#12519](https://github.com/leanprover-community/mathlib/pull/12519))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.mk_list_eq_omega
- \+ *theorem* cardinal.mk_list_le_max



## [2022-03-08 17:53:50](https://github.com/leanprover-community/mathlib/commit/feb24fb)
feat(topology/vector_bundle): direct sum of topological vector bundles ([#12512](https://github.com/leanprover-community/mathlib/pull/12512))
#### Estimated changes
Modified src/data/bundle.lean


Modified src/topology/maps.lean


Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.continuous_proj
- \+ *lemma* topological_vector_bundle.prod.inducing_diag
- \+ *lemma* topological_vector_bundle.trivialization.apply_eq_prod_continuous_linear_equiv_at
- \+ *lemma* topological_vector_bundle.trivialization.base_set_prod
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_prod
- \+ *def* topological_vector_bundle.trivialization.prod.inv_fun'
- \+ *lemma* topological_vector_bundle.trivialization.prod.inv_fun'_apply
- \+ *def* topological_vector_bundle.trivialization.prod.to_fun'
- \+ *def* topological_vector_bundle.trivialization.prod
- \+ *lemma* topological_vector_bundle.trivialization.prod_apply
- \+ *lemma* topological_vector_bundle.trivialization.prod_symm_apply
- \+ *lemma* topological_vector_bundle.trivialization.symm_apply_eq_mk_continuous_linear_equiv_at_symm



## [2022-03-08 17:53:49](https://github.com/leanprover-community/mathlib/commit/1d67b07)
feat(category_theory): cases in which (co)equalizers are split monos (epis) ([#12498](https://github.com/leanprover-community/mathlib/pull/12498))
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.cofork.is_colimit.π_desc_of_π
- \+ *lemma* category_theory.limits.fork.is_limit.lift_of_ι_ι
- \+ *def* category_theory.limits.split_epi_of_coequalizer
- \+ *def* category_theory.limits.split_epi_of_idempotent_coequalizer
- \+ *def* category_theory.limits.split_epi_of_idempotent_of_is_colimit_cofork
- \+ *def* category_theory.limits.split_mono_of_equalizer
- \+ *def* category_theory.limits.split_mono_of_idempotent_equalizer
- \+ *def* category_theory.limits.split_mono_of_idempotent_of_is_limit_fork



## [2022-03-08 17:53:47](https://github.com/leanprover-community/mathlib/commit/b4572d1)
feat(algebra/order/hom/ring): Ordered ring isomorphisms ([#12158](https://github.com/leanprover-community/mathlib/pull/12158))
Define `order_ring_iso`, the type of ordered ring isomorphisms, along with its typeclass `order_ring_iso_class`.
#### Estimated changes
Modified src/algebra/order/hom/ring.lean
- \+/\- *structure* order_ring_hom
- \+ *lemma* order_ring_iso.coe_mk
- \+ *lemma* order_ring_iso.coe_order_iso_refl
- \+ *lemma* order_ring_iso.coe_ring_equiv_refl
- \+ *lemma* order_ring_iso.coe_to_order_iso
- \+ *lemma* order_ring_iso.coe_to_order_ring_hom
- \+ *lemma* order_ring_iso.coe_to_order_ring_hom_refl
- \+ *lemma* order_ring_iso.coe_to_ring_equiv
- \+ *lemma* order_ring_iso.ext
- \+ *lemma* order_ring_iso.mk_coe
- \+ *lemma* order_ring_iso.refl_apply
- \+ *lemma* order_ring_iso.self_trans_symm
- \+ *def* order_ring_iso.simps.symm_apply
- \+ *lemma* order_ring_iso.symm_symm
- \+ *lemma* order_ring_iso.symm_trans_self
- \+ *lemma* order_ring_iso.to_fun_eq_coe
- \+ *def* order_ring_iso.to_order_iso
- \+ *lemma* order_ring_iso.to_order_iso_eq_coe
- \+ *def* order_ring_iso.to_order_ring_hom
- \+ *lemma* order_ring_iso.to_order_ring_hom_eq_coe
- \+ *lemma* order_ring_iso.to_ring_equiv_eq_coe
- \+ *lemma* order_ring_iso.trans_apply
- \+ *structure* order_ring_iso

Modified src/order/hom/basic.lean
- \+ *lemma* le_map_inv_iff
- \+ *lemma* lt_map_inv_iff
- \+ *lemma* map_inv_le_iff
- \+ *lemma* map_inv_lt_iff
- \+ *lemma* map_lt_map_iff



## [2022-03-08 15:58:18](https://github.com/leanprover-community/mathlib/commit/4ad5c5a)
feat(data/finset/noncomm_prod): add noncomm_prod_commute ([#12521](https://github.com/leanprover-community/mathlib/pull/12521))
adding `list.prod_commute`, `multiset.noncomm_prod_commute` and
`finset.noncomm_prod_commute`.
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_commute
- \+ *lemma* multiset.noncomm_prod_commute

Modified src/data/list/prod_monoid.lean
- \+ *lemma* list.prod_commute



## [2022-03-08 15:58:16](https://github.com/leanprover-community/mathlib/commit/fac5ffe)
feat(group_theory/subgroup/basic): disjoint_iff_mul_eq_one ([#12505](https://github.com/leanprover-community/mathlib/pull/12505))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.disjoint_def'
- \+ *lemma* subgroup.disjoint_def
- \+ *lemma* subgroup.disjoint_iff_mul_eq_one

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.disjoint_def'
- \+ *lemma* submonoid.disjoint_def



## [2022-03-08 15:58:15](https://github.com/leanprover-community/mathlib/commit/1597e9a)
feat(set_theory/ordinal_arithmetic): prove `enum_ord_le_of_subset` ([#12199](https://github.com/leanprover-community/mathlib/pull/12199))
I also used this as an excuse to remove a trivial theorem and some awkward dot notation.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *def* ordinal.enum_ord.order_iso
- \- *theorem* ordinal.enum_ord.surjective
- \+ *theorem* ordinal.enum_ord_le_of_subset
- \+ *def* ordinal.enum_ord_order_iso
- \+ *theorem* ordinal.enum_ord_surjective
- \- *theorem* ordinal.enum_ord_zero_le



## [2022-03-08 14:29:38](https://github.com/leanprover-community/mathlib/commit/ab6a892)
feat(data/finset/noncomm_prod): add noncomm_prod_congr ([#12520](https://github.com/leanprover-community/mathlib/pull/12520))
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_congr



## [2022-03-08 14:29:36](https://github.com/leanprover-community/mathlib/commit/c0ba4d6)
feat(ring_theory/polynomial/eisenstein): add cyclotomic_comp_X_add_one_is_eisenstein_at ([#12447](https://github.com/leanprover-community/mathlib/pull/12447))
We add `cyclotomic_comp_X_add_one_is_eisenstein_at`: `(cyclotomic p ℤ).comp (X + 1)` is Eisenstein at `p`.
From flt-regular
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.mul_X_injective
- \+ *lemma* polynomial.mul_X_pow_injective

Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.add_algebra_map
- \- *lemma* minpoly.minpoly_add_algebra_map
- \- *lemma* minpoly.minpoly_sub_algebra_map
- \+ *lemma* minpoly.sub_algebra_map

Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_primitive_root.minpoly_sub_one_eq_cyclotomic_comp

Modified src/ring_theory/polynomial/basic.lean
- \+ *lemma* polynomial.geom_sum_X_comp_X_add_one_eq_sum
- \+ *lemma* polynomial.monic.geom_sum'
- \+ *lemma* polynomial.monic.geom_sum
- \+ *lemma* polynomial.monic_geom_sum_X

Modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* cyclotomic_comp_X_add_one_is_eisenstein_at



## [2022-03-08 12:44:00](https://github.com/leanprover-community/mathlib/commit/94cbfad)
chore(algebra/*): move some lemmas about is_unit from associated.lean ([#12526](https://github.com/leanprover-community/mathlib/pull/12526))
There doesn't seem to be any reason for them to live there.
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* dvd_and_not_dvd_iff
- \- *theorem* is_unit_iff_dvd_one
- \- *theorem* is_unit_iff_forall_dvd
- \- *lemma* is_unit_of_dvd_one
- \- *theorem* is_unit_of_dvd_unit
- \- *lemma* not_is_unit_of_not_is_unit_dvd
- \- *lemma* pow_dvd_pow_iff

Modified src/algebra/divisibility.lean
- \+ *lemma* dvd_and_not_dvd_iff
- \+ *theorem* is_unit_iff_dvd_one
- \+ *theorem* is_unit_iff_forall_dvd
- \+ *lemma* is_unit_of_dvd_one
- \+ *theorem* is_unit_of_dvd_unit
- \+ *lemma* not_is_unit_of_not_is_unit_dvd

Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_dvd_pow_iff



## [2022-03-08 12:43:59](https://github.com/leanprover-community/mathlib/commit/9c13d62)
feat(data/int/gcd): add gcd_pos_iff ([#12522](https://github.com/leanprover-community/mathlib/pull/12522))
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *theorem* int.gcd_pos_iff



## [2022-03-08 12:43:58](https://github.com/leanprover-community/mathlib/commit/6dd3249)
feat(set_theory/ordinal_arithmetic): `brange_const` ([#12483](https://github.com/leanprover-community/mathlib/pull/12483))
This is the `brange` analog to `set.range_const`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.brange_const



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
Modified src/algebra/direct_sum/ring.lean
- \+ *lemma* direct_sum.of_zero_pow

Modified src/algebra/field/basic.lean


Modified src/algebra/graded_monoid.lean
- \+ *lemma* graded_monoid.mk_zero_pow

Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/opposite.lean


Modified src/algebra/group/ulift.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/homology/additive.lean
- \+ *lemma* homological_complex.nsmul_f_apply
- \+ *lemma* homological_complex.zsmul_f_apply

Modified src/algebra/lie/basic.lean
- \+ *lemma* lie_module_hom.coe_nsmul
- \+ *lemma* lie_module_hom.coe_zsmul
- \+ *lemma* lie_module_hom.nsmul_apply
- \+ *lemma* lie_module_hom.zsmul_apply

Modified src/algebra/lie/free.lean


Modified src/algebra/module/submodule.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/nonneg.lean
- \+ *lemma* nonneg.mk_pow
- \+ *lemma* nonneg.nsmul_mk

Modified src/algebra/order/ring.lean


Modified src/algebra/order/with_zero.lean


Modified src/algebra/pointwise.lean
- \+/\- *lemma* finset.coe_mul
- \+ *lemma* finset.coe_one
- \+ *lemma* finset.coe_pow

Modified src/algebra/ring/basic.lean


Modified src/algebra/star/self_adjoint.lean


Modified src/algebra/symmetrized.lean


Modified src/analysis/box_integral/partition/additive.lean


Modified src/analysis/normed/group/hom.lean
- \+ *lemma* normed_group_hom.coe_nsmul
- \+ *lemma* normed_group_hom.coe_zsmul
- \+ *lemma* normed_group_hom.nsmul_apply
- \+ *lemma* normed_group_hom.zsmul_apply

Modified src/analysis/seminorm.lean


Modified src/data/equiv/transfer_instance.lean
- \+ *lemma* equiv.pow_def

Modified src/data/pnat/basic.lean


Modified src/data/pnat/prime.lean


Modified src/data/real/nnreal.lean


Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.zpow_mem

Modified src/geometry/manifold/algebra/left_invariant_derivation.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/specific_groups/cyclic.lean


Modified src/group_theory/subgroup/basic.lean
- \+/\- *lemma* subgroup.coe_pow
- \+/\- *lemma* subgroup.coe_zpow

Modified src/group_theory/submonoid/membership.lean
- \- *theorem* submonoid.coe_pow
- \- *lemma* submonoid.pow_mem

Modified src/group_theory/submonoid/operations.lean
- \+ *theorem* submonoid.coe_pow
- \+ *lemma* submonoid.pow_mem

Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* matrix.special_linear_group.coe_pow

Modified src/measure_theory/function/ae_eq_fun.lean
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_pow
- \+ *lemma* measure_theory.ae_eq_fun.coe_fn_zpow
- \+ *lemma* measure_theory.ae_eq_fun.mk_pow
- \+ *lemma* measure_theory.ae_eq_fun.mk_zpow
- \+ *lemma* measure_theory.ae_eq_fun.pow_to_germ
- \+ *lemma* measure_theory.ae_eq_fun.zpow_to_germ

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.coe_pow
- \+ *lemma* measure_theory.simple_func.coe_zpow
- \+ *lemma* measure_theory.simple_func.pow_apply
- \+ *lemma* measure_theory.simple_func.zpow_apply

Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* measure_theory.vector_measure.add_apply

Modified src/number_theory/cyclotomic/gal.lean


Modified src/order/filter/germ.lean
- \+ *lemma* filter.germ.coe_pow
- \+ *lemma* filter.germ.coe_zpow

Modified src/ring_theory/dedekind_domain/ideal.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_nsmul
- \+ *lemma* is_fractional.nsmul

Modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* subring.coe_pow

Modified src/ring_theory/subsemiring/basic.lean


Modified src/ring_theory/witt_vector/basic.lean
- \+ *lemma* witt_vector.map_fun.nsmul
- \+ *lemma* witt_vector.map_fun.pow
- \+ *lemma* witt_vector.map_fun.zsmul

Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_vector.constant_coeff_witt_nsmul
- \+ *lemma* witt_vector.constant_coeff_witt_zsmul
- \+ *lemma* witt_vector.nsmul_coeff
- \+ *lemma* witt_vector.pow_coeff
- \+ *def* witt_vector.witt_nsmul
- \+ *lemma* witt_vector.witt_nsmul_vars
- \+ *def* witt_vector.witt_pow
- \+ *lemma* witt_vector.witt_pow_vars
- \+ *def* witt_vector.witt_zsmul
- \+ *lemma* witt_vector.witt_zsmul_vars
- \+ *lemma* witt_vector.zsmul_coeff

Modified src/ring_theory/witt_vector/identities.lean


Modified src/ring_theory/witt_vector/init_tail.lean
- \+ *lemma* witt_vector.init_nsmul
- \+ *lemma* witt_vector.init_pow
- \+ *lemma* witt_vector.init_zsmul

Modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* witt_vector.truncate_fun_nsmul
- \+ *lemma* witt_vector.truncate_fun_pow
- \+ *lemma* witt_vector.truncate_fun_zsmul

Modified src/topology/algebra/continuous_affine_map.lean


Modified src/topology/algebra/module/multilinear.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.coe_npow_rec
- \+ *lemma* bounded_continuous_function.coe_nsmul
- \+ *lemma* bounded_continuous_function.coe_nsmul_rec
- \+ *lemma* bounded_continuous_function.coe_pow
- \+ *lemma* bounded_continuous_function.coe_zsmul
- \+ *lemma* bounded_continuous_function.coe_zsmul_rec
- \+ *lemma* bounded_continuous_function.nsmul_apply
- \+ *lemma* bounded_continuous_function.pow_apply
- \+ *lemma* bounded_continuous_function.zsmul_apply



## [2022-03-08 08:31:06](https://github.com/leanprover-community/mathlib/commit/b4a7ad6)
chore(field_theory/laurent): drop unused 'have'. ([#12516](https://github.com/leanprover-community/mathlib/pull/12516))
#### Estimated changes
Modified src/field_theory/laurent.lean




## [2022-03-08 08:31:05](https://github.com/leanprover-community/mathlib/commit/dc093e9)
chore(combinatorics/configuration): don't use classical.some in a proof ([#12515](https://github.com/leanprover-community/mathlib/pull/12515))
#### Estimated changes
Modified src/combinatorics/configuration.lean




## [2022-03-08 08:31:04](https://github.com/leanprover-community/mathlib/commit/ffa6e6d)
feat(set_theory/cardinal): `sum_le_sup_lift` ([#12513](https://github.com/leanprover-community/mathlib/pull/12513))
This is a universe-polymorphic version of `sum_le_sup`.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.sum_le_sup_lift



## [2022-03-08 08:31:03](https://github.com/leanprover-community/mathlib/commit/43cb3ff)
fix(ring_theory/ideal/operations): fix a name and dot notation ([#12507](https://github.com/leanprover-community/mathlib/pull/12507))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \- *theorem* ideal.is_primary.to_is_prime
- \+ *theorem* ideal.is_prime.is_primary



## [2022-03-08 08:31:02](https://github.com/leanprover-community/mathlib/commit/b2377ea)
feat(measure_theory/measure/finite_measure_weak_convergence): generalize scalar action ([#12503](https://github.com/leanprover-community/mathlib/pull/12503))
This means the smul lemmas also work for `nsmul`.
#### Estimated changes
Modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+/\- *lemma* measure_theory.finite_measure.coe_fn_smul
- \+/\- *lemma* measure_theory.finite_measure.coe_smul
- \+/\- *lemma* measure_theory.finite_measure.test_against_nn_smul



## [2022-03-08 08:31:00](https://github.com/leanprover-community/mathlib/commit/65095fe)
doc(order/succ_pred/basic): fix typo ([#12501](https://github.com/leanprover-community/mathlib/pull/12501))
#### Estimated changes
Modified src/order/succ_pred/basic.lean




## [2022-03-08 08:30:59](https://github.com/leanprover-community/mathlib/commit/47182da)
feat(algebra/group/to_additive): add to_additive doc string linter ([#12487](https://github.com/leanprover-community/mathlib/pull/12487))
it is an easy mistake to add a docstring to a lemma with `to_additive`
without also passing a string to `to_additive`. This linter checks for
that, and suggests to add a doc string when needed.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/group/to_additive.lean


Modified src/tactic/lint/default.lean


Added test/lint_to_additive_doc.lean
- \+ *lemma* bar
- \+ *lemma* baz
- \+ *lemma* foo
- \+ *lemma* quux



## [2022-03-08 08:30:58](https://github.com/leanprover-community/mathlib/commit/ccdcce1)
chore(set_theory/game/nim): General golfing ([#12471](https://github.com/leanprover-community/mathlib/pull/12471))
We make use of various relatively new theorems on ordinals to simplify various proofs, or otherwise clean up the file.
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.nim.exists_move_left_eq
- \- *lemma* pgame.nim.nim_wf_lemma
- \+/\- *lemma* pgame.nim.non_zero_first_wins
- \+/\- *lemma* pgame.nonmoves_nonempty

Modified src/set_theory/ordinal.lean




## [2022-03-08 08:30:57](https://github.com/leanprover-community/mathlib/commit/b3fba03)
feat(algebra/homology/homotopy) : `mk_coinductive` ([#12457](https://github.com/leanprover-community/mathlib/pull/12457))
`mk_coinductive` is the dual version of `mk_inductive` in the same file. `mk_inductive` is to build homotopy of chain complexes inductively and `mk_coinductive` is to build homotopy of cochain complexes inductively.
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* homotopy.d_next_cochain_complex
- \+ *def* homotopy.mk_coinductive
- \+ *def* homotopy.mk_coinductive_aux₁
- \+ *def* homotopy.mk_coinductive_aux₂
- \+ *lemma* homotopy.mk_coinductive_aux₃
- \+ *lemma* homotopy.prev_d_succ_cochain_complex
- \+ *lemma* homotopy.prev_d_zero_cochain_complex



## [2022-03-08 07:26:43](https://github.com/leanprover-community/mathlib/commit/14997d0)
feat(analysis/normed_space): allow non-unital C^* rings ([#12327](https://github.com/leanprover-community/mathlib/pull/12327))
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean


Modified src/topology/continuous_function/bounded.lean




## [2022-03-08 06:08:39](https://github.com/leanprover-community/mathlib/commit/74746bd)
chore(counterexamples/canonically_ordered_comm_semiring_two_mul): golf ([#12504](https://github.com/leanprover-community/mathlib/pull/12504))
#### Estimated changes
Modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *def* ex_L.L_subsemiring



## [2022-03-07 22:59:51](https://github.com/leanprover-community/mathlib/commit/5f6d30e)
chore(*): move `has_scalar` instances before `add_comm_monoid` instances ([#12502](https://github.com/leanprover-community/mathlib/pull/12502))
This makes it easier for us to set `nsmul` and `zsmul` in future.
#### Estimated changes
Modified src/linear_algebra/multilinear/basic.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/topology/algebra/module/multilinear.lean




## [2022-03-07 21:31:06](https://github.com/leanprover-community/mathlib/commit/e409a90)
feat(measure_theory/integral/periodic.lean): add lemma `function.periodic.tendsto_at_bot_interval_integral_of_pos'` ([#12500](https://github.com/leanprover-community/mathlib/pull/12500))
Partner of `function.periodic.tendsto_at_top_interval_integral_of_pos'` (I probably should have included this in [#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/order/floor.lean


Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integral.interval_integral_pos_of_pos

Modified src/measure_theory/integral/periodic.lean
- \+ *lemma* function.periodic.integral_le_Sup_add_zsmul_of_pos
- \+ *lemma* function.periodic.tendsto_at_bot_interval_integral_of_pos'
- \+ *lemma* function.periodic.tendsto_at_bot_interval_integral_of_pos



## [2022-03-07 21:31:04](https://github.com/leanprover-community/mathlib/commit/390554d)
feat(ring_theory/coprime/basic): lemmas about multiplying by units ([#12480](https://github.com/leanprover-community/mathlib/pull/12480))
#### Estimated changes
Modified src/ring_theory/coprime/basic.lean
- \+ *lemma* is_coprime_group_smul
- \+ *lemma* is_coprime_group_smul_left
- \+ *lemma* is_coprime_group_smul_right
- \+ *lemma* is_coprime_mul_unit_left
- \+ *lemma* is_coprime_mul_unit_left_left
- \+ *lemma* is_coprime_mul_unit_left_right
- \+ *lemma* is_coprime_mul_unit_right
- \+ *lemma* is_coprime_mul_unit_right_left
- \+ *lemma* is_coprime_mul_unit_right_right



## [2022-03-07 21:31:03](https://github.com/leanprover-community/mathlib/commit/9728bd2)
chore(number_theory/number_field): golf `int.not_is_field` ([#12451](https://github.com/leanprover-community/mathlib/pull/12451))
Golfed proof of number_theory.number_field.int.not_is_field
Co-authored by: David Ang <dka31@cantab.ac.uk>
Co-authored by: Eric Rodriguez <ericrboidi@gmail.com>
Co-authored by: Violeta Hernández <vi.hdz.p@gmail.com>
#### Estimated changes
Modified src/number_theory/number_field.lean
- \+/\- *lemma* int.not_is_field



## [2022-03-07 19:47:38](https://github.com/leanprover-community/mathlib/commit/1b4ee53)
feat(algebra/associated): add pow_not_prime ([#12493](https://github.com/leanprover-community/mathlib/pull/12493))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* of_irreducible_pow
- \+ *lemma* pow_not_prime



## [2022-03-07 19:47:36](https://github.com/leanprover-community/mathlib/commit/f28023e)
feat(measure_theory/function/uniform_integrable): Uniform integrability and Vitali convergence theorem ([#12408](https://github.com/leanprover-community/mathlib/pull/12408))
This PR defines uniform integrability (both in the measure theory sense as well as the probability theory sense) and proves the Vitali convergence theorem which establishes a relation between convergence in measure and uniform integrability with convergence in Lp.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.rpow_one_div_le_iff

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.norm_rpow

Added src/measure_theory/function/uniform_integrable.lean
- \+ *lemma* measure_theory.mem_ℒp.integral_indicator_norm_ge_le
- \+ *lemma* measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le
- \+ *lemma* measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le_of_meas
- \+ *lemma* measure_theory.mem_ℒp.snorm_ess_sup_indicator_norm_ge_eq_zero
- \+ *lemma* measure_theory.mem_ℒp.snorm_indicator_le'
- \+ *lemma* measure_theory.mem_ℒp.snorm_indicator_le
- \+ *lemma* measure_theory.mem_ℒp.snorm_indicator_le_of_meas
- \+ *lemma* measure_theory.mem_ℒp.snorm_indicator_norm_ge_le
- \+ *lemma* measure_theory.mem_ℒp.snorm_indicator_norm_ge_pos_le
- \+ *lemma* measure_theory.snorm_indicator_le_of_bound
- \+ *lemma* measure_theory.snorm_sub_le_of_dist_bdd
- \+ *lemma* measure_theory.tendsto_Lp_of_tendsto_ae
- \+ *lemma* measure_theory.tendsto_Lp_of_tendsto_ae_of_meas
- \+ *lemma* measure_theory.tendsto_Lp_of_tendsto_in_measure
- \+ *lemma* measure_theory.tendsto_in_measure_iff_tendsto_Lp
- \+ *lemma* measure_theory.tendsto_indicator_ge
- \+ *def* measure_theory.unif_integrable
- \+ *lemma* measure_theory.unif_integrable_congr_ae
- \+ *lemma* measure_theory.unif_integrable_const
- \+ *lemma* measure_theory.unif_integrable_fin
- \+ *lemma* measure_theory.unif_integrable_fintype
- \+ *lemma* measure_theory.unif_integrable_of_tendsto_Lp
- \+ *lemma* measure_theory.unif_integrable_of_tendsto_Lp_zero
- \+ *lemma* measure_theory.unif_integrable_subsingleton
- \+ *lemma* measure_theory.uniform_integrable.measurable
- \+ *lemma* measure_theory.uniform_integrable.mem_ℒp
- \+ *lemma* measure_theory.uniform_integrable.unif_integrable
- \+ *def* measure_theory.uniform_integrable

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* filter.eventually_eq.restrict

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.exists_seq_forall_of_frequently
- \+ *lemma* filter.frequently_iff_seq_frequently
- \+ *lemma* filter.not_tendsto_iff_exists_frequently_nmem
- \+ *lemma* filter.subseq_forall_of_frequently
- \+ *lemma* filter.tendsto_iff_forall_eventually_mem
- \+ *lemma* filter.tendsto_of_subseq_tendsto



## [2022-03-07 19:47:34](https://github.com/leanprover-community/mathlib/commit/1ee91a5)
feat(probability_theory/stopping): define progressively measurable processes ([#11350](https://github.com/leanprover-community/mathlib/pull/11350))
* Define progressively measurable processes (`prog_measurable`), which is the correct strengthening of `adapted` to get that the stopped process is also progressively measurable.
* Prove that an adapted continuous process is progressively measurable.
For discrete time processes, progressively measurable is equivalent to `adapted` .
This PR also changes some measurable_space arguments in `measurable_space.lean` from typeclass arguments to implicit.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.measurable_uncurry_of_continuous_of_measurable

Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable.prod_mk
- \+/\- *lemma* measurable.sum_elim
- \+/\- *lemma* measurable_from_prod_encodable
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \+/\- *lemma* measurable_prod
- \+/\- *lemma* measurable_snd
- \+ *def* measurable_space.prod
- \+/\- *lemma* measurable_sum
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_swap_iff
- \+/\- *lemma* measurable_to_encodable

Modified src/probability/stopping.lean
- \+/\- *lemma* measure_theory.adapted.add
- \+ *lemma* measure_theory.adapted.measurable_stopped_process_of_nat
- \+/\- *lemma* measure_theory.adapted.neg
- \+ *theorem* measure_theory.adapted.prog_measurable_of_continuous
- \+ *lemma* measure_theory.adapted.prog_measurable_of_nat
- \+/\- *lemma* measure_theory.adapted.smul
- \- *lemma* measure_theory.adapted.stopped_process
- \+ *lemma* measure_theory.adapted.stopped_process_of_nat
- \+/\- *lemma* measure_theory.integrable_stopped_process
- \+/\- *lemma* measure_theory.integrable_stopped_value
- \- *lemma* measure_theory.is_stopping_time.max
- \- *lemma* measure_theory.is_stopping_time.min
- \- *lemma* measure_theory.measurable_stopped_process
- \+/\- *lemma* measure_theory.mem_ℒp_stopped_process
- \+/\- *lemma* measure_theory.mem_ℒp_stopped_value
- \+ *lemma* measure_theory.prog_measurable.adapted_stopped_process
- \+ *lemma* measure_theory.prog_measurable.measurable_stopped_process
- \+ *lemma* measure_theory.prog_measurable.stopped_process
- \+ *def* measure_theory.prog_measurable
- \+ *lemma* measure_theory.prog_measurable_const
- \+ *lemma* measure_theory.prog_measurable_min_stopping_time
- \+ *lemma* measure_theory.prog_measurable_of_tendsto'
- \+ *lemma* measure_theory.prog_measurable_of_tendsto



## [2022-03-07 18:31:04](https://github.com/leanprover-community/mathlib/commit/e871be2)
feat(data/real/nnreal): floor_semiring instance ([#12495](https://github.com/leanprover-community/mathlib/pull/12495))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60nat.2Eceil.60.20on.20.60nnreal.60.20.3F/near/274353230)
#### Estimated changes
Modified src/algebra/order/floor.lean


Modified src/algebra/order/nonneg.lean
- \+ *lemma* nonneg.nat_ceil_coe
- \+ *lemma* nonneg.nat_floor_coe

Modified src/data/real/nnreal.lean




## [2022-03-07 18:31:03](https://github.com/leanprover-community/mathlib/commit/8d2ffb8)
feat(category_theory): (co)kernels of biproduct projection and inclusion ([#12394](https://github.com/leanprover-community/mathlib/pull/12394))
add kernels and cokernels of biproduct projections and inclusions
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.biprod.fst_kernel_fork
- \+ *lemma* category_theory.limits.biprod.fst_kernel_fork_ι
- \+ *def* category_theory.limits.biprod.inl_cokernel_fork
- \+ *lemma* category_theory.limits.biprod.inl_cokernel_fork_π
- \+ *def* category_theory.limits.biprod.inr_cokernel_fork
- \+ *lemma* category_theory.limits.biprod.inr_cokernel_fork_π
- \+ *def* category_theory.limits.biprod.is_cokernel_inl_cokernel_fork
- \+ *def* category_theory.limits.biprod.is_cokernel_inr_cokernel_fork
- \+ *def* category_theory.limits.biprod.is_kernel_fst_kernel_fork
- \+ *def* category_theory.limits.biprod.is_kernel_snd_kernel_fork
- \+ *def* category_theory.limits.biprod.snd_kernel_fork
- \+ *lemma* category_theory.limits.biprod.snd_kernel_fork_ι
- \+ *def* category_theory.limits.biproduct.from_subtype
- \+ *lemma* category_theory.limits.biproduct.from_subtype_eq_lift
- \+ *lemma* category_theory.limits.biproduct.from_subtype_to_subtype
- \+ *lemma* category_theory.limits.biproduct.from_subtype_π
- \+ *lemma* category_theory.limits.biproduct.from_subtype_π_subtype
- \+ *def* category_theory.limits.biproduct.is_colimit_to_subtype
- \+ *def* category_theory.limits.biproduct.is_limit_from_subtype
- \+/\- *lemma* category_theory.limits.biproduct.lift_map
- \+/\- *abbreviation* category_theory.limits.biproduct.map'
- \+/\- *abbreviation* category_theory.limits.biproduct.map
- \+/\- *lemma* category_theory.limits.biproduct.map_desc
- \+/\- *lemma* category_theory.limits.biproduct.map_eq_map'
- \+/\- *def* category_theory.limits.biproduct.map_iso
- \+/\- *lemma* category_theory.limits.biproduct.map_π
- \+ *def* category_theory.limits.biproduct.to_subtype
- \+ *lemma* category_theory.limits.biproduct.to_subtype_eq_desc
- \+ *lemma* category_theory.limits.biproduct.to_subtype_from_subtype
- \+ *lemma* category_theory.limits.biproduct.to_subtype_π
- \+ *lemma* category_theory.limits.biproduct.ι_from_subtype
- \+/\- *lemma* category_theory.limits.biproduct.ι_map
- \+ *lemma* category_theory.limits.biproduct.ι_to_subtype
- \+ *lemma* category_theory.limits.biproduct.ι_to_subtype_subtype



## [2022-03-07 18:01:16](https://github.com/leanprover-community/mathlib/commit/85a415e)
docs(overview): Add overview of model theory ([#12496](https://github.com/leanprover-community/mathlib/pull/12496))
Adds a subsection on model theory to the mathlib overview.
#### Estimated changes
Modified docs/overview.yaml




## [2022-03-07 16:01:41](https://github.com/leanprover-community/mathlib/commit/3c3c3bc)
fix(tactic/interactive): use non-interactive admit tactic ([#12489](https://github.com/leanprover-community/mathlib/pull/12489))
In a future release of Lean 3, the interactive admit tactic will take an additional argument.
#### Estimated changes
Modified src/tactic/interactive.lean




## [2022-03-07 16:01:39](https://github.com/leanprover-community/mathlib/commit/5f2a6ac)
feat(measure_theory/integral/periodic): further properties of periodic integrals ([#12488](https://github.com/leanprover-community/mathlib/pull/12488))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+ *lemma* int.fract_div_mul_self_add_zsmul_eq
- \+ *lemma* int.fract_div_mul_self_mem_Ico

Modified src/measure_theory/integral/periodic.lean
- \+ *lemma* function.periodic.Inf_add_zsmul_le_integral_of_pos
- \+/\- *lemma* function.periodic.interval_integral_add_eq
- \+ *lemma* function.periodic.interval_integral_add_eq_add
- \+/\- *lemma* function.periodic.interval_integral_add_eq_of_pos
- \+ *lemma* function.periodic.interval_integral_add_zsmul_eq
- \+ *lemma* function.periodic.tendsto_at_top_interval_integral_of_pos'
- \+ *lemma* function.periodic.tendsto_at_top_interval_integral_of_pos
- \+/\- *lemma* is_add_fundamental_domain_Ioc

Modified src/topology/algebra/order/compact.lean
- \+ *lemma* continuous_on.Inf_image_Icc_le
- \+/\- *lemma* continuous_on.image_Icc
- \+/\- *lemma* continuous_on.image_interval
- \+/\- *lemma* continuous_on.image_interval_eq_Icc
- \+ *lemma* continuous_on.le_Sup_image_Icc



## [2022-03-07 16:01:38](https://github.com/leanprover-community/mathlib/commit/c95ce52)
fix(number_theory/modular): prefer `coe` over `coe_fn` in lemma statements ([#12445](https://github.com/leanprover-community/mathlib/pull/12445))
This file is already full of `↑ₘ`s (aka coercions to matrix), we may as well use them uniformly.
#### Estimated changes
Modified src/number_theory/modular.lean




## [2022-03-07 14:11:59](https://github.com/leanprover-community/mathlib/commit/f451e09)
chore(algebra/order/{group,monoid}): trivial lemma about arithmetic on `with_top` and `with_bot` ([#12491](https://github.com/leanprover-community/mathlib/pull/12491))
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* with_top.coe_neg

Modified src/algebra/order/monoid.lean
- \+ *lemma* with_bot.coe_eq_one
- \- *lemma* with_bot.coe_eq_zero
- \- *lemma* with_bot.coe_zero



## [2022-03-07 14:11:57](https://github.com/leanprover-community/mathlib/commit/65ac316)
chore(algebra/order/nonneg): add `nonneg.coe_nat_cast` ([#12490](https://github.com/leanprover-community/mathlib/pull/12490))
#### Estimated changes
Modified src/algebra/order/nonneg.lean




## [2022-03-07 14:11:56](https://github.com/leanprover-community/mathlib/commit/16b6766)
feat(analysis/normed_space): non-unital normed rings ([#12326](https://github.com/leanprover-community/mathlib/pull/12326))
On the way to allowing non-unital C^*-algebras.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/normed/normed_field.lean




## [2022-03-07 14:11:55](https://github.com/leanprover-community/mathlib/commit/9ed4366)
feat(category_theory/limits): limit preservation properties of functor.left_op and similar ([#12168](https://github.com/leanprover-community/mathlib/pull/12168))
#### Estimated changes
Added src/category_theory/limits/preserves/opposites.lean
- \+ *def* category_theory.limits.perserves_colimits_op
- \+ *def* category_theory.limits.preserves_colimit_left_op
- \+ *def* category_theory.limits.preserves_colimit_op
- \+ *def* category_theory.limits.preserves_colimit_right_op
- \+ *def* category_theory.limits.preserves_colimit_unop
- \+ *def* category_theory.limits.preserves_colimits_left_op
- \+ *def* category_theory.limits.preserves_colimits_of_shape_left_op
- \+ *def* category_theory.limits.preserves_colimits_of_shape_op
- \+ *def* category_theory.limits.preserves_colimits_of_shape_right_op
- \+ *def* category_theory.limits.preserves_colimits_of_shape_unop
- \+ *def* category_theory.limits.preserves_colimits_right_op
- \+ *def* category_theory.limits.preserves_colimits_unop
- \+ *def* category_theory.limits.preserves_finite_colimits_left_op
- \+ *def* category_theory.limits.preserves_finite_colimits_op
- \+ *def* category_theory.limits.preserves_finite_colimits_right_op
- \+ *def* category_theory.limits.preserves_finite_colimits_unop
- \+ *def* category_theory.limits.preserves_finite_limits_left_op
- \+ *def* category_theory.limits.preserves_finite_limits_op
- \+ *def* category_theory.limits.preserves_finite_limits_right_op
- \+ *def* category_theory.limits.preserves_finite_limits_unop
- \+ *def* category_theory.limits.preserves_limit_left_op
- \+ *def* category_theory.limits.preserves_limit_op
- \+ *def* category_theory.limits.preserves_limit_right_op
- \+ *def* category_theory.limits.preserves_limit_unop
- \+ *def* category_theory.limits.preserves_limits_left_op
- \+ *def* category_theory.limits.preserves_limits_of_shape_left_op
- \+ *def* category_theory.limits.preserves_limits_of_shape_op
- \+ *def* category_theory.limits.preserves_limits_of_shape_right_op
- \+ *def* category_theory.limits.preserves_limits_of_shape_unop
- \+ *def* category_theory.limits.preserves_limits_op
- \+ *def* category_theory.limits.preserves_limits_right_op
- \+ *def* category_theory.limits.preserves_limits_unop



## [2022-03-07 12:17:08](https://github.com/leanprover-community/mathlib/commit/900ce6f)
chore(data/equiv/basic): rename `involutive.to_equiv` to `to_perm` ([#12486](https://github.com/leanprover-community/mathlib/pull/12486))
#### Estimated changes
Modified src/algebra/quandle.lean


Modified src/algebra/star/basic.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.perm
- \+ *lemma* function.involutive.coe_to_perm
- \- *def* function.involutive.to_equiv
- \+ *def* function.involutive.to_perm
- \+ *lemma* function.involutive.to_perm_involutive
- \+ *lemma* function.involutive.to_perm_symm

Modified src/data/equiv/module.lean


Modified src/data/equiv/mul_add.lean




## [2022-03-07 10:15:48](https://github.com/leanprover-community/mathlib/commit/eb46e7e)
feat(algebra/group/to_additive): let to_additive turn `pow` into `nsmul` ([#12477](https://github.com/leanprover-community/mathlib/pull/12477))
The naming convention for `npow` in lemma names is `pow`, so let’s teach
`to_additive` about it.
A fair number of lemmas now no longer need an explicit additive name.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/group/hom.lean
- \+/\- *theorem* map_pow

Modified src/algebra/group/pi.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* inv_pow

Modified src/algebra/group_power/order.lean


Modified src/algebra/iterate_hom.lean


Modified src/algebra/pointwise.lean


Modified src/group_theory/exponent.lean


Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* pow_eq_mod_card

Modified src/group_theory/submonoid/membership.lean
- \+/\- *theorem* submonoid.coe_pow
- \+/\- *lemma* submonoid.pow_mem

Modified src/number_theory/divisors.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.pow_comp



## [2022-03-07 10:15:47](https://github.com/leanprover-community/mathlib/commit/d704f27)
refactor(set_theory/*): `o.out.r` → `<` ([#12468](https://github.com/leanprover-community/mathlib/pull/12468))
We declare a `linear_order` instance on `o.out.α`, for `o : ordinal`, with `<` def-eq to `o.out.r`. This will improve code clarity and will allow us to state theorems about specific ordinals as ordered structures.
#### Estimated changes
Modified src/measure_theory/card_measurable_space.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/game/nim.lean
- \+ *def* ordinal.out'
- \- *def* ordinal.out
- \- *theorem* ordinal.type_out'
- \+/\- *lemma* pgame.nim.nim_wf_lemma

Modified src/set_theory/ordinal.lean
- \+/\- *lemma* cardinal.card_typein_out_lt
- \+/\- *def* ordinal.initial_seg_out
- \+/\- *def* ordinal.principal_seg_out
- \+/\- *def* ordinal.rel_iso_out
- \+ *lemma* ordinal.type_lt
- \- *theorem* ordinal.type_lt
- \+ *theorem* ordinal.type_lt_iff
- \- *lemma* ordinal.type_out
- \+/\- *theorem* ordinal.typein_lt_self

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.lsub_typein
- \+/\- *theorem* ordinal.sup_typein_succ

Modified src/set_theory/principal.lean




## [2022-03-07 10:15:46](https://github.com/leanprover-community/mathlib/commit/9dd8ec1)
feat(analysis/normed/group/hom): add a module instance ([#12465](https://github.com/leanprover-community/mathlib/pull/12465))
#### Estimated changes
Modified src/analysis/normed/group/hom.lean
- \+ *lemma* normed_group_hom.coe_smul
- \+ *lemma* normed_group_hom.smul_apply



## [2022-03-07 10:15:45](https://github.com/leanprover-community/mathlib/commit/0b86bb8)
feat(measure_theory/group/arithmetic): actions by int and nat are measurable ([#12464](https://github.com/leanprover-community/mathlib/pull/12464))
The `has_measurable_smul₂` proofs are essentially copied from the analogous proofs for `has_measurable_pow`, after golfing them.
#### Estimated changes
Modified src/measure_theory/group/arithmetic.lean




## [2022-03-07 10:15:43](https://github.com/leanprover-community/mathlib/commit/3f353db)
feat(data/nat/basic): add one_le_div_iff ([#12461](https://github.com/leanprover-community/mathlib/pull/12461))
Couldn't find these.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_lt_one_iff
- \+ *lemma* nat.one_le_div_iff



## [2022-03-07 10:15:42](https://github.com/leanprover-community/mathlib/commit/2675b5c)
feat(measure_theory/constructions/polish): injective images of Borel sets in Polish spaces are Borel ([#12448](https://github.com/leanprover-community/mathlib/pull/12448))
We prove several fundamental results on the Borel sigma-algebra in Polish spaces, notably:
* Lusin separation theorem: disjoint analytic sets can be separated via Borel sets
* Lusin-Souslin theorem: a continuous injective image of a Borel set in a Polish space is Borel
* An injective measurable map on a Polish space is a measurable embedding, i.e., it maps measurable sets to measurable sets
#### Estimated changes
Modified docs/references.bib


Added src/measure_theory/constructions/polish.lean
- \+ *theorem* continuous.measurable_embedding
- \+ *theorem* continuous_on.measurable_embedding
- \+ *theorem* is_closed.analytic_set
- \+ *theorem* is_closed.measurable_set_image_of_continuous_on_inj_on
- \+ *lemma* is_open.analytic_set_image
- \+ *lemma* measurable.exists_continuous
- \+ *theorem* measurable.measurable_embedding
- \+ *theorem* measurable_set.analytic_set
- \+ *theorem* measurable_set.image_of_continuous_on_inj_on
- \+ *theorem* measurable_set.image_of_measurable_inj_on
- \+ *lemma* measurable_set.is_clopenable
- \+ *theorem* measure_theory.analytic_set.Inter
- \+ *theorem* measure_theory.analytic_set.Union
- \+ *lemma* measure_theory.analytic_set.image_of_continuous
- \+ *lemma* measure_theory.analytic_set.image_of_continuous_on
- \+ *theorem* measure_theory.analytic_set.measurably_separable
- \+ *def* measure_theory.analytic_set
- \+ *lemma* measure_theory.analytic_set_empty
- \+ *theorem* measure_theory.analytic_set_iff_exists_polish_space_range
- \+ *lemma* measure_theory.analytic_set_range_of_polish_space
- \+ *lemma* measure_theory.is_clopenable_iff_measurable_set
- \+ *theorem* measure_theory.measurable_set_range_of_continuous_injective
- \+ *lemma* measure_theory.measurably_separable.Union
- \+ *def* measure_theory.measurably_separable
- \+ *lemma* measure_theory.measurably_separable_range_of_disjoint



## [2022-03-07 10:15:41](https://github.com/leanprover-community/mathlib/commit/3778353)
feat(set_theory/ordinal_arithmetic): `enum_ord univ = id` ([#12391](https://github.com/leanprover-community/mathlib/pull/12391))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.enum_ord_range
- \+ *theorem* ordinal.enum_ord_univ
- \+ *theorem* ordinal.range_enum_ord



## [2022-03-07 10:15:40](https://github.com/leanprover-community/mathlib/commit/313f405)
feat(category_theory/*): preserves biproducts implies additive ([#12014](https://github.com/leanprover-community/mathlib/pull/12014))
#### Estimated changes
Added src/category_theory/limits/preserves/shapes/biproducts.lean
- \+ *def* category_theory.functor.map_bicone
- \+ *def* category_theory.functor.map_binary_bicone
- \+ *def* category_theory.functor.map_biprod
- \+ *lemma* category_theory.functor.map_biprod_hom
- \+ *lemma* category_theory.functor.map_biprod_inv
- \+ *def* category_theory.functor.map_biproduct
- \+ *lemma* category_theory.functor.map_biproduct_hom
- \+ *lemma* category_theory.functor.map_biproduct_inv
- \+ *lemma* category_theory.limits.biprod.lift_map_biprod
- \+ *lemma* category_theory.limits.biprod.map_biprod_hom_desc
- \+ *lemma* category_theory.limits.biprod.map_biprod_inv_map_desc
- \+ *lemma* category_theory.limits.biprod.map_lift_map_biprod
- \+ *lemma* category_theory.limits.biproduct.map_biproduct_hom_desc
- \+ *lemma* category_theory.limits.biproduct.map_biproduct_inv_map_desc
- \+ *lemma* category_theory.limits.biproduct.map_lift_map_biprod
- \+ *def* category_theory.limits.is_bilimit_of_preserves
- \+ *def* category_theory.limits.is_binary_bilimit_of_preserves
- \+ *def* category_theory.limits.preserves_binary_biproduct_of_preserves_binary_coproduct
- \+ *def* category_theory.limits.preserves_binary_biproduct_of_preserves_binary_product
- \+ *def* category_theory.limits.preserves_binary_biproduct_of_preserves_biproduct
- \+ *def* category_theory.limits.preserves_binary_biproducts_of_preserves_binary_coproducts
- \+ *def* category_theory.limits.preserves_binary_biproducts_of_preserves_binary_products
- \+ *def* category_theory.limits.preserves_binary_biproducts_of_preserves_biproducts
- \+ *def* category_theory.limits.preserves_binary_coproduct_of_preserves_binary_biproduct
- \+ *def* category_theory.limits.preserves_binary_coproducts_of_preserves_binary_biproducts
- \+ *def* category_theory.limits.preserves_binary_product_of_preserves_binary_biproduct
- \+ *def* category_theory.limits.preserves_binary_products_of_preserves_binary_biproducts
- \+ *def* category_theory.limits.preserves_biproduct_of_preserves_coproduct
- \+ *def* category_theory.limits.preserves_biproduct_of_preserves_product
- \+ *def* category_theory.limits.preserves_biproducts_of_shape_of_preserves_coproducts_of_shape
- \+ *def* category_theory.limits.preserves_biproducts_of_shape_of_preserves_products_of_shape
- \+ *def* category_theory.limits.preserves_coproduct_of_preserves_biproduct
- \+ *def* category_theory.limits.preserves_coproducts_of_shape_of_preserves_biproducts_of_shape
- \+ *def* category_theory.limits.preserves_product_of_preserves_biproduct
- \+ *def* category_theory.limits.preserves_products_of_shape_of_preserves_biproducts_of_shape

Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/preadditive/additive_functor.lean
- \+ *lemma* category_theory.functor.additive_of_preserves_binary_biproducts
- \- *def* category_theory.functor.map_biproduct



## [2022-03-07 10:15:38](https://github.com/leanprover-community/mathlib/commit/f063d0c)
feat(geometry/manifold/tangent_bundle): the `tangent_bundle` is a `topological_vector_bundle` ([#8295](https://github.com/leanprover-community/mathlib/pull/8295))
#### Estimated changes
Modified src/geometry/manifold/cont_mdiff.lean
- \- *lemma* basic_smooth_bundle_core.cont_mdiff_at_proj
- \- *lemma* basic_smooth_bundle_core.cont_mdiff_on_proj
- \- *lemma* basic_smooth_bundle_core.cont_mdiff_proj
- \- *lemma* basic_smooth_bundle_core.cont_mdiff_within_at_proj
- \- *lemma* basic_smooth_bundle_core.smooth_at_proj
- \- *lemma* basic_smooth_bundle_core.smooth_const_section
- \- *lemma* basic_smooth_bundle_core.smooth_on_proj
- \- *lemma* basic_smooth_bundle_core.smooth_proj
- \- *lemma* basic_smooth_bundle_core.smooth_within_at_proj
- \+ *lemma* basic_smooth_vector_bundle_core.cont_mdiff_at_proj
- \+ *lemma* basic_smooth_vector_bundle_core.cont_mdiff_on_proj
- \+ *lemma* basic_smooth_vector_bundle_core.cont_mdiff_proj
- \+ *lemma* basic_smooth_vector_bundle_core.cont_mdiff_within_at_proj
- \+ *lemma* basic_smooth_vector_bundle_core.smooth_at_proj
- \+ *lemma* basic_smooth_vector_bundle_core.smooth_const_section
- \+ *lemma* basic_smooth_vector_bundle_core.smooth_on_proj
- \+ *lemma* basic_smooth_vector_bundle_core.smooth_proj
- \+ *lemma* basic_smooth_vector_bundle_core.smooth_within_at_proj
- \- *def* tangent_bundle.zero_section

Modified src/geometry/manifold/mfderiv.lean


Renamed src/geometry/manifold/basic_smooth_bundle.lean to src/geometry/manifold/tangent_bundle.lean
- \- *lemma* basic_smooth_bundle_core.base_set
- \- *def* basic_smooth_bundle_core.chart
- \- *lemma* basic_smooth_bundle_core.chart_source
- \- *lemma* basic_smooth_bundle_core.chart_target
- \- *lemma* basic_smooth_bundle_core.coe_chart_at_fst
- \- *lemma* basic_smooth_bundle_core.coe_chart_at_symm_fst
- \- *lemma* basic_smooth_bundle_core.mem_atlas_iff
- \- *lemma* basic_smooth_bundle_core.mem_chart_source_iff
- \- *lemma* basic_smooth_bundle_core.mem_chart_target_iff
- \- *def* basic_smooth_bundle_core.to_topological_fiber_bundle_core
- \- *structure* basic_smooth_bundle_core
- \+ *lemma* basic_smooth_vector_bundle_core.base_set
- \+ *def* basic_smooth_vector_bundle_core.chart
- \+ *lemma* basic_smooth_vector_bundle_core.chart_source
- \+ *lemma* basic_smooth_vector_bundle_core.chart_target
- \+ *lemma* basic_smooth_vector_bundle_core.coe_chart_at_fst
- \+ *lemma* basic_smooth_vector_bundle_core.coe_chart_at_symm_fst
- \+ *lemma* basic_smooth_vector_bundle_core.mem_atlas_iff
- \+ *lemma* basic_smooth_vector_bundle_core.mem_chart_source_iff
- \+ *lemma* basic_smooth_vector_bundle_core.mem_chart_target_iff
- \+ *lemma* basic_smooth_vector_bundle_core.target
- \+ *def* basic_smooth_vector_bundle_core.to_topological_vector_bundle_core
- \+ *structure* basic_smooth_vector_bundle_core
- \+/\- *def* tangent_bundle
- \+/\- *def* tangent_bundle_core
- \+/\- *def* tangent_space
- \- *def* trivial_basic_smooth_bundle_core
- \+ *def* trivial_basic_smooth_vector_bundle_core

Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle_core.base_set_at
- \+ *lemma* topological_vector_bundle_core.local_triv_apply
- \+ *lemma* topological_vector_bundle_core.local_triv_at_def
- \+ *lemma* topological_vector_bundle_core.local_triv_symm_fst
- \+ *lemma* topological_vector_bundle_core.mem_local_triv_at_base_set
- \+/\- *lemma* topological_vector_bundle_core.mem_local_triv_source
- \+ *lemma* topological_vector_bundle_core.mem_local_triv_target
- \+/\- *lemma* topological_vector_bundle_core.mem_source_at
- \+ *def* topological_vector_bundle_core.total_space
- \+ *def* trivial_topological_vector_bundle_core



## [2022-03-07 08:10:23](https://github.com/leanprover-community/mathlib/commit/a19f6c6)
doc(algebra/group/to_additive): `to_additive` and docstring interaction ([#12476](https://github.com/leanprover-community/mathlib/pull/12476))
#### Estimated changes
Modified src/algebra/group/to_additive.lean




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
Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* ideal.mem_homogeneous_core_of_is_homogeneous_of_mem

Added src/ring_theory/graded_algebra/radical.lean
- \+ *lemma* homogeneous_ideal.coe_radical
- \+ *def* homogeneous_ideal.radical
- \+ *lemma* ideal.is_homogeneous.is_prime_iff
- \+ *lemma* ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem
- \+ *lemma* ideal.is_homogeneous.radical
- \+ *lemma* ideal.is_homogeneous.radical_eq
- \+ *lemma* ideal.is_prime.homogeneous_core



## [2022-03-06 18:41:38](https://github.com/leanprover-community/mathlib/commit/40602e6)
chore(set_theory/cardinal_divisibility): add instance unique (units cardinal) ([#12458](https://github.com/leanprover-community/mathlib/pull/12458))
#### Estimated changes
Modified src/set_theory/cardinal_divisibility.lean




## [2022-03-06 15:36:29](https://github.com/leanprover-community/mathlib/commit/6696187)
chore(set_theory/ordinal_arithmetic): Reorder theorems ([#12475](https://github.com/leanprover-community/mathlib/pull/12475))
It makes more sense for `is_normal.bsup_eq` and `is_normal.blsub_eq` to be together.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-03-06 15:06:27](https://github.com/leanprover-community/mathlib/commit/0a6efe0)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a star normal element is its norm ([#12249](https://github.com/leanprover-community/mathlib/pull/12249))
In a C⋆-algebra over ℂ, the spectral radius of any star normal element is its norm. This extends the corresponding result for selfadjoint elements.
- [x] depends on: [#12211](https://github.com/leanprover-community/mathlib/pull/12211) 
- [x] depends on: [#11991](https://github.com/leanprover-community/mathlib/pull/11991)
#### Estimated changes
Modified src/analysis/normed_space/star/spectrum.lean
- \- *lemma* self_adjoint.coe_spectral_radius_eq_nnnorm
- \+ *lemma* spectral_radius_eq_nnnorm_of_star_normal



## [2022-03-06 11:52:53](https://github.com/leanprover-community/mathlib/commit/28c902d)
fix(algebra/group/pi): Fix apply-simp-lemmas for monoid_hom.single ([#12474](https://github.com/leanprover-community/mathlib/pull/12474))
so that the simp-normal form really is `pi.mul_single`.
While adjusting related lemmas in `group_theory.subgroup.basic`, add a
few missing `to_additive` attributes.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* monoid_hom.single_apply
- \+ *lemma* one_hom.single_apply

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.mul_single_mem_pi
- \+ *lemma* subgroup.pi_mem_of_mul_single_mem
- \+ *lemma* subgroup.pi_mem_of_mul_single_mem_aux
- \- *lemma* subgroup.pi_mem_of_single_mem
- \- *lemma* subgroup.pi_mem_of_single_mem_aux
- \- *lemma* subgroup.single_mem_pi



## [2022-03-06 07:44:42](https://github.com/leanprover-community/mathlib/commit/64d953a)
refactor(set_theory/ordinal): `enum_lt` → `enum_lt_enum` ([#12469](https://github.com/leanprover-community/mathlib/pull/12469))
That way, the theorem name matches that of `enum_le_enum`, `typein_lt_typein`, and `typein_le_typein`.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \- *theorem* ordinal.enum_lt
- \+ *theorem* ordinal.enum_lt_enum

Modified src/set_theory/ordinal_arithmetic.lean




## [2022-03-06 07:44:41](https://github.com/leanprover-community/mathlib/commit/d61ebab)
feat(category_theory/abelian): (co)kernels in terms of exact sequences ([#12460](https://github.com/leanprover-community/mathlib/pull/12460))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.comp_epi_desc
- \+ *def* category_theory.abelian.epi_desc
- \+ *def* category_theory.abelian.mono_lift
- \+ *lemma* category_theory.abelian.mono_lift_comp

Modified src/category_theory/abelian/exact.lean
- \+ *lemma* category_theory.abelian.exact_of_is_cokernel
- \+ *lemma* category_theory.abelian.exact_of_is_kernel
- \+ *def* category_theory.abelian.is_colimit_of_exact_of_epi
- \+ *def* category_theory.abelian.is_limit_of_exact_of_mono



## [2022-03-06 07:44:40](https://github.com/leanprover-community/mathlib/commit/b7808a9)
chore(set_theory/ordinal_arithmetic): Golf `lsub_typein` and `blsub_id` ([#12203](https://github.com/leanprover-community/mathlib/pull/12203))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.blsub_id
- \+/\- *theorem* ordinal.bsup_id_limit
- \+/\- *theorem* ordinal.bsup_id_succ
- \+/\- *theorem* ordinal.lsub_typein
- \+/\- *theorem* ordinal.sup_typein_succ



## [2022-03-06 07:44:39](https://github.com/leanprover-community/mathlib/commit/b4d007f)
feat(category_theory/limits): transport is_limit along F.left_op and similar ([#12166](https://github.com/leanprover-community/mathlib/pull/12166))
#### Estimated changes
Modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* category_theory.limits.has_colimit_of_has_limit_left_op
- \+/\- *lemma* category_theory.limits.has_limit_of_has_colimit_left_op
- \+ *def* category_theory.limits.is_colimit_cocone_left_op_of_cone
- \+ *def* category_theory.limits.is_colimit_cocone_of_cone_left_op
- \+ *def* category_theory.limits.is_colimit_cocone_of_cone_right_op
- \+ *def* category_theory.limits.is_colimit_cocone_right_op_of_cone
- \+ *def* category_theory.limits.is_colimit_cocone_unop_of_cone
- \+ *def* category_theory.limits.is_colimit_cone_of_cocone_unop
- \+ *def* category_theory.limits.is_colimit_cone_op
- \+ *def* category_theory.limits.is_colimit_cone_unop
- \+ *def* category_theory.limits.is_limit_cocone_op
- \+ *def* category_theory.limits.is_limit_cocone_unop
- \+ *def* category_theory.limits.is_limit_cone_left_op_of_cocone
- \+ *def* category_theory.limits.is_limit_cone_of_cocone_left_op
- \+ *def* category_theory.limits.is_limit_cone_of_cocone_right_op
- \+ *def* category_theory.limits.is_limit_cone_of_cocone_unop
- \+ *def* category_theory.limits.is_limit_cone_right_op_of_cocone
- \+ *def* category_theory.limits.is_limit_cone_unop_of_cocone



## [2022-03-06 07:44:38](https://github.com/leanprover-community/mathlib/commit/371b48a)
feal(category_theory/bicategory/functor): define pseudofunctors ([#11992](https://github.com/leanprover-community/mathlib/pull/11992))
This PR defines pseudofunctors between bicategories. 
We provide two constructors (`mk_of_oplax` and `mk_of_oplax'`) that construct pseudofunctors from oplax functors whose `map_id` and `map_comp` are isomorphisms. The constructor `mk_of_oplax` uses `iso` to describe isomorphisms, while `mk_of_oplax'` uses `is_iso`.
#### Estimated changes
Modified src/category_theory/bicategory/functor.lean
- \+/\- *def* category_theory.oplax_functor.comp
- \+/\- *def* category_theory.oplax_functor.id
- \+ *structure* category_theory.oplax_functor.pseudo_core
- \+ *lemma* category_theory.oplax_functor.to_prelax_eq_coe
- \+/\- *lemma* category_theory.oplax_functor.to_prelax_functor_map
- \+/\- *lemma* category_theory.oplax_functor.to_prelax_functor_map₂
- \+/\- *lemma* category_theory.oplax_functor.to_prelax_functor_obj
- \+/\- *structure* category_theory.oplax_functor
- \+/\- *def* category_theory.prelax_functor.comp
- \+/\- *def* category_theory.prelax_functor.id
- \+ *lemma* category_theory.prelax_functor.to_prefunctor_eq_coe
- \+/\- *lemma* category_theory.prelax_functor.to_prefunctor_map
- \+/\- *lemma* category_theory.prelax_functor.to_prefunctor_obj
- \+/\- *structure* category_theory.prelax_functor
- \+ *def* category_theory.pseudofunctor.comp
- \+ *def* category_theory.pseudofunctor.id
- \+ *def* category_theory.pseudofunctor.map_functor
- \+ *def* category_theory.pseudofunctor.map₂_associator_aux
- \+ *def* category_theory.pseudofunctor.mk_of_oplax'
- \+ *def* category_theory.pseudofunctor.mk_of_oplax
- \+ *def* category_theory.pseudofunctor.to_oplax
- \+ *lemma* category_theory.pseudofunctor.to_oplax_eq_coe
- \+ *lemma* category_theory.pseudofunctor.to_oplax_map
- \+ *lemma* category_theory.pseudofunctor.to_oplax_map_comp
- \+ *lemma* category_theory.pseudofunctor.to_oplax_map_id
- \+ *lemma* category_theory.pseudofunctor.to_oplax_map₂
- \+ *lemma* category_theory.pseudofunctor.to_oplax_obj
- \+ *lemma* category_theory.pseudofunctor.to_prelax_functor_eq_coe
- \+ *lemma* category_theory.pseudofunctor.to_prelax_functor_map
- \+ *lemma* category_theory.pseudofunctor.to_prelax_functor_map₂
- \+ *lemma* category_theory.pseudofunctor.to_prelax_functor_obj
- \+ *structure* category_theory.pseudofunctor



## [2022-03-06 07:11:07](https://github.com/leanprover-community/mathlib/commit/62e7d35)
feat(category_theory/limits): uniqueness of preadditive structures ([#12342](https://github.com/leanprover-community/mathlib/pull/12342))
#### Estimated changes
Modified src/category_theory/abelian/non_preadditive.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* category_theory.limits.bicone_ι_π_self
- \+ *lemma* category_theory.limits.biprod.add_eq_lift_desc_id
- \+ *lemma* category_theory.limits.biprod.add_eq_lift_id_desc



## [2022-03-05 17:38:12](https://github.com/leanprover-community/mathlib/commit/974d23c)
feat(data/polynomial/monic): add monic_of_mul_monic_left/right ([#12446](https://github.com/leanprover-community/mathlib/pull/12446))
Also clean up variables that are defined in the section.
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60geom_sum.20.28X.20.20n.29.60.20is.20monic/near/274130839
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+/\- *lemma* polynomial.monic.as_sum
- \+ *lemma* polynomial.monic.of_mul_monic_left
- \+ *lemma* polynomial.monic.of_mul_monic_right
- \+/\- *lemma* polynomial.monic_add_of_left
- \+/\- *lemma* polynomial.monic_add_of_right



## [2022-03-05 16:13:55](https://github.com/leanprover-community/mathlib/commit/e542154)
feat(category_theory/full_subcategory): full_subcategory.map and full_subcategory.lift ([#12335](https://github.com/leanprover-community/mathlib/pull/12335))
#### Estimated changes
Modified src/category_theory/full_subcategory.lean
- \+ *lemma* category_theory.full_subcategory.inclusion_map_lift_map
- \+ *lemma* category_theory.full_subcategory.inclusion_obj_lift_obj
- \+ *def* category_theory.full_subcategory.lift
- \+ *def* category_theory.full_subcategory.lift_comp_inclusion
- \+ *lemma* category_theory.full_subcategory.lift_comp_map
- \+ *def* category_theory.full_subcategory.map
- \+ *lemma* category_theory.full_subcategory.map_inclusion

Modified src/category_theory/functor/fully_faithful.lean
- \+ *def* category_theory.full.of_comp_faithful_iso



## [2022-03-05 16:13:54](https://github.com/leanprover-community/mathlib/commit/51adf3a)
feat(model_theory/terms_and_formulas): Using a list encoding, bounds the number of terms ([#12276](https://github.com/leanprover-community/mathlib/pull/12276))
Defines `term.list_encode` and `term.list_decode`, which turn terms into lists, and reads off lists as lists of terms.
Bounds the number of terms by the number of allowed symbols + omega.
#### Estimated changes
Modified src/model_theory/terms_and_formulas.lean
- \+ *theorem* first_order.language.term.card_le
- \+ *def* first_order.language.term.list_decode
- \+ *theorem* first_order.language.term.list_decode_encode_list
- \+ *def* first_order.language.term.list_encode
- \+ *lemma* first_order.language.term.list_encode_injective



## [2022-03-05 15:19:46](https://github.com/leanprover-community/mathlib/commit/92b27e1)
feat(category_theory/discrete_category): generalize universes for comp_nat_iso_discrete ([#12340](https://github.com/leanprover-community/mathlib/pull/12340))
#### Estimated changes
Modified src/category_theory/discrete_category.lean
- \+/\- *def* category_theory.discrete.comp_nat_iso_discrete



## [2022-03-05 15:19:45](https://github.com/leanprover-community/mathlib/commit/4ecd92a)
feat(category_theory/abelian): faithful functors reflect exact sequences ([#12071](https://github.com/leanprover-community/mathlib/pull/12071))
#### Estimated changes
Modified src/algebra/homology/exact.lean
- \+ *lemma* category_theory.functor.exact_of_exact_map'
- \+ *lemma* category_theory.functor.exact_of_exact_map
- \+/\- *lemma* category_theory.mono_iff_exact_zero_left

Modified src/category_theory/abelian/exact.lean


Modified src/category_theory/limits/preserves/shapes/zero.lean
- \+ *lemma* category_theory.functor.map_eq_zero_iff
- \+ *lemma* category_theory.functor.zero_of_map_zero



## [2022-03-05 13:15:02](https://github.com/leanprover-community/mathlib/commit/fa6b16e)
feat(data/nat/prime): add nat.eq_two_pow_or_exists_odd_prime_and_dvd ([#12395](https://github.com/leanprover-community/mathlib/pull/12395))
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.eq_prime_pow_of_unique_prime_dvd
- \+ *lemma* nat.eq_two_pow_or_exists_odd_prime_and_dvd
- \+ *lemma* nat.prime.eq_two_or_odd'



## [2022-03-05 13:15:01](https://github.com/leanprover-community/mathlib/commit/8b91390)
feat(order/hom/basic): add `order_iso.with_{top,bot}_congr` ([#12264](https://github.com/leanprover-community/mathlib/pull/12264))
This adds:
* `with_bot.to_dual_top`
* `with_top.to_dual_bot`
* `order_iso.with_top_congr`
* `order_iso.with_bot_congr`
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* option.map_coe'
- \+ *theorem* option.map_coe

Modified src/order/bounded_order.lean
- \+ *lemma* with_bot.map_bot
- \+ *lemma* with_bot.map_coe
- \+ *lemma* with_top.map_coe
- \+ *lemma* with_top.map_top

Modified src/order/hom/basic.lean
- \+ *def* order_iso.with_bot_congr
- \+ *lemma* order_iso.with_bot_congr_refl
- \+ *lemma* order_iso.with_bot_congr_symm
- \+ *lemma* order_iso.with_bot_congr_trans
- \+ *def* order_iso.with_top_congr
- \+ *lemma* order_iso.with_top_congr_refl
- \+ *lemma* order_iso.with_top_congr_symm
- \+ *lemma* order_iso.with_top_congr_trans
- \+ *lemma* with_bot.to_dual_top_coe
- \+ *lemma* with_bot.to_dual_top_symm_coe
- \+ *lemma* with_top.to_dual_bot_coe
- \+ *lemma* with_top.to_dual_bot_symm_coe



## [2022-03-05 12:17:39](https://github.com/leanprover-community/mathlib/commit/2840532)
doc(topology/uniform_space/cauchy): fix typo ([#12453](https://github.com/leanprover-community/mathlib/pull/12453))
#### Estimated changes
Modified src/topology/uniform_space/cauchy.lean




## [2022-03-05 10:56:08](https://github.com/leanprover-community/mathlib/commit/bda091d)
feat(measure_theory/card_measurable_space): cardinality of generated sigma-algebras ([#12422](https://github.com/leanprover-community/mathlib/pull/12422))
If a sigma-algebra is generated by a set of sets `s` whose cardinality is at most the continuum,
then the sigma-algebra satisfies the same cardinality bound.
#### Estimated changes
Added src/measure_theory/card_measurable_space.lean
- \+ *lemma* measurable_space.cardinal_Union_generate_measurable_rec_le
- \+ *theorem* measurable_space.cardinal_generate_measurable_le
- \+ *theorem* measurable_space.cardinal_generate_measurable_le_continuum
- \+ *lemma* measurable_space.cardinal_generate_measurable_rec_le
- \+ *theorem* measurable_space.cardinal_measurable_set_le
- \+ *theorem* measurable_space.cardinal_measurable_set_le_continuum
- \+ *def* measurable_space.generate_measurable_rec
- \+ *theorem* measurable_space.generate_measurable_subset_rec

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.power_le_power_left
- \+ *theorem* cardinal.self_le_power

Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.add_le_of_le
- \+ *lemma* cardinal.omega_lt_aleph_one

Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.is_regular_aleph_one

Modified src/set_theory/continuum.lean
- \+ *lemma* cardinal.aleph_one_le_continuum

Modified src/set_theory/ordinal.lean




## [2022-03-05 09:10:31](https://github.com/leanprover-community/mathlib/commit/93451af)
feat(order/category/BoolAlg): The category of Boolean algebras ([#12452](https://github.com/leanprover-community/mathlib/pull/12452))
Define `BoolAlg`, the category of Boolean algebras with bounded lattice homs.
#### Estimated changes
Modified src/order/boolean_algebra.lean


Added src/order/category/BoolAlg.lean
- \+ *def* BoolAlg.dual
- \+ *def* BoolAlg.dual_equiv
- \+ *def* BoolAlg.iso.mk
- \+ *def* BoolAlg.of
- \+ *def* BoolAlg.to_BoundedDistribLattice
- \+ *def* BoolAlg
- \+ *lemma* BoolAlg_dual_comp_forget_to_BoundedDistribLattice



## [2022-03-05 09:10:30](https://github.com/leanprover-community/mathlib/commit/f5b885b)
feat(linear_algebra/clifford_algebra/conjugation): reverse and involute are grade-preserving ([#12373](https://github.com/leanprover-community/mathlib/pull/12373))
This shows that various submodules are preserved under `submodule.map` by `reverse` or `involute`.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *lemma* clifford_algebra.even_odd_comap_involute
- \+ *lemma* clifford_algebra.even_odd_comap_reverse
- \+ *lemma* clifford_algebra.even_odd_map_involute
- \+ *lemma* clifford_algebra.even_odd_map_reverse
- \+ *lemma* clifford_algebra.involute_mem_even_odd_iff
- \+ *lemma* clifford_algebra.reverse_mem_even_odd_iff
- \+ *lemma* clifford_algebra.submodule_comap_mul_reverse
- \+ *lemma* clifford_algebra.submodule_comap_pow_reverse
- \+ *lemma* clifford_algebra.submodule_map_involute_eq_comap
- \+ *lemma* clifford_algebra.submodule_map_mul_reverse
- \+ *lemma* clifford_algebra.submodule_map_pow_reverse
- \+ *lemma* clifford_algebra.submodule_map_reverse_eq_comap

Modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* clifford_algebra.ι_mem_even_odd_one



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
Modified src/data/nat/fib.lean
- \+ *def* nat.fast_fib
- \+ *def* nat.fast_fib_aux
- \+ *lemma* nat.fast_fib_aux_bit_ff
- \+ *lemma* nat.fast_fib_aux_bit_tt
- \+ *lemma* nat.fast_fib_aux_eq
- \+ *lemma* nat.fast_fib_eq
- \+ *lemma* nat.fib_add_two_sub_fib_add_one
- \+ *lemma* nat.fib_bit0
- \+ *lemma* nat.fib_bit0_succ
- \+ *lemma* nat.fib_bit1
- \+ *lemma* nat.fib_bit1_succ
- \+ *lemma* nat.fib_two_mul
- \+ *lemma* nat.fib_two_mul_add_one



## [2022-03-05 06:05:25](https://github.com/leanprover-community/mathlib/commit/36a528d)
feat(set_theory/ordinal_arithmetic): `add_le_of_forall_add_lt` ([#12315](https://github.com/leanprover-community/mathlib/pull/12315))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.add_le_of_forall_add_lt



## [2022-03-05 03:06:09](https://github.com/leanprover-community/mathlib/commit/b0d9462)
feat(category_theory/preadditive/injective) : more basic properties and morphisms about injective objects ([#12450](https://github.com/leanprover-community/mathlib/pull/12450))
This pr dualises the rest of `projective.lean`
#### Estimated changes
Modified src/category_theory/preadditive/injective.lean
- \+ *abbreviation* category_theory.injective.d
- \+ *lemma* category_theory.injective.exact.comp_desc
- \+ *def* category_theory.injective.exact.desc
- \+ *def* category_theory.injective.syzygies
- \+ *def* category_theory.injective.under
- \+ *def* category_theory.injective.ι



## [2022-03-05 03:06:08](https://github.com/leanprover-community/mathlib/commit/fdf43f1)
feat(category_theory/closed): generalize some material from cartesian closed categories to closed monoidal categories ([#12386](https://github.com/leanprover-community/mathlib/pull/12386))
No new content, just moving some trivially generalisable material about cartesian closed categories to closed monoidal categories.
I've defined `ihom` for internal hom, and made `exp` an abbreviation for it in the cartesian closed case.
A few other definitions similarly become abbreviations.
I've left the `⟹` arrow for the internal hom in the cartesian closed case, and added `⟶[C]` for the general internal hom.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean


Modified src/category_theory/closed/cartesian.lean
- \+/\- *lemma* category_theory.cartesian_closed.curry_eq
- \+/\- *lemma* category_theory.cartesian_closed.curry_id_eq_coev
- \+/\- *lemma* category_theory.cartesian_closed.uncurry_eq
- \+/\- *lemma* category_theory.cartesian_closed.uncurry_id_eq_ev
- \- *def* category_theory.coev
- \- *lemma* category_theory.coev_ev
- \- *lemma* category_theory.coev_naturality
- \- *def* category_theory.ev
- \- *lemma* category_theory.ev_coev
- \- *lemma* category_theory.ev_naturality
- \+ *abbreviation* category_theory.exp.adjunction
- \- *def* category_theory.exp.adjunction
- \+ *abbreviation* category_theory.exp.coev
- \+ *lemma* category_theory.exp.coev_ev
- \+ *abbreviation* category_theory.exp.ev
- \+ *lemma* category_theory.exp.ev_coev
- \+ *abbreviation* category_theory.exp
- \- *def* category_theory.exp
- \- *lemma* category_theory.exp_adjunction_counit
- \- *lemma* category_theory.exp_adjunction_unit

Modified src/category_theory/closed/functor.lean


Modified src/category_theory/closed/ideal.lean


Modified src/category_theory/closed/monoidal.lean
- \+ *def* category_theory.ihom.adjunction
- \+ *def* category_theory.ihom.coev
- \+ *lemma* category_theory.ihom.coev_ev
- \+ *lemma* category_theory.ihom.coev_naturality
- \+ *def* category_theory.ihom.ev
- \+ *lemma* category_theory.ihom.ev_coev
- \+ *lemma* category_theory.ihom.ev_naturality
- \+ *lemma* category_theory.ihom.ihom_adjunction_counit
- \+ *lemma* category_theory.ihom.ihom_adjunction_unit
- \+ *def* category_theory.ihom
- \+ *lemma* category_theory.monoidal_closed.coev_app_comp_pre_app
- \+ *def* category_theory.monoidal_closed.curry
- \+ *lemma* category_theory.monoidal_closed.curry_eq
- \+ *lemma* category_theory.monoidal_closed.curry_eq_iff
- \+ *lemma* category_theory.monoidal_closed.curry_id_eq_coev
- \+ *lemma* category_theory.monoidal_closed.curry_injective
- \+ *lemma* category_theory.monoidal_closed.curry_natural_left
- \+ *lemma* category_theory.monoidal_closed.curry_natural_right
- \+ *lemma* category_theory.monoidal_closed.curry_uncurry
- \+ *lemma* category_theory.monoidal_closed.eq_curry_iff
- \+ *lemma* category_theory.monoidal_closed.hom_equiv_apply_eq
- \+ *lemma* category_theory.monoidal_closed.hom_equiv_symm_apply_eq
- \+ *lemma* category_theory.monoidal_closed.id_tensor_pre_app_comp_ev
- \+ *def* category_theory.monoidal_closed.internal_hom
- \+ *def* category_theory.monoidal_closed.pre
- \+ *lemma* category_theory.monoidal_closed.pre_id
- \+ *lemma* category_theory.monoidal_closed.pre_map
- \+ *def* category_theory.monoidal_closed.uncurry
- \+ *lemma* category_theory.monoidal_closed.uncurry_curry
- \+ *lemma* category_theory.monoidal_closed.uncurry_eq
- \+ *lemma* category_theory.monoidal_closed.uncurry_id_eq_ev
- \+ *lemma* category_theory.monoidal_closed.uncurry_injective
- \+ *lemma* category_theory.monoidal_closed.uncurry_natural_left
- \+ *lemma* category_theory.monoidal_closed.uncurry_natural_right
- \+ *lemma* category_theory.monoidal_closed.uncurry_pre
- \+ *def* category_theory.tensor_closed
- \+/\- *def* category_theory.unit_closed

Modified src/category_theory/closed/types.lean




## [2022-03-05 01:51:47](https://github.com/leanprover-community/mathlib/commit/45d235e)
feat(analysis/normed_space/star/matrix): `entrywise_sup_norm_bound_of_unitary` ([#12255](https://github.com/leanprover-community/mathlib/pull/12255))
The entrywise sup norm of a unitary matrix is at most 1.
I suspect there is a simpler proof!
#### Estimated changes
Added src/analysis/normed_space/star/matrix.lean
- \+ *lemma* entry_norm_bound_of_unitary
- \+ *lemma* entrywise_sup_norm_bound_of_unitary



## [2022-03-05 01:51:46](https://github.com/leanprover-community/mathlib/commit/1755911)
feat(topology/compacts): The types of clopens and of compact opens ([#11966](https://github.com/leanprover-community/mathlib/pull/11966))
Define `clopens` and ` compact_opens`, the types of clopens and of compact open sets of a topological space.
#### Estimated changes
Modified src/topology/compacts.lean
- \+ *lemma* topological_space.clopens.clopen
- \+ *lemma* topological_space.clopens.coe_bot
- \+ *lemma* topological_space.clopens.coe_compl
- \+ *lemma* topological_space.clopens.coe_inf
- \+ *lemma* topological_space.clopens.coe_mk
- \+ *lemma* topological_space.clopens.coe_sdiff
- \+ *lemma* topological_space.clopens.coe_sup
- \+ *lemma* topological_space.clopens.coe_top
- \+ *def* topological_space.clopens.to_opens
- \+ *structure* topological_space.clopens
- \+ *lemma* topological_space.compact_opens.coe_bot
- \+ *lemma* topological_space.compact_opens.coe_compl
- \+ *lemma* topological_space.compact_opens.coe_inf
- \+ *lemma* topological_space.compact_opens.coe_map
- \+ *lemma* topological_space.compact_opens.coe_mk
- \+ *lemma* topological_space.compact_opens.coe_sdiff
- \+ *lemma* topological_space.compact_opens.coe_sup
- \+ *lemma* topological_space.compact_opens.coe_top
- \+ *lemma* topological_space.compact_opens.compact
- \+ *def* topological_space.compact_opens.map
- \+ *def* topological_space.compact_opens.to_clopens
- \+ *def* topological_space.compact_opens.to_opens
- \+ *lemma* topological_space.compact_opens.«open»
- \+ *structure* topological_space.compact_opens



## [2022-03-05 00:00:54](https://github.com/leanprover-community/mathlib/commit/8e1da4e)
feat(ring_theory/adjoin/basic): if a set of elements of a subobject commute, its closure/adjoin is also commutative ([#12231](https://github.com/leanprover-community/mathlib/pull/12231))
We show that if a set of elements of a subobject commute, its closure/adjoin is also commutative The subobjects include (additive) submonoids, (additive) subgroups, subsemirings, subrings, and subalgebras.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *def* subgroup.closure_comm_group_of_comm
- \+ *lemma* subgroup.closure_induction₂

Modified src/group_theory/submonoid/basic.lean
- \+ *lemma* submonoid.closure_induction₂

Modified src/group_theory/submonoid/membership.lean
- \+ *def* submonoid.closure_comm_monoid_of_comm

Modified src/ring_theory/adjoin/basic.lean
- \+ *def* algebra.adjoin_comm_ring_of_comm
- \+ *def* algebra.adjoin_comm_semiring_of_comm
- \+ *lemma* algebra.adjoin_induction₂

Modified src/ring_theory/subring/basic.lean
- \+ *def* subring.closure_comm_ring_of_comm
- \+ *lemma* subring.closure_induction₂

Modified src/ring_theory/subsemiring/basic.lean
- \+ *def* subsemiring.closure_comm_semiring_of_comm
- \+ *lemma* subsemiring.closure_induction₂



## [2022-03-04 21:44:21](https://github.com/leanprover-community/mathlib/commit/3ac971b)
feat(order/category/Frame): The category of frames ([#12363](https://github.com/leanprover-community/mathlib/pull/12363))
Define `Frame`, the category of frames with frame homomorphisms.
#### Estimated changes
Added src/order/category/Frame.lean
- \+ *abbreviation* Frame.hom
- \+ *def* Frame.iso.mk
- \+ *def* Frame.of
- \+ *def* Frame



## [2022-03-04 21:44:20](https://github.com/leanprover-community/mathlib/commit/ee4be2d)
feat(ring_theory/simple_module): Simple modules as simple objects in the Module category ([#11927](https://github.com/leanprover-community/mathlib/pull/11927))
A simple module is a simple object in the Module category. 
From there it should be easy to write an alternative proof of Schur's lemma for modules using category theory (using the work already done in category_theory/preadditive/schur.lean).
The other direction (a simple object in the Module category is a simple module) hasn't been proved yet.
#### Estimated changes
Modified src/algebra/category/Module/epi_mono.lean
- \+ *def* Module.unique_of_epi_zero

Added src/algebra/category/Module/simple.lean


Modified src/data/pi.lean
- \+ *def* unique_of_surjective_one

Modified src/logic/unique.lean
- \+ *def* function.surjective.unique_of_surjective_const



## [2022-03-04 21:44:19](https://github.com/leanprover-community/mathlib/commit/a07cf6b)
feat(ring_theory/polynomial/homogeneous) : add lemma `homogeneous_component_homogeneous_polynomial` ([#10113](https://github.com/leanprover-community/mathlib/pull/10113))
add the following lemma
```lean
lemma homogeneous_component_homogeneous_polynomial (m n : ℕ)
  (p : mv_polynomial σ R) (h : p ∈ homogeneous_submodule σ R n) :
  homogeneous_component m p = if m = n then p else 0
```
#### Estimated changes
Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* mv_polynomial.homogeneous_component_homogeneous_polynomial



## [2022-03-04 19:43:16](https://github.com/leanprover-community/mathlib/commit/34d8ff1)
feat(topology/algebra/weak_dual): generalize to weak topologies for arbitrary dualities ([#12284](https://github.com/leanprover-community/mathlib/pull/12284))
#### Estimated changes
Modified src/analysis/normed_space/weak_dual.lean


Modified src/topology/algebra/module/weak_dual.lean
- \+ *lemma* bilin_embedding
- \+ *lemma* coe_fn_continuous
- \+ *lemma* continuous_of_continuous_eval
- \+ *lemma* dual_pairing_apply
- \+ *lemma* eval_continuous
- \+ *theorem* tendsto_iff_forall_eval_tendsto
- \+ *def* top_dual_pairing
- \+ *def* weak_bilin
- \- *lemma* weak_dual.coe_fn_continuous
- \- *lemma* weak_dual.coe_fn_embedding
- \- *lemma* weak_dual.continuous_of_continuous_eval
- \- *lemma* weak_dual.eval_continuous
- \- *theorem* weak_dual.tendsto_iff_forall_eval_tendsto
- \+/\- *def* weak_dual
- \+ *def* weak_space



## [2022-03-04 19:43:15](https://github.com/leanprover-community/mathlib/commit/89654c0)
feat(data/equiv/{mul_add,ring}): Coercions to types of morphisms from their `_class` ([#12243](https://github.com/leanprover-community/mathlib/pull/12243))
Add missing coercions to `α ≃+ β`, `α ≃* β`, `α ≃+* β` from `add_equiv_class`, `mul_equiv_class`, `ring_equiv_class`.
#### Estimated changes
Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/ring.lean




## [2022-03-04 17:34:12](https://github.com/leanprover-community/mathlib/commit/30d63cd)
feat(field_theory/cardinality): a cardinal can have a field structure iff it is a prime power ([#12442](https://github.com/leanprover-community/mathlib/pull/12442))
#### Estimated changes
Modified src/field_theory/cardinality.lean
- \+ *lemma* field.nonempty_iff



## [2022-03-04 17:34:11](https://github.com/leanprover-community/mathlib/commit/858002b)
feat(algebra/char_zero): cast(_pow)_eq_one ([#12429](https://github.com/leanprover-community/mathlib/pull/12429))
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *theorem* nat.cast_eq_one
- \+ *theorem* nat.cast_ne_one
- \+ *lemma* nat.cast_pow_eq_one



## [2022-03-04 17:34:10](https://github.com/leanprover-community/mathlib/commit/a54dd9e)
feat(order/category/BoundedDistribLattice): The category of bounded distributive lattices ([#12347](https://github.com/leanprover-community/mathlib/pull/12347))
Define `BoundedDistribLattice`, the category of bounded distributive lattices with bounded lattice homomorphisms.
#### Estimated changes
Added src/order/category/BoundedDistribLattice.lean
- \+ *lemma* BoundedDistribLattice.coe_of
- \+ *lemma* BoundedDistribLattice.coe_to_BoundedLattice
- \+ *def* BoundedDistribLattice.dual
- \+ *def* BoundedDistribLattice.dual_equiv
- \+ *lemma* BoundedDistribLattice.forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice
- \+ *def* BoundedDistribLattice.iso.mk
- \+ *def* BoundedDistribLattice.of
- \+ *def* BoundedDistribLattice.to_BoundedLattice
- \+ *structure* BoundedDistribLattice
- \+ *lemma* BoundedDistribLattice_dual_comp_forget_to_DistribLattice

Modified src/order/category/DistribLattice.lean




## [2022-03-04 17:34:09](https://github.com/leanprover-community/mathlib/commit/fab59cb)
feat(set_theory/cofinality): `cof_eq_Inf_lsub` ([#12314](https://github.com/leanprover-community/mathlib/pull/12314))
This much nicer characterization of cofinality will allow us to prove various theorems relating it to `lsub` and `blsub`.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.mk_ordinal_out

Modified src/set_theory/cofinality.lean
- \+ *theorem* ordinal.cof_eq_Inf_lsub
- \+ *theorem* ordinal.cof_lsub_def_nonempty



## [2022-03-04 17:34:07](https://github.com/leanprover-community/mathlib/commit/efd9a16)
refactor(group_theory/commutator): Define commutators of subgroups in terms of commutators of elements ([#12309](https://github.com/leanprover-community/mathlib/pull/12309))
This PR defines commutators of elements of groups.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* commutator_element_def

Modified src/group_theory/abelianization.lean
- \+/\- *lemma* commutator_eq_closure

Modified src/group_theory/commutator.lean
- \+ *lemma* commutator_element_inv
- \+ *lemma* conjugate_commutator_element
- \+ *lemma* map_commutator_element

Modified src/group_theory/nilpotent.lean


Modified src/tactic/group.lean


Modified test/group.lean
- \- *def* commutator3
- \- *def* commutator



## [2022-03-04 17:34:06](https://github.com/leanprover-community/mathlib/commit/35b835a)
feat(data/set/sigma): Indexed sum of sets ([#12305](https://github.com/leanprover-community/mathlib/pull/12305))
Define `set.sigma`, the sum of a family of sets indexed by a set.
#### Estimated changes
Modified src/data/finset/sigma.lean
- \+ *lemma* finset.coe_sigma

Added src/data/set/sigma.lean
- \+ *lemma* set.empty_sigma
- \+ *lemma* set.exists_sigma_iff
- \+ *lemma* set.forall_sigma_iff
- \+ *lemma* set.fst_image_sigma
- \+ *lemma* set.fst_image_sigma_subset
- \+ *lemma* set.image_sigma_mk_subset_sigma_left
- \+ *lemma* set.image_sigma_mk_subset_sigma_right
- \+ *lemma* set.insert_sigma
- \+ *lemma* set.mem_sigma_iff
- \+ *lemma* set.mk_mem_sigma
- \+ *lemma* set.mk_preimage_sigma
- \+ *lemma* set.mk_preimage_sigma_eq_empty
- \+ *lemma* set.mk_preimage_sigma_eq_if
- \+ *lemma* set.mk_preimage_sigma_fn_eq_if
- \+ *lemma* set.mk_sigma_iff
- \+ *lemma* set.nonempty.sigma_fst
- \+ *lemma* set.nonempty.sigma_snd
- \+ *lemma* set.preimage_sigma_map_sigma
- \+ *lemma* set.sigma_diff_sigma
- \+ *lemma* set.sigma_empty
- \+ *lemma* set.sigma_eq_empty_iff
- \+ *lemma* set.sigma_insert
- \+ *lemma* set.sigma_inter_sigma
- \+ *lemma* set.sigma_mono
- \+ *lemma* set.sigma_nonempty_iff
- \+ *lemma* set.sigma_preimage_eq
- \+ *lemma* set.sigma_preimage_left
- \+ *lemma* set.sigma_preimage_right
- \+ *lemma* set.sigma_singleton
- \+ *lemma* set.sigma_subset_iff
- \+ *lemma* set.sigma_subset_preimage_fst
- \+ *lemma* set.sigma_union
- \+ *lemma* set.sigma_univ
- \+ *lemma* set.sigma_univ_range_eq
- \+ *lemma* set.singleton_sigma
- \+ *lemma* set.singleton_sigma_singleton
- \+ *lemma* set.union_sigma
- \+ *lemma* set.univ_sigma_univ

Modified src/logic/basic.lean
- \+ *lemma* imp_iff_not_or
- \- *theorem* imp_iff_not_or
- \+ *lemma* imp_iff_or_not
- \+ *lemma* not_or_of_imp
- \- *theorem* not_or_of_imp
- \+ *lemma* or_not_of_imp



## [2022-03-04 17:34:05](https://github.com/leanprover-community/mathlib/commit/ed63386)
feat(category_theory/preadditive/injective) : definition of injective objects in a category ([#11921](https://github.com/leanprover-community/mathlib/pull/11921))
This pr contains definition of injective objects and some useful instances.
#### Estimated changes
Added src/category_theory/preadditive/injective.lean
- \+ *lemma* category_theory.injective.comp_factor_thru
- \+ *def* category_theory.injective.factor_thru
- \+ *lemma* category_theory.injective.iso_iff
- \+ *lemma* category_theory.injective.of_iso
- \+ *structure* category_theory.injective_presentation



## [2022-03-04 17:34:04](https://github.com/leanprover-community/mathlib/commit/a8629a5)
refactor(tactic/interactive): use 1-indexing in work_on_goal ([#11813](https://github.com/leanprover-community/mathlib/pull/11813))
Backporting the change in https://github.com/leanprover-community/mathlib4/pull/178 to make `work_on_goal` 1-indexed. See also: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60work_on_goal.60.20vs.20.60swap.60
#### Estimated changes
Modified archive/100-theorems-list/73_ascending_descending_sequences.lean


Modified src/algebra/algebra/operations.lean


Modified src/combinatorics/hales_jewett.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/group_theory/submonoid/pointwise.lean


Modified src/linear_algebra/alternating.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/tactic/chain.lean


Modified src/tactic/interactive.lean


Modified test/swap_var.lean


Modified test/tidy.lean




## [2022-03-04 15:24:38](https://github.com/leanprover-community/mathlib/commit/0ec8e6a)
feat(algebra/algebra/operations): more lemmas about `mul_opposite` ([#12441](https://github.com/leanprover-community/mathlib/pull/12441))
Naturally the lemmas I left out of the previous PR, notably `map_unop_mul` and `map_unop_pow`, are the ones I actually needed.
This also improves the `simps` lemmas on `submodule.equiv_opposite`, which were previously garbage as `simps` didn't unfold `ring_equiv.symm` properly. At any rate, the only reason it was defined that way was because the lemmas in this PR were missing.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.comap_op_mul
- \+ *lemma* submodule.comap_op_pow
- \+ *lemma* submodule.map_unop_mul
- \+ *lemma* submodule.map_unop_pow



## [2022-03-04 15:24:37](https://github.com/leanprover-community/mathlib/commit/31cb3c1)
chore(algebra/group_with_zero/basic): generalize `units.exists_iff_ne_zero` to arbitrary propositions ([#12439](https://github.com/leanprover-community/mathlib/pull/12439))
This adds a more powerful version of this lemma that allows an existential to be replaced with one over the underlying group with zero.
The naming matches `subtype.exists` and `subtype.exists'`, while the trailing zero matches `units.mk0`.
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* units.exists0'
- \+ *lemma* units.exists0



## [2022-03-04 15:24:36](https://github.com/leanprover-community/mathlib/commit/6e94c53)
feat(complex/basic): nnnorm coercions ([#12428](https://github.com/leanprover-community/mathlib/pull/12428))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.nnnorm_eq_one_of_pow_eq_one
- \+ *lemma* complex.nnnorm_int
- \+ *lemma* complex.nnnorm_nat
- \+ *lemma* complex.nnnorm_real
- \+ *lemma* complex.norm_eq_one_of_pow_eq_one

Modified src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root.nnnorm_eq_one



## [2022-03-04 15:24:34](https://github.com/leanprover-community/mathlib/commit/dc95d02)
feat(order/filter/archimedean): add lemmas about convergence to ±∞ for archimedean rings / groups. ([#12427](https://github.com/leanprover-community/mathlib/pull/12427))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/order/filter/archimedean.lean
- \+ *lemma* filter.tendsto.at_bot_mul_const'
- \+ *lemma* filter.tendsto.at_bot_mul_neg_const'
- \+ *lemma* filter.tendsto.at_bot_zsmul_const
- \+ *lemma* filter.tendsto.at_bot_zsmul_neg_const
- \+/\- *lemma* filter.tendsto.at_top_mul_const'
- \+ *lemma* filter.tendsto.at_top_mul_neg_const'
- \+ *lemma* filter.tendsto.at_top_nsmul_const
- \+ *lemma* filter.tendsto.at_top_nsmul_neg_const
- \+ *lemma* filter.tendsto.at_top_zsmul_const
- \+ *lemma* filter.tendsto.at_top_zsmul_neg_const
- \+/\- *lemma* filter.tendsto.const_mul_at_top'

Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.tendsto_at_bot_iff_tends_to_neg_at_top
- \+ *lemma* filter.tendsto_at_top_iff_tends_to_neg_at_bot



## [2022-03-04 15:24:33](https://github.com/leanprover-community/mathlib/commit/e41303d)
feat(category_theory/limits/shapes): preserving (co)kernels ([#12419](https://github.com/leanprover-community/mathlib/pull/12419))
This is work towards showing that homology is a lax monoidal functor.
#### Estimated changes
Modified src/category_theory/limits/is_limit.lean
- \+ *def* category_theory.limits.is_colimit.equiv_of_nat_iso_of_iso
- \+ *def* category_theory.limits.is_limit.equiv_of_nat_iso_of_iso

Modified src/category_theory/limits/preserves/shapes/equalizers.lean


Added src/category_theory/limits/preserves/shapes/kernels.lean
- \+ *def* category_theory.limits.is_colimit_cofork_map_of_is_colimit'
- \+ *def* category_theory.limits.is_colimit_map_cocone_cofork_equiv'
- \+ *def* category_theory.limits.is_colimit_of_has_cokernel_of_preserves_colimit
- \+ *def* category_theory.limits.is_limit_fork_map_of_is_limit'
- \+ *def* category_theory.limits.is_limit_map_cone_fork_equiv'
- \+ *def* category_theory.limits.is_limit_of_has_kernel_of_preserves_limit
- \+ *def* category_theory.limits.preserves_cokernel.iso
- \+ *lemma* category_theory.limits.preserves_cokernel.iso_hom
- \+ *def* category_theory.limits.preserves_cokernel.of_iso_comparison
- \+ *def* category_theory.limits.preserves_kernel.iso
- \+ *lemma* category_theory.limits.preserves_kernel.iso_hom
- \+ *def* category_theory.limits.preserves_kernel.of_iso_comparison

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.parallel_pair.ext

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_comparison
- \+ *lemma* category_theory.limits.cokernel_comparison_map_desc
- \+ *def* category_theory.limits.cokernel_is_cokernel
- \+ *def* category_theory.limits.kernel_comparison
- \+ *lemma* category_theory.limits.kernel_comparison_comp_π
- \+ *def* category_theory.limits.kernel_is_kernel
- \+ *lemma* category_theory.limits.map_lift_kernel_comparison
- \+ *lemma* category_theory.limits.ι_comp_cokernel_comparison



## [2022-03-04 14:03:56](https://github.com/leanprover-community/mathlib/commit/2d6c52a)
feat(topology/metric_space/polish): definition and basic properties of polish spaces ([#12437](https://github.com/leanprover-community/mathlib/pull/12437))
A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this PR, we establish basic (and not so basic) properties of Polish spaces.
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* embedding.to_isometry
- \+ *lemma* uniform_embedding.to_isometry

Added src/topology/metric_space/polish.lean
- \+ *lemma* closed_embedding.polish_space
- \+ *lemma* complete_polish_space_metric
- \+ *lemma* equiv.polish_space_induced
- \+ *lemma* is_closed.is_clopenable
- \+ *lemma* is_closed.polish_space
- \+ *lemma* is_open.is_clopenable
- \+ *lemma* is_open.polish_space
- \+ *def* polish_space.aux_copy
- \+ *def* polish_space.complete_copy
- \+ *def* polish_space.complete_copy_id_homeo
- \+ *def* polish_space.complete_copy_metric_space
- \+ *lemma* polish_space.complete_space_complete_copy
- \+ *lemma* polish_space.dist_complete_copy_eq
- \+ *lemma* polish_space.dist_le_dist_complete_copy
- \+ *lemma* polish_space.exists_nat_nat_continuous_surjective
- \+ *lemma* polish_space.exists_polish_space_forall_le
- \+ *def* polish_space.has_dist_complete_copy
- \+ *lemma* polish_space.is_clopenable.Union
- \+ *lemma* polish_space.is_clopenable.compl
- \+ *def* polish_space.is_clopenable
- \+ *def* polish_space_metric
- \+ *def* upgrade_polish_space



## [2022-03-04 14:03:54](https://github.com/leanprover-community/mathlib/commit/0a3d144)
chore(topology/algebra/uniform_mul_action): add `has_uniform_continuous_const_smul.op` ([#12434](https://github.com/leanprover-community/mathlib/pull/12434))
This matches `has_continuous_const_smul.op` and other similar lemmas.
With this in place, we can state `is_central_scalar` on `completion`s.
#### Estimated changes
Modified src/topology/algebra/uniform_mul_action.lean




## [2022-03-04 14:03:53](https://github.com/leanprover-community/mathlib/commit/cac9242)
chore(analysis/complex/basic): golf `norm_rat/int/int_of_nonneg` ([#12433](https://github.com/leanprover-community/mathlib/pull/12433))
While looking at PR [#12428](https://github.com/leanprover-community/mathlib/pull/12428), I found some easy golfing of some lemmas (featuring my first-ever use of `single_pass`! :smile: ).
#### Estimated changes
Modified src/analysis/complex/basic.lean




## [2022-03-04 14:03:51](https://github.com/leanprover-community/mathlib/commit/173f161)
feat(set_theory/ordinal_arithmetic): `bsup` / `blsub` of function composition ([#12381](https://github.com/leanprover-community/mathlib/pull/12381))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.blsub_comp
- \+ *theorem* ordinal.bsup_comp



## [2022-03-04 12:39:06](https://github.com/leanprover-community/mathlib/commit/a721700)
chore(algebra/algebra/operations): add missing `@[elab_as_eliminator]` on recursors ([#12440](https://github.com/leanprover-community/mathlib/pull/12440))
`refine submodule.pow_induction_on' _ _ _ _ h` struggles without this attribute
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/linear_algebra/exterior_algebra/grading.lean


Modified src/linear_algebra/tensor_algebra/grading.lean




## [2022-03-04 12:39:04](https://github.com/leanprover-community/mathlib/commit/4a416bc)
feat(set_theory/ordinal_arithmetic): `is_normal.blsub_eq` ([#12379](https://github.com/leanprover-community/mathlib/pull/12379))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.is_normal.blsub_eq



## [2022-03-04 12:39:03](https://github.com/leanprover-community/mathlib/commit/b144460)
feat(number_theory/cyclotomic/primitive_roots): generalize norm_eq_one ([#12359](https://github.com/leanprover-community/mathlib/pull/12359))
We generalize `norm_eq_one`, that now computes the norm of any primitive `n`-th root of unity if `n ≠ 2`. We modify the assumption, that is still verified in the main case of interest `K = ℚ`.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+/\- *lemma* is_cyclotomic_extension.norm_zeta_eq_one
- \+ *lemma* is_primitive_root.norm_eq_neg_one_pow
- \+/\- *lemma* is_primitive_root.norm_eq_one
- \+ *lemma* is_primitive_root.norm_eq_one_of_linearly_ordered
- \+ *lemma* is_primitive_root.norm_of_cyclotomic_irreducible
- \- *lemma* is_primitive_root.prime_ne_two_pow_sub_one_norm
- \+/\- *lemma* is_primitive_root.sub_one_norm_pow_two
- \+ *lemma* is_primitive_root.sub_one_norm_prime_ne_two



## [2022-03-04 12:39:02](https://github.com/leanprover-community/mathlib/commit/53dc7ca)
feat(linear_algebra/basic): some basic lemmas about dfinsupp.sum ([#12214](https://github.com/leanprover-community/mathlib/pull/12214))
Two basic lemmas about dfinsupp.sum that could be useful (I needed them for another project)
#### Estimated changes
Modified src/data/dfinsupp/basic.lean
- \+ *lemma* dfinsupp.prod_eq_one
- \+ *lemma* dfinsupp.smul_sum



## [2022-03-04 09:26:44](https://github.com/leanprover-community/mathlib/commit/052d027)
refactor(algebra/category/Group/basic): Avoid data shuffle in `mul_equiv.to_Group_iso` ([#12407](https://github.com/leanprover-community/mathlib/pull/12407))
Change the definition of `mul_equiv.to_Group_iso` from `{X Y : Type*} [group X] [group Y] (e : X ≃* Y) : Group.of X ≅ Group.of Y` to `{X Y : Group} (e : X ≃* Y) : X ≅ Y`. Not making `X` and `Y` into `Group`s on the fly avoids rebundling them when they already are `Group`s, which breaks definitional equality.
#### Estimated changes
Modified src/algebra/category/Group/basic.lean
- \+/\- *def* mul_equiv.to_CommGroup_iso
- \+/\- *def* mul_equiv.to_Group_iso
- \+/\- *def* mul_equiv_iso_CommGroup_iso
- \+/\- *def* mul_equiv_iso_Group_iso



## [2022-03-04 09:26:43](https://github.com/leanprover-community/mathlib/commit/0666dd5)
feat(order/bounded): The universal set is unbounded ([#12390](https://github.com/leanprover-community/mathlib/pull/12390))
#### Estimated changes
Modified src/order/bounded.lean
- \+ *theorem* set.unbounded_ge_univ
- \+ *theorem* set.unbounded_gt_univ
- \+ *theorem* set.unbounded_le_univ
- \+ *theorem* set.unbounded_lt_univ



## [2022-03-04 09:26:42](https://github.com/leanprover-community/mathlib/commit/09c66fa)
feat(counterexamples/seminorm_lattice_not_distrib): The lattice of seminorms is not distributive. ([#12099](https://github.com/leanprover-community/mathlib/pull/12099))
A counterexample showing the lattice of seminorms is not distributive
#### Estimated changes
Added counterexamples/seminorm_lattice_not_distrib.lean
- \+ *lemma* seminorm_not_distrib.eq_one
- \+ *lemma* seminorm_not_distrib.not_distrib



## [2022-03-04 08:56:10](https://github.com/leanprover-community/mathlib/commit/82a142d)
feat(algebra/category): Module R is monoidal closed for comm_ring R ([#12387](https://github.com/leanprover-community/mathlib/pull/12387))
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean
- \+ *def* Module.monoidal_closed_hom_equiv



## [2022-03-04 07:06:13](https://github.com/leanprover-community/mathlib/commit/e96cf5e)
feat(data/nat/gcd): add coprime_prod_left and coprime_prod_right ([#12268](https://github.com/leanprover-community/mathlib/pull/12268))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.coprime_prod_left
- \+ *lemma* nat.coprime_prod_right



## [2022-03-03 23:56:18](https://github.com/leanprover-community/mathlib/commit/40524f1)
feat(algebra/star/self_adjoint): define normal elements of a star monoid ([#11991](https://github.com/leanprover-community/mathlib/pull/11991))
In this PR, we define the normal elements of a star monoid, i.e. those elements `x`
that commute with `star x`. This is defined as the prop type class `is_star_normal`.
This was formalized as part of the semilinear maps paper.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* self_adjoint.is_star_normal_of_mem
- \+ *lemma* skew_adjoint.is_star_normal_of_mem
- \+ *lemma* star_comm_self'



## [2022-03-03 23:15:44](https://github.com/leanprover-community/mathlib/commit/544f45b)
refactor(linear_algebra/bilinear_form): split off matrix part ([#12435](https://github.com/leanprover-community/mathlib/pull/12435))
The bilinear form file is way too large. The part that concerns matrices is not depended on by the general theory, and belongs in its own file.
#### Estimated changes
Modified src/algebra/lie/skew_adjoint.lean


Modified src/linear_algebra/bilinear_form.lean
- \- *lemma* basis.equiv_fun_symm_std_basis
- \- *lemma* bilin_form.mul_to_matrix'
- \- *lemma* bilin_form.mul_to_matrix'_mul
- \- *lemma* bilin_form.mul_to_matrix
- \- *lemma* bilin_form.mul_to_matrix_mul
- \- *theorem* bilin_form.nondegenerate.to_matrix'
- \- *theorem* bilin_form.nondegenerate.to_matrix
- \- *lemma* bilin_form.nondegenerate_iff_det_ne_zero
- \- *theorem* bilin_form.nondegenerate_of_det_ne_zero
- \- *lemma* bilin_form.nondegenerate_to_bilin'_iff_det_ne_zero
- \- *theorem* bilin_form.nondegenerate_to_bilin'_of_det_ne_zero'
- \- *theorem* bilin_form.nondegenerate_to_matrix'_iff
- \- *theorem* bilin_form.nondegenerate_to_matrix_iff
- \- *def* bilin_form.to_matrix'
- \- *lemma* bilin_form.to_matrix'_apply
- \- *lemma* bilin_form.to_matrix'_comp
- \- *lemma* bilin_form.to_matrix'_comp_left
- \- *lemma* bilin_form.to_matrix'_comp_right
- \- *lemma* bilin_form.to_matrix'_mul
- \- *lemma* bilin_form.to_matrix'_symm
- \- *lemma* bilin_form.to_matrix'_to_bilin'
- \- *lemma* bilin_form.to_matrix_apply
- \- *def* bilin_form.to_matrix_aux
- \- *lemma* bilin_form.to_matrix_aux_std_basis
- \- *lemma* bilin_form.to_matrix_basis_fun
- \- *lemma* bilin_form.to_matrix_comp
- \- *lemma* bilin_form.to_matrix_comp_left
- \- *lemma* bilin_form.to_matrix_comp_right
- \- *lemma* bilin_form.to_matrix_mul
- \- *lemma* bilin_form.to_matrix_mul_basis_to_matrix
- \- *lemma* bilin_form.to_matrix_symm
- \- *lemma* bilin_form.to_matrix_to_bilin
- \- *lemma* bilinear_form.to_matrix_aux_eq
- \- *lemma* is_adjoint_pair_to_bilin'
- \- *lemma* is_adjoint_pair_to_bilin
- \- *def* matrix.is_adjoint_pair
- \- *lemma* matrix.is_adjoint_pair_equiv
- \- *def* matrix.is_self_adjoint
- \- *def* matrix.is_skew_adjoint
- \- *theorem* matrix.nondegenerate.to_bilin'
- \- *theorem* matrix.nondegenerate.to_bilin
- \- *lemma* matrix.nondegenerate_to_bilin'_iff
- \- *lemma* matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \- *lemma* matrix.nondegenerate_to_bilin_iff
- \- *def* matrix.to_bilin'
- \- *lemma* matrix.to_bilin'_apply'
- \- *lemma* matrix.to_bilin'_apply
- \- *def* matrix.to_bilin'_aux
- \- *lemma* matrix.to_bilin'_aux_eq
- \- *lemma* matrix.to_bilin'_aux_std_basis
- \- *lemma* matrix.to_bilin'_comp
- \- *lemma* matrix.to_bilin'_std_basis
- \- *lemma* matrix.to_bilin'_symm
- \- *lemma* matrix.to_bilin'_to_matrix'
- \- *lemma* matrix.to_bilin_apply
- \- *lemma* matrix.to_bilin_basis_fun
- \- *lemma* matrix.to_bilin_comp
- \- *lemma* matrix.to_bilin_symm
- \- *lemma* matrix.to_bilin_to_matrix
- \- *lemma* mem_pair_self_adjoint_matrices_submodule
- \- *lemma* mem_self_adjoint_matrices_submodule
- \- *lemma* mem_skew_adjoint_matrices_submodule
- \- *def* pair_self_adjoint_matrices_submodule
- \- *def* self_adjoint_matrices_submodule
- \- *def* skew_adjoint_matrices_submodule
- \- *lemma* to_bilin'_aux_to_matrix_aux

Added src/linear_algebra/matrix/bilinear_form.lean
- \+ *lemma* basis.equiv_fun_symm_std_basis
- \+ *lemma* bilin_form.mul_to_matrix'
- \+ *lemma* bilin_form.mul_to_matrix'_mul
- \+ *lemma* bilin_form.mul_to_matrix
- \+ *lemma* bilin_form.mul_to_matrix_mul
- \+ *theorem* bilin_form.nondegenerate.to_matrix'
- \+ *theorem* bilin_form.nondegenerate.to_matrix
- \+ *lemma* bilin_form.nondegenerate_iff_det_ne_zero
- \+ *theorem* bilin_form.nondegenerate_of_det_ne_zero
- \+ *lemma* bilin_form.nondegenerate_to_bilin'_iff_det_ne_zero
- \+ *theorem* bilin_form.nondegenerate_to_bilin'_of_det_ne_zero'
- \+ *theorem* bilin_form.nondegenerate_to_matrix'_iff
- \+ *theorem* bilin_form.nondegenerate_to_matrix_iff
- \+ *def* bilin_form.to_matrix'
- \+ *lemma* bilin_form.to_matrix'_apply
- \+ *lemma* bilin_form.to_matrix'_comp
- \+ *lemma* bilin_form.to_matrix'_comp_left
- \+ *lemma* bilin_form.to_matrix'_comp_right
- \+ *lemma* bilin_form.to_matrix'_mul
- \+ *lemma* bilin_form.to_matrix'_symm
- \+ *lemma* bilin_form.to_matrix'_to_bilin'
- \+ *lemma* bilin_form.to_matrix_apply
- \+ *def* bilin_form.to_matrix_aux
- \+ *lemma* bilin_form.to_matrix_aux_std_basis
- \+ *lemma* bilin_form.to_matrix_basis_fun
- \+ *lemma* bilin_form.to_matrix_comp
- \+ *lemma* bilin_form.to_matrix_comp_left
- \+ *lemma* bilin_form.to_matrix_comp_right
- \+ *lemma* bilin_form.to_matrix_mul
- \+ *lemma* bilin_form.to_matrix_mul_basis_to_matrix
- \+ *lemma* bilin_form.to_matrix_symm
- \+ *lemma* bilin_form.to_matrix_to_bilin
- \+ *lemma* bilinear_form.to_matrix_aux_eq
- \+ *lemma* is_adjoint_pair_to_bilin'
- \+ *lemma* is_adjoint_pair_to_bilin
- \+ *def* matrix.is_adjoint_pair
- \+ *lemma* matrix.is_adjoint_pair_equiv
- \+ *def* matrix.is_self_adjoint
- \+ *def* matrix.is_skew_adjoint
- \+ *theorem* matrix.nondegenerate.to_bilin'
- \+ *theorem* matrix.nondegenerate.to_bilin
- \+ *lemma* matrix.nondegenerate_to_bilin'_iff
- \+ *lemma* matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \+ *lemma* matrix.nondegenerate_to_bilin_iff
- \+ *def* matrix.to_bilin'
- \+ *lemma* matrix.to_bilin'_apply'
- \+ *lemma* matrix.to_bilin'_apply
- \+ *def* matrix.to_bilin'_aux
- \+ *lemma* matrix.to_bilin'_aux_eq
- \+ *lemma* matrix.to_bilin'_aux_std_basis
- \+ *lemma* matrix.to_bilin'_comp
- \+ *lemma* matrix.to_bilin'_std_basis
- \+ *lemma* matrix.to_bilin'_symm
- \+ *lemma* matrix.to_bilin'_to_matrix'
- \+ *lemma* matrix.to_bilin_apply
- \+ *lemma* matrix.to_bilin_basis_fun
- \+ *lemma* matrix.to_bilin_comp
- \+ *lemma* matrix.to_bilin_symm
- \+ *lemma* matrix.to_bilin_to_matrix
- \+ *lemma* mem_pair_self_adjoint_matrices_submodule
- \+ *lemma* mem_self_adjoint_matrices_submodule
- \+ *lemma* mem_skew_adjoint_matrices_submodule
- \+ *def* pair_self_adjoint_matrices_submodule
- \+ *def* self_adjoint_matrices_submodule
- \+ *def* skew_adjoint_matrices_submodule
- \+ *lemma* to_bilin'_aux_to_matrix_aux

Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/ring_theory/trace.lean




## [2022-03-03 21:32:01](https://github.com/leanprover-community/mathlib/commit/5371338)
feat(group_theory/torsion): all torsion monoids are groups ([#12432](https://github.com/leanprover-community/mathlib/pull/12432))
#### Estimated changes
Modified src/group_theory/torsion.lean




## [2022-03-03 21:32:00](https://github.com/leanprover-community/mathlib/commit/1af53ff)
feat(polynomial/cyclotomic): some divisibility results ([#12426](https://github.com/leanprover-community/mathlib/pull/12426))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.not_mem_sdiff_of_not_mem_left

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_dvd

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd
- \+ *lemma* polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd
- \+ *lemma* polynomial.cyclotomic_dvd_geom_sum_of_dvd



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
Modified src/algebra/star/basic.lean
- \+ *lemma* star_int_cast
- \+ *lemma* star_nat_cast
- \+ *lemma* star_rat_cast

Modified src/data/int/cast.lean
- \+ *lemma* mul_opposite.op_int_cast
- \+ *lemma* mul_opposite.unop_int_cast

Modified src/data/nat/cast.lean
- \+ *lemma* mul_opposite.op_nat_cast
- \+ *lemma* mul_opposite.unop_nat_cast

Modified src/data/rat/cast.lean
- \+ *lemma* mul_opposite.op_rat_cast
- \+ *lemma* mul_opposite.unop_rat_cast



## [2022-03-03 21:31:57](https://github.com/leanprover-community/mathlib/commit/9deac65)
feat(ring_theory/ideal): more lemmas on ideals multiplied with submodules ([#12401](https://github.com/leanprover-community/mathlib/pull/12401))
These are, like [#12178](https://github.com/leanprover-community/mathlib/pull/12178), split off from [#12287](https://github.com/leanprover-community/mathlib/pull/12287)
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* submodule.exists_sum_of_mem_ideal_smul_span
- \+ *lemma* submodule.mem_smul_span
- \+ *lemma* submodule.smul_comap_le_comap_smul



## [2022-03-03 21:31:56](https://github.com/leanprover-community/mathlib/commit/2fc2d1b)
feat(linear_algebra/clifford_algebra): lemmas about mapping submodules ([#12399](https://github.com/leanprover-community/mathlib/pull/12399))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.range_neg

Modified src/linear_algebra/clifford_algebra/basic.lean
- \+ *lemma* clifford_algebra.ι_range_map_lift
- \+ *lemma* clifford_algebra.ι_range_map_map

Modified src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *def* clifford_algebra.involute_equiv
- \+ *def* clifford_algebra.reverse_equiv
- \+ *lemma* clifford_algebra.ι_range_comap_involute
- \+ *lemma* clifford_algebra.ι_range_comap_reverse
- \+ *lemma* clifford_algebra.ι_range_map_involute
- \+ *lemma* clifford_algebra.ι_range_map_reverse



## [2022-03-03 21:31:55](https://github.com/leanprover-community/mathlib/commit/e84c1a9)
chore(linear_algebra/general_linear_group): replace coe_fn with coe in lemma statements ([#12397](https://github.com/leanprover-community/mathlib/pull/12397))
This way, all the lemmas are expressed in terms of `↑` and not `⇑`.
This matches the approach used in `special_linear_group`.
#### Estimated changes
Modified src/linear_algebra/general_linear_group.lean
- \+ *lemma* matrix.GL_pos.coe_neg
- \+ *lemma* matrix.GL_pos.coe_neg_apply
- \- *lemma* matrix.GL_pos_coe_neg
- \- *lemma* matrix.GL_pos_neg_elt
- \+/\- *lemma* matrix.general_linear_group.coe_fn_eq_coe



## [2022-03-03 21:31:54](https://github.com/leanprover-community/mathlib/commit/4503732)
feat(field_theory/cardinality): cardinality of fields & localizations ([#12285](https://github.com/leanprover-community/mathlib/pull/12285))
#### Estimated changes
Added src/field_theory/cardinality.lean
- \+ *lemma* fintype.is_prime_pow_card_of_field
- \+ *lemma* fintype.nonempty_field_iff
- \+ *lemma* fintype.not_is_field_of_card_not_prime_pow
- \+ *lemma* infinite.nonempty_field

Modified src/ring_theory/localization/basic.lean
- \+ *def* is_localization.unique_of_zero_mem

Added src/ring_theory/localization/cardinality.lean
- \+ *lemma* is_localization.algebra_map_surjective_of_fintype
- \+ *lemma* is_localization.card
- \+ *lemma* is_localization.card_le



## [2022-03-03 21:31:52](https://github.com/leanprover-community/mathlib/commit/2c0fa82)
feat(group_theory/free_product): the 🏓-lemma ([#12210](https://github.com/leanprover-community/mathlib/pull/12210))
The Ping-Pong-Lemma.
If a group action of `G` on `X` so that the `H i` acts in a specific way on disjoint subsets
`X i` we can prove that `lift f` is injective, and thus the image of `lift f` is isomorphic to the free product of the `H i`.
Often the Ping-Pong-Lemma is stated with regard to subgroups `H i` that generate the whole group; we generalize to arbitrary group homomorphisms `f i : H i →* G` and do not require the group to be generated by the images.
Usually the Ping-Pong-Lemma requires that one group `H i` has at least three elements. This condition is only needed if `# ι = 2`, and we accept `3 ≤ # ι` as an alternative.
#### Estimated changes
Modified src/group_theory/free_product.lean
- \+ *lemma* free_product.empty_of_word_prod_eq_one
- \+ *theorem* free_product.lift_injective_of_ping_pong:
- \+ *lemma* free_product.lift_word_ping_pong
- \+ *lemma* free_product.lift_word_prod_nontrivial_of_head_card
- \+ *lemma* free_product.lift_word_prod_nontrivial_of_head_eq_last
- \+ *lemma* free_product.lift_word_prod_nontrivial_of_not_empty
- \+ *lemma* free_product.lift_word_prod_nontrivial_of_other_i
- \+ *lemma* free_product.neword.append_head
- \+ *lemma* free_product.neword.append_last
- \+ *lemma* free_product.neword.append_prod
- \+ *def* free_product.neword.head
- \+ *def* free_product.neword.inv
- \+ *lemma* free_product.neword.inv_head
- \+ *lemma* free_product.neword.inv_last
- \+ *lemma* free_product.neword.inv_prod
- \+ *def* free_product.neword.last
- \+ *def* free_product.neword.mul_head
- \+ *lemma* free_product.neword.mul_head_head
- \+ *lemma* free_product.neword.mul_head_prod
- \+ *lemma* free_product.neword.of_word
- \+ *def* free_product.neword.prod
- \+ *lemma* free_product.neword.prod_singleton
- \+ *def* free_product.neword.replace_head
- \+ *lemma* free_product.neword.replace_head_head
- \+ *lemma* free_product.neword.singleton_head
- \+ *lemma* free_product.neword.singleton_last
- \+ *def* free_product.neword.to_list
- \+ *lemma* free_product.neword.to_list_head'
- \+ *lemma* free_product.neword.to_list_last'
- \+ *lemma* free_product.neword.to_list_ne_nil
- \+ *def* free_product.neword.to_word
- \+ *inductive* free_product.neword
- \+ *lemma* free_product.word.prod_empty
- \- *lemma* free_product.word.prod_nil



## [2022-03-03 21:31:51](https://github.com/leanprover-community/mathlib/commit/f549c10)
feat(set_theory/cardinal_divisibility): add lemmas about divisibility in the cardinals ([#12197](https://github.com/leanprover-community/mathlib/pull/12197))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.omega_le_mul_iff

Added src/set_theory/cardinal_divisibility.lean
- \+ *lemma* cardinal.dvd_of_le_of_omega_le
- \+ *lemma* cardinal.is_prime_iff
- \+ *lemma* cardinal.is_prime_pow_iff
- \+ *lemma* cardinal.is_unit_iff
- \+ *theorem* cardinal.le_of_dvd
- \+ *lemma* cardinal.nat_coe_dvd_iff
- \+ *lemma* cardinal.nat_is_prime_iff
- \+ *lemma* cardinal.not_irreducible_of_omega_le
- \+ *lemma* cardinal.prime_of_omega_le

Modified src/set_theory/cardinal_ordinal.lean
- \+ *lemma* cardinal.mul_eq_max'



## [2022-03-03 21:31:50](https://github.com/leanprover-community/mathlib/commit/2a05bb3)
feat(ring_theory/witt_vector): classify 1d isocrystals ([#12041](https://github.com/leanprover-community/mathlib/pull/12041))
To show an application of semilinear maps that are not linear or conjugate-linear, we formalized the one-dimensional version of a theorem by Dieudonné and Manin classifying the isocrystals over an algebraically closed field with positive characteristic. This work is described in a recent draft from @dupuisf , @hrmacbeth , and myself: https://arxiv.org/abs/2202.05360
#### Estimated changes
Modified docs/references.bib


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_equiv.smul_of_ne_zero

Added src/ring_theory/witt_vector/frobenius_fraction_field.lean
- \+ *lemma* witt_vector.exists_frobenius_solution_fraction_ring
- \+ *lemma* witt_vector.frobenius_frobenius_rotation
- \+ *def* witt_vector.frobenius_rotation
- \+ *lemma* witt_vector.frobenius_rotation_nonzero
- \+ *def* witt_vector.recursion_base.solution
- \+ *lemma* witt_vector.recursion_base.solution_nonzero
- \+ *lemma* witt_vector.recursion_base.solution_pow
- \+ *lemma* witt_vector.recursion_base.solution_spec'
- \+ *lemma* witt_vector.recursion_base.solution_spec
- \+ *lemma* witt_vector.recursion_main.root_exists
- \+ *def* witt_vector.recursion_main.succ_nth_defining_poly
- \+ *lemma* witt_vector.recursion_main.succ_nth_defining_poly_degree
- \+ *def* witt_vector.recursion_main.succ_nth_val
- \+ *lemma* witt_vector.recursion_main.succ_nth_val_spec'
- \+ *lemma* witt_vector.recursion_main.succ_nth_val_spec

Added src/ring_theory/witt_vector/isocrystal.lean
- \+ *def* witt_vector.fraction_ring.frobenius
- \+ *def* witt_vector.fraction_ring.frobenius_ring_hom
- \+ *def* witt_vector.fraction_ring.module
- \+ *def* witt_vector.isocrystal.frobenius
- \+ *theorem* witt_vector.isocrystal_classification
- \+ *structure* witt_vector.isocrystal_equiv
- \+ *structure* witt_vector.isocrystal_hom
- \+ *lemma* witt_vector.standard_one_dim_isocrystal.frobenius_apply
- \+ *def* witt_vector.standard_one_dim_isocrystal



## [2022-03-03 19:28:04](https://github.com/leanprover-community/mathlib/commit/066ffdb)
chore(algebra/*): provide `non_assoc_ring` instances ([#12414](https://github.com/leanprover-community/mathlib/pull/12414))
#### Estimated changes
Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/graded_monoid.lean


Modified src/algebra/monoid_algebra/basic.lean


Modified src/algebra/symmetrized.lean




## [2022-03-03 19:28:03](https://github.com/leanprover-community/mathlib/commit/5d0960b)
feat(data/int/basic): add three lemmas about ints, nats and int_nat_abs ([#12380](https://github.com/leanprover-community/mathlib/pull/12380))
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/int.2Eto_nat_eq_zero)
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.coe_nat_nonpos_iff
- \+ *lemma* int.to_nat_eq_zero
- \+ *lemma* int.to_nat_neg_nat



## [2022-03-03 19:28:02](https://github.com/leanprover-community/mathlib/commit/cdb69d5)
fix(data/set/function): do not use reducible ([#12377](https://github.com/leanprover-community/mathlib/pull/12377))
Reducible should only be used if the definition if it occurs as an explicit argument in a type class and must reduce during type class search, or if it is a type that should inherit instances.  Propositions should only be reducible if they are trivial variants (`<` and `>` for example).
These reducible attributes here will cause issues in Lean 4.  In Lean 4, the simplifier unfold reducible definitions in simp lemmas.  This means that tagging an `inj_on`-theorem with `@[simp]` creates the simp lemma `?a = ?b` (i.e. match anything).
#### Estimated changes
Modified src/data/set/function.lean
- \+/\- *def* set.bij_on
- \+/\- *def* set.inj_on
- \+/\- *def* set.inv_on
- \+/\- *def* set.left_inv_on
- \+/\- *def* set.maps_to
- \+/\- *def* set.surj_on

Modified src/logic/function/basic.lean
- \+/\- *def* function.injective2



## [2022-03-03 19:28:00](https://github.com/leanprover-community/mathlib/commit/363b7cd)
feat(algebra/ring/basic): generalize lemmas about differences of squares to non-commutative rings ([#12366](https://github.com/leanprover-community/mathlib/pull/12366))
This copies `mul_self_sub_mul_self` and `mul_self_eq_mul_self_iff` to the `commute` namespace, and reproves the existing lemmas in terms of the new commute lemmas.
As a result, the requirements on `mul_self_sub_one` and `mul_self_eq_one_iff` and `units.inv_eq_self_iff` can be weakened from `comm_ring` to `non_unital_non_assoc_ring` or `ring`.
This also replaces a few `is_domain`s with the weaker `no_zero_divisors`, since the lemmas are being moved anyway. In practice this just removes the nontriviality requirements.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* commute.mul_self_eq_mul_self_iff
- \+ *lemma* commute.mul_self_sub_mul_self_eq'
- \+ *lemma* commute.mul_self_sub_mul_self_eq
- \+/\- *lemma* mul_self_eq_mul_self_iff
- \+/\- *lemma* mul_self_eq_one_iff
- \+/\- *theorem* mul_self_sub_mul_self
- \+/\- *lemma* mul_self_sub_one
- \+/\- *lemma* units.inv_eq_self_iff



## [2022-03-03 19:27:59](https://github.com/leanprover-community/mathlib/commit/e823109)
chore(algebra/{group,group_with_zero}/basic): rename `div_mul_div` and `div_mul_comm` ([#12365](https://github.com/leanprover-community/mathlib/pull/12365))
The new name, `div_mul_div_comm` is consistent with `mul_mul_mul_comm`.
Obviously this renames the additive versions too.
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/group/basic.lean
- \- *lemma* div_mul_comm
- \+ *lemma* div_mul_div_comm

Modified src/algebra/group/prod.lean


Modified src/algebra/group_with_zero/basic.lean
- \- *lemma* div_mul_div
- \+ *lemma* div_mul_div_comm₀

Modified src/algebra/order/lattice_group.lean


Modified src/analysis/box_integral/partition/additive.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/trigonometric/complex.lean


Modified src/analysis/specific_limits.lean


Modified src/data/nat/basic.lean
- \- *lemma* nat.div_mul_div
- \+ *lemma* nat.div_mul_div_comm

Modified src/data/nat/prime.lean


Modified src/deprecated/subfield.lean


Modified src/field_theory/ratfunc.lean


Modified src/field_theory/subfield.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/liouville/liouville_with.lean




## [2022-03-03 19:27:58](https://github.com/leanprover-community/mathlib/commit/ca7346d)
feat(combinatorics/simple_graph/connectivity): add walk.darts ([#12360](https://github.com/leanprover-community/mathlib/pull/12360))
Darts can be more convenient than edges when working with walks since they keep track of orientation. This adds the list of darts along a walk and uses this to define and prove things about edges along a walk.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.dart.edge_comp_symm
- \+ *abbreviation* simple_graph.dart.fst
- \+ *abbreviation* simple_graph.dart.snd
- \+ *def* simple_graph.dart_adj
- \+ *lemma* simple_graph.dart_edge_eq_mk_iff'
- \+ *lemma* simple_graph.dart_edge_eq_mk_iff

Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.walk.chain'_adj_support
- \+ *lemma* simple_graph.walk.chain'_dart_adj_darts
- \+/\- *lemma* simple_graph.walk.chain_adj_support
- \- *lemma* simple_graph.walk.chain_adj_support_aux
- \+ *lemma* simple_graph.walk.chain_dart_adj_darts
- \+ *lemma* simple_graph.walk.cons_map_snd_darts
- \+ *lemma* simple_graph.walk.dart_fst_mem_support_of_mem_darts
- \+ *lemma* simple_graph.walk.dart_snd_mem_support_of_mem_darts
- \+ *def* simple_graph.walk.darts
- \+ *lemma* simple_graph.walk.darts_append
- \+ *lemma* simple_graph.walk.darts_bypass_subset
- \+ *lemma* simple_graph.walk.darts_cons
- \+ *lemma* simple_graph.walk.darts_drop_until_subset
- \+ *lemma* simple_graph.walk.darts_nil
- \+ *lemma* simple_graph.walk.darts_nodup_of_support_nodup
- \+ *lemma* simple_graph.walk.darts_reverse
- \+ *lemma* simple_graph.walk.darts_take_until_subset
- \+ *lemma* simple_graph.walk.darts_to_path_subset
- \+/\- *def* simple_graph.walk.edges
- \+/\- *lemma* simple_graph.walk.edges_subset_edge_set
- \+ *lemma* simple_graph.walk.length_darts
- \+ *lemma* simple_graph.walk.map_fst_darts
- \+ *lemma* simple_graph.walk.map_fst_darts_append
- \+ *lemma* simple_graph.walk.map_snd_darts
- \+/\- *lemma* simple_graph.walk.mem_support_of_mem_edges
- \+ *lemma* simple_graph.walk.rotate_darts



## [2022-03-03 19:27:57](https://github.com/leanprover-community/mathlib/commit/3b0111b)
feat(field_theory/minpoly): add minpoly_add_algebra_map and minpoly_sub_algebra_map ([#12357](https://github.com/leanprover-community/mathlib/pull/12357))
We add minpoly_add_algebra_map and minpoly_sub_algebra_map: the minimal polynomial of x ± a.
From flt-regular
#### Estimated changes
Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.monic.comp
- \+ *lemma* polynomial.monic.comp_X_add_C
- \+ *lemma* polynomial.monic.comp_X_sub_C

Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.minpoly_add_algebra_map
- \+ *lemma* minpoly.minpoly_sub_algebra_map



## [2022-03-03 19:27:56](https://github.com/leanprover-community/mathlib/commit/301a266)
feat(number_theory/cyclotomic/primitive_roots): add is_primitive_root.sub_one_power_basis ([#12356](https://github.com/leanprover-community/mathlib/pull/12356))
We add `is_primitive_root.sub_one_power_basis`,  the power basis of a cyclotomic extension given by `ζ - 1`, where `ζ ` is a primitive root of unity.
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_primitive_root.power_basis_gen_mem_adjoin_zeta_sub_one

Modified src/ring_theory/adjoin/power_basis.lean


Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.adjoin_eq_top_of_gen_mem_adjoin
- \+ *lemma* power_basis.adjoin_gen_eq_top



## [2022-03-03 19:27:55](https://github.com/leanprover-community/mathlib/commit/78b323b)
feat(analysis/special_functions/trigonometric): inequality `tan x  > x` ([#12352](https://github.com/leanprover-community/mathlib/pull/12352))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/arctan_deriv.lean


Modified src/analysis/special_functions/trigonometric/basic.lean
- \- *lemma* real.sin_gt_sub_cube
- \- *lemma* real.sin_lt

Added src/analysis/special_functions/trigonometric/bounds.lean
- \+ *lemma* real.deriv_tan_sub_id
- \+ *theorem* real.lt_tan
- \+ *lemma* real.sin_gt_sub_cube
- \+ *lemma* real.sin_lt

Modified src/data/real/pi/bounds.lean




## [2022-03-03 19:27:53](https://github.com/leanprover-community/mathlib/commit/d0816c0)
feat(analysis/calculus): support and cont_diff ([#11976](https://github.com/leanprover-community/mathlib/pull/11976))
* Add some lemmas about the support of the (f)derivative of a function
* Add some equivalences for `cont_diff`
#### Estimated changes
Modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff.continuous_deriv
- \+ *theorem* cont_diff_at_one_iff
- \+ *theorem* cont_diff_one_iff_deriv
- \+ *theorem* cont_diff_one_iff_fderiv
- \+ *theorem* cont_diff_top_iff_deriv

Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_eq
- \+ *lemma* has_compact_support.deriv
- \+ *lemma* support_deriv_subset

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_eq
- \+ *lemma* has_compact_support.fderiv
- \+ *lemma* support_fderiv_subset

Modified src/data/set/lattice.lean
- \+ *lemma* set.antitone_bforall



## [2022-03-03 17:48:13](https://github.com/leanprover-community/mathlib/commit/16d48d7)
feat(algebra/star/basic + analysis/normed_space/star/basic): add two eq_zero/ne_zero lemmas ([#12412](https://github.com/leanprover-community/mathlib/pull/12412))
Added two lemmas about elements being zero or non-zero.
Golf a proof.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+/\- *lemma* star_div
- \+ *lemma* star_eq_zero
- \+ *lemma* star_ne_zero

Modified src/analysis/normed_space/star/basic.lean




## [2022-03-03 17:48:12](https://github.com/leanprover-community/mathlib/commit/3fa09c2)
feat(algebra/homology/homotopy): compatibilities of null_homotopic_map with composition and additive functors ([#12392](https://github.com/leanprover-community/mathlib/pull/12392))
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* homotopy.comp_null_homotopic_map'
- \+ *lemma* homotopy.comp_null_homotopic_map
- \+ *lemma* homotopy.map_null_homotopic_map'
- \+ *lemma* homotopy.map_null_homotopic_map
- \+ *lemma* homotopy.null_homotopic_map'_comp
- \+/\- *lemma* homotopy.null_homotopic_map'_f_eq_zero
- \+ *lemma* homotopy.null_homotopic_map_comp
- \+/\- *lemma* homotopy.null_homotopic_map_f_eq_zero



## [2022-03-03 17:48:10](https://github.com/leanprover-community/mathlib/commit/0da2d1d)
feat(ring_theory/polynomial/eisenstein): add mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at ([#12371](https://github.com/leanprover-community/mathlib/pull/12371))
We add `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at`: let `K` be the field of fraction of an integrally closed domain `R` and let `L` be a separable extension of `K`, generated by an integral power basis `B` such that the minimal polynomial of `B.gen` is Eisenstein at `p`. Given `z : L` integral over `R`, if `p ^ n • z ∈ adjoin R {B.gen}`, then `z ∈ adjoin R {B.gen}`. Together with `algebra.discr_mul_is_integral_mem_adjoin` this result often allows to compute the ring of integers of `L`.
From flt-regular
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* no_zero_smul_divisors.trans

Modified src/data/finset/basic.lean
- \+ *lemma* finset.disjoint_range_add_left_embedding
- \+ *lemma* finset.disjoint_range_add_right_embedding

Modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* mem_adjoin_of_dvd_coeff_of_dvd_aeval
- \+ *lemma* mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at
- \+ *lemma* mem_adjoin_of_smul_prime_smul_of_minpoly_is_eiseinstein_at



## [2022-03-03 17:48:08](https://github.com/leanprover-community/mathlib/commit/b0cf3d7)
feat(algebra/algebra/subalgebra): add a helper to promote submodules to subalgebras ([#12368](https://github.com/leanprover-community/mathlib/pull/12368))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.to_submodule_to_subalgebra
- \+ *lemma* submodule.coe_to_subalgebra
- \+ *lemma* submodule.mem_to_subalgebra
- \+ *def* submodule.to_subalgebra
- \+ *lemma* submodule.to_subalgebra_mk
- \+ *lemma* submodule.to_subalgebra_to_submodule



## [2022-03-03 17:48:05](https://github.com/leanprover-community/mathlib/commit/ba998da)
feat(algebra/order/monoid_lemmas_zero_lt): more lemmas using `pos_mul` and friends ([#12355](https://github.com/leanprover-community/mathlib/pull/12355))
This PR continues the `order` refactor.  The added lemmas are the `\le` analogues of the `<` lemmas that are already present.
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.le_of_mul_le_mul_left'
- \+ *lemma* zero_lt.le_of_mul_le_mul_right'
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_left''
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_right''
- \+ *lemma* zero_lt.mul_le_mul_iff_left
- \+ *lemma* zero_lt.mul_le_mul_iff_right
- \+ *lemma* zero_lt.mul_le_mul_left'
- \+ *lemma* zero_lt.mul_le_mul_right'



## [2022-03-03 17:48:03](https://github.com/leanprover-community/mathlib/commit/5159a8f)
feat(simplex_category): various epi/mono lemmas ([#11924](https://github.com/leanprover-community/mathlib/pull/11924))
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* simplex_category.eq_comp_δ_of_not_surjective'
- \+ *lemma* simplex_category.eq_comp_δ_of_not_surjective
- \+ *lemma* simplex_category.eq_id_of_epi
- \+ *lemma* simplex_category.eq_id_of_is_iso
- \+ *lemma* simplex_category.eq_id_of_mono
- \+ *lemma* simplex_category.eq_δ_of_mono
- \+ *lemma* simplex_category.eq_σ_comp_of_not_injective'
- \+ *lemma* simplex_category.eq_σ_comp_of_not_injective
- \+ *lemma* simplex_category.eq_σ_of_epi
- \+ *lemma* simplex_category.is_iso_of_bijective
- \+ *lemma* simplex_category.iso_eq_iso_refl
- \+ *def* simplex_category.order_iso_of_iso

Modified src/data/fin/basic.lean
- \+ *lemma* fin.cast_succ_lt_iff_succ_le



## [2022-03-03 16:19:52](https://github.com/leanprover-community/mathlib/commit/f41897d)
feat(dynamics/fixed_points/basic): Fixed points are a subset of the range ([#12423](https://github.com/leanprover-community/mathlib/pull/12423))
#### Estimated changes
Modified src/dynamics/fixed_points/basic.lean
- \+ *lemma* function.fixed_points_subset_range



## [2022-03-03 16:19:50](https://github.com/leanprover-community/mathlib/commit/4edf36d)
feat(data/nat/fib): sum of initial fragment of the Fibonacci sequence is one less than a Fibonacci number ([#12416](https://github.com/leanprover-community/mathlib/pull/12416))
#### Estimated changes
Modified src/data/nat/fib.lean
- \+ *lemma* nat.fib_succ_eq_succ_sum



## [2022-03-03 16:19:49](https://github.com/leanprover-community/mathlib/commit/59bf454)
refactor(measure_theory): enable dot notation for measure.map ([#12350](https://github.com/leanprover-community/mathlib/pull/12350))
Refactor to allow for using dot notation with `measure.map` (was previously not possible because it was bundled as a linear map). Mirrors `measure.restrict` wrapper implementation for `measure.restrictₗ`.
#### Estimated changes
Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measurable_embedding.ae_map_iff
- \+/\- *theorem* measurable_embedding.map_apply
- \+/\- *lemma* measurable_embedding.map_comap
- \+/\- *lemma* measurable_equiv.map_apply_eq_iff_map_symm_apply_eq
- \+/\- *lemma* measurable_equiv.map_map_symm
- \+/\- *lemma* measurable_equiv.map_symm_map
- \+/\- *lemma* measurable_equiv.restrict_map
- \+/\- *lemma* measure_theory.ae_of_ae_map
- \+/\- *theorem* measure_theory.measure.le_map_apply
- \+/\- *def* measure_theory.measure.map
- \+ *lemma* measure_theory.measure.map_add
- \+/\- *lemma* measure_theory.measure.map_mono
- \+ *lemma* measure_theory.measure.map_smul
- \+ *lemma* measure_theory.measure.map_zero
- \+ *def* measure_theory.measure.mapₗ
- \+ *lemma* measure_theory.measure.mapₗ_apply
- \+/\- *lemma* measure_theory.measure.quasi_measure_preserving.ae_map_le
- \+/\- *lemma* measure_theory.measure.tendsto_ae_map
- \+/\- *lemma* measure_theory.mem_ae_of_mem_ae_map



## [2022-03-03 16:19:48](https://github.com/leanprover-community/mathlib/commit/c504585)
fix(number_theory/number_field): make ring_of_integers_algebra not an instance ([#12331](https://github.com/leanprover-community/mathlib/pull/12331))
This issue has caused problems for at least two of Kevin's PhD students; it is better to remove it for now or disable it temporarily.
c.f. https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/diamond.20for.20monoid.20instance.20on.20ideals
#### Estimated changes
Modified src/number_theory/number_field.lean
- \+ *def* number_field.ring_of_integers_algebra



## [2022-03-03 16:19:47](https://github.com/leanprover-community/mathlib/commit/0ac3f9d)
feat(category_theory/preadditive): the category of additive functors ([#12330](https://github.com/leanprover-community/mathlib/pull/12330))
#### Estimated changes
Modified src/category_theory/preadditive/additive_functor.lean
- \+ *def* category_theory.AdditiveFunctor.forget
- \+ *lemma* category_theory.AdditiveFunctor.forget_map
- \+ *lemma* category_theory.AdditiveFunctor.forget_obj
- \+ *lemma* category_theory.AdditiveFunctor.forget_obj_of
- \+ *def* category_theory.AdditiveFunctor.of
- \+ *lemma* category_theory.AdditiveFunctor.of_fst
- \+ *def* category_theory.AdditiveFunctor



## [2022-03-03 16:19:46](https://github.com/leanprover-community/mathlib/commit/691722a)
feat(set_theory/ordinal): `enum` is injective ([#12319](https://github.com/leanprover-community/mathlib/pull/12319))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.enum_inj



## [2022-03-03 16:19:45](https://github.com/leanprover-community/mathlib/commit/18f53db)
feat(topology/metric_space/pi_nat): metric structure on product spaces ([#12220](https://github.com/leanprover-community/mathlib/pull/12220))
We endow the spaces `Π (n : ℕ), E n` or `Π (i : ι), E i` with various distances (not registered as instances), and use these to show that these spaces retract on their closed subsets.
#### Estimated changes
Added src/topology/metric_space/pi_nat.lean
- \+ *lemma* exists_nat_nat_continuous_surjective_of_complete_space
- \+ *lemma* pi_countable.dist_eq_tsum
- \+ *lemma* pi_countable.dist_le_dist_pi_of_dist_lt
- \+ *lemma* pi_countable.dist_summable
- \+ *lemma* pi_countable.min_dist_le_dist_pi
- \+ *lemma* pi_nat.Union_cylinder_update
- \+ *lemma* pi_nat.apply_eq_of_dist_lt
- \+ *lemma* pi_nat.apply_eq_of_lt_first_diff
- \+ *lemma* pi_nat.apply_first_diff_ne
- \+ *def* pi_nat.cylinder
- \+ *lemma* pi_nat.cylinder_anti
- \+ *lemma* pi_nat.cylinder_eq_cylinder_of_le_first_diff
- \+ *lemma* pi_nat.cylinder_eq_pi
- \+ *lemma* pi_nat.cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff
- \+ *lemma* pi_nat.cylinder_zero
- \+ *lemma* pi_nat.disjoint_cylinder_of_longest_prefix_lt
- \+ *lemma* pi_nat.dist_eq_of_ne
- \+ *lemma* pi_nat.dist_triangle_nonarch
- \+ *lemma* pi_nat.exists_disjoint_cylinder
- \+ *theorem* pi_nat.exists_lipschitz_retraction_of_is_closed
- \+ *theorem* pi_nat.exists_retraction_of_is_closed
- \+ *theorem* pi_nat.exists_retraction_subtype_of_is_closed
- \+ *def* pi_nat.first_diff
- \+ *lemma* pi_nat.first_diff_comm
- \+ *lemma* pi_nat.first_diff_le_longest_prefix
- \+ *lemma* pi_nat.first_diff_lt_shortest_prefix_diff
- \+ *lemma* pi_nat.inter_cylinder_longest_prefix_nonempty
- \+ *lemma* pi_nat.is_open_iff_dist
- \+ *lemma* pi_nat.is_topological_basis_cylinders
- \+ *lemma* pi_nat.lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder
- \+ *def* pi_nat.longest_prefix
- \+ *lemma* pi_nat.mem_cylinder_comm
- \+ *lemma* pi_nat.mem_cylinder_first_diff
- \+ *lemma* pi_nat.mem_cylinder_iff
- \+ *lemma* pi_nat.mem_cylinder_iff_dist_le
- \+ *lemma* pi_nat.mem_cylinder_iff_eq
- \+ *lemma* pi_nat.mem_cylinder_iff_le_first_diff
- \+ *def* pi_nat.metric_space_nat_nat
- \+ *lemma* pi_nat.min_first_diff_le
- \+ *lemma* pi_nat.self_mem_cylinder
- \+ *def* pi_nat.shortest_prefix_diff
- \+ *lemma* pi_nat.shortest_prefix_diff_pos
- \+ *lemma* pi_nat.update_mem_cylinder



## [2022-03-03 14:50:37](https://github.com/leanprover-community/mathlib/commit/8053f56)
feat(ring_theory/dedekind_domain): strengthen `exist_integer_multiples` ([#12184](https://github.com/leanprover-community/mathlib/pull/12184))
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K` to find a collection of elements of `A` that is not completely contained in `J`.
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal.exist_integer_multiples_not_mem

Modified src/ring_theory/fractional_ideal.lean
- \+ *def* fractional_ideal.span_finset
- \+ *lemma* fractional_ideal.span_finset_eq_zero
- \+ *lemma* fractional_ideal.span_finset_ne_zero



## [2022-03-03 14:50:36](https://github.com/leanprover-community/mathlib/commit/4dec7b5)
feat(ring_theory/ideal): `(I : ideal R) • (⊤ : submodule R M)` ([#12178](https://github.com/leanprover-community/mathlib/pull/12178))
Two useful lemmas on the submodule spanned by `I`-scalar multiples.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.smul_top_eq_map
- \+ *lemma* submodule.map_le_smul_top



## [2022-03-03 13:01:44](https://github.com/leanprover-community/mathlib/commit/26d9d38)
feat(number_theory): padic.complete_space instance ([#12424](https://github.com/leanprover-community/mathlib/pull/12424))
#### Estimated changes
Modified src/number_theory/padics/padic_numbers.lean




## [2022-03-03 13:01:43](https://github.com/leanprover-community/mathlib/commit/bf203b9)
docs(set_theory/cofinality): Fix cofinality definition ([#12421](https://github.com/leanprover-community/mathlib/pull/12421))
The condition is `a ≤ b`, not `¬(b > a)`.
#### Estimated changes
Modified src/set_theory/cofinality.lean




## [2022-03-03 13:01:42](https://github.com/leanprover-community/mathlib/commit/02cad2c)
feat(data/complex/basic): add abs_hom ([#12409](https://github.com/leanprover-community/mathlib/pull/12409))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.abs_prod



## [2022-03-03 13:01:40](https://github.com/leanprover-community/mathlib/commit/bc35902)
chore(algebra/group/hom): more generic `f x ≠ 1` lemmas ([#12404](https://github.com/leanprover-community/mathlib/pull/12404))
 * `map_ne_{one,zero}_iff` is the `not_congr` version of `map_eq_one_iff`, which was previously only available for `mul_equiv_class`
 * `ne_{one,zero}_of_map` is one direction of `map_ne_{one,zero}_iff` that doesn't assume injectivity
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* map_ne_one_iff
- \+ *lemma* ne_one_of_map

Modified src/data/equiv/mul_add.lean




## [2022-03-03 13:01:39](https://github.com/leanprover-community/mathlib/commit/ca0ff3a)
feat(algebra/algebra/spectrum): show the star and spectrum operations commute ([#12351](https://github.com/leanprover-community/mathlib/pull/12351))
This establishes the identity `(σ a)⋆ = σ a⋆` for any `a : A` where `A` is a star ring and a star module over a star add monoid `R`.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* spectrum.star_mem_resolvent_set_iff



## [2022-03-03 13:01:38](https://github.com/leanprover-community/mathlib/commit/f7a6fe9)
feat(set_theory/cofinality): Prove simple theorems on regular cardinals ([#12328](https://github.com/leanprover-community/mathlib/pull/12328))
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.aleph'_succ_is_regular
- \+ *theorem* cardinal.aleph_succ_is_regular
- \+ *lemma* cardinal.is_regular.cof_eq
- \+ *lemma* cardinal.is_regular.omega_le



## [2022-03-03 11:09:23](https://github.com/leanprover-community/mathlib/commit/16ad25c)
chore(analysis/normed_space/star/basic): golf a proof ([#12420](https://github.com/leanprover-community/mathlib/pull/12420))
Shorten a proof using ext.
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean




## [2022-03-03 11:09:21](https://github.com/leanprover-community/mathlib/commit/228ab96)
feat(data/list/destutter): add `list.destutter` to remove chained duplicates ([#11934](https://github.com/leanprover-community/mathlib/pull/11934))
#### Estimated changes
Modified src/data/list/defs.lean
- \+ *def* list.destutter'
- \+ *def* list.destutter

Added src/data/list/destutter.lean
- \+ *lemma* list.destutter'_cons
- \+ *lemma* list.destutter'_cons_neg
- \+ *lemma* list.destutter'_cons_pos
- \+ *lemma* list.destutter'_eq_self_iff
- \+ *lemma* list.destutter'_is_chain'
- \+ *lemma* list.destutter'_is_chain
- \+ *lemma* list.destutter'_ne_nil
- \+ *lemma* list.destutter'_nil
- \+ *lemma* list.destutter'_of_chain
- \+ *lemma* list.destutter'_singleton
- \+ *lemma* list.destutter'_sublist
- \+ *lemma* list.destutter_cons'
- \+ *lemma* list.destutter_cons_cons
- \+ *lemma* list.destutter_eq_nil
- \+ *lemma* list.destutter_eq_self_iff
- \+ *lemma* list.destutter_idem
- \+ *lemma* list.destutter_is_chain'
- \+ *lemma* list.destutter_nil
- \+ *lemma* list.destutter_of_chain'
- \+ *lemma* list.destutter_pair
- \+ *lemma* list.destutter_singleton
- \+ *lemma* list.destutter_sublist
- \+ *lemma* list.mem_destutter'



## [2022-03-03 09:29:13](https://github.com/leanprover-community/mathlib/commit/46b9d05)
feat(data/part): Lemmas for get on binary function instances ([#12194](https://github.com/leanprover-community/mathlib/pull/12194))
A variety of lemmas such as `mul_get_eq` for `part`.
#### Estimated changes
Modified src/data/part.lean
- \+ *lemma* part.append_get_eq
- \+ *lemma* part.div_get_eq
- \+ *lemma* part.inter_get_eq
- \+ *lemma* part.left_dom_of_append_dom
- \+ *lemma* part.left_dom_of_div_dom
- \+ *lemma* part.left_dom_of_inter_dom
- \+ *lemma* part.left_dom_of_mod_dom
- \+ *lemma* part.left_dom_of_mul_dom
- \+ *lemma* part.left_dom_of_sdiff_dom
- \+ *lemma* part.left_dom_of_union_dom
- \+ *lemma* part.mod_get_eq
- \+ *lemma* part.mul_get_eq
- \+ *lemma* part.right_dom_of_append_dom
- \+ *lemma* part.right_dom_of_div_dom
- \+ *lemma* part.right_dom_of_inter_dom
- \+ *lemma* part.right_dom_of_mod_dom
- \+ *lemma* part.right_dom_of_mul_dom
- \+ *lemma* part.right_dom_of_sdiff_dom
- \+ *lemma* part.right_dom_of_union_dom
- \+ *lemma* part.sdiff_get_eq
- \+ *lemma* part.union_get_eq



## [2022-03-03 07:35:45](https://github.com/leanprover-community/mathlib/commit/9f721ba)
chore(logic/function/basic): add function.ne_iff ([#12288](https://github.com/leanprover-community/mathlib/pull/12288))
#### Estimated changes
Modified src/data/fun_like/basic.lean
- \+ *lemma* fun_like.ne_iff

Modified src/logic/function/basic.lean
- \+/\- *lemma* function.funext_iff
- \+ *lemma* function.ne_iff



## [2022-03-03 00:08:38](https://github.com/leanprover-community/mathlib/commit/9deeddb)
feat(algebra/algebra/operations): `submodule.map_pow` and opposite lemmas ([#12374](https://github.com/leanprover-community/mathlib/pull/12374))
To prove `map_pow`, we add `submodule.map_hom` to match the very-recently-added `ideal.map_hom`. 
The opposite lemmas can be used to extend these results for maps that reverse multiplication, by factoring them into an `alg_hom` into the opposite type composed with `mul_opposite.op`.
`(↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)` is really a mouthful, but the elaborator can't seem to work out the type any other way, and `.to_linear_map` appears not to be the preferred form for `simp` lemmas.
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+ *lemma* submodule.comap_op_one
- \+ *lemma* submodule.comap_unop_mul
- \+ *lemma* submodule.comap_unop_one
- \+ *lemma* submodule.comap_unop_pow
- \+ *def* submodule.equiv_opposite
- \- *lemma* submodule.map_div
- \+ *def* submodule.map_hom
- \- *lemma* submodule.map_mul
- \+ *lemma* submodule.map_op_mul
- \+ *lemma* submodule.map_op_one
- \+ *lemma* submodule.map_op_pow
- \+ *lemma* submodule.map_unop_one



## [2022-03-02 22:17:15](https://github.com/leanprover-community/mathlib/commit/6f74d3c)
chore(algebra/ring/basic): generalize lemmas to non-associative rings ([#12411](https://github.com/leanprover-community/mathlib/pull/12411))
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *theorem* ring_hom.injective_iff'
- \+/\- *theorem* ring_hom.injective_iff
- \+/\- *def* ring_hom.mk'



## [2022-03-02 21:08:47](https://github.com/leanprover-community/mathlib/commit/ce26d75)
refactor(analysis/normed_space/basic): split into normed_space and ../normed/normed_field ([#12410](https://github.com/leanprover-community/mathlib/pull/12410))
Splits off the sections about normed rings and fields of the file `analysis/normed_space/basic` into a new file `analysis/normed/normed_field`.
#### Estimated changes
Added src/analysis/normed/normed_field.lean
- \+ *lemma* eventually_norm_pow_le
- \+ *lemma* finset.norm_prod_le'
- \+ *lemma* finset.norm_prod_le
- \+ *lemma* int.norm_cast_rat
- \+ *lemma* int.norm_cast_real
- \+ *lemma* int.norm_eq_abs
- \+ *lemma* list.norm_prod_le'
- \+ *lemma* list.norm_prod_le
- \+ *def* matrix.normed_group
- \+ *def* matrix.semi_normed_group
- \+ *lemma* mul_left_bound
- \+ *lemma* mul_right_bound
- \+ *lemma* nnnorm_div
- \+ *def* nnnorm_hom
- \+ *lemma* nnnorm_inv
- \+ *lemma* nnnorm_mul
- \+ *lemma* nnnorm_mul_le
- \+ *lemma* nnnorm_norm
- \+ *lemma* nnnorm_nsmul_le
- \+ *lemma* nnnorm_one
- \+ *lemma* nnnorm_pow
- \+ *lemma* nnnorm_pow_le'
- \+ *lemma* nnnorm_pow_le
- \+ *lemma* nnnorm_prod
- \+ *lemma* nnnorm_zpow
- \+ *lemma* nnnorm_zsmul_le
- \+ *lemma* nnreal.coe_nat_abs
- \+ *lemma* nnreal.nnnorm_eq
- \+ *lemma* nnreal.norm_eq
- \+ *lemma* norm_div
- \+ *def* norm_hom
- \+ *lemma* norm_inv
- \+ *lemma* norm_matrix_le_iff
- \+ *lemma* norm_matrix_lt_iff
- \+ *lemma* norm_mul
- \+ *lemma* norm_mul_le
- \+ *lemma* norm_norm
- \+ *lemma* norm_nsmul_le
- \+ *lemma* norm_pow
- \+ *lemma* norm_pow_le'
- \+ *lemma* norm_pow_le
- \+ *lemma* norm_prod
- \+ *lemma* norm_zpow
- \+ *lemma* norm_zsmul_le
- \+ *lemma* normed_field.exists_lt_norm
- \+ *lemma* normed_field.exists_norm_lt
- \+ *lemma* normed_field.exists_norm_lt_one
- \+ *lemma* normed_field.exists_one_lt_norm
- \+ *lemma* normed_field.nhds_within_is_unit_ne_bot
- \+ *lemma* normed_field.punctured_nhds_ne_bot
- \+ *lemma* normed_group.tendsto_at_top'
- \+ *lemma* normed_group.tendsto_at_top
- \+ *lemma* rat.norm_cast_real
- \+ *lemma* real.ennnorm_eq_of_real
- \+ *lemma* real.nnnorm_coe_nat
- \+ *lemma* real.nnnorm_of_nonneg
- \+ *lemma* real.nnnorm_two
- \+ *lemma* real.norm_coe_nat
- \+ *lemma* real.norm_of_nonneg
- \+ *lemma* real.norm_of_nonpos
- \+ *lemma* real.norm_two
- \+ *lemma* real.of_real_le_ennnorm
- \+ *lemma* summable.mul_norm
- \+ *lemma* summable.mul_of_nonneg
- \+ *lemma* summable_mul_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_antidiagonal_of_summable_norm
- \+ *lemma* summable_norm_sum_mul_range_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
- \+ *lemma* tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
- \+ *lemma* tsum_mul_tsum_of_summable_norm
- \+ *lemma* units.norm_pos

Modified src/analysis/normed_space/basic.lean
- \- *lemma* eventually_norm_pow_le
- \- *lemma* finset.norm_prod_le'
- \- *lemma* finset.norm_prod_le
- \- *lemma* int.norm_cast_rat
- \- *lemma* int.norm_cast_real
- \- *lemma* int.norm_eq_abs
- \- *lemma* list.norm_prod_le'
- \- *lemma* list.norm_prod_le
- \- *def* matrix.normed_group
- \- *def* matrix.semi_normed_group
- \- *lemma* mul_left_bound
- \- *lemma* mul_right_bound
- \- *lemma* nnnorm_div
- \- *def* nnnorm_hom
- \- *lemma* nnnorm_inv
- \- *lemma* nnnorm_mul
- \- *lemma* nnnorm_mul_le
- \- *lemma* nnnorm_norm
- \- *lemma* nnnorm_nsmul_le
- \- *lemma* nnnorm_one
- \- *lemma* nnnorm_pow
- \- *lemma* nnnorm_pow_le'
- \- *lemma* nnnorm_pow_le
- \- *lemma* nnnorm_prod
- \- *lemma* nnnorm_zpow
- \- *lemma* nnnorm_zsmul_le
- \- *lemma* nnreal.coe_nat_abs
- \- *lemma* nnreal.nnnorm_eq
- \- *lemma* nnreal.norm_eq
- \- *lemma* norm_div
- \- *def* norm_hom
- \- *lemma* norm_inv
- \- *lemma* norm_matrix_le_iff
- \- *lemma* norm_matrix_lt_iff
- \- *lemma* norm_mul
- \- *lemma* norm_mul_le
- \- *lemma* norm_norm
- \- *lemma* norm_nsmul_le
- \- *lemma* norm_pow
- \- *lemma* norm_pow_le'
- \- *lemma* norm_pow_le
- \- *lemma* norm_prod
- \- *lemma* norm_zpow
- \- *lemma* norm_zsmul_le
- \- *lemma* normed_field.exists_lt_norm
- \- *lemma* normed_field.exists_norm_lt
- \- *lemma* normed_field.exists_norm_lt_one
- \- *lemma* normed_field.exists_one_lt_norm
- \- *lemma* normed_field.nhds_within_is_unit_ne_bot
- \- *lemma* normed_field.punctured_nhds_ne_bot
- \- *lemma* normed_group.tendsto_at_top'
- \- *lemma* normed_group.tendsto_at_top
- \- *lemma* rat.norm_cast_real
- \- *lemma* real.ennnorm_eq_of_real
- \- *lemma* real.nnnorm_coe_nat
- \- *lemma* real.nnnorm_of_nonneg
- \- *lemma* real.nnnorm_two
- \- *lemma* real.norm_coe_nat
- \- *lemma* real.norm_of_nonneg
- \- *lemma* real.norm_of_nonpos
- \- *lemma* real.norm_two
- \- *lemma* real.of_real_le_ennnorm
- \- *lemma* summable.mul_norm
- \- *lemma* summable.mul_of_nonneg
- \- *lemma* summable_mul_of_summable_norm
- \- *lemma* summable_norm_sum_mul_antidiagonal_of_summable_norm
- \- *lemma* summable_norm_sum_mul_range_of_summable_norm
- \- *lemma* tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
- \- *lemma* tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
- \- *lemma* tsum_mul_tsum_of_summable_norm
- \- *lemma* units.norm_pos



## [2022-03-02 20:03:20](https://github.com/leanprover-community/mathlib/commit/423328e)
chore(probability/independence): change to set notation and `measurable_set` ([#12400](https://github.com/leanprover-community/mathlib/pull/12400))
#### Estimated changes
Modified src/measure_theory/measurable_space_def.lean


Modified src/probability/independence.lean




## [2022-03-02 18:33:51](https://github.com/leanprover-community/mathlib/commit/a283e17)
feat(algebra/module/submodule_pointwise): pointwise negation ([#12405](https://github.com/leanprover-community/mathlib/pull/12405))
We already have pointwise negation on `add_submonoid`s (from [#10451](https://github.com/leanprover-community/mathlib/pull/10451)), this extends it to `submodules`.
The lemmas are all copies of the add_submonoid lemmas, except for two new lemmas:
* `submodule.neg_to_add_submonoid`
* `submodule.neg_eq_self`, which isn't true for `add_submonoid`s
Finally, we provide a `has_distrib_neg` instance; even though the negation is not cancellative, it does distribute over multiplication as expected.
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/module/submodule_pointwise.lean
- \+ *lemma* submodule.closure_neg
- \+ *lemma* submodule.coe_set_neg
- \+ *lemma* submodule.mem_neg
- \+ *lemma* submodule.neg_bot
- \+ *lemma* submodule.neg_eq_self
- \+ *lemma* submodule.neg_inf
- \+ *lemma* submodule.neg_infi
- \+ *lemma* submodule.neg_le
- \+ *lemma* submodule.neg_le_neg
- \+ *def* submodule.neg_order_iso
- \+ *lemma* submodule.neg_sup
- \+ *lemma* submodule.neg_supr
- \+ *lemma* submodule.neg_to_add_submonoid
- \+ *lemma* submodule.neg_top



## [2022-03-02 17:49:08](https://github.com/leanprover-community/mathlib/commit/90e2957)
chore(measure_theory/function/egorov): rename `uniform_integrability` file to `egorov` ([#12402](https://github.com/leanprover-community/mathlib/pull/12402))
#### Estimated changes
Modified src/measure_theory/function/convergence_in_measure.lean


Renamed src/measure_theory/function/uniform_integrable.lean to src/measure_theory/function/egorov.lean




## [2022-03-02 14:31:45](https://github.com/leanprover-community/mathlib/commit/7959d98)
feat(linear_algebra/matrix.determinant): add `matrix.det_neg` ([#12396](https://github.com/leanprover-community/mathlib/pull/12396))
#### Estimated changes
Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/matrix/determinant.lean
- \+ *lemma* matrix.det_neg
- \+ *lemma* matrix.det_neg_eq_smul
- \+/\- *lemma* matrix.det_smul
- \+ *lemma* matrix.det_smul_of_tower



## [2022-03-02 14:31:43](https://github.com/leanprover-community/mathlib/commit/c96fb62)
refactor(group_theory/*): Rename `general_commutator.lean` to `commutator.lean` ([#12388](https://github.com/leanprover-community/mathlib/pull/12388))
Followup to [#12308](https://github.com/leanprover-community/mathlib/pull/12308).
#### Estimated changes
Modified src/group_theory/abelianization.lean


Renamed src/group_theory/general_commutator.lean to src/group_theory/commutator.lean


Modified src/group_theory/nilpotent.lean


Modified src/group_theory/solvable.lean




## [2022-03-02 14:31:41](https://github.com/leanprover-community/mathlib/commit/d00cbee)
feat(algebra/big_operators/basic): prod_dvd_prod_of_subset ([#12383](https://github.com/leanprover-community/mathlib/pull/12383))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_dvd_prod_of_subset



## [2022-03-02 14:31:40](https://github.com/leanprover-community/mathlib/commit/22ddf9a)
feat(ring_theory/ideal): `map f (I^n) = (map f I)^n` ([#12370](https://github.com/leanprover-community/mathlib/pull/12370))
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *def* ideal.map_hom



## [2022-03-02 12:52:29](https://github.com/leanprover-community/mathlib/commit/4e8d8f2)
feat(ring_theory/unique_factorization_domain): factors of `p^k` ([#12369](https://github.com/leanprover-community/mathlib/pull/12369))
This is a relatively trivial application of existing lemmas, but the result is a particularly nice shape that I felt worth to add to the library.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* irreducible.normalized_factors_pow



## [2022-03-02 12:52:28](https://github.com/leanprover-community/mathlib/commit/f191f52)
chore(algebra/big_operators): generalize `map_prod` to `monoid_hom_class` ([#12354](https://github.com/leanprover-community/mathlib/pull/12354))
This PR generalizes the following lemmas to `(add_)monoid_hom_class`:
 * `map_prod`, `map_sum`
 * `map_multiset_prod`, `map_multiset_sum`
 * `map_list_prod`, `map_list_sum`
 * `map_finsupp_prod`, `map_finsupp_sum`
I haven't removed any of the existing specialized, namespaced versions of these lemmas yet, but I have marked them as `protected` and added a docstring saying to use the generic version instead.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* map_prod
- \- *lemma* monoid_hom.map_prod
- \- *lemma* mul_equiv.map_prod
- \- *lemma* ring_hom.map_list_prod
- \- *lemma* ring_hom.map_list_sum
- \- *lemma* ring_hom.map_multiset_prod
- \- *lemma* ring_hom.map_multiset_sum
- \- *lemma* ring_hom.map_prod
- \- *lemma* ring_hom.map_sum
- \- *lemma* ring_hom.unop_map_list_prod

Modified src/algebra/big_operators/multiset.lean
- \+ *lemma* map_multiset_prod
- \- *lemma* monoid_hom.map_multiset_prod
- \+/\- *lemma* multiset.prod_hom'
- \+/\- *lemma* multiset.prod_hom

Modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* polynomial.multiset_prod_X_sub_C_next_coeff
- \+/\- *lemma* polynomial.prod_X_sub_C_next_coeff

Modified src/data/finsupp/basic.lean
- \+ *lemma* map_finsupp_prod
- \- *lemma* monoid_hom.map_finsupp_prod
- \- *lemma* mul_equiv.map_finsupp_prod
- \- *lemma* ring_hom.map_finsupp_prod
- \- *lemma* ring_hom.map_finsupp_sum

Modified src/data/list/big_operators.lean
- \+/\- *lemma* list.prod_hom
- \+/\- *lemma* list.prod_map_hom
- \+ *lemma* map_list_prod
- \- *lemma* monoid_hom.map_list_prod
- \- *lemma* monoid_hom.unop_map_list_prod
- \+ *lemma* unop_map_list_prod

Modified src/data/polynomial/eval.lean
- \- *lemma* polynomial.map_multiset_prod
- \- *lemma* polynomial.map_prod
- \- *lemma* polynomial.map_sum

Modified src/field_theory/splitting_field.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.map_prod

Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/topology/list.lean




## [2022-03-02 10:22:02](https://github.com/leanprover-community/mathlib/commit/20d9541)
chore(ring_theory/localization): `localization_map_bijective` rename & `field` instance version ([#12375](https://github.com/leanprover-community/mathlib/pull/12375))
#### Estimated changes
Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/localization/basic.lean
- \+ *lemma* field.localization_map_bijective
- \+ *lemma* is_field.localization_map_bijective
- \- *lemma* localization_map_bijective_of_field



## [2022-03-02 09:30:27](https://github.com/leanprover-community/mathlib/commit/35086a1)
feat(probability): define conditional probability and add basic related theorems ([#12344](https://github.com/leanprover-community/mathlib/pull/12344))
Add the definition of conditional probability as a scaled restricted measure and prove Bayes' Theorem and other basic theorems.
#### Estimated changes
Modified src/measure_theory/measure/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.pos_of_subset_ne_zero

Added src/probability/conditional.lean
- \+ *def* probability_theory.cond
- \+ *lemma* probability_theory.cond_apply
- \+ *lemma* probability_theory.cond_cond_eq_cond_inter
- \+ *theorem* probability_theory.cond_eq_inv_mul_cond_mul
- \+ *lemma* probability_theory.cond_is_probability_measure
- \+ *lemma* probability_theory.cond_mul_eq_inter
- \+ *lemma* probability_theory.cond_pos_of_inter_ne_zero
- \+ *lemma* probability_theory.cond_univ
- \+ *lemma* probability_theory.inter_pos_of_cond_ne_zero



## [2022-03-02 07:46:20](https://github.com/leanprover-community/mathlib/commit/1eebec5)
perf(data/fintype/basic): speed up mem_of_mem_perms_of_list ([#12389](https://github.com/leanprover-community/mathlib/pull/12389))
This single theorem was taking twice as long as everything else in the file put together, and it was easy to fix.
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2022-03-02 07:46:19](https://github.com/leanprover-community/mathlib/commit/9daa233)
doc(*): fix broken markdown links ([#12385](https://github.com/leanprover-community/mathlib/pull/12385))
Some urls to nLab were also weird, so I replaced it with less weird ones.
The `MM91` reference was presumably intended to reference `MM92`.
#### Estimated changes
Modified src/algebra/group/freiman.lean


Modified src/category_theory/category/PartialFun.lean


Modified src/category_theory/category/Twop.lean


Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/spaces.lean


Modified src/data/nat/sqrt.lean


Modified src/data/two_pointing.lean


Modified src/order/category/DistribLattice.lean


Modified src/order/category/Lattice.lean


Modified src/order/complete_boolean_algebra.lean




## [2022-03-02 07:46:18](https://github.com/leanprover-community/mathlib/commit/b77ff23)
feat(algebra/ring): add non-unital and non-associative rings ([#12300](https://github.com/leanprover-community/mathlib/pull/12300))
Following up on [#11124](https://github.com/leanprover-community/mathlib/pull/11124).
The longer term goal is to develop C^* algebras, where non-unital algebras are an essential part of the theory.
#### Estimated changes
Modified src/algebra/ring/basic.lean


Modified src/algebra/ring/opposite.lean


Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean


Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/splitting_field.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/witt_vector/discrete_valuation_ring.lean




## [2022-03-02 06:23:49](https://github.com/leanprover-community/mathlib/commit/fefe359)
feat(set_theory/principal): prove theorems about additive principal ordinals ([#11704](https://github.com/leanprover-community/mathlib/pull/11704))
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \+ *theorem* cardinal.aleph_is_principal_add
- \+ *theorem* cardinal.ord_is_principal_add

Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.add_absorp
- \- *theorem* ordinal.add_absorp_iff
- \- *theorem* ordinal.add_lt_omega
- \- *theorem* ordinal.add_lt_omega_opow
- \- *theorem* ordinal.add_omega
- \- *theorem* ordinal.add_omega_opow
- \- *theorem* ordinal.mul_omega_opow_opow

Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/principal.lean
- \+ *theorem* ordinal.add_absorp
- \+ *theorem* ordinal.add_omega
- \+ *theorem* ordinal.add_omega_opow
- \+ *theorem* ordinal.mul_principal_add_is_principal_add
- \+ *theorem* ordinal.opow_principal_add_is_principal_add
- \+ *theorem* ordinal.principal_add_iff_add_left_eq_self
- \+ *theorem* ordinal.principal_add_iff_zero_or_omega_power
- \+ *theorem* ordinal.principal_add_is_limit
- \+ *theorem* ordinal.principal_add_of_le_one
- \+ *theorem* ordinal.principal_add_omega
- \+ *theorem* ordinal.principal_add_omega_opow
- \+ *theorem* ordinal.principal_add_one



## [2022-03-02 04:09:19](https://github.com/leanprover-community/mathlib/commit/a9902d5)
feat(algebra/divisibility): generalise basic facts to semigroups ([#12325](https://github.com/leanprover-community/mathlib/pull/12325))
#### Estimated changes
Modified src/algebra/divisibility.lean


Modified src/algebra/gcd_monoid/basic.lean
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right

Modified src/number_theory/padics/ring_homs.lean




## [2022-03-02 02:44:42](https://github.com/leanprover-community/mathlib/commit/cc9de07)
feat(algebra/star): replace star_monoid with star_semigroup ([#12299](https://github.com/leanprover-community/mathlib/pull/12299))
In preparation for allowing non-unital C^* algebras, replace star_monoid with star_semigroup.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+/\- *lemma* is_unit.star
- \+/\- *lemma* is_unit_star
- \+/\- *lemma* star_div
- \+/\- *lemma* star_inv
- \+/\- *lemma* star_inv_of
- \- *def* star_monoid_of_comm
- \+/\- *lemma* star_mul'
- \+/\- *def* star_mul_aut
- \+/\- *def* star_mul_equiv
- \+/\- *lemma* star_mul_self_nonneg'
- \+/\- *lemma* star_mul_self_nonneg
- \+/\- *lemma* star_one
- \+/\- *lemma* star_pow
- \+/\- *lemma* star_prod
- \+/\- *def* star_ring_equiv
- \+ *def* star_semigroup_of_comm
- \+/\- *lemma* star_zpow

Modified src/algebra/star/chsh.lean
- \+/\- *structure* is_CHSH_tuple

Modified src/algebra/star/free.lean


Modified src/algebra/star/module.lean


Modified src/algebra/star/pi.lean


Modified src/algebra/star/pointwise.lean


Modified src/algebra/star/unitary.lean
- \+/\- *def* unitary

Modified src/analysis/inner_product_space/adjoint.lean


Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.conj_transpose_smul



## [2022-03-01 23:58:42](https://github.com/leanprover-community/mathlib/commit/4ba9098)
feat(algebra/euclidean_domain,data/int/basic): dvd_div_of_mul_dvd ([#12382](https://github.com/leanprover-community/mathlib/pull/12382))
We have a separate `int` and `euclidean_domain` version as `euclidean_domain` isn't pulled in by `int.basic`.
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.dvd_div_of_mul_dvd

Modified src/data/int/basic.lean
- \+ *lemma* int.div_dvd_of_dvd
- \- *lemma* int.div_dvd_of_ne_zero_dvd
- \+ *lemma* int.dvd_div_of_mul_dvd



## [2022-03-01 22:20:43](https://github.com/leanprover-community/mathlib/commit/269280a)
feat(topology/bornology/basic): Define bornology ([#12036](https://github.com/leanprover-community/mathlib/pull/12036))
This defines bornologies and provides the basic API. A bornology on a type is a filter consisting of cobounded sets which contains the cofinite sets; bounded sets are then complements of cobounded sets. This is equivalent to the usual formulation in terms of bounded sets, but provides access to mathlib's large filter library. We provide the relevant API for bounded sets.
#### Estimated changes
Modified docs/references.bib


Added src/topology/bornology/basic.lean
- \+ *def* bornology.cofinite
- \+ *lemma* bornology.ext_iff'
- \+ *lemma* bornology.ext_iff_is_bounded
- \+ *lemma* bornology.is_bounded.subset
- \+ *lemma* bornology.is_bounded.union
- \+ *def* bornology.is_bounded
- \+ *lemma* bornology.is_bounded_Union
- \+ *lemma* bornology.is_bounded_bUnion
- \+ *lemma* bornology.is_bounded_compl_iff
- \+ *lemma* bornology.is_bounded_def
- \+ *lemma* bornology.is_bounded_empty
- \+ *lemma* bornology.is_bounded_sUnion
- \+ *def* bornology.is_cobounded
- \+ *lemma* bornology.is_cobounded_def
- \+ *def* bornology.of_bounded
- \+ *lemma* bornology.sUnion_bounded_univ



## [2022-03-01 20:54:12](https://github.com/leanprover-community/mathlib/commit/5c2fa35)
chore(topology/algebra/valuation): add universe ([#11962](https://github.com/leanprover-community/mathlib/pull/11962))
#### Estimated changes
Modified src/topology/algebra/valuation.lean
- \+/\- *lemma* valued.loc_const
- \+/\- *lemma* valued.subgroups_basis

Modified src/topology/algebra/valued_field.lean
- \+/\- *lemma* valued.continuous_extension
- \+/\- *lemma* valued.continuous_valuation
- \+/\- *lemma* valued.extension_extends



## [2022-03-01 19:12:01](https://github.com/leanprover-community/mathlib/commit/818c81f)
feat(ring_theory/integral_domain): finite integral domain is a field ([#12376](https://github.com/leanprover-community/mathlib/pull/12376))
We don't yet have Wedderburn's little theorem (on my todo list), so adding some weaker versions to tide us over.
#### Estimated changes
Modified src/ring_theory/integral_domain.lean
- \- *def* division_ring_of_is_domain
- \+ *def* fintype.division_ring_of_is_domain
- \+ *def* fintype.field_of_domain
- \+ *def* fintype.group_with_zero_of_cancel
- \+ *lemma* fintype.is_field_of_domain
- \- *def* group_with_zero_of_fintype



## [2022-03-01 19:11:59](https://github.com/leanprover-community/mathlib/commit/130e07d)
chore(algebra/group/prod): `prod.swap` commutes with arithmetic ([#12367](https://github.com/leanprover-community/mathlib/pull/12367))
This also adds some missing `div` lemmas using `to_additive`.
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *lemma* prod.fst_div
- \- *lemma* prod.fst_sub
- \+ *lemma* prod.mk_div_mk
- \- *lemma* prod.mk_sub_mk
- \+ *lemma* prod.snd_div
- \- *lemma* prod.snd_sub
- \+ *lemma* prod.swap_div
- \+ *lemma* prod.swap_inv
- \+ *lemma* prod.swap_mul
- \+ *lemma* prod.swap_one

Modified src/group_theory/group_action/prod.lean
- \+ *theorem* prod.smul_swap



## [2022-03-01 17:25:51](https://github.com/leanprover-community/mathlib/commit/5e36e12)
feat(category_theory/abelian/homology): Adds API for homology mimicking that of (co)kernels. ([#12171](https://github.com/leanprover-community/mathlib/pull/12171))
#### Estimated changes
Added src/category_theory/abelian/homology.lean
- \+ *abbreviation* category_theory.abelian.homology_c
- \+ *abbreviation* category_theory.abelian.homology_c_to_k
- \+ *abbreviation* category_theory.abelian.homology_k
- \+ *lemma* homology.condition_ι
- \+ *lemma* homology.condition_π'
- \+ *def* homology.desc'
- \+ *lemma* homology.hom_from_ext
- \+ *lemma* homology.hom_to_ext
- \+ *def* homology.lift
- \+ *lemma* homology.lift_ι
- \+ *lemma* homology.map_eq_desc'_lift_left
- \+ *lemma* homology.map_eq_desc'_lift_right
- \+ *lemma* homology.map_eq_lift_desc'_left
- \+ *lemma* homology.map_eq_lift_desc'_right
- \+ *def* homology.ι
- \+ *def* homology.π'
- \+ *lemma* homology.π'_desc'
- \+ *lemma* homology.π'_eq_π
- \+ *lemma* homology.π'_map
- \+ *lemma* homology.π'_ι
- \+ *def* homology_iso_kernel_desc

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.cokernel_iso_of_eq_hom_comp_desc
- \+ *lemma* category_theory.limits.cokernel_iso_of_eq_inv_comp_desc
- \+ *lemma* category_theory.limits.kernel_iso_of_eq_hom_comp_ι
- \+ *lemma* category_theory.limits.kernel_iso_of_eq_inv_comp_ι
- \+ *lemma* category_theory.limits.lift_comp_kernel_iso_of_eq_hom
- \+ *lemma* category_theory.limits.lift_comp_kernel_iso_of_eq_inv
- \+ *lemma* category_theory.limits.π_comp_cokernel_iso_of_eq_hom
- \+ *lemma* category_theory.limits.π_comp_cokernel_iso_of_eq_inv



## [2022-03-01 17:25:49](https://github.com/leanprover-community/mathlib/commit/b45657f)
feat(algebra/algebra/spectrum, analysis/normed_space/spectrum): prove the spectrum of any element in a complex Banach algebra is nonempty ([#12115](https://github.com/leanprover-community/mathlib/pull/12115))
This establishes that the spectrum of any element in a (nontrivial) complex Banach algebra is nonempty. The nontrivial assumption is necessary, as otherwise the only element is invertible. In addition, we establish some properties of the resolvent function; in particular, it tends to zero at infinity.
- [x] depends on: [#12095](https://github.com/leanprover-community/mathlib/pull/12095)
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* is_unit.smul_sub_iff_sub_inv_smul
- \+ *lemma* spectrum.is_unit_resolvent
- \+ *lemma* spectrum.units_smul_resolvent
- \+ *lemma* spectrum.units_smul_resolvent_self

Modified src/analysis/normed_space/spectrum.lean
- \+ *theorem* spectrum.nonempty
- \+ *lemma* spectrum.norm_resolvent_le_forall



## [2022-03-01 17:25:48](https://github.com/leanprover-community/mathlib/commit/29c84f7)
feat(combinatorics/set_family/lym): Lubell-Yamamoto-Meshalkin inequalities ([#11248](https://github.com/leanprover-community/mathlib/pull/11248))
This proves the two local LYM inequalities, the LYM inequality and Sperner's theorem.
#### Estimated changes
Added src/combinatorics/set_family/lym.lean
- \+ *lemma* finset.card_div_choose_le_card_shadow_div_choose
- \+ *lemma* finset.card_mul_le_card_shadow_mul
- \+ *def* finset.falling
- \+ *lemma* finset.falling_zero_subset
- \+ *lemma* finset.le_card_falling_div_choose
- \+ *lemma* finset.mem_falling
- \+ *lemma* finset.sized_falling
- \+ *lemma* finset.slice_subset_falling
- \+ *lemma* finset.slice_union_shadow_falling_succ
- \+ *lemma* finset.sum_card_slice_div_choose_le_one
- \+ *lemma* is_antichain.disjoint_slice_shadow_falling
- \+ *lemma* is_antichain.sperner

Modified src/combinatorics/set_family/shadow.lean
- \+ *lemma* finset.shadow_singleton_empty
- \+ *lemma* finset.sized_shadow_iff

Modified src/data/finset/basic.lean
- \+ *lemma* finset.ssubset_iff_exists_insert_subset
- \+ *lemma* finset.ssubset_iff_exists_subset_erase

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.insert_inj_on'



## [2022-03-01 15:29:36](https://github.com/leanprover-community/mathlib/commit/3007f24)
chore(*): use `*_*_*_comm` where possible ([#12372](https://github.com/leanprover-community/mathlib/pull/12372))
These lemmas are quite helpful when proving `map_add` type statements; hopefully people will remember them more if they see them used in a few more places.
#### Estimated changes
Modified src/data/num/lemmas.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/prod.lean


Modified src/tactic/omega/eq_elim.lean




## [2022-03-01 15:29:35](https://github.com/leanprover-community/mathlib/commit/3fb051d)
feat(field_theory/krull_topology): added krull_topology_t2 ([#11973](https://github.com/leanprover-community/mathlib/pull/11973))
#### Estimated changes
Modified src/data/fun_like/basic.lean
- \+ *lemma* fun_like.exists_ne

Modified src/field_theory/krull_topology.lean
- \+ *lemma* intermediate_field.fixing_subgroup_is_open
- \+ *lemma* krull_topology_t2
- \+ *lemma* subgroup.is_open_of_one_mem_interior



## [2022-03-01 14:22:58](https://github.com/leanprover-community/mathlib/commit/5a56e46)
chore(data/polynomial/monic): remove useless lemma ([#12364](https://github.com/leanprover-community/mathlib/pull/12364))
There is a `nontrivial` version of this lemma (`ne_zero_of_monic`) which actually has uses in the library, unlike this deleted lemma. We also tidy the proof of the lemma below.
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.ne_zero_of_monic_of_zero_ne_one



## [2022-03-01 14:22:57](https://github.com/leanprover-community/mathlib/commit/a4e936c)
chore(category_theory/idempotents) replaced "idempotence" by "idem" ([#12362](https://github.com/leanprover-community/mathlib/pull/12362))
#### Estimated changes
Modified src/category_theory/idempotents/basic.lean
- \+ *lemma* category_theory.idempotents.idem_of_id_sub_idem
- \- *lemma* category_theory.idempotents.idempotence_of_id_sub_idempotent

Modified src/category_theory/idempotents/biproducts.lean


Modified src/category_theory/idempotents/functor_categories.lean


Modified src/category_theory/idempotents/karoubi.lean
- \+/\- *def* category_theory.idempotents.karoubi.decomp_id_i
- \+/\- *lemma* category_theory.idempotents.karoubi.id_eq
- \+/\- *structure* category_theory.idempotents.karoubi

Modified src/category_theory/idempotents/karoubi_karoubi.lean




## [2022-03-01 10:36:01](https://github.com/leanprover-community/mathlib/commit/1f39ada)
feat(linear_algebra): generalize `linear_equiv.finrank_eq` to rings ([#12358](https://github.com/leanprover-community/mathlib/pull/12358))
Since `finrank` doesn't assume the module is actually a vector space, neither should the statement that linear equivalences preserve it.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *theorem* linear_equiv.finrank_eq
- \+/\- *lemma* linear_equiv.finrank_map_eq



## [2022-03-01 07:35:56](https://github.com/leanprover-community/mathlib/commit/c223a81)
feat(measure_theory/function/locally_integrable): define locally integrable ([#12216](https://github.com/leanprover-community/mathlib/pull/12216))
* Define the locally integrable predicate
* Move all results about integrability on compact sets to a new file
* Rename some lemmas from `integrable_on_compact` -> `locally_integrable`, if appropriate.
* Weaken some type-class assumptions (also on `is_compact_interval`)
* Simplify proof of `continuous.integrable_of_has_compact_support`
* Rename variables in moved lemmas to sensible names
#### Estimated changes
Added src/measure_theory/function/locally_integrable.lean
- \+ *lemma* antitone.locally_integrable
- \+ *lemma* antitone_on.integrable_on_compact
- \+ *lemma* continuous.integrable_of_has_compact_support
- \+ *lemma* continuous.integrable_on_Icc
- \+ *lemma* continuous.integrable_on_Ioc
- \+ *lemma* continuous.integrable_on_interval
- \+ *lemma* continuous.integrable_on_interval_oc
- \+ *lemma* continuous.locally_integrable
- \+ *lemma* continuous_on.integrable_on_Icc
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* continuous_on.integrable_on_interval
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* measure_theory.integrable.locally_integrable
- \+ *lemma* measure_theory.integrable_on.continuous_on_mul
- \+ *lemma* measure_theory.integrable_on.continuous_on_mul_of_subset
- \+ *lemma* measure_theory.integrable_on.mul_continuous_on
- \+ *lemma* measure_theory.integrable_on.mul_continuous_on_of_subset
- \+ *lemma* measure_theory.locally_integrable.ae_measurable
- \+ *def* measure_theory.locally_integrable
- \+ *lemma* measure_theory.locally_integrable_iff
- \+ *lemma* monotone.locally_integrable
- \+ *lemma* monotone_on.integrable_on_compact

Modified src/measure_theory/integral/integrable_on.lean
- \- *lemma* antitone.integrable_on_compact
- \- *lemma* antitone_on.integrable_on_compact
- \- *lemma* continuous.integrable_of_has_compact_support
- \- *lemma* continuous.integrable_on_Icc
- \- *lemma* continuous.integrable_on_Ioc
- \- *lemma* continuous.integrable_on_compact
- \- *lemma* continuous.integrable_on_interval
- \- *lemma* continuous.integrable_on_interval_oc
- \- *lemma* continuous_on.integrable_on_Icc
- \- *lemma* continuous_on.integrable_on_compact
- \- *lemma* continuous_on.integrable_on_interval
- \- *lemma* is_compact.integrable_on_of_nhds_within
- \- *lemma* measure_theory.integrable_on.continuous_on_mul
- \- *lemma* measure_theory.integrable_on.continuous_on_mul_of_subset
- \- *lemma* measure_theory.integrable_on.mul_continuous_on
- \- *lemma* measure_theory.integrable_on.mul_continuous_on_of_subset
- \+ *lemma* measure_theory.integrable_on_iff_integable_of_support_subset
- \- *lemma* monotone.integrable_on_compact
- \- *lemma* monotone_on.integrable_on_compact

Modified src/measure_theory/integral/interval_integral.lean


Modified src/topology/algebra/order/compact.lean
- \+/\- *lemma* is_compact_interval

Modified test/monotonicity.lean




## [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/cd98967)
feat(order/category/CompleteLattice): The category of complete lattices ([#12348](https://github.com/leanprover-community/mathlib/pull/12348))
Define `CompleteLattice`, the category of complete lattices with complete lattice homomorphisms.
#### Estimated changes
Added src/order/category/CompleteLattice.lean
- \+ *def* CompleteLattice.dual
- \+ *def* CompleteLattice.dual_equiv
- \+ *def* CompleteLattice.iso.mk
- \+ *def* CompleteLattice.of
- \+ *def* CompleteLattice
- \+ *lemma* CompleteLattice_dual_comp_forget_to_BoundedLattice

Modified src/order/hom/complete_lattice.lean
- \+ *def* complete_lattice_hom.to_bounded_lattice_hom



## [2022-03-01 02:55:33](https://github.com/leanprover-community/mathlib/commit/37885e8)
feat(category_theory/idempotents): biproducts in idempotent completions ([#12333](https://github.com/leanprover-community/mathlib/pull/12333))
#### Estimated changes
Added src/category_theory/idempotents/biproducts.lean
- \+ *def* category_theory.idempotents.karoubi.biproducts.bicone
- \+ *def* category_theory.idempotents.karoubi.complement
- \+ *def* category_theory.idempotents.karoubi.decomposition
- \+ *lemma* category_theory.idempotents.karoubi.karoubi_has_finite_biproducts



## [2022-03-01 01:31:29](https://github.com/leanprover-community/mathlib/commit/73dd4b5)
refactor(category_theory/functor): a folder for concepts directly related to functors ([#12346](https://github.com/leanprover-community/mathlib/pull/12346))
#### Estimated changes
Modified docs/tutorial/category_theory/intro.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/category_theory/abelian/ext.lean


Modified src/category_theory/adjunction/reflective.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/concrete_category/reflects_isomorphisms.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean


Renamed src/category_theory/functor.lean to src/category_theory/functor/basic.lean


Renamed src/category_theory/functor_category.lean to src/category_theory/functor/category.lean


Renamed src/category_theory/const.lean to src/category_theory/functor/const.lean


Renamed src/category_theory/currying.lean to src/category_theory/functor/currying.lean


Added src/category_theory/functor/default.lean


Renamed src/category_theory/derived.lean to src/category_theory/functor/derived.lean


Renamed src/category_theory/flat_functors.lean to src/category_theory/functor/flat.lean


Renamed src/category_theory/fully_faithful.lean to src/category_theory/functor/fully_faithful.lean


Renamed src/category_theory/functorial.lean to src/category_theory/functor/functorial.lean


Renamed src/category_theory/hom_functor.lean to src/category_theory/functor/hom.lean


Renamed src/category_theory/reflects_isomorphisms.lean to src/category_theory/functor/reflects_isomorphisms.lean


Modified src/category_theory/limits/colimit_limit.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/fubini.lean


Modified src/category_theory/limits/is_limit.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/basic.lean


Modified src/category_theory/monoidal/center.lean


Modified src/category_theory/monoidal/functor_category.lean


Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/tor.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/over.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/sigma/basic.lean


Modified src/category_theory/sites/cover_preserving.lean


Modified src/category_theory/subobject/mono_over.lean


Modified src/category_theory/thin.lean


Modified src/category_theory/types.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean


