## [2021-06-30 21:21:07](https://github.com/leanprover-community/mathlib/commit/0faf086)
feat(data/int/cast): cast_nat_abs ([#8120](https://github.com/leanprover-community/mathlib/pull/8120))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* int.cast_nat_abs



## [2021-06-30 21:21:06](https://github.com/leanprover-community/mathlib/commit/ad00a02)
feat(topology/vector_bundle): `topological_vector_bundle_core` ([#8089](https://github.com/leanprover-community/mathlib/pull/8089))
Analogous construction to `topological_fiber_bundle_core`. This construction gives a way to construct vector bundles from a structure registering how trivialization changes act on fibers.
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+ *def* topological_vector_bundle_core.base
- \+ *lemma* topological_vector_bundle_core.coe_cord_change
- \+ *lemma* topological_vector_bundle_core.continuous_proj
- \+ *lemma* topological_vector_bundle_core.coord_change_linear_comp
- \+ *def* topological_vector_bundle_core.fiber
- \+ *def* topological_vector_bundle_core.index
- \+ *lemma* topological_vector_bundle_core.is_open_map_proj
- \+ *def* topological_vector_bundle_core.local_triv
- \+ *def* topological_vector_bundle_core.local_triv_at
- \+ *lemma* topological_vector_bundle_core.local_triv_at_apply
- \+ *lemma* topological_vector_bundle_core.mem_local_triv_source
- \+ *lemma* topological_vector_bundle_core.mem_source_at
- \+ *lemma* topological_vector_bundle_core.mem_triv_change_source
- \+ *def* topological_vector_bundle_core.proj
- \+ *def* topological_vector_bundle_core.to_topological_vector_bundle_core
- \+ *def* topological_vector_bundle_core.triv_change
- \+ *structure* topological_vector_bundle_core



## [2021-06-30 20:39:41](https://github.com/leanprover-community/mathlib/commit/e70093f)
feat(algebra/free_non_unital_non_assoc_algebra): construction of the free non-unital, non-associative algebra on a type `X` with coefficients in a semiring `R` ([#8141](https://github.com/leanprover-community/mathlib/pull/8141))
#### Estimated changes
Modified src/algebra/free_algebra.lean


Added src/algebra/free_non_unital_non_assoc_algebra.lean
- \+ *lemma* free_non_unital_non_assoc_algebra.hom_ext
- \+ *def* free_non_unital_non_assoc_algebra.lift
- \+ *lemma* free_non_unital_non_assoc_algebra.lift_comp_of
- \+ *lemma* free_non_unital_non_assoc_algebra.lift_of_apply
- \+ *lemma* free_non_unital_non_assoc_algebra.lift_symm_apply
- \+ *lemma* free_non_unital_non_assoc_algebra.lift_unique
- \+ *def* free_non_unital_non_assoc_algebra.of
- \+ *lemma* free_non_unital_non_assoc_algebra.of_comp_lift
- \+ *def* free_non_unital_non_assoc_algebra



## [2021-06-30 18:53:30](https://github.com/leanprover-community/mathlib/commit/e713106)
docs(data/string/*): add module docstrings ([#8144](https://github.com/leanprover-community/mathlib/pull/8144))
#### Estimated changes
Modified src/data/string/basic.lean


Modified src/data/string/defs.lean




## [2021-06-30 18:53:29](https://github.com/leanprover-community/mathlib/commit/8ee2967)
feat(algebra/big_operators/basic): nat_abs_sum_le ([#8132](https://github.com/leanprover-community/mathlib/pull/8132))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* nat_abs_sum_le



## [2021-06-30 18:03:21](https://github.com/leanprover-community/mathlib/commit/3a5851f)
feat(data/complex/module): add complex.lift to match zsqrtd.lift ([#8107](https://github.com/leanprover-community/mathlib/pull/8107))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/The.20unique.20.60.E2.84.82.20.E2.86.92.E2.82.90.5B.E2.84.9D.5D.20A.60.20given.20a.20square.20root.20of.20-1/near/244135262)
#### Estimated changes
Modified src/data/complex/module.lean
- \+ *def* complex.lift_aux
- \+ *lemma* complex.lift_aux_I
- \+ *lemma* complex.lift_aux_apply
- \+ *lemma* complex.lift_aux_apply_I
- \+ *lemma* complex.lift_aux_neg_I



## [2021-06-30 16:49:13](https://github.com/leanprover-community/mathlib/commit/36c90d5)
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
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* alg_hom.subsingleton

Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* alg_equiv.subsingleton_left
- \+ *lemma* alg_equiv.subsingleton_right
- \+ *lemma* alg_hom.subsingleton
- \- *lemma* subalgebra.alg_equiv.subsingleton_left
- \- *lemma* subalgebra.alg_equiv.subsingleton_right
- \- *lemma* subalgebra.alg_hom.subsingleton



## [2021-06-30 16:49:12](https://github.com/leanprover-community/mathlib/commit/d420db5)
chore(algebra/algebra): trivial lemmas for alg_equiv ([#8139](https://github.com/leanprover-community/mathlib/pull/8139))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.coe_alg_hom_injective
- \+ *lemma* alg_equiv.coe_alg_hom_of_alg_hom
- \+/\- *lemma* alg_equiv.coe_ring_equiv_injective
- \+ *lemma* alg_equiv.of_alg_hom_coe_alg_hom
- \+ *lemma* alg_equiv.of_alg_hom_symm
- \- *lemma* alg_equiv.of_linear_equiv_apply
- \+ *lemma* alg_equiv.of_linear_equiv_symm
- \- *theorem* alg_equiv.to_linear_equiv_inj
- \+ *theorem* alg_equiv.to_linear_equiv_injective
- \- *theorem* alg_equiv.to_linear_map_inj
- \+ *theorem* alg_equiv.to_linear_map_injective
- \- *theorem* alg_hom.to_linear_map_inj
- \+ *theorem* alg_hom.to_linear_map_injective

Modified src/algebra/monoid_algebra.lean


Modified src/ring_theory/tensor_product.lean




## [2021-06-30 13:51:06](https://github.com/leanprover-community/mathlib/commit/9c03c03)
feat(data/set/basic): range_pair_subset ([#8133](https://github.com/leanprover-community/mathlib/pull/8133))
From LTE.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.range_pair_subset



## [2021-06-30 12:06:40](https://github.com/leanprover-community/mathlib/commit/1de192f)
feat(algebra/ordered_ring): abs_cases lemma ([#8124](https://github.com/leanprover-community/mathlib/pull/8124))
This lemma makes the following type of argument work seamlessly:
```lean
example (h : x<-1/2) : |x + 1| < |x| := by cases abs_cases (x + 1); cases abs_cases x; linarith
```
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_cases



## [2021-06-30 11:26:31](https://github.com/leanprover-community/mathlib/commit/db05900)
feat(linear_algebra/clifford_algebra): two algebras are isomorphic if their quadratic forms are equivalent ([#8128](https://github.com/leanprover-community/mathlib/pull/8128))
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/basic.lean
- \+ *def* clifford_algebra.equiv_of_isometry
- \+ *lemma* clifford_algebra.equiv_of_isometry_refl
- \+ *lemma* clifford_algebra.equiv_of_isometry_symm
- \+ *lemma* clifford_algebra.equiv_of_isometry_trans
- \+ *def* clifford_algebra.map
- \+ *lemma* clifford_algebra.map_apply_ι
- \+ *lemma* clifford_algebra.map_comp_map
- \+ *lemma* clifford_algebra.map_comp_ι
- \+ *lemma* clifford_algebra.map_id



## [2021-06-30 08:51:20](https://github.com/leanprover-community/mathlib/commit/9a8dcb9)
docs(data/dlist/basic): add module docstring ([#8079](https://github.com/leanprover-community/mathlib/pull/8079))
#### Estimated changes
Modified src/data/dlist/basic.lean




## [2021-06-30 04:28:24](https://github.com/leanprover-community/mathlib/commit/eeeb223)
feat(data/int/basic): int.nat_abs_sub_le ([#8118](https://github.com/leanprover-community/mathlib/pull/8118))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_sub_le



## [2021-06-30 04:28:23](https://github.com/leanprover-community/mathlib/commit/af8a38f)
feat(algebra/{covariant_and_contravariant + ordered_monoid): add instance, golf, docs ([#8067](https://github.com/leanprover-community/mathlib/pull/8067))
Introduce a missing instance for `comm_semigroup`s.
Also, golf a couple of proofs and add a relevant, explicit PR to a comment.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean


Modified src/algebra/ordered_monoid.lean




## [2021-06-30 03:13:34](https://github.com/leanprover-community/mathlib/commit/3ee436d)
docs(data/char): add module docstring ([#8043](https://github.com/leanprover-community/mathlib/pull/8043))
#### Estimated changes
Modified src/data/char.lean




## [2021-06-30 02:07:35](https://github.com/leanprover-community/mathlib/commit/8cacd99)
chore(scripts): update nolints.txt ([#8131](https://github.com/leanprover-community/mathlib/pull/8131))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-29 23:21:40](https://github.com/leanprover-community/mathlib/commit/917bcd4)
doc(topology/separation): module + lemma docs ([#8091](https://github.com/leanprover-community/mathlib/pull/8091))
#### Estimated changes
Modified src/topology/separation.lean
- \+/\- *theorem* compact_t2_tot_disc_iff_tot_sep



## [2021-06-29 23:21:39](https://github.com/leanprover-community/mathlib/commit/2600baf)
docs(data/list/sections): add module docstring ([#8033](https://github.com/leanprover-community/mathlib/pull/8033))
#### Estimated changes
Modified src/data/list/sections.lean




## [2021-06-29 21:36:27](https://github.com/leanprover-community/mathlib/commit/2c749b1)
feat(algebra/to_additive): do not additivize operations on constant types ([#7792](https://github.com/leanprover-community/mathlib/pull/7792))
* Fixes [#4210](https://github.com/leanprover-community/mathlib/pull/4210)
* Adds a heuristic to `@[to_additive]` that decides which multiplicative identifiers to replace with their additive counterparts. 
* See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/to_additive.20and.20fixed.20types) thread or documentation for the precise heuristic.
* We tag some types with `@[to_additive]`, so that they are handled correctly by the heurstic. These types `pempty`, `empty`, `unit` and `punit`.
* We make the following change to enable to above bullet point: you are allowed to translate a declaration to itself, only if you write its name again as argument of the attribute (if you don't specify an argument we want to raise an error, since that likely is a mistake).
* Because of this heuristic, all declarations with the `@[to_additive]` attribute should have a type with a multiplicative structure on it as its first argument. The first argument should not be an arbitrary indexing type. This means that in `finset.prod` and `finprod` we reorder the first two (implicit) arguments, so that the first argument is the codomain of the function.
* This will eliminate many (but not all) type mismatches generated by `@[to_additive]`.
* This heuristic doesn't catch all cases: for example, the declaration could have two type arguments with multiplicative structure, and the second one is `ℕ`, but the first one is a variable.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \- *lemma* finset.eq_of_card_le_one_of_sum_eq
- \- *lemma* finset.eventually_constant_sum
- \+/\- *lemma* finset.prod_empty
- \+/\- *lemma* finset.prod_mk
- \+/\- *lemma* finset.sum_const_zero
- \- *lemma* finset.sum_flip
- \- *lemma* finset.sum_range_add
- \- *lemma* finset.sum_range_one
- \- *lemma* finset.sum_range_succ'
- \- *lemma* finset.sum_range_succ
- \- *lemma* finset.sum_range_succ_comm

Modified src/algebra/big_operators/finprod.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/group/to_additive.lean
- \+/\- *structure* to_additive.value_type

Modified src/category_theory/types.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/data/complex/exponential.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/geometry/manifold/times_cont_mdiff_map.lean


Modified src/group_theory/perm/sign.lean


Modified src/meta/expr.lean


Modified src/tactic/transform_decl.lean




## [2021-06-29 20:21:49](https://github.com/leanprover-community/mathlib/commit/e6ec901)
feat(ring_theory/power_basis): extensionality for algebra homs ([#8110](https://github.com/leanprover-community/mathlib/pull/8110))
This PR shows two `alg_hom`s out of an algebra with a power basis are equal if the generator has the same image for both maps. It uses this result to bundle `power_basis.lift` into an equiv.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom.subsingleton

Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.alg_hom_ext
- \+/\- *lemma* power_basis.constr_pow_mul
- \+/\- *lemma* power_basis.equiv_aeval
- \+/\- *lemma* power_basis.equiv_gen
- \+/\- *lemma* power_basis.equiv_map
- \+/\- *lemma* power_basis.equiv_symm
- \+ *lemma* power_basis.exists_eq_aeval'
- \+/\- *lemma* power_basis.lift_aeval
- \+/\- *lemma* power_basis.lift_gen



## [2021-06-29 19:37:54](https://github.com/leanprover-community/mathlib/commit/505c32f)
feat(analysis/normed_space/inner_product): the orthogonal projection is self adjoint ([#8116](https://github.com/leanprover-community/mathlib/pull/8116))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* inner_orthogonal_projection_left_eq_right



## [2021-06-29 17:54:59](https://github.com/leanprover-community/mathlib/commit/5ecd078)
feat(data/ordmap/ordset): Implement some more `ordset` functions ([#8127](https://github.com/leanprover-community/mathlib/pull/8127))
Implement (with proofs) `erase`, `map`, and `mem` for `ordset` in `src/data/ordmap` along with a few useful related proofs.
#### Estimated changes
Modified src/data/ordmap/ordset.lean
- \+ *theorem* ordnode.erase.valid
- \+ *theorem* ordnode.map.valid
- \+ *theorem* ordnode.pos_size_of_mem
- \+ *theorem* ordnode.size_erase_of_mem
- \+ *theorem* ordnode.valid'.erase_aux
- \+ *theorem* ordnode.valid'.map_aux
- \+ *def* ordset.erase
- \+ *def* ordset.find
- \+ *def* ordset.map
- \+ *def* ordset.mem
- \+ *theorem* ordset.pos_size_of_mem



## [2021-06-29 17:54:58](https://github.com/leanprover-community/mathlib/commit/d558350)
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
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \- *lemma* ordered_comm_group.le_of_mul_le_mul_left
- \- *lemma* ordered_comm_group.lt_of_mul_lt_mul_left
- \- *lemma* ordered_comm_group.mul_lt_mul_left'



## [2021-06-29 17:54:57](https://github.com/leanprover-community/mathlib/commit/bdf2d81)
feat(topology/continuous_function/stone_weierstrass): complex Stone-Weierstrass ([#8012](https://github.com/leanprover-community/mathlib/pull/8012))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.continuous_abs
- \+ *lemma* complex.continuous_norm_sq

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.topological_closure_map
- \+ *lemma* submodule.topological_closure_mono

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* continuous_linear_map.comp_left_continuous_bounded_apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* continuous_linear_map.comp_left_continuous_compact_apply
- \+ *lemma* continuous_linear_map.to_linear_comp_left_continuous_compact
- \+ *lemma* continuous_map.linear_isometry_bounded_of_compact_apply_apply
- \+ *lemma* continuous_map.linear_isometry_bounded_of_compact_symm_apply

Modified src/topology/continuous_function/stone_weierstrass.lean
- \+ *def* continuous_map.conj_invariant_subalgebra
- \+ *lemma* continuous_map.mem_conj_invariant_subalgebra
- \+ *theorem* continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
- \+ *lemma* subalgebra.separates_points.complex_to_real



## [2021-06-29 16:11:34](https://github.com/leanprover-community/mathlib/commit/4cdfbd2)
feat(data/setoid/partition): indexed partition ([#7910](https://github.com/leanprover-community/mathlib/pull/7910))
from LTE
Note that data/setoid/partition.lean, which already existed before this
PR, is currently not imported anywhere in mathlib. But it is used in LTE
and will be used in the next PR, in relation to locally constant
functions.
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.eq_mk_iff_out
- \+ *lemma* quotient.mk_eq_iff_out

Modified src/data/setoid/basic.lean
- \+/\- *lemma* quotient.eq_rel
- \+ *lemma* setoid.comap_rel
- \+ *lemma* setoid.comm'
- \+ *lemma* setoid.ker_apply_mk_out'
- \+ *lemma* setoid.ker_apply_mk_out

Modified src/data/setoid/partition.lean
- \+ *lemma* indexed_partition.Union
- \+ *lemma* indexed_partition.class_of
- \+ *lemma* indexed_partition.disjoint
- \+ *lemma* indexed_partition.eq
- \+ *def* indexed_partition.equiv_quotient
- \+ *lemma* indexed_partition.equiv_quotient_index
- \+ *lemma* indexed_partition.equiv_quotient_index_apply
- \+ *lemma* indexed_partition.equiv_quotient_symm_proj_apply
- \+ *lemma* indexed_partition.exists_mem
- \+ *lemma* indexed_partition.index_out'
- \+ *lemma* indexed_partition.index_some
- \+ *lemma* indexed_partition.mem_iff_index_eq
- \+ *def* indexed_partition.mk'
- \+ *def* indexed_partition.out
- \+ *lemma* indexed_partition.out_proj
- \+ *def* indexed_partition.proj
- \+ *lemma* indexed_partition.proj_eq_iff
- \+ *lemma* indexed_partition.proj_fiber
- \+ *lemma* indexed_partition.proj_out
- \+ *lemma* indexed_partition.proj_some_index
- \+ *lemma* indexed_partition.some_index
- \+ *structure* indexed_partition
- \+ *lemma* setoid.eqv_class_mem'



## [2021-06-29 14:28:25](https://github.com/leanprover-community/mathlib/commit/23ee7ea)
feat(analysis/normed_space/basic): int.norm_eq_abs ([#8117](https://github.com/leanprover-community/mathlib/pull/8117))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* int.norm_eq_abs



## [2021-06-29 14:28:24](https://github.com/leanprover-community/mathlib/commit/d249e53)
feat(algebra/ordered_group): add instances mixing `group` and `co(ntra)variant` ([#8072](https://github.com/leanprover-community/mathlib/pull/8072))
In an attempt to break off small parts of PR [#8060](https://github.com/leanprover-community/mathlib/pull/8060), I extracted some of the instances proven there to this PR.
This is part of the `order` refactor.
~~I tried to get rid of the `@`, but failed.  If you have a trick to avoid them, I would be very happy to learn it!~~  `@`s removed!
#### Estimated changes
Modified src/algebra/ordered_group.lean




## [2021-06-29 14:28:23](https://github.com/leanprover-community/mathlib/commit/70fcf99)
feat(group_theory/free_abelian_group_finsupp): isomorphism between `free_abelian_group` and `finsupp` ([#8046](https://github.com/leanprover-community/mathlib/pull/8046))
From LTE
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean
- \+/\- *lemma* free_abelian_group.map_of_apply

Added src/group_theory/free_abelian_group_finsupp.lean
- \+ *def* finsupp.to_free_abelian_group
- \+ *lemma* finsupp.to_free_abelian_group_comp_single_add_hom
- \+ *lemma* finsupp.to_free_abelian_group_comp_to_finsupp
- \+ *lemma* finsupp.to_free_abelian_group_to_finsupp
- \+ *def* free_abelian_group.coeff
- \+ *def* free_abelian_group.equiv_finsupp
- \+ *lemma* free_abelian_group.mem_support_iff
- \+ *lemma* free_abelian_group.not_mem_support_iff
- \+ *def* free_abelian_group.support
- \+ *lemma* free_abelian_group.support_add
- \+ *lemma* free_abelian_group.support_gsmul
- \+ *lemma* free_abelian_group.support_neg
- \+ *lemma* free_abelian_group.support_nsmul
- \+ *lemma* free_abelian_group.support_of
- \+ *lemma* free_abelian_group.support_zero
- \+ *def* free_abelian_group.to_finsupp
- \+ *lemma* free_abelian_group.to_finsupp_comp_to_free_abelian_group
- \+ *lemma* free_abelian_group.to_finsupp_of
- \+ *lemma* free_abelian_group.to_finsupp_to_free_abelian_group



## [2021-06-29 13:33:01](https://github.com/leanprover-community/mathlib/commit/68d7d00)
chore(analysis/special_functions/pow): versions of tendsto/continuous_at lemmas for (e)nnreal ([#8113](https://github.com/leanprover-community/mathlib/pull/8113))
We have the full suite of lemmas about `tendsto` and `continuous` for real powers of `real`, but apparently not for `nnreal` or `ennreal`.  I have provided a few, rather painfully -- if there is a better way, golfing is welcome!
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.continuous_rpow_const
- \+ *theorem* ennreal.tendsto_rpow_at_top
- \+ *theorem* nnreal.tendsto_rpow_at_top

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.continuous_at_coe_iff
- \+ *lemma* ennreal.tendsto_nhds_coe_iff



## [2021-06-29 12:50:05](https://github.com/leanprover-community/mathlib/commit/54eccb0)
feat(measure_theory/lp_space): add snorm_eq_lintegral_rpow_nnnorm ([#8115](https://github.com/leanprover-community/mathlib/pull/8115))
Add two lemmas to go from `snorm` to integrals (through `snorm'`). The idea is that `snorm'` should then generally not be used, except in the construction of `snorm`.
#### Estimated changes
Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.snorm_eq_lintegral_rpow_nnnorm
- \+ *lemma* measure_theory.snorm_one_eq_lintegral_nnnorm



## [2021-06-29 11:29:09](https://github.com/leanprover-community/mathlib/commit/90d2046)
feat(algebra/monoid_algebra): adjointness for the functor `G ↦ monoid_algebra k G` when `G` carries only `has_mul` ([#7932](https://github.com/leanprover-community/mathlib/pull/7932))
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *lemma* distrib_mul_action_hom.ext_ring
- \+ *lemma* distrib_mul_action_hom.ext_ring_iff
- \+ *lemma* distrib_mul_action_hom.to_add_monoid_hom_injective
- \+ *lemma* distrib_mul_action_hom.to_mul_action_hom_injective

Modified src/algebra/module/linear_map.lean
- \+ *lemma* distrib_mul_action_hom.coe_to_linear_map
- \+ *def* distrib_mul_action_hom.to_linear_map
- \+ *lemma* distrib_mul_action_hom.to_linear_map_eq_coe
- \+ *lemma* distrib_mul_action_hom.to_linear_map_injective

Modified src/algebra/monoid_algebra.lean
- \+ *def* add_monoid_algebra.lift_magma
- \+ *lemma* add_monoid_algebra.non_unital_alg_hom_ext'
- \+ *lemma* add_monoid_algebra.non_unital_alg_hom_ext
- \+ *def* add_monoid_algebra.of_magma
- \+ *def* monoid_algebra.lift_magma
- \+ *lemma* monoid_algebra.non_unital_alg_hom_ext'
- \+ *lemma* monoid_algebra.non_unital_alg_hom_ext
- \+/\- *def* monoid_algebra.of
- \- *lemma* monoid_algebra.of_apply
- \+ *def* monoid_algebra.of_magma

Modified src/algebra/non_unital_alg_hom.lean
- \+ *lemma* non_unital_alg_hom.to_distrib_mul_action_hom_injective
- \+ *lemma* non_unital_alg_hom.to_mul_hom_injective

Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.distrib_mul_action_hom.single
- \+ *lemma* finsupp.distrib_mul_action_hom_ext'
- \+ *lemma* finsupp.distrib_mul_action_hom_ext



## [2021-06-29 10:46:12](https://github.com/leanprover-community/mathlib/commit/d521b2b)
feat(algebraic_topology/simplex_category): epi and monos in the simplex category ([#8101](https://github.com/leanprover-community/mathlib/pull/8101))
Characterize epimorphisms and monomorphisms in `simplex_category` in terms of the function they represent. Add lemmas about their behavior on length of objects.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* simplex_category.epi_iff_surjective
- \+ *lemma* simplex_category.le_of_epi
- \+ *lemma* simplex_category.le_of_mono
- \+ *lemma* simplex_category.len_le_of_epi
- \+ *lemma* simplex_category.len_le_of_mono
- \+ *theorem* simplex_category.mono_iff_injective



## [2021-06-29 06:55:39](https://github.com/leanprover-community/mathlib/commit/07f1235)
chore(category_theory/opposites): make hom explicit in lemmas ([#8088](https://github.com/leanprover-community/mathlib/pull/8088))
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* quiver.hom.op_unop
- \+/\- *lemma* quiver.hom.unop_op



## [2021-06-28 20:13:06](https://github.com/leanprover-community/mathlib/commit/ac156c1)
chore(algebra/algebra/basic): add algebra.right_comm to match left_comm ([#8109](https://github.com/leanprover-community/mathlib/pull/8109))
This also reorders the arguments to `right_comm` to match the order they appear in the LHS of the lemma.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *theorem* algebra.left_comm
- \+ *theorem* algebra.right_comm



## [2021-06-28 16:40:09](https://github.com/leanprover-community/mathlib/commit/a79df55)
chore(algebra/ordered_group): remove linear_ordered_comm_group.to_comm_group ([#7861](https://github.com/leanprover-community/mathlib/pull/7861))
This instance shortcut bypassed `ordered_comm_group`, and could easily result in computability problems since many `linear_order` instances are noncomputable due to their embedded decidable instances. This would happen when:
* Lean needs an `add_comm_group A`
* We have:
  * `noncomputable instance : linear_ordered_comm_group A`
  * `instance : ordered_comm_group A`
* Lean tries `linear_ordered_comm_group.to_comm_group` before `ordered_comm_group.to_comm_group`, and hands us back a noncomputable one, even though there is a computable one available.
There're no comments explaining why things were done this way, suggesting it was accidental, or perhaps that `ordered_comm_group` came later.
This broke one proof which somehow `simponly`ed associativity the wrong way, so I just golfed that proof and the one next to it for good measure.
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/data/nat/modeq.lean




## [2021-06-28 15:38:22](https://github.com/leanprover-community/mathlib/commit/1ffb5be)
feat(data/complex/module): add complex.alg_hom_ext ([#8105](https://github.com/leanprover-community/mathlib/pull/8105))
#### Estimated changes
Modified src/data/complex/module.lean
- \+ *lemma* alg_hom.map_coe_real_complex
- \+ *lemma* complex.alg_hom_ext



## [2021-06-28 13:54:02](https://github.com/leanprover-community/mathlib/commit/b160ac8)
chore(topology/topological_fiber_bundle): reorganizing the code ([#7989](https://github.com/leanprover-community/mathlib/pull/7989))
Mainly redesigning the `simp` strategy.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+ *lemma* local_equiv.source_inter_preimage_target_inter

Modified src/data/set/basic.lean
- \+/\- *theorem* set.preimage_const_of_mem
- \+/\- *theorem* set.preimage_const_of_not_mem

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous.prod.mk

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.is_open_preimage

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.source_inter_preimage_target_inter

Modified src/topology/order.lean
- \+ *lemma* is_open_induced_iff'
- \+ *lemma* le_induced_generate_from

Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* bundle.coe_fst
- \+ *lemma* bundle.coe_snd_map_apply
- \+ *lemma* bundle.coe_snd_map_smul
- \+ *def* bundle.total_space_mk
- \+ *lemma* topological_fiber_bundle_core.base_set_at
- \+ *lemma* topological_fiber_bundle_core.continuous_total_space_mk
- \+/\- *lemma* topological_fiber_bundle_core.local_triv'_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv'_coe
- \+ *lemma* topological_fiber_bundle_core.local_triv'_source
- \+/\- *lemma* topological_fiber_bundle_core.local_triv'_symm_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv'_target
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_apply
- \- *def* topological_fiber_bundle_core.local_triv_at
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_apply
- \+/\- *def* topological_fiber_bundle_core.local_triv_at_ext
- \+ *lemma* topological_fiber_bundle_core.local_triv_at_ext_def
- \- *lemma* topological_fiber_bundle_core.local_triv_at_ext_to_local_homeomorph
- \- *lemma* topological_fiber_bundle_core.local_triv_at_fst
- \- *lemma* topological_fiber_bundle_core.local_triv_at_symm_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_coe
- \+ *lemma* topological_fiber_bundle_core.local_triv_ext_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv_ext_symm_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv_ext_symm_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_source
- \+ *lemma* topological_fiber_bundle_core.local_triv_symm
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_symm_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv_target
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv'_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv'_target
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_at_ext_base_set
- \- *lemma* topological_fiber_bundle_core.mem_local_triv_at_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_ext_source
- \+ *lemma* topological_fiber_bundle_core.mem_local_triv_ext_target
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_target

Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.trivialization.coe_coe
- \+ *lemma* topological_vector_bundle.trivialization.coe_fst



## [2021-06-28 12:36:08](https://github.com/leanprover-community/mathlib/commit/f7c1e5f)
feat(algebra/lie/nilpotent): basic lemmas about nilpotency for Lie subalgebras of associative algebras ([#8090](https://github.com/leanprover-community/mathlib/pull/8090))
The main lemma is: `lie_algebra.is_nilpotent_ad_of_is_nilpotent` which is the first step in proving Engel's theorem.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.commute_lmul_left_right
- \+ *lemma* algebra.lmul_left_eq_zero_iff
- \+ *lemma* algebra.lmul_left_zero_eq_zero
- \+ *lemma* algebra.lmul_right_eq_zero_iff
- \+ *lemma* algebra.lmul_right_zero_eq_zero
- \+ *lemma* algebra.pow_lmul_left
- \+ *lemma* algebra.pow_lmul_right

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_algebra.ad_nilpotent_of_nilpotent
- \+ *lemma* lie_algebra.is_nilpotent_ad_of_is_nilpotent
- \+ *lemma* lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_algebra.ad_eq_lmul_left_sub_lmul_right
- \+ *lemma* lie_subalgebra.ad_comp_incl_eq

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.submodule_pow_eq_zero_of_pow_eq_zero

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* algebra.is_nilpotent_lmul_left_iff
- \+ *lemma* algebra.is_nilpotent_lmul_right_iff



## [2021-06-28 11:54:29](https://github.com/leanprover-community/mathlib/commit/81183ea)
feat(geometry/manifold): `derivation_bundle` ([#7708](https://github.com/leanprover-community/mathlib/pull/7708))
In this PR we define the `derivation_bundle`. Note that this definition is purely algebraic and that the whole geometry/analysis is contained in the algebra structure of smooth global functions on the manifold.
I believe everything runs smoothly and elegantly and that most proofs can be naturally done by `rfl`. To anticipate some discussions that already arose on Zulip about 9 months ago, note that the content of these files is purely algebraic and that there is no intention whatsoever to replace the current tangent bundle. I prefer this definition to the one given through the adjoint representation, because algebra is more easily formalized and simp can solve most proofs with this definition. However, in the future, there will be also the adjoint representation for sure.
#### Estimated changes
Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_ring.lie_apply

Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *def* smooth_map.eval_ring_hom

Added src/geometry/manifold/derivation_bundle.lean
- \+ *lemma* apply_fdifferential
- \+ *def* derivation.eval_at
- \+ *lemma* derivation.eval_at_apply
- \+ *def* fdifferential
- \+ *lemma* fdifferential_comp
- \+ *def* fdifferential_map
- \+ *def* point_derivation
- \+ *def* pointed_smooth_map.eval
- \+ *lemma* pointed_smooth_map.smul_def
- \+ *def* pointed_smooth_map
- \+ *def* smooth_function.eval_at



## [2021-06-28 10:36:19](https://github.com/leanprover-community/mathlib/commit/bfd0685)
fix(algebra/module/linear_map): do not introduce `show` ([#8102](https://github.com/leanprover-community/mathlib/pull/8102))
Without this change, `apply linear_map.coe_injective` on a goal of `f = g` introduces some unpleasant `show` terms, giving a goal of
```lean
(λ (f : M →ₗ[R] M₂), show M → M₂, from ⇑f) f = (λ (f : M →ₗ[R] M₂), show M → M₂, from ⇑f) g
```
which is then frustrating to `rw` at, instead of
```lean
⇑f = ⇑g
```
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *theorem* linear_map.coe_injective



## [2021-06-28 08:51:27](https://github.com/leanprover-community/mathlib/commit/3cb247c)
chore(algebra/ordered_monoid_lemmas): change additive name `left.add_nonneg` to `right.add_nonneg` ([#8065](https://github.com/leanprover-community/mathlib/pull/8065))
A copy-paste error in the name of a lemma that has not been used yet.
Change `pos_add` to `add_pos`.
I also added some paragraph breaks in the documentation.
Co-authored by Eric Wieser.
#### Estimated changes
Modified src/algebra/ordered_monoid_lemmas.lean




## [2021-06-28 06:13:33](https://github.com/leanprover-community/mathlib/commit/80d0234)
fix(algebra/group_power): put opposite lemmas in the right namespace ([#8100](https://github.com/leanprover-community/mathlib/pull/8100))
#### Estimated changes
Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* opposite.op_pow
- \+ *lemma* opposite.unop_pow
- \- *lemma* units.op_pow
- \- *lemma* units.unop_pow



## [2021-06-28 04:53:22](https://github.com/leanprover-community/mathlib/commit/7b253dd)
feat(group_theory/subgroup): lemmas for normal subgroups of subgroups ([#7271](https://github.com/leanprover-community/mathlib/pull/7271))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.comap_bot
- \+/\- *lemma* monoid_hom.range_restrict_ker
- \+ *lemma* subgroup.coe_subgroup_of
- \+/\- *lemma* subgroup.comap_injective
- \+/\- *lemma* subgroup.comap_map_eq
- \+/\- *lemma* subgroup.comap_map_eq_self
- \+/\- *lemma* subgroup.comap_map_eq_self_of_injective
- \+ *lemma* subgroup.comap_sup_comap_le
- \+ *lemma* subgroup.comap_sup_eq
- \+ *lemma* subgroup.inf_mul_assoc
- \+ *lemma* subgroup.inf_subgroup_of_inf_normal_of_left
- \+ *lemma* subgroup.inf_subgroup_of_inf_normal_of_right
- \+/\- *lemma* subgroup.ker_le_comap
- \+/\- *lemma* subgroup.le_comap_map
- \+/\- *lemma* subgroup.map_comap_eq
- \+/\- *lemma* subgroup.map_comap_eq_self
- \+/\- *lemma* subgroup.map_comap_eq_self_of_surjective
- \+/\- *lemma* subgroup.map_comap_le
- \+/\- *lemma* subgroup.map_eq_comap_of_inverse
- \+ *lemma* subgroup.map_inf_eq
- \+ *lemma* subgroup.map_inf_le
- \+/\- *lemma* subgroup.map_injective
- \+ *lemma* subgroup.map_injective_of_ker_le
- \+/\- *lemma* subgroup.map_le_range
- \+ *lemma* subgroup.mem_subgroup_of
- \+ *lemma* subgroup.mul_inf_assoc
- \+ *lemma* subgroup.normal_subgroup_of_iff
- \+ *lemma* subgroup.subgroup_normal.mem_comm
- \+ *def* subgroup.subgroup_of
- \+ *lemma* subgroup.subgroup_of_map_subtype
- \+ *lemma* subgroup.subgroup_of_sup
- \+ *lemma* subgroup.supr_comap_le



## [2021-06-27 15:45:05](https://github.com/leanprover-community/mathlib/commit/f8e9c17)
feat(data/nat/factorial): descending factorial ([#7759](https://github.com/leanprover-community/mathlib/pull/7759))
- rename `desc_fac` to `asc_factorial`
- define `desc_factorial`
- update `data.fintype.card_embedding` to use `desc_factorial`
#### Estimated changes
Modified archive/100-theorems-list/93_birthday_problem.lean


Modified docs/100.yaml


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card_embedding.lean
- \- *theorem* fintype.card_embedding
- \+ *theorem* fintype.card_embedding_eq
- \- *theorem* fintype.card_embedding_eq_if
- \- *lemma* fintype.card_embedding_eq_infinite
- \+ *lemma* fintype.card_embedding_eq_of_infinite
- \+ *lemma* fintype.card_embedding_eq_of_unique
- \- *theorem* fintype.card_embedding_eq_zero
- \- *lemma* fintype.card_embedding_of_unique

Modified src/data/nat/choose/basic.lean
- \+ *lemma* nat.asc_factorial_eq_factorial_mul_choose
- \+ *lemma* nat.choose_eq_asc_factorial_div_factorial
- \- *lemma* nat.choose_eq_desc_fac_div_factorial
- \+ *lemma* nat.choose_eq_desc_factorial_div_factorial
- \- *lemma* nat.desc_fac_eq_factorial_mul_choose
- \+ *lemma* nat.desc_factorial_eq_factorial_mul_choose
- \+ *lemma* nat.factorial_dvd_asc_factorial
- \- *lemma* nat.factorial_dvd_desc_fac
- \+ *lemma* nat.factorial_dvd_desc_factorial

Modified src/data/nat/factorial.lean
- \+ *lemma* nat.add_desc_factorial_eq_asc_factorial
- \+ *def* nat.asc_factorial
- \+ *lemma* nat.asc_factorial_eq_div
- \+ *lemma* nat.asc_factorial_le_pow_add
- \+ *lemma* nat.asc_factorial_lt_pow_add
- \+ *lemma* nat.asc_factorial_of_sub
- \+ *lemma* nat.asc_factorial_pos
- \+ *lemma* nat.asc_factorial_succ
- \+ *lemma* nat.asc_factorial_zero
- \- *def* nat.desc_fac
- \- *lemma* nat.desc_fac_eq_div
- \- *lemma* nat.desc_fac_of_sub
- \- *lemma* nat.desc_fac_succ
- \- *lemma* nat.desc_fac_zero
- \+ *def* nat.desc_factorial
- \+ *lemma* nat.desc_factorial_eq_div
- \+ *lemma* nat.desc_factorial_eq_zero_iff_lt
- \+ *lemma* nat.desc_factorial_le_pow
- \+ *lemma* nat.desc_factorial_lt_pow
- \+ *lemma* nat.desc_factorial_one
- \+ *lemma* nat.desc_factorial_self
- \+ *lemma* nat.desc_factorial_succ
- \+ *lemma* nat.desc_factorial_zero
- \+/\- *def* nat.factorial
- \+/\- *lemma* nat.factorial_inj
- \+/\- *lemma* nat.factorial_lt
- \+ *theorem* nat.factorial_mul_asc_factorial
- \- *theorem* nat.factorial_mul_desc_fac
- \+ *theorem* nat.factorial_mul_desc_factorial
- \+ *lemma* nat.pow_lt_asc_factorial'
- \+ *lemma* nat.pow_lt_asc_factorial
- \+ *lemma* nat.pow_sub_le_desc_factorial
- \+ *lemma* nat.pow_sub_lt_desc_factorial'
- \+ *lemma* nat.pow_sub_lt_desc_factorial
- \+ *lemma* nat.pow_succ_le_asc_factorial
- \+ *lemma* nat.succ_asc_factorial
- \- *lemma* nat.succ_desc_fac
- \+ *lemma* nat.succ_desc_factorial
- \+ *lemma* nat.succ_desc_factorial_succ
- \+ *lemma* nat.zero_asc_factorial
- \- *lemma* nat.zero_desc_fac
- \+ *lemma* nat.zero_desc_factorial_succ

Modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_nat_eq_asc_factorial
- \- *lemma* pochhammer_nat_eq_desc_fac



## [2021-06-27 13:01:13](https://github.com/leanprover-community/mathlib/commit/2dcc307)
feat(category_theory/limits): morphism to terminal is split mono ([#8084](https://github.com/leanprover-community/mathlib/pull/8084))
A generalisation of existing results: we already have an instance `split_mono` to `mono` so this is strictly more general.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.is_initial.split_epi_to
- \+ *def* category_theory.limits.is_terminal.split_mono_from



## [2021-06-27 02:15:39](https://github.com/leanprover-community/mathlib/commit/c5d17ae)
chore(scripts): update nolints.txt ([#8093](https://github.com/leanprover-community/mathlib/pull/8093))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-26 22:33:31](https://github.com/leanprover-community/mathlib/commit/c7a35b4)
doc(topology/homeomorph): fixup glaring error ([#8092](https://github.com/leanprover-community/mathlib/pull/8092))
thanks to @kbuzzard for spotting this error in [#8086](https://github.com/leanprover-community/mathlib/pull/8086)
#### Estimated changes
Modified src/topology/homeomorph.lean




## [2021-06-26 20:35:05](https://github.com/leanprover-community/mathlib/commit/0817020)
doc(topology/homeomorph): module docs ([#8086](https://github.com/leanprover-community/mathlib/pull/8086))
I really wanted to write more, but there's really not much to say about something that is a stronger bijection :b
#### Estimated changes
Modified src/topology/homeomorph.lean




## [2021-06-26 18:57:08](https://github.com/leanprover-community/mathlib/commit/b874abc)
feat(field_theory): state primitive element theorem using `power_basis` ([#8073](https://github.com/leanprover-community/mathlib/pull/8073))
This PR adds an alternative formulation to the primitive element theorem: the original formulation was `∃ α : E, F⟮α⟯ = (⊤ : intermediate_field F E)`, which means a lot of pushing things across the equality/equiv from `F⟮α⟯` to `E` itself. I claim that working with a field `E` that has a power basis over `F` is nicer since you don't need to do a lot of transporting.
#### Estimated changes
Modified src/field_theory/primitive_element.lean




## [2021-06-26 18:15:06](https://github.com/leanprover-community/mathlib/commit/598722a)
feat(algebraic_topology/simplicial_object): Add augment construction ([#8085](https://github.com/leanprover-community/mathlib/pull/8085))
Adds the augmentation construction for (co)simplicial objects.
From LTE.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* simplex_category.hom_zero_zero

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.cosimplicial_object.augment
- \+ *lemma* category_theory.cosimplicial_object.augment_hom_zero
- \+ *def* category_theory.simplicial_object.augment
- \+ *lemma* category_theory.simplicial_object.augment_hom_zero



## [2021-06-26 09:25:11](https://github.com/leanprover-community/mathlib/commit/4630067)
chore(data/set/intervals): syntax clean up ([#8087](https://github.com/leanprover-community/mathlib/pull/8087))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Iio_subset_Iic_self
- \+/\- *lemma* set.Ioi_subset_Ici_self



## [2021-06-25 21:10:33](https://github.com/leanprover-community/mathlib/commit/68ec06c)
chore(analysis/analytic/composition): remove one `have` ([#8083](https://github.com/leanprover-community/mathlib/pull/8083))
A `have` in a proof is not necessary.
#### Estimated changes
Modified src/analysis/analytic/composition.lean




## [2021-06-25 20:31:41](https://github.com/leanprover-community/mathlib/commit/92a7171)
feat(measure_theory/interval_integral): generalize `add_adjacent_intervals` to n-ary sum ([#8050](https://github.com/leanprover-community/mathlib/pull/8050))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable.trans_iterate
- \+ *lemma* interval_integral.sum_integral_adjacent_intervals



## [2021-06-25 18:48:54](https://github.com/leanprover-community/mathlib/commit/6666ba2)
fix(real/sign): make `real.sign 0 = 0` to match `int.sign 0` ([#8080](https://github.com/leanprover-community/mathlib/pull/8080))
Previously `sign 0 = 1` which is quite an unusual definition. This definition brings things in line with `int.sign`, and include a proof of this fact.
A future refactor could probably introduce a sign for all rings with a partial order
#### Estimated changes
Modified src/data/real/sign.lean
- \+/\- *def* real.sign
- \+/\- *lemma* real.sign_apply_eq
- \+ *lemma* real.sign_apply_eq_of_ne_zero
- \+ *lemma* real.sign_eq_zero_iff
- \+ *lemma* real.sign_int_cast
- \+/\- *lemma* real.sign_neg
- \- *lemma* real.sign_of_not_neg
- \+ *lemma* real.sign_of_pos
- \- *lemma* real.sign_of_zero_le
- \+/\- *lemma* real.sign_zero

Modified src/linear_algebra/quadratic_form.lean




## [2021-06-25 18:48:53](https://github.com/leanprover-community/mathlib/commit/a7faaf5)
docs(data/list/chain): add module docstring ([#8041](https://github.com/leanprover-community/mathlib/pull/8041))
#### Estimated changes
Modified src/data/list/chain.lean
- \+/\- *theorem* list.chain'_split
- \+/\- *theorem* list.chain_of_pairwise
- \+/\- *theorem* list.chain_split



## [2021-06-25 18:48:52](https://github.com/leanprover-community/mathlib/commit/cf4a2df)
docs(data/list/range): add module docstring ([#8026](https://github.com/leanprover-community/mathlib/pull/8026))
#### Estimated changes
Modified src/data/list/range.lean




## [2021-06-25 17:09:01](https://github.com/leanprover-community/mathlib/commit/9cc44ba)
feat(ring_theory/nilpotent): basic results about nilpotency in associative rings ([#8055](https://github.com/leanprover-community/mathlib/pull/8055))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_of_le

Added src/ring_theory/nilpotent.lean
- \+ *lemma* commute.is_nilpotent_add
- \+ *lemma* commute.is_nilpotent_mul_left
- \+ *lemma* commute.is_nilpotent_mul_right
- \+ *lemma* commute.is_nilpotent_sub
- \+ *lemma* is_nilpotent.eq_zero
- \+ *lemma* is_nilpotent.neg
- \+ *lemma* is_nilpotent.zero
- \+ *def* is_nilpotent
- \+ *lemma* is_nilpotent_iff_eq_zero
- \+ *lemma* is_nilpotent_neg_iff



## [2021-06-25 10:35:36](https://github.com/leanprover-community/mathlib/commit/1774cf9)
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
#### Estimated changes
Modified src/algebra/quaternion.lean
- \+ *lemma* quaternion.coe_conj_ae
- \- *lemma* quaternion.coe_conj_alg_equiv
- \+ *def* quaternion.conj_ae
- \- *def* quaternion.conj_alg_equiv
- \+ *lemma* quaternion_algebra.coe_conj_ae
- \- *lemma* quaternion_algebra.coe_conj_alg_equiv
- \+ *def* quaternion_algebra.conj_ae
- \- *def* quaternion_algebra.conj_alg_equiv

Modified src/analysis/complex/basic.lean
- \+ *def* complex.conj_cle
- \+ *lemma* complex.conj_cle_apply
- \+ *lemma* complex.conj_cle_coe
- \+ *lemma* complex.conj_cle_norm
- \- *def* complex.conj_clm
- \- *lemma* complex.conj_clm_apply
- \- *lemma* complex.conj_clm_coe
- \- *lemma* complex.conj_clm_norm
- \- *def* complex.conj_li
- \- *lemma* complex.conj_li_apply
- \+ *def* complex.conj_lie
- \+ *lemma* complex.conj_lie_apply
- \+/\- *lemma* complex.continuous_conj
- \+/\- *lemma* complex.continuous_of_real
- \+/\- *lemma* complex.isometry_conj
- \+/\- *lemma* complex.of_real_clm_apply
- \+/\- *lemma* complex.of_real_clm_coe
- \+/\- *def* complex.of_real_li

Modified src/analysis/complex/circle.lean


Modified src/analysis/complex/isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.conj_ae_coe
- \+ *lemma* is_R_or_C.conj_cle_apply
- \+ *lemma* is_R_or_C.conj_cle_coe
- \+ *lemma* is_R_or_C.conj_cle_norm
- \- *lemma* is_R_or_C.conj_clm_apply
- \- *lemma* is_R_or_C.conj_clm_coe
- \- *lemma* is_R_or_C.conj_clm_norm
- \- *lemma* is_R_or_C.conj_li_apply
- \+ *lemma* is_R_or_C.conj_lie_apply
- \- *lemma* is_R_or_C.conj_lm_coe
- \+/\- *lemma* is_R_or_C.continuous_conj
- \+ *lemma* is_R_or_C.of_real_am_coe
- \+/\- *lemma* is_R_or_C.of_real_clm_coe
- \+/\- *lemma* is_R_or_C.of_real_li_apply
- \- *lemma* is_R_or_C.of_real_lm_coe

Modified src/data/complex/module.lean
- \+ *def* complex.conj_ae
- \+ *lemma* complex.conj_ae_coe
- \- *def* complex.conj_alg_equiv
- \- *def* complex.conj_lm
- \- *lemma* complex.conj_lm_coe
- \+ *def* complex.of_real_am
- \+ *lemma* complex.of_real_am_coe
- \- *def* complex.of_real_lm
- \- *lemma* complex.of_real_lm_coe

Modified src/field_theory/polynomial_galois_group.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/set_integral.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.to_linear_map_eq_coe



## [2021-06-25 09:21:01](https://github.com/leanprover-community/mathlib/commit/c515346)
feat(ring_theory/power_basis): map a power basis through an alg_equiv ([#8039](https://github.com/leanprover-community/mathlib/pull/8039))
If `A` is equivalent to `A'` as an `R`-algebra and `A` has a power basis, then `A'` also has a power basis. Included are the relevant `simp` lemmas.
This needs a bit of tweaking to `basis.map` and `alg_equiv.to_linear_equiv` for getting more useful `simp` lemmas.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *def* alg_equiv.to_linear_equiv
- \- *lemma* alg_equiv.to_linear_equiv_apply
- \+ *lemma* alg_equiv.to_linear_equiv_refl
- \+ *lemma* alg_equiv.to_linear_equiv_symm
- \+ *lemma* alg_equiv.to_linear_equiv_trans

Modified src/linear_algebra/basis.lean


Modified src/ring_theory/power_basis.lean
- \+ *lemma* power_basis.equiv_map
- \+ *lemma* power_basis.minpoly_gen_map



## [2021-06-25 07:18:41](https://github.com/leanprover-community/mathlib/commit/10cd252)
docs(overview, undergrad): add Liouville's Theorem on existence of transcendental numbers ([#8068](https://github.com/leanprover-community/mathlib/pull/8068))
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Renamed src/analysis/liouville/basic.lean to src/number_theory/liouville/basic.lean


Renamed src/analysis/liouville/liouville_constant.lean to src/number_theory/liouville/liouville_constant.lean




## [2021-06-24 21:57:47](https://github.com/leanprover-community/mathlib/commit/2608244)
feat(data/matrix/basic): add lemma minor_map  ([#8074](https://github.com/leanprover-community/mathlib/pull/8074))
Add lemma `minor_map` proving that the operations of taking a minor and applying a map to the coefficients of a matrix commute.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.minor_map



## [2021-06-24 21:15:20](https://github.com/leanprover-community/mathlib/commit/e137523)
chore(algebraic_topology/simplex_category): golf proof ([#8076](https://github.com/leanprover-community/mathlib/pull/8076))
The "special case of the first simplicial identity" is a trivial consequence of the "generic case". This makes me wonder whether the special case should be there at all but I do not know the standard references for this stuff.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean




## [2021-06-24 19:39:06](https://github.com/leanprover-community/mathlib/commit/e605b21)
feat(linear_algebra/pi): add linear_equiv.Pi_congr_left ([#8070](https://github.com/leanprover-community/mathlib/pull/8070))
This definition was hiding inside the proof for `is_noetherian_pi`
#### Estimated changes
Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.Pi_congr_left'
- \+ *def* linear_equiv.Pi_congr_left

Modified src/ring_theory/noetherian.lean




## [2021-06-24 16:50:00](https://github.com/leanprover-community/mathlib/commit/25d8aac)
chore(field_theory): turn `intermediate_field.subalgebra.equiv_of_eq`  into `intermediate_field.equiv_of_eq` ([#8069](https://github.com/leanprover-community/mathlib/pull/8069))
I was looking for `intermediate_field.equiv_of_eq`. There was a definition of `subalgebra.equiv_of_eq` in the `intermediate_field` namespace which is equal to the original `subalgebra.equiv_of_eq` definition. Meanwhile, there was no `intermediate_field.equiv_of_eq`. So I decided to turn the duplicate into what I think was intended. (As a bonus, I added the `simp` lemmas from `subalgebra.equiv_of_eq`.)
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *def* intermediate_field.equiv_of_eq
- \+ *lemma* intermediate_field.equiv_of_eq_rfl
- \+ *lemma* intermediate_field.equiv_of_eq_symm
- \+ *lemma* intermediate_field.equiv_of_eq_trans
- \- *def* intermediate_field.subalgebra.equiv_of_eq



## [2021-06-24 15:14:30](https://github.com/leanprover-community/mathlib/commit/db84f2b)
feat(data/polynomial): `aeval_alg_equiv`, like `aeval_alg_hom` ([#8038](https://github.com/leanprover-community/mathlib/pull/8038))
This PR copies `polynomial.aeval_alg_hom` and `aeval_alg_hom_apply` to `aeval_alg_equiv(_apply)`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *theorem* polynomial.aeval_alg_equiv
- \+ *theorem* polynomial.aeval_alg_equiv_apply



## [2021-06-24 15:14:29](https://github.com/leanprover-community/mathlib/commit/2a15520)
chore(data/polynomial): generalize `aeval_eq_sum_range` to `comm_semiring` ([#8037](https://github.com/leanprover-community/mathlib/pull/8037))
This pair of lemmas did not need any `comm_ring` assumptions, so I put them in a new section with weaker typeclass assumptions.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean




## [2021-06-24 15:14:28](https://github.com/leanprover-community/mathlib/commit/3937c1b)
docs(data/list/pairwise): add module docstring ([#8025](https://github.com/leanprover-community/mathlib/pull/8025))
#### Estimated changes
Modified src/data/list/pairwise.lean




## [2021-06-24 15:14:27](https://github.com/leanprover-community/mathlib/commit/520e79d)
feat(analysis/convex/exposed): introduce exposed sets ([#7928](https://github.com/leanprover-community/mathlib/pull/7928))
introduce exposed sets
#### Estimated changes
Added src/analysis/convex/exposed.lean
- \+ *lemma* continuous_linear_map.to_exposed.is_exposed
- \+ *def* continuous_linear_map.to_exposed
- \+ *lemma* exposed_point_def
- \+ *lemma* exposed_points_empty
- \+ *lemma* exposed_points_subset
- \+ *lemma* exposed_points_subset_extreme_points
- \+ *lemma* is_exposed.antisymm
- \+ *lemma* is_exposed.eq_inter_halfspace
- \+ *lemma* is_exposed.inter
- \+ *lemma* is_exposed.inter_left
- \+ *lemma* is_exposed.inter_right
- \+ *lemma* is_exposed.is_closed
- \+ *lemma* is_exposed.is_compact
- \+ *lemma* is_exposed.refl
- \+ *lemma* is_exposed.sInter
- \+ *def* is_exposed
- \+ *lemma* is_exposed_empty
- \+ *lemma* mem_exposed_points_iff_exposed_singleton
- \+ *def* set.exposed_points

Modified src/analysis/convex/extreme.lean




## [2021-06-24 15:14:26](https://github.com/leanprover-community/mathlib/commit/4801fa6)
feat(measure_theory): the Vitali-Caratheodory theorem ([#7766](https://github.com/leanprover-community/mathlib/pull/7766))
This PR proves the Vitali-Carathéodory theorem, asserting that a measurable function can be closely approximated from above by a lower semicontinuous function, and from below by an upper semicontinuous function. 
This is the main ingredient in the proof of the general version of the fundamental theorem of calculus (when `f'` is just integrable, but not continuous).
#### Estimated changes
Added src/measure_theory/vitali_caratheodory.lean
- \+ *lemma* measure_theory.exists_le_lower_semicontinuous_lintegral_ge
- \+ *lemma* measure_theory.exists_lt_lower_semicontinuous_integral_gt_nnreal
- \+ *lemma* measure_theory.exists_lt_lower_semicontinuous_integral_lt
- \+ *lemma* measure_theory.exists_lt_lower_semicontinuous_lintegral_ge
- \+ *lemma* measure_theory.exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable
- \+ *lemma* measure_theory.exists_upper_semicontinuous_le_integral_le
- \+ *lemma* measure_theory.exists_upper_semicontinuous_le_lintegral_le
- \+ *lemma* measure_theory.exists_upper_semicontinuous_lt_integral_gt
- \+ *lemma* measure_theory.simple_func.exists_le_lower_semicontinuous_lintegral_ge
- \+ *lemma* measure_theory.simple_func.exists_upper_semicontinuous_le_lintegral_le



## [2021-06-24 13:55:29](https://github.com/leanprover-community/mathlib/commit/b9bf921)
chore(linear_algebra): switch to named constructors for linear_map ([#8059](https://github.com/leanprover-community/mathlib/pull/8059))
This makes some ideas I have for future refactors easier, and generally makes things less fragile to changes such as additional fields or reordering of fields.
The extra verbosity is not really significant.
This conversion is not exhaustive, there may be anonymous constructors elsewhere that I've missed.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *def* is_linear_map.mk'
- \+/\- *theorem* linear_equiv.apply_symm_apply
- \+/\- *theorem* linear_equiv.symm_apply_apply
- \+/\- *def* linear_map.comp
- \+/\- *theorem* linear_map.is_linear

Modified src/analysis/normed_space/operator_norm.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* submodule.mkq

Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/pi.lean


Modified src/linear_algebra/prod.lean
- \+/\- *def* linear_map.fst
- \+/\- *def* linear_map.snd

Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/hahn_series.lean


Modified src/topology/algebra/module.lean
- \+/\- *theorem* continuous_linear_equiv.apply_symm_apply
- \+/\- *theorem* continuous_linear_equiv.symm_apply_apply

Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_one

Modified src/topology/instances/real_vector_space.lean




## [2021-06-24 12:48:16](https://github.com/leanprover-community/mathlib/commit/2a1cabe)
chore(data/polynomial/eval, ring_theory/polynomial_algebra): golfs ([#8058](https://github.com/leanprover-community/mathlib/pull/8058))
This golfs:
* `polynomial.map_nat_cast` to use `ring_hom.map_nat_cast`
* `polynomial.map.is_semiring_hom` to use `ring_hom.is_semiring_hom`
* `poly_equiv_tensor.to_fun` and `poly_equiv_tensor.to_fun_linear_right` out of existence
And adds a new (unused) lemma `polynomial.map_smul`.
All the other changes in `polynomial/eval` are just reorderings of lemmas to allow the golfing.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_smul

Modified src/ring_theory/polynomial_algebra.lean
- \- *def* poly_equiv_tensor.to_fun
- \+/\- *def* poly_equiv_tensor.to_fun_bilinear
- \+ *lemma* poly_equiv_tensor.to_fun_bilinear_apply_eq_sum
- \- *def* poly_equiv_tensor.to_fun_linear_right
- \+ *lemma* poly_equiv_tensor.to_fun_linear_tmul_apply



## [2021-06-24 11:32:46](https://github.com/leanprover-community/mathlib/commit/5352639)
feat(data/matrix/basic.lean) : added map_scalar and linear_map.map_matrix ([#8061](https://github.com/leanprover-community/mathlib/pull/8061))
Added two lemmas (`map_scalar` and `linear_map.map_matrix_apply`) and a definition (`linear_map.map_matrix`) showing that a map between coefficients induces the same type of map between matrices with those coefficients.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *def* linear_map.map_matrix
- \+ *lemma* matrix.map_smul



## [2021-06-24 09:57:32](https://github.com/leanprover-community/mathlib/commit/5bd649f)
feat(analysis/liouville/liouville_constant): transcendental Liouville numbers exist! ([#8020](https://github.com/leanprover-community/mathlib/pull/8020))
The final (hopefully!) PR in the Liouville series: there are a couple of results and the proof that Liouville numbers are transcendental.
#### Estimated changes
Modified src/analysis/liouville/liouville_constant.lean
- \+/\- *lemma* liouville.aux_calc
- \+ *theorem* liouville.is_liouville
- \+ *lemma* liouville.is_transcendental
- \+/\- *lemma* liouville.liouville_number_eq_initial_terms_add_tail
- \+ *lemma* liouville.liouville_number_rat_initial_terms
- \+/\- *lemma* liouville.liouville_number_tail_pos
- \+/\- *lemma* liouville.tsum_one_div_pow_factorial_lt



## [2021-06-24 09:57:31](https://github.com/leanprover-community/mathlib/commit/f7f12bc)
feat(data/nat/prime): norm_num plugin for factors ([#8009](https://github.com/leanprover-community/mathlib/pull/8009))
Implements a `norm_num` plugin to evaluate terms like `nat.factors 231 = [3, 7, 11]`.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_chain'
- \+ *lemma* nat.factors_chain
- \+ *lemma* nat.factors_chain_2
- \+ *lemma* nat.factors_sorted
- \+ *theorem* nat.le_min_fac'
- \+ *theorem* nat.le_min_fac
- \+ *def* tactic.norm_num.factors_helper
- \+ *lemma* tactic.norm_num.factors_helper_cons'
- \+ *lemma* tactic.norm_num.factors_helper_cons
- \+ *lemma* tactic.norm_num.factors_helper_end
- \+ *lemma* tactic.norm_num.factors_helper_nil
- \+ *lemma* tactic.norm_num.factors_helper_same
- \+ *lemma* tactic.norm_num.factors_helper_same_sn
- \+ *lemma* tactic.norm_num.factors_helper_sn

Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2021-06-24 09:57:30](https://github.com/leanprover-community/mathlib/commit/d9dcf69)
feat(topology/topological_fiber_bundle): a new standard construction for topological fiber bundles ([#7935](https://github.com/leanprover-community/mathlib/pull/7935))
In this PR we implement a new standard construction for topological fiber bundles: namely a structure that permits to define a fiber bundle when trivializations are given as local equivalences but there is not yet a topology on the total space. The total space is hence given a topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations.
#### Estimated changes
Modified src/topology/continuous_on.lean
- \+ *lemma* preimage_nhds_within_coinduced'
- \+ *lemma* preimage_nhds_within_coinduced

Modified src/topology/topological_fiber_bundle.lean
- \+/\- *lemma* bundle_trivialization.apply_symm_apply'
- \+/\- *lemma* bundle_trivialization.apply_symm_apply
- \+/\- *lemma* bundle_trivialization.coe_coe
- \+/\- *lemma* bundle_trivialization.coe_fst'
- \+/\- *lemma* bundle_trivialization.coe_fst
- \+/\- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj'
- \+/\- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj
- \+/\- *lemma* bundle_trivialization.coe_mk
- \+/\- *def* bundle_trivialization.comp_homeomorph
- \+/\- *lemma* bundle_trivialization.continuous_at_proj
- \+/\- *lemma* bundle_trivialization.map_proj_nhds
- \+ *lemma* bundle_trivialization.map_target
- \+/\- *lemma* bundle_trivialization.mem_source
- \+/\- *lemma* bundle_trivialization.mem_target
- \+/\- *lemma* bundle_trivialization.mk_proj_snd'
- \+/\- *lemma* bundle_trivialization.mk_proj_snd
- \+/\- *lemma* bundle_trivialization.proj_symm_apply'
- \+/\- *lemma* bundle_trivialization.proj_symm_apply
- \+/\- *lemma* bundle_trivialization.symm_apply_mk_proj
- \+ *def* bundle_trivialization.to_prebundle_trivialization
- \+ *lemma* prebundle_trivialization.apply_symm_apply'
- \+ *lemma* prebundle_trivialization.apply_symm_apply
- \+ *lemma* prebundle_trivialization.coe_coe
- \+ *lemma* prebundle_trivialization.coe_fst'
- \+ *lemma* prebundle_trivialization.coe_fst
- \+ *lemma* prebundle_trivialization.mem_source
- \+ *lemma* prebundle_trivialization.mem_target
- \+ *lemma* prebundle_trivialization.mk_proj_snd'
- \+ *lemma* prebundle_trivialization.mk_proj_snd
- \+ *lemma* prebundle_trivialization.preimage_symm_proj_base_set
- \+ *lemma* prebundle_trivialization.preimage_symm_proj_inter
- \+ *lemma* prebundle_trivialization.proj_symm_apply'
- \+ *lemma* prebundle_trivialization.proj_symm_apply
- \+ *def* prebundle_trivialization.set_symm
- \+ *lemma* prebundle_trivialization.symm_apply_mk_proj
- \+ *structure* prebundle_trivialization
- \+ *def* topological_fiber_prebundle.bundle_trivialization_at
- \+ *lemma* topological_fiber_prebundle.continuous_proj
- \+ *lemma* topological_fiber_prebundle.continuous_symm_trivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_source_trivialization_at
- \+ *lemma* topological_fiber_prebundle.is_open_target_trivialization_at_inter
- \+ *lemma* topological_fiber_prebundle.is_topological_fiber_bundle
- \+ *def* topological_fiber_prebundle.total_space_topology
- \+ *structure* topological_fiber_prebundle



## [2021-06-24 08:13:45](https://github.com/leanprover-community/mathlib/commit/2f27046)
refactor(algebra/ordered_monoid): use `covariant + contravariant` typeclasses in `algebra/ordered_monoid` ([#7999](https://github.com/leanprover-community/mathlib/pull/7999))
Another stepping stone toward [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean


Modified src/algebra/ordered_monoid.lean
- \+/\- *lemma* one_le



## [2021-06-24 05:12:32](https://github.com/leanprover-community/mathlib/commit/5653516)
feat(data/fin): some lemmas about casts ([#8049](https://github.com/leanprover-community/mathlib/pull/8049))
From [LTE](https://github.com/leanprover-community/lean-liquid/blob/master/src/for_mathlib/fin.lean).
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_succ_eq_zero_iff
- \+ *lemma* fin.cast_succ_ne_zero_iff
- \+ *lemma* fin.cast_succ_pred_eq_pred_cast_succ
- \+ *lemma* fin.pred_succ_above_pred
- \+ *lemma* fin.succ_above_eq_zero_iff
- \+ *lemma* fin.succ_above_ne_zero
- \+ *lemma* fin.succ_above_ne_zero_zero



## [2021-06-24 04:33:52](https://github.com/leanprover-community/mathlib/commit/e07a24a)
chore(data/real/hyperreal): remove @ in a proof ([#8063](https://github.com/leanprover-community/mathlib/pull/8063))
Remove @ in a proof.  Besides its clear aesthetic value, this prevents having to touch this file when the number typeclass arguments in the intervening lemmas changes.
See PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) and [#8060](https://github.com/leanprover-community/mathlib/pull/8060).
#### Estimated changes
Modified src/data/real/hyperreal.lean




## [2021-06-23 23:28:11](https://github.com/leanprover-community/mathlib/commit/b9ef710)
chore(linear_algebra): deduplicate `linear_equiv.{Pi_congr_right,pi}` ([#8056](https://github.com/leanprover-community/mathlib/pull/8056))
PRs [#6415](https://github.com/leanprover-community/mathlib/pull/6415) and [#7489](https://github.com/leanprover-community/mathlib/pull/7489) both added the same linear equiv between Pi types. I propose to unify them, using the name of `Pi_congr_right` (more specific, matches `equiv.Pi_congr_right`), the location of `pi` (more specific) and the implementation of `Pi_congr_right` (shorter).
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \- *def* linear_equiv.Pi_congr_right
- \- *lemma* linear_equiv.Pi_congr_right_refl
- \- *lemma* linear_equiv.Pi_congr_right_symm
- \- *lemma* linear_equiv.Pi_congr_right_trans

Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.Pi_congr_right
- \+ *lemma* linear_equiv.Pi_congr_right_refl
- \+ *lemma* linear_equiv.Pi_congr_right_symm
- \+ *lemma* linear_equiv.Pi_congr_right_trans
- \- *def* linear_equiv.pi



## [2021-06-23 21:01:23](https://github.com/leanprover-community/mathlib/commit/3cf8039)
feat(measure_theory/set_integral): the set integral is continuous ([#7931](https://github.com/leanprover-community/mathlib/pull/7931))
Most of the code is dedicated to building a continuous linear map from Lp to the Lp space corresponding to the restriction of the measure to a set. The set integral is then continuous as composition of the integral and that map.
#### Estimated changes
Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.Lp_to_Lp_restrict_add
- \+ *def* measure_theory.Lp_to_Lp_restrict_clm
- \+ *lemma* measure_theory.Lp_to_Lp_restrict_clm_coe_fn
- \+ *lemma* measure_theory.Lp_to_Lp_restrict_smul
- \+ *lemma* measure_theory.continuous_set_integral
- \+ *lemma* measure_theory.norm_Lp_to_Lp_restrict_le



## [2021-06-23 19:27:20](https://github.com/leanprover-community/mathlib/commit/a31e3c3)
feat(category_theory/arrow/limit): limit cones in arrow categories ([#7457](https://github.com/leanprover-community/mathlib/pull/7457))
#### Estimated changes
Modified src/category_theory/arrow.lean




## [2021-06-23 17:29:28](https://github.com/leanprover-community/mathlib/commit/204ca5f)
docs(data/fin2): add module docstring ([#8047](https://github.com/leanprover-community/mathlib/pull/8047))
#### Estimated changes
Modified src/data/fin2.lean




## [2021-06-23 17:29:27](https://github.com/leanprover-community/mathlib/commit/89b8e0b)
docs(data/option/defs): add module and def docstrings ([#8042](https://github.com/leanprover-community/mathlib/pull/8042))
#### Estimated changes
Modified src/data/option/defs.lean




## [2021-06-23 17:29:26](https://github.com/leanprover-community/mathlib/commit/431207a)
docs(data/list/bag_inter): add module docstring ([#8034](https://github.com/leanprover-community/mathlib/pull/8034))
#### Estimated changes
Modified src/data/list/bag_inter.lean




## [2021-06-23 17:29:25](https://github.com/leanprover-community/mathlib/commit/dd5074c)
feat(analysis/normed_space/basic): add has_nnnorm ([#7986](https://github.com/leanprover-community/mathlib/pull/7986))
We create here classes `has_nndist` and `has_nnnorm` that are variants of `has_dist` and `has_norm` taking values in `ℝ≥0`.  Obvious instances are `pseudo_metric_space` and `semi_normed_group`.
These are not used that much in mathlib, but for example `has_nnnorm` is quite convenient for LTE.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* coe_nnnorm
- \+/\- *lemma* continuous.nnnorm
- \+/\- *lemma* continuous_at.nnnorm
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* continuous_on.nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* mem_emetric_ball_0_iff
- \+/\- *lemma* nndist_eq_nnnorm
- \+/\- *lemma* nndist_nnnorm_nnnorm_le
- \- *def* nnnorm
- \+/\- *lemma* nnnorm_add_le
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* nnnorm_gsmul_le
- \+/\- *lemma* nnnorm_neg
- \+/\- *lemma* nnnorm_norm
- \+/\- *lemma* nnnorm_nsmul_le
- \+/\- *lemma* nnnorm_one
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* nnnorm_zero
- \+/\- *lemma* nnreal.coe_nat_abs
- \+/\- *lemma* nnreal.nnnorm_eq
- \+/\- *lemma* normed_field.nnnorm_div
- \+/\- *lemma* normed_field.nnnorm_fpow
- \+/\- *lemma* normed_field.nnnorm_inv
- \+/\- *lemma* normed_field.nnnorm_mul
- \+/\- *lemma* normed_field.nnnorm_pow
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* prod.nnsemi_norm_def
- \+/\- *lemma* real.ennnorm_eq_of_real
- \+/\- *lemma* real.nnnorm_coe_nat
- \+/\- *lemma* real.nnnorm_of_nonneg
- \+/\- *lemma* real.nnnorm_two
- \+/\- *lemma* real.norm_two
- \+/\- *lemma* summable_of_summable_nnnorm
- \+/\- *lemma* uniform_continuous_nnnorm

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/metric_space/basic.lean
- \- *def* nndist



## [2021-06-23 15:53:39](https://github.com/leanprover-community/mathlib/commit/a7b5237)
feat(category_theory/arrow): arrow.iso_mk ([#8057](https://github.com/leanprover-community/mathlib/pull/8057))
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *def* category_theory.arrow.iso_mk



## [2021-06-23 15:53:38](https://github.com/leanprover-community/mathlib/commit/c841b09)
docs(data/list/tfae): add module docstring ([#8040](https://github.com/leanprover-community/mathlib/pull/8040))
#### Estimated changes
Modified src/data/list/tfae.lean




## [2021-06-23 15:53:37](https://github.com/leanprover-community/mathlib/commit/5787d64)
docs(data/list/zip): add module docstring ([#8036](https://github.com/leanprover-community/mathlib/pull/8036))
#### Estimated changes
Modified src/data/list/zip.lean




## [2021-06-23 14:11:52](https://github.com/leanprover-community/mathlib/commit/97529b4)
docs(data/list/forall2): add module docstring ([#8029](https://github.com/leanprover-community/mathlib/pull/8029))
#### Estimated changes
Modified src/data/list/forall2.lean
- \+/\- *lemma* list.forall₂.flip
- \+/\- *lemma* list.forall₂.mp
- \+/\- *lemma* list.forall₂_same
- \+/\- *lemma* list.right_unique_forall₂'



## [2021-06-23 11:50:23](https://github.com/leanprover-community/mathlib/commit/d9eed42)
feat(analysis/liouville/inequalities_and_series): two useful inequalities for Liouville ([#8001](https://github.com/leanprover-community/mathlib/pull/8001))
This PR ~~creates a file with~~ proves two very specific inequalities.  They will be useful for the Liouville PR, showing that transcendental Liouville numbers exist.
After the initial code review, I scattered an initial segment of this PR into mathlib.  What is left might only be useful in the context of proving the transcendence of Liouville's constants.
~~Given the shortness of this file, I may move it into the main `liouville_constant`, after PR [#8020](https://github.com/leanprover-community/mathlib/pull/8020)  is merged.~~
#### Estimated changes
Modified src/analysis/liouville/liouville_constant.lean
- \+ *lemma* liouville.aux_calc
- \+ *lemma* liouville.tsum_one_div_pow_factorial_lt



## [2021-06-23 09:25:09](https://github.com/leanprover-community/mathlib/commit/47ed97f)
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
#### Estimated changes
Modified src/algebra/big_operators/order.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_monoid_lemmas.lean
- \+ *def* contravariant.to_left_cancel_semigroup
- \+ *def* contravariant.to_right_cancel_semigroup
- \+/\- *lemma* le_mul_iff_one_le_left'
- \+/\- *lemma* le_mul_iff_one_le_right'
- \+ *lemma* le_mul_of_le_of_le_one
- \+/\- *lemma* le_mul_of_one_le_of_le
- \+/\- *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* le_of_mul_le_mul_left'
- \+/\- *lemma* le_of_mul_le_mul_right'
- \+ *lemma* left.mul_lt_one
- \+ *lemma* left.mul_lt_one_of_lt_of_lt_one
- \+/\- *lemma* lt_mul_iff_one_lt_left'
- \+/\- *lemma* lt_mul_iff_one_lt_right'
- \+/\- *lemma* lt_mul_of_le_of_one_lt
- \+/\- *lemma* lt_mul_of_lt_of_one_le
- \+/\- *lemma* lt_mul_of_lt_of_one_lt
- \- *lemma* lt_mul_of_one_le_of_lt'
- \+/\- *lemma* lt_mul_of_one_lt_left'
- \+/\- *lemma* lt_mul_of_one_lt_of_le
- \- *lemma* lt_mul_of_one_lt_of_lt'
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \+/\- *lemma* lt_of_mul_lt_mul_left'
- \+/\- *lemma* monotone.const_mul'
- \+/\- *lemma* monotone.mul'
- \+/\- *lemma* monotone.mul_const'
- \+/\- *lemma* monotone.mul_strict_mono'
- \- *lemma* mul_eq_one_iff_eq_one_of_one_le
- \+/\- *lemma* mul_le_iff_le_one_left'
- \+/\- *lemma* mul_le_iff_le_one_right'
- \+/\- *lemma* mul_le_mul_iff_left
- \+/\- *lemma* mul_le_mul_iff_right
- \+/\- *lemma* mul_le_mul_left'
- \+/\- *lemma* mul_le_mul_right'
- \+/\- *lemma* mul_le_mul_three
- \- *lemma* mul_le_of_le_of_le_one'
- \+/\- *lemma* mul_le_of_le_of_le_one
- \- *lemma* mul_le_of_le_one_of_le'
- \+/\- *lemma* mul_le_of_le_one_of_le
- \+/\- *lemma* mul_le_of_le_one_right'
- \- *lemma* mul_le_one'
- \+/\- *lemma* mul_lt_iff_lt_one_left'
- \+/\- *lemma* mul_lt_iff_lt_one_right'
- \+/\- *lemma* mul_lt_mul_iff_left
- \+/\- *lemma* mul_lt_mul_iff_right
- \+/\- *lemma* mul_lt_mul_left'
- \+/\- *lemma* mul_lt_mul_of_le_of_lt
- \+/\- *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* mul_lt_mul_of_lt_of_lt
- \+/\- *lemma* mul_lt_mul_right'
- \+/\- *lemma* mul_lt_of_le_of_lt_one
- \- *lemma* mul_lt_of_le_one_of_lt'
- \+/\- *lemma* mul_lt_of_le_one_of_lt
- \- *lemma* mul_lt_of_lt_of_le_one'
- \+/\- *lemma* mul_lt_of_lt_of_le_one
- \- *lemma* mul_lt_of_lt_of_lt_one'
- \+ *theorem* mul_lt_of_lt_of_lt_one
- \- *lemma* mul_lt_of_lt_of_lt_one
- \+/\- *lemma* mul_lt_of_lt_one_of_le
- \- *lemma* mul_lt_of_lt_one_of_lt'
- \+ *theorem* mul_lt_of_lt_one_of_lt
- \- *lemma* mul_lt_of_lt_one_of_lt
- \- *lemma* mul_lt_one'
- \- *lemma* mul_lt_one
- \- *lemma* mul_lt_one_of_le_one_of_lt_one'
- \- *lemma* mul_lt_one_of_le_one_of_lt_one
- \- *lemma* mul_lt_one_of_lt_one_of_le_one'
- \- *lemma* mul_lt_one_of_lt_one_of_le_one
- \+/\- *lemma* one_le_mul
- \+ *lemma* one_le_mul_right
- \+ *lemma* right.mul_lt_one
- \+ *lemma* right.mul_lt_one_of_lt_of_lt_one
- \+ *lemma* right.one_le_mul
- \+ *lemma* right.one_lt_mul

Modified src/algebra/quaternion.lean


Modified src/data/int/basic.lean


Modified src/data/nat/pow.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/tactic/linarith/verification.lean




## [2021-06-23 04:58:30](https://github.com/leanprover-community/mathlib/commit/168678e)
feat(analysis/liouville/liouville_constant): develop some API for Liouville ([#8005](https://github.com/leanprover-community/mathlib/pull/8005))
Proof of some inequalities for Liouville numbers.
#### Estimated changes
Modified src/analysis/liouville/liouville_constant.lean
- \+ *lemma* liouville.liouville_number_eq_initial_terms_add_tail
- \+ *lemma* liouville.liouville_number_tail_pos



## [2021-06-23 02:56:34](https://github.com/leanprover-community/mathlib/commit/ac2142c)
chore(scripts): update nolints.txt ([#8051](https://github.com/leanprover-community/mathlib/pull/8051))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-23 01:21:37](https://github.com/leanprover-community/mathlib/commit/0bc09d9)
feat(algebra/ordered_field): a few monotonicity results for powers ([#8022](https://github.com/leanprover-community/mathlib/pull/8022))
This PR proves the monotonicity (strict and non-strict) of `n → 1 / a ^ n`, for a fixed `a < 1` in a linearly ordered field.  These are lemmas extracted from PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001): I moved them to a separate PR after the discussion there.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* one_div_pow_le_one_div_pow_of_le
- \+ *lemma* one_div_pow_lt_one_div_pow_of_lt
- \+ *lemma* one_div_pow_mono
- \+ *lemma* one_div_pow_strict_mono
- \+ *lemma* one_div_strict_mono_decr_on



## [2021-06-22 22:06:38](https://github.com/leanprover-community/mathlib/commit/949e98e)
chore(topology/basic): add missing lemma ([#8048](https://github.com/leanprover-community/mathlib/pull/8048))
Adds `is_closed.sdiff`. From LTE.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* is_closed.sdiff



## [2021-06-22 20:35:50](https://github.com/leanprover-community/mathlib/commit/de4a4ce)
feat(ring_theory/adjoin/basic): lemmas relating adjoin and submodule.span ([#8031](https://github.com/leanprover-community/mathlib/pull/8031))
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.adjoin_eq_span_of_subset
- \+ *lemma* algebra.adjoin_to_submodule_le
- \+ *lemma* algebra.span_le_adjoin



## [2021-06-22 19:52:44](https://github.com/leanprover-community/mathlib/commit/c594196)
chore(topology/continuous_function/algebra): delete old instances, use bundled sub[monoid, group, ring]s ([#8004](https://github.com/leanprover-community/mathlib/pull/8004))
We remove the `monoid`, `group`, ... instances on `{ f : α → β | continuous f }` since `C(α, β)` should be used instead, and we replacce the `sub[monoid, group, ...]` instances on `{ f : α → β | continuous f }` by definitions of bundled subobjects with carrier `{ f : α → β | continuous f }`. We keep the `set_of` for subobjects since we need a subset to be the carrier.
Zulip : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/instances.20on.20continuous.20subtype
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \- *def* continuous.C
- \- *lemma* continuous_functions.coe_smul
- \+ *def* continuous_subalgebra
- \+ *def* continuous_subgroup
- \+ *def* continuous_submodule
- \+ *def* continuous_submonoid
- \+ *def* continuous_subring
- \+ *def* continuous_subsemiring



## [2021-06-22 16:26:58](https://github.com/leanprover-community/mathlib/commit/83bd2e6)
feat(analysis/normed_space/multilinear): add a few inequalities ([#8018](https://github.com/leanprover-community/mathlib/pull/8018))
Also add a few lemmas about `tsum` and `nnnorm`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_tsum_le
- \+ *lemma* tsum_of_nnnorm_bounded

Modified src/analysis/normed_space/multilinear.lean
- \+ *theorem* continuous_multilinear_map.le_of_op_nnnorm_le
- \+ *theorem* continuous_multilinear_map.le_op_nnnorm
- \+ *theorem* continuous_multilinear_map.le_op_norm_mul_pow_card_of_le
- \+ *theorem* continuous_multilinear_map.le_op_norm_mul_pow_of_le
- \+ *theorem* continuous_multilinear_map.le_op_norm_mul_prod_of_le
- \+ *lemma* continuous_multilinear_map.tsum_eval



## [2021-06-22 16:26:57](https://github.com/leanprover-community/mathlib/commit/9c4afb1)
feat(data/zmod): equivalence between the quotient type ℤ / aℤ and `zmod a` ([#7976](https://github.com/leanprover-community/mathlib/pull/7976))
This PR defines the equivalence between `zmod a` and ℤ / aℤ, where `a : ℕ` or `a : ℤ`, and the quotient is a quotient group or quotient ring.
It also defines `zmod.lift n f hf : zmod n →+ A` induced by an additive hom `f : ℤ →+ A` such that `f n = 0`. (The latter map could be, but is no longer, defined as the composition of the equivalence with `quotient.lift f`.)
Zulip threads:
 - [`(ideal.span {d}).quotient` is `zmod d`](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60.28ideal.2Espan.20.7Bd.7D.29.2Equotient.60.20is.20.60zmod.20d.60)
 - [Homomorphism from the integers descends to $$\mathbb{Z}/n$$](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Homomorphism.20from.20the.20integers.20descends.20to.20.24.24.5Cmathbb.7BZ.7D.2Fn.24.24)
 - [ `∈ gmultiples` iff divides](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60.E2.88.88.20gmultiples.60.20iff.20divides)
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.ker_int_cast_add_hom
- \+ *lemma* zmod.ker_int_cast_ring_hom
- \+ *def* zmod.lift
- \+ *lemma* zmod.lift_cast_add_hom
- \+ *lemma* zmod.lift_coe
- \+ *lemma* zmod.lift_comp_cast_add_hom
- \+ *lemma* zmod.lift_comp_coe

Added src/data/zmod/quotient.lean
- \+ *def* int.quotient_gmultiples_equiv_zmod
- \+ *def* int.quotient_gmultiples_nat_equiv_zmod
- \+ *def* int.quotient_span_equiv_zmod
- \+ *def* int.quotient_span_nat_equiv_zmod

Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.mem_gmultiples_iff
- \+ *lemma* int.mem_gmultiples_iff
- \+ *lemma* subgroup.mem_gpowers_iff

Modified src/ring_theory/ideal/basic.lean
- \+ *def* ideal.quot_equiv_of_eq

Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.gmultiples_nat_abs
- \+ *lemma* int.span_nat_abs



## [2021-06-22 14:51:33](https://github.com/leanprover-community/mathlib/commit/f477e03)
docs(data/list/erasedup): add module docstring ([#8030](https://github.com/leanprover-community/mathlib/pull/8030))
#### Estimated changes
Modified src/data/list/erase_dup.lean




## [2021-06-22 14:51:32](https://github.com/leanprover-community/mathlib/commit/7e20058)
feat(topology/Profinite/cofiltered_limit): Locally constant functions from cofiltered limits ([#7992](https://github.com/leanprover-community/mathlib/pull/7992))
This generalizes one of the main technical theorems from LTE about cofiltered limits of profinite sets.
This theorem should be useful for a future proof of Stone duality.
#### Estimated changes
Modified src/topology/category/Profinite/cofiltered_limit.lean
- \+ *theorem* Profinite.exists_locally_constant
- \+ *lemma* Profinite.exists_locally_constant_fin_two
- \+ *theorem* Profinite.exists_locally_constant_fintype_aux
- \+ *theorem* Profinite.exists_locally_constant_fintype_nonempty

Modified src/topology/discrete_quotient.lean
- \+ *def* locally_constant.discrete_quotient
- \+ *lemma* locally_constant.factors
- \+ *def* locally_constant.lift
- \+ *lemma* locally_constant.lift_eq_coe
- \+ *lemma* locally_constant.lift_is_locally_constant
- \+ *def* locally_constant.locally_constant_lift

Modified src/topology/locally_constant/basic.lean
- \+ *lemma* is_locally_constant.is_clopen_fiber
- \+ *lemma* is_locally_constant.is_closed_fiber



## [2021-06-22 13:52:01](https://github.com/leanprover-community/mathlib/commit/6e5de19)
feat(linear_algebra/free_module): add lemmas ([#7950](https://github.com/leanprover-community/mathlib/pull/7950))
Easy results about free modules.
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/module/projective.lean
- \+ *theorem* module.projective_of_basis
- \- *theorem* module.projective_of_free

Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/free_module.lean


Modified src/linear_algebra/std_basis.lean
- \+/\- *lemma* pi.linear_independent_std_basis



## [2021-06-22 12:45:40](https://github.com/leanprover-community/mathlib/commit/cb7b6cb)
docs(data/list/rotate): add module docstring ([#8027](https://github.com/leanprover-community/mathlib/pull/8027))
#### Estimated changes
Modified src/data/list/rotate.lean




## [2021-06-22 12:45:39](https://github.com/leanprover-community/mathlib/commit/94a8073)
feat(analysis/specific_limits): summability of `(λ i, 1 / m ^ f i)` ([#8023](https://github.com/leanprover-community/mathlib/pull/8023))
This PR shows the summability of the series whose `i`th term is `1 / m ^ f i`, where `1 < m` is a fixed real number and `f : ℕ → ℕ` is a function bounded below by the identity function.  While a function eventually bounded below by a constant at least equal to 2 would have been enough, this specific shape is convenient for the Liouville application.
I extracted this lemma, following the discussion in PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001).
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* summable_one_div_pow_of_le



## [2021-06-22 12:45:38](https://github.com/leanprover-community/mathlib/commit/a3699b9)
refactor(topology/sheaves/stalks): Refactor proofs about stalk map ([#8000](https://github.com/leanprover-community/mathlib/pull/8000))
Refactoring and speeding up some of my code on stalk maps from [#7092](https://github.com/leanprover-community/mathlib/pull/7092).
#### Estimated changes
Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.app_surjective_of_stalk_functor_map_bijective
- \+/\- *lemma* Top.presheaf.section_ext



## [2021-06-22 12:45:37](https://github.com/leanprover-community/mathlib/commit/208d4fe)
docs(data/pnat): add module docstrings ([#7960](https://github.com/leanprover-community/mathlib/pull/7960))
#### Estimated changes
Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean
- \- *def* pnat.xgcd:
- \+ *def* pnat.xgcd



## [2021-06-22 11:36:42](https://github.com/leanprover-community/mathlib/commit/4cbe7d6)
feat(group_theory/specific_groups/cyclic): A group is commutative if the quotient by the center is cyclic ([#7952](https://github.com/leanprover-community/mathlib/pull/7952))
#### Estimated changes
Modified src/group_theory/specific_groups/cyclic.lean
- \+ *def* comm_group_of_cycle_center_quotient
- \+ *lemma* commutative_of_cyclic_center_quotient



## [2021-06-22 11:36:40](https://github.com/leanprover-community/mathlib/commit/a1a0940)
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
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean




## [2021-06-22 11:36:40](https://github.com/leanprover-community/mathlib/commit/96f09a6)
feat(group_theory/perm/cycles): cycle_factors_finset ([#7540](https://github.com/leanprover-community/mathlib/pull/7540))
#### Estimated changes
Modified src/data/finset/noncomm_prod.lean
- \+ *lemma* finset.noncomm_prod_singleton

Modified src/group_theory/perm/cycle_type.lean
- \- *lemma* equiv.perm.list_cycles_perm_list_cycles
- \- *lemma* equiv.perm.mem_list_cycles_iff

Modified src/group_theory/perm/cycles.lean
- \+ *def* equiv.perm.cycle_factors_finset
- \+ *lemma* equiv.perm.cycle_factors_finset_eq_empty_iff
- \+ *lemma* equiv.perm.cycle_factors_finset_eq_finset
- \+ *lemma* equiv.perm.cycle_factors_finset_eq_list_to_finset
- \+ *lemma* equiv.perm.cycle_factors_finset_eq_singleton_iff
- \+ *lemma* equiv.perm.cycle_factors_finset_eq_singleton_self_iff
- \+ *lemma* equiv.perm.cycle_factors_finset_injective
- \+ *lemma* equiv.perm.cycle_factors_finset_mem_commute
- \+ *lemma* equiv.perm.cycle_factors_finset_noncomm_prod
- \+ *lemma* equiv.perm.cycle_factors_finset_pairwise_disjoint
- \+ *lemma* equiv.perm.is_cycle.eq_on_support_inter_nonempty_congr
- \+ *lemma* equiv.perm.is_cycle.support_congr
- \+ *lemma* equiv.perm.list_cycles_perm_list_cycles
- \+ *lemma* equiv.perm.mem_cycle_factors_finset_iff
- \+ *lemma* equiv.perm.mem_list_cycles_iff

Modified src/group_theory/perm/sign.lean


Modified src/group_theory/perm/support.lean
- \+ *lemma* equiv.perm.disjoint.commute
- \+ *lemma* equiv.perm.disjoint.mem_imp
- \- *lemma* equiv.perm.disjoint.mul_comm
- \+ *lemma* equiv.perm.disjoint.symmetric
- \+ *lemma* equiv.perm.eq_on_support_mem_disjoint
- \+ *lemma* equiv.perm.pow_eq_on_of_mem_support
- \+/\- *lemma* equiv.perm.support_congr
- \+ *lemma* equiv.perm.support_le_prod_of_mem

Modified src/group_theory/specific_groups/alternating.lean




## [2021-06-22 10:22:32](https://github.com/leanprover-community/mathlib/commit/9ca8597)
feat(linear_algebra/matrix/reindex): add some lemmas ([#7963](https://github.com/leanprover-community/mathlib/pull/7963))
From LTE
Added lemmas `reindex_linear_equiv_trans`, `reindex_linear_equiv_comp`, `reindex_linear_equiv_comp_apply`, `reindex_linear_equiv_one` and `mul_reindex_linear_equiv_mul_one` needed in LTE.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *def* matrix.minor
- \+/\- *lemma* matrix.minor_apply
- \+ *lemma* matrix.mul_minor_one
- \+ *lemma* matrix.one_minor_mul
- \+/\- *lemma* matrix.transpose_minor

Modified src/linear_algebra/matrix/reindex.lean
- \+ *lemma* matrix.mul_reindex_linear_equiv_one
- \+ *lemma* matrix.reindex_linear_equiv_comp
- \+ *lemma* matrix.reindex_linear_equiv_comp_apply
- \+/\- *lemma* matrix.reindex_linear_equiv_mul
- \+ *lemma* matrix.reindex_linear_equiv_one
- \+ *lemma* matrix.reindex_linear_equiv_trans



## [2021-06-22 08:42:23](https://github.com/leanprover-community/mathlib/commit/faaa0bc)
feat(algebra/ordered_field): `(1 - 1 / a)⁻¹ ≤ 2` ([#8021](https://github.com/leanprover-community/mathlib/pull/8021))
A lemma from the Liouville PR [#8001](https://github.com/leanprover-community/mathlib/pull/8001).  I extracted this lemma, after the discussion there.
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* sub_one_div_inv_le_two



## [2021-06-22 03:06:41](https://github.com/leanprover-community/mathlib/commit/3b4d1d8)
chore(scripts): update nolints.txt ([#8032](https://github.com/leanprover-community/mathlib/pull/8032))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-22 03:06:40](https://github.com/leanprover-community/mathlib/commit/6796bee)
chore(algebra/char_p/basic): generalize to non_assoc_semiring ([#7985](https://github.com/leanprover-community/mathlib/pull/7985))
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* char_p.congr
- \+/\- *theorem* char_p.exists
- \+/\- *theorem* char_p.exists_unique



## [2021-06-22 03:06:39](https://github.com/leanprover-community/mathlib/commit/4416eac)
feat(topology/instances/real): a continuous periodic function has compact range (and is hence bounded) ([#7968](https://github.com/leanprover-community/mathlib/pull/7968))
A few more facts about periodic functions, namely:
- If a function `f` is `periodic` with positive period `p`,
  then for all `x` there exists `y` such that `y` is an element of `[0, p)` and `f x = f y`
- A continuous, periodic function has compact range
- A continuous, periodic function is bounded
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* function.periodic.exists_mem_Ico

Modified src/data/set/basic.lean
- \+/\- *theorem* set.image_subset_range
- \+/\- *theorem* set.image_univ
- \+ *theorem* set.mem_range_of_mem_image
- \+/\- *theorem* set.range_subset_iff

Modified src/topology/instances/real.lean
- \+ *lemma* function.periodic.bounded_of_continuous
- \+ *lemma* function.periodic.compact_of_continuous'
- \+ *lemma* function.periodic.compact_of_continuous



## [2021-06-22 01:52:04](https://github.com/leanprover-community/mathlib/commit/e4b9561)
feat(linear_algebra/basic): weaken typeclasses ([#8028](https://github.com/leanprover-community/mathlib/pull/8028))
#### Estimated changes
Modified src/linear_algebra/basic.lean




## [2021-06-21 20:24:31](https://github.com/leanprover-community/mathlib/commit/80daef4)
chore(category_theory/limits): shorten some long lines ([#8007](https://github.com/leanprover-community/mathlib/pull/8007))
#### Estimated changes
Modified src/category_theory/limits/creates.lean




## [2021-06-21 19:43:14](https://github.com/leanprover-community/mathlib/commit/520bbe6)
feat(algebra/non_unital_alg_hom): define non_unital_alg_hom ([#7863](https://github.com/leanprover-community/mathlib/pull/7863))
The motivation is to be able to state the universal property for a magma algebra using bundled morphisms.
#### Estimated changes
Added src/algebra/non_unital_alg_hom.lean
- \+ *lemma* alg_hom.coe_to_non_unital_alg_hom
- \+ *def* alg_hom.to_non_unital_alg_hom
- \+ *lemma* alg_hom.to_non_unital_alg_hom_eq_coe
- \+ *lemma* non_unital_alg_hom.coe_comp
- \+ *lemma* non_unital_alg_hom.coe_distrib_mul_action_hom_mk
- \+ *lemma* non_unital_alg_hom.coe_injective
- \+ *lemma* non_unital_alg_hom.coe_inverse
- \+ *lemma* non_unital_alg_hom.coe_mk
- \+ *lemma* non_unital_alg_hom.coe_mul_hom_mk
- \+ *lemma* non_unital_alg_hom.coe_one
- \+ *lemma* non_unital_alg_hom.coe_to_distrib_mul_action_hom
- \+ *lemma* non_unital_alg_hom.coe_to_mul_hom
- \+ *lemma* non_unital_alg_hom.coe_zero
- \+ *def* non_unital_alg_hom.comp
- \+ *lemma* non_unital_alg_hom.comp_apply
- \+ *lemma* non_unital_alg_hom.ext
- \+ *lemma* non_unital_alg_hom.ext_iff
- \+ *def* non_unital_alg_hom.inverse
- \+ *lemma* non_unital_alg_hom.map_add
- \+ *lemma* non_unital_alg_hom.map_mul
- \+ *lemma* non_unital_alg_hom.map_smul
- \+ *lemma* non_unital_alg_hom.map_zero
- \+ *lemma* non_unital_alg_hom.mk_coe
- \+ *lemma* non_unital_alg_hom.one_apply
- \+ *lemma* non_unital_alg_hom.to_distrib_mul_action_hom_eq_coe
- \+ *lemma* non_unital_alg_hom.to_fun_eq_coe
- \+ *lemma* non_unital_alg_hom.to_mul_hom_eq_coe
- \+ *lemma* non_unital_alg_hom.zero_apply
- \+ *structure* non_unital_alg_hom



## [2021-06-21 19:43:13](https://github.com/leanprover-community/mathlib/commit/2b80d2f)
feat(geometry/euclidean/sphere): proof of Freek thm 95 - Ptolemy’s Theorem ([#7329](https://github.com/leanprover-community/mathlib/pull/7329))
#### Estimated changes
Modified docs/100.yaml


Modified src/geometry/euclidean/sphere.lean
- \+ *theorem* euclidean_geometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical



## [2021-06-21 19:03:52](https://github.com/leanprover-community/mathlib/commit/2fb0842)
perf(ci): use self-hosted runner for bors ([#8024](https://github.com/leanprover-community/mathlib/pull/8024))
Run CI builds for the `staging` branch used by bors on a self-hosted github actions runner.  This runner has been graciously provided by Johan Commelin's DFG grant and is hosted at the Albert-Ludwigs-Universität Freiburg.
We need to use two github actions workflow files to use a separate runner for the `staging` branch: `build.yml` and `bors.yml`.  These are almost identical, except for the `runs-on:` property indicating which runner should be used.  The shell script `mk_build_yml.sh` is therefore used to generate both files from the common template `build.yml.in`.
#### Estimated changes
Added .github/workflows/bors.yml


Modified .github/workflows/build.yml


Added .github/workflows/build.yml.in


Added .github/workflows/lint_self_test.yml


Added .github/workflows/mk_build_yml.sh




## [2021-06-21 14:25:31](https://github.com/leanprover-community/mathlib/commit/eb13f6b)
feat(ring_theory/derivation): add missing dsimp lemmas, use old_structure_command, golf structure proofs ([#8013](https://github.com/leanprover-community/mathlib/pull/8013))
This adds a pile of missing coercion lemmas proved by refl, and uses them to construct the `add_comm_monoid`, `add_comm_group`, and `module` instances.
This also changes `derivation` to be an old-style structure, which is more in line with the other bundled homomorphisms.
This also removes `derivation.commutator` to avoid having two ways to spell the same thing, as this leads to lemmas being harder to apply
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+/\- *lemma* derivation.Rsmul_apply
- \+/\- *lemma* derivation.add_apply
- \+ *lemma* derivation.coe_Rsmul
- \+ *lemma* derivation.coe_Rsmul_linear_map
- \+ *lemma* derivation.coe_add
- \+ *lemma* derivation.coe_add_linear_map
- \+ *def* derivation.coe_fn_add_monoid_hom
- \+/\- *lemma* derivation.coe_fn_coe
- \+/\- *lemma* derivation.coe_injective
- \+ *lemma* derivation.coe_neg
- \+ *lemma* derivation.coe_neg_linear_map
- \+ *lemma* derivation.coe_smul
- \+ *lemma* derivation.coe_smul_linear_map
- \+ *lemma* derivation.coe_sub
- \+ *lemma* derivation.coe_sub_linear_map
- \+ *lemma* derivation.coe_zero
- \+ *lemma* derivation.coe_zero_linear_map
- \- *def* derivation.commutator
- \+/\- *lemma* derivation.mk_coe
- \+ *lemma* derivation.neg_apply
- \+/\- *lemma* derivation.smul_apply
- \- *lemma* derivation.smul_to_linear_map_coe
- \+/\- *lemma* derivation.sub_apply
- \+ *lemma* derivation.to_linear_map_eq_coe
- \+ *lemma* derivation.zero_apply



## [2021-06-21 14:25:28](https://github.com/leanprover-community/mathlib/commit/92263c0)
refactor(algebraic_geometry/structure_sheaf): Enclose definitions in structure_sheaf namespace ([#8010](https://github.com/leanprover-community/mathlib/pull/8010))
Moves some pretty generic names like `const` and `to_open` to the `structure_sheaf` namespace.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/structure_sheaf.lean
- \- *def* algebraic_geometry.basic_open_iso
- \- *lemma* algebraic_geometry.coe_open_to_localization
- \- *def* algebraic_geometry.const
- \- *lemma* algebraic_geometry.const_add
- \- *lemma* algebraic_geometry.const_apply'
- \- *lemma* algebraic_geometry.const_apply
- \- *lemma* algebraic_geometry.const_congr
- \- *lemma* algebraic_geometry.const_ext
- \- *lemma* algebraic_geometry.const_mul
- \- *lemma* algebraic_geometry.const_mul_cancel'
- \- *lemma* algebraic_geometry.const_mul_cancel
- \- *lemma* algebraic_geometry.const_mul_rev
- \- *lemma* algebraic_geometry.const_one
- \- *lemma* algebraic_geometry.const_self
- \- *lemma* algebraic_geometry.const_zero
- \- *lemma* algebraic_geometry.exists_const
- \- *lemma* algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom
- \- *lemma* algebraic_geometry.germ_to_open
- \- *lemma* algebraic_geometry.germ_to_top
- \- *lemma* algebraic_geometry.is_unit_to_basic_open_self
- \- *lemma* algebraic_geometry.is_unit_to_stalk
- \- *lemma* algebraic_geometry.localization_to_basic_open
- \- *def* algebraic_geometry.localization_to_stalk
- \- *lemma* algebraic_geometry.localization_to_stalk_mk'
- \- *lemma* algebraic_geometry.localization_to_stalk_of
- \- *lemma* algebraic_geometry.locally_const_basic_open
- \- *lemma* algebraic_geometry.normalize_finite_fraction_representation
- \- *def* algebraic_geometry.open_to_localization
- \- *lemma* algebraic_geometry.open_to_localization_apply
- \- *lemma* algebraic_geometry.res_apply
- \- *lemma* algebraic_geometry.res_const'
- \- *lemma* algebraic_geometry.res_const
- \- *def* algebraic_geometry.stalk_iso
- \- *def* algebraic_geometry.stalk_to_fiber_ring_hom
- \- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ'
- \- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ
- \- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_to_stalk
- \+ *def* algebraic_geometry.structure_sheaf.basic_open_iso
- \+ *lemma* algebraic_geometry.structure_sheaf.coe_open_to_localization
- \+/\- *def* algebraic_geometry.structure_sheaf.comap
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_apply
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_comp
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_const
- \+/\- *def* algebraic_geometry.structure_sheaf.comap_fun
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_fun_is_locally_fraction
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_id'
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_id
- \+/\- *lemma* algebraic_geometry.structure_sheaf.comap_id_eq_map
- \+ *def* algebraic_geometry.structure_sheaf.const
- \+ *lemma* algebraic_geometry.structure_sheaf.const_add
- \+ *lemma* algebraic_geometry.structure_sheaf.const_apply'
- \+ *lemma* algebraic_geometry.structure_sheaf.const_apply
- \+ *lemma* algebraic_geometry.structure_sheaf.const_congr
- \+ *lemma* algebraic_geometry.structure_sheaf.const_ext
- \+ *lemma* algebraic_geometry.structure_sheaf.const_mul
- \+ *lemma* algebraic_geometry.structure_sheaf.const_mul_cancel'
- \+ *lemma* algebraic_geometry.structure_sheaf.const_mul_cancel
- \+ *lemma* algebraic_geometry.structure_sheaf.const_mul_rev
- \+ *lemma* algebraic_geometry.structure_sheaf.const_one
- \+ *lemma* algebraic_geometry.structure_sheaf.const_self
- \+ *lemma* algebraic_geometry.structure_sheaf.const_zero
- \+ *lemma* algebraic_geometry.structure_sheaf.exists_const
- \+ *lemma* algebraic_geometry.structure_sheaf.germ_comp_stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.structure_sheaf.germ_to_open
- \+ *lemma* algebraic_geometry.structure_sheaf.germ_to_top
- \+ *lemma* algebraic_geometry.structure_sheaf.is_unit_to_basic_open_self
- \+ *lemma* algebraic_geometry.structure_sheaf.is_unit_to_stalk
- \+ *lemma* algebraic_geometry.structure_sheaf.localization_to_basic_open
- \+ *def* algebraic_geometry.structure_sheaf.localization_to_stalk
- \+ *lemma* algebraic_geometry.structure_sheaf.localization_to_stalk_mk'
- \+ *lemma* algebraic_geometry.structure_sheaf.localization_to_stalk_of
- \+ *lemma* algebraic_geometry.structure_sheaf.locally_const_basic_open
- \+ *lemma* algebraic_geometry.structure_sheaf.normalize_finite_fraction_representation
- \+ *def* algebraic_geometry.structure_sheaf.open_to_localization
- \+ *lemma* algebraic_geometry.structure_sheaf.open_to_localization_apply
- \+ *lemma* algebraic_geometry.structure_sheaf.res_apply
- \+ *lemma* algebraic_geometry.structure_sheaf.res_const'
- \+ *lemma* algebraic_geometry.structure_sheaf.res_const
- \+ *def* algebraic_geometry.structure_sheaf.stalk_iso
- \+ *def* algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_germ'
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_germ
- \+ *lemma* algebraic_geometry.structure_sheaf.stalk_to_fiber_ring_hom_to_stalk
- \+ *def* algebraic_geometry.structure_sheaf.to_basic_open
- \+ *lemma* algebraic_geometry.structure_sheaf.to_basic_open_injective
- \+ *lemma* algebraic_geometry.structure_sheaf.to_basic_open_mk'
- \+ *lemma* algebraic_geometry.structure_sheaf.to_basic_open_surjective
- \+ *lemma* algebraic_geometry.structure_sheaf.to_basic_open_to_map
- \+ *def* algebraic_geometry.structure_sheaf.to_open
- \+ *lemma* algebraic_geometry.structure_sheaf.to_open_comp_comap
- \+ *lemma* algebraic_geometry.structure_sheaf.to_open_eq_const
- \+ *lemma* algebraic_geometry.structure_sheaf.to_open_germ
- \+ *lemma* algebraic_geometry.structure_sheaf.to_open_res
- \+ *def* algebraic_geometry.structure_sheaf.to_stalk
- \+ *lemma* algebraic_geometry.structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom
- \- *def* algebraic_geometry.to_basic_open
- \- *lemma* algebraic_geometry.to_basic_open_injective
- \- *lemma* algebraic_geometry.to_basic_open_mk'
- \- *lemma* algebraic_geometry.to_basic_open_surjective
- \- *lemma* algebraic_geometry.to_basic_open_to_map
- \- *def* algebraic_geometry.to_open
- \- *lemma* algebraic_geometry.to_open_comp_comap
- \- *lemma* algebraic_geometry.to_open_eq_const
- \- *lemma* algebraic_geometry.to_open_germ
- \- *lemma* algebraic_geometry.to_open_res
- \- *def* algebraic_geometry.to_stalk
- \- *lemma* algebraic_geometry.to_stalk_comp_stalk_to_fiber_ring_hom



## [2021-06-21 14:25:27](https://github.com/leanprover-community/mathlib/commit/5bc18a9)
feat(topology/category/limits): Generalize Topological Kőnig's lemma  ([#7982](https://github.com/leanprover-community/mathlib/pull/7982))
This PR generalizes the Topological Kőnig's lemma to work with limits over cofiltered categories (as opposed to just directed orders). Along the way, we also prove some more API for the category instance on `ulift C`, and provide an  `as_small C` construction for a category `C`. 
Coauthored with @kmill
#### Estimated changes
Modified src/category_theory/category/ulift.lean
- \+ *def* category_theory.as_small.down
- \+ *def* category_theory.as_small.equiv
- \+ *def* category_theory.as_small.up
- \+ *lemma* category_theory.obj_down_obj_up
- \+ *lemma* category_theory.obj_up_obj_down
- \+/\- *def* category_theory.ulift.down
- \+/\- *def* category_theory.ulift.equivalence
- \+/\- *def* category_theory.ulift.up
- \+ *def* category_theory.ulift_hom.down
- \+ *def* category_theory.ulift_hom.equiv
- \+ *def* category_theory.ulift_hom.obj_down
- \+ *def* category_theory.ulift_hom.obj_up
- \+ *def* category_theory.ulift_hom.up
- \+ *def* category_theory.{w

Modified src/category_theory/filtered.lean


Modified src/topology/category/Top/limits.lean
- \+ *lemma* Top.nonempty_limit_cone_of_compact_t2_cofiltered_system
- \- *lemma* Top.nonempty_limit_cone_of_compact_t2_inverse_system
- \+/\- *lemma* Top.partial_sections.closed
- \+/\- *lemma* Top.partial_sections.directed
- \+/\- *lemma* Top.partial_sections.nonempty
- \+/\- *def* Top.partial_sections
- \+ *lemma* nonempty_sections_of_fintype_cofiltered_system.init
- \+ *theorem* nonempty_sections_of_fintype_cofiltered_system
- \- *lemma* nonempty_sections_of_fintype_inverse_system.init
- \- *def* ulift.directed_order



## [2021-06-21 14:25:26](https://github.com/leanprover-community/mathlib/commit/9ce032c)
feat(data/matrix/basic): generalize to non_assoc_semiring ([#7974](https://github.com/leanprover-community/mathlib/pull/7974))
Matrices with whose coefficients form a non-unital and/or non-associative ring themselves form a non-unital and non-associative ring.
This isn't a full generalization of the file, the main aim was to generalize the typeclass instances available.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.sum_boole
- \+/\- *lemma* ring_hom.map_list_sum
- \+/\- *lemma* ring_hom.map_multiset_sum
- \+/\- *lemma* ring_hom.map_sum

Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.add_dot_product
- \+/\- *lemma* matrix.col_add
- \+/\- *lemma* matrix.col_smul
- \+/\- *lemma* matrix.diagonal_dot_product
- \+/\- *lemma* matrix.dot_product_add
- \+/\- *lemma* matrix.dot_product_assoc
- \+/\- *lemma* matrix.dot_product_diagonal'
- \+/\- *lemma* matrix.dot_product_diagonal
- \+/\- *lemma* matrix.dot_product_smul
- \+/\- *lemma* matrix.dot_product_zero'
- \+/\- *lemma* matrix.dot_product_zero
- \+/\- *lemma* matrix.map_mul
- \+/\- *lemma* matrix.row_add
- \+/\- *lemma* matrix.row_mul_col_apply
- \+/\- *lemma* matrix.row_smul
- \+/\- *lemma* matrix.smul_dot_product
- \+/\- *lemma* matrix.smul_mul_vec_assoc
- \+ *lemma* matrix.sum_apply
- \+/\- *def* matrix.vec_mul_vec
- \+/\- *lemma* matrix.zero_dot_product'
- \+/\- *lemma* matrix.zero_dot_product

Modified src/linear_algebra/char_poly/coeff.lean




## [2021-06-21 08:39:18](https://github.com/leanprover-community/mathlib/commit/3ef52f3)
chore(logic/basic): actually fixup `eq_or_ne` ([#8015](https://github.com/leanprover-community/mathlib/pull/8015))
this lemma loves being broken...
#### Estimated changes
Modified src/logic/basic.lean




## [2021-06-21 08:39:17](https://github.com/leanprover-community/mathlib/commit/abdc316)
feat(analysis/normed_space/normed_group_hom): add lemmas ([#7875](https://github.com/leanprover-community/mathlib/pull/7875))
From LTE.
#### Estimated changes
Modified src/analysis/normed_space/SemiNormedGroup.lean


Modified src/analysis/normed_space/normed_group_hom.lean
- \+ *lemma* normed_group_hom.coe_comp
- \+ *lemma* normed_group_hom.coe_id
- \+ *lemma* normed_group_hom.comp_assoc
- \+/\- *lemma* normed_group_hom.isometry_id
- \+ *lemma* normed_group_hom.norm_comp_le_of_le'
- \+ *lemma* normed_group_hom.norm_comp_le_of_le
- \+/\- *lemma* normed_group_hom.norm_id
- \+/\- *lemma* normed_group_hom.norm_id_le
- \+/\- *lemma* normed_group_hom.norm_noninc.id



## [2021-06-21 03:37:41](https://github.com/leanprover-community/mathlib/commit/c7d094d)
chore(scripts): update nolints.txt ([#8017](https://github.com/leanprover-community/mathlib/pull/8017))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-21 03:37:40](https://github.com/leanprover-community/mathlib/commit/3925fc0)
feat(analysis/liouville/liouville_constant.lean): create a file and introduce Liouville's constant ([#7996](https://github.com/leanprover-community/mathlib/pull/7996))
Introduce a new file and the definition of Liouville's number.  This is on the way to PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).
#### Estimated changes
Modified src/analysis/liouville/basic.lean


Added src/analysis/liouville/liouville_constant.lean
- \+ *def* liouville.liouville_number
- \+ *def* liouville.liouville_number_initial_terms
- \+ *def* liouville.liouville_number_tail



## [2021-06-21 03:37:39](https://github.com/leanprover-community/mathlib/commit/4d69b0f)
chore(topology/algebra/infinite_sum): small todo ([#7994](https://github.com/leanprover-community/mathlib/pull/7994))
Generalize a lemma from `f : ℕ → ℝ` to `f : β → α`, with 
```lean
[add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α] [decidable_eq β] 
```
This was marked as TODO after [#6017](https://github.com/leanprover-community/mathlib/pull/6017)/[#6096](https://github.com/leanprover-community/mathlib/pull/6096).
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_ite_eq_extract
- \+/\- *lemma* tsum_ite_eq_extract



## [2021-06-21 03:37:38](https://github.com/leanprover-community/mathlib/commit/5cdbb4c)
feat(algebra/*/pi, topology/continuous_function/algebra): homomorphism induced by left-composition ([#7984](https://github.com/leanprover-community/mathlib/pull/7984))
Given a monoid homomorphism from `α` to `β`, there is an induced monoid homomorphism from `I → α` to `I → β`, by left-composition.
Same result for semirings, modules, algebras.
Same result for topological monoids, topological semirings, etc, and the function spaces `C(I, α)`, `C(I, β)`, if the homomorphism is continuous.
Of these eight constructions, the only one I particularly want is the last one (topological algebras).  If reviewers feel it is better not to clog mathlib up with unused constructions, I am happy to cut the other seven from this PR.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/ring/pi.lean
- \+/\- *def* pi.eval_ring_hom

Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/pi.lean


Modified src/topology/continuous_function/algebra.lean




## [2021-06-21 03:37:37](https://github.com/leanprover-community/mathlib/commit/18c1c4a)
fix(tactic/linarith/preprocessing): capture result of zify_proof ([#7901](https://github.com/leanprover-community/mathlib/pull/7901))
this fixes the error encountered in the MWE in this Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/delayed_abstraction.20meta-variables/near/242376874
the `simplify` call inside of `zify_proof` does something bad to the tactic state when called in the scope of an `io.run_tactic`, not entirely sure why ¯\_(ツ)_/¯
#### Estimated changes
Modified src/tactic/linarith/preprocessing.lean




## [2021-06-20 21:36:12](https://github.com/leanprover-community/mathlib/commit/767901a)
feat(algebra/ordered_ring): `a + 1 ≤ 2 * a` ([#7995](https://github.com/leanprover-community/mathlib/pull/7995))
Prove one lemma, useful for the Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).  The placement of the lemma will change, once the `ordered` refactor will get to  `ordered_ring`.
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* add_one_le_two_mul



## [2021-06-20 17:21:15](https://github.com/leanprover-community/mathlib/commit/fae00c7)
chore(analysis/special_functions): move measurability statements to measure_theory folder ([#8006](https://github.com/leanprover-community/mathlib/pull/8006))
Make sure that measure theory is not imported in basic files defining trigonometric functions and real powers. The measurability of these functions is postponed to a new file `measure_theory.special_functions`.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \- *lemma* ae_measurable.inner
- \- *lemma* measurable.inner

Modified src/analysis/special_functions/exp_log.lean
- \- *lemma* complex.measurable_exp
- \- *lemma* complex.measurable_im
- \- *lemma* complex.measurable_of_real
- \- *lemma* complex.measurable_re
- \- *lemma* measurable.cexp
- \- *lemma* measurable.exp
- \- *lemma* measurable.log
- \- *lemma* real.measurable_exp
- \- *lemma* real.measurable_log

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/sqrt.lean
- \- *lemma* measurable.sqrt

Modified src/analysis/special_functions/trigonometric.lean
- \- *lemma* complex.measurable_arg
- \- *lemma* complex.measurable_cos
- \- *lemma* complex.measurable_cosh
- \- *lemma* complex.measurable_log
- \- *lemma* complex.measurable_sin
- \- *lemma* complex.measurable_sinh
- \- *lemma* measurable.arctan
- \- *lemma* measurable.carg
- \- *lemma* measurable.ccos
- \- *lemma* measurable.ccosh
- \- *lemma* measurable.clog
- \- *lemma* measurable.cos
- \- *lemma* measurable.cosh
- \- *lemma* measurable.csin
- \- *lemma* measurable.csinh
- \- *lemma* measurable.sin
- \- *lemma* measurable.sinh
- \- *lemma* real.measurable_arccos
- \- *lemma* real.measurable_arcsin
- \- *lemma* real.measurable_arctan
- \- *lemma* real.measurable_cos
- \- *lemma* real.measurable_cosh
- \- *lemma* real.measurable_sin
- \- *lemma* real.measurable_sinh

Modified src/measure_theory/mean_inequalities.lean


Added src/measure_theory/special_functions.lean
- \+ *lemma* ae_measurable.inner
- \+ *lemma* complex.measurable_arg
- \+ *lemma* complex.measurable_cos
- \+ *lemma* complex.measurable_cosh
- \+ *lemma* complex.measurable_exp
- \+ *lemma* complex.measurable_im
- \+ *lemma* complex.measurable_log
- \+ *lemma* complex.measurable_of_real
- \+ *lemma* complex.measurable_re
- \+ *lemma* complex.measurable_sin
- \+ *lemma* complex.measurable_sinh
- \+ *lemma* measurable.arctan
- \+ *lemma* measurable.carg
- \+ *lemma* measurable.ccos
- \+ *lemma* measurable.ccosh
- \+ *lemma* measurable.cexp
- \+ *lemma* measurable.clog
- \+ *lemma* measurable.cos
- \+ *lemma* measurable.cosh
- \+ *lemma* measurable.csin
- \+ *lemma* measurable.csinh
- \+ *lemma* measurable.exp
- \+ *lemma* measurable.inner
- \+ *lemma* measurable.log
- \+ *lemma* measurable.sin
- \+ *lemma* measurable.sinh
- \+ *lemma* measurable.sqrt
- \+ *lemma* real.measurable_arccos
- \+ *lemma* real.measurable_arcsin
- \+ *lemma* real.measurable_arctan
- \+ *lemma* real.measurable_cos
- \+ *lemma* real.measurable_cosh
- \+ *lemma* real.measurable_exp
- \+ *lemma* real.measurable_log
- \+ *lemma* real.measurable_sin
- \+ *lemma* real.measurable_sinh



## [2021-06-20 13:40:08](https://github.com/leanprover-community/mathlib/commit/547df12)
chore(analysis/liouville/liouville + data/real/liouville): create folder `analysis/liouville/`, move `data/real/liouville` into new folder ([#7998](https://github.com/leanprover-community/mathlib/pull/7998))
This PR simply creates a new folder `analysis/liouville` and moves `data/real/liouville` into the new folder.  In PR [#7996](https://github.com/leanprover-community/mathlib/pull/7996) I create a new Liouville-related file in the same folder.
#### Estimated changes
Renamed src/data/real/liouville.lean to src/analysis/liouville/basic.lean




## [2021-06-20 12:05:49](https://github.com/leanprover-community/mathlib/commit/3a0f282)
feat(measure_theory/interval_integral): integral of a non-integrable function ([#8011](https://github.com/leanprover-community/mathlib/pull/8011))
The `interval_integral` of a non-`interval_integrable` function is `0`.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_non_ae_measurable
- \+/\- *lemma* interval_integral.integral_non_ae_measurable_of_le
- \+ *lemma* interval_integral.integral_undef



## [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d155d9)
refactor(topology/metric_space/isometry): move material about isometries of normed spaces ([#8003](https://github.com/leanprover-community/mathlib/pull/8003))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/topology.20and.20analysis
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* add_monoid_hom.isometry_iff_norm
- \+ *lemma* add_monoid_hom.isometry_of_norm
- \+ *lemma* algebra_map_isometry
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
- \+ *lemma* uniform_space.completion.norm_coe

Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/topology/algebra/group_completion.lean


Deleted src/topology/algebra/normed_group.lean
- \- *lemma* uniform_space.completion.norm_coe

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/isometry.lean
- \- *lemma* add_monoid_hom.isometry_iff_norm
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* algebra_map_isometry
- \- *lemma* isometric.add_left_symm
- \- *lemma* isometric.add_left_to_equiv
- \- *lemma* isometric.add_right_apply
- \- *lemma* isometric.add_right_symm
- \- *lemma* isometric.add_right_to_equiv
- \- *lemma* isometric.coe_add_left
- \- *lemma* isometric.coe_add_right
- \- *lemma* isometric.coe_neg
- \- *lemma* isometric.neg_symm
- \- *lemma* isometric.neg_to_equiv



## [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d5b50a)
feat(algebra/homology/homotopy): flesh out the api a bit, add some simps ([#7941](https://github.com/leanprover-community/mathlib/pull/7941))
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* d_next_nat
- \+ *def* homotopy.comp
- \+ *def* homotopy.of_eq
- \+ *lemma* prev_d_nat



## [2021-06-19 18:19:08](https://github.com/leanprover-community/mathlib/commit/63c3ab5)
chore(data/int/basic): rationalize the arguments implicitness (mostly to_nat_sub_of_le) ([#7997](https://github.com/leanprover-community/mathlib/pull/7997))
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *lemma* int.coe_pred_of_pos
- \+/\- *theorem* int.mod_mod_of_dvd
- \+/\- *theorem* int.mul_div_mul_of_pos_left
- \+/\- *theorem* int.mul_mod_mul_of_pos
- \+/\- *theorem* int.of_nat_add_neg_succ_of_nat_of_lt
- \+/\- *lemma* int.sub_div_of_dvd
- \+/\- *lemma* int.to_nat_sub_of_le

Modified src/data/int/modeq.lean




## [2021-06-19 15:31:15](https://github.com/leanprover-community/mathlib/commit/cd8f7b5)
chore(topology/metric_space/pi_Lp): move to analysis folder, import inner_product_space ([#7991](https://github.com/leanprover-community/mathlib/pull/7991))
Currently, the file `pi_Lp` (on finite products of metric spaces, with the `L^p` norm) is in the topology folder, but it imports a lot of analysis (to have real powers) and it defines a normed space structure, so it makes more sense to have it in analysis. Also, it is currently imported by `inner_product_space`, to give an explicit construction of an inner product space on `pi_Lp 2`, which means that all files importing general purposes lemmas on inner product spaces also import real powers, trigonometry, and so on. We swap the imports, letting `pi_Lp` import `inner_product_space` and moving the relevant bits from the latter file to the former. This gives a more reasonable import graph.
#### Estimated changes
Modified src/analysis/normed_space/euclidean_dist.lean


Modified src/analysis/normed_space/inner_product.lean
- \- *def* basis.isometry_euclidean_of_orthonormal
- \- *def* complex.isometry_euclidean
- \- *lemma* complex.isometry_euclidean_apply_one
- \- *lemma* complex.isometry_euclidean_apply_zero
- \- *lemma* complex.isometry_euclidean_proj_eq_self
- \- *lemma* complex.isometry_euclidean_symm_apply
- \- *lemma* euclidean_space.norm_eq
- \- *def* euclidean_space
- \- *lemma* finrank_euclidean_space
- \- *lemma* finrank_euclidean_space_fin
- \- *def* linear_isometry_equiv.from_orthogonal_span_singleton
- \- *def* linear_isometry_equiv.of_inner_product_space
- \- *lemma* pi_Lp.inner_apply
- \- *lemma* pi_Lp.norm_eq_of_L2

Renamed src/topology/metric_space/pi_Lp.lean to src/analysis/normed_space/pi_Lp.lean
- \+ *def* basis.isometry_euclidean_of_orthonormal
- \+ *def* complex.isometry_euclidean
- \+ *lemma* complex.isometry_euclidean_apply_one
- \+ *lemma* complex.isometry_euclidean_apply_zero
- \+ *lemma* complex.isometry_euclidean_proj_eq_self
- \+ *lemma* complex.isometry_euclidean_symm_apply
- \+ *lemma* euclidean_space.norm_eq
- \+ *def* euclidean_space
- \+ *lemma* finrank_euclidean_space
- \+ *lemma* finrank_euclidean_space_fin
- \+ *def* linear_isometry_equiv.from_orthogonal_span_singleton
- \+ *def* linear_isometry_equiv.of_inner_product_space
- \+ *lemma* pi_Lp.inner_apply
- \+ *lemma* pi_Lp.norm_eq_of_L2

Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/instances/real.lean




## [2021-06-19 15:31:14](https://github.com/leanprover-community/mathlib/commit/497b84d)
chore(analysis/mean_inequalities): split integral mean inequalities to a new file ([#7990](https://github.com/leanprover-community/mathlib/pull/7990))
Currently, `normed_space.dual` imports a bunch of integration theory for no reason other than the file `mean_inequalities` contains both inequalities for finite sums and integrals. Splitting the file into two (and moving the integral versions to `measure_theory`) gives a more reasonable import graph.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \- *lemma* ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero
- \- *lemma* ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm
- \- *def* ennreal.fun_mul_inv_snorm
- \- *lemma* ennreal.fun_mul_inv_snorm_rpow
- \- *theorem* ennreal.lintegral_Lp_add_le
- \- *lemma* ennreal.lintegral_Lp_mul_le_Lq_mul_Lr
- \- *lemma* ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \- *theorem* ennreal.lintegral_mul_le_Lp_mul_Lq
- \- *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \- *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \- *lemma* ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \- *lemma* ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \- *lemma* ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
- \- *lemma* ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
- \- *lemma* ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one
- \- *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq

Modified src/measure_theory/lp_space.lean


Added src/measure_theory/mean_inequalities.lean
- \+ *lemma* ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm
- \+ *def* ennreal.fun_mul_inv_snorm
- \+ *lemma* ennreal.fun_mul_inv_snorm_rpow
- \+ *theorem* ennreal.lintegral_Lp_add_le
- \+ *lemma* ennreal.lintegral_Lp_mul_le_Lq_mul_Lr
- \+ *lemma* ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \+ *theorem* ennreal.lintegral_mul_le_Lp_mul_Lq
- \+ *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \+ *lemma* ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \+ *lemma* ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \+ *lemma* ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \+ *lemma* ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
- \+ *lemma* ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
- \+ *lemma* ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one
- \+ *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq



## [2021-06-19 15:31:13](https://github.com/leanprover-community/mathlib/commit/1846a1f)
feat(measure_theory/interval_integral): `abs_integral_le_integral_abs` ([#7959](https://github.com/leanprover-community/mathlib/pull/7959))
The absolute value of the integral of an integrable function is less than or equal to the integral of the absolute value that function.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integrable.abs
- \+/\- *lemma* interval_integrable.norm
- \+ *lemma* interval_integral.abs_integral_le_integral_abs
- \+ *lemma* interval_integral.integral_nonneg_of_forall
- \+ *lemma* interval_integral.norm_integral_le_integral_norm



## [2021-06-19 08:22:50](https://github.com/leanprover-community/mathlib/commit/2ca0452)
feat(data/{fin,nat,zmod}): prove `zmod.coe_add_eq_ite` ([#7975](https://github.com/leanprover-community/mathlib/pull/7975))
This PR adds a couple of lemmas relating addition modulo `n` (in `ℕ`, `fin n` or `zmod n`) and addition in `ℕ` or `ℤ`.
[Based on this Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Homomorphism.20from.20the.20integers.20descends.20to.20.24.24.5Cmathbb.7BZ.7D.2Fn.24.24)
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.coe_add_eq_ite

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_mod_eq_ite

Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.coe_add_eq_ite



## [2021-06-19 03:04:16](https://github.com/leanprover-community/mathlib/commit/28aee95)
chore(scripts): update nolints.txt ([#7993](https://github.com/leanprover-community/mathlib/pull/7993))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-19 03:04:15](https://github.com/leanprover-community/mathlib/commit/2a48c69)
feat(category_theory/yoneda): develop API for representable functors ([#7962](https://github.com/leanprover-community/mathlib/pull/7962))
Dualises and extends API for representable functors which was previously pretty minimal
#### Estimated changes
Modified src/category_theory/sites/canonical.lean
- \+/\- *lemma* category_theory.sheaf.is_sheaf_of_representable

Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/yoneda.lean
- \+ *lemma* category_theory.corepresentable_of_nat_iso
- \- *def* category_theory.coyoneda.iso_comp_punit
- \+ *def* category_theory.coyoneda.punit_iso
- \+ *lemma* category_theory.functor.corepr_w_app_hom
- \+ *lemma* category_theory.functor.repr_w_app_hom
- \+ *lemma* category_theory.functor.repr_w_hom
- \+ *lemma* category_theory.representable_of_nat_iso
- \+/\- *def* category_theory.yoneda_sections



## [2021-06-18 23:32:28](https://github.com/leanprover-community/mathlib/commit/42ab44c)
feat(group_theory): computable 1st isomorphism theorem ([#7988](https://github.com/leanprover-community/mathlib/pull/7988))
This PR defines a computable version of the first isomorphism theorem for groups and monoids that takes a right inverse of the map, `quotient_ker_equiv_of_right_inverse`.
#### Estimated changes
Modified src/group_theory/congruence.lean
- \+ *def* con.quotient_ker_equiv_of_right_inverse

Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_group.quotient_ker_equiv_of_right_inverse



## [2021-06-18 23:32:27](https://github.com/leanprover-community/mathlib/commit/3ee6248)
feat(measure_theory): links between an integral and its improper version ([#7164](https://github.com/leanprover-community/mathlib/pull/7164))
This PR introduces ways of studying and computing `∫ x, f x ∂μ` by studying the limit of the sequence `∫ x in φ n, f x ∂μ` for an appropriate sequence `φ` of subsets of the domain of `f`.
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+ *lemma* ae_measurable.indicator
- \+ *lemma* ae_measurable.restrict
- \+ *lemma* ae_measurable_indicator_iff
- \- *lemma* measure_theory.ae_measurable_indicator_iff

Added src/measure_theory/integral_eq_improper.lean
- \+ *lemma* measure_theory.ae_cover.ae_tendsto_indicator
- \+ *lemma* measure_theory.ae_cover.bInter_Ici_ae_cover
- \+ *lemma* measure_theory.ae_cover.bUnion_Iic_ae_cover
- \+ *lemma* measure_theory.ae_cover.comp_tendsto
- \+ *lemma* measure_theory.ae_cover.integrable_of_integral_norm_tendsto
- \+ *lemma* measure_theory.ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
- \+ *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_tendsto'
- \+ *lemma* measure_theory.ae_cover.integrable_of_lintegral_nnnorm_tendsto
- \+ *lemma* measure_theory.ae_cover.integral_eq_of_tendsto
- \+ *lemma* measure_theory.ae_cover.integral_eq_of_tendsto_of_nonneg_ae
- \+ *lemma* measure_theory.ae_cover.integral_tendsto_of_countably_generated
- \+ *lemma* measure_theory.ae_cover.inter_restrict
- \+ *lemma* measure_theory.ae_cover.lintegral_eq_of_tendsto
- \+ *lemma* measure_theory.ae_cover.lintegral_tendsto_of_countably_generated
- \+ *lemma* measure_theory.ae_cover.lintegral_tendsto_of_nat
- \+ *lemma* measure_theory.ae_cover.restrict
- \+ *lemma* measure_theory.ae_cover.supr_lintegral_eq_of_countably_generated
- \+ *structure* measure_theory.ae_cover
- \+ *lemma* measure_theory.ae_cover_Icc
- \+ *lemma* measure_theory.ae_cover_Ici
- \+ *lemma* measure_theory.ae_cover_Ico
- \+ *lemma* measure_theory.ae_cover_Iic
- \+ *lemma* measure_theory.ae_cover_Iio
- \+ *lemma* measure_theory.ae_cover_Ioc
- \+ *lemma* measure_theory.ae_cover_Ioi
- \+ *lemma* measure_theory.ae_cover_Ioo
- \+ *lemma* measure_theory.ae_cover_restrict_of_ae_imp
- \+ *lemma* measure_theory.integrable_of_interval_integral_norm_tendsto
- \+ *lemma* measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto
- \+ *lemma* measure_theory.integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+ *lemma* measure_theory.interval_integral_tendsto_integral
- \+ *lemma* measure_theory.interval_integral_tendsto_integral_Iic
- \+ *lemma* measure_theory.interval_integral_tendsto_integral_Ioi

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/set_integral.lean




## [2021-06-18 20:48:47](https://github.com/leanprover-community/mathlib/commit/f2f10cc)
docs(data/set/enumerate): add module and definition docstrings ([#7967](https://github.com/leanprover-community/mathlib/pull/7967))
#### Estimated changes
Modified src/data/set/enumerate.lean
- \+/\- *lemma* set.enumerate_eq_none
- \+/\- *lemma* set.enumerate_eq_none_of_sel
- \+/\- *lemma* set.enumerate_inj
- \+/\- *lemma* set.enumerate_mem



## [2021-06-18 20:48:46](https://github.com/leanprover-community/mathlib/commit/3a0653c)
feat(data/real/ennreal): add a `algebra ℝ≥0 ℝ≥0∞` instance ([#7846](https://github.com/leanprover-community/mathlib/pull/7846))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.smul_def

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.smul_def



## [2021-06-18 18:18:49](https://github.com/leanprover-community/mathlib/commit/52dbff0)
chore(topology/basic): rename compact_Icc to is_compact_Icc ([#7979](https://github.com/leanprover-community/mathlib/pull/7979))
Also rename `compact_interval` to `is_compact_interval`. And a bunch of random additions, all minor, as prerequisistes to [#7978](https://github.com/leanprover-community/mathlib/pull/7978)
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* bounded_iff_forall_norm_le
- \+ *lemma* is_compact.exists_bound_of_continuous_on

Modified src/analysis/normed_space/dual.lean
- \+ *lemma* normed_space.eq_iff_forall_dual_eq
- \+ *lemma* normed_space.eq_zero_iff_forall_dual_eq_zero

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *lemma* norm'_eq_zero_iff

Modified src/data/real/ereal.lean
- \+ *lemma* ereal.coe_to_real
- \+ *lemma* ereal.lt_iff_exists_real_btwn

Modified src/data/real/liouville.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integrable_on.lean
- \+ *lemma* continuous.integrable_on_Icc
- \+ *lemma* continuous.integrable_on_interval
- \- *lemma* continuous_linear_map.integrable_comp
- \+ *lemma* continuous_on.integrable_on_Icc
- \+ *lemma* continuous_on.integrable_on_interval
- \+ *lemma* measure_theory.integrable_on.continuous_on_mul
- \+ *lemma* measure_theory.integrable_on.mul_continuous_on
- \+ *lemma* measure_theory.integrable_on_singleton_iff

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* continuous_linear_map.integrable_comp

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.ae_restrict_iff'
- \+ *lemma* measure_theory.ae_restrict_mem

Modified src/topology/algebra/ordered/basic.lean
- \- *lemma* compact_Icc
- \- *lemma* compact_interval
- \- *lemma* compact_pi_Icc
- \+ *lemma* is_compact_Icc
- \+ *lemma* is_compact_interval
- \+ *lemma* is_compact_pi_Icc

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified test/monotonicity.lean




## [2021-06-18 15:33:01](https://github.com/leanprover-community/mathlib/commit/29e7a8d)
feat(topology/algebra/ordered, topology/algebra/infinite_sum): bounded monotone sequences converge (variant versions) ([#7983](https://github.com/leanprover-community/mathlib/pull/7983))
A bounded monotone sequence converges to a value `a`, if and only if `a` is a least upper bound for its range.
Mathlib had several variants of this fact previously (phrased in terms of, eg, `csupr`), but not quite this version (phrased in terms of `has_lub`).  This version has a couple of advantages:
- it applies to more general typeclasses (eg, `linear_order`) where the existence of suprema is not in general known
- it applies to algebraic typeclasses (`linear_ordered_add_comm_monoid`, etc) where, since completeness of orders is not a mix-in, it is not possible to simultaneously assume `(conditionally_)complete_linear_order`
The latter point makes these lemmas useful when dealing with `tsum`.  We get: a nonnegative function `f` satisfies `has_sum f a`, if and only if `a` is a least upper bound for its partial sums.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_le_of_sum_le
- \+ *lemma* has_sum_of_is_lub
- \+ *lemma* has_sum_of_is_lub_of_nonneg
- \+ *lemma* is_lub_has_sum'
- \+ *lemma* is_lub_has_sum
- \+ *lemma* le_has_sum_of_le_sum
- \+/\- *lemma* sum_le_has_sum
- \+ *lemma* tsum_le_of_sum_le'
- \+ *lemma* tsum_le_of_sum_le

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_glb_of_tendsto
- \+ *lemma* is_lub_of_tendsto
- \+ *lemma* monotone.ge_of_tendsto
- \+ *lemma* monotone.le_of_tendsto
- \+ *lemma* tendsto_at_bot_is_glb
- \+ *lemma* tendsto_at_top_is_lub



## [2021-06-18 13:40:11](https://github.com/leanprover-community/mathlib/commit/7c9a811)
feat(analysis/convex/basic): missing lemmas ([#7946](https://github.com/leanprover-community/mathlib/pull/7946))
- the union of a set/indexed family of convex sets is convex
- `open_segment a b` is convex
- a set is nonempty iff its convex hull is
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_Inter
- \+ *lemma* convex_hull_nonempty_iff
- \+ *lemma* convex_open_segment
- \+ *lemma* directed.convex_Union
- \+ *lemma* directed_on.convex_sUnion



## [2021-06-18 01:58:07](https://github.com/leanprover-community/mathlib/commit/e168bf7)
chore(scripts): update nolints.txt ([#7981](https://github.com/leanprover-community/mathlib/pull/7981))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-17 17:11:00](https://github.com/leanprover-community/mathlib/commit/49bf1fd)
chore(order/iterate): fix up the namespace ([#7977](https://github.com/leanprover-community/mathlib/pull/7977))
#### Estimated changes
Modified src/order/iterate.lean
- \- *lemma* function.commute.id_le_iterate_of_id_le
- \- *lemma* function.commute.iterate_le_id_of_le_id
- \- *lemma* function.commute.iterate_le_iterate_of_id_le
- \- *lemma* function.commute.iterate_le_iterate_of_le_id
- \+ *lemma* function.id_le_iterate_of_id_le
- \+ *lemma* function.iterate_le_id_of_le_id
- \+ *lemma* function.iterate_le_iterate_of_id_le
- \+ *lemma* function.iterate_le_iterate_of_le_id



## [2021-06-17 17:10:59](https://github.com/leanprover-community/mathlib/commit/dc73d1b)
docs(data/*/sqrt): add one module docstring and expand the other ([#7973](https://github.com/leanprover-community/mathlib/pull/7973))
#### Estimated changes
Modified src/data/int/sqrt.lean
- \+/\- *def* int.sqrt

Modified src/data/nat/sqrt.lean




## [2021-06-17 17:10:58](https://github.com/leanprover-community/mathlib/commit/3824a43)
docs(data/list/intervals): add module docstring ([#7972](https://github.com/leanprover-community/mathlib/pull/7972))
#### Estimated changes
Modified src/data/list/intervals.lean




## [2021-06-17 17:10:57](https://github.com/leanprover-community/mathlib/commit/93d7812)
docs(data/int/range): add module docstring ([#7971](https://github.com/leanprover-community/mathlib/pull/7971))
#### Estimated changes
Modified src/data/int/range.lean




## [2021-06-17 17:10:56](https://github.com/leanprover-community/mathlib/commit/da1a32c)
docs(data/int/cast): add module docstring ([#7969](https://github.com/leanprover-community/mathlib/pull/7969))
#### Estimated changes
Modified src/data/int/cast.lean




## [2021-06-17 17:10:50](https://github.com/leanprover-community/mathlib/commit/de6d739)
docs(data/nat/dist): add module docstring ([#7966](https://github.com/leanprover-community/mathlib/pull/7966))
#### Estimated changes
Modified src/data/nat/dist.lean




## [2021-06-17 17:10:49](https://github.com/leanprover-community/mathlib/commit/ce23f37)
feat(topology/locally_constant): Adds a few useful constructions ([#7954](https://github.com/leanprover-community/mathlib/pull/7954))
This PR adds a few useful constructions around locallly constant functions:
1. A locally constant function to `fin 2` associated to a clopen set.
2. Flipping a locally constant function taking values in a function type.
3. Unflipping a finite family of locally constant function.
4. Descending locally constant functions along an injective map.
#### Estimated changes
Modified src/topology/locally_constant/basic.lean
- \+ *lemma* is_locally_constant.desc
- \+ *lemma* locally_constant.coe_desc
- \+ *def* locally_constant.desc
- \+ *def* locally_constant.flip
- \+ *lemma* locally_constant.flip_unflip
- \+ *lemma* locally_constant.locally_constant_eq_of_fiber_zero_eq
- \+ *def* locally_constant.of_clopen
- \+ *lemma* locally_constant.of_clopen_fiber_one
- \+ *lemma* locally_constant.of_clopen_fiber_zero
- \+ *def* locally_constant.unflip
- \+ *lemma* locally_constant.unflip_flip



## [2021-06-17 17:10:48](https://github.com/leanprover-community/mathlib/commit/e9f9f3f)
docs(data/nat/cast): add module docstring ([#7947](https://github.com/leanprover-community/mathlib/pull/7947))
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/nat/cast.lean




## [2021-06-17 17:10:47](https://github.com/leanprover-community/mathlib/commit/9784396)
refactor(order/preorder_hom): golf and simp lemmas ([#7429](https://github.com/leanprover-community/mathlib/pull/7429))
The main change here is to adjust `simps` to generate coercion lemmas rather than `.to_fun` for `preorder_hom`, which allows us to auto-generate some simp lemmas.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean


Modified src/order/category/Preorder.lean


Modified src/order/omega_complete_partial_order.lean
- \+/\- *def* omega_complete_partial_order.chain.map

Modified src/order/preorder_hom.lean
- \- *lemma* order_embedding.to_preorder_hom_coe
- \+/\- *lemma* preorder_hom.coe_fun_mk
- \- *lemma* preorder_hom.coe_id
- \- *lemma* preorder_hom.coe_inj
- \+/\- *lemma* preorder_hom.ext
- \+ *lemma* preorder_hom.to_fun_eq_coe
- \- *lemma* rel_hom.to_preorder_hom_coe_fn

Modified src/topology/omega_complete_partial_order.lean




## [2021-06-17 11:31:07](https://github.com/leanprover-community/mathlib/commit/cbb8f01)
feat(algebra/group/basic): prove `a / 1 = a` and remove `sub_zero` ([#7956](https://github.com/leanprover-community/mathlib/pull/7956))
Add a proof that, in a group, `a / 1 = a`.  As a consequence, `sub_zero` is the `to_additive version of this lemma and I removed it.
The name of the lemma is `div_one'`, since the unprimed version is taken by `group_with_zero`.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60div_one'.60
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* div_one'
- \- *lemma* sub_zero



## [2021-06-17 11:31:06](https://github.com/leanprover-community/mathlib/commit/6578f1c)
feat(data/setoid/basic): add a computable version of quotient_ker_equiv_of_surjective ([#7930](https://github.com/leanprover-community/mathlib/pull/7930))
Perhaps more usefully, this also allows definitional control of the inverse mapping
#### Estimated changes
Modified src/data/setoid/basic.lean
- \+ *def* setoid.quotient_ker_equiv_of_right_inverse



## [2021-06-17 08:31:45](https://github.com/leanprover-community/mathlib/commit/1e43208)
refactor(ring_theory): use `x ∈ non_zero_divisors` over `x : non_zero_divisors` ([#7961](https://github.com/leanprover-community/mathlib/pull/7961))
`map_ne_zero_of_mem_non_zero_divisors` and `map_mem_non_zero_divisors` used to take `x : non_zero_divisors A` as an (implicit) argument. This is awkward if you only have `hx : x ∈ non_zero_divisors A`, requiring you to write out `@map_ne_zero_of_mem_non_zero_divisors _ _ _ _ _ _ hf ⟨x, hx⟩`. By making `x ∈ non_zero_divisors A` the explicit argument, we can avoid this annoyance.
See e.g. `ring_theory/polynomial/scale_roots.lean` for the improvement.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/non_zero_divisors.lean


Modified src/ring_theory/polynomial/scale_roots.lean




## [2021-06-17 02:48:11](https://github.com/leanprover-community/mathlib/commit/1a6c871)
chore(scripts): update nolints.txt ([#7965](https://github.com/leanprover-community/mathlib/pull/7965))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-17 00:23:25](https://github.com/leanprover-community/mathlib/commit/dc5d0c1)
feat(data/matrix): `has_repr` instances for `fin` vectors and matrices ([#7953](https://github.com/leanprover-community/mathlib/pull/7953))
This PR provides `has_repr` instances for the types `fin n → α` and `matrix (fin m) (fin n) α`, displaying in the `![...]` matrix notation. This is especially useful if you want to `#eval` a calculation involving matrices.
[Based on this Zulip post.](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Matrix.20operations/near/242766110)
#### Estimated changes
Modified src/data/matrix/notation.lean




## [2021-06-17 00:23:24](https://github.com/leanprover-community/mathlib/commit/641a9d3)
feat(model_theory/basic): Substructures ([#7762](https://github.com/leanprover-community/mathlib/pull/7762))
Defines substructures of first-order structures
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.closed_under.Inf
- \+ *lemma* first_order.language.closed_under.inf
- \+ *lemma* first_order.language.closed_under.inter
- \+ *def* first_order.language.closed_under
- \+ *lemma* first_order.language.embedding.map_const
- \+ *lemma* first_order.language.equiv.map_const
- \+ *lemma* first_order.language.fun_map_eq_coe_const
- \+ *def* first_order.language.hom.eq_locus
- \+ *lemma* first_order.language.hom.eq_of_eq_on_dense
- \+ *lemma* first_order.language.hom.eq_of_eq_on_top
- \+ *lemma* first_order.language.hom.eq_on_closure
- \+ *lemma* first_order.language.hom.map_const
- \+ *lemma* first_order.language.substructure.closed
- \+ *def* first_order.language.substructure.closure
- \+ *lemma* first_order.language.substructure.closure_Union
- \+ *lemma* first_order.language.substructure.closure_empty
- \+ *lemma* first_order.language.substructure.closure_eq
- \+ *lemma* first_order.language.substructure.closure_eq_of_le
- \+ *lemma* first_order.language.substructure.closure_induction
- \+ *lemma* first_order.language.substructure.closure_le
- \+ *lemma* first_order.language.substructure.closure_mono
- \+ *lemma* first_order.language.substructure.closure_union
- \+ *lemma* first_order.language.substructure.closure_univ
- \+ *lemma* first_order.language.substructure.coe_Inf
- \+ *lemma* first_order.language.substructure.coe_copy
- \+ *lemma* first_order.language.substructure.coe_inf
- \+ *lemma* first_order.language.substructure.coe_infi
- \+ *lemma* first_order.language.substructure.coe_top
- \+ *lemma* first_order.language.substructure.const_mem
- \+ *lemma* first_order.language.substructure.copy_eq
- \+ *lemma* first_order.language.substructure.dense_induction
- \+ *theorem* first_order.language.substructure.ext
- \+ *lemma* first_order.language.substructure.mem_Inf
- \+ *lemma* first_order.language.substructure.mem_carrier
- \+ *lemma* first_order.language.substructure.mem_closure
- \+ *lemma* first_order.language.substructure.mem_inf
- \+ *lemma* first_order.language.substructure.mem_infi
- \+ *lemma* first_order.language.substructure.mem_top
- \+ *def* first_order.language.substructure.simps.coe
- \+ *lemma* first_order.language.substructure.subset_closure
- \+ *structure* first_order.language.substructure



## [2021-06-16 18:44:26](https://github.com/leanprover-community/mathlib/commit/456a6d5)
docs(data/option/basic): add module docstring ([#7958](https://github.com/leanprover-community/mathlib/pull/7958))
#### Estimated changes
Modified src/data/option/basic.lean




## [2021-06-16 18:44:25](https://github.com/leanprover-community/mathlib/commit/08dfaab)
docs(data/set/disjointed): add module docstring and some whitespaces ([#7957](https://github.com/leanprover-community/mathlib/pull/7957))
#### Estimated changes
Modified src/data/set/disjointed.lean
- \+/\- *def* pairwise
- \+/\- *lemma* set.Inter_lt_succ
- \+/\- *lemma* set.Union_disjointed
- \+/\- *lemma* set.Union_disjointed_of_mono
- \+/\- *lemma* set.Union_lt_succ
- \+/\- *lemma* set.disjoint_disjointed'
- \+/\- *lemma* set.disjoint_disjointed
- \+/\- *def* set.disjointed
- \+/\- *lemma* set.disjointed_induct
- \+/\- *lemma* set.disjointed_of_mono
- \+/\- *lemma* set.disjointed_subset
- \+/\- *lemma* set.subset_Union_disjointed



## [2021-06-16 18:44:24](https://github.com/leanprover-community/mathlib/commit/49aa106)
docs(data/*/nat_antidiagonal): add one module docstring and harmonise others ([#7919](https://github.com/leanprover-community/mathlib/pull/7919))
#### Estimated changes
Modified src/data/finset/nat_antidiagonal.lean


Modified src/data/list/nat_antidiagonal.lean


Modified src/data/multiset/nat_antidiagonal.lean




## [2021-06-16 18:44:23](https://github.com/leanprover-community/mathlib/commit/366a449)
doc(topology/algebra/ring): add module docs + tidy ([#7893](https://github.com/leanprover-community/mathlib/pull/7893))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.quotient.quotient_ring_saturate

Modified src/topology/algebra/ring.lean
- \+/\- *lemma* ideal.coe_closure
- \- *lemma* quotient_ring_saturate



## [2021-06-16 15:31:34](https://github.com/leanprover-community/mathlib/commit/a564bf1)
feat(data/list/cycle): cycles as quotients of lists ([#7504](https://github.com/leanprover-community/mathlib/pull/7504))
Cycles are common structures, and we define them as a quotient of lists. This is on the route to defining concrete cyclic permutations, and could also be used for encoding properties of cycles in graphs.
#### Estimated changes
Added src/data/list/cycle.lean
- \+ *lemma* cycle.coe_eq_coe
- \+ *def* cycle.length
- \+ *lemma* cycle.length_coe
- \+ *lemma* cycle.length_nontrivial
- \+ *lemma* cycle.length_reverse
- \+ *lemma* cycle.length_subsingleton_iff
- \+ *def* cycle.mem
- \+ *lemma* cycle.mem_coe_iff
- \+ *lemma* cycle.mem_reverse_iff
- \+ *lemma* cycle.mk'_eq_coe
- \+ *lemma* cycle.mk_eq_coe
- \+ *def* cycle.next
- \+ *lemma* cycle.next_mem
- \+ *lemma* cycle.next_reverse_eq_prev
- \+ *def* cycle.nodup
- \+ *lemma* cycle.nodup_coe_iff
- \+ *lemma* cycle.nodup_reverse_iff
- \+ *def* cycle.nontrivial
- \+ *lemma* cycle.nontrivial_reverse_iff
- \+ *def* cycle.prev
- \+ *lemma* cycle.prev_mem
- \+ *lemma* cycle.prev_reverse_eq_next
- \+ *def* cycle.reverse
- \+ *lemma* cycle.reverse_coe
- \+ *lemma* cycle.reverse_reverse
- \+ *lemma* cycle.subsingleton.congr
- \+ *lemma* cycle.subsingleton.nodup
- \+ *def* cycle.subsingleton
- \+ *lemma* cycle.subsingleton_reverse_iff
- \+ *def* cycle.to_finset
- \+ *def* cycle.to_multiset
- \+ *def* cycle
- \+ *lemma* list.is_rotated_next_eq
- \+ *lemma* list.is_rotated_prev_eq
- \+ *lemma* list.mem_of_next_or_ne
- \+ *def* list.next
- \+ *lemma* list.next_cons_concat
- \+ *lemma* list.next_cons_cons_eq'
- \+ *lemma* list.next_cons_cons_eq
- \+ *lemma* list.next_last_cons
- \+ *lemma* list.next_mem
- \+ *lemma* list.next_ne_head_ne_last
- \+ *lemma* list.next_nth_le
- \+ *def* list.next_or
- \+ *lemma* list.next_or_concat
- \+ *lemma* list.next_or_cons_of_ne
- \+ *lemma* list.next_or_eq_next_or_of_mem_of_ne
- \+ *lemma* list.next_or_mem
- \+ *lemma* list.next_or_nil
- \+ *lemma* list.next_or_self_cons_cons
- \+ *lemma* list.next_or_singleton
- \+ *lemma* list.next_prev
- \+ *lemma* list.next_reverse_eq_prev
- \+ *lemma* list.next_singleton
- \+ *lemma* list.pmap_next_eq_rotate_one
- \+ *lemma* list.pmap_prev_eq_rotate_length_sub_one
- \+ *def* list.prev
- \+ *lemma* list.prev_cons_cons_eq'
- \+ *lemma* list.prev_cons_cons_eq
- \+ *lemma* list.prev_cons_cons_of_ne'
- \+ *lemma* list.prev_cons_cons_of_ne
- \+ *lemma* list.prev_last_cons'
- \+ *lemma* list.prev_last_cons
- \+ *lemma* list.prev_mem
- \+ *lemma* list.prev_ne_cons_cons
- \+ *lemma* list.prev_next
- \+ *lemma* list.prev_nth_le
- \+ *lemma* list.prev_reverse_eq_next
- \+ *lemma* list.prev_singleton

Modified src/data/list/rotate.lean
- \+ *lemma* list.nth_le_rotate'
- \+ *lemma* list.rotate_reverse



## [2021-06-16 12:25:45](https://github.com/leanprover-community/mathlib/commit/0490b43)
refactor(geometry/manifold/instances/circle): split out (topological) group facts ([#7951](https://github.com/leanprover-community/mathlib/pull/7951))
Move the group and topological group facts about the unit circle in `ℂ` from `geometry.manifold.instances.circle` to a new file `analysis.complex.circle`.  Delete `geometry.manifold.instances.circle`, moving the remaining material to a section in `geometry.manifold.instances.sphere`.
#### Estimated changes
Renamed src/geometry/manifold/instances/circle.lean to src/analysis/complex/circle.lean
- \- *lemma* times_cont_mdiff_exp_map_circle

Modified src/analysis/fourier.lean


Modified src/geometry/manifold/instances/sphere.lean
- \+ *lemma* times_cont_mdiff_exp_map_circle



## [2021-06-16 09:58:27](https://github.com/leanprover-community/mathlib/commit/95a116a)
chore(measure_theory/lp_space): simplify tendsto_Lp_iff_tendsto_\McLp by using tendsto_iff_dist_tendsto_zero ([#7942](https://github.com/leanprover-community/mathlib/pull/7942))
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.Lp.cauchy_seq_Lp_iff_cauchy_seq_ℒp
- \+ *lemma* measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp'
- \+ *lemma* measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp
- \+/\- *lemma* measure_theory.Lp.tendsto_Lp_of_tendsto_ℒp

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tendsto_to_real_iff



## [2021-06-16 06:02:08](https://github.com/leanprover-community/mathlib/commit/690ab17)
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
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* alg_equiv.comap
- \- *def* alg_hom.comap
- \- *def* algebra.comap.of_comap
- \- *def* algebra.comap.to_comap
- \- *def* algebra.comap
- \- *def* algebra.to_comap
- \- *theorem* algebra.to_comap_apply
- \+ *def* restrict_scalars.alg_equiv
- \+/\- *def* restrict_scalars.linear_equiv
- \+/\- *lemma* restrict_scalars.linear_equiv_map_smul
- \+/\- *def* restrict_scalars
- \+/\- *lemma* restrict_scalars_smul_def

Modified src/algebra/algebra/subalgebra.lean
- \- *def* subalgebra.comap

Modified src/algebra/algebra/tower.lean
- \- *theorem* is_scalar_tower.algebra_comap_eq
- \+ *def* subalgebra.restrict_scalars

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/noetherian.lean




## [2021-06-16 04:52:02](https://github.com/leanprover-community/mathlib/commit/b865892)
feat(algebraic_geometry/Spec): Make Spec a functor. ([#7790](https://github.com/leanprover-community/mathlib/pull/7790))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+/\- *def* algebraic_geometry.Scheme.Spec
- \+ *def* algebraic_geometry.Scheme.Spec_map
- \+ *lemma* algebraic_geometry.Scheme.Spec_map_comp
- \+ *lemma* algebraic_geometry.Scheme.Spec_map_id
- \+ *def* algebraic_geometry.Scheme.Spec_obj
- \+ *lemma* algebraic_geometry.Scheme.Spec_obj_to_LocallyRingedSpace

Modified src/algebraic_geometry/Spec.lean
- \- *def* algebraic_geometry.Spec.LocallyRingedSpace
- \+ *def* algebraic_geometry.Spec.LocallyRingedSpace_map
- \+ *lemma* algebraic_geometry.Spec.LocallyRingedSpace_map_comp
- \+ *lemma* algebraic_geometry.Spec.LocallyRingedSpace_map_id
- \+ *def* algebraic_geometry.Spec.LocallyRingedSpace_obj
- \- *def* algebraic_geometry.Spec.PresheafedSpace
- \- *def* algebraic_geometry.Spec.SheafedSpace
- \+ *def* algebraic_geometry.Spec.SheafedSpace_map
- \+ *lemma* algebraic_geometry.Spec.SheafedSpace_map_comp
- \+ *lemma* algebraic_geometry.Spec.SheafedSpace_map_id
- \+ *def* algebraic_geometry.Spec.SheafedSpace_obj
- \+ *def* algebraic_geometry.Spec.Top_map
- \+ *lemma* algebraic_geometry.Spec.Top_map_comp
- \+ *lemma* algebraic_geometry.Spec.Top_map_id
- \+ *def* algebraic_geometry.Spec.Top_obj
- \+ *def* algebraic_geometry.Spec.to_LocallyRingedSpace
- \+ *def* algebraic_geometry.Spec.to_PresheafedSpace
- \+ *lemma* algebraic_geometry.Spec.to_PresheafedSpace_map
- \+ *lemma* algebraic_geometry.Spec.to_PresheafedSpace_map_op
- \+ *lemma* algebraic_geometry.Spec.to_PresheafedSpace_obj
- \+ *lemma* algebraic_geometry.Spec.to_PresheafedSpace_obj_op
- \+ *def* algebraic_geometry.Spec.to_SheafedSpace
- \+ *def* algebraic_geometry.Spec.to_Top
- \+ *lemma* algebraic_geometry.local_ring_hom_comp_stalk_iso
- \+ *lemma* algebraic_geometry.stalk_map_to_stalk



## [2021-06-16 02:11:41](https://github.com/leanprover-community/mathlib/commit/ba3a4b7)
chore(scripts): update nolints.txt ([#7955](https://github.com/leanprover-community/mathlib/pull/7955))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-15 23:35:55](https://github.com/leanprover-community/mathlib/commit/30314c2)
fix(measure_theory/interval_integral): generalize some lemmas ([#7944](https://github.com/leanprover-community/mathlib/pull/7944))
The proofs of some lemmas about the integral of a function `f : ℝ → ℝ` also hold for `f : α → ℝ` (with `α` under the usual conditions).
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+/\- *lemma* integral_sin_pow_antimono

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_eq_zero_iff_of_le_of_nonneg_ae
- \+/\- *lemma* interval_integral.integral_eq_zero_iff_of_nonneg_ae
- \+/\- *lemma* interval_integral.integral_mono_ae_restrict
- \+/\- *lemma* interval_integral.integral_mono_on
- \+/\- *lemma* interval_integral.integral_nonneg
- \+/\- *lemma* interval_integral.integral_nonneg_of_ae
- \+/\- *lemma* interval_integral.integral_nonneg_of_ae_restrict
- \+/\- *lemma* interval_integral.integral_pos_iff_support_of_nonneg_ae'
- \+/\- *lemma* interval_integral.integral_pos_iff_support_of_nonneg_ae



## [2021-06-15 23:35:54](https://github.com/leanprover-community/mathlib/commit/45619c7)
feat(order/iterate): id_le lemmas ([#7943](https://github.com/leanprover-community/mathlib/pull/7943))
#### Estimated changes
Modified src/order/iterate.lean
- \+ *lemma* function.commute.id_le_iterate_of_id_le
- \+ *lemma* function.commute.iterate_le_id_of_le_id
- \+ *lemma* function.commute.iterate_le_iterate_of_id_le
- \+ *lemma* function.commute.iterate_le_iterate_of_le_id



## [2021-06-15 23:35:52](https://github.com/leanprover-community/mathlib/commit/e5c97e1)
feat(analysis/convex/basic): a linear map is convex and concave ([#7934](https://github.com/leanprover-community/mathlib/pull/7934))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* linear_map.concave_on
- \+ *lemma* linear_map.convex_on



## [2021-06-15 19:56:41](https://github.com/leanprover-community/mathlib/commit/f1f4c23)
feat(analysis/convex/basic): convex_on lemmas ([#7933](https://github.com/leanprover-community/mathlib/pull/7933))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.le_on_segment'
- \+ *lemma* concave_on.le_right_of_left_le'
- \+ *lemma* concave_on.le_right_of_left_le
- \+ *lemma* concave_on.left_le_of_le_right'
- \+ *lemma* concave_on.left_le_of_le_right
- \+ *lemma* convex_on.le_left_of_right_le'
- \+ *lemma* convex_on.le_left_of_right_le
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+ *lemma* convex_on.le_right_of_left_le'
- \+ *lemma* convex_on.le_right_of_left_le



## [2021-06-15 19:56:40](https://github.com/leanprover-community/mathlib/commit/5d03dcd)
feat(analysis/normed_space/dual): add eq_zero_of_forall_dual_eq_zero ([#7929](https://github.com/leanprover-community/mathlib/pull/7929))
The variable `𝕜` is made explicit in `norm_le_dual_bound` because lean can otherwise not guess it in the proof of `eq_zero_of_forall_dual_eq_zero`.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+ *lemma* normed_space.eq_zero_of_forall_dual_eq_zero



## [2021-06-15 19:56:39](https://github.com/leanprover-community/mathlib/commit/e5ff5fb)
feat(data/finsupp/basic): equiv_congr_left ([#7755](https://github.com/leanprover-community/mathlib/pull/7755))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Group.20cohomology/near/240737546).
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.equiv_congr_left
- \+ *lemma* finsupp.equiv_congr_left_apply
- \+ *lemma* finsupp.equiv_congr_left_symm
- \+ *def* finsupp.equiv_map_domain
- \+ *lemma* finsupp.equiv_map_domain_apply
- \+ *lemma* finsupp.equiv_map_domain_eq_map_domain
- \+ *lemma* finsupp.equiv_map_domain_refl'
- \+ *lemma* finsupp.equiv_map_domain_refl
- \+ *lemma* finsupp.equiv_map_domain_single
- \+ *lemma* finsupp.equiv_map_domain_symm_apply
- \+ *lemma* finsupp.equiv_map_domain_trans'
- \+ *lemma* finsupp.equiv_map_domain_trans
- \+ *lemma* finsupp.equiv_map_domain_zero

Modified src/linear_algebra/finsupp.lean




## [2021-06-15 14:54:47](https://github.com/leanprover-community/mathlib/commit/2f1f34a)
feat(measure_theory/lp_space): add `mem_Lp.mono_measure` ([#7927](https://github.com/leanprover-community/mathlib/pull/7927))
also add monotonicity lemmas wrt the measure for `snorm'`, `snorm_ess_sup` and `snorm`.
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.mono_measure
- \+ *lemma* measure_theory.mem_ℒp.restrict
- \+ *lemma* measure_theory.snorm'_mono_measure
- \+ *lemma* measure_theory.snorm_ess_sup_mono_measure
- \+ *lemma* measure_theory.snorm_mono_measure



## [2021-06-15 14:54:46](https://github.com/leanprover-community/mathlib/commit/5f8cc8e)
docs(undergrad): mark convex, convex hull, and extreme points as done ([#7924](https://github.com/leanprover-community/mathlib/pull/7924))
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-06-15 14:54:44](https://github.com/leanprover-community/mathlib/commit/e4ceee6)
feat(group_theory/order_of_element): Raising to a coprime power is a bijection ([#7923](https://github.com/leanprover-community/mathlib/pull/7923))
If `gcd(|G|,k)=1` then the `k`th power map is a bijection
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *def* pow_coprime
- \+ *lemma* pow_coprime_inv
- \+ *lemma* pow_coprime_one



## [2021-06-15 14:54:41](https://github.com/leanprover-community/mathlib/commit/f4991b9)
feat(measure_theory/bochner_integration): properties of simple functions (mem_Lp, integrable, fin_meas_supp) ([#7918](https://github.com/leanprover-community/mathlib/pull/7918))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.simple_func.exists_forall_norm_le
- \+ *lemma* measure_theory.simple_func.integrable_iff
- \+/\- *lemma* measure_theory.simple_func.integrable_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.integrable_of_finite_measure
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_integrable
- \+ *lemma* measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp
- \+ *lemma* measure_theory.simple_func.mem_ℒp_iff_integrable
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure
- \+ *lemma* measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage
- \+ *lemma* measure_theory.simple_func.mem_ℒp_top
- \+ *lemma* measure_theory.simple_func.mem_ℒp_zero

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp_top_of_bound
- \+ *lemma* measure_theory.snorm_ess_sup_le_of_ae_bound
- \+ *lemma* measure_theory.snorm_ess_sup_lt_top_of_ae_bound



## [2021-06-15 14:54:40](https://github.com/leanprover-community/mathlib/commit/b19c491)
chore(order/lattice): rename le_sup_left_of_le ([#7856](https://github.com/leanprover-community/mathlib/pull/7856))
rename `le_sup_left_of_le` to `le_sup_of_le_left`, and variants
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/order_functions.lean
- \- *lemma* le_max_left_of_le
- \+ *lemma* le_max_of_le_left
- \+ *lemma* le_max_of_le_right
- \- *lemma* le_max_right_of_le
- \- *lemma* min_le_left_of_le
- \+ *lemma* min_le_of_left_le
- \+ *lemma* min_le_of_right_le
- \- *lemma* min_le_right_of_le

Modified src/computability/partrec_code.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean


Modified src/linear_algebra/finsupp.lean


Modified src/measure_theory/interval_integral.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/order/bounds.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/lattice.lean
- \- *theorem* inf_le_left_of_le
- \+ *theorem* inf_le_of_left_le
- \+ *theorem* inf_le_of_right_le
- \- *theorem* inf_le_right_of_le
- \- *theorem* le_sup_left_of_le
- \+ *theorem* le_sup_of_le_left
- \+ *theorem* le_sup_of_le_right
- \- *theorem* le_sup_right_of_le

Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/perfection.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/subset_properties.lean




## [2021-06-15 14:54:39](https://github.com/leanprover-community/mathlib/commit/8e28104)
feat(algebra/algebra/basic): define `restrict_scalars.linear_equiv` ([#7807](https://github.com/leanprover-community/mathlib/pull/7807))
Also updating some doc-strings.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* restrict_scalars.linear_equiv
- \+ *lemma* restrict_scalars.linear_equiv_map_smul



## [2021-06-15 14:54:38](https://github.com/leanprover-community/mathlib/commit/a16650c)
feat(geometry/manifold/algebra/smooth_functions): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7749](https://github.com/leanprover-community/mathlib/pull/7749))
Changed names to be consistent with the topology library and proven that some coercions are morphisms.
#### Estimated changes
Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+/\- *def* smooth_map.C
- \+/\- *lemma* smooth_map.coe_div
- \+ *def* smooth_map.coe_fn_alg_hom
- \+ *def* smooth_map.coe_fn_linear_map
- \+ *def* smooth_map.coe_fn_monoid_hom
- \+ *def* smooth_map.coe_fn_ring_hom
- \+/\- *lemma* smooth_map.coe_inv
- \+/\- *lemma* smooth_map.coe_smul
- \+/\- *lemma* smooth_map.smul_comp'
- \+/\- *lemma* smooth_map.smul_comp



## [2021-06-15 06:03:53](https://github.com/leanprover-community/mathlib/commit/bf83c30)
chore(algebra/{ordered_monoid_lemmas, ordered_monoid}): move two sections close together ([#7921](https://github.com/leanprover-community/mathlib/pull/7921))
This PR aims at shortening the diff between `master` and PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) of the order refactor.
I moved the `mono` section of `algebra/ordered_monoid_lemmas` to the end of the file and appended the `strict_mono` section of `algebra/ordered_monoid` after that.
Note: the hypotheses are not optimal, but, with the current `instances` in this version, I did not know how to improve this.  It will get better by the time PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) is merged.  In fact, the next PR in the sequence, [#7876](https://github.com/leanprover-community/mathlib/pull/7876), already removes the unnecessary assumptions.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \- *lemma* monotone.mul_strict_mono'
- \- *lemma* strict_mono.const_mul'
- \- *lemma* strict_mono.mul_const'
- \- *lemma* strict_mono.mul_monotone'

Modified src/algebra/ordered_monoid_lemmas.lean
- \+ *lemma* monotone.mul_strict_mono'
- \+ *lemma* strict_mono.const_mul'
- \+ *lemma* strict_mono.mul_const'
- \+ *lemma* strict_mono.mul_monotone'



## [2021-06-15 06:03:52](https://github.com/leanprover-community/mathlib/commit/d74a898)
fix(meta/expr): fix mreplace ([#7912](https://github.com/leanprover-community/mathlib/pull/7912))
Previously the function would not recurse into macros (like `have`).
Also add warning to docstring.
#### Estimated changes
Modified src/meta/expr.lean




## [2021-06-15 03:22:09](https://github.com/leanprover-community/mathlib/commit/d960b2d)
chore(scripts): update nolints.txt ([#7939](https://github.com/leanprover-community/mathlib/pull/7939))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-15 03:22:08](https://github.com/leanprover-community/mathlib/commit/81f29f9)
chore(topology/metric_space): cleanup Gromov-Hausdorff files ([#7936](https://github.com/leanprover-community/mathlib/pull/7936))
Rename greek type variables to meaningful uppercase letters. Lint the files. Add a header where needed. Add spaces after forall or exist to conform to current style guide. Absolutely no new mathematical content.
#### Estimated changes
Modified src/topology/metric_space/gluing.lean
- \+/\- *def* metric.glue_dist
- \+/\- *lemma* metric.glue_dist_glued_points
- \+/\- *def* metric.glue_metric_approx
- \+/\- *def* metric.glue_premetric
- \+/\- *def* metric.inductive_limit
- \+/\- *def* metric.inductive_limit_dist
- \+/\- *lemma* metric.inductive_limit_dist_eq_dist
- \+/\- *def* metric.inductive_premetric
- \+/\- *lemma* metric.isometry_on_inl
- \+/\- *lemma* metric.isometry_on_inr
- \+/\- *def* metric.metric_space_sum
- \+/\- *def* metric.sum.dist
- \+/\- *lemma* metric.sum.dist_eq
- \+/\- *lemma* metric.sum.dist_eq_glue_dist
- \+/\- *lemma* metric.sum.one_dist_le'
- \+/\- *lemma* metric.sum.one_dist_le
- \+/\- *def* metric.to_glue_l
- \+/\- *def* metric.to_glue_r
- \+/\- *def* metric.to_inductive_limit
- \+/\- *lemma* metric.to_inductive_limit_commute
- \+/\- *lemma* metric.to_inductive_limit_isometry

Modified src/topology/metric_space/gromov_hausdorff.lean
- \+/\- *def* Gromov_Hausdorff.GH_dist
- \+/\- *theorem* Gromov_Hausdorff.GH_dist_eq_Hausdorff_dist
- \+/\- *theorem* Gromov_Hausdorff.GH_dist_le_Hausdorff_dist
- \+/\- *theorem* Gromov_Hausdorff.GH_dist_le_nonempty_compacts_dist
- \+/\- *theorem* Gromov_Hausdorff.GH_dist_le_of_approx_subsets
- \+/\- *lemma* Gromov_Hausdorff.Hausdorff_dist_optimal
- \+/\- *lemma* Gromov_Hausdorff.eq_to_GH_space_iff
- \+/\- *lemma* Gromov_Hausdorff.to_GH_space_eq_to_GH_space_iff_isometric

Modified src/topology/metric_space/gromov_hausdorff_realized.lean
- \+/\- *def* Gromov_Hausdorff.HD
- \+/\- *lemma* Gromov_Hausdorff.HD_below_aux1
- \+/\- *lemma* Gromov_Hausdorff.HD_below_aux2
- \+/\- *lemma* Gromov_Hausdorff.Hausdorff_dist_optimal_le_HD
- \+/\- *def* Gromov_Hausdorff.candidates
- \+/\- *def* Gromov_Hausdorff.candidates_b_dist
- \+/\- *lemma* Gromov_Hausdorff.candidates_b_dist_mem_candidates_b
- \+/\- *def* Gromov_Hausdorff.candidates_b_of_candidates
- \+/\- *lemma* Gromov_Hausdorff.candidates_b_of_candidates_mem
- \+/\- *lemma* Gromov_Hausdorff.isometry_optimal_GH_injl
- \+/\- *lemma* Gromov_Hausdorff.isometry_optimal_GH_injr
- \+/\- *def* Gromov_Hausdorff.optimal_GH_injl
- \+/\- *def* Gromov_Hausdorff.optimal_GH_injr
- \+/\- *def* Gromov_Hausdorff.premetric_optimal_GH_dist



## [2021-06-15 03:22:07](https://github.com/leanprover-community/mathlib/commit/a83f2c2)
feat(group_theory/order_of_element): Power of subset is subgroup ([#7915](https://github.com/leanprover-community/mathlib/pull/7915))
If `S` is a nonempty subset of `G`, then `S ^ |G|` is a subgroup of `G`.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *def* pow_card_subgroup
- \+ *def* subgroup_of_idempotent
- \+ *def* submonoid_of_idempotent

Modified src/group_theory/specific_groups/cyclic.lean




## [2021-06-15 03:22:06](https://github.com/leanprover-community/mathlib/commit/ba25bb8)
feat(measure_theory): define `measure.trim`, restriction of a measure to a sub-sigma algebra ([#7906](https://github.com/leanprover-community/mathlib/pull/7906))
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself is not a measure on `m`. For `hm : m ≤ m0`, we define the measure `μ.trim hm` on `m`.
We add lemmas relating a measure and its trimmed version, mostly about integrals of `m`-measurable functions.
#### Estimated changes
Modified src/measure_theory/arithmetic.lean
- \+ *lemma* measurable_set_eq_fun

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.ae_eq_trim_iff
- \+ *lemma* measure_theory.ae_eq_trim_of_measurable
- \+ *lemma* measure_theory.integral_simple_func_larger_space
- \+ *lemma* measure_theory.integral_trim
- \+ *lemma* measure_theory.integral_trim_ae
- \+ *lemma* measure_theory.integral_trim_simple_func
- \+ *lemma* measure_theory.simple_func.coe_to_larger_space_eq
- \+ *lemma* measure_theory.simple_func.integral_eq_sum
- \+ *def* measure_theory.simple_func.to_larger_space

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_trim
- \+ *lemma* measure_theory.lintegral_trim_ae

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.trim
- \+ *lemma* measure_theory.integrable_of_integrable_trim

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.ess_sup_trim
- \+ *lemma* measure_theory.limsup_trim
- \+ *lemma* measure_theory.snorm'_trim
- \+ *lemma* measure_theory.snorm_ess_sup_trim
- \+ *lemma* measure_theory.snorm_trim

Modified src/measure_theory/measure_space.lean
- \+ *lemma* ae_measurable_of_ae_measurable_trim
- \+ *lemma* measure_theory.ae_eq_of_ae_eq_trim
- \+ *lemma* measure_theory.le_trim
- \+ *def* measure_theory.measure.trim
- \+ *lemma* measure_theory.measure_eq_zero_of_trim_eq_zero
- \+ *lemma* measure_theory.measure_trim_to_measurable_eq_zero
- \+ *lemma* measure_theory.outer_measure.to_measure_zero
- \+ *lemma* measure_theory.restrict_trim
- \+ *lemma* measure_theory.to_outer_measure_trim_eq_trim_to_outer_measure
- \+ *lemma* measure_theory.trim_eq_self
- \+ *lemma* measure_theory.trim_measurable_set_eq
- \+ *lemma* measure_theory.zero_trim

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.set_integral_trim



## [2021-06-14 21:50:17](https://github.com/leanprover-community/mathlib/commit/8377a1f)
feat(measure_theory/lp_space): add snorm_le_snorm_mul_rpow_measure_univ ([#7926](https://github.com/leanprover-community/mathlib/pull/7926))
There were already versions of this lemma for `snorm'` and `snorm_ess_sup`. The new lemma collates these into a statement about `snorm`.
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.snorm_le_snorm_mul_rpow_measure_univ



## [2021-06-14 21:50:16](https://github.com/leanprover-community/mathlib/commit/e041dbe)
chore(algebra/covariant_and_contravariant): fix typos in module doc-strings ([#7925](https://github.com/leanprover-community/mathlib/pull/7925))
This PR changes slightly the doc-strings to make the autogenerated documentation more consistent.  I also removed some unstylish double spaces.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean




## [2021-06-14 21:50:15](https://github.com/leanprover-community/mathlib/commit/4a8ce41)
feat(analysis/special_functions/trigonometric): facts about periodic trigonometric functions  ([#7841](https://github.com/leanprover-community/mathlib/pull/7841))
I use the periodicity API that I added in [#7572](https://github.com/leanprover-community/mathlib/pull/7572) to write lemmas about sine (real and complex), cosine (real and complex), tangent (real and complex), and the  exponential function (complex only).
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.cos_add_int_mul_two_pi
- \+ *lemma* complex.cos_add_nat_mul_two_pi
- \+ *lemma* complex.cos_antiperiodic
- \+ *lemma* complex.cos_int_mul_two_pi_sub
- \+ *lemma* complex.cos_int_mul_two_pi_sub_pi
- \+ *lemma* complex.cos_nat_mul_two_pi_add_pi
- \+ *lemma* complex.cos_nat_mul_two_pi_sub
- \+ *lemma* complex.cos_nat_mul_two_pi_sub_pi
- \+ *lemma* complex.cos_periodic
- \+ *lemma* complex.cos_sub_int_mul_two_pi
- \+ *lemma* complex.cos_sub_nat_mul_two_pi
- \+ *lemma* complex.cos_sub_pi
- \+ *lemma* complex.cos_sub_two_pi
- \+ *lemma* complex.cos_two_pi_sub
- \+ *lemma* complex.exp_antiperiodic
- \+ *lemma* complex.exp_int_mul_two_pi_mul_I
- \+ *lemma* complex.exp_mul_I_antiperiodic
- \+ *lemma* complex.exp_mul_I_periodic
- \+ *lemma* complex.exp_nat_mul_two_pi_mul_I
- \+ *lemma* complex.exp_periodic
- \+ *lemma* complex.exp_two_pi_mul_I
- \+ *lemma* complex.sin_add_int_mul_two_pi
- \+ *lemma* complex.sin_add_nat_mul_two_pi
- \+ *lemma* complex.sin_antiperiodic
- \+ *lemma* complex.sin_int_mul_two_pi_sub
- \+ *lemma* complex.sin_nat_mul_two_pi_sub
- \+ *lemma* complex.sin_periodic
- \+ *lemma* complex.sin_sub_int_mul_two_pi
- \+ *lemma* complex.sin_sub_nat_mul_two_pi
- \+ *lemma* complex.sin_sub_pi
- \+ *lemma* complex.sin_sub_two_pi
- \+ *lemma* complex.sin_two_pi_sub
- \+ *lemma* complex.tan_add_int_mul_pi
- \+ *lemma* complex.tan_add_nat_mul_pi
- \+ *lemma* complex.tan_add_pi
- \+ *lemma* complex.tan_int_mul_pi_sub
- \+ *lemma* complex.tan_nat_mul_pi
- \+ *lemma* complex.tan_nat_mul_pi_sub
- \+ *lemma* complex.tan_periodic
- \+ *lemma* complex.tan_pi_sub
- \+ *lemma* complex.tan_sub_int_mul_pi
- \+ *lemma* complex.tan_sub_nat_mul_pi
- \+ *lemma* complex.tan_sub_pi
- \+ *lemma* real.cos_antiperiodic
- \+ *lemma* real.cos_int_mul_two_pi_sub
- \+ *lemma* real.cos_nat_mul_two_pi_sub
- \+ *lemma* real.cos_periodic
- \+ *lemma* real.cos_two_pi_sub
- \+ *lemma* real.sin_antiperiodic
- \+ *lemma* real.sin_int_mul_two_pi_sub
- \+ *lemma* real.sin_nat_mul_two_pi_sub
- \+ *lemma* real.sin_periodic
- \+ *lemma* real.sin_sub_pi
- \+ *lemma* real.sin_two_pi_sub
- \+ *lemma* real.tan_add_int_mul_pi
- \+ *lemma* real.tan_add_nat_mul_pi
- \+ *lemma* real.tan_add_pi
- \+ *lemma* real.tan_int_mul_pi_sub
- \+ *lemma* real.tan_nat_mul_pi
- \+ *lemma* real.tan_nat_mul_pi_sub
- \+ *lemma* real.tan_periodic
- \+ *lemma* real.tan_pi_sub
- \+ *lemma* real.tan_sub_int_mul_pi
- \+ *lemma* real.tan_sub_nat_mul_pi
- \+ *lemma* real.tan_sub_pi



## [2021-06-14 21:50:14](https://github.com/leanprover-community/mathlib/commit/fed7cf0)
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
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/induction.lean


Modified test/induction.lean
- \+ *inductive* inf_tree.all
- \+ *inductive* inf_tree
- \+ *def* topological_space_tests.generate_from
- \+ *inductive* topological_space_tests.generated_filter
- \+ *inductive* topological_space_tests.generated_open
- \+ *def* topological_space_tests.neighbourhood



## [2021-06-14 21:50:13](https://github.com/leanprover-community/mathlib/commit/f781c47)
feat(linear_algebra/determinant): specialize `linear_equiv.is_unit_det` to automorphisms ([#7667](https://github.com/leanprover-community/mathlib/pull/7667))
`linear_equiv.is_unit_det` is defined for all equivs between equal-dimensional spaces, using `det (linear_map.to_matrix _ _ _)`, but I needed this result for `linear_map.det _` (which only exists between the exact same space). So I added the specialization `linear_equiv.is_unit_det'`.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* linear_equiv.is_unit_det'
- \+ *lemma* linear_map.det_cases



## [2021-06-14 21:50:12](https://github.com/leanprover-community/mathlib/commit/615af75)
feat(measure_theory/interval_integral): `integral_deriv_comp_mul_deriv` ([#7141](https://github.com/leanprover-community/mathlib/pull/7141))
`∫ x in a..b, (g ∘ f) x * f' x`, where `f'` is derivative of `f` and `g` is the derivative of some function (the latter qualification allowing us to compute the integral directly by FTC-2)
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *theorem* interval_integral.integral_deriv_comp_mul_deriv'
- \+ *theorem* interval_integral.integral_deriv_comp_mul_deriv
- \+ *theorem* interval_integral.integral_deriv_mul_eq_sub
- \- *lemma* interval_integral.integral_deriv_mul_eq_sub

Modified test/integration.lean




## [2021-06-14 12:40:22](https://github.com/leanprover-community/mathlib/commit/386962c)
feat(algebra/char_zero): `neg_eq_self_iff` ([#7916](https://github.com/leanprover-community/mathlib/pull/7916))
`-a = a ↔ a = 0` and `a = -a ↔ a = 0`.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* eq_neg_self_iff
- \+ *lemma* neg_eq_self_iff



## [2021-06-14 07:23:15](https://github.com/leanprover-community/mathlib/commit/461b444)
docs(data/rat/denumerable): add module docstring ([#7920](https://github.com/leanprover-community/mathlib/pull/7920))
#### Estimated changes
Modified src/data/rat/denumerable.lean




## [2021-06-14 07:23:14](https://github.com/leanprover-community/mathlib/commit/a853a6a)
feat(analysis/normed_space): nnreal.coe_nat_abs ([#7911](https://github.com/leanprover-community/mathlib/pull/7911))
from LTE
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnreal.coe_nat_abs



## [2021-06-14 06:07:37](https://github.com/leanprover-community/mathlib/commit/6aed9a7)
feat(analysis/convex): add dual cone ([#7738](https://github.com/leanprover-community/mathlib/pull/7738))
Add definition of the dual cone of a set in a real inner product space
#### Estimated changes
Modified src/analysis/convex/cone.lean
- \+ *lemma* inner_dual_cone_empty
- \+ *lemma* inner_dual_cone_le_inner_dual_cone
- \+ *lemma* mem_inner_dual_cone
- \+ *lemma* pointed_inner_dual_cone



## [2021-06-14 03:56:10](https://github.com/leanprover-community/mathlib/commit/fec6c8a)
chore(scripts): update nolints.txt ([#7922](https://github.com/leanprover-community/mathlib/pull/7922))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-13 22:32:12](https://github.com/leanprover-community/mathlib/commit/3004513)
feat(measure_theory/ess_sup): monotonicity of ess_sup/ess_inf w.r.t. the measure ([#7917](https://github.com/leanprover-community/mathlib/pull/7917))
#### Estimated changes
Modified src/measure_theory/ess_sup.lean
- \+/\- *lemma* ennreal.ess_sup_const_mul
- \+/\- *lemma* ennreal.ess_sup_eq_zero_iff
- \+ *lemma* ess_inf_antimono_measure
- \+ *lemma* ess_sup_le_of_ae_le
- \+ *lemma* ess_sup_mono_measure
- \+ *lemma* le_ess_inf_of_ae_le

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.liminf_le_liminf_of_le
- \+ *lemma* filter.limsup_le_limsup_of_le



## [2021-06-13 22:32:11](https://github.com/leanprover-community/mathlib/commit/4fe7781)
chore(algebra/lie/basic + classical): golf some proofs ([#7903](https://github.com/leanprover-community/mathlib/pull/7903))
Another PR with some golfing, to get acquainted with the files!  Oliver, I really like how you set this up!
Also, feel free to say that you do not like the golfing: there is a subtle tension between proving stuff fast and making it accessible!
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/cartan_subalgebra.lean


Modified src/algebra/lie/classical.lean




## [2021-06-13 22:32:10](https://github.com/leanprover-community/mathlib/commit/b324488)
docs(set_theory/schroeder_bernstein): add module docstring ([#7900](https://github.com/leanprover-community/mathlib/pull/7900))
#### Estimated changes
Modified src/set_theory/schroeder_bernstein.lean




## [2021-06-13 22:32:09](https://github.com/leanprover-community/mathlib/commit/e971eae)
docs(data/nat/totient): add module docstring ([#7899](https://github.com/leanprover-community/mathlib/pull/7899))
#### Estimated changes
Modified src/data/nat/totient.lean




## [2021-06-13 22:32:08](https://github.com/leanprover-community/mathlib/commit/a359bd9)
chore(measure_theory): measurability statements for coercions, coherent naming ([#7854](https://github.com/leanprover-community/mathlib/pull/7854))
Also add a few lemmas on measure theory
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* max_zero_sub_max_neg_zero_eq_self

Modified src/analysis/mean_inequalities.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/real/nnreal.lean


Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_eq_integral_pos_part_sub_integral_neg_part

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.coe_ereal_ennreal
- \+ *lemma* ae_measurable.coe_nnreal_ennreal
- \+ *lemma* ae_measurable.coe_nnreal_real
- \+ *lemma* ae_measurable.coe_real_ereal
- \- *lemma* ae_measurable.ennreal_coe
- \+ *lemma* ae_measurable.ennreal_to_nnreal
- \+ *lemma* ae_measurable.ennreal_to_real
- \+ *lemma* ae_measurable.ereal_to_real
- \- *lemma* ae_measurable.nnreal_coe
- \- *lemma* ae_measurable.to_real
- \- *lemma* ennreal.measurable_coe
- \+ *lemma* ereal.measurable_of_measurable_real
- \+ *lemma* lower_semicontinuous.measurable
- \+ *lemma* measurable.coe_ereal_ennreal
- \+ *lemma* measurable.coe_nnreal_ennreal
- \+ *lemma* measurable.coe_nnreal_real
- \+ *lemma* measurable.coe_real_ereal
- \- *lemma* measurable.ennreal_coe
- \+ *lemma* measurable.ennreal_to_nnreal
- \+ *lemma* measurable.ennreal_to_real
- \+ *lemma* measurable.ereal_to_real
- \- *lemma* measurable.nnreal_coe
- \- *lemma* measurable.to_nnreal
- \- *lemma* measurable.to_real
- \+ *lemma* measurable_coe_ennreal_ereal
- \+ *lemma* measurable_coe_nnreal_ennreal
- \+ *lemma* measurable_coe_nnreal_ennreal_iff
- \+ *lemma* measurable_coe_nnreal_real
- \+ *lemma* measurable_coe_real_ereal
- \- *lemma* measurable_ennreal_coe_iff
- \+ *def* measurable_equiv.ereal_equiv_real
- \+ *lemma* measurable_ereal_to_real
- \+ *lemma* measurable_real_to_nnreal
- \- *lemma* nnreal.measurable_coe
- \+ *lemma* upper_semicontinuous.measurable

Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable.real_to_nnreal

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_of_fintype
- \+ *lemma* measurable_of_measurable_on_compl_finite

Modified src/measure_theory/prod.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* coe_nnreal_ennreal_nndist
- \- *lemma* ennreal_coe_nndist



## [2021-06-13 17:23:56](https://github.com/leanprover-community/mathlib/commit/5c11458)
chore(analysis/normed_space/normed_group_hom): golf proof of normed_group_hom.bounded ([#7896](https://github.com/leanprover-community/mathlib/pull/7896))
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean




## [2021-06-13 17:23:55](https://github.com/leanprover-community/mathlib/commit/2f40f35)
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
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Iic_inter_Ioc_of_le

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.forall_interval_oc_iff
- \+ *def* set.interval_oc
- \+ *lemma* set.interval_oc_of_le
- \+ *lemma* set.interval_oc_of_lt

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* ae_interval_oc_iff'
- \+ *lemma* ae_interval_oc_iff
- \+ *lemma* ae_measurable_interval_oc_iff
- \+ *lemma* interval_integrable.norm
- \+ *lemma* interval_integral.continuous_at_of_dominated_interval
- \+ *lemma* interval_integral.continuous_of_dominated_interval
- \+ *lemma* interval_integral.continuous_on_primitive''
- \+ *lemma* interval_integral.continuous_on_primitive'
- \+ *lemma* interval_integral.continuous_on_primitive
- \+ *lemma* interval_integral.continuous_primitive
- \+ *lemma* interval_integral.continuous_within_at_of_dominated_interval
- \+ *lemma* interval_integral.continuous_within_at_primitive
- \+ *lemma* interval_integral.integral_Icc_eq_integral_Ioc
- \+ *lemma* interval_integral.integral_congr_ae'
- \+ *lemma* interval_integral.integral_congr_ae
- \+ *lemma* interval_integral.integral_indicator
- \+ *lemma* interval_integral.integral_zero_ae
- \+ *lemma* measure_theory.integrable.continuous_primitive

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_singleton'
- \+ *lemma* measure_theory.measure.restrict_zero_set



## [2021-06-13 11:45:04](https://github.com/leanprover-community/mathlib/commit/6d2a051)
feat(algebra/covariant_and_contravariant): API for covariant_and_contravariant ([#7889](https://github.com/leanprover-community/mathlib/pull/7889))
This PR introduces more API for `covariant` and `contravariant` stuff .
Besides the API, I have not actually made further use of the typeclasses or of the API.  This happens in subsequent PRs.
This is a step towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* act_rel_act_of_rel
- \+ *lemma* act_rel_act_of_rel_of_rel
- \+ *lemma* act_rel_of_act_rel_of_rel_act_rel
- \+ *lemma* act_rel_of_rel_of_act_rel
- \+/\- *def* contravariant
- \+ *lemma* contravariant_flip_mul_iff
- \+ *lemma* contravariant_lt_of_contravariant_le
- \+ *lemma* covariant_flip_mul_iff
- \+ *lemma* covariant_le_iff_contravariant_lt
- \+ *lemma* covariant_le_of_covariant_lt
- \+ *lemma* covariant_lt_iff_contravariant_le
- \+ *lemma* covconv
- \+ *lemma* group.covariant_iff_contravariant
- \+ *lemma* rel_act_of_act_rel_act_of_rel_act
- \+ *lemma* rel_act_of_rel_of_rel_act
- \+ *lemma* rel_iff_cov
- \+ *lemma* rel_of_act_rel_act

Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_monoid_lemmas.lean




## [2021-06-13 06:04:53](https://github.com/leanprover-community/mathlib/commit/7c9643d)
chore(scripts): update nolints.txt ([#7914](https://github.com/leanprover-community/mathlib/pull/7914))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-13 06:04:52](https://github.com/leanprover-community/mathlib/commit/e13fd48)
docs(data/nat/pairing): add module docstring ([#7897](https://github.com/leanprover-community/mathlib/pull/7897))
#### Estimated changes
Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/data/equiv/list.lean


Modified src/data/nat/pairing.lean
- \- *theorem* nat.le_mkpair_left
- \- *theorem* nat.le_mkpair_right
- \+ *theorem* nat.left_le_mkpair
- \+ *theorem* nat.right_le_mkpair
- \- *theorem* nat.unpair_le_left
- \- *theorem* nat.unpair_le_right
- \+ *theorem* nat.unpair_left_le
- \+ *theorem* nat.unpair_right_le



## [2021-06-13 06:04:51](https://github.com/leanprover-community/mathlib/commit/2c919b0)
chore(algebra/{ordered_group, linear_ordered_comm_group_with_zero.lean}): rename one lemma, remove more @s ([#7895](https://github.com/leanprover-community/mathlib/pull/7895))
The more substantial part of this PR is changing the name of a lemma from `div_lt_div_iff'` to `mul_inv_lt_mul_inv_iff'`: the lemma proves `a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b`.
Furthermore, in the same spirit as a couple of my recent short PRs, I am removing a few more `@`, in order to sweep under the rug, later on, a change in typeclass assumptions.  This PR only changes a name, which was used only once, and a few proofs, but no statement.
On the path towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* div_le_div_iff'
- \+ *lemma* mul_inv_le_mul_inv_iff'



## [2021-06-13 06:04:50](https://github.com/leanprover-community/mathlib/commit/add577d)
feat(group_theory/group_action/defs): add `has_mul.to_has_scalar` and relax typeclass in `smul_mul_smul` ([#7885](https://github.com/leanprover-community/mathlib/pull/7885))
#### Estimated changes
Modified src/data/matrix/basic.lean


Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* mul_smul_comm
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* smul_mul_assoc
- \+/\- *lemma* smul_mul_smul



## [2021-06-12 23:46:04](https://github.com/leanprover-community/mathlib/commit/e0a3303)
chore(category_theory/filtered): Adds missing instances ([#7909](https://github.com/leanprover-community/mathlib/pull/7909))
#### Estimated changes
Modified src/category_theory/filtered.lean


Modified src/order/bounded_lattice.lean




## [2021-06-12 23:46:03](https://github.com/leanprover-community/mathlib/commit/9ad8ea3)
chore(linear_algebra/quadratic_form): fix typo ([#7907](https://github.com/leanprover-community/mathlib/pull/7907))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean




## [2021-06-12 23:46:02](https://github.com/leanprover-community/mathlib/commit/7b7cd0a)
fix(tactic/lint): punctuation of messages ([#7869](https://github.com/leanprover-community/mathlib/pull/7869))
Previously, the linter framework would append punctuation (`.` or `:`) to the message provided by the linter, but this was confusing and lead to some double punctuation. Now all linters specify their own punctuation.
#### Estimated changes
Modified src/tactic/lint/default.lean


Modified src/tactic/lint/frontend.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/lint/type_classes.lean


Modified test/lint.lean




## [2021-06-12 23:46:01](https://github.com/leanprover-community/mathlib/commit/39073fa)
feat(algebra/pointwise): Dynamics of powers of a subset ([#7836](https://github.com/leanprover-community/mathlib/pull/7836))
If `S` is a subset of a group `G`, then the powers of `S` eventually stabilize in size.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* group.card_pow_eq_card_pow_card_univ
- \+ *lemma* group.card_pow_eq_card_pow_card_univ_aux
- \+ *lemma* set.empty_pow



## [2021-06-12 15:55:02](https://github.com/leanprover-community/mathlib/commit/ee4fe74)
feat(topology/category/Profinite/cofiltered_clopen): Theorem about clopen sets in cofiltered limits of profinite sets ([#7837](https://github.com/leanprover-community/mathlib/pull/7837))
This PR proves the theorem that any clopen set in a cofiltered limit of profinite sets arises from a clopen set in one of the factors of the limit.
This generalizes a theorem used in LTE.
#### Estimated changes
Added src/topology/category/Profinite/cofiltered_limit.lean
- \+ *theorem* Profinite.exists_clopen_of_cofiltered



## [2021-06-12 15:55:00](https://github.com/leanprover-community/mathlib/commit/06094d5)
feat(linear_algebra/free_module): add class module.free ([#7801](https://github.com/leanprover-community/mathlib/pull/7801))
We introduce here a new class `module.free`.
#### Estimated changes
Added src/linear_algebra/free_module.lean
- \+ *def* module.free.choose_basis_index
- \+ *lemma* module.free.of_basis
- \+ *lemma* module.free.of_equiv'
- \+ *lemma* module.free.of_equiv
- \+ *lemma* module.free_def
- \+ *lemma* module.free_iff_set



## [2021-06-12 15:54:59](https://github.com/leanprover-community/mathlib/commit/f9935ed)
feat(geometry/manifold): Some lemmas for smooth functions ([#7752](https://github.com/leanprover-community/mathlib/pull/7752))
#### Estimated changes
Modified src/geometry/manifold/algebra/lie_group.lean


Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* L_apply
- \+ *lemma* L_mul
- \+ *lemma* R_apply
- \+ *lemma* R_mul
- \+ *def* smooth_left_mul
- \+ *def* smooth_right_mul

Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *lemma* smooth_map.mul_comp
- \+ *lemma* smooth_map.smul_comp'
- \+ *lemma* smooth_map.smul_comp



## [2021-06-12 11:10:11](https://github.com/leanprover-community/mathlib/commit/b7d4996)
chore(ring_theory/adjoin_root): speedup ([#7905](https://github.com/leanprover-community/mathlib/pull/7905))
Speedup a lemma that has just timed out in bors, by removing a heavy `change`.
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean




## [2021-06-12 11:10:10](https://github.com/leanprover-community/mathlib/commit/15b2434)
chore(data/nat/sqrt): Alternative phrasings of data.nat.sqrt lemmas ([#7748](https://github.com/leanprover-community/mathlib/pull/7748))
Add versions of the `data.nat.sqrt` lemmas to talk about `n^2` where the current versions talk about `n * n`.
#### Estimated changes
Modified src/data/nat/sqrt.lean
- \+ *theorem* nat.eq_sqrt'
- \+ *theorem* nat.exists_mul_self'
- \+ *theorem* nat.le_sqrt'
- \+ *theorem* nat.lt_succ_sqrt'
- \+ *theorem* nat.not_exists_sq'
- \+ *theorem* nat.sqrt_add_eq'
- \+ *theorem* nat.sqrt_eq'
- \+ *theorem* nat.sqrt_le'
- \+ *theorem* nat.sqrt_lt'
- \+ *theorem* nat.sqrt_mul_sqrt_lt_succ'
- \+ *theorem* nat.succ_le_succ_sqrt'



## [2021-06-12 11:10:09](https://github.com/leanprover-community/mathlib/commit/841dce1)
feat(data/polynomial): generalize `polynomial.has_scalar` to require only `distrib_mul_action` instead of `semimodule` ([#7664](https://github.com/leanprover-community/mathlib/pull/7664))
Note that by generalizing this instance, we introduce a diamond with `polynomial.mul_semiring_action`, which has a definitionally different `smul`. To resolve this, we add a proof that the definitions are equivalent, and switch `polynomial.mul_semiring_action` to use the same implementation as `polynomial.has_scalar`. This allows us to generalize `smul_C` to apply to all types of action, and remove `coeff_smul'` which then duplicates the statement of `coeff_smul`.
#### Estimated changes
Modified src/algebra/polynomial/group_ring_action.lean
- \- *lemma* polynomial.coeff_smul'
- \- *lemma* polynomial.smul_C
- \+ *lemma* polynomial.smul_eq_map

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.smul_C
- \+/\- *lemma* polynomial.smul_monomial
- \+/\- *lemma* polynomial.smul_to_finsupp

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* polynomial.coeff_smul
- \+/\- *lemma* polynomial.support_smul



## [2021-06-12 08:06:06](https://github.com/leanprover-community/mathlib/commit/2016a93)
feat(linear_algebra): use `finset`s to define `det` and `trace` ([#7778](https://github.com/leanprover-community/mathlib/pull/7778))
This PR replaces `∃ (s : set M) (b : basis s R M), s.finite` with `∃ (s : finset M), nonempty (basis s R M)` in the definitions in `linear_map.det` and `linear_map.trace`. This should make it much easier to unfold those definitions without having to modify the instance cache or supply implicit params.
In particular, it should help a lot with [#7667](https://github.com/leanprover-community/mathlib/pull/7667).
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *def* basis.reindex_finset_range
- \+ *lemma* basis.reindex_finset_range_apply
- \+ *lemma* basis.reindex_finset_range_repr
- \+ *lemma* basis.reindex_finset_range_repr_self
- \+ *lemma* basis.reindex_finset_range_self

Modified src/linear_algebra/determinant.lean
- \- *lemma* linear_map.det_eq_det_to_matrix_of_finite_set
- \+ *lemma* linear_map.det_eq_det_to_matrix_of_finset

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finrank_eq_zero_of_not_exists_basis_finset

Modified src/linear_algebra/trace.lean
- \- *theorem* linear_map.trace_aux_reindex_range
- \- *theorem* linear_map.trace_eq_matrix_trace_of_finite_set
- \+ *theorem* linear_map.trace_eq_matrix_trace_of_finset

Modified src/ring_theory/norm.lean


Modified src/ring_theory/trace.lean




## [2021-06-12 08:06:04](https://github.com/leanprover-community/mathlib/commit/dabb41f)
feat(tactic/{induction,fresh_names}): improve `induction' with` ([#7726](https://github.com/leanprover-community/mathlib/pull/7726))
This commit introduces two improvements to the `with` clauses of the `cases'`
and `induction'` tactics:
- Users can now write a hyphen instead of a name in the `with` clause. This
  clears the corresponding hypothesis (and any hypotheses depending on it).
- When users give an explicit name in the `with` clause, that name is now used
  verbatim, even if it shadows an existing hypothesis.
#### Estimated changes
Modified src/tactic/fresh_names.lean


Modified src/tactic/induction.lean


Modified test/fresh_names.lean


Modified test/induction.lean
- \+ *inductive* with_tests.test



## [2021-06-12 02:38:03](https://github.com/leanprover-community/mathlib/commit/55c9662)
chore(scripts): update nolints.txt ([#7902](https://github.com/leanprover-community/mathlib/pull/7902))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-12 02:38:02](https://github.com/leanprover-community/mathlib/commit/2974a9f)
feat(ring_theory): every division_ring is_noetherian ([#7661](https://github.com/leanprover-community/mathlib/pull/7661))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* ideal.bot_is_maximal
- \+/\- *lemma* ideal.eq_bot_of_prime
- \+/\- *lemma* ideal.eq_bot_or_top
- \+ *lemma* ideal.span_one
- \+/\- *lemma* ideal.span_singleton_one

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* principal_ideal_ring.is_maximal_of_irreducible



## [2021-06-12 02:38:01](https://github.com/leanprover-community/mathlib/commit/5948cde)
feat(ring_theory): the field trace resp. norm is the sum resp. product of the conjugates ([#7640](https://github.com/leanprover-community/mathlib/pull/7640))
More precise statement of the main result: the field trace (resp. norm) of `x` in `K(x) / K`, mapped to a field `F` that contains all the conjugate roots over `K` of `x`, is equal to the sum (resp. product) of all of these conjugate roots.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* intermediate_field.adjoin_simple.is_integral_gen

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.total_fin_zero

Modified src/ring_theory/norm.lean
- \+ *lemma* algebra.norm_gen_eq_prod_roots

Modified src/ring_theory/trace.lean
- \+ *lemma* algebra.trace_gen_eq_sum_roots



## [2021-06-12 02:38:00](https://github.com/leanprover-community/mathlib/commit/4337918)
feat(analysis/special_functions/integrals): integral of `sin x ^ m * cos x ^ n` ([#7418](https://github.com/leanprover-community/mathlib/pull/7418))
The simplification of integrals of the form `∫ x in a..b, sin x ^ m * cos x ^ n` where (i) `n` is odd, (ii) `m` is odd, and (iii) `m` and `n` are both even.
The computation of the integrals of the following functions are then provided outright:
- `sin x * cos x`, given both in terms of sine and cosine
- `sin x ^ 2 * cos x ^ 2`
- `sin x ^ 2 * cos x` and `sin x * cos x ^ 2`
- `sin x ^ 3` and `cos x ^ 3`
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos_pow_three
- \+ *lemma* integral_sin_mul_cos_sq
- \+ *lemma* integral_sin_mul_cos₁
- \+ *lemma* integral_sin_mul_cos₂
- \+ *lemma* integral_sin_pow_even_mul_cos_pow_even
- \+ *lemma* integral_sin_pow_mul_cos_pow_odd
- \+ *lemma* integral_sin_pow_odd_mul_cos_pow
- \+ *lemma* integral_sin_pow_three
- \+ *lemma* integral_sin_sq_mul_cos
- \+ *lemma* integral_sin_sq_mul_cos_sq

Modified test/integration.lean




## [2021-06-12 02:37:59](https://github.com/leanprover-community/mathlib/commit/2d175ae)
feat(topology/category/Top/limits): Kőnig's lemma for fintypes ([#6288](https://github.com/leanprover-community/mathlib/pull/6288))
Specializes `Top.nonempty_limit_cone_of_compact_t2_inverse_system` to an inverse system of nonempty fintypes.
#### Estimated changes
Modified src/topology/category/Top/limits.lean
- \+ *lemma* nonempty_sections_of_fintype_inverse_system.init
- \+ *theorem* nonempty_sections_of_fintype_inverse_system
- \+ *def* ulift.directed_order



## [2021-06-11 21:18:49](https://github.com/leanprover-community/mathlib/commit/b360611)
chore(src/algebra/lie/abelian): golf ([#7898](https://github.com/leanprover-community/mathlib/pull/7898))
I golfed some of the proofs of the file `algebra/lie/abelian`.  My main motivation was to get familiar with the file.
#### Estimated changes
Modified src/algebra/lie/abelian.lean




## [2021-06-11 21:18:48](https://github.com/leanprover-community/mathlib/commit/dd60035)
chore(algebra/{covariant_and_contravariant + ordered_monoid_lemmas}): new file covariant_and_contravariant ([#7890](https://github.com/leanprover-community/mathlib/pull/7890))
This PR creates a new file `algebra/covariant_and_contravariant` and moves the part of `algebra/ordered_monoid_lemmas` dealing exclusively with `covariant` and `contravariant` into it.
It also rearranges the documentation, with a view to the later PRs, building up to [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
The discrepancy between the added and removed lines is entirely due to longer documentation: no actual Lean code has changed, except, of course, for the `import` in `algebra/ordered_monoid_lemmas` that now uses `covariant_and_contravariant`.
#### Estimated changes
Added src/algebra/covariant_and_contravariant.lean
- \+ *def* contravariant
- \+ *def* covariant

Modified src/algebra/ordered_monoid_lemmas.lean
- \- *def* contravariant
- \- *def* covariant



## [2021-06-11 21:18:47](https://github.com/leanprover-community/mathlib/commit/538f015)
feat(data/finset/basic): `empty_product` and `product_empty` ([#7886](https://github.com/leanprover-community/mathlib/pull/7886))
add `product_empty_<left/right>`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.empty_product
- \+ *lemma* finset.product_empty



## [2021-06-11 21:18:46](https://github.com/leanprover-community/mathlib/commit/97a7a24)
doc(data/pequiv): add module docs ([#7877](https://github.com/leanprover-community/mathlib/pull/7877))
#### Estimated changes
Modified src/data/pequiv.lean




## [2021-06-11 21:18:45](https://github.com/leanprover-community/mathlib/commit/ff44ed5)
feat({algebra/group_action_hom, data/equiv/mul_add}): add missing `inverse` defs ([#7847](https://github.com/leanprover-community/mathlib/pull/7847))
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *lemma* distrib_mul_action_hom.coe_one
- \+ *lemma* distrib_mul_action_hom.coe_zero
- \+ *def* distrib_mul_action_hom.inverse
- \+ *lemma* distrib_mul_action_hom.one_apply
- \+ *lemma* distrib_mul_action_hom.to_fun_eq_coe
- \+ *lemma* distrib_mul_action_hom.zero_apply
- \+ *def* mul_action_hom.inverse

Modified src/data/equiv/mul_add.lean
- \+ *def* monoid_hom.inverse



## [2021-06-11 21:18:44](https://github.com/leanprover-community/mathlib/commit/a008b33)
feat(data/finsupp/to_dfinsupp): add sigma_finsupp_lequiv_dfinsupp ([#7818](https://github.com/leanprover-community/mathlib/pull/7818))
Equivalences between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`.
- [x] depends on: [#7819](https://github.com/leanprover-community/mathlib/pull/7819)
#### Estimated changes
Modified src/data/finsupp/to_dfinsupp.lean
- \+ *def* sigma_finsupp_add_equiv_dfinsupp
- \+ *def* sigma_finsupp_equiv_dfinsupp
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_add
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_apply
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_smul
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_support
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_symm_apply
- \+ *def* sigma_finsupp_lequiv_dfinsupp



## [2021-06-11 21:18:43](https://github.com/leanprover-community/mathlib/commit/64d453e)
feat(ring_theory/adjoin/basic): add subalgebra.fg_prod ([#7811](https://github.com/leanprover-community/mathlib/pull/7811))
We add `subalgebra.fg_prod`: the product of two finitely generated subalgebras is finitely generated.
A mathematical remark: the result is not difficult, but one needs to be careful. For example, `algebra.adjoin_eq_prod` is false without adding `(1,0)` and `(0,1)` by hand to the set of generators. Moreover, `linear_map.inl` and `linear_map.inr` are not ring homomorphisms, so it seems difficult to mimic the proof for modules. A better mathematical proof is to take surjections from two polynomial rings (in finitely many variables) and considering the tensor product of these polynomial rings, that is again a polynomial ring in finitely many variables, and build a surjection to the product of the subalgebras (using the universal property of the tensor product). The problem with this approach is that one needs to know that the tensor product of polynomial rings is again a polynomial ring, and I don't know well enough the API fort the tensor product to prove this.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_hom.fst
- \+ *def* alg_hom.snd

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.inl_map_mul
- \+ *lemma* linear_map.inr_map_mul

Modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* algebra.adjoin_induction
- \+ *lemma* algebra.adjoin_inl_union_inr_eq_prod
- \+ *lemma* algebra.adjoin_inl_union_inr_le_prod
- \+ *lemma* algebra.adjoin_union
- \- *theorem* algebra.adjoin_union
- \+ *theorem* algebra.adjoin_union_eq_under
- \+ *lemma* algebra.mem_adjoin_of_map_mul
- \+ *lemma* subalgebra.fg_prod

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/finiteness.lean




## [2021-06-11 21:18:42](https://github.com/leanprover-community/mathlib/commit/61a04c5)
feat(algebraic_geometry/structure_sheaf): Define comap on structure sheaf ([#7788](https://github.com/leanprover-community/mathlib/pull/7788))
Defines the comap of a ring homomorphism on the structure sheaves of the prime spectra.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *def* algebraic_geometry.stalk_iso
- \+ *def* algebraic_geometry.structure_sheaf.comap
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_apply
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_comp
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_const
- \+ *def* algebraic_geometry.structure_sheaf.comap_fun
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_fun_is_locally_fraction
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_id'
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_id
- \+ *lemma* algebraic_geometry.structure_sheaf.comap_id_eq_map
- \+ *lemma* algebraic_geometry.structure_sheaf.is_fraction.eq_mk'
- \+/\- *def* algebraic_geometry.to_open
- \- *lemma* algebraic_geometry.to_open_apply
- \+ *lemma* algebraic_geometry.to_open_comp_comap



## [2021-06-11 21:18:40](https://github.com/leanprover-community/mathlib/commit/eb9bd55)
feat(linear_algebra/quadratic_form): Real version of Sylvester's law of inertia ([#7427](https://github.com/leanprover-community/mathlib/pull/7427))
We prove that every nondegenerate real quadratic form is equivalent to a weighted sum of squares with the weights being ±1.
#### Estimated changes
Modified docs/undergrad.yaml


Added src/data/real/sign.lean
- \+ *lemma* real.inv_sign
- \+ *def* real.sign
- \+ *lemma* real.sign_apply_eq
- \+ *lemma* real.sign_inv
- \+ *lemma* real.sign_mul_nonneg
- \+ *lemma* real.sign_mul_pos_of_ne_zero
- \+ *lemma* real.sign_neg
- \+ *lemma* real.sign_of_neg
- \+ *lemma* real.sign_of_not_neg
- \+ *lemma* real.sign_of_zero_le
- \+ *lemma* real.sign_one
- \+ *lemma* real.sign_zero

Modified src/linear_algebra/quadratic_form.lean
- \+ *theorem* quadratic_form.equivalent_one_neg_one_weighted_sum_squared



## [2021-06-11 13:26:19](https://github.com/leanprover-community/mathlib/commit/e8add82)
chore(algebra/{ordered_monoid,linear_ordered_comm_group_with_zero}): remove some uses of @ ([#7884](https://github.com/leanprover-community/mathlib/pull/7884))
This PR replaces a couple of uses of `@` with slightly more verbose proofs that only use the given explicit arguments.
The `by apply mul_lt_mul''' hab0 hcd0` line also works with `mul_lt_mul''' hab0 hcd0` alone (at least on my machine).  The reason for the slightly more elaborate proof is that once the typeclass assumptions will change, the direct term-mode proof will break, while the `by apply` version is more stable.
Besides its aesthetic value, this is useful in PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645), as the typeclass arguments of the involved lemmas will change and this will keep the diff (slightly) shorter.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_monoid.lean




## [2021-06-11 13:26:18](https://github.com/leanprover-community/mathlib/commit/9500d95)
feat(number_theory/l_series): The L-series of an arithmetic function ([#7862](https://github.com/leanprover-community/mathlib/pull/7862))
Defines the L-series of an arithmetic function
Proves a few basic facts about convergence of L-series
#### Estimated changes
Added src/number_theory/l_series.lean
- \+ *def* nat.arithmetic_function.l_series
- \+ *theorem* nat.arithmetic_function.l_series_add
- \+ *lemma* nat.arithmetic_function.l_series_eq_zero_of_not_l_series_summable
- \+ *def* nat.arithmetic_function.l_series_summable
- \+ *theorem* nat.arithmetic_function.l_series_summable_iff_of_re_eq_re
- \+ *theorem* nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re
- \+ *theorem* nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_real
- \+ *lemma* nat.arithmetic_function.l_series_summable_zero
- \+ *theorem* nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re



## [2021-06-11 13:26:17](https://github.com/leanprover-community/mathlib/commit/e35438b)
feat(analysis): Cauchy sequence and series lemmas ([#7858](https://github.com/leanprover-community/mathlib/pull/7858))
from LTE. Mostly relaxing assumptions from metric to
pseudo-metric and proving some obvious lemmas.
eventually_constant_prod and eventually_constant_sum are duplicated by hand because `to_additive` gets confused by the appearance of `1`.
In `norm_le_zero_iff' {G : Type*} [semi_normed_group G] [separated_space G]` and the following two lemmas the type classes assumptions look silly, but those lemmas are indeed useful in some specific situation in LTE.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.eventually_constant_prod
- \+ *lemma* finset.eventually_constant_sum

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* cauchy_seq.add
- \+ *lemma* cauchy_seq_sum_of_eventually_eq
- \+ *lemma* norm_eq_zero_iff'
- \+ *lemma* norm_le_insert'
- \+ *lemma* norm_le_zero_iff'
- \+ *lemma* norm_pos_iff'
- \+ *lemma* normed_group.cauchy_seq_iff
- \+ *lemma* semi_normed_group.mem_closure_iff

Modified src/analysis/specific_limits.lean
- \+ *lemma* cauchy_series_of_le_geometric
- \+ *lemma* dist_partial_sum'
- \+ *lemma* dist_partial_sum
- \+ *lemma* normed_group.cauchy_series_of_le_geometric''
- \+ *lemma* normed_group.cauchy_series_of_le_geometric'
- \+ *lemma* semi_normed_group.cauchy_seq_of_le_geometric
- \+/\- *lemma* uniformity_basis_dist_pow_of_lt_1

Modified src/topology/basic.lean
- \+ *lemma* tendsto_at_bot_of_eventually_const
- \+ *lemma* tendsto_at_top_of_eventually_const



## [2021-06-11 13:26:16](https://github.com/leanprover-community/mathlib/commit/a421185)
feat(algebra/periodic): more periodicity lemmas ([#7853](https://github.com/leanprover-community/mathlib/pull/7853))
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* function.antiperiodic.sub_eq'
- \+ *lemma* function.periodic.gsmul_sub_eq
- \+ *lemma* function.periodic.int_mul_sub_eq
- \+ *lemma* function.periodic.nat_mul_sub_eq
- \+ *lemma* function.periodic.nsmul_sub_eq
- \+ *lemma* function.periodic.sub_eq'



## [2021-06-11 13:26:15](https://github.com/leanprover-community/mathlib/commit/9228ff9)
feat(algebra/ordered_group): abs_sub ([#7850](https://github.com/leanprover-community/mathlib/pull/7850))
- rename `abs_sub` to `abs_sub_comm`
- prove `abs_sub`
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/ordered_group.lean
- \+ *theorem* abs_sub
- \- *lemma* abs_sub
- \+ *lemma* abs_sub_comm

Modified src/data/complex/basic.lean
- \- *lemma* complex.abs_sub
- \+ *lemma* complex.abs_sub_comm

Modified src/data/complex/exponential.lean


Modified src/data/complex/exponential_bounds.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/geometry/euclidean/sphere.lean


Modified src/topology/algebra/ordered/basic.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/uniform_space/compare_reals.lean




## [2021-06-11 13:26:14](https://github.com/leanprover-community/mathlib/commit/4bfe8e8)
feat(algebra/order_functions): lt_max_of_lt_<left/right> ([#7849](https://github.com/leanprover-community/mathlib/pull/7849))
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* lt_max_of_lt_left
- \+ *lemma* lt_max_of_lt_right
- \+ *lemma* min_lt_of_left_lt
- \+ *lemma* min_lt_of_right_lt



## [2021-06-11 13:26:12](https://github.com/leanprover-community/mathlib/commit/915a0a2)
feat(topology/algebra/ordered/basic): add a few subseq-related lemmas ([#7828](https://github.com/leanprover-community/mathlib/pull/7828))
These are lemmas I proved while working on [#7164](https://github.com/leanprover-community/mathlib/pull/7164). Some of them are actually not used anymore in that PR because I'm refactoring it, but I thought they would be useful anyway, so here there are.
#### Estimated changes
Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* infi_eq_infi_subseq_of_monotone
- \+ *lemma* supr_eq_supr_subseq_of_monotone
- \+ *lemma* tendsto_iff_tendsto_subseq_of_monotone



## [2021-06-11 12:07:55](https://github.com/leanprover-community/mathlib/commit/51cd821)
chore(algebra/lie/classical): speed up slow proof ([#7894](https://github.com/leanprover-community/mathlib/pull/7894))
Squeeze a simp in a proof that has just timed out on bors
#### Estimated changes
Modified src/algebra/lie/classical.lean




## [2021-06-11 02:16:14](https://github.com/leanprover-community/mathlib/commit/6eb3d97)
chore(scripts): update nolints.txt ([#7887](https://github.com/leanprover-community/mathlib/pull/7887))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-11 02:16:13](https://github.com/leanprover-community/mathlib/commit/6f6dbad)
feat(set_theory/cardinal): missing lemma ([#7880](https://github.com/leanprover-community/mathlib/pull/7880))
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_range_le_lift



## [2021-06-11 02:16:12](https://github.com/leanprover-community/mathlib/commit/e8aa984)
doc(int/modeq): add module doc and tidy ([#7878](https://github.com/leanprover-community/mathlib/pull/7878))
#### Estimated changes
Modified src/data/int/modeq.lean
- \+/\- *lemma* int.modeq.mod_coprime



## [2021-06-11 02:16:11](https://github.com/leanprover-community/mathlib/commit/1b0e5ee)
chore(data/real/nnreal): avoid abusing inequalities in nnreals ([#7872](https://github.com/leanprover-community/mathlib/pull/7872))
I removed the use of `@`, so that all implicit arguments stay implicit.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645): by only having the explicit arguments, the same proof works, without having to fiddle around with underscores.
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2021-06-11 02:16:10](https://github.com/leanprover-community/mathlib/commit/d570596)
feat(logic/function/basic): a lemma on symmetric operations and flip ([#7871](https://github.com/leanprover-community/mathlib/pull/7871))
This lemma is used to show that if multiplication is commutative, then `flip`ping the arguments returns the same function.
This is used in PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) .
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* is_symm_op.flip_eq



## [2021-06-11 02:16:09](https://github.com/leanprover-community/mathlib/commit/9a4881d)
chore(data/real/pi, analysis/special_functions/trigonometric.lean): speed up/simplify proofs ([#7868](https://github.com/leanprover-community/mathlib/pull/7868))
These are mostly cosmetic changes, simplifying a couple of proofs.  I tried to remove the calls to `linarith` or `norm_num`, when the alternatives were either single lemmas or faster than automation.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/real/pi.lean




## [2021-06-11 02:16:08](https://github.com/leanprover-community/mathlib/commit/f157a37)
chore(logic/basic): fixup `eq_or_ne` ([#7865](https://github.com/leanprover-community/mathlib/pull/7865))
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *theorem* decidable.eq_or_ne
- \+/\- *theorem* decidable.ne_or_eq
- \+/\- *theorem* eq_or_ne
- \+/\- *theorem* ne_or_eq



## [2021-06-11 02:16:07](https://github.com/leanprover-community/mathlib/commit/0a80efb)
chore(analysis/normed_space/normed_group_hom): remove bound_by ([#7860](https://github.com/leanprover-community/mathlib/pull/7860))
`bound_by f C` is the same as `∥f∥ ≤ C` and it is therefore useless now that we have `∥f∥`.
#### Estimated changes
Modified src/analysis/normed_space/normed_group_hom.lean
- \- *theorem* normed_group_hom.antilipschitz_of_bound_by
- \+ *theorem* normed_group_hom.antilipschitz_of_norm_ge
- \+/\- *lemma* normed_group_hom.bound
- \- *def* normed_group_hom.bound_by
- \- *lemma* normed_group_hom.bound_by_one_of_isometry
- \- *lemma* normed_group_hom.lipschitz_of_bound_by
- \- *lemma* normed_group_hom.mk_normed_group_hom'_bound_by
- \- *lemma* normed_group_hom.norm_noninc.bound_by_one
- \+ *lemma* normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one

Modified src/analysis/normed_space/normed_group_quotient.lean




## [2021-06-10 16:03:39](https://github.com/leanprover-community/mathlib/commit/0f8e79e)
feat(algebra/big_operators/finsupp): relax assumptions `semiring` to `non_unital_non_assoc_semiring` ([#7874](https://github.com/leanprover-community/mathlib/pull/7874))
#### Estimated changes
Modified src/algebra/big_operators/finsupp.lean




## [2021-06-10 16:03:38](https://github.com/leanprover-community/mathlib/commit/3b5a44b)
chore(src/testing/slim_check/sampleable): simply add explicit namespace `nat.` ([#7873](https://github.com/leanprover-community/mathlib/pull/7873))
This PR only introduces the explicit namespace `nat.` when calling `le_div_iff_mul_le`.  The reason for doing this is that PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) introduces a lemma `le_div_iff_mul_le` in the root namespace and this one then becomes ambiguous.  Note that CI *does build* on this branch even without the explicit namespace.  The change would only become necessary once/if PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) gets merged.
I isolated this change to a separate PR to reduce the diff of [#7645](https://github.com/leanprover-community/mathlib/pull/7645) and also to bring attention to this issue, in case someone has some comment about it.
#### Estimated changes
Modified src/testing/slim_check/sampleable.lean




## [2021-06-10 16:03:37](https://github.com/leanprover-community/mathlib/commit/2e8ef55)
feat(algebra/floor): nat_floor ([#7855](https://github.com/leanprover-community/mathlib/pull/7855))
introduce `nat_floor`
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/nat_floor
#### Estimated changes
Modified src/algebra/floor.lean
- \+ *theorem* le_nat_floor_iff
- \+ *lemma* le_nat_floor_of_le
- \+/\- *theorem* lt_nat_ceil
- \+ *lemma* lt_nat_floor_add_one
- \+ *lemma* lt_of_lt_nat_floor
- \+/\- *def* nat_ceil
- \+/\- *theorem* nat_ceil_le
- \+ *def* nat_floor
- \+ *theorem* nat_floor_add_nat
- \+ *theorem* nat_floor_coe
- \+ *lemma* nat_floor_eq_zero_iff
- \+ *lemma* nat_floor_le
- \+ *theorem* nat_floor_lt_iff
- \+ *theorem* nat_floor_mono
- \+ *lemma* nat_floor_of_nonpos
- \+ *theorem* nat_floor_zero
- \+ *lemma* pos_of_nat_floor_pos

Modified src/data/int/basic.lean
- \+ *lemma* int.to_nat_add_nat
- \- *lemma* int.to_nat_add_one
- \+ *lemma* int.to_nat_of_nonpos
- \- *lemma* int.to_nat_zero_of_neg

Modified src/tactic/norm_num.lean




## [2021-06-10 16:03:36](https://github.com/leanprover-community/mathlib/commit/021c859)
feat(analysis/special_functions/pow): rpow-log inequalities ([#7848](https://github.com/leanprover-community/mathlib/pull/7848))
Inequalities relating rpow and log
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.le_rpow_iff_log_le
- \+ *lemma* real.le_rpow_of_log_le
- \+ *lemma* real.lt_rpow_iff_log_lt
- \+ *lemma* real.lt_rpow_of_log_lt



## [2021-06-10 16:03:35](https://github.com/leanprover-community/mathlib/commit/49f5a15)
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
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* with_bot.bot_lt_mul
- \+ *lemma* with_bot.bot_mul
- \+ *lemma* with_bot.bot_mul_bot
- \+ *lemma* with_bot.coe_mul
- \+ *lemma* with_bot.mul_bot
- \+ *lemma* with_bot.mul_coe
- \+ *lemma* with_bot.mul_def
- \+ *lemma* with_bot.mul_eq_bot_iff
- \+/\- *lemma* with_top.mul_lt_top

Modified src/data/real/ereal.lean
- \- *lemma* ereal.ad_eq_top_iff
- \+ *lemma* ereal.add_eq_top_iff
- \+ *lemma* ereal.bot_mul_bot
- \+ *lemma* ereal.bot_mul_coe
- \+ *lemma* ereal.bot_sub_coe
- \+ *lemma* ereal.bot_sub_top
- \+ *lemma* ereal.coe_mul
- \+ *lemma* ereal.coe_mul_bot
- \+ *lemma* ereal.coe_one
- \+ *lemma* ereal.coe_sub_bot
- \+ *lemma* ereal.mul_top
- \+ *lemma* ereal.sub_bot
- \+ *lemma* ereal.to_real_mul
- \+ *lemma* ereal.to_real_one
- \+ *lemma* ereal.top_mul
- \+ *lemma* ereal.top_sub

Modified src/order/bounded_lattice.lean




## [2021-06-10 23:57:20+10:00](https://github.com/leanprover-community/mathlib/commit/079b8a1)
Revert "feat(set_theory/cofinality): more infinite pigeonhole principles"
This reverts commit c7ba50f41813718472478983370db66b06c2d33e.
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \- *theorem* cardinal.infinite_pigeonhole''
- \- *theorem* cardinal.infinite_pigeonhole'
- \- *lemma* cardinal.le_range_of_union_finset_eq_top



## [2021-06-10 23:56:13+10:00](https://github.com/leanprover-community/mathlib/commit/c7ba50f)
feat(set_theory/cofinality): more infinite pigeonhole principles
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.infinite_pigeonhole''
- \+ *theorem* cardinal.infinite_pigeonhole'
- \+ *lemma* cardinal.le_range_of_union_finset_eq_top



## [2021-06-10 06:56:02](https://github.com/leanprover-community/mathlib/commit/f7e93d9)
chore(algebra/linear_ordered_comm_group_with_zero.lean): extend calc proofs ([#7870](https://github.com/leanprover-community/mathlib/pull/7870))
These are mostly cosmetic changes, simplifying a couple of calc proofs.
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean




## [2021-06-10 06:56:01](https://github.com/leanprover-community/mathlib/commit/05b7b0b)
chore(scripts): update nolints.txt ([#7867](https://github.com/leanprover-community/mathlib/pull/7867))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-10 06:56:00](https://github.com/leanprover-community/mathlib/commit/4da899c)
chore(number_theory/{fermat4, sum_four_squares, zsqrtd/basic}): simplify/rearrange proofs ([#7866](https://github.com/leanprover-community/mathlib/pull/7866))
These are mostly cosmetic changes, simplifying a couple of proofs.  I would have tagged it `easy`, but since there are three files changed, it may take just over 20'' to review!
The main motivation is to reduce the diff in the bigger PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/number_theory/fermat4.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/number_theory/zsqrtd/basic.lean




## [2021-06-10 01:51:29](https://github.com/leanprover-community/mathlib/commit/2fc66c9)
feat(algebra/group_with_zero): add units.can_lift ([#7857](https://github.com/leanprover-community/mathlib/pull/7857))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/projective.20space/near/242041169)
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean




## [2021-06-10 01:51:28](https://github.com/leanprover-community/mathlib/commit/0a34878)
chore(topology/algebra/continuous_functions): making names consistent with the smooth library ([#7844](https://github.com/leanprover-community/mathlib/pull/7844))
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \+ *lemma* continuous_functions.coe_smul
- \- *lemma* continuous_functions.smul_coe
- \+ *lemma* continuous_map.coe_div
- \+ *lemma* continuous_map.coe_inv
- \+ *lemma* continuous_map.coe_mul
- \+ *lemma* continuous_map.coe_one
- \+ *lemma* continuous_map.coe_pow
- \+ *lemma* continuous_map.coe_smul
- \- *lemma* continuous_map.div_coe
- \- *lemma* continuous_map.inv_coe
- \- *lemma* continuous_map.mul_coe
- \- *lemma* continuous_map.one_coe
- \- *lemma* continuous_map.pow_coe
- \- *lemma* continuous_map.smul_coe



## [2021-06-10 01:51:26](https://github.com/leanprover-community/mathlib/commit/06200c8)
feat(ring_theory/ideal): generalize to noncommutative rings ([#7654](https://github.com/leanprover-community/mathlib/pull/7654))
This is a minimalist generalization of existing material on ideals to the setting of noncommutative rings.
I have not attempted to decide how things should be named in the long run. For now `ideal` specifically means a left-ideal (i.e. I didn't change the definition). We can either in future add `two_sided_ideal` (or `biideal` or `ideal₂` or ...), or potentially rename `ideal` to `left_ideal` or `lideal`, etc. Future bikeshedding opportunities!
In this PR I've just left definitions alone, and relaxed `comm_ring` hypotheses to `ring` as far as I could see possible. No new theorems or mathematics, just rearranging to get things in the right order.
(As a side note, both `ring_theory.ideal.basic` and `ring_theory.ideal.operations` should be split into smaller files; I can try this after this PR.)
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/group/units.lean
- \+ *theorem* is_unit.exists_left_inv
- \+ *theorem* is_unit.exists_right_inv

Modified src/ring_theory/ideal/basic.lean
- \+/\- *theorem* coe_subset_nonunits
- \+/\- *def* ideal
- \+/\- *theorem* mem_nonunits_iff

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* ideal.comap_comap
- \+/\- *lemma* ideal.map_map
- \+/\- *lemma* ring_hom.ker_is_prime

Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-06-09 20:42:50](https://github.com/leanprover-community/mathlib/commit/3870896)
doc(data/semiquot): reformat module doc properly, and add missing doc strings ([#7773](https://github.com/leanprover-community/mathlib/pull/7773))
#### Estimated changes
Modified src/data/semiquot.lean
- \+/\- *def* semiquot.is_pure



## [2021-06-09 20:42:48](https://github.com/leanprover-community/mathlib/commit/abe25e9)
docs(data/mllist): fix module doc, and add all doc strings ([#7772](https://github.com/leanprover-community/mathlib/pull/7772))
#### Estimated changes
Modified src/data/mllist.lean




## [2021-06-09 20:42:47](https://github.com/leanprover-community/mathlib/commit/d9b91f3)
feat(measure_theory/tactic): add measurability tactic ([#7756](https://github.com/leanprover-community/mathlib/pull/7756))
Add a measurability tactic defined in the file `measure_theory/tactic.lean`, which is heavily inspired from the continuity tactic. It proves goals of the form `measurable f`, `ae_measurable f µ` and `measurable_set s`. Some tests are provided in `tests/measurability.lean` and the tactic was used to replace a few lines in `integration.lean` and `mean_inequalities.lean`.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/analysis/mean_inequalities.lean


Modified src/measure_theory/arithmetic.lean
- \+ *lemma* ae_measurable.div'
- \+/\- *lemma* ae_measurable.inv
- \+ *lemma* ae_measurable.mul'
- \+ *lemma* measurable.div'
- \+/\- *lemma* measurable.inv
- \+ *lemma* measurable.mul'

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_set_Icc
- \+/\- *lemma* measurable_set_Ici
- \+/\- *lemma* measurable_set_Ico
- \+/\- *lemma* measurable_set_Iic
- \+/\- *lemma* measurable_set_Iio
- \+/\- *lemma* measurable_set_Ioc
- \+/\- *lemma* measurable_set_Ioi
- \+/\- *lemma* measurable_set_Ioo

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lp_space.lean


Modified src/measure_theory/measurable_space.lean
- \- *lemma* finset.measurable_set_bInter
- \- *lemma* finset.measurable_set_bUnion
- \- *lemma* measurable.comp
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable.iterate
- \+/\- *lemma* measurable.prod
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable.subtype_coe
- \- *def* measurable
- \- *lemma* measurable_const
- \+/\- *lemma* measurable_from_nat
- \+/\- *lemma* measurable_fst
- \- *lemma* measurable_id
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \- *lemma* measurable_set.Inter
- \- *lemma* measurable_set.Inter_Prop
- \- *lemma* measurable_set.Inter_fintype
- \- *lemma* measurable_set.Union
- \- *lemma* measurable_set.Union_Prop
- \- *lemma* measurable_set.Union_fintype
- \- *lemma* measurable_set.bInter
- \- *lemma* measurable_set.bUnion
- \- *lemma* measurable_set.bUnion_decode₂
- \- *lemma* measurable_set.compl
- \- *lemma* measurable_set.compl_iff
- \- *lemma* measurable_set.congr
- \- *lemma* measurable_set.const
- \- *lemma* measurable_set.diff
- \- *lemma* measurable_set.disjointed
- \- *lemma* measurable_set.empty
- \- *lemma* measurable_set.insert
- \- *lemma* measurable_set.inter
- \- *lemma* measurable_set.ite
- \- *lemma* measurable_set.of_compl
- \- *lemma* measurable_set.sInter
- \- *lemma* measurable_set.sUnion
- \- *lemma* measurable_set.union
- \- *lemma* measurable_set.univ
- \- *def* measurable_set
- \- *lemma* measurable_set_eq
- \- *lemma* measurable_set_insert
- \+/\- *lemma* measurable_set_mul_support
- \+ *lemma* measurable_set_preimage
- \+/\- *lemma* measurable_snd
- \- *lemma* measurable_space.ext
- \- *lemma* measurable_space.ext_iff
- \- *def* measurable_space.generate_from
- \- *lemma* measurable_space.generate_from_le
- \- *lemma* measurable_space.generate_from_le_iff
- \- *lemma* measurable_space.generate_from_measurable_set
- \- *inductive* measurable_space.generate_measurable
- \- *def* measurable_space.gi_generate_from
- \- *theorem* measurable_space.measurable_set_Inf
- \- *theorem* measurable_space.measurable_set_Sup
- \- *lemma* measurable_space.measurable_set_bot_iff
- \- *lemma* measurable_space.measurable_set_generate_from
- \- *theorem* measurable_space.measurable_set_inf
- \- *theorem* measurable_space.measurable_set_infi
- \- *theorem* measurable_space.measurable_set_sup
- \- *theorem* measurable_space.measurable_set_supr
- \- *theorem* measurable_space.measurable_set_top
- \- *lemma* measurable_space.mk_of_closure_sets
- \- *structure* measurable_space
- \+/\- *lemma* measurable_subtype_coe
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_unit
- \- *lemma* nonempty_measurable_superset
- \- *lemma* set.countable.measurable_set
- \- *lemma* set.finite.measurable_set
- \- *lemma* set.finite.measurable_set_bInter
- \- *lemma* set.finite.measurable_set_bUnion
- \- *lemma* set.finite.measurable_set_sInter
- \- *lemma* set.finite.measurable_set_sUnion
- \+/\- *lemma* subsingleton.measurable
- \- *lemma* subsingleton.measurable_set

Added src/measure_theory/measurable_space_def.lean
- \+ *lemma* finset.measurable_set_bInter
- \+ *lemma* finset.measurable_set_bUnion
- \+ *lemma* measurable.comp
- \+ *def* measurable
- \+ *lemma* measurable_const
- \+ *lemma* measurable_id'
- \+ *lemma* measurable_id
- \+ *lemma* measurable_set.Inter
- \+ *lemma* measurable_set.Inter_Prop
- \+ *lemma* measurable_set.Inter_fintype
- \+ *lemma* measurable_set.Union
- \+ *lemma* measurable_set.Union_Prop
- \+ *lemma* measurable_set.Union_fintype
- \+ *lemma* measurable_set.bInter
- \+ *lemma* measurable_set.bUnion
- \+ *lemma* measurable_set.bUnion_decode₂
- \+ *lemma* measurable_set.compl
- \+ *lemma* measurable_set.compl_iff
- \+ *lemma* measurable_set.congr
- \+ *lemma* measurable_set.const
- \+ *lemma* measurable_set.diff
- \+ *lemma* measurable_set.disjointed
- \+ *lemma* measurable_set.empty
- \+ *lemma* measurable_set.insert
- \+ *lemma* measurable_set.inter
- \+ *lemma* measurable_set.ite
- \+ *lemma* measurable_set.of_compl
- \+ *lemma* measurable_set.sInter
- \+ *lemma* measurable_set.sUnion
- \+ *lemma* measurable_set.union
- \+ *lemma* measurable_set.univ
- \+ *def* measurable_set
- \+ *lemma* measurable_set_eq
- \+ *lemma* measurable_set_insert
- \+ *lemma* measurable_space.ext
- \+ *lemma* measurable_space.ext_iff
- \+ *def* measurable_space.generate_from
- \+ *lemma* measurable_space.generate_from_le
- \+ *lemma* measurable_space.generate_from_le_iff
- \+ *lemma* measurable_space.generate_from_measurable_set
- \+ *inductive* measurable_space.generate_measurable
- \+ *def* measurable_space.gi_generate_from
- \+ *theorem* measurable_space.measurable_set_Inf
- \+ *theorem* measurable_space.measurable_set_Sup
- \+ *lemma* measurable_space.measurable_set_bot_iff
- \+ *lemma* measurable_space.measurable_set_generate_from
- \+ *theorem* measurable_space.measurable_set_inf
- \+ *theorem* measurable_space.measurable_set_infi
- \+ *theorem* measurable_space.measurable_set_sup
- \+ *theorem* measurable_space.measurable_set_supr
- \+ *theorem* measurable_space.measurable_set_top
- \+ *lemma* measurable_space.mk_of_closure_sets
- \+ *structure* measurable_space
- \+ *lemma* nonempty_measurable_superset
- \+ *lemma* set.countable.measurable_set
- \+ *lemma* set.finite.measurable_set
- \+ *lemma* set.finite.measurable_set_bInter
- \+ *lemma* set.finite.measurable_set_bUnion
- \+ *lemma* set.finite.measurable_set_sInter
- \+ *lemma* set.finite.measurable_set_sUnion
- \+ *lemma* subsingleton.measurable_set

Modified src/measure_theory/measure_space.lean
- \- *lemma* ae_measurable.ae_eq_mk
- \- *lemma* ae_measurable.congr
- \- *lemma* ae_measurable.measurable_mk
- \- *def* ae_measurable.mk
- \- *def* ae_measurable
- \- *lemma* ae_measurable_congr
- \- *lemma* ae_measurable_const
- \+/\- *lemma* ae_measurable_zero_measure
- \- *lemma* measurable.ae_measurable
- \- *lemma* measurable.comp_ae_measurable
- \- *lemma* measure_theory.ae_all_iff
- \- *lemma* measure_theory.ae_ball_iff
- \- *lemma* measure_theory.ae_eq_empty
- \- *lemma* measure_theory.ae_eq_refl
- \- *lemma* measure_theory.ae_eq_set
- \- *lemma* measure_theory.ae_eq_symm
- \- *lemma* measure_theory.ae_eq_trans
- \- *lemma* measure_theory.ae_iff
- \- *lemma* measure_theory.ae_imp_iff
- \- *lemma* measure_theory.ae_le_set
- \- *lemma* measure_theory.ae_of_all
- \- *lemma* measure_theory.coe_to_outer_measure
- \- *lemma* measure_theory.compl_mem_ae_iff
- \- *lemma* measure_theory.diff_ae_eq_self
- \- *lemma* measure_theory.exists_measurable_superset
- \- *lemma* measure_theory.exists_measurable_superset_forall_eq
- \- *lemma* measure_theory.exists_measurable_superset_iff_measure_eq_zero
- \- *lemma* measure_theory.exists_measurable_superset_of_null
- \- *lemma* measure_theory.frequently_ae_iff
- \- *lemma* measure_theory.frequently_ae_mem_iff
- \- *lemma* measure_theory.measurable_set_to_measurable
- \- *def* measure_theory.measure.ae
- \- *lemma* measure_theory.measure.ext
- \- *lemma* measure_theory.measure.ext_iff
- \- *def* measure_theory.measure.of_measurable
- \- *lemma* measure_theory.measure.of_measurable_apply
- \- *lemma* measure_theory.measure.to_outer_measure_injective
- \- *structure* measure_theory.measure
- \- *theorem* measure_theory.measure_Union_le
- \- *lemma* measure_theory.measure_Union_null
- \- *lemma* measure_theory.measure_Union_null_iff
- \- *lemma* measure_theory.measure_bUnion_finset_le
- \- *lemma* measure_theory.measure_bUnion_le
- \- *lemma* measure_theory.measure_bUnion_lt_top
- \- *lemma* measure_theory.measure_bUnion_null_iff
- \- *lemma* measure_theory.measure_congr
- \- *lemma* measure_theory.measure_empty
- \- *lemma* measure_theory.measure_eq_extend
- \- *lemma* measure_theory.measure_eq_induced_outer_measure
- \- *lemma* measure_theory.measure_eq_infi'
- \- *lemma* measure_theory.measure_eq_infi
- \- *lemma* measure_theory.measure_eq_trim
- \- *lemma* measure_theory.measure_mono
- \- *lemma* measure_theory.measure_mono_ae
- \- *lemma* measure_theory.measure_mono_null
- \- *lemma* measure_theory.measure_mono_top
- \- *lemma* measure_theory.measure_to_measurable
- \- *theorem* measure_theory.measure_union_le
- \- *lemma* measure_theory.measure_union_null
- \- *lemma* measure_theory.measure_union_null_iff
- \- *lemma* measure_theory.measure_zero_iff_ae_nmem
- \- *lemma* measure_theory.mem_ae_iff
- \- *lemma* measure_theory.nonempty_of_measure_ne_zero
- \- *lemma* measure_theory.subset_to_measurable
- \- *def* measure_theory.to_measurable
- \- *lemma* measure_theory.to_outer_measure_apply
- \- *lemma* measure_theory.to_outer_measure_eq_induced_outer_measure
- \- *lemma* measure_theory.union_ae_eq_right
- \+/\- *lemma* subsingleton.ae_measurable

Added src/measure_theory/measure_space_def.lean
- \+ *lemma* ae_measurable.ae_eq_mk
- \+ *lemma* ae_measurable.congr
- \+ *lemma* ae_measurable.measurable_mk
- \+ *def* ae_measurable.mk
- \+ *def* ae_measurable
- \+ *lemma* ae_measurable_congr
- \+ *lemma* ae_measurable_const
- \+ *lemma* ae_measurable_id'
- \+ *lemma* ae_measurable_id
- \+ *lemma* measurable.ae_measurable
- \+ *lemma* measurable.comp_ae_measurable
- \+ *lemma* measure_theory.ae_all_iff
- \+ *lemma* measure_theory.ae_ball_iff
- \+ *lemma* measure_theory.ae_eq_empty
- \+ *lemma* measure_theory.ae_eq_refl
- \+ *lemma* measure_theory.ae_eq_set
- \+ *lemma* measure_theory.ae_eq_symm
- \+ *lemma* measure_theory.ae_eq_trans
- \+ *lemma* measure_theory.ae_iff
- \+ *lemma* measure_theory.ae_imp_iff
- \+ *lemma* measure_theory.ae_le_set
- \+ *lemma* measure_theory.ae_of_all
- \+ *lemma* measure_theory.coe_to_outer_measure
- \+ *lemma* measure_theory.compl_mem_ae_iff
- \+ *lemma* measure_theory.diff_ae_eq_self
- \+ *lemma* measure_theory.exists_measurable_superset
- \+ *lemma* measure_theory.exists_measurable_superset_forall_eq
- \+ *lemma* measure_theory.exists_measurable_superset_iff_measure_eq_zero
- \+ *lemma* measure_theory.exists_measurable_superset_of_null
- \+ *lemma* measure_theory.frequently_ae_iff
- \+ *lemma* measure_theory.frequently_ae_mem_iff
- \+ *lemma* measure_theory.measurable_set_to_measurable
- \+ *def* measure_theory.measure.ae
- \+ *lemma* measure_theory.measure.ext
- \+ *lemma* measure_theory.measure.ext_iff
- \+ *def* measure_theory.measure.of_measurable
- \+ *lemma* measure_theory.measure.of_measurable_apply
- \+ *lemma* measure_theory.measure.to_outer_measure_injective
- \+ *structure* measure_theory.measure
- \+ *theorem* measure_theory.measure_Union_le
- \+ *lemma* measure_theory.measure_Union_null
- \+ *lemma* measure_theory.measure_Union_null_iff
- \+ *lemma* measure_theory.measure_bUnion_finset_le
- \+ *lemma* measure_theory.measure_bUnion_le
- \+ *lemma* measure_theory.measure_bUnion_lt_top
- \+ *lemma* measure_theory.measure_bUnion_null_iff
- \+ *lemma* measure_theory.measure_congr
- \+ *lemma* measure_theory.measure_empty
- \+ *lemma* measure_theory.measure_eq_extend
- \+ *lemma* measure_theory.measure_eq_induced_outer_measure
- \+ *lemma* measure_theory.measure_eq_infi'
- \+ *lemma* measure_theory.measure_eq_infi
- \+ *lemma* measure_theory.measure_eq_trim
- \+ *lemma* measure_theory.measure_mono
- \+ *lemma* measure_theory.measure_mono_ae
- \+ *lemma* measure_theory.measure_mono_null
- \+ *lemma* measure_theory.measure_mono_top
- \+ *lemma* measure_theory.measure_to_measurable
- \+ *theorem* measure_theory.measure_union_le
- \+ *lemma* measure_theory.measure_union_null
- \+ *lemma* measure_theory.measure_union_null_iff
- \+ *lemma* measure_theory.measure_zero_iff_ae_nmem
- \+ *lemma* measure_theory.mem_ae_iff
- \+ *lemma* measure_theory.nonempty_of_measure_ne_zero
- \+ *lemma* measure_theory.subset_to_measurable
- \+ *def* measure_theory.to_measurable
- \+ *lemma* measure_theory.to_outer_measure_apply
- \+ *lemma* measure_theory.to_outer_measure_eq_induced_outer_measure
- \+ *lemma* measure_theory.union_ae_eq_right

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/pi_system.lean


Added src/measure_theory/tactic.lean


Added test/measurability.lean




## [2021-06-09 15:40:05](https://github.com/leanprover-community/mathlib/commit/8e25717)
chore(geometry/euclidean/circumcenter): remove two `have`s in a proof ([#7852](https://github.com/leanprover-community/mathlib/pull/7852))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/circumcenter
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean




## [2021-06-09 15:40:04](https://github.com/leanprover-community/mathlib/commit/d0ed2a4)
chore(measure_theory/set_integral): put the definition of integrable_on into a new file ([#7842](https://github.com/leanprover-community/mathlib/pull/7842))
The file `measure_theory.set_integral` is split into two: the `integrable_on` predicate is put into its own file, which does not import  `measure_theory.bochner_integration` (this puts the definition of that integrability property before the definition of the actual integral). The file `measure_theory.set_integral` retains all facts about `set_integral`.
#### Estimated changes
Added src/measure_theory/integrable_on.lean
- \+ *lemma* ae_measurable.measurable_at_filter_of_mem
- \+ *lemma* continuous.integrable_of_compact_closure_support
- \+ *lemma* continuous.integrable_on_compact
- \+ *lemma* continuous_linear_map.integrable_comp
- \+ *lemma* continuous_on.ae_measurable
- \+ *lemma* continuous_on.integrable_at_nhds_within
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* measurable_at_bot
- \+ *def* measurable_at_filter
- \+ *lemma* measure_theory.ae_measurable_indicator_iff
- \+ *lemma* measure_theory.has_finite_integral_restrict_of_bounded
- \+ *lemma* measure_theory.integrable.indicator
- \+ *lemma* measure_theory.integrable.integrable_on'
- \+ *lemma* measure_theory.integrable.integrable_on
- \+ *lemma* measure_theory.integrable_add
- \+ *lemma* measure_theory.integrable_at_filter.filter_mono
- \+ *lemma* measure_theory.integrable_at_filter.inf_ae_iff
- \+ *lemma* measure_theory.integrable_at_filter.inf_of_left
- \+ *lemma* measure_theory.integrable_at_filter.inf_of_right
- \+ *def* measure_theory.integrable_at_filter
- \+ *lemma* measure_theory.integrable_indicator_iff
- \+ *lemma* measure_theory.integrable_on.add_measure
- \+ *lemma* measure_theory.integrable_on.indicator
- \+ *lemma* measure_theory.integrable_on.integrable
- \+ *lemma* measure_theory.integrable_on.left_of_union
- \+ *lemma* measure_theory.integrable_on.mono
- \+ *lemma* measure_theory.integrable_on.mono_measure
- \+ *lemma* measure_theory.integrable_on.mono_set
- \+ *lemma* measure_theory.integrable_on.mono_set_ae
- \+ *lemma* measure_theory.integrable_on.restrict
- \+ *lemma* measure_theory.integrable_on.right_of_union
- \+ *lemma* measure_theory.integrable_on.union
- \+ *def* measure_theory.integrable_on
- \+ *lemma* measure_theory.integrable_on_add_measure
- \+ *lemma* measure_theory.integrable_on_const
- \+ *lemma* measure_theory.integrable_on_empty
- \+ *lemma* measure_theory.integrable_on_finite_union
- \+ *lemma* measure_theory.integrable_on_finset_union
- \+ *lemma* measure_theory.integrable_on_union
- \+ *lemma* measure_theory.integrable_on_univ
- \+ *lemma* measure_theory.integrable_on_zero
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+ *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl

Modified src/measure_theory/set_integral.lean
- \- *lemma* ae_measurable.measurable_at_filter_of_mem
- \- *lemma* continuous.integrable_of_compact_closure_support
- \- *lemma* continuous.integrable_on_compact
- \- *lemma* continuous_linear_map.integrable_comp
- \- *lemma* continuous_on.ae_measurable
- \- *lemma* continuous_on.integrable_at_nhds_within
- \- *lemma* continuous_on.integrable_on_compact
- \- *lemma* indicator_ae_eq_restrict
- \- *lemma* indicator_ae_eq_restrict_compl
- \- *lemma* is_compact.integrable_on_of_nhds_within
- \- *lemma* measurable_at_bot
- \- *def* measurable_at_filter
- \- *lemma* measure_theory.ae_measurable_indicator_iff
- \- *lemma* measure_theory.has_finite_integral_restrict_of_bounded
- \- *lemma* measure_theory.integrable.indicator
- \- *lemma* measure_theory.integrable.integrable_on'
- \- *lemma* measure_theory.integrable.integrable_on
- \- *lemma* measure_theory.integrable_add
- \- *lemma* measure_theory.integrable_at_filter.filter_mono
- \- *lemma* measure_theory.integrable_at_filter.inf_ae_iff
- \- *lemma* measure_theory.integrable_at_filter.inf_of_left
- \- *lemma* measure_theory.integrable_at_filter.inf_of_right
- \- *def* measure_theory.integrable_at_filter
- \- *lemma* measure_theory.integrable_indicator_iff
- \- *lemma* measure_theory.integrable_on.add_measure
- \- *lemma* measure_theory.integrable_on.indicator
- \- *lemma* measure_theory.integrable_on.integrable
- \- *lemma* measure_theory.integrable_on.left_of_union
- \- *lemma* measure_theory.integrable_on.mono
- \- *lemma* measure_theory.integrable_on.mono_measure
- \- *lemma* measure_theory.integrable_on.mono_set
- \- *lemma* measure_theory.integrable_on.mono_set_ae
- \- *lemma* measure_theory.integrable_on.restrict
- \- *lemma* measure_theory.integrable_on.right_of_union
- \- *lemma* measure_theory.integrable_on.union
- \- *def* measure_theory.integrable_on
- \- *lemma* measure_theory.integrable_on_add_measure
- \- *lemma* measure_theory.integrable_on_const
- \- *lemma* measure_theory.integrable_on_empty
- \- *lemma* measure_theory.integrable_on_finite_union
- \- *lemma* measure_theory.integrable_on_finset_union
- \- *lemma* measure_theory.integrable_on_union
- \- *lemma* measure_theory.integrable_on_univ
- \- *lemma* measure_theory.integrable_on_zero
- \- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter
- \- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto
- \- *lemma* measure_theory.measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \- *lemma* piecewise_ae_eq_restrict
- \- *lemma* piecewise_ae_eq_restrict_compl



## [2021-06-09 15:40:02](https://github.com/leanprover-community/mathlib/commit/764e878)
feat(algebra/ordered_group): `-abs a ≤ a` ([#7839](https://github.com/leanprover-community/mathlib/pull/7839))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* neg_abs_le_self



## [2021-06-09 15:40:01](https://github.com/leanprover-community/mathlib/commit/a9d4f3d)
fix(*): make some non-instances reducible ([#7835](https://github.com/leanprover-community/mathlib/pull/7835))
* Definitions that involve in instances might need to be reducible, see added library note. 
* This involves the definitions `*order.lift` / `function.injective.*` and `function.surjective.*` 
* This came up in [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/field.lean


Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/algebra/hierarchy_design.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/ring/basic.lean


Modified src/algebra/smul_with_zero.lean


Modified src/group_theory/group_action/defs.lean


Modified src/order/basic.lean
- \+/\- *def* linear_order.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* preorder.lift



## [2021-06-09 15:40:00](https://github.com/leanprover-community/mathlib/commit/20efef7)
chore(algebra/field_power, data/set/intervals/basic): simpler proofs in the first file, fewer parentheses in the second one ([#7831](https://github.com/leanprover-community/mathlib/pull/7831))
This is mostly a cosmetic PR: I removed two calls to `linarith`, where a term-mode proof was very simple.
I also removed some unnecessary parentheses in a different file.
#### Estimated changes
Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/field_power.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* real.cos_one_pos

Modified src/data/set/intervals/basic.lean




## [2021-06-09 15:39:59](https://github.com/leanprover-community/mathlib/commit/02d5370)
chore(measure_theory/outer_measure): add extend_eq_top ([#7827](https://github.com/leanprover-community/mathlib/pull/7827))
#### Estimated changes
Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.extend_eq_top



## [2021-06-09 15:39:58](https://github.com/leanprover-community/mathlib/commit/fa7c6da)
docs(order/bounded_lattice): add module docstring ([#7799](https://github.com/leanprover-community/mathlib/pull/7799))
add module docstring and some sectioning
#### Estimated changes
Modified src/order/bounded_lattice.lean




## [2021-06-09 10:12:47](https://github.com/leanprover-community/mathlib/commit/55abf1a)
chore(scripts): update nolints.txt ([#7851](https://github.com/leanprover-community/mathlib/pull/7851))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-09 10:12:46](https://github.com/leanprover-community/mathlib/commit/8676685)
feat(ring_theory): every left-noetherian ring satisfies the strong rank condition ([#7711](https://github.com/leanprover-community/mathlib/pull/7711))
This PR also discards the proof that every left-noetherian ring satisfies the rank condition, because we already have in [#7683](https://github.com/leanprover-community/mathlib/pull/7683) that this implies that.
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/module/submodule_lattice.lean
- \+ *def* submodule.bot_equiv_punit
- \+ *def* submodule.top_equiv_self

Modified src/analysis/normed_space/inner_product.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.sum_arrow_equiv_prod_arrow_apply_fst
- \+ *lemma* equiv.sum_arrow_equiv_prod_arrow_apply_snd
- \+ *lemma* equiv.sum_arrow_equiv_prod_arrow_symm_apply_inl
- \+ *lemma* equiv.sum_arrow_equiv_prod_arrow_symm_apply_inr

Modified src/data/set/disjointed.lean
- \+ *theorem* pairwise_disjoint_on_nat
- \+ *theorem* pairwise_on_nat

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.comap_inf_map_of_injective
- \+ *lemma* submodule.comap_infi_map_of_injective
- \+ *lemma* submodule.comap_map_eq_of_injective
- \+ *lemma* submodule.comap_sup_map_of_injective
- \+ *lemma* submodule.comap_supr_map_of_injective
- \+ *lemma* submodule.comap_surjective_of_injective
- \+ *def* submodule.gci_map_comap
- \+ *lemma* submodule.map_injective_of_injective
- \+ *lemma* submodule.map_le_map_iff_of_injective
- \+ *lemma* submodule.map_strict_mono_of_injective

Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/pi.lean
- \+ *def* linear_equiv.sum_arrow_lequiv_prod_arrow
- \+ *lemma* linear_equiv.sum_arrow_lequiv_prod_arrow_apply_fst
- \+ *lemma* linear_equiv.sum_arrow_lequiv_prod_arrow_apply_snd
- \+ *lemma* linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inl
- \+ *lemma* linear_equiv.sum_arrow_lequiv_prod_arrow_symm_apply_inr

Modified src/linear_algebra/prod.lean
- \+ *def* linear_map.tailing
- \+ *lemma* linear_map.tailing_disjoint_tunnel_succ
- \+ *lemma* linear_map.tailing_le_tunnel
- \+ *def* linear_map.tailing_linear_equiv
- \+ *lemma* linear_map.tailing_sup_tunnel_succ_le_tunnel
- \+ *def* linear_map.tailings
- \+ *lemma* linear_map.tailings_disjoint_tailing
- \+ *lemma* linear_map.tailings_disjoint_tunnel
- \+ *lemma* linear_map.tailings_succ
- \+ *lemma* linear_map.tailings_zero
- \+ *def* linear_map.tunnel
- \+ *def* linear_map.tunnel_aux
- \+ *lemma* linear_map.tunnel_aux_injective
- \+ *def* submodule.fst
- \+ *def* submodule.fst_equiv
- \+ *lemma* submodule.fst_inf_snd
- \+ *lemma* submodule.fst_map_fst
- \+ *lemma* submodule.fst_map_snd
- \+ *lemma* submodule.fst_sup_snd
- \+ *def* submodule.snd
- \+ *def* submodule.snd_equiv
- \+ *lemma* submodule.snd_map_fst
- \+ *lemma* submodule.snd_map_snd

Modified src/logic/unique.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_disjoint_absorbs

Modified src/order/modular_lattice.lean
- \+ *theorem* disjoint.disjoint_sup_left_of_disjoint_sup_right

Added src/order/partial_sups.lean
- \+ *lemma* le_partial_sups
- \+ *def* partial_sups
- \+ *lemma* partial_sups_disjoint_of_disjoint
- \+ *lemma* partial_sups_eq
- \+ *lemma* partial_sups_le
- \+ *lemma* partial_sups_succ
- \+ *lemma* partial_sups_zero

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *theorem* is_noetherian.bijective_of_surjective_endomorphism
- \+ *lemma* is_noetherian.disjoint_partial_sups_eventually_bot
- \+/\- *lemma* is_noetherian.induction
- \+/\- *theorem* is_noetherian.injective_of_surjective_endomorphism
- \+/\- *theorem* is_noetherian_iff_well_founded
- \+/\- *theorem* monotone_stabilizes_iff_noetherian
- \+/\- *theorem* set_has_maximal_iff_noetherian



## [2021-06-09 10:12:45](https://github.com/leanprover-community/mathlib/commit/47ad680)
feat(measure_theory/interval_integral): integration by substitution / change of variables ([#7273](https://github.com/leanprover-community/mathlib/pull/7273))
Given that `f` has a derivative at `f'` everywhere on `interval a b`,
`∫ x in a..b, (g ∘ f) x * f' x = ∫ x in f a..f b, g x`.
Co-authored by @ADedecker
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *theorem* interval_integral.integral_comp_mul_deriv'
- \+ *theorem* interval_integral.integral_comp_mul_deriv

Modified test/integration.lean




## [2021-06-09 06:11:41](https://github.com/leanprover-community/mathlib/commit/faa58e5)
refactor(algebra/module/projective) make is_projective a class ([#7830](https://github.com/leanprover-community/mathlib/pull/7830))
Make `is_projective` a class.
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/module/projective.lean
- \- *theorem* is_projective.lifting_property
- \- *theorem* is_projective.of_free
- \- *theorem* is_projective.of_lifting_property'
- \- *theorem* is_projective.of_lifting_property
- \- *def* is_projective
- \+ *lemma* module.projective_def
- \+ *theorem* module.projective_lifting_property
- \+ *theorem* module.projective_of_free
- \+ *theorem* module.projective_of_lifting_property'
- \+ *theorem* module.projective_of_lifting_property



## [2021-06-09 06:11:39](https://github.com/leanprover-community/mathlib/commit/c210d0f)
feat(topology/category/limits): Topological bases in cofiltered limits ([#7820](https://github.com/leanprover-community/mathlib/pull/7820))
This PR proves a theorem which provides a simple characterization of certain topological bases in a cofiltered limit of topological spaces.
Eventually I will specialize this assertion to the case where the topological spaces are profinite, and the `T i` are the topological bases given by clopen sets.
This generalizes a lemma from LTE.
#### Estimated changes
Modified src/topology/category/Top/basic.lean
- \+ *def* Top.homeo_of_iso
- \+ *def* Top.iso_of_homeo
- \+ *lemma* Top.of_homeo_of_iso
- \+ *lemma* Top.of_iso_of_homeo

Modified src/topology/category/Top/limits.lean
- \+ *theorem* Top.is_topological_basis_cofiltered_limit
- \+ *def* Top.limit_cone_infi
- \+ *def* Top.limit_cone_infi_is_limit



## [2021-06-09 06:11:38](https://github.com/leanprover-community/mathlib/commit/34c433d)
feat(data/finsupp): generalize finsupp.has_scalar to require only distrib_mul_action instead of semimodule ([#7819](https://github.com/leanprover-community/mathlib/pull/7819))
This propagates the generalization to (add_)monoid_algebra and mv_polynomial.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.coe_smul
- \+/\- *lemma* finsupp.filter_smul
- \+/\- *lemma* finsupp.map_domain_smul
- \+/\- *lemma* finsupp.map_range_smul
- \+/\- *lemma* finsupp.smul_apply
- \+/\- *lemma* finsupp.smul_single
- \+/\- *lemma* finsupp.sum_smul_index'
- \+/\- *lemma* finsupp.support_smul

Modified src/data/finsupp/to_dfinsupp.lean
- \+/\- *lemma* dfinsupp.to_finsupp_smul
- \+/\- *lemma* finsupp.to_dfinsupp_smul

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.coeff_smul



## [2021-06-09 06:11:37](https://github.com/leanprover-community/mathlib/commit/393f638)
feat(ring_theory/localization): Make local_ring_hom more flexible ([#7787](https://github.com/leanprover-community/mathlib/pull/7787))
Make `localization.local_ring_hom` more flexible, by allowing two ideals `I` and `J` as arguments, with the assumption that `I` equals `ideal.comap f J`. Also add lemmas about identity and composition.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* localization.local_ring_hom_comp
- \+ *lemma* localization.local_ring_hom_id
- \+/\- *lemma* localization.local_ring_hom_mk'
- \+/\- *lemma* localization.local_ring_hom_to_map
- \+/\- *lemma* localization.local_ring_hom_unique



## [2021-06-08 19:13:24](https://github.com/leanprover-community/mathlib/commit/5c6d3bc)
feat(topology/instances/ereal): more on ereal, notably its topology ([#7765](https://github.com/leanprover-community/mathlib/pull/7765))
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/data/real/ereal.lean
- \+ *def* ennreal.to_ereal
- \+ *lemma* ereal.ad_eq_top_iff
- \+ *lemma* ereal.add_lt_add
- \+ *lemma* ereal.add_lt_add_left_coe
- \+ *lemma* ereal.add_lt_add_of_lt_of_le
- \+ *lemma* ereal.add_lt_add_right_coe
- \+ *lemma* ereal.add_lt_top_iff
- \+ *lemma* ereal.add_top
- \+ *lemma* ereal.bot_add_bot
- \+ *lemma* ereal.bot_add_coe
- \+ *lemma* ereal.bot_lt_coe
- \+ *lemma* ereal.bot_lt_coe_ennreal
- \+ *lemma* ereal.bot_lt_top
- \+ *lemma* ereal.bot_lt_zero
- \+ *lemma* ereal.bot_ne_coe
- \+ *lemma* ereal.bot_ne_top
- \+ *lemma* ereal.bot_ne_zero
- \+ *lemma* ereal.coe_add
- \+ *lemma* ereal.coe_add_bot
- \+ *lemma* ereal.coe_ennreal_add
- \+ *lemma* ereal.coe_ennreal_eq_coe_ennreal_iff
- \+ *lemma* ereal.coe_ennreal_eq_top_iff
- \+ *lemma* ereal.coe_ennreal_le_coe_ennreal_iff
- \+ *lemma* ereal.coe_ennreal_lt_coe_ennreal_iff
- \+ *lemma* ereal.coe_ennreal_ne_bot
- \+ *lemma* ereal.coe_ennreal_nonneg
- \+ *lemma* ereal.coe_ennreal_top
- \+ *lemma* ereal.coe_ennreal_zero
- \+ *lemma* ereal.coe_lt_top
- \+ *lemma* ereal.coe_ne_bot
- \+ *lemma* ereal.coe_ne_top
- \+ *lemma* ereal.coe_neg
- \+ *lemma* ereal.coe_nnreal_eq_coe_real
- \+ *lemma* ereal.coe_nnreal_lt_top
- \+ *lemma* ereal.coe_nnreal_ne_top
- \+ *lemma* ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal
- \+ *lemma* ereal.coe_zero
- \+ *lemma* ereal.exists_rat_btwn_of_lt
- \+ *lemma* ereal.lt_iff_exists_rat_btwn
- \+ *def* ereal.ne_top_bot_equiv_real
- \+ *lemma* ereal.neg_bot
- \+ *lemma* ereal.neg_eg_bot_iff
- \+ *lemma* ereal.neg_eg_top_iff
- \+ *lemma* ereal.neg_eg_zero_iff
- \+ *theorem* ereal.neg_eq_neg_iff
- \+/\- *theorem* ereal.neg_inj
- \+ *lemma* ereal.neg_le_neg_iff
- \+ *lemma* ereal.neg_lt_iff_neg_lt
- \+ *lemma* ereal.neg_lt_of_neg_lt
- \+ *def* ereal.neg_order_iso
- \+ *lemma* ereal.neg_top
- \+ *lemma* ereal.neg_zero
- \+ *lemma* ereal.sub_eq_add_neg
- \+ *lemma* ereal.sub_le_sub
- \+ *lemma* ereal.sub_lt_sub_of_lt_of_le
- \+ *lemma* ereal.sub_zero
- \+ *def* ereal.to_real
- \+ *lemma* ereal.to_real_add
- \+ *lemma* ereal.to_real_bot
- \+ *lemma* ereal.to_real_coe
- \+ *lemma* ereal.to_real_coe_ennreal
- \+ *lemma* ereal.to_real_le_to_real
- \+ *lemma* ereal.to_real_neg
- \+ *lemma* ereal.to_real_sub
- \+ *lemma* ereal.to_real_top
- \+ *lemma* ereal.to_real_zero
- \+ *lemma* ereal.top_add
- \+ *lemma* ereal.top_ne_coe
- \+ *lemma* ereal.top_ne_zero
- \+ *lemma* ereal.zero_lt_top
- \+ *lemma* ereal.zero_ne_bot
- \+ *lemma* ereal.zero_ne_top
- \+ *lemma* ereal.zero_sub
- \+ *def* real.to_ereal

Modified src/order/conditionally_complete_lattice.lean


Added src/topology/instances/ereal.lean
- \+ *lemma* continuous_coe_ennreal_ereal
- \+ *lemma* continuous_coe_real_ereal
- \+ *lemma* ereal.continuous_at_add
- \+ *lemma* ereal.continuous_at_add_bot_bot
- \+ *lemma* ereal.continuous_at_add_bot_coe
- \+ *lemma* ereal.continuous_at_add_coe_bot
- \+ *lemma* ereal.continuous_at_add_coe_coe
- \+ *lemma* ereal.continuous_at_add_coe_top
- \+ *lemma* ereal.continuous_at_add_top_coe
- \+ *lemma* ereal.continuous_at_add_top_top
- \+ *lemma* ereal.continuous_coe_ennreal_iff
- \+ *lemma* ereal.continuous_coe_iff
- \+ *lemma* ereal.continuous_neg
- \+ *lemma* ereal.continuous_on_to_real
- \+ *lemma* ereal.embedding_coe
- \+ *lemma* ereal.embedding_coe_ennreal
- \+ *lemma* ereal.mem_nhds_bot_iff
- \+ *lemma* ereal.mem_nhds_top_iff
- \+ *def* ereal.ne_bot_top_homeomorph_real
- \+ *def* ereal.neg_homeo
- \+ *lemma* ereal.nhds_bot'
- \+ *lemma* ereal.nhds_bot
- \+ *lemma* ereal.nhds_coe
- \+ *lemma* ereal.nhds_coe_coe
- \+ *lemma* ereal.nhds_top'
- \+ *lemma* ereal.nhds_top
- \+ *lemma* ereal.open_embedding_coe
- \+ *lemma* ereal.tendsto_coe
- \+ *lemma* ereal.tendsto_coe_ennreal
- \+ *lemma* ereal.tendsto_nhds_bot_iff_real
- \+ *lemma* ereal.tendsto_nhds_top_iff_real
- \+ *lemma* ereal.tendsto_to_real



## [2021-06-08 19:13:23](https://github.com/leanprover-community/mathlib/commit/75c81de)
feat(measure_theory/integration): a measurable function is a series of simple functions ([#7764](https://github.com/leanprover-community/mathlib/pull/7764))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *def* measure_theory.simple_func.eapprox_diff
- \+ *lemma* measure_theory.simple_func.eapprox_lt_top
- \+ *lemma* measure_theory.simple_func.sum_eapprox_diff
- \+ *lemma* measure_theory.simple_func.tsum_eapprox_diff



## [2021-06-08 19:13:22](https://github.com/leanprover-community/mathlib/commit/39406bb)
feat(model_theory/basic): First-order languages, structures, homomorphisms, embeddings, and equivs ([#7754](https://github.com/leanprover-community/mathlib/pull/7754))
Defines the following notions from first-order logic:
- languages
- structures
- homomorphisms
- embeddings
- equivalences (isomorphisms)
The definitions of languages and structures take inspiration from the Flypitch project.
#### Estimated changes
Modified docs/references.bib


Added src/model_theory/basic.lean
- \+ *def* first_order.language.const
- \+ *lemma* first_order.language.embedding.coe_injective
- \+ *lemma* first_order.language.embedding.coe_to_hom
- \+ *def* first_order.language.embedding.comp
- \+ *lemma* first_order.language.embedding.comp_apply
- \+ *lemma* first_order.language.embedding.comp_assoc
- \+ *lemma* first_order.language.embedding.ext
- \+ *lemma* first_order.language.embedding.ext_iff
- \+ *lemma* first_order.language.embedding.injective
- \+ *lemma* first_order.language.embedding.map_fun
- \+ *lemma* first_order.language.embedding.map_rel
- \+ *def* first_order.language.embedding.refl
- \+ *lemma* first_order.language.embedding.refl_apply
- \+ *def* first_order.language.embedding.to_hom
- \+ *def* first_order.language.empty
- \+ *lemma* first_order.language.equiv.coe_injective
- \+ *lemma* first_order.language.equiv.coe_to_embedding
- \+ *lemma* first_order.language.equiv.coe_to_hom
- \+ *def* first_order.language.equiv.comp
- \+ *lemma* first_order.language.equiv.comp_apply
- \+ *lemma* first_order.language.equiv.comp_assoc
- \+ *lemma* first_order.language.equiv.ext
- \+ *lemma* first_order.language.equiv.ext_iff
- \+ *lemma* first_order.language.equiv.injective
- \+ *lemma* first_order.language.equiv.map_fun
- \+ *lemma* first_order.language.equiv.map_rel
- \+ *def* first_order.language.equiv.refl
- \+ *lemma* first_order.language.equiv.refl_apply
- \+ *def* first_order.language.equiv.symm
- \+ *def* first_order.language.equiv.to_embedding
- \+ *lemma* first_order.language.equiv.to_embedding_to_hom
- \+ *def* first_order.language.equiv.to_hom
- \+ *lemma* first_order.language.hom.coe_injective
- \+ *def* first_order.language.hom.comp
- \+ *lemma* first_order.language.hom.comp_apply
- \+ *lemma* first_order.language.hom.comp_assoc
- \+ *lemma* first_order.language.hom.ext
- \+ *lemma* first_order.language.hom.ext_iff
- \+ *def* first_order.language.hom.id
- \+ *lemma* first_order.language.hom.id_apply
- \+ *lemma* first_order.language.hom.map_fun
- \+ *lemma* first_order.language.hom.map_rel
- \+ *lemma* first_order.language.hom.to_fun_eq_coe
- \+ *structure* first_order.language



## [2021-06-08 06:35:33](https://github.com/leanprover-community/mathlib/commit/42c4237)
chore(mv_polynomial/equiv): speed up elaboration by adjusting priorities ([#7840](https://github.com/leanprover-community/mathlib/pull/7840))
`option_equiv_left` timed out several times in bors, since the introduction of non-unital rings. We fix this by adjusting the priority to make sure that the problematic instance is found right away.
Also speed up circumcenter file (which also just timed out in bors) by squeezing simps.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean


Modified src/geometry/euclidean/circumcenter.lean




## [2021-06-07 15:40:25](https://github.com/leanprover-community/mathlib/commit/320da57)
chore(data/fintype/basic): add fintype instance for `is_empty` ([#7692](https://github.com/leanprover-community/mathlib/pull/7692))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_eq_empty'
- \+ *theorem* fintype.card_of_is_empty
- \+ *theorem* fintype.univ_of_is_empty

Modified src/data/fintype/card.lean


Modified test/matrix.lean




## [2021-06-07 15:40:24](https://github.com/leanprover-community/mathlib/commit/6e67536)
feat(category/limits): kernel.map ([#7623](https://github.com/leanprover-community/mathlib/pull/7623))
A generalization of a lemma from LTE, stated for a category with (co)kernels.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.parallel_pair_hom
- \+ *lemma* category_theory.limits.parallel_pair_hom_app_one
- \+ *lemma* category_theory.limits.parallel_pair_hom_app_zero

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *abbreviation* category_theory.limits.cokernel.map
- \+ *lemma* category_theory.limits.cokernel.map_desc
- \+ *lemma* category_theory.limits.kernel.lift_map
- \+ *abbreviation* category_theory.limits.kernel.map



## [2021-06-07 15:40:23](https://github.com/leanprover-community/mathlib/commit/fb72599)
feat(algebra/periodic): define periodicity ([#7572](https://github.com/leanprover-community/mathlib/pull/7572))
This PR introduces a general notion of periodicity. It also includes proofs of the "usual" properties of periodic (and antiperiodic) functions.
#### Estimated changes
Added src/algebra/periodic.lean
- \+ *lemma* function.antiperiodic.add
- \+ *lemma* function.antiperiodic.const_inv_mul
- \+ *lemma* function.antiperiodic.const_inv_smul'
- \+ *lemma* function.antiperiodic.const_inv_smul
- \+ *lemma* function.antiperiodic.const_mul
- \+ *lemma* function.antiperiodic.const_smul'
- \+ *lemma* function.antiperiodic.const_smul
- \+ *lemma* function.antiperiodic.div
- \+ *lemma* function.antiperiodic.div_inv
- \+ *lemma* function.antiperiodic.eq
- \+ *lemma* function.antiperiodic.int_even_mul_periodic
- \+ *lemma* function.antiperiodic.int_mul_eq_of_eq_zero
- \+ *lemma* function.antiperiodic.int_odd_mul_antiperiodic
- \+ *lemma* function.antiperiodic.mul
- \+ *lemma* function.antiperiodic.mul_const'
- \+ *lemma* function.antiperiodic.mul_const
- \+ *lemma* function.antiperiodic.mul_const_inv
- \+ *lemma* function.antiperiodic.nat_even_mul_periodic
- \+ *lemma* function.antiperiodic.nat_mul_eq_of_eq_zero
- \+ *lemma* function.antiperiodic.nat_odd_mul_antiperiodic
- \+ *lemma* function.antiperiodic.neg
- \+ *lemma* function.antiperiodic.neg_eq
- \+ *lemma* function.antiperiodic.periodic
- \+ *lemma* function.antiperiodic.sub
- \+ *lemma* function.antiperiodic.sub_eq
- \+ *def* function.antiperiodic
- \+ *lemma* function.periodic.add_antiperiod
- \+ *lemma* function.periodic.add_antiperiod_eq
- \+ *lemma* function.periodic.add_period
- \+ *lemma* function.periodic.comp
- \+ *lemma* function.periodic.comp_add_hom
- \+ *lemma* function.periodic.const_inv_mul
- \+ *lemma* function.periodic.const_inv_smul'
- \+ *lemma* function.periodic.const_inv_smul
- \+ *lemma* function.periodic.const_mul
- \+ *lemma* function.periodic.const_smul'
- \+ *lemma* function.periodic.const_smul
- \+ *lemma* function.periodic.div
- \+ *lemma* function.periodic.div_const
- \+ *lemma* function.periodic.eq
- \+ *lemma* function.periodic.gsmul
- \+ *lemma* function.periodic.gsmul_eq
- \+ *lemma* function.periodic.int_mul
- \+ *lemma* function.periodic.int_mul_eq
- \+ *lemma* function.periodic.mul
- \+ *lemma* function.periodic.mul_const'
- \+ *lemma* function.periodic.mul_const
- \+ *lemma* function.periodic.mul_const_inv
- \+ *lemma* function.periodic.nat_mul
- \+ *lemma* function.periodic.nat_mul_eq
- \+ *lemma* function.periodic.neg
- \+ *lemma* function.periodic.neg_eq
- \+ *lemma* function.periodic.neg_nat_mul
- \+ *lemma* function.periodic.neg_nsmul
- \+ *lemma* function.periodic.nsmul
- \+ *lemma* function.periodic.nsmul_eq
- \+ *lemma* function.periodic.sub_antiperiod
- \+ *lemma* function.periodic.sub_antiperiod_eq
- \+ *lemma* function.periodic.sub_eq
- \+ *lemma* function.periodic.sub_gsmul_eq
- \+ *lemma* function.periodic.sub_int_mul_eq
- \+ *lemma* function.periodic.sub_nat_mul_eq
- \+ *lemma* function.periodic.sub_nsmul_eq
- \+ *lemma* function.periodic.sub_period
- \+ *def* function.periodic
- \+ *lemma* function.periodic_with_period_zero



## [2021-06-07 15:40:22](https://github.com/leanprover-community/mathlib/commit/e55d470)
feat(specific_groups/alternating_group): The alternating group on 5 elements is simple ([#7502](https://github.com/leanprover-community/mathlib/pull/7502))
Shows that `is_simple_group (alternating_group (fin 5))`
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.le_sum_of_mem

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.cycle_type_of_card_le_mem_cycle_type_add_two
- \+ *lemma* equiv.perm.is_three_cycle.is_three_cycle_sq
- \+ *lemma* equiv.perm.is_three_cycle.order_of
- \+ *lemma* equiv.perm.le_card_support_of_mem_cycle_type
- \+ *lemma* equiv.perm.mem_cycle_type_iff

Modified src/group_theory/specific_groups/alternating.lean
- \+ *lemma* alternating_group.is_conj_swap_mul_swap_of_cycle_type_two
- \+ *lemma* alternating_group.nontrivial_of_three_le_card
- \+ *lemma* alternating_group.normal_closure_swap_mul_swap_five
- \+ *lemma* equiv.perm.is_three_cycle_sq_of_three_mem_cycle_type_five

Modified src/group_theory/subgroup.lean
- \+ *lemma* is_conj.normal_closure_eq_top_of
- \+ *lemma* monoid_hom.cod_restrict_apply



## [2021-06-07 15:40:20](https://github.com/leanprover-community/mathlib/commit/fa7b5f2)
feat(linear_algebra/quadratic_form): Complex version of Sylvester's law of inertia ([#7416](https://github.com/leanprover-community/mathlib/pull/7416))
Every nondegenerate complex quadratic form is equivalent to a quadratic form corresponding to the sum of squares.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *def* basis.group_smul
- \+ *lemma* basis.group_smul_apply
- \+ *lemma* basis.group_smul_span_eq_top
- \+ *def* basis.is_unit_smul
- \+ *lemma* basis.is_unit_smul_apply
- \+ *def* basis.units_smul
- \+ *lemma* basis.units_smul_apply
- \+ *lemma* basis.units_smul_span_eq_top

Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.group_smul
- \+ *lemma* linear_independent.units_smul

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.basis_repr_apply
- \+ *theorem* quadratic_form.equivalent_sum_squares
- \+ *lemma* quadratic_form.equivalent_weighted_sum_squares_of_nondegenerate'
- \+ *def* quadratic_form.isometry_of_comp_linear_equiv
- \+ *lemma* quadratic_form.isometry_of_is_Ortho_apply
- \+ *def* quadratic_form.weighted_sum_squares
- \+ *lemma* quadratic_form.weighted_sum_squares_apply



## [2021-06-07 15:40:19](https://github.com/leanprover-community/mathlib/commit/ef7aa94)
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
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/big_operators/ring.lean


Modified src/algebra/category/CommRing/basic.lean
- \+ *abbreviation* SemiRing.assoc_ring_hom

Modified src/algebra/char_p/pi.lean


Modified src/algebra/direct_sum_graded.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/opposites.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/ring/basic.lean
- \+/\- *lemma* add_monoid_hom.coe_mul_left
- \+/\- *lemma* add_monoid_hom.coe_mul_right
- \+/\- *def* add_monoid_hom.mul_left
- \+/\- *def* add_monoid_hom.mul_right
- \+/\- *lemma* add_monoid_hom.mul_right_apply
- \+/\- *lemma* boole_mul
- \+/\- *lemma* mul_boole
- \+/\- *lemma* ring_hom.comp_assoc
- \+/\- *def* ring_hom.id
- \+/\- *theorem* ring_hom.injective_iff
- \+/\- *lemma* ring_hom.is_unit_map
- \+/\- *def* ring_hom.mk'
- \+/\- *structure* ring_hom

Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean
- \+/\- *def* ulift.ring_equiv

Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/equiv/ring.lean
- \+/\- *lemma* ring_equiv.coe_ring_hom_inj_iff

Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/multiset/antidiagonal.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* nat.cast_comm
- \+/\- *lemma* nat.cast_commute
- \+/\- *theorem* nat.cast_mul
- \+/\- *def* nat.cast_ring_hom
- \+/\- *lemma* nat.coe_cast_ring_hom

Modified src/deprecated/group.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* hahn_series.emb_domain_mul
- \+/\- *lemma* hahn_series.emb_domain_one
- \+/\- *def* hahn_series.emb_domain_ring_hom
- \+/\- *lemma* hahn_series.emb_domain_ring_hom_C
- \+/\- *lemma* hahn_series.mul_coeff
- \+/\- *lemma* hahn_series.mul_coeff_left'
- \+/\- *lemma* hahn_series.mul_coeff_order_add_order
- \+/\- *lemma* hahn_series.mul_coeff_right'
- \+/\- *lemma* hahn_series.mul_single_coeff_add
- \+/\- *lemma* hahn_series.mul_single_zero_coeff
- \+/\- *lemma* hahn_series.order_one
- \+/\- *lemma* hahn_series.single_mul_coeff_add
- \+/\- *lemma* hahn_series.single_zero_mul_coeff
- \+/\- *theorem* hahn_series.support_mul_subset_add_support
- \+/\- *lemma* hahn_series.support_one

Modified src/ring_theory/subsemiring.lean
- \+/\- *lemma* subsemiring.coe_pow
- \+/\- *lemma* subsemiring.list_prod_mem
- \+/\- *lemma* subsemiring.mem_closure_iff_exists_list
- \+/\- *lemma* subsemiring.multiset_sum_mem
- \+/\- *lemma* subsemiring.pow_mem
- \+/\- *lemma* subsemiring.smul_def
- \+/\- *lemma* subsemiring.sum_mem
- \+/\- *structure* subsemiring

Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/tactic/ring.lean


Modified src/topology/locally_constant/algebra.lean




## [2021-06-07 15:40:18](https://github.com/leanprover-community/mathlib/commit/1eb3ae4)
feat(order/symm_diff): symmetric difference operator ([#6469](https://github.com/leanprover-community/mathlib/pull/6469))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_eq_iff_is_compl
- \+ *lemma* disjoint.disjoint_sdiff_left
- \+ *lemma* disjoint.disjoint_sdiff_right
- \- *theorem* disjoint_sdiff
- \+ *theorem* disjoint_sdiff_self_left
- \+ *theorem* disjoint_sdiff_self_right
- \+ *theorem* eq_compl_iff_is_compl
- \+ *lemma* sdiff_sdiff_self

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.eq_bot_of_le
- \+ *lemma* disjoint.of_disjoint_inf_of_le'
- \+ *lemma* disjoint.of_disjoint_inf_of_le

Added src/order/symm_diff.lean
- \+ *lemma* bot_symm_diff
- \+ *lemma* compl_symm_diff
- \+ *lemma* compl_symm_diff_self
- \+ *lemma* disjoint.disjoint_symm_diff_of_disjoint
- \+ *lemma* disjoint.symm_diff_eq_sup
- \+ *lemma* disjoint_symm_diff_inf
- \+ *lemma* is_compl.symm_diff_eq_top
- \+ *lemma* sdiff_symm_diff'
- \+ *lemma* sdiff_symm_diff
- \+ *lemma* sdiff_symm_diff_self
- \+ *def* symm_diff
- \+ *lemma* symm_diff_assoc
- \+ *lemma* symm_diff_bot
- \+ *lemma* symm_diff_comm
- \+ *lemma* symm_diff_compl_self
- \+ *lemma* symm_diff_def
- \+ *lemma* symm_diff_eq
- \+ *lemma* symm_diff_eq_bot
- \+ *lemma* symm_diff_eq_iff_sdiff_eq
- \+ *lemma* symm_diff_eq_left
- \+ *lemma* symm_diff_eq_right
- \+ *lemma* symm_diff_eq_sup
- \+ *lemma* symm_diff_eq_sup_sdiff_inf
- \+ *lemma* symm_diff_eq_top_iff
- \+ *lemma* symm_diff_eq_xor
- \+ *lemma* symm_diff_le_sup
- \+ *lemma* symm_diff_left_inj
- \+ *lemma* symm_diff_right_inj
- \+ *lemma* symm_diff_sdiff
- \+ *lemma* symm_diff_sdiff_left
- \+ *lemma* symm_diff_sdiff_right
- \+ *lemma* symm_diff_self
- \+ *lemma* symm_diff_symm_diff_left
- \+ *lemma* symm_diff_symm_diff_right'
- \+ *lemma* symm_diff_symm_diff_right
- \+ *lemma* symm_diff_symm_diff_self'
- \+ *lemma* symm_diff_symm_diff_self
- \+ *lemma* symm_diff_top
- \+ *lemma* top_symm_diff



## [2021-06-07 07:44:02](https://github.com/leanprover-community/mathlib/commit/136e0d6)
feat(data/fintype/basic): The cardinality of a set is at most the cardinality of the universe ([#7823](https://github.com/leanprover-community/mathlib/pull/7823))
I think that the hypothesis `[fintype ↥s]` can be avoided with the use of classical logic. E.g.,
`noncomputable instance set_fintype' {α : Type*} [fintype α] (s : set α) : fintype s :=by { classical, exact set_fintype s }`
Would it make sense to add this?
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *def* set_fintype
- \+ *lemma* set_fintype_card_le_univ



## [2021-06-07 07:44:01](https://github.com/leanprover-community/mathlib/commit/4f38062)
feat(algebra/lie/base_change): define extension and restriction of scalars for Lie algebras ([#7808](https://github.com/leanprover-community/mathlib/pull/7808))
#### Estimated changes
Added src/algebra/lie/base_change.lean
- \+ *lemma* lie_algebra.extend_scalars.bracket_tmul

Modified src/algebra/lie/basic.lean




## [2021-06-07 07:44:00](https://github.com/leanprover-community/mathlib/commit/f57f9c8)
feat(ring_theory): define the field/algebra norm ([#7636](https://github.com/leanprover-community/mathlib/pull/7636))
This PR defines the field norm `algebra.norm K L : L →* K`, where `L` is a finite field extension of `K`. In fact, it defines this for any `algebra R S` instance, where `R` and `S` are integral domains. (With a default value of `1` if `S` does not have a finite `R`-basis.)
The approach is to basically copy `ring_theory/trace.lean` and replace `trace` with `det` or `norm` as appropriate.
#### Estimated changes
Added src/ring_theory/norm.lean
- \+ *lemma* algebra.norm_algebra_map
- \+ *lemma* algebra.norm_algebra_map_of_basis
- \+ *lemma* algebra.norm_apply
- \+ *lemma* algebra.norm_eq_matrix_det
- \+ *lemma* algebra.norm_eq_one_of_not_exists_basis



## [2021-06-07 04:52:49](https://github.com/leanprover-community/mathlib/commit/61ca31a)
chore(scripts): update nolints.txt ([#7829](https://github.com/leanprover-community/mathlib/pull/7829))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-06-07 04:52:49](https://github.com/leanprover-community/mathlib/commit/7a21ae1)
chore(algebra/algebra/subalgebra): make inf and top definitionally convenient ([#7812](https://github.com/leanprover-community/mathlib/pull/7812))
This adjusts the galois insertion such that `lemma coe_inf (S T : subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl`.
It also adds lots of trivial `simp` lemmas that were missing about the interactions of various coercions and lattice operations.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* algebra.Inf_to_submodule
- \+ *lemma* algebra.Inf_to_subsemiring
- \+ *lemma* algebra.coe_Inf
- \+ *lemma* algebra.coe_inf
- \+ *lemma* algebra.coe_infi
- \+ *lemma* algebra.coe_top
- \+ *lemma* algebra.inf_to_submodule
- \+ *lemma* algebra.inf_to_subsemiring
- \+ *lemma* algebra.infi_to_submodule
- \+ *lemma* algebra.mem_Inf
- \+ *lemma* algebra.mem_inf
- \+ *lemma* algebra.mem_infi
- \+ *lemma* algebra.mem_top
- \- *theorem* algebra.mem_top
- \+ *lemma* algebra.top_to_submodule
- \- *theorem* algebra.top_to_submodule
- \+ *lemma* algebra.top_to_subsemiring
- \- *theorem* algebra.top_to_subsemiring
- \+ *lemma* subalgebra.coe_to_submodule
- \+ *lemma* subalgebra.coe_to_subring
- \+ *lemma* subalgebra.coe_to_subsemiring
- \+ *lemma* subalgebra.mem_to_subring
- \+ *lemma* subalgebra.mem_to_subsemiring
- \+ *lemma* subalgebra.prod_inf_prod

Modified src/ring_theory/adjoin/basic.lean
- \- *lemma* algebra.coe_inf
- \- *lemma* algebra.prod_inf_prod

Modified src/ring_theory/finiteness.lean


Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-06-07 01:12:38](https://github.com/leanprover-community/mathlib/commit/685289c)
feat(algebra/pointwise): pow_mem_pow ([#7822](https://github.com/leanprover-community/mathlib/pull/7822))
If `a ∈ s` then `a ^ n ∈ s ^ n`.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.pow_mem_pow
- \+ *lemma* set.pow_subset_pow



## [2021-06-07 01:12:37](https://github.com/leanprover-community/mathlib/commit/29d0c63)
feat(measure_theory): add a few integration-related lemmas ([#7821](https://github.com/leanprover-community/mathlib/pull/7821))
These are lemmas I proved while working on [#7164](https://github.com/leanprover-community/mathlib/pull/7164). Some of them are actually not used anymore in that PR because I'm refactoring it, but I thought they would be useful anyway, so here there are.
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_mono_set'
- \+ *lemma* measure_theory.lintegral_mono_set

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_comm
- \+ *lemma* measure_theory.measure.restrict_mono'

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.integrable_on.restrict
- \+ *lemma* measure_theory.set_integral_mono_set



## [2021-06-07 01:12:36](https://github.com/leanprover-community/mathlib/commit/ef7c335)
fix(data/mv_polynomial): add missing decidable arguments ([#7817](https://github.com/leanprover-community/mathlib/pull/7817))
This:
* fixes a doubled instance name, `finsupp.finsupp.decidable_eq`. Note the linter deliberate ignores instances, as they are often autogenerated
* generalizes `finsupp.decidable_le` to all canonically_ordered_monoids
* adds missing `decidable_eq` arguments to `mv_polynomial` and `mv_power_series` lemmas whose statement contains an `if`. These might in future be lintable.
* adds some missing lemmas about `mv_polynomial` to clean up a few proofs.
#### Estimated changes
Modified src/data/finsupp/basic.lean


Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.coeff_C
- \+/\- *lemma* mv_polynomial.coeff_X'
- \+/\- *lemma* mv_polynomial.coeff_X_pow
- \+/\- *lemma* mv_polynomial.coeff_monomial
- \+/\- *lemma* mv_polynomial.coeff_mul_X'
- \+ *lemma* mv_polynomial.coeff_one
- \+ *lemma* mv_polynomial.coeff_zero_C
- \+ *lemma* mv_polynomial.coeff_zero_one
- \+/\- *lemma* mv_polynomial.constant_coeff_monomial

Modified src/data/mv_polynomial/pderiv.lean
- \+/\- *lemma* mv_polynomial.pderiv_X

Modified src/data/polynomial/field_division.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* mv_power_series.coeff_C
- \+/\- *lemma* mv_power_series.coeff_X
- \+/\- *lemma* mv_power_series.coeff_X_pow
- \+/\- *lemma* mv_power_series.coeff_index_single_X
- \+/\- *lemma* mv_power_series.coeff_inv
- \+/\- *lemma* mv_power_series.coeff_inv_aux
- \+/\- *lemma* mv_power_series.coeff_inv_of_unit
- \+/\- *lemma* mv_power_series.coeff_monomial
- \+/\- *lemma* mv_power_series.coeff_one
- \+ *lemma* mv_power_series.monomial_def
- \+/\- *lemma* power_series.coeff_zero_C
- \+/\- *lemma* power_series.coeff_zero_X
- \+/\- *lemma* power_series.order_monomial



## [2021-06-07 01:12:35](https://github.com/leanprover-community/mathlib/commit/90ae36e)
docs(order/order_iso_nat): add module docstring ([#7804](https://github.com/leanprover-community/mathlib/pull/7804))
add module docstring
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+/\- *def* rel_embedding.nat_gt
- \+/\- *def* rel_embedding.nat_lt
- \+/\- *lemma* rel_embedding.nat_lt_apply



## [2021-06-06 19:30:18](https://github.com/leanprover-community/mathlib/commit/4c8a627)
docs(order/directed): add module docstring ([#7779](https://github.com/leanprover-community/mathlib/pull/7779))
add module docstring
#### Estimated changes
Modified src/order/directed.lean
- \+/\- *def* directed
- \+/\- *def* directed_on



## [2021-06-06 03:28:07](https://github.com/leanprover-community/mathlib/commit/e3f897c)
feat(algebra/char_p): characteristic of fraction_ring ([#7703](https://github.com/leanprover-community/mathlib/pull/7703))
Adding the characteristics of a `fraction_ring` for an integral domain.
#### Estimated changes
Added src/algebra/char_p/algebra.lean
- \+ *lemma* char_p_of_injective_algebra_map
- \+ *lemma* char_zero_of_injective_algebra_map

Modified src/algebra/char_p/default.lean




## [2021-06-06 03:28:06](https://github.com/leanprover-community/mathlib/commit/ba2c056)
feat(data/list/nodup): nodup.pairwise_of_forall_ne ([#7587](https://github.com/leanprover-community/mathlib/pull/7587))
#### Estimated changes
Modified src/data/list/nodup.lean
- \+ *lemma* list.nodup.pairwise_of_forall_ne
- \+ *lemma* list.nodup.pairwise_of_set_pairwise_on

Modified src/data/list/pairwise.lean
- \+ *lemma* list.pairwise.set_pairwise_on
- \+ *lemma* list.pairwise_of_reflexive_of_forall_ne
- \+ *lemma* list.pairwise_of_reflexive_on_dupl_of_forall_ne



## [2021-06-05 09:09:15](https://github.com/leanprover-community/mathlib/commit/7021ff9)
feat(linear_algebra/basis): use is_empty instead of ¬nonempty ([#7815](https://github.com/leanprover-community/mathlib/pull/7815))
This removes the need for `basis.of_dim_eq_zero'` and `basis_of_finrank_zero'`, as these special cases are now covered by the unprimed versions and typeclass search.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/basis.lean
- \- *lemma* basis.empty_unique

Modified src/linear_algebra/dimension.lean
- \- *def* basis.of_dim_eq_zero'
- \- *lemma* basis.of_dim_eq_zero'_apply
- \+/\- *def* basis.of_dim_eq_zero
- \+/\- *lemma* basis.of_dim_eq_zero_apply

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/free_module_pid.lean


Modified src/linear_algebra/quadratic_form.lean




## [2021-06-04 19:29:36](https://github.com/leanprover-community/mathlib/commit/a4ae4ad)
chore(order/(bounded,modular)_lattice): avoid classical.some in `is_complemented` instances ([#7814](https://github.com/leanprover-community/mathlib/pull/7814))
There's no reason to use it here.
#### Estimated changes
Modified src/order/bounded_lattice.lean


Modified src/order/modular_lattice.lean




## [2021-06-04 19:29:35](https://github.com/leanprover-community/mathlib/commit/8b5ff9c)
feat(analysis/special_functions/integrals): `integral_log` ([#7732](https://github.com/leanprover-community/mathlib/pull/7732))
The integral of the (real) logarithmic function over the interval `[a, b]`, provided that `0 ∉ interval a b`.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_log
- \+ *lemma* integral_log_of_neg
- \+ *lemma* integral_log_of_pos

Modified test/integration.lean




## [2021-06-04 16:08:36](https://github.com/leanprover-community/mathlib/commit/0b09858)
feat(linear_algebra/basic): add a unique instance for linear_equiv ([#7816](https://github.com/leanprover-community/mathlib/pull/7816))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_zero
- \+ *lemma* linear_equiv.zero_apply
- \+ *lemma* linear_equiv.zero_symm



## [2021-06-04 13:25:42](https://github.com/leanprover-community/mathlib/commit/65e3b04)
feat(linear_algebra/determinant): various `basis.det` lemmas ([#7669](https://github.com/leanprover-community/mathlib/pull/7669))
A selection of results that I needed for computing the value of `basis.det`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.constr_comp
- \+ *lemma* basis.map_equiv

Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_comp
- \+ *lemma* basis.det_map
- \+ *lemma* basis.det_reindex
- \+ *lemma* basis.det_reindex_symm

Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.to_matrix_map
- \+ *lemma* basis.to_matrix_reindex'
- \+ *lemma* basis.to_matrix_reindex



## [2021-06-04 09:53:02](https://github.com/leanprover-community/mathlib/commit/1a62bb4)
feat(linear_algebra): strong rank condition implies rank condition ([#7683](https://github.com/leanprover-community/mathlib/pull/7683))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.congr_fun
- \+ *lemma* finsupp.equiv_fun_on_fintype_single
- \+ *lemma* finsupp.equiv_fun_on_fintype_symm_single

Modified src/linear_algebra/basic.lean
- \+ *lemma* finsupp.linear_equiv_fun_on_fintype_single
- \+ *lemma* finsupp.linear_equiv_fun_on_fintype_symm_single

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean
- \+ *lemma* linear_map.left_inverse_splitting_of_finsupp_surjective
- \+ *lemma* linear_map.left_inverse_splitting_of_fun_on_fintype_surjective
- \+ *def* linear_map.splitting_of_finsupp_surjective
- \+ *lemma* linear_map.splitting_of_finsupp_surjective_injective
- \+ *lemma* linear_map.splitting_of_finsupp_surjective_splits
- \+ *def* linear_map.splitting_of_fun_on_fintype_surjective
- \+ *lemma* linear_map.splitting_of_fun_on_fintype_surjective_injective
- \+ *lemma* linear_map.splitting_of_fun_on_fintype_surjective_splits

Modified src/linear_algebra/invariant_basis_number.lean




## [2021-06-04 03:56:15](https://github.com/leanprover-community/mathlib/commit/be183e2)
chore(data/finset|multiset|finsupp): reduce algebra/ imports ([#7797](https://github.com/leanprover-community/mathlib/pull/7797))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* multiset.abs_sum_le_sum_abs

Modified src/algebra/big_operators/finsupp.lean
- \+ *lemma* finsupp.mul_sum
- \+ *lemma* finsupp.sum_mul

Modified src/algebra/gcd_monoid.lean


Modified src/algebra/group_power/lemmas.lean
- \- *theorem* list.prod_repeat
- \- *theorem* list.sum_repeat
- \- *theorem* nat.nsmul_eq_mul

Modified src/algebra/iterate_hom.lean


Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \- *lemma* finsupp.mul_sum
- \- *lemma* finsupp.sum_mul

Modified src/data/finsupp/lattice.lean


Modified src/data/list/basic.lean
- \+ *theorem* list.prod_repeat
- \+ *theorem* list.sum_repeat

Modified src/data/list/indexes.lean


Modified src/data/list/perm.lean


Modified src/data/multiset/basic.lean
- \- *lemma* multiset.abs_sum_le_sum_abs

Modified src/data/multiset/range.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/basic.lean
- \+ *theorem* nat.nsmul_eq_mul

Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/multilinear.lean




## [2021-06-03 23:23:09](https://github.com/leanprover-community/mathlib/commit/89928bc)
feat(topology): A locally compact Hausdorff space is totally disconnected if and only if it is totally separated ([#7649](https://github.com/leanprover-community/mathlib/pull/7649))
We prove that a locally compact Hausdorff space is totally disconnected if and only if it is totally separated.
#### Estimated changes
Modified src/topology/connected.lean
- \+ *lemma* exists_clopen_of_totally_separated

Modified src/topology/separation.lean
- \+ *lemma* compact_exists_clopen_in_open
- \+ *theorem* compact_t2_tot_disc_iff_tot_sep
- \+ *lemma* loc_compact_Haus_tot_disc_of_zero_dim
- \+ *theorem* loc_compact_t2_tot_disc_iff_tot_sep
- \+ *lemma* tot_sep_of_zero_dim



## [2021-06-03 16:15:32](https://github.com/leanprover-community/mathlib/commit/685adb0)
fix(tactic/lint): allow pattern def ([#7785](https://github.com/leanprover-community/mathlib/pull/7785))
`Prop` sorted declarations are allowed to be `def` if they have the `@[pattern]` attribute
#### Estimated changes
Modified src/tactic/lint/misc.lean


Modified test/lint.lean
- \+ *def* my_exists_intro



## [2021-06-03 16:15:31](https://github.com/leanprover-community/mathlib/commit/fa51468)
feat(tactic/lift): elaborate proof with the expected type ([#7739](https://github.com/leanprover-community/mathlib/pull/7739))
* also slightly refactor the corresponding function a bit
* add some tests
* move all tests to `tests/lift.lean`
#### Estimated changes
Modified src/tactic/lift.lean


Modified test/lift.lean


Modified test/tactics.lean




## [2021-06-03 16:15:30](https://github.com/leanprover-community/mathlib/commit/05f7e8d)
feat(linear_algebra/tensor_product): define `tensor_tensor_tensor_comm` ([#7724](https://github.com/leanprover-community/mathlib/pull/7724))
The intended application is defining the bracket structure when extending the scalars of a Lie algebra.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *def* tensor_product.left_comm
- \+ *lemma* tensor_product.left_comm_symm_tmul
- \+ *lemma* tensor_product.left_comm_tmul
- \+ *def* tensor_product.tensor_tensor_tensor_comm
- \+ *lemma* tensor_product.tensor_tensor_tensor_comm_symm_tmul
- \+ *lemma* tensor_product.tensor_tensor_tensor_comm_tmul



## [2021-06-03 11:07:26](https://github.com/leanprover-community/mathlib/commit/62655a2)
chore(data/dfinsupp): add the simp lemma coe_pre_mk ([#7806](https://github.com/leanprover-community/mathlib/pull/7806))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.coe_pre_mk



## [2021-06-03 11:07:25](https://github.com/leanprover-community/mathlib/commit/2a93644)
chore(src/linear_algebra/free_module): rename file to free_module_pid ([#7805](https://github.com/leanprover-community/mathlib/pull/7805))
In preparation for [#7801](https://github.com/leanprover-community/mathlib/pull/7801)
#### Estimated changes
Modified src/linear_algebra/determinant.lean


Renamed src/linear_algebra/free_module.lean to src/linear_algebra/free_module_pid.lean




## [2021-06-03 11:07:24](https://github.com/leanprover-community/mathlib/commit/fc6f967)
chore(ring_theory/hahn_series): emb_domain_add needs only add_monoid, not semiring ([#7802](https://github.com/leanprover-community/mathlib/pull/7802))
This is my fault, the lemma ended up in the wrong place in [#7737](https://github.com/leanprover-community/mathlib/pull/7737)
#### Estimated changes
Modified src/ring_theory/hahn_series.lean




## [2021-06-03 11:07:23](https://github.com/leanprover-community/mathlib/commit/54d8b94)
chore(logic/basic): add simp lemmas about exist_unique to match those about exists ([#7784](https://github.com/leanprover-community/mathlib/pull/7784))
Adds:
* `exists_unique_const` to match `exists_const` (provable by simp)
* `exists_unique_prop` to match `exists_prop` (provable by simp)
* `exists_unique_prop_of_true` to match `exists_prop_of_true`
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* exists_unique_const
- \+ *theorem* exists_unique_prop
- \+ *theorem* exists_unique_prop_of_true



## [2021-06-03 11:07:21](https://github.com/leanprover-community/mathlib/commit/ef13938)
feat(ring_theory/tensor_product): the base change of a linear map along an algebra ([#4773](https://github.com/leanprover-community/mathlib/pull/4773))
#### Estimated changes
Modified src/algebra/lie/weights.lean


Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* linear_map.ltensor_mul
- \+ *lemma* linear_map.rtensor_mul
- \+ *lemma* tensor_product.curry_injective
- \+/\- *theorem* tensor_product.smul_tmul'
- \+/\- *lemma* tensor_product.smul_tmul
- \+/\- *lemma* tensor_product.tmul_smul

Modified src/ring_theory/tensor_product.lean
- \+ *def* linear_map.base_change
- \+ *lemma* linear_map.base_change_add
- \+ *lemma* linear_map.base_change_eq_ltensor
- \+ *def* linear_map.base_change_hom
- \+ *lemma* linear_map.base_change_neg
- \+ *lemma* linear_map.base_change_smul
- \+ *lemma* linear_map.base_change_sub
- \+ *lemma* linear_map.base_change_tmul
- \+ *lemma* linear_map.base_change_zero
- \+ *def* tensor_product.algebra_tensor_module.assoc
- \+ *def* tensor_product.algebra_tensor_module.curry
- \+ *lemma* tensor_product.algebra_tensor_module.curry_injective
- \+ *theorem* tensor_product.algebra_tensor_module.ext
- \+ *def* tensor_product.algebra_tensor_module.lcurry
- \+ *def* tensor_product.algebra_tensor_module.lift.equiv
- \+ *def* tensor_product.algebra_tensor_module.lift
- \+ *lemma* tensor_product.algebra_tensor_module.lift_tmul
- \+ *def* tensor_product.algebra_tensor_module.mk
- \+ *lemma* tensor_product.algebra_tensor_module.restrict_scalars_curry
- \+ *lemma* tensor_product.algebra_tensor_module.smul_eq_lsmul_rtensor
- \+ *def* tensor_product.algebra_tensor_module.uncurry



## [2021-06-03 07:38:39](https://github.com/leanprover-community/mathlib/commit/b806fd4)
chore(scripts): update nolints.txt ([#7810](https://github.com/leanprover-community/mathlib/pull/7810))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-03 07:38:38](https://github.com/leanprover-community/mathlib/commit/36decf5)
chore(topology/bases): Rename + unprotect some lemmas ([#7809](https://github.com/leanprover-community/mathlib/pull/7809))
@PatrickMassot Unfortunately I saw your comments after [#7753](https://github.com/leanprover-community/mathlib/pull/7753) was already merged, so here is a followup PR with the changes you requested. I also unprotected and renamed `is_topological_basis_pi` and `is_topological_basis_infi` since dot notation will also not work for those.
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* is_topological_basis_infi
- \+ *lemma* is_topological_basis_pi
- \+ *lemma* topological_space.is_topological_basis_opens



## [2021-06-03 07:38:37](https://github.com/leanprover-community/mathlib/commit/8422d8c)
chore(data/padics): move padics to number_theory/ ([#7771](https://github.com/leanprover-community/mathlib/pull/7771))
Per [zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics).
#### Estimated changes
Deleted src/data/padics/default.lean


Added src/number_theory/padics/default.lean


Renamed src/data/padics/hensel.lean to src/number_theory/padics/hensel.lean


Renamed src/data/padics/padic_integers.lean to src/number_theory/padics/padic_integers.lean


Renamed src/data/padics/padic_norm.lean to src/number_theory/padics/padic_norm.lean


Renamed src/data/padics/padic_numbers.lean to src/number_theory/padics/padic_numbers.lean


Renamed src/data/padics/ring_homs.lean to src/number_theory/padics/ring_homs.lean


Modified src/ring_theory/witt_vector/compare.lean




## [2021-06-03 07:38:36](https://github.com/leanprover-community/mathlib/commit/adae1ad)
feat(order/filter/archimedean): in an archimedean linear ordered ring, `at_top` and `at_bot` are countably generated ([#7751](https://github.com/leanprover-community/mathlib/pull/7751))
#### Estimated changes
Modified src/order/filter/archimedean.lean
- \+ *lemma* at_bot_countable_basis_of_archimedean
- \+ *lemma* at_bot_countably_generated
- \+ *lemma* at_top_countable_basis_of_archimedean
- \+ *lemma* at_top_countably_generated_of_archimedean



## [2021-06-03 07:38:35](https://github.com/leanprover-community/mathlib/commit/6d85ff2)
refactor(linear_algebra/finsupp): replace mem_span_iff_total ([#7735](https://github.com/leanprover-community/mathlib/pull/7735))
This PR renames the existing `mem_span_iff_total` to `mem_span_image_iff_total` and the existing `span_eq_map_total` to `span_image_eq_map_total`, and replaces them with slightly simpler lemmas about sets in the module, rather than indexed families.
As usual in the linear algebra library, there is tension between using sets and using indexed families, but as `span` is defined in terms of sets I think the new lemmas merit taking the simpler names.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/fixed.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *theorem* finsupp.mem_span_iff_total
- \+ *theorem* finsupp.mem_span_image_iff_total
- \- *theorem* finsupp.span_eq_map_total
- \+ *theorem* finsupp.span_eq_range_total
- \+ *theorem* finsupp.span_image_eq_map_total

Modified src/linear_algebra/linear_independent.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_basis.lean




## [2021-06-03 07:38:33](https://github.com/leanprover-community/mathlib/commit/6d90d35)
feat(analysis/fourier): monomials on the circle are orthonormal ([#6952](https://github.com/leanprover-community/mathlib/pull/6952))
Make the circle into a measure space, using Haar measure, and prove that the monomials `z ^ n` are orthonormal when considered as elements of L^2 on the circle.
#### Estimated changes
Added src/analysis/fourier.lean
- \+ *def* fourier
- \+ *lemma* fourier_add
- \+ *lemma* fourier_add_half_inv_index
- \+ *lemma* fourier_neg
- \+ *lemma* fourier_zero
- \+ *def* haar_circle
- \+ *lemma* orthonormal_fourier

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.exp_int_mul

Modified src/geometry/manifold/instances/circle.lean
- \+/\- *lemma* coe_div_circle
- \+/\- *lemma* coe_inv_circle
- \+ *lemma* coe_inv_circle_eq_conj
- \+ *lemma* exp_map_circle_apply
- \+ *lemma* nonzero_of_mem_circle
- \+ *lemma* norm_sq_eq_of_mem_circle

Modified src/measure_theory/l2_space.lean
- \+ *lemma* measure_theory.bounded_continuous_function.inner_to_Lp
- \+ *lemma* measure_theory.continuous_map.inner_to_Lp

Modified src/measure_theory/lp_space.lean
- \+ *lemma* bounded_continuous_function.coe_fn_to_Lp
- \+ *lemma* continuous_map.coe_fn_to_Lp
- \+/\- *lemma* continuous_map.to_Lp_norm_le

Modified src/topology/compacts.lean
- \+ *def* topological_space.positive_compacts_univ

Modified src/topology/metric_space/basic.lean
- \+ *lemma* is_compact_sphere



## [2021-06-03 04:58:21](https://github.com/leanprover-community/mathlib/commit/4b31247)
chore(data/*/gcd): move data/*set/gcd to algebra/gcd_monoid/ ([#7800](https://github.com/leanprover-community/mathlib/pull/7800))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).
#### Estimated changes
Renamed src/data/finset/gcd.lean to src/algebra/gcd_monoid/finset.lean


Renamed src/data/multiset/gcd.lean to src/algebra/gcd_monoid/multiset.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/ring_theory/polynomial/content.lean




## [2021-06-03 04:58:20](https://github.com/leanprover-community/mathlib/commit/e591543)
chore(data/zsqrtd): move to number_theory/ ([#7796](https://github.com/leanprover-community/mathlib/pull/7796))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).
#### Estimated changes
Modified src/number_theory/pell.lean


Modified src/number_theory/sum_two_squares.lean


Renamed src/data/zsqrtd/basic.lean to src/number_theory/zsqrtd/basic.lean


Renamed src/data/zsqrtd/gaussian_int.lean to src/number_theory/zsqrtd/gaussian_int.lean


Renamed src/data/zsqrtd/to_real.lean to src/number_theory/zsqrtd/to_real.lean




## [2021-06-03 04:58:19](https://github.com/leanprover-community/mathlib/commit/ce3ca59)
chore(data/fincard): move to set_theory/ ([#7795](https://github.com/leanprover-community/mathlib/pull/7795))
This is about cardinals, so probably belongs in `set_theory/` not `data/`. (It's also a leaf node for now, so easy to move.)
#### Estimated changes
Renamed src/data/fincard.lean to src/set_theory/fincard.lean




## [2021-06-02 23:53:40](https://github.com/leanprover-community/mathlib/commit/d5a635b)
chore(data/hash_map): remove duplicate imports ([#7794](https://github.com/leanprover-community/mathlib/pull/7794))
#### Estimated changes
Modified src/data/hash_map.lean




## [2021-06-02 23:53:39](https://github.com/leanprover-community/mathlib/commit/a36560c)
chore(data/quaternion): move to algebra/ ([#7793](https://github.com/leanprover-community/mathlib/pull/7793))
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).
#### Estimated changes
Renamed src/data/quaternion.lean to src/algebra/quaternion.lean


Modified src/analysis/quaternion.lean




## [2021-06-02 23:53:38](https://github.com/leanprover-community/mathlib/commit/7e3e883)
chore(data/equiv): add docstrings ([#7704](https://github.com/leanprover-community/mathlib/pull/7704))
- add module docstrings
- add def docstrings
- rename `decode2` to `decode₂`
- squash some simps
#### Estimated changes
Modified scripts/nolints.txt


Modified src/computability/halting.lean


Modified src/computability/partrec.lean
- \- *theorem* partrec.bind_decode2_iff
- \+ *theorem* partrec.bind_decode₂_iff

Modified src/computability/primrec.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable/basic.lean
- \+/\- *def* encodable.choose_x
- \- *def* encodable.decode2
- \- *theorem* encodable.decode2_inj
- \- *theorem* encodable.decode2_is_partial_inv
- \+/\- *def* encodable.decode_subtype
- \+/\- *def* encodable.decode_sum
- \+ *def* encodable.decode₂
- \+ *theorem* encodable.decode₂_inj
- \+ *theorem* encodable.decode₂_is_partial_inv
- \+ *theorem* encodable.decode₂_ne_none_iff
- \+/\- *def* encodable.encode'
- \+/\- *def* encodable.encode_subtype
- \+/\- *def* encodable.encode_sum
- \- *theorem* encodable.encodek2
- \+ *theorem* encodable.encodek₂
- \- *theorem* encodable.mem_decode2'
- \- *theorem* encodable.mem_decode2
- \+ *theorem* encodable.mem_decode₂'
- \+ *theorem* encodable.mem_decode₂

Modified src/data/equiv/encodable/lattice.lean
- \- *lemma* encodable.Union_decode2
- \- *lemma* encodable.Union_decode2_cases
- \- *theorem* encodable.Union_decode2_disjoint_on
- \+ *lemma* encodable.Union_decode₂
- \+ *lemma* encodable.Union_decode₂_cases
- \+ *theorem* encodable.Union_decode₂_disjoint_on
- \- *lemma* encodable.supr_decode2
- \+ *lemma* encodable.supr_decode₂

Modified src/data/equiv/list.lean
- \+/\- *def* encodable.fintype_pi

Modified src/data/equiv/nat.lean


Modified src/measure_theory/measurable_space.lean
- \- *lemma* measurable_set.bUnion_decode2
- \+ *lemma* measurable_set.bUnion_decode₂

Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/pi_system.lean


Modified src/topology/algebra/infinite_sum.lean
- \- *theorem* tsum_Union_decode2
- \+ *theorem* tsum_Union_decode₂
- \- *theorem* tsum_supr_decode2
- \+ *theorem* tsum_supr_decode₂



## [2021-06-02 23:53:37](https://github.com/leanprover-community/mathlib/commit/29d0a4e)
feat(tactic/lint): add linter that type-checks statements  ([#7694](https://github.com/leanprover-community/mathlib/pull/7694))
* Add linter that type-checks the statements of all declarations with the default reducibility settings. A statement might not type-check if locally a declaration was made not `@[irreducible]` while globally it is.
* Fix an issue where  `with_one.monoid.to_mul_one_class` did not unify with `with_one.mul_one_class`.
* Fix some proofs in `category_theory.opposites` so that they work while keeping `quiver.opposite` irreducible.
#### Estimated changes
Modified src/algebra/category/Mon/adjunctions.lean


Modified src/algebra/group/with_one.lean


Modified src/category_theory/opposites.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/misc.lean




## [2021-06-02 18:23:20](https://github.com/leanprover-community/mathlib/commit/6e5899d)
feat(measure_theory/integration): add a version of the monotone convergence theorem using `tendsto` ([#7791](https://github.com/leanprover-community/mathlib/pull/7791))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *theorem* measure_theory.lintegral_tendsto_of_tendsto_of_monotone



## [2021-06-02 18:23:19](https://github.com/leanprover-community/mathlib/commit/82bc3ca)
chore(logic/small): reduce imports ([#7777](https://github.com/leanprover-community/mathlib/pull/7777))
By delaying the `fintype` and `encodable` instances for `small`, I think we can now avoid importing `algebra` at all into `logic`.
~~Since some of the `is_empty` lemmas haven't been used yet,~~ I took the liberty of making some arguments explicit, as one was painful to use as is.
#### Estimated changes
Added src/data/equiv/encodable/small.lean


Added src/data/fintype/small.lean


Modified src/group_theory/group_action/defs.lean


Modified src/logic/is_empty.lean


Modified src/logic/small.lean




## [2021-06-02 18:23:18](https://github.com/leanprover-community/mathlib/commit/47dbdac)
chore(data/support): move data/(support|indicator_function) to algebra/ ([#7774](https://github.com/leanprover-community/mathlib/pull/7774))
These don't define any new structures, have not much to do with programming, and are just about basic features of algebraic gadgets, so belong better in `algebra/` than `data/`. 
See discussion of migrating content from `data/` to `algebra/` at [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics](zulip).
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean


Renamed src/data/indicator_function.lean to src/algebra/indicator_function.lean


Renamed src/data/support.lean to src/algebra/support.lean


Modified src/analysis/normed_space/indicator_function.lean


Modified src/data/finsupp/basic.lean


Modified src/data/real/nnreal.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean


Modified src/order/filter/indicator_function.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/basic.lean


Modified src/topology/semicontinuous.lean




## [2021-06-02 13:27:48](https://github.com/leanprover-community/mathlib/commit/173bc4c)
feat(algebra/algebra/subalgebra): add subalgebra.prod ([#7782](https://github.com/leanprover-community/mathlib/pull/7782))
We add a basic API for product of subalgebras.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_prod
- \+ *lemma* subalgebra.mem_prod
- \+ *def* subalgebra.prod
- \+ *lemma* subalgebra.prod_mono
- \+ *lemma* subalgebra.prod_to_submodule
- \+ *lemma* subalgebra.prod_top

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* algebra.adjoint_prod_le
- \+ *lemma* algebra.coe_inf
- \+ *lemma* algebra.prod_inf_prod



## [2021-06-02 10:33:05](https://github.com/leanprover-community/mathlib/commit/b231c92)
doc(data/finsupp/pointwise): update old module doc ([#7770](https://github.com/leanprover-community/mathlib/pull/7770))
#### Estimated changes
Modified src/data/finsupp/pointwise.lean




## [2021-06-02 10:33:04](https://github.com/leanprover-community/mathlib/commit/b91cdb9)
refactor(data/nnreal): rename nnreal.of_real to real.to_nnreal ([#7750](https://github.com/leanprover-community/mathlib/pull/7750))
I am in the middle of a project involving reals, nnreals, ennreals and ereals. There is a maze of coercions and maps between the 4 of them, with completely incoherent naming scheme (do you think that `measurable.nnreal_coe` is speaking of the coercion from `nnreal` to `real` or to `ennreal`, or of a coercion into `nnreal`? currently, it's for the coercion from `nnreal` to `real`, and the analogous lemma for the coercion from `nnreal` to `ennreal` is called `measurable.ennreal_coe`!). I'd like to normalize all this to have something coherent:
* maps are defined from a type to another one, to be able to use dot notation.
* when there are coercions, all lemmas should be formulated in terms of the coercion, and not of the explicit map
* when there is an ambiguity, lemmas on coercions should mention both the source and the target (like in `measurable.coe_nnreal_real`, say). 
The PR is one first step in this direction, renaming `nnreal.of_real` to `real.to_nnreal` (which makes it possible to use dot notation).
#### Estimated changes
Modified archive/imo/imo2008_q4.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/parametric_integral.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/special_functions/pow.lean
- \- *lemma* nnreal.of_real_rpow_of_nonneg
- \+ *lemma* real.to_nnreal_rpow_of_nonneg

Modified src/data/real/conjugate_exponents.lean
- \+/\- *lemma* real.is_conjugate_exponent.inv_add_inv_conj_nnreal
- \+/\- *lemma* real.is_conjugate_exponent.one_lt_nnreal

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_real_mono
- \+ *lemma* ennreal.to_real_strict_mono

Modified src/data/real/nnreal.lean
- \- *lemma* nnreal.coe_of_real
- \- *lemma* nnreal.coe_of_real_le
- \- *lemma* nnreal.le_coe_of_real
- \- *lemma* nnreal.le_of_real_iff_coe_le'
- \- *lemma* nnreal.le_of_real_iff_coe_le
- \- *lemma* nnreal.lt_of_real_iff_coe_lt
- \- *lemma* nnreal.of_real_add
- \- *lemma* nnreal.of_real_add_le
- \- *lemma* nnreal.of_real_add_of_real
- \- *lemma* nnreal.of_real_bit0
- \- *lemma* nnreal.of_real_bit1
- \- *lemma* nnreal.of_real_coe
- \- *lemma* nnreal.of_real_coe_nat
- \- *lemma* nnreal.of_real_div'
- \- *lemma* nnreal.of_real_div
- \- *lemma* nnreal.of_real_eq_zero
- \- *lemma* nnreal.of_real_inv
- \- *lemma* nnreal.of_real_le_iff_le_coe
- \- *lemma* nnreal.of_real_le_of_real
- \- *lemma* nnreal.of_real_le_of_real_iff
- \- *lemma* nnreal.of_real_lt_iff_lt_coe
- \- *lemma* nnreal.of_real_lt_of_real_iff'
- \- *lemma* nnreal.of_real_lt_of_real_iff
- \- *lemma* nnreal.of_real_lt_of_real_iff_of_nonneg
- \- *lemma* nnreal.of_real_mul
- \- *lemma* nnreal.of_real_of_nonpos
- \- *lemma* nnreal.of_real_one
- \- *lemma* nnreal.of_real_pos
- \- *lemma* nnreal.of_real_prod_of_nonneg
- \- *lemma* nnreal.of_real_sum_of_nonneg
- \- *lemma* nnreal.of_real_zero
- \+/\- *lemma* nnreal.sub_def
- \+ *lemma* nnreal.to_nnreal_coe_nat
- \+ *lemma* real.coe_to_nnreal'
- \+ *lemma* real.coe_to_nnreal
- \+ *lemma* real.coe_to_nnreal_le
- \+ *lemma* real.le_coe_to_nnreal
- \+ *lemma* real.le_to_nnreal_iff_coe_le'
- \+ *lemma* real.le_to_nnreal_iff_coe_le
- \+ *lemma* real.lt_to_nnreal_iff_coe_lt
- \+/\- *lemma* real.nnabs_of_nonneg
- \+ *def* real.to_nnreal
- \+ *lemma* real.to_nnreal_add
- \+ *lemma* real.to_nnreal_add_le
- \+ *lemma* real.to_nnreal_add_to_nnreal
- \+ *lemma* real.to_nnreal_bit0
- \+ *lemma* real.to_nnreal_bit1
- \+ *lemma* real.to_nnreal_coe
- \+ *lemma* real.to_nnreal_div'
- \+ *lemma* real.to_nnreal_div
- \+ *lemma* real.to_nnreal_eq_zero
- \+ *lemma* real.to_nnreal_inv
- \+ *lemma* real.to_nnreal_le_iff_le_coe
- \+ *lemma* real.to_nnreal_le_to_nnreal
- \+ *lemma* real.to_nnreal_le_to_nnreal_iff
- \+ *lemma* real.to_nnreal_lt_iff_lt_coe
- \+ *lemma* real.to_nnreal_lt_to_nnreal_iff'
- \+ *lemma* real.to_nnreal_lt_to_nnreal_iff
- \+ *lemma* real.to_nnreal_lt_to_nnreal_iff_of_nonneg
- \+ *lemma* real.to_nnreal_mul
- \+ *lemma* real.to_nnreal_of_nonpos
- \+ *lemma* real.to_nnreal_one
- \+ *lemma* real.to_nnreal_pos
- \+ *lemma* real.to_nnreal_prod_of_nonneg
- \+ *lemma* real.to_nnreal_sum_of_nonneg
- \+ *lemma* real.to_nnreal_zero

Modified src/data/real/sqrt.lean


Modified src/measure_theory/bochner_integration.lean
- \- *lemma* measure_theory.integral_eq_lintegral_max_sub_lintegral_min
- \+ *lemma* measure_theory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part
- \+/\- *lemma* measure_theory.lintegral_coe_eq_integral

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.nnreal_coe
- \+ *lemma* ae_measurable.real_to_nnreal
- \- *lemma* measurable.nnreal_of_real
- \+ *lemma* measurable.real_to_nnreal

Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.has_finite_integral_iff_of_nnreal

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.continuous_of_real

Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* nndist_dist

Modified src/topology/metric_space/lipschitz.lean




## [2021-06-02 04:57:08](https://github.com/leanprover-community/mathlib/commit/832aff8)
chore(scripts): update nolints.txt ([#7798](https://github.com/leanprover-community/mathlib/pull/7798))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-02 04:57:06](https://github.com/leanprover-community/mathlib/commit/cdf6cf0)
feat(topology/sheaves/stalks): Small lemmas about stalk pushforward and stalk map ([#7789](https://github.com/leanprover-community/mathlib/pull/7789))
`Top.presheaf.stalk_pushforward` and `PresheafedSpace.stalk_map` commute with `Top.presheaf.germ`.
#### Estimated changes
Modified src/algebraic_geometry/stalks.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map_germ

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* Top.presheaf.stalk_pushforward_germ



## [2021-06-02 04:57:05](https://github.com/leanprover-community/mathlib/commit/2164107)
refactor(algebraic_geometry/structure_sheaf): Rename Spec.Top to prime_spectrum.Top ([#7786](https://github.com/leanprover-community/mathlib/pull/7786))
Renames `Spec.Top` to `prime_specturm.Top` to free up the namespace for the Spec functor.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean
- \- *def* algebraic_geometry.Spec.Top
- \+/\- *lemma* algebraic_geometry.coe_open_to_localization
- \+/\- *def* algebraic_geometry.const
- \+/\- *lemma* algebraic_geometry.const_apply'
- \+/\- *lemma* algebraic_geometry.const_apply
- \+/\- *lemma* algebraic_geometry.exists_const
- \+/\- *lemma* algebraic_geometry.germ_comp_stalk_to_fiber_ring_hom
- \+/\- *lemma* algebraic_geometry.germ_to_open
- \+/\- *lemma* algebraic_geometry.germ_to_top
- \+/\- *lemma* algebraic_geometry.is_unit_to_stalk
- \+/\- *def* algebraic_geometry.localization_to_stalk
- \+/\- *lemma* algebraic_geometry.localization_to_stalk_mk'
- \+/\- *lemma* algebraic_geometry.localization_to_stalk_of
- \+/\- *lemma* algebraic_geometry.locally_const_basic_open
- \+/\- *lemma* algebraic_geometry.normalize_finite_fraction_representation
- \+/\- *def* algebraic_geometry.open_to_localization
- \+/\- *lemma* algebraic_geometry.open_to_localization_apply
- \+ *def* algebraic_geometry.prime_spectrum.Top
- \+/\- *lemma* algebraic_geometry.res_apply
- \+/\- *def* algebraic_geometry.stalk_iso
- \+/\- *def* algebraic_geometry.stalk_to_fiber_ring_hom
- \+/\- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ'
- \+/\- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_germ
- \+/\- *lemma* algebraic_geometry.stalk_to_fiber_ring_hom_to_stalk
- \+/\- *def* algebraic_geometry.structure_presheaf_in_CommRing
- \+/\- *def* algebraic_geometry.structure_sheaf.is_fraction
- \+/\- *def* algebraic_geometry.structure_sheaf.localizations
- \+/\- *def* algebraic_geometry.structure_sheaf.sections_subring
- \+/\- *def* algebraic_geometry.structure_sheaf
- \+/\- *def* algebraic_geometry.structure_sheaf_in_Type
- \+/\- *def* algebraic_geometry.to_basic_open
- \+/\- *def* algebraic_geometry.to_open
- \+/\- *lemma* algebraic_geometry.to_open_apply
- \+/\- *lemma* algebraic_geometry.to_open_eq_const
- \+/\- *lemma* algebraic_geometry.to_open_germ
- \+/\- *lemma* algebraic_geometry.to_open_res
- \+/\- *def* algebraic_geometry.to_stalk
- \+/\- *lemma* algebraic_geometry.to_stalk_comp_stalk_to_fiber_ring_hom



## [2021-06-02 04:57:04](https://github.com/leanprover-community/mathlib/commit/2fd0ff4)
chore(order/omega_complete_partial_order): clean up references ([#7781](https://github.com/leanprover-community/mathlib/pull/7781))
fix the references rendering by adding them to the .bib
#### Estimated changes
Modified docs/references.bib


Modified src/order/omega_complete_partial_order.lean




## [2021-06-02 04:57:03](https://github.com/leanprover-community/mathlib/commit/5a42f80)
chore(logic/embedding): move some algebra content ([#7776](https://github.com/leanprover-community/mathlib/pull/7776))
This moves a lemma about multiplication by an element in a left/right cancellative semigroup being an embedding out of `logic.embedding`. I didn't find a great home for it, but put it with some content about regular elements, which is at least talking about similar mathematics.
This removes the only direct import from the `logic/` directory to the `algebra/` directory. There are still indirect imports from `logic.small`, which currently brings in `fintype` and hence the whole algebra hierarchy. I'll look at that separately.
#### Estimated changes
Modified src/algebra/regular.lean
- \+ *def* mul_left_embedding
- \+ *def* mul_right_embedding

Modified src/logic/embedding.lean
- \- *def* mul_left_embedding
- \- *def* mul_right_embedding

Modified src/representation_theory/maschke.lean




## [2021-06-02 04:57:02](https://github.com/leanprover-community/mathlib/commit/6c912de)
feat(topology/bases): Topological basis of a product. ([#7753](https://github.com/leanprover-community/mathlib/pull/7753))
Given a family of topological spaces `X_i` with topological bases `T_i`, this constructs the associated basis of the product topology. 
This also includes a construction of the tautological topological basis consisting of all open sets.
This generalizes a lemma from LTE.
#### Estimated changes
Modified src/topology/bases.lean


Modified src/topology/constructions.lean
- \+ *lemma* inducing_infi_to_pi



## [2021-06-02 04:57:00](https://github.com/leanprover-community/mathlib/commit/4884ea5)
feat(order/[conditionally_]complete_lattice): add more intro lemmas for [c][Sup, Inf] and [c][supr, infi] ([#7730](https://github.com/leanprover-community/mathlib/pull/7730))
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* Sup_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* infi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* supr_eq_of_forall_le_of_forall_lt_exists_gt

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cInf_eq_of_forall_ge_of_forall_gt_exists_lt
- \- *theorem* cInf_intro
- \+ *theorem* cSup_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* cSup_eq_of_is_forall_le_of_forall_le_imp_ge
- \- *theorem* cSup_intro'
- \- *theorem* cSup_intro
- \+ *theorem* cinfi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* csupr_eq_of_forall_le_of_forall_lt_exists_gt

Modified src/topology/algebra/ordered/liminf_limsup.lean




## [2021-06-02 04:56:59](https://github.com/leanprover-community/mathlib/commit/6b2c7a7)
feat(data/finset/noncomm_prod): finset products over monoid ([#7567](https://github.com/leanprover-community/mathlib/pull/7567))
The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.
#### Estimated changes
Added src/data/finset/noncomm_prod.lean
- \+ *def* finset.noncomm_prod
- \+ *lemma* finset.noncomm_prod_empty
- \+ *lemma* finset.noncomm_prod_eq_prod
- \+ *lemma* finset.noncomm_prod_insert_of_not_mem'
- \+ *lemma* finset.noncomm_prod_insert_of_not_mem
- \+ *lemma* finset.noncomm_prod_to_finset
- \+ *def* multiset.noncomm_fold
- \+ *lemma* multiset.noncomm_fold_coe
- \+ *lemma* multiset.noncomm_fold_cons
- \+ *lemma* multiset.noncomm_fold_empty
- \+ *lemma* multiset.noncomm_fold_eq_fold
- \+ *def* multiset.noncomm_foldr
- \+ *lemma* multiset.noncomm_foldr_coe
- \+ *lemma* multiset.noncomm_foldr_cons
- \+ *lemma* multiset.noncomm_foldr_empty
- \+ *lemma* multiset.noncomm_foldr_eq_foldr
- \+ *def* multiset.noncomm_prod
- \+ *lemma* multiset.noncomm_prod_coe
- \+ *lemma* multiset.noncomm_prod_cons'
- \+ *lemma* multiset.noncomm_prod_cons
- \+ *lemma* multiset.noncomm_prod_empty
- \+ *lemma* multiset.noncomm_prod_eq_prod



## [2021-06-01 23:18:36](https://github.com/leanprover-community/mathlib/commit/681b9c2)
feat(ring_theory/adjoin/basic): add missing lemmas ([#7780](https://github.com/leanprover-community/mathlib/pull/7780))
Two missing lemmas about `adjoin`.
These are the `subalgebra` versions of `submodule.span_eq_of_le` and `submodule.span_eq`.
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* algebra.adjoin_eq
- \+ *theorem* algebra.adjoin_eq_of_le



## [2021-06-01 23:18:35](https://github.com/leanprover-community/mathlib/commit/76f41e7)
chore(data/nat): split out data/nat/pow ([#7758](https://github.com/leanprover-community/mathlib/pull/7758))
Split lemmas about the power operation on natural numbers into its own file; slightly reduces imports.
#### Estimated changes
Modified src/algebra/group/hom_instances.lean
- \- *lemma* nat.succ_eq_one_add

Modified src/algebra/ordered_ring.lean
- \+ *lemma* nat.succ_eq_one_add

Modified src/computability/language.lean


Modified src/data/int/basic.lean


Modified src/data/nat/basic.lean
- \- *lemma* nat.dvd_of_pow_dvd
- \- *lemma* nat.lt_pow_self
- \- *theorem* nat.lt_size
- \- *theorem* nat.lt_size_self
- \- *lemma* nat.lt_two_pow
- \- *theorem* nat.mod_pow_succ
- \- *lemma* nat.mul_lt_mul_pow_succ
- \- *lemma* nat.not_pos_pow_dvd
- \- *lemma* nat.one_le_pow'
- \- *lemma* nat.one_le_pow
- \- *lemma* nat.one_le_two_pow
- \- *lemma* nat.one_lt_pow'
- \- *lemma* nat.one_lt_pow
- \- *lemma* nat.one_lt_two_pow'
- \- *lemma* nat.one_lt_two_pow
- \- *lemma* nat.one_shiftl
- \- *lemma* nat.pow_div
- \- *lemma* nat.pow_dvd_of_le_of_pow_dvd
- \- *lemma* nat.pow_dvd_pow_iff_le_right'
- \- *lemma* nat.pow_dvd_pow_iff_le_right
- \- *lemma* nat.pow_dvd_pow_iff_pow_le_pow
- \- *lemma* nat.pow_le_iff_le_left
- \- *lemma* nat.pow_le_iff_le_right
- \- *theorem* nat.pow_le_pow_of_le_right
- \- *lemma* nat.pow_left_injective
- \- *lemma* nat.pow_left_strict_mono
- \- *lemma* nat.pow_lt_iff_lt_left
- \- *lemma* nat.pow_lt_iff_lt_right
- \- *theorem* nat.pow_lt_pow_of_lt_left
- \- *theorem* nat.pow_lt_pow_of_lt_right
- \- *lemma* nat.pow_lt_pow_succ
- \- *lemma* nat.pow_right_injective
- \- *lemma* nat.pow_right_strict_mono
- \- *theorem* nat.shiftl'_ne_zero_left
- \- *lemma* nat.shiftl'_tt_eq_mul_pow
- \- *theorem* nat.shiftl'_tt_ne_zero
- \- *lemma* nat.shiftl_eq_mul_pow
- \- *lemma* nat.shiftr_eq_div_pow
- \- *theorem* nat.size_bit0
- \- *theorem* nat.size_bit1
- \- *theorem* nat.size_bit
- \- *theorem* nat.size_eq_zero
- \- *theorem* nat.size_le
- \- *theorem* nat.size_le_size
- \- *theorem* nat.size_one
- \- *theorem* nat.size_pos
- \- *theorem* nat.size_pow
- \- *theorem* nat.size_shiftl'
- \- *theorem* nat.size_shiftl
- \- *theorem* nat.size_zero
- \- *theorem* nat.sq_sub_sq
- \- *lemma* nat.zero_shiftl
- \- *lemma* nat.zero_shiftr
- \- *lemma* strict_mono.nat_pow

Modified src/data/nat/factorial.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/log.lean


Added src/data/nat/pow.lean
- \+ *lemma* nat.dvd_of_pow_dvd
- \+ *lemma* nat.lt_pow_self
- \+ *theorem* nat.lt_size
- \+ *theorem* nat.lt_size_self
- \+ *lemma* nat.lt_two_pow
- \+ *theorem* nat.mod_pow_succ
- \+ *lemma* nat.mul_lt_mul_pow_succ
- \+ *lemma* nat.not_pos_pow_dvd
- \+ *lemma* nat.one_le_pow'
- \+ *lemma* nat.one_le_pow
- \+ *lemma* nat.one_le_two_pow
- \+ *lemma* nat.one_lt_pow'
- \+ *lemma* nat.one_lt_pow
- \+ *lemma* nat.one_lt_two_pow'
- \+ *lemma* nat.one_lt_two_pow
- \+ *lemma* nat.one_shiftl
- \+ *lemma* nat.pow_div
- \+ *lemma* nat.pow_dvd_of_le_of_pow_dvd
- \+ *lemma* nat.pow_dvd_pow_iff_le_right'
- \+ *lemma* nat.pow_dvd_pow_iff_le_right
- \+ *lemma* nat.pow_dvd_pow_iff_pow_le_pow
- \+ *lemma* nat.pow_le_iff_le_left
- \+ *lemma* nat.pow_le_iff_le_right
- \+ *theorem* nat.pow_le_pow_of_le_right
- \+ *lemma* nat.pow_left_injective
- \+ *lemma* nat.pow_left_strict_mono
- \+ *lemma* nat.pow_lt_iff_lt_left
- \+ *lemma* nat.pow_lt_iff_lt_right
- \+ *theorem* nat.pow_lt_pow_of_lt_left
- \+ *theorem* nat.pow_lt_pow_of_lt_right
- \+ *lemma* nat.pow_lt_pow_succ
- \+ *lemma* nat.pow_right_injective
- \+ *lemma* nat.pow_right_strict_mono
- \+ *theorem* nat.shiftl'_ne_zero_left
- \+ *lemma* nat.shiftl'_tt_eq_mul_pow
- \+ *theorem* nat.shiftl'_tt_ne_zero
- \+ *lemma* nat.shiftl_eq_mul_pow
- \+ *lemma* nat.shiftr_eq_div_pow
- \+ *theorem* nat.size_bit0
- \+ *theorem* nat.size_bit1
- \+ *theorem* nat.size_bit
- \+ *theorem* nat.size_eq_zero
- \+ *theorem* nat.size_le
- \+ *theorem* nat.size_le_size
- \+ *theorem* nat.size_one
- \+ *theorem* nat.size_pos
- \+ *theorem* nat.size_pow
- \+ *theorem* nat.size_shiftl'
- \+ *theorem* nat.size_shiftl
- \+ *theorem* nat.size_zero
- \+ *theorem* nat.sq_sub_sq
- \+ *lemma* nat.zero_shiftl
- \+ *lemma* nat.zero_shiftr
- \+ *lemma* strict_mono.nat_pow

Modified src/data/pnat/basic.lean




## [2021-06-01 23:18:35](https://github.com/leanprover-community/mathlib/commit/2689c51)
feat(category_theory/abelian): abelian categories with enough projectives have projective resolutions ([#7488](https://github.com/leanprover-community/mathlib/pull/7488))
#### Estimated changes
Modified src/category_theory/abelian/projective.lean
- \+ *def* category_theory.ProjectiveResolution.of
- \+ *def* category_theory.ProjectiveResolution.of_complex



## [2021-06-01 20:17:20](https://github.com/leanprover-community/mathlib/commit/4e7c6b2)
chore(algebra/associated): weaken some typeclass assumptions ([#7760](https://github.com/leanprover-community/mathlib/pull/7760))
Also golf ne_zero_iff_of_associated a little.
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* associated_of_irreducible_of_dvd
- \+/\- *lemma* dvd_iff_dvd_of_rel_left
- \+/\- *lemma* dvd_iff_dvd_of_rel_right
- \+/\- *lemma* eq_zero_iff_of_associated
- \+/\- *lemma* irreducible_iff_of_associated
- \+/\- *lemma* irreducible_of_associated
- \+/\- *lemma* ne_zero_iff_of_associated



## [2021-06-01 15:40:08](https://github.com/leanprover-community/mathlib/commit/8527efd)
feat(topology/connected): prod.totally_disconnected_space ([#7747](https://github.com/leanprover-community/mathlib/pull/7747))
From LTE.
#### Estimated changes
Modified src/topology/connected.lean




## [2021-06-01 15:40:07](https://github.com/leanprover-community/mathlib/commit/abe146f)
feat(linear_map): to_*_linear_map_injective ([#7746](https://github.com/leanprover-community/mathlib/pull/7746))
From LTE.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* add_monoid_hom.to_int_linear_map_injective
- \+ *lemma* add_monoid_hom.to_nat_linear_map_injective
- \+ *lemma* add_monoid_hom.to_rat_linear_map_injective



## [2021-06-01 12:28:58](https://github.com/leanprover-community/mathlib/commit/88685b0)
feat(linear_algebra/tensor_product): Add is_scalar_tower instances ([#6741](https://github.com/leanprover-community/mathlib/pull/6741))
If either the left- or right-hand type of a tensor product forms a scalar tower, then the tensor product forms the same tower.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean




## [2021-06-01 05:20:12](https://github.com/leanprover-community/mathlib/commit/31ba155)
feat(algebraic_topology/cech_nerve): The Cech nerve is a right adjoint. ([#7716](https://github.com/leanprover-community/mathlib/pull/7716))
Also fixes the namespace in the file `algebraic_topology/cech_nerve.lean`.
This is needed for LTE
#### Estimated changes
Modified src/algebraic_topology/cech_nerve.lean
- \+ *def* category_theory.arrow.augmented_cech_conerve
- \+ *def* category_theory.arrow.cech_conerve
- \+ *def* category_theory.cosimplicial_object.augmented_cech_conerve
- \+ *def* category_theory.cosimplicial_object.cech_conerve
- \+ *abbreviation* category_theory.cosimplicial_object.cech_conerve_adjunction
- \+ *def* category_theory.cosimplicial_object.cech_conerve_equiv
- \+ *def* category_theory.cosimplicial_object.equivalence_left_to_right
- \+ *def* category_theory.cosimplicial_object.equivalence_right_to_left
- \+ *def* category_theory.simplicial_object.augmented_cech_nerve
- \+ *def* category_theory.simplicial_object.cech_nerve
- \+ *abbreviation* category_theory.simplicial_object.cech_nerve_adjunction
- \+ *def* category_theory.simplicial_object.cech_nerve_equiv
- \+ *def* category_theory.simplicial_object.equivalence_left_to_right
- \+ *def* category_theory.simplicial_object.equivalence_right_to_left
- \- *def* simplicial_object.augmented_cech_nerve
- \- *def* simplicial_object.cech_nerve

Modified src/algebraic_topology/simplex_category.lean
- \+ *def* simplex_category.const
- \+ *lemma* simplex_category.const_comp

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.cosimplicial_object.augmented.to_arrow
- \+ *def* category_theory.simplicial_object.augmented.to_arrow



## [2021-06-01 03:25:51](https://github.com/leanprover-community/mathlib/commit/272a930)
chore(scripts): update nolints.txt ([#7775](https://github.com/leanprover-community/mathlib/pull/7775))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-01 01:52:24](https://github.com/leanprover-community/mathlib/commit/4c2bfde)
chore(order/pilex): add docstring ([#7769](https://github.com/leanprover-community/mathlib/pull/7769))
- add module docstring
- extend `ordered_add_comm_group (pilex ι β)` using `to_additive`
#### Estimated changes
Modified src/order/pilex.lean




## [2021-06-01 01:52:23](https://github.com/leanprover-community/mathlib/commit/a8f5cc1)
feat(algebra/homology): i-th component of a chain map as a →+ ([#7743](https://github.com/leanprover-community/mathlib/pull/7743))
From LTE.
#### Estimated changes
Modified src/algebra/homology/additive.lean
- \+ *def* homological_complex.hom.f_add_monoid_hom

