## [2021-06-30 21:21:07](https://github.com/leanprover-community/mathlib/commit/0faf086)
feat(data/int/cast): cast_nat_abs ([#8120](https://github.com/leanprover-community/mathlib/pull/8120))
#### Estimated changes
Modified src/data/int/cast.lean
- \+ *lemma* cast_nat_abs



## [2021-06-30 21:21:06](https://github.com/leanprover-community/mathlib/commit/ad00a02)
feat(topology/vector_bundle): `topological_vector_bundle_core` ([#8089](https://github.com/leanprover-community/mathlib/pull/8089))
Analogous construction to `topological_fiber_bundle_core`. This construction gives a way to construct vector bundles from a structure registering how trivialization changes act on fibers.
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+ *lemma* coord_change_linear_comp
- \+ *lemma* mem_triv_change_source
- \+ *lemma* coe_cord_change
- \+ *lemma* mem_local_triv_source
- \+ *lemma* mem_source_at
- \+ *lemma* local_triv_at_apply
- \+ *lemma* continuous_proj
- \+ *lemma* is_open_map_proj
- \+ *def* to_topological_vector_bundle_core
- \+ *def* index
- \+ *def* base
- \+ *def* fiber
- \+ *def* proj
- \+ *def* triv_change
- \+ *def* local_triv
- \+ *def* local_triv_at



## [2021-06-30 20:39:41](https://github.com/leanprover-community/mathlib/commit/e70093f)
feat(algebra/free_non_unital_non_assoc_algebra): construction of the free non-unital, non-associative algebra on a type `X` with coefficients in a semiring `R` ([#8141](https://github.com/leanprover-community/mathlib/pull/8141))
#### Estimated changes
Modified src/algebra/free_algebra.lean


Created src/algebra/free_non_unital_non_assoc_algebra.lean
- \+ *lemma* lift_symm_apply
- \+ *lemma* of_comp_lift
- \+ *lemma* lift_unique
- \+ *lemma* lift_of_apply
- \+ *lemma* lift_comp_of
- \+ *lemma* hom_ext
- \+ *def* free_non_unital_non_assoc_algebra
- \+ *def* of
- \+ *def* lift



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
- \+ *lemma* lift_aux_apply
- \+ *lemma* lift_aux_apply_I
- \+ *lemma* lift_aux_I
- \+ *lemma* lift_aux_neg_I
- \+ *def* lift_aux



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
- \- *lemma* subsingleton

Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* _root_.alg_hom.subsingleton
- \+ *lemma* _root_.alg_equiv.subsingleton_left
- \+ *lemma* _root_.alg_equiv.subsingleton_right
- \- *lemma* alg_hom.subsingleton
- \- *lemma* alg_equiv.subsingleton_left
- \- *lemma* alg_equiv.subsingleton_right



## [2021-06-30 16:49:12](https://github.com/leanprover-community/mathlib/commit/d420db5)
chore(algebra/algebra): trivial lemmas for alg_equiv ([#8139](https://github.com/leanprover-community/mathlib/pull/8139))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* coe_ring_equiv_injective
- \+ *lemma* coe_alg_hom_injective
- \+ *lemma* coe_alg_hom_of_alg_hom
- \+ *lemma* of_alg_hom_coe_alg_hom
- \+ *lemma* of_alg_hom_symm
- \+ *lemma* of_linear_equiv_symm
- \- *lemma* of_linear_equiv_apply
- \+ *theorem* to_linear_map_injective
- \+ *theorem* to_linear_equiv_injective
- \- *theorem* to_linear_map_inj
- \- *theorem* to_linear_equiv_inj

Modified src/algebra/monoid_algebra.lean


Modified src/ring_theory/tensor_product.lean




## [2021-06-30 13:51:06](https://github.com/leanprover-community/mathlib/commit/9c03c03)
feat(data/set/basic): range_pair_subset ([#8133](https://github.com/leanprover-community/mathlib/pull/8133))
From LTE.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* range_pair_subset



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
- \+ *lemma* map_comp_ι
- \+ *lemma* map_apply_ι
- \+ *lemma* map_id
- \+ *lemma* map_comp_map
- \+ *lemma* equiv_of_isometry_symm
- \+ *lemma* equiv_of_isometry_trans
- \+ *lemma* equiv_of_isometry_refl
- \+ *def* map
- \+ *def* equiv_of_isometry



## [2021-06-30 08:51:20](https://github.com/leanprover-community/mathlib/commit/9a8dcb9)
docs(data/dlist/basic): add module docstring ([#8079](https://github.com/leanprover-community/mathlib/pull/8079))
#### Estimated changes
Modified src/data/dlist/basic.lean




## [2021-06-30 04:28:24](https://github.com/leanprover-community/mathlib/commit/eeeb223)
feat(data/int/basic): int.nat_abs_sub_le ([#8118](https://github.com/leanprover-community/mathlib/pull/8118))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* nat_abs_sub_le



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
- \+/\- *lemma* prod_mk
- \+/\- *lemma* prod_empty
- \+/\- *lemma* sum_const_zero
- \- *lemma* sum_range_succ_comm
- \- *lemma* sum_range_succ
- \- *lemma* eventually_constant_sum
- \- *lemma* sum_range_one
- \- *lemma* eq_of_card_le_one_of_sum_eq
- \- *lemma* sum_range_succ'
- \- *lemma* sum_range_add
- \- *lemma* sum_flip

Modified src/algebra/big_operators/finprod.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/group/to_additive.lean


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
- \+ *lemma* subsingleton

Modified src/ring_theory/power_basis.lean
- \+ *lemma* exists_eq_aeval'
- \+ *lemma* alg_hom_ext
- \+/\- *lemma* constr_pow_mul
- \+/\- *lemma* lift_gen
- \+/\- *lemma* lift_aeval
- \+/\- *lemma* equiv_aeval
- \+/\- *lemma* equiv_gen
- \+/\- *lemma* equiv_symm
- \+/\- *lemma* equiv_map



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
- \+ *theorem* pos_size_of_mem
- \+ *theorem* valid'.map_aux
- \+ *theorem* map.valid
- \+ *theorem* valid'.erase_aux
- \+ *theorem* erase.valid
- \+ *theorem* size_erase_of_mem
- \+ *def* mem
- \+ *def* find
- \+ *def* erase
- \+ *def* map



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
- \- *lemma* ordered_comm_group.mul_lt_mul_left'
- \- *lemma* ordered_comm_group.le_of_mul_le_mul_left
- \- *lemma* ordered_comm_group.lt_of_mul_lt_mul_left



## [2021-06-29 17:54:57](https://github.com/leanprover-community/mathlib/commit/bdf2d81)
feat(topology/continuous_function/stone_weierstrass): complex Stone-Weierstrass ([#8012](https://github.com/leanprover-community/mathlib/pull/8012))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* continuous_abs
- \+ *lemma* continuous_norm_sq

Modified src/topology/algebra/module.lean
- \+ *lemma* submodule.topological_closure_mono
- \+ *lemma* _root_.submodule.topological_closure_map

Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* _root_.continuous_linear_map.comp_left_continuous_bounded_apply

Modified src/topology/continuous_function/compact.lean
- \+ *lemma* linear_isometry_bounded_of_compact_symm_apply
- \+ *lemma* linear_isometry_bounded_of_compact_apply_apply
- \+ *lemma* continuous_linear_map.to_linear_comp_left_continuous_compact
- \+ *lemma* continuous_linear_map.comp_left_continuous_compact_apply

Modified src/topology/continuous_function/stone_weierstrass.lean
- \+ *lemma* mem_conj_invariant_subalgebra
- \+ *lemma* subalgebra.separates_points.complex_to_real
- \+ *theorem* continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
- \+ *def* conj_invariant_subalgebra



## [2021-06-29 16:11:34](https://github.com/leanprover-community/mathlib/commit/4cdfbd2)
feat(data/setoid/partition): indexed partition ([#7910](https://github.com/leanprover-community/mathlib/pull/7910))
from LTE
Note that data/setoid/partition.lean, which already existed before this
PR, is currently not imported anywhere in mathlib. But it is used in LTE
and will be used in the next PR, in relation to locally constant
functions.
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.mk_eq_iff_out
- \+ *lemma* quotient.eq_mk_iff_out

Modified src/data/setoid/basic.lean
- \+/\- *lemma* quotient.eq_rel
- \+ *lemma* comm'
- \+ *lemma* ker_apply_mk_out
- \+ *lemma* ker_apply_mk_out'
- \+ *lemma* comap_rel

Modified src/data/setoid/partition.lean
- \+ *lemma* eqv_class_mem'
- \+ *lemma* exists_mem
- \+ *lemma* Union
- \+ *lemma* disjoint
- \+ *lemma* mem_iff_index_eq
- \+ *lemma* eq
- \+ *lemma* index_some
- \+ *lemma* some_index
- \+ *lemma* proj_eq_iff
- \+ *lemma* proj_some_index
- \+ *lemma* equiv_quotient_index_apply
- \+ *lemma* equiv_quotient_symm_proj_apply
- \+ *lemma* equiv_quotient_index
- \+ *lemma* out_proj
- \+ *lemma* index_out'
- \+ *lemma* proj_out
- \+ *lemma* class_of
- \+ *lemma* proj_fiber
- \+ *def* indexed_partition.mk'
- \+ *def* proj
- \+ *def* equiv_quotient
- \+ *def* out



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
- \+/\- *lemma* map_of_apply

Created src/group_theory/free_abelian_group_finsupp.lean
- \+ *lemma* finsupp.to_free_abelian_group_comp_single_add_hom
- \+ *lemma* free_abelian_group.to_finsupp_comp_to_free_abelian_group
- \+ *lemma* finsupp.to_free_abelian_group_comp_to_finsupp
- \+ *lemma* finsupp.to_free_abelian_group_to_finsupp
- \+ *lemma* to_finsupp_of
- \+ *lemma* to_finsupp_to_free_abelian_group
- \+ *lemma* mem_support_iff
- \+ *lemma* not_mem_support_iff
- \+ *lemma* support_zero
- \+ *lemma* support_of
- \+ *lemma* support_neg
- \+ *lemma* support_gsmul
- \+ *lemma* support_nsmul
- \+ *lemma* support_add
- \+ *def* free_abelian_group.to_finsupp
- \+ *def* finsupp.to_free_abelian_group
- \+ *def* equiv_finsupp
- \+ *def* coeff
- \+ *def* support



## [2021-06-29 13:33:01](https://github.com/leanprover-community/mathlib/commit/68d7d00)
chore(analysis/special_functions/pow): versions of tendsto/continuous_at lemmas for (e)nnreal ([#8113](https://github.com/leanprover-community/mathlib/pull/8113))
We have the full suite of lemmas about `tendsto` and `continuous` for real powers of `real`, but apparently not for `nnreal` or `ennreal`.  I have provided a few, rather painfully -- if there is a better way, golfing is welcome!
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* continuous_rpow_const
- \+ *theorem* tendsto_rpow_at_top

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_nhds_coe_iff
- \+ *lemma* continuous_at_coe_iff



## [2021-06-29 12:50:05](https://github.com/leanprover-community/mathlib/commit/54eccb0)
feat(measure_theory/lp_space): add snorm_eq_lintegral_rpow_nnnorm ([#8115](https://github.com/leanprover-community/mathlib/pull/8115))
Add two lemmas to go from `snorm` to integrals (through `snorm'`). The idea is that `snorm'` should then generally not be used, except in the construction of `snorm`.
#### Estimated changes
Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_eq_lintegral_rpow_nnnorm
- \+ *lemma* snorm_one_eq_lintegral_nnnorm



## [2021-06-29 11:29:09](https://github.com/leanprover-community/mathlib/commit/90d2046)
feat(algebra/monoid_algebra): adjointness for the functor `G ↦ monoid_algebra k G` when `G` carries only `has_mul` ([#7932](https://github.com/leanprover-community/mathlib/pull/7932))
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *lemma* to_mul_action_hom_injective
- \+ *lemma* to_add_monoid_hom_injective
- \+ *lemma* ext_ring
- \+ *lemma* ext_ring_iff

Modified src/algebra/module/linear_map.lean
- \+ *lemma* to_linear_map_eq_coe
- \+ *lemma* coe_to_linear_map
- \+ *lemma* to_linear_map_injective
- \+ *def* to_linear_map

Modified src/algebra/monoid_algebra.lean
- \+ *lemma* non_unital_alg_hom_ext
- \+ *lemma* non_unital_alg_hom_ext'
- \- *lemma* of_apply
- \+ *def* of_magma
- \+/\- *def* of
- \+ *def* lift_magma

Modified src/algebra/non_unital_alg_hom.lean
- \+ *lemma* to_distrib_mul_action_hom_injective
- \+ *lemma* to_mul_hom_injective

Modified src/data/finsupp/basic.lean
- \+ *lemma* distrib_mul_action_hom_ext
- \+ *lemma* distrib_mul_action_hom_ext'
- \+ *def* distrib_mul_action_hom.single



## [2021-06-29 10:46:12](https://github.com/leanprover-community/mathlib/commit/d521b2b)
feat(algebraic_topology/simplex_category): epi and monos in the simplex category ([#8101](https://github.com/leanprover-community/mathlib/pull/8101))
Characterize epimorphisms and monomorphisms in `simplex_category` in terms of the function they represent. Add lemmas about their behavior on length of objects.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* epi_iff_surjective
- \+ *lemma* len_le_of_mono
- \+ *lemma* le_of_mono
- \+ *lemma* len_le_of_epi
- \+ *lemma* le_of_epi
- \+ *theorem* mono_iff_injective



## [2021-06-29 06:55:39](https://github.com/leanprover-community/mathlib/commit/07f1235)
chore(category_theory/opposites): make hom explicit in lemmas ([#8088](https://github.com/leanprover-community/mathlib/pull/8088))
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean


Modified src/category_theory/opposites.lean
- \+/\- *lemma* quiver.hom.unop_op
- \+/\- *lemma* quiver.hom.op_unop



## [2021-06-28 20:13:06](https://github.com/leanprover-community/mathlib/commit/ac156c1)
chore(algebra/algebra/basic): add algebra.right_comm to match left_comm ([#8109](https://github.com/leanprover-community/mathlib/pull/8109))
This also reorders the arguments to `right_comm` to match the order they appear in the LHS of the lemma.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *theorem* left_comm
- \+ *theorem* right_comm



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
- \+/\- *lemma* coe_algebra_map
- \+ *lemma* _root_.alg_hom.map_coe_real_complex
- \+ *lemma* alg_hom_ext



## [2021-06-28 13:54:02](https://github.com/leanprover-community/mathlib/commit/b160ac8)
chore(topology/topological_fiber_bundle): reorganizing the code ([#7989](https://github.com/leanprover-community/mathlib/pull/7989))
Mainly redesigning the `simp` strategy.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+ *lemma* source_inter_preimage_target_inter

Modified src/data/set/basic.lean
- \+/\- *theorem* preimage_const_of_mem
- \+/\- *theorem* preimage_const_of_not_mem

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous.prod.mk

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.is_open_preimage

Modified src/topology/local_homeomorph.lean
- \+ *lemma* source_inter_preimage_target_inter

Modified src/topology/order.lean
- \+ *lemma* is_open_induced_iff'
- \+ *lemma* le_induced_generate_from

Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* coe_fst
- \+ *lemma* coe_snd_map_apply
- \+ *lemma* coe_snd_map_smul
- \+/\- *lemma* mem_local_triv'_source
- \+/\- *lemma* mem_local_triv'_target
- \+/\- *lemma* local_triv'_apply
- \+/\- *lemma* local_triv'_symm_apply
- \+ *lemma* local_triv'_coe
- \+ *lemma* local_triv'_source
- \+ *lemma* local_triv'_target
- \+/\- *lemma* mem_local_triv_source
- \+/\- *lemma* mem_local_triv_target
- \+/\- *lemma* local_triv_apply
- \+/\- *lemma* local_triv_symm_fst
- \+ *lemma* local_triv_at_ext_def
- \+ *lemma* local_triv_coe
- \+ *lemma* local_triv_source
- \+ *lemma* local_triv_target
- \+ *lemma* local_triv_symm
- \+ *lemma* base_set_at
- \+ *lemma* local_triv_ext_apply
- \+ *lemma* local_triv_ext_symm_apply
- \+ *lemma* mem_local_triv_ext_source
- \+ *lemma* mem_local_triv_ext_target
- \+ *lemma* local_triv_ext_symm_fst
- \+ *lemma* local_triv_at_apply
- \+ *lemma* mem_local_triv_at_ext_base_set
- \+ *lemma* continuous_total_space_mk
- \- *lemma* mem_local_triv_at_source
- \- *lemma* local_triv_at_fst
- \- *lemma* local_triv_at_symm_fst
- \- *lemma* local_triv_at_ext_to_local_homeomorph
- \+ *def* total_space_mk
- \+/\- *def* local_triv_at_ext
- \- *def* local_triv_at

Modified src/topology/vector_bundle.lean
- \+ *lemma* trivialization.coe_coe
- \+ *lemma* trivialization.coe_fst



## [2021-06-28 12:36:08](https://github.com/leanprover-community/mathlib/commit/f7c1e5f)
feat(algebra/lie/nilpotent): basic lemmas about nilpotency for Lie subalgebras of associative algebras ([#8090](https://github.com/leanprover-community/mathlib/pull/8090))
The main lemma is: `lie_algebra.is_nilpotent_ad_of_is_nilpotent` which is the first step in proving Engel's theorem.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* commute_lmul_left_right
- \+ *lemma* lmul_left_zero_eq_zero
- \+ *lemma* lmul_right_zero_eq_zero
- \+ *lemma* lmul_left_eq_zero_iff
- \+ *lemma* lmul_right_eq_zero_iff
- \+ *lemma* pow_lmul_left
- \+ *lemma* pow_lmul_right

Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_algebra.ad_nilpotent_of_nilpotent
- \+ *lemma* lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad
- \+ *lemma* lie_algebra.is_nilpotent_ad_of_is_nilpotent

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_algebra.ad_eq_lmul_left_sub_lmul_right
- \+ *lemma* lie_subalgebra.ad_comp_incl_eq

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule_pow_eq_zero_of_pow_eq_zero

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* is_nilpotent_lmul_left_iff
- \+ *lemma* is_nilpotent_lmul_right_iff



## [2021-06-28 11:54:29](https://github.com/leanprover-community/mathlib/commit/81183ea)
feat(geometry/manifold): `derivation_bundle` ([#7708](https://github.com/leanprover-community/mathlib/pull/7708))
In this PR we define the `derivation_bundle`. Note that this definition is purely algebraic and that the whole geometry/analysis is contained in the algebra structure of smooth global functions on the manifold.
I believe everything runs smoothly and elegantly and that most proofs can be naturally done by `rfl`. To anticipate some discussions that already arose on Zulip about 9 months ago, note that the content of these files is purely algebraic and that there is no intention whatsoever to replace the current tangent bundle. I prefer this definition to the one given through the adjoint representation, because algebra is more easily formalized and simp can solve most proofs with this definition. However, in the future, there will be also the adjoint representation for sure.
#### Estimated changes
Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_apply

Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *def* eval_ring_hom

Created src/geometry/manifold/derivation_bundle.lean
- \+ *lemma* smul_def
- \+ *lemma* eval_at_apply
- \+ *lemma* apply_fdifferential
- \+ *lemma* fdifferential_comp
- \+ *def* pointed_smooth_map
- \+ *def* eval
- \+ *def* point_derivation
- \+ *def* smooth_function.eval_at
- \+ *def* eval_at
- \+ *def* fdifferential_map
- \+ *def* fdifferential



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
- \+/\- *theorem* coe_injective



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




## [2021-06-28 04:53:22](https://github.com/leanprover-community/mathlib/commit/7b253dd)
feat(group_theory/subgroup): lemmas for normal subgroups of subgroups ([#7271](https://github.com/leanprover-community/mathlib/pull/7271))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* comap_sup_comap_le
- \+ *lemma* supr_comap_le
- \+ *lemma* map_inf_le
- \+ *lemma* map_inf_eq
- \+ *lemma* coe_subgroup_of
- \+ *lemma* mem_subgroup_of
- \+ *lemma* subgroup_of_map_subtype
- \+ *lemma* comap_bot
- \+/\- *lemma* range_restrict_ker
- \+/\- *lemma* map_le_range
- \+/\- *lemma* ker_le_comap
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_comap_eq
- \+/\- *lemma* comap_map_eq
- \+/\- *lemma* map_comap_eq_self
- \+/\- *lemma* map_comap_eq_self_of_surjective
- \+/\- *lemma* comap_injective
- \+/\- *lemma* comap_map_eq_self
- \+/\- *lemma* comap_map_eq_self_of_injective
- \+/\- *lemma* map_injective
- \+/\- *lemma* map_eq_comap_of_inverse
- \+ *lemma* map_injective_of_ker_le
- \+ *lemma* comap_sup_eq
- \+ *lemma* mul_inf_assoc
- \+ *lemma* inf_mul_assoc
- \+ *lemma* normal_subgroup_of_iff
- \+ *lemma* inf_subgroup_of_inf_normal_of_right
- \+ *lemma* inf_subgroup_of_inf_normal_of_left
- \+ *lemma* subgroup_of_sup
- \+ *lemma* subgroup_normal.mem_comm
- \+ *def* subgroup_of



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
- \+ *lemma* card_embedding_eq_of_unique
- \+ *lemma* card_embedding_eq_of_infinite
- \- *lemma* card_embedding_of_unique
- \- *lemma* card_embedding_eq_infinite
- \+ *theorem* card_embedding_eq
- \- *theorem* card_embedding
- \- *theorem* card_embedding_eq_zero
- \- *theorem* card_embedding_eq_if

Modified src/data/nat/choose/basic.lean
- \+ *lemma* asc_factorial_eq_factorial_mul_choose
- \+ *lemma* factorial_dvd_asc_factorial
- \+ *lemma* choose_eq_asc_factorial_div_factorial
- \+ *lemma* desc_factorial_eq_factorial_mul_choose
- \+ *lemma* factorial_dvd_desc_factorial
- \+ *lemma* choose_eq_desc_factorial_div_factorial
- \- *lemma* desc_fac_eq_factorial_mul_choose
- \- *lemma* factorial_dvd_desc_fac
- \- *lemma* choose_eq_desc_fac_div_factorial

Modified src/data/nat/factorial.lean
- \+/\- *lemma* factorial_lt
- \+/\- *lemma* factorial_inj
- \+ *lemma* asc_factorial_zero
- \+ *lemma* zero_asc_factorial
- \+ *lemma* asc_factorial_succ
- \+ *lemma* succ_asc_factorial
- \+ *lemma* asc_factorial_eq_div
- \+ *lemma* asc_factorial_of_sub
- \+ *lemma* pow_succ_le_asc_factorial
- \+ *lemma* pow_lt_asc_factorial'
- \+ *lemma* pow_lt_asc_factorial
- \+ *lemma* asc_factorial_le_pow_add
- \+ *lemma* asc_factorial_lt_pow_add
- \+ *lemma* asc_factorial_pos
- \+ *lemma* desc_factorial_zero
- \+ *lemma* desc_factorial_succ
- \+ *lemma* zero_desc_factorial_succ
- \+ *lemma* desc_factorial_one
- \+ *lemma* succ_desc_factorial_succ
- \+ *lemma* succ_desc_factorial
- \+ *lemma* desc_factorial_self
- \+ *lemma* desc_factorial_eq_zero_iff_lt
- \+ *lemma* add_desc_factorial_eq_asc_factorial
- \+ *lemma* desc_factorial_eq_div
- \+ *lemma* pow_sub_le_desc_factorial
- \+ *lemma* pow_sub_lt_desc_factorial'
- \+ *lemma* pow_sub_lt_desc_factorial
- \+ *lemma* desc_factorial_le_pow
- \+ *lemma* desc_factorial_lt_pow
- \- *lemma* desc_fac_zero
- \- *lemma* zero_desc_fac
- \- *lemma* desc_fac_succ
- \- *lemma* succ_desc_fac
- \- *lemma* desc_fac_eq_div
- \- *lemma* desc_fac_of_sub
- \+ *theorem* factorial_mul_asc_factorial
- \+ *theorem* factorial_mul_desc_factorial
- \- *theorem* factorial_mul_desc_fac
- \+/\- *def* factorial
- \+ *def* asc_factorial
- \+ *def* desc_factorial
- \- *def* desc_fac

Modified src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* pochhammer_nat_eq_asc_factorial
- \- *lemma* pochhammer_nat_eq_desc_fac



## [2021-06-27 13:01:13](https://github.com/leanprover-community/mathlib/commit/2dcc307)
feat(category_theory/limits): morphism to terminal is split mono ([#8084](https://github.com/leanprover-community/mathlib/pull/8084))
A generalisation of existing results: we already have an instance `split_mono` to `mono` so this is strictly more general.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* is_terminal.split_mono_from
- \+ *def* is_initial.split_epi_to



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
- \+ *lemma* hom_zero_zero

Modified src/algebraic_topology/simplicial_object.lean
- \+ *lemma* augment_hom_zero
- \+ *def* augment



## [2021-06-26 09:25:11](https://github.com/leanprover-community/mathlib/commit/4630067)
chore(data/set/intervals): syntax clean up ([#8087](https://github.com/leanprover-community/mathlib/pull/8087))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* Ioi_subset_Ici_self
- \+/\- *lemma* Iio_subset_Iic_self



## [2021-06-25 21:10:33](https://github.com/leanprover-community/mathlib/commit/68ec06c)
chore(analysis/analytic/composition): remove one `have` ([#8083](https://github.com/leanprover-community/mathlib/pull/8083))
A `have` in a proof is not necessary.
#### Estimated changes
Modified src/analysis/analytic/composition.lean




## [2021-06-25 20:31:41](https://github.com/leanprover-community/mathlib/commit/92a7171)
feat(measure_theory/interval_integral): generalize `add_adjacent_intervals` to n-ary sum ([#8050](https://github.com/leanprover-community/mathlib/pull/8050))
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* trans_iterate
- \+ *lemma* sum_integral_adjacent_intervals



## [2021-06-25 18:48:54](https://github.com/leanprover-community/mathlib/commit/6666ba2)
fix(real/sign): make `real.sign 0 = 0` to match `int.sign 0` ([#8080](https://github.com/leanprover-community/mathlib/pull/8080))
Previously `sign 0 = 1` which is quite an unusual definition. This definition brings things in line with `int.sign`, and include a proof of this fact.
A future refactor could probably introduce a sign for all rings with a partial order
#### Estimated changes
Modified src/data/real/sign.lean
- \+ *lemma* sign_of_pos
- \+/\- *lemma* sign_zero
- \+/\- *lemma* sign_apply_eq
- \+ *lemma* sign_apply_eq_of_ne_zero
- \+ *lemma* sign_eq_zero_iff
- \+ *lemma* sign_int_cast
- \+/\- *lemma* sign_neg
- \- *lemma* sign_of_not_neg
- \- *lemma* sign_of_zero_le
- \+/\- *def* sign

Modified src/linear_algebra/quadratic_form.lean




## [2021-06-25 18:48:53](https://github.com/leanprover-community/mathlib/commit/a7faaf5)
docs(data/list/chain): add module docstring ([#8041](https://github.com/leanprover-community/mathlib/pull/8041))
#### Estimated changes
Modified src/data/list/chain.lean
- \+/\- *theorem* chain_split
- \+/\- *theorem* chain_of_pairwise
- \+/\- *theorem* chain'_split



## [2021-06-25 18:48:52](https://github.com/leanprover-community/mathlib/commit/cf4a2df)
docs(data/list/range): add module docstring ([#8026](https://github.com/leanprover-community/mathlib/pull/8026))
#### Estimated changes
Modified src/data/list/range.lean




## [2021-06-25 17:09:01](https://github.com/leanprover-community/mathlib/commit/9cc44ba)
feat(ring_theory/nilpotent): basic results about nilpotency in associative rings ([#8055](https://github.com/leanprover-community/mathlib/pull/8055))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_of_le

Created src/ring_theory/nilpotent.lean
- \+ *lemma* is_nilpotent.zero
- \+ *lemma* is_nilpotent.neg
- \+ *lemma* is_nilpotent_neg_iff
- \+ *lemma* is_nilpotent.eq_zero
- \+ *lemma* is_nilpotent_iff_eq_zero
- \+ *lemma* is_nilpotent_add
- \+ *lemma* is_nilpotent_mul_left
- \+ *lemma* is_nilpotent_mul_right
- \+ *lemma* is_nilpotent_sub
- \+ *def* is_nilpotent



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
- \+ *lemma* coe_conj_ae
- \- *lemma* coe_conj_alg_equiv
- \+ *def* conj_ae
- \- *def* conj_alg_equiv

Modified src/analysis/complex/basic.lean
- \+ *lemma* conj_lie_apply
- \+/\- *lemma* isometry_conj
- \+/\- *lemma* continuous_conj
- \+ *lemma* conj_cle_coe
- \+ *lemma* conj_cle_apply
- \+ *lemma* conj_cle_norm
- \+/\- *lemma* continuous_of_real
- \+/\- *lemma* of_real_clm_coe
- \+/\- *lemma* of_real_clm_apply
- \- *lemma* conj_li_apply
- \- *lemma* conj_clm_coe
- \- *lemma* conj_clm_apply
- \- *lemma* conj_clm_norm
- \+ *def* conj_lie
- \+ *def* conj_cle
- \+/\- *def* of_real_li
- \+/\- *def* of_real_clm
- \- *def* conj_li
- \- *def* conj_clm

Modified src/analysis/complex/circle.lean


Modified src/analysis/complex/isometry.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* conj_ae_coe
- \+ *lemma* conj_lie_apply
- \+ *lemma* conj_cle_coe
- \+ *lemma* conj_cle_apply
- \+ *lemma* conj_cle_norm
- \+/\- *lemma* continuous_conj
- \+ *lemma* of_real_am_coe
- \+/\- *lemma* of_real_li_apply
- \+/\- *lemma* of_real_clm_coe
- \- *lemma* conj_lm_coe
- \- *lemma* conj_li_apply
- \- *lemma* conj_clm_coe
- \- *lemma* conj_clm_apply
- \- *lemma* conj_clm_norm
- \- *lemma* of_real_lm_coe

Modified src/data/complex/module.lean
- \+ *lemma* of_real_am_coe
- \+ *lemma* conj_ae_coe
- \- *lemma* of_real_lm_coe
- \- *lemma* conj_lm_coe
- \+ *def* of_real_am
- \+ *def* conj_ae
- \- *def* conj_alg_equiv
- \- *def* of_real_lm
- \- *def* conj_lm

Modified src/field_theory/polynomial_galois_group.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/set_integral.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* to_linear_map_eq_coe



## [2021-06-25 09:21:01](https://github.com/leanprover-community/mathlib/commit/c515346)
feat(ring_theory/power_basis): map a power basis through an alg_equiv ([#8039](https://github.com/leanprover-community/mathlib/pull/8039))
If `A` is equivalent to `A'` as an `R`-algebra and `A` has a power basis, then `A'` also has a power basis. Included are the relevant `simp` lemmas.
This needs a bit of tweaking to `basis.map` and `alg_equiv.to_linear_equiv` for getting more useful `simp` lemmas.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* to_linear_equiv_refl
- \+ *lemma* to_linear_equiv_symm
- \+ *lemma* to_linear_equiv_trans
- \- *lemma* to_linear_equiv_apply
- \+/\- *def* to_linear_equiv

Modified src/linear_algebra/basis.lean


Modified src/ring_theory/power_basis.lean
- \+ *lemma* minpoly_gen_map
- \+ *lemma* equiv_map



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
- \+ *lemma* minor_map



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
- \+ *def* Pi_congr_left'
- \+ *def* Pi_congr_left

Modified src/ring_theory/noetherian.lean




## [2021-06-24 16:50:00](https://github.com/leanprover-community/mathlib/commit/25d8aac)
chore(field_theory): turn `intermediate_field.subalgebra.equiv_of_eq`  into `intermediate_field.equiv_of_eq` ([#8069](https://github.com/leanprover-community/mathlib/pull/8069))
I was looking for `intermediate_field.equiv_of_eq`. There was a definition of `subalgebra.equiv_of_eq` in the `intermediate_field` namespace which is equal to the original `subalgebra.equiv_of_eq` definition. Meanwhile, there was no `intermediate_field.equiv_of_eq`. So I decided to turn the duplicate into what I think was intended. (As a bonus, I added the `simp` lemmas from `subalgebra.equiv_of_eq`.)
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* equiv_of_eq_symm
- \+ *lemma* equiv_of_eq_rfl
- \+ *lemma* equiv_of_eq_trans
- \+ *def* equiv_of_eq
- \- *def* subalgebra.equiv_of_eq



## [2021-06-24 15:14:30](https://github.com/leanprover-community/mathlib/commit/db84f2b)
feat(data/polynomial): `aeval_alg_equiv`, like `aeval_alg_hom` ([#8038](https://github.com/leanprover-community/mathlib/pull/8038))
This PR copies `polynomial.aeval_alg_hom` and `aeval_alg_hom_apply` to `aeval_alg_equiv(_apply)`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *theorem* aeval_alg_equiv
- \+ *theorem* aeval_alg_equiv_apply



## [2021-06-24 15:14:29](https://github.com/leanprover-community/mathlib/commit/2a15520)
chore(data/polynomial): generalize `aeval_eq_sum_range` to `comm_semiring` ([#8037](https://github.com/leanprover-community/mathlib/pull/8037))
This pair of lemmas did not need any `comm_ring` assumptions, so I put them in a new section with weaker typeclass assumptions.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* aeval_eq_sum_range
- \+/\- *lemma* aeval_eq_sum_range'



## [2021-06-24 15:14:28](https://github.com/leanprover-community/mathlib/commit/3937c1b)
docs(data/list/pairwise): add module docstring ([#8025](https://github.com/leanprover-community/mathlib/pull/8025))
#### Estimated changes
Modified src/data/list/pairwise.lean




## [2021-06-24 15:14:27](https://github.com/leanprover-community/mathlib/commit/520e79d)
feat(analysis/convex/exposed): introduce exposed sets ([#7928](https://github.com/leanprover-community/mathlib/pull/7928))
introduce exposed sets
#### Estimated changes
Created src/analysis/convex/exposed.lean
- \+ *lemma* continuous_linear_map.to_exposed.is_exposed
- \+ *lemma* is_exposed_empty
- \+ *lemma* refl
- \+ *lemma* antisymm
- \+ *lemma* eq_inter_halfspace
- \+ *lemma* inter
- \+ *lemma* sInter
- \+ *lemma* inter_left
- \+ *lemma* inter_right
- \+ *lemma* is_closed
- \+ *lemma* is_compact
- \+ *lemma* exposed_point_def
- \+ *lemma* mem_exposed_points_iff_exposed_singleton
- \+ *lemma* exposed_points_subset
- \+ *lemma* exposed_points_subset_extreme_points
- \+ *lemma* exposed_points_empty
- \+ *def* is_exposed
- \+ *def* continuous_linear_map.to_exposed
- \+ *def* set.exposed_points

Modified src/analysis/convex/extreme.lean




## [2021-06-24 15:14:26](https://github.com/leanprover-community/mathlib/commit/4801fa6)
feat(measure_theory): the Vitali-Caratheodory theorem ([#7766](https://github.com/leanprover-community/mathlib/pull/7766))
This PR proves the Vitali-Carathéodory theorem, asserting that a measurable function can be closely approximated from above by a lower semicontinuous function, and from below by an upper semicontinuous function. 
This is the main ingredient in the proof of the general version of the fundamental theorem of calculus (when `f'` is just integrable, but not continuous).
#### Estimated changes
Created src/measure_theory/vitali_caratheodory.lean
- \+ *lemma* simple_func.exists_le_lower_semicontinuous_lintegral_ge
- \+ *lemma* exists_le_lower_semicontinuous_lintegral_ge
- \+ *lemma* exists_lt_lower_semicontinuous_lintegral_ge
- \+ *lemma* exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable
- \+ *lemma* exists_lt_lower_semicontinuous_integral_gt_nnreal
- \+ *lemma* simple_func.exists_upper_semicontinuous_le_lintegral_le
- \+ *lemma* exists_upper_semicontinuous_le_lintegral_le
- \+ *lemma* exists_upper_semicontinuous_le_integral_le
- \+ *lemma* exists_lt_lower_semicontinuous_integral_lt
- \+ *lemma* exists_upper_semicontinuous_lt_integral_gt



## [2021-06-24 13:55:29](https://github.com/leanprover-community/mathlib/commit/b9bf921)
chore(linear_algebra): switch to named constructors for linear_map ([#8059](https://github.com/leanprover-community/mathlib/pull/8059))
This makes some ideas I have for future refactors easier, and generally makes things less fragile to changes such as additional fields or reordering of fields.
The extra verbosity is not really significant.
This conversion is not exhaustive, there may be anonymous constructors elsewhere that I've missed.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *theorem* is_linear
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *def* comp
- \+/\- *def* mk'

Modified src/analysis/normed_space/operator_norm.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* mkq

Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/linear_algebra/pi.lean


Modified src/linear_algebra/prod.lean
- \+/\- *def* fst
- \+/\- *def* snd

Modified src/linear_algebra/tensor_product.lean


Modified src/ring_theory/hahn_series.lean


Modified src/topology/algebra/module.lean
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply

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
- \+/\- *lemma* map_mul
- \+ *lemma* map_smul
- \+/\- *lemma* coe_map_ring_hom
- \+/\- *def* map_ring_hom

Modified src/ring_theory/polynomial_algebra.lean
- \+ *lemma* to_fun_bilinear_apply_eq_sum
- \+ *lemma* to_fun_linear_tmul_apply
- \+/\- *def* to_fun_bilinear
- \- *def* to_fun
- \- *def* to_fun_linear_right



## [2021-06-24 11:32:46](https://github.com/leanprover-community/mathlib/commit/5352639)
feat(data/matrix/basic.lean) : added map_scalar and linear_map.map_matrix ([#8061](https://github.com/leanprover-community/mathlib/pull/8061))
Added two lemmas (`map_scalar` and `linear_map.map_matrix_apply`) and a definition (`linear_map.map_matrix`) showing that a map between coefficients induces the same type of map between matrices with those coefficients.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* map_smul
- \+ *def* linear_map.map_matrix



## [2021-06-24 09:57:32](https://github.com/leanprover-community/mathlib/commit/5bd649f)
feat(analysis/liouville/liouville_constant): transcendental Liouville numbers exist! ([#8020](https://github.com/leanprover-community/mathlib/pull/8020))
The final (hopefully!) PR in the Liouville series: there are a couple of results and the proof that Liouville numbers are transcendental.
#### Estimated changes
Modified src/analysis/liouville/liouville_constant.lean
- \+/\- *lemma* liouville_number_tail_pos
- \+/\- *lemma* liouville_number_eq_initial_terms_add_tail
- \+/\- *lemma* tsum_one_div_pow_factorial_lt
- \+/\- *lemma* aux_calc
- \+ *lemma* liouville_number_rat_initial_terms
- \+ *lemma* is_transcendental
- \+ *theorem* is_liouville



## [2021-06-24 09:57:31](https://github.com/leanprover-community/mathlib/commit/f7f12bc)
feat(data/nat/prime): norm_num plugin for factors ([#8009](https://github.com/leanprover-community/mathlib/pull/8009))
Implements a `norm_num` plugin to evaluate terms like `nat.factors 231 = [3, 7, 11]`.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* factors_chain
- \+ *lemma* factors_chain_2
- \+ *lemma* factors_chain'
- \+ *lemma* factors_sorted
- \+ *lemma* factors_helper_nil
- \+ *lemma* factors_helper_cons'
- \+ *lemma* factors_helper_cons
- \+ *lemma* factors_helper_sn
- \+ *lemma* factors_helper_same
- \+ *lemma* factors_helper_same_sn
- \+ *lemma* factors_helper_end
- \+ *def* factors_helper

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
- \+ *lemma* coe_coe
- \+ *lemma* coe_fst
- \+ *lemma* mem_source
- \+ *lemma* coe_fst'
- \+ *lemma* mk_proj_snd
- \+ *lemma* mk_proj_snd'
- \+ *lemma* mem_target
- \+ *lemma* proj_symm_apply
- \+ *lemma* proj_symm_apply'
- \+ *lemma* apply_symm_apply
- \+ *lemma* apply_symm_apply'
- \+ *lemma* symm_apply_mk_proj
- \+ *lemma* preimage_symm_proj_base_set
- \+ *lemma* preimage_symm_proj_inter
- \+ *lemma* coe_mk
- \+ *lemma* map_target
- \+ *lemma* coe_fst_eventually_eq_proj
- \+ *lemma* coe_fst_eventually_eq_proj'
- \+ *lemma* map_proj_nhds
- \+ *lemma* continuous_at_proj
- \+/\- *lemma* is_trivial_topological_fiber_bundle.is_topological_fiber_bundle
- \+ *lemma* continuous_symm_trivialization_at
- \+ *lemma* is_open_source_trivialization_at
- \+ *lemma* is_open_target_trivialization_at_inter
- \+ *lemma* is_topological_fiber_bundle
- \+ *lemma* continuous_proj
- \- *lemma* bundle_trivialization.coe_coe
- \- *lemma* bundle_trivialization.coe_mk
- \- *lemma* bundle_trivialization.mem_source
- \- *lemma* bundle_trivialization.mem_target
- \- *lemma* bundle_trivialization.coe_fst
- \- *lemma* bundle_trivialization.coe_fst'
- \- *lemma* bundle_trivialization.mk_proj_snd
- \- *lemma* bundle_trivialization.mk_proj_snd'
- \- *lemma* bundle_trivialization.proj_symm_apply
- \- *lemma* bundle_trivialization.proj_symm_apply'
- \- *lemma* bundle_trivialization.apply_symm_apply
- \- *lemma* bundle_trivialization.apply_symm_apply'
- \- *lemma* bundle_trivialization.symm_apply_mk_proj
- \- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj
- \- *lemma* bundle_trivialization.coe_fst_eventually_eq_proj'
- \- *lemma* bundle_trivialization.map_proj_nhds
- \- *lemma* bundle_trivialization.continuous_at_proj
- \+ *def* set_symm
- \+ *def* to_prebundle_trivialization
- \+ *def* comp_homeomorph
- \+/\- *def* is_topological_fiber_bundle
- \+/\- *def* is_trivial_topological_fiber_bundle
- \+ *def* total_space_topology
- \+ *def* bundle_trivialization_at
- \- *def* bundle_trivialization.comp_homeomorph



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
- \+ *lemma* cast_succ_eq_zero_iff
- \+ *lemma* cast_succ_ne_zero_iff
- \+ *lemma* succ_above_ne_zero_zero
- \+ *lemma* succ_above_eq_zero_iff
- \+ *lemma* succ_above_ne_zero
- \+ *lemma* cast_succ_pred_eq_pred_cast_succ
- \+ *lemma* pred_succ_above_pred



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
- \- *lemma* Pi_congr_right_refl
- \- *lemma* Pi_congr_right_symm
- \- *lemma* Pi_congr_right_trans
- \- *def* Pi_congr_right

Modified src/linear_algebra/pi.lean
- \+ *lemma* Pi_congr_right_refl
- \+ *lemma* Pi_congr_right_symm
- \+ *lemma* Pi_congr_right_trans
- \+ *def* Pi_congr_right
- \- *def* pi



## [2021-06-23 21:01:23](https://github.com/leanprover-community/mathlib/commit/3cf8039)
feat(measure_theory/set_integral): the set integral is continuous ([#7931](https://github.com/leanprover-community/mathlib/pull/7931))
Most of the code is dedicated to building a continuous linear map from Lp to the Lp space corresponding to the restriction of the measure to a set. The set integral is then continuous as composition of the integral and that map.
#### Estimated changes
Modified src/measure_theory/set_integral.lean
- \+ *lemma* Lp_to_Lp_restrict_add
- \+ *lemma* Lp_to_Lp_restrict_smul
- \+ *lemma* norm_Lp_to_Lp_restrict_le
- \+ *lemma* Lp_to_Lp_restrict_clm_coe_fn
- \+ *lemma* continuous_set_integral
- \+ *def* Lp_to_Lp_restrict_clm



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
- \+/\- *lemma* nndist_eq_nnnorm
- \+/\- *lemma* nnnorm_zero
- \+/\- *lemma* nnnorm_add_le
- \+/\- *lemma* nnnorm_neg
- \+/\- *lemma* nndist_nnnorm_nnnorm_le
- \+/\- *lemma* of_real_norm_eq_coe_nnnorm
- \+/\- *lemma* edist_eq_coe_nnnorm_sub
- \+/\- *lemma* edist_eq_coe_nnnorm
- \+/\- *lemma* mem_emetric_ball_0_iff
- \+/\- *lemma* prod.nnsemi_norm_def
- \+/\- *lemma* continuous_nnnorm
- \+/\- *lemma* uniform_continuous_nnnorm
- \+/\- *lemma* continuous.nnnorm
- \+/\- *lemma* continuous_at.nnnorm
- \+/\- *lemma* continuous_on.nnnorm
- \+/\- *lemma* nnnorm_eq_zero
- \+/\- *lemma* prod.nnnorm_def
- \+/\- *lemma* nnnorm_one
- \+/\- *lemma* nnnorm_mul
- \+/\- *lemma* nnnorm_pow
- \+/\- *lemma* nnnorm_div
- \+/\- *lemma* nnnorm_inv
- \+/\- *lemma* nnnorm_fpow
- \+/\- *lemma* nnnorm_coe_nat
- \+/\- *lemma* norm_two
- \+/\- *lemma* nnnorm_two
- \+/\- *lemma* nnnorm_of_nonneg
- \+/\- *lemma* ennnorm_eq_of_real
- \+/\- *lemma* nnnorm_eq
- \+/\- *lemma* nnnorm_norm
- \+/\- *lemma* nnreal.coe_nat_abs
- \+/\- *lemma* nnnorm_nsmul_le
- \+/\- *lemma* nnnorm_gsmul_le
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* summable_of_summable_nnnorm
- \- *def* nnnorm

Modified src/measure_theory/bochner_integration.lean


Modified src/topology/metric_space/basic.lean
- \- *def* nndist



## [2021-06-23 15:53:39](https://github.com/leanprover-community/mathlib/commit/a7b5237)
feat(category_theory/arrow): arrow.iso_mk ([#8057](https://github.com/leanprover-community/mathlib/pull/8057))
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *def* iso_mk



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
- \+/\- *lemma* forall₂.mp
- \+/\- *lemma* forall₂.flip
- \+/\- *lemma* forall₂_same
- \+/\- *lemma* right_unique_forall₂'



## [2021-06-23 11:50:23](https://github.com/leanprover-community/mathlib/commit/d9eed42)
feat(analysis/liouville/inequalities_and_series): two useful inequalities for Liouville ([#8001](https://github.com/leanprover-community/mathlib/pull/8001))
This PR ~~creates a file with~~ proves two very specific inequalities.  They will be useful for the Liouville PR, showing that transcendental Liouville numbers exist.
After the initial code review, I scattered an initial segment of this PR into mathlib.  What is left might only be useful in the context of proving the transcendence of Liouville's constants.
~~Given the shortness of this file, I may move it into the main `liouville_constant`, after PR [#8020](https://github.com/leanprover-community/mathlib/pull/8020)  is merged.~~
#### Estimated changes
Modified src/analysis/liouville/liouville_constant.lean
- \+ *lemma* tsum_one_div_pow_factorial_lt
- \+ *lemma* aux_calc



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
- \+/\- *lemma* mul_le_mul_iff_left
- \+/\- *lemma* mul_le_mul_iff_right
- \+/\- *lemma* mul_le_mul_left'
- \+/\- *lemma* le_of_mul_le_mul_left'
- \+/\- *lemma* mul_le_mul_right'
- \+/\- *lemma* le_of_mul_le_mul_right'
- \+/\- *lemma* mul_lt_mul_iff_left
- \+/\- *lemma* mul_lt_mul_iff_right
- \+/\- *lemma* mul_lt_mul_left'
- \+/\- *lemma* lt_of_mul_lt_mul_left'
- \+/\- *lemma* mul_lt_mul_right'
- \+/\- *lemma* lt_of_mul_lt_mul_right'
- \+/\- *lemma* le_mul_iff_one_le_right'
- \+/\- *lemma* mul_le_iff_le_one_right'
- \+/\- *lemma* le_mul_iff_one_le_left'
- \+/\- *lemma* mul_le_iff_le_one_left'
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \+/\- *lemma* lt_mul_iff_one_lt_right'
- \+/\- *lemma* mul_lt_iff_lt_one_left'
- \+/\- *lemma* lt_mul_iff_one_lt_left'
- \+/\- *lemma* mul_lt_iff_lt_one_right'
- \+/\- *lemma* mul_le_of_le_of_le_one
- \+/\- *lemma* lt_mul_of_lt_of_one_le
- \+/\- *lemma* mul_lt_of_lt_of_le_one
- \+/\- *lemma* lt_mul_of_le_of_one_lt
- \+/\- *lemma* mul_lt_of_le_one_of_lt
- \+/\- *lemma* mul_le_of_le_one_of_le
- \+/\- *lemma* le_mul_of_one_le_of_le
- \+ *lemma* left.mul_lt_one
- \+ *lemma* right.mul_lt_one
- \+/\- *lemma* mul_lt_of_le_of_lt_one
- \+/\- *lemma* mul_lt_of_lt_one_of_le
- \+/\- *lemma* lt_mul_of_one_lt_of_le
- \+ *lemma* le_mul_of_le_of_le_one
- \+/\- *lemma* one_le_mul
- \+/\- *lemma* lt_mul_of_lt_of_one_lt
- \+ *lemma* left.mul_lt_one_of_lt_of_lt_one
- \+ *lemma* right.mul_lt_one_of_lt_of_lt_one
- \+ *lemma* right.one_le_mul
- \+ *lemma* right.one_lt_mul
- \+/\- *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* mul_le_of_le_one_right'
- \+ *lemma* mul_lt_mul_of_lt_of_lt
- \+/\- *lemma* mul_lt_mul_of_le_of_lt
- \+/\- *lemma* mul_lt_mul'''
- \+/\- *lemma* mul_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_mul'
- \+/\- *lemma* mul_le_mul_three
- \+/\- *lemma* lt_mul_of_one_lt_left'
- \+ *lemma* one_le_mul_right
- \+/\- *lemma* one_lt_mul_of_le_of_lt'
- \+/\- *lemma* lt_mul_of_one_le_of_lt
- \+/\- *lemma* lt_mul_of_one_lt_of_lt
- \+/\- *lemma* monotone.const_mul'
- \+/\- *lemma* monotone.mul_const'
- \+/\- *lemma* monotone.mul'
- \+/\- *lemma* monotone.mul_strict_mono'
- \- *lemma* lt_mul_of_one_le_of_lt'
- \- *lemma* lt_mul_of_one_lt_of_lt'
- \- *lemma* mul_le_one'
- \- *lemma* mul_le_of_le_one_of_le'
- \- *lemma* mul_le_of_le_of_le_one'
- \- *lemma* mul_lt_one_of_lt_one_of_le_one'
- \- *lemma* mul_lt_one_of_le_one_of_lt_one'
- \- *lemma* mul_lt_one'
- \- *lemma* mul_lt_of_le_one_of_lt'
- \- *lemma* mul_lt_of_lt_of_le_one'
- \- *lemma* mul_lt_of_lt_one_of_lt'
- \- *lemma* mul_lt_of_lt_of_lt_one'
- \- *lemma* mul_lt_one_of_lt_one_of_le_one
- \- *lemma* mul_lt_one_of_le_one_of_lt_one
- \- *lemma* mul_eq_one_iff_eq_one_of_one_le
- \- *lemma* mul_lt_one
- \- *lemma* mul_lt_of_lt_one_of_lt
- \- *lemma* mul_lt_of_lt_of_lt_one
- \+ *theorem* mul_lt_of_lt_of_lt_one
- \+ *theorem* mul_lt_of_lt_one_of_lt
- \+ *def* contravariant.to_left_cancel_semigroup
- \+ *def* contravariant.to_right_cancel_semigroup

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
- \+ *lemma* liouville_number_tail_pos
- \+ *lemma* liouville_number_eq_initial_terms_add_tail



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
- \+ *lemma* one_div_strict_mono_decr_on
- \+ *lemma* one_div_pow_le_one_div_pow_of_le
- \+ *lemma* one_div_pow_lt_one_div_pow_of_lt
- \+ *lemma* one_div_pow_mono
- \+ *lemma* one_div_pow_strict_mono



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
- \+ *lemma* span_le_adjoin
- \+ *lemma* adjoin_to_submodule_le
- \+ *lemma* adjoin_eq_span_of_subset



## [2021-06-22 19:52:44](https://github.com/leanprover-community/mathlib/commit/c594196)
chore(topology/continuous_function/algebra): delete old instances, use bundled sub[monoid, group, ring]s ([#8004](https://github.com/leanprover-community/mathlib/pull/8004))
We remove the `monoid`, `group`, ... instances on `{ f : α → β | continuous f }` since `C(α, β)` should be used instead, and we replacce the `sub[monoid, group, ...]` instances on `{ f : α → β | continuous f }` by definitions of bundled subobjects with carrier `{ f : α → β | continuous f }`. We keep the `set_of` for subobjects since we need a subset to be the carrier.
Zulip : https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/instances.20on.20continuous.20subtype
#### Estimated changes
Modified src/topology/continuous_function/algebra.lean
- \- *lemma* continuous_functions.coe_smul
- \+ *def* continuous_submonoid
- \+ *def* continuous_subgroup
- \+ *def* continuous_subsemiring
- \+ *def* continuous_subring
- \+ *def* continuous_submodule
- \+ *def* continuous_subalgebra
- \- *def* continuous.C



## [2021-06-22 16:26:58](https://github.com/leanprover-community/mathlib/commit/83bd2e6)
feat(analysis/normed_space/multilinear): add a few inequalities ([#8018](https://github.com/leanprover-community/mathlib/pull/8018))
Also add a few lemmas about `tsum` and `nnnorm`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* tsum_of_nnnorm_bounded
- \+ *lemma* nnnorm_tsum_le

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* tsum_eval
- \+ *theorem* le_op_norm_mul_prod_of_le
- \+ *theorem* le_op_norm_mul_pow_card_of_le
- \+ *theorem* le_op_norm_mul_pow_of_le
- \+ *theorem* le_op_nnnorm
- \+ *theorem* le_of_op_nnnorm_le



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
- \+ *lemma* ker_int_cast_add_hom
- \+ *lemma* ker_int_cast_ring_hom
- \+ *lemma* lift_coe
- \+ *lemma* lift_cast_add_hom
- \+ *lemma* lift_comp_coe
- \+ *lemma* lift_comp_cast_add_hom
- \+ *def* lift

Created src/data/zmod/quotient.lean
- \+ *def* quotient_gmultiples_nat_equiv_zmod
- \+ *def* quotient_gmultiples_equiv_zmod
- \+ *def* quotient_span_nat_equiv_zmod
- \+ *def* quotient_span_equiv_zmod

Modified src/group_theory/subgroup.lean
- \+ *lemma* mem_gpowers_iff
- \+ *lemma* mem_gmultiples_iff
- \+ *lemma* int.mem_gmultiples_iff

Modified src/ring_theory/ideal/basic.lean
- \+ *def* quot_equiv_of_eq

Modified src/ring_theory/int/basic.lean
- \+ *lemma* gmultiples_nat_abs
- \+ *lemma* span_nat_abs



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
- \+ *lemma* exists_locally_constant_fin_two
- \+ *theorem* exists_locally_constant_fintype_aux
- \+ *theorem* exists_locally_constant_fintype_nonempty
- \+ *theorem* exists_locally_constant

Modified src/topology/discrete_quotient.lean
- \+ *lemma* lift_is_locally_constant
- \+ *lemma* lift_eq_coe
- \+ *lemma* factors
- \+ *def* discrete_quotient
- \+ *def* lift
- \+ *def* locally_constant_lift

Modified src/topology/locally_constant/basic.lean
- \+ *lemma* is_closed_fiber
- \+ *lemma* is_clopen_fiber



## [2021-06-22 13:52:01](https://github.com/leanprover-community/mathlib/commit/6e5de19)
feat(linear_algebra/free_module): add lemmas ([#7950](https://github.com/leanprover-community/mathlib/pull/7950))
Easy results about free modules.
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/module/projective.lean
- \+ *theorem* projective_of_basis
- \- *theorem* projective_of_free

Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/free_module.lean


Modified src/linear_algebra/std_basis.lean
- \+/\- *lemma* linear_independent_std_basis



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
- \+/\- *lemma* section_ext
- \+ *lemma* app_surjective_of_stalk_functor_map_bijective
- \+/\- *lemma* app_bijective_of_stalk_functor_map_bijective



## [2021-06-22 12:45:37](https://github.com/leanprover-community/mathlib/commit/208d4fe)
docs(data/pnat): add module docstrings ([#7960](https://github.com/leanprover-community/mathlib/pull/7960))
#### Estimated changes
Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean
- \+ *def* xgcd
- \- *def* xgcd:



## [2021-06-22 11:36:42](https://github.com/leanprover-community/mathlib/commit/4cbe7d6)
feat(group_theory/specific_groups/cyclic): A group is commutative if the quotient by the center is cyclic ([#7952](https://github.com/leanprover-community/mathlib/pull/7952))
#### Estimated changes
Modified src/group_theory/specific_groups/cyclic.lean
- \+ *lemma* commutative_of_cyclic_center_quotient
- \+ *def* comm_group_of_cycle_center_quotient



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
- \+ *lemma* noncomm_prod_singleton

Modified src/group_theory/perm/cycle_type.lean
- \- *lemma* mem_list_cycles_iff
- \- *lemma* list_cycles_perm_list_cycles

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle.support_congr
- \+ *lemma* is_cycle.eq_on_support_inter_nonempty_congr
- \+ *lemma* mem_list_cycles_iff
- \+ *lemma* list_cycles_perm_list_cycles
- \+ *lemma* cycle_factors_finset_eq_list_to_finset
- \+ *lemma* cycle_factors_finset_eq_finset
- \+ *lemma* cycle_factors_finset_pairwise_disjoint
- \+ *lemma* cycle_factors_finset_mem_commute
- \+ *lemma* cycle_factors_finset_noncomm_prod
- \+ *lemma* mem_cycle_factors_finset_iff
- \+ *lemma* cycle_factors_finset_eq_empty_iff
- \+ *lemma* cycle_factors_finset_eq_singleton_self_iff
- \+ *lemma* cycle_factors_finset_eq_singleton_iff
- \+ *lemma* cycle_factors_finset_injective
- \+ *def* cycle_factors_finset

Modified src/group_theory/perm/sign.lean


Modified src/group_theory/perm/support.lean
- \+ *lemma* disjoint.symmetric
- \+ *lemma* disjoint.commute
- \+/\- *lemma* support_congr
- \+ *lemma* pow_eq_on_of_mem_support
- \+ *lemma* disjoint.mem_imp
- \+ *lemma* eq_on_support_mem_disjoint
- \+ *lemma* support_le_prod_of_mem
- \- *lemma* disjoint.mul_comm

Modified src/group_theory/specific_groups/alternating.lean




## [2021-06-22 10:22:32](https://github.com/leanprover-community/mathlib/commit/9ca8597)
feat(linear_algebra/matrix/reindex): add some lemmas ([#7963](https://github.com/leanprover-community/mathlib/pull/7963))
From LTE
Added lemmas `reindex_linear_equiv_trans`, `reindex_linear_equiv_comp`, `reindex_linear_equiv_comp_apply`, `reindex_linear_equiv_one` and `mul_reindex_linear_equiv_mul_one` needed in LTE.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* minor_apply
- \+/\- *lemma* transpose_minor
- \+ *lemma* mul_minor_one
- \+ *lemma* one_minor_mul
- \+/\- *def* minor

Modified src/linear_algebra/matrix/reindex.lean
- \+ *lemma* reindex_linear_equiv_trans
- \+ *lemma* reindex_linear_equiv_comp
- \+ *lemma* reindex_linear_equiv_comp_apply
- \+ *lemma* reindex_linear_equiv_one
- \+/\- *lemma* reindex_linear_equiv_mul
- \+ *lemma* mul_reindex_linear_equiv_one



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
- \+/\- *theorem* char_p.exists
- \+/\- *theorem* char_p.exists_unique
- \+/\- *theorem* char_p.congr



## [2021-06-22 03:06:39](https://github.com/leanprover-community/mathlib/commit/4416eac)
feat(topology/instances/real): a continuous periodic function has compact range (and is hence bounded) ([#7968](https://github.com/leanprover-community/mathlib/pull/7968))
A few more facts about periodic functions, namely:
- If a function `f` is `periodic` with positive period `p`,
  then for all `x` there exists `y` such that `y` is an element of `[0, p)` and `f x = f y`
- A continuous, periodic function has compact range
- A continuous, periodic function is bounded
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* periodic.exists_mem_Ico

Modified src/data/set/basic.lean
- \+/\- *theorem* image_univ
- \+/\- *theorem* image_subset_range
- \+ *theorem* mem_range_of_mem_image
- \+/\- *theorem* range_subset_iff

Modified src/topology/instances/real.lean
- \+ *lemma* periodic.compact_of_continuous'
- \+ *lemma* periodic.compact_of_continuous
- \+ *lemma* periodic.bounded_of_continuous



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
Created src/algebra/non_unital_alg_hom.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* to_distrib_mul_action_hom_eq_coe
- \+ *lemma* to_mul_hom_eq_coe
- \+ *lemma* coe_to_distrib_mul_action_hom
- \+ *lemma* coe_to_mul_hom
- \+ *lemma* coe_distrib_mul_action_hom_mk
- \+ *lemma* coe_mul_hom_mk
- \+ *lemma* map_smul
- \+ *lemma* map_add
- \+ *lemma* map_mul
- \+ *lemma* map_zero
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* zero_apply
- \+ *lemma* one_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_inverse
- \+ *lemma* to_non_unital_alg_hom_eq_coe
- \+ *lemma* coe_to_non_unital_alg_hom
- \+ *def* comp
- \+ *def* inverse
- \+ *def* to_non_unital_alg_hom



## [2021-06-21 19:43:13](https://github.com/leanprover-community/mathlib/commit/2b80d2f)
feat(geometry/euclidean/sphere): proof of Freek thm 95 - Ptolemy’s Theorem ([#7329](https://github.com/leanprover-community/mathlib/pull/7329))
#### Estimated changes
Modified docs/100.yaml


Modified src/geometry/euclidean/sphere.lean
- \+ *theorem* mul_dist_add_mul_dist_eq_mul_dist_of_cospherical



## [2021-06-21 19:03:52](https://github.com/leanprover-community/mathlib/commit/2fb0842)
perf(ci): use self-hosted runner for bors ([#8024](https://github.com/leanprover-community/mathlib/pull/8024))
Run CI builds for the `staging` branch used by bors on a self-hosted github actions runner.  This runner has been graciously provided by Johan Commelin's DFG grant and is hosted at the Albert-Ludwigs-Universität Freiburg.
We need to use two github actions workflow files to use a separate runner for the `staging` branch: `build.yml` and `bors.yml`.  These are almost identical, except for the `runs-on:` property indicating which runner should be used.  The shell script `mk_build_yml.sh` is therefore used to generate both files from the common template `build.yml.in`.
#### Estimated changes
Created .github/workflows/bors.yml


Modified .github/workflows/build.yml


Created .github/workflows/build.yml.in


Created .github/workflows/lint_self_test.yml


Created .github/workflows/mk_build_yml.sh




## [2021-06-21 14:25:31](https://github.com/leanprover-community/mathlib/commit/eb13f6b)
feat(ring_theory/derivation): add missing dsimp lemmas, use old_structure_command, golf structure proofs ([#8013](https://github.com/leanprover-community/mathlib/pull/8013))
This adds a pile of missing coercion lemmas proved by refl, and uses them to construct the `add_comm_monoid`, `add_comm_group`, and `module` instances.
This also changes `derivation` to be an old-style structure, which is more in line with the other bundled homomorphisms.
This also removes `derivation.commutator` to avoid having two ways to spell the same thing, as this leads to lemmas being harder to apply
#### Estimated changes
Modified src/ring_theory/derivation.lean
- \+/\- *lemma* to_fun_eq_coe
- \+ *lemma* to_linear_map_eq_coe
- \+/\- *lemma* mk_coe
- \+/\- *lemma* coe_fn_coe
- \+/\- *lemma* coe_injective
- \+ *lemma* coe_zero
- \+ *lemma* coe_zero_linear_map
- \+ *lemma* zero_apply
- \+ *lemma* coe_add
- \+ *lemma* coe_add_linear_map
- \+/\- *lemma* add_apply
- \+ *lemma* coe_Rsmul
- \+ *lemma* coe_Rsmul_linear_map
- \+/\- *lemma* Rsmul_apply
- \+ *lemma* coe_smul
- \+ *lemma* coe_smul_linear_map
- \+/\- *lemma* smul_apply
- \+ *lemma* coe_neg
- \+ *lemma* coe_neg_linear_map
- \+ *lemma* neg_apply
- \+ *lemma* coe_sub
- \+ *lemma* coe_sub_linear_map
- \+/\- *lemma* sub_apply
- \- *lemma* smul_to_linear_map_coe
- \+ *def* coe_fn_add_monoid_hom
- \- *def* commutator



## [2021-06-21 14:25:28](https://github.com/leanprover-community/mathlib/commit/92263c0)
refactor(algebraic_geometry/structure_sheaf): Enclose definitions in structure_sheaf namespace ([#8010](https://github.com/leanprover-community/mathlib/pull/8010))
Moves some pretty generic names like `const` and `to_open` to the `structure_sheaf` namespace.
#### Estimated changes
Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* comap_fun_is_locally_fraction
- \+ *lemma* comap_apply
- \+ *lemma* comap_const
- \+ *lemma* comap_id_eq_map
- \+ *lemma* comap_id
- \+ *lemma* comap_id'
- \+ *lemma* comap_comp
- \- *lemma* structure_sheaf.comap_fun_is_locally_fraction
- \- *lemma* structure_sheaf.comap_apply
- \- *lemma* structure_sheaf.comap_const
- \- *lemma* structure_sheaf.comap_id_eq_map
- \- *lemma* structure_sheaf.comap_id
- \- *lemma* structure_sheaf.comap_id'
- \- *lemma* structure_sheaf.comap_comp
- \+ *def* comap_fun
- \+ *def* comap
- \- *def* structure_sheaf.comap_fun
- \- *def* structure_sheaf.comap



## [2021-06-21 14:25:27](https://github.com/leanprover-community/mathlib/commit/5bc18a9)
feat(topology/category/limits): Generalize Topological Kőnig's lemma  ([#7982](https://github.com/leanprover-community/mathlib/pull/7982))
This PR generalizes the Topological Kőnig's lemma to work with limits over cofiltered categories (as opposed to just directed orders). Along the way, we also prove some more API for the category instance on `ulift C`, and provide an  `as_small C` construction for a category `C`. 
Coauthored with @kmill
#### Estimated changes
Modified src/category_theory/category/ulift.lean
- \+ *lemma* obj_down_obj_up
- \+ *lemma* obj_up_obj_down
- \+/\- *def* ulift.up
- \+/\- *def* ulift.down
- \+/\- *def* ulift.equivalence
- \+ *def* {w
- \+ *def* ulift_hom.obj_down
- \+ *def* ulift_hom.obj_up
- \+ *def* ulift_hom.up
- \+ *def* ulift_hom.down
- \+ *def* ulift_hom.equiv
- \+ *def* as_small.up
- \+ *def* as_small.down
- \+ *def* as_small.equiv

Modified src/category_theory/filtered.lean


Modified src/topology/category/Top/limits.lean
- \+/\- *lemma* partial_sections.nonempty
- \+/\- *lemma* partial_sections.directed
- \+/\- *lemma* partial_sections.closed
- \+ *lemma* nonempty_limit_cone_of_compact_t2_cofiltered_system
- \+ *lemma* nonempty_sections_of_fintype_cofiltered_system.init
- \- *lemma* nonempty_limit_cone_of_compact_t2_inverse_system
- \- *lemma* nonempty_sections_of_fintype_inverse_system.init
- \+ *theorem* nonempty_sections_of_fintype_cofiltered_system
- \+/\- *def* partial_sections
- \- *def* ulift.directed_order



## [2021-06-21 14:25:26](https://github.com/leanprover-community/mathlib/commit/9ce032c)
feat(data/matrix/basic): generalize to non_assoc_semiring ([#7974](https://github.com/leanprover-community/mathlib/pull/7974))
Matrices with whose coefficients form a non-unital and/or non-associative ring themselves form a non-unital and non-associative ring.
This isn't a full generalization of the file, the main aim was to generalize the typeclass instances available.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* ring_hom.map_list_sum
- \+/\- *lemma* ring_hom.map_multiset_sum
- \+/\- *lemma* ring_hom.map_sum
- \+/\- *lemma* sum_boole

Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/data/matrix/basic.lean
- \+/\- *lemma* dot_product_assoc
- \+/\- *lemma* dot_product_zero
- \+/\- *lemma* dot_product_zero'
- \+/\- *lemma* zero_dot_product
- \+/\- *lemma* zero_dot_product'
- \+/\- *lemma* add_dot_product
- \+/\- *lemma* dot_product_add
- \+/\- *lemma* diagonal_dot_product
- \+/\- *lemma* dot_product_diagonal
- \+/\- *lemma* dot_product_diagonal'
- \+/\- *lemma* smul_dot_product
- \+/\- *lemma* dot_product_smul
- \+ *lemma* sum_apply
- \+/\- *lemma* map_mul
- \+/\- *lemma* smul_mul_vec_assoc
- \+/\- *lemma* vec_mul_vec_mul
- \+/\- *lemma* mul_vec_mul_vec
- \+/\- *lemma* mul_vec_one
- \+/\- *lemma* vec_mul_one
- \+/\- *lemma* col_add
- \+/\- *lemma* col_smul
- \+/\- *lemma* row_add
- \+/\- *lemma* row_smul
- \+/\- *lemma* row_mul_col_apply
- \+/\- *def* vec_mul_vec

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
- \+/\- *lemma* norm_id_le
- \+/\- *lemma* norm_id
- \+ *lemma* coe_id
- \+ *lemma* norm_comp_le_of_le
- \+ *lemma* norm_comp_le_of_le'
- \+ *lemma* comp_assoc
- \+ *lemma* coe_comp
- \+/\- *lemma* id
- \+/\- *lemma* isometry_id



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


Created src/analysis/liouville/liouville_constant.lean
- \+ *def* liouville_number
- \+ *def* liouville_number_initial_terms
- \+ *def* liouville_number_tail



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
- \+ *def* pi.eval_ring_hom
- \- *def* eval_ring_hom

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
- \- *lemma* measurable.inner
- \- *lemma* ae_measurable.inner

Modified src/analysis/special_functions/exp_log.lean
- \- *lemma* measurable_re
- \- *lemma* measurable_im
- \- *lemma* measurable_of_real
- \- *lemma* measurable_exp
- \- *lemma* measurable.cexp
- \- *lemma* measurable.exp
- \- *lemma* measurable_log
- \- *lemma* measurable.log

Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/sqrt.lean
- \- *lemma* measurable.sqrt

Modified src/analysis/special_functions/trigonometric.lean
- \- *lemma* measurable_sin
- \- *lemma* measurable_cos
- \- *lemma* measurable_sinh
- \- *lemma* measurable_cosh
- \- *lemma* measurable.ccos
- \- *lemma* measurable.csin
- \- *lemma* measurable.ccosh
- \- *lemma* measurable.csinh
- \- *lemma* measurable.cos
- \- *lemma* measurable.sin
- \- *lemma* measurable.cosh
- \- *lemma* measurable.sinh
- \- *lemma* measurable_arcsin
- \- *lemma* measurable_arccos
- \- *lemma* measurable_arg
- \- *lemma* measurable_log
- \- *lemma* measurable.carg
- \- *lemma* measurable.clog
- \- *lemma* measurable_arctan
- \- *lemma* measurable.arctan

Modified src/measure_theory/mean_inequalities.lean


Created src/measure_theory/special_functions.lean
- \+ *lemma* measurable_exp
- \+ *lemma* measurable_log
- \+ *lemma* measurable_sin
- \+ *lemma* measurable_cos
- \+ *lemma* measurable_sinh
- \+ *lemma* measurable_cosh
- \+ *lemma* measurable_arcsin
- \+ *lemma* measurable_arccos
- \+ *lemma* measurable_arctan
- \+ *lemma* measurable_re
- \+ *lemma* measurable_im
- \+ *lemma* measurable_of_real
- \+ *lemma* measurable_arg
- \+ *lemma* measurable.exp
- \+ *lemma* measurable.log
- \+ *lemma* measurable.cos
- \+ *lemma* measurable.sin
- \+ *lemma* measurable.cosh
- \+ *lemma* measurable.sinh
- \+ *lemma* measurable.arctan
- \+ *lemma* measurable.sqrt
- \+ *lemma* measurable.cexp
- \+ *lemma* measurable.ccos
- \+ *lemma* measurable.csin
- \+ *lemma* measurable.ccosh
- \+ *lemma* measurable.csinh
- \+ *lemma* measurable.carg
- \+ *lemma* measurable.clog
- \+ *lemma* measurable.inner
- \+ *lemma* ae_measurable.inner



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
- \+ *lemma* integral_undef
- \+/\- *lemma* integral_non_ae_measurable
- \+/\- *lemma* integral_non_ae_measurable_of_le



## [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d155d9)
refactor(topology/metric_space/isometry): move material about isometries of normed spaces ([#8003](https://github.com/leanprover-community/mathlib/pull/8003))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/topology.20and.20analysis
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean
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
- \+ *lemma* add_monoid_hom.isometry_iff_norm
- \+ *lemma* add_monoid_hom.isometry_of_norm
- \+ *lemma* algebra_map_isometry
- \+ *lemma* norm_coe

Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/normed_group_hom.lean


Modified src/topology/algebra/group_completion.lean


Deleted src/topology/algebra/normed_group.lean
- \- *lemma* norm_coe

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/isometry.lean
- \- *lemma* isometry_iff_norm
- \- *lemma* isometry_of_norm
- \- *lemma* add_right_to_equiv
- \- *lemma* coe_add_right
- \- *lemma* add_right_apply
- \- *lemma* add_right_symm
- \- *lemma* add_left_to_equiv
- \- *lemma* coe_add_left
- \- *lemma* add_left_symm
- \- *lemma* neg_symm
- \- *lemma* neg_to_equiv
- \- *lemma* coe_neg
- \- *lemma* algebra_map_isometry



## [2021-06-19 23:38:51](https://github.com/leanprover-community/mathlib/commit/7d5b50a)
feat(algebra/homology/homotopy): flesh out the api a bit, add some simps ([#7941](https://github.com/leanprover-community/mathlib/pull/7941))
#### Estimated changes
Modified src/algebra/homology/homotopy.lean
- \+ *lemma* d_next_nat
- \+ *lemma* prev_d_nat
- \+ *def* of_eq
- \+ *def* comp



## [2021-06-19 18:19:08](https://github.com/leanprover-community/mathlib/commit/63c3ab5)
chore(data/int/basic): rationalize the arguments implicitness (mostly to_nat_sub_of_le) ([#7997](https://github.com/leanprover-community/mathlib/pull/7997))
#### Estimated changes
Modified src/data/int/basic.lean
- \+/\- *lemma* coe_pred_of_pos
- \+/\- *lemma* sub_div_of_dvd
- \+/\- *lemma* to_nat_sub_of_le
- \+/\- *theorem* mod_mod_of_dvd
- \+/\- *theorem* mul_div_mul_of_pos_left
- \+/\- *theorem* mul_mod_mul_of_pos
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_lt

Modified src/data/int/modeq.lean




## [2021-06-19 15:31:15](https://github.com/leanprover-community/mathlib/commit/cd8f7b5)
chore(topology/metric_space/pi_Lp): move to analysis folder, import inner_product_space ([#7991](https://github.com/leanprover-community/mathlib/pull/7991))
Currently, the file `pi_Lp` (on finite products of metric spaces, with the `L^p` norm) is in the topology folder, but it imports a lot of analysis (to have real powers) and it defines a normed space structure, so it makes more sense to have it in analysis. Also, it is currently imported by `inner_product_space`, to give an explicit construction of an inner product space on `pi_Lp 2`, which means that all files importing general purposes lemmas on inner product spaces also import real powers, trigonometry, and so on. We swap the imports, letting `pi_Lp` import `inner_product_space` and moving the relevant bits from the latter file to the former. This gives a more reasonable import graph.
#### Estimated changes
Modified src/analysis/normed_space/euclidean_dist.lean


Modified src/analysis/normed_space/inner_product.lean
- \- *lemma* pi_Lp.inner_apply
- \- *lemma* pi_Lp.norm_eq_of_L2
- \- *lemma* euclidean_space.norm_eq
- \- *lemma* finrank_euclidean_space
- \- *lemma* finrank_euclidean_space_fin
- \- *lemma* complex.isometry_euclidean_symm_apply
- \- *lemma* complex.isometry_euclidean_proj_eq_self
- \- *lemma* complex.isometry_euclidean_apply_zero
- \- *lemma* complex.isometry_euclidean_apply_one
- \- *def* euclidean_space
- \- *def* basis.isometry_euclidean_of_orthonormal
- \- *def* complex.isometry_euclidean
- \- *def* linear_isometry_equiv.of_inner_product_space
- \- *def* linear_isometry_equiv.from_orthogonal_span_singleton

Renamed src/topology/metric_space/pi_Lp.lean to src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.inner_apply
- \+ *lemma* pi_Lp.norm_eq_of_L2
- \+ *lemma* euclidean_space.norm_eq
- \+ *lemma* finrank_euclidean_space
- \+ *lemma* finrank_euclidean_space_fin
- \+ *lemma* complex.isometry_euclidean_symm_apply
- \+ *lemma* complex.isometry_euclidean_proj_eq_self
- \+ *lemma* complex.isometry_euclidean_apply_zero
- \+ *lemma* complex.isometry_euclidean_apply_one
- \+ *def* euclidean_space
- \+ *def* basis.isometry_euclidean_of_orthonormal
- \+ *def* complex.isometry_euclidean
- \+ *def* linear_isometry_equiv.of_inner_product_space
- \+ *def* linear_isometry_equiv.from_orthogonal_span_singleton

Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/instances/real.lean




## [2021-06-19 15:31:14](https://github.com/leanprover-community/mathlib/commit/497b84d)
chore(analysis/mean_inequalities): split integral mean inequalities to a new file ([#7990](https://github.com/leanprover-community/mathlib/pull/7990))
Currently, `normed_space.dual` imports a bunch of integration theory for no reason other than the file `mean_inequalities` contains both inequalities for finite sums and integrals. Splitting the file into two (and moving the integral versions to `measure_theory`) gives a more reasonable import graph.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \- *lemma* lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \- *lemma* fun_eq_fun_mul_inv_snorm_mul_snorm
- \- *lemma* fun_mul_inv_snorm_rpow
- \- *lemma* lintegral_rpow_fun_mul_inv_snorm_eq_one
- \- *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \- *lemma* ae_eq_zero_of_lintegral_rpow_eq_zero
- \- *lemma* lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \- *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \- *lemma* lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
- \- *lemma* lintegral_Lp_mul_le_Lq_mul_Lr
- \- *lemma* lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \- *lemma* lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
- \- *theorem* lintegral_mul_le_Lp_mul_Lq
- \- *theorem* lintegral_Lp_add_le
- \- *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq
- \- *def* fun_mul_inv_snorm

Modified src/measure_theory/lp_space.lean


Created src/measure_theory/mean_inequalities.lean
- \+ *lemma* lintegral_mul_le_one_of_lintegral_rpow_eq_one
- \+ *lemma* fun_eq_fun_mul_inv_snorm_mul_snorm
- \+ *lemma* fun_mul_inv_snorm_rpow
- \+ *lemma* lintegral_rpow_fun_mul_inv_snorm_eq_one
- \+ *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
- \+ *lemma* ae_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
- \+ *lemma* lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
- \+ *lemma* lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
- \+ *lemma* lintegral_Lp_mul_le_Lq_mul_Lr
- \+ *lemma* lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
- \+ *lemma* lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
- \+ *theorem* lintegral_mul_le_Lp_mul_Lq
- \+ *theorem* lintegral_Lp_add_le
- \+ *theorem* nnreal.lintegral_mul_le_Lp_mul_Lq
- \+ *def* fun_mul_inv_snorm



## [2021-06-19 15:31:13](https://github.com/leanprover-community/mathlib/commit/1846a1f)
feat(measure_theory/interval_integral): `abs_integral_le_integral_abs` ([#7959](https://github.com/leanprover-community/mathlib/pull/7959))
The absolute value of the integral of an integrable function is less than or equal to the integral of the absolute value that function.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* norm
- \+ *lemma* abs
- \+ *lemma* integral_nonneg_of_forall
- \+ *lemma* norm_integral_le_integral_norm
- \+ *lemma* abs_integral_le_integral_abs
- \- *lemma* interval_integrable.norm



## [2021-06-19 08:22:50](https://github.com/leanprover-community/mathlib/commit/2ca0452)
feat(data/{fin,nat,zmod}): prove `zmod.coe_add_eq_ite` ([#7975](https://github.com/leanprover-community/mathlib/pull/7975))
This PR adds a couple of lemmas relating addition modulo `n` (in `ℕ`, `fin n` or `zmod n`) and addition in `ℕ` or `ℤ`.
[Based on this Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Homomorphism.20from.20the.20integers.20descends.20to.20.24.24.5Cmathbb.7BZ.7D.2Fn.24.24)
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* coe_add_eq_ite

Modified src/data/nat/basic.lean
- \+ *lemma* add_mod_eq_ite

Modified src/data/zmod/basic.lean
- \+ *lemma* coe_add_eq_ite



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
- \+/\- *lemma* is_sheaf_of_representable

Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/yoneda.lean
- \+ *lemma* repr_w_hom
- \+ *lemma* repr_w_app_hom
- \+ *lemma* corepr_w_app_hom
- \+ *lemma* representable_of_nat_iso
- \+ *lemma* corepresentable_of_nat_iso
- \+/\- *lemma* yoneda_equiv_naturality
- \+ *def* punit_iso
- \+/\- *def* yoneda_sections
- \- *def* iso_comp_punit



## [2021-06-18 23:32:28](https://github.com/leanprover-community/mathlib/commit/42ab44c)
feat(group_theory): computable 1st isomorphism theorem ([#7988](https://github.com/leanprover-community/mathlib/pull/7988))
This PR defines a computable version of the first isomorphism theorem for groups and monoids that takes a right inverse of the map, `quotient_ker_equiv_of_right_inverse`.
#### Estimated changes
Modified src/group_theory/congruence.lean
- \+ *def* quotient_ker_equiv_of_right_inverse

Modified src/group_theory/quotient_group.lean
- \+ *def* quotient_ker_equiv_of_right_inverse



## [2021-06-18 23:32:27](https://github.com/leanprover-community/mathlib/commit/3ee6248)
feat(measure_theory): links between an integral and its improper version ([#7164](https://github.com/leanprover-community/mathlib/pull/7164))
This PR introduces ways of studying and computing `∫ x, f x ∂μ` by studying the limit of the sequence `∫ x in φ n, f x ∂μ` for an appropriate sequence `φ` of subsets of the domain of `f`.
#### Estimated changes
Modified src/measure_theory/integrable_on.lean
- \+/\- *lemma* ae_measurable_indicator_iff
- \+ *lemma* ae_measurable.restrict
- \+ *lemma* ae_measurable.indicator

Created src/measure_theory/integral_eq_improper.lean
- \+ *lemma* ae_cover_Icc
- \+ *lemma* ae_cover_Ici
- \+ *lemma* ae_cover_Iic
- \+ *lemma* ae_cover_Ioo
- \+ *lemma* ae_cover_Ioc
- \+ *lemma* ae_cover_Ico
- \+ *lemma* ae_cover_Ioi
- \+ *lemma* ae_cover_Iio
- \+ *lemma* ae_cover.restrict
- \+ *lemma* ae_cover_restrict_of_ae_imp
- \+ *lemma* ae_cover.inter_restrict
- \+ *lemma* ae_cover.ae_tendsto_indicator
- \+ *lemma* ae_cover.comp_tendsto
- \+ *lemma* ae_cover.bUnion_Iic_ae_cover
- \+ *lemma* ae_cover.bInter_Ici_ae_cover
- \+ *lemma* ae_cover.lintegral_tendsto_of_nat
- \+ *lemma* ae_cover.lintegral_tendsto_of_countably_generated
- \+ *lemma* ae_cover.lintegral_eq_of_tendsto
- \+ *lemma* ae_cover.supr_lintegral_eq_of_countably_generated
- \+ *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto
- \+ *lemma* ae_cover.integrable_of_lintegral_nnnorm_tendsto'
- \+ *lemma* ae_cover.integrable_of_integral_norm_tendsto
- \+ *lemma* ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
- \+ *lemma* ae_cover.integral_tendsto_of_countably_generated
- \+ *lemma* ae_cover.integral_eq_of_tendsto
- \+ *lemma* ae_cover.integral_eq_of_tendsto_of_nonneg_ae
- \+ *lemma* integrable_of_interval_integral_norm_tendsto
- \+ *lemma* integrable_on_Iic_of_interval_integral_norm_tendsto
- \+ *lemma* integrable_on_Ioi_of_interval_integral_norm_tendsto
- \+ *lemma* interval_integral_tendsto_integral
- \+ *lemma* interval_integral_tendsto_integral_Iic
- \+ *lemma* interval_integral_tendsto_integral_Ioi

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/set_integral.lean




## [2021-06-18 20:48:47](https://github.com/leanprover-community/mathlib/commit/f2f10cc)
docs(data/set/enumerate): add module and definition docstrings ([#7967](https://github.com/leanprover-community/mathlib/pull/7967))
#### Estimated changes
Modified src/data/set/enumerate.lean
- \+/\- *lemma* enumerate_eq_none_of_sel
- \+/\- *lemma* enumerate_eq_none
- \+/\- *lemma* enumerate_mem
- \+/\- *lemma* enumerate_inj



## [2021-06-18 20:48:46](https://github.com/leanprover-community/mathlib/commit/3a0653c)
feat(data/real/ennreal): add a `algebra ℝ≥0 ℝ≥0∞` instance ([#7846](https://github.com/leanprover-community/mathlib/pull/7846))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* smul_def

Modified src/data/real/nnreal.lean
- \+ *lemma* smul_def



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
- \+ *lemma* eq_zero_iff_forall_dual_eq_zero
- \+ *lemma* eq_iff_forall_dual_eq

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *lemma* norm'_eq_zero_iff

Modified src/data/real/ereal.lean
- \+ *lemma* coe_to_real
- \+ *lemma* lt_iff_exists_real_btwn

Modified src/data/real/liouville.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integrable_on.lean
- \+ *lemma* integrable_on_singleton_iff
- \+ *lemma* continuous_on.integrable_on_Icc
- \+ *lemma* continuous_on.integrable_on_interval
- \+ *lemma* continuous.integrable_on_Icc
- \+ *lemma* continuous.integrable_on_interval
- \+ *lemma* measure_theory.integrable_on.mul_continuous_on
- \+ *lemma* measure_theory.integrable_on.continuous_on_mul
- \- *lemma* integrable_comp

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* continuous_linear_map.integrable_comp

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ae_restrict_iff'
- \+ *lemma* ae_restrict_mem

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* is_compact_Icc
- \+ *lemma* is_compact_interval
- \+ *lemma* is_compact_pi_Icc
- \- *lemma* compact_Icc
- \- *lemma* compact_interval
- \- *lemma* compact_pi_Icc

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
- \+ *lemma* le_has_sum_of_le_sum
- \+/\- *lemma* sum_le_has_sum
- \+ *lemma* is_lub_has_sum
- \+ *lemma* tsum_le_of_sum_le
- \+ *lemma* tsum_le_of_sum_le'
- \+ *lemma* is_lub_has_sum'
- \+ *lemma* has_sum_of_is_lub_of_nonneg
- \+ *lemma* has_sum_of_is_lub

Modified src/topology/algebra/ordered/basic.lean
- \+ *lemma* tendsto_at_top_is_lub
- \+ *lemma* tendsto_at_bot_is_glb
- \+/\- *lemma* tendsto_at_top_csupr
- \+ *lemma* monotone.ge_of_tendsto
- \+ *lemma* monotone.le_of_tendsto
- \+ *lemma* is_lub_of_tendsto
- \+ *lemma* is_glb_of_tendsto



## [2021-06-18 13:40:11](https://github.com/leanprover-community/mathlib/commit/7c9a811)
feat(analysis/convex/basic): missing lemmas ([#7946](https://github.com/leanprover-community/mathlib/pull/7946))
- the union of a set/indexed family of convex sets is convex
- `open_segment a b` is convex
- a set is nonempty iff its convex hull is
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_Inter
- \+ *lemma* directed.convex_Union
- \+ *lemma* directed_on.convex_sUnion
- \+ *lemma* convex_open_segment
- \+ *lemma* convex_hull_nonempty_iff



## [2021-06-18 01:58:07](https://github.com/leanprover-community/mathlib/commit/e168bf7)
chore(scripts): update nolints.txt ([#7981](https://github.com/leanprover-community/mathlib/pull/7981))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-17 17:11:00](https://github.com/leanprover-community/mathlib/commit/49bf1fd)
chore(order/iterate): fix up the namespace ([#7977](https://github.com/leanprover-community/mathlib/pull/7977))
#### Estimated changes
Modified src/order/iterate.lean
- \+/\- *lemma* iterate_le_of_map_le
- \+/\- *lemma* iterate_pos_lt_of_map_lt
- \+/\- *lemma* iterate_pos_lt_of_map_lt'



## [2021-06-17 17:10:59](https://github.com/leanprover-community/mathlib/commit/dc73d1b)
docs(data/*/sqrt): add one module docstring and expand the other ([#7973](https://github.com/leanprover-community/mathlib/pull/7973))
#### Estimated changes
Modified src/data/int/sqrt.lean
- \+/\- *def* sqrt

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
- \+ *lemma* desc
- \+ *lemma* of_clopen_fiber_zero
- \+ *lemma* of_clopen_fiber_one
- \+ *lemma* locally_constant_eq_of_fiber_zero_eq
- \+ *lemma* unflip_flip
- \+ *lemma* flip_unflip
- \+ *lemma* coe_desc
- \+ *def* of_clopen
- \+ *def* flip
- \+ *def* unflip
- \+ *def* desc



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
- \+/\- *def* map

Modified src/order/preorder_hom.lean
- \+ *lemma* to_fun_eq_coe
- \+/\- *lemma* coe_fun_mk
- \+/\- *lemma* ext
- \- *lemma* coe_inj
- \- *lemma* coe_id
- \- *lemma* to_preorder_hom_coe
- \- *lemma* to_preorder_hom_coe_fn

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
- \+ *def* quotient_ker_equiv_of_right_inverse



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
- \+ *lemma* fun_map_eq_coe_const
- \+ *lemma* map_const
- \+ *lemma* inter
- \+ *lemma* inf
- \+ *lemma* Inf
- \+ *lemma* mem_carrier
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+ *lemma* const_mem
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closed
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* dense_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* eq_on_closure
- \+ *lemma* eq_of_eq_on_top
- \+ *lemma* eq_of_eq_on_dense
- \+ *theorem* ext
- \+ *def* closed_under
- \+ *def* simps.coe
- \+ *def* closure
- \+ *def* eq_locus



## [2021-06-16 18:44:26](https://github.com/leanprover-community/mathlib/commit/456a6d5)
docs(data/option/basic): add module docstring ([#7958](https://github.com/leanprover-community/mathlib/pull/7958))
#### Estimated changes
Modified src/data/option/basic.lean




## [2021-06-16 18:44:25](https://github.com/leanprover-community/mathlib/commit/08dfaab)
docs(data/set/disjointed): add module docstring and some whitespaces ([#7957](https://github.com/leanprover-community/mathlib/pull/7957))
#### Estimated changes
Modified src/data/set/disjointed.lean
- \+/\- *lemma* disjoint_disjointed
- \+/\- *lemma* disjoint_disjointed'
- \+/\- *lemma* disjointed_subset
- \+/\- *lemma* Union_lt_succ
- \+/\- *lemma* Inter_lt_succ
- \+/\- *lemma* disjointed_induct
- \+/\- *lemma* disjointed_of_mono
- \+/\- *lemma* subset_Union_disjointed
- \+/\- *lemma* Union_disjointed
- \+/\- *lemma* Union_disjointed_of_mono
- \+/\- *def* pairwise
- \+/\- *def* disjointed



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
- \+ *lemma* quotient_ring_saturate

Modified src/topology/algebra/ring.lean
- \+/\- *lemma* ideal.coe_closure
- \- *lemma* quotient_ring_saturate



## [2021-06-16 15:31:34](https://github.com/leanprover-community/mathlib/commit/a564bf1)
feat(data/list/cycle): cycles as quotients of lists ([#7504](https://github.com/leanprover-community/mathlib/pull/7504))
Cycles are common structures, and we define them as a quotient of lists. This is on the route to defining concrete cyclic permutations, and could also be used for encoding properties of cycles in graphs.
#### Estimated changes
Created src/data/list/cycle.lean
- \+ *lemma* next_or_nil
- \+ *lemma* next_or_singleton
- \+ *lemma* next_or_self_cons_cons
- \+ *lemma* next_or_cons_of_ne
- \+ *lemma* next_or_eq_next_or_of_mem_of_ne
- \+ *lemma* mem_of_next_or_ne
- \+ *lemma* next_or_concat
- \+ *lemma* next_or_mem
- \+ *lemma* next_singleton
- \+ *lemma* prev_singleton
- \+ *lemma* next_cons_cons_eq'
- \+ *lemma* next_cons_cons_eq
- \+ *lemma* next_ne_head_ne_last
- \+ *lemma* next_cons_concat
- \+ *lemma* next_last_cons
- \+ *lemma* prev_last_cons'
- \+ *lemma* prev_last_cons
- \+ *lemma* prev_cons_cons_eq'
- \+ *lemma* prev_cons_cons_eq
- \+ *lemma* prev_cons_cons_of_ne'
- \+ *lemma* prev_cons_cons_of_ne
- \+ *lemma* prev_ne_cons_cons
- \+ *lemma* next_mem
- \+ *lemma* prev_mem
- \+ *lemma* next_nth_le
- \+ *lemma* prev_nth_le
- \+ *lemma* pmap_next_eq_rotate_one
- \+ *lemma* pmap_prev_eq_rotate_length_sub_one
- \+ *lemma* prev_next
- \+ *lemma* next_prev
- \+ *lemma* prev_reverse_eq_next
- \+ *lemma* next_reverse_eq_prev
- \+ *lemma* is_rotated_next_eq
- \+ *lemma* is_rotated_prev_eq
- \+ *lemma* coe_eq_coe
- \+ *lemma* mk_eq_coe
- \+ *lemma* mk'_eq_coe
- \+ *lemma* mem_coe_iff
- \+ *lemma* reverse_coe
- \+ *lemma* mem_reverse_iff
- \+ *lemma* reverse_reverse
- \+ *lemma* length_coe
- \+ *lemma* length_reverse
- \+ *lemma* length_subsingleton_iff
- \+ *lemma* subsingleton_reverse_iff
- \+ *lemma* subsingleton.congr
- \+ *lemma* nontrivial_reverse_iff
- \+ *lemma* length_nontrivial
- \+ *lemma* nodup_coe_iff
- \+ *lemma* nodup_reverse_iff
- \+ *lemma* subsingleton.nodup
- \+ *def* next_or
- \+ *def* next
- \+ *def* prev
- \+ *def* cycle
- \+ *def* mem
- \+ *def* reverse
- \+ *def* length
- \+ *def* subsingleton
- \+ *def* nontrivial
- \+ *def* nodup
- \+ *def* to_multiset
- \+ *def* to_finset

Modified src/data/list/rotate.lean
- \+ *lemma* nth_le_rotate'
- \+ *lemma* rotate_reverse



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
- \+ *lemma* tendsto_Lp_iff_tendsto_ℒp'
- \+ *lemma* tendsto_Lp_iff_tendsto_ℒp
- \+/\- *lemma* tendsto_Lp_of_tendsto_ℒp
- \+ *lemma* cauchy_seq_Lp_iff_cauchy_seq_ℒp

Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_to_real_iff



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
- \+/\- *lemma* restrict_scalars_smul_def
- \+ *lemma* restrict_scalars.linear_equiv_map_smul
- \- *lemma* linear_equiv_map_smul
- \- *theorem* to_comap_apply
- \+/\- *def* restrict_scalars
- \+ *def* restrict_scalars.linear_equiv
- \+ *def* restrict_scalars.alg_equiv
- \- *def* comap
- \- *def* comap.to_comap
- \- *def* comap.of_comap
- \- *def* to_comap
- \- *def* alg_hom.comap
- \- *def* alg_equiv.comap
- \- *def* linear_equiv

Modified src/algebra/algebra/subalgebra.lean
- \- *def* comap

Modified src/algebra/algebra/tower.lean
- \- *theorem* algebra_comap_eq
- \+ *def* subalgebra.restrict_scalars

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/noetherian.lean




## [2021-06-16 04:52:02](https://github.com/leanprover-community/mathlib/commit/b865892)
feat(algebraic_geometry/Spec): Make Spec a functor. ([#7790](https://github.com/leanprover-community/mathlib/pull/7790))
#### Estimated changes
Modified src/algebraic_geometry/Scheme.lean
- \+ *lemma* Spec_obj_to_LocallyRingedSpace
- \+ *lemma* Spec_map_id
- \+ *lemma* Spec_map_comp
- \+ *def* Spec_obj
- \+ *def* Spec_map
- \+/\- *def* Spec

Modified src/algebraic_geometry/Spec.lean
- \+ *lemma* Spec.Top_map_id
- \+ *lemma* Spec.Top_map_comp
- \+ *lemma* Spec.SheafedSpace_map_id
- \+ *lemma* Spec.SheafedSpace_map_comp
- \+ *lemma* Spec.to_PresheafedSpace_obj
- \+ *lemma* Spec.to_PresheafedSpace_obj_op
- \+ *lemma* Spec.to_PresheafedSpace_map
- \+ *lemma* Spec.to_PresheafedSpace_map_op
- \+ *lemma* stalk_map_to_stalk
- \+ *lemma* local_ring_hom_comp_stalk_iso
- \+ *lemma* Spec.LocallyRingedSpace_map_id
- \+ *lemma* Spec.LocallyRingedSpace_map_comp
- \+ *def* Spec.Top_obj
- \+ *def* Spec.Top_map
- \+ *def* Spec.to_Top
- \+ *def* Spec.SheafedSpace_obj
- \+ *def* Spec.SheafedSpace_map
- \+ *def* Spec.to_SheafedSpace
- \+ *def* Spec.to_PresheafedSpace
- \+ *def* Spec.LocallyRingedSpace_obj
- \+ *def* Spec.LocallyRingedSpace_map
- \+ *def* Spec.to_LocallyRingedSpace
- \- *def* Spec.SheafedSpace
- \- *def* Spec.PresheafedSpace
- \- *def* Spec.LocallyRingedSpace



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
- \+/\- *lemma* integral_eq_zero_iff_of_le_of_nonneg_ae
- \+/\- *lemma* integral_eq_zero_iff_of_nonneg_ae
- \+/\- *lemma* integral_pos_iff_support_of_nonneg_ae'
- \+/\- *lemma* integral_pos_iff_support_of_nonneg_ae
- \+/\- *lemma* integral_nonneg_of_ae_restrict
- \+/\- *lemma* integral_nonneg_of_ae
- \+/\- *lemma* integral_nonneg
- \+/\- *lemma* integral_mono_ae_restrict
- \+/\- *lemma* integral_mono_on



## [2021-06-15 23:35:54](https://github.com/leanprover-community/mathlib/commit/45619c7)
feat(order/iterate): id_le lemmas ([#7943](https://github.com/leanprover-community/mathlib/pull/7943))
#### Estimated changes
Modified src/order/iterate.lean
- \+ *lemma* id_le_iterate_of_id_le
- \+ *lemma* iterate_le_id_of_le_id
- \+ *lemma* iterate_le_iterate_of_id_le
- \+ *lemma* iterate_le_iterate_of_le_id



## [2021-06-15 23:35:52](https://github.com/leanprover-community/mathlib/commit/e5c97e1)
feat(analysis/convex/basic): a linear map is convex and concave ([#7934](https://github.com/leanprover-community/mathlib/pull/7934))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* linear_map.convex_on
- \+ *lemma* linear_map.concave_on



## [2021-06-15 19:56:41](https://github.com/leanprover-community/mathlib/commit/f1f4c23)
feat(analysis/convex/basic): convex_on lemmas ([#7933](https://github.com/leanprover-community/mathlib/pull/7933))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_on.le_on_segment'
- \+/\- *lemma* concave_on.le_on_segment'
- \+/\- *lemma* convex_on.le_on_segment
- \+ *lemma* convex_on.le_left_of_right_le'
- \+ *lemma* concave_on.left_le_of_le_right'
- \+ *lemma* convex_on.le_right_of_left_le'
- \+ *lemma* concave_on.le_right_of_left_le'
- \+ *lemma* convex_on.le_left_of_right_le
- \+ *lemma* concave_on.left_le_of_le_right
- \+ *lemma* convex_on.le_right_of_left_le
- \+ *lemma* concave_on.le_right_of_left_le



## [2021-06-15 19:56:40](https://github.com/leanprover-community/mathlib/commit/5d03dcd)
feat(analysis/normed_space/dual): add eq_zero_of_forall_dual_eq_zero ([#7929](https://github.com/leanprover-community/mathlib/pull/7929))
The variable `𝕜` is made explicit in `norm_le_dual_bound` because lean can otherwise not guess it in the proof of `eq_zero_of_forall_dual_eq_zero`.
#### Estimated changes
Modified src/analysis/normed_space/dual.lean
- \+ *lemma* eq_zero_of_forall_dual_eq_zero



## [2021-06-15 19:56:39](https://github.com/leanprover-community/mathlib/commit/e5ff5fb)
feat(data/finsupp/basic): equiv_congr_left ([#7755](https://github.com/leanprover-community/mathlib/pull/7755))
As [requested on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Group.20cohomology/near/240737546).
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \+ *lemma* equiv_map_domain_apply
- \+ *lemma* equiv_map_domain_symm_apply
- \+ *lemma* equiv_map_domain_refl
- \+ *lemma* equiv_map_domain_refl'
- \+ *lemma* equiv_map_domain_trans
- \+ *lemma* equiv_map_domain_trans'
- \+ *lemma* equiv_map_domain_single
- \+ *lemma* equiv_map_domain_zero
- \+ *lemma* equiv_map_domain_eq_map_domain
- \+ *lemma* equiv_congr_left_apply
- \+ *lemma* equiv_congr_left_symm
- \+ *def* equiv_map_domain
- \+ *def* equiv_congr_left

Modified src/linear_algebra/finsupp.lean




## [2021-06-15 14:54:47](https://github.com/leanprover-community/mathlib/commit/2f1f34a)
feat(measure_theory/lp_space): add `mem_Lp.mono_measure` ([#7927](https://github.com/leanprover-community/mathlib/pull/7927))
also add monotonicity lemmas wrt the measure for `snorm'`, `snorm_ess_sup` and `snorm`.
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm'_mono_measure
- \+ *lemma* snorm_ess_sup_mono_measure
- \+ *lemma* snorm_mono_measure
- \+ *lemma* mem_ℒp.mono_measure
- \+ *lemma* mem_ℒp.restrict



## [2021-06-15 14:54:46](https://github.com/leanprover-community/mathlib/commit/5f8cc8e)
docs(undergrad): mark convex, convex hull, and extreme points as done ([#7924](https://github.com/leanprover-community/mathlib/pull/7924))
#### Estimated changes
Modified docs/undergrad.yaml




## [2021-06-15 14:54:44](https://github.com/leanprover-community/mathlib/commit/e4ceee6)
feat(group_theory/order_of_element): Raising to a coprime power is a bijection ([#7923](https://github.com/leanprover-community/mathlib/pull/7923))
If `gcd(|G|,k)=1` then the `k`th power map is a bijection
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* pow_coprime_one
- \+ *lemma* pow_coprime_inv
- \+ *def* pow_coprime



## [2021-06-15 14:54:41](https://github.com/leanprover-community/mathlib/commit/f4991b9)
feat(measure_theory/bochner_integration): properties of simple functions (mem_Lp, integrable, fin_meas_supp) ([#7918](https://github.com/leanprover-community/mathlib/pull/7918))
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* exists_forall_norm_le
- \+ *lemma* mem_ℒp_zero
- \+ *lemma* mem_ℒp_top
- \+ *lemma* measure_preimage_lt_top_of_mem_ℒp
- \+ *lemma* mem_ℒp_of_finite_measure_preimage
- \+ *lemma* mem_ℒp_iff
- \+ *lemma* integrable_iff
- \+ *lemma* mem_ℒp_iff_integrable
- \+ *lemma* mem_ℒp_iff_fin_meas_supp
- \+/\- *lemma* integrable_iff_fin_meas_supp
- \+ *lemma* mem_ℒp_of_finite_measure
- \+ *lemma* integrable_of_finite_measure
- \+ *lemma* measure_preimage_lt_top_of_integrable

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_ess_sup_le_of_ae_bound
- \+ *lemma* snorm_ess_sup_lt_top_of_ae_bound
- \+ *lemma* mem_ℒp_top_of_bound



## [2021-06-15 14:54:40](https://github.com/leanprover-community/mathlib/commit/b19c491)
chore(order/lattice): rename le_sup_left_of_le ([#7856](https://github.com/leanprover-community/mathlib/pull/7856))
rename `le_sup_left_of_le` to `le_sup_of_le_left`, and variants
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/order_functions.lean
- \+ *lemma* le_max_of_le_left
- \+ *lemma* le_max_of_le_right
- \+ *lemma* min_le_of_left_le
- \+ *lemma* min_le_of_right_le
- \- *lemma* le_max_left_of_le
- \- *lemma* le_max_right_of_le
- \- *lemma* min_le_left_of_le
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
- \+ *theorem* le_sup_of_le_left
- \+ *theorem* le_sup_of_le_right
- \+ *theorem* inf_le_of_left_le
- \+ *theorem* inf_le_of_right_le
- \- *theorem* le_sup_left_of_le
- \- *theorem* le_sup_right_of_le
- \- *theorem* inf_le_left_of_le
- \- *theorem* inf_le_right_of_le

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
- \+ *lemma* linear_equiv_map_smul
- \+ *def* linear_equiv



## [2021-06-15 14:54:38](https://github.com/leanprover-community/mathlib/commit/a16650c)
feat(geometry/manifold/algebra/smooth_functions): add `coe_fn_(linear_map|ring_hom|alg_hom)` ([#7749](https://github.com/leanprover-community/mathlib/pull/7749))
Changed names to be consistent with the topology library and proven that some coercions are morphisms.
#### Estimated changes
Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *lemma* coe_inv
- \+ *lemma* coe_div
- \+ *lemma* coe_smul
- \+ *lemma* smul_comp
- \+ *lemma* smul_comp'
- \- *lemma* smooth_map.coe_inv
- \- *lemma* smooth_map.coe_div
- \- *lemma* smooth_map.coe_smul
- \- *lemma* smooth_map.smul_comp
- \- *lemma* smooth_map.smul_comp'
- \+ *def* coe_fn_monoid_hom
- \+ *def* coe_fn_ring_hom
- \+ *def* coe_fn_linear_map
- \+ *def* C
- \+ *def* coe_fn_alg_hom
- \- *def* smooth_map.C



## [2021-06-15 06:03:53](https://github.com/leanprover-community/mathlib/commit/bf83c30)
chore(algebra/{ordered_monoid_lemmas, ordered_monoid}): move two sections close together ([#7921](https://github.com/leanprover-community/mathlib/pull/7921))
This PR aims at shortening the diff between `master` and PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) of the order refactor.
I moved the `mono` section of `algebra/ordered_monoid_lemmas` to the end of the file and appended the `strict_mono` section of `algebra/ordered_monoid` after that.
Note: the hypotheses are not optimal, but, with the current `instances` in this version, I did not know how to improve this.  It will get better by the time PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645) is merged.  In fact, the next PR in the sequence, [#7876](https://github.com/leanprover-community/mathlib/pull/7876), already removes the unnecessary assumptions.
#### Estimated changes
Modified src/algebra/ordered_monoid.lean
- \- *lemma* monotone.mul_strict_mono'
- \- *lemma* strict_mono.mul_monotone'
- \- *lemma* strict_mono.mul_const'
- \- *lemma* strict_mono.const_mul'

Modified src/algebra/ordered_monoid_lemmas.lean
- \+/\- *lemma* monotone.mul'
- \+/\- *lemma* monotone.mul_const'
- \+/\- *lemma* monotone.const_mul'
- \+ *lemma* strict_mono.const_mul'
- \+ *lemma* strict_mono.mul_const'
- \+ *lemma* monotone.mul_strict_mono'
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
- \+/\- *lemma* glue_dist_glued_points
- \+/\- *lemma* sum.dist_eq_glue_dist
- \+/\- *lemma* sum.one_dist_le
- \+/\- *lemma* sum.one_dist_le'
- \+/\- *lemma* sum.dist_eq
- \+/\- *lemma* isometry_on_inl
- \+/\- *lemma* isometry_on_inr
- \+/\- *lemma* inductive_limit_dist_eq_dist
- \+/\- *lemma* to_inductive_limit_isometry
- \+/\- *lemma* to_inductive_limit_commute
- \+/\- *def* glue_dist
- \+/\- *def* glue_metric_approx
- \+/\- *def* sum.dist
- \+/\- *def* metric_space_sum
- \+/\- *def* glue_premetric
- \+/\- *def* to_glue_l
- \+/\- *def* to_glue_r
- \+/\- *def* inductive_limit_dist
- \+/\- *def* inductive_premetric
- \+/\- *def* inductive_limit
- \+/\- *def* to_inductive_limit

Modified src/topology/metric_space/gromov_hausdorff.lean
- \+/\- *lemma* eq_to_GH_space_iff
- \+/\- *lemma* to_GH_space_eq_to_GH_space_iff_isometric
- \+/\- *lemma* Hausdorff_dist_optimal
- \+/\- *theorem* GH_dist_le_Hausdorff_dist
- \+/\- *theorem* GH_dist_eq_Hausdorff_dist
- \+/\- *theorem* GH_dist_le_nonempty_compacts_dist
- \+/\- *theorem* GH_dist_le_of_approx_subsets
- \+/\- *def* GH_dist

Modified src/topology/metric_space/gromov_hausdorff_realized.lean
- \+/\- *lemma* candidates_b_of_candidates_mem
- \+/\- *lemma* candidates_b_dist_mem_candidates_b
- \+/\- *lemma* HD_below_aux1
- \+/\- *lemma* HD_below_aux2
- \+/\- *lemma* isometry_optimal_GH_injl
- \+/\- *lemma* isometry_optimal_GH_injr
- \+/\- *lemma* Hausdorff_dist_optimal_le_HD
- \+/\- *def* candidates
- \+/\- *def* candidates_b_of_candidates
- \+/\- *def* candidates_b_dist
- \+/\- *def* HD
- \+/\- *def* premetric_optimal_GH_dist
- \+/\- *def* optimal_GH_injl
- \+/\- *def* optimal_GH_injr



## [2021-06-15 03:22:07](https://github.com/leanprover-community/mathlib/commit/a83f2c2)
feat(group_theory/order_of_element): Power of subset is subgroup ([#7915](https://github.com/leanprover-community/mathlib/pull/7915))
If `S` is a nonempty subset of `G`, then `S ^ |G|` is a subgroup of `G`.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *def* submonoid_of_idempotent
- \+ *def* subgroup_of_idempotent
- \+ *def* pow_card_subgroup

Modified src/group_theory/specific_groups/cyclic.lean




## [2021-06-15 03:22:06](https://github.com/leanprover-community/mathlib/commit/ba25bb8)
feat(measure_theory): define `measure.trim`, restriction of a measure to a sub-sigma algebra ([#7906](https://github.com/leanprover-community/mathlib/pull/7906))
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself is not a measure on `m`. For `hm : m ≤ m0`, we define the measure `μ.trim hm` on `m`.
We add lemmas relating a measure and its trimmed version, mostly about integrals of `m`-measurable functions.
#### Estimated changes
Modified src/measure_theory/arithmetic.lean
- \+ *lemma* measurable_set_eq_fun

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* simple_func.integral_eq_sum
- \+ *lemma* simple_func.coe_to_larger_space_eq
- \+ *lemma* integral_simple_func_larger_space
- \+ *lemma* integral_trim_simple_func
- \+ *lemma* integral_trim
- \+ *lemma* integral_trim_ae
- \+ *lemma* ae_eq_trim_of_measurable
- \+ *lemma* ae_eq_trim_iff
- \+ *def* simple_func.to_larger_space

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_trim
- \+ *lemma* lintegral_trim_ae

Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.trim
- \+ *lemma* integrable_of_integrable_trim

Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm'_trim
- \+ *lemma* limsup_trim
- \+ *lemma* ess_sup_trim
- \+ *lemma* snorm_ess_sup_trim
- \+ *lemma* snorm_trim

Modified src/measure_theory/measure_space.lean
- \+ *lemma* outer_measure.to_measure_zero
- \+ *lemma* trim_eq_self
- \+ *lemma* to_outer_measure_trim_eq_trim_to_outer_measure
- \+ *lemma* zero_trim
- \+ *lemma* trim_measurable_set_eq
- \+ *lemma* le_trim
- \+ *lemma* measure_eq_zero_of_trim_eq_zero
- \+ *lemma* measure_trim_to_measurable_eq_zero
- \+ *lemma* ae_eq_of_ae_eq_trim
- \+ *lemma* restrict_trim
- \+ *lemma* ae_measurable_of_ae_measurable_trim
- \+ *def* measure.trim

Modified src/measure_theory/set_integral.lean
- \+ *lemma* set_integral_trim



## [2021-06-14 21:50:17](https://github.com/leanprover-community/mathlib/commit/8377a1f)
feat(measure_theory/lp_space): add snorm_le_snorm_mul_rpow_measure_univ ([#7926](https://github.com/leanprover-community/mathlib/pull/7926))
There were already versions of this lemma for `snorm'` and `snorm_ess_sup`. The new lemma collates these into a statement about `snorm`.
#### Estimated changes
Modified src/measure_theory/lp_space.lean
- \+ *lemma* snorm_le_snorm_mul_rpow_measure_univ



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
- \+ *lemma* sin_antiperiodic
- \+ *lemma* sin_periodic
- \+/\- *lemma* sin_add_pi
- \+/\- *lemma* sin_add_two_pi
- \+ *lemma* sin_sub_pi
- \+/\- *lemma* sin_sub_two_pi
- \+/\- *lemma* sin_pi_sub
- \+ *lemma* sin_two_pi_sub
- \+/\- *lemma* sin_nat_mul_pi
- \+/\- *lemma* sin_int_mul_pi
- \+/\- *lemma* sin_add_nat_mul_two_pi
- \+/\- *lemma* sin_add_int_mul_two_pi
- \+/\- *lemma* sin_sub_nat_mul_two_pi
- \+/\- *lemma* sin_sub_int_mul_two_pi
- \+ *lemma* sin_nat_mul_two_pi_sub
- \+ *lemma* sin_int_mul_two_pi_sub
- \+ *lemma* cos_antiperiodic
- \+ *lemma* cos_periodic
- \+/\- *lemma* cos_add_pi
- \+/\- *lemma* cos_sub_pi
- \+/\- *lemma* cos_pi_sub
- \+ *lemma* cos_two_pi_sub
- \+/\- *lemma* cos_nat_mul_two_pi
- \+/\- *lemma* cos_int_mul_two_pi
- \+/\- *lemma* cos_add_nat_mul_two_pi
- \+/\- *lemma* cos_add_int_mul_two_pi
- \+/\- *lemma* cos_sub_nat_mul_two_pi
- \+/\- *lemma* cos_sub_int_mul_two_pi
- \+ *lemma* cos_nat_mul_two_pi_sub
- \+ *lemma* cos_int_mul_two_pi_sub
- \+/\- *lemma* cos_nat_mul_two_pi_add_pi
- \+/\- *lemma* cos_int_mul_two_pi_add_pi
- \+/\- *lemma* cos_nat_mul_two_pi_sub_pi
- \+/\- *lemma* cos_int_mul_two_pi_sub_pi
- \+/\- *lemma* cos_add_two_pi
- \+ *lemma* cos_sub_two_pi
- \+ *lemma* tan_periodic
- \+ *lemma* tan_add_pi
- \+ *lemma* tan_sub_pi
- \+ *lemma* tan_pi_sub
- \+ *lemma* tan_nat_mul_pi
- \+/\- *lemma* tan_int_mul_pi
- \+ *lemma* tan_add_nat_mul_pi
- \+ *lemma* tan_add_int_mul_pi
- \+ *lemma* tan_sub_nat_mul_pi
- \+ *lemma* tan_sub_int_mul_pi
- \+ *lemma* tan_nat_mul_pi_sub
- \+ *lemma* tan_int_mul_pi_sub
- \+ *lemma* exp_antiperiodic
- \+ *lemma* exp_periodic
- \+ *lemma* exp_mul_I_antiperiodic
- \+ *lemma* exp_mul_I_periodic
- \+ *lemma* exp_two_pi_mul_I
- \+ *lemma* exp_nat_mul_two_pi_mul_I
- \+ *lemma* exp_int_mul_two_pi_mul_I



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
- \+ *def* generate_from
- \+ *def* neighbourhood



## [2021-06-14 21:50:13](https://github.com/leanprover-community/mathlib/commit/f781c47)
feat(linear_algebra/determinant): specialize `linear_equiv.is_unit_det` to automorphisms ([#7667](https://github.com/leanprover-community/mathlib/pull/7667))
`linear_equiv.is_unit_det` is defined for all equivs between equal-dimensional spaces, using `det (linear_map.to_matrix _ _ _)`, but I needed this result for `linear_map.det _` (which only exists between the exact same space). So I added the specialization `linear_equiv.is_unit_det'`.
#### Estimated changes
Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_cases
- \+ *lemma* linear_equiv.is_unit_det'



## [2021-06-14 21:50:12](https://github.com/leanprover-community/mathlib/commit/615af75)
feat(measure_theory/interval_integral): `integral_deriv_comp_mul_deriv` ([#7141](https://github.com/leanprover-community/mathlib/pull/7141))
`∫ x in a..b, (g ∘ f) x * f' x`, where `f'` is derivative of `f` and `g` is the derivative of some function (the latter qualification allowing us to compute the integral directly by FTC-2)
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \- *lemma* integral_deriv_mul_eq_sub
- \+ *theorem* integral_deriv_mul_eq_sub
- \+ *theorem* integral_deriv_comp_mul_deriv'
- \+ *theorem* integral_deriv_comp_mul_deriv

Modified test/integration.lean




## [2021-06-14 12:40:22](https://github.com/leanprover-community/mathlib/commit/386962c)
feat(algebra/char_zero): `neg_eq_self_iff` ([#7916](https://github.com/leanprover-community/mathlib/pull/7916))
`-a = a ↔ a = 0` and `a = -a ↔ a = 0`.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* neg_eq_self_iff
- \+ *lemma* eq_neg_self_iff



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
- \+ *lemma* mem_inner_dual_cone
- \+ *lemma* inner_dual_cone_empty
- \+ *lemma* inner_dual_cone_le_inner_dual_cone
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
- \+ *lemma* ess_sup_le_of_ae_le
- \+ *lemma* le_ess_inf_of_ae_le
- \+ *lemma* ess_sup_mono_measure
- \+ *lemma* ess_inf_antimono_measure
- \+/\- *lemma* ess_sup_eq_zero_iff
- \+/\- *lemma* ess_sup_const_mul

Modified src/order/liminf_limsup.lean
- \+ *lemma* limsup_le_limsup_of_le
- \+ *lemma* liminf_le_liminf_of_le



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
- \+ *lemma* integral_eq_integral_pos_part_sub_integral_neg_part

Modified src/measure_theory/borel_space.lean
- \+ *lemma* upper_semicontinuous.measurable
- \+ *lemma* lower_semicontinuous.measurable
- \+ *lemma* measurable_real_to_nnreal
- \+ *lemma* measurable_coe_nnreal_real
- \+ *lemma* measurable.coe_nnreal_real
- \+ *lemma* ae_measurable.coe_nnreal_real
- \+ *lemma* measurable_coe_nnreal_ennreal
- \+ *lemma* measurable.coe_nnreal_ennreal
- \+ *lemma* ae_measurable.coe_nnreal_ennreal
- \+ *lemma* measurable.ennreal_to_nnreal
- \+ *lemma* ae_measurable.ennreal_to_nnreal
- \+ *lemma* measurable_coe_nnreal_ennreal_iff
- \+ *lemma* measurable.ennreal_to_real
- \+ *lemma* ae_measurable.ennreal_to_real
- \+ *lemma* measurable_coe_real_ereal
- \+ *lemma* measurable.coe_real_ereal
- \+ *lemma* ae_measurable.coe_real_ereal
- \+ *lemma* ereal.measurable_of_measurable_real
- \+ *lemma* measurable_ereal_to_real
- \+ *lemma* measurable.ereal_to_real
- \+ *lemma* ae_measurable.ereal_to_real
- \+ *lemma* measurable_coe_ennreal_ereal
- \+ *lemma* measurable.coe_ereal_ennreal
- \+ *lemma* ae_measurable.coe_ereal_ennreal
- \- *lemma* nnreal.measurable_coe
- \- *lemma* measurable.nnreal_coe
- \- *lemma* ae_measurable.nnreal_coe
- \- *lemma* measurable.ennreal_coe
- \- *lemma* ae_measurable.ennreal_coe
- \- *lemma* measurable_coe
- \- *lemma* measurable.to_nnreal
- \- *lemma* measurable_ennreal_coe_iff
- \- *lemma* measurable.to_real
- \- *lemma* ae_measurable.to_real
- \+ *def* measurable_equiv.ereal_equiv_real

Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable.real_to_nnreal

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
- \+ *lemma* Iic_inter_Ioc_of_le

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* interval_oc_of_le
- \+ *lemma* interval_oc_of_lt
- \+ *lemma* forall_interval_oc_iff
- \+ *def* interval_oc

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* ae_interval_oc_iff
- \+ *lemma* ae_measurable_interval_oc_iff
- \+ *lemma* ae_interval_oc_iff'
- \+ *lemma* interval_integrable.norm
- \+ *lemma* integral_Icc_eq_integral_Ioc
- \+ *lemma* integral_congr_ae'
- \+ *lemma* integral_congr_ae
- \+ *lemma* integral_zero_ae
- \+ *lemma* integral_indicator
- \+ *lemma* continuous_within_at_of_dominated_interval
- \+ *lemma* continuous_at_of_dominated_interval
- \+ *lemma* continuous_of_dominated_interval
- \+ *lemma* continuous_within_at_primitive
- \+ *lemma* continuous_on_primitive
- \+ *lemma* continuous_on_primitive'
- \+ *lemma* continuous_on_primitive''
- \+ *lemma* continuous_primitive
- \+ *lemma* _root_.measure_theory.integrable.continuous_primitive

Modified src/measure_theory/measure_space.lean
- \+ *lemma* restrict_zero_set
- \+ *lemma* measure.restrict_singleton'



## [2021-06-13 11:45:04](https://github.com/leanprover-community/mathlib/commit/6d2a051)
feat(algebra/covariant_and_contravariant): API for covariant_and_contravariant ([#7889](https://github.com/leanprover-community/mathlib/pull/7889))
This PR introduces more API for `covariant` and `contravariant` stuff .
Besides the API, I have not actually made further use of the typeclasses or of the API.  This happens in subsequent PRs.
This is a step towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* rel_iff_cov
- \+ *lemma* act_rel_act_of_rel
- \+ *lemma* group.covariant_iff_contravariant
- \+ *lemma* covconv
- \+ *lemma* act_rel_of_rel_of_act_rel
- \+ *lemma* rel_act_of_rel_of_rel_act
- \+ *lemma* act_rel_act_of_rel_of_rel
- \+ *lemma* rel_of_act_rel_act
- \+ *lemma* act_rel_of_act_rel_of_rel_act_rel
- \+ *lemma* rel_act_of_act_rel_act_of_rel_act
- \+ *lemma* covariant_le_of_covariant_lt
- \+ *lemma* contravariant_lt_of_contravariant_le
- \+ *lemma* covariant_le_iff_contravariant_lt
- \+ *lemma* covariant_lt_iff_contravariant_le
- \+ *lemma* covariant_flip_mul_iff
- \+ *lemma* contravariant_flip_mul_iff
- \+/\- *def* contravariant

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
- \+ *theorem* unpair_left_le
- \+ *theorem* left_le_mkpair
- \+ *theorem* right_le_mkpair
- \+ *theorem* unpair_right_le
- \- *theorem* unpair_le_left
- \- *theorem* le_mkpair_left
- \- *theorem* le_mkpair_right
- \- *theorem* unpair_le_right



## [2021-06-13 06:04:51](https://github.com/leanprover-community/mathlib/commit/2c919b0)
chore(algebra/{ordered_group, linear_ordered_comm_group_with_zero.lean}): rename one lemma, remove more @s ([#7895](https://github.com/leanprover-community/mathlib/pull/7895))
The more substantial part of this PR is changing the name of a lemma from `div_lt_div_iff'` to `mul_inv_lt_mul_inv_iff'`: the lemma proves `a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b`.
Furthermore, in the same spirit as a couple of my recent short PRs, I am removing a few more `@`, in order to sweep under the rug, later on, a change in typeclass assumptions.  This PR only changes a name, which was used only once, and a few proofs, but no statement.
On the path towards PR [#7645](https://github.com/leanprover-community/mathlib/pull/7645).
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean
- \+ *lemma* mul_inv_le_mul_inv_iff'
- \- *lemma* div_le_div_iff'



## [2021-06-13 06:04:50](https://github.com/leanprover-community/mathlib/commit/add577d)
feat(group_theory/group_action/defs): add `has_mul.to_has_scalar` and relax typeclass in `smul_mul_smul` ([#7885](https://github.com/leanprover-community/mathlib/pull/7885))
#### Estimated changes
Modified src/data/matrix/basic.lean


Modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* mul_smul_comm
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
- \+ *lemma* empty_pow
- \+ *lemma* card_pow_eq_card_pow_card_univ_aux
- \+ *lemma* card_pow_eq_card_pow_card_univ



## [2021-06-12 15:55:02](https://github.com/leanprover-community/mathlib/commit/ee4fe74)
feat(topology/category/Profinite/cofiltered_clopen): Theorem about clopen sets in cofiltered limits of profinite sets ([#7837](https://github.com/leanprover-community/mathlib/pull/7837))
This PR proves the theorem that any clopen set in a cofiltered limit of profinite sets arises from a clopen set in one of the factors of the limit.
This generalizes a theorem used in LTE.
#### Estimated changes
Created src/topology/category/Profinite/cofiltered_limit.lean
- \+ *theorem* exists_clopen_of_cofiltered



## [2021-06-12 15:55:00](https://github.com/leanprover-community/mathlib/commit/06094d5)
feat(linear_algebra/free_module): add class module.free ([#7801](https://github.com/leanprover-community/mathlib/pull/7801))
We introduce here a new class `module.free`.
#### Estimated changes
Created src/linear_algebra/free_module.lean
- \+ *lemma* module.free_def
- \+ *lemma* module.free_iff_set
- \+ *lemma* module.free.of_basis
- \+ *lemma* of_equiv
- \+ *lemma* of_equiv'
- \+ *def* choose_basis_index



## [2021-06-12 15:54:59](https://github.com/leanprover-community/mathlib/commit/f9935ed)
feat(geometry/manifold): Some lemmas for smooth functions ([#7752](https://github.com/leanprover-community/mathlib/pull/7752))
#### Estimated changes
Modified src/geometry/manifold/algebra/lie_group.lean


Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* L_apply
- \+ *lemma* R_apply
- \+ *lemma* L_mul
- \+ *lemma* R_mul
- \+ *def* smooth_left_mul
- \+ *def* smooth_right_mul

Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *lemma* mul_comp
- \+ *lemma* smooth_map.smul_comp
- \+ *lemma* smooth_map.smul_comp'



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
- \+ *theorem* sqrt_le'
- \+ *theorem* lt_succ_sqrt'
- \+ *theorem* le_sqrt'
- \+ *theorem* sqrt_lt'
- \+ *theorem* eq_sqrt'
- \+ *theorem* sqrt_add_eq'
- \+ *theorem* sqrt_eq'
- \+ *theorem* exists_mul_self'
- \+ *theorem* sqrt_mul_sqrt_lt_succ'
- \+ *theorem* succ_le_succ_sqrt'
- \+ *theorem* not_exists_sq'



## [2021-06-12 11:10:09](https://github.com/leanprover-community/mathlib/commit/841dce1)
feat(data/polynomial): generalize `polynomial.has_scalar` to require only `distrib_mul_action` instead of `semimodule` ([#7664](https://github.com/leanprover-community/mathlib/pull/7664))
Note that by generalizing this instance, we introduce a diamond with `polynomial.mul_semiring_action`, which has a definitionally different `smul`. To resolve this, we add a proof that the definitions are equivalent, and switch `polynomial.mul_semiring_action` to use the same implementation as `polynomial.has_scalar`. This allows us to generalize `smul_C` to apply to all types of action, and remove `coeff_smul'` which then duplicates the statement of `coeff_smul`.
#### Estimated changes
Modified src/algebra/polynomial/group_ring_action.lean
- \+ *lemma* smul_eq_map
- \- *lemma* coeff_smul'
- \- *lemma* smul_C

Modified src/data/polynomial/basic.lean
- \+/\- *lemma* smul_to_finsupp
- \+/\- *lemma* smul_monomial
- \+ *lemma* smul_C

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* support_smul



## [2021-06-12 08:06:06](https://github.com/leanprover-community/mathlib/commit/2016a93)
feat(linear_algebra): use `finset`s to define `det` and `trace` ([#7778](https://github.com/leanprover-community/mathlib/pull/7778))
This PR replaces `∃ (s : set M) (b : basis s R M), s.finite` with `∃ (s : finset M), nonempty (basis s R M)` in the definitions in `linear_map.det` and `linear_map.trace`. This should make it much easier to unfold those definitions without having to modify the instance cache or supply implicit params.
In particular, it should help a lot with [#7667](https://github.com/leanprover-community/mathlib/pull/7667).
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* reindex_finset_range_self
- \+ *lemma* reindex_finset_range_apply
- \+ *lemma* reindex_finset_range_repr_self
- \+ *lemma* reindex_finset_range_repr
- \+ *def* reindex_finset_range

Modified src/linear_algebra/determinant.lean
- \+ *lemma* det_eq_det_to_matrix_of_finset
- \- *lemma* det_eq_det_to_matrix_of_finite_set

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finrank_eq_zero_of_not_exists_basis_finset

Modified src/linear_algebra/trace.lean
- \+ *theorem* trace_eq_matrix_trace_of_finset
- \- *theorem* trace_aux_reindex_range
- \- *theorem* trace_eq_matrix_trace_of_finite_set

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




## [2021-06-12 02:38:03](https://github.com/leanprover-community/mathlib/commit/55c9662)
chore(scripts): update nolints.txt ([#7902](https://github.com/leanprover-community/mathlib/pull/7902))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-06-12 02:38:02](https://github.com/leanprover-community/mathlib/commit/2974a9f)
feat(ring_theory): every division_ring is_noetherian ([#7661](https://github.com/leanprover-community/mathlib/pull/7661))
#### Estimated changes
Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* span_singleton_one
- \+ *lemma* span_one
- \+/\- *lemma* eq_bot_or_top
- \+/\- *lemma* eq_bot_of_prime
- \+/\- *lemma* bot_is_maximal

Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* mem_iff_generator_dvd
- \+/\- *lemma* is_maximal_of_irreducible



## [2021-06-12 02:38:01](https://github.com/leanprover-community/mathlib/commit/5948cde)
feat(ring_theory): the field trace resp. norm is the sum resp. product of the conjugates ([#7640](https://github.com/leanprover-community/mathlib/pull/7640))
More precise statement of the main result: the field trace (resp. norm) of `x` in `K(x) / K`, mapped to a field `F` that contains all the conjugate roots over `K` of `x`, is equal to the sum (resp. product) of all of these conjugate roots.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* adjoin_simple.is_integral_gen

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* total_fin_zero

Modified src/ring_theory/norm.lean
- \+ *lemma* norm_gen_eq_prod_roots

Modified src/ring_theory/trace.lean
- \+ *lemma* trace_gen_eq_sum_roots



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
- \+ *lemma* integral_sin_pow_mul_cos_pow_odd
- \+ *lemma* integral_sin_mul_cos₁
- \+ *lemma* integral_sin_sq_mul_cos
- \+ *lemma* integral_cos_pow_three
- \+ *lemma* integral_sin_pow_odd_mul_cos_pow
- \+ *lemma* integral_sin_mul_cos₂
- \+ *lemma* integral_sin_mul_cos_sq
- \+ *lemma* integral_sin_pow_three
- \+ *lemma* integral_sin_pow_even_mul_cos_pow_even
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
Created src/algebra/covariant_and_contravariant.lean
- \+ *def* covariant
- \+ *def* contravariant

Modified src/algebra/ordered_monoid_lemmas.lean
- \- *def* covariant
- \- *def* contravariant



## [2021-06-11 21:18:47](https://github.com/leanprover-community/mathlib/commit/538f015)
feat(data/finset/basic): `empty_product` and `product_empty` ([#7886](https://github.com/leanprover-community/mathlib/pull/7886))
add `product_empty_<left/right>`
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* empty_product
- \+ *lemma* product_empty



## [2021-06-11 21:18:46](https://github.com/leanprover-community/mathlib/commit/97a7a24)
doc(data/pequiv): add module docs ([#7877](https://github.com/leanprover-community/mathlib/pull/7877))
#### Estimated changes
Modified src/data/pequiv.lean




## [2021-06-11 21:18:45](https://github.com/leanprover-community/mathlib/commit/ff44ed5)
feat({algebra/group_action_hom, data/equiv/mul_add}): add missing `inverse` defs ([#7847](https://github.com/leanprover-community/mathlib/pull/7847))
#### Estimated changes
Modified src/algebra/group_action_hom.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* zero_apply
- \+ *lemma* one_apply
- \+ *def* inverse

Modified src/data/equiv/mul_add.lean
- \+ *def* monoid_hom.inverse



## [2021-06-11 21:18:44](https://github.com/leanprover-community/mathlib/commit/a008b33)
feat(data/finsupp/to_dfinsupp): add sigma_finsupp_lequiv_dfinsupp ([#7818](https://github.com/leanprover-community/mathlib/pull/7818))
Equivalences between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`.
- [x] depends on: [#7819](https://github.com/leanprover-community/mathlib/pull/7819)
#### Estimated changes
Modified src/data/finsupp/to_dfinsupp.lean
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_apply
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_symm_apply
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_support
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_add
- \+ *lemma* sigma_finsupp_equiv_dfinsupp_smul
- \+ *def* sigma_finsupp_equiv_dfinsupp
- \+ *def* sigma_finsupp_add_equiv_dfinsupp
- \+ *def* sigma_finsupp_lequiv_dfinsupp



## [2021-06-11 21:18:43](https://github.com/leanprover-community/mathlib/commit/64d453e)
feat(ring_theory/adjoin/basic): add subalgebra.fg_prod ([#7811](https://github.com/leanprover-community/mathlib/pull/7811))
We add `subalgebra.fg_prod`: the product of two finitely generated subalgebras is finitely generated.
A mathematical remark: the result is not difficult, but one needs to be careful. For example, `algebra.adjoin_eq_prod` is false without adding `(1,0)` and `(0,1)` by hand to the set of generators. Moreover, `linear_map.inl` and `linear_map.inr` are not ring homomorphisms, so it seems difficult to mimic the proof for modules. A better mathematical proof is to take surjections from two polynomial rings (in finitely many variables) and considering the tensor product of these polynomial rings, that is again a polynomial ring in finitely many variables, and build a surjection to the product of the subalgebras (using the universal property of the tensor product). The problem with this approach is that one needs to know that the tensor product of polynomial rings is again a polynomial ring, and I don't know well enough the API fort the tensor product to prove this.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* fst
- \+ *def* snd

Modified src/field_theory/splitting_field.lean


Modified src/linear_algebra/prod.lean
- \+ *lemma* inl_map_mul
- \+ *lemma* inr_map_mul

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* adjoin_union
- \+ *lemma* adjoin_inl_union_inr_le_prod
- \+ *lemma* mem_adjoin_of_map_mul
- \+ *lemma* adjoin_inl_union_inr_eq_prod
- \+ *lemma* fg_prod
- \+ *theorem* adjoin_induction
- \+ *theorem* adjoin_union_eq_under
- \- *theorem* adjoin_union

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/finiteness.lean




## [2021-06-11 21:18:42](https://github.com/leanprover-community/mathlib/commit/61a04c5)
feat(algebraic_geometry/structure_sheaf): Define comap on structure sheaf ([#7788](https://github.com/leanprover-community/mathlib/pull/7788))
Defines the comap of a ring homomorphism on the structure sheaves of the prime spectra.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean
- \+ *lemma* is_fraction.eq_mk'
- \+ *lemma* structure_sheaf.comap_fun_is_locally_fraction
- \+ *lemma* structure_sheaf.comap_apply
- \+ *lemma* structure_sheaf.comap_const
- \+ *lemma* structure_sheaf.comap_id_eq_map
- \+ *lemma* structure_sheaf.comap_id
- \+ *lemma* structure_sheaf.comap_id'
- \+ *lemma* structure_sheaf.comap_comp
- \+ *lemma* to_open_comp_comap
- \- *lemma* to_open_apply
- \+/\- *def* to_open
- \+/\- *def* stalk_iso
- \+ *def* structure_sheaf.comap_fun
- \+ *def* structure_sheaf.comap



## [2021-06-11 21:18:40](https://github.com/leanprover-community/mathlib/commit/eb9bd55)
feat(linear_algebra/quadratic_form): Real version of Sylvester's law of inertia ([#7427](https://github.com/leanprover-community/mathlib/pull/7427))
We prove that every nondegenerate real quadratic form is equivalent to a weighted sum of squares with the weights being ±1.
#### Estimated changes
Modified docs/undergrad.yaml


Created src/data/real/sign.lean
- \+ *lemma* sign_of_neg
- \+ *lemma* sign_of_not_neg
- \+ *lemma* sign_of_zero_le
- \+ *lemma* sign_zero
- \+ *lemma* sign_one
- \+ *lemma* sign_apply_eq
- \+ *lemma* sign_neg
- \+ *lemma* sign_mul_nonneg
- \+ *lemma* sign_mul_pos_of_ne_zero
- \+ *lemma* inv_sign
- \+ *lemma* sign_inv
- \+ *def* sign

Modified src/linear_algebra/quadratic_form.lean
- \+ *theorem* equivalent_one_neg_one_weighted_sum_squared



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
Created src/number_theory/l_series.lean
- \+ *lemma* l_series_eq_zero_of_not_l_series_summable
- \+ *lemma* l_series_summable_zero
- \+ *theorem* l_series_summable_of_bounded_of_one_lt_real
- \+ *theorem* l_series_summable_iff_of_re_eq_re
- \+ *theorem* l_series_summable_of_bounded_of_one_lt_re
- \+ *theorem* zeta_l_series_summable_iff_one_lt_re
- \+ *theorem* l_series_add
- \+ *def* l_series
- \+ *def* l_series_summable



## [2021-06-11 13:26:17](https://github.com/leanprover-community/mathlib/commit/e35438b)
feat(analysis): Cauchy sequence and series lemmas ([#7858](https://github.com/leanprover-community/mathlib/pull/7858))
from LTE. Mostly relaxing assumptions from metric to
pseudo-metric and proving some obvious lemmas.
eventually_constant_prod and eventually_constant_sum are duplicated by hand because `to_additive` gets confused by the appearance of `1`.
In `norm_le_zero_iff' {G : Type*} [semi_normed_group G] [separated_space G]` and the following two lemmas the type classes assumptions look silly, but those lemmas are indeed useful in some specific situation in LTE.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* eventually_constant_prod
- \+ *lemma* eventually_constant_sum

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_le_insert'
- \+ *lemma* normed_group.cauchy_seq_iff
- \+ *lemma* cauchy_seq.add
- \+ *lemma* cauchy_seq_sum_of_eventually_eq
- \+ *lemma* semi_normed_group.mem_closure_iff
- \+ *lemma* norm_le_zero_iff'
- \+ *lemma* norm_eq_zero_iff'
- \+ *lemma* norm_pos_iff'

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* uniformity_basis_dist_pow_of_lt_1
- \+ *lemma* semi_normed_group.cauchy_seq_of_le_geometric
- \+ *lemma* dist_partial_sum
- \+ *lemma* dist_partial_sum'
- \+ *lemma* cauchy_series_of_le_geometric
- \+ *lemma* normed_group.cauchy_series_of_le_geometric'
- \+ *lemma* normed_group.cauchy_series_of_le_geometric''

Modified src/topology/basic.lean
- \+ *lemma* tendsto_at_top_of_eventually_const
- \+ *lemma* tendsto_at_bot_of_eventually_const



## [2021-06-11 13:26:16](https://github.com/leanprover-community/mathlib/commit/a421185)
feat(algebra/periodic): more periodicity lemmas ([#7853](https://github.com/leanprover-community/mathlib/pull/7853))
#### Estimated changes
Modified src/algebra/periodic.lean
- \+ *lemma* periodic.sub_eq'
- \+ *lemma* periodic.nsmul_sub_eq
- \+ *lemma* periodic.nat_mul_sub_eq
- \+ *lemma* periodic.gsmul_sub_eq
- \+ *lemma* periodic.int_mul_sub_eq
- \+ *lemma* antiperiodic.sub_eq'



## [2021-06-11 13:26:15](https://github.com/leanprover-community/mathlib/commit/9228ff9)
feat(algebra/ordered_group): abs_sub ([#7850](https://github.com/leanprover-community/mathlib/pull/7850))
- rename `abs_sub` to `abs_sub_comm`
- prove `abs_sub`
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/algebra/ordered_group.lean
- \+ *lemma* abs_sub_comm
- \- *lemma* abs_sub
- \+ *theorem* abs_sub

Modified src/data/complex/basic.lean
- \+ *lemma* abs_sub_comm
- \- *lemma* abs_sub

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
- \+ *lemma* tendsto_iff_tendsto_subseq_of_monotone
- \+ *lemma* supr_eq_supr_subseq_of_monotone
- \+ *lemma* infi_eq_infi_subseq_of_monotone



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
- \+ *theorem* mk_range_le_lift



## [2021-06-11 02:16:12](https://github.com/leanprover-community/mathlib/commit/e8aa984)
doc(int/modeq): add module doc and tidy ([#7878](https://github.com/leanprover-community/mathlib/pull/7878))
#### Estimated changes
Modified src/data/int/modeq.lean
- \+/\- *lemma* mod_coprime



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
- \+/\- *lemma* bound
- \+ *lemma* norm_noninc_iff_norm_le_one
- \- *lemma* mk_normed_group_hom'_bound_by
- \- *lemma* lipschitz_of_bound_by
- \- *lemma* bound_by_one
- \- *lemma* bound_by_one_of_isometry
- \+ *theorem* antilipschitz_of_norm_ge
- \- *theorem* antilipschitz_of_bound_by
- \- *def* bound_by

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
- \+ *lemma* nat_floor_of_nonpos
- \+ *lemma* pos_of_nat_floor_pos
- \+ *lemma* nat_floor_le
- \+ *lemma* le_nat_floor_of_le
- \+ *lemma* lt_of_lt_nat_floor
- \+ *lemma* lt_nat_floor_add_one
- \+ *lemma* nat_floor_eq_zero_iff
- \+ *theorem* le_nat_floor_iff
- \+ *theorem* nat_floor_lt_iff
- \+ *theorem* nat_floor_mono
- \+ *theorem* nat_floor_coe
- \+ *theorem* nat_floor_zero
- \+ *theorem* nat_floor_add_nat
- \+/\- *theorem* nat_ceil_le
- \+/\- *theorem* lt_nat_ceil
- \+ *def* nat_floor
- \+/\- *def* nat_ceil

Modified src/data/int/basic.lean
- \+ *lemma* to_nat_add_nat
- \+ *lemma* to_nat_of_nonpos
- \- *lemma* to_nat_add_one
- \- *lemma* to_nat_zero_of_neg

Modified src/tactic/norm_num.lean




## [2021-06-10 16:03:36](https://github.com/leanprover-community/mathlib/commit/021c859)
feat(analysis/special_functions/pow): rpow-log inequalities ([#7848](https://github.com/leanprover-community/mathlib/pull/7848))
Inequalities relating rpow and log
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* le_rpow_iff_log_le
- \+ *lemma* le_rpow_of_log_le
- \+ *lemma* lt_rpow_iff_log_lt
- \+ *lemma* lt_rpow_of_log_lt



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
- \+/\- *lemma* mul_lt_top
- \+ *lemma* mul_def
- \+ *lemma* mul_bot
- \+ *lemma* bot_mul
- \+ *lemma* bot_mul_bot
- \+ *lemma* coe_mul
- \+ *lemma* mul_coe
- \+ *lemma* mul_eq_bot_iff
- \+ *lemma* bot_lt_mul

Modified src/data/real/ereal.lean
- \+ *lemma* add_eq_top_iff
- \+ *lemma* top_sub
- \+ *lemma* sub_bot
- \+ *lemma* bot_sub_top
- \+ *lemma* bot_sub_coe
- \+ *lemma* coe_sub_bot
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* mul_top
- \+ *lemma* top_mul
- \+ *lemma* bot_mul_bot
- \+ *lemma* bot_mul_coe
- \+ *lemma* coe_mul_bot
- \+ *lemma* to_real_one
- \+ *lemma* to_real_mul
- \- *lemma* ad_eq_top_iff

Modified src/order/bounded_lattice.lean




## [2021-06-10 23:57:20+10:00](https://github.com/leanprover-community/mathlib/commit/079b8a1)
Revert "feat(set_theory/cofinality): more infinite pigeonhole principles"
This reverts commit c7ba50f41813718472478983370db66b06c2d33e.
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \- *lemma* le_range_of_union_finset_eq_top
- \- *theorem* infinite_pigeonhole'
- \- *theorem* infinite_pigeonhole''



## [2021-06-10 23:56:13+10:00](https://github.com/leanprover-community/mathlib/commit/c7ba50f)
feat(set_theory/cofinality): more infinite pigeonhole principles
#### Estimated changes
Modified src/set_theory/cofinality.lean
- \+ *lemma* le_range_of_union_finset_eq_top
- \+ *theorem* infinite_pigeonhole'
- \+ *theorem* infinite_pigeonhole''



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
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_pow
- \+ *lemma* coe_inv
- \+ *lemma* coe_div
- \+ *lemma* continuous_functions.coe_smul
- \+ *lemma* coe_smul
- \- *lemma* mul_coe
- \- *lemma* one_coe
- \- *lemma* pow_coe
- \- *lemma* inv_coe
- \- *lemma* div_coe
- \- *lemma* continuous_functions.smul_coe
- \- *lemma* smul_coe



## [2021-06-10 01:51:26](https://github.com/leanprover-community/mathlib/commit/06200c8)
feat(ring_theory/ideal): generalize to noncommutative rings ([#7654](https://github.com/leanprover-community/mathlib/pull/7654))
This is a minimalist generalization of existing material on ideals to the setting of noncommutative rings.
I have not attempted to decide how things should be named in the long run. For now `ideal` specifically means a left-ideal (i.e. I didn't change the definition). We can either in future add `two_sided_ideal` (or `biideal` or `ideal₂` or ...), or potentially rename `ideal` to `left_ideal` or `lideal`, etc. Future bikeshedding opportunities!
In this PR I've just left definitions alone, and relaxed `comm_ring` hypotheses to `ring` as far as I could see possible. No new theorems or mathematics, just rearranging to get things in the right order.
(As a side note, both `ring_theory.ideal.basic` and `ring_theory.ideal.operations` should be split into smaller files; I can try this after this PR.)
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/group/units.lean
- \+ *theorem* is_unit.exists_right_inv
- \+ *theorem* is_unit.exists_left_inv

Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* mem_sup_left
- \+/\- *lemma* mem_sup_right
- \+/\- *lemma* mem_supr_of_mem
- \+/\- *lemma* mem_Sup_of_mem
- \+/\- *lemma* mem_inf
- \+/\- *lemma* mem_infi
- \+/\- *lemma* mem_bot
- \+/\- *lemma* mem_pi
- \+/\- *lemma* mem_span_singleton
- \+/\- *lemma* span_singleton_le_span_singleton
- \+/\- *lemma* span_singleton_eq_span_singleton
- \+/\- *lemma* span_singleton_mul_right_unit
- \+/\- *lemma* span_singleton_mul_left_unit
- \+/\- *lemma* span_singleton_eq_top
- \+/\- *lemma* mul_mem_right
- \+/\- *lemma* pow_mem_of_mem
- \+/\- *theorem* is_maximal.exists_inv
- \+/\- *theorem* mem_Inf
- \+/\- *theorem* mul_unit_mem_iff_mem
- \+/\- *theorem* span_singleton_prime
- \+/\- *theorem* is_maximal.is_prime
- \+/\- *theorem* is_prime.mul_mem_iff_mem_or_mem
- \+/\- *theorem* is_prime.pow_mem_iff_mem
- \+/\- *theorem* mem_nonunits_iff
- \+/\- *theorem* coe_subset_nonunits
- \+/\- *def* ideal
- \+/\- *def* pi

Modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* comap_comap
- \+/\- *lemma* map_map
- \+/\- *lemma* map_of_equiv
- \+/\- *lemma* comap_of_equiv
- \+/\- *lemma* map_comap_of_equiv
- \+/\- *lemma* mem_quotient_iff_mem
- \+/\- *lemma* map_quotient_self
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* mk_ker
- \+/\- *theorem* map_mul
- \+/\- *theorem* comap_radical
- \+/\- *theorem* map_radical_le
- \+/\- *theorem* le_comap_mul

Modified src/ring_theory/ideal/prod.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-06-09 20:42:50](https://github.com/leanprover-community/mathlib/commit/3870896)
doc(data/semiquot): reformat module doc properly, and add missing doc strings ([#7773](https://github.com/leanprover-community/mathlib/pull/7773))
#### Estimated changes
Modified src/data/semiquot.lean
- \+/\- *def* is_pure



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
- \+ *lemma* measurable.mul'
- \+/\- *lemma* measurable.mul
- \+ *lemma* ae_measurable.mul'
- \+/\- *lemma* ae_measurable.mul
- \+ *lemma* measurable.div'
- \+/\- *lemma* measurable.div
- \+ *lemma* ae_measurable.div'
- \+/\- *lemma* ae_measurable.div
- \+/\- *lemma* measurable.inv
- \+/\- *lemma* ae_measurable.inv

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* measurable_set_Ici
- \+/\- *lemma* measurable_set_Iic
- \+/\- *lemma* measurable_set_Icc
- \+/\- *lemma* measurable_set_Iio
- \+/\- *lemma* measurable_set_Ioi
- \+/\- *lemma* measurable_set_Ioo
- \+/\- *lemma* measurable_set_Ioc
- \+/\- *lemma* measurable_set_Ico

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lp_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set_preimage
- \+/\- *lemma* measurable.iterate
- \+/\- *lemma* subsingleton.measurable
- \+/\- *lemma* measurable_set_mul_support
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* measurable_from_nat
- \+/\- *lemma* measurable_subtype_coe
- \+/\- *lemma* measurable.subtype_coe
- \+/\- *lemma* measurable_fst
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable_snd
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable.prod
- \+/\- *lemma* measurable_swap
- \+/\- *lemma* measurable_inl
- \+/\- *lemma* measurable_inr
- \- *lemma* measurable_set.empty
- \- *lemma* measurable_set.compl
- \- *lemma* measurable_set.of_compl
- \- *lemma* measurable_set.compl_iff
- \- *lemma* measurable_set.univ
- \- *lemma* subsingleton.measurable_set
- \- *lemma* measurable_set.congr
- \- *lemma* measurable_set.bUnion_decode₂
- \- *lemma* measurable_set.Union
- \- *lemma* measurable_set.bUnion
- \- *lemma* set.finite.measurable_set_bUnion
- \- *lemma* finset.measurable_set_bUnion
- \- *lemma* measurable_set.sUnion
- \- *lemma* set.finite.measurable_set_sUnion
- \- *lemma* measurable_set.Union_Prop
- \- *lemma* measurable_set.Inter
- \- *lemma* measurable_set.Union_fintype
- \- *lemma* measurable_set.Inter_fintype
- \- *lemma* measurable_set.bInter
- \- *lemma* set.finite.measurable_set_bInter
- \- *lemma* finset.measurable_set_bInter
- \- *lemma* measurable_set.sInter
- \- *lemma* set.finite.measurable_set_sInter
- \- *lemma* measurable_set.Inter_Prop
- \- *lemma* measurable_set.union
- \- *lemma* measurable_set.inter
- \- *lemma* measurable_set.diff
- \- *lemma* measurable_set.ite
- \- *lemma* measurable_set.disjointed
- \- *lemma* measurable_set.const
- \- *lemma* nonempty_measurable_superset
- \- *lemma* measurable_space.ext
- \- *lemma* measurable_space.ext_iff
- \- *lemma* measurable_set_eq
- \- *lemma* measurable_set.insert
- \- *lemma* measurable_set_insert
- \- *lemma* set.finite.measurable_set
- \- *lemma* set.countable.measurable_set
- \- *lemma* measurable_set_generate_from
- \- *lemma* generate_from_le
- \- *lemma* generate_from_le_iff
- \- *lemma* generate_from_measurable_set
- \- *lemma* mk_of_closure_sets
- \- *lemma* measurable_set_bot_iff
- \- *lemma* measurable_id
- \- *lemma* measurable.comp
- \- *lemma* measurable_const
- \- *theorem* measurable_set_top
- \- *theorem* measurable_set_inf
- \- *theorem* measurable_set_Inf
- \- *theorem* measurable_set_infi
- \- *theorem* measurable_set_sup
- \- *theorem* measurable_set_Sup
- \- *theorem* measurable_set_supr
- \- *def* measurable_set
- \- *def* generate_from
- \- *def* gi_generate_from
- \- *def* measurable

Created src/measure_theory/measurable_space_def.lean
- \+ *lemma* measurable_set.empty
- \+ *lemma* measurable_set.compl
- \+ *lemma* measurable_set.of_compl
- \+ *lemma* measurable_set.compl_iff
- \+ *lemma* measurable_set.univ
- \+ *lemma* subsingleton.measurable_set
- \+ *lemma* measurable_set.congr
- \+ *lemma* measurable_set.bUnion_decode₂
- \+ *lemma* measurable_set.Union
- \+ *lemma* measurable_set.bUnion
- \+ *lemma* set.finite.measurable_set_bUnion
- \+ *lemma* finset.measurable_set_bUnion
- \+ *lemma* measurable_set.sUnion
- \+ *lemma* set.finite.measurable_set_sUnion
- \+ *lemma* measurable_set.Union_Prop
- \+ *lemma* measurable_set.Inter
- \+ *lemma* measurable_set.Union_fintype
- \+ *lemma* measurable_set.Inter_fintype
- \+ *lemma* measurable_set.bInter
- \+ *lemma* set.finite.measurable_set_bInter
- \+ *lemma* finset.measurable_set_bInter
- \+ *lemma* measurable_set.sInter
- \+ *lemma* set.finite.measurable_set_sInter
- \+ *lemma* measurable_set.Inter_Prop
- \+ *lemma* measurable_set.union
- \+ *lemma* measurable_set.inter
- \+ *lemma* measurable_set.diff
- \+ *lemma* measurable_set.ite
- \+ *lemma* measurable_set.disjointed
- \+ *lemma* measurable_set.const
- \+ *lemma* nonempty_measurable_superset
- \+ *lemma* measurable_space.ext
- \+ *lemma* measurable_space.ext_iff
- \+ *lemma* measurable_set_eq
- \+ *lemma* measurable_set.insert
- \+ *lemma* measurable_set_insert
- \+ *lemma* set.finite.measurable_set
- \+ *lemma* set.countable.measurable_set
- \+ *lemma* measurable_set_generate_from
- \+ *lemma* generate_from_le
- \+ *lemma* generate_from_le_iff
- \+ *lemma* generate_from_measurable_set
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* measurable_set_bot_iff
- \+ *lemma* measurable_id
- \+ *lemma* measurable_id'
- \+ *lemma* measurable.comp
- \+ *lemma* measurable_const
- \+ *theorem* measurable_set_top
- \+ *theorem* measurable_set_inf
- \+ *theorem* measurable_set_Inf
- \+ *theorem* measurable_set_infi
- \+ *theorem* measurable_set_sup
- \+ *theorem* measurable_set_Sup
- \+ *theorem* measurable_set_supr
- \+ *def* measurable_set
- \+ *def* generate_from
- \+ *def* gi_generate_from
- \+ *def* measurable

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* subsingleton.ae_measurable
- \+/\- *lemma* ae_measurable_zero_measure
- \- *lemma* of_measurable_apply
- \- *lemma* to_outer_measure_injective
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* coe_to_outer_measure
- \- *lemma* to_outer_measure_apply
- \- *lemma* measure_eq_trim
- \- *lemma* measure_eq_infi
- \- *lemma* measure_eq_infi'
- \- *lemma* measure_eq_induced_outer_measure
- \- *lemma* to_outer_measure_eq_induced_outer_measure
- \- *lemma* measure_eq_extend
- \- *lemma* measure_empty
- \- *lemma* nonempty_of_measure_ne_zero
- \- *lemma* measure_mono
- \- *lemma* measure_mono_null
- \- *lemma* measure_mono_top
- \- *lemma* exists_measurable_superset
- \- *lemma* exists_measurable_superset_forall_eq
- \- *lemma* subset_to_measurable
- \- *lemma* measurable_set_to_measurable
- \- *lemma* measure_to_measurable
- \- *lemma* exists_measurable_superset_of_null
- \- *lemma* exists_measurable_superset_iff_measure_eq_zero
- \- *lemma* measure_bUnion_le
- \- *lemma* measure_bUnion_finset_le
- \- *lemma* measure_bUnion_lt_top
- \- *lemma* measure_Union_null
- \- *lemma* measure_Union_null_iff
- \- *lemma* measure_bUnion_null_iff
- \- *lemma* measure_union_null
- \- *lemma* measure_union_null_iff
- \- *lemma* mem_ae_iff
- \- *lemma* ae_iff
- \- *lemma* compl_mem_ae_iff
- \- *lemma* frequently_ae_iff
- \- *lemma* frequently_ae_mem_iff
- \- *lemma* measure_zero_iff_ae_nmem
- \- *lemma* ae_of_all
- \- *lemma* ae_imp_iff
- \- *lemma* ae_all_iff
- \- *lemma* ae_ball_iff
- \- *lemma* ae_eq_refl
- \- *lemma* ae_eq_symm
- \- *lemma* ae_eq_trans
- \- *lemma* ae_eq_empty
- \- *lemma* ae_le_set
- \- *lemma* union_ae_eq_right
- \- *lemma* diff_ae_eq_self
- \- *lemma* ae_eq_set
- \- *lemma* measure_mono_ae
- \- *lemma* measure_congr
- \- *lemma* measurable.ae_measurable
- \- *lemma* measurable_mk
- \- *lemma* ae_eq_mk
- \- *lemma* congr
- \- *lemma* ae_measurable_congr
- \- *lemma* ae_measurable_const
- \- *lemma* measurable.comp_ae_measurable
- \- *theorem* measure_Union_le
- \- *theorem* measure_union_le
- \- *def* of_measurable
- \- *def* to_measurable
- \- *def* measure.ae
- \- *def* ae_measurable
- \- *def* mk

Created src/measure_theory/measure_space_def.lean
- \+ *lemma* of_measurable_apply
- \+ *lemma* to_outer_measure_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_to_outer_measure
- \+ *lemma* to_outer_measure_apply
- \+ *lemma* measure_eq_trim
- \+ *lemma* measure_eq_infi
- \+ *lemma* measure_eq_infi'
- \+ *lemma* measure_eq_induced_outer_measure
- \+ *lemma* to_outer_measure_eq_induced_outer_measure
- \+ *lemma* measure_eq_extend
- \+ *lemma* measure_empty
- \+ *lemma* nonempty_of_measure_ne_zero
- \+ *lemma* measure_mono
- \+ *lemma* measure_mono_null
- \+ *lemma* measure_mono_top
- \+ *lemma* exists_measurable_superset
- \+ *lemma* exists_measurable_superset_forall_eq
- \+ *lemma* subset_to_measurable
- \+ *lemma* measurable_set_to_measurable
- \+ *lemma* measure_to_measurable
- \+ *lemma* exists_measurable_superset_of_null
- \+ *lemma* exists_measurable_superset_iff_measure_eq_zero
- \+ *lemma* measure_bUnion_le
- \+ *lemma* measure_bUnion_finset_le
- \+ *lemma* measure_bUnion_lt_top
- \+ *lemma* measure_Union_null
- \+ *lemma* measure_Union_null_iff
- \+ *lemma* measure_bUnion_null_iff
- \+ *lemma* measure_union_null
- \+ *lemma* measure_union_null_iff
- \+ *lemma* mem_ae_iff
- \+ *lemma* ae_iff
- \+ *lemma* compl_mem_ae_iff
- \+ *lemma* frequently_ae_iff
- \+ *lemma* frequently_ae_mem_iff
- \+ *lemma* measure_zero_iff_ae_nmem
- \+ *lemma* ae_of_all
- \+ *lemma* ae_imp_iff
- \+ *lemma* ae_all_iff
- \+ *lemma* ae_ball_iff
- \+ *lemma* ae_eq_refl
- \+ *lemma* ae_eq_symm
- \+ *lemma* ae_eq_trans
- \+ *lemma* ae_eq_empty
- \+ *lemma* ae_le_set
- \+ *lemma* union_ae_eq_right
- \+ *lemma* diff_ae_eq_self
- \+ *lemma* ae_eq_set
- \+ *lemma* measure_mono_ae
- \+ *lemma* measure_congr
- \+ *lemma* measurable.ae_measurable
- \+ *lemma* measurable_mk
- \+ *lemma* ae_eq_mk
- \+ *lemma* congr
- \+ *lemma* ae_measurable_congr
- \+ *lemma* ae_measurable_const
- \+ *lemma* ae_measurable_id
- \+ *lemma* ae_measurable_id'
- \+ *lemma* measurable.comp_ae_measurable
- \+ *theorem* measure_Union_le
- \+ *theorem* measure_union_le
- \+ *def* of_measurable
- \+ *def* to_measurable
- \+ *def* measure.ae
- \+ *def* ae_measurable
- \+ *def* mk

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/pi_system.lean


Created src/measure_theory/tactic.lean


Created test/measurability.lean




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
Created src/measure_theory/integrable_on.lean
- \+ *lemma* piecewise_ae_eq_restrict
- \+ *lemma* piecewise_ae_eq_restrict_compl
- \+ *lemma* indicator_ae_eq_restrict
- \+ *lemma* indicator_ae_eq_restrict_compl
- \+ *lemma* measurable_at_bot
- \+ *lemma* ae_measurable.measurable_at_filter_of_mem
- \+ *lemma* has_finite_integral_restrict_of_bounded
- \+ *lemma* integrable_on.integrable
- \+ *lemma* integrable_on_empty
- \+ *lemma* integrable_on_univ
- \+ *lemma* integrable_on_zero
- \+ *lemma* integrable_on_const
- \+ *lemma* integrable_on.mono
- \+ *lemma* integrable_on.mono_set
- \+ *lemma* integrable_on.mono_measure
- \+ *lemma* integrable_on.mono_set_ae
- \+ *lemma* integrable.integrable_on
- \+ *lemma* integrable.integrable_on'
- \+ *lemma* integrable_on.restrict
- \+ *lemma* integrable_on.left_of_union
- \+ *lemma* integrable_on.right_of_union
- \+ *lemma* integrable_on.union
- \+ *lemma* integrable_on_union
- \+ *lemma* integrable_on_finite_union
- \+ *lemma* integrable_on_finset_union
- \+ *lemma* integrable_on.add_measure
- \+ *lemma* integrable_on_add_measure
- \+ *lemma* ae_measurable_indicator_iff
- \+ *lemma* integrable_indicator_iff
- \+ *lemma* integrable_on.indicator
- \+ *lemma* integrable.indicator
- \+ *lemma* integrable_at_filter.filter_mono
- \+ *lemma* integrable_at_filter.inf_of_left
- \+ *lemma* integrable_at_filter.inf_of_right
- \+ *lemma* integrable_at_filter.inf_ae_iff
- \+ *lemma* measure.finite_at_filter.integrable_at_filter
- \+ *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \+ *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \+ *lemma* integrable_add
- \+ *lemma* is_compact.integrable_on_of_nhds_within
- \+ *lemma* continuous_on.ae_measurable
- \+ *lemma* continuous_on.integrable_at_nhds_within
- \+ *lemma* continuous_on.integrable_on_compact
- \+ *lemma* continuous.integrable_on_compact
- \+ *lemma* continuous.integrable_of_compact_closure_support
- \+ *lemma* integrable_comp
- \+ *def* measurable_at_filter
- \+ *def* integrable_on
- \+ *def* integrable_at_filter

Modified src/measure_theory/set_integral.lean
- \- *lemma* piecewise_ae_eq_restrict
- \- *lemma* piecewise_ae_eq_restrict_compl
- \- *lemma* indicator_ae_eq_restrict
- \- *lemma* indicator_ae_eq_restrict_compl
- \- *lemma* measurable_at_bot
- \- *lemma* ae_measurable.measurable_at_filter_of_mem
- \- *lemma* has_finite_integral_restrict_of_bounded
- \- *lemma* integrable_on.integrable
- \- *lemma* integrable_on_empty
- \- *lemma* integrable_on_univ
- \- *lemma* integrable_on_zero
- \- *lemma* integrable_on_const
- \- *lemma* integrable_on.mono
- \- *lemma* integrable_on.mono_set
- \- *lemma* integrable_on.mono_measure
- \- *lemma* integrable_on.mono_set_ae
- \- *lemma* integrable.integrable_on
- \- *lemma* integrable.integrable_on'
- \- *lemma* integrable_on.restrict
- \- *lemma* integrable_on.left_of_union
- \- *lemma* integrable_on.right_of_union
- \- *lemma* integrable_on.union
- \- *lemma* integrable_on_union
- \- *lemma* integrable_on_finite_union
- \- *lemma* integrable_on_finset_union
- \- *lemma* integrable_on.add_measure
- \- *lemma* integrable_on_add_measure
- \- *lemma* ae_measurable_indicator_iff
- \- *lemma* integrable_indicator_iff
- \- *lemma* integrable_on.indicator
- \- *lemma* integrable.indicator
- \- *lemma* integrable_at_filter.filter_mono
- \- *lemma* integrable_at_filter.inf_of_left
- \- *lemma* integrable_at_filter.inf_of_right
- \- *lemma* integrable_at_filter.inf_ae_iff
- \- *lemma* measure.finite_at_filter.integrable_at_filter
- \- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto_ae
- \- *lemma* measure.finite_at_filter.integrable_at_filter_of_tendsto
- \- *lemma* integrable_add
- \- *lemma* is_compact.integrable_on_of_nhds_within
- \- *lemma* continuous_on.ae_measurable
- \- *lemma* continuous_on.integrable_at_nhds_within
- \- *lemma* continuous_on.integrable_on_compact
- \- *lemma* continuous.integrable_on_compact
- \- *lemma* continuous.integrable_of_compact_closure_support
- \- *lemma* integrable_comp
- \- *def* measurable_at_filter
- \- *def* integrable_on
- \- *def* integrable_at_filter



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
- \+/\- *def* preorder.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* linear_order.lift



## [2021-06-09 15:40:00](https://github.com/leanprover-community/mathlib/commit/20efef7)
chore(algebra/field_power, data/set/intervals/basic): simpler proofs in the first file, fewer parentheses in the second one ([#7831](https://github.com/leanprover-community/mathlib/pull/7831))
This is mostly a cosmetic PR: I removed two calls to `linarith`, where a term-mode proof was very simple.
I also removed some unnecessary parentheses in a different file.
#### Estimated changes
Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/field_power.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* cos_one_pos

Modified src/data/set/intervals/basic.lean




## [2021-06-09 15:39:59](https://github.com/leanprover-community/mathlib/commit/02d5370)
chore(measure_theory/outer_measure): add extend_eq_top ([#7827](https://github.com/leanprover-community/mathlib/pull/7827))
#### Estimated changes
Modified src/measure_theory/outer_measure.lean
- \+ *lemma* extend_eq_top



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
- \+ *def* bot_equiv_punit
- \+ *def* top_equiv_self

Modified src/analysis/normed_space/inner_product.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* sum_arrow_equiv_prod_arrow_apply_fst
- \+ *lemma* sum_arrow_equiv_prod_arrow_apply_snd
- \+ *lemma* sum_arrow_equiv_prod_arrow_symm_apply_inl
- \+ *lemma* sum_arrow_equiv_prod_arrow_symm_apply_inr

Modified src/data/set/disjointed.lean
- \+ *theorem* pairwise_on_nat
- \+ *theorem* pairwise_disjoint_on_nat

Modified src/linear_algebra/basic.lean
- \+ *lemma* comap_map_eq_of_injective
- \+ *lemma* comap_surjective_of_injective
- \+ *lemma* map_injective_of_injective
- \+ *lemma* comap_inf_map_of_injective
- \+ *lemma* comap_infi_map_of_injective
- \+ *lemma* comap_sup_map_of_injective
- \+ *lemma* comap_supr_map_of_injective
- \+ *lemma* map_le_map_iff_of_injective
- \+ *lemma* map_strict_mono_of_injective
- \+ *def* gci_map_comap

Modified src/linear_algebra/invariant_basis_number.lean


Modified src/linear_algebra/pi.lean
- \+ *lemma* sum_arrow_lequiv_prod_arrow_apply_fst
- \+ *lemma* sum_arrow_lequiv_prod_arrow_apply_snd
- \+ *lemma* sum_arrow_lequiv_prod_arrow_symm_apply_inl
- \+ *lemma* sum_arrow_lequiv_prod_arrow_symm_apply_inr
- \+ *def* sum_arrow_lequiv_prod_arrow

Modified src/linear_algebra/prod.lean
- \+ *lemma* fst_map_fst
- \+ *lemma* fst_map_snd
- \+ *lemma* snd_map_fst
- \+ *lemma* snd_map_snd
- \+ *lemma* fst_sup_snd
- \+ *lemma* fst_inf_snd
- \+ *lemma* tunnel_aux_injective
- \+ *lemma* tailing_le_tunnel
- \+ *lemma* tailing_disjoint_tunnel_succ
- \+ *lemma* tailing_sup_tunnel_succ_le_tunnel
- \+ *lemma* tailings_zero
- \+ *lemma* tailings_succ
- \+ *lemma* tailings_disjoint_tunnel
- \+ *lemma* tailings_disjoint_tailing
- \+ *def* fst
- \+ *def* fst_equiv
- \+ *def* snd
- \+ *def* snd_equiv
- \+ *def* tunnel_aux
- \+ *def* tunnel
- \+ *def* tailing
- \+ *def* tailing_linear_equiv
- \+ *def* tailings

Modified src/logic/unique.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_disjoint_absorbs

Modified src/order/modular_lattice.lean
- \+ *theorem* disjoint.disjoint_sup_left_of_disjoint_sup_right

Created src/order/partial_sups.lean
- \+ *lemma* partial_sups_zero
- \+ *lemma* partial_sups_succ
- \+ *lemma* le_partial_sups
- \+ *lemma* partial_sups_le
- \+ *lemma* partial_sups_eq
- \+ *lemma* partial_sups_disjoint_of_disjoint
- \+ *def* partial_sups

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* finite_of_linear_independent
- \+/\- *lemma* is_noetherian.induction
- \+ *lemma* is_noetherian.disjoint_partial_sups_eventually_bot
- \+/\- *theorem* is_noetherian_iff_well_founded
- \+/\- *theorem* set_has_maximal_iff_noetherian
- \+/\- *theorem* monotone_stabilizes_iff_noetherian
- \+/\- *theorem* is_noetherian.injective_of_surjective_endomorphism
- \+/\- *theorem* is_noetherian.bijective_of_surjective_endomorphism



## [2021-06-09 10:12:45](https://github.com/leanprover-community/mathlib/commit/47ad680)
feat(measure_theory/interval_integral): integration by substitution / change of variables ([#7273](https://github.com/leanprover-community/mathlib/pull/7273))
Given that `f` has a derivative at `f'` everywhere on `interval a b`,
`∫ x in a..b, (g ∘ f) x * f' x = ∫ x in f a..f b, g x`.
Co-authored by @ADedecker
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *theorem* integral_comp_mul_deriv'
- \+ *theorem* integral_comp_mul_deriv

Modified test/integration.lean




## [2021-06-09 06:11:41](https://github.com/leanprover-community/mathlib/commit/faa58e5)
refactor(algebra/module/projective) make is_projective a class ([#7830](https://github.com/leanprover-community/mathlib/pull/7830))
Make `is_projective` a class.
#### Estimated changes
Modified src/algebra/category/Module/projective.lean


Modified src/algebra/module/projective.lean
- \+ *lemma* projective_def
- \+ *theorem* projective_lifting_property
- \+ *theorem* projective_of_lifting_property'
- \+ *theorem* projective_of_lifting_property
- \+ *theorem* projective_of_free
- \- *theorem* lifting_property
- \- *theorem* of_lifting_property'
- \- *theorem* of_lifting_property
- \- *theorem* of_free
- \- *def* is_projective



## [2021-06-09 06:11:39](https://github.com/leanprover-community/mathlib/commit/c210d0f)
feat(topology/category/limits): Topological bases in cofiltered limits ([#7820](https://github.com/leanprover-community/mathlib/pull/7820))
This PR proves a theorem which provides a simple characterization of certain topological bases in a cofiltered limit of topological spaces.
Eventually I will specialize this assertion to the case where the topological spaces are profinite, and the `T i` are the topological bases given by clopen sets.
This generalizes a lemma from LTE.
#### Estimated changes
Modified src/topology/category/Top/basic.lean
- \+ *lemma* of_iso_of_homeo
- \+ *lemma* of_homeo_of_iso
- \+ *def* iso_of_homeo
- \+ *def* homeo_of_iso

Modified src/topology/category/Top/limits.lean
- \+ *theorem* is_topological_basis_cofiltered_limit
- \+ *def* limit_cone_infi
- \+ *def* limit_cone_infi_is_limit



## [2021-06-09 06:11:38](https://github.com/leanprover-community/mathlib/commit/34c433d)
feat(data/finsupp): generalize finsupp.has_scalar to require only distrib_mul_action instead of semimodule ([#7819](https://github.com/leanprover-community/mathlib/pull/7819))
This propagates the generalization to (add_)monoid_algebra and mv_polynomial.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* support_smul
- \+/\- *lemma* filter_smul
- \+/\- *lemma* map_domain_smul
- \+/\- *lemma* smul_single
- \+/\- *lemma* map_range_smul
- \+/\- *lemma* sum_smul_index'

Modified src/data/finsupp/to_dfinsupp.lean
- \+/\- *lemma* to_dfinsupp_smul
- \+/\- *lemma* to_finsupp_smul

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* coeff_smul



## [2021-06-09 06:11:37](https://github.com/leanprover-community/mathlib/commit/393f638)
feat(ring_theory/localization): Make local_ring_hom more flexible ([#7787](https://github.com/leanprover-community/mathlib/pull/7787))
Make `localization.local_ring_hom` more flexible, by allowing two ideals `I` and `J` as arguments, with the assumption that `I` equals `ideal.comap f J`. Also add lemmas about identity and composition.
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *lemma* local_ring_hom_to_map
- \+/\- *lemma* local_ring_hom_mk'
- \+/\- *lemma* local_ring_hom_unique
- \+ *lemma* local_ring_hom_id
- \+ *lemma* local_ring_hom_comp



## [2021-06-08 19:13:24](https://github.com/leanprover-community/mathlib/commit/5c6d3bc)
feat(topology/instances/ereal): more on ereal, notably its topology ([#7765](https://github.com/leanprover-community/mathlib/pull/7765))
#### Estimated changes
Modified src/algebra/ordered_monoid.lean


Modified src/data/real/ereal.lean
- \+ *lemma* bot_lt_top
- \+ *lemma* bot_ne_top
- \+ *lemma* to_real_top
- \+ *lemma* to_real_bot
- \+ *lemma* to_real_zero
- \+ *lemma* to_real_coe
- \+ *lemma* bot_lt_coe
- \+ *lemma* coe_ne_bot
- \+ *lemma* bot_ne_coe
- \+ *lemma* coe_lt_top
- \+ *lemma* coe_ne_top
- \+ *lemma* top_ne_coe
- \+ *lemma* bot_lt_zero
- \+ *lemma* bot_ne_zero
- \+ *lemma* zero_ne_bot
- \+ *lemma* zero_lt_top
- \+ *lemma* zero_ne_top
- \+ *lemma* top_ne_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* to_real_le_to_real
- \+ *lemma* to_real_coe_ennreal
- \+ *lemma* coe_nnreal_eq_coe_real
- \+ *lemma* coe_ennreal_top
- \+ *lemma* coe_ennreal_eq_top_iff
- \+ *lemma* coe_nnreal_ne_top
- \+ *lemma* coe_nnreal_lt_top
- \+ *lemma* coe_ennreal_le_coe_ennreal_iff
- \+ *lemma* coe_ennreal_lt_coe_ennreal_iff
- \+ *lemma* coe_ennreal_eq_coe_ennreal_iff
- \+ *lemma* coe_ennreal_nonneg
- \+ *lemma* bot_lt_coe_ennreal
- \+ *lemma* coe_ennreal_ne_bot
- \+ *lemma* coe_ennreal_add
- \+ *lemma* coe_ennreal_zero
- \+ *lemma* exists_rat_btwn_of_lt
- \+ *lemma* lt_iff_exists_rat_btwn
- \+ *lemma* add_top
- \+ *lemma* top_add
- \+ *lemma* bot_add_bot
- \+ *lemma* bot_add_coe
- \+ *lemma* coe_add_bot
- \+ *lemma* to_real_add
- \+ *lemma* add_lt_add_right_coe
- \+ *lemma* add_lt_add_of_lt_of_le
- \+ *lemma* add_lt_add_left_coe
- \+ *lemma* add_lt_add
- \+ *lemma* ad_eq_top_iff
- \+ *lemma* add_lt_top_iff
- \+ *lemma* neg_top
- \+ *lemma* neg_bot
- \+ *lemma* neg_zero
- \+ *lemma* to_real_neg
- \+ *lemma* neg_eg_top_iff
- \+ *lemma* neg_eg_bot_iff
- \+ *lemma* neg_eg_zero_iff
- \+ *lemma* neg_le_neg_iff
- \+ *lemma* coe_neg
- \+ *lemma* neg_lt_of_neg_lt
- \+ *lemma* neg_lt_iff_neg_lt
- \+ *lemma* sub_zero
- \+ *lemma* zero_sub
- \+ *lemma* sub_eq_add_neg
- \+ *lemma* sub_le_sub
- \+ *lemma* sub_lt_sub_of_lt_of_le
- \+ *lemma* coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal
- \+ *lemma* to_real_sub
- \+/\- *theorem* neg_inj
- \+ *theorem* neg_eq_neg_iff
- \+ *def* real.to_ereal
- \+ *def* _root_.ennreal.to_ereal
- \+ *def* to_real
- \+ *def* ne_top_bot_equiv_real
- \+ *def* neg_order_iso

Modified src/order/conditionally_complete_lattice.lean


Created src/topology/instances/ereal.lean
- \+ *lemma* embedding_coe
- \+ *lemma* open_embedding_coe
- \+ *lemma* tendsto_coe
- \+ *lemma* _root_.continuous_coe_real_ereal
- \+ *lemma* continuous_coe_iff
- \+ *lemma* nhds_coe
- \+ *lemma* nhds_coe_coe
- \+ *lemma* tendsto_to_real
- \+ *lemma* continuous_on_to_real
- \+ *lemma* embedding_coe_ennreal
- \+ *lemma* tendsto_coe_ennreal
- \+ *lemma* _root_.continuous_coe_ennreal_ereal
- \+ *lemma* continuous_coe_ennreal_iff
- \+ *lemma* nhds_top
- \+ *lemma* nhds_top'
- \+ *lemma* mem_nhds_top_iff
- \+ *lemma* tendsto_nhds_top_iff_real
- \+ *lemma* nhds_bot
- \+ *lemma* nhds_bot'
- \+ *lemma* mem_nhds_bot_iff
- \+ *lemma* tendsto_nhds_bot_iff_real
- \+ *lemma* continuous_at_add_coe_coe
- \+ *lemma* continuous_at_add_top_coe
- \+ *lemma* continuous_at_add_coe_top
- \+ *lemma* continuous_at_add_top_top
- \+ *lemma* continuous_at_add_bot_coe
- \+ *lemma* continuous_at_add_coe_bot
- \+ *lemma* continuous_at_add_bot_bot
- \+ *lemma* continuous_at_add
- \+ *lemma* continuous_neg
- \+ *def* ne_bot_top_homeomorph_real
- \+ *def* neg_homeo



## [2021-06-08 19:13:23](https://github.com/leanprover-community/mathlib/commit/75c81de)
feat(measure_theory/integration): a measurable function is a series of simple functions ([#7764](https://github.com/leanprover-community/mathlib/pull/7764))
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* eapprox_lt_top
- \+ *lemma* sum_eapprox_diff
- \+ *lemma* tsum_eapprox_diff
- \+ *def* eapprox_diff



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


Created src/model_theory/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* map_fun
- \+ *lemma* map_rel
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* coe_to_hom
- \+ *lemma* injective
- \+ *lemma* refl_apply
- \+ *lemma* to_embedding_to_hom
- \+ *lemma* coe_to_embedding
- \+ *def* empty
- \+ *def* const
- \+ *def* id
- \+ *def* comp
- \+ *def* to_hom
- \+ *def* refl
- \+ *def* symm
- \+ *def* to_embedding



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
- \+ *lemma* univ_eq_empty'
- \+ *theorem* univ_of_is_empty
- \+ *theorem* card_of_is_empty

Modified src/data/fintype/card.lean


Modified test/matrix.lean




## [2021-06-07 15:40:24](https://github.com/leanprover-community/mathlib/commit/6e67536)
feat(category/limits): kernel.map ([#7623](https://github.com/leanprover-community/mathlib/pull/7623))
A generalization of a lemma from LTE, stated for a category with (co)kernels.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* parallel_pair_hom_app_zero
- \+ *lemma* parallel_pair_hom_app_one
- \+ *def* parallel_pair_hom

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel.lift_map
- \+ *lemma* cokernel.map_desc



## [2021-06-07 15:40:23](https://github.com/leanprover-community/mathlib/commit/fb72599)
feat(algebra/periodic): define periodicity ([#7572](https://github.com/leanprover-community/mathlib/pull/7572))
This PR introduces a general notion of periodicity. It also includes proofs of the "usual" properties of periodic (and antiperiodic) functions.
#### Estimated changes
Created src/algebra/periodic.lean
- \+ *lemma* periodic.comp
- \+ *lemma* periodic.comp_add_hom
- \+ *lemma* periodic.mul
- \+ *lemma* periodic.div
- \+ *lemma* periodic.const_smul
- \+ *lemma* periodic.const_smul'
- \+ *lemma* periodic.const_mul
- \+ *lemma* periodic.const_inv_smul
- \+ *lemma* periodic.const_inv_smul'
- \+ *lemma* periodic.const_inv_mul
- \+ *lemma* periodic.mul_const
- \+ *lemma* periodic.mul_const'
- \+ *lemma* periodic.mul_const_inv
- \+ *lemma* periodic.div_const
- \+ *lemma* periodic.add_period
- \+ *lemma* periodic.sub_eq
- \+ *lemma* periodic.neg
- \+ *lemma* periodic.sub_period
- \+ *lemma* periodic.nsmul
- \+ *lemma* periodic.nat_mul
- \+ *lemma* periodic.neg_nsmul
- \+ *lemma* periodic.neg_nat_mul
- \+ *lemma* periodic.sub_nsmul_eq
- \+ *lemma* periodic.sub_nat_mul_eq
- \+ *lemma* periodic.gsmul
- \+ *lemma* periodic.int_mul
- \+ *lemma* periodic.sub_gsmul_eq
- \+ *lemma* periodic.sub_int_mul_eq
- \+ *lemma* periodic.eq
- \+ *lemma* periodic.neg_eq
- \+ *lemma* periodic.nsmul_eq
- \+ *lemma* periodic.nat_mul_eq
- \+ *lemma* periodic.gsmul_eq
- \+ *lemma* periodic.int_mul_eq
- \+ *lemma* periodic_with_period_zero
- \+ *lemma* antiperiodic.periodic
- \+ *lemma* antiperiodic.eq
- \+ *lemma* antiperiodic.nat_even_mul_periodic
- \+ *lemma* antiperiodic.nat_odd_mul_antiperiodic
- \+ *lemma* antiperiodic.int_even_mul_periodic
- \+ *lemma* antiperiodic.int_odd_mul_antiperiodic
- \+ *lemma* antiperiodic.nat_mul_eq_of_eq_zero
- \+ *lemma* antiperiodic.int_mul_eq_of_eq_zero
- \+ *lemma* antiperiodic.sub_eq
- \+ *lemma* antiperiodic.neg
- \+ *lemma* antiperiodic.neg_eq
- \+ *lemma* antiperiodic.const_smul
- \+ *lemma* antiperiodic.const_smul'
- \+ *lemma* antiperiodic.const_mul
- \+ *lemma* antiperiodic.const_inv_smul
- \+ *lemma* antiperiodic.const_inv_smul'
- \+ *lemma* antiperiodic.const_inv_mul
- \+ *lemma* antiperiodic.mul_const
- \+ *lemma* antiperiodic.mul_const'
- \+ *lemma* antiperiodic.mul_const_inv
- \+ *lemma* antiperiodic.div_inv
- \+ *lemma* antiperiodic.add
- \+ *lemma* antiperiodic.sub
- \+ *lemma* periodic.add_antiperiod
- \+ *lemma* periodic.sub_antiperiod
- \+ *lemma* periodic.add_antiperiod_eq
- \+ *lemma* periodic.sub_antiperiod_eq
- \+ *lemma* antiperiodic.mul
- \+ *lemma* antiperiodic.div
- \+ *def* periodic
- \+ *def* antiperiodic



## [2021-06-07 15:40:22](https://github.com/leanprover-community/mathlib/commit/e55d470)
feat(specific_groups/alternating_group): The alternating group on 5 elements is simple ([#7502](https://github.com/leanprover-community/mathlib/pull/7502))
Shows that `is_simple_group (alternating_group (fin 5))`
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* le_sum_of_mem

Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* mem_cycle_type_iff
- \+ *lemma* le_card_support_of_mem_cycle_type
- \+ *lemma* cycle_type_of_card_le_mem_cycle_type_add_two
- \+ *lemma* order_of
- \+ *lemma* is_three_cycle_sq

Modified src/group_theory/specific_groups/alternating.lean
- \+ *lemma* is_three_cycle_sq_of_three_mem_cycle_type_five
- \+ *lemma* nontrivial_of_three_le_card
- \+ *lemma* normal_closure_swap_mul_swap_five
- \+ *lemma* is_conj_swap_mul_swap_of_cycle_type_two

Modified src/group_theory/subgroup.lean
- \+ *lemma* cod_restrict_apply
- \+ *lemma* normal_closure_eq_top_of



## [2021-06-07 15:40:20](https://github.com/leanprover-community/mathlib/commit/fa7b5f2)
feat(linear_algebra/quadratic_form): Complex version of Sylvester's law of inertia ([#7416](https://github.com/leanprover-community/mathlib/pull/7416))
Every nondegenerate complex quadratic form is equivalent to a quadratic form corresponding to the sum of squares.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* group_smul_span_eq_top
- \+ *lemma* group_smul_apply
- \+ *lemma* units_smul_span_eq_top
- \+ *lemma* units_smul_apply
- \+ *lemma* is_unit_smul_apply
- \+ *def* group_smul
- \+ *def* units_smul
- \+ *def* is_unit_smul

Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.group_smul
- \+ *lemma* linear_independent.units_smul

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* basis_repr_apply
- \+ *lemma* isometry_of_is_Ortho_apply
- \+ *lemma* weighted_sum_squares_apply
- \+ *lemma* equivalent_weighted_sum_squares_of_nondegenerate'
- \+ *theorem* equivalent_sum_squares
- \+ *def* isometry_of_comp_linear_equiv
- \+ *def* weighted_sum_squares



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


Modified src/algebra/char_p/pi.lean


Modified src/algebra/direct_sum_graded.lean


Modified src/algebra/monoid_algebra.lean


Modified src/algebra/opposites.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/ring/basic.lean
- \+/\- *lemma* mul_boole
- \+/\- *lemma* boole_mul
- \+/\- *lemma* coe_mul_left
- \+/\- *lemma* coe_mul_right
- \+/\- *lemma* mul_right_apply
- \+/\- *lemma* is_unit_map
- \+/\- *lemma* comp_assoc
- \+/\- *theorem* injective_iff
- \+/\- *def* mul_left
- \+/\- *def* mul_right
- \+/\- *def* id
- \+/\- *def* mk'

Modified src/algebra/ring/pi.lean


Modified src/algebra/ring/prod.lean


Modified src/algebra/ring/ulift.lean
- \+/\- *def* ring_equiv

Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/equiv/ring.lean
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_eq_zero_iff
- \+/\- *lemma* map_ne_zero_iff
- \+/\- *lemma* coe_ring_hom_inj_iff

Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/pointwise.lean


Modified src/data/multiset/antidiagonal.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* coe_cast_ring_hom
- \+/\- *lemma* cast_commute
- \+/\- *lemma* cast_comm
- \+/\- *theorem* cast_mul
- \+/\- *def* cast_ring_hom

Modified src/deprecated/group.lean


Modified src/field_theory/perfect_closure.lean


Modified src/group_theory/submonoid/membership.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* support_one
- \+/\- *lemma* order_one
- \+/\- *lemma* mul_coeff
- \+/\- *lemma* mul_coeff_right'
- \+/\- *lemma* mul_coeff_left'
- \+/\- *lemma* single_mul_coeff_add
- \+/\- *lemma* mul_single_coeff_add
- \+/\- *lemma* mul_single_zero_coeff
- \+/\- *lemma* single_zero_mul_coeff
- \+/\- *lemma* mul_coeff_order_add_order
- \+/\- *lemma* C_mul_eq_smul
- \+/\- *lemma* emb_domain_mul
- \+/\- *lemma* emb_domain_one
- \+/\- *lemma* emb_domain_ring_hom_C
- \+/\- *theorem* support_mul_subset_add_support
- \+/\- *def* emb_domain_ring_hom

Modified src/ring_theory/subsemiring.lean
- \+/\- *lemma* list_prod_mem
- \+/\- *lemma* multiset_sum_mem
- \+/\- *lemma* sum_mem
- \+/\- *lemma* pow_mem
- \+/\- *lemma* coe_pow
- \+/\- *lemma* mem_closure_iff_exists_list
- \+/\- *lemma* smul_def

Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/tactic/ring.lean


Modified src/topology/locally_constant/algebra.lean




## [2021-06-07 15:40:18](https://github.com/leanprover-community/mathlib/commit/1eb3ae4)
feat(order/symm_diff): symmetric difference operator ([#6469](https://github.com/leanprover-community/mathlib/pull/6469))
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *lemma* disjoint.disjoint_sdiff_left
- \+ *lemma* disjoint.disjoint_sdiff_right
- \+ *lemma* sdiff_sdiff_self
- \+ *theorem* disjoint_sdiff_self_left
- \+ *theorem* disjoint_sdiff_self_right
- \+ *theorem* eq_compl_iff_is_compl
- \+ *theorem* compl_eq_iff_is_compl
- \- *theorem* disjoint_sdiff

Modified src/order/bounded_lattice.lean
- \+ *lemma* disjoint.eq_bot_of_le
- \+ *lemma* disjoint.of_disjoint_inf_of_le
- \+ *lemma* disjoint.of_disjoint_inf_of_le'

Created src/order/symm_diff.lean
- \+ *lemma* symm_diff_def
- \+ *lemma* symm_diff_eq_xor
- \+ *lemma* symm_diff_comm
- \+ *lemma* symm_diff_self
- \+ *lemma* symm_diff_bot
- \+ *lemma* bot_symm_diff
- \+ *lemma* symm_diff_eq_sup_sdiff_inf
- \+ *lemma* disjoint_symm_diff_inf
- \+ *lemma* symm_diff_le_sup
- \+ *lemma* sdiff_symm_diff
- \+ *lemma* sdiff_symm_diff'
- \+ *lemma* symm_diff_sdiff
- \+ *lemma* symm_diff_sdiff_left
- \+ *lemma* symm_diff_sdiff_right
- \+ *lemma* sdiff_symm_diff_self
- \+ *lemma* symm_diff_eq_iff_sdiff_eq
- \+ *lemma* disjoint.symm_diff_eq_sup
- \+ *lemma* symm_diff_eq_sup
- \+ *lemma* symm_diff_symm_diff_left
- \+ *lemma* symm_diff_symm_diff_right
- \+ *lemma* symm_diff_assoc
- \+ *lemma* symm_diff_symm_diff_self
- \+ *lemma* symm_diff_symm_diff_self'
- \+ *lemma* symm_diff_right_inj
- \+ *lemma* symm_diff_left_inj
- \+ *lemma* symm_diff_eq_left
- \+ *lemma* symm_diff_eq_right
- \+ *lemma* symm_diff_eq_bot
- \+ *lemma* symm_diff_eq
- \+ *lemma* symm_diff_top
- \+ *lemma* top_symm_diff
- \+ *lemma* compl_symm_diff
- \+ *lemma* symm_diff_eq_top_iff
- \+ *lemma* is_compl.symm_diff_eq_top
- \+ *lemma* compl_symm_diff_self
- \+ *lemma* symm_diff_compl_self
- \+ *lemma* symm_diff_symm_diff_right'
- \+ *lemma* disjoint.disjoint_symm_diff_of_disjoint
- \+ *def* symm_diff



## [2021-06-07 07:44:02](https://github.com/leanprover-community/mathlib/commit/136e0d6)
feat(data/fintype/basic): The cardinality of a set is at most the cardinality of the universe ([#7823](https://github.com/leanprover-community/mathlib/pull/7823))
I think that the hypothesis `[fintype ↥s]` can be avoided with the use of classical logic. E.g.,
`noncomputable instance set_fintype' {α : Type*} [fintype α] (s : set α) : fintype s :=by { classical, exact set_fintype s }`
Would it make sense to add this?
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* set_fintype_card_le_univ
- \+/\- *def* set_fintype



## [2021-06-07 07:44:01](https://github.com/leanprover-community/mathlib/commit/4f38062)
feat(algebra/lie/base_change): define extension and restriction of scalars for Lie algebras ([#7808](https://github.com/leanprover-community/mathlib/pull/7808))
#### Estimated changes
Created src/algebra/lie/base_change.lean
- \+ *lemma* bracket_tmul

Modified src/algebra/lie/basic.lean




## [2021-06-07 07:44:00](https://github.com/leanprover-community/mathlib/commit/f57f9c8)
feat(ring_theory): define the field/algebra norm ([#7636](https://github.com/leanprover-community/mathlib/pull/7636))
This PR defines the field norm `algebra.norm K L : L →* K`, where `L` is a finite field extension of `K`. In fact, it defines this for any `algebra R S` instance, where `R` and `S` are integral domains. (With a default value of `1` if `S` does not have a finite `R`-basis.)
The approach is to basically copy `ring_theory/trace.lean` and replace `trace` with `det` or `norm` as appropriate.
#### Estimated changes
Created src/ring_theory/norm.lean
- \+ *lemma* norm_apply
- \+ *lemma* norm_eq_one_of_not_exists_basis
- \+ *lemma* norm_eq_matrix_det
- \+ *lemma* norm_algebra_map_of_basis
- \+ *lemma* norm_algebra_map



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
- \+ *lemma* mem_to_subsemiring
- \+ *lemma* coe_to_subsemiring
- \+ *lemma* mem_to_subring
- \+ *lemma* coe_to_subring
- \+ *lemma* coe_to_submodule
- \+ *lemma* coe_top
- \+ *lemma* mem_top
- \+ *lemma* top_to_submodule
- \+ *lemma* top_to_subsemiring
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* inf_to_submodule
- \+ *lemma* inf_to_subsemiring
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* Inf_to_submodule
- \+ *lemma* Inf_to_subsemiring
- \+ *lemma* coe_infi
- \+ *lemma* mem_infi
- \+ *lemma* infi_to_submodule
- \+ *lemma* prod_inf_prod
- \- *theorem* mem_top
- \- *theorem* top_to_submodule
- \- *theorem* top_to_subsemiring

Modified src/ring_theory/adjoin/basic.lean
- \- *lemma* coe_inf
- \- *lemma* prod_inf_prod

Modified src/ring_theory/finiteness.lean


Modified src/topology/continuous_function/stone_weierstrass.lean




## [2021-06-07 01:12:38](https://github.com/leanprover-community/mathlib/commit/685289c)
feat(algebra/pointwise): pow_mem_pow ([#7822](https://github.com/leanprover-community/mathlib/pull/7822))
If `a ∈ s` then `a ^ n ∈ s ^ n`.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* pow_mem_pow
- \+ *lemma* pow_subset_pow



## [2021-06-07 01:12:37](https://github.com/leanprover-community/mathlib/commit/29d0c63)
feat(measure_theory): add a few integration-related lemmas ([#7821](https://github.com/leanprover-community/mathlib/pull/7821))
These are lemmas I proved while working on [#7164](https://github.com/leanprover-community/mathlib/pull/7164). Some of them are actually not used anymore in that PR because I'm refactoring it, but I thought they would be useful anyway, so here there are.
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_mono_set
- \+ *lemma* lintegral_mono_set'

Modified src/measure_theory/measure_space.lean
- \+ *lemma* restrict_comm
- \+ *lemma* restrict_mono'
- \+/\- *lemma* restrict_mono

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integrable_on.restrict
- \+ *lemma* set_integral_mono_set



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
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* coeff_C
- \+ *lemma* coeff_one
- \+ *lemma* coeff_zero_C
- \+ *lemma* coeff_zero_one
- \+/\- *lemma* coeff_X_pow
- \+/\- *lemma* coeff_X'
- \+/\- *lemma* coeff_mul_X'
- \+/\- *lemma* constant_coeff_monomial

Modified src/data/mv_polynomial/pderiv.lean
- \+/\- *lemma* pderiv_X

Modified src/data/polynomial/field_division.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* monomial_def
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* coeff_one
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_index_single_X
- \+/\- *lemma* coeff_X_pow
- \+/\- *lemma* coeff_inv_aux
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* coeff_inv
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* order_monomial



## [2021-06-07 01:12:35](https://github.com/leanprover-community/mathlib/commit/90ae36e)
docs(order/order_iso_nat): add module docstring ([#7804](https://github.com/leanprover-community/mathlib/pull/7804))
add module docstring
#### Estimated changes
Modified src/order/order_iso_nat.lean
- \+/\- *lemma* nat_lt_apply
- \+/\- *def* nat_lt
- \+/\- *def* nat_gt



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
Created src/algebra/char_p/algebra.lean
- \+ *lemma* char_p_of_injective_algebra_map
- \+ *lemma* char_zero_of_injective_algebra_map

Modified src/algebra/char_p/default.lean




## [2021-06-06 03:28:06](https://github.com/leanprover-community/mathlib/commit/ba2c056)
feat(data/list/nodup): nodup.pairwise_of_forall_ne ([#7587](https://github.com/leanprover-community/mathlib/pull/7587))
#### Estimated changes
Modified src/data/list/nodup.lean
- \+ *lemma* nodup.pairwise_of_forall_ne
- \+ *lemma* nodup.pairwise_of_set_pairwise_on

Modified src/data/list/pairwise.lean
- \+ *lemma* pairwise.set_pairwise_on
- \+ *lemma* pairwise_of_reflexive_on_dupl_of_forall_ne
- \+ *lemma* pairwise_of_reflexive_of_forall_ne



## [2021-06-05 09:09:15](https://github.com/leanprover-community/mathlib/commit/7021ff9)
feat(linear_algebra/basis): use is_empty instead of ¬nonempty ([#7815](https://github.com/leanprover-community/mathlib/pull/7815))
This removes the need for `basis.of_dim_eq_zero'` and `basis_of_finrank_zero'`, as these special cases are now covered by the unprimed versions and typeclass search.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/basis.lean
- \- *lemma* empty_unique

Modified src/linear_algebra/dimension.lean
- \+/\- *lemma* basis.of_dim_eq_zero_apply
- \- *lemma* basis.of_dim_eq_zero'_apply
- \+/\- *def* basis.of_dim_eq_zero
- \- *def* basis.of_dim_eq_zero'

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
- \+/\- *lemma* integral_exp
- \+ *lemma* integral_log
- \+ *lemma* integral_log_of_pos
- \+ *lemma* integral_log_of_neg

Modified test/integration.lean




## [2021-06-04 16:08:36](https://github.com/leanprover-community/mathlib/commit/0b09858)
feat(linear_algebra/basic): add a unique instance for linear_equiv ([#7816](https://github.com/leanprover-community/mathlib/pull/7816))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* zero_symm
- \+ *lemma* coe_zero
- \+ *lemma* zero_apply



## [2021-06-04 13:25:42](https://github.com/leanprover-community/mathlib/commit/65e3b04)
feat(linear_algebra/determinant): various `basis.det` lemmas ([#7669](https://github.com/leanprover-community/mathlib/pull/7669))
A selection of results that I needed for computing the value of `basis.det`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* constr_comp
- \+ *lemma* map_equiv

Modified src/linear_algebra/determinant.lean
- \+ *lemma* basis.det_comp
- \+ *lemma* basis.det_reindex
- \+ *lemma* basis.det_reindex_symm
- \+ *lemma* basis.det_map

Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.to_matrix_reindex
- \+ *lemma* basis.to_matrix_reindex'
- \+ *lemma* basis.to_matrix_map



## [2021-06-04 09:53:02](https://github.com/leanprover-community/mathlib/commit/1a62bb4)
feat(linear_algebra): strong rank condition implies rank condition ([#7683](https://github.com/leanprover-community/mathlib/pull/7683))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* congr_fun
- \+ *lemma* equiv_fun_on_fintype_single
- \+ *lemma* equiv_fun_on_fintype_symm_single

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv_fun_on_fintype_single
- \+ *lemma* linear_equiv_fun_on_fintype_symm_single

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/finsupp.lean
- \+ *lemma* splitting_of_finsupp_surjective_splits
- \+ *lemma* left_inverse_splitting_of_finsupp_surjective
- \+ *lemma* splitting_of_finsupp_surjective_injective
- \+ *lemma* splitting_of_fun_on_fintype_surjective_splits
- \+ *lemma* left_inverse_splitting_of_fun_on_fintype_surjective
- \+ *lemma* splitting_of_fun_on_fintype_surjective_injective
- \+ *def* splitting_of_finsupp_surjective
- \+ *def* splitting_of_fun_on_fintype_surjective

Modified src/linear_algebra/invariant_basis_number.lean




## [2021-06-04 03:56:15](https://github.com/leanprover-community/mathlib/commit/be183e2)
chore(data/finset|multiset|finsupp): reduce algebra/ imports ([#7797](https://github.com/leanprover-community/mathlib/pull/7797))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* abs_sum_le_sum_abs

Modified src/algebra/big_operators/finsupp.lean
- \+ *lemma* finsupp.sum_mul
- \+ *lemma* finsupp.mul_sum

Modified src/algebra/gcd_monoid.lean


Modified src/algebra/group_power/lemmas.lean
- \- *theorem* list.prod_repeat
- \- *theorem* list.sum_repeat
- \- *theorem* nat.nsmul_eq_mul

Modified src/algebra/iterate_hom.lean


Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean
- \- *lemma* sum_mul
- \- *lemma* mul_sum

Modified src/data/finsupp/lattice.lean


Modified src/data/list/basic.lean
- \+ *theorem* prod_repeat
- \+ *theorem* sum_repeat

Modified src/data/list/indexes.lean


Modified src/data/list/perm.lean


Modified src/data/multiset/basic.lean
- \- *lemma* abs_sum_le_sum_abs
- \+/\- *theorem* prod_to_list

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
- \+ *lemma* tot_sep_of_zero_dim
- \+ *lemma* compact_exists_clopen_in_open
- \+ *lemma* loc_compact_Haus_tot_disc_of_zero_dim
- \+ *theorem* compact_t2_tot_disc_iff_tot_sep
- \+ *theorem* loc_compact_t2_tot_disc_iff_tot_sep



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
- \+ *lemma* left_comm_tmul
- \+ *lemma* left_comm_symm_tmul
- \+ *lemma* tensor_tensor_tensor_comm_tmul
- \+ *lemma* tensor_tensor_tensor_comm_symm_tmul
- \+ *def* left_comm
- \+ *def* tensor_tensor_tensor_comm



## [2021-06-03 11:07:26](https://github.com/leanprover-community/mathlib/commit/62655a2)
chore(data/dfinsupp): add the simp lemma coe_pre_mk ([#7806](https://github.com/leanprover-community/mathlib/pull/7806))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* coe_pre_mk



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
- \+/\- *lemma* emb_domain_add



## [2021-06-03 11:07:23](https://github.com/leanprover-community/mathlib/commit/54d8b94)
chore(logic/basic): add simp lemmas about exist_unique to match those about exists ([#7784](https://github.com/leanprover-community/mathlib/pull/7784))
Adds:
* `exists_unique_const` to match `exists_const` (provable by simp)
* `exists_unique_prop` to match `exists_prop` (provable by simp)
* `exists_unique_prop_of_true` to match `exists_prop_of_true`
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* exists_unique.exists
- \+/\- *lemma* exists_unique_iff_exists
- \+ *theorem* exists_unique_const
- \+ *theorem* exists_unique_prop
- \+ *theorem* exists_unique_prop_of_true



## [2021-06-03 11:07:21](https://github.com/leanprover-community/mathlib/commit/ef13938)
feat(ring_theory/tensor_product): the base change of a linear map along an algebra ([#4773](https://github.com/leanprover-community/mathlib/pull/4773))
#### Estimated changes
Modified src/algebra/lie/weights.lean


Modified src/linear_algebra/tensor_product.lean
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+ *lemma* curry_injective
- \+ *lemma* ltensor_mul
- \+ *lemma* rtensor_mul
- \+/\- *theorem* smul_tmul'

Modified src/ring_theory/tensor_product.lean
- \+ *lemma* smul_eq_lsmul_rtensor
- \+ *lemma* restrict_scalars_curry
- \+ *lemma* curry_injective
- \+ *lemma* lift_tmul
- \+ *lemma* base_change_tmul
- \+ *lemma* base_change_eq_ltensor
- \+ *lemma* base_change_add
- \+ *lemma* base_change_zero
- \+ *lemma* base_change_smul
- \+ *lemma* base_change_sub
- \+ *lemma* base_change_neg
- \+ *theorem* ext
- \+ *def* curry
- \+ *def* lift
- \+ *def* uncurry
- \+ *def* lcurry
- \+ *def* lift.equiv
- \+ *def* mk
- \+ *def* assoc
- \+ *def* base_change
- \+ *def* base_change_hom



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
- \+ *lemma* is_topological_basis_opens
- \+ *lemma* is_topological_basis_pi
- \+ *lemma* is_topological_basis_infi



## [2021-06-03 07:38:37](https://github.com/leanprover-community/mathlib/commit/8422d8c)
chore(data/padics): move padics to number_theory/ ([#7771](https://github.com/leanprover-community/mathlib/pull/7771))
Per [zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/move.20p-adics).
#### Estimated changes
Deleted src/data/padics/default.lean


Created src/number_theory/padics/default.lean


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
- \+ *lemma* at_top_countable_basis_of_archimedean
- \+ *lemma* at_bot_countable_basis_of_archimedean
- \+ *lemma* at_top_countably_generated_of_archimedean
- \+ *lemma* at_bot_countably_generated



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
- \+ *theorem* span_eq_range_total
- \+/\- *theorem* mem_span_iff_total
- \+ *theorem* span_image_eq_map_total
- \+ *theorem* mem_span_image_iff_total
- \- *theorem* span_eq_map_total

Modified src/linear_algebra/linear_independent.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_basis.lean




## [2021-06-03 07:38:33](https://github.com/leanprover-community/mathlib/commit/6d90d35)
feat(analysis/fourier): monomials on the circle are orthonormal ([#6952](https://github.com/leanprover-community/mathlib/pull/6952))
Make the circle into a measure space, using Haar measure, and prove that the monomials `z ^ n` are orthonormal when considered as elements of L^2 on the circle.
#### Estimated changes
Created src/analysis/fourier.lean
- \+ *lemma* fourier_zero
- \+ *lemma* fourier_neg
- \+ *lemma* fourier_add
- \+ *lemma* fourier_add_half_inv_index
- \+ *lemma* orthonormal_fourier
- \+ *def* haar_circle
- \+ *def* fourier

Modified src/data/complex/exponential.lean
- \+ *lemma* exp_int_mul

Modified src/geometry/manifold/instances/circle.lean
- \+ *lemma* norm_sq_eq_of_mem_circle
- \+ *lemma* nonzero_of_mem_circle
- \+ *lemma* coe_inv_circle_eq_conj
- \+/\- *lemma* coe_inv_circle
- \+/\- *lemma* coe_div_circle
- \+ *lemma* exp_map_circle_apply

Modified src/measure_theory/l2_space.lean
- \+ *lemma* bounded_continuous_function.inner_to_Lp
- \+ *lemma* continuous_map.inner_to_Lp

Modified src/measure_theory/lp_space.lean
- \+ *lemma* coe_fn_to_Lp
- \+/\- *lemma* to_Lp_norm_le

Modified src/topology/compacts.lean
- \+ *def* positive_compacts_univ

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
- \+ *theorem* bind_decode₂_iff
- \- *theorem* bind_decode2_iff

Modified src/computability/primrec.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable/basic.lean
- \+ *theorem* mem_decode₂'
- \+ *theorem* mem_decode₂
- \+ *theorem* decode₂_ne_none_iff
- \+ *theorem* decode₂_is_partial_inv
- \+ *theorem* decode₂_inj
- \+ *theorem* encodek₂
- \- *theorem* mem_decode2'
- \- *theorem* mem_decode2
- \- *theorem* decode2_is_partial_inv
- \- *theorem* decode2_inj
- \- *theorem* encodek2
- \+ *def* decode₂
- \+/\- *def* encode_sum
- \+/\- *def* decode_sum
- \+/\- *def* encode_subtype
- \+/\- *def* decode_subtype
- \+/\- *def* choose_x
- \+/\- *def* encode'
- \- *def* decode2

Modified src/data/equiv/encodable/lattice.lean
- \+ *lemma* supr_decode₂
- \+ *lemma* Union_decode₂
- \+ *lemma* Union_decode₂_cases
- \- *lemma* supr_decode2
- \- *lemma* Union_decode2
- \- *lemma* Union_decode2_cases
- \+ *theorem* Union_decode₂_disjoint_on
- \- *theorem* Union_decode2_disjoint_on

Modified src/data/equiv/list.lean
- \+/\- *def* fintype_pi

Modified src/data/equiv/nat.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set.bUnion_decode₂
- \- *lemma* measurable_set.bUnion_decode2

Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/pi_system.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *theorem* tsum_supr_decode₂
- \+ *theorem* tsum_Union_decode₂
- \- *theorem* tsum_supr_decode2
- \- *theorem* tsum_Union_decode2



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
- \+ *theorem* lintegral_tendsto_of_tendsto_of_monotone



## [2021-06-02 18:23:19](https://github.com/leanprover-community/mathlib/commit/82bc3ca)
chore(logic/small): reduce imports ([#7777](https://github.com/leanprover-community/mathlib/pull/7777))
By delaying the `fintype` and `encodable` instances for `small`, I think we can now avoid importing `algebra` at all into `logic`.
~~Since some of the `is_empty` lemmas haven't been used yet,~~ I took the liberty of making some arguments explicit, as one was painful to use as is.
#### Estimated changes
Created src/data/equiv/encodable/small.lean


Created src/data/fintype/small.lean


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
- \+ *lemma* coe_prod
- \+ *lemma* prod_to_submodule
- \+ *lemma* mem_prod
- \+ *lemma* prod_top
- \+ *lemma* prod_mono
- \+ *def* prod

Modified src/ring_theory/adjoin/basic.lean
- \+ *lemma* coe_inf
- \+ *lemma* adjoint_prod_le
- \+ *lemma* prod_inf_prod



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
- \+ *lemma* _root_.real.to_nnreal_rpow_of_nonneg
- \- *lemma* of_real_rpow_of_nonneg

Modified src/data/real/conjugate_exponents.lean
- \+/\- *lemma* one_lt_nnreal
- \+/\- *lemma* inv_add_inv_conj_nnreal

Modified src/data/real/ennreal.lean
- \+ *lemma* to_real_mono
- \+ *lemma* to_real_strict_mono

Modified src/data/real/nnreal.lean
- \+ *lemma* _root_.real.coe_to_nnreal
- \+ *lemma* _root_.real.le_coe_to_nnreal
- \+ *lemma* _root_.real.to_nnreal_sum_of_nonneg
- \+ *lemma* _root_.real.to_nnreal_prod_of_nonneg
- \+ *lemma* _root_.real.to_nnreal_coe
- \+ *lemma* to_nnreal_coe_nat
- \+ *lemma* to_nnreal_zero
- \+ *lemma* to_nnreal_one
- \+ *lemma* to_nnreal_pos
- \+ *lemma* to_nnreal_eq_zero
- \+ *lemma* to_nnreal_of_nonpos
- \+ *lemma* coe_to_nnreal'
- \+ *lemma* to_nnreal_le_to_nnreal_iff
- \+ *lemma* to_nnreal_lt_to_nnreal_iff'
- \+ *lemma* to_nnreal_lt_to_nnreal_iff
- \+ *lemma* to_nnreal_lt_to_nnreal_iff_of_nonneg
- \+ *lemma* to_nnreal_add
- \+ *lemma* to_nnreal_add_to_nnreal
- \+ *lemma* to_nnreal_le_to_nnreal
- \+ *lemma* to_nnreal_add_le
- \+ *lemma* to_nnreal_le_iff_le_coe
- \+ *lemma* le_to_nnreal_iff_coe_le
- \+ *lemma* le_to_nnreal_iff_coe_le'
- \+ *lemma* to_nnreal_lt_iff_lt_coe
- \+ *lemma* lt_to_nnreal_iff_coe_lt
- \+ *lemma* to_nnreal_bit0
- \+ *lemma* to_nnreal_bit1
- \+ *lemma* _root_.real.to_nnreal_mul
- \+/\- *lemma* sub_def
- \+ *lemma* _root_.real.to_nnreal_inv
- \+ *lemma* _root_.real.to_nnreal_div
- \+ *lemma* _root_.real.to_nnreal_div'
- \+/\- *lemma* real.nnabs_of_nonneg
- \+ *lemma* real.coe_to_nnreal_le
- \- *lemma* coe_of_real
- \- *lemma* le_coe_of_real
- \- *lemma* of_real_sum_of_nonneg
- \- *lemma* of_real_prod_of_nonneg
- \- *lemma* of_real_coe
- \- *lemma* of_real_coe_nat
- \- *lemma* of_real_zero
- \- *lemma* of_real_one
- \- *lemma* of_real_pos
- \- *lemma* of_real_eq_zero
- \- *lemma* of_real_of_nonpos
- \- *lemma* of_real_le_of_real_iff
- \- *lemma* of_real_lt_of_real_iff'
- \- *lemma* of_real_lt_of_real_iff
- \- *lemma* of_real_lt_of_real_iff_of_nonneg
- \- *lemma* of_real_add
- \- *lemma* of_real_add_of_real
- \- *lemma* of_real_le_of_real
- \- *lemma* of_real_add_le
- \- *lemma* of_real_le_iff_le_coe
- \- *lemma* le_of_real_iff_coe_le
- \- *lemma* le_of_real_iff_coe_le'
- \- *lemma* of_real_lt_iff_lt_coe
- \- *lemma* lt_of_real_iff_coe_lt
- \- *lemma* of_real_bit0
- \- *lemma* of_real_bit1
- \- *lemma* of_real_mul
- \- *lemma* of_real_inv
- \- *lemma* of_real_div
- \- *lemma* of_real_div'
- \- *lemma* nnreal.coe_of_real_le
- \+ *def* _root_.real.to_nnreal

Modified src/data/real/sqrt.lean


Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_eq_lintegral_pos_part_sub_lintegral_neg_part
- \+/\- *lemma* lintegral_coe_eq_integral
- \- *lemma* integral_eq_lintegral_max_sub_lintegral_min

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.real_to_nnreal
- \+ *lemma* ae_measurable.real_to_nnreal
- \+ *lemma* ae_measurable.nnreal_coe
- \- *lemma* measurable.nnreal_of_real

Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* has_finite_integral_iff_of_nnreal

Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* continuous_of_real

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
- \+ *lemma* stalk_map_germ

Modified src/topology/sheaves/stalks.lean
- \+ *lemma* stalk_pushforward_germ



## [2021-06-02 04:57:05](https://github.com/leanprover-community/mathlib/commit/2164107)
refactor(algebraic_geometry/structure_sheaf): Rename Spec.Top to prime_spectrum.Top ([#7786](https://github.com/leanprover-community/mathlib/pull/7786))
Renames `Spec.Top` to `prime_specturm.Top` to free up the namespace for the Spec functor.
#### Estimated changes
Modified src/algebraic_geometry/structure_sheaf.lean
- \+/\- *lemma* res_apply
- \+/\- *lemma* const_apply
- \+/\- *lemma* const_apply'
- \+/\- *lemma* exists_const
- \+/\- *lemma* to_open_res
- \+/\- *lemma* to_open_apply
- \+/\- *lemma* to_open_eq_const
- \+/\- *lemma* to_open_germ
- \+/\- *lemma* germ_to_open
- \+/\- *lemma* germ_to_top
- \+/\- *lemma* is_unit_to_stalk
- \+/\- *lemma* localization_to_stalk_of
- \+/\- *lemma* localization_to_stalk_mk'
- \+/\- *lemma* coe_open_to_localization
- \+/\- *lemma* open_to_localization_apply
- \+/\- *lemma* germ_comp_stalk_to_fiber_ring_hom
- \+/\- *lemma* stalk_to_fiber_ring_hom_germ'
- \+/\- *lemma* stalk_to_fiber_ring_hom_germ
- \+/\- *lemma* to_stalk_comp_stalk_to_fiber_ring_hom
- \+/\- *lemma* stalk_to_fiber_ring_hom_to_stalk
- \+/\- *lemma* locally_const_basic_open
- \+/\- *lemma* normalize_finite_fraction_representation
- \+ *def* prime_spectrum.Top
- \+/\- *def* localizations
- \+/\- *def* is_fraction
- \+/\- *def* sections_subring
- \+/\- *def* structure_sheaf_in_Type
- \+/\- *def* structure_presheaf_in_CommRing
- \+/\- *def* structure_sheaf
- \+/\- *def* const
- \+/\- *def* to_open
- \+/\- *def* to_stalk
- \+/\- *def* localization_to_stalk
- \+/\- *def* open_to_localization
- \+/\- *def* stalk_to_fiber_ring_hom
- \+/\- *def* stalk_iso
- \+/\- *def* to_basic_open
- \- *def* Spec.Top



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
- \+ *theorem* Sup_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* supr_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* infi_eq_of_forall_ge_of_forall_gt_exists_lt

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cSup_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* cInf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* csupr_eq_of_forall_le_of_forall_lt_exists_gt
- \+ *theorem* cinfi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+ *theorem* cSup_eq_of_is_forall_le_of_forall_le_imp_ge
- \- *theorem* cSup_intro
- \- *theorem* cInf_intro
- \- *theorem* cSup_intro'

Modified src/topology/algebra/ordered/liminf_limsup.lean




## [2021-06-02 04:56:59](https://github.com/leanprover-community/mathlib/commit/6b2c7a7)
feat(data/finset/noncomm_prod): finset products over monoid ([#7567](https://github.com/leanprover-community/mathlib/pull/7567))
The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.
#### Estimated changes
Created src/data/finset/noncomm_prod.lean
- \+ *lemma* noncomm_foldr_coe
- \+ *lemma* noncomm_foldr_empty
- \+ *lemma* noncomm_foldr_cons
- \+ *lemma* noncomm_foldr_eq_foldr
- \+ *lemma* noncomm_fold_coe
- \+ *lemma* noncomm_fold_empty
- \+ *lemma* noncomm_fold_cons
- \+ *lemma* noncomm_fold_eq_fold
- \+ *lemma* noncomm_prod_coe
- \+ *lemma* noncomm_prod_empty
- \+ *lemma* noncomm_prod_cons
- \+ *lemma* noncomm_prod_cons'
- \+ *lemma* noncomm_prod_eq_prod
- \+ *lemma* noncomm_prod_to_finset
- \+ *lemma* noncomm_prod_insert_of_not_mem
- \+ *lemma* noncomm_prod_insert_of_not_mem'
- \+ *def* noncomm_foldr
- \+ *def* noncomm_fold
- \+ *def* noncomm_prod



## [2021-06-01 23:18:36](https://github.com/leanprover-community/mathlib/commit/681b9c2)
feat(ring_theory/adjoin/basic): add missing lemmas ([#7780](https://github.com/leanprover-community/mathlib/pull/7780))
Two missing lemmas about `adjoin`.
These are the `subalgebra` versions of `submodule.span_eq_of_le` and `submodule.span_eq`.
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean
- \+ *theorem* adjoin_eq_of_le
- \+ *theorem* adjoin_eq



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
- \- *lemma* pow_lt_pow_succ
- \- *lemma* lt_pow_self
- \- *lemma* lt_two_pow
- \- *lemma* one_le_pow
- \- *lemma* one_le_pow'
- \- *lemma* one_le_two_pow
- \- *lemma* one_lt_pow
- \- *lemma* one_lt_pow'
- \- *lemma* one_lt_two_pow
- \- *lemma* one_lt_two_pow'
- \- *lemma* pow_right_strict_mono
- \- *lemma* pow_le_iff_le_right
- \- *lemma* pow_lt_iff_lt_right
- \- *lemma* pow_right_injective
- \- *lemma* pow_left_strict_mono
- \- *lemma* mul_lt_mul_pow_succ
- \- *lemma* strict_mono.nat_pow
- \- *lemma* pow_le_iff_le_left
- \- *lemma* pow_lt_iff_lt_left
- \- *lemma* pow_left_injective
- \- *lemma* pow_dvd_pow_iff_pow_le_pow
- \- *lemma* pow_dvd_pow_iff_le_right
- \- *lemma* pow_dvd_pow_iff_le_right'
- \- *lemma* not_pos_pow_dvd
- \- *lemma* pow_dvd_of_le_of_pow_dvd
- \- *lemma* dvd_of_pow_dvd
- \- *lemma* pow_div
- \- *lemma* shiftl_eq_mul_pow
- \- *lemma* shiftl'_tt_eq_mul_pow
- \- *lemma* one_shiftl
- \- *lemma* zero_shiftl
- \- *lemma* shiftr_eq_div_pow
- \- *lemma* zero_shiftr
- \- *theorem* pow_le_pow_of_le_right
- \- *theorem* pow_lt_pow_of_lt_left
- \- *theorem* pow_lt_pow_of_lt_right
- \- *theorem* sq_sub_sq
- \- *theorem* mod_pow_succ
- \- *theorem* shiftl'_ne_zero_left
- \- *theorem* shiftl'_tt_ne_zero
- \- *theorem* size_zero
- \- *theorem* size_bit
- \- *theorem* size_bit0
- \- *theorem* size_bit1
- \- *theorem* size_one
- \- *theorem* size_shiftl'
- \- *theorem* size_shiftl
- \- *theorem* lt_size_self
- \- *theorem* size_le
- \- *theorem* lt_size
- \- *theorem* size_pos
- \- *theorem* size_eq_zero
- \- *theorem* size_pow
- \- *theorem* size_le_size

Modified src/data/nat/factorial.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/log.lean


Created src/data/nat/pow.lean
- \+ *lemma* pow_lt_pow_succ
- \+ *lemma* lt_pow_self
- \+ *lemma* lt_two_pow
- \+ *lemma* one_le_pow
- \+ *lemma* one_le_pow'
- \+ *lemma* one_le_two_pow
- \+ *lemma* one_lt_pow
- \+ *lemma* one_lt_pow'
- \+ *lemma* one_lt_two_pow
- \+ *lemma* one_lt_two_pow'
- \+ *lemma* pow_right_strict_mono
- \+ *lemma* pow_le_iff_le_right
- \+ *lemma* pow_lt_iff_lt_right
- \+ *lemma* pow_right_injective
- \+ *lemma* pow_left_strict_mono
- \+ *lemma* mul_lt_mul_pow_succ
- \+ *lemma* strict_mono.nat_pow
- \+ *lemma* pow_le_iff_le_left
- \+ *lemma* pow_lt_iff_lt_left
- \+ *lemma* pow_left_injective
- \+ *lemma* pow_dvd_pow_iff_pow_le_pow
- \+ *lemma* pow_dvd_pow_iff_le_right
- \+ *lemma* pow_dvd_pow_iff_le_right'
- \+ *lemma* not_pos_pow_dvd
- \+ *lemma* pow_dvd_of_le_of_pow_dvd
- \+ *lemma* dvd_of_pow_dvd
- \+ *lemma* pow_div
- \+ *lemma* shiftl_eq_mul_pow
- \+ *lemma* shiftl'_tt_eq_mul_pow
- \+ *lemma* one_shiftl
- \+ *lemma* zero_shiftl
- \+ *lemma* shiftr_eq_div_pow
- \+ *lemma* zero_shiftr
- \+ *theorem* pow_le_pow_of_le_right
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_lt_pow_of_lt_right
- \+ *theorem* sq_sub_sq
- \+ *theorem* mod_pow_succ
- \+ *theorem* shiftl'_ne_zero_left
- \+ *theorem* shiftl'_tt_ne_zero
- \+ *theorem* size_zero
- \+ *theorem* size_bit
- \+ *theorem* size_bit0
- \+ *theorem* size_bit1
- \+ *theorem* size_one
- \+ *theorem* size_shiftl'
- \+ *theorem* size_shiftl
- \+ *theorem* lt_size_self
- \+ *theorem* size_le
- \+ *theorem* lt_size
- \+ *theorem* size_pos
- \+ *theorem* size_eq_zero
- \+ *theorem* size_pow
- \+ *theorem* size_le_size

Modified src/data/pnat/basic.lean




## [2021-06-01 23:18:35](https://github.com/leanprover-community/mathlib/commit/2689c51)
feat(category_theory/abelian): abelian categories with enough projectives have projective resolutions ([#7488](https://github.com/leanprover-community/mathlib/pull/7488))
#### Estimated changes
Modified src/category_theory/abelian/projective.lean
- \+ *def* of_complex
- \+ *def* of



## [2021-06-01 20:17:20](https://github.com/leanprover-community/mathlib/commit/4e7c6b2)
chore(algebra/associated): weaken some typeclass assumptions ([#7760](https://github.com/leanprover-community/mathlib/pull/7760))
Also golf ne_zero_iff_of_associated a little.
#### Estimated changes
Modified src/algebra/associated.lean
- \+/\- *lemma* dvd_iff_dvd_of_rel_left
- \+/\- *lemma* dvd_iff_dvd_of_rel_right
- \+/\- *lemma* eq_zero_iff_of_associated
- \+/\- *lemma* ne_zero_iff_of_associated
- \+/\- *lemma* associated_of_irreducible_of_dvd
- \+/\- *lemma* irreducible_of_associated
- \+/\- *lemma* irreducible_iff_of_associated



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
- \+ *lemma* add_monoid_hom.to_nat_linear_map_injective
- \+ *lemma* add_monoid_hom.to_int_linear_map_injective
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
- \+ *def* equivalence_right_to_left
- \+ *def* equivalence_left_to_right
- \+ *def* cech_nerve_equiv
- \+ *def* cech_conerve
- \+ *def* augmented_cech_conerve
- \+ *def* cech_conerve_equiv

Modified src/algebraic_topology/simplex_category.lean
- \+ *lemma* const_comp
- \+ *def* const

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* to_arrow



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
- \+ *def* hom.f_add_monoid_hom

