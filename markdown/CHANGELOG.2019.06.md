## [2019-06-29 16:56:28](https://github.com/leanprover-community/mathlib/commit/469da29)
feat(data/list/basic): map_nil and map_eq_nil ([#1161](https://github.com/leanprover-community/mathlib/pull/1161))
* feat(data/list/basic): map_nil and map_eq_nil
* Update basic.lean
* make Simon's changes
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.map_eq_nil



## [2019-06-29 13:28:56](https://github.com/leanprover-community/mathlib/commit/0858157)
refactor(category_theory/category): reorder arguments of `End.has_mul` ([#1128](https://github.com/leanprover-community/mathlib/pull/1128))
* Reorder arguments of `End.has_mul` and `Aut.has_mul`, adjust `category/fold`
* clean up proofs in `category.fold`
#### Estimated changes
Modified src/category/fold.lean
- \+ *def* monoid.foldl.get
- \+/\- *def* monoid.foldl.mk
- \+/\- *def* monoid.foldl
- \+/\- *def* monoid.foldr.get
- \+/\- *def* monoid.foldr.mk
- \+/\- *def* monoid.foldr
- \+ *def* monoid.mfoldl.get
- \+/\- *def* monoid.mfoldl.mk
- \+/\- *def* monoid.mfoldl
- \+/\- *def* monoid.mfoldr.get
- \+/\- *def* monoid.mfoldr.mk
- \+ *lemma* traversable.foldl.unop_of_free_monoid
- \- *lemma* traversable.foldr.unop_of_free_monoid
- \+ *lemma* traversable.mfoldl.unop_of_free_monoid
- \- *lemma* traversable.mfoldr.unop_of_free_monoid

Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.End.mul_def

Modified src/category_theory/isomorphism.lean


Modified src/data/opposite.lean
- \+ *lemma* opposite.op_inj_iff
- \+ *lemma* opposite.unop_inj_iff



## [2019-06-29 12:31:13](https://github.com/leanprover-community/mathlib/commit/e310349)
refactor(ring_theory/ideals): refactor local rings, add local ring homs ([#1102](https://github.com/leanprover-community/mathlib/pull/1102))
* WIP
* refactor(ring_theory/ideals): refactor local rings, add local ring homs
* residue_field.map is a field hom
* make is_local_ring_hom extends is_ring_hom
* refactor local_ring
* tiny changes
* Bump instance search depth
#### Estimated changes
Modified src/data/mv_polynomial.lean


Modified src/data/padics/padic_integers.lean


Modified src/ring_theory/ideals.lean
- \+/\- *theorem* coe_subset_nonunits
- \+ *lemma* exists_max_ideal_of_mem_nonunits
- \+/\- *theorem* ideal.is_coprime_def
- \+/\- *theorem* ideal.is_coprime_self
- \+/\- *theorem* ideal.mem_span_pair
- \- *def* is_local_ring.zero_ne_one
- \+/\- *def* is_local_ring
- \+ *lemma* is_unit_of_map_unit
- \+ *def* local_of_is_local_ring
- \+ *def* local_of_nonunits_ideal
- \- *theorem* local_of_nonunits_ideal
- \+ *def* local_of_unique_max_ideal
- \+ *def* local_of_unit_or_unit_one_sub
- \+ *lemma* local_ring.is_unit_of_mem_nonunits_one_sub_self
- \+ *lemma* local_ring.is_unit_one_sub_self_of_mem_nonunits
- \+ *lemma* local_ring.is_unit_or_is_unit_one_sub_self
- \+ *lemma* local_ring.max_ideal_unique
- \+ *lemma* local_ring.mem_nonunits_ideal
- \+ *lemma* local_ring.nonunits_add
- \+ *def* local_ring.nonunits_ideal
- \+ *def* local_ring.residue_field
- \+ *lemma* map_nonunit
- \- *theorem* mem_nonunits_ideal
- \+/\- *theorem* mem_nonunits_iff
- \+/\- *theorem* mul_mem_nonunits_left
- \+/\- *theorem* mul_mem_nonunits_right
- \+/\- *def* nonunits
- \- *def* nonunits_ideal
- \+/\- *theorem* one_not_mem_nonunits
- \+/\- *theorem* zero_mem_nonunits

Modified src/ring_theory/localization.lean




## [2019-06-28 15:11:00](https://github.com/leanprover-community/mathlib/commit/4a5a1a5)
fix(data/list/min_max): correct names of mem_maximum and mem_minimum ([#1162](https://github.com/leanprover-community/mathlib/pull/1162))
* fix(data/list/min_max): correct names of mem_maximum and mem_minimum
* Update denumerable.lean
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/list/min_max.lean
- \+ *theorem* list.maximum_mem
- \- *theorem* list.mem_maximum
- \- *theorem* list.mem_minimum
- \+ *theorem* list.minimum_mem



## [2019-06-28 09:09:55](https://github.com/leanprover-community/mathlib/commit/7d56447)
feat(logic/unique): fin 1 is unique ([#1158](https://github.com/leanprover-community/mathlib/pull/1158))
#### Estimated changes
Modified src/logic/unique.lean




## [2019-06-27 11:12:29](https://github.com/leanprover-community/mathlib/commit/6bc930a)
chore(src/tactic/interactive): `convert` docstring ([#1148](https://github.com/leanprover-community/mathlib/pull/1148))
* chore(src/tactic/interactive): `convert` docstring 
The `using` option to `convert` was not mentioned in the docstring, and I often struggle to remember the (perhaps slightly exotic?) `using` catchphrase
* Update src/tactic/interactive.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update interactive.lean
#### Estimated changes
Modified src/tactic/interactive.lean




## [2019-06-26 12:11:33](https://github.com/leanprover-community/mathlib/commit/9b0fd36)
feat(data/fintype): unique.fintype ([#1154](https://github.com/leanprover-community/mathlib/pull/1154))
#### Estimated changes
Modified src/data/fintype.lean




## [2019-06-25 14:30:39](https://github.com/leanprover-community/mathlib/commit/7484ab4)
fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement ([#1151](https://github.com/leanprover-community/mathlib/pull/1151))
* fix(data/matrix): add brackets to mul_neg and neg_mul to correct statement
Each side of `mul_neg` was identical.
* fix
#### Estimated changes
Modified src/data/matrix.lean




## [2019-06-25 13:00:33](https://github.com/leanprover-community/mathlib/commit/a2aeabb)
feat(data/finset): length_sort ([#1150](https://github.com/leanprover-community/mathlib/pull/1150))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.length_sort

Modified src/data/list/sort.lean
- \+ *lemma* list.length_merge_sort

Modified src/data/multiset.lean
- \+ *theorem* multiset.length_sort



## [2019-06-25 13:54:02+02:00](https://github.com/leanprover-community/mathlib/commit/c4a4f79)
feat(algebra/pi_instances): pi.ordered_comm_group ([#1152](https://github.com/leanprover-community/mathlib/pull/1152))
#### Estimated changes
Modified src/algebra/pi_instances.lean




## [2019-06-24 12:33:51](https://github.com/leanprover-community/mathlib/commit/c7ee110)
feat(meta/expr): `simp` and `dsimp` an expr ([#1147](https://github.com/leanprover-community/mathlib/pull/1147))
* feat(meta/expr): `simp` and `dsimp` an expr
* removing def that we don't need yet
#### Estimated changes
Modified src/meta/expr.lean




## [2019-06-23 02:01:56](https://github.com/leanprover-community/mathlib/commit/d7283d7)
feat(string): `split_on` a `char` ([#1145](https://github.com/leanprover-community/mathlib/pull/1145))
* lib: string
* type
#### Estimated changes
Modified src/data/string/defs.lean
- \+ *def* string.split_on



## [2019-06-20 08:30:31](https://github.com/leanprover-community/mathlib/commit/a35d682)
feat(topology/order): more facts on continuous_on ([#1140](https://github.com/leanprover-community/mathlib/pull/1140))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_on.inv
- \+ *lemma* continuous_on.sub

Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_on.mul

Modified src/topology/basic.lean
- \+ *theorem* nhds_within_le_of_mem
- \+ *theorem* nhds_within_restrict''
- \+ *theorem* self_mem_nhds_within

Modified src/topology/order.lean
- \+ *lemma* continuous.comp_continuous_on
- \+ *lemma* continuous.continuous_at
- \+ *lemma* continuous_at.preimage_mem_nhds
- \+ *lemma* continuous_on.preimage_closed_of_closed
- \+ *theorem* continuous_on_iff_is_closed
- \+ *lemma* continuous_on_open_iff
- \+ *lemma* continuous_on_open_of_generate_from
- \+ *lemma* continuous_within_at.congr_of_mem_nhds_within
- \+ *lemma* continuous_within_at.continuous_at
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within
- \+ *lemma* continuous_within_at_inter'
- \+ *lemma* continuous_within_at_inter



## [2019-06-19 21:00:28](https://github.com/leanprover-community/mathlib/commit/e598894)
chore(topology/*): reverse order on topological and uniform spaces ([#1138](https://github.com/leanprover-community/mathlib/pull/1138))
* chore(topology/*): reverse order on topological and uniform spaces
* fix(topology/order): private lemma hiding partial order oscillation,
following Mario's suggestion
* change a temporary name
Co-Authored-By: Johan Commelin <johan@commelin.net>
* forgotten rename
#### Estimated changes
Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* ennreal.measurable_sub
- \+/\- *lemma* nnreal.measurable_add
- \+/\- *lemma* nnreal.measurable_mul
- \+/\- *lemma* nnreal.measurable_sub

Modified src/order/complete_lattice.lean
- \+ *theorem* lattice.infi_pair
- \+ *theorem* lattice.supr_pair

Modified src/topology/Top/adjunctions.lean


Modified src/topology/Top/basic.lean


Modified src/topology/Top/limits.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.continuous_sub'
- \+/\- *lemma* nnreal.continuous_sub

Modified src/topology/maps.lean


Modified src/topology/order.lean
- \+ *lemma* coinduced_bot
- \- *lemma* coinduced_inf
- \- *lemma* coinduced_infi
- \+ *lemma* coinduced_le_iff_le_induced
- \+ *lemma* coinduced_sup
- \+ *lemma* coinduced_supr
- \- *lemma* coinduced_top
- \+/\- *lemma* continuous_Inf_dom
- \+/\- *lemma* continuous_Inf_rng
- \+/\- *lemma* continuous_Sup_dom
- \+/\- *lemma* continuous_Sup_rng
- \+/\- *lemma* continuous_bot
- \+ *lemma* continuous_iff_coinduced_le
- \- *lemma* continuous_iff_induced_le
- \- *lemma* continuous_iff_le_coinduced
- \+ *lemma* continuous_iff_le_induced
- \- *lemma* continuous_inf_dom
- \+ *lemma* continuous_inf_dom_left
- \+ *lemma* continuous_inf_dom_right
- \+ *lemma* continuous_inf_rng
- \- *lemma* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_right
- \+/\- *lemma* continuous_infi_dom
- \+/\- *lemma* continuous_infi_rng
- \+ *lemma* continuous_sup_dom
- \- *lemma* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_right
- \- *lemma* continuous_sup_rng
- \+ *lemma* continuous_sup_rng_left
- \+ *lemma* continuous_sup_rng_right
- \+/\- *lemma* continuous_supr_dom
- \+/\- *lemma* continuous_supr_rng
- \+/\- *lemma* continuous_top
- \+ *lemma* eq_bot_of_singletons_open
- \+/\- *lemma* eq_of_nhds_eq_nhds
- \- *lemma* eq_top_of_singletons_open
- \+ *lemma* gc_coinduced_induced
- \- *lemma* gc_induced_coinduced
- \- *lemma* generate_from_le
- \- *lemma* generate_from_le_iff_subset_is_open
- \- *lemma* induced_bot
- \+ *lemma* induced_inf
- \+ *lemma* induced_infi
- \- *lemma* induced_le_iff_le_coinduced
- \- *lemma* induced_sup
- \- *lemma* induced_supr
- \+ *lemma* induced_top
- \+/\- *lemma* is_closed_infi_iff
- \- *lemma* is_open_infi_iff
- \+ *lemma* is_open_supr_iff
- \+ *lemma* le_generate_from
- \+ *lemma* le_generate_from_iff_subset_is_open
- \+/\- *lemma* le_of_nhds_le_nhds
- \+ *lemma* nhds_Inf
- \- *lemma* nhds_Sup
- \+/\- *lemma* nhds_bot
- \+ *lemma* nhds_inf
- \+ *lemma* nhds_infi
- \- *lemma* nhds_sup
- \- *lemma* nhds_supr
- \+/\- *lemma* nhds_top
- \+ *def* tmp_complete_lattice
- \+ *def* tmp_order

Modified src/topology/separation.lean


Modified src/topology/stone_cech.lean
- \+/\- *lemma* dense_embedding_pure

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* inf_uniformity
- \+ *lemma* infi_uniformity
- \- *lemma* sup_uniformity
- \- *lemma* supr_uniformity
- \+ *lemma* to_topological_space_Inf
- \- *lemma* to_topological_space_Sup
- \+/\- *lemma* to_topological_space_bot
- \+ *lemma* to_topological_space_inf
- \+ *lemma* to_topological_space_infi
- \- *lemma* to_topological_space_sup
- \- *lemma* to_topological_space_supr
- \+/\- *lemma* to_topological_space_top

Modified src/topology/uniform_space/pi.lean




## [2019-06-19 08:03:18](https://github.com/leanprover-community/mathlib/commit/b1cb48d)
feat(data/set): simple lemmas, renaming ([#1137](https://github.com/leanprover-community/mathlib/pull/1137))
* feat(data/set): simple lemmas, renaming
* improve projection lemmas
* arguments order
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.fst_image_prod
- \+ *lemma* set.fst_image_prod_subset
- \+/\- *theorem* set.preimage_id
- \+ *lemma* set.snd_image_prod
- \+ *lemma* set.snd_image_prod_subset

Modified src/data/set/lattice.lean
- \+ *theorem* set.Inter_inter
- \+ *theorem* set.Union_diff
- \+ *theorem* set.Union_inter
- \+ *theorem* set.Union_union
- \+ *theorem* set.bUnion_inter
- \+ *theorem* set.diff_Inter
- \- *theorem* set.diff_Inter_left
- \+ *theorem* set.diff_Union
- \- *theorem* set.diff_Union_left
- \- *theorem* set.diff_Union_right
- \+ *theorem* set.inter_Inter
- \- *theorem* set.inter_Inter_left
- \- *theorem* set.inter_Inter_right
- \+ *theorem* set.inter_Union
- \- *theorem* set.inter_Union_left
- \- *theorem* set.inter_Union_right
- \+ *theorem* set.inter_bUnion
- \+ *theorem* set.union_Inter
- \- *theorem* set.union_Inter_left
- \+ *theorem* set.union_Union
- \- *theorem* set.union_Union_left
- \- *theorem* set.union_Union_right

Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.limsup_lintegral_le
- \+/\- *lemma* measure_theory.lintegral_supr_ae

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.all_ae_of_all

Modified src/measure_theory/outer_measure.lean




## [2019-06-18 22:06:30](https://github.com/leanprover-community/mathlib/commit/235b899)
fix(category_theory/types): rename lemma `ulift_functor.map` ([#1133](https://github.com/leanprover-community/mathlib/pull/1133))
* fix(category_theory/types): avoid shadowing `ulift_functor.map` by a lemma
Now we can use `ulift_functor.map` in the sense `functor.map ulift_functor`.
* `ulift_functor.map_spec` → `ulift_functor_map`
as suggested by @semorrison in https://github.com/leanprover-community/mathlib/pull/1133#pullrequestreview-250179914
#### Estimated changes
Modified src/category_theory/types.lean
- \- *lemma* category_theory.ulift_functor.map
- \+ *lemma* category_theory.ulift_functor_map



## [2019-06-17 13:09:55](https://github.com/leanprover-community/mathlib/commit/d8d25e9)
refactor(analysis/normed_space/deriv): split and move to calculus folder ([#1135](https://github.com/leanprover-community/mathlib/pull/1135))
#### Estimated changes
Renamed src/analysis/normed_space/deriv.lean to src/analysis/calculus/deriv.lean
- \- *lemma* is_open.unique_diff_on
- \- *lemma* is_open.unique_diff_within_at
- \- *lemma* tangent_cone_at.lim_zero
- \- *def* tangent_cone_at
- \- *lemma* tangent_cone_inter_open
- \- *lemma* tangent_cone_mono
- \- *lemma* tangent_cone_univ
- \- *def* unique_diff_on
- \- *lemma* unique_diff_on_inter
- \- *def* unique_diff_within_at
- \- *lemma* unique_diff_within_at_inter
- \- *lemma* unique_diff_within_univ_at

Added src/analysis/calculus/tangent_cone.lean
- \+ *lemma* is_open.unique_diff_on
- \+ *lemma* is_open.unique_diff_within_at
- \+ *lemma* tangent_cone_at.lim_zero
- \+ *def* tangent_cone_at
- \+ *lemma* tangent_cone_inter_open
- \+ *lemma* tangent_cone_mono
- \+ *lemma* tangent_cone_univ
- \+ *def* unique_diff_on
- \+ *lemma* unique_diff_on_inter
- \+ *def* unique_diff_within_at
- \+ *lemma* unique_diff_within_at_inter
- \+ *lemma* unique_diff_within_univ_at



## [2019-06-16 19:28:43](https://github.com/leanprover-community/mathlib/commit/7b715eb)
Direct limit of modules, abelian groups, rings, and fields. ([#754](https://github.com/leanprover-community/mathlib/pull/754))
* stuff
* stuff
* more stuff
* pre merge commit
* prove of_zero.exact
* remove silly rewrite
* slightly shorten proof
* direct limit of modules
* upgrade mathlib
* direct limit of rings
* direct limit of fields (WIP)
* trying to prove zero_exact for rings
* use sqrt 2 instead of F4
* direct limit of field
* cleanup for mathlib
* remove ununsed lemmas
* clean up
* docstrings
* local
* fix build
* Replace real with polynomial int in proof
* Update basic.lean
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *theorem* finset.exists_le

Added src/algebra/direct_limit.lean
- \+ *def* add_comm_group.direct_limit.directed_system
- \+ *def* add_comm_group.direct_limit.lift
- \+ *lemma* add_comm_group.direct_limit.lift_add
- \+ *lemma* add_comm_group.direct_limit.lift_neg
- \+ *lemma* add_comm_group.direct_limit.lift_of
- \+ *lemma* add_comm_group.direct_limit.lift_sub
- \+ *lemma* add_comm_group.direct_limit.lift_unique
- \+ *lemma* add_comm_group.direct_limit.lift_zero
- \+ *theorem* add_comm_group.direct_limit.of.zero_exact
- \+ *def* add_comm_group.direct_limit.of
- \+ *lemma* add_comm_group.direct_limit.of_add
- \+ *lemma* add_comm_group.direct_limit.of_f
- \+ *lemma* add_comm_group.direct_limit.of_neg
- \+ *lemma* add_comm_group.direct_limit.of_sub
- \+ *lemma* add_comm_group.direct_limit.of_zero
- \+ *def* add_comm_group.direct_limit
- \+ *theorem* field.direct_limit.exists_inv
- \+ *theorem* module.direct_limit.exists_of
- \+ *def* module.direct_limit.lift
- \+ *lemma* module.direct_limit.lift_of
- \+ *theorem* module.direct_limit.lift_unique
- \+ *theorem* module.direct_limit.of.zero_exact
- \+ *lemma* module.direct_limit.of.zero_exact_aux
- \+ *def* module.direct_limit.of
- \+ *lemma* module.direct_limit.of_f
- \+ *lemma* module.direct_limit.to_module_totalize_of_le
- \+ *lemma* module.direct_limit.totalize_apply
- \+ *def* module.direct_limit
- \+ *theorem* ring.direct_limit.exists_of
- \+ *theorem* ring.direct_limit.induction_on
- \+ *def* ring.direct_limit.lift
- \+ *lemma* ring.direct_limit.lift_add
- \+ *lemma* ring.direct_limit.lift_mul
- \+ *lemma* ring.direct_limit.lift_neg
- \+ *lemma* ring.direct_limit.lift_of
- \+ *lemma* ring.direct_limit.lift_one
- \+ *lemma* ring.direct_limit.lift_pow
- \+ *lemma* ring.direct_limit.lift_sub
- \+ *theorem* ring.direct_limit.lift_unique
- \+ *lemma* ring.direct_limit.lift_zero
- \+ *lemma* ring.direct_limit.of.zero_exact
- \+ *lemma* ring.direct_limit.of.zero_exact_aux2
- \+ *lemma* ring.direct_limit.of.zero_exact_aux
- \+ *def* ring.direct_limit.of
- \+ *lemma* ring.direct_limit.of_add
- \+ *lemma* ring.direct_limit.of_f
- \+ *theorem* ring.direct_limit.of_inj
- \+ *lemma* ring.direct_limit.of_mul
- \+ *lemma* ring.direct_limit.of_neg
- \+ *lemma* ring.direct_limit.of_one
- \+ *lemma* ring.direct_limit.of_pow
- \+ *lemma* ring.direct_limit.of_sub
- \+ *lemma* ring.direct_limit.of_zero
- \+ *def* ring.direct_limit

Modified src/algebra/module.lean
- \+ *def* is_add_group_hom.to_linear_map

Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.support_smul

Modified src/data/polynomial.lean
- \+ *lemma* polynomial.int_cast_eq_C
- \+ *lemma* polynomial.nat_cast_eq_C
- \+ *lemma* polynomial.nat_degree_int_cast
- \+ *lemma* polynomial.nat_degree_nat_cast

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* direct_sum.apply_eq_component
- \+ *lemma* direct_sum.component.lof_self
- \+ *lemma* direct_sum.component.of
- \+ *def* direct_sum.component
- \+ *lemma* direct_sum.ext
- \+ *lemma* direct_sum.ext_iff
- \+ *lemma* direct_sum.lof_apply
- \+ *lemma* direct_sum.single_eq_lof

Modified src/linear_algebra/tensor_product.lean


Modified src/order/basic.lean


Modified src/ring_theory/free_comm_ring.lean
- \+ *theorem* free_comm_ring.exists_finite_support
- \+ *theorem* free_comm_ring.exists_finset_support
- \+ *def* free_comm_ring.is_supported
- \+ *theorem* free_comm_ring.is_supported_add
- \+ *theorem* free_comm_ring.is_supported_int
- \+ *theorem* free_comm_ring.is_supported_mul
- \+ *theorem* free_comm_ring.is_supported_neg
- \+ *theorem* free_comm_ring.is_supported_of
- \+ *theorem* free_comm_ring.is_supported_one
- \+ *theorem* free_comm_ring.is_supported_sub
- \+ *theorem* free_comm_ring.is_supported_upwards
- \+ *theorem* free_comm_ring.is_supported_zero
- \+ *theorem* free_comm_ring.map_subtype_val_restriction
- \+ *def* free_comm_ring.restriction
- \+ *lemma* free_comm_ring.restriction_add
- \+ *lemma* free_comm_ring.restriction_mul
- \+ *lemma* free_comm_ring.restriction_neg
- \+ *lemma* free_comm_ring.restriction_of
- \+ *lemma* free_comm_ring.restriction_one
- \+ *lemma* free_comm_ring.restriction_sub
- \+ *lemma* free_comm_ring.restriction_zero

Modified src/ring_theory/free_ring.lean




## [2019-06-16 19:04:52](https://github.com/leanprover-community/mathlib/commit/38d5c12)
feat(ring_theory/integral_closure): integral closure ([#1087](https://github.com/leanprover-community/mathlib/pull/1087))
* feat(ring_theory/integral_closure): integral closure
* update
#### Estimated changes
Added src/ring_theory/integral_closure.lean
- \+ *theorem* fg_adjoin_of_finite
- \+ *theorem* fg_adjoin_singleton_of_integral
- \+ *def* integral_closure
- \+ *theorem* integral_closure_idem
- \+ *def* is_integral
- \+ *theorem* is_integral_add
- \+ *theorem* is_integral_algebra_map
- \+ *theorem* is_integral_iff_is_integral_closure_finite
- \+ *theorem* is_integral_mul
- \+ *theorem* is_integral_neg
- \+ *theorem* is_integral_of_mem_closure
- \+ *theorem* is_integral_of_mem_of_fg
- \+ *theorem* is_integral_of_noetherian'
- \+ *theorem* is_integral_of_noetherian
- \+ *theorem* is_integral_of_subring
- \+ *theorem* is_integral_one
- \+ *theorem* is_integral_sub
- \+ *theorem* is_integral_zero
- \+ *theorem* mem_integral_closure_iff_mem_fg



## [2019-06-15 01:30:00](https://github.com/leanprover-community/mathlib/commit/3ad3522)
feat(data/rat/denumerable): computable denumerability of Q ([#1104](https://github.com/leanprover-community/mathlib/pull/1104))
* feat(data/rat/denumerable): computable denumerability of Q
* blah
* fix build
* remove unnecessary decidable_eq
* add header
* delete rat.lean and update imports
* fix build
* prove exists_not_mem_finset
* massively speed up encode
* minor change
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/data/equiv/denumerable.lean
- \+ *def* denumerable.of_encodable_of_infinite
- \+ *def* nat.subtype.denumerable
- \+ *lemma* nat.subtype.exists_succ
- \+ *lemma* nat.subtype.le_succ_of_forall_lt_le
- \+ *lemma* nat.subtype.lt_succ_iff_le
- \+ *lemma* nat.subtype.lt_succ_self
- \+ *def* nat.subtype.of_nat
- \+ *lemma* nat.subtype.of_nat_surjective
- \+ *lemma* nat.subtype.of_nat_surjective_aux
- \+ *def* nat.subtype.succ
- \+ *lemma* nat.subtype.succ_le_of_lt

Modified src/data/equiv/encodable.lean
- \+ *def* encodable.decidable_range_encode
- \+ *def* encodable.equiv_range_encode

Modified src/data/fintype.lean
- \+ *lemma* infinite.exists_not_mem_finset
- \+ *lemma* infinite.of_injective
- \+ *lemma* infinite.of_surjective

Modified src/data/fp/basic.lean


Modified src/data/option/basic.lean
- \+ *lemma* option.get_some
- \+ *lemma* option.some_get

Modified src/data/padics/padic_norm.lean


Renamed src/data/rat.lean to src/data/rat/basic.lean


Added src/data/rat/denumerable.lean


Modified src/measure_theory/outer_measure.lean


Modified src/order/bounded_lattice.lean


Modified src/tactic/norm_num.lean




## [2019-06-14 17:40:58](https://github.com/leanprover-community/mathlib/commit/5040c81)
feat(measure_theory/integration): dominated convergence theorem ([#1123](https://github.com/leanprover-community/mathlib/pull/1123))
* Create .DS_Store
* Revert "Create .DS_Store"
This reverts commit 5612886d493aef59205eddc5a34a75e6e5ba22c1.
* feat(measure_theory/integration): dominated convergence theorem
* Changes to styles
* Update ordered.lean
* Changes to styles
* Update integration.lean
* Changes to styles
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.sub_left_inj

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ennreal.measurable_add
- \+ *lemma* ennreal.measurable_sub
- \+ *lemma* measure_theory.measurable.infi_Prop
- \+ *lemma* measure_theory.measurable.supr_Prop
- \+ *lemma* nnreal.measurable_add
- \+ *lemma* nnreal.measurable_mul
- \+ *lemma* nnreal.measurable_sub

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.dominated_convergence_nn
- \+ *lemma* measure_theory.limsup_lintegral_le
- \+ *lemma* measure_theory.lintegral_infi_ae
- \+ *lemma* measure_theory.lintegral_liminf_le
- \+ *lemma* measure_theory.lintegral_sub
- \+ *lemma* measure_theory.lintegral_supr_ae

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.all_ae_of_all

Modified src/order/liminf_limsup.lean
- \+ *lemma* filter.liminf_eq_supr_infi_of_nat
- \+ *lemma* filter.liminf_le_limsup
- \+ *lemma* filter.limsup_eq_infi_supr_of_nat

Modified src/topology/algebra/ordered.lean
- \+ *theorem* liminf_eq_of_tendsto
- \+ *theorem* limsup_eq_of_tendsto
- \+ *theorem* tendsto_of_liminf_eq_limsup

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.continuous_sub'
- \+ *lemma* nnreal.continuous_sub



## [2019-06-14 13:35:52](https://github.com/leanprover-community/mathlib/commit/5a183f0)
provide some proof terms explicitly ([#1132](https://github.com/leanprover-community/mathlib/pull/1132))
#### Estimated changes
Modified src/algebra/pi_instances.lean


Modified src/data/complex/basic.lean


Modified src/linear_algebra/basic.lean




## [2019-06-12 04:45:45](https://github.com/leanprover-community/mathlib/commit/0c627fb)
chore(algebra/group/hom): drop unused section variables ([#1130](https://github.com/leanprover-community/mathlib/pull/1130))
#### Estimated changes
Modified src/algebra/group/hom.lean




## [2019-06-11 21:06:39](https://github.com/leanprover-community/mathlib/commit/3492206)
feat(data/mv_polynomial): misc lemmas on rename, map, and eval2 ([#1127](https://github.com/leanprover-community/mathlib/pull/1127))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.coeff_X
- \+ *lemma* mv_polynomial.eval₂_comp_right
- \+ *lemma* mv_polynomial.map_eval₂
- \+ *lemma* mv_polynomial.map_rename
- \+ *lemma* mv_polynomial.rename_add
- \+ *lemma* mv_polynomial.rename_mul
- \+ *lemma* mv_polynomial.rename_one
- \+ *lemma* mv_polynomial.rename_pow
- \+ *lemma* mv_polynomial.rename_sub
- \+ *lemma* mv_polynomial.rename_zero



## [2019-06-11 19:10:13](https://github.com/leanprover-community/mathlib/commit/953c612)
fix(category_theory): simplifying universes ([#1122](https://github.com/leanprover-community/mathlib/pull/1122))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.category.assoc_symm
- \+/\- *abbreviation* category_theory.large_category
- \+/\- *abbreviation* category_theory.small_category

Modified src/category_theory/comma.lean
- \+/\- *structure* category_theory.comma

Modified src/category_theory/concrete_category.lean
- \+/\- *structure* category_theory.bundled
- \+/\- *def* category_theory.forget
- \+/\- *def* category_theory.mk_ob

Modified src/category_theory/const.lean


Modified src/category_theory/core.lean
- \+/\- *def* category_theory.core

Modified src/category_theory/discrete_category.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean
- \+/\- *structure* category_theory.equivalence

Modified src/category_theory/full_subcategory.lean
- \+/\- *def* category_theory.induced_category

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean
- \+/\- *structure* category_theory.functor

Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean
- \+/\- *abbreviation* category_theory.large_groupoid
- \+/\- *abbreviation* category_theory.small_groupoid

Modified src/category_theory/isomorphism.lean
- \+/\- *structure* category_theory.iso

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.map_post
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+/\- *def* category_theory.limits.is_colimit.of_faithful
- \+/\- *def* category_theory.limits.is_limit.of_faithful
- \+/\- *lemma* category_theory.limits.limit.map_post
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* category_theory.limits.pair_function

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/monoidal/category.lean
- \+/\- *def* category_theory.tensor_iso

Modified src/category_theory/monoidal/category_aux.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.iso.app

Modified src/category_theory/natural_transformation.lean
- \+/\- *structure* category_theory.nat_trans

Modified src/category_theory/opposites.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/products/default.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/sparse.lean


Modified src/category_theory/types.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean




## [2019-06-11 17:46:50](https://github.com/leanprover-community/mathlib/commit/98ece77)
refactor(algebra/group): split into smaller files ([#1121](https://github.com/leanprover-community/mathlib/pull/1121))
* rename `src/algebra/group.lean` → `src/algebra/group/default.lean`
* Split algebra/group/default into smaller files
No code changes, except for variables declaration and imports
* Fix compile
* fix compile error: import `anti_hom` in `algebra/group/default`
* Drop unused imports
#### Estimated changes
Deleted src/algebra/group.lean
- \- *lemma* add_add_sub_cancel
- \- *lemma* add_sub_cancel'
- \- *lemma* add_sub_cancel'_right
- \- *lemma* add_sub_sub_cancel
- \- *def* additive
- \- *lemma* bit0_zero
- \- *lemma* bit1_zero
- \- *lemma* conj_inv
- \- *lemma* conj_mul
- \- *def* divp
- \- *theorem* divp_assoc
- \- *theorem* divp_eq_one
- \- *theorem* divp_mul_cancel
- \- *theorem* divp_one
- \- *theorem* divp_right_inj
- \- *theorem* divp_self
- \- *theorem* eq_iff_eq_of_sub_eq_sub
- \- *theorem* eq_inv_iff_eq_inv
- \- *theorem* eq_inv_iff_mul_eq_one
- \- *theorem* eq_inv_mul_iff_mul_eq
- \- *theorem* eq_mul_inv_iff_mul_eq
- \- *theorem* eq_of_inv_eq_inv
- \- *lemma* eq_sub_iff_add_eq'
- \- *theorem* eq_sub_iff_add_eq
- \- *lemma* free_add_monoid.add_def
- \- *lemma* free_add_monoid.zero_def
- \- *def* free_add_monoid
- \- *lemma* free_monoid.mul_def
- \- *lemma* free_monoid.one_def
- \- *def* free_monoid
- \- *lemma* inv.is_group_hom
- \- *theorem* inv_comm_of_comm
- \- *theorem* inv_eq_iff_inv_eq
- \- *theorem* inv_eq_iff_mul_eq_one
- \- *theorem* inv_eq_one
- \- *theorem* inv_inj'
- \- *theorem* inv_is_group_anti_hom
- \- *theorem* inv_mul_eq_iff_eq_mul
- \- *theorem* inv_ne_one
- \- *lemma* is_add_group_hom.map_sub
- \- *lemma* is_add_group_hom.sub
- \- *lemma* is_add_monoid_hom.map_add
- \- *def* is_conj
- \- *lemma* is_conj_iff_eq
- \- *lemma* is_conj_one_left
- \- *lemma* is_conj_one_right
- \- *lemma* is_conj_refl
- \- *lemma* is_conj_symm
- \- *lemma* is_conj_trans
- \- *theorem* is_group_anti_hom.map_inv
- \- *theorem* is_group_anti_hom.map_one
- \- *lemma* is_group_hom.injective_iff
- \- *lemma* is_group_hom.inv
- \- *theorem* is_group_hom.map_inv
- \- *theorem* is_group_hom.map_one
- \- *lemma* is_group_hom.mul
- \- *lemma* is_group_hom.to_is_monoid_hom
- \- *lemma* is_monoid_hom.map_mul
- \- *lemma* is_mul_hom.comp'
- \- *lemma* is_mul_hom.comp
- \- *lemma* is_mul_hom.id
- \- *theorem* left_inverse_add_left_sub
- \- *theorem* left_inverse_add_right_neg_add
- \- *theorem* left_inverse_inv
- \- *theorem* left_inverse_neg_add_add_right
- \- *theorem* left_inverse_sub_add_left
- \- *theorem* mul_divp_cancel
- \- *theorem* mul_eq_one_iff_eq_inv
- \- *theorem* mul_eq_one_iff_inv_eq
- \- *theorem* mul_inv_eq_iff_eq_mul
- \- *theorem* mul_inv_eq_one
- \- *theorem* mul_left_inj
- \- *theorem* mul_mul_mul_comm
- \- *theorem* mul_right_inj
- \- *theorem* mul_self_iff_eq_one
- \- *def* multiplicative
- \- *theorem* nat.units_eq_one
- \- *theorem* neg_add'
- \- *lemma* neg_sub_neg
- \- *theorem* one_divp
- \- *lemma* sub_add_add_cancel
- \- *lemma* sub_add_sub_cancel'
- \- *lemma* sub_add_sub_cancel
- \- *lemma* sub_eq_iff_eq_add'
- \- *theorem* sub_eq_iff_eq_add
- \- *lemma* sub_eq_neg_add
- \- *lemma* sub_eq_sub_iff_sub_eq_sub
- \- *theorem* sub_eq_zero
- \- *lemma* sub_left_inj
- \- *theorem* sub_ne_zero
- \- *lemma* sub_right_comm
- \- *lemma* sub_right_inj
- \- *def* sub_sub_cancel
- \- *lemma* sub_sub_sub_cancel_left
- \- *lemma* sub_sub_sub_cancel_right
- \- *lemma* units.coe_inv
- \- *lemma* units.coe_map
- \- *lemma* units.coe_mul
- \- *lemma* units.coe_one
- \- *theorem* units.ext
- \- *theorem* units.ext_iff
- \- *lemma* units.inv_mul
- \- *lemma* units.inv_mul_cancel_left
- \- *lemma* units.inv_mul_cancel_right
- \- *lemma* units.map_comp'
- \- *lemma* units.map_comp
- \- *lemma* units.map_id
- \- *def* units.mk_of_mul_eq_one
- \- *lemma* units.mul_inv
- \- *lemma* units.mul_inv_cancel_left
- \- *lemma* units.mul_inv_cancel_right
- \- *theorem* units.mul_left_inj
- \- *theorem* units.mul_right_inj
- \- *lemma* units.val_coe
- \- *structure* units
- \- *lemma* with_one.coe_inj
- \- *lemma* with_one.coe_ne_one
- \- *lemma* with_one.mul_coe
- \- *lemma* with_one.ne_one_iff_exists
- \- *lemma* with_one.one_ne_coe
- \- *def* with_one
- \- *lemma* with_zero.coe_one
- \- *lemma* with_zero.div_coe
- \- *lemma* with_zero.div_eq_div
- \- *lemma* with_zero.div_eq_iff_mul_eq
- \- *lemma* with_zero.div_mul_cancel
- \- *lemma* with_zero.div_one
- \- *lemma* with_zero.div_zero
- \- *lemma* with_zero.inv_coe
- \- *lemma* with_zero.inv_one
- \- *lemma* with_zero.inv_zero
- \- *lemma* with_zero.mul_coe
- \- *lemma* with_zero.mul_div_cancel
- \- *lemma* with_zero.mul_inv_rev
- \- *lemma* with_zero.mul_left_inv
- \- *lemma* with_zero.mul_right_inv
- \- *lemma* with_zero.one_div
- \- *lemma* with_zero.zero_div

Added src/algebra/group/anti_hom.lean
- \+ *theorem* inv_is_group_anti_hom
- \+ *theorem* is_group_anti_hom.map_inv
- \+ *theorem* is_group_anti_hom.map_one

Added src/algebra/group/basic.lean
- \+ *lemma* add_add_sub_cancel
- \+ *lemma* add_sub_cancel'
- \+ *lemma* add_sub_cancel'_right
- \+ *lemma* add_sub_sub_cancel
- \+ *lemma* bit0_zero
- \+ *lemma* bit1_zero
- \+ *theorem* eq_iff_eq_of_sub_eq_sub
- \+ *theorem* eq_inv_iff_eq_inv
- \+ *theorem* eq_inv_iff_mul_eq_one
- \+ *theorem* eq_inv_mul_iff_mul_eq
- \+ *theorem* eq_mul_inv_iff_mul_eq
- \+ *theorem* eq_of_inv_eq_inv
- \+ *lemma* eq_sub_iff_add_eq'
- \+ *theorem* eq_sub_iff_add_eq
- \+ *theorem* inv_comm_of_comm
- \+ *theorem* inv_eq_iff_inv_eq
- \+ *theorem* inv_eq_iff_mul_eq_one
- \+ *theorem* inv_eq_one
- \+ *theorem* inv_inj'
- \+ *theorem* inv_mul_eq_iff_eq_mul
- \+ *theorem* inv_ne_one
- \+ *theorem* left_inverse_add_left_sub
- \+ *theorem* left_inverse_add_right_neg_add
- \+ *theorem* left_inverse_inv
- \+ *theorem* left_inverse_neg_add_add_right
- \+ *theorem* left_inverse_sub_add_left
- \+ *theorem* mul_eq_one_iff_eq_inv
- \+ *theorem* mul_eq_one_iff_inv_eq
- \+ *theorem* mul_inv_eq_iff_eq_mul
- \+ *theorem* mul_inv_eq_one
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_mul_mul_comm
- \+ *theorem* mul_right_inj
- \+ *theorem* mul_self_iff_eq_one
- \+ *theorem* neg_add'
- \+ *lemma* neg_sub_neg
- \+ *lemma* sub_add_add_cancel
- \+ *lemma* sub_add_sub_cancel'
- \+ *lemma* sub_add_sub_cancel
- \+ *lemma* sub_eq_iff_eq_add'
- \+ *theorem* sub_eq_iff_eq_add
- \+ *lemma* sub_eq_neg_add
- \+ *lemma* sub_eq_sub_iff_sub_eq_sub
- \+ *theorem* sub_eq_zero
- \+ *lemma* sub_left_inj
- \+ *theorem* sub_ne_zero
- \+ *lemma* sub_right_comm
- \+ *lemma* sub_right_inj
- \+ *def* sub_sub_cancel
- \+ *lemma* sub_sub_sub_cancel_left
- \+ *lemma* sub_sub_sub_cancel_right

Added src/algebra/group/conj.lean
- \+ *lemma* conj_inv
- \+ *lemma* conj_mul
- \+ *def* is_conj
- \+ *lemma* is_conj_iff_eq
- \+ *lemma* is_conj_one_left
- \+ *lemma* is_conj_one_right
- \+ *lemma* is_conj_refl
- \+ *lemma* is_conj_symm
- \+ *lemma* is_conj_trans

Added src/algebra/group/default.lean


Added src/algebra/group/free_monoid.lean
- \+ *lemma* free_add_monoid.add_def
- \+ *lemma* free_add_monoid.zero_def
- \+ *def* free_add_monoid
- \+ *lemma* free_monoid.mul_def
- \+ *lemma* free_monoid.one_def
- \+ *def* free_monoid

Added src/algebra/group/hom.lean
- \+ *lemma* inv.is_group_hom
- \+ *lemma* is_add_group_hom.map_sub
- \+ *lemma* is_add_group_hom.sub
- \+ *lemma* is_add_monoid_hom.map_add
- \+ *lemma* is_group_hom.injective_iff
- \+ *lemma* is_group_hom.inv
- \+ *theorem* is_group_hom.map_inv
- \+ *theorem* is_group_hom.map_one
- \+ *lemma* is_group_hom.mul
- \+ *lemma* is_group_hom.to_is_monoid_hom
- \+ *lemma* is_monoid_hom.map_mul
- \+ *lemma* is_mul_hom.comp'
- \+ *lemma* is_mul_hom.comp
- \+ *lemma* is_mul_hom.id

Added src/algebra/group/to_additive.lean


Added src/algebra/group/type_tags.lean
- \+ *def* additive
- \+ *def* multiplicative

Added src/algebra/group/units.lean
- \+ *def* divp
- \+ *theorem* divp_assoc
- \+ *theorem* divp_eq_one
- \+ *theorem* divp_mul_cancel
- \+ *theorem* divp_one
- \+ *theorem* divp_right_inj
- \+ *theorem* divp_self
- \+ *theorem* mul_divp_cancel
- \+ *theorem* nat.units_eq_one
- \+ *theorem* one_divp
- \+ *lemma* units.coe_inv
- \+ *lemma* units.coe_mul
- \+ *lemma* units.coe_one
- \+ *theorem* units.ext
- \+ *theorem* units.ext_iff
- \+ *lemma* units.inv_mul
- \+ *lemma* units.inv_mul_cancel_left
- \+ *lemma* units.inv_mul_cancel_right
- \+ *def* units.mk_of_mul_eq_one
- \+ *lemma* units.mul_inv
- \+ *lemma* units.mul_inv_cancel_left
- \+ *lemma* units.mul_inv_cancel_right
- \+ *theorem* units.mul_left_inj
- \+ *theorem* units.mul_right_inj
- \+ *lemma* units.val_coe
- \+ *structure* units

Added src/algebra/group/units_hom.lean
- \+ *lemma* units.coe_map
- \+ *lemma* units.map_comp'
- \+ *lemma* units.map_comp
- \+ *lemma* units.map_id

Added src/algebra/group/with_one.lean
- \+ *lemma* with_one.coe_inj
- \+ *lemma* with_one.coe_ne_one
- \+ *lemma* with_one.mul_coe
- \+ *lemma* with_one.ne_one_iff_exists
- \+ *lemma* with_one.one_ne_coe
- \+ *def* with_one
- \+ *lemma* with_zero.coe_one
- \+ *lemma* with_zero.div_coe
- \+ *lemma* with_zero.div_eq_div
- \+ *lemma* with_zero.div_eq_iff_mul_eq
- \+ *lemma* with_zero.div_mul_cancel
- \+ *lemma* with_zero.div_one
- \+ *lemma* with_zero.div_zero
- \+ *lemma* with_zero.inv_coe
- \+ *lemma* with_zero.inv_one
- \+ *lemma* with_zero.inv_zero
- \+ *lemma* with_zero.mul_coe
- \+ *lemma* with_zero.mul_div_cancel
- \+ *lemma* with_zero.mul_inv_rev
- \+ *lemma* with_zero.mul_left_inv
- \+ *lemma* with_zero.mul_right_inv
- \+ *lemma* with_zero.one_div
- \+ *lemma* with_zero.zero_div



## [2019-06-11 12:53:04-04:00](https://github.com/leanprover-community/mathlib/commit/8d0e719)
chore(mergify): don't dismiss reviews [ci-skip] ([#1124](https://github.com/leanprover-community/mathlib/pull/1124))
#### Estimated changes
Modified .mergify.yml




## [2019-06-11 04:39:39](https://github.com/leanprover-community/mathlib/commit/abfaf8d)
refactor(group_theory/abelianization): simplify abelianization  ([#1126](https://github.com/leanprover-community/mathlib/pull/1126))
* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* trying to merge
* feat(group_theory\presented_group):  define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.
* feat(group_theory\presented_group): define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate
* Update src/group_theory/presented_group.lean
Co-Authored-By: Keeley Hoek <keeley@hoek.io>
* Uniqueness of extension
* Tidied up to_group.unique
* Removed unnecessary line
* Changed naming
* refactor(group_theory/abelianization): simplify abelianization
The commutator of a group was previously defined using lists.
Now it is defined using `normal_closure`.
This change simplifies some of the proofs
#### Estimated changes
Modified src/group_theory/abelianization.lean
- \+ *lemma* abelianization.commutator_subset_ker
- \+/\- *lemma* abelianization.lift.of



## [2019-06-10 13:38:37](https://github.com/leanprover-community/mathlib/commit/bd2f35f)
feat(group_theory/presented_group): define presented groups ([#1118](https://github.com/leanprover-community/mathlib/pull/1118))
* feat(group_theory/conjugates) : define conjugates
define group conjugates and normal closure
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* trying to merge
* feat(group_theory\presented_group):  define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate.
* feat(group_theory\presented_group): define presented groups
Presented groups are defined as a quotient of a free group by the normal subgroup  the relations generate
* Update src/group_theory/presented_group.lean
Co-Authored-By: Keeley Hoek <keeley@hoek.io>
* Uniqueness of extension
* Tidied up to_group.unique
* Removed unnecessary line
* Changed naming
#### Estimated changes
Added src/group_theory/presented_group.lean
- \+ *lemma* presented_group.closure_rels_subset_ker
- \+ *def* presented_group.of
- \+ *lemma* presented_group.to_group.inv
- \+ *lemma* presented_group.to_group.mul
- \+ *lemma* presented_group.to_group.of
- \+ *lemma* presented_group.to_group.one
- \+ *theorem* presented_group.to_group.unique
- \+ *def* presented_group.to_group
- \+ *lemma* presented_group.to_group_eq_one_of_mem_closure
- \+ *def* presented_group



## [2019-06-10 08:38:52+01:00](https://github.com/leanprover-community/mathlib/commit/004e0b3)
feat (data/pnat): extensions to pnat  ([#1073](https://github.com/leanprover-community/mathlib/pull/1073))
* Extended API, especially divisibility and primes
* Positive euclidean algorithm
* Disambiguate overloaded ::
* Tweak broken proof of flip_is_special
* Change to mathlib style
* Update src/data/pnat.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/pnat.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Adjust style for mathlib
* Moved and renamed
* Move some material from basic.lean to prime.lean
* Move some material from basic.lean to factors.lean
* Update import to data.pnat.basic.
* Update import to data.pnat.basic
* Fix import of data.pnat.basic
* Use monoid.pow instead of nat.pow
* Fix pnat.pow_succ -> pow_succ; stylistic changes
* More systematic use of coercion
* More consistent use of coercion
* Formatting; change flip' to prod.swap
#### Estimated changes
Modified src/data/hash_map.lean


Modified src/data/nat/prime.lean
- \+ *theorem* nat.primes.coe_nat_inj
- \+ *def* nat.primes

Deleted src/data/pnat.lean
- \- *def* nat.succ_pnat
- \- *theorem* nat.succ_pnat_coe
- \- *def* nat.to_pnat'
- \- *def* nat.to_pnat
- \- *theorem* pnat.add_coe
- \- *theorem* pnat.coe_to_pnat'
- \- *theorem* pnat.eq
- \- *theorem* pnat.mk_coe
- \- *theorem* pnat.mul_coe
- \- *theorem* pnat.ne_zero
- \- *theorem* pnat.one_coe
- \- *theorem* pnat.pos
- \- *def* pnat.pow
- \- *theorem* pnat.pow_coe
- \- *theorem* pnat.to_pnat'_coe
- \- *def* pnat

Added src/data/pnat/basic.lean
- \+ *theorem* nat.primes.coe_pnat_inj
- \+ *theorem* nat.primes.coe_pnat_nat
- \+ *def* nat.succ_pnat
- \+ *theorem* nat.succ_pnat_coe
- \+ *theorem* nat.succ_pnat_inj
- \+ *def* nat.to_pnat'
- \+ *theorem* nat.to_pnat'_coe
- \+ *def* nat.to_pnat
- \+ *theorem* pnat.add_coe
- \+ *theorem* pnat.add_sub_of_lt
- \+ *theorem* pnat.coe_to_pnat'
- \+ *def* pnat.div
- \+ *theorem* pnat.div_coe
- \+ *def* pnat.div_exact
- \+ *theorem* pnat.dvd_antisymm
- \+ *theorem* pnat.dvd_gcd
- \+ *theorem* pnat.dvd_iff''
- \+ *theorem* pnat.dvd_iff'
- \+ *theorem* pnat.dvd_iff
- \+ *theorem* pnat.dvd_intro
- \+ *theorem* pnat.dvd_lcm_left
- \+ *theorem* pnat.dvd_lcm_right
- \+ *theorem* pnat.dvd_one_iff
- \+ *theorem* pnat.dvd_refl
- \+ *theorem* pnat.dvd_trans
- \+ *theorem* pnat.eq
- \+ *def* pnat.gcd
- \+ *theorem* pnat.gcd_coe
- \+ *theorem* pnat.gcd_dvd_left
- \+ *theorem* pnat.gcd_dvd_right
- \+ *theorem* pnat.gcd_mul_lcm
- \+ *def* pnat.lcm
- \+ *theorem* pnat.lcm_coe
- \+ *theorem* pnat.lcm_dvd
- \+ *theorem* pnat.mk_coe
- \+ *def* pnat.mod
- \+ *theorem* pnat.mod_add_div
- \+ *theorem* pnat.mod_coe
- \+ *def* pnat.mod_div
- \+ *def* pnat.mod_div_aux
- \+ *lemma* pnat.mod_div_aux_spec
- \+ *theorem* pnat.mod_le
- \+ *theorem* pnat.mul_coe
- \+ *theorem* pnat.mul_div_exact
- \+ *theorem* pnat.ne_zero
- \+ *theorem* pnat.one_coe
- \+ *theorem* pnat.one_dvd
- \+ *theorem* pnat.pos
- \+ *theorem* pnat.pow_coe
- \+ *def* pnat.prime
- \+ *theorem* pnat.sub_coe
- \+ *theorem* pnat.to_pnat'_coe
- \+ *def* pnat

Added src/data/pnat/factors.lean
- \+ *theorem* pnat.coe_nat_factor_multiset
- \+ *theorem* pnat.count_factor_multiset
- \+ *def* pnat.factor_multiset
- \+ *def* pnat.factor_multiset_equiv
- \+ *theorem* pnat.factor_multiset_gcd
- \+ *theorem* pnat.factor_multiset_lcm
- \+ *theorem* pnat.factor_multiset_le_iff'
- \+ *theorem* pnat.factor_multiset_le_iff
- \+ *theorem* pnat.factor_multiset_mul
- \+ *theorem* pnat.factor_multiset_of_prime
- \+ *theorem* pnat.factor_multiset_one
- \+ *theorem* pnat.factor_multiset_pow
- \+ *theorem* pnat.prod_factor_multiset
- \+ *theorem* prime_multiset.add_sub_of_le
- \+ *theorem* prime_multiset.card_of_prime
- \+ *theorem* prime_multiset.coe_nat_inj
- \+ *theorem* prime_multiset.coe_nat_of_prime
- \+ *theorem* prime_multiset.coe_nat_prime
- \+ *theorem* prime_multiset.coe_pnat_inj
- \+ *theorem* prime_multiset.coe_pnat_nat
- \+ *theorem* prime_multiset.coe_pnat_of_prime
- \+ *theorem* prime_multiset.coe_pnat_prime
- \+ *theorem* prime_multiset.coe_prod
- \+ *theorem* prime_multiset.factor_multiset_prod
- \+ *def* prime_multiset.of_nat_list
- \+ *def* prime_multiset.of_nat_multiset
- \+ *def* prime_multiset.of_pnat_list
- \+ *def* prime_multiset.of_pnat_multiset
- \+ *def* prime_multiset.of_prime
- \+ *def* prime_multiset.prod
- \+ *theorem* prime_multiset.prod_add
- \+ *theorem* prime_multiset.prod_dvd_iff'
- \+ *theorem* prime_multiset.prod_dvd_iff
- \+ *theorem* prime_multiset.prod_inf
- \+ *theorem* prime_multiset.prod_of_nat_list
- \+ *theorem* prime_multiset.prod_of_nat_multiset
- \+ *theorem* prime_multiset.prod_of_pnat_list
- \+ *theorem* prime_multiset.prod_of_pnat_multiset
- \+ *theorem* prime_multiset.prod_of_prime
- \+ *theorem* prime_multiset.prod_smul
- \+ *theorem* prime_multiset.prod_sup
- \+ *theorem* prime_multiset.prod_zero
- \+ *def* prime_multiset.to_nat_multiset
- \+ *theorem* prime_multiset.to_of_nat_multiset
- \+ *theorem* prime_multiset.to_of_pnat_multiset
- \+ *def* prime_multiset.to_pnat_multiset
- \+ *def* prime_multiset

Added src/data/pnat/xgcd.lean
- \+ *def* pnat.gcd_a'
- \+ *theorem* pnat.gcd_a'_coe
- \+ *theorem* pnat.gcd_a_eq
- \+ *def* pnat.gcd_b'
- \+ *theorem* pnat.gcd_b'_coe
- \+ *theorem* pnat.gcd_b_eq
- \+ *def* pnat.gcd_d
- \+ *theorem* pnat.gcd_det_eq
- \+ *theorem* pnat.gcd_eq
- \+ *theorem* pnat.gcd_props
- \+ *theorem* pnat.gcd_rel_left'
- \+ *theorem* pnat.gcd_rel_left
- \+ *theorem* pnat.gcd_rel_right'
- \+ *theorem* pnat.gcd_rel_right
- \+ *def* pnat.gcd_w
- \+ *def* pnat.gcd_x
- \+ *def* pnat.gcd_y
- \+ *def* pnat.gcd_z
- \+ *def* pnat.xgcd:
- \+ *def* pnat.xgcd_type.a
- \+ *def* pnat.xgcd_type.b
- \+ *def* pnat.xgcd_type.finish
- \+ *theorem* pnat.xgcd_type.finish_is_reduced
- \+ *theorem* pnat.xgcd_type.finish_is_special
- \+ *theorem* pnat.xgcd_type.finish_v
- \+ *def* pnat.xgcd_type.flip
- \+ *theorem* pnat.xgcd_type.flip_a
- \+ *theorem* pnat.xgcd_type.flip_b
- \+ *theorem* pnat.xgcd_type.flip_is_reduced
- \+ *theorem* pnat.xgcd_type.flip_is_special
- \+ *theorem* pnat.xgcd_type.flip_v
- \+ *theorem* pnat.xgcd_type.flip_w
- \+ *theorem* pnat.xgcd_type.flip_x
- \+ *theorem* pnat.xgcd_type.flip_y
- \+ *theorem* pnat.xgcd_type.flip_z
- \+ *def* pnat.xgcd_type.is_reduced'
- \+ *def* pnat.xgcd_type.is_reduced
- \+ *theorem* pnat.xgcd_type.is_reduced_iff
- \+ *def* pnat.xgcd_type.is_special'
- \+ *def* pnat.xgcd_type.is_special
- \+ *theorem* pnat.xgcd_type.is_special_iff
- \+ *def* pnat.xgcd_type.mk'
- \+ *def* pnat.xgcd_type.q
- \+ *def* pnat.xgcd_type.qp
- \+ *theorem* pnat.xgcd_type.qp_eq
- \+ *def* pnat.xgcd_type.r
- \+ *def* pnat.xgcd_type.reduce
- \+ *theorem* pnat.xgcd_type.reduce_a
- \+ *theorem* pnat.xgcd_type.reduce_b
- \+ *theorem* pnat.xgcd_type.reduce_reduced'
- \+ *theorem* pnat.xgcd_type.reduce_reduced
- \+ *theorem* pnat.xgcd_type.reduce_special'
- \+ *theorem* pnat.xgcd_type.reduce_special
- \+ *theorem* pnat.xgcd_type.reduce_v
- \+ *theorem* pnat.xgcd_type.rq_eq
- \+ *def* pnat.xgcd_type.start
- \+ *theorem* pnat.xgcd_type.start_is_special
- \+ *theorem* pnat.xgcd_type.start_v
- \+ *def* pnat.xgcd_type.step
- \+ *theorem* pnat.xgcd_type.step_is_special
- \+ *theorem* pnat.xgcd_type.step_v
- \+ *theorem* pnat.xgcd_type.step_wf
- \+ *def* pnat.xgcd_type.succ₂
- \+ *def* pnat.xgcd_type.v
- \+ *theorem* pnat.xgcd_type.v_eq_succ_vp
- \+ *def* pnat.xgcd_type.vp
- \+ *def* pnat.xgcd_type.w
- \+ *def* pnat.xgcd_type.z
- \+ *structure* pnat.xgcd_type

Modified src/data/rat.lean


Modified src/data/zmod/basic.lean


Modified src/set_theory/ordinal_notation.lean




## [2019-06-08 23:11:29](https://github.com/leanprover-community/mathlib/commit/3f9916e)
feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite ([#999](https://github.com/leanprover-community/mathlib/pull/999))
* feat(tactic/rewrite_all): tactic to perform the nth occurrence of a rewrite
* formatting
* formatting
* perhaps a little bit easier to read?
* try renaming
* there was a duplicate definition, just not the one lean complained about
* Namespaces
* I think kabstract works now
* Fix
* Test
* Fix guard
* updating test to reflect difference between congr and kabstract
* oops
* adding Keeley's example
* remove kabstract implementation for now
* cleanup test file
* rename common to basic
* Update src/tactic/rewrite_all/default.lean
#### Estimated changes
Modified src/data/mllist.lean


Added src/tactic/rewrite_all/basic.lean
- \+ *def* side.other
- \+ *def* side.to_string
- \+ *inductive* side

Added src/tactic/rewrite_all/congr.lean


Added src/tactic/rewrite_all/default.lean


Added test/rewrite_all.lean
- \+ *structure* F
- \+ *structure* cat



## [2019-06-07 16:54:39](https://github.com/leanprover-community/mathlib/commit/b55e44d)
refactor(analysis/normed_space/basic): change normed_space definition ([#1112](https://github.com/leanprover-community/mathlib/pull/1112))
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/convex.lean
- \+/\- *lemma* convex_ball
- \+/\- *lemma* convex_closed_ball
- \+/\- *lemma* convex_on_dist

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *structure* normed_group.core
- \+ *theorem* normed_group.tendsto_nhds_zero
- \- *structure* normed_space.core
- \- *theorem* normed_space.tendsto_nhds_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *structure* is_bounded_linear_map

Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_norm_neg



## [2019-06-07 15:21:25](https://github.com/leanprover-community/mathlib/commit/85ed958)
feat(data/quot): quot.map: act on non-id maps ([#1120](https://github.com/leanprover-community/mathlib/pull/1120))
* old version renamed to `quot.map_right`
* similar changes to `quot.congr` and `quotient.congr`
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/quot.lean


Modified src/topology/algebra/uniform_ring.lean




## [2019-06-06 16:45:38](https://github.com/leanprover-community/mathlib/commit/f36fdfb)
refactor(category_theory/equivalence): simplify equivalence.trans ([#1114](https://github.com/leanprover-community/mathlib/pull/1114))
#### Estimated changes
Modified src/category_theory/equivalence.lean




## [2019-06-05 07:54:30](https://github.com/leanprover-community/mathlib/commit/a7524b6)
refactor(analysis/normed_space/operator_norm): topological modules ([#1085](https://github.com/leanprover-community/mathlib/pull/1085))
* refactor(analysis/normed_space/operator_norm): topological modules
* remove useless typeclass in definition of topological module
* refactor(analysis/normed_space/operator_norm): style
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \- *lemma* continuous_smul

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* bounded_linear_map.is_bounded_linear_map
- \- *lemma* bounded_linear_map.is_bounded_linear_map_comp_left
- \- *lemma* bounded_linear_map.is_bounded_linear_map_comp_right
- \+ *lemma* continuous_linear_map.is_bounded_linear_map
- \+ *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+ *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+ *def* is_bounded_bilinear_map.linear_deriv
- \+ *lemma* is_bounded_bilinear_map_deriv_coe
- \- *def* is_bounded_linear_map.to_bounded_linear_map
- \+ *def* is_bounded_linear_map.to_continuous_linear_map
- \- *theorem* is_linear_map.bounded_of_continuous_at

Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* bounded_linear_map.add_apply
- \- *lemma* bounded_linear_map.bounds_bdd_below
- \- *lemma* bounded_linear_map.bounds_nonempty
- \- *lemma* bounded_linear_map.coe_add'
- \- *lemma* bounded_linear_map.coe_add
- \- *lemma* bounded_linear_map.coe_apply'
- \- *lemma* bounded_linear_map.coe_apply
- \- *lemma* bounded_linear_map.coe_coe
- \- *lemma* bounded_linear_map.coe_comp'
- \- *lemma* bounded_linear_map.coe_comp
- \- *lemma* bounded_linear_map.coe_id'
- \- *lemma* bounded_linear_map.coe_id
- \- *lemma* bounded_linear_map.coe_neg'
- \- *lemma* bounded_linear_map.coe_neg
- \- *lemma* bounded_linear_map.coe_sub'
- \- *lemma* bounded_linear_map.coe_sub
- \- *lemma* bounded_linear_map.coe_zero'
- \- *lemma* bounded_linear_map.coe_zero
- \- *def* bounded_linear_map.comp
- \- *theorem* bounded_linear_map.continuous
- \- *theorem* bounded_linear_map.ext
- \- *theorem* bounded_linear_map.ext_iff
- \- *def* bounded_linear_map.id
- \- *lemma* bounded_linear_map.id_apply
- \- *theorem* bounded_linear_map.is_O_comp
- \- *theorem* bounded_linear_map.is_O_id
- \- *theorem* bounded_linear_map.is_O_sub
- \- *theorem* bounded_linear_map.le_op_norm
- \- *theorem* bounded_linear_map.lipschitz
- \- *lemma* bounded_linear_map.map_add
- \- *lemma* bounded_linear_map.map_neg
- \- *lemma* bounded_linear_map.map_smul
- \- *lemma* bounded_linear_map.map_sub
- \- *lemma* bounded_linear_map.map_zero
- \- *lemma* bounded_linear_map.neg_apply
- \- *def* bounded_linear_map.op_norm
- \- *lemma* bounded_linear_map.op_norm_comp_le
- \- *lemma* bounded_linear_map.op_norm_le_bound
- \- *lemma* bounded_linear_map.op_norm_nonneg
- \- *lemma* bounded_linear_map.op_norm_smul
- \- *theorem* bounded_linear_map.op_norm_triangle
- \- *theorem* bounded_linear_map.op_norm_zero_iff
- \- *def* bounded_linear_map.prod
- \- *lemma* bounded_linear_map.ratio_le_op_norm
- \- *def* bounded_linear_map.scalar_prod_space_iso
- \- *lemma* bounded_linear_map.smul_apply
- \- *lemma* bounded_linear_map.sub_apply
- \- *lemma* bounded_linear_map.unit_le_op_norm
- \- *def* bounded_linear_map.zero
- \- *lemma* bounded_linear_map.zero_apply
- \- *structure* bounded_linear_map
- \+ *theorem* continuous_linear_map.bound
- \+ *lemma* continuous_linear_map.bounds_bdd_below
- \+ *lemma* continuous_linear_map.bounds_nonempty
- \+ *theorem* continuous_linear_map.is_O_comp
- \+ *theorem* continuous_linear_map.is_O_id
- \+ *theorem* continuous_linear_map.is_O_sub
- \+ *theorem* continuous_linear_map.le_op_norm
- \+ *theorem* continuous_linear_map.lipschitz
- \+ *lemma* continuous_linear_map.norm_id
- \+ *lemma* continuous_linear_map.norm_zero
- \+ *def* continuous_linear_map.op_norm
- \+ *lemma* continuous_linear_map.op_norm_comp_le
- \+ *lemma* continuous_linear_map.op_norm_le_bound
- \+ *lemma* continuous_linear_map.op_norm_nonneg
- \+ *lemma* continuous_linear_map.op_norm_smul
- \+ *theorem* continuous_linear_map.op_norm_triangle
- \+ *theorem* continuous_linear_map.op_norm_zero_iff
- \+ *lemma* continuous_linear_map.ratio_le_op_norm
- \+ *lemma* continuous_linear_map.scalar_prod_space_iso_norm
- \+ *lemma* continuous_linear_map.unit_le_op_norm
- \+ *lemma* linear_map.continuous_of_bound
- \+ *def* linear_map.with_bound
- \+ *lemma* linear_map_with_bound_apply
- \+ *lemma* linear_map_with_bound_coe

Added src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.add_apply
- \+ *lemma* continuous_linear_map.coe_add'
- \+ *lemma* continuous_linear_map.coe_add
- \+ *lemma* continuous_linear_map.coe_apply'
- \+ *lemma* continuous_linear_map.coe_apply
- \+ *lemma* continuous_linear_map.coe_coe
- \+ *lemma* continuous_linear_map.coe_comp'
- \+ *lemma* continuous_linear_map.coe_comp
- \+ *lemma* continuous_linear_map.coe_id'
- \+ *lemma* continuous_linear_map.coe_id
- \+ *lemma* continuous_linear_map.coe_neg'
- \+ *lemma* continuous_linear_map.coe_neg
- \+ *lemma* continuous_linear_map.coe_sub'
- \+ *lemma* continuous_linear_map.coe_sub
- \+ *lemma* continuous_linear_map.coe_zero'
- \+ *lemma* continuous_linear_map.coe_zero
- \+ *def* continuous_linear_map.comp
- \+ *theorem* continuous_linear_map.ext
- \+ *theorem* continuous_linear_map.ext_iff
- \+ *def* continuous_linear_map.id
- \+ *lemma* continuous_linear_map.id_apply
- \+ *lemma* continuous_linear_map.map_add
- \+ *lemma* continuous_linear_map.map_neg
- \+ *lemma* continuous_linear_map.map_smul
- \+ *lemma* continuous_linear_map.map_sub
- \+ *lemma* continuous_linear_map.map_zero
- \+ *lemma* continuous_linear_map.neg_apply
- \+ *def* continuous_linear_map.prod
- \+ *def* continuous_linear_map.scalar_prod_space_iso
- \+ *lemma* continuous_linear_map.smul_apply
- \+ *lemma* continuous_linear_map.sub_apply
- \+ *def* continuous_linear_map.zero
- \+ *lemma* continuous_linear_map.zero_apply
- \+ *structure* continuous_linear_map
- \+ *lemma* continuous_smul'
- \+ *lemma* continuous_smul



## [2019-06-04 20:49:06](https://github.com/leanprover-community/mathlib/commit/a152f3a)
chore(doc/install/macos): improve mac install instructions ([#1106](https://github.com/leanprover-community/mathlib/pull/1106))
* tweaking install instructions
* minor
* minor
* minor
* minor
* small icon
* improve instructions for installing the extension on all OSes
* minor
#### Estimated changes
Modified docs/install/debian_details.md


Added docs/install/extensions-icon.png


Modified docs/install/linux.md


Modified docs/install/macos.md


Modified docs/install/project.md


Modified docs/install/windows.md




## [2019-06-04 14:48:57+01:00](https://github.com/leanprover-community/mathlib/commit/542d25d)
fix(data/logic/basic): Use a Sort for classical.some_spec2 ([#1111](https://github.com/leanprover-community/mathlib/pull/1111))
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* classical.some_spec2



## [2019-06-03 22:11:39](https://github.com/leanprover-community/mathlib/commit/dd832f0)
feat(topology/basic): is_open_Inter and others ([#1108](https://github.com/leanprover-community/mathlib/pull/1108))
#### Estimated changes
Modified src/topology/basic.lean
- \+/\- *lemma* is_closed_Union
- \+ *lemma* is_closed_Union_prop
- \+ *lemma* is_closed_bUnion
- \+ *lemma* is_open_Inter
- \+ *lemma* is_open_Inter_prop

Modified src/topology/uniform_space/cauchy.lean




## [2019-06-03 20:36:09](https://github.com/leanprover-community/mathlib/commit/504c0ad)
feat(data/set/basic): union_inter_distrib lemmas ([#1107](https://github.com/leanprover-community/mathlib/pull/1107))
* feat(data/set/basic): union_inter_distrib lemmas
* add parentheses
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.inter_union_distrib_left
- \+ *theorem* set.inter_union_distrib_right
- \+ *theorem* set.union_inter_distrib_left
- \+ *theorem* set.union_inter_distrib_right



## [2019-06-03 18:05:35](https://github.com/leanprover-community/mathlib/commit/4263b2b)
fix(data/nat/gcd): correct order of arguments in nat.coprime_mul_iff_right ([#1105](https://github.com/leanprover-community/mathlib/pull/1105))
* Not sure how this works
* Fix order for coprime_mul_iff_right
* Remove spurious file
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+/\- *lemma* nat.coprime_mul_iff_right



## [2019-06-01 20:38:34](https://github.com/leanprover-community/mathlib/commit/38b8054)
feat(data/mv_polynomial): add coeff for mv_polynomial ([#1101](https://github.com/leanprover-community/mathlib/pull/1101))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.nat_sub_apply

Modified src/data/mv_polynomial.lean
- \+ *def* mv_polynomial.coeff
- \+ *lemma* mv_polynomial.coeff_C
- \+ *lemma* mv_polynomial.coeff_C_mul
- \+ *lemma* mv_polynomial.coeff_add
- \+ *lemma* mv_polynomial.coeff_map
- \+ *lemma* mv_polynomial.coeff_monomial
- \+ *lemma* mv_polynomial.coeff_mul_X'
- \+ *lemma* mv_polynomial.coeff_mul_X
- \+ *lemma* mv_polynomial.coeff_sub
- \+ *lemma* mv_polynomial.coeff_sum
- \+ *lemma* mv_polynomial.coeff_zero
- \+ *lemma* mv_polynomial.coeff_zero_X
- \+ *lemma* mv_polynomial.ext
- \+ *lemma* mv_polynomial.monic_monomial_eq
- \+ *def* mv_polynomial.tmp.coe

