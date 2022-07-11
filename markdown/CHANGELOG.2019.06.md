## [2019-06-29 16:56:28](https://github.com/leanprover-community/mathlib/commit/469da29)
feat(data/list/basic): map_nil and map_eq_nil ([#1161](https://github.com/leanprover-community/mathlib/pull/1161))
* feat(data/list/basic): map_nil and map_eq_nil
* Update basic.lean
* make Simon's changes
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* map_eq_nil



## [2019-06-29 13:28:56](https://github.com/leanprover-community/mathlib/commit/0858157)
refactor(category_theory/category): reorder arguments of `End.has_mul` ([#1128](https://github.com/leanprover-community/mathlib/pull/1128))
* Reorder arguments of `End.has_mul` and `Aut.has_mul`, adjust `category/fold`
* clean up proofs in `category.fold`
#### Estimated changes
Modified src/category/fold.lean
- \+ *lemma* foldl.unop_of_free_monoid
- \+ *lemma* mfoldl.unop_of_free_monoid
- \- *lemma* foldr.unop_of_free_monoid
- \- *lemma* mfoldr.unop_of_free_monoid
- \+/\- *def* foldl
- \+/\- *def* foldl.mk
- \+ *def* foldl.get
- \+/\- *def* foldr
- \+/\- *def* foldr.mk
- \+/\- *def* foldr.get
- \+/\- *def* mfoldl
- \+/\- *def* mfoldl.mk
- \+ *def* mfoldl.get
- \+/\- *def* mfoldr.mk
- \+/\- *def* mfoldr.get

Modified src/category_theory/category.lean
- \+/\- *lemma* End.mul_def

Modified src/category_theory/isomorphism.lean


Modified src/data/opposite.lean
- \+ *lemma* op_inj_iff
- \+ *lemma* unop_inj_iff



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
- \+ *lemma* exists_max_ideal_of_mem_nonunits
- \+ *lemma* is_unit_or_is_unit_one_sub_self
- \+ *lemma* is_unit_of_mem_nonunits_one_sub_self
- \+ *lemma* is_unit_one_sub_self_of_mem_nonunits
- \+ *lemma* nonunits_add
- \+ *lemma* max_ideal_unique
- \+ *lemma* mem_nonunits_ideal
- \+ *lemma* is_unit_of_map_unit
- \+ *lemma* map_nonunit
- \+/\- *theorem* mem_span_pair
- \+/\- *theorem* is_coprime_def
- \+/\- *theorem* is_coprime_self
- \+/\- *theorem* mem_nonunits_iff
- \+/\- *theorem* mul_mem_nonunits_right
- \+/\- *theorem* mul_mem_nonunits_left
- \+/\- *theorem* zero_mem_nonunits
- \+/\- *theorem* one_not_mem_nonunits
- \+/\- *theorem* coe_subset_nonunits
- \- *theorem* mem_nonunits_ideal
- \- *theorem* local_of_nonunits_ideal
- \+/\- *def* nonunits
- \+/\- *def* nonunits_ideal
- \+/\- *def* is_local_ring
- \+ *def* local_of_is_local_ring
- \+ *def* local_of_unit_or_unit_one_sub
- \+ *def* local_of_nonunits_ideal
- \+ *def* local_of_unique_max_ideal
- \+ *def* residue_field
- \- *def* is_local_ring.zero_ne_one

Modified src/ring_theory/localization.lean




## [2019-06-28 15:11:00](https://github.com/leanprover-community/mathlib/commit/4a5a1a5)
fix(data/list/min_max): correct names of mem_maximum and mem_minimum ([#1162](https://github.com/leanprover-community/mathlib/pull/1162))
* fix(data/list/min_max): correct names of mem_maximum and mem_minimum
* Update denumerable.lean
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/list/min_max.lean
- \+ *theorem* maximum_mem
- \+ *theorem* minimum_mem
- \- *theorem* mem_maximum
- \- *theorem* mem_minimum



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
- \+ *theorem* length_sort

Modified src/data/list/sort.lean
- \+ *lemma* length_merge_sort

Modified src/data/multiset.lean
- \+ *theorem* length_sort



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
- \+ *def* split_on



## [2019-06-20 08:30:31](https://github.com/leanprover-community/mathlib/commit/a35d682)
feat(topology/order): more facts on continuous_on ([#1140](https://github.com/leanprover-community/mathlib/pull/1140))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_on.inv
- \+ *lemma* continuous_on.sub

Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_on.mul

Modified src/topology/basic.lean
- \+ *theorem* self_mem_nhds_within
- \+ *theorem* nhds_within_restrict''
- \+/\- *theorem* nhds_within_restrict'
- \+ *theorem* nhds_within_le_of_mem

Modified src/topology/order.lean
- \+ *lemma* continuous_within_at_inter'
- \+ *lemma* continuous_within_at_inter
- \+ *lemma* continuous_within_at.continuous_at
- \+ *lemma* continuous.comp_continuous_on
- \+ *lemma* continuous.continuous_at
- \+ *lemma* continuous_at.preimage_mem_nhds
- \+ *lemma* continuous_within_at.preimage_mem_nhds_within
- \+ *lemma* continuous_within_at.congr_of_mem_nhds_within
- \+ *lemma* continuous_on_open_iff
- \+ *lemma* continuous_on.preimage_closed_of_closed
- \+ *lemma* continuous_on_open_of_generate_from
- \+ *theorem* continuous_on_iff_is_closed



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
- \+/\- *lemma* measurable_add
- \+/\- *lemma* measurable_sub
- \+/\- *lemma* measurable_mul

Modified src/order/complete_lattice.lean
- \+ *theorem* infi_pair
- \+ *theorem* supr_pair

Modified src/topology/Top/adjunctions.lean


Modified src/topology/Top/basic.lean
- \+/\- *def* trivial

Modified src/topology/Top/limits.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/constructions.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* continuous_sub'
- \+/\- *lemma* continuous_sub

Modified src/topology/maps.lean


Modified src/topology/order.lean
- \+ *lemma* le_generate_from_iff_subset_is_open
- \+/\- *lemma* nhds_bot
- \+/\- *lemma* le_of_nhds_le_nhds
- \+/\- *lemma* eq_of_nhds_eq_nhds
- \+ *lemma* eq_bot_of_singletons_open
- \+ *lemma* coinduced_le_iff_le_induced
- \+ *lemma* gc_coinduced_induced
- \+ *lemma* induced_top
- \+ *lemma* induced_inf
- \+ *lemma* induced_infi
- \+ *lemma* coinduced_bot
- \+ *lemma* coinduced_sup
- \+ *lemma* coinduced_supr
- \+ *lemma* le_generate_from
- \+ *lemma* nhds_infi
- \+ *lemma* nhds_Inf
- \+ *lemma* nhds_inf
- \+/\- *lemma* nhds_top
- \+ *lemma* continuous_iff_coinduced_le
- \+ *lemma* continuous_iff_le_induced
- \+ *lemma* continuous_sup_dom
- \+ *lemma* continuous_sup_rng_left
- \+ *lemma* continuous_sup_rng_right
- \+/\- *lemma* continuous_Sup_dom
- \+/\- *lemma* continuous_Sup_rng
- \+/\- *lemma* continuous_supr_dom
- \+/\- *lemma* continuous_supr_rng
- \+ *lemma* continuous_inf_rng
- \+ *lemma* continuous_inf_dom_left
- \+ *lemma* continuous_inf_dom_right
- \+/\- *lemma* continuous_Inf_dom
- \+/\- *lemma* continuous_Inf_rng
- \+/\- *lemma* continuous_infi_dom
- \+/\- *lemma* continuous_infi_rng
- \+/\- *lemma* continuous_bot
- \+/\- *lemma* continuous_top
- \+ *lemma* is_open_supr_iff
- \+/\- *lemma* is_closed_infi_iff
- \- *lemma* generate_from_le_iff_subset_is_open
- \- *lemma* eq_top_of_singletons_open
- \- *lemma* induced_le_iff_le_coinduced
- \- *lemma* gc_induced_coinduced
- \- *lemma* induced_bot
- \- *lemma* induced_sup
- \- *lemma* induced_supr
- \- *lemma* coinduced_top
- \- *lemma* coinduced_inf
- \- *lemma* coinduced_infi
- \- *lemma* generate_from_le
- \- *lemma* nhds_supr
- \- *lemma* nhds_Sup
- \- *lemma* nhds_sup
- \- *lemma* continuous_iff_le_coinduced
- \- *lemma* continuous_iff_induced_le
- \- *lemma* continuous_inf_dom
- \- *lemma* continuous_inf_rng_left
- \- *lemma* continuous_inf_rng_right
- \- *lemma* continuous_sup_rng
- \- *lemma* continuous_sup_dom_left
- \- *lemma* continuous_sup_dom_right
- \- *lemma* is_open_infi_iff
- \+ *def* tmp_order
- \+ *def* tmp_complete_lattice

Modified src/topology/separation.lean


Modified src/topology/stone_cech.lean
- \+/\- *lemma* dense_embedding_pure

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* infi_uniformity
- \+ *lemma* inf_uniformity
- \+/\- *lemma* to_topological_space_bot
- \+/\- *lemma* to_topological_space_top
- \+ *lemma* to_topological_space_infi
- \+ *lemma* to_topological_space_Inf
- \+ *lemma* to_topological_space_inf
- \- *lemma* supr_uniformity
- \- *lemma* sup_uniformity
- \- *lemma* to_topological_space_supr
- \- *lemma* to_topological_space_Sup
- \- *lemma* to_topological_space_sup

Modified src/topology/uniform_space/pi.lean




## [2019-06-19 08:03:18](https://github.com/leanprover-community/mathlib/commit/b1cb48d)
feat(data/set): simple lemmas, renaming ([#1137](https://github.com/leanprover-community/mathlib/pull/1137))
* feat(data/set): simple lemmas, renaming
* improve projection lemmas
* arguments order
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* fst_image_prod_subset
- \+ *lemma* fst_image_prod
- \+ *lemma* snd_image_prod_subset
- \+ *lemma* snd_image_prod
- \+/\- *theorem* preimage_id

Modified src/data/set/lattice.lean
- \+ *theorem* inter_Union
- \+ *theorem* Union_inter
- \+ *theorem* union_Union
- \+ *theorem* Union_union
- \+ *theorem* inter_Inter
- \+ *theorem* Inter_inter
- \+ *theorem* union_Inter
- \+ *theorem* Union_diff
- \+ *theorem* diff_Union
- \+ *theorem* diff_Inter
- \+ *theorem* inter_bUnion
- \+ *theorem* bUnion_inter
- \- *theorem* inter_Union_left
- \- *theorem* inter_Union_right
- \- *theorem* union_Union_left
- \- *theorem* union_Union_right
- \- *theorem* inter_Inter_left
- \- *theorem* inter_Inter_right
- \- *theorem* union_Inter_left
- \- *theorem* diff_Union_right
- \- *theorem* diff_Union_left
- \- *theorem* diff_Inter_left

Modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_supr_ae
- \+/\- *lemma* limsup_lintegral_le

Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* all_ae_of_all

Modified src/measure_theory/outer_measure.lean




## [2019-06-18 22:06:30](https://github.com/leanprover-community/mathlib/commit/235b899)
fix(category_theory/types): rename lemma `ulift_functor.map` ([#1133](https://github.com/leanprover-community/mathlib/pull/1133))
* fix(category_theory/types): avoid shadowing `ulift_functor.map` by a lemma
Now we can use `ulift_functor.map` in the sense `functor.map ulift_functor`.
* `ulift_functor.map_spec` → `ulift_functor_map`
as suggested by @semorrison in https://github.com/leanprover-community/mathlib/pull/1133#pullrequestreview-250179914
#### Estimated changes
Modified src/category_theory/types.lean
- \+ *lemma* ulift_functor_map
- \- *lemma* ulift_functor.map



## [2019-06-17 13:09:55](https://github.com/leanprover-community/mathlib/commit/d8d25e9)
refactor(analysis/normed_space/deriv): split and move to calculus folder ([#1135](https://github.com/leanprover-community/mathlib/pull/1135))
#### Estimated changes
Renamed src/analysis/normed_space/deriv.lean to src/analysis/calculus/deriv.lean
- \- *lemma* tangent_cone_univ
- \- *lemma* tangent_cone_mono
- \- *lemma* tangent_cone_at.lim_zero
- \- *lemma* tangent_cone_inter_open
- \- *lemma* unique_diff_within_univ_at
- \- *lemma* unique_diff_within_at_inter
- \- *lemma* is_open.unique_diff_within_at
- \- *lemma* unique_diff_on_inter
- \- *lemma* is_open.unique_diff_on
- \- *def* tangent_cone_at
- \- *def* unique_diff_within_at
- \- *def* unique_diff_on

Created src/analysis/calculus/tangent_cone.lean
- \+ *lemma* tangent_cone_univ
- \+ *lemma* tangent_cone_mono
- \+ *lemma* tangent_cone_at.lim_zero
- \+ *lemma* tangent_cone_inter_open
- \+ *lemma* unique_diff_within_univ_at
- \+ *lemma* unique_diff_within_at_inter
- \+ *lemma* is_open.unique_diff_within_at
- \+ *lemma* unique_diff_on_inter
- \+ *lemma* is_open.unique_diff_on
- \+ *def* tangent_cone_at
- \+ *def* unique_diff_within_at
- \+ *def* unique_diff_on



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

Created src/algebra/direct_limit.lean
- \+ *lemma* of_f
- \+ *lemma* lift_of
- \+ *lemma* totalize_apply
- \+ *lemma* to_module_totalize_of_le
- \+ *lemma* of.zero_exact_aux
- \+ *lemma* of_zero
- \+ *lemma* of_add
- \+ *lemma* of_neg
- \+ *lemma* of_sub
- \+ *lemma* lift_zero
- \+ *lemma* lift_add
- \+ *lemma* lift_neg
- \+ *lemma* lift_sub
- \+ *lemma* lift_unique
- \+ *lemma* of_one
- \+ *lemma* of_mul
- \+ *lemma* of_pow
- \+ *lemma* of.zero_exact_aux2
- \+ *lemma* of.zero_exact
- \+ *lemma* lift_one
- \+ *lemma* lift_mul
- \+ *lemma* lift_pow
- \+ *theorem* exists_of
- \+ *theorem* lift_unique
- \+ *theorem* of.zero_exact
- \+ *theorem* induction_on
- \+ *theorem* of_inj
- \+ *theorem* exists_inv
- \+ *def* direct_limit
- \+ *def* of
- \+ *def* lift
- \+ *def* directed_system

Modified src/algebra/module.lean
- \+ *def* is_add_group_hom.to_linear_map

Modified src/data/dfinsupp.lean
- \+ *lemma* support_smul

Modified src/data/polynomial.lean
- \+ *lemma* nat_cast_eq_C
- \+ *lemma* nat_degree_nat_cast
- \+ *lemma* int_cast_eq_C
- \+ *lemma* nat_degree_int_cast

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* single_eq_lof
- \+ *lemma* lof_apply
- \+ *lemma* apply_eq_component
- \+ *lemma* component.lof_self
- \+ *lemma* component.of
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *def* component

Modified src/linear_algebra/tensor_product.lean


Modified src/order/basic.lean


Modified src/ring_theory/free_comm_ring.lean
- \+ *lemma* restriction_of
- \+ *lemma* restriction_zero
- \+ *lemma* restriction_one
- \+ *lemma* restriction_add
- \+ *lemma* restriction_neg
- \+ *lemma* restriction_sub
- \+ *lemma* restriction_mul
- \+ *theorem* is_supported_upwards
- \+ *theorem* is_supported_add
- \+ *theorem* is_supported_neg
- \+ *theorem* is_supported_sub
- \+ *theorem* is_supported_mul
- \+ *theorem* is_supported_zero
- \+ *theorem* is_supported_one
- \+ *theorem* is_supported_int
- \+ *theorem* is_supported_of
- \+ *theorem* map_subtype_val_restriction
- \+ *theorem* exists_finite_support
- \+ *theorem* exists_finset_support
- \+ *def* is_supported
- \+ *def* restriction

Modified src/ring_theory/free_ring.lean




## [2019-06-16 19:04:52](https://github.com/leanprover-community/mathlib/commit/38d5c12)
feat(ring_theory/integral_closure): integral closure ([#1087](https://github.com/leanprover-community/mathlib/pull/1087))
* feat(ring_theory/integral_closure): integral closure
* update
#### Estimated changes
Created src/ring_theory/integral_closure.lean
- \+ *theorem* is_integral_algebra_map
- \+ *theorem* is_integral_of_subring
- \+ *theorem* is_integral_iff_is_integral_closure_finite
- \+ *theorem* fg_adjoin_singleton_of_integral
- \+ *theorem* fg_adjoin_of_finite
- \+ *theorem* is_integral_of_noetherian'
- \+ *theorem* is_integral_of_noetherian
- \+ *theorem* is_integral_of_mem_of_fg
- \+ *theorem* is_integral_of_mem_closure
- \+ *theorem* is_integral_zero
- \+ *theorem* is_integral_one
- \+ *theorem* is_integral_add
- \+ *theorem* is_integral_neg
- \+ *theorem* is_integral_sub
- \+ *theorem* is_integral_mul
- \+ *theorem* mem_integral_closure_iff_mem_fg
- \+ *theorem* integral_closure_idem
- \+ *def* is_integral
- \+ *def* integral_closure



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
- \+ *lemma* exists_succ
- \+ *lemma* succ_le_of_lt
- \+ *lemma* le_succ_of_forall_lt_le
- \+ *lemma* lt_succ_self
- \+ *lemma* lt_succ_iff_le
- \+ *lemma* of_nat_surjective_aux
- \+ *lemma* of_nat_surjective
- \+ *def* succ
- \+ *def* of_nat
- \+ *def* denumerable
- \+ *def* of_encodable_of_infinite

Modified src/data/equiv/encodable.lean
- \+ *def* decidable_range_encode
- \+ *def* equiv_range_encode

Modified src/data/fintype.lean
- \+ *lemma* exists_not_mem_finset
- \+ *lemma* of_injective
- \+ *lemma* of_surjective

Modified src/data/fp/basic.lean


Modified src/data/option/basic.lean
- \+ *lemma* some_get
- \+ *lemma* get_some

Modified src/data/padics/padic_norm.lean


Renamed src/data/rat.lean to src/data/rat/basic.lean


Created src/data/rat/denumerable.lean


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
- \+ *lemma* sub_left_inj

Modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable.supr_Prop
- \+ *lemma* measurable.infi_Prop
- \+ *lemma* measurable_add
- \+ *lemma* measurable_sub
- \+ *lemma* measurable_mul

Modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_supr_ae
- \+ *lemma* lintegral_sub
- \+ *lemma* lintegral_infi_ae
- \+ *lemma* lintegral_liminf_le
- \+ *lemma* limsup_lintegral_le
- \+ *lemma* dominated_convergence_nn

Modified src/measure_theory/measure_space.lean
- \+ *lemma* all_ae_of_all

Modified src/order/liminf_limsup.lean
- \+ *lemma* liminf_le_limsup
- \+ *lemma* limsup_eq_infi_supr_of_nat
- \+ *lemma* liminf_eq_supr_infi_of_nat

Modified src/topology/algebra/ordered.lean
- \+ *theorem* tendsto_of_liminf_eq_limsup
- \+ *theorem* limsup_eq_of_tendsto
- \+ *theorem* liminf_eq_of_tendsto

Modified src/topology/instances/nnreal.lean
- \+ *lemma* continuous_sub'
- \+ *lemma* continuous_sub



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
- \+ *lemma* coeff_X
- \+ *lemma* eval₂_comp_right
- \+ *lemma* map_eval₂
- \+ *lemma* rename_zero
- \+ *lemma* rename_one
- \+ *lemma* rename_add
- \+ *lemma* rename_sub
- \+ *lemma* rename_mul
- \+ *lemma* rename_pow
- \+ *lemma* map_rename



## [2019-06-11 19:10:13](https://github.com/leanprover-community/mathlib/commit/953c612)
fix(category_theory): simplifying universes ([#1122](https://github.com/leanprover-community/mathlib/pull/1122))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category.lean
- \+/\- *lemma* category.assoc_symm

Modified src/category_theory/comma.lean


Modified src/category_theory/concrete_category.lean
- \+/\- *def* mk_ob
- \+/\- *def* forget

Modified src/category_theory/const.lean


Modified src/category_theory/core.lean
- \+/\- *def* core

Modified src/category_theory/discrete_category.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean
- \+/\- *def* induced_category

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.map_post
- \+/\- *def* of_faithful

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* pair_function

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/monoidal/category.lean
- \+/\- *def* tensor_iso

Modified src/category_theory/monoidal/category_aux.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *def* iso.app

Modified src/category_theory/natural_transformation.lean


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
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* val_coe
- \- *lemma* coe_inv
- \- *lemma* inv_mul
- \- *lemma* mul_inv
- \- *lemma* mul_inv_cancel_left
- \- *lemma* inv_mul_cancel_left
- \- *lemma* mul_inv_cancel_right
- \- *lemma* inv_mul_cancel_right
- \- *lemma* free_monoid.one_def
- \- *lemma* free_monoid.mul_def
- \- *lemma* free_add_monoid.zero_def
- \- *lemma* free_add_monoid.add_def
- \- *lemma* is_conj_refl
- \- *lemma* is_conj_symm
- \- *lemma* is_conj_trans
- \- *lemma* is_conj_one_right
- \- *lemma* is_conj_one_left
- \- *lemma* conj_inv
- \- *lemma* conj_mul
- \- *lemma* is_conj_iff_eq
- \- *lemma* id
- \- *lemma* comp
- \- *lemma* comp'
- \- *lemma* map_mul
- \- *lemma* map_add
- \- *lemma* to_is_monoid_hom
- \- *lemma* injective_iff
- \- *lemma* is_group_hom.mul
- \- *lemma* is_group_hom.inv
- \- *lemma* inv.is_group_hom
- \- *lemma* map_sub
- \- *lemma* is_add_group_hom.sub
- \- *lemma* coe_map
- \- *lemma* map_id
- \- *lemma* map_comp
- \- *lemma* map_comp'
- \- *lemma* with_one.one_ne_coe
- \- *lemma* with_one.coe_ne_one
- \- *lemma* with_one.ne_one_iff_exists
- \- *lemma* with_one.coe_inj
- \- *lemma* with_one.mul_coe
- \- *lemma* mul_coe
- \- *lemma* inv_coe
- \- *lemma* inv_zero
- \- *lemma* inv_one
- \- *lemma* zero_div
- \- *lemma* div_zero
- \- *lemma* div_coe
- \- *lemma* one_div
- \- *lemma* div_one
- \- *lemma* mul_right_inv
- \- *lemma* mul_left_inv
- \- *lemma* mul_inv_rev
- \- *lemma* mul_div_cancel
- \- *lemma* div_mul_cancel
- \- *lemma* div_eq_iff_mul_eq
- \- *lemma* div_eq_div
- \- *theorem* mul_left_inj
- \- *theorem* mul_right_inj
- \- *theorem* ext
- \- *theorem* ext_iff
- \- *theorem* nat.units_eq_one
- \- *theorem* map_one
- \- *theorem* map_inv
- \- *theorem* inv_is_group_anti_hom
- \- *def* additive
- \- *def* multiplicative
- \- *def* units.mk_of_mul_eq_one
- \- *def* free_monoid
- \- *def* free_add_monoid
- \- *def* is_conj
- \- *def* with_one

Created src/algebra/group/anti_hom.lean
- \+ *theorem* map_one
- \+ *theorem* map_inv
- \+ *theorem* inv_is_group_anti_hom

Created src/algebra/group/basic.lean
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_right_inj

Created src/algebra/group/conj.lean
- \+ *lemma* is_conj_refl
- \+ *lemma* is_conj_symm
- \+ *lemma* is_conj_trans
- \+ *lemma* is_conj_one_right
- \+ *lemma* is_conj_one_left
- \+ *lemma* conj_inv
- \+ *lemma* conj_mul
- \+ *lemma* is_conj_iff_eq
- \+ *def* is_conj

Created src/algebra/group/default.lean


Created src/algebra/group/free_monoid.lean
- \+ *lemma* free_monoid.one_def
- \+ *lemma* free_monoid.mul_def
- \+ *lemma* free_add_monoid.zero_def
- \+ *lemma* free_add_monoid.add_def
- \+ *def* free_monoid
- \+ *def* free_add_monoid

Created src/algebra/group/hom.lean
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* comp'
- \+ *lemma* map_mul
- \+ *lemma* map_add
- \+ *lemma* to_is_monoid_hom
- \+ *lemma* injective_iff
- \+ *lemma* is_group_hom.mul
- \+ *lemma* is_group_hom.inv
- \+ *lemma* inv.is_group_hom
- \+ *lemma* map_sub
- \+ *lemma* is_add_group_hom.sub
- \+ *theorem* map_one
- \+ *theorem* map_inv

Created src/algebra/group/to_additive.lean


Created src/algebra/group/type_tags.lean
- \+ *def* additive
- \+ *def* multiplicative

Created src/algebra/group/units.lean
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* val_coe
- \+ *lemma* coe_inv
- \+ *lemma* inv_mul
- \+ *lemma* mul_inv
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* inv_mul_cancel_right
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_right_inj
- \+ *theorem* nat.units_eq_one
- \+ *def* units.mk_of_mul_eq_one

Created src/algebra/group/units_hom.lean
- \+ *lemma* coe_map
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_comp'

Created src/algebra/group/with_one.lean
- \+ *lemma* with_one.one_ne_coe
- \+ *lemma* with_one.coe_ne_one
- \+ *lemma* with_one.ne_one_iff_exists
- \+ *lemma* with_one.coe_inj
- \+ *lemma* with_one.mul_coe
- \+ *lemma* coe_one
- \+ *lemma* mul_coe
- \+ *lemma* inv_coe
- \+ *lemma* inv_zero
- \+ *lemma* inv_one
- \+ *lemma* zero_div
- \+ *lemma* div_zero
- \+ *lemma* div_coe
- \+ *lemma* one_div
- \+ *lemma* div_one
- \+ *lemma* mul_right_inv
- \+ *lemma* mul_left_inv
- \+ *lemma* mul_inv_rev
- \+ *lemma* mul_div_cancel
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_eq_iff_mul_eq
- \+ *lemma* div_eq_div
- \+ *def* with_one



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
- \+ *lemma* commutator_subset_ker
- \+/\- *lemma* lift.of



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
Created src/group_theory/presented_group.lean
- \+ *lemma* closure_rels_subset_ker
- \+ *lemma* to_group_eq_one_of_mem_closure
- \+ *lemma* to_group.of
- \+ *lemma* to_group.mul
- \+ *lemma* to_group.one
- \+ *lemma* to_group.inv
- \+ *theorem* to_group.unique
- \+ *def* presented_group
- \+ *def* of
- \+ *def* to_group



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
- \+ *theorem* coe_nat_inj
- \+ *def* primes

Deleted src/data/pnat.lean
- \- *theorem* succ_pnat_coe
- \- *theorem* pos
- \- *theorem* eq
- \- *theorem* mk_coe
- \- *theorem* add_coe
- \- *theorem* ne_zero
- \- *theorem* to_pnat'_coe
- \- *theorem* coe_to_pnat'
- \- *theorem* one_coe
- \- *theorem* mul_coe
- \- *theorem* pow_coe
- \- *def* pnat
- \- *def* to_pnat
- \- *def* succ_pnat
- \- *def* to_pnat'
- \- *def* pow

Created src/data/pnat/basic.lean
- \+ *lemma* mod_div_aux_spec
- \+ *theorem* succ_pnat_coe
- \+ *theorem* succ_pnat_inj
- \+ *theorem* to_pnat'_coe
- \+ *theorem* coe_pnat_nat
- \+ *theorem* coe_pnat_inj
- \+ *theorem* pos
- \+ *theorem* eq
- \+ *theorem* mk_coe
- \+ *theorem* add_coe
- \+ *theorem* ne_zero
- \+ *theorem* coe_to_pnat'
- \+ *theorem* one_coe
- \+ *theorem* mul_coe
- \+ *theorem* pow_coe
- \+ *theorem* sub_coe
- \+ *theorem* add_sub_of_lt
- \+ *theorem* mod_add_div
- \+ *theorem* mod_coe
- \+ *theorem* div_coe
- \+ *theorem* mod_le
- \+ *theorem* dvd_iff
- \+ *theorem* dvd_iff'
- \+ *theorem* mul_div_exact
- \+ *theorem* dvd_iff''
- \+ *theorem* dvd_intro
- \+ *theorem* dvd_refl
- \+ *theorem* dvd_antisymm
- \+ *theorem* dvd_trans
- \+ *theorem* one_dvd
- \+ *theorem* dvd_one_iff
- \+ *theorem* gcd_coe
- \+ *theorem* lcm_coe
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* dvd_gcd
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* lcm_dvd
- \+ *theorem* gcd_mul_lcm
- \+ *def* pnat
- \+ *def* to_pnat
- \+ *def* succ_pnat
- \+ *def* to_pnat'
- \+ *def* mod_div_aux
- \+ *def* mod_div
- \+ *def* mod
- \+ *def* div
- \+ *def* div_exact
- \+ *def* gcd
- \+ *def* lcm
- \+ *def* prime

Created src/data/pnat/factors.lean
- \+ *theorem* add_sub_of_le
- \+ *theorem* card_of_prime
- \+ *theorem* coe_nat_inj
- \+ *theorem* coe_nat_of_prime
- \+ *theorem* coe_nat_prime
- \+ *theorem* coe_pnat_inj
- \+ *theorem* coe_pnat_of_prime
- \+ *theorem* coe_pnat_prime
- \+ *theorem* coe_pnat_nat
- \+ *theorem* coe_prod
- \+ *theorem* prod_of_prime
- \+ *theorem* to_of_nat_multiset
- \+ *theorem* prod_of_nat_multiset
- \+ *theorem* to_of_pnat_multiset
- \+ *theorem* prod_of_pnat_multiset
- \+ *theorem* prod_of_nat_list
- \+ *theorem* prod_of_pnat_list
- \+ *theorem* prod_zero
- \+ *theorem* prod_add
- \+ *theorem* prod_smul
- \+ *theorem* prod_factor_multiset
- \+ *theorem* coe_nat_factor_multiset
- \+ *theorem* factor_multiset_prod
- \+ *theorem* factor_multiset_one
- \+ *theorem* factor_multiset_mul
- \+ *theorem* factor_multiset_pow
- \+ *theorem* factor_multiset_of_prime
- \+ *theorem* factor_multiset_le_iff
- \+ *theorem* factor_multiset_le_iff'
- \+ *theorem* prod_dvd_iff
- \+ *theorem* prod_dvd_iff'
- \+ *theorem* factor_multiset_gcd
- \+ *theorem* factor_multiset_lcm
- \+ *theorem* count_factor_multiset
- \+ *theorem* prod_inf
- \+ *theorem* prod_sup
- \+ *def* prime_multiset
- \+ *def* of_prime
- \+ *def* to_nat_multiset
- \+ *def* to_pnat_multiset
- \+ *def* prod
- \+ *def* of_nat_multiset
- \+ *def* of_pnat_multiset
- \+ *def* of_nat_list
- \+ *def* of_pnat_list
- \+ *def* factor_multiset
- \+ *def* factor_multiset_equiv

Created src/data/pnat/xgcd.lean
- \+ *theorem* v_eq_succ_vp
- \+ *theorem* is_special_iff
- \+ *theorem* is_reduced_iff
- \+ *theorem* flip_w
- \+ *theorem* flip_x
- \+ *theorem* flip_y
- \+ *theorem* flip_z
- \+ *theorem* flip_a
- \+ *theorem* flip_b
- \+ *theorem* flip_is_reduced
- \+ *theorem* flip_is_special
- \+ *theorem* flip_v
- \+ *theorem* rq_eq
- \+ *theorem* qp_eq
- \+ *theorem* start_is_special
- \+ *theorem* start_v
- \+ *theorem* finish_is_reduced
- \+ *theorem* finish_is_special
- \+ *theorem* finish_v
- \+ *theorem* step_wf
- \+ *theorem* step_is_special
- \+ *theorem* step_v
- \+ *theorem* reduce_a
- \+ *theorem* reduce_b
- \+ *theorem* reduce_reduced
- \+ *theorem* reduce_reduced'
- \+ *theorem* reduce_special
- \+ *theorem* reduce_special'
- \+ *theorem* reduce_v
- \+ *theorem* gcd_a'_coe
- \+ *theorem* gcd_b'_coe
- \+ *theorem* gcd_props
- \+ *theorem* gcd_eq
- \+ *theorem* gcd_det_eq
- \+ *theorem* gcd_a_eq
- \+ *theorem* gcd_b_eq
- \+ *theorem* gcd_rel_left'
- \+ *theorem* gcd_rel_right'
- \+ *theorem* gcd_rel_left
- \+ *theorem* gcd_rel_right
- \+ *def* mk'
- \+ *def* w
- \+ *def* z
- \+ *def* a
- \+ *def* b
- \+ *def* r
- \+ *def* q
- \+ *def* qp
- \+ *def* vp
- \+ *def* v
- \+ *def* succ₂
- \+ *def* is_special
- \+ *def* is_special'
- \+ *def* is_reduced
- \+ *def* is_reduced'
- \+ *def* flip
- \+ *def* start
- \+ *def* finish
- \+ *def* step
- \+ *def* reduce
- \+ *def* xgcd:
- \+ *def* gcd_d
- \+ *def* gcd_w
- \+ *def* gcd_x
- \+ *def* gcd_y
- \+ *def* gcd_z
- \+ *def* gcd_a'
- \+ *def* gcd_b'

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


Created src/tactic/rewrite_all/basic.lean
- \+ *def* side.other
- \+ *def* side.to_string

Created src/tactic/rewrite_all/congr.lean


Created src/tactic/rewrite_all/default.lean


Created test/rewrite_all.lean




## [2019-06-07 16:54:39](https://github.com/leanprover-community/mathlib/commit/b55e44d)
refactor(analysis/normed_space/basic): change normed_space definition ([#1112](https://github.com/leanprover-community/mathlib/pull/1112))
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/convex.lean
- \+/\- *lemma* convex_on_dist
- \+/\- *lemma* convex_ball
- \+/\- *lemma* convex_closed_ball

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *theorem* normed_group.tendsto_nhds_zero
- \- *theorem* normed_space.tendsto_nhds_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* op_norm_neg



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
- \+ *lemma* continuous_linear_map.is_bounded_linear_map
- \+ *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+ *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+ *lemma* is_bounded_bilinear_map_deriv_coe
- \- *lemma* bounded_linear_map.is_bounded_linear_map
- \- *lemma* bounded_linear_map.is_bounded_linear_map_comp_left
- \- *lemma* bounded_linear_map.is_bounded_linear_map_comp_right
- \- *theorem* is_linear_map.bounded_of_continuous_at
- \+ *def* to_continuous_linear_map
- \+ *def* is_bounded_bilinear_map.linear_deriv
- \+/\- *def* is_bounded_bilinear_map.deriv
- \- *def* to_bounded_linear_map

Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.continuous_of_bound
- \+ *lemma* linear_map_with_bound_coe
- \+ *lemma* linear_map_with_bound_apply
- \+ *lemma* norm_zero
- \+ *lemma* norm_id
- \+ *lemma* scalar_prod_space_iso_norm
- \- *lemma* map_zero
- \- *lemma* map_add
- \- *lemma* map_sub
- \- *lemma* map_smul
- \- *lemma* map_neg
- \- *lemma* coe_coe
- \- *lemma* zero_apply
- \- *lemma* coe_zero
- \- *lemma* coe_zero'
- \- *lemma* id_apply
- \- *lemma* coe_id
- \- *lemma* coe_id'
- \- *lemma* add_apply
- \- *lemma* coe_add
- \- *lemma* coe_add'
- \- *lemma* smul_apply
- \- *lemma* coe_apply
- \- *lemma* coe_apply'
- \- *lemma* neg_apply
- \- *lemma* coe_neg
- \- *lemma* coe_neg'
- \- *lemma* sub_apply
- \- *lemma* coe_sub
- \- *lemma* coe_sub'
- \- *lemma* coe_comp
- \- *lemma* coe_comp'
- \+ *theorem* bound
- \+/\- *theorem* is_O_id
- \- *theorem* ext
- \- *theorem* ext_iff
- \- *theorem* continuous
- \+ *def* linear_map.with_bound
- \- *def* zero
- \- *def* id
- \- *def* comp
- \- *def* prod
- \- *def* scalar_prod_space_iso

Created src/topology/algebra/module.lean
- \+ *lemma* continuous_smul'
- \+ *lemma* continuous_smul
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_sub
- \+ *lemma* map_smul
- \+ *lemma* map_neg
- \+ *lemma* coe_coe
- \+ *lemma* zero_apply
- \+ *lemma* coe_zero
- \+ *lemma* coe_zero'
- \+ *lemma* id_apply
- \+ *lemma* coe_id
- \+ *lemma* coe_id'
- \+ *lemma* add_apply
- \+ *lemma* coe_add
- \+ *lemma* coe_add'
- \+ *lemma* neg_apply
- \+ *lemma* coe_neg
- \+ *lemma* coe_neg'
- \+ *lemma* sub_apply
- \+ *lemma* coe_sub
- \+ *lemma* coe_sub'
- \+ *lemma* coe_comp
- \+ *lemma* coe_comp'
- \+ *lemma* smul_apply
- \+ *lemma* coe_apply
- \+ *lemma* coe_apply'
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *def* zero
- \+ *def* id
- \+ *def* comp
- \+ *def* prod
- \+ *def* scalar_prod_space_iso



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


Created docs/install/extensions-icon.png


Modified docs/install/linux.md


Modified docs/install/macos.md


Modified docs/install/project.md


Modified docs/install/windows.md




## [2019-06-04 14:48:57+01:00](https://github.com/leanprover-community/mathlib/commit/542d25d)
fix(data/logic/basic): Use a Sort for classical.some_spec2 ([#1111](https://github.com/leanprover-community/mathlib/pull/1111))
#### Estimated changes
Modified src/logic/basic.lean
- \+/\- *lemma* some_spec2



## [2019-06-03 22:11:39](https://github.com/leanprover-community/mathlib/commit/dd832f0)
feat(topology/basic): is_open_Inter and others ([#1108](https://github.com/leanprover-community/mathlib/pull/1108))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* is_open_Inter
- \+ *lemma* is_open_Inter_prop
- \+ *lemma* is_closed_bUnion
- \+/\- *lemma* is_closed_Union
- \+ *lemma* is_closed_Union_prop

Modified src/topology/uniform_space/cauchy.lean




## [2019-06-03 20:36:09](https://github.com/leanprover-community/mathlib/commit/504c0ad)
feat(data/set/basic): union_inter_distrib lemmas ([#1107](https://github.com/leanprover-community/mathlib/pull/1107))
* feat(data/set/basic): union_inter_distrib lemmas
* add parentheses
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* inter_union_distrib_left
- \+ *theorem* inter_union_distrib_right
- \+ *theorem* union_inter_distrib_left
- \+ *theorem* union_inter_distrib_right



## [2019-06-03 18:05:35](https://github.com/leanprover-community/mathlib/commit/4263b2b)
fix(data/nat/gcd): correct order of arguments in nat.coprime_mul_iff_right ([#1105](https://github.com/leanprover-community/mathlib/pull/1105))
* Not sure how this works
* Fix order for coprime_mul_iff_right
* Remove spurious file
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+/\- *lemma* coprime_mul_iff_right



## [2019-06-01 20:38:34](https://github.com/leanprover-community/mathlib/commit/38b8054)
feat(data/mv_polynomial): add coeff for mv_polynomial ([#1101](https://github.com/leanprover-community/mathlib/pull/1101))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* nat_sub_apply

Modified src/data/mv_polynomial.lean
- \+ *lemma* ext
- \+ *lemma* coeff_add
- \+ *lemma* coeff_zero
- \+ *lemma* coeff_zero_X
- \+ *lemma* coeff_sum
- \+ *lemma* monic_monomial_eq
- \+ *lemma* coeff_monomial
- \+ *lemma* coeff_C
- \+ *lemma* coeff_C_mul
- \+ *lemma* coeff_mul_X
- \+ *lemma* coeff_mul_X'
- \+ *lemma* coeff_map
- \+ *lemma* coeff_sub
- \+ *def* tmp.coe
- \+ *def* coeff

