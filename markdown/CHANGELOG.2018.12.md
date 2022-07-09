## [2018-12-28 02:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/17d6263)
refactor(category_theory): minimize the amount of universe annotations in category_theory ([#552](https://github.com/leanprover-community/mathlib/pull/552))
#### Estimated changes
Modified category_theory/category.lean
- \+/\- *lemma* category.assoc_symm
- \+/\- *lemma* category.assoc_symm

Modified category_theory/comma.lean

Modified category_theory/const.lean

Modified category_theory/discrete_category.lean

Modified category_theory/eq_to_hom.lean

Modified category_theory/equivalence.lean
- \+/\- *def* obj_preimage
- \+/\- *def* obj_preimage

Modified category_theory/examples/topological_spaces.lean

Modified category_theory/full_subcategory.lean

Modified category_theory/fully_faithful.lean

Modified category_theory/functor.lean

Modified category_theory/functor_category.lean

Modified category_theory/groupoid.lean

Modified category_theory/isomorphism.lean

Modified category_theory/limits/cones.lean

Modified category_theory/limits/functor_category.lean
- \+/\- *def* functor_category_is_colimit_cocone
- \+/\- *def* functor_category_is_colimit_cocone

Modified category_theory/limits/limits.lean
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_pre'
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.pre_map'
- \+/\- *lemma* colimit.map_post
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_pre'
- \+/\- *lemma* limit.map_post
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.pre_map'
- \+/\- *lemma* colimit.map_post
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful
- \+/\- *def* of_faithful

Modified category_theory/limits/preserves.lean

Modified category_theory/limits/types.lean

Modified category_theory/natural_isomorphism.lean
- \+/\- *def* ulift_down_up
- \+/\- *def* ulift_up_down
- \+/\- *def* ulift_down_up
- \+/\- *def* ulift_up_down

Modified category_theory/natural_transformation.lean

Modified category_theory/opposites.lean

Modified category_theory/pempty.lean

Modified category_theory/products.lean

Modified category_theory/punit.lean

Modified category_theory/types.lean

Modified category_theory/whiskering.lean

Modified category_theory/yoneda.lean



## [2018-12-26 19:45:48-05:00](https://github.com/leanprover-community/mathlib/commit/a71628a)
feat(algebra/order,...): material on orders ([#554](https://github.com/leanprover-community/mathlib/pull/554))
#### Estimated changes
Modified algebra/order.lean
- \+ *lemma* le_of_forall_le'
- \+ *lemma* le_of_forall_lt'

Modified algebra/order_functions.lean
- \+/\- *lemma* le_min_iff
- \+/\- *lemma* max_le_iff
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* le_max_iff
- \+/\- *lemma* max_lt_iff
- \+/\- *lemma* lt_min_iff
- \+/\- *lemma* lt_max_iff
- \+/\- *lemma* min_lt_iff
- \+/\- *lemma* le_min_iff
- \+/\- *lemma* max_le_iff
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* le_max_iff
- \+/\- *lemma* max_lt_iff
- \+/\- *lemma* lt_min_iff
- \+/\- *lemma* lt_max_iff
- \+/\- *lemma* min_lt_iff

Modified algebra/ordered_group.lean
- \+ *lemma* add_lt_top
- \+ *lemma* with_top.add_lt_add_iff_right

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_eq_top_iff

Modified data/finset.lean

Modified order/bounded_lattice.lean
- \+ *lemma* ne_top_of_lt
- \+ *lemma* ne_bot_of_gt

Modified order/lattice.lean
- \+ *lemma* sup_lt_iff
- \+ *lemma* lt_inf_iff



## [2018-12-24 20:12:21-05:00](https://github.com/leanprover-community/mathlib/commit/a04c7e2)
feat(analysis/topology): miscellaneous topology ([#484](https://github.com/leanprover-community/mathlib/pull/484))
* miscellaneous topology
* C is a proper metric space
* Sum of metric spaces is a def instead of instance
* refactor(analysis): shorten/simplify proofs
#### Estimated changes
Modified analysis/complex.lean
- \+ *def* real_prod_homeo

Modified analysis/metric_space.lean
- \+ *lemma* closed_ball_Icc
- \+ *lemma* prod.dist_eq
- \+ *lemma* sum.one_dist_le
- \+ *lemma* sum.one_dist_le'
- \+ *def* metric_space_sum

Modified analysis/real.lean

Modified analysis/topology/continuity.lean
- \+ *lemma* compact_prod
- \+ *lemma* compact_image
- \+ *lemma* compact_preimage
- \- *lemma* compact_univ
- \- *lemma* compact_of_closed

Modified analysis/topology/topological_space.lean
- \+ *lemma* compact_Union_of_compact
- \+ *lemma* compact_union_of_compact
- \+ *lemma* compact_univ
- \+ *lemma* compact_of_closed

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* closure_le_eq
- \+ *lemma* mem_closure_of_is_lub
- \+ *lemma* mem_of_is_lub_of_is_closed
- \+ *lemma* mem_closure_of_is_glb
- \+ *lemma* mem_of_is_glb_of_is_closed
- \+ *lemma* bdd_below_of_compact
- \+ *lemma* bdd_above_of_compact
- \+ *lemma* Sup_mem_closure
- \+ *lemma* Inf_mem_closure
- \+ *lemma* Sup_mem_of_is_closed
- \+ *lemma* Inf_mem_of_is_closed
- \+ *lemma* Sup_of_Sup_of_monotone_of_continuous
- \+ *lemma* supr_of_supr_of_monotone_of_continuous
- \+ *lemma* Inf_of_Inf_of_monotone_of_continuous
- \+ *lemma* infi_of_infi_of_monotone_of_continuous
- \+ *lemma* cSup_mem_closure
- \+ *lemma* cInf_mem_closure
- \+ *lemma* cSup_mem_of_is_closed
- \+ *lemma* cInf_mem_of_is_closed
- \+ *lemma* cSup_of_cSup_of_monotone_of_continuous
- \+ *lemma* csupr_of_csupr_of_monotone_of_continuous
- \+ *lemma* cInf_of_cInf_of_monotone_of_continuous
- \+ *lemma* cinfi_of_cinfi_of_monotone_of_continuous
- \+ *lemma* exists_forall_le_of_compact_of_continuous
- \+ *lemma* exists_forall_ge_of_compact_of_continuous
- \+/\- *lemma* closure_le_eq

Modified analysis/topology/uniform_space.lean
- \+ *lemma* union_mem_uniformity_sum
- \+ *lemma* uniformity_sum_of_open_aux
- \+ *lemma* open_of_uniformity_sum_aux
- \+ *lemma* sum.uniformity
- \+ *def* uniform_space.core.sum

Modified data/complex/basic.lean
- \+ *theorem* real_prod_equiv_apply
- \+ *theorem* real_prod_equiv_symm_re
- \+ *theorem* real_prod_equiv_symm_im
- \+ *def* real_prod_equiv

Modified data/real/basic.lean

Modified data/real/nnreal.lean
- \- *lemma* image_eq_empty

Modified data/set/basic.lean
- \+ *lemma* univ_eq_empty_iff
- \+ *lemma* exists_mem_of_nonempty
- \+ *lemma* univ_ne_empty
- \+ *lemma* image_eq_empty
- \+ *lemma* range_eq_empty

Modified data/set/finite.lean
- \+ *theorem* finite_univ

Modified order/complete_lattice.lean
- \+ *def* has_Inf_to_nonempty
- \+ *def* has_Sup_to_nonempty

Modified order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_below_empty
- \+ *lemma* bdd_above_inter_left
- \+ *lemma* bdd_above_inter_right
- \+ *lemma* bdd_below_inter_left
- \+ *lemma* bdd_below_inter_right
- \+ *lemma* bdd_above_of_bdd_above_of_monotone
- \+ *lemma* bdd_below_of_bdd_below_of_monotone
- \+/\- *lemma* bdd_above_finite
- \+/\- *lemma* bdd_above_finite_union
- \+/\- *lemma* bdd_below_finite
- \+/\- *lemma* bdd_below_finite_union
- \+ *lemma* csupr_le_csupr
- \+ *lemma* csupr_le
- \+ *lemma* le_csupr
- \+ *lemma* cinfi_le_cinfi
- \+ *lemma* le_cinfi
- \+ *lemma* cinfi_le
- \+ *lemma* is_lub_cSup
- \+ *lemma* is_glb_cInf
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_below_empty
- \- *lemma* bdd_above_Int1
- \- *lemma* bdd_above_Int2
- \- *lemma* bdd_below_Int1
- \- *lemma* bdd_below_Int2
- \+/\- *lemma* bdd_above_finite
- \+/\- *lemma* bdd_above_finite_union
- \+/\- *lemma* bdd_below_finite
- \+/\- *lemma* bdd_below_finite_union
- \+ *theorem* cSup_of_mem_of_le
- \+ *theorem* cInf_of_mem_of_le
- \- *theorem* cSup_of_in_of_le
- \- *theorem* cInf_of_in_of_le



## [2018-12-22 01:10:55-05:00](https://github.com/leanprover-community/mathlib/commit/3eb7424)
refactor(data/set/basic): remove unused hypotheses in union_inter_cancel_* ([#551](https://github.com/leanprover-community/mathlib/pull/551))
#### Estimated changes
Modified analysis/measure_theory/outer_measure.lean

Modified data/set/basic.lean
- \+/\- *theorem* union_inter_cancel_left
- \+/\- *theorem* union_inter_cancel_right
- \+/\- *theorem* union_inter_cancel_left
- \+/\- *theorem* union_inter_cancel_right



## [2018-12-21 04:05:56-05:00](https://github.com/leanprover-community/mathlib/commit/cdab35d)
fix(category_theory/punit): fix regression ([#550](https://github.com/leanprover-community/mathlib/pull/550))
#### Estimated changes
Modified category_theory/punit.lean
- \+ *lemma* obj_obj
- \+ *lemma* obj_map
- \+ *lemma* map_app
- \+ *def* of



## [2018-12-21 03:12:01-05:00](https://github.com/leanprover-community/mathlib/commit/b11b83b)
feat(data/list/basic): rotate a list ([#542](https://github.com/leanprover-community/mathlib/pull/542))
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* nth_le_singleton
- \+ *lemma* nth_le_append
- \+ *lemma* nth_le_repeat
- \+ *lemma* nth_append
- \+ *lemma* nth_concat_length:
- \+ *lemma* drop_all
- \+ *lemma* drop_append_of_le_length
- \+ *lemma* take_append_of_le_length
- \+ *lemma* rotate_mod
- \+ *lemma* rotate_nil
- \+ *lemma* rotate_zero
- \+ *lemma* rotate'_nil
- \+ *lemma* rotate'_zero
- \+ *lemma* rotate'_cons_succ
- \+ *lemma* length_rotate'
- \+ *lemma* rotate'_eq_take_append_drop
- \+ *lemma* rotate'_rotate'
- \+ *lemma* rotate'_length
- \+ *lemma* rotate'_length_mul
- \+ *lemma* rotate'_mod
- \+ *lemma* rotate_eq_rotate'
- \+ *lemma* rotate_cons_succ
- \+ *lemma* length_rotate
- \+ *lemma* rotate_eq_take_append_drop
- \+ *lemma* rotate_rotate
- \+ *lemma* rotate_length
- \+ *lemma* rotate_length_mul
- \+ *lemma* prod_rotate_eq_one_of_prod_eq_one
- \+/\- *theorem* take_all
- \+/\- *theorem* take_all

Modified data/list/defs.lean
- \+ *def* rotate
- \+ *def* rotate'

Modified data/nat/modeq.lean
- \+ *lemma* nth_rotate
- \+ *lemma* rotate_eq_self_iff_eq_repeat



## [2018-12-21 02:35:06-05:00](https://github.com/leanprover-community/mathlib/commit/d7cea06)
feat (ring_theory/noetherian) various lemmas ([#548](https://github.com/leanprover-community/mathlib/pull/548))
#### Estimated changes
Modified ring_theory/noetherian.lean
- \+ *theorem* fg_bot
- \+ *theorem* fg_sup
- \+ *theorem* fg_map
- \+ *theorem* fg_prod
- \+ *theorem* fg_of_fg_map_of_fg_inf_ker
- \+ *theorem* is_noetherian_submodule
- \+ *theorem* is_noetherian_submodule_left
- \+ *theorem* is_noetherian_submodule_right
- \+ *theorem* is_noetherian_of_surjective
- \+ *theorem* is_noetherian_of_linear_equiv
- \+ *theorem* is_noetherian_prod
- \+ *theorem* is_noetherian_pi
- \+ *theorem* is_noetherian_of_fg_of_noetherian
- \+ *theorem* is_noetherian_ring_of_surjective
- \+ *theorem* is_noetherian_ring_of_ring_equiv



## [2018-12-20 23:14:00-05:00](https://github.com/leanprover-community/mathlib/commit/3762d96)
feat(ring_theory/ideals): lift for quotient rings ([#529](https://github.com/leanprover-community/mathlib/pull/529))
#### Estimated changes
Modified ring_theory/ideals.lean
- \+ *lemma* ext
- \+ *lemma* lift_mk
- \+ *theorem* mem_span_pair
- \+ *theorem* is_coprime_def
- \+ *theorem* is_coprime_self
- \+ *def* is_coprime
- \+ *def* lift



## [2018-12-20 23:12:51-05:00](https://github.com/leanprover-community/mathlib/commit/73933b7)
feat(category_theory): assorted small changes from the old limits PR ([#512](https://github.com/leanprover-community/mathlib/pull/512))
#### Estimated changes
Modified algebra/pi_instances.lean
- \+ *def* is_ring_hom_pi

Modified category_theory/category.lean
- \+ *lemma* category.assoc_symm
- \+ *lemma* bundled_hom_coe

Created category_theory/discrete_category.lean
- \+ *lemma* functor_map_id
- \+ *def* discrete
- \+ *def* of_function
- \+ *def* of_function
- \+ *def* lift

Modified category_theory/examples/rings.lean
- \+ *lemma* CommRing_hom_coe_app
- \+/\- *def* forget_to_CommMon
- \- *def* is_comm_ring_hom
- \+/\- *def* forget_to_CommMon

Modified category_theory/examples/topological_spaces.lean

Modified category_theory/functor.lean

Modified category_theory/functor_category.lean

Modified category_theory/limits/cones.lean

Modified category_theory/limits/limits.lean
- \+ *lemma* limit.lift_extend
- \+ *lemma* colimit.desc_extend

Modified category_theory/opposites.lean

Modified category_theory/pempty.lean
- \+/\- *def* empty
- \+/\- *def* empty

Modified category_theory/punit.lean
- \- *lemma* obj_obj
- \- *lemma* obj_map
- \- *lemma* map_app
- \- *def* of

Created data/ulift.lean
- \+ *lemma* plift.rec.constant
- \+ *lemma* ulift.rec.constant

Modified tactic/ext.lean
- \+ *lemma* ext



## [2018-12-20 09:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/1854dd9)
feat(group_theory/order_of_element): lemmas about card of subgroups and normalizer ([#545](https://github.com/leanprover-community/mathlib/pull/545))
#### Estimated changes
Modified group_theory/order_of_element.lean
- \+ *lemma* conj_inj
- \+ *lemma* mem_normalizer_fintype
- \+ *lemma* card_eq_card_quotient_mul_card_subgroup
- \+ *lemma* card_subgroup_dvd_card
- \+ *lemma* card_quotient_dvd_card
- \+ *lemma* card_trivial
- \+ *lemma* order_of_one
- \+ *lemma* order_of_eq_one_iff

Modified group_theory/subgroup.lean
- \+ *lemma* subset_normalizer
- \+/\- *def* gpowers
- \+/\- *def* gmultiples
- \+ *def* normalizer
- \+/\- *def* gpowers
- \+/\- *def* gmultiples



## [2018-12-20 09:30:12-05:00](https://github.com/leanprover-community/mathlib/commit/95bdce8)
feat(data/set/finite): card_range_of_injective ([#543](https://github.com/leanprover-community/mathlib/pull/543))
#### Estimated changes
Modified data/set/finite.lean
- \+ *lemma* card_range_of_injective



## [2018-12-20 09:29:35-05:00](https://github.com/leanprover-community/mathlib/commit/0882f8e)
feat(data/fintype): exists_ne_of_card_gt_one ([#544](https://github.com/leanprover-community/mathlib/pull/544))
#### Estimated changes
Modified data/fintype.lean
- \+ *lemma* fintype.exists_ne_of_card_gt_one
- \+ *lemma* card_vector



## [2018-12-20 09:28:29-05:00](https://github.com/leanprover-community/mathlib/commit/4335380)
feat(data/vector2): vector_zero_subsingleton ([#547](https://github.com/leanprover-community/mathlib/pull/547))
#### Estimated changes
Modified data/vector2.lean



## [2018-12-20 08:15:19-05:00](https://github.com/leanprover-community/mathlib/commit/402e71e)
feat(order/filter): tendsto_at_top_at_top ([#540](https://github.com/leanprover-community/mathlib/pull/540))
#### Estimated changes
Modified order/filter.lean
- \+ *lemma* tendsto_at_top_at_top



## [2018-12-20 08:14:46-05:00](https://github.com/leanprover-community/mathlib/commit/f64b9aa)
feat(data/finsupp): frange ([#537](https://github.com/leanprover-community/mathlib/pull/537))
#### Estimated changes
Modified data/finsupp.lean
- \+ *theorem* mem_frange
- \+ *theorem* zero_not_mem_frange
- \+ *theorem* frange_single
- \+ *def* frange



## [2018-12-20 08:13:39-05:00](https://github.com/leanprover-community/mathlib/commit/bc21f62)
feat(ring_theory/ideal_operations): correspondence under surjection ([#534](https://github.com/leanprover-community/mathlib/pull/534))
#### Estimated changes
Modified ring_theory/ideal_operations.lean
- \+ *theorem* map_comap_of_surjective
- \+ *theorem* mem_image_of_mem_map_of_surjective
- \+ *theorem* comap_map_of_surjective
- \+ *def* order_iso_of_surjective
- \+ *def* le_order_embedding_of_surjective
- \+ *def* lt_order_embedding_of_surjective



## [2018-12-20 08:12:52-05:00](https://github.com/leanprover-community/mathlib/commit/f7697ce)
feat(data/equiv/algebra): ring_equiv ([#533](https://github.com/leanprover-community/mathlib/pull/533))
#### Estimated changes
Modified data/equiv/algebra.lean



## [2018-12-20 08:12:00-05:00](https://github.com/leanprover-community/mathlib/commit/fc90e00)
feat(ring_theory/subring) various lemmas ([#532](https://github.com/leanprover-community/mathlib/pull/532))
new lemmas:
- is_ring_hom.is_subring_set_range
- ring.in_closure.rec_on
- ring.closure_mono
changed:
- ring.exists_list_of_mem_closure
#### Estimated changes
Modified ring_theory/subring.lean
- \+ *theorem* closure_mono



## [2018-12-20 08:10:59-05:00](https://github.com/leanprover-community/mathlib/commit/35ed7f4)
feat(data/int/basic) int.cast is ring hom ([#531](https://github.com/leanprover-community/mathlib/pull/531))
#### Estimated changes
Modified data/int/basic.lean



## [2018-12-20 04:57:06-05:00](https://github.com/leanprover-community/mathlib/commit/ddd1376)
fix(group_theory/coset): remove bad attributes
#### Estimated changes
Modified group_theory/coset.lean



## [2018-12-20 03:40:45-05:00](https://github.com/leanprover-community/mathlib/commit/caa2076)
feat(command): Add `#where` command, dumping environment info ([#489](https://github.com/leanprover-community/mathlib/pull/489))
The command tells you your current namespace (wherever you write it),
the current `include`s, and the current `variables` which have been
used at least once.
#### Estimated changes
Modified tactic/basic.lean

Created tactic/where.lean
- \+ *def* select_for_which
- \+ *def* inflate



## [2018-12-18 00:51:12-05:00](https://github.com/leanprover-community/mathlib/commit/293ba83)
feat(category_theory/examples/topological_spaces): limits and colimits ([#518](https://github.com/leanprover-community/mathlib/pull/518))
#### Estimated changes
Modified category_theory/category.lean

Modified category_theory/examples/topological_spaces.lean
- \+ *def* limit
- \+ *def* limit_is_limit
- \+ *def* colimit
- \+ *def* colimit_is_colimit

Modified category_theory/limits/limits.lean
- \+ *def* of_faithful
- \+ *def* of_faithful

Modified category_theory/types.lean



## [2018-12-18 00:48:52-05:00](https://github.com/leanprover-community/mathlib/commit/3d4297b)
feat(category_theory/eq_to_hom): equality of functors; more simp lemmas ([#526](https://github.com/leanprover-community/mathlib/pull/526))
#### Estimated changes
Created category_theory/eq_to_hom.lean
- \+ *lemma* eq_to_hom_refl
- \+ *lemma* eq_to_hom_trans
- \+ *lemma* eq_to_hom_trans_assoc
- \+ *lemma* eq_to_iso.hom
- \+ *lemma* eq_to_iso_refl
- \+ *lemma* eq_to_iso_trans
- \+ *lemma* ext
- \+ *lemma* congr_obj
- \+ *lemma* congr_hom
- \+ *lemma* eq_to_hom_map
- \+ *lemma* eq_to_iso_map
- \+ *lemma* eq_to_hom_app
- \+ *def* eq_to_hom
- \+ *def* eq_to_iso

Modified category_theory/examples/topological_spaces.lean

Modified category_theory/isomorphism.lean
- \- *lemma* eq_to_hom_refl
- \- *lemma* eq_to_hom_trans
- \- *lemma* eq_to_iso.hom
- \- *lemma* eq_to_iso_refl
- \- *lemma* eq_to_iso_trans
- \- *lemma* eq_to_iso
- \- *def* eq_to_hom
- \- *def* eq_to_iso



## [2018-12-18 00:45:47-05:00](https://github.com/leanprover-community/mathlib/commit/76a4b15)
feat(data/set/basic): make subtype_val_range a simp lemma ([#524](https://github.com/leanprover-community/mathlib/pull/524))
#### Estimated changes
Modified data/set/basic.lean
- \+/\- *lemma* subtype_val_range
- \+/\- *lemma* subtype_val_range



## [2018-12-17 15:19:10-05:00](https://github.com/leanprover-community/mathlib/commit/2bc9354)
feat(data/nat/enat): extended natural numbers ([#522](https://github.com/leanprover-community/mathlib/pull/522))
#### Estimated changes
Created data/nat/enat.lean
- \+ *lemma* coe_inj
- \+ *lemma* top_add
- \+ *lemma* add_top
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_add_get
- \+ *lemma* get_add
- \+ *lemma* coe_get
- \+ *lemma* get_zero
- \+ *lemma* get_one
- \+ *lemma* dom_of_le_some
- \+ *lemma* coe_le_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* get_le_get
- \+ *lemma* coe_lt_top
- \+ *lemma* pos_iff_one_le
- \+ *lemma* sup_eq_max
- \+ *lemma* inf_eq_min
- \+ *def* enat

Modified data/pfun.lean
- \+ *lemma* some_inj
- \+ *lemma* some_get
- \+ *lemma* get_eq_iff_eq_some
- \+ *lemma* get_or_else_none
- \+ *lemma* get_or_else_some
- \+ *theorem* get_some
- \+ *def* get_or_else



## [2018-12-17 15:10:48-05:00](https://github.com/leanprover-community/mathlib/commit/418c116)
feat(data/polynomial): degree_map ([#517](https://github.com/leanprover-community/mathlib/pull/517))
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* prod_hom
- \+ *lemma* sum_hom
- \+/\- *lemma* prod_hom

Modified algebra/group.lean
- \+ *lemma* to_is_monoid_hom
- \+ *lemma* inv.is_group_hom

Modified algebra/group_power.lean

Modified algebra/module.lean

Modified algebra/pi_instances.lean
- \+ *lemma* fst.is_monoid_hom
- \+ *lemma* snd.is_monoid_hom
- \+ *lemma* fst.is_group_hom
- \+ *lemma* snd.is_group_hom

Modified analysis/topology/infinite_sum.lean

Modified data/complex/basic.lean

Modified data/complex/exponential.lean

Modified data/dfinsupp.lean

Modified data/finsupp.lean

Modified data/multiset.lean

Modified data/nat/cast.lean

Modified data/polynomial.lean
- \+/\- *lemma* coeff_sum
- \+ *lemma* coeff_map
- \+ *lemma* degree_map_le
- \+ *lemma* degree_map_eq
- \+/\- *lemma* coeff_sum

Modified data/real/ennreal.lean

Modified data/real/nnreal.lean

Modified data/zmod/quadratic_reciprocity.lean

Modified linear_algebra/basic.lean

Modified linear_algebra/direct_sum_module.lean



## [2018-12-17 14:47:05-05:00](https://github.com/leanprover-community/mathlib/commit/d947a3a)
refactor(analysis/topology/continuity): use subtype.val_injective ([#525](https://github.com/leanprover-community/mathlib/pull/525))
#### Estimated changes
Modified analysis/topology/continuity.lean



## [2018-12-17 12:40:24-05:00](https://github.com/leanprover-community/mathlib/commit/21ce531)
fix(data/list): fix build
#### Estimated changes
Modified data/equiv/list.lean

Modified data/list/sigma.lean
- \+/\- *theorem* nodupkeys_nil
- \+/\- *theorem* nodupkeys_nil



## [2018-12-17 12:35:03-05:00](https://github.com/leanprover-community/mathlib/commit/b405158)
feat(tactic/explode): improve readability & support proofs using 'suffices' ([#516](https://github.com/leanprover-community/mathlib/pull/516))
* improve readability & support proofs using 'suffices'
* feat(tactic/explode): improve readability & support proofs using 'suffices'
#### Estimated changes
Modified tactic/explode.lean



## [2018-12-17 11:35:44-05:00](https://github.com/leanprover-community/mathlib/commit/a4b699c)
feat(order/basic): antisymm_of_asymm
#### Estimated changes
Modified order/basic.lean
- \+ *def* antisymm_of_asymm



## [2018-12-17 11:35:42-05:00](https://github.com/leanprover-community/mathlib/commit/ebf3008)
feat(tactic/elide): hide subterms of complicated expressions
#### Estimated changes
Modified docs/tactics.md

Modified logic/basic.lean
- \+ *def* hidden

Modified tactic/basic.lean

Created tactic/elide.lean

Modified tactic/interactive.lean



## [2018-12-17 11:35:41-05:00](https://github.com/leanprover-community/mathlib/commit/b7d74c4)
feat(data/list): list.chain' for empty chains
#### Estimated changes
Modified data/list/basic.lean
- \+/\- *theorem* chain.iff_mem
- \+ *theorem* chain'.imp
- \+ *theorem* chain'.iff
- \+ *theorem* chain'.iff_mem
- \+ *theorem* chain'_singleton
- \+ *theorem* chain'_split
- \+ *theorem* chain'_map
- \+ *theorem* chain'_of_chain'_map
- \+ *theorem* chain'_map_of_chain'
- \+ *theorem* chain'_of_pairwise
- \+ *theorem* chain'_iff_pairwise
- \+/\- *theorem* nodup_nil
- \+/\- *theorem* chain.iff_mem
- \+/\- *theorem* nodup_nil

Modified data/list/defs.lean
- \+ *def* chain'

Modified data/list/sort.lean
- \+/\- *theorem* sorted_nil
- \+/\- *theorem* sorted_nil

Modified data/multiset.lean
- \+/\- *theorem* nodup_zero
- \+/\- *theorem* nodup_zero



## [2018-12-17 11:01:50-05:00](https://github.com/leanprover-community/mathlib/commit/e9be5c1)
fix(category/traversable/instances): fix build
#### Estimated changes
Modified category/traversable/instances.lean



## [2018-12-17 10:50:58-05:00](https://github.com/leanprover-community/mathlib/commit/53b08c1)
fix(*): untangle dependency hierarchy
#### Estimated changes
Modified algebra/group.lean

Modified category/traversable/basic.lean

Modified category/traversable/instances.lean

Deleted core/data/list.lean
- \- *def* partition_map

Deleted core/default.lean

Modified data/equiv/basic.lean

Modified data/list/basic.lean

Modified data/list/defs.lean
- \+ *def* partition_map

Modified data/nat/basic.lean

Renamed data/option.lean to data/option/basic.lean
- \+/\- *theorem* guard_eq_some'
- \- *theorem* mem_def
- \- *theorem* some_inj
- \- *theorem* is_none_iff_eq_none
- \- *theorem* iget_some
- \+/\- *theorem* guard_eq_some'
- \- *theorem* mem_to_list
- \- *def* iget
- \- *def* guard
- \- *def* filter
- \- *def* to_list
- \- *def* lift_or_get

Created data/option/defs.lean
- \+ *theorem* mem_def
- \+ *theorem* is_none_iff_eq_none
- \+ *theorem* some_inj
- \+ *theorem* iget_some
- \+ *theorem* mem_to_list
- \+ *def* iget
- \+ *def* guard
- \+ *def* filter
- \+ *def* to_list
- \+ *def* lift_or_get

Modified data/pfun.lean

Modified data/prod.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext

Modified logic/embedding.lean

Modified logic/function.lean

Modified meta/rb_map.lean

Modified order/bounded_lattice.lean

Modified tactic/auto_cases.lean

Modified tactic/chain.lean

Modified tactic/ext.lean

Modified tactic/interactive.lean

Modified tactic/pi_instances.lean

Created tactic/simpa.lean

Modified tactic/squeeze.lean



## [2018-12-17 09:19:16-05:00](https://github.com/leanprover-community/mathlib/commit/3ee1071)
feat(data/polynomial): lemmas relating unit and irreducible with degree ([#514](https://github.com/leanprover-community/mathlib/pull/514))
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* coe_one

Modified algebra/ordered_ring.lean

Modified data/nat/basic.lean
- \+ *lemma* one_lt_iff_ne_zero_and_ne_one
- \+ *lemma* with_bot.add_eq_zero_iff
- \+ *lemma* with_bot.add_eq_one_iff

Modified data/nat/prime.lean
- \+ *lemma* prime.ne_one

Modified data/polynomial.lean
- \+ *lemma* coeff_X_zero
- \+ *lemma* coeff_zero_eq_eval_zero
- \+ *lemma* nat_degree_eq_of_degree_eq_some
- \+ *lemma* monic_X
- \+ *lemma* zero_le_degree_iff
- \+ *lemma* coeff_mul_X_zero
- \+ *lemma* mod_by_monic_one
- \+ *lemma* div_by_monic_one
- \+ *lemma* X_ne_zero
- \+ *lemma* mod_by_monic_X
- \+ *lemma* nat_degree_mul_eq
- \+ *lemma* degree_eq_zero_of_is_unit
- \+ *lemma* is_unit_iff_degree_eq_zero
- \+ *lemma* degree_pos_of_ne_zero_of_nonunit
- \+ *lemma* irreducible_of_degree_eq_one

Modified data/zmod/quadratic_reciprocity.lean
- \+/\- *lemma* wilsons_lemma
- \+/\- *lemma* prod_range_prime_erase_zero
- \+/\- *lemma* prod_range_p_mul_q_filter_coprime_mod_p
- \+/\- *lemma* legendre_sym_eq_pow
- \+/\- *lemma* legendre_sym_eq_one_or_neg_one
- \+/\- *lemma* wilsons_lemma
- \+/\- *lemma* prod_range_prime_erase_zero
- \+/\- *lemma* prod_range_p_mul_q_filter_coprime_mod_p
- \+/\- *lemma* legendre_sym_eq_pow
- \+/\- *lemma* legendre_sym_eq_one_or_neg_one
- \+/\- *theorem* fermat_little
- \+/\- *theorem* quadratic_reciprocity
- \+/\- *theorem* fermat_little
- \+/\- *theorem* quadratic_reciprocity
- \+/\- *def* legendre_sym
- \+/\- *def* legendre_sym

Modified ring_theory/associated.lean
- \+ *lemma* is_unit_pow
- \+ *lemma* not_prime_one
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int
- \+ *lemma* irreducible_of_prime
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *lemma* mk_one
- \+ *lemma* mk_pow
- \+ *theorem* is_unit_int



## [2018-12-17 09:15:28-05:00](https://github.com/leanprover-community/mathlib/commit/d4d05e3)
feat(docs/extras/tactic_writing): Tactic writing tutorial ([#513](https://github.com/leanprover-community/mathlib/pull/513))
#### Estimated changes
Modified docs/extras.md

Created docs/extras/tactic_writing.md



## [2018-12-17 09:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/e6065a7)
chore(tactic/interactive): make squeeze_simp available by default ([#521](https://github.com/leanprover-community/mathlib/pull/521))
#### Estimated changes
Modified tactic/interactive.lean



## [2018-12-17 09:08:53-05:00](https://github.com/leanprover-community/mathlib/commit/b140a07)
chore(category_theory/limits/limits): Add missing lemmas ([#520](https://github.com/leanprover-community/mathlib/pull/520))
#### Estimated changes
Modified category_theory/limits/limits.lean
- \+ *lemma* limit.map_pre'
- \+ *lemma* limit.id_pre
- \+ *lemma* colimit.pre_map'
- \+ *lemma* colimit.pre_id



## [2018-12-17 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/218fe1f)
feat(category_theory/opposites): opposites of full and faithful functors ([#504](https://github.com/leanprover-community/mathlib/pull/504))
#### Estimated changes
Modified category_theory/opposites.lean
- \+ *lemma* preimage_id



## [2018-12-15 12:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/9506e6c)
feat(category_theory): functoriality of (co)cones ([#507](https://github.com/leanprover-community/mathlib/pull/507))
#### Estimated changes
Modified category_theory/limits/cones.lean
- \+ *lemma* cones_obj
- \+ *lemma* cones_map
- \+ *lemma* cocones_obj
- \+ *lemma* cocones_map
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* cones
- \+/\- *def* cocones
- \+/\- *def* cones
- \+/\- *def* cocones

Modified category_theory/limits/limits.lean
- \+ *def* lim_yoneda
- \+ *def* colim_coyoneda

Modified category_theory/opposites.lean
- \+ *lemma* op_id_app
- \+ *lemma* op_comp_app



## [2018-12-15 12:32:06-05:00](https://github.com/leanprover-community/mathlib/commit/072e1ba)
feat(category_theory/const): Constant functor of object from punit ([#508](https://github.com/leanprover-community/mathlib/pull/508))
#### Estimated changes
Modified category_theory/punit.lean
- \+ *lemma* obj_obj
- \+ *lemma* obj_map
- \+ *lemma* map_app
- \- *lemma* of_obj_obj
- \+ *def* of
- \- *def* of_obj



## [2018-12-15 12:31:24-05:00](https://github.com/leanprover-community/mathlib/commit/b1d0501)
fix(analysis/topology/topological_space): Improve the lattice structure on opens ([#511](https://github.com/leanprover-community/mathlib/pull/511))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* gi_choice_val



## [2018-12-15 12:18:12-05:00](https://github.com/leanprover-community/mathlib/commit/1f72be1)
feat(category_theory/whiskering): simp-lemmas for unitors and associators ([#505](https://github.com/leanprover-community/mathlib/pull/505))
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *lemma* left_unitor_hom_app
- \+ *lemma* left_unitor_inv_app
- \+ *lemma* right_unitor_hom_app
- \+ *lemma* right_unitor_inv_app
- \+ *lemma* associator_hom_app
- \+ *lemma* associator_inv_app



## [2018-12-15 12:17:49-05:00](https://github.com/leanprover-community/mathlib/commit/28909a8)
feat(category_theory/commas): add simp-lemmas for comma categories ([#503](https://github.com/leanprover-community/mathlib/pull/503))
#### Estimated changes
Modified category_theory/comma.lean
- \+ *lemma* comp_left
- \+ *lemma* comp_right
- \+ *lemma* map_left_obj_left
- \+ *lemma* map_left_obj_right
- \+ *lemma* map_left_obj_hom
- \+ *lemma* map_left_map_left
- \+ *lemma* map_left_map_right
- \+ *lemma* map_left_id_hom_app_left
- \+ *lemma* map_left_id_hom_app_right
- \+ *lemma* map_left_id_inv_app_left
- \+ *lemma* map_left_id_inv_app_right
- \+ *lemma* map_left_comp_hom_app_left
- \+ *lemma* map_left_comp_hom_app_right
- \+ *lemma* map_left_comp_inv_app_left
- \+ *lemma* map_left_comp_inv_app_right
- \+ *lemma* map_right_obj_left
- \+ *lemma* map_right_obj_right
- \+ *lemma* map_right_obj_hom
- \+ *lemma* map_right_map_left
- \+ *lemma* map_right_map_right
- \+ *lemma* map_right_id_hom_app_left
- \+ *lemma* map_right_id_hom_app_right
- \+ *lemma* map_right_id_inv_app_left
- \+ *lemma* map_right_id_inv_app_right
- \+ *lemma* map_right_comp_hom_app_left
- \+ *lemma* map_right_comp_hom_app_right
- \+ *lemma* map_right_comp_inv_app_left
- \+ *lemma* map_right_comp_inv_app_right
- \+ *def* map_left_id
- \+ *def* map_left_comp
- \+ *def* map_right_id
- \+ *def* map_right_comp



## [2018-12-10 17:44:27-05:00](https://github.com/leanprover-community/mathlib/commit/3ddfc23)
fix(order/basic): define preorder.lift lt by restriction
This makes it definitionally equal to `inv_image (<) f`, which appears
for example in the type of `inv_image.wf`.
#### Estimated changes
Modified order/basic.lean



## [2018-12-05 12:45:33-05:00](https://github.com/leanprover-community/mathlib/commit/257fd84)
doc(data/list/basic): improve docstrings [ci-skip]
#### Estimated changes
Modified data/list/defs.lean



## [2018-12-05 08:55:27-05:00](https://github.com/leanprover-community/mathlib/commit/b0d47ea)
refactor(set_theory/ordinal): minor simplifications
#### Estimated changes
Modified set_theory/ordinal.lean
- \+/\- *theorem* antisymm.aux
- \+/\- *theorem* enum_lt
- \+/\- *theorem* antisymm.aux
- \+/\- *theorem* enum_lt



## [2018-12-05 08:54:06-05:00](https://github.com/leanprover-community/mathlib/commit/843a1c3)
fix(tactic/norm_num): uninstantiated mvars can confuse things
#### Estimated changes
Modified tactic/norm_num.lean



## [2018-12-05 08:42:51-05:00](https://github.com/leanprover-community/mathlib/commit/94d9ac1)
fix(finset): removing bad simp lemmas ([#491](https://github.com/leanprover-community/mathlib/pull/491))
#### Estimated changes
Modified algebra/big_operators.lean

Modified analysis/limits.lean

Modified analysis/measure_theory/outer_measure.lean

Modified data/finset.lean
- \+/\- *theorem* insert.comm
- \+ *theorem* range_one
- \+/\- *theorem* range_succ
- \+/\- *theorem* insert.comm
- \+/\- *theorem* range_succ

Modified data/nat/choose.lean

Modified data/zmod/quadratic_reciprocity.lean

Modified group_theory/order_of_element.lean



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/5856459)
fix(category_theory/limits): add subsingleton instances in preserves.lean
#### Estimated changes
Modified category_theory/limits/preserves.lean



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/af6ee09)
fix(category_theory/limits): adding Type annotations in preserves.lean
#### Estimated changes
Modified category_theory/limits/preserves.lean
- \+/\- *def* preserves_limits_of_shape
- \+/\- *def* preserves_colimits_of_shape
- \+/\- *def* preserves_limits
- \+/\- *def* preserves_colimits
- \+/\- *def* reflects_limits_of_shape
- \+/\- *def* reflects_colimits_of_shape
- \+/\- *def* reflects_limits
- \+/\- *def* reflects_colimits
- \+/\- *def* preserves_limits_of_shape
- \+/\- *def* preserves_colimits_of_shape
- \+/\- *def* preserves_limits
- \+/\- *def* preserves_colimits
- \+/\- *def* reflects_limits_of_shape
- \+/\- *def* reflects_colimits_of_shape
- \+/\- *def* reflects_limits
- \+/\- *def* reflects_colimits



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/74b65e2)
fix(category_theory/limits): change argument order on
cones.precompose/whisker
#### Estimated changes
Modified category_theory/limits/cones.lean
- \+/\- *def* postcompose
- \+/\- *def* whisker
- \+/\- *def* precompose
- \+/\- *def* whisker
- \+/\- *def* postcompose
- \+/\- *def* whisker
- \+/\- *def* precompose
- \+/\- *def* whisker



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/4b0a82c)
feat(category_theory): preservation of (co)limits, (co)limits in functor categories
#### Estimated changes
Created category_theory/limits/functor_category.lean
- \+ *lemma* cone.functor_w
- \+ *lemma* cocone.functor_w
- \+ *def* functor_category_limit_cone
- \+ *def* functor_category_colimit_cocone
- \+ *def* evaluate_functor_category_limit_cone
- \+ *def* evaluate_functor_category_colimit_cocone
- \+ *def* functor_category_is_limit_cone
- \+ *def* functor_category_is_colimit_cocone

Created category_theory/limits/preserves.lean
- \+ *def* preserves_limits_of_shape
- \+ *def* preserves_colimits_of_shape
- \+ *def* preserves_limits
- \+ *def* preserves_colimits
- \+ *def* preserves_limit_of_preserves_limit_cone
- \+ *def* preserves_colimit_of_preserves_colimit_cocone
- \+ *def* reflects_limits_of_shape
- \+ *def* reflects_colimits_of_shape
- \+ *def* reflects_limits
- \+ *def* reflects_colimits

Modified category_theory/natural_transformation.lean
- \+ *lemma* congr_app



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/6267717)
fix(category_theory/limits): namespaces for is_(co)limit
#### Estimated changes
Modified category_theory/limits/cones.lean

Modified category_theory/limits/limits.lean
- \+ *lemma* uniq_cone_morphism
- \+ *lemma* hom_lift
- \+ *lemma* hom_ext
- \+ *lemma* hom_iso_hom
- \+ *lemma* uniq_cocone_morphism
- \+ *lemma* hom_desc
- \+ *lemma* hom_ext
- \+ *lemma* hom_iso_hom
- \- *lemma* is_limit.uniq_cone_morphism
- \- *lemma* is_limit.hom_lift
- \- *lemma* is_limit.hom_ext
- \- *lemma* is_limit.hom_iso_hom
- \- *lemma* is_colimit.uniq_cocone_morphism
- \- *lemma* is_colimit.hom_desc
- \- *lemma* is_colimit.hom_ext
- \- *lemma* is_colimit.hom_iso_hom
- \+ *def* lift_cone_morphism
- \+ *def* mk_cone_morphism
- \+ *def* unique
- \+ *def* of_iso_limit
- \+ *def* hom_iso
- \+ *def* nat_iso
- \+ *def* hom_iso'
- \+ *def* desc_cocone_morphism
- \+ *def* mk_cocone_morphism
- \+ *def* unique
- \+ *def* of_iso_colimit
- \+ *def* hom_iso
- \+ *def* nat_iso
- \+ *def* hom_iso'
- \- *def* is_limit.lift_cone_morphism
- \- *def* is_limit.mk_cone_morphism
- \- *def* is_limit.unique
- \- *def* is_limit.of_iso_limit
- \- *def* is_limit.hom_iso
- \- *def* is_limit.nat_iso
- \- *def* is_limit.hom_iso'
- \- *def* is_colimit.desc_cocone_morphism
- \- *def* is_colimit.mk_cocone_morphism
- \- *def* is_colimit.unique
- \- *def* is_colimit.of_iso_colimit
- \- *def* is_colimit.hom_iso
- \- *def* is_colimit.nat_iso
- \- *def* is_colimit.hom_iso'



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/de4f689)
feat(category_theory/limits): (co)limits, and (co)limits in Type
#### Estimated changes
Created category_theory/limits/limits.lean
- \+ *lemma* is_limit.uniq_cone_morphism
- \+ *lemma* is_limit.hom_lift
- \+ *lemma* is_limit.hom_ext
- \+ *lemma* is_limit.hom_iso_hom
- \+ *lemma* is_colimit.uniq_cocone_morphism
- \+ *lemma* is_colimit.hom_desc
- \+ *lemma* is_colimit.hom_ext
- \+ *lemma* is_colimit.hom_iso_hom
- \+ *lemma* limit.cone_π
- \+ *lemma* limit.w
- \+ *lemma* limit.is_limit_lift
- \+ *lemma* limit.lift_π
- \+ *lemma* limit.cone_morphism_hom
- \+ *lemma* limit.cone_morphism_π
- \+ *lemma* limit.hom_ext
- \+ *lemma* limit.hom_iso_hom
- \+ *lemma* limit.pre_π
- \+ *lemma* limit.lift_pre
- \+ *lemma* limit.pre_pre
- \+ *lemma* limit.post_π
- \+ *lemma* limit.lift_post
- \+ *lemma* limit.post_post
- \+ *lemma* limit.pre_post
- \+ *lemma* lim.map_π
- \+ *lemma* limit.lift_map
- \+ *lemma* limit.map_pre
- \+ *lemma* limit.map_post
- \+ *lemma* colimit.cocone_ι
- \+ *lemma* colimit.w
- \+ *lemma* colimit.is_colimit_desc
- \+ *lemma* colimit.ι_desc
- \+ *lemma* colimit.cocone_morphism_hom
- \+ *lemma* colimit.ι_cocone_morphism
- \+ *lemma* colimit.hom_ext
- \+ *lemma* colimit.hom_iso_hom
- \+ *lemma* colimit.ι_pre
- \+ *lemma* colimit.pre_desc
- \+ *lemma* colimit.pre_pre
- \+ *lemma* colimit.ι_post
- \+ *lemma* colimit.post_desc
- \+ *lemma* colimit.post_post
- \+ *lemma* colimit.pre_post
- \+ *lemma* colim.ι_map
- \+ *lemma* colimit.map_desc
- \+ *lemma* colimit.pre_map
- \+ *lemma* colimit.map_post
- \+ *def* is_limit.lift_cone_morphism
- \+ *def* is_limit.mk_cone_morphism
- \+ *def* is_limit.unique
- \+ *def* is_limit.of_iso_limit
- \+ *def* is_limit.hom_iso
- \+ *def* is_limit.nat_iso
- \+ *def* is_limit.hom_iso'
- \+ *def* is_colimit.desc_cocone_morphism
- \+ *def* is_colimit.mk_cocone_morphism
- \+ *def* is_colimit.unique
- \+ *def* is_colimit.of_iso_colimit
- \+ *def* is_colimit.hom_iso
- \+ *def* is_colimit.nat_iso
- \+ *def* is_colimit.hom_iso'
- \+ *def* has_limits_of_shape
- \+ *def* has_limits
- \+ *def* limit.cone
- \+ *def* limit
- \+ *def* limit.π
- \+ *def* limit.is_limit
- \+ *def* limit.lift
- \+ *def* limit.cone_morphism
- \+ *def* limit.hom_iso
- \+ *def* limit.hom_iso'
- \+ *def* limit.pre
- \+ *def* limit.post
- \+ *def* lim
- \+ *def* has_colimits_of_shape
- \+ *def* has_colimits
- \+ *def* colimit.cocone
- \+ *def* colimit
- \+ *def* colimit.ι
- \+ *def* colimit.is_colimit
- \+ *def* colimit.desc
- \+ *def* colimit.cocone_morphism
- \+ *def* colimit.hom_iso
- \+ *def* colimit.hom_iso'
- \+ *def* colimit.pre
- \+ *def* colimit.post
- \+ *def* colim

Created category_theory/limits/types.lean
- \+ *lemma* types_limit
- \+ *lemma* types_limit_π
- \+ *lemma* types_limit_pre
- \+ *lemma* types_limit_map
- \+ *lemma* types_limit_lift
- \+ *lemma* types_colimit
- \+ *lemma* types_colimit_ι
- \+ *lemma* types_colimit_pre
- \+ *lemma* types_colimit_map
- \+ *lemma* types_colimit_desc
- \+ *def* limit
- \+ *def* limit_is_limit
- \+ *def* colimit
- \+ *def* colimit_is_colimit



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/a5e2ebe)
feat(category_theory/limits/cones): (co)cones on a diagram
#### Estimated changes
Created category_theory/limits/cones.lean
- \+ *lemma* cones_obj
- \+ *lemma* cocones_obj
- \+ *lemma* cone.w
- \+ *lemma* cocone.w
- \+ *lemma* whisker_π_app
- \+ *lemma* whisker_ι_app
- \+ *lemma* cone_morphism.ext
- \+ *lemma* id.hom
- \+ *lemma* comp.hom
- \+ *lemma* cocone_morphism.ext
- \+ *lemma* id.hom
- \+ *lemma* comp.hom
- \+ *lemma* map_cone_π
- \+ *lemma* map_cocone_ι
- \+ *def* cones
- \+ *def* cocones
- \+ *def* extensions
- \+ *def* extend
- \+ *def* postcompose
- \+ *def* whisker
- \+ *def* extensions
- \+ *def* extend
- \+ *def* precompose
- \+ *def* whisker
- \+ *def* ext
- \+ *def* functoriality
- \+ *def* ext
- \+ *def* functoriality
- \+ *def* map_cone
- \+ *def* map_cocone
- \+ *def* map_cone_morphism
- \+ *def* map_cocone_morphism

Modified category_theory/natural_isomorphism.lean
- \- *def* id_comp
- \- *def* comp_id
- \- *def* assoc

Modified category_theory/yoneda.lean
- \+ *lemma* obj_obj
- \+ *lemma* obj_map
- \+ *lemma* map_app
- \+/\- *def* yoneda
- \+ *def* coyoneda
- \+/\- *def* yoneda



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/68c98eb)
feat(category_theory/isomorphism): lemmas for manipulating isomorphisms
#### Estimated changes
Modified category_theory/equivalence.lean

Modified category_theory/isomorphism.lean
- \+ *lemma* hom_inv_id_assoc
- \+ *lemma* inv_hom_id_assoc
- \+ *lemma* inv_comp_eq
- \+ *lemma* eq_inv_comp
- \+ *lemma* comp_inv_eq
- \+ *lemma* eq_comp_inv

Modified category_theory/natural_isomorphism.lean



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/382abaf)
feat(category_theory/const): constant functors
#### Estimated changes
Created category_theory/const.lean
- \+ *lemma* obj_obj
- \+ *lemma* obj_map
- \+ *lemma* map_app
- \+ *lemma* const_comp_hom_app
- \+ *lemma* const_comp_inv_app
- \+ *def* const
- \+ *def* const_comp



## [2018-12-02 06:41:58-05:00](https://github.com/leanprover-community/mathlib/commit/51afb41)
fix(category_theory/yoneda): add componentwise lemma ([#480](https://github.com/leanprover-community/mathlib/pull/480))
#### Estimated changes
Modified category_theory/types.lean
- \+ *lemma* ulift_functor.map
- \+ *def* ulift_trivial

Modified category_theory/yoneda.lean
- \+ *def* yoneda_sections
- \+ *def* yoneda_sections_small

