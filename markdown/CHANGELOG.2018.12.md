## [2018-12-28 02:49:24-05:00](https://github.com/leanprover-community/mathlib/commit/17d6263)
refactor(category_theory): minimize the amount of universe annotations in category_theory ([#552](https://github.com/leanprover-community/mathlib/pull/552))
#### Estimated changes
Modified category_theory/category.lean
- \+/\- *lemma* category_theory.category.assoc_symm
- \+/\- *abbreviation* category_theory.large_category
- \+/\- *abbreviation* category_theory.small_category

Modified category_theory/comma.lean


Modified category_theory/const.lean


Modified category_theory/discrete_category.lean


Modified category_theory/eq_to_hom.lean


Modified category_theory/equivalence.lean
- \+/\- *structure* category_theory.equivalence
- \+/\- *def* category_theory.functor.obj_preimage

Modified category_theory/examples/topological_spaces.lean


Modified category_theory/full_subcategory.lean


Modified category_theory/fully_faithful.lean


Modified category_theory/functor.lean
- \+/\- *structure* category_theory.functor

Modified category_theory/functor_category.lean


Modified category_theory/groupoid.lean
- \+/\- *abbreviation* category_theory.large_groupoid
- \+/\- *abbreviation* category_theory.small_groupoid

Modified category_theory/isomorphism.lean
- \+/\- *structure* category_theory.iso

Modified category_theory/limits/cones.lean


Modified category_theory/limits/functor_category.lean
- \+/\- *def* category_theory.limits.functor_category_is_colimit_cocone

Modified category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.map_post
- \+/\- *lemma* category_theory.limits.colimit.pre_map'
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+/\- *def* category_theory.limits.is_colimit.of_faithful
- \+/\- *def* category_theory.limits.is_limit.of_faithful
- \+/\- *lemma* category_theory.limits.limit.map_post
- \+/\- *lemma* category_theory.limits.limit.map_pre'
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified category_theory/limits/preserves.lean


Modified category_theory/limits/types.lean


Modified category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.functor.ulift_down_up
- \+/\- *def* category_theory.functor.ulift_up_down

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
- \+/\- *lemma* le_max_iff
- \+/\- *lemma* le_min_iff
- \+/\- *lemma* lt_max_iff
- \+/\- *lemma* lt_min_iff
- \+/\- *lemma* max_le_iff
- \+/\- *lemma* max_lt_iff
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* min_lt_iff

Modified algebra/ordered_group.lean
- \+ *lemma* with_top.add_lt_add_iff_right
- \+ *lemma* with_top.add_lt_top

Modified algebra/ordered_ring.lean
- \+ *lemma* with_top.mul_eq_top_iff

Modified data/finset.lean


Modified order/bounded_lattice.lean
- \+ *lemma* lattice.ne_bot_of_gt
- \+ *lemma* lattice.ne_top_of_lt

Modified order/lattice.lean
- \+ *lemma* lattice.lt_inf_iff
- \+ *lemma* lattice.sup_lt_iff



## [2018-12-24 20:12:21-05:00](https://github.com/leanprover-community/mathlib/commit/a04c7e2)
feat(analysis/topology): miscellaneous topology ([#484](https://github.com/leanprover-community/mathlib/pull/484))
* miscellaneous topology
* C is a proper metric space
* Sum of metric spaces is a def instead of instance
* refactor(analysis): shorten/simplify proofs
#### Estimated changes
Modified analysis/complex.lean
- \+ *def* complex.real_prod_homeo

Modified analysis/metric_space.lean
- \+ *lemma* closed_ball_Icc
- \+ *def* metric_space_sum
- \+ *lemma* prod.dist_eq
- \+ *lemma* sum.one_dist_le'
- \+ *lemma* sum.one_dist_le

Modified analysis/real.lean


Modified analysis/topology/continuity.lean
- \- *lemma* compact_of_closed
- \+ *lemma* compact_prod
- \- *lemma* compact_univ
- \+ *lemma* homeomorph.compact_image
- \+ *lemma* homeomorph.compact_preimage

Modified analysis/topology/topological_space.lean
- \+ *lemma* compact_Union_of_compact
- \+ *lemma* compact_of_closed
- \+ *lemma* compact_union_of_compact
- \+ *lemma* compact_univ

Modified analysis/topology/topological_structures.lean
- \+ *lemma* Inf_mem_closure
- \+ *lemma* Inf_mem_of_is_closed
- \+ *lemma* Inf_of_Inf_of_monotone_of_continuous
- \+ *lemma* Sup_mem_closure
- \+ *lemma* Sup_mem_of_is_closed
- \+ *lemma* Sup_of_Sup_of_monotone_of_continuous
- \+ *lemma* bdd_above_of_compact
- \+ *lemma* bdd_below_of_compact
- \+ *lemma* cInf_mem_closure
- \+ *lemma* cInf_mem_of_is_closed
- \+ *lemma* cInf_of_cInf_of_monotone_of_continuous
- \+ *lemma* cSup_mem_closure
- \+ *lemma* cSup_mem_of_is_closed
- \+ *lemma* cSup_of_cSup_of_monotone_of_continuous
- \+ *lemma* cinfi_of_cinfi_of_monotone_of_continuous
- \+ *lemma* csupr_of_csupr_of_monotone_of_continuous
- \+ *lemma* exists_forall_ge_of_compact_of_continuous
- \+ *lemma* exists_forall_le_of_compact_of_continuous
- \+ *lemma* infi_of_infi_of_monotone_of_continuous
- \+ *lemma* mem_closure_of_is_glb
- \+ *lemma* mem_closure_of_is_lub
- \+ *lemma* mem_of_is_glb_of_is_closed
- \+ *lemma* mem_of_is_lub_of_is_closed
- \+ *lemma* supr_of_supr_of_monotone_of_continuous

Modified analysis/topology/uniform_space.lean
- \+ *lemma* open_of_uniformity_sum_aux
- \+ *lemma* sum.uniformity
- \+ *def* uniform_space.core.sum
- \+ *lemma* uniformity_sum_of_open_aux
- \+ *lemma* union_mem_uniformity_sum

Modified data/complex/basic.lean
- \+ *def* complex.real_prod_equiv
- \+ *theorem* complex.real_prod_equiv_apply
- \+ *theorem* complex.real_prod_equiv_symm_im
- \+ *theorem* complex.real_prod_equiv_symm_re

Modified data/real/basic.lean


Modified data/real/nnreal.lean
- \- *lemma* set.image_eq_empty

Modified data/set/basic.lean
- \+ *lemma* set.exists_mem_of_nonempty
- \+ *lemma* set.image_eq_empty
- \+ *lemma* set.range_eq_empty
- \+ *lemma* set.univ_eq_empty_iff
- \+ *lemma* set.univ_ne_empty

Modified data/set/finite.lean
- \+ *theorem* set.finite_univ

Modified order/complete_lattice.lean
- \+ *def* lattice.has_Inf_to_nonempty
- \+ *def* lattice.has_Sup_to_nonempty

Modified order/conditionally_complete_lattice.lean
- \- *lemma* bdd_above_Int1
- \- *lemma* bdd_above_Int2
- \+/\- *lemma* bdd_above_empty
- \+/\- *lemma* bdd_above_finite
- \+/\- *lemma* bdd_above_finite_union
- \+ *lemma* bdd_above_inter_left
- \+ *lemma* bdd_above_inter_right
- \+ *lemma* bdd_above_of_bdd_above_of_monotone
- \- *lemma* bdd_below_Int1
- \- *lemma* bdd_below_Int2
- \+/\- *lemma* bdd_below_empty
- \+/\- *lemma* bdd_below_finite
- \+/\- *lemma* bdd_below_finite_union
- \+ *lemma* bdd_below_inter_left
- \+ *lemma* bdd_below_inter_right
- \+ *lemma* bdd_below_of_bdd_below_of_monotone
- \- *theorem* lattice.cInf_of_in_of_le
- \+ *theorem* lattice.cInf_of_mem_of_le
- \- *theorem* lattice.cSup_of_in_of_le
- \+ *theorem* lattice.cSup_of_mem_of_le
- \+ *lemma* lattice.cinfi_le
- \+ *lemma* lattice.cinfi_le_cinfi
- \+ *lemma* lattice.csupr_le
- \+ *lemma* lattice.csupr_le_csupr
- \+ *lemma* lattice.is_glb_cInf
- \+ *lemma* lattice.is_lub_cSup
- \+ *lemma* lattice.le_cinfi
- \+ *lemma* lattice.le_csupr



## [2018-12-22 01:10:55-05:00](https://github.com/leanprover-community/mathlib/commit/3eb7424)
refactor(data/set/basic): remove unused hypotheses in union_inter_cancel_* ([#551](https://github.com/leanprover-community/mathlib/pull/551))
#### Estimated changes
Modified analysis/measure_theory/outer_measure.lean


Modified data/set/basic.lean
- \+/\- *theorem* set.union_inter_cancel_left
- \+/\- *theorem* set.union_inter_cancel_right



## [2018-12-21 04:05:56-05:00](https://github.com/leanprover-community/mathlib/commit/cdab35d)
fix(category_theory/punit): fix regression ([#550](https://github.com/leanprover-community/mathlib/pull/550))
#### Estimated changes
Modified category_theory/punit.lean
- \+ *lemma* category_theory.functor.of.map_app
- \+ *lemma* category_theory.functor.of.obj_map
- \+ *lemma* category_theory.functor.of.obj_obj
- \+ *def* category_theory.functor.of



## [2018-12-21 03:12:01-05:00](https://github.com/leanprover-community/mathlib/commit/b11b83b)
feat(data/list/basic): rotate a list ([#542](https://github.com/leanprover-community/mathlib/pull/542))
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.drop_all
- \+ *lemma* list.drop_append_of_le_length
- \+ *lemma* list.length_rotate'
- \+ *lemma* list.length_rotate
- \+ *lemma* list.nth_append
- \+ *lemma* list.nth_concat_length:
- \+ *lemma* list.nth_le_append
- \+ *lemma* list.nth_le_repeat
- \+ *lemma* list.nth_le_singleton
- \+ *lemma* list.prod_rotate_eq_one_of_prod_eq_one
- \+ *lemma* list.rotate'_cons_succ
- \+ *lemma* list.rotate'_eq_take_append_drop
- \+ *lemma* list.rotate'_length
- \+ *lemma* list.rotate'_length_mul
- \+ *lemma* list.rotate'_mod
- \+ *lemma* list.rotate'_nil
- \+ *lemma* list.rotate'_rotate'
- \+ *lemma* list.rotate'_zero
- \+ *lemma* list.rotate_cons_succ
- \+ *lemma* list.rotate_eq_rotate'
- \+ *lemma* list.rotate_eq_take_append_drop
- \+ *lemma* list.rotate_length
- \+ *lemma* list.rotate_length_mul
- \+ *lemma* list.rotate_mod
- \+ *lemma* list.rotate_nil
- \+ *lemma* list.rotate_rotate
- \+ *lemma* list.rotate_zero
- \+/\- *theorem* list.take_all
- \+ *lemma* list.take_append_of_le_length

Modified data/list/defs.lean
- \+ *def* list.rotate'
- \+ *def* list.rotate

Modified data/nat/modeq.lean
- \+ *lemma* list.nth_rotate
- \+ *lemma* list.rotate_eq_self_iff_eq_repeat



## [2018-12-21 02:35:06-05:00](https://github.com/leanprover-community/mathlib/commit/d7cea06)
feat (ring_theory/noetherian) various lemmas ([#548](https://github.com/leanprover-community/mathlib/pull/548))
#### Estimated changes
Modified ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_of_fg_of_noetherian
- \+ *theorem* is_noetherian_of_linear_equiv
- \+ *theorem* is_noetherian_of_surjective
- \+ *theorem* is_noetherian_pi
- \+ *theorem* is_noetherian_prod
- \+ *theorem* is_noetherian_ring_of_ring_equiv
- \+ *theorem* is_noetherian_ring_of_surjective
- \+ *theorem* is_noetherian_submodule
- \+ *theorem* is_noetherian_submodule_left
- \+ *theorem* is_noetherian_submodule_right
- \+ *theorem* submodule.fg_bot
- \+ *theorem* submodule.fg_map
- \+ *theorem* submodule.fg_of_fg_map_of_fg_inf_ker
- \+ *theorem* submodule.fg_prod
- \+ *theorem* submodule.fg_sup



## [2018-12-20 23:14:00-05:00](https://github.com/leanprover-community/mathlib/commit/3762d96)
feat(ring_theory/ideals): lift for quotient rings ([#529](https://github.com/leanprover-community/mathlib/pull/529))
#### Estimated changes
Modified ring_theory/ideals.lean
- \+ *lemma* ideal.ext
- \+ *def* ideal.is_coprime
- \+ *theorem* ideal.is_coprime_def
- \+ *theorem* ideal.is_coprime_self
- \+ *theorem* ideal.mem_span_pair
- \+ *def* ideal.quotient.lift
- \+ *lemma* ideal.quotient.lift_mk



## [2018-12-20 23:12:51-05:00](https://github.com/leanprover-community/mathlib/commit/73933b7)
feat(category_theory): assorted small changes from the old limits PR ([#512](https://github.com/leanprover-community/mathlib/pull/512))
#### Estimated changes
Modified algebra/pi_instances.lean
- \+ *def* pi.is_ring_hom_pi

Modified category_theory/category.lean
- \+ *lemma* category_theory.bundled_hom_coe
- \+ *lemma* category_theory.category.assoc_symm

Added category_theory/discrete_category.lean
- \+ *lemma* category_theory.discrete.functor_map_id
- \+ *def* category_theory.discrete.lift
- \+ *def* category_theory.discrete
- \+ *def* category_theory.functor.of_function
- \+ *def* category_theory.nat_trans.of_function

Modified category_theory/examples/rings.lean
- \+/\- *def* category_theory.examples.CommRing.forget_to_CommMon
- \+ *lemma* category_theory.examples.CommRing_hom_coe_app
- \- *def* category_theory.examples.is_comm_ring_hom

Modified category_theory/examples/topological_spaces.lean
- \- *def* category_theory.examples.map
- \- *def* category_theory.examples.map_id
- \- *lemma* category_theory.examples.map_id_obj
- \- *def* category_theory.examples.map_iso
- \- *def* category_theory.examples.map_iso_id
- \+ *def* topological_space.opens.map
- \+ *def* topological_space.opens.map_id
- \+ *lemma* topological_space.opens.map_id_obj
- \+ *def* topological_space.opens.map_iso
- \+ *def* topological_space.opens.map_iso_id

Modified category_theory/functor.lean


Modified category_theory/functor_category.lean


Modified category_theory/limits/cones.lean


Modified category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colimit.desc_extend
- \+ *lemma* category_theory.limits.limit.lift_extend

Modified category_theory/opposites.lean


Modified category_theory/pempty.lean
- \+/\- *def* category_theory.functor.empty

Modified category_theory/punit.lean
- \- *lemma* category_theory.functor.of.map_app
- \- *lemma* category_theory.functor.of.obj_map
- \- *lemma* category_theory.functor.of.obj_obj
- \- *def* category_theory.functor.of

Added data/ulift.lean
- \+ *lemma* plift.rec.constant
- \+ *lemma* ulift.rec.constant

Modified tactic/ext.lean
- \+ *lemma* plift.ext



## [2018-12-20 09:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/1854dd9)
feat(group_theory/order_of_element): lemmas about card of subgroups and normalizer ([#545](https://github.com/leanprover-community/mathlib/pull/545))
#### Estimated changes
Modified group_theory/order_of_element.lean
- \+ *lemma* card_eq_card_quotient_mul_card_subgroup
- \+ *lemma* card_quotient_dvd_card
- \+ *lemma* card_subgroup_dvd_card
- \+ *lemma* card_trivial
- \+ *lemma* conj_inj
- \+ *lemma* mem_normalizer_fintype
- \+ *lemma* order_of_eq_one_iff
- \+ *lemma* order_of_one

Modified group_theory/subgroup.lean
- \+/\- *def* gmultiples
- \+/\- *def* gpowers
- \+ *def* is_subgroup.normalizer
- \+ *lemma* is_subgroup.subset_normalizer



## [2018-12-20 09:30:12-05:00](https://github.com/leanprover-community/mathlib/commit/95bdce8)
feat(data/set/finite): card_range_of_injective ([#543](https://github.com/leanprover-community/mathlib/pull/543))
#### Estimated changes
Modified data/set/finite.lean
- \+ *lemma* set.card_range_of_injective



## [2018-12-20 09:29:35-05:00](https://github.com/leanprover-community/mathlib/commit/0882f8e)
feat(data/fintype): exists_ne_of_card_gt_one ([#544](https://github.com/leanprover-community/mathlib/pull/544))
#### Estimated changes
Modified data/fintype.lean
- \+ *lemma* card_vector
- \+ *lemma* fintype.exists_ne_of_card_gt_one



## [2018-12-20 09:28:29-05:00](https://github.com/leanprover-community/mathlib/commit/4335380)
feat(data/vector2): vector_zero_subsingleton ([#547](https://github.com/leanprover-community/mathlib/pull/547))
#### Estimated changes
Modified data/vector2.lean




## [2018-12-20 08:15:19-05:00](https://github.com/leanprover-community/mathlib/commit/402e71e)
feat(order/filter): tendsto_at_top_at_top ([#540](https://github.com/leanprover-community/mathlib/pull/540))
#### Estimated changes
Modified order/filter.lean
- \+ *lemma* filter.tendsto_at_top_at_top



## [2018-12-20 08:14:46-05:00](https://github.com/leanprover-community/mathlib/commit/f64b9aa)
feat(data/finsupp): frange ([#537](https://github.com/leanprover-community/mathlib/pull/537))
#### Estimated changes
Modified data/finsupp.lean
- \+ *def* finsupp.frange
- \+ *theorem* finsupp.frange_single
- \+ *theorem* finsupp.mem_frange
- \+ *theorem* finsupp.zero_not_mem_frange



## [2018-12-20 08:13:39-05:00](https://github.com/leanprover-community/mathlib/commit/bc21f62)
feat(ring_theory/ideal_operations): correspondence under surjection ([#534](https://github.com/leanprover-community/mathlib/pull/534))
#### Estimated changes
Modified ring_theory/ideal_operations.lean
- \+ *theorem* ideal.comap_map_of_surjective
- \+ *def* ideal.le_order_embedding_of_surjective
- \+ *def* ideal.lt_order_embedding_of_surjective
- \+ *theorem* ideal.map_comap_of_surjective
- \+ *theorem* ideal.mem_image_of_mem_map_of_surjective
- \+ *def* ideal.order_iso_of_surjective



## [2018-12-20 08:12:52-05:00](https://github.com/leanprover-community/mathlib/commit/f7697ce)
feat(data/equiv/algebra): ring_equiv ([#533](https://github.com/leanprover-community/mathlib/pull/533))
#### Estimated changes
Modified data/equiv/algebra.lean
- \+ *structure* ring_equiv



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
- \+ *theorem* ring.closure_mono



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


Added tactic/where.lean
- \+ *def* where.inflate
- \+ *def* where.select_for_which



## [2018-12-18 00:51:12-05:00](https://github.com/leanprover-community/mathlib/commit/293ba83)
feat(category_theory/examples/topological_spaces): limits and colimits ([#518](https://github.com/leanprover-community/mathlib/pull/518))
#### Estimated changes
Modified category_theory/category.lean


Modified category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.Top.colimit
- \+ *def* category_theory.examples.Top.colimit_is_colimit
- \+ *def* category_theory.examples.Top.limit
- \+ *def* category_theory.examples.Top.limit_is_limit

Modified category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.of_faithful
- \+ *def* category_theory.limits.is_limit.of_faithful

Modified category_theory/types.lean




## [2018-12-18 00:48:52-05:00](https://github.com/leanprover-community/mathlib/commit/3d4297b)
feat(category_theory/eq_to_hom): equality of functors; more simp lemmas ([#526](https://github.com/leanprover-community/mathlib/pull/526))
#### Estimated changes
Added category_theory/eq_to_hom.lean
- \+ *def* category_theory.eq_to_hom
- \+ *lemma* category_theory.eq_to_hom_app
- \+ *lemma* category_theory.eq_to_hom_map
- \+ *lemma* category_theory.eq_to_hom_refl
- \+ *lemma* category_theory.eq_to_hom_trans
- \+ *lemma* category_theory.eq_to_hom_trans_assoc
- \+ *lemma* category_theory.eq_to_iso.hom
- \+ *def* category_theory.eq_to_iso
- \+ *lemma* category_theory.eq_to_iso_map
- \+ *lemma* category_theory.eq_to_iso_refl
- \+ *lemma* category_theory.eq_to_iso_trans
- \+ *lemma* category_theory.functor.congr_hom
- \+ *lemma* category_theory.functor.congr_obj
- \+ *lemma* category_theory.functor.ext

Modified category_theory/examples/topological_spaces.lean


Modified category_theory/isomorphism.lean
- \- *def* category_theory.eq_to_hom
- \- *lemma* category_theory.eq_to_hom_refl
- \- *lemma* category_theory.eq_to_hom_trans
- \- *lemma* category_theory.eq_to_iso.hom
- \- *def* category_theory.eq_to_iso
- \- *lemma* category_theory.eq_to_iso_refl
- \- *lemma* category_theory.eq_to_iso_trans
- \- *lemma* category_theory.functor.eq_to_iso



## [2018-12-18 00:45:47-05:00](https://github.com/leanprover-community/mathlib/commit/76a4b15)
feat(data/set/basic): make subtype_val_range a simp lemma ([#524](https://github.com/leanprover-community/mathlib/pull/524))
#### Estimated changes
Modified data/set/basic.lean
- \+/\- *lemma* set.subtype_val_range



## [2018-12-17 15:19:10-05:00](https://github.com/leanprover-community/mathlib/commit/2bc9354)
feat(data/nat/enat): extended natural numbers ([#522](https://github.com/leanprover-community/mathlib/pull/522))
#### Estimated changes
Added data/nat/enat.lean
- \+ *lemma* enat.add_top
- \+ *lemma* enat.coe_add
- \+ *lemma* enat.coe_add_get
- \+ *lemma* enat.coe_get
- \+ *lemma* enat.coe_inj
- \+ *lemma* enat.coe_le_coe
- \+ *lemma* enat.coe_lt_coe
- \+ *lemma* enat.coe_lt_top
- \+ *lemma* enat.coe_one
- \+ *lemma* enat.coe_zero
- \+ *lemma* enat.dom_of_le_some
- \+ *lemma* enat.get_add
- \+ *lemma* enat.get_le_get
- \+ *lemma* enat.get_one
- \+ *lemma* enat.get_zero
- \+ *lemma* enat.inf_eq_min
- \+ *lemma* enat.pos_iff_one_le
- \+ *lemma* enat.sup_eq_max
- \+ *lemma* enat.top_add
- \+ *def* enat

Modified data/pfun.lean
- \+ *lemma* roption.get_eq_iff_eq_some
- \+ *def* roption.get_or_else
- \+ *lemma* roption.get_or_else_none
- \+ *lemma* roption.get_or_else_some
- \+ *theorem* roption.get_some
- \+ *lemma* roption.some_get
- \+ *lemma* roption.some_inj



## [2018-12-17 15:10:48-05:00](https://github.com/leanprover-community/mathlib/commit/418c116)
feat(data/polynomial): degree_map ([#517](https://github.com/leanprover-community/mathlib/pull/517))
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_hom
- \+ *lemma* finset.sum_hom

Modified algebra/group.lean
- \+ *lemma* inv.is_group_hom
- \+ *lemma* is_group_hom.to_is_monoid_hom

Modified algebra/group_power.lean


Modified algebra/module.lean


Modified algebra/pi_instances.lean
- \+ *lemma* prod.fst.is_group_hom
- \+ *lemma* prod.fst.is_monoid_hom
- \+ *lemma* prod.snd.is_group_hom
- \+ *lemma* prod.snd.is_monoid_hom

Modified analysis/topology/infinite_sum.lean


Modified data/complex/basic.lean


Modified data/complex/exponential.lean


Modified data/dfinsupp.lean


Modified data/finsupp.lean


Modified data/multiset.lean


Modified data/nat/cast.lean


Modified data/polynomial.lean
- \+ *lemma* polynomial.coeff_map
- \+/\- *lemma* polynomial.coeff_sum
- \+ *lemma* polynomial.degree_map_eq
- \+ *lemma* polynomial.degree_map_le

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
- \+/\- *theorem* list.nodupkeys_nil



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


Added tactic/elide.lean


Modified tactic/interactive.lean




## [2018-12-17 11:35:41-05:00](https://github.com/leanprover-community/mathlib/commit/b7d74c4)
feat(data/list): list.chain' for empty chains
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.chain'.iff
- \+ *theorem* list.chain'.iff_mem
- \+ *theorem* list.chain'.imp
- \+ *theorem* list.chain'_iff_pairwise
- \+ *theorem* list.chain'_map
- \+ *theorem* list.chain'_map_of_chain'
- \+ *theorem* list.chain'_of_chain'_map
- \+ *theorem* list.chain'_of_pairwise
- \+ *theorem* list.chain'_singleton
- \+ *theorem* list.chain'_split
- \+/\- *theorem* list.chain.iff_mem
- \+/\- *theorem* list.nodup_nil

Modified data/list/defs.lean
- \+ *def* list.chain'

Modified data/list/sort.lean
- \+/\- *theorem* list.sorted_nil

Modified data/multiset.lean
- \+/\- *theorem* multiset.nodup_zero



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
- \- *def* list.partition_map

Deleted core/default.lean


Modified data/equiv/basic.lean


Modified data/list/basic.lean
- \- *inductive* list.forall₂

Modified data/list/defs.lean
- \+ *inductive* list.forall₂
- \+ *def* list.partition_map

Modified data/nat/basic.lean


Renamed data/option.lean to data/option/basic.lean
- \- *def* option.filter
- \- *def* option.guard
- \- *def* option.iget
- \- *theorem* option.iget_some
- \- *theorem* option.is_none_iff_eq_none
- \- *def* option.lift_or_get
- \- *theorem* option.mem_def
- \- *theorem* option.mem_to_list
- \- *inductive* option.rel
- \- *theorem* option.some_inj
- \- *def* option.to_list

Added data/option/defs.lean
- \+ *def* option.filter
- \+ *def* option.guard
- \+ *def* option.iget
- \+ *theorem* option.iget_some
- \+ *theorem* option.is_none_iff_eq_none
- \+ *def* option.lift_or_get
- \+ *theorem* option.mem_def
- \+ *theorem* option.mem_to_list
- \+ *inductive* option.rel
- \+ *theorem* option.some_inj
- \+ *def* option.to_list

Modified data/pfun.lean


Modified data/prod.lean
- \+/\- *lemma* prod.ext

Modified logic/embedding.lean


Modified logic/function.lean


Modified meta/rb_map.lean


Modified order/bounded_lattice.lean


Modified tactic/auto_cases.lean


Modified tactic/chain.lean


Modified tactic/ext.lean


Modified tactic/interactive.lean


Modified tactic/pi_instances.lean


Added tactic/simpa.lean


Modified tactic/squeeze.lean




## [2018-12-17 09:19:16-05:00](https://github.com/leanprover-community/mathlib/commit/3ee1071)
feat(data/polynomial): lemmas relating unit and irreducible with degree ([#514](https://github.com/leanprover-community/mathlib/pull/514))
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* with_bot.coe_one

Modified algebra/ordered_ring.lean


Modified data/nat/basic.lean
- \+ *lemma* nat.one_lt_iff_ne_zero_and_ne_one
- \+ *lemma* nat.with_bot.add_eq_one_iff
- \+ *lemma* nat.with_bot.add_eq_zero_iff

Modified data/nat/prime.lean
- \+ *lemma* nat.prime.ne_one

Modified data/polynomial.lean
- \+ *lemma* polynomial.X_ne_zero
- \+ *lemma* polynomial.coeff_X_zero
- \+ *lemma* polynomial.coeff_mul_X_zero
- \+ *lemma* polynomial.coeff_zero_eq_eval_zero
- \+ *lemma* polynomial.degree_eq_zero_of_is_unit
- \+ *lemma* polynomial.degree_pos_of_ne_zero_of_nonunit
- \+ *lemma* polynomial.div_by_monic_one
- \+ *lemma* polynomial.irreducible_of_degree_eq_one
- \+ *lemma* polynomial.is_unit_iff_degree_eq_zero
- \+ *lemma* polynomial.mod_by_monic_X
- \+ *lemma* polynomial.mod_by_monic_one
- \+ *lemma* polynomial.monic_X
- \+ *lemma* polynomial.nat_degree_eq_of_degree_eq_some
- \+ *lemma* polynomial.nat_degree_mul_eq
- \+ *lemma* polynomial.zero_le_degree_iff

Modified data/zmod/quadratic_reciprocity.lean
- \+/\- *lemma* quadratic_reciprocity_aux.prod_range_p_mul_q_filter_coprime_mod_p
- \+/\- *theorem* zmodp.fermat_little
- \+/\- *def* zmodp.legendre_sym
- \+/\- *lemma* zmodp.legendre_sym_eq_one_or_neg_one
- \+/\- *lemma* zmodp.legendre_sym_eq_pow
- \+/\- *lemma* zmodp.prod_range_prime_erase_zero
- \+/\- *theorem* zmodp.quadratic_reciprocity
- \+/\- *lemma* zmodp.wilsons_lemma

Modified ring_theory/associated.lean
- \+ *lemma* associates.mk_one
- \+ *lemma* associates.mk_pow
- \+ *lemma* irreducible_of_prime
- \+ *theorem* is_unit_int
- \+ *lemma* is_unit_pow
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int
- \+ *lemma* not_prime_one
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul



## [2018-12-17 09:15:28-05:00](https://github.com/leanprover-community/mathlib/commit/d4d05e3)
feat(docs/extras/tactic_writing): Tactic writing tutorial ([#513](https://github.com/leanprover-community/mathlib/pull/513))
#### Estimated changes
Modified docs/extras.md


Added docs/extras/tactic_writing.md




## [2018-12-17 09:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/e6065a7)
chore(tactic/interactive): make squeeze_simp available by default ([#521](https://github.com/leanprover-community/mathlib/pull/521))
#### Estimated changes
Modified tactic/interactive.lean




## [2018-12-17 09:08:53-05:00](https://github.com/leanprover-community/mathlib/commit/b140a07)
chore(category_theory/limits/limits): Add missing lemmas ([#520](https://github.com/leanprover-community/mathlib/pull/520))
#### Estimated changes
Modified category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colimit.pre_id
- \+ *lemma* category_theory.limits.colimit.pre_map'
- \+ *lemma* category_theory.limits.limit.id_pre
- \+ *lemma* category_theory.limits.limit.map_pre'



## [2018-12-17 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/218fe1f)
feat(category_theory/opposites): opposites of full and faithful functors ([#504](https://github.com/leanprover-community/mathlib/pull/504))
#### Estimated changes
Modified category_theory/opposites.lean
- \+ *lemma* category_theory.functor.preimage_id



## [2018-12-15 12:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/9506e6c)
feat(category_theory): functoriality of (co)cones ([#507](https://github.com/leanprover-community/mathlib/pull/507))
#### Estimated changes
Modified category_theory/limits/cones.lean
- \+ *def* category_theory.cocones
- \+ *lemma* category_theory.cocones_map
- \+ *lemma* category_theory.cocones_obj
- \+ *def* category_theory.cones
- \+ *lemma* category_theory.cones_map
- \+ *lemma* category_theory.cones_obj
- \+/\- *def* category_theory.functor.cocones
- \+/\- *def* category_theory.functor.cones

Modified category_theory/limits/limits.lean
- \+ *def* category_theory.limits.colim_coyoneda
- \+ *def* category_theory.limits.lim_yoneda

Modified category_theory/opposites.lean
- \+ *lemma* category_theory.functor.category.op_comp_app
- \+ *lemma* category_theory.functor.category.op_id_app



## [2018-12-15 12:32:06-05:00](https://github.com/leanprover-community/mathlib/commit/072e1ba)
feat(category_theory/const): Constant functor of object from punit ([#508](https://github.com/leanprover-community/mathlib/pull/508))
#### Estimated changes
Modified category_theory/punit.lean
- \+ *lemma* category_theory.functor.of.map_app
- \+ *lemma* category_theory.functor.of.obj_map
- \+ *lemma* category_theory.functor.of.obj_obj
- \+ *def* category_theory.functor.of
- \- *def* category_theory.functor.of_obj
- \- *lemma* category_theory.functor.of_obj_obj



## [2018-12-15 12:31:24-05:00](https://github.com/leanprover-community/mathlib/commit/b1d0501)
fix(analysis/topology/topological_space): Improve the lattice structure on opens ([#511](https://github.com/leanprover-community/mathlib/pull/511))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.opens.gi_choice_val



## [2018-12-15 12:18:12-05:00](https://github.com/leanprover-community/mathlib/commit/1f72be1)
feat(category_theory/whiskering): simp-lemmas for unitors and associators ([#505](https://github.com/leanprover-community/mathlib/pull/505))
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *lemma* category_theory.functor.associator_hom_app
- \+ *lemma* category_theory.functor.associator_inv_app
- \+ *lemma* category_theory.functor.left_unitor_hom_app
- \+ *lemma* category_theory.functor.left_unitor_inv_app
- \+ *lemma* category_theory.functor.right_unitor_hom_app
- \+ *lemma* category_theory.functor.right_unitor_inv_app



## [2018-12-15 12:17:49-05:00](https://github.com/leanprover-community/mathlib/commit/28909a8)
feat(category_theory/commas): add simp-lemmas for comma categories ([#503](https://github.com/leanprover-community/mathlib/pull/503))
#### Estimated changes
Modified category_theory/comma.lean
- \+ *lemma* category_theory.comma.comp_left
- \+ *lemma* category_theory.comma.comp_right
- \+ *def* category_theory.comma.map_left_comp
- \+ *lemma* category_theory.comma.map_left_comp_hom_app_left
- \+ *lemma* category_theory.comma.map_left_comp_hom_app_right
- \+ *lemma* category_theory.comma.map_left_comp_inv_app_left
- \+ *lemma* category_theory.comma.map_left_comp_inv_app_right
- \+ *def* category_theory.comma.map_left_id
- \+ *lemma* category_theory.comma.map_left_id_hom_app_left
- \+ *lemma* category_theory.comma.map_left_id_hom_app_right
- \+ *lemma* category_theory.comma.map_left_id_inv_app_left
- \+ *lemma* category_theory.comma.map_left_id_inv_app_right
- \+ *lemma* category_theory.comma.map_left_map_left
- \+ *lemma* category_theory.comma.map_left_map_right
- \+ *lemma* category_theory.comma.map_left_obj_hom
- \+ *lemma* category_theory.comma.map_left_obj_left
- \+ *lemma* category_theory.comma.map_left_obj_right
- \+ *def* category_theory.comma.map_right_comp
- \+ *lemma* category_theory.comma.map_right_comp_hom_app_left
- \+ *lemma* category_theory.comma.map_right_comp_hom_app_right
- \+ *lemma* category_theory.comma.map_right_comp_inv_app_left
- \+ *lemma* category_theory.comma.map_right_comp_inv_app_right
- \+ *def* category_theory.comma.map_right_id
- \+ *lemma* category_theory.comma.map_right_id_hom_app_left
- \+ *lemma* category_theory.comma.map_right_id_hom_app_right
- \+ *lemma* category_theory.comma.map_right_id_inv_app_left
- \+ *lemma* category_theory.comma.map_right_id_inv_app_right
- \+ *lemma* category_theory.comma.map_right_map_left
- \+ *lemma* category_theory.comma.map_right_map_right
- \+ *lemma* category_theory.comma.map_right_obj_hom
- \+ *lemma* category_theory.comma.map_right_obj_left
- \+ *lemma* category_theory.comma.map_right_obj_right



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
- \+/\- *theorem* initial_seg.antisymm.aux
- \+/\- *theorem* ordinal.enum_lt



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
- \+/\- *theorem* finset.insert.comm
- \+ *theorem* finset.range_one
- \+/\- *theorem* finset.range_succ

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
- \+/\- *def* category_theory.limits.preserves_colimits
- \+/\- *def* category_theory.limits.preserves_colimits_of_shape
- \+/\- *def* category_theory.limits.preserves_limits
- \+/\- *def* category_theory.limits.preserves_limits_of_shape
- \+/\- *def* category_theory.limits.reflects_colimits
- \+/\- *def* category_theory.limits.reflects_colimits_of_shape
- \+/\- *def* category_theory.limits.reflects_limits
- \+/\- *def* category_theory.limits.reflects_limits_of_shape



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/74b65e2)
fix(category_theory/limits): change argument order on
cones.precompose/whisker
#### Estimated changes
Modified category_theory/limits/cones.lean
- \+/\- *def* category_theory.limits.cocone.precompose
- \+/\- *def* category_theory.limits.cocone.whisker
- \+/\- *def* category_theory.limits.cone.postcompose
- \+/\- *def* category_theory.limits.cone.whisker



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/4b0a82c)
feat(category_theory): preservation of (co)limits, (co)limits in functor categories
#### Estimated changes
Added category_theory/limits/functor_category.lean
- \+ *lemma* category_theory.limits.cocone.functor_w
- \+ *lemma* category_theory.limits.cone.functor_w
- \+ *def* category_theory.limits.evaluate_functor_category_colimit_cocone
- \+ *def* category_theory.limits.evaluate_functor_category_limit_cone
- \+ *def* category_theory.limits.functor_category_colimit_cocone
- \+ *def* category_theory.limits.functor_category_is_colimit_cocone
- \+ *def* category_theory.limits.functor_category_is_limit_cone
- \+ *def* category_theory.limits.functor_category_limit_cone

Added category_theory/limits/preserves.lean
- \+ *def* category_theory.limits.preserves_colimit_of_preserves_colimit_cocone
- \+ *def* category_theory.limits.preserves_colimits
- \+ *def* category_theory.limits.preserves_colimits_of_shape
- \+ *def* category_theory.limits.preserves_limit_of_preserves_limit_cone
- \+ *def* category_theory.limits.preserves_limits
- \+ *def* category_theory.limits.preserves_limits_of_shape
- \+ *def* category_theory.limits.reflects_colimits
- \+ *def* category_theory.limits.reflects_colimits_of_shape
- \+ *def* category_theory.limits.reflects_limits
- \+ *def* category_theory.limits.reflects_limits_of_shape

Modified category_theory/natural_transformation.lean
- \+ *lemma* category_theory.nat_trans.congr_app



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/6267717)
fix(category_theory/limits): namespaces for is_(co)limit
#### Estimated changes
Modified category_theory/limits/cones.lean


Modified category_theory/limits/limits.lean
- \+/\- *def* category_theory.limits.is_colimit.desc_cocone_morphism
- \+/\- *lemma* category_theory.limits.is_colimit.hom_desc
- \+/\- *lemma* category_theory.limits.is_colimit.hom_ext
- \+/\- *def* category_theory.limits.is_colimit.hom_iso'
- \+/\- *def* category_theory.limits.is_colimit.hom_iso
- \+/\- *lemma* category_theory.limits.is_colimit.hom_iso_hom
- \+/\- *def* category_theory.limits.is_colimit.mk_cocone_morphism
- \+/\- *def* category_theory.limits.is_colimit.nat_iso
- \+/\- *def* category_theory.limits.is_colimit.of_iso_colimit
- \+/\- *lemma* category_theory.limits.is_colimit.uniq_cocone_morphism
- \+/\- *def* category_theory.limits.is_colimit.unique
- \+/\- *lemma* category_theory.limits.is_limit.hom_ext
- \+/\- *def* category_theory.limits.is_limit.hom_iso'
- \+/\- *def* category_theory.limits.is_limit.hom_iso
- \+/\- *lemma* category_theory.limits.is_limit.hom_iso_hom
- \+/\- *lemma* category_theory.limits.is_limit.hom_lift
- \+/\- *def* category_theory.limits.is_limit.lift_cone_morphism
- \+/\- *def* category_theory.limits.is_limit.mk_cone_morphism
- \+/\- *def* category_theory.limits.is_limit.nat_iso
- \+/\- *def* category_theory.limits.is_limit.of_iso_limit
- \+/\- *lemma* category_theory.limits.is_limit.uniq_cone_morphism
- \+/\- *def* category_theory.limits.is_limit.unique



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/de4f689)
feat(category_theory/limits): (co)limits, and (co)limits in Type
#### Estimated changes
Added category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.colim.ι_map
- \+ *def* category_theory.limits.colim
- \+ *def* category_theory.limits.colimit.cocone
- \+ *def* category_theory.limits.colimit.cocone_morphism
- \+ *lemma* category_theory.limits.colimit.cocone_morphism_hom
- \+ *lemma* category_theory.limits.colimit.cocone_ι
- \+ *def* category_theory.limits.colimit.desc
- \+ *lemma* category_theory.limits.colimit.hom_ext
- \+ *def* category_theory.limits.colimit.hom_iso'
- \+ *def* category_theory.limits.colimit.hom_iso
- \+ *lemma* category_theory.limits.colimit.hom_iso_hom
- \+ *def* category_theory.limits.colimit.is_colimit
- \+ *lemma* category_theory.limits.colimit.is_colimit_desc
- \+ *lemma* category_theory.limits.colimit.map_desc
- \+ *lemma* category_theory.limits.colimit.map_post
- \+ *def* category_theory.limits.colimit.post
- \+ *lemma* category_theory.limits.colimit.post_desc
- \+ *lemma* category_theory.limits.colimit.post_post
- \+ *def* category_theory.limits.colimit.pre
- \+ *lemma* category_theory.limits.colimit.pre_desc
- \+ *lemma* category_theory.limits.colimit.pre_map
- \+ *lemma* category_theory.limits.colimit.pre_post
- \+ *lemma* category_theory.limits.colimit.pre_pre
- \+ *lemma* category_theory.limits.colimit.w
- \+ *def* category_theory.limits.colimit.ι
- \+ *lemma* category_theory.limits.colimit.ι_cocone_morphism
- \+ *lemma* category_theory.limits.colimit.ι_desc
- \+ *lemma* category_theory.limits.colimit.ι_post
- \+ *lemma* category_theory.limits.colimit.ι_pre
- \+ *def* category_theory.limits.colimit
- \+ *def* category_theory.limits.has_colimits
- \+ *def* category_theory.limits.has_colimits_of_shape
- \+ *def* category_theory.limits.has_limits
- \+ *def* category_theory.limits.has_limits_of_shape
- \+ *def* category_theory.limits.is_colimit.desc_cocone_morphism
- \+ *lemma* category_theory.limits.is_colimit.hom_desc
- \+ *lemma* category_theory.limits.is_colimit.hom_ext
- \+ *def* category_theory.limits.is_colimit.hom_iso'
- \+ *def* category_theory.limits.is_colimit.hom_iso
- \+ *lemma* category_theory.limits.is_colimit.hom_iso_hom
- \+ *def* category_theory.limits.is_colimit.mk_cocone_morphism
- \+ *def* category_theory.limits.is_colimit.nat_iso
- \+ *def* category_theory.limits.is_colimit.of_iso_colimit
- \+ *lemma* category_theory.limits.is_colimit.uniq_cocone_morphism
- \+ *def* category_theory.limits.is_colimit.unique
- \+ *structure* category_theory.limits.is_colimit
- \+ *lemma* category_theory.limits.is_limit.hom_ext
- \+ *def* category_theory.limits.is_limit.hom_iso'
- \+ *def* category_theory.limits.is_limit.hom_iso
- \+ *lemma* category_theory.limits.is_limit.hom_iso_hom
- \+ *lemma* category_theory.limits.is_limit.hom_lift
- \+ *def* category_theory.limits.is_limit.lift_cone_morphism
- \+ *def* category_theory.limits.is_limit.mk_cone_morphism
- \+ *def* category_theory.limits.is_limit.nat_iso
- \+ *def* category_theory.limits.is_limit.of_iso_limit
- \+ *lemma* category_theory.limits.is_limit.uniq_cone_morphism
- \+ *def* category_theory.limits.is_limit.unique
- \+ *structure* category_theory.limits.is_limit
- \+ *lemma* category_theory.limits.lim.map_π
- \+ *def* category_theory.limits.lim
- \+ *def* category_theory.limits.limit.cone
- \+ *def* category_theory.limits.limit.cone_morphism
- \+ *lemma* category_theory.limits.limit.cone_morphism_hom
- \+ *lemma* category_theory.limits.limit.cone_morphism_π
- \+ *lemma* category_theory.limits.limit.cone_π
- \+ *lemma* category_theory.limits.limit.hom_ext
- \+ *def* category_theory.limits.limit.hom_iso'
- \+ *def* category_theory.limits.limit.hom_iso
- \+ *lemma* category_theory.limits.limit.hom_iso_hom
- \+ *def* category_theory.limits.limit.is_limit
- \+ *lemma* category_theory.limits.limit.is_limit_lift
- \+ *def* category_theory.limits.limit.lift
- \+ *lemma* category_theory.limits.limit.lift_map
- \+ *lemma* category_theory.limits.limit.lift_post
- \+ *lemma* category_theory.limits.limit.lift_pre
- \+ *lemma* category_theory.limits.limit.lift_π
- \+ *lemma* category_theory.limits.limit.map_post
- \+ *lemma* category_theory.limits.limit.map_pre
- \+ *def* category_theory.limits.limit.post
- \+ *lemma* category_theory.limits.limit.post_post
- \+ *lemma* category_theory.limits.limit.post_π
- \+ *def* category_theory.limits.limit.pre
- \+ *lemma* category_theory.limits.limit.pre_post
- \+ *lemma* category_theory.limits.limit.pre_pre
- \+ *lemma* category_theory.limits.limit.pre_π
- \+ *lemma* category_theory.limits.limit.w
- \+ *def* category_theory.limits.limit.π
- \+ *def* category_theory.limits.limit

Added category_theory/limits/types.lean
- \+ *def* category_theory.limits.types.colimit
- \+ *def* category_theory.limits.types.colimit_is_colimit
- \+ *def* category_theory.limits.types.limit
- \+ *def* category_theory.limits.types.limit_is_limit
- \+ *lemma* category_theory.limits.types.types_colimit
- \+ *lemma* category_theory.limits.types.types_colimit_desc
- \+ *lemma* category_theory.limits.types.types_colimit_map
- \+ *lemma* category_theory.limits.types.types_colimit_pre
- \+ *lemma* category_theory.limits.types.types_colimit_ι
- \+ *lemma* category_theory.limits.types.types_limit
- \+ *lemma* category_theory.limits.types.types_limit_lift
- \+ *lemma* category_theory.limits.types.types_limit_map
- \+ *lemma* category_theory.limits.types.types_limit_pre
- \+ *lemma* category_theory.limits.types.types_limit_π



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/a5e2ebe)
feat(category_theory/limits/cones): (co)cones on a diagram
#### Estimated changes
Added category_theory/limits/cones.lean
- \+ *def* category_theory.functor.cocones
- \+ *lemma* category_theory.functor.cocones_obj
- \+ *def* category_theory.functor.cones
- \+ *lemma* category_theory.functor.cones_obj
- \+ *def* category_theory.functor.map_cocone
- \+ *def* category_theory.functor.map_cocone_morphism
- \+ *lemma* category_theory.functor.map_cocone_ι
- \+ *def* category_theory.functor.map_cone
- \+ *def* category_theory.functor.map_cone_morphism
- \+ *lemma* category_theory.functor.map_cone_π
- \+ *def* category_theory.limits.cocone.extend
- \+ *def* category_theory.limits.cocone.extensions
- \+ *def* category_theory.limits.cocone.precompose
- \+ *lemma* category_theory.limits.cocone.w
- \+ *def* category_theory.limits.cocone.whisker
- \+ *lemma* category_theory.limits.cocone.whisker_ι_app
- \+ *structure* category_theory.limits.cocone
- \+ *lemma* category_theory.limits.cocone_morphism.ext
- \+ *structure* category_theory.limits.cocone_morphism
- \+ *lemma* category_theory.limits.cocones.comp.hom
- \+ *def* category_theory.limits.cocones.ext
- \+ *def* category_theory.limits.cocones.functoriality
- \+ *lemma* category_theory.limits.cocones.id.hom
- \+ *def* category_theory.limits.cone.extend
- \+ *def* category_theory.limits.cone.extensions
- \+ *def* category_theory.limits.cone.postcompose
- \+ *lemma* category_theory.limits.cone.w
- \+ *def* category_theory.limits.cone.whisker
- \+ *lemma* category_theory.limits.cone.whisker_π_app
- \+ *structure* category_theory.limits.cone
- \+ *lemma* category_theory.limits.cone_morphism.ext
- \+ *structure* category_theory.limits.cone_morphism
- \+ *lemma* category_theory.limits.cones.comp.hom
- \+ *def* category_theory.limits.cones.ext
- \+ *def* category_theory.limits.cones.functoriality
- \+ *lemma* category_theory.limits.cones.id.hom

Modified category_theory/natural_isomorphism.lean
- \- *def* category_theory.functor.assoc
- \- *def* category_theory.functor.comp_id
- \- *def* category_theory.functor.id_comp

Modified category_theory/yoneda.lean
- \+ *lemma* category_theory.coyoneda.map_app
- \+ *lemma* category_theory.coyoneda.obj_map
- \+ *lemma* category_theory.coyoneda.obj_obj
- \+ *def* category_theory.coyoneda
- \+/\- *def* category_theory.yoneda



## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/68c98eb)
feat(category_theory/isomorphism): lemmas for manipulating isomorphisms
#### Estimated changes
Modified category_theory/equivalence.lean


Modified category_theory/isomorphism.lean
- \+ *lemma* category_theory.iso.comp_inv_eq
- \+ *lemma* category_theory.iso.eq_comp_inv
- \+ *lemma* category_theory.iso.eq_inv_comp
- \+ *lemma* category_theory.iso.hom_inv_id_assoc
- \+ *lemma* category_theory.iso.inv_comp_eq
- \+ *lemma* category_theory.iso.inv_hom_id_assoc

Modified category_theory/natural_isomorphism.lean




## [2018-12-02 17:36:23-05:00](https://github.com/leanprover-community/mathlib/commit/382abaf)
feat(category_theory/const): constant functors
#### Estimated changes
Added category_theory/const.lean
- \+ *lemma* category_theory.functor.const.map_app
- \+ *lemma* category_theory.functor.const.obj_map
- \+ *lemma* category_theory.functor.const.obj_obj
- \+ *def* category_theory.functor.const
- \+ *def* category_theory.functor.const_comp
- \+ *lemma* category_theory.functor.const_comp_hom_app
- \+ *lemma* category_theory.functor.const_comp_inv_app



## [2018-12-02 06:41:58-05:00](https://github.com/leanprover-community/mathlib/commit/51afb41)
fix(category_theory/yoneda): add componentwise lemma ([#480](https://github.com/leanprover-community/mathlib/pull/480))
#### Estimated changes
Modified category_theory/types.lean
- \+ *lemma* category_theory.ulift_functor.map
- \+ *def* category_theory.ulift_trivial

Modified category_theory/yoneda.lean
- \+ *def* category_theory.yoneda_sections
- \+ *def* category_theory.yoneda_sections_small

