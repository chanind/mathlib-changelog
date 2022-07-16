## [2017-09-28 19:28:00-04:00](https://github.com/leanprover-community/mathlib/commit/e7b2a0f)
style(analysis): renames the topology directory to analysis and introduced topology and measure_theory subdirectories
#### Estimated changes
Renamed topology/ennreal.lean to analysis/ennreal.lean


Renamed topology/limits.lean to analysis/limits.lean
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg

Renamed topology/borel_space.lean to analysis/measure_theory/borel_space.lean


Renamed topology/lebesgue_measure.lean to analysis/measure_theory/lebesgue_measure.lean


Renamed topology/measurable_space.lean to analysis/measure_theory/measurable_space.lean


Renamed topology/measure.lean to analysis/measure_theory/measure_space.lean


Renamed topology/outer_measure.lean to analysis/measure_theory/outer_measure.lean


Renamed topology/metric_space.lean to analysis/metric_space.lean


Renamed topology/of_nat.lean to analysis/of_nat.lean


Renamed topology/real.lean to analysis/real.lean


Renamed topology/continuity.lean to analysis/topology/continuity.lean


Renamed topology/infinite_sum.lean to analysis/topology/infinite_sum.lean
- \- *lemma* has_sum_of_absolute_convergence
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

Renamed topology/topological_space.lean to analysis/topology/topological_space.lean


Renamed topology/topological_structures.lean to analysis/topology/topological_structures.lean


Renamed topology/uniform_space.lean to analysis/topology/uniform_space.lean




## [2017-09-28 19:16:36-04:00](https://github.com/leanprover-community/mathlib/commit/afefdcb)
chore(topology): move general theorems to the corresponding theories
#### Estimated changes
Added algebra/default.lean


Modified algebra/field.lean
- \+ *lemma* inv_le_inv
- \+ *lemma* one_lt_inv

Modified algebra/ordered_group.lean
- \+ *lemma* lt_sub_iff
- \+ *lemma* sub_lt_iff

Modified algebra/ordered_ring.lean
- \+ *lemma* one_lt_two

Modified algebra/ring.lean
- \+ *lemma* add_div
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* neg_inv

Added data/quot.lean
- \+ *lemma* forall_quotient_iff
- \+ *lemma* quot_mk_image_univ_eq

Modified data/set/basic.lean
- \+ *lemma* set.image_preimage_eq_inter_rng

Added data/set/disjointed.lean
- \+ *def* pairwise
- \+ *lemma* set.disjoint_disjointed
- \+ *def* set.disjointed
- \+ *lemma* set.disjointed_Union
- \+ *lemma* set.disjointed_induct
- \+ *lemma* set.disjointed_of_mono

Modified data/set/lattice.lean
- \+ *lemma* subtype_val_image

Modified data/set/prod.lean
- \+ *lemma* set.univ_prod_univ

Added data/subtype.lean
- \+ *theorem* exists_subtype
- \+ *lemma* forall_subtype

Modified order/complete_lattice.lean
- \+ *lemma* lattice.binfi_inf
- \+ *lemma* lattice.infi_bool_eq
- \+ *lemma* lattice.supr_bool_eq

Modified order/filter.lean
- \+ *lemma* filter.at_top_ne_bot
- \+ *lemma* filter.inf_principal_eq_bot
- \+ *lemma* filter.map_at_top_eq
- \+ *lemma* filter.mem_at_top
- \+ *lemma* filter.mem_at_top_iff
- \+ *lemma* filter.mem_infi_sets_finset
- \+ *lemma* filter.tendsto_finset_image_at_top_at_top

Modified topology/borel_space.lean
- \+ *lemma* measure_theory.borel_eq_generate_from_Iio_of_rat
- \+ *lemma* measure_theory.borel_eq_generate_from_Ioo_of_rat_of_rat
- \+ *lemma* measure_theory.is_topological_basis_Ioo_of_rat_of_rat

Modified topology/continuity.lean
- \+ *lemma* continuous_if
- \- *lemma* image_preimage_eq_inter_rng
- \- *lemma* subtype.val_image
- \- *lemma* univ_prod_univ

Modified topology/ennreal.lean
- \- *lemma* supr_bool_eq

Modified topology/infinite_sum.lean
- \- *lemma* add_div
- \- *lemma* at_top_ne_bot
- \- *lemma* cauchy_iff
- \- *lemma* filter.mem_at_top
- \- *lemma* filter.mem_infi_sets_finset
- \- *theorem* forall_and_distrib'
- \- *lemma* map_at_top_eq
- \- *lemma* mem_at_top_iff
- \- *lemma* mem_closure_of_tendsto
- \- *lemma* tendsto_finset_image_at_top_at_top

Modified topology/lebesgue_measure.lean
- \- *lemma* borel_eq_generate_from_Iio_of_rat
- \- *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \- *lemma* inv_le_inv
- \- *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \- *lemma* is_topological_basis_of_open_of_nhds
- \- *lemma* max_of_rat_of_rat
- \- *lemma* min_of_rat_of_rat

Modified topology/limits.lean
- \- *lemma* div_eq_mul_inv
- \- *lemma* exists_lt_of_nat
- \- *lemma* int_of_nat_eq_of_nat
- \- *lemma* neg_inv
- \- *def* of_nat
- \- *lemma* of_nat_add
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_one
- \- *lemma* of_nat_pos
- \- *lemma* of_nat_sub
- \- *lemma* one_lt_inv
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* zero_le_of_nat

Modified topology/measurable_space.lean
- \- *def* pairwise
- \- *lemma* set.disjoint_disjointed
- \- *def* set.disjointed
- \- *lemma* set.disjointed_Union
- \- *lemma* set.disjointed_induct
- \- *lemma* set.disjointed_of_mono

Modified topology/metric_space.lean
- \- *theorem* exists_subtype

Added topology/of_nat.lean
- \+ *lemma* exists_lt_of_nat
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *def* of_nat
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_pos
- \+ *lemma* of_nat_sub
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* zero_le_of_nat

Modified topology/real.lean
- \- *lemma* forall_subtype_iff
- \- *lemma* lt_sub_iff
- \+ *lemma* max_of_rat_of_rat
- \+ *lemma* min_of_rat_of_rat
- \- *lemma* one_lt_two
- \- *lemma* orderable_topology_of_nhds_abs
- \- *lemma* quot_mk_image_univ_eq
- \- *lemma* sub_lt_iff

Modified topology/topological_space.lean
- \+ *lemma* closure_compl
- \+ *def* frontier
- \+ *lemma* frontier_eq_closure_inter_closure
- \+ *lemma* interior_compl
- \+ *lemma* mem_closure_of_tendsto
- \+ *lemma* topological_space.is_topological_basis_of_open_of_nhds

Modified topology/topological_structures.lean
- \- *lemma* binfi_inf
- \- *lemma* closure_compl
- \- *lemma* continuous_if
- \- *def* frontier
- \- *lemma* frontier_eq_closure_inter_closure
- \- *lemma* inf_principal_eq_bot
- \- *lemma* interior_compl
- \+ *lemma* orderable_topology_of_nhds_abs

Modified topology/uniform_space.lean
- \+ *lemma* cauchy_iff
- \- *lemma* forall_quotient_iff



## [2017-09-28 18:16:44-04:00](https://github.com/leanprover-community/mathlib/commit/7e7c6f5)
feat(topology): various additions (preparation for the nonnegative integral)
#### Estimated changes
Modified data/set/countable.lean


Modified data/set/finite.lean
- \+ *lemma* set.finite_prod

Modified data/set/prod.lean
- \+ *lemma* set.empty_prod
- \+ *lemma* set.insert_prod
- \+ *lemma* set.prod_empty
- \+ *lemma* set.prod_insert

Modified topology/borel_space.lean
- \+/\- *lemma* measure_theory.borel_prod
- \+/\- *lemma* measure_theory.measurable_add
- \+/\- *lemma* measure_theory.measurable_mul
- \+/\- *lemma* measure_theory.measurable_neg
- \+/\- *lemma* measure_theory.measurable_of_continuous2
- \+/\- *lemma* measure_theory.measurable_of_continuous
- \+/\- *lemma* measure_theory.measurable_sub

Modified topology/ennreal.lean


Modified topology/infinite_sum.lean
- \+ *lemma* tsum_eq_single



## [2017-09-28 18:08:23-04:00](https://github.com/leanprover-community/mathlib/commit/c3aeb53)
feat(topology): add Lebesgue measure
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* inv_lt_one

Modified data/rat.lean


Modified data/set/basic.lean
- \+ *lemma* set.range_eq_image

Modified data/set/countable.lean
- \+/\- *lemma* set.countable_Union
- \+ *lemma* set.countable_Union_Prop
- \+ *lemma* set.countable_bUnion

Modified data/set/default.lean


Added data/set/intervals.lean
- \+ *def* set.Ico
- \+ *lemma* set.Ico_eq_Ico_iff
- \+ *lemma* set.Ico_eq_empty
- \+ *lemma* set.Ico_eq_empty_iff
- \+ *lemma* set.Ico_inter_Iio_eq
- \+ *lemma* set.Ico_sdiff_Iio_eq
- \+ *lemma* set.Ico_subset_Ico_iff
- \+ *def* set.Iio
- \+ *def* set.Ioo
- \+ *lemma* set.Ioo_eq_empty_of_ge
- \+ *lemma* set.Ioo_inter_Ioo

Modified data/set/lattice.lean
- \+ *theorem* set.sdiff_inter_same
- \+ *theorem* set.sdiff_union_same
- \+ *lemma* set.subset.antisymm_iff
- \+ *lemma* set.union_of_subset_right

Modified logic/basic.lean
- \+ *lemma* classical.or_not

Modified order/bounds.lean
- \+ *lemma* ne_empty_of_is_glb
- \+ *lemma* ne_empty_of_is_lub

Modified order/complete_lattice.lean
- \+ *lemma* lattice.Inf_lt_iff
- \+ *lemma* lattice.Sup_eq_top
- \+ *lemma* lattice.infi_lt_iff
- \+ *lemma* lattice.lt_Sup_iff
- \+ *lemma* lattice.lt_supr_iff

Modified topology/borel_space.lean
- \+ *lemma* measure_theory.is_measurable_Ico
- \+ *lemma* measure_theory.is_measurable_Iio
- \+ *lemma* measure_theory.is_measurable_Ioo

Modified topology/continuity.lean
- \+ *lemma* prod_generate_from_generate_from_eq

Modified topology/ennreal.lean
- \- *lemma* Inf_lt_iff
- \- *lemma* Sup_eq_top
- \+ *lemma* ennreal.add_infi
- \+ *lemma* ennreal.add_sub_self
- \+ *lemma* ennreal.infi_add
- \+ *lemma* ennreal.infi_add_infi
- \+ *lemma* ennreal.infi_of_real
- \+ *lemma* ennreal.infi_sum
- \+ *lemma* ennreal.infty_sub_of_real
- \- *lemma* ennreal.le_sub_iff_add_le
- \+ *lemma* ennreal.of_real_le_of_real
- \+ *lemma* ennreal.of_real_sub_of_real
- \+ *lemma* ennreal.sub_supr
- \+ *lemma* ennreal.supr_of_real
- \- *lemma* infi_lt_iff
- \- *lemma* lt_Sup_iff
- \- *lemma* lt_supr_iff
- \+ *lemma* supr_bool_eq

Modified topology/lebesgue_measure.lean
- \- *def* Ico
- \- *lemma* Ico_eq_Ico_iff
- \- *lemma* Ico_eq_empty
- \- *lemma* Ico_eq_empty_iff
- \- *lemma* Ico_inter_Iio_eq
- \- *lemma* Ico_sdiff_Iio_eq
- \- *lemma* Ico_subset_Ico_iff
- \- *def* Iio
- \+ *lemma* borel_eq_generate_from_Iio_of_rat
- \+ *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \+ *lemma* inv_le_inv
- \- *lemma* is_lub_of_is_lub_of_tendsto
- \+ *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \+ *lemma* is_topological_basis_of_open_of_nhds
- \+ *lemma* max_of_rat_of_rat
- \+ *def* measure_theory.lebesgue
- \+ *lemma* measure_theory.lebesgue_Ico
- \+ *lemma* measure_theory.lebesgue_Ioo
- \+ *lemma* measure_theory.lebesgue_singleton
- \+ *lemma* measure_theory.tendsto_of_nat_at_top_at_top
- \+ *lemma* min_of_rat_of_rat
- \- *lemma* nhds_principal_ne_top_of_is_lub
- \- *lemma* set.subset.antisymm_iff

Modified topology/limits.lean
- \+ *lemma* of_nat_pos

Modified topology/measurable_space.lean
- \+ *lemma* is_measurable_set_prod
- \+ *lemma* measurable_fst
- \+ *lemma* measurable_prod
- \+ *lemma* measurable_prod_mk
- \+ *lemma* measurable_snd
- \+ *lemma* measurable_space.comap_generate_from
- \+ *lemma* measurable_space.generate_from_le_generate_from
- \+ *lemma* measurable_space.generate_from_sup_generate_from
- \+ *lemma* measurable_subtype_mk
- \+ *lemma* measurable_subtype_val
- \+ *lemma* set.disjointed_of_mono

Modified topology/measure.lean
- \+ *lemma* measure_theory.measure_Inter_eq_infi_nat
- \+ *lemma* measure_theory.measure_Union_eq_supr_nat
- \- *lemma* measure_theory.measure_Union_le_nat
- \+ *lemma* measure_theory.measure_Union_le_tsum_nat
- \+/\- *lemma* measure_theory.measure_empty
- \- *lemma* measure_theory.measure_eq_measure_of
- \+/\- *lemma* measure_theory.measure_mono
- \+ *lemma* measure_theory.measure_sdiff
- \- *def* measure_theory.measure_space.measure
- \+/\- *lemma* measure_theory.measure_union
- \+ *def* measure_theory.outer_measure.to_measure
- \- *lemma* supr_bool_eq

Modified topology/outer_measure.lean
- \- *lemma* classical.or_not
- \- *lemma* ennreal.add_infi
- \- *lemma* ennreal.infi_add
- \- *lemma* ennreal.infi_add_infi
- \- *lemma* ennreal.infi_sum
- \- *lemma* inv_lt_one
- \+ *lemma* measure_theory.outer_measure.caratheodory_is_measurable
- \+ *lemma* measure_theory.outer_measure.caratheodory_is_measurable_eq
- \- *def* measure_theory.outer_measure.inf
- \- *lemma* measure_theory.outer_measure.inf_space_is_measurable
- \- *def* measure_theory.outer_measure.measure
- \- *def* measure_theory.outer_measure.space
- \- *lemma* measure_theory.outer_measure.space_is_measurable_eq

Modified topology/real.lean
- \+ *lemma* exists_gt_of_rat
- \+ *lemma* exists_lt_of_rat_of_rat_gt

Modified topology/topological_space.lean
- \+ *lemma* induced_le_iff_le_coinduced
- \+ *def* topological_space.is_topological_basis
- \+ *lemma* topological_space.is_topological_basis_of_subbasis
- \+ *lemma* topological_space.mem_nhds_of_is_topological_basis

Modified topology/topological_structures.lean
- \+ *lemma* closure_compl
- \+ *lemma* closure_le_eq
- \+ *lemma* continuous_if
- \+ *lemma* continuous_max
- \+ *lemma* continuous_min
- \+ *lemma* continuous_sub'
- \+ *def* frontier
- \+ *lemma* frontier_eq_closure_inter_closure
- \+ *lemma* frontier_le_subset_eq
- \+ *lemma* interior_compl
- \+ *lemma* is_glb_of_is_glb_of_tendsto
- \+ *lemma* is_glb_of_is_lub_of_tendsto
- \+ *lemma* is_glb_of_mem_nhds
- \+ *lemma* is_lub_of_is_lub_of_tendsto
- \+ *lemma* is_lub_of_mem_nhds
- \+ *lemma* is_open_Iio
- \+ *lemma* is_open_Ioo
- \+ *lemma* nhds_principal_ne_bot_of_is_glb
- \+ *lemma* nhds_principal_ne_bot_of_is_lub
- \+ *lemma* tendsto_max
- \+ *lemma* tendsto_min



## [2017-09-28 18:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/4297eeb)
feat(topology): add Borel spaces
#### Estimated changes
Modified data/set/basic.lean
- \- *theorem* set.image_preimage_subset
- \- *lemma* set.image_subset_eq
- \- *theorem* set.image_union_supset
- \- *theorem* set.inter_preimage_subset
- \- *theorem* set.preimage_diff
- \- *theorem* set.subset_preimage_image
- \- *theorem* set.union_preimage_subset

Modified data/set/countable.lean
- \+/\- *lemma* set.countable_empty
- \+ *lemma* set.countable_set_of_finite_subset
- \+/\- *lemma* set.countable_singleton

Deleted data/set/function.lean
- \- *lemma* set.bij_on.mk
- \- *def* set.bij_on
- \- *theorem* set.bij_on_comp
- \- *theorem* set.bij_on_of_eq_on
- \- *theorem* set.bij_on_of_inv_on
- \- *lemma* set.bijective_iff_bij_on_univ
- \- *theorem* set.eq_on_of_left_inv_of_right_inv
- \- *lemma* set.image_eq_of_bij_on
- \- *lemma* set.image_eq_of_maps_to_of_surj_on
- \- *theorem* set.image_subset_of_maps_to
- \- *theorem* set.image_subset_of_maps_to_of_subset
- \- *def* set.inj_on
- \- *theorem* set.inj_on_comp
- \- *theorem* set.inj_on_empty
- \- *lemma* set.inj_on_of_bij_on
- \- *theorem* set.inj_on_of_eq_on
- \- *theorem* set.inj_on_of_inj_on_of_subset
- \- *theorem* set.inj_on_of_left_inv_on
- \- *lemma* set.injective_iff_inj_on_univ
- \- *def* set.inv_on
- \- *def* set.left_inv_on
- \- *theorem* set.left_inv_on_comp
- \- *theorem* set.left_inv_on_of_eq_on_left
- \- *theorem* set.left_inv_on_of_eq_on_right
- \- *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \- *def* set.maps_to
- \- *theorem* set.maps_to_comp
- \- *lemma* set.maps_to_of_bij_on
- \- *theorem* set.maps_to_of_eq_on
- \- *theorem* set.maps_to_univ_univ
- \- *def* set.right_inv_on
- \- *theorem* set.right_inv_on_comp
- \- *theorem* set.right_inv_on_of_eq_on_left
- \- *theorem* set.right_inv_on_of_eq_on_right
- \- *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \- *def* set.surj_on
- \- *theorem* set.surj_on_comp
- \- *lemma* set.surj_on_of_bij_on
- \- *theorem* set.surj_on_of_eq_on
- \- *theorem* set.surj_on_of_right_inv_on
- \- *lemma* set.surjective_iff_surj_on_univ

Modified data/set/lattice.lean
- \+ *lemma* bind_def
- \+ *def* disjoint
- \+ *theorem* disjoint_bot_left
- \+ *theorem* disjoint_bot_right
- \+ *theorem* disjoint_symm
- \+ *lemma* fmap_eq_image
- \+ *lemma* image_Union
- \+ *lemma* mem_seq_iff
- \+ *theorem* monotone_preimage
- \+ *theorem* preimage_Union
- \+ *theorem* preimage_sUnion
- \+ *lemma* set.Inter_neg
- \+ *lemma* set.Inter_pos
- \+ *lemma* set.Inter_univ
- \+ *lemma* set.Union_empty
- \+ *lemma* set.Union_neg
- \+ *lemma* set.Union_pos
- \- *lemma* set.bind_def
- \- *def* set.disjoint
- \- *theorem* set.disjoint_bot_left
- \- *theorem* set.disjoint_bot_right
- \- *theorem* set.disjoint_symm
- \- *lemma* set.fmap_eq_image
- \- *lemma* set.image_Union
- \- *lemma* set.mem_seq_iff
- \- *theorem* set.monotone_preimage
- \- *theorem* set.preimage_Union
- \- *theorem* set.preimage_sUnion
- \+ *lemma* set.sdiff_empty
- \+ *lemma* set.sdiff_eq:
- \+ *lemma* set.union_sdiff_left
- \+ *lemma* set.union_sdiff_right
- \- *lemma* set.univ_subtype
- \+ *lemma* univ_subtype

Modified order/complete_lattice.lean
- \+ *lemma* lattice.infi_neg
- \+ *lemma* lattice.infi_pos
- \+ *lemma* lattice.supr_neg
- \+ *lemma* lattice.supr_pos

Added topology/borel_space.lean
- \+ *lemma* measure_theory.borel_comap
- \+ *lemma* measure_theory.borel_eq_generate_from_of_subbasis
- \+ *lemma* measure_theory.borel_prod
- \+ *lemma* measure_theory.is_measurable_closure
- \+ *lemma* measure_theory.is_measurable_interior
- \+ *lemma* measure_theory.is_measurable_of_is_closed
- \+ *lemma* measure_theory.is_measurable_of_is_open
- \+ *lemma* measure_theory.measurable_add
- \+ *lemma* measure_theory.measurable_mul
- \+ *lemma* measure_theory.measurable_neg
- \+ *lemma* measure_theory.measurable_of_continuous2
- \+ *lemma* measure_theory.measurable_of_continuous
- \+ *lemma* measure_theory.measurable_sub

Modified topology/measurable_space.lean


Modified topology/outer_measure.lean
- \- *lemma* Inter_neg
- \- *lemma* Inter_pos
- \- *lemma* Inter_univ
- \- *lemma* Union_empty
- \- *lemma* Union_neg
- \- *lemma* Union_pos
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right

Modified topology/topological_space.lean
- \+ *lemma* is_open_sInter
- \+ *lemma* topological_space.is_open_generated_countable_inter

Modified topology/topological_structures.lean
- \- *lemma* infi_neg
- \- *lemma* infi_pos
- \- *lemma* supr_neg
- \- *lemma* supr_pos



## [2017-09-22 12:52:07-05:00](https://github.com/leanprover-community/mathlib/commit/865ba36)
feat(data/set): add functions over sets
#### Estimated changes
Modified data/set/basic.lean
- \+ *theorem* set.image_preimage_subset
- \+ *lemma* set.image_subset_eq
- \+ *theorem* set.image_union_supset
- \+ *theorem* set.inter_preimage_subset
- \+ *theorem* set.preimage_diff
- \+ *theorem* set.subset_preimage_image
- \+ *theorem* set.union_preimage_subset

Modified data/set/countable.lean
- \+/\- *lemma* set.countable_empty
- \- *lemma* set.countable_set_of_finite_subset
- \+/\- *lemma* set.countable_singleton

Added data/set/function.lean
- \+ *lemma* set.bij_on.mk
- \+ *def* set.bij_on
- \+ *theorem* set.bij_on_comp
- \+ *theorem* set.bij_on_of_eq_on
- \+ *theorem* set.bij_on_of_inv_on
- \+ *lemma* set.bijective_iff_bij_on_univ
- \+ *theorem* set.eq_on_of_left_inv_of_right_inv
- \+ *lemma* set.image_eq_of_bij_on
- \+ *lemma* set.image_eq_of_maps_to_of_surj_on
- \+ *theorem* set.image_subset_of_maps_to
- \+ *theorem* set.image_subset_of_maps_to_of_subset
- \+ *def* set.inj_on
- \+ *theorem* set.inj_on_comp
- \+ *theorem* set.inj_on_empty
- \+ *lemma* set.inj_on_of_bij_on
- \+ *theorem* set.inj_on_of_eq_on
- \+ *theorem* set.inj_on_of_inj_on_of_subset
- \+ *theorem* set.inj_on_of_left_inv_on
- \+ *lemma* set.injective_iff_inj_on_univ
- \+ *def* set.inv_on
- \+ *def* set.left_inv_on
- \+ *theorem* set.left_inv_on_comp
- \+ *theorem* set.left_inv_on_of_eq_on_left
- \+ *theorem* set.left_inv_on_of_eq_on_right
- \+ *theorem* set.left_inv_on_of_surj_on_right_inv_on
- \+ *def* set.maps_to
- \+ *theorem* set.maps_to_comp
- \+ *lemma* set.maps_to_of_bij_on
- \+ *theorem* set.maps_to_of_eq_on
- \+ *theorem* set.maps_to_univ_univ
- \+ *def* set.right_inv_on
- \+ *theorem* set.right_inv_on_comp
- \+ *theorem* set.right_inv_on_of_eq_on_left
- \+ *theorem* set.right_inv_on_of_eq_on_right
- \+ *theorem* set.right_inv_on_of_inj_on_of_left_inv_on
- \+ *def* set.surj_on
- \+ *theorem* set.surj_on_comp
- \+ *lemma* set.surj_on_of_bij_on
- \+ *theorem* set.surj_on_of_eq_on
- \+ *theorem* set.surj_on_of_right_inv_on
- \+ *lemma* set.surjective_iff_surj_on_univ

Modified data/set/lattice.lean
- \- *lemma* bind_def
- \- *def* disjoint
- \- *theorem* disjoint_bot_left
- \- *theorem* disjoint_bot_right
- \- *theorem* disjoint_symm
- \- *lemma* fmap_eq_image
- \- *lemma* image_Union
- \- *lemma* mem_seq_iff
- \- *theorem* monotone_preimage
- \- *theorem* preimage_Union
- \- *theorem* preimage_sUnion
- \- *lemma* set.Inter_neg
- \- *lemma* set.Inter_pos
- \- *lemma* set.Inter_univ
- \- *lemma* set.Union_empty
- \- *lemma* set.Union_neg
- \- *lemma* set.Union_pos
- \+ *lemma* set.bind_def
- \+ *def* set.disjoint
- \+ *theorem* set.disjoint_bot_left
- \+ *theorem* set.disjoint_bot_right
- \+ *theorem* set.disjoint_symm
- \+ *lemma* set.fmap_eq_image
- \+ *lemma* set.image_Union
- \+ *lemma* set.mem_seq_iff
- \+ *theorem* set.monotone_preimage
- \+ *theorem* set.preimage_Union
- \+ *theorem* set.preimage_sUnion
- \- *lemma* set.sdiff_empty
- \- *lemma* set.sdiff_eq:
- \- *lemma* set.union_sdiff_left
- \- *lemma* set.union_sdiff_right
- \+ *lemma* set.univ_subtype
- \- *lemma* univ_subtype

Modified order/complete_lattice.lean
- \- *lemma* lattice.infi_neg
- \- *lemma* lattice.infi_pos
- \- *lemma* lattice.supr_neg
- \- *lemma* lattice.supr_pos

Modified topology/measurable_space.lean


Modified topology/outer_measure.lean
- \+ *lemma* Inter_neg
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_univ
- \+ *lemma* Union_empty
- \+ *lemma* Union_neg
- \+ *lemma* Union_pos
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right

Modified topology/topological_space.lean
- \- *lemma* is_open_sInter
- \- *lemma* topological_space.is_open_generated_countable_inter

Modified topology/topological_structures.lean
- \+ *lemma* infi_neg
- \+ *lemma* infi_pos
- \+ *lemma* supr_neg
- \+ *lemma* supr_pos



## [2017-09-22 12:31:19-04:00](https://github.com/leanprover-community/mathlib/commit/e0abdab)
feat(topology/topological_space): add countablility and separability axioms for topological spaces
#### Estimated changes
Modified data/set/countable.lean
- \+/\- *lemma* set.countable_empty
- \+ *lemma* set.countable_set_of_finite_subset
- \+/\- *lemma* set.countable_singleton

Modified data/set/lattice.lean
- \+ *lemma* bind_def
- \+ *def* disjoint
- \+ *theorem* disjoint_bot_left
- \+ *theorem* disjoint_bot_right
- \+ *theorem* disjoint_symm
- \+ *lemma* fmap_eq_image
- \+ *lemma* image_Union
- \+ *lemma* mem_seq_iff
- \+ *theorem* monotone_preimage
- \+ *theorem* preimage_Union
- \+ *theorem* preimage_sUnion
- \+ *lemma* set.Inter_neg
- \+ *lemma* set.Inter_pos
- \+ *lemma* set.Inter_univ
- \+ *lemma* set.Union_empty
- \+ *lemma* set.Union_neg
- \+ *lemma* set.Union_pos
- \- *lemma* set.bind_def
- \- *def* set.disjoint
- \- *theorem* set.disjoint_bot_left
- \- *theorem* set.disjoint_bot_right
- \- *theorem* set.disjoint_symm
- \- *lemma* set.fmap_eq_image
- \- *lemma* set.image_Union
- \- *lemma* set.mem_seq_iff
- \- *theorem* set.monotone_preimage
- \- *theorem* set.preimage_Union
- \- *theorem* set.preimage_sUnion
- \+ *lemma* set.sdiff_empty
- \+ *lemma* set.sdiff_eq:
- \+ *lemma* set.union_sdiff_left
- \+ *lemma* set.union_sdiff_right
- \- *lemma* set.univ_subtype
- \+ *lemma* univ_subtype

Modified order/complete_lattice.lean
- \+ *lemma* lattice.infi_neg
- \+ *lemma* lattice.infi_pos
- \+ *lemma* lattice.supr_neg
- \+ *lemma* lattice.supr_pos

Modified topology/measurable_space.lean


Modified topology/outer_measure.lean
- \- *lemma* Inter_neg
- \- *lemma* Inter_pos
- \- *lemma* Inter_univ
- \- *lemma* Union_empty
- \- *lemma* Union_neg
- \- *lemma* Union_pos
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right

Modified topology/topological_space.lean
- \+ *lemma* is_open_sInter
- \+ *lemma* topological_space.is_open_generated_countable_inter

Modified topology/topological_structures.lean
- \- *lemma* infi_neg
- \- *lemma* infi_pos
- \- *lemma* supr_neg
- \- *lemma* supr_pos



## [2017-09-21 15:10:53-05:00](https://github.com/leanprover-community/mathlib/commit/d5e009f)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-09-21 13:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/5bb145e)
feat(topology/lebesgue_measure): add Lebesgue outer measure; show that the lower half open interval is measurable
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.abs_sum_le_sum_abs
- \+ *lemma* finset.prod_sdiff

Modified algebra/field.lean
- \+ *lemma* inv_pos

Modified algebra/group_power.lean
- \+ *theorem* inv_inv'
- \+ *theorem* inv_one
- \+/\- *theorem* pow_ge_one_of_ge_one
- \+ *theorem* pow_inv
- \+ *theorem* pow_le_pow
- \+ *theorem* pow_ne_zero
- \+ *theorem* pow_nonneg
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_succ'

Modified algebra/ordered_monoid.lean


Modified data/finset/basic.lean
- \+ *theorem* finset.exists_nat_subset_upto
- \+ *theorem* finset.not_mem_upto
- \+ *lemma* finset.sdiff_subset_sdiff
- \+/\- *theorem* finset.subset.refl
- \+ *theorem* finset.upto_subset_upto_iff
- \+/\- *theorem* finset.upto_succ
- \+/\- *theorem* finset.upto_zero
- \+ *lemma* lt_max_iff

Modified data/set/lattice.lean
- \+ *theorem* set.sdiff_subset_sdiff
- \+ *theorem* set.subset_Union

Modified order/boolean_algebra.lean
- \+ *theorem* lattice.sub_le_sub

Modified topology/ennreal.lean
- \+ *lemma* Inf_lt_iff
- \+ *lemma* ennreal.le_of_forall_epsilon_le
- \+ *lemma* ennreal.lt_add_right
- \+ *lemma* ennreal.sum_of_real
- \+ *lemma* ennreal.supr_add
- \+ *lemma* infi_lt_iff
- \- *lemma* inv_inv'
- \- *lemma* inv_pos

Modified topology/infinite_sum.lean
- \+ *lemma* add_div
- \+ *lemma* filter.mem_at_top
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \+ *lemma* tendsto_sum_nat_of_is_sum

Added topology/lebesgue_measure.lean
- \+ *def* Ico
- \+ *lemma* Ico_eq_Ico_iff
- \+ *lemma* Ico_eq_empty
- \+ *lemma* Ico_eq_empty_iff
- \+ *lemma* Ico_inter_Iio_eq
- \+ *lemma* Ico_sdiff_Iio_eq
- \+ *lemma* Ico_subset_Ico_iff
- \+ *def* Iio
- \+ *lemma* is_lub_of_is_lub_of_tendsto
- \+ *lemma* measure_theory.le_lebesgue_length
- \+ *def* measure_theory.lebesgue_length
- \+ *lemma* measure_theory.lebesgue_length_Ico
- \+ *lemma* measure_theory.lebesgue_length_Ico_le_lebesgue_length_Ico
- \+ *lemma* measure_theory.lebesgue_length_empty
- \+ *lemma* measure_theory.lebesgue_length_subadditive
- \+ *def* measure_theory.lebesgue_outer
- \+ *lemma* measure_theory.lebesgue_outer_Ico
- \+ *lemma* measure_theory.lebesgue_outer_is_measurable_Iio
- \+ *lemma* nhds_principal_ne_top_of_is_lub
- \+ *lemma* set.subset.antisymm_iff

Added topology/limits.lean
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* exists_lt_of_nat
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *lemma* is_sum_geometric
- \+ *lemma* map_succ_at_top_eq
- \+ *lemma* mul_add_one_le_pow
- \+ *lemma* neg_inv
- \+ *def* of_nat
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_sub
- \+ *lemma* one_lt_inv
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* sum_geometric'
- \+ *lemma* sum_geometric
- \+ *lemma* tendsto_comp_succ_at_top_iff
- \+ *lemma* tendsto_inverse_at_top_nhds_0
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* zero_le_of_nat

Modified topology/measure.lean


Modified topology/metric_space.lean
- \+ *theorem* mem_uniformity_dist

Added topology/outer_measure.lean
- \+ *lemma* Inter_neg
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_univ
- \+ *lemma* Union_empty
- \+ *lemma* Union_neg
- \+ *lemma* Union_pos
- \+ *lemma* classical.or_not
- \+ *lemma* ennreal.add_infi
- \+ *lemma* ennreal.infi_add
- \+ *lemma* ennreal.infi_add_infi
- \+ *lemma* ennreal.infi_sum
- \+ *lemma* inv_lt_one
- \+ *def* measure_theory.outer_measure.inf
- \+ *lemma* measure_theory.outer_measure.inf_space_is_measurable
- \+ *def* measure_theory.outer_measure.measure
- \+ *def* measure_theory.outer_measure.space
- \+ *lemma* measure_theory.outer_measure.space_is_measurable_eq
- \+ *lemma* measure_theory.outer_measure.subadditive
- \+ *structure* measure_theory.outer_measure
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right

Modified topology/real.lean
- \+/\- *lemma* one_lt_two



## [2017-09-21 10:33:23-05:00](https://github.com/leanprover-community/mathlib/commit/d9865ae)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* finset.abs_sum_le_sum_abs
- \- *lemma* finset.prod_sdiff

Modified algebra/field.lean
- \- *lemma* inv_pos

Modified algebra/group_power.lean
- \- *theorem* inv_inv'
- \- *theorem* inv_one
- \+/\- *theorem* pow_ge_one_of_ge_one
- \- *theorem* pow_inv
- \- *theorem* pow_le_pow
- \- *theorem* pow_ne_zero
- \- *theorem* pow_nonneg
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_succ'

Modified algebra/ordered_monoid.lean


Modified data/finset/basic.lean
- \- *theorem* finset.exists_nat_subset_upto
- \- *theorem* finset.not_mem_upto
- \- *lemma* finset.sdiff_subset_sdiff
- \+/\- *theorem* finset.subset.refl
- \- *theorem* finset.upto_subset_upto_iff
- \+/\- *theorem* finset.upto_succ
- \+/\- *theorem* finset.upto_zero
- \- *lemma* lt_max_iff

Modified data/set/lattice.lean
- \- *theorem* set.sdiff_subset_sdiff
- \- *theorem* set.subset_Union

Modified order/boolean_algebra.lean
- \- *theorem* lattice.sub_le_sub

Modified topology/ennreal.lean
- \- *lemma* Inf_lt_iff
- \- *lemma* ennreal.le_of_forall_epsilon_le
- \- *lemma* ennreal.lt_add_right
- \- *lemma* ennreal.sum_of_real
- \- *lemma* ennreal.supr_add
- \- *lemma* infi_lt_iff
- \+ *lemma* inv_inv'
- \+ *lemma* inv_pos

Modified topology/infinite_sum.lean
- \- *lemma* add_div
- \- *lemma* filter.mem_at_top
- \- *lemma* has_sum_of_absolute_convergence
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \- *lemma* tendsto_sum_nat_of_is_sum

Deleted topology/limits.lean
- \- *lemma* div_eq_mul_inv
- \- *lemma* exists_lt_of_nat
- \- *lemma* int_of_nat_eq_of_nat
- \- *lemma* is_sum_geometric
- \- *lemma* map_succ_at_top_eq
- \- *lemma* mul_add_one_le_pow
- \- *lemma* neg_inv
- \- *def* of_nat
- \- *lemma* of_nat_add
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_one
- \- *lemma* of_nat_sub
- \- *lemma* one_lt_inv
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* sum_geometric'
- \- *lemma* sum_geometric
- \- *lemma* tendsto_comp_succ_at_top_iff
- \- *lemma* tendsto_inverse_at_top_nhds_0
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* zero_le_of_nat

Modified topology/measure.lean


Modified topology/metric_space.lean
- \- *theorem* mem_uniformity_dist

Deleted topology/outer_measure.lean
- \- *lemma* Inter_neg
- \- *lemma* Inter_pos
- \- *lemma* Inter_univ
- \- *lemma* Union_empty
- \- *lemma* Union_neg
- \- *lemma* Union_pos
- \- *lemma* classical.or_not
- \- *lemma* ennreal.add_infi
- \- *lemma* ennreal.infi_add
- \- *lemma* ennreal.infi_add_infi
- \- *lemma* ennreal.infi_sum
- \- *lemma* inv_lt_one
- \- *def* measure_theory.outer_measure.inf
- \- *lemma* measure_theory.outer_measure.inf_space_is_measurable
- \- *def* measure_theory.outer_measure.measure
- \- *def* measure_theory.outer_measure.space
- \- *lemma* measure_theory.outer_measure.space_is_measurable_eq
- \- *lemma* measure_theory.outer_measure.subadditive
- \- *structure* measure_theory.outer_measure
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right

Modified topology/real.lean
- \+/\- *lemma* one_lt_two



## [2017-09-20 20:02:04-04:00](https://github.com/leanprover-community/mathlib/commit/4235594)
feat(topology/outer_measure): add outer measures and tools for Caratheodorys extension method
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* inv_pos

Modified algebra/ordered_monoid.lean


Modified data/finset/basic.lean
- \+/\- *theorem* finset.subset.refl
- \+/\- *theorem* finset.upto_succ
- \+/\- *theorem* finset.upto_zero
- \+ *lemma* lt_max_iff

Modified data/set/lattice.lean
- \+ *theorem* set.sdiff_subset_sdiff
- \+ *theorem* set.subset_Union

Modified order/boolean_algebra.lean
- \+ *theorem* lattice.sub_le_sub

Modified topology/ennreal.lean
- \+ *lemma* Inf_lt_iff
- \+ *lemma* ennreal.le_of_forall_epsilon_le
- \+ *lemma* ennreal.lt_add_right
- \+ *lemma* ennreal.sum_of_real
- \+ *lemma* ennreal.supr_add
- \+ *lemma* infi_lt_iff
- \- *lemma* inv_inv'
- \- *lemma* inv_pos

Modified topology/limits.lean
- \- *lemma* inv_pos

Modified topology/measure.lean


Added topology/outer_measure.lean
- \+ *lemma* Inter_neg
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_univ
- \+ *lemma* Union_empty
- \+ *lemma* Union_neg
- \+ *lemma* Union_pos
- \+ *lemma* classical.or_not
- \+ *lemma* ennreal.add_infi
- \+ *lemma* ennreal.infi_add
- \+ *lemma* ennreal.infi_add_infi
- \+ *lemma* ennreal.infi_sum
- \+ *lemma* inv_lt_one
- \+ *def* measure_theory.outer_measure.inf
- \+ *lemma* measure_theory.outer_measure.inf_space_is_measurable
- \+ *def* measure_theory.outer_measure.measure
- \+ *def* measure_theory.outer_measure.space
- \+ *lemma* measure_theory.outer_measure.space_is_measurable_eq
- \+ *lemma* measure_theory.outer_measure.subadditive
- \+ *structure* measure_theory.outer_measure
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right

Modified topology/real.lean
- \+/\- *lemma* one_lt_two



## [2017-09-20 18:29:06-04:00](https://github.com/leanprover-community/mathlib/commit/4698828)
feat(topology): prove geometric series
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.abs_sum_le_sum_abs
- \+ *lemma* finset.prod_sdiff

Modified algebra/group_power.lean
- \+ *theorem* inv_inv'
- \+ *theorem* inv_one
- \+/\- *theorem* pow_ge_one_of_ge_one
- \+ *theorem* pow_inv
- \+ *theorem* pow_le_pow
- \+ *theorem* pow_ne_zero
- \+ *theorem* pow_nonneg
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_succ'

Modified data/finset/basic.lean
- \+ *theorem* finset.exists_nat_subset_upto
- \+ *theorem* finset.not_mem_upto
- \+ *lemma* finset.sdiff_subset_sdiff
- \+ *theorem* finset.upto_subset_upto_iff

Modified topology/infinite_sum.lean
- \+ *lemma* add_div
- \+ *lemma* filter.mem_at_top
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \+ *lemma* tendsto_sum_nat_of_is_sum

Added topology/limits.lean
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* exists_lt_of_nat
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *lemma* inv_pos
- \+ *lemma* is_sum_geometric
- \+ *lemma* map_succ_at_top_eq
- \+ *lemma* mul_add_one_le_pow
- \+ *lemma* neg_inv
- \+ *def* of_nat
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_sub
- \+ *lemma* one_lt_inv
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* sum_geometric'
- \+ *lemma* sum_geometric
- \+ *lemma* tendsto_comp_succ_at_top_iff
- \+ *lemma* tendsto_inverse_at_top_nhds_0
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* zero_le_of_nat

Modified topology/metric_space.lean
- \+ *theorem* mem_uniformity_dist

Modified topology/real.lean




## [2017-09-19 02:55:14-04:00](https://github.com/leanprover-community/mathlib/commit/6b93e93)
refactor(data/equiv,encodable): refactor/simplify proofs
#### Estimated changes
Modified data/encodable.lean
- \+/\- *def* encodable.choose
- \+/\- *lemma* encodable.choose_spec
- \+ *def* encodable.choose_x
- \- *def* encodable.pn
- \- *lemma* succ_ne_zero

Modified data/equiv.lean
- \+/\- *lemma* equiv.apply_eq_iff_eq_inverse_apply
- \+/\- *def* equiv.bool_prod_equiv_sum
- \+ *def* equiv.bool_prod_nat_equiv_nat
- \+/\- *lemma* equiv.coe_fn_symm_mk
- \+ *def* equiv.equiv_empty
- \+/\- *def* equiv.false_equiv_empty
- \+/\- *lemma* equiv.inverse_apply_apply
- \+/\- *def* equiv.nat_equiv_nat_sum_unit
- \+/\- *def* equiv.nat_prod_nat_equiv_nat
- \+/\- *def* equiv.nat_sum_bool_equiv_nat
- \+ *def* equiv.nat_sum_nat_equiv_nat
- \+/\- *def* equiv.nat_sum_unit_equiv_nat
- \+ *def* equiv.option_equiv_sum_unit
- \+ *def* equiv.prod_equiv_of_equiv_nat
- \+/\- *def* equiv.subtype_equiv_of_subtype

Modified data/fin.lean


Modified data/nat/basic.lean
- \+ *theorem* nat.bodd_div2_eq

Modified data/option.lean
- \+ *lemma* option.bind_some

Modified data/set/enumerate.lean
- \- *lemma* option.bind_some

Modified tactic/interactive.lean




## [2017-09-18 22:41:41-04:00](https://github.com/leanprover-community/mathlib/commit/1e4c869)
doc(tactic/interactive): rename simpf -> simpa, document rcases and simpa
#### Estimated changes
Modified algebra/ordered_group.lean


Modified algebra/ordered_ring.lean


Modified data/nat/pairing.lean


Modified data/nat/sqrt.lean


Modified tactic/interactive.lean


Modified topology/real.lean


Modified topology/topological_space.lean


Modified topology/uniform_space.lean




## [2017-09-18 22:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/cb4a92e)
chore(algebra/ordered_ring): fix names, update to lean
#### Estimated changes
Modified algebra/ordered_ring.lean


Modified data/nat/pairing.lean
- \+ *theorem* nat.unpair_le
- \+/\- *theorem* nat.unpair_lt
- \- *theorem* nat.unpair_lt_aux



## [2017-09-18 21:57:48-04:00](https://github.com/leanprover-community/mathlib/commit/06e797b)
refactor(data/nat/pairing): improve proof readability
in response to review comments on 0acdf1c
#### Estimated changes
Modified data/nat/pairing.lean
- \+/\- *theorem* nat.unpair_lt



## [2017-09-17 15:38:03-04:00](https://github.com/leanprover-community/mathlib/commit/0acdf1c)
feat(data/nat): better sqrt + pairing, prime numbers, renames...
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* lt_min_iff
- \+ *lemma* max_lt_iff

Modified algebra/group_power.lean


Modified algebra/order.lean
- \+ *lemma* eq_or_lt_of_le
- \+ *lemma* lt_iff_le_and_ne

Modified algebra/ring.lean
- \+ *theorem* mul_dvd_mul_iff_left
- \+ *theorem* mul_dvd_mul_iff_right

Modified data/finset/basic.lean


Modified data/int/basic.lean


Modified data/nat/basic.lean
- \+ *theorem* nat.bit0_le_bit
- \+ *theorem* nat.bit_le
- \+ *theorem* nat.bit_le_bit1
- \+ *theorem* nat.bit_lt_bit0
- \+ *theorem* nat.bit_lt_bit
- \+ *theorem* nat.bit_ne_zero
- \+ *theorem* nat.dvd_fact
- \+ *def* nat.fact
- \+ *theorem* nat.fact_dvd_fact
- \+ *theorem* nat.fact_le
- \+ *theorem* nat.fact_ne_zero
- \+ *theorem* nat.fact_one
- \+ *theorem* nat.fact_pos
- \+ *theorem* nat.fact_succ
- \+ *theorem* nat.fact_zero
- \+ *theorem* nat.le_add_one_iff
- \- *lemma* nat.le_add_one_iff
- \+ *theorem* nat.le_zero_iff
- \- *lemma* nat.le_zero_iff
- \+ *lemma* nat.lt_pred_of_succ_lt
- \+ *theorem* nat.lt_size
- \+ *theorem* nat.lt_size_self
- \+ *theorem* nat.lt_succ_iff
- \- *theorem* nat.lt_succ_iff_le
- \+ *lemma* nat.lt_succ_iff_lt_or_eq
- \+ *theorem* nat.mul_self_inj
- \+ *theorem* nat.pos_iff_ne_zero'
- \+ *theorem* nat.pos_iff_ne_zero
- \+ *theorem* nat.pow_add
- \+ *theorem* nat.pow_dvd_pow
- \+ *theorem* nat.shiftl'_ne_zero_left
- \+ *theorem* nat.shiftl'_tt_ne_zero
- \+ *theorem* nat.size_bit0
- \+ *theorem* nat.size_bit1
- \+ *theorem* nat.size_bit
- \+ *theorem* nat.size_eq_zero
- \+ *theorem* nat.size_le
- \+ *theorem* nat.size_le_size
- \+ *theorem* nat.size_pos
- \+ *theorem* nat.size_pow
- \+ *theorem* nat.size_shiftl'
- \+ *theorem* nat.size_shiftl
- \+ *theorem* nat.size_zero
- \+ *theorem* nat.sub_le_left_iff_le_add
- \+ *theorem* nat.sub_le_right_iff_le_add
- \+/\- *theorem* nat.succ_le_succ_iff

Deleted data/nat/bquant.lean
- \- *def* ball'
- \- *def* ball
- \- *theorem* ball_of_ball_succ'
- \- *theorem* ball_of_ball_succ
- \- *theorem* ball_succ_of_ball
- \- *theorem* ball_zero'
- \- *theorem* ball_zero
- \- *theorem* not_ball_of_not
- \- *theorem* not_ball_succ_of_not_ball
- \- *def* step_p

Renamed data/nat/sub.lean to data/nat/dist.lean


Modified data/nat/gcd.lean
- \+ *theorem* nat.coprime.coprime_dvd_left
- \+ *theorem* nat.coprime.coprime_dvd_right
- \+ *theorem* nat.coprime.coprime_mul_left
- \+ *theorem* nat.coprime.coprime_mul_left_right
- \+ *theorem* nat.coprime.coprime_mul_right
- \+ *theorem* nat.coprime.coprime_mul_right_right
- \+ *theorem* nat.coprime.dvd_of_dvd_mul_left
- \+ *theorem* nat.coprime.dvd_of_dvd_mul_right
- \+ *theorem* nat.coprime.eq_one_of_dvd
- \+ *theorem* nat.coprime.gcd_eq_one
- \+ *theorem* nat.coprime.gcd_mul_left_cancel
- \+ *theorem* nat.coprime.gcd_mul_left_cancel_right
- \+ *theorem* nat.coprime.gcd_mul_right_cancel
- \+ *theorem* nat.coprime.gcd_mul_right_cancel_right
- \+ *theorem* nat.coprime.mul
- \+ *theorem* nat.coprime.mul_right
- \+ *theorem* nat.coprime.pow
- \+ *theorem* nat.coprime.pow_left
- \+ *theorem* nat.coprime.pow_right
- \+ *theorem* nat.coprime.symm
- \- *theorem* nat.coprime_mul
- \- *theorem* nat.coprime_mul_right
- \- *theorem* nat.coprime_of_coprime_dvd_left
- \- *theorem* nat.coprime_of_coprime_dvd_right
- \- *theorem* nat.coprime_of_coprime_mul_left
- \- *theorem* nat.coprime_of_coprime_mul_left_right
- \- *theorem* nat.coprime_of_coprime_mul_right
- \- *theorem* nat.coprime_of_coprime_mul_right_right
- \- *theorem* nat.coprime_pow
- \- *theorem* nat.coprime_pow_left
- \- *theorem* nat.coprime_pow_right
- \- *theorem* nat.coprime_swap
- \- *theorem* nat.dvd_of_coprime_of_dvd_mul_left
- \- *theorem* nat.dvd_of_coprime_of_dvd_mul_right
- \+ *theorem* nat.gcd_eq_left
- \- *theorem* nat.gcd_eq_one_of_coprime
- \+ *theorem* nat.gcd_eq_right
- \- *theorem* nat.gcd_mul_left_cancel_of_coprime
- \- *theorem* nat.gcd_mul_left_cancel_of_coprime_right
- \- *theorem* nat.gcd_mul_right_cancel_of_coprime
- \- *theorem* nat.gcd_mul_right_cancel_of_coprime_right

Modified data/nat/pairing.lean
- \+/\- *theorem* nat.unpair_lt
- \+/\- *theorem* nat.unpair_lt_aux

Added data/nat/prime.lean
- \+ *theorem* nat.coprime_or_dvd_of_prime
- \+ *theorem* nat.coprime_pow_primes
- \+ *theorem* nat.coprime_primes
- \+ *def* nat.decidable_prime_1
- \+ *theorem* nat.dvd_of_prime_of_dvd_pow
- \+ *theorem* nat.dvd_prime
- \+ *theorem* nat.dvd_prime_ge_two
- \+ *theorem* nat.dvd_prime_pow
- \+ *theorem* nat.exists_dvd_of_not_prime2
- \+ *theorem* nat.exists_dvd_of_not_prime
- \+ *theorem* nat.exists_infinite_primes
- \+ *theorem* nat.exists_prime_and_dvd
- \+ *def* nat.min_fac
- \+ *def* nat.min_fac_aux
- \+ *theorem* nat.min_fac_aux_has_prop
- \+ *theorem* nat.min_fac_dvd
- \+ *theorem* nat.min_fac_eq
- \+ *theorem* nat.min_fac_has_prop
- \+ *theorem* nat.min_fac_le
- \+ *theorem* nat.min_fac_le_of_dvd
- \+ *theorem* nat.min_fac_one
- \+ *theorem* nat.min_fac_pos
- \+ *theorem* nat.min_fac_prime
- \+ *theorem* nat.min_fac_zero
- \+ *theorem* nat.not_prime_iff_min_fac_lt
- \+ *theorem* nat.not_prime_one
- \+ *theorem* nat.not_prime_zero
- \+ *theorem* nat.prime.coprime_iff_not_dvd
- \+ *theorem* nat.prime.coprime_pow_of_not_dvd
- \+ *theorem* nat.prime.dvd_iff_not_coprime
- \+ *theorem* nat.prime.dvd_mul
- \+ *theorem* nat.prime.ge_two
- \+ *theorem* nat.prime.gt_one
- \+ *theorem* nat.prime.not_dvd_mul
- \+ *theorem* nat.prime.not_dvd_one
- \+ *theorem* nat.prime.pos
- \+ *theorem* nat.prime.pred_pos
- \+ *def* nat.prime
- \+ *theorem* nat.prime_def_le_sqrt
- \+ *theorem* nat.prime_def_lt'
- \+ *theorem* nat.prime_def_lt
- \+ *theorem* nat.prime_def_min_fac
- \+ *theorem* nat.prime_three
- \+ *theorem* nat.prime_two
- \+ *theorem* nat.succ_pred_prime

Modified data/nat/sqrt.lean
- \- *theorem* nat.eq_zero_of_sqrt_eq_zero
- \+ *theorem* nat.le_sqrt
- \+/\- *theorem* nat.le_three_of_sqrt_eq_one
- \+ *theorem* nat.lt_succ_sqrt
- \- *theorem* nat.mul_square_cancel
- \+ *def* nat.sqrt
- \+ *theorem* nat.sqrt_add_eq
- \+ *def* nat.sqrt_aux
- \+ *theorem* nat.sqrt_aux_0
- \+ *theorem* nat.sqrt_aux_1
- \+ *theorem* nat.sqrt_aux_2
- \+ *theorem* nat.sqrt_aux_dec
- \+/\- *theorem* nat.sqrt_eq
- \+ *theorem* nat.sqrt_eq_zero
- \+ *theorem* nat.sqrt_le
- \+ *theorem* nat.sqrt_le_add
- \+ *theorem* nat.sqrt_le_self
- \+ *theorem* nat.sqrt_le_sqrt
- \- *theorem* nat.sqrt_lower
- \+/\- *theorem* nat.sqrt_lt
- \+ *theorem* nat.sqrt_lt_self
- \- *theorem* nat.sqrt_mono
- \- *theorem* nat.sqrt_mul_eq
- \+ *theorem* nat.sqrt_pos
- \- *theorem* nat.sqrt_pos_of_pos
- \- *theorem* nat.sqrt_upper

Modified data/rat.lean


Modified logic/basic.lean
- \+ *theorem* not.imp

Modified tactic/rcases.lean


Modified topology/measurable_space.lean
- \- *lemma* nat.lt_succ_iff

Modified topology/topological_structures.lean
- \- *lemma* lt_min_iff
- \- *lemma* max_lt_iff



## [2017-09-16 03:26:54-04:00](https://github.com/leanprover-community/mathlib/commit/f542d42)
chore(algebra/ordered_ring): update to lean
#### Estimated changes
Modified algebra/ordered_ring.lean
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero



## [2017-09-16 02:55:01-04:00](https://github.com/leanprover-community/mathlib/commit/fe1ad4b)
feat(data/rat): derive properties of rat floor and ceil
#### Estimated changes
Modified data/int/basic.lean
- \+ *theorem* int.le_to_nat
- \+ *theorem* int.lt_succ_self
- \+ *theorem* int.pred_self_lt
- \+ *theorem* int.to_nat_eq_max
- \+ *theorem* int.to_nat_le

Modified data/rat.lean
- \+ *theorem* rat.ceil_add_int
- \+ *theorem* rat.ceil_coe
- \+ *theorem* rat.ceil_le
- \+ *theorem* rat.ceil_mono
- \+ *theorem* rat.ceil_sub_int
- \+ *theorem* rat.coe_int_add
- \- *lemma* rat.coe_int_add
- \+ *theorem* rat.coe_int_eq_mk
- \- *lemma* rat.coe_int_eq_mk
- \+ *theorem* rat.coe_int_inj
- \+ *theorem* rat.coe_int_le
- \+ *theorem* rat.coe_int_lt
- \+ *theorem* rat.coe_int_mul
- \+ *theorem* rat.coe_int_neg
- \+ *theorem* rat.coe_int_one
- \- *lemma* rat.coe_int_one
- \+ *theorem* rat.coe_int_sub
- \- *lemma* rat.coe_int_sub
- \+ *theorem* rat.coe_nat_rat_eq_mk
- \- *lemma* rat.coe_nat_rat_eq_mk
- \- *lemma* rat.exists_upper_nat_bound
- \+ *theorem* rat.floor_add_int
- \+ *theorem* rat.floor_coe
- \+ *theorem* rat.floor_le
- \+ *theorem* rat.floor_lt
- \+ *theorem* rat.floor_mono
- \+ *theorem* rat.floor_sub_int
- \+ *theorem* rat.le_ceil
- \+ *theorem* rat.le_floor
- \+ *theorem* rat.le_nat_ceil
- \- *lemma* rat.le_of_of_int_le_of_int
- \+ *theorem* rat.lt_nat_ceil
- \+ *theorem* rat.lt_succ_floor
- \+ *theorem* rat.mk_le
- \+/\- *def* rat.nat_ceil
- \+ *theorem* rat.nat_ceil_add_nat
- \- *lemma* rat.nat_ceil_add_one_eq
- \+ *theorem* rat.nat_ceil_coe
- \+ *theorem* rat.nat_ceil_le
- \+ *theorem* rat.nat_ceil_lt_add_one
- \- *lemma* rat.nat_ceil_lt_add_one
- \- *lemma* rat.nat_ceil_min
- \+ *theorem* rat.nat_ceil_mono
- \- *lemma* rat.nat_ceil_mono
- \- *lemma* rat.nat_ceil_spec
- \+ *theorem* rat.nat_ceil_zero
- \- *lemma* rat.nat_ceil_zero
- \+ *theorem* rat.sub_def

Modified topology/real.lean




## [2017-09-16 02:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/a1c3e2d)
feat(algebra): new algebra theorems (more iff)
#### Estimated changes
Modified algebra/big_operators.lean


Added algebra/functions.lean
- \+ *lemma* abs_eq_zero
- \+ *theorem* abs_le
- \+ *lemma* abs_lt
- \+ *lemma* le_min_iff
- \+ *lemma* max_le_iff

Modified algebra/group.lean
- \- *lemma* abs_eq_zero_iff
- \- *lemma* abs_le_iff
- \- *lemma* abs_lt_iff
- \+ *lemma* add_sub_cancel'
- \+ *lemma* add_sub_cancel'_right
- \- *theorem* eq_iff_sub_eq_zero
- \+/\- *theorem* eq_inv_iff_eq_inv
- \+ *theorem* eq_inv_mul_iff_mul_eq
- \+ *theorem* eq_mul_inv_iff_mul_eq
- \+ *theorem* eq_of_inv_eq_inv
- \- *theorem* eq_of_mul_inv_eq_one
- \- *theorem* eq_one_of_inv_eq_one
- \+ *lemma* eq_sub_iff_add_eq'
- \+/\- *theorem* eq_sub_iff_add_eq
- \+ *theorem* inv_eq_iff_inv_eq
- \- *theorem* inv_eq_inv_iff_eq
- \+ *theorem* inv_eq_one
- \- *theorem* inv_eq_one_iff_eq_one
- \+ *theorem* inv_inj'
- \+ *theorem* inv_mul_eq_iff_eq_mul
- \+ *theorem* inv_ne_one
- \+ *theorem* le_sub_iff_add_le
- \- *lemma* le_sub_iff_add_le
- \+/\- *theorem* left_inverse_inv
- \- *theorem* mul_eq_iff_eq_inv_mul
- \- *theorem* mul_eq_iff_eq_mul_inv
- \+ *theorem* mul_eq_one_iff_eq_inv
- \+ *theorem* mul_eq_one_iff_inv_eq
- \+ *theorem* mul_inv_eq_iff_eq_mul
- \+ *theorem* mul_inv_eq_one
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_right_inj
- \+ *theorem* mul_self_iff_eq_one
- \+ *theorem* neg_add'
- \+ *lemma* sub_add_sub_cancel
- \+ *lemma* sub_eq_iff_eq_add'
- \+/\- *theorem* sub_eq_iff_eq_add
- \+ *lemma* sub_eq_neg_add
- \+ *theorem* sub_eq_zero
- \+ *theorem* sub_le_iff_le_add
- \- *lemma* sub_le_iff_le_add
- \+ *lemma* sub_left_inj
- \+ *theorem* sub_ne_zero
- \+ *lemma* sub_right_inj
- \+ *lemma* sub_sub_sub_cancel_left
- \+ *lemma* sub_sub_sub_cancel_right
- \+ *lemma* sub_sub_swap

Added algebra/order.lean
- \+ *lemma* eq_of_forall_ge_iff
- \+ *lemma* eq_of_forall_le_iff
- \+ *lemma* le_iff_eq_or_lt
- \+ *lemma* le_iff_le_iff_lt_iff_lt
- \+ *lemma* le_imp_le_iff_lt_imp_lt
- \+ *lemma* le_of_not_lt
- \+ *lemma* not_le
- \+ *lemma* not_le_of_lt
- \+ *lemma* not_lt
- \+ *lemma* not_lt_iff_eq_or_lt
- \+ *lemma* not_lt_of_le
- \+ *lemma* not_lt_of_lt

Added algebra/ordered_group.lean
- \+ *lemma* add_eq_zero_iff_eq_zero_of_nonneg
- \+ *lemma* add_le_add_iff_left
- \+ *lemma* add_le_add_iff_right
- \+ *lemma* add_lt_add_iff_left
- \+ *lemma* add_lt_add_iff_right
- \+ *lemma* le_add_iff_nonneg_left
- \+ *lemma* le_add_iff_nonneg_right
- \+ *lemma* le_neg
- \+ *lemma* le_neg_add_iff_add_le
- \+ *lemma* le_sub_left_iff_add_le
- \+ *lemma* le_sub_right_iff_add_le
- \+ *lemma* lt_add_iff_pos_left
- \+ *lemma* lt_add_iff_pos_right
- \+ *lemma* lt_neg
- \+ *lemma* lt_neg_add_iff_add_lt
- \+ *lemma* lt_sub_left_iff_add_lt
- \+ *lemma* lt_sub_right_iff_add_lt
- \+ *lemma* neg_add_le_iff_le_add
- \+ *lemma* neg_add_le_iff_le_add_right
- \+ *lemma* neg_add_lt_iff_lt_add
- \+ *lemma* neg_add_lt_iff_lt_add_right
- \+ *lemma* neg_le
- \+ *lemma* neg_le_neg_iff
- \+ *lemma* neg_le_sub_iff_le_add
- \+ *lemma* neg_le_sub_iff_le_add_left
- \+ *lemma* neg_lt
- \+ *lemma* neg_lt_neg_iff
- \+ *lemma* neg_lt_sub_iff_lt_add
- \+ *lemma* neg_lt_sub_iff_lt_add_left
- \+ *lemma* neg_lt_zero
- \+ *lemma* neg_nonneg
- \+ *lemma* neg_nonpos
- \+ *lemma* neg_pos
- \+ *theorem* nonneg_comm_group.nonneg_def
- \+ *theorem* nonneg_comm_group.nonneg_total_iff
- \+ *theorem* nonneg_comm_group.not_zero_pos
- \+ *theorem* nonneg_comm_group.pos_def
- \+ *def* nonneg_comm_group.to_decidable_linear_ordered_comm_group
- \+ *theorem* nonneg_comm_group.zero_lt_iff_nonneg_nonneg
- \+ *lemma* sub_le
- \+ *lemma* sub_le_self_iff
- \+ *lemma* sub_le_sub_iff_left
- \+ *lemma* sub_le_sub_iff_right
- \+ *lemma* sub_left_le_iff_le_add
- \+ *lemma* sub_left_lt_iff_lt_add
- \+ *lemma* sub_lt
- \+ *lemma* sub_lt_self_iff
- \+ *lemma* sub_lt_sub_iff_left
- \+ *lemma* sub_lt_sub_iff_right
- \+ *lemma* sub_lt_zero
- \+ *lemma* sub_nonneg
- \+ *lemma* sub_nonpos
- \+ *lemma* sub_pos
- \+ *lemma* sub_right_le_iff_le_add
- \+ *lemma* sub_right_lt_iff_lt_add

Added algebra/ordered_ring.lean
- \+ *lemma* le_mul_iff_one_le_left
- \+ *lemma* le_mul_iff_one_le_right
- \+ *lemma* le_mul_of_ge_one_left'
- \+ *lemma* le_mul_of_ge_one_right'
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* lt_mul_iff_one_lt_left
- \+ *lemma* lt_mul_iff_one_lt_right
- \+ *lemma* lt_mul_of_gt_one_right'
- \+ *lemma* mul_le_mul_left
- \+ *lemma* mul_le_mul_left_of_neg
- \+ *lemma* mul_le_mul_right
- \+ *lemma* mul_le_mul_right_of_neg
- \+ *lemma* mul_lt_mul_left
- \+ *lemma* mul_lt_mul_left_of_neg
- \+ *lemma* mul_lt_mul_right
- \+ *lemma* mul_lt_mul_right_of_neg
- \+ *def* nonneg_ring.nonneg_ring.to_linear_nonneg_ring

Modified algebra/ring.lean
- \+ *theorem* domain.mul_left_inj
- \+ *theorem* domain.mul_right_inj
- \+ *lemma* dvd_neg
- \+/\- *theorem* eq_of_mul_eq_mul_left_of_ne_zero
- \+/\- *theorem* eq_of_mul_eq_mul_right_of_ne_zero
- \+ *theorem* eq_zero_of_mul_eq_self_left'
- \+ *theorem* eq_zero_of_mul_eq_self_right'
- \+ *theorem* mul_eq_zero
- \+ *theorem* mul_ne_zero'
- \+ *theorem* mul_ne_zero_comm'
- \+ *theorem* mul_two
- \+/\- *theorem* ne_zero_and_ne_zero_of_mul_ne_zero
- \+ *lemma* neg_dvd

Modified topology/ennreal.lean


Modified topology/metric_space.lean


Modified topology/real.lean




## [2017-09-16 02:51:50-04:00](https://github.com/leanprover-community/mathlib/commit/a967d8d)
feat(tactic/interactive): allow exprs in simpf, interactive try_for
#### Estimated changes
Modified tactic/interactive.lean




## [2017-09-13 17:34:12-04:00](https://github.com/leanprover-community/mathlib/commit/f705963)
feat(topology/measure): introduce measures
#### Estimated changes
Modified data/set/lattice.lean
- \+/\- *lemma* set.Union_subset_Union2
- \+/\- *theorem* set.inter_distrib_Union_left
- \+ *theorem* set.inter_distrib_Union_right

Modified topology/ennreal.lean
- \- *lemma* ennreal.add_le_add
- \- *lemma* ennreal.lt_of_add_lt_add_left
- \+ *lemma* lt_supr_iff

Modified topology/infinite_sum.lean
- \+ *lemma* has_sum_sigma
- \+ *lemma* is_sum_iff_is_sum_of_iso
- \+ *lemma* is_sum_le
- \+ *lemma* tsum_eq_sum
- \+ *lemma* tsum_eq_tsum_of_is_sum_iff_is_sum
- \+ *lemma* tsum_eq_tsum_of_iso
- \+ *lemma* tsum_eq_tsum_of_ne_zero_bij
- \+ *lemma* tsum_le_tsum
- \+ *lemma* tsum_sigma

Modified topology/measurable_space.lean
- \+ *lemma* is_measurable_disjointed
- \+ *def* pairwise
- \+/\- *lemma* set.disjoint_disjointed
- \+ *lemma* set.disjointed_induct

Added topology/measure.lean
- \+ *def* measure_theory.count
- \+ *lemma* measure_theory.measure_Union_le_nat
- \+ *lemma* measure_theory.measure_Union_nat
- \+ *lemma* measure_theory.measure_bUnion
- \+ *lemma* measure_theory.measure_empty
- \+ *lemma* measure_theory.measure_eq_measure_of
- \+ *lemma* measure_theory.measure_mono
- \+ *lemma* measure_theory.measure_sUnion
- \+ *def* measure_theory.measure_space.measure
- \+ *structure* measure_theory.measure_space
- \+ *lemma* measure_theory.measure_space_eq
- \+ *lemma* measure_theory.measure_space_eq_of
- \+ *lemma* measure_theory.measure_union
- \+ *lemma* supr_bool_eq

Modified topology/topological_structures.lean
- \+/\- *lemma* binfi_inf
- \+ *lemma* inf_principal_eq_bot
- \+ *lemma* infi_neg
- \+ *lemma* infi_pos
- \+/\- *lemma* le_of_tendsto
- \- *lemma* mem_nhds_lattice_unbounded
- \+ *lemma* mem_nhds_orderable_dest
- \+ *lemma* mem_nhds_unbounded
- \+ *lemma* supr_neg
- \+ *lemma* supr_pos



## [2017-09-13 14:20:42-04:00](https://github.com/leanprover-community/mathlib/commit/0b16336)
feat(topology/infinite_sum): strengten bijection proof
#### Estimated changes
Modified topology/infinite_sum.lean
- \+ *lemma* tsum_eq_tsum_of_ne_zero
- \+/\- *lemma* tsum_zero



## [2017-09-13 14:19:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b077c)
chore(data/equiv): use has_coe_to_fun
#### Estimated changes
Modified data/equiv.lean
- \+/\- *lemma* equiv.apply_eq_iff_eq
- \+/\- *lemma* equiv.apply_eq_iff_eq_inverse_apply
- \+ *lemma* equiv.coe_fn_mk
- \+ *lemma* equiv.coe_fn_symm_mk
- \+/\- *lemma* equiv.comp_apply
- \+/\- *lemma* equiv.eq_of_to_fun_eq
- \- *def* equiv.fn
- \+/\- *lemma* equiv.id_apply
- \- *def* equiv.inv
- \+/\- *lemma* equiv.inverse_apply_apply
- \+/\- *def* equiv.subtype_equiv_of_subtype
- \+/\- *lemma* equiv.swap_apply_def
- \+/\- *lemma* equiv.swap_apply_left
- \+/\- *lemma* equiv.swap_apply_of_ne_of_ne
- \+/\- *lemma* equiv.swap_apply_right



## [2017-09-11 21:55:00-04:00](https://github.com/leanprover-community/mathlib/commit/bf58bf4)
feat(topology/measurable_space): induction rule for sigma-algebras with intersection-stable generators; uses Dynkin systems
#### Estimated changes
Modified topology/measurable_space.lean
- \+ *lemma* is_measurable_univ
- \+ *lemma* measurable_generate_from
- \+ *lemma* measurable_space.dynkin_system.dynkin_system_eq
- \+ *def* measurable_space.dynkin_system.generate
- \+ *lemma* measurable_space.dynkin_system.generate_from_eq
- \+ *inductive* measurable_space.dynkin_system.generate_has
- \+ *lemma* measurable_space.dynkin_system.generate_inter
- \+ *lemma* measurable_space.dynkin_system.generate_le
- \+ *lemma* measurable_space.dynkin_system.has_sdiff
- \+ *lemma* measurable_space.dynkin_system.has_union
- \+ *lemma* measurable_space.dynkin_system.has_univ
- \+ *def* measurable_space.dynkin_system.of_measurable_space
- \+ *lemma* measurable_space.dynkin_system.of_measurable_space_le_of_measurable_space_iff
- \+ *lemma* measurable_space.dynkin_system.of_measurable_space_to_measurable_space
- \+ *def* measurable_space.dynkin_system.restrict_on
- \+ *def* measurable_space.dynkin_system.to_measurable_space
- \+ *structure* measurable_space.dynkin_system
- \+ *def* measurable_space.generate_from
- \+ *lemma* measurable_space.generate_from_le
- \+ *inductive* measurable_space.generate_measurable
- \+ *lemma* measurable_space.induction_on_inter
- \+ *lemma* measurable_space.is_measurable_generate_from
- \+ *lemma* nat.lt_succ_iff
- \+ *lemma* set.disjoint_disjointed
- \+ *def* set.disjointed
- \+ *lemma* set.disjointed_Union



## [2017-09-11 14:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/74c3e6e)
feat(topology/measurable_space): measurable sets invariant under (countable) set operations
#### Estimated changes
Modified topology/measurable_space.lean
- \+ *lemma* is_measurable_Inter
- \+/\- *lemma* is_measurable_Union
- \+ *lemma* is_measurable_Union_nat
- \+ *lemma* is_measurable_bInter
- \+ *lemma* is_measurable_bUnion
- \+ *lemma* is_measurable_inter
- \+ *lemma* is_measurable_sInter
- \+ *lemma* is_measurable_sUnion
- \+ *lemma* is_measurable_sdiff
- \+ *lemma* is_measurable_sub
- \+ *lemma* is_measurable_union



## [2017-09-11 13:56:06-04:00](https://github.com/leanprover-community/mathlib/commit/b890425)
feat(topology/ennreal): ennreal forms a topological monoid
#### Estimated changes
Modified order/filter.lean
- \+ *lemma* filter.tendsto_inf_left

Modified topology/ennreal.lean
- \+ *lemma* ennreal.nhds_of_real_eq_map_of_real_nhds_nonneg

Modified topology/real.lean
- \- *lemma* ge_mem_nhds
- \- *lemma* gt_mem_nhds
- \- *lemma* le_mem_nhds
- \- *lemma* lt_mem_nhds

Modified topology/topological_structures.lean
- \+ *lemma* ge_mem_nhds
- \+ *lemma* gt_mem_nhds
- \+ *lemma* le_mem_nhds
- \+ *lemma* lt_mem_nhds



## [2017-09-11 11:58:16-04:00](https://github.com/leanprover-community/mathlib/commit/8ed673d)
feat(data/set/countable): finite sets are countable
#### Estimated changes
Modified data/encodable.lean


Modified data/set/countable.lean
- \+ *lemma* set.countable_Union
- \+ *lemma* set.countable_finite
- \+ *lemma* set.countable_insert
- \+ *lemma* set.countable_union



## [2017-09-11 11:32:25-04:00](https://github.com/leanprover-community/mathlib/commit/28b46a2)
fix(data/set/countable): finish proof countable_sUnion
#### Estimated changes
Modified data/set/countable.lean
- \- *lemma* option.bind_some
- \+/\- *lemma* set.countable_sUnion
- \- *def* set.enumerate
- \- *lemma* set.enumerate_eq_none
- \- *lemma* set.enumerate_eq_none_of_sel
- \- *lemma* set.enumerate_inj
- \- *lemma* set.enumerate_mem

Added data/set/enumerate.lean
- \+ *lemma* option.bind_some
- \+ *def* set.enumerate
- \+ *lemma* set.enumerate_eq_none
- \+ *lemma* set.enumerate_eq_none_of_sel
- \+ *lemma* set.enumerate_inj
- \+ *lemma* set.enumerate_mem



## [2017-09-10 23:28:41-04:00](https://github.com/leanprover-community/mathlib/commit/8ee2629)
feat(data/set): add countable sets
#### Estimated changes
Modified data/encodable.lean


Added data/set/countable.lean
- \+ *lemma* option.bind_some
- \+ *lemma* set.countable.to_encodable
- \+ *def* set.countable
- \+ *lemma* set.countable_empty
- \+ *lemma* set.countable_encodable'
- \+ *lemma* set.countable_encodable
- \+ *lemma* set.countable_iff_exists_surjective
- \+ *lemma* set.countable_image
- \+ *lemma* set.countable_sUnion
- \+ *lemma* set.countable_singleton
- \+ *lemma* set.countable_subset
- \+ *def* set.encodable_of_inj
- \+ *def* set.enumerate
- \+ *lemma* set.enumerate_eq_none
- \+ *lemma* set.enumerate_eq_none_of_sel
- \+ *lemma* set.enumerate_inj
- \+ *lemma* set.enumerate_mem

Modified data/set/finite.lean
- \+ *def* set.infinite

Modified logic/function_inverse.lean
- \+ *theorem* set.inv_fun_on_eq'

Modified order/filter.lean




## [2017-09-10 20:33:16-04:00](https://github.com/leanprover-community/mathlib/commit/7e06124)
feat(logic): add small theory on inverse functions
#### Estimated changes
Added logic/function_inverse.lean
- \+ *lemma* set.has_left_inverse
- \+ *lemma* set.has_right_inverse
- \+ *lemma* set.injective_surj_inv
- \+ *def* set.inv_fun
- \+ *theorem* set.inv_fun_eq
- \+ *theorem* set.inv_fun_eq_of_injective_of_right_inverse
- \+ *def* set.inv_fun_on
- \+ *theorem* set.inv_fun_on_eq
- \+ *theorem* set.inv_fun_on_mem
- \+ *theorem* set.inv_fun_on_neg
- \+ *theorem* set.inv_fun_on_pos
- \+ *lemma* set.left_inverse_inv_fun
- \+ *lemma* set.right_inverse_inv_fun
- \+ *lemma* set.right_inverse_surj_inv
- \+ *def* set.surj_inv
- \+ *lemma* set.surj_inv_eq



## [2017-09-09 12:48:22-04:00](https://github.com/leanprover-community/mathlib/commit/a5f32d2)
feat(data/encodable): port countable choice from Lean2
#### Estimated changes
Modified data/encodable.lean
- \+ *theorem* encodable.axiom_of_choice
- \+ *def* encodable.choose
- \+ *lemma* encodable.choose_spec
- \+ *def* encodable.pn
- \+ *theorem* encodable.skolem
- \+ *def* quot.encodable_quotient
- \+ *def* quot.rep
- \+ *theorem* quot.rep_spec



## [2017-09-08 20:06:26-04:00](https://github.com/leanprover-community/mathlib/commit/3399baa)
feat(data/encodable): ported data/encodable.lean from Lean2
#### Estimated changes
Added data/encodable.lean
- \+ *def* encodable_of_equiv
- \+ *def* encodable_of_left_injection
- \+ *lemma* succ_ne_zero

Modified data/list/sort.lean
- \+ *lemma* list.eq_of_sorted_of_perm
- \- *theorem* list.sorted_insert_sort
- \+ *theorem* list.sorted_insertion_sort



## [2017-09-08 18:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/741065b)
chore(data/equiv): using nat pairing
#### Estimated changes
Modified data/equiv.lean
- \+ *def* equiv.nat_prod_nat_equiv_nat



## [2017-09-08 18:05:53-04:00](https://github.com/leanprover-community/mathlib/commit/22c8fae)
feat(data/nat/pairing): ported data/nat/pairing.lean from Lean2
#### Estimated changes
Added data/nat/pairing.lean
- \+ *def* nat.mkpair
- \+ *theorem* nat.mkpair_unpair
- \+ *def* nat.unpair
- \+ *theorem* nat.unpair_lt
- \+ *theorem* nat.unpair_lt_aux
- \+ *theorem* nat.unpair_mkpair



## [2017-09-08 17:19:17-04:00](https://github.com/leanprover-community/mathlib/commit/7c67c29)
feat(data/nat/sqrt): ported data/nat/sqrt.lean from Lean2
#### Estimated changes
Added data/nat/sqrt.lean
- \+ *theorem* nat.eq_zero_of_sqrt_eq_zero
- \+ *theorem* nat.le_three_of_sqrt_eq_one
- \+ *theorem* nat.mul_square_cancel
- \+ *theorem* nat.sqrt_eq
- \+ *theorem* nat.sqrt_lower
- \+ *theorem* nat.sqrt_lt
- \+ *theorem* nat.sqrt_mono
- \+ *theorem* nat.sqrt_mul_eq
- \+ *theorem* nat.sqrt_pos_of_pos
- \+ *theorem* nat.sqrt_upper



## [2017-09-08 14:50:51-04:00](https://github.com/leanprover-community/mathlib/commit/445a5a4)
fix(topology/real): remove (unnecessary) admit
#### Estimated changes
Modified topology/real.lean




## [2017-09-08 14:49:07-04:00](https://github.com/leanprover-community/mathlib/commit/8ef8f81)
feat(data/equiv): port data/equiv.lean from Lean2
#### Estimated changes
Added data/equiv.lean
- \+ *lemma* equiv.apply_eq_iff_eq
- \+ *lemma* equiv.apply_eq_iff_eq_inverse_apply
- \+ *def* equiv.arrow_arrow_equiv_prod_arrow
- \+ *def* equiv.arrow_congr
- \+ *def* equiv.arrow_prod_equiv_prod_arrow
- \+ *def* equiv.arrow_unit_equiv_unit
- \+ *def* equiv.bool_equiv_unit_sum_unit
- \+ *def* equiv.bool_prod_equiv_sum
- \+ *lemma* equiv.comp_apply
- \+ *def* equiv.decidable_eq_of_equiv
- \+ *def* equiv.empty_arrow_equiv_unit
- \+ *lemma* equiv.eq_iff_eq_of_injective
- \+ *lemma* equiv.eq_of_to_fun_eq
- \+ *def* equiv.false_arrow_equiv_unit
- \+ *def* equiv.false_equiv_empty
- \+ *def* equiv.fn
- \+ *def* equiv.id
- \+ *lemma* equiv.id_apply
- \+ *def* equiv.inhabited_of_equiv
- \+ *def* equiv.inv
- \+ *lemma* equiv.inverse_apply_apply
- \+ *def* equiv.nat_equiv_nat_sum_unit
- \+ *def* equiv.nat_sum_bool_equiv_nat
- \+ *def* equiv.nat_sum_unit_equiv_nat
- \+ *def* equiv.perm
- \+ *def* equiv.prod_assoc
- \+ *def* equiv.prod_comm
- \+ *def* equiv.prod_congr
- \+ *def* equiv.prod_empty_left
- \+ *def* equiv.prod_empty_right
- \+ *def* equiv.prod_sum_distrib
- \+ *def* equiv.prod_unit_left
- \+ *def* equiv.prod_unit_right
- \+ *def* equiv.subtype_equiv_of_subtype
- \+ *def* equiv.sum_arrow_equiv_prod_arrow
- \+ *def* equiv.sum_assoc
- \+ *def* equiv.sum_comm
- \+ *def* equiv.sum_congr
- \+ *def* equiv.sum_empty_left
- \+ *def* equiv.sum_empty_right
- \+ *def* equiv.sum_prod_distrib
- \+ *def* equiv.swap
- \+ *lemma* equiv.swap_apply_def
- \+ *lemma* equiv.swap_apply_left
- \+ *lemma* equiv.swap_apply_of_ne_of_ne
- \+ *lemma* equiv.swap_apply_right
- \+ *lemma* equiv.swap_comm
- \+ *lemma* equiv.swap_comp_apply
- \+ *def* equiv.swap_core
- \+ *lemma* equiv.swap_core_comm
- \+ *lemma* equiv.swap_core_self
- \+ *lemma* equiv.swap_core_swap_core
- \+ *lemma* equiv.swap_self
- \+ *lemma* equiv.swap_swap
- \+ *def* equiv.unit_arrow_equiv
- \+ *structure* equiv
- \+ *lemma* function.left_inverse.f_g_eq_id
- \+ *lemma* function.right_inverse.g_f_eq_id
- \+ *def* subtype.map
- \+ *lemma* subtype.map_comp
- \+ *lemma* subtype.map_id



## [2017-09-07 20:38:33-04:00](https://github.com/leanprover-community/mathlib/commit/ddeefb8)
feat(topology/topological_structures,ennreal): show continuity of of_ennreal and of_real
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.image_inter_on
- \+/\- *lemma* set.mem_range

Modified order/filter.lean
- \+ *lemma* filter.eq_of_map_eq_map_inj'
- \+ *lemma* filter.le_of_map_le_map_inj'
- \+/\- *lemma* filter.map_binfi_eq
- \+ *lemma* filter.map_inf'
- \+ *lemma* filter.tendsto_principal

Modified order/lattice.lean
- \+ *theorem* lattice.not_lt_bot
- \+ *theorem* lattice.not_top_lt

Modified topology/ennreal.lean
- \+ *lemma* ennreal.nhds_of_real_eq_map_of_real_nhds
- \+ *lemma* ennreal.tendsto_of_ennreal
- \+ *lemma* ennreal.tendsto_of_real

Modified topology/topological_space.lean
- \+ *lemma* is_open_neg

Modified topology/topological_structures.lean
- \+ *lemma* binfi_inf
- \+ *lemma* is_closed_ge'
- \+ *lemma* is_closed_le'
- \+/\- *lemma* is_open_gt'
- \+/\- *lemma* is_open_lt'
- \+ *lemma* lt_min_iff
- \+ *lemma* max_lt_iff
- \+ *lemma* mem_nhds_lattice_unbounded
- \+ *lemma* nhds_bot_orderable
- \+ *lemma* nhds_eq_orderable
- \+ *lemma* nhds_orderable_unbounded
- \+ *lemma* nhds_top_orderable
- \+ *lemma* tendsto_orderable
- \+ *lemma* tendsto_orderable_unbounded



## [2017-09-06 19:31:17-04:00](https://github.com/leanprover-community/mathlib/commit/32f3f45)
feat(topology): restructure order topologies; (start) proof that ennreal is a topological monoid
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* abs_lt_iff

Modified topology/ennreal.lean
- \+ *lemma* ennreal.continuous_of_real
- \+ *lemma* ennreal.inv_infty
- \+ *lemma* ennreal.inv_inv
- \+ *lemma* ennreal.inv_of_real
- \+ *lemma* ennreal.inv_zero
- \+ *lemma* ennreal.not_lt_zero
- \+ *lemma* ennreal.of_real_lt_of_real_iff_cases
- \+ *lemma* ennreal.of_real_of_nonpos
- \+ *lemma* ennreal.of_real_of_not_nonneg
- \+ *lemma* ennreal.one_le_of_real_iff
- \+ *lemma* ennreal.zero_lt_of_real_iff
- \+ *lemma* inv_inv'
- \+ *lemma* inv_pos

Modified topology/real.lean
- \- *lemma* is_closed_imp
- \+ *lemma* lt_sub_iff
- \+ *lemma* nhds_eq_real
- \+ *lemma* orderable_topology_of_nhds_abs
- \+ *lemma* sub_lt_iff

Modified topology/topological_space.lean
- \+/\- *lemma* closure_diff
- \+ *lemma* is_closed_imp
- \+ *lemma* is_open_and
- \+ *lemma* is_open_const
- \+ *lemma* mem_of_closed_of_tendsto

Modified topology/topological_structures.lean
- \+ *lemma* is_open_gt'
- \+ *lemma* is_open_iff_generate_intervals
- \+ *lemma* is_open_lt'
- \- *lemma* is_open_lt_fst_snd
- \+ *lemma* le_of_tendsto

Modified topology/uniform_space.lean
- \+ *lemma* nhds_eq_vmap_uniformity



## [2017-09-06 16:19:02-04:00](https://github.com/leanprover-community/mathlib/commit/17e48db)
fix(data/list/comb): implement fix from rlewis1988
#### Estimated changes
Modified data/list/comb.lean




## [2017-09-05 22:38:07-04:00](https://github.com/leanprover-community/mathlib/commit/f80ae1f)
feat(topology/infinite_sum): add tsum (with ∑ notation) and has_sum; add lemmas for different algebraic structures
#### Estimated changes
Modified topology/continuity.lean
- \+/\- *lemma* continuous_const

Modified topology/infinite_sum.lean
- \- *lemma* exists_is_sum_of_is_sum
- \+ *def* has_sum
- \+ *lemma* has_sum_add
- \+ *lemma* has_sum_iff_has_sum_ne_zero
- \+ *lemma* has_sum_mul_left
- \+ *lemma* has_sum_mul_right
- \+ *lemma* has_sum_neg
- \+ *lemma* has_sum_of_has_sum_of_sub
- \+ *lemma* has_sum_spec
- \+ *lemma* has_sum_sub
- \+ *lemma* has_sum_sum
- \+ *lemma* has_sum_sum_of_ne_finset_zero
- \+ *lemma* has_sum_zero
- \+/\- *lemma* is_sum_hom
- \+ *lemma* is_sum_mul_left
- \+ *lemma* is_sum_mul_right
- \+ *lemma* is_sum_neg
- \+ *lemma* is_sum_sub
- \+ *lemma* is_sum_sum_of_ne_finset_zero
- \- *lemma* is_sum_sum_of_ne_zero
- \+ *lemma* is_sum_tsum
- \+ *lemma* is_sum_unique
- \+ *def* tsum
- \+ *lemma* tsum_add
- \+ *lemma* tsum_eq_is_sum
- \+ *lemma* tsum_mul_left
- \+ *lemma* tsum_mul_right
- \+ *lemma* tsum_neg
- \+ *lemma* tsum_sub
- \+ *lemma* tsum_sum
- \+ *lemma* tsum_zero

Modified topology/real.lean


Modified topology/topological_structures.lean
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* tendsto_mul



## [2017-09-05 19:48:25-04:00](https://github.com/leanprover-community/mathlib/commit/1e4f6cc)
chore(data/seq,data/hash_map): adapt to changes in injection tactic (https://github.com/leanprover/lean/commit/8a10d4c72c948cd1b7af02f316e553e202b1368f)
#### Estimated changes
Modified data/hash_map.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean




## [2017-09-05 19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/c6747ee)
chore(topology/uniform_space): use Type* and Sort*
#### Estimated changes
Modified topology/uniform_space.lean
- \+/\- *def* id_rel
- \+/\- *lemma* supr_uniformity
- \+/\- *lemma* to_topological_space_supr
- \+/\- *lemma* uniform_embedding_prod
- \+/\- *lemma* uniform_embedding_subtype_emb
- \+/\- *lemma* uniform_extend_subtype



## [2017-09-05 19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/7c38416)
feat(data/sigma,data/finset,algebra): add support for the sigma type to finset and big operators
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_sigma

Modified data/finset/fold.lean
- \+ *lemma* finset.mem_sigma_iff
- \+ *lemma* finset.sigma_mono
- \+ *lemma* heq_iff_eq

Added data/sigma/basic.lean
- \+ *def* sigma.map
- \+ *lemma* sigma.mk_eq_mk_iff

Added data/sigma/default.lean


Modified topology/infinite_sum.lean
- \+/\- *lemma* is_sum_sigma



## [2017-09-05 19:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/7d8e3f3)
feat(algebra): add ordered (non-cancellative) additive monoid; use for sum-big operator
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.sum_eq_zero_iff_of_nonneg
- \+ *lemma* finset.sum_le_sum'
- \+ *lemma* finset.sum_le_sum_of_ne_zero
- \+ *lemma* finset.sum_le_sum_of_subset
- \+ *lemma* finset.sum_le_sum_of_subset_of_nonneg
- \+ *lemma* finset.sum_le_zero'
- \+ *lemma* finset.zero_le_sum'

Added algebra/ordered_monoid.lean
- \+ *lemma* add_eq_zero_iff
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \+ *lemma* add_le_add'
- \+ *lemma* add_le_add_left'
- \+ *lemma* add_le_add_right'
- \+ *lemma* add_le_of_le_of_nonpos'
- \+ *lemma* add_le_of_nonpos_of_le'
- \+ *lemma* add_lt_of_lt_of_neg'
- \+ *lemma* add_lt_of_lt_of_nonpos'
- \+ *lemma* add_lt_of_neg_of_lt'
- \+ *lemma* add_lt_of_nonpos_of_lt'
- \+ *lemma* add_neg'
- \+ *lemma* add_neg_of_neg_of_nonpos'
- \+ *lemma* add_neg_of_nonpos_of_neg'
- \+ *lemma* add_nonneg'
- \+ *lemma* add_nonpos'
- \+ *lemma* add_pos'
- \+ *lemma* add_pos_of_nonneg_of_pos'
- \+ *lemma* add_pos_of_pos_of_nonneg'
- \+ *lemma* le_add_of_le_of_nonneg'
- \+ *lemma* le_add_of_nonneg_left'
- \+ *lemma* le_add_of_nonneg_of_le'
- \+ *lemma* le_add_of_nonneg_right'
- \+ *lemma* le_iff_exists_add
- \+ *lemma* lt_add_of_lt_of_nonneg'
- \+ *lemma* lt_add_of_lt_of_pos'
- \+ *lemma* lt_add_of_nonneg_of_lt'
- \+ *lemma* lt_add_of_pos_of_lt'
- \+ *lemma* lt_of_add_lt_add_left'
- \+ *lemma* lt_of_add_lt_add_right'
- \+ *lemma* zero_le



## [2017-09-05 15:09:41-04:00](https://github.com/leanprover-community/mathlib/commit/fde992f)
chore(*): use `induction generalizing`
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* int.of_nat_add_neg_succ_of_nat_of_ge
- \+/\- *theorem* int.of_nat_add_neg_succ_of_nat_of_lt

Modified data/list/basic.lean


Modified data/list/comb.lean


Modified data/num/lemmas.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean




## [2017-09-05 15:05:29-04:00](https://github.com/leanprover-community/mathlib/commit/a8a1a91)
chore(topology/uniform_space): simplify proof (suggested by @gebner)
#### Estimated changes
Modified topology/uniform_space.lean




## [2017-09-05 14:15:01-04:00](https://github.com/leanprover-community/mathlib/commit/ba95269)
feat(topology): introduce infinite sums on topological monoids
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_bind
- \+ *lemma* finset.prod_comm
- \+ *lemma* finset.prod_product
- \+ *lemma* finset.prod_subset

Modified data/finset/basic.lean
- \+ *theorem* finset.filter_false
- \+ *theorem* finset.filter_filter
- \+ *theorem* finset.filter_inter_filter_neg_eq
- \+ *theorem* finset.filter_subset
- \+ *theorem* finset.filter_union
- \+ *theorem* finset.filter_union_filter_neg_eq
- \+ *lemma* finset.image_empty
- \+ *lemma* finset.image_eq_empty_iff
- \+ *lemma* finset.image_filter
- \+ *lemma* finset.image_insert
- \+ *lemma* finset.image_inter
- \+ *lemma* finset.image_singleton
- \+ *lemma* finset.image_subset_image
- \+ *lemma* finset.image_union
- \+ *theorem* finset.inter_subset_left
- \+ *theorem* finset.inter_subset_right
- \+ *theorem* finset.mem_filter_iff
- \+ *lemma* finset.mem_image_iff
- \+ *theorem* finset.mem_sdiff_iff
- \+ *theorem* finset.mem_to_finset_iff
- \+ *lemma* finset.sdiff_inter_self
- \+ *lemma* finset.sdiff_union_of_subset
- \+ *theorem* finset.subset_inter
- \+ *theorem* finset.subset_union_left
- \+ *theorem* finset.subset_union_right
- \+ *theorem* finset.union_idempotent
- \+ *theorem* finset.union_subset
- \- *def* finset
- \+/\- *def* nodup_list
- \+ *def* {u}

Modified data/finset/fold.lean
- \+ *lemma* finset.bind_empty
- \+ *lemma* finset.bind_image
- \+ *lemma* finset.bind_insert
- \+ *lemma* finset.fold_insert_idem
- \+ *lemma* finset.image_bind
- \+ *lemma* finset.mem_bind_iff
- \+ *lemma* finset.mem_product_iff

Modified data/list/basic.lean
- \+ *theorem* list.mem_filter_iff

Modified logic/basic.lean


Modified order/complete_lattice.lean
- \+ *lemma* lattice.infi_top
- \+ *lemma* lattice.supr_bot

Added topology/infinite_sum.lean
- \+ *lemma* at_top_ne_bot
- \+ *lemma* cauchy_iff
- \+ *lemma* exists_is_sum_of_is_sum
- \+ *lemma* filter.mem_infi_sets_finset
- \+ *theorem* forall_and_distrib'
- \+ *def* is_sum
- \+ *lemma* is_sum_add
- \+ *lemma* is_sum_hom
- \+ *lemma* is_sum_iff_is_sum
- \+ *lemma* is_sum_iff_is_sum_of_ne_zero
- \+ *lemma* is_sum_of_is_sum
- \+ *lemma* is_sum_of_is_sum_ne_zero
- \+ *lemma* is_sum_of_iso
- \+ *lemma* is_sum_sigma
- \+ *lemma* is_sum_sum
- \+ *lemma* is_sum_sum_of_ne_zero
- \+ *lemma* is_sum_zero
- \+ *lemma* map_at_top_eq
- \+ *lemma* mem_at_top_iff
- \+ *lemma* mem_closure_of_tendsto
- \+ *lemma* tendsto_finset_image_at_top_at_top

Modified topology/topological_structures.lean
- \+ *lemma* tendsto_add'
- \+ *lemma* tendsto_sum
- \+ *lemma* uniform_continuous_add'
- \+ *lemma* uniform_continuous_add
- \+ *lemma* uniform_continuous_neg'
- \+ *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous_sub'
- \+ *lemma* uniform_continuous_sub

Modified topology/uniform_space.lean
- \+ *lemma* uniform_continuous_id



## [2017-09-05 12:47:49-05:00](https://github.com/leanprover-community/mathlib/commit/6c321fe)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-09-05 10:33:20-04:00](https://github.com/leanprover-community/mathlib/commit/c7a3c75)
fix(data/seq): option_bind, option_map -> option.bind, option.map (changed in Lean)
#### Estimated changes
Modified data/seq/parallel.lean


Modified data/seq/seq.lean
- \+/\- *theorem* seq.map_nth

Modified data/seq/wseq.lean
- \+/\- *def* wseq.map



## [2017-09-04 12:33:01-04:00](https://github.com/leanprover-community/mathlib/commit/80e1474)
fix(logic/basic): fix simp performance issue
Having `forall_true_iff'` as a simp lemma caused way too much backtracking, so only the 2 and 3 implication versions are added as simp lemmas, and the user can add `forall_true_iff'` to their simp set if they need to reduce more.
#### Estimated changes
Modified logic/basic.lean
- \+ *theorem* forall_2_true_iff
- \+ *theorem* forall_3_true_iff
- \+/\- *theorem* forall_true_iff'
- \+ *theorem* imp.swap

Modified order/filter.lean




## [2017-09-03 23:13:00-04:00](https://github.com/leanprover-community/mathlib/commit/086ac36)
feat(tactic/interactive): simpf tactic, more logic refactor
#### Estimated changes
Modified logic/basic.lean
- \- *theorem* imp_of_not_or
- \+ *theorem* not_and'
- \+ *theorem* not_and
- \- *theorem* not_and_iff_imp'
- \- *theorem* not_and_iff_imp
- \+ *theorem* not_and_not_right

Modified order/zorn.lean


Modified tactic/interactive.lean


Modified topology/ennreal.lean


Modified topology/topological_space.lean


Modified topology/uniform_space.lean




## [2017-09-03 20:55:23-04:00](https://github.com/leanprover-community/mathlib/commit/8faac5f)
refactor(logic/basic): refactor logic theorems
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* exists_false

Modified data/finset/basic.lean
- \- *theorem* finset.eq_of_mem_singleton
- \- *theorem* finset.eq_of_singleton_eq
- \+/\- *theorem* finset.mem_singleton
- \- *theorem* finset.mem_singleton_iff
- \- *theorem* finset.mem_singleton_of_eq
- \+ *theorem* finset.mem_singleton_self
- \+ *theorem* finset.singleton_inj
- \+ *theorem* finset.subset_iff
- \- *theorem* finset.subset_of_forall
- \- *lemma* or_self_or
- \- *theorem* perm_insert_cons_of_not_mem

Modified data/finset/fold.lean
- \+/\- *lemma* finset.fold_congr
- \+/\- *lemma* list.map_congr

Modified data/list/basic.lean


Modified data/list/comb.lean


Modified data/list/perm.lean


Modified data/list/set.lean


Modified data/seq/seq.lean


Modified data/set/basic.lean
- \+ *theorem* set.ball_empty_iff
- \+ *theorem* set.ball_image_iff
- \+ *theorem* set.ball_image_of_ball
- \+ *theorem* set.ball_insert_iff
- \- *theorem* set.bounded_forall_empty_iff
- \- *theorem* set.bounded_forall_image_iff
- \- *theorem* set.bounded_forall_image_of_bounded_forall
- \- *theorem* set.bounded_forall_insert_iff
- \+ *theorem* set.mem_union
- \- *theorem* set.mem_union_iff
- \+ *lemma* set.not_not_mem
- \- *lemma* set.not_not_mem_iff

Modified data/set/lattice.lean


Modified logic/basic.lean
- \+ *theorem* and.imp_left
- \+ *theorem* and.imp_right
- \- *theorem* and_distrib
- \- *theorem* and_distrib_right
- \+/\- *theorem* and_iff_not_or_not
- \+ *theorem* and_imp
- \- *theorem* and_imp_iff
- \- *theorem* and_implies_iff
- \- *theorem* and_implies_left
- \- *theorem* and_implies_right
- \- *theorem* and_not_of_not_implies
- \- *theorem* and_of_and_of_imp_left
- \- *theorem* and_of_and_of_imp_right
- \- *theorem* and_of_and_of_implies_of_implies
- \+ *theorem* and_or_distrib_left
- \+ *theorem* and_or_distrib_right
- \+ *theorem* ball.imp_left
- \+ *theorem* ball.imp_right
- \+ *theorem* ball_and_distrib
- \+ *theorem* ball_congr
- \+ *theorem* ball_of_forall
- \+ *theorem* ball_true_iff
- \+ *theorem* bex.elim
- \+ *theorem* bex.imp_left
- \+ *theorem* bex.imp_right
- \+ *theorem* bex.intro
- \+ *theorem* bex_congr
- \+ *theorem* bex_def
- \+ *theorem* bex_imp_distrib
- \+ *theorem* bex_of_exists
- \+ *theorem* bex_or_distrib
- \- *theorem* bexists.elim
- \- *theorem* bexists.intro
- \- *theorem* bexists_congr
- \- *theorem* bexists_def
- \- *theorem* bexists_implies_distrib
- \- *theorem* bexists_implies_of_bforall_implies
- \- *theorem* bexists_not_of_not_bforall
- \- *theorem* bexists_of_bexists
- \- *theorem* bexists_of_exists
- \- *theorem* bexists_or_distrib
- \- *theorem* bforall_and_distrib
- \- *theorem* bforall_congr
- \- *theorem* bforall_implies_of_bexists_implies
- \- *theorem* bforall_not_of_not_bexists
- \- *theorem* bforall_of_bforall
- \- *theorem* bforall_of_forall
- \- *theorem* bforall_true_iff
- \- *theorem* classical.bexists_not_of_not_bforall
- \- *theorem* classical.exists_not_of_not_forall
- \+ *theorem* classical.not_ball
- \- *theorem* classical.not_bforall_iff_bexists_not
- \+ *theorem* classical.not_forall
- \- *theorem* classical.not_forall_iff
- \+ *def* decidable_of_iff'
- \+ *def* decidable_of_iff
- \+/\- *theorem* eq_iff_le_and_le
- \+ *theorem* exists_const
- \+ *theorem* exists_eq'
- \+ *theorem* exists_eq
- \+ *theorem* exists_eq_right'
- \+ *theorem* exists_eq_right
- \+ *theorem* exists_false
- \+ *theorem* exists_imp_distrib
- \- *theorem* exists_implies_distrib
- \- *theorem* exists_implies_of_forall_implies
- \- *theorem* exists_not_of_not_forall
- \+ *theorem* exists_of_bex
- \- *theorem* exists_of_bexists
- \+/\- *theorem* exists_of_exists
- \+/\- *theorem* exists_or_distrib
- \- *theorem* exists_p_iff_p
- \+ *theorem* exists_prop
- \- *theorem* exists_prop_iff
- \+ *theorem* exists_swap
- \+/\- *theorem* forall_and_distrib
- \+ *theorem* forall_const
- \+ *theorem* forall_eq'
- \+/\- *theorem* forall_eq
- \- *theorem* forall_implies_of_exists_implies
- \+ *theorem* forall_of_ball
- \- *theorem* forall_of_bforall
- \+/\- *theorem* forall_of_forall
- \+ *theorem* forall_or_of_or_forall
- \- *theorem* forall_p_iff_p
- \+ *theorem* forall_swap
- \+ *theorem* forall_true_iff'
- \+/\- *theorem* forall_true_iff
- \+ *theorem* iff_def'
- \+/\- *theorem* iff_def
- \+ *theorem* iff_false_left
- \+ *theorem* iff_false_right
- \+ *theorem* iff_not_comm
- \+ *theorem* iff_of_false
- \+ *theorem* iff_of_true
- \+ *theorem* iff_true_left
- \+ *theorem* iff_true_right
- \+ *theorem* imp_and_distrib
- \+ *theorem* imp_false
- \+ *theorem* imp_iff_not_or
- \+ *theorem* imp_iff_right
- \+ *theorem* imp_intro
- \+ *theorem* imp_not_comm
- \+ *theorem* imp_of_not_or
- \+ *theorem* imp_self
- \+ *theorem* imp_true_iff
- \- *theorem* implies_and_iff
- \- *theorem* implies_false_iff
- \- *theorem* implies_iff
- \- *theorem* implies_iff_not_or
- \- *theorem* implies_intro
- \- *theorem* implies_of_not_or
- \- *theorem* implies_self
- \+ *theorem* not.elim
- \+ *theorem* not.imp_symm
- \+ *theorem* not_and_distrib'
- \+ *theorem* not_and_distrib
- \- *theorem* not_and_iff
- \+ *theorem* not_and_iff_imp'
- \+ *theorem* not_and_iff_imp
- \- *theorem* not_and_iff_imp_not
- \- *theorem* not_and_not_of_not_or
- \+ *theorem* not_ball
- \+ *theorem* not_ball_of_bex_not
- \+ *theorem* not_bex
- \- *theorem* not_bexists_iff_bforall_not
- \- *theorem* not_bexists_of_bforall_not
- \- *theorem* not_bforall_iff_bexists_not
- \- *theorem* not_bforall_of_bexists_not
- \+ *theorem* not_exists
- \- *theorem* not_exists_iff
- \+ *theorem* not_exists_not
- \+ *theorem* not_forall
- \- *theorem* not_forall_iff
- \+ *theorem* not_forall_not
- \+/\- *theorem* not_forall_of_exists_not
- \+ *theorem* not_iff_comm
- \+ *theorem* not_iff_not
- \+ *theorem* not_imp
- \+ *theorem* not_imp_comm
- \- *theorem* not_imp_iff_not_imp
- \+ *theorem* not_imp_not
- \+ *theorem* not_imp_of_and_not
- \- *theorem* not_implies_iff
- \- *theorem* not_implies_of_and_not
- \+ *theorem* not_not
- \- *theorem* not_not_elim
- \- *theorem* not_not_iff
- \+ *theorem* not_not_of_not_imp
- \- *theorem* not_not_of_not_implies
- \+ *theorem* not_of_not_imp
- \- *theorem* not_of_not_implies
- \+ *theorem* not_or_distrib
- \- *theorem* not_or_iff
- \- *theorem* not_or_not_of_not_and'
- \- *theorem* not_or_not_of_not_and
- \+ *theorem* not_or_of_imp
- \- *theorem* not_or_of_implies
- \- *theorem* not_or_of_not_and_not
- \+ *theorem* of_not_imp
- \- *theorem* of_not_implies
- \+ *theorem* of_not_not
- \+ *theorem* or_and_distrib_left
- \+ *theorem* or_and_distrib_right
- \- *theorem* or_distrib
- \- *theorem* or_distrib_right
- \+/\- *theorem* or_iff_not_and_not
- \+ *theorem* or_iff_not_imp_left
- \+ *theorem* or_iff_not_imp_right
- \- *theorem* or_iff_or
- \+ *theorem* or_imp_distrib
- \- *theorem* or_imp_iff_and_imp
- \- *theorem* or_implies_distrib
- \- *theorem* or_of_not_implies'
- \- *theorem* or_of_not_implies
- \+ *theorem* or_of_or_of_imp_left
- \+ *theorem* or_of_or_of_imp_of_imp
- \+ *theorem* or_of_or_of_imp_right
- \- *theorem* or_of_or_of_implies_left
- \- *theorem* or_of_or_of_implies_of_implies
- \- *theorem* or_of_or_of_implies_right
- \- *theorem* or_resolve_left
- \- *theorem* or_resolve_right
- \+/\- *theorem* prod.exists
- \+/\- *theorem* prod.forall
- \+/\- *theorem* prod.mk.inj_iff
- \- *lemma* {u
- \- *theorem* {u}

Modified order/bounds.lean


Modified order/filter.lean


Modified order/zorn.lean


Modified tactic/finish.lean
- \+/\- *theorem* auto.classical.implies_iff_not_or
- \+/\- *theorem* auto.not_and_eq
- \+/\- *theorem* auto.not_exists_eq
- \+/\- *theorem* auto.not_forall_eq
- \+/\- *theorem* auto.not_implies_eq
- \+/\- *theorem* auto.not_not_eq
- \+/\- *theorem* auto.not_or_eq

Modified topology/continuity.lean


Modified topology/ennreal.lean


Modified topology/measurable_space.lean


Modified topology/metric_space.lean
- \+ *theorem* continuous_dist'
- \- *lemma* continuous_dist'
- \+ *theorem* continuous_dist
- \- *lemma* continuous_dist
- \+ *theorem* dist_comm
- \- *lemma* dist_comm
- \+ *theorem* dist_eq_zero_iff
- \- *lemma* dist_eq_zero_iff
- \+ *theorem* dist_nonneg
- \- *lemma* dist_nonneg
- \+ *theorem* dist_pos_of_ne
- \- *lemma* dist_pos_of_ne
- \+ *theorem* dist_self
- \- *lemma* dist_self
- \+ *theorem* dist_triangle
- \- *lemma* dist_triangle
- \+ *theorem* eq_of_dist_eq_zero
- \- *lemma* eq_of_dist_eq_zero
- \+ *theorem* eq_of_forall_dist_le
- \- *lemma* eq_of_forall_dist_le
- \+ *theorem* exists_subtype
- \- *lemma* exists_subtype
- \+ *theorem* ne_of_dist_pos
- \- *lemma* ne_of_dist_pos
- \+ *theorem* open_ball_subset_open_ball_of_le
- \- *lemma* open_ball_subset_open_ball_of_le
- \+ *theorem* tendsto_dist
- \- *lemma* tendsto_dist
- \+ *theorem* uniform_continuous_dist'
- \- *lemma* uniform_continuous_dist'
- \+ *theorem* uniform_continuous_dist
- \- *lemma* uniform_continuous_dist
- \+ *theorem* uniformity_dist'
- \- *lemma* uniformity_dist'
- \+ *theorem* uniformity_dist
- \- *lemma* uniformity_dist
- \+ *theorem* zero_eq_dist_iff
- \- *lemma* zero_eq_dist_iff

Modified topology/real.lean


Modified topology/topological_space.lean


Modified topology/topological_structures.lean


Modified topology/uniform_space.lean




## [2017-09-02 19:56:17-04:00](https://github.com/leanprover-community/mathlib/commit/74cfa93)
fix(data/list/perm): fix broken match
This reverts commit 3d817686fdb02eba0f51ab303a4d5b50ac2a9f5e.
#### Estimated changes
Modified data/list/perm.lean


