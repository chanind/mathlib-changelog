## [2017-09-28 19:28:00-04:00](https://github.com/leanprover-community/mathlib/commit/e7b2a0f)
style(analysis): renames the topology directory to analysis and introduced topology and measure_theory subdirectories
#### Estimated changes
renamed topology/ennreal.lean to analysis/ennreal.lean

renamed topology/limits.lean to analysis/limits.lean
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg

renamed topology/borel_space.lean to analysis/measure_theory/borel_space.lean

renamed topology/lebesgue_measure.lean to analysis/measure_theory/lebesgue_measure.lean

renamed topology/measurable_space.lean to analysis/measure_theory/measurable_space.lean

renamed topology/measure.lean to analysis/measure_theory/measure_space.lean

renamed topology/outer_measure.lean to analysis/measure_theory/outer_measure.lean

renamed topology/metric_space.lean to analysis/metric_space.lean

renamed topology/of_nat.lean to analysis/of_nat.lean

renamed topology/real.lean to analysis/real.lean

renamed topology/continuity.lean to analysis/topology/continuity.lean

renamed topology/infinite_sum.lean to analysis/topology/infinite_sum.lean
- \- *lemma* has_sum_of_absolute_convergence
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

renamed topology/topological_space.lean to analysis/topology/topological_space.lean

renamed topology/topological_structures.lean to analysis/topology/topological_structures.lean

renamed topology/uniform_space.lean to analysis/topology/uniform_space.lean



## [2017-09-28 19:16:36-04:00](https://github.com/leanprover-community/mathlib/commit/afefdcb)
chore(topology): move general theorems to the corresponding theories
#### Estimated changes
created algebra/default.lean

modified algebra/field.lean
- \+ *lemma* one_lt_inv
- \+ *lemma* inv_le_inv

modified algebra/ordered_group.lean
- \+ *lemma* sub_lt_iff
- \+ *lemma* lt_sub_iff

modified algebra/ordered_ring.lean
- \+ *lemma* one_lt_two

modified algebra/ring.lean
- \+ *lemma* add_div
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* neg_inv

created data/quot.lean
- \+ *lemma* forall_quotient_iff
- \+ *lemma* quot_mk_image_univ_eq

modified data/set/basic.lean
- \+ *lemma* image_preimage_eq_inter_rng

created data/set/disjointed.lean
- \+ *lemma* disjoint_disjointed
- \+ *lemma* disjointed_Union
- \+ *lemma* disjointed_induct
- \+ *lemma* disjointed_of_mono
- \+ *def* pairwise
- \+ *def* disjointed

modified data/set/lattice.lean
- \+ *lemma* subtype_val_image

modified data/set/prod.lean
- \+ *lemma* univ_prod_univ

created data/subtype.lean
- \+ *lemma* forall_subtype
- \+ *theorem* exists_subtype

modified order/complete_lattice.lean
- \+ *lemma* binfi_inf
- \+ *lemma* supr_bool_eq
- \+ *lemma* infi_bool_eq

modified order/filter.lean
- \+/\- *lemma* mem_top_sets_iff
- \+ *lemma* mem_infi_sets_finset
- \+ *lemma* inf_principal_eq_bot
- \+ *lemma* mem_at_top
- \+ *lemma* at_top_ne_bot
- \+ *lemma* mem_at_top_iff
- \+ *lemma* map_at_top_eq
- \+ *lemma* tendsto_finset_image_at_top_at_top
- \+/\- *lemma* mem_top_sets_iff
- \+/\- *def* at_top
- \+/\- *def* at_bot
- \+/\- *def* at_top
- \+/\- *def* at_bot

modified topology/borel_space.lean
- \+ *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \+ *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \+ *lemma* borel_eq_generate_from_Iio_of_rat

modified topology/continuity.lean
- \+ *lemma* continuous_if
- \- *lemma* image_preimage_eq_inter_rng
- \- *lemma* subtype.val_image
- \- *lemma* univ_prod_univ

modified topology/ennreal.lean
- \- *lemma* supr_bool_eq

modified topology/infinite_sum.lean
- \- *lemma* add_div
- \- *lemma* mem_at_top
- \- *lemma* mem_infi_sets_finset
- \- *lemma* mem_closure_of_tendsto
- \- *lemma* cauchy_iff
- \- *lemma* at_top_ne_bot
- \- *lemma* mem_at_top_iff
- \- *lemma* map_at_top_eq
- \- *lemma* tendsto_finset_image_at_top_at_top
- \- *theorem* forall_and_distrib'

modified topology/lebesgue_measure.lean
- \- *lemma* inv_le_inv
- \- *lemma* min_of_rat_of_rat
- \- *lemma* max_of_rat_of_rat
- \- *lemma* is_topological_basis_of_open_of_nhds
- \- *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \- *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \- *lemma* borel_eq_generate_from_Iio_of_rat

modified topology/limits.lean
- \- *lemma* one_lt_inv
- \- *lemma* div_eq_mul_inv
- \- *lemma* neg_inv
- \- *lemma* of_nat_add
- \- *lemma* of_nat_one
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_sub
- \- *lemma* int_of_nat_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* zero_le_of_nat
- \- *lemma* of_nat_pos
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* exists_lt_of_nat
- \- *def* of_nat

modified topology/measurable_space.lean
- \- *lemma* disjoint_disjointed
- \- *lemma* disjointed_Union
- \- *lemma* disjointed_induct
- \- *lemma* disjointed_of_mono
- \- *def* pairwise
- \- *def* disjointed

modified topology/metric_space.lean
- \- *theorem* exists_subtype

created topology/of_nat.lean
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_sub
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* zero_le_of_nat
- \+ *lemma* of_nat_pos
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* exists_lt_of_nat
- \+ *def* of_nat

modified topology/real.lean
- \+ *lemma* min_of_rat_of_rat
- \+ *lemma* max_of_rat_of_rat
- \- *lemma* quot_mk_image_univ_eq
- \- *lemma* forall_subtype_iff
- \- *lemma* one_lt_two
- \- *lemma* sub_lt_iff
- \- *lemma* lt_sub_iff
- \- *lemma* orderable_topology_of_nhds_abs

modified topology/topological_space.lean
- \+ *lemma* closure_compl
- \+ *lemma* interior_compl
- \+ *lemma* frontier_eq_closure_inter_closure
- \+ *lemma* mem_closure_of_tendsto
- \+ *lemma* is_topological_basis_of_open_of_nhds
- \+ *def* frontier

modified topology/topological_structures.lean
- \+ *lemma* orderable_topology_of_nhds_abs
- \- *lemma* binfi_inf
- \- *lemma* inf_principal_eq_bot
- \- *lemma* closure_compl
- \- *lemma* interior_compl
- \- *lemma* frontier_eq_closure_inter_closure
- \- *lemma* continuous_if
- \- *def* frontier

modified topology/uniform_space.lean
- \+ *lemma* cauchy_iff
- \- *lemma* forall_quotient_iff



## [2017-09-28 18:16:44-04:00](https://github.com/leanprover-community/mathlib/commit/7e7c6f5)
feat(topology): various additions (preparation for the nonnegative integral)
#### Estimated changes
modified data/set/countable.lean

modified data/set/finite.lean
- \+ *lemma* finite_prod

modified data/set/prod.lean
- \+ *lemma* prod_empty
- \+ *lemma* empty_prod
- \+ *lemma* insert_prod
- \+ *lemma* prod_insert

modified topology/borel_space.lean
- \+/\- *lemma* measurable_of_continuous
- \+/\- *lemma* borel_prod
- \+/\- *lemma* measurable_of_continuous2
- \+/\- *lemma* measurable_add
- \+/\- *lemma* measurable_neg
- \+/\- *lemma* measurable_sub
- \+/\- *lemma* measurable_mul
- \+/\- *lemma* measurable_of_continuous
- \+/\- *lemma* borel_prod
- \+/\- *lemma* measurable_of_continuous2
- \+/\- *lemma* measurable_add
- \+/\- *lemma* measurable_neg
- \+/\- *lemma* measurable_sub
- \+/\- *lemma* measurable_mul

modified topology/ennreal.lean

modified topology/infinite_sum.lean
- \+ *lemma* tsum_eq_single



## [2017-09-28 18:08:23-04:00](https://github.com/leanprover-community/mathlib/commit/c3aeb53)
feat(topology): add Lebesgue measure
#### Estimated changes
modified algebra/field.lean
- \+ *lemma* inv_lt_one

modified data/rat.lean

modified data/set/basic.lean
- \+ *lemma* range_eq_image

modified data/set/countable.lean
- \+ *lemma* countable_bUnion
- \+/\- *lemma* countable_Union
- \+ *lemma* countable_Union_Prop
- \+/\- *lemma* countable_Union

modified data/set/default.lean

created data/set/intervals.lean
- \+ *lemma* Ioo_eq_empty_of_ge
- \+ *lemma* Ico_eq_empty_iff
- \+ *lemma* Ico_eq_empty
- \+ *lemma* Ico_subset_Ico_iff
- \+ *lemma* Ico_eq_Ico_iff
- \+ *lemma* Ico_sdiff_Iio_eq
- \+ *lemma* Ico_inter_Iio_eq
- \+ *lemma* Ioo_inter_Ioo
- \+ *def* Ioo
- \+ *def* Ico
- \+ *def* Iio

modified data/set/lattice.lean
- \+ *lemma* subset.antisymm_iff
- \+ *lemma* union_of_subset_right
- \+ *theorem* sdiff_union_same
- \+ *theorem* sdiff_inter_same

modified logic/basic.lean
- \+ *lemma* or_not

modified order/bounds.lean
- \+ *lemma* ne_empty_of_is_lub
- \+ *lemma* ne_empty_of_is_glb

modified order/complete_lattice.lean
- \+ *lemma* Inf_lt_iff
- \+ *lemma* lt_Sup_iff
- \+ *lemma* Sup_eq_top
- \+ *lemma* lt_supr_iff
- \+ *lemma* infi_lt_iff

modified topology/borel_space.lean
- \+ *lemma* is_measurable_Ioo
- \+ *lemma* is_measurable_Iio
- \+ *lemma* is_measurable_Ico

modified topology/continuity.lean
- \+ *lemma* prod_generate_from_generate_from_eq

modified topology/ennreal.lean
- \+ *lemma* supr_bool_eq
- \+ *lemma* of_real_le_of_real
- \+ *lemma* supr_of_real
- \+ *lemma* infi_of_real
- \+/\- *lemma* Inf_add
- \+/\- *lemma* Sup_add
- \+/\- *lemma* supr_add
- \+ *lemma* infi_add
- \+ *lemma* add_infi
- \+ *lemma* infi_add_infi
- \+ *lemma* infi_sum
- \+ *lemma* infty_sub_of_real
- \+ *lemma* of_real_sub_of_real
- \+ *lemma* add_sub_self
- \+ *lemma* sub_supr
- \- *lemma* Inf_lt_iff
- \- *lemma* lt_Sup_iff
- \- *lemma* lt_supr_iff
- \- *lemma* infi_lt_iff
- \- *lemma* Sup_eq_top
- \+/\- *lemma* Inf_add
- \+/\- *lemma* Sup_add
- \+/\- *lemma* supr_add
- \- *lemma* le_sub_iff_add_le

modified topology/lebesgue_measure.lean
- \+ *lemma* inv_le_inv
- \+ *lemma* min_of_rat_of_rat
- \+ *lemma* max_of_rat_of_rat
- \+ *lemma* is_topological_basis_of_open_of_nhds
- \+ *lemma* is_topological_basis_Ioo_of_rat_of_rat
- \+ *lemma* borel_eq_generate_from_Ioo_of_rat_of_rat
- \+ *lemma* borel_eq_generate_from_Iio_of_rat
- \+ *lemma* tendsto_of_nat_at_top_at_top
- \+ *lemma* lebesgue_Ico
- \+ *lemma* lebesgue_Ioo
- \+ *lemma* lebesgue_singleton
- \- *lemma* subset.antisymm_iff
- \- *lemma* Ico_eq_empty_iff
- \- *lemma* Ico_eq_empty
- \- *lemma* Ico_subset_Ico_iff
- \- *lemma* Ico_eq_Ico_iff
- \- *lemma* Ico_sdiff_Iio_eq
- \- *lemma* Ico_inter_Iio_eq
- \- *lemma* nhds_principal_ne_top_of_is_lub
- \- *lemma* is_lub_of_is_lub_of_tendsto
- \+ *def* lebesgue
- \- *def* Ico
- \- *def* Iio

modified topology/limits.lean
- \+ *lemma* of_nat_pos

modified topology/measurable_space.lean
- \+ *lemma* disjointed_of_mono
- \+ *lemma* comap_generate_from
- \+ *lemma* generate_from_le_generate_from
- \+ *lemma* generate_from_sup_generate_from
- \+ *lemma* measurable_subtype_val
- \+ *lemma* measurable_subtype_mk
- \+ *lemma* measurable_fst
- \+ *lemma* measurable_snd
- \+ *lemma* measurable_prod
- \+ *lemma* measurable_prod_mk
- \+ *lemma* is_measurable_set_prod

modified topology/measure.lean
- \+/\- *lemma* measure_empty
- \+/\- *lemma* measure_mono
- \+ *lemma* measure_Union_le_tsum_nat
- \+/\- *lemma* measure_union
- \+ *lemma* measure_sdiff
- \+ *lemma* measure_Union_eq_supr_nat
- \+ *lemma* measure_Inter_eq_infi_nat
- \- *lemma* supr_bool_eq
- \- *lemma* measure_eq_measure_of
- \+/\- *lemma* measure_empty
- \+/\- *lemma* measure_union
- \+/\- *lemma* measure_mono
- \- *lemma* measure_Union_le_nat
- \+ *def* outer_measure.to_measure
- \- *def* measure_space.measure

modified topology/outer_measure.lean
- \+ *lemma* caratheodory_is_measurable_eq
- \+ *lemma* caratheodory_is_measurable
- \- *lemma* inv_lt_one
- \- *lemma* or_not
- \- *lemma* infi_add
- \- *lemma* add_infi
- \- *lemma* infi_add_infi
- \- *lemma* infi_sum
- \- *lemma* space_is_measurable_eq
- \- *lemma* inf_space_is_measurable
- \- *def* inf
- \- *def* space
- \- *def* measure

modified topology/real.lean
- \+ *lemma* exists_gt_of_rat
- \+ *lemma* exists_lt_of_rat_of_rat_gt

modified topology/topological_space.lean
- \+ *lemma* induced_le_iff_le_coinduced
- \+ *lemma* is_topological_basis_of_subbasis
- \+ *lemma* mem_nhds_of_is_topological_basis
- \+ *def* is_topological_basis

modified topology/topological_structures.lean
- \+ *lemma* closure_compl
- \+ *lemma* interior_compl
- \+ *lemma* frontier_eq_closure_inter_closure
- \+ *lemma* continuous_if
- \+ *lemma* continuous_sub'
- \+ *lemma* closure_le_eq
- \+ *lemma* is_open_Ioo
- \+ *lemma* is_open_Iio
- \+ *lemma* frontier_le_subset_eq
- \+ *lemma* continuous_max
- \+ *lemma* continuous_min
- \+ *lemma* tendsto_max
- \+ *lemma* tendsto_min
- \+ *lemma* nhds_principal_ne_bot_of_is_lub
- \+ *lemma* nhds_principal_ne_bot_of_is_glb
- \+ *lemma* is_lub_of_mem_nhds
- \+ *lemma* is_glb_of_mem_nhds
- \+ *lemma* is_lub_of_is_lub_of_tendsto
- \+ *lemma* is_glb_of_is_glb_of_tendsto
- \+ *lemma* is_glb_of_is_lub_of_tendsto
- \+ *def* frontier



## [2017-09-28 18:07:43-04:00](https://github.com/leanprover-community/mathlib/commit/4297eeb)
feat(topology): add Borel spaces
#### Estimated changes
modified data/set/basic.lean
- \- *lemma* image_subset_eq
- \- *theorem* preimage_diff
- \- *theorem* image_preimage_subset
- \- *theorem* subset_preimage_image
- \- *theorem* inter_preimage_subset
- \- *theorem* union_preimage_subset
- \- *theorem* image_union_supset

modified data/set/countable.lean
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \+ *lemma* countable_set_of_finite_subset
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton

deleted data/set/function.lean
- \- *lemma* injective_iff_inj_on_univ
- \- *lemma* surjective_iff_surj_on_univ
- \- *lemma* image_eq_of_maps_to_of_surj_on
- \- *lemma* maps_to_of_bij_on
- \- *lemma* inj_on_of_bij_on
- \- *lemma* surj_on_of_bij_on
- \- *lemma* bij_on.mk
- \- *lemma* image_eq_of_bij_on
- \- *lemma* bijective_iff_bij_on_univ
- \- *theorem* maps_to_of_eq_on
- \- *theorem* maps_to_comp
- \- *theorem* maps_to_univ_univ
- \- *theorem* image_subset_of_maps_to_of_subset
- \- *theorem* image_subset_of_maps_to
- \- *theorem* inj_on_empty
- \- *theorem* inj_on_of_eq_on
- \- *theorem* inj_on_comp
- \- *theorem* inj_on_of_inj_on_of_subset
- \- *theorem* surj_on_of_eq_on
- \- *theorem* surj_on_comp
- \- *theorem* bij_on_of_eq_on
- \- *theorem* bij_on_comp
- \- *theorem* left_inv_on_of_eq_on_left
- \- *theorem* left_inv_on_of_eq_on_right
- \- *theorem* inj_on_of_left_inv_on
- \- *theorem* left_inv_on_comp
- \- *theorem* right_inv_on_of_eq_on_left
- \- *theorem* right_inv_on_of_eq_on_right
- \- *theorem* surj_on_of_right_inv_on
- \- *theorem* right_inv_on_comp
- \- *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \- *theorem* eq_on_of_left_inv_of_right_inv
- \- *theorem* left_inv_on_of_surj_on_right_inv_on
- \- *theorem* bij_on_of_inv_on
- \- *def* maps_to
- \- *def* inj_on
- \- *def* surj_on
- \- *def* bij_on
- \- *def* left_inv_on
- \- *def* right_inv_on
- \- *def* inv_on

modified data/set/lattice.lean
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_neg
- \+ *lemma* Union_pos
- \+ *lemma* Union_neg
- \+ *lemma* Union_empty
- \+ *lemma* Inter_univ

modified order/complete_lattice.lean
- \+ *lemma* infi_pos
- \+ *lemma* infi_neg
- \+ *lemma* supr_pos
- \+ *lemma* supr_neg

created topology/borel_space.lean
- \+ *lemma* borel_eq_generate_from_of_subbasis
- \+ *lemma* borel_comap
- \+ *lemma* is_measurable_of_is_open
- \+ *lemma* is_measurable_interior
- \+ *lemma* is_measurable_of_is_closed
- \+ *lemma* is_measurable_closure
- \+ *lemma* measurable_of_continuous
- \+ *lemma* borel_prod
- \+ *lemma* measurable_of_continuous2
- \+ *lemma* measurable_add
- \+ *lemma* measurable_neg
- \+ *lemma* measurable_sub
- \+ *lemma* measurable_mul

modified topology/measurable_space.lean

modified topology/outer_measure.lean
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right
- \- *lemma* Inter_pos
- \- *lemma* Inter_neg
- \- *lemma* Union_pos
- \- *lemma* Union_neg
- \- *lemma* Union_empty
- \- *lemma* Inter_univ

modified topology/topological_space.lean
- \+ *lemma* is_open_sInter
- \+ *lemma* is_open_generated_countable_inter

modified topology/topological_structures.lean
- \- *lemma* infi_pos
- \- *lemma* infi_neg
- \- *lemma* supr_pos
- \- *lemma* supr_neg



## [2017-09-22 12:52:07-05:00](https://github.com/leanprover-community/mathlib/commit/865ba36)
feat(data/set): add functions over sets
#### Estimated changes
modified data/set/basic.lean
- \+ *lemma* image_subset_eq
- \+ *theorem* preimage_diff
- \+ *theorem* image_preimage_subset
- \+ *theorem* subset_preimage_image
- \+ *theorem* inter_preimage_subset
- \+ *theorem* union_preimage_subset
- \+ *theorem* image_union_supset

modified data/set/countable.lean
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \- *lemma* countable_set_of_finite_subset

created data/set/function.lean
- \+ *lemma* injective_iff_inj_on_univ
- \+ *lemma* surjective_iff_surj_on_univ
- \+ *lemma* image_eq_of_maps_to_of_surj_on
- \+ *lemma* maps_to_of_bij_on
- \+ *lemma* inj_on_of_bij_on
- \+ *lemma* surj_on_of_bij_on
- \+ *lemma* bij_on.mk
- \+ *lemma* image_eq_of_bij_on
- \+ *lemma* bijective_iff_bij_on_univ
- \+ *theorem* maps_to_of_eq_on
- \+ *theorem* maps_to_comp
- \+ *theorem* maps_to_univ_univ
- \+ *theorem* image_subset_of_maps_to_of_subset
- \+ *theorem* image_subset_of_maps_to
- \+ *theorem* inj_on_empty
- \+ *theorem* inj_on_of_eq_on
- \+ *theorem* inj_on_comp
- \+ *theorem* inj_on_of_inj_on_of_subset
- \+ *theorem* surj_on_of_eq_on
- \+ *theorem* surj_on_comp
- \+ *theorem* bij_on_of_eq_on
- \+ *theorem* bij_on_comp
- \+ *theorem* left_inv_on_of_eq_on_left
- \+ *theorem* left_inv_on_of_eq_on_right
- \+ *theorem* inj_on_of_left_inv_on
- \+ *theorem* left_inv_on_comp
- \+ *theorem* right_inv_on_of_eq_on_left
- \+ *theorem* right_inv_on_of_eq_on_right
- \+ *theorem* surj_on_of_right_inv_on
- \+ *theorem* right_inv_on_comp
- \+ *theorem* right_inv_on_of_inj_on_of_left_inv_on
- \+ *theorem* eq_on_of_left_inv_of_right_inv
- \+ *theorem* left_inv_on_of_surj_on_right_inv_on
- \+ *theorem* bij_on_of_inv_on
- \+ *def* maps_to
- \+ *def* inj_on
- \+ *def* surj_on
- \+ *def* bij_on
- \+ *def* left_inv_on
- \+ *def* right_inv_on
- \+ *def* inv_on

modified data/set/lattice.lean
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right
- \- *lemma* Inter_pos
- \- *lemma* Inter_neg
- \- *lemma* Union_pos
- \- *lemma* Union_neg
- \- *lemma* Union_empty
- \- *lemma* Inter_univ

modified order/complete_lattice.lean
- \- *lemma* infi_pos
- \- *lemma* infi_neg
- \- *lemma* supr_pos
- \- *lemma* supr_neg

modified topology/measurable_space.lean

modified topology/outer_measure.lean
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_neg
- \+ *lemma* Union_pos
- \+ *lemma* Union_neg
- \+ *lemma* Union_empty
- \+ *lemma* Inter_univ

modified topology/topological_space.lean
- \- *lemma* is_open_sInter
- \- *lemma* is_open_generated_countable_inter

modified topology/topological_structures.lean
- \+ *lemma* infi_pos
- \+ *lemma* infi_neg
- \+ *lemma* supr_pos
- \+ *lemma* supr_neg



## [2017-09-22 12:31:19-04:00](https://github.com/leanprover-community/mathlib/commit/e0abdab)
feat(topology/topological_space): add countablility and separability axioms for topological spaces
#### Estimated changes
modified data/set/countable.lean
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \+ *lemma* countable_set_of_finite_subset
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton

modified data/set/lattice.lean
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_neg
- \+ *lemma* Union_pos
- \+ *lemma* Union_neg
- \+ *lemma* Union_empty
- \+ *lemma* Inter_univ

modified order/complete_lattice.lean
- \+ *lemma* infi_pos
- \+ *lemma* infi_neg
- \+ *lemma* supr_pos
- \+ *lemma* supr_neg

modified topology/measurable_space.lean

modified topology/outer_measure.lean
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right
- \- *lemma* Inter_pos
- \- *lemma* Inter_neg
- \- *lemma* Union_pos
- \- *lemma* Union_neg
- \- *lemma* Union_empty
- \- *lemma* Inter_univ

modified topology/topological_space.lean
- \+ *lemma* is_open_sInter
- \+ *lemma* is_open_generated_countable_inter

modified topology/topological_structures.lean
- \- *lemma* infi_pos
- \- *lemma* infi_neg
- \- *lemma* supr_pos
- \- *lemma* supr_neg



## [2017-09-21 15:10:53-05:00](https://github.com/leanprover-community/mathlib/commit/d5e009f)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-09-21 13:22:44-04:00](https://github.com/leanprover-community/mathlib/commit/5bb145e)
feat(topology/lebesgue_measure): add Lebesgue outer measure; show that the lower half open interval is measurable
#### Estimated changes
modified algebra/big_operators.lean
- \+ *lemma* prod_sdiff
- \+ *lemma* abs_sum_le_sum_abs

modified algebra/field.lean
- \+ *lemma* inv_pos

modified algebra/group_power.lean
- \+ *theorem* inv_one
- \+ *theorem* inv_inv'
- \+/\- *theorem* pow_succ'
- \+ *theorem* pow_ne_zero
- \+ *theorem* pow_inv
- \+/\- *theorem* pow_pos
- \+ *theorem* pow_nonneg
- \+/\- *theorem* pow_ge_one_of_ge_one
- \+ *theorem* pow_le_pow
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_ge_one_of_ge_one

modified algebra/ordered_monoid.lean

modified data/finset/basic.lean
- \+ *lemma* lt_max_iff
- \+ *lemma* sdiff_subset_sdiff
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ
- \+ *theorem* not_mem_upto
- \+ *theorem* upto_subset_upto_iff
- \+ *theorem* exists_nat_subset_upto
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ

modified data/set/lattice.lean
- \+ *theorem* subset_Union
- \+ *theorem* sdiff_subset_sdiff

modified order/boolean_algebra.lean
- \+ *theorem* sub_le_sub

modified topology/ennreal.lean
- \+ *lemma* Inf_lt_iff
- \+ *lemma* infi_lt_iff
- \+ *lemma* sum_of_real
- \+ *lemma* lt_add_right
- \+ *lemma* le_of_forall_epsilon_le
- \+ *lemma* supr_add
- \- *lemma* inv_pos
- \- *lemma* inv_inv'

modified topology/infinite_sum.lean
- \+ *lemma* add_div
- \+ *lemma* mem_at_top
- \+ *lemma* tendsto_sum_nat_of_is_sum
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg

created topology/lebesgue_measure.lean
- \+ *lemma* subset.antisymm_iff
- \+ *lemma* Ico_eq_empty_iff
- \+ *lemma* Ico_eq_empty
- \+ *lemma* Ico_subset_Ico_iff
- \+ *lemma* Ico_eq_Ico_iff
- \+ *lemma* Ico_sdiff_Iio_eq
- \+ *lemma* Ico_inter_Iio_eq
- \+ *lemma* nhds_principal_ne_top_of_is_lub
- \+ *lemma* is_lub_of_is_lub_of_tendsto
- \+ *lemma* lebesgue_length_Ico
- \+ *lemma* lebesgue_length_empty
- \+ *lemma* le_lebesgue_length
- \+ *lemma* lebesgue_length_Ico_le_lebesgue_length_Ico
- \+ *lemma* lebesgue_length_subadditive
- \+ *lemma* lebesgue_outer_Ico
- \+ *lemma* lebesgue_outer_is_measurable_Iio
- \+ *def* Ico
- \+ *def* Iio
- \+ *def* lebesgue_length
- \+ *def* lebesgue_outer

created topology/limits.lean
- \+ *lemma* one_lt_inv
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* neg_inv
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_sub
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* zero_le_of_nat
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* exists_lt_of_nat
- \+ *lemma* mul_add_one_le_pow
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+ *lemma* tendsto_inverse_at_top_nhds_0
- \+ *lemma* map_succ_at_top_eq
- \+ *lemma* tendsto_comp_succ_at_top_iff
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* sum_geometric'
- \+ *lemma* sum_geometric
- \+ *lemma* is_sum_geometric
- \+ *def* of_nat

modified topology/measure.lean

modified topology/metric_space.lean
- \+ *theorem* mem_uniformity_dist
- \- *theorem* is_closed_metric
- \- *theorem* uniform_continuous_metric_iff
- \- *theorem* continuous_metric_iff

created topology/outer_measure.lean
- \+ *lemma* inv_lt_one
- \+ *lemma* or_not
- \+ *lemma* infi_add
- \+ *lemma* add_infi
- \+ *lemma* infi_add_infi
- \+ *lemma* infi_sum
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_neg
- \+ *lemma* Union_pos
- \+ *lemma* Union_neg
- \+ *lemma* Union_empty
- \+ *lemma* Inter_univ
- \+ *lemma* subadditive
- \+ *lemma* space_is_measurable_eq
- \+ *lemma* inf_space_is_measurable
- \+ *def* inf
- \+ *def* space
- \+ *def* measure

modified topology/real.lean
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_lt_two



## [2017-09-21 10:33:23-05:00](https://github.com/leanprover-community/mathlib/commit/d9865ae)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes
modified algebra/big_operators.lean
- \- *lemma* prod_sdiff
- \- *lemma* abs_sum_le_sum_abs

modified algebra/field.lean
- \- *lemma* inv_pos

modified algebra/group_power.lean
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_ge_one_of_ge_one
- \- *theorem* inv_one
- \- *theorem* inv_inv'
- \+/\- *theorem* pow_succ'
- \- *theorem* pow_ne_zero
- \- *theorem* pow_inv
- \+/\- *theorem* pow_pos
- \- *theorem* pow_nonneg
- \+/\- *theorem* pow_ge_one_of_ge_one
- \- *theorem* pow_le_pow

modified algebra/ordered_monoid.lean

modified data/finset/basic.lean
- \- *lemma* lt_max_iff
- \- *lemma* sdiff_subset_sdiff
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ
- \- *theorem* not_mem_upto
- \- *theorem* upto_subset_upto_iff
- \- *theorem* exists_nat_subset_upto

modified data/set/lattice.lean
- \- *theorem* subset_Union
- \- *theorem* sdiff_subset_sdiff

modified order/boolean_algebra.lean
- \- *theorem* sub_le_sub

modified topology/ennreal.lean
- \+ *lemma* inv_pos
- \+ *lemma* inv_inv'
- \- *lemma* Inf_lt_iff
- \- *lemma* infi_lt_iff
- \- *lemma* sum_of_real
- \- *lemma* lt_add_right
- \- *lemma* le_of_forall_epsilon_le
- \- *lemma* supr_add

modified topology/infinite_sum.lean
- \- *lemma* add_div
- \- *lemma* mem_at_top
- \- *lemma* tendsto_sum_nat_of_is_sum
- \- *lemma* has_sum_of_absolute_convergence
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

deleted topology/limits.lean
- \- *lemma* one_lt_inv
- \- *lemma* div_eq_mul_inv
- \- *lemma* neg_inv
- \- *lemma* of_nat_add
- \- *lemma* of_nat_one
- \- *lemma* of_nat_mul
- \- *lemma* of_nat_bit0
- \- *lemma* of_nat_bit1
- \- *lemma* of_nat_sub
- \- *lemma* int_of_nat_eq_of_nat
- \- *lemma* rat_of_nat_eq_of_nat
- \- *lemma* rat_coe_eq_of_nat
- \- *lemma* real_of_rat_of_nat_eq_of_nat
- \- *lemma* zero_le_of_nat
- \- *lemma* of_nat_le_of_nat
- \- *lemma* of_nat_le_of_nat_iff
- \- *lemma* exists_lt_of_nat
- \- *lemma* mul_add_one_le_pow
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \- *lemma* tendsto_inverse_at_top_nhds_0
- \- *lemma* map_succ_at_top_eq
- \- *lemma* tendsto_comp_succ_at_top_iff
- \- *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \- *lemma* sum_geometric'
- \- *lemma* sum_geometric
- \- *lemma* is_sum_geometric
- \- *def* of_nat

modified topology/measure.lean

modified topology/metric_space.lean
- \+ *theorem* is_closed_metric
- \+ *theorem* uniform_continuous_metric_iff
- \+ *theorem* continuous_metric_iff
- \- *theorem* mem_uniformity_dist

deleted topology/outer_measure.lean
- \- *lemma* inv_lt_one
- \- *lemma* or_not
- \- *lemma* infi_add
- \- *lemma* add_infi
- \- *lemma* infi_add_infi
- \- *lemma* infi_sum
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right
- \- *lemma* Inter_pos
- \- *lemma* Inter_neg
- \- *lemma* Union_pos
- \- *lemma* Union_neg
- \- *lemma* Union_empty
- \- *lemma* Inter_univ
- \- *lemma* subadditive
- \- *lemma* space_is_measurable_eq
- \- *lemma* inf_space_is_measurable
- \- *def* inf
- \- *def* space
- \- *def* measure

modified topology/real.lean
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_lt_two



## [2017-09-20 20:02:04-04:00](https://github.com/leanprover-community/mathlib/commit/4235594)
feat(topology/outer_measure): add outer measures and tools for Caratheodorys extension method
#### Estimated changes
modified algebra/field.lean
- \+ *lemma* inv_pos

modified algebra/ordered_monoid.lean

modified data/finset/basic.lean
- \+ *lemma* lt_max_iff
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ
- \+/\- *theorem* subset.refl
- \+/\- *theorem* upto_zero
- \+/\- *theorem* upto_succ

modified data/set/lattice.lean
- \+ *theorem* subset_Union
- \+ *theorem* sdiff_subset_sdiff

modified order/boolean_algebra.lean
- \+ *theorem* sub_le_sub

modified topology/ennreal.lean
- \+ *lemma* Inf_lt_iff
- \+ *lemma* infi_lt_iff
- \+ *lemma* sum_of_real
- \+ *lemma* lt_add_right
- \+ *lemma* le_of_forall_epsilon_le
- \+ *lemma* supr_add
- \- *lemma* inv_pos
- \- *lemma* inv_inv'

modified topology/limits.lean
- \- *lemma* inv_pos

modified topology/measure.lean

created topology/outer_measure.lean
- \+ *lemma* inv_lt_one
- \+ *lemma* or_not
- \+ *lemma* infi_add
- \+ *lemma* add_infi
- \+ *lemma* infi_add_infi
- \+ *lemma* infi_sum
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_eq:
- \+ *lemma* union_sdiff_left
- \+ *lemma* union_sdiff_right
- \+ *lemma* Inter_pos
- \+ *lemma* Inter_neg
- \+ *lemma* Union_pos
- \+ *lemma* Union_neg
- \+ *lemma* Union_empty
- \+ *lemma* Inter_univ
- \+ *lemma* subadditive
- \+ *lemma* space_is_measurable_eq
- \+ *lemma* inf_space_is_measurable
- \+ *def* inf
- \+ *def* space
- \+ *def* measure

modified topology/real.lean
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_lt_two



## [2017-09-20 18:29:06-04:00](https://github.com/leanprover-community/mathlib/commit/4698828)
feat(topology): prove geometric series
#### Estimated changes
modified algebra/big_operators.lean
- \+ *lemma* prod_sdiff
- \+ *lemma* abs_sum_le_sum_abs

modified algebra/group_power.lean
- \+ *theorem* inv_one
- \+ *theorem* inv_inv'
- \+/\- *theorem* pow_succ'
- \+ *theorem* pow_ne_zero
- \+ *theorem* pow_inv
- \+/\- *theorem* pow_pos
- \+ *theorem* pow_nonneg
- \+/\- *theorem* pow_ge_one_of_ge_one
- \+ *theorem* pow_le_pow
- \+/\- *theorem* pow_succ'
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_ge_one_of_ge_one

modified data/finset/basic.lean
- \+ *lemma* sdiff_subset_sdiff
- \+ *theorem* not_mem_upto
- \+ *theorem* upto_subset_upto_iff
- \+ *theorem* exists_nat_subset_upto

modified topology/infinite_sum.lean
- \+ *lemma* add_div
- \+ *lemma* mem_at_top
- \+ *lemma* tendsto_sum_nat_of_is_sum
- \+ *lemma* has_sum_of_absolute_convergence
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg

created topology/limits.lean
- \+ *lemma* inv_pos
- \+ *lemma* one_lt_inv
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* neg_inv
- \+ *lemma* of_nat_add
- \+ *lemma* of_nat_one
- \+ *lemma* of_nat_mul
- \+ *lemma* of_nat_bit0
- \+ *lemma* of_nat_bit1
- \+ *lemma* of_nat_sub
- \+ *lemma* int_of_nat_eq_of_nat
- \+ *lemma* rat_of_nat_eq_of_nat
- \+ *lemma* rat_coe_eq_of_nat
- \+ *lemma* real_of_rat_of_nat_eq_of_nat
- \+ *lemma* zero_le_of_nat
- \+ *lemma* of_nat_le_of_nat
- \+ *lemma* of_nat_le_of_nat_iff
- \+ *lemma* exists_lt_of_nat
- \+ *lemma* mul_add_one_le_pow
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \+ *lemma* tendsto_inverse_at_top_nhds_0
- \+ *lemma* map_succ_at_top_eq
- \+ *lemma* tendsto_comp_succ_at_top_iff
- \+ *lemma* tendsto_pow_at_top_nhds_0_of_lt_1
- \+ *lemma* sum_geometric'
- \+ *lemma* sum_geometric
- \+ *lemma* is_sum_geometric
- \+ *def* of_nat

modified topology/metric_space.lean
- \+ *theorem* mem_uniformity_dist
- \- *theorem* is_closed_metric
- \- *theorem* uniform_continuous_metric_iff
- \- *theorem* continuous_metric_iff

modified topology/real.lean



## [2017-09-19 02:55:14-04:00](https://github.com/leanprover-community/mathlib/commit/6b93e93)
refactor(data/equiv,encodable): refactor/simplify proofs
#### Estimated changes
modified data/encodable.lean
- \+/\- *lemma* choose_spec
- \- *lemma* succ_ne_zero
- \+/\- *lemma* choose_spec
- \+ *def* choose_x
- \+/\- *def* choose
- \- *def* pn
- \+/\- *def* choose

modified data/equiv.lean
- \+/\- *lemma* coe_fn_symm_mk
- \+/\- *lemma* inverse_apply_apply
- \+/\- *lemma* apply_eq_iff_eq_inverse_apply
- \+/\- *lemma* coe_fn_symm_mk
- \+/\- *lemma* inverse_apply_apply
- \+/\- *lemma* apply_eq_iff_eq_inverse_apply
- \+ *def* equiv_empty
- \+/\- *def* false_equiv_empty
- \+ *def* option_equiv_sum_unit
- \+/\- *def* bool_prod_equiv_sum
- \+/\- *def* nat_equiv_nat_sum_unit
- \+/\- *def* nat_sum_unit_equiv_nat
- \+/\- *def* nat_prod_nat_equiv_nat
- \+/\- *def* nat_sum_bool_equiv_nat
- \+ *def* bool_prod_nat_equiv_nat
- \+/\- *def* nat_sum_nat_equiv_nat
- \+/\- *def* prod_equiv_of_equiv_nat
- \+/\- *def* subtype_equiv_of_subtype
- \+/\- *def* false_equiv_empty
- \+/\- *def* bool_prod_equiv_sum
- \+/\- *def* nat_equiv_nat_sum_unit
- \+/\- *def* nat_sum_unit_equiv_nat
- \+/\- *def* nat_prod_nat_equiv_nat
- \+/\- *def* nat_sum_bool_equiv_nat
- \+/\- *def* nat_sum_nat_equiv_nat
- \+/\- *def* prod_equiv_of_equiv_nat
- \+/\- *def* subtype_equiv_of_subtype

modified data/fin.lean

modified data/nat/basic.lean
- \+ *theorem* bodd_div2_eq

modified data/option.lean
- \+ *lemma* bind_some

modified data/set/enumerate.lean
- \- *lemma* bind_some

modified tactic/interactive.lean



## [2017-09-18 22:41:41-04:00](https://github.com/leanprover-community/mathlib/commit/1e4c869)
doc(tactic/interactive): rename simpf -> simpa, document rcases and simpa
#### Estimated changes
modified algebra/ordered_group.lean

modified algebra/ordered_ring.lean

modified data/nat/pairing.lean

modified data/nat/sqrt.lean

modified tactic/interactive.lean

modified topology/real.lean

modified topology/topological_space.lean

modified topology/uniform_space.lean



## [2017-09-18 22:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/cb4a92e)
chore(algebra/ordered_ring): fix names, update to lean
#### Estimated changes
modified algebra/ordered_ring.lean

modified data/nat/pairing.lean
- \+/\- *theorem* unpair_lt
- \+ *theorem* unpair_le
- \- *theorem* unpair_lt_aux
- \+/\- *theorem* unpair_lt



## [2017-09-18 21:57:48-04:00](https://github.com/leanprover-community/mathlib/commit/06e797b)
refactor(data/nat/pairing): improve proof readability
in response to review comments on 0acdf1c
#### Estimated changes
modified data/nat/pairing.lean
- \+/\- *theorem* unpair_lt
- \+/\- *theorem* unpair_lt



## [2017-09-17 15:38:03-04:00](https://github.com/leanprover-community/mathlib/commit/0acdf1c)
feat(data/nat): better sqrt + pairing, prime numbers, renames...
#### Estimated changes
modified algebra/functions.lean
- \+ *lemma* max_lt_iff
- \+ *lemma* lt_min_iff

modified algebra/group_power.lean

modified algebra/order.lean
- \+ *lemma* lt_iff_le_and_ne
- \+ *lemma* eq_or_lt_of_le

modified algebra/ring.lean

modified data/finset/basic.lean

modified data/int/basic.lean

modified data/nat/basic.lean
- \+ *lemma* lt_pred_of_succ_lt
- \+ *lemma* lt_succ_iff_lt_or_eq
- \- *lemma* le_zero_iff
- \- *lemma* le_add_one_iff
- \+ *theorem* pos_iff_ne_zero
- \+ *theorem* pos_iff_ne_zero'
- \+ *theorem* sub_le_left_iff_le_add
- \+ *theorem* sub_le_right_iff_le_add
- \+/\- *theorem* succ_le_succ_iff
- \+ *theorem* lt_succ_iff
- \+ *theorem* le_zero_iff
- \+ *theorem* le_add_one_iff
- \+ *theorem* mul_self_inj
- \+ *theorem* bit_le
- \+ *theorem* bit_ne_zero
- \+ *theorem* bit0_le_bit
- \+ *theorem* bit_le_bit1
- \+ *theorem* bit_lt_bit0
- \+ *theorem* bit_lt_bit
- \+ *theorem* pow_add
- \+ *theorem* pow_dvd_pow
- \+ *theorem* shiftl'_ne_zero_left
- \+ *theorem* shiftl'_tt_ne_zero
- \+ *theorem* size_zero
- \+ *theorem* size_bit
- \+ *theorem* size_bit0
- \+ *theorem* size_bit1
- \+ *theorem* size_shiftl'
- \+ *theorem* size_shiftl
- \+ *theorem* lt_size_self
- \+ *theorem* size_le
- \+ *theorem* lt_size
- \+ *theorem* size_pos
- \+ *theorem* size_eq_zero
- \+ *theorem* size_pow
- \+ *theorem* size_le_size
- \+ *theorem* fact_zero
- \+ *theorem* fact_one
- \+ *theorem* fact_succ
- \+ *theorem* fact_pos
- \+ *theorem* fact_ne_zero
- \+ *theorem* fact_dvd_fact
- \+ *theorem* dvd_fact
- \+ *theorem* fact_le
- \+/\- *theorem* succ_le_succ_iff
- \- *theorem* lt_succ_iff_le
- \+ *def* fact

deleted data/nat/bquant.lean
- \- *def* ball

renamed data/nat/sub.lean to data/nat/dist.lean

modified data/nat/gcd.lean
- \+ *theorem* gcd_eq_left
- \+ *theorem* gcd_eq_right
- \+ *theorem* coprime.gcd_eq_one
- \+ *theorem* coprime.symm
- \+ *theorem* coprime.dvd_of_dvd_mul_right
- \+ *theorem* coprime.dvd_of_dvd_mul_left
- \+ *theorem* coprime.gcd_mul_left_cancel
- \+ *theorem* coprime.gcd_mul_right_cancel
- \+ *theorem* coprime.gcd_mul_left_cancel_right
- \+ *theorem* coprime.gcd_mul_right_cancel_right
- \+ *theorem* coprime.mul
- \+ *theorem* coprime.mul_right
- \+ *theorem* coprime.coprime_dvd_left
- \+ *theorem* coprime.coprime_dvd_right
- \+ *theorem* coprime.coprime_mul_left
- \+ *theorem* coprime.coprime_mul_right
- \+ *theorem* coprime.coprime_mul_left_right
- \+ *theorem* coprime.coprime_mul_right_right
- \+ *theorem* coprime.pow_left
- \+ *theorem* coprime.pow_right
- \+ *theorem* coprime.pow
- \+ *theorem* coprime.eq_one_of_dvd
- \- *theorem* gcd_eq_one_of_coprime
- \- *theorem* coprime_swap
- \- *theorem* dvd_of_coprime_of_dvd_mul_right
- \- *theorem* dvd_of_coprime_of_dvd_mul_left
- \- *theorem* gcd_mul_left_cancel_of_coprime
- \- *theorem* gcd_mul_right_cancel_of_coprime
- \- *theorem* gcd_mul_left_cancel_of_coprime_right
- \- *theorem* gcd_mul_right_cancel_of_coprime_right
- \- *theorem* coprime_mul
- \- *theorem* coprime_mul_right
- \- *theorem* coprime_of_coprime_dvd_left
- \- *theorem* coprime_of_coprime_dvd_right
- \- *theorem* coprime_of_coprime_mul_left
- \- *theorem* coprime_of_coprime_mul_right
- \- *theorem* coprime_of_coprime_mul_left_right
- \- *theorem* coprime_of_coprime_mul_right_right
- \- *theorem* coprime_pow_left
- \- *theorem* coprime_pow_right
- \- *theorem* coprime_pow

modified data/nat/pairing.lean
- \+/\- *theorem* unpair_lt_aux
- \+/\- *theorem* unpair_lt
- \+/\- *theorem* unpair_lt_aux
- \+/\- *theorem* unpair_lt

created data/nat/prime.lean
- \+ *theorem* prime.ge_two
- \+ *theorem* prime.gt_one
- \+ *theorem* prime_def_lt
- \+ *theorem* prime_def_lt'
- \+ *theorem* prime_def_le_sqrt
- \+ *theorem* prime.pos
- \+ *theorem* not_prime_zero
- \+ *theorem* not_prime_one
- \+ *theorem* prime_two
- \+ *theorem* prime_three
- \+ *theorem* prime.pred_pos
- \+ *theorem* succ_pred_prime
- \+ *theorem* dvd_prime
- \+ *theorem* dvd_prime_ge_two
- \+ *theorem* prime.not_dvd_one
- \+ *theorem* exists_dvd_of_not_prime
- \+ *theorem* exists_dvd_of_not_prime2
- \+ *theorem* exists_prime_and_dvd
- \+ *theorem* exists_infinite_primes
- \+ *theorem* prime.coprime_iff_not_dvd
- \+ *theorem* prime.dvd_iff_not_coprime
- \+ *theorem* prime.dvd_mul
- \+ *theorem* prime.not_dvd_mul
- \+ *theorem* dvd_of_prime_of_dvd_pow
- \+ *theorem* prime.coprime_pow_of_not_dvd
- \+ *theorem* coprime_primes
- \+ *theorem* coprime_pow_primes
- \+ *theorem* coprime_or_dvd_of_prime
- \+ *theorem* dvd_prime_pow
- \+ *def* prime
- \+ *def* decidable_prime_1

modified data/nat/sqrt.lean
- \+ *theorem* sqrt_aux_dec
- \+ *theorem* sqrt_aux_0
- \+ *theorem* sqrt_aux_1
- \+ *theorem* sqrt_aux_2
- \+ *theorem* sqrt_le
- \+ *theorem* lt_succ_sqrt
- \+ *theorem* sqrt_le_add
- \+ *theorem* le_sqrt
- \+/\- *theorem* sqrt_lt
- \+ *theorem* sqrt_le_self
- \+ *theorem* sqrt_le_sqrt
- \+ *theorem* sqrt_eq_zero
- \+/\- *theorem* le_three_of_sqrt_eq_one
- \+ *theorem* sqrt_lt_self
- \+ *theorem* sqrt_pos
- \+ *theorem* sqrt_add_eq
- \+/\- *theorem* sqrt_eq
- \- *theorem* sqrt_upper
- \- *theorem* sqrt_lower
- \- *theorem* sqrt_mono
- \+/\- *theorem* sqrt_eq
- \- *theorem* eq_zero_of_sqrt_eq_zero
- \+/\- *theorem* le_three_of_sqrt_eq_one
- \+/\- *theorem* sqrt_lt
- \- *theorem* sqrt_pos_of_pos
- \- *theorem* sqrt_mul_eq
- \- *theorem* mul_square_cancel
- \+ *def* sqrt_aux
- \+ *def* sqrt

modified data/rat.lean

modified logic/basic.lean
- \+ *theorem* not.imp

modified tactic/rcases.lean

modified topology/measurable_space.lean
- \- *lemma* lt_succ_iff

modified topology/topological_structures.lean
- \- *lemma* max_lt_iff
- \- *lemma* lt_min_iff



## [2017-09-16 03:26:54-04:00](https://github.com/leanprover-community/mathlib/commit/f542d42)
chore(algebra/ordered_ring): update to lean
#### Estimated changes
modified algebra/ordered_ring.lean
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero



## [2017-09-16 02:55:01-04:00](https://github.com/leanprover-community/mathlib/commit/fe1ad4b)
feat(data/rat): derive properties of rat floor and ceil
#### Estimated changes
modified data/int/basic.lean
- \+ *theorem* lt_succ_self
- \+ *theorem* pred_self_lt
- \+ *theorem* to_nat_eq_max
- \+ *theorem* le_to_nat
- \+ *theorem* to_nat_le

modified data/rat.lean
- \- *lemma* coe_int_eq_mk
- \- *lemma* coe_nat_rat_eq_mk
- \- *lemma* coe_int_add
- \- *lemma* coe_int_sub
- \- *lemma* coe_int_one
- \- *lemma* le_of_of_int_le_of_int
- \- *lemma* exists_upper_nat_bound
- \- *lemma* nat_ceil_spec
- \- *lemma* nat_ceil_min
- \- *lemma* nat_ceil_mono
- \- *lemma* nat_ceil_zero
- \- *lemma* nat_ceil_add_one_eq
- \- *lemma* nat_ceil_lt_add_one
- \+ *theorem* sub_def
- \+ *theorem* mk_le
- \+ *theorem* coe_int_eq_mk
- \+ *theorem* coe_nat_rat_eq_mk
- \+ *theorem* coe_int_inj
- \+ *theorem* coe_int_add
- \+ *theorem* coe_int_neg
- \+ *theorem* coe_int_sub
- \+ *theorem* coe_int_mul
- \+ *theorem* coe_int_one
- \+ *theorem* coe_int_le
- \+ *theorem* coe_int_lt
- \+ *theorem* le_floor
- \+ *theorem* floor_lt
- \+ *theorem* floor_le
- \+ *theorem* lt_succ_floor
- \+ *theorem* floor_coe
- \+ *theorem* floor_mono
- \+ *theorem* floor_add_int
- \+ *theorem* floor_sub_int
- \+ *theorem* ceil_le
- \+ *theorem* le_ceil
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_sub_int
- \+ *theorem* nat_ceil_le
- \+ *theorem* lt_nat_ceil
- \+ *theorem* le_nat_ceil
- \+ *theorem* nat_ceil_mono
- \+ *theorem* nat_ceil_coe
- \+ *theorem* nat_ceil_zero
- \+ *theorem* nat_ceil_add_nat
- \+ *theorem* nat_ceil_lt_add_one
- \+/\- *def* nat_ceil
- \+/\- *def* nat_ceil

modified topology/real.lean



## [2017-09-16 02:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/a1c3e2d)
feat(algebra): new algebra theorems (more iff)
#### Estimated changes
modified algebra/big_operators.lean

created algebra/functions.lean
- \+ *lemma* le_min_iff
- \+ *lemma* max_le_iff
- \+ *lemma* abs_lt
- \+ *lemma* abs_eq_zero
- \+ *theorem* abs_le

modified algebra/group.lean
- \- *lemma* le_sub_iff_add_le
- \- *lemma* sub_le_iff_le_add
- \- *lemma* abs_le_iff
- \- *lemma* abs_lt_iff
- \- *lemma* abs_eq_zero_iff
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_right_inj
- \+ *theorem* le_sub_iff_add_le
- \+ *theorem* sub_le_iff_le_add
- \- *theorem* add_comm_four
- \- *theorem* add_comm_middle
- \- *theorem* bit0_add_bit0
- \- *theorem* bit0_add_bit0_helper
- \- *theorem* bit1_add_bit0
- \- *theorem* bit1_add_bit0_helper
- \- *theorem* bit0_add_bit1
- \- *theorem* bit0_add_bit1_helper
- \- *theorem* bit1_add_bit1
- \- *theorem* bit1_add_bit1_helper
- \- *theorem* bin_add_zero
- \- *theorem* bin_zero_add
- \- *theorem* one_add_bit0
- \- *theorem* bit0_add_one
- \- *theorem* bit1_add_one
- \- *theorem* bit1_add_one_helper
- \- *theorem* one_add_bit1
- \- *theorem* one_add_bit1_helper
- \- *theorem* add1_bit0
- \- *theorem* add1_bit1
- \- *theorem* add1_bit1_helper
- \- *theorem* add1_one
- \- *theorem* add1_zero
- \- *theorem* one_add_one
- \- *theorem* subst_into_sum
- \- *theorem* neg_zero_helper
- \- *def* add1

created algebra/order.lean
- \+ *lemma* not_le_of_lt
- \+ *lemma* not_lt_of_le
- \+ *lemma* not_lt_of_lt
- \+ *lemma* le_iff_eq_or_lt
- \+ *lemma* not_lt
- \+ *lemma* le_of_not_lt
- \+ *lemma* not_le
- \+ *lemma* not_lt_iff_eq_or_lt
- \+ *lemma* le_imp_le_iff_lt_imp_lt
- \+ *lemma* le_iff_le_iff_lt_iff_lt
- \+ *lemma* eq_of_forall_le_iff
- \+ *lemma* eq_of_forall_ge_iff

created algebra/ordered_group.lean
- \+ *lemma* add_le_add_iff_left
- \+ *lemma* add_le_add_iff_right
- \+ *lemma* add_lt_add_iff_left
- \+ *lemma* add_lt_add_iff_right
- \+ *lemma* le_add_iff_nonneg_right
- \+ *lemma* le_add_iff_nonneg_left
- \+ *lemma* lt_add_iff_pos_right
- \+ *lemma* lt_add_iff_pos_left
- \+ *lemma* add_eq_zero_iff_eq_zero_of_nonneg
- \+ *lemma* neg_le_neg_iff
- \+ *lemma* neg_le
- \+ *lemma* le_neg
- \+ *lemma* neg_nonpos
- \+ *lemma* neg_nonneg
- \+ *lemma* neg_lt_neg_iff
- \+ *lemma* neg_lt_zero
- \+ *lemma* neg_pos
- \+ *lemma* neg_lt
- \+ *lemma* lt_neg
- \+ *lemma* sub_le_sub_iff_left
- \+ *lemma* sub_le_sub_iff_right
- \+ *lemma* sub_lt_sub_iff_left
- \+ *lemma* sub_lt_sub_iff_right
- \+ *lemma* sub_nonneg
- \+ *lemma* sub_nonpos
- \+ *lemma* sub_pos
- \+ *lemma* sub_lt_zero
- \+ *lemma* le_neg_add_iff_add_le
- \+ *lemma* le_sub_left_iff_add_le
- \+ *lemma* le_sub_right_iff_add_le
- \+ *lemma* neg_add_le_iff_le_add
- \+ *lemma* sub_left_le_iff_le_add
- \+ *lemma* sub_right_le_iff_le_add
- \+ *lemma* neg_add_le_iff_le_add_right
- \+ *lemma* neg_le_sub_iff_le_add
- \+ *lemma* neg_le_sub_iff_le_add_left
- \+ *lemma* sub_le
- \+ *lemma* lt_neg_add_iff_add_lt
- \+ *lemma* lt_sub_left_iff_add_lt
- \+ *lemma* lt_sub_right_iff_add_lt
- \+ *lemma* neg_add_lt_iff_lt_add
- \+ *lemma* sub_left_lt_iff_lt_add
- \+ *lemma* sub_right_lt_iff_lt_add
- \+ *lemma* neg_add_lt_iff_lt_add_right
- \+ *lemma* neg_lt_sub_iff_lt_add
- \+ *lemma* neg_lt_sub_iff_lt_add_left
- \+ *lemma* sub_lt
- \+ *lemma* sub_le_self_iff
- \+ *lemma* sub_lt_self_iff
- \+ *theorem* nonneg_def
- \+ *theorem* pos_def
- \+ *theorem* not_zero_pos
- \+ *theorem* zero_lt_iff_nonneg_nonneg
- \+ *theorem* nonneg_total_iff
- \+ *def* to_decidable_linear_ordered_comm_group

created algebra/ordered_ring.lean
- \+ *lemma* mul_le_mul_left
- \+ *lemma* mul_le_mul_right
- \+ *lemma* mul_lt_mul_left
- \+ *lemma* mul_lt_mul_right
- \+ *lemma* le_mul_iff_one_le_left
- \+ *lemma* lt_mul_iff_one_lt_left
- \+ *lemma* le_mul_iff_one_le_right
- \+ *lemma* lt_mul_iff_one_lt_right
- \+ *lemma* lt_mul_of_gt_one_right'
- \+ *lemma* le_mul_of_ge_one_right'
- \+ *lemma* le_mul_of_ge_one_left'
- \+ *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* mul_le_mul_left_of_neg
- \+ *lemma* mul_le_mul_right_of_neg
- \+ *lemma* mul_lt_mul_left_of_neg
- \+ *lemma* mul_lt_mul_right_of_neg
- \+ *def* nonneg_ring.to_linear_nonneg_ring

modified algebra/ring.lean
- \- *theorem* mul_zero
- \- *theorem* zero_mul
- \- *theorem* mul_one
- \- *theorem* mul_bit0
- \- *theorem* mul_bit0_helper
- \- *theorem* mul_bit1
- \- *theorem* mul_bit1_helper
- \- *theorem* subst_into_prod
- \- *theorem* mk_cong
- \- *theorem* neg_add_neg_eq_of_add_add_eq_zero
- \- *theorem* neg_add_neg_helper
- \- *theorem* neg_add_pos_eq_of_eq_add
- \- *theorem* neg_add_pos_helper1
- \- *theorem* neg_add_pos_helper2
- \- *theorem* pos_add_neg_helper
- \- *theorem* sub_eq_add_neg_helper
- \- *theorem* pos_add_pos_helper
- \- *theorem* subst_into_subtr
- \- *theorem* neg_neg_helper
- \- *theorem* neg_mul_neg_helper
- \- *theorem* neg_mul_pos_helper
- \- *theorem* pos_mul_neg_helper

modified topology/ennreal.lean

modified topology/metric_space.lean

modified topology/real.lean



## [2017-09-16 02:51:50-04:00](https://github.com/leanprover-community/mathlib/commit/a967d8d)
feat(tactic/interactive): allow exprs in simpf, interactive try_for
#### Estimated changes
modified tactic/interactive.lean



## [2017-09-13 17:34:12-04:00](https://github.com/leanprover-community/mathlib/commit/f705963)
feat(topology/measure): introduce measures
#### Estimated changes
modified data/set/lattice.lean
- \+/\- *lemma* Union_subset_Union2
- \+/\- *lemma* Union_subset_Union2
- \+/\- *theorem* inter_distrib_Union_left
- \+ *theorem* inter_distrib_Union_right
- \+/\- *theorem* inter_distrib_Union_left

modified topology/ennreal.lean
- \+ *lemma* lt_supr_iff
- \- *lemma* add_le_add
- \- *lemma* lt_of_add_lt_add_left

modified topology/infinite_sum.lean
- \+ *lemma* is_sum_iff_is_sum_of_iso
- \+ *lemma* has_sum_sigma
- \+ *lemma* tsum_eq_sum
- \+ *lemma* tsum_sigma
- \+ *lemma* tsum_eq_tsum_of_is_sum_iff_is_sum
- \+/\- *lemma* tsum_eq_tsum_of_ne_zero
- \+ *lemma* tsum_eq_tsum_of_ne_zero_bij
- \+ *lemma* tsum_eq_tsum_of_iso
- \+ *lemma* is_sum_le
- \+ *lemma* tsum_le_tsum
- \+/\- *lemma* tsum_eq_tsum_of_ne_zero

modified topology/measurable_space.lean
- \+/\- *lemma* lt_succ_iff
- \+/\- *lemma* disjoint_disjointed
- \+ *lemma* disjointed_induct
- \+ *lemma* is_measurable_disjointed
- \+/\- *lemma* disjoint_disjointed
- \+/\- *lemma* lt_succ_iff
- \+ *def* pairwise

created topology/measure.lean
- \+ *lemma* supr_bool_eq
- \+ *lemma* measure_eq_measure_of
- \+ *lemma* measure_space_eq_of
- \+ *lemma* measure_space_eq
- \+ *lemma* measure_empty
- \+ *lemma* measure_Union_nat
- \+ *lemma* measure_bUnion
- \+ *lemma* measure_sUnion
- \+ *lemma* measure_union
- \+ *lemma* measure_mono
- \+ *lemma* measure_Union_le_nat
- \+ *def* measure_space.measure
- \+ *def* count

modified topology/topological_structures.lean
- \+ *lemma* infi_pos
- \+ *lemma* infi_neg
- \+ *lemma* supr_pos
- \+ *lemma* supr_neg
- \+/\- *lemma* binfi_inf
- \+ *lemma* inf_principal_eq_bot
- \+/\- *lemma* le_of_tendsto
- \+ *lemma* mem_nhds_orderable_dest
- \+ *lemma* mem_nhds_unbounded
- \+/\- *lemma* binfi_inf
- \+/\- *lemma* le_of_tendsto
- \- *lemma* mem_nhds_lattice_unbounded



## [2017-09-13 14:20:42-04:00](https://github.com/leanprover-community/mathlib/commit/0b16336)
feat(topology/infinite_sum): strengten bijection proof
#### Estimated changes
modified topology/infinite_sum.lean
- \+/\- *lemma* tsum_zero
- \+ *lemma* tsum_eq_tsum_of_ne_zero
- \+/\- *lemma* tsum_zero



## [2017-09-13 14:19:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b077c)
chore(data/equiv): use has_coe_to_fun
#### Estimated changes
modified data/equiv.lean
- \+ *lemma* coe_fn_mk
- \+/\- *lemma* eq_of_to_fun_eq
- \+ *lemma* coe_fn_symm_mk
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* inverse_apply_apply
- \+/\- *lemma* apply_eq_iff_eq
- \+/\- *lemma* apply_eq_iff_eq_inverse_apply
- \+/\- *lemma* swap_apply_def
- \+/\- *lemma* swap_apply_left
- \+/\- *lemma* swap_apply_right
- \+/\- *lemma* swap_apply_of_ne_of_ne
- \+/\- *lemma* eq_of_to_fun_eq
- \+/\- *lemma* id_apply
- \+/\- *lemma* comp_apply
- \+/\- *lemma* inverse_apply_apply
- \+/\- *lemma* apply_eq_iff_eq
- \+/\- *lemma* apply_eq_iff_eq_inverse_apply
- \+/\- *lemma* swap_apply_def
- \+/\- *lemma* swap_apply_left
- \+/\- *lemma* swap_apply_right
- \+/\- *lemma* swap_apply_of_ne_of_ne
- \+/\- *def* subtype_equiv_of_subtype
- \- *def* fn
- \- *def* inv
- \+/\- *def* subtype_equiv_of_subtype



## [2017-09-11 21:55:00-04:00](https://github.com/leanprover-community/mathlib/commit/bf58bf4)
feat(topology/measurable_space): induction rule for sigma-algebras with intersection-stable generators; uses Dynkin systems
#### Estimated changes
modified topology/measurable_space.lean
- \+ *lemma* disjoint_disjointed
- \+ *lemma* disjointed_Union
- \+ *lemma* lt_succ_iff
- \+ *lemma* is_measurable_univ
- \+ *lemma* is_measurable_generate_from
- \+ *lemma* generate_from_le
- \+ *lemma* measurable_generate_from
- \+ *lemma* dynkin_system_eq
- \+ *lemma* of_measurable_space_le_of_measurable_space_iff
- \+ *lemma* has_univ
- \+ *lemma* has_union
- \+ *lemma* has_sdiff
- \+ *lemma* of_measurable_space_to_measurable_space
- \+ *lemma* generate_le
- \+ *lemma* generate_inter
- \+ *lemma* generate_from_eq
- \+ *lemma* induction_on_inter
- \+ *def* disjointed
- \+ *def* generate_from
- \+ *def* of_measurable_space
- \+ *def* generate
- \+ *def* to_measurable_space
- \+ *def* restrict_on



## [2017-09-11 14:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/74c3e6e)
feat(topology/measurable_space): measurable sets invariant under (countable) set operations
#### Estimated changes
modified topology/measurable_space.lean
- \+ *lemma* is_measurable_Union_nat
- \+ *lemma* is_measurable_sUnion
- \+ *lemma* is_measurable_bUnion
- \+/\- *lemma* is_measurable_Union
- \+ *lemma* is_measurable_sInter
- \+ *lemma* is_measurable_bInter
- \+ *lemma* is_measurable_Inter
- \+ *lemma* is_measurable_union
- \+ *lemma* is_measurable_inter
- \+ *lemma* is_measurable_sdiff
- \+ *lemma* is_measurable_sub
- \+/\- *lemma* is_measurable_Union



## [2017-09-11 13:56:06-04:00](https://github.com/leanprover-community/mathlib/commit/b890425)
feat(topology/ennreal): ennreal forms a topological monoid
#### Estimated changes
modified order/filter.lean
- \+ *lemma* tendsto_inf_left

modified topology/ennreal.lean
- \+ *lemma* nhds_of_real_eq_map_of_real_nhds_nonneg

modified topology/real.lean
- \- *lemma* lt_mem_nhds
- \- *lemma* le_mem_nhds
- \- *lemma* gt_mem_nhds
- \- *lemma* ge_mem_nhds

modified topology/topological_structures.lean
- \+ *lemma* lt_mem_nhds
- \+ *lemma* le_mem_nhds
- \+ *lemma* gt_mem_nhds
- \+ *lemma* ge_mem_nhds



## [2017-09-11 11:58:16-04:00](https://github.com/leanprover-community/mathlib/commit/8ed673d)
feat(data/set/countable): finite sets are countable
#### Estimated changes
modified data/encodable.lean
- \- *def* encodable_finType*

modified data/set/countable.lean
- \+ *lemma* countable_Union
- \+ *lemma* countable_union
- \+ *lemma* countable_insert
- \+ *lemma* countable_finite



## [2017-09-11 11:32:25-04:00](https://github.com/leanprover-community/mathlib/commit/28b46a2)
fix(data/set/countable): finish proof countable_sUnion
#### Estimated changes
modified data/set/countable.lean
- \+/\- *lemma* countable_sUnion
- \- *lemma* bind_some
- \- *lemma* enumerate_eq_none_of_sel
- \- *lemma* enumerate_eq_none
- \- *lemma* enumerate_mem
- \- *lemma* enumerate_inj
- \+/\- *lemma* countable_sUnion
- \- *def* enumerate

created data/set/enumerate.lean
- \+ *lemma* bind_some
- \+ *lemma* enumerate_eq_none_of_sel
- \+ *lemma* enumerate_eq_none
- \+ *lemma* enumerate_mem
- \+ *lemma* enumerate_inj
- \+ *def* enumerate



## [2017-09-10 23:28:41-04:00](https://github.com/leanprover-community/mathlib/commit/8ee2629)
feat(data/set): add countable sets
#### Estimated changes
modified data/encodable.lean
- \- *def* countable_of_encodable

created data/set/countable.lean
- \+ *lemma* bind_some
- \+ *lemma* enumerate_eq_none_of_sel
- \+ *lemma* enumerate_eq_none
- \+ *lemma* enumerate_mem
- \+ *lemma* enumerate_inj
- \+ *lemma* countable_iff_exists_surjective
- \+ *lemma* countable.to_encodable
- \+ *lemma* countable_encodable'
- \+ *lemma* countable_encodable
- \+ *lemma* countable_empty
- \+ *lemma* countable_singleton
- \+ *lemma* countable_subset
- \+ *lemma* countable_image
- \+ *lemma* countable_sUnion
- \+ *def* enumerate
- \+ *def* encodable_of_inj
- \+ *def* countable

modified data/set/finite.lean
- \+ *def* infinite

modified logic/function_inverse.lean
- \+ *theorem* inv_fun_on_eq'

modified order/filter.lean



## [2017-09-10 20:33:16-04:00](https://github.com/leanprover-community/mathlib/commit/7e06124)
feat(logic): add small theory on inverse functions
#### Estimated changes
created logic/function_inverse.lean
- \+ *lemma* right_inverse_inv_fun
- \+ *lemma* left_inverse_inv_fun
- \+ *lemma* has_left_inverse
- \+ *lemma* surj_inv_eq
- \+ *lemma* right_inverse_surj_inv
- \+ *lemma* has_right_inverse
- \+ *lemma* injective_surj_inv
- \+ *theorem* inv_fun_on_pos
- \+ *theorem* inv_fun_on_mem
- \+ *theorem* inv_fun_on_eq
- \+ *theorem* inv_fun_on_neg
- \+ *theorem* inv_fun_eq
- \+ *theorem* inv_fun_eq_of_injective_of_right_inverse
- \+ *def* inv_fun_on
- \+ *def* inv_fun
- \+ *def* surj_inv



## [2017-09-09 12:48:22-04:00](https://github.com/leanprover-community/mathlib/commit/a5f32d2)
feat(data/encodable): port countable choice from Lean2
#### Estimated changes
modified data/encodable.lean
- \+ *lemma* choose_spec
- \+/\- *theorem* axiom_of_choice
- \+/\- *theorem* skolem
- \+/\- *theorem* rep_spec
- \- *theorem* choose_spec
- \+/\- *theorem* axiom_of_choice
- \+/\- *theorem* skolem
- \+/\- *theorem* rep_spec
- \+ *def* pn
- \+/\- *def* choose
- \+/\- *def* rep
- \+ *def* encodable_quotient
- \+/\- *def* choose
- \+/\- *def* rep
- \- *def* encodable_quot



## [2017-09-08 20:06:26-04:00](https://github.com/leanprover-community/mathlib/commit/3399baa)
feat(data/encodable): ported data/encodable.lean from Lean2
#### Estimated changes
created data/encodable.lean
- \+ *lemma* succ_ne_zero
- \+ *theorem* choose_spec
- \+ *theorem* axiom_of_choice
- \+ *theorem* skolem
- \+ *theorem* rep_spec
- \+ *def* countable_of_encodable
- \+ *def* encodable_finType*
- \+ *def* encodable_of_left_injection
- \+ *def* encodable_of_equiv
- \+ *def* choose
- \+ *def* rep
- \+ *def* encodable_quot

modified data/list/sort.lean
- \+ *lemma* eq_of_sorted_of_perm
- \+ *theorem* sorted_insertion_sort
- \- *theorem* sorted_insert_sort



## [2017-09-08 18:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/741065b)
chore(data/equiv): using nat pairing
#### Estimated changes
modified data/equiv.lean



## [2017-09-08 18:05:53-04:00](https://github.com/leanprover-community/mathlib/commit/22c8fae)
feat(data/nat/pairing): ported data/nat/pairing.lean from Lean2
#### Estimated changes
created data/nat/pairing.lean
- \+ *theorem* mkpair_unpair
- \+ *theorem* unpair_mkpair
- \+ *theorem* unpair_lt_aux
- \+ *theorem* unpair_lt
- \+ *def* mkpair
- \+ *def* unpair



## [2017-09-08 17:19:17-04:00](https://github.com/leanprover-community/mathlib/commit/7c67c29)
feat(data/nat/sqrt): ported data/nat/sqrt.lean from Lean2
#### Estimated changes
created data/nat/sqrt.lean
- \+ *theorem* sqrt_upper
- \+ *theorem* sqrt_lower
- \+ *theorem* sqrt_mono
- \+ *theorem* sqrt_eq
- \+ *theorem* eq_zero_of_sqrt_eq_zero
- \+ *theorem* le_three_of_sqrt_eq_one
- \+ *theorem* sqrt_lt
- \+ *theorem* sqrt_pos_of_pos
- \+ *theorem* sqrt_mul_eq
- \+ *theorem* mul_square_cancel



## [2017-09-08 14:50:51-04:00](https://github.com/leanprover-community/mathlib/commit/445a5a4)
fix(topology/real): remove (unnecessary) admit
#### Estimated changes
modified topology/real.lean



## [2017-09-08 14:49:07-04:00](https://github.com/leanprover-community/mathlib/commit/8ef8f81)
feat(data/equiv): port data/equiv.lean from Lean2
#### Estimated changes
created data/equiv.lean
- \+ *lemma* map_comp
- \+ *lemma* map_id
- \+ *lemma* left_inverse.f_g_eq_id
- \+ *lemma* right_inverse.g_f_eq_id
- \+ *lemma* eq_of_to_fun_eq
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *lemma* inverse_apply_apply
- \+ *lemma* eq_iff_eq_of_injective
- \+ *lemma* apply_eq_iff_eq
- \+ *lemma* apply_eq_iff_eq_inverse_apply
- \+ *lemma* swap_core_self
- \+ *lemma* swap_core_swap_core
- \+ *lemma* swap_core_comm
- \+ *lemma* swap_self
- \+ *lemma* swap_comm
- \+ *lemma* swap_apply_def
- \+ *lemma* swap_apply_left
- \+ *lemma* swap_apply_right
- \+ *lemma* swap_apply_of_ne_of_ne
- \+ *lemma* swap_swap
- \+ *lemma* swap_comp_apply
- \+ *def* map
- \+ *def* perm
- \+ *def* fn
- \+ *def* inv
- \+ *def* id
- \+ *def* false_equiv_empty
- \+ *def* arrow_congr
- \+ *def* arrow_unit_equiv_unit
- \+ *def* unit_arrow_equiv
- \+ *def* empty_arrow_equiv_unit
- \+ *def* false_arrow_equiv_unit
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* prod_assoc
- \+ *def* prod_unit_right
- \+ *def* prod_unit_left
- \+ *def* prod_empty_right
- \+ *def* prod_empty_left
- \+ *def* sum_congr
- \+ *def* bool_equiv_unit_sum_unit
- \+ *def* sum_comm
- \+ *def* sum_assoc
- \+ *def* sum_empty_right
- \+ *def* sum_empty_left
- \+ *def* arrow_prod_equiv_prod_arrow
- \+ *def* arrow_arrow_equiv_prod_arrow
- \+ *def* sum_arrow_equiv_prod_arrow
- \+ *def* sum_prod_distrib
- \+ *def* prod_sum_distrib
- \+ *def* bool_prod_equiv_sum
- \+ *def* nat_equiv_nat_sum_unit
- \+ *def* nat_sum_unit_equiv_nat
- \+ *def* nat_prod_nat_equiv_nat
- \+ *def* nat_sum_bool_equiv_nat
- \+ *def* nat_sum_nat_equiv_nat
- \+ *def* prod_equiv_of_equiv_nat
- \+ *def* decidable_eq_of_equiv
- \+ *def* inhabited_of_equiv
- \+ *def* subtype_equiv_of_subtype
- \+ *def* swap_core
- \+ *def* swap



## [2017-09-07 20:38:33-04:00](https://github.com/leanprover-community/mathlib/commit/ddeefb8)
feat(topology/topological_structures,ennreal): show continuity of of_ennreal and of_real
#### Estimated changes
modified data/set/basic.lean
- \+ *lemma* image_inter_on
- \+/\- *lemma* image_inter
- \+/\- *lemma* mem_range
- \+/\- *lemma* image_inter
- \+/\- *lemma* mem_range

modified order/filter.lean
- \+ *lemma* le_of_map_le_map_inj'
- \+ *lemma* eq_of_map_eq_map_inj'
- \+/\- *lemma* map_binfi_eq
- \+ *lemma* map_inf'
- \+/\- *lemma* map_inf
- \+ *lemma* tendsto_principal
- \+/\- *lemma* map_binfi_eq
- \+/\- *lemma* map_inf

modified order/lattice.lean
- \+ *theorem* not_top_lt
- \+ *theorem* not_lt_bot

modified topology/ennreal.lean
- \+ *lemma* tendsto_of_real
- \+ *lemma* tendsto_of_ennreal

modified topology/topological_space.lean
- \+ *lemma* is_open_neg

modified topology/topological_structures.lean
- \+ *lemma* max_lt_iff
- \+ *lemma* lt_min_iff
- \+ *lemma* binfi_inf
- \+ *lemma* is_closed_le'
- \+ *lemma* is_closed_ge'
- \+/\- *lemma* is_open_lt'
- \+/\- *lemma* is_open_gt'
- \+ *lemma* nhds_eq_orderable
- \+ *lemma* tendsto_orderable
- \+ *lemma* nhds_orderable_unbounded
- \+ *lemma* tendsto_orderable_unbounded
- \+ *lemma* nhds_top_orderable
- \+ *lemma* nhds_bot_orderable
- \+ *lemma* mem_nhds_lattice_unbounded
- \+/\- *lemma* is_open_lt'
- \+/\- *lemma* is_open_gt'



## [2017-09-06 19:31:17-04:00](https://github.com/leanprover-community/mathlib/commit/32f3f45)
feat(topology): restructure order topologies; (start) proof that ennreal is a topological monoid
#### Estimated changes
modified algebra/group.lean
- \+ *lemma* abs_lt_iff

modified topology/ennreal.lean
- \+ *lemma* inv_pos
- \+ *lemma* inv_inv'
- \+ *lemma* of_real_of_nonpos
- \+ *lemma* of_real_of_not_nonneg
- \+ *lemma* one_le_of_real_iff
- \+ *lemma* zero_lt_of_real_iff
- \+ *lemma* not_lt_zero
- \+ *lemma* of_real_lt_of_real_iff_cases
- \+ *lemma* continuous_of_real
- \+ *lemma* nhds_of_real_eq_map_of_real_nhds
- \+ *lemma* inv_zero
- \+ *lemma* inv_infty
- \+ *lemma* inv_of_real
- \+ *lemma* inv_inv

modified topology/real.lean
- \+ *lemma* sub_lt_iff
- \+ *lemma* lt_sub_iff
- \+ *lemma* orderable_topology_of_nhds_abs
- \+/\- *lemma* exists_pos_of_rat
- \+ *lemma* nhds_eq_real
- \+/\- *lemma* closure_of_rat_image_le_eq
- \+/\- *lemma* closure_of_rat_image_le_le_eq
- \+/\- *lemma* closure_of_rat_image_le_eq
- \+/\- *lemma* closure_of_rat_image_le_le_eq
- \- *lemma* is_closed_imp
- \+/\- *lemma* exists_pos_of_rat

modified topology/topological_space.lean
- \+ *lemma* is_open_const
- \+ *lemma* is_open_and
- \+ *lemma* is_closed_imp
- \+/\- *lemma* closure_diff
- \+ *lemma* mem_of_closed_of_tendsto
- \+/\- *lemma* closure_diff

modified topology/topological_structures.lean
- \+/\- *lemma* is_closed_le
- \+ *lemma* le_of_tendsto
- \+/\- *lemma* is_open_lt
- \+ *lemma* is_open_iff_generate_intervals
- \+ *lemma* is_open_lt'
- \+ *lemma* is_open_gt'
- \- *lemma* is_open_lt_fst_snd
- \+/\- *lemma* is_open_lt
- \+/\- *lemma* is_closed_le

modified topology/uniform_space.lean
- \+ *lemma* nhds_eq_vmap_uniformity



## [2017-09-06 16:19:02-04:00](https://github.com/leanprover-community/mathlib/commit/17e48db)
fix(data/list/comb): implement fix from rlewis1988
#### Estimated changes
modified data/list/comb.lean



## [2017-09-05 22:38:07-04:00](https://github.com/leanprover-community/mathlib/commit/f80ae1f)
feat(topology/infinite_sum): add tsum (with ∑ notation) and has_sum; add lemmas for different algebraic structures
#### Estimated changes
modified topology/continuity.lean
- \+/\- *lemma* continuous_const
- \+/\- *lemma* continuous_const

modified topology/infinite_sum.lean
- \+ *lemma* is_sum_tsum
- \+ *lemma* has_sum_spec
- \+ *lemma* has_sum_zero
- \+ *lemma* has_sum_add
- \+ *lemma* has_sum_sum
- \+ *lemma* is_sum_sum_of_ne_finset_zero
- \+ *lemma* has_sum_sum_of_ne_finset_zero
- \+/\- *lemma* is_sum_hom
- \+ *lemma* has_sum_iff_has_sum_ne_zero
- \+ *lemma* is_sum_unique
- \+ *lemma* tsum_eq_is_sum
- \+ *lemma* tsum_zero
- \+ *lemma* tsum_add
- \+ *lemma* tsum_sum
- \+ *lemma* is_sum_neg
- \+ *lemma* has_sum_neg
- \+ *lemma* is_sum_sub
- \+ *lemma* has_sum_sub
- \+ *lemma* tsum_neg
- \+ *lemma* tsum_sub
- \+ *lemma* is_sum_mul_left
- \+ *lemma* is_sum_mul_right
- \+ *lemma* has_sum_mul_left
- \+ *lemma* has_sum_mul_right
- \+ *lemma* tsum_mul_left
- \+ *lemma* tsum_mul_right
- \+ *lemma* has_sum_of_has_sum_of_sub
- \- *lemma* is_sum_sum_of_ne_zero
- \+/\- *lemma* is_sum_hom
- \- *lemma* exists_is_sum_of_is_sum
- \+ *def* has_sum
- \+ *def* tsum

modified topology/real.lean

modified topology/topological_structures.lean
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* tendsto_mul
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* tendsto_mul



## [2017-09-05 19:48:25-04:00](https://github.com/leanprover-community/mathlib/commit/1e4f6cc)
chore(data/seq,data/hash_map): adapt to changes in injection tactic (https://github.com/leanprover/lean/commit/8a10d4c72c948cd1b7af02f316e553e202b1368f)
#### Estimated changes
modified data/hash_map.lean

modified data/seq/computation.lean

modified data/seq/parallel.lean

modified data/seq/seq.lean

modified data/seq/wseq.lean



## [2017-09-05 19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/c6747ee)
chore(topology/uniform_space): use Type* and Sort*
#### Estimated changes
modified topology/uniform_space.lean
- \+/\- *lemma* supr_uniformity
- \+/\- *lemma* to_topological_space_supr
- \+/\- *lemma* uniform_embedding_subtype_emb
- \+/\- *lemma* uniform_extend_subtype
- \+/\- *lemma* uniform_embedding_prod
- \+/\- *lemma* supr_uniformity
- \+/\- *lemma* to_topological_space_supr
- \+/\- *lemma* uniform_embedding_subtype_emb
- \+/\- *lemma* uniform_extend_subtype
- \+/\- *lemma* uniform_embedding_prod
- \+/\- *def* id_rel
- \+/\- *def* id_rel



## [2017-09-05 19:32:31-04:00](https://github.com/leanprover-community/mathlib/commit/7c38416)
feat(data/sigma,data/finset,algebra): add support for the sigma type to finset and big operators
#### Estimated changes
modified algebra/big_operators.lean
- \+ *lemma* prod_sigma

modified data/finset/fold.lean
- \+ *lemma* heq_iff_eq
- \+ *lemma* mem_sigma_iff
- \+ *lemma* sigma_mono

created data/sigma/basic.lean
- \+ *lemma* mk_eq_mk_iff
- \+ *def* map

created data/sigma/default.lean

modified topology/infinite_sum.lean
- \+/\- *lemma* is_sum_sigma
- \+/\- *lemma* is_sum_sigma



## [2017-09-05 19:24:56-04:00](https://github.com/leanprover-community/mathlib/commit/7d8e3f3)
feat(algebra): add ordered (non-cancellative) additive monoid; use for sum-big operator
#### Estimated changes
modified algebra/big_operators.lean
- \+ *lemma* sum_le_sum'
- \+ *lemma* zero_le_sum'
- \+ *lemma* sum_le_zero'
- \+ *lemma* sum_le_sum_of_subset_of_nonneg
- \+ *lemma* sum_eq_zero_iff_of_nonneg
- \+ *lemma* sum_le_sum_of_subset
- \+ *lemma* sum_le_sum_of_ne_zero

created algebra/ordered_monoid.lean
- \+ *lemma* add_le_add_left'
- \+ *lemma* add_le_add_right'
- \+ *lemma* lt_of_add_lt_add_left'
- \+ *lemma* add_le_add'
- \+ *lemma* le_add_of_nonneg_right'
- \+ *lemma* le_add_of_nonneg_left'
- \+ *lemma* lt_of_add_lt_add_right'
- \+ *lemma* le_add_of_nonneg_of_le'
- \+ *lemma* le_add_of_le_of_nonneg'
- \+ *lemma* add_nonneg'
- \+ *lemma* add_pos_of_pos_of_nonneg'
- \+ *lemma* add_pos'
- \+ *lemma* add_pos_of_nonneg_of_pos'
- \+ *lemma* add_nonpos'
- \+ *lemma* add_le_of_nonpos_of_le'
- \+ *lemma* add_le_of_le_of_nonpos'
- \+ *lemma* add_neg_of_neg_of_nonpos'
- \+ *lemma* add_neg_of_nonpos_of_neg'
- \+ *lemma* add_neg'
- \+ *lemma* lt_add_of_nonneg_of_lt'
- \+ *lemma* lt_add_of_lt_of_nonneg'
- \+ *lemma* lt_add_of_pos_of_lt'
- \+ *lemma* lt_add_of_lt_of_pos'
- \+ *lemma* add_lt_of_nonpos_of_lt'
- \+ *lemma* add_lt_of_lt_of_nonpos'
- \+ *lemma* add_lt_of_neg_of_lt'
- \+ *lemma* add_lt_of_lt_of_neg'
- \+ *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
- \+ *lemma* le_iff_exists_add
- \+ *lemma* zero_le
- \+ *lemma* add_eq_zero_iff



## [2017-09-05 15:09:41-04:00](https://github.com/leanprover-community/mathlib/commit/fde992f)
chore(*): use `induction generalizing`
#### Estimated changes
modified data/int/basic.lean
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_lt
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_ge
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_lt
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_ge

modified data/list/basic.lean

modified data/list/comb.lean

modified data/num/lemmas.lean

modified data/seq/computation.lean

modified data/seq/parallel.lean

modified data/seq/seq.lean



## [2017-09-05 15:05:29-04:00](https://github.com/leanprover-community/mathlib/commit/a8a1a91)
chore(topology/uniform_space): simplify proof (suggested by @gebner)
#### Estimated changes
modified topology/uniform_space.lean



## [2017-09-05 14:15:01-04:00](https://github.com/leanprover-community/mathlib/commit/ba95269)
feat(topology): introduce infinite sums on topological monoids
#### Estimated changes
modified algebra/big_operators.lean
- \+/\- *lemma* prod_const_one
- \+ *lemma* prod_bind
- \+ *lemma* prod_product
- \+ *lemma* prod_comm
- \+ *lemma* prod_subset
- \+/\- *lemma* prod_const_one

modified data/finset/basic.lean
- \+ *lemma* sdiff_union_of_subset
- \+ *lemma* sdiff_inter_self
- \+ *lemma* image_empty
- \+ *lemma* mem_image_iff
- \+ *lemma* image_subset_image
- \+ *lemma* image_filter
- \+ *lemma* image_union
- \+ *lemma* image_inter
- \+ *lemma* image_singleton
- \+ *lemma* image_insert
- \+ *lemma* image_eq_empty_iff
- \+/\- *theorem* mem_to_finset
- \+ *theorem* mem_to_finset_iff
- \+ *theorem* union_subset
- \+ *theorem* subset_union_left
- \+ *theorem* subset_union_right
- \+ *theorem* union_idempotent
- \+ *theorem* inter_subset_left
- \+ *theorem* inter_subset_right
- \+ *theorem* subset_inter
- \+ *theorem* mem_filter_iff
- \+ *theorem* filter_subset
- \+ *theorem* filter_union
- \+ *theorem* filter_filter
- \+ *theorem* filter_false
- \+ *theorem* filter_union_filter_neg_eq
- \+ *theorem* filter_inter_filter_neg_eq
- \+ *theorem* mem_sdiff_iff
- \+/\- *theorem* mem_to_finset
- \+/\- *def* nodup_list
- \+ *def* {u}
- \+/\- *def* nodup_list
- \- *def* finset

modified data/finset/fold.lean
- \+ *lemma* fold_insert_idem
- \+ *lemma* bind_empty
- \+ *lemma* bind_insert
- \+ *lemma* mem_bind_iff
- \+ *lemma* image_bind
- \+ *lemma* bind_image
- \+ *lemma* mem_product_iff

modified data/list/basic.lean
- \+ *theorem* mem_filter_iff

modified logic/basic.lean

modified order/complete_lattice.lean
- \+ *lemma* infi_top
- \+ *lemma* supr_bot

created topology/infinite_sum.lean
- \+ *lemma* mem_infi_sets_finset
- \+ *lemma* mem_closure_of_tendsto
- \+ *lemma* cauchy_iff
- \+ *lemma* at_top_ne_bot
- \+ *lemma* mem_at_top_iff
- \+ *lemma* map_at_top_eq
- \+ *lemma* tendsto_finset_image_at_top_at_top
- \+ *lemma* is_sum_zero
- \+ *lemma* is_sum_add
- \+ *lemma* is_sum_sum
- \+ *lemma* is_sum_sum_of_ne_zero
- \+ *lemma* is_sum_of_iso
- \+ *lemma* is_sum_hom
- \+ *lemma* is_sum_of_is_sum
- \+ *lemma* is_sum_iff_is_sum
- \+ *lemma* is_sum_of_is_sum_ne_zero
- \+ *lemma* is_sum_iff_is_sum_of_ne_zero
- \+ *lemma* is_sum_sigma
- \+ *lemma* exists_is_sum_of_is_sum
- \+ *theorem* forall_and_distrib'
- \+ *def* is_sum

modified topology/topological_structures.lean
- \+ *lemma* tendsto_add'
- \+ *lemma* tendsto_sum
- \+ *lemma* uniform_continuous_sub'
- \+ *lemma* uniform_continuous_sub
- \+ *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous_neg'
- \+ *lemma* uniform_continuous_add
- \+ *lemma* uniform_continuous_add'

modified topology/uniform_space.lean
- \+ *lemma* uniform_continuous_id



## [2017-09-05 12:47:49-05:00](https://github.com/leanprover-community/mathlib/commit/6c321fe)
Merge branch 'master' of https://github.com/leanprover/mathlib
#### Estimated changes



## [2017-09-05 10:33:20-04:00](https://github.com/leanprover-community/mathlib/commit/c7a3c75)
fix(data/seq): option_bind, option_map -> option.bind, option.map (changed in Lean)
#### Estimated changes
modified data/seq/parallel.lean

modified data/seq/seq.lean
- \+/\- *theorem* map_nth
- \+/\- *theorem* map_nth

modified data/seq/wseq.lean
- \+/\- *def* map
- \+/\- *def* map



## [2017-09-04 12:33:01-04:00](https://github.com/leanprover-community/mathlib/commit/80e1474)
fix(logic/basic): fix simp performance issue
Having `forall_true_iff'` as a simp lemma caused way too much backtracking, so only the 2 and 3 implication versions are added as simp lemmas, and the user can add `forall_true_iff'` to their simp set if they need to reduce more.
#### Estimated changes
modified logic/basic.lean
- \+ *theorem* imp.swap
- \+/\- *theorem* imp_not_comm
- \+/\- *theorem* forall_true_iff'
- \+ *theorem* forall_2_true_iff
- \+ *theorem* forall_3_true_iff
- \+/\- *theorem* imp_not_comm
- \+/\- *theorem* forall_true_iff'

modified order/filter.lean



## [2017-09-03 23:13:00-04:00](https://github.com/leanprover-community/mathlib/commit/086ac36)
feat(tactic/interactive): simpf tactic, more logic refactor
#### Estimated changes
modified logic/basic.lean
- \+ *theorem* not_and_not_right
- \+ *theorem* not_and
- \+ *theorem* not_and'
- \- *theorem* imp_of_not_or
- \- *theorem* not_and_iff_imp
- \- *theorem* not_and_iff_imp'

modified order/zorn.lean

modified tactic/interactive.lean

modified topology/ennreal.lean

modified topology/topological_space.lean

modified topology/uniform_space.lean



## [2017-09-03 20:55:23-04:00](https://github.com/leanprover-community/mathlib/commit/8faac5f)
refactor(logic/basic): refactor logic theorems
#### Estimated changes
modified algebra/big_operators.lean
- \- *lemma* exists_false

modified data/finset/basic.lean
- \- *lemma* or_self_or
- \+ *theorem* subset_iff
- \+/\- *theorem* mem_singleton
- \+ *theorem* mem_singleton_self
- \+ *theorem* singleton_inj
- \- *theorem* perm_insert_cons_of_not_mem
- \- *theorem* subset_of_forall
- \- *theorem* mem_singleton_iff
- \+/\- *theorem* mem_singleton
- \- *theorem* mem_singleton_of_eq
- \- *theorem* eq_of_mem_singleton
- \- *theorem* eq_of_singleton_eq

modified data/finset/fold.lean
- \+/\- *lemma* map_congr
- \+/\- *lemma* fold_congr
- \+/\- *lemma* map_congr
- \+/\- *lemma* fold_congr

modified data/list/basic.lean

modified data/list/comb.lean

modified data/list/perm.lean

modified data/list/set.lean

modified data/seq/seq.lean

modified data/set/basic.lean
- \+ *lemma* not_not_mem
- \- *lemma* not_not_mem_iff
- \+ *theorem* ball_empty_iff
- \+ *theorem* mem_union
- \+ *theorem* ball_insert_iff
- \+ *theorem* ball_image_of_ball
- \+ *theorem* ball_image_iff
- \- *theorem* bounded_forall_empty_iff
- \- *theorem* mem_union_iff
- \- *theorem* bounded_forall_insert_iff
- \- *theorem* bounded_forall_image_of_bounded_forall
- \- *theorem* bounded_forall_image_iff

modified data/set/lattice.lean

modified logic/basic.lean
- \- *lemma* {u
- \+/\- *theorem* eq_iff_le_and_le
- \+/\- *theorem* prod.mk.inj_iff
- \+/\- *theorem* prod.forall
- \+/\- *theorem* prod.exists
- \+ *theorem* imp_self
- \+ *theorem* imp_intro
- \+ *theorem* imp_false
- \+ *theorem* imp_and_distrib
- \+ *theorem* and_imp
- \+/\- *theorem* iff_def
- \+ *theorem* iff_def'
- \+ *theorem* imp_true_iff
- \+ *theorem* imp_iff_right
- \+ *theorem* not.elim
- \+ *theorem* not_not_of_not_imp
- \+ *theorem* not_of_not_imp
- \+ *theorem* not_not
- \+ *theorem* of_not_not
- \+ *theorem* of_not_imp
- \+ *theorem* not.imp_symm
- \+ *theorem* not_imp_comm
- \+ *theorem* imp_not_comm
- \+ *theorem* and.imp_left
- \+ *theorem* and.imp_right
- \+ *theorem* or_of_or_of_imp_of_imp
- \+ *theorem* or_of_or_of_imp_left
- \+ *theorem* or_of_or_of_imp_right
- \+ *theorem* or_imp_distrib
- \+ *theorem* or_iff_not_imp_left
- \+ *theorem* or_iff_not_imp_right
- \+ *theorem* not_imp_not
- \+ *theorem* and_or_distrib_left
- \+ *theorem* or_and_distrib_right
- \+ *theorem* or_and_distrib_left
- \+ *theorem* and_or_distrib_right
- \+ *theorem* iff_of_true
- \+ *theorem* iff_of_false
- \+ *theorem* iff_true_left
- \+ *theorem* iff_true_right
- \+ *theorem* iff_false_left
- \+ *theorem* iff_false_right
- \+ *theorem* not_or_of_imp
- \+ *theorem* imp_of_not_or
- \+ *theorem* imp_iff_not_or
- \+ *theorem* not_imp_of_and_not
- \+ *theorem* not_imp
- \+ *theorem* not_iff_not
- \+ *theorem* not_iff_comm
- \+ *theorem* iff_not_comm
- \+/\- *theorem* not_and_of_not_or_not
- \+ *theorem* not_and_distrib
- \+ *theorem* not_and_distrib'
- \+ *theorem* not_and_iff_imp
- \+ *theorem* not_and_iff_imp'
- \+ *theorem* not_or_distrib
- \+/\- *theorem* or_iff_not_and_not
- \+/\- *theorem* and_iff_not_or_not
- \+ *theorem* forall_swap
- \+ *theorem* exists_swap
- \+/\- *theorem* forall_of_forall
- \+/\- *theorem* exists_of_exists
- \+ *theorem* exists_imp_distrib
- \+ *theorem* not_exists
- \+/\- *theorem* not_forall_of_exists_not
- \+ *theorem* not_forall
- \+ *theorem* not_forall_not
- \+ *theorem* not_exists_not
- \+/\- *theorem* forall_true_iff
- \+ *theorem* forall_true_iff'
- \+ *theorem* forall_const
- \+ *theorem* exists_const
- \+/\- *theorem* forall_and_distrib
- \+/\- *theorem* exists_or_distrib
- \+/\- *theorem* forall_eq
- \+ *theorem* exists_eq
- \+ *theorem* exists_eq_right
- \+ *theorem* forall_eq'
- \+ *theorem* exists_eq'
- \+ *theorem* exists_eq_right'
- \+ *theorem* forall_or_of_or_forall
- \+ *theorem* exists_prop
- \+ *theorem* exists_false
- \+ *theorem* not_forall
- \+ *theorem* bex_def
- \+ *theorem* bex.elim
- \+ *theorem* bex.intro
- \+ *theorem* ball_congr
- \+ *theorem* bex_congr
- \+ *theorem* ball.imp_right
- \+ *theorem* bex.imp_right
- \+ *theorem* ball.imp_left
- \+ *theorem* bex.imp_left
- \+ *theorem* ball_of_forall
- \+ *theorem* forall_of_ball
- \+ *theorem* bex_of_exists
- \+ *theorem* exists_of_bex
- \+ *theorem* bex_imp_distrib
- \+ *theorem* not_bex
- \+ *theorem* not_ball_of_bex_not
- \+ *theorem* not_ball
- \+ *theorem* ball_true_iff
- \+ *theorem* ball_and_distrib
- \+ *theorem* bex_or_distrib
- \+ *theorem* not_ball
- \+/\- *theorem* eq_iff_le_and_le
- \+/\- *theorem* prod.mk.inj_iff
- \+/\- *theorem* prod.forall
- \+/\- *theorem* prod.exists
- \- *theorem* implies_self
- \- *theorem* implies_intro
- \- *theorem* implies_false_iff
- \- *theorem* implies_and_iff
- \- *theorem* and_implies_iff
- \+/\- *theorem* iff_def
- \- *theorem* {u}
- \- *theorem* not_not_of_not_implies
- \- *theorem* not_of_not_implies
- \- *theorem* not_not_iff
- \- *theorem* not_not_elim
- \- *theorem* of_not_implies
- \- *theorem* and_implies_left
- \- *theorem* and_implies_right
- \- *theorem* and_of_and_of_implies_of_implies
- \- *theorem* and_of_and_of_imp_left
- \- *theorem* and_of_and_of_imp_right
- \- *theorem* and_imp_iff
- \- *theorem* or_of_or_of_implies_of_implies
- \- *theorem* or_of_or_of_implies_left
- \- *theorem* or_of_or_of_implies_right
- \- *theorem* or_resolve_right
- \- *theorem* or_resolve_left
- \- *theorem* or_implies_distrib
- \- *theorem* or_iff_or
- \- *theorem* or_of_not_implies
- \- *theorem* or_of_not_implies'
- \- *theorem* not_imp_iff_not_imp
- \- *theorem* and_distrib
- \- *theorem* and_distrib_right
- \- *theorem* or_distrib
- \- *theorem* or_distrib_right
- \- *theorem* implies_iff
- \- *theorem* not_or_of_implies
- \- *theorem* implies_of_not_or
- \- *theorem* implies_iff_not_or
- \- *theorem* not_implies_of_and_not
- \- *theorem* and_not_of_not_implies
- \- *theorem* not_implies_iff
- \+/\- *theorem* not_and_of_not_or_not
- \- *theorem* not_or_not_of_not_and
- \- *theorem* not_or_not_of_not_and'
- \- *theorem* not_and_iff
- \- *theorem* not_and_iff_imp_not
- \- *theorem* not_or_of_not_and_not
- \- *theorem* not_and_not_of_not_or
- \- *theorem* not_or_iff
- \+/\- *theorem* or_iff_not_and_not
- \+/\- *theorem* and_iff_not_or_not
- \- *theorem* or_imp_iff_and_imp
- \+/\- *theorem* forall_of_forall
- \+/\- *theorem* exists_of_exists
- \- *theorem* forall_implies_of_exists_implies
- \- *theorem* exists_implies_of_forall_implies
- \- *theorem* exists_implies_distrib
- \- *theorem* forall_not_of_not_exists
- \- *theorem* not_exists_iff
- \- *theorem* exists_not_of_not_forall
- \+/\- *theorem* not_forall_of_exists_not
- \- *theorem* not_forall_iff
- \+/\- *theorem* forall_true_iff
- \- *theorem* forall_p_iff_p
- \- *theorem* exists_p_iff_p
- \+/\- *theorem* forall_and_distrib
- \+/\- *theorem* exists_or_distrib
- \+/\- *theorem* forall_eq
- \- *theorem* exists_prop_iff
- \- *theorem* exists_not_of_not_forall
- \- *theorem* not_forall_iff
- \- *theorem* bexists_def
- \- *theorem* bexists.elim
- \- *theorem* bexists.intro
- \- *theorem* bforall_congr
- \- *theorem* bexists_congr
- \- *theorem* bforall_of_bforall
- \- *theorem* bexists_of_bexists
- \- *theorem* bforall_of_forall
- \- *theorem* forall_of_bforall
- \- *theorem* bexists_of_exists
- \- *theorem* exists_of_bexists
- \- *theorem* bforall_implies_of_bexists_implies
- \- *theorem* bexists_implies_of_bforall_implies
- \- *theorem* bexists_implies_distrib
- \- *theorem* bforall_not_of_not_bexists
- \- *theorem* not_bexists_of_bforall_not
- \- *theorem* not_bexists_iff_bforall_not
- \- *theorem* bexists_not_of_not_bforall
- \- *theorem* not_bforall_of_bexists_not
- \- *theorem* not_bforall_iff_bexists_not
- \- *theorem* bforall_true_iff
- \- *theorem* bforall_and_distrib
- \- *theorem* bexists_or_distrib
- \- *theorem* bexists_not_of_not_bforall
- \- *theorem* not_bforall_iff_bexists_not
- \+ *def* decidable_of_iff
- \+ *def* decidable_of_iff'

modified order/bounds.lean

modified order/filter.lean

modified order/zorn.lean

modified tactic/finish.lean
- \+/\- *theorem* not_not_eq
- \+/\- *theorem* not_and_eq
- \+/\- *theorem* not_or_eq
- \+/\- *theorem* not_forall_eq
- \+/\- *theorem* not_exists_eq
- \+/\- *theorem* not_implies_eq
- \+/\- *theorem* classical.implies_iff_not_or
- \+/\- *theorem* not_not_eq
- \+/\- *theorem* not_and_eq
- \+/\- *theorem* not_or_eq
- \+/\- *theorem* not_forall_eq
- \+/\- *theorem* not_exists_eq
- \+/\- *theorem* not_implies_eq
- \+/\- *theorem* classical.implies_iff_not_or

modified topology/continuity.lean

modified topology/ennreal.lean

modified topology/measurable_space.lean

modified topology/metric_space.lean
- \- *lemma* exists_subtype
- \- *lemma* dist_self
- \- *lemma* eq_of_dist_eq_zero
- \- *lemma* dist_comm
- \- *lemma* dist_eq_zero_iff
- \- *lemma* zero_eq_dist_iff
- \- *lemma* dist_triangle
- \- *lemma* uniformity_dist
- \- *lemma* uniformity_dist'
- \- *lemma* dist_nonneg
- \- *lemma* dist_pos_of_ne
- \- *lemma* ne_of_dist_pos
- \- *lemma* eq_of_forall_dist_le
- \- *lemma* uniform_continuous_dist'
- \- *lemma* uniform_continuous_dist
- \- *lemma* continuous_dist'
- \- *lemma* continuous_dist
- \- *lemma* tendsto_dist
- \- *lemma* open_ball_subset_open_ball_of_le
- \+ *theorem* exists_subtype
- \+ *theorem* dist_self
- \+ *theorem* eq_of_dist_eq_zero
- \+ *theorem* dist_comm
- \+ *theorem* dist_eq_zero_iff
- \+ *theorem* zero_eq_dist_iff
- \+ *theorem* dist_triangle
- \+ *theorem* uniformity_dist
- \+ *theorem* uniformity_dist'
- \+ *theorem* dist_nonneg
- \+ *theorem* dist_pos_of_ne
- \+ *theorem* ne_of_dist_pos
- \+ *theorem* eq_of_forall_dist_le
- \+ *theorem* uniform_continuous_dist'
- \+ *theorem* uniform_continuous_dist
- \+ *theorem* continuous_dist'
- \+ *theorem* continuous_dist
- \+ *theorem* tendsto_dist
- \+ *theorem* open_ball_subset_open_ball_of_le

modified topology/real.lean

modified topology/topological_space.lean

modified topology/topological_structures.lean

modified topology/uniform_space.lean



## [2017-09-02 19:56:17-04:00](https://github.com/leanprover-community/mathlib/commit/74cfa93)
fix(data/list/perm): fix broken match
This reverts commit 3d817686fdb02eba0f51ab303a4d5b50ac2a9f5e.
#### Estimated changes
modified data/list/perm.lean

