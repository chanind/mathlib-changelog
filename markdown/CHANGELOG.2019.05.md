## [2019-05-31 20:59:47](https://github.com/leanprover-community/mathlib/commit/4f6307e)
feat(topology/algebra/open_subgroup): basics on open subgroups  ([#1067](https://github.com/leanprover-community/mathlib/pull/1067))
* Dump the file into mathlib
* feat(algebra/pi_instances): product of submonoids/groups/rings
From the perfectoid project.
* Small changes
* feat(topology/algebra/open_subgroup): basics on open subgroups
* Some proof compression
* Update src/topology/algebra/open_subgroup.lean
#### Estimated changes
Added src/topology/algebra/open_subgroup.lean
- \+ *lemma* ideal.is_open_of_open_subideal
- \+ *lemma* open_add_subgroup.coe_inf
- \+ *lemma* open_add_subgroup.is_open_of_open_add_subgroup
- \+ *lemma* open_add_subgroup.le_iff
- \+ *lemma* open_add_subgroup.mem_nhds_zero
- \+ *def* open_add_subgroup.prod
- \+ *lemma* open_subgroup.coe_inf
- \+ *lemma* open_subgroup.coe_injective
- \+ *lemma* open_subgroup.ext'
- \+ *lemma* open_subgroup.ext
- \+ *lemma* open_subgroup.is_closed
- \+ *lemma* open_subgroup.is_open_of_nonempty_open_subset
- \+ *lemma* open_subgroup.is_open_of_open_subgroup
- \+ *lemma* open_subgroup.le_iff
- \+ *lemma* open_subgroup.mem_nhds_one
- \+ *def* open_subgroup.prod
- \+ *def* open_subgroup
- \+ *lemma* submodule.is_open_of_open_submodule



## [2019-05-31 19:49:44](https://github.com/leanprover-community/mathlib/commit/6237939)
fix(data/nat/enat): change [] to {} in some lemmas ([#1054](https://github.com/leanprover-community/mathlib/pull/1054))
* fix(data/nat/enat): change [] to {} in some lemmas
* Update enat.lean
* remove space
#### Estimated changes
Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.to_with_top_coe'
- \+/\- *lemma* enat.to_with_top_top'
- \+/\- *lemma* enat.to_with_top_zero'



## [2019-05-31 17:26:55](https://github.com/leanprover-community/mathlib/commit/8ebea31)
feat(category_theory/monoidal): the monoidal category of types ([#1100](https://github.com/leanprover-community/mathlib/pull/1100))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* almost
* oops
* getting there
* one more
* sleep
* good to go
* monoidal category of types
* fix names
* renaming
* linebreak
* temporary notations
* notations for associator, unitors?
* more notation
* names
* more names
* oops
* renaming, and namespaces
* comment
* fix comment
* remove unnecessary open, formatting
* removing dsimps
* replace with simp lemmas
* fix
* Update types.lean
* fix namespace
#### Estimated changes
Added src/category_theory/monoidal/types.lean
- \+ *def* category_theory.monoidal.types_associator
- \+ *def* category_theory.monoidal.types_associator_inv
- \+ *def* category_theory.monoidal.types_braiding
- \+ *def* category_theory.monoidal.types_braiding_inv
- \+ *def* category_theory.monoidal.types_left_unitor
- \+ *def* category_theory.monoidal.types_left_unitor_inv
- \+ *def* category_theory.monoidal.types_right_unitor
- \+ *def* category_theory.monoidal.types_right_unitor_inv



## [2019-05-31 06:43:58](https://github.com/leanprover-community/mathlib/commit/2db435d)
chore(category_theory): move all instances (e.g. Top, CommRing, Meas) into the root namespace ([#1074](https://github.com/leanprover-community/mathlib/pull/1074))
* splitting adjunction.lean
* chore(CommRing/adjunctions): refactor proofs
* remove unnecessary assumptions
* add helpful doc-string
* cleanup
* chore(category_theory): move all instances (e.g. Top, CommRing, Meas) to the root namespace
* minor
* breaking things, haven't finished yet
* deterministic timeout
* unfold_coes to the rescue
* one more int.cast
* yet another int.cast
* fix merge
* minor
* merge
* fix imports
* fix merge
* fix imports/namespaces
* more namespace fixes
* fixes
* delete stray file
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean


Renamed src/category_theory/instances/CommRing/adjunctions.lean to src/algebra/CommRing/adjunctions.lean
- \+ *lemma* CommRing.polynomial_ring_map_val
- \+ *lemma* CommRing.polynomial_ring_obj_α
- \- *lemma* category_theory.instances.CommRing.polynomial_ring_map_val
- \- *lemma* category_theory.instances.CommRing.polynomial_ring_obj_α

Renamed src/category_theory/instances/CommRing/basic.lean to src/algebra/CommRing/basic.lean
- \+ *def* CommRing.Int.cast
- \+ *def* CommRing.Int.hom_unique
- \+ *lemma* CommRing.comp_val
- \+ *abbreviation* CommRing.forget
- \+ *def* CommRing.forget_to_CommMon
- \+ *lemma* CommRing.id_val
- \+ *def* CommRing.is_comm_ring_hom
- \+ *def* CommRing.of
- \+ *def* CommRing.to_Ring
- \+ *def* CommRing
- \+ *abbreviation* Ring.forget
- \+ *def* Ring.of
- \+ *def* Ring
- \- *def* category_theory.instances.CommRing.Int.cast
- \- *def* category_theory.instances.CommRing.Int.hom_unique
- \- *def* category_theory.instances.CommRing.Int
- \- *lemma* category_theory.instances.CommRing.comp_val
- \- *def* category_theory.instances.CommRing.forget
- \- *def* category_theory.instances.CommRing.forget_to_CommMon
- \- *lemma* category_theory.instances.CommRing.hom.ext
- \- *lemma* category_theory.instances.CommRing.hom_coe_app
- \- *lemma* category_theory.instances.CommRing.id_val
- \- *def* category_theory.instances.CommRing.of
- \- *def* category_theory.instances.CommRing.to_Ring
- \- *def* category_theory.instances.CommRing
- \- *def* category_theory.instances.Ring

Renamed src/category_theory/instances/CommRing/colimits.lean to src/algebra/CommRing/colimits.lean
- \+ *def* CommRing.colimits.cocone_fun
- \+ *def* CommRing.colimits.cocone_morphism
- \+ *lemma* CommRing.colimits.cocone_naturality
- \+ *lemma* CommRing.colimits.cocone_naturality_components
- \+ *def* CommRing.colimits.colimit
- \+ *def* CommRing.colimits.colimit_cocone
- \+ *def* CommRing.colimits.colimit_is_colimit
- \+ *def* CommRing.colimits.colimit_setoid
- \+ *def* CommRing.colimits.colimit_type
- \+ *def* CommRing.colimits.desc_fun
- \+ *def* CommRing.colimits.desc_fun_lift
- \+ *def* CommRing.colimits.desc_morphism
- \+ *lemma* CommRing.colimits.naturality_bundled
- \+ *inductive* CommRing.colimits.prequotient
- \+ *lemma* CommRing.colimits.quot_add
- \+ *lemma* CommRing.colimits.quot_mul
- \+ *lemma* CommRing.colimits.quot_neg
- \+ *lemma* CommRing.colimits.quot_one
- \+ *lemma* CommRing.colimits.quot_zero
- \+ *inductive* CommRing.colimits.relation
- \- *def* category_theory.instances.CommRing.colimits.cocone_fun
- \- *def* category_theory.instances.CommRing.colimits.cocone_morphism
- \- *lemma* category_theory.instances.CommRing.colimits.cocone_naturality
- \- *lemma* category_theory.instances.CommRing.colimits.cocone_naturality_components
- \- *def* category_theory.instances.CommRing.colimits.colimit
- \- *def* category_theory.instances.CommRing.colimits.colimit_cocone
- \- *def* category_theory.instances.CommRing.colimits.colimit_is_colimit
- \- *def* category_theory.instances.CommRing.colimits.colimit_setoid
- \- *def* category_theory.instances.CommRing.colimits.colimit_type
- \- *def* category_theory.instances.CommRing.colimits.desc_fun
- \- *def* category_theory.instances.CommRing.colimits.desc_fun_lift
- \- *def* category_theory.instances.CommRing.colimits.desc_morphism
- \- *lemma* category_theory.instances.CommRing.colimits.naturality_bundled
- \- *inductive* category_theory.instances.CommRing.colimits.prequotient
- \- *lemma* category_theory.instances.CommRing.colimits.quot_add
- \- *lemma* category_theory.instances.CommRing.colimits.quot_mul
- \- *lemma* category_theory.instances.CommRing.colimits.quot_neg
- \- *lemma* category_theory.instances.CommRing.colimits.quot_one
- \- *lemma* category_theory.instances.CommRing.colimits.quot_zero
- \- *inductive* category_theory.instances.CommRing.colimits.relation

Renamed src/category_theory/instances/CommRing/default.lean to src/algebra/CommRing/default.lean


Renamed src/category_theory/instances/CommRing/limits.lean to src/algebra/CommRing/limits.lean
- \+ *def* CommRing.limit
- \+ *def* CommRing.limit_is_limit
- \- *def* category_theory.instances.CommRing.limit
- \- *def* category_theory.instances.CommRing.limit_is_limit

Renamed src/category_theory/instances/Mon/basic.lean to src/algebra/Mon/basic.lean
- \+ *abbreviation* CommMon.forget
- \+ *def* CommMon.forget_to_Mon
- \+ *def* CommMon.is_comm_monoid_hom
- \+ *def* CommMon.of
- \+ *def* CommMon
- \+ *abbreviation* Mon.forget
- \+ *def* Mon.of
- \+ *def* Mon
- \- *def* category_theory.instances.CommMon.forget_to_Mon
- \- *def* category_theory.instances.CommMon
- \- *def* category_theory.instances.Mon
- \- *def* category_theory.instances.is_comm_monoid_hom

Renamed src/category_theory/instances/Mon/colimits.lean to src/algebra/Mon/colimits.lean
- \+ *def* Mon.colimits.cocone_fun
- \+ *def* Mon.colimits.cocone_morphism
- \+ *lemma* Mon.colimits.cocone_naturality
- \+ *lemma* Mon.colimits.cocone_naturality_components
- \+ *def* Mon.colimits.colimit
- \+ *def* Mon.colimits.colimit_cocone
- \+ *def* Mon.colimits.colimit_is_colimit
- \+ *def* Mon.colimits.colimit_setoid
- \+ *def* Mon.colimits.colimit_type
- \+ *def* Mon.colimits.desc_fun
- \+ *def* Mon.colimits.desc_fun_lift
- \+ *def* Mon.colimits.desc_morphism
- \+ *inductive* Mon.colimits.prequotient
- \+ *lemma* Mon.colimits.quot_mul
- \+ *lemma* Mon.colimits.quot_one
- \+ *inductive* Mon.colimits.relation
- \- *def* category_theory.instances.Mon.colimits.cocone_fun
- \- *def* category_theory.instances.Mon.colimits.cocone_morphism
- \- *lemma* category_theory.instances.Mon.colimits.cocone_naturality
- \- *lemma* category_theory.instances.Mon.colimits.cocone_naturality_components
- \- *def* category_theory.instances.Mon.colimits.colimit
- \- *def* category_theory.instances.Mon.colimits.colimit_cocone
- \- *def* category_theory.instances.Mon.colimits.colimit_is_colimit
- \- *def* category_theory.instances.Mon.colimits.colimit_setoid
- \- *def* category_theory.instances.Mon.colimits.colimit_type
- \- *def* category_theory.instances.Mon.colimits.desc_fun
- \- *def* category_theory.instances.Mon.colimits.desc_fun_lift
- \- *def* category_theory.instances.Mon.colimits.desc_morphism
- \- *inductive* category_theory.instances.Mon.colimits.prequotient
- \- *lemma* category_theory.instances.Mon.colimits.quot_mul
- \- *lemma* category_theory.instances.Mon.colimits.quot_one
- \- *inductive* category_theory.instances.Mon.colimits.relation

Renamed src/category_theory/instances/Mon/default.lean to src/algebra/Mon/default.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/stalks.lean


Modified src/category_theory/concrete_category.lean
- \- *lemma* category_theory.bundled.bundled_hom.ext
- \+/\- *lemma* category_theory.bundled.concrete_category_id
- \+ *lemma* category_theory.bundled.hom_ext

Deleted src/category_theory/instances/Top/default.lean


Deleted src/category_theory/instances/TopCommRing/default.lean


Renamed src/category_theory/instances/groups.lean to src/group_theory/category.lean
- \+ *def* AddCommGroup.forget_to_Group
- \+ *def* AddCommGroup.is_add_comm_group_hom
- \+ *def* AddCommGroup.of
- \+ *def* AddCommGroup
- \+ *def* Group.of
- \+ *def* Group
- \- *def* category_theory.instances.AddCommGroup.forget_to_Group
- \- *def* category_theory.instances.AddCommGroup
- \- *def* category_theory.instances.Group
- \- *def* category_theory.instances.is_add_comm_group_hom

Renamed src/category_theory/instances/measurable_space.lean to src/measure_theory/Meas.lean
- \+ *def* Borel
- \+ *def* Meas.of
- \+ *def* Meas
- \- *def* category_theory.instances.Borel
- \- *def* category_theory.instances.Meas

Renamed src/category_theory/instances/Top/adjunctions.lean to src/topology/Top/adjunctions.lean
- \+ *def* Top.adj₁
- \+ *def* Top.adj₂
- \- *def* category_theory.instances.Top.adj₁
- \- *def* category_theory.instances.Top.adj₂

Renamed src/category_theory/instances/Top/basic.lean to src/topology/Top/basic.lean
- \+ *def* Top.discrete
- \+ *abbreviation* Top.forget
- \+ *def* Top.of
- \+ *def* Top.trivial
- \+ *def* Top
- \- *def* category_theory.instances.Top.discrete
- \- *abbreviation* category_theory.instances.Top.forget
- \- *def* category_theory.instances.Top.of
- \- *def* category_theory.instances.Top.trivial
- \- *def* category_theory.instances.Top

Added src/topology/Top/default.lean


Renamed src/category_theory/instances/Top/epi_mono.lean to src/topology/Top/epi_mono.lean
- \+ *lemma* Top.epi_iff_surjective
- \+ *lemma* Top.mono_iff_injective
- \- *lemma* category_theory.instances.Top.epi_iff_surjective
- \- *lemma* category_theory.instances.Top.mono_iff_injective

Renamed src/category_theory/instances/Top/limits.lean to src/topology/Top/limits.lean
- \+ *def* Top.colimit
- \+ *def* Top.colimit_is_colimit
- \+ *def* Top.limit
- \+ *def* Top.limit_is_limit
- \- *def* category_theory.instances.Top.colimit
- \- *def* category_theory.instances.Top.colimit_is_colimit
- \- *def* category_theory.instances.Top.limit
- \- *def* category_theory.instances.Top.limit_is_limit

Renamed src/category_theory/instances/Top/open_nhds.lean to src/topology/Top/open_nhds.lean


Renamed src/category_theory/instances/Top/opens.lean to src/topology/Top/opens.lean


Renamed src/category_theory/instances/Top/presheaf.lean to src/topology/Top/presheaf.lean
- \+ *def* Top.presheaf.pushforward.comp
- \+ *lemma* Top.presheaf.pushforward.comp_hom_app
- \+ *lemma* Top.presheaf.pushforward.comp_inv_app
- \+ *def* Top.presheaf.pushforward.id
- \+ *lemma* Top.presheaf.pushforward.id_hom_app'
- \+ *lemma* Top.presheaf.pushforward.id_hom_app
- \+ *lemma* Top.presheaf.pushforward.id_inv_app'
- \+ *def* Top.presheaf.pushforward
- \+ *def* Top.presheaf.pushforward_eq
- \+ *lemma* Top.presheaf.pushforward_eq_eq
- \+ *def* Top.presheaf
- \- *def* category_theory.instances.Top.presheaf.pushforward.comp
- \- *lemma* category_theory.instances.Top.presheaf.pushforward.comp_hom_app
- \- *lemma* category_theory.instances.Top.presheaf.pushforward.comp_inv_app
- \- *def* category_theory.instances.Top.presheaf.pushforward.id
- \- *lemma* category_theory.instances.Top.presheaf.pushforward.id_hom_app'
- \- *lemma* category_theory.instances.Top.presheaf.pushforward.id_hom_app
- \- *lemma* category_theory.instances.Top.presheaf.pushforward.id_inv_app'
- \- *def* category_theory.instances.Top.presheaf.pushforward
- \- *def* category_theory.instances.Top.presheaf.pushforward_eq
- \- *lemma* category_theory.instances.Top.presheaf.pushforward_eq_eq
- \- *def* category_theory.instances.Top.presheaf

Renamed src/category_theory/instances/Top/presheaf_of_functions.lean to src/topology/Top/presheaf_of_functions.lean
- \+ *def* Top.CommRing_yoneda
- \+ *lemma* Top.continuous_functions.add
- \+ *def* Top.continuous_functions.map
- \+ *lemma* Top.continuous_functions.mul
- \+ *lemma* Top.continuous_functions.one
- \+ *def* Top.continuous_functions.pullback
- \+ *def* Top.continuous_functions
- \+ *def* Top.presheaf_to_Top
- \+ *def* Top.presheaf_to_TopCommRing
- \- *def* category_theory.instances.Top.CommRing_yoneda
- \- *lemma* category_theory.instances.Top.continuous_functions.add
- \- *def* category_theory.instances.Top.continuous_functions.map
- \- *lemma* category_theory.instances.Top.continuous_functions.mul
- \- *lemma* category_theory.instances.Top.continuous_functions.one
- \- *def* category_theory.instances.Top.continuous_functions.pullback
- \- *def* category_theory.instances.Top.continuous_functions
- \- *def* category_theory.instances.Top.presheaf_to_Top
- \- *def* category_theory.instances.Top.presheaf_to_TopCommRing

Renamed src/category_theory/instances/Top/stalks.lean to src/topology/Top/stalks.lean
- \+ *def* Top.presheaf.stalk
- \+ *def* Top.presheaf.stalk_functor
- \+ *lemma* Top.presheaf.stalk_functor_obj
- \+ *lemma* Top.presheaf.stalk_pushforward.comp
- \+ *lemma* Top.presheaf.stalk_pushforward.id
- \+ *def* Top.presheaf.stalk_pushforward
- \- *def* category_theory.instances.Top.presheaf.stalk
- \- *def* category_theory.instances.Top.presheaf.stalk_functor
- \- *lemma* category_theory.instances.Top.presheaf.stalk_functor_obj
- \- *lemma* category_theory.instances.Top.presheaf.stalk_pushforward.comp
- \- *lemma* category_theory.instances.Top.presheaf.stalk_pushforward.id
- \- *def* category_theory.instances.Top.presheaf.stalk_pushforward

Renamed src/category_theory/instances/TopCommRing/basic.lean to src/topology/algebra/TopCommRing/basic.lean
- \+ *def* TopCommRing.forget
- \+ *def* TopCommRing.forget_to_CommRing
- \+ *def* TopCommRing.forget_to_Top
- \+ *def* TopCommRing.forget_to_Type_via_CommRing
- \+ *def* TopCommRing.forget_to_Type_via_Top
- \+ *def* TopCommRing.of
- \+ *structure* TopCommRing
- \- *def* category_theory.instances.TopCommRing.forget
- \- *def* category_theory.instances.TopCommRing.forget_to_CommRing
- \- *def* category_theory.instances.TopCommRing.forget_to_Top
- \- *def* category_theory.instances.TopCommRing.forget_to_Type_via_CommRing
- \- *def* category_theory.instances.TopCommRing.forget_to_Type_via_Top
- \- *def* category_theory.instances.TopCommRing.of
- \- *structure* category_theory.instances.TopCommRing

Added src/topology/algebra/TopCommRing/default.lean




## [2019-05-30 12:43:47](https://github.com/leanprover-community/mathlib/commit/c49ac06)
feat(category_theory/monoidal): monoidal categories, monoidal functors ([#1002](https://github.com/leanprover-community/mathlib/pull/1002))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* almost
* oops
* getting there
* one more
* sleep
* good to go
* fix names
* renaming
* linebreak
* temporary notations
* notations for associator, unitors?
* more notation
* names
* more names
* oops
* renaming, and namespaces
* comment
* fix comment
* remove unnecessary open, formatting
* removing dsimps
* replace with simp lemmas
* fix
#### Estimated changes
Added src/category_theory/monoidal/category.lean
- \+ *lemma* category_theory.monoidal_category.associator_inv_naturality
- \+ *def* category_theory.monoidal_category.associator_nat_iso
- \+ *lemma* category_theory.monoidal_category.comp_tensor_id
- \+ *lemma* category_theory.monoidal_category.id_tensor_comp
- \+ *lemma* category_theory.monoidal_category.id_tensor_comp_tensor_id
- \+ *lemma* category_theory.monoidal_category.inv_tensor
- \+ *def* category_theory.monoidal_category.left_assoc_tensor
- \+ *lemma* category_theory.monoidal_category.left_assoc_tensor_map
- \+ *lemma* category_theory.monoidal_category.left_assoc_tensor_obj
- \+ *lemma* category_theory.monoidal_category.left_unitor_inv_naturality
- \+ *def* category_theory.monoidal_category.left_unitor_nat_iso
- \+ *lemma* category_theory.monoidal_category.left_unitor_product_aux
- \+ *lemma* category_theory.monoidal_category.left_unitor_product_aux_perimeter
- \+ *lemma* category_theory.monoidal_category.left_unitor_product_aux_square
- \+ *lemma* category_theory.monoidal_category.left_unitor_product_aux_triangle
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor
- \+ *lemma* category_theory.monoidal_category.left_unitor_tensor_inv
- \+ *lemma* category_theory.monoidal_category.pentagon_inv
- \+ *def* category_theory.monoidal_category.right_assoc_tensor
- \+ *lemma* category_theory.monoidal_category.right_assoc_tensor_map
- \+ *lemma* category_theory.monoidal_category.right_assoc_tensor_obj
- \+ *lemma* category_theory.monoidal_category.right_unitor_inv_naturality
- \+ *def* category_theory.monoidal_category.right_unitor_nat_iso
- \+ *lemma* category_theory.monoidal_category.right_unitor_product_aux
- \+ *lemma* category_theory.monoidal_category.right_unitor_product_aux_perimeter
- \+ *lemma* category_theory.monoidal_category.right_unitor_product_aux_square
- \+ *lemma* category_theory.monoidal_category.right_unitor_product_aux_triangle
- \+ *lemma* category_theory.monoidal_category.right_unitor_tensor
- \+ *lemma* category_theory.monoidal_category.right_unitor_tensor_inv
- \+ *def* category_theory.monoidal_category.tensor
- \+ *lemma* category_theory.monoidal_category.tensor_id_comp_id_tensor
- \+ *lemma* category_theory.monoidal_category.tensor_left_iff
- \+ *lemma* category_theory.monoidal_category.tensor_right_iff
- \+ *def* category_theory.monoidal_category.tensor_unit_left
- \+ *def* category_theory.monoidal_category.tensor_unit_right
- \+ *lemma* category_theory.monoidal_category.triangle_assoc_comp_left
- \+ *lemma* category_theory.monoidal_category.triangle_assoc_comp_left_inv
- \+ *lemma* category_theory.monoidal_category.triangle_assoc_comp_right
- \+ *lemma* category_theory.monoidal_category.triangle_assoc_comp_right_inv
- \+ *def* category_theory.tensor_iso

Added src/category_theory/monoidal/category_aux.lean
- \+ *def* category_theory.assoc_natural
- \+ *def* category_theory.assoc_obj
- \+ *def* category_theory.left_unitor_natural
- \+ *def* category_theory.left_unitor_obj
- \+ *def* category_theory.pentagon
- \+ *def* category_theory.right_unitor_natural
- \+ *def* category_theory.right_unitor_obj
- \+ *def* category_theory.tensor_hom_type
- \+ *def* category_theory.tensor_obj_type
- \+ *def* category_theory.triangle

Added src/category_theory/monoidal/functor.lean
- \+ *def* category_theory.lax_monoidal_functor.comp
- \+ *lemma* category_theory.lax_monoidal_functor.comp_map
- \+ *lemma* category_theory.lax_monoidal_functor.comp_obj
- \+ *lemma* category_theory.lax_monoidal_functor.comp_ε
- \+ *lemma* category_theory.lax_monoidal_functor.comp_μ
- \+ *structure* category_theory.lax_monoidal_functor
- \+ *def* category_theory.monoidal_functor.comp
- \+ *def* category_theory.monoidal_functor.id
- \+ *lemma* category_theory.monoidal_functor.id_map
- \+ *lemma* category_theory.monoidal_functor.id_obj
- \+ *lemma* category_theory.monoidal_functor.id_ε
- \+ *lemma* category_theory.monoidal_functor.id_μ
- \+ *def* category_theory.monoidal_functor.ε_iso
- \+ *def* category_theory.monoidal_functor.μ_iso
- \+ *def* category_theory.monoidal_functor.μ_nat_iso
- \+ *structure* category_theory.monoidal_functor



## [2019-05-29 22:06:00](https://github.com/leanprover-community/mathlib/commit/4845b66)
feat(ring_theory): free_ring and free_comm_ring ([#734](https://github.com/leanprover-community/mathlib/pull/734))
* feat(ring_theory): free_ring and free_comm_ring
* Define isomorphism with mv_polynomial int
* Ring hom free_ring -> free_comm_ring; 1 sorry left
* Coe from free_ring to free_comm_ring is ring_hom
* WIP
* WIP
* WIP
* WIP
* Refactoring a bunch of stuff
* functor.map_equiv
* Fix build
* Fix build
* Make multiset.subsingleton_equiv computable
* Define specific equivs using general machinery
* Fix build
* Remove old commented code
* feat(data/equiv/functor): map_equiv
* fix(data/multiset): remove duplicate setoid instance
* namespace changes
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean


Added src/ring_theory/free_comm_ring.lean
- \+ *def* free_comm_ring.lift
- \+ *lemma* free_comm_ring.lift_add
- \+ *lemma* free_comm_ring.lift_comp_of
- \+ *lemma* free_comm_ring.lift_mul
- \+ *lemma* free_comm_ring.lift_neg
- \+ *lemma* free_comm_ring.lift_of
- \+ *lemma* free_comm_ring.lift_one
- \+ *lemma* free_comm_ring.lift_pow
- \+ *lemma* free_comm_ring.lift_sub
- \+ *lemma* free_comm_ring.lift_zero
- \+ *def* free_comm_ring.map
- \+ *lemma* free_comm_ring.map_add
- \+ *lemma* free_comm_ring.map_mul
- \+ *lemma* free_comm_ring.map_neg
- \+ *lemma* free_comm_ring.map_of
- \+ *lemma* free_comm_ring.map_one
- \+ *lemma* free_comm_ring.map_pow
- \+ *lemma* free_comm_ring.map_sub
- \+ *lemma* free_comm_ring.map_zero
- \+ *def* free_comm_ring.of
- \+ *def* free_comm_ring
- \+ *def* free_comm_ring_equiv_mv_polynomial_int
- \+ *def* free_comm_ring_pempty_equiv_int
- \+ *def* free_comm_ring_punit_equiv_polynomial_int
- \+ *lemma* free_ring.coe_eq
- \+ *def* free_ring.subsingleton_equiv_free_comm_ring
- \+ *def* free_ring.to_free_comm_ring
- \+ *def* free_ring_pempty_equiv_int
- \+ *def* free_ring_punit_equiv_polynomial_int

Added src/ring_theory/free_ring.lean
- \+ *def* free_ring.lift
- \+ *lemma* free_ring.lift_add
- \+ *lemma* free_ring.lift_comp_of
- \+ *lemma* free_ring.lift_mul
- \+ *lemma* free_ring.lift_neg
- \+ *lemma* free_ring.lift_of
- \+ *lemma* free_ring.lift_one
- \+ *lemma* free_ring.lift_pow
- \+ *lemma* free_ring.lift_sub
- \+ *lemma* free_ring.lift_zero
- \+ *def* free_ring.map
- \+ *lemma* free_ring.map_add
- \+ *lemma* free_ring.map_mul
- \+ *lemma* free_ring.map_neg
- \+ *lemma* free_ring.map_of
- \+ *lemma* free_ring.map_one
- \+ *lemma* free_ring.map_pow
- \+ *lemma* free_ring.map_sub
- \+ *lemma* free_ring.map_zero
- \+ *def* free_ring.of
- \+ *def* free_ring



## [2019-05-29 11:10:22](https://github.com/leanprover-community/mathlib/commit/d935bc3)
feat(presheaves/stalks): stalks of presheafs, and presheafed spaces with extra structure on stalks ([#1018](https://github.com/leanprover-community/mathlib/pull/1018))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* feat(category_theory): stalks of sheaves
* renaming
* fixes after rebase
* nothing
* yay, got rid of the @s
* attempting a very general version of structured stalks
* missed one
* typo
* WIP
* oops
* the presheaf of continuous functions to ℂ
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* renaming
* probably working again?
* update notation
* remove old lemma
* fix
* comment out unfinished stuff
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* moving instances
* remove crap
* tidy
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* cleanup
* cleaning up
* cleaning up
* move
* cleaning up
* structured stalks
* comment
* structured stalks
* more simp lemmas
* formatting
* Update src/category_theory/instances/Top/presheaf_of_functions.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fixes in response to review
* tidy regressions... :-(
* oops
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/instances/TopCommRing/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* def to lemma
* remove useless lemma
* explicit associator
* broken
* can't get proofs to work...
* remove superfluous imports
* missing headers
* change example
* reverting changes to tidy
* remove presheaf_Z, as it doesn't work at the moment
* fixes
* fixes
* fix
* postponing stuff on structured stalks for a later PR
* coercions
* getting rid of all the `erw`
* omitting some proofs
* deleting more proofs
* convert begin ... end to by
* local
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* algebraic_geometry.PresheafedSpace.as_coe
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_c_app
- \- *lemma* algebraic_geometry.PresheafedSpace.comp_f
- \+ *lemma* algebraic_geometry.PresheafedSpace.f_as_coe
- \+ *lemma* algebraic_geometry.PresheafedSpace.hom_mk_coe
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_c_app
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_coe
- \- *lemma* algebraic_geometry.PresheafedSpace.id_f
- \+ *lemma* algebraic_geometry.PresheafedSpace.mk_coe

Added src/algebraic_geometry/stalks.lean
- \+ *def* algebraic_geometry.PresheafedSpace.stalk
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.comp
- \+ *lemma* algebraic_geometry.PresheafedSpace.stalk_map.id
- \+ *def* algebraic_geometry.PresheafedSpace.stalk_map

Modified src/category_theory/functor_category.lean
- \+ *lemma* category_theory.functor.flip_map_app
- \+ *lemma* category_theory.functor.flip_obj_obj

Modified src/category_theory/instances/Top/basic.lean
- \+ *abbreviation* category_theory.instances.Top.forget

Modified src/category_theory/instances/Top/open_nhds.lean
- \+ *lemma* topological_space.open_nhds.map_obj

Modified src/category_theory/instances/Top/opens.lean
- \+ *lemma* topological_space.opens.map_obj

Modified src/category_theory/instances/Top/presheaf.lean


Modified src/category_theory/instances/Top/presheaf_of_functions.lean


Added src/category_theory/instances/Top/stalks.lean
- \+ *def* category_theory.instances.Top.presheaf.stalk
- \+ *def* category_theory.instances.Top.presheaf.stalk_functor
- \+ *lemma* category_theory.instances.Top.presheaf.stalk_functor_obj
- \+ *lemma* category_theory.instances.Top.presheaf.stalk_pushforward.comp
- \+ *lemma* category_theory.instances.Top.presheaf.stalk_pushforward.id
- \+ *def* category_theory.instances.Top.presheaf.stalk_pushforward

Modified src/category_theory/instances/TopCommRing/basic.lean
- \+/\- *def* category_theory.instances.TopCommRing.forget_to_Type_via_CommRing
- \+/\- *def* category_theory.instances.TopCommRing.forget_to_Type_via_Top

Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/whiskering.lean


Modified src/data/opposite.lean




## [2019-05-29 06:03:02](https://github.com/leanprover-community/mathlib/commit/0de4bba)
feat(ordered_group): add missing instance ([#1094](https://github.com/leanprover-community/mathlib/pull/1094))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+/\- *lemma* neg_neg_iff_pos



## [2019-05-28 15:01:35](https://github.com/leanprover-community/mathlib/commit/b20b722)
fix(tactic/rcases): add parse desc to rcases/rintro ([#1091](https://github.com/leanprover-community/mathlib/pull/1091))
#### Estimated changes
Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2019-05-26 20:12:00](https://github.com/leanprover-community/mathlib/commit/d434397)
feat(group_theory/conjugates) : define conjugates ([#1029](https://github.com/leanprover-community/mathlib/pull/1029))
* feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
* moving stuff to where it belongs
* removed unecessary import
* Changed to union
* Update src/group_theory/subgroup.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Stylistic changes
* Added authorship
* Moved mem_conjugates_of_set
* Authorship
* Trying fixes
* Putting everything in the right order
* removed import
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* conj_inv
- \+ *lemma* conj_mul

Modified src/group_theory/subgroup.lean
- \+ *lemma* group.conj_mem_conjugates_of_set
- \+ *def* group.conjugates
- \+ *def* group.conjugates_of_set
- \+ *theorem* group.conjugates_of_set_mono
- \+ *theorem* group.conjugates_of_set_subset
- \+ *theorem* group.conjugates_of_set_subset_normal_closure
- \+ *lemma* group.conjugates_subset
- \+ *lemma* group.mem_conjugates_of_set_iff
- \+ *lemma* group.mem_conjugates_self
- \+ *def* group.normal_closure
- \+ *theorem* group.normal_closure_mono
- \+ *theorem* group.normal_closure_subset
- \+ *lemma* group.normal_closure_subset_iff
- \+ *theorem* group.subset_conjugates_of_set
- \+ *theorem* group.subset_normal_closure



## [2019-05-24 05:29:59](https://github.com/leanprover-community/mathlib/commit/c6a7f30)
refactor(set_theory/ordinal): shorten proof of well_ordering_thm ([#1078](https://github.com/leanprover-community/mathlib/pull/1078))
* refactor(set_theory/ordinal): shorten proof of well_ordering_thm§
* Update ordinal.lean
* Update ordinal.lean
* Update ordinal.lean
* Improve readability
* shorten proof
* Shorten proof
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \- *theorem* chain_ub
- \+/\- *theorem* well_ordering_thm



## [2019-05-23 13:50:06](https://github.com/leanprover-community/mathlib/commit/62acd6b)
chore(CommRing/adjunctions): refactor proofs ([#1049](https://github.com/leanprover-community/mathlib/pull/1049))
* splitting adjunction.lean
* chore(CommRing/adjunctions): refactor proofs
* remove unnecessary assumptions
* add helpful doc-string
* cleanup
* breaking things, haven't finished yet
* deterministic timeout
* unfold_coes to the rescue
* one more int.cast
* yet another int.cast
* Update src/data/mv_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/data/mv_polynomial.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* WIP
* Fix build
* Fix build
#### Estimated changes
Renamed src/category_theory/adjunction.lean to src/category_theory/adjunction/basic.lean
- \- *def* category_theory.adjunction.cocones_iso
- \- *def* category_theory.adjunction.cones_iso
- \- *def* category_theory.adjunction.functoriality_is_left_adjoint
- \- *def* category_theory.adjunction.functoriality_is_right_adjoint
- \- *def* category_theory.adjunction.left_adjoint_preserves_colimits
- \- *def* category_theory.adjunction.right_adjoint_preserves_limits

Added src/category_theory/adjunction/default.lean


Added src/category_theory/adjunction/limits.lean
- \+ *def* category_theory.adjunction.cocones_iso
- \+ *def* category_theory.adjunction.cones_iso
- \+ *def* category_theory.adjunction.functoriality_is_left_adjoint
- \+ *def* category_theory.adjunction.functoriality_is_right_adjoint
- \+ *def* category_theory.adjunction.left_adjoint_preserves_colimits
- \+ *def* category_theory.adjunction.right_adjoint_preserves_limits

Modified src/category_theory/epi_mono.lean


Modified src/category_theory/instances/CommRing/adjunctions.lean
- \- *lemma* category_theory.instances.CommRing.hom_coe_app'

Modified src/category_theory/instances/CommRing/basic.lean
- \- *def* category_theory.instances.CommRing.int.eq_cast'

Modified src/category_theory/instances/Top/adjunctions.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* category_theory.types_comp
- \+/\- *lemma* category_theory.types_id

Modified src/data/int/basic.lean
- \+ *lemma* int.eq_cast'

Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.eval₂_cast_comp
- \+ *lemma* mv_polynomial.eval₂_hom_X
- \+ *lemma* mv_polynomial.hom_C
- \+/\- *lemma* mv_polynomial.rename_id
- \+/\- *lemma* mv_polynomial.rename_rename

Modified src/tactic/tidy.lean




## [2019-05-23 11:08:00](https://github.com/leanprover-community/mathlib/commit/15fecbd)
doc(finsupp,category_theory): fixes ([#1075](https://github.com/leanprover-community/mathlib/pull/1075))
* doc
* update emb_domain doc string
* typo
#### Estimated changes
Modified docs/theories/category_theory.md


Modified src/data/finsupp.lean




## [2019-05-22 19:04:36](https://github.com/leanprover-community/mathlib/commit/d07e3b3)
feat(linear_algebra/basic): general_linear_group basics ([#1064](https://github.com/leanprover-community/mathlib/pull/1064))
* feat(linear_algebra/basic): general_linear_group basics
This patch proves that the general_linear_group (defined as units in the
endomorphism ring) are equivalent to the group of linear equivalences.
* shorten proof of ext
* Add mul_equiv
* Use coe
* Fix stupid error
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.ext
- \+ *lemma* linear_equiv.to_equiv_injective
- \+ *def* linear_map.general_linear_group.general_linear_equiv
- \+ *lemma* linear_map.general_linear_group.general_linear_equiv_to_linear_map
- \+ *def* linear_map.general_linear_group.of_linear_equiv
- \+ *def* linear_map.general_linear_group.to_linear_equiv



## [2019-05-22 16:32:40](https://github.com/leanprover-community/mathlib/commit/f004d32)
feat(data/nat): various lemmas ([#1017](https://github.com/leanprover-community/mathlib/pull/1017))
* feat(data/nat): various lemmas
* protect a definition
* fixes
* Rob's suggestions
* Mario’s proof
(Working offline, let’s see what Travis says)
* minigolf
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_eq_self
- \+ *lemma* nat.div_le_div_left
- \+ *lemma* nat.eq_of_dvd_quot_one
- \+ *lemma* nat.eq_zero_of_double_le
- \+ *lemma* nat.eq_zero_of_le_div
- \+ *lemma* nat.eq_zero_of_le_half
- \+ *lemma* nat.eq_zero_of_mul_le
- \+ *lemma* nat.lt_mul_of_div_lt



## [2019-05-21 21:29:42](https://github.com/leanprover-community/mathlib/commit/971ddcc)
feat(*): image_closure ([#1069](https://github.com/leanprover-community/mathlib/pull/1069))
Prove that the image of the closure is the closure of the image,
for submonoids/groups/rings.
From the perfectoid project.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* add_group.image_closure
- \+ *lemma* group.image_closure

Modified src/group_theory/submonoid.lean
- \+ *lemma* add_monoid.image_closure
- \+ *lemma* monoid.image_closure

Modified src/ring_theory/subring.lean
- \+ *lemma* ring.image_closure



## [2019-05-21 16:01:07](https://github.com/leanprover-community/mathlib/commit/3461399)
refactor(integration.lean): changing `measure_space` to `measurable_space` ([#1072](https://github.com/leanprover-community/mathlib/pull/1072))
I've been using this file and `range_const` doesn't seem to require the spurious `measure_space` instance. `measurable_space` seems to suffice.
#### Estimated changes
Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.range_const



## [2019-05-20 19:27:04](https://github.com/leanprover-community/mathlib/commit/cb30c97)
feat(algebra/pi_instances): product of submonoids/groups/rings ([#1066](https://github.com/leanprover-community/mathlib/pull/1066))
From the perfectoid project.
#### Estimated changes
Modified src/algebra/pi_instances.lean




## [2019-05-20 18:35:19](https://github.com/leanprover-community/mathlib/commit/0ab8a89)
feat(category_theory): limits in CommRing ([#1006](https://github.com/leanprover-community/mathlib/pull/1006))
* feat(category_theory): limits in CommRing
* by
* rename
* sections
* Update src/category_theory/types.lean
Co-Authored-By: Johannes Hölzl <johannes.hoelzl@gmx.de>
#### Estimated changes
Modified src/algebra/pi_instances.lean
- \- *def* pi.is_ring_hom_pi

Modified src/category_theory/instances/CommRing/basic.lean


Added src/category_theory/instances/CommRing/limits.lean
- \+ *def* category_theory.instances.CommRing.limit
- \+ *def* category_theory.instances.CommRing.limit_is_limit

Modified src/category_theory/limits/types.lean


Modified src/category_theory/types.lean
- \+ *def* category_theory.functor.sections



## [2019-05-20 15:36:59](https://github.com/leanprover-community/mathlib/commit/8cf7c4c)
chore(topology/algebra/monoid): continuous_mul_left/right ([#1065](https://github.com/leanprover-community/mathlib/pull/1065))
#### Estimated changes
Modified src/topology/algebra/monoid.lean
- \+ *lemma* continuous_mul_left
- \+ *lemma* continuous_mul_right



## [2019-05-20 15:11:50](https://github.com/leanprover-community/mathlib/commit/593938c)
chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map ([#1062](https://github.com/leanprover-community/mathlib/pull/1062))
* chore(ring_theory/algebra): simp-lemmas for alg_hom.to_linear_map
From the perfectoid project.
* Stupid error
* Update src/ring_theory/algebra.lean
Co-Authored-By: Chris Hughes <33847686+ChrisHughes24@users.noreply.github.com>
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_hom.comp_to_linear_map
- \+ *lemma* alg_hom.id_to_linear_map



## [2019-05-20 11:52:29](https://github.com/leanprover-community/mathlib/commit/d001abf)
feat(tactic/basic): adds `contrapose` tactic ([#1015](https://github.com/leanprover-community/mathlib/pull/1015))
* feat(tactic/basic): adds `contrapose` tactic
* fix(tactic/push_neg): fix is_prop testing
* Setup error message testing following Rob, add tests for `contrapose`
* refactor(tactic/interactive): move noninteractive success_if_fail_with_msg to tactic/core
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/tactic/push_neg.lean
- \+ *lemma* imp_of_not_imp_not

Modified test/push_neg.lean




## [2019-05-20 11:16:53](https://github.com/leanprover-community/mathlib/commit/15a6af2)
feat(topology/opens): continuous.comap : opens Y → opens X ([#1061](https://github.com/leanprover-community/mathlib/pull/1061))
* feat(topology/opens): continuous.comap : opens Y → opens X
From the perfectoid project.
* Update opens.lean
#### Estimated changes
Modified src/topology/opens.lean
- \+ *def* continuous.comap
- \+ *lemma* continuous.comap_id
- \+ *lemma* continuous.comap_mono



## [2019-05-20 09:26:59](https://github.com/leanprover-community/mathlib/commit/d4c7b7a)
feat(tactic/linarith): better input syntax linarith only [...] ([#1056](https://github.com/leanprover-community/mathlib/pull/1056))
* feat(tactic/ring, tactic/linarith): add reducibility parameter
* fix(tactic/ring): interactive parsing for argument to ring1
* feat(tactic/linarith): better input syntax linarith only [...]
* fix(docs/tactics): fix linarith doc
#### Estimated changes
Modified docs/tactics.md


Modified src/analysis/complex/exponential.lean


Modified src/data/complex/exponential.lean


Modified src/tactic/core.lean


Modified src/tactic/linarith.lean


Modified src/tactic/ring.lean


Modified test/linarith.lean


Modified test/ring.lean




## [2019-05-19 17:40:09](https://github.com/leanprover-community/mathlib/commit/f253401)
refactor: coherent composition order ([#1055](https://github.com/leanprover-community/mathlib/pull/1055))
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/order/filter/basic.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/basic.lean
- \+ *theorem* inter_mem_nhds_within
- \+ *theorem* nhds_within_restrict'

Modified src/topology/constructions.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/order.lean
- \+ *lemma* continuous_at.comp
- \+/\- *lemma* continuous_on.comp
- \+ *lemma* continuous_within_at.comp

Modified src/topology/sequences.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean




## [2019-05-19 13:39:22](https://github.com/leanprover-community/mathlib/commit/cb4c9ee)
refactor(topology/metric/gromov_hausdorff): make Hausdorff_edist irreducible ([#1052](https://github.com/leanprover-community/mathlib/pull/1052))
* refactor(topology/metric/gromov_hausdorff): remove linarith calls
* refactor(topology/metric/hausdorff_dist): make hausdorff_dist irreducible
#### Estimated changes
Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* emetric.Hausdorff_edist_def



## [2019-05-19 12:47:56](https://github.com/leanprover-community/mathlib/commit/b9cb69c)
feat(topology/order): make nhds irreducible ([#1043](https://github.com/leanprover-community/mathlib/pull/1043))
* feat(topology/order): make nhds irreducible
* move nhds irreducible to topology.basic
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* le_nhds_iff
- \+ *lemma* nhds_def
- \+ *lemma* nhds_le_of_le

Modified src/topology/order.lean




## [2019-05-18 16:36:44-04:00](https://github.com/leanprover-community/mathlib/commit/73c3f71)
feat(tactic/squeeze): remove noise from output ([#1047](https://github.com/leanprover-community/mathlib/pull/1047))
#### Estimated changes
Modified src/tactic/squeeze.lean




## [2019-05-18 13:27:57](https://github.com/leanprover-community/mathlib/commit/fa0e757)
refactor(data/complex/exponential): improve trig proofs ([#1041](https://github.com/leanprover-community/mathlib/pull/1041))
* fix(data/complex/exponential): make complex.exp irreducible
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.
* refactor(data/complex/exponential): improve trig proofs
* fix build
* fix(algebra/group): prove lemma for comm_semigroup instead of comm_monoid
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* add_add_sub_cancel
- \+ *lemma* add_sub_sub_cancel
- \+ *theorem* mul_mul_mul_comm
- \+ *lemma* sub_add_add_cancel

Modified src/algebra/group_power.lean
- \+ *theorem* sq_sub_sq

Modified src/algebra/ring.lean
- \+ *theorem* mul_self_sub_mul_self

Modified src/analysis/complex/exponential.lean


Modified src/data/complex/basic.lean
- \+ *lemma* complex.I_sq
- \+ *lemma* complex.eq_conj_iff_re
- \+/\- *lemma* complex.eq_conj_iff_real

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.cos_add_sin_I
- \+ *lemma* complex.cos_sub_sin_I
- \+ *lemma* complex.cos_two_mul'
- \+ *lemma* complex.cosh_add_sinh
- \+ *lemma* complex.cosh_mul_I
- \+ *lemma* complex.cosh_sq_sub_sinh_sq
- \+ *lemma* complex.cosh_sub_sinh
- \- *lemma* complex.sin_pow_two_add_cos_pow_two
- \+ *lemma* complex.sin_sq_add_cos_sq
- \+ *lemma* complex.sinh_add_cosh
- \+ *lemma* complex.sinh_mul_I
- \+ *lemma* complex.two_cos
- \+ *lemma* complex.two_cosh
- \+ *lemma* complex.two_sin
- \+ *lemma* complex.two_sinh
- \- *lemma* real.cos_pow_two_le_one
- \+ *lemma* real.cos_sq_le_one
- \+/\- *lemma* real.exp_injective
- \+/\- *lemma* real.exp_le_exp
- \+/\- *lemma* real.exp_lt_exp
- \+ *lemma* real.exp_strict_mono
- \- *lemma* real.sin_pow_two_add_cos_pow_two
- \- *lemma* real.sin_pow_two_le_one
- \+ *lemma* real.sin_sq_add_cos_sq
- \+ *lemma* real.sin_sq_le_one



## [2019-05-17 20:21:42](https://github.com/leanprover-community/mathlib/commit/5e5298b)
feat(adjointify): make definition easier for elaborator ([#1045](https://github.com/leanprover-community/mathlib/pull/1045))
#### Estimated changes
Modified src/category_theory/equivalence.lean




## [2019-05-17 18:53:41](https://github.com/leanprover-community/mathlib/commit/45afa86)
fix(topology/stone_cech): faster proof from @PatrickMassot ([#1042](https://github.com/leanprover-community/mathlib/pull/1042))
#### Estimated changes
Modified src/topology/stone_cech.lean




## [2019-05-17 17:38:35](https://github.com/leanprover-community/mathlib/commit/901178e)
feat(set_theory/surreal): surreal numbers ([#958](https://github.com/leanprover-community/mathlib/pull/958))
* feat(set_theory/surreal): surreal numbers
* doc(set_theory/surreal): surreal docs
* minor changes in surreal
#### Estimated changes
Added src/set_theory/surreal.lean
- \+ *def* pSurreal.add
- \+ *def* pSurreal.equiv
- \+ *theorem* pSurreal.equiv_refl
- \+ *theorem* pSurreal.equiv_symm
- \+ *theorem* pSurreal.equiv_trans
- \+ *def* pSurreal.inv'
- \+ *def* pSurreal.inv_val
- \+ *theorem* pSurreal.le_congr
- \+ *def* pSurreal.le_lt
- \+ *theorem* pSurreal.le_of_lt
- \+ *theorem* pSurreal.le_refl
- \+ *theorem* pSurreal.le_trans
- \+ *theorem* pSurreal.le_trans_aux
- \+ *theorem* pSurreal.lt_asymm
- \+ *theorem* pSurreal.lt_congr
- \+ *theorem* pSurreal.lt_iff_le_not_le
- \+ *theorem* pSurreal.lt_irrefl
- \+ *theorem* pSurreal.lt_mk_of_le
- \+ *theorem* pSurreal.lt_of_le_mk
- \+ *theorem* pSurreal.lt_of_mk_le
- \+ *theorem* pSurreal.mk_le_mk
- \+ *theorem* pSurreal.mk_lt_mk
- \+ *theorem* pSurreal.mk_lt_of_le
- \+ *def* pSurreal.mul
- \+ *theorem* pSurreal.ne_of_lt
- \+ *def* pSurreal.neg
- \+ *theorem* pSurreal.not_le
- \+ *theorem* pSurreal.not_le_lt
- \+ *theorem* pSurreal.not_lt
- \+ *def* pSurreal.ok
- \+ *theorem* pSurreal.ok_rec
- \+ *def* pSurreal.omega
- \+ *inductive* pSurreal.{u}
- \+ *def* surreal.equiv
- \+ *def* surreal.le
- \+ *def* surreal.lift
- \+ *def* surreal.lift₂
- \+ *def* surreal.lt
- \+ *def* surreal.mk
- \+ *theorem* surreal.not_le
- \+ *def* surreal
- \+ *inductive* {u}



## [2019-05-17 16:13:20](https://github.com/leanprover-community/mathlib/commit/0b35022)
refactor: change variables order in some composition lemmas ([#1035](https://github.com/leanprover-community/mathlib/pull/1035))
#### Estimated changes
Modified src/analysis/complex/exponential.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \- *theorem* has_fderiv_within_at.comp_has_fderiv_at

Modified src/category_theory/concrete_category.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.measure.map_map

Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/basic.lean
- \+/\- *lemma* continuous.comp

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/compact_open.lean
- \+/\- *def* continuous_map.induced

Modified src/topology/constructions.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/maps.lean
- \+/\- *lemma* embedding_compose

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \+/\- *theorem* isometry.comp

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* uniform_space.completion.map_comp



## [2019-05-17 14:46:24](https://github.com/leanprover-community/mathlib/commit/f633c94)
feat(tactic/basic): add tactic.rewrite, and sort list ([#1039](https://github.com/leanprover-community/mathlib/pull/1039))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-05-17 13:20:21](https://github.com/leanprover-community/mathlib/commit/a6c1f37)
fix(data/complex/exponential): make complex.exp irreducible ([#1040](https://github.com/leanprover-community/mathlib/pull/1040))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.
#### Estimated changes
Modified src/data/complex/exponential.lean




## [2019-05-17 06:56:38](https://github.com/leanprover-community/mathlib/commit/96ea9b9)
chore(opposites): merge two definitions of `opposite` ([#1036](https://github.com/leanprover-community/mathlib/pull/1036))
* chore(opposites): merge two definitions of `opposite`
* merge `opposite.opposite` from `algebra/opposites` with
  `category_theory.opposite` from `category_theory/opposites`, and put
  it into `data/opposite`
* main reasons: DRY, avoid confusion if both namespaces are open
* see https://github.com/leanprover-community/mathlib/pull/538#issuecomment-459488227
* Authors merged from `git blame` output on both original files;
  I assume my contribution to be trivial
* Update opposite.lean
#### Estimated changes
Modified src/algebra/opposites.lean
- \- *def* opposite.op
- \- *theorem* opposite.op_inj
- \- *theorem* opposite.op_unop
- \- *def* opposite.unop
- \- *theorem* opposite.unop_inj
- \- *theorem* opposite.unop_op
- \- *def* opposite

Modified src/category_theory/adjunction.lean


Modified src/category_theory/const.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/instances/Top/open_nhds.lean


Modified src/category_theory/instances/Top/opens.lean


Modified src/category_theory/instances/Top/presheaf.lean


Modified src/category_theory/instances/Top/presheaf_of_functions.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/opposites.lean
- \- *def* category_theory.op
- \- *def* category_theory.op_induction
- \- *lemma* category_theory.op_inj
- \- *lemma* category_theory.op_unop
- \- *def* category_theory.opposite
- \- *def* category_theory.unop
- \- *lemma* category_theory.unop_inj
- \- *lemma* category_theory.unop_op

Modified src/category_theory/yoneda.lean


Added src/data/opposite.lean
- \+ *def* opposite.op
- \+ *def* opposite.op_induction
- \+ *lemma* opposite.op_inj
- \+ *lemma* opposite.op_unop
- \+ *def* opposite.opposite
- \+ *def* opposite.unop
- \+ *lemma* opposite.unop_inj
- \+ *lemma* opposite.unop_op



## [2019-05-17 00:16:39](https://github.com/leanprover-community/mathlib/commit/def48b0)
feat(data/nat/basic): make decreasing induction eliminate to Sort ([#1032](https://github.com/leanprover-community/mathlib/pull/1032))
* add interface for decreasing_induction to Sort
* make decreasing_induction a def
* add simp tags and explicit type
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *def* nat.decreasing_induction
- \- *lemma* nat.decreasing_induction
- \+ *lemma* nat.decreasing_induction_self
- \+ *lemma* nat.decreasing_induction_succ'
- \+ *lemma* nat.decreasing_induction_succ
- \+ *lemma* nat.decreasing_induction_succ_left
- \+ *lemma* nat.decreasing_induction_trans
- \+ *theorem* nat.le_rec_on_succ_left



## [2019-05-16 12:58:27](https://github.com/leanprover-community/mathlib/commit/ad0f42d)
fix(data/nat/enat): Fix typo in lemma name ([#1037](https://github.com/leanprover-community/mathlib/pull/1037))
#### Estimated changes
Modified src/data/nat/enat.lean
- \- *lemma* enat.coe_ne_bot
- \+ *lemma* enat.coe_ne_top



## [2019-05-16 07:24:12](https://github.com/leanprover-community/mathlib/commit/c75c096)
chore(*): reduce imports ([#1033](https://github.com/leanprover-community/mathlib/pull/1033))
* chore(*): reduce imports
* restoring import in later file
* fix import
#### Estimated changes
Modified src/data/holor.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.hyperfilter_le_cofinite
- \+/\- *lemma* filter.is_ultrafilter_hyperfilter
- \+/\- *lemma* filter.tendsto_at_top_at_bot

Modified src/order/filter/filter_product.lean


Modified src/order/filter/partial.lean


Modified src/topology/algebra/monoid.lean




## [2019-05-15 17:08:22](https://github.com/leanprover-community/mathlib/commit/b5aae18)
feat(category_theory): monos and epis in Type and Top ([#1030](https://github.com/leanprover-community/mathlib/pull/1030))
* feat(category_theory): monos and epis in Type and Top
* imports
* add file header
* use notation for adjunction
#### Estimated changes
Added src/category_theory/epi_mono.lean
- \+ *lemma* category_theory.faithful_reflects_epi
- \+ *lemma* category_theory.faithful_reflects_mono
- \+ *lemma* category_theory.left_adjoint_preserves_epi
- \+ *lemma* category_theory.right_adjoint_preserves_mono

Modified src/category_theory/instances/Top/default.lean


Added src/category_theory/instances/Top/epi_mono.lean
- \+ *lemma* category_theory.instances.Top.epi_iff_surjective
- \+ *lemma* category_theory.instances.Top.mono_iff_injective

Modified src/category_theory/types.lean
- \+ *lemma* category_theory.epi_iff_surjective
- \+ *def* category_theory.hom_of_element
- \+ *lemma* category_theory.hom_of_element_eq_iff
- \+ *lemma* category_theory.mono_iff_injective



## [2019-05-15 13:26:27](https://github.com/leanprover-community/mathlib/commit/136e67a)
refactor(topology): change continuous_at_within to continuous_within_at ([#1034](https://github.com/leanprover-community/mathlib/pull/1034))
#### Estimated changes
Modified src/analysis/normed_space/deriv.lean
- \- *lemma* differentiable_within_at.continuous_at_within
- \+ *lemma* differentiable_within_at.continuous_within_at
- \- *theorem* has_fderiv_within_at.continuous_at_within
- \+ *theorem* has_fderiv_within_at.continuous_within_at

Modified src/topology/basic.lean
- \- *def* continuous_at_within
- \+/\- *def* continuous_on
- \+ *def* continuous_within_at

Modified src/topology/constructions.lean
- \- *lemma* continuous_at_within.prod
- \+ *lemma* continuous_within_at.prod

Modified src/topology/order.lean
- \- *lemma* continuous_at.continuous_at_within
- \+ *lemma* continuous_at.continuous_within_at
- \- *lemma* continuous_at_within.mono
- \- *theorem* continuous_at_within.tendsto_nhds_within_image
- \- *theorem* continuous_at_within_iff_continuous_at_restrict
- \- *theorem* continuous_at_within_iff_ptendsto_res
- \- *theorem* continuous_at_within_univ
- \+ *lemma* continuous_within_at.mono
- \+ *theorem* continuous_within_at.tendsto_nhds_within_image
- \+ *theorem* continuous_within_at_iff_continuous_at_restrict
- \+ *theorem* continuous_within_at_iff_ptendsto_res
- \+ *theorem* continuous_within_at_univ
- \+/\- *theorem* nhds_within_le_comap



## [2019-05-15 09:44:25](https://github.com/leanprover-community/mathlib/commit/3022caf)
feat(tactic/terminal_goal): determine if other goals depend on the current one ([#984](https://github.com/leanprover-community/mathlib/pull/984))
* feat(tactics): add "terminal_goal" tactic and relatives
* fix(test/tactics): renaming test functions to avoid a name collision
* fix(tactic): moving terminal_goal to tactic/basic.lean
* fix(test/tactics): open tactics
* touching a file, to prompt travis to try again
* terminal_goal
* fix
* merge
#### Estimated changes
Modified src/tactic/core.lean


Added test/terminal_goal.lean
- \+ *structure* C
- \+ *def* f
- \+ *structure* terminal_goal_struct'
- \+ *structure* terminal_goal_struct
- \+ *def* test_subsingleton_goal_1
- \+ *def* test_subsingleton_goal_2
- \+ *def* test_terminal_goal_1
- \+ *lemma* test_terminal_goal_2
- \+ *def* test_terminal_goal_3
- \+ *def* test_terminal_goal_4



## [2019-05-14 20:21:21](https://github.com/leanprover-community/mathlib/commit/7b579b7)
feat(category_theory): adjoint equivalences and limits under equivalences ([#986](https://github.com/leanprover-community/mathlib/pull/986))
* feat(category_theory): adjoint equivalences and limits
* Define equivalences to be adjoint equivalences.
  * Show that one triangle law implies the other for equivalences
  * Prove that having a limit of shape `J` is preserved under an equivalence `J ≌ J'`.
  * Construct an adjoint equivalence from a (non-adjoint) equivalence
* Put `nat_iso.app` in the `iso` namespace, so that we can write `α.app` for `α : F ≅ G`.
* Add some basic lemmas about equivalences, isomorphisms.
* Move some lemmas from `nat_trans` to `functor_category` and state them using `F ⟶ G` instead of `nat_trans F G` (maybe these files should just be merged?)
* Some small tweaks, improvements
* opposite of discrete is discrete
This also shows that C^op has coproducts if C has products and vice versa
Also fix rebase errors
* fix error (I don't know what caused this to break)
* Use tidy a bit more
* construct an adjunction from an equivalence
add notation `⊣` for an adjunction.
make some arguments of adjunction constructors implicit
* use adjunction notation
* formatting
* do adjointify_η as a natural iso directly, to avoid checking naturality
* tersifying
* fix errors, a bit of cleanup
* fix elements.lean
* fix error, address comments
#### Estimated changes
Modified src/category_theory/adjunction.lean
- \+/\- *def* category_theory.adjunction.adjunction_of_equiv_left
- \+/\- *def* category_theory.adjunction.adjunction_of_equiv_right
- \+/\- *def* category_theory.adjunction.comp
- \+ *def* category_theory.adjunction.equivalence.to_adjunction
- \+/\- *def* category_theory.adjunction.id
- \+/\- *def* category_theory.adjunction.mk_of_hom_equiv
- \+/\- *def* category_theory.adjunction.mk_of_unit_counit

Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.category.assoc_symm

Modified src/category_theory/const.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean
- \+ *lemma* category_theory.discrete.id_def
- \+ *def* category_theory.nat_iso.of_isos
- \+ *def* category_theory.nat_trans.of_homs

Modified src/category_theory/elements.lean


Modified src/category_theory/equivalence.lean
- \+ *def* category_theory.equivalence.adjointify_η
- \+ *lemma* category_theory.equivalence.adjointify_η_ε
- \+ *def* category_theory.equivalence.counit
- \+ *lemma* category_theory.equivalence.counit_def
- \+ *lemma* category_theory.equivalence.counit_functor
- \+ *def* category_theory.equivalence.counit_inv
- \+ *lemma* category_theory.equivalence.counit_inv_def
- \+ *lemma* category_theory.equivalence.counit_inv_functor_comp
- \+ *def* category_theory.equivalence.fun_inv_id_assoc
- \+ *lemma* category_theory.equivalence.fun_inv_id_assoc_hom_app
- \+ *lemma* category_theory.equivalence.fun_inv_id_assoc_inv_app
- \+ *lemma* category_theory.equivalence.functor_unit
- \+ *lemma* category_theory.equivalence.functor_unit_comp
- \+ *def* category_theory.equivalence.inv_fun_id_assoc
- \+ *lemma* category_theory.equivalence.inv_fun_id_assoc_hom_app
- \+ *lemma* category_theory.equivalence.inv_fun_id_assoc_inv_app
- \+ *lemma* category_theory.equivalence.inverse_counit
- \+ *lemma* category_theory.equivalence.inverse_counit_inv_comp
- \+/\- *def* category_theory.equivalence.refl
- \+ *def* category_theory.equivalence.unit
- \+ *lemma* category_theory.equivalence.unit_def
- \+ *def* category_theory.equivalence.unit_inv
- \+ *lemma* category_theory.equivalence.unit_inv_def
- \+ *lemma* category_theory.equivalence.unit_inverse
- \+ *lemma* category_theory.equivalence.unit_inverse_comp
- \+/\- *def* category_theory.functor.fun_inv_id
- \+/\- *def* category_theory.functor.inv_fun_id

Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean
- \- *lemma* category_theory.functor.category.comp_app
- \- *lemma* category_theory.functor.category.id_app
- \- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \- *lemma* category_theory.functor.category.nat_trans.naturality_app
- \+ *lemma* category_theory.nat_trans.app_naturality
- \+ *lemma* category_theory.nat_trans.comp_app
- \+ *lemma* category_theory.nat_trans.congr_app
- \+ *lemma* category_theory.nat_trans.exchange
- \+ *def* category_theory.nat_trans.hcomp
- \+ *lemma* category_theory.nat_trans.hcomp_app
- \+ *lemma* category_theory.nat_trans.id_app
- \+ *lemma* category_theory.nat_trans.naturality_app
- \+ *lemma* category_theory.nat_trans.vcomp_eq_comp

Modified src/category_theory/instances/CommRing/adjunctions.lean


Modified src/category_theory/instances/Top/adjunctions.lean
- \+/\- *def* category_theory.instances.Top.adj₁
- \+/\- *def* category_theory.instances.Top.adj₂

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.is_iso.inv_eq_inv
- \+ *lemma* category_theory.iso.comp_hom_eq_id
- \+ *lemma* category_theory.iso.hom_comp_eq_id
- \+ *lemma* category_theory.iso.hom_eq_inv
- \+ *lemma* category_theory.iso.inv_eq_inv

Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.limits.cocones.ext_hom_hom
- \+ *def* category_theory.limits.cocones.precompose_comp
- \+ *def* category_theory.limits.cocones.precompose_equivalence
- \+ *def* category_theory.limits.cocones.precompose_id
- \+ *lemma* category_theory.limits.cones.ext_hom_hom
- \+ *def* category_theory.limits.cones.postcompose_comp
- \+ *def* category_theory.limits.cones.postcompose_equivalence
- \+ *def* category_theory.limits.cones.postcompose_id

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.pre_map'
- \+/\- *lemma* category_theory.limits.colimit.pre_map
- \+/\- *lemma* category_theory.limits.colimit.pre_post
- \+ *def* category_theory.limits.has_colimit_of_equivalence_comp
- \+ *def* category_theory.limits.has_colimit_of_iso
- \+ *def* category_theory.limits.has_colimits_of_shape_of_equivalence
- \+ *def* category_theory.limits.has_limit_of_equivalence_comp
- \+ *def* category_theory.limits.has_limit_of_iso
- \+ *def* category_theory.limits.has_limits_of_shape_of_equivalence
- \+/\- *lemma* category_theory.limits.limit.map_pre'
- \+/\- *lemma* category_theory.limits.limit.map_pre
- \+/\- *lemma* category_theory.limits.limit.pre_post

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/natural_isomorphism.lean
- \+ *def* category_theory.iso.app
- \- *def* category_theory.nat_iso.app
- \+/\- *lemma* category_theory.nat_iso.app_hom
- \+/\- *lemma* category_theory.nat_iso.app_inv
- \- *lemma* category_theory.nat_iso.comp_app
- \+ *def* category_theory.nat_iso.hcomp
- \+ *def* category_theory.nat_iso.is_iso_of_is_iso_app
- \+ *lemma* category_theory.nat_iso.trans_app

Modified src/category_theory/natural_transformation.lean
- \- *lemma* category_theory.nat_trans.congr_app
- \- *lemma* category_theory.nat_trans.exchange
- \+/\- *lemma* category_theory.nat_trans.ext
- \- *def* category_theory.nat_trans.hcomp
- \- *lemma* category_theory.nat_trans.hcomp_app
- \+ *lemma* category_theory.nat_trans.id_app'
- \- *lemma* category_theory.nat_trans.id_app
- \- *lemma* category_theory.nat_trans.vcomp_assoc

Modified src/category_theory/products/associator.lean
- \+/\- *def* category_theory.prod.associativity

Modified src/category_theory/products/default.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean




## [2019-05-14 18:15:35](https://github.com/leanprover-community/mathlib/commit/ae8f197)
feat(data/nat/basic): decreasing induction ([#1031](https://github.com/leanprover-community/mathlib/pull/1031))
* feat(data/nat/basic): decreasing induction
* feat(data/nat/basic): better proof of decreasing induction
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.decreasing_induction
- \+/\- *lemma* nat.lt_iff_add_one_le
- \+/\- *lemma* nat.zero_max



## [2019-05-14 14:46:29](https://github.com/leanprover-community/mathlib/commit/e7b64c5)
feat(data/equiv/functor): map_equiv ([#1026](https://github.com/leanprover-community/mathlib/pull/1026))
* feat(data/equiv/functor): map_equiv
* golf proofs
#### Estimated changes
Added src/data/equiv/functor.lean
- \+ *def* functor.map_equiv



## [2019-05-14 15:06:32+02:00](https://github.com/leanprover-community/mathlib/commit/02857d5)
fix(docs/tactics): fix layout, remove noise
#### Estimated changes
Modified docs/tactics.md




## [2019-05-14 12:43:19](https://github.com/leanprover-community/mathlib/commit/22790e0)
feat(tactic): new tactics to normalize casts inside expressions ([#988](https://github.com/leanprover-community/mathlib/pull/988))
* new tactics for normalizing casts
* update using the norm_cast tactics
* minor proof update
* minor changes
* moved a norm_cast lemma
* minor changes
* fix(doc/tactics): make headers uniform
* nicer proof using discharger
* fixed numerals handling by adding simp_cast lemmas
* add documentation
* fixed unnecessary normalizations in assumption_mod_cast
* minor proof update
* minor coding style update
* documentation update
* rename flip_equation to expr.flip_eq
* update proofs to remove boiler plate code about casts
* revert to old proof
* fixed imports and moved attributes
* add test file
* new attribute system
- the attribute norm_cast is split into norm_cast and norm_cast_rev
- update of the equation flipping mechanism
- update of the numerals handling
* syntax fix
* change attributes names
* test update
* small update
* add elim_cast attribute
* add examples for attributes
* new examples
#### Estimated changes
Modified docs/tactics.md


Modified src/algebra/char_zero.lean
- \+/\- *theorem* nat.cast_inj

Modified src/algebra/group_power.lean
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* int.coe_nat_pow
- \+/\- *theorem* nat.cast_pow

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_cast_nat
- \+/\- *lemma* complex.int_cast_im
- \+/\- *lemma* complex.int_cast_re
- \+/\- *lemma* complex.nat_cast_im
- \+/\- *lemma* complex.nat_cast_re
- \+/\- *lemma* complex.of_real_add
- \+/\- *lemma* complex.of_real_bit0
- \+/\- *lemma* complex.of_real_bit1
- \+/\- *lemma* complex.of_real_div
- \+/\- *lemma* complex.of_real_fpow
- \+/\- *lemma* complex.of_real_im
- \+/\- *theorem* complex.of_real_inj
- \+/\- *theorem* complex.of_real_int_cast
- \+/\- *lemma* complex.of_real_inv
- \+/\- *lemma* complex.of_real_mul
- \+/\- *theorem* complex.of_real_nat_cast
- \+/\- *lemma* complex.of_real_neg
- \+/\- *lemma* complex.of_real_one
- \+/\- *lemma* complex.of_real_pow
- \+/\- *theorem* complex.of_real_rat_cast
- \+/\- *lemma* complex.of_real_re
- \+/\- *lemma* complex.of_real_sub
- \+/\- *lemma* complex.of_real_zero
- \+/\- *lemma* complex.rat_cast_im
- \+/\- *lemma* complex.rat_cast_re

Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_abs
- \+/\- *theorem* int.cast_add
- \+/\- *theorem* int.cast_bit0
- \+/\- *theorem* int.cast_bit1
- \+/\- *theorem* int.cast_coe_nat
- \+/\- *theorem* int.cast_id
- \+/\- *theorem* int.cast_inj
- \+/\- *theorem* int.cast_le
- \+/\- *theorem* int.cast_lt
- \+/\- *theorem* int.cast_max
- \+/\- *theorem* int.cast_min
- \+/\- *theorem* int.cast_mul
- \+/\- *theorem* int.cast_neg
- \+/\- *theorem* int.cast_neg_of_nat
- \+/\- *theorem* int.cast_neg_succ_of_nat
- \+/\- *theorem* int.cast_one
- \+/\- *theorem* int.cast_sub
- \+/\- *theorem* int.cast_sub_nat_nat
- \+/\- *theorem* int.cast_zero
- \+/\- *theorem* int.coe_nat_abs
- \+ *theorem* int.coe_nat_bit0
- \+ *theorem* int.coe_nat_bit1
- \+/\- *theorem* int.coe_nat_div
- \+/\- *theorem* int.coe_nat_dvd
- \+/\- *theorem* int.coe_nat_inj'
- \+/\- *theorem* int.coe_nat_le
- \+/\- *theorem* int.coe_nat_lt

Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.abs_cast
- \+/\- *theorem* nat.cast_add
- \+/\- *theorem* nat.cast_bit0
- \+/\- *theorem* nat.cast_bit1
- \+/\- *theorem* nat.cast_id
- \+/\- *theorem* nat.cast_le
- \+/\- *theorem* nat.cast_lt
- \+/\- *theorem* nat.cast_max
- \+/\- *theorem* nat.cast_min
- \+/\- *theorem* nat.cast_mul
- \+/\- *theorem* nat.cast_one
- \+/\- *theorem* nat.cast_pred
- \+/\- *theorem* nat.cast_sub
- \+/\- *theorem* nat.cast_succ
- \+/\- *theorem* nat.cast_zero

Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_add
- \+/\- *lemma* enat.coe_get
- \+/\- *lemma* enat.coe_le_coe
- \+/\- *lemma* enat.coe_lt_coe
- \+/\- *lemma* enat.coe_one
- \+/\- *lemma* enat.coe_zero

Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* padic_int.cast_pow
- \+/\- *lemma* padic_int.coe_add
- \+/\- *lemma* padic_int.coe_coe
- \+/\- *lemma* padic_int.coe_mul
- \+/\- *lemma* padic_int.coe_neg
- \+/\- *lemma* padic_int.coe_one
- \+/\- *lemma* padic_int.coe_sub
- \+/\- *lemma* padic_int.coe_zero

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+ *lemma* padic.coe_add
- \+ *lemma* padic.coe_div
- \+ *lemma* padic.coe_inj
- \+ *lemma* padic.coe_mul
- \+ *lemma* padic.coe_neg
- \+ *lemma* padic.coe_one
- \+ *lemma* padic.coe_sub
- \+ *lemma* padic.coe_zero
- \+/\- *lemma* padic_norm_e.eq_padic_norm

Modified src/data/rat.lean
- \+/\- *theorem* rat.cast_abs
- \+/\- *theorem* rat.cast_add
- \+/\- *theorem* rat.cast_add_of_ne_zero
- \+/\- *theorem* rat.cast_bit0
- \+/\- *theorem* rat.cast_bit1
- \+/\- *theorem* rat.cast_coe_int
- \+/\- *theorem* rat.cast_coe_nat
- \+/\- *theorem* rat.cast_div
- \+/\- *theorem* rat.cast_div_of_ne_zero
- \+/\- *theorem* rat.cast_id
- \+/\- *theorem* rat.cast_inj
- \+/\- *theorem* rat.cast_inv
- \+/\- *theorem* rat.cast_inv_of_ne_zero
- \+/\- *theorem* rat.cast_le
- \+/\- *theorem* rat.cast_lt
- \+/\- *theorem* rat.cast_max
- \+/\- *theorem* rat.cast_min
- \+/\- *theorem* rat.cast_mk
- \+/\- *theorem* rat.cast_mk_of_ne_zero
- \+/\- *theorem* rat.cast_mul
- \+/\- *theorem* rat.cast_mul_of_ne_zero
- \+/\- *theorem* rat.cast_neg
- \+/\- *theorem* rat.cast_one
- \+/\- *theorem* rat.cast_pow
- \+/\- *theorem* rat.cast_sub
- \+/\- *theorem* rat.cast_sub_of_ne_zero
- \+/\- *theorem* rat.cast_zero
- \+/\- *theorem* rat.coe_int_denom
- \+/\- *theorem* rat.coe_int_num
- \+/\- *theorem* rat.coe_nat_denom
- \+/\- *theorem* rat.coe_nat_num

Modified src/ring_theory/multiplicity.lean
- \+ *theorem* multiplicity.int.coe_nat_multiplicity
- \+ *theorem* nat.find_le

Added src/tactic/norm_cast.lean
- \+ *lemma* ge_from_le
- \+ *lemma* gt_from_lt
- \+ *lemma* ite_cast
- \+ *lemma* ne_from_not_eq

Added test/norm_cast.lean




## [2019-05-14 11:13:33](https://github.com/leanprover-community/mathlib/commit/fe19bdb)
fix(data/multiset): remove duplicate setoid instance ([#1027](https://github.com/leanprover-community/mathlib/pull/1027))
* fix(data/multiset): remove duplicate setoid instance
* s/ : Type uu//
#### Estimated changes
Modified src/data/list/perm.lean
- \+/\- *theorem* list.perm.eqv

Modified src/data/multiset.lean
- \+ *def* multiset.subsingleton_equiv



## [2019-05-14 10:24:51](https://github.com/leanprover-community/mathlib/commit/ade99c8)
feat(analysis/normed_space/deriv): more material on derivatives ([#966](https://github.com/leanprover-community/mathlib/pull/966))
* feat(analysis/normed_space/deriv): more material on derivatives
* feat(analysis/normed_space/deriv): minor improvements
* feat(analysis/normed_space/deriv) rename fderiv_at_within to fderiv_within_at
* feat(analysis/normed_space/deriv): more systematic renaming
* feat(analysis/normed_space/deriv): fix style
* modify travis.yml as advised by Simon Hudon
* fix travis.yml, second try
* feat(analysis/normed_space/deriv): add two missing lemmas
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O.prod_rightl
- \+ *lemma* asymptotics.is_O.prod_rightr
- \+ *theorem* asymptotics.is_O_one_of_tendsto
- \+ *theorem* asymptotics.is_O_prod_left
- \+ *lemma* asymptotics.is_o.prod_rightl
- \+ *lemma* asymptotics.is_o.prod_rightr
- \+ *theorem* asymptotics.is_o_prod_left

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* bounded_linear_map.is_bounded_linear_map_comp_left
- \+ *lemma* bounded_linear_map.is_bounded_linear_map_comp_right
- \+ *def* is_bounded_bilinear_map.deriv
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_deriv
- \+ *lemma* is_bounded_bilinear_map.map_sub_left
- \+ *lemma* is_bounded_bilinear_map.map_sub_right
- \+ *structure* is_bounded_bilinear_map
- \+ *lemma* is_bounded_bilinear_map_comp
- \+ *lemma* is_bounded_bilinear_map_mul
- \+ *lemma* is_bounded_bilinear_map_smul
- \+ *lemma* is_bounded_linear_map_prod_iso

Modified src/analysis/normed_space/deriv.lean
- \+ *lemma* differentiable.add
- \+ *lemma* differentiable.congr'
- \+ *lemma* differentiable.congr
- \+ *lemma* differentiable.continuous
- \+ *lemma* differentiable.differentiable_on
- \+ *lemma* differentiable.fderiv_within
- \+ *lemma* differentiable.mul
- \+ *lemma* differentiable.neg
- \+ *lemma* differentiable.prod
- \+ *lemma* differentiable.smul'
- \+ *lemma* differentiable.smul
- \+ *lemma* differentiable.sub
- \+ *def* differentiable
- \+ *lemma* differentiable_at.add
- \+ *lemma* differentiable_at.comp
- \+ *lemma* differentiable_at.congr
- \+ *lemma* differentiable_at.continuous_at
- \+ *lemma* differentiable_at.differentiable_within_at
- \+ *lemma* differentiable_at.fderiv_congr'
- \+ *lemma* differentiable_at.fderiv_congr
- \+ *lemma* differentiable_at.fderiv_prod
- \+ *lemma* differentiable_at.fderiv_within_prod
- \+ *lemma* differentiable_at.has_fderiv_at
- \+ *lemma* differentiable_at.mul
- \+ *lemma* differentiable_at.neg
- \+ *lemma* differentiable_at.prod
- \+ *lemma* differentiable_at.smul'
- \+ *lemma* differentiable_at.smul
- \+ *lemma* differentiable_at.sub
- \+ *def* differentiable_at
- \+ *lemma* differentiable_at_const
- \+ *lemma* differentiable_at_id
- \+ *lemma* differentiable_const
- \+ *lemma* differentiable_id
- \+ *lemma* differentiable_on.add
- \+ *lemma* differentiable_on.comp
- \+ *lemma* differentiable_on.congr_mono
- \+ *lemma* differentiable_on.continuous_on
- \+ *lemma* differentiable_on.mono
- \+ *lemma* differentiable_on.mul
- \+ *lemma* differentiable_on.neg
- \+ *lemma* differentiable_on.prod
- \+ *lemma* differentiable_on.smul'
- \+ *lemma* differentiable_on.smul
- \+ *lemma* differentiable_on.sub
- \+ *def* differentiable_on
- \+ *lemma* differentiable_on_const
- \+ *lemma* differentiable_on_id
- \+ *lemma* differentiable_on_of_locally_differentiable_on
- \+ *lemma* differentiable_on_univ
- \+ *lemma* differentiable_within_at.add
- \+ *lemma* differentiable_within_at.comp
- \+ *lemma* differentiable_within_at.congr_mono
- \+ *lemma* differentiable_within_at.continuous_at_within
- \+ *lemma* differentiable_within_at.differentiable_at'
- \+ *lemma* differentiable_within_at.differentiable_at
- \+ *lemma* differentiable_within_at.fderiv_within_congr_mono
- \+ *lemma* differentiable_within_at.has_fderiv_within_at
- \+ *lemma* differentiable_within_at.mono
- \+ *lemma* differentiable_within_at.mul
- \+ *lemma* differentiable_within_at.neg
- \+ *lemma* differentiable_within_at.prod
- \+ *lemma* differentiable_within_at.smul'
- \+ *lemma* differentiable_within_at.smul
- \+ *lemma* differentiable_within_at.sub
- \+ *def* differentiable_within_at
- \+ *lemma* differentiable_within_at_const
- \+ *lemma* differentiable_within_at_id
- \+ *lemma* differentiable_within_at_inter
- \+ *lemma* differentiable_within_univ_at
- \+ *lemma* fderiv.comp
- \+ *def* fderiv
- \+ *lemma* fderiv_add
- \- *lemma* fderiv_at_filter_unique
- \- *theorem* fderiv_at_unique
- \- *theorem* fderiv_at_within_open_unique
- \+ *lemma* fderiv_const
- \+ *lemma* fderiv_id
- \+ *lemma* fderiv_mul
- \+ *lemma* fderiv_neg
- \+ *lemma* fderiv_smul'
- \+ *lemma* fderiv_smul
- \+ *lemma* fderiv_sub
- \+ *lemma* fderiv_within.comp
- \+ *def* fderiv_within
- \+ *lemma* fderiv_within_add
- \+ *lemma* fderiv_within_const
- \+ *lemma* fderiv_within_id
- \+ *lemma* fderiv_within_mul
- \+ *lemma* fderiv_within_neg
- \+ *lemma* fderiv_within_smul'
- \+ *lemma* fderiv_within_smul
- \+ *lemma* fderiv_within_sub
- \+ *lemma* fderiv_within_univ
- \+ *theorem* has_fderiv_at.add
- \+ *lemma* has_fderiv_at.differentiable_at
- \+ *lemma* has_fderiv_at.fderiv
- \+ *theorem* has_fderiv_at.has_fderiv_at_filter
- \+ *theorem* has_fderiv_at.has_fderiv_within_at
- \+ *theorem* has_fderiv_at.mul
- \+ *theorem* has_fderiv_at.neg
- \+ *lemma* has_fderiv_at.prod
- \+ *theorem* has_fderiv_at.smul'
- \+ *theorem* has_fderiv_at.smul
- \+ *theorem* has_fderiv_at.sub
- \+/\- *def* has_fderiv_at
- \- *theorem* has_fderiv_at_add
- \+ *theorem* has_fderiv_at_filter.add
- \+ *lemma* has_fderiv_at_filter.congr'
- \+/\- *theorem* has_fderiv_at_filter.mono
- \+ *theorem* has_fderiv_at_filter.neg
- \+ *lemma* has_fderiv_at_filter.prod
- \+ *theorem* has_fderiv_at_filter.smul
- \+ *theorem* has_fderiv_at_filter.sub
- \+/\- *def* has_fderiv_at_filter
- \- *theorem* has_fderiv_at_filter_add
- \- *theorem* has_fderiv_at_filter_neg
- \- *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \- *theorem* has_fderiv_at_filter_smul
- \- *theorem* has_fderiv_at_filter_sub
- \+/\- *theorem* has_fderiv_at_iff_tendsto
- \- *theorem* has_fderiv_at_neg
- \- *theorem* has_fderiv_at_smul
- \- *theorem* has_fderiv_at_sub
- \+ *theorem* has_fderiv_at_unique
- \- *theorem* has_fderiv_at_within.comp
- \- *theorem* has_fderiv_at_within.congr
- \- *theorem* has_fderiv_at_within.continuous_at_within
- \- *theorem* has_fderiv_at_within.mono
- \- *def* has_fderiv_at_within
- \- *theorem* has_fderiv_at_within_add
- \- *theorem* has_fderiv_at_within_congr
- \- *theorem* has_fderiv_at_within_const
- \- *theorem* has_fderiv_at_within_id
- \- *theorem* has_fderiv_at_within_iff_tendsto
- \- *theorem* has_fderiv_at_within_neg
- \- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \- *theorem* has_fderiv_at_within_smul
- \- *theorem* has_fderiv_at_within_sub
- \+ *theorem* has_fderiv_within_at.add
- \+ *theorem* has_fderiv_within_at.comp
- \+ *theorem* has_fderiv_within_at.comp_has_fderiv_at
- \+ *theorem* has_fderiv_within_at.congr
- \+ *lemma* has_fderiv_within_at.congr_mono
- \+ *theorem* has_fderiv_within_at.continuous_at_within
- \+ *lemma* has_fderiv_within_at.differentiable_within_at
- \+ *lemma* has_fderiv_within_at.fderiv_within
- \+ *theorem* has_fderiv_within_at.mono
- \+ *theorem* has_fderiv_within_at.mul
- \+ *theorem* has_fderiv_within_at.neg
- \+ *lemma* has_fderiv_within_at.prod
- \+ *theorem* has_fderiv_within_at.smul'
- \+ *theorem* has_fderiv_within_at.smul
- \+ *theorem* has_fderiv_within_at.sub
- \+ *def* has_fderiv_within_at
- \+ *theorem* has_fderiv_within_at_congr
- \+ *theorem* has_fderiv_within_at_const
- \+ *theorem* has_fderiv_within_at_id
- \+ *theorem* has_fderiv_within_at_iff_tendsto
- \+ *lemma* has_fderiv_within_univ_at
- \+ *lemma* is_bounded_bilinear_map.continuous
- \+ *lemma* is_bounded_bilinear_map.differentiable
- \+ *lemma* is_bounded_bilinear_map.differentiable_at
- \+ *lemma* is_bounded_bilinear_map.differentiable_on
- \+ *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+ *lemma* is_bounded_bilinear_map.fderiv
- \+ *lemma* is_bounded_bilinear_map.fderiv_within
- \+ *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+ *lemma* is_bounded_bilinear_map.has_fderiv_within_at
- \+ *lemma* is_bounded_linear_map.differentiable
- \+ *lemma* is_bounded_linear_map.differentiable_at
- \+ *lemma* is_bounded_linear_map.differentiable_on
- \+ *lemma* is_bounded_linear_map.differentiable_within_at
- \+ *lemma* is_bounded_linear_map.fderiv
- \+ *lemma* is_bounded_linear_map.fderiv_within
- \+ *lemma* is_bounded_linear_map.has_fderiv_at
- \+ *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \+ *lemma* is_bounded_linear_map.has_fderiv_within_at
- \+ *lemma* is_open.unique_diff_on
- \+ *lemma* is_open.unique_diff_within_at
- \+ *lemma* tangent_cone_at.lim_zero
- \+ *def* tangent_cone_at
- \+ *lemma* tangent_cone_inter_open
- \+ *lemma* tangent_cone_mono
- \+ *lemma* tangent_cone_univ
- \+ *theorem* unique_diff_on.eq
- \+ *def* unique_diff_on
- \+ *lemma* unique_diff_on_inter
- \+ *theorem* unique_diff_within_at.eq
- \+ *def* unique_diff_within_at
- \+ *lemma* unique_diff_within_at_inter
- \+ *lemma* unique_diff_within_univ_at

Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* bounded_linear_map.prod
- \+ *def* bounded_linear_map.scalar_prod_space_iso

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.is_linear_map_prod_iso
- \+ *def* linear_map.prod
- \+ *def* linear_map.scalar_prod_space_iso

Modified src/topology/constructions.lean
- \+ *lemma* continuous_at.prod
- \+ *lemma* continuous_at_within.prod
- \+/\- *lemma* continuous_inclusion
- \+ *lemma* continuous_on.prod

Modified src/topology/order.lean
- \+ *lemma* continuous.continuous_on
- \+ *lemma* continuous_at.continuous_at_within
- \+ *lemma* continuous_at_within.mono
- \+ *def* continuous_iff_continuous_on_univ
- \+ *lemma* continuous_on.comp
- \+ *lemma* continuous_on.congr_mono
- \+ *lemma* continuous_on.mono
- \+ *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \+ *lemma* continuous_on.preimage_open_of_open
- \+ *lemma* continuous_on_const
- \+ *lemma* continuous_on_of_locally_continuous_on



## [2019-05-14 07:24:40](https://github.com/leanprover-community/mathlib/commit/a72641b)
squeeze_simp ([#1019](https://github.com/leanprover-community/mathlib/pull/1019))
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/algebra/pi_instances.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean


Modified src/data/fin.lean


Modified src/data/semiquot.lean


Modified src/data/set/intervals.lean




## [2019-05-14 05:35:17](https://github.com/leanprover-community/mathlib/commit/cefb9d4)
feat(category_theory/opposites): iso.op ([#1021](https://github.com/leanprover-community/mathlib/pull/1021))
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.iso.op_hom
- \+ *lemma* category_theory.iso.op_inv



## [2019-05-14 01:23:18](https://github.com/leanprover-community/mathlib/commit/6dc0682)
feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+/\- *lemma* strict_mono.monotone



## [2019-05-13 23:54:13](https://github.com/leanprover-community/mathlib/commit/07ba43e)
feat(topology/constructions): topology of sum types ([#1016](https://github.com/leanprover-community/mathlib/pull/1016))
#### Estimated changes
Modified src/data/sigma/basic.lean
- \+ *lemma* injective_sigma_map
- \+ *lemma* injective_sigma_mk

Modified src/topology/constructions.lean
- \+ *lemma* closed_embedding_sigma_mk
- \+ *lemma* continuous_sigma
- \+ *lemma* continuous_sigma_map
- \+ *lemma* continuous_sigma_mk
- \+ *lemma* embedding_sigma_map
- \+ *lemma* embedding_sigma_mk
- \+ *lemma* is_closed_map_sigma_mk
- \+ *lemma* is_closed_sigma_iff
- \+ *lemma* is_closed_sigma_mk
- \+ *lemma* is_open_map_sigma_mk
- \+ *lemma* is_open_range_sigma_mk
- \+ *lemma* is_open_sigma_iff

Modified src/topology/maps.lean
- \- *lemma* continuous_Prop
- \- *lemma* is_open_singleton_true

Modified src/topology/order.lean
- \+ *lemma* continuous_Prop
- \+ *lemma* is_closed_infi_iff
- \+ *lemma* is_open_infi_iff
- \+ *lemma* is_open_singleton_true



## [2019-05-13 22:28:23](https://github.com/leanprover-community/mathlib/commit/f8385b1)
feat(data/equiv/basic): equiv.nonempty_iff_nonempty ([#1020](https://github.com/leanprover-community/mathlib/pull/1020))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.nonempty_iff_nonempty



## [2019-05-13 20:36:11](https://github.com/leanprover-community/mathlib/commit/01b345c)
feat(tactics/interactive): choose uses exists_prop ([#1014](https://github.com/leanprover-community/mathlib/pull/1014))
* feat(tactics/interactive): choose uses exists_prop
* fix build
#### Estimated changes
Modified src/tactic/interactive.lean


Modified src/topology/bounded_continuous_function.lean


Modified test/examples.lean




## [2019-05-13 20:00:57](https://github.com/leanprover-community/mathlib/commit/c8a0bb6)
feat(category_theory/products): missing simp lemmas ([#1003](https://github.com/leanprover-community/mathlib/pull/1003))
* feat(category_theory/products): missing simp lemmas
* cleanup proofs
* fix proof
* squeeze_simp
#### Estimated changes
Modified src/category_theory/products/default.lean
- \+/\- *def* category_theory.evaluation
- \+ *lemma* category_theory.evaluation_map_app
- \+ *lemma* category_theory.evaluation_obj_map
- \+ *lemma* category_theory.evaluation_obj_obj
- \+/\- *def* category_theory.evaluation_uncurried
- \+ *lemma* category_theory.evaluation_uncurried_map
- \+ *lemma* category_theory.evaluation_uncurried_obj
- \+/\- *lemma* category_theory.functor.prod_map
- \+/\- *lemma* category_theory.functor.prod_obj
- \+ *lemma* category_theory.prod.fst_map
- \+ *lemma* category_theory.prod.fst_obj
- \+ *lemma* category_theory.prod.inl_map
- \+ *lemma* category_theory.prod.inl_obj
- \+ *lemma* category_theory.prod.inr_map
- \+ *lemma* category_theory.prod.inr_obj
- \+ *lemma* category_theory.prod.snd_map
- \+ *lemma* category_theory.prod.snd_obj
- \+ *lemma* category_theory.prod.swap_map
- \+ *lemma* category_theory.prod.swap_obj



## [2019-05-13 19:33:32](https://github.com/leanprover-community/mathlib/commit/6c35df0)
feat(category_theory/iso): missing lemmas ([#1001](https://github.com/leanprover-community/mathlib/pull/1001))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* oops
* one more
* sleep
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean


Modified src/category_theory/category.lean
- \+/\- *lemma* category_theory.cancel_epi
- \+/\- *lemma* category_theory.cancel_mono

Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.eq_of_inv_eq_inv
- \+ *lemma* category_theory.is_iso.inv_comp
- \+ *lemma* category_theory.is_iso.inv_id
- \+ *lemma* category_theory.is_iso.is_iso.inv_inv
- \+ *lemma* category_theory.is_iso.iso.inv_hom
- \+ *lemma* category_theory.is_iso.iso.inv_inv



## [2019-05-13 18:39:56+02:00](https://github.com/leanprover-community/mathlib/commit/82f151f)
document the change in scripts ([#1024](https://github.com/leanprover-community/mathlib/pull/1024))
#### Estimated changes
Modified docs/install/debian.md


Modified docs/install/debian_details.md


Modified docs/install/linux.md


Modified docs/install/macos.md


Modified docs/install/windows.md




## [2019-05-13 15:42:01](https://github.com/leanprover-community/mathlib/commit/70cd00b)
feat(Top.presheaf_ℂ): presheaves of functions to topological commutative rings ([#976](https://github.com/leanprover-community/mathlib/pull/976))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* missed one
* typo
* WIP
* oops
* the presheaf of continuous functions to ℂ
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* renaming
* update notation
* fix
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* moving instances
* remove crap
* tidy
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* cleanup
* cleaning up
* cleaning up
* move
* Update src/category_theory/instances/Top/presheaf_of_functions.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
* fixes in response to review
#### Estimated changes
Modified src/category_theory/instances/CommRing/basic.lean
- \+ *def* category_theory.instances.CommRing.of

Modified src/category_theory/instances/Top/default.lean


Modified src/category_theory/instances/Top/opens.lean
- \+ *def* topological_space.opens.to_Top

Added src/category_theory/instances/Top/presheaf_of_functions.lean
- \+ *def* category_theory.instances.Top.CommRing_yoneda
- \+ *lemma* category_theory.instances.Top.continuous_functions.add
- \+ *def* category_theory.instances.Top.continuous_functions.map
- \+ *lemma* category_theory.instances.Top.continuous_functions.mul
- \+ *lemma* category_theory.instances.Top.continuous_functions.one
- \+ *def* category_theory.instances.Top.continuous_functions.pullback
- \+ *def* category_theory.instances.Top.continuous_functions
- \+ *def* category_theory.instances.Top.presheaf_to_Top
- \+ *def* category_theory.instances.Top.presheaf_to_TopCommRing

Added src/category_theory/instances/TopCommRing/basic.lean
- \+ *def* category_theory.instances.TopCommRing.forget
- \+ *def* category_theory.instances.TopCommRing.forget_to_CommRing
- \+ *def* category_theory.instances.TopCommRing.forget_to_Top
- \+ *def* category_theory.instances.TopCommRing.forget_to_Type_via_CommRing
- \+ *def* category_theory.instances.TopCommRing.forget_to_Type_via_Top
- \+ *def* category_theory.instances.TopCommRing.of
- \+ *structure* category_theory.instances.TopCommRing

Added src/category_theory/instances/TopCommRing/default.lean




## [2019-05-13 11:21:50-04:00](https://github.com/leanprover-community/mathlib/commit/b9b5bb4)
chore(Github): no need to wait for Appveyor anymopre
#### Estimated changes
Modified .mergify.yml




## [2019-05-13 11:12:35-04:00](https://github.com/leanprover-community/mathlib/commit/e42d808)
chore(scripts): migrate scripts to own repo ([#1011](https://github.com/leanprover-community/mathlib/pull/1011))
#### Estimated changes
Modified .travis.yml


Deleted appveyor.yml


Deleted scripts/auth_github.py


Deleted scripts/cache-olean.py


Deleted scripts/delayed_interrupt.py


Modified scripts/deploy_nightly.sh


Deleted scripts/install_debian.sh


Deleted scripts/leanpkg-example.toml


Deleted scripts/post-checkout


Deleted scripts/post-commit


Deleted scripts/remote-install-update-mathlib.sh


Deleted scripts/setup-dev-scripts.sh


Deleted scripts/setup-lean-git-hooks.sh


Deleted scripts/update-mathlib.py




## [2019-05-13 18:20:20+10:00](https://github.com/leanprover-community/mathlib/commit/4864515)
feat(category_theory): lemmas about cancellation ([#1005](https://github.com/leanprover-community/mathlib/pull/1005))
* feat(category_theory): lemmas about cancellation
* rename hypotheses
* Squeeze proofs
#### Estimated changes
Modified src/category_theory/category.lean
- \+ *lemma* category_theory.eq_of_comp_left_eq'
- \+ *lemma* category_theory.eq_of_comp_left_eq
- \+ *lemma* category_theory.eq_of_comp_right_eq'
- \+ *lemma* category_theory.eq_of_comp_right_eq
- \+ *lemma* category_theory.id_of_comp_left_id
- \+ *lemma* category_theory.id_of_comp_right_id



## [2019-05-12 14:51:35](https://github.com/leanprover-community/mathlib/commit/1e0761e)
feat(topology/maps): closed embeddings ([#1013](https://github.com/leanprover-community/mathlib/pull/1013))
* feat(topology/maps): closed embeddings
* fix "is_open_map"
#### Estimated changes
Modified src/topology/maps.lean
- \+ *lemma* closed_embedding.closed_iff_image_closed
- \+ *lemma* closed_embedding.closed_iff_preimage_closed
- \+ *def* closed_embedding
- \+ *lemma* closed_embedding_compose
- \+ *lemma* closed_embedding_id
- \+ *lemma* closed_embedding_of_continuous_injective_closed
- \+ *lemma* is_closed_map.of_inverse
- \+ *def* is_closed_map



## [2019-05-12 01:21:18](https://github.com/leanprover-community/mathlib/commit/de5d038)
feat(logic/function): comp₂ -- useful for binary operations ([#993](https://github.com/leanprover-community/mathlib/pull/993))
* feat(logic/function): comp₂ -- useful for binary operations
For example, when working with topological groups
it does not suffice to look at `mul : G → G → G`;
we need to require that `G × G → G` is continuous.
This lemma helps with rewriting back and forth
between the curried and the uncurried versions.
* Fix: we are already in the function namespace, duh
* Replace comp₂ with a generalisation of bicompr
* fix error in bitraversable
* partially open function namespace in bitraversable
#### Estimated changes
Modified src/category/bifunctor.lean
- \- *def* bifunctor.bicompl
- \- *def* bifunctor.bicompr

Modified src/category/bitraversable/instances.lean
- \+/\- *def* bicompl.bitraverse
- \+/\- *def* bicompr.bitraverse

Modified src/logic/function.lean
- \+ *def* function.bicompl
- \+ *def* function.bicompr
- \+ *lemma* function.uncurry_bicompr



## [2019-05-11 18:16:49-04:00](https://github.com/leanprover-community/mathlib/commit/a154ded)
fix(docs/*): docs reorganization [skip ci] ([#1012](https://github.com/leanprover-community/mathlib/pull/1012))
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md


Modified README.md


Renamed docs/code-review.md to docs/contribute/code-review.md


Renamed docs/howto-contribute.md to docs/contribute/index.md


Renamed docs/naming.md to docs/contribute/naming.md


Renamed docs/style.md to docs/contribute/style.md


Deleted docs/elan.md


Added docs/install/debian.md


Renamed docs/install_debian_details.md to docs/install/debian_details.md


Added docs/install/linux.md


Added docs/install/macos.md


Renamed docs/install_debian.md to docs/install/project.md


Added docs/install/windows.md




## [2019-05-11 14:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/8e71cee)
chore(build): remove script testing on PRs [skip ci]
#### Estimated changes
Modified .travis.yml




## [2019-05-11 13:26:30-04:00](https://github.com/leanprover-community/mathlib/commit/e6d959d)
docs(algebra/ring): document compatibility hack [skip ci]
#### Estimated changes
Modified src/algebra/ring.lean




## [2019-05-11 12:46:31-04:00](https://github.com/leanprover-community/mathlib/commit/c7d870e)
chore(compatibility): compatibility with Lean 3.5.0c ([#1007](https://github.com/leanprover-community/mathlib/pull/1007))
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *def* has_div_of_division_ring

Modified src/order/filter/filter_product.lean
- \+/\- *def* filter.bigly_equal
- \+/\- *lemma* filter.filter_product.lt_def'
- \+/\- *lemma* filter.filter_product.lt_def
- \+/\- *lemma* filter.filter_product.max_def
- \+/\- *lemma* filter.filter_product.min_def
- \+/\- *lemma* filter.filter_product.of_abs
- \+/\- *lemma* filter.filter_product.of_div
- \+/\- *lemma* filter.filter_product.of_eq
- \+/\- *lemma* filter.filter_product.of_lt
- \+/\- *lemma* filter.filter_product.of_lt_of_lt
- \+/\- *lemma* filter.filter_product.of_max
- \+/\- *lemma* filter.filter_product.of_min
- \+/\- *lemma* filter.filter_product.of_ne
- \+/\- *lemma* filter.filter_product.of_rel
- \+/\- *lemma* filter.filter_product.of_rel_of_rel
- \+/\- *lemma* filter.filter_product.of_rel_of_rel₂
- \+/\- *lemma* filter.filter_product.of_rel₂
- \+/\- *lemma* filter.filter_product.of_seq_add
- \+/\- *theorem* filter.filter_product.of_seq_fun
- \+/\- *theorem* filter.filter_product.of_seq_fun₂
- \+/\- *lemma* filter.filter_product.of_seq_mul



## [2019-05-11 15:00:03](https://github.com/leanprover-community/mathlib/commit/60da4f4)
feat(data/polynomial): degree_eq_one_of_irreducible_of_root ([#1010](https://github.com/leanprover-community/mathlib/pull/1010))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.degree_eq_one_of_irreducible_of_root



## [2019-05-11 13:14:21](https://github.com/leanprover-community/mathlib/commit/8603e6b)
refactor(algebra/associated): rename nonzero_of_irreducible to ne_zero_of_irreducible ([#1009](https://github.com/leanprover-community/mathlib/pull/1009))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* ne_zero_of_irreducible
- \- *theorem* nonzero_of_irreducible

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2019-05-11 00:09:41](https://github.com/leanprover-community/mathlib/commit/6858c2f)
fix(category/fold): use correct `opposite` ([#1008](https://github.com/leanprover-community/mathlib/pull/1008))
#### Estimated changes
Modified src/category/fold.lean
- \+/\- *def* monoid.foldr
- \+/\- *def* monoid.mfoldr

Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.opposite.op_mul
- \- *lemma* category_theory.opposite.op_one
- \- *lemma* category_theory.opposite.unop_mul
- \- *lemma* category_theory.opposite.unop_one



## [2019-05-10 02:32:26](https://github.com/leanprover-community/mathlib/commit/91a7fc2)
fix(tactic/basic): missing `conv` from tactic.basic ([#1004](https://github.com/leanprover-community/mathlib/pull/1004))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-05-10 00:53:48](https://github.com/leanprover-community/mathlib/commit/e66e1f3)
feat(set_theory): add to cardinal, ordinal, cofinality ([#963](https://github.com/leanprover-community/mathlib/pull/963))
* feat(set_theory): add to cardinal, ordinal, cofinality
The main new fact is the infinite pigeonhole principle
Also includes many basic additions
* fix name change in other files
* address all of Mario's comments
* use classical tactic in order/basic
I did not use it for well_founded.succ, because that resulted in an error in lt_succ
* fix error
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finsupp.lean


Modified src/measure_theory/measurable_space.lean


Modified src/order/basic.lean
- \+ *lemma* not_bounded_iff
- \+ *lemma* not_unbounded_iff
- \+/\- *theorem* well_founded.has_min
- \+/\- *theorem* well_founded.min_mem
- \+/\- *theorem* well_founded.not_lt_min

Modified src/order/order_iso.lean
- \+ *lemma* order_iso.ord''
- \+ *lemma* order_iso.to_equiv_to_fun

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.countable_iff
- \+ *lemma* cardinal.finset_card_lt_omega
- \+ *theorem* cardinal.le_mk_iff_exists_subset
- \+ *lemma* cardinal.le_powerlt
- \+ *lemma* cardinal.mk_Union_le
- \+ *lemma* cardinal.mk_bUnion_le
- \- *theorem* cardinal.mk_eq_of_injective
- \+ *theorem* cardinal.mk_image_eq
- \+ *lemma* cardinal.mk_image_eq_lift
- \+ *lemma* cardinal.mk_image_eq_of_inj_on
- \+ *lemma* cardinal.mk_image_eq_of_inj_on_lift
- \+ *lemma* cardinal.mk_preimage_of_injective
- \+ *lemma* cardinal.mk_preimage_of_injective_lift
- \+ *lemma* cardinal.mk_preimage_of_injective_of_subset_range
- \+ *lemma* cardinal.mk_preimage_of_injective_of_subset_range_lift
- \+ *lemma* cardinal.mk_preimage_of_subset_range
- \+ *lemma* cardinal.mk_preimage_of_subset_range_lift
- \+ *lemma* cardinal.mk_range_eq
- \+/\- *theorem* cardinal.mk_range_le
- \+ *lemma* cardinal.mk_sUnion_le
- \+ *lemma* cardinal.mk_sep
- \+ *lemma* cardinal.mk_set_le
- \+ *lemma* cardinal.mk_subset_ge_of_subset_image
- \+ *lemma* cardinal.mk_subset_ge_of_subset_image_lift
- \+ *lemma* cardinal.mk_subtype_mono
- \+ *lemma* cardinal.mk_subtype_of_equiv
- \+ *theorem* cardinal.out_embedding
- \+ *theorem* cardinal.powerlt_aux
- \+ *lemma* cardinal.powerlt_le
- \+ *lemma* cardinal.powerlt_le_powerlt_left
- \+ *lemma* cardinal.powerlt_max
- \+ *lemma* cardinal.powerlt_succ
- \+ *lemma* cardinal.powerlt_zero
- \+ *lemma* cardinal.succ_ne_zero
- \+ *theorem* cardinal.sup_eq_zero
- \+ *lemma* cardinal.two_le_iff'
- \+ *lemma* cardinal.two_le_iff
- \+ *lemma* cardinal.zero_power_le
- \+ *lemma* cardinal.zero_powerlt

Modified src/set_theory/cofinality.lean
- \+ *theorem* cardinal.sup_lt_ord_of_is_regular
- \+/\- *def* order.cof
- \+ *lemma* order.cof_le
- \+ *lemma* order.le_cof
- \+ *lemma* ordinal.cof_type
- \+ *theorem* ordinal.infinite_pigeonhole
- \+ *theorem* ordinal.infinite_pigeonhole_card
- \+ *theorem* ordinal.infinite_pigeonhole_set
- \+ *theorem* ordinal.sup_lt
- \+ *theorem* ordinal.sup_lt_ord
- \+ *theorem* ordinal.unbounded_of_unbounded_Union
- \+ *theorem* ordinal.unbounded_of_unbounded_sUnion
- \+ *def* strict_order.cof

Modified src/set_theory/ordinal.lean
- \+ *lemma* cardinal.add_one_eq
- \+ *lemma* cardinal.card_typein_lt
- \+ *lemma* cardinal.card_typein_out_lt
- \+ *lemma* cardinal.lt_ord_succ_card
- \+ *lemma* cardinal.mk_bounded_set_le
- \+ *lemma* cardinal.mk_bounded_set_le_of_omega_le
- \+ *lemma* cardinal.mk_bounded_subset_le
- \+ *lemma* cardinal.mk_ord_out
- \+ *lemma* cardinal.mul_eq_max_of_omega_le_left
- \+ *lemma* cardinal.mul_le_max_of_omega_le_left
- \+ *lemma* cardinal.ord_injective
- \+ *lemma* cardinal.power_nat_le
- \+ *lemma* cardinal.powerlt_omega
- \+ *lemma* cardinal.powerlt_omega_le
- \+ *lemma* ordinal.card_typein
- \+ *lemma* ordinal.enum_le_enum
- \+ *lemma* ordinal.has_succ_of_is_limit
- \+ *def* ordinal.initial_seg_out
- \+ *lemma* ordinal.injective_typein
- \+ *lemma* ordinal.mk_initial_seg
- \+ *lemma* ordinal.order_iso_enum'
- \+ *lemma* ordinal.order_iso_enum
- \+ *def* ordinal.order_iso_out
- \+ *def* ordinal.principal_seg_out
- \+ *lemma* ordinal.sup_succ
- \+ *lemma* ordinal.type_out
- \+ *lemma* ordinal.type_subrel_lt
- \+ *def* ordinal.typein_iso
- \+ *lemma* ordinal.typein_le_typein
- \+ *lemma* ordinal.unbounded_range_of_sup_ge
- \+ *def* principal_seg.lt_equiv
- \+ *lemma* principal_seg.top_lt_top



## [2019-05-09 09:29:20](https://github.com/leanprover-community/mathlib/commit/5329bf3)
feat(algebra/pointwise): More lemmas on pointwise multiplication ([#997](https://github.com/leanprover-community/mathlib/pull/997))
* feat(algebra/pointwise): More lemmas on pointwise multiplication
* Fix build, hopefully
* Fix build
* to_additive + fix formatting
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.mem_smul_set
- \+ *lemma* set.mul_subset_mul
- \+ *def* set.pointwise_add_fintype
- \+ *def* set.pointwise_mul_action
- \+ *def* set.pointwise_mul_fintype
- \+ *def* set.pointwise_mul_image_is_semiring_hom
- \+ *lemma* set.smul_set_eq_image



## [2019-05-09 05:36:49](https://github.com/leanprover-community/mathlib/commit/df5edde)
refactor(strict_mono): make definition + move to order_functions ([#998](https://github.com/leanprover-community/mathlib/pull/998))
* refactor(strict_mono): make definition + move to order_functions
* Weaken assumptions from preorder to has_lt
#### Estimated changes
Modified src/algebra/order.lean
- \- *lemma* injective_of_strict_mono
- \- *lemma* le_iff_le_of_strict_mono
- \- *lemma* lt_iff_lt_of_strict_mono
- \- *theorem* ordering.compares_of_strict_mono

Modified src/algebra/order_functions.lean
- \+ *theorem* strict_mono.compares
- \+ *lemma* strict_mono.injective
- \+ *lemma* strict_mono.le_iff_le
- \+ *lemma* strict_mono.lt_iff_lt
- \+ *lemma* strict_mono.monotone
- \+ *def* strict_mono
- \+ *lemma* strict_mono_of_monotone_of_injective

Modified src/ring_theory/noetherian.lean


Modified src/set_theory/ordinal.lean




## [2019-05-08 22:40:27](https://github.com/leanprover-community/mathlib/commit/8f5d240)
refactor(order/basic): make type class args explicit in {*}order.lift ([#995](https://github.com/leanprover-community/mathlib/pull/995))
* refactor(order/basic): make type class arguments explicit for {*}order.lift
* Let's try again
* And another try
* Silly typo
* Fix error
* Oops, missed this one
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/data/fin.lean


Modified src/data/real/nnreal.lean


Modified src/linear_algebra/basic.lean


Modified src/order/basic.lean
- \+/\- *def* decidable_linear_order.lift
- \+/\- *def* linear_order.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* preorder.lift

Modified src/order/zorn.lean




## [2019-05-08 20:20:16](https://github.com/leanprover-community/mathlib/commit/7f9717f)
feat(*): preorder instances for with_bot and with_zero ([#996](https://github.com/leanprover-community/mathlib/pull/996))
* feat(*): preorder instances for with_bot and with_zero
* Let's try again
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/order/bounded_lattice.lean




## [2019-05-08 11:42:00](https://github.com/leanprover-community/mathlib/commit/c9cfafc)
chore(tactics): splitting tactics and tests into more files ([#985](https://github.com/leanprover-community/mathlib/pull/985))
* chore(tactics): splitting tactics and tests into more files, cleaning up dependencies
* tweaking comment
* introducing `tactic.basic` and fixing imports
* fixes
* fix copyright
* fix some things
#### Estimated changes
Modified src/algebra/group.lean


Modified src/category/bitraversable/instances.lean


Modified src/category/monad/basic.lean


Modified src/category/monad/writer.lean


Modified src/category_theory/category.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/data/list/defs.lean
- \+/\- *def* list.func.add
- \+/\- *def* list.func.neg
- \+/\- *def* list.func.pointwise
- \+/\- *def* list.func.sub

Modified src/data/option/basic.lean


Modified src/data/padics/hensel.lean


Modified src/data/rel.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/set/basic.lean


Modified src/group_theory/eckmann_hilton.lean


Modified src/logic/basic.lean


Modified src/logic/relation.lean


Modified src/order/lexicographic.lean


Modified src/tactic/algebra.lean


Modified src/tactic/auto_cases.lean


Modified src/tactic/basic.lean


Modified src/tactic/cache.lean


Modified src/tactic/chain.lean


Modified src/tactic/converter/interactive.lean


Added src/tactic/core.lean


Modified src/tactic/default.lean


Modified src/tactic/elide.lean


Modified src/tactic/explode.lean


Modified src/tactic/ext.lean


Modified src/tactic/find.lean


Modified src/tactic/generalize_proofs.lean


Modified src/tactic/interactive.lean


Modified src/tactic/library_search.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/default.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/rcases.lean


Modified src/tactic/replacer.lean


Modified src/tactic/rewrite.lean


Modified src/tactic/scc.lean


Added src/tactic/solve_by_elim.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tidy.lean


Modified src/tactic/where.lean


Modified src/tactic/wlog.lean


Added test/conv.lean


Added test/convert.lean
- \+ *lemma* singleton_inter_singleton_eq_empty

Added test/ext.lean
- \+ *structure* dependent_fields
- \+ *lemma* df.ext
- \+ *def* my_bar
- \+ *def* my_foo
- \+ *lemma* unit.ext

Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean


Modified test/monotonicity.lean


Modified test/monotonicity/test_cases.lean


Added test/rcases.lean


Added test/rewrite.lean


Modified test/solve_by_elim.lean


Modified test/tactics.lean
- \- *structure* dependent_fields
- \- *lemma* df.ext
- \- *def* my_bar
- \- *def* my_foo
- \- *lemma* unit.ext

Added test/tauto.lean


Added test/wlog.lean




## [2019-05-08 09:47:14](https://github.com/leanprover-community/mathlib/commit/73a30da)
feat(group_theory/subgroup): is_subgroup.inter ([#994](https://github.com/leanprover-community/mathlib/pull/994))
#### Estimated changes
Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean
- \+ *lemma* is_submonoid.inter



## [2019-05-07 20:44:11-05:00](https://github.com/leanprover-community/mathlib/commit/87cf6e3)
feat(category_theory/category_of_elements) ([#990](https://github.com/leanprover-community/mathlib/pull/990))
* feat(category_theory/category_of_elements)
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/elements.lean
Co-Authored-By: semorrison <scott@tqft.net>
* Update src/category_theory/punit.lean
Co-Authored-By: semorrison <scott@tqft.net>
* various
* remaining simp lemmas
#### Estimated changes
Added src/category_theory/elements.lean
- \+ *def* category_theory.category_of_elements.comma_equivalence
- \+ *def* category_theory.category_of_elements.from_comma
- \+ *lemma* category_theory.category_of_elements.from_comma_map
- \+ *lemma* category_theory.category_of_elements.from_comma_obj
- \+ *def* category_theory.category_of_elements.to_comma
- \+ *lemma* category_theory.category_of_elements.to_comma_map
- \+ *lemma* category_theory.category_of_elements.to_comma_obj
- \+ *def* category_theory.category_of_elements.π
- \+ *lemma* category_theory.category_of_elements.π_map
- \+ *lemma* category_theory.category_of_elements.π_obj
- \+ *def* category_theory.functor.elements

Modified src/category_theory/punit.lean
- \+ *def* category_theory.functor.star
- \+ *lemma* category_theory.functor.star_map
- \+ *lemma* category_theory.functor.star_obj



## [2019-05-07 19:03:46](https://github.com/leanprover-community/mathlib/commit/820bac3)
building the hyperreal library ([#835](https://github.com/leanprover-community/mathlib/pull/835))
* more instances
* fix stuff that got weirded
* fix stuff that got weird
* fix stuff that became weird
* build hyperreal library (with sorries)
* fix weirdness, prettify etc.
* spaces
* st lt le lemmas fix type
* Update src/data/real/hyperreal.lean
Co-Authored-By: abhimanyupallavisudhir <43954672+abhimanyupallavisudhir@users.noreply.github.com>
* if then
* more stuff
* Update hyperreal.lean
* Update hyperreal.lean
* Update basic.lean
* Update basic.lean
* Update hyperreal.lean
* of_max, of_min, of_abs
* Update filter_product.lean
* Update hyperreal.lean
* abs_def etc.
* Update filter_product.lean
* hole
* Update hyperreal.lean
* Update filter_product.lean
* Update filter_product.lean
* Update filter_product.lean
* Update hyperreal.lean
* Update hyperreal.lean
* Update filter_product.lean
* Update hyperreal.lean
* Update hyperreal.lean
* finally done with all sorries!
* Update hyperreal.lean
* fix (?)
* fix (?) ring issue
* real.Sup_univ
* st is Sup
* st_id_real spacebar
* sup --> Sup
* fix weirds
* dollar signs
* 100-column
* 100 columns rule
* Update hyperreal.lean
* removing uparrows
* uparrows
* some stuff that got away
* fix
* lift_id
* fix?
* fix mono, hopefully
* fix mono, hopefully
* this should work
* fix -- no more mono
* fixes
* fixes
* fixes
* fixes
* ok, fixed
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* neg_neg_iff_pos

Modified src/data/real/basic.lean
- \+ *theorem* real.Sup_univ

Modified src/data/real/hyperreal.lean
- \+ *theorem* hyperreal.abs_lt_real_iff_infinitesimal
- \+ *lemma* hyperreal.epsilon_eq_inv_omega
- \- *theorem* hyperreal.epsilon_eq_inv_omega
- \+/\- *lemma* hyperreal.epsilon_lt_pos
- \+ *lemma* hyperreal.eq_of_is_st_real
- \+ *theorem* hyperreal.exists_st_iff_not_infinite
- \+ *theorem* hyperreal.exists_st_of_not_infinite
- \+ *theorem* hyperreal.gt_of_neg_of_infinitesimal
- \+ *def* hyperreal.infinite
- \+ *lemma* hyperreal.infinite_iff_abs_lt_abs
- \+ *lemma* hyperreal.infinite_iff_infinite_abs
- \+ *lemma* hyperreal.infinite_iff_infinite_neg
- \+ *lemma* hyperreal.infinite_iff_infinite_pos_abs
- \+ *theorem* hyperreal.infinite_iff_infinitesimal_inv
- \+ *theorem* hyperreal.infinite_iff_not_exists_st
- \+ *lemma* hyperreal.infinite_mul_infinite
- \+ *lemma* hyperreal.infinite_mul_of_infinite_not_infinitesimal
- \+ *lemma* hyperreal.infinite_mul_of_not_infinitesimal_infinite
- \+ *def* hyperreal.infinite_neg
- \+ *lemma* hyperreal.infinite_neg_add_infinite_neg
- \+ *lemma* hyperreal.infinite_neg_add_not_infinite
- \+ *lemma* hyperreal.infinite_neg_add_not_infinite_pos
- \+ *lemma* hyperreal.infinite_neg_def
- \+ *lemma* hyperreal.infinite_neg_iff_infinite_and_neg
- \+ *lemma* hyperreal.infinite_neg_iff_infinite_of_neg
- \+ *lemma* hyperreal.infinite_neg_iff_infinite_pos_neg
- \+ *lemma* hyperreal.infinite_neg_iff_infinitesimal_inv_neg
- \+ *lemma* hyperreal.infinite_neg_mul_infinite_neg
- \+ *lemma* hyperreal.infinite_neg_mul_infinite_pos
- \+ *lemma* hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos
- \+ *lemma* hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg
- \+ *lemma* hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos
- \+ *lemma* hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg
- \+ *lemma* hyperreal.infinite_neg_neg_of_infinite_pos
- \+ *theorem* hyperreal.infinite_neg_of_tendsto_bot
- \+ *theorem* hyperreal.infinite_of_infinitesimal_inv
- \+ *lemma* hyperreal.infinite_omega
- \+ *def* hyperreal.infinite_pos
- \+ *lemma* hyperreal.infinite_pos_abs_iff_infinite_abs
- \+ *lemma* hyperreal.infinite_pos_add_infinite_pos
- \+ *lemma* hyperreal.infinite_pos_add_not_infinite
- \+ *lemma* hyperreal.infinite_pos_add_not_infinite_neg
- \+ *lemma* hyperreal.infinite_pos_def
- \+ *lemma* hyperreal.infinite_pos_iff_infinite_and_pos
- \+ *lemma* hyperreal.infinite_pos_iff_infinite_neg_neg
- \+ *lemma* hyperreal.infinite_pos_iff_infinite_of_nonneg
- \+ *lemma* hyperreal.infinite_pos_iff_infinite_of_pos
- \+ *lemma* hyperreal.infinite_pos_iff_infinitesimal_inv_pos
- \+ *lemma* hyperreal.infinite_pos_mul_infinite_neg
- \+ *lemma* hyperreal.infinite_pos_mul_infinite_pos
- \+ *lemma* hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg
- \+ *lemma* hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
- \+ *lemma* hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg
- \+ *lemma* hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos
- \+ *lemma* hyperreal.infinite_pos_neg_of_infinite_neg
- \+ *theorem* hyperreal.infinite_pos_of_tendsto_top
- \+ *lemma* hyperreal.infinite_pos_omega
- \+ *lemma* hyperreal.infinitesimal_add
- \+ *theorem* hyperreal.infinitesimal_def
- \+/\- *theorem* hyperreal.infinitesimal_epsilon
- \+ *theorem* hyperreal.infinitesimal_iff_infinite_inv
- \+ *theorem* hyperreal.infinitesimal_inv_of_infinite
- \+ *lemma* hyperreal.infinitesimal_mul
- \+ *lemma* hyperreal.infinitesimal_neg
- \+ *lemma* hyperreal.infinitesimal_neg_iff
- \+ *lemma* hyperreal.infinitesimal_neg_iff_infinite_neg_inv
- \+/\- *theorem* hyperreal.infinitesimal_of_tendsto_zero
- \+ *lemma* hyperreal.infinitesimal_pos_iff_infinite_pos_inv
- \+ *theorem* hyperreal.infinitesimal_sub_is_st
- \+ *theorem* hyperreal.infinitesimal_sub_st
- \+ *lemma* hyperreal.infinitesimal_zero
- \+ *lemma* hyperreal.inv_epsilon_eq_omega
- \- *theorem* hyperreal.inv_epsilon_eq_omega
- \+ *theorem* hyperreal.is_st_Sup
- \+ *lemma* hyperreal.is_st_add
- \+ *lemma* hyperreal.is_st_iff_abs_sub_lt_delta
- \+ *lemma* hyperreal.is_st_inj_real
- \+ *lemma* hyperreal.is_st_inv
- \+ *lemma* hyperreal.is_st_le_of_le
- \+ *lemma* hyperreal.is_st_mul
- \+ *lemma* hyperreal.is_st_neg
- \+ *theorem* hyperreal.is_st_of_tendsto
- \+ *lemma* hyperreal.is_st_real_iff_eq
- \+ *lemma* hyperreal.is_st_refl_real
- \+ *lemma* hyperreal.is_st_st'
- \+ *lemma* hyperreal.is_st_st
- \+ *lemma* hyperreal.is_st_st_of_exists_st
- \+ *lemma* hyperreal.is_st_st_of_is_st
- \+ *lemma* hyperreal.is_st_sub
- \+ *lemma* hyperreal.is_st_symm_real
- \+ *lemma* hyperreal.is_st_trans_real
- \+/\- *theorem* hyperreal.is_st_unique
- \+ *theorem* hyperreal.lt_neg_of_pos_of_infinitesimal
- \+ *lemma* hyperreal.lt_of_is_st_lt
- \+ *theorem* hyperreal.lt_of_pos_of_infinitesimal
- \+ *lemma* hyperreal.lt_of_st_lt
- \+ *lemma* hyperreal.ne_zero_of_infinite
- \- *lemma* hyperreal.neg_lt_of_tendsto_zero_of_neg
- \+ *lemma* hyperreal.neg_lt_of_tendsto_zero_of_pos
- \+ *lemma* hyperreal.neg_of_infinite_neg
- \+ *lemma* hyperreal.not_infinite_add
- \+ *theorem* hyperreal.not_infinite_iff_exist_lt_gt
- \+ *lemma* hyperreal.not_infinite_mul
- \+ *lemma* hyperreal.not_infinite_neg
- \+ *lemma* hyperreal.not_infinite_neg_add_infinite_pos
- \+ *lemma* hyperreal.not_infinite_neg_of_infinite_pos
- \+ *theorem* hyperreal.not_infinite_of_exists_st
- \+ *lemma* hyperreal.not_infinite_of_infinitesimal
- \+ *lemma* hyperreal.not_infinite_pos_add_infinite_neg
- \+ *lemma* hyperreal.not_infinite_pos_of_infinite_neg
- \+ *theorem* hyperreal.not_infinite_real
- \+ *lemma* hyperreal.not_infinite_zero
- \+ *lemma* hyperreal.not_infinitesimal_of_infinite
- \+ *lemma* hyperreal.not_infinitesimal_of_infinite_neg
- \+ *lemma* hyperreal.not_infinitesimal_of_infinite_pos
- \+ *theorem* hyperreal.not_real_of_infinite
- \+ *lemma* hyperreal.not_real_of_infinitesimal_ne_zero
- \+ *lemma* hyperreal.pos_of_infinite_pos
- \+ *lemma* hyperreal.st_add
- \+ *theorem* hyperreal.st_eq_Sup
- \+ *lemma* hyperreal.st_id_real
- \+ *theorem* hyperreal.st_infinite
- \+ *lemma* hyperreal.st_inv
- \+ *lemma* hyperreal.st_le_of_le
- \+ *lemma* hyperreal.st_mul
- \+ *lemma* hyperreal.st_neg
- \+ *lemma* hyperreal.st_of_is_st
- \+ *lemma* hyperreal.zero_iff_infinitesimal_real
- \+ *lemma* hyperreal.zero_of_infinitesimal_real

Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto_at_top_at_bot

Modified src/order/filter/filter_product.lean
- \+ *lemma* filter.filter_product.abs_def
- \+ *lemma* filter.filter_product.lift_id
- \+/\- *lemma* filter.filter_product.lt_def
- \+ *lemma* filter.filter_product.max_def
- \+ *lemma* filter.filter_product.min_def
- \+ *lemma* filter.filter_product.of_abs
- \+ *lemma* filter.filter_product.of_div
- \+/\- *lemma* filter.filter_product.of_eq
- \+/\- *lemma* filter.filter_product.of_eq_coe
- \- *lemma* filter.filter_product.of_id
- \+/\- *lemma* filter.filter_product.of_le
- \+/\- *lemma* filter.filter_product.of_le_of_le
- \+/\- *lemma* filter.filter_product.of_lt
- \+/\- *lemma* filter.filter_product.of_lt_of_lt
- \+ *lemma* filter.filter_product.of_max
- \+ *lemma* filter.filter_product.of_min
- \+/\- *lemma* filter.filter_product.of_ne
- \+/\- *lemma* filter.filter_product.of_rel
- \+/\- *lemma* filter.filter_product.of_rel_of_rel
- \+/\- *lemma* filter.filter_product.of_rel_of_rel₂
- \+/\- *lemma* filter.filter_product.of_rel₂
- \+/\- *lemma* filter.filter_product.of_seq_add
- \+/\- *lemma* filter.filter_product.of_seq_mul
- \+ *lemma* filter.filter_product.of_sub



## [2019-05-07 17:27:55](https://github.com/leanprover-community/mathlib/commit/4a38d2e)
feat(scripts): add --build-new flag to cache-olean ([#992](https://github.com/leanprover-community/mathlib/pull/992))
#### Estimated changes
Modified scripts/cache-olean.py




## [2019-05-07 10:49:02-04:00](https://github.com/leanprover-community/mathlib/commit/717033e)
chore(build): cron build restarts from scratch
#### Estimated changes
Modified .travis.yml




## [2019-05-07 08:45:19](https://github.com/leanprover-community/mathlib/commit/c726c12)
feat(category/monad/cont): monad_cont instances for state_t, reader_t, except_t and option_t ([#733](https://github.com/leanprover-community/mathlib/pull/733))
* feat(category/monad/cont): monad_cont instances for state_t, reader_t,
except_t and option_t
* feat(category/monad/writer): writer monad transformer
#### Estimated changes
Added src/category/monad/basic.lean
- \+ *lemma* map_eq_bind_pure_comp

Modified src/category/monad/cont.lean
- \+ *def* cont
- \+ *def* cont_t.cont_t.monad_lift
- \+ *def* except_t.call_cc
- \+ *lemma* except_t.goto_mk_label
- \+ *def* except_t.mk_label
- \+ *def* option_t.call_cc
- \+ *lemma* option_t.goto_mk_label
- \+ *def* option_t.mk_label
- \+ *def* reader_t.call_cc
- \+ *lemma* reader_t.goto_mk_label
- \+ *def* reader_t.mk_label
- \+ *def* state_t.call_cc
- \+ *lemma* state_t.goto_mk_label
- \+ *def* state_t.mk_label
- \+ *def* writer_t.call_cc
- \+ *lemma* writer_t.goto_mk_label
- \+ *def* writer_t.mk_label

Added src/category/monad/writer.lean
- \+ *def* except_t.pass_aux
- \+ *def* option_t.pass_aux
- \+ *def* swap_right
- \+ *def* writer
- \+ *structure* writer_t



## [2019-05-07 01:25:54-04:00](https://github.com/leanprover-community/mathlib/commit/98ba07b)
chore(build): fix stages in cron job
#### Estimated changes
Modified .travis.yml




## [2019-05-07 00:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/505f748)
chore(build): build against Lean 3.5 nightly build ([#989](https://github.com/leanprover-community/mathlib/pull/989))
#### Estimated changes
Modified .travis.yml




## [2019-05-06 16:50:37](https://github.com/leanprover-community/mathlib/commit/6eba20b)
feat(category_theory): currying for functors ([#981](https://github.com/leanprover-community/mathlib/pull/981))
* feat(category_theory): currying for functors
* Update src/category_theory/currying.lean
Co-Authored-By: semorrison <scott@tqft.net>
* compacting
* fix import
* change from review
* rfl on same line
#### Estimated changes
Added src/category_theory/currying.lean
- \+ *lemma* category_theory.curry.map_app_app
- \+ *lemma* category_theory.curry.obj_map_app
- \+ *lemma* category_theory.curry.obj_obj_map
- \+ *lemma* category_theory.curry.obj_obj_obj
- \+ *def* category_theory.curry
- \+ *def* category_theory.curry_obj
- \+ *def* category_theory.currying
- \+ *lemma* category_theory.uncurry.map_app
- \+ *lemma* category_theory.uncurry.obj_map
- \+ *lemma* category_theory.uncurry.obj_obj
- \+ *def* category_theory.uncurry



## [2019-05-06 05:34:58](https://github.com/leanprover-community/mathlib/commit/f536dac)
six(style.md): fix broken code ([#987](https://github.com/leanprover-community/mathlib/pull/987))
#### Estimated changes
Modified docs/style.md




## [2019-05-05 11:57:30](https://github.com/leanprover-community/mathlib/commit/23270e7)
feat(ring_theory/adjoin): adjoining elements to form subalgebras ([#756](https://github.com/leanprover-community/mathlib/pull/756))
* feat(ring_theory/adjoin): adjoining elements to form subalgebras
* Fix build
* Change to_submodule into a coercion
* Use pointwise_mul
* add simp attribute to adjoin_empty
#### Estimated changes
Added src/ring_theory/adjoin.lean
- \+ *theorem* algebra.adjoin_empty
- \+ *theorem* algebra.adjoin_eq_range
- \+ *theorem* algebra.adjoin_eq_span
- \+ *theorem* algebra.adjoin_int
- \+ *theorem* algebra.adjoin_le
- \+ *theorem* algebra.adjoin_le_iff
- \+ *theorem* algebra.adjoin_mono
- \+ *theorem* algebra.adjoin_singleton_eq_range
- \+ *theorem* algebra.adjoin_union
- \+ *theorem* algebra.adjoin_union_coe_submodule
- \+ *theorem* algebra.fg_trans
- \+ *theorem* algebra.subset_adjoin
- \+ *theorem* is_noetherian_ring_closure
- \+ *theorem* is_noetherian_ring_of_fg
- \+ *def* subalgebra.fg
- \+ *theorem* subalgebra.fg_bot
- \+ *theorem* subalgebra.fg_def

Modified src/ring_theory/algebra.lean




## [2019-05-05 07:50:10](https://github.com/leanprover-community/mathlib/commit/3f26ba8)
feat(category_theory/products): associators ([#982](https://github.com/leanprover-community/mathlib/pull/982))
#### Estimated changes
Added src/category_theory/products/associator.lean
- \+ *def* category_theory.prod.associativity
- \+ *def* category_theory.prod.associator
- \+ *lemma* category_theory.prod.associator_map
- \+ *lemma* category_theory.prod.associator_obj
- \+ *def* category_theory.prod.inverse_associator
- \+ *lemma* category_theory.prod.inverse_associator_map
- \+ *lemma* category_theory.prod.inverse_associator_obj

Renamed src/category_theory/bifunctor.lean to src/category_theory/products/bifunctor.lean


Renamed src/category_theory/products.lean to src/category_theory/products/default.lean




## [2019-05-05 07:02:45](https://github.com/leanprover-community/mathlib/commit/1e8f438)
feat(presheaves) ([#886](https://github.com/leanprover-community/mathlib/pull/886))
* feat(category_theory/colimits): missing simp lemmas
* feat(category_theory): functor.map_nat_iso
* define `functor.map_nat_iso`, and relate to whiskering
* rename `functor.on_iso` to `functor.map_iso`
* add some missing lemmas about whiskering
* fix(category_theory): presheaves, unbundled and bundled, and pushforwards
* restoring `(opens X)ᵒᵖ`
* various changes from working on stalks
* rename `nbhds` to `open_nhds`
* fix introduced typo
* typo
* compactify a proof
* rename `presheaf` to `presheaf_on_space`
* fix(category_theory): turn `has_limits` classes into structures
* naming instances to avoid collisions
* breaking up instances.topological_spaces
* fixing all the other pi-type typclasses
* fix import
* oops
* fix import
* missed one
* typo
* restoring eq_to_hom simp lemmas
* removing unnecessary simp lemma
* remove another superfluous lemma
* removing the nat_trans and vcomp notations; use \hom and \gg
* a simpler proposal
* getting rid of vcomp
* fix
* splitting files
* update notation
* fix
* cleanup
* use iso_whisker_right instead of map_nat_iso
* proofs magically got easier?
* improve some proofs
* remove crap
* minimise imports
* chore(travis): disable the check for minimal imports
* Update src/algebraic_geometry/presheafed_space.lean
Co-Authored-By: semorrison <scott@tqft.net>
* writing `op_induction` tactic, and improving proofs
* squeeze_simping
* cleanup
* rearranging
* Update src/category_theory/instances/Top/presheaf.lean
Co-Authored-By: semorrison <scott@tqft.net>
* fix `open` statements, and use `op_induction`
* rename terms of PresheafedSpace to X Y Z. rename field from .X to .to_Top
* forgetful functor
* update comments about unfortunate proofs
* add coercion from morphisms of PresheafedSpaces to morphisms in Top
#### Estimated changes
Added src/algebraic_geometry/presheafed_space.lean
- \+ *def* algebraic_geometry.PresheafedSpace.comp
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_c
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_coe
- \+ *lemma* algebraic_geometry.PresheafedSpace.comp_f
- \+ *lemma* algebraic_geometry.PresheafedSpace.ext
- \+ *def* algebraic_geometry.PresheafedSpace.forget
- \+ *structure* algebraic_geometry.PresheafedSpace.hom
- \+ *def* algebraic_geometry.PresheafedSpace.id
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_c
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_f
- \+ *structure* algebraic_geometry.PresheafedSpace
- \+ *def* category_theory.functor.map_presheaf
- \+ *lemma* category_theory.functor.map_presheaf_map_c
- \+ *lemma* category_theory.functor.map_presheaf_map_f
- \+ *lemma* category_theory.functor.map_presheaf_obj_X
- \+ *lemma* category_theory.functor.map_presheaf_obj_𝒪
- \+ *def* category_theory.nat_trans.on_presheaf

Modified src/category_theory/instances/Top/basic.lean


Modified src/category_theory/instances/Top/default.lean


Modified src/category_theory/instances/Top/open_nhds.lean


Modified src/category_theory/instances/Top/opens.lean


Added src/category_theory/instances/Top/presheaf.lean
- \+ *def* category_theory.instances.Top.presheaf.pushforward.comp
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward.comp_hom_app
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward.comp_inv_app
- \+ *def* category_theory.instances.Top.presheaf.pushforward.id
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward.id_hom_app'
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward.id_hom_app
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward.id_inv_app'
- \+ *def* category_theory.instances.Top.presheaf.pushforward
- \+ *def* category_theory.instances.Top.presheaf.pushforward_eq
- \+ *lemma* category_theory.instances.Top.presheaf.pushforward_eq_eq
- \+ *def* category_theory.instances.Top.presheaf

Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.nat_iso.op_hom
- \+ *lemma* category_theory.nat_iso.op_inv
- \+ *def* category_theory.op_induction



## [2019-05-05 02:40:54](https://github.com/leanprover-community/mathlib/commit/fc8b08b)
feat(data/set/basic): prod_subset_iff ([#980](https://github.com/leanprover-community/mathlib/pull/980))
* feat(data/set/basic): prod_subset_iff
* syntax
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.prod_subset_iff



## [2019-05-04 23:56:50](https://github.com/leanprover-community/mathlib/commit/fbce6e4)
fix(data/set/finite): make fintype_seq an instance ([#979](https://github.com/leanprover-community/mathlib/pull/979))
#### Estimated changes
Modified src/data/set/finite.lean
- \- *def* set.fintype_seq



## [2019-05-04 22:16:39](https://github.com/leanprover-community/mathlib/commit/7dea60b)
feat(logic/basic): forall_iff_forall_surj ([#977](https://github.com/leanprover-community/mathlib/pull/977))
a lemma from the perfectoid project
#### Estimated changes
Modified src/logic/basic.lean
- \+ *theorem* forall_iff_forall_surj



## [2019-05-04 20:01:33](https://github.com/leanprover-community/mathlib/commit/b4d483e)
feat(colimits): arbitrary colimits in Mon and CommRing ([#910](https://github.com/leanprover-community/mathlib/pull/910))
* feat(category_theory): working in Sort rather than Type, as far as possible
* missed one
* adding a comment about working in Type
* remove imax
* removing `props`, it's covered by `types`.
* fixing comment on `rel`
* tweak comment
* add matching extend_π lemma
* remove unnecessary universe annotation
* another missing s/Type/Sort/
* feat(category_theory/shapes): basic shapes of cones and conversions
minor tweaks
* Moving into src. Everything is borked.
* investigating sparse
* blech
* maybe working again?
* removing terrible square/cosquare names
* returning to filtered colimits
* colimits in Mon
* rename
* actually jump through the final hoop
* experiments
* fixing use of ext
* feat(colimits): colimits in Mon and CommRing
* fixes
* removing stuff I didn't mean to have in here
* minor
* fixes
* merge
* update after merge
* fix import
#### Estimated changes
Modified src/category_theory/concrete_category.lean
- \+ *lemma* category_theory.bundled.bundled_hom.ext
- \+/\- *lemma* category_theory.bundled.bundled_hom_coe

Modified src/category_theory/instances/CommRing/adjunctions.lean
- \+ *lemma* category_theory.instances.CommRing.hom_coe_app'

Modified src/category_theory/instances/CommRing/basic.lean
- \+ *lemma* category_theory.instances.CommRing.hom.ext
- \+/\- *lemma* category_theory.instances.CommRing.hom_coe_app

Added src/category_theory/instances/CommRing/colimits.lean
- \+ *def* category_theory.instances.CommRing.colimits.cocone_fun
- \+ *def* category_theory.instances.CommRing.colimits.cocone_morphism
- \+ *lemma* category_theory.instances.CommRing.colimits.cocone_naturality
- \+ *lemma* category_theory.instances.CommRing.colimits.cocone_naturality_components
- \+ *def* category_theory.instances.CommRing.colimits.colimit
- \+ *def* category_theory.instances.CommRing.colimits.colimit_cocone
- \+ *def* category_theory.instances.CommRing.colimits.colimit_is_colimit
- \+ *def* category_theory.instances.CommRing.colimits.colimit_setoid
- \+ *def* category_theory.instances.CommRing.colimits.colimit_type
- \+ *def* category_theory.instances.CommRing.colimits.desc_fun
- \+ *def* category_theory.instances.CommRing.colimits.desc_fun_lift
- \+ *def* category_theory.instances.CommRing.colimits.desc_morphism
- \+ *lemma* category_theory.instances.CommRing.colimits.naturality_bundled
- \+ *inductive* category_theory.instances.CommRing.colimits.prequotient
- \+ *lemma* category_theory.instances.CommRing.colimits.quot_add
- \+ *lemma* category_theory.instances.CommRing.colimits.quot_mul
- \+ *lemma* category_theory.instances.CommRing.colimits.quot_neg
- \+ *lemma* category_theory.instances.CommRing.colimits.quot_one
- \+ *lemma* category_theory.instances.CommRing.colimits.quot_zero
- \+ *inductive* category_theory.instances.CommRing.colimits.relation

Modified src/category_theory/instances/CommRing/default.lean


Renamed src/category_theory/instances/monoids.lean to src/category_theory/instances/Mon/basic.lean


Added src/category_theory/instances/Mon/colimits.lean
- \+ *def* category_theory.instances.Mon.colimits.cocone_fun
- \+ *def* category_theory.instances.Mon.colimits.cocone_morphism
- \+ *lemma* category_theory.instances.Mon.colimits.cocone_naturality
- \+ *lemma* category_theory.instances.Mon.colimits.cocone_naturality_components
- \+ *def* category_theory.instances.Mon.colimits.colimit
- \+ *def* category_theory.instances.Mon.colimits.colimit_cocone
- \+ *def* category_theory.instances.Mon.colimits.colimit_is_colimit
- \+ *def* category_theory.instances.Mon.colimits.colimit_setoid
- \+ *def* category_theory.instances.Mon.colimits.colimit_type
- \+ *def* category_theory.instances.Mon.colimits.desc_fun
- \+ *def* category_theory.instances.Mon.colimits.desc_fun_lift
- \+ *def* category_theory.instances.Mon.colimits.desc_morphism
- \+ *inductive* category_theory.instances.Mon.colimits.prequotient
- \+ *lemma* category_theory.instances.Mon.colimits.quot_mul
- \+ *lemma* category_theory.instances.Mon.colimits.quot_one
- \+ *inductive* category_theory.instances.Mon.colimits.relation

Added src/category_theory/instances/Mon/default.lean


Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.limits.cocone.naturality_bundled
- \+ *lemma* category_theory.limits.cone.naturality_bundled



## [2019-05-04 12:06:04-05:00](https://github.com/leanprover-community/mathlib/commit/c7baf8e)
feat(option/injective_map) ([#978](https://github.com/leanprover-community/mathlib/pull/978))
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* option.injective_map



## [2019-05-03 21:34:29](https://github.com/leanprover-community/mathlib/commit/f98ffde)
feat(tactic/decl_mk_const): performance improvement for library_search ([#967](https://github.com/leanprover-community/mathlib/pull/967))
* feat(tactic/decl_mk_const): auxiliary tactic for library_search [WIP]
* use decl_mk_const in library_search
* use decl_mk_const
* move into tactic/basic.lean
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/library_search.lean


Modified test/fin_cases.lean


Modified test/library_search/basic.lean


Modified test/library_search/ordered_ring.lean


Modified test/library_search/ring_theory.lean


Modified test/mllist.lean




## [2019-05-03 13:58:06-04:00](https://github.com/leanprover-community/mathlib/commit/7b1105b)
chore(build): build only master and its related PRs
#### Estimated changes
Modified .travis.yml




## [2019-05-03 13:37:08-04:00](https://github.com/leanprover-community/mathlib/commit/e747c91)
chore(README): put the badges in the README on one line ([#975](https://github.com/leanprover-community/mathlib/pull/975))
#### Estimated changes
Modified README.md




## [2019-05-03 12:35:46-04:00](https://github.com/leanprover-community/mathlib/commit/f2db636)
feat(docs/install_debian): Debian startup guide ([#974](https://github.com/leanprover-community/mathlib/pull/974))
* feat(docs/install_debian): Debian startup guide
* feat(scripts/install_debian): One-line install for Debian  [ci skip]
* fix(docs/install_debian*): Typos pointed out by Johan
Also adds a summary of what will be installed
#### Estimated changes
Added docs/install_debian.md


Added docs/install_debian_details.md


Added scripts/install_debian.sh




## [2019-05-03 11:30:19-05:00](https://github.com/leanprover-community/mathlib/commit/f5060c4)
feat(category_theory/limits): support for special shapes of (co)limits ([#938](https://github.com/leanprover-community/mathlib/pull/938))
feat(category_theory/limits): support for special shapes of (co)limits
#### Estimated changes
Added docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+ *def* I
- \+ *def* I_0
- \+ *def* I_1
- \+ *def* R
- \+ *def* X
- \+ *def* Y
- \+ *def* cylinder
- \+ *def* cylinder_0
- \+ *def* cylinder_1
- \+ *def* d
- \+ *def* f
- \+ *def* g
- \+ *def* mapping_cone
- \+ *def* mapping_cylinder
- \+ *def* mapping_cylinder_0
- \+ *def* pt
- \+ *def* q
- \+ *def* to_pt
- \+ *def* w

Modified src/category_theory/discrete_category.lean


Modified src/category_theory/instances/Top/basic.lean
- \+ *def* category_theory.instances.Top.of

Added src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.binary_cofan.mk
- \+ *abbreviation* category_theory.limits.binary_cofan
- \+ *def* category_theory.limits.binary_fan.mk
- \+ *abbreviation* category_theory.limits.binary_fan
- \+ *def* category_theory.limits.pair
- \+ *def* category_theory.limits.pair_function
- \+ *inductive* category_theory.limits.walking_pair

Added src/category_theory/limits/shapes/default.lean


Added src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cocone.of_cofork
- \+ *lemma* category_theory.limits.cocone.of_cofork_ι
- \+ *def* category_theory.limits.cofork.condition
- \+ *def* category_theory.limits.cofork.of_cocone
- \+ *lemma* category_theory.limits.cofork.of_cocone_ι
- \+ *def* category_theory.limits.cofork.of_π
- \+ *def* category_theory.limits.cofork.π
- \+ *abbreviation* category_theory.limits.cofork
- \+ *def* category_theory.limits.cone.of_fork
- \+ *lemma* category_theory.limits.cone.of_fork_π
- \+ *def* category_theory.limits.fork.condition
- \+ *def* category_theory.limits.fork.of_cone
- \+ *lemma* category_theory.limits.fork.of_cone_π
- \+ *def* category_theory.limits.fork.of_ι
- \+ *lemma* category_theory.limits.fork.of_ι_app_one
- \+ *lemma* category_theory.limits.fork.of_ι_app_zero
- \+ *def* category_theory.limits.fork.ι
- \+ *abbreviation* category_theory.limits.fork
- \+ *def* category_theory.limits.parallel_pair
- \+ *lemma* category_theory.limits.parallel_pair_functor_obj
- \+ *lemma* category_theory.limits.parallel_pair_map_left
- \+ *lemma* category_theory.limits.parallel_pair_map_right
- \+ *inductive* category_theory.limits.walking_parallel_pair
- \+ *def* category_theory.limits.walking_parallel_pair_hom.comp
- \+ *inductive* category_theory.limits.walking_parallel_pair_hom
- \+ *lemma* category_theory.limits.walking_parallel_pair_hom_id

Added src/category_theory/limits/shapes/products.lean
- \+ *def* category_theory.limits.cofan.mk
- \+ *abbreviation* category_theory.limits.cofan
- \+ *def* category_theory.limits.fan.mk
- \+ *abbreviation* category_theory.limits.fan

Added src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.cocone.of_pushout_cocone
- \+ *lemma* category_theory.limits.cocone.of_pushout_cocone_ι
- \+ *def* category_theory.limits.cone.of_pullback_cone
- \+ *lemma* category_theory.limits.cone.of_pullback_cone_π
- \+ *def* category_theory.limits.cospan
- \+ *lemma* category_theory.limits.cospan_left
- \+ *lemma* category_theory.limits.cospan_map_id
- \+ *lemma* category_theory.limits.cospan_map_inl
- \+ *lemma* category_theory.limits.cospan_map_inr
- \+ *lemma* category_theory.limits.cospan_one
- \+ *lemma* category_theory.limits.cospan_right
- \+ *lemma* category_theory.limits.pullback_cone.condition
- \+ *def* category_theory.limits.pullback_cone.mk
- \+ *def* category_theory.limits.pullback_cone.of_cone
- \+ *lemma* category_theory.limits.pullback_cone.of_cone_π
- \+ *def* category_theory.limits.pullback_cone.π₁
- \+ *def* category_theory.limits.pullback_cone.π₂
- \+ *abbreviation* category_theory.limits.pullback_cone
- \+ *lemma* category_theory.limits.pushout_cocone.condition
- \+ *def* category_theory.limits.pushout_cocone.mk
- \+ *def* category_theory.limits.pushout_cocone.of_cocone
- \+ *lemma* category_theory.limits.pushout_cocone.of_cocone_ι
- \+ *def* category_theory.limits.pushout_cocone.ι₁
- \+ *def* category_theory.limits.pushout_cocone.ι₂
- \+ *abbreviation* category_theory.limits.pushout_cocone
- \+ *def* category_theory.limits.span
- \+ *lemma* category_theory.limits.span_left
- \+ *lemma* category_theory.limits.span_map_fst
- \+ *lemma* category_theory.limits.span_map_id
- \+ *lemma* category_theory.limits.span_map_snd
- \+ *lemma* category_theory.limits.span_right
- \+ *lemma* category_theory.limits.span_zero
- \+ *def* category_theory.limits.walking_cospan.hom.comp
- \+ *inductive* category_theory.limits.walking_cospan.hom
- \+ *lemma* category_theory.limits.walking_cospan.hom_id
- \+ *inductive* category_theory.limits.walking_cospan
- \+ *def* category_theory.limits.walking_span.hom.comp
- \+ *inductive* category_theory.limits.walking_span.hom
- \+ *lemma* category_theory.limits.walking_span.hom_id
- \+ *inductive* category_theory.limits.walking_span

Added src/category_theory/sparse.lean
- \+ *def* category_theory.sparse_category

Modified src/tactic/basic.lean




## [2019-05-03 15:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/219cb1a)
chore(travis): disable the check for minimal imports ([#973](https://github.com/leanprover-community/mathlib/pull/973))
#### Estimated changes
Modified .travis.yml




## [2019-05-03 14:11:01+01:00](https://github.com/leanprover-community/mathlib/commit/44386cd)
chore(docs): delete docs/wip.md ([#972](https://github.com/leanprover-community/mathlib/pull/972))
* chore(docs): delete docs/wip.md
long outdated
* remove link in README
#### Estimated changes
Modified README.md


Deleted docs/wip.md




## [2019-05-03 10:59:45](https://github.com/leanprover-community/mathlib/commit/3eb7ebc)
remove code duplication ([#971](https://github.com/leanprover-community/mathlib/pull/971))
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean




## [2019-05-02 22:55:52+01:00](https://github.com/leanprover-community/mathlib/commit/6956daa)
fix(data/polynomial): change instance order in polynomial.subsingleton ([#970](https://github.com/leanprover-community/mathlib/pull/970))
#### Estimated changes
Modified src/data/polynomial.lean




## [2019-05-02 17:32:09](https://github.com/leanprover-community/mathlib/commit/60b3c19)
fix(scripts/remote-install-update-mathlib): apt shouldn't ask ([#969](https://github.com/leanprover-community/mathlib/pull/969))
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh




## [2019-05-02 12:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/d288905)
fix(script/remote-install-update-mathlib) fix answer reading and requests/urllib3 version conflict ([#968](https://github.com/leanprover-community/mathlib/pull/968))
#### Estimated changes
Modified README.md


Modified scripts/remote-install-update-mathlib.sh




## [2019-05-02 08:40:53](https://github.com/leanprover-community/mathlib/commit/8a097f1)
feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms ([#951](https://github.com/leanprover-community/mathlib/pull/951))
* feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms
* Update subgroup.lean
* Update ideal_operations.lean
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* is_group_hom.trivial_ker_iff_eq_one

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* is_ring_hom.inj_iff_ker_eq_bot
- \+ *lemma* is_ring_hom.injective_iff
- \+ *def* is_ring_hom.ker
- \+ *lemma* is_ring_hom.ker_eq
- \+ *lemma* is_ring_hom.ker_eq_bot_iff_eq_zero



## [2019-05-02 08:08:14](https://github.com/leanprover-community/mathlib/commit/ef11fb3)
feat(category_theory/limits/opposites): (co)limits in opposite categories ([#926](https://github.com/leanprover-community/mathlib/pull/926))
* (co)limits in opposite categories
* moving lemmas
* moving stuff about complete lattices to separate PR
* renaming category_of_preorder elsewhere
* build limits functor/shape at a time
* removing stray commas, and making one-liners
* remove non-terminal simps
#### Estimated changes
Modified src/category_theory/const.lean
- \+ *def* category_theory.functor.const.op_obj_op
- \+ *lemma* category_theory.functor.const.op_obj_op_hom_app
- \+ *lemma* category_theory.functor.const.op_obj_op_inv_app
- \+ *def* category_theory.functor.const.op_obj_unop
- \+ *lemma* category_theory.functor.const.op_obj_unop_hom_app
- \+ *lemma* category_theory.functor.const.op_obj_unop_inv_app

Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocone_left_op_of_cone
- \+ *lemma* category_theory.limits.cocone_left_op_of_cone_X
- \+ *lemma* category_theory.limits.cocone_left_op_of_cone_ι_app
- \+ *def* category_theory.limits.cocone_of_cone_left_op
- \+ *lemma* category_theory.limits.cocone_of_cone_left_op_X
- \+ *lemma* category_theory.limits.cocone_of_cone_left_op_ι_app
- \+ *def* category_theory.limits.cone_left_op_of_cocone
- \+ *lemma* category_theory.limits.cone_left_op_of_cocone_X
- \+ *lemma* category_theory.limits.cone_left_op_of_cocone_π_app
- \+ *def* category_theory.limits.cone_of_cocone_left_op
- \+ *lemma* category_theory.limits.cone_of_cocone_left_op_X
- \+ *lemma* category_theory.limits.cone_of_cocone_left_op_π_app

Added src/category_theory/limits/opposites.lean


Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.functor.left_op_map
- \+ *lemma* category_theory.functor.left_op_obj
- \+ *lemma* category_theory.functor.right_op_map
- \+ *lemma* category_theory.functor.right_op_obj
- \+ *lemma* category_theory.nat_trans.left_op_app
- \+ *lemma* category_theory.nat_trans.op_app
- \+ *lemma* category_theory.nat_trans.right_op_app
- \+ *lemma* category_theory.nat_trans.unop_app

Modified src/category_theory/yoneda.lean




## [2019-05-02 04:37:39](https://github.com/leanprover-community/mathlib/commit/69094fc)
fix(tactic/library_search): iff lemmas with universes ([#935](https://github.com/leanprover-community/mathlib/pull/935))
* fix(tactic/library_search): iff lemmas with universes
* cleaning up
* add crossreference
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/library_search.lean


Modified test/library_search/basic.lean
- \+ *def* test.library_search.P
- \+ *def* test.library_search.Q
- \+ *def* test.library_search.f

Added test/library_search/ordered_ring.lean




## [2019-05-02 02:35:03](https://github.com/leanprover-community/mathlib/commit/9b7fb5f)
feat(category_theory/limits): complete lattices have (co)limits ([#931](https://github.com/leanprover-community/mathlib/pull/931))
* feat(category_theory/limits): complete lattices have (co)limits
* Update lattice.lean
#### Estimated changes
Added src/category_theory/limits/lattice.lean




## [2019-05-01 08:53:51-04:00](https://github.com/leanprover-community/mathlib/commit/b3433a5)
feat(script/auth_github): improve messages [ci skip] ([#965](https://github.com/leanprover-community/mathlib/pull/965))
#### Estimated changes
Modified scripts/auth_github.py


