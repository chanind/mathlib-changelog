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
created src/topology/algebra/open_subgroup.lean
- \+ *lemma* ext
- \+ *lemma* ext'
- \+ *lemma* coe_injective
- \+ *lemma* mem_nhds_one
- \+ *lemma* is_open_of_nonempty_open_subset
- \+ *lemma* is_open_of_open_subgroup
- \+ *lemma* is_closed
- \+ *lemma* coe_inf
- \+ *lemma* le_iff
- \+ *lemma* mem_nhds_zero
- \+ *lemma* is_open_of_open_add_subgroup
- \+ *lemma* coe_inf
- \+ *lemma* le_iff
- \+ *lemma* is_open_of_open_submodule
- \+ *lemma* is_open_of_open_subideal
- \+ *def* open_subgroup
- \+ *def* prod
- \+ *def* prod



## [2019-05-31 19:49:44](https://github.com/leanprover-community/mathlib/commit/6237939)
fix(data/nat/enat): change [] to {} in some lemmas ([#1054](https://github.com/leanprover-community/mathlib/pull/1054))
* fix(data/nat/enat): change [] to {} in some lemmas
* Update enat.lean
* remove space
#### Estimated changes
modified src/data/nat/enat.lean
- \+/\- *lemma* to_with_top_top'
- \+/\- *lemma* to_with_top_zero'
- \+/\- *lemma* to_with_top_coe'
- \+/\- *lemma* to_with_top_top'
- \+/\- *lemma* to_with_top_zero'
- \+/\- *lemma* to_with_top_coe'



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
created src/category_theory/monoidal/types.lean
- \+ *def* types_left_unitor
- \+ *def* types_left_unitor_inv
- \+ *def* types_right_unitor
- \+ *def* types_right_unitor_inv
- \+ *def* types_associator
- \+ *def* types_associator_inv
- \+ *def* types_braiding
- \+ *def* types_braiding_inv



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
modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean

renamed src/category_theory/instances/CommRing/adjunctions.lean to src/algebra/CommRing/adjunctions.lean

renamed src/category_theory/instances/CommRing/basic.lean to src/algebra/CommRing/basic.lean
- \+/\- *lemma* id_val
- \+/\- *lemma* comp_val
- \+/\- *lemma* id_val
- \+/\- *lemma* comp_val
- \- *lemma* hom.ext
- \- *lemma* hom_coe_app
- \+/\- *def* CommRing
- \+/\- *def* of
- \+ *def* is_comm_ring_hom
- \+/\- *def* of
- \+/\- *def* Int.cast
- \+/\- *def* Int.hom_unique
- \+/\- *def* CommRing
- \+/\- *def* of
- \- *def* Int
- \+/\- *def* Int.cast
- \+/\- *def* Int.hom_unique
- \- *def* forget

renamed src/category_theory/instances/CommRing/colimits.lean to src/algebra/CommRing/colimits.lean

renamed src/category_theory/instances/CommRing/default.lean to src/algebra/CommRing/default.lean

renamed src/category_theory/instances/CommRing/limits.lean to src/algebra/CommRing/limits.lean

renamed src/category_theory/instances/Mon/basic.lean to src/algebra/Mon/basic.lean
- \+/\- *def* CommMon
- \+ *def* of
- \+ *def* of
- \+/\- *def* CommMon

renamed src/category_theory/instances/Mon/colimits.lean to src/algebra/Mon/colimits.lean

renamed src/category_theory/instances/Mon/default.lean to src/algebra/Mon/default.lean

modified src/algebraic_geometry/presheafed_space.lean

modified src/algebraic_geometry/stalks.lean

modified src/category_theory/concrete_category.lean
- \+/\- *lemma* concrete_category_id
- \+ *lemma* hom_ext
- \+/\- *lemma* concrete_category_id
- \- *lemma* bundled_hom.ext

deleted src/category_theory/instances/Top/default.lean

deleted src/category_theory/instances/TopCommRing/default.lean

renamed src/category_theory/instances/groups.lean to src/group_theory/category.lean
- \+/\- *def* AddCommGroup
- \+ *def* of
- \+ *def* of
- \+/\- *def* AddCommGroup

renamed src/category_theory/instances/measurable_space.lean to src/measure_theory/Meas.lean
- \+ *def* of

renamed src/category_theory/instances/Top/adjunctions.lean to src/topology/Top/adjunctions.lean

renamed src/category_theory/instances/Top/basic.lean to src/topology/Top/basic.lean
- \+/\- *def* of
- \+/\- *def* of

created src/topology/Top/default.lean

renamed src/category_theory/instances/Top/epi_mono.lean to src/topology/Top/epi_mono.lean

renamed src/category_theory/instances/Top/limits.lean to src/topology/Top/limits.lean

renamed src/category_theory/instances/Top/open_nhds.lean to src/topology/Top/open_nhds.lean

renamed src/category_theory/instances/Top/opens.lean to src/topology/Top/opens.lean

renamed src/category_theory/instances/Top/presheaf.lean to src/topology/Top/presheaf.lean

renamed src/category_theory/instances/Top/presheaf_of_functions.lean to src/topology/Top/presheaf_of_functions.lean

renamed src/category_theory/instances/Top/stalks.lean to src/topology/Top/stalks.lean

renamed src/category_theory/instances/TopCommRing/basic.lean to src/topology/algebra/TopCommRing/basic.lean
- \+/\- *def* of
- \+/\- *def* of

created src/topology/algebra/TopCommRing/default.lean



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
created src/category_theory/monoidal/category.lean
- \+ *lemma* inv_tensor
- \+ *lemma* comp_tensor_id
- \+ *lemma* id_tensor_comp
- \+ *lemma* id_tensor_comp_tensor_id
- \+ *lemma* tensor_id_comp_id_tensor
- \+ *lemma* left_unitor_inv_naturality
- \+ *lemma* right_unitor_inv_naturality
- \+ *lemma* tensor_left_iff
- \+ *lemma* tensor_right_iff
- \+ *lemma* left_unitor_product_aux_perimeter
- \+ *lemma* left_unitor_product_aux_triangle
- \+ *lemma* left_unitor_product_aux_square
- \+ *lemma* left_unitor_product_aux
- \+ *lemma* right_unitor_product_aux_perimeter
- \+ *lemma* right_unitor_product_aux_triangle
- \+ *lemma* right_unitor_product_aux_square
- \+ *lemma* right_unitor_product_aux
- \+ *lemma* left_unitor_tensor
- \+ *lemma* left_unitor_tensor_inv
- \+ *lemma* right_unitor_tensor
- \+ *lemma* right_unitor_tensor_inv
- \+ *lemma* associator_inv_naturality
- \+ *lemma* pentagon_inv
- \+ *lemma* triangle_assoc_comp_left
- \+ *lemma* triangle_assoc_comp_right
- \+ *lemma* triangle_assoc_comp_right_inv
- \+ *lemma* triangle_assoc_comp_left_inv
- \+ *lemma* left_assoc_tensor_obj
- \+ *lemma* left_assoc_tensor_map
- \+ *lemma* right_assoc_tensor_obj
- \+ *lemma* right_assoc_tensor_map
- \+ *def* tensor_iso
- \+ *def* tensor
- \+ *def* left_assoc_tensor
- \+ *def* right_assoc_tensor
- \+ *def* tensor_unit_left
- \+ *def* tensor_unit_right
- \+ *def* associator_nat_iso
- \+ *def* left_unitor_nat_iso
- \+ *def* right_unitor_nat_iso

created src/category_theory/monoidal/category_aux.lean
- \+ *def* tensor_obj_type
- \+ *def* tensor_hom_type
- \+ *def* assoc_obj
- \+ *def* assoc_natural
- \+ *def* left_unitor_obj
- \+ *def* left_unitor_natural
- \+ *def* right_unitor_obj
- \+ *def* right_unitor_natural
- \+ *def* pentagon
- \+ *def* triangle

created src/category_theory/monoidal/functor.lean
- \+ *lemma* id_obj
- \+ *lemma* id_map
- \+ *lemma* id_ε
- \+ *lemma* id_μ
- \+ *lemma* comp_obj
- \+ *lemma* comp_map
- \+ *lemma* comp_ε
- \+ *lemma* comp_μ
- \+ *def* monoidal_functor.ε_iso
- \+ *def* monoidal_functor.μ_iso
- \+ *def* μ_nat_iso
- \+ *def* id
- \+ *def* comp
- \+ *def* comp



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
modified src/group_theory/free_abelian_group.lean

created src/ring_theory/free_comm_ring.lean
- \+ *lemma* lift_zero
- \+ *lemma* lift_one
- \+ *lemma* lift_of
- \+ *lemma* lift_add
- \+ *lemma* lift_neg
- \+ *lemma* lift_sub
- \+ *lemma* lift_mul
- \+ *lemma* lift_pow
- \+ *lemma* lift_comp_of
- \+ *lemma* map_zero
- \+ *lemma* map_one
- \+ *lemma* map_of
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_mul
- \+ *lemma* map_pow
- \+ *lemma* coe_eq
- \+ *def* free_comm_ring
- \+ *def* of
- \+ *def* lift
- \+ *def* map
- \+ *def* to_free_comm_ring
- \+ *def* subsingleton_equiv_free_comm_ring
- \+ *def* free_comm_ring_equiv_mv_polynomial_int
- \+ *def* free_comm_ring_pempty_equiv_int
- \+ *def* free_comm_ring_punit_equiv_polynomial_int
- \+ *def* free_ring_pempty_equiv_int
- \+ *def* free_ring_punit_equiv_polynomial_int

created src/ring_theory/free_ring.lean
- \+ *lemma* lift_zero
- \+ *lemma* lift_one
- \+ *lemma* lift_of
- \+ *lemma* lift_add
- \+ *lemma* lift_neg
- \+ *lemma* lift_sub
- \+ *lemma* lift_mul
- \+ *lemma* lift_pow
- \+ *lemma* lift_comp_of
- \+ *lemma* map_zero
- \+ *lemma* map_one
- \+ *lemma* map_of
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_mul
- \+ *lemma* map_pow
- \+ *def* free_ring
- \+ *def* of
- \+ *def* lift
- \+ *def* map



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
modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* as_coe
- \+ *lemma* mk_coe
- \+ *lemma* hom_mk_coe
- \+ *lemma* f_as_coe
- \+ *lemma* id_coe
- \+ *lemma* id_c_app
- \+ *lemma* comp_c_app
- \- *lemma* id_f
- \- *lemma* comp_f

created src/algebraic_geometry/stalks.lean
- \+ *lemma* id
- \+ *lemma* comp
- \+ *def* stalk
- \+ *def* stalk_map

modified src/category_theory/functor_category.lean
- \+ *lemma* flip_obj_obj
- \+ *lemma* flip_map_app

modified src/category_theory/instances/Top/basic.lean

modified src/category_theory/instances/Top/open_nhds.lean
- \+ *lemma* map_obj

modified src/category_theory/instances/Top/opens.lean
- \+ *lemma* map_obj

modified src/category_theory/instances/Top/presheaf.lean

modified src/category_theory/instances/Top/presheaf_of_functions.lean

created src/category_theory/instances/Top/stalks.lean
- \+ *lemma* stalk_functor_obj
- \+ *lemma* id
- \+ *lemma* comp
- \+ *def* stalk_functor
- \+ *def* stalk
- \+ *def* stalk_pushforward

modified src/category_theory/instances/TopCommRing/basic.lean
- \+/\- *def* forget_to_Type_via_Top
- \+/\- *def* forget_to_Type_via_CommRing
- \+/\- *def* forget_to_Type_via_Top
- \+/\- *def* forget_to_Type_via_CommRing

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/natural_isomorphism.lean

modified src/category_theory/natural_transformation.lean

modified src/category_theory/whiskering.lean

modified src/data/opposite.lean



## [2019-05-29 06:03:02](https://github.com/leanprover-community/mathlib/commit/0de4bba)
feat(ordered_group): add missing instance ([#1094](https://github.com/leanprover-community/mathlib/pull/1094))
#### Estimated changes
modified src/algebra/ordered_group.lean
- \+/\- *lemma* neg_neg_iff_pos
- \+/\- *lemma* neg_neg_iff_pos



## [2019-05-28 15:01:35](https://github.com/leanprover-community/mathlib/commit/b20b722)
fix(tactic/rcases): add parse desc to rcases/rintro ([#1091](https://github.com/leanprover-community/mathlib/pull/1091))
#### Estimated changes
modified src/tactic/rcases.lean

modified test/rcases.lean



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
modified src/algebra/group.lean
- \+ *lemma* conj_inv
- \+ *lemma* conj_mul

modified src/group_theory/subgroup.lean
- \+ *lemma* mem_conjugates_self
- \+ *lemma* mem_conjugates_of_set_iff
- \+ *lemma* conjugates_subset
- \+ *lemma* conj_mem_conjugates_of_set
- \+ *lemma* normal_closure_subset_iff
- \+ *theorem* subset_conjugates_of_set
- \+ *theorem* conjugates_of_set_mono
- \+ *theorem* conjugates_of_set_subset
- \+ *theorem* conjugates_of_set_subset_normal_closure
- \+ *theorem* subset_normal_closure
- \+ *theorem* normal_closure_subset
- \+ *theorem* normal_closure_mono
- \+ *def* conjugates
- \+ *def* conjugates_of_set
- \+ *def* normal_closure



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
modified src/set_theory/ordinal.lean
- \+/\- *theorem* well_ordering_thm
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
renamed src/category_theory/adjunction.lean to src/category_theory/adjunction/basic.lean
- \- *def* functoriality_is_left_adjoint
- \- *def* left_adjoint_preserves_colimits
- \- *def* functoriality_is_right_adjoint
- \- *def* right_adjoint_preserves_limits
- \- *def* cocones_iso
- \- *def* cones_iso

created src/category_theory/adjunction/default.lean

created src/category_theory/adjunction/limits.lean
- \+ *def* functoriality_is_left_adjoint
- \+ *def* left_adjoint_preserves_colimits
- \+ *def* functoriality_is_right_adjoint
- \+ *def* right_adjoint_preserves_limits
- \+ *def* cocones_iso
- \+ *def* cones_iso

modified src/category_theory/epi_mono.lean

modified src/category_theory/instances/CommRing/adjunctions.lean
- \- *lemma* hom_coe_app'

modified src/category_theory/instances/CommRing/basic.lean
- \- *def* int.eq_cast'

modified src/category_theory/instances/Top/adjunctions.lean

modified src/category_theory/types.lean
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp

modified src/data/int/basic.lean
- \+ *lemma* eq_cast'

modified src/data/mv_polynomial.lean
- \+ *lemma* hom_C
- \+ *lemma* eval₂_hom_X
- \+/\- *lemma* rename_rename
- \+/\- *lemma* rename_id
- \+ *lemma* eval₂_cast_comp
- \+/\- *lemma* rename_rename
- \+/\- *lemma* rename_id

modified src/tactic/tidy.lean



## [2019-05-23 11:08:00](https://github.com/leanprover-community/mathlib/commit/15fecbd)
doc(finsupp,category_theory): fixes ([#1075](https://github.com/leanprover-community/mathlib/pull/1075))
* doc
* update emb_domain doc string
* typo
#### Estimated changes
modified docs/theories/category_theory.md

modified src/data/finsupp.lean



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
modified src/linear_algebra/basic.lean
- \+ *lemma* to_equiv_injective
- \+ *lemma* ext
- \+ *lemma* general_linear_equiv_to_linear_map
- \+/\- *theorem* coe_apply
- \+/\- *theorem* coe_apply
- \+/\- *def* general_linear_group
- \+ *def* to_linear_equiv
- \+ *def* of_linear_equiv
- \+ *def* general_linear_equiv
- \+/\- *def* general_linear_group



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
modified src/data/nat/basic.lean
- \+ *lemma* eq_zero_of_double_le
- \+ *lemma* eq_zero_of_mul_le
- \+ *lemma* lt_mul_of_div_lt
- \+ *lemma* eq_zero_of_le_div
- \+ *lemma* eq_zero_of_le_half
- \+ *lemma* eq_of_dvd_quot_one
- \+ *lemma* div_le_div_left
- \+ *lemma* div_eq_self



## [2019-05-21 21:29:42](https://github.com/leanprover-community/mathlib/commit/971ddcc)
feat(*): image_closure ([#1069](https://github.com/leanprover-community/mathlib/pull/1069))
Prove that the image of the closure is the closure of the image,
for submonoids/groups/rings.
From the perfectoid project.
#### Estimated changes
modified src/group_theory/subgroup.lean
- \+/\- *lemma* mem_closure
- \+/\- *lemma* closure_subset_iff
- \+ *lemma* image_closure
- \+/\- *lemma* mem_closure
- \+ *lemma* image_closure
- \+/\- *lemma* trivial_eq_closure
- \+/\- *lemma* mem_closure
- \+/\- *lemma* closure_subset_iff
- \+/\- *lemma* mem_closure
- \+/\- *lemma* trivial_eq_closure
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* gpowers_eq_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* gmultiples_eq_closure
- \+/\- *theorem* in_closure.rec_on
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* subset_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *theorem* gpowers_eq_closure
- \+/\- *theorem* closure_subset
- \+/\- *theorem* gmultiples_eq_closure
- \+/\- *theorem* in_closure.rec_on
- \+/\- *theorem* closure_mono
- \+/\- *theorem* exists_list_of_mem_closure
- \+/\- *theorem* mclosure_subset
- \+/\- *theorem* mclosure_inv_subset
- \+/\- *theorem* closure_eq_mclosure
- \+/\- *theorem* mem_closure_union_iff
- \+/\- *def* closure
- \+/\- *def* closure
- \+/\- *def* closure
- \+/\- *def* closure

modified src/group_theory/submonoid.lean
- \+ *lemma* image_closure
- \+ *lemma* image_closure

modified src/ring_theory/subring.lean
- \+ *lemma* image_closure



## [2019-05-21 16:01:07](https://github.com/leanprover-community/mathlib/commit/3461399)
refactor(integration.lean): changing `measure_space` to `measurable_space` ([#1072](https://github.com/leanprover-community/mathlib/pull/1072))
I've been using this file and `range_const` doesn't seem to require the spurious `measure_space` instance. `measurable_space` seems to suffice.
#### Estimated changes
modified src/measure_theory/integration.lean
- \+/\- *lemma* range_const
- \+/\- *lemma* range_const



## [2019-05-20 19:27:04](https://github.com/leanprover-community/mathlib/commit/cb30c97)
feat(algebra/pi_instances): product of submonoids/groups/rings ([#1066](https://github.com/leanprover-community/mathlib/pull/1066))
From the perfectoid project.
#### Estimated changes
modified src/algebra/pi_instances.lean



## [2019-05-20 18:35:19](https://github.com/leanprover-community/mathlib/commit/0ab8a89)
feat(category_theory): limits in CommRing ([#1006](https://github.com/leanprover-community/mathlib/pull/1006))
* feat(category_theory): limits in CommRing
* by
* rename
* sections
* Update src/category_theory/types.lean
Co-Authored-By: Johannes Hölzl <johannes.hoelzl@gmx.de>
#### Estimated changes
modified src/algebra/pi_instances.lean
- \- *def* is_ring_hom_pi

modified src/category_theory/instances/CommRing/basic.lean

created src/category_theory/instances/CommRing/limits.lean
- \+ *def* limit
- \+ *def* limit_is_limit

modified src/category_theory/limits/types.lean

modified src/category_theory/types.lean
- \+ *def* sections



## [2019-05-20 15:36:59](https://github.com/leanprover-community/mathlib/commit/8cf7c4c)
chore(topology/algebra/monoid): continuous_mul_left/right ([#1065](https://github.com/leanprover-community/mathlib/pull/1065))
#### Estimated changes
modified src/topology/algebra/monoid.lean
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
modified src/ring_theory/algebra.lean
- \+ *lemma* id_to_linear_map
- \+ *lemma* comp_to_linear_map



## [2019-05-20 11:52:29](https://github.com/leanprover-community/mathlib/commit/d001abf)
feat(tactic/basic): adds `contrapose` tactic ([#1015](https://github.com/leanprover-community/mathlib/pull/1015))
* feat(tactic/basic): adds `contrapose` tactic
* fix(tactic/push_neg): fix is_prop testing
* Setup error message testing following Rob, add tests for `contrapose`
* refactor(tactic/interactive): move noninteractive success_if_fail_with_msg to tactic/core
#### Estimated changes
modified docs/tactics.md

modified src/tactic/basic.lean

modified src/tactic/core.lean

modified src/tactic/interactive.lean

modified src/tactic/push_neg.lean
- \+ *lemma* imp_of_not_imp_not

modified test/push_neg.lean



## [2019-05-20 11:16:53](https://github.com/leanprover-community/mathlib/commit/15a6af2)
feat(topology/opens): continuous.comap : opens Y → opens X ([#1061](https://github.com/leanprover-community/mathlib/pull/1061))
* feat(topology/opens): continuous.comap : opens Y → opens X
From the perfectoid project.
* Update opens.lean
#### Estimated changes
modified src/topology/opens.lean
- \+ *lemma* comap_id
- \+ *lemma* comap_mono
- \+ *def* comap



## [2019-05-20 09:26:59](https://github.com/leanprover-community/mathlib/commit/d4c7b7a)
feat(tactic/linarith): better input syntax linarith only [...] ([#1056](https://github.com/leanprover-community/mathlib/pull/1056))
* feat(tactic/ring, tactic/linarith): add reducibility parameter
* fix(tactic/ring): interactive parsing for argument to ring1
* feat(tactic/linarith): better input syntax linarith only [...]
* fix(docs/tactics): fix linarith doc
#### Estimated changes
modified docs/tactics.md

modified src/analysis/complex/exponential.lean

modified src/data/complex/exponential.lean

modified src/tactic/core.lean

modified src/tactic/linarith.lean

modified src/tactic/ring.lean

modified test/linarith.lean

modified test/ring.lean



## [2019-05-19 17:40:09](https://github.com/leanprover-community/mathlib/commit/f253401)
refactor: coherent composition order ([#1055](https://github.com/leanprover-community/mathlib/pull/1055))
#### Estimated changes
modified src/analysis/asymptotics.lean

modified src/analysis/complex/exponential.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/deriv.lean

modified src/analysis/specific_limits.lean

modified src/data/padics/hensel.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/decomposition.lean

modified src/order/filter/basic.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/ordered.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/basic.lean
- \+ *theorem* inter_mem_nhds_within
- \+ *theorem* nhds_within_restrict'
- \+/\- *theorem* nhds_within_restrict
- \+/\- *theorem* nhds_within_restrict

modified src/topology/constructions.lean

modified src/topology/instances/complex.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean

modified src/topology/instances/real.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/completion.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/lipschitz.lean

modified src/topology/order.lean
- \+ *lemma* continuous_within_at.comp
- \+ *lemma* continuous_at.comp
- \+/\- *lemma* continuous_on.comp
- \+/\- *lemma* continuous_on.comp

modified src/topology/sequences.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/completion.lean

modified src/topology/uniform_space/separation.lean



## [2019-05-19 13:39:22](https://github.com/leanprover-community/mathlib/commit/cb4c9ee)
refactor(topology/metric/gromov_hausdorff): make Hausdorff_edist irreducible ([#1052](https://github.com/leanprover-community/mathlib/pull/1052))
* refactor(topology/metric/gromov_hausdorff): remove linarith calls
* refactor(topology/metric/hausdorff_dist): make hausdorff_dist irreducible
#### Estimated changes
modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* Hausdorff_edist_def



## [2019-05-19 12:47:56](https://github.com/leanprover-community/mathlib/commit/b9cb69c)
feat(topology/order): make nhds irreducible ([#1043](https://github.com/leanprover-community/mathlib/pull/1043))
* feat(topology/order): make nhds irreducible
* move nhds irreducible to topology.basic
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* nhds_def
- \+ *lemma* le_nhds_iff
- \+ *lemma* nhds_le_of_le

modified src/topology/order.lean



## [2019-05-18 16:36:44-04:00](https://github.com/leanprover-community/mathlib/commit/73c3f71)
feat(tactic/squeeze): remove noise from output ([#1047](https://github.com/leanprover-community/mathlib/pull/1047))
#### Estimated changes
modified src/tactic/squeeze.lean



## [2019-05-18 13:27:57](https://github.com/leanprover-community/mathlib/commit/fa0e757)
refactor(data/complex/exponential): improve trig proofs ([#1041](https://github.com/leanprover-community/mathlib/pull/1041))
* fix(data/complex/exponential): make complex.exp irreducible
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.
* refactor(data/complex/exponential): improve trig proofs
* fix build
* fix(algebra/group): prove lemma for comm_semigroup instead of comm_monoid
#### Estimated changes
modified src/algebra/group.lean

modified src/algebra/group_power.lean
- \+ *theorem* sq_sub_sq

modified src/algebra/ring.lean

modified src/analysis/complex/exponential.lean

modified src/data/complex/basic.lean
- \+/\- *lemma* eq_conj_iff_real
- \+ *lemma* eq_conj_iff_re
- \+ *lemma* I_sq
- \+/\- *lemma* eq_conj_iff_real

modified src/data/complex/exponential.lean
- \+/\- *lemma* of_real_exp_of_real_re
- \+/\- *lemma* of_real_exp
- \+ *lemma* two_sinh
- \+ *lemma* two_cosh
- \+/\- *lemma* sinh_zero
- \+/\- *lemma* sinh_neg
- \+/\- *lemma* sinh_add
- \+/\- *lemma* cosh_zero
- \+/\- *lemma* cosh_neg
- \+/\- *lemma* cosh_add
- \+/\- *lemma* sinh_sub
- \+/\- *lemma* cosh_sub
- \+/\- *lemma* sinh_conj
- \+/\- *lemma* of_real_sinh_of_real_re
- \+/\- *lemma* of_real_sinh
- \+/\- *lemma* sinh_of_real_im
- \+/\- *lemma* sinh_of_real_re
- \+/\- *lemma* cosh_conj
- \+/\- *lemma* of_real_cosh_of_real_re
- \+/\- *lemma* of_real_cosh
- \+/\- *lemma* cosh_of_real_im
- \+/\- *lemma* cosh_of_real_re
- \+/\- *lemma* tanh_eq_sinh_div_cosh
- \+/\- *lemma* tanh_zero
- \+/\- *lemma* tanh_neg
- \+/\- *lemma* tanh_conj
- \+/\- *lemma* of_real_tanh_of_real_re
- \+/\- *lemma* of_real_tanh
- \+/\- *lemma* tanh_of_real_im
- \+/\- *lemma* tanh_of_real_re
- \+ *lemma* cosh_add_sinh
- \+ *lemma* sinh_add_cosh
- \+ *lemma* cosh_sub_sinh
- \+ *lemma* cosh_sq_sub_sinh_sq
- \+ *lemma* two_sin
- \+ *lemma* two_cos
- \+ *lemma* sinh_mul_I
- \+ *lemma* cosh_mul_I
- \+/\- *lemma* sin_of_real_im
- \+/\- *lemma* sin_of_real_re
- \+/\- *lemma* cos_conj
- \+/\- *lemma* cos_of_real_im
- \+/\- *lemma* cos_of_real_re
- \+/\- *lemma* of_real_tan_of_real_re
- \+/\- *lemma* of_real_tan
- \+ *lemma* cos_add_sin_I
- \+ *lemma* cos_sub_sin_I
- \+ *lemma* sin_sq_add_cos_sq
- \+ *lemma* cos_two_mul'
- \+ *lemma* sin_sq_add_cos_sq
- \+ *lemma* sin_sq_le_one
- \+ *lemma* cos_sq_le_one
- \+ *lemma* exp_strict_mono
- \+/\- *lemma* exp_lt_exp
- \+/\- *lemma* exp_le_exp
- \+/\- *lemma* exp_injective
- \+/\- *lemma* of_real_exp_of_real_re
- \+/\- *lemma* of_real_exp
- \+/\- *lemma* sin_of_real_im
- \+/\- *lemma* sin_of_real_re
- \+/\- *lemma* cos_conj
- \+/\- *lemma* cos_of_real_im
- \+/\- *lemma* cos_of_real_re
- \+/\- *lemma* of_real_tan_of_real_re
- \+/\- *lemma* of_real_tan
- \- *lemma* sin_pow_two_add_cos_pow_two
- \+/\- *lemma* sinh_zero
- \+/\- *lemma* sinh_neg
- \+/\- *lemma* sinh_add
- \+/\- *lemma* cosh_zero
- \+/\- *lemma* cosh_neg
- \+/\- *lemma* cosh_add
- \+/\- *lemma* sinh_sub
- \+/\- *lemma* cosh_sub
- \+/\- *lemma* sinh_conj
- \+/\- *lemma* sinh_of_real_im
- \+/\- *lemma* sinh_of_real_re
- \+/\- *lemma* of_real_sinh_of_real_re
- \+/\- *lemma* of_real_sinh
- \+/\- *lemma* cosh_conj
- \+/\- *lemma* cosh_of_real_im
- \+/\- *lemma* cosh_of_real_re
- \+/\- *lemma* of_real_cosh_of_real_re
- \+/\- *lemma* of_real_cosh
- \+/\- *lemma* tanh_eq_sinh_div_cosh
- \+/\- *lemma* tanh_zero
- \+/\- *lemma* tanh_neg
- \+/\- *lemma* tanh_conj
- \+/\- *lemma* tanh_of_real_im
- \+/\- *lemma* tanh_of_real_re
- \+/\- *lemma* of_real_tanh_of_real_re
- \+/\- *lemma* of_real_tanh
- \- *lemma* sin_pow_two_add_cos_pow_two
- \- *lemma* sin_pow_two_le_one
- \- *lemma* cos_pow_two_le_one
- \+/\- *lemma* exp_lt_exp
- \+/\- *lemma* exp_le_exp
- \+/\- *lemma* exp_injective



## [2019-05-17 20:21:42](https://github.com/leanprover-community/mathlib/commit/5e5298b)
feat(adjointify): make definition easier for elaborator ([#1045](https://github.com/leanprover-community/mathlib/pull/1045))
#### Estimated changes
modified src/category_theory/equivalence.lean



## [2019-05-17 18:53:41](https://github.com/leanprover-community/mathlib/commit/45afa86)
fix(topology/stone_cech): faster proof from @PatrickMassot ([#1042](https://github.com/leanprover-community/mathlib/pull/1042))
#### Estimated changes
modified src/topology/stone_cech.lean



## [2019-05-17 17:38:35](https://github.com/leanprover-community/mathlib/commit/901178e)
feat(set_theory/surreal): surreal numbers ([#958](https://github.com/leanprover-community/mathlib/pull/958))
* feat(set_theory/surreal): surreal numbers
* doc(set_theory/surreal): surreal docs
* minor changes in surreal
#### Estimated changes
created src/set_theory/surreal.lean
- \+ *theorem* mk_le_mk
- \+ *theorem* mk_lt_mk
- \+ *theorem* lt_of_le_mk
- \+ *theorem* lt_of_mk_le
- \+ *theorem* mk_lt_of_le
- \+ *theorem* lt_mk_of_le
- \+ *theorem* not_le_lt
- \+ *theorem* not_le
- \+ *theorem* not_lt
- \+ *theorem* le_refl
- \+ *theorem* lt_irrefl
- \+ *theorem* ne_of_lt
- \+ *theorem* le_trans_aux
- \+ *theorem* le_trans
- \+ *theorem* ok_rec
- \+ *theorem* lt_asymm
- \+ *theorem* le_of_lt
- \+ *theorem* lt_iff_le_not_le
- \+ *theorem* equiv_refl
- \+ *theorem* equiv_symm
- \+ *theorem* equiv_trans
- \+ *theorem* le_congr
- \+ *theorem* lt_congr
- \+ *theorem* not_le
- \+ *def* le_lt
- \+ *def* ok
- \+ *def* equiv
- \+ *def* neg
- \+ *def* add
- \+ *def* mul
- \+ *def* inv_val
- \+ *def* inv'
- \+ *def* omega
- \+ *def* surreal.equiv
- \+ *def* surreal
- \+ *def* mk
- \+ *def* lift
- \+ *def* lift₂
- \+ *def* le
- \+ *def* lt



## [2019-05-17 16:13:20](https://github.com/leanprover-community/mathlib/commit/0b35022)
refactor: change variables order in some composition lemmas ([#1035](https://github.com/leanprover-community/mathlib/pull/1035))
#### Estimated changes
modified src/analysis/complex/exponential.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/deriv.lean
- \+ *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \- *theorem* has_fderiv_within_at.comp_has_fderiv_at

modified src/category_theory/concrete_category.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/giry_monad.lean

modified src/measure_theory/integration.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure_space.lean
- \+/\- *lemma* map_map
- \+/\- *lemma* map_map

modified src/topology/algebra/continuous_functions.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/basic.lean
- \+/\- *lemma* continuous.comp
- \+/\- *lemma* continuous.comp

modified src/topology/bounded_continuous_function.lean

modified src/topology/compact_open.lean
- \+/\- *def* induced
- \+/\- *def* induced

modified src/topology/constructions.lean

modified src/topology/instances/complex.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean

modified src/topology/instances/real.lean

modified src/topology/maps.lean
- \+/\- *lemma* embedding_compose
- \+/\- *lemma* embedding_compose

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/completion.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/isometry.lean
- \+/\- *theorem* isometry.comp
- \+/\- *theorem* isometry.comp

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_comp



## [2019-05-17 14:46:24](https://github.com/leanprover-community/mathlib/commit/f633c94)
feat(tactic/basic): add tactic.rewrite, and sort list ([#1039](https://github.com/leanprover-community/mathlib/pull/1039))
#### Estimated changes
modified src/tactic/basic.lean



## [2019-05-17 13:20:21](https://github.com/leanprover-community/mathlib/commit/a6c1f37)
fix(data/complex/exponential): make complex.exp irreducible ([#1040](https://github.com/leanprover-community/mathlib/pull/1040))
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/-T50000.20challenge
Using `ring` (and other tactics) on terms involving `exp` can lead to some unpleasant and unnecessary unfolding.
#### Estimated changes
modified src/data/complex/exponential.lean



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
modified src/algebra/opposites.lean
- \- *theorem* op_inj
- \- *theorem* unop_inj
- \- *theorem* op_unop
- \- *theorem* unop_op
- \- *def* opposite
- \- *def* op
- \- *def* unop

modified src/category_theory/adjunction.lean

modified src/category_theory/const.lean

modified src/category_theory/discrete_category.lean

modified src/category_theory/eq_to_hom.lean

modified src/category_theory/instances/Top/open_nhds.lean

modified src/category_theory/instances/Top/opens.lean

modified src/category_theory/instances/Top/presheaf.lean

modified src/category_theory/instances/Top/presheaf_of_functions.lean

modified src/category_theory/limits/cones.lean

modified src/category_theory/limits/limits.lean

modified src/category_theory/limits/opposites.lean

modified src/category_theory/opposites.lean
- \- *lemma* unop_op
- \- *lemma* op_unop
- \- *lemma* op_inj
- \- *lemma* unop_inj
- \- *def* opposite
- \- *def* op
- \- *def* unop
- \- *def* op_induction

modified src/category_theory/yoneda.lean

created src/data/opposite.lean
- \+ *lemma* op_inj
- \+ *lemma* unop_inj
- \+ *lemma* op_unop
- \+ *lemma* unop_op
- \+ *def* opposite
- \+ *def* op
- \+ *def* unop
- \+ *def* op_induction



## [2019-05-17 00:16:39](https://github.com/leanprover-community/mathlib/commit/def48b0)
feat(data/nat/basic): make decreasing induction eliminate to Sort ([#1032](https://github.com/leanprover-community/mathlib/pull/1032))
* add interface for decreasing_induction to Sort
* make decreasing_induction a def
* add simp tags and explicit type
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* decreasing_induction_self
- \+ *lemma* decreasing_induction_succ
- \+ *lemma* decreasing_induction_succ'
- \+ *lemma* decreasing_induction_trans
- \+ *lemma* decreasing_induction_succ_left
- \- *lemma* decreasing_induction
- \+ *theorem* le_rec_on_succ_left
- \+ *def* decreasing_induction



## [2019-05-16 12:58:27](https://github.com/leanprover-community/mathlib/commit/ad0f42d)
fix(data/nat/enat): Fix typo in lemma name ([#1037](https://github.com/leanprover-community/mathlib/pull/1037))
#### Estimated changes
modified src/data/nat/enat.lean
- \+ *lemma* coe_ne_top
- \- *lemma* coe_ne_bot



## [2019-05-16 07:24:12](https://github.com/leanprover-community/mathlib/commit/c75c096)
chore(*): reduce imports ([#1033](https://github.com/leanprover-community/mathlib/pull/1033))
* chore(*): reduce imports
* restoring import in later file
* fix import
#### Estimated changes
modified src/data/holor.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* tendsto_at_top_at_bot
- \+/\- *lemma* hyperfilter_le_cofinite
- \+/\- *lemma* is_ultrafilter_hyperfilter
- \+/\- *lemma* tendsto_at_top_at_bot
- \+/\- *lemma* hyperfilter_le_cofinite
- \+/\- *lemma* is_ultrafilter_hyperfilter

modified src/order/filter/filter_product.lean

modified src/order/filter/partial.lean

modified src/topology/algebra/monoid.lean



## [2019-05-15 17:08:22](https://github.com/leanprover-community/mathlib/commit/b5aae18)
feat(category_theory): monos and epis in Type and Top ([#1030](https://github.com/leanprover-community/mathlib/pull/1030))
* feat(category_theory): monos and epis in Type and Top
* imports
* add file header
* use notation for adjunction
#### Estimated changes
created src/category_theory/epi_mono.lean
- \+ *lemma* left_adjoint_preserves_epi
- \+ *lemma* right_adjoint_preserves_mono
- \+ *lemma* faithful_reflects_epi
- \+ *lemma* faithful_reflects_mono

modified src/category_theory/instances/Top/default.lean

created src/category_theory/instances/Top/epi_mono.lean
- \+ *lemma* epi_iff_surjective
- \+ *lemma* mono_iff_injective

modified src/category_theory/types.lean
- \+ *lemma* hom_of_element_eq_iff
- \+ *lemma* mono_iff_injective
- \+ *lemma* epi_iff_surjective
- \+ *def* hom_of_element



## [2019-05-15 13:26:27](https://github.com/leanprover-community/mathlib/commit/136e67a)
refactor(topology): change continuous_at_within to continuous_within_at ([#1034](https://github.com/leanprover-community/mathlib/pull/1034))
#### Estimated changes
modified src/analysis/normed_space/deriv.lean
- \+ *lemma* differentiable_within_at.continuous_within_at
- \- *lemma* differentiable_within_at.continuous_at_within
- \+ *theorem* has_fderiv_within_at.continuous_within_at
- \- *theorem* has_fderiv_within_at.continuous_at_within

modified src/topology/basic.lean
- \+ *def* continuous_within_at
- \+/\- *def* continuous_on
- \- *def* continuous_at_within
- \+/\- *def* continuous_on

modified src/topology/constructions.lean
- \+ *lemma* continuous_within_at.prod
- \- *lemma* continuous_at_within.prod

modified src/topology/order.lean
- \+ *lemma* continuous_within_at.mono
- \+ *lemma* continuous_at.continuous_within_at
- \- *lemma* continuous_at_within.mono
- \- *lemma* continuous_at.continuous_at_within
- \+ *theorem* continuous_within_at_univ
- \+ *theorem* continuous_within_at_iff_continuous_at_restrict
- \+ *theorem* continuous_within_at.tendsto_nhds_within_image
- \+/\- *theorem* nhds_within_le_comap
- \+ *theorem* continuous_within_at_iff_ptendsto_res
- \- *theorem* continuous_at_within_univ
- \- *theorem* continuous_at_within_iff_continuous_at_restrict
- \- *theorem* continuous_at_within.tendsto_nhds_within_image
- \+/\- *theorem* nhds_within_le_comap
- \- *theorem* continuous_at_within_iff_ptendsto_res



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
modified src/tactic/core.lean

created test/terminal_goal.lean
- \+ *lemma* test_terminal_goal_2
- \+ *def* test_terminal_goal_1
- \+ *def* test_terminal_goal_3
- \+ *def* f
- \+ *def* test_terminal_goal_4
- \+ *def* test_subsingleton_goal_1
- \+ *def* test_subsingleton_goal_2



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
modified src/category_theory/adjunction.lean
- \+/\- *def* mk_of_hom_equiv
- \+/\- *def* mk_of_unit_counit
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* adjunction_of_equiv_left
- \+/\- *def* adjunction_of_equiv_right
- \+ *def* to_adjunction
- \+/\- *def* mk_of_hom_equiv
- \+/\- *def* mk_of_unit_counit
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* adjunction_of_equiv_left
- \+/\- *def* adjunction_of_equiv_right

modified src/category_theory/category.lean
- \+/\- *lemma* category.assoc_symm
- \+/\- *lemma* category.assoc_symm

modified src/category_theory/const.lean

modified src/category_theory/currying.lean

modified src/category_theory/discrete_category.lean
- \+ *lemma* id_def
- \+ *def* of_homs
- \+ *def* of_isos

modified src/category_theory/elements.lean

modified src/category_theory/equivalence.lean
- \+ *lemma* unit_def
- \+ *lemma* counit_def
- \+ *lemma* unit_inv_def
- \+ *lemma* counit_inv_def
- \+ *lemma* functor_unit_comp
- \+ *lemma* counit_inv_functor_comp
- \+ *lemma* functor_unit
- \+ *lemma* counit_functor
- \+ *lemma* unit_inverse_comp
- \+ *lemma* inverse_counit_inv_comp
- \+ *lemma* unit_inverse
- \+ *lemma* inverse_counit
- \+/\- *lemma* fun_inv_map
- \+ *lemma* adjointify_η_ε
- \+ *lemma* fun_inv_id_assoc_hom_app
- \+ *lemma* fun_inv_id_assoc_inv_app
- \+ *lemma* inv_fun_id_assoc_hom_app
- \+ *lemma* inv_fun_id_assoc_inv_app
- \+/\- *lemma* fun_inv_map
- \+ *def* unit
- \+ *def* counit
- \+ *def* unit_inv
- \+ *def* counit_inv
- \+ *def* adjointify_η
- \+/\- *def* refl
- \+/\- *def* symm
- \+ *def* fun_inv_id_assoc
- \+ *def* inv_fun_id_assoc
- \+/\- *def* as_equivalence
- \+/\- *def* fun_inv_id
- \+/\- *def* inv_fun_id
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* fun_inv_id
- \+/\- *def* inv_fun_id
- \+/\- *def* as_equivalence

modified src/category_theory/fully_faithful.lean

modified src/category_theory/functor.lean

modified src/category_theory/functor_category.lean
- \+ *lemma* vcomp_eq_comp
- \+ *lemma* congr_app
- \+ *lemma* hcomp_app
- \+ *lemma* exchange
- \+ *def* hcomp

modified src/category_theory/instances/CommRing/adjunctions.lean

modified src/category_theory/instances/Top/adjunctions.lean
- \+/\- *def* adj₁
- \+/\- *def* adj₂
- \+/\- *def* adj₁
- \+/\- *def* adj₂

modified src/category_theory/isomorphism.lean
- \+ *lemma* inv_eq_inv
- \+ *lemma* hom_comp_eq_id
- \+ *lemma* comp_hom_eq_id
- \+ *lemma* hom_eq_inv
- \+ *lemma* is_iso.inv_eq_inv

modified src/category_theory/limits/cones.lean
- \+ *lemma* ext_hom_hom
- \+ *lemma* ext_hom_hom
- \+ *def* postcompose_comp
- \+ *def* postcompose_id
- \+ *def* postcompose_equivalence
- \+ *def* precompose_comp
- \+ *def* precompose_id
- \+ *def* precompose_equivalence

modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_pre
- \+/\- *lemma* limit.map_pre'
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.pre_map
- \+/\- *lemma* colimit.pre_map'
- \+/\- *lemma* limit.pre_post
- \+/\- *lemma* limit.map_pre
- \+/\- *lemma* limit.map_pre'
- \+/\- *lemma* colimit.pre_post
- \+/\- *lemma* colimit.pre_map
- \+/\- *lemma* colimit.pre_map'
- \+ *def* has_limit_of_iso
- \+ *def* has_limit_of_equivalence_comp
- \+ *def* has_limits_of_shape_of_equivalence
- \+ *def* has_colimit_of_iso
- \+ *def* has_colimit_of_equivalence_comp
- \+ *def* has_colimits_of_shape_of_equivalence

modified src/category_theory/limits/opposites.lean

modified src/category_theory/limits/shapes/products.lean

modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* trans_app
- \+/\- *lemma* app_hom
- \+/\- *lemma* app_inv
- \- *lemma* comp_app
- \+/\- *lemma* app_hom
- \+/\- *lemma* app_inv
- \+ *def* iso.app
- \+ *def* is_iso_of_is_iso_app
- \+ *def* hcomp
- \- *def* app

modified src/category_theory/natural_transformation.lean
- \+ *lemma* id_app'
- \+/\- *lemma* ext
- \+/\- *lemma* vcomp_app
- \- *lemma* id_app
- \+/\- *lemma* ext
- \- *lemma* congr_app
- \+/\- *lemma* vcomp_app
- \- *lemma* vcomp_assoc
- \- *lemma* hcomp_app
- \- *lemma* exchange
- \- *def* hcomp

modified src/category_theory/products/associator.lean
- \+/\- *def* associativity
- \+/\- *def* associativity

modified src/category_theory/products/default.lean

modified src/category_theory/whiskering.lean

modified src/category_theory/yoneda.lean



## [2019-05-14 18:15:35](https://github.com/leanprover-community/mathlib/commit/ae8f197)
feat(data/nat/basic): decreasing induction ([#1031](https://github.com/leanprover-community/mathlib/pull/1031))
* feat(data/nat/basic): decreasing induction
* feat(data/nat/basic): better proof of decreasing induction
#### Estimated changes
modified src/data/nat/basic.lean
- \+/\- *lemma* zero_max
- \+/\- *lemma* lt_iff_add_one_le
- \+ *lemma* decreasing_induction
- \+/\- *lemma* zero_max
- \+/\- *lemma* lt_iff_add_one_le



## [2019-05-14 14:46:29](https://github.com/leanprover-community/mathlib/commit/e7b64c5)
feat(data/equiv/functor): map_equiv ([#1026](https://github.com/leanprover-community/mathlib/pull/1026))
* feat(data/equiv/functor): map_equiv
* golf proofs
#### Estimated changes
created src/data/equiv/functor.lean
- \+ *def* functor.map_equiv



## [2019-05-14 15:06:32+02:00](https://github.com/leanprover-community/mathlib/commit/02857d5)
fix(docs/tactics): fix layout, remove noise
#### Estimated changes
modified docs/tactics.md



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
modified docs/tactics.md

modified src/algebra/char_zero.lean
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_inj

modified src/algebra/group_power.lean
- \+/\- *theorem* nat.cast_pow
- \+/\- *theorem* int.coe_nat_pow
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* nat.cast_pow
- \+/\- *theorem* int.coe_nat_pow
- \+/\- *theorem* int.cast_pow

modified src/data/complex/basic.lean
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* of_real_one
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* of_real_fpow
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* abs_cast_nat
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* of_real_one
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* of_real_fpow
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* abs_cast_nat
- \+/\- *theorem* of_real_inj
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_rat_cast
- \+/\- *theorem* of_real_inj
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_rat_cast

modified src/data/int/basic.lean
- \+/\- *theorem* coe_nat_le
- \+/\- *theorem* coe_nat_lt
- \+/\- *theorem* coe_nat_inj'
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* coe_nat_div
- \+/\- *theorem* coe_nat_dvd
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_neg_succ_of_nat
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_sub_nat_nat
- \+/\- *theorem* cast_neg_of_nat
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_mul
- \+ *theorem* coe_nat_bit0
- \+ *theorem* coe_nat_bit1
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* coe_nat_le
- \+/\- *theorem* coe_nat_lt
- \+/\- *theorem* coe_nat_inj'
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* coe_nat_div
- \+/\- *theorem* coe_nat_dvd
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_neg_succ_of_nat
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_sub_nat_nat
- \+/\- *theorem* cast_neg_of_nat
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

modified src/data/nat/cast.lean
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_pred
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_pred
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast

modified src/data/nat/enat.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_get
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_get
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe

modified src/data/padics/padic_integers.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* cast_pow
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* cast_pow

modified src/data/padics/padic_norm.lean

modified src/data/padics/padic_numbers.lean
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_mul
- \+ *lemma* coe_sub
- \+ *lemma* coe_div
- \+ *lemma* coe_one
- \+ *lemma* coe_zero
- \+ *lemma* coe_inj
- \+/\- *lemma* eq_padic_norm
- \+/\- *lemma* eq_padic_norm

modified src/data/rat.lean
- \+/\- *theorem* cast_coe_int
- \+/\- *theorem* coe_int_num
- \+/\- *theorem* coe_int_denom
- \+/\- *theorem* coe_nat_num
- \+/\- *theorem* coe_nat_denom
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_mk_of_ne_zero
- \+/\- *theorem* cast_add_of_ne_zero
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub_of_ne_zero
- \+/\- *theorem* cast_mul_of_ne_zero
- \+/\- *theorem* cast_inv_of_ne_zero
- \+/\- *theorem* cast_div_of_ne_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* cast_coe_int
- \+/\- *theorem* coe_int_num
- \+/\- *theorem* coe_int_denom
- \+/\- *theorem* coe_nat_num
- \+/\- *theorem* coe_nat_denom
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_mk_of_ne_zero
- \+/\- *theorem* cast_add_of_ne_zero
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub_of_ne_zero
- \+/\- *theorem* cast_mul_of_ne_zero
- \+/\- *theorem* cast_inv_of_ne_zero
- \+/\- *theorem* cast_div_of_ne_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

modified src/ring_theory/multiplicity.lean
- \+ *theorem* nat.find_le
- \+ *theorem* int.coe_nat_multiplicity

created src/tactic/norm_cast.lean
- \+ *lemma* ge_from_le
- \+ *lemma* gt_from_lt
- \+ *lemma* ne_from_not_eq
- \+ *lemma* ite_cast

created test/norm_cast.lean



## [2019-05-14 11:13:33](https://github.com/leanprover-community/mathlib/commit/fe19bdb)
fix(data/multiset): remove duplicate setoid instance ([#1027](https://github.com/leanprover-community/mathlib/pull/1027))
* fix(data/multiset): remove duplicate setoid instance
* s/ : Type uu//
#### Estimated changes
modified src/data/list/perm.lean
- \+/\- *theorem* perm.eqv
- \+/\- *theorem* perm.eqv

modified src/data/multiset.lean
- \+ *def* subsingleton_equiv



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
modified src/analysis/asymptotics.lean
- \+ *lemma* is_O.prod_rightl
- \+ *lemma* is_O.prod_rightr
- \+ *lemma* is_o.prod_rightl
- \+ *lemma* is_o.prod_rightr
- \+ *theorem* is_O_prod_left
- \+ *theorem* is_o_prod_left
- \+ *theorem* is_O_one_of_tendsto

modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero
- \+/\- *lemma* tendsto_zero_iff_norm_tendsto_zero

modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* is_bounded_linear_map_prod_iso
- \+ *lemma* bounded_linear_map.is_bounded_linear_map_comp_left
- \+ *lemma* bounded_linear_map.is_bounded_linear_map_comp_right
- \+ *lemma* is_bounded_bilinear_map.map_sub_left
- \+ *lemma* is_bounded_bilinear_map.map_sub_right
- \+ *lemma* is_bounded_bilinear_map_smul
- \+ *lemma* is_bounded_bilinear_map_mul
- \+ *lemma* is_bounded_bilinear_map_comp
- \+ *lemma* is_bounded_bilinear_map.is_bounded_linear_map_deriv
- \+ *def* is_bounded_bilinear_map.deriv

modified src/analysis/normed_space/deriv.lean
- \+ *lemma* tangent_cone_univ
- \+ *lemma* tangent_cone_mono
- \+ *lemma* tangent_cone_at.lim_zero
- \+ *lemma* tangent_cone_inter_open
- \+ *lemma* unique_diff_within_univ_at
- \+ *lemma* unique_diff_within_at_inter
- \+ *lemma* is_open.unique_diff_within_at
- \+ *lemma* unique_diff_on_inter
- \+ *lemma* is_open.unique_diff_on
- \+ *lemma* has_fderiv_within_at.differentiable_within_at
- \+ *lemma* has_fderiv_at.differentiable_at
- \+ *lemma* differentiable_within_at.has_fderiv_within_at
- \+ *lemma* differentiable_at.has_fderiv_at
- \+ *lemma* differentiable_within_at.mono
- \+ *lemma* differentiable_within_univ_at
- \+ *lemma* has_fderiv_within_univ_at
- \+ *lemma* differentiable_at.differentiable_within_at
- \+ *lemma* differentiable_within_at.differentiable_at'
- \+ *lemma* differentiable_within_at.differentiable_at
- \+ *lemma* has_fderiv_within_at.fderiv_within
- \+ *lemma* has_fderiv_at.fderiv
- \+ *lemma* differentiable.fderiv_within
- \+ *lemma* differentiable_on.mono
- \+ *lemma* differentiable_on_univ
- \+ *lemma* differentiable.differentiable_on
- \+ *lemma* fderiv_within_univ
- \+ *lemma* differentiable_within_at_inter
- \+ *lemma* differentiable_on_of_locally_differentiable_on
- \+ *lemma* has_fderiv_at_filter.congr'
- \+ *lemma* has_fderiv_within_at.congr_mono
- \+ *lemma* differentiable_within_at.congr_mono
- \+ *lemma* differentiable_at.congr
- \+ *lemma* differentiable_on.congr_mono
- \+ *lemma* differentiable.congr
- \+ *lemma* differentiable.congr'
- \+ *lemma* differentiable_within_at.fderiv_within_congr_mono
- \+ *lemma* differentiable_at.fderiv_congr
- \+ *lemma* differentiable_at.fderiv_congr'
- \+ *lemma* differentiable_at_id
- \+ *lemma* differentiable_within_at_id
- \+ *lemma* differentiable_id
- \+ *lemma* differentiable_on_id
- \+ *lemma* fderiv_id
- \+ *lemma* fderiv_within_id
- \+ *lemma* differentiable_at_const
- \+ *lemma* differentiable_within_at_const
- \+ *lemma* fderiv_const
- \+ *lemma* fderiv_within_const
- \+ *lemma* differentiable_const
- \+ *lemma* differentiable_on_const
- \+ *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \+ *lemma* is_bounded_linear_map.has_fderiv_within_at
- \+ *lemma* is_bounded_linear_map.has_fderiv_at
- \+ *lemma* is_bounded_linear_map.differentiable_at
- \+ *lemma* is_bounded_linear_map.differentiable_within_at
- \+ *lemma* is_bounded_linear_map.fderiv
- \+ *lemma* is_bounded_linear_map.fderiv_within
- \+ *lemma* is_bounded_linear_map.differentiable
- \+ *lemma* is_bounded_linear_map.differentiable_on
- \+ *lemma* differentiable_within_at.smul
- \+ *lemma* differentiable_at.smul
- \+ *lemma* differentiable_on.smul
- \+ *lemma* differentiable.smul
- \+ *lemma* fderiv_within_smul
- \+ *lemma* fderiv_smul
- \+ *lemma* differentiable_within_at.add
- \+ *lemma* differentiable_at.add
- \+ *lemma* differentiable_on.add
- \+ *lemma* differentiable.add
- \+ *lemma* fderiv_within_add
- \+ *lemma* fderiv_add
- \+ *lemma* differentiable_within_at.neg
- \+ *lemma* differentiable_at.neg
- \+ *lemma* differentiable_on.neg
- \+ *lemma* differentiable.neg
- \+ *lemma* fderiv_within_neg
- \+ *lemma* fderiv_neg
- \+ *lemma* differentiable_within_at.sub
- \+ *lemma* differentiable_at.sub
- \+ *lemma* differentiable_on.sub
- \+ *lemma* differentiable.sub
- \+ *lemma* fderiv_within_sub
- \+ *lemma* fderiv_sub
- \+ *lemma* differentiable_within_at.continuous_at_within
- \+ *lemma* differentiable_at.continuous_at
- \+ *lemma* differentiable_on.continuous_on
- \+ *lemma* differentiable.continuous
- \+ *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+ *lemma* is_bounded_bilinear_map.has_fderiv_within_at
- \+ *lemma* is_bounded_bilinear_map.differentiable_at
- \+ *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+ *lemma* is_bounded_bilinear_map.fderiv
- \+ *lemma* is_bounded_bilinear_map.fderiv_within
- \+ *lemma* is_bounded_bilinear_map.differentiable
- \+ *lemma* is_bounded_bilinear_map.differentiable_on
- \+ *lemma* is_bounded_bilinear_map.continuous
- \+ *lemma* has_fderiv_at_filter.prod
- \+ *lemma* has_fderiv_within_at.prod
- \+ *lemma* has_fderiv_at.prod
- \+ *lemma* differentiable_within_at.prod
- \+ *lemma* differentiable_at.prod
- \+ *lemma* differentiable_on.prod
- \+ *lemma* differentiable.prod
- \+ *lemma* differentiable_at.fderiv_prod
- \+ *lemma* differentiable_at.fderiv_within_prod
- \+ *lemma* differentiable_within_at.comp
- \+ *lemma* differentiable_at.comp
- \+ *lemma* fderiv_within.comp
- \+ *lemma* fderiv.comp
- \+ *lemma* differentiable_on.comp
- \+ *lemma* differentiable_within_at.smul'
- \+ *lemma* differentiable_at.smul'
- \+ *lemma* differentiable_on.smul'
- \+ *lemma* differentiable.smul'
- \+ *lemma* fderiv_within_smul'
- \+ *lemma* fderiv_smul'
- \+ *lemma* differentiable_within_at.mul
- \+ *lemma* differentiable_at.mul
- \+ *lemma* differentiable_on.mul
- \+ *lemma* differentiable.mul
- \+ *lemma* fderiv_within_mul
- \+ *lemma* fderiv_mul
- \- *lemma* fderiv_at_filter_unique
- \+ *theorem* unique_diff_within_at.eq
- \+ *theorem* unique_diff_on.eq
- \+ *theorem* has_fderiv_within_at_iff_tendsto
- \+/\- *theorem* has_fderiv_at_iff_tendsto
- \+/\- *theorem* has_fderiv_at_filter.mono
- \+ *theorem* has_fderiv_within_at.mono
- \+ *theorem* has_fderiv_at.has_fderiv_at_filter
- \+ *theorem* has_fderiv_at.has_fderiv_within_at
- \+ *theorem* has_fderiv_at_unique
- \+ *theorem* has_fderiv_within_at_congr
- \+ *theorem* has_fderiv_within_at.congr
- \+ *theorem* has_fderiv_within_at_id
- \+ *theorem* has_fderiv_within_at_const
- \+ *theorem* has_fderiv_at_filter.smul
- \+ *theorem* has_fderiv_within_at.smul
- \+ *theorem* has_fderiv_at.smul
- \+ *theorem* has_fderiv_at_filter.add
- \+ *theorem* has_fderiv_within_at.add
- \+ *theorem* has_fderiv_at.add
- \+ *theorem* has_fderiv_at_filter.neg
- \+ *theorem* has_fderiv_within_at.neg
- \+ *theorem* has_fderiv_at.neg
- \+ *theorem* has_fderiv_at_filter.sub
- \+ *theorem* has_fderiv_within_at.sub
- \+ *theorem* has_fderiv_at.sub
- \+ *theorem* has_fderiv_within_at.continuous_at_within
- \+ *theorem* has_fderiv_within_at.comp
- \+ *theorem* has_fderiv_within_at.comp_has_fderiv_at
- \+ *theorem* has_fderiv_within_at.smul'
- \+ *theorem* has_fderiv_at.smul'
- \+ *theorem* has_fderiv_within_at.mul
- \+ *theorem* has_fderiv_at.mul
- \- *theorem* has_fderiv_at_within_iff_tendsto
- \+/\- *theorem* has_fderiv_at_iff_tendsto
- \+/\- *theorem* has_fderiv_at_filter.mono
- \- *theorem* has_fderiv_at_within.mono
- \- *theorem* has_fderiv_at_filter_of_has_fderiv_at
- \- *theorem* has_fderiv_at_within_of_has_fderiv_at
- \- *theorem* has_fderiv_at_within_congr
- \- *theorem* has_fderiv_at_within.congr
- \- *theorem* has_fderiv_at_within_id
- \- *theorem* has_fderiv_at_within_const
- \- *theorem* has_fderiv_at_filter_smul
- \- *theorem* has_fderiv_at_within_smul
- \- *theorem* has_fderiv_at_smul
- \- *theorem* has_fderiv_at_filter_add
- \- *theorem* has_fderiv_at_within_add
- \- *theorem* has_fderiv_at_add
- \- *theorem* has_fderiv_at_filter_neg
- \- *theorem* has_fderiv_at_within_neg
- \- *theorem* has_fderiv_at_neg
- \- *theorem* has_fderiv_at_filter_sub
- \- *theorem* has_fderiv_at_within_sub
- \- *theorem* has_fderiv_at_sub
- \- *theorem* has_fderiv_at_within.continuous_at_within
- \- *theorem* has_fderiv_at_within.comp
- \- *theorem* fderiv_at_unique
- \- *theorem* fderiv_at_within_open_unique
- \+/\- *def* has_fderiv_at_filter
- \+ *def* has_fderiv_within_at
- \+/\- *def* has_fderiv_at
- \+ *def* differentiable_within_at
- \+ *def* differentiable_at
- \+ *def* fderiv_within
- \+ *def* fderiv
- \+ *def* differentiable_on
- \+ *def* differentiable
- \+ *def* tangent_cone_at
- \+ *def* unique_diff_within_at
- \+ *def* unique_diff_on
- \+/\- *def* has_fderiv_at_filter
- \- *def* has_fderiv_at_within
- \+/\- *def* has_fderiv_at

modified src/analysis/normed_space/operator_norm.lean
- \+ *def* prod
- \+ *def* scalar_prod_space_iso

modified src/linear_algebra/basic.lean
- \+ *lemma* is_linear_map_prod_iso
- \+ *def* prod
- \+ *def* scalar_prod_space_iso

modified src/topology/constructions.lean
- \+ *lemma* continuous_at_within.prod
- \+ *lemma* continuous_at.prod
- \+ *lemma* continuous_on.prod
- \+/\- *lemma* continuous_inclusion
- \+/\- *lemma* continuous_inclusion

modified src/topology/order.lean
- \+ *lemma* continuous_at_within.mono
- \+ *lemma* continuous_on.congr_mono
- \+ *lemma* continuous_at.continuous_at_within
- \+ *lemma* continuous_on.comp
- \+ *lemma* continuous_on.mono
- \+ *lemma* continuous.continuous_on
- \+ *lemma* continuous_on_const
- \+ *lemma* continuous_on.preimage_open_of_open
- \+ *lemma* continuous_on.preimage_interior_subset_interior_preimage
- \+ *lemma* continuous_on_of_locally_continuous_on
- \+ *def* continuous_iff_continuous_on_univ



## [2019-05-14 07:24:40](https://github.com/leanprover-community/mathlib/commit/a72641b)
squeeze_simp ([#1019](https://github.com/leanprover-community/mathlib/pull/1019))
#### Estimated changes
modified src/algebra/group_power.lean

modified src/algebra/pi_instances.lean

modified src/category_theory/equivalence.lean

modified src/category_theory/whiskering.lean

modified src/category_theory/yoneda.lean

modified src/data/fin.lean

modified src/data/semiquot.lean

modified src/data/set/intervals.lean



## [2019-05-14 05:35:17](https://github.com/leanprover-community/mathlib/commit/cefb9d4)
feat(category_theory/opposites): iso.op ([#1021](https://github.com/leanprover-community/mathlib/pull/1021))
#### Estimated changes
modified src/category_theory/opposites.lean
- \+ *lemma* op_hom
- \+ *lemma* op_inv



## [2019-05-14 01:23:18](https://github.com/leanprover-community/mathlib/commit/6dc0682)
feat(algebra/order_functions): generalize strict_mono.monotone ([#1022](https://github.com/leanprover-community/mathlib/pull/1022))
#### Estimated changes
modified src/algebra/order_functions.lean
- \+/\- *lemma* monotone
- \+/\- *lemma* monotone



## [2019-05-13 23:54:13](https://github.com/leanprover-community/mathlib/commit/07ba43e)
feat(topology/constructions): topology of sum types ([#1016](https://github.com/leanprover-community/mathlib/pull/1016))
#### Estimated changes
modified src/data/sigma/basic.lean
- \+ *lemma* injective_sigma_mk
- \+ *lemma* injective_sigma_map

modified src/topology/constructions.lean
- \+ *lemma* continuous_sigma_mk
- \+ *lemma* is_open_sigma_iff
- \+ *lemma* is_closed_sigma_iff
- \+ *lemma* is_open_map_sigma_mk
- \+ *lemma* is_open_range_sigma_mk
- \+ *lemma* is_closed_map_sigma_mk
- \+ *lemma* is_closed_sigma_mk
- \+ *lemma* closed_embedding_sigma_mk
- \+ *lemma* embedding_sigma_mk
- \+ *lemma* continuous_sigma
- \+ *lemma* continuous_sigma_map
- \+ *lemma* embedding_sigma_map

modified src/topology/maps.lean
- \- *lemma* is_open_singleton_true
- \- *lemma* continuous_Prop

modified src/topology/order.lean
- \+ *lemma* is_open_singleton_true
- \+ *lemma* continuous_Prop
- \+ *lemma* is_open_infi_iff
- \+ *lemma* is_closed_infi_iff



## [2019-05-13 22:28:23](https://github.com/leanprover-community/mathlib/commit/f8385b1)
feat(data/equiv/basic): equiv.nonempty_iff_nonempty ([#1020](https://github.com/leanprover-community/mathlib/pull/1020))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* nonempty_iff_nonempty



## [2019-05-13 20:36:11](https://github.com/leanprover-community/mathlib/commit/01b345c)
feat(tactics/interactive): choose uses exists_prop ([#1014](https://github.com/leanprover-community/mathlib/pull/1014))
* feat(tactics/interactive): choose uses exists_prop
* fix build
#### Estimated changes
modified src/tactic/interactive.lean

modified src/topology/bounded_continuous_function.lean

modified test/examples.lean



## [2019-05-13 20:00:57](https://github.com/leanprover-community/mathlib/commit/c8a0bb6)
feat(category_theory/products): missing simp lemmas ([#1003](https://github.com/leanprover-community/mathlib/pull/1003))
* feat(category_theory/products): missing simp lemmas
* cleanup proofs
* fix proof
* squeeze_simp
#### Estimated changes
modified src/category_theory/products/default.lean
- \+ *lemma* inl_obj
- \+ *lemma* inl_map
- \+ *lemma* inr_obj
- \+ *lemma* inr_map
- \+ *lemma* fst_obj
- \+ *lemma* fst_map
- \+ *lemma* snd_obj
- \+ *lemma* snd_map
- \+ *lemma* swap_obj
- \+ *lemma* swap_map
- \+ *lemma* evaluation_obj_obj
- \+ *lemma* evaluation_obj_map
- \+ *lemma* evaluation_map_app
- \+ *lemma* evaluation_uncurried_obj
- \+ *lemma* evaluation_uncurried_map
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *def* evaluation
- \+/\- *def* evaluation_uncurried
- \+/\- *def* evaluation
- \+/\- *def* evaluation_uncurried



## [2019-05-13 19:33:32](https://github.com/leanprover-community/mathlib/commit/6c35df0)
feat(category_theory/iso): missing lemmas ([#1001](https://github.com/leanprover-community/mathlib/pull/1001))
* feat(category_theory/iso): missing lemmas
* formatting
* formatting
* oops
* one more
* sleep
#### Estimated changes
modified src/algebraic_geometry/presheafed_space.lean

modified src/category_theory/category.lean
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono

modified src/category_theory/isomorphism.lean
- \+ *lemma* inv_id
- \+ *lemma* inv_comp
- \+ *lemma* is_iso.inv_inv
- \+ *lemma* iso.inv_inv
- \+ *lemma* iso.inv_hom
- \+ *lemma* eq_of_inv_eq_inv



## [2019-05-13 18:39:56+02:00](https://github.com/leanprover-community/mathlib/commit/82f151f)
document the change in scripts ([#1024](https://github.com/leanprover-community/mathlib/pull/1024))
#### Estimated changes
modified docs/install/debian.md

modified docs/install/debian_details.md

modified docs/install/linux.md

modified docs/install/macos.md

modified docs/install/windows.md



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
modified src/category_theory/instances/CommRing/basic.lean
- \+ *def* of

modified src/category_theory/instances/Top/default.lean

modified src/category_theory/instances/Top/opens.lean
- \+ *def* to_Top

created src/category_theory/instances/Top/presheaf_of_functions.lean
- \+ *lemma* one
- \+ *lemma* add
- \+ *lemma* mul
- \+ *def* presheaf_to_Top
- \+ *def* continuous_functions
- \+ *def* pullback
- \+ *def* map
- \+ *def* CommRing_yoneda
- \+ *def* presheaf_to_TopCommRing

created src/category_theory/instances/TopCommRing/basic.lean
- \+ *def* of
- \+ *def* forget_to_CommRing
- \+ *def* forget_to_Top
- \+ *def* forget
- \+ *def* forget_to_Type_via_Top
- \+ *def* forget_to_Type_via_CommRing

created src/category_theory/instances/TopCommRing/default.lean



## [2019-05-13 11:21:50-04:00](https://github.com/leanprover-community/mathlib/commit/b9b5bb4)
chore(Github): no need to wait for Appveyor anymopre
#### Estimated changes
modified .mergify.yml



## [2019-05-13 11:12:35-04:00](https://github.com/leanprover-community/mathlib/commit/e42d808)
chore(scripts): migrate scripts to own repo ([#1011](https://github.com/leanprover-community/mathlib/pull/1011))
#### Estimated changes
modified .travis.yml

deleted appveyor.yml

deleted scripts/auth_github.py
- \- *def* auth_github():

deleted scripts/cache-olean.py
- \- *def* make_cache(fn):
- \- *def* mathlib_asset(repo,
- \- *def* fetch_mathlib(asset):

deleted scripts/delayed_interrupt.py

modified scripts/deploy_nightly.sh

deleted scripts/install_debian.sh

deleted scripts/leanpkg-example.toml

deleted scripts/post-checkout

deleted scripts/post-commit

deleted scripts/remote-install-update-mathlib.sh

deleted scripts/setup-dev-scripts.sh

deleted scripts/setup-lean-git-hooks.sh

deleted scripts/update-mathlib.py



## [2019-05-13 18:20:20+10:00](https://github.com/leanprover-community/mathlib/commit/4864515)
feat(category_theory): lemmas about cancellation ([#1005](https://github.com/leanprover-community/mathlib/pull/1005))
* feat(category_theory): lemmas about cancellation
* rename hypotheses
* Squeeze proofs
#### Estimated changes
modified src/category_theory/category.lean
- \+ *lemma* eq_of_comp_left_eq
- \+ *lemma* eq_of_comp_right_eq
- \+ *lemma* eq_of_comp_left_eq'
- \+ *lemma* eq_of_comp_right_eq'
- \+ *lemma* id_of_comp_left_id
- \+ *lemma* id_of_comp_right_id



## [2019-05-12 14:51:35](https://github.com/leanprover-community/mathlib/commit/1e0761e)
feat(topology/maps): closed embeddings ([#1013](https://github.com/leanprover-community/mathlib/pull/1013))
* feat(topology/maps): closed embeddings
* fix "is_open_map"
#### Estimated changes
modified src/topology/maps.lean
- \+ *lemma* of_inverse
- \+ *lemma* closed_embedding.closed_iff_image_closed
- \+ *lemma* closed_embedding.closed_iff_preimage_closed
- \+ *lemma* closed_embedding_of_continuous_injective_closed
- \+ *lemma* closed_embedding_id
- \+ *lemma* closed_embedding_compose
- \+ *def* is_closed_map
- \+ *def* closed_embedding



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
modified src/category/bifunctor.lean
- \- *def* bicompl
- \- *def* bicompr

modified src/category/bitraversable/instances.lean
- \+/\- *def* bicompl.bitraverse
- \+/\- *def* bicompr.bitraverse
- \+/\- *def* bicompl.bitraverse
- \+/\- *def* bicompr.bitraverse

modified src/logic/function.lean
- \+ *lemma* uncurry_bicompr
- \+ *def* bicompl
- \+ *def* bicompr



## [2019-05-11 18:16:49-04:00](https://github.com/leanprover-community/mathlib/commit/a154ded)
fix(docs/*): docs reorganization [skip ci] ([#1012](https://github.com/leanprover-community/mathlib/pull/1012))
#### Estimated changes
modified .github/PULL_REQUEST_TEMPLATE.md

modified README.md

renamed docs/code-review.md to docs/contribute/code-review.md

renamed docs/howto-contribute.md to docs/contribute/index.md

renamed docs/naming.md to docs/contribute/naming.md

renamed docs/style.md to docs/contribute/style.md

deleted docs/elan.md

created docs/install/debian.md

renamed docs/install_debian_details.md to docs/install/debian_details.md

created docs/install/linux.md

created docs/install/macos.md

renamed docs/install_debian.md to docs/install/project.md

created docs/install/windows.md



## [2019-05-11 14:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/8e71cee)
chore(build): remove script testing on PRs [skip ci]
#### Estimated changes
modified .travis.yml



## [2019-05-11 13:26:30-04:00](https://github.com/leanprover-community/mathlib/commit/e6d959d)
docs(algebra/ring): document compatibility hack [skip ci]
#### Estimated changes
modified src/algebra/ring.lean



## [2019-05-11 12:46:31-04:00](https://github.com/leanprover-community/mathlib/commit/c7d870e)
chore(compatibility): compatibility with Lean 3.5.0c ([#1007](https://github.com/leanprover-community/mathlib/pull/1007))
#### Estimated changes
modified src/algebra/ring.lean
- \+ *def* has_div_of_division_ring

modified src/order/filter/filter_product.lean
- \+/\- *lemma* of_seq_add
- \+/\- *lemma* of_seq_mul
- \+/\- *lemma* of_eq
- \+/\- *lemma* of_ne
- \+/\- *lemma* of_div
- \+/\- *lemma* of_rel_of_rel
- \+/\- *lemma* of_rel
- \+/\- *lemma* of_rel_of_rel₂
- \+/\- *lemma* of_rel₂
- \+/\- *lemma* lt_def
- \+/\- *lemma* lt_def'
- \+/\- *lemma* of_lt_of_lt
- \+/\- *lemma* of_lt
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* of_max
- \+/\- *lemma* of_min
- \+/\- *lemma* of_abs
- \+/\- *lemma* of_seq_add
- \+/\- *lemma* of_seq_mul
- \+/\- *lemma* of_eq
- \+/\- *lemma* of_ne
- \+/\- *lemma* of_div
- \+/\- *lemma* of_rel_of_rel
- \+/\- *lemma* of_rel
- \+/\- *lemma* of_rel_of_rel₂
- \+/\- *lemma* of_rel₂
- \+/\- *lemma* lt_def
- \+/\- *lemma* lt_def'
- \+/\- *lemma* of_lt_of_lt
- \+/\- *lemma* of_lt
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* of_max
- \+/\- *lemma* of_min
- \+/\- *lemma* of_abs
- \+/\- *theorem* of_seq_fun
- \+/\- *theorem* of_seq_fun₂
- \+/\- *theorem* of_seq_fun
- \+/\- *theorem* of_seq_fun₂
- \+/\- *def* bigly_equal
- \+/\- *def* bigly_equal



## [2019-05-11 15:00:03](https://github.com/leanprover-community/mathlib/commit/60da4f4)
feat(data/polynomial): degree_eq_one_of_irreducible_of_root ([#1010](https://github.com/leanprover-community/mathlib/pull/1010))
#### Estimated changes
modified src/data/polynomial.lean
- \+ *lemma* degree_eq_one_of_irreducible_of_root



## [2019-05-11 13:14:21](https://github.com/leanprover-community/mathlib/commit/8603e6b)
refactor(algebra/associated): rename nonzero_of_irreducible to ne_zero_of_irreducible ([#1009](https://github.com/leanprover-community/mathlib/pull/1009))
#### Estimated changes
modified src/algebra/associated.lean
- \+ *theorem* ne_zero_of_irreducible
- \- *theorem* nonzero_of_irreducible

modified src/field_theory/splitting_field.lean

modified src/ring_theory/principal_ideal_domain.lean

modified src/ring_theory/unique_factorization_domain.lean



## [2019-05-11 00:09:41](https://github.com/leanprover-community/mathlib/commit/6858c2f)
fix(category/fold): use correct `opposite` ([#1008](https://github.com/leanprover-community/mathlib/pull/1008))
#### Estimated changes
modified src/category/fold.lean
- \+/\- *def* foldr
- \+/\- *def* mfoldr
- \+/\- *def* foldr
- \+/\- *def* mfoldr

modified src/category_theory/opposites.lean
- \- *lemma* opposite.unop_one
- \- *lemma* opposite.unop_mul
- \- *lemma* opposite.op_one
- \- *lemma* opposite.op_mul



## [2019-05-10 02:32:26](https://github.com/leanprover-community/mathlib/commit/91a7fc2)
fix(tactic/basic): missing `conv` from tactic.basic ([#1004](https://github.com/leanprover-community/mathlib/pull/1004))
#### Estimated changes
modified src/tactic/basic.lean



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
modified src/data/equiv/basic.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finsupp.lean

modified src/measure_theory/measurable_space.lean

modified src/order/basic.lean
- \+ *lemma* not_bounded_iff
- \+ *lemma* not_unbounded_iff
- \+ *theorem* has_min
- \+ *theorem* min_mem
- \+ *theorem* not_lt_min
- \- *theorem* well_founded.has_min
- \- *theorem* well_founded.min_mem
- \- *theorem* well_founded.not_lt_min

modified src/order/order_iso.lean
- \+ *lemma* to_equiv_to_fun
- \+ *lemma* ord''

modified src/set_theory/cardinal.lean
- \+ *lemma* zero_power_le
- \+ *lemma* succ_ne_zero
- \+ *lemma* countable_iff
- \+ *lemma* two_le_iff
- \+ *lemma* two_le_iff'
- \+ *lemma* mk_range_eq
- \+ *lemma* mk_Union_le
- \+ *lemma* mk_sUnion_le
- \+ *lemma* mk_bUnion_le
- \+ *lemma* finset_card_lt_omega
- \+ *lemma* mk_subtype_mono
- \+ *lemma* mk_set_le
- \+ *lemma* mk_image_eq_lift
- \+ *lemma* mk_image_eq_of_inj_on_lift
- \+ *lemma* mk_image_eq_of_inj_on
- \+ *lemma* mk_subtype_of_equiv
- \+ *lemma* mk_sep
- \+ *lemma* mk_preimage_of_injective_lift
- \+ *lemma* mk_preimage_of_subset_range_lift
- \+ *lemma* mk_preimage_of_injective_of_subset_range_lift
- \+ *lemma* mk_preimage_of_injective
- \+ *lemma* mk_preimage_of_subset_range
- \+ *lemma* mk_preimage_of_injective_of_subset_range
- \+ *lemma* mk_subset_ge_of_subset_image_lift
- \+ *lemma* mk_subset_ge_of_subset_image
- \+ *lemma* le_powerlt
- \+ *lemma* powerlt_le
- \+ *lemma* powerlt_le_powerlt_left
- \+ *lemma* powerlt_succ
- \+ *lemma* powerlt_max
- \+ *lemma* zero_powerlt
- \+ *lemma* powerlt_zero
- \+ *theorem* out_embedding
- \+ *theorem* sup_eq_zero
- \+/\- *theorem* mk_range_le
- \+ *theorem* mk_image_eq
- \+ *theorem* le_mk_iff_exists_subset
- \+ *theorem* powerlt_aux
- \+/\- *theorem* mk_range_le
- \- *theorem* mk_eq_of_injective

modified src/set_theory/cofinality.lean
- \+ *lemma* cof_le
- \+ *lemma* le_cof
- \+ *lemma* cof_type
- \+ *theorem* sup_lt_ord
- \+ *theorem* sup_lt
- \+ *theorem* unbounded_of_unbounded_sUnion
- \+ *theorem* unbounded_of_unbounded_Union
- \+ *theorem* infinite_pigeonhole
- \+ *theorem* infinite_pigeonhole_card
- \+ *theorem* infinite_pigeonhole_set
- \+ *theorem* sup_lt_ord_of_is_regular
- \+ *def* cof
- \+ *def* strict_order.cof
- \- *def* order.cof

modified src/set_theory/ordinal.lean
- \+ *lemma* top_lt_top
- \+ *lemma* type_out
- \+ *lemma* injective_typein
- \+ *lemma* order_iso_enum'
- \+ *lemma* order_iso_enum
- \+ *lemma* card_typein
- \+ *lemma* typein_le_typein
- \+ *lemma* enum_le_enum
- \+ *lemma* has_succ_of_is_limit
- \+ *lemma* type_subrel_lt
- \+ *lemma* mk_initial_seg
- \+ *lemma* lt_ord_succ_card
- \+ *lemma* mk_ord_out
- \+ *lemma* card_typein_lt
- \+ *lemma* card_typein_out_lt
- \+ *lemma* ord_injective
- \+ *lemma* sup_succ
- \+ *lemma* unbounded_range_of_sup_ge
- \+ *lemma* mul_le_max_of_omega_le_left
- \+ *lemma* mul_eq_max_of_omega_le_left
- \+ *lemma* add_one_eq
- \+ *lemma* power_nat_le
- \+ *lemma* powerlt_omega
- \+ *lemma* powerlt_omega_le
- \+ *lemma* mk_bounded_set_le_of_omega_le
- \+ *lemma* mk_bounded_set_le
- \+ *lemma* mk_bounded_subset_le
- \+/\- *theorem* type_le'
- \+/\- *theorem* type_le'
- \+ *def* lt_equiv
- \+ *def* initial_seg_out
- \+ *def* principal_seg_out
- \+ *def* order_iso_out
- \+ *def* typein_iso



## [2019-05-09 09:29:20](https://github.com/leanprover-community/mathlib/commit/5329bf3)
feat(algebra/pointwise): More lemmas on pointwise multiplication ([#997](https://github.com/leanprover-community/mathlib/pull/997))
* feat(algebra/pointwise): More lemmas on pointwise multiplication
* Fix build, hopefully
* Fix build
* to_additive + fix formatting
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* mul_subset_mul
- \+ *lemma* mem_smul_set
- \+ *lemma* smul_set_eq_image
- \+ *def* pointwise_mul_fintype
- \+ *def* pointwise_add_fintype
- \+ *def* pointwise_mul_image_is_semiring_hom
- \+ *def* pointwise_mul_action



## [2019-05-09 05:36:49](https://github.com/leanprover-community/mathlib/commit/df5edde)
refactor(strict_mono): make definition + move to order_functions ([#998](https://github.com/leanprover-community/mathlib/pull/998))
* refactor(strict_mono): make definition + move to order_functions
* Weaken assumptions from preorder to has_lt
#### Estimated changes
modified src/algebra/order.lean
- \- *lemma* lt_iff_lt_of_strict_mono
- \- *lemma* le_iff_le_of_strict_mono
- \- *lemma* injective_of_strict_mono
- \- *theorem* compares_of_strict_mono

modified src/algebra/order_functions.lean
- \+ *lemma* lt_iff_lt
- \+ *lemma* injective
- \+ *lemma* le_iff_le
- \+ *lemma* monotone
- \+ *lemma* strict_mono_of_monotone_of_injective
- \+ *theorem* compares
- \+ *def* strict_mono

modified src/ring_theory/noetherian.lean

modified src/set_theory/ordinal.lean



## [2019-05-08 22:40:27](https://github.com/leanprover-community/mathlib/commit/8f5d240)
refactor(order/basic): make type class args explicit in {*}order.lift ([#995](https://github.com/leanprover-community/mathlib/pull/995))
* refactor(order/basic): make type class arguments explicit for {*}order.lift
* Let's try again
* And another try
* Silly typo
* Fix error
* Oops, missed this one
#### Estimated changes
modified src/algebra/ordered_group.lean

modified src/data/fin.lean

modified src/data/real/nnreal.lean

modified src/linear_algebra/basic.lean

modified src/order/basic.lean
- \+/\- *def* preorder.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* linear_order.lift
- \+/\- *def* decidable_linear_order.lift
- \+/\- *def* preorder.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* linear_order.lift
- \+/\- *def* decidable_linear_order.lift

modified src/order/zorn.lean



## [2019-05-08 20:20:16](https://github.com/leanprover-community/mathlib/commit/7f9717f)
feat(*): preorder instances for with_bot and with_zero ([#996](https://github.com/leanprover-community/mathlib/pull/996))
* feat(*): preorder instances for with_bot and with_zero
* Let's try again
#### Estimated changes
modified src/algebra/ordered_group.lean

modified src/order/bounded_lattice.lean



## [2019-05-08 11:42:00](https://github.com/leanprover-community/mathlib/commit/c9cfafc)
chore(tactics): splitting tactics and tests into more files ([#985](https://github.com/leanprover-community/mathlib/pull/985))
* chore(tactics): splitting tactics and tests into more files, cleaning up dependencies
* tweaking comment
* introducing `tactic.basic` and fixing imports
* fixes
* fix copyright
* fix some things
#### Estimated changes
modified src/algebra/group.lean

modified src/category/bitraversable/instances.lean

modified src/category/monad/basic.lean

modified src/category/monad/writer.lean

modified src/category_theory/category.lean

modified src/category_theory/functor.lean

modified src/category_theory/natural_isomorphism.lean

modified src/data/list/defs.lean
- \+/\- *def* neg
- \+/\- *def* pointwise
- \+/\- *def* add
- \+/\- *def* sub
- \+/\- *def* neg
- \+/\- *def* pointwise
- \+/\- *def* add
- \+/\- *def* sub

modified src/data/option/basic.lean

modified src/data/padics/hensel.lean

modified src/data/rel.lean

modified src/data/seq/computation.lean

modified src/data/seq/seq.lean

modified src/data/set/basic.lean

modified src/group_theory/eckmann_hilton.lean

modified src/logic/basic.lean

modified src/logic/relation.lean

modified src/order/lexicographic.lean

modified src/tactic/algebra.lean

modified src/tactic/auto_cases.lean

modified src/tactic/basic.lean
- \- *def* foo
- \- *def* foo

modified src/tactic/cache.lean

modified src/tactic/chain.lean

modified src/tactic/converter/interactive.lean

created src/tactic/core.lean
- \+ *def* foo
- \+ *def* foo

modified src/tactic/default.lean

modified src/tactic/elide.lean

modified src/tactic/explode.lean

modified src/tactic/ext.lean

modified src/tactic/find.lean

modified src/tactic/generalize_proofs.lean

modified src/tactic/interactive.lean

modified src/tactic/library_search.lean

modified src/tactic/local_cache.lean

modified src/tactic/monotonicity/basic.lean

modified src/tactic/monotonicity/default.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/monotonicity/lemmas.lean

modified src/tactic/pi_instances.lean

modified src/tactic/rcases.lean

modified src/tactic/replacer.lean

modified src/tactic/rewrite.lean

modified src/tactic/scc.lean

created src/tactic/solve_by_elim.lean

modified src/tactic/squeeze.lean

modified src/tactic/tauto.lean

modified src/tactic/tidy.lean

modified src/tactic/where.lean

modified src/tactic/wlog.lean

created test/conv.lean

created test/convert.lean
- \+ *lemma* singleton_inter_singleton_eq_empty

created test/ext.lean
- \+ *lemma* unit.ext
- \+ *lemma* df.ext
- \+ *def* my_foo
- \+ *def* my_bar

modified test/library_search/ordered_ring.lean

modified test/library_search/ring_theory.lean

modified test/monotonicity.lean

modified test/monotonicity/test_cases.lean

created test/rcases.lean

created test/rewrite.lean

modified test/solve_by_elim.lean

modified test/tactics.lean
- \- *lemma* unit.ext
- \- *lemma* df.ext
- \- *def* my_foo
- \- *def* my_bar

created test/tauto.lean

created test/wlog.lean



## [2019-05-08 09:47:14](https://github.com/leanprover-community/mathlib/commit/73a30da)
feat(group_theory/subgroup): is_subgroup.inter ([#994](https://github.com/leanprover-community/mathlib/pull/994))
#### Estimated changes
modified src/group_theory/subgroup.lean

modified src/group_theory/submonoid.lean
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
created src/category_theory/elements.lean
- \+ *lemma* π_obj
- \+ *lemma* π_map
- \+ *lemma* to_comma_obj
- \+ *lemma* to_comma_map
- \+ *lemma* from_comma_obj
- \+ *lemma* from_comma_map
- \+ *def* functor.elements
- \+ *def* π
- \+ *def* to_comma
- \+ *def* from_comma
- \+ *def* comma_equivalence

modified src/category_theory/punit.lean
- \+ *lemma* star_obj
- \+ *lemma* star_map
- \+ *def* star



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
modified src/algebra/ordered_group.lean
- \+ *lemma* neg_neg_iff_pos

modified src/data/real/basic.lean
- \+ *theorem* Sup_univ

modified src/data/real/hyperreal.lean
- \+ *lemma* epsilon_eq_inv_omega
- \+ *lemma* inv_epsilon_eq_omega
- \+ *lemma* neg_lt_of_tendsto_zero_of_pos
- \+/\- *lemma* epsilon_lt_pos
- \+ *lemma* st_of_is_st
- \+ *lemma* is_st_st_of_is_st
- \+ *lemma* is_st_st_of_exists_st
- \+ *lemma* is_st_st
- \+ *lemma* is_st_st'
- \+ *lemma* is_st_refl_real
- \+ *lemma* st_id_real
- \+ *lemma* eq_of_is_st_real
- \+ *lemma* is_st_real_iff_eq
- \+ *lemma* is_st_symm_real
- \+ *lemma* is_st_trans_real
- \+ *lemma* is_st_inj_real
- \+ *lemma* is_st_iff_abs_sub_lt_delta
- \+ *lemma* is_st_add
- \+ *lemma* is_st_neg
- \+ *lemma* is_st_sub
- \+ *lemma* lt_of_is_st_lt
- \+ *lemma* is_st_le_of_le
- \+ *lemma* st_le_of_le
- \+ *lemma* lt_of_st_lt
- \+ *lemma* infinite_pos_def
- \+ *lemma* infinite_neg_def
- \+ *lemma* ne_zero_of_infinite
- \+ *lemma* not_infinite_zero
- \+ *lemma* pos_of_infinite_pos
- \+ *lemma* neg_of_infinite_neg
- \+ *lemma* not_infinite_pos_of_infinite_neg
- \+ *lemma* not_infinite_neg_of_infinite_pos
- \+ *lemma* infinite_neg_neg_of_infinite_pos
- \+ *lemma* infinite_pos_neg_of_infinite_neg
- \+ *lemma* infinite_pos_iff_infinite_neg_neg
- \+ *lemma* infinite_neg_iff_infinite_pos_neg
- \+ *lemma* infinite_iff_infinite_neg
- \+ *lemma* not_infinite_of_infinitesimal
- \+ *lemma* not_infinitesimal_of_infinite
- \+ *lemma* not_infinitesimal_of_infinite_pos
- \+ *lemma* not_infinitesimal_of_infinite_neg
- \+ *lemma* infinite_pos_iff_infinite_and_pos
- \+ *lemma* infinite_neg_iff_infinite_and_neg
- \+ *lemma* infinite_pos_iff_infinite_of_pos
- \+ *lemma* infinite_pos_iff_infinite_of_nonneg
- \+ *lemma* infinite_neg_iff_infinite_of_neg
- \+ *lemma* infinite_pos_abs_iff_infinite_abs
- \+ *lemma* infinite_iff_infinite_pos_abs
- \+ *lemma* infinite_iff_infinite_abs
- \+ *lemma* infinite_iff_abs_lt_abs
- \+ *lemma* infinite_pos_add_not_infinite_neg
- \+ *lemma* not_infinite_neg_add_infinite_pos
- \+ *lemma* infinite_neg_add_not_infinite_pos
- \+ *lemma* not_infinite_pos_add_infinite_neg
- \+ *lemma* infinite_pos_add_infinite_pos
- \+ *lemma* infinite_neg_add_infinite_neg
- \+ *lemma* infinite_pos_add_not_infinite
- \+ *lemma* infinite_neg_add_not_infinite
- \+ *lemma* not_infinite_neg
- \+ *lemma* not_infinite_add
- \+ *lemma* is_st_mul
- \+ *lemma* not_infinite_mul
- \+ *lemma* st_add
- \+ *lemma* st_neg
- \+ *lemma* st_mul
- \+ *lemma* infinitesimal_zero
- \+ *lemma* zero_of_infinitesimal_real
- \+ *lemma* zero_iff_infinitesimal_real
- \+ *lemma* infinitesimal_add
- \+ *lemma* infinitesimal_neg
- \+ *lemma* infinitesimal_neg_iff
- \+ *lemma* infinitesimal_mul
- \+ *lemma* not_real_of_infinitesimal_ne_zero
- \+ *lemma* infinite_pos_iff_infinitesimal_inv_pos
- \+ *lemma* infinite_neg_iff_infinitesimal_inv_neg
- \+ *lemma* infinitesimal_pos_iff_infinite_pos_inv
- \+ *lemma* infinitesimal_neg_iff_infinite_neg_inv
- \+ *lemma* is_st_inv
- \+ *lemma* st_inv
- \+ *lemma* infinite_pos_omega
- \+ *lemma* infinite_omega
- \+ *lemma* infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
- \+ *lemma* infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos
- \+ *lemma* infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg
- \+ *lemma* infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg
- \+ *lemma* infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg
- \+ *lemma* infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos
- \+ *lemma* infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos
- \+ *lemma* infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg
- \+ *lemma* infinite_pos_mul_infinite_pos
- \+ *lemma* infinite_neg_mul_infinite_neg
- \+ *lemma* infinite_pos_mul_infinite_neg
- \+ *lemma* infinite_neg_mul_infinite_pos
- \+ *lemma* infinite_mul_of_infinite_not_infinitesimal
- \+ *lemma* infinite_mul_of_not_infinitesimal_infinite
- \+ *lemma* infinite_mul_infinite
- \- *lemma* neg_lt_of_tendsto_zero_of_neg
- \+/\- *lemma* epsilon_lt_pos
- \+/\- *theorem* is_st_unique
- \+ *theorem* not_infinite_of_exists_st
- \+ *theorem* is_st_Sup
- \+ *theorem* exists_st_of_not_infinite
- \+ *theorem* st_eq_Sup
- \+ *theorem* exists_st_iff_not_infinite
- \+ *theorem* infinite_iff_not_exists_st
- \+ *theorem* st_infinite
- \+ *theorem* infinite_pos_of_tendsto_top
- \+ *theorem* infinite_neg_of_tendsto_bot
- \+ *theorem* not_infinite_iff_exist_lt_gt
- \+ *theorem* not_infinite_real
- \+ *theorem* not_real_of_infinite
- \+ *theorem* infinitesimal_def
- \+ *theorem* lt_of_pos_of_infinitesimal
- \+ *theorem* lt_neg_of_pos_of_infinitesimal
- \+ *theorem* gt_of_neg_of_infinitesimal
- \+ *theorem* abs_lt_real_iff_infinitesimal
- \+/\- *theorem* infinitesimal_of_tendsto_zero
- \+/\- *theorem* infinitesimal_epsilon
- \+ *theorem* infinitesimal_sub_is_st
- \+ *theorem* infinitesimal_sub_st
- \+ *theorem* infinitesimal_inv_of_infinite
- \+ *theorem* infinite_of_infinitesimal_inv
- \+ *theorem* infinite_iff_infinitesimal_inv
- \+ *theorem* infinitesimal_iff_infinite_inv
- \+ *theorem* is_st_of_tendsto
- \- *theorem* epsilon_eq_inv_omega
- \- *theorem* inv_epsilon_eq_omega
- \+/\- *theorem* is_st_unique
- \+/\- *theorem* infinitesimal_of_tendsto_zero
- \+/\- *theorem* infinitesimal_epsilon
- \+/\- *def* infinitesimal
- \+ *def* infinite_pos
- \+ *def* infinite_neg
- \+ *def* infinite
- \+/\- *def* infinitesimal

modified src/order/filter/basic.lean
- \+ *lemma* tendsto_at_top_at_bot

modified src/order/filter/filter_product.lean
- \+/\- *lemma* of_seq_add
- \+/\- *lemma* of_seq_mul
- \+/\- *lemma* of_eq_coe
- \+/\- *lemma* of_eq
- \+/\- *lemma* of_ne
- \+ *lemma* of_sub
- \+ *lemma* of_div
- \+/\- *lemma* of_rel_of_rel
- \+/\- *lemma* of_rel
- \+/\- *lemma* of_rel_of_rel₂
- \+/\- *lemma* of_rel₂
- \+/\- *lemma* of_le_of_le
- \+/\- *lemma* of_le
- \+/\- *lemma* lt_def
- \+/\- *lemma* of_lt_of_lt
- \+/\- *lemma* of_lt
- \+ *lemma* lift_id
- \+ *lemma* max_def
- \+ *lemma* min_def
- \+ *lemma* abs_def
- \+ *lemma* of_max
- \+ *lemma* of_min
- \+ *lemma* of_abs
- \+/\- *lemma* of_seq_add
- \+/\- *lemma* of_seq_mul
- \+/\- *lemma* of_eq_coe
- \- *lemma* of_id
- \+/\- *lemma* of_eq
- \+/\- *lemma* of_ne
- \+/\- *lemma* of_rel_of_rel
- \+/\- *lemma* of_rel
- \+/\- *lemma* of_rel_of_rel₂
- \+/\- *lemma* of_rel₂
- \+/\- *lemma* of_le_of_le
- \+/\- *lemma* of_le
- \+/\- *lemma* lt_def
- \+/\- *lemma* of_lt_of_lt
- \+/\- *lemma* of_lt



## [2019-05-07 17:27:55](https://github.com/leanprover-community/mathlib/commit/4a38d2e)
feat(scripts): add --build-new flag to cache-olean ([#992](https://github.com/leanprover-community/mathlib/pull/992))
#### Estimated changes
modified scripts/cache-olean.py



## [2019-05-07 10:49:02-04:00](https://github.com/leanprover-community/mathlib/commit/717033e)
chore(build): cron build restarts from scratch
#### Estimated changes
modified .travis.yml



## [2019-05-07 08:45:19](https://github.com/leanprover-community/mathlib/commit/c726c12)
feat(category/monad/cont): monad_cont instances for state_t, reader_t, except_t and option_t ([#733](https://github.com/leanprover-community/mathlib/pull/733))
* feat(category/monad/cont): monad_cont instances for state_t, reader_t,
except_t and option_t
* feat(category/monad/writer): writer monad transformer
#### Estimated changes
created src/category/monad/basic.lean
- \+ *lemma* map_eq_bind_pure_comp

modified src/category/monad/cont.lean
- \+ *lemma* except_t.goto_mk_label
- \+ *lemma* option_t.goto_mk_label
- \+ *lemma* writer_t.goto_mk_label
- \+ *lemma* state_t.goto_mk_label
- \+ *lemma* reader_t.goto_mk_label
- \+ *def* cont
- \+ *def* cont_t.monad_lift
- \+ *def* except_t.mk_label
- \+ *def* except_t.call_cc
- \+ *def* option_t.mk_label
- \+ *def* option_t.call_cc
- \+ *def* writer_t.mk_label
- \+ *def* writer_t.call_cc
- \+ *def* state_t.mk_label
- \+ *def* state_t.call_cc
- \+ *def* reader_t.mk_label
- \+ *def* reader_t.call_cc

created src/category/monad/writer.lean
- \+ *def* writer
- \+ *def* swap_right
- \+ *def* except_t.pass_aux
- \+ *def* option_t.pass_aux



## [2019-05-07 01:25:54-04:00](https://github.com/leanprover-community/mathlib/commit/98ba07b)
chore(build): fix stages in cron job
#### Estimated changes
modified .travis.yml



## [2019-05-07 00:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/505f748)
chore(build): build against Lean 3.5 nightly build ([#989](https://github.com/leanprover-community/mathlib/pull/989))
#### Estimated changes
modified .travis.yml



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
created src/category_theory/currying.lean
- \+ *lemma* uncurry.obj_obj
- \+ *lemma* uncurry.obj_map
- \+ *lemma* uncurry.map_app
- \+ *lemma* curry.obj_obj_obj
- \+ *lemma* curry.obj_obj_map
- \+ *lemma* curry.obj_map_app
- \+ *lemma* curry.map_app_app
- \+ *def* uncurry
- \+ *def* curry_obj
- \+ *def* curry
- \+ *def* currying



## [2019-05-06 05:34:58](https://github.com/leanprover-community/mathlib/commit/f536dac)
six(style.md): fix broken code ([#987](https://github.com/leanprover-community/mathlib/pull/987))
#### Estimated changes
modified docs/style.md



## [2019-05-05 11:57:30](https://github.com/leanprover-community/mathlib/commit/23270e7)
feat(ring_theory/adjoin): adjoining elements to form subalgebras ([#756](https://github.com/leanprover-community/mathlib/pull/756))
* feat(ring_theory/adjoin): adjoining elements to form subalgebras
* Fix build
* Change to_submodule into a coercion
* Use pointwise_mul
* add simp attribute to adjoin_empty
#### Estimated changes
created src/ring_theory/adjoin.lean
- \+ *theorem* subset_adjoin
- \+ *theorem* adjoin_le
- \+ *theorem* adjoin_le_iff
- \+ *theorem* adjoin_mono
- \+ *theorem* adjoin_empty
- \+ *theorem* adjoin_union
- \+ *theorem* adjoin_eq_span
- \+ *theorem* adjoin_eq_range
- \+ *theorem* adjoin_singleton_eq_range
- \+ *theorem* adjoin_union_coe_submodule
- \+ *theorem* adjoin_int
- \+ *theorem* fg_trans
- \+ *theorem* fg_def
- \+ *theorem* fg_bot
- \+ *theorem* is_noetherian_ring_of_fg
- \+ *theorem* is_noetherian_ring_closure
- \+ *def* fg

modified src/ring_theory/algebra.lean



## [2019-05-05 07:50:10](https://github.com/leanprover-community/mathlib/commit/3f26ba8)
feat(category_theory/products): associators ([#982](https://github.com/leanprover-community/mathlib/pull/982))
#### Estimated changes
created src/category_theory/products/associator.lean
- \+ *lemma* associator_obj
- \+ *lemma* associator_map
- \+ *lemma* inverse_associator_obj
- \+ *lemma* inverse_associator_map
- \+ *def* associator
- \+ *def* inverse_associator
- \+ *def* associativity

renamed src/category_theory/bifunctor.lean to src/category_theory/products/bifunctor.lean

renamed src/category_theory/products.lean to src/category_theory/products/default.lean



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
created src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* ext
- \+ *lemma* id_f
- \+ *lemma* comp_f
- \+ *lemma* comp_coe
- \+ *lemma* id_c
- \+ *lemma* comp_c
- \+ *lemma* map_presheaf_obj_X
- \+ *lemma* map_presheaf_obj_𝒪
- \+ *lemma* map_presheaf_map_f
- \+ *lemma* map_presheaf_map_c
- \+ *def* id
- \+ *def* comp
- \+ *def* forget
- \+ *def* map_presheaf
- \+ *def* on_presheaf

modified src/category_theory/instances/Top/basic.lean

modified src/category_theory/instances/Top/default.lean

modified src/category_theory/instances/Top/open_nhds.lean

modified src/category_theory/instances/Top/opens.lean

created src/category_theory/instances/Top/presheaf.lean
- \+ *lemma* pushforward_eq_eq
- \+ *lemma* id_hom_app'
- \+ *lemma* id_hom_app
- \+ *lemma* id_inv_app'
- \+ *lemma* comp_hom_app
- \+ *lemma* comp_inv_app
- \+ *def* presheaf
- \+ *def* pushforward
- \+ *def* pushforward_eq
- \+ *def* id
- \+ *def* comp

modified src/category_theory/opposites.lean
- \+ *lemma* op_hom
- \+ *lemma* op_inv
- \+ *def* op_induction



## [2019-05-05 02:40:54](https://github.com/leanprover-community/mathlib/commit/fc8b08b)
feat(data/set/basic): prod_subset_iff ([#980](https://github.com/leanprover-community/mathlib/pull/980))
* feat(data/set/basic): prod_subset_iff
* syntax
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* prod_subset_iff



## [2019-05-04 23:56:50](https://github.com/leanprover-community/mathlib/commit/fbce6e4)
fix(data/set/finite): make fintype_seq an instance ([#979](https://github.com/leanprover-community/mathlib/pull/979))
#### Estimated changes
modified src/data/set/finite.lean
- \- *def* fintype_seq



## [2019-05-04 22:16:39](https://github.com/leanprover-community/mathlib/commit/7dea60b)
feat(logic/basic): forall_iff_forall_surj ([#977](https://github.com/leanprover-community/mathlib/pull/977))
a lemma from the perfectoid project
#### Estimated changes
modified src/logic/basic.lean
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
modified src/category_theory/concrete_category.lean
- \+ *lemma* bundled_hom.ext
- \+/\- *lemma* bundled_hom_coe
- \+/\- *lemma* bundled_hom_coe

modified src/category_theory/instances/CommRing/adjunctions.lean
- \+ *lemma* hom_coe_app'

modified src/category_theory/instances/CommRing/basic.lean
- \+ *lemma* hom.ext
- \+/\- *lemma* hom_coe_app
- \+/\- *lemma* hom_coe_app

created src/category_theory/instances/CommRing/colimits.lean
- \+ *lemma* quot_zero
- \+ *lemma* quot_one
- \+ *lemma* quot_neg
- \+ *lemma* quot_add
- \+ *lemma* quot_mul
- \+ *lemma* cocone_naturality
- \+ *lemma* cocone_naturality_components
- \+ *lemma* naturality_bundled
- \+ *def* colimit_setoid
- \+ *def* colimit_type
- \+ *def* colimit
- \+ *def* cocone_fun
- \+ *def* cocone_morphism
- \+ *def* colimit_cocone
- \+ *def* desc_fun_lift
- \+ *def* desc_fun
- \+ *def* desc_morphism
- \+ *def* colimit_is_colimit

modified src/category_theory/instances/CommRing/default.lean

renamed src/category_theory/instances/monoids.lean to src/category_theory/instances/Mon/basic.lean

created src/category_theory/instances/Mon/colimits.lean
- \+ *lemma* quot_one
- \+ *lemma* quot_mul
- \+ *lemma* cocone_naturality
- \+ *lemma* cocone_naturality_components
- \+ *def* colimit_setoid
- \+ *def* colimit_type
- \+ *def* colimit
- \+ *def* cocone_fun
- \+ *def* cocone_morphism
- \+ *def* colimit_cocone
- \+ *def* desc_fun_lift
- \+ *def* desc_fun
- \+ *def* desc_morphism
- \+ *def* colimit_is_colimit

created src/category_theory/instances/Mon/default.lean

modified src/category_theory/limits/cones.lean
- \+ *lemma* naturality_bundled
- \+ *lemma* naturality_bundled



## [2019-05-04 12:06:04-05:00](https://github.com/leanprover-community/mathlib/commit/c7baf8e)
feat(option/injective_map) ([#978](https://github.com/leanprover-community/mathlib/pull/978))
#### Estimated changes
modified src/data/option/basic.lean
- \+ *theorem* injective_map



## [2019-05-03 21:34:29](https://github.com/leanprover-community/mathlib/commit/f98ffde)
feat(tactic/decl_mk_const): performance improvement for library_search ([#967](https://github.com/leanprover-community/mathlib/pull/967))
* feat(tactic/decl_mk_const): auxiliary tactic for library_search [WIP]
* use decl_mk_const in library_search
* use decl_mk_const
* move into tactic/basic.lean
#### Estimated changes
modified src/tactic/basic.lean

modified src/tactic/library_search.lean

modified test/fin_cases.lean

modified test/library_search/basic.lean

modified test/library_search/ordered_ring.lean

modified test/library_search/ring_theory.lean

modified test/mllist.lean



## [2019-05-03 13:58:06-04:00](https://github.com/leanprover-community/mathlib/commit/7b1105b)
chore(build): build only master and its related PRs
#### Estimated changes
modified .travis.yml



## [2019-05-03 13:37:08-04:00](https://github.com/leanprover-community/mathlib/commit/e747c91)
chore(README): put the badges in the README on one line ([#975](https://github.com/leanprover-community/mathlib/pull/975))
#### Estimated changes
modified README.md



## [2019-05-03 12:35:46-04:00](https://github.com/leanprover-community/mathlib/commit/f2db636)
feat(docs/install_debian): Debian startup guide ([#974](https://github.com/leanprover-community/mathlib/pull/974))
* feat(docs/install_debian): Debian startup guide
* feat(scripts/install_debian): One-line install for Debian  [ci skip]
* fix(docs/install_debian*): Typos pointed out by Johan
Also adds a summary of what will be installed
#### Estimated changes
created docs/install_debian.md

created docs/install_debian_details.md

created scripts/install_debian.sh



## [2019-05-03 11:30:19-05:00](https://github.com/leanprover-community/mathlib/commit/f5060c4)
feat(category_theory/limits): support for special shapes of (co)limits ([#938](https://github.com/leanprover-community/mathlib/pull/938))
feat(category_theory/limits): support for special shapes of (co)limits
#### Estimated changes
created docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+ *def* R
- \+ *def* I
- \+ *def* pt
- \+ *def* to_pt
- \+ *def* I_0
- \+ *def* I_1
- \+ *def* cylinder
- \+ *def* cylinder_0
- \+ *def* cylinder_1
- \+ *def* mapping_cylinder
- \+ *def* mapping_cylinder_0
- \+ *def* mapping_cone
- \+ *def* f
- \+ *def* X
- \+ *def* g
- \+ *def* d
- \+ *def* Y
- \+ *def* w
- \+ *def* q

modified src/category_theory/discrete_category.lean

modified src/category_theory/instances/Top/basic.lean
- \+ *def* of

created src/category_theory/limits/shapes/binary_products.lean
- \+ *def* pair_function
- \+ *def* pair
- \+ *def* binary_fan.mk
- \+ *def* binary_cofan.mk

created src/category_theory/limits/shapes/default.lean

created src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* walking_parallel_pair_hom_id
- \+ *lemma* parallel_pair_map_left
- \+ *lemma* parallel_pair_map_right
- \+ *lemma* parallel_pair_functor_obj
- \+ *lemma* fork.of_ι_app_zero
- \+ *lemma* fork.of_ι_app_one
- \+ *lemma* cone.of_fork_π
- \+ *lemma* cocone.of_cofork_ι
- \+ *lemma* fork.of_cone_π
- \+ *lemma* cofork.of_cocone_ι
- \+ *def* walking_parallel_pair_hom.comp
- \+ *def* parallel_pair
- \+ *def* fork.of_ι
- \+ *def* cofork.of_π
- \+ *def* fork.ι
- \+ *def* cofork.π
- \+ *def* fork.condition
- \+ *def* cofork.condition
- \+ *def* cone.of_fork
- \+ *def* cocone.of_cofork
- \+ *def* fork.of_cone
- \+ *def* cofork.of_cocone

created src/category_theory/limits/shapes/products.lean
- \+ *def* fan.mk
- \+ *def* cofan.mk

created src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* hom_id
- \+ *lemma* hom_id
- \+ *lemma* cospan_left
- \+ *lemma* span_left
- \+ *lemma* cospan_right
- \+ *lemma* span_right
- \+ *lemma* cospan_one
- \+ *lemma* span_zero
- \+ *lemma* cospan_map_inl
- \+ *lemma* span_map_fst
- \+ *lemma* cospan_map_inr
- \+ *lemma* span_map_snd
- \+ *lemma* cospan_map_id
- \+ *lemma* span_map_id
- \+ *lemma* condition
- \+ *lemma* condition
- \+ *lemma* cone.of_pullback_cone_π
- \+ *lemma* cocone.of_pushout_cocone_ι
- \+ *lemma* pullback_cone.of_cone_π
- \+ *lemma* pushout_cocone.of_cocone_ι
- \+ *def* hom.comp
- \+ *def* hom.comp
- \+ *def* cospan
- \+ *def* span
- \+ *def* π₁
- \+ *def* π₂
- \+ *def* mk
- \+ *def* ι₁
- \+ *def* ι₂
- \+ *def* mk
- \+ *def* cone.of_pullback_cone
- \+ *def* cocone.of_pushout_cocone
- \+ *def* pullback_cone.of_cone
- \+ *def* pushout_cocone.of_cocone

created src/category_theory/sparse.lean
- \+ *def* sparse_category

modified src/tactic/basic.lean



## [2019-05-03 15:24:11+02:00](https://github.com/leanprover-community/mathlib/commit/219cb1a)
chore(travis): disable the check for minimal imports ([#973](https://github.com/leanprover-community/mathlib/pull/973))
#### Estimated changes
modified .travis.yml



## [2019-05-03 14:11:01+01:00](https://github.com/leanprover-community/mathlib/commit/44386cd)
chore(docs): delete docs/wip.md ([#972](https://github.com/leanprover-community/mathlib/pull/972))
* chore(docs): delete docs/wip.md
long outdated
* remove link in README
#### Estimated changes
modified README.md

deleted docs/wip.md



## [2019-05-03 10:59:45](https://github.com/leanprover-community/mathlib/commit/3eb7ebc)
remove code duplication ([#971](https://github.com/leanprover-community/mathlib/pull/971))
#### Estimated changes
modified src/category_theory/natural_isomorphism.lean



## [2019-05-02 22:55:52+01:00](https://github.com/leanprover-community/mathlib/commit/6956daa)
fix(data/polynomial): change instance order in polynomial.subsingleton ([#970](https://github.com/leanprover-community/mathlib/pull/970))
#### Estimated changes
modified src/data/polynomial.lean



## [2019-05-02 17:32:09](https://github.com/leanprover-community/mathlib/commit/60b3c19)
fix(scripts/remote-install-update-mathlib): apt shouldn't ask ([#969](https://github.com/leanprover-community/mathlib/pull/969))
#### Estimated changes
modified scripts/remote-install-update-mathlib.sh



## [2019-05-02 12:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/d288905)
fix(script/remote-install-update-mathlib) fix answer reading and requests/urllib3 version conflict ([#968](https://github.com/leanprover-community/mathlib/pull/968))
#### Estimated changes
modified README.md

modified scripts/remote-install-update-mathlib.sh



## [2019-05-02 08:40:53](https://github.com/leanprover-community/mathlib/commit/8a097f1)
feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms ([#951](https://github.com/leanprover-community/mathlib/pull/951))
* feat(ring_theory/ideal_operations): inj_iff_trivial_ker for ring homomorphisms
* Update subgroup.lean
* Update ideal_operations.lean
#### Estimated changes
modified src/group_theory/subgroup.lean
- \+ *lemma* trivial_ker_iff_eq_one

modified src/ring_theory/ideal_operations.lean
- \+ *lemma* ker_eq
- \+ *lemma* inj_iff_ker_eq_bot
- \+ *lemma* ker_eq_bot_iff_eq_zero
- \+ *lemma* injective_iff
- \+ *def* ker



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
modified src/category_theory/const.lean
- \+ *lemma* op_obj_op_hom_app
- \+ *lemma* op_obj_op_inv_app
- \+ *lemma* op_obj_unop_hom_app
- \+ *lemma* op_obj_unop_inv_app
- \+ *def* op_obj_op
- \+ *def* op_obj_unop

modified src/category_theory/limits/cones.lean
- \+ *lemma* cone_of_cocone_left_op_X
- \+ *lemma* cone_of_cocone_left_op_π_app
- \+ *lemma* cocone_left_op_of_cone_X
- \+ *lemma* cocone_left_op_of_cone_ι_app
- \+ *lemma* cocone_of_cone_left_op_X
- \+ *lemma* cocone_of_cone_left_op_ι_app
- \+ *lemma* cone_left_op_of_cocone_X
- \+ *lemma* cone_left_op_of_cocone_π_app
- \+ *def* cone_of_cocone_left_op
- \+ *def* cocone_left_op_of_cone
- \+ *def* cocone_of_cone_left_op
- \+ *def* cone_left_op_of_cocone

created src/category_theory/limits/opposites.lean

modified src/category_theory/opposites.lean
- \+ *lemma* left_op_obj
- \+ *lemma* left_op_map
- \+ *lemma* right_op_obj
- \+ *lemma* right_op_map
- \+ *lemma* op_app
- \+ *lemma* unop_app
- \+ *lemma* left_op_app
- \+ *lemma* right_op_app

modified src/category_theory/yoneda.lean



## [2019-05-02 04:37:39](https://github.com/leanprover-community/mathlib/commit/69094fc)
fix(tactic/library_search): iff lemmas with universes ([#935](https://github.com/leanprover-community/mathlib/pull/935))
* fix(tactic/library_search): iff lemmas with universes
* cleaning up
* add crossreference
#### Estimated changes
modified src/tactic/basic.lean

modified src/tactic/library_search.lean

modified test/library_search/basic.lean
- \+ *def* P
- \+ *def* Q
- \+ *def* f

created test/library_search/ordered_ring.lean



## [2019-05-02 02:35:03](https://github.com/leanprover-community/mathlib/commit/9b7fb5f)
feat(category_theory/limits): complete lattices have (co)limits ([#931](https://github.com/leanprover-community/mathlib/pull/931))
* feat(category_theory/limits): complete lattices have (co)limits
* Update lattice.lean
#### Estimated changes
created src/category_theory/limits/lattice.lean



## [2019-05-01 08:53:51-04:00](https://github.com/leanprover-community/mathlib/commit/b3433a5)
feat(script/auth_github): improve messages [ci skip] ([#965](https://github.com/leanprover-community/mathlib/pull/965))
#### Estimated changes
modified scripts/auth_github.py

