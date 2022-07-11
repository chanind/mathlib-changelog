## [2019-08-31 22:37:28](https://github.com/leanprover-community/mathlib/commit/df65dde)
feat(data/option/basic): eq_some_iff_get_eq ([#1370](https://github.com/leanprover-community/mathlib/pull/1370))
* feat(data/option/basic): eq_some_iff_get_eq
* Update basic.lean
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* eq_some_iff_get_eq



## [2019-08-31 20:38:30](https://github.com/leanprover-community/mathlib/commit/72ce940)
feat(category_theory/limits/of_nat_iso): missing parts of the limits API ([#1355](https://github.com/leanprover-community/mathlib/pull/1355))
* feat(category_theory/limits/of_nat_isp)
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* Update src/category_theory/limits/limits.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* use @[reassoc]
* fixing after rename
* fix renaming
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/limits/limits.lean
- \+ *lemma* cone_of_hom_of_cone
- \+ *lemma* hom_of_cone_of_hom
- \+ *lemma* cone_of_hom_fac
- \+ *lemma* cone_fac
- \+ *lemma* cocone_of_hom_of_cocone
- \+ *lemma* hom_of_cocone_of_hom
- \+ *lemma* cocone_of_hom_fac
- \+ *lemma* cocone_fac
- \+ *def* unique_up_to_iso
- \+ *def* iso_unique_cone_morphism
- \+ *def* cone_of_hom
- \+ *def* hom_of_cone
- \+ *def* limit_cone
- \+ *def* of_nat_iso
- \+ *def* iso_unique_cocone_morphism
- \+ *def* cocone_of_hom
- \+ *def* hom_of_cocone
- \+ *def* colimit_cocone
- \- *def* unique
- \- *def* is_limit_iso_unique_cone_morphism
- \- *def* is_colimit_iso_unique_cocone_morphism

Modified src/category_theory/limits/preserves.lean




## [2019-08-30 20:07:24](https://github.com/leanprover-community/mathlib/commit/455f060)
chore(unicode): improve arrows ([#1373](https://github.com/leanprover-community/mathlib/pull/1373))
* chore(unicode): improve arrows
* grammar
Co-Authored-By: Johan Commelin <johan@commelin.net>
* moar
#### Estimated changes
Modified docs/extras/simp.md
- \+/\- *lemma* my_lemma

Modified src/category/traversable/basic.lean


Modified src/computability/primrec.lean


Modified src/data/list/defs.lean


Modified src/data/mv_polynomial.lean


Modified src/order/filter/basic.lean


Modified src/tactic/apply.lean


Modified src/tactic/finish.lean




## [2019-08-30 13:16:52-04:00](https://github.com/leanprover-community/mathlib/commit/4c5c4dc)
doc(contribute): add detailed instructions for cache-olean [skip ci] ([#1367](https://github.com/leanprover-community/mathlib/pull/1367))
#### Estimated changes
Modified docs/contribute/index.md




## [2019-08-30 16:13:59](https://github.com/leanprover-community/mathlib/commit/2db7fa4)
feat(sanity_check): improve sanity_check ([#1369](https://github.com/leanprover-community/mathlib/pull/1369))
* feat(sanity_check): improve sanity_check
- add hole command for sanity check (note: hole commands only work when an expression is expected, not when a command is expected, which is unfortunate)
- print the type of the unused arguments
- print whether an unused argument is a duplicate
- better check to filter automatically generated declarations
- do not print arguments of type `parse _`
- The binding brackets from `tactic.where` are moved to `meta.expr`. The definition is changed so that strict implicit arguments are printed as `{{ ... }}`
* typos
* improve docstring
* Also check for duplicated namespaces
Fun fact: I had to remove an unused argument from `decidable_chain'` for my function to work.
#### Estimated changes
Modified src/data/list/defs.lean


Modified src/meta/expr.lean
- \+ *def* brackets

Modified src/tactic/core.lean


Modified src/tactic/sanity_check.lean


Modified src/tactic/where.lean


Modified test/sanity_check.lean




## [2019-08-30 11:48:46](https://github.com/leanprover-community/mathlib/commit/afe51c7)
feat(category_theory/limits): special shapes ([#1339](https://github.com/leanprover-community/mathlib/pull/1339))
* providing minimal API for limits of special shapes
* apis for special shapes
* fintype instances
* associators, unitors, braidings for binary product
* map
* instances
* assoc lemma
* coprod
* fix import
* names
* adding some docs
* updating tutorial on limits
* minor
* uniqueness of morphisms to terminal object
* better treatment of has_terminal
* various
* not there yet
* deleting a dumb file
* remove constructions for a later PR
* use @[reassoc]
* Update src/category_theory/limits/shapes/finite_products.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* improving the colimits tutorial
* minor
* notation for `prod_obj` and `sigma_obj`.
* reverting to `condition`
* implicit arguments
* more implicit arguments
* minor
* notational for initial and terminal objects
* various
* fix notation priorities
* remove unused case bash tactic
* fix whitespace
* comment
* notations
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean
- \+ *def* I₀
- \+ *def* I₁
- \+/\- *def* cylinder
- \+ *def* cylinder₀
- \+ *def* cylinder₁
- \+/\- *def* mapping_cylinder
- \+ *def* mapping_cylinder₀
- \+/\- *def* mapping_cone
- \+/\- *def* X
- \+/\- *def* Y
- \- *def* I_0
- \- *def* I_1
- \- *def* cylinder_0
- \- *def* cylinder_1
- \- *def* mapping_cylinder_0
- \- *def* d
- \- *def* w

Modified src/category_theory/discrete_category.lean
- \+ *lemma* of_function_obj
- \+ *lemma* of_function_map
- \+ *lemma* of_function_app
- \+/\- *def* of_function
- \+/\- *def* of_homs
- \+/\- *def* of_isos

Modified src/category_theory/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.lift_π
- \+/\- *lemma* lim.map_π

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* pair_obj_left
- \+ *lemma* pair_obj_right
- \+ *lemma* map_pair_left
- \+ *lemma* map_pair_right
- \+ *lemma* binary_fan.mk_π_app_left
- \+ *lemma* binary_fan.mk_π_app_right
- \+ *lemma* binary_cofan.mk_π_app_left
- \+ *lemma* binary_cofan.mk_π_app_right
- \+ *lemma* prod.symmetry
- \+ *lemma* coprod.symmetry
- \+ *def* map_pair
- \+ *def* prod.braiding
- \+ *def* prod.associator
- \+ *def* prod.left_unitor
- \+ *def* prod.right_unitor
- \+ *def* coprod.braiding
- \+ *def* coprod.associator
- \+ *def* coprod.left_unitor
- \+ *def* coprod.right_unitor

Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* equalizer.condition
- \+ *lemma* coequalizer.condition

Created src/category_theory/limits/shapes/finite_limits.lean


Created src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/products.lean
- \+ *lemma* fan.mk_π_app
- \+ *lemma* cofan.mk_π_app

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *lemma* condition
- \+ *lemma* pullback.condition
- \+ *lemma* pushout.condition
- \+/\- *def* mk
- \- *def* π₁
- \- *def* π₂
- \- *def* ι₁
- \- *def* ι₂

Created src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/single_obj.lean




## [2019-08-29 21:31:25](https://github.com/leanprover-community/mathlib/commit/1278efd)
Fix `tactic.exact` timeout in `apply'` ([#1371](https://github.com/leanprover-community/mathlib/pull/1371))
Sometimes `tactic.exact` may timeout for no reason. See zulip discussion https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.60apply'.60timeout/near/174415043
#### Estimated changes
Modified src/tactic/apply.lean




## [2019-08-29 12:31:24](https://github.com/leanprover-community/mathlib/commit/1ff3585)
feat(analysis/calculus/times_cont_diff): adding a lemma ([#1358](https://github.com/leanprover-community/mathlib/pull/1358))
* feat(analysis/calculus/times_cont_diff): adding a lemma
* doc
* change k to \bbk
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_on.differentiable_on



## [2019-08-28 21:31:26](https://github.com/leanprover-community/mathlib/commit/3b19503)
refactor(category_theory/single_obj): migrate to bundled morphisms ([#1330](https://github.com/leanprover-community/mathlib/pull/1330))
* Define equivalence between `{ f // is_monoid_hom f }` and `monoid_hom`
* Migrate `single_obj` to bundled homomorphisms
Fix a bug in `to_End`: the old implementation used a wrong monoid
structure on `End`.
* Fix `Mon.hom_equiv_monoid_hom` as suggested by @jcommelin
#### Estimated changes
Modified src/algebra/Mon/basic.lean
- \+ *def* hom_equiv_monoid_hom

Modified src/category_theory/single_obj.lean
- \+/\- *lemma* to_End_def
- \+/\- *lemma* map_hom_id
- \+/\- *lemma* map_hom_comp
- \+ *lemma* id_to_functor
- \+ *lemma* comp_to_functor
- \+ *lemma* to_Aut_hom
- \+ *lemma* to_Aut_inv
- \+/\- *def* to_End
- \+/\- *def* map_hom
- \+ *def* to_functor
- \+ *def* to_Aut
- \- *def* to_End_equiv
- \- *def* map_hom_equiv



## [2019-08-28 16:20:58](https://github.com/leanprover-community/mathlib/commit/d4c1c0f)
fix(tactic.basic): add sanity_check import ([#1365](https://github.com/leanprover-community/mathlib/pull/1365))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-08-28 10:14:09](https://github.com/leanprover-community/mathlib/commit/721d67a)
fix(topology/uniform_space): sanity_check pass ([#1364](https://github.com/leanprover-community/mathlib/pull/1364))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* mem_uniformity_is_closed
- \+/\- *lemma* to_topological_space_prod
- \+/\- *lemma* sum.uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_iff_exists_le_nhds
- \+/\- *lemma* cauchy_map_iff_exists_tendsto
- \+/\- *lemma* cauchy_seq_tendsto_of_is_complete
- \+/\- *lemma* totally_bounded_subset
- \+/\- *lemma* totally_bounded_empty
- \+/\- *lemma* totally_bounded_closure
- \+/\- *lemma* totally_bounded_image
- \+/\- *theorem* cauchy_seq_tendsto_of_complete
- \+/\- *def* cauchy_seq

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* extension_coe
- \+/\- *lemma* extension₂_coe_coe

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* uniform_continuous_quotient_lift₂

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing.mk'
- \+/\- *lemma* uniform_extend_subtype
- \+/\- *lemma* uniformly_extend_of_ind
- \- *def* uniform_inducing.mk'



## [2019-08-28 09:17:30](https://github.com/leanprover-community/mathlib/commit/79dccba)
refactor: change field notation from k to \bbk ([#1363](https://github.com/leanprover-community/mathlib/pull/1363))
* refactor: change field notation from k to \bbK
* change \bbK to \bbk
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* has_fderiv_at.differentiable_at
- \+/\- *lemma* differentiable_within_at.has_fderiv_within_at
- \+/\- *lemma* differentiable_at.has_fderiv_at
- \+/\- *lemma* has_fderiv_at.fderiv
- \+/\- *lemma* differentiable_within_at.mono
- \+/\- *lemma* differentiable_on.mono
- \+/\- *lemma* differentiable.differentiable_on
- \+/\- *lemma* fderiv_within_subset
- \+/\- *lemma* fderiv_within_univ
- \+/\- *lemma* fderiv_within_inter
- \+/\- *lemma* differentiable_within_at.congr_mono
- \+/\- *lemma* differentiable_on.congr_mono
- \+/\- *lemma* differentiable_at.congr_of_mem_nhds
- \+/\- *lemma* differentiable_within_at.fderiv_within_congr_mono
- \+/\- *lemma* fderiv_within_congr_of_mem_nhds_within
- \+/\- *lemma* fderiv_within_congr
- \+/\- *lemma* differentiable_at_id
- \+/\- *lemma* differentiable_within_at_id
- \+/\- *lemma* differentiable_id
- \+/\- *lemma* differentiable_on_id
- \+/\- *lemma* fderiv_id
- \+/\- *lemma* fderiv_within_id
- \+/\- *lemma* differentiable_at_const
- \+/\- *lemma* differentiable_within_at_const
- \+/\- *lemma* fderiv_const
- \+/\- *lemma* fderiv_within_const
- \+/\- *lemma* differentiable_const
- \+/\- *lemma* differentiable_on_const
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_within_at
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_linear_map.differentiable_at
- \+/\- *lemma* is_bounded_linear_map.differentiable_within_at
- \+/\- *lemma* is_bounded_linear_map.fderiv
- \+/\- *lemma* is_bounded_linear_map.fderiv_within
- \+/\- *lemma* is_bounded_linear_map.differentiable
- \+/\- *lemma* is_bounded_linear_map.differentiable_on
- \+/\- *lemma* differentiable_within_at.smul
- \+/\- *lemma* differentiable_at.smul
- \+/\- *lemma* differentiable_on.smul
- \+/\- *lemma* differentiable.smul
- \+/\- *lemma* fderiv_within_smul
- \+/\- *lemma* fderiv_smul
- \+/\- *lemma* fderiv_within_add
- \+/\- *lemma* differentiable_within_at.neg
- \+/\- *lemma* differentiable_at.neg
- \+/\- *lemma* differentiable_on.neg
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* fderiv_within_neg
- \+/\- *lemma* fderiv_neg
- \+/\- *lemma* fderiv_within_sub
- \+/\- *lemma* differentiable_within_at.continuous_within_at
- \+/\- *lemma* differentiable_at.continuous_at
- \+/\- *lemma* differentiable_on.continuous_on
- \+/\- *lemma* differentiable.continuous
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_within_at
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_at
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+/\- *lemma* is_bounded_bilinear_map.fderiv
- \+/\- *lemma* is_bounded_bilinear_map.fderiv_within
- \+/\- *lemma* is_bounded_bilinear_map.differentiable
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_on
- \+/\- *lemma* is_bounded_bilinear_map.continuous
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable.comp
- \+/\- *lemma* differentiable_at.smul'
- \+/\- *lemma* differentiable_on.smul'
- \+/\- *lemma* differentiable.smul'
- \+/\- *lemma* fderiv_within_smul'
- \+/\- *lemma* fderiv_smul'
- \+/\- *lemma* differentiable_at.mul
- \+/\- *lemma* differentiable_on.mul
- \+/\- *lemma* differentiable.mul
- \+/\- *lemma* fderiv_within_mul
- \+/\- *lemma* fderiv_mul
- \+/\- *theorem* unique_diff_within_at.eq
- \+/\- *theorem* unique_diff_on.eq
- \+/\- *theorem* has_fderiv_at_id
- \+/\- *theorem* has_fderiv_at_filter.smul
- \+/\- *theorem* has_fderiv_within_at.smul
- \+/\- *theorem* has_fderiv_at.smul
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_within_at.comp
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \+/\- *def* has_fderiv_at_filter
- \+/\- *def* has_fderiv_within_at
- \+/\- *def* has_fderiv_at
- \+/\- *def* fderiv_within
- \+/\- *def* fderiv

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* tangent_cone_univ
- \+/\- *lemma* tangent_cone_at.lim_zero
- \+/\- *lemma* unique_diff_within_at_univ
- \+/\- *lemma* unique_diff_on_univ
- \+/\- *lemma* unique_diff_within_at.inter
- \+/\- *lemma* unique_diff_within_at.mono
- \+/\- *lemma* is_open.unique_diff_within_at
- \+/\- *lemma* unique_diff_on_inter
- \+/\- *lemma* is_open.unique_diff_on
- \+/\- *lemma* unique_diff_on.prod

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* iterated_fderiv_within_congr
- \+/\- *lemma* times_cont_diff_rec.of_succ
- \+/\- *lemma* times_cont_diff_rec.continuous
- \+/\- *lemma* times_cont_diff_rec.differentiable
- \+/\- *lemma* times_cont_diff_on_rec.of_succ
- \+/\- *lemma* times_cont_diff_on_rec.differentiable_on
- \+/\- *lemma* times_cont_diff_on.of_succ
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+/\- *lemma* times_cont_diff_on.congr_mono
- \+/\- *lemma* times_cont_diff_on.congr
- \+/\- *lemma* times_cont_diff_on.congr_mono'
- \+/\- *lemma* times_cont_diff_on.mono
- \+/\- *lemma* times_cont_diff.of_le
- \+/\- *lemma* times_cont_diff.of_succ
- \+/\- *lemma* times_cont_diff.continuous
- \+/\- *lemma* times_cont_diff.continuous_fderiv
- \+/\- *lemma* times_cont_diff_top
- \+/\- *lemma* times_cont_diff_const
- \+/\- *lemma* is_bounded_linear_map.times_cont_diff
- \+/\- *lemma* times_cont_diff_fst
- \+/\- *lemma* times_cont_diff_snd
- \+/\- *lemma* times_cont_diff_id
- \+/\- *lemma* is_bounded_bilinear_map.times_cont_diff
- \+/\- *def* iterated_continuous_linear_map
- \+/\- *def* iterated_continuous_linear_map.normed_group_rec
- \+/\- *def* iterated_continuous_linear_map.normed_space_rec
- \+/\- *def* iterated_fderiv
- \+/\- *def* iterated_fderiv_within
- \+/\- *def* times_cont_diff_rec
- \+/\- *def* times_cont_diff_on_rec
- \+/\- *def* times_cont_diff_on
- \+/\- *def* times_cont_diff

Modified src/analysis/normed_space/banach.lean
- \+/\- *theorem* exists_preimage_norm_le
- \+/\- *theorem* open_mapping
- \+/\- *theorem* linear_equiv.is_bounded_inv

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map
- \+/\- *lemma* zero
- \+/\- *lemma* id
- \+/\- *lemma* fst
- \+/\- *lemma* snd
- \+/\- *lemma* smul
- \+/\- *lemma* neg
- \+/\- *lemma* add
- \+/\- *lemma* sub
- \+/\- *lemma* tendsto
- \+/\- *lemma* continuous
- \+/\- *lemma* lim_zero_bounded_linear_map
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+/\- *lemma* is_bounded_bilinear_map.map_sub_left
- \+/\- *lemma* is_bounded_bilinear_map.map_sub_right
- \+/\- *lemma* is_bounded_bilinear_map_deriv_coe
- \+/\- *lemma* is_bounded_bilinear_map.is_bounded_linear_map_deriv
- \+/\- *theorem* is_O_id
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_sub
- \+/\- *def* to_linear_map
- \+/\- *def* to_continuous_linear_map
- \+/\- *def* is_bounded_bilinear_map.linear_deriv
- \+/\- *def* is_bounded_bilinear_map.deriv

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* linear_map.continuous_of_bound
- \+/\- *lemma* linear_map_with_bound_coe
- \+/\- *lemma* linear_map_with_bound_apply
- \+/\- *lemma* bounds_nonempty
- \+/\- *lemma* bounds_bdd_below
- \+/\- *lemma* norm_zero
- \+/\- *lemma* norm_id
- \+/\- *lemma* scalar_prod_space_iso_norm
- \+/\- *theorem* is_O_comp
- \+/\- *theorem* is_O_sub
- \+/\- *def* linear_map.with_bound



## [2019-08-27 23:19:25+02:00](https://github.com/leanprover-community/mathlib/commit/45df75b)
fix(topology/algebra/uniform_group): tiny priority tweak
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean




## [2019-08-26 17:11:07](https://github.com/leanprover-community/mathlib/commit/cc04ba7)
chore(algebra/ring): change semiring_hom to ring_hom ([#1361](https://github.com/leanprover-community/mathlib/pull/1361))
* added bundled ring homs
* removed comment
* Tidy and making docstrings consistent
* fix spacing
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* whoops, actually removing instances
* change semiring_hom to ring_hom
* corrected docstring
#### Estimated changes
Modified src/algebra/ring.lean




## [2019-08-26 14:50:25](https://github.com/leanprover-community/mathlib/commit/914c572)
feat(data/rat): add lt, le, and eq def lemmas, move casts into rat to basic ([#1348](https://github.com/leanprover-community/mathlib/pull/1348))
#### Estimated changes
Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/rat/basic.lean
- \+ *lemma* eq_iff_mul_eq_mul
- \+ *lemma* coe_int_num_of_denom_eq_one
- \+ *lemma* inv_def'
- \+ *lemma* mul_own_denom_eq_num
- \+/\- *theorem* num_denom
- \+/\- *theorem* num_denom'
- \+/\- *theorem* of_int_eq_mk
- \+ *theorem* coe_int_eq_mk
- \+ *theorem* mk_eq_div
- \+ *theorem* coe_int_eq_of_int
- \+ *theorem* coe_int_num
- \+ *theorem* coe_int_denom
- \+ *theorem* coe_nat_eq_mk
- \+ *theorem* coe_nat_num
- \+ *theorem* coe_nat_denom

Modified src/data/rat/cast.lean
- \- *lemma* coe_int_num_of_denom_eq_one
- \- *theorem* coe_int_eq_mk
- \- *theorem* mk_eq_div
- \- *theorem* coe_int_eq_of_int
- \- *theorem* coe_int_num
- \- *theorem* coe_int_denom
- \- *theorem* coe_nat_eq_mk
- \- *theorem* coe_nat_num
- \- *theorem* coe_nat_denom

Modified src/data/rat/order.lean
- \+ *lemma* div_lt_div_iff_mul_lt_mul
- \+ *lemma* lt_one_iff_num_lt_denom



## [2019-08-26 08:13:13](https://github.com/leanprover-community/mathlib/commit/7bc18a8)
feat(data/fin): coe_eq_val and coe_mk ([#1321](https://github.com/leanprover-community/mathlib/pull/1321))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* mk_val
- \+ *lemma* coe_mk
- \+ *lemma* coe_eq_val
- \- *def* mk_val



## [2019-08-23 12:07:10+02:00](https://github.com/leanprover-community/mathlib/commit/253a9f7)
fix(docs/install): resize extensions icons for consistency [ci skip]
#### Estimated changes
Modified docs/install/extensions-icon.png


Modified docs/install/new-extensions-icon.png




## [2019-08-23 12:00:49+02:00](https://github.com/leanprover-community/mathlib/commit/91a9b4b)
doc(install/*): new VS-code icon [ci skip]
#### Estimated changes
Modified docs/install/linux.md


Modified docs/install/macos.md


Created docs/install/new-extensions-icon.png


Modified docs/install/windows.md




## [2019-08-23 08:45:41](https://github.com/leanprover-community/mathlib/commit/9a42572)
feat(tactic/apply'): apply without unfolding type definitions ([#1234](https://github.com/leanprover-community/mathlib/pull/1234))
* feat(tactic/apply'): apply without unfolding type definitions
* Update src/tactic/interactive.lean
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
* improve doc
* more doc
* Update core.lean
* add test case
* add test case
* improve treatment of type class instances for apply'
* tweak application of instance resolution
* fix
* move `apply'` to its own file
* adjust docs
* import apply from tactic.default
* fix import in test
* Update tactics.lean
#### Estimated changes
Created src/tactic/apply.lean
- \+ *def* reorder_goals

Modified src/tactic/core.lean


Modified src/tactic/default.lean


Modified src/tactic/interactive.lean


Created test/apply.lean


Modified test/examples.lean


Modified test/tactics.lean




## [2019-08-22 18:22:53](https://github.com/leanprover-community/mathlib/commit/f74cc70)
fix(tactic/tauto): use intro1 to deal with negations ([#1354](https://github.com/leanprover-community/mathlib/pull/1354))
* fix(tactic/tauto): use intro1 to deal with negations
* test(tactic/tauto): add tests
#### Estimated changes
Modified src/tactic/tauto.lean


Modified test/tauto.lean




## [2019-08-22 15:27:06](https://github.com/leanprover-community/mathlib/commit/40b09aa)
feat(*): small lemmas from the sensitivity formalization ([#1352](https://github.com/leanprover-community/mathlib/pull/1352))
* feat(set_theory/cardinal): norm_cast attributes and extra lemma
* feat(logic/basic): ne.symm_iff
* feat(data/fin): succ_ne_zero
* feat(data/bool): bxor_of_ne
* feat(algebra/big_operators, data/fintype): {finset,fintype}.card_eq_sum_ones
* feat(data/set): range_restrict
* feat(data/finset): inter lemmas
* Reid's corrections
* fixes
* fix cardinal power lemma
* fixes
* Update bool.lean
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* card_eq_sum_ones

Modified src/data/bool.lean
- \+ *lemma* bxor_iff_ne

Modified src/data/fin.lean
- \+ *lemma* succ_ne_zero

Modified src/data/finset.lean
- \+ *lemma* inter_subset_inter
- \+ *lemma* inter_subset_inter_right
- \+ *lemma* inter_subset_inter_left

Modified src/data/fintype.lean
- \+ *lemma* card_eq_sum_ones
- \+ *theorem* univ_of_subsingleton
- \+ *theorem* card_of_subsingleton
- \- *theorem* fintype.univ_of_subsingleton
- \- *theorem* fintype.card_of_subsingleton

Modified src/data/set/function.lean
- \+ *lemma* range_restrict

Modified src/logic/basic.lean
- \+ *lemma* ne_comm

Modified src/set_theory/cardinal.lean
- \+ *lemma* pow_cast_right
- \+/\- *theorem* nat_cast_pow
- \+/\- *theorem* nat_cast_le
- \+/\- *theorem* nat_cast_lt
- \+/\- *theorem* nat_cast_inj
- \+/\- *theorem* nat_succ



## [2019-08-22 10:31:24](https://github.com/leanprover-community/mathlib/commit/f442a41)
docs(category/monad,bitraversable): add module docstrings [#1260](https://github.com/leanprover-community/mathlib/pull/1260)  ([#1286](https://github.com/leanprover-community/mathlib/pull/1286))
* docs(category/monad,bitraversable): add module docstrings
* more docs
* still more doc
* doc about traversable
#### Estimated changes
Modified src/category/bitraversable/basic.lean
- \+ *def* alist

Modified src/category/bitraversable/instances.lean


Modified src/category/bitraversable/lemmas.lean
- \+/\- *def* tfst
- \+/\- *def* tsnd

Modified src/category/monad/basic.lean


Modified src/category/traversable/basic.lean




## [2019-08-22 09:32:22+02:00](https://github.com/leanprover-community/mathlib/commit/a489719)
Rename Groupoid.lean to groupoid_category.lean ([#1353](https://github.com/leanprover-community/mathlib/pull/1353))
This fixes a problem with `category_theory/groupoid` and `category_theory/Groupoid` having the same name except for the case of the first letter, which causes a problem on case insensitive file systems.
#### Estimated changes
Renamed src/category_theory/Groupoid.lean to src/category_theory/groupoid_category.lean




## [2019-08-21 19:35:06](https://github.com/leanprover-community/mathlib/commit/8de4273)
feat(category_theory/Groupoid): category of groupoids ([#1325](https://github.com/leanprover-community/mathlib/pull/1325))
* feat(category_theory/Groupoid): category of groupoids
* fix comment
* more articles
#### Estimated changes
Created src/category_theory/Groupoid.lean
- \+ *def* Groupoid
- \+ *def* of
- \+ *def* objects
- \+ *def* forget_to_Cat



## [2019-08-21 12:19:41](https://github.com/leanprover-community/mathlib/commit/35144f2)
feat(conv/conv): conv tactics for zooming/saving state ([#1351](https://github.com/leanprover-community/mathlib/pull/1351))
* feat(conv/conv): conv tactics for zooming/saving state
* rob's doc fixes
* nicer docs
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/converter/interactive.lean


Created test/conv/conv.lean




## [2019-08-21 11:04:30](https://github.com/leanprover-community/mathlib/commit/3f915fc)
feat(archive): add the cubing a cube proof ([#1343](https://github.com/leanprover-community/mathlib/pull/1343))
* feat(archive): add the cubing a cube proof
* rename file
* add leanpkg configure to travis
#### Estimated changes
Modified .travis.yml


Created archive/cubing_a_cube.lean
- \+ *lemma* Ico_lemma
- \+ *lemma* hw'
- \+ *lemma* b_mem_side
- \+ *lemma* b_mem_to_set
- \+ *lemma* side_tail
- \+ *lemma* b_mem_bottom
- \+ *lemma* b_lt_xm
- \+ *lemma* b_ne_xm
- \+ *lemma* tail_shift_up
- \+ *lemma* head_shift_up
- \+ *lemma* side_unit_cube
- \+ *lemma* to_set_subset_unit_cube
- \+ *lemma* side_subset
- \+ *lemma* zero_le_of_mem_side
- \+ *lemma* zero_le_of_mem
- \+ *lemma* zero_le_b
- \+ *lemma* b_add_w_le_one
- \+ *lemma* w_ne_one
- \+ *lemma* shift_up_bottom_subset_bottoms
- \+ *lemma* valley_unit_cube
- \+ *lemma* tail_sub
- \+ *lemma* bottom_mem_side
- \+ *lemma* b_le_b
- \+ *lemma* t_le_t
- \+ *lemma* w_lt_w
- \+ *lemma* two_le_mk_bcubes
- \+ *lemma* nonempty_bcubes
- \+ *lemma* exists_mi
- \+ *lemma* mi_mem_bcubes
- \+ *lemma* mi_minimal
- \+ *lemma* mi_strict_minimal
- \+ *lemma* mi_xm_ne_one
- \+ *lemma* smallest_on_boundary
- \+ *lemma* mi_not_on_boundary
- \+ *lemma* mi_not_on_boundary'
- \+ *lemma* strict_mono_sequence_of_cubes
- \+ *theorem* not_correct
- \+ *theorem* cannot_cube_a_cube
- \+ *def* side
- \+ *def* to_set
- \+ *def* to_set_subset
- \+ *def* to_set_disjoint
- \+ *def* bottom
- \+ *def* xm
- \+ *def* shift_up
- \+ *def* unit_cube
- \+ *def* correct
- \+ *def* valley
- \+ *def* bcubes
- \+ *def* on_boundary
- \+ *def* mi
- \+ *def* valley_mi
- \+ *def* decreasing_sequence



## [2019-08-21 05:42:55](https://github.com/leanprover-community/mathlib/commit/c512875)
refactor(*): rewrite `to_additive` attribute ([#1345](https://github.com/leanprover-community/mathlib/pull/1345))
* chore(algebra/group/to_additive): auto add structure fields
* Snapshot
* Rewrite `@[to_additive]`
* Drop more explicit `name` arguments to `to_additive`
* Drop more explicit arguments to `to_additive`
* Map namespaces with `run_cmd to_additive.map_namespace`
* fix(`group_theory/perm/sign`): fix compile
* Fix handling of equational lemmas; fix warnings
* Use `list.mmap'`
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* is_group_hom.map_finset_prod
- \- *lemma* sum_hom
- \- *lemma* is_group_hom.finset_prod

Modified src/algebra/direct_limit.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/hom.lean
- \+/\- *lemma* coe_as_monoid_hom
- \+ *lemma* ext
- \+/\- *lemma* map_one
- \+/\- *lemma* map_mul
- \+/\- *theorem* map_inv
- \+ *theorem* map_mul_inv
- \+ *theorem* add_monoid_hom.map_sub
- \- *theorem* map_div
- \- *theorem* map_neg
- \- *theorem* map_sub
- \- *def* ext
- \- *def* map_zero
- \- *def* map_add
- \- *def* id
- \- *def* comp
- \- *def* mk'
- \- *def* neg

Modified src/algebra/group/to_additive.lean
- \+ *theorem* mul_comm'

Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/pointwise.lean
- \- *def* pointwise_add_add_semigroup
- \- *def* pointwise_add_add_monoid

Modified src/algebra/punit_instances.lean
- \+/\- *lemma* one_eq
- \+/\- *lemma* mul_eq
- \+/\- *lemma* inv_eq

Modified src/data/dfinsupp.lean


Modified src/data/equiv/algebra.lean
- \+/\- *theorem* to_equiv_symm
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* apply_symm_apply
- \+/\- *def* symm_apply_apply
- \+/\- *def* map_one
- \- *def* map_add
- \- *def* map_zero
- \- *def* to_add_monoid_hom

Modified src/data/finsupp.lean


Modified src/data/fintype.lean


Modified src/data/list/basic.lean


Modified src/data/list/perm.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/set/finite.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* ker_mk
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_inv
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_mk'

Modified src/group_theory/subgroup.lean
- \+ *lemma* gpowers_subset
- \+ *lemma* gmultiples_subset
- \+/\- *lemma* mem_trivial
- \+/\- *lemma* closure_subgroup
- \- *lemma* mem_closure
- \- *lemma* image_closure
- \- *theorem* closure_subset
- \- *theorem* gmultiples_eq_closure
- \- *theorem* in_closure.rec_on
- \- *theorem* exists_list_of_mem_closure
- \- *theorem* closure_eq_mclosure
- \- *theorem* mem_closure_union_iff
- \- *def* trivial
- \- *def* center
- \- *def* closure

Modified src/group_theory/submonoid.lean
- \+ *lemma* powers.mul_mem
- \+ *lemma* multiples.add_mem
- \- *lemma* is_add_submonoid_Union_of_directed
- \- *lemma* image_closure
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* closure_mono
- \- *theorem* closure_singleton
- \- *theorem* exists_list_of_mem_closure
- \- *theorem* in_closure.rec_on
- \- *theorem* mem_closure_union_iff
- \- *def* closure

Modified src/linear_algebra/tensor_product.lean


Modified src/meta/expr.lean
- \+ *def* map_prefix

Modified src/order/filter/pointwise.lean
- \- *def* pointwise_add

Modified src/tactic/algebra.lean


Created src/tactic/transport.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* coe_inf
- \+/\- *lemma* le_iff
- \- *lemma* mem_nhds_zero
- \- *lemma* is_open_of_open_add_subgroup
- \- *def* prod



## [2019-08-21 03:42:10](https://github.com/leanprover-community/mathlib/commit/733f616)
chore(gitignore): ignore files generated by mk_all script ([#1328](https://github.com/leanprover-community/mathlib/pull/1328))
#### Estimated changes
Modified .gitignore




## [2019-08-21 01:39:40](https://github.com/leanprover-community/mathlib/commit/8070049)
feat(tactic/lift): add lift tactic ([#1315](https://github.com/leanprover-community/mathlib/pull/1315))
* start on lift_to tactic
* finish lift tactic
* add instance to lift rat to int
this required me to move some lemmas from rat/order to rat/basic which had nothing to do with the order on rat
* move test to test/tactic.lean
* add header and documentation
* add more/better documentation
* typo
* more documentation
* rewrite, minor
* move import
* remove can_lift attribute
now we automatically construct the simp set used to simplify
Thanks to @cipher1024 for the idea and writing the main part of this code
* remove occurrence of [can_lift]
#### Estimated changes
Modified docs/tactics.md


Modified src/data/rat/cast.lean
- \+ *lemma* coe_int_num_of_denom_eq_one

Modified src/tactic/basic.lean


Created src/tactic/lift.lean


Modified test/tactics.lean




## [2019-08-20 23:38:53](https://github.com/leanprover-community/mathlib/commit/26a3e31)
chore(category_theory/monoidal): monoidal_category doesn't extend category ([#1338](https://github.com/leanprover-community/mathlib/pull/1338))
* chore(category_theory/monoidal): monoidal_category doesn't extend category
* remove _aux file, simplifying
* make notations global, and add doc-strings
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+/\- *def* tensor_iso

Deleted src/category_theory/monoidal/category_aux.lean
- \- *def* tensor_obj_type
- \- *def* tensor_hom_type
- \- *def* assoc_obj
- \- *def* assoc_natural
- \- *def* left_unitor_obj
- \- *def* left_unitor_natural
- \- *def* right_unitor_obj
- \- *def* right_unitor_natural
- \- *def* pentagon
- \- *def* triangle

Modified src/category_theory/monoidal/functor.lean




## [2019-08-20 21:37:32](https://github.com/leanprover-community/mathlib/commit/0dbe3a9)
feat(algebra,equiv,logic): add various lemmas ([#1342](https://github.com/leanprover-community/mathlib/pull/1342))
* add various lemmas
* add simp lemma
* fix simp
* rename to subtype_sigma_equiv
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* fn_min_add_fn_max
- \+ *lemma* min_add_max
- \+ *lemma* fn_min_mul_fn_max
- \+ *lemma* min_mul_max

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_self_add_mul_self_eq_zero

Modified src/algebra/ring.lean
- \+ *lemma* Vieta_formula_quadratic

Modified src/data/equiv/basic.lean
- \+ *def* subtype_sigma_equiv

Modified src/data/list/basic.lean
- \+/\- *theorem* tfae_singleton

Modified src/logic/basic.lean
- \+ *lemma* eq_iff_iff
- \+ *lemma* eq.congr_left
- \+ *lemma* eq.congr_right



## [2019-08-20 15:42:54](https://github.com/leanprover-community/mathlib/commit/14024a3)
feat(linear_algebra/bilinear_form, linear_algebra/sesquilinear_form, ring_theory/maps): bilinear/sesquilinear forms ([#1300](https://github.com/leanprover-community/mathlib/pull/1300))
* Create involution.lean
* Update involution.lean
* Update involution.lean
* Rename involution.lean to maps.lean
* Create bilinear_form.lean
* Create sesquilinear_form.lean
* Update sesquilinear_form.lean
* Style fixes
* Update sesquilinear_form.lean
* Style fixes
* fix typo
#### Estimated changes
Created src/linear_algebra/bilinear_form.lean
- \+ *lemma* add_left
- \+ *lemma* smul_left
- \+ *lemma* add_right
- \+ *lemma* smul_right
- \+ *lemma* zero_left
- \+ *lemma* zero_right
- \+ *lemma* neg_left
- \+ *lemma* neg_right
- \+ *lemma* sub_left
- \+ *lemma* sub_right
- \+ *lemma* ext
- \+ *lemma* ortho_zero
- \+ *lemma* eq_zero
- \+ *lemma* ortho_sym
- \+ *lemma* sym
- \+ *lemma* is_refl
- \+ *lemma* self_eq_zero
- \+ *lemma* neg
- \+ *theorem* ortho_smul_left
- \+ *theorem* ortho_smul_right
- \+ *def* linear_map.to_bilin
- \+ *def* to_linear_map
- \+ *def* bilin_linear_map_equiv
- \+ *def* is_ortho
- \+ *def* is_refl
- \+ *def* is_sym
- \+ *def* is_alt

Created src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* add_left
- \+ *lemma* smul_left
- \+ *lemma* add_right
- \+ *lemma* smul_right
- \+ *lemma* zero_left
- \+ *lemma* zero_right
- \+ *lemma* neg_left
- \+ *lemma* neg_right
- \+ *lemma* sub_left
- \+ *lemma* sub_right
- \+ *lemma* ext
- \+ *lemma* ortho_zero
- \+ *lemma* eq_zero
- \+ *lemma* ortho_sym
- \+ *lemma* sym
- \+ *lemma* is_refl
- \+ *lemma* self_eq_zero
- \+ *lemma* neg
- \+ *theorem* ortho_smul_left
- \+ *theorem* ortho_smul_right
- \+ *def* is_ortho
- \+ *def* is_refl
- \+ *def* is_sym
- \+ *def* is_alt

Created src/ring_theory/maps.lean
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_add
- \+ *lemma* map_mul
- \+ *lemma* map_one
- \+ *lemma* map_neg_one
- \+ *lemma* bijective
- \+ *lemma* map_zero_iff
- \+ *theorem* comm_ring.hom_to_anti_hom
- \+ *theorem* comm_ring.anti_hom_to_hom
- \+ *def* to_ring_anti_equiv
- \+ *def* comm_ring.equiv_to_anti_equiv
- \+ *def* comm_ring.anti_equiv_to_equiv



## [2019-08-20 13:12:03](https://github.com/leanprover-community/mathlib/commit/6f747ec)
feat(data/vector2): nth_map ([#1349](https://github.com/leanprover-community/mathlib/pull/1349))
* feat(data/vector2): nth_map
* Update vector2.lean
* Update vector2.lean
#### Estimated changes
Modified src/data/vector2.lean
- \+ *lemma* nth_map



## [2019-08-20 12:14:30](https://github.com/leanprover-community/mathlib/commit/8771432)
doc(tactic/ring2): document parts of ring2 ([#1208](https://github.com/leanprover-community/mathlib/pull/1208))
* doc(tactic/ring2): document parts of ring2
* feat(data/tree): refactor binary trees into their own module
* feat(tactic/ring2): resolve correct correctness
* chore(tactic/ring2): move copyright into comment
* doc(tactic/ring2): wording
#### Estimated changes
Created src/data/tree.lean
- \+ *def* repr
- \+ *def* of_rbnode
- \+ *def* index_of
- \+ *def* get
- \+ *def* get_or_else
- \+ *def* map

Modified src/tactic/linarith.lean
- \- *def* tree.repr

Modified src/tactic/ring2.lean
- \+ *def* to_string
- \- *def* tree.get
- \- *def* tree.of_rbnode
- \- *def* tree.index_of
- \- *def* repr



## [2019-08-20 11:13:39+02:00](https://github.com/leanprover-community/mathlib/commit/f3eb8c2)
chore(data/matrix): simp attribute for transpose_tranpose ([#1350](https://github.com/leanprover-community/mathlib/pull/1350))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* transpose_transpose



## [2019-08-19 21:05:01](https://github.com/leanprover-community/mathlib/commit/5a309a3)
fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* eq_to_hom_map
- \+/\- *lemma* eq_to_iso_map
- \+/\- *lemma* eq_to_hom_app



## [2019-08-19 19:01:37](https://github.com/leanprover-community/mathlib/commit/9eefd40)
refactor(data/list/min_max): use with_top for maximum and define argmax ([#1320](https://github.com/leanprover-community/mathlib/pull/1320))
* refactor(data/list/min_max): use option for maximum and define argmax
* prove minimum_singleton
* fix build
* use with_bot for maximum
* update comments
#### Estimated changes
Modified src/data/equiv/denumerable.lean


Modified src/data/list/min_max.lean
- \+ *lemma* argmax_two_self
- \+ *lemma* argmax_nil
- \+ *lemma* argmin_nil
- \+ *lemma* argmax_singleton
- \+ *lemma* argmin_singleton
- \+ *lemma* foldl_argmax₂_eq_none
- \+ *lemma* maximum_nil
- \+ *lemma* minimum_nil
- \+ *lemma* maximum_singleton
- \+ *lemma* minimum_singleton
- \+ *theorem* argmax_mem
- \+ *theorem* argmin_mem
- \+ *theorem* argmax_eq_none
- \+ *theorem* argmin_eq_none
- \+ *theorem* le_argmax_of_mem
- \+ *theorem* argmin_le_of_mem
- \+ *theorem* argmax_concat
- \+ *theorem* argmin_concat
- \+ *theorem* argmax_cons
- \+ *theorem* argmin_cons
- \+ *theorem* index_of_argmax
- \+ *theorem* index_of_argmin
- \+ *theorem* mem_argmax_iff
- \+ *theorem* argmax_eq_some_iff
- \+ *theorem* mem_argmin_iff
- \+ *theorem* argmin_eq_some_iff
- \+/\- *theorem* maximum_mem
- \+/\- *theorem* minimum_mem
- \+ *theorem* maximum_eq_none
- \+ *theorem* minimum_eq_none
- \+/\- *theorem* le_maximum_of_mem
- \+ *theorem* minimum_le_of_mem
- \+ *theorem* le_maximum_of_mem'
- \+ *theorem* le_minimum_of_mem'
- \+ *theorem* maximum_concat
- \+ *theorem* minimum_concat
- \+ *theorem* maximum_cons
- \+ *theorem* minimum_cons
- \+ *theorem* maximum_eq_coe_iff
- \+ *theorem* minimum_eq_coe_iff
- \- *theorem* le_of_foldr_max
- \- *theorem* le_of_foldr_min
- \- *theorem* le_of_foldl_max
- \- *theorem* le_of_foldl_min
- \- *theorem* mem_foldr_max
- \- *theorem* mem_foldr_min
- \- *theorem* mem_foldl_max
- \- *theorem* mem_foldl_min
- \- *theorem* mem_maximum_aux
- \- *theorem* mem_minimum_aux
- \- *theorem* le_maximum_aux_of_mem
- \- *theorem* le_minimum_aux_of_mem
- \- *theorem* le_minimum_of_mem
- \+ *def* argmax₂
- \+ *def* argmax
- \+ *def* argmin
- \+/\- *def* maximum
- \+/\- *def* minimum
- \- *def* maximum_aux
- \- *def* minimum_aux
- \- *def* maximum_singleton
- \- *def* minimum_singleton
- \- *def* maximum_aux_cons
- \- *def* minimum_aux_cons
- \- *def* maximum_cons
- \- *def* minimum_cons

Modified src/tactic/omega/find_scalars.lean




## [2019-08-19 17:09:44](https://github.com/leanprover-community/mathlib/commit/92fa24c)
feat(data/fin): val simp lemmas ([#1347](https://github.com/leanprover-community/mathlib/pull/1347))
* feat(data/fin): val simp lemmas
* Update fin.lean
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* cast_le_val
- \+ *lemma* cast_add_val
- \+ *lemma* last_val
- \+ *lemma* cast_lt_cast_succ



## [2019-08-19 09:36:05-04:00](https://github.com/leanprover-community/mathlib/commit/6fbcc04)
feat(tactic/reassoc_axiom): produce associativity-friendly lemmas in category theory ([#1341](https://github.com/leanprover-community/mathlib/pull/1341))
#### Estimated changes
Modified docs/tactics.md
- \+ *lemma* some_lemma
- \+ *lemma* some_lemma_assoc
- \+ *lemma* some_class.bar_assoc

Modified src/category_theory/adjunction/basic.lean
- \+/\- *lemma* left_triangle_components
- \+/\- *lemma* right_triangle_components
- \+/\- *lemma* counit_naturality
- \+/\- *lemma* unit_naturality
- \- *lemma* left_triangle_components_assoc
- \- *lemma* right_triangle_components_assoc
- \- *lemma* counit_naturality_assoc
- \- *lemma* unit_naturality_assoc

Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* eq_to_hom_trans
- \- *lemma* eq_to_hom_trans_assoc

Modified src/category_theory/isomorphism.lean
- \- *lemma* hom_inv_id_assoc
- \- *lemma* inv_hom_id_assoc

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* colimit.ι_desc
- \+/\- *lemma* colimit.ι_pre
- \+/\- *lemma* colimit.ι_post
- \+/\- *lemma* colim.ι_map
- \- *lemma* colimit.ι_desc_assoc
- \- *lemma* colimit.ι_pre_assoc
- \- *lemma* colimit.ι_post_assoc
- \- *lemma* colim.ι_map_assoc

Created src/tactic/reassoc_axiom.lean
- \+ *lemma* some_lemma
- \+ *lemma* some_lemma_assoc
- \+ *lemma* foo_bar
- \+ *lemma* foo_bar_assoc



## [2019-08-19 13:15:20](https://github.com/leanprover-community/mathlib/commit/8f09b0f)
fix(tactic/omega): simplify with mul_one and one_mul ([#1344](https://github.com/leanprover-community/mathlib/pull/1344))
* Simplify multiplication by one
* Remove debug trace
* Fix integer version of omega
#### Estimated changes
Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/nat/main.lean


Modified test/omega.lean




## [2019-08-19 11:20:20](https://github.com/leanprover-community/mathlib/commit/9c1718a)
feat(tactic/obtain): make type argument optional ([#1327](https://github.com/leanprover-community/mathlib/pull/1327))
* feat(tactic/obtain): make type argument optional
* fix(tactic/obtain): unnecessary steps
* feat(tactic/obtain): simplify cases
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2019-08-18 19:43:51](https://github.com/leanprover-community/mathlib/commit/ab7d39b)
feat(data/vector2): update_nth ([#1334](https://github.com/leanprover-community/mathlib/pull/1334))
* feat(data/vector2): update_nth
* naming and docstrings
* remove double namespace fom vector.nth_mem
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* exists_iff
- \+ *lemma* forall_iff
- \+/\- *lemma* mem_find_iff
- \+/\- *lemma* find_eq_some_iff

Modified src/data/list/basic.lean
- \+ *lemma* nth_le_update_nth_eq
- \+ *lemma* nth_le_update_nth_of_ne

Modified src/data/vector2.lean
- \+ *lemma* mem_iff_nth
- \+ *lemma* nodup_iff_nth_inj
- \+ *lemma* nth_mem
- \+ *lemma* nth_update_nth_same
- \+ *lemma* nth_update_nth_of_ne
- \+ *lemma* nth_update_nth_eq_if
- \+ *def* update_nth



## [2019-08-17 20:50:04](https://github.com/leanprover-community/mathlib/commit/538d3f6)
feat(data/vector2): to_list_map ([#1335](https://github.com/leanprover-community/mathlib/pull/1335))
#### Estimated changes
Modified src/data/vector2.lean
- \+ *lemma* to_list_map



## [2019-08-17 18:55:40](https://github.com/leanprover-community/mathlib/commit/66fa499)
feat(data/list/basic): list.mem_insert_nth ([#1336](https://github.com/leanprover-community/mathlib/pull/1336))
* feat(data/list/basic): list.mem_insert_nth
* Update src/data/list/basic.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* mem_insert_nth



## [2019-08-16 10:20:57](https://github.com/leanprover-community/mathlib/commit/a1dda1e)
feat(linear_algebra/matrix): linear maps are linearly equivalent to matrices ([#1310](https://github.com/leanprover-community/mathlib/pull/1310))
* linear map to matrix (WIP)
* WIP
* feat (linear_algebra/matrix): lin_equiv_matrix
* feat (linear_algebra.basic): linear_equiv.arrow_congr, std_basis_eq_single
* change unnecessary vector_space assumption for equiv_fun_basis to module
* add docstrings and refactor
* add docstrings
* move instance to pi_instances
* add docstrings + name change
* remove duplicate instance
#### Estimated changes
Modified src/field_theory/finite_card.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* std_basis_eq_single
- \+ *def* arrow_congr
- \+/\- *def* congr_right
- \+ *def* conj

Modified src/linear_algebra/basis.lean
- \+ *theorem* module.card_fintype
- \+/\- *theorem* vector_space.card_fintype
- \- *theorem* vector_space.card_fintype'
- \+ *def* equiv_fun_basis

Modified src/linear_algebra/matrix.lean
- \+ *lemma* to_matrix_to_lin
- \+ *lemma* to_lin_to_matrix
- \+ *def* to_matrixₗ
- \+ *def* to_matrix
- \+ *def* lin_equiv_matrix'
- \+ *def* lin_equiv_matrix



## [2019-08-16 02:19:14](https://github.com/leanprover-community/mathlib/commit/2e76f36)
feat(tactic/sanity_check): add #sanity_check command ([#1318](https://github.com/leanprover-community/mathlib/pull/1318))
* create a file sanity_check
Currently it contains a tactic that detects unused arguments in declarations
In the future I want to add other cleaning tactics
* fix last tactic
* update comment
* checkpoint
* checkpoint
* rewrite sanity_check
* update sanity_check
* move results to appropriate files
* move some declarations
Some declarations in tactic.core made more sense in meta.expr
tactic.core now imports string.defs (which adds very little)
add documentation
* add entry to docs/tactic.md
* fix errors
* some extra documentation
* add test
* add doc to meta.expr
#### Estimated changes
Modified docs/tactics.md


Modified src/data/string/defs.lean
- \+ *def* popn

Modified src/meta/expr.lean


Modified src/tactic/core.lean


Created src/tactic/sanity_check.lean


Created test/sanity_check.lean
- \+ *lemma* foo3
- \+ *lemma* foo4
- \+ *def* foo1
- \+ *def* foo2



## [2019-08-16 00:19:33](https://github.com/leanprover-community/mathlib/commit/397c016)
feat(tactic/finish): parse ematch lemmas with `finish using ...` ([#1326](https://github.com/leanprover-community/mathlib/pull/1326))
* feat(tactic/finish): parse ematch lemmas with `finish using ...`
Add test
Add documentation
* Add docstrings
* Formatting and docstrings
* Clean up test
* Add even more docstrings
clean up match expressions
Fix typo
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/finish.lean


Created test/finish4.lean
- \+ *lemma* hd_rev
- \+ *theorem* log_mul'
- \+ *def* append1
- \+ *def* rev



## [2019-08-15 22:29:27](https://github.com/leanprover-community/mathlib/commit/2e90bed)
feat(analysis/complex/exponential): prove that rpow is continuous ([#1306](https://github.com/leanprover-community/mathlib/pull/1306))
* rpow is continuous
* Update exponential.lean
* Fix things
* Fix things
* Fix things
* Fix things
#### Estimated changes
Modified src/algebra/quadratic_discriminant.lean
- \+ *lemma* exists_le_mul_self
- \+ *lemma* exists_lt_mul_self
- \- *lemma* exists_le_mul
- \- *lemma* exists_lt_mul

Modified src/analysis/complex/exponential.lean
- \+ *lemma* log_lt_log
- \+ *lemma* log_lt_log_iff
- \+ *lemma* log_pos_iff
- \+ *lemma* log_pos
- \+ *lemma* log_neg_iff
- \+ *lemma* log_neg
- \+ *lemma* log_nonneg
- \+ *lemma* log_nonpos
- \+ *lemma* tendsto_log_one_zero
- \+ *lemma* continuous_log'
- \+ *lemma* continuous_at_log
- \+ *lemma* continuous_log
- \+ *lemma* rpow_def_of_pos
- \+ *lemma* rpow_def_of_neg
- \+ *lemma* rpow_def_of_nonpos
- \+ *lemma* abs_rpow_le_abs_rpow
- \+ *lemma* rpow_lt_rpow
- \+ *lemma* rpow_lt_rpow_of_exponent_lt
- \+ *lemma* rpow_le_rpow_of_exponent_le
- \+ *lemma* rpow_lt_rpow_of_exponent_gt
- \+ *lemma* rpow_le_rpow_of_exponent_ge
- \+ *lemma* one_lt_rpow
- \+ *lemma* rpow_lt_one
- \+ *lemma* continuous_rpow_aux1
- \+ *lemma* continuous_rpow_aux2
- \+ *lemma* continuous_at_rpow_of_ne_zero
- \+ *lemma* continuous_rpow_aux3
- \+ *lemma* continuous_at_rpow_of_pos
- \+ *lemma* continuous_rpow
- \+ *lemma* continuous_rpow_of_ne_zero
- \+ *lemma* continuous_rpow_of_pos
- \+ *lemma* sqrt_eq_rpow
- \+ *lemma* continuous_sqrt

Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean
- \- *lemma* continuous_sqrt

Modified src/data/complex/exponential.lean
- \+ *lemma* one_lt_exp_iff
- \+ *lemma* exp_lt_one_iff

Modified src/data/real/basic.lean
- \- *lemma* abs_sqrt_sub_sqrt_le_sqrt_abs



## [2019-08-15 20:26:47](https://github.com/leanprover-community/mathlib/commit/74c25a5)
feat(*): lemmas needed for two projects ([#1294](https://github.com/leanprover-community/mathlib/pull/1294))
* feat(multiplicity|enat): add facts needed for IMO 2019-4
* feat(*): various lemmas needed for the cubing a cube proof
* typo
* some cleanup
* fixes, add choose_two_right
* projections for associated.prime and irreducible
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* pow_dvd_pow_iff
- \+ *lemma* ne_zero
- \+ *lemma* not_unit
- \+ *lemma* div_or_div
- \+/\- *lemma* not_prime_zero
- \+ *lemma* is_unit_or_is_unit
- \+ *lemma* prime.ne_zero
- \+ *lemma* prime.ne_one
- \+ *lemma* prime.le_or_le
- \+ *theorem* irreducible.ne_zero
- \- *theorem* ne_zero_of_irreducible

Modified src/algebra/big_operators.lean
- \+ *lemma* prod_nat_cast
- \+ *lemma* prod_nonneg
- \+ *lemma* prod_pos
- \+ *lemma* prod_le_prod

Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean
- \+ *lemma* add_le_iff_nonpos_left
- \+ *lemma* add_le_iff_nonpos_right
- \+ *lemma* add_lt_iff_neg_right
- \+ *lemma* add_lt_iff_neg_left

Modified src/data/fin.lean
- \+ *lemma* forall_fin_succ
- \+ *lemma* exists_fin_succ
- \+ *lemma* tail_cons
- \+ *lemma* cons_succ
- \+ *lemma* cons_zero
- \+ *def* tail
- \+ *def* cons

Modified src/data/finset.lean
- \+ *lemma* exists_min

Modified src/data/multiset.lean
- \+ *theorem* multiset.map_eq_zero

Modified src/data/nat/basic.lean
- \+ *lemma* triangle_succ
- \+ *lemma* monotone_fact
- \+ *lemma* fact_lt
- \+ *lemma* one_lt_fact
- \+ *lemma* fact_eq_one
- \+ *lemma* fact_inj
- \+ *lemma* choose_two_right

Modified src/data/nat/enat.lean
- \+ *lemma* top_eq_none
- \+ *lemma* ne_top_iff
- \+ *lemma* ne_top_of_lt
- \+ *lemma* lt_add_one
- \+ *lemma* le_of_lt_add_one
- \+ *lemma* add_one_le_of_lt
- \+ *lemma* add_one_le_iff_lt
- \+ *lemma* lt_add_one_iff_lt

Modified src/data/padics/padic_norm.lean


Modified src/data/pfun.lean
- \+ *lemma* some_ne_none
- \+ *lemma* ne_none_iff

Modified src/data/set/finite.lean
- \+ *lemma* exists_min

Modified src/data/set/intervals.lean
- \+ *lemma* eq_of_Ico_disjoint
- \+ *lemma* nonempty_Ico_sdiff

Modified src/data/set/lattice.lean
- \+ *lemma* not_disjoint_iff

Modified src/field_theory/splitting_field.lean


Modified src/order/basic.lean
- \+ *lemma* reflect_lt

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity_lt_iff_neg_dvd
- \+ *lemma* multiplicity_add_of_gt
- \+ *lemma* multiplicity_sub_of_gt
- \+ *lemma* multiplicity_add_eq_min
- \+ *lemma* finset.prod
- \+ *lemma* multiplicity_pow_self
- \+ *lemma* multiplicity_pow_self_of_prime

Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2019-08-15 18:18:27](https://github.com/leanprover-community/mathlib/commit/fa68342)
feat(data/rat): move lemmas to right file, add nat cast lemmas, remove ([#1333](https://github.com/leanprover-community/mathlib/pull/1333))
redundant lemma
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *theorem* of_int_eq_mk

Modified src/data/rat/cast.lean
- \+ *theorem* coe_int_eq_mk
- \+ *theorem* mk_eq_div
- \+ *theorem* coe_int_eq_of_int
- \+ *theorem* coe_nat_eq_mk

Modified src/data/rat/floor.lean


Modified src/data/rat/order.lean
- \- *theorem* mk_le
- \- *theorem* of_int_eq_mk
- \- *theorem* coe_int_eq_mk
- \- *theorem* coe_int_eq_of_int
- \- *theorem* mk_eq_div



## [2019-08-15 15:09:08](https://github.com/leanprover-community/mathlib/commit/73cc56c)
refactor(data/fintype): shorten proof of card_eq ([#1332](https://github.com/leanprover-community/mathlib/pull/1332))
#### Estimated changes
Modified src/data/fintype.lean




## [2019-08-15 11:27:01](https://github.com/leanprover-community/mathlib/commit/ebbbb76)
doc(contribute/style): remove outdated syntax [ci skip] ([#1329](https://github.com/leanprover-community/mathlib/pull/1329))
* doc(contribute/style): remove outdated syntax [ci skip]
* doc(contribute/style): mistaken find/replace
#### Estimated changes
Modified docs/contribute/style.md
- \+/\- *theorem* mem_split
- \+/\- *theorem* add_right_inj



## [2019-08-15 10:26:30](https://github.com/leanprover-community/mathlib/commit/3d512f7)
chore(category_theory/isomorphism): docstring, DRY, add some trivial lemmas ([#1309](https://github.com/leanprover-community/mathlib/pull/1309))
- add module docstring;
- use `as_iso` more aggressively to avoid repeating proofs;
- add more trivial lemmas.
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *lemma* symm_symm_eq
- \+ *lemma* symm_eq_iff
- \+/\- *lemma* refl_symm
- \+/\- *lemma* trans_symm
- \+ *lemma* trans_assoc
- \+ *lemma* refl_trans
- \+ *lemma* trans_refl
- \+ *lemma* symm_self_id
- \+ *lemma* self_symm_id
- \+ *lemma* symm_self_id_assoc
- \+ *lemma* self_symm_id_assoc
- \+/\- *lemma* as_iso_hom
- \+/\- *lemma* as_iso_inv
- \+/\- *lemma* hom_inv_id
- \+/\- *lemma* inv_hom_id
- \+/\- *lemma* hom_inv_id_assoc
- \+/\- *lemma* inv_hom_id_assoc
- \+/\- *lemma* inv_id
- \+/\- *lemma* inv_comp
- \+/\- *lemma* is_iso.inv_inv
- \+/\- *lemma* iso.inv_inv
- \+/\- *lemma* iso.inv_hom
- \+ *lemma* map_iso_symm
- \+/\- *lemma* map_inv
- \+/\- *def* as_iso
- \- *def* inv



## [2019-08-15 05:08:24](https://github.com/leanprover-community/mathlib/commit/e48ad0d)
chore(*): migrate `units.map` to bundled homs ([#1331](https://github.com/leanprover-community/mathlib/pull/1331))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* is_unit.map
- \+ *lemma* is_unit.map'
- \+ *theorem* is_unit.mk0

Modified src/algebra/group/hom.lean
- \+ *lemma* coe_as_monoid_hom
- \+ *def* as_monoid_hom

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* coe_map
- \+ *lemma* coe_map'
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+ *lemma* coe_hom_apply
- \+ *def* map
- \+ *def* map'
- \+ *def* coe_hom

Modified src/data/equiv/algebra.lean


Modified src/data/polynomial.lean


Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series.lean




## [2019-08-14 18:01:25](https://github.com/leanprover-community/mathlib/commit/02548ad)
fix(data/mllist): fix off-by-one bug in mllist.take ([#1298](https://github.com/leanprover-community/mathlib/pull/1298))
* Update mllist.lean
Changed `n` to `n+1` in line 72. This fixes a bug in the `take` function for monadic lazy lists (mllist).
* add a test showing correct behaviour of take
#### Estimated changes
Modified src/data/mllist.lean


Modified test/mllist.lean




## [2019-08-14 15:58:41](https://github.com/leanprover-community/mathlib/commit/0bc4a40)
feat(data/pequiv): symm_single_apply ([#1324](https://github.com/leanprover-community/mathlib/pull/1324))
#### Estimated changes
Modified src/data/pequiv.lean
- \+ *lemma* symm_single_apply



## [2019-08-13 15:12:57](https://github.com/leanprover-community/mathlib/commit/2a131d9)
fix(.github): typo ([#1323](https://github.com/leanprover-community/mathlib/pull/1323))
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2019-08-13 15:19:45+02:00](https://github.com/leanprover-community/mathlib/commit/5796465)
fix(algebra/ring): fix typo in docstring ([#1322](https://github.com/leanprover-community/mathlib/pull/1322))
#### Estimated changes
Modified src/algebra/ring.lean




## [2019-08-12 17:42:15](https://github.com/leanprover-community/mathlib/commit/900c53a)
feat(scripts): add scripts to import all mathlib files ([#1281](https://github.com/leanprover-community/mathlib/pull/1281))
* add scripts to import all mathlib files
mk_all makes a file all.lean in each subdirectory of src/, importing all files in that directory, including subdirectories
rm_all removes the files all.lean
* also delete all.olean files
* remove unnecessary maxdepth
* add comments, and generate comments
#### Estimated changes
Created scripts/mk_all.sh


Created scripts/rm_all.sh




## [2019-08-12 17:59:16+02:00](https://github.com/leanprover-community/mathlib/commit/df1fb07)
doc(contribute): add link to doc requirements ([#1317](https://github.com/leanprover-community/mathlib/pull/1317))
#### Estimated changes
Modified docs/contribute/index.md




## [2019-08-12 15:28:09](https://github.com/leanprover-community/mathlib/commit/92a5424)
feat(data/fin): mem_find_iff ([#1307](https://github.com/leanprover-community/mathlib/pull/1307))
* feat(data/fin): mem_find_iff
* add find_eq_some_iff ([#1308](https://github.com/leanprover-community/mathlib/pull/1308))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* mem_find_iff
- \+ *lemma* find_eq_some_iff



## [2019-08-12 13:41:27](https://github.com/leanprover-community/mathlib/commit/f46b0dc)
feat(algebra/ordered_field): le_div_iff_of_neg ([#1311](https://github.com/leanprover-community/mathlib/pull/1311))
* feat(algebra/ordered_field): le_div_iff_of_neg
* Update ordered_field.lean
* Update ordered_field.lean
* Update ordered_field.lean
* Update ordered_field.lean
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* le_div_iff_of_neg



## [2019-08-12 11:55:24](https://github.com/leanprover-community/mathlib/commit/3bd3dcd)
feat(data/option/basic): bind_eq_none' ([#1312](https://github.com/leanprover-community/mathlib/pull/1312))
* feat(data/option/basic): bind_eq_none'
* Update basic.lean
* fix build and add simp
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *theorem* bind_eq_none'
- \+/\- *theorem* bind_eq_none



## [2019-08-12 10:14:40](https://github.com/leanprover-community/mathlib/commit/01cb33c)
feat(algebra/ordered_ring): pos_of_mul_neg_left and similar ([#1313](https://github.com/leanprover-community/mathlib/pull/1313))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* nonpos_of_mul_nonneg_left
- \+ *lemma* nonpos_of_mul_nonneg_right
- \+ *lemma* neg_of_mul_pos_left
- \+ *lemma* neg_of_mul_pos_right
- \+ *lemma* nonneg_of_mul_nonpos_left
- \+ *lemma* nonneg_of_mul_nonpos_right
- \+ *lemma* pos_of_mul_neg_left
- \+ *lemma* pos_of_mul_neg_right



## [2019-08-11 09:21:07](https://github.com/leanprover-community/mathlib/commit/37d4eda)
Delete repeated item ([#1316](https://github.com/leanprover-community/mathlib/pull/1316))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean




## [2019-08-10 04:04:40](https://github.com/leanprover-community/mathlib/commit/3aad7f1)
feat(data/matrix/pequiv): partial equivalences to represent matrices ([#1228](https://github.com/leanprover-community/mathlib/pull/1228))
* feat(matrix/pequiv): partial equivalences to represent matrices
* use notation for pequiv
* correct imports
* finish correcting imports
* add some docs
* Add documentation
* improve documentation
#### Estimated changes
Renamed src/data/matrix.lean to src/data/matrix/basic.lean


Created src/data/matrix/pequiv.lean
- \+ *lemma* to_matrix_symm
- \+ *lemma* to_matrix_refl
- \+ *lemma* mul_matrix_apply
- \+ *lemma* matrix_mul_apply
- \+ *lemma* to_matrix_trans
- \+ *lemma* to_matrix_bot
- \+ *lemma* to_matrix_injective
- \+ *lemma* to_matrix_swap
- \+ *lemma* single_mul_single
- \+ *lemma* single_mul_single_of_ne
- \+ *lemma* single_mul_single_right
- \+ *def* to_matrix

Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean




## [2019-08-09 09:57:38](https://github.com/leanprover-community/mathlib/commit/a79794a)
feat(archive): add archive ([#1295](https://github.com/leanprover-community/mathlib/pull/1295))
* feat(archive): add archive
* reformulate sentence
#### Estimated changes
Modified .travis.yml


Created archive/README.md




## [2019-08-08 14:14:07+02:00](https://github.com/leanprover-community/mathlib/commit/dd4db5f)
fix(tactic/linarith): handle neq goals ([#1303](https://github.com/leanprover-community/mathlib/pull/1303))
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-08-08 02:35:57](https://github.com/leanprover-community/mathlib/commit/9c4dd95)
feat (analysis/normed_space): Define real inner product space ([#1248](https://github.com/leanprover-community/mathlib/pull/1248))
* Inner product space
* Change the definition of inner_product_space
The original definition introduces an instance loop.
See Zulip talks: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/ring.20tactic.20works.20at.20one.20place.2C.20fails.20at.20another
* Orthogonal Projection
Prove the existence of orthogonal projections onto complete subspaces in an inner product space.
* Fix names
* small fixes
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+ *lemma* one_div_le_one_div
- \+ *lemma* one_div_lt_one_div

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_self_le_mul_self_of_le_of_neg_le

Created src/algebra/quadratic_discriminant.lean
- \+ *lemma* exists_le_mul
- \+ *lemma* exists_lt_mul
- \+ *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+ *lemma* quadratic_eq_zero_iff
- \+ *lemma* exist_quadratic_eq_zero
- \+ *lemma* quadratic_eq_zero_iff_of_discrim_eq_zero
- \+ *lemma* quadratic_ne_zero_of_discrim_ne_square
- \+ *lemma* discriminant_le_zero
- \+ *lemma* discriminant_lt_zero
- \+ *def* discrim

Modified src/analysis/convex.lean
- \+ *lemma* convex_submodule
- \+ *lemma* convex_subspace

Created src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* inner_comm
- \+ *lemma* inner_self_nonneg
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_smul_left
- \+ *lemma* inner_smul_right
- \+ *lemma* inner_zero_left
- \+ *lemma* inner_zero_right
- \+ *lemma* inner_self_eq_zero
- \+ *lemma* inner_neg_left
- \+ *lemma* inner_neg_right
- \+ *lemma* inner_neg_neg
- \+ *lemma* inner_sub_left
- \+ *lemma* inner_sub_right
- \+ *lemma* inner_add_add_self
- \+ *lemma* inner_sub_sub_self
- \+ *lemma* parallelogram_law
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* norm_eq_sqrt_inner
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* norm_add_pow_two
- \+ *lemma* norm_add_mul_self
- \+ *lemma* norm_sub_pow_two
- \+ *lemma* norm_sub_mul_self
- \+ *lemma* abs_inner_le_norm
- \+ *lemma* parallelogram_law_with_norm
- \+ *theorem* exists_norm_eq_infi_of_complete_convex
- \+ *theorem* norm_eq_infi_iff_inner_le_zero
- \+ *theorem* exists_norm_eq_infi_of_complete_subspace
- \+ *theorem* norm_eq_infi_iff_inner_eq_zero

Modified src/analysis/specific_limits.lean
- \+ *lemma* continuous_sqrt

Modified src/data/real/basic.lean
- \+ *lemma* abs_sqrt_sub_sqrt_le_sqrt_abs
- \+/\- *theorem* Sup_univ

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* exists_lt_of_lt_csupr
- \+ *lemma* exists_lt_of_cinfi_lt

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq_tendsto_of_is_complete



## [2019-08-07 07:50:47](https://github.com/leanprover-community/mathlib/commit/a2a867e)
feat(algebra/ring): bundled semiring homs ([#1305](https://github.com/leanprover-community/mathlib/pull/1305))
* added bundled ring homs
* removed comment
* Tidy and making docstrings consistent
* fix spacing
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* fix typo
Co-Authored-By: Johan Commelin <johan@commelin.net>
* whoops, actually removing instances
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* map_zero
- \+ *lemma* map_one
- \+ *lemma* map_add
- \+ *lemma* map_mul
- \+ *theorem* ext
- \+ *theorem* map_neg
- \+ *theorem* map_sub
- \+ *def* id
- \+ *def* comp
- \+ *def* mk'



## [2019-08-06 15:58:05+02:00](https://github.com/leanprover-community/mathlib/commit/57c1d6d)
chore(data/matrix): protect some lemmas ([#1304](https://github.com/leanprover-community/mathlib/pull/1304))
#### Estimated changes
Modified src/data/matrix.lean
- \- *theorem* mul_zero
- \- *theorem* zero_mul
- \- *theorem* mul_add
- \- *theorem* add_mul



## [2019-08-05 21:37:42](https://github.com/leanprover-community/mathlib/commit/88ad3cf)
feat(tactic/push_neg): add optional name argument to contrapose ([#1302](https://github.com/leanprover-community/mathlib/pull/1302))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/push_neg.lean


Modified test/push_neg.lean




## [2019-08-05 15:01:21](https://github.com/leanprover-community/mathlib/commit/de83205)
refactor(algebra/big_operators) delete duplicates and change names ([#1301](https://github.com/leanprover-community/mathlib/pull/1301))
* refactor(algebra/big_operators) delete duplicates and change names
* fix build
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* sum_le_sum
- \+ *lemma* sum_nonneg
- \+ *lemma* sum_nonpos
- \- *lemma* zero_le_sum
- \- *lemma* sum_le_zero
- \- *lemma* sum_le_sum'
- \- *lemma* zero_le_sum'
- \- *lemma* sum_le_zero'

Modified src/analysis/convex.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/ennreal.lean


Modified src/measure_theory/integration.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/instances/ennreal.lean




## [2019-08-05 09:15:59](https://github.com/leanprover-community/mathlib/commit/fc56c85)
feat(algebra/order_functions): abs_nonpos_iff ([#1299](https://github.com/leanprover-community/mathlib/pull/1299))
* feat(algebra/ordered_group): abs_nonpos_iff
* Update ordered_group.lean
* move to order_functions
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* abs_nonpos_iff



## [2019-08-04 04:21:08](https://github.com/leanprover-community/mathlib/commit/b46665f)
chore(ring_theory/algebra): make first type argument explicit in alg_hom ([#1296](https://github.com/leanprover-community/mathlib/pull/1296))
* chore(ring_theory/algebra): make first type argument explicit in alg_hom
Now this works, and it didn't work previously even with `@`
```lean
structure alg_equiv (α β γ : Type*) [comm_ring α] [ring β] [ring γ]
  [algebra α β] [algebra α γ] extends alg_hom α β γ :=
```
* Update algebra.lean
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2019-08-03 04:14:56](https://github.com/leanprover-community/mathlib/commit/27d34b3)
feat(algebra/direct_limit): discrete_field ([#1293](https://github.com/leanprover-community/mathlib/pull/1293))
#### Estimated changes
Modified src/algebra/direct_limit.lean




## [2019-08-02 17:15:07](https://github.com/leanprover-community/mathlib/commit/8fe73f3)
feat(data/fintype): psigma.fintype ([#1291](https://github.com/leanprover-community/mathlib/pull/1291))
* feat(data/fintype): psigma.fintype
* Update fintype.lean
* Swap instance argument order
#### Estimated changes
Modified src/data/fintype.lean




## [2019-08-02 15:14:38](https://github.com/leanprover-community/mathlib/commit/3af92be)
feat(algebra/module): linear_map.coe_mk ([#1290](https://github.com/leanprover-community/mathlib/pull/1290))
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* coe_mk



## [2019-08-02 14:52:18](https://github.com/leanprover-community/mathlib/commit/1061238)
feat(topology): category of uniform spaces ([#1275](https://github.com/leanprover-community/mathlib/pull/1275))
* feat(category_theory): uniform spaces
* feat(topology/uniform_spaces): CpltSepUniformSpace is a reflective subcategory
#### Estimated changes
Created src/topology/uniform_space/UniformSpace.lean
- \+ *lemma* completion_hom_val
- \+ *lemma* extension_hom_val
- \+ *lemma* extension_comp_coe
- \+ *def* UniformSpace
- \+ *def* of
- \+ *def* forget_to_Top
- \+ *def* forget_to_Type_via_Top
- \+ *def* to_UniformSpace
- \+ *def* forget_to_UniformSpace
- \+ *def* forget
- \+ *def* forget_to_Type_via_UniformSpace
- \+ *def* completion_hom

Modified src/topology/uniform_space/completion.lean
- \+ *lemma* extension_comp_coe
- \+/\- *lemma* map_id



## [2019-08-02 12:48:54](https://github.com/leanprover-community/mathlib/commit/5b4b208)
feat(data/fintype): univ_unique ([#1289](https://github.com/leanprover-community/mathlib/pull/1289))
#### Estimated changes
Modified src/data/fintype.lean
- \+ *lemma* univ_unique



## [2019-08-01 17:01:15](https://github.com/leanprover-community/mathlib/commit/766807f)
feat(data/rat): refactor into smaller files and add documentation ([#1284](https://github.com/leanprover-community/mathlib/pull/1284))
#### Estimated changes
Modified docs/contribute/doc.md


Modified src/algebra/archimedean.lean


Modified src/data/fp/basic.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/rat/basic.lean
- \- *theorem* mk_nonneg
- \- *theorem* nonneg_iff_zero_le
- \- *theorem* num_nonneg_iff_zero_le
- \- *theorem* mk_le
- \- *theorem* num_pos_iff_pos
- \- *theorem* of_int_eq_mk
- \- *theorem* coe_int_eq_mk
- \- *theorem* coe_int_eq_of_int
- \- *theorem* mk_eq_div
- \- *theorem* le_floor
- \- *theorem* floor_lt
- \- *theorem* floor_le
- \- *theorem* lt_succ_floor
- \- *theorem* floor_coe
- \- *theorem* floor_mono
- \- *theorem* floor_add_int
- \- *theorem* floor_sub_int
- \- *theorem* ceil_le
- \- *theorem* le_ceil
- \- *theorem* ceil_coe
- \- *theorem* ceil_mono
- \- *theorem* ceil_add_int
- \- *theorem* ceil_sub_int
- \- *theorem* cast_of_int
- \- *theorem* cast_coe_int
- \- *theorem* coe_int_num
- \- *theorem* coe_int_denom
- \- *theorem* coe_nat_num
- \- *theorem* coe_nat_denom
- \- *theorem* cast_coe_nat
- \- *theorem* cast_zero
- \- *theorem* cast_one
- \- *theorem* mul_cast_comm
- \- *theorem* cast_mk_of_ne_zero
- \- *theorem* cast_add_of_ne_zero
- \- *theorem* cast_neg
- \- *theorem* cast_sub_of_ne_zero
- \- *theorem* cast_mul_of_ne_zero
- \- *theorem* cast_inv_of_ne_zero
- \- *theorem* cast_div_of_ne_zero
- \- *theorem* cast_inj
- \- *theorem* cast_injective
- \- *theorem* cast_eq_zero
- \- *theorem* cast_ne_zero
- \- *theorem* eq_cast_of_ne_zero
- \- *theorem* eq_cast
- \- *theorem* cast_mk
- \- *theorem* cast_add
- \- *theorem* cast_sub
- \- *theorem* cast_mul
- \- *theorem* cast_inv
- \- *theorem* cast_div
- \- *theorem* cast_pow
- \- *theorem* cast_bit0
- \- *theorem* cast_bit1
- \- *theorem* cast_nonneg
- \- *theorem* cast_le
- \- *theorem* cast_lt
- \- *theorem* cast_nonpos
- \- *theorem* cast_pos
- \- *theorem* cast_lt_zero
- \- *theorem* cast_id
- \- *theorem* cast_min
- \- *theorem* cast_max
- \- *theorem* cast_abs
- \- *theorem* nat_ceil_le
- \- *theorem* lt_nat_ceil
- \- *theorem* le_nat_ceil
- \- *theorem* nat_ceil_mono
- \- *theorem* nat_ceil_coe
- \- *theorem* nat_ceil_zero
- \- *theorem* nat_ceil_add_nat
- \- *theorem* nat_ceil_lt_add_one
- \- *theorem* abs_def
- \- *theorem* sqrt_eq
- \- *theorem* exists_mul_self
- \- *theorem* sqrt_nonneg
- \- *def* floor
- \- *def* ceil
- \- *def* nat_ceil
- \- *def* sqrt

Created src/data/rat/cast.lean
- \+ *theorem* cast_of_int
- \+ *theorem* cast_coe_int
- \+ *theorem* coe_int_num
- \+ *theorem* coe_int_denom
- \+ *theorem* coe_nat_num
- \+ *theorem* coe_nat_denom
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_one
- \+ *theorem* mul_cast_comm
- \+ *theorem* cast_mk_of_ne_zero
- \+ *theorem* cast_add_of_ne_zero
- \+ *theorem* cast_neg
- \+ *theorem* cast_sub_of_ne_zero
- \+ *theorem* cast_mul_of_ne_zero
- \+ *theorem* cast_inv_of_ne_zero
- \+ *theorem* cast_div_of_ne_zero
- \+ *theorem* cast_inj
- \+ *theorem* cast_injective
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero
- \+ *theorem* eq_cast_of_ne_zero
- \+ *theorem* eq_cast
- \+ *theorem* cast_mk
- \+ *theorem* cast_add
- \+ *theorem* cast_sub
- \+ *theorem* cast_mul
- \+ *theorem* cast_inv
- \+ *theorem* cast_div
- \+ *theorem* cast_pow
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1
- \+ *theorem* cast_nonneg
- \+ *theorem* cast_le
- \+ *theorem* cast_lt
- \+ *theorem* cast_nonpos
- \+ *theorem* cast_pos
- \+ *theorem* cast_lt_zero
- \+ *theorem* cast_id
- \+ *theorem* cast_min
- \+ *theorem* cast_max
- \+ *theorem* cast_abs

Created src/data/rat/default.lean


Modified src/data/rat/denumerable.lean


Created src/data/rat/floor.lean
- \+ *lemma* floor_def
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
- \+ *def* floor
- \+ *def* ceil
- \+ *def* nat_ceil

Created src/data/rat/order.lean
- \+ *theorem* mk_nonneg
- \+ *theorem* nonneg_iff_zero_le
- \+ *theorem* num_nonneg_iff_zero_le
- \+ *theorem* mk_le
- \+ *theorem* num_pos_iff_pos
- \+ *theorem* of_int_eq_mk
- \+ *theorem* coe_int_eq_mk
- \+ *theorem* coe_int_eq_of_int
- \+ *theorem* mk_eq_div
- \+ *theorem* abs_def
- \+ *theorem* sqrt_eq
- \+ *theorem* exists_mul_self
- \+ *theorem* sqrt_nonneg
- \+ *def* sqrt

Modified src/tactic/norm_num.lean




## [2019-08-01 15:02:26](https://github.com/leanprover-community/mathlib/commit/0d66c87)
feat(data/seq): add ext proof, nats def, zip_with lemmas, and extract seq property ([#1278](https://github.com/leanprover-community/mathlib/pull/1278))
#### Estimated changes
Modified src/data/seq/seq.lean
- \+ *lemma* ge_stable
- \+ *lemma* nats_nth
- \+ *lemma* zip_with_nth_some
- \+ *lemma* zip_with_nth_none
- \+ *lemma* zip_with_nth_none'
- \+ *def* stream.is_seq
- \+/\- *def* seq
- \+ *def* nats

Modified src/data/seq/wseq.lean


