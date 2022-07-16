## [2019-08-31 22:37:28](https://github.com/leanprover-community/mathlib/commit/df65dde)
feat(data/option/basic): eq_some_iff_get_eq ([#1370](https://github.com/leanprover-community/mathlib/pull/1370))
* feat(data/option/basic): eq_some_iff_get_eq
* Update basic.lean
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.eq_some_iff_get_eq



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
- \+ *def* category_theory.limits.is_colimit.iso_unique_cocone_morphism
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_fac
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_fac
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_of_cocone
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.colimit_cocone
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone_of_hom
- \+ *def* category_theory.limits.is_colimit.of_nat_iso
- \- *def* category_theory.limits.is_colimit.unique
- \+ *def* category_theory.limits.is_colimit.unique_up_to_iso
- \- *def* category_theory.limits.is_colimit_iso_unique_cocone_morphism
- \+ *def* category_theory.limits.is_limit.iso_unique_cone_morphism
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_fac
- \+ *def* category_theory.limits.is_limit.of_nat_iso.cone_of_hom
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_fac
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_of_cone
- \+ *def* category_theory.limits.is_limit.of_nat_iso.hom_of_cone
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.hom_of_cone_of_hom
- \+ *def* category_theory.limits.is_limit.of_nat_iso.limit_cone
- \+ *def* category_theory.limits.is_limit.of_nat_iso
- \- *def* category_theory.limits.is_limit.unique
- \+ *def* category_theory.limits.is_limit.unique_up_to_iso
- \- *def* category_theory.limits.is_limit_iso_unique_cone_morphism

Modified src/category_theory/limits/preserves.lean




## [2019-08-30 20:07:24](https://github.com/leanprover-community/mathlib/commit/455f060)
chore(unicode): improve arrows ([#1373](https://github.com/leanprover-community/mathlib/pull/1373))
* chore(unicode): improve arrows
* grammar
Co-Authored-By: Johan Commelin <johan@commelin.net>
* moar
#### Estimated changes
Modified docs/extras/simp.md


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
- \+ *def* binder_info.brackets

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
- \- *def* I_0
- \- *def* I_1
- \+ *def* I₀
- \+ *def* I₁
- \+/\- *def* X
- \+/\- *def* Y
- \+/\- *def* cylinder
- \- *def* cylinder_0
- \- *def* cylinder_1
- \+ *def* cylinder₀
- \+ *def* cylinder₁
- \- *def* d
- \+/\- *def* mapping_cone
- \+/\- *def* mapping_cylinder
- \- *def* mapping_cylinder_0
- \+ *def* mapping_cylinder₀
- \- *def* w

Modified src/category_theory/discrete_category.lean
- \+/\- *def* category_theory.functor.of_function
- \+ *lemma* category_theory.functor.of_function_map
- \+ *lemma* category_theory.functor.of_function_obj
- \+/\- *def* category_theory.nat_iso.of_isos
- \+/\- *def* category_theory.nat_trans.of_function
- \+ *lemma* category_theory.nat_trans.of_function_app
- \+/\- *def* category_theory.nat_trans.of_homs

Modified src/category_theory/functor_category.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.lim.map_π
- \+/\- *lemma* category_theory.limits.limit.lift_π

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.binary_cofan.mk_π_app_left
- \+ *lemma* category_theory.limits.binary_cofan.mk_π_app_right
- \+ *lemma* category_theory.limits.binary_fan.mk_π_app_left
- \+ *lemma* category_theory.limits.binary_fan.mk_π_app_right
- \+ *def* category_theory.limits.coprod.associator
- \+ *def* category_theory.limits.coprod.braiding
- \+ *abbreviation* category_theory.limits.coprod.desc
- \+ *abbreviation* category_theory.limits.coprod.inl
- \+ *abbreviation* category_theory.limits.coprod.inr
- \+ *def* category_theory.limits.coprod.left_unitor
- \+ *abbreviation* category_theory.limits.coprod.map
- \+ *def* category_theory.limits.coprod.right_unitor
- \+ *lemma* category_theory.limits.coprod.symmetry
- \+ *abbreviation* category_theory.limits.coprod
- \+ *def* category_theory.limits.map_pair
- \+ *lemma* category_theory.limits.map_pair_left
- \+ *lemma* category_theory.limits.map_pair_right
- \+ *lemma* category_theory.limits.pair_obj_left
- \+ *lemma* category_theory.limits.pair_obj_right
- \+ *def* category_theory.limits.prod.associator
- \+ *def* category_theory.limits.prod.braiding
- \+ *abbreviation* category_theory.limits.prod.fst
- \+ *def* category_theory.limits.prod.left_unitor
- \+ *abbreviation* category_theory.limits.prod.lift
- \+ *abbreviation* category_theory.limits.prod.map
- \+ *def* category_theory.limits.prod.right_unitor
- \+ *abbreviation* category_theory.limits.prod.snd
- \+ *lemma* category_theory.limits.prod.symmetry
- \+ *abbreviation* category_theory.limits.prod
- \+/\- *inductive* category_theory.limits.walking_pair

Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.coequalizer.condition
- \+ *abbreviation* category_theory.limits.coequalizer.desc
- \+ *abbreviation* category_theory.limits.coequalizer.π
- \+ *abbreviation* category_theory.limits.coequalizer
- \+ *lemma* category_theory.limits.equalizer.condition
- \+ *abbreviation* category_theory.limits.equalizer.lift
- \+ *abbreviation* category_theory.limits.equalizer.ι
- \+ *abbreviation* category_theory.limits.equalizer

Added src/category_theory/limits/shapes/finite_limits.lean


Added src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/products.lean
- \+ *lemma* category_theory.limits.cofan.mk_π_app
- \+ *lemma* category_theory.limits.fan.mk_π_app
- \+ *abbreviation* category_theory.limits.pi.lift
- \+ *abbreviation* category_theory.limits.pi.map
- \+ *abbreviation* category_theory.limits.pi.π
- \+ *abbreviation* category_theory.limits.pi_obj
- \+ *abbreviation* category_theory.limits.sigma.desc
- \+ *abbreviation* category_theory.limits.sigma.map
- \+ *abbreviation* category_theory.limits.sigma.ι
- \+ *abbreviation* category_theory.limits.sigma_obj

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.pullback.condition
- \+ *abbreviation* category_theory.limits.pullback.fst
- \+ *abbreviation* category_theory.limits.pullback.lift
- \+ *abbreviation* category_theory.limits.pullback.snd
- \+ *abbreviation* category_theory.limits.pullback
- \+/\- *lemma* category_theory.limits.pullback_cone.condition
- \+ *abbreviation* category_theory.limits.pullback_cone.fst
- \+/\- *def* category_theory.limits.pullback_cone.mk
- \+ *abbreviation* category_theory.limits.pullback_cone.snd
- \- *def* category_theory.limits.pullback_cone.π₁
- \- *def* category_theory.limits.pullback_cone.π₂
- \+ *lemma* category_theory.limits.pushout.condition
- \+ *abbreviation* category_theory.limits.pushout.desc
- \+ *abbreviation* category_theory.limits.pushout.inl
- \+ *abbreviation* category_theory.limits.pushout.inr
- \+ *abbreviation* category_theory.limits.pushout
- \+/\- *lemma* category_theory.limits.pushout_cocone.condition
- \+ *abbreviation* category_theory.limits.pushout_cocone.inl
- \+ *abbreviation* category_theory.limits.pushout_cocone.inr
- \+/\- *def* category_theory.limits.pushout_cocone.mk
- \- *def* category_theory.limits.pushout_cocone.ι₁
- \- *def* category_theory.limits.pushout_cocone.ι₂

Added src/category_theory/limits/shapes/terminal.lean
- \+ *abbreviation* category_theory.limits.initial.to
- \+ *abbreviation* category_theory.limits.initial
- \+ *abbreviation* category_theory.limits.terminal.from
- \+ *abbreviation* category_theory.limits.terminal

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
- \+ *def* Mon.hom_equiv_monoid_hom

Modified src/category_theory/single_obj.lean
- \+/\- *def* category_theory.single_obj.map_hom
- \+/\- *lemma* category_theory.single_obj.map_hom_comp
- \- *def* category_theory.single_obj.map_hom_equiv
- \+/\- *lemma* category_theory.single_obj.map_hom_id
- \+/\- *def* category_theory.single_obj.to_End
- \+/\- *lemma* category_theory.single_obj.to_End_def
- \- *def* category_theory.single_obj.to_End_equiv
- \+ *lemma* monoid_hom.comp_to_functor
- \+ *lemma* monoid_hom.id_to_functor
- \+ *def* monoid_hom.to_functor
- \+ *def* units.to_Aut
- \+ *lemma* units.to_Aut_hom
- \+ *lemma* units.to_Aut_inv



## [2019-08-28 16:20:58](https://github.com/leanprover-community/mathlib/commit/d4c1c0f)
fix(tactic.basic): add sanity_check import ([#1365](https://github.com/leanprover-community/mathlib/pull/1365))
#### Estimated changes
Modified src/tactic/basic.lean




## [2019-08-28 10:14:09](https://github.com/leanprover-community/mathlib/commit/721d67a)
fix(topology/uniform_space): sanity_check pass ([#1364](https://github.com/leanprover-community/mathlib/pull/1364))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* mem_uniformity_is_closed
- \+/\- *lemma* sum.uniformity
- \+/\- *lemma* to_topological_space_prod

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_iff_exists_le_nhds
- \+/\- *lemma* cauchy_map_iff_exists_tendsto
- \+/\- *def* cauchy_seq
- \+/\- *theorem* cauchy_seq_tendsto_of_complete
- \+/\- *lemma* cauchy_seq_tendsto_of_is_complete
- \+/\- *lemma* totally_bounded_closure
- \+/\- *lemma* totally_bounded_empty
- \+/\- *lemma* totally_bounded_image
- \+/\- *lemma* totally_bounded_subset

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* uniform_space.uniform_continuous_quotient_lift₂

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing.mk'
- \- *def* uniform_inducing.mk'



## [2019-08-28 09:17:30](https://github.com/leanprover-community/mathlib/commit/79dccba)
refactor: change field notation from k to \bbk ([#1363](https://github.com/leanprover-community/mathlib/pull/1363))
* refactor: change field notation from k to \bbK
* change \bbK to \bbk
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *lemma* differentiable.comp
- \+/\- *lemma* differentiable.continuous
- \+/\- *lemma* differentiable.differentiable_on
- \+/\- *lemma* differentiable.mul
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* differentiable.prod
- \+/\- *lemma* differentiable.smul'
- \+/\- *lemma* differentiable.smul
- \+/\- *lemma* differentiable_at.congr_of_mem_nhds
- \+/\- *lemma* differentiable_at.continuous_at
- \+/\- *lemma* differentiable_at.has_fderiv_at
- \+/\- *lemma* differentiable_at.mul
- \+/\- *lemma* differentiable_at.neg
- \+/\- *lemma* differentiable_at.prod
- \+/\- *lemma* differentiable_at.smul'
- \+/\- *lemma* differentiable_at.smul
- \+/\- *lemma* differentiable_at_const
- \+/\- *lemma* differentiable_at_id
- \+/\- *lemma* differentiable_const
- \+/\- *lemma* differentiable_id
- \+/\- *lemma* differentiable_on.congr_mono
- \+/\- *lemma* differentiable_on.continuous_on
- \+/\- *lemma* differentiable_on.mono
- \+/\- *lemma* differentiable_on.mul
- \+/\- *lemma* differentiable_on.neg
- \+/\- *lemma* differentiable_on.prod
- \+/\- *lemma* differentiable_on.smul'
- \+/\- *lemma* differentiable_on.smul
- \+/\- *lemma* differentiable_on_const
- \+/\- *lemma* differentiable_on_id
- \+/\- *lemma* differentiable_within_at.congr_mono
- \+/\- *lemma* differentiable_within_at.continuous_within_at
- \+/\- *lemma* differentiable_within_at.fderiv_within_congr_mono
- \+/\- *lemma* differentiable_within_at.has_fderiv_within_at
- \+/\- *lemma* differentiable_within_at.mono
- \+/\- *lemma* differentiable_within_at.neg
- \+/\- *lemma* differentiable_within_at.smul
- \+/\- *lemma* differentiable_within_at_const
- \+/\- *lemma* differentiable_within_at_id
- \+/\- *def* fderiv
- \+/\- *lemma* fderiv_const
- \+/\- *lemma* fderiv_id
- \+/\- *lemma* fderiv_mul
- \+/\- *lemma* fderiv_neg
- \+/\- *lemma* fderiv_smul'
- \+/\- *lemma* fderiv_smul
- \+/\- *def* fderiv_within
- \+/\- *lemma* fderiv_within_add
- \+/\- *lemma* fderiv_within_congr
- \+/\- *lemma* fderiv_within_congr_of_mem_nhds_within
- \+/\- *lemma* fderiv_within_const
- \+/\- *lemma* fderiv_within_id
- \+/\- *lemma* fderiv_within_inter
- \+/\- *lemma* fderiv_within_mul
- \+/\- *lemma* fderiv_within_neg
- \+/\- *lemma* fderiv_within_smul'
- \+/\- *lemma* fderiv_within_smul
- \+/\- *lemma* fderiv_within_sub
- \+/\- *lemma* fderiv_within_subset
- \+/\- *lemma* fderiv_within_univ
- \+/\- *theorem* has_fderiv_at.comp
- \+/\- *theorem* has_fderiv_at.comp_has_fderiv_within_at
- \+/\- *lemma* has_fderiv_at.differentiable_at
- \+/\- *lemma* has_fderiv_at.fderiv
- \+/\- *theorem* has_fderiv_at.smul
- \+/\- *def* has_fderiv_at
- \+/\- *theorem* has_fderiv_at_filter.comp
- \+/\- *theorem* has_fderiv_at_filter.smul
- \+/\- *def* has_fderiv_at_filter
- \+/\- *theorem* has_fderiv_at_id
- \+/\- *theorem* has_fderiv_within_at.comp
- \+/\- *theorem* has_fderiv_within_at.smul
- \+/\- *def* has_fderiv_within_at
- \+/\- *lemma* is_bounded_bilinear_map.continuous
- \+/\- *lemma* is_bounded_bilinear_map.differentiable
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_at
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_on
- \+/\- *lemma* is_bounded_bilinear_map.differentiable_within_at
- \+/\- *lemma* is_bounded_bilinear_map.fderiv
- \+/\- *lemma* is_bounded_bilinear_map.fderiv_within
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_bilinear_map.has_fderiv_within_at
- \+/\- *lemma* is_bounded_linear_map.differentiable
- \+/\- *lemma* is_bounded_linear_map.differentiable_at
- \+/\- *lemma* is_bounded_linear_map.differentiable_on
- \+/\- *lemma* is_bounded_linear_map.differentiable_within_at
- \+/\- *lemma* is_bounded_linear_map.fderiv
- \+/\- *lemma* is_bounded_linear_map.fderiv_within
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_at_filter
- \+/\- *lemma* is_bounded_linear_map.has_fderiv_within_at
- \+/\- *theorem* unique_diff_on.eq
- \+/\- *theorem* unique_diff_within_at.eq

Modified src/analysis/calculus/tangent_cone.lean
- \+/\- *lemma* is_open.unique_diff_on
- \+/\- *lemma* is_open.unique_diff_within_at
- \+/\- *lemma* tangent_cone_at.lim_zero
- \+/\- *lemma* tangent_cone_univ
- \+/\- *lemma* unique_diff_on.prod
- \+/\- *lemma* unique_diff_on_inter
- \+/\- *lemma* unique_diff_on_univ
- \+/\- *lemma* unique_diff_within_at.inter
- \+/\- *lemma* unique_diff_within_at.mono
- \+/\- *lemma* unique_diff_within_at_univ

Modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* is_bounded_bilinear_map.times_cont_diff
- \+/\- *lemma* is_bounded_linear_map.times_cont_diff
- \+/\- *def* iterated_continuous_linear_map.normed_group_rec
- \+/\- *def* iterated_continuous_linear_map.normed_space_rec
- \+/\- *def* iterated_continuous_linear_map
- \+/\- *def* iterated_fderiv
- \+/\- *def* iterated_fderiv_within
- \+/\- *lemma* iterated_fderiv_within_congr
- \+/\- *lemma* times_cont_diff.continuous
- \+/\- *lemma* times_cont_diff.continuous_fderiv
- \+/\- *lemma* times_cont_diff.of_le
- \+/\- *lemma* times_cont_diff.of_succ
- \+/\- *def* times_cont_diff
- \+/\- *lemma* times_cont_diff_const
- \+/\- *lemma* times_cont_diff_fst
- \+/\- *lemma* times_cont_diff_id
- \+/\- *lemma* times_cont_diff_on.congr
- \+/\- *lemma* times_cont_diff_on.congr_mono'
- \+/\- *lemma* times_cont_diff_on.congr_mono
- \+/\- *lemma* times_cont_diff_on.continuous_on
- \+/\- *lemma* times_cont_diff_on.mono
- \+/\- *lemma* times_cont_diff_on.of_succ
- \+/\- *def* times_cont_diff_on
- \+/\- *lemma* times_cont_diff_on_rec.differentiable_on
- \+/\- *lemma* times_cont_diff_on_rec.of_succ
- \+/\- *def* times_cont_diff_on_rec
- \+/\- *lemma* times_cont_diff_rec.continuous
- \+/\- *lemma* times_cont_diff_rec.differentiable
- \+/\- *lemma* times_cont_diff_rec.of_succ
- \+/\- *def* times_cont_diff_rec
- \+/\- *lemma* times_cont_diff_snd
- \+/\- *lemma* times_cont_diff_top

Modified src/analysis/normed_space/banach.lean
- \+/\- *theorem* exists_preimage_norm_le
- \+/\- *theorem* linear_equiv.is_bounded_inv
- \+/\- *theorem* open_mapping

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_left
- \+/\- *lemma* continuous_linear_map.is_bounded_linear_map_comp_right
- \+/\- *def* is_bounded_bilinear_map.deriv
- \+/\- *lemma* is_bounded_bilinear_map.is_bounded_linear_map_deriv
- \+/\- *def* is_bounded_bilinear_map.linear_deriv
- \+/\- *lemma* is_bounded_bilinear_map.map_sub_left
- \+/\- *lemma* is_bounded_bilinear_map.map_sub_right
- \+/\- *lemma* is_bounded_bilinear_map_deriv_coe
- \+/\- *lemma* is_bounded_linear_map.add
- \+/\- *lemma* is_bounded_linear_map.continuous
- \+/\- *lemma* is_bounded_linear_map.fst
- \+/\- *lemma* is_bounded_linear_map.id
- \+/\- *theorem* is_bounded_linear_map.is_O_comp
- \+/\- *theorem* is_bounded_linear_map.is_O_id
- \+/\- *theorem* is_bounded_linear_map.is_O_sub
- \+/\- *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \+/\- *lemma* is_bounded_linear_map.neg
- \+/\- *lemma* is_bounded_linear_map.smul
- \+/\- *lemma* is_bounded_linear_map.snd
- \+/\- *lemma* is_bounded_linear_map.sub
- \+/\- *lemma* is_bounded_linear_map.tendsto
- \+/\- *def* is_bounded_linear_map.to_continuous_linear_map
- \+/\- *def* is_bounded_linear_map.to_linear_map
- \+/\- *lemma* is_bounded_linear_map.zero
- \+/\- *structure* is_bounded_linear_map

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.bounds_bdd_below
- \+/\- *lemma* continuous_linear_map.bounds_nonempty
- \+/\- *theorem* continuous_linear_map.is_O_comp
- \+/\- *theorem* continuous_linear_map.is_O_sub
- \+/\- *lemma* continuous_linear_map.norm_id
- \+/\- *lemma* continuous_linear_map.norm_zero
- \+/\- *lemma* continuous_linear_map.scalar_prod_space_iso_norm
- \+/\- *lemma* linear_map.continuous_of_bound
- \+/\- *def* linear_map.with_bound
- \+/\- *lemma* linear_map_with_bound_apply
- \+/\- *lemma* linear_map_with_bound_coe



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
- \+ *def* ring_hom.comp
- \+ *theorem* ring_hom.ext
- \+ *def* ring_hom.id
- \+ *lemma* ring_hom.map_add
- \+ *lemma* ring_hom.map_mul
- \+ *theorem* ring_hom.map_neg
- \+ *lemma* ring_hom.map_one
- \+ *theorem* ring_hom.map_sub
- \+ *lemma* ring_hom.map_zero
- \+ *def* ring_hom.mk'
- \+ *structure* ring_hom
- \- *def* semiring_hom.comp
- \- *theorem* semiring_hom.ext
- \- *def* semiring_hom.id
- \- *lemma* semiring_hom.map_add
- \- *lemma* semiring_hom.map_mul
- \- *theorem* semiring_hom.map_neg
- \- *lemma* semiring_hom.map_one
- \- *theorem* semiring_hom.map_sub
- \- *lemma* semiring_hom.map_zero
- \- *def* semiring_hom.mk'
- \- *structure* semiring_hom



## [2019-08-26 14:50:25](https://github.com/leanprover-community/mathlib/commit/914c572)
feat(data/rat): add lt, le, and eq def lemmas, move casts into rat to basic ([#1348](https://github.com/leanprover-community/mathlib/pull/1348))
#### Estimated changes
Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/rat/basic.lean
- \+ *theorem* rat.coe_int_denom
- \+ *theorem* rat.coe_int_eq_mk
- \+ *theorem* rat.coe_int_eq_of_int
- \+ *theorem* rat.coe_int_num
- \+ *lemma* rat.coe_int_num_of_denom_eq_one
- \+ *theorem* rat.coe_nat_denom
- \+ *theorem* rat.coe_nat_eq_mk
- \+ *theorem* rat.coe_nat_num
- \+ *lemma* rat.eq_iff_mul_eq_mul
- \+ *lemma* rat.inv_def'
- \+ *theorem* rat.mk_eq_div
- \+ *lemma* rat.mul_own_denom_eq_num
- \+/\- *theorem* rat.num_denom'
- \+/\- *theorem* rat.num_denom
- \+/\- *theorem* rat.of_int_eq_mk

Modified src/data/rat/cast.lean
- \- *theorem* rat.coe_int_denom
- \- *theorem* rat.coe_int_eq_mk
- \- *theorem* rat.coe_int_eq_of_int
- \- *theorem* rat.coe_int_num
- \- *lemma* rat.coe_int_num_of_denom_eq_one
- \- *theorem* rat.coe_nat_denom
- \- *theorem* rat.coe_nat_eq_mk
- \- *theorem* rat.coe_nat_num
- \- *theorem* rat.mk_eq_div

Modified src/data/rat/order.lean
- \+ *lemma* rat.div_lt_div_iff_mul_lt_mul
- \+ *lemma* rat.lt_one_iff_num_lt_denom



## [2019-08-26 08:13:13](https://github.com/leanprover-community/mathlib/commit/7bc18a8)
feat(data/fin): coe_eq_val and coe_mk ([#1321](https://github.com/leanprover-community/mathlib/pull/1321))
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.coe_eq_val
- \+ *lemma* fin.coe_mk
- \+ *lemma* fin.mk_val
- \- *def* fin.mk_val



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


Added docs/install/new-extensions-icon.png


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
Added src/tactic/apply.lean
- \+ *def* tactic.reorder_goals

Modified src/tactic/core.lean


Modified src/tactic/default.lean


Modified src/tactic/interactive.lean


Added test/apply.lean


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
- \+ *lemma* finset.card_eq_sum_ones

Modified src/data/bool.lean
- \+ *lemma* bool.bxor_iff_ne

Modified src/data/fin.lean
- \+ *lemma* fin.succ_ne_zero

Modified src/data/finset.lean
- \+ *lemma* finset.inter_subset_inter
- \+ *lemma* finset.inter_subset_inter_left
- \+ *lemma* finset.inter_subset_inter_right

Modified src/data/fintype.lean
- \+ *lemma* fintype.card_eq_sum_ones
- \+ *theorem* fintype.card_of_subsingleton
- \- *theorem* fintype.fintype.card_of_subsingleton
- \- *theorem* fintype.fintype.univ_of_subsingleton
- \+ *theorem* fintype.univ_of_subsingleton

Modified src/data/set/function.lean
- \+ *lemma* set.range_restrict

Modified src/logic/basic.lean
- \+ *lemma* ne_comm

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.nat_cast_inj
- \+/\- *theorem* cardinal.nat_cast_le
- \+/\- *theorem* cardinal.nat_cast_lt
- \+/\- *theorem* cardinal.nat_cast_pow
- \+/\- *theorem* cardinal.nat_succ
- \+ *lemma* cardinal.pow_cast_right



## [2019-08-22 10:31:24](https://github.com/leanprover-community/mathlib/commit/f442a41)
docs(category/monad,bitraversable): add module docstrings [#1260](https://github.com/leanprover-community/mathlib/pull/1260)  ([#1286](https://github.com/leanprover-community/mathlib/pull/1286))
* docs(category/monad,bitraversable): add module docstrings
* more docs
* still more doc
* doc about traversable
#### Estimated changes
Modified src/category/bitraversable/basic.lean


Modified src/category/bitraversable/instances.lean


Modified src/category/bitraversable/lemmas.lean
- \+/\- *def* bitraversable.tfst
- \+/\- *def* bitraversable.tsnd

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
Added src/category_theory/Groupoid.lean
- \+ *def* category_theory.Groupoid.forget_to_Cat
- \+ *def* category_theory.Groupoid.objects
- \+ *def* category_theory.Groupoid.of
- \+ *def* category_theory.Groupoid



## [2019-08-21 12:19:41](https://github.com/leanprover-community/mathlib/commit/35144f2)
feat(conv/conv): conv tactics for zooming/saving state ([#1351](https://github.com/leanprover-community/mathlib/pull/1351))
* feat(conv/conv): conv tactics for zooming/saving state
* rob's doc fixes
* nicer docs
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/converter/interactive.lean


Added test/conv/conv.lean




## [2019-08-21 11:04:30](https://github.com/leanprover-community/mathlib/commit/3f915fc)
feat(archive): add the cubing a cube proof ([#1343](https://github.com/leanprover-community/mathlib/pull/1343))
* feat(archive): add the cubing a cube proof
* rename file
* add leanpkg configure to travis
#### Estimated changes
Modified .travis.yml


Added archive/cubing_a_cube.lean
- \+ *lemma* Ico_lemma
- \+ *lemma* b_add_w_le_one
- \+ *lemma* b_le_b
- \+ *def* bcubes
- \+ *lemma* bottom_mem_side
- \+ *theorem* cannot_cube_a_cube
- \+ *def* correct
- \+ *lemma* cube.b_lt_xm
- \+ *lemma* cube.b_mem_bottom
- \+ *lemma* cube.b_mem_side
- \+ *lemma* cube.b_mem_to_set
- \+ *lemma* cube.b_ne_xm
- \+ *def* cube.bottom
- \+ *lemma* cube.head_shift_up
- \+ *lemma* cube.hw'
- \+ *def* cube.shift_up
- \+ *def* cube.side
- \+ *lemma* cube.side_tail
- \+ *lemma* cube.side_unit_cube
- \+ *lemma* cube.tail_shift_up
- \+ *def* cube.to_set
- \+ *def* cube.to_set_disjoint
- \+ *def* cube.to_set_subset
- \+ *def* cube.unit_cube
- \+ *def* cube.xm
- \+ *structure* cube
- \+ *def* decreasing_sequence
- \+ *lemma* exists_mi
- \+ *def* mi
- \+ *lemma* mi_mem_bcubes
- \+ *lemma* mi_minimal
- \+ *lemma* mi_not_on_boundary'
- \+ *lemma* mi_not_on_boundary
- \+ *lemma* mi_strict_minimal
- \+ *lemma* mi_xm_ne_one
- \+ *lemma* nonempty_bcubes
- \+ *theorem* not_correct
- \+ *def* on_boundary
- \+ *lemma* shift_up_bottom_subset_bottoms
- \+ *lemma* side_subset
- \+ *lemma* smallest_on_boundary
- \+ *lemma* strict_mono_sequence_of_cubes
- \+ *lemma* t_le_t
- \+ *lemma* tail_sub
- \+ *lemma* to_set_subset_unit_cube
- \+ *lemma* two_le_mk_bcubes
- \+ *def* valley
- \+ *def* valley_mi
- \+ *lemma* valley_unit_cube
- \+ *lemma* w_lt_w
- \+ *lemma* w_ne_one
- \+ *lemma* zero_le_b
- \+ *lemma* zero_le_of_mem
- \+ *lemma* zero_le_of_mem_side



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
- \- *lemma* finset.sum_hom
- \- *lemma* is_group_hom.finset_prod
- \+ *lemma* is_group_hom.map_finset_prod

Modified src/algebra/direct_limit.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/hom.lean
- \- *def* add_monoid_hom.comp
- \- *def* add_monoid_hom.ext
- \- *def* add_monoid_hom.id
- \- *def* add_monoid_hom.map_add
- \- *theorem* add_monoid_hom.map_neg
- \+/\- *theorem* add_monoid_hom.map_sub
- \- *def* add_monoid_hom.map_zero
- \- *def* add_monoid_hom.mk'
- \- *def* add_monoid_hom.neg
- \+/\- *lemma* coe_as_monoid_hom
- \+ *lemma* monoid_hom.ext
- \- *def* monoid_hom.ext
- \- *theorem* monoid_hom.map_div
- \+/\- *theorem* monoid_hom.map_inv
- \+/\- *lemma* monoid_hom.map_mul
- \+ *theorem* monoid_hom.map_mul_inv
- \+/\- *lemma* monoid_hom.map_one

Modified src/algebra/group/to_additive.lean
- \+ *structure* to_additive.value_type

Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/pointwise.lean
- \- *def* set.pointwise_add_add_monoid
- \- *def* set.pointwise_add_add_semigroup

Modified src/algebra/punit_instances.lean
- \+/\- *lemma* punit.inv_eq
- \+/\- *lemma* punit.mul_eq
- \+/\- *lemma* punit.one_eq

Modified src/data/dfinsupp.lean


Modified src/data/equiv/algebra.lean
- \- *def* add_equiv.apply_symm_apply
- \- *def* add_equiv.map_add
- \- *def* add_equiv.map_zero
- \- *def* add_equiv.refl
- \- *def* add_equiv.symm
- \- *def* add_equiv.symm_apply_apply
- \- *def* add_equiv.to_add_monoid_hom
- \- *theorem* add_equiv.to_equiv_symm
- \- *def* add_equiv.trans
- \+/\- *def* mul_equiv.apply_symm_apply
- \+/\- *def* mul_equiv.map_one
- \+/\- *def* mul_equiv.refl
- \+/\- *def* mul_equiv.symm
- \+/\- *def* mul_equiv.symm_apply_apply
- \+/\- *theorem* mul_equiv.to_equiv_symm
- \+/\- *def* mul_equiv.trans

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
- \+/\- *lemma* quotient_group.coe_inv
- \+/\- *lemma* quotient_group.coe_mul
- \+/\- *lemma* quotient_group.coe_one
- \+/\- *lemma* quotient_group.ker_mk
- \+/\- *lemma* quotient_group.lift_mk'
- \+/\- *lemma* quotient_group.lift_mk

Modified src/group_theory/subgroup.lean
- \- *def* add_group.closure
- \- *theorem* add_group.closure_eq_mclosure
- \- *theorem* add_group.closure_subset
- \- *theorem* add_group.exists_list_of_mem_closure
- \- *theorem* add_group.gmultiples_eq_closure
- \- *lemma* add_group.image_closure
- \- *theorem* add_group.in_closure.rec_on
- \+ *inductive* add_group.in_closure
- \- *lemma* add_group.mem_closure
- \- *theorem* add_group.mem_closure_union_iff
- \+ *lemma* gmultiples_subset
- \+ *lemma* gpowers_subset
- \+/\- *lemma* group.closure_subgroup
- \- *def* is_add_subgroup.center
- \- *def* is_add_subgroup.trivial
- \+/\- *lemma* is_subgroup.mem_trivial

Modified src/group_theory/submonoid.lean
- \- *def* add_monoid.closure
- \- *theorem* add_monoid.closure_mono
- \- *theorem* add_monoid.closure_singleton
- \- *theorem* add_monoid.closure_subset
- \- *theorem* add_monoid.exists_list_of_mem_closure
- \- *lemma* add_monoid.image_closure
- \- *theorem* add_monoid.in_closure.rec_on
- \+ *inductive* add_monoid.in_closure
- \- *theorem* add_monoid.mem_closure_union_iff
- \- *theorem* add_monoid.subset_closure
- \- *lemma* is_add_submonoid_Union_of_directed
- \+ *lemma* multiples.add_mem
- \+ *lemma* powers.mul_mem

Modified src/linear_algebra/tensor_product.lean


Modified src/meta/expr.lean
- \+ *def* name.map_prefix

Modified src/order/filter/pointwise.lean
- \- *def* filter.pointwise_add

Modified src/tactic/algebra.lean


Added src/tactic/transport.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean
- \- *lemma* open_add_subgroup.coe_inf
- \- *lemma* open_add_subgroup.is_open_of_open_add_subgroup
- \- *lemma* open_add_subgroup.le_iff
- \- *lemma* open_add_subgroup.mem_nhds_zero
- \- *def* open_add_subgroup.prod
- \+/\- *lemma* open_subgroup.coe_inf
- \+/\- *lemma* open_subgroup.le_iff



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
- \+ *lemma* rat.coe_int_num_of_denom_eq_one

Modified src/tactic/basic.lean


Added src/tactic/lift.lean


Modified test/tactics.lean




## [2019-08-20 23:38:53](https://github.com/leanprover-community/mathlib/commit/26a3e31)
chore(category_theory/monoidal): monoidal_category doesn't extend category ([#1338](https://github.com/leanprover-community/mathlib/pull/1338))
* chore(category_theory/monoidal): monoidal_category doesn't extend category
* remove _aux file, simplifying
* make notations global, and add doc-strings
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+/\- *def* category_theory.tensor_iso

Deleted src/category_theory/monoidal/category_aux.lean
- \- *def* category_theory.assoc_natural
- \- *def* category_theory.assoc_obj
- \- *def* category_theory.left_unitor_natural
- \- *def* category_theory.left_unitor_obj
- \- *def* category_theory.pentagon
- \- *def* category_theory.right_unitor_natural
- \- *def* category_theory.right_unitor_obj
- \- *def* category_theory.tensor_hom_type
- \- *def* category_theory.tensor_obj_type
- \- *def* category_theory.triangle

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
- \+ *lemma* fn_min_mul_fn_max
- \+ *lemma* min_add_max
- \+ *lemma* min_mul_max

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_self_add_mul_self_eq_zero

Modified src/algebra/ring.lean
- \+ *lemma* Vieta_formula_quadratic
- \+ *lemma* mul_self_eq_zero
- \+ *lemma* zero_eq_mul_self

Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_sigma_equiv

Modified src/data/list/basic.lean
- \+/\- *theorem* list.tfae_singleton

Modified src/logic/basic.lean
- \+ *lemma* eq.congr_left
- \+ *lemma* eq.congr_right
- \+ *lemma* eq_iff_iff



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
Added src/linear_algebra/bilinear_form.lean
- \+ *def* alt_bilin_form.is_alt
- \+ *lemma* alt_bilin_form.neg
- \+ *lemma* alt_bilin_form.self_eq_zero
- \+ *lemma* bilin_form.add_left
- \+ *lemma* bilin_form.add_right
- \+ *def* bilin_form.bilin_linear_map_equiv
- \+ *lemma* bilin_form.ext
- \+ *def* bilin_form.is_ortho
- \+ *lemma* bilin_form.neg_left
- \+ *lemma* bilin_form.neg_right
- \+ *theorem* bilin_form.ortho_smul_left
- \+ *theorem* bilin_form.ortho_smul_right
- \+ *lemma* bilin_form.ortho_zero
- \+ *lemma* bilin_form.smul_left
- \+ *lemma* bilin_form.smul_right
- \+ *lemma* bilin_form.sub_left
- \+ *lemma* bilin_form.sub_right
- \+ *def* bilin_form.to_linear_map
- \+ *lemma* bilin_form.zero_left
- \+ *lemma* bilin_form.zero_right
- \+ *structure* bilin_form
- \+ *def* linear_map.to_bilin
- \+ *lemma* refl_bilin_form.eq_zero
- \+ *def* refl_bilin_form.is_refl
- \+ *lemma* refl_bilin_form.ortho_sym
- \+ *lemma* sym_bilin_form.is_refl
- \+ *def* sym_bilin_form.is_sym
- \+ *lemma* sym_bilin_form.ortho_sym
- \+ *lemma* sym_bilin_form.sym

Added src/linear_algebra/sesquilinear_form.lean
- \+ *def* alt_sesq_form.is_alt
- \+ *lemma* alt_sesq_form.neg
- \+ *lemma* alt_sesq_form.self_eq_zero
- \+ *lemma* refl_sesq_form.eq_zero
- \+ *def* refl_sesq_form.is_refl
- \+ *lemma* refl_sesq_form.ortho_sym
- \+ *lemma* sesq_form.add_left
- \+ *lemma* sesq_form.add_right
- \+ *lemma* sesq_form.ext
- \+ *def* sesq_form.is_ortho
- \+ *lemma* sesq_form.neg_left
- \+ *lemma* sesq_form.neg_right
- \+ *theorem* sesq_form.ortho_smul_left
- \+ *theorem* sesq_form.ortho_smul_right
- \+ *lemma* sesq_form.ortho_zero
- \+ *lemma* sesq_form.smul_left
- \+ *lemma* sesq_form.smul_right
- \+ *lemma* sesq_form.sub_left
- \+ *lemma* sesq_form.sub_right
- \+ *lemma* sesq_form.zero_left
- \+ *lemma* sesq_form.zero_right
- \+ *structure* sesq_form
- \+ *lemma* sym_sesq_form.is_refl
- \+ *def* sym_sesq_form.is_sym
- \+ *lemma* sym_sesq_form.ortho_sym
- \+ *lemma* sym_sesq_form.sym

Added src/ring_theory/maps.lean
- \+ *def* comm_ring.anti_equiv_to_equiv
- \+ *theorem* comm_ring.anti_hom_to_hom
- \+ *def* comm_ring.equiv_to_anti_equiv
- \+ *theorem* comm_ring.hom_to_anti_hom
- \+ *lemma* is_ring_anti_hom.map_neg
- \+ *lemma* is_ring_anti_hom.map_sub
- \+ *lemma* is_ring_anti_hom.map_zero
- \+ *lemma* ring_anti_equiv.bijective
- \+ *lemma* ring_anti_equiv.map_add
- \+ *lemma* ring_anti_equiv.map_mul
- \+ *lemma* ring_anti_equiv.map_neg
- \+ *lemma* ring_anti_equiv.map_neg_one
- \+ *lemma* ring_anti_equiv.map_one
- \+ *lemma* ring_anti_equiv.map_sub
- \+ *lemma* ring_anti_equiv.map_zero
- \+ *lemma* ring_anti_equiv.map_zero_iff
- \+ *structure* ring_anti_equiv
- \+ *lemma* ring_equiv.bijective
- \+ *lemma* ring_equiv.map_add
- \+ *lemma* ring_equiv.map_mul
- \+ *lemma* ring_equiv.map_neg
- \+ *lemma* ring_equiv.map_neg_one
- \+ *lemma* ring_equiv.map_one
- \+ *lemma* ring_equiv.map_sub
- \+ *lemma* ring_equiv.map_zero
- \+ *lemma* ring_equiv.map_zero_iff
- \+ *lemma* ring_invo.bijective
- \+ *lemma* ring_invo.map_add
- \+ *lemma* ring_invo.map_mul
- \+ *lemma* ring_invo.map_neg
- \+ *lemma* ring_invo.map_neg_one
- \+ *lemma* ring_invo.map_one
- \+ *lemma* ring_invo.map_sub
- \+ *lemma* ring_invo.map_zero
- \+ *lemma* ring_invo.map_zero_iff
- \+ *def* ring_invo.to_ring_anti_equiv
- \+ *structure* ring_invo



## [2019-08-20 13:12:03](https://github.com/leanprover-community/mathlib/commit/6f747ec)
feat(data/vector2): nth_map ([#1349](https://github.com/leanprover-community/mathlib/pull/1349))
* feat(data/vector2): nth_map
* Update vector2.lean
* Update vector2.lean
#### Estimated changes
Modified src/data/vector2.lean
- \+ *lemma* vector.nth_map



## [2019-08-20 12:14:30](https://github.com/leanprover-community/mathlib/commit/8771432)
doc(tactic/ring2): document parts of ring2 ([#1208](https://github.com/leanprover-community/mathlib/pull/1208))
* doc(tactic/ring2): document parts of ring2
* feat(data/tree): refactor binary trees into their own module
* feat(tactic/ring2): resolve correct correctness
* chore(tactic/ring2): move copyright into comment
* doc(tactic/ring2): wording
#### Estimated changes
Added src/data/tree.lean
- \+ *def* tree.get
- \+ *def* tree.get_or_else
- \+ *def* tree.index_of
- \+ *def* tree.map
- \+ *def* tree.of_rbnode
- \+ *def* tree.repr
- \+ *inductive* {u}

Modified src/tactic/linarith.lean
- \- *def* linarith.tree.repr
- \- *inductive* linarith.{u}

Modified src/tactic/ring2.lean
- \- *def* tactic.ring2.horner_expr.repr
- \+ *def* tactic.ring2.horner_expr.to_string
- \- *def* tactic.ring2.tree.get
- \- *def* tactic.ring2.tree.index_of
- \- *def* tactic.ring2.tree.of_rbnode
- \- *inductive* tactic.ring2.{u}



## [2019-08-20 11:13:39+02:00](https://github.com/leanprover-community/mathlib/commit/f3eb8c2)
chore(data/matrix): simp attribute for transpose_tranpose ([#1350](https://github.com/leanprover-community/mathlib/pull/1350))
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.transpose_transpose



## [2019-08-19 21:05:01](https://github.com/leanprover-community/mathlib/commit/5a309a3)
fix(category_theory/eq_to_hom): remove bad simp lemmas ([#1346](https://github.com/leanprover-community/mathlib/pull/1346))
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.eq_to_hom_app
- \+/\- *lemma* category_theory.eq_to_hom_map
- \+/\- *lemma* category_theory.eq_to_iso_map



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
- \+ *def* list.argmax
- \+ *theorem* list.argmax_concat
- \+ *theorem* list.argmax_cons
- \+ *theorem* list.argmax_eq_none
- \+ *theorem* list.argmax_eq_some_iff
- \+ *theorem* list.argmax_mem
- \+ *lemma* list.argmax_nil
- \+ *lemma* list.argmax_singleton
- \+ *lemma* list.argmax_two_self
- \+ *def* list.argmax₂
- \+ *def* list.argmin
- \+ *theorem* list.argmin_concat
- \+ *theorem* list.argmin_cons
- \+ *theorem* list.argmin_eq_none
- \+ *theorem* list.argmin_eq_some_iff
- \+ *theorem* list.argmin_le_of_mem
- \+ *theorem* list.argmin_mem
- \+ *lemma* list.argmin_nil
- \+ *lemma* list.argmin_singleton
- \+ *lemma* list.foldl_argmax₂_eq_none
- \+ *theorem* list.index_of_argmax
- \+ *theorem* list.index_of_argmin
- \+ *theorem* list.le_argmax_of_mem
- \- *theorem* list.le_maximum_aux_of_mem
- \+ *theorem* list.le_maximum_of_mem'
- \+/\- *theorem* list.le_maximum_of_mem
- \- *theorem* list.le_minimum_aux_of_mem
- \+ *theorem* list.le_minimum_of_mem'
- \- *theorem* list.le_minimum_of_mem
- \- *theorem* list.le_of_foldl_max
- \- *theorem* list.le_of_foldl_min
- \- *theorem* list.le_of_foldr_max
- \- *theorem* list.le_of_foldr_min
- \+/\- *def* list.maximum
- \- *def* list.maximum_aux
- \- *def* list.maximum_aux_cons
- \+ *theorem* list.maximum_concat
- \+ *theorem* list.maximum_cons
- \- *def* list.maximum_cons
- \+ *theorem* list.maximum_eq_coe_iff
- \+ *theorem* list.maximum_eq_none
- \+/\- *theorem* list.maximum_mem
- \+ *lemma* list.maximum_nil
- \+ *lemma* list.maximum_singleton
- \- *def* list.maximum_singleton
- \+ *theorem* list.mem_argmax_iff
- \+ *theorem* list.mem_argmin_iff
- \- *theorem* list.mem_foldl_max
- \- *theorem* list.mem_foldl_min
- \- *theorem* list.mem_foldr_max
- \- *theorem* list.mem_foldr_min
- \- *theorem* list.mem_maximum_aux
- \- *theorem* list.mem_minimum_aux
- \+/\- *def* list.minimum
- \- *def* list.minimum_aux
- \- *def* list.minimum_aux_cons
- \+ *theorem* list.minimum_concat
- \+ *theorem* list.minimum_cons
- \- *def* list.minimum_cons
- \+ *theorem* list.minimum_eq_coe_iff
- \+ *theorem* list.minimum_eq_none
- \+ *theorem* list.minimum_le_of_mem
- \+/\- *theorem* list.minimum_mem
- \+ *lemma* list.minimum_nil
- \+ *lemma* list.minimum_singleton
- \- *def* list.minimum_singleton

Modified src/tactic/omega/find_scalars.lean




## [2019-08-19 17:09:44](https://github.com/leanprover-community/mathlib/commit/92fa24c)
feat(data/fin): val simp lemmas ([#1347](https://github.com/leanprover-community/mathlib/pull/1347))
* feat(data/fin): val simp lemmas
* Update fin.lean
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.cast_add_val
- \+ *lemma* fin.cast_le_val
- \+ *lemma* fin.cast_lt_cast_succ
- \+ *lemma* fin.last_val



## [2019-08-19 09:36:05-04:00](https://github.com/leanprover-community/mathlib/commit/6fbcc04)
feat(tactic/reassoc_axiom): produce associativity-friendly lemmas in category theory ([#1341](https://github.com/leanprover-community/mathlib/pull/1341))
#### Estimated changes
Modified docs/tactics.md


Modified src/category_theory/adjunction/basic.lean
- \+/\- *lemma* category_theory.adjunction.counit_naturality
- \- *lemma* category_theory.adjunction.counit_naturality_assoc
- \+/\- *lemma* category_theory.adjunction.left_triangle_components
- \- *lemma* category_theory.adjunction.left_triangle_components_assoc
- \+/\- *lemma* category_theory.adjunction.right_triangle_components
- \- *lemma* category_theory.adjunction.right_triangle_components_assoc
- \+/\- *lemma* category_theory.adjunction.unit_naturality
- \- *lemma* category_theory.adjunction.unit_naturality_assoc

Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.eq_to_hom_trans
- \- *lemma* category_theory.eq_to_hom_trans_assoc

Modified src/category_theory/isomorphism.lean
- \- *lemma* category_theory.iso.hom_inv_id_assoc
- \- *lemma* category_theory.iso.inv_hom_id_assoc

Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colim.ι_map
- \- *lemma* category_theory.limits.colim.ι_map_assoc
- \+/\- *lemma* category_theory.limits.colimit.ι_desc
- \- *lemma* category_theory.limits.colimit.ι_desc_assoc
- \+/\- *lemma* category_theory.limits.colimit.ι_post
- \- *lemma* category_theory.limits.colimit.ι_post_assoc
- \+/\- *lemma* category_theory.limits.colimit.ι_pre
- \- *lemma* category_theory.limits.colimit.ι_pre_assoc

Added src/tactic/reassoc_axiom.lean




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
- \+ *lemma* fin.exists_iff
- \+/\- *lemma* fin.find_eq_some_iff
- \+ *lemma* fin.forall_iff
- \+/\- *lemma* fin.mem_find_iff

Modified src/data/list/basic.lean
- \+ *lemma* list.nth_le_update_nth_eq
- \+ *lemma* list.nth_le_update_nth_of_ne

Modified src/data/vector2.lean
- \+ *lemma* vector.mem_iff_nth
- \+ *lemma* vector.nodup_iff_nth_inj
- \+ *lemma* vector.nth_mem
- \+ *lemma* vector.nth_update_nth_eq_if
- \+ *lemma* vector.nth_update_nth_of_ne
- \+ *lemma* vector.nth_update_nth_same
- \+ *def* vector.update_nth



## [2019-08-17 20:50:04](https://github.com/leanprover-community/mathlib/commit/538d3f6)
feat(data/vector2): to_list_map ([#1335](https://github.com/leanprover-community/mathlib/pull/1335))
#### Estimated changes
Modified src/data/vector2.lean
- \+ *lemma* vector.to_list_map



## [2019-08-17 18:55:40](https://github.com/leanprover-community/mathlib/commit/66fa499)
feat(data/list/basic): list.mem_insert_nth ([#1336](https://github.com/leanprover-community/mathlib/pull/1336))
* feat(data/list/basic): list.mem_insert_nth
* Update src/data/list/basic.lean
Co-Authored-By: Floris van Doorn <fpvdoorn@gmail.com>
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.mem_insert_nth



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
- \+ *def* linear_equiv.arrow_congr
- \+/\- *def* linear_equiv.congr_right
- \+ *def* linear_equiv.conj
- \+ *lemma* linear_map.std_basis_eq_single

Modified src/linear_algebra/basis.lean
- \+ *def* equiv_fun_basis
- \+ *theorem* module.card_fintype
- \- *theorem* vector_space.card_fintype'
- \+/\- *theorem* vector_space.card_fintype

Modified src/linear_algebra/matrix.lean
- \+ *def* lin_equiv_matrix'
- \+ *def* lin_equiv_matrix
- \+ *def* linear_map.to_matrix
- \+ *def* linear_map.to_matrixₗ
- \+ *lemma* to_lin_to_matrix
- \+ *lemma* to_matrix_to_lin



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
- \+ *def* string.popn

Modified src/meta/expr.lean


Modified src/tactic/core.lean


Added src/tactic/sanity_check.lean


Added test/sanity_check.lean
- \+ *def* foo1
- \+ *def* foo2
- \+ *lemma* foo3
- \+ *lemma* foo4



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


Added test/finish4.lean
- \+ *def* append1
- \+ *lemma* hd_rev
- \+ *theorem* log_mul'
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
- \- *lemma* exists_le_mul
- \+ *lemma* exists_le_mul_self
- \- *lemma* exists_lt_mul
- \+ *lemma* exists_lt_mul_self

Modified src/analysis/complex/exponential.lean
- \+ *lemma* real.abs_rpow_le_abs_rpow
- \+ *lemma* real.continuous_at_log
- \+ *lemma* real.continuous_at_rpow_of_ne_zero
- \+ *lemma* real.continuous_at_rpow_of_pos
- \+ *lemma* real.continuous_log'
- \+ *lemma* real.continuous_log
- \+ *lemma* real.continuous_rpow
- \+ *lemma* real.continuous_rpow_aux1
- \+ *lemma* real.continuous_rpow_aux2
- \+ *lemma* real.continuous_rpow_aux3
- \+ *lemma* real.continuous_rpow_of_ne_zero
- \+ *lemma* real.continuous_rpow_of_pos
- \+ *lemma* real.continuous_sqrt
- \+ *lemma* real.log_lt_log
- \+ *lemma* real.log_lt_log_iff
- \+ *lemma* real.log_neg
- \+ *lemma* real.log_neg_iff
- \+ *lemma* real.log_nonneg
- \+ *lemma* real.log_nonpos
- \+ *lemma* real.log_pos
- \+ *lemma* real.log_pos_iff
- \+ *lemma* real.one_lt_rpow
- \+ *lemma* real.rpow_def_of_neg
- \+ *lemma* real.rpow_def_of_nonpos
- \+ *lemma* real.rpow_def_of_pos
- \+ *lemma* real.rpow_le_rpow_of_exponent_ge
- \+ *lemma* real.rpow_le_rpow_of_exponent_le
- \+ *lemma* real.rpow_lt_one
- \+ *lemma* real.rpow_lt_rpow
- \+ *lemma* real.rpow_lt_rpow_of_exponent_gt
- \+ *lemma* real.rpow_lt_rpow_of_exponent_lt
- \+ *lemma* real.sqrt_eq_rpow
- \+ *lemma* real.tendsto_log_one_zero

Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/specific_limits.lean
- \- *lemma* real.continuous_sqrt

Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_lt_one_iff
- \+ *lemma* real.one_lt_exp_iff

Modified src/data/real/basic.lean
- \- *lemma* real.abs_sqrt_sub_sqrt_le_sqrt_abs



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
- \+ *lemma* associates.prime.le_or_le
- \+ *lemma* associates.prime.ne_one
- \+ *lemma* associates.prime.ne_zero
- \+ *lemma* irreducible.is_unit_or_is_unit
- \+ *theorem* irreducible.ne_zero
- \+ *lemma* irreducible.not_unit
- \- *theorem* ne_zero_of_irreducible
- \+/\- *lemma* not_prime_zero
- \+ *lemma* pow_dvd_pow_iff
- \+ *lemma* prime.div_or_div
- \+ *lemma* prime.ne_zero
- \+ *lemma* prime.not_unit

Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_le_prod
- \+ *lemma* finset.prod_nat_cast
- \+ *lemma* finset.prod_nonneg
- \+ *lemma* finset.prod_pos

Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean
- \+ *lemma* add_le_iff_nonpos_left
- \+ *lemma* add_le_iff_nonpos_right
- \+ *lemma* add_lt_iff_neg_left
- \+ *lemma* add_lt_iff_neg_right

Modified src/data/fin.lean
- \+ *def* fin.cons
- \+ *lemma* fin.cons_succ
- \+ *lemma* fin.cons_zero
- \+ *lemma* fin.exists_fin_succ
- \+ *lemma* fin.forall_fin_succ
- \+ *def* fin.tail
- \+ *lemma* fin.tail_cons

Modified src/data/finset.lean
- \+ *lemma* finset.exists_min

Modified src/data/multiset.lean
- \+ *theorem* multiset.multiset.map_eq_zero

Modified src/data/nat/basic.lean
- \+ *lemma* nat.choose_two_right
- \+ *lemma* nat.fact_eq_one
- \+ *lemma* nat.fact_inj
- \+ *lemma* nat.fact_lt
- \+ *lemma* nat.monotone_fact
- \+ *lemma* nat.one_lt_fact
- \+ *lemma* nat.triangle_succ

Modified src/data/nat/enat.lean
- \+ *lemma* enat.add_one_le_iff_lt
- \+ *lemma* enat.add_one_le_of_lt
- \+ *lemma* enat.le_of_lt_add_one
- \+ *lemma* enat.lt_add_one
- \+ *lemma* enat.lt_add_one_iff_lt
- \+ *lemma* enat.ne_top_iff
- \+ *lemma* enat.ne_top_of_lt
- \+ *lemma* enat.top_eq_none

Modified src/data/padics/padic_norm.lean


Modified src/data/pfun.lean
- \+ *lemma* roption.ne_none_iff
- \+ *lemma* roption.some_ne_none

Modified src/data/set/finite.lean
- \+ *lemma* set.exists_min

Modified src/data/set/intervals.lean
- \+ *lemma* set.eq_of_Ico_disjoint
- \+ *lemma* set.nonempty_Ico_sdiff

Modified src/data/set/lattice.lean
- \+ *lemma* set.not_disjoint_iff

Modified src/field_theory/splitting_field.lean


Modified src/order/basic.lean
- \+ *lemma* reflect_lt

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.finset.prod
- \+ *lemma* multiplicity.multiplicity_add_eq_min
- \+ *lemma* multiplicity.multiplicity_add_of_gt
- \+ *lemma* multiplicity.multiplicity_lt_iff_neg_dvd
- \+ *lemma* multiplicity.multiplicity_pow_self
- \+ *lemma* multiplicity.multiplicity_pow_self_of_prime
- \+ *lemma* multiplicity.multiplicity_sub_of_gt

Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2019-08-15 18:18:27](https://github.com/leanprover-community/mathlib/commit/fa68342)
feat(data/rat): move lemmas to right file, add nat cast lemmas, remove ([#1333](https://github.com/leanprover-community/mathlib/pull/1333))
redundant lemma
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *theorem* rat.of_int_eq_mk

Modified src/data/rat/cast.lean
- \+ *theorem* rat.coe_int_eq_mk
- \+ *theorem* rat.coe_int_eq_of_int
- \+ *theorem* rat.coe_nat_eq_mk
- \+ *theorem* rat.mk_eq_div

Modified src/data/rat/floor.lean


Modified src/data/rat/order.lean
- \- *theorem* rat.coe_int_eq_mk
- \- *theorem* rat.coe_int_eq_of_int
- \- *theorem* rat.mk_eq_div
- \- *theorem* rat.mk_le
- \- *theorem* rat.of_int_eq_mk



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




## [2019-08-15 10:26:30](https://github.com/leanprover-community/mathlib/commit/3d512f7)
chore(category_theory/isomorphism): docstring, DRY, add some trivial lemmas ([#1309](https://github.com/leanprover-community/mathlib/pull/1309))
- add module docstring;
- use `as_iso` more aggressively to avoid repeating proofs;
- add more trivial lemmas.
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+/\- *def* category_theory.as_iso
- \+/\- *lemma* category_theory.functor.map_inv
- \+ *lemma* category_theory.functor.map_iso_symm
- \- *def* category_theory.inv
- \+/\- *lemma* category_theory.is_iso.hom_inv_id
- \+/\- *lemma* category_theory.is_iso.hom_inv_id_assoc
- \+/\- *lemma* category_theory.is_iso.inv_comp
- \+/\- *lemma* category_theory.is_iso.inv_hom_id
- \+/\- *lemma* category_theory.is_iso.inv_hom_id_assoc
- \+/\- *lemma* category_theory.is_iso.inv_id
- \+/\- *lemma* category_theory.is_iso.is_iso.inv_inv
- \+/\- *lemma* category_theory.is_iso.iso.inv_hom
- \+/\- *lemma* category_theory.is_iso.iso.inv_inv
- \+/\- *lemma* category_theory.iso.refl_symm
- \+ *lemma* category_theory.iso.refl_trans
- \+ *lemma* category_theory.iso.self_symm_id
- \+ *lemma* category_theory.iso.self_symm_id_assoc
- \+ *lemma* category_theory.iso.symm_eq_iff
- \+ *lemma* category_theory.iso.symm_self_id
- \+ *lemma* category_theory.iso.symm_self_id_assoc
- \+ *lemma* category_theory.iso.symm_symm_eq
- \+ *lemma* category_theory.iso.trans_assoc
- \+ *lemma* category_theory.iso.trans_refl
- \+/\- *lemma* category_theory.iso.trans_symm



## [2019-08-15 05:08:24](https://github.com/leanprover-community/mathlib/commit/e48ad0d)
chore(*): migrate `units.map` to bundled homs ([#1331](https://github.com/leanprover-community/mathlib/pull/1331))
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* is_unit.map'
- \+ *lemma* is_unit.map
- \+ *theorem* is_unit.mk0

Modified src/algebra/group/hom.lean
- \+ *def* as_monoid_hom
- \+ *lemma* coe_as_monoid_hom

Modified src/algebra/group/units_hom.lean
- \+ *def* units.coe_hom
- \+ *lemma* units.coe_hom_apply
- \+ *lemma* units.coe_map'
- \+/\- *lemma* units.coe_map
- \+ *def* units.map'
- \+ *def* units.map
- \+/\- *lemma* units.map_comp
- \+/\- *lemma* units.map_id

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
- \+ *lemma* pequiv.symm_single_apply



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
Added scripts/mk_all.sh


Added scripts/rm_all.sh




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
- \+ *lemma* fin.find_eq_some_iff
- \+ *lemma* fin.mem_find_iff



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
- \+ *theorem* option.bind_eq_none'
- \+/\- *theorem* option.bind_eq_none



## [2019-08-12 10:14:40](https://github.com/leanprover-community/mathlib/commit/01cb33c)
feat(algebra/ordered_ring): pos_of_mul_neg_left and similar ([#1313](https://github.com/leanprover-community/mathlib/pull/1313))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* neg_of_mul_pos_left
- \+ *lemma* neg_of_mul_pos_right
- \+ *lemma* nonneg_of_mul_nonpos_left
- \+ *lemma* nonneg_of_mul_nonpos_right
- \+ *lemma* nonpos_of_mul_nonneg_left
- \+ *lemma* nonpos_of_mul_nonneg_right
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


Added src/data/matrix/pequiv.lean
- \+ *lemma* pequiv.matrix_mul_apply
- \+ *lemma* pequiv.mul_matrix_apply
- \+ *lemma* pequiv.single_mul_single
- \+ *lemma* pequiv.single_mul_single_of_ne
- \+ *lemma* pequiv.single_mul_single_right
- \+ *def* pequiv.to_matrix
- \+ *lemma* pequiv.to_matrix_bot
- \+ *lemma* pequiv.to_matrix_injective
- \+ *lemma* pequiv.to_matrix_refl
- \+ *lemma* pequiv.to_matrix_swap
- \+ *lemma* pequiv.to_matrix_symm
- \+ *lemma* pequiv.to_matrix_trans

Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/matrix.lean




## [2019-08-09 09:57:38](https://github.com/leanprover-community/mathlib/commit/a79794a)
feat(archive): add archive ([#1295](https://github.com/leanprover-community/mathlib/pull/1295))
* feat(archive): add archive
* reformulate sentence
#### Estimated changes
Modified .travis.yml


Added archive/README.md




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
- \+ *lemma* nat.one_div_le_one_div
- \+ *lemma* nat.one_div_lt_one_div

Modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_self_le_mul_self_of_le_of_neg_le

Added src/algebra/quadratic_discriminant.lean
- \+ *def* discrim
- \+ *lemma* discriminant_le_zero
- \+ *lemma* discriminant_lt_zero
- \+ *lemma* exist_quadratic_eq_zero
- \+ *lemma* exists_le_mul
- \+ *lemma* exists_lt_mul
- \+ *lemma* quadratic_eq_zero_iff
- \+ *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+ *lemma* quadratic_eq_zero_iff_of_discrim_eq_zero
- \+ *lemma* quadratic_ne_zero_of_discrim_ne_square

Modified src/analysis/convex.lean
- \+ *lemma* convex_submodule
- \+ *lemma* convex_subspace

Added src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* abs_inner_le_norm
- \+ *theorem* exists_norm_eq_infi_of_complete_convex
- \+ *theorem* exists_norm_eq_infi_of_complete_subspace
- \+ *lemma* inner_add_add_self
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_comm
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* inner_neg_left
- \+ *lemma* inner_neg_neg
- \+ *lemma* inner_neg_right
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_nonneg
- \+ *lemma* inner_smul_left
- \+ *lemma* inner_smul_right
- \+ *lemma* inner_sub_left
- \+ *lemma* inner_sub_right
- \+ *lemma* inner_sub_sub_self
- \+ *lemma* inner_zero_left
- \+ *lemma* inner_zero_right
- \+ *lemma* norm_add_mul_self
- \+ *lemma* norm_add_pow_two
- \+ *theorem* norm_eq_infi_iff_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_inner_le_zero
- \+ *lemma* norm_eq_sqrt_inner
- \+ *lemma* norm_sub_mul_self
- \+ *lemma* norm_sub_pow_two
- \+ *lemma* parallelogram_law
- \+ *lemma* parallelogram_law_with_norm

Modified src/analysis/specific_limits.lean
- \+ *lemma* real.continuous_sqrt

Modified src/data/real/basic.lean
- \+/\- *theorem* real.Sup_univ
- \+ *lemma* real.abs_sqrt_sub_sqrt_le_sqrt_abs

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* lattice.exists_lt_of_cinfi_lt
- \+ *lemma* lattice.exists_lt_of_lt_csupr

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
- \+ *def* semiring_hom.comp
- \+ *theorem* semiring_hom.ext
- \+ *def* semiring_hom.id
- \+ *lemma* semiring_hom.map_add
- \+ *lemma* semiring_hom.map_mul
- \+ *theorem* semiring_hom.map_neg
- \+ *lemma* semiring_hom.map_one
- \+ *theorem* semiring_hom.map_sub
- \+ *lemma* semiring_hom.map_zero
- \+ *def* semiring_hom.mk'
- \+ *structure* semiring_hom



## [2019-08-06 15:58:05+02:00](https://github.com/leanprover-community/mathlib/commit/57c1d6d)
chore(data/matrix): protect some lemmas ([#1304](https://github.com/leanprover-community/mathlib/pull/1304))
#### Estimated changes
Modified src/data/matrix.lean
- \- *theorem* matrix.add_mul
- \- *theorem* matrix.mul_add
- \- *theorem* matrix.mul_zero
- \- *theorem* matrix.zero_mul



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
- \- *lemma* finset.sum_le_sum'
- \- *lemma* finset.sum_le_zero'
- \- *lemma* finset.sum_le_zero
- \+ *lemma* finset.sum_nonneg
- \+ *lemma* finset.sum_nonpos
- \- *lemma* finset.zero_le_sum'
- \- *lemma* finset.zero_le_sum

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
- \+/\- *structure* alg_hom



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
- \+ *lemma* linear_map.coe_mk



## [2019-08-02 14:52:18](https://github.com/leanprover-community/mathlib/commit/1061238)
feat(topology): category of uniform spaces ([#1275](https://github.com/leanprover-community/mathlib/pull/1275))
* feat(category_theory): uniform spaces
* feat(topology/uniform_spaces): CpltSepUniformSpace is a reflective subcategory
#### Estimated changes
Added src/topology/uniform_space/UniformSpace.lean
- \+ *def* CpltSepUniformSpace.forget
- \+ *def* CpltSepUniformSpace.forget_to_Type_via_UniformSpace
- \+ *def* CpltSepUniformSpace.forget_to_UniformSpace
- \+ *def* CpltSepUniformSpace.of
- \+ *def* CpltSepUniformSpace.to_UniformSpace
- \+ *structure* CpltSepUniformSpace
- \+ *def* UniformSpace.completion_hom
- \+ *lemma* UniformSpace.completion_hom_val
- \+ *lemma* UniformSpace.extension_comp_coe
- \+ *lemma* UniformSpace.extension_hom_val
- \+ *abbreviation* UniformSpace.forget
- \+ *def* UniformSpace.forget_to_Top
- \+ *def* UniformSpace.forget_to_Type_via_Top
- \+ *def* UniformSpace.of
- \+ *def* UniformSpace

Modified src/topology/uniform_space/completion.lean
- \+ *lemma* uniform_space.completion.extension_comp_coe
- \+/\- *lemma* uniform_space.completion.map_id



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
- \- *theorem* rat.abs_def
- \- *theorem* rat.cast_abs
- \- *theorem* rat.cast_add
- \- *theorem* rat.cast_add_of_ne_zero
- \- *theorem* rat.cast_bit0
- \- *theorem* rat.cast_bit1
- \- *theorem* rat.cast_coe_int
- \- *theorem* rat.cast_coe_nat
- \- *theorem* rat.cast_div
- \- *theorem* rat.cast_div_of_ne_zero
- \- *theorem* rat.cast_eq_zero
- \- *theorem* rat.cast_id
- \- *theorem* rat.cast_inj
- \- *theorem* rat.cast_injective
- \- *theorem* rat.cast_inv
- \- *theorem* rat.cast_inv_of_ne_zero
- \- *theorem* rat.cast_le
- \- *theorem* rat.cast_lt
- \- *theorem* rat.cast_lt_zero
- \- *theorem* rat.cast_max
- \- *theorem* rat.cast_min
- \- *theorem* rat.cast_mk
- \- *theorem* rat.cast_mk_of_ne_zero
- \- *theorem* rat.cast_mul
- \- *theorem* rat.cast_mul_of_ne_zero
- \- *theorem* rat.cast_ne_zero
- \- *theorem* rat.cast_neg
- \- *theorem* rat.cast_nonneg
- \- *theorem* rat.cast_nonpos
- \- *theorem* rat.cast_of_int
- \- *theorem* rat.cast_one
- \- *theorem* rat.cast_pos
- \- *theorem* rat.cast_pow
- \- *theorem* rat.cast_sub
- \- *theorem* rat.cast_sub_of_ne_zero
- \- *theorem* rat.cast_zero
- \- *def* rat.ceil
- \- *theorem* rat.ceil_add_int
- \- *theorem* rat.ceil_coe
- \- *theorem* rat.ceil_le
- \- *theorem* rat.ceil_mono
- \- *theorem* rat.ceil_sub_int
- \- *theorem* rat.coe_int_denom
- \- *theorem* rat.coe_int_eq_mk
- \- *theorem* rat.coe_int_eq_of_int
- \- *theorem* rat.coe_int_num
- \- *theorem* rat.coe_nat_denom
- \- *theorem* rat.coe_nat_num
- \- *theorem* rat.eq_cast
- \- *theorem* rat.eq_cast_of_ne_zero
- \- *theorem* rat.exists_mul_self
- \- *def* rat.floor
- \- *theorem* rat.floor_add_int
- \- *theorem* rat.floor_coe
- \- *theorem* rat.floor_le
- \- *theorem* rat.floor_lt
- \- *theorem* rat.floor_mono
- \- *theorem* rat.floor_sub_int
- \- *theorem* rat.le_ceil
- \- *theorem* rat.le_floor
- \- *theorem* rat.le_nat_ceil
- \- *theorem* rat.lt_nat_ceil
- \- *theorem* rat.lt_succ_floor
- \- *theorem* rat.mk_eq_div
- \- *theorem* rat.mk_le
- \- *theorem* rat.mk_nonneg
- \- *theorem* rat.mul_cast_comm
- \- *def* rat.nat_ceil
- \- *theorem* rat.nat_ceil_add_nat
- \- *theorem* rat.nat_ceil_coe
- \- *theorem* rat.nat_ceil_le
- \- *theorem* rat.nat_ceil_lt_add_one
- \- *theorem* rat.nat_ceil_mono
- \- *theorem* rat.nat_ceil_zero
- \- *theorem* rat.nonneg_iff_zero_le
- \- *theorem* rat.num_nonneg_iff_zero_le
- \- *theorem* rat.num_pos_iff_pos
- \- *theorem* rat.of_int_eq_mk
- \- *def* rat.sqrt
- \- *theorem* rat.sqrt_eq
- \- *theorem* rat.sqrt_nonneg

Added src/data/rat/cast.lean
- \+ *theorem* rat.cast_abs
- \+ *theorem* rat.cast_add
- \+ *theorem* rat.cast_add_of_ne_zero
- \+ *theorem* rat.cast_bit0
- \+ *theorem* rat.cast_bit1
- \+ *theorem* rat.cast_coe_int
- \+ *theorem* rat.cast_coe_nat
- \+ *theorem* rat.cast_div
- \+ *theorem* rat.cast_div_of_ne_zero
- \+ *theorem* rat.cast_eq_zero
- \+ *theorem* rat.cast_id
- \+ *theorem* rat.cast_inj
- \+ *theorem* rat.cast_injective
- \+ *theorem* rat.cast_inv
- \+ *theorem* rat.cast_inv_of_ne_zero
- \+ *theorem* rat.cast_le
- \+ *theorem* rat.cast_lt
- \+ *theorem* rat.cast_lt_zero
- \+ *theorem* rat.cast_max
- \+ *theorem* rat.cast_min
- \+ *theorem* rat.cast_mk
- \+ *theorem* rat.cast_mk_of_ne_zero
- \+ *theorem* rat.cast_mul
- \+ *theorem* rat.cast_mul_of_ne_zero
- \+ *theorem* rat.cast_ne_zero
- \+ *theorem* rat.cast_neg
- \+ *theorem* rat.cast_nonneg
- \+ *theorem* rat.cast_nonpos
- \+ *theorem* rat.cast_of_int
- \+ *theorem* rat.cast_one
- \+ *theorem* rat.cast_pos
- \+ *theorem* rat.cast_pow
- \+ *theorem* rat.cast_sub
- \+ *theorem* rat.cast_sub_of_ne_zero
- \+ *theorem* rat.cast_zero
- \+ *theorem* rat.coe_int_denom
- \+ *theorem* rat.coe_int_num
- \+ *theorem* rat.coe_nat_denom
- \+ *theorem* rat.coe_nat_num
- \+ *theorem* rat.eq_cast
- \+ *theorem* rat.eq_cast_of_ne_zero
- \+ *theorem* rat.mul_cast_comm

Added src/data/rat/default.lean


Modified src/data/rat/denumerable.lean


Added src/data/rat/floor.lean
- \+ *def* rat.ceil
- \+ *theorem* rat.ceil_add_int
- \+ *theorem* rat.ceil_coe
- \+ *theorem* rat.ceil_le
- \+ *theorem* rat.ceil_mono
- \+ *theorem* rat.ceil_sub_int
- \+ *def* rat.floor
- \+ *theorem* rat.floor_add_int
- \+ *theorem* rat.floor_coe
- \+ *lemma* rat.floor_def
- \+ *theorem* rat.floor_le
- \+ *theorem* rat.floor_lt
- \+ *theorem* rat.floor_mono
- \+ *theorem* rat.floor_sub_int
- \+ *theorem* rat.le_ceil
- \+ *theorem* rat.le_floor
- \+ *theorem* rat.le_nat_ceil
- \+ *theorem* rat.lt_nat_ceil
- \+ *theorem* rat.lt_succ_floor
- \+ *def* rat.nat_ceil
- \+ *theorem* rat.nat_ceil_add_nat
- \+ *theorem* rat.nat_ceil_coe
- \+ *theorem* rat.nat_ceil_le
- \+ *theorem* rat.nat_ceil_lt_add_one
- \+ *theorem* rat.nat_ceil_mono
- \+ *theorem* rat.nat_ceil_zero

Added src/data/rat/order.lean
- \+ *theorem* rat.abs_def
- \+ *theorem* rat.coe_int_eq_mk
- \+ *theorem* rat.coe_int_eq_of_int
- \+ *theorem* rat.exists_mul_self
- \+ *theorem* rat.mk_eq_div
- \+ *theorem* rat.mk_le
- \+ *theorem* rat.mk_nonneg
- \+ *theorem* rat.nonneg_iff_zero_le
- \+ *theorem* rat.num_nonneg_iff_zero_le
- \+ *theorem* rat.num_pos_iff_pos
- \+ *theorem* rat.of_int_eq_mk
- \+ *def* rat.sqrt
- \+ *theorem* rat.sqrt_eq
- \+ *theorem* rat.sqrt_nonneg

Modified src/tactic/norm_num.lean




## [2019-08-01 15:02:26](https://github.com/leanprover-community/mathlib/commit/0d66c87)
feat(data/seq): add ext proof, nats def, zip_with lemmas, and extract seq property ([#1278](https://github.com/leanprover-community/mathlib/pull/1278))
#### Estimated changes
Modified src/data/seq/seq.lean
- \+ *lemma* seq.ge_stable
- \+ *def* seq.nats
- \+ *lemma* seq.nats_nth
- \+ *lemma* seq.zip_with_nth_none'
- \+ *lemma* seq.zip_with_nth_none
- \+ *lemma* seq.zip_with_nth_some
- \+/\- *def* seq
- \+ *def* stream.is_seq

Modified src/data/seq/wseq.lean


