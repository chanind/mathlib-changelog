## [2021-03-31 21:24:16](https://github.com/leanprover-community/mathlib/commit/5f1b450)
refactor(algebra/*): add new `mul_one_class` and `add_zero_class` for non-associative monoids ([#6865](https://github.com/leanprover-community/mathlib/pull/6865))
This extracts a base class from `monoid M`, `mul_one_class M`, that drops the associativity assumption.
It goes on to weaken `monoid_hom` and `submonoid` to require `mul_one_class M` instead of `monoid M`, along with weakening the typeclass requirements for other primitive constructions like `monoid_hom.fst`.
Instances of the new classes are provided on `pi`, `prod`, `finsupp`, `(add_)submonoid`, and `(add_)monoid_algebra`.
This is by no means an exhaustive relaxation across mathlib, but it aims to broadly cover the foundations.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* monoid_hom.coe_prod
- \+/\- *lemma* monoid_hom.finset_prod_apply

Modified src/algebra/category/Mon/adjunctions.lean


Modified src/algebra/category/Mon/basic.lean
- \+ *abbreviation* Mon.assoc_monoid_hom

Modified src/algebra/group/defs.lean


Modified src/algebra/group/hom.lean
- \+/\- *structure* add_monoid_hom
- \+/\- *lemma* monoid_hom.cancel_left
- \+/\- *lemma* monoid_hom.cancel_right
- \+/\- *lemma* monoid_hom.coe_comp
- \+/\- *lemma* monoid_hom.coe_eq_to_mul_hom
- \+/\- *lemma* monoid_hom.coe_eq_to_one_hom
- \+/\- *lemma* monoid_hom.coe_inj
- \+/\- *lemma* monoid_hom.coe_mk
- \+/\- *def* monoid_hom.comp
- \+/\- *lemma* monoid_hom.comp_apply
- \+/\- *lemma* monoid_hom.comp_assoc
- \+/\- *def* monoid_hom.comp_hom
- \+/\- *lemma* monoid_hom.comp_id
- \+/\- *lemma* monoid_hom.comp_inv
- \+/\- *lemma* monoid_hom.comp_mul
- \+/\- *lemma* monoid_hom.comp_one
- \+/\- *theorem* monoid_hom.congr_arg
- \+/\- *theorem* monoid_hom.congr_fun
- \+/\- *lemma* monoid_hom.div_apply
- \+/\- *def* monoid_hom.eval
- \+/\- *lemma* monoid_hom.eval_apply
- \+/\- *lemma* monoid_hom.ext
- \+/\- *lemma* monoid_hom.ext_iff
- \+/\- *def* monoid_hom.flip
- \+/\- *lemma* monoid_hom.flip_apply
- \+/\- *def* monoid_hom.id
- \+/\- *lemma* monoid_hom.id_apply
- \+/\- *lemma* monoid_hom.id_comp
- \+/\- *lemma* monoid_hom.injective_iff
- \+/\- *lemma* monoid_hom.inv_apply
- \+/\- *lemma* monoid_hom.inv_comp
- \+/\- *lemma* monoid_hom.map_mul
- \+/\- *lemma* monoid_hom.map_one
- \+/\- *lemma* monoid_hom.mk_coe
- \+/\- *lemma* monoid_hom.mul_apply
- \+/\- *lemma* monoid_hom.mul_comp
- \+/\- *lemma* monoid_hom.one_apply
- \+/\- *lemma* monoid_hom.one_comp
- \+/\- *lemma* monoid_hom.to_fun_eq_coe
- \+/\- *lemma* monoid_hom.to_mul_hom_coe
- \+/\- *lemma* monoid_hom.to_one_hom_coe
- \+/\- *structure* monoid_hom

Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/pi.lean
- \+/\- *def* add_monoid_hom.single
- \+/\- *def* monoid_hom.coe_fn
- \+/\- *lemma* pi.single_add

Modified src/algebra/group/prod.lean
- \+/\- *lemma* prod.fst_mul_snd

Modified src/algebra/group/type_tags.lean
- \+/\- *def* add_monoid_hom.to_multiplicative''
- \+/\- *def* add_monoid_hom.to_multiplicative'
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive''
- \+/\- *def* monoid_hom.to_additive'
- \+/\- *def* monoid_hom.to_additive

Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_one.map_comp

Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* add_monoid_algebra.lift_nc_smul
- \+/\- *lemma* add_monoid_algebra.mul_single_zero_apply
- \+/\- *def* add_monoid_algebra.of
- \+/\- *lemma* add_monoid_algebra.of_apply
- \+/\- *lemma* add_monoid_algebra.of_injective
- \+/\- *lemma* add_monoid_algebra.single_zero_mul_apply
- \+/\- *lemma* monoid_algebra.lift_nc_smul
- \+/\- *lemma* monoid_algebra.mul_single_one_apply
- \+/\- *lemma* monoid_algebra.of_apply
- \+/\- *lemma* monoid_algebra.of_injective
- \+/\- *lemma* monoid_algebra.single_one_comm
- \+/\- *lemma* monoid_algebra.single_one_mul_apply

Modified src/algebra/opposites.lean


Modified src/algebra/pointwise.lean


Modified src/category_theory/endomorphism.lean


Modified src/data/dfinsupp.lean
- \+/\- *lemma* add_monoid_hom.coe_dfinsupp_sum_add_hom
- \+/\- *lemma* add_monoid_hom.dfinsupp_sum_add_hom_apply
- \+/\- *lemma* dfinsupp.add_apply
- \+/\- *lemma* dfinsupp.add_hom_ext'
- \+/\- *lemma* dfinsupp.add_hom_ext
- \+/\- *lemma* dfinsupp.coe_add
- \+/\- *lemma* dfinsupp.comp_lift_add_hom
- \+/\- *lemma* dfinsupp.comp_sum_add_hom
- \+/\- *lemma* dfinsupp.filter_pos_add_filter_neg
- \+/\- *def* dfinsupp.lift_add_hom
- \+/\- *lemma* dfinsupp.lift_add_hom_apply_single
- \+/\- *lemma* dfinsupp.lift_add_hom_comp_single
- \+/\- *lemma* dfinsupp.mk_add
- \+/\- *lemma* dfinsupp.subtype_domain_add
- \+/\- *def* dfinsupp.sum_add_hom
- \+/\- *lemma* dfinsupp.sum_add_hom_add
- \+/\- *lemma* dfinsupp.sum_add_hom_apply
- \+/\- *lemma* dfinsupp.sum_add_hom_comp_single
- \+/\- *lemma* dfinsupp.sum_add_hom_single
- \+/\- *lemma* dfinsupp.sum_add_hom_zero
- \+/\- *lemma* dfinsupp.support_add

Modified src/data/equiv/mul_add.lean
- \+/\- *def* add_equiv.to_multiplicative''
- \+/\- *def* add_equiv.to_multiplicative'
- \+/\- *def* add_equiv.to_multiplicative
- \+/\- *def* add_monoid_hom.to_add_equiv
- \+/\- *lemma* monoid_hom.coe_to_mul_equiv
- \+/\- *def* monoid_hom.to_mul_equiv
- \+/\- *def* mul_equiv.arrow_congr
- \+/\- *lemma* mul_equiv.coe_to_monoid_hom
- \+/\- *lemma* mul_equiv.map_eq_one_iff
- \+/\- *lemma* mul_equiv.map_ne_one_iff
- \+/\- *lemma* mul_equiv.map_one
- \+/\- *def* mul_equiv.monoid_hom_congr
- \+/\- *def* mul_equiv.to_additive''
- \+/\- *def* mul_equiv.to_additive'
- \+/\- *def* mul_equiv.to_additive
- \+/\- *def* mul_equiv.to_monoid_hom
- \+/\- *lemma* mul_equiv.to_monoid_hom_injective

Modified src/data/equiv/transfer_instance.lean


Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.add_hom_ext'
- \+/\- *lemma* finsupp.add_hom_ext
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg
- \+/\- *lemma* finsupp.map_range_add
- \+/\- *lemma* finsupp.mul_hom_ext'
- \+/\- *lemma* finsupp.mul_hom_ext

Modified src/data/indicator_function.lean
- \+/\- *def* set.mul_indicator_hom

Modified src/deprecated/group.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/submonoid/basic.lean
- \+/\- *structure* add_submonoid
- \+/\- *def* monoid_hom.of_mdense
- \+/\- *structure* submonoid

Modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* submonoid.mem_powers
- \+/\- *def* submonoid.powers
- \+/\- *lemma* submonoid.powers_eq_closure
- \+/\- *lemma* submonoid.powers_subset

Modified src/group_theory/submonoid/operations.lean
- \+/\- *def* add_submonoid.of_submonoid
- \+/\- *def* add_submonoid.to_submonoid
- \+/\- *lemma* monoid_hom.coe_mrange_restrict
- \+/\- *def* monoid_hom.mrange_restrict
- \+/\- *lemma* monoid_hom.mrange_top_iff_surjective
- \+/\- *lemma* monoid_hom.mrange_top_of_surjective
- \+/\- *def* monoid_hom.mrestrict
- \+/\- *lemma* monoid_hom.mrestrict_apply
- \+/\- *def* submonoid.add_submonoid_equiv
- \+/\- *def* submonoid.of_add_submonoid
- \+/\- *def* submonoid.to_add_submonoid

Modified src/ring_theory/power_series/basic.lean


Modified src/tactic/norm_num.lean


Modified src/topology/locally_constant/algebra.lean




## [2021-03-31 17:53:07](https://github.com/leanprover-community/mathlib/commit/cc99152)
feat(data/list/zip): `nth_zip_with` univ polymorphic, `zip_with_eq_nil_iff` ([#6974](https://github.com/leanprover-community/mathlib/pull/6974))
#### Estimated changes
Modified src/data/list/zip.lean
- \+/\- *lemma* list.nth_zip_with
- \+ *lemma* list.zip_with_eq_nil_iff



## [2021-03-31 14:28:55](https://github.com/leanprover-community/mathlib/commit/23dbb4c)
feat(tactic/elementwise): autogenerate lemmas in concrete categories ([#6941](https://github.com/leanprover-community/mathlib/pull/6941))
# The `elementwise` attribute
The `elementwise` attribute can be applied to a lemma
```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C] {X Y : C} (f g : X ⟶ Y) : f = g := ...
```
and produce
```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y : C} (f g : X ⟶ Y) (x : X) : f x = g x := ...
```
(Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f` and `g` are being coerced to functions via `concrete_category.has_coe_to_fun`.)
The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.
#### Estimated changes
Modified src/category_theory/limits/concrete_category.lean
- \- *lemma* category_theory.limits.cocone.w_apply
- \- *lemma* category_theory.limits.cocone.w_forget_apply
- \- *lemma* category_theory.limits.colimit.w_apply
- \- *lemma* category_theory.limits.colimit.ι_desc_apply
- \- *lemma* category_theory.limits.cone.w_apply
- \- *lemma* category_theory.limits.cone.w_forget_apply
- \- *lemma* category_theory.limits.limit.lift_π_apply
- \- *lemma* category_theory.limits.limit.w_apply

Modified src/category_theory/limits/shapes/concrete_category.lean
- \- *lemma* category_theory.limits.cokernel_condition_apply
- \- *lemma* category_theory.limits.kernel_condition_apply

Added src/tactic/elementwise.lean
- \+ *theorem* category_theory.elementwise_of

Modified src/tactic/reassoc_axiom.lean


Added test/elementwise.lean
- \+ *lemma* bar'''
- \+ *lemma* bar''
- \+ *lemma* bar'
- \+ *lemma* bar
- \+ *lemma* foo'
- \+ *lemma* foo



## [2021-03-31 13:16:42](https://github.com/leanprover-community/mathlib/commit/f29b0b4)
feat(category_theory/lifting_properties): create a new file about lifting properties ([#6852](https://github.com/leanprover-community/mathlib/pull/6852))
This file introduces lifting properties, establishes a few basic properties, and constructs a subcategory spanned by morphisms having a right lifting property.
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.square_from_iso_invert
- \+ *lemma* category_theory.arrow.square_to_iso_invert
- \+ *def* category_theory.arrow.square_to_snd
- \+ *lemma* category_theory.arrow.w_mk_right

Added src/category_theory/lifting_properties.lean
- \+ *lemma* category_theory.has_right_lifting_property_comp'
- \+ *lemma* category_theory.has_right_lifting_property_comp
- \+ *lemma* category_theory.id_has_right_lifting_property'
- \+ *lemma* category_theory.id_has_right_lifting_property
- \+ *lemma* category_theory.iso_has_right_lifting_property
- \+ *lemma* category_theory.right_lifting_property_initial_iff
- \+ *def* category_theory.right_lifting_subcat.X
- \+ *def* category_theory.right_lifting_subcat
- \+ *def* category_theory.right_lifting_subcategory

Modified src/category_theory/limits/shapes/images.lean




## [2021-03-31 11:08:19](https://github.com/leanprover-community/mathlib/commit/09110f1)
feat(geometry/manifold/bump_function): define smooth bump functions, baby version of the Whitney embedding thm ([#6839](https://github.com/leanprover-community/mathlib/pull/6839))
* refactor some functions in `analysis/calculus/specific_functions` to use bundled structures;
* define `to_euclidean`, `euclidean.dist`, `euclidean.ball`, and `euclidean.closed_ball`;
* define smooth bump functions on manifolds;
* prove a baby version of the Whitney embedding theorem.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean
- \+ *lemma* real.smooth_transition.le_one
- \+ *lemma* real.smooth_transition.lt_one_of_lt_one
- \+ *lemma* real.smooth_transition.nonneg
- \+ *lemma* real.smooth_transition.one_of_one_le
- \+ *lemma* real.smooth_transition.pos_denom
- \+ *lemma* real.smooth_transition.pos_of_pos
- \+ *lemma* real.smooth_transition.zero_of_nonpos
- \+ *def* real.smooth_transition
- \- *lemma* smooth_bump_function.eventually_eq_one
- \- *lemma* smooth_bump_function.eventually_eq_one_of_mem_ball
- \- *lemma* smooth_bump_function.le_one
- \- *lemma* smooth_bump_function.lt_one_of_lt_dist
- \- *lemma* smooth_bump_function.nonneg
- \- *lemma* smooth_bump_function.one_of_mem_closed_ball
- \- *lemma* smooth_bump_function.pos_of_mem_ball
- \- *lemma* smooth_bump_function.support_eq
- \- *lemma* smooth_bump_function.zero_of_le_dist
- \- *def* smooth_bump_function
- \- *lemma* smooth_transition.le_one
- \- *lemma* smooth_transition.lt_one_of_lt_one
- \- *lemma* smooth_transition.nonneg
- \- *lemma* smooth_transition.one_of_one_le
- \- *lemma* smooth_transition.pos_denom
- \- *lemma* smooth_transition.pos_of_pos
- \- *lemma* smooth_transition.zero_of_nonpos
- \- *def* smooth_transition
- \+ *lemma* times_cont_diff_bump.R_pos
- \+ *lemma* times_cont_diff_bump.closure_support_eq
- \+ *lemma* times_cont_diff_bump.coe_eq_comp
- \+ *lemma* times_cont_diff_bump.compact_closure_support
- \+ *lemma* times_cont_diff_bump.eventually_eq_one
- \+ *lemma* times_cont_diff_bump.eventually_eq_one_of_mem_ball
- \+ *lemma* times_cont_diff_bump.exists_closure_subset
- \+ *lemma* times_cont_diff_bump.exists_closure_support_subset
- \+ *lemma* times_cont_diff_bump.le_one
- \+ *lemma* times_cont_diff_bump.lt_one_of_lt_dist
- \+ *lemma* times_cont_diff_bump.nonneg
- \+ *lemma* times_cont_diff_bump.one_of_mem_closed_ball
- \+ *lemma* times_cont_diff_bump.pos_of_mem_ball
- \+ *lemma* times_cont_diff_bump.support_eq
- \+ *def* times_cont_diff_bump.to_fun
- \+ *lemma* times_cont_diff_bump.zero_of_le_dist
- \+ *structure* times_cont_diff_bump
- \+ *lemma* times_cont_diff_bump_of_inner.R_pos
- \+ *lemma* times_cont_diff_bump_of_inner.eventually_eq_one
- \+ *lemma* times_cont_diff_bump_of_inner.eventually_eq_one_of_mem_ball
- \+ *lemma* times_cont_diff_bump_of_inner.le_one
- \+ *lemma* times_cont_diff_bump_of_inner.lt_one_of_lt_dist
- \+ *lemma* times_cont_diff_bump_of_inner.nonneg
- \+ *lemma* times_cont_diff_bump_of_inner.one_of_mem_closed_ball
- \+ *lemma* times_cont_diff_bump_of_inner.pos_of_mem_ball
- \+ *lemma* times_cont_diff_bump_of_inner.support_eq
- \+ *def* times_cont_diff_bump_of_inner.to_fun
- \+ *lemma* times_cont_diff_bump_of_inner.zero_of_le_dist
- \+ *structure* times_cont_diff_bump_of_inner

Added src/analysis/normed_space/euclidean_dist.lean
- \+ *def* euclidean.ball
- \+ *lemma* euclidean.ball_eq_preimage
- \+ *lemma* euclidean.ball_mem_nhds
- \+ *lemma* euclidean.ball_subset_closed_ball
- \+ *def* euclidean.closed_ball
- \+ *lemma* euclidean.closed_ball_eq_image
- \+ *lemma* euclidean.closed_ball_eq_preimage
- \+ *lemma* euclidean.closed_ball_mem_nhds
- \+ *lemma* euclidean.closure_ball
- \+ *lemma* euclidean.compact_ball
- \+ *def* euclidean.dist
- \+ *lemma* euclidean.exists_pos_lt_subset_ball
- \+ *lemma* euclidean.is_closed_closed_ball
- \+ *lemma* euclidean.is_open_ball
- \+ *lemma* euclidean.mem_ball_self
- \+ *lemma* euclidean.nhds_basis_ball
- \+ *lemma* euclidean.nhds_basis_closed_ball
- \+ *lemma* times_cont_diff.euclidean_dist
- \+ *def* to_euclidean

Added src/geometry/manifold/bump_function.lean
- \+ *lemma* exists_embedding_findim_of_compact
- \+ *lemma* smooth_bump_covering.apply_ind
- \+ *def* smooth_bump_covering.choice
- \+ *def* smooth_bump_covering.choice_set
- \+ *lemma* smooth_bump_covering.coe_mk
- \+ *lemma* smooth_bump_covering.comp_embedding_pi_tangent_mfderiv
- \+ *def* smooth_bump_covering.embedding_pi_tangent
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_inj_on
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_injective
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_injective_mfderiv
- \+ *lemma* smooth_bump_covering.embedding_pi_tangent_ker_mfderiv
- \+ *lemma* smooth_bump_covering.eventually_eq_one
- \+ *lemma* smooth_bump_covering.exists_immersion_findim
- \+ *lemma* smooth_bump_covering.exists_is_subordinate
- \+ *def* smooth_bump_covering.ind
- \+ *def* smooth_bump_covering.is_subordinate
- \+ *lemma* smooth_bump_covering.mem_chart_at_ind_source
- \+ *lemma* smooth_bump_covering.mem_chart_at_source_of_eq_one
- \+ *lemma* smooth_bump_covering.mem_ext_chart_at_ind_source
- \+ *lemma* smooth_bump_covering.mem_ext_chart_at_source_of_eq_one
- \+ *lemma* smooth_bump_covering.mem_support_ind
- \+ *structure* smooth_bump_covering
- \+ *lemma* smooth_bump_function.R_pos
- \+ *lemma* smooth_bump_function.ball_subset
- \+ *lemma* smooth_bump_function.c_mem_support
- \+ *lemma* smooth_bump_function.closed_image_of_closed
- \+ *lemma* smooth_bump_function.closed_symm_image_closed_ball
- \+ *lemma* smooth_bump_function.closure_support_mem_nhds
- \+ *lemma* smooth_bump_function.closure_support_subset_chart_at_source
- \+ *lemma* smooth_bump_function.closure_support_subset_ext_chart_at_source
- \+ *lemma* smooth_bump_function.closure_support_subset_symm_image_closed_ball
- \+ *lemma* smooth_bump_function.coe_def
- \+ *lemma* smooth_bump_function.compact_closure_support
- \+ *lemma* smooth_bump_function.compact_symm_image_closed_ball
- \+ *lemma* smooth_bump_function.eq_on_source
- \+ *lemma* smooth_bump_function.eq_one
- \+ *lemma* smooth_bump_function.eventually_eq_of_mem_source
- \+ *lemma* smooth_bump_function.eventually_eq_one
- \+ *lemma* smooth_bump_function.eventually_eq_one_of_dist_lt
- \+ *lemma* smooth_bump_function.exists_r_pos_lt_subset_ball
- \+ *lemma* smooth_bump_function.image_eq_inter_preimage_of_subset_support
- \+ *lemma* smooth_bump_function.le_one
- \+ *lemma* smooth_bump_function.mem_Icc
- \+ *lemma* smooth_bump_function.nhds_basis_closure_support
- \+ *lemma* smooth_bump_function.nhds_basis_support
- \+ *lemma* smooth_bump_function.nhds_within_range_basis
- \+ *lemma* smooth_bump_function.nonempty_support
- \+ *lemma* smooth_bump_function.nonneg
- \+ *lemma* smooth_bump_function.one_of_dist_le
- \+ *lemma* smooth_bump_function.open_support
- \+ *lemma* smooth_bump_function.smooth_smul
- \+ *lemma* smooth_bump_function.support_eq_inter_preimage
- \+ *lemma* smooth_bump_function.support_eq_symm_image
- \+ *lemma* smooth_bump_function.support_mem_nhds
- \+ *lemma* smooth_bump_function.support_subset_source
- \+ *lemma* smooth_bump_function.support_update_r
- \+ *def* smooth_bump_function.to_fun
- \+ *def* smooth_bump_function.update_r
- \+ *lemma* smooth_bump_function.update_r_R
- \+ *lemma* smooth_bump_function.update_r_r
- \+ *structure* smooth_bump_function

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* ext_chart_preimage_open_of_open'
- \+ *lemma* ext_chart_preimage_open_of_open

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth_at.smul
- \+ *lemma* smooth_on.smul
- \+ *lemma* times_cont_mdiff_of_support
- \+ *lemma* times_cont_mdiff_on_ext_chart_at

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.is_closed_image
- \+ *lemma* continuous_linear_equiv.preimage_closure

Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/shrinking_lemma.lean
- \+ *lemma* exists_Union_eq_closed_subset
- \+ *lemma* exists_subset_Union_closed_subset



## [2021-03-31 09:30:06](https://github.com/leanprover-community/mathlib/commit/1fdce2f)
refactor(analysis/normed_space/basic): add semi_normed_ring ([#6889](https://github.com/leanprover-community/mathlib/pull/6889))
This is the natural continuation of [#6888](https://github.com/leanprover-community/mathlib/pull/6888) . We add here semi_normed_ring, semi_normed_comm_ring, semi_normed_space and semi_normed_algebra.
I didn't add `semi_normed_field`: the most important result for normed_field is `∥1∥ = 1`, that is false for `semi_normed_field`, making it a more or less useless notion. In particular a `semi_normed_space` is by definition a vector space over a `normed_field`.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* closure_ball
- \+/\- *lemma* dist_smul
- \+/\- *theorem* frontier_ball
- \+/\- *theorem* frontier_closed_ball
- \+/\- *theorem* interior_closed_ball
- \+/\- *lemma* nndist_smul
- \+/\- *lemma* nnnorm_norm
- \+/\- *lemma* nnnorm_one
- \+/\- *lemma* nnnorm_smul
- \+/\- *lemma* norm_algebra_map_eq
- \+/\- *lemma* norm_norm
- \+/\- *lemma* norm_smul
- \+/\- *lemma* norm_smul_of_nonneg
- \+/\- *lemma* normed_group.tendsto_at_top
- \+ *lemma* rescale_to_shell_semi_normed
- \+ *def* semi_normed_space.restrict_scalars



## [2021-03-31 03:01:59](https://github.com/leanprover-community/mathlib/commit/85c8961)
chore(scripts): update nolints.txt ([#6970](https://github.com/leanprover-community/mathlib/pull/6970))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2021-03-31 00:41:44](https://github.com/leanprover-community/mathlib/commit/8ed5c3c)
chore(topology/algebra/group_with_zero): continuity attributes ([#6965](https://github.com/leanprover-community/mathlib/pull/6965))
Some `@[continuity]` tags, requested at https://github.com/leanprover-community/mathlib/pull/6937#discussion_r604139611
#### Estimated changes
Modified src/topology/algebra/group_with_zero.lean
- \+/\- *lemma* continuous.div
- \+/\- *lemma* continuous.div_const
- \+/\- *lemma* continuous.fpow
- \+/\- *lemma* continuous.inv'



## [2021-03-31 00:41:43](https://github.com/leanprover-community/mathlib/commit/6f6ee00)
chore(data/finsupp): add simp lemmas about dom_congr ([#6963](https://github.com/leanprover-community/mathlib/pull/6963))
Inspired by [#6905](https://github.com/leanprover-community/mathlib/pull/6905)
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.dom_congr_refl
- \+ *lemma* finsupp.dom_congr_symm
- \+ *lemma* finsupp.dom_congr_trans



## [2021-03-30 20:36:57](https://github.com/leanprover-community/mathlib/commit/f2b433f)
refactor(data/equiv/basic): remove `equiv.set.range` ([#6960](https://github.com/leanprover-community/mathlib/pull/6960))
We already had `equiv.of_injective`, which duplicated the API. `of_injective` is the preferred naming, so we change all occurrences accordingly.
This also renames `equiv.set.range_of_left_inverse` to `equiv.of_left_inverse`, to match names like `linear_equiv.of_left_inverse`.
Note that the `congr` and `powerset` definitions which appear in the diff have just been reordered, and are otherwise unchanged.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.apply_of_injective_symm
- \+ *abbreviation* equiv.of_left_inverse'
- \+ *def* equiv.of_left_inverse
- \+ *lemma* equiv.of_left_inverse_eq_of_injective
- \- *theorem* equiv.set.apply_range_symm
- \- *abbreviation* equiv.set.range_of_left_inverse'
- \- *def* equiv.set.range_of_left_inverse

Modified src/data/equiv/denumerable.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/finite.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/perm/subgroup.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/logic/small.lean


Modified src/order/rel_iso.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/metric_space/isometry.lean




## [2021-03-30 20:36:56](https://github.com/leanprover-community/mathlib/commit/cf377e2)
chore(algebra/category/*): fix some names ([#6846](https://github.com/leanprover-community/mathlib/pull/6846))
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Module/monoidal.lean




## [2021-03-30 17:12:57](https://github.com/leanprover-community/mathlib/commit/33f443f)
feat(archive/imo): add 2011 Q5 ([#6927](https://github.com/leanprover-community/mathlib/pull/6927))
proof of IMO 2011 Q5
#### Estimated changes
Added archive/imo/imo2011_q5.lean
- \+ *theorem* imo2011_q5



## [2021-03-30 17:12:56](https://github.com/leanprover-community/mathlib/commit/0c0fb53)
feat(group_theory/perm/cycles): Order of is_cycle ([#6873](https://github.com/leanprover-community/mathlib/pull/6873))
The order of a cycle equals the cardinality of its support.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.gpow_apply_comm

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.order_of_is_cycle



## [2021-03-30 14:01:24](https://github.com/leanprover-community/mathlib/commit/a192783)
chore(algebra/direct_sum_graded): relax typeclass assumptions ([#6961](https://github.com/leanprover-community/mathlib/pull/6961))
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+/\- *def* direct_sum.ghas_mul.of_add_subgroups
- \+/\- *def* direct_sum.ghas_mul.of_add_submonoids
- \+/\- *def* direct_sum.ghas_mul.to_sigma_has_mul
- \+/\- *def* direct_sum.ghas_one.of_add_subgroups
- \+/\- *def* direct_sum.ghas_one.of_add_submonoids



## [2021-03-30 14:01:23](https://github.com/leanprover-community/mathlib/commit/ed6d94a)
chore(group_theory/group_action/defs): combine duplicated `comp_hom` and rename derivative definitions ([#6942](https://github.com/leanprover-community/mathlib/pull/6942))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Duplicate.20mul_action.20defs/near/232246589)
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean
- \- *def* ring_hom.comp_semimodule
- \+ *def* semimodule.comp_hom

Modified src/algebra/smul_with_zero.lean
- \+ *def* mul_action_with_zero.comp_hom
- \+ *def* smul_with_zero.comp_hom

Modified src/group_theory/group_action/defs.lean
- \+ *def* distrib_mul_action.comp_hom
- \- *def* monoid_hom.comp_distrib_mul_action
- \- *def* monoid_hom.comp_mul_action



## [2021-03-30 14:01:22](https://github.com/leanprover-community/mathlib/commit/e1f66f1)
feat(topology/algebra/group_with_zero): continuity of exponentiation to an integer power (`fpow`) ([#6937](https://github.com/leanprover-community/mathlib/pull/6937))
In a topological group-with-zero (more precisely, in a space with `has_continuous_inv'` and `has_continuous_mul`), the `k`-th power function is continuous for integer `k`, with the possible exception of at 0.
#### Estimated changes
Modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous.fpow
- \+ *lemma* continuous_at.fpow
- \+ *lemma* continuous_at_fpow
- \+ *lemma* continuous_on_fpow
- \+ *lemma* filter.tendsto.fpow
- \+ *lemma* tendsto_fpow



## [2021-03-30 14:01:21](https://github.com/leanprover-community/mathlib/commit/bcfaabf)
feat(data/set_like): remove repeated boilerplate from subobjects ([#6768](https://github.com/leanprover-community/mathlib/pull/6768))
This just scratches the surface, and removes all of the boilerplate that is just a consequence of the injective map to a `set`.
Already this trims more than 150 lines.
For every lemma of the form `set_like.*` added in this PR, the corresponding `submonoid.*`, `add_submonoid.*`, `sub_mul_action.*`, `submodule.*`, `subsemiring.*`, `subring.*`, `subfield.*`, `subalgebra.*`, and `intermediate_field.*` lemmas have been removed.
Often these lemmas only existed for one or two of these subtypes, so this means that we have lemmas for more things not fewer.
Note that while the `ext_iff`, `ext'`, and `ext'_iff` lemmas have been removed, we still need the `ext` lemma as `set_like.ext` cannot directly be tagged `@[ext]`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/subalgebra.lean
- \- *lemma* subalgebra.coe_injective
- \+/\- *theorem* subalgebra.ext
- \- *theorem* subalgebra.ext_iff
- \- *lemma* subalgebra.le_def
- \- *theorem* subalgebra.mem_coe

Modified src/algebra/direct_limit.lean


Modified src/algebra/lie/cartan_subalgebra.lean


Modified src/algebra/lie/subalgebra.lean


Modified src/algebra/lie/submodule.lean


Modified src/algebra/module/submodule.lean
- \- *lemma* submodule.coe_eq_coe
- \+/\- *lemma* submodule.coe_eq_zero
- \- *theorem* submodule.coe_injective
- \- *theorem* submodule.coe_set_eq
- \- *theorem* submodule.coe_sort_coe
- \- *theorem* submodule.ext'_iff
- \+/\- *theorem* submodule.ext
- \- *theorem* submodule.mem_coe

Modified src/algebra/module/submodule_lattice.lean
- \- *lemma* submodule.coe_subset_coe
- \- *lemma* submodule.exists_of_lt
- \- *lemma* submodule.le_def'
- \- *lemma* submodule.le_def
- \- *lemma* submodule.lt_def
- \- *lemma* submodule.lt_iff_le_and_exists
- \- *lemma* submodule.not_le_iff_exists

Modified src/algebra/pointwise.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/convex/cone.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/coeff.lean


Added src/data/set_like.lean
- \+ *lemma* set_like.coe_eq_coe
- \+ *theorem* set_like.coe_injective
- \+ *lemma* set_like.coe_mem
- \+ *lemma* set_like.coe_mk
- \+ *theorem* set_like.coe_set_eq
- \+ *theorem* set_like.coe_sort_coe
- \+ *lemma* set_like.coe_ssubset_coe
- \+ *lemma* set_like.coe_subset_coe
- \+ *lemma* set_like.exists_of_lt
- \+ *theorem* set_like.ext'
- \+ *theorem* set_like.ext'_iff
- \+ *theorem* set_like.ext
- \+ *theorem* set_like.ext_iff
- \+ *lemma* set_like.le_def
- \+ *lemma* set_like.lt_iff_le_and_exists
- \+ *theorem* set_like.mem_coe
- \+ *lemma* set_like.not_le_iff_exists

Modified src/field_theory/adjoin.lean


Modified src/field_theory/finite/polynomial.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/intermediate_field.lean
- \- *theorem* intermediate_field.ext'
- \+ *lemma* intermediate_field.mem_carrier
- \- *lemma* intermediate_field.mem_coe

Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean
- \- *lemma* subfield.coe_coe
- \- *lemma* subfield.coe_ssubset_coe
- \- *lemma* subfield.coe_subset_coe
- \- *theorem* subfield.ext'
- \+/\- *theorem* subfield.ext
- \- *lemma* subfield.le_def
- \+ *lemma* subfield.mem_carrier
- \- *lemma* subfield.mem_coe

Modified src/group_theory/coset.lean


Modified src/group_theory/group_action/sub_mul_action.lean
- \- *lemma* sub_mul_action.coe_eq_coe
- \- *theorem* sub_mul_action.coe_injective
- \- *lemma* sub_mul_action.coe_mem
- \- *theorem* sub_mul_action.coe_set_eq
- \- *theorem* sub_mul_action.coe_sort_coe
- \- *theorem* sub_mul_action.ext'_iff
- \+/\- *theorem* sub_mul_action.ext
- \+ *lemma* sub_mul_action.mem_carrier
- \- *theorem* sub_mul_action.mem_coe

Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/subgroup.lean
- \- *lemma* subgroup.coe_coe
- \- *lemma* subgroup.coe_subset_coe
- \- *theorem* subgroup.ext'
- \+/\- *theorem* subgroup.ext
- \- *lemma* subgroup.le_def
- \+ *lemma* subgroup.mem_carrier
- \- *lemma* subgroup.mem_coe

Modified src/group_theory/submonoid/basic.lean
- \- *lemma* submonoid.coe_coe
- \- *lemma* submonoid.coe_eq_coe
- \- *lemma* submonoid.coe_injective
- \- *lemma* submonoid.coe_ssubset_coe
- \- *lemma* submonoid.coe_subset_coe
- \+/\- *lemma* submonoid.copy_eq
- \- *theorem* submonoid.ext'
- \- *lemma* submonoid.le_def
- \- *lemma* submonoid.mem_coe

Modified src/group_theory/submonoid/membership.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/pi.lean


Modified src/linear_algebra/prod.lean


Modified src/linear_algebra/projection.lean


Modified src/linear_algebra/std_basis.lean


Modified src/ring_theory/adjoin/basic.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/hahn_series.lean


Modified src/ring_theory/ideal/basic.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/subring.lean
- \- *lemma* subring.coe_coe
- \- *lemma* subring.coe_ssubset_coe
- \- *lemma* subring.coe_subset_coe
- \- *theorem* subring.ext'
- \+/\- *theorem* subring.ext
- \- *lemma* subring.le_def
- \+ *lemma* subring.mem_carrier
- \- *lemma* subring.mem_coe

Modified src/ring_theory/subsemiring.lean
- \- *lemma* subsemiring.coe_coe
- \- *lemma* subsemiring.coe_ssubset_coe
- \- *lemma* subsemiring.coe_subset_coe
- \- *theorem* subsemiring.ext'
- \+/\- *theorem* subsemiring.ext
- \- *lemma* subsemiring.le_def
- \+ *lemma* subsemiring.mem_carrier
- \- *lemma* subsemiring.mem_coe

Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/continuous_function/algebra.lean




## [2021-03-30 10:02:55](https://github.com/leanprover-community/mathlib/commit/b0ece6f)
chore(data/set/{basic,countable}): add, rename, golf ([#6935](https://github.com/leanprover-community/mathlib/pull/6935))
* add `set.range_prod_map` and `set.countable.image2`;
* rename `set.countable_prod` to `set.countable.prod`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.range_prod_map

Modified src/data/set/countable.lean
- \+ *lemma* set.countable.image2
- \- *lemma* set.countable_prod

Modified src/topology/G_delta.lean




## [2021-03-30 10:02:54](https://github.com/leanprover-community/mathlib/commit/7e109c4)
feat(measure_theory/lp_space): continuous functions on compact space are in Lp ([#6919](https://github.com/leanprover-community/mathlib/pull/6919))
Continuous functions on a compact space equipped with a finite Borel measure are in Lp, and the inclusion is a bounded linear map.  This follows directly by transferring the construction in [#6878](https://github.com/leanprover-community/mathlib/pull/6878) for bounded continuous functions, using the fact that continuous function on a compact space are bounded.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.coe_to_linear_isometry

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.op_norm_comp_linear_isometry_equiv
- \+ *lemma* continuous_linear_map.op_norm_subsingleton

Modified src/measure_theory/lp_space.lean
- \+ *lemma* continuous_map.coe_to_Lp
- \+ *def* continuous_map.to_Lp
- \+ *lemma* continuous_map.to_Lp_comp_forget_boundedness
- \+ *lemma* continuous_map.to_Lp_def
- \+ *lemma* continuous_map.to_Lp_norm_eq_to_Lp_norm_coe
- \+ *lemma* continuous_map.to_Lp_norm_le

Modified src/topology/continuous_function/basic.lean


Modified src/topology/continuous_function/compact.lean




## [2021-03-30 10:02:53](https://github.com/leanprover-community/mathlib/commit/3e67f50)
feat(analysis/normed_space/inner_product): isometry of ℂ with Euclidean space ([#6877](https://github.com/leanprover-community/mathlib/pull/6877))
`ℂ` is isometric to `fin 2 → ℝ` with the Euclidean inner product.  The isometry given here is that defined by the ordered basis {1, i} for `ℂ`.
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *def* complex.isometry_euclidean
- \+ *lemma* complex.isometry_euclidean_apply_one
- \+ *lemma* complex.isometry_euclidean_apply_zero
- \+ *lemma* complex.isometry_euclidean_proj_eq_self
- \+ *lemma* complex.isometry_euclidean_symm_apply



## [2021-03-30 07:31:27](https://github.com/leanprover-community/mathlib/commit/877af10)
chore(algebra/big_operators/order): generalize some lemmas to `ordered_comm_semiring` ([#6950](https://github.com/leanprover-community/mathlib/pull/6950))
#### Estimated changes
Modified src/algebra/big_operators/order.lean




## [2021-03-30 07:31:27](https://github.com/leanprover-community/mathlib/commit/fe00980)
feat(topology/compact_open): β ≃ₜ C(α, β) if α has a single element ([#6946](https://github.com/leanprover-community/mathlib/pull/6946))
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *def* homeomorph.continuous_map_of_unique
- \+ *lemma* homeomorph.continuous_map_of_unique_apply
- \+ *lemma* homeomorph.continuous_map_of_unique_symm_apply



## [2021-03-30 03:44:59](https://github.com/leanprover-community/mathlib/commit/8d398a8)
chore(scripts): update nolints.txt ([#6957](https://github.com/leanprover-community/mathlib/pull/6957))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-30 03:44:58](https://github.com/leanprover-community/mathlib/commit/b4ce9b7)
feat(group_theory/order_of_element): exists_pow_eq_self_of_coprime ([#6875](https://github.com/leanprover-community/mathlib/pull/6875))
If `n` is coprime to the order of `g`, then there exists an `m` such that `(g ^ n) ^ m = g`.
#### Estimated changes
Modified src/data/int/gcd.lean
- \+ *lemma* nat.exists_mul_mod_eq_gcd
- \+ *lemma* nat.exists_mul_mod_eq_one_of_coprime

Modified src/group_theory/order_of_element.lean
- \+ *lemma* exists_pow_eq_self_of_coprime



## [2021-03-30 03:44:57](https://github.com/leanprover-community/mathlib/commit/b449a3c)
feat(order/ideal, order/pfilter, order/prime_ideal): added `is_ideal`, `is_pfilter`, `is_prime`, `is_maximal`, `prime_pair` ([#6656](https://github.com/leanprover-community/mathlib/pull/6656))
Proved basic lemmas about them. Also extended the is_proper API.
Made the `pfilter`arguments of some lemmas explicit:
- `pfilter.nonempty`
- `pfilter.directed`
#### Estimated changes
Modified src/order/boolean_algebra.lean
- \+ *theorem* is_compl.eq_compl

Modified src/order/ideal.lean
- \+ *lemma* is_coatom.is_maximal
- \+ *lemma* is_coatom.is_proper
- \+ *lemma* order.ideal.ext'_iff
- \+ *lemma* order.ideal.ext_set_eq
- \+ *lemma* order.ideal.is_ideal
- \+ *lemma* order.ideal.is_maximal.is_coatom'
- \+ *lemma* order.ideal.is_maximal.is_coatom
- \+ *lemma* order.ideal.is_maximal_iff_is_coatom
- \+ *lemma* order.ideal.is_proper.ne_top
- \+ *lemma* order.ideal.is_proper_iff_ne_top
- \+ *lemma* order.ideal.is_proper_of_ne_top
- \+ *lemma* order.ideal.is_proper_of_not_mem
- \- *lemma* order.ideal.proper_of_ne_top
- \- *lemma* order.ideal.proper_of_not_mem
- \+ *lemma* order.ideal.top_coe
- \+/\- *lemma* order.ideal.top_of_mem_top
- \+ *def* order.is_ideal.to_ideal
- \+ *structure* order.is_ideal

Modified src/order/pfilter.lean
- \+ *def* order.is_pfilter.to_pfilter
- \+ *def* order.is_pfilter
- \+ *lemma* order.pfilter.directed
- \+ *lemma* order.pfilter.ext
- \+ *lemma* order.pfilter.inf_mem
- \+ *lemma* order.pfilter.inf_mem_iff
- \+ *lemma* order.pfilter.is_pfilter
- \+ *lemma* order.pfilter.mem_of_le
- \+ *lemma* order.pfilter.mem_of_mem_of_le
- \+ *lemma* order.pfilter.nonempty
- \+ *def* order.pfilter.principal
- \+ *lemma* order.pfilter.principal_le_iff
- \+ *lemma* order.pfilter.top_mem
- \+ *structure* order.pfilter
- \- *lemma* pfilter.directed
- \- *lemma* pfilter.ext
- \- *lemma* pfilter.inf_mem
- \- *lemma* pfilter.inf_mem_iff
- \- *lemma* pfilter.mem_of_le
- \- *lemma* pfilter.mem_of_mem_of_le
- \- *lemma* pfilter.nonempty
- \- *def* pfilter.principal
- \- *lemma* pfilter.principal_le_iff
- \- *lemma* pfilter.top_mem
- \- *structure* pfilter

Added src/order/prime_ideal.lean
- \+ *def* order.ideal.is_prime.to_prime_pair
- \+ *lemma* order.ideal.prime_pair.F_is_prime
- \+ *lemma* order.ideal.prime_pair.F_union_I
- \+ *lemma* order.ideal.prime_pair.I_is_prime
- \+ *lemma* order.ideal.prime_pair.I_is_proper
- \+ *lemma* order.ideal.prime_pair.I_union_F
- \+ *lemma* order.ideal.prime_pair.compl_F_eq_I
- \+ *lemma* order.ideal.prime_pair.compl_I_eq_F
- \+ *lemma* order.ideal.prime_pair.disjoint
- \+ *structure* order.ideal.prime_pair
- \+ *def* order.pfilter.is_prime.to_prime_pair



## [2021-03-29 23:43:35](https://github.com/leanprover-community/mathlib/commit/e5c112d)
feat(category_theory/arrow): simp lemmas for lifts involving arrow.mk ([#6953](https://github.com/leanprover-community/mathlib/pull/6953))
These came up during review of [#6852](https://github.com/leanprover-community/mathlib/pull/6852).
#### Estimated changes
Modified src/category_theory/arrow.lean
- \+ *lemma* category_theory.arrow.lift.fac_left_of_from_mk
- \+ *lemma* category_theory.arrow.lift.fac_right_of_to_mk



## [2021-03-29 23:43:35](https://github.com/leanprover-community/mathlib/commit/87bc893)
feat(group_theory/{subgroup, order_of_element}): refactors simple groups, classifies finite simple abelian/solvable groups ([#6926](https://github.com/leanprover-community/mathlib/pull/6926))
Refactors the deprecated `simple_group` to a new `is_simple_group`
Shows that all cyclic groups of prime order are simple
Shows that all simple `comm_group`s are cyclic
Shows that all simple finite `comm_group`s have prime order
Shows that a simple group is solvable iff it is commutative
#### Estimated changes
Modified src/deprecated/subgroup.lean
- \- *theorem* additive.simple_add_group_iff
- \- *theorem* multiplicative.simple_group_iff
- \- *lemma* simple_group_of_surjective

Modified src/group_theory/order_of_element.lean
- \+ *theorem* comm_group.is_simple_iff_is_cyclic_and_prime_card
- \+ *theorem* is_simple_group.prime_card
- \+ *lemma* is_simple_group_of_prime_card

Modified src/group_theory/solvable.lean
- \+ *lemma* is_simple_group.comm_iff_is_solvable
- \+ *lemma* is_simple_group.derived_series_succ

Modified src/group_theory/subgroup.lean
- \+ *lemma* is_simple_group.is_simple_group_of_surjective
- \+ *lemma* subgroup.eq_bot_of_subsingleton
- \+ *lemma* subgroup.normal.eq_bot_or_eq_top



## [2021-03-29 23:43:33](https://github.com/leanprover-community/mathlib/commit/ad4aca0)
feat(topology/local_homeomorph): add `is_image`, `piecewise`, and `disjoint_union` ([#6804](https://github.com/leanprover-community/mathlib/pull/6804))
Also add `local_equiv.copy` and `local_homeomorph.replace_equiv` and use them for `local_equiv.disjoint_union` and `local_homeomorph.disjoint_union.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+ *def* local_equiv.copy
- \+ *lemma* local_equiv.copy_eq_self
- \+ *lemma* local_equiv.disjoint_union_eq_piecewise
- \+ *lemma* local_equiv.is_image.inter_eq_of_inter_eq_of_eq_on
- \+ *lemma* local_equiv.is_image.symm_eq_on_of_inter_eq_of_eq_on
- \+ *lemma* local_equiv.is_image_source_target_of_disjoint

Modified src/data/set/basic.lean
- \+/\- *theorem* set.diff_union_self
- \+ *lemma* set.ite_inter_of_inter_eq
- \+ *lemma* set.ite_left
- \+ *lemma* set.ite_right
- \+ *theorem* set.preimage_ite
- \+ *lemma* set.subset_ite
- \+/\- *theorem* set.union_diff_self

Modified src/data/set/function.lean
- \+ *lemma* set.eq_on_empty
- \+/\- *lemma* set.piecewise_eq_of_mem
- \+/\- *lemma* set.piecewise_eq_of_not_mem

Modified src/geometry/manifold/charted_space.lean


Modified src/topology/basic.lean
- \+ *lemma* frontier_subset_closure
- \+ *lemma* is_open.inter_frontier_eq
- \+ *lemma* is_open.inter_frontier_eq_empty_of_disjoint

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_piecewise_ite'
- \+ *lemma* continuous_on_piecewise_ite
- \+ *lemma* ite_inter_closure_compl_eq_of_inter_frontier_eq
- \+ *lemma* ite_inter_closure_eq_of_inter_frontier_eq

Modified src/topology/local_homeomorph.lean
- \+ *def* local_homeomorph.disjoint_union
- \+/\- *lemma* local_homeomorph.image_mem_nhds
- \+ *lemma* local_homeomorph.is_image.apply_mem_iff
- \+ *lemma* local_homeomorph.is_image.iff_preimage_eq'
- \+ *lemma* local_homeomorph.is_image.iff_preimage_eq
- \+ *lemma* local_homeomorph.is_image.iff_symm_preimage_eq'
- \+ *lemma* local_homeomorph.is_image.iff_symm_preimage_eq
- \+ *lemma* local_homeomorph.is_image.image_eq
- \+ *lemma* local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on
- \+ *lemma* local_homeomorph.is_image.is_open_iff
- \+ *lemma* local_homeomorph.is_image.left_inv_on_piecewise
- \+ *lemma* local_homeomorph.is_image.map_nhds_within_eq
- \+ *lemma* local_homeomorph.is_image.of_image_eq
- \+ *lemma* local_homeomorph.is_image.of_symm_image_eq
- \+ *def* local_homeomorph.is_image.restr
- \+ *lemma* local_homeomorph.is_image.symm_apply_mem_iff
- \+ *lemma* local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on
- \+ *lemma* local_homeomorph.is_image.symm_iff
- \+ *lemma* local_homeomorph.is_image.symm_image_eq
- \+ *lemma* local_homeomorph.is_image.symm_maps_to
- \+ *lemma* local_homeomorph.is_image.to_local_equiv
- \+ *def* local_homeomorph.is_image
- \+ *lemma* local_homeomorph.is_image_source_target
- \+ *lemma* local_homeomorph.is_image_source_target_of_disjoint
- \+/\- *lemma* local_homeomorph.map_nhds_eq
- \+ *def* local_homeomorph.piecewise
- \+ *lemma* local_homeomorph.piecewise_coe
- \+ *lemma* local_homeomorph.piecewise_to_local_equiv
- \+/\- *lemma* local_homeomorph.preimage_open_of_open_symm
- \+/\- *lemma* local_homeomorph.prod_to_local_equiv
- \+ *def* local_homeomorph.replace_equiv
- \+ *lemma* local_homeomorph.replace_equiv_eq_self
- \+/\- *lemma* local_homeomorph.source_preimage_target
- \+/\- *lemma* local_homeomorph.symm_map_nhds_eq
- \+ *lemma* local_homeomorph.symm_piecewise
- \+/\- *lemma* local_homeomorph.tendsto_symm



## [2021-03-29 20:11:52](https://github.com/leanprover-community/mathlib/commit/50225da)
feat(data/fin): fin n.succ is an add_comm_group ([#6898](https://github.com/leanprover-community/mathlib/pull/6898))
This just moves the proof out of `data.zmod` basic.
Moving the full ring instance is left for future work, as `modeq`, used to prove left_distrib, is not available to import in `data/fin/basic`.
Note this adds an import of `data.int.basic` to `data.fin.basic`. I think this is probably acceptable?
#### Estimated changes
Modified src/data/fin.lean


Modified src/data/zmod/basic.lean
- \- *def* fin.comm_ring
- \- *def* fin.comm_semigroup
- \- *def* fin.has_neg



## [2021-03-29 18:22:24](https://github.com/leanprover-community/mathlib/commit/8b7c8a4)
chore(topology/instances/real): golf ([#6945](https://github.com/leanprover-community/mathlib/pull/6945))
#### Estimated changes
Modified src/topology/instances/real.lean




## [2021-03-29 18:22:23](https://github.com/leanprover-community/mathlib/commit/3fdf529)
chore(topology/instances/ennreal): golf ([#6944](https://github.com/leanprover-community/mathlib/pull/6944))
#### Estimated changes
Modified src/topology/instances/ennreal.lean




## [2021-03-29 13:12:21](https://github.com/leanprover-community/mathlib/commit/1677653)
chore(*): long lines ([#6939](https://github.com/leanprover-community/mathlib/pull/6939))
Except for URLs, references to books, and `src/tactic/*`, this should be very close to the last of our long lines.
#### Estimated changes
Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/data/sym2.lean


Modified src/meta/expr_lens.lean


Modified src/meta/rb_map.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/fixed_points.lean


Modified src/order/lexicographic.lean


Modified src/order/ord_continuous.lean


Modified src/order/pilex.lean


Modified src/order/preorder_hom.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/set_theory/surreal.lean


Modified src/system/random/basic.lean
- \+/\- *def* rand.random_series_r

Modified src/tactic/abel.lean


Modified src/tactic/cache.lean


Modified src/tactic/chain.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/hint.lean


Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* uniform_space.ring_sep_quot

Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/omega_complete_partial_order.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/sheaf.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/stalks.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2021-03-29 13:12:19](https://github.com/leanprover-community/mathlib/commit/f1fe129)
feat(category_theory/images): instance for precomposition by iso ([#6931](https://github.com/leanprover-community/mathlib/pull/6931))
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.image.pre_comp_ι



## [2021-03-29 13:12:17](https://github.com/leanprover-community/mathlib/commit/d2e5976)
feat(category_theory/limits/terminal): constructor for is_terminal ([#6929](https://github.com/leanprover-community/mathlib/pull/6929))
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.is_initial.of_unique
- \+ *def* category_theory.limits.is_terminal.of_unique



## [2021-03-29 13:12:15](https://github.com/leanprover-community/mathlib/commit/cf56f88)
feat(category_theory/limits/zero): functor categories have zero morphisms ([#6928](https://github.com/leanprover-community/mathlib/pull/6928))
#### Estimated changes
Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.zero_app



## [2021-03-29 13:12:14](https://github.com/leanprover-community/mathlib/commit/407ad21)
feat(algebra.smul_with_zero): add mul_zero_class.to_smul_with_zero ([#6911](https://github.com/leanprover-community/mathlib/pull/6911))
#### Estimated changes
Modified src/algebra/smul_with_zero.lean




## [2021-03-29 13:12:12](https://github.com/leanprover-community/mathlib/commit/fe29f88)
feat(data/nat/basic):  (n+1) / 2 ≤ n ([#6863](https://github.com/leanprover-community/mathlib/pull/6863))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_eq_sub_mod_div
- \+ *lemma* nat.div_le_iff_le_mul_add_pred
- \+ *lemma* nat.lt_iff_le_pred
- \+ *lemma* nat.lt_mul_div_succ
- \+ *lemma* nat.mod_div_self
- \+ *lemma* nat.mul_div_le



## [2021-03-29 13:12:11](https://github.com/leanprover-community/mathlib/commit/66ee65c)
feat(category): structured arrows ([#6830](https://github.com/leanprover-community/mathlib/pull/6830))
Factored out from [#6820](https://github.com/leanprover-community/mathlib/pull/6820).
#### Estimated changes
Modified src/category_theory/elements.lean
- \- *def* category_theory.category_of_elements.comma_equivalence
- \- *lemma* category_theory.category_of_elements.comma_equivalence_functor
- \- *lemma* category_theory.category_of_elements.comma_equivalence_inverse
- \- *def* category_theory.category_of_elements.from_comma
- \- *lemma* category_theory.category_of_elements.from_comma_map
- \- *lemma* category_theory.category_of_elements.from_comma_obj
- \+ *def* category_theory.category_of_elements.from_structured_arrow
- \+ *lemma* category_theory.category_of_elements.from_structured_arrow_map
- \+ *lemma* category_theory.category_of_elements.from_structured_arrow_obj
- \+ *def* category_theory.category_of_elements.structured_arrow_equivalence
- \- *def* category_theory.category_of_elements.to_comma
- \- *lemma* category_theory.category_of_elements.to_comma_map
- \+ *lemma* category_theory.category_of_elements.to_comma_map_right
- \- *lemma* category_theory.category_of_elements.to_comma_obj
- \+ *def* category_theory.category_of_elements.to_structured_arrow
- \+ *lemma* category_theory.category_of_elements.to_structured_arrow_obj

Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/over.lean
- \+/\- *def* category_theory.over
- \+/\- *def* category_theory.under

Added src/category_theory/structured_arrow.lean
- \+ *lemma* category_theory.costructured_arrow.eq_mk
- \+ *def* category_theory.costructured_arrow.hom_mk
- \+ *def* category_theory.costructured_arrow.iso_mk
- \+ *def* category_theory.costructured_arrow.map
- \+ *lemma* category_theory.costructured_arrow.map_comp
- \+ *lemma* category_theory.costructured_arrow.map_id
- \+ *lemma* category_theory.costructured_arrow.map_mk
- \+ *def* category_theory.costructured_arrow.mk
- \+ *lemma* category_theory.costructured_arrow.mk_hom_eq_self
- \+ *def* category_theory.costructured_arrow.mk_id_terminal
- \+ *lemma* category_theory.costructured_arrow.mk_left
- \+ *lemma* category_theory.costructured_arrow.mk_right
- \+ *def* category_theory.costructured_arrow
- \+ *lemma* category_theory.structured_arrow.eq_mk
- \+ *def* category_theory.structured_arrow.hom_mk
- \+ *def* category_theory.structured_arrow.iso_mk
- \+ *def* category_theory.structured_arrow.map
- \+ *lemma* category_theory.structured_arrow.map_comp
- \+ *lemma* category_theory.structured_arrow.map_id
- \+ *lemma* category_theory.structured_arrow.map_mk
- \+ *def* category_theory.structured_arrow.mk
- \+ *lemma* category_theory.structured_arrow.mk_hom_eq_self
- \+ *def* category_theory.structured_arrow.mk_id_initial
- \+ *lemma* category_theory.structured_arrow.mk_left
- \+ *lemma* category_theory.structured_arrow.mk_right
- \+ *def* category_theory.structured_arrow

Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean




## [2021-03-29 13:12:10](https://github.com/leanprover-community/mathlib/commit/318cb4b)
feat(category_theory): essentially_small categories ([#6801](https://github.com/leanprover-community/mathlib/pull/6801))
Preparation for `well_powered`, then for `complete_semilattice_Inf|Sup` on `subobject X`, then for work on chain complexes.
#### Estimated changes
Modified src/category_theory/equivalence.lean


Added src/category_theory/essentially_small.lean
- \+ *def* category_theory.equiv_small_model
- \+ *lemma* category_theory.essentially_small.mk'
- \+ *lemma* category_theory.essentially_small_congr
- \+ *theorem* category_theory.essentially_small_iff
- \+ *theorem* category_theory.essentially_small_iff_of_thin
- \+ *lemma* category_theory.locally_small_congr
- \+ *def* category_theory.shrink_homs.equivalence
- \+ *def* category_theory.shrink_homs.from_shrink_homs
- \+ *lemma* category_theory.shrink_homs.from_to
- \+ *def* category_theory.shrink_homs.functor
- \+ *def* category_theory.shrink_homs.inverse
- \+ *lemma* category_theory.shrink_homs.to_from
- \+ *def* category_theory.shrink_homs.to_shrink_homs
- \+ *def* category_theory.shrink_homs
- \+ *def* category_theory.small_model

Modified src/category_theory/skeletal.lean
- \+ *def* category_theory.equivalence.skeleton_equiv
- \+ *lemma* category_theory.skeleton_skeletal

Modified src/data/equiv/basic.lean
- \+ *def* equiv.punit_of_nonempty_of_subsingleton

Modified src/data/fintype/basic.lean


Added src/logic/small.lean
- \+ *def* equiv_shrink
- \+ *def* shrink
- \+ *lemma* small.mk'
- \+ *theorem* small_congr
- \+ *theorem* small_of_injective



## [2021-03-29 13:12:08](https://github.com/leanprover-community/mathlib/commit/8d8b64e)
feat(data/equiv/mul_add_aut): adding conjugation in an additive group ([#6774](https://github.com/leanprover-community/mathlib/pull/6774))
assuming `[add_group G]` this defines `G ->+ additive (add_aut G)`
#### Estimated changes
Modified src/data/equiv/mul_add_aut.lean
- \+ *def* add_aut.conj
- \+ *lemma* add_aut.conj_apply
- \+ *lemma* add_aut.conj_inv_apply
- \+ *lemma* add_aut.conj_symm_apply
- \+/\- *lemma* mul_aut.conj_inv_apply



## [2021-03-29 08:42:19](https://github.com/leanprover-community/mathlib/commit/2ad4a4c)
chore(group_theory/subgroup,logic/nontrivial): golf ([#6934](https://github.com/leanprover-community/mathlib/pull/6934))
#### Estimated changes
Modified src/group_theory/subgroup.lean


Modified src/logic/nontrivial.lean
- \+ *lemma* nontrivial_iff_exists_ne
- \+ *lemma* subtype.nontrivial_iff_exists_ne



## [2021-03-29 05:18:50](https://github.com/leanprover-community/mathlib/commit/5ab177a)
chore(topology/instances/real): remove instance `real_maps_algebra` ([#6920](https://github.com/leanprover-community/mathlib/pull/6920))
Remove 
```lean
instance reals_semimodule : has_continuous_smul ℝ ℝ
instance real_maps_algebra {α : Type*} [topological_space α] : algebra ℝ C(α, ℝ)
```
These are not used explicitly anywhere in the library, I suspect because if needed they can be found by typeclass inference.  Deleting them cleans up the import hierarchy by requiring many fewer files to import `topology.continuous_function.algebra`.
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/instances/real.lean




## [2021-03-29 03:17:36](https://github.com/leanprover-community/mathlib/commit/cb1d1c6)
chore(scripts): update nolints.txt ([#6933](https://github.com/leanprover-community/mathlib/pull/6933))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-29 03:17:36](https://github.com/leanprover-community/mathlib/commit/f290000)
feat(data/equiv/fin): rename sum_fin_sum_equiv to fin_sum_fin_equiv ([#6857](https://github.com/leanprover-community/mathlib/pull/6857))
Renames `sum_fin_sum_equiv` to `fin_sum_fin_equiv` (as discussed 
[on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/sum_fin_add_comm_equiv))
Introduces a version with `fin(n + m)` instead of `fin(m + n)` 
Adds a bunch of simp lemmas for applying these (and their inverses)
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *def* fin_sum_fin_equiv
- \+ *lemma* fin_sum_fin_equiv_apply_left
- \+ *lemma* fin_sum_fin_equiv_apply_right
- \+ *lemma* fin_sum_fin_equiv_symm_apply_left
- \+ *lemma* fin_sum_fin_equiv_symm_apply_right
- \- *def* sum_fin_sum_equiv

Modified src/ring_theory/finiteness.lean




## [2021-03-28 19:54:49](https://github.com/leanprover-community/mathlib/commit/8e275a3)
fix(order/complete_lattice): fix typo in docstring ([#6925](https://github.com/leanprover-community/mathlib/pull/6925))
#### Estimated changes
Modified src/order/complete_lattice.lean




## [2021-03-28 19:54:48](https://github.com/leanprover-community/mathlib/commit/a17f38f)
feat(measure_theory/lp_space): bounded continuous functions are in Lp ([#6878](https://github.com/leanprover-community/mathlib/pull/6878))
Under appropriate conditions (finite Borel measure, second-countable), a bounded continuous function is in L^p.  The main result of this PR is `bounded_continuous_function.to_Lp`, which provides this operation as a bounded linear map.  There are also several variations.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.to_real_le_coe_of_le_coe

Modified src/measure_theory/ae_eq_fun.lean
- \+ *lemma* continuous_map.coe_fn_to_ae_eq_fun
- \+ *def* continuous_map.to_ae_eq_fun
- \+ *def* continuous_map.to_ae_eq_fun_linear_map
- \+ *def* continuous_map.to_ae_eq_fun_mul_hom

Modified src/measure_theory/lp_space.lean
- \+ *lemma* bounded_continuous_function.Lp_norm_le
- \+ *lemma* bounded_continuous_function.mem_Lp
- \+ *def* bounded_continuous_function.to_Lp
- \+ *def* bounded_continuous_function.to_Lp_hom
- \+ *lemma* bounded_continuous_function.to_Lp_norm_le
- \+ *def* measure_theory.Lp.Lp_submodule
- \+ *lemma* measure_theory.Lp.coe_Lp_submodule
- \+ *lemma* measure_theory.Lp.mem_Lp_of_ae_bound
- \+ *lemma* measure_theory.Lp.norm_le_of_ae_bound
- \+ *lemma* measure_theory.mem_ℒp.of_bound
- \+ *lemma* measure_theory.snorm_le_of_ae_bound

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.coe_measure_univ_nnreal
- \+ *def* measure_theory.measure_univ_nnreal
- \+ *lemma* measure_theory.measure_univ_nnreal_eq_zero
- \+ *lemma* measure_theory.measure_univ_nnreal_pos
- \+ *lemma* measure_theory.measure_univ_nnreal_zero

Modified src/topology/continuous_function/bounded.lean
- \+ *def* bounded_continuous_function.forget_boundedness_linear_map



## [2021-03-28 16:13:09](https://github.com/leanprover-community/mathlib/commit/4487e73)
feat(order/bounded_lattice): is_total, coe_sup and unique_maximal lemmas ([#6922](https://github.com/leanprover-community/mathlib/pull/6922))
A few little additions for with_top and with_bot.
#### Estimated changes
Modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_minimal
- \+ *lemma* eq_top_of_maximal
- \+ *lemma* with_bot.coe_inf
- \+ *lemma* with_bot.coe_sup



## [2021-03-28 16:13:08](https://github.com/leanprover-community/mathlib/commit/7285fb6)
feat(data/complex/circle): circle is a Lie group ([#6907](https://github.com/leanprover-community/mathlib/pull/6907))
Define `circle` to be the unit circle in `ℂ` and give it the structure of a Lie group.  Also define `exp_map_circle` to be the natural map `λ t, exp (t * I)` from `ℝ` to `circle`, and give it (separately) the structures of a group homomorphism and a smooth map (we seem not to have the definition of a Lie group homomorphism).
#### Estimated changes
Modified src/data/complex/module.lean
- \+ *lemma* complex.findim_real_complex_fact

Added src/geometry/manifold/instances/circle.lean
- \+ *lemma* abs_eq_of_mem_circle
- \+ *def* circle
- \+ *lemma* circle_def
- \+ *lemma* coe_div_circle
- \+ *lemma* coe_inv_circle
- \+ *def* exp_map_circle
- \+ *def* exp_map_circle_hom
- \+ *lemma* mem_circle_iff_abs
- \+ *lemma* times_cont_mdiff_exp_map_circle



## [2021-03-28 14:22:34](https://github.com/leanprover-community/mathlib/commit/accb9d2)
fix(topology/algebra/mul_action): fix typo in instance name ([#6921](https://github.com/leanprover-community/mathlib/pull/6921))
#### Estimated changes
Modified src/topology/algebra/mul_action.lean




## [2021-03-28 12:00:37](https://github.com/leanprover-community/mathlib/commit/0e4760b)
refactor(measure_theory): add typeclasses for measurability of operations ([#6832](https://github.com/leanprover-community/mathlib/pull/6832))
With these typeclasses and lemmas we can use, e.g., `measurable.mul` for any type with measurable `uncurry (*)`, not only those with `has_continuous_mul`.
New typeclasses:
* `has_measurable_add`, `has_measurable_add₂`: measurable left/right addition and measurable `uncurry (+)`;
* `has_measurable_mul`, `has_measurable_mul₂`: measurable left/right multiplication and measurable `uncurry (*)`;
* `has_measurable_pow`: measurable `uncurry (^)`
* `has_measurable_sub`, `has_measurable_sub₂`: measurable left/right subtraction and measurable `λ (a, b), a - b`
* `has_measurable_div`, `has_measurable_div₂` : measurability of division as a function of numerator/denominator and measurability of `λ (a, b), a / b`;
* `has_measurable_neg`, `has_measurable_inv`: measurable negation/inverse;
* `has_measurable_const_smul`, `has_measurable_smul`: measurable `λ x, c • x` and measurable `λ (c, x), c • x`
#### Estimated changes
Modified src/analysis/mean_inequalities.lean


Modified src/analysis/special_functions/pow.lean
- \- *lemma* ae_measurable.ennreal_rpow_const
- \- *lemma* ae_measurable.rpow_const
- \- *lemma* ennreal.measurable_rpow
- \- *lemma* ennreal.measurable_rpow_const
- \- *lemma* measurable.cpow
- \- *lemma* measurable.ennreal_rpow
- \- *lemma* measurable.ennreal_rpow_const
- \- *lemma* measurable.nnreal_rpow
- \- *lemma* measurable.nnreal_rpow_const
- \- *lemma* measurable.rpow
- \- *lemma* measurable.rpow_const
- \- *lemma* real.measurable_rpow_const

Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/ae_eq_fun_metric.lean


Added src/measure_theory/arithmetic.lean
- \+ *lemma* ae_measurable.const_div
- \+ *lemma* ae_measurable.const_mul
- \+ *lemma* ae_measurable.const_pow
- \+ *lemma* ae_measurable.const_smul'
- \+ *lemma* ae_measurable.const_smul
- \+ *lemma* ae_measurable.div
- \+ *lemma* ae_measurable.div_const
- \+ *lemma* ae_measurable.inv
- \+ *lemma* ae_measurable.mul
- \+ *lemma* ae_measurable.mul_const
- \+ *lemma* ae_measurable.pow
- \+ *lemma* ae_measurable.pow_const
- \+ *lemma* ae_measurable.smul
- \+ *lemma* ae_measurable.smul_const
- \+ *lemma* ae_measurable_const_smul_iff'
- \+ *lemma* ae_measurable_const_smul_iff
- \+ *lemma* ae_measurable_inv_iff'
- \+ *lemma* ae_measurable_inv_iff
- \+ *lemma* finset.ae_measurable_prod'
- \+ *lemma* finset.ae_measurable_prod
- \+ *lemma* finset.measurable_prod'
- \+ *lemma* finset.measurable_prod
- \+ *lemma* is_unit.ae_measurable_const_smul_iff
- \+ *lemma* is_unit.measurable_const_smul_iff
- \+ *lemma* list.ae_measurable_prod'
- \+ *lemma* list.ae_measurable_prod
- \+ *lemma* list.measurable_prod'
- \+ *lemma* list.measurable_prod
- \+ *lemma* measurable.const_div
- \+ *lemma* measurable.const_mul
- \+ *lemma* measurable.const_pow
- \+ *lemma* measurable.const_smul'
- \+ *lemma* measurable.const_smul
- \+ *lemma* measurable.div
- \+ *lemma* measurable.div_const
- \+ *lemma* measurable.inv
- \+ *lemma* measurable.mul
- \+ *lemma* measurable.mul_const
- \+ *lemma* measurable.pow
- \+ *lemma* measurable.pow_const
- \+ *lemma* measurable.smul
- \+ *lemma* measurable.smul_const
- \+ *lemma* measurable_const_smul_iff'
- \+ *lemma* measurable_const_smul_iff
- \+ *lemma* measurable_inv_iff'
- \+ *lemma* measurable_inv_iff
- \+ *lemma* multiset.ae_measurable_prod'
- \+ *lemma* multiset.ae_measurable_prod
- \+ *lemma* multiset.measurable_prod'
- \+ *lemma* multiset.measurable_prod
- \+ *lemma* units.ae_measurable_const_smul_iff
- \+ *lemma* units.measurable_const_smul_iff

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.L1.simple_func.integral_smul
- \+/\- *lemma* measure_theory.integral_smul

Modified src/measure_theory/borel_space.lean
- \- *lemma* ae_measurable.const_smul
- \- *lemma* ae_measurable.ennreal_mul
- \- *lemma* ae_measurable.inv
- \- *lemma* ae_measurable.mul
- \- *lemma* ae_measurable.pow
- \- *lemma* ae_measurable.smul
- \- *lemma* ae_measurable.sub
- \- *lemma* ae_measurable_const_smul_iff
- \- *lemma* ennreal.measurable_div
- \- *lemma* ennreal.measurable_inv
- \- *lemma* ennreal.measurable_mul
- \- *lemma* ennreal.measurable_sub
- \- *lemma* finset.ae_measurable_prod
- \- *lemma* finset.measurable_prod
- \- *lemma* measurable.const_mul
- \- *lemma* measurable.const_smul
- \- *lemma* measurable.div
- \- *lemma* measurable.ennreal_div
- \- *lemma* measurable.ennreal_inv
- \- *lemma* measurable.ennreal_mul
- \- *lemma* measurable.ennreal_sub
- \- *lemma* measurable.inv'
- \- *lemma* measurable.inv
- \- *lemma* measurable.mul'
- \- *lemma* measurable.mul
- \- *lemma* measurable.mul_const
- \- *lemma* measurable.of_inv
- \- *lemma* measurable.pow
- \- *lemma* measurable.smul
- \- *lemma* measurable.sub
- \- *lemma* measurable.sub_const
- \- *lemma* measurable.sub_nnreal
- \- *lemma* measurable_const_smul_iff
- \- *lemma* measurable_inv'
- \- *lemma* measurable_inv
- \- *lemma* measurable_inv_iff
- \- *lemma* measurable_mul
- \- *lemma* measurable_mul_left
- \- *lemma* measurable_mul_right
- \- *lemma* measurable_pow

Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/group.lean


Modified src/measure_theory/haar_measure.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.lintegral_finset_sum

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integrable.smul

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/l2_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.mem_ℒp.const_smul

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_from_prod_encodable

Modified src/measure_theory/measure_space.lean
- \- *lemma* ae_measurable.null_measurable_set
- \- *lemma* ae_measurable_of_zero_measure
- \+ *lemma* ae_measurable_one
- \- *lemma* ae_measurable_zero
- \+ *lemma* ae_measurable_zero_measure

Modified src/measure_theory/prod.lean


Modified src/measure_theory/prod_group.lean


Modified src/probability_theory/integration.lean




## [2021-03-28 04:55:34](https://github.com/leanprover-community/mathlib/commit/dc34b21)
lint(*): split long lines ([#6918](https://github.com/leanprover-community/mathlib/pull/6918))
#### Estimated changes
Modified src/control/functor/multivariate.lean


Modified src/control/monad/writer.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/gcd.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean


Modified src/geometry/euclidean/circumcenter.lean
- \+/\- *lemma* affine.simplex.sum_centroid_weights_with_circumcenter

Modified src/geometry/manifold/charted_space.lean
- \+/\- *def* structomorph.trans

Modified src/geometry/manifold/local_invariant_properties.lean
- \+/\- *lemma* structure_groupoid.local_invariant_prop.lift_prop_on_mono

Modified src/meta/coinductive_predicates.lean


Modified src/meta/expr.lean


Modified src/order/bounded_lattice.lean


Modified src/order/filter/extr.lean
- \+/\- *lemma* is_extr_filter.comp_tendsto

Modified src/order/filter/lift.lean


Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.lift_lift

Modified src/tactic/chain.lean


Modified src/tactic/converter/binders.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/find_unused.lean


Modified src/tactic/finish.lean


Modified src/tactic/group.lean
- \+/\- *lemma* tactic.group.gpow_trick_sub

Modified src/tactic/linarith/frontend.lean


Modified src/tactic/linarith/lemmas.lean
- \+/\- *lemma* linarith.int.coe_nat_bit0_mul
- \+/\- *lemma* linarith.int.coe_nat_bit1_mul
- \+/\- *lemma* linarith.int.coe_nat_mul_bit0
- \+/\- *lemma* linarith.int.coe_nat_mul_bit1
- \+/\- *lemma* linarith.mul_zero_eq
- \+/\- *lemma* linarith.nat_eq_subst
- \+/\- *lemma* linarith.nat_le_subst
- \+/\- *lemma* linarith.nat_lt_subst
- \+/\- *lemma* linarith.zero_mul_eq

Modified src/tactic/norm_cast.lean


Modified src/tactic/nth_rewrite/default.lean


Modified src/tactic/omega/find_ees.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/ring.lean
- \+/\- *theorem* tactic.ring.pow_add_rev_right

Modified src/tactic/ring2.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/simp_result.lean


Modified src/tactic/simp_rw.lean


Modified src/topology/sheaves/presheaf_of_functions.lean


Modified src/topology/sheaves/sheaf_of_functions.lean


Modified test/group.lean


Modified test/lint.lean


Modified test/random.lean


Modified test/where.lean




## [2021-03-28 01:36:58](https://github.com/leanprover-community/mathlib/commit/e129117)
chore(scripts): update nolints.txt ([#6917](https://github.com/leanprover-community/mathlib/pull/6917))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-27 23:51:09](https://github.com/leanprover-community/mathlib/commit/879cb47)
feat(test/integration): add examples of computing integrals by simp ([#6859](https://github.com/leanprover-community/mathlib/pull/6859))
As suggested in [[#6216](https://github.com/leanprover-community/mathlib/pull/6216) (comment)](https://github.com/leanprover-community/mathlib/pull/6216#discussion_r580389848).
The examples added here were made possible by [#6216](https://github.com/leanprover-community/mathlib/pull/6216), [#6334](https://github.com/leanprover-community/mathlib/pull/6334), [#6357](https://github.com/leanprover-community/mathlib/pull/6357), [#6597](https://github.com/leanprover-community/mathlib/pull/6597).
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean


Added test/integration.lean




## [2021-03-27 21:49:34](https://github.com/leanprover-community/mathlib/commit/06b21d0)
chore(category_theory/monads): remove empty file ([#6915](https://github.com/leanprover-community/mathlib/pull/6915))
In [#5889](https://github.com/leanprover-community/mathlib/pull/5889) I moved the contents of this file into monad/basic but I forgot to delete this file.
#### Estimated changes
Deleted src/category_theory/monad/bundled.lean


Modified src/category_theory/monad/equiv_mon.lean




## [2021-03-27 18:47:28](https://github.com/leanprover-community/mathlib/commit/27c8676)
refactor(geometry/manifold/algebra/smooth_functions): make `smooth_map_group` division defeq to `pi.has_div` ([#6912](https://github.com/leanprover-community/mathlib/pull/6912))
The motivation was the fact that this allows `smooth_map.coe_div` to be `rfl` but this should be more generally useful.
#### Estimated changes
Modified src/geometry/manifold/algebra/lie_group.lean
- \+ *lemma* smooth.div
- \+ *lemma* smooth_on.div

Modified src/geometry/manifold/algebra/smooth_functions.lean




## [2021-03-27 15:21:25](https://github.com/leanprover-community/mathlib/commit/d104413)
chore(topology/metric_space): golf, generalize, rename ([#6849](https://github.com/leanprover-community/mathlib/pull/6849))
### Second countable topology
* generalize `metric.second_countable_of_almost_dense_set` to a pseudo
  emetric space, see
  `emetric.subset_countable_closure_of_almost_dense_set` (for sets)
  and `emetric.second_countable_of_almost_dense_set` (for the whole space);
* use it to generalize `emetric.countable_closure_of_compact` to a
  pseudo emetric space (replacing `closure t = s` with
  `s ⊆ closure t`) and prove that a sigma compact pseudo emetric space has
  second countable topology;
* generalize `second_countable_of_proper` to a pseudo metric space;
### `emetric.diam`
* rename `emetric.diam_le_iff_forall_edist_le` to `emetric.diam_le_iff`;
* rename `emetric.diam_le_of_forall_edist_le` to `emetric.diam_le`.
#### Estimated changes
Modified src/analysis/convex/topology.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.bounded_closure_iff

Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* emetric.countable_closure_of_compact
- \+ *lemma* emetric.diam_image_le_iff
- \+ *lemma* emetric.diam_le
- \+ *lemma* emetric.diam_le_iff
- \- *lemma* emetric.diam_le_iff_forall_edist_le
- \- *lemma* emetric.diam_le_of_forall_edist_le
- \+ *lemma* emetric.edist_le_of_diam_le
- \+ *lemma* emetric.second_countable_of_almost_dense_set
- \+/\- *lemma* emetric.second_countable_of_separable
- \+ *lemma* emetric.second_countable_of_sigma_compact
- \+ *lemma* emetric.subset_countable_closure_of_almost_dense_set
- \+ *lemma* emetric.subset_countable_closure_of_compact

Modified src/topology/metric_space/isometry.lean


Modified src/topology/metric_space/lipschitz.lean




## [2021-03-27 06:35:11](https://github.com/leanprover-community/mathlib/commit/cc7e722)
refactor(representation_theory/maschke): replaces `¬(ring_char k ∣ fintype.card G)` with `invertible (fintype.card G : k)` instance ([#6901](https://github.com/leanprover-community/mathlib/pull/6901))
Refactors Maschke's theorem to take an instance of `invertible (fintype.card G : k)` instead of an explicit `not_dvd : ¬(ring_char k ∣ fintype.card G)`.
Provides that instance in the context `char_zero k`.
Allows `monoid_algebra.submodule.is_complemented` to be an instance.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* ring_char.eq_zero

Modified src/algebra/char_p/invertible.lean
- \+ *lemma* ring_char_not_dvd_of_invertible

Modified src/representation_theory/maschke.lean
- \- *theorem* monoid_algebra.is_semisimple_module
- \- *theorem* monoid_algebra.submodule.is_complemented



## [2021-03-27 06:35:10](https://github.com/leanprover-community/mathlib/commit/d32f9c7)
feat(data/nat/log): add some lemmas and monotonicity ([#6899](https://github.com/leanprover-community/mathlib/pull/6899))
#### Estimated changes
Modified src/data/nat/log.lean
- \+ *lemma* nat.log_b_one_eq_zero
- \+ *lemma* nat.log_b_zero_eq_zero
- \+ *lemma* nat.log_eq_zero
- \+ *lemma* nat.log_eq_zero_of_le
- \+ *lemma* nat.log_eq_zero_of_lt
- \+ *lemma* nat.log_le_log_of_le
- \+ *lemma* nat.log_le_log_succ
- \+ *lemma* nat.log_mono
- \+ *lemma* nat.log_one_eq_zero
- \+ *lemma* nat.log_zero_eq_zero



## [2021-03-27 06:35:09](https://github.com/leanprover-community/mathlib/commit/5ecb1f7)
feat(group_theory/order_of_element): order_of is the same in a submonoid ([#6876](https://github.com/leanprover-community/mathlib/pull/6876))
The first lemma shows that `order_of` is the same in a submonoid, but it seems like you also need a lemma for subgroups.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_order_of_iff
- \+ *lemma* order_of_injective
- \+ *lemma* order_of_subgroup
- \+ *lemma* order_of_submonoid



## [2021-03-27 03:05:14](https://github.com/leanprover-community/mathlib/commit/5c95d48)
chore(scripts): update nolints.txt ([#6902](https://github.com/leanprover-community/mathlib/pull/6902))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-03-27 03:05:12](https://github.com/leanprover-community/mathlib/commit/3fe67c8)
feat(algebra/module): pull-back module structures along homomorphisms ([#6895](https://github.com/leanprover-community/mathlib/pull/6895))
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/module/basic.lean
- \+ *def* ring_hom.comp_semimodule

Modified src/group_theory/group_action/basic.lean


Modified src/group_theory/group_action/defs.lean
- \+ *def* monoid_hom.comp_distrib_mul_action
- \+ *def* monoid_hom.comp_mul_action



## [2021-03-27 03:05:11](https://github.com/leanprover-community/mathlib/commit/4b261a8)
chore(algebra/smul_with_zero): add missing injective / surjective transferring functions ([#6892](https://github.com/leanprover-community/mathlib/pull/6892))
#### Estimated changes
Modified src/algebra/smul_with_zero.lean
- \+ *lemma* smul_zero'
- \+/\- *lemma* zero_smul



## [2021-03-27 03:05:10](https://github.com/leanprover-community/mathlib/commit/832a2eb)
refactor(topology/continuous_functions): change file layout ([#6890](https://github.com/leanprover-community/mathlib/pull/6890))
Moves `topology/bounded_continuous_function.lean` to `topology/continuous_functions/bounded.lean`, splitting out the content about continuous functions on a compact space to `topology/continuous_functions/compact.lean`.
Renames `topology/continuous_map.lean` to `topology/continuous_functions/basic.lean`.
Renames `topology/algebra/continuous_functions.lean` to `topology/continuous_functions/algebra.lean`.
Also changes the direction of the equivalences, replacing `bounded_continuous_function.equiv_continuous_map_of_compact` with `continuous_map.equiv_bounded_of_compact` (and also the more structured version).
There's definitely more work to be done here, particularly giving at least some lemmas characterising the norm on `C(α, β)`, but I wanted to do a minimal PR changing the layout first.
#### Estimated changes
Modified src/geometry/manifold/times_cont_mdiff_map.lean


Modified src/topology/algebra/affine.lean


Modified src/topology/category/Top/basic.lean


Modified src/topology/compact_open.lean


Renamed src/topology/algebra/continuous_functions.lean to src/topology/continuous_function/algebra.lean


Renamed src/topology/continuous_map.lean to src/topology/continuous_function/basic.lean


Renamed src/topology/bounded_continuous_function.lean to src/topology/continuous_function/bounded.lean
- \- *def* bounded_continuous_function.add_equiv_continuous_map_of_compact
- \- *lemma* bounded_continuous_function.add_equiv_continuous_map_of_compact_to_equiv
- \- *def* bounded_continuous_function.equiv_continuous_map_of_compact
- \- *def* bounded_continuous_function.isometric_continuous_map_of_compact
- \- *lemma* bounded_continuous_function.isometric_continuous_map_of_compact_to_isometric
- \- *def* bounded_continuous_function.linear_isometry_continuous_map_of_compact
- \- *lemma* bounded_continuous_function.linear_isometry_continuous_map_of_compact_to_add_equiv
- \- *lemma* bounded_continuous_function.linear_isometry_continuous_map_of_compact_to_equiv

Added src/topology/continuous_function/compact.lean
- \+ *def* continuous_map.add_equiv_bounded_of_compact
- \+ *lemma* continuous_map.add_equiv_bounded_of_compact_apply_apply
- \+ *lemma* continuous_map.add_equiv_bounded_of_compact_to_equiv
- \+ *def* continuous_map.equiv_bounded_of_compact
- \+ *def* continuous_map.isometric_bounded_of_compact
- \+ *def* continuous_map.linear_isometry_bounded_of_compact
- \+ *lemma* continuous_map.linear_isometry_bounded_of_compact_of_compact_to_equiv
- \+ *lemma* continuous_map.linear_isometry_bounded_of_compact_to_add_equiv
- \+ *lemma* continuous_map.linear_isometry_bounded_of_compact_to_isometric

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/kuratowski.lean


Modified src/topology/sheaves/presheaf_of_functions.lean




## [2021-03-27 03:05:09](https://github.com/leanprover-community/mathlib/commit/99c23ea)
refactor(analysis/normed_space/basic): add semi_normed_group ([#6888](https://github.com/leanprover-community/mathlib/pull/6888))
This is part of a series of PR to have semi_normed_group (and related concepts) in mathlib.
 
To keep the PR as small as possibile I just added the new class `semi_normed_group`. I didn't introduce anything like `semi_normed_ring` and I didn't do anything about morphisms.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* has_fderiv_at_fst
- \+/\- *lemma* has_fderiv_at_snd
- \+/\- *lemma* has_strict_fderiv_at_fst
- \+/\- *lemma* has_strict_fderiv_at_snd

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* antilipschitz_with.add_lipschitz_with
- \+/\- *lemma* coe_norm_subgroup
- \+/\- *lemma* lipschitz_with.add
- \+/\- *lemma* lipschitz_with.neg
- \+/\- *lemma* lipschitz_with.sub
- \+ *lemma* ne_zero_of_norm_pos
- \+/\- *lemma* norm_zero
- \+ *lemma* normed_group.core.to_semi_normed_group.core
- \- *def* normed_group.of_add_dist'
- \+ *lemma* pi_nnsemi_norm_const
- \+ *lemma* pi_semi_norm_const
- \+ *lemma* pi_semi_norm_le_iff
- \+ *lemma* pi_semi_norm_lt_iff
- \+ *lemma* prod.nnsemi_norm_def
- \+ *lemma* prod.semi_norm_def
- \- *lemma* real.fpow_bit0_norm
- \- *lemma* real.fpow_even_norm
- \- *lemma* real.pow_bit0_norm
- \- *lemma* real.pow_even_norm
- \+ *lemma* semi_norm_fst_le
- \+ *lemma* semi_norm_le_pi_norm
- \+ *lemma* semi_norm_prod_le_iff
- \+ *lemma* semi_norm_snd_le
- \+ *structure* semi_normed_group.core
- \+ *def* semi_normed_group.of_add_dist'
- \+ *def* semi_normed_group.of_add_dist

Modified src/analysis/normed_space/operator_norm.lean


Modified src/geometry/euclidean/basic.lean


Modified src/measure_theory/prod.lean




## [2021-03-27 03:05:08](https://github.com/leanprover-community/mathlib/commit/bc33f1a)
feat(group_theory/perm/cycles): is_cycle_of_is_cycle_pow ([#6871](https://github.com/leanprover-community/mathlib/pull/6871))
If `g ^ n` is a cycle, and if `g ^ n` doesn't have smaller support, then `g` is a cycle.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.is_cycle_of_is_cycle_pow



## [2021-03-27 03:05:07](https://github.com/leanprover-community/mathlib/commit/5eead09)
feat(algebra/big_operators/basic): add lemmas for a product with two non one factors ([#6826](https://github.com/leanprover-community/mathlib/pull/6826))
Add another version of `prod_eq_one` and 3 versions of `prod_eq_double`, a lemma that says a product with only 2 non one factors is equal to the product of the 2 factors.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_eq_mul
- \+ *lemma* finset.prod_eq_mul_of_mem
- \+ *lemma* finset.prod_eq_single_of_mem

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.prod_eq_mul



## [2021-03-27 03:05:06](https://github.com/leanprover-community/mathlib/commit/cfd1a4c)
feat(linear_algebra/bilinear_form): generalize some constructions to the noncomm case ([#6824](https://github.com/leanprover-community/mathlib/pull/6824))
Introduce an operation `flip` on a bilinear form, which swaps the arguments.  Generalize the construction `bilin_form.to_lin` (which currently exists for commutative rings) to a weaker construction `bilin_form.to_lin'` for arbitrary rings.
Rename lemmas
`sesq_form.map_sum_right` -> `sesq_form.sum_right`
`sesq_form.map_sum_left` -> `sesq_form.sum_left`
`bilin_form.map_sum_right` -> `bilin_form.sum_right`
`bilin_form.map_sum_left` -> `bilin_form.sum_left`
`to_linear_map_apply` (sic, no namespace) -> `bilin_form.to_lin_apply`
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/linear_algebra/bilinear_form.lean
- \+ *abbreviation* bilin_form.flip'
- \+ *abbreviation* bilin_form.flip
- \+ *lemma* bilin_form.flip_apply
- \+ *lemma* bilin_form.flip_flip
- \+ *lemma* bilin_form.flip_flip_aux
- \+ *def* bilin_form.flip_hom
- \+ *def* bilin_form.flip_hom_aux
- \+/\- *lemma* bilin_form.smul_apply
- \+ *lemma* bilin_form.sum_left
- \+ *lemma* bilin_form.sum_right
- \+ *abbreviation* bilin_form.to_lin'
- \+ *lemma* bilin_form.to_lin'_apply
- \+ *abbreviation* bilin_form.to_lin'_flip
- \+ *lemma* bilin_form.to_lin'_flip_apply
- \+ *lemma* bilin_form.to_lin_apply
- \+ *def* bilin_form.to_lin_hom
- \+ *def* bilin_form.to_lin_hom_flip
- \+/\- *structure* bilin_form
- \- *lemma* map_sum_left
- \- *lemma* map_sum_right
- \+ *lemma* sym_bilin_form.is_sym_iff_flip'
- \- *lemma* to_linear_map_apply

Modified src/linear_algebra/sesquilinear_form.lean
- \- *lemma* sesq_form.map_sum_left
- \- *lemma* sesq_form.map_sum_right
- \+ *lemma* sesq_form.sum_left
- \+ *lemma* sesq_form.sum_right

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* linear_map.map_sum₂



## [2021-03-27 03:05:05](https://github.com/leanprover-community/mathlib/commit/ec26d96)
feat(order/lattice): add complete_semilattice_Sup/Inf ([#6797](https://github.com/leanprover-community/mathlib/pull/6797))
This adds `complete_semilattice_Sup` and `complete_semilattice_Inf` above `complete_lattice`.
This has not much effect, as in fact either implies `complete_lattice`. However it's useful at times to have these, when you can naturally define just one half of the structure at a time (e.g. the subobject lattice in a general category, where for `Sup` we need coproducts and images, while for the `Inf` we need wide pullbacks).
There are many places in mathlib that currently use `complete_lattice_of_Inf`. It might be slightly nicer to instead construct a `complete_semilattice_Inf`, and then use the new `complete_lattice_of_complete_semilattice_Inf`, but I haven't done that here.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.supr_zero_eq_zero

Modified src/measure_theory/measure_space.lean


Modified src/order/complete_lattice.lean
- \+/\- *theorem* Inf_le
- \+/\- *theorem* Sup_le
- \+ *def* complete_lattice_of_complete_semilattice_Inf
- \+ *def* complete_lattice_of_complete_semilattice_Sup
- \+/\- *theorem* le_Inf
- \+/\- *theorem* le_Sup

Modified src/topology/instances/ennreal.lean


Modified src/topology/omega_complete_partial_order.lean




## [2021-03-26 23:52:29](https://github.com/leanprover-community/mathlib/commit/e36656e)
chore(category_theory/monoidal): golf some proofs ([#6894](https://github.com/leanprover-community/mathlib/pull/6894))
Golfs proofs of `tensor_left_iff`, `tensor_right_iff`, `left_unitor_tensor'`, `right_unitor_tensor` and `unitors_equal` - in particular removes the file `monoidal/unitors` as all it contained was a proof of `unitors_equal` which is a two line proof.
#### Estimated changes
Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* category_theory.monoidal_category.comp_tensor_id
- \+/\- *lemma* category_theory.monoidal_category.id_tensor_comp
- \- *lemma* category_theory.monoidal_category.left_unitor_product_aux
- \- *lemma* category_theory.monoidal_category.left_unitor_product_aux_perimeter
- \- *lemma* category_theory.monoidal_category.left_unitor_product_aux_square
- \- *lemma* category_theory.monoidal_category.left_unitor_product_aux_triangle
- \- *lemma* category_theory.monoidal_category.right_unitor_product_aux
- \- *lemma* category_theory.monoidal_category.right_unitor_product_aux_perimeter
- \- *lemma* category_theory.monoidal_category.right_unitor_product_aux_square
- \- *lemma* category_theory.monoidal_category.right_unitor_product_aux_triangle
- \+ *lemma* category_theory.monoidal_category.unitors_equal

Deleted src/category_theory/monoidal/unitors.lean
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_10_13
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_14
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_15
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_1_2
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_1_4
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_1_7
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_3_4
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_4'
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_4
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_5_6
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_6'
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_6
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_7
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_8
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_9
- \- *lemma* category_theory.monoidal_category.unitors_equal.cells_9_13
- \- *lemma* category_theory.monoidal_category.unitors_equal



## [2021-03-26 23:52:28](https://github.com/leanprover-community/mathlib/commit/e21b4bc)
chore(data/equiv/transfer_instance): reuse existing proofs ([#6868](https://github.com/leanprover-community/mathlib/pull/6868))
This makes all the proofs in this file identical. It's unfortunate that the `letI`s have to be written out in each case,
#### Estimated changes
Modified src/data/equiv/transfer_instance.lean




## [2021-03-26 23:52:27](https://github.com/leanprover-community/mathlib/commit/9e00c2b)
feat(ring_theory/int/basic): Induction, nat_abs and units ([#6733](https://github.com/leanprover-community/mathlib/pull/6733))
Proves : 
 * Induction on primes (special case for nat)
 * In `int`, a number and its `nat_abs` are associated
 * An integer is prime iff its `nat_abs` is prime
 * Two integers are associated iff they are equal or opposites
 * Classification of the units in `int` (trivial but handy lemma)
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_eq_nat_abs_iff

Modified src/ring_theory/int/basic.lean
- \+ *lemma* induction_on_primes
- \+ *lemma* int.associated_iff
- \+ *theorem* int.associated_iff_nat_abs
- \+ *lemma* int.associated_nat_abs
- \+ *lemma* int.prime_iff_nat_abs_prime



## [2021-03-26 22:21:04](https://github.com/leanprover-community/mathlib/commit/ca7dca3)
feat(geometry/manifold/algebra/smooth_functions): simp lemmas for coercions to functions ([#6893](https://github.com/leanprover-community/mathlib/pull/6893))
These came up while working on the branch `replace_algebra_def` but seem worth adding
in their own right.
#### Estimated changes
Modified src/geometry/manifold/algebra/smooth_functions.lean
- \+ *lemma* smooth_map.coe_div
- \+ *lemma* smooth_map.coe_inv
- \+ *lemma* smooth_map.coe_mul
- \+ *lemma* smooth_map.coe_one
- \+ *lemma* smooth_map.coe_smul



## [2021-03-26 18:26:23](https://github.com/leanprover-community/mathlib/commit/902b01d)
chore(algebra/group): rename `is_unit_unit` to `units.is_unit` ([#6886](https://github.com/leanprover-community/mathlib/pull/6886))
#### Estimated changes
Modified src/algebra/group/units.lean
- \- *lemma* is_unit_unit

Modified src/algebra/group/units_hom.lean


Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* is_unit.mk0

Modified src/algebra/ring/basic.lean


Modified src/analysis/normed_space/units.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/padics/padic_integers.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series/basic.lean




## [2021-03-26 18:26:22](https://github.com/leanprover-community/mathlib/commit/e43d964)
chore(data/pi,algebra/group/pi): reorganize proofs ([#6869](https://github.com/leanprover-community/mathlib/pull/6869))
Add `pi.single_op` and `pi.single_binop` and use them in the proofs.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *def* mul_hom.single
- \+/\- *lemma* pi.single_mul
- \- *lemma* pi.single_zero

Modified src/algebra/module/pi.lean


Modified src/data/pi.lean
- \+ *lemma* pi.mul_def
- \+/\- *lemma* pi.single_eq_of_ne
- \+/\- *lemma* pi.single_eq_same
- \+ *lemma* pi.single_op
- \+ *lemma* pi.single_op₂
- \+ *lemma* pi.single_zero



## [2021-03-26 18:26:20](https://github.com/leanprover-community/mathlib/commit/3566cbb)
feat(*): add more lemmas about `set.piecewise` ([#6862](https://github.com/leanprover-community/mathlib/pull/6862))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.piecewise_div
- \+ *lemma* pi.piecewise_inv
- \+ *lemma* set.piecewise_mul

Modified src/data/indicator_function.lean


Modified src/data/set/function.lean
- \+ *lemma* set.apply_piecewise
- \+ *lemma* set.apply_piecewise₂
- \- *lemma* set.comp_piecewise
- \+ *lemma* set.le_piecewise
- \+ *lemma* set.piecewise_le
- \+ *lemma* set.piecewise_le_piecewise
- \+ *lemma* set.piecewise_op
- \+ *lemma* set.piecewise_op₂

Modified src/data/set/intervals/pi.lean
- \+ *lemma* set.piecewise_mem_Icc'
- \+ *lemma* set.piecewise_mem_Icc



## [2021-03-26 18:26:19](https://github.com/leanprover-community/mathlib/commit/ef7fe6f)
feat(dynamics/ergodic/conservative): define conservative systems, formalize Poincaré recurrence thm ([#2311](https://github.com/leanprover-community/mathlib/pull/2311))
#### Estimated changes
Modified src/combinatorics/pigeonhole.lean
- \+ *theorem* nat.exists_lt_modeq_of_infinite

Modified src/data/set/finite.lean
- \+ *theorem* set.infinite.exists_lt_map_eq_of_maps_to
- \+ *theorem* set.infinite.exists_ne_map_eq_of_maps_to

Added src/dynamics/ergodic/conservative.lean
- \+ *lemma* measure_theory.conservative.ae_forall_image_mem_imp_frequently_image_mem
- \+ *lemma* measure_theory.conservative.ae_frequently_mem_of_mem_nhds
- \+ *lemma* measure_theory.conservative.ae_mem_imp_frequently_image_mem
- \+ *lemma* measure_theory.conservative.exists_gt_measure_inter_ne_zero
- \+ *lemma* measure_theory.conservative.frequently_ae_mem_and_frequently_image_mem
- \+ *lemma* measure_theory.conservative.frequently_measure_inter_ne_zero
- \+ *lemma* measure_theory.conservative.inter_frequently_image_mem_ae_eq
- \+ *lemma* measure_theory.conservative.measure_inter_frequently_image_mem_eq
- \+ *lemma* measure_theory.conservative.measure_mem_forall_ge_image_not_mem_eq_zero
- \+ *structure* measure_theory.conservative

Modified src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.exists_mem_image_mem
- \+ *lemma* measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.frequently_ae_iff
- \+ *lemma* measure_theory.frequently_ae_mem_iff
- \+ *lemma* measure_theory.measure_bUnion_null_iff
- \+ *lemma* measure_theory.measure_diff_null'
- \+ *lemma* measure_theory.measure_diff_null

Modified src/order/filter/basic.lean
- \+ *lemma* filter.inter_eventually_eq_left
- \+ *lemma* filter.inter_eventually_eq_right

Modified src/order/filter/cofinite.lean




## [2021-03-26 14:24:21](https://github.com/leanprover-community/mathlib/commit/f0bfb25)
feat(geometry/manifold/mfderiv): differentiability of `f : E ≃L[𝕜] E'` ([#6850](https://github.com/leanprover-community/mathlib/pull/6850))
#### Estimated changes
Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* continuous_linear_equiv.mfderiv_eq
- \+ *lemma* continuous_linear_equiv.mfderiv_within_eq



## [2021-03-26 14:24:20](https://github.com/leanprover-community/mathlib/commit/2b71c80)
feat(linear_algebra/dual): add the dual map ([#6807](https://github.com/leanprover-community/mathlib/pull/6807))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+ *def* linear_equiv.dual_map
- \+ *lemma* linear_equiv.dual_map_apply
- \+ *lemma* linear_equiv.dual_map_refl
- \+ *lemma* linear_equiv.dual_map_symm
- \+ *lemma* linear_equiv.dual_map_trans
- \+ *def* linear_map.dual_map
- \+ *lemma* linear_map.dual_map_apply
- \+ *lemma* linear_map.dual_map_comp_dual_map
- \+ *lemma* linear_map.dual_map_id
- \+ *lemma* linear_map.findim_range_dual_map_eq_findim_range
- \+ *lemma* linear_map.ker_dual_map_eq_dual_annihilator_range
- \+ *lemma* linear_map.range_dual_map_eq_dual_annihilator_ker
- \+ *lemma* linear_map.range_dual_map_le_dual_annihilator_ker



## [2021-03-26 14:24:19](https://github.com/leanprover-community/mathlib/commit/8addf9a)
feat(topology/bcf): better dist_lt_of_* lemmas ([#6781](https://github.com/leanprover-community/mathlib/pull/6781))
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+ *lemma* bounded_continuous_function.dist_le_of_nonempty
- \+ *lemma* bounded_continuous_function.dist_lt_iff_of_compact
- \+ *lemma* bounded_continuous_function.dist_lt_iff_of_nonempty_compact
- \+ *lemma* bounded_continuous_function.dist_lt_of_nonempty_compact
- \+ *lemma* bounded_continuous_function.norm_lt_iff_of_compact
- \+ *lemma* bounded_continuous_function.norm_lt_iff_of_nonempty_compact
- \- *lemma* bounded_continuous_function.norm_lt_of_compact



## [2021-03-26 14:24:17](https://github.com/leanprover-community/mathlib/commit/6ae9f00)
feat(ring_theory/polynomial/symmetric): degrees_esymm ([#6718](https://github.com/leanprover-community/mathlib/pull/6718))
A lot of API also added for finset, finsupp, multiset, powerset_len
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.sum_multiset_singleton

Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.sup_finset_image

Modified src/data/finset/powerset.lean
- \+ *lemma* finset.powerset_len_nonempty
- \+ *lemma* finset.powerset_len_self
- \+ *lemma* finset.powerset_len_succ_insert
- \+ *lemma* finset.powerset_len_sup

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.single_eq_pi_single
- \+ *lemma* finsupp.support_single_disjoint
- \+ *lemma* finsupp.support_single_ne_bot
- \+ *lemma* finsupp.support_sum_eq_bUnion
- \+ *lemma* finsupp.to_multiset_sum
- \+ *lemma* finsupp.to_multiset_sum_single

Modified src/data/fintype/basic.lean
- \+ *lemma* multiset.count_univ

Modified src/data/multiset/lattice.lean
- \+ *lemma* multiset.nodup_sup_iff

Modified src/data/set/basic.lean
- \+ *lemma* set.pairwise_on_empty
- \+ *lemma* set.pairwise_on_insert_of_symmetric

Modified src/data/support.lean
- \+ *lemma* pi.support_single_disjoint

Modified src/order/compactly_generated.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/symmetric.lean
- \+ *lemma* mv_polynomial.degrees_esymm
- \+ *lemma* mv_polynomial.support_esymm''
- \+ *lemma* mv_polynomial.support_esymm'
- \+ *lemma* mv_polynomial.support_esymm



## [2021-03-26 11:55:37](https://github.com/leanprover-community/mathlib/commit/34a3317)
feat(group_theory/perm/sign): power has smaller support ([#6872](https://github.com/leanprover-community/mathlib/pull/6872))
The support of `g ^ n` is contained in the support of `g`.
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.support_pow_le



## [2021-03-26 11:55:36](https://github.com/leanprover-community/mathlib/commit/adc5f9d)
feat(ring_theory/ideal/operations): add an instance ([#6717](https://github.com/leanprover-community/mathlib/pull/6717))
This instance has been suggested by @eric-wieser in [#6640](https://github.com/leanprover-community/mathlib/pull/6640).
On my machine I get a deterministic timeout in `ring_theory/finiteness` at line 325, but in principle it seems a useful instance to have.
#### Estimated changes
Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/operations.lean




## [2021-03-26 08:06:47](https://github.com/leanprover-community/mathlib/commit/fb49529)
chore(topology/sheaves): speed up a slow proof ([#6879](https://github.com/leanprover-community/mathlib/pull/6879))
In another branch this proof mysteriously becomes slightly too slow, so I'm offering a pre-emptive speed up, just replacing `simp` with `rw`.
#### Estimated changes
Modified src/topology/sheaves/local_predicate.lean




## [2021-03-26 08:06:45](https://github.com/leanprover-community/mathlib/commit/c658f5c)
refactor(algebra/field): allow custom `div` ([#6874](https://github.com/leanprover-community/mathlib/pull/6874))
#### Estimated changes
Modified src/algebra/field.lean


Modified src/algebra/ordered_field.lean


Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/exponential.lean


Modified src/data/polynomial/denoms_clearable.lean


Modified src/data/real/cau_seq.lean
- \+ *theorem* cau_seq.const_zero

Modified src/data/real/cau_seq_completion.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/deprecated/subfield.lean
- \+ *lemma* is_subfield.div_mem

Modified src/measure_theory/borel_space.lean


Modified src/order/filter/at_top_bot.lean


Modified src/ring_theory/ideal/basic.lean




## [2021-03-26 08:06:44](https://github.com/leanprover-community/mathlib/commit/c07c310)
feat(group_theory/perm_basic): Lemma swap_apply_apply ([#6870](https://github.com/leanprover-community/mathlib/pull/6870))
A useful rw lemma.
#### Estimated changes
Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.swap_apply_apply



## [2021-03-26 08:06:42](https://github.com/leanprover-community/mathlib/commit/0977b20)
feat(measure_theory/interval_integral): weaken assumption in `integral_non_ae_measurable` ([#6858](https://github.com/leanprover-community/mathlib/pull/6858))
I don't see any reason for having a strict inequality here.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_non_ae_measurable_of_le



## [2021-03-26 08:06:41](https://github.com/leanprover-community/mathlib/commit/03f0bb1)
refactor(topology/algebra): define `has_continuous_smul`, use for topological semirings and algebras ([#6823](https://github.com/leanprover-community/mathlib/pull/6823))
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.algebra_map_eq_smul_one'

Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/normed_space/basic.lean
- \- *lemma* normed_algebra.algebra_map_continuous

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/seminorm.lean


Modified src/data/equiv/mul_add.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/affine.lean
- \+/\- *lemma* affine_map.line_map_continuous

Modified src/topology/algebra/algebra.lean
- \+ *lemma* continuous_algebra_map
- \+ *lemma* continuous_algebra_map_iff_smul
- \+ *lemma* has_continuous_smul_of_algebra_map

Modified src/topology/algebra/continuous_functions.lean
- \+/\- *lemma* continuous_map.smul_apply

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean
- \- *lemma* continuous.smul
- \+/\- *lemma* continuous_linear_map.smul_right_comp
- \+/\- *lemma* continuous_linear_map.smul_right_one_pow
- \- *lemma* continuous_on.smul
- \- *lemma* continuous_smul
- \- *lemma* filter.tendsto.smul
- \- *lemma* is_closed_map_smul_of_ne_zero
- \- *lemma* is_closed_map_smul_of_unit
- \- *lemma* is_open_map_smul_of_ne_zero
- \- *lemma* is_open_map_smul_of_unit
- \- *lemma* tendsto_smul
- \- *abbreviation* topological_module
- \- *abbreviation* topological_vector_space

Added src/topology/algebra/mul_action.lean
- \+ *lemma* continuous.const_smul
- \+ *lemma* continuous.smul
- \+ *lemma* continuous_at.const_smul
- \+ *lemma* continuous_at.smul
- \+ *lemma* continuous_at_const_smul_iff'
- \+ *lemma* continuous_at_const_smul_iff
- \+ *lemma* continuous_const_smul_iff'
- \+ *lemma* continuous_const_smul_iff
- \+ *lemma* continuous_on.const_smul
- \+ *lemma* continuous_on.smul
- \+ *lemma* continuous_on_const_smul_iff'
- \+ *lemma* continuous_on_const_smul_iff
- \+ *lemma* continuous_within_at.const_smul
- \+ *lemma* continuous_within_at.smul
- \+ *lemma* continuous_within_at_const_smul_iff'
- \+ *lemma* continuous_within_at_const_smul_iff
- \+ *lemma* filter.tendsto.const_smul
- \+ *lemma* filter.tendsto.smul
- \+ *lemma* is_closed_map_smul'
- \+ *lemma* is_closed_map_smul
- \+ *lemma* is_open_map_smul'
- \+ *lemma* is_open_map_smul
- \+ *lemma* is_unit.continuous_at_const_smul_iff
- \+ *lemma* is_unit.continuous_const_smul_iff
- \+ *lemma* is_unit.continuous_on_const_smul_iff
- \+ *lemma* is_unit.continuous_within_at_const_smul_iff
- \+ *lemma* is_unit.is_closed_map_smul
- \+ *lemma* is_unit.is_open_map_smul
- \+ *lemma* is_unit.tendsto_const_smul_iff
- \+ *lemma* tendsto_const_smul_iff'
- \+ *lemma* tendsto_const_smul_iff
- \+ *lemma* units.tendsto_const_smul_iff

Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/real.lean


Modified src/topology/instances/real_vector_space.lean


Modified src/topology/maps.lean
- \+ *lemma* is_open_map.image_interior_subset



## [2021-03-26 08:06:39](https://github.com/leanprover-community/mathlib/commit/5c93c2d)
feat(category_theory/triangulated/rotate): add definition of rotation and inverse rotation of triangles and their morphisms ([#6803](https://github.com/leanprover-community/mathlib/pull/6803))
This PR adds the definition of rotation and inverse rotation of triangles and triangle morphisms.
It also shows that rotation is an equivalence on the category of triangles in an additive category.
#### Estimated changes
Modified src/category_theory/triangulated/basic.lean
- \+ *def* category_theory.triangulated.contractible_triangle

Added src/category_theory/triangulated/rotate.lean
- \+ *def* category_theory.triangulated.inv_rot_comp_rot
- \+ *def* category_theory.triangulated.inv_rot_comp_rot_hom
- \+ *def* category_theory.triangulated.inv_rot_comp_rot_inv
- \+ *def* category_theory.triangulated.inv_rotate
- \+ *def* category_theory.triangulated.rot_comp_inv_rot
- \+ *def* category_theory.triangulated.rot_comp_inv_rot_hom
- \+ *def* category_theory.triangulated.rot_comp_inv_rot_inv
- \+ *def* category_theory.triangulated.rotate
- \+ *def* category_theory.triangulated.triangle.inv_rotate
- \+ *def* category_theory.triangulated.triangle.rotate
- \+ *def* category_theory.triangulated.triangle_morphism.inv_rotate
- \+ *def* category_theory.triangulated.triangle_morphism.rotate
- \+ *def* category_theory.triangulated.triangle_rotation



## [2021-03-26 08:06:38](https://github.com/leanprover-community/mathlib/commit/5c856c3)
feat(topology/vector_bundle): definition of topological vector bundle ([#4658](https://github.com/leanprover-community/mathlib/pull/4658))
# Topological vector bundles
In this file we define topological vector bundles.
Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.
To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:
* `F` should be a topological vector space over a field `𝕜`;
* There should be a topology on `bundle.total_space E`, for which the projection to `E` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `𝕜`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.
If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle 𝕜 F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.
The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `𝕜`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[𝕜] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[𝕜] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[𝕜] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.
Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.
Coauthored-by: Sebastien Gouezel  <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Modified src/linear_algebra/dual.lean


Modified src/topology/order.lean
- \+ *lemma* induced_const

Modified src/topology/topological_fiber_bundle.lean
- \+ *def* bundle.proj
- \+ *lemma* bundle.to_total_space_coe
- \+ *def* bundle.total_space
- \+ *def* bundle.trivial.proj_snd
- \+ *def* bundle.trivial
- \+/\- *def* topological_fiber_bundle_core.local_triv_at
- \+/\- *def* topological_fiber_bundle_core.proj
- \+/\- *def* topological_fiber_bundle_core.total_space

Added src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.is_topological_vector_bundle_is_topological_fiber_bundle
- \+ *lemma* topological_vector_bundle.mem_base_set_trivialization_at
- \+ *lemma* topological_vector_bundle.mem_source_trivialization_at
- \+ *def* topological_vector_bundle.trivial_bundle_trivialization
- \+ *def* topological_vector_bundle.trivialization.continuous_linear_equiv_at
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply'
- \+ *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply
- \+ *lemma* topological_vector_bundle.trivialization.mem_source
- \+ *structure* topological_vector_bundle.trivialization
- \+ *def* topological_vector_bundle.trivialization_at



## [2021-03-26 03:02:05](https://github.com/leanprover-community/mathlib/commit/b797d51)
chore(scripts): update nolints.txt ([#6885](https://github.com/leanprover-community/mathlib/pull/6885))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-25 21:40:33](https://github.com/leanprover-community/mathlib/commit/e6d01b8)
feat(topology/bounded_continuous_function): add `coe_mul`, `mul_apply` ([#6867](https://github.com/leanprover-community/mathlib/pull/6867))
Partners of the extant `coe_smul`, `smul_apply` lemmas (see line 630).
These came up while working on the `replace_algebra_def` branch but
seem worth adding independently.
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+/\- *lemma* bounded_continuous_function.coe_add
- \+ *lemma* bounded_continuous_function.coe_mul
- \+/\- *lemma* bounded_continuous_function.coe_neg
- \+/\- *lemma* bounded_continuous_function.coe_sub
- \+ *lemma* bounded_continuous_function.mul_apply



## [2021-03-25 21:40:32](https://github.com/leanprover-community/mathlib/commit/b670391)
chore(algebra/group/{pi,prod}): add missing instances ([#6866](https://github.com/leanprover-community/mathlib/pull/6866))
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/data/equiv/transfer_instance.lean




## [2021-03-25 21:40:31](https://github.com/leanprover-community/mathlib/commit/6e14e8f)
feat(data/equiv/mul_add): define `mul_hom.inverse` ([#6864](https://github.com/leanprover-community/mathlib/pull/6864))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *def* mul_hom.inverse



## [2021-03-25 19:35:08](https://github.com/leanprover-community/mathlib/commit/e054705)
refactor(topology/metric_space/antilipschitz): generalize to pseudo_metric_space ([#6841](https://github.com/leanprover-community/mathlib/pull/6841))
This is part of a series of PR to introduce semi_normed_group in mathlib.
We introduce here anti Lipschitz maps for `pseudo_emetric_space`.
#### Estimated changes
Modified src/topology/metric_space/antilipschitz.lean
- \+/\- *lemma* antilipschitz_with.closed_embedding
- \+/\- *lemma* antilipschitz_with.mul_le_dist
- \+/\- *lemma* antilipschitz_with.uniform_embedding
- \+ *lemma* antilipschitz_with.uniform_embedding_of_injective
- \+/\- *def* antilipschitz_with
- \+/\- *lemma* antilipschitz_with_iff_le_mul_dist
- \+/\- *lemma* lipschitz_with.to_right_inverse



## [2021-03-25 19:35:07](https://github.com/leanprover-community/mathlib/commit/b299d14)
feat(algebra/geom_sum): rename geom_series to geom_sum, adds a lemma for the geometric sum ([#6828](https://github.com/leanprover-community/mathlib/pull/6828))
Declarations with names including `geom_series` have been renamed to use `geom_sum`, instead.
Also adds the lemma `geom_sum₂_succ_eq`: `geom_sum₂ x y (n + 1) = x ^ n + y * (geom_sum₂ x y n)`
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \- *def* geom_series
- \- *theorem* geom_series_def
- \- *theorem* geom_series_one
- \- *theorem* geom_series_zero
- \- *def* geom_series₂
- \- *theorem* geom_series₂_def
- \- *theorem* geom_series₂_one
- \- *theorem* geom_series₂_self
- \- *theorem* geom_series₂_with_one
- \- *theorem* geom_series₂_zero
- \+ *def* geom_sum
- \- *theorem* geom_sum
- \+ *theorem* geom_sum_def
- \+ *theorem* geom_sum_eq
- \+ *theorem* geom_sum_one
- \+ *theorem* geom_sum_zero
- \+ *def* geom_sum₂
- \+ *theorem* geom_sum₂_def
- \+ *theorem* geom_sum₂_one
- \+ *theorem* geom_sum₂_self
- \+ *theorem* geom_sum₂_succ_eq
- \+ *theorem* geom_sum₂_with_one
- \+ *theorem* geom_sum₂_zero
- \- *lemma* op_geom_series
- \- *lemma* op_geom_series₂
- \+ *lemma* op_geom_sum
- \+ *lemma* op_geom_sum₂
- \- *theorem* ring_hom.map_geom_series
- \- *theorem* ring_hom.map_geom_series₂
- \+ *theorem* ring_hom.map_geom_sum
- \+ *theorem* ring_hom.map_geom_sum₂

Modified src/analysis/normed_space/units.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/colex.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/pi.lean


Modified src/number_theory/basic.lean


Modified src/number_theory/bernoulli.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/polynomial/cyclotomic.lean
- \- *lemma* polynomial.cyclotomic_eq_geom_series
- \+ *lemma* polynomial.cyclotomic_eq_geom_sum



## [2021-03-25 15:21:05](https://github.com/leanprover-community/mathlib/commit/1be91a1)
chore(order/filter/lift,topology/algebra/ordered): drop `[nonempty ι]` ([#6861](https://github.com/leanprover-community/mathlib/pull/6861))
* add `set.powerset_univ`, `filter.lift_top`, `filter.lift'_top`;
* remove `[nonempty ι]` from `filter.lift'_infi_powerset` and `tendsto_Icc_class_nhds_pi`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.powerset_univ

Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift'_infi_powerset
- \+ *lemma* filter.lift'_top
- \+ *lemma* filter.lift_top

Modified src/topology/algebra/ordered.lean




## [2021-03-25 10:59:25](https://github.com/leanprover-community/mathlib/commit/879273e)
feat(logic/basic, logic/function/basic): make `cast` the simp-normal form of `eq.mp` and `eq.mpr`, add lemmas ([#6834](https://github.com/leanprover-community/mathlib/pull/6834))
This adds the fact that `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` are bijective, as well as some simp lemmas that follow from their injectivity.
#### Estimated changes
Modified src/data/fin.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/real/irrational.lean


Modified src/logic/basic.lean
- \+ *lemma* cast_cast
- \+ *lemma* eq_mp_eq_cast
- \- *lemma* eq_mp_rfl
- \+ *lemma* eq_mpr_eq_cast
- \- *lemma* eq_mpr_rfl
- \+ *lemma* heq_of_cast_eq
- \- *lemma* heq_of_eq_mp
- \- *lemma* {u}

Modified src/logic/function/basic.lean
- \+ *lemma* cast_bijective
- \+ *lemma* cast_inj
- \+ *lemma* eq_mp_bijective
- \+ *lemma* eq_mpr_bijective
- \+ *lemma* eq_rec_inj
- \+ *lemma* eq_rec_on_bijective

Modified src/tactic/interactive.lean


Modified src/tactic/transport.lean


Modified test/equiv_rw.lean




## [2021-03-25 03:23:45](https://github.com/leanprover-community/mathlib/commit/81e8a13)
chore(scripts): update nolints.txt ([#6856](https://github.com/leanprover-community/mathlib/pull/6856))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-25 03:23:44](https://github.com/leanprover-community/mathlib/commit/ec77f22)
chore(measure_theory/measure): add `exists_measurable_superset_forall_eq` ([#6853](https://github.com/leanprover-community/mathlib/pull/6853))
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.exists_measurable_superset_forall_eq



## [2021-03-25 03:23:43](https://github.com/leanprover-community/mathlib/commit/5a72daf)
feat(data/equiv/basic): add a computable version of equiv.set.range ([#6821](https://github.com/leanprover-community/mathlib/pull/6821))
If a left-inverse of `f` is known, it can be used to construct the equiv both computably and with control over definitional reduction.
This adds the definition `equiv.set.range_of_left_inverse` to mirror `linear_equiv.of_left_inverse` and `ring_equiv.of_left_inverse`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *abbreviation* equiv.set.range_of_left_inverse'
- \+ *def* equiv.set.range_of_left_inverse



## [2021-03-25 03:23:42](https://github.com/leanprover-community/mathlib/commit/c3034c2)
feat(data/indicator_function): add multiplicative version ([#6794](https://github.com/leanprover-community/mathlib/pull/6794))
We need it for `finprod`
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/data/indicator_function.lean
- \- *lemma* add_monoid_hom.map_indicator
- \+ *lemma* monoid_hom.map_mul_indicator
- \- *lemma* set.comp_indicator
- \+ *lemma* set.comp_mul_indicator
- \- *lemma* set.eq_on_indicator
- \+ *lemma* set.eq_on_mul_indicator
- \+/\- *def* set.indicator
- \- *lemma* set.indicator_Union_apply
- \- *lemma* set.indicator_add
- \- *lemma* set.indicator_add_eq_left
- \- *lemma* set.indicator_add_eq_right
- \- *lemma* set.indicator_apply
- \- *lemma* set.indicator_apply_eq_self
- \- *lemma* set.indicator_apply_eq_zero
- \- *lemma* set.indicator_comp_of_zero
- \- *lemma* set.indicator_comp_right
- \+/\- *lemma* set.indicator_compl
- \- *lemma* set.indicator_compl_add_self
- \- *lemma* set.indicator_compl_add_self_apply
- \- *lemma* set.indicator_congr
- \- *lemma* set.indicator_empty
- \- *lemma* set.indicator_eq_self
- \- *lemma* set.indicator_eq_self_of_superset
- \- *lemma* set.indicator_eq_zero'
- \- *lemma* set.indicator_eq_zero
- \- *lemma* set.indicator_eq_zero_or_self
- \- *lemma* set.indicator_finset_bUnion
- \- *lemma* set.indicator_finset_sum
- \- *lemma* set.indicator_indicator
- \- *lemma* set.indicator_le'
- \- *lemma* set.indicator_le
- \- *lemma* set.indicator_le_indicator
- \- *lemma* set.indicator_le_indicator_of_subset
- \- *lemma* set.indicator_le_self'
- \- *lemma* set.indicator_le_self
- \+/\- *lemma* set.indicator_mul
- \+/\- *lemma* set.indicator_mul_left
- \+/\- *lemma* set.indicator_mul_right
- \- *lemma* set.indicator_neg
- \- *lemma* set.indicator_nonneg'
- \- *lemma* set.indicator_nonneg
- \- *lemma* set.indicator_nonpos'
- \- *lemma* set.indicator_nonpos
- \- *lemma* set.indicator_of_mem
- \- *lemma* set.indicator_of_not_mem
- \- *lemma* set.indicator_preimage
- \- *lemma* set.indicator_preimage_of_not_mem
- \+/\- *lemma* set.indicator_prod_one
- \- *lemma* set.indicator_range_comp
- \- *lemma* set.indicator_rel_indicator
- \- *lemma* set.indicator_self_add_compl
- \- *lemma* set.indicator_self_add_compl_apply
- \+/\- *lemma* set.indicator_smul
- \+/\- *lemma* set.indicator_sub
- \- *lemma* set.indicator_support
- \- *lemma* set.indicator_union_of_disjoint
- \- *lemma* set.indicator_union_of_not_mem_inter
- \- *lemma* set.indicator_univ
- \- *lemma* set.indicator_zero'
- \- *lemma* set.indicator_zero
- \+/\- *lemma* set.inter_indicator_mul
- \+ *lemma* set.le_mul_indicator
- \+ *lemma* set.le_mul_indicator_apply
- \- *lemma* set.mem_of_indicator_ne_zero
- \+ *lemma* set.mem_of_mul_indicator_ne_one
- \- *lemma* set.mem_range_indicator
- \+ *lemma* set.mem_range_mul_indicator
- \+ *def* set.mul_indicator
- \+ *lemma* set.mul_indicator_Union_apply
- \+ *lemma* set.mul_indicator_apply
- \+ *lemma* set.mul_indicator_apply_eq_one
- \+ *lemma* set.mul_indicator_apply_eq_self
- \+ *lemma* set.mul_indicator_apply_le'
- \+ *lemma* set.mul_indicator_apply_le
- \+ *lemma* set.mul_indicator_apply_le_one
- \+ *lemma* set.mul_indicator_comp_of_one
- \+ *lemma* set.mul_indicator_comp_right
- \+ *lemma* set.mul_indicator_compl
- \+ *lemma* set.mul_indicator_compl_mul_self
- \+ *lemma* set.mul_indicator_compl_mul_self_apply
- \+ *lemma* set.mul_indicator_congr
- \+ *lemma* set.mul_indicator_empty
- \+ *lemma* set.mul_indicator_eq_one'
- \+ *lemma* set.mul_indicator_eq_one
- \+ *lemma* set.mul_indicator_eq_one_or_self
- \+ *lemma* set.mul_indicator_eq_self
- \+ *lemma* set.mul_indicator_eq_self_of_superset
- \+ *lemma* set.mul_indicator_finset_bUnion
- \+ *lemma* set.mul_indicator_finset_prod
- \+ *def* set.mul_indicator_hom
- \+ *lemma* set.mul_indicator_inter_mul_support
- \+ *lemma* set.mul_indicator_inv'
- \+ *lemma* set.mul_indicator_inv
- \+ *lemma* set.mul_indicator_le'
- \+ *lemma* set.mul_indicator_le
- \+ *lemma* set.mul_indicator_le_mul_indicator
- \+ *lemma* set.mul_indicator_le_mul_indicator_of_subset
- \+ *lemma* set.mul_indicator_le_one
- \+ *lemma* set.mul_indicator_le_self'
- \+ *lemma* set.mul_indicator_le_self
- \+ *lemma* set.mul_indicator_mul
- \+ *lemma* set.mul_indicator_mul_eq_left
- \+ *lemma* set.mul_indicator_mul_eq_right
- \+ *lemma* set.mul_indicator_mul_indicator
- \+ *lemma* set.mul_indicator_mul_support
- \+ *lemma* set.mul_indicator_of_mem
- \+ *lemma* set.mul_indicator_of_not_mem
- \+ *lemma* set.mul_indicator_one'
- \+ *lemma* set.mul_indicator_one
- \+ *lemma* set.mul_indicator_preimage
- \+ *lemma* set.mul_indicator_preimage_of_not_mem
- \+ *lemma* set.mul_indicator_range_comp
- \+ *lemma* set.mul_indicator_rel_mul_indicator
- \+ *lemma* set.mul_indicator_self_mul_compl
- \+ *lemma* set.mul_indicator_self_mul_compl_apply
- \+ *lemma* set.mul_indicator_union_mul_inter
- \+ *lemma* set.mul_indicator_union_mul_inter_apply
- \+ *lemma* set.mul_indicator_union_of_disjoint
- \+ *lemma* set.mul_indicator_union_of_not_mem_inter
- \+ *lemma* set.mul_indicator_univ
- \+ *lemma* set.mul_support_mul_indicator
- \+ *lemma* set.mul_support_mul_indicator_subset
- \+ *lemma* set.one_le_mul_indicator
- \+ *lemma* set.one_le_mul_indicator_apply
- \- *lemma* set.piecewise_eq_indicator
- \+ *lemma* set.piecewise_eq_mul_indicator
- \+ *lemma* set.prod_mul_indicator_subset
- \+ *lemma* set.prod_mul_indicator_subset_of_eq_one
- \- *lemma* set.sum_indicator_subset
- \- *lemma* set.sum_indicator_subset_of_eq_zero
- \- *lemma* set.support_indicator
- \- *lemma* set.support_indicator_subset

Modified src/data/support.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set_mul_support

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.integrable.indicator



## [2021-03-24 23:20:35](https://github.com/leanprover-community/mathlib/commit/19e214e)
feat(algebra/normed_space/basic,algebra/group_with_zero/power): real.(f)?pow_{even,bit0}_norm and field fpow lemmas ([#6757](https://github.com/leanprover-community/mathlib/pull/6757))
Simplifcation of `norm` when to an even numeral power.
Additionally, add `fpow` lemmas to match `pow` lemmas, and change `fpow_nonneg_to_nonneg` to `fpow_nonneg` to match `pow` naming.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* abs_fpow_bit0
- \+ *lemma* abs_fpow_even
- \+ *lemma* fpow_bit0_abs
- \+ *lemma* fpow_bit0_neg
- \+ *theorem* fpow_bit0_nonneg
- \+ *theorem* fpow_bit0_pos
- \+ *lemma* fpow_bit1_neg
- \+ *theorem* fpow_bit1_neg_iff
- \+ *theorem* fpow_bit1_nonneg_iff
- \+ *theorem* fpow_bit1_nonpos_iff
- \+ *theorem* fpow_bit1_pos_iff
- \+ *lemma* fpow_eq_zero_iff
- \+ *lemma* fpow_even_abs
- \+ *lemma* fpow_even_neg
- \+ *lemma* fpow_even_nonneg
- \+ *theorem* fpow_even_pos
- \+ *lemma* fpow_nonneg
- \- *lemma* fpow_nonneg_of_nonneg
- \+ *theorem* fpow_odd_neg
- \+ *theorem* fpow_odd_nonneg
- \+ *theorem* fpow_odd_nonpos
- \+ *theorem* fpow_odd_pos
- \+ *theorem* fpow_two_nonneg
- \+ *theorem* fpow_two_pos_of_ne_zero
- \- *lemma* neg_fpow_bit0
- \- *lemma* neg_fpow_bit1

Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* sqr_abs

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* pow_bit0_abs
- \+ *lemma* pow_even_abs

Modified src/algebra/group_with_zero/power.lean
- \+ *lemma* fzero_pow_eq

Modified src/algebra/ring/basic.lean
- \+ *lemma* even_bit0
- \+ *lemma* odd_bit1

Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* real.fpow_bit0_norm
- \+ *lemma* real.fpow_even_norm
- \+ *lemma* real.pow_bit0_norm
- \+ *lemma* real.pow_even_norm

Modified src/data/padics/padic_norm.lean




## [2021-03-24 23:20:34](https://github.com/leanprover-community/mathlib/commit/039dfd2)
refactor(data/finsupp): add decidable_eq ([#6333](https://github.com/leanprover-community/mathlib/pull/6333))
... when the statement (not the proof) of the theorem depends on a
decidability assumption. This prevents instance mismatch issues in
downstream theorems.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.antidiagonal_support_filter_fst_eq
- \+/\- *lemma* finsupp.antidiagonal_support_filter_snd_eq
- \+/\- *lemma* finsupp.count_to_multiset
- \+/\- *lemma* finsupp.filter_apply
- \+/\- *lemma* finsupp.filter_eq_sum
- \+/\- *lemma* finsupp.map_domain_support
- \+/\- *lemma* finsupp.support_add
- \+/\- *lemma* finsupp.support_add_eq
- \+/\- *lemma* finsupp.support_curry
- \+/\- *lemma* finsupp.support_filter
- \+/\- *lemma* finsupp.support_subtype_domain
- \+/\- *lemma* finsupp.support_sum
- \+/\- *lemma* finsupp.support_zip_with
- \+/\- *lemma* finsupp.to_finset_to_multiset
- \+/\- *lemma* multiset.to_finsupp_apply
- \+/\- *lemma* multiset.to_finsupp_support

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.support_add

Modified src/data/polynomial/basic.lean
- \+/\- *lemma* polynomial.support_add

Modified src/logic/basic.lean




## [2021-03-24 19:57:27](https://github.com/leanprover-community/mathlib/commit/77c3bfe)
chore(data/zmod/basic): make `fin.comm_ring.sub` defeq to `fin.sub` ([#6848](https://github.com/leanprover-community/mathlib/pull/6848))
This is only possible now that `fin.sub` is not saturating, and we allow `sub` and `neg` to be defined separately.
#### Estimated changes
Modified src/data/zmod/basic.lean




## [2021-03-24 19:57:24](https://github.com/leanprover-community/mathlib/commit/ab2c44c)
feat(algebra/big_operators/ring): add finset.prod_[one_]sub_ordered ([#6811](https://github.com/leanprover-community/mathlib/pull/6811))
Add 2 lemmas useful for partition of unity, `finset.prod_sub_ordered` and `finset.prod_one_sub_ordered`.
Also add an explicit `[decidable_eq]` assumption to `finset.induction_on_max` (without it some `rw`s failed).
#### Estimated changes
Modified src/algebra/big_operators/ring.lean
- \+ *lemma* finset.prod_add_ordered
- \+ *lemma* finset.prod_one_sub_ordered
- \+ *lemma* finset.prod_sub_ordered

Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.induction_on_max
- \+/\- *lemma* finset.induction_on_min



## [2021-03-24 16:04:14](https://github.com/leanprover-community/mathlib/commit/b4373e5)
feat(tactic/lint): linter for @[class] def ([#6061](https://github.com/leanprover-community/mathlib/pull/6061))
Also cleaning up some uses of `@[class] def` that were missed in [#6028](https://github.com/leanprover-community/mathlib/pull/6028).
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* add_pow_char_of_commute

Modified src/algebra/char_p/invertible.lean


Modified src/algebra/char_p/quotient.lean


Modified src/algebra/homology/exact.lean


Modified src/analysis/calculus/darboux.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/mates.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean
- \- *def* category_theory.is_iso

Modified src/category_theory/limits/cofinal.lean
- \- *def* category_theory.cofinal

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/constructions/over/products.lean


Modified src/category_theory/limits/is_limit.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/shapes/finite_limits.lean
- \- *def* category_theory.limits.has_finite_colimits
- \- *def* category_theory.limits.has_finite_limits
- \- *def* category_theory.limits.has_finite_wide_pullbacks
- \- *def* category_theory.limits.has_finite_wide_pushouts

Modified src/category_theory/limits/shapes/finite_products.lean
- \- *def* category_theory.limits.has_finite_coproducts
- \- *def* category_theory.limits.has_finite_products

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/strong_epi.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monoidal/End.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/natural_transformation.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/over.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/reflects_isomorphisms.lean


Modified src/category_theory/simple.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sieves.lean


Modified src/category_theory/subterminal.lean


Modified src/data/bitvec/basic.lean


Modified src/data/fin.lean
- \+/\- *lemma* fact.succ.pos
- \+/\- *def* fin.of_nat'

Modified src/data/nat/basic.lean


Modified src/data/nat/prime.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean
- \+/\- *lemma* padic_val_nat_primes

Modified src/data/padics/padic_numbers.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/real/irrational.lean


Modified src/data/set/intervals/ord_connected.lean
- \+ *lemma* set.ord_connected.out
- \- *def* set.ord_connected
- \+ *lemma* set.ord_connected_def
- \+/\- *lemma* set.ord_connected_empty
- \+/\- *lemma* set.ord_connected_univ

Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* zmod.frobenius_zmod

Modified src/field_theory/polynomial_galois_group.lean
- \+/\- *def* polynomial.gal.gal_action_hom
- \+/\- *lemma* polynomial.gal.gal_action_hom_injective
- \+/\- *def* polynomial.gal.map_roots
- \+/\- *def* polynomial.gal.restrict
- \+/\- *lemma* polynomial.gal.restrict_smul
- \+/\- *lemma* polynomial.gal.restrict_surjective
- \+/\- *def* polynomial.gal.roots_equiv_roots

Modified src/field_theory/separable.lean


Modified src/geometry/manifold/instances/real.lean
- \+/\- *lemma* fact_zero_lt_one

Modified src/group_theory/dihedral_group.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/quaternion_group.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/logic/basic.lean
- \+/\- *lemma* fact.elim
- \- *def* fact
- \+ *lemma* fact_iff

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* fact_one_le_one_ennreal
- \+/\- *lemma* fact_one_le_top_ennreal

Modified src/measure_theory/prod.lean


Modified src/number_theory/lucas_lehmer.lean
- \+ *lemma* lucas_lehmer.fact_pnat_pos

Modified src/number_theory/primes_congruent_one.lean


Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.eisenstein_lemma
- \+ *lemma* zmod.fact_prime_two
- \+/\- *lemma* zmod.gauss_lemma

Modified src/number_theory/sum_four_squares.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/interval.lean


Modified src/probability_theory/independence.lean


Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* algebra.finite_type.self
- \- *def* algebra.finite_type
- \+/\- *lemma* module.finite.trans
- \- *def* module.finite
- \+/\- *lemma* module.finite_def

Modified src/ring_theory/flat.lean
- \- *def* module.flat

Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/cyclotomic.lean
- \+/\- *lemma* polynomial.order_of_root_cyclotomic
- \+/\- *lemma* polynomial.order_of_root_cyclotomic_dvd

Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/compare.lean


Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/structure_polynomial.lean


Modified src/ring_theory/witt_vector/teichmuller.lean


Modified src/ring_theory/witt_vector/verschiebung.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean


Modified src/set_theory/ordinal_notation.lean
- \+/\- *def* nonote.of_nat
- \- *def* onote.NF

Modified src/set_theory/zfc.lean
- \- *inductive* pSet.definable

Modified src/tactic/lint/type_classes.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified test/linarith.lean
- \+/\- *lemma* T.zero_lt_one
- \+/\- *lemma* abs_nonneg'

Modified test/random.lean
- \+/\- *def* iterated_primality_test_aux
- \+/\- *def* primality_test



## [2021-03-24 13:49:38](https://github.com/leanprover-community/mathlib/commit/a756333)
chore(algebra/algebra/subalgebra): Add missing coe_sort for subalgebra ([#6800](https://github.com/leanprover-community/mathlib/pull/6800))
Unlike all the other subobject types, `subalgebra` does not implement `has_coe_to_sort` directly, instead going via a coercion to one of `submodule` and `subsemiring`.
This removes the `has_coe (subalgebra R A) (subsemiring A)` and `has_coe (subalgebra R A) (submodule R A)` instances; we don't have these for any other subobjects, and they cause the elaborator more difficulty than the corresponding `to_subsemiring` and `to_submodule` projections.
This changes the definition of `le` to not involve coercions, which matches `submodule` but requires a few proofs to change.
This speeds up the `lift_of_splits` proof by adding `finite_dimensional.of_subalgebra_to_submodule`.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+/\- *theorem* algebra.coe_top
- \+/\- *theorem* algebra.to_submodule_bot
- \+ *lemma* subalgebra.coe_injective
- \+/\- *theorem* subalgebra.ext
- \+/\- *theorem* subalgebra.ext_iff
- \+ *lemma* subalgebra.le_def
- \+ *lemma* subalgebra.mem_carrier
- \+/\- *theorem* subalgebra.mem_coe
- \+/\- *lemma* subalgebra.mem_to_submodule
- \+/\- *theorem* subalgebra.mul_self
- \+/\- *theorem* subalgebra.srange_le
- \+/\- *def* subalgebra.to_submodule_equiv
- \+/\- *theorem* subalgebra.to_submodule_inj
- \+/\- *theorem* subalgebra.to_submodule_injective

Modified src/field_theory/adjoin.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/splitting_field.lean
- \+ *lemma* finite_dimensional.of_subalgebra_to_submodule

Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/adjoin/basic.lean
- \+/\- *theorem* algebra.adjoin_eq_span
- \+/\- *theorem* algebra.adjoin_union_coe_submodule
- \+/\- *theorem* algebra.fg_trans
- \+/\- *theorem* subalgebra.fg_of_fg_to_submodule

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean




## [2021-03-24 09:40:12](https://github.com/leanprover-community/mathlib/commit/144e9c4)
chore(*): removing some completed TODOs ([#6844](https://github.com/leanprover-community/mathlib/pull/6844))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/ring_quot.lean


Modified src/category_theory/types.lean
- \+/\- *def* equiv_equiv_iso

Modified src/data/equiv/basic.lean


Modified src/data/hash_map.lean




## [2021-03-24 09:40:11](https://github.com/leanprover-community/mathlib/commit/6773016)
chore(category_theory/triangulated): cleanup ([#6827](https://github.com/leanprover-community/mathlib/pull/6827))
#### Estimated changes
Modified src/category_theory/triangulated/basic.lean
- \- *lemma* category_theory.triangulated.triangle_morphism.comp_assoc
- \- *lemma* category_theory.triangulated.triangle_morphism.comp_id
- \- *lemma* category_theory.triangulated.triangle_morphism.id_comp
- \+/\- *structure* category_theory.triangulated.triangle_morphism



## [2021-03-24 05:49:35](https://github.com/leanprover-community/mathlib/commit/beb2cc9)
feat(algebra/category): subobjects in the category of R-modules ([#6842](https://github.com/leanprover-community/mathlib/pull/6842))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.comp_def

Added src/algebra/category/Module/subobject.lean


Modified src/category_theory/subobject/basic.lean
- \+ *lemma* category_theory.subobject.le_mk_of_comm
- \+ *lemma* category_theory.subobject.mk_le_mk_of_comm
- \+ *lemma* category_theory.subobject.mk_le_of_comm



## [2021-03-24 05:49:34](https://github.com/leanprover-community/mathlib/commit/935003e)
chore(data/nat/basic): add @[simp] to some lemmas about numerals ([#6652](https://github.com/leanprover-community/mathlib/pull/6652))
Allows the simplifier to make more progress in equalities of numerals (both in nat, and in `[(semi)ring R] [no_zero_divisors R] [char_zero R]`). Also adds `@[simp]` to `nat.succ_ne_zero` and `nat.succ_ne_self`.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *lemma* bit0_eq_bit0
- \+ *lemma* bit0_injective
- \+ *lemma* bit1_eq_bit1
- \+ *lemma* bit1_eq_one
- \+ *lemma* bit1_injective
- \+ *lemma* nat_mul_inj'
- \+ *lemma* nat_mul_inj
- \+ *lemma* one_eq_bit1
- \+ *lemma* zero_eq_bit0

Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/nat/basic.lean
- \+ *lemma* nat.bit0_eq_bit0
- \+ *lemma* nat.bit1_eq_bit1
- \+ *lemma* nat.bit1_eq_one
- \+ *lemma* nat.one_eq_bit1

Modified src/data/sym2.lean


Modified src/ring_theory/polynomial/bernstein.lean




## [2021-03-24 02:11:42](https://github.com/leanprover-community/mathlib/commit/e0a7918)
chore(scripts): update nolints.txt ([#6843](https://github.com/leanprover-community/mathlib/pull/6843))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-24 02:11:41](https://github.com/leanprover-community/mathlib/commit/94a4a95)
feat(logic/basic): `is_trans Prop iff` instance ([#6836](https://github.com/leanprover-community/mathlib/pull/6836))
If you've ever wondered why `trans h1 h2` works for `≤` but not for `↔`, this is the reason.
#### Estimated changes
Modified src/logic/basic.lean




## [2021-03-24 02:11:40](https://github.com/leanprover-community/mathlib/commit/a008609)
doc(topology/sheaves/presheaf_of_functions): fix some documentation t… ([#6835](https://github.com/leanprover-community/mathlib/pull/6835))
makes variable names in the documentation match up with the names in the code
#### Estimated changes
Modified src/topology/sheaves/presheaf_of_functions.lean




## [2021-03-24 02:11:39](https://github.com/leanprover-community/mathlib/commit/36fc1ca)
feat(algebraic_geometry/prime_spectrum): prime spectrum analogue of Hilberts Nullstellensatz ([#6805](https://github.com/leanprover-community/mathlib/pull/6805))
Referring to a TODO comment in `algebraic_geometry/prime_spectrum.lean`, which I presume is outdated.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.vanishing_ideal_zero_locus_eq_radical



## [2021-03-24 02:11:38](https://github.com/leanprover-community/mathlib/commit/12170e2)
feat(topology/algebra/continuous_functions): separates points ([#6783](https://github.com/leanprover-community/mathlib/pull/6783))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *def* separates_points
- \+ *def* separates_points_strongly

Modified src/topology/algebra/continuous_functions.lean
- \+ *lemma* subalgebra.separates_points.strongly
- \+ *abbreviation* subalgebra.separates_points
- \+ *lemma* subalgebra.separates_points_monotone



## [2021-03-23 23:08:24](https://github.com/leanprover-community/mathlib/commit/fd5f433)
fix(algebraic_topology): added FQNs to simplicial locale ([#6838](https://github.com/leanprover-community/mathlib/pull/6838))
This fix, which fully qualifies some notation, makes it so that
```
import algebraic_topology.simplicial_set
open_locale simplicial
```
works without errors.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean


Modified src/algebraic_topology/simplicial_set.lean




## [2021-03-23 23:08:23](https://github.com/leanprover-community/mathlib/commit/ee5e9fb)
feat(data/indicator_function): eq_self_of_superset ([#6829](https://github.com/leanprover-community/mathlib/pull/6829))
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_eq_self_of_superset



## [2021-03-23 23:08:21](https://github.com/leanprover-community/mathlib/commit/aadd853)
feat(algebra/category): add more variants of Module.as_hom ([#6822](https://github.com/leanprover-community/mathlib/pull/6822))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+ *def* Module.as_hom_left
- \+ *def* Module.as_hom_right
- \+ *def* linear_equiv.to_Module_iso'_left
- \+ *def* linear_equiv.to_Module_iso'_right

Modified src/category_theory/sites/types.lean


Modified src/category_theory/types.lean




## [2021-03-23 23:08:19](https://github.com/leanprover-community/mathlib/commit/b6e4d0b)
feat(combinatorics/quiver): every connected graph has a spanning tree ([#6806](https://github.com/leanprover-community/mathlib/pull/6806))
Prove a directed version of the fact that a connected graph has a
spanning tree. The subtree we use is what you would get from 'running a
DFS from the root'. This proof avoids any use of Zorn's lemma. Currently
we have no notion of undirected tree, but once that is in place, this
proof should also give undirected spanning trees.
#### Estimated changes
Modified src/combinatorics/quiver.lean
- \+ *def* quiver.geodesic_subtree
- \+ *lemma* quiver.path.length_cons
- \+ *lemma* quiver.path.length_nil
- \+ *lemma* quiver.shortest_path_spec



## [2021-03-23 19:49:37](https://github.com/leanprover-community/mathlib/commit/315faac)
feat(data/multiset/basic): generalize rel.mono, rel_map ([#6771](https://github.com/leanprover-community/mathlib/pull/6771))
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/data/multiset/basic.lean
- \+/\- *lemma* multiset.rel.mono
- \+/\- *lemma* multiset.rel_map



## [2021-03-23 19:49:36](https://github.com/leanprover-community/mathlib/commit/9cda1ff)
fix(data/complex/module): kill a non-defeq diamond  ([#6760](https://github.com/leanprover-community/mathlib/pull/6760))
`restrict_scalars.semimodule ℝ ℂ ℂ  = complex.semimodule` is currently not definitionally true. The PR tweaks the smul definition to make sure that this becomes true. This solves a diamond that appears naturally in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.60inner_product_space.20.E2.84.9D.20%28euclidean_space.20.F0.9D.95.9C.20n%29.60.3F/near/230780186
#### Estimated changes
Modified src/data/complex/module.lean
- \+/\- *lemma* complex.smul_im
- \+/\- *lemma* complex.smul_re



## [2021-03-23 19:49:35](https://github.com/leanprover-community/mathlib/commit/9893a26)
chore(field_theory/splitting_field): module doc and generalise one lemma ([#6739](https://github.com/leanprover-community/mathlib/pull/6739))
This PR provides a module doc for `field_theory.splitting_field`, which is the last file without module doc in `field_theory`. Furthermore, I took the opportunity of renaming the fields in that file from `\alpha`, `\beta`, `\gamma` to `K`, `L`, `F` to make it more readable for newcomers.
Moved `nat_degree_multiset_prod`, to `algebra.polynomial.big_operators`). In order to get the `no_zero_divisors` instance on `polynomial R`, I had to include `data.polynomial.ring_division` in that file. Furthermore, with the help of Damiano, generalised this lemma to `no_zero_divisors R`.
Coauthored by: Damiano Testa adomani@gmail.com
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean
- \+ *lemma* polynomial.nat_degree_multiset_prod

Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C
- \+/\- *theorem* polynomial.X_sub_C_mul_remove_factor
- \+/\- *lemma* polynomial.degree_eq_card_roots
- \+/\- *lemma* polynomial.degree_eq_one_of_irreducible_of_splits
- \+/\- *lemma* polynomial.eq_X_sub_C_of_splits_of_single_root
- \+/\- *lemma* polynomial.eq_prod_roots_of_splits
- \+/\- *lemma* polynomial.exists_multiset_of_splits
- \+/\- *lemma* polynomial.exists_root_of_splits
- \+/\- *def* polynomial.factor
- \+/\- *theorem* polynomial.factor_dvd_of_degree_ne_zero
- \+/\- *theorem* polynomial.factor_dvd_of_nat_degree_ne_zero
- \+/\- *theorem* polynomial.factor_dvd_of_not_is_unit
- \+/\- *def* polynomial.is_splitting_field.alg_equiv
- \+/\- *theorem* polynomial.is_splitting_field.finite_dimensional
- \+/\- *def* polynomial.is_splitting_field.lift
- \+/\- *theorem* polynomial.is_splitting_field.mul
- \+/\- *theorem* polynomial.is_splitting_field.splits_iff
- \+/\- *theorem* polynomial.map_root_of_splits
- \+/\- *lemma* polynomial.nat_degree_eq_card_roots
- \- *lemma* polynomial.nat_degree_multiset_prod
- \+/\- *theorem* polynomial.nat_degree_remove_factor'
- \+/\- *theorem* polynomial.nat_degree_remove_factor
- \+/\- *lemma* polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+/\- *def* polynomial.remove_factor
- \+/\- *def* polynomial.root_of_splits
- \+/\- *theorem* polynomial.roots_map
- \+/\- *def* polynomial.splits
- \+/\- *lemma* polynomial.splits_C
- \+/\- *theorem* polynomial.splits_X_sub_C
- \+/\- *lemma* polynomial.splits_comp_of_splits
- \+/\- *theorem* polynomial.splits_id_iff_splits
- \+/\- *lemma* polynomial.splits_iff_card_roots
- \+/\- *lemma* polynomial.splits_iff_exists_multiset
- \+/\- *lemma* polynomial.splits_map_iff
- \+/\- *lemma* polynomial.splits_mul
- \+/\- *theorem* polynomial.splits_mul_iff
- \+/\- *lemma* polynomial.splits_of_degree_eq_one
- \+/\- *lemma* polynomial.splits_of_degree_le_one
- \+/\- *lemma* polynomial.splits_of_exists_multiset
- \+/\- *theorem* polynomial.splits_of_is_unit
- \+/\- *lemma* polynomial.splits_of_nat_degree_eq_one
- \+/\- *lemma* polynomial.splits_of_nat_degree_le_one
- \+/\- *lemma* polynomial.splits_of_splits_gcd_left
- \+/\- *lemma* polynomial.splits_of_splits_gcd_right
- \+/\- *lemma* polynomial.splits_of_splits_id
- \+/\- *lemma* polynomial.splits_of_splits_mul
- \+/\- *lemma* polynomial.splits_of_splits_of_dvd
- \+/\- *lemma* polynomial.splits_pow
- \+/\- *theorem* polynomial.splits_prod
- \+/\- *theorem* polynomial.splits_prod_iff
- \+/\- *lemma* polynomial.splits_zero
- \+/\- *theorem* polynomial.splitting_field.adjoin_root_set
- \+/\- *theorem* polynomial.splitting_field.adjoin_roots
- \+/\- *def* polynomial.splitting_field.lift
- \+/\- *def* polynomial.splitting_field
- \+/\- *theorem* polynomial.splitting_field_aux.adjoin_roots
- \+/\- *theorem* polynomial.splitting_field_aux.algebra_map_succ
- \+/\- *theorem* polynomial.splitting_field_aux.exists_lift
- \+/\- *theorem* polynomial.splitting_field_aux.succ
- \+/\- *def* polynomial.splitting_field_aux



## [2021-03-23 19:49:34](https://github.com/leanprover-community/mathlib/commit/c521336)
feat(data/polynomial/bernstein): identities ([#6470](https://github.com/leanprover-community/mathlib/pull/6470))
#### Estimated changes
Modified src/data/mv_polynomial/pderiv.lean
- \+ *lemma* mv_polynomial.pderiv_X
- \+ *lemma* mv_polynomial.pderiv_X_self
- \+ *lemma* mv_polynomial.pderiv_nat_cast
- \+ *lemma* mv_polynomial.pderiv_one
- \+ *lemma* mv_polynomial.pderiv_pow

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.nat_cast_mul

Modified src/ring_theory/polynomial/bernstein.lean
- \+ *lemma* bernstein_polynomial.sum
- \+ *lemma* bernstein_polynomial.sum_mul_smul
- \+ *lemma* bernstein_polynomial.sum_smul



## [2021-03-23 19:49:32](https://github.com/leanprover-community/mathlib/commit/edfe7e1)
feat(combinatorics/simple_graph): degree lemmas ([#5966](https://github.com/leanprover-community/mathlib/pull/5966))
Proves some lemmas about the minimum/maximum degree of vertices in a graph - also weakens the assumptions for the definitions, following the usual mathlib pattern of defining total functions.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.degree_le_max_degree
- \+ *lemma* simple_graph.exists_maximal_degree_vertex
- \+ *lemma* simple_graph.exists_minimal_degree_vertex
- \+ *lemma* simple_graph.le_min_degree_of_forall_le_degree
- \+/\- *def* simple_graph.max_degree
- \+ *lemma* simple_graph.max_degree_le_of_forall_degree_le
- \+ *lemma* simple_graph.max_degree_lt_card_verts
- \+/\- *def* simple_graph.min_degree
- \+ *lemma* simple_graph.min_degree_le_degree



## [2021-03-23 15:29:30](https://github.com/leanprover-community/mathlib/commit/61ed14e)
lint(*): split long lines ([#6833](https://github.com/leanprover-community/mathlib/pull/6833))
#### Estimated changes
Modified src/analysis/convex/caratheodory.lean


Modified src/analysis/specific_limits.lean


Modified src/data/padics/hensel.lean


Modified src/data/set/basic.lean


Modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* euclidean_geometry.dist_reflection

Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* basic_smooth_bundle_core.mem_chart_source_iff

Modified src/geometry/manifold/charted_space.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/times_cont_mdiff.lean
- \+/\- *lemma* smooth.mdifferentiable_within_at
- \+/\- *lemma* times_cont_mdiff_within_at.of_succ

Modified src/logic/function/basic.lean
- \+/\- *lemma* function.update_noteq
- \+/\- *def* set.piecewise

Modified src/order/galois_connection.lean
- \+/\- *def* galois_coinsertion.monotone_intro

Modified src/order/zorn.lean


Modified src/topology/instances/real.lean
- \+/\- *lemma* real.mem_closure_iff

Modified src/topology/local_homeomorph.lean
- \+/\- *def* local_homeomorph.prod
- \+/\- *lemma* local_homeomorph.prod_to_local_equiv

Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* Top.presheaf.pushforward.comp_hom_app
- \+/\- *lemma* Top.presheaf.pushforward.comp_inv_app
- \+/\- *def* Top.presheaf.pushforward_map

Modified src/topology/tactic.lean


Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* uniform_space.separation_quotient.lift_mk

Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2021-03-23 15:29:29](https://github.com/leanprover-community/mathlib/commit/7803435)
refactor(topology/metric_space/lipschitz): generalize to pseudo_emetric_space ([#6831](https://github.com/leanprover-community/mathlib/pull/6831))
This is part of a series of PR to introduce `semi_normed_group` in mathlib.
We introduce here Lipschitz maps for `pseudo_emetric_space` (I also improve some theorem name in `topology/metric_space/emetric_space`).
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/basic.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *lemma* edist_pi_const
- \+/\- *lemma* edist_pi_def
- \+/\- *lemma* prod.edist_eq
- \- *lemma* prod.pesudoedist_eq
- \- *lemma* pseudo_edist_pi_const
- \- *lemma* pseudo_edist_pi_def

Modified src/topology/metric_space/lipschitz.lean
- \+/\- *lemma* lipschitz_on_univ
- \+/\- *lemma* lipschitz_on_with.mono
- \+/\- *def* lipschitz_on_with
- \+/\- *lemma* lipschitz_on_with_empty
- \+/\- *lemma* lipschitz_on_with_iff_dist_le_mul
- \+/\- *lemma* lipschitz_on_with_iff_restrict
- \+/\- *def* lipschitz_with
- \+/\- *lemma* lipschitz_with_iff_dist_le_mul



## [2021-03-23 15:29:28](https://github.com/leanprover-community/mathlib/commit/489f522)
feat(category_theory/subobject): API for working with inequalities ([#6818](https://github.com/leanprover-community/mathlib/pull/6818))
This PR adds two types of declarations:
* Helper functions for showing that two subobjects are equal by giving a compatible isomorphism, and
* functions `of_le`/`of_le_mk`/`of_mk_le`/`of_mk_le_mk` that produce a morphism between the underlying objects from a proof of `X ≤ Y`. These are in essence just thin wrappers around `underlying.map`.
#### Estimated changes
Modified src/category_theory/subobject/basic.lean
- \+ *lemma* category_theory.subobject.eq_mk_of_comm
- \+ *lemma* category_theory.subobject.eq_of_comm
- \+ *lemma* category_theory.subobject.mk_eq_mk_of_comm
- \+ *lemma* category_theory.subobject.mk_eq_of_comm
- \+ *def* category_theory.subobject.of_le
- \+ *lemma* category_theory.subobject.of_le_arrow
- \+ *def* category_theory.subobject.of_le_mk
- \+ *lemma* category_theory.subobject.of_le_mk_comp
- \+ *def* category_theory.subobject.of_mk_le
- \+ *lemma* category_theory.subobject.of_mk_le_arrow
- \+ *def* category_theory.subobject.of_mk_le_mk
- \+ *lemma* category_theory.subobject.of_mk_le_mk_comp
- \+ *lemma* category_theory.subobject.underlying_iso_hom_comp_eq_mk



## [2021-03-23 15:29:25](https://github.com/leanprover-community/mathlib/commit/736b1e8)
feat(data/fintype/basic): add decidable_mem_range_fintype ([#6817](https://github.com/leanprover-community/mathlib/pull/6817))
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2021-03-23 15:29:24](https://github.com/leanprover-community/mathlib/commit/c2e9ec0)
feat(group_theory/subgroup): add {monoid,add_monoid,ring}_hom.lift_of_right_inverse ([#6814](https://github.com/leanprover-community/mathlib/pull/6814))
This provides a computable alternative to `lift_of_surjective`.
#### Estimated changes
Modified src/data/zmod/basic.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.eq_lift_of_right_inverse
- \- *lemma* monoid_hom.eq_lift_of_surjective
- \+ *def* monoid_hom.lift_of_right_inverse
- \+ *def* monoid_hom.lift_of_right_inverse_aux
- \+ *lemma* monoid_hom.lift_of_right_inverse_aux_comp_apply
- \+ *lemma* monoid_hom.lift_of_right_inverse_comp
- \+ *lemma* monoid_hom.lift_of_right_inverse_comp_apply
- \- *lemma* monoid_hom.lift_of_surjective_comp
- \- *lemma* monoid_hom.lift_of_surjective_comp_apply

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ring_hom.eq_lift_of_right_inverse
- \- *lemma* ring_hom.eq_lift_of_surjective
- \+ *def* ring_hom.lift_of_right_inverse
- \+ *def* ring_hom.lift_of_right_inverse_aux
- \+ *lemma* ring_hom.lift_of_right_inverse_aux_comp_apply
- \+ *lemma* ring_hom.lift_of_right_inverse_comp
- \+ *lemma* ring_hom.lift_of_right_inverse_comp_apply
- \- *lemma* ring_hom.lift_of_surjective_comp
- \- *lemma* ring_hom.lift_of_surjective_comp_apply

Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/truncated.lean




## [2021-03-23 15:29:23](https://github.com/leanprover-community/mathlib/commit/5cafdff)
chore(algebra/group/basic): dedup, add a lemma ([#6810](https://github.com/leanprover-community/mathlib/pull/6810))
* drop `sub_eq_zero_iff_eq`, was a duplicate of `sub_eq_zero`;
* add a `simp` lemma `sub_eq_self : a - b = a ↔ b = 0`.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/group/basic.lean
- \+ *theorem* sub_eq_self
- \- *lemma* sub_eq_zero_iff_eq
- \- *lemma* sub_eq_zero_of_eq

Modified src/algebra/lie/basic.lean


Modified src/algebra/linear_recurrence.lean


Modified src/algebra/ring/basic.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/ring_division.lean


Modified src/data/real/golden_ratio.lean


Modified src/data/real/liouville.lean


Modified src/field_theory/abel_ruffini.lean


Modified src/geometry/euclidean/basic.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/dual.lean


Modified src/number_theory/bernoulli.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-03-23 06:50:41](https://github.com/leanprover-community/mathlib/commit/94f59d8)
feat(ring_theory/polynomial/homogenous): add a `direct_sum.gcomm_monoid` instance ([#6825](https://github.com/leanprover-community/mathlib/pull/6825))
This also corrects a stupid typo I made in `direct_sum.comm_ring` which was previously declared a `ring`!
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean


Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-03-22 23:38:18](https://github.com/leanprover-community/mathlib/commit/9f56a0b)
refactor(tactic/ring): split off `ring_nf` tactic ([#6792](https://github.com/leanprover-community/mathlib/pull/6792))
[As requested on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring.20not.20idempotent/near/231178246) This splits the current behavior of `ring` into two tactics:
* `ring1`: closing tactic which solves equations in the goal only
* `ring_nf mode? (at h)?`: simplification tactic which puts ring expressions into normal form
The `ring` tactic will still call `ring1` with `ring_nf` as fallback, as it does currently, but in the latter case it will print a message telling the user to use `ring_nf` instead. The form `ring at h` is removed, because this never uses `ring1` so you should just call `ring_nf` directly.
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified archive/imo/imo2013_q5.lean


Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/star/chsh.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/fp/basic.lean


Modified src/data/nat/fib.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/real/golden_ratio.lean


Modified src/data/real/pi.lean


Modified src/data/zmod/basic.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/number_theory/pell.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/group.lean


Modified src/tactic/ring.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/path_connected.lean


Modified test/conv.lean


Modified test/differentiable.lean


Modified test/linarith.lean


Modified test/ring.lean




## [2021-03-22 19:59:29](https://github.com/leanprover-community/mathlib/commit/a0a2177)
feat(data/support): add `function.mul_support` ([#6791](https://github.com/leanprover-community/mathlib/pull/6791))
This will help us add `finprod` in [#6355](https://github.com/leanprover-community/mathlib/pull/6355)
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/data/support.lean
- \+ *lemma* function.compl_mul_support
- \- *lemma* function.compl_support
- \+ *lemma* function.mem_mul_support
- \- *lemma* function.mem_support
- \+ *def* function.mul_support
- \+ *lemma* function.mul_support_add_one'
- \+ *lemma* function.mul_support_add_one
- \+ *lemma* function.mul_support_binop_subset
- \+ *lemma* function.mul_support_comp_eq
- \+ *lemma* function.mul_support_comp_eq_preimage
- \+ *lemma* function.mul_support_comp_subset
- \+ *lemma* function.mul_support_div
- \+ *lemma* function.mul_support_eq_empty_iff
- \+ *lemma* function.mul_support_group_div
- \+ *lemma* function.mul_support_inf
- \+ *lemma* function.mul_support_infi
- \+ *lemma* function.mul_support_inv''
- \+ *lemma* function.mul_support_inv'
- \+ *lemma* function.mul_support_inv
- \+ *lemma* function.mul_support_max
- \+ *lemma* function.mul_support_min
- \+ *lemma* function.mul_support_mul
- \+ *lemma* function.mul_support_mul_inv
- \+ *lemma* function.mul_support_one'
- \+ *lemma* function.mul_support_one
- \+ *lemma* function.mul_support_one_add'
- \+ *lemma* function.mul_support_one_add
- \+ *lemma* function.mul_support_one_sub'
- \+ *lemma* function.mul_support_one_sub
- \+ *lemma* function.mul_support_prod
- \+ *lemma* function.mul_support_prod_mk'
- \+ *lemma* function.mul_support_prod_mk
- \+ *lemma* function.mul_support_subset_comp
- \+ *lemma* function.mul_support_subset_iff'
- \+ *lemma* function.mul_support_subset_iff
- \+ *lemma* function.mul_support_sup
- \+ *lemma* function.mul_support_supr
- \+ *lemma* function.nmem_mul_support
- \- *lemma* function.nmem_support
- \- *lemma* function.support_add
- \- *lemma* function.support_binop_subset
- \- *lemma* function.support_comp_eq
- \- *lemma* function.support_comp_eq_preimage
- \- *lemma* function.support_comp_subset
- \+/\- *lemma* function.support_div
- \- *lemma* function.support_eq_empty_iff
- \- *lemma* function.support_inf
- \- *lemma* function.support_infi
- \+/\- *lemma* function.support_inv
- \- *lemma* function.support_max
- \- *lemma* function.support_min
- \+/\- *lemma* function.support_mul
- \- *lemma* function.support_neg
- \- *lemma* function.support_prod_mk
- \+/\- *lemma* function.support_smul
- \+/\- *lemma* function.support_smul_subset_left
- \- *lemma* function.support_sub
- \- *lemma* function.support_subset_comp
- \- *lemma* function.support_subset_iff'
- \- *lemma* function.support_subset_iff
- \- *lemma* function.support_sum
- \- *lemma* function.support_sup
- \- *lemma* function.support_supr
- \- *lemma* function.support_zero'
- \- *lemma* function.support_zero
- \+/\- *lemma* pi.support_single_of_ne



## [2021-03-22 16:18:52](https://github.com/leanprover-community/mathlib/commit/ffca31a)
feat(linear_algebra): composing with a linear equivalence does not change the image ([#6816](https://github.com/leanprover-community/mathlib/pull/6816))
I also did some minor reorganisation in order to relax some typeclass arguments.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_equiv.ker_comp
- \+ *theorem* linear_equiv.range_comp
- \+ *lemma* linear_map.ker_comp_of_ker_eq_bot
- \+ *lemma* linear_map.range_comp_of_range_eq_top



## [2021-03-22 16:18:51](https://github.com/leanprover-community/mathlib/commit/e54f633)
feat(data/finsupp/basic): add `can_lift (α → M₀) (α →₀ M₀)` ([#6777](https://github.com/leanprover-community/mathlib/pull/6777))
Also add a few missing `simp`/`norm_cast` lemmas.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* finset.coe_empty
- \+ *lemma* finset.coe_eq_empty

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_eq_zero
- \+ *lemma* finsupp.coe_fn_inj
- \+/\- *lemma* finsupp.coe_zero
- \- *lemma* finsupp.finite_supp
- \+ *lemma* finsupp.finite_support
- \+/\- *lemma* finsupp.fun_support_eq
- \+ *lemma* finsupp.of_support_finite_coe

Modified src/ring_theory/polynomial/homogeneous.lean




## [2021-03-22 16:18:49](https://github.com/leanprover-community/mathlib/commit/480b00c)
feat(algebra/group/type_tags): adding function coercion for `additive` and `multiplicative` ([#6657](https://github.com/leanprover-community/mathlib/pull/6657))
[As on zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/to_additive.20mismatch/near/230042978)
#### Estimated changes
Modified src/algebra/group/type_tags.lean




## [2021-03-22 10:12:29](https://github.com/leanprover-community/mathlib/commit/0b543c3)
feat(linear_algebra/dual): add dual_annihilator_sup_eq_inf_dual_annihilator ([#6808](https://github.com/leanprover-community/mathlib/pull/6808))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+ *lemma* submodule.dual_annihilator_sup_eq_inf_dual_annihilator



## [2021-03-22 10:12:28](https://github.com/leanprover-community/mathlib/commit/f3a4c48)
feat(algebra/subalgebra): missing norm_cast lemmas about operations ([#6790](https://github.com/leanprover-community/mathlib/pull/6790))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* subalgebra.coe_add
- \+ *lemma* subalgebra.coe_algebra_map
- \+ *lemma* subalgebra.coe_eq_one
- \+ *lemma* subalgebra.coe_eq_zero
- \+ *lemma* subalgebra.coe_mul
- \+ *lemma* subalgebra.coe_neg
- \+ *lemma* subalgebra.coe_one
- \+ *lemma* subalgebra.coe_pow
- \+ *lemma* subalgebra.coe_smul
- \+ *lemma* subalgebra.coe_sub
- \+ *lemma* subalgebra.coe_zero

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.coe_add
- \+/\- *lemma* subsemiring.coe_mul
- \+/\- *lemma* subsemiring.coe_one
- \+ *lemma* subsemiring.coe_pow
- \+ *lemma* subsemiring.coe_zero



## [2021-03-22 07:20:26](https://github.com/leanprover-community/mathlib/commit/e7d74ba)
feat(algebra/smul_regular): add `M`-regular elements ([#6659](https://github.com/leanprover-community/mathlib/pull/6659))
This PR extends PR [#6590](https://github.com/leanprover-community/mathlib/pull/6590), that is now merged.  The current PR contains the actual API to work with `M`-regular elements `r : R`, called `is_smul_regular M r`.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews
From the doc-string:
### Action of regular elements on a module
We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `is_smul_regular`.
There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting an a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Smultiplications involving `0` are, of course, all trivial.
The defining property is that an element `a ∈ R` is `M`-regular if the smultiplication map
`M → M`, defined by `m ↦ a • m`, is injective.
This property is the direct generalization to modules of the property `is_left_regular` defined in
`algebra/regular`.  Lemma `is_smul_regular.is_left_regular_iff` shows that indeed the two notions
coincide.
#### Estimated changes
Added src/algebra/smul_regular.lean
- \+ *lemma* is_smul_regular.is_left_regular_iff
- \+ *lemma* is_smul_regular.mul
- \+ *lemma* is_smul_regular.mul_and_mul_iff
- \+ *lemma* is_smul_regular.mul_iff
- \+ *lemma* is_smul_regular.mul_iff_right
- \+ *lemma* is_smul_regular.not_zero
- \+ *lemma* is_smul_regular.not_zero_iff
- \+ *lemma* is_smul_regular.of_mul
- \+ *lemma* is_smul_regular.of_mul_eq_one
- \+ *lemma* is_smul_regular.of_smul
- \+ *lemma* is_smul_regular.of_smul_eq_one
- \+ *lemma* is_smul_regular.one
- \+ *lemma* is_smul_regular.pow
- \+ *lemma* is_smul_regular.pow_iff
- \+ *lemma* is_smul_regular.smul
- \+ *lemma* is_smul_regular.smul_iff
- \+ *lemma* is_smul_regular.zero
- \+ *lemma* is_smul_regular.zero_iff_subsingleton
- \+ *def* is_smul_regular
- \+ *lemma* is_unit.is_smul_regular
- \+ *lemma* units.is_smul_regular

Modified src/algebra/smul_with_zero.lean




## [2021-03-22 01:19:20](https://github.com/leanprover-community/mathlib/commit/5be0b0c)
feat(data/finset/basic): add strong_induction and strong_induction_eq ([#6682](https://github.com/leanprover-community/mathlib/pull/6682))
An alternative to `finset.strong_induction_on` that has an associated equation lemma.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *def* finset.strong_induction
- \+ *lemma* finset.strong_induction_eq
- \+ *lemma* finset.strong_induction_on_eq



## [2021-03-21 20:45:07](https://github.com/leanprover-community/mathlib/commit/3f74b10)
chore(order/filter/bases): a few more constructors ([#6798](https://github.com/leanprover-community/mathlib/pull/6798))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.to_has_basis'
- \+ *lemma* filter.has_basis.to_subset



## [2021-03-21 15:58:36](https://github.com/leanprover-community/mathlib/commit/852064a)
refactor(category_theory/subobject): split into smaller files ([#6796](https://github.com/leanprover-community/mathlib/pull/6796))
No change in content, just splitting into four files.
#### Estimated changes
Deleted src/category_theory/subobject.lean
- \- *def* category_theory.limits.equalizer_subobject
- \- *lemma* category_theory.limits.equalizer_subobject_arrow'
- \- *lemma* category_theory.limits.equalizer_subobject_arrow
- \- *lemma* category_theory.limits.equalizer_subobject_arrow_comp
- \- *lemma* category_theory.limits.equalizer_subobject_factors
- \- *lemma* category_theory.limits.equalizer_subobject_factors_iff
- \- *def* category_theory.limits.equalizer_subobject_iso
- \- *def* category_theory.limits.factor_thru_image_subobject
- \- *def* category_theory.limits.image_subobject
- \- *lemma* category_theory.limits.image_subobject_arrow'
- \- *lemma* category_theory.limits.image_subobject_arrow
- \- *lemma* category_theory.limits.image_subobject_arrow_comp
- \- *lemma* category_theory.limits.image_subobject_factors
- \- *def* category_theory.limits.image_subobject_iso
- \- *lemma* category_theory.limits.image_subobject_le
- \- *def* category_theory.limits.kernel_subobject
- \- *lemma* category_theory.limits.kernel_subobject_arrow'
- \- *lemma* category_theory.limits.kernel_subobject_arrow
- \- *lemma* category_theory.limits.kernel_subobject_arrow_comp
- \- *lemma* category_theory.limits.kernel_subobject_factors
- \- *lemma* category_theory.limits.kernel_subobject_factors_iff
- \- *def* category_theory.limits.kernel_subobject_iso
- \- *abbreviation* category_theory.mono_over.arrow
- \- *lemma* category_theory.mono_over.bot_arrow
- \- *def* category_theory.mono_over.bot_le
- \- *lemma* category_theory.mono_over.bot_left
- \- *def* category_theory.mono_over.exists_iso_map
- \- *def* category_theory.mono_over.exists_pullback_adj
- \- *def* category_theory.mono_over.factor_thru
- \- *def* category_theory.mono_over.factors
- \- *def* category_theory.mono_over.forget
- \- *def* category_theory.mono_over.forget_image
- \- *lemma* category_theory.mono_over.forget_obj_hom
- \- *lemma* category_theory.mono_over.forget_obj_left
- \- *abbreviation* category_theory.mono_over.hom_mk
- \- *def* category_theory.mono_over.image
- \- *def* category_theory.mono_over.image_forget_adj
- \- *def* category_theory.mono_over.image_mono_over
- \- *lemma* category_theory.mono_over.image_mono_over_arrow
- \- *def* category_theory.mono_over.inf
- \- *def* category_theory.mono_over.inf_le_left
- \- *def* category_theory.mono_over.inf_le_right
- \- *def* category_theory.mono_over.iso_mk
- \- *def* category_theory.mono_over.le_inf
- \- *def* category_theory.mono_over.le_sup_left
- \- *def* category_theory.mono_over.le_sup_right
- \- *def* category_theory.mono_over.le_top
- \- *def* category_theory.mono_over.lift
- \- *lemma* category_theory.mono_over.lift_comm
- \- *def* category_theory.mono_over.lift_comp
- \- *def* category_theory.mono_over.lift_id
- \- *def* category_theory.mono_over.lift_iso
- \- *def* category_theory.mono_over.map
- \- *def* category_theory.mono_over.map_bot
- \- *def* category_theory.mono_over.map_comp
- \- *def* category_theory.mono_over.map_id
- \- *def* category_theory.mono_over.map_iso
- \- *lemma* category_theory.mono_over.map_obj_arrow
- \- *lemma* category_theory.mono_over.map_obj_left
- \- *def* category_theory.mono_over.map_pullback_adj
- \- *def* category_theory.mono_over.map_top
- \- *def* category_theory.mono_over.mk'
- \- *lemma* category_theory.mono_over.mk'_arrow
- \- *def* category_theory.mono_over.pullback
- \- *def* category_theory.mono_over.pullback_comp
- \- *def* category_theory.mono_over.pullback_id
- \- *def* category_theory.mono_over.pullback_map_self
- \- *lemma* category_theory.mono_over.pullback_obj_arrow
- \- *lemma* category_theory.mono_over.pullback_obj_left
- \- *def* category_theory.mono_over.pullback_self
- \- *def* category_theory.mono_over.pullback_top
- \- *def* category_theory.mono_over.slice
- \- *def* category_theory.mono_over.sup
- \- *def* category_theory.mono_over.sup_le
- \- *lemma* category_theory.mono_over.top_arrow
- \- *def* category_theory.mono_over.top_le_pullback_self
- \- *lemma* category_theory.mono_over.top_left
- \- *lemma* category_theory.mono_over.w
- \- *def* category_theory.mono_over.«exists»
- \- *def* category_theory.mono_over
- \- *def* category_theory.subobject.arrow
- \- *lemma* category_theory.subobject.bot_arrow
- \- *def* category_theory.subobject.bot_coe_iso_zero
- \- *lemma* category_theory.subobject.bot_eq_zero
- \- *lemma* category_theory.subobject.bot_factors_iff_zero
- \- *lemma* category_theory.subobject.eq_of_comp_arrow_eq
- \- *lemma* category_theory.subobject.exists_iso_map
- \- *def* category_theory.subobject.exists_pullback_adj
- \- *def* category_theory.subobject.factor_thru
- \- *lemma* category_theory.subobject.factor_thru_arrow
- \- *lemma* category_theory.subobject.factor_thru_eq_zero
- \- *lemma* category_theory.subobject.factor_thru_right
- \- *def* category_theory.subobject.factors
- \- *lemma* category_theory.subobject.factors_comp_arrow
- \- *lemma* category_theory.subobject.factors_iff
- \- *lemma* category_theory.subobject.factors_left_of_inf_factors
- \- *lemma* category_theory.subobject.factors_of_factors_right
- \- *lemma* category_theory.subobject.factors_of_le
- \- *lemma* category_theory.subobject.factors_right_of_inf_factors
- \- *lemma* category_theory.subobject.finset_inf_arrow_factors
- \- *lemma* category_theory.subobject.finset_inf_factors
- \- *lemma* category_theory.subobject.finset_sup_factors
- \- *def* category_theory.subobject.functor
- \- *def* category_theory.subobject.inf
- \- *lemma* category_theory.subobject.inf_arrow_factors_left
- \- *lemma* category_theory.subobject.inf_arrow_factors_right
- \- *lemma* category_theory.subobject.inf_def
- \- *lemma* category_theory.subobject.inf_eq_map_pullback'
- \- *lemma* category_theory.subobject.inf_eq_map_pullback
- \- *lemma* category_theory.subobject.inf_factors
- \- *lemma* category_theory.subobject.inf_le_left
- \- *lemma* category_theory.subobject.inf_le_right
- \- *lemma* category_theory.subobject.inf_map
- \- *lemma* category_theory.subobject.inf_pullback
- \- *lemma* category_theory.subobject.le_inf
- \- *lemma* category_theory.subobject.le_of_comm
- \- *def* category_theory.subobject.lower
- \- *def* category_theory.subobject.lower_adjunction
- \- *lemma* category_theory.subobject.lower_comm
- \- *def* category_theory.subobject.lower_equivalence
- \- *lemma* category_theory.subobject.lower_iso
- \- *def* category_theory.subobject.lower₂
- \- *def* category_theory.subobject.map
- \- *lemma* category_theory.subobject.map_bot
- \- *lemma* category_theory.subobject.map_comp
- \- *lemma* category_theory.subobject.map_id
- \- *def* category_theory.subobject.map_iso
- \- *def* category_theory.subobject.map_iso_to_order_iso
- \- *lemma* category_theory.subobject.map_iso_to_order_iso_apply
- \- *lemma* category_theory.subobject.map_iso_to_order_iso_symm_apply
- \- *lemma* category_theory.subobject.map_pullback
- \- *def* category_theory.subobject.map_pullback_adj
- \- *lemma* category_theory.subobject.map_top
- \- *abbreviation* category_theory.subobject.mk
- \- *lemma* category_theory.subobject.prod_eq_inf
- \- *def* category_theory.subobject.pullback
- \- *lemma* category_theory.subobject.pullback_comp
- \- *lemma* category_theory.subobject.pullback_id
- \- *lemma* category_theory.subobject.pullback_map_self
- \- *lemma* category_theory.subobject.pullback_self
- \- *lemma* category_theory.subobject.pullback_top
- \- *def* category_theory.subobject.representative
- \- *lemma* category_theory.subobject.representative_arrow
- \- *lemma* category_theory.subobject.representative_coe
- \- *def* category_theory.subobject.representative_iso
- \- *def* category_theory.subobject.sup
- \- *lemma* category_theory.subobject.sup_factors_of_factors_left
- \- *lemma* category_theory.subobject.sup_factors_of_factors_right
- \- *def* category_theory.subobject.top_coe_iso_self
- \- *lemma* category_theory.subobject.top_eq_id
- \- *lemma* category_theory.subobject.top_factors
- \- *def* category_theory.subobject.underlying
- \- *lemma* category_theory.subobject.underlying_arrow
- \- *lemma* category_theory.subobject.underlying_as_coe
- \- *def* category_theory.subobject.underlying_iso
- \- *lemma* category_theory.subobject.underlying_iso_arrow
- \- *lemma* category_theory.subobject.underlying_iso_id_eq_top_coe_iso_self
- \- *lemma* category_theory.subobject.underlying_iso_inv_top_arrow
- \- *def* category_theory.subobject.«exists»
- \- *def* category_theory.subobject

Added src/category_theory/subobject/basic.lean
- \+ *def* category_theory.subobject.arrow
- \+ *lemma* category_theory.subobject.eq_of_comp_arrow_eq
- \+ *lemma* category_theory.subobject.exists_iso_map
- \+ *def* category_theory.subobject.exists_pullback_adj
- \+ *lemma* category_theory.subobject.le_of_comm
- \+ *def* category_theory.subobject.lower
- \+ *def* category_theory.subobject.lower_adjunction
- \+ *lemma* category_theory.subobject.lower_comm
- \+ *def* category_theory.subobject.lower_equivalence
- \+ *lemma* category_theory.subobject.lower_iso
- \+ *def* category_theory.subobject.lower₂
- \+ *def* category_theory.subobject.map
- \+ *lemma* category_theory.subobject.map_comp
- \+ *lemma* category_theory.subobject.map_id
- \+ *def* category_theory.subobject.map_iso
- \+ *def* category_theory.subobject.map_iso_to_order_iso
- \+ *lemma* category_theory.subobject.map_iso_to_order_iso_apply
- \+ *lemma* category_theory.subobject.map_iso_to_order_iso_symm_apply
- \+ *lemma* category_theory.subobject.map_pullback
- \+ *def* category_theory.subobject.map_pullback_adj
- \+ *abbreviation* category_theory.subobject.mk
- \+ *def* category_theory.subobject.pullback
- \+ *lemma* category_theory.subobject.pullback_comp
- \+ *lemma* category_theory.subobject.pullback_id
- \+ *lemma* category_theory.subobject.pullback_map_self
- \+ *def* category_theory.subobject.representative
- \+ *lemma* category_theory.subobject.representative_arrow
- \+ *lemma* category_theory.subobject.representative_coe
- \+ *def* category_theory.subobject.representative_iso
- \+ *def* category_theory.subobject.underlying
- \+ *lemma* category_theory.subobject.underlying_arrow
- \+ *lemma* category_theory.subobject.underlying_as_coe
- \+ *def* category_theory.subobject.underlying_iso
- \+ *lemma* category_theory.subobject.underlying_iso_arrow
- \+ *def* category_theory.subobject.«exists»
- \+ *def* category_theory.subobject

Added src/category_theory/subobject/default.lean


Added src/category_theory/subobject/factor_thru.lean
- \+ *def* category_theory.limits.equalizer_subobject
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow'
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow
- \+ *lemma* category_theory.limits.equalizer_subobject_arrow_comp
- \+ *lemma* category_theory.limits.equalizer_subobject_factors
- \+ *lemma* category_theory.limits.equalizer_subobject_factors_iff
- \+ *def* category_theory.limits.equalizer_subobject_iso
- \+ *def* category_theory.limits.factor_thru_image_subobject
- \+ *def* category_theory.limits.image_subobject
- \+ *lemma* category_theory.limits.image_subobject_arrow'
- \+ *lemma* category_theory.limits.image_subobject_arrow
- \+ *lemma* category_theory.limits.image_subobject_arrow_comp
- \+ *lemma* category_theory.limits.image_subobject_factors
- \+ *def* category_theory.limits.image_subobject_iso
- \+ *lemma* category_theory.limits.image_subobject_le
- \+ *def* category_theory.limits.kernel_subobject
- \+ *lemma* category_theory.limits.kernel_subobject_arrow'
- \+ *lemma* category_theory.limits.kernel_subobject_arrow
- \+ *lemma* category_theory.limits.kernel_subobject_arrow_comp
- \+ *lemma* category_theory.limits.kernel_subobject_factors
- \+ *lemma* category_theory.limits.kernel_subobject_factors_iff
- \+ *def* category_theory.limits.kernel_subobject_iso
- \+ *def* category_theory.mono_over.factor_thru
- \+ *def* category_theory.mono_over.factors
- \+ *def* category_theory.subobject.factor_thru
- \+ *lemma* category_theory.subobject.factor_thru_arrow
- \+ *lemma* category_theory.subobject.factor_thru_eq_zero
- \+ *lemma* category_theory.subobject.factor_thru_right
- \+ *def* category_theory.subobject.factors
- \+ *lemma* category_theory.subobject.factors_comp_arrow
- \+ *lemma* category_theory.subobject.factors_iff
- \+ *lemma* category_theory.subobject.factors_of_factors_right
- \+ *lemma* category_theory.subobject.factors_of_le

Added src/category_theory/subobject/lattice.lean
- \+ *lemma* category_theory.mono_over.bot_arrow
- \+ *def* category_theory.mono_over.bot_le
- \+ *lemma* category_theory.mono_over.bot_left
- \+ *def* category_theory.mono_over.inf
- \+ *def* category_theory.mono_over.inf_le_left
- \+ *def* category_theory.mono_over.inf_le_right
- \+ *def* category_theory.mono_over.le_inf
- \+ *def* category_theory.mono_over.le_sup_left
- \+ *def* category_theory.mono_over.le_sup_right
- \+ *def* category_theory.mono_over.le_top
- \+ *def* category_theory.mono_over.map_bot
- \+ *def* category_theory.mono_over.map_top
- \+ *def* category_theory.mono_over.pullback_self
- \+ *def* category_theory.mono_over.pullback_top
- \+ *def* category_theory.mono_over.sup
- \+ *def* category_theory.mono_over.sup_le
- \+ *lemma* category_theory.mono_over.top_arrow
- \+ *def* category_theory.mono_over.top_le_pullback_self
- \+ *lemma* category_theory.mono_over.top_left
- \+ *lemma* category_theory.subobject.bot_arrow
- \+ *def* category_theory.subobject.bot_coe_iso_zero
- \+ *lemma* category_theory.subobject.bot_eq_zero
- \+ *lemma* category_theory.subobject.bot_factors_iff_zero
- \+ *lemma* category_theory.subobject.factors_left_of_inf_factors
- \+ *lemma* category_theory.subobject.factors_right_of_inf_factors
- \+ *lemma* category_theory.subobject.finset_inf_arrow_factors
- \+ *lemma* category_theory.subobject.finset_inf_factors
- \+ *lemma* category_theory.subobject.finset_sup_factors
- \+ *def* category_theory.subobject.functor
- \+ *def* category_theory.subobject.inf
- \+ *lemma* category_theory.subobject.inf_arrow_factors_left
- \+ *lemma* category_theory.subobject.inf_arrow_factors_right
- \+ *lemma* category_theory.subobject.inf_def
- \+ *lemma* category_theory.subobject.inf_eq_map_pullback'
- \+ *lemma* category_theory.subobject.inf_eq_map_pullback
- \+ *lemma* category_theory.subobject.inf_factors
- \+ *lemma* category_theory.subobject.inf_le_left
- \+ *lemma* category_theory.subobject.inf_le_right
- \+ *lemma* category_theory.subobject.inf_map
- \+ *lemma* category_theory.subobject.inf_pullback
- \+ *lemma* category_theory.subobject.le_inf
- \+ *lemma* category_theory.subobject.map_bot
- \+ *lemma* category_theory.subobject.map_top
- \+ *lemma* category_theory.subobject.prod_eq_inf
- \+ *lemma* category_theory.subobject.pullback_self
- \+ *lemma* category_theory.subobject.pullback_top
- \+ *def* category_theory.subobject.sup
- \+ *lemma* category_theory.subobject.sup_factors_of_factors_left
- \+ *lemma* category_theory.subobject.sup_factors_of_factors_right
- \+ *def* category_theory.subobject.top_coe_iso_self
- \+ *lemma* category_theory.subobject.top_eq_id
- \+ *lemma* category_theory.subobject.top_factors
- \+ *lemma* category_theory.subobject.underlying_iso_id_eq_top_coe_iso_self
- \+ *lemma* category_theory.subobject.underlying_iso_inv_top_arrow

Added src/category_theory/subobject/mono_over.lean
- \+ *abbreviation* category_theory.mono_over.arrow
- \+ *def* category_theory.mono_over.exists_iso_map
- \+ *def* category_theory.mono_over.exists_pullback_adj
- \+ *def* category_theory.mono_over.forget
- \+ *def* category_theory.mono_over.forget_image
- \+ *lemma* category_theory.mono_over.forget_obj_hom
- \+ *lemma* category_theory.mono_over.forget_obj_left
- \+ *abbreviation* category_theory.mono_over.hom_mk
- \+ *def* category_theory.mono_over.image
- \+ *def* category_theory.mono_over.image_forget_adj
- \+ *def* category_theory.mono_over.image_mono_over
- \+ *lemma* category_theory.mono_over.image_mono_over_arrow
- \+ *def* category_theory.mono_over.iso_mk
- \+ *def* category_theory.mono_over.lift
- \+ *lemma* category_theory.mono_over.lift_comm
- \+ *def* category_theory.mono_over.lift_comp
- \+ *def* category_theory.mono_over.lift_id
- \+ *def* category_theory.mono_over.lift_iso
- \+ *def* category_theory.mono_over.map
- \+ *def* category_theory.mono_over.map_comp
- \+ *def* category_theory.mono_over.map_id
- \+ *def* category_theory.mono_over.map_iso
- \+ *lemma* category_theory.mono_over.map_obj_arrow
- \+ *lemma* category_theory.mono_over.map_obj_left
- \+ *def* category_theory.mono_over.map_pullback_adj
- \+ *def* category_theory.mono_over.mk'
- \+ *lemma* category_theory.mono_over.mk'_arrow
- \+ *def* category_theory.mono_over.pullback
- \+ *def* category_theory.mono_over.pullback_comp
- \+ *def* category_theory.mono_over.pullback_id
- \+ *def* category_theory.mono_over.pullback_map_self
- \+ *lemma* category_theory.mono_over.pullback_obj_arrow
- \+ *lemma* category_theory.mono_over.pullback_obj_left
- \+ *def* category_theory.mono_over.slice
- \+ *lemma* category_theory.mono_over.w
- \+ *def* category_theory.mono_over.«exists»
- \+ *def* category_theory.mono_over

Modified src/category_theory/subterminal.lean




## [2021-03-21 11:05:45](https://github.com/leanprover-community/mathlib/commit/5d67033)
feat(topology/algebra/continuous_functions): missing lemmas ([#6782](https://github.com/leanprover-community/mathlib/pull/6782))
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean
- \+ *lemma* algebra_map_apply
- \+ *lemma* continuous_map.C_apply
- \+ *lemma* continuous_map.div_comp
- \+ *lemma* continuous_map.inv_comp
- \+ *lemma* continuous_map.mul_comp
- \+ *lemma* continuous_map.pow_comp
- \+ *lemma* continuous_map.smul_comp
- \+ *lemma* inv_coe
- \+ *lemma* pow_coe



## [2021-03-21 03:36:01](https://github.com/leanprover-community/mathlib/commit/a22df99)
chore(scripts): update nolints.txt ([#6793](https://github.com/leanprover-community/mathlib/pull/6793))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-21 03:36:00](https://github.com/leanprover-community/mathlib/commit/f331648)
feat(analysis/normed_space): normed_algebra.to_topological_algebra ([#6779](https://github.com/leanprover-community/mathlib/pull/6779))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* add_monoid_hom.continuous_of_bound
- \+ *lemma* normed_algebra.algebra_map_continuous



## [2021-03-21 03:35:59](https://github.com/leanprover-community/mathlib/commit/abfddbf)
feat(ring_theory): define `left_mul_matrix` and `algebra.trace` ([#6653](https://github.com/leanprover-community/mathlib/pull/6653))
This PR defines the algebra trace, and the bilinear trace form, for an algebra `S` over a ring `R`, for example a field extension `L / K`.
Follow-up PRs will prove that `algebra.trace K L x` is the sum of the conjugate roots of `x` in `L`, that `trace_form` is nondegenerate and that `trace K L x` is integral over `K`. Then we'll use this to find an integral basis for field extensions, and then we can prove that the integral closure of a Dedekind domain is again a Dedekind domain.
#### Estimated changes
Modified src/algebra/algebra/tower.lean
- \+ *lemma* algebra.lmul_algebra_map

Modified src/algebra/lie/matrix.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_eq_zero_of_not_exists_basis

Modified src/linear_algebra/matrix.lean
- \+ *lemma* algebra.left_mul_matrix_apply
- \+ *lemma* algebra.left_mul_matrix_eq_repr_mul
- \+ *lemma* algebra.left_mul_matrix_injective
- \+ *lemma* algebra.left_mul_matrix_mul_vec_repr
- \+ *lemma* algebra.smul_left_mul_matrix
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map_eq
- \+ *lemma* algebra.smul_left_mul_matrix_algebra_map_ne
- \+ *lemma* algebra.to_matrix_lmul'
- \+ *lemma* algebra.to_matrix_lmul_eq
- \+ *lemma* algebra.to_matrix_lsmul
- \+ *lemma* linear_map.to_matrix_mul_vec_repr
- \+ *lemma* linear_map.to_matrix_one
- \+/\- *lemma* linear_map.trace_aux_def
- \+ *lemma* matrix.ker_to_lin_eq_bot
- \+ *lemma* matrix.range_to_lin_eq_top
- \+ *def* matrix.to_linear_equiv'
- \+ *lemma* matrix.to_linear_equiv'_apply
- \+ *lemma* matrix.to_linear_equiv'_symm_apply
- \+/\- *def* matrix.to_linear_equiv
- \- *lemma* matrix.to_linear_equiv_apply
- \- *lemma* matrix.to_linear_equiv_symm_apply
- \+ *lemma* matrix.trace_apply

Added src/ring_theory/trace.lean
- \+ *lemma* algebra.trace_algebra_map
- \+ *lemma* algebra.trace_algebra_map_of_basis
- \+ *lemma* algebra.trace_eq_matrix_trace
- \+ *lemma* algebra.trace_eq_zero_of_not_exists_basis
- \+ *lemma* algebra.trace_form_apply
- \+ *lemma* algebra.trace_form_is_sym
- \+ *lemma* algebra.trace_form_to_matrix
- \+ *lemma* algebra.trace_form_to_matrix_power_basis



## [2021-03-21 03:35:58](https://github.com/leanprover-community/mathlib/commit/b75ec5c)
feat(data/polynomial): Bernstein polynomials ([#6465](https://github.com/leanprover-community/mathlib/pull/6465))
The definition of the Bernstein polynomials
`bernstein_polynomial (R : Type*) [ring R] (n ν : ℕ) : polynomial R := (choose n ν) * X^ν * (1 - X)^(n - ν)`
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.
(Future work: use these to prove Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* mul_neg_one_pow_eq_zero_iff
- \+ *lemma* neg_one_pow_mul_eq_zero_iff

Modified src/data/fin.lean
- \+ *lemma* fin.init_def
- \+ *lemma* fin.tail_def

Modified src/data/int/basic.lean
- \+ *lemma* int.neg_one_pow_ne_zero

Modified src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.derivative_comp_one_sub_X
- \+ *lemma* polynomial.iterate_derivative_comp_one_sub_X

Modified src/linear_algebra/multilinear.lean


Modified src/number_theory/quadratic_reciprocity.lean


Added src/ring_theory/polynomial/bernstein.lean
- \+ *lemma* bernstein_polynomial.derivative_succ
- \+ *lemma* bernstein_polynomial.derivative_succ_aux
- \+ *lemma* bernstein_polynomial.derivative_zero
- \+ *lemma* bernstein_polynomial.eq_zero_of_lt
- \+ *lemma* bernstein_polynomial.eval_at_0
- \+ *lemma* bernstein_polynomial.eval_at_1
- \+ *lemma* bernstein_polynomial.flip'
- \+ *lemma* bernstein_polynomial.flip
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_0
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_0_aux₁
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_0_aux₂
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_0_eq_zero_of_lt
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_0_ne_zero
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_1
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_1_eq_zero_of_lt
- \+ *lemma* bernstein_polynomial.iterate_derivative_at_1_ne_zero
- \+ *lemma* bernstein_polynomial.iterate_derivative_succ_at_0_eq_zero
- \+ *lemma* bernstein_polynomial.linear_independent
- \+ *lemma* bernstein_polynomial.linear_independent_aux
- \+ *lemma* bernstein_polynomial.map
- \+ *def* bernstein_polynomial



## [2021-03-21 03:35:57](https://github.com/leanprover-community/mathlib/commit/4cc4207)
feat(algebra/module/linear_map): Add linear_map.iterate ([#6377](https://github.com/leanprover-community/mathlib/pull/6377))
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *theorem* linear_map.comp_id
- \+ *theorem* linear_map.id_comp

Modified src/linear_algebra/basic.lean
- \- *theorem* linear_map.comp_id
- \- *theorem* linear_map.id_comp
- \+ *lemma* linear_map.injective_of_iterate_injective
- \+ *lemma* linear_map.iterate_bijective
- \+ *lemma* linear_map.iterate_injective
- \+ *lemma* linear_map.iterate_succ
- \+ *lemma* linear_map.iterate_surjective



## [2021-03-20 23:19:57](https://github.com/leanprover-community/mathlib/commit/e20c730)
feat(topology/continuous_map): formulas for sup and inf in terms of abs ([#6720](https://github.com/leanprover-community/mathlib/pull/6720))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* sub_le_sub_flip

Modified src/topology/algebra/continuous_functions.lean
- \+ *lemma* continuous_map.inf_eq
- \+ *lemma* continuous_map.sup_eq
- \+ *lemma* div_coe
- \+ *lemma* max_eq_half_add_add_abs_sub
- \+ *lemma* min_eq_half_add_sub_abs_sub

Modified src/topology/continuous_map.lean
- \+ *def* continuous_map.abs
- \+ *lemma* continuous_map.abs_apply



## [2021-03-20 21:36:26](https://github.com/leanprover-community/mathlib/commit/3153153)
feat(measure_theory/interval_integral): add `integral_comp_mul_left` ([#6787](https://github.com/leanprover-community/mathlib/pull/6787))
I need this lemma for my work toward making integrals computable by `norm_num`.
#### Estimated changes
Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integral.integral_comp_add_right
- \+ *lemma* interval_integral.integral_comp_mul_left
- \+/\- *lemma* interval_integral.integral_comp_mul_right
- \+/\- *lemma* interval_integral.integral_comp_neg



## [2021-03-20 19:58:20](https://github.com/leanprover-community/mathlib/commit/240836a)
feat(analysis/normed_space/basic): generalize submodule.normed_space ([#6766](https://github.com/leanprover-community/mathlib/pull/6766))
This means that a ℂ-submodule of an ℝ-normed space is still an ℝ-normed space.
There's too much randomness in the profiling for me to tell if this speeds up or slows down `exists_extension_norm_eq`; but it does at least save a line there.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/hahn_banach.lean




## [2021-03-20 17:42:10](https://github.com/leanprover-community/mathlib/commit/d650674)
feat(category_theory/subterminal): subterminal category equiv subobjects of terminal ([#6755](https://github.com/leanprover-community/mathlib/pull/6755))
#### Estimated changes
Modified src/category_theory/subterminal.lean
- \+ *lemma* category_theory.mono_over_terminal_to_subterminals_comp
- \+ *def* category_theory.subterminals_equiv_mono_over_terminal
- \+ *lemma* category_theory.subterminals_to_mono_over_terminal_comp_forget



## [2021-03-20 16:28:06](https://github.com/leanprover-community/mathlib/commit/86b8f39)
doc(docs/overview): Update overview ([#6772](https://github.com/leanprover-community/mathlib/pull/6772))
Update the overview to mention Abel-Ruffini.
#### Estimated changes
Modified docs/overview.yaml




## [2021-03-20 16:28:05](https://github.com/leanprover-community/mathlib/commit/5d7efa0)
feat(combinatorics/quiver): define quivers ([#6680](https://github.com/leanprover-community/mathlib/pull/6680))
Define quivers (a very permissive notion of graph), subquivers, paths
and arborescences, which are like rooted trees.
This PR comes from https://github.com/dwarn/nielsen-schreier-2 .
#### Estimated changes
Added src/combinatorics/quiver.lean
- \+ *lemma* quiver.empty_arrow
- \+ *def* quiver.labelling
- \+ *lemma* quiver.opposite_arrow
- \+ *lemma* quiver.opposite_opposite
- \+ *def* quiver.path.length
- \+ *inductive* quiver.path
- \+ *lemma* quiver.sum_arrow
- \+ *def* quiver.symmetrify
- \+ *lemma* quiver.symmetrify_arrow
- \+ *def* quiver.wide_subquiver_equiv_set_total
- \+ *def* quiver.wide_subquiver_symmetrify
- \+ *structure* quiver
- \+ *def* wide_subquiver.quiver
- \+ *def* wide_subquiver



## [2021-03-20 15:04:09](https://github.com/leanprover-community/mathlib/commit/df4c9c9)
chore(ring_theory/adjoin/basic): golf some proofs about algebra.adjoin ([#6784](https://github.com/leanprover-community/mathlib/pull/6784))
#### Estimated changes
Modified src/ring_theory/adjoin/basic.lean




## [2021-03-20 13:24:55](https://github.com/leanprover-community/mathlib/commit/9f77db2)
chore(topology/metric_space): add '@[continuity]' attributes ([#6780](https://github.com/leanprover-community/mathlib/pull/6780))
#### Estimated changes
Modified src/topology/metric_space/basic.lean




## [2021-03-20 10:08:03](https://github.com/leanprover-community/mathlib/commit/695d7f4)
refactor(algebraic_topology/simplex_category): Make simplex_category universe polymorphic. ([#6761](https://github.com/leanprover-community/mathlib/pull/6761))
This PR changes the definition of `simplex_category` so that it becomes universe polymorphic.
This is useful when we want to take (co)limits of simplicial objects indexed by categories constructed out of `simplex_category`.
This PR also makes a small wrapper around morphisms in `simplex_category` for hygiene purposes, and introduces a notation `X _[n]` for the n-th term of a simplicial object X.
Note: this PR makes `simplex_category` and `simplex_category.hom` irreducible.
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \- *lemma* simplex_category.comp_apply
- \+ *lemma* simplex_category.ext
- \+ *def* simplex_category.hom.comp
- \+ *lemma* simplex_category.hom.ext
- \+ *def* simplex_category.hom.id
- \+ *def* simplex_category.hom.mk
- \+ *lemma* simplex_category.hom.mk_to_preorder_hom
- \+ *lemma* simplex_category.hom.mk_to_preorder_hom_apply
- \+ *def* simplex_category.hom.to_preorder_hom
- \+ *lemma* simplex_category.hom.to_preorder_hom_mk
- \- *lemma* simplex_category.id_apply
- \+/\- *def* simplex_category.is_skeleton_of
- \+/\- *def* simplex_category.len
- \+/\- *def* simplex_category.mk
- \+ *def* simplex_category.mk_hom
- \+/\- *lemma* simplex_category.mk_len
- \+/\- *def* simplex_category.skeletal_functor
- \+/\- *def* simplex_category.σ
- \+/\- *def* simplex_category

Modified src/algebraic_topology/simplicial_object.lean
- \+/\- *def* category_theory.simplicial_object.eq_to_iso
- \+/\- *def* category_theory.simplicial_object.truncated
- \+/\- *def* category_theory.simplicial_object.δ
- \+/\- *def* category_theory.simplicial_object.σ
- \+/\- *def* category_theory.simplicial_object

Modified src/algebraic_topology/simplicial_set.lean




## [2021-03-20 10:08:02](https://github.com/leanprover-community/mathlib/commit/4db82a4)
refactor(category_theory/cones): golf and cleanup cones ([#6756](https://github.com/leanprover-community/mathlib/pull/6756))
No mathematical content here, basically just golfing and tidying in preparation for future PRs.
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.functor.cones
- \+/\- *def* category_theory.limits.cocone.extend
- \- *lemma* category_theory.limits.cocone.extend_ι
- \+/\- *def* category_theory.limits.cocone.extensions
- \+/\- *def* category_theory.limits.cocone.whisker
- \+/\- *def* category_theory.limits.cocones.equivalence_of_reindexing
- \+/\- *def* category_theory.limits.cocones.whiskering
- \+/\- *def* category_theory.limits.cocones.whiskering_equivalence
- \+/\- *def* category_theory.limits.cone.extend
- \- *lemma* category_theory.limits.cone.extend_π
- \+/\- *def* category_theory.limits.cone.extensions
- \+/\- *def* category_theory.limits.cone.whisker
- \+/\- *def* category_theory.limits.cones.equivalence_of_reindexing
- \+/\- *def* category_theory.limits.cones.whiskering
- \+/\- *def* category_theory.limits.cones.whiskering_equivalence

Modified src/category_theory/limits/is_limit.lean




## [2021-03-20 10:08:00](https://github.com/leanprover-community/mathlib/commit/56e5aa7)
feat(category_theory/closed): currying rfl lemmas ([#6754](https://github.com/leanprover-community/mathlib/pull/6754))
Add `rfl` lemmas for currying
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* category_theory.cartesian_closed.hom_equiv_apply_eq
- \+ *lemma* category_theory.cartesian_closed.hom_equiv_symm_apply_eq



## [2021-03-20 09:08:36](https://github.com/leanprover-community/mathlib/commit/b0150a5)
fix(analysis/special_functions/integrals): move lemmas out of namespace ([#6778](https://github.com/leanprover-community/mathlib/pull/6778))
Some lemmas should not have been moved into a namespace, so I fix that here.
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos
- \+ *lemma* integral_exp
- \+ *lemma* integral_id
- \+ *lemma* integral_inv
- \+ *lemma* integral_inv_of_neg
- \+ *lemma* integral_inv_of_pos
- \+ *lemma* integral_inv_one_add_sq
- \+ *lemma* integral_one
- \+ *lemma* integral_one_div
- \+ *lemma* integral_one_div_of_neg
- \+ *lemma* integral_one_div_of_pos
- \+ *lemma* integral_one_div_one_add_sq
- \+ *lemma* integral_pow
- \+ *lemma* integral_sin
- \+ *lemma* integral_sin_pow_aux
- \+ *theorem* integral_sin_pow_even
- \+ *theorem* integral_sin_pow_odd
- \+ *lemma* integral_sin_pow_pos
- \+ *lemma* integral_sin_pow_succ_succ
- \- *lemma* interval_integral.integral_cos
- \- *lemma* interval_integral.integral_exp
- \- *lemma* interval_integral.integral_id
- \- *lemma* interval_integral.integral_inv
- \- *lemma* interval_integral.integral_inv_of_neg
- \- *lemma* interval_integral.integral_inv_of_pos
- \- *lemma* interval_integral.integral_inv_one_add_sq
- \- *lemma* interval_integral.integral_one
- \- *lemma* interval_integral.integral_one_div
- \- *lemma* interval_integral.integral_one_div_of_neg
- \- *lemma* interval_integral.integral_one_div_of_pos
- \- *lemma* interval_integral.integral_one_div_one_add_sq
- \- *lemma* interval_integral.integral_pow
- \- *lemma* interval_integral.integral_sin
- \- *lemma* interval_integral.integral_sin_pow_aux
- \- *theorem* interval_integral.integral_sin_pow_even
- \- *theorem* interval_integral.integral_sin_pow_odd
- \- *lemma* interval_integral.integral_sin_pow_pos
- \- *lemma* interval_integral.integral_sin_pow_succ_succ



## [2021-03-20 03:08:13](https://github.com/leanprover-community/mathlib/commit/26fcfbc)
feat(topology): continuous_pi_iff pi.has_continuous_mul pi.topological_group ([#6689](https://github.com/leanprover-community/mathlib/pull/6689))
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous_pi_iff



## [2021-03-20 01:57:36](https://github.com/leanprover-community/mathlib/commit/07282da)
chore(scripts): update nolints.txt ([#6776](https://github.com/leanprover-community/mathlib/pull/6776))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-19 22:17:14](https://github.com/leanprover-community/mathlib/commit/b4a2991)
feat(dynamics/ergodic): define measure preserving maps ([#6764](https://github.com/leanprover-community/mathlib/pull/6764))
Also prove some missing lemmas about measures.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.preimage_prod_map_prod

Added src/dynamics/ergodic/measure_preserving.lean
- \+ *lemma* measure_theory.measure_preserving.comp
- \+ *lemma* measure_theory.measure_preserving.measure_preimage
- \+ *lemma* measure_theory.measure_preserving.prod
- \+ *lemma* measure_theory.measure_preserving.skew_product
- \+ *structure* measure_theory.measure_preserving

Modified src/measure_theory/giry_monad.lean
- \+ *lemma* measure_theory.measure.bind_zero_left
- \+ *lemma* measure_theory.measure.bind_zero_right'
- \+ *lemma* measure_theory.measure.bind_zero_right
- \+ *lemma* measure_theory.measure.join_zero

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.prod_map

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_ne_bot
- \+ *lemma* measure_theory.sigma_finite.of_map

Modified src/measure_theory/prod.lean
- \+ *lemma* measure_theory.measure.map_prod_map
- \+ *lemma* measure_theory.measure.prod_zero
- \+ *lemma* measure_theory.measure.zero_prod



## [2021-03-19 22:17:13](https://github.com/leanprover-community/mathlib/commit/eba4829)
feat(data/real/pi): Wallis product for pi ([#6568](https://github.com/leanprover-community/mathlib/pull/6568))
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \- *lemma* integral_cos
- \- *lemma* integral_exp
- \- *lemma* integral_id
- \- *lemma* integral_inv
- \- *lemma* integral_inv_of_neg
- \- *lemma* integral_inv_of_pos
- \- *lemma* integral_inv_one_add_sq
- \- *lemma* integral_one
- \- *lemma* integral_one_div
- \- *lemma* integral_one_div_of_neg
- \- *lemma* integral_one_div_of_pos
- \- *lemma* integral_one_div_one_add_sq
- \- *lemma* integral_pow
- \- *lemma* integral_sin
- \+ *lemma* interval_integral.integral_cos
- \+ *lemma* interval_integral.integral_exp
- \+ *lemma* interval_integral.integral_id
- \+ *lemma* interval_integral.integral_inv
- \+ *lemma* interval_integral.integral_inv_of_neg
- \+ *lemma* interval_integral.integral_inv_of_pos
- \+ *lemma* interval_integral.integral_inv_one_add_sq
- \+ *lemma* interval_integral.integral_one
- \+ *lemma* interval_integral.integral_one_div
- \+ *lemma* interval_integral.integral_one_div_of_neg
- \+ *lemma* interval_integral.integral_one_div_of_pos
- \+ *lemma* interval_integral.integral_one_div_one_add_sq
- \+ *lemma* interval_integral.integral_pow
- \+ *lemma* interval_integral.integral_sin
- \+ *lemma* interval_integral.integral_sin_pow_aux
- \+ *theorem* interval_integral.integral_sin_pow_even
- \+ *theorem* interval_integral.integral_sin_pow_odd
- \+ *lemma* interval_integral.integral_sin_pow_pos
- \+ *lemma* interval_integral.integral_sin_pow_succ_succ

Modified src/data/real/pi.lean
- \+ *lemma* real.integral_sin_pow_antimono
- \+ *lemma* real.integral_sin_pow_div_tendsto_one
- \+ *theorem* real.tendsto_prod_pi_div_two



## [2021-03-19 19:07:52](https://github.com/leanprover-community/mathlib/commit/c65146d)
chore(data/finset/basic): erase_inj_on ([#6769](https://github.com/leanprover-community/mathlib/pull/6769))
Quick follow-up to [#6737](https://github.com/leanprover-community/mathlib/pull/6737)
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_inj_on



## [2021-03-19 19:07:51](https://github.com/leanprover-community/mathlib/commit/2d2929f)
feat(measure_theory): define Hausdorff measure and Hausdorff dimension ([#6710](https://github.com/leanprover-community/mathlib/pull/6710))
#### Estimated changes
Modified docs/references.bib


Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.rpow_sub

Modified src/measure_theory/borel_space.lean
- \+ *lemma* borel_eq_generate_from_is_closed

Added src/measure_theory/hausdorff_measure.lean
- \+ *def* measure_theory.dimH
- \+ *lemma* measure_theory.hausdorff_measure_of_dimH_lt
- \+ *lemma* measure_theory.hausdorff_measure_of_lt_dimH
- \+ *def* measure_theory.measure.hausdorff_measure
- \+ *lemma* measure_theory.measure.hausdorff_measure_apply'
- \+ *lemma* measure_theory.measure.hausdorff_measure_apply
- \+ *lemma* measure_theory.measure.hausdorff_measure_mono
- \+ *lemma* measure_theory.measure.hausdorff_measure_zero_or_top
- \+ *def* measure_theory.measure.mk_metric'
- \+ *lemma* measure_theory.measure.mk_metric'_to_outer_measure
- \+ *def* measure_theory.measure.mk_metric
- \+ *lemma* measure_theory.measure.mk_metric_apply
- \+ *lemma* measure_theory.measure.mk_metric_mono
- \+ *lemma* measure_theory.measure.mk_metric_mono_smul
- \+ *lemma* measure_theory.measure.mk_metric_to_outer_measure
- \+ *lemma* measure_theory.measure_zero_of_dimH_lt
- \+ *lemma* measure_theory.outer_measure.coe_mk_metric
- \+ *lemma* measure_theory.outer_measure.is_metric.borel_le_caratheodory
- \+ *lemma* measure_theory.outer_measure.is_metric.finset_Union_of_pairwise_separated
- \+ *lemma* measure_theory.outer_measure.is_metric.le_caratheodory
- \+ *def* measure_theory.outer_measure.is_metric
- \+ *lemma* measure_theory.outer_measure.isometric_comap_mk_metric
- \+ *lemma* measure_theory.outer_measure.isometric_map_mk_metric
- \+ *lemma* measure_theory.outer_measure.isometry_comap_mk_metric
- \+ *lemma* measure_theory.outer_measure.isometry_map_mk_metric
- \+ *lemma* measure_theory.outer_measure.mk_metric'.eq_supr_nat
- \+ *lemma* measure_theory.outer_measure.mk_metric'.le_pre
- \+ *lemma* measure_theory.outer_measure.mk_metric'.mono_pre
- \+ *lemma* measure_theory.outer_measure.mk_metric'.mono_pre_nat
- \+ *def* measure_theory.outer_measure.mk_metric'.pre
- \+ *lemma* measure_theory.outer_measure.mk_metric'.pre_le
- \+ *lemma* measure_theory.outer_measure.mk_metric'.tendsto_pre
- \+ *lemma* measure_theory.outer_measure.mk_metric'.tendsto_pre_nat
- \+ *lemma* measure_theory.outer_measure.mk_metric'.trim_pre
- \+ *def* measure_theory.outer_measure.mk_metric'
- \+ *lemma* measure_theory.outer_measure.mk_metric'_is_metric
- \+ *def* measure_theory.outer_measure.mk_metric
- \+ *lemma* measure_theory.outer_measure.mk_metric_mono
- \+ *lemma* measure_theory.outer_measure.mk_metric_mono_smul
- \+ *lemma* measure_theory.outer_measure.trim_mk_metric

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.bounded_by_union_of_top_of_nonempty_inter
- \+ *lemma* measure_theory.outer_measure.comap_bounded_by
- \+ *lemma* measure_theory.outer_measure.smul_bounded_by

Modified src/topology/separation.lean
- \+ *lemma* tendsto_nhds_unique_of_eventually_eq



## [2021-03-19 17:15:52](https://github.com/leanprover-community/mathlib/commit/152412f)
feat(analysis/special_functions/exp_log): log_nonzero_of_ne_one and log_inj_pos ([#6734](https://github.com/leanprover-community/mathlib/pull/6734))
log_nonzero_of_ne_one and log_inj_pos
Proves : 
 * When `x > 0`, `log(x)` is `0` iff `x = 1`
 * The real logarithm is injective (when restraining the domain to the positive reals)
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.eq_one_of_pos_of_log_eq_zero
- \+ *lemma* real.log_inj_on_pos
- \+ *lemma* real.log_ne_zero_of_pos_of_ne_one



## [2021-03-19 17:15:51](https://github.com/leanprover-community/mathlib/commit/6f3e0ad)
feat(ring_theory/multiplicity): Multiplicity with units ([#6729](https://github.com/leanprover-community/mathlib/pull/6729))
Renames `multiplicity.multiplicity_unit` into `multiplicity.is_unit_left`.
Adds : 
 * `multiplicity.is_unit_right`
 * `multiplicity.unit_left`
 * `multiplicity.unit_right`
#### Estimated changes
Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.is_unit_left
- \+ *lemma* multiplicity.is_unit_right
- \- *lemma* multiplicity.multiplicity_unit
- \+/\- *lemma* multiplicity.one_left
- \+/\- *lemma* multiplicity.one_right
- \+ *lemma* multiplicity.unit_left
- \+ *lemma* multiplicity.unit_right



## [2021-03-19 14:35:20](https://github.com/leanprover-community/mathlib/commit/591c34b)
refactor(linear_algebra/basic): move the lattice structure to its own file ([#6767](https://github.com/leanprover-community/mathlib/pull/6767))
The entire lattice structure is thoroughly uninteresting.
By moving it to its own shorter file, it should be easier to unify with the lattice of `submonoid`
I'd hope in future we can generate this automatically for any `subobject A` with an injection into `set A`.
#### Estimated changes
Added src/algebra/module/submodule_lattice.lean
- \+ *theorem* submodule.Inf_coe
- \+ *lemma* submodule.bot_coe
- \+ *lemma* submodule.bot_to_add_submonoid
- \+ *lemma* submodule.coe_subset_coe
- \+ *lemma* submodule.eq_top_iff'
- \+ *lemma* submodule.exists_of_lt
- \+ *theorem* submodule.inf_coe
- \+ *theorem* submodule.infi_coe
- \+ *lemma* submodule.le_def'
- \+ *lemma* submodule.le_def
- \+ *lemma* submodule.lt_def
- \+ *lemma* submodule.lt_iff_le_and_exists
- \+ *lemma* submodule.mem_Inf
- \+ *lemma* submodule.mem_Sup_of_mem
- \+ *lemma* submodule.mem_bot
- \+ *theorem* submodule.mem_inf
- \+ *theorem* submodule.mem_infi
- \+ *lemma* submodule.mem_sup_left
- \+ *lemma* submodule.mem_sup_right
- \+ *lemma* submodule.mem_supr_of_mem
- \+ *lemma* submodule.mem_top
- \+ *lemma* submodule.nonzero_mem_of_bot_lt
- \+ *lemma* submodule.not_le_iff_exists
- \+ *lemma* submodule.top_coe
- \+ *lemma* submodule.top_to_add_submonoid

Modified src/linear_algebra/basic.lean
- \- *theorem* submodule.Inf_coe
- \- *lemma* submodule.bot_coe
- \- *lemma* submodule.bot_to_add_submonoid
- \- *lemma* submodule.coe_subset_coe
- \- *lemma* submodule.eq_top_iff'
- \- *lemma* submodule.exists_of_lt
- \- *theorem* submodule.inf_coe
- \- *theorem* submodule.infi_coe
- \- *lemma* submodule.le_def'
- \- *lemma* submodule.le_def
- \- *lemma* submodule.lt_def
- \- *lemma* submodule.lt_iff_le_and_exists
- \- *lemma* submodule.mem_Inf
- \- *lemma* submodule.mem_Sup_of_mem
- \- *lemma* submodule.mem_bot
- \- *theorem* submodule.mem_inf
- \- *theorem* submodule.mem_infi
- \- *lemma* submodule.mem_sup_left
- \- *lemma* submodule.mem_sup_right
- \- *lemma* submodule.mem_supr_of_mem
- \- *lemma* submodule.mem_top
- \- *lemma* submodule.nonzero_mem_of_bot_lt
- \- *lemma* submodule.not_le_iff_exists
- \- *lemma* submodule.top_coe
- \- *lemma* submodule.top_to_add_submonoid



## [2021-03-19 12:51:59](https://github.com/leanprover-community/mathlib/commit/ce107da)
feat(analysis/special_functions/integrals): integrating linear combinations of functions ([#6597](https://github.com/leanprover-community/mathlib/pull/6597))
Together with [#6357](https://github.com/leanprover-community/mathlib/pull/6357), this PR makes it possible to compute integrals of the form `∫ x in a..b, c * f x + d * g x` by `simp` (where `c` and `d` are constants and `f` and `g` are functions that are `interval_integrable` on `interval a b`.
Notably, this allows us to compute the integrals of polynomials by `norm_num`. Here's an example, followed by an example of a more random linear combination of `interval_integrable` functions:
```
import analysis.special_functions.integrals
open interval_integral real
open_locale real
example : ∫ x:ℝ in 0..2, 6*x^5 + 3*x^4 + x^3 - 2*x^2 + x - 7 = 1048 / 15 := by norm_num
example : ∫ x:ℝ in 0..1, exp x + 9 * x^8 + x^3 - x/2 + (1 + x^2)⁻¹ = exp 1 + π/4 := by norm_num
```
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integral.interval_integrable.const_mul
- \+ *lemma* interval_integral.interval_integrable.div
- \+ *lemma* interval_integral.interval_integrable.mul_const
- \+ *lemma* interval_integral.interval_integrable_const
- \+ *lemma* interval_integral.interval_integrable_cos
- \+ *lemma* interval_integral.interval_integrable_exp
- \+ *lemma* interval_integral.interval_integrable_id
- \+ *lemma* interval_integral.interval_integrable_inv
- \+ *lemma* interval_integral.interval_integrable_inv_one_add_sq
- \+ *lemma* interval_integral.interval_integrable_one_div
- \+ *lemma* interval_integral.interval_integrable_one_div_one_add_sq
- \+ *lemma* interval_integral.interval_integrable_pow
- \+ *lemma* interval_integral.interval_integrable_sin

Modified src/measure_theory/interval_integral.lean
- \+/\- *lemma* interval_integrable.add
- \+/\- *lemma* interval_integrable.sub
- \+/\- *lemma* interval_integral.integral_add
- \+/\- *lemma* interval_integral.integral_sub



## [2021-03-19 09:01:18](https://github.com/leanprover-community/mathlib/commit/590f43d)
docs(category_theory): missing module docs ([#6752](https://github.com/leanprover-community/mathlib/pull/6752))
Module docs for a number of files under `category_theory/`.
This is largely a "low hanging fruit" selection; none of the files are particularly complicated.
#### Estimated changes
Modified src/category_theory/const.lean


Modified src/category_theory/core.lean
- \+/\- *def* category_theory.core.forget_functor_to_core

Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/reflects_isomorphisms.lean


Modified src/category_theory/simple.lean


Modified src/category_theory/sums/associator.lean


Modified src/category_theory/sums/basic.lean




## [2021-03-19 09:01:17](https://github.com/leanprover-community/mathlib/commit/c170128)
feat(number_theory/bernoulli): faulhaber' ([#6684](https://github.com/leanprover-community/mathlib/pull/6684))
This deduces an alternative form `faulhaber'` of Faulhaber's theorem from `faulhaber`. In this version, we 
1. sum over `1` to `n` instead of `0` to `n - 1` and
2. use `bernoulli'` instead of `bernoulli`.
Arguably, this is the more common form one finds Faulhaber's theorem in the literature.
#### Estimated changes
Modified docs/100.yaml


Modified src/number_theory/bernoulli.lean
- \+ *theorem* sum_range_pow'



## [2021-03-19 09:01:16](https://github.com/leanprover-community/mathlib/commit/86e1b17)
feat(field_theory/abel_ruffini): solvable by radicals implies solvable Galois group ([#6631](https://github.com/leanprover-community/mathlib/pull/6631))
Proves the theoretical part of insolvability of the quintic. We still need to exhibit a specific polynomial with non-solvable Galois group
#### Estimated changes
Added src/field_theory/abel_ruffini.lean
- \+ *lemma* gal_C_is_solvable
- \+ *lemma* gal_X_is_solvable
- \+ *lemma* gal_X_pow_is_solvable
- \+ *lemma* gal_X_pow_sub_C_is_solvable
- \+ *lemma* gal_X_pow_sub_C_is_solvable_aux
- \+ *lemma* gal_X_pow_sub_one_is_solvable
- \+ *lemma* gal_X_sub_C_is_solvable
- \+ *lemma* gal_is_solvable_of_splits
- \+ *lemma* gal_is_solvable_tower
- \+ *lemma* gal_mul_is_solvable
- \+ *lemma* gal_one_is_solvable
- \+ *lemma* gal_prod_is_solvable
- \+ *lemma* gal_zero_is_solvable
- \+ *inductive* is_solvable_by_rad
- \+ *def* solvable_by_rad.P
- \+ *lemma* solvable_by_rad.induction1
- \+ *lemma* solvable_by_rad.induction2
- \+ *lemma* solvable_by_rad.induction3
- \+ *lemma* solvable_by_rad.induction
- \+ *theorem* solvable_by_rad.is_integral
- \+ *theorem* solvable_by_rad.is_solvable
- \+ *def* solvable_by_rad
- \+ *lemma* splits_X_pow_sub_one_of_X_pow_sub_C



## [2021-03-19 06:00:11](https://github.com/leanprover-community/mathlib/commit/62d532a)
feat(data/finset): erase is partially injective ([#6737](https://github.com/leanprover-community/mathlib/pull/6737))
Show that erase is partially injective, ie that if `s.erase x = s.erase y` and `x` is in `s`, then `x = y`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_inj



## [2021-03-19 03:43:24](https://github.com/leanprover-community/mathlib/commit/a1305be)
chore(scripts): update nolints.txt ([#6763](https://github.com/leanprover-community/mathlib/pull/6763))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-18 23:42:19](https://github.com/leanprover-community/mathlib/commit/cc11e44)
ci(*): lint 'Authors: ' line ([#6750](https://github.com/leanprover-community/mathlib/pull/6750))
#### Estimated changes
Modified scripts/lint-style.py




## [2021-03-18 23:42:17](https://github.com/leanprover-community/mathlib/commit/c3e40be)
feat(data/equiv/local_equiv): define `piecewise` and `disjoint_union` ([#6700](https://github.com/leanprover-community/mathlib/pull/6700))
Also change some lemmas to use `set.ite`.
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+ *def* local_equiv.disjoint_union
- \+ *lemma* local_equiv.is_image.apply_mem_iff
- \+ *lemma* local_equiv.is_image.iff_preimage_eq
- \+ *lemma* local_equiv.is_image.iff_symm_preimage_eq
- \+ *lemma* local_equiv.is_image.image_eq
- \+ *lemma* local_equiv.is_image.left_inv_on_piecewise
- \+ *lemma* local_equiv.is_image.of_image_eq
- \+ *lemma* local_equiv.is_image.of_symm_image_eq
- \+ *def* local_equiv.is_image.restr
- \+ *lemma* local_equiv.is_image.symm_apply_mem_iff
- \+ *lemma* local_equiv.is_image.symm_iff
- \+ *lemma* local_equiv.is_image.symm_image_eq
- \+ *lemma* local_equiv.is_image.symm_maps_to
- \+ *def* local_equiv.is_image
- \+ *lemma* local_equiv.is_image_source_target
- \+ *def* local_equiv.piecewise
- \+ *def* local_equiv.simps.inv_fun
- \+ *lemma* local_equiv.symm_piecewise

Modified src/data/indicator_function.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.ite_empty_left
- \+ *lemma* set.ite_empty_right

Modified src/data/set/function.lean
- \+ *theorem* set.eq_on.piecewise_ite'
- \+ *theorem* set.eq_on.piecewise_ite
- \+ *theorem* set.eq_on_piecewise
- \+ *theorem* set.maps_to.piecewise_ite

Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable_set.ite

Modified src/measure_theory/set_integral.lean




## [2021-03-18 19:27:39](https://github.com/leanprover-community/mathlib/commit/02f77ab)
doc(field_theory/normal): Add authors ([#6759](https://github.com/leanprover-community/mathlib/pull/6759))
Adds Patrick Lutz and I as authors to normal.lean. The last three-quarters of the file are from our work on Abel-Ruffini.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Author.20on.20normal.2Elean.3F
#### Estimated changes
Modified src/field_theory/normal.lean




## [2021-03-18 19:27:37](https://github.com/leanprover-community/mathlib/commit/aea7dfb)
chore(algebra/char_p/basic): weaken assumptions integral_domain --> semiring+ ([#6753](https://github.com/leanprover-community/mathlib/pull/6753))
Taking advantage of the `no_zero_divisors` typeclass, the assumptions on some of the results can be weakened.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* char_p.char_is_prime
- \+/\- *lemma* char_p.char_is_prime_of_pos
- \+/\- *theorem* char_p.char_is_prime_of_two_le
- \+/\- *theorem* char_p.char_is_prime_or_zero
- \+/\- *theorem* char_p.char_ne_one



## [2021-03-18 19:27:36](https://github.com/leanprover-community/mathlib/commit/a10bc3d)
feat(normed_space/inner_product): euclidean_space.norm_eq ([#6744](https://github.com/leanprover-community/mathlib/pull/6744))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* euclidean_space.norm_eq
- \+ *lemma* pi_Lp.norm_eq_of_L2

Modified src/topology/metric_space/pi_Lp.lean
- \+ *lemma* pi_Lp.norm_eq_of_nat



## [2021-03-18 19:27:35](https://github.com/leanprover-community/mathlib/commit/e1ff2df)
chore(*): update `injective` lemma names to match the naming guide ([#6740](https://github.com/leanprover-community/mathlib/pull/6740))
In `src/algebra/group_ring_action.lean`:
- `injective_to_semiring_hom` -> `to_semiring_hom_injective`
In `src/algebra/module/linear_map.lean`:
- `linear_equiv.injective_to_equiv` -> `linear_equiv.to_equiv_injective`
- `linear_equiv.injective_to_linear_map` -> `linear_equiv.to_linear_map_injective`
In `src/analysis/normed_space/enorm.lean`:
- `enorm.injective_coe_fn` -> `enorm.coe_fn_injective`
In `src/data/equiv/basic.lean`:
- `equiv.injective_coe_fn` -> `equiv.coe_fn_injective`
In `src/data/real/nnreal.lean`:
- `nnreal.injective_coe` -> `nnreal.coe_injective`
In `src/data/sum.lean`:
- `sum.injective_inl` -> `sum.inl_injective`
- `sum.injective_inr` -> `sum.inr_injective`
In `src/linear_algebra/affine_space/affine_equiv.lean`:
- `affine_equiv.injective_to_affine_map` -> `affine_equiv.to_affine_map_injective`
- `affine_equiv.injective_coe_fn` -> `affine_equiv.coe_fn_injective`
- `affine_equiv.injective_to_equiv` -> `affine_equiv.to_equiv_injective`
In `src/linear_algebra/affine_space/affine_map.lean`:
- `affine_map.injective_coe_fn` -> `affine_map.coe_fn_injective`
In `src/measure_theory/outer_measure.lean`:
- `measure_theory.outer_measure.injective_coe_fn` -> `measure_theory.outer_measure.coe_fn_injective`
In `src/order/rel_iso.lean`:
- `rel_iso.injective_to_equiv` -> `rel_iso.to_equiv_injective`
- `rel_iso.injective_coe_fn` -> `rel_iso.coe_fn_injective`
In `src/topology/algebra/module.lean`:
- `continuous_linear_map.injective_coe_fn` -> `continuous_linear_map.coe_fn_injective`
#### Estimated changes
Modified src/algebra/group_ring_action.lean
- \- *theorem* injective_to_semiring_hom
- \+ *theorem* to_semiring_hom_injective

Modified src/algebra/module/linear_map.lean
- \- *lemma* linear_equiv.injective_to_equiv
- \- *lemma* linear_equiv.injective_to_linear_map
- \+/\- *lemma* linear_equiv.refl_trans
- \+ *lemma* linear_equiv.to_equiv_injective
- \+ *lemma* linear_equiv.to_linear_map_injective
- \+/\- *lemma* linear_equiv.trans_refl

Modified src/analysis/normed_space/enorm.lean
- \+ *lemma* enorm.coe_fn_injective
- \- *lemma* enorm.injective_coe_fn

Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.coe_fn_injective
- \- *theorem* equiv.injective_coe_fn

Modified src/data/real/nnreal.lean


Modified src/data/sum.lean
- \- *lemma* sum.injective_inl
- \- *lemma* sum.injective_inr
- \+ *lemma* sum.inl_injective
- \+ *lemma* sum.inr_injective

Modified src/field_theory/fixed.lean


Modified src/geometry/manifold/diffeomorph.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.coe_fn_injective
- \- *lemma* affine_equiv.injective_coe_fn
- \- *lemma* affine_equiv.injective_to_affine_map
- \- *lemma* affine_equiv.injective_to_equiv
- \+ *lemma* affine_equiv.to_affine_map_injective
- \+ *lemma* affine_equiv.to_equiv_injective

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.coe_fn_injective
- \- *lemma* affine_map.injective_coe_fn

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/pi_tensor_product.lean


Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.coe_fn_injective
- \- *lemma* measure_theory.outer_measure.injective_coe_fn

Modified src/order/rel_iso.lean
- \+ *theorem* rel_iso.coe_fn_injective
- \- *theorem* rel_iso.injective_coe_fn
- \- *theorem* rel_iso.injective_to_equiv
- \+ *theorem* rel_iso.to_equiv_injective

Modified src/set_theory/ordinal.lean


Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_map.coe_fn_injective
- \- *theorem* continuous_linear_map.injective_coe_fn



## [2021-03-18 19:27:33](https://github.com/leanprover-community/mathlib/commit/83b0981)
feat(ring_theory/polynomial): the symmetric and homogenous polynomials form a subalgebra and submodules, respectively ([#6666](https://github.com/leanprover-community/mathlib/pull/6666))
This adds:
* the new definitions:
  * `mv_polynomial.homogeneous_submodule σ R n`, defined as the `{ x | x.is_homogeneous n }`
  * `mv_polynomial.symmetric_subalgebra σ R`, defined as the `{ x | x.is_symmetric }`
* simp lemmas to reduce membership of the above to the `.is_*` form
* `mv_polynomial.homogenous_submodule_mul` a statement about the product of homogenous submodules
* `mv_polynomial.homogenous_submodule_eq_finsupp_supported` a statement that we already have a different definition of homogenous submodules elsewhere
All the other proofs have just been moved around the files.
#### Estimated changes
Modified src/ring_theory/polynomial/homogeneous.lean
- \+ *lemma* mv_polynomial.homogenous_submodule_eq_finsupp_supported
- \+ *lemma* mv_polynomial.homogenous_submodule_mul
- \+ *lemma* mv_polynomial.mem_homogeneous_submodule

Modified src/ring_theory/polynomial/symmetric.lean
- \+ *lemma* mv_polynomial.mem_symmetric_subalgebra
- \+ *def* mv_polynomial.symmetric_subalgebra



## [2021-03-18 13:48:35](https://github.com/leanprover-community/mathlib/commit/744d59a)
refactor(category_theory/limits): split file ([#6751](https://github.com/leanprover-community/mathlib/pull/6751))
This splits `category_theory.limits.limits` into
`category_theory.limits.is_limit` and `category_theory.limits.has_limits`.
It doesn't meaningfully reduce imports, as everything imports `has_limits`, but in principle it could, and hopefully it makes the content slightly easier to understand when separated.
In any case, the file was certainly too large.
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Mon/colimits.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/category_theory/limits/fubini.lean


Renamed src/category_theory/limits/limits.lean to src/category_theory/limits/has_limits.lean
- \- *def* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso
- \- *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_hom_desc
- \- *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_inv_desc
- \- *def* category_theory.limits.is_colimit.cocone_points_iso_of_equivalence
- \- *def* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso
- \- *lemma* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso_hom_desc
- \- *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_hom
- \- *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_inv
- \- *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_hom
- \- *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_inv
- \- *def* category_theory.limits.is_colimit.desc_cocone_morphism
- \- *lemma* category_theory.limits.is_colimit.desc_self
- \- *def* category_theory.limits.is_colimit.equiv_iso_colimit
- \- *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_apply
- \- *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_symm_apply
- \- *lemma* category_theory.limits.is_colimit.hom_desc
- \- *lemma* category_theory.limits.is_colimit.hom_ext
- \- *lemma* category_theory.limits.is_colimit.hom_is_iso
- \- *def* category_theory.limits.is_colimit.hom_iso'
- \- *def* category_theory.limits.is_colimit.hom_iso
- \- *lemma* category_theory.limits.is_colimit.hom_iso_hom
- \- *def* category_theory.limits.is_colimit.iso_unique_cocone_morphism
- \- *def* category_theory.limits.is_colimit.map
- \- *def* category_theory.limits.is_colimit.map_cocone_equiv
- \- *def* category_theory.limits.is_colimit.mk_cocone_morphism
- \- *def* category_theory.limits.is_colimit.nat_iso
- \- *def* category_theory.limits.is_colimit.of_cocone_equiv
- \- *lemma* category_theory.limits.is_colimit.of_cocone_equiv_apply_desc
- \- *lemma* category_theory.limits.is_colimit.of_cocone_equiv_symm_apply_desc
- \- *def* category_theory.limits.is_colimit.of_faithful
- \- *def* category_theory.limits.is_colimit.of_iso_colimit
- \- *lemma* category_theory.limits.is_colimit.of_iso_colimit_desc
- \- *def* category_theory.limits.is_colimit.of_left_adjoint
- \- *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_fac
- \- *def* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom
- \- *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_fac
- \- *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_of_cocone
- \- *def* category_theory.limits.is_colimit.of_nat_iso.colimit_cocone
- \- *def* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone
- \- *lemma* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone_of_hom
- \- *def* category_theory.limits.is_colimit.of_nat_iso
- \- *def* category_theory.limits.is_colimit.of_point_iso
- \- *def* category_theory.limits.is_colimit.precompose_hom_equiv
- \- *def* category_theory.limits.is_colimit.precompose_inv_equiv
- \- *lemma* category_theory.limits.is_colimit.uniq_cocone_morphism
- \- *def* category_theory.limits.is_colimit.unique_up_to_iso
- \- *def* category_theory.limits.is_colimit.whisker_equivalence
- \- *lemma* category_theory.limits.is_colimit.ι_map
- \- *structure* category_theory.limits.is_colimit
- \- *def* category_theory.limits.is_limit.cone_point_unique_up_to_iso
- \- *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_hom_comp
- \- *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_inv_comp
- \- *def* category_theory.limits.is_limit.cone_points_iso_of_equivalence
- \- *def* category_theory.limits.is_limit.cone_points_iso_of_nat_iso
- \- *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_hom_comp
- \- *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_inv_comp
- \- *def* category_theory.limits.is_limit.equiv_iso_limit
- \- *lemma* category_theory.limits.is_limit.equiv_iso_limit_apply
- \- *lemma* category_theory.limits.is_limit.equiv_iso_limit_symm_apply
- \- *lemma* category_theory.limits.is_limit.hom_ext
- \- *lemma* category_theory.limits.is_limit.hom_is_iso
- \- *def* category_theory.limits.is_limit.hom_iso'
- \- *def* category_theory.limits.is_limit.hom_iso
- \- *lemma* category_theory.limits.is_limit.hom_iso_hom
- \- *lemma* category_theory.limits.is_limit.hom_lift
- \- *def* category_theory.limits.is_limit.iso_unique_cone_morphism
- \- *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_hom
- \- *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_inv
- \- *lemma* category_theory.limits.is_limit.lift_comp_cone_points_iso_of_nat_iso_hom
- \- *def* category_theory.limits.is_limit.lift_cone_morphism
- \- *lemma* category_theory.limits.is_limit.lift_self
- \- *def* category_theory.limits.is_limit.map
- \- *def* category_theory.limits.is_limit.map_cone_equiv
- \- *lemma* category_theory.limits.is_limit.map_π
- \- *def* category_theory.limits.is_limit.mk_cone_morphism
- \- *def* category_theory.limits.is_limit.nat_iso
- \- *def* category_theory.limits.is_limit.of_cone_equiv
- \- *lemma* category_theory.limits.is_limit.of_cone_equiv_apply_desc
- \- *lemma* category_theory.limits.is_limit.of_cone_equiv_symm_apply_desc
- \- *def* category_theory.limits.is_limit.of_faithful
- \- *def* category_theory.limits.is_limit.of_iso_limit
- \- *lemma* category_theory.limits.is_limit.of_iso_limit_lift
- \- *lemma* category_theory.limits.is_limit.of_nat_iso.cone_fac
- \- *def* category_theory.limits.is_limit.of_nat_iso.cone_of_hom
- \- *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_fac
- \- *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_of_cone
- \- *def* category_theory.limits.is_limit.of_nat_iso.hom_of_cone
- \- *lemma* category_theory.limits.is_limit.of_nat_iso.hom_of_cone_of_hom
- \- *def* category_theory.limits.is_limit.of_nat_iso.limit_cone
- \- *def* category_theory.limits.is_limit.of_nat_iso
- \- *def* category_theory.limits.is_limit.of_point_iso
- \- *def* category_theory.limits.is_limit.of_right_adjoint
- \- *def* category_theory.limits.is_limit.postcompose_hom_equiv
- \- *def* category_theory.limits.is_limit.postcompose_inv_equiv
- \- *lemma* category_theory.limits.is_limit.uniq_cone_morphism
- \- *def* category_theory.limits.is_limit.unique_up_to_iso
- \- *def* category_theory.limits.is_limit.whisker_equivalence
- \- *structure* category_theory.limits.is_limit

Added src/category_theory/limits/is_limit.lean
- \+ *def* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso
- \+ *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_hom_desc
- \+ *lemma* category_theory.limits.is_colimit.cocone_point_unique_up_to_iso_inv_desc
- \+ *def* category_theory.limits.is_colimit.cocone_points_iso_of_equivalence
- \+ *def* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso
- \+ *lemma* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso_hom_desc
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_point_unique_up_to_iso_inv
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_hom
- \+ *lemma* category_theory.limits.is_colimit.comp_cocone_points_iso_of_nat_iso_inv
- \+ *def* category_theory.limits.is_colimit.desc_cocone_morphism
- \+ *lemma* category_theory.limits.is_colimit.desc_self
- \+ *def* category_theory.limits.is_colimit.equiv_iso_colimit
- \+ *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_apply
- \+ *lemma* category_theory.limits.is_colimit.equiv_iso_colimit_symm_apply
- \+ *lemma* category_theory.limits.is_colimit.hom_desc
- \+ *lemma* category_theory.limits.is_colimit.hom_ext
- \+ *lemma* category_theory.limits.is_colimit.hom_is_iso
- \+ *def* category_theory.limits.is_colimit.hom_iso'
- \+ *def* category_theory.limits.is_colimit.hom_iso
- \+ *lemma* category_theory.limits.is_colimit.hom_iso_hom
- \+ *def* category_theory.limits.is_colimit.iso_unique_cocone_morphism
- \+ *def* category_theory.limits.is_colimit.map
- \+ *def* category_theory.limits.is_colimit.map_cocone_equiv
- \+ *def* category_theory.limits.is_colimit.mk_cocone_morphism
- \+ *def* category_theory.limits.is_colimit.nat_iso
- \+ *def* category_theory.limits.is_colimit.of_cocone_equiv
- \+ *lemma* category_theory.limits.is_colimit.of_cocone_equiv_apply_desc
- \+ *lemma* category_theory.limits.is_colimit.of_cocone_equiv_symm_apply_desc
- \+ *def* category_theory.limits.is_colimit.of_faithful
- \+ *def* category_theory.limits.is_colimit.of_iso_colimit
- \+ *lemma* category_theory.limits.is_colimit.of_iso_colimit_desc
- \+ *def* category_theory.limits.is_colimit.of_left_adjoint
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_fac
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_fac
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.cocone_of_hom_of_cocone
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.colimit_cocone
- \+ *def* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone
- \+ *lemma* category_theory.limits.is_colimit.of_nat_iso.hom_of_cocone_of_hom
- \+ *def* category_theory.limits.is_colimit.of_nat_iso
- \+ *def* category_theory.limits.is_colimit.of_point_iso
- \+ *def* category_theory.limits.is_colimit.precompose_hom_equiv
- \+ *def* category_theory.limits.is_colimit.precompose_inv_equiv
- \+ *lemma* category_theory.limits.is_colimit.uniq_cocone_morphism
- \+ *def* category_theory.limits.is_colimit.unique_up_to_iso
- \+ *def* category_theory.limits.is_colimit.whisker_equivalence
- \+ *lemma* category_theory.limits.is_colimit.ι_map
- \+ *structure* category_theory.limits.is_colimit
- \+ *def* category_theory.limits.is_limit.cone_point_unique_up_to_iso
- \+ *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_hom_comp
- \+ *lemma* category_theory.limits.is_limit.cone_point_unique_up_to_iso_inv_comp
- \+ *def* category_theory.limits.is_limit.cone_points_iso_of_equivalence
- \+ *def* category_theory.limits.is_limit.cone_points_iso_of_nat_iso
- \+ *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_hom_comp
- \+ *lemma* category_theory.limits.is_limit.cone_points_iso_of_nat_iso_inv_comp
- \+ *def* category_theory.limits.is_limit.equiv_iso_limit
- \+ *lemma* category_theory.limits.is_limit.equiv_iso_limit_apply
- \+ *lemma* category_theory.limits.is_limit.equiv_iso_limit_symm_apply
- \+ *lemma* category_theory.limits.is_limit.hom_ext
- \+ *lemma* category_theory.limits.is_limit.hom_is_iso
- \+ *def* category_theory.limits.is_limit.hom_iso'
- \+ *def* category_theory.limits.is_limit.hom_iso
- \+ *lemma* category_theory.limits.is_limit.hom_iso_hom
- \+ *lemma* category_theory.limits.is_limit.hom_lift
- \+ *def* category_theory.limits.is_limit.iso_unique_cone_morphism
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_point_unique_up_to_iso_inv
- \+ *lemma* category_theory.limits.is_limit.lift_comp_cone_points_iso_of_nat_iso_hom
- \+ *def* category_theory.limits.is_limit.lift_cone_morphism
- \+ *lemma* category_theory.limits.is_limit.lift_self
- \+ *def* category_theory.limits.is_limit.map
- \+ *def* category_theory.limits.is_limit.map_cone_equiv
- \+ *lemma* category_theory.limits.is_limit.map_π
- \+ *def* category_theory.limits.is_limit.mk_cone_morphism
- \+ *def* category_theory.limits.is_limit.nat_iso
- \+ *def* category_theory.limits.is_limit.of_cone_equiv
- \+ *lemma* category_theory.limits.is_limit.of_cone_equiv_apply_desc
- \+ *lemma* category_theory.limits.is_limit.of_cone_equiv_symm_apply_desc
- \+ *def* category_theory.limits.is_limit.of_faithful
- \+ *def* category_theory.limits.is_limit.of_iso_limit
- \+ *lemma* category_theory.limits.is_limit.of_iso_limit_lift
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_fac
- \+ *def* category_theory.limits.is_limit.of_nat_iso.cone_of_hom
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_fac
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.cone_of_hom_of_cone
- \+ *def* category_theory.limits.is_limit.of_nat_iso.hom_of_cone
- \+ *lemma* category_theory.limits.is_limit.of_nat_iso.hom_of_cone_of_hom
- \+ *def* category_theory.limits.is_limit.of_nat_iso.limit_cone
- \+ *def* category_theory.limits.is_limit.of_nat_iso
- \+ *def* category_theory.limits.is_limit.of_point_iso
- \+ *def* category_theory.limits.is_limit.of_right_adjoint
- \+ *def* category_theory.limits.is_limit.postcompose_hom_equiv
- \+ *def* category_theory.limits.is_limit.postcompose_inv_equiv
- \+ *lemma* category_theory.limits.is_limit.uniq_cone_morphism
- \+ *def* category_theory.limits.is_limit.unique_up_to_iso
- \+ *def* category_theory.limits.is_limit.whisker_equivalence
- \+ *structure* category_theory.limits.is_limit

Modified src/category_theory/limits/pi.lean


Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/punit.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/category_theory/limits/yoneda.lean


Modified src/category_theory/monoidal/limits.lean


Modified src/topology/sheaves/stalks.lean




## [2021-03-18 13:48:34](https://github.com/leanprover-community/mathlib/commit/58581d0)
chore(*): normalize Authors: line ([#6749](https://github.com/leanprover-community/mathlib/pull/6749))
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified archive/arithcc.lean


Modified archive/examples/mersenne_primes.lean


Modified archive/examples/prop_encodable.lean


Modified archive/imo/imo1987_q1.lean


Modified archive/imo/imo2020_q2.lean


Modified archive/sensitivity.lean


Modified docs/100.yaml


Modified scripts/lint_mathlib.lean


Modified src/algebra/add_torsor.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/char_p/basic.lean


Modified src/algebra/char_p/invertible.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/invertible.lean


Modified src/algebra/iterate_hom.lean


Modified src/algebra/polynomial/big_operators.lean


Modified src/algebra/star/algebra.lean


Modified src/algebra/star/basic.lean


Modified src/algebra/star/chsh.lean


Modified src/analysis/analytic/linear.lean


Modified src/analysis/analytic/radius_liminf.lean


Modified src/analysis/calculus/formal_multilinear_series.lean


Modified src/analysis/calculus/implicit.lean


Modified src/analysis/calculus/lagrange_multipliers.lean


Modified src/analysis/convex/integral.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/complemented.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/special_functions/sqrt.lean


Modified src/category_theory/adjunction/mates.lean


Modified src/category_theory/category/Kleisli.lean


Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/small_complete.lean


Modified src/category_theory/monad/kleisli.lean


Modified src/category_theory/pempty.lean


Modified src/combinatorics/hall.lean


Modified src/combinatorics/simple_graph/adj_matrix.lean


Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/combinatorics/simple_graph/matching.lean


Modified src/computability/encoding.lean


Modified src/computability/halting.lean


Modified src/computability/language.lean


Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean


Modified src/computability/primrec.lean


Modified src/computability/regular_expressions.lean


Modified src/computability/tm_computable.lean


Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean


Modified src/control/applicative.lean


Modified src/control/bifunctor.lean


Modified src/control/bitraversable/basic.lean


Modified src/control/bitraversable/instances.lean


Modified src/control/bitraversable/lemmas.lean


Modified src/control/equiv_functor.lean


Modified src/control/equiv_functor/instances.lean


Modified src/control/fix.lean


Modified src/control/functor.lean


Modified src/control/functor/multivariate.lean


Modified src/control/lawful_fix.lean


Modified src/control/monad/basic.lean


Modified src/control/monad/cont.lean


Modified src/control/traversable/basic.lean


Modified src/control/traversable/derive.lean


Modified src/control/traversable/instances.lean


Modified src/control/traversable/lemmas.lean


Modified src/control/uliftable.lean


Modified src/data/W.lean


Modified src/data/bitvec/basic.lean


Modified src/data/bool.lean


Modified src/data/bracket.lean


Modified src/data/char.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable/basic.lean


Modified src/data/equiv/encodable/lattice.lean


Modified src/data/equiv/fin.lean


Modified src/data/equiv/list.lean


Modified src/data/equiv/nat.lean


Modified src/data/equiv/option.lean


Modified src/data/erased.lean


Modified src/data/fin_enum.lean


Modified src/data/finset/fold.lean


Modified src/data/finset/gcd.lean


Modified src/data/finset/lattice.lean


Modified src/data/finset/pi.lean


Modified src/data/finset/powerset.lean


Modified src/data/finset/sort.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/fintype/sort.lean


Modified src/data/int/range.lean


Modified src/data/list/default.lean


Modified src/data/list/nodup_equiv_fin.lean


Modified src/data/list/sort.lean


Modified src/data/mllist.lean


Modified src/data/multiset/antidiagonal.lean


Modified src/data/multiset/basic.lean


Modified src/data/multiset/erase_dup.lean


Modified src/data/multiset/finset_ops.lean


Modified src/data/multiset/fold.lean


Modified src/data/multiset/functor.lean


Modified src/data/multiset/gcd.lean


Modified src/data/multiset/lattice.lean


Modified src/data/multiset/nodup.lean


Modified src/data/multiset/pi.lean


Modified src/data/multiset/powerset.lean


Modified src/data/multiset/range.lean


Modified src/data/multiset/sections.lean


Modified src/data/multiset/sort.lean


Modified src/data/mv_polynomial/invertible.lean


Modified src/data/mv_polynomial/monad.lean


Modified src/data/nat/psub.lean


Modified src/data/nat/upto.lean


Modified src/data/num/bitwise.lean


Modified src/data/num/lemmas.lean


Modified src/data/num/prime.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/pfunctor/multivariate/M.lean


Modified src/data/pfunctor/multivariate/W.lean


Modified src/data/pfunctor/multivariate/basic.lean


Modified src/data/pfunctor/univariate/basic.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/pnat/intervals.lean


Modified src/data/pnat/prime.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial/lifts.lean


Modified src/data/qpf/multivariate/basic.lean


Modified src/data/qpf/multivariate/constructions/cofix.lean


Modified src/data/qpf/multivariate/constructions/comp.lean


Modified src/data/qpf/multivariate/constructions/const.lean


Modified src/data/qpf/multivariate/constructions/fix.lean


Modified src/data/qpf/multivariate/constructions/prj.lean


Modified src/data/qpf/multivariate/constructions/quot.lean


Modified src/data/qpf/multivariate/constructions/sigma.lean


Modified src/data/qpf/univariate/basic.lean


Modified src/data/rat/denumerable.lean


Modified src/data/rat/meta_defs.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/irrational.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/parallel.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/countable.lean


Modified src/data/set/enumerate.lean


Modified src/data/set/function.lean


Modified src/data/set/intervals/ord_connected.lean


Modified src/data/set/intervals/pi.lean


Modified src/data/set/intervals/surj_on.lean


Modified src/data/sigma/basic.lean


Modified src/data/string/basic.lean


Modified src/data/string/defs.lean


Modified src/data/subtype.lean


Modified src/data/sym.lean


Modified src/data/sym2.lean


Modified src/data/tree.lean


Modified src/data/typevec.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/parity.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/dynamics/periodic_pts.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/primitive_element.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/geometry/manifold/algebra/lie_group.lean


Modified src/geometry/manifold/diffeomorph.lean


Modified src/geometry/manifold/times_cont_mdiff_map.lean


Modified src/group_theory/perm/fin.lean


Modified src/group_theory/perm/option.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/solvable.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean


Modified src/linear_algebra/affine_space/affine_map.lean


Modified src/linear_algebra/affine_space/affine_subspace.lean


Modified src/linear_algebra/affine_space/basic.lean


Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/affine_space/midpoint.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/dfinsupp.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/direct_sum/finsupp.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/exterior_algebra.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/free_module.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/projection.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/linear_algebra/tensor_algebra.lean


Modified src/linear_algebra/unitary_group.lean


Modified src/logic/function/conjugate.lean


Modified src/logic/function/iterate.lean


Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/meta/coinductive_predicates.lean


Modified src/meta/rb_map.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/fermat4.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/number_theory/primes_congruent_one.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/sum_two_squares.lean


Modified src/order/atoms.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/order/closure.lean


Modified src/order/directed.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/countable_Inter.lean


Modified src/order/filter/interval.lean


Modified src/order/galois_connection.lean


Modified src/order/iterate.lean


Modified src/order/lattice_intervals.lean


Modified src/order/lexicographic.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/order_iso_nat.lean


Modified src/order/semiconj_Sup.lean


Modified src/probability_theory/independence.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/cyclotomic.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/power_series/well_known.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/simple_module.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/zfc.lean


Modified src/system/random/basic.lean


Modified src/tactic/apply.lean


Modified src/tactic/clear.lean


Modified src/tactic/explode.lean


Modified src/tactic/explode_widget.lean


Modified src/tactic/fin_cases.lean


Modified src/tactic/fresh_names.lean


Modified src/tactic/generalizes.lean


Modified src/tactic/group.lean


Modified src/tactic/has_variable_names.lean


Modified src/tactic/induction.lean


Modified src/tactic/interactive.lean


Modified src/tactic/interactive_expr.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/linarith/frontend.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/default.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/omega/clause.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/find_ees.lean


Modified src/tactic/omega/find_scalars.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/lin_comb.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/form.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/omega/nat/preterm.lean


Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/omega/prove_unsats.lean


Modified src/tactic/omega/term.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/pretty_cases.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/reassoc_axiom.lean


Modified src/tactic/replacer.lean


Modified src/tactic/ring_exp.lean


Modified src/tactic/slim_check.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/squeeze.lean


Modified src/tactic/suggest.lean


Modified src/tactic/transfer.lean


Modified src/tactic/unify_equations.lean


Modified src/testing/slim_check/functions.lean


Modified src/testing/slim_check/gen.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/testing/slim_check/testable.lean


Modified src/topology/algebra/group_with_zero.lean


Modified src/topology/algebra/nonarchimedean/basic.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/continuous_map.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real_vector_space.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/metric_separated.lean


Modified src/topology/omega_complete_partial_order.lean


Modified test/fresh_names.lean


Modified test/general_recursion.lean


Modified test/generalizes.lean


Modified test/monotonicity.lean


Modified test/monotonicity/test_cases.lean


Modified test/pi_simp.lean


Modified test/unify_equations.lean




## [2021-03-18 13:48:33](https://github.com/leanprover-community/mathlib/commit/542ff6a)
refactor(algebra/algebra/basic): change submodule.restrict_scalars to use is_scalar_tower ([#6745](https://github.com/leanprover-community/mathlib/pull/6745))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* linear_map.ker_restrict_scalars
- \+/\- *def* submodule.restrict_scalars
- \+/\- *lemma* submodule.restrict_scalars_bot
- \+/\- *lemma* submodule.restrict_scalars_inj
- \+/\- *lemma* submodule.restrict_scalars_mem
- \+/\- *lemma* submodule.restrict_scalars_top
- \+/\- *lemma* submodule.span_le_restrict_scalars



## [2021-03-18 13:48:32](https://github.com/leanprover-community/mathlib/commit/59cda3b)
feat(algebra/associated): Primes that divide each other are associated ([#6732](https://github.com/leanprover-community/mathlib/pull/6732))
Primes that divide each other are associated
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associated_of_irreducible_of_dvd
- \+ *lemma* associated_of_prime_of_dvd



## [2021-03-18 13:48:31](https://github.com/leanprover-community/mathlib/commit/db2a972)
feat(ring_theory/principal_ideal_domain): The generator of a principal prime ideal is a prime ([#6731](https://github.com/leanprover-community/mathlib/pull/6731))
The generator of a principal prime ideal is a prime
#### Estimated changes
Modified src/ring_theory/principal_ideal_domain.lean
- \+ *lemma* submodule.is_principal.prime_generator_of_is_prime



## [2021-03-18 13:48:30](https://github.com/leanprover-community/mathlib/commit/b4afd64)
feat(data/padics/padic_norm): p-adic norm of primes other than p ([#6730](https://github.com/leanprover-community/mathlib/pull/6730))
The p-adic norm of `q` is `1` if `q` is another prime than `p`.
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *lemma* padic_norm.padic_norm_of_prime_of_ne



## [2021-03-18 09:41:26](https://github.com/leanprover-community/mathlib/commit/216aecd)
feat(group_theory/quaternion_group): define the (generalised) quaternion groups ([#6683](https://github.com/leanprover-community/mathlib/pull/6683))
This PR introduces the generalised quaternion groups and determines the orders of its elements.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.succ_mul_pos

Renamed src/group_theory/dihedral.lean to src/group_theory/dihedral_group.lean
- \- *lemma* dihedral.card
- \- *lemma* dihedral.one_def
- \- *lemma* dihedral.order_of_r
- \- *lemma* dihedral.order_of_r_one
- \- *lemma* dihedral.order_of_sr
- \- *lemma* dihedral.r_mul_r
- \- *lemma* dihedral.r_mul_sr
- \- *lemma* dihedral.r_one_pow
- \- *lemma* dihedral.r_one_pow_n
- \- *lemma* dihedral.sr_mul_r
- \- *lemma* dihedral.sr_mul_self
- \- *lemma* dihedral.sr_mul_sr
- \- *inductive* dihedral
- \+ *lemma* dihedral_group.card
- \+ *lemma* dihedral_group.one_def
- \+ *lemma* dihedral_group.order_of_r
- \+ *lemma* dihedral_group.order_of_r_one
- \+ *lemma* dihedral_group.order_of_sr
- \+ *lemma* dihedral_group.r_mul_r
- \+ *lemma* dihedral_group.r_mul_sr
- \+ *lemma* dihedral_group.r_one_pow
- \+ *lemma* dihedral_group.r_one_pow_n
- \+ *lemma* dihedral_group.sr_mul_r
- \+ *lemma* dihedral_group.sr_mul_self
- \+ *lemma* dihedral_group.sr_mul_sr
- \+ *inductive* dihedral_group

Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_eq_prime_pow

Added src/group_theory/quaternion_group.lean
- \+ *lemma* quaternion_group.a_mul_a
- \+ *lemma* quaternion_group.a_mul_xa
- \+ *lemma* quaternion_group.a_one_pow
- \+ *lemma* quaternion_group.a_one_pow_n
- \+ *lemma* quaternion_group.card
- \+ *lemma* quaternion_group.one_def
- \+ *lemma* quaternion_group.order_of_a
- \+ *lemma* quaternion_group.order_of_a_one
- \+ *lemma* quaternion_group.order_of_xa
- \+ *lemma* quaternion_group.quaternion_group_one_is_cyclic
- \+ *def* quaternion_group.quaternion_group_zero_equiv_dihedral_group_zero
- \+ *lemma* quaternion_group.xa_mul_a
- \+ *lemma* quaternion_group.xa_mul_xa
- \+ *lemma* quaternion_group.xa_pow_four
- \+ *lemma* quaternion_group.xa_pow_two
- \+ *inductive* quaternion_group



## [2021-03-18 06:07:05](https://github.com/leanprover-community/mathlib/commit/8116851)
doc(category_theory): convert comments about universes to library note ([#6748](https://github.com/leanprover-community/mathlib/pull/6748))
#### Estimated changes
Modified docs/tutorial/category_theory/calculating_colimits_in_Top.lean


Modified docs/tutorial/category_theory/intro.lean


Modified src/category_theory/adjunction/opposites.lean


Modified src/category_theory/arrow.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/core.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/constructions/over/connected.lean


Modified src/category_theory/limits/constructions/over/default.lean


Modified src/category_theory/limits/constructions/over/products.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/basic.lean


Modified src/category_theory/monad/bundled.lean


Modified src/category_theory/monad/equiv_mon.lean


Modified src/category_theory/monad/kleisli.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monad/products.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/over.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/sums/basic.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean


Modified src/data/opposite.lean


Modified src/ring_theory/valuation/basic.lean




## [2021-03-18 04:45:13](https://github.com/leanprover-community/mathlib/commit/e955a6b)
chore(scripts): update nolints.txt ([#6747](https://github.com/leanprover-community/mathlib/pull/6747))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-03-18 03:01:54](https://github.com/leanprover-community/mathlib/commit/9b8d41a)
feat(ring_theory/finiteness): add transitivity of finite presentation ([#6640](https://github.com/leanprover-community/mathlib/pull/6640))
This adds transitivity of finite presentation (for rings). I think we now have a basic API for finitely presented algebras.
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* alg_hom.finite_presentation.comp
- \+ *lemma* algebra.finite_presentation.trans
- \+ *lemma* ring_hom.finite_presentation.comp



## [2021-03-17 23:52:47](https://github.com/leanprover-community/mathlib/commit/804b0ed)
chore(data/mv_polynomial/basic): add coeff_smul to match coeff_add etc ([#6742](https://github.com/leanprover-community/mathlib/pull/6742))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.coeff_smul



## [2021-03-17 22:49:08](https://github.com/leanprover-community/mathlib/commit/30b3455)
feat(ring_theory/roots_of_unity): Restrict ring homomorphism to roots of unity ([#6646](https://github.com/leanprover-community/mathlib/pull/6646))
Restrict a ring homomorphism to roots of unity.
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *def* ring_equiv.restrict_roots_of_unity
- \+ *lemma* ring_equiv.restrict_roots_of_unity_coe_apply
- \+ *lemma* ring_equiv.restrict_roots_of_unity_symm
- \+ *lemma* ring_hom.map_root_of_unity_eq_pow_self
- \+ *def* ring_hom.restrict_roots_of_unity
- \+ *lemma* ring_hom.restrict_roots_of_unity_coe_apply
- \+ *lemma* roots_of_unity.coe_pow



## [2021-03-17 19:18:34](https://github.com/leanprover-community/mathlib/commit/9507a34)
chore(category_theory/limits/creates): fix typo in docstring ([#6738](https://github.com/leanprover-community/mathlib/pull/6738))
#### Estimated changes
Modified src/category_theory/limits/creates.lean




## [2021-03-17 19:18:33](https://github.com/leanprover-community/mathlib/commit/6e1143a)
chore(combinatorics/simple_graph): remove bad simp attribute ([#6736](https://github.com/leanprover-community/mathlib/pull/6736))
As in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/symmetry.20fails.20if.20simple.20graph.20is.20imported.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.edge_symm'
- \+/\- *lemma* simple_graph.edge_symm



## [2021-03-17 19:18:32](https://github.com/leanprover-community/mathlib/commit/ce8a6ca)
refactor(data/multiset/basic): consistently use 'nsmul' in names ([#6735](https://github.com/leanprover-community/mathlib/pull/6735))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* multiset.to_finset_sum_count_nsmul_eq
- \- *lemma* multiset.to_finset_sum_count_smul_eq

Modified src/data/finsupp/basic.lean


Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.card_nsmul
- \- *lemma* multiset.card_smul
- \+ *theorem* multiset.count_nsmul
- \- *theorem* multiset.count_smul
- \+ *lemma* multiset.prod_nsmul
- \- *lemma* multiset.prod_smul

Modified src/data/multiset/fold.lean


Modified src/data/pnat/factors.lean




## [2021-03-17 19:18:31](https://github.com/leanprover-community/mathlib/commit/7e82bba)
feat(algebra/module/submodule): add `smul_of_tower_mem` ([#6712](https://github.com/leanprover-community/mathlib/pull/6712))
This adds the lemmas:
* `sub_mul_action.smul_of_tower_mem`
* `submodule.smul_of_tower_mem`
And uses them to construct the new scalar actions:
* `sub_mul_action.mul_action'`
* `sub_mul_action.is_scalar_tower`
* `submodule.semimodule'`
* `submodule.is_scalar_tower`
With associated lemmas
* `sub_mul_action.coe_smul_of_tower`
* `submodule.coe_smul_of_tower`
The unprimed instance continue to hold their old values, and exist to speed up typeclass search; the same pattern we use for `tensor_product.semimodule` vs `tensor_product.semimodule`.
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+/\- *lemma* submodule.coe_smul
- \+ *lemma* submodule.coe_smul_of_tower
- \+/\- *lemma* submodule.smul_mem_iff'
- \+/\- *theorem* submodule.smul_mem_iff
- \+ *lemma* submodule.smul_of_tower_mem

Modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* sub_mul_action.coe_smul_of_tower
- \+/\- *lemma* sub_mul_action.smul_mem_iff'
- \+/\- *theorem* sub_mul_action.smul_mem_iff
- \+ *lemma* sub_mul_action.smul_of_tower_mem



## [2021-03-17 19:18:29](https://github.com/leanprover-community/mathlib/commit/4ae81c2)
feat(bounded_continuous_function): transport structure to C(α, β) when α compact ([#6701](https://github.com/leanprover-community/mathlib/pull/6701))
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean
- \+ *lemma* continuous_map.mul_coe
- \+ *lemma* continuous_map.one_coe
- \+ *lemma* continuous_map.smul_apply

Modified src/topology/bounded_continuous_function.lean
- \+ *def* bounded_continuous_function.add_equiv_continuous_map_of_compact
- \+ *lemma* bounded_continuous_function.add_equiv_continuous_map_of_compact_to_equiv
- \+ *def* bounded_continuous_function.equiv_continuous_map_of_compact
- \+ *def* bounded_continuous_function.forget_boundedness
- \+ *def* bounded_continuous_function.forget_boundedness_add_hom
- \+ *lemma* bounded_continuous_function.forget_boundedness_coe
- \+ *def* bounded_continuous_function.isometric_continuous_map_of_compact
- \+ *lemma* bounded_continuous_function.isometric_continuous_map_of_compact_to_isometric
- \+ *def* bounded_continuous_function.linear_isometry_continuous_map_of_compact
- \+ *lemma* bounded_continuous_function.linear_isometry_continuous_map_of_compact_to_add_equiv
- \+ *lemma* bounded_continuous_function.linear_isometry_continuous_map_of_compact_to_equiv



## [2021-03-17 19:18:25](https://github.com/leanprover-community/mathlib/commit/0b0fd52)
chore(analysis/normed_space/extend): provide a version without restrict_scalars ([#6693](https://github.com/leanprover-community/mathlib/pull/6693))
This is some pre-work to try and speed up the proof in `hahn_banach`, which as I understand it is super slow because it has to work very hard to unify typeclass which keep switching back and forth between `F` and `restrict_scalars ℝ 𝕜 F`. 
This PR is unlikely to have changed the speed of that proof, but I suspect these definitions might help in a future PR - and it pushes `restrict_scalars` out of the interesting bit of the proof.
#### Estimated changes
Modified src/analysis/normed_space/extend.lean
- \+ *lemma* continuous_linear_map.extend_to_𝕜'_apply
- \+ *lemma* continuous_linear_map.extend_to_𝕜_apply
- \+ *lemma* linear_map.extend_to_𝕜'_apply
- \+ *lemma* linear_map.extend_to_𝕜_apply
- \+/\- *lemma* norm_bound

Modified src/analysis/normed_space/hahn_banach.lean




## [2021-03-17 19:18:22](https://github.com/leanprover-community/mathlib/commit/6db70c9)
refactor(linear_algebra/determinant): refactor proof of upper_two_block_triangular_det ([#6690](https://github.com/leanprover-community/mathlib/pull/6690))
Refactored the proof of upper_two_block_triangular_det (to use sum_congr_hom.range) following a suggestion from Eric Wieser (during PR review of [#6050](https://github.com/leanprover-community/mathlib/pull/6050)).
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.mem_sum_congr_hom_range_of_perm_maps_to_inl
- \- *lemma* equiv.perm.perm_on_inl_iff_perm_on_inr

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* matrix.upper_two_block_triangular_det



## [2021-03-17 19:18:19](https://github.com/leanprover-community/mathlib/commit/4119181)
feat(measure_theory/l2_space): L2 is an inner product space ([#6596](https://github.com/leanprover-community/mathlib/pull/6596))
If `E` is an inner product space, then so is `Lp E 2 µ`, with inner product being the integral of the inner products between function values.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/group_power/basic.lean
- \+ *lemma* sub_pow_two
- \+ *lemma* two_mul_le_add_pow_two

Modified src/algebra/ordered_field.lean
- \+ *lemma* half_le_self

Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* ae_measurable.inner

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.lipschitz_with.integrable_comp_iff_of_antilipschitz

Added src/measure_theory/l2_space.lean
- \+ *lemma* measure_theory.L2.inner_def
- \+ *lemma* measure_theory.L2.integrable_inner
- \+ *lemma* measure_theory.L2.integral_inner_eq_sq_snorm
- \+ *lemma* measure_theory.L2.mem_L1_inner
- \+ *lemma* measure_theory.L2.snorm_inner_lt_top
- \+ *lemma* measure_theory.L2.snorm_rpow_two_norm_lt_top

Modified src/measure_theory/lp_space.lean
- \+ *lemma* lipschitz_with.mem_ℒp_comp_iff_of_antilipschitz

Modified src/measure_theory/prod.lean


Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous_linear_map.integral_comp_comm'
- \+ *lemma* integral_conj
- \+ *lemma* integral_of_real
- \+ *lemma* linear_isometry.integral_comp_comm

Modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* antilipschitz_with.closed_embedding

Modified src/topology/metric_space/isometry.lean
- \+ *theorem* isometry.closed_embedding



## [2021-03-17 19:18:17](https://github.com/leanprover-community/mathlib/commit/fb28eac)
feat(number_theory/bernoulli): Faulhaber's theorem ([#6409](https://github.com/leanprover-community/mathlib/pull/6409))
Co-authored-by Fabian Kruse
#### Estimated changes
Modified docs/100.yaml


Modified docs/references.bib


Modified src/number_theory/bernoulli.lean
- \+/\- *lemma* bernoulli'_four
- \+/\- *lemma* bernoulli'_one
- \+/\- *lemma* bernoulli'_three
- \+/\- *lemma* bernoulli'_two
- \+/\- *lemma* bernoulli'_zero
- \+/\- *lemma* bernoulli_one
- \+/\- *lemma* bernoulli_zero
- \+ *theorem* sum_range_pow



## [2021-03-17 16:20:31](https://github.com/leanprover-community/mathlib/commit/83a4b8b)
chore(group_theory/subgroup): fix typo in docstring ([#6722](https://github.com/leanprover-community/mathlib/pull/6722))
#### Estimated changes
Modified src/group_theory/subgroup.lean




## [2021-03-17 16:20:30](https://github.com/leanprover-community/mathlib/commit/73922b5)
feat(data/zsqrtd/basic): add some lemmas about conj, norm ([#6715](https://github.com/leanprover-community/mathlib/pull/6715))
#### Estimated changes
Modified src/data/zsqrtd/basic.lean
- \+ *lemma* zsqrtd.conj_add
- \+ *lemma* zsqrtd.conj_conj
- \+ *def* zsqrtd.conj_hom
- \+ *lemma* zsqrtd.conj_neg
- \+ *lemma* zsqrtd.conj_one
- \+ *lemma* zsqrtd.conj_sub
- \+ *lemma* zsqrtd.conj_zero
- \+ *lemma* zsqrtd.norm_conj
- \+ *lemma* zsqrtd.norm_neg



## [2021-03-17 12:41:30](https://github.com/leanprover-community/mathlib/commit/1f50530)
feat(data/set/intervals/image_preimage, algebra/ordered_monoid): new typeclass for interval bijection lemmas ([#6629](https://github.com/leanprover-community/mathlib/pull/6629))
This commit introduces a ``has_exists_add_of_le`` typeclass extending ``ordered_add_comm_monoid``; is the assumption needed so that additively translating an interval gives a bijection. We then prove this fact for all flavours of interval. 
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Correct.20setting.20for.20positive.20shifts.20of.20intervals
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean


Modified src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.Icc_add_bij
- \+ *lemma* set.Ici_add_bij
- \+ *lemma* set.Ico_add_bij
- \+ *lemma* set.Iic_add_bij
- \+ *lemma* set.Iio_add_bij
- \+ *lemma* set.Ioc_add_bij
- \+ *lemma* set.Ioi_add_bij
- \+ *lemma* set.Ioo_add_bij



## [2021-03-17 10:17:23](https://github.com/leanprover-community/mathlib/commit/1345319)
feat(ring_theory/algebraic data/real/irrational): add a proof that a transcendental real number is irrational ([#6721](https://github.com/leanprover-community/mathlib/pull/6721))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/263328-triage
#### Estimated changes
Modified src/data/real/irrational.lean
- \+ *lemma* transcendental.irrational

Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_algebra_map



## [2021-03-17 10:17:22](https://github.com/leanprover-community/mathlib/commit/4b1d588)
chore(linear_algebra/determinant): redefine det using multilinear_map.alternatization ([#6708](https://github.com/leanprover-community/mathlib/pull/6708))
This slightly changes the definitional unfolding of `matrix.det` (moving a function application outside a sum and adjusting the version of int-multiplication used).
By doing this, a large number of proofs become a trivial application of a more general statement about alternating maps.
`det_row_multilinear` already existed prior to this commit, but now `det` is defined in terms of it instead of the other way around.
We still need both, as otherwise we would break `M.det` dot notation, as `det_row_multilinear` does not have its argument expressed as a matrix.
#### Estimated changes
Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.map_coord_zero
- \+ *lemma* alternating_map.map_update_zero
- \+ *lemma* alternating_map.map_zero

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/determinant.lean
- \+ *abbreviation* matrix.det
- \+ *lemma* matrix.det_apply'
- \+ *lemma* matrix.det_apply
- \+/\- *def* matrix.det_row_multilinear

Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified test/matrix.lean




## [2021-03-17 10:17:21](https://github.com/leanprover-community/mathlib/commit/84933f1)
feat(ring_theory/polynomial): Pochhammer polynomials ([#6598](https://github.com/leanprover-community/mathlib/pull/6598))
# The Pochhammer polynomials
We define and prove some basic relations about
`pochhammer S n : polynomial S = X * (X+1) * ... * (X + n - 1)`
which is also known as the rising factorial.
#### Estimated changes
Added src/ring_theory/polynomial/pochhammer.lean
- \+ *lemma* choose_eq_pochhammer_eval_div_factorial
- \+ *lemma* factorial_mul_pochhammer'
- \+ *lemma* factorial_mul_pochhammer
- \+ *lemma* pochhammer_eval_cast
- \+ *lemma* pochhammer_eval_eq_choose_mul_factorial
- \+ *lemma* pochhammer_eval_eq_factorial_div_factorial
- \+ *lemma* pochhammer_eval_one'
- \+ *lemma* pochhammer_eval_one
- \+ *lemma* pochhammer_eval_zero
- \+ *lemma* pochhammer_map
- \+ *lemma* pochhammer_mul
- \+ *lemma* pochhammer_ne_zero_eval_zero
- \+ *lemma* pochhammer_one
- \+ *lemma* pochhammer_pos
- \+ *lemma* pochhammer_succ_left
- \+ *lemma* pochhammer_succ_right
- \+ *lemma* pochhammer_zero
- \+ *lemma* pochhammer_zero_eval_zero
- \+ *lemma* polynomial.mul_X_add_nat_cast_comp



## [2021-03-17 08:30:54](https://github.com/leanprover-community/mathlib/commit/861f594)
feat(field_theory/normal): Tower of solvable extensions is solvable ([#6643](https://github.com/leanprover-community/mathlib/pull/6643))
This is the key lemma that makes Abel-Ruffini work.
#### Estimated changes
Modified src/field_theory/normal.lean
- \+ *lemma* is_solvable_of_is_scalar_tower



## [2021-03-17 08:30:53](https://github.com/leanprover-community/mathlib/commit/6f6b548)
refactor(group_theory/order_of_element): now makes sense for infinite monoids ([#6587](https://github.com/leanprover-community/mathlib/pull/6587))
This PR generalises `order_of` from finite groups to (potentially infinite) monoids. By convention, the value of `order_of` for an element of infinite order is `0`. This is non-standard for the order of an element, but agrees with the convention that the characteristic of a field is `0` if `1` has infinite additive order. It also enables to remove the assumption `0<n` for some lemmas about orders of elements of the dihedral group, which by convention is also the infinite dihedral group for `n=0`.
The whole file has been restructured to take into account that `order_of` now makes sense for monoids. There is still an open issue about adding [to_additive], but this should be done in a seperate PR. Also, some results could be generalised with assumption `0 < order_of a` instead of finiteness of the whole group.
#### Estimated changes
Modified src/group_theory/dihedral.lean
- \+/\- *lemma* dihedral.order_of_r_one
- \+/\- *lemma* dihedral.order_of_sr

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_pow_eq_one
- \+ *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq'
- \+/\- *lemma* image_range_order_of
- \+/\- *lemma* is_cyclic.card_order_of_eq_totient
- \+/\- *lemma* is_cyclic.card_pow_eq_one_le
- \+/\- *lemma* is_cyclic.exists_monoid_generator
- \+/\- *lemma* is_cyclic_of_order_of_eq_card
- \+/\- *lemma* is_cyclic_of_prime_card
- \+/\- *lemma* mem_gpowers_iff_mem_range_order_of
- \+ *lemma* mem_powers_iff_mem_range_order_of
- \+/\- *lemma* order_eq_card_gpowers
- \+ *lemma* order_eq_card_powers
- \- *def* order_of
- \+/\- *lemma* order_of_eq_card_of_forall_mem_gpowers
- \+ *lemma* order_of_eq_zero
- \+/\- *lemma* order_of_le_card_univ
- \+ *lemma* order_of_le_of_pow_eq_one'
- \+ *lemma* order_of_pos'
- \+ *lemma* order_of_pow''
- \+ *lemma* order_of_pow'
- \+/\- *lemma* order_of_pow
- \+/\- *lemma* pow_card_eq_one
- \+/\- *lemma* pow_gcd_card_eq_one_iff
- \+/\- *lemma* pow_injective_of_lt_order_of
- \+/\- *lemma* pow_order_of_eq_one
- \+/\- *lemma* sum_card_order_of_eq_card_pow_eq_one

Modified src/group_theory/perm/cycles.lean
- \- *def* equiv.perm.cycle_factors
- \- *def* equiv.perm.cycle_factors_aux
- \- *def* equiv.perm.cycle_of

Modified src/ring_theory/integral_domain.lean




## [2021-03-17 05:36:54](https://github.com/leanprover-community/mathlib/commit/3e7a56e)
feat(tactic/norm_num): support for nat.cast + int constructors ([#6235](https://github.com/leanprover-community/mathlib/pull/6235))
This adds support for the functions `nat.cast`, `int.cast`, `rat.cast`
as well as `int.to_nat`, `int.nat_abs` and the constructors of int
 `int.of_nat` and `int.neg_succ_of_nat`, at least in their simp-normal
 forms.
#### Estimated changes
Modified src/tactic/norm_num.lean
- \+ *theorem* norm_num.int_to_nat_cast
- \+ *theorem* norm_num.int_to_nat_neg
- \+ *theorem* norm_num.int_to_nat_pos
- \+ *theorem* norm_num.nat_abs_neg
- \+ *theorem* norm_num.nat_abs_pos
- \+ *theorem* norm_num.neg_succ_of_nat



## [2021-03-17 03:47:21](https://github.com/leanprover-community/mathlib/commit/d292fd7)
refactor(topology/metric_space/basic): add pseudo_metric ([#6716](https://github.com/leanprover-community/mathlib/pull/6716))
This is the natural continuation of [#6694](https://github.com/leanprover-community/mathlib/pull/6694): we introduce here `pseudo_metric_space`.
Note that I didn't do anything fancy, I only generalize the results that work out of the box for pseudometric spaces (quite a lot indeed).
It's possible that there is some duplicate code, especially in the section about products.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* ball_prod_same
- \+/\- *theorem* closed_ball_prod_same
- \+/\- *theorem* dist_comm
- \+/\- *theorem* dist_eq_zero
- \+/\- *theorem* dist_le_zero
- \+/\- *theorem* dist_pos
- \+/\- *theorem* dist_self
- \+/\- *lemma* edist_lt_top
- \+/\- *theorem* eq_of_dist_eq_zero
- \+/\- *theorem* eq_of_forall_dist_le
- \+/\- *theorem* eq_of_nndist_eq_zero
- \+/\- *lemma* exists_locally_finite_Union_eq_ball_radius_lt
- \+/\- *lemma* finite_cover_balls_of_compact
- \+/\- *lemma* metric.compact_iff_closed_bounded
- \+/\- *theorem* metric.continuous_at_iff
- \+/\- *theorem* metric.continuous_iff
- \+/\- *theorem* metric.continuous_on_iff
- \+/\- *theorem* metric.continuous_within_at_iff
- \+ *theorem* metric.controlled_of_uniform_embedding
- \+/\- *lemma* metric.is_open_singleton_iff
- \+/\- *theorem* metric.mem_closure_iff
- \+/\- *lemma* metric.mem_closure_range_iff
- \+/\- *lemma* metric.mem_closure_range_iff_nat
- \+/\- *theorem* metric.mem_of_closed'
- \+ *def* metric.of_t2_pseudo_metric_space
- \+/\- *theorem* metric.tendsto_nhds_nhds
- \+/\- *theorem* metric.tendsto_nhds_within_nhds
- \+/\- *theorem* metric.tendsto_nhds_within_nhds_within
- \+/\- *theorem* metric.uniform_continuous_iff
- \+/\- *lemma* metric.uniform_continuous_on_iff
- \+/\- *theorem* metric.uniform_embedding_iff'
- \+/\- *theorem* metric.uniform_embedding_iff
- \+/\- *def* metric_space.induced
- \+/\- *def* metric_space.replace_uniformity
- \+/\- *theorem* nndist_eq_zero
- \+/\- *lemma* nndist_pi_const
- \+/\- *lemma* prod.dist_eq
- \+ *def* pseudo_emetric_space.to_pseudo_metric_space
- \+ *def* pseudo_emetric_space.to_pseudo_metric_space_of_dist
- \+ *def* pseudo_metric.dist_setoid
- \+ *lemma* pseudo_metric_quot_dist_eq
- \+ *def* pseudo_metric_space.induced
- \+ *def* pseudo_metric_space.replace_uniformity
- \+ *theorem* subtype.pseudo_dist_eq
- \+/\- *theorem* zero_eq_dist
- \+/\- *theorem* zero_eq_nndist

Modified src/topology/metric_space/emetric_space.lean
- \+ *def* emetric_of_t2_pseudo_emetric_space
- \+ *lemma* pseudo_edist_pi_const
- \+ *lemma* pseudo_edist_pi_def
- \+ *def* pseudo_emetric_space.replace_uniformity
- \- *lemma* pseudoedist_pi_const
- \- *lemma* pseudoedist_pi_def
- \- *def* pseudoemetric_space.replace_uniformity

Modified src/topology/metric_space/gluing.lean
- \+/\- *def* metric.glue_premetric

Modified src/topology/metric_space/gromov_hausdorff_realized.lean
- \+/\- *def* Gromov_Hausdorff.premetric_optimal_GH_dist

Deleted src/topology/metric_space/premetric_space.lean
- \- *def* premetric.dist_setoid
- \- *lemma* premetric.metric_quot_dist_eq



## [2021-03-17 02:56:43](https://github.com/leanprover-community/mathlib/commit/3936f5f)
chore(scripts): update nolints.txt ([#6719](https://github.com/leanprover-community/mathlib/pull/6719))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-03-17 01:14:27](https://github.com/leanprover-community/mathlib/commit/b9ccb8f)
feat(algebraic_topology/simplicial_objects + ...): Truncated simplicial objects + skeleton ([#6711](https://github.com/leanprover-community/mathlib/pull/6711))
This PR adds truncated simplicial objects and the skeleton functor (aka the truncation functor).
#### Estimated changes
Modified src/algebraic_topology/simplex_category.lean
- \+ *def* simplex_category.len
- \+ *lemma* simplex_category.len_mk
- \+ *lemma* simplex_category.mk_len
- \+ *def* simplex_category.truncated.inclusion
- \+ *def* simplex_category.truncated

Modified src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.simplicial_object.sk
- \+ *def* category_theory.simplicial_object.truncated

Modified src/algebraic_topology/simplicial_set.lean
- \+ *def* sSet.sk
- \+ *def* sSet.truncated



## [2021-03-17 01:14:26](https://github.com/leanprover-community/mathlib/commit/87c12ab)
feat(topology/continuous_map): lattice structures ([#6706](https://github.com/leanprover-community/mathlib/pull/6706))
#### Estimated changes
Modified src/topology/continuous_map.lean
- \+ *def* continuous_map.equiv_fn_of_discrete
- \+ *lemma* continuous_map.inf_apply
- \+ *lemma* continuous_map.le_def
- \+ *lemma* continuous_map.lt_def
- \+ *lemma* continuous_map.sup_apply



## [2021-03-16 21:43:26](https://github.com/leanprover-community/mathlib/commit/40a0ac7)
chore(linear_algebra/finite_dimensional): change instance ([#6713](https://github.com/leanprover-community/mathlib/pull/6713))
With the new instance `finite_dimensional K K` Lean can deduce the old instance automatically. I don not completely understand why it needs the new instance (`apply_instance` proves it), probably this is related to the order of unfolding `finite_dimensional` and applying `is_noetherian` instances.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean




## [2021-03-16 21:43:25](https://github.com/leanprover-community/mathlib/commit/177020e)
feat(topology/separation): `(closure s).subsingleton ↔ s.subsingleton` ([#6707](https://github.com/leanprover-community/mathlib/pull/6707))
Also migrate `set.subsingleton_of_image` to `set.subsingleton`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* function.injective.subsingleton_image_iff
- \+/\- *lemma* set.subsingleton_empty
- \+/\- *lemma* set.subsingleton_singleton

Modified src/topology/separation.lean
- \+ *lemma* set.subsingleton.closure
- \+ *lemma* subsingleton_closure



## [2021-03-16 21:43:23](https://github.com/leanprover-community/mathlib/commit/890066a)
feat(measure_theory/measure_space): define `quasi_measure_preserving` ([#6699](https://github.com/leanprover-community/mathlib/pull/6699))
* add `measurable.iterate`
* move section about `measure_space` up to make `volume_tac` available
  much earlier;
* add `map_of_not_measurable`;
* drop assumption `measurable f` in `map_mono`;
* add `tendsto_ae_map`;
* more API about `absolutely_continuous`;
* define `quasi_measure_preserving` and prove some properties.
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \+ *lemma* measurable.iterate

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.absolutely_continuous.ae_eq
- \+/\- *lemma* measure_theory.measure.absolutely_continuous.mk
- \- *lemma* measure_theory.measure.absolutely_continuous.refl
- \- *lemma* measure_theory.measure.absolutely_continuous.rfl
- \- *lemma* measure_theory.measure.absolutely_continuous.trans
- \+/\- *lemma* measure_theory.measure.absolutely_continuous_of_eq
- \+ *lemma* measure_theory.measure.absolutely_continuous_of_le
- \+ *lemma* measure_theory.measure.ae_le_iff_absolutely_continuous
- \+/\- *lemma* measure_theory.measure.map_mono
- \+ *theorem* measure_theory.measure.map_of_not_measurable
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.ae
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.ae_eq
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.ae_map_le
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.mono
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.mono_left
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.mono_right
- \+ *lemma* measure_theory.measure.quasi_measure_preserving.tendsto_ae
- \+ *structure* measure_theory.measure.quasi_measure_preserving
- \+ *lemma* measure_theory.measure.tendsto_ae_map

Modified src/measure_theory/set_integral.lean




## [2021-03-16 21:43:22](https://github.com/leanprover-community/mathlib/commit/f5f42bc)
chore(*): update to Lean 3.28.0c ([#6691](https://github.com/leanprover-community/mathlib/pull/6691))
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/char_p/basic.lean


Modified src/combinatorics/colex.lean


Modified src/computability/turing_machine.lean


Modified src/data/finset/basic.lean


Modified src/data/multiset/basic.lean


Modified src/data/nat/prime.lean


Modified src/data/option/defs.lean


Modified src/data/quot.lean


Modified src/data/typevec.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/tactic/explode_widget.lean




## [2021-03-16 21:43:21](https://github.com/leanprover-community/mathlib/commit/a116025)
feat(geometry/manifold/mfderiv): more lemmas ([#6679](https://github.com/leanprover-community/mathlib/pull/6679))
* move section `mfderiv_fderiv` up, add aliases;
* rename old `unique_mdiff_on.unique_diff_on` to `unique_mdiff_on.unique_diff_on_target_inter`;
* add a section about `continuous_linear_map`;
* more lemmas about `model_with_corners`;
* add lemmas about `ext_chart_at`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at.congr'

Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* continuous_linear_map.mfderiv_eq
- \+ *lemma* continuous_linear_map.mfderiv_within_eq
- \+ *lemma* has_mfderiv_at_ext_chart_at
- \+ *lemma* has_mfderiv_at_iff_has_fderiv_at
- \+ *lemma* has_mfderiv_within_at_ext_chart_at
- \+ *lemma* has_mfderiv_within_at_iff_has_fderiv_within_at
- \+ *lemma* local_homeomorph.mdifferentiable.ker_mfderiv_eq_bot
- \+ *lemma* local_homeomorph.mdifferentiable.mfderiv_injective
- \+ *lemma* local_homeomorph.mdifferentiable.range_mfderiv_eq_top
- \+ *lemma* mdifferentiable_at_ext_chart_at
- \+ *lemma* mdifferentiable_on_ext_chart_at
- \+/\- *theorem* mfderiv_eq_fderiv
- \+/\- *theorem* mfderiv_within_eq_fderiv_within
- \+ *lemma* model_with_corners.has_mfderiv_within_at_symm
- \- *lemma* model_with_corners.mdifferentiable
- \+/\- *lemma* model_with_corners.mdifferentiable_on_symm
- \- *lemma* unique_mdiff_on.unique_diff_on
- \+ *lemma* unique_mdiff_on.unique_diff_on_target_inter

Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners.continuous_at_symm
- \+ *lemma* model_with_corners.continuous_within_at_symm

Modified src/geometry/manifold/times_cont_mdiff.lean




## [2021-03-16 21:43:20](https://github.com/leanprover-community/mathlib/commit/214b8e8)
feat(topology/algebra): more on closure ([#6675](https://github.com/leanprover-community/mathlib/pull/6675))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *theorem* subgroup.inv_coe_set

Added src/topology/algebra/algebra.lean
- \+ *lemma* subalgebra.is_closed_topological_closure
- \+ *lemma* subalgebra.subring_topological_closure
- \+ *def* subalgebra.topological_closure
- \+ *lemma* subalgebra.topological_closure_minimal

Modified src/topology/algebra/group.lean
- \+ *lemma* subgroup.is_closed_topological_closure
- \+ *lemma* subgroup.subgroup_topological_closure
- \+/\- *def* subgroup.topological_closure
- \+ *lemma* subgroup.topological_closure_minimal

Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/ring.lean
- \+ *lemma* subring.is_closed_topological_closure
- \+ *lemma* subring.subring_topological_closure
- \+ *def* subring.topological_closure
- \+ *lemma* subring.topological_closure_minimal
- \+ *lemma* subsemiring.is_closed_topological_closure
- \+ *lemma* subsemiring.subring_topological_closure
- \+ *def* subsemiring.topological_closure
- \+ *lemma* subsemiring.topological_closure_minimal



## [2021-03-16 19:18:11](https://github.com/leanprover-community/mathlib/commit/8d8c356)
chore(ring_theory/noetherian): add `fg_span` and `fg_span_singleton` ([#6709](https://github.com/leanprover-community/mathlib/pull/6709))
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \+ *theorem* submodule.fg_span
- \+ *theorem* submodule.fg_span_singleton



## [2021-03-16 19:18:09](https://github.com/leanprover-community/mathlib/commit/f221bfd)
feat(data/polynomial/degree/definitions): leading_coeff_X_pow_sub_C ([#6633](https://github.com/leanprover-community/mathlib/pull/6633))
Lemma for the leading coefficient of `X ^ n - C r`.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.leading_coeff_X_pow_sub_C
- \+ *lemma* polynomial.leading_coeff_X_pow_sub_one



## [2021-03-16 19:18:08](https://github.com/leanprover-community/mathlib/commit/81dabda)
feat(data/buffer/parser/*): expand parser properties ([#6339](https://github.com/leanprover-community/mathlib/pull/6339))
Add several new properties to parsers:
`static`
`err_static`
`step`
`prog`
`bounded`
`unfailing`
`conditionally_unfailing`.
Most of these properties hold cleanly for existing core parsers, and are provided as classes. This allows nice derivation for any parsers that are made using parser combinators.
This PR is towards proving that the `nat` parser provides the maximal possible natural.
Other API lemmas are introduced for `string`, `buffer`, `char`, and `array`.
#### Estimated changes
Modified src/data/buffer/basic.lean
- \+ *lemma* buffer.ext_iff
- \+ *lemma* buffer.nth_le_to_list'
- \+ *lemma* buffer.nth_le_to_list
- \+ *lemma* buffer.read_eq_nth_le_to_list
- \+ *lemma* buffer.size_eq_zero_iff
- \+ *lemma* buffer.size_nil
- \+ *lemma* buffer.to_list_nil
- \+ *lemma* buffer.to_list_to_array

Modified src/data/buffer/parser/basic.lean
- \+/\- *lemma* parser.any_char_eq_done
- \+ *lemma* parser.any_char_eq_fail
- \+ *lemma* parser.bounded.char_buf_iff
- \+ *lemma* parser.bounded.decorate_error_iff
- \+ *lemma* parser.bounded.decorate_errors_iff
- \+ *lemma* parser.bounded.done_of_unbounded
- \+ *lemma* parser.bounded.eof
- \+ *lemma* parser.bounded.eps
- \+ *lemma* parser.bounded.exists
- \+ *lemma* parser.bounded.fix
- \+ *lemma* parser.bounded.fix_core
- \+ *lemma* parser.bounded.foldl
- \+ *lemma* parser.bounded.foldl_core
- \+ *lemma* parser.bounded.foldr
- \+ *lemma* parser.bounded.foldr_core
- \+ *lemma* parser.bounded.guard_iff
- \+ *lemma* parser.bounded.many'
- \+ *lemma* parser.bounded.many
- \+ *lemma* parser.bounded.many_char
- \+ *lemma* parser.bounded.of_done
- \+ *lemma* parser.bounded.pure
- \+ *lemma* parser.bounded.remaining
- \+ *lemma* parser.bounded.str_iff
- \+/\- *lemma* parser.ch_eq_done
- \+ *lemma* parser.char_buf_eq_done
- \+ *lemma* parser.conditionally_unfailing.of_fail
- \+/\- *lemma* parser.digit_eq_done
- \+ *lemma* parser.digit_eq_fail
- \+/\- *lemma* parser.eof_eq_done
- \+/\- *lemma* parser.eps_eq_done
- \+ *lemma* parser.err_static.fix
- \+ *lemma* parser.err_static.fix_core
- \+ *lemma* parser.err_static.not_of_ne
- \+ *lemma* parser.exists_done
- \+ *lemma* parser.exists_done_in_bounds
- \+/\- *lemma* parser.guard_eq_done
- \+/\- *lemma* parser.many'_eq_done
- \+ *lemma* parser.many1_bounded_of_done
- \+ *lemma* parser.many1_eq_done_iff_many_eq_done
- \+ *lemma* parser.many1_length_of_done
- \+ *lemma* parser.many_eq_nil_of_done
- \+ *lemma* parser.many_eq_nil_of_out_of_bound
- \+ *lemma* parser.many_sublist_of_done
- \+/\- *lemma* parser.one_of'_eq_done
- \+ *lemma* parser.prog.char_buf_iff
- \+ *lemma* parser.prog.decorate_error_iff
- \+ *lemma* parser.prog.decorate_errors_iff
- \+ *lemma* parser.prog.eof
- \+ *lemma* parser.prog.eps
- \+ *lemma* parser.prog.fix
- \+ *lemma* parser.prog.fix_core
- \+ *lemma* parser.prog.guard_true
- \+ *lemma* parser.prog.pure
- \+ *lemma* parser.prog.remaining
- \+ *lemma* parser.prog.str_iff
- \+ *lemma* parser.remaining_ne_fail
- \+ *lemma* parser.sat_eq_fail
- \+ *lemma* parser.static.any_char
- \+ *lemma* parser.static.ch
- \+ *lemma* parser.static.char_buf_iff
- \+ *lemma* parser.static.digit
- \+ *lemma* parser.static.fix
- \+ *lemma* parser.static.fix_core
- \+ *lemma* parser.static.iff
- \+ *lemma* parser.static.nat
- \+ *lemma* parser.static.not_of_ne
- \+ *lemma* parser.static.one_of'_iff
- \+ *lemma* parser.static.one_of_iff
- \+ *lemma* parser.static.sat_iff
- \+ *lemma* parser.static.str_iff
- \+ *lemma* parser.step.char_buf_iff
- \+ *lemma* parser.step.decorate_error_iff
- \+ *lemma* parser.step.decorate_errors_iff
- \+ *lemma* parser.step.eof
- \+ *lemma* parser.step.eps
- \+ *lemma* parser.step.fix
- \+ *lemma* parser.step.fix_core
- \+ *lemma* parser.step.guard_true
- \+ *lemma* parser.step.not_step_of_static_done
- \+ *lemma* parser.step.pure
- \+ *lemma* parser.step.remaining
- \+ *lemma* parser.step.str_iff
- \+ *lemma* parser.str_eq_char_buf
- \+ *lemma* parser.str_eq_done
- \+ *lemma* parser.unfailing.digit
- \+ *lemma* parser.unfailing.failure
- \+ *lemma* parser.unfailing.foldr_core_zero
- \+ *lemma* parser.unfailing.guard
- \+ *lemma* parser.unfailing.nat
- \+ *lemma* parser.unfailing.of_bounded
- \+ *lemma* parser.unfailing.of_fail
- \+ *lemma* parser.unfailing.sat

Modified src/data/buffer/parser/numeral.lean
- \+/\- *def* parser.numeral.char.of_fintype
- \+/\- *def* parser.numeral.char
- \+/\- *def* parser.numeral.from_one.of_fintype
- \+/\- *def* parser.numeral.from_one
- \+/\- *def* parser.numeral.of_fintype
- \+/\- *def* parser.numeral

Modified src/data/char.lean
- \+ *lemma* char.of_nat_to_nat

Modified src/data/string/basic.lean
- \+ *lemma* list.length_as_string
- \+ *lemma* string.length_to_list



## [2021-03-16 16:06:27](https://github.com/leanprover-community/mathlib/commit/03a6c95)
chore(ring_theory/ideal): use `ideal.mul_mem_left` instead of `ideal.smul_mem` ([#6704](https://github.com/leanprover-community/mathlib/pull/6704))
Lots of proofs are relying on the fact that mul and smul are defeq, but this makes them hard to follow, as the goal state never contains the smul referenced by these lemmas.
#### Estimated changes
Modified src/field_theory/mv_polynomial.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-03-16 16:06:26](https://github.com/leanprover-community/mathlib/commit/d9fbe9d)
chore(geometry/manifold/times_cont_mdiff_map): add `times_cont_mdiff_map.mdifferentiable` ([#6703](https://github.com/leanprover-community/mathlib/pull/6703))
#### Estimated changes
Modified src/geometry/manifold/times_cont_mdiff_map.lean




## [2021-03-16 16:06:25](https://github.com/leanprover-community/mathlib/commit/ffacd12)
feat(algebra/iterate_hom): add `equiv.perm.coe_pow` ([#6698](https://github.com/leanprover-community/mathlib/pull/6698))
Also rewrite `equiv.perm.perm_group` in a more explicit manner.
#### Estimated changes
Modified src/algebra/iterate_hom.lean
- \+ *lemma* equiv.perm.coe_pow
- \+ *lemma* hom_coe_pow
- \+ *lemma* monoid_hom.coe_pow
- \+/\- *lemma* ring_hom.coe_pow

Modified src/group_theory/perm/basic.lean




## [2021-03-16 16:06:23](https://github.com/leanprover-community/mathlib/commit/900963c)
refactor(topology/metric_space/emetric_space): add pseudo_emetric ([#6694](https://github.com/leanprover-community/mathlib/pull/6694))
Working on the Liquid Tensor Experiment, we realize we need seminorms ~~pseudonorms~~ (meaning we don't require `∥x∥ = 0 → x = 0`). For this reason I would like to include seminorms, pseudometric and pseudoemetric to mathlib. (We currently have `premetric_space`, my plan is to change the name to `pseudometric_space`, that seems to be the standard terminology.)
I started modifying `emetric_space` since it seems the more fundamental (looking at the structure of the imports). What I did here is to define a new class `pseudo_emetric_space`, generalize almost all the results about `emetric_space` to this case (I mean, all the results that are actually true) and at the end of the file I defined `emetric_space` and prove the remaining results. It is the first time I did a refactor like this, so I probably did something wrong, but at least it compiles on my computer.
I don't know why one proof in `measure_theory/ae_eq_fun_metric.lean` stopped working, the same proof in tactic mode works.
#### Estimated changes
Modified src/measure_theory/ae_eq_fun_metric.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* edist_eq_zero
- \+/\- *theorem* edist_le_zero
- \+/\- *theorem* edist_pos
- \+/\- *theorem* emetric.ball_prod_same
- \+/\- *theorem* emetric.closed_ball_prod_same
- \+ *theorem* emetric.controlled_of_uniform_embedding
- \+/\- *lemma* emetric.countable_closure_of_compact
- \+/\- *lemma* emetric.second_countable_of_separable
- \+/\- *theorem* emetric.uniform_continuous_iff
- \+/\- *theorem* emetric.uniform_continuous_on_iff
- \- *theorem* emetric.uniform_embedding_iff'
- \+/\- *theorem* emetric.uniform_embedding_iff
- \+/\- *def* emetric_space.induced
- \+/\- *def* emetric_space.replace_uniformity
- \+/\- *theorem* eq_of_forall_edist_le
- \+/\- *lemma* prod.edist_eq
- \+ *lemma* prod.pesudoedist_eq
- \+ *def* pseudo_emetric_space.induced
- \+ *lemma* pseudoedist_pi_const
- \+ *lemma* pseudoedist_pi_def
- \+ *def* pseudoemetric_space.replace_uniformity
- \+ *theorem* uniform_embedding_iff'
- \+ *theorem* uniformity_pseudoedist
- \+/\- *theorem* zero_eq_edist



## [2021-03-16 10:12:38](https://github.com/leanprover-community/mathlib/commit/22eba86)
feat(*): add some missing `coe_*` lemmas ([#6697](https://github.com/leanprover-community/mathlib/pull/6697))
* add `submonoid.coe_pow`, `submonoid.coe_list_prod`,
  `submonoid.coe_multiset_prod`, `submonoid.coe_finset_prod`,
  `subring.coe_pow`, `subring.coe_nat_cast`, `subring.coe_int_cast`;
* add `rat.num_div_denom`;
* add `inv_of_pow`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* inv_of_pow

Modified src/data/rat/basic.lean
- \+ *theorem* rat.num_div_denom

Modified src/group_theory/submonoid/membership.lean
- \+ *theorem* submonoid.coe_finset_prod
- \+ *theorem* submonoid.coe_list_prod
- \+ *theorem* submonoid.coe_multiset_prod
- \+ *theorem* submonoid.coe_pow
- \+/\- *lemma* submonoid.pow_mem

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.coe_int_cast
- \+ *lemma* subring.coe_nat_cast
- \+ *lemma* subring.coe_pow



## [2021-03-16 10:12:37](https://github.com/leanprover-community/mathlib/commit/57de126)
refactor(category_theory/limits): use auto_param ([#6696](https://github.com/leanprover-community/mathlib/pull/6696))
Add an `auto_param`, making it slightly more convenient when build limits of particular shapes first, then all limits.
#### Estimated changes
Modified src/category_theory/limits/constructions/over/default.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/opposites.lean
- \+/\- *lemma* category_theory.limits.has_colimits_op_of_has_limits
- \+/\- *lemma* category_theory.limits.has_limits_op_of_has_colimits

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/kernels.lean




## [2021-03-16 10:12:36](https://github.com/leanprover-community/mathlib/commit/c0036af)
feat(category/is_iso): make is_iso a Prop ([#6662](https://github.com/leanprover-community/mathlib/pull/6662))
Perhaps long overdue, this makes `is_iso` into a Prop.
It hasn't been a big deal, as it was always a subsingleton. Nevertheless this is probably safer than carrying data around in the typeclass inference system. 
As a side effect `simple` is now a Prop as well.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebra/homology/exact.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.is_iso_of_mono_of_epi
- \- *def* category_theory.abelian.is_iso_of_mono_of_epi

Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* category_theory.non_preadditive_abelian.is_iso_of_mono_of_epi
- \- *def* category_theory.non_preadditive_abelian.is_iso_of_mono_of_epi
- \+/\- *abbreviation* category_theory.non_preadditive_abelian.σ

Modified src/category_theory/action.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/mates.lean
- \+ *lemma* category_theory.transfer_nat_trans_self_of_iso
- \- *def* category_theory.transfer_nat_trans_self_of_iso
- \+ *lemma* category_theory.transfer_nat_trans_self_symm_of_iso
- \- *def* category_theory.transfer_nat_trans_self_symm_of_iso

Modified src/category_theory/adjunction/opposites.lean


Modified src/category_theory/adjunction/reflective.lean
- \+ *lemma* category_theory.functor.ess_image.unit_is_iso
- \- *def* category_theory.functor.ess_image.unit_is_iso

Modified src/category_theory/closed/cartesian.lean
- \+ *lemma* category_theory.strict_initial
- \- *def* category_theory.strict_initial

Modified src/category_theory/closed/functor.lean
- \+ *lemma* category_theory.exp_comparison_iso_of_frobenius_morphism_iso
- \- *def* category_theory.exp_comparison_iso_of_frobenius_morphism_iso
- \+ *lemma* category_theory.frobenius_morphism_iso_of_exp_comparison_iso
- \- *def* category_theory.frobenius_morphism_iso_of_exp_comparison_iso

Modified src/category_theory/comma.lean


Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/epi_mono.lean
- \+ *lemma* category_theory.is_iso.of_epi_section
- \- *def* category_theory.is_iso.of_epi_section
- \+ *lemma* category_theory.is_iso.of_mono_retraction
- \- *def* category_theory.is_iso.of_mono_retraction
- \+ *lemma* category_theory.is_iso_of_epi_of_split_mono
- \- *def* category_theory.is_iso_of_epi_of_split_mono
- \+ *lemma* category_theory.is_iso_of_mono_of_split_epi
- \- *def* category_theory.is_iso_of_mono_of_split_epi

Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.inv_eq_to_hom

Modified src/category_theory/fully_faithful.lean
- \+ *lemma* category_theory.is_iso_of_fully_faithful
- \- *def* category_theory.is_iso_of_fully_faithful

Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism.lean
- \+/\- *def* category_theory.as_iso
- \- *lemma* category_theory.functor.map_iso_hom
- \- *lemma* category_theory.functor.map_iso_inv
- \+ *lemma* category_theory.is_iso.eq_inv_of_hom_inv_id
- \+ *lemma* category_theory.is_iso.eq_inv_of_inv_hom_id
- \+/\- *lemma* category_theory.is_iso.hom_inv_id
- \- *lemma* category_theory.is_iso.hom_inv_id_assoc
- \+/\- *lemma* category_theory.is_iso.inv_comp
- \+ *lemma* category_theory.is_iso.inv_eq_of_hom_inv_id
- \+ *lemma* category_theory.is_iso.inv_eq_of_inv_hom_id
- \+/\- *lemma* category_theory.is_iso.inv_hom_id
- \- *lemma* category_theory.is_iso.inv_hom_id_assoc
- \+/\- *lemma* category_theory.is_iso.inv_id
- \+/\- *lemma* category_theory.is_iso.inv_inv
- \+/\- *lemma* category_theory.is_iso.iso.inv_hom
- \+/\- *lemma* category_theory.is_iso.iso.inv_inv
- \+ *def* category_theory.is_iso
- \+ *lemma* category_theory.iso.inv_ext'
- \+ *lemma* category_theory.iso.inv_ext

Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/limits/cones.lean
- \+ *lemma* category_theory.limits.cocones.cocone_iso_of_hom_iso
- \- *def* category_theory.limits.cocones.cocone_iso_of_hom_iso
- \+ *lemma* category_theory.limits.cones.cone_iso_of_hom_iso
- \- *def* category_theory.limits.cones.cone_iso_of_hom_iso

Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.is_colimit.hom_is_iso
- \- *def* category_theory.limits.is_colimit.hom_is_iso
- \+ *lemma* category_theory.limits.is_limit.hom_is_iso
- \- *def* category_theory.limits.is_limit.hom_is_iso

Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.coequalizer.π_of_eq
- \- *def* category_theory.limits.coequalizer.π_of_eq
- \+ *lemma* category_theory.limits.equalizer.ι_of_eq
- \- *def* category_theory.limits.equalizer.ι_of_eq
- \+ *lemma* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_eq
- \- *def* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_eq
- \+ *lemma* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_self
- \- *def* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_self
- \+ *lemma* category_theory.limits.is_iso_limit_cocone_parallel_pair_of_epi
- \- *def* category_theory.limits.is_iso_limit_cocone_parallel_pair_of_epi
- \+ *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_epi
- \- *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_epi
- \+ *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_eq
- \- *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_eq
- \+ *lemma* category_theory.limits.is_iso_limit_cone_parallel_pair_of_self
- \- *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_self

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* category_theory.limits.cokernel.π_of_zero
- \- *def* category_theory.limits.cokernel.π_of_zero
- \+ *lemma* category_theory.limits.kernel.ι_of_zero
- \- *def* category_theory.limits.kernel.ι_of_zero

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *lemma* category_theory.is_iso_of_regular_epi_of_mono
- \- *def* category_theory.is_iso_of_regular_epi_of_mono
- \+ *lemma* category_theory.is_iso_of_regular_mono_of_epi
- \- *def* category_theory.is_iso_of_regular_mono_of_epi

Modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* category_theory.is_iso_of_mono_of_strong_epi

Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean
- \+ *lemma* category_theory.comonad.coalgebra_iso_of_iso
- \- *def* category_theory.comonad.coalgebra_iso_of_iso
- \+ *lemma* category_theory.monad.algebra_iso_of_iso
- \- *def* category_theory.monad.algebra_iso_of_iso

Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monoidal/End.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/functor_category.lean


Modified src/category_theory/monoidal/natural_transformation.lean


Modified src/category_theory/natural_isomorphism.lean
- \+/\- *lemma* category_theory.nat_iso.is_iso_inv_app
- \+ *lemma* category_theory.nat_iso.is_iso_of_is_iso_app
- \- *def* category_theory.nat_iso.is_iso_of_is_iso_app

Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.is_iso_of_op
- \- *def* category_theory.is_iso_of_op

Modified src/category_theory/over.lean


Modified src/category_theory/preadditive/biproducts.lean
- \+ *lemma* category_theory.is_iso_left_of_is_iso_biprod_map
- \- *def* category_theory.is_iso_left_of_is_iso_biprod_map
- \+ *lemma* category_theory.is_iso_right_of_is_iso_biprod_map
- \- *def* category_theory.is_iso_right_of_is_iso_biprod_map

Modified src/category_theory/preadditive/schur.lean
- \+ *lemma* category_theory.is_iso_of_hom_simple
- \- *def* category_theory.is_iso_of_hom_simple

Modified src/category_theory/products/associator.lean


Modified src/category_theory/reflects_isomorphisms.lean
- \+ *lemma* category_theory.is_iso_of_reflects_iso
- \- *def* category_theory.is_iso_of_reflects_iso

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.is_iso_of_epi_of_nonzero
- \- *def* category_theory.is_iso_of_epi_of_nonzero
- \+ *lemma* category_theory.is_iso_of_mono_of_nonzero
- \- *def* category_theory.is_iso_of_mono_of_nonzero
- \- *lemma* category_theory.simple.ext
- \+ *lemma* category_theory.simple_of_cosimple
- \- *def* category_theory.simple_of_cosimple

Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sieves.lean


Modified src/category_theory/subterminal.lean
- \+ *lemma* category_theory.is_subterminal.is_iso_diag
- \- *def* category_theory.is_subterminal.is_iso_diag

Modified src/category_theory/types.lean
- \- *def* category_theory.is_iso_equiv_bijective
- \+ *lemma* category_theory.is_iso_iff_bijective

Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean
- \+ *lemma* category_theory.coyoneda.is_iso
- \- *def* category_theory.coyoneda.is_iso
- \+ *lemma* category_theory.yoneda.is_iso
- \- *def* category_theory.yoneda.is_iso

Modified src/topology/category/TopCommRing.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/presheaf.lean
- \+/\- *lemma* Top.presheaf.pushforward_eq_hom_app



## [2021-03-16 06:30:41](https://github.com/leanprover-community/mathlib/commit/6669a28)
feat(algebraic_topology/simplicial_object + ...): Add has_limits + has_colimits instances ([#6695](https://github.com/leanprover-community/mathlib/pull/6695))
This PR adds `has_limits` and `has_colimits` instances for the category of simplicial objects (assuming the existence of such an instance for the base category). The category of simplicial sets now has both limits and colimits, and we include a small example of a simplicial set (the circle) constructed as a colimit.
This PR also includes the following two components, which were required for the above:
1. A basic API for working with `ulift C` where `C` is a category. This was required to avoid some annoying universe issues in the definitions of `has_colimits` and `has_limits`.
2. A small shim that transports a `has_(co)limit` instance along an equivalence of categories.
#### Estimated changes
Modified src/algebraic_topology/simplicial_object.lean


Modified src/algebraic_topology/simplicial_set.lean


Modified src/category_theory/adjunction/limits.lean
- \+ *lemma* category_theory.adjunction.has_colimits_of_equivalence
- \+ *lemma* category_theory.adjunction.has_colimits_of_shape_of_equivalence
- \+ *lemma* category_theory.adjunction.has_limits_of_equivalence
- \+ *lemma* category_theory.adjunction.has_limits_of_shape_of_equivalence

Added src/category_theory/category/ulift.lean
- \+ *def* category_theory.ulift.down
- \+ *def* category_theory.ulift.equivalence
- \+ *def* category_theory.ulift.up



## [2021-03-16 06:30:40](https://github.com/leanprover-community/mathlib/commit/6d7d169)
feat(topology): More lemmas from LTE, refactor `is_totally_disconnected` to use `set.subsingleton` ([#6673](https://github.com/leanprover-community/mathlib/pull/6673))
From the liquid tensor experiment
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_iff_singleton

Modified src/topology/connected.lean
- \+ *lemma* embedding.is_totally_disconnected
- \+ *lemma* is_preconnected.subsingleton
- \+ *lemma* is_totally_disconnected_of_image
- \+ *lemma* is_totally_disconnected_of_totally_disconnected_space

Modified src/topology/maps.lean
- \+ *lemma* inducing.is_open_iff

Modified src/topology/separation.lean
- \+ *lemma* embedding.t2_space

Modified src/topology/subset_properties.lean
- \+ *lemma* inducing.is_compact_iff



## [2021-03-16 04:37:30](https://github.com/leanprover-community/mathlib/commit/0176b42)
feat(ring_theory/finiteness): add `mv_polynomial_of_finite_presentation` ([#6512](https://github.com/leanprover-community/mathlib/pull/6512))
Add `mv_polynomial_of_finite_presentation`: the polynomial ring over a finitely presented algebra is finitely presented.
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* algebra.finite_presentation.iff
- \+ *lemma* algebra.finite_presentation.mv_polynomial_of_finite_presentation

Modified src/ring_theory/noetherian.lean
- \+ *lemma* submodule.map_fg_of_fg



## [2021-03-16 03:41:52](https://github.com/leanprover-community/mathlib/commit/afe38ca)
chore(scripts): update nolints.txt ([#6702](https://github.com/leanprover-community/mathlib/pull/6702))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-15 22:29:25](https://github.com/leanprover-community/mathlib/commit/f1b69a1)
feat(linear_algebra/quadratic_form): add nondegenerate_of_anisotropic ([#6692](https://github.com/leanprover-community/mathlib/pull/6692))
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* bilin_form.nondegenerate_of_anisotropic
- \+ *lemma* quadratic_form.nondegenerate_of_anisotropic



## [2021-03-15 22:29:23](https://github.com/leanprover-community/mathlib/commit/ddb4617)
refactor(topology/metric_space/isometry): move Kuratowski embedding to another file ([#6678](https://github.com/leanprover-community/mathlib/pull/6678))
This reduces the import dependencies of `topology.metric_space.isometry`.
#### Estimated changes
Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean
- \- *def* Kuratowski_embedding.embedding_of_subset
- \- *lemma* Kuratowski_embedding.embedding_of_subset_coe
- \- *lemma* Kuratowski_embedding.embedding_of_subset_dist_le
- \- *lemma* Kuratowski_embedding.embedding_of_subset_isometry
- \- *theorem* Kuratowski_embedding.exists_isometric_embedding
- \- *def* Kuratowski_embedding
- \- *def* nonempty_compacts.Kuratowski_embedding
- \- *def* ℓ_infty_ℝ

Added src/topology/metric_space/kuratowski.lean
- \+ *def* Kuratowski_embedding.embedding_of_subset
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_coe
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_dist_le
- \+ *lemma* Kuratowski_embedding.embedding_of_subset_isometry
- \+ *theorem* Kuratowski_embedding.exists_isometric_embedding
- \+ *def* Kuratowski_embedding
- \+ *def* nonempty_compacts.Kuratowski_embedding
- \+ *def* ℓ_infty_ℝ



## [2021-03-15 22:29:22](https://github.com/leanprover-community/mathlib/commit/cc48a5a)
feat(geometry/manifold/diffeomorph): expand API ([#6668](https://github.com/leanprover-community/mathlib/pull/6668))
#### Estimated changes
Modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* continuous_linear_equiv.coe_to_diffeomorph
- \+ *lemma* continuous_linear_equiv.coe_to_diffeomorph_symm
- \+ *lemma* continuous_linear_equiv.symm_to_diffeomorph
- \+ *def* continuous_linear_equiv.to_diffeomorph
- \+ *lemma* diffeomorph.apply_symm_apply
- \+ *lemma* diffeomorph.coe_coe
- \+ *lemma* diffeomorph.coe_fn_injective
- \+ *lemma* diffeomorph.coe_refl
- \+ *lemma* diffeomorph.coe_to_equiv
- \+ *lemma* diffeomorph.coe_to_homeomorph
- \+ *lemma* diffeomorph.coe_to_homeomorph_symm
- \+ *lemma* diffeomorph.coe_trans
- \+ *lemma* diffeomorph.ext
- \+ *lemma* diffeomorph.image_eq_preimage
- \+ *lemma* diffeomorph.image_symm_image
- \+ *lemma* diffeomorph.range_comp
- \+ *lemma* diffeomorph.refl_to_equiv
- \+ *lemma* diffeomorph.refl_trans
- \+ *lemma* diffeomorph.smooth_trans_diffeomorph_left
- \+ *lemma* diffeomorph.smooth_trans_diffeomorph_right
- \+ *lemma* diffeomorph.symm_apply_apply
- \+ *lemma* diffeomorph.symm_image_eq_preimage
- \+ *lemma* diffeomorph.symm_image_image
- \+ *lemma* diffeomorph.symm_refl
- \+ *lemma* diffeomorph.symm_to_equiv
- \+ *lemma* diffeomorph.symm_to_homeomorph
- \+ *lemma* diffeomorph.symm_trans'
- \+ *lemma* diffeomorph.symm_trans
- \+ *lemma* diffeomorph.times_cont_mdiff_at_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_at_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_at_trans_diffeomorph_left
- \+ *lemma* diffeomorph.times_cont_mdiff_at_trans_diffeomorph_right
- \+ *lemma* diffeomorph.times_cont_mdiff_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_on_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_on_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_on_trans_diffeomorph_left
- \+ *lemma* diffeomorph.times_cont_mdiff_on_trans_diffeomorph_right
- \+ *lemma* diffeomorph.times_cont_mdiff_trans_diffeomorph_left
- \+ *lemma* diffeomorph.times_cont_mdiff_trans_diffeomorph_right
- \+ *lemma* diffeomorph.times_cont_mdiff_within_at_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_within_at_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.times_cont_mdiff_within_at_trans_diffeomorph_left
- \+ *lemma* diffeomorph.times_cont_mdiff_within_at_trans_diffeomorph_right
- \+ *lemma* diffeomorph.to_equiv_coe_symm
- \+ *lemma* diffeomorph.to_equiv_inj
- \+ *lemma* diffeomorph.to_equiv_injective
- \+ *def* diffeomorph.to_homeomorph
- \+ *lemma* diffeomorph.to_homeomorph_to_equiv
- \+ *lemma* diffeomorph.to_local_homeomorph_mdifferentiable
- \+ *def* diffeomorph.to_trans_diffeomorph
- \+ *lemma* diffeomorph.trans_refl
- \+ *lemma* diffeomorph.trans_symm
- \+ *lemma* diffeomorph.unique_diff_on_image
- \+ *lemma* diffeomorph.unique_diff_on_preimage
- \+ *lemma* diffeomorph.unique_mdiff_on_image
- \+ *lemma* diffeomorph.unique_mdiff_on_image_aux
- \+ *lemma* diffeomorph.unique_mdiff_on_preimage
- \+ *structure* diffeomorph
- \- *def* diffeomorph
- \+ *lemma* model_with_corners.coe_ext_chart_at_trans_diffeomorph
- \+ *lemma* model_with_corners.coe_ext_chart_at_trans_diffeomorph_symm
- \+ *lemma* model_with_corners.coe_trans_diffeomorph
- \+ *lemma* model_with_corners.coe_trans_diffeomorph_symm
- \+ *lemma* model_with_corners.ext_chart_at_trans_diffeomorph_target
- \+ *def* model_with_corners.trans_diffeomorph
- \+ *lemma* model_with_corners.trans_diffeomorph_range
- \- *lemma* times_diffeomorph.coe_eq_to_equiv
- \- *structure* times_diffeomorph

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* times_cont_mdiff_at.comp_times_cont_mdiff_within_at



## [2021-03-15 22:29:21](https://github.com/leanprover-community/mathlib/commit/bd386a8)
feat(measure_theory/outer_measure): golf, add lemmas ([#6664](https://github.com/leanprover-community/mathlib/pull/6664))
* `Union_of_tendsto_zero`, `Union_nat_of_monotone_of_tsum_ne_top`, `of_function_union_of_separated`:
  supporting lemmas for the upcoming definition of the Hausdorff
  measure (and more generally metric outer measures).
* `ext_nonempty`, `smul_supr`, `map_sup`, `map_supr`, `comap_supr`,
  `restrict_univ`, `restrict_empty`, `restrict_supr`, `map_comap`,
  `map_comap_le`, `map_comap_of_surjective`, `restrict_le_self`,
  `map_le_restrict_range`, `le_comap_map`, `comap_map`, `comap_top`,
  `top_apply'`, `map_top`, `map_top_of_surjective`: new API lemmas
  about `map`/`comap`/`restrict` and `sup`/`supr`/`top`;
* `is_greatest_of_function`, `of_function_eq_Sup`,
`comap_of_function`, `map_of_function_le`, `map_of_function`,
restrict_of_function`, `smul_of_function`: new lemmas about
`of_function`;
* `Inf_apply'`: a version of `Inf_apply` that assumes that another set
is nonempty;
* `infi_apply`, `infi_apply'`, `binfi_apply`, `binfi_apply'`,
`map_infi_le`, `comap_infi`, `map_infi`, `map_infi_comap`,
`map_binfi_comap`, `restrict_infi_restrict`, `restrict_infi`,
`restrict_binfi`: new lemmas about `map`/`comap`/`restrict` and
`Inf`/`infi`;
* `extend_congr`: `infi_congr_Prop` specialized for `extend`; why this
is not a `congr` lemma?
* `le_induced_outer_measure`: `le_of_function` for
`induced_outer_measure`;
* `trim_le_trim` → `trim_mono`: rename, use `monotone`;
* `exists_measurable_superset_forall_eq_trim`: a version of
`exists_measurable_superset_eq_trim` that works for countable families
of measures;
* `trim_binop`, `trim_op`: new helper lemmas to golf `trim_add` etc;
* `trim_sup`, `trim_supr`: new lemmas about `trim`.
* `map_mono`, `comap_mono`, `mono''`, `restrict_mono`, `trim_mono`:
`@[mono]` lemmas.
#### Estimated changes
Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.extend_congr
- \+ *lemma* measure_theory.induced_outer_measure_union_of_false_of_nonempty_inter
- \+ *lemma* measure_theory.le_induced_outer_measure
- \+ *lemma* measure_theory.outer_measure.Inf_apply'
- \+ *lemma* measure_theory.outer_measure.Union_nat_of_monotone_of_tsum_ne_top
- \+ *lemma* measure_theory.outer_measure.Union_of_tendsto_zero
- \+ *lemma* measure_theory.outer_measure.binfi_apply'
- \+ *lemma* measure_theory.outer_measure.binfi_apply
- \+ *lemma* measure_theory.outer_measure.comap_infi
- \+ *lemma* measure_theory.outer_measure.comap_map
- \+ *lemma* measure_theory.outer_measure.comap_mono
- \+ *lemma* measure_theory.outer_measure.comap_of_function
- \+ *theorem* measure_theory.outer_measure.comap_supr
- \+ *theorem* measure_theory.outer_measure.comap_top
- \+ *lemma* measure_theory.outer_measure.exists_measurable_superset_forall_eq_trim
- \+ *lemma* measure_theory.outer_measure.ext_nonempty
- \+ *lemma* measure_theory.outer_measure.infi_apply'
- \+ *lemma* measure_theory.outer_measure.infi_apply
- \+ *lemma* measure_theory.outer_measure.is_greatest_of_function
- \+ *lemma* measure_theory.outer_measure.le_comap_map
- \+ *lemma* measure_theory.outer_measure.map_binfi_comap
- \+ *lemma* measure_theory.outer_measure.map_comap
- \+ *lemma* measure_theory.outer_measure.map_comap_le
- \+ *lemma* measure_theory.outer_measure.map_comap_of_surjective
- \+ *lemma* measure_theory.outer_measure.map_infi
- \+ *lemma* measure_theory.outer_measure.map_infi_comap
- \+ *lemma* measure_theory.outer_measure.map_infi_le
- \+ *lemma* measure_theory.outer_measure.map_le_restrict_range
- \+ *theorem* measure_theory.outer_measure.map_mono
- \+ *lemma* measure_theory.outer_measure.map_of_function
- \+ *lemma* measure_theory.outer_measure.map_of_function_le
- \+ *theorem* measure_theory.outer_measure.map_sup
- \+ *theorem* measure_theory.outer_measure.map_supr
- \+ *theorem* measure_theory.outer_measure.map_top
- \+ *theorem* measure_theory.outer_measure.map_top_of_surjective
- \+ *lemma* measure_theory.outer_measure.mono''
- \+ *lemma* measure_theory.outer_measure.of_function_eq_Sup
- \+ *lemma* measure_theory.outer_measure.of_function_union_of_top_of_nonempty_inter
- \+ *lemma* measure_theory.outer_measure.restrict_binfi
- \+ *lemma* measure_theory.outer_measure.restrict_empty
- \+ *lemma* measure_theory.outer_measure.restrict_infi
- \+ *lemma* measure_theory.outer_measure.restrict_infi_restrict
- \+ *lemma* measure_theory.outer_measure.restrict_le_self
- \+ *lemma* measure_theory.outer_measure.restrict_mono
- \+ *lemma* measure_theory.outer_measure.restrict_of_function
- \+ *lemma* measure_theory.outer_measure.restrict_supr
- \+ *lemma* measure_theory.outer_measure.restrict_univ
- \+ *lemma* measure_theory.outer_measure.smul_of_function
- \+ *theorem* measure_theory.outer_measure.smul_supr
- \+ *theorem* measure_theory.outer_measure.top_apply'
- \+/\- *theorem* measure_theory.outer_measure.top_apply
- \+ *theorem* measure_theory.outer_measure.trim_binop
- \- *theorem* measure_theory.outer_measure.trim_le_trim
- \+ *theorem* measure_theory.outer_measure.trim_mono
- \+ *theorem* measure_theory.outer_measure.trim_op
- \+ *theorem* measure_theory.outer_measure.trim_sup
- \+ *lemma* measure_theory.outer_measure.trim_supr



## [2021-03-15 18:15:30](https://github.com/leanprover-community/mathlib/commit/c358676)
feat(meta/expr): monadic analogue of expr.replace ([#6661](https://github.com/leanprover-community/mathlib/pull/6661))
#### Estimated changes
Modified src/data/option/defs.lean
- \+ *def* option.melim
- \+ *def* option.mget_or_else

Modified src/meta/expr.lean




## [2021-03-15 18:15:29](https://github.com/leanprover-community/mathlib/commit/3ec8c1d)
feat(algebra/direct_sum_graded): a direct_sum formed of powers of a submodule of an algebra inherits a ring structure ([#6550](https://github.com/leanprover-community/mathlib/pull/6550))
This also fixes some incorrect universe parameters to the `of_submodules` constructors.
#### Estimated changes
Modified src/algebra/direct_sum_graded.lean
- \+/\- *def* direct_sum.gcomm_monoid.of_add_subgroups
- \+/\- *def* direct_sum.gcomm_monoid.of_add_submonoids
- \+/\- *def* direct_sum.gcomm_monoid.of_submodules
- \+/\- *def* direct_sum.ghas_mul.of_add_subgroups
- \+/\- *def* direct_sum.ghas_mul.of_add_submonoids
- \+/\- *def* direct_sum.ghas_mul.of_submodules
- \+/\- *def* direct_sum.ghas_one.of_add_subgroups
- \+/\- *def* direct_sum.ghas_one.of_add_submonoids
- \+/\- *def* direct_sum.ghas_one.of_submodules
- \+/\- *def* direct_sum.gmonoid.of_add_subgroups
- \+/\- *def* direct_sum.gmonoid.of_add_submonoids
- \+/\- *def* direct_sum.gmonoid.of_submodules



## [2021-03-15 17:06:11](https://github.com/leanprover-community/mathlib/commit/d9dc30e)
feat(algebra/free): turn `free_magma.lift` into an equivalence ([#6672](https://github.com/leanprover-community/mathlib/pull/6672))
This will be convenient for some work I have in mind and is more consistent with the pattern used elsewhere, such as:
- [`free_algebra.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/free_algebra.html#free_algebra.lift)
- [`monoid_algebra.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/monoid_algebra.html#monoid_algebra.lift)
- [`universal_enveloping.lift`](https://leanprover-community.github.io/mathlib_docs/algebra/lie/universal_enveloping.html#universal_enveloping_algebra.lift)
- ...
#### Estimated changes
Modified src/algebra/free.lean
- \- *def* free_add_magma.lift
- \+ *def* free_add_magma.lift_aux
- \+/\- *def* free_magma.lift
- \+ *def* free_magma.lift_aux
- \+ *theorem* free_magma.lift_aux_unique
- \- *lemma* free_magma.lift_mul
- \- *theorem* free_magma.lift_unique



## [2021-03-15 15:39:13](https://github.com/leanprover-community/mathlib/commit/ae77628)
chore(geometry/manifold/times_cont_mdiff): add `prod_mk_space` versions of `prod_mk` lemmas ([#6681](https://github.com/leanprover-community/mathlib/pull/6681))
These lemmas are useful when dealing with maps `f : M → E' × F'` where
`E'` and `F'` are normed spaces. This means some code duplication with
`prod_mk` lemmas but I see no way to avoid this without making proofs
about `M → E' × F'` longer/harder.
#### Estimated changes
Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth.prod_mk_space
- \+ *lemma* smooth_at.prod_mk_space
- \+ *lemma* smooth_on.prod_mk_space
- \+ *lemma* smooth_within_at.prod_mk_space
- \+ *lemma* times_cont_mdiff.prod_mk_space
- \+ *lemma* times_cont_mdiff_at.prod_mk_space
- \+ *lemma* times_cont_mdiff_on.prod_mk_space
- \+ *lemma* times_cont_mdiff_within_at.prod_mk_space



## [2021-03-15 12:40:53](https://github.com/leanprover-community/mathlib/commit/e16ae24)
doc(readme): add Eric Wieser to maintainer list ([#6688](https://github.com/leanprover-community/mathlib/pull/6688))
#### Estimated changes
Modified README.md




## [2021-03-15 12:40:52](https://github.com/leanprover-community/mathlib/commit/b5f3832)
feat(topology/metric_space): introduce `is_metric_separated` ([#6685](https://github.com/leanprover-community/mathlib/pull/6685))
#### Estimated changes
Added src/topology/metric_space/metric_separated.lean
- \+ *lemma* is_metric_separated.comm
- \+ *lemma* is_metric_separated.empty_left
- \+ *lemma* is_metric_separated.empty_right
- \+ *lemma* is_metric_separated.finite_Union_left_iff
- \+ *lemma* is_metric_separated.finite_Union_right_iff
- \+ *lemma* is_metric_separated.finset_Union_left_iff
- \+ *lemma* is_metric_separated.finset_Union_right_iff
- \+ *lemma* is_metric_separated.mono
- \+ *lemma* is_metric_separated.mono_left
- \+ *lemma* is_metric_separated.mono_right
- \+ *lemma* is_metric_separated.subset_compl_right
- \+ *lemma* is_metric_separated.symm
- \+ *lemma* is_metric_separated.union_left
- \+ *lemma* is_metric_separated.union_left_iff
- \+ *lemma* is_metric_separated.union_right
- \+ *lemma* is_metric_separated.union_right_iff
- \+ *def* is_metric_separated



## [2021-03-15 12:40:51](https://github.com/leanprover-community/mathlib/commit/90db6fc)
feat(analysis/calculus/times_cont_diff): smoothness of `f : E → Π i, F i` ([#6674](https://github.com/leanprover-community/mathlib/pull/6674))
Also add helper lemmas/definitions about multilinear maps.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on_pi'
- \+ *lemma* has_ftaylor_series_up_to_on_pi
- \+ *lemma* times_cont_diff_at_pi
- \+ *lemma* times_cont_diff_on_pi
- \+ *lemma* times_cont_diff_pi
- \+ *lemma* times_cont_diff_within_at_pi

Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.norm_pi
- \+ *def* continuous_multilinear_map.piₗᵢ

Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth_at_pi_space
- \+ *lemma* smooth_on_pi_space
- \+ *lemma* smooth_pi_space
- \+ *lemma* smooth_within_at_pi_space
- \+ *lemma* times_cont_mdiff_at_pi_space
- \+ *lemma* times_cont_mdiff_on_pi_space
- \+ *lemma* times_cont_mdiff_pi_space
- \+ *lemma* times_cont_mdiff_within_at_pi_space

Modified src/linear_algebra/multilinear.lean
- \+ *def* multilinear_map.pi

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* continuous_multilinear_map.coe_pi
- \+ *def* continuous_multilinear_map.pi
- \+ *lemma* continuous_multilinear_map.pi_apply



## [2021-03-15 09:03:13](https://github.com/leanprover-community/mathlib/commit/1f47833)
feat(algebra/*, * : [regular, smul_with_zero, module/basic]): introduce `mul_action_with_zero` and `M`-regular elements ([#6590](https://github.com/leanprover-community/mathlib/pull/6590))
This PR has been split and there are now two separate PRs.
* [#6590](https://github.com/leanprover-community/mathlib/pull/6590), this one, introducing `smul_with_zero` and `mul_action_with_zero`: two typeclasses to deal with multiplicative actions of `monoid_with_zero`, without the need to assume the presence of an addition!
* [#6659](https://github.com/leanprover-community/mathlib/pull/6659), introducing `M`-regular elements, called `smul_regular`: the analogue of `is_left_regular`, but defined for an action of `monoid_with_zero` on a module `M`.
This PR is a preparation for introducing `M`-regular elements.
From the doc-string:
### Introduce `smul_with_zero`
In analogy with the usual monoid action on a Type `M`, we introduce an action of a `monoid_with_zero` on a Type with `0`.
In particular, for Types `R` and `M`, both containing `0`, we define `smul_with_zero R M` to be the typeclass where the products `r • 0` and `0 • m` vanish for all `r ∈ R` and all `m ∈ M`.
Moreover, in the case in which `R` is a `monoid_with_zero`, we introduce the typeclass `mul_action_with_zero R M`, mimicking group actions and having an absorbing `0` in `R`.  Thus, the action is required to be compatible with
* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.
Next, in a separate file, I introduce `M`-regular elements for a `monoid_with_zero R` with a `mul_action_with_zero` on a module `M`.  The definition is simply to require that an element `a : R` is `M`-regular if the smultiplication `M → M`, given by `m ↦ a • m` is injective.
We also prove some basic facts about `M`-regular elements.
The PR further changes three further the files
* `data/polynomial/coeffs`;
* `topology/algebra/module.lean`;
* `analysis/normed_space/bounded_linear_maps`.
The changes are prompted by a failure in CI.  In each case, the change was tiny, mostly having to do with an exchange of a multiplication by a smultiplication or vice-versa.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *theorem* zero_smul

Modified src/algebra/regular.lean
- \+ *lemma* not_is_left_regular_zero
- \+ *lemma* not_is_regular_zero
- \+ *lemma* not_is_right_regular_zero

Added src/algebra/smul_with_zero.lean
- \+ *lemma* zero_smul

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/data/polynomial/coeff.lean


Modified src/topology/algebra/module.lean




## [2021-03-15 09:03:12](https://github.com/leanprover-community/mathlib/commit/abf2ab4)
feat(linear_algebra/quadratic_form): associated bilinear form over noncommutative rings ([#6585](https://github.com/leanprover-community/mathlib/pull/6585))
The `associated` bilinear form to a quadratic form is currently constructed for commutative rings, but nearly the same construction works without a commutativity hypothesis (the only part that fails is that the operation of performing the construction is now an `add_monoid_hom` rather than a `linear_map`.  I provide this construction, naming it `associated'`.
Needed for [#5814](https://github.com/leanprover-community/mathlib/pull/5814) (not exactly a dependency since we can merge a non-optimal version of that PR before this one is merged).
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *theorem* commute.inv_of_left
- \+ *theorem* commute.inv_of_right

Modified src/algebra/ring/basic.lean
- \+ *lemma* commute.bit0_left
- \+ *lemma* commute.bit0_right
- \+ *lemma* commute.bit1_left
- \+ *lemma* commute.bit1_right

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.zero_apply

Modified src/linear_algebra/quadratic_form.lean
- \+/\- *lemma* bilin_form.exists_bilin_form_self_neq_zero
- \+ *abbreviation* quadratic_form.associated'
- \+ *abbreviation* quadratic_form.associated
- \- *def* quadratic_form.associated
- \+/\- *lemma* quadratic_form.associated_comp
- \+/\- *lemma* quadratic_form.associated_eq_self_apply
- \+ *def* quadratic_form.associated_hom
- \+/\- *lemma* quadratic_form.associated_is_sym
- \+/\- *lemma* quadratic_form.associated_right_inverse
- \+/\- *lemma* quadratic_form.associated_to_quadratic_form



## [2021-03-15 07:04:07](https://github.com/leanprover-community/mathlib/commit/249fd4f)
refactor(data/polynomial,ring_theory): use big operators for polynomials ([#6616](https://github.com/leanprover-community/mathlib/pull/6616))
This untangles some more definitions on polynomials from finsupp.  This uses the same approach as in [#6605](https://github.com/leanprover-community/mathlib/pull/6605).
#### Estimated changes
Modified src/data/polynomial/div.lean
- \+ *lemma* polynomial.coeff_div_X

Modified src/data/polynomial/integral_normalization.lean
- \+/\- *lemma* polynomial.integral_normalization_aeval_eq_zero
- \+ *lemma* polynomial.integral_normalization_coeff
- \+/\- *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \+ *lemma* polynomial.integral_normalization_support
- \+ *lemma* polynomial.integral_normalization_zero
- \+/\- *lemma* polynomial.support_integral_normalization

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/polynomial/scale_roots.lean




## [2021-03-15 01:08:57](https://github.com/leanprover-community/mathlib/commit/c5796c7)
chore(scripts): update nolints.txt ([#6686](https://github.com/leanprover-community/mathlib/pull/6686))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2021-03-14 15:45:18](https://github.com/leanprover-community/mathlib/commit/0a16148)
feat(measure_theory/lp_space): add snorm_norm_rpow ([#6619](https://github.com/leanprover-community/mathlib/pull/6619))
The lemma `snorm_norm_rpow` states `snorm (λ x, ∥f x∥ ^ q) p μ = (snorm f (p * ennreal.of_real q) μ) ^ q`.
Also add measurability lemmas about pow/rpow.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ae_measurable.rpow_const
- \+ *lemma* ennreal.of_real_rpow_of_nonneg
- \+ *lemma* ennreal.of_real_rpow_of_pos
- \+ *lemma* real.abs_rpow_of_nonneg
- \+ *lemma* real.norm_rpow_of_nonneg

Modified src/measure_theory/borel_space.lean
- \+ *lemma* ae_measurable.pow
- \+ *lemma* measurable.pow
- \+ *lemma* measurable_pow

Modified src/measure_theory/lp_space.lean
- \+/\- *lemma* measure_theory.snorm'_norm
- \+ *lemma* measure_theory.snorm'_norm_rpow
- \+ *lemma* measure_theory.snorm_norm_rpow



## [2021-03-14 12:22:07](https://github.com/leanprover-community/mathlib/commit/feab14b)
fix(algebra/continued_fractions): fix import ([#6677](https://github.com/leanprover-community/mathlib/pull/6677))
Just fix an import
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean




## [2021-03-14 10:50:39](https://github.com/leanprover-community/mathlib/commit/b48cf17)
feat(linear_algebra/alternating): Add dom_coprod ([#5269](https://github.com/leanprover-community/mathlib/pull/5269))
This implements a variant of the multiplication defined in the second half of [Proposition 22.24 of "Notes on Differential Geometry and Lie Groups" (Jean Gallier)](https://www.cis.upenn.edu/~cis610/diffgeom-n.pdf):
![image](https://user-images.githubusercontent.com/425260/104042315-3dfe7380-51d2-11eb-9b3a-bbbb52d180f0.png)
#### Estimated changes
Modified docs/references.bib


Modified src/linear_algebra/alternating.lean
- \+ *lemma* alternating_map.coe_multilinear_map_injective
- \+ *def* alternating_map.dom_coprod'
- \+ *lemma* alternating_map.dom_coprod'_apply
- \+ *def* alternating_map.dom_coprod.summand
- \+ *lemma* alternating_map.dom_coprod.summand_add_swap_smul_eq_zero
- \+ *lemma* alternating_map.dom_coprod.summand_eq_zero_of_smul_invariant
- \+ *lemma* alternating_map.dom_coprod.summand_mk'
- \+ *def* alternating_map.dom_coprod
- \+ *lemma* alternating_map.dom_coprod_coe
- \+ *lemma* equiv.perm.mod_sum_congr.swap_smul_involutive
- \+ *abbreviation* equiv.perm.mod_sum_congr
- \+ *lemma* multilinear_map.dom_coprod_alternization
- \+ *lemma* multilinear_map.dom_coprod_alternization_coe
- \+ *lemma* multilinear_map.dom_coprod_alternization_eq



## [2021-03-14 06:52:22](https://github.com/leanprover-community/mathlib/commit/b52337a)
feat(topology/algebra/group): Add two easy lemmas ([#6669](https://github.com/leanprover-community/mathlib/pull/6669))
A topological group is discrete as soon as {1} is open.
The closure of a subgroup is a subgroup.
From the liquid tensor experiment.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* discrete_topology_of_open_singleton_one
- \+ *def* subgroup.topological_closure

Modified src/topology/basic.lean
- \+ *lemma* closure_subset_preimage_closure_image



## [2021-03-14 03:22:20](https://github.com/leanprover-community/mathlib/commit/464d04a)
feat(data/nat/fincard): introduce `nat.card`, `enat.card` ([#6670](https://github.com/leanprover-community/mathlib/pull/6670))
Defines `nat`- and `enat`-valued cardinality functions.
#### Estimated changes
Added src/data/fincard.lean
- \+ *def* enat.card
- \+ *lemma* enat.card_eq_coe_fintype_card
- \+ *lemma* enat.card_eq_top_of_infinite
- \+ *def* nat.card
- \+ *lemma* nat.card_eq_fintype_card
- \+ *lemma* nat.card_eq_zero_of_infinite



## [2021-03-14 03:22:18](https://github.com/leanprover-community/mathlib/commit/70662e1)
chore(data/rat/basic): a few trivial lemmas about `rat.denom` ([#6667](https://github.com/leanprover-community/mathlib/pull/6667))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *theorem* rat.add_denom_dvd
- \+/\- *lemma* rat.denom_neg_eq_denom
- \+ *lemma* rat.denom_zero
- \+ *theorem* rat.mk_pnat_denom_dvd
- \+ *theorem* rat.mul_denom_dvd
- \+/\- *lemma* rat.num_neg_eq_neg_num

Modified src/data/rat/order.lean




## [2021-03-14 03:22:18](https://github.com/leanprover-community/mathlib/commit/69d7134)
feat(topology/basic): `f =ᶠ[𝓝 a] 0` iff `a ∉ closure (support f)` ([#6665](https://github.com/leanprover-community/mathlib/pull/6665))
Also add `equiv.image_symm_image` and `function.compl_support`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.image_symm_image
- \+/\- *lemma* equiv.symm_image_image

Modified src/data/support.lean
- \+ *lemma* function.compl_support

Modified src/topology/basic.lean
- \+ *lemma* eventually_eq_zero_nhds



## [2021-03-14 03:22:17](https://github.com/leanprover-community/mathlib/commit/c928e34)
feat(data/real/ennreal,topology/*): assorted lemmas ([#6663](https://github.com/leanprover-community/mathlib/pull/6663))
* add `@[simp]` to `ennreal.coe_nat_lt_coe_nat` and `ennreal.coe_nat_le_coe_nat`;
* add `ennreal.le_of_add_le_add_right`;
* add `set.nonempty.preimage`;
* add `ennreal.infi_mul_left'` and `ennreal.infi_mul_right'`;
* add `ennreal.tsum_top`;
* add `emetric.diam_closure`;
* add `edist_pos`;
* add `isometric.bijective`, `isometric.injective`, and `isometric.surjective`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_nat_le_coe_nat
- \+/\- *lemma* ennreal.coe_nat_lt_coe_nat
- \+ *lemma* ennreal.le_of_add_le_add_right

Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty.preimage

Modified src/topology/instances/ennreal.lean
- \+ *lemma* emetric.diam_closure
- \+ *lemma* ennreal.infi_mul_left'
- \+ *lemma* ennreal.infi_mul_right'

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* edist_pos

Modified src/topology/metric_space/isometry.lean




## [2021-03-14 03:22:15](https://github.com/leanprover-community/mathlib/commit/1e9f664)
refactor(ring_theory/discrete_valuation_ring): `discrete_valuation_ring.add_val` as an `add_valuation` ([#6660](https://github.com/leanprover-community/mathlib/pull/6660))
Refactors `discrete_valuation_ring.add_val` to be an `enat`-valued `add_valuation`.
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/ring_theory/discrete_valuation_ring.lean
- \+/\- *lemma* discrete_valuation_ring.add_val_add
- \+ *lemma* discrete_valuation_ring.add_val_eq_top_iff
- \+/\- *lemma* discrete_valuation_ring.add_val_le_iff_dvd
- \+/\- *lemma* discrete_valuation_ring.add_val_mul
- \+/\- *lemma* discrete_valuation_ring.add_val_pow
- \- *theorem* discrete_valuation_ring.add_val_spec
- \+/\- *lemma* discrete_valuation_ring.add_val_zero
- \+ *theorem* discrete_valuation_ring.exists_prime

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.eq_of_associated_left
- \+ *lemma* multiplicity.eq_of_associated_right
- \- *lemma* multiplicity.multiplicity_le_multiplicity_of_dvd
- \+ *lemma* multiplicity.multiplicity_le_multiplicity_of_dvd_left
- \+ *lemma* multiplicity.multiplicity_le_multiplicity_of_dvd_right



## [2021-03-14 03:22:14](https://github.com/leanprover-community/mathlib/commit/d61d8bf)
feat(measure_theory/bochner_integration): extend the integral_smul lemmas ([#6654](https://github.com/leanprover-community/mathlib/pull/6654))
Extend the `integral_smul` lemmas to multiplication of a function `f : α → E` with scalars in `𝕜` with `[nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]` instead of only `ℝ`.
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+ *def* measure_theory.L1.integral_clm'
- \+/\- *def* measure_theory.L1.integral_clm
- \+/\- *lemma* measure_theory.L1.integral_smul
- \+ *def* measure_theory.L1.simple_func.integral_clm'
- \+/\- *def* measure_theory.L1.simple_func.integral_clm
- \+/\- *lemma* measure_theory.L1.simple_func.integral_smul
- \+/\- *lemma* measure_theory.integral_smul
- \+/\- *lemma* measure_theory.simple_func.integral_smul



## [2021-03-14 03:22:13](https://github.com/leanprover-community/mathlib/commit/a8af8e8)
feat(polynomial/algebra_map): aeval_algebra_map_apply ([#6649](https://github.com/leanprover-community/mathlib/pull/6649))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.aeval_algebra_map_apply



## [2021-03-14 03:22:12](https://github.com/leanprover-community/mathlib/commit/3e011d6)
chore(equiv/*): add missing lemmas to traverse coercion diamonds ([#6648](https://github.com/leanprover-community/mathlib/pull/6648))
These don't have a preferred direction, but there are cases when they are definitely needed.
The conversion paths commute as squares:
```
`→+` <-- `→+*` <-- `→ₐ[R]`
 ^         ^          ^
 |         |          |
`≃+` <-- `≃+*` <-- `≃ₐ[R]`
```
so we only need lemmas to swap within each square.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.coe_ring_hom_commutes

Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_equiv.to_add_monoid_hom_commutes

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.to_add_monoid_hom_commutes
- \+ *lemma* ring_equiv.to_equiv_commutes
- \+ *lemma* ring_equiv.to_monoid_hom_commutes



## [2021-03-14 03:22:11](https://github.com/leanprover-community/mathlib/commit/a3050f4)
feat(group_theory/order_of_element): Endomorphisms of cyclic groups ([#6645](https://github.com/leanprover-community/mathlib/pull/6645))
If G is cyclic then every group homomorphism G -> G is a power map.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* monoid_hom.map_cyclic



## [2021-03-14 03:22:10](https://github.com/leanprover-community/mathlib/commit/b23e14d)
feat(data/polynomial/eval): prod_comp ([#6644](https://github.com/leanprover-community/mathlib/pull/6644))
Extend `mul_comp` to `multiset.prod`
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.prod_comp



## [2021-03-14 03:22:09](https://github.com/leanprover-community/mathlib/commit/d5563ae)
feat(group_theory/solvable): Solvability preserved by short exact sequences ([#6632](https://github.com/leanprover-community/mathlib/pull/6632))
Proves that if 0 -> A -> B -> C -> 0 is a short exact sequence of groups, and if A and C are both solvable, then so is B.
#### Estimated changes
Modified src/group_theory/solvable.lean
- \+ *lemma* solvable_of_ker_le_range



## [2021-03-14 03:22:08](https://github.com/leanprover-community/mathlib/commit/ade8889)
feat(algebra/algebra/basic): An algebra isomorphism induces a group isomorphism between automorphism groups ([#6622](https://github.com/leanprover-community/mathlib/pull/6622))
Constructs the group isomorphism induced from an algebra isomorphism.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.aut_congr
- \+ *lemma* alg_equiv.aut_congr_refl
- \+ *lemma* alg_equiv.aut_congr_symm
- \+ *lemma* alg_equiv.aut_congr_trans
- \+ *lemma* alg_equiv.mul_apply



## [2021-03-14 00:42:57](https://github.com/leanprover-community/mathlib/commit/552ebeb)
feat(algebra/continued_fractions): add convergence theorem  ([#6607](https://github.com/leanprover-community/mathlib/pull/6607))
1. Add convergence theorem for continued fractions, i.e. `(gcf.of v).convergents` converges to `v`. 
2. Add some simple corollaries following from the already existing approximation lemmas for continued fractions, e.g. the equivalence of the convergent computations for continued fractions computed by `gcf.of` (`(gcf.of v).convergents` and `(gcf.of v).convergents'`).
#### Estimated changes
Modified src/algebra/continued_fractions/basic.lean
- \+ *def* simple_continued_fraction.is_continued_fraction
- \- *def* simple_continued_fraction.is_regular_continued_fraction

Added src/algebra/continued_fractions/computation/approximation_corollaries.lean
- \+ *def* continued_fraction.of
- \+ *theorem* generalized_continued_fraction.of_convergence
- \+ *theorem* generalized_continued_fraction.of_convergence_epsilon
- \+ *lemma* generalized_continued_fraction.of_convergents_eq_convergents'
- \+ *lemma* generalized_continued_fraction.of_is_simple_continued_fraction
- \+ *def* simple_continued_fraction.of
- \+ *lemma* simple_continued_fraction.of_is_continued_fraction

Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/default.lean


Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/continued_fractions/default.lean




## [2021-03-14 00:42:55](https://github.com/leanprover-community/mathlib/commit/a7410df)
feat(analysis/calculus/tangent_cone): add `unique_diff_on.pi` ([#6577](https://github.com/leanprover-community/mathlib/pull/6577))
#### Estimated changes
Modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* maps_to_tangent_cone_pi
- \+ *lemma* unique_diff_on.pi
- \+ *lemma* unique_diff_on.univ_pi
- \+ *lemma* unique_diff_within_at.pi
- \+ *lemma* unique_diff_within_at.univ_pi

Modified src/analysis/normed_space/basic.lean
- \+ *theorem* eventually_nhds_norm_smul_sub_lt



## [2021-03-14 00:42:54](https://github.com/leanprover-community/mathlib/commit/1b0db8e)
feat(order/well_founded_set, ring_theory/hahn_series): `hahn_series.add_val` ([#6564](https://github.com/leanprover-community/mathlib/pull/6564))
Defines `set.is_wf.min` in terms of `well_founded.min`
Places an `add_valuation`, `hahn_series.add_val`, on `hahn_series`
#### Estimated changes
Modified src/order/well_founded_set.lean
- \+ *theorem* finset.mul_antidiagonal_min_mul_min
- \+ *lemma* set.is_wf.le_min_iff
- \+ *lemma* set.is_wf.min_le
- \+ *lemma* set.is_wf.min_le_min_of_subset
- \+ *lemma* set.is_wf.min_mem
- \+ *theorem* set.is_wf.min_mul
- \+ *lemma* set.is_wf.min_union
- \+ *lemma* set.is_wf.not_lt_min
- \+ *lemma* set.is_wf_min_singleton

Modified src/ring_theory/hahn_series.lean
- \+ *def* hahn_series.add_val
- \+ *lemma* hahn_series.add_val_apply
- \+ *lemma* hahn_series.add_val_apply_of_ne
- \+ *lemma* hahn_series.coeff_min_ne_zero
- \+ *lemma* hahn_series.mul_coeff_min_add_min
- \+/\- *theorem* hahn_series.single_coeff_same
- \+ *lemma* hahn_series.support_add_subset
- \+ *lemma* hahn_series.support_nonempty_iff
- \+ *lemma* hahn_series.support_one



## [2021-03-14 00:42:53](https://github.com/leanprover-community/mathlib/commit/0c26cea)
feat(order/filter/cofinite): a growing function has a minimum ([#6556](https://github.com/leanprover-community/mathlib/pull/6556))
If `tendsto f cofinite at_top`, then `f` has a minimal element.
#### Estimated changes
Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.tendsto.exists_forall_ge
- \+ *lemma* filter.tendsto.exists_forall_le



## [2021-03-14 00:42:52](https://github.com/leanprover-community/mathlib/commit/19ecff8)
feat(topology/algebra/nonarchimedean): added nonarchimedean groups and rings ([#6551](https://github.com/leanprover-community/mathlib/pull/6551))
Adding nonarchimedean topological groups and rings.
#### Estimated changes
Added src/topology/algebra/nonarchimedean/basic.lean
- \+ *lemma* nonarchimedean_group.nonarchimedean_of_emb
- \+ *lemma* nonarchimedean_group.prod_self_subset
- \+ *lemma* nonarchimedean_group.prod_subset
- \+ *lemma* nonarchimedean_ring.left_mul_subset
- \+ *lemma* nonarchimedean_ring.mul_subset

Modified src/topology/algebra/open_subgroup.lean
- \+ *lemma* open_subgroup.coe_comap
- \+ *def* open_subgroup.comap
- \+ *lemma* open_subgroup.comap_comap
- \+ *lemma* open_subgroup.mem_comap

Modified src/topology/algebra/ring.lean




## [2021-03-14 00:42:51](https://github.com/leanprover-community/mathlib/commit/ae33fb0)
feat(group_theory/submonoid/operations): add eq_top_iff' ([#6536](https://github.com/leanprover-community/mathlib/pull/6536))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* subgroup.eq_top_iff'

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.eq_top_iff'

Modified src/ring_theory/subring.lean
- \+ *lemma* subring.eq_top_iff'

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.eq_top_iff'



## [2021-03-14 00:42:50](https://github.com/leanprover-community/mathlib/commit/f4c4d10)
feat(probability_theory/independence): prove equivalences for indep_set ([#6242](https://github.com/leanprover-community/mathlib/pull/6242))
Prove the following equivalences on `indep_set`, for measurable sets `s,t` and a probability measure `µ` :
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
In `indep_sets.indep_set_of_mem`, we use those equivalences to obtain `indep_set s t µ` from `indep_sets S T µ` and `s ∈ S`, `t ∈ T`.
#### Estimated changes
Modified src/probability_theory/independence.lean
- \+ *lemma* probability_theory.indep_set_iff_indep_sets_singleton
- \+ *lemma* probability_theory.indep_set_iff_measure_inter_eq_mul
- \+ *lemma* probability_theory.indep_sets.indep_set_of_mem
- \+ *lemma* probability_theory.indep_sets_singleton_iff



## [2021-03-13 21:18:31](https://github.com/leanprover-community/mathlib/commit/c277752)
feat(algebra/group/defs, data/nat/basic): some `ne` lemmas ([#6637](https://github.com/leanprover-community/mathlib/pull/6637))
`≠` versions of `mul_left_inj`, `mul_right_inj`, and `succ_inj`, as well as the lemma `succ_succ_ne_one`.
#### Estimated changes
Modified src/algebra/group/basic.lean


Modified src/algebra/group/defs.lean
- \+ *theorem* mul_ne_mul_left
- \+ *theorem* mul_ne_mul_right

Modified src/data/nat/basic.lean
- \+ *lemma* nat.mul_ne_mul_left
- \+ *lemma* nat.mul_ne_mul_right
- \+ *lemma* nat.one_lt_succ_succ
- \+ *lemma* nat.succ_ne_succ
- \+ *lemma* nat.succ_succ_ne_one



## [2021-03-13 21:18:30](https://github.com/leanprover-community/mathlib/commit/468b8ff)
feat(field_theory/polynomial_galois_group): instances of trivial Galois group ([#6634](https://github.com/leanprover-community/mathlib/pull/6634))
This PR adds a bunch of instances where the Galois group of a polynomial is trivial.
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *def* polynomial.gal.unique_gal_of_splits



## [2021-03-13 21:18:29](https://github.com/leanprover-community/mathlib/commit/ba6b689)
feat(field_theory/intermediate_field): coe_pow ([#6626](https://github.com/leanprover-community/mathlib/pull/6626))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.coe_pow



## [2021-03-13 15:08:17](https://github.com/leanprover-community/mathlib/commit/e6819d3)
feat(algebra/group_power/lemmas): add invertible_of_pow_eq_one ([#6658](https://github.com/leanprover-community/mathlib/pull/6658))
#### Estimated changes
Modified src/algebra/associated.lean
- \- *lemma* is_unit.pow

Modified src/algebra/group_power/lemmas.lean
- \+ *def* invertible_of_pow_eq_one
- \+ *def* invertible_of_pow_succ_eq_one
- \+ *lemma* is_unit.pow



## [2021-03-13 01:18:53](https://github.com/leanprover-community/mathlib/commit/ff8c8f5)
fix(tactic/norm_num): perform cleanup even if norm_num fails ([#6655](https://github.com/leanprover-community/mathlib/pull/6655))
[As reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/norm_num.20fails.20when.20simp.20is.20too.20effective/near/230004826).
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean


Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2021-03-12 14:44:38](https://github.com/leanprover-community/mathlib/commit/f54f81c)
refactor(algebra/invertible): push deeper into the import graph ([#6650](https://github.com/leanprover-community/mathlib/pull/6650))
I want to be able to import this in files where we use `is_unit`, to remove a few unecessary non-computables.
This moves all the lemmas about `char_p` and `char_zero` from `algebra.invertible` to `algebra.char_p.invertible`. This means that we can talk about `invertible` elements without having to build up the theory in `order_of_element` first.
This doesn't change any lemma statements or proofs, but it does move some type arguments into `variables` statements.
#### Estimated changes
Modified src/algebra/associated.lean


Added src/algebra/char_p/invertible.lean
- \+ *def* invertible_of_char_p_not_dvd
- \+ *def* invertible_of_ring_char_not_dvd

Modified src/algebra/invertible.lean
- \- *def* invertible_of_char_p_not_dvd
- \- *def* invertible_of_ring_char_not_dvd

Modified src/algebra/quadratic_discriminant.lean


Modified src/linear_algebra/affine_space/midpoint.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/witt_vector/witt_polynomial.lean




## [2021-03-12 08:19:11](https://github.com/leanprover-community/mathlib/commit/85c6a79)
feat(measure_theory/lp_space): Lp is complete ([#6563](https://github.com/leanprover-community/mathlib/pull/6563))
Prove the completeness of `Lp` by showing that Cauchy sequences of `ℒp` have a limit.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/measure_theory/ess_sup.lean
- \+ *lemma* ennreal.ess_sup_liminf_le

Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.Lp.ae_tendsto_of_cauchy_snorm'
- \+ *lemma* measure_theory.Lp.ae_tendsto_of_cauchy_snorm
- \+ *lemma* measure_theory.Lp.cauchy_complete_ℒp
- \+ *lemma* measure_theory.Lp.cauchy_tendsto_of_tendsto
- \+ *lemma* measure_theory.Lp.complete_space_Lp_of_cauchy_complete_ℒp
- \+ *lemma* measure_theory.Lp.mem_ℒp_of_cauchy_tendsto
- \+ *lemma* measure_theory.Lp.snorm'_lim_eq_lintegral_liminf
- \+ *lemma* measure_theory.Lp.snorm'_lim_le_liminf_snorm'
- \+ *lemma* measure_theory.Lp.snorm_exponent_top_lim_eq_ess_sup_liminf
- \+ *lemma* measure_theory.Lp.snorm_exponent_top_lim_le_liminf_snorm_exponent_top
- \+ *lemma* measure_theory.Lp.snorm_lim_le_liminf_snorm
- \+ *lemma* measure_theory.Lp.tendsto_Lp_of_tendsto_ℒp
- \+ *lemma* measure_theory.snorm'_norm

Modified src/order/filter/ennreal.lean
- \+ *lemma* ennreal.limsup_liminf_le_liminf_limsup

Modified src/topology/instances/ennreal.lean




## [2021-03-12 04:45:09](https://github.com/leanprover-community/mathlib/commit/dae047e)
feat(data/polynomial/*): more lemmas, especially for noncommutative rings ([#6599](https://github.com/leanprover-community/mathlib/pull/6599))
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* zero_pow_eq

Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.single_pow

Modified src/data/int/cast.lean
- \+ *lemma* int.cast_comm

Modified src/data/nat/cast.lean
- \+ *lemma* nat.cast_comm

Modified src/data/polynomial/algebra_map.lean
- \- *lemma* polynomial.eval_comp
- \- *lemma* polynomial.eval₂_comp

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.X_mul_monomial
- \+ *lemma* polynomial.X_pow_mul_monomial
- \+ *lemma* polynomial.monomial_mul_X
- \+ *lemma* polynomial.monomial_mul_X_pow
- \+ *lemma* polynomial.monomial_one_one_eq_X
- \+ *lemma* polynomial.monomial_one_right_eq_X_pow
- \+ *lemma* polynomial.monomial_pow
- \+ *lemma* polynomial.monomial_zero_one

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.C_mul_comp
- \+ *lemma* polynomial.X_pow_comp
- \- *lemma* polynomial.cast_nat_comp
- \+ *lemma* polynomial.eval_C_mul
- \+ *lemma* polynomial.eval_comp
- \+ *lemma* polynomial.eval_mul_X
- \+ *lemma* polynomial.eval_mul_X_pow
- \+ *lemma* polynomial.eval_nat_cast_mul
- \+ *lemma* polynomial.eval₂_at_apply
- \+ *lemma* polynomial.eval₂_at_nat_cast
- \+ *lemma* polynomial.eval₂_at_one
- \+ *lemma* polynomial.eval₂_at_zero
- \+ *lemma* polynomial.eval₂_comp
- \+ *lemma* polynomial.mul_X_comp
- \+ *lemma* polynomial.mul_X_pow_comp
- \+ *lemma* polynomial.nat_cast_comp
- \+ *lemma* polynomial.nat_cast_mul_comp

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.C_mul_monomial
- \+ *lemma* polynomial.monomial_mul_C

Modified src/data/rat/cast.lean
- \+ *theorem* rat.cast_comm



## [2021-03-12 01:21:10](https://github.com/leanprover-community/mathlib/commit/b852648)
chore(scripts): update nolints.txt ([#6651](https://github.com/leanprover-community/mathlib/pull/6651))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-12 00:18:01](https://github.com/leanprover-community/mathlib/commit/2dabe5a)
feat(.docker): Docker containers for debian, alpine, and gitpod ([#6515](https://github.com/leanprover-community/mathlib/pull/6515))
# Docker containers
The `.docker` directory contains instructions for building Docker containers
with Lean and mathlib.
## Build
You can build these containers using `scripts/docker_build.sh`.
This will result in the creation of two containers:
* `leanprovercommunity/lean` - contains elan, lean, and leanproject
* `leanprovercommunity/mathlib` - additionally contains a copy of mathlib, with oleans
In fact, for each container you'll get three different tags, `:debian`, `:alpine` and `:latest`.
`:debian` and `:alpine` use those respective distributions, and `:latest` just points at `:debian`.
Finally, there is also a `leanprovercommunity/mathlib:gitpod` for use at
[https://gitpod.io/](https://gitpod.io/).
## Usage
### gitpod.io
There is a container based on `gitpod/workspace-base`
enabling [https://gitpod.io/](https://gitpod.io/) to create in-browser VSCode sessions
with elan/lean/leanproject/mathlib already set up.
Either prepend `https://gitpod.io/#` to basically any URL at github, e.g.
[https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker](https://gitpod.io/#https://github.com/leanprover-community/mathlib/tree/docker),
or install a [gitpod browser extension](https://www.gitpod.io/docs/browser-extension/)
which will add buttons directly on github.
### Command line
You can use these containers as virtual machines:
```sh
docker run -it leanprovercommunity/mathlib
```
### Docker registry
These containers are deployed to the Docker registry, so anyone can just
`docker run -it leanprovercommunity/mathlib` to get a local lean+mathlib environment.
There is a local script in `scripts/docker_push.sh` for deployment,
but I have also set up `hub.docker.com` to watch the `docker` branch for updates
and automatically rebuild.
If this PR is merged to master we should change that to watch `master`.
### Remote containers for VSCode
Installing the `Remote - Containers` VSCode extension
will allow you to open a project inside the `leanprovercommunity/mathlib` container
(meaning you don't even need a local copy of lean installed).
The file `/.devcontainer/devcontainer.json` sets this up:
if you have the extension installed, you'll be prompted to ask if you'd like to run inside the
container, no configuration necessary.
#### Estimated changes
Added .devcontainer/README.md


Added .devcontainer/devcontainer.json


Added .docker/README.md


Added .docker/alpine/lean/.profile


Added .docker/alpine/lean/Dockerfile


Added .docker/alpine/mathlib/Dockerfile


Added .docker/debian/lean/Dockerfile


Added .docker/debian/mathlib/Dockerfile


Added .docker/gitpod/mathlib/Dockerfile


Modified .github/PULL_REQUEST_TEMPLATE.md


Added .gitpod.yml


Modified README.md


Added scripts/docker_build.sh


Added scripts/docker_push.sh




## [2021-03-11 22:32:31](https://github.com/leanprover-community/mathlib/commit/b1aafb2)
fix (topology/algebra/basic): fix universe issue with of_nhds_one ([#6647](https://github.com/leanprover-community/mathlib/pull/6647))
Everything had type max{u v} before.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+/\- *lemma* topological_group.of_nhds_one



## [2021-03-11 17:09:38](https://github.com/leanprover-community/mathlib/commit/4d8d344)
feat(data/multiset/basic): Multiset induction lemma ([#6623](https://github.com/leanprover-community/mathlib/pull/6623))
This is the multiset analog of `finset.induction_on'`
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.induction_on'



## [2021-03-11 17:09:36](https://github.com/leanprover-community/mathlib/commit/bd3695a)
feat(data/complex/is_R_or_C): add linear maps for is_R_or_C.re, im, conj and of_real ([#6621](https://github.com/leanprover-community/mathlib/pull/6621))
Add continuous linear maps and linear isometries (when applicable) for the following `is_R_or_C` functions: `re`, `im`, `conj` and `of_real`.
Rename the existing continuous linear maps defined in complex.basic to adopt the naming convention of is_R_or_C.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *def* complex.conj_clm
- \+ *lemma* complex.conj_clm_apply
- \+ *lemma* complex.conj_clm_coe
- \+ *lemma* complex.conj_clm_norm
- \+ *def* complex.conj_li
- \+/\- *lemma* complex.continuous_conj
- \+/\- *lemma* complex.continuous_im
- \- *def* complex.continuous_linear_map.conj
- \- *lemma* complex.continuous_linear_map.conj_apply
- \- *lemma* complex.continuous_linear_map.conj_coe
- \- *lemma* complex.continuous_linear_map.conj_norm
- \- *def* complex.continuous_linear_map.im
- \- *lemma* complex.continuous_linear_map.im_apply
- \- *lemma* complex.continuous_linear_map.im_coe
- \- *lemma* complex.continuous_linear_map.im_norm
- \- *def* complex.continuous_linear_map.of_real
- \- *lemma* complex.continuous_linear_map.of_real_apply
- \- *lemma* complex.continuous_linear_map.of_real_coe
- \- *lemma* complex.continuous_linear_map.of_real_norm
- \- *def* complex.continuous_linear_map.re
- \- *lemma* complex.continuous_linear_map.re_apply
- \- *lemma* complex.continuous_linear_map.re_coe
- \- *lemma* complex.continuous_linear_map.re_norm
- \+/\- *lemma* complex.continuous_re
- \+ *def* complex.im_clm
- \+ *lemma* complex.im_clm_apply
- \+ *lemma* complex.im_clm_coe
- \+ *lemma* complex.im_clm_norm
- \+/\- *lemma* complex.isometry_conj
- \+/\- *lemma* complex.isometry_of_real
- \- *def* complex.linear_isometry.conj
- \- *def* complex.linear_isometry.of_real
- \+ *def* complex.of_real_clm
- \+ *lemma* complex.of_real_clm_apply
- \+ *lemma* complex.of_real_clm_coe
- \+ *lemma* complex.of_real_clm_norm
- \+ *def* complex.of_real_li
- \+ *def* complex.re_clm
- \+ *lemma* complex.re_clm_apply
- \+ *lemma* complex.re_clm_coe
- \+ *lemma* complex.re_clm_norm

Modified src/analysis/complex/real_deriv.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.conj_clm_apply
- \+ *lemma* is_R_or_C.conj_clm_coe
- \+ *lemma* is_R_or_C.conj_clm_norm
- \+ *lemma* is_R_or_C.conj_eq_re_sub_im
- \+ *lemma* is_R_or_C.conj_li_apply
- \+ *lemma* is_R_or_C.conj_lm_coe
- \+ *lemma* is_R_or_C.conj_smul
- \+ *lemma* is_R_or_C.continuous_conj
- \+ *lemma* is_R_or_C.continuous_im
- \+ *lemma* is_R_or_C.continuous_of_real
- \+ *lemma* is_R_or_C.continuous_re
- \+ *lemma* is_R_or_C.im_clm_apply
- \+ *lemma* is_R_or_C.im_clm_coe
- \+ *lemma* is_R_or_C.im_lm_coe
- \- *lemma* is_R_or_C.norm_re_clm
- \+ *lemma* is_R_or_C.of_real_clm_apply
- \+ *lemma* is_R_or_C.of_real_clm_coe
- \+ *lemma* is_R_or_C.of_real_clm_norm
- \+ *lemma* is_R_or_C.of_real_li_apply
- \+ *lemma* is_R_or_C.of_real_lm_coe
- \+ *lemma* is_R_or_C.of_real_smul
- \+ *lemma* is_R_or_C.re_clm_norm

Modified src/data/complex/module.lean
- \+ *def* complex.conj_lm
- \+ *lemma* complex.conj_lm_coe
- \+ *def* complex.im_lm
- \+ *lemma* complex.im_lm_coe
- \- *lemma* complex.linear_map.coe_conj
- \- *lemma* complex.linear_map.coe_im
- \- *lemma* complex.linear_map.coe_of_real
- \- *lemma* complex.linear_map.coe_re
- \- *def* complex.linear_map.conj
- \- *def* complex.linear_map.im
- \- *def* complex.linear_map.of_real
- \- *def* complex.linear_map.re
- \+ *def* complex.of_real_lm
- \+ *lemma* complex.of_real_lm_coe
- \+ *def* complex.re_lm
- \+ *lemma* complex.re_lm_coe



## [2021-03-11 17:09:35](https://github.com/leanprover-community/mathlib/commit/998a382)
feat(topology/algebra/infinite_sum): add `tsum_even_add_odd` ([#6620](https://github.com/leanprover-community/mathlib/pull/6620))
Prove `∑' i, f (2 * i) + ∑' i, f (2 * i + 1) = ∑' i, f i` and some
supporting lemmas.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *lemma* range_two_mul
- \+ *lemma* range_two_mul_add_one

Modified src/data/nat/parity.lean
- \+ *lemma* nat.is_compl_even_odd

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* function.injective.has_sum_range_iff
- \+ *lemma* has_sum.add_disjoint
- \+ *lemma* has_sum.add_is_compl
- \+ *lemma* has_sum.even_add_odd
- \+ *lemma* summable.even_add_odd
- \+ *lemma* tsum_even_add_odd
- \+ *lemma* tsum_union_disjoint



## [2021-03-11 17:09:34](https://github.com/leanprover-community/mathlib/commit/95a8e95)
refactor(data/{,mv_}polynomial): support function ([#6615](https://github.com/leanprover-community/mathlib/pull/6615))
With polynomials, we try to avoid the function coercion in favor of the `coeff` functions.  However the coercion easily leaks through the abstraction because of the `finsupp.mem_support_iff` lemma.
This PR adds the `polynomial.support` and `mv_polynomial.support` functions.  This allows us to define the `polynomial.mem_support_iff` and `mv_polynomial.mem_support_iff` lemmas that are stated in terms of `coeff`.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.C_0
- \+ *lemma* mv_polynomial.C_apply
- \+/\- *def* mv_polynomial.coeff
- \+/\- *lemma* mv_polynomial.coeff_C_mul
- \- *def* mv_polynomial.coeff_coe_to_fun
- \+ *lemma* mv_polynomial.mem_support_iff
- \+ *lemma* mv_polynomial.mul_def
- \+ *lemma* mv_polynomial.not_mem_support_iff
- \+ *lemma* mv_polynomial.sum_C
- \+ *lemma* mv_polynomial.sum_def
- \+ *def* mv_polynomial.support
- \+ *lemma* mv_polynomial.support_X
- \+ *lemma* mv_polynomial.support_add
- \+ *lemma* mv_polynomial.support_monomial
- \+ *lemma* mv_polynomial.support_monomial_subset
- \+ *lemma* mv_polynomial.support_mul

Modified src/data/mv_polynomial/comm_ring.lean
- \+ *lemma* mv_polynomial.support_neg

Modified src/data/mv_polynomial/rename.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.card_support_eq_zero
- \+ *def* polynomial.support
- \+ *lemma* polynomial.support_add
- \+ *lemma* polynomial.support_eq_empty
- \+ *lemma* polynomial.support_neg

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.mem_support_iff
- \- *lemma* polynomial.mem_support_iff_coeff_ne_zero
- \+ *lemma* polynomial.not_mem_support_iff
- \- *lemma* polynomial.not_mem_support_iff_coeff_zero
- \+ *lemma* polynomial.sum_def

Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/degree/lemmas.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/data/polynomial/derivative.lean


Modified src/data/polynomial/div.lean
- \- *lemma* polynomial.apply_eq_coeff
- \- *def* polynomial.coeff_coe_to_fun

Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/polynomial/reverse.lean


Modified src/field_theory/separable.lean


Modified src/linear_algebra/char_poly/coeff.lean


Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/polynomial/homogeneous.lean


Modified src/ring_theory/polynomial/scale_roots.lean




## [2021-03-11 17:09:33](https://github.com/leanprover-community/mathlib/commit/f5c9d0f)
feat(topology/algebra/ordered): generalize `real.compact_Icc` ([#6602](https://github.com/leanprover-community/mathlib/pull/6602))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_bot_top

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* ultrafilter.diff_mem_iff

Modified src/topology/algebra/ordered.lean
- \+ *lemma* compact_Icc
- \+ *lemma* compact_interval
- \+ *lemma* compact_pi_Icc

Modified src/topology/instances/real.lean
- \- *lemma* compact_Icc
- \- *lemma* compact_pi_Icc
- \- *lemma* real.totally_bounded_Icc
- \- *lemma* real.totally_bounded_Ico
- \- *lemma* real.totally_bounded_Ioo

Modified src/topology/metric_space/basic.lean
- \+ *lemma* totally_bounded_Icc
- \+ *lemma* totally_bounded_Ico
- \+ *lemma* totally_bounded_Ioc
- \+ *lemma* totally_bounded_Ioo

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* is_compact.is_complete
- \+ *lemma* is_compact.totally_bounded



## [2021-03-11 13:28:38](https://github.com/leanprover-community/mathlib/commit/3b3a8b5)
fix(normed_space/multilinear): speed up slow proof ([#6639](https://github.com/leanprover-community/mathlib/pull/6639))
This proof seems to be right on the edge of timing out and has been causing CI issues.
I'm not sure if this is the only culprit. This whole file is very slow. Is this because of recent changes, or has it always been like this?
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean




## [2021-03-11 13:28:36](https://github.com/leanprover-community/mathlib/commit/3d451c7)
chore(tactic/interactive): propagate tags in `substs` ([#6638](https://github.com/leanprover-community/mathlib/pull/6638))
Before this change, the `case left` tactic here did not work:
```lean
example {α : Type*} (a b c : α) (h : a = b) : (a = b ∨ a = c) ∧ true :=
begin
  with_cases {apply and.intro},
  substs' h,
  case left : { exact or.inl rfl },
  case right : { trivial }
end
```
#### Estimated changes
Modified src/tactic/interactive.lean




## [2021-03-11 13:28:35](https://github.com/leanprover-community/mathlib/commit/9beec03)
feat(group_theory/subgroup): le_ker_iff ([#6630](https://github.com/leanprover-community/mathlib/pull/6630))
A subgroup is contained in the kernel iff it is mapped to the trivial subgroup.
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean


Modified src/algebra/lie/solvable.lean


Modified src/algebra/lie/submodule.lean
- \- *lemma* lie_hom.map_bot_iff
- \+ *lemma* lie_ideal.map_eq_bot_iff

Modified src/group_theory/solvable.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* monoid_hom.ker_eq_bot_iff
- \+/\- *lemma* subgroup.map_eq_bot_iff
- \+ *lemma* subgroup.map_eq_bot_iff_of_injective



## [2021-03-11 13:28:33](https://github.com/leanprover-community/mathlib/commit/57fda28)
refactor(data/polynomial/degree/definitions): Remove hypothesis of nat_degree_X_pow_sub_C ([#6628](https://github.com/leanprover-community/mathlib/pull/6628))
The lemma `nat_degree_X_pow_sub_C ` had an unnecessary hypothesis.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.nat_degree_X_pow_sub_C

Modified src/ring_theory/polynomial/cyclotomic.lean




## [2021-03-11 13:28:32](https://github.com/leanprover-community/mathlib/commit/41f1196)
feat(field_theory/polynomial_galois_group): ext lemma ([#6627](https://github.com/leanprover-community/mathlib/pull/6627))
Two elements of `gal p` are equal if they agree on all roots of `p`
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean
- \+ *lemma* polynomial.gal.ext



## [2021-03-11 13:28:31](https://github.com/leanprover-community/mathlib/commit/3dd1257)
feat(group_theory/solvable): Commutative groups are solvable ([#6625](https://github.com/leanprover-community/mathlib/pull/6625))
In practice, `is_solvable_of_comm` is hard to use, since you often aren't working with a `comm_group`. Instead, it is much nicer to be able to write:
`apply is_solvable_of_comm'`
`intros g h`
#### Estimated changes
Modified src/group_theory/solvable.lean
- \+ *lemma* is_solvable_of_comm



## [2021-03-11 13:28:30](https://github.com/leanprover-community/mathlib/commit/2c4a985)
feat(field_theory/splitting_field): splits_pow ([#6624](https://github.com/leanprover-community/mathlib/pull/6624))
If a polynomial splits then so do its powers.
#### Estimated changes
Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.splits_X_pow
- \+ *lemma* polynomial.splits_pow



## [2021-03-11 13:28:29](https://github.com/leanprover-community/mathlib/commit/653fd29)
refactor(topology): make is_closed a class ([#6552](https://github.com/leanprover-community/mathlib/pull/6552))
In `lean-liquid`, it would be useful that `is_closed` would be a class, to be able to infer a normed space structure on `E/F` when `F` is a closed subspace of a normed space `E`. This is implemented in this PR. This is mostly straightforward: the only proofs that need fixing are those abusing defeqness, so the new version makes them clearer IMHO.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/convex/integral.lean


Modified src/data/analysis/topology.lean


Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \- *def* is_closed
- \+ *lemma* is_open.is_closed_compl
- \+/\- *lemma* is_open_compl_iff

Modified src/topology/category/Compactum.lean


Modified src/topology/connected.lean


Modified src/topology/constructions.lean


Modified src/topology/homeomorph.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/order.lean


Modified src/topology/paracompact.lean


Modified src/topology/separation.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/separation.lean




## [2021-03-11 11:19:18](https://github.com/leanprover-community/mathlib/commit/56065f7)
feat(measure_theory/pi_system) lemmas for pi_system, useful for independence. ([#6353](https://github.com/leanprover-community/mathlib/pull/6353))
The goal here is to prove that the expectation of a product of an finite number of independent random variables equals the production of the expectations.
See https://github.com/leanprover-community/mathlib/tree/mzinkevi_independent_finite_alt
#### Estimated changes
Modified src/measure_theory/measurable_space.lean
- \- *def* is_pi_system
- \- *lemma* measurable_space.dynkin_system.ext
- \- *def* measurable_space.dynkin_system.generate
- \- *lemma* measurable_space.dynkin_system.generate_from_eq
- \- *inductive* measurable_space.dynkin_system.generate_has
- \- *lemma* measurable_space.dynkin_system.generate_has_compl
- \- *lemma* measurable_space.dynkin_system.generate_has_def
- \- *lemma* measurable_space.dynkin_system.generate_has_subset_generate_measurable
- \- *lemma* measurable_space.dynkin_system.generate_inter
- \- *lemma* measurable_space.dynkin_system.generate_le
- \- *theorem* measurable_space.dynkin_system.has_Union
- \- *lemma* measurable_space.dynkin_system.has_compl_iff
- \- *lemma* measurable_space.dynkin_system.has_diff
- \- *theorem* measurable_space.dynkin_system.has_union
- \- *lemma* measurable_space.dynkin_system.has_univ
- \- *def* measurable_space.dynkin_system.of_measurable_space
- \- *lemma* measurable_space.dynkin_system.of_measurable_space_le_of_measurable_space_iff
- \- *lemma* measurable_space.dynkin_system.of_measurable_space_to_measurable_space
- \- *def* measurable_space.dynkin_system.restrict_on
- \- *def* measurable_space.dynkin_system.to_measurable_space
- \- *structure* measurable_space.dynkin_system
- \- *lemma* measurable_space.induction_on_inter
- \- *lemma* measurable_space.is_pi_system_measurable_set

Modified src/measure_theory/outer_measure.lean


Added src/measure_theory/pi_system.lean
- \+ *lemma* generate_from_generate_pi_system_eq
- \+ *lemma* generate_from_measurable_set_of_generate_pi_system
- \+ *inductive* generate_pi_system
- \+ *lemma* generate_pi_system_eq
- \+ *lemma* generate_pi_system_measurable_set
- \+ *lemma* generate_pi_system_mono
- \+ *lemma* generate_pi_system_subset_self
- \+ *lemma* is_pi_system.singleton
- \+ *def* is_pi_system
- \+ *lemma* is_pi_system_generate_pi_system
- \+ *lemma* measurable_space.dynkin_system.ext
- \+ *def* measurable_space.dynkin_system.generate
- \+ *lemma* measurable_space.dynkin_system.generate_from_eq
- \+ *inductive* measurable_space.dynkin_system.generate_has
- \+ *lemma* measurable_space.dynkin_system.generate_has_compl
- \+ *lemma* measurable_space.dynkin_system.generate_has_def
- \+ *lemma* measurable_space.dynkin_system.generate_has_subset_generate_measurable
- \+ *lemma* measurable_space.dynkin_system.generate_inter
- \+ *lemma* measurable_space.dynkin_system.generate_le
- \+ *theorem* measurable_space.dynkin_system.has_Union
- \+ *lemma* measurable_space.dynkin_system.has_compl_iff
- \+ *lemma* measurable_space.dynkin_system.has_diff
- \+ *theorem* measurable_space.dynkin_system.has_union
- \+ *lemma* measurable_space.dynkin_system.has_univ
- \+ *def* measurable_space.dynkin_system.of_measurable_space
- \+ *lemma* measurable_space.dynkin_system.of_measurable_space_le_of_measurable_space_iff
- \+ *lemma* measurable_space.dynkin_system.of_measurable_space_to_measurable_space
- \+ *def* measurable_space.dynkin_system.restrict_on
- \+ *def* measurable_space.dynkin_system.to_measurable_space
- \+ *structure* measurable_space.dynkin_system
- \+ *theorem* measurable_space.induction_on_inter
- \+ *lemma* measurable_space.is_pi_system_measurable_set
- \+ *lemma* mem_generate_pi_system_Union_elim'
- \+ *lemma* mem_generate_pi_system_Union_elim
- \+ *lemma* subset_generate_pi_system_self



## [2021-03-11 06:05:43](https://github.com/leanprover-community/mathlib/commit/925ea07)
feat(linear_algebra/basic): add missing lemma finsupp.sum_smul_index_linear_map' ([#6565](https://github.com/leanprover-community/mathlib/pull/6565))
See also [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Sum.20is.20linear/near/229021943). cc @eric-wieser
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.sum_smul_index_add_monoid_hom

Modified src/linear_algebra/basic.lean
- \+ *lemma* finsupp.sum_smul_index_linear_map'



## [2021-03-11 05:06:41](https://github.com/leanprover-community/mathlib/commit/b7c5709)
chore(geometry/manifold): use notation `𝓘(𝕜, E)` ([#6636](https://github.com/leanprover-community/mathlib/pull/6636))
#### Estimated changes
Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean




## [2021-03-11 02:48:51](https://github.com/leanprover-community/mathlib/commit/514973a)
chore(scripts): update nolints.txt ([#6635](https://github.com/leanprover-community/mathlib/pull/6635))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-11 02:48:49](https://github.com/leanprover-community/mathlib/commit/0e32116)
feat(data/dfinsupp): add is_scalar_tower and smul_comm_class ([#6614](https://github.com/leanprover-community/mathlib/pull/6614))
This also weakens the requirements for the `has_scalar` instance
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.coe_smul
- \+/\- *lemma* dfinsupp.smul_apply

Modified src/linear_algebra/direct_sum_module.lean




## [2021-03-11 02:48:47](https://github.com/leanprover-community/mathlib/commit/a814e18)
ci(.github/workflows/build.yml): do not install azcopy, change upload logic ([#6613](https://github.com/leanprover-community/mathlib/pull/6613))
The "install azcopy" step has been [failing](https://github.com/leanprover-community/mathlib/runs/2070026978) from time to time, probably due to failed downloads. As it turns out, the GitHub-hosted actions runner [comes with it installed](https://github.com/actions/virtual-environments/blob/main/images/linux/Ubuntu2004-README.md#tools), so I've removed that step entirely.
I also made two other changes:
- The "push release to azure" step now only runs if the build actually started. The idea is that if the build never even starts due to e.g. `elan` temporarily failing to install, then we should be able to restart the build on GitHub and get `.olean`s for that commit without having to push another dummy commit. Currently we can't do this because we push an empty archive to Azure no matter what.
- We now upload artifacts if the build fails. This gives us an alternative way to get `.olean`s in case something goes wrong with Azure, and might make working with forks of mathlib slightly easier.
#### Estimated changes
Modified .github/workflows/build.yml




## [2021-03-11 00:47:49](https://github.com/leanprover-community/mathlib/commit/c5c97f2)
chore(ring_theory/polynomial/basic): remove a use of comap ([#6612](https://github.com/leanprover-community/mathlib/pull/6612))
This merges together `quotient_equiv_quotient_mv_polynomial` and `quotient_alg_equiv_quotient_mv_polynomial`, since the two now have the same domain and codomain.
`comap` was previously needed here to provide a wrapper type with an R-algebra structure on `mv_polynomial σ (I.quotient)`.
The updated `mv_polynomial.algebra` in [#6533](https://github.com/leanprover-community/mathlib/pull/6533) transfers the `algebra R I.quotient` structure directly to `mv_polynomial σ I.quotient`, eliminating the need for this wrapper type.
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \- *def* mv_polynomial.quotient_alg_equiv_quotient_mv_polynomial



## [2021-03-11 00:47:48](https://github.com/leanprover-community/mathlib/commit/590444c)
chore(topology/metric/hausdorff_distance): use `infi`/`supr` ([#6611](https://github.com/leanprover-community/mathlib/pull/6611))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.sup_eq_zero
- \+ *lemma* ennreal.supr_eq_zero

Modified src/topology/instances/ennreal.lean
- \- *lemma* ennreal.supr_eq_zero

Modified src/topology/metric_space/hausdorff_distance.lean
- \+/\- *def* emetric.inf_edist
- \+/\- *lemma* emetric.inf_edist_empty
- \+ *lemma* emetric.le_inf_edist



## [2021-03-10 20:43:06](https://github.com/leanprover-community/mathlib/commit/5be9cea)
chore(linear_algebra/quadratic_form): clean up universe collisions, generalize smul lemmas ([#6609](https://github.com/leanprover-community/mathlib/pull/6609))
#### Estimated changes
Modified src/linear_algebra/quadratic_form.lean
- \+/\- *lemma* quadratic_form.coe_fn_smul
- \+/\- *lemma* quadratic_form.polar_comm
- \+/\- *lemma* quadratic_form.polar_smul
- \+ *lemma* quadratic_form.polar_smul_left_of_tower
- \+ *lemma* quadratic_form.polar_smul_right_of_tower
- \+/\- *lemma* quadratic_form.smul_apply



## [2021-03-10 20:43:05](https://github.com/leanprover-community/mathlib/commit/547bf55)
feat(data/complex/module): transfer all `has_scalar ℝ` structures to `ℂ` ([#6562](https://github.com/leanprover-community/mathlib/pull/6562))
This provides (for an `R` with the same instance on `ℝ`) the instances:
* `has_scalar R ℂ`
* `is_scalar_tower R S ℂ`
* `smul_comm_class R S ℂ`
* `mul_action R ℂ`
* `distrib_mul_action R ℂ`
* `semimodule R ℂ`
* `algebra R ℂ`
* `normed_algebra R ℂ`
This has the downside that `smul_coe` is no longer a `rfl` lemma, but means that `ℂ` is automatically an algebra over `ℝ≥0`.
It renames `smul_re` and `smul_im` to `of_real_mul_re` and `of_real_mul_im`, since the previous statements did not use `smul` at all, and renaming frees up these names for lemmas which _do_ use `smul`.
This removes `normed_space.restrict_scalars_real E` (implemented as `normed_space.restrict_scalars ℝ ℂ E`) as:
* As an instance, it now causes unwanted diamonds
* After downgrading to a def, it is never used
* The docs for `normed_space.restrict_scalars` suggest judicious use, and that if you want this instance you should use the type synonym `semimodule.restrict_scalars ℝ ℂ E` which will have this instance for free.
#### Estimated changes
Modified src/analysis/complex/basic.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/complex/basic.lean
- \+ *lemma* complex.of_real_mul'
- \+ *lemma* complex.of_real_mul_im
- \+ *lemma* complex.of_real_mul_re
- \- *lemma* complex.of_real_smul
- \- *lemma* complex.smul_im
- \- *lemma* complex.smul_re

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.of_real_mul_im
- \- *lemma* is_R_or_C.smul_im'
- \+/\- *lemma* is_R_or_C.smul_im
- \- *lemma* is_R_or_C.smul_re'
- \+/\- *lemma* is_R_or_C.smul_re

Modified src/data/complex/module.lean
- \+/\- *lemma* complex.smul_coe
- \+ *lemma* complex.smul_im
- \+ *lemma* complex.smul_re

Modified src/ring_theory/polynomial/cyclotomic.lean




## [2021-03-10 20:43:04](https://github.com/leanprover-community/mathlib/commit/60e2579)
feat(ring_theory/valuation/basic): additive valuations ([#6559](https://github.com/leanprover-community/mathlib/pull/6559))
Introduces `add_valuation`, a version of `valuation` that takes values in a `linear_ordered_add_comm_monoid_with_top`.
As an example, defines `multiplicity.add_valuation`
#### Estimated changes
Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity.add_valuation_apply

Modified src/ring_theory/valuation/basic.lean
- \+ *def* add_valuation.comap
- \+ *lemma* add_valuation.comap_comp
- \+ *lemma* add_valuation.comap_id
- \+ *lemma* add_valuation.comap_on_quot_eq
- \+ *lemma* add_valuation.comap_supp
- \+ *lemma* add_valuation.ext
- \+ *lemma* add_valuation.ext_iff
- \+ *lemma* add_valuation.is_equiv.comap
- \+ *lemma* add_valuation.is_equiv.map
- \+ *lemma* add_valuation.is_equiv.ne_top
- \+ *lemma* add_valuation.is_equiv.of_eq
- \+ *lemma* add_valuation.is_equiv.refl
- \+ *lemma* add_valuation.is_equiv.symm
- \+ *lemma* add_valuation.is_equiv.trans
- \+ *lemma* add_valuation.is_equiv.val_eq
- \+ *def* add_valuation.is_equiv
- \+ *def* add_valuation.map
- \+ *lemma* add_valuation.map_add
- \+ *lemma* add_valuation.map_add_supp
- \+ *lemma* add_valuation.map_le_add
- \+ *lemma* add_valuation.map_le_sum
- \+ *lemma* add_valuation.map_lt_add
- \+ *lemma* add_valuation.map_lt_sum'
- \+ *lemma* add_valuation.map_lt_sum
- \+ *lemma* add_valuation.map_mul
- \+ *lemma* add_valuation.map_one
- \+ *lemma* add_valuation.map_pow
- \+ *lemma* add_valuation.map_zero
- \+ *lemma* add_valuation.mem_supp_iff
- \+ *lemma* add_valuation.ne_top_iff
- \+ *def* add_valuation.of
- \+ *theorem* add_valuation.of_apply
- \+ *def* add_valuation.on_quot
- \+ *lemma* add_valuation.on_quot_comap_eq
- \+ *def* add_valuation.on_quot_val
- \+ *lemma* add_valuation.self_le_supp_comap
- \+ *def* add_valuation.supp
- \+ *lemma* add_valuation.supp_quot
- \+ *lemma* add_valuation.supp_quot_supp
- \+ *def* add_valuation.to_preorder
- \+ *lemma* add_valuation.top_iff
- \+ *def* add_valuation



## [2021-03-10 20:43:02](https://github.com/leanprover-community/mathlib/commit/e62a406)
feat(linear_algebra/determinant): determinant of a block triangular matrix ([#6050](https://github.com/leanprover-community/mathlib/pull/6050))
Add lemmas for determinants of block triangular matrices.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.subtype_subtype_equiv_subtype_apply
- \+ *lemma* equiv.subtype_subtype_equiv_subtype_exists_apply
- \+ *lemma* equiv.subtype_subtype_equiv_subtype_inter_apply

Modified src/data/matrix/basic.lean
- \+ *def* matrix.to_block
- \+ *lemma* matrix.to_block_apply
- \+ *def* matrix.to_square_block'
- \+ *def* matrix.to_square_block
- \+ *lemma* matrix.to_square_block_def'
- \+ *lemma* matrix.to_square_block_def
- \+ *def* matrix.to_square_block_prop
- \+ *lemma* matrix.to_square_block_prop_def

Modified src/group_theory/perm/basic.lean
- \+ *lemma* equiv.perm.default_perm

Modified src/group_theory/perm/sign.lean
- \+ *lemma* equiv.perm.perm_maps_to_inl_iff_maps_to_inr
- \+ *lemma* equiv.perm.perm_on_inl_iff_perm_on_inr

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_eq_elem_of_card_eq_one
- \+ *lemma* matrix.det_unique
- \+ *lemma* matrix.upper_two_block_triangular_det

Modified src/linear_algebra/matrix.lean
- \+ *def* matrix.block_triangular_matrix'
- \+ *def* matrix.block_triangular_matrix
- \+ *lemma* matrix.det_of_block_triangular_matrix''
- \+ *lemma* matrix.det_of_block_triangular_matrix'
- \+ *lemma* matrix.det_of_block_triangular_matrix
- \+ *lemma* matrix.det_of_lower_triangular
- \+ *lemma* matrix.det_of_upper_triangular
- \+ *lemma* matrix.det_to_block
- \+ *lemma* matrix.det_to_square_block'
- \+ *lemma* matrix.det_to_square_block
- \+ *lemma* matrix.equiv_block_det
- \+ *lemma* matrix.to_square_block_det''
- \+ *lemma* matrix.two_block_triangular_det
- \+ *lemma* matrix.upper_two_block_triangular'
- \+ *lemma* matrix.upper_two_block_triangular



## [2021-03-10 17:05:28](https://github.com/leanprover-community/mathlib/commit/664feed)
chore(topology/algebra/ordered): add some `at_bot` versions of lemmas ([#6618](https://github.com/leanprover-community/mathlib/pull/6618))
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_bot_cinfi
- \+ *lemma* tendsto_at_bot_csupr
- \+ *lemma* tendsto_at_bot_infi
- \+ *lemma* tendsto_at_bot_supr



## [2021-03-10 17:05:27](https://github.com/leanprover-community/mathlib/commit/f675a86)
feat(data/real/{nnreal,ennreal}): add (e)nnreal.of_real_bit0/bit1 ([#6617](https://github.com/leanprover-community/mathlib/pull/6617))
Add bit0/bit1 lemmas for `nnreal.of_real`, `ennreal.of_real` and `ennreal.to_nnreal`.
With these additions, it is for example possible to prove `h : ennreal.of_real (2 : ℝ) = 2 := by simp`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.of_real_bit0
- \+ *lemma* ennreal.of_real_bit1
- \+ *lemma* ennreal.to_nnreal_bit0
- \+ *lemma* ennreal.to_nnreal_bit1
- \+ *lemma* ennreal.to_real_bit0
- \+ *lemma* ennreal.to_real_bit1

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.of_real_bit0
- \+ *lemma* nnreal.of_real_bit1



## [2021-03-10 17:05:26](https://github.com/leanprover-community/mathlib/commit/df1337e)
feat(data/local_equiv,topology/local_homeomorph): add `local_equiv.pi` and `local_homeomorph.pi` ([#6574](https://github.com/leanprover-community/mathlib/pull/6574))
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \+ *lemma* local_equiv.pi_coe
- \+ *lemma* local_equiv.pi_symm

Modified src/data/set/basic.lean
- \+ *lemma* set.range_dcomp

Modified src/topology/constructions.lean
- \+ *lemma* continuous_at_pi

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_pi
- \+ *lemma* continuous_within_at_pi

Modified src/topology/local_homeomorph.lean
- \+ *def* local_homeomorph.pi



## [2021-03-10 11:57:13](https://github.com/leanprover-community/mathlib/commit/e221dc9)
feat(ring_theory/hahn_series): algebra structure, equivalences with power series ([#6540](https://github.com/leanprover-community/mathlib/pull/6540))
Places an `algebra` structure on `hahn_series`
Defines a `ring_equiv` and when relevant an `alg_equiv` between `hahn_series nat R` and `power_series R`.
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/order/well_founded_set.lean
- \+ *lemma* set.is_wf_univ_iff
- \+ *lemma* well_founded.is_wf

Modified src/ring_theory/hahn_series.lean
- \+ *def* hahn_series.C
- \+ *lemma* hahn_series.C_apply
- \+ *theorem* hahn_series.C_eq_algebra_map
- \+ *lemma* hahn_series.C_mul_eq_smul
- \+ *lemma* hahn_series.C_one
- \+ *lemma* hahn_series.C_zero
- \+/\- *lemma* hahn_series.add_coeff'
- \+/\- *lemma* hahn_series.add_coeff
- \+ *theorem* hahn_series.algebra_map_apply
- \+ *lemma* hahn_series.coeff_to_power_series
- \+ *lemma* hahn_series.coeff_to_power_series_symm
- \+ *lemma* hahn_series.eq_of_mem_support_single
- \+ *lemma* hahn_series.mul_single_coeff_add
- \+ *def* hahn_series.single.add_monoid_hom
- \+ *lemma* hahn_series.single.add_monoid_hom_apply
- \+ *def* hahn_series.single.linear_map
- \+ *lemma* hahn_series.single.linear_map_apply
- \+/\- *def* hahn_series.single
- \+/\- *lemma* hahn_series.single_eq_zero
- \+ *lemma* hahn_series.single_mul_coeff_add
- \+ *lemma* hahn_series.single_mul_single
- \+ *lemma* hahn_series.single_zero_mul_coeff
- \+ *lemma* hahn_series.support_single_subset
- \+ *def* hahn_series.to_power_series
- \+ *def* hahn_series.to_power_series_alg
- \+ *lemma* hahn_series.to_power_series_alg_apply
- \+ *lemma* hahn_series.to_power_series_alg_symm_apply

Modified src/ring_theory/power_series/basic.lean
- \+ *theorem* mv_power_series.C_eq_algebra_map
- \+ *theorem* mv_power_series.algebra_map_apply
- \+ *theorem* power_series.C_eq_algebra_map
- \+ *theorem* power_series.algebra_map_apply



## [2021-03-10 11:57:12](https://github.com/leanprover-community/mathlib/commit/eaa0218)
feat(category_theory/triangulated/basic): add definitions of additive category and triangle ([#6539](https://github.com/leanprover-community/mathlib/pull/6539))
This PR adds the definition of an additive category and the definition of a triangle in an additive category with an additive shift.
#### Estimated changes
Added src/category_theory/additive/basic.lean


Added src/category_theory/triangulated/basic.lean
- \+ *structure* category_theory.triangulated.triangle
- \+ *def* category_theory.triangulated.triangle_morphism.comp
- \+ *lemma* category_theory.triangulated.triangle_morphism.comp_assoc
- \+ *lemma* category_theory.triangulated.triangle_morphism.comp_id
- \+ *lemma* category_theory.triangulated.triangle_morphism.id_comp
- \+ *structure* category_theory.triangulated.triangle_morphism
- \+ *def* category_theory.triangulated.triangle_morphism_id



## [2021-03-10 11:57:10](https://github.com/leanprover-community/mathlib/commit/a7f1e3c)
feat(normed_group): tendsto_at_top ([#6525](https://github.com/leanprover-community/mathlib/pull/6525))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* normed_group.tendsto_at_top'
- \+ *lemma* normed_group.tendsto_at_top

Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.tendsto_at_top'



## [2021-03-10 11:57:09](https://github.com/leanprover-community/mathlib/commit/ccd35db)
feat(linear_algebra/matrix): to_matrix and to_lin as alg_equiv ([#6496](https://github.com/leanprover-community/mathlib/pull/6496))
The existing `linear_map.to_matrix` and `matrix.to_lin` can be upgraded to an `alg_equiv` if working on linear endomorphisms or square matrices. The API is copied over in rote fashion.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* matrix.algebra_map_eq_smul

Modified src/linear_algebra/matrix.lean
- \+ *def* linear_map.to_matrix_alg_equiv'
- \+ *lemma* linear_map.to_matrix_alg_equiv'_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv'_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv'_id
- \+ *lemma* linear_map.to_matrix_alg_equiv'_mul
- \+ *lemma* linear_map.to_matrix_alg_equiv'_symm
- \+ *lemma* linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'
- \+ *def* linear_map.to_matrix_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply'
- \+ *lemma* linear_map.to_matrix_alg_equiv_apply
- \+ *lemma* linear_map.to_matrix_alg_equiv_comp
- \+ *lemma* linear_map.to_matrix_alg_equiv_id
- \+ *lemma* linear_map.to_matrix_alg_equiv_mul
- \+ *theorem* linear_map.to_matrix_alg_equiv_range
- \+ *lemma* linear_map.to_matrix_alg_equiv_symm
- \+ *lemma* linear_map.to_matrix_alg_equiv_to_lin_alg_equiv
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply'
- \+ *lemma* linear_map.to_matrix_alg_equiv_transpose_apply
- \+ *def* matrix.to_lin_alg_equiv'
- \+ *lemma* matrix.to_lin_alg_equiv'_apply
- \+ *lemma* matrix.to_lin_alg_equiv'_mul
- \+ *lemma* matrix.to_lin_alg_equiv'_one
- \+ *lemma* matrix.to_lin_alg_equiv'_symm
- \+ *lemma* matrix.to_lin_alg_equiv'_to_matrix_alg_equiv'
- \+ *def* matrix.to_lin_alg_equiv
- \+ *lemma* matrix.to_lin_alg_equiv_apply
- \+ *lemma* matrix.to_lin_alg_equiv_mul
- \+ *lemma* matrix.to_lin_alg_equiv_one
- \+ *lemma* matrix.to_lin_alg_equiv_self
- \+ *lemma* matrix.to_lin_alg_equiv_symm
- \+ *lemma* matrix.to_lin_alg_equiv_to_matrix_alg_equiv



## [2021-03-10 08:51:55](https://github.com/leanprover-community/mathlib/commit/b1ecc98)
feat(nat/digits): natural basis representation using list sum and map ([#5975](https://github.com/leanprover-community/mathlib/pull/5975))
#### Estimated changes
Modified src/data/list/zip.lean
- \+ *lemma* list.sum_zip_with_distrib_left

Modified src/data/nat/digits.lean
- \+ *lemma* nat.of_digits_eq_sum_map_with_index
- \+ *lemma* nat.of_digits_eq_sum_map_with_index_aux



## [2021-03-10 02:23:34](https://github.com/leanprover-community/mathlib/commit/fad44b9)
feat(ring_theory/ideal/operations): add quotient_equiv ([#6492](https://github.com/leanprover-community/mathlib/pull/6492))
The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`,  where `J = f(I)`, and similarly for algebras.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.comap_of_equiv
- \+ *lemma* ideal.map_comap_of_equiv
- \+ *lemma* ideal.map_of_equiv
- \+ *def* ideal.quotient_equiv
- \+ *def* ideal.quotient_equiv_alg
- \+ *lemma* ideal.quotient_map_comp_mkₐ
- \+ *lemma* ideal.quotient_map_mkₐ
- \+ *def* ideal.quotient_mapₐ



## [2021-03-10 02:23:33](https://github.com/leanprover-community/mathlib/commit/4e370b5)
feat(topology): shrinking lemma ([#6478](https://github.com/leanprover-community/mathlib/pull/6478))
### Add a few versions of the shrinking lemma:
* `exists_subset_Union_closure_subset` and `exists_Union_eq_closure_subset`: shrinking lemma for general normal spaces;
* `exists_subset_Union_ball_radius_lt`, `exists_Union_ball_eq_radius_lt`, `exists_subset_Union_ball_radius_pos_lt`, `exists_Union_ball_eq_radius_pos_lt`: shrinking lemma for coverings by open balls in a proper metric space;
* `exists_locally_finite_subset_Union_ball_radius_lt`, `exists_locally_finite_Union_eq_ball_radius_lt`: given a positive function `R : X → ℝ`, finds a locally finite covering by open balls `ball (c i) (r' i)`, `r' i < R` and a subcovering by balls of strictly smaller radius `ball (c i) (r i)`, `0 < r i < r' i`.
### Other API changes
* add `@[simp]` to `set.compl_subset_compl`;
* add `is_closed_bInter` and `locally_finite.point_finite`;
* add `metric.closed_ball_subset_closed_ball`, `metric.uniformity_basis_dist_lt`, `exists_pos_lt_subset_ball`, and `exists_lt_subset_ball`;
* generalize `refinement_of_locally_compact_sigma_compact_of_nhds_basis` to `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set`, replace arguments `(s : X → set X) (hs : ∀ x, s x ∈ 𝓝 x)` with a hint to use `filter.has_basis.restrict_subset` if needed.
* make `s` and `t` arguments of `normal_separation` implicit;
* add `normal_exists_closure_subset`;
* turn `sigma_compact_space_of_locally_compact_second_countable` into an `instance`.
#### Estimated changes
Modified roadmap/topology/shrinking_lemma.lean
- \+ *lemma* roadmap.shrinking_lemma
- \- *lemma* shrinking_lemma

Modified src/data/set/basic.lean
- \+/\- *lemma* set.compl_subset_compl

Modified src/topology/basic.lean
- \+ *lemma* is_closed_bInter
- \+ *lemma* locally_finite.point_finite

Modified src/topology/metric_space/basic.lean
- \+ *lemma* exists_Union_ball_eq_radius_lt
- \+ *lemma* exists_Union_ball_eq_radius_pos_lt
- \+ *lemma* exists_locally_finite_Union_eq_ball_radius_lt
- \+ *lemma* exists_locally_finite_subset_Union_ball_radius_lt
- \+ *lemma* exists_lt_subset_ball
- \+ *lemma* exists_pos_lt_subset_ball
- \+ *lemma* exists_subset_Union_ball_radius_lt
- \+ *lemma* exists_subset_Union_ball_radius_pos_lt
- \+ *theorem* metric.closed_ball_subset_ball
- \+ *theorem* metric.uniformity_basis_dist_lt

Modified src/topology/paracompact.lean
- \+ *theorem* refinement_of_locally_compact_sigma_compact_of_nhds_basis_set

Modified src/topology/separation.lean
- \+ *theorem* normal_exists_closure_subset
- \+/\- *theorem* normal_separation

Added src/topology/shrinking_lemma.lean
- \+ *lemma* exists_Union_eq_closure_subset
- \+ *lemma* exists_subset_Union_closure_subset
- \+ *lemma* shrinking_lemma.partial_refinement.apply_eq
- \+ *lemma* shrinking_lemma.partial_refinement.apply_eq_of_chain
- \+ *def* shrinking_lemma.partial_refinement.chain_Sup
- \+ *def* shrinking_lemma.partial_refinement.chain_Sup_carrier
- \+ *lemma* shrinking_lemma.partial_refinement.closure_subset
- \+ *lemma* shrinking_lemma.partial_refinement.exists_gt
- \+ *def* shrinking_lemma.partial_refinement.find
- \+ *lemma* shrinking_lemma.partial_refinement.find_apply_of_mem
- \+ *lemma* shrinking_lemma.partial_refinement.find_mem
- \+ *lemma* shrinking_lemma.partial_refinement.le_chain_Sup
- \+ *lemma* shrinking_lemma.partial_refinement.mem_find_carrier_iff
- \+ *lemma* shrinking_lemma.partial_refinement.subset_Union
- \+ *structure* shrinking_lemma.partial_refinement

Modified src/topology/subset_properties.lean
- \- *lemma* sigma_compact_space_of_locally_compact_second_countable



## [2021-03-10 02:23:32](https://github.com/leanprover-community/mathlib/commit/05d3955)
feat(number_theory/bernoulli): bernoulli_power_series ([#6456](https://github.com/leanprover-community/mathlib/pull/6456))
Co-authored-by Ashvni Narayanan
#### Estimated changes
Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* finset.nat.antidiagonal_congr

Modified src/number_theory/bernoulli.lean
- \+ *lemma* bernoulli'_eq_bernoulli
- \+ *def* bernoulli'_power_series
- \- *theorem* bernoulli'_power_series
- \+ *theorem* bernoulli'_power_series_mul_exp_sub_one
- \+ *def* bernoulli_power_series
- \+ *theorem* bernoulli_power_series_mul_exp_sub_one
- \+ *lemma* bernoulli_spec'



## [2021-03-10 02:23:31](https://github.com/leanprover-community/mathlib/commit/c962871)
feat(linear_algebra): linear_independent_fin_snoc ([#6455](https://github.com/leanprover-community/mathlib/pull/6455))
A slight variation on the existing `linear_independent_fin_cons`.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+/\- *lemma* fin_add_flip_apply_left

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent_fin_snoc
- \+ *lemma* linear_independent_fin_succ'



## [2021-03-09 21:43:56](https://github.com/leanprover-community/mathlib/commit/b697e52)
refactor(ring_theory/power_series/basic): simplify truncation ([#6605](https://github.com/leanprover-community/mathlib/pull/6605))
I'm trying to reduce how much finsupp leaks through the polynomial API, in this case it works quite nicely.
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_power_series.coeff_trunc_fun



## [2021-03-09 21:43:55](https://github.com/leanprover-community/mathlib/commit/09a505a)
feat(ring_theory/witt_vector): use structure instead of irreducible ([#6604](https://github.com/leanprover-community/mathlib/pull/6604))
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.cons_fin_one

Modified src/ring_theory/witt_vector/basic.lean
- \+/\- *def* witt_vector.map_fun
- \+ *lemma* witt_vector.matrix_vec_empty_coeff

Modified src/ring_theory/witt_vector/defs.lean
- \- *def* witt_vector.coeff
- \+/\- *lemma* witt_vector.coeff_mk
- \- *def* witt_vector.mk
- \+ *lemma* witt_vector.v2_coeff
- \+ *structure* witt_vector
- \- *def* witt_vector

Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/ring_theory/witt_vector/is_poly.lean


Modified src/ring_theory/witt_vector/teichmuller.lean
- \+/\- *def* witt_vector.teichmuller_fun

Modified src/ring_theory/witt_vector/truncated.lean


Modified src/ring_theory/witt_vector/verschiebung.lean




## [2021-03-09 21:43:53](https://github.com/leanprover-community/mathlib/commit/18d4e51)
chore(algebra/ring/basic): weaken ring.inverse to only require monoid_with_zero ([#6603](https://github.com/leanprover-community/mathlib/pull/6603))
Split from [#5539](https://github.com/leanprover-community/mathlib/pull/5539) because I actually want to use this, and the PR is large and stalled.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* ring.inverse_non_unit
- \+/\- *lemma* ring.inverse_unit



## [2021-03-09 21:43:52](https://github.com/leanprover-community/mathlib/commit/fb674e1)
feat(data/finset/lattice): map_sup, map_inf ([#6601](https://github.com/leanprover-community/mathlib/pull/6601))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.map_inf
- \+ *lemma* finset.map_sup



## [2021-03-09 21:43:51](https://github.com/leanprover-community/mathlib/commit/be6753c)
feat(data/{list,multiset,finset}): map_filter ([#6600](https://github.com/leanprover-community/mathlib/pull/6600))
This renames `list.filter_of_map` to `list.map_filter`, which unifies the name of the `map_filter` lemmas for lists and finsets, and adds a corresponding lemma for multisets.
Unfortunately, the name `list.filter_map` is already used for a definition.
#### Estimated changes
Modified src/data/finset/basic.lean


Modified src/data/list/basic.lean
- \- *theorem* list.filter_of_map
- \+ *theorem* list.map_filter

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.map_filter



## [2021-03-09 21:43:50](https://github.com/leanprover-community/mathlib/commit/366a23f)
feat(topology/constructions): frontier/interior/closure in `X × Y` ([#6594](https://github.com/leanprover-community/mathlib/pull/6594))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.prod_diff_prod

Modified src/order/filter/basic.lean
- \+ *lemma* filter.prod_mem_prod_iff

Modified src/topology/algebra/ordered.lean
- \+ *lemma* frontier_Ici_subset
- \+ *lemma* frontier_Iic_subset

Modified src/topology/basic.lean
- \+ *lemma* frontier_empty
- \+ *lemma* frontier_univ

Modified src/topology/constructions.lean
- \+ *lemma* frontier_prod_eq
- \+ *lemma* frontier_prod_univ_eq
- \+ *lemma* frontier_univ_prod_eq
- \+ *lemma* interior_prod_eq
- \+ *lemma* prod_mem_nhds_iff



## [2021-03-09 21:43:49](https://github.com/leanprover-community/mathlib/commit/9ff7458)
feat(algebra/group_power/basic): add abs_add_eq_add_abs_iff ([#6593](https://github.com/leanprover-community/mathlib/pull/6593))
I've added
```
lemma abs_add_eq_add_abs_iff {α : Type*} [linear_ordered_add_comm_group α]  (a b : α) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0)
```
from `lean-liquid`. For some reasons I am not able to use `wlog hle : a ≤ b using [a b, b a]` at the beginning of the proof, Lean says `unknown identifier 'wlog'` and if I try to import `tactic.wlog` I have tons of errors.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* abs_add_eq_add_abs_iff
- \+ *lemma* abs_add_eq_add_abs_le
- \+ *lemma* abs_gsmul
- \+ *lemma* abs_nsmul



## [2021-03-09 21:43:47](https://github.com/leanprover-community/mathlib/commit/8e246cb)
refactor(data/mv_polynomial): cleanup equivs ([#6589](https://github.com/leanprover-community/mathlib/pull/6589))
This:
* Replaces `alg_equiv_congr_left` with `rename_equiv` (to match `rename`)
* Removes `ring_equiv_congr_left` (it's now `rename_equiv.to_ring_equiv`)
* Renames `alg_equiv_congr_right` to `map_alg_equiv` (to match `map`) and removes the `comap` from the definition
* Renames `ring_equiv_congr_right` to `map_equiv` (to match `map`)
* Removes `alg_equiv_congr` (it's now `(map_alg_equiv R e).trans $ (rename_equiv e_var).restrict_scalars _`, which while longer is never used anyway)
* Removes `ring_equiv_congr` (it's now `(map_equiv R e).trans $ (rename_equiv e_var).to_ring_equiv`, which while longer is never used anyway)
* Replaces `punit_ring_equiv` with `punit_alg_equiv`
* Removes `comap` from the definition of `sum_alg_equiv`
* Promotes `option_equiv_left`, `option_equiv_right`, and `fin_succ_equiv` to `alg_equiv`s
This is a follow-up to [#6420](https://github.com/leanprover-community/mathlib/pull/6420)
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \- *def* mv_polynomial.alg_equiv_congr
- \- *def* mv_polynomial.alg_equiv_congr_left
- \- *lemma* mv_polynomial.alg_equiv_congr_left_apply
- \- *lemma* mv_polynomial.alg_equiv_congr_left_symm_apply
- \- *def* mv_polynomial.alg_equiv_congr_right
- \- *lemma* mv_polynomial.alg_equiv_congr_right_apply
- \- *lemma* mv_polynomial.alg_equiv_congr_right_symm_apply
- \+ *def* mv_polynomial.map_alg_equiv
- \+ *lemma* mv_polynomial.map_alg_equiv_apply
- \+ *lemma* mv_polynomial.map_alg_equiv_refl
- \+ *lemma* mv_polynomial.map_alg_equiv_symm
- \+ *lemma* mv_polynomial.map_alg_equiv_trans
- \+ *def* mv_polynomial.map_equiv
- \+ *lemma* mv_polynomial.map_equiv_refl
- \+ *lemma* mv_polynomial.map_equiv_symm
- \+ *lemma* mv_polynomial.map_equiv_trans
- \+/\- *def* mv_polynomial.option_equiv_left
- \+/\- *def* mv_polynomial.option_equiv_right
- \+ *def* mv_polynomial.punit_alg_equiv
- \- *def* mv_polynomial.punit_ring_equiv
- \- *def* mv_polynomial.ring_equiv_congr
- \- *def* mv_polynomial.ring_equiv_congr_left
- \- *lemma* mv_polynomial.ring_equiv_congr_left_apply
- \- *lemma* mv_polynomial.ring_equiv_congr_left_symm_apply
- \- *def* mv_polynomial.ring_equiv_congr_right
- \- *lemma* mv_polynomial.ring_equiv_congr_right_apply
- \- *lemma* mv_polynomial.ring_equiv_congr_right_symm_apply

Modified src/data/mv_polynomial/funext.lean


Modified src/data/mv_polynomial/rename.lean
- \+ *def* mv_polynomial.rename_equiv
- \+ *lemma* mv_polynomial.rename_equiv_refl
- \+ *lemma* mv_polynomial.rename_equiv_symm
- \+ *lemma* mv_polynomial.rename_equiv_trans

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-03-09 21:43:46](https://github.com/leanprover-community/mathlib/commit/5d82d1d)
feat(algebra,linear_algebra): `{smul,lmul,lsmul}_injective` ([#6588](https://github.com/leanprover-community/mathlib/pull/6588))
This PR proves a few injectivity results for (scalar) multiplication in the setting of modules and algebras over a ring.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.lmul_injective
- \+ *lemma* algebra.lmul_left_injective
- \+ *lemma* algebra.lmul_right_injective

Modified src/algebra/algebra/tower.lean
- \+ *lemma* algebra.lsmul_injective

Modified src/algebra/group_with_zero/defs.lean
- \+ *lemma* mul_left_injective'
- \+ *lemma* mul_right_injective'

Modified src/algebra/module/basic.lean
- \+ *lemma* smul_injective

Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* linear_map.lsmul_injective



## [2021-03-09 21:43:45](https://github.com/leanprover-community/mathlib/commit/3d75242)
chore(data/equiv/local_equiv,topology/local_homeomorph): put `source`/`target` to the left in `∩` ([#6583](https://github.com/leanprover-community/mathlib/pull/6583))
#### Estimated changes
Modified src/data/equiv/local_equiv.lean
- \- *lemma* local_equiv.image_inter_source_eq'
- \- *lemma* local_equiv.image_inter_source_eq
- \+ *lemma* local_equiv.image_source_inter_eq'
- \+ *lemma* local_equiv.image_source_inter_eq
- \- *lemma* local_equiv.symm_image_inter_target_eq'
- \- *lemma* local_equiv.symm_image_inter_target_eq
- \+ *lemma* local_equiv.symm_image_target_inter_eq'
- \+ *lemma* local_equiv.symm_image_target_inter_eq

Modified src/data/set/function.lean
- \+ *theorem* set.eq_on.inter_preimage_eq

Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* local_homeomorph.continuous_at_iff_continuous_at_comp_left
- \- *lemma* local_homeomorph.image_inter_source_eq'
- \- *lemma* local_homeomorph.image_inter_source_eq
- \+/\- *lemma* local_homeomorph.image_open_of_open'
- \+ *lemma* local_homeomorph.image_source_inter_eq'
- \+ *lemma* local_homeomorph.image_source_inter_eq
- \+ *lemma* local_homeomorph.map_nhds_within_preimage_eq
- \+ *lemma* local_homeomorph.nhds_within_source_inter
- \+ *lemma* local_homeomorph.nhds_within_target_inter
- \+ *lemma* local_homeomorph.source_inter_preimage_inv_preimage
- \- *lemma* local_homeomorph.symm_image_inter_target_eq
- \+ *lemma* local_homeomorph.symm_image_target_inter_eq
- \+ *lemma* local_homeomorph.target_inter_inv_preimage_preimage



## [2021-03-09 21:43:44](https://github.com/leanprover-community/mathlib/commit/78af5b1)
feat(topology): closure in a `pi` space ([#6575](https://github.com/leanprover-community/mathlib/pull/6575))
Also add `can_lift` instances that lift `f : subtype p → β` to `f : α → β` and a version of `filter.mem_infi_iff` that uses a globally defined function.
#### Estimated changes
Modified src/data/set/basic.lean


Modified src/data/set/function.lean
- \+ *lemma* set.pi_piecewise
- \+ *lemma* set.univ_pi_piecewise

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.inf_principal_eq_bot
- \+ *lemma* filter.infi_principal_finite
- \+ *lemma* filter.mem_infi_iff'

Modified src/order/lattice.lean
- \+ *lemma* inf_right_comm
- \+ *lemma* sup_right_comm

Modified src/tactic/lift.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/constructions.lean
- \+ *lemma* is_closed_set_pi

Modified src/topology/continuous_on.lean
- \+ *lemma* closure_pi_set
- \+ *lemma* dense_pi
- \+ *lemma* mem_closure_pi
- \+ *lemma* nhds_within_pi_eq'
- \+ *lemma* nhds_within_pi_eq
- \+ *lemma* nhds_within_pi_eq_bot
- \+ *lemma* nhds_within_pi_ne_bot
- \+ *lemma* nhds_within_pi_univ_eq
- \+ *lemma* nhds_within_pi_univ_eq_bot



## [2021-03-09 21:43:43](https://github.com/leanprover-community/mathlib/commit/792e492)
feat(topology/separation): add API for interaction between discrete topology and subsets ([#6570](https://github.com/leanprover-community/mathlib/pull/6570))
The final result:
Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.
The proofs are by Patrick Massot.
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* discrete_topology.of_subset
- \+ *lemma* discrete_topology_iff_nhds
- \+ *lemma* discrete_topology_induced
- \+ *lemma* induced_bot
- \+ *lemma* topological_space.subset_trans



## [2021-03-09 16:22:20](https://github.com/leanprover-community/mathlib/commit/8713c0b)
feat(measure/pi): prove extensionality for `measure.pi` ([#6304](https://github.com/leanprover-community/mathlib/pull/6304))
* If two measures in a finitary product are equal on cubes with measurable sides (or with sides in a set generating the corresponding sigma-algebra), then the measures are equal.
* Add `sigma_finite` instance for `measure.pi`
* Some basic lemmas about sets (more specifically `Union` and `set.pi`)
* rename `measurable_set.pi_univ` -> `measurable_set.univ_pi` (`pi univ t` is called `univ_pi` consistently in `set/basic`, but it's not always consistent elsewhere)
* rename `[bs]?Union_prod` -> `[bs]?Union_prod_const`
#### Estimated changes
Modified src/data/equiv/encodable/basic.lean
- \+ *lemma* encodable.surjective_decode_iget

Modified src/data/nat/pairing.lean
- \+ *lemma* nat.surjective_unpair

Modified src/data/set/basic.lean
- \+ *lemma* set.eval_preimage'
- \+ *lemma* set.eval_preimage
- \+ *lemma* set.univ_pi_ite

Modified src/data/set/lattice.lean
- \+ *lemma* function.surjective.Inter_comp
- \+ *lemma* function.surjective.Union_comp
- \+ *lemma* set.Inter_congr
- \+ *lemma* set.Union_congr
- \+/\- *lemma* set.Union_of_singleton
- \+/\- *lemma* set.Union_prod
- \+ *lemma* set.Union_prod_const
- \+/\- *lemma* set.Union_subset_Union2
- \+/\- *lemma* set.Union_subset_Union_const
- \+ *lemma* set.Union_univ_pi
- \- *lemma* set.bUnion_prod
- \+ *lemma* set.bUnion_prod_const
- \+/\- *lemma* set.directed_on_Union
- \+/\- *theorem* set.preimage_Union
- \- *lemma* set.sUnion_prod
- \+ *lemma* set.sUnion_prod_const
- \+ *lemma* set.univ_pi_eq_Inter

Modified src/measure_theory/measurable_space.lean
- \- *lemma* measurable_set.pi_univ
- \+ *lemma* measurable_set.univ_pi
- \+ *lemma* measurable_set.univ_pi_fintype

Modified src/measure_theory/pi.lean
- \+ *lemma* generate_from_eq_pi
- \+ *lemma* generate_from_pi
- \+ *lemma* generate_from_pi_eq
- \+ *lemma* is_countably_spanning.pi
- \+ *lemma* is_pi_system.pi
- \+ *lemma* is_pi_system_pi
- \+ *def* measure_theory.measure.finite_spanning_sets_in.pi
- \+ *lemma* measure_theory.measure.pi_eq
- \+ *lemma* measure_theory.measure.pi_eq_generate_from
- \+/\- *lemma* measure_theory.measure.pi_pi

Modified src/measure_theory/prod.lean




## [2021-03-09 11:19:52](https://github.com/leanprover-community/mathlib/commit/c1a7c19)
chore(data/polynomial/basic): add missing is_scalar_tower and smul_comm_class instances ([#6592](https://github.com/leanprover-community/mathlib/pull/6592))
These already exist for `mv_polynomial`, but the PR that I added them in forgot to add them for `polynomial`.
Notably, this provides the instance `is_scalar_tower R (mv_polynomial S₁ R) (polynomial (mv_polynomial S₁ R))`.
#### Estimated changes
Modified src/data/polynomial/basic.lean




## [2021-03-09 11:19:51](https://github.com/leanprover-community/mathlib/commit/fa28a8c)
feat(data/nat/parity): even/odd.mul_even/odd ([#6584](https://github.com/leanprover-community/mathlib/pull/6584))
Lemmas pertaining to the multiplication of even and odd natural numbers.
#### Estimated changes
Modified src/data/nat/parity.lean
- \+ *theorem* nat.even.mul_left
- \+ *theorem* nat.even.mul_right
- \+ *theorem* nat.even_div
- \- *lemma* nat.even_div
- \+ *theorem* nat.odd.mul
- \+ *theorem* nat.odd.of_mul_left
- \+ *theorem* nat.odd.of_mul_right
- \+ *theorem* nat.odd_mul
- \+/\- *lemma* nat.two_not_dvd_two_mul_sub_one



## [2021-03-09 11:19:50](https://github.com/leanprover-community/mathlib/commit/49afae5)
feat(number_theory/bernoulli): bernoulli_poly_eval_one ([#6581](https://github.com/leanprover-community/mathlib/pull/6581))
#### Estimated changes
Modified src/number_theory/bernoulli.lean
- \- *theorem* bernoulli_eq_bernoulli'
- \+ *theorem* bernoulli_eq_bernoulli'_of_ne_one
- \+/\- *theorem* sum_bernoulli

Modified src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* bernoulli_poly.bernoulli_poly_eval_one



## [2021-03-09 11:19:49](https://github.com/leanprover-community/mathlib/commit/9889502)
feat(linear_algebra/pi): add `submodule.pi` ([#6576](https://github.com/leanprover-community/mathlib/pull/6576))
#### Estimated changes
Modified src/data/set/basic.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.coe_subset_coe
- \+ *lemma* submodule.sum_mem_bsupr
- \+ *lemma* submodule.sum_mem_supr

Modified src/linear_algebra/pi.lean
- \+ *lemma* submodule.binfi_comap_proj
- \+ *lemma* submodule.coe_pi
- \+ *lemma* submodule.infi_comap_proj
- \+ *lemma* submodule.mem_pi
- \+ *def* submodule.pi
- \+ *lemma* submodule.supr_map_single

Modified src/linear_algebra/prod.lean




## [2021-03-09 11:19:47](https://github.com/leanprover-community/mathlib/commit/a331113)
feat(analysis/normed_space/normed_group_hom): bounded homs between normed groups ([#6375](https://github.com/leanprover-community/mathlib/pull/6375))
From `lean-liquid`
#### Estimated changes
Added src/analysis/normed_space/normed_group_hom.lean
- \+ *def* add_monoid_hom.mk_normed_group_hom'
- \+ *def* add_monoid_hom.mk_normed_group_hom
- \+ *lemma* exists_pos_bound_of_bound
- \+ *lemma* normed_group_hom.add_apply
- \+ *theorem* normed_group_hom.antilipschitz_of_bound_by
- \+ *lemma* normed_group_hom.bound
- \+ *def* normed_group_hom.bound_by
- \+ *lemma* normed_group_hom.bound_by_one_of_isometry
- \+ *lemma* normed_group_hom.bounds_bdd_below
- \+ *lemma* normed_group_hom.bounds_nonempty
- \+ *lemma* normed_group_hom.coe_add
- \+ *def* normed_group_hom.coe_fn_add_hom
- \+ *lemma* normed_group_hom.coe_inj
- \+ *lemma* normed_group_hom.coe_inj_iff
- \+ *lemma* normed_group_hom.coe_injective
- \+ *lemma* normed_group_hom.coe_mk
- \+ *lemma* normed_group_hom.coe_mk_normed_group_hom'
- \+ *lemma* normed_group_hom.coe_mk_normed_group_hom
- \+ *lemma* normed_group_hom.coe_neg
- \+ *lemma* normed_group_hom.coe_sub
- \+ *lemma* normed_group_hom.coe_sum
- \+ *lemma* normed_group_hom.coe_to_add_monoid_hom
- \+ *lemma* normed_group_hom.coe_zero
- \+ *def* normed_group_hom.comp_hom
- \+ *lemma* normed_group_hom.comp_zero
- \+ *lemma* normed_group_hom.ext
- \+ *lemma* normed_group_hom.ext_iff
- \+ *def* normed_group_hom.id
- \+ *def* normed_group_hom.incl
- \+ *lemma* normed_group_hom.isometry_comp
- \+ *lemma* normed_group_hom.isometry_id
- \+ *lemma* normed_group_hom.isometry_iff_norm
- \+ *lemma* normed_group_hom.isometry_of_norm
- \+ *lemma* normed_group_hom.ker.incl_comp_lift
- \+ *def* normed_group_hom.ker.lift
- \+ *def* normed_group_hom.ker
- \+ *theorem* normed_group_hom.le_of_op_norm_le
- \+ *theorem* normed_group_hom.le_op_norm
- \+ *theorem* normed_group_hom.le_op_norm_of_le
- \+ *theorem* normed_group_hom.lipschitz
- \+ *lemma* normed_group_hom.lipschitz_of_bound_by
- \+ *lemma* normed_group_hom.map_add
- \+ *lemma* normed_group_hom.map_neg
- \+ *lemma* normed_group_hom.map_sub
- \+ *lemma* normed_group_hom.map_sum
- \+ *lemma* normed_group_hom.map_zero
- \+ *lemma* normed_group_hom.mem_ker
- \+ *lemma* normed_group_hom.mem_range
- \+ *lemma* normed_group_hom.mk_normed_group_hom'_bound_by
- \+ *lemma* normed_group_hom.mk_normed_group_hom_norm_le'
- \+ *lemma* normed_group_hom.mk_normed_group_hom_norm_le
- \+ *lemma* normed_group_hom.mk_to_add_monoid_hom
- \+ *lemma* normed_group_hom.neg_apply
- \+ *lemma* normed_group_hom.norm_comp_le
- \+ *lemma* normed_group_hom.norm_def
- \+ *lemma* normed_group_hom.norm_eq_of_isometry
- \+ *lemma* normed_group_hom.norm_id
- \+ *lemma* normed_group_hom.norm_id_le
- \+ *lemma* normed_group_hom.norm_noninc.bound_by_one
- \+ *lemma* normed_group_hom.norm_noninc.comp
- \+ *lemma* normed_group_hom.norm_noninc.id
- \+ *def* normed_group_hom.norm_noninc
- \+ *lemma* normed_group_hom.norm_noninc_of_isometry
- \+ *def* normed_group_hom.op_norm
- \+ *theorem* normed_group_hom.op_norm_add_le
- \+ *lemma* normed_group_hom.op_norm_le_bound
- \+ *theorem* normed_group_hom.op_norm_le_of_lipschitz
- \+ *lemma* normed_group_hom.op_norm_neg
- \+ *lemma* normed_group_hom.op_norm_nonneg
- \+ *theorem* normed_group_hom.op_norm_zero_iff
- \+ *def* normed_group_hom.range
- \+ *lemma* normed_group_hom.ratio_le_op_norm
- \+ *lemma* normed_group_hom.sub_apply
- \+ *lemma* normed_group_hom.sum_apply
- \+ *def* normed_group_hom.to_add_monoid_hom
- \+ *lemma* normed_group_hom.to_add_monoid_hom_injective
- \+ *lemma* normed_group_hom.to_fun_eq_coe
- \+ *lemma* normed_group_hom.zero_apply
- \+ *lemma* normed_group_hom.zero_comp
- \+ *structure* normed_group_hom

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* exists_pos_bound_of_bound



## [2021-03-09 08:12:31](https://github.com/leanprover-community/mathlib/commit/6dec23b)
chore(topology/algebra/ordered): use dot notation, golf some proofs ([#6595](https://github.com/leanprover-community/mathlib/pull/6595))
Use more precise typeclass arguments here and there, golf some proofs, use dot notation.
### Renamed lemmas
* `is_lub_of_is_lub_of_tendsto` → `is_lub.is_lub_of_tendsto`;
* `is_glb_of_is_glb_of_tendsto` → `is_glb.is_glb_of_tendsto`;
* `is_glb_of_is_lub_of_tendsto` → `is_lub.is_glb_of_tendsto`;
* `is_lub_of_is_glb_of_tendsto` → `is_glb.is_lub_of_tendsto`;
* `mem_closure_of_is_lub` → `is_lub.mem_closure`;
* `mem_of_is_lub_of_is_closed` → `is_lub.mem_of_is_closed`, `is_closed.is_lub_mem`;
* `mem_closure_of_is_glb` → `is_glb.mem_closure`;
* `mem_of_is_glb_of_is_closed` → `is_glb.mem_of_is_closed`, `is_closed.is_glb_mem`;
### New lemmas
* `is_lub.inter_Ici_of_mem`
* `is_glb.inter_Iic_of_mem`
* `frequently.filter_mono`
* `is_lub.frequently_mem`
* `is_lub.frequently_nhds_mem`
* `is_glb.frequently_mem`
* `is_glb.frequently_nhds_mem`
* `is_lub.mem_upper_bounds_of_tendsto`
* `is_glb.mem_lower_bounds_of_tendsto`
* `is_lub.mem_lower_bounds_of_tendsto`
* `is_glb.mem_upper_bounds_of_tendsto`
* `diff_subset_closure_iff`
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* is_glb.inter_Iic_of_mem
- \+ *lemma* is_lub.inter_Ici_of_mem

Modified src/order/filter/basic.lean
- \+ *lemma* filter.frequently.filter_mono

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_glb.frequently_mem
- \+ *lemma* is_glb.frequently_nhds_mem
- \+ *lemma* is_glb.is_glb_of_tendsto
- \+ *lemma* is_glb.is_lub_of_tendsto
- \+ *lemma* is_glb.mem_closure
- \+ *lemma* is_glb.mem_lower_bounds_of_tendsto
- \+ *lemma* is_glb.mem_of_is_closed
- \+ *lemma* is_glb.mem_upper_bounds_of_tendsto
- \- *lemma* is_glb_of_is_glb_of_tendsto
- \- *lemma* is_glb_of_is_lub_of_tendsto
- \+ *lemma* is_lub.frequently_mem
- \+ *lemma* is_lub.frequently_nhds_mem
- \+ *lemma* is_lub.is_glb_of_tendsto
- \+ *lemma* is_lub.is_lub_of_tendsto
- \+ *lemma* is_lub.mem_closure
- \+ *lemma* is_lub.mem_lower_bounds_of_tendsto
- \+ *lemma* is_lub.mem_of_is_closed
- \+ *lemma* is_lub.mem_upper_bounds_of_tendsto
- \- *lemma* is_lub_of_is_glb_of_tendsto
- \- *lemma* is_lub_of_is_lub_of_tendsto
- \- *lemma* mem_closure_of_is_glb
- \- *lemma* mem_closure_of_is_lub
- \- *lemma* mem_of_is_glb_of_is_closed
- \- *lemma* mem_of_is_lub_of_is_closed

Modified src/topology/basic.lean
- \+ *lemma* diff_subset_closure_iff

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.sub_supr



## [2021-03-09 02:15:11](https://github.com/leanprover-community/mathlib/commit/32bd00f)
refactor(topology/bounded_continuous_function): structure extending continuous_map ([#6521](https://github.com/leanprover-community/mathlib/pull/6521))
Convert `bounded_continuous_function` from a subtype to a structure extending `continuous_map`, and some minor improvements to `@[simp]` lemmas.
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+/\- *def* bounded_continuous_function.const
- \- *theorem* bounded_continuous_function.continuous_evalf
- \+ *def* bounded_continuous_function.mk_of_bound
- \+ *lemma* bounded_continuous_function.mk_of_bound_coe
- \+/\- *def* bounded_continuous_function.mk_of_compact
- \+ *lemma* bounded_continuous_function.mk_of_compact_apply
- \+/\- *def* bounded_continuous_function.mk_of_discrete
- \+ *lemma* bounded_continuous_function.mk_of_discrete_apply
- \+ *structure* bounded_continuous_function
- \- *def* bounded_continuous_function

Modified src/topology/continuous_map.lean
- \+ *lemma* continuous_map.comp_apply
- \+ *lemma* continuous_map.comp_coe
- \+ *lemma* continuous_map.const_apply
- \+ *lemma* continuous_map.const_coe
- \+ *lemma* continuous_map.id_apply
- \+ *lemma* continuous_map.id_coe
- \+ *lemma* continuous_map.to_fun_eq_coe

Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2021-03-08 19:42:23](https://github.com/leanprover-community/mathlib/commit/3e5d90d)
feat(algebra/continued_fractions) add determinant formula and approximations for error term ([#6461](https://github.com/leanprover-community/mathlib/pull/6461))
#### Estimated changes
Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/continued_fractions/computation/approximations.lean
- \+ *lemma* generalized_continued_fraction.abs_sub_convergents_le'
- \+ *theorem* generalized_continued_fraction.abs_sub_convergents_le
- \+ *lemma* generalized_continued_fraction.determinant
- \+ *lemma* generalized_continued_fraction.determinant_aux
- \+ *lemma* generalized_continued_fraction.sub_convergents_eq

Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean




## [2021-03-08 19:42:22](https://github.com/leanprover-community/mathlib/commit/0afdaab)
feat(linear_algebra): submodules of f.g. free modules are free ([#6178](https://github.com/leanprover-community/mathlib/pull/6178))
This PR proves the first half of the structure theorem for modules over a PID: if `R` is a principal ideal domain and `M` an `R`-module which is free and finitely generated (expressed by `is_basis R (b : ι → M)`, for a `[fintype ι]`), then all submodules of `M` are also free and finitely generated.
This result requires some lemmas about the rank of (free) modules (which in that case is basically the same as `fintype.card ι`). If `M` were a vector space, this could just be expressed as `findim R M`, but it isn't necessarily, so it can't be.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* fin.range_cons

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.range_map_nonempty

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.ext_elem
- \+ *lemma* is_basis.no_zero_smul_divisors
- \+ *lemma* is_basis.repr_eq_zero
- \+ *lemma* is_basis.smul_eq_zero

Added src/linear_algebra/free_module.lean
- \+ *lemma* eq_bot_of_generator_maximal_map_eq_zero
- \+ *lemma* eq_bot_of_rank_eq_zero
- \+ *lemma* generator_map_dvd_of_mem
- \+ *lemma* is_basis.card_le_card_of_linear_independent
- \+ *lemma* is_basis.card_le_card_of_linear_independent_aux
- \+ *lemma* ne_zero_of_ortho
- \+ *lemma* not_mem_of_ortho
- \+ *theorem* submodule.exists_is_basis
- \+ *lemma* submodule.exists_is_basis_of_le
- \+ *lemma* submodule.exists_is_basis_of_le_span
- \+ *def* submodule.induction_on_rank
- \+ *def* submodule.induction_on_rank_aux

Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.fin_cons'



## [2021-03-08 17:02:28](https://github.com/leanprover-community/mathlib/commit/cdc222d)
chore(topology): add a few simple lemmas ([#6580](https://github.com/leanprover-community/mathlib/pull/6580))
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.image_closure

Modified src/topology/separation.lean
- \+ *lemma* compact_closure_of_subset_compact
- \+ *lemma* image_closure_of_compact



## [2021-03-08 17:02:27](https://github.com/leanprover-community/mathlib/commit/87eec0b)
feat(linear_algebra/bilinear_form): Existence of orthogonal basis with respect to a bilinear form ([#5814](https://github.com/leanprover-community/mathlib/pull/5814))
We state and prove the result that there exists an orthogonal basis with respect to a symmetric nondegenerate.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.span_singleton_sup_ker_eq_top

Modified src/linear_algebra/bilinear_form.lean
- \+ *def* bilin_form.is_Ortho
- \+ *lemma* bilin_form.is_Ortho_def
- \+ *lemma* bilin_form.is_compl_span_singleton_orthogonal
- \+ *lemma* bilin_form.is_ortho_def
- \+ *lemma* bilin_form.is_ortho_zero_left
- \+ *lemma* bilin_form.is_ortho_zero_right
- \+ *lemma* bilin_form.le_orthogonal_orthogonal
- \+ *lemma* bilin_form.linear_independent_of_is_Ortho
- \+ *lemma* bilin_form.mem_orthogonal_iff
- \+ *lemma* bilin_form.ne_zero_of_not_is_ortho_self
- \+ *def* bilin_form.nondegenerate
- \+ *theorem* bilin_form.nondegenerate_iff_ker_eq_bot
- \- *lemma* bilin_form.ortho_zero
- \+ *def* bilin_form.orthogonal
- \+ *lemma* bilin_form.orthogonal_le
- \+ *lemma* bilin_form.orthogonal_span_singleton_eq_to_lin_ker
- \+ *def* bilin_form.restrict
- \+ *lemma* bilin_form.restrict_orthogonal_span_singleton_nondegenerate
- \+ *lemma* bilin_form.restrict_sym
- \+ *lemma* bilin_form.span_singleton_inf_orthogonal_eq_bot
- \+ *lemma* bilin_form.span_singleton_sup_orthogonal_eq_top
- \+ *lemma* bilin_form.to_dual_def
- \+ *lemma* matrix.to_bilin'_apply'

Modified src/linear_algebra/dual.lean
- \+ *lemma* subspace.dual_findim_eq

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* linear_map.linear_equiv_of_ker_eq_bot_apply
- \+ *lemma* submodule.findim_add_eq_of_is_compl

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* bilin_form.exists_bilin_form_self_neq_zero
- \+ *lemma* bilin_form.exists_orthogonal_basis'
- \+ *theorem* bilin_form.exists_orthogonal_basis
- \+ *lemma* quadratic_form.exists_quadratic_form_neq_zero



## [2021-03-08 14:38:24](https://github.com/leanprover-community/mathlib/commit/6791ed9)
chore(algebra/module/linear_map): add linear_map.to_distrib_mul_action_hom ([#6573](https://github.com/leanprover-community/mathlib/pull/6573))
My aim in adding this is primarily to give the reader a hint that `distrib_mul_action_hom` exists.
The only difference between the two is that `linear_map` can infer `map_zero'` from its typeclass arguments.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *def* linear_map.to_distrib_mul_action_hom



## [2021-03-08 14:38:23](https://github.com/leanprover-community/mathlib/commit/13d86df)
chore(algebra/monoid_algebra): provide finer-grained levels of structure for less-structured `G`. ([#6572](https://github.com/leanprover-community/mathlib/pull/6572))
This provides `distrib` and `mul_zero_class` for when `G` is just `has_mul`, and `semigroup` for when `G` is just `semigroup`.
It also weakens the typeclass assumptions on some correspondings lemmas.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* add_monoid_algebra.lift_nc_smul
- \+/\- *lemma* add_monoid_algebra.mul_apply
- \+/\- *lemma* add_monoid_algebra.mul_apply_antidiagonal
- \+/\- *lemma* add_monoid_algebra.mul_single_apply_aux
- \+/\- *lemma* add_monoid_algebra.mul_single_zero_apply
- \+/\- *def* add_monoid_algebra.of
- \+/\- *lemma* add_monoid_algebra.of_apply
- \+/\- *lemma* add_monoid_algebra.of_injective
- \+/\- *lemma* add_monoid_algebra.single_mul_apply_aux
- \+/\- *lemma* add_monoid_algebra.single_mul_single
- \+/\- *lemma* add_monoid_algebra.single_zero_mul_apply
- \+/\- *lemma* add_monoid_algebra.support_mul
- \+/\- *lemma* monoid_algebra.lift_nc_smul
- \+/\- *lemma* monoid_algebra.map_domain_mul
- \+/\- *lemma* monoid_algebra.mul_apply
- \+/\- *lemma* monoid_algebra.mul_apply_antidiagonal
- \+/\- *lemma* monoid_algebra.mul_single_apply_aux
- \+/\- *lemma* monoid_algebra.mul_single_one_apply
- \+/\- *lemma* monoid_algebra.of_apply
- \+/\- *lemma* monoid_algebra.of_injective
- \+/\- *lemma* monoid_algebra.single_mul_apply_aux
- \+/\- *lemma* monoid_algebra.single_mul_single
- \+/\- *lemma* monoid_algebra.single_one_mul_apply
- \+/\- *lemma* monoid_algebra.single_pow
- \+/\- *lemma* monoid_algebra.support_mul



## [2021-03-08 12:32:37](https://github.com/leanprover-community/mathlib/commit/7058fa6)
feat(linear_algebra/{bilinear,quadratic}_form): inherit scalar actions from algebras ([#6586](https://github.com/leanprover-community/mathlib/pull/6586))
For example, this means a quadratic form over the quaternions inherits an `ℝ` action.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.smul_apply

Modified src/linear_algebra/quadratic_form.lean
- \+/\- *lemma* quadratic_form.coe_fn_smul
- \+/\- *lemma* quadratic_form.smul_apply



## [2021-03-08 12:32:35](https://github.com/leanprover-community/mathlib/commit/5d0a40f)
feat(algebra/algebra/{basic,tower}): add alg_equiv.comap and alg_equiv.restrict_scalars ([#6548](https://github.com/leanprover-community/mathlib/pull/6548))
This also renames `is_scalar_tower.restrict_base` to `alg_hom.restrict_scalars`, to enable dot notation and match `linear_map.restrict_scalars`.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.comap
- \+/\- *def* alg_hom.comap

Modified src/algebra/algebra/tower.lean
- \+ *lemma* alg_equiv.coe_restrict_scalars'
- \+ *lemma* alg_equiv.coe_restrict_scalars
- \+ *def* alg_equiv.restrict_scalars
- \+ *lemma* alg_equiv.restrict_scalars_apply
- \+ *lemma* alg_hom.coe_restrict_scalars'
- \+ *lemma* alg_hom.coe_restrict_scalars
- \+ *def* alg_hom.restrict_scalars
- \+ *lemma* alg_hom.restrict_scalars_apply
- \- *lemma* is_scalar_tower.coe_restrict_base'
- \- *lemma* is_scalar_tower.coe_restrict_base
- \- *def* is_scalar_tower.restrict_base
- \- *lemma* is_scalar_tower.restrict_base_apply

Modified src/field_theory/normal.lean


Modified src/ring_theory/algebra_tower.lean




## [2021-03-08 11:35:06](https://github.com/leanprover-community/mathlib/commit/b6ed62c)
feat(algebraic_topology): simplicial objects and simplicial types ([#6195](https://github.com/leanprover-community/mathlib/pull/6195))
#### Estimated changes
Added src/algebraic_topology/simplicial_object.lean
- \+ *def* category_theory.simplicial_object.eq_to_iso
- \+ *lemma* category_theory.simplicial_object.eq_to_iso_refl
- \+ *def* category_theory.simplicial_object.δ
- \+ *lemma* category_theory.simplicial_object.δ_comp_δ
- \+ *lemma* category_theory.simplicial_object.δ_comp_δ_self
- \+ *lemma* category_theory.simplicial_object.δ_comp_σ_of_gt
- \+ *lemma* category_theory.simplicial_object.δ_comp_σ_of_le
- \+ *lemma* category_theory.simplicial_object.δ_comp_σ_self
- \+ *lemma* category_theory.simplicial_object.δ_comp_σ_succ
- \+ *def* category_theory.simplicial_object.σ
- \+ *lemma* category_theory.simplicial_object.σ_comp_σ
- \+ *def* category_theory.simplicial_object

Added src/algebraic_topology/simplicial_set.lean
- \+ *def* sSet.as_preorder_hom
- \+ *def* sSet.boundary
- \+ *def* sSet.boundary_inclusion
- \+ *def* sSet.horn
- \+ *def* sSet.horn_inclusion
- \+ *def* sSet.standard_simplex
- \+ *def* sSet



## [2021-03-08 10:21:12](https://github.com/leanprover-community/mathlib/commit/f3dbe9f)
feat(bounded_continuous_function): coe_sum ([#6522](https://github.com/leanprover-community/mathlib/pull/6522))
#### Estimated changes
Modified src/topology/bounded_continuous_function.lean
- \+ *def* bounded_continuous_function.coe_fn_add_hom
- \+ *lemma* bounded_continuous_function.coe_sum
- \+/\- *lemma* bounded_continuous_function.coe_zero
- \+ *lemma* bounded_continuous_function.sum_apply



## [2021-03-08 02:11:14](https://github.com/leanprover-community/mathlib/commit/98c6bbc)
feat(data/set/function): three lemmas about maps_to ([#6518](https://github.com/leanprover-community/mathlib/pull/6518))
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* set.maps_image_to
- \+ *lemma* set.maps_range_to
- \+ *lemma* set.maps_univ_to



## [2021-03-08 01:18:53](https://github.com/leanprover-community/mathlib/commit/5b61f07)
chore(scripts): update nolints.txt ([#6582](https://github.com/leanprover-community/mathlib/pull/6582))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-07 22:03:50](https://github.com/leanprover-community/mathlib/commit/2d3c522)
feat(order/ideal): added proper ideal typeclass and lemmas to order_top ([#6566](https://github.com/leanprover-community/mathlib/pull/6566))
Defined `proper` and proved basic lemmas about proper ideals.
Also turned `order_top` into a section.
#### Estimated changes
Modified src/order/ideal.lean
- \+ *lemma* order.ideal.proper_of_ne_top
- \+ *lemma* order.ideal.proper_of_not_mem
- \+ *lemma* order.ideal.top_carrier
- \+ *lemma* order.ideal.top_of_mem_top



## [2021-03-07 21:14:26](https://github.com/leanprover-community/mathlib/commit/79be90a)
feat(algebra/regular): add lemmas about regularity of non-zero elements ([#6579](https://github.com/leanprover-community/mathlib/pull/6579))
More API, to deal with cases in which a regular element is non-zero.
#### Estimated changes
Modified src/algebra/regular.lean
- \+ *lemma* is_left_regular.ne_zero
- \+ *lemma* is_regular.ne_zero
- \+ *lemma* is_regular_iff_ne_zero
- \+ *lemma* is_right_regular.ne_zero



## [2021-03-07 17:19:18](https://github.com/leanprover-community/mathlib/commit/b25994d)
feat(number_theory/bernoulli): definition and properties of Bernoulli polynomials ([#6309](https://github.com/leanprover-community/mathlib/pull/6309))
The Bernoulli polynomials and its properties are defined.
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean


Modified src/data/finset/basic.lean
- \+ *lemma* finset.mem_range_le
- \+ *lemma* finset.mem_range_sub_ne_zero

Added src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* bernoulli_poly.bernoulli_poly_eval_zero
- \+ *lemma* bernoulli_poly.bernoulli_poly_zero
- \+ *theorem* bernoulli_poly.exp_bernoulli_poly'
- \+ *theorem* bernoulli_poly.sum_bernoulli_poly
- \+ *def* bernoulli_poly
- \+ *lemma* bernoulli_poly_def



## [2021-03-07 14:37:15](https://github.com/leanprover-community/mathlib/commit/d9370e0)
fead(data/support): add `support_smul` ([#6569](https://github.com/leanprover-community/mathlib/pull/6569))
* add `smul_ne_zero`;
* rename `support_smul_subset` to `support_smul_subset_right`;
* add `support_smul_subset_left` and `support_smul`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *theorem* smul_ne_zero

Modified src/data/support.lean
- \+ *lemma* function.support_smul
- \- *lemma* function.support_smul_subset
- \+ *lemma* function.support_smul_subset_left
- \+ *lemma* function.support_smul_subset_right

Modified src/ring_theory/hahn_series.lean




## [2021-03-07 10:18:36](https://github.com/leanprover-community/mathlib/commit/02251b1)
refactor(geometry/manifold): drop some unused arguments ([#6545](https://github.com/leanprover-community/mathlib/pull/6545))
API changes:
* add lemmas about `map (ext_chart_at I x) (𝓝[s] x')`;
* prove `times_cont_mdiff_within_at.comp` directly without using other charts; the new proof does not need a `smooth_manifold_with_corners` instance;
* add aliases `times_cont_mdiff.times_cont_diff` etc;
* `times_cont_mdiff_map` no longer needs a `smooth_manifold_with_corners` instance;
* `has_smooth_mul` no longer extends `smooth_manifold_with_corners` and no longer takes `has_continuous_mul` as an argument;
* `has_smooth_mul_core` is gone in favor of `has_continuous_mul_of_smooth`;
* `smooth_monoid_morphism` now works with any model space (needed, e.g., to define `smooth_monoid_morphism.prod`);
* `lie_group_morphism` is gone: we use `M →* N` both for monoids and groups, no reason to have two structures in this case;
* `lie_group` no longer extends `smooth_manifold_with_corners` and no longer takes `topological_group` as an argument;
* `lie_group_core` is gone in favor of `topological_group_of_lie_group`;
* the `I : model_with_corners 𝕜 E H` argument of `smooth_mul` and `smooth_inv` is now explicit.
#### Estimated changes
Modified src/geometry/manifold/algebra/lie_group.lean
- \- *structure* lie_add_group_core
- \- *structure* lie_add_group_morphism
- \- *structure* lie_group_core
- \- *structure* lie_group_morphism
- \- *lemma* smooth_pow
- \+ *lemma* topological_group_of_lie_group

Modified src/geometry/manifold/algebra/monoid.lean
- \+ *lemma* has_continuous_mul_of_smooth
- \- *structure* has_smooth_add_core
- \- *structure* has_smooth_mul_core
- \+/\- *structure* smooth_add_monoid_morphism
- \+/\- *structure* smooth_monoid_morphism
- \+ *lemma* smooth_pow

Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/algebra/structures.lean
- \+ *lemma* topological_ring_of_smooth
- \+ *lemma* topological_semiring_of_smooth

Modified src/geometry/manifold/diffeomorph.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* ext_chart_at_map_nhds_within'
- \+ *lemma* ext_chart_at_map_nhds_within
- \+ *lemma* ext_chart_at_map_nhds_within_eq_image'
- \+ *lemma* ext_chart_at_map_nhds_within_eq_image
- \+ *lemma* ext_chart_at_source_mem_nhds_within'
- \+ *lemma* ext_chart_at_source_mem_nhds_within
- \+ *lemma* ext_chart_at_symm_map_nhds_within'
- \+ *lemma* ext_chart_at_symm_map_nhds_within
- \+ *lemma* ext_chart_at_symm_map_nhds_within_range'
- \+ *lemma* ext_chart_at_symm_map_nhds_within_range
- \+ *lemma* ext_chart_at_target_mem_nhds_within'
- \+ *lemma* nhds_within_ext_chart_target_eq'

Modified src/geometry/manifold/times_cont_mdiff.lean
- \- *lemma* times_cont_diff.times_cont_mdiff
- \- *lemma* times_cont_diff_at.times_cont_mdiff_at
- \- *lemma* times_cont_diff_on.times_cont_mdiff_on
- \- *lemma* times_cont_diff_within_at.times_cont_mdiff_within_at
- \+ *lemma* times_cont_mdiff_within_at_iff''

Modified src/geometry/manifold/times_cont_mdiff_map.lean




## [2021-03-07 04:25:18](https://github.com/leanprover-community/mathlib/commit/ebe2c61)
feat(analysis/normed_space/multilinear): a few more bundled (bi)linear maps ([#6546](https://github.com/leanprover-community/mathlib/pull/6546))
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+ *def* continuous_linear_map.comp_continuous_multilinear_mapL
- \+ *def* continuous_linear_map.flip_multilinear
- \+/\- *lemma* continuous_linear_map.norm_comp_continuous_multilinear_map_le
- \+ *def* continuous_multilinear_map.comp_continuous_linear_mapL
- \+ *lemma* continuous_multilinear_map.comp_continuous_linear_mapL_apply
- \+ *lemma* continuous_multilinear_map.norm_comp_continuous_linear_le
- \+ *lemma* continuous_multilinear_map.norm_comp_continuous_linear_mapL_le
- \+/\- *lemma* continuous_multilinear_map.norm_mk_pi_algebra_fin
- \+ *lemma* continuous_multilinear_map.op_norm_prod
- \+ *def* continuous_multilinear_map.prodL



## [2021-03-07 03:26:19](https://github.com/leanprover-community/mathlib/commit/9f17db5)
feat(analysis/special_functions/integrals): mul/div by a const ([#6357](https://github.com/leanprover-community/mathlib/pull/6357))
This PR, together with [#6216](https://github.com/leanprover-community/mathlib/pull/6216), makes the following possible:
```
import analysis.special_functions.integrals
open real interval_integral
open_locale real
example : ∫ x in 0..π, 2 * sin x = 4 := by norm_num
example : ∫ x:ℝ in 4..5, x * 2 = 9 := by norm_num
example : ∫ x in 0..π/2, cos x / 2 = 1 / 2 := by simp
```
#### Estimated changes
Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integral.integral_const_mul
- \+ *lemma* interval_integral.integral_div
- \+ *lemma* interval_integral.integral_mul_const



## [2021-03-07 01:15:46](https://github.com/leanprover-community/mathlib/commit/07fc982)
chore(scripts): update nolints.txt ([#6567](https://github.com/leanprover-community/mathlib/pull/6567))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-06 21:16:19](https://github.com/leanprover-community/mathlib/commit/df1e6f9)
refactor(data/{finset,multiset}): move inductions proofs on sum/prod from finset to multiset, add more induction lemmas ([#6561](https://github.com/leanprover-community/mathlib/pull/6561))
The starting point is `finset.le_sum_of_subadditive`, which is extended in several ways:
* It is written in multiplicative form, and a `[to_additive]` attribute generates the additive version,
* It is proven for multiset, which is then used for the proof of the finset case.
* For multiset, some lemmas are written for foldr/foldl (and prod is a foldr).
* Versions of these lemmas specialized to nonempty sets are provided. These don't need the initial hypothesis `f 1 = 1`/`f 0 = 0`.
* The new `..._on_pred` lemmas like `finset.le_sum_of_subadditive_on_pred` apply to functions that are only sub-additive for arguments that verify some property. I included an application of this with `snorm_sum_le`, which uses that the Lp seminorm is subadditive on a.e.-measurable functions. Those `on_pred` lemmas could be avoided by constructing the submonoid given by the predicate, then using the standard subadditive result, but I find convenient to be able to use them directly.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_induction_nonempty

Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.le_prod_nonempty_of_submultiplicative
- \+ *lemma* finset.le_prod_nonempty_of_submultiplicative_on_pred
- \+ *lemma* finset.le_prod_of_submultiplicative
- \+ *lemma* finset.le_prod_of_submultiplicative_on_pred
- \- *lemma* finset.le_sum_of_subadditive

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.foldl_induction'
- \+ *lemma* multiset.foldl_induction
- \+ *lemma* multiset.foldr_induction'
- \+ *lemma* multiset.foldr_induction
- \+ *lemma* multiset.le_prod_nonempty_of_submultiplicative
- \+ *lemma* multiset.le_prod_nonempty_of_submultiplicative_on_pred
- \+ *lemma* multiset.le_prod_of_submultiplicative
- \+ *lemma* multiset.le_prod_of_submultiplicative_on_pred
- \- *lemma* multiset.le_sum_of_subadditive
- \+ *lemma* multiset.prod_induction
- \+ *lemma* multiset.prod_induction_nonempty

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/lp_space.lean
- \+ *lemma* measure_theory.snorm'_sum_le
- \+ *lemma* measure_theory.snorm_sum_le



## [2021-03-06 21:16:18](https://github.com/leanprover-community/mathlib/commit/b280b00)
feat(data/set/basic): add `set.set_ite` ([#6557](https://github.com/leanprover-community/mathlib/pull/6557))
I'm going to use it as `source` and `target` in
`local_equiv.piecewise` and `local_homeomorph.piecewise`. There are
many non-defeq ways to define this set and I think that it's better to
have a name than to ensure that we always use the same formula.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.diff_univ
- \+ *lemma* set.inter_subset_ite
- \+ *lemma* set.ite_compl
- \+ *lemma* set.ite_diff_self
- \+ *lemma* set.ite_empty
- \+ *lemma* set.ite_inter
- \+ *lemma* set.ite_inter_compl_self
- \+ *lemma* set.ite_inter_inter
- \+ *lemma* set.ite_inter_self
- \+ *lemma* set.ite_mono
- \+ *lemma* set.ite_same
- \+ *lemma* set.ite_subset_union
- \+ *lemma* set.ite_univ

Modified src/topology/continuous_on.lean
- \+ *lemma* is_open.ite'
- \+ *lemma* is_open.ite
- \- *lemma* is_open_inter_union_inter_compl'
- \- *lemma* is_open_inter_union_inter_compl



## [2021-03-06 19:15:21](https://github.com/leanprover-community/mathlib/commit/ac8a119)
chore(geometry/manifold): use `namespace`, rename `image` to `image_eq` ([#6517](https://github.com/leanprover-community/mathlib/pull/6517))
* use `namespace` command in
  `geometry/manifold/smooth_manifold_with_corners`;
* rename `model_with_corners.image` to `model_with_corners.image_eq`
  to match `source_eq` etc;
* replace `homeomorph.coe_eq_to_equiv` with
  `@[simp] lemma coe_to_equiv`;
* add `continuous_linear_map.symm_image_image` and
  `continuous_linear_map.image_symm_image`;
* add `unique_diff_on.image`,
  `continuous_linear_equiv.unique_diff_on_image_iff`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* continuous_linear_equiv.unique_diff_on_image
- \+ *lemma* continuous_linear_equiv.unique_diff_on_image_iff
- \+/\- *lemma* continuous_linear_equiv.unique_diff_on_preimage_iff
- \+ *lemma* unique_diff_on.image

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* model_with_corners.closed_range
- \+/\- *lemma* model_with_corners.continuous_symm
- \- *lemma* model_with_corners.image
- \+/\- *lemma* model_with_corners.image_mem_nhds_within
- \- *lemma* model_with_corners.left_inv
- \- *lemma* model_with_corners.locally_compact
- \+/\- *lemma* model_with_corners.map_nhds_eq
- \+/\- *lemma* model_with_corners.mk_coe
- \- *lemma* model_with_corners.mk_coe_symm
- \+ *lemma* model_with_corners.mk_symm
- \- *lemma* model_with_corners.right_inv
- \+/\- *lemma* model_with_corners.symm_comp_self
- \+/\- *lemma* model_with_corners.symm_map_nhds_within_range
- \+/\- *lemma* model_with_corners.target_eq
- \+/\- *lemma* model_with_corners.to_local_equiv_coe
- \+/\- *lemma* model_with_corners.to_local_equiv_coe_symm
- \- *lemma* model_with_corners.unique_diff
- \+/\- *lemma* model_with_corners.unique_diff_at_image
- \+/\- *lemma* model_with_corners.unique_diff_preimage
- \+/\- *lemma* model_with_corners.unique_diff_preimage_source

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_equiv.image_symm_image
- \+ *theorem* continuous_linear_equiv.symm_image_image

Modified src/topology/homeomorph.lean
- \- *lemma* homeomorph.coe_eq_to_equiv
- \+ *lemma* homeomorph.coe_to_equiv



## [2021-03-06 17:06:17](https://github.com/leanprover-community/mathlib/commit/16ef291)
feat(order/filter/*, topology/subset_properties): define "coproduct" of two filters ([#6372](https://github.com/leanprover-community/mathlib/pull/6372))
Define the "coproduct" of two filters (unclear if this is really a categorical coproduct) as
```lean
protected def coprod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊔ g.comap prod.snd
```
and prove the three lemmas which motivated this construction ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Filter.20golf)):  coproduct of cofinite filters is the cofinite filter, coproduct of cocompact filters is the cocompact filter, and
```lean
(tendsto f a c) → (tendsto g b d) → (tendsto (prod.map f g) (a.coprod b) (c.coprod d))
```
Co-authored by: Kevin Buzzard <k.buzzard@imperial.ac.uk>
Co-authored by: Patrick Massot <patrickmassot@free.fr>
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.coprod_mono
- \+ *lemma* filter.map_const_principal_coprod_map_id_principal
- \+ *lemma* filter.map_prod_map_const_id_principal_coprod_principal
- \+ *lemma* filter.map_prod_map_coprod_le
- \+ *lemma* filter.mem_coprod_iff
- \+ *lemma* filter.principal_coprod_principal
- \+ *lemma* filter.tendsto.prod_map_coprod

Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.coprod_cofinite

Modified src/topology/subset_properties.lean
- \+ *lemma* filter.coprod_cocompact



## [2021-03-06 11:31:49](https://github.com/leanprover-community/mathlib/commit/0fa0d61)
feat(topology/paracompact): define paracompact spaces ([#6395](https://github.com/leanprover-community/mathlib/pull/6395))
Fixes [#6391](https://github.com/leanprover-community/mathlib/pull/6391)
#### Estimated changes
Modified docs/references.bib


Modified roadmap/topology/paracompact.lean
- \- *lemma* normal_of_paracompact_t2
- \- *lemma* paracompact_of_compact
- \- *lemma* paracompact_of_metric
- \- *lemma* paracompact_space.precise_refinement
- \+ *lemma* roadmap.normal_of_paracompact_t2
- \+ *lemma* roadmap.paracompact_of_compact
- \+ *lemma* roadmap.paracompact_of_metric
- \+ *lemma* roadmap.paracompact_space.precise_refinement

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.exists_inv_two_pow_lt
- \+ *lemma* ennreal.inv_le_one
- \+ *lemma* ennreal.one_le_inv
- \+ *lemma* ennreal.pow_le_pow_of_le_one

Modified src/order/filter/bases.lean


Modified src/topology/basic.lean
- \+ *lemma* closure_inter_open'
- \+ *lemma* closure_nonempty_iff
- \- *lemma* is_closed_Union_of_locally_finite
- \+ *lemma* locally_finite.closure
- \+ *lemma* locally_finite.closure_Union
- \+ *lemma* locally_finite.comp_injective
- \+ *lemma* locally_finite.is_closed_Union
- \+ *lemma* locally_finite.subset
- \- *lemma* locally_finite_subset
- \- *lemma* set.nonempty.closure

Modified src/topology/constructions.lean


Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* uniformity_basis_edist_inv_two_pow

Added src/topology/paracompact.lean
- \+ *lemma* normal_of_paracompact_t2
- \+ *lemma* precise_refinement
- \+ *lemma* precise_refinement_set
- \+ *theorem* refinement_of_locally_compact_sigma_compact_of_nhds_basis

Modified src/topology/separation.lean
- \+ *lemma* compact_exhaustion.is_closed

Modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.elim_nhds_subcover'
- \+ *lemma* is_compact.elim_nhds_subcover



## [2021-03-06 07:42:55](https://github.com/leanprover-community/mathlib/commit/126cebc)
feat(data/real/nnreal): ℝ is an ℝ≥0-algebra ([#6560](https://github.com/leanprover-community/mathlib/pull/6560))
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/rings.20from.20subtype
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2021-03-06 07:42:54](https://github.com/leanprover-community/mathlib/commit/a05b35c)
doc(*): wrap raw URLs containing parentheses with angle brackets ([#6554](https://github.com/leanprover-community/mathlib/pull/6554))
Raw URLs with parentheses in them are tricky for `doc-gen` to parse, so this commit wraps them in angle brackets.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/measure_theory/content.lean


Modified src/order/ideal.lean


Modified src/order/pfilter.lean




## [2021-03-06 07:42:53](https://github.com/leanprover-community/mathlib/commit/3e5643e)
feat(category_theory/opposites): use simps everywhere ([#6553](https://github.com/leanprover-community/mathlib/pull/6553))
This is possible after leanprover-community/lean[#538](https://github.com/leanprover-community/mathlib/pull/538)
#### Estimated changes
Modified src/category_theory/opposites.lean
- \- *lemma* category_theory.iso.op_hom
- \- *lemma* category_theory.iso.op_inv
- \- *lemma* category_theory.nat_iso.op_hom
- \- *lemma* category_theory.nat_iso.op_inv
- \- *lemma* category_theory.nat_iso.remove_op_hom
- \- *lemma* category_theory.nat_iso.remove_op_inv
- \- *lemma* category_theory.nat_iso.unop_hom
- \- *lemma* category_theory.nat_iso.unop_inv
- \- *lemma* category_theory.nat_trans.left_op_app
- \- *lemma* category_theory.nat_trans.remove_left_op_app
- \+/\- *def* category_theory.op_equiv
- \- *lemma* category_theory.op_equiv_apply
- \- *lemma* category_theory.op_equiv_symm_apply



## [2021-03-06 07:42:52](https://github.com/leanprover-community/mathlib/commit/5962c76)
feat(algebra/ring/boolean_ring): Boolean rings ([#6464](https://github.com/leanprover-community/mathlib/pull/6464))
`boolean_ring.to_boolean_algebra` is the Boolean algebra structure on a Boolean ring.
#### Estimated changes
Added src/algebra/ring/boolean_ring.lean
- \+ *lemma* add_eq_zero
- \+ *lemma* add_self
- \+ *def* boolean_ring.has_inf
- \+ *def* boolean_ring.has_sup
- \+ *lemma* boolean_ring.inf_assoc
- \+ *lemma* boolean_ring.inf_comm
- \+ *lemma* boolean_ring.inf_sup_self
- \+ *lemma* boolean_ring.le_sup_inf
- \+ *lemma* boolean_ring.le_sup_inf_aux
- \+ *lemma* boolean_ring.sup_assoc
- \+ *lemma* boolean_ring.sup_comm
- \+ *lemma* boolean_ring.sup_inf_self
- \+ *def* boolean_ring.to_boolean_algebra
- \+ *lemma* mul_add_mul
- \+ *lemma* mul_self
- \+ *lemma* neg_eq
- \+ *lemma* sub_eq_add



## [2021-03-06 02:14:45](https://github.com/leanprover-community/mathlib/commit/32547fc)
chore(scripts): update nolints.txt ([#6558](https://github.com/leanprover-community/mathlib/pull/6558))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-06 01:08:46](https://github.com/leanprover-community/mathlib/commit/4428243)
chore(polynomial/chebyshev): changes names of chebyshev₁ to chebyshev.T and chebyshev₂ to chebyshev.U ([#6519](https://github.com/leanprover-community/mathlib/pull/6519))
Still have to write here what was changed (will be a long list). More or less this is just search and replace `chebyshev₁` for `chebyshev.T` and `chebyshev₂` for `chebyshev.U`.
* `polynomial.chebyshev₁` is now `polynomial.chebyshev.T`
* `polynomial.chebyshev₁_zero` is now `polynomial.chebyshev.T_zero`
* `polynomial.chebyshev₁_one` is now `polynomial.chebyshev.T_one`
* `polynomial.chebyshev₁_two` is now `polynomial.chebyshev.T_two`
* `polynomial.chebyshev₁_add_two` is now `polynomial.chebyshev.T_add_two`
* `polynomial.chebyshev₁_of_two_le` is now `polynomial.chebyshev.T_of_two_le`
* `polynomial.map_chebyshev₁` is now `polynomial.chebyshev.map_T`
* `polynomial.chebyshev₂` is now `polynomial.chebyshev.U`
* `polynomial.chebyshev₂_zero` is now `polynomial.chebyshev.U_zero`
* `polynomial.chebyshev₂_one` is now `polynomial.chebyshev.U_one`
* `polynomial.chebyshev₂_two` is now `polynomial.chebyshev.U_two`
* `polynomial.chebyshev₂_add_two` is now `polynomial.chebyshev.U_add_two`
* `polynomial.chebyshev₂_of_two_le` is now `polynomial.chebyshev.U_of_two_le`
* `polynomial.chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁` is now `polynomial.chebyshev.U_eq_X_mul_U_add_T`
* `polynomial.chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂` is now `polynomial.chebyshev.T_eq_U_sub_X_mul_U`
* `polynomial.chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂` is now `polynomial.chebyshev.T_eq_X_mul_T_sub_pol_U`
* `polynomial.one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁` is now `polynomial.chebyshev.one_sub_X_pow_two_mul_U_eq_pol_in_T`
* `polynomial.map_chebyshev₂` is now `polynomial.chebyshev.map_U`
* `polynomial.chebyshev₁_derivative_eq_chebyshev₂` is now `polynomial.chebyshev.T_derivative_eq_U`
* `polynomial.one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁` is now `polynomial.chebyshev.one_sub_X_pow_two_mul_derivative_T_eq_poly_in_T`
* `polynomial.add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂` is now `polynomial.chebyshev.add_one_mul_T_eq_poly_in_U`
* `polynomial.mul_chebyshev₁` is now `polynomial.chebyshev.mul_T`
* `polynomial.chebyshev₁_mul` is now `polynomial.chebyshev.T_mul`
* `polynomial.dickson_one_one_eq_chebyshev₁` is now `polynomial.dickson_one_one_eq_chebyshev_T`
* `polynomial.chebyshev₁_eq_dickson_one_one` is now `polynomial.chebyshev_T_eq_dickson_one_one`
* `chebyshev₁_complex_cos` is now `polynomial.chebyshev.T_complex_cos`
* `cos_nat_mul` is now `polynomial.chebyshev.cos_nat_mul`
* `chebyshev₂_complex_cos` is now `polynomial.chebyshev.U_complex_cos`
* `sin_nat_succ_mul` is now `polynomial.chebyshev.sin_nat_succ_mul`
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \- *lemma* chebyshev₁_complex_cos
- \- *lemma* chebyshev₂_complex_cos
- \- *lemma* cos_nat_mul
- \+ *lemma* polynomial.chebyshev.T_complex_cos
- \+ *lemma* polynomial.chebyshev.U_complex_cos
- \+ *lemma* polynomial.chebyshev.cos_nat_mul
- \+ *lemma* polynomial.chebyshev.sin_nat_succ_mul
- \- *lemma* sin_nat_succ_mul

Modified src/ring_theory/polynomial/chebyshev.lean
- \- *lemma* polynomial.add_one_mul_chebyshev₁_eq_poly_in_chebyshev₂
- \+ *lemma* polynomial.chebyshev.T_add_two
- \+ *lemma* polynomial.chebyshev.T_derivative_eq_U
- \+ *lemma* polynomial.chebyshev.T_eq_U_sub_X_mul_U
- \+ *lemma* polynomial.chebyshev.T_eq_X_mul_T_sub_pol_U
- \+ *lemma* polynomial.chebyshev.T_mul
- \+ *lemma* polynomial.chebyshev.T_of_two_le
- \+ *lemma* polynomial.chebyshev.T_one
- \+ *lemma* polynomial.chebyshev.T_two
- \+ *lemma* polynomial.chebyshev.T_zero
- \+ *lemma* polynomial.chebyshev.U_add_two
- \+ *lemma* polynomial.chebyshev.U_eq_X_mul_U_add_T
- \+ *lemma* polynomial.chebyshev.U_of_two_le
- \+ *lemma* polynomial.chebyshev.U_one
- \+ *lemma* polynomial.chebyshev.U_two
- \+ *lemma* polynomial.chebyshev.U_zero
- \+ *lemma* polynomial.chebyshev.add_one_mul_T_eq_poly_in_U
- \+ *lemma* polynomial.chebyshev.map_T
- \+ *lemma* polynomial.chebyshev.map_U
- \+ *lemma* polynomial.chebyshev.mul_T
- \+ *lemma* polynomial.chebyshev.one_sub_X_pow_two_mul_U_eq_pol_in_T
- \+ *lemma* polynomial.chebyshev.one_sub_X_pow_two_mul_derivative_T_eq_poly_in_T
- \- *lemma* polynomial.chebyshev₁_add_two
- \- *lemma* polynomial.chebyshev₁_derivative_eq_chebyshev₂
- \- *lemma* polynomial.chebyshev₁_eq_X_mul_chebyshev₁_sub_pol_chebyshev₂
- \- *lemma* polynomial.chebyshev₁_eq_chebyshev₂_sub_X_mul_chebyshev₂
- \- *lemma* polynomial.chebyshev₁_mul
- \- *lemma* polynomial.chebyshev₁_of_two_le
- \- *lemma* polynomial.chebyshev₁_one
- \- *lemma* polynomial.chebyshev₁_two
- \- *lemma* polynomial.chebyshev₁_zero
- \- *lemma* polynomial.chebyshev₂_add_two
- \- *lemma* polynomial.chebyshev₂_eq_X_mul_chebyshev₂_add_chebyshev₁
- \- *lemma* polynomial.chebyshev₂_of_two_le
- \- *lemma* polynomial.chebyshev₂_one
- \- *lemma* polynomial.chebyshev₂_two
- \- *lemma* polynomial.chebyshev₂_zero
- \- *lemma* polynomial.map_chebyshev₁
- \- *lemma* polynomial.map_chebyshev₂
- \- *lemma* polynomial.mul_chebyshev₁
- \- *lemma* polynomial.one_sub_X_pow_two_mul_chebyshev₂_eq_pol_in_chebyshev₁
- \- *lemma* polynomial.one_sub_X_pow_two_mul_derivative_chebyshev₁_eq_poly_in_chebyshev₁

Modified src/ring_theory/polynomial/dickson.lean
- \+ *lemma* polynomial.chebyshev_T_eq_dickson_one_one
- \- *lemma* polynomial.chebyshev₁_eq_dickson_one_one
- \+ *lemma* polynomial.dickson_one_one_eq_chebyshev_T
- \- *lemma* polynomial.dickson_one_one_eq_chebyshev₁



## [2021-03-05 21:45:36](https://github.com/leanprover-community/mathlib/commit/4bc6707)
feat(topology/local_homeomorph): preimage of `closure` and `frontier` ([#6547](https://github.com/leanprover-community/mathlib/pull/6547))
#### Estimated changes
Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.image_inter_source_eq'
- \+ *lemma* local_homeomorph.map_nhds_within_eq
- \+ *lemma* local_homeomorph.preimage_closure
- \+ *lemma* local_homeomorph.preimage_frontier



## [2021-03-05 21:45:35](https://github.com/leanprover-community/mathlib/commit/cbcbe24)
feat(algebra/ordered_monoid): linear_ordered_add_comm_monoid(_with_top) ([#6520](https://github.com/leanprover-community/mathlib/pull/6520))
Separates out classes for `linear_ordered_(add_)comm_monoid`
Creates `linear_ordered_add_comm_monoid_with_top`, an additive and order-reversed version of `linear_ordered_comm_monoid_with_zero`.
Puts an instance of `linear_ordered_add_comm_monoid_with_top` on `with_top` of any `linear_ordered_add_comm_monoid` and also on `enat`
#### Estimated changes
Modified src/algebra/group/type_tags.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/module/submodule.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_monoid.lean
- \+ *lemma* add_top
- \+ *def* function.injective.linear_ordered_comm_monoid
- \+ *lemma* top_add

Modified src/data/nat/enat.lean


Modified src/group_theory/submonoid/operations.lean




## [2021-03-05 20:52:35](https://github.com/leanprover-community/mathlib/commit/626cb42)
feat(data/polynomial/mirror): new file ([#6426](https://github.com/leanprover-community/mathlib/pull/6426))
This files defines an alternate version of `polynomial.reverse`. This version is often nicer to work with since it preserves `nat_degree` and `nat_trailing_degree` and is always an involution.
(this PR is part of the irreducibility saga)
#### Estimated changes
Added src/data/polynomial/mirror.lean
- \+ *lemma* polynomial.coeff_mirror
- \+ *lemma* polynomial.irreducible_of_mirror
- \+ *lemma* polynomial.mirror_C
- \+ *lemma* polynomial.mirror_X
- \+ *lemma* polynomial.mirror_eq_zero
- \+ *lemma* polynomial.mirror_eval_one
- \+ *lemma* polynomial.mirror_leading_coeff
- \+ *lemma* polynomial.mirror_mirror
- \+ *lemma* polynomial.mirror_monomial
- \+ *lemma* polynomial.mirror_mul_of_domain
- \+ *lemma* polynomial.mirror_nat_degree
- \+ *lemma* polynomial.mirror_nat_trailing_degree
- \+ *lemma* polynomial.mirror_neg
- \+ *lemma* polynomial.mirror_smul
- \+ *lemma* polynomial.mirror_trailing_coeff
- \+ *lemma* polynomial.mirror_zero



## [2021-03-05 16:16:24](https://github.com/leanprover-community/mathlib/commit/913950e)
feat(group_theory/subgroup): add monoid_hom.restrict ([#6537](https://github.com/leanprover-community/mathlib/pull/6537))
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *def* monoid_hom.restrict
- \+ *lemma* monoid_hom.restrict_apply



## [2021-03-05 15:05:25](https://github.com/leanprover-community/mathlib/commit/d40487b)
feat(measure_theory/[set_integral, interval_integral]): mono and nonneg lemmas ([#6292](https://github.com/leanprover-community/mathlib/pull/6292))
See https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60integral_restrict.60/near/226274072
#### Estimated changes
Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_mono

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_mono
- \+ *lemma* interval_integral.integral_mono_ae
- \+ *lemma* interval_integral.integral_mono_ae_restrict
- \+ *lemma* interval_integral.integral_mono_on
- \+ *lemma* interval_integral.integral_nonneg
- \+ *lemma* interval_integral.integral_nonneg_of_ae
- \+ *lemma* interval_integral.integral_nonneg_of_ae_restrict

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_restrict_of_ae
- \+ *lemma* measure_theory.ae_restrict_of_ae_restrict_of_subset

Modified src/measure_theory/set_integral.lean
- \+ *lemma* measure_theory.set_integral_mono
- \+ *lemma* measure_theory.set_integral_mono_ae
- \+ *lemma* measure_theory.set_integral_mono_ae_restrict
- \+ *lemma* measure_theory.set_integral_mono_on
- \+ *lemma* measure_theory.set_integral_nonneg
- \+ *lemma* measure_theory.set_integral_nonneg_of_ae
- \+ *lemma* measure_theory.set_integral_nonneg_of_ae_restrict

Modified test/monotonicity.lean




## [2021-03-05 13:04:47](https://github.com/leanprover-community/mathlib/commit/97d13d7)
feat(algebra/lie/subalgebra): define the Lie subalgebra generated by a subset ([#6549](https://github.com/leanprover-community/mathlib/pull/6549))
The work here is a lightly-edited copy-paste of the corresponding results for Lie submodules
#### Estimated changes
Modified src/algebra/lie/abelian.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.coe_lie_span_submodule_eq_iff
- \+ *def* lie_subalgebra.lie_span
- \+ *lemma* lie_subalgebra.lie_span_eq
- \+ *lemma* lie_subalgebra.lie_span_le
- \+ *lemma* lie_subalgebra.lie_span_mono
- \+ *lemma* lie_subalgebra.mem_lie_span
- \+ *lemma* lie_subalgebra.submodule_span_le_lie_span
- \+ *lemma* lie_subalgebra.subset_lie_span
- \+ *lemma* submodule.exists_lie_subalgebra_coe_eq_iff



## [2021-03-05 11:27:59](https://github.com/leanprover-community/mathlib/commit/d90448c)
chore(linear_algebra/*): changes to finsupp_vectorspaces and move module doc dual ([#6516](https://github.com/leanprover-community/mathlib/pull/6516))
This PR does the following:
- move the module doc of `linear_algebra.dual` so that it is recognised by the linter.
- add `ker_eq_bot_iff_range_eq_top_of_findim_eq_findim` to `linear_algebra.finite_dimensional`, this replaces `injective_of_surjective` in `linear_algebra.finsupp_vectorspaces`
- remove `eq_bot_iff_dim_eq_zero` from `linear_algebra.finsupp_vectorspaces`, this already exists as `dim_eq_zero` in `linear_algebra.finite_dimensional`
- changed `cardinal_mk_eq_cardinal_mk_field_pow_dim` and `cardinal_lt_omega_of_dim_lt_omega` to assume `finite_dimensional K V` instead of `dim < omega`.
- renamed `cardinal_lt_omega_of_dim_lt_omega` to `cardinal_lt_omega_of_finite_dimensional` since the assumption changed.
- provided a module doc for `linear_algebra.finsupp_vectorspaces` which should remove `linear_algebra.*` from the style exceptions file.
This file should probably be looked at again by someone more experienced in the linear_algebra part of the library. It seems to me that most of the statements in this file in fact would better fit in other files.
#### Estimated changes
Modified src/field_theory/finite/polynomial.lean
- \+ *lemma* mv_polynomial.findim_R

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.findim_eq_of_dim_eq
- \+ *lemma* linear_map.ker_eq_bot_iff_range_eq_top_of_findim_eq_findim

Modified src/linear_algebra/finsupp_vector_space.lean
- \- *lemma* cardinal_lt_omega_of_dim_lt_omega
- \+ *lemma* cardinal_lt_omega_of_finite_dimensional
- \+/\- *lemma* cardinal_mk_eq_cardinal_mk_field_pow_dim
- \- *lemma* eq_bot_iff_dim_eq_zero
- \- *lemma* injective_of_surjective



## [2021-03-05 08:42:35](https://github.com/leanprover-community/mathlib/commit/c782e28)
chore(analysis/normed_space/units): add `protected`, minor review ([#6544](https://github.com/leanprover-community/mathlib/pull/6544))
#### Estimated changes
Modified src/analysis/normed_space/units.lean
- \- *lemma* units.is_open
- \- *lemma* units.nhds



## [2021-03-05 08:42:34](https://github.com/leanprover-community/mathlib/commit/f158f25)
feat(data/mv_polynomial/basic): add is_scalar_tower and smul_comm_class instances ([#6542](https://github.com/leanprover-community/mathlib/pull/6542))
This also fixes the `semimodule` instance to not require `comm_semiring R`
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean




## [2021-03-05 05:37:32](https://github.com/leanprover-community/mathlib/commit/340dd69)
fix(*): remove some simp lemmas ([#6541](https://github.com/leanprover-community/mathlib/pull/6541))
All of these simp lemmas are also declared in core. 
Maybe one of the copies can be removed in a future PR, but this PR is just to remove the duplicate simp attributes.
This is part of fixing linting problems in core, done in leanprover-community/lean[#545](https://github.com/leanprover-community/mathlib/pull/545). 
Most of the duplicate simp lemmas are fixed in `core`, but I prefer to remove the simp attribute here in mathlib if the simp lemmas were already used in core.
#### Estimated changes
Modified src/data/bool.lean
- \+/\- *theorem* bool.coe_sort_ff
- \+/\- *theorem* bool.coe_sort_tt
- \+/\- *theorem* bool.to_bool_false
- \+/\- *theorem* bool.to_bool_true

Modified src/data/list/basic.lean
- \+/\- *theorem* list.bind_append

Modified src/logic/basic.lean
- \+/\- *theorem* forall_true_iff



## [2021-03-05 04:34:20](https://github.com/leanprover-community/mathlib/commit/990a5bb)
chore(analysis/normed_space/extend): remove unnecessary imports ([#6538](https://github.com/leanprover-community/mathlib/pull/6538))
Remove two imports.  `import analysis.complex.basic` is actually unnecessary, `import analysis.normed_space.operator_norm` is indirectly imported via `data.complex.is_R_or_C`.
#### Estimated changes
Modified src/analysis/normed_space/extend.lean




## [2021-03-05 02:26:15](https://github.com/leanprover-community/mathlib/commit/10aaddd)
chore(scripts): update nolints.txt ([#6543](https://github.com/leanprover-community/mathlib/pull/6543))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-05 00:23:57](https://github.com/leanprover-community/mathlib/commit/d2cc044)
chore(algebra/algebra/basic): add a missing coe lemma ([#6535](https://github.com/leanprover-community/mathlib/pull/6535))
This is just to stop the terrible pain of having to work with `⇑(e.to_ring_equiv) x` in goals.
In the long run, we should sort out the simp normal form, but for now I just want to stop the pain.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.coe_ring_equiv'



## [2021-03-04 21:18:05](https://github.com/leanprover-community/mathlib/commit/ef1a00b)
feat(data/finsupp, algebra/monoid_algebra): add is_scalar_tower and smul_comm_class ([#6534](https://github.com/leanprover-community/mathlib/pull/6534))
This stops just short of transferring these instances to `polynomial` and `mv_polynomial`.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean


Modified src/data/finsupp/basic.lean




## [2021-03-04 21:18:04](https://github.com/leanprover-community/mathlib/commit/0dfba50)
feat(algebra/algebra/basic): alg_equiv.of_linear_equiv ([#6495](https://github.com/leanprover-community/mathlib/pull/6495))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.of_linear_equiv
- \+ *lemma* alg_equiv.of_linear_equiv_apply
- \+ *lemma* alg_equiv.of_linear_equiv_to_linear_equiv
- \+ *lemma* alg_equiv.to_linear_equiv_of_linear_equiv



## [2021-03-04 21:18:02](https://github.com/leanprover-community/mathlib/commit/744e79c)
feat(algebra/ordered_*, */sub{monoid,group,ring,semiring,field,algebra}): pullback of ordered algebraic structures under an injective map ([#6489](https://github.com/leanprover-community/mathlib/pull/6489))
Prove that the following 14 order typeclasses can be pulled back via an injective map (`function.injective.*`), and use them to attach 30 new instances to sub-objects:
* `ordered_comm_monoid` (and the implied `ordered_add_comm_monoid`)
  * `submonoid.to_ordered_comm_monoid`
  * `submodule.to_ordered_add_comm_monoid`
* `ordered_comm_group` (and the implied `ordered_add_comm_group`)
  * `subgroup.to_ordered_comm_group`
  * `submodule.to_ordered_add_comm_group`
* `ordered_cancel_comm_monoid` (and the implied `ordered_cancel_add_comm_monoid`)
  * `submonoid.to_ordered_cancel_comm_monoid`
  * `submodule.to_ordered_cancel_add_comm_monoid`
* `linear_ordered_cancel_comm_monoid` (and the implied `linear_ordered_cancel_add_comm_monoid`)
  * `submonoid.to_linear_ordered_cancel_comm_monoid`
  *  `submodule.to_linear_ordered_cancel_add_comm_monoid`
* `linear_ordered_comm_monoid_with_zero`
  * (no suitable subobject exists for monoid_with_zero)
* `linear_ordered_comm_group` (and the implied `linear_ordered_add_comm_group`)
  * `subgroup.to_linear_ordered_comm_group`
  * `submodule.to_linear_ordered_add_comm_group`
* `ordered_semiring`
  * `subsemiring.to_ordered_semiring`
  * `subalgebra.to_ordered_semiring`
* `ordered_comm_semiring`
  * `subsemiring.to_ordered_comm_semiring`
  * `subalgebra.to_ordered_comm_semiring`
* `ordered_ring`
  * `subring.to_ordered_ring`
  * `subalgebra.to_ordered_ring`
* `ordered_comm_ring`
  * `subring.to_ordered_comm_ring`
  * `subalgebra.to_ordered_comm_ring`
* `linear_ordered_semiring`
  * `subring.to_linear_ordered_semiring`
  * `subalgebra.to_linear_ordered_semiring`
* `linear_ordered_ring`
  * `subring.to_linear_ordered_ring`
  * `subalgebra.to_linear_ordered_ring`
* `linear_ordered_comm_ring`
  * `subring.to_linear_ordered_comm_ring`
  * `subalgebra.to_linear_ordered_comm_ring`
* `linear_ordered_field`
  * `subfield.to_linear_ordered_field`
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/rings.20from.20subtype
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *def* function.injective.linear_ordered_comm_monoid_with_zero

Modified src/algebra/module/submodule.lean


Modified src/algebra/ordered_field.lean
- \+ *def* function.injective.linear_ordered_field

Modified src/algebra/ordered_group.lean
- \+ *def* function.injective.linear_ordered_comm_group
- \+ *def* function.injective.ordered_comm_group

Modified src/algebra/ordered_monoid.lean
- \+ *def* function.injective.linear_ordered_cancel_comm_monoid
- \+ *def* function.injective.ordered_cancel_comm_monoid
- \+ *def* function.injective.ordered_comm_monoid

Modified src/algebra/ordered_ring.lean
- \+ *def* function.injective.linear_ordered_comm_ring
- \+ *def* function.injective.linear_ordered_ring
- \+ *def* function.injective.linear_ordered_semiring
- \+ *def* function.injective.ordered_comm_ring
- \+ *def* function.injective.ordered_comm_semiring
- \+ *def* function.injective.ordered_ring
- \+ *def* function.injective.ordered_semiring

Modified src/field_theory/subfield.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean




## [2021-03-04 21:18:00](https://github.com/leanprover-community/mathlib/commit/09273ae)
feat(measure_theory/probability_mass_function): Generalize bind on pmfs to binding on the support ([#6210](https://github.com/leanprover-community/mathlib/pull/6210))
#### Estimated changes
Modified src/measure_theory/probability_mass_function.lean
- \+ *def* pmf.bind_on_support
- \+ *lemma* pmf.bind_on_support_apply
- \+ *lemma* pmf.bind_on_support_bind_on_support
- \+ *lemma* pmf.bind_on_support_comm
- \+ *lemma* pmf.bind_on_support_eq_bind
- \+ *lemma* pmf.bind_on_support_eq_zero_iff
- \+ *lemma* pmf.bind_on_support_pure
- \+ *lemma* pmf.coe_bind_on_support_apply
- \+ *lemma* pmf.mem_support_bind_on_support_iff
- \+ *lemma* pmf.mem_support_pure_iff
- \+ *lemma* pmf.pure_bind_on_support

Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* tsum_congr
- \+ *lemma* tsum_dite_left
- \+ *lemma* tsum_dite_right
- \+ *lemma* tsum_ne_zero_iff



## [2021-03-04 17:49:12](https://github.com/leanprover-community/mathlib/commit/8c72ca3)
feat(data/mv_polynomial/basic): a polynomial ring over an R-algebra is also an R-algebra ([#6533](https://github.com/leanprover-community/mathlib/pull/6533))
#### Estimated changes
Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/data/mv_polynomial/basic.lean


Modified src/data/mv_polynomial/monad.lean




## [2021-03-04 17:49:11](https://github.com/leanprover-community/mathlib/commit/84f4d5c)
feat(order/zorn): nonempty formulation of Zorn's lemma ([#6532](https://github.com/leanprover-community/mathlib/pull/6532))
In practice it's often helpful to have this alternate formulation of Zorn's lemma
#### Estimated changes
Modified src/order/zorn.lean
- \+ *theorem* zorn.exists_maximal_of_nonempty_chains_bounded
- \+ *theorem* zorn.zorn_nonempty_partial_order



## [2021-03-04 17:49:10](https://github.com/leanprover-community/mathlib/commit/dbddee6)
feat(topology/continuous_on): add `set.left_inv_on.map_nhds_within_eq` ([#6529](https://github.com/leanprover-community/mathlib/pull/6529))
Also add some trivial lemmas to `data/set/function` and
`order/filter/basic`.
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* function.left_inverse.left_inv_on
- \+ *lemma* function.right_inverse.right_inv_on
- \+ *lemma* set.left_inv_on.right_inv_on_image
- \+ *theorem* set.surj_on_image

Modified src/order/filter/basic.lean
- \+ *lemma* set.maps_to.tendsto

Modified src/topology/continuous_on.lean
- \+ *lemma* function.left_inverse.map_nhds_eq
- \+ *theorem* nhds_within_inter_of_mem
- \+ *lemma* set.left_inv_on.map_nhds_within_eq



## [2021-03-04 17:49:09](https://github.com/leanprover-community/mathlib/commit/0690d97)
feat(bounded_continuous_function): norm_lt_of_compact ([#6524](https://github.com/leanprover-community/mathlib/pull/6524))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Modified src/topology/bounded_continuous_function.lean
- \+ *lemma* bounded_continuous_function.norm_le_of_nonempty
- \+ *lemma* bounded_continuous_function.norm_lt_of_compact

Modified src/topology/order.lean




## [2021-03-04 17:49:08](https://github.com/leanprover-community/mathlib/commit/10d2e70)
feat(order/lattice): "algebraic" constructors for (semi-)lattices ([#6460](https://github.com/leanprover-community/mathlib/pull/6460))
I also added a module doc string for `order/lattice.lean`.
#### Estimated changes
Modified src/order/lattice.lean
- \+ *def* lattice.mk'
- \+ *theorem* semilattice_inf.dual_dual
- \+ *def* semilattice_inf.mk'
- \+ *theorem* semilattice_sup.dual_dual
- \+ *def* semilattice_sup.mk'
- \+ *lemma* semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order
- \+ *theorem* sup_eq_iff_inf_eq



## [2021-03-04 16:01:55](https://github.com/leanprover-community/mathlib/commit/1cc59b9)
feat(set_theory/cardinal, data/nat/fincard): Define `nat`- and `enat`-valued cardinalities ([#6494](https://github.com/leanprover-community/mathlib/pull/6494))
Defines `cardinal.to_nat` and `cardinal.to_enat`
Uses those to define `nat.card` and `enat.card`
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.cast_to_nat_of_lt_omega
- \+ *lemma* cardinal.mk_to_enat_eq_coe_card
- \+ *lemma* cardinal.mk_to_enat_of_infinite
- \+ *lemma* cardinal.mk_to_nat_eq_card
- \+ *lemma* cardinal.mk_to_nat_of_infinite
- \+ *lemma* cardinal.one_to_nat
- \+ *lemma* cardinal.to_enat_apply_of_lt_omega
- \+ *lemma* cardinal.to_enat_apply_of_omega_le
- \+ *lemma* cardinal.to_enat_cast
- \+ *lemma* cardinal.to_enat_surjective
- \+ *lemma* cardinal.to_nat_apply_of_lt_omega
- \+ *lemma* cardinal.to_nat_apply_of_omega_le
- \+ *lemma* cardinal.to_nat_cast
- \+ *lemma* cardinal.to_nat_right_inverse
- \+ *lemma* cardinal.to_nat_surjective
- \+ *lemma* cardinal.zero_to_nat



## [2021-03-04 14:43:48](https://github.com/leanprover-community/mathlib/commit/9607dbd)
feat(analysis/convex): linear image of segment ([#6531](https://github.com/leanprover-community/mathlib/pull/6531))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* segment_image



## [2021-03-04 14:43:47](https://github.com/leanprover-community/mathlib/commit/a8d285c)
feat(algebra/direct_sum_graded): endow `direct_sum` with a ring structure ([#6053](https://github.com/leanprover-community/mathlib/pull/6053))
To quote the module docstring
> This module provides a set of heterogenous typeclasses for defining a multiplicative structure
> over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
> additively-graded ring. The typeclasses are:
> 
> * `direct_sum.ghas_one A`
> * `direct_sum.ghas_mul A`
> * `direct_sum.gmonoid A`
> * `direct_sum.gcomm_monoid A`
> 
> Respectively, these imbue the direct sum `⨁ i, A i` with:
> 
> * `has_one`
> * `mul_zero_class`, `distrib`
> * `semiring`, `ring`
> * `comm_semiring`, `comm_ring`
>
> Additionally, this module provides helper functions to construct `gmonoid` and `gcomm_monoid`
> instances for:
> 
> * `A : ι → submonoid S`: `direct_sum.ghas_one.of_submonoids`, `direct_sum.ghas_mul.of_submonoids`,
>   `direct_sum.gmonoid.of_submonoids`, `direct_sum.gcomm_monoid.of_submonoids`
> * `A : ι → submonoid S`: `direct_sum.ghas_one.of_subgroups`, `direct_sum.ghas_mul.of_subgroups`,
>   `direct_sum.gmonoid.of_subgroups`, `direct_sum.gcomm_monoid.of_subgroups`
> 
> If the `A i` are disjoint, these provide a gradation of `⨆ i, A i`, and the mapping
> `⨁ i, A i →+ ⨆ i, A i` can be obtained as
> `direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.
#### Estimated changes
Added src/algebra/direct_sum_graded.lean
- \+ *def* direct_sum.gcomm_monoid.of_add_subgroups
- \+ *def* direct_sum.gcomm_monoid.of_add_submonoids
- \+ *def* direct_sum.gcomm_monoid.of_submodules
- \+ *def* direct_sum.ghas_mul.of_add_subgroups
- \+ *def* direct_sum.ghas_mul.of_add_submonoids
- \+ *def* direct_sum.ghas_mul.of_submodules
- \+ *def* direct_sum.ghas_mul.to_sigma_has_mul
- \+ *def* direct_sum.ghas_one.of_add_subgroups
- \+ *def* direct_sum.ghas_one.of_add_submonoids
- \+ *def* direct_sum.ghas_one.of_submodules
- \+ *def* direct_sum.ghas_one.to_sigma_has_one
- \+ *def* direct_sum.gmonoid.of_add_subgroups
- \+ *def* direct_sum.gmonoid.of_add_submonoids
- \+ *def* direct_sum.gmonoid.of_submodules
- \+ *lemma* direct_sum.of_mul_of



## [2021-03-04 13:58:56](https://github.com/leanprover-community/mathlib/commit/edbbecb)
doc(group_theory/sylow): module doc ([#6477](https://github.com/leanprover-community/mathlib/pull/6477))
This PR provides the last module doc which was missing from `group_theory`, namely that for `sylow`.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *theorem* sylow.exists_subgroup_card_pow_prime
- \- *lemma* sylow.exists_subgroup_card_pow_prime



## [2021-03-04 11:33:23](https://github.com/leanprover-community/mathlib/commit/d32bb6e)
feat(data/finsupp/basic): add support_nonempty_iff and nonzero_iff_exists ([#6530](https://github.com/leanprover-community/mathlib/pull/6530))
Add two lemmas to work with `finsupp`s with non-empty support.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/finsupp.2Enonzero_iff_exists
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.nonzero_iff_exists
- \+ *lemma* finsupp.support_nonempty_iff



## [2021-03-04 11:33:22](https://github.com/leanprover-community/mathlib/commit/ca96bfb)
feat(linear_algebra/clifford_algebra): add definitions of the conjugation operators and some API ([#6491](https://github.com/leanprover-community/mathlib/pull/6491))
This also replaces the file with a directory, to avoid monstrous files from developing.
#### Estimated changes
Renamed src/linear_algebra/clifford_algebra.lean to src/linear_algebra/clifford_algebra/basic.lean


Added src/linear_algebra/clifford_algebra/conjugation.lean
- \+ *def* clifford_algebra.involute
- \+ *lemma* clifford_algebra.involute_comp_involute
- \+ *lemma* clifford_algebra.involute_involute
- \+ *lemma* clifford_algebra.involute_involutive
- \+ *lemma* clifford_algebra.involute_prod_map_ι
- \+ *lemma* clifford_algebra.involute_ι
- \+ *lemma* clifford_algebra.reverse.commutes
- \+ *lemma* clifford_algebra.reverse.map_mul
- \+ *lemma* clifford_algebra.reverse.map_one
- \+ *def* clifford_algebra.reverse
- \+ *lemma* clifford_algebra.reverse_comp_involute
- \+ *lemma* clifford_algebra.reverse_comp_reverse
- \+ *lemma* clifford_algebra.reverse_involute
- \+ *lemma* clifford_algebra.reverse_involute_commute
- \+ *lemma* clifford_algebra.reverse_involutive
- \+ *lemma* clifford_algebra.reverse_prod_map_ι
- \+ *lemma* clifford_algebra.reverse_reverse
- \+ *lemma* clifford_algebra.reverse_ι

Added src/linear_algebra/clifford_algebra/default.lean




## [2021-03-04 11:33:21](https://github.com/leanprover-community/mathlib/commit/deb3d45)
feat(data/mv_polynomial/equiv): generalize ring_equiv_congr ([#6420](https://github.com/leanprover-community/mathlib/pull/6420))
Following the discussion in [#6324](https://github.com/leanprover-community/mathlib/pull/6324), I have modified `mv_polynomial.ring_equiv_of_equiv` and `mv_polynomial.ring_equiv_congr`, that are now called `ring_equiv_congr_left` and `ring_equiv_congr_left`: both are proved as special cases of `ring_equiv_congr` (the situation for algebras is exactly the same).
This has the side effect that the lemmas automatically generated by `@[simps]` are not in a good form (see for example the lemma `mv_polynomial.alg_equiv_congr_left_apply ` in the current mathlib, where there is an unwanted `alg_equiv.refl.to_ring_equiv`). To avoid this I deleted the `@[simps]` and I wrote the lemmas by hand (also correcting the problem with `mv_polynomial.alg_equiv_congr_left_apply`). I probably don't understand completely `@[simps]`, since I had to manually modified some other proofs that no longer worked (I mean, I had to do something more that just using the new names).
If there is some `simp` lemma I forgot I would be happy to write it.
#### Estimated changes
Modified src/data/mv_polynomial/equiv.lean
- \+ *lemma* mv_polynomial.alg_equiv_congr_left_apply
- \+ *lemma* mv_polynomial.alg_equiv_congr_left_symm_apply
- \+ *lemma* mv_polynomial.alg_equiv_congr_right_apply
- \+ *lemma* mv_polynomial.alg_equiv_congr_right_symm_apply
- \+/\- *def* mv_polynomial.ring_equiv_congr
- \+ *def* mv_polynomial.ring_equiv_congr_left
- \+ *lemma* mv_polynomial.ring_equiv_congr_left_apply
- \+ *lemma* mv_polynomial.ring_equiv_congr_left_symm_apply
- \+ *def* mv_polynomial.ring_equiv_congr_right
- \+ *lemma* mv_polynomial.ring_equiv_congr_right_apply
- \+ *lemma* mv_polynomial.ring_equiv_congr_right_symm_apply
- \- *def* mv_polynomial.ring_equiv_of_equiv

Modified src/data/mv_polynomial/funext.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/polynomial/basic.lean




## [2021-03-04 08:43:30](https://github.com/leanprover-community/mathlib/commit/3329ec4)
chore(topology/algebra/*): tendsto namespacing ([#6528](https://github.com/leanprover-community/mathlib/pull/6528))
Correct a few lemmas which I noticed were namespaced as `tendsto.***` rather than `filter.tendsto.***`, and thus couldn't be used with projection notation.
Also use the projection notation, where now permitted.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Search.20for.20all.20declarations.20in.20a.20namespace)
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/real/pi.lean


Modified src/topology/algebra/monoid.lean
- \+ *lemma* filter.tendsto.const_mul
- \+ *lemma* filter.tendsto.mul_const
- \- *lemma* tendsto.const_mul
- \- *lemma* tendsto.mul_const

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.tendsto.inv_tendsto_at_top
- \+ *lemma* filter.tendsto.inv_tendsto_zero
- \+ *lemma* filter.tendsto.max
- \+ *lemma* filter.tendsto.min
- \- *lemma* tendsto.inv_tendsto_at_top
- \- *lemma* tendsto.inv_tendsto_zero
- \- *lemma* tendsto.max
- \- *lemma* tendsto.min



## [2021-03-04 08:43:29](https://github.com/leanprover-community/mathlib/commit/76aee25)
refactor(big_operators/basic): move prod_mul_prod_compl ([#6526](https://github.com/leanprover-community/mathlib/pull/6526))
Several lemmas were unnecessarily in `src/data/fintype/card.lean`, and I've relocated them to `src/algebra/big_operators/basic.lean`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_compl_mul_prod
- \+ *lemma* finset.prod_mul_prod_compl
- \+ *lemma* is_compl.prod_mul_prod

Modified src/data/fintype/basic.lean
- \+ *theorem* finset.union_compl

Modified src/data/fintype/card.lean
- \- *lemma* finset.prod_compl_mul_prod
- \- *lemma* finset.prod_mul_prod_compl
- \- *lemma* is_compl.prod_mul_prod



## [2021-03-04 08:43:28](https://github.com/leanprover-community/mathlib/commit/d7fa1bc)
feat(topology/instances/real): generalize 'compact_space I' to 'compact_space (Icc a b)' ([#6523](https://github.com/leanprover-community/mathlib/pull/6523))
#### Estimated changes
Modified src/topology/instances/real.lean


Modified src/topology/path_connected.lean




## [2021-03-04 08:43:27](https://github.com/leanprover-community/mathlib/commit/2f35779)
chore(*/sub*): tidy up inherited algebraic structures from parent objects ([#6509](https://github.com/leanprover-community/mathlib/pull/6509))
This changes `subfield.to_field` to ensure that division is defeq.
It also removes `subring.subset_comm_ring` which was identical to `subring.to_comm_ring`, renames some `subalgebra` instances to match those of `subring`s, and cleans up a few related proofs that relied on the old names.
These are cleanups split from [#6489](https://github.com/leanprover-community/mathlib/pull/6489), which failed CI but was otherwise approved
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/field_theory/subfield.lean
- \+ *lemma* subfield.coe_div
- \+ *lemma* subfield.coe_sub

Modified src/group_theory/subgroup.lean




## [2021-03-04 07:49:34](https://github.com/leanprover-community/mathlib/commit/f4db322)
feat(category_theory/subobject): factoring morphisms through subobjects ([#6302](https://github.com/leanprover-community/mathlib/pull/6302))
The predicate `h : P.factors f`, for `P : subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factor_thru f : X ⟶ (P : C)` making the obvious diagram commute.
We provide conditions for `P.factors f`, when `P` is a kernel/equalizer/image/inf/sup subobject.
#### Estimated changes
Modified src/category_theory/subobject.lean
- \+ *lemma* category_theory.limits.equalizer_subobject_factors
- \+ *lemma* category_theory.limits.equalizer_subobject_factors_iff
- \+ *lemma* category_theory.limits.image_subobject_factors
- \+ *lemma* category_theory.limits.image_subobject_le
- \+ *lemma* category_theory.limits.kernel_subobject_factors
- \+ *lemma* category_theory.limits.kernel_subobject_factors_iff
- \+ *def* category_theory.mono_over.factor_thru
- \+ *def* category_theory.mono_over.factors
- \+ *lemma* category_theory.mono_over.image_mono_over_arrow
- \+ *lemma* category_theory.subobject.bot_arrow
- \+ *def* category_theory.subobject.bot_coe_iso_zero
- \+ *lemma* category_theory.subobject.bot_factors_iff_zero
- \+ *lemma* category_theory.subobject.eq_of_comp_arrow_eq
- \+ *def* category_theory.subobject.factor_thru
- \+ *lemma* category_theory.subobject.factor_thru_arrow
- \+ *lemma* category_theory.subobject.factor_thru_eq_zero
- \+ *lemma* category_theory.subobject.factor_thru_right
- \+ *def* category_theory.subobject.factors
- \+ *lemma* category_theory.subobject.factors_comp_arrow
- \+ *lemma* category_theory.subobject.factors_iff
- \+ *lemma* category_theory.subobject.factors_left_of_inf_factors
- \+ *lemma* category_theory.subobject.factors_of_factors_right
- \+ *lemma* category_theory.subobject.factors_of_le
- \+ *lemma* category_theory.subobject.factors_right_of_inf_factors
- \+ *lemma* category_theory.subobject.finset_inf_arrow_factors
- \+ *lemma* category_theory.subobject.finset_inf_factors
- \+ *lemma* category_theory.subobject.finset_sup_factors
- \+ *lemma* category_theory.subobject.inf_arrow_factors_left
- \+ *lemma* category_theory.subobject.inf_arrow_factors_right
- \+ *lemma* category_theory.subobject.inf_factors
- \+ *lemma* category_theory.subobject.le_of_comm
- \+ *lemma* category_theory.subobject.representative_arrow
- \+ *lemma* category_theory.subobject.representative_coe
- \+ *lemma* category_theory.subobject.sup_factors_of_factors_left
- \+ *lemma* category_theory.subobject.sup_factors_of_factors_right
- \+ *def* category_theory.subobject.top_coe_iso_self
- \+ *lemma* category_theory.subobject.top_factors
- \+ *lemma* category_theory.subobject.underlying_iso_arrow
- \+ *lemma* category_theory.subobject.underlying_iso_id_eq_top_coe_iso_self
- \+ *lemma* category_theory.subobject.underlying_iso_inv_top_arrow



## [2021-03-04 02:11:25](https://github.com/leanprover-community/mathlib/commit/8289518)
feat(algebra/star): the Bell/CHSH/Tsirelson inequalities ([#4687](https://github.com/leanprover-community/mathlib/pull/4687))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/star/basic.lean


Added src/algebra/star/chsh.lean
- \+ *lemma* CHSH_inequality_of_comm
- \+ *structure* is_CHSH_tuple
- \+ *lemma* tsirelson_inequality.neg_two_gsmul_half_smul
- \+ *lemma* tsirelson_inequality.smul_four
- \+ *lemma* tsirelson_inequality.smul_two
- \+ *lemma* tsirelson_inequality.sqrt_two_inv_mul_self
- \+ *lemma* tsirelson_inequality.tsirelson_inequality_aux
- \+ *lemma* tsirelson_inequality.two_gsmul_half_smul
- \+ *lemma* tsirelson_inequality

Modified src/data/complex/basic.lean


Modified src/data/matrix/basic.lean


Modified src/data/real/basic.lean




## [2021-03-04 01:15:55](https://github.com/leanprover-community/mathlib/commit/2837807)
chore(scripts): update nolints.txt ([#6527](https://github.com/leanprover-community/mathlib/pull/6527))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-03 13:41:37](https://github.com/leanprover-community/mathlib/commit/3c9399d)
chore(algebra/ordered_group): put to_additive on lemmas about linear_ordered_comm_group ([#6506](https://github.com/leanprover-community/mathlib/pull/6506))
No lemmas are added or renamed for the additive version, this just adds lemmas (and more importantly instances) for the multiplicative version.
This:
* Adds missing `ancestor` attributes to `linear_ordered_add_comm_group` and `linear_ordered_comm_group`, which are needed to make `to_additive` work correctly on `to_add_comm_group` and `to_comm_group`
* Adds multiplicative versions of:
  * `sub_le_self_iff` (`div_le_self_iff`)
  * `sub_lt_self_iff` (`div_lt_self_iff `)
  * `linear_ordered_add_comm_group.to_linear_ordered_cancel_add_comm_monoid` (`linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid`)
  * `linear_ordered_add_comm_group.add_lt_add_left` (`linear_ordered_comm_group.mul_lt_mul_left'`)
  * `min_neg_neg` (`min_inv_inv'`)
  * `max_neg_neg` (`max_inv_inv'`)
  * `min_sub_sub_right` (`min_div_div_right'`)
  * `min_sub_sub_left` (`min_div_div_left'`)
  * `max_sub_sub_right` (`max_div_div_right'`)
  * `max_sub_sub_left` (`max_div_div_left'`)
  * `max_zero_sub_eq_self` (`max_one_div_eq_self'`)
  * `eq_zero_of_neg_eq` (`eq_one_of_inv_eq'`)
  * `exists_zero_lt` (`exists_one_lt'`)
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* div_le_self_iff
- \+ *lemma* div_lt_self_iff
- \+ *lemma* eq_one_of_inv_eq'
- \- *lemma* eq_zero_of_neg_eq
- \+ *lemma* exists_one_lt'
- \- *lemma* exists_zero_lt
- \- *lemma* linear_ordered_add_comm_group.add_lt_add_left
- \+ *lemma* linear_ordered_comm_group.mul_lt_mul_left'
- \+ *lemma* max_div_div_left'
- \+ *lemma* max_div_div_right'
- \+ *lemma* max_inv_inv'
- \- *lemma* max_neg_neg
- \+ *lemma* max_one_div_eq_self'
- \- *lemma* max_sub_sub_left
- \- *lemma* max_sub_sub_right
- \- *lemma* max_zero_sub_eq_self
- \+ *lemma* min_div_div_left'
- \+ *lemma* min_div_div_right'
- \+ *lemma* min_inv_inv'
- \- *lemma* min_neg_neg
- \- *lemma* min_sub_sub_left
- \- *lemma* min_sub_sub_right
- \- *lemma* sub_le_self_iff
- \- *lemma* sub_lt_self_iff



## [2021-03-03 13:41:37](https://github.com/leanprover-community/mathlib/commit/d4ac4c3)
feat(data/list/basic): add `list.prod_eq_zero(_iff)` ([#6504](https://github.com/leanprover-community/mathlib/pull/6504))
API changes:
* add `list.prod_eq_zero`, `list.prod_eq_zero_iff`, ;
* lemmas `list.prod_ne_zero`, `multiset.prod_ne_zero`, `polynomial.root_list_prod`, `polynomial.roots_multiset_prod`, `polynomial.nat_degree_multiset_prod`,  now assume `0 ∉ L` (or `0 ∉ m`/`0 ∉ s`) instead of `∀ x ∈ L, x ≠ 0`
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.prod_eq_zero
- \+ *theorem* list.prod_eq_zero_iff
- \+/\- *theorem* list.prod_ne_zero

Modified src/data/multiset/basic.lean
- \+/\- *lemma* multiset.prod_eq_zero
- \+ *lemma* multiset.prod_eq_zero_iff
- \- *theorem* multiset.prod_eq_zero_iff
- \+/\- *theorem* multiset.prod_ne_zero

Modified src/data/polynomial/degree/definitions.lean
- \+ *theorem* polynomial.zero_nmem_multiset_map_X_sub_C

Modified src/data/polynomial/ring_division.lean


Modified src/field_theory/splitting_field.lean




## [2021-03-03 13:41:36](https://github.com/leanprover-community/mathlib/commit/a852bf4)
feat(data/equiv/fin): fin_add_flip and fin_rotate ([#6454](https://github.com/leanprover-community/mathlib/pull/6454))
Add
* `fin_add_flip : fin (m + n) ≃ fin (n + m)`
* `fin_rotate : Π n, fin n ≃ fin n` (acts by +1 mod n)
and simp lemmas, and shows `fin.snoc` is a rotation of `fin.cons`.
#### Estimated changes
Modified src/data/equiv/fin.lean
- \+ *lemma* fin.snoc_eq_cons_rotate
- \+ *def* fin_add_flip
- \+ *lemma* fin_add_flip_apply_left
- \+ *lemma* fin_add_flip_apply_right
- \+ *def* fin_congr
- \+ *lemma* fin_congr_apply_coe
- \+ *lemma* fin_congr_apply_mk
- \+ *lemma* fin_congr_symm
- \+ *lemma* fin_congr_symm_apply_coe
- \+ *def* fin_rotate
- \+ *lemma* fin_rotate_last'
- \+ *lemma* fin_rotate_last
- \+ *lemma* fin_rotate_of_lt

Modified src/data/nat/basic.lean
- \+ *lemma* nat.eq_of_le_of_lt_succ



## [2021-03-03 10:36:54](https://github.com/leanprover-community/mathlib/commit/9c48eb1)
chore(ring_theory/{subring,integral_closure}): simplify a proof, remove redundant instances ([#6513](https://github.com/leanprover-community/mathlib/pull/6513))
#### Estimated changes
Modified src/field_theory/subfield.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/subring.lean
- \- *def* subring.subset_comm_ring



## [2021-03-03 10:36:53](https://github.com/leanprover-community/mathlib/commit/eec54d0)
feat(algebra/field): add function.injective.field ([#6511](https://github.com/leanprover-community/mathlib/pull/6511))
We already have defs of this style for all sorts of algebraic constructions, why not one more.
#### Estimated changes
Modified src/algebra/field.lean




## [2021-03-03 10:36:52](https://github.com/leanprover-community/mathlib/commit/3309ce2)
refactor(ring_theory/polynomial/chebyshev): move lemmas around ([#6510](https://github.com/leanprover-community/mathlib/pull/6510))
As discussed in [#6501](https://github.com/leanprover-community/mathlib/pull/6501), split up the old file `ring_theory.polynomial.chebyshev.basic`, moving half its contents to `ring_theory.polynomial.chebyshev.defs` and the other half to `ring_theory.polynomial.chebyshev.dickson`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean


Renamed src/ring_theory/polynomial/chebyshev/defs.lean to src/ring_theory/polynomial/chebyshev.lean
- \+ *lemma* polynomial.chebyshev₁_mul
- \+ *lemma* polynomial.mul_chebyshev₁

Deleted src/ring_theory/polynomial/chebyshev/default.lean


Deleted src/ring_theory/polynomial/chebyshev/dickson.lean
- \- *lemma* polynomial.dickson_add_two
- \- *lemma* polynomial.dickson_of_two_le
- \- *lemma* polynomial.dickson_one
- \- *lemma* polynomial.dickson_two
- \- *lemma* polynomial.dickson_two_zero
- \- *lemma* polynomial.dickson_zero
- \- *lemma* polynomial.map_dickson

Renamed src/ring_theory/polynomial/chebyshev/basic.lean to src/ring_theory/polynomial/dickson.lean
- \- *lemma* polynomial.chebyshev₁_mul
- \+ *lemma* polynomial.dickson_add_two
- \+ *lemma* polynomial.dickson_of_two_le
- \+ *lemma* polynomial.dickson_one
- \+ *lemma* polynomial.dickson_two
- \+ *lemma* polynomial.dickson_two_zero
- \+ *lemma* polynomial.dickson_zero
- \+ *lemma* polynomial.map_dickson
- \- *lemma* polynomial.mul_chebyshev₁



## [2021-03-03 07:35:46](https://github.com/leanprover-community/mathlib/commit/383dd2b)
chore(data/equiv): add missing simp lemmas about mk ([#6505](https://github.com/leanprover-community/mathlib/pull/6505))
This adds missing `mk_coe` lemmas, and new `symm_mk`, `symm_bijective`, and `mk_coe'` lemmas.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.coe_mk
- \- *lemma* alg_equiv.mk_apply
- \+ *lemma* alg_equiv.mk_coe'
- \+ *theorem* alg_equiv.mk_coe
- \+ *lemma* alg_equiv.symm_bijective
- \+ *theorem* alg_equiv.symm_mk
- \+/\- *lemma* alg_equiv.symm_symm
- \- *lemma* alg_equiv.to_fun_apply
- \+ *lemma* alg_equiv.to_fun_eq_coe
- \+ *lemma* alg_hom.to_fun_eq_coe

Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_equiv.mk_coe'
- \+ *lemma* linear_equiv.mk_coe
- \+ *lemma* linear_equiv.symm_bijective
- \+ *theorem* linear_equiv.symm_mk

Modified src/data/equiv/mul_add.lean
- \- *theorem* mul_equiv.coe_symm_mk
- \+ *lemma* mul_equiv.mk_coe'
- \+ *lemma* mul_equiv.mk_coe
- \+ *lemma* mul_equiv.symm_bijective
- \+ *theorem* mul_equiv.symm_mk
- \+ *lemma* mul_equiv.symm_symm

Modified src/data/equiv/ring.lean
- \+ *theorem* ring_equiv.coe_mk
- \- *lemma* ring_equiv.coe_symm_mk
- \+ *lemma* ring_equiv.mk_coe'
- \+ *theorem* ring_equiv.mk_coe
- \+ *lemma* ring_equiv.symm_bijective
- \+ *lemma* ring_equiv.symm_mk



## [2021-03-02 23:24:10](https://github.com/leanprover-community/mathlib/commit/22e3437)
feat(algebra/big_operators/basic): lemmas prod_range_add, sum_range_add ([#6484](https://github.com/leanprover-community/mathlib/pull/6484))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_range_add
- \+ *lemma* finset.sum_range_add



## [2021-03-02 22:25:31](https://github.com/leanprover-community/mathlib/commit/19ed0f8)
refactor(ring_theory/valuation): valuations in `linear_ordered_comm_monoid_with_zero` ([#6500](https://github.com/leanprover-community/mathlib/pull/6500))
Generalizes the value group in a `valuation` to a `linear_ordered_comm_monoid_with_zero`
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* valuation.is_equiv_of_map_strict_mono
- \+/\- *lemma* valuation.is_equiv_of_val_le_one
- \+/\- *lemma* valuation.ne_zero_iff
- \+/\- *lemma* valuation.zero_iff



## [2021-03-02 19:27:12](https://github.com/leanprover-community/mathlib/commit/0c5b517)
feat(ring_theory/polynomial/chebyshev/basic): multiplication of Chebyshev polynomials ([#6501](https://github.com/leanprover-community/mathlib/pull/6501))
Add the identity for multiplication of Chebyshev polynomials,
```lean
2 * chebyshev₁ R m * chebyshev₁ R (m + k) = chebyshev₁ R (2 * m + k) + chebyshev₁ R k
```
Use this to give a direct proof of the identity `chebyshev₁_mul` for composition of Chebyshev polynomials, replacing the current proof using trig functions.  This means that the import `import analysis.special_functions.trigonometric` to the Chebyshev file can be removed.
#### Estimated changes
Modified src/ring_theory/polynomial/chebyshev/basic.lean
- \+/\- *lemma* polynomial.chebyshev₁_mul
- \+ *lemma* polynomial.mul_chebyshev₁



## [2021-03-02 19:27:11](https://github.com/leanprover-community/mathlib/commit/0c863e9)
refactor(data/set/finite): change type of `set.finite.dependent_image` ([#6475](https://github.com/leanprover-community/mathlib/pull/6475))
The old lemma combined a statement similar to `set.finite.image` with
`set.finite.subset`. The new statement is a direct generalization of
`set.finite.image`.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* set.finite.dependent_image



## [2021-03-02 16:36:18](https://github.com/leanprover-community/mathlib/commit/c087011)
refactor(data/set/finite): make `finite` argument of `set.finite.mem_to_finset` explicit ([#6508](https://github.com/leanprover-community/mathlib/pull/6508))
This way we can use dot notation.
#### Estimated changes
Modified src/data/finset/preimage.lean


Modified src/data/set/finite.lean
- \+/\- *theorem* set.finite.mem_to_finset

Modified src/linear_algebra/linear_independent.lean


Modified src/measure_theory/integration.lean


Modified src/order/compactly_generated.lean


Modified src/order/filter/cofinite.lean


Modified src/order/order_iso_nat.lean




## [2021-03-02 15:26:34](https://github.com/leanprover-community/mathlib/commit/9f0f05e)
feat(data/{nat,int}/parity): even_mul_succ_self ([#6507](https://github.com/leanprover-community/mathlib/pull/6507))
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *lemma* int.even_mul_succ_self

Modified src/data/nat/parity.lean
- \+ *lemma* nat.even_mul_succ_self



## [2021-03-02 08:23:47](https://github.com/leanprover-community/mathlib/commit/6b5e48d)
feat(data/finset/lattice): +2 induction principles for `finset`s ([#6502](https://github.com/leanprover-community/mathlib/pull/6502))
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.induction_on_max
- \+ *lemma* finset.induction_on_min



## [2021-03-02 06:06:52](https://github.com/leanprover-community/mathlib/commit/572f727)
chore(algebra/big_operators): use weaker typeclass assumptions ([#6503](https://github.com/leanprover-community/mathlib/pull/6503))
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+/\- *lemma* finset.prod_pos



## [2021-03-02 04:20:01](https://github.com/leanprover-community/mathlib/commit/c69c8a9)
chore(scripts): update nolints.txt ([#6499](https://github.com/leanprover-community/mathlib/pull/6499))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2021-03-02 02:22:47](https://github.com/leanprover-community/mathlib/commit/f63069f)
feat(linear_algebra/basic): simp lemmas about endomorphisms ([#6452](https://github.com/leanprover-community/mathlib/pull/6452))
Also renames some lemmas:
* `linear_map.one_app` has been renamed to `linear_map.one_apply`
* `linear_map.mul_app` has been removed in favour of the existing `linear_map.mul_app`.
#### Estimated changes
Modified src/algebra/lie/quotient.lean


Modified src/analysis/calculus/lagrange_multipliers.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.coe_mul
- \+ *lemma* linear_map.coe_one
- \+ *lemma* linear_map.coe_pow
- \- *lemma* linear_map.mul_app
- \+/\- *lemma* linear_map.mul_apply
- \- *lemma* linear_map.one_app
- \+ *lemma* linear_map.one_apply
- \+ *lemma* linear_map.pow_apply

Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/matrix.lean


Modified src/ring_theory/derivation.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/simple_module.lean




## [2021-03-02 02:22:45](https://github.com/leanprover-community/mathlib/commit/5c01613)
feat(analysis/special_functions/integrals): some simple integration lemmas ([#6216](https://github.com/leanprover-community/mathlib/pull/6216))
Integration of some simple functions, including `sin`, `cos`, `pow`, and `inv`. @ADedecker and I are working on the integrals of some more intricate functions, which we hope to add in a subsequent (series of) PR(s).
With this PR, simple integrals are now computable by `norm_num`. Here are some examples:
```
import analysis.special_functions.integrals
open real interval_integral
open_locale real
example : ∫ x in 0..π, sin x = 2 := by norm_num
example : ∫ x in 0..π/4, cos x = sqrt 2 / 2 := by simp
example : ∫ x:ℝ in 2..4, x^(3:ℕ) = 60 := by norm_num
example : ∫ x in 0..2, -exp x = 1 - exp 2 := by simp
example : ∫ x:ℝ in (-1)..4, x = 15/2 := by norm_num
example : ∫ x:ℝ in 8..11, (1:ℝ) = 3 := by norm_num
example : ∫ x:ℝ in 2..3, x⁻¹ = log (3/2) := by norm_num
example : ∫ x:ℝ in 0..1, 1 / (1 + x^2) = π/4 := by simp
```
`integral_deriv_eq_sub'` courtesy of @gebner.
#### Estimated changes
Added src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_cos
- \+ *lemma* integral_exp
- \+ *lemma* integral_id
- \+ *lemma* integral_inv
- \+ *lemma* integral_inv_of_neg
- \+ *lemma* integral_inv_of_pos
- \+ *lemma* integral_inv_one_add_sq
- \+ *lemma* integral_one
- \+ *lemma* integral_one_div
- \+ *lemma* integral_one_div_of_neg
- \+ *lemma* integral_one_div_of_pos
- \+ *lemma* integral_one_div_one_add_sq
- \+ *lemma* integral_pow
- \+ *lemma* integral_sin

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* real.continuous_on_sin

Modified src/measure_theory/interval_integral.lean
- \+ *theorem* interval_integral.integral_deriv_eq_sub'



## [2021-03-02 00:24:51](https://github.com/leanprover-community/mathlib/commit/5eb7ebb)
feat(data/polynomial): lemmas about polynomial derivative ([#6433](https://github.com/leanprover-community/mathlib/pull/6433))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \- *lemma* polynomial.pow_comp

Modified src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.derivative_C_mul
- \+ *lemma* polynomial.derivative_cast_nat
- \+ *lemma* polynomial.derivative_comp
- \+ *def* polynomial.derivative_lhom
- \+ *lemma* polynomial.derivative_lhom_coe
- \+/\- *lemma* polynomial.derivative_sub
- \+ *lemma* polynomial.iterate_derivative_C_mul
- \+ *lemma* polynomial.iterate_derivative_add
- \+ *lemma* polynomial.iterate_derivative_cast_nat_mul
- \+ *theorem* polynomial.iterate_derivative_map
- \+ *lemma* polynomial.iterate_derivative_neg
- \+ *lemma* polynomial.iterate_derivative_smul
- \+ *lemma* polynomial.iterate_derivative_sub
- \+ *lemma* polynomial.iterate_derivative_zero

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.cast_int_comp
- \+ *lemma* polynomial.cast_nat_comp
- \+ *lemma* polynomial.monomial_comp
- \+ *lemma* polynomial.pow_comp



## [2021-03-01 21:31:43](https://github.com/leanprover-community/mathlib/commit/0334475)
ci(scripts/detect_errors): try to show info messages in a way github understands ([#6493](https://github.com/leanprover-community/mathlib/pull/6493))
I don't actually know if this works, but I know that the previous code was not working:
https://github.com/leanprover-community/mathlib/pull/6485/checks?check_run_id=2006396264#step:7:7
#### Estimated changes
Modified scripts/detect_errors.py




## [2021-03-01 21:31:42](https://github.com/leanprover-community/mathlib/commit/0a5f69c)
feat(src/order/basic): show injectivity of order conversions, and tag lemmas with ext ([#6490](https://github.com/leanprover-community/mathlib/pull/6490))
Stating these as `function.injective` provides slightly more API, especially since before only the composition was proven as injective.
For convenience, this leaves behind `preorder.ext`, `partial_order.ext`, and `linear_order.ext`, although these are now provable with trivial applications of `ext`.
#### Estimated changes
Modified src/order/basic.lean
- \+ *lemma* linear_order.to_partial_order_injective
- \+ *lemma* partial_order.to_preorder_injective
- \+ *lemma* preorder.to_has_le_injective



## [2021-03-01 21:31:41](https://github.com/leanprover-community/mathlib/commit/cc57915)
chore(data/equiv/basic): add simp lemmas about subtype_equiv ([#6479](https://github.com/leanprover-community/mathlib/pull/6479))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.cast_refl
- \+ *lemma* equiv.subtype_equiv_refl
- \+ *lemma* equiv.subtype_equiv_symm
- \- *lemma* equiv.subtype_equiv_symm_apply
- \+ *lemma* equiv.subtype_equiv_trans



## [2021-03-01 21:31:40](https://github.com/leanprover-community/mathlib/commit/354fda0)
feat(linear_algebra/finsupp): add mem_span_set ([#6457](https://github.com/leanprover-community/mathlib/pull/6457))
From the doc-string:
If `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, then we can write
`m` as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`.
The initial proof was a substantial simplification of mine, due to Kevin Buzzard.  The final one is due to Eric Wieser.
Zulip discussion for the proof:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/submodule.2Espan.20as_sum
Zulip discussion for the universe issue:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universe.20issue.20with.20.60Type*.60
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+ *lemma* mem_span_set



## [2021-03-01 21:31:39](https://github.com/leanprover-community/mathlib/commit/e0a4dd8)
feat(ring_theory/finiteness): improve API for finite presentation ([#6382](https://github.com/leanprover-community/mathlib/pull/6382))
Improve the API for finitely presented morphism. I changed the name from `algebra.finitely_presented` to `algebra.finite_presentation` that seems more coherent with the other names.
Coming soon: transitivity of finite presentation.
#### Estimated changes
Modified src/ring_theory/finiteness.lean
- \+ *lemma* alg_hom.finite_presentation.comp_surjective
- \+ *lemma* alg_hom.finite_presentation.id
- \+ *lemma* alg_hom.finite_presentation.of_finite_type
- \+ *lemma* alg_hom.finite_presentation.of_surjective
- \+ *def* alg_hom.finite_presentation
- \+ *lemma* alg_hom.finite_type.of_finite_presentation
- \+ *lemma* algebra.finite_presentation.equiv
- \+ *lemma* algebra.finite_presentation.iff_quotient_mv_polynomial'
- \+ *lemma* algebra.finite_presentation.mv_polynomial
- \+ *lemma* algebra.finite_presentation.of_finite_type
- \+ *lemma* algebra.finite_presentation.of_surjective
- \+ *lemma* algebra.finite_presentation.quotient
- \+ *lemma* algebra.finite_presentation.self
- \+ *def* algebra.finite_presentation
- \+ *lemma* algebra.finite_type.of_finite_presentation
- \- *lemma* algebra.finite_type.of_finitely_presented
- \- *lemma* algebra.finitely_presented.equiv
- \- *lemma* algebra.finitely_presented.mv_polynomial
- \- *lemma* algebra.finitely_presented.of_surjective
- \- *lemma* algebra.finitely_presented.quotient
- \- *lemma* algebra.finitely_presented.self
- \- *def* algebra.finitely_presented
- \+ *lemma* ring_hom.finite_presentation.comp_surjective
- \+ *lemma* ring_hom.finite_presentation.id
- \+ *lemma* ring_hom.finite_presentation.of_finite_type
- \+ *lemma* ring_hom.finite_presentation.of_surjective
- \+ *def* ring_hom.finite_presentation
- \+ *lemma* ring_hom.finite_type.of_finite_presentation



## [2021-03-01 18:58:11](https://github.com/leanprover-community/mathlib/commit/0faa788)
feat(ring_theory/hahn_series): introduce ring of Hahn series ([#6237](https://github.com/leanprover-community/mathlib/pull/6237))
Defines Hahn series
Provides basic algebraic structure on Hahn series, up to `comm_ring`.
#### Estimated changes
Modified src/data/support.lean
- \+ *lemma* function.support_smul_subset
- \+ *lemma* pi.support_single
- \+ *lemma* pi.support_single_of_ne
- \+ *lemma* pi.support_single_subset
- \+ *lemma* pi.support_single_zero

Added src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.add_coeff'
- \+ *lemma* hahn_series.add_coeff
- \+ *lemma* hahn_series.is_wf_support
- \+ *lemma* hahn_series.mem_support
- \+ *lemma* hahn_series.mul_coeff
- \+ *lemma* hahn_series.mul_coeff_left'
- \+ *lemma* hahn_series.mul_coeff_right'
- \+ *lemma* hahn_series.mul_single_zero_coeff
- \+ *lemma* hahn_series.neg_coeff'
- \+ *lemma* hahn_series.neg_coeff
- \+ *lemma* hahn_series.one_coeff
- \+ *def* hahn_series.single
- \+ *theorem* hahn_series.single_coeff
- \+ *theorem* hahn_series.single_coeff_of_ne
- \+ *theorem* hahn_series.single_coeff_same
- \+ *lemma* hahn_series.single_eq_zero
- \+ *lemma* hahn_series.single_zero_mul_eq_smul
- \+ *lemma* hahn_series.single_zero_one
- \+ *lemma* hahn_series.smul_coeff
- \+ *lemma* hahn_series.sub_coeff'
- \+ *lemma* hahn_series.sub_coeff
- \+ *def* hahn_series.support
- \+ *theorem* hahn_series.support_mul_subset_add_support
- \+ *lemma* hahn_series.support_single_of_ne
- \+ *lemma* hahn_series.support_zero
- \+ *lemma* hahn_series.zero_coeff
- \+ *structure* hahn_series



## [2021-03-01 15:40:36](https://github.com/leanprover-community/mathlib/commit/e77f071)
feat(linear_algebra/{clifford,exterior,tensor}_algebra): add induction principles ([#6416](https://github.com/leanprover-community/mathlib/pull/6416))
These are closely derived from the induction principle for the free algebra.
I can't think of a good way to deduplicate them, so for now I've added comments making it clear to the reader that the code is largely copied.
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/linear_algebra/clifford_algebra.lean
- \+ *lemma* clifford_algebra.induction

Modified src/linear_algebra/exterior_algebra.lean
- \+ *lemma* exterior_algebra.induction

Modified src/linear_algebra/tensor_algebra.lean
- \+ *lemma* tensor_algebra.induction



## [2021-03-01 10:35:11](https://github.com/leanprover-community/mathlib/commit/aff6bd1)
fix(group_action/defs): make mul_action.regular an instance ([#6241](https://github.com/leanprover-community/mathlib/pull/6241))
This is essentially already an instance via `semiring.to_semimodule.to_distrib_mul_action.to_mul_action`, but with an unecessary `semiring R` constraint.
I can't remember the details, but I've run into multiple instance resolution issues in the past that were resolved with `local attribute [instance] mul_action.regular`.
This also renames the instance to `monoid.to_mul_action` for consistency with `semiring.to_semimodule`.
#### Estimated changes
Modified src/algebra/group_action_hom.lean


Modified src/algebra/module/basic.lean
- \- *lemma* smul_eq_mul

Modified src/data/finsupp/basic.lean


Modified src/group_theory/group_action/defs.lean
- \- *def* mul_action.regular
- \+ *lemma* smul_eq_mul



## [2021-03-01 04:31:52](https://github.com/leanprover-community/mathlib/commit/6ac19b4)
doc(algebra/ring/basic): change pullback and injective to pushforward and surjective ([#6487](https://github.com/leanprover-community/mathlib/pull/6487))
Zulip reference:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/pullback.20vs.20pushforward
#### Estimated changes
Modified src/algebra/ring/basic.lean




## [2021-03-01 01:14:26](https://github.com/leanprover-community/mathlib/commit/9ad469d)
chore(scripts): update nolints.txt ([#6486](https://github.com/leanprover-community/mathlib/pull/6486))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt


