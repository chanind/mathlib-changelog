## [2020-06-30 22:34:44](https://github.com/leanprover-community/mathlib/commit/0625691)
chore(topology/*): use dot syntax for some lemmas ([#3251](https://github.com/leanprover-community/mathlib/pull/3251))
Rename:
* `closure_eq_of_is_closed` to `is_closed.closure_eq`;
* `closed_of_compact` to `compact.is_closed`;
* `bdd_above_of_compact` to `compact.bdd_above`;
* `bdd_below_of_compact` to `compact.bdd_below`.
* `is_complete_of_is_closed` to `is_closed.is_complete`
* `is_closed_of_is_complete` to `is_complete.is_closed`
* `is_closed_iff_nhds` to `is_closed_iff_cluster_pt`
* `closure_subset_iff_subset_of_is_closed` to `is_closed.closure_subset_iff`
Add:
* `closure_closed_ball` (`@[simp]` lemma)
* `is_closed.closure_subset : is_closed s → closure s ⊆ s`
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/ordered.lean
- \- *lemma* bdd_above_of_compact
- \- *lemma* bdd_below_of_compact
- \+ *lemma* compact.bdd_above
- \+ *lemma* compact.bdd_below

Modified src/topology/basic.lean
- \+/\- *lemma* closure_empty_iff
- \- *lemma* closure_eq_of_is_closed
- \+ *lemma* closure_subset_iff_is_closed
- \- *lemma* closure_subset_iff_subset_of_is_closed
- \+ *lemma* is_closed.closure_eq
- \+ *lemma* is_closed.closure_subset
- \+ *lemma* is_closed.closure_subset_iff
- \+ *lemma* is_closed_iff_cluster_pt
- \- *lemma* is_closed_iff_nhds

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.closure_closed_ball

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/opens.lean


Modified src/topology/separation.lean
- \- *lemma* closed_of_compact
- \+ *lemma* compact.is_closed

Modified src/topology/sequences.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* is_closed.is_complete
- \- *lemma* is_complete_of_is_closed

Modified src/topology/uniform_space/complete_separated.lean
- \- *lemma* is_closed_of_is_complete
- \+ *lemma* is_complete.is_closed

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-30 17:14:16](https://github.com/leanprover-community/mathlib/commit/b391563)
feat(algebra/lie_algebra): conjugation transformation for Lie algebras of skew-adjoint endomorphims, matrices ([#3229](https://github.com/leanprover-community/mathlib/pull/3229))
The two main results are the lemmas:
 * skew_adjoint_lie_subalgebra_equiv
 * skew_adjoint_matrices_lie_subalgebra_equiv
The latter is expected to be useful when defining the classical Lie algebras
of type B and D.
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* bilin_form.is_skew_adjoint_bracket
- \- *def* bilin_form.skew_adjoint_lie_subalgebra
- \- *def* bilin_form.skew_adjoint_matrices_lie_embedding
- \- *def* bilin_form.skew_adjoint_matrices_lie_subalgebra
- \+ *lemma* lie_algebra.equiv.apply_symm_apply
- \+ *lemma* lie_algebra.equiv.coe_to_lie_equiv
- \+ *lemma* lie_algebra.equiv.coe_to_linear_equiv
- \+ *def* lie_algebra.equiv.of_eq
- \+ *lemma* lie_algebra.equiv.of_eq_apply
- \+ *lemma* lie_algebra.equiv.of_injective_apply
- \+ *def* lie_algebra.equiv.of_subalgebra
- \+ *lemma* lie_algebra.equiv.of_subalgebra_apply
- \+ *def* lie_algebra.equiv.of_subalgebras
- \+ *lemma* lie_algebra.equiv.of_subalgebras_apply
- \+ *lemma* lie_algebra.equiv.of_subalgebras_symm_apply
- \+ *lemma* lie_algebra.equiv.one_apply
- \+ *lemma* lie_algebra.equiv.refl_apply
- \+ *lemma* lie_algebra.equiv.symm_apply_apply
- \+ *lemma* lie_algebra.equiv.symm_symm
- \+ *lemma* lie_algebra.equiv.symm_trans_apply
- \+ *lemma* lie_algebra.equiv.trans_apply
- \+/\- *def* lie_algebra.morphism.range
- \+ *lemma* lie_algebra.morphism.range_bracket
- \+ *lemma* lie_equiv_matrix'_apply
- \+ *lemma* lie_equiv_matrix'_symm_apply
- \+ *lemma* lie_subalgebra.coe_bracket
- \+ *lemma* lie_subalgebra.ext
- \+ *lemma* lie_subalgebra.ext_iff
- \+/\- *def* lie_subalgebra.incl
- \+ *def* lie_subalgebra.map
- \+ *lemma* lie_subalgebra.mem_coe'
- \+ *lemma* lie_subalgebra.mem_coe
- \+ *lemma* lie_subalgebra.mem_map_submodule
- \+ *def* linear_equiv.lie_conj
- \+ *lemma* linear_equiv.lie_conj_apply
- \+ *lemma* linear_equiv.lie_conj_symm
- \+ *lemma* matrix.is_skew_adjoint_bracket
- \+ *lemma* matrix.lie_conj_apply
- \+ *lemma* matrix.lie_conj_symm_apply
- \+ *lemma* matrix.lie_transpose
- \+ *def* skew_adjoint_lie_subalgebra
- \+ *def* skew_adjoint_lie_subalgebra_equiv
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_apply
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_symm_apply
- \+ *def* skew_adjoint_matrices_lie_subalgebra
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_apply

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.transpose_sub

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_equiv.conj_apply
- \+ *lemma* linear_equiv.conj_comp
- \+ *lemma* linear_equiv.conj_trans
- \+ *theorem* linear_equiv.of_injective_apply
- \+ *def* linear_equiv.of_submodule
- \+ *lemma* linear_equiv.of_submodule_apply
- \+ *lemma* linear_equiv.of_submodule_symm_apply
- \+ *def* linear_equiv.of_submodules
- \+ *lemma* linear_equiv.of_submodules_apply
- \+ *lemma* linear_equiv.of_submodules_symm_apply
- \+ *lemma* linear_equiv.symm_conj_apply
- \+ *def* linear_map.dom_restrict
- \+ *lemma* linear_map.dom_restrict_apply
- \+ *lemma* submodule.mem_map_equiv

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.comp_injective
- \+ *lemma* bilin_form.is_pair_self_adjoint_equiv
- \+ *lemma* bilin_form.mem_is_pair_self_adjoint_submodule
- \+ *lemma* matrix.is_adjoint_pair_equiv
- \+ *lemma* matrix.to_bilin_form_comp
- \+/\- *lemma* matrix_is_adjoint_pair_bilin_form
- \+ *lemma* mem_self_adjoint_matrices_submodule
- \+ *lemma* mem_skew_adjoint_matrices_submodule
- \- *def* pair_self_adjoint_matrices_linear_embedding
- \- *lemma* pair_self_adjoint_matrices_linear_embedding_apply
- \- *lemma* pair_self_adjoint_matrices_linear_embedding_injective

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.diagonal_comp_std_basis
- \+/\- *lemma* matrix.diagonal_to_lin
- \+/\- *lemma* matrix.proj_diagonal
- \+ *def* matrix.to_linear_equiv
- \+ *lemma* matrix.to_linear_equiv_apply
- \+ *lemma* matrix.to_linear_equiv_symm_apply

Modified test/noncomm_ring.lean




## [2020-06-30 16:18:08](https://github.com/leanprover-community/mathlib/commit/ea961f7)
chore(ring_theory/polynomial): move `ring_theory.polynomial` to `ring_theory.polynomial.basic` ([#3248](https://github.com/leanprover-community/mathlib/pull/3248))
This PR is the intersection of [#3223](https://github.com/leanprover-community/mathlib/pull/3223) and [#3241](https://github.com/leanprover-community/mathlib/pull/3241), allowing them to be merged in either order.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/where.20should.20these.20definitions.20live.3F
#### Estimated changes
Renamed src/ring_theory/polynomial.lean to src/ring_theory/polynomial/basic.lean


Added src/ring_theory/polynomial/default.lean




## [2020-06-30 14:58:52](https://github.com/leanprover-community/mathlib/commit/9524dee)
feat(topology): real.image_Icc ([#3224](https://github.com/leanprover-community/mathlib/pull/3224))
The image of a segment under a real-valued continuous function is a segment.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \- *lemma* has_Inf_to_nonempty
- \- *lemma* has_Sup_to_nonempty

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* subset_Icc_cInf_cSup

Modified src/topology/algebra/ordered.lean
- \+ *lemma* compact.Inf_mem
- \+ *lemma* compact.Sup_mem
- \+ *lemma* compact.exists_Inf_image_eq
- \+ *lemma* compact.exists_Sup_image_eq
- \+ *lemma* compact.exists_is_glb
- \+ *lemma* compact.exists_is_greatest
- \+ *lemma* compact.exists_is_least
- \+ *lemma* compact.exists_is_lub
- \+ *lemma* compact.is_glb_Inf
- \+ *lemma* compact.is_greatest_Sup
- \+ *lemma* compact.is_least_Inf
- \+ *lemma* compact.is_lub_Sup
- \+ *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \+ *lemma* eq_Icc_of_connected_compact
- \+/\- *lemma* is_closed.cInf_mem
- \+/\- *lemma* is_closed.cSup_mem
- \+ *lemma* is_connected.Icc_subset

Modified src/topology/instances/real.lean
- \+ *lemma* real.image_Icc



## [2020-06-30 12:42:26](https://github.com/leanprover-community/mathlib/commit/1bc6eba)
fix(tactic/interactive_expr): show let-values in tactic state widget ([#3228](https://github.com/leanprover-community/mathlib/pull/3228))
Fixes the missing let-values in the tactic state widget:
![let_widget](https://user-images.githubusercontent.com/313929/86048315-9d740d80-ba50-11ea-9a8c-09c853687343.png)
#### Estimated changes
Modified src/tactic/interactive_expr.lean




## [2020-06-30 11:46:05](https://github.com/leanprover-community/mathlib/commit/b82ed0c)
fix(tactic/apply_fun): beta reduction was too aggressive ([#3214](https://github.com/leanprover-community/mathlib/pull/3214))
The beta reduction performed by `apply_fun` was previously too aggressive -- in particular it was unfolding `A * B` to `A.mul B` when `A` and `B` are matrices. 
This fix avoids using `dsimp`, and instead calls `head_beta` separately on the left and right sides of the new hypothesis.
#### Estimated changes
Modified src/tactic/apply_fun.lean


Modified test/apply_fun.lean




## [2020-06-30 09:50:40](https://github.com/leanprover-community/mathlib/commit/6d0f40a)
chore(topology/algebra/ordered): use `continuous_at`, rename ([#3231](https://github.com/leanprover-community/mathlib/pull/3231))
* rename `Sup_mem_of_is_closed` and `Inf_mem_of_is_closed` to
  `is_closed.Sup_mem` and `is_closed.Inf_mem`, similarly with
  `cSup` and `cInf`;
* make `Sup_of_continuous` etc take `continuous_at` instead
  of `continuous`, rename to `Sup_of_continuous_at_of_monotone` etc,
  similarly with `cSup`/`cInf`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* Inf_mem_closure
- \- *lemma* Inf_mem_of_is_closed
- \- *lemma* Inf_of_continuous'
- \- *lemma* Inf_of_continuous
- \+/\- *lemma* Sup_mem_closure
- \- *lemma* Sup_mem_of_is_closed
- \- *lemma* Sup_of_continuous'
- \- *lemma* Sup_of_continuous
- \- *lemma* cInf_mem_of_is_closed
- \- *lemma* cInf_of_cInf_of_monotone_of_continuous
- \- *lemma* cSup_mem_of_is_closed
- \- *lemma* cSup_of_cSup_of_monotone_of_continuous
- \- *lemma* cinfi_of_cinfi_of_monotone_of_continuous
- \- *lemma* csupr_of_csupr_of_monotone_of_continuous
- \- *lemma* infi_of_continuous'
- \- *lemma* infi_of_continuous
- \+ *lemma* is_closed.Inf_mem
- \+ *lemma* is_closed.Sup_mem
- \+ *lemma* is_closed.cInf_mem
- \+ *lemma* is_closed.cSup_mem
- \+ *lemma* map_Inf_of_continuous_at_of_monotone'
- \+ *lemma* map_Inf_of_continuous_at_of_monotone
- \+ *lemma* map_Sup_of_continuous_at_of_monotone'
- \+ *lemma* map_Sup_of_continuous_at_of_monotone
- \+ *lemma* map_cInf_of_continuous_at_of_monotone
- \+ *lemma* map_cSup_of_continuous_at_of_monotone
- \+ *lemma* map_cinfi_of_continuous_at_of_monotone
- \+ *lemma* map_csupr_of_continuous_at_of_monotone
- \+ *lemma* map_infi_of_continuous_at_of_monotone'
- \+ *lemma* map_infi_of_continuous_at_of_monotone
- \+ *lemma* map_supr_of_continuous_at_of_monotone'
- \+ *lemma* map_supr_of_continuous_at_of_monotone
- \- *lemma* supr_of_continuous'
- \- *lemma* supr_of_continuous

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.infi_mul_left
- \+ *lemma* ennreal.infi_mul_right

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean
- \+/\- *def* Gromov_Hausdorff.HD
- \+/\- *lemma* Gromov_Hausdorff.HD_below_aux1
- \+/\- *lemma* Gromov_Hausdorff.HD_below_aux2
- \+/\- *lemma* Gromov_Hausdorff.HD_candidates_b_dist_le

Modified src/topology/metric_space/hausdorff_distance.lean




## [2020-06-30 08:06:04](https://github.com/leanprover-community/mathlib/commit/a143c38)
refactor(linear_algebra/affine_space): allow empty affine subspaces ([#3219](https://github.com/leanprover-community/mathlib/pull/3219))
When definitions of affine spaces and subspaces were added in [#2816](https://github.com/leanprover-community/mathlib/pull/2816),
there was some discussion of whether an affine subspace should be
allowed to be empty.
After further consideration of what lemmas need to be added to fill
out the interface for affine subspaces, I've concluded that it does
indeed make sense to allow empty affine subspaces, with `nonempty`
hypotheses then added for those results that need them, to avoid
artificial `nonempty` hypotheses for other results on affine spans and
intersections of affine subspaces that don't depend on any way on
affine subspaces being nonempty and can be more cleanly stated if they
can be empty.
Thus, change the definition to allow affine subspaces to be empty and
remove the bundled `direction`.  The new definition of `direction` (as
the `vector_span` of the points in the subspace, i.e. the
`submodule.span` of the `vsub_set` of the points) is the zero
submodule for both empty affine subspaces and for those consisting of
a single point (and it's proved that in the nonempty case it contains
exactly the pairwise subtractions of points in the affine subspace).
This doesn't generally add new lemmas beyond those used in reproving
existing results (including what were previously the `add` and `sub`
axioms for affine subspaces) with the new definitions.  It also
doesn't add the complete lattice structure for affine subspaces, just
helps enable adding it later.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.vsub_mem_vsub_set
- \+ *lemma* add_torsor.vsub_set_mono

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_space.subset_span_points
- \+ *lemma* affine_space.vsub_mem_vector_span
- \+ *lemma* affine_space.vsub_set_subset_vector_span
- \+/\- *def* affine_span
- \- *lemma* affine_span_coe
- \- *lemma* affine_span_mem
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set
- \+ *def* affine_subspace.direction
- \+ *lemma* affine_subspace.direction_eq_vector_span
- \+ *lemma* affine_subspace.direction_mk'
- \- *lemma* affine_subspace.direction_mk_of_point_of_direction
- \+ *def* affine_subspace.direction_of_nonempty
- \+ *lemma* affine_subspace.direction_of_nonempty_eq_direction
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub
- \- *lemma* affine_subspace.mem_mk_of_point_of_direction
- \+ *def* affine_subspace.mk'
- \+ *lemma* affine_subspace.mk'_eq
- \+ *lemma* affine_subspace.mk'_nonempty
- \- *def* affine_subspace.mk_of_point_of_direction
- \- *lemma* affine_subspace.mk_of_point_of_direction_eq
- \+ *lemma* affine_subspace.self_mem_mk'
- \+ *lemma* affine_subspace.vadd_mem_mk'
- \+ *lemma* affine_subspace.vadd_mem_of_mem_direction
- \+ *lemma* affine_subspace.vsub_mem_direction
- \+ *lemma* coe_affine_span
- \+ *lemma* direction_affine_span
- \+ *lemma* mem_affine_span



## [2020-06-30 05:20:57](https://github.com/leanprover-community/mathlib/commit/e250eb4)
feat(category/schur): a small corollary of the baby schur's lemma ([#3239](https://github.com/leanprover-community/mathlib/pull/3239))
#### Estimated changes
Modified src/category_theory/schur.lean
- \+ *def* category_theory.is_iso_equiv_nonzero

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.id_nonzero



## [2020-06-30 05:20:54](https://github.com/leanprover-community/mathlib/commit/d788d4b)
chore(data/set/intervals): split `I??_union_I??_eq_I??` ([#3237](https://github.com/leanprover-community/mathlib/pull/3237))
For each lemma `I??_union_I??_eq_I??` add a lemma
`I??_subset_I??_union_I??` with no assumptions.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_subset_Icc_union_Icc
- \+ *lemma* set.Icc_subset_Icc_union_Ioc
- \+ *lemma* set.Icc_subset_Ico_union_Icc
- \+/\- *lemma* set.Icc_union_Icc_eq_Icc
- \+ *lemma* set.Icc_union_Ici_eq_Ici
- \- *lemma* set.Icc_union_Ici_eq_Ioi
- \+/\- *lemma* set.Icc_union_Ico_eq_Ico
- \+/\- *lemma* set.Icc_union_Ioc_eq_Icc
- \+ *lemma* set.Icc_union_Ioi_eq_Ici
- \- *lemma* set.Icc_union_Ioi_eq_Ioi
- \+/\- *lemma* set.Icc_union_Ioo_eq_Ico
- \+ *lemma* set.Ici_subset_Icc_union_Ici
- \+ *lemma* set.Ici_subset_Icc_union_Ioi
- \+ *lemma* set.Ici_subset_Ico_union_Ici
- \+ *lemma* set.Ico_subset_Icc_union_Ico
- \+ *lemma* set.Ico_subset_Icc_union_Ioo
- \+ *lemma* set.Ico_subset_Ico_union_Ico
- \+/\- *lemma* set.Ico_union_Icc_eq_Icc
- \+ *lemma* set.Ico_union_Ici_eq_Ici
- \- *lemma* set.Ico_union_Ici_eq_Ioi
- \+/\- *lemma* set.Ico_union_Ico_eq_Ico
- \+ *lemma* set.Iic_subset_Iic_union_Icc
- \+ *lemma* set.Iic_subset_Iic_union_Ioc
- \+ *lemma* set.Iic_subset_Iio_union_Icc
- \+ *lemma* set.Iio_subset_Iic_union_Ico
- \+ *lemma* set.Iio_subset_Iic_union_Ioo
- \+ *lemma* set.Iio_subset_Iio_union_Ico
- \+ *lemma* set.Ioc_subset_Ioc_union_Icc
- \+ *lemma* set.Ioc_subset_Ioc_union_Ioc
- \+ *lemma* set.Ioc_subset_Ioo_union_Icc
- \+/\- *lemma* set.Ioc_union_Icc_eq_Ioc
- \+/\- *lemma* set.Ioc_union_Ico_eq_Ioo
- \+/\- *lemma* set.Ioc_union_Ioc_eq_Ioc
- \+/\- *lemma* set.Ioc_union_Ioo_eq_Ioo
- \+ *lemma* set.Ioi_subset_Ioc_union_Ici
- \+ *lemma* set.Ioi_subset_Ioc_union_Ioi
- \+ *lemma* set.Ioi_subset_Ioo_union_Ici
- \+ *lemma* set.Ioo_subset_Ioc_union_Ico
- \+ *lemma* set.Ioo_subset_Ioc_union_Ioo
- \+ *lemma* set.Ioo_subset_Ioo_union_Ici
- \+/\- *lemma* set.Ioo_union_Icc_eq_Ioc
- \+/\- *lemma* set.Ioo_union_Ico_eq_Ioo



## [2020-06-30 05:20:51](https://github.com/leanprover-community/mathlib/commit/af53c9d)
chore(algebra/ring): move some classes to `group_with_zero` ([#3232](https://github.com/leanprover-community/mathlib/pull/3232))
Move `nonzero`, `mul_zero_class` and `no_zero_divisors` to
`group_with_zero`: these classes don't need `(+)`.
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/algebra/group_with_zero.lean
- \+ *theorem* commute.zero_left
- \+ *theorem* commute.zero_right
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *theorem* mul_eq_zero
- \+ *theorem* mul_eq_zero_comm
- \+ *theorem* mul_ne_zero
- \+ *theorem* mul_ne_zero_comm
- \+ *theorem* mul_ne_zero_iff
- \+ *lemma* mul_self_eq_zero
- \+ *lemma* mul_zero
- \+ *lemma* one_ne_zero
- \+ *lemma* semiconj_by.zero_left
- \+ *lemma* semiconj_by.zero_right
- \+ *theorem* zero_eq_mul
- \+ *lemma* zero_eq_mul_self
- \+ *lemma* zero_mul
- \+ *lemma* zero_ne_one

Modified src/algebra/ring.lean
- \- *theorem* commute.zero_left
- \- *theorem* commute.zero_right
- \- *lemma* eq_zero_of_mul_self_eq_zero
- \- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* left_distrib
- \- *theorem* mul_eq_zero
- \- *theorem* mul_eq_zero_comm
- \- *theorem* mul_ne_zero
- \- *theorem* mul_ne_zero_comm
- \- *theorem* mul_ne_zero_iff
- \- *lemma* mul_self_eq_zero
- \- *lemma* mul_zero
- \- *lemma* one_ne_zero
- \+/\- *lemma* right_distrib
- \- *lemma* semiconj_by.zero_left
- \- *lemma* semiconj_by.zero_right
- \- *theorem* zero_eq_mul
- \- *lemma* zero_eq_mul_self
- \- *lemma* zero_mul
- \- *lemma* zero_ne_one

Modified src/data/real/hyperreal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean




## [2020-06-30 05:20:45](https://github.com/leanprover-community/mathlib/commit/da481e7)
chore(data/polynomial): partial move from is_ring_hom to ring_hom ([#3213](https://github.com/leanprover-community/mathlib/pull/3213))
This does not attempt to do a complete refactor of `polynomial.lean` and `mv_polynomial.lean` to remove use of `is_ring_hom`, but only to fix `eval₂` which we need for the current work on Cayley-Hamilton.
Having struggled with these two files for the last few days, I'm keen to get them cleaned up, so I'll promise to return to this more thoroughly in a later PR.
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+/\- *def* mv_polynomial.C

Modified src/data/polynomial.lean
- \+/\- *def* polynomial.eval
- \+ *lemma* polynomial.eval₂_X_pow
- \+/\- *lemma* polynomial.eval₂_comp
- \+/\- *lemma* polynomial.eval₂_hom
- \+/\- *lemma* polynomial.eval₂_map
- \+ *lemma* polynomial.eval₂_monomial
- \+/\- *lemma* polynomial.eval₂_neg
- \+/\- *lemma* polynomial.eval₂_pow
- \+/\- *lemma* polynomial.eval₂_sub
- \+/\- *lemma* polynomial.hom_eval₂
- \+/\- *def* polynomial.map

Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial.lean




## [2020-06-30 04:15:21](https://github.com/leanprover-community/mathlib/commit/38904ac)
feat(data/fintype/basic): card_eq_zero_equiv_equiv_pempty ([#3238](https://github.com/leanprover-community/mathlib/pull/3238))
Adds a constructive equivalence `α ≃ pempty.{v+1}` given `fintype.card α = 0`, which I think wasn't available previously.
I would have stated this as an `iff`, but as the right hand side is data is an `equiv` itself.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* fintype.card_eq_zero_equiv_equiv_pempty



## [2020-06-30 04:15:19](https://github.com/leanprover-community/mathlib/commit/1588d81)
feat(category_theory): remove nearly all universe annotations ([#3221](https://github.com/leanprover-community/mathlib/pull/3221))
Due to some recent changes to mathlib (does someone know the relevant versions/commits?) most of the universe annotations `.{v}` and `include 𝒞` statements that were previously needed in the category_theory library are no longer necessary.
This PR removes them!
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+/\- *def* category_theory.iso.to_alg_equiv

Modified src/algebra/category/CommRing/adjunctions.lean
- \+/\- *def* CommRing.free

Modified src/algebra/category/CommRing/basic.lean
- \+/\- *def* category_theory.iso.CommRing_iso_to_ring_equiv
- \+/\- *def* category_theory.iso.Ring_iso_to_ring_equiv

Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* CommRing.CommRing_has_limits.limit
- \+/\- *def* CommRing.CommRing_has_limits.limit_is_limit
- \+/\- *def* CommRing.limit_π_ring_hom

Modified src/algebra/category/Group/adjunctions.lean
- \+/\- *def* AddCommGroup.free

Modified src/algebra/category/Group/basic.lean
- \+/\- *def* category_theory.iso.CommGroup_iso_to_mul_equiv
- \+/\- *def* category_theory.iso.Group_iso_to_mul_equiv

Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Group/limits.lean
- \+/\- *def* AddCommGroup.AddCommGroup_has_limits.limit
- \+/\- *def* AddCommGroup.AddCommGroup_has_limits.limit_is_limit
- \+/\- *def* AddCommGroup.limit_π_add_monoid_hom

Modified src/algebra/category/Group/preadditive.lean


Modified src/algebra/category/Group/zero.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* category_theory.iso.to_linear_equiv

Modified src/algebra/category/Module/monoidal.lean
- \+/\- *lemma* Module.monoidal_category.left_unitor_hom

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* category_theory.iso.CommMon_iso_to_mul_equiv
- \+/\- *def* category_theory.iso.Mon_iso_to_mul_equiv

Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/homology/chain_complex.lean
- \+/\- *lemma* chain_complex.d_squared
- \+/\- *lemma* cochain_complex.d_squared

Modified src/algebra/homology/homology.lean
- \+/\- *def* cochain_complex.cohomology_functor
- \+/\- *def* cochain_complex.cohomology_map
- \+/\- *lemma* cochain_complex.cohomology_map_comp
- \+/\- *lemma* cochain_complex.cohomology_map_condition
- \+/\- *lemma* cochain_complex.cohomology_map_id
- \+/\- *abbreviation* cochain_complex.image_map
- \+/\- *lemma* cochain_complex.image_map_ι
- \+/\- *lemma* cochain_complex.induced_maps_commute
- \+/\- *def* cochain_complex.kernel_functor
- \+/\- *lemma* cochain_complex.kernel_map_comp
- \+/\- *lemma* cochain_complex.kernel_map_id

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.as_coe
- \+/\- *def* algebraic_geometry.PresheafedSpace.comp
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.comp_c_app
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.comp_coe
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.ext
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.f_as_coe
- \+/\- *def* algebraic_geometry.PresheafedSpace.forget
- \+/\- *structure* algebraic_geometry.PresheafedSpace.hom
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.hom_mk_coe
- \+/\- *def* algebraic_geometry.PresheafedSpace.id
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_c
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_c_app
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_coe
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.id_coe_fn
- \+/\- *def* category_theory.functor.map_presheaf
- \+/\- *lemma* category_theory.functor.map_presheaf_map_c
- \+/\- *lemma* category_theory.functor.map_presheaf_map_f
- \+/\- *lemma* category_theory.functor.map_presheaf_obj_X
- \+/\- *lemma* category_theory.functor.map_presheaf_obj_𝒪

Modified src/algebraic_geometry/stalks.lean
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.comp
- \+/\- *lemma* algebraic_geometry.PresheafedSpace.stalk_map.id
- \+/\- *def* algebraic_geometry.PresheafedSpace.stalk_map

Modified src/category_theory/abelian/basic.lean
- \+/\- *def* category_theory.abelian.has_pullbacks
- \+/\- *def* category_theory.abelian.has_pushouts

Modified src/category_theory/action.lean


Modified src/category_theory/category/Rel.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* category_theory.binary_product_exponentiable
- \+/\- *abbreviation* category_theory.cartesian_closed
- \+/\- *abbreviation* category_theory.exponentiable
- \+/\- *def* category_theory.mul_zero
- \+/\- *def* category_theory.pow_zero
- \+/\- *def* category_theory.prod_coprod_distrib
- \+/\- *def* category_theory.terminal_exponentiable
- \+/\- *def* category_theory.zero_mul

Modified src/category_theory/conj.lean
- \+/\- *lemma* category_theory.iso.refl_conj

Modified src/category_theory/differential_object.lean
- \+/\- *lemma* category_theory.differential_object.comp_f
- \+/\- *def* category_theory.differential_object.forget
- \+/\- *def* category_theory.differential_object.hom.comp
- \+/\- *def* category_theory.differential_object.hom.id
- \+/\- *structure* category_theory.differential_object.hom
- \+/\- *lemma* category_theory.differential_object.id_f
- \+/\- *lemma* category_theory.differential_object.zero_f

Modified src/category_theory/elements.lean


Modified src/category_theory/endomorphism.lean
- \+/\- *def* category_theory.End

Modified src/category_theory/epi_mono.lean
- \+/\- *def* category_theory.retraction
- \+/\- *def* category_theory.section_

Modified src/category_theory/graded_object.lean
- \+/\- *lemma* category_theory.graded_object.zero_apply

Modified src/category_theory/groupoid.lean
- \+/\- *def* category_theory.groupoid.of_is_iso

Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* category_theory.limits.functor_category_is_colimit_cocone

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* category_theory.limits.colimit.pre_map'
- \+/\- *lemma* category_theory.limits.limit.map_pre'

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean
- \+/\- *def* category_theory.over.construct_products.over_binary_product_of_pullback
- \+/\- *def* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \+/\- *def* category_theory.over.construct_products.over_product_of_wide_pullback
- \+/\- *def* category_theory.over.construct_products.over_products_of_wide_pullbacks

Modified src/category_theory/limits/preserves.lean
- \+/\- *def* category_theory.limits.preserves_colimit_iso
- \+/\- *def* category_theory.limits.preserves_limit_iso

Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *abbreviation* category_theory.limits.coprod.map
- \+/\- *abbreviation* category_theory.limits.prod.map

Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* category_theory.limits.binary_bicone.to_cocone
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cocone_X
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cocone_ι_app_left
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cocone_ι_app_right
- \+/\- *def* category_theory.limits.binary_bicone.to_cone
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cone_X
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cone_π_app_left
- \+/\- *lemma* category_theory.limits.binary_bicone.to_cone_π_app_right
- \+/\- *abbreviation* category_theory.limits.biprod.desc
- \+/\- *abbreviation* category_theory.limits.biprod.fst
- \+/\- *lemma* category_theory.limits.biprod.hom_ext'
- \+/\- *lemma* category_theory.limits.biprod.hom_ext
- \+/\- *abbreviation* category_theory.limits.biprod.inl
- \+/\- *lemma* category_theory.limits.biprod.inl_fst
- \+/\- *lemma* category_theory.limits.biprod.inl_map
- \+/\- *lemma* category_theory.limits.biprod.inl_snd
- \+/\- *abbreviation* category_theory.limits.biprod.inr
- \+/\- *lemma* category_theory.limits.biprod.inr_fst
- \+/\- *lemma* category_theory.limits.biprod.inr_map
- \+/\- *lemma* category_theory.limits.biprod.inr_snd
- \+/\- *abbreviation* category_theory.limits.biprod.lift
- \+/\- *abbreviation* category_theory.limits.biprod.map'
- \+/\- *abbreviation* category_theory.limits.biprod.map
- \+/\- *lemma* category_theory.limits.biprod.map_eq
- \+/\- *lemma* category_theory.limits.biprod.map_eq_map'
- \+/\- *lemma* category_theory.limits.biprod.map_fst
- \+/\- *def* category_theory.limits.biprod.map_iso
- \+/\- *lemma* category_theory.limits.biprod.map_snd
- \+/\- *abbreviation* category_theory.limits.biprod.snd
- \+/\- *abbreviation* category_theory.limits.biprod
- \+/\- *def* category_theory.limits.biprod_iso
- \+/\- *lemma* category_theory.limits.biproduct.hom_ext'
- \+/\- *lemma* category_theory.limits.biproduct.hom_ext
- \+/\- *lemma* category_theory.limits.biproduct.inl_map
- \+/\- *abbreviation* category_theory.limits.biproduct.map'
- \+/\- *abbreviation* category_theory.limits.biproduct.map
- \+/\- *lemma* category_theory.limits.biproduct.map_eq
- \+/\- *lemma* category_theory.limits.biproduct.map_eq_map'
- \+/\- *def* category_theory.limits.has_binary_biproduct.of_has_binary_coproduct
- \+/\- *def* category_theory.limits.has_binary_biproduct.of_has_binary_product
- \+/\- *def* category_theory.limits.has_binary_biproducts.of_has_binary_coproducts
- \+/\- *def* category_theory.limits.has_binary_biproducts.of_has_binary_products
- \+/\- *def* category_theory.limits.has_binary_biproducts_of_finite_biproducts
- \+/\- *def* category_theory.limits.has_biproduct.of_has_coproduct
- \+/\- *def* category_theory.limits.has_biproduct.of_has_product

Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* category_theory.limits.cofork.of_cocone_ι
- \+/\- *def* category_theory.limits.diagram_iso_parallel_pair
- \+/\- *lemma* category_theory.limits.fork.of_cone_π
- \+/\- *def* category_theory.limits.has_coequalizers_of_has_finite_colimits
- \+/\- *def* category_theory.limits.has_equalizers_of_has_finite_limits
- \+/\- *def* category_theory.limits.parallel_pair
- \+/\- *lemma* category_theory.limits.walking_parallel_pair_hom_id

Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/images.lean
- \+/\- *structure* category_theory.limits.strong_epi_mono_factorisation

Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.has_cokernels_of_has_finite_colimits
- \+/\- *def* category_theory.limits.has_kernels_of_has_finite_limits

Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *def* category_theory.limits.cospan
- \+/\- *def* category_theory.limits.has_pullbacks_of_has_finite_limits
- \+/\- *def* category_theory.limits.has_pushouts_of_has_finite_colimits
- \+/\- *def* category_theory.limits.span

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* category_theory.limits.has_initial_of_unique
- \+/\- *def* category_theory.limits.has_terminal_of_unique
- \+/\- *abbreviation* category_theory.limits.initial.to
- \+/\- *abbreviation* category_theory.limits.initial
- \+/\- *abbreviation* category_theory.limits.terminal.from
- \+/\- *abbreviation* category_theory.limits.terminal

Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+/\- *def* has_finite_wide_pullbacks_of_has_finite_limits
- \+/\- *def* has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/zero.lean
- \+/\- *lemma* category_theory.limits.has_zero_morphisms.ext
- \+/\- *def* category_theory.limits.has_zero_object.has_initial
- \+/\- *def* category_theory.limits.has_zero_object.has_terminal
- \+/\- *def* category_theory.limits.has_zero_object.zero_morphisms_of_zero_object

Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean
- \+/\- *structure* category_theory.comonad.coalgebra
- \+/\- *structure* category_theory.monad.algebra

Modified src/category_theory/monad/limits.lean
- \+/\- *def* category_theory.has_limits_of_reflective
- \+/\- *def* category_theory.monadic_creates_limits

Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+/\- *def* category_theory.monoidal_of_has_finite_coproducts
- \+/\- *def* category_theory.monoidal_of_has_finite_products

Modified src/category_theory/preadditive.lean
- \+/\- *def* category_theory.preadditive.has_coequalizers_of_has_cokernels
- \+/\- *def* category_theory.preadditive.has_equalizers_of_has_kernels

Modified src/category_theory/schur.lean
- \+/\- *def* category_theory.is_iso_of_hom_simple

Modified src/category_theory/shift.lean
- \+/\- *def* category_theory.shift

Modified src/category_theory/simple.lean
- \+/\- *def* category_theory.is_iso_of_epi_of_nonzero
- \+/\- *def* category_theory.is_iso_of_mono_of_nonzero
- \+/\- *lemma* category_theory.simple.ext
- \+/\- *def* category_theory.simple_of_cosimple
- \+/\- *lemma* category_theory.zero_not_simple



## [2020-06-30 03:05:21](https://github.com/leanprover-community/mathlib/commit/056a72a)
perf(linarith): don't repeat nonneg proofs for nat-to-int casts ([#3226](https://github.com/leanprover-community/mathlib/pull/3226))
This performance issue showed up particularly when using `nlinarith` over `nat`s. Proofs that `(n : int) >= 0` were being repeated many times, which led to quadratic blowup in the `nlinarith` preprocessing.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* real.cos_le_cos_of_nonneg_of_le_pi
- \+/\- *lemma* real.cos_lt_cos_of_nonneg_of_le_pi
- \+/\- *lemma* real.cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+/\- *lemma* real.tan_lt_tan_of_lt_of_lt_pi_div_two
- \+/\- *lemma* real.tan_lt_tan_of_nonneg_of_lt_pi_div_two

Modified src/meta/rb_map.lean


Modified src/tactic/linarith/preprocessing.lean


Modified test/linarith.lean




## [2020-06-30 03:05:19](https://github.com/leanprover-community/mathlib/commit/791744b)
feat(analysis/normed_space/real_inner_product,geometry/euclidean): inner products of weighted subtractions ([#3203](https://github.com/leanprover-community/mathlib/pull/3203))
Express the inner product of two weighted sums, where the weights in
each sum add to 0, in terms of the norms of pairwise differences.
Thus, express inner products for vectors expressed in terms of
`weighted_vsub` and distances for points expressed in terms of
`affine_combination`.
This is a general form of the standard formula for a distance between
points expressed in terms of barycentric coordinates: if the
difference between the normalized barycentric coordinates (with
respect to triangle ABC) for two points is (x, y, z) then the squared
distance between them is -(a^2 yz + b^2 zx + c^2 xy).
Although some of the lemmas are given with the two vectors expressed
as sums over different indexed families of vectors or points (since
nothing in the statement or proof depends on them being the same), I
expect almost all uses will be in cases where the two indexed families
are the same and only the weights vary.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* inner_sum_smul_sum_smul_of_sum_eq_zero

Modified src/geometry/euclidean.lean
- \+ *lemma* euclidean_geometry.dist_affine_combination
- \+ *lemma* euclidean_geometry.inner_weighted_vsub

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* finset.weighted_vsub_apply



## [2020-06-30 01:43:20](https://github.com/leanprover-community/mathlib/commit/4fcd6fd)
chore(*): import expression widgets from core ([#3181](https://github.com/leanprover-community/mathlib/pull/3181))
With widgets, the rendering of the tactic state is implemented in pure Lean code.  I would like to move this part (temporarily) into mathlib to facilitate collaborative improvement and rapid iteration under a mature community review procedure.  (That is, I want other people to tweak it themselves without having to wait a week for the next Lean release to see the effect.)
I didn't need to change anything in the source code (except for adding some doc strings).  So it should be easy to copy it back to core if we want to.
There are no changes required to core for this PR.
#### Estimated changes
Modified src/tactic/core.lean


Added src/tactic/interactive_expr.lean




## [2020-06-30 00:37:07](https://github.com/leanprover-community/mathlib/commit/e8fd085)
chore(scripts): update nolints.txt ([#3234](https://github.com/leanprover-community/mathlib/pull/3234))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-29 19:03:51](https://github.com/leanprover-community/mathlib/commit/45904fb)
chore(*): change notation for `set.compl` ([#3212](https://github.com/leanprover-community/mathlib/pull/3212))
* introduce typeclass `has_compl` and notation `∁` for `has_compl.compl`
* use it instead of `has_neg` for `set` and `boolean_algebra`
#### Estimated changes
Modified src/algebra/punit_instances.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/analysis/filter.lean


Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.set.sum_compl_apply_inr

Modified src/data/indicator_function.lean
- \+/\- *lemma* set.indicator_compl

Modified src/data/pfun.lean
- \+/\- *lemma* pfun.compl_dom_subset_core
- \+/\- *lemma* pfun.core_eq
- \+/\- *lemma* pfun.core_res

Modified src/data/real/hyperreal.lean


Modified src/data/set/basic.lean
- \+/\- *theorem* set.compl_compl
- \+/\- *theorem* set.compl_empty
- \+/\- *lemma* set.compl_empty_iff
- \+/\- *theorem* set.compl_eq_univ_diff
- \+/\- *theorem* set.compl_image
- \+/\- *theorem* set.compl_inter
- \+/\- *theorem* set.compl_inter_self
- \+/\- *lemma* set.compl_set_of
- \+/\- *lemma* set.compl_singleton_eq
- \+/\- *theorem* set.compl_subset_comm
- \+/\- *lemma* set.compl_subset_compl
- \+/\- *theorem* set.compl_subset_iff_union
- \+/\- *theorem* set.compl_union
- \+/\- *theorem* set.compl_union_self
- \+/\- *theorem* set.compl_univ
- \+/\- *lemma* set.compl_univ_iff
- \+/\- *lemma* set.diff_compl
- \+/\- *theorem* set.diff_eq
- \- *theorem* set.fix_set_compl
- \+/\- *theorem* set.image_compl_eq
- \+/\- *theorem* set.image_compl_subset
- \+/\- *lemma* set.inter_compl_nonempty_iff
- \+/\- *theorem* set.inter_compl_self
- \+/\- *theorem* set.inter_eq_compl_compl_union_compl
- \+/\- *theorem* set.inter_subset
- \+/\- *theorem* set.mem_compl
- \+/\- *theorem* set.mem_compl_eq
- \+/\- *theorem* set.mem_compl_iff
- \+/\- *lemma* set.mem_compl_singleton_iff
- \+/\- *lemma* set.nonempty_compl
- \+/\- *theorem* set.not_mem_of_mem_compl
- \+/\- *theorem* set.preimage_compl
- \+/\- *theorem* set.subset_compl_comm
- \+/\- *theorem* set.subset_compl_iff_disjoint
- \+/\- *lemma* set.subset_compl_singleton_iff
- \+/\- *theorem* set.subset_image_compl
- \+/\- *theorem* set.union_compl_self
- \+/\- *theorem* set.union_eq_compl_compl_inter_compl

Modified src/data/set/disjointed.lean
- \+/\- *def* set.disjointed

Modified src/data/set/enumerate.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.compl_Ici
- \+/\- *lemma* set.compl_Iic
- \+/\- *lemma* set.compl_Iio
- \+/\- *lemma* set.compl_Ioi

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.Inter_eq_comp_Union_comp
- \+/\- *theorem* set.Union_eq_comp_Inter_comp
- \+/\- *theorem* set.compl_Inter
- \+/\- *theorem* set.compl_Union
- \+/\- *theorem* set.compl_bInter
- \+/\- *theorem* set.compl_bUnion
- \+/\- *theorem* set.disjoint_compl
- \- *theorem* set.sub_eq_diff

Modified src/linear_algebra/matrix.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.compl
- \+/\- *lemma* is_measurable.compl_iff
- \+/\- *lemma* is_measurable.of_compl
- \- *lemma* is_measurable.sub
- \+/\- *lemma* measurable_space.dynkin_system.has_compl_iff

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.mem_ae_iff

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/order/boolean_algebra.lean
- \- *theorem* boolean_algebra.sub_le_sub
- \+/\- *theorem* compl_bot
- \+/\- *theorem* compl_compl'
- \+/\- *theorem* compl_inf
- \+/\- *theorem* compl_inf_eq_bot
- \+/\- *theorem* compl_inj_iff
- \+/\- *theorem* compl_injective
- \+/\- *theorem* compl_le_compl
- \+/\- *theorem* compl_le_compl_iff_le
- \+/\- *theorem* compl_le_iff_compl_le
- \+/\- *theorem* compl_le_of_compl_le
- \+/\- *theorem* compl_sup
- \+/\- *theorem* compl_sup_eq_top
- \+/\- *theorem* compl_top
- \+/\- *theorem* compl_unique
- \+/\- *theorem* inf_compl_eq_bot
- \+ *theorem* is_compl.compl_eq
- \- *theorem* is_compl.neg_eq
- \+ *theorem* is_compl_compl
- \- *theorem* is_compl_neg
- \+/\- *theorem* le_compl_of_le_compl
- \+ *theorem* sdiff_eq
- \+ *theorem* sdiff_eq_left
- \+ *theorem* sdiff_le_sdiff
- \- *theorem* sub_eq
- \- *theorem* sub_eq_left
- \+/\- *theorem* sup_compl_eq_top
- \+ *theorem* sup_sdiff_same
- \- *theorem* sup_sub_same

Modified src/order/complete_boolean_algebra.lean
- \+/\- *theorem* compl_Inf
- \+/\- *theorem* compl_Sup
- \+/\- *theorem* compl_infi
- \+/\- *theorem* compl_supr

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.inf_principal_eq_bot
- \+/\- *lemma* filter.is_compl_principal
- \+/\- *lemma* filter.mem_sets_of_eq_bot

Modified src/order/filter/cofinite.lean
- \+/\- *lemma* filter.mem_cofinite

Modified src/order/filter/ultrafilter.lean
- \+/\- *theorem* filter.mem_hyperfilter_of_finite_compl

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.mk_sum_compl

Modified src/set_theory/ordinal.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+/\- *lemma* closure_compl
- \+/\- *lemma* closure_diff
- \+/\- *lemma* closure_eq_compl_interior_compl
- \+/\- *lemma* frontier_compl
- \+/\- *lemma* interior_compl
- \+/\- *def* is_closed
- \+/\- *lemma* is_closed_compl_iff
- \+/\- *lemma* is_open_compl_iff

Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/order.lean


Modified src/topology/separation.lean
- \+/\- *lemma* compl_singleton_mem_nhds

Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean
- \+/\- *theorem* is_clopen_compl
- \+/\- *theorem* is_clopen_compl_iff
- \+/\- *theorem* is_clopen_diff

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compact_separated.lean


Modified src/topology/uniform_space/separation.lean




## [2020-06-29 16:12:00](https://github.com/leanprover-community/mathlib/commit/d3006ba)
chore(init_/): remove this directory ([#3227](https://github.com/leanprover-community/mathlib/pull/3227))
* remove `init_/algebra`;
* move `init_/data/nat` to `data/nat/basic`;
* move `init_/data/int` to `data/int/basic`.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *theorem* int.abs_eq_nat_abs
- \+ *theorem* int.nat_abs_abs
- \+ *theorem* int.sign_mul_abs

Modified src/data/nat/basic.lean
- \+ *theorem* nat.eq_of_mul_eq_mul_right
- \+ *theorem* nat.le_mul_self
- \+ *theorem* nat.mul_self_le_mul_self
- \+ *theorem* nat.mul_self_le_mul_self_iff
- \+ *theorem* nat.mul_self_lt_mul_self
- \+ *theorem* nat.mul_self_lt_mul_self_iff
- \+ *theorem* nat.one_add

Modified src/data/nat/sqrt.lean


Deleted src/init_/algebra/default.lean


Deleted src/init_/algebra/norm_num.lean
- \- *def* norm_num.add1
- \- *lemma* norm_num.add1_bit0
- \- *lemma* norm_num.add1_bit1
- \- *lemma* norm_num.add1_bit1_helper
- \- *lemma* norm_num.add1_one
- \- *lemma* norm_num.add1_zero
- \- *lemma* norm_num.add_comm_four
- \- *lemma* norm_num.add_comm_middle
- \- *lemma* norm_num.add_div_helper
- \- *lemma* norm_num.bin_add_zero
- \- *lemma* norm_num.bin_zero_add
- \- *lemma* norm_num.bit0_add_bit0
- \- *lemma* norm_num.bit0_add_bit0_helper
- \- *lemma* norm_num.bit0_add_bit1
- \- *lemma* norm_num.bit0_add_bit1_helper
- \- *lemma* norm_num.bit0_add_one
- \- *lemma* norm_num.bit1_add_bit0
- \- *lemma* norm_num.bit1_add_bit0_helper
- \- *lemma* norm_num.bit1_add_bit1
- \- *lemma* norm_num.bit1_add_bit1_helper
- \- *lemma* norm_num.bit1_add_one
- \- *lemma* norm_num.bit1_add_one_helper
- \- *lemma* norm_num.div_add_helper
- \- *lemma* norm_num.div_eq_div_helper
- \- *lemma* norm_num.div_helper
- \- *lemma* norm_num.div_mul_helper
- \- *lemma* norm_num.mk_cong
- \- *lemma* norm_num.mul_bit0
- \- *lemma* norm_num.mul_bit0_helper
- \- *lemma* norm_num.mul_bit1
- \- *lemma* norm_num.mul_bit1_helper
- \- *lemma* norm_num.mul_div_helper
- \- *lemma* norm_num.mul_one
- \- *lemma* norm_num.mul_zero
- \- *lemma* norm_num.neg_add_neg_eq_of_add_add_eq_zero
- \- *lemma* norm_num.neg_add_neg_helper
- \- *lemma* norm_num.neg_add_pos_eq_of_eq_add
- \- *lemma* norm_num.neg_add_pos_helper1
- \- *lemma* norm_num.neg_add_pos_helper2
- \- *lemma* norm_num.neg_mul_neg_helper
- \- *lemma* norm_num.neg_mul_pos_helper
- \- *lemma* norm_num.neg_neg_helper
- \- *lemma* norm_num.neg_zero_helper
- \- *lemma* norm_num.nonneg_bit0_helper
- \- *lemma* norm_num.nonneg_bit1_helper
- \- *lemma* norm_num.nonzero_of_div_helper
- \- *lemma* norm_num.nonzero_of_neg_helper
- \- *lemma* norm_num.nonzero_of_pos_helper
- \- *lemma* norm_num.one_add_bit0
- \- *lemma* norm_num.one_add_bit1
- \- *lemma* norm_num.one_add_bit1_helper
- \- *lemma* norm_num.one_add_one
- \- *lemma* norm_num.pos_add_neg_helper
- \- *lemma* norm_num.pos_bit0_helper
- \- *lemma* norm_num.pos_bit1_helper
- \- *lemma* norm_num.pos_mul_neg_helper
- \- *lemma* norm_num.sub_nat_pos_helper
- \- *lemma* norm_num.sub_nat_zero_helper
- \- *lemma* norm_num.subst_into_div
- \- *lemma* norm_num.subst_into_prod
- \- *lemma* norm_num.subst_into_subtr
- \- *lemma* norm_num.subst_into_sum
- \- *lemma* norm_num.zero_mul

Deleted src/init_/data/int/basic.lean


Deleted src/init_/data/int/order.lean
- \- *theorem* int.abs_eq_nat_abs
- \- *theorem* int.nat_abs_abs
- \- *theorem* int.sign_mul_abs

Deleted src/init_/data/nat/lemmas.lean
- \- *theorem* nat.eq_of_mul_eq_mul_right
- \- *theorem* nat.le_mul_self
- \- *theorem* nat.mul_self_le_mul_self
- \- *theorem* nat.mul_self_le_mul_self_iff
- \- *theorem* nat.mul_self_lt_mul_self
- \- *theorem* nat.mul_self_lt_mul_self_iff
- \- *theorem* nat.one_add

Deleted src/init_/default.lean


Modified test/library_search/ordered_ring.lean


Modified test/nth_rewrite.lean


Modified test/push_neg.lean


Modified test/rewrite.lean




## [2020-06-29 15:01:42](https://github.com/leanprover-community/mathlib/commit/eb05a94)
feat(order/filter/germ): define `filter.germ` ([#3172](https://github.com/leanprover-community/mathlib/pull/3172))
Actually we already had this definition under the name
`filter_product`.
#### Estimated changes
Modified src/data/real/hyperreal.lean
- \- *lemma* hyperreal.cast_div
- \+/\- *lemma* hyperreal.coe_abs
- \+ *lemma* hyperreal.coe_add
- \+ *lemma* hyperreal.coe_bit0
- \+ *lemma* hyperreal.coe_bit1
- \+ *lemma* hyperreal.coe_div
- \+/\- *lemma* hyperreal.coe_eq_coe
- \+ *lemma* hyperreal.coe_eq_one
- \+ *lemma* hyperreal.coe_eq_zero
- \+ *lemma* hyperreal.coe_inv
- \+/\- *lemma* hyperreal.coe_le_coe
- \+/\- *lemma* hyperreal.coe_lt_coe
- \+/\- *lemma* hyperreal.coe_max
- \+/\- *lemma* hyperreal.coe_min
- \+ *lemma* hyperreal.coe_mul
- \+ *lemma* hyperreal.coe_neg
- \+ *lemma* hyperreal.coe_one
- \+ *lemma* hyperreal.coe_pos
- \+ *lemma* hyperreal.coe_sub
- \+ *lemma* hyperreal.coe_zero
- \+/\- *lemma* hyperreal.epsilon_lt_pos
- \- *lemma* hyperreal.hyperfilter_ne_bot'
- \- *lemma* hyperreal.hyperfilter_ne_bot
- \+/\- *def* hyperreal.is_st
- \+/\- *theorem* hyperreal.is_st_Sup
- \+/\- *theorem* hyperreal.not_real_of_infinite
- \+/\- *theorem* hyperreal.st_eq_Sup
- \+/\- *def* hyperreal

Modified src/order/filter/filter_product.lean
- \- *def* filter.bigly_equal
- \- *lemma* filter.filter_product.abs_def
- \- *lemma* filter.filter_product.coe_inj
- \- *def* filter.filter_product.lift
- \- *lemma* filter.filter_product.lift_id
- \- *def* filter.filter_product.lift_rel
- \- *def* filter.filter_product.lift_rel₂
- \- *def* filter.filter_product.lift₂
- \- *lemma* filter.filter_product.lt_def'
- \- *lemma* filter.filter_product.lt_def
- \- *lemma* filter.filter_product.max_def
- \- *lemma* filter.filter_product.min_def
- \- *def* filter.filter_product.of
- \- *lemma* filter.filter_product.of_abs
- \- *lemma* filter.filter_product.of_add
- \- *lemma* filter.filter_product.of_bit0
- \- *lemma* filter.filter_product.of_bit1
- \- *lemma* filter.filter_product.of_div
- \- *lemma* filter.filter_product.of_eq
- \- *lemma* filter.filter_product.of_eq_coe
- \- *lemma* filter.filter_product.of_eq_zero
- \- *theorem* filter.filter_product.of_injective
- \- *lemma* filter.filter_product.of_inv
- \- *lemma* filter.filter_product.of_le
- \- *lemma* filter.filter_product.of_le_of_le
- \- *lemma* filter.filter_product.of_lt
- \- *lemma* filter.filter_product.of_lt_of_lt
- \- *lemma* filter.filter_product.of_max
- \- *lemma* filter.filter_product.of_min
- \- *lemma* filter.filter_product.of_mul
- \- *lemma* filter.filter_product.of_ne
- \- *lemma* filter.filter_product.of_ne_zero
- \- *lemma* filter.filter_product.of_neg
- \- *lemma* filter.filter_product.of_one
- \- *lemma* filter.filter_product.of_rel
- \- *lemma* filter.filter_product.of_rel_of_rel
- \- *lemma* filter.filter_product.of_rel_of_rel₂
- \- *lemma* filter.filter_product.of_rel₂
- \- *def* filter.filter_product.of_seq
- \- *lemma* filter.filter_product.of_seq_add
- \- *theorem* filter.filter_product.of_seq_fun
- \- *theorem* filter.filter_product.of_seq_fun₂
- \- *lemma* filter.filter_product.of_seq_inv
- \- *lemma* filter.filter_product.of_seq_mul
- \- *lemma* filter.filter_product.of_seq_neg
- \- *lemma* filter.filter_product.of_seq_one
- \- *lemma* filter.filter_product.of_seq_zero
- \- *lemma* filter.filter_product.of_sub
- \- *lemma* filter.filter_product.of_zero
- \- *def* filter.filterprod
- \+ *lemma* filter.germ.abs_def
- \+ *lemma* filter.germ.coe_lt
- \+ *lemma* filter.germ.coe_pos
- \+ *lemma* filter.germ.const_abs
- \+ *lemma* filter.germ.const_div
- \+ *lemma* filter.germ.const_lt
- \+ *lemma* filter.germ.const_max
- \+ *lemma* filter.germ.const_min
- \+ *lemma* filter.germ.lt_def
- \+ *lemma* filter.germ.max_def
- \+ *lemma* filter.germ.min_def

Added src/order/filter/germ.lean
- \+ *lemma* filter.const_eventually_eq'
- \+ *lemma* filter.const_eventually_eq
- \+ *lemma* filter.eventually_eq.comp_tendsto
- \+ *lemma* filter.eventually_eq.le
- \+ *lemma* filter.eventually_eq.trans_le
- \+ *lemma* filter.eventually_le.antisymm
- \+ *lemma* filter.eventually_le.congr
- \+ *lemma* filter.eventually_le.refl
- \+ *lemma* filter.eventually_le.trans
- \+ *lemma* filter.eventually_le.trans_eq
- \+ *def* filter.eventually_le
- \+ *lemma* filter.eventually_le_congr
- \+ *lemma* filter.germ.coe_coe_mul_hom
- \+ *lemma* filter.germ.coe_coe_ring_hom
- \+ *lemma* filter.germ.coe_comp_tendsto'
- \+ *lemma* filter.germ.coe_comp_tendsto
- \+ *lemma* filter.germ.coe_eq
- \+ *lemma* filter.germ.coe_inv
- \+ *lemma* filter.germ.coe_le
- \+ *lemma* filter.germ.coe_mul
- \+ *def* filter.germ.coe_mul_hom
- \+ *lemma* filter.germ.coe_one
- \+ *def* filter.germ.coe_ring_hom
- \+ *lemma* filter.germ.coe_smul'
- \+ *lemma* filter.germ.coe_smul
- \+ *lemma* filter.germ.coe_sub
- \+ *lemma* filter.germ.coe_tendsto
- \+ *def* filter.germ.comp_tendsto'
- \+ *lemma* filter.germ.comp_tendsto'_coe
- \+ *def* filter.germ.comp_tendsto
- \+ *lemma* filter.germ.const_bot
- \+ *lemma* filter.germ.const_comp_tendsto'
- \+ *lemma* filter.germ.const_comp_tendsto
- \+ *lemma* filter.germ.const_inf
- \+ *lemma* filter.germ.const_inj
- \+ *lemma* filter.germ.const_le
- \+ *lemma* filter.germ.const_le_iff
- \+ *lemma* filter.germ.const_sup
- \+ *lemma* filter.germ.const_top
- \+ *lemma* filter.germ.induction_on
- \+ *lemma* filter.germ.induction_on₂
- \+ *lemma* filter.germ.induction_on₃
- \+ *def* filter.germ.lift_on
- \+ *def* filter.germ.lift_pred
- \+ *lemma* filter.germ.lift_pred_coe
- \+ *lemma* filter.germ.lift_pred_const
- \+ *lemma* filter.germ.lift_pred_const_iff
- \+ *def* filter.germ.lift_rel
- \+ *lemma* filter.germ.lift_rel_coe
- \+ *lemma* filter.germ.lift_rel_const
- \+ *lemma* filter.germ.lift_rel_const_iff
- \+ *def* filter.germ.map'
- \+ *lemma* filter.germ.map'_coe
- \+ *def* filter.germ.map
- \+ *lemma* filter.germ.map_coe
- \+ *lemma* filter.germ.map_const
- \+ *lemma* filter.germ.map_id
- \+ *lemma* filter.germ.map_map
- \+ *def* filter.germ.map₂
- \+ *lemma* filter.germ.map₂_const
- \+ *lemma* filter.germ.mk'_eq_coe
- \+ *lemma* filter.germ.quot_mk_eq_coe
- \+ *def* filter.germ
- \+ *def* filter.germ_setoid

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* filter.bot_ne_hyperfilter
- \+ *lemma* filter.hyperfilter_ne_bot
- \+ *lemma* filter.is_ultrafilter.em
- \+ *lemma* filter.is_ultrafilter.eventually_imp
- \+ *lemma* filter.is_ultrafilter.eventually_not
- \+ *lemma* filter.is_ultrafilter.eventually_or



## [2020-06-29 13:48:28](https://github.com/leanprover-community/mathlib/commit/4907d5d)
feat(algebra/ring): ite_mul_one and ite_mul_zero_... ([#3217](https://github.com/leanprover-community/mathlib/pull/3217))
Three simple lemmas about if statements involving multiplication, useful while rewriting.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* ite_mul_one

Modified src/algebra/ring.lean
- \+ *lemma* ite_mul_zero_left
- \+ *lemma* ite_mul_zero_right



## [2020-06-29 13:48:26](https://github.com/leanprover-community/mathlib/commit/964f0e5)
feat(data/polynomial): work over noncommutative rings where possible ([#3193](https://github.com/leanprover-community/mathlib/pull/3193))
After downgrading `C` from an algebra homomorphism to a ring homomorphism in [69931ac](https://github.com/leanprover-community/mathlib/commit/69931acfe7b6a29f988bcf7094e090767b34fb85), which requires a few tweaks, everything else is straightforward.
#### Estimated changes
Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.sum_smul_index

Modified src/data/monoid_algebra.lean
- \+ *def* add_monoid_algebra.algebra_map'
- \+ *def* monoid_algebra.algebra_map'

Modified src/data/polynomial.lean
- \+/\- *def* polynomial.C
- \+ *lemma* polynomial.C_eq_int_cast
- \+ *lemma* polynomial.C_eq_nat_cast
- \+/\- *lemma* polynomial.C_neg
- \+/\- *lemma* polynomial.C_sub
- \+ *lemma* polynomial.X_mul
- \+ *lemma* polynomial.X_pow_mul
- \+ *lemma* polynomial.X_pow_mul_assoc
- \+/\- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* polynomial.degree_map_le
- \+/\- *lemma* polynomial.degree_pos_of_root
- \+/\- *def* polynomial.derivative_hom
- \+/\- *lemma* polynomial.derivative_neg
- \+/\- *lemma* polynomial.derivative_sub
- \+ *lemma* polynomial.eval_int_cast
- \+/\- *lemma* polynomial.eval_map
- \+ *lemma* polynomial.eval_nat_cast
- \+ *lemma* polynomial.eval_smul
- \+/\- *lemma* polynomial.eval₂_neg
- \+/\- *lemma* polynomial.eval₂_smul
- \+/\- *lemma* polynomial.eval₂_sub
- \- *lemma* polynomial.int_cast_eq_C
- \+/\- *lemma* polynomial.map_map
- \+/\- *lemma* polynomial.map_mul
- \+/\- *lemma* polynomial.map_pow
- \+/\- *lemma* polynomial.monic.ne_zero
- \+/\- *lemma* polynomial.monic_map
- \- *lemma* polynomial.nat_cast_eq_C

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/localization.lean




## [2020-06-29 13:48:23](https://github.com/leanprover-community/mathlib/commit/a708f85)
feat(category/limits/shapes): fix biproducts ([#3175](https://github.com/leanprover-community/mathlib/pull/3175))
This is a second attempt at [#3102](https://github.com/leanprover-community/mathlib/pull/3102).
Previously the definition of a (binary) biproduct in a category with zero morphisms (but not necessarily) preadditive was just wrong.
The definition for a "bicone" was just something that was simultaneously a cone and a cocone, with the same cone points. It was a "biproduct bicone" if the cone was a limit cone and the cocone was a colimit cocone. However, this definition was not particularly useful. In particular, there was no way to prove that the two different `map` constructions providing a morphism `W ⊞ X ⟶ Y ⊞ Z` (i.e. by treating the biproducts either as cones, or as cocones) were actually equal. Blech.
So, I've added the axioms `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q` to `bicone P Q`. (Note these only require the exist of zero morphisms, not preadditivity.)
Now the two map constructions are equal.
I've then entirely removed the `has_preadditive_biproduct` typeclass. Instead we have
1. additional theorems providing `total`, when `preadditive C` is available
2. alternative constructors for `has_biproduct` that use `total` rather than `is_limit` and `is_colimit`.
This PR also introduces some abbreviations along the lines of `abbreviation has_binary_product (X Y : C) := has_limit (pair X Y)`, just to improve readability.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *def* category_theory.limits.coprod.desc'
- \+/\- *abbreviation* category_theory.limits.coprod.desc
- \+/\- *lemma* category_theory.limits.coprod.desc_comp_comp
- \+/\- *lemma* category_theory.limits.coprod.hom_ext
- \+/\- *abbreviation* category_theory.limits.coprod.inl
- \+/\- *lemma* category_theory.limits.coprod.inl_desc
- \+/\- *abbreviation* category_theory.limits.coprod.inr
- \+/\- *lemma* category_theory.limits.coprod.inr_desc
- \+ *abbreviation* category_theory.limits.coprod.map_iso
- \+ *lemma* category_theory.limits.coprod.map_iso_hom
- \+ *lemma* category_theory.limits.coprod.map_iso_inv
- \+/\- *abbreviation* category_theory.limits.coprod
- \+ *abbreviation* category_theory.limits.has_binary_coproduct
- \+ *abbreviation* category_theory.limits.has_binary_product
- \+/\- *abbreviation* category_theory.limits.prod.fst
- \+/\- *lemma* category_theory.limits.prod.hom_ext
- \+/\- *def* category_theory.limits.prod.lift'
- \+/\- *abbreviation* category_theory.limits.prod.lift
- \+/\- *lemma* category_theory.limits.prod.lift_comp_comp
- \+/\- *lemma* category_theory.limits.prod.lift_fst
- \+/\- *lemma* category_theory.limits.prod.lift_snd
- \+ *abbreviation* category_theory.limits.prod.map_iso
- \+ *lemma* category_theory.limits.prod.map_iso_hom
- \+ *lemma* category_theory.limits.prod.map_iso_inv
- \+/\- *abbreviation* category_theory.limits.prod.snd
- \+/\- *abbreviation* category_theory.limits.prod
- \+ *def* category_theory.limits.walking_pair.equiv_bool
- \+ *lemma* category_theory.limits.walking_pair.equiv_bool_apply_left
- \+ *lemma* category_theory.limits.walking_pair.equiv_bool_apply_right
- \+ *lemma* category_theory.limits.walking_pair.equiv_bool_symm_apply_ff
- \+ *lemma* category_theory.limits.walking_pair.equiv_bool_symm_apply_tt
- \+ *def* category_theory.limits.walking_pair.swap
- \+ *lemma* category_theory.limits.walking_pair.swap_apply_left
- \+ *lemma* category_theory.limits.walking_pair.swap_apply_right
- \+ *lemma* category_theory.limits.walking_pair.swap_symm_apply_ff
- \+ *lemma* category_theory.limits.walking_pair.swap_symm_apply_tt

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.bicone.to_binary_bicone
- \+ *def* category_theory.limits.bicone.to_binary_bicone_is_colimit
- \+ *def* category_theory.limits.bicone.to_binary_bicone_is_limit
- \+/\- *def* category_theory.limits.bicone.to_cocone
- \+/\- *def* category_theory.limits.bicone.to_cone
- \+/\- *structure* category_theory.limits.bicone
- \+ *lemma* category_theory.limits.bicone_ι_π_ne
- \+ *lemma* category_theory.limits.bicone_ι_π_self
- \+ *lemma* category_theory.limits.binary_bicone.to_cocone_X
- \+ *lemma* category_theory.limits.binary_bicone.to_cocone_ι_app_left
- \+ *lemma* category_theory.limits.binary_bicone.to_cocone_ι_app_right
- \+ *lemma* category_theory.limits.binary_bicone.to_cone_X
- \+ *lemma* category_theory.limits.binary_bicone.to_cone_π_app_left
- \+ *lemma* category_theory.limits.binary_bicone.to_cone_π_app_right
- \+ *lemma* category_theory.limits.biprod.braid_natural
- \+ *def* category_theory.limits.biprod.braiding'
- \+ *lemma* category_theory.limits.biprod.braiding'_eq_braiding
- \+ *def* category_theory.limits.biprod.braiding
- \+ *lemma* category_theory.limits.biprod.braiding_map_braiding
- \+ *lemma* category_theory.limits.biprod.desc_eq
- \- *lemma* category_theory.limits.biprod.fst_add_snd
- \- *lemma* category_theory.limits.biprod.inl_add_inr
- \+/\- *lemma* category_theory.limits.biprod.inl_fst
- \+ *lemma* category_theory.limits.biprod.inl_map
- \+/\- *lemma* category_theory.limits.biprod.inl_snd
- \+/\- *lemma* category_theory.limits.biprod.inr_fst
- \+ *lemma* category_theory.limits.biprod.inr_map
- \+/\- *lemma* category_theory.limits.biprod.inr_snd
- \+ *lemma* category_theory.limits.biprod.lift_eq
- \+ *abbreviation* category_theory.limits.biprod.map'
- \+/\- *abbreviation* category_theory.limits.biprod.map
- \+ *lemma* category_theory.limits.biprod.map_eq
- \+ *lemma* category_theory.limits.biprod.map_eq_map'
- \+ *lemma* category_theory.limits.biprod.map_fst
- \+ *def* category_theory.limits.biprod.map_iso
- \+ *lemma* category_theory.limits.biprod.map_snd
- \+ *lemma* category_theory.limits.biprod.symmetry'
- \+ *lemma* category_theory.limits.biprod.symmetry
- \+ *abbreviation* category_theory.limits.biproduct.bicone
- \+ *lemma* category_theory.limits.biproduct.desc_eq
- \+ *lemma* category_theory.limits.biproduct.hom_ext'
- \+ *lemma* category_theory.limits.biproduct.hom_ext
- \+ *lemma* category_theory.limits.biproduct.inl_map
- \+ *abbreviation* category_theory.limits.biproduct.is_colimit
- \+ *abbreviation* category_theory.limits.biproduct.is_limit
- \+ *lemma* category_theory.limits.biproduct.lift_desc
- \+ *lemma* category_theory.limits.biproduct.lift_eq
- \+ *abbreviation* category_theory.limits.biproduct.map'
- \+/\- *abbreviation* category_theory.limits.biproduct.map
- \+ *lemma* category_theory.limits.biproduct.map_eq
- \+ *lemma* category_theory.limits.biproduct.map_eq_map'
- \+ *lemma* category_theory.limits.biproduct.total
- \+/\- *abbreviation* category_theory.limits.biproduct.ι
- \+ *lemma* category_theory.limits.biproduct.ι_π
- \+ *lemma* category_theory.limits.biproduct.ι_π_ne
- \+ *lemma* category_theory.limits.biproduct.ι_π_self
- \+/\- *abbreviation* category_theory.limits.biproduct.π
- \+/\- *abbreviation* category_theory.limits.biproduct
- \+/\- *def* category_theory.limits.biproduct_iso
- \+ *def* category_theory.limits.has_binary_biproduct.of_has_binary_coproduct
- \+ *def* category_theory.limits.has_binary_biproduct.of_has_binary_product
- \+ *def* category_theory.limits.has_binary_biproduct_of_total
- \+ *def* category_theory.limits.has_binary_biproducts.of_has_binary_coproducts
- \+ *def* category_theory.limits.has_binary_biproducts.of_has_binary_products
- \+ *def* category_theory.limits.has_binary_biproducts_of_finite_biproducts
- \+ *def* category_theory.limits.has_biproduct.of_has_coproduct
- \+ *def* category_theory.limits.has_biproduct.of_has_product
- \+ *def* category_theory.limits.has_biproduct_of_total
- \- *def* category_theory.limits.has_preadditive_binary_biproduct.of_has_colimit_pair
- \- *def* category_theory.limits.has_preadditive_binary_biproduct.of_has_limit_pair
- \- *def* category_theory.limits.has_preadditive_binary_biproducts_of_has_binary_coproducts
- \- *def* category_theory.limits.has_preadditive_binary_biproducts_of_has_binary_products

Modified src/category_theory/limits/shapes/products.lean
- \+ *abbreviation* category_theory.limits.has_coproduct
- \+ *abbreviation* category_theory.limits.has_coproducts_of_shape
- \+ *abbreviation* category_theory.limits.has_product
- \+ *abbreviation* category_theory.limits.has_products_of_shape
- \+/\- *abbreviation* category_theory.limits.pi.lift
- \+/\- *abbreviation* category_theory.limits.pi.map
- \+/\- *abbreviation* category_theory.limits.pi.π
- \+/\- *abbreviation* category_theory.limits.pi_obj
- \+/\- *abbreviation* category_theory.limits.sigma.desc
- \+/\- *abbreviation* category_theory.limits.sigma.map
- \+/\- *abbreviation* category_theory.limits.sigma.ι
- \+/\- *abbreviation* category_theory.limits.sigma_obj



## [2020-06-29 13:48:21](https://github.com/leanprover-community/mathlib/commit/78beab4)
feat(linear_algebra/affine_space): affine independence ([#3140](https://github.com/leanprover-community/mathlib/pull/3140))
Define affine independent indexed families of points (in terms of no
nontrivial `weighted_vsub` in the family being zero), prove that a
family of at most one point is affine independent, and prove a family
of points is affine independent if and only if a corresponding family
of subtractions is linearly independent.
There are of course other equivalent descriptions of affine
independent families it will be useful to add later (that the affine
span of all proper subfamilies is smaller than the affine span of the
whole family, that each point is not in the affine span of the rest;
in the case of a family indexed by a `fintype`, that the dimension of
the affine span is one less than the cardinality).  But I think the
definition and one equivalent formulation is a reasonable starting
point.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_insert_one
- \+ *lemma* finset.prod_subtype_eq_prod_filter
- \+ *lemma* finset.prod_subtype_map_embedding
- \+ *lemma* finset.prod_subtype_of_mem

Modified src/data/finset.lean
- \+/\- *lemma* finset.filter_true
- \+ *lemma* finset.filter_true_of_mem
- \+ *lemma* finset.not_mem_map_subtype_of_not_property
- \+ *lemma* finset.subtype_map
- \+ *lemma* finset.subtype_map_of_mem

Modified src/linear_algebra/affine_space.lean
- \+ *def* affine_independent
- \+ *lemma* affine_independent_iff_linear_independent_vsub
- \+ *lemma* affine_independent_of_subsingleton
- \+ *lemma* finset.weighted_vsub_of_point_erase
- \+ *lemma* finset.weighted_vsub_of_point_insert



## [2020-06-29 12:45:16](https://github.com/leanprover-community/mathlib/commit/36ce13f)
chore(finset/nat/antidiagonal): simplify some proofs ([#3225](https://github.com/leanprover-community/mathlib/pull/3225))
Replace some proofs with `rfl`, and avoid `multiset.to_finset` when there is a `nodup` available.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.card_mk

Modified src/data/list/antidiagonal.lean


Modified src/data/multiset.lean




## [2020-06-29 08:15:17](https://github.com/leanprover-community/mathlib/commit/c4f9176)
feat(linear_algebra/tensor_product): ite_tmul ([#3216](https://github.com/leanprover-community/mathlib/pull/3216))
```
((if P then x₁ else 0) ⊗ₜ[R] x₂) = if P then (x₁ ⊗ₜ x₂) else 0
```
and the symmetric version.
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* tensor_product.ite_tmul
- \+ *lemma* tensor_product.tmul_ite



## [2020-06-29 06:59:46](https://github.com/leanprover-community/mathlib/commit/ca44926)
chore(ring_theory/tensor_product): missing simp lemmas ([#3215](https://github.com/leanprover-community/mathlib/pull/3215))
A few missing `simp` lemmas.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *lemma* algebra.tensor_product.alg_hom_of_linear_map_tensor_product_apply
- \+ *lemma* algebra.tensor_product.include_left_apply
- \+ *lemma* algebra.tensor_product.include_right_apply
- \- *lemma* algebra.tensor_product.mul_tmul
- \+ *lemma* algebra.tensor_product.tmul_mul_tmul
- \+ *lemma* algebra.tensor_product.tmul_pow



## [2020-06-29 04:45:10](https://github.com/leanprover-community/mathlib/commit/a443d8b)
feat(simp_nf): instructions for linter timeout ([#3205](https://github.com/leanprover-community/mathlib/pull/3205))
#### Estimated changes
Modified src/tactic/lint/simp.lean
- \- *lemma* add_zero
- \- *lemma* zero_add_zero



## [2020-06-29 04:21:12](https://github.com/leanprover-community/mathlib/commit/9a1c0a6)
feat(data/padics/padic_norm) Fix namespacing of padic_val_nat ([#3207](https://github.com/leanprover-community/mathlib/pull/3207))
No longer need we `padic_val_rat.padic_val_nat`.
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *def* padic_val_nat
- \+ *lemma* padic_val_nat_def
- \- *def* padic_val_rat.padic_val_nat
- \- *lemma* padic_val_rat.padic_val_nat_def
- \- *lemma* padic_val_rat.padic_val_rat_of_nat
- \- *lemma* padic_val_rat.zero_le_padic_val_rat_of_nat
- \+ *lemma* padic_val_rat_of_nat
- \+ *lemma* zero_le_padic_val_rat_of_nat



## [2020-06-29 03:57:10](https://github.com/leanprover-community/mathlib/commit/9acf590)
feat(data/matrix/notation): smul matrix lemmas ([#3208](https://github.com/leanprover-community/mathlib/pull/3208))
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.smul_mat_cons
- \+ *lemma* matrix.smul_mat_empty



## [2020-06-29 03:20:59](https://github.com/leanprover-community/mathlib/commit/d2b46ab)
chore(category_theory/punit): use discrete punit instead of punit ([#3201](https://github.com/leanprover-community/mathlib/pull/3201))
Analogous to [#3191](https://github.com/leanprover-community/mathlib/pull/3191) for `punit`. I also removed some `simp` lemmas which can be generated instead by `[simps]`.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean


Modified src/category_theory/comma.lean
- \- *lemma* category_theory.arrow.hom_mk'_left
- \- *lemma* category_theory.arrow.hom_mk'_right
- \- *lemma* category_theory.arrow.hom_mk_left
- \- *lemma* category_theory.arrow.hom_mk_right
- \- *lemma* category_theory.arrow.mk_hom
- \- *lemma* category_theory.comma.fst_map
- \- *lemma* category_theory.comma.fst_obj
- \- *lemma* category_theory.comma.map_left_comp_hom_app_left
- \- *lemma* category_theory.comma.map_left_comp_hom_app_right
- \- *lemma* category_theory.comma.map_left_comp_inv_app_left
- \- *lemma* category_theory.comma.map_left_comp_inv_app_right
- \- *lemma* category_theory.comma.map_left_id_hom_app_left
- \- *lemma* category_theory.comma.map_left_id_hom_app_right
- \- *lemma* category_theory.comma.map_left_id_inv_app_left
- \- *lemma* category_theory.comma.map_left_id_inv_app_right
- \- *lemma* category_theory.comma.map_left_map_left
- \- *lemma* category_theory.comma.map_left_map_right
- \- *lemma* category_theory.comma.map_left_obj_hom
- \- *lemma* category_theory.comma.map_left_obj_left
- \- *lemma* category_theory.comma.map_left_obj_right
- \- *lemma* category_theory.comma.map_right_comp_hom_app_left
- \- *lemma* category_theory.comma.map_right_comp_hom_app_right
- \- *lemma* category_theory.comma.map_right_comp_inv_app_left
- \- *lemma* category_theory.comma.map_right_comp_inv_app_right
- \- *lemma* category_theory.comma.map_right_id_hom_app_left
- \- *lemma* category_theory.comma.map_right_id_hom_app_right
- \- *lemma* category_theory.comma.map_right_id_inv_app_left
- \- *lemma* category_theory.comma.map_right_id_inv_app_right
- \- *lemma* category_theory.comma.map_right_map_left
- \- *lemma* category_theory.comma.map_right_map_right
- \- *lemma* category_theory.comma.map_right_obj_hom
- \- *lemma* category_theory.comma.map_right_obj_left
- \- *lemma* category_theory.comma.map_right_obj_right
- \- *lemma* category_theory.comma.snd_map
- \- *lemma* category_theory.comma.snd_obj
- \- *lemma* category_theory.over.hom_mk_left
- \+/\- *def* category_theory.over.map
- \- *lemma* category_theory.over.over_morphism_right
- \+/\- *def* category_theory.over
- \- *lemma* category_theory.under.hom_mk_right
- \+/\- *def* category_theory.under.map
- \- *lemma* category_theory.under.mk_hom
- \- *lemma* category_theory.under.mk_right
- \- *lemma* category_theory.under.under_morphism_left
- \+/\- *def* category_theory.under

Modified src/category_theory/connected.lean
- \+ *def* category_theory.discrete_connected_equiv_punit

Modified src/category_theory/discrete_category.lean
- \+ *def* category_theory.discrete.equiv_of_equivalence

Modified src/category_theory/elements.lean
- \+/\- *def* category_theory.category_of_elements.comma_equivalence
- \+ *lemma* category_theory.category_of_elements.comma_equivalence_functor
- \+ *lemma* category_theory.category_of_elements.comma_equivalence_inverse
- \+/\- *def* category_theory.category_of_elements.from_comma
- \+/\- *def* category_theory.category_of_elements.to_comma
- \- *lemma* category_theory.category_of_elements.π_map
- \- *lemma* category_theory.category_of_elements.π_obj

Modified src/category_theory/groupoid.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/punit.lean
- \+ *def* category_theory.functor.equiv
- \+ *abbreviation* category_theory.functor.from_punit
- \+ *lemma* category_theory.functor.punit_ext'
- \+ *def* category_theory.functor.punit_ext
- \+/\- *def* category_theory.functor.star
- \- *lemma* category_theory.functor.star_map
- \- *lemma* category_theory.functor.star_obj



## [2020-06-29 02:24:01](https://github.com/leanprover-community/mathlib/commit/b503fb4)
chore(docs/tutorial): change category declarations ([#3220](https://github.com/leanprover-community/mathlib/pull/3220))
change category declarations to match syntax in recent commit (i.e. no more explicit typeclass naming), delete unnecessary "include" lines as they are no longer needed for Lean to include the typeclass, update tutorial text to explain new syntax
#### Estimated changes
Modified docs/tutorial/category_theory/intro.lean




## [2020-06-28 22:51:22](https://github.com/leanprover-community/mathlib/commit/2ec83dc)
chore(group_theory/submonoid): split into 3 files ([#3058](https://github.com/leanprover-community/mathlib/pull/3058))
Now
* `group_theory.submonoid.basic` contains the definition, `complete_lattice` structure, and some basic facts about `closure`;
* `group_theory.submonoid.operations` contains definitions of various operations on submonoids;
* `group_theory.submonoid.membership` contains various facts about membership in a submonoid or the submonoid closure of a set.
#### Estimated changes
Modified src/group_theory/subgroup.lean


Deleted src/group_theory/submonoid.lean
- \- *lemma* add_submonoid.closure_singleton_eq
- \- *lemma* add_submonoid.mem_closure_singleton
- \- *def* add_submonoid.of_submonoid
- \- *lemma* add_submonoid.smul_mem
- \- *def* add_submonoid.to_submonoid
- \- *structure* add_submonoid
- \- *theorem* free_monoid.closure_range_of
- \- *def* monoid_hom.cod_mrestrict
- \- *lemma* monoid_hom.coe_mrange
- \- *lemma* monoid_hom.coe_mrange_restrict
- \- *def* monoid_hom.eq_mlocus
- \- *lemma* monoid_hom.eq_of_eq_on_mdense
- \- *lemma* monoid_hom.eq_of_eq_on_mtop
- \- *lemma* monoid_hom.eq_on_mclosure
- \- *lemma* monoid_hom.map_mclosure
- \- *lemma* monoid_hom.map_mrange
- \- *lemma* monoid_hom.mclosure_preimage_le
- \- *lemma* monoid_hom.mem_mrange
- \- *def* monoid_hom.mrange
- \- *def* monoid_hom.mrange_restrict
- \- *lemma* monoid_hom.mrange_top_iff_surjective
- \- *lemma* monoid_hom.mrange_top_of_surjective
- \- *def* monoid_hom.mrestrict
- \- *lemma* monoid_hom.mrestrict_apply
- \- *def* mul_equiv.submonoid_congr
- \- *def* submonoid.add_submonoid_equiv
- \- *lemma* submonoid.bot_prod_bot
- \- *def* submonoid.closure
- \- *lemma* submonoid.closure_Union
- \- *lemma* submonoid.closure_empty
- \- *lemma* submonoid.closure_eq
- \- *lemma* submonoid.closure_eq_mrange
- \- *lemma* submonoid.closure_eq_of_le
- \- *lemma* submonoid.closure_induction
- \- *lemma* submonoid.closure_le
- \- *lemma* submonoid.closure_mono
- \- *lemma* submonoid.closure_singleton_eq
- \- *lemma* submonoid.closure_union
- \- *lemma* submonoid.closure_univ
- \- *lemma* submonoid.coe_Inf
- \- *lemma* submonoid.coe_Sup_of_directed_on
- \- *lemma* submonoid.coe_bot
- \- *lemma* submonoid.coe_coe
- \- *lemma* submonoid.coe_comap
- \- *lemma* submonoid.coe_copy
- \- *lemma* submonoid.coe_eq_coe
- \- *lemma* submonoid.coe_inf
- \- *lemma* submonoid.coe_infi
- \- *lemma* submonoid.coe_map
- \- *lemma* submonoid.coe_mul
- \- *lemma* submonoid.coe_one
- \- *lemma* submonoid.coe_prod
- \- *lemma* submonoid.coe_ssubset_coe
- \- *lemma* submonoid.coe_subset_coe
- \- *theorem* submonoid.coe_subtype
- \- *lemma* submonoid.coe_supr_of_directed
- \- *lemma* submonoid.coe_top
- \- *def* submonoid.comap
- \- *lemma* submonoid.comap_comap
- \- *lemma* submonoid.comap_inf
- \- *lemma* submonoid.comap_infi
- \- *lemma* submonoid.comap_top
- \- *def* submonoid.copy
- \- *lemma* submonoid.copy_eq
- \- *lemma* submonoid.exists_list_of_mem_closure
- \- *theorem* submonoid.ext'
- \- *theorem* submonoid.ext
- \- *lemma* submonoid.gc_map_comap
- \- *def* submonoid.inclusion
- \- *lemma* submonoid.le_def
- \- *lemma* submonoid.list_prod_mem
- \- *def* submonoid.map
- \- *lemma* submonoid.map_bot
- \- *lemma* submonoid.map_id
- \- *lemma* submonoid.map_inl
- \- *lemma* submonoid.map_inr
- \- *lemma* submonoid.map_le_iff_le_comap
- \- *lemma* submonoid.map_map
- \- *lemma* submonoid.map_sup
- \- *lemma* submonoid.map_supr
- \- *lemma* submonoid.mem_Inf
- \- *lemma* submonoid.mem_Sup_of_directed_on
- \- *lemma* submonoid.mem_bot
- \- *lemma* submonoid.mem_carrier
- \- *lemma* submonoid.mem_closure
- \- *lemma* submonoid.mem_closure_singleton
- \- *lemma* submonoid.mem_coe
- \- *lemma* submonoid.mem_comap
- \- *lemma* submonoid.mem_inf
- \- *lemma* submonoid.mem_infi
- \- *lemma* submonoid.mem_map
- \- *lemma* submonoid.mem_prod
- \- *lemma* submonoid.mem_sup
- \- *lemma* submonoid.mem_supr_of_directed
- \- *lemma* submonoid.mem_top
- \- *theorem* submonoid.mul_mem
- \- *lemma* submonoid.multiset_prod_mem
- \- *def* submonoid.of_add_submonoid
- \- *theorem* submonoid.one_mem
- \- *lemma* submonoid.pow_mem
- \- *def* submonoid.prod
- \- *lemma* submonoid.prod_bot_sup_bot_prod
- \- *def* submonoid.prod_equiv
- \- *lemma* submonoid.prod_mem
- \- *lemma* submonoid.prod_mono
- \- *lemma* submonoid.prod_mono_left
- \- *lemma* submonoid.prod_mono_right
- \- *lemma* submonoid.prod_top
- \- *lemma* submonoid.range_fst
- \- *lemma* submonoid.range_inl'
- \- *lemma* submonoid.range_inl
- \- *lemma* submonoid.range_inl_sup_range_inr
- \- *lemma* submonoid.range_inr'
- \- *lemma* submonoid.range_inr
- \- *lemma* submonoid.range_snd
- \- *lemma* submonoid.range_subtype
- \- *lemma* submonoid.subset_closure
- \- *def* submonoid.subtype
- \- *lemma* submonoid.sup_eq_range
- \- *def* submonoid.to_add_submonoid
- \- *lemma* submonoid.top_prod
- \- *lemma* submonoid.top_prod_top
- \- *structure* submonoid

Added src/group_theory/submonoid/basic.lean
- \+ *structure* add_submonoid
- \+ *lemma* monoid_hom.coe_of_mdense
- \+ *def* monoid_hom.eq_mlocus
- \+ *lemma* monoid_hom.eq_of_eq_on_mdense
- \+ *lemma* monoid_hom.eq_of_eq_on_mtop
- \+ *lemma* monoid_hom.eq_on_mclosure
- \+ *def* monoid_hom.of_mdense
- \+ *def* submonoid.closure
- \+ *lemma* submonoid.closure_Union
- \+ *lemma* submonoid.closure_empty
- \+ *lemma* submonoid.closure_eq
- \+ *lemma* submonoid.closure_eq_of_le
- \+ *lemma* submonoid.closure_induction
- \+ *lemma* submonoid.closure_le
- \+ *lemma* submonoid.closure_mono
- \+ *lemma* submonoid.closure_union
- \+ *lemma* submonoid.closure_univ
- \+ *lemma* submonoid.coe_Inf
- \+ *lemma* submonoid.coe_bot
- \+ *lemma* submonoid.coe_coe
- \+ *lemma* submonoid.coe_copy
- \+ *lemma* submonoid.coe_eq_coe
- \+ *lemma* submonoid.coe_inf
- \+ *lemma* submonoid.coe_infi
- \+ *lemma* submonoid.coe_ssubset_coe
- \+ *lemma* submonoid.coe_subset_coe
- \+ *lemma* submonoid.coe_top
- \+ *def* submonoid.copy
- \+ *lemma* submonoid.copy_eq
- \+ *lemma* submonoid.dense_induction
- \+ *theorem* submonoid.ext'
- \+ *theorem* submonoid.ext
- \+ *lemma* submonoid.le_def
- \+ *lemma* submonoid.mem_Inf
- \+ *lemma* submonoid.mem_bot
- \+ *lemma* submonoid.mem_carrier
- \+ *lemma* submonoid.mem_closure
- \+ *lemma* submonoid.mem_coe
- \+ *lemma* submonoid.mem_inf
- \+ *lemma* submonoid.mem_infi
- \+ *lemma* submonoid.mem_top
- \+ *theorem* submonoid.mul_mem
- \+ *theorem* submonoid.one_mem
- \+ *lemma* submonoid.subset_closure
- \+ *structure* submonoid

Added src/group_theory/submonoid/default.lean


Added src/group_theory/submonoid/membership.lean
- \+ *lemma* add_submonoid.closure_singleton_eq
- \+ *lemma* add_submonoid.mem_closure_singleton
- \+ *lemma* add_submonoid.nsmul_mem
- \+ *theorem* free_monoid.closure_range_of
- \+ *lemma* submonoid.closure_eq_mrange
- \+ *lemma* submonoid.closure_singleton_eq
- \+ *lemma* submonoid.coe_Sup_of_directed_on
- \+ *lemma* submonoid.coe_supr_of_directed
- \+ *lemma* submonoid.exists_list_of_mem_closure
- \+ *lemma* submonoid.list_prod_mem
- \+ *lemma* submonoid.mem_Sup_of_directed_on
- \+ *lemma* submonoid.mem_closure_singleton
- \+ *lemma* submonoid.mem_sup
- \+ *lemma* submonoid.mem_supr_of_directed
- \+ *lemma* submonoid.multiset_prod_mem
- \+ *lemma* submonoid.pow_mem
- \+ *lemma* submonoid.prod_mem
- \+ *lemma* submonoid.sup_eq_range

Added src/group_theory/submonoid/operations.lean
- \+ *def* add_submonoid.of_submonoid
- \+ *def* add_submonoid.to_submonoid
- \+ *def* monoid_hom.cod_mrestrict
- \+ *lemma* monoid_hom.coe_mrange
- \+ *lemma* monoid_hom.coe_mrange_restrict
- \+ *lemma* monoid_hom.map_mclosure
- \+ *lemma* monoid_hom.map_mrange
- \+ *lemma* monoid_hom.mclosure_preimage_le
- \+ *lemma* monoid_hom.mem_mrange
- \+ *def* monoid_hom.mrange
- \+ *def* monoid_hom.mrange_restrict
- \+ *lemma* monoid_hom.mrange_top_iff_surjective
- \+ *lemma* monoid_hom.mrange_top_of_surjective
- \+ *def* monoid_hom.mrestrict
- \+ *lemma* monoid_hom.mrestrict_apply
- \+ *def* mul_equiv.submonoid_congr
- \+ *def* submonoid.add_submonoid_equiv
- \+ *lemma* submonoid.bot_prod_bot
- \+ *lemma* submonoid.coe_comap
- \+ *lemma* submonoid.coe_map
- \+ *lemma* submonoid.coe_mul
- \+ *lemma* submonoid.coe_one
- \+ *lemma* submonoid.coe_prod
- \+ *theorem* submonoid.coe_subtype
- \+ *def* submonoid.comap
- \+ *lemma* submonoid.comap_comap
- \+ *lemma* submonoid.comap_inf
- \+ *lemma* submonoid.comap_infi
- \+ *lemma* submonoid.comap_top
- \+ *lemma* submonoid.gc_map_comap
- \+ *def* submonoid.inclusion
- \+ *def* submonoid.map
- \+ *lemma* submonoid.map_bot
- \+ *lemma* submonoid.map_id
- \+ *lemma* submonoid.map_inl
- \+ *lemma* submonoid.map_inr
- \+ *lemma* submonoid.map_le_iff_le_comap
- \+ *lemma* submonoid.map_map
- \+ *lemma* submonoid.map_sup
- \+ *lemma* submonoid.map_supr
- \+ *lemma* submonoid.mem_comap
- \+ *lemma* submonoid.mem_map
- \+ *lemma* submonoid.mem_prod
- \+ *lemma* submonoid.mrange_fst
- \+ *lemma* submonoid.mrange_inl'
- \+ *lemma* submonoid.mrange_inl
- \+ *lemma* submonoid.mrange_inl_sup_mrange_inr
- \+ *lemma* submonoid.mrange_inr'
- \+ *lemma* submonoid.mrange_inr
- \+ *lemma* submonoid.mrange_snd
- \+ *def* submonoid.of_add_submonoid
- \+ *def* submonoid.prod
- \+ *lemma* submonoid.prod_bot_sup_bot_prod
- \+ *def* submonoid.prod_equiv
- \+ *lemma* submonoid.prod_mono
- \+ *lemma* submonoid.prod_top
- \+ *lemma* submonoid.range_subtype
- \+ *def* submonoid.subtype
- \+ *def* submonoid.to_add_submonoid
- \+ *lemma* submonoid.top_prod
- \+ *lemma* submonoid.top_prod_top

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* subsemiring.nsmul_mem
- \- *lemma* subsemiring.smul_mem



## [2020-06-28 22:28:30](https://github.com/leanprover-community/mathlib/commit/4ad82e5)
feat(uniform_space): compact uniform spaces, Heine-Cantor ([#3180](https://github.com/leanprover-community/mathlib/pull/3180))
feat(uniform_space): compact uniform spaces
Compact Hausdorff spaces are uniquely uniformizable and continuous
functions on them are uniformly continuous (Heine-Cantor).
#### Estimated changes
Added src/topology/uniform_space/compact_separated.lean
- \+ *lemma* compact.uniform_continuous_on_of_continuous'
- \+ *lemma* compact.uniform_continuous_on_of_continuous
- \+ *lemma* compact_space.uniform_continuous_of_continuous
- \+ *lemma* compact_space_uniformity
- \+ *def* uniform_space_of_compact_t2
- \+ *lemma* unique_uniformity_of_compact_t2



## [2020-06-28 21:26:32](https://github.com/leanprover-community/mathlib/commit/3d72c97)
chore(measure_theory/outer_measure,measure_space): use `complete_lattice_of_Inf/Sup` ([#3185](https://github.com/leanprover-community/mathlib/pull/3185))
Also add a few supporting lemmas about `bsupr`/`binfi` to `order/complete_lattice`
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.coe_supr

Modified src/order/complete_lattice.lean
- \+/\- *lemma* binfi_inf
- \+ *theorem* binfi_le
- \+ *theorem* binfi_le_binfi
- \+ *theorem* bsupr_le
- \+ *theorem* bsupr_le_bsupr
- \+/\- *lemma* infi_lt_iff
- \+ *theorem* le_binfi
- \+ *theorem* le_bsupr
- \+/\- *lemma* lt_supr_iff



## [2020-06-28 13:39:01](https://github.com/leanprover-community/mathlib/commit/35fbfe0)
fix(tactic/linarith): use refine instead of apply to avoid apply bug ([#3199](https://github.com/leanprover-community/mathlib/pull/3199))
closes [#3142](https://github.com/leanprover-community/mathlib/pull/3142)
#### Estimated changes
Modified src/tactic/linarith/frontend.lean


Modified test/linarith.lean
- \+ *def* leα



## [2020-06-28 09:35:54](https://github.com/leanprover-community/mathlib/commit/da210bf)
doc(contribute/bors.md): update some outdated info ([#3209](https://github.com/leanprover-community/mathlib/pull/3209))
#### Estimated changes
Modified docs/contribute/bors.md




## [2020-06-28 08:10:20](https://github.com/leanprover-community/mathlib/commit/2f6a5f5)
feat(nat, lattice): preliminaries for Haar measure ([#3190](https://github.com/leanprover-community/mathlib/pull/3190))
PR 2/5 to put the Haar measure in mathlib. This PR: results about lattices and lattice operations on `nat`.
add some simp lemmas for `nat.find` (simplifying a proof in `sum_four_squares`)
rename `finset.sup_val` to `finset.sup_def` (it was unused). In PR 3 I will add a new declaration `finset.sup_val`
`Inf_nat_def` and `Sup_nat_def` renamed to `nat.Inf_def` and `nat.Sup_def`, and use `set.nonempty` in statement (they were unused outside that file)
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.sup_def
- \- *lemma* finset.sup_val

Modified src/data/nat/basic.lean
- \+ *lemma* nat.find_eq_zero
- \+ *lemma* nat.find_pos

Modified src/number_theory/sum_four_squares.lean


Modified src/order/bounded_lattice.lean


Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_range
- \+/\- *lemma* Sup_range
- \+/\- *def* complete_lattice_of_Inf
- \+ *lemma* infi_and'
- \+/\- *lemma* infi_apply
- \+ *lemma* infi_congr
- \+/\- *theorem* infi_congr_Prop
- \+/\- *theorem* infi_prod
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* infi_sum
- \+ *lemma* supr_and'
- \+/\- *lemma* supr_apply
- \+ *lemma* supr_congr
- \+/\- *theorem* supr_congr_Prop
- \+/\- *theorem* supr_prod
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* supr_sum

Modified src/order/conditionally_complete_lattice.lean
- \- *lemma* Inf_nat_def
- \- *lemma* Sup_nat_def
- \+ *lemma* nat.Inf_def
- \+ *lemma* nat.Inf_eq_zero
- \+ *lemma* nat.Inf_mem
- \+ *lemma* nat.Sup_def
- \+ *lemma* nat.not_mem_of_lt_Inf



## [2020-06-28 07:12:16](https://github.com/leanprover-community/mathlib/commit/4e2b46a)
feat(algebra/big_operators): add induction principles ([#3197](https://github.com/leanprover-community/mathlib/pull/3197))
add sum_induction and prod_induction
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_induction



## [2020-06-28 06:01:24](https://github.com/leanprover-community/mathlib/commit/a220286)
feat(subtype): standardize ([#3204](https://github.com/leanprover-community/mathlib/pull/3204))
Add simp lemma from x.val to coe x
Use correct ext/ext_iff naming scheme
Use coe in more places in the library
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/module.lean
- \+/\- *lemma* submodule.coe_eq_coe
- \+/\- *lemma* submodule.mk_eq_zero

Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/limits/types.lean


Modified src/computability/tm_to_partrec.lean


Modified src/data/dfinsupp.lean
- \+/\- *def* dfinsupp.mk
- \+/\- *lemma* dfinsupp.mk_add
- \+/\- *lemma* dfinsupp.mk_apply

Modified src/data/equiv/basic.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/finset.lean
- \+ *theorem* finset.range_coe
- \- *theorem* finset.range_val

Modified src/data/hash_map.lean
- \+/\- *theorem* hash_map.mk_as_list
- \+/\- *def* hash_map.mk_idx
- \+/\- *theorem* hash_map.mk_valid

Modified src/data/holor.lean


Modified src/data/list/range.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* padic_int.ext

Modified src/data/polynomial.lean


Modified src/data/real/nnreal.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/basic.lean
- \- *theorem* set.preimage_coe_eq_preimage_coe_iff
- \- *lemma* set.range_coe_subtype
- \+ *theorem* set.set_of_set
- \+ *lemma* subtype.coe_image
- \+ *theorem* subtype.coe_image_subset
- \+ *theorem* subtype.coe_image_univ
- \+/\- *theorem* subtype.image_preimage_val
- \+/\- *lemma* subtype.mem
- \+ *theorem* subtype.preimage_coe_eq_preimage_coe_iff
- \+ *lemma* subtype.range_coe
- \+ *lemma* subtype.range_coe_subtype
- \+/\- *lemma* subtype.range_val
- \+ *lemma* subtype.range_val_subtype
- \- *lemma* subtype.val_image
- \- *theorem* subtype.val_image_subset
- \- *theorem* subtype.val_image_univ
- \- *lemma* subtype.val_range

Modified src/data/set/countable.lean


Modified src/data/set/finite.lean


Modified src/data/set/function.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid/basic.lean


Modified src/data/setoid/partition.lean
- \+/\- *lemma* setoid.is_partition.pairwise_disjoint
- \+/\- *lemma* setoid.is_partition.sUnion_eq_univ

Modified src/data/subtype.lean
- \+/\- *theorem* subtype.coe_eta
- \- *lemma* subtype.coe_ext
- \+ *theorem* subtype.coe_injective
- \+/\- *theorem* subtype.coe_mk
- \+ *lemma* subtype.coe_prop
- \- *theorem* subtype.exists
- \- *lemma* subtype.ext
- \+ *lemma* subtype.ext_iff
- \+ *lemma* subtype.ext_iff_val
- \+ *lemma* subtype.ext_val
- \- *theorem* subtype.forall'
- \- *theorem* subtype.forall
- \+/\- *theorem* subtype.mk_eq_mk
- \+ *lemma* subtype.prop
- \+/\- *lemma* subtype.restrict_def
- \+/\- *lemma* subtype.val_eq_coe
- \- *lemma* subtype.val_prop'
- \+/\- *lemma* subtype.val_prop

Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/dual.lean
- \+ *lemma* vector_space.erange_coe
- \- *lemma* vector_space.eval_range

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.of_finset_basis

Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/linear_pmap.lean
- \- *lemma* subtype.coe_prop

Modified src/linear_algebra/special_linear_group.lean


Modified src/logic/embedding.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/order/complete_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/zorn.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/localization.lean
- \+/\- *lemma* localization_map.mk'_self''

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* associates.map_subtype_coe_factors'
- \- *theorem* associates.map_subtype_val_factors'

Modified src/set_theory/ordinal.lean


Modified src/tactic/subtype_instance.lean


Modified src/topology/algebra/module.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/constructions.lean
- \+ *lemma* continuous_at_subtype_coe
- \- *lemma* continuous_at_subtype_val
- \+ *lemma* embedding_subtype_coe
- \- *lemma* embedding_subtype_val
- \+ *lemma* is_closed.closed_embedding_subtype_coe
- \- *lemma* is_closed.closed_embedding_subtype_val
- \+ *lemma* is_open.is_open_map_subtype_coe
- \- *lemma* is_open.is_open_map_subtype_val
- \+ *lemma* is_open.open_embedding_subtype_coe
- \- *lemma* is_open.open_embedding_subtype_val
- \+ *lemma* map_nhds_subtype_coe_eq
- \- *lemma* map_nhds_subtype_val_eq

Modified src/topology/continuous_on.lean
- \+ *theorem* nhds_within_eq_map_subtype_coe
- \- *theorem* nhds_within_eq_map_subtype_val

Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/list.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometry_subtype_coe
- \- *lemma* isometry_subtype_val

Modified src/topology/opens.lean
- \+/\- *lemma* topological_space.opens.ext

Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+/\- *lemma* compact_iff_compact_univ

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-28 00:34:00](https://github.com/leanprover-community/mathlib/commit/dd2f1b9)
chore(scripts): update nolints.txt ([#3206](https://github.com/leanprover-community/mathlib/pull/3206))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-27 18:19:16](https://github.com/leanprover-community/mathlib/commit/247fe80)
feat(category_theory/cones): cone functoriality is fully faithful ([#3202](https://github.com/leanprover-community/mathlib/pull/3202))
The functors `cones.functoriality` and `cocones.functoriality` are fully faithful if the transformation functor is as well.
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.limits.cocones.functoriality
- \+/\- *def* category_theory.limits.cones.functoriality



## [2020-06-27 10:10:55](https://github.com/leanprover-community/mathlib/commit/adcd09d)
chore(tactic/linarith): remove final linting error ([#3196](https://github.com/leanprover-community/mathlib/pull/3196))
#### Estimated changes
Modified src/tactic/linarith/lemmas.lean




## [2020-06-27 05:25:00](https://github.com/leanprover-community/mathlib/commit/e7e9f30)
feat(set): preliminaries for Haar measure ([#3189](https://github.com/leanprover-community/mathlib/pull/3189))
`comp_sup_eq_sup_comp` is renamed `comp_sup_eq_sup_comp_of_is_total` and there is a new version that doesn't assume that the order is linear.
`set.image_injective` is renamed `function.injective.image_injective` (in the same way as the existing `function.surjective.preimage_injective`). `set.image_injective` is now an `iff`.
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.bInter_coe
- \+ *lemma* finset.bInter_finset_image
- \+ *lemma* finset.bInter_insert
- \+ *lemma* finset.bInter_inter
- \+ *theorem* finset.bInter_singleton
- \+ *lemma* finset.bUnion_finset_image
- \- *lemma* finset.bUnion_preimage_singleton
- \+ *lemma* finset.card_union_eq
- \+/\- *lemma* finset.comp_inf_eq_inf_comp
- \+ *lemma* finset.comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* finset.comp_sup_eq_sup_comp
- \+ *lemma* finset.comp_sup_eq_sup_comp_of_is_total
- \+ *lemma* finset.infi_finset_image
- \+ *lemma* finset.infi_insert
- \+ *theorem* finset.infi_singleton
- \+ *theorem* finset.infi_union
- \+ *def* finset.subtype_insert_equiv_option
- \+ *lemma* finset.supr_finset_image
- \+ *lemma* finset.supr_insert
- \+ *theorem* finset.supr_singleton
- \+/\- *theorem* finset.supr_union

Modified src/data/set/basic.lean
- \+ *lemma* function.injective.image_injective
- \+ *lemma* function.injective.nonempty_apply_iff
- \+ *lemma* function.injective.preimage_surjective
- \+ *lemma* function.surjective.image_surjective
- \+/\- *lemma* function.surjective.preimage_injective
- \+ *lemma* set.diff_inter_diff
- \+/\- *lemma* set.image_injective
- \+ *lemma* set.image_surjective
- \+ *theorem* set.preimage_id'
- \+ *lemma* set.preimage_injective
- \+ *lemma* set.preimage_preimage
- \+ *lemma* set.preimage_surjective
- \+ *theorem* set.subset.rfl

Modified src/data/set/lattice.lean
- \+ *lemma* set.disjoint.preimage
- \+ *theorem* set.disjoint_iff_inter_eq_empty
- \+ *theorem* set.disjoint_of_subset
- \+ *theorem* set.disjoint_of_subset_left
- \+ *theorem* set.disjoint_of_subset_right
- \+ *lemma* set.subset_diff

Modified src/logic/embedding.lean


Modified src/logic/function/basic.lean
- \+/\- *lemma* function.injective.ne
- \+ *lemma* function.injective.ne_iff

Modified src/topology/metric_space/basic.lean




## [2020-06-27 03:21:26](https://github.com/leanprover-community/mathlib/commit/8413b3f)
feat(analysis/normed_space/real_inner_product): sums and bilinear form ([#3187](https://github.com/leanprover-community/mathlib/pull/3187))
Add lemmas about distributing the inner product into a sum.  The
natural approach to proving those seems to be to use the corresponding
lemmas for bilinear forms, so also add a construction of a `bilin_form
ℝ α` from the inner product.
I realise this might all get refactored later if inner products get
refactored to cover the case of complex inner products as well.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *def* bilin_form_of_inner
- \+ *lemma* inner_sum
- \+ *lemma* sum_inner



## [2020-06-27 02:52:56](https://github.com/leanprover-community/mathlib/commit/6ed3325)
feat(category_theory/limits): limit of point iso ([#3188](https://github.com/leanprover-community/mathlib/pull/3188))
Prove a cone is a limit given that the canonical morphism from it to a limiting cone is an iso.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.of_point_iso
- \+ *def* category_theory.limits.is_limit.of_point_iso

Modified src/category_theory/reflect_isomorphisms.lean


Modified src/topology/category/Top/limits.lean




## [2020-06-27 00:32:10](https://github.com/leanprover-community/mathlib/commit/c6fd69d)
chore(scripts): update nolints.txt ([#3192](https://github.com/leanprover-community/mathlib/pull/3192))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-26 23:51:42](https://github.com/leanprover-community/mathlib/commit/78d6780)
chore(category_theory/pempty): use discrete pempty instead of a special pempty category ([#3191](https://github.com/leanprover-community/mathlib/pull/3191))
Use `discrete pempty` instead of a specialised `pempty` category.
Motivation: Since we have a good API for `discrete` categories, there doesn't seem to be much point in defining a specialised `pempty` category with an equivalence, instead we might as well just use `discrete pempty`.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/pempty.lean
- \+/\- *def* category_theory.functor.empty
- \+ *lemma* category_theory.functor.empty_ext'
- \+/\- *def* category_theory.functor.empty_ext
- \+ *def* category_theory.functor.unique_from_empty



## [2020-06-26 16:35:02](https://github.com/leanprover-community/mathlib/commit/2d270ff)
feat(data/set/basic): +2 lemmas, +2 `simp` attrs ([#3182](https://github.com/leanprover-community/mathlib/pull/3182))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.image_diff
- \+ *theorem* set.subset_image_diff
- \+ *theorem* subtype.image_preimage_coe
- \+/\- *theorem* subtype.image_preimage_val



## [2020-06-26 15:11:50](https://github.com/leanprover-community/mathlib/commit/ef62d1c)
chore(*): last preparations for Heine ([#3179](https://github.com/leanprover-community/mathlib/pull/3179))
This is hopefully the last preparatory PR before we study compact uniform spaces. It has almost no mathematical content, except that I define `uniform_continuous_on`, and check it is equivalent to uniform continuity for the induced uniformity.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.diagonal_eq_range
- \+ *lemma* set.mem_diagonal

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_split
- \+ *lemma* infi_split_single
- \+ *lemma* supr_split
- \+ *lemma* supr_split_single

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_const_of_mem
- \+ *lemma* filter.comap_const_of_not_mem
- \+ *lemma* filter.comap_prod
- \+ *lemma* filter.le_iff_forall_inf_principal_compl
- \+ *lemma* filter.mem_iff_inf_principal_compl
- \+ *lemma* filter.principal_le_iff
- \+ *lemma* filter.subtype_coe_map_comap_prod

Modified src/topology/basic.lean
- \+ *lemma* cluster_pt.of_inf_left
- \+ *lemma* cluster_pt.of_inf_right
- \+ *lemma* cluster_pt_iff
- \- *lemma* cluster_pt_of_inf_left
- \- *lemma* cluster_pt_of_inf_right
- \+ *theorem* mem_closure_iff_cluster_pt
- \+ *lemma* subset_interior_iff_nhds

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.uniform_continuous_on_iff

Modified src/topology/separation.lean
- \+ *lemma* disjoint_nested_nhds

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* nhds_eq_comap_uniformity_aux
- \+ *lemma* nhds_le_uniformity
- \+ *def* uniform_continuous_on
- \+ *lemma* uniform_continuous_on_iff_restrict

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* eq_of_uniformity_inf_nhds



## [2020-06-26 13:39:18](https://github.com/leanprover-community/mathlib/commit/6624509)
feat(algebra/big_operators): telescoping sums ([#3184](https://github.com/leanprover-community/mathlib/pull/3184))
generalize sum_range_sub_of_monotone, a theorem about nats, to a theorem about commutative groups
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_range_div
- \+ *lemma* finset.sum_range_sub



## [2020-06-26 09:59:19](https://github.com/leanprover-community/mathlib/commit/5b97da6)
feat(ring_theory/matrix_equiv_tensor): matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) ([#3177](https://github.com/leanprover-community/mathlib/pull/3177))
When `A` is an `R`-algebra, matrices over `A` are equivalent (as an algebra) to `A ⊗[R] matrix n n R`.
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* ring_hom.to_fun_eq_coe

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.mul_mul_left
- \+ *lemma* matrix.mul_mul_right
- \+ *def* matrix.scalar
- \+ *lemma* ring_hom.map_matrix_mul

Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* tensor_product.sum_tmul
- \+ *lemma* tensor_product.tmul_sum

Modified src/logic/basic.lean
- \+ *lemma* apply_dite
- \+ *lemma* apply_ite
- \+ *lemma* dite_apply
- \+ *lemma* ite_apply

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.symm_symm
- \+ *lemma* algebra.algebra_map_eq_smul_one

Added src/ring_theory/matrix_algebra.lean
- \+ *lemma* algebra_map_matrix_val
- \+ *def* matrix_equiv_tensor.equiv
- \+ *def* matrix_equiv_tensor.inv_fun
- \+ *lemma* matrix_equiv_tensor.inv_fun_add
- \+ *lemma* matrix_equiv_tensor.inv_fun_algebra_map
- \+ *lemma* matrix_equiv_tensor.inv_fun_smul
- \+ *lemma* matrix_equiv_tensor.inv_fun_zero
- \+ *lemma* matrix_equiv_tensor.left_inv
- \+ *lemma* matrix_equiv_tensor.right_inv
- \+ *def* matrix_equiv_tensor.to_fun
- \+ *def* matrix_equiv_tensor.to_fun_alg_hom
- \+ *lemma* matrix_equiv_tensor.to_fun_alg_hom_apply
- \+ *def* matrix_equiv_tensor.to_fun_bilinear
- \+ *def* matrix_equiv_tensor.to_fun_linear
- \+ *def* matrix_equiv_tensor.to_fun_right_linear
- \+ *def* matrix_equiv_tensor
- \+ *lemma* matrix_equiv_tensor_apply
- \+ *lemma* matrix_equiv_tensor_apply_symm

Modified src/ring_theory/tensor_product.lean




## [2020-06-26 07:16:55](https://github.com/leanprover-community/mathlib/commit/3cfc0e7)
chore(category/*): linting ([#3178](https://github.com/leanprover-community/mathlib/pull/3178))
Some linting work on `category_theory/`.
#### Estimated changes
Modified src/algebra/category/Group/basic.lean


Modified src/category_theory/category/Cat.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/category_theory/conj.lean


Modified src/category_theory/const.lean
- \+/\- *lemma* category_theory.functor.const.op_obj_unop_hom_app
- \+/\- *lemma* category_theory.functor.const.op_obj_unop_inv_app

Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean
- \- *def* category_theory.functor.ulift_down
- \- *def* category_theory.functor.ulift_up

Modified src/category_theory/functor_category.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/natural_isomorphism.lean
- \- *def* category_theory.functor.ulift_down_up
- \- *def* category_theory.functor.ulift_up_down

Modified src/category_theory/natural_transformation.lean
- \+/\- *structure* category_theory.nat_trans

Modified src/category_theory/products/associator.lean
- \+/\- *def* category_theory.prod.associator
- \+/\- *def* category_theory.prod.inverse_associator

Modified src/category_theory/punit.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/sums/associator.lean
- \+/\- *def* category_theory.sum.associator
- \+/\- *def* category_theory.sum.inverse_associator



## [2020-06-26 06:18:21](https://github.com/leanprover-community/mathlib/commit/c3923e3)
feat(data/fintype): trunc_sigma_of_exists ([#3166](https://github.com/leanprover-community/mathlib/pull/3166))
When working over a `fintype`, you can lift existential statements to `trunc` statements.
This PR adds:
```
def trunc_of_nonempty_fintype {α} (h : nonempty α) [fintype α] : trunc α
def trunc_sigma_of_exists {α} [fintype α] {P : α → Prop} [decidable_pred P] (h : ∃ a, P a) : trunc (Σ' a, P a)
```
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *def* trunc_of_card_pos
- \+ *def* trunc_of_multiset_exists_mem
- \+ *def* trunc_of_nonempty_fintype
- \+ *def* trunc_sigma_of_exists



## [2020-06-26 01:23:06](https://github.com/leanprover-community/mathlib/commit/616cb5e)
chore(category_theory/equivalence) explicit transitivity transformation ([#3176](https://github.com/leanprover-community/mathlib/pull/3176))
Modifies the construction of the transitive equivalence to be explicit in what exactly the natural transformations are.
The motivation for this is two-fold: firstly we get auto-generated projection lemmas for extracting the functor and inverse, and the natural transformations aren't obscured through `adjointify_η`.
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+/\- *def* category_theory.equivalence.trans



## [2020-06-26 00:34:33](https://github.com/leanprover-community/mathlib/commit/abae5a3)
chore(scripts): update nolints.txt ([#3174](https://github.com/leanprover-community/mathlib/pull/3174))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-25 23:10:54](https://github.com/leanprover-community/mathlib/commit/43a2b24)
feat(tactic/abel) teach abel to gsmul_zero ([#3173](https://github.com/leanprover-community/mathlib/pull/3173))
As reported by Heather Macbeth in:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/limitations.20of.20.60abel.60
`abel` was not negating zero to zero.
#### Estimated changes
Modified src/tactic/abel.lean


Modified test/abel.lean




## [2020-06-25 16:36:04](https://github.com/leanprover-community/mathlib/commit/db7a53a)
refactor(ring_theory/ideals): make local_ring a prop class ([#3171](https://github.com/leanprover-community/mathlib/pull/3171))
#### Estimated changes
Modified src/ring_theory/ideals.lean
- \- *def* is_local_ring
- \- *def* local_of_is_local_ring
- \+ *lemma* local_of_nonunits_ideal
- \- *def* local_of_nonunits_ideal
- \+ *lemma* local_of_unique_max_ideal
- \- *def* local_of_unique_max_ideal
- \- *def* local_of_unit_or_unit_one_sub
- \+ *def* local_ring.maximal_ideal
- \+ *lemma* local_ring.mem_maximal_ideal
- \- *lemma* local_ring.mem_nonunits_ideal
- \- *def* local_ring.nonunits_ideal
- \+/\- *def* local_ring.residue_field
- \+/\- *lemma* map_nonunit

Modified src/ring_theory/power_series.lean
- \- *lemma* mv_power_series.is_local_ring
- \- *lemma* power_series.is_local_ring



## [2020-06-25 15:51:37](https://github.com/leanprover-community/mathlib/commit/afc1c24)
feat(category/default): comp_dite ([#3163](https://github.com/leanprover-community/mathlib/pull/3163))
Adds lemmas to "distribute" composition over `if` statements.
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+ *lemma* category_theory.comp_dite
- \+ *lemma* category_theory.dite_comp



## [2020-06-25 15:51:35](https://github.com/leanprover-community/mathlib/commit/c6f629b)
feat(category_theory/limits): isos from reindexing limits ([#3100](https://github.com/leanprover-community/mathlib/pull/3100))
Three related constructions which are helpful when identifying "the same limit written different ways".
1. The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
2. We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.
3. The chosen limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocones.equivalence_of_reindexing
- \+ *lemma* category_theory.limits.cocones.equivalence_of_reindexing_functor_obj
- \+ *def* category_theory.limits.cocones.whiskering
- \+ *def* category_theory.limits.cocones.whiskering_equivalence
- \+ *def* category_theory.limits.cones.equivalence_of_reindexing
- \+ *lemma* category_theory.limits.cones.equivalence_of_reindexing_functor_obj
- \+ *def* category_theory.limits.cones.whiskering
- \+ *def* category_theory.limits.cones.whiskering_equivalence

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.colim_map
- \+ *def* category_theory.limits.has_colimit.iso_of_equivalence
- \+ *lemma* category_theory.limits.has_colimit.iso_of_equivalence_π
- \+ *def* category_theory.limits.has_colimit.iso_of_nat_iso
- \+ *lemma* category_theory.limits.has_colimit.iso_of_nat_iso_hom_π
- \+ *def* category_theory.limits.has_limit.iso_of_equivalence
- \+ *lemma* category_theory.limits.has_limit.iso_of_equivalence_π
- \+ *def* category_theory.limits.has_limit.iso_of_nat_iso
- \+ *lemma* category_theory.limits.has_limit.iso_of_nat_iso_hom_π
- \+ *def* category_theory.limits.is_colimit.cocone_points_iso_of_equivalence
- \+ *def* category_theory.limits.is_colimit.cocone_points_iso_of_nat_iso
- \+ *def* category_theory.limits.is_colimit.whisker_equivalence
- \+ *def* category_theory.limits.is_limit.cone_points_iso_of_equivalence
- \+ *def* category_theory.limits.is_limit.cone_points_iso_of_nat_iso
- \+ *def* category_theory.limits.is_limit.whisker_equivalence
- \+ *def* category_theory.limits.lim_map
- \+ *lemma* category_theory.limits.lim_map_π
- \+ *lemma* category_theory.limits.ι_colim_map



## [2020-06-25 14:32:01](https://github.com/leanprover-community/mathlib/commit/158e84a)
feat(*): bump to Lean 3.16.5 ([#3170](https://github.com/leanprover-community/mathlib/pull/3170))
There should be no changes required in mathlib.
#### Estimated changes
Modified leanpkg.toml




## [2020-06-25 13:06:57](https://github.com/leanprover-community/mathlib/commit/7d331eb)
chore(*): assorted lemmas about `set` and `finset` ([#3158](https://github.com/leanprover-community/mathlib/pull/3158))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.bUnion_coe
- \+ *lemma* finset.bUnion_preimage_singleton

Modified src/data/indicator_function.lean
- \+ *lemma* set.eq_on_indicator
- \+ *lemma* set.indicator_preimage_of_not_mem
- \+ *lemma* set.mem_range_indicator

Modified src/data/set/basic.lean
- \+ *theorem* set.preimage_const
- \+ *theorem* set.preimage_const_of_mem
- \+ *theorem* set.preimage_const_of_not_mem
- \+/\- *theorem* set.preimage_inter_range
- \+ *lemma* set.preimage_range
- \+ *theorem* set.preimage_range_inter
- \+ *theorem* set.preimage_singleton_eq_empty
- \+ *theorem* set.preimage_singleton_nonempty
- \+ *theorem* set.sep_mem_eq

Modified src/data/set/disjointed.lean
- \+ *theorem* pairwise_disjoint_fiber
- \+ *theorem* set.pairwise_on_univ

Modified src/data/set/lattice.lean
- \+ *lemma* set.bUnion_preimage_singleton
- \+ *lemma* set.bUnion_range_preimage_singleton
- \+ *theorem* set.pairwise_on_disjoint_fiber

Modified src/logic/basic.lean
- \+ *lemma* ite_eq_iff

Modified src/measure_theory/integration.lean




## [2020-06-25 13:06:55](https://github.com/leanprover-community/mathlib/commit/80a0877)
feat(category_theory): show a pullback of a regular mono is regular ([#2780](https://github.com/leanprover-community/mathlib/pull/2780))
And adds two methods for constructing limits which I've found much easier to use in practice.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.cofork.is_colimit.mk'
- \+ *def* category_theory.limits.fork.is_limit.mk'

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.pullback_cone.flip_is_limit
- \+ *def* category_theory.limits.pullback_cone.is_limit.mk'
- \+ *def* category_theory.limits.pushout_cocone.flip_is_colimit
- \+ *def* category_theory.limits.pushout_cocone.is_colimit.mk'

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* category_theory.normal_of_is_pullback_fst_of_normal
- \+ *def* category_theory.normal_of_is_pullback_snd_of_normal
- \+ *def* category_theory.normal_of_is_pushout_fst_of_normal
- \+ *def* category_theory.normal_of_is_pushout_snd_of_normal
- \+ *def* category_theory.regular_of_is_pullback_fst_of_regular
- \+ *def* category_theory.regular_of_is_pullback_snd_of_regular
- \+ *def* category_theory.regular_of_is_pushout_fst_of_regular
- \+ *def* category_theory.regular_of_is_pushout_snd_of_regular



## [2020-06-25 12:26:52](https://github.com/leanprover-community/mathlib/commit/3f868fa)
feat(filter, topology): cluster_pt and principal notation, redefine compactness ([#3160](https://github.com/leanprover-community/mathlib/pull/3160))
This PR implements what is discussed in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Picking.20sides. It introduces a notation for `filter.principal`, defines `cluster_pt` and uses it to redefine compactness in a way which makes the library more consistent by always putting the neighborhood filter on the left, as in the description of closures and `nhds_within`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *def* filter.at_bot
- \+/\- *def* filter.at_top
- \+ *lemma* filter.inf_map_at_top_ne_bot_iff
- \- *lemma* filter.map_at_top_inf_ne_bot_iff

Modified src/order/filter/bases.lean
- \+/\- *lemma* filter.is_countably_generated_of_seq
- \+/\- *lemma* filter.is_countably_generated_seq
- \+/\- *lemma* filter_basis.eq_infi_principal

Modified src/order/filter/basic.lean
- \+/\- *theorem* filter.comap_principal
- \+/\- *lemma* filter.inf_principal
- \+/\- *lemma* filter.inf_principal_eq_bot
- \+/\- *lemma* filter.is_compl_principal
- \+/\- *lemma* filter.join_principal_eq_Sup
- \+/\- *lemma* filter.le_principal_iff
- \+/\- *lemma* filter.mem_principal_self
- \+/\- *lemma* filter.mem_principal_sets
- \+/\- *lemma* filter.mem_sets_of_eq_bot
- \+/\- *lemma* filter.monotone_principal
- \+/\- *lemma* filter.principal_empty
- \+/\- *lemma* filter.principal_eq_bot_iff
- \+/\- *lemma* filter.principal_eq_iff_eq
- \+/\- *lemma* filter.principal_mono
- \+/\- *lemma* filter.principal_ne_bot_iff
- \+/\- *lemma* filter.principal_univ
- \+/\- *lemma* filter.pure_eq_principal
- \+/\- *lemma* filter.sup_principal
- \+/\- *lemma* filter.supr_principal

Modified src/order/filter/countable_Inter.lean


Modified src/order/filter/extr.lean
- \+/\- *def* is_extr_on
- \+/\- *def* is_max_on
- \+/\- *def* is_min_on

Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift_principal2

Modified src/order/filter/partial.lean


Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* filter.le_of_ultrafilter

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* filter.is_bounded_principal

Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean
- \+/\- *lemma* topological_space.first_countable_topology.tendsto_subseq

Modified src/topology/basic.lean
- \+ *lemma* closure_eq_cluster_pts
- \- *lemma* closure_eq_nhds
- \+ *lemma* cluster_pt.mono
- \+ *lemma* cluster_pt.of_le_nhds
- \+ *lemma* cluster_pt.of_nhds_le
- \+ *def* cluster_pt
- \+ *lemma* cluster_pt_of_inf_left
- \+ *lemma* cluster_pt_of_inf_right
- \+/\- *lemma* interior_eq_nhds
- \+/\- *lemma* is_closed_iff_nhds
- \+/\- *lemma* is_open_iff_nhds
- \+ *def* map_cluster_pt
- \+ *lemma* map_cluster_pt_iff
- \+ *lemma* map_cluster_pt_of_comp
- \+/\- *def* nhds
- \+/\- *lemma* nhds_def
- \+/\- *lemma* nhds_le_of_le

Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean
- \+/\- *def* nhds_within

Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.nhds_of_ne_top
- \+/\- *lemma* ennreal.nhds_top
- \+/\- *lemma* ennreal.nhds_zero

Modified src/topology/local_extr.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.uniformity_edist

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.nhds_eq

Modified src/topology/order.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+/\- *def* compact

Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* refl_le_uniformity

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* is_complete

Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-25 07:40:04](https://github.com/leanprover-community/mathlib/commit/e7db701)
feat(category/adjunction): missing simp lemmas ([#3168](https://github.com/leanprover-community/mathlib/pull/3168))
Just two missing simp lemmas.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* category_theory.functor.left_adjoint_of_is_equivalence
- \+ *lemma* category_theory.functor.right_adjoint_of_is_equivalence



## [2020-06-25 07:40:02](https://github.com/leanprover-community/mathlib/commit/d86f1c8)
chore(category/discrete): missing simp lemmas ([#3165](https://github.com/leanprover-community/mathlib/pull/3165))
Some obvious missing `simp` lemmas for `discrete.nat_iso`.
#### Estimated changes
Modified src/category_theory/discrete_category.lean
- \+ *lemma* category_theory.discrete.nat_iso_app
- \+ *lemma* category_theory.discrete.nat_iso_hom_app
- \+ *lemma* category_theory.discrete.nat_iso_inv_app



## [2020-06-25 07:40:01](https://github.com/leanprover-community/mathlib/commit/266d316)
chore(category/equivalence): cleanup ([#3164](https://github.com/leanprover-community/mathlib/pull/3164))
Previously some "shorthands" like
```
@[simp] def unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse := e.unit_iso.hom
```
had been added in `equivalence.lean`.
These were a bit annoying, as even though they were marked as `simp` sometimes the syntactic difference between `e.unit` and `e.unit_iso.hom` would get in the way of tactics working.
This PR turns these into abbreviations.
This comes at a slight cost: apparently expressions like `{ X := X }.Y` won't reduce when `.Y` is an abbreviation for `.X.Z`, so we add some `@[simp]` lemmas back in to achieve this.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/equivalence.lean
- \+ *abbreviation* category_theory.equivalence.counit
- \- *def* category_theory.equivalence.counit
- \- *lemma* category_theory.equivalence.counit_def
- \+ *abbreviation* category_theory.equivalence.counit_inv
- \- *def* category_theory.equivalence.counit_inv
- \- *lemma* category_theory.equivalence.counit_inv_def
- \+ *lemma* category_theory.equivalence.equivalence_mk'_counit
- \+ *lemma* category_theory.equivalence.equivalence_mk'_counit_inv
- \+ *lemma* category_theory.equivalence.equivalence_mk'_unit
- \+ *lemma* category_theory.equivalence.equivalence_mk'_unit_inv
- \+ *lemma* category_theory.equivalence.functor_as_equivalence
- \+ *lemma* category_theory.equivalence.functor_inv
- \+/\- *lemma* category_theory.equivalence.functor_unit_comp
- \+ *lemma* category_theory.equivalence.inverse_as_equivalence
- \+ *lemma* category_theory.equivalence.inverse_inv
- \+ *abbreviation* category_theory.equivalence.unit
- \- *def* category_theory.equivalence.unit
- \- *lemma* category_theory.equivalence.unit_def
- \+ *abbreviation* category_theory.equivalence.unit_inv
- \- *def* category_theory.equivalence.unit_inv
- \- *lemma* category_theory.equivalence.unit_inv_def
- \+ *lemma* category_theory.functor.as_equivalence_functor
- \+ *lemma* category_theory.functor.as_equivalence_inverse
- \+ *lemma* category_theory.functor.inv_inv



## [2020-06-25 07:39:59](https://github.com/leanprover-community/mathlib/commit/e8187ac)
feat(category/preadditive): comp_sum ([#3162](https://github.com/leanprover-community/mathlib/pull/3162))
Adds lemmas to distribute composition over `finset.sum`, in a preadditive category.
#### Estimated changes
Modified src/category_theory/preadditive.lean
- \+ *lemma* category_theory.preadditive.comp_sum
- \+ *lemma* category_theory.preadditive.sum_comp



## [2020-06-25 06:32:59](https://github.com/leanprover-community/mathlib/commit/3875012)
feat(data/quot): add `map'`, `hrec_on'`, and `hrec_on₂'` ([#3148](https://github.com/leanprover-community/mathlib/pull/3148))
Also add a few `simp` lemmas
#### Estimated changes
Modified src/data/quot.lean
- \+/\- *theorem* quotient.choice_eq
- \+ *lemma* quotient.hrec_on'_mk'
- \+ *lemma* quotient.hrec_on₂'_mk'
- \+ *lemma* quotient.map'_mk'
- \+ *lemma* quotient.map_mk
- \+ *lemma* quotient.map₂'_mk'



## [2020-06-25 05:38:59](https://github.com/leanprover-community/mathlib/commit/553e453)
feat(algebra/big_operators): prod_dite_eq ([#3167](https://github.com/leanprover-community/mathlib/pull/3167))
Add `finset.prod_dite_eq`, the dependent analogue of `finset.prod_ite_eq`, and its primed version for the flipped equality.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_dite_eq'
- \+ *lemma* finset.prod_dite_eq



## [2020-06-25 04:35:29](https://github.com/leanprover-community/mathlib/commit/8f04a92)
refactor(algebra/*): small API fixes ([#3157](https://github.com/leanprover-community/mathlib/pull/3157))
## Changes to `canonically_ordered_comm_semiring`
* in the definition of `canonically_ordered_comm_semiring` replace
  `mul_eq_zero_iff` with `eq_zero_or_eq_zero_of_mul_eq_zero`; the other
  implication is always true because of `[semiring]`;
* add instance `canonically_ordered_comm_semiring.to_no_zero_divisors`;
## Changes to `with_top`
* use `to_additive` for `with_top.has_one`, `with_top.coe_one` etc;
* move `with_top.coe_ne_zero` to `algebra.ordered_group`;
* add `with_top.has_add`, make `coe_add`, `coe_bit*` require only `[has_add α]`;
* use proper instances for lemmas about multiplication in `with_top`, not
  just `canonically_ordered_comm_semiring` for everything;
## Changes to `associates`
* merge `associates.mk_zero_eq` and `associates.mk_eq_zero_iff_eq_zero` into
  `associates.mk_eq_zero`;
* drop `associates.mul_zero`, `associates.zero_mul`, `associates.zero_ne_one`,
  and `associates.mul_eq_zero_iff` in favor of typeclass instances;
## Misc changes
* drop `mul_eq_zero_iff_eq_zero_or_eq_zero` in favor of `mul_eq_zero`;
* drop `ennreal.mul_eq_zero` in favor of `mul_eq_zero` from instance.
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *theorem* associates.mk_eq_zero
- \- *theorem* associates.mk_eq_zero_iff_eq_zero
- \- *theorem* associates.mk_zero_eq
- \- *theorem* associates.mul_eq_zero_iff
- \- *theorem* associates.mul_zero
- \- *theorem* associates.zero_ne_one

Modified src/algebra/big_operators.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* with_top.coe_add
- \+/\- *lemma* with_top.coe_bit0
- \+/\- *lemma* with_top.coe_bit1
- \+/\- *lemma* with_top.coe_eq_one
- \- *lemma* with_top.coe_eq_zero
- \+/\- *lemma* with_top.coe_one
- \- *lemma* with_top.coe_zero
- \+ *theorem* with_top.one_eq_coe
- \+ *theorem* with_top.one_ne_top
- \+ *theorem* with_top.top_ne_one

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* with_top.coe_mul
- \- *theorem* with_top.top_ne_zero
- \- *theorem* with_top.zero_eq_coe
- \- *theorem* with_top.zero_ne_top

Modified src/algebra/ring.lean
- \- *theorem* eq_zero_of_mul_eq_self_left'
- \+ *theorem* eq_zero_of_mul_eq_self_left
- \- *lemma* eq_zero_of_mul_eq_self_left
- \- *theorem* eq_zero_of_mul_eq_self_right'
- \+ *theorem* eq_zero_of_mul_eq_self_right
- \- *lemma* eq_zero_of_mul_eq_self_right
- \- *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero

Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* with_top.coe_nat

Modified src/data/padics/padic_integers.lean


Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.mul_eq_zero

Modified src/data/real/nnreal.lean


Modified src/number_theory/dioph.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/topology/instances/ennreal.lean




## [2020-06-25 01:09:38](https://github.com/leanprover-community/mathlib/commit/e1a72b5)
feat(archive/100-theorems-list/73_ascending_descending_sequences): Erdős–Szekeres ([#3074](https://github.com/leanprover-community/mathlib/pull/3074))
Prove the Erdős-Szekeres theorem on ascending or descending sequences
#### Estimated changes
Added archive/100-theorems-list/73_ascending_descending_sequences.lean
- \+ *theorem* erdos_szekeres

Modified src/data/nat/basic.lean
- \+ *theorem* nat.succ_injective

Modified src/order/basic.lean
- \+ *lemma* injective_of_lt_imp_ne
- \+ *def* strict_mono_decr_on
- \+ *def* strict_mono_incr_on



## [2020-06-25 00:34:07](https://github.com/leanprover-community/mathlib/commit/5c7e1a2)
chore(scripts): update nolints.txt ([#3161](https://github.com/leanprover-community/mathlib/pull/3161))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-24 19:51:54](https://github.com/leanprover-community/mathlib/commit/2aa08c1)
chore(algebra/ordered_group): merge `add_le_add'` with `add_le_add` ([#3159](https://github.com/leanprover-community/mathlib/pull/3159))
Also drop `mul_le_mul''` (was a weaker version of `mul_le_mul'`).
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/group_power.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* mul_le_mul''

Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/data/polynomial.lean


Modified src/data/real/ennreal.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/order/filter/extr.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/lipschitz.lean




## [2020-06-24 14:36:47](https://github.com/leanprover-community/mathlib/commit/04a5bdb)
feat(linear_algebra/finsupp_vector_space): is_basis.tensor_product ([#3147](https://github.com/leanprover-community/mathlib/pull/3147))
If `b : ι → M` and `c : κ → N` are bases then so is `λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.sum_smul_index'

Modified src/linear_algebra/basis.lean
- \+ *theorem* module_equiv_finsupp_apply_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.coe_lsum
- \+ *theorem* finsupp.dom_lcongr_single
- \+ *def* finsupp.lcongr
- \+ *theorem* finsupp.lcongr_single
- \+/\- *def* finsupp.lsum
- \+/\- *theorem* finsupp.lsum_apply
- \+ *theorem* finsupp.lsum_single
- \+ *def* finsupp_lequiv_direct_sum
- \+ *theorem* finsupp_lequiv_direct_sum_single
- \+ *theorem* finsupp_lequiv_direct_sum_symm_lof
- \+ *def* finsupp_tensor_finsupp
- \+ *theorem* finsupp_tensor_finsupp_single
- \+ *theorem* finsupp_tensor_finsupp_symm_single

Modified src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* finsupp.is_basis.tensor_product
- \+/\- *lemma* finsupp.is_basis_single
- \+ *lemma* finsupp.is_basis_single_one

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* tensor_product.congr_tmul
- \+ *theorem* tensor_product.direct_sum_lof_tmul_lof



## [2020-06-24 10:22:57](https://github.com/leanprover-community/mathlib/commit/dd9b5c6)
refactor(tactic/linarith): big refactor and docs ([#3113](https://github.com/leanprover-community/mathlib/pull/3113))
This PR:
* Splits `linarith` into multiple files for organizational purposes
* Uses the general `zify` and `cancel_denom` tactics instead of weaker custom versions
* Refactors many components of `linarith`, in particular,
* Modularizes `linarith` preprocessing, so that users can insert custom steps
* Implements `nlinarith` preprocessing as such a custom step, so it happens at the correct point of the preprocessing stage
* Better encapsulates the FM elimination module, to make it easier to plug in alternate oracles if/when they exist
* Docs, docs, docs
The change to zification means that some goals which involved multiplication of natural numbers will no longer be solved. However, others are now in scope. `nlinarith` is a possible drop-in replacement; otherwise, generalize the product of naturals to a single natural, and `linarith` should still succeed.
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified src/data/list/defs.lean
- \+ *def* list.mfind
- \+ *def* list.mmap_upper_triangle

Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/core.lean


Deleted src/tactic/linarith.lean
- \- *lemma* linarith.add_subst
- \- *def* linarith.comp.vars
- \- *structure* linarith.comp
- \- *def* linarith.comp_source.to_string
- \- *inductive* linarith.comp_source
- \- *lemma* linarith.div_subst
- \- *lemma* linarith.eq_of_eq_of_eq
- \- *lemma* linarith.eq_of_not_lt_of_not_gt
- \- *def* linarith.ineq.cmp
- \- *def* linarith.ineq.max
- \- *def* linarith.ineq.to_string
- \- *inductive* linarith.ineq
- \- *lemma* linarith.int.coe_nat_bit0
- \- *lemma* linarith.int.coe_nat_bit0_mul
- \- *lemma* linarith.int.coe_nat_bit1
- \- *lemma* linarith.int.coe_nat_bit1_mul
- \- *lemma* linarith.int.coe_nat_mul_bit0
- \- *lemma* linarith.int.coe_nat_mul_bit1
- \- *lemma* linarith.int.coe_nat_mul_one
- \- *lemma* linarith.int.coe_nat_mul_zero
- \- *lemma* linarith.int.coe_nat_one_mul
- \- *lemma* linarith.int.coe_nat_zero_mul
- \- *lemma* linarith.le_of_eq_of_le
- \- *lemma* linarith.le_of_le_of_eq
- \- *def* linarith.linexp.cmp
- \- *def* linarith.linexp.contains
- \- *def* linarith.linexp.get
- \- *def* linarith.linexp.scale
- \- *def* linarith.linexp.vars
- \- *def* linarith.linexp.zfind
- \- *def* linarith.linexp
- \- *lemma* linarith.lt_of_eq_of_lt
- \- *lemma* linarith.lt_of_lt_of_eq
- \- *lemma* linarith.mul_eq
- \- *lemma* linarith.mul_neg
- \- *lemma* linarith.mul_nonpos
- \- *lemma* linarith.mul_subst
- \- *lemma* linarith.mul_zero_eq
- \- *lemma* linarith.nat_eq_subst
- \- *lemma* linarith.nat_le_subst
- \- *lemma* linarith.nat_lt_subst
- \- *lemma* linarith.neg_subst
- \- *lemma* linarith.sub_into_lt
- \- *lemma* linarith.sub_subst
- \- *lemma* linarith.zero_mul_eq

Added src/tactic/linarith/datatypes.lean
- \+ *def* linarith.comp.coeff_of
- \+ *def* linarith.comp.scale
- \+ *def* linarith.comp.vars
- \+ *structure* linarith.comp
- \+ *def* linarith.ineq.cmp
- \+ *def* linarith.ineq.max
- \+ *def* linarith.ineq.to_string
- \+ *inductive* linarith.ineq
- \+ *def* linarith.linexp.cmp
- \+ *def* linarith.linexp.contains
- \+ *def* linarith.linexp.get
- \+ *def* linarith.linexp.scale
- \+ *def* linarith.linexp.vars
- \+ *def* linarith.linexp.zfind
- \+ *def* linarith.linexp

Added src/tactic/linarith/default.lean


Added src/tactic/linarith/elimination.lean
- \+ *def* linarith.comp_source.to_string
- \+ *inductive* linarith.comp_source

Added src/tactic/linarith/frontend.lean


Added src/tactic/linarith/lemmas.lean
- \+ *lemma* linarith.eq_of_eq_of_eq
- \+ *lemma* linarith.eq_of_not_lt_of_not_gt
- \+ *lemma* linarith.int.coe_nat_bit0
- \+ *lemma* linarith.int.coe_nat_bit0_mul
- \+ *lemma* linarith.int.coe_nat_bit1
- \+ *lemma* linarith.int.coe_nat_bit1_mul
- \+ *lemma* linarith.int.coe_nat_mul_bit0
- \+ *lemma* linarith.int.coe_nat_mul_bit1
- \+ *lemma* linarith.int.coe_nat_mul_one
- \+ *lemma* linarith.int.coe_nat_mul_zero
- \+ *lemma* linarith.int.coe_nat_one_mul
- \+ *lemma* linarith.int.coe_nat_zero_mul
- \+ *lemma* linarith.le_of_eq_of_le
- \+ *lemma* linarith.le_of_le_of_eq
- \+ *lemma* linarith.lt_of_eq_of_lt
- \+ *lemma* linarith.lt_of_lt_of_eq
- \+ *lemma* linarith.mul_eq
- \+ *lemma* linarith.mul_neg
- \+ *lemma* linarith.mul_nonpos
- \+ *lemma* linarith.mul_zero_eq
- \+ *lemma* linarith.nat_eq_subst
- \+ *lemma* linarith.nat_le_subst
- \+ *lemma* linarith.nat_lt_subst
- \+ *lemma* linarith.zero_mul_eq

Added src/tactic/linarith/parsing.lean


Added src/tactic/linarith/preprocessing.lean


Added src/tactic/linarith/verification.lean


Modified src/tactic/zify.lean


Modified test/linarith.lean
- \+ *lemma* norm_eq_zero_iff
- \+ *lemma* norm_nonpos_left
- \+ *lemma* norm_nonpos_right



## [2020-06-24 09:30:51](https://github.com/leanprover-community/mathlib/commit/194edc1)
feat(ring_theory/localization): integral closure in field extension ([#3096](https://github.com/leanprover-community/mathlib/pull/3096))
Let `A` be an integral domain with field of fractions `K` and `L` a finite extension of `K`. This PR shows the integral closure of `A` in `L` has fraction field `L`. If those definitions existed, the corollary is that the ring of integers of a number field is a number ring.
For this, we need two constructions on polynomials:
 * If `p` is a nonzero polynomial, `integral_normalization p` is a monic polynomial with roots `z * a` for `z` a root of `p` and `a` the leading coefficient of `p`
 * If `f` is the localization map from `A` to `K` and `p` has coefficients in `K`, then `f.integer_normalization p` is a polynomial with coefficients in `A` (think: `∀ i, is_integer (f.integer_normalization p).coeff i`) with the same roots as `p`.
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *lemma* polynomial.coeff_ne_zero_of_eq_degree
- \+ *lemma* polynomial.degree_ne_of_nat_degree_ne
- \+ *lemma* polynomial.degree_pos_of_aeval_root
- \+ *lemma* polynomial.degree_pos_of_eval₂_root
- \+ *lemma* polynomial.eq_C_of_nat_degree_le_zero
- \+ *lemma* polynomial.eval₂_smul
- \+ *lemma* polynomial.integral_normalization_aeval_eq_zero
- \+ *lemma* polynomial.integral_normalization_coeff_degree
- \+ *lemma* polynomial.integral_normalization_coeff_nat_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_degree
- \+ *lemma* polynomial.integral_normalization_coeff_ne_nat_degree
- \+ *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \+ *lemma* polynomial.monic_integral_normalization
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+ *lemma* polynomial.nat_degree_pos_iff_degree_pos
- \+ *lemma* polynomial.nat_degree_pos_of_aeval_root
- \+ *lemma* polynomial.nat_degree_pos_of_eval₂_root
- \+ *lemma* polynomial.support_integral_normalization

Modified src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_algebraic_of_finite
- \+ *lemma* exists_integral_multiple

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* fraction_map.comap_is_algebraic_iff
- \+ *lemma* fraction_map.integer_normalization_eq_zero_iff
- \+ *def* integral_closure.fraction_map_of_algebraic
- \+ *def* integral_closure.fraction_map_of_finite_extension
- \+ *lemma* localization_map.coeff_integer_normalization_mem_support
- \+ *lemma* localization_map.exist_integer_multiples_of_finset
- \+ *lemma* localization_map.integer_normalization_aeval_eq_zero
- \+ *lemma* localization_map.integer_normalization_coeff
- \+ *lemma* localization_map.integer_normalization_eval₂_eq_zero
- \+ *lemma* localization_map.integer_normalization_map_to_map
- \+ *lemma* localization_map.integer_normalization_spec
- \+ *lemma* localization_map.map_smul



## [2020-06-24 07:12:51](https://github.com/leanprover-community/mathlib/commit/8ecf53d)
feat(order/filter/countable_Inter): `sup` and `inf` ([#3154](https://github.com/leanprover-community/mathlib/pull/3154))
#### Estimated changes
Modified src/order/filter/countable_Inter.lean




## [2020-06-24 06:13:13](https://github.com/leanprover-community/mathlib/commit/617b07e)
feat(uniform_space/separation): add separated_set ([#3130](https://github.com/leanprover-community/mathlib/pull/3130))
Also add documentation and simplify the proof of separated => t2 and add the converse.
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* uniform_space.completion.is_add_group_hom_extension

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean
- \+/\- *def* uniform_space.completion.extension_hom

Modified src/topology/category/UniformSpace.lean
- \+/\- *def* CpltSepUniformSpace.of

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/separation.lean
- \+/\- *lemma* is_closed_diagonal
- \+ *lemma* t2_iff_is_closed_diagonal

Modified src/topology/uniform_space/abstract_completion.lean
- \+/\- *lemma* abstract_completion.extend_map

Modified src/topology/uniform_space/complete_separated.lean
- \+/\- *lemma* is_closed_of_is_complete

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* Cauchy.separated_pure_cauchy_injective
- \+/\- *lemma* uniform_space.completion.dense_embedding_coe
- \+/\- *lemma* uniform_space.completion.extension_map
- \+/\- *lemma* uniform_space.completion.uniform_embedding_coe

Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/separation.lean
- \+ *lemma* eq_of_uniformity_inf_nhds
- \+ *lemma* eq_of_uniformity_inf_nhds_of_is_separated
- \+ *lemma* id_rel_sub_separation_relation
- \+ *lemma* is_closed_separation_rel
- \+ *def* is_separated
- \+ *lemma* is_separated_def'
- \+ *lemma* is_separated_def
- \+ *lemma* is_separated_iff_induced
- \+ *lemma* is_separated_of_separated_space
- \- *def* separated
- \+/\- *lemma* separated_equiv
- \+ *lemma* separated_iff_t2
- \+ *def* separated_space
- \+ *lemma* separation_rel_comap
- \+ *lemma* separation_rel_eq_inter_closure
- \+/\- *lemma* uniform_space.eq_of_separated_of_uniform_continuous
- \+/\- *def* uniform_space.separation_quotient.lift
- \+/\- *lemma* uniform_space.separation_quotient.lift_mk
- \+/\- *lemma* uniform_space.separation_quotient.uniform_continuous_lift
- \+ *lemma* univ_separated_iff

Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-24 00:48:46](https://github.com/leanprover-community/mathlib/commit/985cce7)
chore(scripts): update nolints.txt ([#3156](https://github.com/leanprover-community/mathlib/pull/3156))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-24 00:18:26](https://github.com/leanprover-community/mathlib/commit/d57ac08)
feat(field_theory/separable): definition and basic properties ([#3155](https://github.com/leanprover-community/mathlib/pull/3155))
#### Estimated changes
Added src/field_theory/separable.lean
- \+ *lemma* polynomial.separable.mul
- \+ *lemma* polynomial.separable.of_mul_left
- \+ *lemma* polynomial.separable.of_mul_right
- \+ *def* polynomial.separable
- \+ *lemma* polynomial.separable_X
- \+ *lemma* polynomial.separable_X_add_C
- \+ *lemma* polynomial.separable_def'
- \+ *lemma* polynomial.separable_def
- \+ *lemma* polynomial.separable_one

Modified src/ring_theory/coprime.lean
- \+ *lemma* is_coprime.add_mul_left_left
- \+ *lemma* is_coprime.add_mul_left_left_iff
- \+ *lemma* is_coprime.add_mul_left_right
- \+ *lemma* is_coprime.add_mul_left_right_iff
- \+ *lemma* is_coprime.add_mul_right_left
- \+ *lemma* is_coprime.add_mul_right_left_iff
- \+ *lemma* is_coprime.add_mul_right_right
- \+ *lemma* is_coprime.add_mul_right_right_iff
- \+ *lemma* is_coprime.mul_add_left_left
- \+ *lemma* is_coprime.mul_add_left_left_iff
- \+ *lemma* is_coprime.mul_add_left_right
- \+ *lemma* is_coprime.mul_add_left_right_iff
- \+ *lemma* is_coprime.mul_add_right_left
- \+ *lemma* is_coprime.mul_add_right_left_iff
- \+ *lemma* is_coprime.mul_add_right_right
- \+ *lemma* is_coprime.mul_add_right_right_iff
- \+ *lemma* is_coprime.of_add_mul_left_left
- \+ *lemma* is_coprime.of_add_mul_left_right
- \+ *lemma* is_coprime.of_add_mul_right_left
- \+ *lemma* is_coprime.of_add_mul_right_right
- \+ *lemma* is_coprime.of_mul_add_left_left
- \+ *lemma* is_coprime.of_mul_add_left_right
- \+ *lemma* is_coprime.of_mul_add_right_left
- \+ *lemma* is_coprime.of_mul_add_right_right



## [2020-06-23 22:02:55](https://github.com/leanprover-community/mathlib/commit/340d5a9)
refactor(geometry/manifold/*): rename to charted_space and tangent_map ([#3103](https://github.com/leanprover-community/mathlib/pull/3103))
@PatrickMassot  had asked some time ago if what is currently called `manifold` in mathlib could be renamed to `charted_space`, and in a recent PR he asked if `bundled_mfderiv` could be called `tangent_map`. Both changes make sense. They are implemented in this PR, together with several tiny improvements to the manifold library.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/convex/basic.lean


Modified src/data/equiv/local_equiv.lean
- \+/\- *lemma* equiv.refl_to_local_equiv
- \+/\- *lemma* equiv.symm_to_local_equiv
- \+/\- *lemma* equiv.to_local_equiv_coe
- \+/\- *lemma* equiv.to_local_equiv_source
- \+/\- *lemma* equiv.to_local_equiv_symm_coe
- \+/\- *lemma* equiv.to_local_equiv_target
- \+/\- *lemma* equiv.trans_to_local_equiv
- \+/\- *theorem* local_equiv.coe_mk
- \+/\- *theorem* local_equiv.coe_symm_mk
- \+/\- *lemma* local_equiv.coe_trans
- \+/\- *lemma* local_equiv.coe_trans_symm
- \+ *lemma* local_equiv.image_inter_source_eq'
- \+ *lemma* local_equiv.image_inter_source_eq
- \+/\- *lemma* local_equiv.inv_fun_as_coe
- \- *lemma* local_equiv.inv_image_eq_source_inter_preimage
- \+/\- *lemma* local_equiv.left_inv
- \+/\- *lemma* local_equiv.map_source
- \+/\- *lemma* local_equiv.map_target
- \+/\- *lemma* local_equiv.of_set_coe
- \+/\- *lemma* local_equiv.of_set_source
- \+/\- *lemma* local_equiv.of_set_symm
- \+/\- *lemma* local_equiv.of_set_target
- \+/\- *lemma* local_equiv.prod_coe
- \+/\- *lemma* local_equiv.prod_coe_symm
- \+/\- *lemma* local_equiv.prod_source
- \+ *lemma* local_equiv.prod_symm
- \+/\- *lemma* local_equiv.prod_target
- \+ *lemma* local_equiv.prod_trans
- \+/\- *lemma* local_equiv.refl_coe
- \+/\- *lemma* local_equiv.refl_restr_source
- \+/\- *lemma* local_equiv.refl_restr_target
- \+/\- *lemma* local_equiv.refl_source
- \+/\- *lemma* local_equiv.refl_symm
- \+/\- *lemma* local_equiv.refl_target
- \+/\- *lemma* local_equiv.refl_trans
- \+/\- *lemma* local_equiv.restr_coe
- \+/\- *lemma* local_equiv.restr_coe_symm
- \+/\- *lemma* local_equiv.restr_source
- \+/\- *lemma* local_equiv.restr_target
- \+/\- *lemma* local_equiv.restr_univ
- \+/\- *lemma* local_equiv.right_inv
- \+ *lemma* local_equiv.symm_image_eq_source_inter_preimage
- \+ *lemma* local_equiv.symm_image_inter_target_eq'
- \+ *lemma* local_equiv.symm_image_inter_target_eq
- \+/\- *lemma* local_equiv.symm_source
- \+/\- *lemma* local_equiv.symm_symm
- \+/\- *lemma* local_equiv.symm_target
- \+/\- *lemma* local_equiv.to_fun_as_coe
- \+/\- *lemma* local_equiv.trans_refl
- \+/\- *lemma* local_equiv.trans_source
- \+/\- *lemma* local_equiv.trans_target

Modified src/data/monoid_algebra.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pnat/xgcd.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* basic_smooth_bundle_core.base_set
- \+/\- *lemma* basic_smooth_bundle_core.chart_source
- \+/\- *lemma* basic_smooth_bundle_core.chart_target
- \+/\- *lemma* basic_smooth_bundle_core.coe_chart_at_fst
- \+/\- *lemma* basic_smooth_bundle_core.coe_chart_at_symm_fst
- \+/\- *lemma* basic_smooth_bundle_core.mem_chart_source_iff
- \+/\- *lemma* basic_smooth_bundle_core.mem_chart_target_iff
- \+/\- *lemma* tangent_bundle_model_space_chart_at
- \+/\- *lemma* tangent_bundle_model_space_coe_chart_at
- \+/\- *lemma* tangent_bundle_model_space_coe_chart_at_symm

Renamed src/geometry/manifold/manifold.lean to src/geometry/manifold/charted_space.lean
- \+/\- *lemma* chart_at_model_space_eq
- \+ *def* charted_space_core.local_homeomorph
- \+ *lemma* charted_space_core.open_source'
- \+ *lemma* charted_space_core.open_target
- \+ *def* charted_space_core.to_charted_space
- \+ *structure* charted_space_core
- \- *def* manifold_core.local_homeomorph
- \- *lemma* manifold_core.open_source'
- \- *lemma* manifold_core.open_target
- \- *def* manifold_core.to_manifold
- \- *structure* manifold_core
- \+ *lemma* mem_maximal_atlas_iff
- \+/\- *lemma* model_space_atlas
- \+/\- *def* structomorph.refl
- \+ *lemma* structure_groupoid.chart_mem_maximal_atlas
- \+ *lemma* structure_groupoid.compatible
- \+ *lemma* structure_groupoid.compatible_of_mem_maximal_atlas
- \+ *lemma* structure_groupoid.eq_on_source
- \+ *lemma* structure_groupoid.id_mem
- \+ *lemma* structure_groupoid.le_iff
- \+ *lemma* structure_groupoid.locality
- \+ *def* structure_groupoid.maximal_atlas
- \+ *lemma* structure_groupoid.mem_maximal_atlas_of_mem_atlas
- \+ *lemma* structure_groupoid.symm
- \+ *lemma* structure_groupoid.trans

Modified src/geometry/manifold/mfderiv.lean
- \- *def* bundle_mfderiv
- \- *lemma* bundle_mfderiv_chart
- \- *lemma* bundle_mfderiv_chart_symm
- \- *lemma* bundle_mfderiv_comp
- \- *lemma* bundle_mfderiv_comp_at
- \- *lemma* bundle_mfderiv_proj
- \- *lemma* bundle_mfderiv_tangent_bundle_proj
- \- *def* bundle_mfderiv_within
- \- *lemma* bundle_mfderiv_within_comp_at
- \- *lemma* bundle_mfderiv_within_eq_bundle_mfderiv
- \- *lemma* bundle_mfderiv_within_proj
- \- *lemma* bundle_mfderiv_within_subset
- \- *lemma* bundle_mfderiv_within_tangent_bundle_proj
- \- *lemma* bundle_mfderiv_within_univ
- \+/\- *lemma* has_mfderiv_within_at_univ
- \+/\- *lemma* mfderiv_const
- \+/\- *lemma* mfderiv_id
- \+/\- *lemma* mfderiv_within_univ
- \+ *def* tangent_map
- \+ *lemma* tangent_map_chart
- \+ *lemma* tangent_map_chart_symm
- \+ *lemma* tangent_map_comp
- \+ *lemma* tangent_map_comp_at
- \+ *lemma* tangent_map_proj
- \+ *lemma* tangent_map_tangent_bundle_proj
- \+ *def* tangent_map_within
- \+ *lemma* tangent_map_within_comp_at
- \+ *lemma* tangent_map_within_eq_tangent_map
- \+ *lemma* tangent_map_within_proj
- \+ *lemma* tangent_map_within_subset
- \+ *lemma* tangent_map_within_tangent_bundle_proj
- \+ *lemma* tangent_map_within_univ
- \+ *lemma* unique_mdiff_on_univ
- \+/\- *def* written_in_ext_chart_at
- \+/\- *lemma* written_in_ext_chart_model_space

Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *def* ext_chart_at
- \+/\- *lemma* ext_chart_at_to_inv
- \+/\- *lemma* ext_chart_model_space_eq_id
- \+/\- *lemma* mem_ext_chart_source
- \+/\- *lemma* model_with_corners.left_inv'
- \+/\- *lemma* model_with_corners.left_inv
- \+/\- *lemma* model_with_corners.mk_coe
- \+/\- *lemma* model_with_corners.mk_coe_symm
- \+/\- *lemma* model_with_corners.right_inv
- \+/\- *lemma* model_with_corners.target
- \+/\- *lemma* model_with_corners.to_local_equiv_coe
- \+/\- *lemma* model_with_corners.to_local_equiv_coe_symm
- \+/\- *lemma* model_with_corners_self_coe
- \+/\- *lemma* model_with_corners_self_coe_symm
- \+/\- *lemma* model_with_corners_self_local_equiv
- \+ *lemma* smooth_manifold_with_corners.chart_mem_maximal_atlas
- \+ *lemma* smooth_manifold_with_corners.compatible
- \+ *lemma* smooth_manifold_with_corners.compatible_of_mem_maximal_atlas
- \+ *def* smooth_manifold_with_corners.maximal_atlas
- \+ *lemma* smooth_manifold_with_corners.mem_maximal_atlas_of_mem_atlas

Modified src/group_theory/monoid_localization.lean


Modified src/linear_algebra/basis.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/transport.lean


Modified src/topology/algebra/module.lean


Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* homeomorph.refl_to_local_homeomorph
- \+/\- *lemma* homeomorph.symm_to_local_homeomorph
- \+/\- *lemma* homeomorph.to_local_homeomorph_coe
- \+/\- *lemma* homeomorph.to_local_homeomorph_coe_symm
- \+/\- *lemma* homeomorph.to_local_homeomorph_source
- \+/\- *lemma* homeomorph.to_local_homeomorph_target
- \+/\- *lemma* homeomorph.trans_to_local_homeomorph
- \+/\- *lemma* local_homeomorph.coe_coe
- \+/\- *lemma* local_homeomorph.coe_coe_symm
- \+/\- *lemma* local_homeomorph.coe_trans
- \+/\- *lemma* local_homeomorph.coe_trans_symm
- \+ *lemma* local_homeomorph.image_eq_target_inter_inv_preimage
- \+ *lemma* local_homeomorph.image_inter_source_eq
- \+/\- *lemma* local_homeomorph.inv_fun_eq_coe
- \+/\- *lemma* local_homeomorph.left_inv
- \+/\- *lemma* local_homeomorph.map_source
- \+/\- *lemma* local_homeomorph.map_target
- \+/\- *lemma* local_homeomorph.mk_coe
- \+/\- *lemma* local_homeomorph.mk_coe_symm
- \+/\- *lemma* local_homeomorph.of_set_coe
- \+/\- *lemma* local_homeomorph.of_set_symm
- \+/\- *lemma* local_homeomorph.of_set_to_local_equiv
- \+/\- *lemma* local_homeomorph.prod_coe
- \+/\- *lemma* local_homeomorph.prod_coe_symm
- \+ *lemma* local_homeomorph.prod_symm
- \+/\- *lemma* local_homeomorph.prod_to_local_equiv
- \+ *lemma* local_homeomorph.prod_trans
- \+/\- *lemma* local_homeomorph.refl_coe
- \+/\- *lemma* local_homeomorph.refl_local_equiv
- \+/\- *lemma* local_homeomorph.refl_symm
- \+/\- *lemma* local_homeomorph.refl_trans
- \+/\- *lemma* local_homeomorph.restr_coe
- \+/\- *lemma* local_homeomorph.restr_coe_symm
- \+/\- *lemma* local_homeomorph.restr_open_to_local_equiv
- \+/\- *lemma* local_homeomorph.restr_to_local_equiv
- \+/\- *lemma* local_homeomorph.restr_univ
- \+/\- *lemma* local_homeomorph.right_inv
- \+ *lemma* local_homeomorph.symm_image_eq_source_inter_preimage
- \+ *lemma* local_homeomorph.symm_image_inter_target_eq
- \+/\- *lemma* local_homeomorph.symm_symm
- \+/\- *lemma* local_homeomorph.symm_to_local_equiv
- \+/\- *lemma* local_homeomorph.to_fun_eq_coe
- \+/\- *lemma* local_homeomorph.to_homeomorph_coe
- \+/\- *lemma* local_homeomorph.to_homeomorph_symm_coe
- \+/\- *lemma* local_homeomorph.trans_refl
- \+/\- *lemma* local_homeomorph.trans_to_local_equiv

Modified src/topology/topological_fiber_bundle.lean
- \+/\- *lemma* bundle_trivialization.coe_coe
- \+/\- *lemma* bundle_trivialization.coe_fst
- \+/\- *lemma* bundle_trivialization.coe_mk
- \+/\- *lemma* topological_fiber_bundle_core.local_triv'_fst
- \+/\- *lemma* topological_fiber_bundle_core.local_triv'_inv_fst
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_at_ext_to_local_homeomorph
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_at_fst
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_at_symm_fst
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_fst
- \+/\- *lemma* topological_fiber_bundle_core.local_triv_symm_fst
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv'_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv'_target
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_at_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_source
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_target
- \+/\- *lemma* topological_fiber_bundle_core.mem_triv_change_source
- \+/\- *def* topological_fiber_bundle_core.proj

Modified test/equiv_rw.lean




## [2020-06-23 17:57:24](https://github.com/leanprover-community/mathlib/commit/bc3ed51)
chore(data/set/finite): use dot notation ([#3151](https://github.com/leanprover-community/mathlib/pull/3151))
Rename:
* `finite_insert` to `finite.insert`;
* `finite_union` to `finite.union`;
* `finite_subset` to `finite.subset`;
* `finite_image` to `finite.image`;
* `finite_dependent_image` to `finite.dependent_image`;
* `finite_map` to `finite.map`;
* `finite_image_iff_on` to `finite_image_iff`;
* `finite_preimage` to `finite.preimage`;
* `finite_sUnion` to `finite.sUnion`;
* `finite_bUnion` to `finite.bUnion`, merge with `finite_bUnion'` and
  use `f : Π i ∈ s, set α` instead of `f : ι → set α`;
* `finite_prod` to `finite.prod`;
* `finite_seq` to `finite.seq`;
* `finite_subsets_of_finite` to `finite.finite_subsets`;
* `bdd_above_finite` to `finite.bdd_above`;
* `bdd_above_finite_union` to `finite.bdd_above_bUnion`;
* `bdd_below_finite` to `finite.bdd_below`;
* `bdd_below_finite_union` to `finite.bdd_below_bUnion`.
Delete
* `finite_of_finite_image_on`, was a copy of `finite_of_fintie_image`;
* `finite_bUnion'`: merge with `finite_bUnion` into `finite.bUnion`.
#### Estimated changes
Modified src/algebra/pointwise.lean


Modified src/analysis/analytic/composition.lean


Modified src/data/analysis/filter.lean


Modified src/data/analysis/topology.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/real/hyperreal.lean


Modified src/data/set/finite.lean
- \- *lemma* finset.bdd_above
- \- *lemma* finset.bdd_below
- \- *lemma* set.bdd_above_finite
- \- *lemma* set.bdd_above_finite_union
- \- *lemma* set.bdd_below_finite
- \- *lemma* set.bdd_below_finite_union
- \+ *theorem* set.finite.bUnion
- \+ *lemma* set.finite.bdd_above_bUnion
- \+ *lemma* set.finite.bdd_below_bUnion
- \+ *lemma* set.finite.dependent_image
- \+ *lemma* set.finite.finite_subsets
- \+ *theorem* set.finite.image
- \+ *theorem* set.finite.insert
- \+ *theorem* set.finite.map
- \+ *theorem* set.finite.preimage
- \+ *lemma* set.finite.prod
- \+ *theorem* set.finite.sUnion
- \+ *theorem* set.finite.seq
- \+ *theorem* set.finite.subset
- \+ *theorem* set.finite.union
- \- *theorem* set.finite_bUnion'
- \- *theorem* set.finite_bUnion
- \- *lemma* set.finite_dependent_image
- \- *theorem* set.finite_image
- \+ *theorem* set.finite_image_iff
- \- *theorem* set.finite_image_iff_on
- \- *theorem* set.finite_insert
- \- *theorem* set.finite_map
- \+/\- *theorem* set.finite_of_finite_image
- \- *theorem* set.finite_of_finite_image_on
- \- *theorem* set.finite_preimage
- \- *lemma* set.finite_prod
- \- *theorem* set.finite_sUnion
- \- *theorem* set.finite_seq
- \- *theorem* set.finite_subset
- \- *lemma* set.finite_subsets_of_finite
- \- *theorem* set.finite_union

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/integration.lean
- \- *theorem* measure_theory.simple_func.measurable

Modified src/measure_theory/simple_func_dense.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/cofinite.lean


Modified src/order/filter/ultrafilter.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/noetherian.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-23 17:15:59](https://github.com/leanprover-community/mathlib/commit/26918a0)
feat(topology/metric_space/baire): define filter `residual` ([#3149](https://github.com/leanprover-community/mathlib/pull/3149))
Fixes [#2265](https://github.com/leanprover-community/mathlib/pull/2265). Also define a typeclass `countable_Inter_filter` and prove that both `residual`
and `μ.ae` have this property.
#### Estimated changes
Modified src/analysis/normed_space/banach.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_ball_iff

Added src/order/filter/countable_Inter.lean
- \+ *lemma* countable_Inter_mem_sets
- \+ *lemma* countable_bInter_mem_sets
- \+ *lemma* countable_sInter_mem_sets
- \+ *lemma* eventually_countable_ball
- \+ *lemma* eventually_countable_forall

Modified src/topology/basic.lean
- \+ *lemma* dense_inter_of_open_left
- \+ *lemma* dense_inter_of_open_right

Modified src/topology/instances/ennreal.lean
- \+ *lemma* emetric.is_closed_ball

Modified src/topology/metric_space/baire.lean
- \+ *lemma* eventually_residual
- \+ *lemma* mem_residual
- \+ *def* residual

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.nhds_basis_closed_eball



## [2020-06-23 16:11:19](https://github.com/leanprover-community/mathlib/commit/62e1364)
chore(linear_algebra/nonsingular_inverse): `matrix.nonsing_inv` no longer requires base ring to carry `has_inv` instance ([#3136](https://github.com/leanprover-community/mathlib/pull/3136))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.unit_spec
- \+ *lemma* units.inv_eq_of_mul_eq_one
- \+ *lemma* units.inv_mul'
- \+ *lemma* units.inv_unique
- \+ *lemma* units.mul_inv'

Modified src/algebra/invertible.lean
- \+ *lemma* invertible_unique

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* matrix.is_unit_det_transpose
- \+ *lemma* matrix.is_unit_iff_is_unit_det
- \+ *lemma* matrix.is_unit_nonsing_inv_det
- \+ *lemma* matrix.mul_nonsing_inv
- \- *theorem* matrix.mul_nonsing_inv
- \- *def* matrix.nonsing_inv
- \+ *lemma* matrix.nonsing_inv_apply
- \+ *lemma* matrix.nonsing_inv_det
- \+ *lemma* matrix.nonsing_inv_mul
- \- *theorem* matrix.nonsing_inv_mul
- \+ *lemma* matrix.nonsing_inv_nonsing_inv
- \- *lemma* matrix.nonsing_inv_val
- \+/\- *lemma* matrix.transpose_nonsing_inv



## [2020-06-23 14:59:38](https://github.com/leanprover-community/mathlib/commit/ea665e7)
fix(algebra/ordered*): add norm_cast attribute ([#3132](https://github.com/leanprover-community/mathlib/pull/3132))
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* with_bot.coe_add
- \+ *lemma* with_bot.coe_bit0
- \+ *lemma* with_bot.coe_bit1
- \+ *lemma* with_bot.coe_eq_zero
- \+/\- *lemma* with_bot.coe_one
- \+/\- *lemma* with_bot.coe_zero
- \+/\- *lemma* with_top.coe_add
- \+ *lemma* with_top.coe_bit0
- \+ *lemma* with_top.coe_bit1
- \+ *lemma* with_top.coe_eq_one
- \+ *lemma* with_top.coe_eq_zero
- \+ *lemma* with_top.coe_one
- \+ *lemma* with_top.coe_zero
- \+/\- *lemma* with_top.zero_lt_coe

Modified src/algebra/ordered_ring.lean
- \- *theorem* with_top.coe_eq_zero
- \- *theorem* with_top.coe_zero

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_bot.coe_le_coe
- \+/\- *theorem* with_top.coe_le_coe

Modified src/ring_theory/unique_factorization_domain.lean




## [2020-06-23 13:58:52](https://github.com/leanprover-community/mathlib/commit/d287d34)
refactor(order/filter/basic): define `filter.eventually_eq` ([#3134](https://github.com/leanprover-community/mathlib/pull/3134))
* Define `eventually_eq` (`f =^f[l] g`) and `eventually_le` (`f ≤^f[l] g`).
* Use new notation and definitions in some files.
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/data/padics/hensel.lean


Modified src/measure_theory/indicator_function.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually.filter_mono
- \+ *lemma* filter.eventually_eq.comp₂
- \+ *lemma* filter.eventually_eq.div
- \+ *lemma* filter.eventually_eq.fun_comp
- \+ *lemma* filter.eventually_eq.inv
- \+ *lemma* filter.eventually_eq.mul
- \+ *lemma* filter.eventually_eq.refl
- \+ *lemma* filter.eventually_eq.rw
- \+ *lemma* filter.eventually_eq.sub
- \+ *lemma* filter.eventually_eq.symm
- \+ *lemma* filter.eventually_eq.trans
- \+ *def* filter.eventually_eq
- \- *lemma* filter.map_cong
- \+ *lemma* filter.map_congr

Modified src/topology/continuous_on.lean
- \+/\- *lemma* continuous_on.congr
- \+/\- *lemma* continuous_on_congr



## [2020-06-23 08:40:54](https://github.com/leanprover-community/mathlib/commit/421ed70)
chore(topology/metric_space/baire): review ([#3146](https://github.com/leanprover-community/mathlib/pull/3146))
* Simplify some proofs in `topology/metric_space/baire`;
* Allow dependency on `hi : i ∈ S` in some `bUnion`/`bInter` lemmas.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.eq_univ_of_subset

Modified src/data/set/countable.lean
- \+/\- *lemma* set.countable.bUnion

Modified src/data/set/lattice.lean
- \+/\- *theorem* set.bInter_eq_Inter
- \+/\- *theorem* set.bUnion_eq_Union
- \+/\- *lemma* set.sInter_bUnion
- \+/\- *lemma* set.sInter_eq_Inter
- \+/\- *theorem* set.sInter_range
- \+/\- *lemma* set.sUnion_bUnion
- \+/\- *lemma* set.sUnion_eq_Union
- \+/\- *theorem* set.sUnion_range

Modified src/measure_theory/measure_space.lean


Modified src/topology/basic.lean


Modified src/topology/metric_space/baire.lean
- \+/\- *theorem* dense_bInter_of_Gδ
- \+ *theorem* dense_inter_of_Gδ
- \+ *lemma* is_Gδ.inter
- \+ *lemma* is_Gδ_Inter
- \+/\- *lemma* is_Gδ_Inter_of_open
- \+ *lemma* is_Gδ_bInter
- \+/\- *lemma* is_Gδ_bInter_of_open
- \+ *lemma* is_Gδ_univ



## [2020-06-23 08:40:52](https://github.com/leanprover-community/mathlib/commit/159766e)
chore(topology/metric_space/basic): rename `uniform_continuous_dist'` ([#3145](https://github.com/leanprover-community/mathlib/pull/3145))
* rename `uniform_continuous_dist'` to `uniform_continuous_dist`;
* rename `uniform_continuous_dist` to `uniform_continuous.dist`;
* add `uniform_continuous.nndist`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* uniform_continuous.dist
- \+ *lemma* uniform_continuous.nndist
- \- *theorem* uniform_continuous_dist'
- \+/\- *theorem* uniform_continuous_dist

Modified src/topology/metric_space/completion.lean




## [2020-06-23 07:31:42](https://github.com/leanprover-community/mathlib/commit/02d880b)
perf(tactic/cache): call `freeze_local_instances` after `reset_instance_cache` ([#3128](https://github.com/leanprover-community/mathlib/pull/3128))
Calling `unfreeze_local_instances` unfreezes the local instances of the main goal, and thereby disables the type-class cache (for this goal).  It is therefore advisable to call `freeze_local_instances` afterwards as soon as possible.  (The type-class cache will still be trashed when you switch between goals with different local instances, but that's only half as bad as disabling the cache entirely.)
To this end this PR contains several changes:
 * The `reset_instance_cache` function (and `resetI` tactic) immediately call `freeze_local_instances`.
 * The `unfreezeI` tactic is removed.  Instead we introduce `unfreezingI { tac }`, which only temporarily unfreezes the local instances while executing `tac`.  Try to keep `tac` as small as possible.
 * We add `substI h` and `casesI t` tactics (which are short for `unfreezingI { subst h }` and `unfreezingI { casesI t }`, resp.) as abbreviations for the most common uses of `unfreezingI`.
 * Various other uses of `unfreeze_local_instances` are eliminated.  Avoid use of `unfreeze_local_instances` if possible.  Use the `unfreezing tac` combinator instead (the non-interactive version of `unfreezingI`).
See discussion at https://github.com/leanprover-community/mathlib/pull/3113#issuecomment-647150256
#### Estimated changes
Modified src/algebra/module.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/closed/cartesian.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/simple.lean


Modified src/control/bitraversable/instances.lean


Modified src/control/traversable/equiv.lean


Modified src/data/analysis/filter.lean


Modified src/data/fin.lean


Modified src/data/fintype/card.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/parallel.lean


Modified src/data/set/countable.lean


Modified src/data/set/finite.lean


Modified src/data/zmod/basic.lean


Modified src/field_theory/finite.lean


Modified src/group_theory/order_of_element.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/multilinear.lean


Modified src/logic/embedding.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/copy.lean


Modified src/order/lattice.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/game/short.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/tactic/cache.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/lint/simp.lean


Modified src/tactic/trunc_cases.lean


Modified src/topology/metric_space/basic.lean


Added test/instance_cache.lean




## [2020-06-23 04:53:57](https://github.com/leanprover-community/mathlib/commit/c0d74a3)
refactor(group/perm) bundle sign of a perm as a monoid_hom ([#3143](https://github.com/leanprover-community/mathlib/pull/3143))
We're trying to bundle everything right?
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* equiv.perm.eq_sign_of_surjective_hom
- \+/\- *def* equiv.perm.sign



## [2020-06-23 03:11:26](https://github.com/leanprover-community/mathlib/commit/23d6141)
chore(algebra/ring,char_zero): generalize some lemmas ([#3141](https://github.com/leanprover-community/mathlib/pull/3141))
`mul_eq_zero` etc only need `[mul_zero_class]` and `[no_zero_divisors]`. In particular, they don't need `has_neg`. Also deduplicate with `group_with_zero.*`.
#### Estimated changes
Modified src/algebra/char_zero.lean


Modified src/algebra/field.lean
- \- *lemma* division_ring.mul_ne_zero
- \- *lemma* division_ring.one_div_mul_one_div
- \+/\- *lemma* mul_inv'
- \- *lemma* mul_ne_zero_comm

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* div_eq_zero_iff
- \+/\- *lemma* div_ne_zero_iff
- \- *lemma* mul_eq_zero'
- \- *lemma* mul_eq_zero_iff'
- \- *lemma* mul_ne_zero''
- \- *lemma* mul_ne_zero_comm''
- \- *lemma* mul_ne_zero_iff

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ring.lean
- \+ *theorem* mul_eq_zero_comm
- \- *theorem* mul_ne_zero'
- \+ *theorem* mul_ne_zero
- \- *lemma* mul_ne_zero
- \- *theorem* mul_ne_zero_comm'
- \+ *theorem* mul_ne_zero_comm
- \+ *theorem* mul_ne_zero_iff
- \+/\- *lemma* mul_self_eq_zero
- \+/\- *lemma* zero_eq_mul_self

Modified src/data/rat/cast.lean


Modified src/data/real/nnreal.lean


Modified src/data/support.lean
- \- *lemma* function.support_mul'
- \+/\- *lemma* function.support_mul

Modified src/geometry/euclidean.lean


Modified src/number_theory/quadratic_reciprocity.lean




## [2020-06-23 00:34:00](https://github.com/leanprover-community/mathlib/commit/52abfcf)
chore(scripts): update nolints.txt ([#3144](https://github.com/leanprover-community/mathlib/pull/3144))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-22 20:52:37](https://github.com/leanprover-community/mathlib/commit/b562575)
feat(data/finset): add card_insert_of_mem ([#3137](https://github.com/leanprover-community/mathlib/pull/3137))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.card_insert_of_mem



## [2020-06-22 19:11:00](https://github.com/leanprover-community/mathlib/commit/36e3b9f)
chore(*): update to Lean 3.16.4c ([#3139](https://github.com/leanprover-community/mathlib/pull/3139))
#### Estimated changes
Modified leanpkg.toml




## [2020-06-22 19:10:58](https://github.com/leanprover-community/mathlib/commit/67844a8)
feat(order/complete_lattice): complete lattice of Sup ([#3138](https://github.com/leanprover-community/mathlib/pull/3138))
Construct a complete lattice from a least upper bound function. 
From a Xena group discussion.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+ *def* complete_lattice_of_Sup



## [2020-06-22 18:22:19](https://github.com/leanprover-community/mathlib/commit/f059336)
fix(algebra/pi_instances): improve definitions of `pi.*` ([#3116](https://github.com/leanprover-community/mathlib/pull/3116))
The new `test/pi_simp.lean` fails with current `master`. Note that
this is a workaround, not a proper fix for `tactic.pi_instance`.
See also [Zulip chat](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60id.60.20in.20pi_instances)
Also use `@[to_additive]` to generate additive definitions, add ordered multiplicative monoids, and add `semimodule (Π i, f i) (Π, g i)`.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/pi_instances.lean
- \- *lemma* pi.add_apply
- \+/\- *lemma* pi.inv_apply
- \+/\- *lemma* pi.mul_apply
- \- *lemma* pi.neg_apply
- \+/\- *lemma* pi.one_apply
- \+ *lemma* pi.smul_apply'
- \+/\- *lemma* pi.smul_apply
- \- *lemma* pi.zero_apply

Modified src/topology/metric_space/pi_Lp.lean


Added test/pi_simp.lean
- \+ *def* test.eval_default
- \+ *lemma* test.eval_default_one



## [2020-06-22 16:12:16](https://github.com/leanprover-community/mathlib/commit/54cc126)
feat(data/finset,data/fintype,algebra/big_operators): some more lemmas ([#3124](https://github.com/leanprover-community/mathlib/pull/3124))
Add some `finset`, `fintype` and `algebra.big_operators` lemmas that
were found useful in proving things related to affine independent
families.  (In all cases where results are proved for products, and
then derived for sums where possible using `to_additive`, it was the
result for sums that I actually had a use for.  In the case of
`eq_one_of_card_le_one_of_prod_eq_one` and
`eq_zero_of_card_le_one_of_sum_eq_zero`, `to_additive` couldn't be
used because it also tries to convert the `1` in `s.card ≤ 1` to `0`.)
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.eq_of_card_le_one_of_prod_eq
- \+ *lemma* finset.eq_of_card_le_one_of_sum_eq
- \+ *lemma* finset.eq_one_of_prod_eq_one
- \+ *lemma* finset.prod_erase

Modified src/data/finset.lean
- \+ *lemma* finset.eq_of_mem_of_not_mem_erase

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.card_le_one_of_subsingleton

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.eq_of_subsingleton_of_prod_eq



## [2020-06-22 13:19:55](https://github.com/leanprover-community/mathlib/commit/86dcd5c)
feat(analysis/calculus): C^1 implies strictly differentiable ([#3119](https://github.com/leanprover-community/mathlib/pull/3119))
Over the reals, a continuously differentiable function is strictly differentiable.
Supporting material:  Add a standard mean-value-theorem-related trick as its own lemma, and refactor another proof (in `calculus/extend_deriv`) to use that lemma.
Other material:  an _equality_ (rather than _inequality_) version of the mean value theorem for domains; slight refactor of `normed_space/dual`.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean
- \- *theorem* has_fderiv_at_boundary_of_tendsto_fderiv_aux

Modified src/analysis/calculus/mean_value.lean
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_le'
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le'
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
- \+ *theorem* domain_mvt
- \+ *lemma* strict_fderiv_of_cont_diff

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.has_strict_fderiv_at
- \+ *lemma* times_cont_diff.has_strict_fderiv_at
- \+ *lemma* times_cont_diff_on.has_strict_fderiv_at

Modified src/analysis/normed_space/dual.lean
- \+ *lemma* normed_space.norm_le_dual_bound

Modified src/topology/continuous_on.lean
- \+ *lemma* nhds_of_nhds_within_of_nhds



## [2020-06-22 11:57:27](https://github.com/leanprover-community/mathlib/commit/46a8894)
feat(linear_algebra/affine_space): affine combinations for finsets ([#3122](https://github.com/leanprover-community/mathlib/pull/3122))
Extend the definitions of affine combinations over a `fintype` to the
case of sums over a `finset` of an arbitrary index type (which is
appropriate for use cases such as affine independence of a possibly
infinite family of points).
Also change to have only bundled versions of `weighted_vsub_of_point`
and `weighted_vsub`, following review, so avoiding duplicating parts
of `linear_map` API.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \- *def* affine_space.affine_combination
- \- *lemma* affine_space.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \- *lemma* affine_space.affine_combination_vsub
- \- *def* affine_space.weighted_vsub
- \- *lemma* affine_space.weighted_vsub_add
- \- *lemma* affine_space.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \- *lemma* affine_space.weighted_vsub_neg
- \- *def* affine_space.weighted_vsub_of_point
- \- *lemma* affine_space.weighted_vsub_of_point_add
- \- *lemma* affine_space.weighted_vsub_of_point_eq_of_sum_eq_zero
- \- *def* affine_space.weighted_vsub_of_point_linear
- \- *lemma* affine_space.weighted_vsub_of_point_linear_apply
- \- *lemma* affine_space.weighted_vsub_of_point_neg
- \- *lemma* affine_space.weighted_vsub_of_point_smul
- \- *lemma* affine_space.weighted_vsub_of_point_sub
- \- *lemma* affine_space.weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \- *lemma* affine_space.weighted_vsub_of_point_zero
- \- *lemma* affine_space.weighted_vsub_smul
- \- *lemma* affine_space.weighted_vsub_sub
- \- *lemma* affine_space.weighted_vsub_vadd_affine_combination
- \- *lemma* affine_space.weighted_vsub_zero
- \+ *def* finset.affine_combination
- \+ *lemma* finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \+ *lemma* finset.affine_combination_vsub
- \+ *def* finset.weighted_vsub
- \+ *lemma* finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \+ *def* finset.weighted_vsub_of_point
- \+ *lemma* finset.weighted_vsub_of_point_apply
- \+ *lemma* finset.weighted_vsub_of_point_eq_of_sum_eq_zero
- \+ *lemma* finset.weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \+ *lemma* finset.weighted_vsub_vadd_affine_combination



## [2020-06-22 10:46:14](https://github.com/leanprover-community/mathlib/commit/105fa17)
feat(linear_algebra/matrix): trace of an endomorphism independent of basis ([#3125](https://github.com/leanprover-community/mathlib/pull/3125))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.of_injective_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.arrow_congr_trans
- \+ *lemma* linear_equiv.symm_trans_apply
- \+ *def* linear_map.fun_congr_left
- \+ *theorem* linear_map.fun_congr_left_apply
- \+ *theorem* linear_map.fun_congr_left_comp
- \+ *theorem* linear_map.fun_congr_left_id
- \+ *lemma* linear_map.fun_congr_left_symm
- \+ *def* linear_map.fun_left
- \+ *theorem* linear_map.fun_left_apply
- \+ *theorem* linear_map.fun_left_comp
- \+ *theorem* linear_map.fun_left_id

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.range

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_equiv_matrix'_apply
- \+ *theorem* linear_equiv_matrix_range
- \+ *theorem* linear_map.to_matrix_of_equiv
- \+ *def* linear_map.trace
- \+ *def* linear_map.trace_aux
- \+ *lemma* linear_map.trace_aux_def
- \+ *theorem* linear_map.trace_aux_eq'
- \+ *theorem* linear_map.trace_aux_eq
- \+ *theorem* linear_map.trace_aux_range
- \+ *theorem* linear_map.trace_eq_matrix_trace
- \+ *theorem* linear_map.trace_mul_comm
- \+ *lemma* matrix.linear_equiv_matrix_comp
- \+ *lemma* matrix.linear_equiv_matrix_mul
- \+ *theorem* matrix.to_lin_of_equiv



## [2020-06-22 08:01:57](https://github.com/leanprover-community/mathlib/commit/068aaaf)
chore(data/finmap): nolint ([#3131](https://github.com/leanprover-community/mathlib/pull/3131))
#### Estimated changes
Modified src/data/finmap.lean
- \+/\- *def* finmap.disjoint
- \+/\- *theorem* finmap.insert_insert
- \+/\- *theorem* finmap.insert_singleton_eq
- \+/\- *theorem* finmap.lookup_list_to_finmap
- \+/\- *theorem* finmap.lookup_union_left_of_not_in
- \+/\- *theorem* finmap.mem_list_to_finmap
- \+/\- *def* finmap.singleton
- \+/\- *theorem* finmap.to_finmap_cons
- \+/\- *theorem* finmap.to_finmap_nil
- \+/\- *theorem* finmap.union_cancel
- \+/\- *def* list.to_finmap



## [2020-06-22 07:22:10](https://github.com/leanprover-community/mathlib/commit/3f9b52a)
refactor(ring_theory/*): make PID class a predicate ([#3114](https://github.com/leanprover-community/mathlib/pull/3114))
#### Estimated changes
Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/splitting_field.lean


Modified src/number_theory/sum_two_squares.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+ *lemma* ideal.factors_decreasing

Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* is_prime.to_maximal_ideal
- \- *lemma* principal_ideal_domain.associates_irreducible_iff_prime
- \- *lemma* principal_ideal_domain.factors_decreasing
- \- *lemma* principal_ideal_domain.factors_spec
- \- *lemma* principal_ideal_domain.irreducible_iff_prime
- \- *lemma* principal_ideal_domain.is_maximal_of_irreducible
- \+ *lemma* principal_ideal_ring.associates_irreducible_iff_prime
- \+ *lemma* principal_ideal_ring.factors_spec
- \+ *lemma* principal_ideal_ring.irreducible_iff_prime
- \+ *lemma* principal_ideal_ring.is_maximal_of_irreducible



## [2020-06-22 00:33:41](https://github.com/leanprover-community/mathlib/commit/6aba958)
chore(scripts): update nolints.txt ([#3133](https://github.com/leanprover-community/mathlib/pull/3133))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-21 21:04:24](https://github.com/leanprover-community/mathlib/commit/d59adc1)
chore(data/list/alist): nolint ([#3129](https://github.com/leanprover-community/mathlib/pull/3129))
#### Estimated changes
Modified src/data/list/alist.lean
- \+/\- *def* alist.disjoint



## [2020-06-21 19:44:08](https://github.com/leanprover-community/mathlib/commit/5b5ff79)
fix(tactic/delta_instance): bug in computing pi arity ([#3127](https://github.com/leanprover-community/mathlib/pull/3127))
#### Estimated changes
Modified src/tactic/core.lean




## [2020-06-21 19:09:48](https://github.com/leanprover-community/mathlib/commit/eff9ed3)
feat(topology/uniform_space): some basic lemmas ([#3123](https://github.com/leanprover-community/mathlib/pull/3123))
This is the second PR on the road to Heine. It contains various elementary lemmas about uniform spaces.
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* closure_eq_uniformity
- \+ *lemma* comp_comp_symm_mem_uniformity_sets
- \+ *lemma* comp_rel_mono
- \+ *lemma* comp_symm_mem_uniformity_sets
- \+ *lemma* mem_comp_comp
- \+ *lemma* mem_comp_of_mem_ball
- \+ *lemma* subset_comp_self
- \+ *lemma* subset_comp_self_of_mem_uniformity
- \+ *lemma* symmetric_rel_inter
- \+ *lemma* uniform_space.ball_mem_nhds
- \+ *lemma* uniform_space.has_basis_nhds
- \+ *lemma* uniform_space.has_basis_nhds_prod
- \+ *lemma* uniform_space.mem_nhds_iff
- \+ *lemma* uniform_space.mem_nhds_iff_symm
- \+ *lemma* uniformity_comap
- \+ *lemma* uniformity_has_basis_closed
- \+ *lemma* uniformity_has_basis_closure



## [2020-06-21 17:25:22](https://github.com/leanprover-community/mathlib/commit/7073c8b)
feat(tactic/cancel_denoms): try to remove numeral denominators  ([#3109](https://github.com/leanprover-community/mathlib/pull/3109))
#### Estimated changes
Added src/tactic/cancel_denoms.lean
- \+ *lemma* cancel_factors.add_subst
- \+ *lemma* cancel_factors.cancel_factors_eq
- \+ *lemma* cancel_factors.cancel_factors_eq_div
- \+ *lemma* cancel_factors.cancel_factors_le
- \+ *lemma* cancel_factors.cancel_factors_lt
- \+ *lemma* cancel_factors.div_subst
- \+ *lemma* cancel_factors.mul_subst
- \+ *lemma* cancel_factors.neg_subst
- \+ *lemma* cancel_factors.sub_subst

Modified src/tactic/default.lean


Modified src/tactic/interactive.lean


Added test/cancel_denoms.lean




## [2020-06-21 16:23:00](https://github.com/leanprover-community/mathlib/commit/b7d056a)
feat(tactic/zify): move nat propositions to int ([#3108](https://github.com/leanprover-community/mathlib/pull/3108))
#### Estimated changes
Modified src/tactic/default.lean


Modified src/tactic/lift.lean


Modified src/tactic/norm_cast.lean


Added src/tactic/zify.lean
- \+ *lemma* int.coe_nat_ne_coe_nat_iff

Added test/zify.lean




## [2020-06-21 15:04:19](https://github.com/leanprover-community/mathlib/commit/d097161)
fix(tactic/set): use provided type for new variable ([#3126](https://github.com/leanprover-community/mathlib/pull/3126))
closes [#3111](https://github.com/leanprover-community/mathlib/pull/3111)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Added test/set.lean
- \+ *def* S
- \+ *def* T
- \+ *def* p
- \+ *def* u
- \+ *def* v



## [2020-06-20 19:21:52](https://github.com/leanprover-community/mathlib/commit/8729fe2)
feat(tactic/simps): option `trace.simps.verbose` prints generated lemmas ([#3121](https://github.com/leanprover-community/mathlib/pull/3121))
#### Estimated changes
Modified src/tactic/simps.lean




## [2020-06-20 15:10:42](https://github.com/leanprover-community/mathlib/commit/e8ff6ff)
feat(*): random lemmas about sets and filters ([#3118](https://github.com/leanprover-community/mathlib/pull/3118))
This is the first in a series of PR that will culminate in a proof of Heine's theorem (a continuous function from a compact separated uniform space to any uniform space is uniformly continuous). I'm slicing a 600 lines files into PRs. This first PR is only about sets, filters and a bit of topology. Uniform spaces stuff will come later.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *def* set.diagonal
- \+ *lemma* set.inter_compl_nonempty_iff
- \+ *lemma* set.preimage_coe_coe_diagonal

Modified src/order/filter/bases.lean
- \+ *lemma* filter.comap_has_basis
- \+ *lemma* filter.has_basis.prod'
- \+ *lemma* filter.has_basis.sInter_sets
- \+ *lemma* filter.has_basis_self

Modified src/order/filter/basic.lean
- \+ *lemma* filter.inf_principal_ne_bot_iff
- \+ *lemma* filter.subtype_coe_map_comap
- \+ *lemma* filter.tendsto.prod_map

Modified src/topology/algebra/ordered.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.prod_map
- \+ *lemma* continuous_within_at.prod_map



## [2020-06-20 11:22:01](https://github.com/leanprover-community/mathlib/commit/cd9e8b5)
fix(tactic/group): bugfix for inverse of 1 ([#3117](https://github.com/leanprover-community/mathlib/pull/3117))
The new group tactic made goals like
```lean
example {G : Type*} [group G] (x : G) (h : x = 1) : x = 1 :=
begin
  group, -- x * 1 ^(-1) = 1
  exact h,
end
```
worse, presumably from trying to move the rhs to the lhs we end up with `x * 1^(-1) = 1`, we add a couple more lemmas to try to fix this.
#### Estimated changes
Modified src/tactic/group.lean


Modified test/group.lean




## [2020-06-19 13:54:55](https://github.com/leanprover-community/mathlib/commit/103743e)
doc(tactic/core,uniform_space/basic): minor doc fixes ([#3115](https://github.com/leanprover-community/mathlib/pull/3115))
#### Estimated changes
Modified src/tactic/core.lean


Modified src/topology/uniform_space/basic.lean




## [2020-06-19 04:18:45](https://github.com/leanprover-community/mathlib/commit/8e44b9f)
feat(algebra/big_operators): `prod_apply_dite` and `prod_dite` ([#3110](https://github.com/leanprover-community/mathlib/pull/3110))
Generalize `prod_apply_ite` and `prod_ite` to dependent if-then-else. Since the proofs require `prod_attach`, it needed to move to an earlier line.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/prod_ite_eq
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.prod_apply_dite
- \+ *lemma* finset.prod_dite



## [2020-06-19 00:33:30](https://github.com/leanprover-community/mathlib/commit/56a580d)
chore(scripts): update nolints.txt ([#3112](https://github.com/leanprover-community/mathlib/pull/3112))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-18 22:26:13](https://github.com/leanprover-community/mathlib/commit/ed44541)
chore(*): regularize naming using injective ([#3071](https://github.com/leanprover-community/mathlib/pull/3071))
This begins some of the naming regularization discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/naming.20of.20injectivity.20lemmas
Some general rules:
1. Lemmas should have `injective` in the name iff they have `injective` in the conclusion
2. `X_injective` is preferable to `injective_X`.
3. Unidirectional `inj` lemmas should be dropped in favour of bidirectional ones.
Mostly, this PR tried to fix the names of lemmas that conclude `injective` (also `surjective` and `bijective`, but they seemed to be much better already).
A lot of the changes are from `injective_X` to `X_injective` style
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/direct_limit.lean
- \- *theorem* ring.direct_limit.of_inj
- \+ *theorem* ring.direct_limit.of_injective

Modified src/algebra/direct_sum.lean
- \- *theorem* direct_sum.mk_inj
- \+ *theorem* direct_sum.mk_injective
- \- *theorem* direct_sum.of_inj
- \+ *theorem* direct_sum.of_injective

Modified src/algebra/field_power.lean
- \+ *lemma* fpow_injective
- \- *lemma* injective_fpow

Modified src/algebra/group/type_tags.lean
- \- *lemma* of_add_inj
- \+ *lemma* of_add_injective
- \- *lemma* of_mul_inj
- \+ *lemma* of_mul_injective
- \- *lemma* to_add_inj
- \+ *lemma* to_add_injective
- \- *lemma* to_mul_inj
- \+ *lemma* to_mul_injective

Modified src/algebra/module.lean
- \+ *theorem* submodule.coe_injective
- \+/\- *theorem* submodule.coe_set_eq
- \- *theorem* submodule.ext'
- \+/\- *theorem* submodule.ext

Modified src/algebra/opposites.lean


Modified src/algebra/pi_instances.lean
- \- *lemma* prod.injective_inl
- \- *lemma* prod.injective_inr
- \+ *lemma* prod.inl_injective
- \+ *lemma* prod.inr_injective

Modified src/algebra/ring.lean
- \- *theorem* ring_hom.coe_add_monoid_hom_inj
- \+ *theorem* ring_hom.coe_add_monoid_hom_injective
- \- *theorem* ring_hom.coe_monoid_hom_inj
- \+ *theorem* ring_hom.coe_monoid_hom_injective

Modified src/analysis/analytic/basic.lean
- \- *lemma* formal_multilinear_series.change_origin_summable_aux_j_inj
- \+ *lemma* formal_multilinear_series.change_origin_summable_aux_j_injective

Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/point_reflection.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/fully_faithful.lean
- \- *lemma* category_theory.functor.injectivity
- \+ *lemma* category_theory.functor.map_injective

Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean


Modified src/combinatorics/composition.lean
- \- *lemma* composition.embedding_inj
- \+ *lemma* composition.embedding_injective

Modified src/computability/partrec_code.lean
- \+ *theorem* nat.partrec.code.const_inj
- \+ *theorem* nat.partrec.code.curry_inj
- \- *theorem* nat.partrec.code.injective_const
- \- *theorem* nat.partrec.code.injective_curry
- \+/\- *theorem* nat.partrec.code.smn

Modified src/control/fold.lean


Modified src/data/dfinsupp.lean
- \- *theorem* dfinsupp.mk_inj
- \+ *theorem* dfinsupp.mk_injective

Modified src/data/equiv/list.lean


Modified src/data/equiv/mul_add.lean
- \- *lemma* equiv.point_reflection_fixed_iff_of_bit0_inj
- \+ *lemma* equiv.point_reflection_fixed_iff_of_bit0_injective

Modified src/data/fin.lean
- \+ *lemma* fin.cast_le_injective
- \+ *lemma* fin.cast_succ_injective
- \- *lemma* fin.injective_cast_le
- \- *lemma* fin.injective_cast_succ
- \- *lemma* fin.injective_succ
- \- *lemma* fin.injective_val
- \+ *lemma* fin.succ_injective
- \+ *lemma* fin.val_injective

Modified src/data/finset.lean
- \- *lemma* finset.injective_pi_cons
- \+ *lemma* finset.pi_cons_injective

Modified src/data/finsupp.lean
- \- *lemma* finsupp.injective_map_domain
- \- *lemma* finsupp.injective_single
- \+ *lemma* finsupp.map_domain_injective
- \+ *lemma* finsupp.single_injective

Modified src/data/int/basic.lean


Modified src/data/list/basic.lean
- \- *theorem* list.cons_inj'
- \+/\- *theorem* list.cons_inj
- \+ *theorem* list.cons_injective
- \- *lemma* list.injective_length
- \- *lemma* list.injective_length_iff
- \- *theorem* list.injective_map_iff
- \+ *lemma* list.length_injective
- \+ *lemma* list.length_injective_iff
- \+ *theorem* list.map_injective_iff
- \- *theorem* list.mem_map_of_inj
- \+ *theorem* list.mem_map_of_injective

Modified src/data/multiset.lean
- \- *theorem* multiset.injective_map
- \- *lemma* multiset.injective_pi_cons
- \+ *theorem* multiset.map_injective
- \- *theorem* multiset.mem_map_of_inj
- \+ *theorem* multiset.mem_map_of_injective
- \+ *lemma* multiset.pi_cons_injective

Modified src/data/mv_polynomial.lean
- \- *lemma* mv_polynomial.injective_rename
- \+ *lemma* mv_polynomial.rename_injective

Modified src/data/nat/cast.lean


Modified src/data/opposite.lean
- \- *lemma* opposite.op_inj
- \+ *lemma* opposite.op_injective
- \- *lemma* opposite.unop_inj
- \+ *lemma* opposite.unop_injective

Modified src/data/option/basic.lean
- \- *theorem* option.injective_map
- \- *theorem* option.injective_some
- \+ *theorem* option.map_injective
- \+ *theorem* option.some_injective

Modified src/data/pnat/factors.lean
- \- *theorem* prime_multiset.coe_nat_inj
- \+ *theorem* prime_multiset.coe_nat_injective
- \- *theorem* prime_multiset.coe_pnat_inj
- \+ *theorem* prime_multiset.coe_pnat_injective

Modified src/data/real/cardinality.lean
- \+ *lemma* cardinal.cantor_function_injective
- \- *lemma* cardinal.injective_cantor_function

Modified src/data/real/hyperreal.lean


Modified src/data/set/basic.lean
- \- *lemma* function.surjective.injective_preimage
- \+ *lemma* function.surjective.preimage_injective
- \+ *lemma* set.image_injective
- \- *lemma* set.injective_image

Modified src/data/set/lattice.lean
- \- *lemma* set.bijective_sigma_to_Union
- \- *lemma* set.injective_sigma_to_Union
- \+ *lemma* set.sigma_to_Union_bijective
- \+ *lemma* set.sigma_to_Union_injective
- \+ *lemma* set.sigma_to_Union_surjective
- \- *lemma* set.surjective_sigma_to_Union

Modified src/data/setoid/basic.lean
- \- *lemma* setoid.injective_ker_lift
- \+ *lemma* setoid.ker_lift_injective

Modified src/data/sigma/basic.lean
- \- *lemma* injective_sigma_map
- \- *lemma* injective_sigma_mk
- \+ *lemma* sigma_map_injective
- \+ *lemma* sigma_mk_injective

Modified src/deprecated/subgroup.lean
- \- *lemma* is_group_hom.inj_iff_trivial_ker
- \- *lemma* is_group_hom.inj_of_trivial_ker
- \+ *lemma* is_group_hom.injective_iff_trivial_ker
- \+ *lemma* is_group_hom.injective_of_trivial_ker
- \- *lemma* is_group_hom.trivial_ker_of_inj
- \+ *lemma* is_group_hom.trivial_ker_of_injective

Modified src/group_theory/congruence.lean
- \- *lemma* con.injective_ker_lift
- \+ *lemma* con.ker_lift_injective

Modified src/group_theory/order_of_element.lean
- \- *lemma* conj_inj
- \+ *lemma* conj_injective

Modified src/group_theory/quotient_group.lean
- \- *lemma* quotient_group.injective_ker_lift
- \+ *lemma* quotient_group.ker_lift_injective

Modified src/group_theory/sylow.lean
- \- *lemma* sylow.mk_vector_prod_eq_one_inj
- \+ *lemma* sylow.mk_vector_prod_eq_one_injective

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean
- \- *lemma* dim_eq_injective
- \+ *lemma* dim_eq_of_injective
- \+ *lemma* dim_eq_of_surjective
- \- *lemma* dim_eq_surjective
- \- *lemma* dim_le_injective
- \+ *lemma* dim_le_of_injective
- \+ *lemma* dim_le_of_surjective
- \- *lemma* dim_le_surjective

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/logic/embedding.lean
- \- *theorem* function.embedding.inj
- \+ *theorem* function.embedding.injective

Modified src/order/boolean_algebra.lean
- \- *theorem* compl_inj
- \+ *theorem* compl_injective

Modified src/order/complete_boolean_algebra.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.pure_inj
- \+ *lemma* filter.pure_injective

Modified src/order/filter/filter_product.lean
- \+ *lemma* filter.filter_product.coe_inj
- \- *lemma* filter.filter_product.coe_injective
- \- *theorem* filter.filter_product.of_inj
- \+ *theorem* filter.filter_product.of_injective

Modified src/order/order_iso.lean
- \+ *theorem* order_embedding.coe_fn_inj
- \- *theorem* order_embedding.coe_fn_injective
- \- *theorem* order_embedding.inj
- \+ *theorem* order_embedding.injective

Modified src/ring_theory/algebra.lean
- \- *theorem* alg_hom.coe_add_monoid_hom_inj
- \+ *theorem* alg_hom.coe_add_monoid_hom_injective
- \- *theorem* alg_hom.coe_monoid_hom_inj
- \+ *theorem* alg_hom.coe_monoid_hom_injective
- \- *theorem* alg_hom.coe_ring_hom_inj
- \+ *theorem* alg_hom.coe_ring_hom_injective

Modified src/ring_theory/ideal_operations.lean
- \- *theorem* ideal.bijective_quotient_inf_to_pi_quotient
- \+ *theorem* ideal.quotient_inf_to_pi_quotient_bijective
- \- *lemma* ring_hom.inj_iff_ker_eq_bot
- \+ *lemma* ring_hom.injective_iff_ker_eq_bot

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cardinal.lean
- \- *lemma* cardinal.mk_range_eq_of_inj
- \+ *lemma* cardinal.mk_range_eq_of_injective

Modified src/set_theory/ordinal.lean
- \- *lemma* ordinal.injective_typein
- \+ *lemma* ordinal.typein_injective

Modified src/set_theory/schroeder_bernstein.lean
- \- *theorem* function.embedding.injective_min
- \+ *theorem* function.embedding.min_injective

Modified src/topology/algebra/open_subgroup.lean
- \+ *lemma* open_subgroup.coe_injective
- \- *lemma* open_subgroup.ext'
- \+/\- *lemma* open_subgroup.ext

Modified src/topology/constructions.lean


Modified src/topology/uniform_space/completion.lean
- \- *lemma* Cauchy.injective_separated_pure_cauchy
- \+ *lemma* Cauchy.separated_pure_cauchy_injective



## [2020-06-18 21:08:16](https://github.com/leanprover-community/mathlib/commit/e060c93)
feat(category_theory/discrete): build equivalence from equiv ([#3099](https://github.com/leanprover-community/mathlib/pull/3099))
* renames all the construction building functors/transformations out of discrete categories as `discrete.functor`, `discrete.nat_trans`, `discrete.nat_iso`, rather than names using `of_function`.
* adds `def discrete.equivalence {I J : Type u₁} (e : I ≃ J) : discrete I ≌ discrete J`,
* removes some redundant definitions
* breaks some long lines, 
* and adds doc-strings.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean


Modified src/category_theory/discrete_category.lean
- \+ *def* category_theory.discrete.equivalence
- \+ *def* category_theory.discrete.functor
- \+ *lemma* category_theory.discrete.functor_map
- \+ *lemma* category_theory.discrete.functor_obj
- \- *def* category_theory.discrete.lift
- \+ *def* category_theory.discrete.nat_iso
- \+ *def* category_theory.discrete.nat_trans
- \+ *lemma* category_theory.discrete.nat_trans_app
- \- *def* category_theory.functor.of_function
- \- *lemma* category_theory.functor.of_function_map
- \- *lemma* category_theory.functor.of_function_obj
- \- *def* category_theory.nat_iso.of_isos
- \- *def* category_theory.nat_trans.of_function
- \- *lemma* category_theory.nat_trans.of_function_app
- \- *def* category_theory.nat_trans.of_homs
- \- *lemma* category_theory.nat_trans.of_homs_app

Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *abbreviation* category_theory.limits.biproduct.ι
- \+/\- *abbreviation* category_theory.limits.biproduct.π
- \+/\- *abbreviation* category_theory.limits.biproduct
- \+/\- *def* category_theory.limits.biproduct_iso

Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/products.lean
- \+/\- *abbreviation* category_theory.limits.cofan
- \+/\- *abbreviation* category_theory.limits.fan
- \+/\- *abbreviation* category_theory.limits.pi.lift
- \+/\- *abbreviation* category_theory.limits.pi.π
- \+/\- *abbreviation* category_theory.limits.pi_obj
- \+/\- *abbreviation* category_theory.limits.sigma.desc
- \+/\- *abbreviation* category_theory.limits.sigma.ι
- \+/\- *abbreviation* category_theory.limits.sigma_obj

Modified src/category_theory/limits/shapes/zero.lean




## [2020-06-18 21:08:14](https://github.com/leanprover-community/mathlib/commit/73caeaa)
perf(tactic/linarith): implement redundancy test to reduce number of comparisons ([#3079](https://github.com/leanprover-community/mathlib/pull/3079))
This implements a redundancy check in `linarith` which can drastically reduce the size of the sets of comparisons that the tactic needs to deal with.
`linarith` iteratively transforms sets of inequalities to equisatisfiable sets by eliminating a single variable. If there are `n` comparisons in the set, we expect `O(n^2)` comparisons after one elimination step. Many of these comparisons are redundant, i.e. removing them from the set does not change its satisfiability.
Deciding redundancy is expensive, but there are cheap approximations that are very useful in practice. This PR tests comparisons for non-minimal history (http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13, theorem 7). Non-minimal history implies redundancy.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* real.sin_le_sin_of_le_of_le_pi_div_two
- \+/\- *lemma* real.sin_lt_sin_of_le_of_le_pi_div_two

Modified src/meta/rb_map.lean


Modified src/tactic/linarith.lean
- \+ *def* linarith.comp.vars
- \+ *structure* linarith.comp
- \+ *def* linarith.comp_source.to_string
- \+ *inductive* linarith.comp_source
- \+ *def* linarith.linexp.vars



## [2020-06-18 20:37:24](https://github.com/leanprover-community/mathlib/commit/21bf873)
refactor(category_theory/abelian): use has_finite_products ([#2917](https://github.com/leanprover-community/mathlib/pull/2917))
This doesn't go nearly as far as I wanted.
Really I'd like to factor out `additive`, which is a `preadditive` category with all finite biproducts, and then layer `abelian` on top of that (with (co)kernels and every epi/mono normal).
I can't do that immediately, because:
1. we don't provide the instances from `has_finite_biproducts` to `has_finite_(co)products`
2. we don't define the preadditive version of finite biproducts (we only did the binary ones)
3. hence we don't show that in a preadditive category finite products give rise to finite biproducts
@TwoFX, @b-mehta, if either of you are interested in doing any of these, that would be great. I'll hopefully get to them eventually.
#### Estimated changes
Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/zero.lean
- \+ *def* category_theory.limits.has_zero_object.has_initial
- \- *def* category_theory.limits.has_zero_object.has_initial_of_has_zero_object
- \+ *def* category_theory.limits.has_zero_object.has_terminal
- \- *def* category_theory.limits.has_zero_object.has_terminal_of_has_zero_object



## [2020-06-18 13:45:55](https://github.com/leanprover-community/mathlib/commit/53af714)
chore(*): update to lean 3.16.3 ([#3107](https://github.com/leanprover-community/mathlib/pull/3107))
The changes to mathlib are from https://github.com/leanprover-community/lean/pull/321 which removed some redundant lemmas:
* `int.of_nat_inj` -> `int.of_nat.inj`
* `int.neg_succ_of_nat_inj` -> `int.neg_succ_of_nat.inj`
* `nat.succ_inj` -> `nat.succ.inj`
#### Estimated changes
Modified leanpkg.toml


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset.lean


Modified src/data/fintype/basic.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/zip.lean


Modified src/data/nat/basic.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/xgcd.lean


Modified src/tactic/alias.lean


Modified src/topology/algebra/infinite_sum.lean


Modified test/lint.lean




## [2020-06-18 11:39:55](https://github.com/leanprover-community/mathlib/commit/24792be)
chore(data/finset): minor review ([#3105](https://github.com/leanprover-community/mathlib/pull/3105))
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.nonempty_iff_nonempty

Modified src/data/finset.lean
- \+/\- *lemma* finset.coe_erase
- \+/\- *lemma* finset.coe_filter
- \+/\- *lemma* finset.coe_image
- \+/\- *lemma* finset.coe_insert
- \+/\- *theorem* finset.coe_map
- \+/\- *lemma* finset.coe_nonempty
- \+/\- *lemma* finset.coe_sdiff
- \+/\- *lemma* finset.coe_ssubset
- \+/\- *theorem* finset.coe_subset
- \+/\- *lemma* finset.comp_inf_eq_inf_comp
- \- *lemma* finset.lt_inf
- \+ *lemma* finset.lt_inf_iff
- \+/\- *lemma* finset.ssubset_iff

Modified src/data/multiset.lean
- \+ *theorem* multiset.ndinter_subset_left
- \+ *theorem* multiset.subset_ndunion_right

Modified src/data/set/basic.lean
- \+ *theorem* set.ssubset_iff_insert

Modified src/data/set/lattice.lean
- \+ *lemma* set.bot_eq_empty
- \+ *lemma* set.inf_eq_inter
- \+ *lemma* set.le_eq_subset
- \+ *lemma* set.lt_eq_ssubset
- \+ *lemma* set.sup_eq_union

Modified src/logic/function/basic.lean
- \+/\- *def* function.injective.decidable_eq

Modified src/order/basic.lean
- \- *theorem* monotone.order_dual

Modified src/order/lattice.lean
- \+ *lemma* monotone.map_inf
- \+ *lemma* monotone.map_sup



## [2020-06-18 09:54:38](https://github.com/leanprover-community/mathlib/commit/eb5b7fb)
fix(tactic/linarith): don't fail trying to preprocess irrelevant hypotheses ([#3104](https://github.com/leanprover-community/mathlib/pull/3104))
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2020-06-18 01:11:41](https://github.com/leanprover-community/mathlib/commit/b91909e)
chore(category_theory/closed/cartesian): style ([#3098](https://github.com/leanprover-community/mathlib/pull/3098))
Just breaking long lines, and using braces in a multi-goal proof, for a recently added file.
 ([#2894](https://github.com/leanprover-community/mathlib/pull/2894))
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+/\- *lemma* category_theory.ev_coev



## [2020-06-17 19:57:11](https://github.com/leanprover-community/mathlib/commit/b5baf55)
feat(algebra/linear_ordered_comm_group_with_zero) define linear_ordered_comm_group_with_zero ([#3072](https://github.com/leanprover-community/mathlib/pull/3072))
#### Estimated changes
Added src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* div_le_div'
- \+ *lemma* inv_le_inv''
- \+ *lemma* inv_lt_inv''
- \+ *lemma* le_mul_inv_of_mul_le
- \+ *lemma* le_of_le_mul_right
- \+ *lemma* le_zero_iff
- \+ *lemma* mul_inv_le_of_le_mul
- \+ *lemma* mul_inv_lt_of_lt_mul'
- \+ *lemma* mul_lt_mul''''
- \+ *lemma* mul_lt_right'
- \+ *lemma* ne_zero_of_lt
- \+ *lemma* not_lt_zero'
- \+ *lemma* zero_le'
- \+ *lemma* zero_le_one'
- \+ *lemma* zero_lt_iff
- \+ *lemma* zero_lt_one'
- \+ *lemma* zero_lt_unit

Modified src/algebra/ordered_group.lean
- \+ *lemma* div_le_div_iff'

Modified src/data/real/nnreal.lean




## [2020-06-17 19:10:21](https://github.com/leanprover-community/mathlib/commit/48c4f40)
refactor(measure_theory): make `volume` a bundled measure ([#3075](https://github.com/leanprover-community/mathlib/pull/3075))
This way we can `apply` and `rw` lemmas about `measure`s without
introducing a `volume`-specific version.
#### Estimated changes
Modified src/data/set/disjointed.lean
- \+ *theorem* pairwise.pairwise_on
- \+ *theorem* set.pairwise_on.on_injective

Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.measure.integral_zero

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.ae_all_iff
- \+ *lemma* measure_theory.ae_eq_refl
- \+ *lemma* measure_theory.ae_eq_symm
- \+ *lemma* measure_theory.ae_eq_trans
- \+ *lemma* measure_theory.ae_iff
- \+ *lemma* measure_theory.ae_of_all
- \- *def* measure_theory.all_ae
- \- *lemma* measure_theory.all_ae_all_iff
- \- *lemma* measure_theory.all_ae_and_iff
- \- *lemma* measure_theory.all_ae_congr
- \- *lemma* measure_theory.all_ae_eq_refl
- \- *lemma* measure_theory.all_ae_eq_symm
- \- *lemma* measure_theory.all_ae_eq_trans
- \- *lemma* measure_theory.all_ae_iff
- \- *lemma* measure_theory.all_ae_imp_distrib_left
- \- *lemma* measure_theory.all_ae_of_all
- \- *lemma* measure_theory.all_ae_or_distrib_left
- \- *lemma* measure_theory.all_ae_or_distrib_right
- \+ *lemma* measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure
- \+ *lemma* measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure
- \- *lemma* measure_theory.exists_nonempty_inter_of_volume_univ_lt_sum_volume
- \- *lemma* measure_theory.exists_nonempty_inter_of_volume_univ_lt_tsum_volume
- \- *def* measure_theory.measure.a_e
- \+ *def* measure_theory.measure.ae
- \- *lemma* measure_theory.measure.mem_a_e_iff
- \+ *lemma* measure_theory.measure_bUnion_finset
- \+ *lemma* measure_theory.measure_zero_iff_ae_nmem
- \+ *lemma* measure_theory.mem_ae_iff
- \+ *lemma* measure_theory.sum_measure_le_measure_univ
- \- *lemma* measure_theory.sum_volume_le_volume_univ
- \+ *lemma* measure_theory.tsum_measure_le_measure_univ
- \- *lemma* measure_theory.tsum_volume_le_volume_univ
- \- *def* measure_theory.volume
- \- *lemma* measure_theory.volume_Union
- \- *theorem* measure_theory.volume_Union_le
- \- *lemma* measure_theory.volume_Union_null
- \- *lemma* measure_theory.volume_bUnion
- \- *lemma* measure_theory.volume_bUnion_finset
- \- *lemma* measure_theory.volume_diff
- \- *lemma* measure_theory.volume_empty
- \- *lemma* measure_theory.volume_mono
- \- *lemma* measure_theory.volume_mono_null
- \- *lemma* measure_theory.volume_sUnion
- \- *lemma* measure_theory.volume_union
- \- *theorem* measure_theory.volume_union_le
- \- *lemma* measure_theory.volume_union_null
- \- *lemma* measure_theory.volume_zero_iff_all_ae_nmem

Modified src/measure_theory/set_integral.lean


Modified src/measure_theory/simple_func_dense.lean




## [2020-06-17 12:07:34](https://github.com/leanprover-community/mathlib/commit/0736c95)
chore(order/filter/basic): move some parts to new files ([#3087](https://github.com/leanprover-community/mathlib/pull/3087))
Move `at_top`/`at_bot`, `cofinite`, and `ultrafilter` to new files.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/data/analysis/filter.lean


Added src/order/filter/at_top_bot.lean
- \+ *lemma* filter.Iio_mem_at_bot
- \+ *lemma* filter.Ioi_mem_at_top
- \+ *def* filter.at_bot
- \+ *def* filter.at_top
- \+ *lemma* filter.at_top_ne_bot
- \+ *lemma* filter.eventually.exists_forall_of_at_top
- \+ *lemma* filter.eventually_at_top
- \+ *lemma* filter.exists_le_of_tendsto_at_top
- \+ *lemma* filter.exists_lt_of_tendsto_at_top
- \+ *lemma* filter.extraction_of_eventually_at_top
- \+ *lemma* filter.extraction_of_frequently_at_top'
- \+ *lemma* filter.extraction_of_frequently_at_top
- \+ *lemma* filter.frequently.forall_exists_of_at_top
- \+ *lemma* filter.frequently_at_top'
- \+ *lemma* filter.frequently_at_top
- \+ *lemma* filter.frequently_high_scores
- \+ *lemma* filter.high_scores
- \+ *lemma* filter.map_add_at_top_eq_nat
- \+ *lemma* filter.map_at_top_eq
- \+ *lemma* filter.map_at_top_eq_of_gc
- \+ *lemma* filter.map_at_top_inf_ne_bot_iff
- \+ *lemma* filter.map_div_at_top_eq_nat
- \+ *lemma* filter.map_sub_at_top_eq_nat
- \+ *lemma* filter.mem_at_bot
- \+ *lemma* filter.mem_at_top
- \+ *lemma* filter.mem_at_top_sets
- \+ *lemma* filter.monotone.tendsto_at_top_finset
- \+ *lemma* filter.prod_at_top_at_top_eq
- \+ *lemma* filter.prod_map_at_top_eq
- \+ *lemma* filter.strict_mono_subseq_of_id_le
- \+ *lemma* filter.strict_mono_subseq_of_tendsto_at_top
- \+ *lemma* filter.strict_mono_tendsto_at_top
- \+ *lemma* filter.tendsto_add_at_top_iff_nat
- \+ *lemma* filter.tendsto_add_at_top_nat
- \+ *lemma* filter.tendsto_at_top'
- \+ *lemma* filter.tendsto_at_top
- \+ *lemma* filter.tendsto_at_top_add_const_left
- \+ *lemma* filter.tendsto_at_top_add_const_right
- \+ *lemma* filter.tendsto_at_top_add_left_of_le'
- \+ *lemma* filter.tendsto_at_top_add_left_of_le
- \+ *lemma* filter.tendsto_at_top_add_nonneg_left'
- \+ *lemma* filter.tendsto_at_top_add_nonneg_left
- \+ *lemma* filter.tendsto_at_top_add_nonneg_right'
- \+ *lemma* filter.tendsto_at_top_add_nonneg_right
- \+ *lemma* filter.tendsto_at_top_add_right_of_le'
- \+ *lemma* filter.tendsto_at_top_add_right_of_le
- \+ *lemma* filter.tendsto_at_top_at_bot
- \+ *lemma* filter.tendsto_at_top_at_top
- \+ *lemma* filter.tendsto_at_top_at_top_of_monotone
- \+ *lemma* filter.tendsto_at_top_embedding
- \+ *lemma* filter.tendsto_at_top_mono'
- \+ *lemma* filter.tendsto_at_top_mono
- \+ *lemma* filter.tendsto_at_top_of_add_bdd_above_left'
- \+ *lemma* filter.tendsto_at_top_of_add_bdd_above_left
- \+ *lemma* filter.tendsto_at_top_of_add_bdd_above_right'
- \+ *lemma* filter.tendsto_at_top_of_add_bdd_above_right
- \+ *lemma* filter.tendsto_at_top_of_add_const_left
- \+ *lemma* filter.tendsto_at_top_of_add_const_right
- \+ *theorem* filter.tendsto_at_top_principal
- \+ *lemma* filter.tendsto_finset_image_at_top_at_top
- \+ *lemma* filter.tendsto_finset_range
- \+ *lemma* filter.tendsto_sub_at_top_nat

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \- *lemma* filter.Iio_mem_at_bot
- \- *lemma* filter.Ioi_mem_at_top
- \- *def* filter.at_bot
- \- *def* filter.at_top
- \- *lemma* filter.at_top_ne_bot
- \- *def* filter.cofinite
- \- *lemma* filter.cofinite_ne_bot
- \- *theorem* filter.compl_mem_hyperfilter_of_finite
- \- *lemma* filter.eventually.exists_forall_of_at_top
- \- *lemma* filter.eventually_at_top
- \- *lemma* filter.exists_le_of_tendsto_at_top
- \- *lemma* filter.exists_lt_of_tendsto_at_top
- \- *lemma* filter.exists_ultrafilter
- \- *lemma* filter.exists_ultrafilter_iff
- \- *lemma* filter.extraction_of_eventually_at_top
- \- *lemma* filter.extraction_of_frequently_at_top'
- \- *lemma* filter.extraction_of_frequently_at_top
- \- *lemma* filter.frequently.forall_exists_of_at_top
- \- *lemma* filter.frequently_at_top'
- \- *lemma* filter.frequently_at_top
- \- *lemma* filter.frequently_cofinite_iff_infinite
- \- *lemma* filter.frequently_high_scores
- \- *lemma* filter.high_scores
- \- *lemma* filter.hyperfilter_le_cofinite
- \- *def* filter.is_ultrafilter
- \- *lemma* filter.is_ultrafilter_hyperfilter
- \- *lemma* filter.le_of_ultrafilter
- \- *lemma* filter.map_add_at_top_eq_nat
- \- *lemma* filter.map_at_top_eq
- \- *lemma* filter.map_at_top_eq_of_gc
- \- *lemma* filter.map_at_top_inf_ne_bot_iff
- \- *lemma* filter.map_div_at_top_eq_nat
- \- *lemma* filter.map_sub_at_top_eq_nat
- \- *lemma* filter.mem_at_bot
- \- *lemma* filter.mem_at_top
- \- *lemma* filter.mem_at_top_sets
- \- *lemma* filter.mem_cofinite
- \- *theorem* filter.mem_hyperfilter_of_finite_compl
- \- *lemma* filter.mem_of_finite_Union_ultrafilter
- \- *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \- *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \- *lemma* filter.mem_or_mem_of_ultrafilter
- \- *lemma* filter.monotone.tendsto_at_top_finset
- \- *lemma* filter.nat.cofinite_eq_at_top
- \- *theorem* filter.nmem_hyperfilter_of_finite
- \- *lemma* filter.prod_at_top_at_top_eq
- \- *lemma* filter.prod_map_at_top_eq
- \- *lemma* filter.set.infinite_iff_frequently_cofinite
- \- *lemma* filter.strict_mono_subseq_of_id_le
- \- *lemma* filter.strict_mono_subseq_of_tendsto_at_top
- \- *lemma* filter.strict_mono_tendsto_at_top
- \- *lemma* filter.sup_of_ultrafilters
- \- *lemma* filter.tendsto_add_at_top_iff_nat
- \- *lemma* filter.tendsto_add_at_top_nat
- \- *lemma* filter.tendsto_at_top'
- \- *lemma* filter.tendsto_at_top
- \- *lemma* filter.tendsto_at_top_add_const_left
- \- *lemma* filter.tendsto_at_top_add_const_right
- \- *lemma* filter.tendsto_at_top_add_left_of_le'
- \- *lemma* filter.tendsto_at_top_add_left_of_le
- \- *lemma* filter.tendsto_at_top_add_nonneg_left'
- \- *lemma* filter.tendsto_at_top_add_nonneg_left
- \- *lemma* filter.tendsto_at_top_add_nonneg_right'
- \- *lemma* filter.tendsto_at_top_add_nonneg_right
- \- *lemma* filter.tendsto_at_top_add_right_of_le'
- \- *lemma* filter.tendsto_at_top_add_right_of_le
- \- *lemma* filter.tendsto_at_top_at_bot
- \- *lemma* filter.tendsto_at_top_at_top
- \- *lemma* filter.tendsto_at_top_at_top_of_monotone
- \- *lemma* filter.tendsto_at_top_embedding
- \- *lemma* filter.tendsto_at_top_mono'
- \- *lemma* filter.tendsto_at_top_mono
- \- *lemma* filter.tendsto_at_top_of_add_bdd_above_left'
- \- *lemma* filter.tendsto_at_top_of_add_bdd_above_left
- \- *lemma* filter.tendsto_at_top_of_add_bdd_above_right'
- \- *lemma* filter.tendsto_at_top_of_add_bdd_above_right
- \- *lemma* filter.tendsto_at_top_of_add_const_left
- \- *lemma* filter.tendsto_at_top_of_add_const_right
- \- *theorem* filter.tendsto_at_top_principal
- \- *lemma* filter.tendsto_finset_image_at_top_at_top
- \- *lemma* filter.tendsto_finset_range
- \- *lemma* filter.tendsto_iff_ultrafilter
- \- *lemma* filter.tendsto_sub_at_top_nat
- \- *def* filter.ultrafilter.bind
- \- *lemma* filter.ultrafilter.eq_iff_val_le_val
- \- *def* filter.ultrafilter.map
- \- *def* filter.ultrafilter.pure
- \- *def* filter.ultrafilter
- \- *lemma* filter.ultrafilter_bind
- \- *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem
- \- *lemma* filter.ultrafilter_map
- \- *lemma* filter.ultrafilter_of_le
- \- *lemma* filter.ultrafilter_of_spec
- \- *lemma* filter.ultrafilter_of_ultrafilter
- \- *lemma* filter.ultrafilter_pure
- \- *lemma* filter.ultrafilter_ultrafilter_of
- \- *lemma* filter.ultrafilter_unique

Added src/order/filter/cofinite.lean
- \+ *def* filter.cofinite
- \+ *lemma* filter.cofinite_ne_bot
- \+ *lemma* filter.frequently_cofinite_iff_infinite
- \+ *lemma* filter.mem_cofinite
- \+ *lemma* nat.cofinite_eq_at_top
- \+ *lemma* set.infinite_iff_frequently_cofinite

Modified src/order/filter/filter_product.lean


Added src/order/filter/ultrafilter.lean
- \+ *theorem* filter.compl_mem_hyperfilter_of_finite
- \+ *lemma* filter.exists_ultrafilter
- \+ *lemma* filter.exists_ultrafilter_iff
- \+ *lemma* filter.hyperfilter_le_cofinite
- \+ *def* filter.is_ultrafilter
- \+ *lemma* filter.is_ultrafilter_hyperfilter
- \+ *lemma* filter.le_of_ultrafilter
- \+ *theorem* filter.mem_hyperfilter_of_finite_compl
- \+ *lemma* filter.mem_of_finite_Union_ultrafilter
- \+ *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \+ *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \+ *lemma* filter.mem_or_mem_of_ultrafilter
- \+ *theorem* filter.nmem_hyperfilter_of_finite
- \+ *lemma* filter.sup_of_ultrafilters
- \+ *lemma* filter.tendsto_iff_ultrafilter
- \+ *def* filter.ultrafilter.bind
- \+ *lemma* filter.ultrafilter.eq_iff_val_le_val
- \+ *def* filter.ultrafilter.map
- \+ *def* filter.ultrafilter.pure
- \+ *def* filter.ultrafilter
- \+ *lemma* filter.ultrafilter_bind
- \+ *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem
- \+ *lemma* filter.ultrafilter_map
- \+ *lemma* filter.ultrafilter_of_le
- \+ *lemma* filter.ultrafilter_of_spec
- \+ *lemma* filter.ultrafilter_of_ultrafilter
- \+ *lemma* filter.ultrafilter_pure
- \+ *lemma* filter.ultrafilter_ultrafilter_of
- \+ *lemma* filter.ultrafilter_unique

Modified src/order/liminf_limsup.lean


Modified src/topology/basic.lean




## [2020-06-17 11:06:54](https://github.com/leanprover-community/mathlib/commit/077cd7c)
feat(algebra/category/Algebra): basic setup for category of bundled R-algebras ([#3047](https://github.com/leanprover-community/mathlib/pull/3047))
Just boilerplate. If I don't run out of enthusiasm I'll do tensor product of R-algebras soon. ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))
#### Estimated changes
Added src/algebra/category/Algebra/basic.lean
- \+ *lemma* Algebra.coe_comp
- \+ *lemma* Algebra.id_apply
- \+ *def* Algebra.of
- \+ *lemma* Algebra.of_apply
- \+ *def* Algebra.of_self_iso
- \+ *structure* Algebra
- \+ *def* alg_equiv.to_Algebra_iso
- \+ *def* alg_equiv_iso_Algebra_iso
- \+ *def* category_theory.iso.to_alg_equiv

Modified src/algebra/category/Module/basic.lean
- \- *def* linear_equiv_iso_Group_iso
- \+ *def* linear_equiv_iso_Module_iso

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.coe_fun_injective
- \+ *lemma* alg_equiv.coe_ring_equiv_injective
- \+ *lemma* alg_equiv.ext



## [2020-06-17 09:57:50](https://github.com/leanprover-community/mathlib/commit/54441b5)
feat(algebra/group_action_hom): define equivariant maps ([#2866](https://github.com/leanprover-community/mathlib/pull/2866))
#### Estimated changes
Added src/algebra/group_action_hom.lean
- \+ *lemma* distrib_mul_action_hom.coe_fn_coe'
- \+ *lemma* distrib_mul_action_hom.coe_fn_coe
- \+ *def* distrib_mul_action_hom.comp
- \+ *lemma* distrib_mul_action_hom.comp_apply
- \+ *lemma* distrib_mul_action_hom.comp_id
- \+ *theorem* distrib_mul_action_hom.ext
- \+ *theorem* distrib_mul_action_hom.ext_iff
- \+ *lemma* distrib_mul_action_hom.id_apply
- \+ *lemma* distrib_mul_action_hom.id_comp
- \+ *lemma* distrib_mul_action_hom.map_add
- \+ *lemma* distrib_mul_action_hom.map_neg
- \+ *lemma* distrib_mul_action_hom.map_smul
- \+ *lemma* distrib_mul_action_hom.map_sub
- \+ *lemma* distrib_mul_action_hom.map_zero
- \+ *structure* distrib_mul_action_hom
- \+ *def* mul_action_hom.comp
- \+ *lemma* mul_action_hom.comp_apply
- \+ *lemma* mul_action_hom.comp_id
- \+ *theorem* mul_action_hom.ext
- \+ *theorem* mul_action_hom.ext_iff
- \+ *lemma* mul_action_hom.id_apply
- \+ *lemma* mul_action_hom.id_comp
- \+ *lemma* mul_action_hom.map_smul
- \+ *def* mul_action_hom.to_quotient
- \+ *lemma* mul_action_hom.to_quotient_apply
- \+ *structure* mul_action_hom
- \+ *lemma* mul_semiring_action_hom.coe_fn_coe'
- \+ *lemma* mul_semiring_action_hom.coe_fn_coe
- \+ *def* mul_semiring_action_hom.comp
- \+ *lemma* mul_semiring_action_hom.comp_apply
- \+ *lemma* mul_semiring_action_hom.comp_id
- \+ *theorem* mul_semiring_action_hom.ext
- \+ *theorem* mul_semiring_action_hom.ext_iff
- \+ *lemma* mul_semiring_action_hom.id_apply
- \+ *lemma* mul_semiring_action_hom.id_comp
- \+ *lemma* mul_semiring_action_hom.map_add
- \+ *lemma* mul_semiring_action_hom.map_mul
- \+ *lemma* mul_semiring_action_hom.map_neg
- \+ *lemma* mul_semiring_action_hom.map_one
- \+ *lemma* mul_semiring_action_hom.map_smul
- \+ *lemma* mul_semiring_action_hom.map_sub
- \+ *lemma* mul_semiring_action_hom.map_zero
- \+ *structure* mul_semiring_action_hom



## [2020-06-17 03:12:21](https://github.com/leanprover-community/mathlib/commit/e40de30)
chore(category_theory/closed): move one thing to monoidal closed and fix naming ([#3090](https://github.com/leanprover-community/mathlib/pull/3090))
Move one of the CCC defs to MCC as an example, and make the naming consistent.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+ *def* category_theory.cartesian_closed.curry
- \+ *def* category_theory.cartesian_closed.uncurry
- \- *def* category_theory.is_cartesian_closed.curry
- \- *def* category_theory.is_cartesian_closed.uncurry
- \+/\- *def* category_theory.terminal_exponentiable

Modified src/category_theory/closed/monoidal.lean
- \+ *def* category_theory.unit_closed

Modified src/category_theory/monoidal/category.lean




## [2020-06-17 00:45:09](https://github.com/leanprover-community/mathlib/commit/a19dca6)
chore(scripts): update nolints.txt ([#3091](https://github.com/leanprover-community/mathlib/pull/3091))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-16 19:33:00](https://github.com/leanprover-community/mathlib/commit/e3c9fd8)
feat(topology): sequential compactness ([#3061](https://github.com/leanprover-community/mathlib/pull/3061))
This is the long overdue PR bringing Bolzano-Weierstrass to mathlib. I'm sorry it's a bit large. I did use a couple of preliminary PRs, that one is really about converging subsequences, but supporting material is spread in many files.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *def* nat.strong_rec_on'
- \+ *theorem* nat.strong_rec_on_beta'

Modified src/data/set/finite.lean
- \+ *lemma* set.seq_of_forall_finite_exists

Modified src/data/set/lattice.lean
- \+ *theorem* set.bUnion_mono
- \+ *theorem* set.bUnion_subset_bUnion

Modified src/order/basic.lean
- \+ *lemma* strict_mono.id_le

Modified src/order/filter/bases.lean
- \+ *lemma* filter.is_countably_generated.subseq_tendsto

Modified src/order/filter/basic.lean
- \+ *lemma* filter.exists_le_of_tendsto_at_top
- \+ *lemma* filter.exists_lt_of_tendsto_at_top
- \+ *lemma* filter.extraction_of_eventually_at_top
- \+ *lemma* filter.extraction_of_frequently_at_top'
- \+ *lemma* filter.extraction_of_frequently_at_top
- \+ *lemma* filter.frequently_high_scores
- \+ *lemma* filter.frequently_of_forall
- \+ *lemma* filter.high_scores
- \+ *lemma* filter.strict_mono_subseq_of_id_le
- \+ *lemma* filter.strict_mono_subseq_of_tendsto_at_top
- \+ *lemma* filter.strict_mono_tendsto_at_top

Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/bases.lean
- \+ *lemma* topological_space.first_countable_topology.tendsto_subseq

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.ball_eq_ball'
- \+ *lemma* metric.ball_eq_ball
- \+ *lemma* metric.bounded_closure_of_bounded
- \+ *theorem* metric.finite_approx_of_totally_bounded
- \+/\- *lemma* metric.totally_bounded_of_finite_discretization

Modified src/topology/sequences.lean
- \+ *lemma* compact.seq_compact
- \+ *lemma* compact.tendsto_subseq'
- \+ *lemma* compact.tendsto_subseq
- \+ *lemma* compact_space.tendsto_subseq
- \+ *lemma* lebesgue_number_lemma_seq
- \+ *lemma* metric.compact_iff_seq_compact
- \+ *lemma* metric.compact_space_iff_seq_compact_space
- \+ *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+ *lemma* seq_compact.subseq_of_frequently_in
- \+ *lemma* seq_compact.totally_bounded
- \+ *def* seq_compact
- \+ *lemma* seq_compact_space.tendsto_subseq
- \+ *lemma* tendsto_subseq_of_bounded
- \+ *lemma* tendsto_subseq_of_frequently_bounded
- \+ *lemma* uniform_space.compact_space_iff_seq_compact_space

Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.mem_entourage
- \+ *lemma* totally_bounded_of_forall_symm



## [2020-06-16 17:58:48](https://github.com/leanprover-community/mathlib/commit/a478f91)
chore(algebra/ring): move `add_mul_self_eq` to `comm_semiring` ([#3089](https://github.com/leanprover-community/mathlib/pull/3089))
Also use `alias` instead of `def ... := @...` to make linter happy.
Fixes https://github.com/leanprover-community/lean/issues/232
#### Estimated changes
Modified src/algebra/ring.lean
- \- *def* dvd.trans
- \- *def* dvd_of_mul_left_eq
- \- *def* dvd_of_mul_right_eq



## [2020-06-16 17:08:01](https://github.com/leanprover-community/mathlib/commit/ae6bf56)
feat(ring_theory/tensor_product): tensor product of algebras ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))
The R-algebra structure on the tensor product of two R-algebras.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_equiv.coe_coe
- \+/\- *lemma* linear_equiv.coe_to_equiv
- \+ *lemma* linear_equiv.inv_fun_apply
- \+ *lemma* linear_equiv.mk_apply
- \+ *lemma* linear_equiv.to_fun_apply

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* tensor_product.comm_tmul

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.coe_alg_hom
- \- *lemma* alg_equiv.coe_to_alg_equiv
- \+ *lemma* alg_equiv.inv_fun_apply
- \+ *lemma* alg_equiv.mk_apply
- \+ *def* alg_equiv.of_alg_hom
- \+ *lemma* alg_equiv.to_fun_apply
- \+/\- *theorem* alg_hom.ext
- \+ *theorem* alg_hom.ext_iff

Added src/ring_theory/tensor_product.lean
- \+ *def* algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product
- \+ *lemma* algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product_apply
- \+ *def* algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product
- \+ *lemma* algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product_apply
- \+ *def* algebra.tensor_product.alg_hom_of_linear_map_tensor_product
- \+ *lemma* algebra.tensor_product.algebra_map_apply
- \+ *lemma* algebra.tensor_product.assoc_aux_1
- \+ *lemma* algebra.tensor_product.assoc_aux_2
- \+ *theorem* algebra.tensor_product.comm_tmul
- \+ *def* algebra.tensor_product.congr
- \+ *lemma* algebra.tensor_product.congr_apply
- \+ *lemma* algebra.tensor_product.congr_symm_apply
- \+ *theorem* algebra.tensor_product.ext
- \+ *def* algebra.tensor_product.include_left
- \+ *def* algebra.tensor_product.include_right
- \+ *theorem* algebra.tensor_product.lid_tmul
- \+ *def* algebra.tensor_product.map
- \+ *theorem* algebra.tensor_product.map_tmul
- \+ *def* algebra.tensor_product.mul
- \+ *lemma* algebra.tensor_product.mul_apply
- \+ *lemma* algebra.tensor_product.mul_assoc'
- \+ *lemma* algebra.tensor_product.mul_assoc
- \+ *def* algebra.tensor_product.mul_aux
- \+ *lemma* algebra.tensor_product.mul_aux_apply
- \+ *lemma* algebra.tensor_product.mul_one
- \+ *lemma* algebra.tensor_product.mul_tmul
- \+ *lemma* algebra.tensor_product.one_def
- \+ *lemma* algebra.tensor_product.one_mul
- \+ *theorem* algebra.tensor_product.rid_tmul
- \+ *def* algebra.tensor_product.tensor_algebra_map



## [2020-06-16 06:49:06](https://github.com/leanprover-community/mathlib/commit/a432a3a)
feat(analysis/convex): Carathéodory's convexity theorem ([#2960](https://github.com/leanprover-community/mathlib/pull/2960))
```
theorem caratheodory (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1), convex_hull ↑t
```
and more explicitly
```
theorem eq_center_mass_card_dim_succ_of_mem_convex_hull (s : set E) (x : E) (h : x ∈ convex_hull s) :
  ∃ (t : finset E) (w : ↑t ⊆ s) (b : t.card ≤ findim ℝ E + 1)
    (f : E → ℝ), (∀ y ∈ t, 0 ≤ f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x
```
#### Estimated changes
Added src/analysis/convex/caratheodory.lean
- \+ *lemma* caratheodory.mem_convex_hull_erase
- \+ *lemma* caratheodory.shrink'
- \+ *lemma* caratheodory.shrink
- \+ *lemma* caratheodory.step
- \+ *theorem* convex_hull_eq_union
- \+ *lemma* convex_hull_subset_union
- \+ *theorem* eq_center_mass_card_le_dim_succ_of_mem_convex_hull
- \+ *theorem* eq_pos_center_mass_card_le_dim_succ_of_mem_convex_hull



## [2020-06-16 04:03:38](https://github.com/leanprover-community/mathlib/commit/b51028f)
chore(linear_algebra/finite_dimensional): lin-indep lemma typos ([#3086](https://github.com/leanprover-community/mathlib/pull/3086))
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean




## [2020-06-16 02:35:24](https://github.com/leanprover-community/mathlib/commit/e087174)
feat(linear_algebra/finite_dimensional): bases given by finsets ([#3041](https://github.com/leanprover-community/mathlib/pull/3041))
In some cases, it might be more straightforward working with finsets of
the vector space instead of indexed types or carrying around a proof of
set.finite. Also provide a lemma on equal dimension
and basis cardinality lemma that uses a finset basis.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.exists_is_basis_finset
- \+ *lemma* finite_dimensional.findim_eq_card_finset_basis
- \+ *lemma* finite_dimensional.of_finset_basis



## [2020-06-15 23:58:09](https://github.com/leanprover-community/mathlib/commit/a796008)
feat(category_theory): cartesian closed categories ([#2894](https://github.com/leanprover-community/mathlib/pull/2894))
Cartesian closed categories, from my topos project.
#### Estimated changes
Added src/category_theory/closed/cartesian.lean
- \+ *def* category_theory.binary_product_exponentiable
- \+ *abbreviation* category_theory.cartesian_closed
- \+ *def* category_theory.cartesian_closed_of_equiv
- \+ *def* category_theory.coev
- \+ *lemma* category_theory.coev_ev
- \+ *lemma* category_theory.curry_eq
- \+ *lemma* category_theory.curry_eq_iff
- \+ *lemma* category_theory.curry_id_eq_coev
- \+ *lemma* category_theory.curry_injective
- \+ *lemma* category_theory.curry_natural_left
- \+ *lemma* category_theory.curry_natural_right
- \+ *lemma* category_theory.curry_uncurry
- \+ *lemma* category_theory.eq_curry_iff
- \+ *def* category_theory.ev
- \+ *lemma* category_theory.ev_coev
- \+ *def* category_theory.exp.adjunction
- \+ *def* category_theory.exp
- \+ *def* category_theory.exp_comparison
- \+ *lemma* category_theory.exp_comparison_natural_left
- \+ *lemma* category_theory.exp_comparison_natural_right
- \+ *def* category_theory.exp_terminal_iso_self
- \+ *abbreviation* category_theory.exponentiable
- \+ *def* category_theory.internal_hom
- \+ *def* category_theory.internalize_hom
- \+ *def* category_theory.is_cartesian_closed.curry
- \+ *def* category_theory.is_cartesian_closed.uncurry
- \+ *def* category_theory.mul_zero
- \+ *def* category_theory.pow_zero
- \+ *def* category_theory.pre
- \+ *lemma* category_theory.pre_id
- \+ *lemma* category_theory.pre_map
- \+ *lemma* category_theory.pre_post_comm
- \+ *def* category_theory.prod_coprod_distrib
- \+ *def* category_theory.terminal_exponentiable
- \+ *lemma* category_theory.uncurry_curry
- \+ *lemma* category_theory.uncurry_eq
- \+ *lemma* category_theory.uncurry_id_eq_ev
- \+ *lemma* category_theory.uncurry_injective
- \+ *lemma* category_theory.uncurry_natural_left
- \+ *lemma* category_theory.uncurry_natural_right
- \+ *def* category_theory.zero_mul

Added src/category_theory/closed/monoidal.lean


Modified src/category_theory/epi_mono.lean
- \+ *def* category_theory.is_iso_of_epi_of_split_mono
- \+ *def* category_theory.is_iso_of_mono_of_split_epi

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.inv_prod_comparison_map_fst
- \+ *lemma* category_theory.limits.inv_prod_comparison_map_snd
- \+ *lemma* category_theory.limits.prod_comparison_inv_natural

Modified src/category_theory/monoidal/category.lean
- \+ *def* category_theory.monoidal_category.tensor_left
- \+ *def* category_theory.monoidal_category.tensor_left_tensor
- \+ *lemma* category_theory.monoidal_category.tensor_left_tensor_hom_app
- \+ *lemma* category_theory.monoidal_category.tensor_left_tensor_inv_app
- \+ *def* category_theory.monoidal_category.tensor_right
- \+ *def* category_theory.monoidal_category.tensor_right_tensor
- \+ *lemma* category_theory.monoidal_category.tensor_right_tensor_hom_app
- \+ *lemma* category_theory.monoidal_category.tensor_right_tensor_inv_app

Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.tensor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_coproducts.tensor_obj
- \+ *lemma* category_theory.monoidal_of_has_finite_products.tensor_hom
- \+ *lemma* category_theory.monoidal_of_has_finite_products.tensor_obj



## [2020-06-15 20:59:03](https://github.com/leanprover-community/mathlib/commit/25e414d)
feat(tactic/linarith): nlinarith tactic ([#2637](https://github.com/leanprover-community/mathlib/pull/2637))
Based on Coq's [nra](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.nra) tactic, and requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nonlinear.20linarith).
#### Estimated changes
Modified src/data/bool.lean


Modified src/data/list/defs.lean
- \+ *def* list.mmap'_diag

Modified src/tactic/linarith.lean
- \+ *lemma* linarith.mul_zero_eq
- \+ *lemma* linarith.zero_mul_eq

Modified test/linarith.lean
- \- *lemma* test6



## [2020-06-15 16:49:19](https://github.com/leanprover-community/mathlib/commit/2e752e1)
feat(tactic/group): group normalization tactic ([#3062](https://github.com/leanprover-community/mathlib/pull/3062))
A tactic to normalize expressions in multiplicative groups.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* mul_gpow_neg_one
- \+ *lemma* mul_gpow_self
- \+ *lemma* mul_self_gpow

Modified src/tactic/default.lean


Added src/tactic/group.lean
- \+ *lemma* tactic.group.gpow_trick
- \+ *lemma* tactic.group.gpow_trick_one'
- \+ *lemma* tactic.group.gpow_trick_one
- \+ *lemma* tactic.group.gpow_trick_sub

Added test/group.lean
- \+ *def* commutator3
- \+ *def* commutator



## [2020-06-15 15:45:46](https://github.com/leanprover-community/mathlib/commit/aa35f36)
feat(analysis/hofer): Hofer's lemma ([#3064](https://github.com/leanprover-community/mathlib/pull/3064))
Adds Hofer's lemma about complete metric spaces, with supporting material.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* div_pow_le
- \+ *lemma* pos_div_pow_pos

Added src/analysis/hofer.lean
- \+ *lemma* hofer

Modified src/analysis/specific_limits.lean
- \+ *lemma* geom_lt
- \+ *lemma* sum_geometric_two_le
- \+ *lemma* tendsto_at_top_of_geom_lt

Modified src/order/filter/basic.lean
- \+ *lemma* filter.Iio_mem_at_bot
- \+ *lemma* filter.Ioi_mem_at_top
- \+ *lemma* filter.inf_eq_bot_iff
- \+ *lemma* filter.mem_at_bot
- \+ *lemma* filter.tendsto.not_tendsto

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Iio_mem_nhds
- \+ *lemma* Ioi_mem_nhds
- \+ *lemma* Ioo_mem_nhds
- \+ *lemma* disjoint_nhds_at_bot
- \+ *lemma* disjoint_nhds_at_top
- \+ *lemma* inf_nhds_at_bot
- \+ *lemma* inf_nhds_at_top
- \+ *lemma* not_tendsto_at_bot_of_tendsto_nhds
- \+ *lemma* not_tendsto_at_top_of_tendsto_nhds
- \+ *lemma* not_tendsto_nhds_of_tendsto_at_bot
- \+ *lemma* not_tendsto_nhds_of_tendsto_at_top



## [2020-06-15 13:00:34](https://github.com/leanprover-community/mathlib/commit/4843bb1)
chore(linear_algebra/finsupp_vector_space): remove leftover pp.universes ([#3081](https://github.com/leanprover-community/mathlib/pull/3081))
See also [#1608](https://github.com/leanprover-community/mathlib/pull/1608).
#### Estimated changes
Modified src/linear_algebra/finsupp_vector_space.lean




## [2020-06-15 08:05:05](https://github.com/leanprover-community/mathlib/commit/758806e)
feat(linear_algebra/affine_space): more on affine subspaces ([#3076](https://github.com/leanprover-community/mathlib/pull/3076))
Add extensionality lemmas for affine subspaces, and a constructor to
make an affine subspace from a point and a direction.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_subspace.direction_mk_of_point_of_direction
- \+ *lemma* affine_subspace.ext
- \+ *lemma* affine_subspace.ext_of_direction_eq
- \+ *lemma* affine_subspace.mem_mk_of_point_of_direction
- \+ *def* affine_subspace.mk_of_point_of_direction
- \+ *lemma* affine_subspace.mk_of_point_of_direction_eq



## [2020-06-15 02:06:19](https://github.com/leanprover-community/mathlib/commit/543359c)
feat(field_theory/finite): Chevalley–Warning ([#1564](https://github.com/leanprover-community/mathlib/pull/1564))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.coe_subtype_equiv_codomain
- \+ *lemma* equiv.coe_subtype_equiv_codomain_symm
- \+ *def* equiv.subtype_equiv_codomain
- \+ *lemma* equiv.subtype_equiv_codomain_apply
- \+ *lemma* equiv.subtype_equiv_codomain_symm_apply
- \+ *lemma* equiv.subtype_equiv_codomain_symm_apply_eq
- \+ *lemma* equiv.subtype_equiv_codomain_symm_apply_ne

Modified src/data/finsupp.lean
- \+ *lemma* finsupp.prod_fintype

Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.eval_eq'
- \+ *lemma* mv_polynomial.eval_eq
- \+ *lemma* mv_polynomial.eval_prod
- \+ *lemma* mv_polynomial.eval_sum
- \+ *lemma* mv_polynomial.eval₂_eq'
- \+ *lemma* mv_polynomial.eval₂_eq
- \+ *lemma* mv_polynomial.exists_degree_lt

Added src/field_theory/chevalley_warning.lean
- \+ *theorem* char_dvd_card_solutions
- \+ *theorem* char_dvd_card_solutions_family
- \+ *lemma* mv_polynomial.sum_mv_polynomial_eq_zero



## [2020-06-15 01:22:53](https://github.com/leanprover-community/mathlib/commit/3a66d9a)
feat(polynomial): generalising some material to (noncomm_)semiring ([#3043](https://github.com/leanprover-community/mathlib/pull/3043))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.coeff_sum
- \+ *lemma* polynomial.monomial_eq_smul_X
- \+ *lemma* polynomial.monomial_one_eq_X_pow
- \+/\- *def* polynomial

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/adjoin_root.lean




## [2020-06-15 00:49:47](https://github.com/leanprover-community/mathlib/commit/01732f7)
chore(scripts): update nolints.txt ([#3078](https://github.com/leanprover-community/mathlib/pull/3078))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-15 00:15:36](https://github.com/leanprover-community/mathlib/commit/c91fc15)
chore(geometry/manifold/real_instances): use euclidean_space ([#3077](https://github.com/leanprover-community/mathlib/pull/3077))
Now that `euclidean_space` has been refactored to use the product topology, we can fix the geometry file that used a version of the product space (with the sup norm!) called `euclidean_space2`, using now instead the proper `euclidean_space`.
#### Estimated changes
Modified src/geometry/manifold/real_instances.lean
- \+/\- *def* euclidean_quadrant
- \- *def* euclidean_space2
- \- *lemma* findim_euclidean_space2



## [2020-06-14 20:40:58](https://github.com/leanprover-community/mathlib/commit/c4a32e7)
doc(topology/uniform_space/basic): library note on forgetful inheritance ([#3070](https://github.com/leanprover-community/mathlib/pull/3070))
A (long) library note explaining design decisions related to forgetful inheritance, and reference to this note in various places (I have probably forgotten a few of them).
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/pi_Lp.lean


Modified src/topology/uniform_space/basic.lean




## [2020-06-14 19:26:34](https://github.com/leanprover-community/mathlib/commit/797177c)
feat(linear_algebra/affine_space): affine combinations of points ([#2979](https://github.com/leanprover-community/mathlib/pull/2979))
Some basic definitions and lemmas related to affine combinations of
points, in preparation for defining barycentric coordinates for use in
geometry.
This version for sums over a `fintype` is probably the most convenient
for geometrical uses (where the type will be `fin 3` in the case of a
triangle, or more generally `fin (n + 1)` for an n-simplex), but other
use cases may find that `finset` or `finsupp` versions of these
definitions are of use as well.
The definition `weighted_vsub` is expected to be used with weights
that sum to zero, and the definition `affine_combination` is expected
to be used with weights that sum to 1, but such a hypothesis is only
specified for lemmas that need it rather than for those definitions.
I expect that most nontrivial geometric uses of barycentric
coordinates will need to prove such a hypothesis at some point, but
that it will still be more convenient not to need to pass it to all
the definitions and trivial lemmas.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* pi.vadd_apply

Modified src/linear_algebra/affine_space.lean
- \+ *def* affine_map.weighted_vsub_of_point
- \+ *def* affine_space.affine_combination
- \+ *lemma* affine_space.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \+ *lemma* affine_space.affine_combination_vsub
- \+ *def* affine_space.weighted_vsub
- \+ *lemma* affine_space.weighted_vsub_add
- \+ *lemma* affine_space.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \+ *lemma* affine_space.weighted_vsub_neg
- \+ *def* affine_space.weighted_vsub_of_point
- \+ *lemma* affine_space.weighted_vsub_of_point_add
- \+ *lemma* affine_space.weighted_vsub_of_point_eq_of_sum_eq_zero
- \+ *def* affine_space.weighted_vsub_of_point_linear
- \+ *lemma* affine_space.weighted_vsub_of_point_linear_apply
- \+ *lemma* affine_space.weighted_vsub_of_point_neg
- \+ *lemma* affine_space.weighted_vsub_of_point_smul
- \+ *lemma* affine_space.weighted_vsub_of_point_sub
- \+ *lemma* affine_space.weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \+ *lemma* affine_space.weighted_vsub_of_point_zero
- \+ *lemma* affine_space.weighted_vsub_smul
- \+ *lemma* affine_space.weighted_vsub_sub
- \+ *lemma* affine_space.weighted_vsub_vadd_affine_combination
- \+ *lemma* affine_space.weighted_vsub_zero



## [2020-06-14 16:36:35](https://github.com/leanprover-community/mathlib/commit/77c5dfe)
perf(*): avoid `user_attribute.get_param` ([#3073](https://github.com/leanprover-community/mathlib/pull/3073))
Recent studies have shown that `monoid_localization.lean` is the slowest file in mathlib.  One hundred and three seconds (93%) of its class-leading runtime are spent in constructing the attribute cache for `_to_additive`.  This is due to the use of the `user_attribute.get_param` function inside `get_cache`.  See the [library note on user attribute parameters](https://leanprover-community.github.io/mathlib_docs/notes.html#user%20attribute%20parameters) for more information on this anti-pattern.
This PR removes two uses of `user_attribute.get_param`, one in `to_additive` and the other in `ancestor`.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/algebra.lean




## [2020-06-14 16:36:33](https://github.com/leanprover-community/mathlib/commit/0d05299)
chore(data/finset): rename `ext`/`ext'`/`ext_iff` ([#3069](https://github.com/leanprover-community/mathlib/pull/3069))
Now
* `ext` is the `@[ext]` lemma;
* `ext_iff` is the lemma `s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂`.
Also add 2 `norm_cast` attributes and a lemma `ssubset_iff_of_subset`.
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/finmap.lean


Modified src/data/finset.lean
- \+/\- *theorem* finset.coe_inj
- \- *theorem* finset.ext'
- \+/\- *theorem* finset.ext
- \+ *theorem* finset.ext_iff
- \+/\- *lemma* finset.mem_coe
- \+ *theorem* finset.ssubset_iff_of_subset

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.ssubset_iff_of_subset

Modified src/data/set/finite.lean


Modified src/field_theory/finite.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/sign.lean


Modified src/linear_algebra/basis.lean


Modified src/measure_theory/outer_measure.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/topology/metric_space/emetric_space.lean




## [2020-06-14 16:36:31](https://github.com/leanprover-community/mathlib/commit/1f16da1)
refactor(analysis/normed_space/real_inner_product): extend normed_space in the definition ([#3060](https://github.com/leanprover-community/mathlib/pull/3060))
Currently, inner product spaces do not extend normed spaces, and a norm is constructed from the inner product. This makes it impossible to put an instance on reals, because it would lead to two non-defeq norms. We refactor inner product spaces to extend normed spaces, with the condition that the norm is equal (but maybe not defeq) to the square root of the inner product, to solve this issue.
The possibility to construct a norm from a well-behaved inner product is still given by a constructor `inner_product_space.of_core`.
We also register the inner product structure on a finite product of inner product spaces (not on the Pi type, which has the sup norm, but on `pi_Lp 2 one_le_two \alpha` which has the right norm).
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \- *lemma* euclidean_space.inner_def
- \+/\- *def* euclidean_space
- \+ *lemma* findim_euclidean_space
- \+ *lemma* findim_euclidean_space_fin
- \+ *structure* inner_product_space.core
- \+ *lemma* inner_product_space.of_core.abs_inner_le_norm
- \+ *lemma* inner_product_space.of_core.inner_add_add_self
- \+ *lemma* inner_product_space.of_core.inner_add_left
- \+ *lemma* inner_product_space.of_core.inner_add_right
- \+ *lemma* inner_product_space.of_core.inner_comm
- \+ *lemma* inner_product_space.of_core.inner_mul_inner_self_le
- \+ *lemma* inner_product_space.of_core.inner_self_eq_norm_square
- \+ *lemma* inner_product_space.of_core.inner_smul_left
- \+ *lemma* inner_product_space.of_core.inner_smul_right
- \+ *lemma* inner_product_space.of_core.norm_eq_sqrt_inner
- \+ *def* inner_product_space.of_core.to_has_inner
- \+ *def* inner_product_space.of_core.to_has_norm
- \+ *def* inner_product_space.of_core.to_normed_group
- \+ *def* inner_product_space.of_core.to_normed_space
- \+ *def* inner_product_space.of_core
- \+/\- *lemma* inner_self_nonneg
- \- *lemma* norm_eq_sqrt_inner
- \- *def* pi.inner_product_space
- \- *def* real.inner_product_space

Modified src/geometry/manifold/real_instances.lean
- \+ *lemma* findim_euclidean_space2
- \- *lemma* findim_euclidean_space



## [2020-06-14 15:09:35](https://github.com/leanprover-community/mathlib/commit/85b8bdc)
perf(tactic/linarith): use key/value lists instead of rb_maps to represent linear expressions ([#3004](https://github.com/leanprover-community/mathlib/pull/3004))
This has essentially no effect on the test file, but scales much better. 
See discussion at https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/Real.20analysis for an example which is in reach with this change.
#### Estimated changes
Modified src/meta/rb_map.lean


Modified src/tactic/linarith.lean
- \+ *def* linarith.ineq.cmp
- \- *def* linarith.ineq.is_lt
- \+ *def* linarith.linexp.cmp
- \+ *def* linarith.linexp.contains
- \+ *def* linarith.linexp.get
- \+ *def* linarith.linexp.scale
- \+ *def* linarith.linexp.zfind
- \+ *def* linarith.linexp

Modified test/linarith.lean
- \+ *lemma* test6



## [2020-06-14 12:37:42](https://github.com/leanprover-community/mathlib/commit/7f60a62)
chore(order/basic): move unbundled order classes to `rel_classes ([#3066](https://github.com/leanprover-community/mathlib/pull/3066))
Reason: these classes are rarely used in `mathlib`, we don't need to mix them with classes extending `has_le`.
#### Estimated changes
Modified src/data/list/basic.lean


Modified src/order/basic.lean
- \- *lemma* antisymm_of_asymm
- \- *def* bounded
- \- *def* decidable_linear_order_of_STO'
- \- *theorem* is_antisymm.swap
- \- *theorem* is_asymm.swap
- \- *theorem* is_irrefl.swap
- \- *theorem* is_irrefl_of_is_asymm
- \- *theorem* is_linear_order.swap
- \- *theorem* is_order_connected.neg_trans
- \- *theorem* is_partial_order.swap
- \- *theorem* is_preorder.swap
- \- *theorem* is_refl.swap
- \- *theorem* is_strict_order.swap
- \- *theorem* is_strict_total_order'.swap
- \- *theorem* is_strict_weak_order_of_is_order_connected
- \- *theorem* is_total.swap
- \- *theorem* is_total_preorder.swap
- \- *theorem* is_trans.swap
- \- *theorem* is_trichotomous.swap
- \- *def* linear_order_of_STO'
- \- *lemma* not_bounded_iff
- \- *lemma* not_unbounded_iff
- \- *def* partial_order_of_SO
- \- *lemma* trans_trichotomous_left
- \- *lemma* trans_trichotomous_right
- \- *def* unbounded
- \- *theorem* well_founded.has_min
- \- *theorem* well_founded.min_mem
- \- *theorem* well_founded.not_lt_min

Modified src/order/order_iso.lean


Added src/order/rel_classes.lean
- \+ *def* bounded
- \+ *def* decidable_linear_order_of_STO'
- \+ *theorem* is_antisymm.swap
- \+ *theorem* is_asymm.swap
- \+ *theorem* is_irrefl.swap
- \+ *theorem* is_linear_order.swap
- \+ *theorem* is_order_connected.neg_trans
- \+ *theorem* is_partial_order.swap
- \+ *theorem* is_preorder.swap
- \+ *theorem* is_refl.swap
- \+ *theorem* is_strict_order.swap
- \+ *theorem* is_strict_total_order'.swap
- \+ *theorem* is_strict_weak_order_of_is_order_connected
- \+ *theorem* is_total.swap
- \+ *theorem* is_total_preorder.swap
- \+ *theorem* is_trans.swap
- \+ *theorem* is_trichotomous.swap
- \+ *def* linear_order_of_STO'
- \+ *lemma* not_bounded_iff
- \+ *lemma* not_unbounded_iff
- \+ *def* partial_order_of_SO
- \+ *lemma* trans_trichotomous_left
- \+ *lemma* trans_trichotomous_right
- \+ *def* unbounded
- \+ *theorem* well_founded.has_min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min



## [2020-06-14 12:37:40](https://github.com/leanprover-community/mathlib/commit/2c97f23)
feat(tactic/library_search): small improvements ([#3037](https://github.com/leanprover-community/mathlib/pull/3037))
This makes the following small improvements to `library_search`:
1. ~~Don't use `*.inj` lemmas, which are rarely useful. (Cuts test file from 95 seconds to 90 seconds.)~~
2. Some refactoring for reusability in other tactics.
3. `apply_declaration` now reports how many subgoals were successfully closed by `solve_by_elim` (for use by new tactics)
#### Estimated changes
Modified src/tactic/suggest.lean




## [2020-06-14 12:37:38](https://github.com/leanprover-community/mathlib/commit/a6534db)
feat(normed_space/dual): (topological) dual of a normed space ([#3021](https://github.com/leanprover-community/mathlib/pull/3021))
Define the topological dual of a normed space, and prove that over the reals, the inclusion into the double dual is an isometry.
Supporting material:  a corollary of Hahn-Banach; material about spans of singletons added to `linear_algebra.basic` and `normed_space.operator_norm`; material about homotheties added to `normed_space.operator_norm`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Added src/analysis/normed_space/dual.lean
- \+ *lemma* normed_space.double_dual_bound
- \+ *lemma* normed_space.dual_def
- \+ *def* normed_space.inclusion_in_double_dual'
- \+ *def* normed_space.inclusion_in_double_dual
- \+ *lemma* normed_space.inclusion_in_double_dual_isometry

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *lemma* coord_norm'
- \+ *lemma* coord_self'
- \+ *theorem* exists_dual_vector'
- \+ *theorem* exists_dual_vector

Modified src/analysis/normed_space/operator_norm.lean
- \+ *abbreviation* continuous_linear_equiv.coord
- \+ *lemma* continuous_linear_equiv.coord_norm
- \+ *lemma* continuous_linear_equiv.homothety_inverse
- \+ *def* continuous_linear_equiv.of_homothety
- \+ *def* continuous_linear_equiv.to_span_nonzero_singleton
- \+ *lemma* continuous_linear_equiv.to_span_nonzero_singleton_homothety
- \+ *lemma* continuous_linear_map.homothety_norm
- \+ *def* continuous_linear_map.of_homothety
- \+ *def* continuous_linear_map.to_span_singleton
- \+ *lemma* continuous_linear_map.to_span_singleton_homothety
- \+ *lemma* continuous_linear_map.to_span_singleton_norm

Modified src/linear_algebra/basic.lean
- \+ *abbreviation* linear_equiv.coord
- \+ *lemma* linear_equiv.coord_self
- \+ *def* linear_equiv.to_span_nonzero_singleton
- \+ *lemma* linear_equiv.to_span_nonzero_singleton_one
- \+ *lemma* linear_map.span_singleton_eq_range
- \+ *def* linear_map.to_span_singleton
- \+ *lemma* linear_map.to_span_singleton_one
- \+ *lemma* submodule.mem_span_singleton_self

Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/algebra.lean
- \+ *def* subspace.restrict_scalars



## [2020-06-14 11:55:48](https://github.com/leanprover-community/mathlib/commit/4e88687)
chore(data/complex/basic): rearrange into sections ([#3068](https://github.com/leanprover-community/mathlib/pull/3068))
Also:
* reworded some docstrings,
* removed dependence on `deprecated.field` by changing the proofs of `of_real_div` and `of_real_fpow` to use `ring_hom` lemmas instead of `is_ring_hom` lemma,
* renamed the instance `of_real.is_ring_hom` too `coe.is_ring_hom`,
* renamed `real_prod_equiv*` to `equiv_prod_real*`, and
* `conj_two` was removed in favor of `conj_bit0` and `conj_bit1`.
#### Estimated changes
Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_abs_sub_le_abs_sub
- \+ *lemma* complex.conj_bit0
- \+ *lemma* complex.conj_bit1
- \- *lemma* complex.conj_two
- \+ *def* complex.equiv_real_prod
- \+ *theorem* complex.equiv_real_prod_apply
- \+ *theorem* complex.equiv_real_prod_symm_im
- \+ *theorem* complex.equiv_real_prod_symm_re
- \+/\- *lemma* complex.of_real_add
- \+/\- *lemma* complex.of_real_bit0
- \+/\- *lemma* complex.of_real_bit1
- \+/\- *theorem* complex.of_real_int_cast
- \+/\- *theorem* complex.of_real_rat_cast
- \- *def* complex.real_prod_equiv
- \- *theorem* complex.real_prod_equiv_apply
- \- *theorem* complex.real_prod_equiv_symm_im
- \- *theorem* complex.real_prod_equiv_symm_re

Modified src/data/complex/exponential.lean


Modified src/topology/instances/complex.lean




## [2020-06-14 09:10:57](https://github.com/leanprover-community/mathlib/commit/2cd329f)
feat(algebra/continued_fractions): add correctness of terminating computations ([#2911](https://github.com/leanprover-community/mathlib/pull/2911))
### What
Add correctness lemmas for terminating computations of continued fractions
### Why
To show that the continued fractions algorithm is computing the right thing in case of termination. For non-terminating sequences, lemmas about the limit will be added in a later PR.
### How
1. Show that the value to be approximated can always be obtained by adding the corresponding, remaining fractional part stored in `int_fract_pair.stream`.
2. Use this to derive that once the fractional part becomes 0 (and hence the continued fraction terminates), we have exactly computed the value.
#### Estimated changes
Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Added src/algebra/continued_fractions/computation/correctness_terminating.lean
- \+ *lemma* generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_none
- \+ *lemma* generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some
- \+ *lemma* generalized_continued_fraction.of_correctness_at_top_of_terminates
- \+ *theorem* generalized_continued_fraction.of_correctness_of_terminated_at
- \+ *lemma* generalized_continued_fraction.of_correctness_of_terminates

Modified src/algebra/continued_fractions/computation/default.lean


Modified src/algebra/continued_fractions/continuants_recurrence.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean




## [2020-06-14 08:08:09](https://github.com/leanprover-community/mathlib/commit/fdc326c)
feat(geometry/euclidean): sum of angles of a triangle ([#2994](https://github.com/leanprover-community/mathlib/pull/2994))
Item 27 from the 100-theorems list.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* euclidean_geometry.angle_add_angle_add_angle_eq_pi
- \+ *lemma* inner_product_geometry.angle_add_angle_sub_add_angle_sub_eq_pi
- \+ *lemma* inner_product_geometry.cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \+ *lemma* inner_product_geometry.cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \+ *lemma* inner_product_geometry.sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \+ *lemma* inner_product_geometry.sin_angle_sub_add_angle_sub_rev_eq_sin_angle



## [2020-06-14 04:30:41](https://github.com/leanprover-community/mathlib/commit/c8c1869)
refactor(order/basic): make `*order.lift` use `[]` argument ([#3067](https://github.com/leanprover-community/mathlib/pull/3067))
Take an order on the codomain as a `[*order β]` argument.
#### Estimated changes
Modified src/algebra/ordered_group.lean


Modified src/analysis/convex/cone.lean


Modified src/data/fin.lean


Modified src/data/real/nnreal.lean


Modified src/geometry/manifold/manifold.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean


Modified src/order/basic.lean
- \+/\- *def* decidable_linear_order.lift
- \+/\- *def* linear_order.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* preorder.lift

Modified src/order/zorn.lean


Modified src/ring_theory/subsemiring.lean


Modified src/topology/algebra/open_subgroup.lean




## [2020-06-14 01:30:16](https://github.com/leanprover-community/mathlib/commit/67f7288)
doc(measure_theory): document basic measure theory files ([#3057](https://github.com/leanprover-community/mathlib/pull/3057))
#### Estimated changes
Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean




## [2020-06-14 00:41:33](https://github.com/leanprover-community/mathlib/commit/0f98c37)
chore(scripts): update nolints.txt ([#3065](https://github.com/leanprover-community/mathlib/pull/3065))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-13 19:37:02](https://github.com/leanprover-community/mathlib/commit/e33245c)
feat(topology/metric_space/pi_Lp): L^p distance on finite products ([#3059](https://github.com/leanprover-community/mathlib/pull/3059))
`L^p` edistance (or distance, or norm) on finite products of emetric spaces (or metric spaces, or normed groups), put on a type synonym `pi_Lp p hp α` to avoid instance clashes, and being careful to register as uniformity the product uniformity.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.mul_rpow_of_nonneg
- \+/\- *lemma* ennreal.rpow_eq_top_iff
- \+/\- *lemma* ennreal.rpow_eq_zero_iff
- \+ *lemma* ennreal.to_real_rpow
- \+/\- *lemma* ennreal.top_rpow_of_neg
- \+/\- *lemma* ennreal.top_rpow_of_pos
- \+/\- *lemma* ennreal.zero_rpow_of_neg
- \+/\- *lemma* ennreal.zero_rpow_of_pos
- \+ *lemma* nnreal.rpow_neg_one

Added src/topology/metric_space/pi_Lp.lean
- \+ *lemma* pi_Lp.add_apply
- \+ *lemma* pi_Lp.antilipschitz_with_equiv
- \+ *lemma* pi_Lp.aux_uniformity_eq
- \+ *def* pi_Lp.emetric_aux
- \+ *lemma* pi_Lp.lipschitz_with_equiv
- \+ *lemma* pi_Lp.neg_apply
- \+ *lemma* pi_Lp.norm_eq
- \+ *lemma* pi_Lp.smul_apply
- \+ *lemma* pi_Lp.sub_apply
- \+ *def* pi_Lp



## [2020-06-13 13:42:10](https://github.com/leanprover-community/mathlib/commit/cc16d35)
feat(linear_algebra/finite_dimensional): cardinalities and linear independence ([#3056](https://github.com/leanprover-community/mathlib/pull/3056))
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.cardinal_mk_le_findim_of_linear_independent
- \+ *lemma* finite_dimensional.exists_nontrivial_relation_of_dim_lt_card
- \+ *lemma* finite_dimensional.exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
- \+ *lemma* finite_dimensional.exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card
- \+ *lemma* finite_dimensional.finset_card_le_findim_of_linear_independent
- \+ *lemma* finite_dimensional.fintype_card_le_findim_of_linear_independent



## [2020-06-13 12:38:45](https://github.com/leanprover-community/mathlib/commit/b7048a4)
feat(tactic/linarith): improve parsing expressions into linear form ([#2995](https://github.com/leanprover-community/mathlib/pull/2995))
This PR generalizes the parsing stage of `linarith`. It will try harder to recognize expressions as linear combinations of monomials, and will match monomials up to commutativity. 
```lean
example (u v r s t : ℚ) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u :=
by linarith
```
This is helpful for [#2637](https://github.com/leanprover-community/mathlib/pull/2637) .
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2020-06-13 11:08:59](https://github.com/leanprover-community/mathlib/commit/4bb29ab)
doc(algebra/group/to_additive): add doc strings and tactic doc entry ([#3055](https://github.com/leanprover-community/mathlib/pull/3055))
#### Estimated changes
Modified src/algebra/group/to_additive.lean
- \+/\- *structure* to_additive.value_type



## [2020-06-13 11:08:57](https://github.com/leanprover-community/mathlib/commit/a22b657)
refactor(topology/uniform_space): docstring and notation ([#3052](https://github.com/leanprover-community/mathlib/pull/3052))
The goal of this PR is to make `topology/uniform_space/basic.lean` more accessible. 
First it introduces the standard notation for relation composition that was inexplicably not used before. I used a non-standard unicode circle here `\ciw` but this is up for discussion as long as it looks like a composition circle.
Then I introduced balls as discussed on [this Zulip topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/notations.20for.20uniform.20spaces).  There could be used more, but at least this should be mostly sufficient for following PRs.
And of course I put a huge module docstring. As with `order/filter/basic.lean`, I think we need more mathematical explanations than in the average mathlib file.
I also added a bit of content about symmetric entourages but I don't have enough courage to split this off unless someone really insists.
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* ball_eq_of_symmetry
- \+ *lemma* ball_mono
- \+ *lemma* ball_subset_of_comp_subset
- \+/\- *lemma* comp_le_uniformity
- \+/\- *lemma* id_comp_rel
- \+ *lemma* is_open_iff_ball_subset
- \+ *lemma* mem_ball_comp
- \+ *lemma* mem_ball_symmetry
- \+ *def* symmetric_rel
- \+ *lemma* symmetric_symmetrize_rel
- \+ *lemma* symmetrize_mem_uniformity
- \+ *lemma* symmetrize_mono
- \+ *def* symmetrize_rel
- \+ *lemma* symmetrize_rel_subset_self
- \+ *theorem* uniform_continuous_iff_eventually
- \+ *def* uniform_space.ball
- \+ *lemma* uniform_space.has_basis_symmetric
- \+ *lemma* uniform_space.has_seq_basis



## [2020-06-13 09:51:05](https://github.com/leanprover-community/mathlib/commit/938b73a)
feat(topology/metric_space/pi_lp): Holder and Minkowski inequalities in ennreal ([#2988](https://github.com/leanprover-community/mathlib/pull/2988))
Hölder and Minkowski inequalities for finite sums. Versions for ennreals.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* with_top.sum_eq_top_iff

Modified src/analysis/mean_inequalities.lean
- \+ *theorem* ennreal.Lp_add_le
- \+ *theorem* ennreal.inner_le_Lp_mul_Lq

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.one_to_nnreal
- \+ *lemma* ennreal.one_to_real
- \+ *lemma* ennreal.sum_eq_top_iff



## [2020-06-13 09:19:08](https://github.com/leanprover-community/mathlib/commit/dc69dc3)
refactor(ci): only update nolints once a day ([#3036](https://github.com/leanprover-community/mathlib/pull/3036))
This PR moves the update nolints step to a new GitHub actions workflow `update_nolints.yml` which runs once a day.
#### Estimated changes
Modified .github/workflows/build.yml


Added .github/workflows/update_nolints.yml


Modified scripts/update_nolints.sh




## [2020-06-13 07:27:55](https://github.com/leanprover-community/mathlib/commit/1645542)
feat(linear_algebra): elements of a dim zero space ([#3054](https://github.com/leanprover-community/mathlib/pull/3054))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_pos_iff_exists_ne_zero
- \+ *lemma* dim_zero_iff_forall_zero

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* bot_eq_top_of_dim_eq_zero
- \+ *lemma* findim_bot
- \+ *lemma* findim_eq_zero_of_dim_eq_zero
- \+ *lemma* finite_dimensional_bot
- \+ *lemma* finite_dimensional_of_dim_eq_zero

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.mk_emptyc_iff



## [2020-06-12 18:08:42](https://github.com/leanprover-community/mathlib/commit/51ad2a1)
chore(*): update to Lean 3.16.2c ([#3053](https://github.com/leanprover-community/mathlib/pull/3053))
#### Estimated changes
Modified leanpkg.toml




## [2020-06-12 18:08:40](https://github.com/leanprover-community/mathlib/commit/ce594be)
feat(linear_algebra/affine_space): define a few affine maps ([#2981](https://github.com/leanprover-community/mathlib/pull/2981))
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_map.add_linear
- \+ *lemma* affine_map.affine_apply_line_map
- \+ *lemma* affine_map.affine_comp_line_map
- \+ *lemma* affine_map.coe_add
- \+ *lemma* affine_map.coe_const
- \+ *lemma* affine_map.coe_homothety_affine
- \+ *lemma* affine_map.coe_homothety_hom
- \+ *lemma* affine_map.coe_mul
- \+ *lemma* affine_map.coe_one
- \+ *lemma* affine_map.coe_smul
- \+ *lemma* affine_map.coe_zero
- \+ *lemma* affine_map.comp_assoc
- \+ *lemma* affine_map.comp_id
- \+ *def* affine_map.const
- \+ *lemma* affine_map.const_linear
- \+/\- *lemma* affine_map.ext
- \+ *lemma* affine_map.ext_iff
- \+ *def* affine_map.homothety
- \+ *lemma* affine_map.homothety_add
- \+ *def* affine_map.homothety_affine
- \+ *lemma* affine_map.homothety_apply
- \+ *lemma* affine_map.homothety_def
- \+ *def* affine_map.homothety_hom
- \+ *lemma* affine_map.homothety_mul
- \+ *lemma* affine_map.homothety_one
- \+ *lemma* affine_map.homothety_zero
- \+ *lemma* affine_map.id_comp
- \+ *lemma* affine_map.id_linear
- \+ *def* affine_map.line_map
- \+ *lemma* affine_map.line_map_apply
- \+ *lemma* affine_map.line_map_apply_zero
- \+ *lemma* affine_map.line_map_linear
- \+ *lemma* affine_map.line_map_vadd_neg
- \+ *lemma* affine_map.line_map_zero
- \+ *lemma* affine_map.linear_map_vsub
- \- *lemma* affine_map.map_vsub
- \+ *lemma* affine_map.vadd_apply
- \+ *lemma* affine_map.vsub_apply
- \+ *lemma* affine_map.zero_linear
- \+ *lemma* linear_map.coe_to_affine_map
- \+ *def* linear_map.to_affine_map
- \+ *lemma* linear_map.to_affine_map_linear



## [2020-06-12 16:33:01](https://github.com/leanprover-community/mathlib/commit/1429279)
feat(data/*): lemmas converting finset, set.finite, and their card ([#3042](https://github.com/leanprover-community/mathlib/pull/3042))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.attach_eq_univ

Modified src/data/set/finite.lean
- \+ *lemma* set.finite.card_to_finset



## [2020-06-12 16:32:59](https://github.com/leanprover-community/mathlib/commit/c955537)
fix(library_search): only unfold reducible definitions when matching ([#3038](https://github.com/leanprover-community/mathlib/pull/3038))
By default `library_search` only unfolds `reducible` definitions
when attempting to match lemmas against the goal.
Previously, it would unfold most definitions, sometimes giving surprising answers, or slow answers.
The old behaviour is still available via `library_search!`.
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean


Modified test/library_search/ring_theory.lean




## [2020-06-12 15:35:03](https://github.com/leanprover-community/mathlib/commit/5c0000c)
chore(*): remove extra author info ([#3051](https://github.com/leanprover-community/mathlib/pull/3051))
Removing changes to author headers in files with recent changes. Authorship should be cited in the headers only for significant contributions.
#### Estimated changes
Modified src/data/matrix/basic.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/matrix.lean




## [2020-06-12 13:27:48](https://github.com/leanprover-community/mathlib/commit/64461b8)
chore(scripts): update nolints.txt ([#3049](https://github.com/leanprover-community/mathlib/pull/3049))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-12 12:19:15](https://github.com/leanprover-community/mathlib/commit/6aa2464)
chore(scripts): update nolints.txt ([#3048](https://github.com/leanprover-community/mathlib/pull/3048))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-12 11:43:13](https://github.com/leanprover-community/mathlib/commit/f78693d)
chore(data/complex/exponential): linting and pp_nodot ([#3045](https://github.com/leanprover-community/mathlib/pull/3045))
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+/\- *def* complex.cos
- \+/\- *def* complex.cosh
- \+/\- *def* complex.exp'
- \+/\- *def* complex.exp
- \+/\- *lemma* complex.is_cau_exp
- \+/\- *def* complex.sin
- \+/\- *def* complex.sinh
- \+/\- *def* complex.tan
- \+/\- *def* complex.tanh
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* is_cau_series_of_abv_le_cau
- \+/\- *def* real.cos
- \+/\- *lemma* real.cos_bound
- \+/\- *def* real.cosh
- \+/\- *def* real.exp
- \+/\- *def* real.sin
- \+/\- *lemma* real.sin_bound
- \+/\- *def* real.sinh
- \+/\- *def* real.tan
- \+/\- *def* real.tanh



## [2020-06-12 11:43:11](https://github.com/leanprover-community/mathlib/commit/5808afc)
feat(analysis/mean_inequalities): Holder and Minkowski inequalities ([#3025](https://github.com/leanprover-community/mathlib/pull/3025))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* nnreal.Lp_add_le
- \- *theorem* nnreal.am_gm2_weighted
- \- *theorem* nnreal.am_gm3_weighted
- \- *theorem* nnreal.am_gm_weighted
- \+ *theorem* nnreal.arith_mean_le_rpow_mean
- \+ *theorem* nnreal.geom_mean_le_arith_mean2_weighted
- \+ *theorem* nnreal.geom_mean_le_arith_mean3_weighted
- \+ *theorem* nnreal.geom_mean_le_arith_mean_weighted
- \+ *theorem* nnreal.inner_le_Lp_mul_Lq
- \+ *theorem* nnreal.is_greatest_Lp
- \- *theorem* nnreal.pow_am_le_am_pow
- \+ *theorem* nnreal.pow_arith_mean_le_arith_mean_pow
- \- *theorem* nnreal.rpow_am_le_am_rpow
- \+ *theorem* nnreal.rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* real.Lp_add_le
- \+ *theorem* real.Lp_add_le_of_nonneg
- \- *theorem* real.am_gm2_weighted
- \- *theorem* real.am_gm_weighted
- \+ *theorem* real.arith_mean_le_rpow_mean
- \- *theorem* real.fpow_am_le_am_fpow
- \+ *theorem* real.fpow_arith_mean_le_arith_mean_fpow
- \+ *theorem* real.geom_mean_le_arith_mean2_weighted
- \+ *theorem* real.geom_mean_le_arith_mean_weighted
- \+ *theorem* real.inner_le_Lp_mul_Lq
- \+ *theorem* real.inner_le_Lp_mul_Lq_of_nonneg
- \- *theorem* real.pow_am_le_am_pow
- \- *theorem* real.pow_am_le_am_pow_of_even
- \+ *theorem* real.pow_arith_mean_le_arith_mean_pow
- \+ *theorem* real.pow_arith_mean_le_arith_mean_pow_of_even
- \- *theorem* real.rpow_am_le_am_rpow
- \+ *theorem* real.rpow_arith_mean_le_arith_mean_rpow



## [2020-06-12 11:10:43](https://github.com/leanprover-community/mathlib/commit/27a0946)
chore(scripts): update nolints.txt ([#3046](https://github.com/leanprover-community/mathlib/pull/3046))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-12 10:19:27](https://github.com/leanprover-community/mathlib/commit/30e620c)
chore(data/real/cau_seq): linting ([#3040](https://github.com/leanprover-community/mathlib/pull/3040))
#### Estimated changes
Modified src/data/real/cau_seq.lean
- \+/\- *theorem* cau_seq.cauchy₂
- \+/\- *theorem* cau_seq.cauchy₃
- \+/\- *theorem* cau_seq.equiv_def₃
- \+/\- *def* cau_seq.inv
- \+/\- *def* cau_seq.lim_zero
- \+/\- *theorem* is_cau_seq.cauchy₂
- \+/\- *theorem* is_cau_seq.cauchy₃



## [2020-06-12 09:31:29](https://github.com/leanprover-community/mathlib/commit/0f6b3ca)
doc(data/complex/basic): docstrings and pp_nodots ([#3044](https://github.com/leanprover-community/mathlib/pull/3044))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+/\- *def* complex.norm_sq



## [2020-06-12 05:32:43](https://github.com/leanprover-community/mathlib/commit/96676a7)
chore(scripts): update nolints.txt ([#3039](https://github.com/leanprover-community/mathlib/pull/3039))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-12 03:49:42](https://github.com/leanprover-community/mathlib/commit/4ec7cc5)
refactor(*): fix field names in `linear_map` and `submodule` ([#3032](https://github.com/leanprover-community/mathlib/pull/3032))
* `linear_map` now uses `map_add'` and `map_smul`';
* `submodule` now `extends add_submonoid` and adds `smul_mem'`;
* no more `submodule.is_add_subgroup` instance;
* `open_subgroup` now uses bundled subgroups;
* `is_linear_map` is not a `class` anymore: we had a couple of
  `instances` but zero lemmas taking it as a typeclass argument;
* `subgroup.mem_coe` now takes `{g : G}` as it should, not `[g : G]`.
#### Estimated changes
Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/lie_algebra.lean
- \+/\- *def* lie_algebra.Ad

Modified src/algebra/module.lean
- \- *lemma* is_linear_map.map_add
- \- *lemma* is_linear_map.map_smul
- \+/\- *def* is_linear_map.mk'
- \+ *structure* is_linear_map
- \+/\- *theorem* linear_map.is_linear
- \+/\- *lemma* linear_map.map_add
- \+/\- *lemma* linear_map.map_smul
- \+/\- *lemma* submodule.add_mem
- \+ *theorem* submodule.coe_set_eq
- \+ *theorem* submodule.coe_sort_coe
- \+ *lemma* submodule.coe_to_add_subgroup
- \+/\- *theorem* submodule.ext'
- \+ *theorem* submodule.ext'_iff
- \+/\- *theorem* submodule.ext
- \+/\- *lemma* submodule.neg_mem_iff
- \+/\- *lemma* submodule.smul_mem
- \+/\- *lemma* submodule.sum_mem
- \+ *def* submodule.to_add_subgroup
- \+ *theorem* submodule.to_add_submonoid_eq
- \+ *theorem* submodule.to_add_submonoid_injective
- \+/\- *lemma* submodule.zero_mem

Modified src/analysis/analytic/composition.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/data/monoid_algebra.lean


Modified src/data/polynomial.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* subgroup.mem_coe

Modified src/linear_algebra/affine_space.lean


Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_equiv.map_add
- \+/\- *theorem* linear_equiv.map_smul
- \+/\- *def* linear_equiv.to_add_equiv

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/lagrange.lean


Modified src/linear_algebra/linear_action.lean


Modified src/linear_algebra/linear_pmap.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/ring_theory/algebra.lean
- \+/\- *lemma* span_int_eq

Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/open_subgroup.lean
- \+/\- *lemma* ideal.is_open_of_open_subideal
- \+ *structure* open_add_subgroup
- \- *lemma* open_subgroup.coe_injective
- \+ *lemma* open_subgroup.coe_subgroup_le
- \+ *lemma* open_subgroup.coe_subset
- \+/\- *lemma* open_subgroup.ext'
- \+/\- *lemma* open_subgroup.ext
- \+ *lemma* open_subgroup.ext_iff
- \- *lemma* open_subgroup.is_open_of_nonempty_open_subset
- \- *lemma* open_subgroup.is_open_of_open_subgroup
- \- *lemma* open_subgroup.le_iff
- \+ *lemma* open_subgroup.mem_coe
- \+ *lemma* open_subgroup.mem_coe_opens
- \+ *lemma* open_subgroup.mem_coe_subgroup
- \+ *structure* open_subgroup
- \- *def* open_subgroup
- \+ *lemma* subgroup.is_open_mono
- \+ *lemma* subgroup.is_open_of_mem_nhds
- \+ *lemma* subgroup.is_open_of_open_subgroup
- \+ *lemma* submodule.is_open_mono
- \- *lemma* submodule.is_open_of_open_submodule

Modified src/topology/algebra/ring.lean




## [2020-06-12 02:45:20](https://github.com/leanprover-community/mathlib/commit/338bbd2)
chore(measure/theory): remove useless module instances ([#3031](https://github.com/leanprover-community/mathlib/pull/3031))
Remove useless `module` and `vector_space` instances, as these words are now synonyms of `semimodule`.
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/ring_theory/power_series.lean




## [2020-06-11 22:32:06](https://github.com/leanprover-community/mathlib/commit/593f731)
chore(scripts): update nolints.txt ([#3035](https://github.com/leanprover-community/mathlib/pull/3035))
I am happy to remove some nolints for you!
#### Estimated changes



## [2020-06-11 21:56:33](https://github.com/leanprover-community/mathlib/commit/5444945)
chore(scripts): update nolints.txt ([#3034](https://github.com/leanprover-community/mathlib/pull/3034))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-11 21:56:31](https://github.com/leanprover-community/mathlib/commit/f71e359)
chore(ring_theory/power_series): avoid id in instances ([#3033](https://github.com/leanprover-community/mathlib/pull/3033))
The power series instances contain a spurious `id`, that we remove.
#### Estimated changes
Modified src/ring_theory/power_series.lean




## [2020-06-11 20:24:50](https://github.com/leanprover-community/mathlib/commit/9a7151c)
feat(data/finsupp): set.finite {m | m ≤ n} ([#3029](https://github.com/leanprover-community/mathlib/pull/3029))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.finite_le_nat
- \+ *lemma* finsupp.finite_lt_nat



## [2020-06-11 20:24:48](https://github.com/leanprover-community/mathlib/commit/666b9e5)
refactor(analysis/mean_inequalities): review ([#3023](https://github.com/leanprover-community/mathlib/pull/3023))
Also add several lemmas to other files
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \+ *lemma* div_mul_cancel_of_imp
- \+ *lemma* mul_div_cancel_left_of_imp
- \+ *lemma* mul_div_cancel_of_imp'
- \+ *lemma* mul_div_cancel_of_imp

Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_on_const
- \+ *lemma* convex_on_id

Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/mean_inequalities.lean
- \+/\- *theorem* nnreal.am_gm2_weighted
- \+/\- *theorem* nnreal.am_gm3_weighted
- \+/\- *theorem* nnreal.am_gm_weighted
- \+/\- *theorem* nnreal.pow_am_le_am_pow
- \+ *theorem* nnreal.rpow_am_le_am_rpow
- \+/\- *theorem* nnreal.young_inequality
- \+/\- *theorem* real.am_gm2_weighted
- \+/\- *theorem* real.am_gm_weighted
- \+/\- *theorem* real.fpow_am_le_am_fpow
- \+/\- *theorem* real.pow_am_le_am_pow
- \+/\- *theorem* real.pow_am_le_am_pow_of_even
- \+ *theorem* real.rpow_am_le_am_rpow
- \+/\- *theorem* real.young_inequality
- \+ *theorem* real.young_inequality_of_nonneg

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* nnreal.rpow_add
- \+ *lemma* nnreal.rpow_le_rpow_iff
- \+ *lemma* nnreal.rpow_lt_rpow_iff
- \+ *lemma* nnreal.rpow_sub'
- \+ *lemma* nnreal.rpow_sub
- \+ *lemma* real.rpow_le_rpow_iff
- \+ *lemma* real.rpow_lt_rpow_iff
- \+ *lemma* real.rpow_sub'
- \+ *lemma* real.rpow_sub

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* real.is_conjugate_exponent.conjugate_eq
- \+ *lemma* real.is_conjugate_exponent.mul_eq_add
- \+ *lemma* real.is_conjugate_exponent.nonneg
- \+ *lemma* real.is_conjugate_exponent.one_div_nonneg
- \+ *lemma* real.is_conjugate_exponent.sub_one_mul_conj
- \+ *lemma* real.is_conjugate_exponent.sub_one_pos

Modified src/data/real/nnreal.lean
- \- *lemma* nnreal.div_mul_cancel
- \+ *lemma* nnreal.div_self_le



## [2020-06-11 18:53:58](https://github.com/leanprover-community/mathlib/commit/257d1b7)
feat(*): preparations for Caratheodory's convexity theorem ([#3030](https://github.com/leanprover-community/mathlib/pull/3030))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.exists_pos_of_sum_zero_of_exists_nonzero

Modified src/algebra/ordered_field.lean


Modified src/data/equiv/basic.lean
- \+ *theorem* equiv.set.apply_range_symm
- \+ *lemma* equiv.set.sum_diff_subset_apply_inl
- \+ *lemma* equiv.set.sum_diff_subset_apply_inr
- \+ *lemma* equiv.set.sum_diff_subset_symm_apply_of_mem
- \+ *lemma* equiv.set.sum_diff_subset_symm_apply_of_not_mem

Modified src/data/finset.lean
- \+ *lemma* finset.coe_mem
- \+ *lemma* finset.filter_ne'
- \+ *lemma* finset.filter_ne
- \+ *lemma* finset.mk_coe

Modified src/data/set/basic.lean
- \+ *lemma* set.coe_inclusion

Modified src/data/set/finite.lean
- \+ *lemma* finset.finite_to_set_to_finset

Modified src/data/set/lattice.lean
- \+ *theorem* set.subset_subset_Union

Modified src/linear_algebra/basis.lean
- \+ *lemma* exists_sum_is_basis
- \+ *theorem* linear_dependent_iff

Modified src/linear_algebra/dimension.lean
- \+ *lemma* cardinal_le_dim_of_linear_independent'
- \+ *lemma* cardinal_le_dim_of_linear_independent

Modified src/logic/embedding.lean
- \+ *def* function.embedding.inl
- \+ *def* function.embedding.inr



## [2020-06-11 18:53:56](https://github.com/leanprover-community/mathlib/commit/447a2d6)
chore(data/matrix/basic): move numeral section into diagonal ([#3022](https://github.com/leanprover-community/mathlib/pull/3022))
Since the numeral section defines numerals for matrices as scalar
multiples of `one_val`, which is the identity matrix, these are defined
solely for diagonal matrices of type `matrix n n r`. So the numeral
section should be in the diagonal section.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.bit0_val
- \+/\- *theorem* matrix.diagonal_add



## [2020-06-11 18:19:12](https://github.com/leanprover-community/mathlib/commit/1df9301)
feat(group_theory/semidirect_product): introduce semidirect_products of groups ([#3028](https://github.com/leanprover-community/mathlib/pull/3028))
#### Estimated changes
Added src/group_theory/semidirect_product.lean
- \+ *def* semidirect_product.inl
- \+ *lemma* semidirect_product.inl_aut
- \+ *lemma* semidirect_product.inl_inj
- \+ *lemma* semidirect_product.inl_injective
- \+ *lemma* semidirect_product.inl_left_mul_inr_right
- \+ *def* semidirect_product.inr
- \+ *lemma* semidirect_product.inr_inj
- \+ *lemma* semidirect_product.inr_injective
- \+ *lemma* semidirect_product.inv_left
- \+ *lemma* semidirect_product.inv_right
- \+ *lemma* semidirect_product.left_inl
- \+ *lemma* semidirect_product.left_inr
- \+ *def* semidirect_product.lift
- \+ *lemma* semidirect_product.lift_comp_inl
- \+ *lemma* semidirect_product.lift_comp_inr
- \+ *lemma* semidirect_product.lift_inl
- \+ *lemma* semidirect_product.lift_inr
- \+ *lemma* semidirect_product.lift_unique
- \+ *lemma* semidirect_product.mul_left
- \+ *lemma* semidirect_product.mul_right
- \+ *lemma* semidirect_product.one_left
- \+ *lemma* semidirect_product.one_right
- \+ *lemma* semidirect_product.range_inl_eq_ker_right_hom
- \+ *def* semidirect_product.right_hom
- \+ *lemma* semidirect_product.right_hom_comp_inl
- \+ *lemma* semidirect_product.right_hom_comp_inr
- \+ *lemma* semidirect_product.right_hom_eq_right
- \+ *lemma* semidirect_product.right_hom_inl
- \+ *lemma* semidirect_product.right_hom_inr
- \+ *lemma* semidirect_product.right_hom_surjective
- \+ *lemma* semidirect_product.right_inl
- \+ *lemma* semidirect_product.right_inr
- \+ *structure* semidirect_product



## [2020-06-11 15:35:28](https://github.com/leanprover-community/mathlib/commit/ce48b6b)
chore(data/finsupp): drop `finsupp.module` and `vector_space` ([#3009](https://github.com/leanprover-community/mathlib/pull/3009))
These instances are not needed as `module` and `vector_space` are abbreviations for `semimodule`.
Also add two bundled versions of `eval`: as `add_monoid_hom` and as `linear_map`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.coe_leval'
- \+ *lemma* finsupp.coe_leval
- \+ *def* finsupp.eval_add_hom
- \+ *lemma* finsupp.eval_add_hom_apply
- \+ *def* finsupp.leval'
- \+ *def* finsupp.leval

Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/field_theory/mv_polynomial.lean


Modified test/library_search/ring_theory.lean




## [2020-06-11 11:41:18](https://github.com/leanprover-community/mathlib/commit/cf0c6b8)
chore(*): use prod and sum notation ([#3027](https://github.com/leanprover-community/mathlib/pull/3027))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.prod_Ico_id_eq_fact
- \+/\- *lemma* finset.prod_mul_distrib

Modified src/algebra/pi_instances.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean
- \+/\- *theorem* continuous_multilinear_map.bound
- \+/\- *theorem* continuous_multilinear_map.le_op_norm
- \+/\- *lemma* continuous_multilinear_map.norm_def
- \+/\- *def* continuous_multilinear_map.op_norm
- \+/\- *lemma* continuous_multilinear_map.op_norm_le_bound
- \+/\- *lemma* continuous_multilinear_map.ratio_le_op_norm
- \+/\- *theorem* multilinear_map.continuous_of_bound
- \+/\- *def* multilinear_map.mk_continuous

Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.exp_sum
- \+/\- *lemma* real.exp_sum

Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.prod_univ_zero

Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean
- \+/\- *lemma* mv_polynomial.as_sum
- \+/\- *lemma* mv_polynomial.support_sum_monomial_coeff

Modified src/data/real/nnreal.lean


Modified src/data/set/finite.lean


Modified src/deprecated/submonoid.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* matrix.det_diagonal

Modified src/linear_algebra/multilinear.lean


Modified src/measure_theory/borel_space.lean


Modified src/ring_theory/subsemiring.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/multilinear.lean




## [2020-06-11 09:43:11](https://github.com/leanprover-community/mathlib/commit/5129aed)
chore(algebra/group/to_additive): improve warning message ([#3024](https://github.com/leanprover-community/mathlib/pull/3024))
Also prevent `group_theory/subgroup` from generating this warning.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/group_theory/subgroup.lean




## [2020-06-11 08:03:33](https://github.com/leanprover-community/mathlib/commit/ade196f)
chore(scripts): update nolints.txt ([#3026](https://github.com/leanprover-community/mathlib/pull/3026))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-11 06:36:39](https://github.com/leanprover-community/mathlib/commit/8863666)
feat(ring_theory/ideals): prod_dvd_of_coprime ([#2815](https://github.com/leanprover-community/mathlib/pull/2815))
#### Estimated changes
Modified src/data/polynomial.lean
- \+ *theorem* polynomial.pairwise_coprime_X_sub

Added src/ring_theory/coprime.lean
- \+ *theorem* finset.prod_dvd_of_coprime
- \+ *theorem* fintype.prod_dvd_of_coprime
- \+ *theorem* is_coprime.dvd_of_dvd_mul_left
- \+ *theorem* is_coprime.dvd_of_dvd_mul_right
- \+ *theorem* is_coprime.is_unit_of_dvd
- \+ *theorem* is_coprime.map
- \+ *theorem* is_coprime.mul_dvd
- \+ *theorem* is_coprime.mul_left
- \+ *theorem* is_coprime.mul_left_iff
- \+ *theorem* is_coprime.mul_right
- \+ *theorem* is_coprime.mul_right_iff
- \+ *theorem* is_coprime.of_mul_left_left
- \+ *theorem* is_coprime.of_mul_left_right
- \+ *theorem* is_coprime.of_mul_right_left
- \+ *theorem* is_coprime.of_mul_right_right
- \+ *theorem* is_coprime.of_prod_left
- \+ *theorem* is_coprime.of_prod_right
- \+ *theorem* is_coprime.pow
- \+ *theorem* is_coprime.pow_left
- \+ *theorem* is_coprime.pow_right
- \+ *theorem* is_coprime.prod_left
- \+ *theorem* is_coprime.prod_left_iff
- \+ *theorem* is_coprime.prod_right
- \+ *theorem* is_coprime.prod_right_iff
- \+ *theorem* is_coprime.symm
- \+ *def* is_coprime
- \+ *theorem* is_coprime_comm
- \+ *theorem* is_coprime_one_left
- \+ *theorem* is_coprime_one_right
- \+ *theorem* is_coprime_self
- \+ *theorem* is_coprime_zero_left
- \+ *theorem* is_coprime_zero_right
- \+ *theorem* nat.is_coprime_iff_coprime

Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/ideals.lean
- \- *def* ideal.is_coprime
- \- *theorem* ideal.is_coprime_def
- \- *theorem* ideal.is_coprime_self



## [2020-06-10 19:03:46](https://github.com/leanprover-community/mathlib/commit/2779093)
feat(linear_algebra/matrix): matrix has finite dim  ([#3013](https://github.com/leanprover-community/mathlib/pull/3013))
Using the fact that currying is a linear operation, we give matrix
a finite dimensional instance. This allows one to invoke `findim`
on matrices, giving the expected dimensions for a finite-dim matrix.
The import is changed to linear_algebra.finite_dimension,
which brings in the previous linear_algebra.dimension import.
#### Estimated changes
Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.findim_matrix



## [2020-06-10 15:54:19](https://github.com/leanprover-community/mathlib/commit/067a96b)
chore(*): update to lean 3.16.1c ([#3020](https://github.com/leanprover-community/mathlib/pull/3020))
#### Estimated changes
Modified leanpkg.toml




## [2020-06-10 15:54:17](https://github.com/leanprover-community/mathlib/commit/76e7d29)
chore(scripts): update nolints.txt ([#3019](https://github.com/leanprover-community/mathlib/pull/3019))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-10 15:54:15](https://github.com/leanprover-community/mathlib/commit/f7654b3)
feat(tactic/generalizes): tactic for generalizing over multiple expressions ([#2982](https://github.com/leanprover-community/mathlib/pull/2982))
This commit adds a tactic `generalizes` which works like `generalize` but for multiple expressions at once. The tactic is more powerful than calling `generalize` multiple times since this usually fails when there are dependencies between the expressions. By contrast, `generalizes` handles at least some such situations.
#### Estimated changes
Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Added src/tactic/generalizes.lean


Added test/generalizes.lean
- \+ *inductive* Vec.eq
- \+ *lemma* Vec.eq_cons_inversion
- \+ *inductive* Vec.fancy_unit
- \+ *lemma* Vec.test₁
- \+ *lemma* Vec.test₂
- \+ *inductive* Vec
- \+ *lemma* example_from_docs₁
- \+ *lemma* example_from_docs₂



## [2020-06-10 14:24:39](https://github.com/leanprover-community/mathlib/commit/daed8a4)
style(*): use rcases patterns with ext ([#3018](https://github.com/leanprover-community/mathlib/pull/3018))
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/convex/basic.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/data/equiv/basic.lean


Modified src/data/finset.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/countable.lean


Modified src/ring_theory/noetherian.lean


Modified src/tactic/ext.lean


Modified src/topology/constructions.lean




## [2020-06-10 14:24:37](https://github.com/leanprover-community/mathlib/commit/026d639)
ci(build.yml): add -T100000 to test step ([#3017](https://github.com/leanprover-community/mathlib/pull/3017))
cf. [#2276](https://github.com/leanprover-community/mathlib/pull/2276).  This will also prevent some confusing timeouts, see e.g. https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Tests.20fail
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-06-10 12:50:03](https://github.com/leanprover-community/mathlib/commit/614d1ca)
chore(*): update to lean 3.16.0 ([#3016](https://github.com/leanprover-community/mathlib/pull/3016))
The only change relevant to mathlib is that the precedence of unary `-` has changed, so that `-a^n` parses as `-(a^n)` and not (as formerly) `(-a)^n`.
#### Estimated changes
Modified leanpkg.toml


Modified src/algebra/group_power.lean
- \+/\- *lemma* neg_one_pow_eq_pow_mod_two

Modified src/group_theory/perm/sign.lean




## [2020-06-10 12:50:01](https://github.com/leanprover-community/mathlib/commit/4b62261)
chore(algebra/field): deduplicate with group_with_zero ([#3015](https://github.com/leanprover-community/mathlib/pull/3015))
For historical reasons there are lots of lemmas we prove for `group_with_zero`, then again for a `division_ring`. Merge some of them.
#### Estimated changes
Modified src/algebra/continued_fractions/convergents_equiv.lean


Modified src/algebra/field.lean
- \- *lemma* div_div_div_div_eq
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_eq_mul_one_div
- \- *lemma* div_helper
- \- *lemma* div_mul_cancel
- \- *lemma* div_mul_div
- \- *lemma* div_mul_eq_div_mul_one_div
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm
- \- *lemma* div_mul_left
- \- *lemma* div_mul_right
- \- *lemma* div_one
- \- *lemma* div_self
- \- *lemma* division_def
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* eq_zero_of_one_div_eq_zero
- \- *lemma* inv_mul_cancel
- \- *lemma* inv_ne_zero
- \- *theorem* inv_one
- \- *lemma* mul_div_assoc
- \- *lemma* mul_div_cancel'
- \- *lemma* mul_div_cancel
- \- *lemma* mul_div_cancel_left
- \- *lemma* mul_div_mul_left
- \- *lemma* mul_div_mul_right
- \- *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* mul_inv_cancel
- \- *lemma* mul_one_div_cancel
- \- *lemma* ne_zero_of_one_div_ne_zero
- \- *lemma* one_div_mul_cancel
- \- *lemma* one_div_mul_one_div
- \- *lemma* one_div_ne_zero
- \- *lemma* one_div_one
- \- *lemma* one_inv_eq
- \- *lemma* zero_div

Modified src/algebra/group_with_zero.lean
- \- *lemma* div_div_div_div_eq'
- \+ *lemma* div_div_div_div_eq
- \- *lemma* div_div_eq_div_mul'
- \+ *lemma* div_div_eq_div_mul
- \- *lemma* div_div_eq_mul_div'
- \+ *lemma* div_div_eq_mul_div
- \- *lemma* div_eq_mul_one_div'
- \+ *lemma* div_eq_mul_one_div
- \- *lemma* div_helper'
- \+ *lemma* div_helper
- \- *lemma* div_mul_cancel'
- \+ *lemma* div_mul_cancel
- \- *lemma* div_mul_div'
- \+ *lemma* div_mul_div
- \- *lemma* div_mul_eq_div_mul_one_div'
- \+ *lemma* div_mul_eq_div_mul_one_div
- \- *lemma* div_mul_eq_mul_div'
- \+ *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm'
- \+ *lemma* div_mul_eq_mul_div_comm
- \- *lemma* div_mul_left'
- \+ *lemma* div_mul_left
- \- *lemma* div_mul_right'
- \+ *lemma* div_mul_right
- \- *lemma* div_one'
- \+ *lemma* div_one
- \- *lemma* div_self'
- \+ *lemma* div_self
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* eq_zero_of_one_div_eq_zero'
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \- *lemma* inv_mul_cancel'
- \+ *lemma* inv_mul_cancel
- \- *lemma* inv_ne_zero'
- \+ *lemma* inv_ne_zero
- \- *lemma* inv_one'
- \+ *lemma* inv_one
- \- *lemma* mul_div_assoc''
- \+ *lemma* mul_div_assoc
- \- *lemma* mul_div_cancel'''
- \- *lemma* mul_div_cancel''
- \+ *lemma* mul_div_cancel'
- \+ *lemma* mul_div_cancel
- \- *lemma* mul_div_cancel_left'
- \+ *lemma* mul_div_cancel_left
- \- *lemma* mul_div_mul_left'
- \+ *lemma* mul_div_mul_left
- \- *lemma* mul_div_mul_right'
- \+ *lemma* mul_div_mul_right
- \- *lemma* mul_eq_mul_of_div_eq_div'
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* mul_inv_cancel'
- \+ *lemma* mul_inv_cancel
- \- *lemma* mul_one_div_cancel'
- \+ *lemma* mul_one_div_cancel
- \- *lemma* ne_zero_of_one_div_ne_zero'
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \- *lemma* one_div_mul_cancel'
- \+ *lemma* one_div_mul_cancel
- \- *lemma* one_div_mul_one_div'
- \+ *lemma* one_div_mul_one_div
- \- *lemma* one_div_ne_zero'
- \+ *lemma* one_div_ne_zero
- \- *lemma* one_div_one'
- \+ *lemma* one_div_one
- \+ *lemma* one_inv_eq
- \- *lemma* zero_div'
- \+ *lemma* zero_div

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/invertible.lean


Modified src/data/real/nnreal.lean


Modified src/geometry/euclidean.lean




## [2020-06-10 12:49:59](https://github.com/leanprover-community/mathlib/commit/b427ebf)
chore(data/equiv/basic): add many docstrings, review ([#3008](https://github.com/leanprover-community/mathlib/pull/3008))
Non-docstring changes:
* drop `decidable_eq_of_equiv` (was a copy of `equiv.decidable_eq`);
* rename `inhabited_of_equiv` to `equiv.inhabited`;
* rename `unique_of_equiv` to `equiv.unique`, take `unique β` as an
  instance argument;
* better defeq for `equiv.list_equiv_of_equiv`;
* use `coe` instead of `subtype.val` in `equiv.set.union'`;
* use `s ∩ t ⊆ ∅` instead of `s ∩ t = ∅` in `equiv.set.union`;
  this way it agrees with `disjoint`;
* use `[decidable_pred (λ x, x ∈ s)]` instead of `[decidable_pred s]`
  in `equiv.set.union`;
* use `coe` instead of `subtype.val` in `equiv.set.sep`;
* make `f` an explicit argument in `equiv.of_bijective f hf`;
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.Pi_congr_right
- \+ *theorem* equiv.coe_of_bijective
- \- *def* equiv.decidable_eq_of_equiv
- \- *def* equiv.equiv_pempty
- \- *def* equiv.inhabited_of_equiv
- \+/\- *def* equiv.list_equiv_of_equiv
- \- *theorem* equiv.of_bijective_to_fun
- \+/\- *def* equiv.psigma_equiv_sigma
- \+/\- *lemma* equiv.set.union_apply_left
- \+/\- *lemma* equiv.set.union_apply_right
- \+/\- *def* equiv.sigma_congr_right
- \+/\- *def* equiv.subtype_congr_right
- \+ *def* equiv.subtype_equiv_of_subtype
- \- *def* equiv.unique_of_equiv
- \+ *def* equiv.{u'

Modified src/data/fin_enum.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/finite.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid/basic.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/quotient_group.lean


Modified src/linear_algebra/determinant.lean


Modified src/logic/embedding.lean


Modified src/order/order_iso.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/set_theory/cardinal.lean
- \+/\- *lemma* cardinal.mk_subtype_of_equiv
- \+/\- *theorem* cardinal.mk_union_add_mk_inter
- \+/\- *theorem* cardinal.mk_union_of_disjoint

Modified src/set_theory/schroeder_bernstein.lean




## [2020-06-10 12:49:57](https://github.com/leanprover-community/mathlib/commit/671284e)
feat(control/equiv_functor/instances): allow equiv_rw on finset ([#2997](https://github.com/leanprover-community/mathlib/pull/2997))
Allows moving `finset` over an `equiv` using `equiv_rw`, as requested by @jcommelin.
e.g.
```
import data.finset
import tactic.equiv_rw
example (σ τ : Type) (e : σ ≃ τ) : finset σ ≃ finset τ :=
by { equiv_rw e, refl, }
```
#### Estimated changes
Modified src/control/equiv_functor/instances.lean


Modified src/data/finset.lean
- \+/\- *theorem* finset.map_refl

Modified src/logic/embedding.lean
- \+ *lemma* equiv.refl_to_embedding
- \+ *lemma* equiv.trans_to_embedding

Modified src/tactic/equiv_rw.lean




## [2020-06-10 11:19:50](https://github.com/leanprover-community/mathlib/commit/b932a51)
feat(data/set/function): add lemmas about `semiconj` ([#3007](https://github.com/leanprover-community/mathlib/pull/3007))
Also redefine `set.maps_to` to avoid unfolding `mem_preimage`.
#### Estimated changes
Modified src/analysis/calculus/inverse.lean


Modified src/data/set/function.lean
- \+ *lemma* function.semiconj.bij_on_image
- \+ *lemma* function.semiconj.bij_on_range
- \+ *lemma* function.semiconj.inj_on_image
- \+ *lemma* function.semiconj.inj_on_preimage
- \+ *lemma* function.semiconj.inj_on_range
- \+ *lemma* function.semiconj.maps_to_image
- \+ *lemma* function.semiconj.maps_to_preimage
- \+ *lemma* function.semiconj.maps_to_range
- \+ *lemma* function.semiconj.surj_on_image
- \+ *lemma* function.semiconj.surj_on_range
- \+/\- *theorem* set.inv_on.bij_on
- \+/\- *def* set.maps_to

Modified src/linear_algebra/basis.lean




## [2020-06-10 09:47:17](https://github.com/leanprover-community/mathlib/commit/836c0a2)
chore(*): use sum notation ([#3014](https://github.com/leanprover-community/mathlib/pull/3014))
The biggest field test of the new summation notation.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *theorem* finset.exists_le_of_sum_le

Modified src/algebra/direct_sum.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/ring.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.sum_mem
- \+/\- *lemma* finset.center_mass_eq_of_sum_1
- \+/\- *lemma* finset.center_mass_insert

Modified src/analysis/mean_inequalities.lean
- \+/\- *theorem* nnreal.am_gm_weighted
- \+/\- *theorem* nnreal.pow_am_le_am_pow

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* nnnorm_sum_le
- \+/\- *lemma* norm_sum_le

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/composition.lean
- \+/\- *lemma* composition.sum_blocks_fun

Modified src/data/complex/exponential.lean
- \+/\- *def* complex.exp'
- \+/\- *lemma* complex.exp_sum
- \+/\- *lemma* complex.is_cau_exp
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* real.exp_sum

Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/card.lean


Modified src/data/holor.lean


Modified src/data/indicator_function.lean


Modified src/data/matrix/basic.lean


Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean
- \+/\- *lemma* nat.sum_totient

Modified src/data/polynomial.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/support.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.trace_diag

Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* multilinear_map.map_sum_finset_aux

Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* pmf.of_fintype

Modified src/measure_theory/set_integral.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/subsemiring.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* has_sum
- \+/\- *lemma* has_sum_fintype
- \+/\- *lemma* has_sum_sum_of_ne_finset_zero
- \+/\- *lemma* tsum_fintype

Modified src/topology/algebra/module.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean




## [2020-06-10 08:49:53](https://github.com/leanprover-community/mathlib/commit/d9934b2)
feat(linear_algebra/basic): curry is linear_equiv ([#3012](https://github.com/leanprover-community/mathlib/pull/3012))
Currying provides a linear_equiv. This can be used to show that
matrix lookup is a linear operation. This should allow to easily
provide a finite_dimensional instance for matrices.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_uncurry
- \+ *lemma* linear_equiv.coe_uncurry_symm



## [2020-06-10 07:15:39](https://github.com/leanprover-community/mathlib/commit/6a0412e)
chore(data/fintype): generalise `to_finset_card` ([#2316](https://github.com/leanprover-community/mathlib/pull/2316))
Slight generalisation of a lemma, allowing a more flexible `fintype` instance.
Also americanises some spelling. :-)
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified archive/sensitivity.lean


Modified src/data/equiv/basic.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* set.to_finset_card

Modified src/data/set/finite.lean
- \- *lemma* set.to_finset_card
- \+/\- *lemma* set.to_finset_inter



## [2020-06-10 00:06:07](https://github.com/leanprover-community/mathlib/commit/f1df14c)
feat(group_theory/subgroup): normal_closure and gpowers ([#2959](https://github.com/leanprover-community/mathlib/pull/2959))
Transfer some more proofs from `deprecated/subgroup`
#### Estimated changes
Modified src/deprecated/subgroup.lean
- \- *lemma* group.conj_mem_conjugates_of_set
- \- *def* group.conjugates
- \- *def* group.conjugates_of_set
- \- *theorem* group.conjugates_of_set_mono
- \+ *theorem* group.conjugates_of_set_subset'
- \- *theorem* group.conjugates_of_set_subset
- \- *lemma* group.mem_conjugates_of_set_iff
- \- *lemma* group.mem_conjugates_self
- \- *theorem* group.subset_conjugates_of_set
- \- *lemma* injective_mul

Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.coe_gsmul
- \+ *lemma* add_subgroup.coe_smul
- \+ *def* add_subgroup.gmultiples
- \+ *lemma* add_subgroup.gmultiples_eq_closure
- \+ *lemma* add_subgroup.mem_gmultiples
- \+ *structure* add_subgroup.normal
- \+ *lemma* group.conj_mem_conjugates_of_set
- \+ *def* group.conjugates
- \+ *def* group.conjugates_of_set
- \+ *theorem* group.conjugates_of_set_mono
- \+ *theorem* group.conjugates_of_set_subset
- \+ *lemma* group.conjugates_subset_normal
- \+ *lemma* group.mem_conjugates_of_set_iff
- \+ *lemma* group.mem_conjugates_self
- \+ *theorem* group.subset_conjugates_of_set
- \+/\- *lemma* monoid_hom.normal_ker
- \+/\- *def* monoid_hom.range
- \+ *lemma* monoid_hom.range_eq_map
- \+/\- *lemma* subgroup.bot_normal
- \+ *lemma* subgroup.coe_gpow
- \+/\- *lemma* subgroup.coe_inv
- \+/\- *lemma* subgroup.coe_mk
- \+/\- *lemma* subgroup.coe_mul
- \+/\- *lemma* subgroup.coe_one
- \+ *lemma* subgroup.coe_pow
- \+ *theorem* subgroup.conjugates_of_set_subset_normal_closure
- \+ *def* subgroup.gpowers
- \+ *lemma* subgroup.gpowers_eq_closure
- \+/\- *lemma* subgroup.le_normalizer_of_normal
- \+ *lemma* subgroup.mem_gpowers
- \+ *lemma* subgroup.normal.comap
- \- *lemma* subgroup.normal.conj_mem
- \+ *structure* subgroup.normal
- \+ *def* subgroup.normal_closure
- \+ *theorem* subgroup.normal_closure_eq_infi
- \+ *theorem* subgroup.normal_closure_le_normal
- \+ *theorem* subgroup.normal_closure_mono
- \+ *lemma* subgroup.normal_closure_normal
- \+ *lemma* subgroup.normal_closure_subset_iff
- \+ *lemma* subgroup.normal_comap
- \+ *def* subgroup.of_div
- \+ *theorem* subgroup.subset_normal_closure



## [2020-06-09 21:53:37](https://github.com/leanprover-community/mathlib/commit/4e1558b)
chore(algebra/group_power): simp attribute on nsmul_eq_mul and gsmul_eq_mul ([#2983](https://github.com/leanprover-community/mathlib/pull/2983))
Also fix the resulting lint failures, corresponding to the fact that several lemmas are not in simp normal form any more.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* commute.cast_int_mul_cast_int_mul
- \+ *lemma* commute.cast_int_mul_left
- \+ *lemma* commute.cast_int_mul_right
- \+ *theorem* commute.cast_int_mul_self
- \+ *theorem* commute.cast_nat_mul_cast_nat_mul
- \+ *theorem* commute.cast_nat_mul_left
- \+ *theorem* commute.cast_nat_mul_right
- \+ *theorem* commute.cast_nat_mul_self
- \- *lemma* commute.gsmul_gsmul
- \- *lemma* commute.gsmul_left
- \- *lemma* commute.gsmul_right
- \- *theorem* commute.gsmul_self
- \- *theorem* commute.nsmul_left
- \- *theorem* commute.nsmul_nsmul
- \- *theorem* commute.nsmul_right
- \- *theorem* commute.nsmul_self
- \+ *theorem* commute.self_cast_int_mul
- \+ *theorem* commute.self_cast_int_mul_cast_int_mul
- \+ *theorem* commute.self_cast_nat_mul
- \+ *theorem* commute.self_cast_nat_mul_cast_nat_mul
- \- *theorem* commute.self_gsmul
- \- *theorem* commute.self_gsmul_gsmul
- \- *theorem* commute.self_nsmul
- \- *theorem* commute.self_nsmul_nsmul
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* nat.nsmul_eq_mul
- \+/\- *theorem* nsmul_eq_mul
- \+ *lemma* semiconj_by.cast_int_mul_cast_int_mul
- \+ *lemma* semiconj_by.cast_int_mul_left
- \+ *lemma* semiconj_by.cast_int_mul_right
- \+ *lemma* semiconj_by.cast_nat_mul_cast_nat_mul
- \+ *lemma* semiconj_by.cast_nat_mul_left
- \+ *lemma* semiconj_by.cast_nat_mul_right
- \- *lemma* semiconj_by.gsmul_gsmul
- \- *lemma* semiconj_by.gsmul_left
- \- *lemma* semiconj_by.gsmul_right
- \- *lemma* semiconj_by.nsmul_left
- \- *lemma* semiconj_by.nsmul_nsmul
- \- *lemma* semiconj_by.nsmul_right

Modified src/analysis/special_functions/trigonometric.lean
- \- *lemma* real.angle.coe_gsmul
- \+ *lemma* real.angle.coe_int_mul_eq_gsmul
- \+ *lemma* real.angle.coe_nat_mul_eq_nsmul
- \- *lemma* real.angle.coe_smul

Modified src/data/real/nnreal.lean




## [2020-06-09 20:16:58](https://github.com/leanprover-community/mathlib/commit/a02ab48)
refactor(group_theory/subgroup): swap `mul_mem_cancel_left/right` ([#3011](https://github.com/leanprover-community/mathlib/pull/3011))
This way the name follows the position of the term we cancel.
#### Estimated changes
Modified src/deprecated/subgroup.lean
- \+/\- *lemma* is_subgroup.mul_mem_cancel_left
- \+/\- *lemma* is_subgroup.mul_mem_cancel_right

Modified src/group_theory/coset.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+ *theorem* subgroup.inv_mem_iff
- \+/\- *lemma* subgroup.mul_mem_cancel_left
- \+/\- *lemma* subgroup.mul_mem_cancel_right

Modified src/group_theory/sylow.lean




## [2020-06-09 19:36:31](https://github.com/leanprover-community/mathlib/commit/df34ee2)
chore(scripts): update nolints.txt ([#3010](https://github.com/leanprover-community/mathlib/pull/3010))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-09 17:36:44](https://github.com/leanprover-community/mathlib/commit/1a4f0c2)
refactor(algebra/ordered_group): multiplicative versions of ordered monoids/groups ([#2844](https://github.com/leanprover-community/mathlib/pull/2844))
This PR defines multiplicative versions of ordered monoids and groups. It also lints the file.
#### Estimated changes
Modified src/algebra/group/defs.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* add_eq_zero_iff'
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \- *lemma* add_eq_zero_iff_eq_zero_of_nonneg
- \- *lemma* add_le_add'
- \- *lemma* add_le_add
- \- *lemma* add_le_add_iff_left
- \- *lemma* add_le_add_iff_right
- \- *lemma* add_le_add_left'
- \- *lemma* add_le_add_left
- \- *lemma* add_le_add_right'
- \- *lemma* add_le_add_right
- \- *lemma* add_le_add_three
- \- *lemma* add_le_iff_nonpos_left
- \- *lemma* add_le_iff_nonpos_right
- \- *lemma* add_le_of_le_neg_add
- \- *lemma* add_le_of_le_of_nonpos'
- \- *lemma* add_le_of_le_of_nonpos
- \- *lemma* add_le_of_nonpos_of_le'
- \- *lemma* add_le_of_nonpos_of_le
- \- *lemma* add_lt_add
- \- *lemma* add_lt_add_iff_left
- \- *lemma* add_lt_add_iff_right
- \- *lemma* add_lt_add_left
- \- *lemma* add_lt_add_of_le_of_lt
- \- *lemma* add_lt_add_of_lt_of_le
- \- *theorem* add_lt_add_right
- \- *lemma* add_lt_iff_neg_left
- \- *lemma* add_lt_iff_neg_right
- \- *lemma* add_lt_of_le_of_neg
- \- *lemma* add_lt_of_lt_neg_add
- \- *lemma* add_lt_of_lt_of_neg'
- \- *lemma* add_lt_of_lt_of_neg
- \- *lemma* add_lt_of_lt_of_nonpos'
- \- *lemma* add_lt_of_lt_of_nonpos
- \- *lemma* add_lt_of_neg_of_le
- \- *lemma* add_lt_of_neg_of_lt'
- \- *lemma* add_lt_of_neg_of_lt
- \- *lemma* add_lt_of_nonpos_of_lt'
- \- *lemma* add_lt_of_nonpos_of_lt
- \- *lemma* add_neg'
- \- *lemma* add_neg
- \- *lemma* add_neg_le_iff_le_add'
- \- *lemma* add_neg_le_iff_le_add
- \- *lemma* add_neg_of_neg_of_nonpos'
- \- *lemma* add_neg_of_neg_of_nonpos
- \- *lemma* add_neg_of_nonpos_of_neg'
- \- *lemma* add_neg_of_nonpos_of_neg
- \- *lemma* add_nonneg'
- \- *lemma* add_nonneg
- \- *lemma* add_nonpos'
- \- *lemma* add_nonpos
- \- *lemma* add_pos'
- \- *lemma* add_pos
- \- *lemma* add_pos_of_nonneg_of_pos'
- \- *lemma* add_pos_of_nonneg_of_pos
- \- *lemma* add_pos_of_pos_of_nonneg'
- \- *lemma* add_pos_of_pos_of_nonneg
- \+/\- *lemma* bit0_pos
- \+/\- *lemma* dist_bdd_within_interval
- \+ *lemma* inv_inv_of_one_lt
- \+ *lemma* inv_le'
- \+ *lemma* inv_le_iff_one_le_mul
- \+ *lemma* inv_le_inv'
- \+ *lemma* inv_le_inv_iff
- \+ *lemma* inv_le_of_inv_le
- \+ *lemma* inv_le_one'
- \+ *lemma* inv_le_one_of_one_le
- \+ *lemma* inv_le_self
- \+ *lemma* inv_lt'
- \+ *lemma* inv_lt_inv'
- \+ *lemma* inv_lt_inv_iff
- \+ *lemma* inv_lt_of_inv_lt
- \+ *lemma* inv_lt_one'
- \+ *lemma* inv_lt_one_iff_one_lt
- \+ *lemma* inv_mul_le_iff_le_mul'
- \+ *lemma* inv_mul_le_iff_le_mul
- \+ *lemma* inv_mul_le_left_of_le_mul
- \+ *lemma* inv_mul_le_of_le_mul
- \+ *lemma* inv_mul_le_right_of_le_mul
- \+ *lemma* inv_mul_lt_iff_lt_mul
- \+ *lemma* inv_mul_lt_iff_lt_mul_right
- \+ *lemma* inv_mul_lt_left_of_lt_mul
- \+ *lemma* inv_mul_lt_of_lt_mul
- \+ *lemma* inv_mul_lt_right_of_lt_mul
- \+ *lemma* inv_of_one_lt_inv
- \- *lemma* le_add_iff_nonneg_left
- \- *lemma* le_add_iff_nonneg_right
- \- *lemma* le_add_of_le_of_nonneg'
- \- *lemma* le_add_of_le_of_nonneg
- \- *lemma* le_add_of_neg_add_le
- \- *lemma* le_add_of_neg_add_le_left
- \- *lemma* le_add_of_neg_add_le_right
- \- *lemma* le_add_of_nonneg_left'
- \- *lemma* le_add_of_nonneg_left
- \- *lemma* le_add_of_nonneg_of_le'
- \- *lemma* le_add_of_nonneg_of_le
- \- *lemma* le_add_of_nonneg_right'
- \- *lemma* le_add_of_nonneg_right
- \+ *lemma* le_inv'
- \+ *lemma* le_inv_iff_mul_le_one
- \+ *lemma* le_inv_mul_iff_mul_le
- \+ *lemma* le_inv_mul_of_mul_le
- \+ *lemma* le_inv_of_le_inv
- \+ *lemma* le_mul_iff_one_le_left'
- \+ *lemma* le_mul_iff_one_le_right'
- \+ *lemma* le_mul_of_inv_mul_le
- \+ *lemma* le_mul_of_inv_mul_le_left
- \+ *lemma* le_mul_of_inv_mul_le_right
- \+ *lemma* le_mul_of_le_of_one_le'
- \+ *lemma* le_mul_of_le_of_one_le
- \+ *lemma* le_mul_of_one_le_left''
- \+ *lemma* le_mul_of_one_le_left
- \+ *lemma* le_mul_of_one_le_of_le'
- \+ *lemma* le_mul_of_one_le_of_le
- \+ *lemma* le_mul_of_one_le_right''
- \+ *lemma* le_mul_of_one_le_right
- \- *lemma* le_neg
- \- *lemma* le_neg_add_iff_add_le
- \- *lemma* le_neg_add_of_add_le
- \- *lemma* le_neg_iff_add_nonpos
- \- *lemma* le_neg_of_le_neg
- \- *lemma* le_of_add_le_add_left
- \- *lemma* le_of_add_le_add_right
- \+ *lemma* le_of_inv_le_inv
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* le_of_mul_le_mul_right'
- \- *lemma* le_of_neg_le_neg
- \+ *lemma* le_one_of_one_le_inv
- \- *lemma* lt_add_iff_pos_left
- \- *lemma* lt_add_iff_pos_right
- \- *lemma* lt_add_of_le_of_pos
- \- *lemma* lt_add_of_lt_of_nonneg'
- \- *lemma* lt_add_of_lt_of_nonneg
- \- *lemma* lt_add_of_lt_of_pos'
- \- *lemma* lt_add_of_lt_of_pos
- \- *lemma* lt_add_of_neg_add_lt
- \- *lemma* lt_add_of_neg_add_lt_left
- \- *lemma* lt_add_of_neg_add_lt_right
- \- *lemma* lt_add_of_nonneg_of_lt'
- \- *lemma* lt_add_of_nonneg_of_lt
- \- *lemma* lt_add_of_pos_left
- \- *lemma* lt_add_of_pos_of_le
- \- *lemma* lt_add_of_pos_of_lt'
- \- *lemma* lt_add_of_pos_of_lt
- \- *lemma* lt_add_of_pos_right
- \+ *lemma* lt_inv'
- \+ *lemma* lt_inv_mul_iff_mul_lt
- \+ *lemma* lt_inv_mul_of_mul_lt
- \+ *lemma* lt_inv_of_lt_inv
- \+ *lemma* lt_mul_iff_one_lt_left'
- \+ *lemma* lt_mul_iff_one_lt_right'
- \+ *lemma* lt_mul_of_inv_mul_lt
- \+ *lemma* lt_mul_of_inv_mul_lt_left
- \+ *lemma* lt_mul_of_inv_mul_lt_right
- \+ *lemma* lt_mul_of_le_of_one_lt
- \+ *lemma* lt_mul_of_lt_of_one_le'
- \+ *lemma* lt_mul_of_lt_of_one_le
- \+ *lemma* lt_mul_of_lt_of_one_lt'
- \+ *lemma* lt_mul_of_lt_of_one_lt
- \+ *lemma* lt_mul_of_one_le_of_lt'
- \+ *lemma* lt_mul_of_one_le_of_lt
- \+ *lemma* lt_mul_of_one_lt_left
- \+ *lemma* lt_mul_of_one_lt_of_le
- \+ *lemma* lt_mul_of_one_lt_of_lt'
- \+ *lemma* lt_mul_of_one_lt_of_lt
- \+ *lemma* lt_mul_of_one_lt_right
- \- *lemma* lt_neg
- \- *lemma* lt_neg_add_iff_add_lt
- \- *lemma* lt_neg_add_of_add_lt
- \- *lemma* lt_neg_of_lt_neg
- \- *lemma* lt_of_add_lt_add_left'
- \- *lemma* lt_of_add_lt_add_left
- \- *lemma* lt_of_add_lt_add_right'
- \- *lemma* lt_of_add_lt_add_right
- \+ *lemma* lt_of_inv_lt_inv
- \+ *lemma* lt_of_mul_lt_mul_left''
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* lt_of_mul_lt_mul_right''
- \+ *lemma* lt_of_mul_lt_mul_right'
- \- *lemma* lt_of_neg_lt_neg
- \- *lemma* monotone.add
- \- *lemma* monotone.add_const
- \- *lemma* monotone.add_strict_mono
- \- *lemma* monotone.const_add
- \+ *lemma* monotone.const_mul'
- \+ *lemma* monotone.mul'
- \+ *lemma* monotone.mul_const'
- \+ *lemma* monotone.mul_strict_mono'
- \+ *lemma* mul_eq_one_iff'
- \+ *lemma* mul_eq_one_iff_eq_one_and_eq_one_of_one_le_of_one_le
- \+ *lemma* mul_eq_one_iff_eq_one_of_one_le
- \+ *lemma* mul_inv_le_iff_le_mul'
- \+ *lemma* mul_inv_le_iff_le_mul
- \+ *lemma* mul_le_iff_le_one_left'
- \+ *lemma* mul_le_iff_le_one_right'
- \+ *lemma* mul_le_mul''
- \+ *lemma* mul_le_mul'
- \+ *lemma* mul_le_mul_iff_left
- \+ *lemma* mul_le_mul_iff_right
- \+ *lemma* mul_le_mul_left''
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right''
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* mul_le_mul_three
- \+ *lemma* mul_le_of_le_inv_mul
- \+ *lemma* mul_le_of_le_of_le_one'
- \+ *lemma* mul_le_of_le_of_le_one
- \+ *lemma* mul_le_of_le_one_of_le'
- \+ *lemma* mul_le_of_le_one_of_le
- \+ *lemma* mul_le_one''
- \+ *lemma* mul_le_one'
- \+ *lemma* mul_lt_iff_lt_one_left'
- \+ *lemma* mul_lt_iff_lt_one_right'
- \+ *lemma* mul_lt_mul'''
- \+ *lemma* mul_lt_mul_iff_left
- \+ *lemma* mul_lt_mul_iff_right
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* mul_lt_mul_of_le_of_lt
- \+ *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* mul_lt_of_le_of_lt_one
- \+ *lemma* mul_lt_of_le_one_of_lt'
- \+ *lemma* mul_lt_of_le_one_of_lt
- \+ *lemma* mul_lt_of_lt_inv_mul
- \+ *lemma* mul_lt_of_lt_of_le_one'
- \+ *lemma* mul_lt_of_lt_of_le_one
- \+ *lemma* mul_lt_of_lt_of_lt_one'
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \+ *lemma* mul_lt_of_lt_one_of_le
- \+ *lemma* mul_lt_of_lt_one_of_lt'
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \+ *lemma* mul_lt_one'
- \+ *lemma* mul_lt_one
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one'
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one'
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one
- \+ *lemma* mul_one_lt'
- \+ *lemma* mul_one_lt
- \+ *lemma* mul_one_lt_of_one_le_of_one_lt'
- \+ *lemma* mul_one_lt_of_one_le_of_one_lt
- \+ *lemma* mul_one_lt_of_one_lt_of_one_le'
- \+ *lemma* mul_one_lt_of_one_lt_of_one_le
- \- *lemma* neg_add_le_iff_le_add'
- \- *lemma* neg_add_le_iff_le_add
- \- *lemma* neg_add_le_left_of_le_add
- \- *lemma* neg_add_le_of_le_add
- \- *lemma* neg_add_le_right_of_le_add
- \- *lemma* neg_add_lt_iff_lt_add
- \- *lemma* neg_add_lt_iff_lt_add_right
- \- *lemma* neg_add_lt_left_of_lt_add
- \- *lemma* neg_add_lt_of_lt_add
- \- *lemma* neg_add_lt_right_of_lt_add
- \- *lemma* neg_le
- \- *lemma* neg_le_iff_add_nonneg
- \- *lemma* neg_le_neg
- \- *lemma* neg_le_neg_iff
- \- *lemma* neg_le_of_neg_le
- \- *lemma* neg_le_self
- \- *lemma* neg_lt
- \- *lemma* neg_lt_neg
- \- *lemma* neg_lt_neg_iff
- \- *lemma* neg_lt_of_neg_lt
- \- *lemma* neg_lt_zero
- \- *lemma* neg_neg_iff_pos
- \- *lemma* neg_neg_of_pos
- \- *lemma* neg_nonneg
- \- *lemma* neg_nonneg_of_nonpos
- \- *lemma* neg_nonpos
- \- *lemma* neg_nonpos_of_nonneg
- \- *lemma* neg_of_neg_pos
- \- *lemma* neg_pos
- \- *lemma* neg_pos_of_neg
- \- *lemma* nonneg_of_neg_nonpos
- \- *lemma* nonpos_of_neg_nonneg
- \+ *lemma* one_le_inv'
- \+ *lemma* one_le_inv_of_le_one
- \+ *lemma* one_le_mul'
- \+ *lemma* one_le_mul
- \+ *lemma* one_le_of_inv_le_one
- \+ *lemma* one_lt_inv'
- \+ *lemma* one_lt_inv_of_inv
- \+ *lemma* one_lt_of_inv_inv
- \- *lemma* ordered_add_comm_group.add_lt_add_left
- \- *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \- *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \- *def* ordered_add_comm_group.mk'
- \+ *lemma* ordered_comm_group.le_of_mul_le_mul_left
- \+ *lemma* ordered_comm_group.lt_of_mul_lt_mul_left
- \+ *def* ordered_comm_group.mk'
- \+ *lemma* ordered_comm_group.mul_lt_mul_left'
- \- *lemma* pos_of_neg_neg
- \+ *lemma* self_le_inv
- \- *lemma* self_le_neg
- \- *lemma* strict_mono.add_const
- \- *lemma* strict_mono.add_monotone
- \- *lemma* strict_mono.const_add
- \+ *lemma* strict_mono.const_mul'
- \+ *lemma* strict_mono.mul_const'
- \+ *lemma* strict_mono.mul_monotone'
- \+/\- *theorem* units.coe_le_coe
- \+/\- *theorem* units.coe_lt_coe



## [2020-06-09 17:00:44](https://github.com/leanprover-community/mathlib/commit/f098c16)
feat(ring_theory/localization): more lemmas and defs about fields of fractions ([#3005](https://github.com/leanprover-community/mathlib/pull/3005))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *lemma* fraction_map.is_unit_map_of_injective
- \+ *lemma* fraction_map.lift_mk'
- \+ *lemma* fraction_map.mk'_eq_div
- \+ *lemma* fraction_ring.mk_eq_div
- \+ *def* fraction_ring
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+/\- *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *def* of



## [2020-06-09 12:21:46](https://github.com/leanprover-community/mathlib/commit/ccdf1d2)
feat(category_theory/limits): prod.lift_comp_comp ([#2968](https://github.com/leanprover-community/mathlib/pull/2968))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.desc_comp_comp
- \+ *lemma* category_theory.limits.prod.lift_comp_comp



## [2020-06-09 11:36:39](https://github.com/leanprover-community/mathlib/commit/7cb0a85)
refactor(topology): rename `lim` to `Lim` ([#2977](https://github.com/leanprover-community/mathlib/pull/2977))
Also introduce `lim (f : filter α) (g : α → β)`.
#### Estimated changes
Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/topology/basic.lean
- \+ *lemma* Lim_spec
- \+/\- *lemma* lim_spec

Modified src/topology/dense_embedding.lean
- \+/\- *lemma* dense_inducing.extend_eq

Modified src/topology/separation.lean
- \+ *lemma* Lim_eq
- \+ *lemma* Lim_nhds
- \+ *lemma* Lim_nhds_within
- \+ *lemma* continuous.lim_eq
- \+ *lemma* filter.tendsto.lim_eq
- \- *lemma* lim_eq
- \- *lemma* lim_nhds_eq
- \- *lemma* lim_nhds_eq_of_closure
- \+ *lemma* lim_nhds_id
- \+ *lemma* lim_nhds_within_id

Modified src/topology/uniform_space/cauchy.lean
- \+ *theorem* cauchy.le_nhds_Lim
- \+ *theorem* cauchy_seq.tendsto_lim
- \- *theorem* le_nhds_lim_of_cauchy

Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-09 11:05:31](https://github.com/leanprover-community/mathlib/commit/76792dc)
feat(algebra/add_torsor): add `prod.add_torsor` ([#2980](https://github.com/leanprover-community/mathlib/pull/2980))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* prod.fst_vadd
- \+ *lemma* prod.fst_vsub
- \+ *lemma* prod.mk_vadd_mk
- \+ *lemma* prod.mk_vsub_mk
- \+ *lemma* prod.snd_vadd
- \+ *lemma* prod.snd_vsub



## [2020-06-09 09:07:38](https://github.com/leanprover-community/mathlib/commit/4281343)
refactor(data/polynomial): redefine `C` as an `alg_hom` ([#3003](https://github.com/leanprover-community/mathlib/pull/3003))
As a side effect Lean parses `C 1` as `polynomial nat`. If you need `polynomial R`, then use `C (1:R)`.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/data/polynomial.lean
- \+/\- *def* polynomial.C
- \+/\- *lemma* polynomial.C_0
- \+/\- *lemma* polynomial.C_1
- \+/\- *lemma* polynomial.C_add
- \+ *lemma* polynomial.C_def
- \+/\- *lemma* polynomial.C_mul
- \+/\- *lemma* polynomial.C_neg
- \+/\- *lemma* polynomial.C_pow
- \+/\- *lemma* polynomial.C_sub
- \+/\- *lemma* polynomial.int_cast_eq_C
- \+/\- *def* polynomial.lcoeff
- \+/\- *lemma* polynomial.nat_cast_eq_C

Modified src/field_theory/minimal_polynomial.lean




## [2020-06-09 08:13:56](https://github.com/leanprover-community/mathlib/commit/34302c6)
chore(ring_theory/algebra): add comments explaining absence of 2 `simp` attrs ([#3002](https://github.com/leanprover-community/mathlib/pull/3002))
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2020-06-09 08:13:54](https://github.com/leanprover-community/mathlib/commit/03c345f)
chore(data/real/nnreal): +2 lemmas ([#3000](https://github.com/leanprover-community/mathlib/pull/3000))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.div_le_iff
- \+ *lemma* nnreal.sum_div



## [2020-06-09 08:13:52](https://github.com/leanprover-community/mathlib/commit/1091462)
feat(analysis/special_functions/pow): `inv_rpow`, `div_rpow` ([#2999](https://github.com/leanprover-community/mathlib/pull/2999))
Also use notation `ℝ≥0` and use `nnreal.eq` instead of `rw ← nnreal.coe_eq`.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.log_inv

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* ennreal.coe_mul_rpow
- \+/\- *lemma* ennreal.coe_rpow_of_ne_zero
- \+/\- *lemma* ennreal.coe_rpow_of_nonneg
- \+/\- *lemma* filter.tendsto.nnrpow
- \+/\- *lemma* nnreal.coe_rpow
- \+/\- *lemma* nnreal.continuous_at_rpow
- \+ *lemma* nnreal.div_rpow
- \+ *lemma* nnreal.inv_rpow
- \+/\- *lemma* nnreal.mul_rpow
- \+/\- *lemma* nnreal.one_le_rpow
- \+/\- *lemma* nnreal.one_lt_rpow
- \+/\- *lemma* nnreal.one_rpow
- \+/\- *lemma* nnreal.pow_nat_rpow_nat_inv
- \+ *lemma* nnreal.rpow_add'
- \+/\- *lemma* nnreal.rpow_add
- \+/\- *lemma* nnreal.rpow_eq_pow
- \+/\- *lemma* nnreal.rpow_eq_zero_iff
- \+/\- *lemma* nnreal.rpow_le_one
- \+/\- *lemma* nnreal.rpow_le_rpow
- \+/\- *lemma* nnreal.rpow_le_rpow_of_exponent_ge
- \+/\- *lemma* nnreal.rpow_le_rpow_of_exponent_le
- \+/\- *lemma* nnreal.rpow_lt_one
- \+/\- *lemma* nnreal.rpow_lt_rpow
- \+/\- *lemma* nnreal.rpow_lt_rpow_of_exponent_gt
- \+/\- *lemma* nnreal.rpow_lt_rpow_of_exponent_lt
- \+/\- *lemma* nnreal.rpow_mul
- \+/\- *lemma* nnreal.rpow_nat_cast
- \+/\- *lemma* nnreal.rpow_nat_inv_pow_nat
- \+/\- *lemma* nnreal.rpow_neg
- \+/\- *lemma* nnreal.rpow_one
- \+/\- *lemma* nnreal.rpow_zero
- \+/\- *lemma* nnreal.zero_rpow
- \+ *lemma* real.div_rpow
- \+ *lemma* real.inv_rpow
- \+/\- *lemma* real.one_le_rpow



## [2020-06-09 07:06:53](https://github.com/leanprover-community/mathlib/commit/45567dc)
chore(algebra/big_operators): add `@[simp] lemma sum_eq_zero_iff` ([#2998](https://github.com/leanprover-community/mathlib/pull/2998))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* finset.sum_eq_zero_iff



## [2020-06-09 05:24:03](https://github.com/leanprover-community/mathlib/commit/24ce416)
chore(data/matrix/basic): clean up of new lemmas on matrix numerals ([#2996](https://github.com/leanprover-community/mathlib/pull/2996))
Generalise and improve use of `@[simp]` for some newly added lemmas about matrix numerals.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \- *lemma* matrix.bit0_apply_apply
- \+ *lemma* matrix.bit0_val
- \- *lemma* matrix.bit1_apply_apply
- \+ *lemma* matrix.bit1_val
- \+ *lemma* matrix.bit1_val_eq
- \+ *lemma* matrix.bit1_val_ne



## [2020-06-08 20:32:11](https://github.com/leanprover-community/mathlib/commit/7bb2d89)
feat(dynamics/fixed_points/topology): new file ([#2991](https://github.com/leanprover-community/mathlib/pull/2991))
* Move `is_fixed_pt_of_tendsto_iterate` from
  `topology.metric_space.contracting`, reformulate it without `∃`.
* Add `is_closed_fixed_points`.
* Move `dynamics.fixed_points` to `dynamics.fixed_points.basic`.
#### Estimated changes
Modified src/dynamics/circle/rotation_number/translation_number.lean


Renamed src/dynamics/fixed_points.lean to src/dynamics/fixed_points/basic.lean


Added src/dynamics/fixed_points/topology.lean
- \+ *lemma* is_closed_fixed_points
- \+ *lemma* is_fixed_pt_of_tendsto_iterate

Modified src/order/fixed_points.lean


Modified src/topology/basic.lean
- \+ *lemma* continuous_at.tendsto

Modified src/topology/metric_space/contracting.lean
- \- *lemma* is_fixed_pt_of_tendsto_iterate



## [2020-06-08 19:36:45](https://github.com/leanprover-community/mathlib/commit/470ccd3)
chore(scripts): update nolints.txt ([#2993](https://github.com/leanprover-community/mathlib/pull/2993))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-08 19:36:43](https://github.com/leanprover-community/mathlib/commit/94deddd)
feat(data/real/conjugate_exponents): define real conjugate exponents ([#2992](https://github.com/leanprover-community/mathlib/pull/2992))
#### Estimated changes
Added src/data/real/conjugate_exponents.lean
- \+ *def* real.conjugate_exponent
- \+ *lemma* real.is_conjugate_exponent.conj_eq
- \+ *lemma* real.is_conjugate_exponent.ne_zero
- \+ *lemma* real.is_conjugate_exponent.one_div_ne_zero
- \+ *lemma* real.is_conjugate_exponent.one_div_pos
- \+ *lemma* real.is_conjugate_exponent.pos
- \+ *lemma* real.is_conjugate_exponent.sub_one_ne_zero
- \+ *structure* real.is_conjugate_exponent
- \+ *lemma* real.is_conjugate_exponent_conjugate_exponent
- \+ *lemma* real.is_conjugate_exponent_iff



## [2020-06-08 19:36:41](https://github.com/leanprover-community/mathlib/commit/4ee67ac)
chore(*): use prod notation ([#2989](https://github.com/leanprover-community/mathlib/pull/2989))
The biggest field test of the new product notation.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/mean_inequalities.lean


Modified src/data/monoid_algebra.lean


Modified src/data/real/ennreal.lean


Modified src/data/support.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.prod_Ico_one_prime

Modified src/ring_theory/algebra.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/multiplicity.lean




## [2020-06-08 19:36:39](https://github.com/leanprover-community/mathlib/commit/a377993)
feat(geometry/euclidean): angles and some basic lemmas ([#2865](https://github.com/leanprover-community/mathlib/pull/2865))
Define angles (undirected, between 0 and π, in terms of inner
product), and prove some basic lemmas involving angles, for real inner
product spaces and Euclidean affine spaces.
From the 100-theorems list, this provides versions of
* 04 Pythagorean Theorem,
* 65 Isosceles Triangle Theorem and
* 94 The Law of Cosines, with various existing definitions implicitly providing
* 91 The Triangle Inequality.
#### Estimated changes
Modified src/analysis/normed_space/real_inner_product.lean
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* abs_inner_div_norm_mul_norm_le_one
- \+ *lemma* inner_div_norm_mul_norm_eq_neg_one_iff
- \+ *lemma* inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \+ *lemma* inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \+ *lemma* inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \+ *lemma* inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
- \+ *lemma* inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \+ *lemma* inner_smul_self_left
- \+ *lemma* inner_smul_self_right
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero

Modified src/geometry/euclidean.lean
- \+ *def* euclidean_geometry.angle
- \+ *lemma* euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_comm
- \+ *lemma* euclidean_geometry.angle_eq_angle_of_angle_eq_pi
- \+ *lemma* euclidean_geometry.angle_eq_angle_of_dist_eq
- \+ *lemma* euclidean_geometry.angle_eq_left
- \+ *lemma* euclidean_geometry.angle_eq_of_ne
- \+ *lemma* euclidean_geometry.angle_eq_right
- \+ *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left
- \+ *lemma* euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right
- \+ *lemma* euclidean_geometry.angle_le_pi
- \+ *lemma* euclidean_geometry.angle_nonneg
- \+ *lemma* euclidean_geometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \+ *lemma* euclidean_geometry.dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \+ *def* inner_product_geometry.angle
- \+ *lemma* inner_product_geometry.angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* inner_product_geometry.angle_comm
- \+ *lemma* inner_product_geometry.angle_eq_pi_iff
- \+ *lemma* inner_product_geometry.angle_eq_zero_iff
- \+ *lemma* inner_product_geometry.angle_le_pi
- \+ *lemma* inner_product_geometry.angle_neg_left
- \+ *lemma* inner_product_geometry.angle_neg_neg
- \+ *lemma* inner_product_geometry.angle_neg_right
- \+ *lemma* inner_product_geometry.angle_neg_self_of_nonzero
- \+ *lemma* inner_product_geometry.angle_nonneg
- \+ *lemma* inner_product_geometry.angle_self
- \+ *lemma* inner_product_geometry.angle_self_neg_of_nonzero
- \+ *lemma* inner_product_geometry.angle_smul_left_of_neg
- \+ *lemma* inner_product_geometry.angle_smul_left_of_pos
- \+ *lemma* inner_product_geometry.angle_smul_right_of_neg
- \+ *lemma* inner_product_geometry.angle_smul_right_of_pos
- \+ *lemma* inner_product_geometry.angle_sub_eq_angle_sub_rev_of_norm_eq
- \+ *lemma* inner_product_geometry.angle_zero_left
- \+ *lemma* inner_product_geometry.angle_zero_right
- \+ *lemma* inner_product_geometry.cos_angle
- \+ *lemma* inner_product_geometry.cos_angle_mul_norm_mul_norm
- \+ *lemma* inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square'
- \+ *lemma* inner_product_geometry.norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square'
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* inner_product_geometry.norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \+ *lemma* inner_product_geometry.sin_angle_mul_norm_mul_norm



## [2020-06-08 19:05:30](https://github.com/leanprover-community/mathlib/commit/dbbd696)
feat(order/ideal): order ideals, cofinal sets and the Rasiowa-Sikorski lemma ([#2850](https://github.com/leanprover-community/mathlib/pull/2850))
We define order ideals and cofinal sets, and use them to prove the (very simple) Rasiowa-Sikorski lemma: given a countable family of cofinal subsets of an inhabited preorder, there is an upwards directed set meeting each one. This provides an API for certain recursive constructions.
#### Estimated changes
Added src/order/ideal.lean
- \+ *lemma* order.cofinal.above_mem
- \+ *lemma* order.cofinal.le_above
- \+ *structure* order.cofinal
- \+ *lemma* order.cofinal_meets_ideal_of_cofinals
- \+ *def* order.ideal.principal
- \+ *structure* order.ideal
- \+ *def* order.ideal_of_cofinals
- \+ *lemma* order.mem_ideal_of_cofinals
- \+ *lemma* order.sequence_of_cofinals.encode_mem
- \+ *lemma* order.sequence_of_cofinals.monotone



## [2020-06-08 17:34:19](https://github.com/leanprover-community/mathlib/commit/d204daa)
chore(*): add docs and nolints ([#2990](https://github.com/leanprover-community/mathlib/pull/2990))
Other changes:
* Reuse `gmultiples_hom` for `AddCommGroup.as_hom`.
* Reuse `add_monoid_hom.ext_int` for `AddCommGroup.int_hom_ext`.
* Drop the following definitions, define an `instance` right away
  instead:
  - `algebra.div`;
  - `monoid_hom.one`, `add_monoid_hom.zero`;
  - `monoid_hom.mul`, `add_monoid_hom.add`;
  - `monoid_hom.inv`, `add_monoid_hom.neg`.
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/field.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/defs.lean


Modified src/algebra/group/hom.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean




## [2020-06-08 17:34:17](https://github.com/leanprover-community/mathlib/commit/9fba817)
refactor(algebra/*): move `commute` below `ring` in `import`s ([#2973](https://github.com/leanprover-community/mathlib/pull/2973))
Fixes [#1865](https://github.com/leanprover-community/mathlib/pull/1865)
API changes:
* drop lemmas about unbundled `center`;
* add `to_additive` to `semiconj_by` and `commute`;
* drop `inv_comm_of_comm` in favor of `commute.left_inv`,
  same with `inv_comm_of_comm` and `commute.left_inv'`;
* rename `monoid_hom.map_commute` to `commute.map`, same with
  `semiconj_by`;
* drop `commute.cast_*_*` and `nat/int/rat.mul_cast_comm`, add
  `nat/int/rat.cast_commute` and `nat.int.rat.commute_cast`;
* add `commute.mul_fpow`.
#### Estimated changes
Deleted src/algebra/commute.lean
- \- *lemma* add_monoid.centralizer_closure
- \- *def* centralizer.add_submonoid
- \- *lemma* centralizer.inter_units_is_subgroup
- \- *def* centralizer
- \- *theorem* commute.add_left
- \- *theorem* commute.add_right
- \- *theorem* commute.cast_int_left
- \- *theorem* commute.cast_int_right
- \- *theorem* commute.cast_nat_left
- \- *theorem* commute.cast_nat_right
- \- *theorem* commute.div_left
- \- *theorem* commute.div_right
- \- *theorem* commute.finv_finv
- \- *theorem* commute.finv_left
- \- *theorem* commute.finv_left_iff
- \- *theorem* commute.finv_right
- \- *theorem* commute.finv_right_iff
- \- *theorem* commute.gpow_gpow
- \- *theorem* commute.gpow_gpow_self
- \- *theorem* commute.gpow_left
- \- *theorem* commute.gpow_right
- \- *theorem* commute.gpow_self
- \- *theorem* commute.gsmul_gsmul
- \- *theorem* commute.gsmul_left
- \- *theorem* commute.gsmul_right
- \- *theorem* commute.gsmul_self
- \- *theorem* commute.inv_inv
- \- *theorem* commute.inv_inv_iff
- \- *theorem* commute.inv_left
- \- *theorem* commute.inv_left_iff
- \- *theorem* commute.inv_right
- \- *theorem* commute.inv_right_iff
- \- *theorem* commute.list_prod_left
- \- *theorem* commute.list_prod_right
- \- *theorem* commute.mul_left
- \- *theorem* commute.mul_right
- \- *theorem* commute.neg_left
- \- *theorem* commute.neg_left_iff
- \- *theorem* commute.neg_one_left
- \- *theorem* commute.neg_one_right
- \- *theorem* commute.neg_right
- \- *theorem* commute.neg_right_iff
- \- *theorem* commute.nsmul_left
- \- *theorem* commute.nsmul_nsmul
- \- *theorem* commute.nsmul_right
- \- *theorem* commute.nsmul_self
- \- *theorem* commute.one_left
- \- *theorem* commute.one_right
- \- *theorem* commute.pow_left
- \- *theorem* commute.pow_pow
- \- *theorem* commute.pow_pow_self
- \- *theorem* commute.pow_right
- \- *theorem* commute.pow_self
- \- *theorem* commute.self_gpow
- \- *theorem* commute.self_gsmul
- \- *theorem* commute.self_gsmul_gsmul
- \- *theorem* commute.self_nsmul
- \- *theorem* commute.self_nsmul_nsmul
- \- *theorem* commute.self_pow
- \- *theorem* commute.sub_left
- \- *theorem* commute.sub_right
- \- *theorem* commute.units_coe
- \- *theorem* commute.units_coe_iff
- \- *theorem* commute.units_inv_left
- \- *theorem* commute.units_inv_left_iff
- \- *theorem* commute.units_inv_right
- \- *theorem* commute.units_inv_right_iff
- \- *theorem* commute.units_of_coe
- \- *theorem* commute.zero_left
- \- *theorem* commute.zero_right
- \- *def* commute
- \- *lemma* group.centralizer_closure
- \- *theorem* mem_centralizer
- \- *theorem* monoid.centralizer_closure
- \- *theorem* neg_pow
- \- *lemma* ring.centralizer_closure
- \- *def* set.centralizer.add_submonoid
- \- *def* submonoid.centralizer
- \- *def* submonoid.set.centralizer

Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \- *theorem* inv_comm_of_comm

Added src/algebra/group/commute.lean
- \+ *theorem* commute.inv_inv
- \+ *theorem* commute.inv_inv_iff
- \+ *theorem* commute.inv_left
- \+ *theorem* commute.inv_left_iff
- \+ *theorem* commute.inv_right
- \+ *theorem* commute.inv_right_iff
- \+ *theorem* commute.mul_left
- \+ *theorem* commute.mul_right
- \+ *theorem* commute.one_left
- \+ *theorem* commute.one_right
- \+ *theorem* commute.units_coe
- \+ *theorem* commute.units_coe_iff
- \+ *theorem* commute.units_inv_left
- \+ *theorem* commute.units_inv_left_iff
- \+ *theorem* commute.units_inv_right
- \+ *theorem* commute.units_inv_right_iff
- \+ *theorem* commute.units_of_coe
- \+ *def* commute

Modified src/algebra/group/hom.lean


Added src/algebra/group/semiconj.lean
- \+ *lemma* semiconj_by.conj_mk
- \+ *lemma* semiconj_by.inv_inv_symm
- \+ *lemma* semiconj_by.inv_inv_symm_iff
- \+ *lemma* semiconj_by.inv_right
- \+ *lemma* semiconj_by.inv_right_iff
- \+ *lemma* semiconj_by.inv_symm_left
- \+ *lemma* semiconj_by.inv_symm_left_iff
- \+ *lemma* semiconj_by.mul_left
- \+ *lemma* semiconj_by.mul_right
- \+ *lemma* semiconj_by.one_left
- \+ *lemma* semiconj_by.one_right
- \+ *theorem* semiconj_by.units_coe
- \+ *theorem* semiconj_by.units_coe_iff
- \+ *lemma* semiconj_by.units_inv_right
- \+ *lemma* semiconj_by.units_inv_right_iff
- \+ *lemma* semiconj_by.units_inv_symm_left
- \+ *lemma* semiconj_by.units_inv_symm_left_iff
- \+ *theorem* semiconj_by.units_of_coe
- \+ *def* semiconj_by
- \+ *lemma* units.mk_semiconj_by

Modified src/algebra/group_power.lean
- \+ *lemma* commute.gpow_gpow
- \+ *theorem* commute.gpow_gpow_self
- \+ *lemma* commute.gpow_left
- \+ *lemma* commute.gpow_right
- \+ *theorem* commute.gpow_self
- \+ *lemma* commute.gsmul_gsmul
- \+ *lemma* commute.gsmul_left
- \+ *lemma* commute.gsmul_right
- \+ *theorem* commute.gsmul_self
- \+ *theorem* commute.mul_gpow
- \+ *lemma* commute.mul_pow
- \+ *theorem* commute.nsmul_left
- \+ *theorem* commute.nsmul_nsmul
- \+ *theorem* commute.nsmul_right
- \+ *theorem* commute.nsmul_self
- \+ *theorem* commute.pow_left
- \+ *theorem* commute.pow_pow
- \+ *theorem* commute.pow_pow_self
- \+ *theorem* commute.pow_right
- \+ *theorem* commute.pow_self
- \+ *theorem* commute.self_gpow
- \+ *theorem* commute.self_gsmul
- \+ *theorem* commute.self_gsmul_gsmul
- \+ *theorem* commute.self_nsmul
- \+ *theorem* commute.self_nsmul_nsmul
- \+ *theorem* commute.self_pow
- \+ *lemma* commute.units_gpow_left
- \+ *lemma* commute.units_gpow_right
- \+/\- *theorem* gpow_one
- \+/\- *theorem* mul_gpow
- \+ *theorem* neg_pow
- \+/\- *theorem* pow_mul_comm'
- \+ *lemma* semiconj_by.gpow_right
- \+ *lemma* semiconj_by.gsmul_gsmul
- \+ *lemma* semiconj_by.gsmul_left
- \+ *lemma* semiconj_by.gsmul_right
- \+ *lemma* semiconj_by.nsmul_left
- \+ *lemma* semiconj_by.nsmul_nsmul
- \+ *lemma* semiconj_by.nsmul_right
- \+ *lemma* semiconj_by.pow_right
- \+ *lemma* semiconj_by.units_gpow_right
- \+ *lemma* units.conj_pow'
- \+ *lemma* units.conj_pow

Modified src/algebra/group_with_zero.lean
- \+ *theorem* commute.div_left
- \+ *theorem* commute.div_right
- \+ *theorem* commute.inv_inv'
- \+ *theorem* commute.inv_left'
- \+ *theorem* commute.inv_left_iff'
- \+ *theorem* commute.inv_right'
- \+ *theorem* commute.inv_right_iff'
- \- *theorem* inv_comm_of_comm'
- \+ *lemma* semiconj_by.div_right
- \+ *lemma* semiconj_by.inv_right'
- \+ *lemma* semiconj_by.inv_right_iff'
- \+ *lemma* semiconj_by.inv_symm_left'
- \+ *lemma* semiconj_by.inv_symm_left_iff'

Modified src/algebra/group_with_zero_power.lean
- \+ *theorem* commute.fpow_fpow
- \+ *theorem* commute.fpow_fpow_self
- \+ *theorem* commute.fpow_left
- \+ *theorem* commute.fpow_right
- \+ *theorem* commute.fpow_self
- \+ *lemma* commute.mul_fpow
- \+ *theorem* commute.self_fpow
- \- *theorem* fpow_mul_comm
- \+/\- *lemma* mul_fpow
- \+ *theorem* semiconj_by.fpow_right

Modified src/algebra/ring.lean
- \+ *theorem* commute.add_left
- \+ *theorem* commute.add_right
- \+ *theorem* commute.neg_left
- \+ *theorem* commute.neg_left_iff
- \+ *theorem* commute.neg_one_left
- \+ *theorem* commute.neg_one_right
- \+ *theorem* commute.neg_right
- \+ *theorem* commute.neg_right_iff
- \+ *theorem* commute.sub_left
- \+ *theorem* commute.sub_right
- \+ *theorem* commute.zero_left
- \+ *theorem* commute.zero_right
- \+ *lemma* semiconj_by.add_left
- \+ *lemma* semiconj_by.add_right
- \+ *lemma* semiconj_by.neg_left
- \+ *lemma* semiconj_by.neg_left_iff
- \+ *lemma* semiconj_by.neg_one_left
- \+ *lemma* semiconj_by.neg_one_right
- \+ *lemma* semiconj_by.neg_right
- \+ *lemma* semiconj_by.neg_right_iff
- \+ *lemma* semiconj_by.sub_left
- \+ *lemma* semiconj_by.sub_right
- \+ *lemma* semiconj_by.zero_left
- \+ *lemma* semiconj_by.zero_right

Deleted src/algebra/semiconj.lean
- \- *lemma* semiconj_by.add_left
- \- *lemma* semiconj_by.add_right
- \- *lemma* semiconj_by.cast_nat_left
- \- *lemma* semiconj_by.cast_nat_right
- \- *lemma* semiconj_by.conj_mk
- \- *lemma* semiconj_by.finv_symm_left
- \- *lemma* semiconj_by.finv_symm_left_iff
- \- *lemma* semiconj_by.gpow_right
- \- *lemma* semiconj_by.gsmul_gsmul
- \- *lemma* semiconj_by.gsmul_left
- \- *lemma* semiconj_by.gsmul_right
- \- *lemma* semiconj_by.inv_inv_symm
- \- *lemma* semiconj_by.inv_inv_symm_iff
- \- *lemma* semiconj_by.inv_right
- \- *lemma* semiconj_by.inv_right_iff
- \- *lemma* semiconj_by.inv_symm_left
- \- *lemma* semiconj_by.inv_symm_left_iff
- \- *lemma* semiconj_by.mul_left
- \- *lemma* semiconj_by.mul_right
- \- *lemma* semiconj_by.neg_left
- \- *lemma* semiconj_by.neg_left_iff
- \- *lemma* semiconj_by.neg_one_left
- \- *lemma* semiconj_by.neg_one_right
- \- *lemma* semiconj_by.neg_right
- \- *lemma* semiconj_by.neg_right_iff
- \- *lemma* semiconj_by.nsmul_left
- \- *lemma* semiconj_by.nsmul_nsmul
- \- *lemma* semiconj_by.nsmul_right
- \- *lemma* semiconj_by.one_left
- \- *lemma* semiconj_by.one_right
- \- *lemma* semiconj_by.pow_right
- \- *lemma* semiconj_by.sub_left
- \- *lemma* semiconj_by.sub_right
- \- *theorem* semiconj_by.units_coe
- \- *theorem* semiconj_by.units_coe_iff
- \- *lemma* semiconj_by.units_gpow_right
- \- *lemma* semiconj_by.units_inv_right
- \- *lemma* semiconj_by.units_inv_right_iff
- \- *lemma* semiconj_by.units_inv_symm_left
- \- *lemma* semiconj_by.units_inv_symm_left_iff
- \- *theorem* semiconj_by.units_of_coe
- \- *lemma* semiconj_by.zero_left
- \- *lemma* semiconj_by.zero_right
- \- *def* semiconj_by
- \- *lemma* units.conj_pow'
- \- *lemma* units.conj_pow
- \- *lemma* units.mk_semiconj_by

Modified src/data/int/basic.lean
- \+ *lemma* int.cast_commute
- \+ *lemma* int.commute_cast
- \- *theorem* int.mul_cast_comm

Modified src/data/nat/cast.lean
- \+ *lemma* nat.cast_commute
- \+/\- *lemma* nat.coe_cast_ring_hom
- \+ *lemma* nat.commute_cast
- \- *theorem* nat.mul_cast_comm

Modified src/data/nat/choose.lean


Modified src/data/rat/cast.lean
- \+ *theorem* rat.cast_commute
- \+ *theorem* rat.commute_cast
- \- *theorem* rat.mul_cast_comm

Modified src/ring_theory/algebra.lean




## [2020-06-08 16:39:55](https://github.com/leanprover-community/mathlib/commit/2caf479)
feat(data/matrix/basic): add bit0, bit1 lemmas ([#2987](https://github.com/leanprover-community/mathlib/pull/2987))
Based on a conversation in
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Matrix.20equality.20by.20extensionality
we define simp lemmas for matrices represented by numerals.
This should result in better representation of scalar multiples of
 `one_val : matrix n n a`.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.bit0_apply_apply
- \+ *lemma* matrix.bit1_apply_apply



## [2020-06-08 15:06:15](https://github.com/leanprover-community/mathlib/commit/3ca4c27)
chore(algebra/ordered_ring): use le instead of ge ([#2986](https://github.com/leanprover-community/mathlib/pull/2986))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* le_of_mul_le_mul_left
- \+/\- *lemma* le_of_mul_le_mul_right
- \- *lemma* le_of_mul_le_of_ge_one
- \+ *lemma* le_of_mul_le_of_one_le
- \+/\- *lemma* lt_of_mul_lt_mul_left
- \+/\- *lemma* lt_of_mul_lt_mul_right
- \+/\- *lemma* mul_lt_mul'
- \+/\- *lemma* mul_neg_of_neg_of_pos
- \+/\- *lemma* mul_neg_of_pos_of_neg
- \+/\- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+/\- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* neg_one_lt_zero
- \+/\- *lemma* nonneg_le_nonneg_of_squares_le
- \+ *lemma* one_le_two
- \+/\- *lemma* one_lt_two
- \- *lemma* two_ge_one
- \- *lemma* two_gt_one
- \- *lemma* zero_gt_neg_one



## [2020-06-08 15:06:12](https://github.com/leanprover-community/mathlib/commit/47f7335)
feat(data/nat/digits): digits, and divisibility tests for Freek 85 ([#2686](https://github.com/leanprover-community/mathlib/pull/2686))
I couldn't quite believe how much low hanging fruit there is on Lean's attempt at Freek's list, and so took a moment to do surely the lowest of the low...
This provides `digits b n`, which extracts the digits of a natural number `n` with respect to a base `b`, and `of_digits b L`, which reconstitutes a number from its digits, proves a few simple facts about these functions, and proves the usual divisibility by 3, 9, and 11 tests.
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* dvd_iff_dvd_of_dvd_sub
- \+ *lemma* dvd_mul_sub_mul

Modified src/data/fintype/card.lean
- \+ *lemma* list.alternating_prod_eq_finset_prod
- \+ *lemma* list.alternating_sum_eq_finset_sum

Modified src/data/int/basic.lean
- \+/\- *theorem* int.nat_cast_eq_coe_nat

Modified src/data/list/basic.lean
- \+ *lemma* list.alternating_prod_cons_cons
- \+ *lemma* list.alternating_prod_nil
- \+ *lemma* list.alternating_prod_singleton
- \+ *lemma* list.alternating_sum_cons_cons

Modified src/data/list/defs.lean
- \+ *def* list.alternating_prod
- \+ *def* list.alternating_sum

Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_lt_self'

Added src/data/nat/digits.lean
- \+ *lemma* coe_int_of_digits
- \+ *lemma* coe_of_digits
- \+ *def* digits
- \+ *lemma* digits_add
- \+ *lemma* digits_add_two_add_one
- \+ *def* digits_aux
- \+ *def* digits_aux_0
- \+ *def* digits_aux_1
- \+ *lemma* digits_aux_def
- \+ *lemma* digits_aux_zero
- \+ *lemma* digits_of_digits
- \+ *lemma* digits_of_lt
- \+ *lemma* digits_one_succ
- \+ *lemma* digits_zero
- \+ *lemma* digits_zero_of_eq_zero
- \+ *lemma* dvd_iff_dvd_digits_sum
- \+ *lemma* dvd_iff_dvd_of_digits
- \+ *lemma* dvd_of_digits_sub_of_digits
- \+ *lemma* eleven_dvd_iff
- \+ *lemma* modeq_digits_sum
- \+ *lemma* modeq_eleven_digits_sum
- \+ *lemma* modeq_nine_digits_sum
- \+ *lemma* modeq_three_digits_sum
- \+ *lemma* nine_dvd_iff
- \+ *def* of_digits
- \+ *lemma* of_digits_digits
- \+ *lemma* of_digits_eq_foldr
- \+ *lemma* of_digits_mod
- \+ *lemma* of_digits_modeq'
- \+ *lemma* of_digits_modeq
- \+ *lemma* of_digits_neg_one
- \+ *lemma* of_digits_one
- \+ *lemma* of_digits_one_cons
- \+ *lemma* of_digits_zmod
- \+ *lemma* of_digits_zmodeq'
- \+ *lemma* of_digits_zmodeq
- \+ *lemma* three_dvd_iff
- \+ *lemma* zmodeq_of_digits_digits



## [2020-06-08 13:54:41](https://github.com/leanprover-community/mathlib/commit/a793042)
feat(ring_theory/fractional_ideal): pushforward of fractional ideals ([#2984](https://github.com/leanprover-community/mathlib/pull/2984))
Extend `submodule.map` to fractional ideals by showing that the pushforward is also fractional.
For this, we need a slightly tweaked definition of fractional ideal: if we localize `R` at the submonoid `S`, the old definition required a nonzero `x : R` such that `xI ≤ R`, and the new definition requires `x ∈ S` instead. In the most common case, `S = non_zero_divisors R`, the results are exactly the same, and all operations are still the same.
A practical use of these pushforwards is included: `canonical_equiv` states fractional ideals don't depend on choice of localization map.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.coe_add_equiv_refl
- \+ *lemma* ring_equiv.coe_mul_equiv_refl
- \+ *lemma* ring_equiv.refl_apply
- \+ *lemma* ring_equiv.to_add_monoid_hom_refl
- \- *lemma* ring_equiv.to_fun_eq_coe
- \+ *lemma* ring_equiv.to_fun_eq_coe_fun
- \+ *lemma* ring_equiv.to_monoid_hom_refl
- \+ *lemma* ring_equiv.to_ring_hom_refl

Modified src/group_theory/submonoid.lean
- \+ *lemma* submonoid.map_id

Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_equiv.coe_refl
- \+ *lemma* alg_equiv.comp_symm
- \+ *lemma* alg_equiv.symm_comp

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* submodule.map_mul

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* ring.fractional_ideal.coe_add
- \+ *lemma* ring.fractional_ideal.coe_coe_ideal
- \+ *lemma* ring.fractional_ideal.coe_ideal_span_singleton
- \+ *lemma* ring.fractional_ideal.coe_inv_of_nonzero
- \+ *lemma* ring.fractional_ideal.coe_map
- \+ *lemma* ring.fractional_ideal.coe_mul
- \+ *lemma* ring.fractional_ideal.coe_ne_bot_iff_nonzero
- \+ *lemma* ring.fractional_ideal.coe_one
- \+/\- *lemma* ring.fractional_ideal.coe_span_singleton
- \+ *lemma* ring.fractional_ideal.coe_zero
- \+/\- *lemma* ring.fractional_ideal.eq_span_singleton_of_principal
- \+/\- *lemma* ring.fractional_ideal.ext
- \+ *lemma* ring.fractional_ideal.fractional_map
- \- *lemma* ring.fractional_ideal.invertible_of_principal
- \+ *lemma* ring.fractional_ideal.is_principal_iff
- \+ *def* ring.fractional_ideal.map
- \+ *lemma* ring.fractional_ideal.map_add
- \+ *lemma* ring.fractional_ideal.map_comp
- \+ *def* ring.fractional_ideal.map_equiv
- \+ *lemma* ring.fractional_ideal.map_equiv_apply
- \+ *lemma* ring.fractional_ideal.map_equiv_refl
- \+ *lemma* ring.fractional_ideal.map_id
- \+ *lemma* ring.fractional_ideal.map_mul
- \+/\- *lemma* ring.fractional_ideal.mem_singleton_mul
- \+ *lemma* ring.fractional_ideal.mul_generator_self_inv
- \- *lemma* ring.fractional_ideal.nonzero_iff_val_nonzero
- \+/\- *def* ring.fractional_ideal.span_singleton
- \+ *lemma* ring.fractional_ideal.span_singleton_eq_zero_iff
- \+/\- *lemma* ring.fractional_ideal.span_singleton_fractional
- \+/\- *lemma* ring.fractional_ideal.span_singleton_mul_span_singleton
- \+/\- *lemma* ring.fractional_ideal.span_singleton_one
- \+/\- *lemma* ring.fractional_ideal.span_singleton_zero
- \- *lemma* ring.fractional_ideal.val_add
- \- *lemma* ring.fractional_ideal.val_coe_ideal
- \+ *lemma* ring.fractional_ideal.val_eq_coe
- \- *lemma* ring.fractional_ideal.val_inv_of_nonzero
- \- *lemma* ring.fractional_ideal.val_mul
- \- *lemma* ring.fractional_ideal.val_one
- \- *lemma* ring.fractional_ideal.val_span_singleton
- \- *lemma* ring.fractional_ideal.val_zero



## [2020-06-08 07:55:43](https://github.com/leanprover-community/mathlib/commit/c360e01)
feat(ring/localization): add fraction map for int to rat cast ([#2921](https://github.com/leanprover-community/mathlib/pull/2921))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.mul_denom_eq_num
- \- *lemma* rat.mul_own_denom_eq_num

Modified src/ring_theory/localization.lean
- \+ *def* fraction_map.int.fraction_map



## [2020-06-08 07:00:32](https://github.com/leanprover-community/mathlib/commit/592f769)
feat(dynamics/circle): define translation number of a lift of a circle homeo ([#2974](https://github.com/leanprover-community/mathlib/pull/2974))
Define a structure `circle_deg1_lift`, a function `translation_number : circle_deg1_lift → ℝ`, and prove some basic properties
#### Estimated changes
Modified src/algebra/semiconj.lean
- \- *lemma* semiconj_by.units_conj_mk
- \+ *lemma* units.conj_pow'
- \+ *lemma* units.conj_pow
- \+ *lemma* units.mk_semiconj_by

Added src/dynamics/circle/rotation_number/translation_number.lean
- \+ *lemma* circle_deg1_lift.ceil_map_map_zero_le
- \+ *theorem* circle_deg1_lift.coe_inj
- \+ *lemma* circle_deg1_lift.coe_mk
- \+ *lemma* circle_deg1_lift.coe_mul
- \+ *lemma* circle_deg1_lift.coe_one
- \+ *lemma* circle_deg1_lift.coe_pow
- \+ *lemma* circle_deg1_lift.commute_add_int
- \+ *lemma* circle_deg1_lift.commute_add_nat
- \+ *lemma* circle_deg1_lift.commute_iff_commute
- \+ *lemma* circle_deg1_lift.commute_int_add
- \+ *lemma* circle_deg1_lift.commute_nat_add
- \+ *lemma* circle_deg1_lift.commute_sub_int
- \+ *lemma* circle_deg1_lift.commute_sub_nat
- \+ *lemma* circle_deg1_lift.continuous_pow
- \+ *lemma* circle_deg1_lift.dist_map_map_zero_lt
- \+ *lemma* circle_deg1_lift.dist_map_zero_lt_of_semiconj
- \+ *lemma* circle_deg1_lift.dist_map_zero_lt_of_semiconj_by
- \+ *lemma* circle_deg1_lift.dist_map_zero_translation_number_le
- \+ *lemma* circle_deg1_lift.dist_pow_map_zero_mul_translation_number_le
- \+ *lemma* circle_deg1_lift.exists_eq_add_translation_number
- \+ *theorem* circle_deg1_lift.ext
- \+ *theorem* circle_deg1_lift.ext_iff
- \+ *lemma* circle_deg1_lift.floor_map_map_zero_le
- \+ *lemma* circle_deg1_lift.floor_sub_le_translation_number
- \+ *lemma* circle_deg1_lift.forall_map_sub_of_Icc
- \+ *lemma* circle_deg1_lift.inf_apply
- \+ *lemma* circle_deg1_lift.iterate_eq_of_map_eq_add_int
- \+ *lemma* circle_deg1_lift.iterate_le_of_map_le_add_int
- \+ *lemma* circle_deg1_lift.iterate_mono
- \+ *lemma* circle_deg1_lift.iterate_monotone
- \+ *lemma* circle_deg1_lift.iterate_pos_eq_iff
- \+ *lemma* circle_deg1_lift.iterate_pos_le_iff
- \+ *lemma* circle_deg1_lift.iterate_pos_lt_iff
- \+ *lemma* circle_deg1_lift.le_ceil_map_map_zero
- \+ *lemma* circle_deg1_lift.le_floor_map_map_zero
- \+ *lemma* circle_deg1_lift.le_iterate_of_add_int_le_map
- \+ *lemma* circle_deg1_lift.le_iterate_pos_iff
- \+ *lemma* circle_deg1_lift.le_map_map_zero
- \+ *lemma* circle_deg1_lift.le_map_of_map_zero
- \+ *lemma* circle_deg1_lift.le_translation_number_of_add_int_le
- \+ *lemma* circle_deg1_lift.le_translation_number_of_add_le
- \+ *lemma* circle_deg1_lift.le_translation_number_of_add_nat_le
- \+ *lemma* circle_deg1_lift.lt_iterate_pos_iff
- \+ *lemma* circle_deg1_lift.lt_map_map_zero
- \+ *lemma* circle_deg1_lift.lt_map_of_int_lt_translation_number
- \+ *lemma* circle_deg1_lift.lt_map_of_nat_lt_translation_number
- \+ *lemma* circle_deg1_lift.lt_translation_number_of_forall_add_lt
- \+ *lemma* circle_deg1_lift.map_add_int
- \+ *lemma* circle_deg1_lift.map_add_nat
- \+ *lemma* circle_deg1_lift.map_add_one
- \+ *lemma* circle_deg1_lift.map_fract_sub_fract_eq
- \+ *lemma* circle_deg1_lift.map_int_add
- \+ *lemma* circle_deg1_lift.map_int_of_map_zero
- \+ *lemma* circle_deg1_lift.map_le_of_map_zero
- \+ *lemma* circle_deg1_lift.map_lt_of_translation_number_lt_int
- \+ *lemma* circle_deg1_lift.map_lt_of_translation_number_lt_nat
- \+ *lemma* circle_deg1_lift.map_map_zero_le
- \+ *lemma* circle_deg1_lift.map_map_zero_lt
- \+ *lemma* circle_deg1_lift.map_nat_add
- \+ *lemma* circle_deg1_lift.map_one_add
- \+ *lemma* circle_deg1_lift.map_sub_int
- \+ *lemma* circle_deg1_lift.map_sub_nat
- \+ *lemma* circle_deg1_lift.mono
- \+ *lemma* circle_deg1_lift.mul_apply
- \+ *lemma* circle_deg1_lift.mul_floor_map_zero_le_floor_iterate_zero
- \+ *lemma* circle_deg1_lift.pow_mono
- \+ *lemma* circle_deg1_lift.pow_monotone
- \+ *lemma* circle_deg1_lift.semiconj_by_iff_semiconj
- \+ *lemma* circle_deg1_lift.sup_apply
- \+ *lemma* circle_deg1_lift.tendsto_translation_number'
- \+ *lemma* circle_deg1_lift.tendsto_translation_number
- \+ *lemma* circle_deg1_lift.tendsto_translation_number_aux
- \+ *lemma* circle_deg1_lift.tendsto_translation_number_of_dist_bounded_aux
- \+ *lemma* circle_deg1_lift.tendsto_translation_number₀'
- \+ *lemma* circle_deg1_lift.tendsto_translation_number₀
- \+ *def* circle_deg1_lift.translate
- \+ *lemma* circle_deg1_lift.translate_apply
- \+ *lemma* circle_deg1_lift.translate_gpow
- \+ *lemma* circle_deg1_lift.translate_inv_apply
- \+ *lemma* circle_deg1_lift.translate_iterate
- \+ *lemma* circle_deg1_lift.translate_pow
- \+ *def* circle_deg1_lift.translation_number
- \+ *lemma* circle_deg1_lift.translation_number_conj_eq'
- \+ *lemma* circle_deg1_lift.translation_number_conj_eq
- \+ *lemma* circle_deg1_lift.translation_number_eq_int_iff
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_dist_bounded
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_semiconj
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_semiconj_by
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_tendsto_aux
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_tendsto₀'
- \+ *lemma* circle_deg1_lift.translation_number_eq_of_tendsto₀
- \+ *lemma* circle_deg1_lift.translation_number_eq_rat_iff
- \+ *lemma* circle_deg1_lift.translation_number_le_ceil_sub
- \+ *lemma* circle_deg1_lift.translation_number_le_of_le_add
- \+ *lemma* circle_deg1_lift.translation_number_le_of_le_add_int
- \+ *lemma* circle_deg1_lift.translation_number_le_of_le_add_nat
- \+ *lemma* circle_deg1_lift.translation_number_lt_of_forall_lt_add
- \+ *lemma* circle_deg1_lift.translation_number_map_id
- \+ *lemma* circle_deg1_lift.translation_number_mono
- \+ *lemma* circle_deg1_lift.translation_number_mul_of_commute
- \+ *lemma* circle_deg1_lift.translation_number_of_eq_add_int
- \+ *lemma* circle_deg1_lift.translation_number_of_map_pow_eq_add_int
- \+ *lemma* circle_deg1_lift.translation_number_pow
- \+ *lemma* circle_deg1_lift.translation_number_translate
- \+ *def* circle_deg1_lift.transnum_aux_seq
- \+ *lemma* circle_deg1_lift.transnum_aux_seq_def
- \+ *lemma* circle_deg1_lift.transnum_aux_seq_dist_lt
- \+ *lemma* circle_deg1_lift.transnum_aux_seq_zero
- \+ *lemma* circle_deg1_lift.units_coe
- \+ *structure* circle_deg1_lift



## [2020-06-07 17:42:45](https://github.com/leanprover-community/mathlib/commit/edd0209)
ci(deploy_docs.sh): generalize for use in doc-gen CI ([#2978](https://github.com/leanprover-community/mathlib/pull/2978))
This moves some installation steps out of `deploy_docs.sh` script and makes it accept several path arguments so that it can be re-used in the CI for `doc-gen`. 
The associated `doc-gen` PR: https://github.com/leanprover-community/doc-gen/pull/27 will be updated after this is merged.
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/deploy_docs.sh




## [2020-06-07 16:14:35](https://github.com/leanprover-community/mathlib/commit/be21b9a)
fix(data/nat/basic): use protected attribute ([#2976](https://github.com/leanprover-community/mathlib/pull/2976))
#### Estimated changes
Modified src/data/nat/basic.lean




## [2020-06-07 11:42:06](https://github.com/leanprover-community/mathlib/commit/516d9b5)
chore(scripts): update nolints.txt ([#2975](https://github.com/leanprover-community/mathlib/pull/2975))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-07 09:39:31](https://github.com/leanprover-community/mathlib/commit/a7f0069)
chore(algebra/ring): fix docs, `def`/`lemma` ([#2972](https://github.com/leanprover-community/mathlib/pull/2972))
#### Estimated changes
Modified src/algebra/ring.lean
- \- *def* add_mul
- \- *def* mul_add
- \- *def* mul_sub
- \- *def* sub_mul

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_tsum_le_tsum_norm



## [2020-06-07 04:23:17](https://github.com/leanprover-community/mathlib/commit/16ad1b4)
chore(topology/basic): remove unneeded `mk_protected` ([#2971](https://github.com/leanprover-community/mathlib/pull/2971))
It was already fixed by adding `@[protect_proj]`.
#### Estimated changes
Modified src/topology/basic.lean




## [2020-06-07 03:29:48](https://github.com/leanprover-community/mathlib/commit/b59f777)
feat(category_theory/eq_to_hom): functor extensionality using heq ([#2712](https://github.com/leanprover-community/mathlib/pull/2712))
Used in https://github.com/rwbarton/lean-homotopy-theory.
Also proves `faithful.div_comp`, but using it would create an import loop
so for now I just leave a comment.
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.functor.hext

Modified src/category_theory/fully_faithful.lean




## [2020-06-06 20:56:40](https://github.com/leanprover-community/mathlib/commit/2a36d25)
chore(analysis/normed_space/mazur_ulam): add `to_affine_map` ([#2963](https://github.com/leanprover-community/mathlib/pull/2963))
#### Estimated changes
Modified src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* isometric.coe_to_affine_map
- \+ *def* isometric.to_affine_map

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_map.coe_mk'
- \+ *def* affine_map.mk'
- \+ *lemma* affine_map.mk'_linear



## [2020-06-06 18:14:53](https://github.com/leanprover-community/mathlib/commit/a44c9a1)
chore(*): protect some definitions to get rid of _root_ ([#2846](https://github.com/leanprover-community/mathlib/pull/2846))
These were amongst the worst offenders.
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/computability/primrec.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/basic.lean


Modified src/data/monoid_algebra.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/choose.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pnat/basic.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/cau_seq.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/multiplicity.lean


Modified src/topology/basic.lean


Modified test/ring_exp.lean




## [2020-06-06 17:40:41](https://github.com/leanprover-community/mathlib/commit/e48c2af)
feat(data/padics/padic_norm): New padic_val_nat convenience functions ([#2970](https://github.com/leanprover-community/mathlib/pull/2970))
Convenience functions to allow us to deal either with the p-adic valuation or with multiplicity in the naturals, depending on what is locally convenient.
#### Estimated changes
Modified src/data/padics/padic_norm.lean
- \+ *def* padic_val_rat.padic_val_nat
- \+ *lemma* padic_val_rat.padic_val_nat_def
- \+ *lemma* padic_val_rat.padic_val_rat_of_nat
- \+ *lemma* padic_val_rat.zero_le_padic_val_rat_of_nat



## [2020-06-06 17:40:39](https://github.com/leanprover-community/mathlib/commit/589bdb9)
feat(number_theory/lucas_lehmer): prime (2^127 - 1) ([#2842](https://github.com/leanprover-community/mathlib/pull/2842))
This PR
1. proves the sufficiency of the Lucas-Lehmer test for Mersenne primes
2. provides a tactic that uses `norm_num` to do each step of the calculation of Lucas-Lehmer residues
3. proves 2^127 - 1 = 170141183460469231731687303715884105727 is prime
It doesn't
1. prove the necessity of the Lucas-Lehmer test (mathlib certainly has the necessary material if someone wants to do this)
2. use the trick `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]` that is essential to calculating Lucas-Lehmer residues quickly
3. manage to prove any "computer era" primes are prime! (Although my guess is that 2^521 - 1 would run in <1 day with the current implementation.)
I think using "the trick" is very plausible, and would be a fun project for someone who wanted to experiment with certified/fast arithmetic in Lean. It likely would make much larger Mersenne primes accessible.
This is a tidy-up and completion of work started by a student, Ainsley Pahljina.
#### Estimated changes
Added archive/examples/mersenne_primes.lean


Modified src/data/nat/parity.lean
- \+ *lemma* nat.two_not_dvd_two_mul_add_one
- \+ *lemma* nat.two_not_dvd_two_mul_sub_one

Added src/number_theory/lucas_lehmer.lean
- \+ *lemma* lucas_lehmer.X.X_card
- \+ *lemma* lucas_lehmer.X.add_fst
- \+ *lemma* lucas_lehmer.X.add_snd
- \+ *lemma* lucas_lehmer.X.bit0_fst
- \+ *lemma* lucas_lehmer.X.bit0_snd
- \+ *lemma* lucas_lehmer.X.bit1_fst
- \+ *lemma* lucas_lehmer.X.bit1_snd
- \+ *lemma* lucas_lehmer.X.closed_form
- \+ *lemma* lucas_lehmer.X.coe_mul
- \+ *lemma* lucas_lehmer.X.coe_nat
- \+ *lemma* lucas_lehmer.X.ext
- \+ *lemma* lucas_lehmer.X.int_coe_fst
- \+ *lemma* lucas_lehmer.X.int_coe_snd
- \+ *lemma* lucas_lehmer.X.left_distrib
- \+ *lemma* lucas_lehmer.X.mul_fst
- \+ *lemma* lucas_lehmer.X.mul_snd
- \+ *lemma* lucas_lehmer.X.nat_coe_fst
- \+ *lemma* lucas_lehmer.X.nat_coe_snd
- \+ *lemma* lucas_lehmer.X.neg_fst
- \+ *lemma* lucas_lehmer.X.neg_snd
- \+ *lemma* lucas_lehmer.X.one_fst
- \+ *lemma* lucas_lehmer.X.one_snd
- \+ *lemma* lucas_lehmer.X.right_distrib
- \+ *lemma* lucas_lehmer.X.units_card
- \+ *def* lucas_lehmer.X.ω
- \+ *lemma* lucas_lehmer.X.ω_mul_ωb
- \+ *def* lucas_lehmer.X.ωb
- \+ *lemma* lucas_lehmer.X.ωb_mul_ω
- \+ *def* lucas_lehmer.X
- \+ *lemma* lucas_lehmer.int.coe_nat_pow_pred
- \+ *lemma* lucas_lehmer.int.coe_nat_two_pow_pred
- \+ *def* lucas_lehmer.lucas_lehmer_residue
- \+ *def* lucas_lehmer.lucas_lehmer_test
- \+ *theorem* lucas_lehmer.mersenne_coe_X
- \+ *lemma* lucas_lehmer.mersenne_int_ne_zero
- \+ *lemma* lucas_lehmer.order_ineq
- \+ *theorem* lucas_lehmer.order_ω
- \+ *def* lucas_lehmer.q
- \+ *lemma* lucas_lehmer.residue_eq_zero_iff_s_mod_eq_zero
- \+ *def* lucas_lehmer.s
- \+ *def* lucas_lehmer.s_mod
- \+ *lemma* lucas_lehmer.s_mod_lt
- \+ *lemma* lucas_lehmer.s_mod_mod
- \+ *lemma* lucas_lehmer.s_mod_nonneg
- \+ *lemma* lucas_lehmer.s_mod_succ
- \+ *def* lucas_lehmer.s_zmod
- \+ *lemma* lucas_lehmer.s_zmod_eq_s
- \+ *lemma* lucas_lehmer.s_zmod_eq_s_mod
- \+ *lemma* lucas_lehmer.two_lt_q
- \+ *theorem* lucas_lehmer.ω_pow_eq_neg_one
- \+ *theorem* lucas_lehmer.ω_pow_eq_one
- \+ *theorem* lucas_lehmer.ω_pow_formula
- \+ *def* lucas_lehmer.ω_unit
- \+ *lemma* lucas_lehmer.ω_unit_coe
- \+ *theorem* lucas_lehmer_sufficiency
- \+ *def* mersenne
- \+ *lemma* mersenne_pos
- \+ *lemma* modeq_mersenne



## [2020-06-06 15:39:02](https://github.com/leanprover-community/mathlib/commit/ed5f636)
chore(algebra/group_with_zero_power): review ([#2966](https://github.com/leanprover-community/mathlib/pull/2966))
List of changes:
* Rename `gpow_neg_succ` to `gpow_neg_succ_of_nat` to match other names in `int` namespace.
* Add `units.coe_gpow`.
* Remove `fpow_neg_succ`, leave `fpow_neg_succ_of_nat`.
* Rewrite the proof of `fpow_add` in the same way I rewrote the proof of `gpow_add`.
* Make argument `a` implicit in some lemmas because they have an argument `ha : a ≠ 0`.
* Remove `fpow_inv`. This was a copy of `fpow_neg_one` with a misleading name.
* Remove `unit_pow` in favor of a more general `units.coe_pow`.
* Remove `unit_gpow`, add a more general `units.coe_gpow'` instead.
#### Estimated changes
Modified src/algebra/commute.lean


Modified src/algebra/field_power.lean


Modified src/algebra/group_power.lean
- \- *theorem* gpow_neg_succ
- \+ *theorem* gpow_neg_succ_of_nat
- \- *theorem* gsmul_neg_succ
- \+ *theorem* gsmul_neg_succ_of_nat
- \+ *lemma* units.coe_gpow

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* fpow_add
- \- *theorem* fpow_add
- \+ *lemma* fpow_add_one
- \- *theorem* fpow_add_one
- \- *lemma* fpow_inv
- \- *theorem* fpow_neg_succ
- \+ *theorem* fpow_neg_succ_of_nat
- \- *lemma* fpow_neg_succ_of_nat
- \+/\- *theorem* fpow_one_add
- \+ *lemma* fpow_sub_one
- \- *lemma* unit_gpow
- \- *lemma* unit_pow
- \+ *lemma* units.coe_gpow'

Modified src/algebra/semiconj.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean




## [2020-06-06 15:05:30](https://github.com/leanprover-community/mathlib/commit/2f028a8)
feat(analysis/convex/specific_functions): convexity of rpow ([#2965](https://github.com/leanprover-community/mathlib/pull/2965))
The function `x -> x^p` is convex on `[0, +\infty)` when `p \ge 1`.
#### Estimated changes
Modified src/analysis/convex/specific_functions.lean
- \+ *lemma* convex_on_rpow

Modified src/analysis/special_functions/pow.lean




## [2020-06-06 13:23:11](https://github.com/leanprover-community/mathlib/commit/f096a74)
fix(tactic/ring_exp): `ring_exp` now recognizes that `2^(n+1+1) = 2 * 2^(n+1)` ([#2929](https://github.com/leanprover-community/mathlib/pull/2929))
[Zulip thread with bug report](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_exp.20needs.20ring).
The problem was a missing lemma so that `norm_num` could fire on `x^y` if `x` and `y` are coefficients.
#### Estimated changes
Modified src/tactic/ring_exp.lean
- \+ *lemma* tactic.ring_exp.pow_pf_c_c

Modified test/ring_exp.lean




## [2020-06-06 09:55:46](https://github.com/leanprover-community/mathlib/commit/6f27271)
fix(documentation): fix a typo in the readme ([#2969](https://github.com/leanprover-community/mathlib/pull/2969))
#### Estimated changes
Modified README.md




## [2020-06-06 08:01:08](https://github.com/leanprover-community/mathlib/commit/d1ae307)
chore(algebra/ordered_group): add `exists_pos_add_of_lt` ([#2967](https://github.com/leanprover-community/mathlib/pull/2967))
Also drop `protected` on `_root_.zero_lt_iff_ne_zero`.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* exists_pos_add_of_lt
- \+ *lemma* zero_lt_iff_ne_zero



## [2020-06-06 07:15:17](https://github.com/leanprover-community/mathlib/commit/d18061f)
chore(algebra/add_torsor): a few more lemmas and implicit args ([#2964](https://github.com/leanprover-community/mathlib/pull/2964))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_action.vadd_left_cancel_iff
- \+ *lemma* add_torsor.vadd_right_cancel_iff

Modified src/linear_algebra/affine_space.lean




## [2020-06-05 16:16:43](https://github.com/leanprover-community/mathlib/commit/1b2048d)
feat(analysis/special_functions/pow): rpow is differentiable ([#2930](https://github.com/leanprover-community/mathlib/pull/2930))
Differentiability of the real power function `x ↦ x^p`. Also register the lemmas about the composition with a function to make sure that the simplifier can handle automatically the differentiability of `x ↦ (f x)^p` and more complicated expressions involving powers.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean
- \+ *lemma* has_deriv_at_interval_right_endpoint_of_tendsto_deriv
- \+ *lemma* has_deriv_at_of_has_deriv_at_of_ne
- \- *lemma* has_fderiv_at_interval_right_endpoint_of_tendsto_deriv

Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.exp_log_of_neg

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* complex.cpow_neg_one
- \+ *lemma* deriv_rpow
- \+ *lemma* deriv_rpow_of_one_le
- \+ *lemma* deriv_sqrt
- \+ *lemma* deriv_within_rpow
- \+ *lemma* deriv_within_rpow_of_one_le
- \+ *lemma* deriv_within_sqrt
- \+ *lemma* differentiable.rpow
- \+ *lemma* differentiable.rpow_of_one_le
- \+ *lemma* differentiable.sqrt
- \+ *lemma* differentiable_at.rpow
- \+ *lemma* differentiable_at.rpow_of_one_le
- \+ *lemma* differentiable_at.sqrt
- \+ *lemma* differentiable_on.rpow
- \+ *lemma* differentiable_on.rpow_of_one_le
- \+ *lemma* differentiable_on.sqrt
- \+ *lemma* differentiable_within_at.rpow
- \+ *lemma* differentiable_within_at.rpow_of_one_le
- \+ *lemma* differentiable_within_at.sqrt
- \+ *lemma* has_deriv_at.rpow
- \+ *lemma* has_deriv_at.rpow_of_one_le
- \+ *lemma* has_deriv_at.sqrt
- \+ *lemma* has_deriv_within_at.rpow
- \+ *lemma* has_deriv_within_at.rpow_of_one_le
- \+ *lemma* has_deriv_within_at.sqrt
- \+ *lemma* real.has_deriv_at_rpow
- \+ *lemma* real.has_deriv_at_rpow_of_neg
- \+ *lemma* real.has_deriv_at_rpow_of_one_le
- \+ *lemma* real.has_deriv_at_rpow_of_pos
- \+ *lemma* real.has_deriv_at_rpow_zero_of_one_le
- \+ *lemma* real.le_rpow_add
- \+ *lemma* real.rpow_add'
- \+/\- *lemma* real.rpow_add
- \+ *lemma* real.rpow_neg_one
- \+ *lemma* real.zero_rpow_le_one
- \+ *lemma* real.zero_rpow_nonneg



## [2020-06-05 13:39:37](https://github.com/leanprover-community/mathlib/commit/5c851bd)
fix(tactic/squeeze_simp): make `squeeze_simp [←...]` work ([#2961](https://github.com/leanprover-community/mathlib/pull/2961))
`squeeze_simp` parses the argument list using a function in core Lean, and when support for backwards arguments was added to `simp`, it used a new function to parse the additional structure. This PR fixes the TODO left in the code to switch `squeeze_simp` to the new function by deleting the code that needed it - it wasn't used anyway!
To add a test for the fix, I moved the single existing `squeeze_simp` test from the deprecated file `examples.lean` to a new file.
#### Estimated changes
Modified src/tactic/squeeze.lean


Modified test/examples.lean


Added test/squeeze.lean




## [2020-06-05 11:58:53](https://github.com/leanprover-community/mathlib/commit/a433eb0)
feat(analysis/special_functions/pow): real powers on ennreal ([#2951](https://github.com/leanprover-community/mathlib/pull/2951))
Real powers of extended nonnegative real numbers. We develop an API based on that of real powers of reals and nnreals, proving the corresponding lemmas.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* ennreal.coe_mul_rpow
- \+ *lemma* ennreal.coe_rpow_of_ne_zero
- \+ *lemma* ennreal.coe_rpow_of_nonneg
- \+ *lemma* ennreal.mul_rpow_of_ne_top
- \+ *lemma* ennreal.mul_rpow_of_ne_zero
- \+ *lemma* ennreal.one_le_rpow
- \+ *lemma* ennreal.one_lt_rpow
- \+ *lemma* ennreal.one_rpow
- \+ *lemma* ennreal.rpow_add
- \+ *lemma* ennreal.rpow_eq_pow
- \+ *lemma* ennreal.rpow_eq_top_iff
- \+ *lemma* ennreal.rpow_eq_zero_iff
- \+ *lemma* ennreal.rpow_le_one
- \+ *lemma* ennreal.rpow_le_rpow
- \+ *lemma* ennreal.rpow_le_rpow_of_exponent_ge
- \+ *lemma* ennreal.rpow_le_rpow_of_exponent_le
- \+ *lemma* ennreal.rpow_lt_one
- \+ *lemma* ennreal.rpow_lt_rpow
- \+ *lemma* ennreal.rpow_lt_rpow_of_exponent_gt
- \+ *lemma* ennreal.rpow_lt_rpow_of_exponent_lt
- \+ *lemma* ennreal.rpow_mul
- \+ *lemma* ennreal.rpow_nat_cast
- \+ *lemma* ennreal.rpow_neg
- \+ *lemma* ennreal.rpow_neg_one
- \+ *lemma* ennreal.rpow_one
- \+ *lemma* ennreal.rpow_zero
- \+ *lemma* ennreal.top_rpow_def
- \+ *lemma* ennreal.top_rpow_of_neg
- \+ *lemma* ennreal.top_rpow_of_pos
- \+ *lemma* ennreal.zero_rpow_def
- \+ *lemma* ennreal.zero_rpow_of_neg
- \+ *lemma* ennreal.zero_rpow_of_pos
- \+/\- *lemma* nnreal.rpow_add
- \+/\- *lemma* nnreal.rpow_le_one
- \+/\- *lemma* real.rpow_le_one



## [2020-06-05 10:41:53](https://github.com/leanprover-community/mathlib/commit/fd623d6)
feat(data/set/intervals/image_preimage): new file ([#2958](https://github.com/leanprover-community/mathlib/pull/2958))
* Create a file for lemmas like
  `(λ x, x + a) '' Icc b c = Icc (b + a) (b + c)`.
* Prove lemmas about images and preimages of all intervals under
  `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x`.
* Move lemmas about multiplication from `basic`.
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/data/set/intervals/basic.lean
- \- *lemma* set.image_add_left_Icc
- \- *lemma* set.image_add_right_Icc
- \- *lemma* set.image_mul_left_Icc'
- \- *lemma* set.image_mul_left_Icc
- \- *lemma* set.image_mul_right_Icc'
- \- *lemma* set.image_mul_right_Icc
- \- *lemma* set.image_neg_Iic
- \- *lemma* set.image_neg_Iio

Added src/data/set/intervals/image_preimage.lean
- \+ *lemma* set.image_add_const_Icc
- \+ *lemma* set.image_add_const_Ici
- \+ *lemma* set.image_add_const_Ico
- \+ *lemma* set.image_add_const_Iic
- \+ *lemma* set.image_add_const_Iio
- \+ *lemma* set.image_add_const_Ioc
- \+ *lemma* set.image_add_const_Ioi
- \+ *lemma* set.image_add_const_Ioo
- \+ *lemma* set.image_const_add_Icc
- \+ *lemma* set.image_const_add_Ici
- \+ *lemma* set.image_const_add_Ico
- \+ *lemma* set.image_const_add_Iic
- \+ *lemma* set.image_const_add_Iio
- \+ *lemma* set.image_const_add_Ioc
- \+ *lemma* set.image_const_add_Ioi
- \+ *lemma* set.image_const_add_Ioo
- \+ *lemma* set.image_const_sub_Icc
- \+ *lemma* set.image_const_sub_Ici
- \+ *lemma* set.image_const_sub_Ico
- \+ *lemma* set.image_const_sub_Iic
- \+ *lemma* set.image_const_sub_Iio
- \+ *lemma* set.image_const_sub_Ioc
- \+ *lemma* set.image_const_sub_Ioi
- \+ *lemma* set.image_const_sub_Ioo
- \+ *lemma* set.image_mul_left_Icc'
- \+ *lemma* set.image_mul_left_Icc
- \+ *lemma* set.image_mul_right_Icc'
- \+ *lemma* set.image_mul_right_Icc
- \+ *lemma* set.image_neg_Icc
- \+ *lemma* set.image_neg_Ici
- \+ *lemma* set.image_neg_Ico
- \+ *lemma* set.image_neg_Iic
- \+ *lemma* set.image_neg_Iio
- \+ *lemma* set.image_neg_Ioc
- \+ *lemma* set.image_neg_Ioi
- \+ *lemma* set.image_neg_Ioo
- \+ *lemma* set.image_sub_const_Icc
- \+ *lemma* set.image_sub_const_Ici
- \+ *lemma* set.image_sub_const_Ico
- \+ *lemma* set.image_sub_const_Iic
- \+ *lemma* set.image_sub_const_Iio
- \+ *lemma* set.image_sub_const_Ioc
- \+ *lemma* set.image_sub_const_Ioi
- \+ *lemma* set.image_sub_const_Ioo
- \+ *lemma* set.preimage_add_const_Icc
- \+ *lemma* set.preimage_add_const_Ici
- \+ *lemma* set.preimage_add_const_Ico
- \+ *lemma* set.preimage_add_const_Iic
- \+ *lemma* set.preimage_add_const_Iio
- \+ *lemma* set.preimage_add_const_Ioc
- \+ *lemma* set.preimage_add_const_Ioi
- \+ *lemma* set.preimage_add_const_Ioo
- \+ *lemma* set.preimage_const_add_Icc
- \+ *lemma* set.preimage_const_add_Ici
- \+ *lemma* set.preimage_const_add_Ico
- \+ *lemma* set.preimage_const_add_Iic
- \+ *lemma* set.preimage_const_add_Iio
- \+ *lemma* set.preimage_const_add_Ioc
- \+ *lemma* set.preimage_const_add_Ioi
- \+ *lemma* set.preimage_const_add_Ioo
- \+ *lemma* set.preimage_const_sub_Icc
- \+ *lemma* set.preimage_const_sub_Ici
- \+ *lemma* set.preimage_const_sub_Ico
- \+ *lemma* set.preimage_const_sub_Iic
- \+ *lemma* set.preimage_const_sub_Iio
- \+ *lemma* set.preimage_const_sub_Ioc
- \+ *lemma* set.preimage_const_sub_Ioi
- \+ *lemma* set.preimage_const_sub_Ioo
- \+ *lemma* set.preimage_neg_Icc
- \+ *lemma* set.preimage_neg_Ici
- \+ *lemma* set.preimage_neg_Ico
- \+ *lemma* set.preimage_neg_Iic
- \+ *lemma* set.preimage_neg_Iio
- \+ *lemma* set.preimage_neg_Ioc
- \+ *lemma* set.preimage_neg_Ioi
- \+ *lemma* set.preimage_neg_Ioo
- \+ *lemma* set.preimage_sub_const_Icc
- \+ *lemma* set.preimage_sub_const_Ici
- \+ *lemma* set.preimage_sub_const_Ico
- \+ *lemma* set.preimage_sub_const_Iic
- \+ *lemma* set.preimage_sub_const_Iio
- \+ *lemma* set.preimage_sub_const_Ioc
- \+ *lemma* set.preimage_sub_const_Ioi
- \+ *lemma* set.preimage_sub_const_Ioo



## [2020-06-05 10:10:03](https://github.com/leanprover-community/mathlib/commit/1ef65c9)
feat(linear_algebra/quadratic_form): more constructions for quadratic forms ([#2949](https://github.com/leanprover-community/mathlib/pull/2949))
Define multiplication of two linear forms to give a quadratic form and addition of quadratic forms. With these definitions, we can write a generic binary quadratic form as `a • proj R₁ 0 0 + b • proj R₁ 0 1 + c • proj R₁ 1 1 : quadratic_form R₁ (fin 2 → R₁)`.
In order to prove the linearity conditions on the constructions, there are new `simp` lemmas `polar_add_left`, `polar_smul_left`, `polar_add_right` and `polar_smul_right` copying from the corresponding fields of the `quadratic_form` structure, that use `⇑ Q` instead of `Q.to_fun`. The original field names have a `'` appended to avoid name clashes.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *def* bilin_form.lin_mul_lin
- \+ *lemma* bilin_form.lin_mul_lin_apply
- \+ *lemma* bilin_form.lin_mul_lin_comp
- \+ *lemma* bilin_form.lin_mul_lin_comp_left
- \+ *lemma* bilin_form.lin_mul_lin_comp_right

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* quadratic_form.add_apply
- \+ *lemma* quadratic_form.add_lin_mul_lin
- \+/\- *def* quadratic_form.associated
- \+ *lemma* quadratic_form.associated_lin_mul_lin
- \- *lemma* quadratic_form.associated_smul
- \+ *lemma* quadratic_form.coe_fn_add
- \+ *lemma* quadratic_form.coe_fn_neg
- \+ *lemma* quadratic_form.coe_fn_smul
- \+/\- *lemma* quadratic_form.discr_smul
- \+ *def* quadratic_form.lin_mul_lin
- \+ *lemma* quadratic_form.lin_mul_lin_add
- \+ *lemma* quadratic_form.lin_mul_lin_apply
- \+ *lemma* quadratic_form.lin_mul_lin_comp
- \+ *lemma* quadratic_form.lin_mul_lin_self_pos_def
- \+ *def* quadratic_form.mk_left
- \+ *lemma* quadratic_form.neg_apply
- \+/\- *def* quadratic_form.polar
- \+ *lemma* quadratic_form.polar_add
- \+ *lemma* quadratic_form.polar_add_left
- \+ *lemma* quadratic_form.polar_add_right
- \+ *lemma* quadratic_form.polar_comm
- \+ *lemma* quadratic_form.polar_neg
- \+ *lemma* quadratic_form.polar_smul
- \+ *lemma* quadratic_form.polar_smul_left
- \+ *lemma* quadratic_form.polar_smul_right
- \+ *lemma* quadratic_form.pos_def.add
- \+ *lemma* quadratic_form.pos_def.smul
- \+ *def* quadratic_form.proj
- \+ *lemma* quadratic_form.proj_apply
- \+/\- *lemma* quadratic_form.smul_apply
- \- *lemma* quadratic_form.smul_pos_def_of_nonzero
- \- *lemma* quadratic_form.smul_pos_def_of_smul_nonzero
- \+ *lemma* quadratic_form.zero_apply



## [2020-06-05 08:41:12](https://github.com/leanprover-community/mathlib/commit/31ceb62)
feat(data/int|nat/basic): add `add_monoid_hom.ext_nat/int` ([#2957](https://github.com/leanprover-community/mathlib/pull/2957))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.eq_on_inv

Modified src/algebra/group_power.lean


Modified src/data/int/basic.lean
- \+/\- *theorem* add_monoid_hom.eq_int_cast
- \+ *theorem* add_monoid_hom.eq_int_cast_hom
- \+ *theorem* add_monoid_hom.ext_int
- \+ *def* int.cast_add_hom
- \+ *lemma* int.coe_cast_add_hom

Modified src/data/nat/cast.lean
- \+/\- *lemma* add_monoid_hom.eq_nat_cast
- \+ *lemma* add_monoid_hom.ext_nat
- \+/\- *theorem* nat.abs_cast
- \+/\- *theorem* nat.cast_bit0
- \+/\- *theorem* nat.cast_bit1
- \+/\- *theorem* nat.cast_max
- \+/\- *theorem* nat.cast_min
- \+/\- *theorem* nat.cast_pred
- \+/\- *theorem* nat.cast_sub
- \+/\- *lemma* nat.coe_cast_add_monoid_hom
- \+/\- *lemma* ring_hom.eq_nat_cast
- \+/\- *lemma* ring_hom.ext_nat
- \+/\- *lemma* ring_hom.map_nat_cast



## [2020-06-05 08:41:10](https://github.com/leanprover-community/mathlib/commit/edb4422)
feat(algebra/add_torsor): add `equiv.const_vadd` and `equiv.vadd_const` ([#2907](https://github.com/leanprover-community/mathlib/pull/2907))
Also define their `isometric.*` versions in `analysis/normed_space/add_torsor`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* add_torsor.vadd_vsub_vadd_cancel_left
- \+ *lemma* add_torsor.vadd_vsub_vadd_cancel_right
- \+ *lemma* add_torsor.vsub_sub_vsub_cancel_left
- \+ *lemma* add_torsor.vsub_sub_vsub_cancel_right
- \- *lemma* add_torsor.vsub_sub_vsub_left_cancel
- \- *lemma* add_torsor.vsub_sub_vsub_right_cancel
- \+ *lemma* equiv.coe_const_vadd
- \+ *lemma* equiv.coe_vadd_const
- \+ *lemma* equiv.coe_vadd_const_symm
- \+ *def* equiv.const_vadd
- \+ *lemma* equiv.const_vadd_add
- \+ *def* equiv.const_vadd_hom
- \+ *lemma* equiv.const_vadd_zero
- \+ *def* equiv.vadd_const

Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_vadd_cancel_left
- \+ *lemma* dist_vadd_cancel_right
- \+ *lemma* isometric.coe_const_vadd
- \+ *lemma* isometric.coe_vadd_const
- \+ *lemma* isometric.coe_vadd_const_symm
- \+ *def* isometric.const_vadd
- \+ *lemma* isometric.const_vadd_zero
- \+ *def* isometric.vadd_const
- \+ *lemma* isometric.vadd_const_to_equiv



## [2020-06-05 07:28:47](https://github.com/leanprover-community/mathlib/commit/a130c73)
feat(topology/algebra/ordered): list of preconnected sets ([#2943](https://github.com/leanprover-community/mathlib/pull/2943))
A subset of a densely ordered conditionally complete lattice (e.g., `ℝ`) with order topology is preconnected if and only if it is one of the intervals.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.diff_compl
- \+ *lemma* set.diff_diff_cancel_left
- \+ *lemma* set.diff_diff_right
- \+ *lemma* set.diff_inter
- \+/\- *lemma* set.mem_diff_singleton
- \+ *lemma* set.subset_diff_singleton

Modified src/data/set/intervals/basic.lean
- \- *lemma* set.Icc_diff_Ico_eq_singleton
- \+ *lemma* set.Icc_diff_Ico_same
- \- *lemma* set.Icc_diff_Ioc_eq_singleton
- \+ *lemma* set.Icc_diff_Ioc_same
- \+ *lemma* set.Icc_diff_Ioo_same
- \+ *lemma* set.Icc_diff_both
- \+ *lemma* set.Icc_diff_left
- \+ *lemma* set.Icc_diff_right
- \+ *lemma* set.Ici_diff_Ioi_same
- \+ *lemma* set.Ici_diff_left
- \- *lemma* set.Ico_diff_Ioo_eq_singleton
- \+ *lemma* set.Ico_diff_Ioo_same
- \+ *lemma* set.Ico_diff_left
- \+ *lemma* set.Iic_diff_Iio_same
- \+ *lemma* set.Iic_diff_right
- \+ *lemma* set.Iio_union_right
- \- *lemma* set.Ioc_diff_Ioo_eq_singleton
- \+ *lemma* set.Ioc_diff_Ioo_same
- \+ *lemma* set.Ioc_diff_right
- \+ *lemma* set.Ioi_union_left
- \+ *lemma* set.mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
- \+ *lemma* set.mem_Ici_Ioi_of_subset_of_subset
- \+ *lemma* set.mem_Iic_Iio_of_subset_of_subset

Modified src/order/bounds.lean
- \+ *lemma* nonempty_of_not_bdd_above
- \+ *lemma* nonempty_of_not_bdd_below
- \+ *lemma* not_bdd_above_iff'
- \+ *lemma* not_bdd_above_iff
- \+ *lemma* not_bdd_below_iff'
- \+ *lemma* not_bdd_below_iff

Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* cInf_mem_closure
- \+/\- *lemma* cInf_mem_of_is_closed
- \+/\- *lemma* cSup_mem_closure
- \+/\- *lemma* cSup_mem_of_is_closed
- \+ *lemma* is_connected.Ioo_cInf_cSup_subset
- \+ *lemma* is_glb.nhds_within_ne_bot
- \+ *lemma* is_lub.nhds_within_ne_bot
- \+ *lemma* is_preconnected.Icc_subset
- \+ *lemma* is_preconnected.Iio_cSup_subset
- \+ *lemma* is_preconnected.Ioi_cInf_subset
- \+ *lemma* is_preconnected.eq_univ_of_unbounded
- \- *lemma* is_preconnected.forall_Icc_subset
- \+ *lemma* is_preconnected.mem_intervals
- \+/\- *lemma* mem_closure_of_is_glb
- \+/\- *lemma* mem_closure_of_is_lub
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \- *lemma* nhds_principal_ne_bot_of_is_glb
- \- *lemma* nhds_principal_ne_bot_of_is_lub
- \+ *lemma* set_of_is_preconnected_eq_of_ordered
- \+ *lemma* set_of_is_preconnected_subset_of_ordered

Modified src/topology/subset_properties.lean




## [2020-06-05 05:31:21](https://github.com/leanprover-community/mathlib/commit/8f89bd8)
chore(algebra/group_power): simplify a proof ([#2955](https://github.com/leanprover-community/mathlib/pull/2955))
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* gpow_add
- \- *theorem* gpow_add
- \+ *lemma* gpow_add_one
- \- *theorem* gpow_add_one
- \+/\- *theorem* gpow_mul
- \+ *lemma* gpow_sub
- \+ *lemma* gpow_sub_one
- \+ *lemma* sub_gsmul



## [2020-06-05 05:31:19](https://github.com/leanprover-community/mathlib/commit/d7fa405)
chore(algebra/*): merge `inv_inv''` with `inv_inv'` ([#2954](https://github.com/leanprover-community/mathlib/pull/2954))
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* inv_inv'

Modified src/algebra/group_with_zero.lean
- \- *lemma* inv_inv''
- \+ *lemma* inv_inv'

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/pointwise.lean




## [2020-06-05 05:31:17](https://github.com/leanprover-community/mathlib/commit/8161888)
feat(group_theory/subgroup): define normal bundled subgroups ([#2947](https://github.com/leanprover-community/mathlib/pull/2947))
Most proofs are adapted from `deprecated/subgroup`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.sub_mem
- \+ *lemma* monoid_hom.normal_ker
- \- *lemma* monoid_hom.rang_top_of_surjective
- \+ *lemma* monoid_hom.range_top_of_surjective
- \+ *lemma* subgroup.bot_normal
- \+ *def* subgroup.center
- \+ *lemma* subgroup.center_normal
- \+/\- *lemma* subgroup.coe_inv
- \+ *lemma* subgroup.coe_mk
- \+ *lemma* subgroup.le_normalizer
- \+ *lemma* subgroup.le_normalizer_of_normal
- \+ *lemma* subgroup.mem_center_iff
- \+ *lemma* subgroup.mem_normalizer_iff
- \+ *lemma* subgroup.mul_mem_cancel_left
- \+ *lemma* subgroup.mul_mem_cancel_right
- \+ *lemma* subgroup.normal.conj_mem
- \+ *lemma* subgroup.normal.mem_comm
- \+ *lemma* subgroup.normal.mem_comm_iff
- \+ *lemma* subgroup.normal_in_normalizer
- \+ *lemma* subgroup.normal_of_comm
- \+ *def* subgroup.normalizer



## [2020-06-05 05:31:15](https://github.com/leanprover-community/mathlib/commit/2131382)
feat(data/setoid/partition): some lemmas about partitions ([#2937](https://github.com/leanprover-community/mathlib/pull/2937))
#### Estimated changes
Modified src/data/setoid/partition.lean
- \+ *lemma* setoid.is_partition.pairwise_disjoint
- \+ *lemma* setoid.is_partition.sUnion_eq_univ
- \+ *lemma* setoid.is_partition_classes



## [2020-06-05 04:53:19](https://github.com/leanprover-community/mathlib/commit/80a52e9)
chore(analysis/convex/basic): add `finset.convex_hull_eq` ([#2956](https://github.com/leanprover-community/mathlib/pull/2956))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* finset.convex_hull_eq



## [2020-06-04 18:38:01](https://github.com/leanprover-community/mathlib/commit/2ceb7f7)
feat(analysis/convex): preparatory statement for caratheodory ([#2944](https://github.com/leanprover-community/mathlib/pull/2944))
Proves
```lean
lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t
```
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_hull_eq_union_convex_hull_finite_subsets
- \+ *lemma* convex_hull_singleton



## [2020-06-04 18:05:52](https://github.com/leanprover-community/mathlib/commit/beb5d45)
chore(scripts): update nolints.txt ([#2952](https://github.com/leanprover-community/mathlib/pull/2952))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-04 16:18:37](https://github.com/leanprover-community/mathlib/commit/1a29796)
chore(is_ring_hom): remove some uses of is_ring_hom ([#2884](https://github.com/leanprover-community/mathlib/pull/2884))
This PR deletes the definitions `is_ring_anti_hom` and `ring_anti_equiv`, in favour of using the bundled `R →+* Rᵒᵖ` and `R ≃+* Rᵒᵖ`. It also changes the definition of `ring_invo`.
This is work towards removing the deprecated `is_*_hom` family.
#### Estimated changes
Modified src/algebra/opposites.lean
- \+ *lemma* opposite.op_eq_one_iff
- \+ *lemma* opposite.op_eq_zero_iff
- \+ *lemma* opposite.unop_eq_one_iff
- \+ *lemma* opposite.unop_eq_zero_iff

Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.to_fun_apply

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.to_fun_eq_coe
- \+ *def* ring_equiv.to_opposite
- \+ *lemma* ring_equiv.to_opposite_apply
- \+ *lemma* ring_equiv.to_opposite_symm_apply

Modified src/data/opposite.lean
- \+ *def* opposite.equiv_to_opposite
- \+ *lemma* opposite.equiv_to_opposite_apply
- \+ *lemma* opposite.equiv_to_opposite_symm_apply

Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* sesq_form.neg_left
- \+/\- *lemma* sesq_form.neg_right
- \+/\- *lemma* sesq_form.smul_right
- \+/\- *lemma* sesq_form.zero_left
- \+/\- *lemma* sesq_form.zero_right
- \+/\- *structure* sesq_form
- \+/\- *lemma* sym_sesq_form.is_refl
- \+/\- *def* sym_sesq_form.is_sym
- \+/\- *lemma* sym_sesq_form.sym

Modified src/ring_theory/maps.lean
- \- *def* comm_ring.anti_equiv_to_equiv
- \- *theorem* comm_ring.anti_hom_to_hom
- \- *def* comm_ring.equiv_to_anti_equiv
- \- *theorem* comm_ring.hom_to_anti_hom
- \- *lemma* is_ring_anti_hom.map_neg
- \- *lemma* is_ring_anti_hom.map_sub
- \- *lemma* is_ring_anti_hom.map_zero
- \- *lemma* ring_anti_equiv.bijective
- \- *lemma* ring_anti_equiv.map_add
- \- *lemma* ring_anti_equiv.map_mul
- \- *lemma* ring_anti_equiv.map_neg
- \- *lemma* ring_anti_equiv.map_neg_one
- \- *lemma* ring_anti_equiv.map_one
- \- *lemma* ring_anti_equiv.map_sub
- \- *lemma* ring_anti_equiv.map_zero
- \- *lemma* ring_anti_equiv.map_zero_iff
- \- *structure* ring_anti_equiv
- \- *lemma* ring_equiv.bijective
- \- *lemma* ring_equiv.map_zero_iff
- \- *lemma* ring_invo.bijective
- \+ *lemma* ring_invo.coe_ring_equiv
- \- *lemma* ring_invo.map_add
- \+ *lemma* ring_invo.map_eq_zero_iff
- \- *lemma* ring_invo.map_mul
- \- *lemma* ring_invo.map_neg
- \- *lemma* ring_invo.map_neg_one
- \- *lemma* ring_invo.map_one
- \- *lemma* ring_invo.map_sub
- \- *lemma* ring_invo.map_zero
- \- *lemma* ring_invo.map_zero_iff
- \+ *def* ring_invo.mk'
- \+ *lemma* ring_invo.to_fun_eq_coe
- \- *def* ring_invo.to_ring_anti_equiv
- \+/\- *structure* ring_invo

Modified src/topology/algebra/uniform_ring.lean
- \+ *def* uniform_space.completion.coe_ring_hom
- \+ *def* uniform_space.completion.extension_hom
- \+ *def* uniform_space.completion.map_ring_hom



## [2020-06-04 15:38:26](https://github.com/leanprover-community/mathlib/commit/7d803a9)
feat(topology/metric_space/isometry): group structure on isometries ([#2950](https://github.com/leanprover-community/mathlib/pull/2950))
Closes [#2908](https://github.com/leanprover-community/mathlib/pull/2908)
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.apply_inv_self
- \+ *lemma* isometric.coe_mul
- \+ *lemma* isometric.coe_one
- \+ *lemma* isometric.inv_apply_self
- \+ *lemma* isometric.mul_apply



## [2020-06-04 15:38:24](https://github.com/leanprover-community/mathlib/commit/add0c9a)
feat(ring/localization): add construction of localization as a quotient type ([#2922](https://github.com/leanprover-community/mathlib/pull/2922))
#### Estimated changes
Modified src/group_theory/congruence.lean


Modified src/group_theory/monoid_localization.lean
- \+ *theorem* localization.ind
- \+ *theorem* localization.induction_on
- \+ *theorem* localization.induction_on₂
- \+ *theorem* localization.induction_on₃
- \+ *def* localization.mk
- \+ *lemma* localization.mk_eq_monoid_of_mk'
- \+ *lemma* localization.mk_eq_monoid_of_mk'_apply
- \+ *lemma* localization.mk_one_eq_monoid_of_mk
- \+ *def* localization.monoid_of
- \+ *lemma* localization.mul_equiv_of_quotient_apply
- \+ *lemma* localization.mul_equiv_of_quotient_mk'
- \+ *lemma* localization.mul_equiv_of_quotient_mk
- \+ *lemma* localization.mul_equiv_of_quotient_monoid_of
- \+ *lemma* localization.mul_equiv_of_quotient_symm_mk'
- \+ *lemma* localization.mul_equiv_of_quotient_symm_mk
- \+ *lemma* localization.mul_equiv_of_quotient_symm_monoid_of
- \+ *lemma* localization.one_rel
- \+ *def* localization.r'
- \+ *def* localization.r
- \+ *theorem* localization.r_eq_r'
- \+ *lemma* localization.r_iff_exists
- \+ *theorem* localization.r_of_eq
- \+ *def* localization
- \- *def* submonoid.localization.r'
- \- *def* submonoid.localization.r
- \- *theorem* submonoid.localization.r_eq_r'
- \- *lemma* submonoid.localization.r_iff_exists
- \- *def* submonoid.localization

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+/\- *def* fraction_map
- \- *def* localization.codomain
- \- *lemma* localization.epic_of_localization_map
- \- *lemma* localization.eq_iff_eq
- \- *lemma* localization.eq_iff_exists
- \- *theorem* localization.eq_mk'_iff_mul_eq
- \- *lemma* localization.eq_of_eq
- \- *lemma* localization.eq_zero_of_fst_eq_zero
- \- *lemma* localization.exists_integer_multiple'
- \- *lemma* localization.exists_integer_multiple
- \- *lemma* localization.ext
- \- *lemma* localization.ext_iff
- \- *def* localization.is_integer
- \- *lemma* localization.is_integer_add
- \- *lemma* localization.is_integer_mul
- \- *lemma* localization.is_integer_smul
- \- *lemma* localization.is_unit_comp
- \- *lemma* localization.lift_comp
- \- *lemma* localization.lift_eq
- \- *lemma* localization.lift_eq_iff
- \- *lemma* localization.lift_id
- \- *lemma* localization.lift_injective_iff
- \- *lemma* localization.lift_left_inverse
- \- *lemma* localization.lift_mk'
- \- *lemma* localization.lift_mk'_spec
- \- *lemma* localization.lift_of_comp
- \- *lemma* localization.lift_surjective_iff
- \- *lemma* localization.lift_unique
- \- *def* localization.lin_coe
- \- *lemma* localization.lin_coe_apply
- \- *lemma* localization.map_comp
- \- *lemma* localization.map_comp_map
- \- *lemma* localization.map_eq
- \- *lemma* localization.map_id
- \- *lemma* localization.map_left_cancel
- \- *lemma* localization.map_map
- \- *lemma* localization.map_mk'
- \- *lemma* localization.map_right_cancel
- \- *lemma* localization.map_units
- \- *lemma* localization.mem_coe
- \- *lemma* localization.mk'_add
- \- *lemma* localization.mk'_eq_iff_eq
- \- *theorem* localization.mk'_eq_iff_eq_mul
- \- *lemma* localization.mk'_eq_iff_mk'_eq
- \- *lemma* localization.mk'_eq_mul_mk'_one
- \- *lemma* localization.mk'_eq_of_eq
- \- *lemma* localization.mk'_mul
- \- *lemma* localization.mk'_mul_cancel_left
- \- *lemma* localization.mk'_mul_cancel_right
- \- *lemma* localization.mk'_one
- \- *lemma* localization.mk'_sec
- \- *lemma* localization.mk'_self''
- \- *lemma* localization.mk'_self'
- \- *lemma* localization.mk'_self
- \- *lemma* localization.mk'_spec'
- \- *lemma* localization.mk'_spec
- \+ *lemma* localization.mk_eq_mk'
- \+ *lemma* localization.mk_eq_mk'_apply
- \+ *lemma* localization.mk_one_eq_of
- \+ *lemma* localization.monoid_of_eq_of
- \- *lemma* localization.mul_mk'_eq_mk'_of_mul
- \+ *def* localization.of
- \- *lemma* localization.of_id
- \+ *lemma* localization.ring_equiv_of_quotient_apply
- \+ *lemma* localization.ring_equiv_of_quotient_mk'
- \+ *lemma* localization.ring_equiv_of_quotient_mk
- \+ *lemma* localization.ring_equiv_of_quotient_of
- \+ *lemma* localization.ring_equiv_of_quotient_symm_mk'
- \+ *lemma* localization.ring_equiv_of_quotient_symm_mk
- \+ *lemma* localization.ring_equiv_of_quotient_symm_of
- \- *lemma* localization.ring_equiv_of_ring_equiv_eq
- \- *lemma* localization.ring_equiv_of_ring_equiv_eq_map
- \- *lemma* localization.ring_equiv_of_ring_equiv_eq_map_apply
- \- *lemma* localization.ring_equiv_of_ring_equiv_mk'
- \- *lemma* localization.sec_spec'
- \- *lemma* localization.sec_spec
- \- *lemma* localization.surj
- \- *abbreviation* localization.to_map
- \- *lemma* localization.to_map_injective
- \- *structure* localization
- \+ *def* localization_map.codomain
- \+ *lemma* localization_map.epic_of_localization_map
- \+ *lemma* localization_map.eq_iff_eq
- \+ *lemma* localization_map.eq_iff_exists
- \+ *theorem* localization_map.eq_mk'_iff_mul_eq
- \+ *lemma* localization_map.eq_of_eq
- \+ *lemma* localization_map.eq_zero_of_fst_eq_zero
- \+ *lemma* localization_map.exists_integer_multiple'
- \+ *lemma* localization_map.exists_integer_multiple
- \+ *lemma* localization_map.ext
- \+ *lemma* localization_map.ext_iff
- \+ *def* localization_map.is_integer
- \+ *lemma* localization_map.is_integer_add
- \+ *lemma* localization_map.is_integer_mul
- \+ *lemma* localization_map.is_integer_smul
- \+ *lemma* localization_map.is_unit_comp
- \+ *lemma* localization_map.lift_comp
- \+ *lemma* localization_map.lift_eq
- \+ *lemma* localization_map.lift_eq_iff
- \+ *lemma* localization_map.lift_id
- \+ *lemma* localization_map.lift_injective_iff
- \+ *lemma* localization_map.lift_left_inverse
- \+ *lemma* localization_map.lift_mk'
- \+ *lemma* localization_map.lift_mk'_spec
- \+ *lemma* localization_map.lift_of_comp
- \+ *lemma* localization_map.lift_surjective_iff
- \+ *lemma* localization_map.lift_unique
- \+ *def* localization_map.lin_coe
- \+ *lemma* localization_map.lin_coe_apply
- \+ *lemma* localization_map.map_comp
- \+ *lemma* localization_map.map_comp_map
- \+ *lemma* localization_map.map_eq
- \+ *lemma* localization_map.map_id
- \+ *lemma* localization_map.map_left_cancel
- \+ *lemma* localization_map.map_map
- \+ *lemma* localization_map.map_mk'
- \+ *lemma* localization_map.map_right_cancel
- \+ *lemma* localization_map.map_units
- \+ *lemma* localization_map.mem_coe
- \+ *lemma* localization_map.mk'_add
- \+ *lemma* localization_map.mk'_eq_iff_eq
- \+ *theorem* localization_map.mk'_eq_iff_eq_mul
- \+ *lemma* localization_map.mk'_eq_iff_mk'_eq
- \+ *lemma* localization_map.mk'_eq_mul_mk'_one
- \+ *lemma* localization_map.mk'_eq_of_eq
- \+ *lemma* localization_map.mk'_mul
- \+ *lemma* localization_map.mk'_mul_cancel_left
- \+ *lemma* localization_map.mk'_mul_cancel_right
- \+ *lemma* localization_map.mk'_one
- \+ *lemma* localization_map.mk'_sec
- \+ *lemma* localization_map.mk'_self''
- \+ *lemma* localization_map.mk'_self'
- \+ *lemma* localization_map.mk'_self
- \+ *lemma* localization_map.mk'_spec'
- \+ *lemma* localization_map.mk'_spec
- \+ *lemma* localization_map.mul_mk'_eq_mk'_of_mul
- \+ *lemma* localization_map.of_id
- \+ *lemma* localization_map.ring_equiv_of_ring_equiv_eq
- \+ *lemma* localization_map.ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* localization_map.ring_equiv_of_ring_equiv_eq_map_apply
- \+ *lemma* localization_map.ring_equiv_of_ring_equiv_mk'
- \+ *lemma* localization_map.sec_spec'
- \+ *lemma* localization_map.sec_spec
- \+ *lemma* localization_map.surj
- \+ *abbreviation* localization_map.to_map
- \+ *lemma* localization_map.to_map_injective
- \+ *structure* localization_map
- \- *def* ring_hom.to_localization
- \+ *def* ring_hom.to_localization_map
- \+ *def* submonoid.localization_map.to_ring_localization



## [2020-06-04 15:06:53](https://github.com/leanprover-community/mathlib/commit/2dbf550)
feat(ring_theory/eisenstein_criterion): Eisenstein's criterion ([#2946](https://github.com/leanprover-community/mathlib/pull/2946))
#### Estimated changes
Added src/ring_theory/eisenstein_criterion.lean
- \+ *lemma* polynomial.eisenstein_criterion_aux.eval_zero_mem_ideal_of_eq_mul_X_pow
- \+ *lemma* polynomial.eisenstein_criterion_aux.is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
- \+ *lemma* polynomial.eisenstein_criterion_aux.le_nat_degree_of_map_eq_mul_X_pow
- \+ *lemma* polynomial.eisenstein_criterion_aux.map_eq_C_mul_X_pow_of_forall_coeff_mem
- \+ *theorem* polynomial.irreducible_of_eisenstein_criterion

Added src/ring_theory/prime.lean
- \+ *lemma* mul_eq_mul_prime_pow
- \+ *lemma* mul_eq_mul_prime_prod



## [2020-06-04 14:28:44](https://github.com/leanprover-community/mathlib/commit/c2e78d2)
refactor(data/zmod): generalize zmod.cast_hom ([#2900](https://github.com/leanprover-community/mathlib/pull/2900))
Currently, `zmod.cast_hom` would cast `zmod n` to rings `R` of characteristic `n`.
This PR builds `cast_hom` for rings `R` with characteristic `m` that divides `n`.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_add'
- \+/\- *lemma* zmod.cast_add
- \+/\- *def* zmod.cast_hom
- \+/\- *lemma* zmod.cast_hom_apply
- \+ *lemma* zmod.cast_int_cast'
- \+/\- *lemma* zmod.cast_int_cast
- \+ *lemma* zmod.cast_mul'
- \+/\- *lemma* zmod.cast_mul
- \+ *lemma* zmod.cast_nat_cast'
- \+/\- *lemma* zmod.cast_nat_cast
- \+ *lemma* zmod.cast_one'
- \+/\- *lemma* zmod.cast_one
- \+ *lemma* zmod.cast_pow'
- \+ *lemma* zmod.cast_pow
- \+ *lemma* zmod.cast_sub'
- \+ *lemma* zmod.cast_sub

Modified src/field_theory/finite.lean


Modified src/linear_algebra/basis.lean




## [2020-06-04 07:22:09](https://github.com/leanprover-community/mathlib/commit/e397b4c)
chore(scripts): update nolints.txt ([#2948](https://github.com/leanprover-community/mathlib/pull/2948))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-04 04:42:31](https://github.com/leanprover-community/mathlib/commit/5744f89)
chore(*): fix some `ge_or_gt` lint issues ([#2945](https://github.com/leanprover-community/mathlib/pull/2945))
Also rename a few definitions:
* `ge_of_forall_ge_sub` : `le_of_forall_sub_le`;
* `power_series.order_ge_nat` : `power_series.nat_le_order`;
* `power_series.order_ge`: `power_series.le_order`;
#### Estimated changes
Modified src/algebra/ordered_field.lean
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \- *lemma* ge_of_forall_ge_sub
- \+ *lemma* le_of_forall_sub_le

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_pos_of_ne_zero
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* le_add_of_nonneg_left
- \+/\- *lemma* le_add_of_nonneg_right
- \+/\- *lemma* lt_add_of_pos_left
- \+/\- *lemma* lt_add_of_pos_right
- \+/\- *lemma* sub_le_self
- \+/\- *lemma* sub_lt_self

Modified src/analysis/normed_space/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/pi.lean
- \+/\- *lemma* real.pi_gt_sqrt_two_add_series
- \+/\- *lemma* real.sqrt_two_add_series_nonneg
- \+/\- *lemma* real.sqrt_two_add_series_zero_nonneg

Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/integration.lean


Modified src/number_theory/dioph.lean
- \+/\- *theorem* dioph.pell_dioph
- \+/\- *theorem* dioph.xn_dioph

Modified src/number_theory/pell.lean
- \+/\- *theorem* pell.d_pos
- \+/\- *theorem* pell.eq_of_xn_modeq'
- \+/\- *theorem* pell.eq_of_xn_modeq
- \+/\- *theorem* pell.eq_of_xn_modeq_le
- \+/\- *theorem* pell.eq_of_xn_modeq_lem3
- \+/\- *lemma* pell.eq_pell_lem
- \+/\- *lemma* pell.eq_pow_of_pell_lem
- \+/\- *theorem* pell.matiyasevic
- \+/\- *theorem* pell.modeq_of_xn_modeq
- \+/\- *theorem* pell.x_pos
- \+/\- *theorem* pell.xy_modeq_of_modeq

Modified src/order/complete_lattice.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean
- \+ *lemma* power_series.le_order
- \+ *lemma* power_series.le_order_add
- \+ *lemma* power_series.nat_le_order
- \- *lemma* power_series.order_add_ge
- \- *lemma* power_series.order_ge
- \- *lemma* power_series.order_ge_nat

Modified src/tactic/lint/misc.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* eq_of_forall_dist_le
- \+/\- *lemma* metric.diam_ball
- \+/\- *lemma* metric.diam_closed_ball
- \+/\- *theorem* metric.mem_ball_self
- \+/\- *theorem* metric.mem_closed_ball_self
- \+/\- *theorem* metric.pos_of_mem_ball

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* eq_of_forall_edist_le

Modified src/topology/uniform_space/absolute_value.lean




## [2020-06-03 16:19:29](https://github.com/leanprover-community/mathlib/commit/ef6d8d9)
refactor(analysis/specific_limits): prove `0 < r → (1+r)^n→∞` for semirings ([#2935](https://github.com/leanprover-community/mathlib/pull/2935))
* Add `add_one_pow_unbounded_of_pos` and
  `tendsto_add_one_pow_at_top_at_top_of_pos` assuming
  `[linear_ordered_semiring α]` `[archimedean α]`.
* Rename `tendsto_pow_at_top_at_top_of_gt_1` to
  `tendsto_pow_at_top_at_top_of_one_lt`, generalize to an archimedean
  ordered ring.
* Rename `tendsto_pow_at_top_at_top_of_gt_1_nat` to
  `nat.tendsto_pow_at_top_at_top_of_one_lt`.
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* add_one_pow_unbounded_of_pos
- \+/\- *lemma* pow_unbounded_of_one_lt

Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/specific_limits.lean
- \+ *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \+ *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat
- \+ *lemma* tendsto_pow_at_top_at_top_of_one_lt

Modified src/data/padics/hensel.lean




## [2020-06-03 15:11:28](https://github.com/leanprover-community/mathlib/commit/1adf204)
chore(scripts): update nolints.txt ([#2942](https://github.com/leanprover-community/mathlib/pull/2942))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-03 15:11:26](https://github.com/leanprover-community/mathlib/commit/494b43e)
chore(category_theory/limits/over): granularity in forget preserving colimits ([#2941](https://github.com/leanprover-community/mathlib/pull/2941))
a bit more granularity for instances about forget preserving colimits
#### Estimated changes
Modified src/category_theory/limits/over.lean




## [2020-06-03 15:11:24](https://github.com/leanprover-community/mathlib/commit/97265f9)
feat(category_theory/limits): dualise a limits result ([#2940](https://github.com/leanprover-community/mathlib/pull/2940))
Add the dual of `is_limit.of_cone_equiv`.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *def* category_theory.adjunction.of_left_adjoint
- \+ *def* category_theory.adjunction.of_right_adjoint

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_colimit.of_cocone_equiv
- \+/\- *def* category_theory.limits.is_limit.of_cone_equiv

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean
- \+ *def* category_theory.limits.preserves_colimit_of_iso



## [2020-06-03 13:41:29](https://github.com/leanprover-community/mathlib/commit/e205228)
feat(data/fintype/basic): to_finset_inj ([#2938](https://github.com/leanprover-community/mathlib/pull/2938))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* set.to_finset_inj



## [2020-06-03 13:41:27](https://github.com/leanprover-community/mathlib/commit/74037cb)
feat(topology/algebra/ordered): IVT for two functions ([#2933](https://github.com/leanprover-community/mathlib/pull/2933))
Also rename some `is_connected_I*` lemmas to `is_preconnected_I*`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* closure_le_eq
- \+/\- *lemma* closure_lt_subset_le
- \+/\- *lemma* intermediate_value_univ
- \+ *lemma* intermediate_value_univ₂
- \+ *lemma* is_closed.is_closed_le
- \- *lemma* is_connected_Icc
- \- *lemma* is_connected_Ioo
- \+ *lemma* is_preconnected.intermediate_value₂
- \+ *lemma* is_preconnected_Icc
- \+ *lemma* is_preconnected_Ioo
- \+/\- *lemma* tendsto_abs_at_top_at_top

Modified src/topology/subset_properties.lean
- \+/\- *theorem* is_preirreducible.is_preconnected



## [2020-06-03 13:41:25](https://github.com/leanprover-community/mathlib/commit/f44509c)
chore(tactic/localized): lower priority of bad decidability instances in classical locale ([#2932](https://github.com/leanprover-community/mathlib/pull/2932))
Also add a decidability instance for complex numbers.
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/monoid_algebra.2Emul_apply/near/199595932
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/slow.20elaboration/near/199543997
#### Estimated changes
Modified src/data/complex/basic.lean


Modified src/data/real/basic.lean


Modified src/measure_theory/indicator_function.lean
- \+/\- *lemma* tendsto_indicator_bUnion_finset
- \+/\- *lemma* tendsto_indicator_of_antimono
- \+/\- *lemma* tendsto_indicator_of_monotone

Modified src/tactic/localized.lean




## [2020-06-03 12:09:46](https://github.com/leanprover-community/mathlib/commit/ed91bb2)
feat(data/setoid/partition): sUnion _classes ([#2936](https://github.com/leanprover-community/mathlib/pull/2936))
#### Estimated changes
Modified src/data/setoid/partition.lean
- \+ *theorem* setoid.sUnion_classes



## [2020-06-03 12:09:44](https://github.com/leanprover-community/mathlib/commit/c3221f7)
feat(data/rat): denom_div_cast_eq_one_iff ([#2934](https://github.com/leanprover-community/mathlib/pull/2934))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.coe_int_inj
- \+ *lemma* rat.denom_div_cast_eq_one_iff



## [2020-06-03 12:09:43](https://github.com/leanprover-community/mathlib/commit/1f2102d)
chore(group_theory/group_action): protect_proj attribute for mul_action ([#2931](https://github.com/leanprover-community/mathlib/pull/2931))
#### Estimated changes
Modified src/group_theory/group_action.lean




## [2020-06-03 12:09:41](https://github.com/leanprover-community/mathlib/commit/687fc51)
ci(bors): set `cut_body_after` to `---` ([#2927](https://github.com/leanprover-community/mathlib/pull/2927))
#### Estimated changes
Added .github/PULL_REQUEST_TEMPLATE.md


Modified bors.toml




## [2020-06-03 12:09:39](https://github.com/leanprover-community/mathlib/commit/9fc2413)
feat(order/iterate): a few more lemmas about `f^[n]` ([#2925](https://github.com/leanprover-community/mathlib/pull/2925))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *theorem* ordering.compares_iff_of_compares_impl

Modified src/logic/function/iterate.lean
- \+/\- *theorem* function.iterate_id

Modified src/order/iterate.lean
- \+ *lemma* function.commute.iterate_pos_eq_iff_map_eq
- \+ *lemma* function.commute.iterate_pos_le_iff_map_le'
- \+ *lemma* function.commute.iterate_pos_le_iff_map_le
- \+ *lemma* monotone.iterate_ge_of_ge
- \+ *lemma* monotone.iterate_le_of_le



## [2020-06-03 12:09:37](https://github.com/leanprover-community/mathlib/commit/0ec9c0e)
feat(algebra/iterate_hom): add `mul_left_iterate` etc ([#2923](https://github.com/leanprover-community/mathlib/pull/2923))
#### Estimated changes
Modified src/algebra/iterate_hom.lean
- \+ *lemma* add_left_iterate
- \+ *lemma* add_right_iterate
- \+ *lemma* mul_left_iterate
- \+ *lemma* mul_right_iterate



## [2020-06-03 11:09:01](https://github.com/leanprover-community/mathlib/commit/8d9e541)
feat(group_theory/group_action): some lemmas about orbits ([#2928](https://github.com/leanprover-community/mathlib/pull/2928))
also remove the simp attribute unfolding the definition of orbit.
Depends on [#2924](https://github.com/leanprover-community/mathlib/pull/2924)
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+/\- *lemma* mul_action.mem_orbit_iff
- \+ *lemma* mul_action.mem_orbit_smul
- \+ *lemma* mul_action.smul_mem_orbit_smul



## [2020-06-03 09:28:49](https://github.com/leanprover-community/mathlib/commit/5020285)
chore(group_theory/group_action): simp attributes on inv_smul_smul and smul_inv_smul ([#2924](https://github.com/leanprover-community/mathlib/pull/2924))
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+/\- *lemma* mul_action.inv_smul_smul
- \+/\- *lemma* mul_action.smul_inv_smul



## [2020-06-03 07:59:41](https://github.com/leanprover-community/mathlib/commit/3904374)
chore(algebra/ordered_group)`: add `strict_mono.add_const/const_add` ([#2926](https://github.com/leanprover-community/mathlib/pull/2926))
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* strict_mono.add_const
- \+ *lemma* strict_mono.const_add



## [2020-06-03 06:31:17](https://github.com/leanprover-community/mathlib/commit/879bad2)
feat(analysis/normed_space/enorm): define extended norm ([#2897](https://github.com/leanprover-community/mathlib/pull/2897))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* nnnorm_eq_zero
- \+ *lemma* normed_field.nnnorm_inv
- \+ *lemma* normed_field.nnnorm_one
- \+ *lemma* real.nnnorm_coe_nat
- \+ *lemma* real.nnnorm_two
- \+ *lemma* real.norm_coe_nat
- \+/\- *lemma* real.norm_eq_abs
- \+/\- *lemma* real.norm_two

Added src/analysis/normed_space/enorm.lean
- \+ *lemma* enorm.coe_fn_injective
- \+ *lemma* enorm.coe_max
- \+ *def* enorm.emetric_space
- \+ *lemma* enorm.eq_zero_iff
- \+ *lemma* enorm.ext
- \+ *lemma* enorm.ext_iff
- \+ *lemma* enorm.finite_dist_eq
- \+ *lemma* enorm.finite_edist_eq
- \+ *lemma* enorm.finite_norm_eq
- \+ *def* enorm.finite_subspace
- \+ *lemma* enorm.map_add_le
- \+ *lemma* enorm.map_neg
- \+ *lemma* enorm.map_smul
- \+ *lemma* enorm.map_sub_le
- \+ *lemma* enorm.map_sub_rev
- \+ *lemma* enorm.map_zero
- \+ *lemma* enorm.max_map
- \+ *lemma* enorm.top_map
- \+ *structure* enorm



## [2020-06-02 21:15:28](https://github.com/leanprover-community/mathlib/commit/efae3d9)
feat(data/mv_polynomial): C_inj and C_injective ([#2920](https://github.com/leanprover-community/mathlib/pull/2920))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* mv_polynomial.C_inj
- \+ *lemma* mv_polynomial.C_injective



## [2020-06-02 19:58:24](https://github.com/leanprover-community/mathlib/commit/607286e)
feat(data/*): ring_hom.ext_{nat,int,rat,zmod} ([#2918](https://github.com/leanprover-community/mathlib/pull/2918))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* ring_hom.ext_int

Modified src/data/nat/cast.lean
- \+ *lemma* ring_hom.ext_nat

Modified src/data/rat/cast.lean
- \+ *lemma* ring_hom.ext_rat

Modified src/data/zmod/basic.lean
- \+ *lemma* ring_hom.ext_zmod



## [2020-06-02 17:27:51](https://github.com/leanprover-community/mathlib/commit/62ec2c5)
feat(linear_algebra/matrix): add alg_equiv_matrix ([#2919](https://github.com/leanprover-community/mathlib/pull/2919))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.arrow_congr_apply
- \+ *lemma* linear_equiv.arrow_congr_comp
- \+ *lemma* linear_equiv.conj_apply
- \+ *lemma* linear_equiv.conj_id

Modified src/linear_algebra/matrix.lean
- \+ *def* alg_equiv_matrix'
- \+ *def* alg_equiv_matrix
- \+ *def* linear_equiv.alg_conj



## [2020-06-02 07:41:15](https://github.com/leanprover-community/mathlib/commit/1a4de99)
feat(category_theory/limits) equalizer morphism is regular mono ([#2916](https://github.com/leanprover-community/mathlib/pull/2916))
The equalizer morphism is a regular mono, and its dual
#### Estimated changes
Modified src/category_theory/limits/shapes/regular_mono.lean




## [2020-06-02 06:13:44](https://github.com/leanprover-community/mathlib/commit/1494cc1)
feat(order/semiconj_Sup): use `Sup` to semiconjugate functions ([#2895](https://github.com/leanprover-community/mathlib/pull/2895))
Formalize two lemmas from a paper by É. Ghys.
#### Estimated changes
Modified docs/references.bib


Modified src/order/bounds.lean
- \+ *lemma* is_glb.mono
- \+ *lemma* is_greatest.mono
- \+ *lemma* is_least.mono
- \+ *lemma* is_lub.mono

Modified src/order/complete_lattice.lean


Added src/order/semiconj_Sup.lean
- \+ *lemma* function.Sup_div_semiconj
- \+ *lemma* function.cSup_div_semiconj
- \+ *lemma* function.semiconj.symm_adjoint
- \+ *lemma* function.semiconj_of_is_lub
- \+ *lemma* is_order_right_adjoint.right_mono
- \+ *lemma* is_order_right_adjoint.unique
- \+ *def* is_order_right_adjoint
- \+ *lemma* is_order_right_adjoint_Sup
- \+ *lemma* is_order_right_adjoint_cSup



## [2020-06-02 02:13:40](https://github.com/leanprover-community/mathlib/commit/4372d17)
chore(scripts): update nolints.txt ([#2914](https://github.com/leanprover-community/mathlib/pull/2914))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-02 00:43:24](https://github.com/leanprover-community/mathlib/commit/eb616cf)
chore(*): split long lines ([#2913](https://github.com/leanprover-community/mathlib/pull/2913))
#### Estimated changes
Modified docs/tutorial/category_theory/Ab.lean


Modified docs/tutorial/category_theory/intro.lean


Modified roadmap/topology/shrinking_lemma.lean


Modified src/data/equiv/encodable.lean


Modified src/data/equiv/list.lean
- \+/\- *theorem* encodable.length_sorted_univ

Modified src/data/equiv/local_equiv.lean


Modified src/data/fin_enum.lean
- \+/\- *lemma* fin_enum.finset.mem_enum
- \+/\- *lemma* fin_enum.mem_pi
- \+/\- *def* fin_enum.of_nodup_list
- \+/\- *lemma* fin_enum.pi.mem_enum
- \+/\- *def* fin_enum.pi

Modified src/data/finset.lean
- \+/\- *lemma* finset.coe_inter
- \+/\- *lemma* finset.coe_union
- \+/\- *lemma* finset.disjoint_filter_filter
- \+/\- *lemma* finset.exists_max_image
- \+/\- *lemma* finset.exists_min_image
- \+/\- *theorem* finset.fold_insert
- \+/\- *theorem* finset.image_to_finset
- \+/\- *theorem* finset.insert_union_distrib
- \+/\- *theorem* finset.mem_insert_of_mem
- \+/\- *theorem* finset.mem_of_mem_inter_left
- \+/\- *theorem* finset.mem_of_mem_inter_right
- \+/\- *theorem* finset.mem_union_left
- \+/\- *theorem* finset.mem_union_right
- \+/\- *def* finset.pi.cons
- \+/\- *lemma* finset.pi.cons_ne
- \+/\- *lemma* finset.pi.cons_same
- \+/\- *theorem* finset.sdiff_subset_sdiff
- \+/\- *theorem* finset.sigma_eq_bind

Modified src/data/int/basic.lean
- \+/\- *theorem* int.cast_eq_zero
- \+/\- *theorem* int.cast_inj
- \+/\- *theorem* int.coe_nat_bit0
- \+/\- *theorem* int.coe_nat_bit1
- \+/\- *theorem* int.coe_nat_inj'
- \+/\- *theorem* int.coe_nat_le
- \+/\- *theorem* int.coe_nat_lt
- \+/\- *lemma* int.shiftr_neg_succ
- \+/\- *lemma* int.test_bit_ldiff

Modified src/data/int/modeq.lean
- \+/\- *theorem* int.modeq.modeq_add_cancel_left
- \+/\- *theorem* int.modeq.modeq_add_cancel_right

Modified src/data/list/bag_inter.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* list.exists_of_mem_map
- \+/\- *theorem* list.map_subset_iff

Modified src/data/list/defs.lean
- \+/\- *def* list.split_on_p_aux

Modified src/data/list/forall2.lean
- \+/\- *lemma* list.forall₂_cons_left_iff

Modified src/data/list/func.lean
- \+/\- *lemma* list.func.pointwise_nil

Modified src/data/list/min_max.lean


Modified src/data/list/nodup.lean
- \+/\- *theorem* list.nodup_erase_eq_filter
- \+/\- *theorem* list.nodup_join
- \+/\- *theorem* list.nth_le_index_of

Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean
- \+/\- *theorem* list.length_permutations_aux
- \+/\- *theorem* list.permutations_aux2_snd_cons

Modified src/data/list/range.lean
- \+/\- *theorem* list.map_sub_range'

Modified src/data/list/zip.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pequiv.lean
- \+/\- *lemma* pequiv.single_trans_single

Modified src/data/pnat/basic.lean
- \+/\- *lemma* pnat.bit0_le_bit0
- \+/\- *lemma* pnat.bit0_le_bit1
- \+/\- *lemma* pnat.bit1_le_bit0
- \+/\- *lemma* pnat.bit1_le_bit1

Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.coeff_add
- \+/\- *lemma* polynomial.coeff_derivative
- \+/\- *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \+/\- *lemma* polynomial.coeff_sub
- \+/\- *lemma* polynomial.derivative_eval
- \+/\- *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval

Modified src/data/quot.lean
- \+/\- *lemma* quotient.lift_beta
- \+/\- *lemma* quotient.lift_on_beta

Modified src/data/rat/basic.lean


Modified src/data/real/cau_seq.lean
- \+/\- *theorem* cau_seq.const_inv

Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.of_real_le_of_real_iff
- \+/\- *lemma* ennreal.of_real_lt_of_real_iff

Modified src/data/real/nnreal.lean


Modified src/data/seq/computation.lean
- \+/\- *theorem* computation.destruct_map

Modified src/data/seq/wseq.lean
- \+/\- *theorem* wseq.destruct_flatten
- \+/\- *theorem* wseq.destruct_terminates_of_nth_terminates
- \+/\- *theorem* wseq.head_terminates_of_nth_terminates
- \+/\- *theorem* wseq.nth_terminates_le

Modified src/data/ulift.lean
- \+/\- *lemma* plift.rec.constant
- \+/\- *lemma* ulift.rec.constant

Modified src/data/zmod/basic.lean


Modified src/deprecated/group.lean


Modified src/logic/relation.lean
- \+/\- *lemma* relation.equivalence_join
- \+/\- *lemma* relation.refl_trans_gen.trans
- \+/\- *lemma* relation.refl_trans_gen_of_transitive_reflexive

Modified src/logic/relator.lean
- \+/\- *lemma* relator.rel_exists_of_left_total
- \+/\- *lemma* relator.rel_forall_of_right_total

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.integrable_smul_iff
- \+/\- *lemma* measure_theory.l1.dist_to_fun
- \+/\- *lemma* measure_theory.l1.norm_eq_norm_to_fun
- \+/\- *lemma* measure_theory.l1.norm_of_fun

Modified test/conv/apply_congr.lean


Modified test/equiv_rw.lean


Modified test/hint.lean


Modified test/norm_cast_cardinal.lean
- \+/\- *lemma* coe_bit1

Modified test/nth_rewrite.lean


Modified test/ring_exp.lean


Modified test/tauto.lean




## [2020-06-01 23:39:34](https://github.com/leanprover-community/mathlib/commit/b95f165)
chore(group_theory/sub*): move unbundled submonoids and subgroups to `deprecated` ([#2912](https://github.com/leanprover-community/mathlib/pull/2912))
* move unbundled submonoids to `deprecated/submonoid.lean`;
* move unbundled subgroups to `deprecated/subgroup.lean`;
* move bundled subgroups to `group_theory/subgroup.lean`;
* unbundled versions import bundled.
#### Estimated changes
Added src/deprecated/subgroup.lean
- \+ *inductive* add_group.in_closure
- \+ *lemma* additive.is_add_subgroup
- \+ *theorem* additive.is_add_subgroup_iff
- \+ *lemma* additive.normal_add_subgroup
- \+ *theorem* additive.normal_add_subgroup_iff
- \+ *theorem* additive.simple_add_group_iff
- \+ *def* gmultiples
- \+ *lemma* gmultiples_subset
- \+ *def* gpowers
- \+ *lemma* gpowers_subset
- \+ *def* group.closure
- \+ *theorem* group.closure_eq_mclosure
- \+ *theorem* group.closure_mono
- \+ *lemma* group.closure_subgroup
- \+ *theorem* group.closure_subset
- \+ *lemma* group.closure_subset_iff
- \+ *lemma* group.conj_mem_conjugates_of_set
- \+ *def* group.conjugates
- \+ *def* group.conjugates_of_set
- \+ *theorem* group.conjugates_of_set_mono
- \+ *theorem* group.conjugates_of_set_subset
- \+ *theorem* group.conjugates_of_set_subset_normal_closure
- \+ *lemma* group.conjugates_subset
- \+ *theorem* group.exists_list_of_mem_closure
- \+ *theorem* group.gpowers_eq_closure
- \+ *lemma* group.image_closure
- \+ *inductive* group.in_closure
- \+ *theorem* group.mclosure_inv_subset
- \+ *theorem* group.mclosure_subset
- \+ *lemma* group.mem_closure
- \+ *theorem* group.mem_closure_union_iff
- \+ *lemma* group.mem_conjugates_of_set_iff
- \+ *lemma* group.mem_conjugates_self
- \+ *def* group.normal_closure
- \+ *theorem* group.normal_closure_mono
- \+ *theorem* group.normal_closure_subset
- \+ *lemma* group.normal_closure_subset_iff
- \+ *theorem* group.subset_closure
- \+ *theorem* group.subset_conjugates_of_set
- \+ *theorem* group.subset_normal_closure
- \+ *lemma* injective_mul
- \+ *lemma* is_add_subgroup.gsmul_coe
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+ *theorem* is_add_subgroup.of_sub
- \+ *theorem* is_add_subgroup.sub_mem
- \+ *lemma* is_group_hom.inj_iff_trivial_ker
- \+ *lemma* is_group_hom.inj_of_trivial_ker
- \+ *lemma* is_group_hom.inv_iff_ker'
- \+ *lemma* is_group_hom.inv_iff_ker
- \+ *lemma* is_group_hom.inv_ker_one'
- \+ *lemma* is_group_hom.inv_ker_one
- \+ *def* is_group_hom.ker
- \+ *lemma* is_group_hom.mem_ker
- \+ *lemma* is_group_hom.one_iff_ker_inv'
- \+ *lemma* is_group_hom.one_iff_ker_inv
- \+ *lemma* is_group_hom.one_ker_inv'
- \+ *lemma* is_group_hom.one_ker_inv
- \+ *lemma* is_group_hom.trivial_ker_iff_eq_one
- \+ *lemma* is_group_hom.trivial_ker_of_inj
- \+ *def* is_subgroup.center
- \+ *lemma* is_subgroup.coe_gpow
- \+ *lemma* is_subgroup.coe_inv
- \+ *lemma* is_subgroup.eq_trivial_iff
- \+ *lemma* is_subgroup.gpow_mem
- \+ *lemma* is_subgroup.inv_mem_iff
- \+ *lemma* is_subgroup.mem_center
- \+ *lemma* is_subgroup.mem_norm_comm
- \+ *lemma* is_subgroup.mem_norm_comm_iff
- \+ *lemma* is_subgroup.mem_trivial
- \+ *lemma* is_subgroup.mul_mem_cancel_left
- \+ *lemma* is_subgroup.mul_mem_cancel_right
- \+ *def* is_subgroup.normalizer
- \+ *theorem* is_subgroup.of_div
- \+ *lemma* is_subgroup.subset_normalizer
- \+ *def* is_subgroup.trivial
- \+ *lemma* is_subgroup.trivial_eq_closure
- \+ *lemma* is_subgroup_Union_of_directed
- \+ *lemma* mem_gmultiples
- \+ *lemma* mem_gpowers
- \+ *def* monoid_hom.range_factorization
- \+ *def* monoid_hom.range_subtype_val
- \+ *lemma* multiplicative.is_subgroup
- \+ *theorem* multiplicative.is_subgroup_iff
- \+ *lemma* multiplicative.normal_subgroup
- \+ *theorem* multiplicative.normal_subgroup_iff
- \+ *theorem* multiplicative.simple_group_iff
- \+ *lemma* normal_subgroup_of_comm_group
- \+ *lemma* simple_group_of_surjective
- \+ *def* subgroup.of

Added src/deprecated/submonoid.lean
- \+ *inductive* add_monoid.in_closure
- \+ *lemma* additive.is_add_submonoid
- \+ *theorem* additive.is_add_submonoid_iff
- \+ *lemma* image.is_submonoid
- \+ *lemma* is_add_submonoid.multiple_subset
- \+ *lemma* is_add_submonoid.smul_coe
- \+ *lemma* is_add_submonoid.smul_mem
- \+ *lemma* is_submonoid.coe_mul
- \+ *lemma* is_submonoid.coe_one
- \+ *lemma* is_submonoid.coe_pow
- \+ *lemma* is_submonoid.finset_prod_mem
- \+ *lemma* is_submonoid.list_prod_mem
- \+ *lemma* is_submonoid.multiset_prod_mem
- \+ *lemma* is_submonoid.pow_mem
- \+ *lemma* is_submonoid.power_subset
- \+ *lemma* is_submonoid_Union_of_directed
- \+ *def* monoid.closure
- \+ *theorem* monoid.closure_mono
- \+ *theorem* monoid.closure_singleton
- \+ *theorem* monoid.closure_subset
- \+ *theorem* monoid.exists_list_of_mem_closure
- \+ *lemma* monoid.image_closure
- \+ *inductive* monoid.in_closure
- \+ *theorem* monoid.mem_closure_union_iff
- \+ *theorem* monoid.subset_closure
- \+ *lemma* multiples.add_mem
- \+ *lemma* multiples.self_mem
- \+ *lemma* multiples.zero_mem
- \+ *def* multiples
- \+ *lemma* multiplicative.is_submonoid
- \+ *theorem* multiplicative.is_submonoid_iff
- \+ *lemma* powers.mul_mem
- \+ *lemma* powers.one_mem
- \+ *lemma* powers.self_mem
- \+ *def* powers
- \+ *def* submonoid.of

Deleted src/group_theory/bundled_subgroup.lean
- \- *lemma* add_subgroup.gsmul_mem
- \- *lemma* add_subgroup.mem_closure_singleton
- \- *def* add_subgroup.of_subgroup
- \- *def* add_subgroup.to_subgroup
- \- *structure* add_subgroup
- \- *lemma* monoid_hom.coe_range
- \- *lemma* monoid_hom.comap_ker
- \- *def* monoid_hom.eq_locus
- \- *lemma* monoid_hom.eq_of_eq_on_dense
- \- *lemma* monoid_hom.eq_of_eq_on_top
- \- *lemma* monoid_hom.eq_on_closure
- \- *lemma* monoid_hom.gclosure_preimage_le
- \- *def* monoid_hom.ker
- \- *lemma* monoid_hom.map_closure
- \- *lemma* monoid_hom.map_range
- \- *lemma* monoid_hom.mem_ker
- \- *lemma* monoid_hom.mem_range
- \- *lemma* monoid_hom.rang_top_of_surjective
- \- *def* monoid_hom.range
- \- *lemma* monoid_hom.range_top_iff_surjective
- \- *def* mul_equiv.subgroup_congr
- \- *def* subgroup.add_subgroup_equiv
- \- *lemma* subgroup.bot_prod_bot
- \- *def* subgroup.closure
- \- *lemma* subgroup.closure_Union
- \- *lemma* subgroup.closure_empty
- \- *lemma* subgroup.closure_eq
- \- *lemma* subgroup.closure_eq_of_le
- \- *lemma* subgroup.closure_induction
- \- *lemma* subgroup.closure_le
- \- *lemma* subgroup.closure_mono
- \- *lemma* subgroup.closure_union
- \- *lemma* subgroup.closure_univ
- \- *lemma* subgroup.coe_Inf
- \- *lemma* subgroup.coe_bot
- \- *lemma* subgroup.coe_coe
- \- *lemma* subgroup.coe_comap
- \- *lemma* subgroup.coe_inf
- \- *lemma* subgroup.coe_inv
- \- *lemma* subgroup.coe_map
- \- *lemma* subgroup.coe_mul
- \- *lemma* subgroup.coe_one
- \- *lemma* subgroup.coe_prod
- \- *lemma* subgroup.coe_subset_coe
- \- *theorem* subgroup.coe_subtype
- \- *lemma* subgroup.coe_to_submonoid
- \- *lemma* subgroup.coe_top
- \- *def* subgroup.comap
- \- *lemma* subgroup.comap_comap
- \- *lemma* subgroup.comap_inf
- \- *lemma* subgroup.comap_infi
- \- *lemma* subgroup.comap_top
- \- *theorem* subgroup.ext'
- \- *theorem* subgroup.ext
- \- *lemma* subgroup.gc_map_comap
- \- *lemma* subgroup.gpow_mem
- \- *theorem* subgroup.inv_mem
- \- *lemma* subgroup.le_def
- \- *lemma* subgroup.list_prod_mem
- \- *def* subgroup.map
- \- *lemma* subgroup.map_bot
- \- *lemma* subgroup.map_le_iff_le_comap
- \- *lemma* subgroup.map_map
- \- *lemma* subgroup.map_sup
- \- *lemma* subgroup.map_supr
- \- *lemma* subgroup.mem_Inf
- \- *lemma* subgroup.mem_Sup_of_directed_on
- \- *lemma* subgroup.mem_bot
- \- *lemma* subgroup.mem_closure
- \- *lemma* subgroup.mem_closure_singleton
- \- *lemma* subgroup.mem_coe
- \- *lemma* subgroup.mem_comap
- \- *lemma* subgroup.mem_inf
- \- *lemma* subgroup.mem_map
- \- *lemma* subgroup.mem_prod
- \- *lemma* subgroup.mem_supr_of_directed
- \- *lemma* subgroup.mem_top
- \- *theorem* subgroup.mul_mem
- \- *lemma* subgroup.multiset_prod_mem
- \- *def* subgroup.of
- \- *def* subgroup.of_add_subgroup
- \- *theorem* subgroup.one_mem
- \- *lemma* subgroup.pow_mem
- \- *def* subgroup.prod
- \- *def* subgroup.prod_equiv
- \- *lemma* subgroup.prod_mem
- \- *lemma* subgroup.prod_mono
- \- *lemma* subgroup.prod_mono_left
- \- *lemma* subgroup.prod_mono_right
- \- *lemma* subgroup.prod_top
- \- *lemma* subgroup.subset_closure
- \- *def* subgroup.subtype
- \- *def* subgroup.to_add_subgroup
- \- *lemma* subgroup.top_prod
- \- *lemma* subgroup.top_prod_top
- \- *structure* subgroup

Modified src/group_theory/coset.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/subgroup.lean
- \- *inductive* add_group.in_closure
- \+ *lemma* add_subgroup.gsmul_mem
- \+ *lemma* add_subgroup.mem_closure_singleton
- \+ *def* add_subgroup.of_subgroup
- \+ *def* add_subgroup.to_subgroup
- \+ *structure* add_subgroup
- \- *lemma* additive.is_add_subgroup
- \- *theorem* additive.is_add_subgroup_iff
- \- *lemma* additive.normal_add_subgroup
- \- *theorem* additive.normal_add_subgroup_iff
- \- *theorem* additive.simple_add_group_iff
- \- *def* gmultiples
- \- *lemma* gmultiples_subset
- \- *def* gpowers
- \- *lemma* gpowers_subset
- \- *def* group.closure
- \- *theorem* group.closure_eq_mclosure
- \- *theorem* group.closure_mono
- \- *lemma* group.closure_subgroup
- \- *theorem* group.closure_subset
- \- *lemma* group.closure_subset_iff
- \- *lemma* group.conj_mem_conjugates_of_set
- \- *def* group.conjugates
- \- *def* group.conjugates_of_set
- \- *theorem* group.conjugates_of_set_mono
- \- *theorem* group.conjugates_of_set_subset
- \- *theorem* group.conjugates_of_set_subset_normal_closure
- \- *lemma* group.conjugates_subset
- \- *theorem* group.exists_list_of_mem_closure
- \- *theorem* group.gpowers_eq_closure
- \- *lemma* group.image_closure
- \- *inductive* group.in_closure
- \- *theorem* group.mclosure_inv_subset
- \- *theorem* group.mclosure_subset
- \- *lemma* group.mem_closure
- \- *theorem* group.mem_closure_union_iff
- \- *lemma* group.mem_conjugates_of_set_iff
- \- *lemma* group.mem_conjugates_self
- \- *def* group.normal_closure
- \- *theorem* group.normal_closure_mono
- \- *theorem* group.normal_closure_subset
- \- *lemma* group.normal_closure_subset_iff
- \- *theorem* group.subset_closure
- \- *theorem* group.subset_conjugates_of_set
- \- *theorem* group.subset_normal_closure
- \- *lemma* injective_mul
- \- *lemma* is_add_subgroup.gsmul_coe
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *theorem* is_add_subgroup.of_sub
- \- *theorem* is_add_subgroup.sub_mem
- \- *lemma* is_group_hom.inj_iff_trivial_ker
- \- *lemma* is_group_hom.inj_of_trivial_ker
- \- *lemma* is_group_hom.inv_iff_ker'
- \- *lemma* is_group_hom.inv_iff_ker
- \- *lemma* is_group_hom.inv_ker_one'
- \- *lemma* is_group_hom.inv_ker_one
- \- *def* is_group_hom.ker
- \- *lemma* is_group_hom.mem_ker
- \- *lemma* is_group_hom.one_iff_ker_inv'
- \- *lemma* is_group_hom.one_iff_ker_inv
- \- *lemma* is_group_hom.one_ker_inv'
- \- *lemma* is_group_hom.one_ker_inv
- \- *lemma* is_group_hom.trivial_ker_iff_eq_one
- \- *lemma* is_group_hom.trivial_ker_of_inj
- \- *def* is_subgroup.center
- \- *lemma* is_subgroup.coe_gpow
- \- *lemma* is_subgroup.coe_inv
- \- *lemma* is_subgroup.eq_trivial_iff
- \- *lemma* is_subgroup.gpow_mem
- \- *lemma* is_subgroup.inv_mem_iff
- \- *lemma* is_subgroup.mem_center
- \- *lemma* is_subgroup.mem_norm_comm
- \- *lemma* is_subgroup.mem_norm_comm_iff
- \- *lemma* is_subgroup.mem_trivial
- \- *lemma* is_subgroup.mul_mem_cancel_left
- \- *lemma* is_subgroup.mul_mem_cancel_right
- \- *def* is_subgroup.normalizer
- \- *theorem* is_subgroup.of_div
- \- *lemma* is_subgroup.subset_normalizer
- \- *def* is_subgroup.trivial
- \- *lemma* is_subgroup.trivial_eq_closure
- \- *lemma* is_subgroup_Union_of_directed
- \- *lemma* mem_gmultiples
- \- *lemma* mem_gpowers
- \+ *lemma* monoid_hom.coe_range
- \+ *lemma* monoid_hom.comap_ker
- \+ *def* monoid_hom.eq_locus
- \+ *lemma* monoid_hom.eq_of_eq_on_dense
- \+ *lemma* monoid_hom.eq_of_eq_on_top
- \+ *lemma* monoid_hom.eq_on_closure
- \+ *lemma* monoid_hom.gclosure_preimage_le
- \+ *def* monoid_hom.ker
- \+ *lemma* monoid_hom.map_closure
- \+ *lemma* monoid_hom.map_range
- \+ *lemma* monoid_hom.mem_ker
- \+ *lemma* monoid_hom.mem_range
- \+ *lemma* monoid_hom.rang_top_of_surjective
- \+ *def* monoid_hom.range
- \- *def* monoid_hom.range_factorization
- \- *def* monoid_hom.range_subtype_val
- \+ *lemma* monoid_hom.range_top_iff_surjective
- \+ *def* mul_equiv.subgroup_congr
- \- *lemma* multiplicative.is_subgroup
- \- *theorem* multiplicative.is_subgroup_iff
- \- *lemma* multiplicative.normal_subgroup
- \- *theorem* multiplicative.normal_subgroup_iff
- \- *theorem* multiplicative.simple_group_iff
- \- *lemma* normal_subgroup_of_comm_group
- \- *lemma* simple_group_of_surjective
- \+ *def* subgroup.add_subgroup_equiv
- \+ *lemma* subgroup.bot_prod_bot
- \+ *def* subgroup.closure
- \+ *lemma* subgroup.closure_Union
- \+ *lemma* subgroup.closure_empty
- \+ *lemma* subgroup.closure_eq
- \+ *lemma* subgroup.closure_eq_of_le
- \+ *lemma* subgroup.closure_induction
- \+ *lemma* subgroup.closure_le
- \+ *lemma* subgroup.closure_mono
- \+ *lemma* subgroup.closure_union
- \+ *lemma* subgroup.closure_univ
- \+ *lemma* subgroup.coe_Inf
- \+ *lemma* subgroup.coe_bot
- \+ *lemma* subgroup.coe_coe
- \+ *lemma* subgroup.coe_comap
- \+ *lemma* subgroup.coe_inf
- \+ *lemma* subgroup.coe_inv
- \+ *lemma* subgroup.coe_map
- \+ *lemma* subgroup.coe_mul
- \+ *lemma* subgroup.coe_one
- \+ *lemma* subgroup.coe_prod
- \+ *lemma* subgroup.coe_subset_coe
- \+ *theorem* subgroup.coe_subtype
- \+ *lemma* subgroup.coe_to_submonoid
- \+ *lemma* subgroup.coe_top
- \+ *def* subgroup.comap
- \+ *lemma* subgroup.comap_comap
- \+ *lemma* subgroup.comap_inf
- \+ *lemma* subgroup.comap_infi
- \+ *lemma* subgroup.comap_top
- \+ *theorem* subgroup.ext'
- \+ *theorem* subgroup.ext
- \+ *lemma* subgroup.gc_map_comap
- \+ *lemma* subgroup.gpow_mem
- \+ *theorem* subgroup.inv_mem
- \+ *lemma* subgroup.le_def
- \+ *lemma* subgroup.list_prod_mem
- \+ *def* subgroup.map
- \+ *lemma* subgroup.map_bot
- \+ *lemma* subgroup.map_le_iff_le_comap
- \+ *lemma* subgroup.map_map
- \+ *lemma* subgroup.map_sup
- \+ *lemma* subgroup.map_supr
- \+ *lemma* subgroup.mem_Inf
- \+ *lemma* subgroup.mem_Sup_of_directed_on
- \+ *lemma* subgroup.mem_bot
- \+ *lemma* subgroup.mem_closure
- \+ *lemma* subgroup.mem_closure_singleton
- \+ *lemma* subgroup.mem_coe
- \+ *lemma* subgroup.mem_comap
- \+ *lemma* subgroup.mem_inf
- \+ *lemma* subgroup.mem_map
- \+ *lemma* subgroup.mem_prod
- \+ *lemma* subgroup.mem_supr_of_directed
- \+ *lemma* subgroup.mem_top
- \+ *theorem* subgroup.mul_mem
- \+ *lemma* subgroup.multiset_prod_mem
- \+ *def* subgroup.of_add_subgroup
- \+ *theorem* subgroup.one_mem
- \+ *lemma* subgroup.pow_mem
- \+ *def* subgroup.prod
- \+ *def* subgroup.prod_equiv
- \+ *lemma* subgroup.prod_mem
- \+ *lemma* subgroup.prod_mono
- \+ *lemma* subgroup.prod_mono_left
- \+ *lemma* subgroup.prod_mono_right
- \+ *lemma* subgroup.prod_top
- \+ *lemma* subgroup.subset_closure
- \+ *def* subgroup.subtype
- \+ *def* subgroup.to_add_subgroup
- \+ *lemma* subgroup.top_prod
- \+ *lemma* subgroup.top_prod_top
- \+ *structure* subgroup

Modified src/group_theory/submonoid.lean
- \- *inductive* add_monoid.in_closure
- \- *lemma* additive.is_add_submonoid
- \- *theorem* additive.is_add_submonoid_iff
- \- *lemma* image.is_submonoid
- \- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* is_add_submonoid.smul_coe
- \- *lemma* is_add_submonoid.smul_mem
- \- *lemma* is_submonoid.coe_mul
- \- *lemma* is_submonoid.coe_one
- \- *lemma* is_submonoid.coe_pow
- \- *lemma* is_submonoid.finset_prod_mem
- \- *lemma* is_submonoid.list_prod_mem
- \- *lemma* is_submonoid.multiset_prod_mem
- \- *lemma* is_submonoid.pow_mem
- \- *lemma* is_submonoid.power_subset
- \- *lemma* is_submonoid_Union_of_directed
- \- *def* monoid.closure
- \- *theorem* monoid.closure_mono
- \- *theorem* monoid.closure_singleton
- \- *theorem* monoid.closure_subset
- \- *theorem* monoid.exists_list_of_mem_closure
- \- *lemma* monoid.image_closure
- \- *inductive* monoid.in_closure
- \- *theorem* monoid.mem_closure_union_iff
- \- *theorem* monoid.subset_closure
- \- *lemma* multiples.add_mem
- \- *lemma* multiples.self_mem
- \- *lemma* multiples.zero_mem
- \- *def* multiples
- \- *lemma* multiplicative.is_submonoid
- \- *theorem* multiplicative.is_submonoid_iff
- \- *lemma* powers.mul_mem
- \- *lemma* powers.one_mem
- \- *lemma* powers.self_mem
- \- *def* powers
- \- *def* submonoid.of

Modified src/ring_theory/subring.lean




## [2020-06-01 21:26:03](https://github.com/leanprover-community/mathlib/commit/66ce5d0)
feat(representation_theory/maschke): Maschke's theorem ([#2762](https://github.com/leanprover-community/mathlib/pull/2762))
The final theorem is
```
lemma monoid_algebra.submodule.exists_is_compl
  (not_dvd : ¬(ring_char k ∣ fintype.card G)) (p : submodule (monoid_algebra k G) V) :
  ∃ q : submodule (monoid_algebra k G) V, is_compl p q
```
for `[field k]`.
The core computation, turning a `k`-linear retraction of `k[G]`-linear map into a `k[G]`-linear retraction by averaging over `G`, happens over an arbitrary `[comm_ring k]` in which `[invertible (fintype.card G : k)]`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* finsupp.smul_single'

Modified src/data/monoid_algebra.lean
- \+ *def* monoid_algebra.equivariant_of_linear_of_comm
- \+ *lemma* monoid_algebra.equivariant_of_linear_of_comm_apply
- \+ *def* monoid_algebra.group_smul.linear_map
- \+ *lemma* monoid_algebra.group_smul.linear_map_apply
- \+ *lemma* monoid_algebra.single_one_comm

Modified src/logic/embedding.lean
- \+ *def* mul_left_embedding
- \+ *lemma* mul_left_embedding_apply
- \+ *def* mul_right_embedding
- \+ *lemma* mul_right_embedding_apply

Added src/representation_theory/maschke.lean
- \+ *def* conjugate
- \+ *lemma* conjugate_i
- \+ *def* equivariant_projection
- \+ *lemma* equivariant_projection_condition
- \+ *lemma* monoid_algebra.exists_left_inverse_of_injective
- \+ *lemma* monoid_algebra.submodule.exists_is_compl
- \+ *def* sum_of_conjugates
- \+ *def* sum_of_conjugates_equivariant

Modified src/ring_theory/algebra.lean




## [2020-06-01 19:40:48](https://github.com/leanprover-community/mathlib/commit/085aade)
chore(linear_algebra/affine_space): use implicit args ([#2905](https://github.com/leanprover-community/mathlib/pull/2905))
Whenever we have an argument `f : affine_map k V P`, Lean can figure out `k`, `V`, and `P`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* affine_map.coe_comp
- \+ *lemma* affine_map.coe_id
- \+/\- *lemma* affine_map.comp_apply
- \+/\- *lemma* affine_map.id_apply



## [2020-06-01 17:01:58](https://github.com/leanprover-community/mathlib/commit/17296e9)
feat(category_theory/abelian): Schur's lemma ([#2838](https://github.com/leanprover-community/mathlib/pull/2838))
I wrote this mostly to gain some familiarity with @TwoFX's work on abelian categories from [#2817](https://github.com/leanprover-community/mathlib/pull/2817).
That all looked great, and Schur's lemma was pleasantly straightforward.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.epi_of_epi_image

Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* category_theory.limits.cokernel.cokernel_iso
- \+/\- *def* category_theory.limits.cokernel.of_epi
- \+/\- *def* category_theory.limits.cokernel.of_iso_comp
- \+/\- *lemma* category_theory.limits.cokernel.π_of_epi
- \+/\- *def* category_theory.limits.cokernel.π_of_zero
- \+ *def* category_theory.limits.cokernel.π_zero_is_iso
- \+ *lemma* category_theory.limits.cokernel_not_iso_of_nonzero
- \+ *lemma* category_theory.limits.cokernel_not_mono_of_nonzero
- \+ *lemma* category_theory.limits.eq_zero_of_epi_kernel
- \+ *lemma* category_theory.limits.eq_zero_of_mono_cokernel
- \+ *abbreviation* category_theory.limits.has_cokernel
- \+ *abbreviation* category_theory.limits.has_kernel
- \+/\- *def* category_theory.limits.kernel.iso_kernel
- \+/\- *def* category_theory.limits.kernel.of_comp_iso
- \+/\- *def* category_theory.limits.kernel.of_mono
- \+/\- *lemma* category_theory.limits.kernel.ι_of_mono
- \+/\- *def* category_theory.limits.kernel.ι_of_zero
- \+/\- *def* category_theory.limits.kernel.ι_zero_is_iso
- \+ *lemma* category_theory.limits.kernel_not_epi_of_nonzero
- \+ *lemma* category_theory.limits.kernel_not_iso_of_nonzero

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* category_theory.limits.eq_zero_of_image_eq_zero
- \+ *lemma* category_theory.limits.has_zero_object.from_zero_ext
- \+ *lemma* category_theory.limits.has_zero_object.to_zero_ext
- \+ *lemma* category_theory.limits.nonzero_image_of_nonzero

Modified src/category_theory/preadditive.lean
- \+ *lemma* category_theory.preadditive.epi_of_cokernel_zero
- \+/\- *def* category_theory.preadditive.has_colimit_parallel_pair
- \+/\- *def* category_theory.preadditive.has_limit_parallel_pair
- \+ *lemma* category_theory.preadditive.mono_of_kernel_zero

Added src/category_theory/schur.lean
- \+ *def* category_theory.is_iso_of_hom_simple

Added src/category_theory/simple.lean
- \+ *lemma* category_theory.cokernel_zero_of_nonzero_to_simple
- \+ *lemma* category_theory.epi_from_simple_zero_of_not_iso
- \+ *def* category_theory.is_iso_of_epi_of_nonzero
- \+ *def* category_theory.is_iso_of_mono_of_nonzero
- \+ *lemma* category_theory.kernel_zero_of_nonzero_from_simple
- \+ *lemma* category_theory.mono_to_simple_zero_of_not_iso
- \+ *lemma* category_theory.simple.ext
- \+ *def* category_theory.simple_of_cosimple
- \+ *lemma* category_theory.zero_not_simple



## [2020-06-01 15:13:02](https://github.com/leanprover-community/mathlib/commit/2812cdc)
fix(ci): check nolints.txt against master ([#2906](https://github.com/leanprover-community/mathlib/pull/2906))
Currently, leanprover-community-bot makes an "update nolints" PR if both of the following hold:
- the `nolints` branch doesn't exist, meaning there isn't already an open nolints PR
- `nolints.txt` has been modified compared to HEAD.
This can lead to a duplicate nolints PR (see e.g. [#2899](https://github.com/leanprover-community/mathlib/pull/2899) and [#2901](https://github.com/leanprover-community/mathlib/pull/2901)), since a nolints PR might have been merged after this build on `master` started, but before this step runs.
This PR changes the second check so that it instead compares `nolints.txt` against the most recent `master` commit, which should fix this.
#### Estimated changes
Modified scripts/update_nolints.sh




## [2020-06-01 12:17:18](https://github.com/leanprover-community/mathlib/commit/f142b42)
fix(scripts/deploy_docs): correct git push syntax ([#2903](https://github.com/leanprover-community/mathlib/pull/2903))
The suggestion I made in [#2893](https://github.com/leanprover-community/mathlib/pull/2893) didn't work.
#### Estimated changes
Modified scripts/deploy_docs.sh




## [2020-06-01 12:17:17](https://github.com/leanprover-community/mathlib/commit/b405a5e)
fix(tactic/equiv_rw): use kdepends_on rather than occurs ([#2898](https://github.com/leanprover-community/mathlib/pull/2898))
`kdepends_on t e` and `e.occurs t` sometimes give different answers, and it seems `equiv_rw` wants the behaviour that `kdepends_on` provides.
There is a new test which failed with `occurs`, and succeeds using `kdepends_on`. No other changes.
#### Estimated changes
Modified src/tactic/equiv_rw.lean


Modified test/equiv_rw.lean




## [2020-06-01 11:48:05](https://github.com/leanprover-community/mathlib/commit/b9d485d)
chore(data/mv_polynomial): swap the order of mv_polynomial.ext_iff ([#2902](https://github.com/leanprover-community/mathlib/pull/2902))
The previous order of implications is not the one you usually want to simp or rw with.
#### Estimated changes
Modified src/data/mv_polynomial.lean




## [2020-06-01 10:50:43](https://github.com/leanprover-community/mathlib/commit/0485e0f)
feat(scripts/deploy_docs): force push generated docs ([#2893](https://github.com/leanprover-community/mathlib/pull/2893))
(1) We build the full html docs in every CI run, even though they only get saved on master builds. Just compiling the .lean files used in doc generation should be enough to catch 95% of breaks. I think the bit of extra risk is worth speeding up the CI runs, especially since linting is now as fast as tests + docs. 
(2) The repo hosting the html pages was 1.3gb because we kept every revision. Half of the time spent on doc builds was just checking out the repo. I've deleted the history. This PR changes the build script to overwrite the previous version.
#### Estimated changes
Modified scripts/deploy_docs.sh




## [2020-06-01 09:01:28](https://github.com/leanprover-community/mathlib/commit/9172cdf)
feat(linear_algebra/affine_space): affine spaces ([#2816](https://github.com/leanprover-community/mathlib/pull/2816))
Define (very minimally) affine spaces (as an abbreviation for
add_torsor in the case where the group is a vector space), affine
subspaces, the affine span of a set of points and affine maps.
#### Estimated changes
Added src/linear_algebra/affine_space.lean
- \+ *lemma* affine_map.coe_mk
- \+ *def* affine_map.comp
- \+ *lemma* affine_map.comp_apply
- \+ *lemma* affine_map.ext
- \+ *def* affine_map.id
- \+ *lemma* affine_map.id_apply
- \+ *lemma* affine_map.map_vadd
- \+ *lemma* affine_map.map_vsub
- \+ *lemma* affine_map.to_fun_eq_coe
- \+ *structure* affine_map
- \+ *lemma* affine_space.mem_span_points
- \+ *def* affine_space.span_points
- \+ *lemma* affine_space.span_points_nonempty_of_nonempty
- \+ *lemma* affine_space.vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \+ *def* affine_space.vector_span
- \+ *lemma* affine_space.vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \+ *abbreviation* affine_space
- \+ *def* affine_span
- \+ *lemma* affine_span_coe
- \+ *lemma* affine_span_mem
- \+ *lemma* affine_subspace.mem_coe
- \+ *lemma* affine_subspace.mem_univ
- \+ *def* affine_subspace.univ
- \+ *lemma* affine_subspace.univ_coe
- \+ *structure* affine_subspace



## [2020-06-01 06:43:53](https://github.com/leanprover-community/mathlib/commit/6beebb0)
chore(scripts): update nolints.txt ([#2899](https://github.com/leanprover-community/mathlib/pull/2899))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-01 05:31:26](https://github.com/leanprover-community/mathlib/commit/7263917)
chore(order/complete_lattice): redefine `ord_continuous` ([#2886](https://github.com/leanprover-community/mathlib/pull/2886))
Redefine `ord_continuous` using `is_lub` to ensure that the definition
makes sense for `conditionally_complete_lattice`s.
#### Estimated changes
Modified src/order/bounds.lean


Modified src/order/complete_lattice.lean
- \- *lemma* ord_continuous.mono
- \- *lemma* ord_continuous.sup
- \- *def* ord_continuous

Added src/order/ord_continuous.lean
- \+ *lemma* left_ord_continuous.coe_to_le_order_embedding
- \+ *lemma* left_ord_continuous.coe_to_lt_order_embedding
- \+ *lemma* left_ord_continuous.comp
- \+ *lemma* left_ord_continuous.le_iff
- \+ *lemma* left_ord_continuous.lt_iff
- \+ *lemma* left_ord_continuous.map_Sup'
- \+ *lemma* left_ord_continuous.map_Sup
- \+ *lemma* left_ord_continuous.map_cSup
- \+ *lemma* left_ord_continuous.map_csupr
- \+ *lemma* left_ord_continuous.map_is_greatest
- \+ *lemma* left_ord_continuous.map_sup
- \+ *lemma* left_ord_continuous.map_supr
- \+ *lemma* left_ord_continuous.mono
- \+ *def* left_ord_continuous.to_le_order_embedding
- \+ *def* left_ord_continuous.to_lt_order_embedding
- \+ *def* left_ord_continuous
- \+ *lemma* right_ord_continuous.coe_to_le_order_embedding
- \+ *lemma* right_ord_continuous.coe_to_lt_order_embedding
- \+ *lemma* right_ord_continuous.comp
- \+ *lemma* right_ord_continuous.le_iff
- \+ *lemma* right_ord_continuous.lt_iff
- \+ *lemma* right_ord_continuous.map_Inf'
- \+ *lemma* right_ord_continuous.map_Inf
- \+ *lemma* right_ord_continuous.map_cInf
- \+ *lemma* right_ord_continuous.map_cinfi
- \+ *lemma* right_ord_continuous.map_inf
- \+ *lemma* right_ord_continuous.map_infi
- \+ *lemma* right_ord_continuous.map_is_least
- \+ *lemma* right_ord_continuous.mono
- \+ *def* right_ord_continuous.to_le_order_embedding
- \+ *def* right_ord_continuous.to_lt_order_embedding
- \+ *def* right_ord_continuous



## [2020-06-01 04:59:52](https://github.com/leanprover-community/mathlib/commit/ea76bd8)
chore(scripts): update nolints.txt ([#2896](https://github.com/leanprover-community/mathlib/pull/2896))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-01 03:45:00](https://github.com/leanprover-community/mathlib/commit/5c27885)
feat(order/order_iso): group structure on order automorphisms ([#2875](https://github.com/leanprover-community/mathlib/pull/2875))
Also add a few missing lemmas about `order_iso`
#### Estimated changes
Modified src/order/order_iso.lean
- \+ *lemma* order_iso.apply_inv_self
- \+/\- *theorem* order_iso.apply_symm_apply
- \+/\- *theorem* order_iso.coe_fn_injective
- \+ *lemma* order_iso.coe_mul
- \+ *lemma* order_iso.coe_one
- \+ *theorem* order_iso.ext
- \+ *lemma* order_iso.inv_apply_self
- \+ *lemma* order_iso.mul_apply
- \- *def* order_iso.preimage
- \+ *theorem* order_iso.rel_symm_apply
- \+ *def* order_iso.rsymm
- \+/\- *theorem* order_iso.symm_apply_apply
- \+ *theorem* order_iso.symm_apply_rel
- \+ *theorem* order_iso.to_equiv_injective
- \- *lemma* order_iso.to_equiv_to_fun
- \+/\- *theorem* order_iso.trans_apply

Modified src/set_theory/ordinal.lean




## [2020-06-01 01:58:08](https://github.com/leanprover-community/mathlib/commit/73f95a7)
chore(algebra/group): move defs to `defs.lean` ([#2885](https://github.com/leanprover-community/mathlib/pull/2885))
Also delete the aliases `eq_of_add_eq_add_left` and `eq_of_add_eq_add_right`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \- *def* eq_of_add_eq_add_left
- \- *def* eq_of_add_eq_add_right
- \- *lemma* group.mul_left_cancel
- \- *lemma* group.mul_right_cancel
- \- *lemma* inv_eq_of_mul_eq_one
- \- *lemma* inv_inv
- \- *lemma* inv_mul_cancel_left
- \- *def* inv_mul_self
- \- *lemma* left_inv_eq_right_inv
- \- *lemma* mul_assoc
- \- *lemma* mul_comm
- \- *lemma* mul_inv_cancel_right
- \- *def* mul_inv_self
- \- *lemma* mul_left_cancel
- \- *lemma* mul_left_cancel_iff
- \- *theorem* mul_left_inj
- \- *theorem* mul_left_injective
- \- *lemma* mul_left_inv
- \- *lemma* mul_one
- \- *lemma* mul_right_cancel
- \- *lemma* mul_right_cancel_iff
- \- *theorem* mul_right_inj
- \- *theorem* mul_right_injective
- \- *lemma* mul_right_inv
- \- *lemma* one_mul
- \- *lemma* sub_eq_add_neg

Added src/algebra/group/defs.lean
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* inv_inv
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_self
- \+ *lemma* left_inv_eq_right_inv
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_self
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_left_injective
- \+ *lemma* mul_left_inv
- \+ *lemma* mul_one
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_right_cancel_iff
- \+ *theorem* mul_right_inj
- \+ *theorem* mul_right_injective
- \+ *lemma* mul_right_inv
- \+ *lemma* one_mul
- \+ *lemma* sub_eq_add_neg

Modified src/set_theory/ordinal.lean


Modified src/topology/algebra/uniform_group.lean


