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
- \+ *lemma* compact.bdd_below
- \+ *lemma* compact.bdd_above
- \- *lemma* bdd_below_of_compact
- \- *lemma* bdd_above_of_compact

Modified src/topology/basic.lean
- \+ *lemma* is_closed.closure_eq
- \+ *lemma* is_closed.closure_subset
- \+ *lemma* is_closed.closure_subset_iff
- \+/\- *lemma* closure_eq_iff_is_closed
- \+ *lemma* closure_subset_iff_is_closed
- \+/\- *lemma* closure_empty_iff
- \+ *lemma* is_closed_iff_cluster_pt
- \- *lemma* closure_eq_of_is_closed
- \- *lemma* closure_subset_iff_subset_of_is_closed
- \- *lemma* is_closed_iff_nhds

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean


Modified src/topology/dense_embedding.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* closure_closed_ball

Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/opens.lean


Modified src/topology/separation.lean
- \+ *lemma* compact.is_closed
- \- *lemma* closed_of_compact

Modified src/topology/sequences.lean


Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* is_closed.is_complete
- \- *lemma* is_complete_of_is_closed

Modified src/topology/uniform_space/complete_separated.lean
- \+ *lemma* is_complete.is_closed
- \- *lemma* is_closed_of_is_complete

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
- \+ *lemma* coe_to_lie_equiv
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* one_apply
- \+ *lemma* refl_apply
- \+ *lemma* symm_symm
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* trans_apply
- \+ *lemma* symm_trans_apply
- \+ *lemma* lie_subalgebra.mem_coe
- \+ *lemma* lie_subalgebra.mem_coe'
- \+ *lemma* lie_subalgebra.coe_bracket
- \+ *lemma* lie_subalgebra.ext
- \+ *lemma* lie_subalgebra.ext_iff
- \+ *lemma* lie_algebra.morphism.range_bracket
- \+ *lemma* lie_subalgebra.mem_map_submodule
- \+ *lemma* of_injective_apply
- \+ *lemma* of_eq_apply
- \+ *lemma* of_subalgebra_apply
- \+ *lemma* of_subalgebras_apply
- \+ *lemma* of_subalgebras_symm_apply
- \+ *lemma* lie_conj_apply
- \+ *lemma* lie_conj_symm
- \+ *lemma* lie_equiv_matrix'_apply
- \+ *lemma* lie_equiv_matrix'_symm_apply
- \+ *lemma* matrix.lie_conj_apply
- \+ *lemma* matrix.lie_conj_symm_apply
- \+ *lemma* bilin_form.is_skew_adjoint_bracket
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_apply
- \+ *lemma* skew_adjoint_lie_subalgebra_equiv_symm_apply
- \+ *lemma* matrix.lie_transpose
- \+ *lemma* matrix.is_skew_adjoint_bracket
- \+ *lemma* skew_adjoint_matrices_lie_subalgebra_equiv_apply
- \- *lemma* is_skew_adjoint_bracket
- \+/\- *def* lie_subalgebra_of_subalgebra
- \+/\- *def* lie_subalgebra.incl
- \+/\- *def* lie_algebra.morphism.range
- \+ *def* lie_subalgebra.map
- \+ *def* of_eq
- \+ *def* of_subalgebra
- \+ *def* of_subalgebras
- \+ *def* lie_conj
- \+ *def* skew_adjoint_lie_subalgebra_equiv
- \- *def* skew_adjoint_matrices_lie_embedding

Modified src/data/matrix/basic.lean
- \+ *lemma* transpose_sub

Modified src/linear_algebra/basic.lean
- \+ *lemma* dom_restrict_apply
- \+ *lemma* of_submodule_apply
- \+ *lemma* of_submodule_symm_apply
- \+ *lemma* of_submodules_apply
- \+ *lemma* of_submodules_symm_apply
- \+/\- *lemma* conj_apply
- \+ *lemma* symm_conj_apply
- \+ *lemma* conj_comp
- \+ *lemma* conj_trans
- \+ *lemma* mem_map_equiv
- \+ *theorem* of_injective_apply
- \+ *def* dom_restrict
- \+ *def* of_submodule
- \+ *def* of_submodules

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* comp_injective
- \+ *lemma* matrix.to_bilin_form_comp
- \+ *lemma* mem_is_pair_self_adjoint_submodule
- \+ *lemma* is_pair_self_adjoint_equiv
- \+/\- *lemma* matrix_is_adjoint_pair_bilin_form
- \+ *lemma* matrix.is_adjoint_pair_equiv
- \+ *lemma* mem_self_adjoint_matrices_submodule
- \+ *lemma* mem_skew_adjoint_matrices_submodule
- \- *lemma* pair_self_adjoint_matrices_linear_embedding_apply
- \- *lemma* pair_self_adjoint_matrices_linear_embedding_injective
- \- *def* pair_self_adjoint_matrices_linear_embedding

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* proj_diagonal
- \+/\- *lemma* diagonal_comp_std_basis
- \+/\- *lemma* diagonal_to_lin
- \+ *lemma* to_linear_equiv_apply
- \+ *lemma* to_linear_equiv_symm_apply
- \+ *def* to_linear_equiv

Modified test/noncomm_ring.lean




## [2020-06-30 16:18:08](https://github.com/leanprover-community/mathlib/commit/ea961f7)
chore(ring_theory/polynomial): move `ring_theory.polynomial` to `ring_theory.polynomial.basic` ([#3248](https://github.com/leanprover-community/mathlib/pull/3248))
This PR is the intersection of [#3223](https://github.com/leanprover-community/mathlib/pull/3223) and [#3241](https://github.com/leanprover-community/mathlib/pull/3241), allowing them to be merged in either order.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/where.20should.20these.20definitions.20live.3F
#### Estimated changes
Renamed src/ring_theory/polynomial.lean to src/ring_theory/polynomial/basic.lean


Created src/ring_theory/polynomial/default.lean




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
- \+ *lemma* is_connected.Icc_subset
- \+/\- *lemma* is_closed.cSup_mem
- \+/\- *lemma* is_closed.cInf_mem
- \+ *lemma* eq_Icc_cInf_cSup_of_connected_bdd_closed
- \+ *lemma* compact.Inf_mem
- \+ *lemma* compact.Sup_mem
- \+ *lemma* compact.is_glb_Inf
- \+ *lemma* compact.is_lub_Sup
- \+ *lemma* compact.is_least_Inf
- \+ *lemma* compact.is_greatest_Sup
- \+ *lemma* compact.exists_is_least
- \+ *lemma* compact.exists_is_greatest
- \+ *lemma* compact.exists_is_glb
- \+ *lemma* compact.exists_is_lub
- \+ *lemma* compact.exists_Inf_image_eq
- \+ *lemma* compact.exists_Sup_image_eq
- \+ *lemma* eq_Icc_of_connected_compact

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
- \+/\- *lemma* Sup_mem_closure
- \+/\- *lemma* Inf_mem_closure
- \+ *lemma* is_closed.Sup_mem
- \+ *lemma* is_closed.Inf_mem
- \+ *lemma* map_Sup_of_continuous_at_of_monotone'
- \+ *lemma* map_Sup_of_continuous_at_of_monotone
- \+ *lemma* map_supr_of_continuous_at_of_monotone'
- \+ *lemma* map_supr_of_continuous_at_of_monotone
- \+ *lemma* map_Inf_of_continuous_at_of_monotone'
- \+ *lemma* map_Inf_of_continuous_at_of_monotone
- \+ *lemma* map_infi_of_continuous_at_of_monotone'
- \+ *lemma* map_infi_of_continuous_at_of_monotone
- \+ *lemma* is_closed.cSup_mem
- \+ *lemma* is_closed.cInf_mem
- \+ *lemma* map_cSup_of_continuous_at_of_monotone
- \+ *lemma* map_csupr_of_continuous_at_of_monotone
- \+ *lemma* map_cInf_of_continuous_at_of_monotone
- \+ *lemma* map_cinfi_of_continuous_at_of_monotone
- \- *lemma* Sup_mem_of_is_closed
- \- *lemma* Inf_mem_of_is_closed
- \- *lemma* Sup_of_continuous'
- \- *lemma* Sup_of_continuous
- \- *lemma* supr_of_continuous'
- \- *lemma* supr_of_continuous
- \- *lemma* Inf_of_continuous'
- \- *lemma* Inf_of_continuous
- \- *lemma* infi_of_continuous'
- \- *lemma* infi_of_continuous
- \- *lemma* cSup_mem_of_is_closed
- \- *lemma* cInf_mem_of_is_closed
- \- *lemma* cSup_of_cSup_of_monotone_of_continuous
- \- *lemma* csupr_of_csupr_of_monotone_of_continuous
- \- *lemma* cInf_of_cInf_of_monotone_of_continuous
- \- *lemma* cinfi_of_cinfi_of_monotone_of_continuous

Modified src/topology/instances/ennreal.lean
- \+ *lemma* infi_mul_left
- \+ *lemma* infi_mul_right

Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean
- \+/\- *lemma* HD_below_aux1
- \+/\- *lemma* HD_below_aux2
- \+/\- *lemma* HD_candidates_b_dist_le
- \+/\- *def* HD

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
- \+ *lemma* vsub_mem_vsub_set
- \+ *lemma* vsub_set_mono

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* vsub_set_subset_vector_span
- \+ *lemma* vsub_mem_vector_span
- \+ *lemma* subset_span_points
- \+ *lemma* direction_eq_vector_span
- \+ *lemma* direction_of_nonempty_eq_direction
- \+ *lemma* coe_direction_eq_vsub_set
- \+ *lemma* mem_direction_iff_eq_vsub
- \+ *lemma* vadd_mem_of_mem_direction
- \+ *lemma* vsub_mem_direction
- \+ *lemma* self_mem_mk'
- \+ *lemma* vadd_mem_mk'
- \+ *lemma* mk'_nonempty
- \+ *lemma* direction_mk'
- \+ *lemma* mk'_eq
- \+ *lemma* coe_affine_span
- \+ *lemma* direction_affine_span
- \+ *lemma* mem_affine_span
- \- *lemma* direction_mk_of_point_of_direction
- \- *lemma* mem_mk_of_point_of_direction
- \- *lemma* mk_of_point_of_direction_eq
- \- *lemma* affine_span_coe
- \- *lemma* affine_span_mem
- \+ *def* direction
- \+ *def* direction_of_nonempty
- \+ *def* mk'
- \+/\- *def* affine_span
- \- *def* mk_of_point_of_direction



## [2020-06-30 05:20:57](https://github.com/leanprover-community/mathlib/commit/e250eb4)
feat(category/schur): a small corollary of the baby schur's lemma ([#3239](https://github.com/leanprover-community/mathlib/pull/3239))
#### Estimated changes
Modified src/category_theory/schur.lean
- \+ *def* is_iso_equiv_nonzero

Modified src/category_theory/simple.lean
- \+ *lemma* id_nonzero



## [2020-06-30 05:20:54](https://github.com/leanprover-community/mathlib/commit/d788d4b)
chore(data/set/intervals): split `I??_union_I??_eq_I??` ([#3237](https://github.com/leanprover-community/mathlib/pull/3237))
For each lemma `I??_union_I??_eq_I??` add a lemma
`I??_subset_I??_union_I??` with no assumptions.
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioi_subset_Ioo_union_Ici
- \+ *lemma* Ici_subset_Ico_union_Ici
- \+ *lemma* Ico_union_Ici_eq_Ici
- \+ *lemma* Ioi_subset_Ioc_union_Ioi
- \+ *lemma* Ici_subset_Icc_union_Ioi
- \+ *lemma* Icc_union_Ioi_eq_Ici
- \+ *lemma* Ioi_subset_Ioc_union_Ici
- \+/\- *lemma* Ioc_union_Ici_eq_Ioi
- \+ *lemma* Ici_subset_Icc_union_Ici
- \+ *lemma* Icc_union_Ici_eq_Ici
- \+ *lemma* Iic_subset_Iio_union_Icc
- \+ *lemma* Iio_subset_Iio_union_Ico
- \+ *lemma* Iic_subset_Iic_union_Ioc
- \+ *lemma* Iio_subset_Iic_union_Ioo
- \+/\- *lemma* Iic_union_Ioo_eq_Iio
- \+ *lemma* Iic_subset_Iic_union_Icc
- \+/\- *lemma* Iic_union_Icc_eq_Iic
- \+ *lemma* Iio_subset_Iic_union_Ico
- \+/\- *lemma* Iic_union_Ico_eq_Iio
- \+ *lemma* Ioo_subset_Ioo_union_Ici
- \+/\- *lemma* Ioo_union_Ico_eq_Ioo
- \+ *lemma* Ico_subset_Ico_union_Ico
- \+/\- *lemma* Ico_union_Ico_eq_Ico
- \+ *lemma* Icc_subset_Ico_union_Icc
- \+/\- *lemma* Ico_union_Icc_eq_Icc
- \+ *lemma* Ioc_subset_Ioo_union_Icc
- \+/\- *lemma* Ioo_union_Icc_eq_Ioc
- \+ *lemma* Ioo_subset_Ioc_union_Ioo
- \+/\- *lemma* Ioc_union_Ioo_eq_Ioo
- \+ *lemma* Ico_subset_Icc_union_Ioo
- \+/\- *lemma* Icc_union_Ioo_eq_Ico
- \+ *lemma* Icc_subset_Icc_union_Ioc
- \+/\- *lemma* Icc_union_Ioc_eq_Icc
- \+ *lemma* Ioc_subset_Ioc_union_Ioc
- \+/\- *lemma* Ioc_union_Ioc_eq_Ioc
- \+ *lemma* Ioo_subset_Ioc_union_Ico
- \+/\- *lemma* Ioc_union_Ico_eq_Ioo
- \+ *lemma* Ico_subset_Icc_union_Ico
- \+/\- *lemma* Icc_union_Ico_eq_Ico
- \+ *lemma* Icc_subset_Icc_union_Icc
- \+/\- *lemma* Icc_union_Icc_eq_Icc
- \+ *lemma* Ioc_subset_Ioc_union_Icc
- \+/\- *lemma* Ioc_union_Icc_eq_Ioc
- \- *lemma* Icc_union_Ici_eq_Ioi
- \- *lemma* Ico_union_Ici_eq_Ioi
- \- *lemma* Icc_union_Ioi_eq_Ioi



## [2020-06-30 05:20:51](https://github.com/leanprover-community/mathlib/commit/af53c9d)
chore(algebra/ring): move some classes to `group_with_zero` ([#3232](https://github.com/leanprover-community/mathlib/pull/3232))
Move `nonzero`, `mul_zero_class` and `no_zero_divisors` to
`group_with_zero`: these classes don't need `(+)`.
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/algebra/group_with_zero.lean
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* zero_ne_one
- \+ *lemma* one_ne_zero
- \+ *lemma* eq_zero_of_mul_self_eq_zero
- \+ *lemma* mul_self_eq_zero
- \+ *lemma* zero_eq_mul_self
- \+ *lemma* zero_right
- \+ *lemma* zero_left
- \+ *theorem* mul_eq_zero
- \+ *theorem* zero_eq_mul
- \+ *theorem* mul_ne_zero_iff
- \+ *theorem* mul_ne_zero
- \+ *theorem* mul_eq_zero_comm
- \+ *theorem* mul_ne_zero_comm
- \+ *theorem* zero_right
- \+ *theorem* zero_left

Modified src/algebra/ring.lean
- \+/\- *lemma* left_distrib
- \+/\- *lemma* right_distrib
- \- *lemma* zero_mul
- \- *lemma* mul_zero
- \- *lemma* zero_ne_one
- \- *lemma* one_ne_zero
- \- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \- *lemma* eq_zero_of_mul_self_eq_zero
- \- *lemma* mul_self_eq_zero
- \- *lemma* zero_eq_mul_self
- \- *lemma* zero_right
- \- *lemma* zero_left
- \- *theorem* mul_eq_zero
- \- *theorem* zero_eq_mul
- \- *theorem* mul_ne_zero_iff
- \- *theorem* mul_ne_zero
- \- *theorem* mul_eq_zero_comm
- \- *theorem* mul_ne_zero_comm
- \- *theorem* zero_right
- \- *theorem* zero_left

Modified src/data/real/hyperreal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean




## [2020-06-30 05:20:45](https://github.com/leanprover-community/mathlib/commit/da481e7)
chore(data/polynomial): partial move from is_ring_hom to ring_hom ([#3213](https://github.com/leanprover-community/mathlib/pull/3213))
This does not attempt to do a complete refactor of `polynomial.lean` and `mv_polynomial.lean` to remove use of `is_ring_hom`, but only to fix `eval₂` which we need for the current work on Cayley-Hamilton.
Having struggled with these two files for the last few days, I'm keen to get them cleaned up, so I'll promise to return to this more thoroughly in a later PR.
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+/\- *def* C

Modified src/data/polynomial.lean
- \+ *lemma* eval₂_monomial
- \+ *lemma* eval₂_X_pow
- \+/\- *lemma* eval₂_pow
- \+/\- *lemma* eval₂_hom
- \+/\- *lemma* eval₂_comp
- \+/\- *lemma* eval₂_map
- \+/\- *lemma* eval_map
- \+/\- *lemma* hom_eval₂
- \+/\- *lemma* eval₂_neg
- \+/\- *lemma* eval₂_sub
- \+/\- *def* eval
- \+/\- *def* map

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
- \+/\- *def* to_alg_equiv

Modified src/algebra/category/CommRing/adjunctions.lean
- \+/\- *def* free

Modified src/algebra/category/CommRing/basic.lean
- \+/\- *def* Ring_iso_to_ring_equiv
- \+/\- *def* CommRing_iso_to_ring_equiv

Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/limits.lean
- \+/\- *def* limit_π_ring_hom
- \+/\- *def* limit
- \+/\- *def* limit_is_limit

Modified src/algebra/category/Group/adjunctions.lean
- \+/\- *def* free

Modified src/algebra/category/Group/basic.lean
- \+/\- *def* Group_iso_to_mul_equiv
- \+/\- *def* CommGroup_iso_to_mul_equiv

Modified src/algebra/category/Group/biproducts.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Group/limits.lean
- \+/\- *def* limit_π_add_monoid_hom
- \+/\- *def* limit
- \+/\- *def* limit_is_limit

Modified src/algebra/category/Group/preadditive.lean


Modified src/algebra/category/Group/zero.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* to_linear_equiv

Modified src/algebra/category/Module/monoidal.lean
- \+/\- *lemma* left_unitor_hom

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* Mon_iso_to_mul_equiv
- \+/\- *def* CommMon_iso_to_mul_equiv

Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/homology/chain_complex.lean
- \+/\- *lemma* d_squared

Modified src/algebra/homology/homology.lean
- \+/\- *lemma* kernel_map_id
- \+/\- *lemma* kernel_map_comp
- \+/\- *lemma* image_map_ι
- \+/\- *lemma* induced_maps_commute
- \+/\- *lemma* cohomology_map_condition
- \+/\- *lemma* cohomology_map_id
- \+/\- *lemma* cohomology_map_comp
- \+/\- *def* kernel_functor
- \+/\- *def* cohomology_map
- \+/\- *def* cohomology_functor

Modified src/algebraic_geometry/presheafed_space.lean
- \+/\- *lemma* as_coe
- \+/\- *lemma* ext
- \+/\- *lemma* hom_mk_coe
- \+/\- *lemma* f_as_coe
- \+/\- *lemma* id_coe
- \+/\- *lemma* id_coe_fn
- \+/\- *lemma* comp_coe
- \+/\- *lemma* id_c
- \+/\- *lemma* id_c_app
- \+/\- *lemma* comp_c_app
- \+/\- *lemma* map_presheaf_obj_X
- \+/\- *lemma* map_presheaf_obj_𝒪
- \+/\- *lemma* map_presheaf_map_f
- \+/\- *lemma* map_presheaf_map_c
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* forget
- \+/\- *def* map_presheaf

Modified src/algebraic_geometry/stalks.lean
- \+/\- *lemma* id
- \+/\- *lemma* comp
- \+/\- *def* stalk
- \+/\- *def* stalk_map

Modified src/category_theory/abelian/basic.lean
- \+/\- *def* has_pullbacks
- \+/\- *def* has_pushouts

Modified src/category_theory/action.lean


Modified src/category_theory/category/Rel.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* binary_product_exponentiable
- \+/\- *def* terminal_exponentiable
- \+/\- *def* zero_mul
- \+/\- *def* mul_zero
- \+/\- *def* pow_zero
- \+/\- *def* prod_coprod_distrib

Modified src/category_theory/conj.lean
- \+/\- *lemma* refl_conj

Modified src/category_theory/differential_object.lean
- \+/\- *lemma* id_f
- \+/\- *lemma* comp_f
- \+/\- *lemma* zero_f
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* forget

Modified src/category_theory/elements.lean


Modified src/category_theory/endomorphism.lean
- \+/\- *def* End

Modified src/category_theory/epi_mono.lean
- \+/\- *def* retraction
- \+/\- *def* section_

Modified src/category_theory/graded_object.lean
- \+/\- *lemma* zero_apply

Modified src/category_theory/groupoid.lean
- \+/\- *def* groupoid.of_is_iso

Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean
- \+/\- *def* functor_category_is_colimit_cocone

Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *lemma* limit.map_pre'
- \+/\- *lemma* colimit.pre_map'

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean
- \+/\- *def* over_product_of_wide_pullback
- \+/\- *def* over_binary_product_of_pullback
- \+/\- *def* over_products_of_wide_pullbacks
- \+/\- *def* over_finite_products_of_finite_wide_pullbacks

Modified src/category_theory/limits/preserves.lean
- \+/\- *def* preserves_limit_iso
- \+/\- *def* preserves_colimit_iso

Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* biproduct.hom_ext
- \+/\- *lemma* biproduct.hom_ext'
- \+/\- *lemma* biproduct.map_eq_map'
- \+/\- *lemma* biproduct.inl_map
- \+/\- *lemma* to_cone_X
- \+/\- *lemma* to_cone_π_app_left
- \+/\- *lemma* to_cone_π_app_right
- \+/\- *lemma* to_cocone_X
- \+/\- *lemma* to_cocone_ι_app_left
- \+/\- *lemma* to_cocone_ι_app_right
- \+/\- *lemma* biprod.inl_fst
- \+/\- *lemma* biprod.inl_snd
- \+/\- *lemma* biprod.inr_fst
- \+/\- *lemma* biprod.inr_snd
- \+/\- *lemma* biprod.hom_ext
- \+/\- *lemma* biprod.hom_ext'
- \+/\- *lemma* biprod.map_eq_map'
- \+/\- *lemma* biprod.map_fst
- \+/\- *lemma* biprod.map_snd
- \+/\- *lemma* biprod.inl_map
- \+/\- *lemma* biprod.inr_map
- \+/\- *lemma* biproduct.map_eq
- \+/\- *lemma* biprod.map_eq
- \+/\- *def* to_cone
- \+/\- *def* to_cocone
- \+/\- *def* has_binary_biproducts_of_finite_biproducts
- \+/\- *def* biprod_iso
- \+/\- *def* biprod.map_iso
- \+/\- *def* has_biproduct.of_has_product
- \+/\- *def* has_biproduct.of_has_coproduct
- \+/\- *def* has_binary_biproduct.of_has_binary_product
- \+/\- *def* has_binary_biproducts.of_has_binary_products
- \+/\- *def* has_binary_biproduct.of_has_binary_coproduct
- \+/\- *def* has_binary_biproducts.of_has_binary_coproducts

Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* walking_parallel_pair_hom_id
- \+/\- *lemma* fork.of_cone_π
- \+/\- *lemma* cofork.of_cocone_ι
- \+/\- *def* parallel_pair
- \+/\- *def* diagram_iso_parallel_pair
- \+/\- *def* has_equalizers_of_has_finite_limits
- \+/\- *def* has_coequalizers_of_has_finite_colimits

Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/kernels.lean
- \+/\- *def* has_kernels_of_has_finite_limits
- \+/\- *def* has_cokernels_of_has_finite_colimits

Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean
- \+/\- *def* cospan
- \+/\- *def* span
- \+/\- *def* has_pullbacks_of_has_finite_limits
- \+/\- *def* has_pushouts_of_has_finite_colimits

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* has_terminal_of_unique
- \+/\- *def* has_initial_of_unique

Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+/\- *def* has_finite_wide_pullbacks_of_has_finite_limits
- \+/\- *def* has_finite_wide_pushouts_of_has_finite_limits

Modified src/category_theory/limits/shapes/zero.lean
- \+/\- *lemma* ext
- \+/\- *def* zero_morphisms_of_zero_object
- \+/\- *def* has_initial
- \+/\- *def* has_terminal

Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/limits.lean
- \+/\- *def* monadic_creates_limits
- \+/\- *def* has_limits_of_reflective

Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functorial.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+/\- *def* monoidal_of_has_finite_products
- \+/\- *def* monoidal_of_has_finite_coproducts

Modified src/category_theory/preadditive.lean
- \+/\- *def* has_equalizers_of_has_kernels
- \+/\- *def* has_coequalizers_of_has_cokernels

Modified src/category_theory/schur.lean
- \+/\- *def* is_iso_of_hom_simple

Modified src/category_theory/shift.lean
- \+/\- *def* shift

Modified src/category_theory/simple.lean
- \+/\- *lemma* simple.ext
- \+/\- *lemma* zero_not_simple
- \+/\- *def* is_iso_of_mono_of_nonzero
- \+/\- *def* simple_of_cosimple
- \+/\- *def* is_iso_of_epi_of_nonzero



## [2020-06-30 03:05:21](https://github.com/leanprover-community/mathlib/commit/056a72a)
perf(linarith): don't repeat nonneg proofs for nat-to-int casts ([#3226](https://github.com/leanprover-community/mathlib/pull/3226))
This performance issue showed up particularly when using `nlinarith` over `nat`s. Proofs that `(n : int) >= 0` were being repeated many times, which led to quadratic blowup in the `nlinarith` preprocessing.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+/\- *lemma* cos_lt_cos_of_nonneg_of_le_pi
- \+/\- *lemma* cos_le_cos_of_nonneg_of_le_pi
- \+/\- *lemma* tan_lt_tan_of_nonneg_of_lt_pi_div_two
- \+/\- *lemma* tan_lt_tan_of_lt_of_lt_pi_div_two

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
- \+ *lemma* inner_weighted_vsub
- \+ *lemma* dist_affine_combination

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* weighted_vsub_apply



## [2020-06-30 01:43:20](https://github.com/leanprover-community/mathlib/commit/4fcd6fd)
chore(*): import expression widgets from core ([#3181](https://github.com/leanprover-community/mathlib/pull/3181))
With widgets, the rendering of the tactic state is implemented in pure Lean code.  I would like to move this part (temporarily) into mathlib to facilitate collaborative improvement and rapid iteration under a mature community review procedure.  (That is, I want other people to tweak it themselves without having to wait a week for the next Lean release to see the effect.)
I didn't need to change anything in the source code (except for adding some doc strings).  So it should be easy to copy it back to core if we want to.
There are no changes required to core for this PR.
#### Estimated changes
Modified src/tactic/core.lean


Created src/tactic/interactive_expr.lean




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
- \+/\- *lemma* sum_compl_apply_inr

Modified src/data/indicator_function.lean
- \+/\- *lemma* indicator_compl

Modified src/data/pfun.lean
- \+/\- *lemma* compl_dom_subset_core
- \+/\- *lemma* core_res
- \+/\- *lemma* core_eq

Modified src/data/real/hyperreal.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* inter_compl_nonempty_iff
- \+/\- *lemma* compl_set_of
- \+/\- *lemma* compl_empty_iff
- \+/\- *lemma* compl_univ_iff
- \+/\- *lemma* nonempty_compl
- \+/\- *lemma* mem_compl_singleton_iff
- \+/\- *lemma* compl_singleton_eq
- \+/\- *lemma* compl_subset_compl
- \+/\- *lemma* subset_compl_singleton_iff
- \+/\- *lemma* diff_compl
- \+/\- *theorem* mem_compl
- \+/\- *theorem* not_mem_of_mem_compl
- \+/\- *theorem* mem_compl_eq
- \+/\- *theorem* mem_compl_iff
- \+/\- *theorem* inter_compl_self
- \+/\- *theorem* compl_inter_self
- \+/\- *theorem* compl_empty
- \+/\- *theorem* compl_union
- \+/\- *theorem* compl_compl
- \+/\- *theorem* compl_inter
- \+/\- *theorem* compl_univ
- \+/\- *theorem* union_eq_compl_compl_inter_compl
- \+/\- *theorem* inter_eq_compl_compl_union_compl
- \+/\- *theorem* union_compl_self
- \+/\- *theorem* compl_union_self
- \+/\- *theorem* compl_subset_comm
- \+/\- *theorem* compl_subset_iff_union
- \+/\- *theorem* subset_compl_comm
- \+/\- *theorem* subset_compl_iff_disjoint
- \+/\- *theorem* inter_subset
- \+/\- *theorem* diff_eq
- \+/\- *theorem* compl_eq_univ_diff
- \+/\- *theorem* preimage_compl
- \+/\- *theorem* image_compl_subset
- \+/\- *theorem* subset_image_compl
- \+/\- *theorem* image_compl_eq
- \+/\- *theorem* compl_image
- \- *theorem* fix_set_compl

Modified src/data/set/disjointed.lean
- \+/\- *def* disjointed

Modified src/data/set/enumerate.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* compl_Iic
- \+/\- *lemma* compl_Ici
- \+/\- *lemma* compl_Iio
- \+/\- *lemma* compl_Ioi

Modified src/data/set/lattice.lean
- \+/\- *theorem* compl_Union
- \+/\- *theorem* compl_Inter
- \+/\- *theorem* Union_eq_comp_Inter_comp
- \+/\- *theorem* Inter_eq_comp_Union_comp
- \+/\- *theorem* compl_bUnion
- \+/\- *theorem* compl_bInter
- \+/\- *theorem* disjoint_compl
- \- *theorem* sub_eq_diff

Modified src/linear_algebra/matrix.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.compl
- \+/\- *lemma* is_measurable.of_compl
- \+/\- *lemma* is_measurable.compl_iff
- \+/\- *lemma* has_compl_iff
- \- *lemma* is_measurable.sub

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* mem_ae_iff

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/order/boolean_algebra.lean
- \+/\- *theorem* inf_compl_eq_bot
- \+/\- *theorem* compl_inf_eq_bot
- \+/\- *theorem* sup_compl_eq_top
- \+/\- *theorem* compl_sup_eq_top
- \+ *theorem* is_compl_compl
- \+ *theorem* is_compl.compl_eq
- \+ *theorem* sdiff_eq
- \+/\- *theorem* compl_unique
- \+/\- *theorem* compl_top
- \+/\- *theorem* compl_bot
- \+/\- *theorem* compl_compl'
- \+/\- *theorem* compl_injective
- \+/\- *theorem* compl_inj_iff
- \+/\- *theorem* compl_inf
- \+/\- *theorem* compl_sup
- \+/\- *theorem* compl_le_compl
- \+/\- *theorem* compl_le_compl_iff_le
- \+/\- *theorem* le_compl_of_le_compl
- \+/\- *theorem* compl_le_of_compl_le
- \+/\- *theorem* compl_le_iff_compl_le
- \+ *theorem* sup_sdiff_same
- \+ *theorem* sdiff_eq_left
- \+ *theorem* sdiff_le_sdiff
- \- *theorem* is_compl_neg
- \- *theorem* is_compl.neg_eq
- \- *theorem* sub_eq
- \- *theorem* sup_sub_same
- \- *theorem* sub_eq_left
- \- *theorem* boolean_algebra.sub_le_sub

Modified src/order/complete_boolean_algebra.lean
- \+/\- *theorem* compl_infi
- \+/\- *theorem* compl_supr
- \+/\- *theorem* compl_Inf
- \+/\- *theorem* compl_Sup

Modified src/order/filter/basic.lean
- \+/\- *lemma* mem_sets_of_eq_bot
- \+/\- *lemma* is_compl_principal
- \+/\- *lemma* inf_principal_eq_bot

Modified src/order/filter/cofinite.lean
- \+/\- *lemma* mem_cofinite

Modified src/order/filter/ultrafilter.lean
- \+/\- *theorem* mem_hyperfilter_of_finite_compl

Modified src/set_theory/cardinal.lean
- \+/\- *lemma* mk_sum_compl

Modified src/set_theory/ordinal.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean
- \+/\- *lemma* is_open_compl_iff
- \+/\- *lemma* is_closed_compl_iff
- \+/\- *lemma* closure_eq_compl_interior_compl
- \+/\- *lemma* interior_compl
- \+/\- *lemma* closure_compl
- \+/\- *lemma* frontier_compl
- \+/\- *lemma* closure_diff
- \+/\- *def* is_closed

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
- \+ *theorem* abs_eq_nat_abs
- \+ *theorem* nat_abs_abs
- \+ *theorem* sign_mul_abs

Modified src/data/nat/basic.lean
- \+ *theorem* mul_self_le_mul_self
- \+ *theorem* mul_self_lt_mul_self
- \+ *theorem* mul_self_le_mul_self_iff
- \+ *theorem* mul_self_lt_mul_self_iff
- \+ *theorem* le_mul_self
- \+ *theorem* eq_of_mul_eq_mul_right
- \+ *theorem* one_add

Modified src/data/nat/sqrt.lean


Deleted src/init_/algebra/default.lean


Deleted src/init_/algebra/norm_num.lean
- \- *lemma* mul_zero
- \- *lemma* zero_mul
- \- *lemma* mul_one
- \- *lemma* mul_bit0
- \- *lemma* mul_bit0_helper
- \- *lemma* mul_bit1
- \- *lemma* mul_bit1_helper
- \- *lemma* subst_into_prod
- \- *lemma* mk_cong
- \- *lemma* neg_add_neg_eq_of_add_add_eq_zero
- \- *lemma* neg_add_neg_helper
- \- *lemma* neg_add_pos_eq_of_eq_add
- \- *lemma* neg_add_pos_helper1
- \- *lemma* neg_add_pos_helper2
- \- *lemma* pos_add_neg_helper
- \- *lemma* subst_into_subtr
- \- *lemma* neg_neg_helper
- \- *lemma* neg_mul_neg_helper
- \- *lemma* neg_mul_pos_helper
- \- *lemma* pos_mul_neg_helper
- \- *lemma* div_add_helper
- \- *lemma* add_div_helper
- \- *lemma* div_mul_helper
- \- *lemma* mul_div_helper
- \- *lemma* nonzero_of_div_helper
- \- *lemma* div_helper
- \- *lemma* div_eq_div_helper
- \- *lemma* subst_into_div
- \- *lemma* add_comm_four
- \- *lemma* add_comm_middle
- \- *lemma* bit0_add_bit0
- \- *lemma* bit0_add_bit0_helper
- \- *lemma* bit1_add_bit0
- \- *lemma* bit1_add_bit0_helper
- \- *lemma* bit0_add_bit1
- \- *lemma* bit0_add_bit1_helper
- \- *lemma* bit1_add_bit1
- \- *lemma* bit1_add_bit1_helper
- \- *lemma* bin_add_zero
- \- *lemma* bin_zero_add
- \- *lemma* one_add_bit0
- \- *lemma* bit0_add_one
- \- *lemma* bit1_add_one
- \- *lemma* bit1_add_one_helper
- \- *lemma* one_add_bit1
- \- *lemma* one_add_bit1_helper
- \- *lemma* add1_bit0
- \- *lemma* add1_bit1
- \- *lemma* add1_bit1_helper
- \- *lemma* add1_one
- \- *lemma* add1_zero
- \- *lemma* one_add_one
- \- *lemma* subst_into_sum
- \- *lemma* neg_zero_helper
- \- *lemma* pos_bit0_helper
- \- *lemma* nonneg_bit0_helper
- \- *lemma* pos_bit1_helper
- \- *lemma* nonneg_bit1_helper
- \- *lemma* nonzero_of_pos_helper
- \- *lemma* nonzero_of_neg_helper
- \- *lemma* sub_nat_zero_helper
- \- *lemma* sub_nat_pos_helper
- \- *def* add1

Deleted src/init_/data/int/basic.lean


Deleted src/init_/data/int/order.lean
- \- *theorem* abs_eq_nat_abs
- \- *theorem* nat_abs_abs
- \- *theorem* sign_mul_abs

Deleted src/init_/data/nat/lemmas.lean
- \- *theorem* mul_self_le_mul_self
- \- *theorem* mul_self_lt_mul_self
- \- *theorem* mul_self_le_mul_self_iff
- \- *theorem* mul_self_lt_mul_self_iff
- \- *theorem* le_mul_self
- \- *theorem* eq_of_mul_eq_mul_right
- \- *theorem* one_add

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
- \+/\- *lemma* coe_eq_coe
- \+ *lemma* coe_eq_zero
- \+ *lemma* coe_eq_one
- \+ *lemma* coe_one
- \+ *lemma* coe_zero
- \+ *lemma* coe_inv
- \+ *lemma* coe_neg
- \+ *lemma* coe_add
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+ *lemma* coe_mul
- \+ *lemma* coe_div
- \+ *lemma* coe_sub
- \+/\- *lemma* coe_lt_coe
- \+ *lemma* coe_pos
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_abs
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *lemma* epsilon_lt_pos
- \- *lemma* hyperfilter_ne_bot
- \- *lemma* hyperfilter_ne_bot'
- \- *lemma* cast_div
- \+/\- *theorem* is_st_Sup
- \+/\- *theorem* st_eq_Sup
- \+/\- *theorem* not_real_of_infinite
- \+/\- *def* hyperreal
- \+/\- *def* is_st

Modified src/order/filter/filter_product.lean
- \+ *lemma* const_div
- \+ *lemma* coe_lt
- \+ *lemma* coe_pos
- \+ *lemma* const_lt
- \+/\- *lemma* lt_def
- \+ *lemma* const_max
- \+ *lemma* const_min
- \+ *lemma* const_abs
- \- *lemma* of_seq_zero
- \- *lemma* of_seq_add
- \- *lemma* of_seq_neg
- \- *lemma* of_seq_one
- \- *lemma* of_seq_mul
- \- *lemma* of_seq_inv
- \- *lemma* of_eq_coe
- \- *lemma* coe_inj
- \- *lemma* of_eq
- \- *lemma* of_ne
- \- *lemma* of_eq_zero
- \- *lemma* of_ne_zero
- \- *lemma* of_zero
- \- *lemma* of_add
- \- *lemma* of_bit0
- \- *lemma* of_bit1
- \- *lemma* of_neg
- \- *lemma* of_sub
- \- *lemma* of_one
- \- *lemma* of_mul
- \- *lemma* of_inv
- \- *lemma* of_div
- \- *lemma* of_rel_of_rel
- \- *lemma* of_rel
- \- *lemma* of_rel_of_rel₂
- \- *lemma* of_rel₂
- \- *lemma* of_le_of_le
- \- *lemma* of_le
- \- *lemma* lt_def'
- \- *lemma* of_lt_of_lt
- \- *lemma* of_lt
- \- *lemma* lift_id
- \- *lemma* of_max
- \- *lemma* of_min
- \- *lemma* of_abs
- \- *theorem* of_injective
- \- *theorem* of_seq_fun
- \- *theorem* of_seq_fun₂
- \- *def* bigly_equal
- \- *def* filterprod
- \- *def* of_seq
- \- *def* of
- \- *def* lift
- \- *def* lift₂
- \- *def* lift_rel
- \- *def* lift_rel₂

Created src/order/filter/germ.lean
- \+ *lemma* const_eventually_eq'
- \+ *lemma* const_eventually_eq
- \+ *lemma* eventually_eq.comp_tendsto
- \+ *lemma* eventually_le.congr
- \+ *lemma* eventually_le_congr
- \+ *lemma* eventually_eq.le
- \+ *lemma* eventually_le.refl
- \+ *lemma* eventually_le.trans
- \+ *lemma* eventually_eq.trans_le
- \+ *lemma* eventually_le.trans_eq
- \+ *lemma* eventually_le.antisymm
- \+ *lemma* quot_mk_eq_coe
- \+ *lemma* mk'_eq_coe
- \+ *lemma* induction_on
- \+ *lemma* induction_on₂
- \+ *lemma* induction_on₃
- \+ *lemma* map'_coe
- \+ *lemma* coe_eq
- \+ *lemma* map_coe
- \+ *lemma* map_id
- \+ *lemma* map_map
- \+ *lemma* coe_tendsto
- \+ *lemma* coe_comp_tendsto'
- \+ *lemma* coe_comp_tendsto
- \+ *lemma* comp_tendsto'_coe
- \+ *lemma* const_inj
- \+ *lemma* map_const
- \+ *lemma* map₂_const
- \+ *lemma* const_comp_tendsto
- \+ *lemma* const_comp_tendsto'
- \+ *lemma* lift_pred_coe
- \+ *lemma* lift_pred_const
- \+ *lemma* lift_pred_const_iff
- \+ *lemma* lift_rel_coe
- \+ *lemma* lift_rel_const
- \+ *lemma* lift_rel_const_iff
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_coe_mul_hom
- \+ *lemma* coe_inv
- \+ *lemma* coe_sub
- \+ *lemma* coe_coe_ring_hom
- \+ *lemma* coe_smul
- \+ *lemma* coe_smul'
- \+ *lemma* coe_le
- \+ *lemma* const_le
- \+ *lemma* const_le_iff
- \+ *lemma* const_bot
- \+ *lemma* const_top
- \+ *lemma* const_sup
- \+ *lemma* const_inf
- \+ *def* eventually_le
- \+ *def* germ_setoid
- \+ *def* germ
- \+ *def* map'
- \+ *def* lift_on
- \+ *def* map
- \+ *def* map₂
- \+ *def* comp_tendsto'
- \+ *def* comp_tendsto
- \+ *def* lift_pred
- \+ *def* lift_rel
- \+ *def* coe_mul_hom
- \+ *def* coe_ring_hom

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* is_ultrafilter.em
- \+ *lemma* is_ultrafilter.eventually_or
- \+ *lemma* is_ultrafilter.eventually_not
- \+ *lemma* is_ultrafilter.eventually_imp
- \+ *lemma* hyperfilter_ne_bot
- \+ *lemma* bot_ne_hyperfilter



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
- \+/\- *lemma* sum_smul_index

Modified src/data/monoid_algebra.lean
- \+ *def* algebra_map'

Modified src/data/polynomial.lean
- \+ *lemma* X_mul
- \+ *lemma* X_pow_mul
- \+ *lemma* X_pow_mul_assoc
- \+ *lemma* C_eq_nat_cast
- \+/\- *lemma* eval₂_smul
- \+ *lemma* eval_nat_cast
- \+ *lemma* eval_smul
- \+/\- *lemma* add_comp
- \+/\- *lemma* eval₂_mul
- \+/\- *lemma* coe_eval₂_ring_hom
- \+/\- *lemma* eval₂_pow
- \+/\- *lemma* eval_mul
- \+/\- *lemma* eval_pow
- \+/\- *lemma* eval₂_hom
- \+/\- *lemma* root_mul_left_of_is_root
- \+/\- *lemma* root_mul_right_of_is_root
- \+/\- *lemma* eval₂_comp
- \+/\- *lemma* eval_comp
- \+/\- *lemma* map_map
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* monic_map
- \+/\- *lemma* zero_le_degree_iff
- \+/\- *lemma* coeff_mul_X_zero
- \+/\- *lemma* degree_nonneg_iff_ne_zero
- \+/\- *lemma* nat_degree_eq_zero_iff_degree_le_zero
- \+/\- *lemma* map_mul
- \+/\- *lemma* map_pow
- \+/\- *lemma* mem_map_range
- \+/\- *lemma* eval₂_map
- \+/\- *lemma* eval_map
- \+/\- *lemma* hom_eval₂
- \+/\- *lemma* degree_pos_of_root
- \+/\- *lemma* eq_C_of_nat_degree_le_zero
- \+/\- *lemma* nat_degree_pos_iff_degree_pos
- \+/\- *lemma* nat_degree_pos_of_eval₂_root
- \+/\- *lemma* degree_pos_of_eval₂_root
- \+ *lemma* C_eq_int_cast
- \+/\- *lemma* C_neg
- \+/\- *lemma* C_sub
- \+ *lemma* eval_int_cast
- \+/\- *lemma* eval₂_neg
- \+/\- *lemma* eval₂_sub
- \+/\- *lemma* mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* derivative_neg
- \+/\- *lemma* derivative_sub
- \+/\- *lemma* derivative_smul
- \- *lemma* nat_cast_eq_C
- \- *lemma* int_cast_eq_C
- \+/\- *theorem* monic_X_sub_C
- \+/\- *theorem* monic_X_pow_sub
- \+/\- *theorem* degree_mod_by_monic_le
- \+/\- *def* C
- \+/\- *def* eval₂_ring_hom
- \+/\- *def* derivative_hom

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
- \+ *lemma* walking_pair.swap_apply_left
- \+ *lemma* walking_pair.swap_apply_right
- \+ *lemma* walking_pair.swap_symm_apply_tt
- \+ *lemma* walking_pair.swap_symm_apply_ff
- \+ *lemma* walking_pair.equiv_bool_apply_left
- \+ *lemma* walking_pair.equiv_bool_apply_right
- \+ *lemma* walking_pair.equiv_bool_symm_apply_tt
- \+ *lemma* walking_pair.equiv_bool_symm_apply_ff
- \+/\- *lemma* prod.hom_ext
- \+/\- *lemma* coprod.hom_ext
- \+/\- *lemma* prod.lift_fst
- \+/\- *lemma* prod.lift_snd
- \+/\- *lemma* prod.lift_comp_comp
- \+/\- *lemma* coprod.inl_desc
- \+/\- *lemma* coprod.inr_desc
- \+/\- *lemma* coprod.desc_comp_comp
- \+ *lemma* prod.map_iso_hom
- \+ *lemma* prod.map_iso_inv
- \+ *lemma* coprod.map_iso_hom
- \+ *lemma* coprod.map_iso_inv
- \+ *def* walking_pair.swap
- \+ *def* walking_pair.equiv_bool
- \+/\- *def* prod.lift'
- \+/\- *def* coprod.desc'

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* bicone_ι_π_self
- \+ *lemma* bicone_ι_π_ne
- \+ *lemma* biproduct.ι_π
- \+ *lemma* biproduct.ι_π_self
- \+ *lemma* biproduct.ι_π_ne
- \+ *lemma* biproduct.hom_ext
- \+ *lemma* biproduct.hom_ext'
- \+ *lemma* biproduct.map_eq_map'
- \+ *lemma* biproduct.inl_map
- \+ *lemma* to_cone_X
- \+ *lemma* to_cone_π_app_left
- \+ *lemma* to_cone_π_app_right
- \+ *lemma* to_cocone_X
- \+ *lemma* to_cocone_ι_app_left
- \+ *lemma* to_cocone_ι_app_right
- \+/\- *lemma* biprod.inl_fst
- \+/\- *lemma* biprod.inl_snd
- \+/\- *lemma* biprod.inr_fst
- \+/\- *lemma* biprod.inr_snd
- \+/\- *lemma* biprod.hom_ext
- \+/\- *lemma* biprod.hom_ext'
- \+ *lemma* biprod.map_eq_map'
- \+ *lemma* biprod.map_fst
- \+ *lemma* biprod.map_snd
- \+ *lemma* biprod.inl_map
- \+ *lemma* biprod.inr_map
- \+ *lemma* biprod.braiding'_eq_braiding
- \+ *lemma* biprod.braid_natural
- \+ *lemma* biprod.braiding_map_braiding
- \+ *lemma* biprod.symmetry'
- \+ *lemma* biprod.symmetry
- \+ *lemma* biproduct.total
- \+ *lemma* biproduct.lift_eq
- \+ *lemma* biproduct.desc_eq
- \+ *lemma* biproduct.lift_desc
- \+ *lemma* biproduct.map_eq
- \+/\- *lemma* biprod.total
- \+ *lemma* biprod.lift_eq
- \+ *lemma* biprod.desc_eq
- \+/\- *lemma* biprod.lift_desc
- \+ *lemma* biprod.map_eq
- \- *lemma* biprod.inl_add_inr
- \- *lemma* biprod.fst_add_snd
- \+/\- *def* to_cone
- \+/\- *def* to_cocone
- \+/\- *def* biproduct_iso
- \+ *def* to_binary_bicone
- \+ *def* to_binary_bicone_is_limit
- \+ *def* to_binary_bicone_is_colimit
- \+ *def* has_binary_biproducts_of_finite_biproducts
- \+ *def* biprod.map_iso
- \+ *def* biprod.braiding
- \+ *def* biprod.braiding'
- \+ *def* has_biproduct_of_total
- \+ *def* has_biproduct.of_has_product
- \+ *def* has_biproduct.of_has_coproduct
- \+ *def* has_binary_biproduct_of_total
- \+ *def* has_binary_biproduct.of_has_binary_product
- \+ *def* has_binary_biproducts.of_has_binary_products
- \+ *def* has_binary_biproduct.of_has_binary_coproduct
- \+ *def* has_binary_biproducts.of_has_binary_coproducts
- \- *def* has_preadditive_binary_biproduct.of_has_limit_pair
- \- *def* has_preadditive_binary_biproduct.of_has_colimit_pair
- \- *def* has_preadditive_binary_biproducts_of_has_binary_products
- \- *def* has_preadditive_binary_biproducts_of_has_binary_coproducts

Modified src/category_theory/limits/shapes/products.lean




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
- \+ *lemma* prod_insert_one
- \+ *lemma* prod_subtype_eq_prod_filter
- \+ *lemma* prod_subtype_of_mem
- \+ *lemma* prod_subtype_map_embedding

Modified src/data/finset.lean
- \+/\- *lemma* filter_true
- \+ *lemma* filter_true_of_mem
- \+ *lemma* subtype_map
- \+ *lemma* subtype_map_of_mem
- \+ *lemma* not_mem_map_subtype_of_not_property

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* weighted_vsub_of_point_erase
- \+ *lemma* weighted_vsub_of_point_insert
- \+ *lemma* affine_independent_of_subsingleton
- \+ *lemma* affine_independent_iff_linear_independent_vsub
- \+ *def* affine_independent



## [2020-06-29 12:45:16](https://github.com/leanprover-community/mathlib/commit/36ce13f)
chore(finset/nat/antidiagonal): simplify some proofs ([#3225](https://github.com/leanprover-community/mathlib/pull/3225))
Replace some proofs with `rfl`, and avoid `multiset.to_finset` when there is a `nodup` available.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* card_mk

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
- \+ *lemma* ite_tmul
- \+ *lemma* tmul_ite



## [2020-06-29 06:59:46](https://github.com/leanprover-community/mathlib/commit/ca44926)
chore(ring_theory/tensor_product): missing simp lemmas ([#3215](https://github.com/leanprover-community/mathlib/pull/3215))
A few missing `simp` lemmas.
#### Estimated changes
Modified src/ring_theory/tensor_product.lean
- \+ *lemma* tmul_mul_tmul
- \+ *lemma* tmul_pow
- \+ *lemma* include_left_apply
- \+ *lemma* include_right_apply
- \+ *lemma* alg_hom_of_linear_map_tensor_product_apply
- \- *lemma* mul_tmul



## [2020-06-29 04:45:10](https://github.com/leanprover-community/mathlib/commit/a443d8b)
feat(simp_nf): instructions for linter timeout ([#3205](https://github.com/leanprover-community/mathlib/pull/3205))
#### Estimated changes
Modified src/tactic/lint/simp.lean




## [2020-06-29 04:21:12](https://github.com/leanprover-community/mathlib/commit/9a1c0a6)
feat(data/padics/padic_norm) Fix namespacing of padic_val_nat ([#3207](https://github.com/leanprover-community/mathlib/pull/3207))
No longer need we `padic_val_rat.padic_val_nat`.
#### Estimated changes
Modified src/data/padics/padic_norm.lean




## [2020-06-29 03:57:10](https://github.com/leanprover-community/mathlib/commit/9acf590)
feat(data/matrix/notation): smul matrix lemmas ([#3208](https://github.com/leanprover-community/mathlib/pull/3208))
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+ *lemma* smul_mat_empty
- \+ *lemma* smul_mat_cons



## [2020-06-29 03:20:59](https://github.com/leanprover-community/mathlib/commit/d2b46ab)
chore(category_theory/punit): use discrete punit instead of punit ([#3201](https://github.com/leanprover-community/mathlib/pull/3201))
Analogous to [#3191](https://github.com/leanprover-community/mathlib/pull/3191) for `punit`. I also removed some `simp` lemmas which can be generated instead by `[simps]`.
#### Estimated changes
Modified src/algebra/homology/chain_complex.lean


Modified src/category_theory/comma.lean
- \- *lemma* fst_obj
- \- *lemma* snd_obj
- \- *lemma* fst_map
- \- *lemma* snd_map
- \- *lemma* map_left_obj_left
- \- *lemma* map_left_obj_right
- \- *lemma* map_left_obj_hom
- \- *lemma* map_left_map_left
- \- *lemma* map_left_map_right
- \- *lemma* map_left_id_hom_app_left
- \- *lemma* map_left_id_hom_app_right
- \- *lemma* map_left_id_inv_app_left
- \- *lemma* map_left_id_inv_app_right
- \- *lemma* map_left_comp_hom_app_left
- \- *lemma* map_left_comp_hom_app_right
- \- *lemma* map_left_comp_inv_app_left
- \- *lemma* map_left_comp_inv_app_right
- \- *lemma* map_right_obj_left
- \- *lemma* map_right_obj_right
- \- *lemma* map_right_obj_hom
- \- *lemma* map_right_map_left
- \- *lemma* map_right_map_right
- \- *lemma* map_right_id_hom_app_left
- \- *lemma* map_right_id_hom_app_right
- \- *lemma* map_right_id_inv_app_left
- \- *lemma* map_right_id_inv_app_right
- \- *lemma* map_right_comp_hom_app_left
- \- *lemma* map_right_comp_hom_app_right
- \- *lemma* map_right_comp_inv_app_left
- \- *lemma* map_right_comp_inv_app_right
- \- *lemma* over_morphism_right
- \- *lemma* hom_mk_left
- \- *lemma* under_morphism_left
- \- *lemma* mk_right
- \- *lemma* mk_hom
- \- *lemma* hom_mk_right
- \- *lemma* hom_mk'_left
- \- *lemma* hom_mk'_right
- \+/\- *def* over
- \+/\- *def* map
- \+/\- *def* under

Modified src/category_theory/connected.lean
- \+ *def* discrete_connected_equiv_punit

Modified src/category_theory/discrete_category.lean
- \+ *def* equiv_of_equivalence

Modified src/category_theory/elements.lean
- \+ *lemma* comma_equivalence_functor
- \+ *lemma* comma_equivalence_inverse
- \- *lemma* π_obj
- \- *lemma* π_map
- \+/\- *def* to_comma
- \+/\- *def* from_comma
- \+/\- *def* comma_equivalence

Modified src/category_theory/groupoid.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/punit.lean
- \+ *lemma* punit_ext'
- \- *lemma* star_obj
- \- *lemma* star_map
- \+/\- *def* star
- \+ *def* punit_ext
- \+ *def* equiv



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
- \- *lemma* mem_carrier
- \- *lemma* mem_coe
- \- *lemma* coe_coe
- \- *lemma* coe_copy
- \- *lemma* copy_eq
- \- *lemma* list_prod_mem
- \- *lemma* multiset_prod_mem
- \- *lemma* prod_mem
- \- *lemma* pow_mem
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* coe_eq_coe
- \- *lemma* le_def
- \- *lemma* coe_subset_coe
- \- *lemma* coe_ssubset_coe
- \- *lemma* mem_bot
- \- *lemma* mem_top
- \- *lemma* coe_top
- \- *lemma* coe_bot
- \- *lemma* coe_inf
- \- *lemma* mem_inf
- \- *lemma* coe_Inf
- \- *lemma* mem_Inf
- \- *lemma* mem_infi
- \- *lemma* coe_infi
- \- *lemma* mem_closure
- \- *lemma* subset_closure
- \- *lemma* closure_le
- \- *lemma* closure_mono
- \- *lemma* closure_eq_of_le
- \- *lemma* closure_induction
- \- *lemma* closure_eq
- \- *lemma* closure_empty
- \- *lemma* closure_univ
- \- *lemma* closure_union
- \- *lemma* closure_Union
- \- *lemma* mem_supr_of_directed
- \- *lemma* coe_supr_of_directed
- \- *lemma* mem_Sup_of_directed_on
- \- *lemma* coe_Sup_of_directed_on
- \- *lemma* coe_comap
- \- *lemma* mem_comap
- \- *lemma* comap_comap
- \- *lemma* coe_map
- \- *lemma* mem_map
- \- *lemma* map_map
- \- *lemma* map_le_iff_le_comap
- \- *lemma* gc_map_comap
- \- *lemma* map_sup
- \- *lemma* map_supr
- \- *lemma* comap_inf
- \- *lemma* comap_infi
- \- *lemma* map_bot
- \- *lemma* comap_top
- \- *lemma* map_id
- \- *lemma* coe_prod
- \- *lemma* mem_prod
- \- *lemma* prod_mono
- \- *lemma* prod_mono_right
- \- *lemma* prod_mono_left
- \- *lemma* prod_top
- \- *lemma* top_prod
- \- *lemma* top_prod_top
- \- *lemma* bot_prod_bot
- \- *lemma* coe_mrange
- \- *lemma* mem_mrange
- \- *lemma* map_mrange
- \- *lemma* mrestrict_apply
- \- *lemma* coe_mrange_restrict
- \- *lemma* mrange_top_iff_surjective
- \- *lemma* mrange_top_of_surjective
- \- *lemma* eq_on_mclosure
- \- *lemma* eq_of_eq_on_mtop
- \- *lemma* eq_of_eq_on_mdense
- \- *lemma* mclosure_preimage_le
- \- *lemma* map_mclosure
- \- *lemma* range_subtype
- \- *lemma* closure_singleton_eq
- \- *lemma* mem_closure_singleton
- \- *lemma* closure_eq_mrange
- \- *lemma* exists_list_of_mem_closure
- \- *lemma* map_inl
- \- *lemma* map_inr
- \- *lemma* range_inl
- \- *lemma* range_inr
- \- *lemma* range_inl'
- \- *lemma* range_inr'
- \- *lemma* range_fst
- \- *lemma* range_snd
- \- *lemma* prod_bot_sup_bot_prod
- \- *lemma* range_inl_sup_range_inr
- \- *lemma* sup_eq_range
- \- *lemma* mem_sup
- \- *lemma* smul_mem
- \- *theorem* ext'
- \- *theorem* ext
- \- *theorem* one_mem
- \- *theorem* mul_mem
- \- *theorem* coe_subtype
- \- *theorem* closure_range_of
- \- *def* submonoid.to_add_submonoid
- \- *def* submonoid.of_add_submonoid
- \- *def* add_submonoid.to_submonoid
- \- *def* add_submonoid.of_submonoid
- \- *def* submonoid.add_submonoid_equiv
- \- *def* copy
- \- *def* subtype
- \- *def* closure
- \- *def* comap
- \- *def* map
- \- *def* prod
- \- *def* prod_equiv
- \- *def* mrange
- \- *def* mrestrict
- \- *def* cod_mrestrict
- \- *def* mrange_restrict
- \- *def* eq_mlocus
- \- *def* inclusion
- \- *def* submonoid_congr

Created src/group_theory/submonoid/basic.lean
- \+ *lemma* mem_carrier
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+ *lemma* coe_eq_coe
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* dense_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* eq_on_mclosure
- \+ *lemma* eq_of_eq_on_mtop
- \+ *lemma* eq_of_eq_on_mdense
- \+ *lemma* coe_of_mdense
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *def* copy
- \+ *def* closure
- \+ *def* eq_mlocus
- \+ *def* of_mdense

Created src/group_theory/submonoid/default.lean


Created src/group_theory/submonoid/membership.lean
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* prod_mem
- \+ *lemma* pow_mem
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* coe_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_Sup_of_directed_on
- \+ *lemma* closure_singleton_eq
- \+ *lemma* mem_closure_singleton
- \+ *lemma* closure_eq_mrange
- \+ *lemma* exists_list_of_mem_closure
- \+ *lemma* sup_eq_range
- \+ *lemma* mem_sup
- \+ *lemma* nsmul_mem
- \+ *theorem* closure_range_of

Created src/group_theory/submonoid/operations.lean
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* map_id
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* bot_prod_bot
- \+ *lemma* map_inl
- \+ *lemma* map_inr
- \+ *lemma* prod_bot_sup_bot_prod
- \+ *lemma* coe_mrange
- \+ *lemma* mem_mrange
- \+ *lemma* map_mrange
- \+ *lemma* mrange_top_iff_surjective
- \+ *lemma* mrange_top_of_surjective
- \+ *lemma* mclosure_preimage_le
- \+ *lemma* map_mclosure
- \+ *lemma* mrestrict_apply
- \+ *lemma* coe_mrange_restrict
- \+ *lemma* mrange_inl
- \+ *lemma* mrange_inr
- \+ *lemma* mrange_inl'
- \+ *lemma* mrange_inr'
- \+ *lemma* mrange_fst
- \+ *lemma* mrange_snd
- \+ *lemma* mrange_inl_sup_mrange_inr
- \+ *lemma* range_subtype
- \+ *theorem* coe_subtype
- \+ *def* submonoid.to_add_submonoid
- \+ *def* submonoid.of_add_submonoid
- \+ *def* add_submonoid.to_submonoid
- \+ *def* add_submonoid.of_submonoid
- \+ *def* submonoid.add_submonoid_equiv
- \+ *def* comap
- \+ *def* map
- \+ *def* subtype
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* mrange
- \+ *def* mrestrict
- \+ *def* cod_mrestrict
- \+ *def* mrange_restrict
- \+ *def* inclusion
- \+ *def* submonoid_congr

Modified src/ring_theory/subsemiring.lean
- \+ *lemma* nsmul_mem
- \- *lemma* smul_mem



## [2020-06-28 22:28:30](https://github.com/leanprover-community/mathlib/commit/4ad82e5)
feat(uniform_space): compact uniform spaces, Heine-Cantor ([#3180](https://github.com/leanprover-community/mathlib/pull/3180))
feat(uniform_space): compact uniform spaces
Compact Hausdorff spaces are uniquely uniformizable and continuous
functions on them are uniformly continuous (Heine-Cantor).
#### Estimated changes
Created src/topology/uniform_space/compact_separated.lean
- \+ *lemma* compact_space_uniformity
- \+ *lemma* unique_uniformity_of_compact_t2
- \+ *lemma* compact_space.uniform_continuous_of_continuous
- \+ *lemma* compact.uniform_continuous_on_of_continuous'
- \+ *lemma* compact.uniform_continuous_on_of_continuous
- \+ *def* uniform_space_of_compact_t2



## [2020-06-28 21:26:32](https://github.com/leanprover-community/mathlib/commit/3d72c97)
chore(measure_theory/outer_measure,measure_space): use `complete_lattice_of_Inf/Sup` ([#3185](https://github.com/leanprover-community/mathlib/pull/3185))
Also add a few supporting lemmas about `bsupr`/`binfi` to `order/complete_lattice`
#### Estimated changes
Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean
- \+ *theorem* coe_supr

Modified src/order/complete_lattice.lean
- \+/\- *lemma* lt_supr_iff
- \+/\- *lemma* infi_lt_iff
- \+/\- *lemma* binfi_inf
- \+ *theorem* le_bsupr
- \+ *theorem* bsupr_le
- \+ *theorem* bsupr_le_bsupr
- \+ *theorem* binfi_le
- \+ *theorem* le_binfi
- \+ *theorem* binfi_le_binfi



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
- \+ *lemma* sup_def
- \- *lemma* sup_val

Modified src/data/nat/basic.lean
- \+ *lemma* find_eq_zero
- \+ *lemma* find_pos

Modified src/number_theory/sum_four_squares.lean


Modified src/order/bounded_lattice.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* supr_congr
- \+ *lemma* infi_congr
- \+ *lemma* infi_and'
- \+ *lemma* supr_and'
- \+/\- *lemma* Sup_range
- \+/\- *lemma* Inf_range
- \+/\- *lemma* infi_apply
- \+/\- *lemma* supr_apply
- \+/\- *theorem* supr_congr_Prop
- \+/\- *theorem* infi_congr_Prop
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod
- \+/\- *theorem* infi_sum
- \+/\- *theorem* supr_sum
- \+/\- *def* complete_lattice_of_Inf

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* Inf_def
- \+ *lemma* Sup_def
- \+ *lemma* Inf_eq_zero
- \+ *lemma* Inf_mem
- \+ *lemma* not_mem_of_lt_Inf
- \- *lemma* Inf_nat_def
- \- *lemma* Sup_nat_def



## [2020-06-28 07:12:16](https://github.com/leanprover-community/mathlib/commit/4e2b46a)
feat(algebra/big_operators): add induction principles ([#3197](https://github.com/leanprover-community/mathlib/pull/3197))
add sum_induction and prod_induction
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_induction



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
- \+/\- *lemma* mk_eq_zero
- \+/\- *lemma* coe_eq_coe

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
- \+/\- *lemma* mk_apply
- \+/\- *lemma* mk_add
- \+/\- *def* mk

Modified src/data/equiv/basic.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/finset.lean
- \+ *theorem* range_coe
- \- *theorem* range_val

Modified src/data/hash_map.lean
- \+/\- *theorem* mk_as_list
- \+/\- *theorem* mk_valid
- \+/\- *def* hash_map.mk_idx

Modified src/data/holor.lean


Modified src/data/list/range.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* ext

Modified src/data/polynomial.lean


Modified src/data/real/nnreal.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/basic.lean
- \+/\- *lemma* subtype.mem
- \+ *lemma* coe_image
- \+ *lemma* range_coe
- \+/\- *lemma* range_val
- \+/\- *lemma* range_coe_subtype
- \+ *lemma* range_val_subtype
- \- *lemma* val_image
- \- *lemma* val_range
- \+ *theorem* set_of_set
- \+ *theorem* coe_image_subset
- \+ *theorem* coe_image_univ
- \+/\- *theorem* image_preimage_val
- \+/\- *theorem* preimage_coe_eq_preimage_coe_iff
- \+/\- *theorem* preimage_val_eq_preimage_val_iff
- \- *theorem* val_image_subset
- \- *theorem* val_image_univ

Modified src/data/set/countable.lean


Modified src/data/set/finite.lean


Modified src/data/set/function.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid/basic.lean


Modified src/data/setoid/partition.lean
- \+/\- *lemma* is_partition.pairwise_disjoint
- \+/\- *lemma* is_partition.sUnion_eq_univ

Modified src/data/subtype.lean
- \+ *lemma* prop
- \+/\- *lemma* val_eq_coe
- \+ *lemma* ext_iff
- \+ *lemma* ext_val
- \+ *lemma* ext_iff_val
- \+/\- *lemma* restrict_def
- \+ *lemma* coe_prop
- \+/\- *lemma* val_prop
- \- *lemma* ext
- \- *lemma* coe_ext
- \- *lemma* val_prop'
- \+/\- *theorem* coe_eta
- \+/\- *theorem* coe_mk
- \+/\- *theorem* mk_eq_mk
- \+ *theorem* coe_injective
- \- *theorem* subtype.forall
- \- *theorem* subtype.forall'
- \- *theorem* subtype.exists

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
- \+ *lemma* erange_coe
- \- *lemma* eval_range

Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* of_finset_basis

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
- \+/\- *lemma* mk'_self''

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/subring.lean


Modified src/ring_theory/subsemiring.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* map_subtype_coe_factors'
- \- *theorem* map_subtype_val_factors'

Modified src/set_theory/ordinal.lean


Modified src/tactic/subtype_instance.lean


Modified src/topology/algebra/module.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/constructions.lean
- \+ *lemma* embedding_subtype_coe
- \+ *lemma* is_open.open_embedding_subtype_coe
- \+ *lemma* is_open.is_open_map_subtype_coe
- \+ *lemma* is_closed.closed_embedding_subtype_coe
- \+ *lemma* continuous_at_subtype_coe
- \+ *lemma* map_nhds_subtype_coe_eq
- \- *lemma* embedding_subtype_val
- \- *lemma* is_open.open_embedding_subtype_val
- \- *lemma* is_open.is_open_map_subtype_val
- \- *lemma* is_closed.closed_embedding_subtype_val
- \- *lemma* continuous_at_subtype_val
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
- \+/\- *lemma* ext

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
- \+/\- *def* functoriality



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
- \+ *lemma* card_union_eq
- \+/\- *lemma* comp_sup_eq_sup_comp
- \+ *lemma* comp_sup_eq_sup_comp_of_is_total
- \+/\- *lemma* comp_inf_eq_inf_comp
- \+ *lemma* comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* supr_coe
- \+/\- *lemma* infi_coe
- \+ *lemma* supr_insert
- \+ *lemma* infi_insert
- \+ *lemma* supr_finset_image
- \+ *lemma* infi_finset_image
- \+ *lemma* bInter_inter
- \+ *lemma* bInter_insert
- \+ *lemma* bUnion_finset_image
- \+ *lemma* bInter_finset_image
- \- *lemma* bUnion_preimage_singleton
- \+ *theorem* supr_singleton
- \+ *theorem* infi_singleton
- \+/\- *theorem* supr_union
- \+ *theorem* infi_union
- \+ *theorem* bInter_coe
- \+ *theorem* bInter_singleton
- \+ *def* subtype_insert_equiv_option

Modified src/data/set/basic.lean
- \+ *lemma* diff_inter_diff
- \+ *lemma* preimage_preimage
- \+/\- *lemma* surjective.preimage_injective
- \+ *lemma* injective.preimage_surjective
- \+ *lemma* surjective.image_surjective
- \+ *lemma* injective.image_injective
- \+/\- *lemma* surjective.range_eq
- \+/\- *lemma* surjective.range_comp
- \+ *lemma* injective.nonempty_apply_iff
- \+ *lemma* preimage_injective
- \+ *lemma* preimage_surjective
- \+ *lemma* image_surjective
- \+/\- *lemma* image_injective
- \+ *theorem* subset.rfl
- \+ *theorem* preimage_id'

Modified src/data/set/lattice.lean
- \+ *lemma* disjoint.preimage
- \+ *lemma* subset_diff
- \+ *theorem* disjoint_iff_inter_eq_empty
- \+ *theorem* disjoint_of_subset_left
- \+ *theorem* disjoint_of_subset_right
- \+ *theorem* disjoint_of_subset

Modified src/logic/embedding.lean


Modified src/logic/function/basic.lean
- \+/\- *lemma* injective.ne
- \+ *lemma* injective.ne_iff

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
- \+ *lemma* sum_inner
- \+ *lemma* inner_sum
- \+ *def* bilin_form_of_inner



## [2020-06-27 02:52:56](https://github.com/leanprover-community/mathlib/commit/6ed3325)
feat(category_theory/limits): limit of point iso ([#3188](https://github.com/leanprover-community/mathlib/pull/3188))
Prove a cone is a limit given that the canonical morphism from it to a limiting cone is an iso.
#### Estimated changes
Modified src/algebra/category/Group/limits.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* of_point_iso

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
- \+ *lemma* empty_ext'
- \+/\- *def* empty
- \+/\- *def* empty_ext
- \+ *def* unique_from_empty



## [2020-06-26 16:35:02](https://github.com/leanprover-community/mathlib/commit/2d270ff)
feat(data/set/basic): +2 lemmas, +2 `simp` attrs ([#3182](https://github.com/leanprover-community/mathlib/pull/3182))
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* subset_image_diff
- \+ *theorem* image_diff
- \+/\- *theorem* image_preimage_val
- \+ *theorem* image_preimage_coe



## [2020-06-26 15:11:50](https://github.com/leanprover-community/mathlib/commit/ef62d1c)
chore(*): last preparations for Heine ([#3179](https://github.com/leanprover-community/mathlib/pull/3179))
This is hopefully the last preparatory PR before we study compact uniform spaces. It has almost no mathematical content, except that I define `uniform_continuous_on`, and check it is equivalent to uniform continuity for the induced uniformity.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* mem_diagonal
- \+ *lemma* diagonal_eq_range

Modified src/order/complete_lattice.lean
- \+ *lemma* infi_split
- \+ *lemma* infi_split_single
- \+ *lemma* supr_split
- \+ *lemma* supr_split_single

Modified src/order/filter/basic.lean
- \+ *lemma* mem_iff_inf_principal_compl
- \+ *lemma* le_iff_forall_inf_principal_compl
- \+ *lemma* principal_le_iff
- \+ *lemma* comap_const_of_not_mem
- \+ *lemma* comap_const_of_mem
- \+ *lemma* subtype_coe_map_comap_prod
- \+ *lemma* comap_prod

Modified src/topology/basic.lean
- \+ *lemma* cluster_pt_iff
- \+ *lemma* cluster_pt.of_inf_left
- \+ *lemma* cluster_pt.of_inf_right
- \+ *lemma* subset_interior_iff_nhds
- \- *lemma* cluster_pt_of_inf_left
- \- *lemma* cluster_pt_of_inf_right
- \+ *theorem* mem_closure_iff_cluster_pt

Modified src/topology/metric_space/basic.lean
- \+ *lemma* uniform_continuous_on_iff

Modified src/topology/separation.lean
- \+ *lemma* disjoint_nested_nhds

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/basic.lean
- \+ *lemma* nhds_eq_comap_uniformity_aux
- \+/\- *lemma* nhds_eq_comap_uniformity
- \+ *lemma* nhds_le_uniformity
- \+ *lemma* uniform_continuous_on_iff_restrict
- \+ *def* uniform_continuous_on

Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* eq_of_uniformity_inf_nhds



## [2020-06-26 13:39:18](https://github.com/leanprover-community/mathlib/commit/6624509)
feat(algebra/big_operators): telescoping sums ([#3184](https://github.com/leanprover-community/mathlib/pull/3184))
generalize sum_range_sub_of_monotone, a theorem about nats, to a theorem about commutative groups
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_range_sub
- \+ *lemma* prod_range_div



## [2020-06-26 09:59:19](https://github.com/leanprover-community/mathlib/commit/5b97da6)
feat(ring_theory/matrix_equiv_tensor): matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) ([#3177](https://github.com/leanprover-community/mathlib/pull/3177))
When `A` is an `R`-algebra, matrices over `A` are equivalent (as an algebra) to `A ⊗[R] matrix n n R`.
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* to_fun_eq_coe

Modified src/data/matrix/basic.lean
- \+/\- *lemma* smul_mul
- \+ *lemma* mul_mul_left
- \+ *lemma* mul_mul_right
- \+ *lemma* map_matrix_mul
- \+ *def* scalar

Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* sum_tmul
- \+ *lemma* tmul_sum

Modified src/logic/basic.lean
- \+ *lemma* apply_dite
- \+ *lemma* apply_ite
- \+ *lemma* dite_apply
- \+ *lemma* ite_apply

Modified src/ring_theory/algebra.lean
- \+ *lemma* algebra_map_eq_smul_one
- \+ *lemma* symm_symm

Created src/ring_theory/matrix_algebra.lean
- \+ *lemma* algebra_map_matrix_val
- \+ *lemma* to_fun_alg_hom_apply
- \+ *lemma* inv_fun_zero
- \+ *lemma* inv_fun_add
- \+ *lemma* inv_fun_smul
- \+ *lemma* inv_fun_algebra_map
- \+ *lemma* right_inv
- \+ *lemma* left_inv
- \+ *lemma* matrix_equiv_tensor_apply
- \+ *lemma* matrix_equiv_tensor_apply_symm
- \+ *def* to_fun
- \+ *def* to_fun_right_linear
- \+ *def* to_fun_bilinear
- \+ *def* to_fun_linear
- \+ *def* to_fun_alg_hom
- \+ *def* inv_fun
- \+ *def* equiv
- \+ *def* matrix_equiv_tensor

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
- \+/\- *lemma* op_obj_unop_hom_app
- \+/\- *lemma* op_obj_unop_inv_app

Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean
- \- *def* ulift_down
- \- *def* ulift_up

Modified src/category_theory/functor_category.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/natural_isomorphism.lean
- \- *def* ulift_down_up
- \- *def* ulift_up_down

Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/products/associator.lean
- \+/\- *def* associator
- \+/\- *def* inverse_associator

Modified src/category_theory/punit.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/sums/associator.lean
- \+/\- *def* associator
- \+/\- *def* inverse_associator



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
- \+ *def* trunc_of_multiset_exists_mem
- \+ *def* trunc_of_nonempty_fintype
- \+ *def* trunc_of_card_pos
- \+ *def* trunc_sigma_of_exists



## [2020-06-26 01:23:06](https://github.com/leanprover-community/mathlib/commit/616cb5e)
chore(category_theory/equivalence) explicit transitivity transformation ([#3176](https://github.com/leanprover-community/mathlib/pull/3176))
Modifies the construction of the transitive equivalence to be explicit in what exactly the natural transformations are.
The motivation for this is two-fold: firstly we get auto-generated projection lemmas for extracting the functor and inverse, and the natural transformations aren't obscured through `adjointify_η`.
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+/\- *def* trans



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
- \+ *lemma* mem_maximal_ideal
- \+ *lemma* local_of_nonunits_ideal
- \+ *lemma* local_of_unique_max_ideal
- \+/\- *lemma* map_nonunit
- \- *lemma* mem_nonunits_ideal
- \+ *def* maximal_ideal
- \+/\- *def* residue_field
- \- *def* nonunits_ideal
- \- *def* is_local_ring
- \- *def* local_of_is_local_ring
- \- *def* local_of_unit_or_unit_one_sub
- \- *def* local_of_nonunits_ideal
- \- *def* local_of_unique_max_ideal

Modified src/ring_theory/power_series.lean
- \- *lemma* is_local_ring



## [2020-06-25 15:51:37](https://github.com/leanprover-community/mathlib/commit/afc1c24)
feat(category/default): comp_dite ([#3163](https://github.com/leanprover-community/mathlib/pull/3163))
Adds lemmas to "distribute" composition over `if` statements.
#### Estimated changes
Modified src/category_theory/category/default.lean
- \+ *lemma* comp_dite
- \+ *lemma* dite_comp



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
- \+ *lemma* equivalence_of_reindexing_functor_obj
- \+ *def* whiskering
- \+ *def* whiskering_equivalence
- \+ *def* equivalence_of_reindexing

Modified src/category_theory/limits/limits.lean
- \+ *lemma* has_limit.iso_of_nat_iso_hom_π
- \+ *lemma* has_limit.iso_of_equivalence_π
- \+ *lemma* lim_map_π
- \+ *lemma* has_colimit.iso_of_nat_iso_hom_π
- \+ *lemma* has_colimit.iso_of_equivalence_π
- \+ *lemma* ι_colim_map
- \+/\- *def* of_cone_equiv
- \+ *def* cone_points_iso_of_nat_iso
- \+ *def* whisker_equivalence
- \+ *def* cone_points_iso_of_equivalence
- \+/\- *def* of_cocone_equiv
- \+ *def* cocone_points_iso_of_nat_iso
- \+ *def* cocone_points_iso_of_equivalence
- \+ *def* has_limit.iso_of_nat_iso
- \+ *def* has_limit.iso_of_equivalence
- \+ *def* lim_map
- \+ *def* has_colimit.iso_of_nat_iso
- \+ *def* has_colimit.iso_of_equivalence
- \+ *def* colim_map



## [2020-06-25 14:32:01](https://github.com/leanprover-community/mathlib/commit/158e84a)
feat(*): bump to Lean 3.16.5 ([#3170](https://github.com/leanprover-community/mathlib/pull/3170))
There should be no changes required in mathlib.
#### Estimated changes
Modified leanpkg.toml




## [2020-06-25 13:06:57](https://github.com/leanprover-community/mathlib/commit/7d331eb)
chore(*): assorted lemmas about `set` and `finset` ([#3158](https://github.com/leanprover-community/mathlib/pull/3158))
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* bUnion_preimage_singleton
- \+ *theorem* bUnion_coe

Modified src/data/indicator_function.lean
- \+ *lemma* eq_on_indicator
- \+ *lemma* indicator_preimage_of_not_mem
- \+ *lemma* mem_range_indicator

Modified src/data/set/basic.lean
- \+ *lemma* preimage_range
- \+ *theorem* sep_mem_eq
- \+ *theorem* preimage_const_of_mem
- \+ *theorem* preimage_const_of_not_mem
- \+ *theorem* preimage_const
- \+/\- *theorem* preimage_inter_range
- \+ *theorem* preimage_range_inter
- \+ *theorem* preimage_singleton_nonempty
- \+ *theorem* preimage_singleton_eq_empty

Modified src/data/set/disjointed.lean
- \+ *theorem* set.pairwise_on_univ
- \+ *theorem* pairwise_disjoint_fiber

Modified src/data/set/lattice.lean
- \+ *lemma* bUnion_preimage_singleton
- \+ *lemma* bUnion_range_preimage_singleton
- \+ *theorem* pairwise_on_disjoint_fiber

Modified src/logic/basic.lean
- \+ *lemma* ite_eq_iff

Modified src/measure_theory/integration.lean




## [2020-06-25 13:06:55](https://github.com/leanprover-community/mathlib/commit/80a0877)
feat(category_theory): show a pullback of a regular mono is regular ([#2780](https://github.com/leanprover-community/mathlib/pull/2780))
And adds two methods for constructing limits which I've found much easier to use in practice.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* fork.is_limit.mk'
- \+ *def* cofork.is_colimit.mk'

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* is_limit.mk'
- \+ *def* flip_is_limit
- \+ *def* is_colimit.mk'
- \+ *def* flip_is_colimit

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* regular_of_is_pullback_snd_of_regular
- \+ *def* regular_of_is_pullback_fst_of_regular
- \+ *def* normal_of_is_pullback_snd_of_normal
- \+ *def* normal_of_is_pullback_fst_of_normal
- \+ *def* regular_of_is_pushout_snd_of_regular
- \+ *def* regular_of_is_pushout_fst_of_regular
- \+ *def* normal_of_is_pushout_snd_of_normal
- \+ *def* normal_of_is_pushout_fst_of_normal



## [2020-06-25 12:26:52](https://github.com/leanprover-community/mathlib/commit/3f868fa)
feat(filter, topology): cluster_pt and principal notation, redefine compactness ([#3160](https://github.com/leanprover-community/mathlib/pull/3160))
This PR implements what is discussed in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Picking.20sides. It introduces a notation for `filter.principal`, defines `cluster_pt` and uses it to redefine compactness in a way which makes the library more consistent by always putting the neighborhood filter on the left, as in the description of closures and `nhds_within`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* inf_map_at_top_ne_bot_iff
- \- *lemma* map_at_top_inf_ne_bot_iff
- \+/\- *def* at_top
- \+/\- *def* at_bot

Modified src/order/filter/bases.lean
- \+/\- *lemma* eq_infi_principal
- \+/\- *lemma* is_countably_generated_seq
- \+/\- *lemma* is_countably_generated_of_seq

Modified src/order/filter/basic.lean
- \+/\- *lemma* mem_principal_sets
- \+/\- *lemma* mem_principal_self
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* principal_mono
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* principal_eq_iff_eq
- \+/\- *lemma* join_principal_eq_Sup
- \+/\- *lemma* principal_univ
- \+/\- *lemma* principal_empty
- \+/\- *lemma* mem_sets_of_eq_bot
- \+/\- *lemma* inf_principal
- \+/\- *lemma* sup_principal
- \+/\- *lemma* supr_principal
- \+/\- *lemma* principal_eq_bot_iff
- \+/\- *lemma* principal_ne_bot_iff
- \+/\- *lemma* is_compl_principal
- \+/\- *lemma* inf_principal_eq_bot
- \+/\- *lemma* pure_eq_principal
- \+/\- *theorem* comap_principal

Modified src/order/filter/countable_Inter.lean


Modified src/order/filter/extr.lean
- \+/\- *def* is_min_on
- \+/\- *def* is_max_on
- \+/\- *def* is_extr_on

Modified src/order/filter/lift.lean
- \+/\- *lemma* lift_principal2

Modified src/order/filter/partial.lean


Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* le_of_ultrafilter

Modified src/order/liminf_limsup.lean
- \+/\- *lemma* is_bounded_principal

Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean
- \+/\- *lemma* tendsto_subseq

Modified src/topology/basic.lean
- \+/\- *lemma* nhds_def
- \+/\- *lemma* nhds_le_of_le
- \+ *lemma* cluster_pt.of_le_nhds
- \+ *lemma* cluster_pt.of_nhds_le
- \+ *lemma* cluster_pt.mono
- \+ *lemma* cluster_pt_of_inf_left
- \+ *lemma* cluster_pt_of_inf_right
- \+ *lemma* map_cluster_pt_iff
- \+ *lemma* map_cluster_pt_of_comp
- \+/\- *lemma* interior_eq_nhds
- \+/\- *lemma* is_open_iff_nhds
- \+ *lemma* closure_eq_cluster_pts
- \+/\- *lemma* is_closed_iff_nhds
- \- *lemma* closure_eq_nhds
- \+/\- *def* nhds
- \+ *def* cluster_pt
- \+ *def* map_cluster_pt

Modified src/topology/constructions.lean


Modified src/topology/continuous_on.lean
- \+/\- *def* nhds_within

Modified src/topology/dense_embedding.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* nhds_top
- \+/\- *lemma* nhds_zero
- \+/\- *lemma* nhds_of_ne_top

Modified src/topology/local_extr.lean


Modified src/topology/maps.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.uniformity_edist

Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* nhds_eq

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
- \+ *lemma* right_adjoint_of_is_equivalence
- \+ *lemma* left_adjoint_of_is_equivalence



## [2020-06-25 07:40:02](https://github.com/leanprover-community/mathlib/commit/d86f1c8)
chore(category/discrete): missing simp lemmas ([#3165](https://github.com/leanprover-community/mathlib/pull/3165))
Some obvious missing `simp` lemmas for `discrete.nat_iso`.
#### Estimated changes
Modified src/category_theory/discrete_category.lean
- \+ *lemma* nat_iso_hom_app
- \+ *lemma* nat_iso_inv_app
- \+ *lemma* nat_iso_app



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
- \+ *lemma* equivalence_mk'_unit
- \+ *lemma* equivalence_mk'_counit
- \+ *lemma* equivalence_mk'_unit_inv
- \+ *lemma* equivalence_mk'_counit_inv
- \+/\- *lemma* functor_unit_comp
- \+ *lemma* as_equivalence_functor
- \+ *lemma* as_equivalence_inverse
- \+ *lemma* inv_inv
- \+ *lemma* functor_inv
- \+ *lemma* inverse_inv
- \+ *lemma* functor_as_equivalence
- \+ *lemma* inverse_as_equivalence
- \- *lemma* unit_def
- \- *lemma* counit_def
- \- *lemma* unit_inv_def
- \- *lemma* counit_inv_def
- \- *def* unit
- \- *def* counit
- \- *def* unit_inv
- \- *def* counit_inv



## [2020-06-25 07:39:59](https://github.com/leanprover-community/mathlib/commit/e8187ac)
feat(category/preadditive): comp_sum ([#3162](https://github.com/leanprover-community/mathlib/pull/3162))
Adds lemmas to distribute composition over `finset.sum`, in a preadditive category.
#### Estimated changes
Modified src/category_theory/preadditive.lean
- \+ *lemma* comp_sum
- \+ *lemma* sum_comp



## [2020-06-25 06:32:59](https://github.com/leanprover-community/mathlib/commit/3875012)
feat(data/quot): add `map'`, `hrec_on'`, and `hrec_on₂'` ([#3148](https://github.com/leanprover-community/mathlib/pull/3148))
Also add a few `simp` lemmas
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* map_mk
- \+ *lemma* hrec_on'_mk'
- \+ *lemma* hrec_on₂'_mk'
- \+ *lemma* map'_mk'
- \+ *lemma* map₂'_mk'
- \+/\- *theorem* quotient.choice_eq



## [2020-06-25 05:38:59](https://github.com/leanprover-community/mathlib/commit/553e453)
feat(algebra/big_operators): prod_dite_eq ([#3167](https://github.com/leanprover-community/mathlib/pull/3167))
Add `finset.prod_dite_eq`, the dependent analogue of `finset.prod_ite_eq`, and its primed version for the flipped equality.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_eq_one
- \+ *lemma* prod_dite_eq
- \+ *lemma* prod_dite_eq'
- \+/\- *lemma* prod_ite_eq



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
- \+ *theorem* mk_eq_zero
- \- *theorem* mk_zero_eq
- \- *theorem* mul_zero
- \- *theorem* mk_eq_zero_iff_eq_zero
- \- *theorem* zero_ne_one
- \- *theorem* mul_eq_zero_iff

Modified src/algebra/big_operators.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_bit0
- \+/\- *lemma* coe_bit1
- \- *lemma* coe_zero
- \- *lemma* coe_eq_zero
- \+ *theorem* one_eq_coe
- \+ *theorem* top_ne_one
- \+ *theorem* one_ne_top

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* mul_eq_top_iff
- \- *theorem* top_ne_zero
- \- *theorem* zero_ne_top
- \- *theorem* zero_eq_coe

Modified src/algebra/ring.lean
- \- *lemma* mul_eq_zero_iff_eq_zero_or_eq_zero
- \- *lemma* eq_zero_of_mul_eq_self_right
- \- *lemma* eq_zero_of_mul_eq_self_left
- \+ *theorem* eq_zero_of_mul_eq_self_right
- \+ *theorem* eq_zero_of_mul_eq_self_left
- \- *theorem* eq_zero_of_mul_eq_self_right'
- \- *theorem* eq_zero_of_mul_eq_self_left'

Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* coe_nat

Modified src/data/padics/padic_integers.lean


Modified src/data/real/ennreal.lean
- \- *lemma* mul_eq_zero

Modified src/data/real/nnreal.lean


Modified src/number_theory/dioph.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/topology/instances/ennreal.lean




## [2020-06-25 01:09:38](https://github.com/leanprover-community/mathlib/commit/e1a72b5)
feat(archive/100-theorems-list/73_ascending_descending_sequences): Erdős–Szekeres ([#3074](https://github.com/leanprover-community/mathlib/pull/3074))
Prove the Erdős-Szekeres theorem on ascending or descending sequences
#### Estimated changes
Created archive/100-theorems-list/73_ascending_descending_sequences.lean
- \+ *theorem* erdos_szekeres

Modified src/data/nat/basic.lean
- \+ *theorem* succ_injective

Modified src/order/basic.lean
- \+ *lemma* injective_of_lt_imp_ne
- \+ *def* strict_mono_incr_on
- \+ *def* strict_mono_decr_on



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
- \+ *lemma* sum_smul_index'

Modified src/linear_algebra/basis.lean
- \+ *theorem* module_equiv_finsupp_apply_basis

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* coe_lsum
- \+/\- *theorem* lsum_apply
- \+ *theorem* lsum_single
- \+ *theorem* dom_lcongr_single
- \+ *theorem* lcongr_single
- \+ *theorem* finsupp_lequiv_direct_sum_single
- \+ *theorem* finsupp_lequiv_direct_sum_symm_lof
- \+ *theorem* finsupp_tensor_finsupp_single
- \+ *theorem* finsupp_tensor_finsupp_symm_single
- \+/\- *def* lsum
- \+ *def* lcongr
- \+ *def* finsupp_lequiv_direct_sum
- \+ *def* finsupp_tensor_finsupp

Modified src/linear_algebra/finsupp_vector_space.lean
- \+/\- *lemma* is_basis_single
- \+ *lemma* is_basis_single_one
- \+ *lemma* is_basis.tensor_product

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* congr_tmul
- \+ *theorem* direct_sum_lof_tmul_lof



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
- \+ *def* mfind
- \+ *def* mmap_upper_triangle

Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/tactic/cancel_denoms.lean


Modified src/tactic/core.lean


Deleted src/tactic/linarith.lean
- \- *lemma* int.coe_nat_bit0
- \- *lemma* int.coe_nat_bit1
- \- *lemma* int.coe_nat_bit0_mul
- \- *lemma* int.coe_nat_bit1_mul
- \- *lemma* int.coe_nat_one_mul
- \- *lemma* int.coe_nat_zero_mul
- \- *lemma* int.coe_nat_mul_bit0
- \- *lemma* int.coe_nat_mul_bit1
- \- *lemma* int.coe_nat_mul_one
- \- *lemma* int.coe_nat_mul_zero
- \- *lemma* nat_eq_subst
- \- *lemma* nat_le_subst
- \- *lemma* nat_lt_subst
- \- *lemma* eq_of_eq_of_eq
- \- *lemma* le_of_eq_of_le
- \- *lemma* lt_of_eq_of_lt
- \- *lemma* le_of_le_of_eq
- \- *lemma* lt_of_lt_of_eq
- \- *lemma* mul_neg
- \- *lemma* mul_nonpos
- \- *lemma* mul_eq
- \- *lemma* eq_of_not_lt_of_not_gt
- \- *lemma* add_subst
- \- *lemma* sub_subst
- \- *lemma* neg_subst
- \- *lemma* mul_subst
- \- *lemma* div_subst
- \- *lemma* sub_into_lt
- \- *lemma* mul_zero_eq
- \- *lemma* zero_mul_eq
- \- *def* linexp
- \- *def* scale
- \- *def* get
- \- *def* contains
- \- *def* zfind
- \- *def* cmp
- \- *def* vars
- \- *def* ineq.max
- \- *def* ineq.cmp
- \- *def* ineq.to_string
- \- *def* comp.vars
- \- *def* comp_source.to_string

Created src/tactic/linarith/datatypes.lean
- \+ *def* linexp
- \+ *def* scale
- \+ *def* get
- \+ *def* contains
- \+ *def* zfind
- \+ *def* vars
- \+ *def* cmp
- \+ *def* max
- \+ *def* to_string
- \+ *def* comp.vars
- \+ *def* comp.coeff_of
- \+ *def* comp.scale

Created src/tactic/linarith/default.lean


Created src/tactic/linarith/elimination.lean
- \+ *def* comp_source.to_string

Created src/tactic/linarith/frontend.lean


Created src/tactic/linarith/lemmas.lean
- \+ *lemma* int.coe_nat_bit0
- \+ *lemma* int.coe_nat_bit1
- \+ *lemma* int.coe_nat_bit0_mul
- \+ *lemma* int.coe_nat_bit1_mul
- \+ *lemma* int.coe_nat_one_mul
- \+ *lemma* int.coe_nat_zero_mul
- \+ *lemma* int.coe_nat_mul_bit0
- \+ *lemma* int.coe_nat_mul_bit1
- \+ *lemma* int.coe_nat_mul_one
- \+ *lemma* int.coe_nat_mul_zero
- \+ *lemma* nat_eq_subst
- \+ *lemma* nat_le_subst
- \+ *lemma* nat_lt_subst
- \+ *lemma* eq_of_eq_of_eq
- \+ *lemma* le_of_eq_of_le
- \+ *lemma* lt_of_eq_of_lt
- \+ *lemma* le_of_le_of_eq
- \+ *lemma* lt_of_lt_of_eq
- \+ *lemma* mul_neg
- \+ *lemma* mul_nonpos
- \+ *lemma* mul_eq
- \+ *lemma* eq_of_not_lt_of_not_gt
- \+ *lemma* mul_zero_eq
- \+ *lemma* zero_mul_eq

Created src/tactic/linarith/parsing.lean


Created src/tactic/linarith/preprocessing.lean


Created src/tactic/linarith/verification.lean


Modified src/tactic/zify.lean


Modified test/linarith.lean
- \+ *lemma* norm_eq_zero_iff
- \+ *lemma* norm_nonpos_right



## [2020-06-24 09:30:51](https://github.com/leanprover-community/mathlib/commit/194edc1)
feat(ring_theory/localization): integral closure in field extension ([#3096](https://github.com/leanprover-community/mathlib/pull/3096))
Let `A` be an integral domain with field of fractions `K` and `L` a finite extension of `K`. This PR shows the integral closure of `A` in `L` has fraction field `L`. If those definitions existed, the corollary is that the ring of integers of a number field is a number ring.
For this, we need two constructions on polynomials:
 * If `p` is a nonzero polynomial, `integral_normalization p` is a monic polynomial with roots `z * a` for `z` a root of `p` and `a` the leading coefficient of `p`
 * If `f` is the localization map from `A` to `K` and `p` has coefficients in `K`, then `f.integer_normalization p` is a polynomial with coefficients in `A` (think: `∀ i, is_integer (f.integer_normalization p).coeff i`) with the same roots as `p`.
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* eval₂_zero
- \+ *lemma* eval₂_smul
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+ *lemma* degree_ne_of_nat_degree_ne
- \+/\- *lemma* degree_C
- \+/\- *lemma* degree_C_le
- \+/\- *lemma* degree_one_le
- \+ *lemma* coeff_ne_zero_of_eq_degree
- \+ *lemma* eq_C_of_nat_degree_le_zero
- \+ *lemma* nat_degree_pos_iff_degree_pos
- \+ *lemma* nat_degree_pos_of_eval₂_root
- \+ *lemma* degree_pos_of_eval₂_root
- \+ *lemma* nat_degree_pos_of_aeval_root
- \+ *lemma* degree_pos_of_aeval_root
- \+ *lemma* integral_normalization_coeff_degree
- \+ *lemma* integral_normalization_coeff_nat_degree
- \+ *lemma* integral_normalization_coeff_ne_degree
- \+ *lemma* integral_normalization_coeff_ne_nat_degree
- \+ *lemma* monic_integral_normalization
- \+ *lemma* support_integral_normalization
- \+ *lemma* integral_normalization_eval₂_eq_zero
- \+ *lemma* integral_normalization_aeval_eq_zero

Modified src/ring_theory/algebraic.lean
- \+ *lemma* is_algebraic_of_finite
- \+ *lemma* exists_integral_multiple

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean
- \+ *lemma* exist_integer_multiples_of_finset
- \+ *lemma* map_smul
- \+ *lemma* coeff_integer_normalization_mem_support
- \+ *lemma* integer_normalization_coeff
- \+ *lemma* integer_normalization_spec
- \+ *lemma* integer_normalization_map_to_map
- \+ *lemma* integer_normalization_eval₂_eq_zero
- \+ *lemma* integer_normalization_aeval_eq_zero
- \+ *lemma* integer_normalization_eq_zero_iff
- \+ *lemma* comap_is_algebraic_iff
- \+ *def* fraction_map_of_algebraic
- \+ *def* fraction_map_of_finite_extension



## [2020-06-24 07:12:51](https://github.com/leanprover-community/mathlib/commit/8ecf53d)
feat(order/filter/countable_Inter): `sup` and `inf` ([#3154](https://github.com/leanprover-community/mathlib/pull/3154))
#### Estimated changes
Modified src/order/filter/countable_Inter.lean




## [2020-06-24 06:13:13](https://github.com/leanprover-community/mathlib/commit/617b07e)
feat(uniform_space/separation): add separated_set ([#3130](https://github.com/leanprover-community/mathlib/pull/3130))
Also add documentation and simplify the proof of separated => t2 and add the converse.
#### Estimated changes
Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* is_add_group_hom_extension

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean
- \+/\- *def* extension_hom

Modified src/topology/category/UniformSpace.lean
- \+/\- *def* of

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/separation.lean
- \+/\- *lemma* is_closed_diagonal
- \+ *lemma* t2_iff_is_closed_diagonal

Modified src/topology/uniform_space/abstract_completion.lean
- \+/\- *lemma* extend_map

Modified src/topology/uniform_space/complete_separated.lean
- \+/\- *lemma* is_closed_of_is_complete

Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* separated_pure_cauchy_injective
- \+/\- *lemma* uniform_embedding_coe
- \+/\- *lemma* dense_embedding_coe
- \+/\- *lemma* extension_map

Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/separation.lean
- \+/\- *lemma* separated_equiv
- \+ *lemma* id_rel_sub_separation_relation
- \+ *lemma* separation_rel_comap
- \+ *lemma* separation_rel_eq_inter_closure
- \+ *lemma* is_closed_separation_rel
- \+ *lemma* separated_iff_t2
- \+ *lemma* is_separated_def
- \+ *lemma* is_separated_def'
- \+ *lemma* univ_separated_iff
- \+ *lemma* is_separated_of_separated_space
- \+ *lemma* is_separated_iff_induced
- \+ *lemma* eq_of_uniformity_inf_nhds_of_is_separated
- \+ *lemma* eq_of_uniformity_inf_nhds
- \+/\- *lemma* eq_of_separated_of_uniform_continuous
- \+/\- *lemma* lift_mk
- \+/\- *lemma* uniform_continuous_lift
- \+ *def* separated_space
- \+ *def* is_separated
- \+/\- *def* lift
- \- *def* separated

Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-06-24 00:48:46](https://github.com/leanprover-community/mathlib/commit/985cce7)
chore(scripts): update nolints.txt ([#3156](https://github.com/leanprover-community/mathlib/pull/3156))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-24 00:18:26](https://github.com/leanprover-community/mathlib/commit/d57ac08)
feat(field_theory/separable): definition and basic properties ([#3155](https://github.com/leanprover-community/mathlib/pull/3155))
#### Estimated changes
Created src/field_theory/separable.lean
- \+ *lemma* separable_def
- \+ *lemma* separable_def'
- \+ *lemma* separable_one
- \+ *lemma* separable_X_add_C
- \+ *lemma* separable_X
- \+ *lemma* separable.of_mul_left
- \+ *lemma* separable.of_mul_right
- \+ *lemma* separable.mul
- \+ *def* separable

Modified src/ring_theory/coprime.lean
- \+ *lemma* is_coprime.of_add_mul_left_left
- \+ *lemma* is_coprime.of_add_mul_right_left
- \+ *lemma* is_coprime.of_add_mul_left_right
- \+ *lemma* is_coprime.of_add_mul_right_right
- \+ *lemma* is_coprime.of_mul_add_left_left
- \+ *lemma* is_coprime.of_mul_add_right_left
- \+ *lemma* is_coprime.of_mul_add_left_right
- \+ *lemma* is_coprime.of_mul_add_right_right
- \+ *lemma* add_mul_left_left
- \+ *lemma* add_mul_right_left
- \+ *lemma* add_mul_left_right
- \+ *lemma* add_mul_right_right
- \+ *lemma* mul_add_left_left
- \+ *lemma* mul_add_right_left
- \+ *lemma* mul_add_left_right
- \+ *lemma* mul_add_right_right
- \+ *lemma* add_mul_left_left_iff
- \+ *lemma* add_mul_right_left_iff
- \+ *lemma* add_mul_left_right_iff
- \+ *lemma* add_mul_right_right_iff
- \+ *lemma* mul_add_left_left_iff
- \+ *lemma* mul_add_right_left_iff
- \+ *lemma* mul_add_left_right_iff
- \+ *lemma* mul_add_right_right_iff



## [2020-06-23 22:02:55](https://github.com/leanprover-community/mathlib/commit/340d5a9)
refactor(geometry/manifold/*): rename to charted_space and tangent_map ([#3103](https://github.com/leanprover-community/mathlib/pull/3103))
@PatrickMassot  had asked some time ago if what is currently called `manifold` in mathlib could be renamed to `charted_space`, and in a recent PR he asked if `bundled_mfderiv` could be called `tangent_map`. Both changes make sense. They are implemented in this PR, together with several tiny improvements to the manifold library.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/convex/basic.lean


Modified src/data/equiv/local_equiv.lean
- \+/\- *lemma* to_fun_as_coe
- \+/\- *lemma* inv_fun_as_coe
- \+/\- *lemma* map_source
- \+/\- *lemma* map_target
- \+/\- *lemma* left_inv
- \+/\- *lemma* right_inv
- \+/\- *lemma* symm_source
- \+/\- *lemma* symm_target
- \+/\- *lemma* symm_symm
- \+ *lemma* image_inter_source_eq
- \+ *lemma* image_inter_source_eq'
- \+ *lemma* symm_image_eq_source_inter_preimage
- \+ *lemma* symm_image_inter_target_eq
- \+ *lemma* symm_image_inter_target_eq'
- \+/\- *lemma* restr_coe
- \+/\- *lemma* restr_coe_symm
- \+/\- *lemma* restr_source
- \+/\- *lemma* restr_target
- \+/\- *lemma* restr_univ
- \+/\- *lemma* refl_source
- \+/\- *lemma* refl_target
- \+/\- *lemma* refl_coe
- \+/\- *lemma* refl_symm
- \+/\- *lemma* refl_restr_source
- \+/\- *lemma* refl_restr_target
- \+/\- *lemma* of_set_source
- \+/\- *lemma* of_set_target
- \+/\- *lemma* of_set_coe
- \+/\- *lemma* of_set_symm
- \+/\- *lemma* coe_trans
- \+/\- *lemma* coe_trans_symm
- \+/\- *lemma* trans_source
- \+/\- *lemma* trans_target
- \+/\- *lemma* trans_refl
- \+/\- *lemma* refl_trans
- \+/\- *lemma* prod_source
- \+/\- *lemma* prod_target
- \+/\- *lemma* prod_coe
- \+/\- *lemma* prod_coe_symm
- \+ *lemma* prod_symm
- \+ *lemma* prod_trans
- \+/\- *lemma* to_local_equiv_coe
- \+/\- *lemma* to_local_equiv_symm_coe
- \+/\- *lemma* to_local_equiv_source
- \+/\- *lemma* to_local_equiv_target
- \+/\- *lemma* refl_to_local_equiv
- \+/\- *lemma* symm_to_local_equiv
- \+/\- *lemma* trans_to_local_equiv
- \- *lemma* inv_image_eq_source_inter_preimage
- \+/\- *theorem* coe_mk
- \+/\- *theorem* coe_symm_mk

Modified src/data/monoid_algebra.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pnat/xgcd.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean
- \+/\- *lemma* base_set
- \+/\- *lemma* chart_source
- \+/\- *lemma* chart_target
- \+/\- *lemma* mem_chart_source_iff
- \+/\- *lemma* mem_chart_target_iff
- \+/\- *lemma* coe_chart_at_fst
- \+/\- *lemma* coe_chart_at_symm_fst
- \+/\- *lemma* tangent_bundle_model_space_chart_at
- \+/\- *lemma* tangent_bundle_model_space_coe_chart_at
- \+/\- *lemma* tangent_bundle_model_space_coe_chart_at_symm

Renamed src/geometry/manifold/manifold.lean to src/geometry/manifold/charted_space.lean
- \+ *lemma* structure_groupoid.trans
- \+ *lemma* structure_groupoid.symm
- \+ *lemma* structure_groupoid.id_mem
- \+ *lemma* structure_groupoid.locality
- \+ *lemma* structure_groupoid.eq_on_source
- \+ *lemma* structure_groupoid.le_iff
- \+/\- *lemma* model_space_atlas
- \+/\- *lemma* chart_at_model_space_eq
- \+ *lemma* structure_groupoid.compatible
- \+ *lemma* structure_groupoid.mem_maximal_atlas_of_mem_atlas
- \+ *lemma* structure_groupoid.chart_mem_maximal_atlas
- \+ *lemma* mem_maximal_atlas_iff
- \+ *lemma* structure_groupoid.compatible_of_mem_maximal_atlas
- \+ *def* to_charted_space
- \+ *def* structure_groupoid.maximal_atlas
- \+/\- *def* structomorph.refl
- \- *def* to_manifold

Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* unique_mdiff_on_univ
- \+/\- *lemma* has_mfderiv_within_at_univ
- \+/\- *lemma* mfderiv_within_univ
- \+ *lemma* tangent_map_within_subset
- \+ *lemma* tangent_map_within_univ
- \+ *lemma* tangent_map_within_eq_tangent_map
- \+ *lemma* tangent_map_within_tangent_bundle_proj
- \+ *lemma* tangent_map_within_proj
- \+ *lemma* tangent_map_tangent_bundle_proj
- \+ *lemma* tangent_map_proj
- \+ *lemma* tangent_map_within_comp_at
- \+ *lemma* tangent_map_comp_at
- \+ *lemma* tangent_map_comp
- \+/\- *lemma* mfderiv_id
- \+/\- *lemma* mfderiv_const
- \+ *lemma* tangent_map_chart
- \+ *lemma* tangent_map_chart_symm
- \+/\- *lemma* written_in_ext_chart_model_space
- \- *lemma* bundle_mfderiv_within_subset
- \- *lemma* bundle_mfderiv_within_univ
- \- *lemma* bundle_mfderiv_within_eq_bundle_mfderiv
- \- *lemma* bundle_mfderiv_within_tangent_bundle_proj
- \- *lemma* bundle_mfderiv_within_proj
- \- *lemma* bundle_mfderiv_tangent_bundle_proj
- \- *lemma* bundle_mfderiv_proj
- \- *lemma* bundle_mfderiv_within_comp_at
- \- *lemma* bundle_mfderiv_comp_at
- \- *lemma* bundle_mfderiv_comp
- \- *lemma* bundle_mfderiv_chart
- \- *lemma* bundle_mfderiv_chart_symm
- \+/\- *def* written_in_ext_chart_at
- \+ *def* tangent_map_within
- \+ *def* tangent_map
- \- *def* bundle_mfderiv_within
- \- *def* bundle_mfderiv

Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+/\- *lemma* model_with_corners.to_local_equiv_coe
- \+/\- *lemma* model_with_corners.mk_coe
- \+/\- *lemma* model_with_corners.to_local_equiv_coe_symm
- \+/\- *lemma* model_with_corners.mk_coe_symm
- \+/\- *lemma* model_with_corners_self_local_equiv
- \+/\- *lemma* model_with_corners_self_coe
- \+/\- *lemma* model_with_corners_self_coe_symm
- \+/\- *lemma* model_with_corners.target
- \+/\- *lemma* model_with_corners.left_inv
- \+/\- *lemma* model_with_corners.left_inv'
- \+/\- *lemma* model_with_corners.right_inv
- \+ *lemma* compatible
- \+ *lemma* mem_maximal_atlas_of_mem_atlas
- \+ *lemma* chart_mem_maximal_atlas
- \+ *lemma* compatible_of_mem_maximal_atlas
- \+/\- *lemma* mem_ext_chart_source
- \+/\- *lemma* ext_chart_at_to_inv
- \+/\- *lemma* ext_chart_model_space_eq_id
- \+ *def* maximal_atlas
- \+/\- *def* ext_chart_at

Modified src/group_theory/monoid_localization.lean


Modified src/linear_algebra/basis.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/ring_theory/localization.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/transport.lean


Modified src/topology/algebra/module.lean


Modified src/topology/local_homeomorph.lean
- \+/\- *lemma* mk_coe
- \+/\- *lemma* mk_coe_symm
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* inv_fun_eq_coe
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_coe_symm
- \+/\- *lemma* map_source
- \+/\- *lemma* map_target
- \+/\- *lemma* left_inv
- \+/\- *lemma* right_inv
- \+ *lemma* image_eq_target_inter_inv_preimage
- \+ *lemma* image_inter_source_eq
- \+ *lemma* symm_image_eq_source_inter_preimage
- \+ *lemma* symm_image_inter_target_eq
- \+/\- *lemma* symm_to_local_equiv
- \+/\- *lemma* symm_symm
- \+/\- *lemma* restr_open_to_local_equiv
- \+/\- *lemma* restr_to_local_equiv
- \+/\- *lemma* restr_coe
- \+/\- *lemma* restr_coe_symm
- \+/\- *lemma* restr_univ
- \+/\- *lemma* refl_local_equiv
- \+/\- *lemma* refl_symm
- \+/\- *lemma* refl_coe
- \+/\- *lemma* of_set_to_local_equiv
- \+/\- *lemma* of_set_coe
- \+/\- *lemma* of_set_symm
- \+/\- *lemma* trans_to_local_equiv
- \+/\- *lemma* coe_trans
- \+/\- *lemma* coe_trans_symm
- \+/\- *lemma* trans_refl
- \+/\- *lemma* refl_trans
- \+/\- *lemma* prod_to_local_equiv
- \+/\- *lemma* prod_coe
- \+/\- *lemma* prod_coe_symm
- \+ *lemma* prod_symm
- \+ *lemma* prod_trans
- \+/\- *lemma* to_homeomorph_coe
- \+/\- *lemma* to_homeomorph_symm_coe
- \+/\- *lemma* to_local_homeomorph_source
- \+/\- *lemma* to_local_homeomorph_target
- \+/\- *lemma* to_local_homeomorph_coe
- \+/\- *lemma* to_local_homeomorph_coe_symm
- \+/\- *lemma* refl_to_local_homeomorph
- \+/\- *lemma* symm_to_local_homeomorph
- \+/\- *lemma* trans_to_local_homeomorph

Modified src/topology/topological_fiber_bundle.lean
- \+/\- *lemma* bundle_trivialization.coe_coe
- \+/\- *lemma* bundle_trivialization.coe_mk
- \+/\- *lemma* bundle_trivialization.coe_fst
- \+/\- *lemma* mem_triv_change_source
- \+/\- *lemma* mem_local_triv'_source
- \+/\- *lemma* mem_local_triv'_target
- \+/\- *lemma* local_triv'_fst
- \+/\- *lemma* local_triv'_inv_fst
- \+/\- *lemma* mem_local_triv_source
- \+/\- *lemma* mem_local_triv_target
- \+/\- *lemma* local_triv_fst
- \+/\- *lemma* local_triv_symm_fst
- \+/\- *lemma* mem_local_triv_at_source
- \+/\- *lemma* local_triv_at_fst
- \+/\- *lemma* local_triv_at_symm_fst
- \+/\- *lemma* local_triv_at_ext_to_local_homeomorph
- \+/\- *def* proj

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
- \+ *lemma* finite.dependent_image
- \+ *lemma* finite.prod
- \+ *lemma* finite.finite_subsets
- \+ *lemma* finite.bdd_above_bUnion
- \+ *lemma* finite.bdd_below_bUnion
- \- *lemma* finite_dependent_image
- \- *lemma* finite_prod
- \- *lemma* finite_subsets_of_finite
- \- *lemma* bdd_above_finite
- \- *lemma* bdd_above_finite_union
- \- *lemma* bdd_below_finite
- \- *lemma* bdd_below_finite_union
- \- *lemma* bdd_above
- \- *lemma* bdd_below
- \+ *theorem* finite.insert
- \+ *theorem* finite.union
- \+ *theorem* finite.subset
- \+ *theorem* finite.image
- \+ *theorem* finite.map
- \+/\- *theorem* finite_of_finite_image
- \+ *theorem* finite_image_iff
- \+ *theorem* finite.preimage
- \+ *theorem* finite.sUnion
- \+ *theorem* finite.bUnion
- \+ *theorem* finite.seq
- \- *theorem* finite_insert
- \- *theorem* finite_union
- \- *theorem* finite_subset
- \- *theorem* finite_image
- \- *theorem* finite_map
- \- *theorem* finite_of_finite_image_on
- \- *theorem* finite_image_iff_on
- \- *theorem* finite_preimage
- \- *theorem* finite_sUnion
- \- *theorem* finite_bUnion
- \- *theorem* finite_bUnion'
- \- *theorem* finite_seq

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean


Modified src/measure_theory/integration.lean
- \- *theorem* measurable

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
- \+ *lemma* ae_ball_iff

Created src/order/filter/countable_Inter.lean
- \+ *lemma* countable_sInter_mem_sets
- \+ *lemma* countable_Inter_mem_sets
- \+ *lemma* countable_bInter_mem_sets
- \+ *lemma* eventually_countable_forall
- \+ *lemma* eventually_countable_ball

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
- \+ *theorem* nhds_basis_closed_eball



## [2020-06-23 16:11:19](https://github.com/leanprover-community/mathlib/commit/62e1364)
chore(linear_algebra/nonsingular_inverse): `matrix.nonsing_inv` no longer requires base ring to carry `has_inv` instance ([#3136](https://github.com/leanprover-community/mathlib/pull/3136))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* inv_mul'
- \+ *lemma* mul_inv'
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* inv_unique
- \+ *lemma* is_unit.unit_spec

Modified src/algebra/invertible.lean
- \+ *lemma* invertible_unique

Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* is_unit_det_transpose
- \+ *lemma* nonsing_inv_apply
- \+/\- *lemma* transpose_nonsing_inv
- \+ *lemma* mul_nonsing_inv
- \+ *lemma* nonsing_inv_mul
- \+ *lemma* nonsing_inv_det
- \+ *lemma* is_unit_nonsing_inv_det
- \+ *lemma* nonsing_inv_nonsing_inv
- \+ *lemma* is_unit_iff_is_unit_det
- \- *lemma* nonsing_inv_val
- \- *theorem* mul_nonsing_inv
- \- *theorem* nonsing_inv_mul
- \- *def* nonsing_inv



## [2020-06-23 14:59:38](https://github.com/leanprover-community/mathlib/commit/ea665e7)
fix(algebra/ordered*): add norm_cast attribute ([#3132](https://github.com/leanprover-community/mathlib/pull/3132))
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* coe_zero
- \+ *lemma* coe_eq_zero
- \+/\- *lemma* coe_one
- \+ *lemma* coe_eq_one
- \+/\- *lemma* coe_add
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1
- \+/\- *lemma* zero_lt_coe
- \+/\- *lemma* bot_add
- \+/\- *lemma* add_bot

Modified src/algebra/ordered_ring.lean
- \- *theorem* coe_eq_zero
- \- *theorem* coe_zero

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* coe_le_coe

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
- \+ *lemma* eventually.filter_mono
- \+ *lemma* eventually_eq.rw
- \+ *lemma* eventually_eq.refl
- \+ *lemma* eventually_eq.symm
- \+ *lemma* eventually_eq.trans
- \+ *lemma* eventually_eq.fun_comp
- \+ *lemma* eventually_eq.comp₂
- \+ *lemma* eventually_eq.mul
- \+ *lemma* eventually_eq.inv
- \+ *lemma* eventually_eq.div
- \+ *lemma* eventually_eq.sub
- \+ *lemma* map_congr
- \- *lemma* map_cong
- \+ *def* eventually_eq

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
- \+ *lemma* eq_univ_of_subset

Modified src/data/set/countable.lean
- \+/\- *lemma* countable.bUnion

Modified src/data/set/lattice.lean
- \+/\- *lemma* sUnion_eq_Union
- \+/\- *lemma* sInter_eq_Inter
- \+/\- *lemma* sInter_bUnion
- \+/\- *lemma* sUnion_bUnion
- \+/\- *theorem* bUnion_eq_Union
- \+/\- *theorem* bInter_eq_Inter
- \+/\- *theorem* sUnion_range
- \+/\- *theorem* sInter_range

Modified src/measure_theory/measure_space.lean


Modified src/topology/basic.lean


Modified src/topology/metric_space/baire.lean
- \+ *lemma* is_Gδ_univ
- \+/\- *lemma* is_Gδ_bInter_of_open
- \+/\- *lemma* is_Gδ_Inter_of_open
- \+ *lemma* is_Gδ_Inter
- \+ *lemma* is_Gδ_bInter
- \+ *lemma* is_Gδ.inter
- \+/\- *theorem* dense_bInter_of_Gδ
- \+ *theorem* dense_inter_of_Gδ



## [2020-06-23 08:40:52](https://github.com/leanprover-community/mathlib/commit/159766e)
chore(topology/metric_space/basic): rename `uniform_continuous_dist'` ([#3145](https://github.com/leanprover-community/mathlib/pull/3145))
* rename `uniform_continuous_dist'` to `uniform_continuous_dist`;
* rename `uniform_continuous_dist` to `uniform_continuous.dist`;
* add `uniform_continuous.nndist`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *lemma* uniform_continuous.nndist
- \+/\- *theorem* uniform_continuous_dist
- \+ *theorem* uniform_continuous.dist
- \- *theorem* uniform_continuous_dist'

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


Created test/instance_cache.lean




## [2020-06-23 04:53:57](https://github.com/leanprover-community/mathlib/commit/c0d74a3)
refactor(group/perm) bundle sign of a perm as a monoid_hom ([#3143](https://github.com/leanprover-community/mathlib/pull/3143))
We're trying to bundle everything right?
#### Estimated changes
Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* eq_sign_of_surjective_hom
- \+/\- *def* sign



## [2020-06-23 03:11:26](https://github.com/leanprover-community/mathlib/commit/23d6141)
chore(algebra/ring,char_zero): generalize some lemmas ([#3141](https://github.com/leanprover-community/mathlib/pull/3141))
`mul_eq_zero` etc only need `[mul_zero_class]` and `[no_zero_divisors]`. In particular, they don't need `has_neg`. Also deduplicate with `group_with_zero.*`.
#### Estimated changes
Modified src/algebra/char_zero.lean


Modified src/algebra/field.lean
- \+/\- *lemma* mul_inv'
- \- *lemma* division_ring.mul_ne_zero
- \- *lemma* mul_ne_zero_comm
- \- *lemma* division_ring.one_div_mul_one_div

Modified src/algebra/group_with_zero.lean
- \+/\- *lemma* div_eq_zero_iff
- \+/\- *lemma* div_ne_zero_iff
- \- *lemma* mul_eq_zero'
- \- *lemma* mul_eq_zero_iff'
- \- *lemma* mul_ne_zero''
- \- *lemma* mul_ne_zero_iff
- \- *lemma* mul_ne_zero_comm''

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ring.lean
- \+/\- *lemma* mul_self_eq_zero
- \+/\- *lemma* zero_eq_mul_self
- \- *lemma* mul_ne_zero
- \+/\- *theorem* mul_eq_zero
- \+/\- *theorem* zero_eq_mul
- \+ *theorem* mul_ne_zero_iff
- \+ *theorem* mul_ne_zero
- \+ *theorem* mul_eq_zero_comm
- \+ *theorem* mul_ne_zero_comm
- \- *theorem* mul_ne_zero'
- \- *theorem* mul_ne_zero_comm'

Modified src/data/rat/cast.lean


Modified src/data/real/nnreal.lean


Modified src/data/support.lean
- \+/\- *lemma* support_mul
- \- *lemma* support_mul'

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
- \+ *theorem* card_insert_of_mem



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
- \+/\- *lemma* one_apply
- \+/\- *lemma* mul_apply
- \+/\- *lemma* inv_apply
- \+/\- *lemma* smul_apply
- \+ *lemma* smul_apply'
- \- *lemma* zero_apply
- \- *lemma* add_apply
- \- *lemma* neg_apply

Modified src/topology/metric_space/pi_Lp.lean


Created test/pi_simp.lean
- \+ *lemma* eval_default_one
- \+ *def* eval_default



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
- \+ *lemma* eq_of_card_le_one_of_prod_eq
- \+ *lemma* eq_of_card_le_one_of_sum_eq
- \+ *lemma* prod_erase
- \+ *lemma* eq_one_of_prod_eq_one

Modified src/data/finset.lean
- \+ *lemma* eq_of_mem_of_not_mem_erase

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.card_le_one_of_subsingleton

Modified src/data/fintype/card.lean
- \+ *lemma* eq_of_subsingleton_of_prod_eq



## [2020-06-22 13:19:55](https://github.com/leanprover-community/mathlib/commit/86dcd5c)
feat(analysis/calculus): C^1 implies strictly differentiable ([#3119](https://github.com/leanprover-community/mathlib/pull/3119))
Over the reals, a continuously differentiable function is strictly differentiable.
Supporting material:  Add a standard mean-value-theorem-related trick as its own lemma, and refactor another proof (in `calculus/extend_deriv`) to use that lemma.
Other material:  an _equality_ (rather than _inequality_) version of the mean value theorem for domains; slight refactor of `normed_space/dual`.
#### Estimated changes
Modified src/analysis/calculus/extend_deriv.lean
- \+/\- *theorem* has_fderiv_at_boundary_of_tendsto_fderiv
- \- *theorem* has_fderiv_at_boundary_of_tendsto_fderiv_aux

Modified src/analysis/calculus/mean_value.lean
- \+ *lemma* strict_fderiv_of_cont_diff
- \+ *theorem* convex.norm_image_sub_le_of_norm_has_fderiv_within_le'
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_within_le'
- \+ *theorem* convex.norm_image_sub_le_of_norm_fderiv_le'
- \+ *theorem* domain_mvt

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* has_ftaylor_series_up_to_on.has_strict_fderiv_at
- \+ *lemma* times_cont_diff_on.has_strict_fderiv_at
- \+ *lemma* times_cont_diff.has_strict_fderiv_at

Modified src/analysis/normed_space/dual.lean
- \+ *lemma* norm_le_dual_bound
- \+/\- *lemma* inclusion_in_double_dual_isometry

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
- \+ *lemma* weighted_vsub_of_point_apply
- \+/\- *lemma* weighted_vsub_of_point_eq_of_sum_eq_zero
- \+/\- *lemma* weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \- *lemma* weighted_vsub_of_point_linear_apply
- \- *lemma* weighted_vsub_of_point_zero
- \- *lemma* weighted_vsub_of_point_smul
- \- *lemma* weighted_vsub_of_point_neg
- \- *lemma* weighted_vsub_of_point_add
- \- *lemma* weighted_vsub_of_point_sub
- \- *lemma* weighted_vsub_zero
- \- *lemma* weighted_vsub_smul
- \- *lemma* weighted_vsub_neg
- \- *lemma* weighted_vsub_add
- \- *lemma* weighted_vsub_sub
- \+/\- *def* weighted_vsub_of_point
- \+/\- *def* weighted_vsub
- \- *def* weighted_vsub_of_point_linear



## [2020-06-22 10:46:14](https://github.com/leanprover-community/mathlib/commit/105fa17)
feat(linear_algebra/matrix): trace of an endomorphism independent of basis ([#3125](https://github.com/leanprover-community/mathlib/pull/3125))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* of_injective_apply

Modified src/linear_algebra/basic.lean
- \+ *lemma* symm_trans_apply
- \+ *lemma* arrow_congr_trans
- \+ *lemma* fun_congr_left_symm
- \+ *theorem* fun_left_apply
- \+ *theorem* fun_left_id
- \+ *theorem* fun_left_comp
- \+ *theorem* fun_congr_left_apply
- \+ *theorem* fun_congr_left_id
- \+ *theorem* fun_congr_left_comp
- \+ *def* fun_left
- \+ *def* fun_congr_left

Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.range

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_equiv_matrix'_apply
- \+ *lemma* linear_equiv_matrix_comp
- \+ *lemma* linear_equiv_matrix_mul
- \+ *lemma* trace_aux_def
- \+ *theorem* to_lin_of_equiv
- \+ *theorem* to_matrix_of_equiv
- \+ *theorem* linear_equiv_matrix_range
- \+ *theorem* trace_aux_eq'
- \+ *theorem* trace_aux_range
- \+ *theorem* trace_aux_eq
- \+ *theorem* trace_eq_matrix_trace
- \+ *theorem* trace_mul_comm
- \+ *def* trace_aux
- \+ *def* trace



## [2020-06-22 08:01:57](https://github.com/leanprover-community/mathlib/commit/068aaaf)
chore(data/finmap): nolint ([#3131](https://github.com/leanprover-community/mathlib/pull/3131))
#### Estimated changes
Modified src/data/finmap.lean
- \+/\- *lemma* mem_iff
- \+/\- *lemma* mem_of_lookup_eq_some
- \+/\- *theorem* to_finmap_nil
- \+/\- *theorem* lookup_list_to_finmap
- \+/\- *theorem* ext_lookup
- \+/\- *theorem* insert_insert
- \+/\- *theorem* to_finmap_cons
- \+/\- *theorem* mem_list_to_finmap
- \+/\- *theorem* insert_singleton_eq
- \+/\- *theorem* lookup_union_left_of_not_in
- \+/\- *theorem* union_cancel
- \+/\- *def* list.to_finmap
- \+/\- *def* singleton
- \+/\- *def* disjoint



## [2020-06-22 07:22:10](https://github.com/leanprover-community/mathlib/commit/3f9b52a)
refactor(ring_theory/*): make PID class a predicate ([#3114](https://github.com/leanprover-community/mathlib/pull/3114))
#### Estimated changes
Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/splitting_field.lean


Modified src/number_theory/sum_two_squares.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideals.lean
- \+ *lemma* factors_decreasing

Modified src/ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* to_maximal_ideal
- \- *lemma* factors_decreasing



## [2020-06-22 00:33:41](https://github.com/leanprover-community/mathlib/commit/6aba958)
chore(scripts): update nolints.txt ([#3133](https://github.com/leanprover-community/mathlib/pull/3133))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-21 21:04:24](https://github.com/leanprover-community/mathlib/commit/d59adc1)
chore(data/list/alist): nolint ([#3129](https://github.com/leanprover-community/mathlib/pull/3129))
#### Estimated changes
Modified src/data/list/alist.lean
- \+/\- *def* disjoint



## [2020-06-21 19:44:08](https://github.com/leanprover-community/mathlib/commit/5b5ff79)
fix(tactic/delta_instance): bug in computing pi arity ([#3127](https://github.com/leanprover-community/mathlib/pull/3127))
#### Estimated changes
Modified src/tactic/core.lean




## [2020-06-21 19:09:48](https://github.com/leanprover-community/mathlib/commit/eff9ed3)
feat(topology/uniform_space): some basic lemmas ([#3123](https://github.com/leanprover-community/mathlib/pull/3123))
This is the second PR on the road to Heine. It contains various elementary lemmas about uniform spaces.
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* comp_rel_mono
- \+ *lemma* subset_comp_self
- \+ *lemma* symmetric_rel_inter
- \+ *lemma* comp_symm_mem_uniformity_sets
- \+ *lemma* subset_comp_self_of_mem_uniformity
- \+ *lemma* comp_comp_symm_mem_uniformity_sets
- \+ *lemma* mem_comp_of_mem_ball
- \+ *lemma* mem_comp_comp
- \+ *lemma* uniform_space.mem_nhds_iff
- \+ *lemma* uniform_space.ball_mem_nhds
- \+ *lemma* uniform_space.mem_nhds_iff_symm
- \+ *lemma* uniform_space.has_basis_nhds
- \+ *lemma* uniform_space.has_basis_nhds_prod
- \+ *lemma* closure_eq_uniformity
- \+ *lemma* uniformity_has_basis_closed
- \+ *lemma* uniformity_has_basis_closure
- \+ *lemma* uniformity_comap



## [2020-06-21 17:25:22](https://github.com/leanprover-community/mathlib/commit/7073c8b)
feat(tactic/cancel_denoms): try to remove numeral denominators  ([#3109](https://github.com/leanprover-community/mathlib/pull/3109))
#### Estimated changes
Created src/tactic/cancel_denoms.lean
- \+ *lemma* mul_subst
- \+ *lemma* div_subst
- \+ *lemma* cancel_factors_eq_div
- \+ *lemma* add_subst
- \+ *lemma* sub_subst
- \+ *lemma* neg_subst
- \+ *lemma* cancel_factors_lt
- \+ *lemma* cancel_factors_le
- \+ *lemma* cancel_factors_eq

Modified src/tactic/default.lean


Modified src/tactic/interactive.lean


Created test/cancel_denoms.lean




## [2020-06-21 16:23:00](https://github.com/leanprover-community/mathlib/commit/b7d056a)
feat(tactic/zify): move nat propositions to int ([#3108](https://github.com/leanprover-community/mathlib/pull/3108))
#### Estimated changes
Modified src/tactic/default.lean


Modified src/tactic/lift.lean


Modified src/tactic/norm_cast.lean


Created src/tactic/zify.lean
- \+ *lemma* int.coe_nat_ne_coe_nat_iff

Created test/zify.lean




## [2020-06-21 15:04:19](https://github.com/leanprover-community/mathlib/commit/d097161)
fix(tactic/set): use provided type for new variable ([#3126](https://github.com/leanprover-community/mathlib/pull/3126))
closes [#3111](https://github.com/leanprover-community/mathlib/pull/3111)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Created test/set.lean
- \+ *def* T
- \+ *def* v
- \+ *def* S
- \+ *def* u
- \+ *def* p



## [2020-06-20 19:21:52](https://github.com/leanprover-community/mathlib/commit/8729fe2)
feat(tactic/simps): option `trace.simps.verbose` prints generated lemmas ([#3121](https://github.com/leanprover-community/mathlib/pull/3121))
#### Estimated changes
Modified src/tactic/simps.lean




## [2020-06-20 15:10:42](https://github.com/leanprover-community/mathlib/commit/e8ff6ff)
feat(*): random lemmas about sets and filters ([#3118](https://github.com/leanprover-community/mathlib/pull/3118))
This is the first in a series of PR that will culminate in a proof of Heine's theorem (a continuous function from a compact separated uniform space to any uniform space is uniformly continuous). I'm slicing a 600 lines files into PRs. This first PR is only about sets, filters and a bit of topology. Uniform spaces stuff will come later.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* inter_compl_nonempty_iff
- \+ *lemma* preimage_coe_coe_diagonal
- \+ *def* diagonal

Modified src/order/filter/bases.lean
- \+ *lemma* has_basis_self
- \+ *lemma* comap_has_basis
- \+ *lemma* has_basis.sInter_sets
- \+ *lemma* has_basis.prod'

Modified src/order/filter/basic.lean
- \+ *lemma* inf_principal_ne_bot_iff
- \+ *lemma* subtype_coe_map_comap
- \+ *lemma* tendsto.prod_map

Modified src/topology/algebra/ordered.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.prod_map
- \+ *lemma* continuous_on.prod_map



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
- \+/\- *lemma* prod_attach
- \+ *lemma* prod_apply_dite
- \+/\- *lemma* prod_apply_ite
- \+ *lemma* prod_dite



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
- \+ *theorem* of_injective
- \- *theorem* of_inj

Modified src/algebra/direct_sum.lean
- \+ *theorem* mk_injective
- \+ *theorem* of_injective
- \- *theorem* mk_inj
- \- *theorem* of_inj

Modified src/algebra/field_power.lean
- \+ *lemma* fpow_injective
- \- *lemma* injective_fpow

Modified src/algebra/group/type_tags.lean
- \+ *lemma* of_mul_injective
- \+ *lemma* to_mul_injective
- \+ *lemma* of_add_injective
- \+ *lemma* to_add_injective
- \- *lemma* of_mul_inj
- \- *lemma* to_mul_inj
- \- *lemma* of_add_inj
- \- *lemma* to_add_inj

Modified src/algebra/module.lean
- \+ *theorem* coe_injective
- \+/\- *theorem* coe_set_eq
- \+/\- *theorem* ext
- \- *theorem* ext'

Modified src/algebra/opposites.lean


Modified src/algebra/pi_instances.lean
- \+ *lemma* inl_injective
- \+ *lemma* inr_injective
- \- *lemma* injective_inl
- \- *lemma* injective_inr

Modified src/algebra/ring.lean
- \+ *theorem* coe_add_monoid_hom_injective
- \+ *theorem* coe_monoid_hom_injective
- \- *theorem* coe_add_monoid_hom_inj
- \- *theorem* coe_monoid_hom_inj

Modified src/analysis/analytic/basic.lean
- \+ *lemma* change_origin_summable_aux_j_injective
- \- *lemma* change_origin_summable_aux_j_inj

Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/point_reflection.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/concrete_category/bundled_hom.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/fully_faithful.lean
- \+ *lemma* map_injective
- \- *lemma* injectivity

Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean


Modified src/combinatorics/composition.lean
- \+ *lemma* embedding_injective
- \- *lemma* embedding_inj

Modified src/computability/partrec_code.lean
- \+ *theorem* const_inj
- \+ *theorem* curry_inj
- \+/\- *theorem* smn
- \- *theorem* injective_const
- \- *theorem* injective_curry

Modified src/control/fold.lean


Modified src/data/dfinsupp.lean
- \+ *theorem* mk_injective
- \- *theorem* mk_inj

Modified src/data/equiv/list.lean


Modified src/data/equiv/mul_add.lean
- \+ *lemma* point_reflection_fixed_iff_of_bit0_injective
- \- *lemma* point_reflection_fixed_iff_of_bit0_inj

Modified src/data/fin.lean
- \+ *lemma* val_injective
- \+ *lemma* succ_injective
- \+ *lemma* cast_le_injective
- \+ *lemma* cast_succ_injective
- \- *lemma* injective_val
- \- *lemma* injective_succ
- \- *lemma* injective_cast_le
- \- *lemma* injective_cast_succ

Modified src/data/finset.lean
- \+ *lemma* pi_cons_injective
- \- *lemma* injective_pi_cons

Modified src/data/finsupp.lean
- \+ *lemma* single_injective
- \+ *lemma* map_domain_injective
- \- *lemma* injective_single
- \- *lemma* injective_map_domain

Modified src/data/int/basic.lean


Modified src/data/list/basic.lean
- \+ *lemma* length_injective_iff
- \+ *lemma* length_injective
- \- *lemma* injective_length_iff
- \- *lemma* injective_length
- \+ *theorem* cons_injective
- \+/\- *theorem* cons_inj
- \+ *theorem* mem_map_of_injective
- \+ *theorem* map_injective_iff
- \- *theorem* cons_inj'
- \- *theorem* mem_map_of_inj
- \- *theorem* injective_map_iff

Modified src/data/multiset.lean
- \+ *lemma* pi_cons_injective
- \- *lemma* injective_pi_cons
- \+ *theorem* mem_map_of_injective
- \+ *theorem* map_injective
- \- *theorem* mem_map_of_inj
- \- *theorem* injective_map

Modified src/data/mv_polynomial.lean
- \+ *lemma* rename_injective
- \- *lemma* injective_rename

Modified src/data/nat/cast.lean


Modified src/data/opposite.lean
- \+ *lemma* op_injective
- \+ *lemma* unop_injective
- \- *lemma* op_inj
- \- *lemma* unop_inj

Modified src/data/option/basic.lean
- \+ *theorem* some_injective
- \+ *theorem* map_injective
- \- *theorem* injective_some
- \- *theorem* injective_map

Modified src/data/pnat/factors.lean
- \+ *theorem* coe_nat_injective
- \+ *theorem* coe_pnat_injective
- \- *theorem* coe_nat_inj
- \- *theorem* coe_pnat_inj

Modified src/data/real/cardinality.lean
- \+ *lemma* cantor_function_injective
- \- *lemma* injective_cantor_function

Modified src/data/real/hyperreal.lean


Modified src/data/set/basic.lean
- \+ *lemma* image_injective
- \+ *lemma* surjective.preimage_injective
- \- *lemma* injective_image
- \- *lemma* surjective.injective_preimage

Modified src/data/set/lattice.lean
- \+ *lemma* sigma_to_Union_surjective
- \+ *lemma* sigma_to_Union_injective
- \+ *lemma* sigma_to_Union_bijective
- \- *lemma* surjective_sigma_to_Union
- \- *lemma* injective_sigma_to_Union
- \- *lemma* bijective_sigma_to_Union

Modified src/data/setoid/basic.lean
- \+ *lemma* ker_lift_injective
- \- *lemma* injective_ker_lift

Modified src/data/sigma/basic.lean
- \+ *lemma* sigma_mk_injective
- \+ *lemma* sigma_map_injective
- \- *lemma* injective_sigma_mk
- \- *lemma* injective_sigma_map

Modified src/deprecated/subgroup.lean
- \+ *lemma* injective_of_trivial_ker
- \+ *lemma* trivial_ker_of_injective
- \+ *lemma* injective_iff_trivial_ker
- \- *lemma* inj_of_trivial_ker
- \- *lemma* trivial_ker_of_inj
- \- *lemma* inj_iff_trivial_ker

Modified src/group_theory/congruence.lean
- \+ *lemma* ker_lift_injective
- \- *lemma* injective_ker_lift

Modified src/group_theory/order_of_element.lean
- \+ *lemma* conj_injective
- \- *lemma* conj_inj

Modified src/group_theory/quotient_group.lean
- \+ *lemma* ker_lift_injective
- \- *lemma* injective_ker_lift

Modified src/group_theory/sylow.lean
- \+ *lemma* mk_vector_prod_eq_one_injective
- \- *lemma* mk_vector_prod_eq_one_inj

Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_eq_of_surjective
- \+ *lemma* dim_le_of_surjective
- \+ *lemma* dim_eq_of_injective
- \+ *lemma* dim_le_of_injective
- \- *lemma* dim_eq_surjective
- \- *lemma* dim_le_surjective
- \- *lemma* dim_eq_injective
- \- *lemma* dim_le_injective

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/logic/embedding.lean
- \+ *theorem* injective
- \- *theorem* inj

Modified src/order/boolean_algebra.lean
- \+ *theorem* compl_injective
- \- *theorem* compl_inj

Modified src/order/complete_boolean_algebra.lean


Modified src/order/filter/basic.lean
- \+ *lemma* pure_injective
- \- *lemma* pure_inj

Modified src/order/filter/filter_product.lean
- \+ *lemma* coe_inj
- \- *lemma* coe_injective
- \+ *theorem* of_injective
- \- *theorem* of_inj

Modified src/order/order_iso.lean
- \+ *theorem* injective
- \+ *theorem* coe_fn_inj
- \- *theorem* inj
- \- *theorem* coe_fn_injective

Modified src/ring_theory/algebra.lean
- \+ *theorem* coe_ring_hom_injective
- \+ *theorem* coe_monoid_hom_injective
- \+ *theorem* coe_add_monoid_hom_injective
- \- *theorem* coe_ring_hom_inj
- \- *theorem* coe_monoid_hom_inj
- \- *theorem* coe_add_monoid_hom_inj

Modified src/ring_theory/ideal_operations.lean
- \+ *lemma* injective_iff_ker_eq_bot
- \- *lemma* inj_iff_ker_eq_bot
- \+ *theorem* quotient_inf_to_pi_quotient_bijective
- \- *theorem* bijective_quotient_inf_to_pi_quotient

Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/set_theory/cardinal.lean
- \+ *lemma* mk_range_eq_of_injective
- \- *lemma* mk_range_eq_of_inj

Modified src/set_theory/ordinal.lean
- \+ *lemma* typein_injective
- \- *lemma* injective_typein

Modified src/set_theory/schroeder_bernstein.lean
- \+ *theorem* min_injective
- \- *theorem* injective_min

Modified src/topology/algebra/open_subgroup.lean
- \+ *lemma* coe_injective
- \+/\- *lemma* ext
- \- *lemma* ext'

Modified src/topology/constructions.lean


Modified src/topology/uniform_space/completion.lean
- \+ *lemma* separated_pure_cauchy_injective
- \- *lemma* injective_separated_pure_cauchy



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
- \+ *lemma* functor_obj
- \+ *lemma* functor_map
- \+ *lemma* nat_trans_app
- \- *lemma* of_function_obj
- \- *lemma* of_function_map
- \- *lemma* of_homs_app
- \- *lemma* of_function_app
- \+ *def* functor
- \+ *def* nat_trans
- \+ *def* nat_iso
- \+ *def* equivalence
- \- *def* of_function
- \- *def* of_homs
- \- *def* of_isos
- \- *def* lift

Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* biproduct_iso

Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/zero.lean




## [2020-06-18 21:08:14](https://github.com/leanprover-community/mathlib/commit/73caeaa)
perf(tactic/linarith): implement redundancy test to reduce number of comparisons ([#3079](https://github.com/leanprover-community/mathlib/pull/3079))
This implements a redundancy check in `linarith` which can drastically reduce the size of the sets of comparisons that the tactic needs to deal with.
`linarith` iteratively transforms sets of inequalities to equisatisfiable sets by eliminating a single variable. If there are `n` comparisons in the set, we expect `O(n^2)` comparisons after one elimination step. Many of these comparisons are redundant, i.e. removing them from the set does not change its satisfiability.
Deciding redundancy is expensive, but there are cheap approximations that are very useful in practice. This PR tests comparisons for non-minimal history (http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.493&rep=rep1&type=pdf p.13, theorem 7). Non-minimal history implies redundancy.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* sin_lt_sin_of_le_of_le_pi_div_two
- \+/\- *lemma* sin_le_sin_of_le_of_le_pi_div_two

Modified src/meta/rb_map.lean


Modified src/tactic/linarith.lean
- \+ *def* vars
- \+ *def* comp.vars
- \+ *def* comp_source.to_string



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
- \+ *def* has_initial
- \+ *def* has_terminal
- \- *def* has_initial_of_has_zero_object
- \- *def* has_terminal_of_has_zero_object



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
- \+/\- *lemma* nonempty_iff_nonempty

Modified src/data/finset.lean
- \+/\- *lemma* coe_ssubset
- \+/\- *lemma* coe_nonempty
- \+/\- *lemma* coe_insert
- \+/\- *lemma* ssubset_iff
- \+/\- *lemma* coe_erase
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* coe_filter
- \+/\- *lemma* coe_image
- \+ *lemma* lt_inf_iff
- \+/\- *lemma* comp_inf_eq_inf_comp
- \- *lemma* lt_inf
- \+/\- *theorem* coe_subset
- \+/\- *theorem* coe_map

Modified src/data/multiset.lean
- \+ *theorem* subset_ndunion_right
- \+ *theorem* ndinter_subset_left

Modified src/data/set/basic.lean
- \+ *theorem* ssubset_iff_insert

Modified src/data/set/lattice.lean
- \+ *lemma* bot_eq_empty
- \+ *lemma* sup_eq_union
- \+ *lemma* inf_eq_inter
- \+ *lemma* le_eq_subset
- \+ *lemma* lt_eq_ssubset

Modified src/logic/function/basic.lean
- \+/\- *def* injective.decidable_eq

Modified src/order/basic.lean
- \- *theorem* monotone.order_dual

Modified src/order/lattice.lean
- \+ *lemma* map_sup
- \+ *lemma* map_inf



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
- \+/\- *lemma* ev_coev



## [2020-06-17 19:57:11](https://github.com/leanprover-community/mathlib/commit/b5baf55)
feat(algebra/linear_ordered_comm_group_with_zero) define linear_ordered_comm_group_with_zero ([#3072](https://github.com/leanprover-community/mathlib/pull/3072))
#### Estimated changes
Created src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* zero_le_one'
- \+ *lemma* zero_lt_one'
- \+ *lemma* zero_le'
- \+ *lemma* not_lt_zero'
- \+ *lemma* le_zero_iff
- \+ *lemma* zero_lt_iff
- \+ *lemma* le_of_le_mul_right
- \+ *lemma* le_mul_inv_of_mul_le
- \+ *lemma* mul_inv_le_of_le_mul
- \+ *lemma* div_le_div'
- \+ *lemma* ne_zero_of_lt
- \+ *lemma* zero_lt_unit
- \+ *lemma* mul_lt_mul''''
- \+ *lemma* mul_inv_lt_of_lt_mul'
- \+ *lemma* mul_lt_right'
- \+ *lemma* inv_lt_inv''
- \+ *lemma* inv_le_inv''

Modified src/algebra/ordered_group.lean
- \+ *lemma* div_le_div_iff'

Modified src/data/real/nnreal.lean




## [2020-06-17 19:10:21](https://github.com/leanprover-community/mathlib/commit/48c4f40)
refactor(measure_theory): make `volume` a bundled measure ([#3075](https://github.com/leanprover-community/mathlib/pull/3075))
This way we can `apply` and `rw` lemmas about `measure`s without
introducing a `volume`-specific version.
#### Estimated changes
Modified src/data/set/disjointed.lean
- \+ *theorem* set.pairwise_on.on_injective
- \+ *theorem* pairwise.pairwise_on

Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* integral_zero

Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_bUnion_finset
- \+ *lemma* sum_measure_le_measure_univ
- \+ *lemma* tsum_measure_le_measure_univ
- \+ *lemma* exists_nonempty_inter_of_measure_univ_lt_tsum_measure
- \+ *lemma* exists_nonempty_inter_of_measure_univ_lt_sum_measure
- \+ *lemma* mem_ae_iff
- \+ *lemma* ae_iff
- \+ *lemma* measure_zero_iff_ae_nmem
- \+ *lemma* ae_of_all
- \+ *lemma* ae_all_iff
- \+ *lemma* ae_eq_refl
- \+ *lemma* ae_eq_symm
- \+ *lemma* ae_eq_trans
- \- *lemma* mem_a_e_iff
- \- *lemma* volume_empty
- \- *lemma* volume_mono
- \- *lemma* volume_mono_null
- \- *lemma* volume_Union_null
- \- *lemma* volume_union_null
- \- *lemma* volume_Union
- \- *lemma* volume_union
- \- *lemma* volume_bUnion
- \- *lemma* volume_sUnion
- \- *lemma* volume_bUnion_finset
- \- *lemma* volume_diff
- \- *lemma* sum_volume_le_volume_univ
- \- *lemma* tsum_volume_le_volume_univ
- \- *lemma* exists_nonempty_inter_of_volume_univ_lt_tsum_volume
- \- *lemma* exists_nonempty_inter_of_volume_univ_lt_sum_volume
- \- *lemma* all_ae_congr
- \- *lemma* all_ae_iff
- \- *lemma* volume_zero_iff_all_ae_nmem
- \- *lemma* all_ae_of_all
- \- *lemma* all_ae_all_iff
- \- *lemma* all_ae_and_iff
- \- *lemma* all_ae_imp_distrib_left
- \- *lemma* all_ae_or_distrib_left
- \- *lemma* all_ae_or_distrib_right
- \- *lemma* all_ae_eq_refl
- \- *lemma* all_ae_eq_symm
- \- *lemma* all_ae_eq_trans
- \- *theorem* volume_Union_le
- \- *theorem* volume_union_le
- \+ *def* ae
- \- *def* a_e
- \- *def* volume
- \- *def* all_ae

Modified src/measure_theory/set_integral.lean


Modified src/measure_theory/simple_func_dense.lean




## [2020-06-17 12:07:34](https://github.com/leanprover-community/mathlib/commit/0736c95)
chore(order/filter/basic): move some parts to new files ([#3087](https://github.com/leanprover-community/mathlib/pull/3087))
Move `at_top`/`at_bot`, `cofinite`, and `ultrafilter` to new files.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/data/analysis/filter.lean


Created src/order/filter/at_top_bot.lean
- \+ *lemma* mem_at_top
- \+ *lemma* Ioi_mem_at_top
- \+ *lemma* mem_at_bot
- \+ *lemma* Iio_mem_at_bot
- \+ *lemma* at_top_ne_bot
- \+ *lemma* mem_at_top_sets
- \+ *lemma* eventually_at_top
- \+ *lemma* eventually.exists_forall_of_at_top
- \+ *lemma* frequently_at_top
- \+ *lemma* frequently_at_top'
- \+ *lemma* frequently.forall_exists_of_at_top
- \+ *lemma* map_at_top_eq
- \+ *lemma* tendsto_at_top
- \+ *lemma* tendsto_at_top_mono'
- \+ *lemma* tendsto_at_top_mono
- \+ *lemma* map_at_top_inf_ne_bot_iff
- \+ *lemma* extraction_of_frequently_at_top'
- \+ *lemma* extraction_of_frequently_at_top
- \+ *lemma* extraction_of_eventually_at_top
- \+ *lemma* exists_le_of_tendsto_at_top
- \+ *lemma* exists_lt_of_tendsto_at_top
- \+ *lemma* high_scores
- \+ *lemma* frequently_high_scores
- \+ *lemma* strict_mono_subseq_of_tendsto_at_top
- \+ *lemma* strict_mono_subseq_of_id_le
- \+ *lemma* strict_mono_tendsto_at_top
- \+ *lemma* tendsto_at_top_add_nonneg_left'
- \+ *lemma* tendsto_at_top_add_nonneg_left
- \+ *lemma* tendsto_at_top_add_nonneg_right'
- \+ *lemma* tendsto_at_top_add_nonneg_right
- \+ *lemma* tendsto_at_top_of_add_const_left
- \+ *lemma* tendsto_at_top_of_add_const_right
- \+ *lemma* tendsto_at_top_of_add_bdd_above_left'
- \+ *lemma* tendsto_at_top_of_add_bdd_above_left
- \+ *lemma* tendsto_at_top_of_add_bdd_above_right'
- \+ *lemma* tendsto_at_top_of_add_bdd_above_right
- \+ *lemma* tendsto_at_top_add_left_of_le'
- \+ *lemma* tendsto_at_top_add_left_of_le
- \+ *lemma* tendsto_at_top_add_right_of_le'
- \+ *lemma* tendsto_at_top_add_right_of_le
- \+ *lemma* tendsto_at_top_add_const_left
- \+ *lemma* tendsto_at_top_add_const_right
- \+ *lemma* tendsto_at_top'
- \+ *lemma* tendsto_at_top_embedding
- \+ *lemma* tendsto_at_top_at_top
- \+ *lemma* tendsto_at_top_at_bot
- \+ *lemma* tendsto_at_top_at_top_of_monotone
- \+ *lemma* tendsto_finset_range
- \+ *lemma* monotone.tendsto_at_top_finset
- \+ *lemma* tendsto_finset_image_at_top_at_top
- \+ *lemma* prod_at_top_at_top_eq
- \+ *lemma* prod_map_at_top_eq
- \+ *lemma* map_at_top_eq_of_gc
- \+ *lemma* map_add_at_top_eq_nat
- \+ *lemma* map_sub_at_top_eq_nat
- \+ *lemma* tendsto_add_at_top_nat
- \+ *lemma* tendsto_sub_at_top_nat
- \+ *lemma* tendsto_add_at_top_iff_nat
- \+ *lemma* map_div_at_top_eq_nat
- \+ *theorem* tendsto_at_top_principal
- \+ *def* at_top
- \+ *def* at_bot

Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean
- \- *lemma* mem_at_top
- \- *lemma* Ioi_mem_at_top
- \- *lemma* mem_at_bot
- \- *lemma* Iio_mem_at_bot
- \- *lemma* at_top_ne_bot
- \- *lemma* mem_at_top_sets
- \- *lemma* eventually_at_top
- \- *lemma* eventually.exists_forall_of_at_top
- \- *lemma* frequently_at_top
- \- *lemma* frequently_at_top'
- \- *lemma* frequently.forall_exists_of_at_top
- \- *lemma* map_at_top_eq
- \- *lemma* tendsto_at_top
- \- *lemma* tendsto_at_top_mono'
- \- *lemma* tendsto_at_top_mono
- \- *lemma* map_at_top_inf_ne_bot_iff
- \- *lemma* extraction_of_frequently_at_top'
- \- *lemma* extraction_of_frequently_at_top
- \- *lemma* extraction_of_eventually_at_top
- \- *lemma* exists_le_of_tendsto_at_top
- \- *lemma* exists_lt_of_tendsto_at_top
- \- *lemma* high_scores
- \- *lemma* frequently_high_scores
- \- *lemma* strict_mono_subseq_of_tendsto_at_top
- \- *lemma* strict_mono_subseq_of_id_le
- \- *lemma* strict_mono_tendsto_at_top
- \- *lemma* tendsto_at_top_add_nonneg_left'
- \- *lemma* tendsto_at_top_add_nonneg_left
- \- *lemma* tendsto_at_top_add_nonneg_right'
- \- *lemma* tendsto_at_top_add_nonneg_right
- \- *lemma* tendsto_at_top_of_add_const_left
- \- *lemma* tendsto_at_top_of_add_const_right
- \- *lemma* tendsto_at_top_of_add_bdd_above_left'
- \- *lemma* tendsto_at_top_of_add_bdd_above_left
- \- *lemma* tendsto_at_top_of_add_bdd_above_right'
- \- *lemma* tendsto_at_top_of_add_bdd_above_right
- \- *lemma* tendsto_at_top_add_left_of_le'
- \- *lemma* tendsto_at_top_add_left_of_le
- \- *lemma* tendsto_at_top_add_right_of_le'
- \- *lemma* tendsto_at_top_add_right_of_le
- \- *lemma* tendsto_at_top_add_const_left
- \- *lemma* tendsto_at_top_add_const_right
- \- *lemma* tendsto_at_top'
- \- *lemma* tendsto_at_top_embedding
- \- *lemma* tendsto_at_top_at_top
- \- *lemma* tendsto_at_top_at_bot
- \- *lemma* tendsto_at_top_at_top_of_monotone
- \- *lemma* tendsto_finset_range
- \- *lemma* monotone.tendsto_at_top_finset
- \- *lemma* tendsto_finset_image_at_top_at_top
- \- *lemma* prod_at_top_at_top_eq
- \- *lemma* prod_map_at_top_eq
- \- *lemma* map_at_top_eq_of_gc
- \- *lemma* map_add_at_top_eq_nat
- \- *lemma* map_sub_at_top_eq_nat
- \- *lemma* tendsto_add_at_top_nat
- \- *lemma* tendsto_sub_at_top_nat
- \- *lemma* tendsto_add_at_top_iff_nat
- \- *lemma* map_div_at_top_eq_nat
- \- *lemma* mem_cofinite
- \- *lemma* cofinite_ne_bot
- \- *lemma* frequently_cofinite_iff_infinite
- \- *lemma* set.infinite_iff_frequently_cofinite
- \- *lemma* nat.cofinite_eq_at_top
- \- *lemma* ultrafilter_unique
- \- *lemma* le_of_ultrafilter
- \- *lemma* ultrafilter_iff_compl_mem_iff_not_mem
- \- *lemma* mem_or_compl_mem_of_ultrafilter
- \- *lemma* mem_or_mem_of_ultrafilter
- \- *lemma* mem_of_finite_sUnion_ultrafilter
- \- *lemma* mem_of_finite_Union_ultrafilter
- \- *lemma* ultrafilter_map
- \- *lemma* ultrafilter_pure
- \- *lemma* ultrafilter_bind
- \- *lemma* exists_ultrafilter
- \- *lemma* ultrafilter_of_spec
- \- *lemma* ultrafilter_of_le
- \- *lemma* ultrafilter_ultrafilter_of
- \- *lemma* ultrafilter_of_ultrafilter
- \- *lemma* sup_of_ultrafilters
- \- *lemma* tendsto_iff_ultrafilter
- \- *lemma* hyperfilter_le_cofinite
- \- *lemma* is_ultrafilter_hyperfilter
- \- *lemma* ultrafilter.eq_iff_val_le_val
- \- *lemma* exists_ultrafilter_iff
- \- *theorem* tendsto_at_top_principal
- \- *theorem* nmem_hyperfilter_of_finite
- \- *theorem* compl_mem_hyperfilter_of_finite
- \- *theorem* mem_hyperfilter_of_finite_compl
- \- *def* at_top
- \- *def* at_bot
- \- *def* cofinite
- \- *def* is_ultrafilter
- \- *def* ultrafilter
- \- *def* ultrafilter.map
- \- *def* ultrafilter.pure
- \- *def* ultrafilter.bind

Created src/order/filter/cofinite.lean
- \+ *lemma* mem_cofinite
- \+ *lemma* cofinite_ne_bot
- \+ *lemma* frequently_cofinite_iff_infinite
- \+ *lemma* set.infinite_iff_frequently_cofinite
- \+ *lemma* nat.cofinite_eq_at_top
- \+ *def* cofinite

Modified src/order/filter/filter_product.lean


Created src/order/filter/ultrafilter.lean
- \+ *lemma* ultrafilter_unique
- \+ *lemma* le_of_ultrafilter
- \+ *lemma* ultrafilter_iff_compl_mem_iff_not_mem
- \+ *lemma* mem_or_compl_mem_of_ultrafilter
- \+ *lemma* mem_or_mem_of_ultrafilter
- \+ *lemma* mem_of_finite_sUnion_ultrafilter
- \+ *lemma* mem_of_finite_Union_ultrafilter
- \+ *lemma* ultrafilter_map
- \+ *lemma* ultrafilter_pure
- \+ *lemma* ultrafilter_bind
- \+ *lemma* exists_ultrafilter
- \+ *lemma* ultrafilter_of_spec
- \+ *lemma* ultrafilter_of_le
- \+ *lemma* ultrafilter_ultrafilter_of
- \+ *lemma* ultrafilter_of_ultrafilter
- \+ *lemma* sup_of_ultrafilters
- \+ *lemma* tendsto_iff_ultrafilter
- \+ *lemma* hyperfilter_le_cofinite
- \+ *lemma* is_ultrafilter_hyperfilter
- \+ *lemma* ultrafilter.eq_iff_val_le_val
- \+ *lemma* exists_ultrafilter_iff
- \+ *theorem* nmem_hyperfilter_of_finite
- \+ *theorem* compl_mem_hyperfilter_of_finite
- \+ *theorem* mem_hyperfilter_of_finite_compl
- \+ *def* is_ultrafilter
- \+ *def* ultrafilter
- \+ *def* ultrafilter.map
- \+ *def* ultrafilter.pure
- \+ *def* ultrafilter.bind

Modified src/order/liminf_limsup.lean


Modified src/topology/basic.lean




## [2020-06-17 11:06:54](https://github.com/leanprover-community/mathlib/commit/077cd7c)
feat(algebra/category/Algebra): basic setup for category of bundled R-algebras ([#3047](https://github.com/leanprover-community/mathlib/pull/3047))
Just boilerplate. If I don't run out of enthusiasm I'll do tensor product of R-algebras soon. ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))
#### Estimated changes
Created src/algebra/category/Algebra/basic.lean
- \+ *lemma* of_apply
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *def* of
- \+ *def* of_self_iso
- \+ *def* alg_equiv.to_Algebra_iso
- \+ *def* to_alg_equiv
- \+ *def* alg_equiv_iso_Algebra_iso

Modified src/algebra/category/Module/basic.lean
- \+ *def* linear_equiv_iso_Module_iso
- \- *def* linear_equiv_iso_Group_iso

Modified src/ring_theory/algebra.lean
- \+ *lemma* ext
- \+ *lemma* coe_fun_injective
- \+ *lemma* coe_ring_equiv_injective



## [2020-06-17 09:57:50](https://github.com/leanprover-community/mathlib/commit/54441b5)
feat(algebra/group_action_hom): define equivariant maps ([#2866](https://github.com/leanprover-community/mathlib/pull/2866))
#### Estimated changes
Created src/algebra/group_action_hom.lean
- \+ *lemma* map_smul
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* to_quotient_apply
- \+ *lemma* coe_fn_coe
- \+ *lemma* coe_fn_coe'
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *def* comp
- \+ *def* to_quotient



## [2020-06-17 03:12:21](https://github.com/leanprover-community/mathlib/commit/e40de30)
chore(category_theory/closed): move one thing to monoidal closed and fix naming ([#3090](https://github.com/leanprover-community/mathlib/pull/3090))
Move one of the CCC defs to MCC as an example, and make the naming consistent.
#### Estimated changes
Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* terminal_exponentiable

Modified src/category_theory/closed/monoidal.lean
- \+ *def* unit_closed

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
- \+ *theorem* strong_rec_on_beta'
- \+ *def* strong_rec_on'

Modified src/data/set/finite.lean
- \+ *lemma* seq_of_forall_finite_exists

Modified src/data/set/lattice.lean
- \+ *theorem* bUnion_subset_bUnion
- \+ *theorem* bUnion_mono

Modified src/order/basic.lean
- \+ *lemma* id_le

Modified src/order/filter/bases.lean
- \+ *lemma* subseq_tendsto

Modified src/order/filter/basic.lean
- \+ *lemma* frequently_of_forall
- \+ *lemma* extraction_of_frequently_at_top'
- \+ *lemma* extraction_of_frequently_at_top
- \+ *lemma* extraction_of_eventually_at_top
- \+ *lemma* exists_le_of_tendsto_at_top
- \+ *lemma* exists_lt_of_tendsto_at_top
- \+ *lemma* high_scores
- \+ *lemma* frequently_high_scores
- \+ *lemma* strict_mono_subseq_of_tendsto_at_top
- \+ *lemma* strict_mono_subseq_of_id_le
- \+ *lemma* strict_mono_tendsto_at_top

Modified src/tactic/monotonicity/lemmas.lean


Modified src/topology/bases.lean
- \+ *lemma* tendsto_subseq

Modified src/topology/metric_space/basic.lean
- \+ *lemma* ball_eq_ball
- \+ *lemma* ball_eq_ball'
- \+/\- *lemma* totally_bounded_of_finite_discretization
- \+ *lemma* bounded_closure_of_bounded
- \+ *theorem* finite_approx_of_totally_bounded

Modified src/topology/sequences.lean
- \+ *lemma* seq_compact.subseq_of_frequently_in
- \+ *lemma* seq_compact_space.tendsto_subseq
- \+ *lemma* compact.seq_compact
- \+ *lemma* compact.tendsto_subseq'
- \+ *lemma* compact.tendsto_subseq
- \+ *lemma* compact_space.tendsto_subseq
- \+ *lemma* lebesgue_number_lemma_seq
- \+ *lemma* seq_compact.totally_bounded
- \+ *lemma* uniform_space.compact_space_iff_seq_compact_space
- \+ *lemma* metric.compact_iff_seq_compact
- \+ *lemma* tendsto_subseq_of_frequently_bounded
- \+ *lemma* tendsto_subseq_of_bounded
- \+ *lemma* metric.compact_space_iff_seq_compact_space
- \+ *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+ *def* seq_compact

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
- \+/\- *lemma* add_mul_self_eq
- \- *def* dvd_of_mul_right_eq
- \- *def* dvd_of_mul_left_eq
- \- *def* dvd.trans



## [2020-06-16 17:08:01](https://github.com/leanprover-community/mathlib/commit/ae6bf56)
feat(ring_theory/tensor_product): tensor product of algebras ([#3050](https://github.com/leanprover-community/mathlib/pull/3050))
The R-algebra structure on the tensor product of two R-algebras.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* mk_apply
- \+/\- *lemma* coe_to_equiv
- \+ *lemma* to_fun_apply
- \+ *lemma* inv_fun_apply
- \+/\- *theorem* coe_coe

Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* comm_tmul

Modified src/ring_theory/algebra.lean
- \+ *lemma* mk_apply
- \+ *lemma* to_fun_apply
- \+ *lemma* coe_alg_hom
- \+ *lemma* inv_fun_apply
- \- *lemma* coe_to_alg_equiv
- \+/\- *theorem* ext
- \+ *theorem* ext_iff
- \+ *def* of_alg_hom

Created src/ring_theory/tensor_product.lean
- \+ *lemma* mul_aux_apply
- \+ *lemma* mul_apply
- \+ *lemma* mul_assoc'
- \+ *lemma* mul_assoc
- \+ *lemma* one_mul
- \+ *lemma* mul_one
- \+ *lemma* one_def
- \+ *lemma* mul_tmul
- \+ *lemma* algebra_map_apply
- \+ *lemma* alg_equiv_of_linear_equiv_tensor_product_apply
- \+ *lemma* alg_equiv_of_linear_equiv_triple_tensor_product_apply
- \+ *lemma* assoc_aux_1
- \+ *lemma* assoc_aux_2
- \+ *lemma* congr_apply
- \+ *lemma* congr_symm_apply
- \+ *theorem* ext
- \+ *theorem* lid_tmul
- \+ *theorem* rid_tmul
- \+ *theorem* comm_tmul
- \+ *theorem* map_tmul
- \+ *def* mul_aux
- \+ *def* mul
- \+ *def* tensor_algebra_map
- \+ *def* include_left
- \+ *def* include_right
- \+ *def* alg_hom_of_linear_map_tensor_product
- \+ *def* alg_equiv_of_linear_equiv_tensor_product
- \+ *def* alg_equiv_of_linear_equiv_triple_tensor_product
- \+ *def* map
- \+ *def* congr



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
Created src/analysis/convex/caratheodory.lean
- \+ *lemma* mem_convex_hull_erase
- \+ *lemma* step
- \+ *lemma* shrink'
- \+ *lemma* shrink
- \+ *lemma* convex_hull_subset_union
- \+ *theorem* convex_hull_eq_union
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
- \+ *lemma* exists_is_basis_finset
- \+ *lemma* of_finset_basis
- \+ *lemma* findim_eq_card_finset_basis



## [2020-06-15 23:58:09](https://github.com/leanprover-community/mathlib/commit/a796008)
feat(category_theory): cartesian closed categories ([#2894](https://github.com/leanprover-community/mathlib/pull/2894))
Cartesian closed categories, from my topos project.
#### Estimated changes
Created src/category_theory/closed/cartesian.lean
- \+ *lemma* ev_coev
- \+ *lemma* coev_ev
- \+ *lemma* curry_natural_left
- \+ *lemma* curry_natural_right
- \+ *lemma* uncurry_natural_right
- \+ *lemma* uncurry_natural_left
- \+ *lemma* uncurry_curry
- \+ *lemma* curry_uncurry
- \+ *lemma* curry_eq_iff
- \+ *lemma* eq_curry_iff
- \+ *lemma* uncurry_eq
- \+ *lemma* curry_eq
- \+ *lemma* uncurry_id_eq_ev
- \+ *lemma* curry_id_eq_coev
- \+ *lemma* curry_injective
- \+ *lemma* uncurry_injective
- \+ *lemma* pre_id
- \+ *lemma* pre_map
- \+ *lemma* pre_post_comm
- \+ *lemma* exp_comparison_natural_left
- \+ *lemma* exp_comparison_natural_right
- \+ *def* binary_product_exponentiable
- \+ *def* terminal_exponentiable
- \+ *def* exp
- \+ *def* exp.adjunction
- \+ *def* ev
- \+ *def* coev
- \+ *def* curry
- \+ *def* uncurry
- \+ *def* exp_terminal_iso_self
- \+ *def* internalize_hom
- \+ *def* pre
- \+ *def* internal_hom
- \+ *def* zero_mul
- \+ *def* mul_zero
- \+ *def* pow_zero
- \+ *def* prod_coprod_distrib
- \+ *def* cartesian_closed_of_equiv
- \+ *def* exp_comparison

Created src/category_theory/closed/monoidal.lean


Modified src/category_theory/epi_mono.lean
- \+ *def* is_iso_of_epi_of_split_mono
- \+ *def* is_iso_of_mono_of_split_epi

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* inv_prod_comparison_map_fst
- \+ *lemma* inv_prod_comparison_map_snd
- \+ *lemma* prod_comparison_inv_natural

Modified src/category_theory/monoidal/category.lean
- \+ *lemma* tensor_left_tensor_hom_app
- \+ *lemma* tensor_left_tensor_inv_app
- \+ *lemma* tensor_right_tensor_hom_app
- \+ *lemma* tensor_right_tensor_inv_app
- \+ *def* tensor_left
- \+ *def* tensor_left_tensor
- \+ *def* tensor_right
- \+ *def* tensor_right_tensor

Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* tensor_obj
- \+ *lemma* tensor_hom



## [2020-06-15 20:59:03](https://github.com/leanprover-community/mathlib/commit/25e414d)
feat(tactic/linarith): nlinarith tactic ([#2637](https://github.com/leanprover-community/mathlib/pull/2637))
Based on Coq's [nra](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.nra) tactic, and requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nonlinear.20linarith).
#### Estimated changes
Modified src/data/bool.lean


Modified src/data/list/defs.lean
- \+ *def* mmap'_diag

Modified src/tactic/linarith.lean
- \+ *lemma* mul_zero_eq
- \+ *lemma* zero_mul_eq

Modified test/linarith.lean
- \+ *lemma* norm_nonpos_left
- \- *lemma* test6



## [2020-06-15 16:49:19](https://github.com/leanprover-community/mathlib/commit/2e752e1)
feat(tactic/group): group normalization tactic ([#3062](https://github.com/leanprover-community/mathlib/pull/3062))
A tactic to normalize expressions in multiplicative groups.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* mul_gpow_neg_one
- \+ *lemma* mul_self_gpow
- \+ *lemma* mul_gpow_self

Modified src/tactic/default.lean


Created src/tactic/group.lean
- \+ *lemma* tactic.group.gpow_trick
- \+ *lemma* tactic.group.gpow_trick_one
- \+ *lemma* tactic.group.gpow_trick_one'
- \+ *lemma* tactic.group.gpow_trick_sub

Created test/group.lean
- \+ *def* commutator
- \+ *def* commutator3



## [2020-06-15 15:45:46](https://github.com/leanprover-community/mathlib/commit/aa35f36)
feat(analysis/hofer): Hofer's lemma ([#3064](https://github.com/leanprover-community/mathlib/pull/3064))
Adds Hofer's lemma about complete metric spaces, with supporting material.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* pos_div_pow_pos
- \+ *lemma* div_pow_le

Created src/analysis/hofer.lean
- \+ *lemma* hofer

Modified src/analysis/specific_limits.lean
- \+ *lemma* geom_lt
- \+ *lemma* tendsto_at_top_of_geom_lt
- \+ *lemma* sum_geometric_two_le

Modified src/order/filter/basic.lean
- \+ *lemma* inf_eq_bot_iff
- \+ *lemma* tendsto.not_tendsto
- \+ *lemma* Ioi_mem_at_top
- \+ *lemma* mem_at_bot
- \+ *lemma* Iio_mem_at_bot

Modified src/topology/algebra/ordered.lean
- \+ *lemma* Iio_mem_nhds
- \+ *lemma* Ioi_mem_nhds
- \+ *lemma* Ioo_mem_nhds
- \+ *lemma* disjoint_nhds_at_top
- \+ *lemma* inf_nhds_at_top
- \+ *lemma* disjoint_nhds_at_bot
- \+ *lemma* inf_nhds_at_bot
- \+ *lemma* not_tendsto_nhds_of_tendsto_at_top
- \+ *lemma* not_tendsto_at_top_of_tendsto_nhds
- \+ *lemma* not_tendsto_nhds_of_tendsto_at_bot
- \+ *lemma* not_tendsto_at_bot_of_tendsto_nhds



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
- \+ *lemma* ext
- \+ *lemma* ext_of_direction_eq
- \+ *lemma* direction_mk_of_point_of_direction
- \+ *lemma* mem_mk_of_point_of_direction
- \+ *lemma* mk_of_point_of_direction_eq
- \+ *def* mk_of_point_of_direction



## [2020-06-15 02:06:19](https://github.com/leanprover-community/mathlib/commit/543359c)
feat(field_theory/finite): Chevalley–Warning ([#1564](https://github.com/leanprover-community/mathlib/pull/1564))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* coe_subtype_equiv_codomain
- \+ *lemma* subtype_equiv_codomain_apply
- \+ *lemma* coe_subtype_equiv_codomain_symm
- \+ *lemma* subtype_equiv_codomain_symm_apply
- \+ *lemma* subtype_equiv_codomain_symm_apply_eq
- \+ *lemma* subtype_equiv_codomain_symm_apply_ne
- \+ *def* subtype_equiv_codomain

Modified src/data/finsupp.lean
- \+ *lemma* prod_fintype

Modified src/data/mv_polynomial.lean
- \+ *lemma* eval₂_eq
- \+ *lemma* eval₂_eq'
- \+ *lemma* eval_eq
- \+ *lemma* eval_eq'
- \+ *lemma* eval_sum
- \+ *lemma* eval_prod
- \+ *lemma* exists_degree_lt

Created src/field_theory/chevalley_warning.lean
- \+ *lemma* mv_polynomial.sum_mv_polynomial_eq_zero
- \+ *theorem* char_dvd_card_solutions_family
- \+ *theorem* char_dvd_card_solutions



## [2020-06-15 01:22:53](https://github.com/leanprover-community/mathlib/commit/3a66d9a)
feat(polynomial): generalising some material to (noncomm_)semiring ([#3043](https://github.com/leanprover-community/mathlib/pull/3043))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* coeff_sum
- \+ *lemma* monomial_one_eq_X_pow
- \+ *lemma* monomial_eq_smul_X
- \+/\- *lemma* coeff_X_pow
- \+/\- *lemma* C_def
- \+/\- *lemma* single_eq_C_mul_X
- \+/\- *lemma* sum_C_mul_X_eq
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \+/\- *lemma* C_mul
- \+/\- *lemma* C_add
- \+/\- *lemma* C_pow
- \+/\- *lemma* nat_cast_eq_C
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_C_zero
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* C_mul'
- \+/\- *def* polynomial
- \+/\- *def* C

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
- \- *lemma* findim_euclidean_space2
- \+/\- *def* euclidean_quadrant
- \- *def* euclidean_space2



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
- \+ *lemma* vadd_apply

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* weighted_vsub_of_point_linear_apply
- \+ *lemma* weighted_vsub_of_point_zero
- \+ *lemma* weighted_vsub_of_point_smul
- \+ *lemma* weighted_vsub_of_point_neg
- \+ *lemma* weighted_vsub_of_point_add
- \+ *lemma* weighted_vsub_of_point_sub
- \+ *lemma* weighted_vsub_of_point_eq_of_sum_eq_zero
- \+ *lemma* weighted_vsub_of_point_vadd_eq_of_sum_eq_one
- \+ *lemma* weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero
- \+ *lemma* weighted_vsub_zero
- \+ *lemma* weighted_vsub_smul
- \+ *lemma* weighted_vsub_neg
- \+ *lemma* weighted_vsub_add
- \+ *lemma* weighted_vsub_sub
- \+ *lemma* affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one
- \+ *lemma* weighted_vsub_vadd_affine_combination
- \+ *lemma* affine_combination_vsub
- \+ *def* weighted_vsub_of_point
- \+ *def* weighted_vsub_of_point_linear
- \+ *def* weighted_vsub
- \+ *def* affine_combination



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
- \+/\- *lemma* mem_coe
- \+ *theorem* ext_iff
- \+/\- *theorem* ext
- \+/\- *theorem* coe_inj
- \+ *theorem* ssubset_iff_of_subset
- \- *theorem* ext'

Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/totient.lean


Modified src/data/set/basic.lean
- \+ *lemma* ssubset_iff_of_subset

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
- \+ *lemma* inner_comm
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_smul_left
- \+ *lemma* inner_smul_right
- \+/\- *lemma* norm_eq_sqrt_inner
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* inner_add_add_self
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* abs_inner_le_norm
- \+/\- *lemma* inner_self_nonneg
- \+ *lemma* findim_euclidean_space
- \+ *lemma* findim_euclidean_space_fin
- \- *lemma* euclidean_space.inner_def
- \+ *def* to_has_inner
- \+ *def* to_has_norm
- \+ *def* to_normed_group
- \+ *def* to_normed_space
- \+ *def* inner_product_space.of_core
- \+/\- *def* euclidean_space
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
- \+ *def* linexp
- \+ *def* scale
- \+ *def* get
- \+ *def* contains
- \+ *def* zfind
- \+ *def* cmp
- \+ *def* ineq.cmp
- \- *def* ineq.is_lt

Modified test/linarith.lean
- \+ *lemma* test6



## [2020-06-14 12:37:42](https://github.com/leanprover-community/mathlib/commit/7f60a62)
chore(order/basic): move unbundled order classes to `rel_classes ([#3066](https://github.com/leanprover-community/mathlib/pull/3066))
Reason: these classes are rarely used in `mathlib`, we don't need to mix them with classes extending `has_le`.
#### Estimated changes
Modified src/data/list/basic.lean


Modified src/order/basic.lean
- \- *lemma* antisymm_of_asymm
- \- *lemma* trans_trichotomous_left
- \- *lemma* trans_trichotomous_right
- \- *lemma* not_bounded_iff
- \- *lemma* not_unbounded_iff
- \- *theorem* is_refl.swap
- \- *theorem* is_irrefl.swap
- \- *theorem* is_trans.swap
- \- *theorem* is_antisymm.swap
- \- *theorem* is_asymm.swap
- \- *theorem* is_total.swap
- \- *theorem* is_trichotomous.swap
- \- *theorem* is_preorder.swap
- \- *theorem* is_strict_order.swap
- \- *theorem* is_partial_order.swap
- \- *theorem* is_total_preorder.swap
- \- *theorem* is_linear_order.swap
- \- *theorem* is_irrefl_of_is_asymm
- \- *theorem* is_strict_total_order'.swap
- \- *theorem* is_order_connected.neg_trans
- \- *theorem* is_strict_weak_order_of_is_order_connected
- \- *theorem* has_min
- \- *theorem* min_mem
- \- *theorem* not_lt_min
- \- *def* partial_order_of_SO
- \- *def* linear_order_of_STO'
- \- *def* decidable_linear_order_of_STO'
- \- *def* unbounded
- \- *def* bounded

Modified src/order/order_iso.lean


Created src/order/rel_classes.lean
- \+ *lemma* trans_trichotomous_left
- \+ *lemma* trans_trichotomous_right
- \+ *lemma* not_bounded_iff
- \+ *lemma* not_unbounded_iff
- \+ *theorem* is_refl.swap
- \+ *theorem* is_irrefl.swap
- \+ *theorem* is_trans.swap
- \+ *theorem* is_antisymm.swap
- \+ *theorem* is_asymm.swap
- \+ *theorem* is_total.swap
- \+ *theorem* is_trichotomous.swap
- \+ *theorem* is_preorder.swap
- \+ *theorem* is_strict_order.swap
- \+ *theorem* is_partial_order.swap
- \+ *theorem* is_total_preorder.swap
- \+ *theorem* is_linear_order.swap
- \+ *theorem* is_strict_total_order'.swap
- \+ *theorem* is_order_connected.neg_trans
- \+ *theorem* is_strict_weak_order_of_is_order_connected
- \+ *theorem* has_min
- \+ *theorem* min_mem
- \+ *theorem* not_lt_min
- \+ *def* partial_order_of_SO
- \+ *def* linear_order_of_STO'
- \+ *def* decidable_linear_order_of_STO'
- \+ *def* unbounded
- \+ *def* bounded



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


Created src/analysis/normed_space/dual.lean
- \+ *lemma* dual_def
- \+ *lemma* double_dual_bound
- \+ *lemma* inclusion_in_double_dual_isometry
- \+ *def* inclusion_in_double_dual'
- \+ *def* inclusion_in_double_dual

Modified src/analysis/normed_space/hahn_banach.lean
- \+ *lemma* coord_self'
- \+ *lemma* coord_norm'
- \+ *theorem* exists_dual_vector
- \+ *theorem* exists_dual_vector'

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* to_span_singleton_homothety
- \+ *lemma* homothety_norm
- \+ *lemma* to_span_singleton_norm
- \+ *lemma* homothety_inverse
- \+ *lemma* to_span_nonzero_singleton_homothety
- \+ *lemma* coord_norm
- \+ *def* of_homothety
- \+ *def* to_span_singleton
- \+ *def* to_span_nonzero_singleton

Modified src/linear_algebra/basic.lean
- \+ *lemma* mem_span_singleton_self
- \+ *lemma* span_singleton_eq_range
- \+ *lemma* to_span_singleton_one
- \+ *lemma* to_span_nonzero_singleton_one
- \+ *lemma* coord_self
- \+ *def* to_span_singleton
- \+ *def* to_span_nonzero_singleton

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
- \+/\- *lemma* bit0_re
- \+/\- *lemma* bit1_re
- \+/\- *lemma* bit0_im
- \+/\- *lemma* bit1_im
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* I_re
- \+/\- *lemma* I_im
- \+ *lemma* conj_bit0
- \+ *lemma* conj_bit1
- \+/\- *lemma* conj_sub
- \+/\- *lemma* conj_inv
- \+/\- *lemma* abs_abs_sub_le_abs_sub
- \- *lemma* conj_two
- \+ *theorem* equiv_real_prod_apply
- \+ *theorem* equiv_real_prod_symm_re
- \+ *theorem* equiv_real_prod_symm_im
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_rat_cast
- \+/\- *theorem* re_eq_add_conj
- \- *theorem* real_prod_equiv_apply
- \- *theorem* real_prod_equiv_symm_re
- \- *theorem* real_prod_equiv_symm_im
- \+ *def* equiv_real_prod
- \+/\- *def* I
- \- *def* real_prod_equiv

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


Created src/algebra/continued_fractions/computation/correctness_terminating.lean
- \+ *lemma* comp_exact_value_correctness_of_stream_eq_some
- \+ *lemma* comp_exact_value_correctness_of_stream_eq_none
- \+ *lemma* of_correctness_of_terminates
- \+ *lemma* of_correctness_at_top_of_terminates
- \+ *theorem* of_correctness_of_terminated_at

Modified src/algebra/continued_fractions/computation/default.lean


Modified src/algebra/continued_fractions/continuants_recurrence.lean


Modified src/algebra/continued_fractions/convergents_equiv.lean




## [2020-06-14 08:08:09](https://github.com/leanprover-community/mathlib/commit/fdc326c)
feat(geometry/euclidean): sum of angles of a triangle ([#2994](https://github.com/leanprover-community/mathlib/pull/2994))
Item 27 from the 100-theorems list.
#### Estimated changes
Modified src/geometry/euclidean.lean
- \+ *lemma* cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle
- \+ *lemma* sin_angle_sub_add_angle_sub_rev_eq_sin_angle
- \+ *lemma* cos_angle_add_angle_sub_add_angle_sub_eq_neg_one
- \+ *lemma* sin_angle_add_angle_sub_add_angle_sub_eq_zero
- \+ *lemma* angle_add_angle_sub_add_angle_sub_eq_pi
- \+ *lemma* angle_add_angle_add_angle_eq_pi



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
- \+/\- *def* preorder.lift
- \+/\- *def* partial_order.lift
- \+/\- *def* linear_order.lift
- \+/\- *def* decidable_linear_order.lift

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
- \+ *lemma* rpow_neg_one
- \+/\- *lemma* top_rpow_of_pos
- \+/\- *lemma* top_rpow_of_neg
- \+/\- *lemma* zero_rpow_of_pos
- \+/\- *lemma* zero_rpow_of_neg
- \+/\- *lemma* rpow_eq_zero_iff
- \+/\- *lemma* rpow_eq_top_iff
- \+ *lemma* mul_rpow_of_nonneg
- \+ *lemma* to_real_rpow

Created src/topology/metric_space/pi_Lp.lean
- \+ *lemma* lipschitz_with_equiv
- \+ *lemma* antilipschitz_with_equiv
- \+ *lemma* aux_uniformity_eq
- \+ *lemma* norm_eq
- \+ *lemma* add_apply
- \+ *lemma* sub_apply
- \+ *lemma* smul_apply
- \+ *lemma* neg_apply
- \+ *def* pi_Lp
- \+ *def* emetric_aux



## [2020-06-13 13:42:10](https://github.com/leanprover-community/mathlib/commit/cc16d35)
feat(linear_algebra/finite_dimensional): cardinalities and linear independence ([#3056](https://github.com/leanprover-community/mathlib/pull/3056))
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* cardinal_mk_le_findim_of_linear_independent
- \+ *lemma* fintype_card_le_findim_of_linear_independent
- \+ *lemma* finset_card_le_findim_of_linear_independent
- \+ *lemma* exists_nontrivial_relation_of_dim_lt_card
- \+ *lemma* exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
- \+ *lemma* exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card



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
- \+/\- *theorem* mul_comm'
- \+ *theorem* foo



## [2020-06-13 11:08:57](https://github.com/leanprover-community/mathlib/commit/a22b657)
refactor(topology/uniform_space): docstring and notation ([#3052](https://github.com/leanprover-community/mathlib/pull/3052))
The goal of this PR is to make `topology/uniform_space/basic.lean` more accessible. 
First it introduces the standard notation for relation composition that was inexplicably not used before. I used a non-standard unicode circle here `\ciw` but this is up for discussion as long as it looks like a composition circle.
Then I introduced balls as discussed on [this Zulip topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/notations.20for.20uniform.20spaces).  There could be used more, but at least this should be mostly sufficient for following PRs.
And of course I put a huge module docstring. As with `order/filter/basic.lean`, I think we need more mathematical explanations than in the average mathlib file.
I also added a bit of content about symmetric entourages but I don't have enough courage to split this off unless someone really insists.
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* id_comp_rel
- \+ *lemma* symmetric_symmetrize_rel
- \+ *lemma* symmetrize_rel_subset_self
- \+ *lemma* symmetrize_mono
- \+/\- *lemma* comp_le_uniformity
- \+ *lemma* symmetrize_mem_uniformity
- \+ *lemma* mem_ball_comp
- \+ *lemma* ball_subset_of_comp_subset
- \+ *lemma* ball_mono
- \+ *lemma* mem_ball_symmetry
- \+ *lemma* ball_eq_of_symmetry
- \+ *lemma* is_open_iff_ball_subset
- \+/\- *lemma* filter.has_basis.mem_uniformity_iff
- \+ *lemma* uniform_space.has_basis_symmetric
- \+ *lemma* uniform_space.has_seq_basis
- \+ *theorem* uniform_continuous_iff_eventually
- \+ *def* symmetric_rel
- \+ *def* symmetrize_rel
- \+ *def* uniform_space.ball



## [2020-06-13 09:51:05](https://github.com/leanprover-community/mathlib/commit/938b73a)
feat(topology/metric_space/pi_lp): Holder and Minkowski inequalities in ennreal ([#2988](https://github.com/leanprover-community/mathlib/pull/2988))
Hölder and Minkowski inequalities for finite sums. Versions for ennreals.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_eq_top_iff

Modified src/analysis/mean_inequalities.lean
- \+ *theorem* inner_le_Lp_mul_Lq
- \+ *theorem* Lp_add_le

Modified src/data/real/ennreal.lean
- \+ *lemma* one_to_real
- \+ *lemma* one_to_nnreal
- \+ *lemma* sum_eq_top_iff



## [2020-06-13 09:19:08](https://github.com/leanprover-community/mathlib/commit/dc69dc3)
refactor(ci): only update nolints once a day ([#3036](https://github.com/leanprover-community/mathlib/pull/3036))
This PR moves the update nolints step to a new GitHub actions workflow `update_nolints.yml` which runs once a day.
#### Estimated changes
Modified .github/workflows/build.yml


Created .github/workflows/update_nolints.yml


Modified scripts/update_nolints.sh




## [2020-06-13 07:27:55](https://github.com/leanprover-community/mathlib/commit/1645542)
feat(linear_algebra): elements of a dim zero space ([#3054](https://github.com/leanprover-community/mathlib/pull/3054))
#### Estimated changes
Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_zero_iff_forall_zero
- \+ *lemma* dim_pos_iff_exists_ne_zero

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional_of_dim_eq_zero
- \+ *lemma* findim_eq_zero_of_dim_eq_zero
- \+ *lemma* finite_dimensional_bot
- \+ *lemma* findim_bot
- \+ *lemma* bot_eq_top_of_dim_eq_zero

Modified src/set_theory/cardinal.lean
- \+ *lemma* mk_emptyc_iff



## [2020-06-12 18:08:42](https://github.com/leanprover-community/mathlib/commit/51ad2a1)
chore(*): update to Lean 3.16.2c ([#3053](https://github.com/leanprover-community/mathlib/pull/3053))
#### Estimated changes
Modified leanpkg.toml




## [2020-06-12 18:08:40](https://github.com/leanprover-community/mathlib/commit/ce594be)
feat(linear_algebra/affine_space): define a few affine maps ([#2981](https://github.com/leanprover-community/mathlib/pull/2981))
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* linear_map_vsub
- \+/\- *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_const
- \+ *lemma* const_linear
- \+ *lemma* coe_zero
- \+ *lemma* zero_linear
- \+ *lemma* coe_add
- \+ *lemma* add_linear
- \+ *lemma* vadd_apply
- \+ *lemma* vsub_apply
- \+ *lemma* id_linear
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* comp_assoc
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* line_map_apply
- \+ *lemma* line_map_linear
- \+ *lemma* line_map_zero
- \+ *lemma* line_map_apply_zero
- \+ *lemma* affine_apply_line_map
- \+ *lemma* affine_comp_line_map
- \+ *lemma* line_map_vadd_neg
- \+ *lemma* coe_smul
- \+ *lemma* homothety_def
- \+ *lemma* homothety_apply
- \+ *lemma* homothety_one
- \+ *lemma* homothety_mul
- \+ *lemma* homothety_zero
- \+ *lemma* homothety_add
- \+ *lemma* coe_homothety_hom
- \+ *lemma* coe_homothety_affine
- \+ *lemma* coe_to_affine_map
- \+ *lemma* to_affine_map_linear
- \- *lemma* map_vsub
- \+ *def* const
- \+ *def* line_map
- \+ *def* homothety
- \+ *def* homothety_hom
- \+ *def* homothety_affine
- \+ *def* to_affine_map



## [2020-06-12 16:33:01](https://github.com/leanprover-community/mathlib/commit/1429279)
feat(data/*): lemmas converting finset, set.finite, and their card ([#3042](https://github.com/leanprover-community/mathlib/pull/3042))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* finset.attach_eq_univ

Modified src/data/set/finite.lean
- \+ *lemma* finite.card_to_finset



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
- \+/\- *lemma* is_cau_series_of_abv_le_cau
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* abv_sum_le_sum_abv
- \+/\- *lemma* is_cau_exp
- \+/\- *lemma* cos_bound
- \+/\- *lemma* sin_bound
- \+/\- *def* exp'
- \+/\- *def* exp
- \+/\- *def* sin
- \+/\- *def* cos
- \+/\- *def* tan
- \+/\- *def* sinh
- \+/\- *def* cosh
- \+/\- *def* tanh



## [2020-06-12 11:43:11](https://github.com/leanprover-community/mathlib/commit/5808afc)
feat(analysis/mean_inequalities): Holder and Minkowski inequalities ([#3025](https://github.com/leanprover-community/mathlib/pull/3025))
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* geom_mean_le_arith_mean_weighted
- \+ *theorem* pow_arith_mean_le_arith_mean_pow
- \+ *theorem* pow_arith_mean_le_arith_mean_pow_of_even
- \+ *theorem* fpow_arith_mean_le_arith_mean_fpow
- \+ *theorem* rpow_arith_mean_le_arith_mean_rpow
- \+ *theorem* arith_mean_le_rpow_mean
- \+ *theorem* geom_mean_le_arith_mean2_weighted
- \+ *theorem* geom_mean_le_arith_mean3_weighted
- \+ *theorem* inner_le_Lp_mul_Lq
- \+ *theorem* is_greatest_Lp
- \+ *theorem* Lp_add_le
- \+ *theorem* inner_le_Lp_mul_Lq_of_nonneg
- \+ *theorem* Lp_add_le_of_nonneg
- \- *theorem* am_gm_weighted
- \- *theorem* am_gm2_weighted
- \- *theorem* am_gm3_weighted
- \- *theorem* pow_am_le_am_pow
- \- *theorem* pow_am_le_am_pow_of_even
- \- *theorem* fpow_am_le_am_fpow
- \- *theorem* rpow_am_le_am_rpow



## [2020-06-12 11:10:43](https://github.com/leanprover-community/mathlib/commit/27a0946)
chore(scripts): update nolints.txt ([#3046](https://github.com/leanprover-community/mathlib/pull/3046))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-06-12 10:19:27](https://github.com/leanprover-community/mathlib/commit/30e620c)
chore(data/real/cau_seq): linting ([#3040](https://github.com/leanprover-community/mathlib/pull/3040))
#### Estimated changes
Modified src/data/real/cau_seq.lean
- \+/\- *theorem* cauchy₂
- \+/\- *theorem* cauchy₃
- \+/\- *theorem* equiv_def₃
- \+/\- *def* lim_zero
- \+/\- *def* inv



## [2020-06-12 09:31:29](https://github.com/leanprover-community/mathlib/commit/0f6b3ca)
doc(data/complex/basic): docstrings and pp_nodots ([#3044](https://github.com/leanprover-community/mathlib/pull/3044))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+/\- *def* norm_sq



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
- \+/\- *def* Ad

Modified src/algebra/module.lean
- \+/\- *lemma* map_add
- \+/\- *lemma* map_smul
- \+/\- *lemma* zero_mem
- \+/\- *lemma* add_mem
- \+/\- *lemma* smul_mem
- \+/\- *lemma* sum_mem
- \+ *lemma* coe_to_add_subgroup
- \+/\- *lemma* neg_mem_iff
- \+/\- *theorem* is_linear
- \+ *theorem* coe_sort_coe
- \+/\- *theorem* ext'
- \+ *theorem* coe_set_eq
- \+ *theorem* ext'_iff
- \+/\- *theorem* ext
- \+ *theorem* to_add_submonoid_injective
- \+ *theorem* to_add_submonoid_eq
- \+/\- *def* mk'
- \+ *def* to_add_subgroup

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
- \+/\- *lemma* mem_coe

Modified src/linear_algebra/affine_space.lean


Modified src/linear_algebra/basic.lean
- \+/\- *theorem* map_add
- \+/\- *theorem* map_smul
- \+/\- *def* to_add_equiv

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
- \+ *lemma* mem_coe
- \+ *lemma* mem_coe_opens
- \+ *lemma* mem_coe_subgroup
- \+/\- *lemma* ext'
- \+/\- *lemma* ext
- \+ *lemma* ext_iff
- \+/\- *lemma* coe_inf
- \+ *lemma* coe_subset
- \+ *lemma* coe_subgroup_le
- \+ *lemma* is_open_of_mem_nhds
- \+/\- *lemma* is_open_of_open_subgroup
- \+ *lemma* is_open_mono
- \+/\- *lemma* is_open_of_open_subideal
- \- *lemma* coe_injective
- \- *lemma* is_open_of_nonempty_open_subset
- \- *lemma* le_iff
- \- *lemma* is_open_of_open_submodule
- \- *def* open_subgroup

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
- \+ *lemma* finite_le_nat
- \+ *lemma* finite_lt_nat



## [2020-06-11 20:24:48](https://github.com/leanprover-community/mathlib/commit/666b9e5)
refactor(analysis/mean_inequalities): review ([#3023](https://github.com/leanprover-community/mathlib/pull/3023))
Also add several lemmas to other files
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \+ *lemma* div_mul_cancel_of_imp
- \+ *lemma* mul_div_cancel_of_imp
- \+ *lemma* mul_div_cancel_left_of_imp
- \+ *lemma* mul_div_cancel_of_imp'

Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_on_id
- \+ *lemma* convex_on_const

Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/mean_inequalities.lean
- \+ *theorem* am_gm_weighted
- \+ *theorem* am_gm2_weighted
- \+ *theorem* am_gm3_weighted
- \+ *theorem* young_inequality_of_nonneg
- \+ *theorem* young_inequality
- \+ *theorem* pow_am_le_am_pow
- \+ *theorem* pow_am_le_am_pow_of_even
- \+ *theorem* fpow_am_le_am_fpow
- \+ *theorem* rpow_am_le_am_rpow
- \- *theorem* real.am_gm_weighted
- \- *theorem* nnreal.am_gm_weighted
- \- *theorem* nnreal.am_gm2_weighted
- \- *theorem* real.am_gm2_weighted
- \- *theorem* nnreal.am_gm3_weighted
- \- *theorem* nnreal.young_inequality
- \- *theorem* real.young_inequality
- \- *theorem* real.pow_am_le_am_pow
- \- *theorem* nnreal.pow_am_le_am_pow
- \- *theorem* real.pow_am_le_am_pow_of_even
- \- *theorem* real.fpow_am_le_am_fpow

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_sub
- \+ *lemma* rpow_sub'
- \+/\- *lemma* rpow_le_rpow
- \+ *lemma* rpow_lt_rpow_iff
- \+ *lemma* rpow_le_rpow_iff
- \+/\- *lemma* rpow_add

Modified src/data/real/conjugate_exponents.lean
- \+ *lemma* nonneg
- \+ *lemma* sub_one_pos
- \+ *lemma* one_div_nonneg
- \+ *lemma* conjugate_eq
- \+ *lemma* sub_one_mul_conj
- \+ *lemma* mul_eq_add
- \+/\- *lemma* is_conjugate_exponent_iff
- \+/\- *lemma* is_conjugate_exponent_conjugate_exponent

Modified src/data/real/nnreal.lean
- \+ *lemma* div_self_le
- \- *lemma* div_mul_cancel



## [2020-06-11 18:53:58](https://github.com/leanprover-community/mathlib/commit/257d1b7)
feat(*): preparations for Caratheodory's convexity theorem ([#3030](https://github.com/leanprover-community/mathlib/pull/3030))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* exists_pos_of_sum_zero_of_exists_nonzero

Modified src/algebra/ordered_field.lean


Modified src/data/equiv/basic.lean
- \+ *lemma* sum_diff_subset_apply_inl
- \+ *lemma* sum_diff_subset_apply_inr
- \+ *lemma* sum_diff_subset_symm_apply_of_mem
- \+ *lemma* sum_diff_subset_symm_apply_of_not_mem
- \+ *theorem* apply_range_symm

Modified src/data/finset.lean
- \+ *lemma* coe_mem
- \+ *lemma* mk_coe
- \+ *lemma* filter_ne
- \+ *lemma* filter_ne'

Modified src/data/set/basic.lean
- \+ *lemma* coe_inclusion

Modified src/data/set/finite.lean
- \+ *lemma* finite_to_set_to_finset

Modified src/data/set/lattice.lean
- \+ *theorem* subset_subset_Union

Modified src/linear_algebra/basis.lean
- \+ *lemma* exists_sum_is_basis
- \+ *theorem* linear_dependent_iff

Modified src/linear_algebra/dimension.lean
- \+ *lemma* cardinal_le_dim_of_linear_independent
- \+ *lemma* cardinal_le_dim_of_linear_independent'

Modified src/logic/embedding.lean
- \+ *def* inl
- \+ *def* inr



## [2020-06-11 18:53:56](https://github.com/leanprover-community/mathlib/commit/447a2d6)
chore(data/matrix/basic): move numeral section into diagonal ([#3022](https://github.com/leanprover-community/mathlib/pull/3022))
Since the numeral section defines numerals for matrices as scalar
multiples of `one_val`, which is the identity matrix, these are defined
solely for diagonal matrices of type `matrix n n r`. So the numeral
section should be in the diagonal section.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* bit0_val
- \+/\- *theorem* diagonal_add



## [2020-06-11 18:19:12](https://github.com/leanprover-community/mathlib/commit/1df9301)
feat(group_theory/semidirect_product): introduce semidirect_products of groups ([#3028](https://github.com/leanprover-community/mathlib/pull/3028))
#### Estimated changes
Created src/group_theory/semidirect_product.lean
- \+ *lemma* one_left
- \+ *lemma* one_right
- \+ *lemma* inv_left
- \+ *lemma* inv_right
- \+ *lemma* mul_left
- \+ *lemma* mul_right
- \+ *lemma* left_inl
- \+ *lemma* right_inl
- \+ *lemma* inl_injective
- \+ *lemma* inl_inj
- \+ *lemma* left_inr
- \+ *lemma* right_inr
- \+ *lemma* inr_injective
- \+ *lemma* inr_inj
- \+ *lemma* inl_aut
- \+ *lemma* inl_left_mul_inr_right
- \+ *lemma* right_hom_eq_right
- \+ *lemma* right_hom_comp_inl
- \+ *lemma* right_hom_comp_inr
- \+ *lemma* right_hom_inl
- \+ *lemma* right_hom_inr
- \+ *lemma* right_hom_surjective
- \+ *lemma* range_inl_eq_ker_right_hom
- \+ *lemma* lift_inl
- \+ *lemma* lift_comp_inl
- \+ *lemma* lift_inr
- \+ *lemma* lift_comp_inr
- \+ *lemma* lift_unique
- \+ *def* inl
- \+ *def* inr
- \+ *def* right_hom
- \+ *def* lift



## [2020-06-11 15:35:28](https://github.com/leanprover-community/mathlib/commit/ce48b6b)
chore(data/finsupp): drop `finsupp.module` and `vector_space` ([#3009](https://github.com/leanprover-community/mathlib/pull/3009))
These instances are not needed as `module` and `vector_space` are abbreviations for `semimodule`.
Also add two bundled versions of `eval`: as `add_monoid_hom` and as `linear_map`.
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* eval_add_hom_apply
- \+ *lemma* coe_leval'
- \+ *lemma* coe_leval
- \+ *def* eval_add_hom
- \+ *def* leval'
- \+ *def* leval

Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean


Modified src/data/polynomial.lean


Modified src/field_theory/mv_polynomial.lean


Modified test/library_search/ring_theory.lean




## [2020-06-11 11:41:18](https://github.com/leanprover-community/mathlib/commit/cf0c6b8)
chore(*): use prod and sum notation ([#3027](https://github.com/leanprover-community/mathlib/pull/3027))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_mul_distrib
- \+/\- *lemma* prod_Ico_id_eq_fact

Modified src/algebra/pi_instances.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean
- \+/\- *lemma* norm_def
- \+/\- *lemma* ratio_le_op_norm
- \+/\- *lemma* op_norm_le_bound
- \+/\- *theorem* continuous_of_bound
- \+/\- *theorem* bound
- \+/\- *theorem* le_op_norm
- \+/\- *def* mk_continuous
- \+/\- *def* op_norm

Modified src/data/complex/exponential.lean
- \+/\- *lemma* exp_sum

Modified src/data/dfinsupp.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/card.lean
- \+/\- *theorem* fin.prod_univ_zero

Modified src/data/monoid_algebra.lean


Modified src/data/mv_polynomial.lean
- \+/\- *lemma* support_sum_monomial_coeff
- \+/\- *lemma* as_sum

Modified src/data/real/nnreal.lean


Modified src/data/set/finite.lean


Modified src/deprecated/submonoid.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* det_diagonal

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
- \+ *theorem* pairwise_coprime_X_sub

Created src/ring_theory/coprime.lean
- \+ *theorem* nat.is_coprime_iff_coprime
- \+ *theorem* is_coprime.symm
- \+ *theorem* is_coprime_comm
- \+ *theorem* is_coprime_self
- \+ *theorem* is_coprime_zero_left
- \+ *theorem* is_coprime_zero_right
- \+ *theorem* is_coprime_one_left
- \+ *theorem* is_coprime_one_right
- \+ *theorem* is_coprime.dvd_of_dvd_mul_right
- \+ *theorem* is_coprime.dvd_of_dvd_mul_left
- \+ *theorem* is_coprime.mul_left
- \+ *theorem* is_coprime.mul_right
- \+ *theorem* is_coprime.prod_left
- \+ *theorem* is_coprime.prod_right
- \+ *theorem* is_coprime.mul_dvd
- \+ *theorem* finset.prod_dvd_of_coprime
- \+ *theorem* fintype.prod_dvd_of_coprime
- \+ *theorem* is_coprime.of_mul_left_left
- \+ *theorem* is_coprime.of_mul_left_right
- \+ *theorem* is_coprime.of_mul_right_left
- \+ *theorem* is_coprime.of_mul_right_right
- \+ *theorem* is_coprime.mul_left_iff
- \+ *theorem* is_coprime.mul_right_iff
- \+ *theorem* is_coprime.prod_left_iff
- \+ *theorem* is_coprime.prod_right_iff
- \+ *theorem* is_coprime.of_prod_left
- \+ *theorem* is_coprime.of_prod_right
- \+ *theorem* is_coprime.pow_left
- \+ *theorem* is_coprime.pow_right
- \+ *theorem* is_coprime.pow
- \+ *theorem* is_coprime.is_unit_of_dvd
- \+ *theorem* is_coprime.map
- \+ *def* is_coprime

Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/ideals.lean
- \- *theorem* is_coprime_def
- \- *theorem* is_coprime_self
- \- *def* is_coprime



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
- \+ *lemma* findim_matrix



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


Created src/tactic/generalizes.lean


Created test/generalizes.lean
- \+ *lemma* example_from_docs₁
- \+ *lemma* example_from_docs₂
- \+ *lemma* test₁
- \+ *lemma* test₂
- \+ *lemma* eq_cons_inversion



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
- \- *lemma* division_def
- \- *lemma* mul_inv_cancel
- \- *lemma* inv_mul_cancel
- \- *lemma* div_eq_mul_one_div
- \- *lemma* mul_one_div_cancel
- \- *lemma* one_div_mul_cancel
- \- *lemma* div_self
- \- *lemma* one_div_one
- \- *lemma* mul_div_assoc
- \- *lemma* one_div_ne_zero
- \- *lemma* ne_zero_of_one_div_ne_zero
- \- *lemma* inv_ne_zero
- \- *lemma* eq_zero_of_one_div_eq_zero
- \- *lemma* one_inv_eq
- \- *lemma* div_one
- \- *lemma* zero_div
- \- *lemma* div_helper
- \- *lemma* mul_div_cancel
- \- *lemma* div_mul_cancel
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_mul_left
- \- *lemma* mul_div_mul_right
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \- *lemma* one_div_mul_one_div
- \- *lemma* div_mul_right
- \- *lemma* mul_div_cancel_left
- \- *lemma* mul_div_cancel'
- \- *lemma* div_mul_div
- \- *lemma* mul_div_mul_left
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm
- \- *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_div_div_div_eq
- \- *lemma* div_mul_eq_div_mul_one_div
- \- *theorem* inv_one

Modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_inv_cancel
- \+ *lemma* inv_ne_zero
- \+ *lemma* inv_mul_cancel
- \+ *lemma* one_inv_eq
- \+ *lemma* inv_one
- \+ *lemma* div_self
- \+ *lemma* div_one
- \+ *lemma* zero_div
- \+ *lemma* div_mul_cancel
- \+ *lemma* mul_div_cancel
- \+ *lemma* mul_div_assoc
- \+ *lemma* div_eq_mul_one_div
- \+ *lemma* mul_one_div_cancel
- \+ *lemma* one_div_mul_cancel
- \+ *lemma* one_div_one
- \+ *lemma* one_div_ne_zero
- \+ *lemma* div_mul_left
- \+ *lemma* mul_div_mul_right
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* div_mul_right
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_cancel'
- \+ *lemma* div_mul_div
- \+ *lemma* mul_div_mul_left
- \+ *lemma* div_mul_eq_mul_div
- \+ *lemma* div_mul_eq_mul_div_comm
- \+ *lemma* mul_eq_mul_of_div_eq_div
- \+ *lemma* div_div_eq_mul_div
- \+ *lemma* div_div_eq_div_mul
- \+ *lemma* div_div_div_div_eq
- \+ *lemma* div_mul_eq_div_mul_one_div
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right
- \+ *lemma* ne_zero_of_one_div_ne_zero
- \+ *lemma* eq_zero_of_one_div_eq_zero
- \+ *lemma* div_helper
- \- *lemma* mul_inv_cancel'
- \- *lemma* inv_ne_zero'
- \- *lemma* inv_mul_cancel'
- \- *lemma* inv_one'
- \- *lemma* div_self'
- \- *lemma* div_one'
- \- *lemma* zero_div'
- \- *lemma* div_mul_cancel'
- \- *lemma* mul_div_cancel''
- \- *lemma* mul_div_assoc''
- \- *lemma* div_eq_mul_one_div'
- \- *lemma* mul_one_div_cancel'
- \- *lemma* one_div_mul_cancel'
- \- *lemma* one_div_one'
- \- *lemma* one_div_ne_zero'
- \- *lemma* one_div_mul_one_div'
- \- *lemma* div_mul_right'
- \- *lemma* div_mul_left'
- \- *lemma* mul_div_cancel_left'
- \- *lemma* mul_div_cancel'''
- \- *lemma* div_mul_div'
- \- *lemma* mul_div_mul_left'
- \- *lemma* mul_div_mul_right'
- \- *lemma* div_mul_eq_mul_div'
- \- *lemma* div_mul_eq_mul_div_comm'
- \- *lemma* mul_eq_mul_of_div_eq_div'
- \- *lemma* div_div_eq_mul_div'
- \- *lemma* div_div_eq_div_mul'
- \- *lemma* div_div_div_div_eq'
- \- *lemma* div_mul_eq_div_mul_one_div'
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_left'
- \- *lemma* eq_of_mul_eq_mul_of_nonzero_right'
- \- *lemma* ne_zero_of_one_div_ne_zero'
- \- *lemma* eq_zero_of_one_div_eq_zero'
- \- *lemma* div_helper'

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
- \+/\- *lemma* union_apply_left
- \+/\- *lemma* union_apply_right
- \+ *theorem* coe_of_bijective
- \- *theorem* of_bijective_to_fun
- \+ *def* {u'
- \+/\- *def* Pi_congr_right
- \+/\- *def* psigma_equiv_sigma
- \+/\- *def* sigma_congr_right
- \+/\- *def* list_equiv_of_equiv
- \+/\- *def* subtype_congr_right
- \+ *def* subtype_equiv_of_subtype
- \+/\- *def* unique_unique_equiv
- \- *def* equiv_pempty
- \- *def* decidable_eq_of_equiv
- \- *def* inhabited_of_equiv
- \- *def* unique_of_equiv

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
- \+/\- *lemma* mk_subtype_of_equiv
- \+/\- *theorem* mk_union_add_mk_inter
- \+/\- *theorem* mk_union_of_disjoint

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
- \+/\- *theorem* map_refl

Modified src/logic/embedding.lean
- \+ *lemma* refl_to_embedding
- \+ *lemma* trans_to_embedding

Modified src/tactic/equiv_rw.lean




## [2020-06-10 11:19:50](https://github.com/leanprover-community/mathlib/commit/b932a51)
feat(data/set/function): add lemmas about `semiconj` ([#3007](https://github.com/leanprover-community/mathlib/pull/3007))
Also redefine `set.maps_to` to avoid unfolding `mem_preimage`.
#### Estimated changes
Modified src/analysis/calculus/inverse.lean


Modified src/data/set/function.lean
- \+ *lemma* maps_to_image
- \+ *lemma* maps_to_range
- \+ *lemma* surj_on_image
- \+ *lemma* surj_on_range
- \+ *lemma* inj_on_image
- \+ *lemma* inj_on_range
- \+ *lemma* bij_on_image
- \+ *lemma* bij_on_range
- \+ *lemma* maps_to_preimage
- \+ *lemma* inj_on_preimage
- \+/\- *theorem* inv_on.bij_on
- \+/\- *def* maps_to

Modified src/linear_algebra/basis.lean




## [2020-06-10 09:47:17](https://github.com/leanprover-community/mathlib/commit/836c0a2)
chore(*): use sum notation ([#3014](https://github.com/leanprover-community/mathlib/pull/3014))
The biggest field test of the new summation notation.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *theorem* exists_le_of_sum_le

Modified src/algebra/direct_sum.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/ring.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/convex/basic.lean
- \+/\- *lemma* finset.center_mass_insert
- \+/\- *lemma* finset.center_mass_eq_of_sum_1
- \+/\- *lemma* convex.sum_mem

Modified src/analysis/mean_inequalities.lean
- \+/\- *theorem* nnreal.am_gm_weighted
- \+/\- *theorem* nnreal.pow_am_le_am_pow

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_sum_le
- \+/\- *lemma* nnnorm_sum_le

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/composition.lean
- \+/\- *lemma* sum_blocks_fun

Modified src/data/complex/exponential.lean
- \+/\- *lemma* is_cau_series_of_abv_cau
- \+/\- *lemma* is_cau_geo_series_const
- \+/\- *lemma* is_cau_exp
- \+/\- *lemma* exp_sum
- \+/\- *def* exp'

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
- \+/\- *lemma* sum_totient

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
- \+/\- *lemma* trace_diag

Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* map_sum_finset_aux

Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* of_fintype

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
- \+/\- *lemma* has_sum_sum_of_ne_finset_zero
- \+/\- *lemma* has_sum_fintype
- \+/\- *lemma* tsum_fintype
- \+/\- *def* has_sum

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
- \+ *lemma* coe_uncurry
- \+ *lemma* coe_uncurry_symm



## [2020-06-10 07:15:39](https://github.com/leanprover-community/mathlib/commit/6a0412e)
chore(data/fintype): generalise `to_finset_card` ([#2316](https://github.com/leanprover-community/mathlib/pull/2316))
Slight generalisation of a lemma, allowing a more flexible `fintype` instance.
Also americanises some spelling. :-)
#### Estimated changes
Modified archive/imo1988_q6.lean


Modified archive/sensitivity.lean


Modified src/data/equiv/basic.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* to_finset_card

Modified src/data/set/finite.lean
- \+/\- *lemma* to_finset_inter
- \- *lemma* to_finset_card



## [2020-06-10 00:06:07](https://github.com/leanprover-community/mathlib/commit/f1df14c)
feat(group_theory/subgroup): normal_closure and gpowers ([#2959](https://github.com/leanprover-community/mathlib/pull/2959))
Transfer some more proofs from `deprecated/subgroup`
#### Estimated changes
Modified src/deprecated/subgroup.lean
- \- *lemma* injective_mul
- \- *lemma* mem_conjugates_self
- \- *lemma* mem_conjugates_of_set_iff
- \- *lemma* conj_mem_conjugates_of_set
- \+ *theorem* conjugates_of_set_subset'
- \- *theorem* subset_conjugates_of_set
- \- *theorem* conjugates_of_set_mono
- \- *theorem* conjugates_of_set_subset
- \- *def* conjugates
- \- *def* conjugates_of_set

Modified src/group_theory/subgroup.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_mk
- \+ *lemma* coe_pow
- \+ *lemma* coe_gpow
- \+/\- *lemma* bot_normal
- \+/\- *lemma* le_normalizer_of_normal
- \+ *lemma* mem_conjugates_self
- \+ *lemma* mem_conjugates_of_set_iff
- \+ *lemma* conjugates_subset_normal
- \+ *lemma* conj_mem_conjugates_of_set
- \+ *lemma* normal_closure_normal
- \+ *lemma* normal_closure_subset_iff
- \+ *lemma* coe_smul
- \+ *lemma* coe_gsmul
- \+ *lemma* range_eq_map
- \+ *lemma* subgroup.normal.comap
- \+ *lemma* subgroup.normal_comap
- \+ *lemma* monoid_hom.normal_ker
- \+ *lemma* mem_gpowers
- \+ *lemma* gpowers_eq_closure
- \+ *lemma* mem_gmultiples
- \+ *lemma* gmultiples_eq_closure
- \- *lemma* conj_mem
- \- *lemma* normal_ker
- \+ *theorem* subset_conjugates_of_set
- \+ *theorem* conjugates_of_set_mono
- \+ *theorem* conjugates_of_set_subset
- \+ *theorem* conjugates_of_set_subset_normal_closure
- \+ *theorem* subset_normal_closure
- \+ *theorem* normal_closure_le_normal
- \+ *theorem* normal_closure_mono
- \+ *theorem* normal_closure_eq_infi
- \+ *def* of_div
- \+ *def* conjugates
- \+ *def* conjugates_of_set
- \+ *def* normal_closure
- \+/\- *def* range
- \+ *def* gpowers
- \+ *def* gmultiples
- \- *def* normal



## [2020-06-09 21:53:37](https://github.com/leanprover-community/mathlib/commit/4e1558b)
chore(algebra/group_power): simp attribute on nsmul_eq_mul and gsmul_eq_mul ([#2983](https://github.com/leanprover-community/mathlib/pull/2983))
Also fix the resulting lint failures, corresponding to the fact that several lemmas are not in simp normal form any more.
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* cast_nat_mul_right
- \+ *lemma* cast_nat_mul_left
- \+ *lemma* cast_nat_mul_cast_nat_mul
- \+ *lemma* cast_int_mul_right
- \+ *lemma* cast_int_mul_left
- \+ *lemma* cast_int_mul_cast_int_mul
- \- *lemma* nsmul_right
- \- *lemma* nsmul_left
- \- *lemma* nsmul_nsmul
- \- *lemma* gsmul_right
- \- *lemma* gsmul_left
- \- *lemma* gsmul_gsmul
- \+/\- *theorem* nat.nsmul_eq_mul
- \+/\- *theorem* nsmul_eq_mul
- \+/\- *theorem* gsmul_eq_mul
- \+ *theorem* cast_nat_mul_right
- \+ *theorem* cast_nat_mul_left
- \+ *theorem* cast_nat_mul_cast_nat_mul
- \+ *theorem* self_cast_nat_mul
- \+ *theorem* cast_nat_mul_self
- \+ *theorem* self_cast_nat_mul_cast_nat_mul
- \+ *theorem* self_cast_int_mul
- \+ *theorem* cast_int_mul_self
- \+ *theorem* self_cast_int_mul_cast_int_mul
- \- *theorem* nsmul_right
- \- *theorem* nsmul_left
- \- *theorem* nsmul_nsmul
- \- *theorem* self_nsmul
- \- *theorem* nsmul_self
- \- *theorem* self_nsmul_nsmul
- \- *theorem* self_gsmul
- \- *theorem* gsmul_self
- \- *theorem* self_gsmul_gsmul

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* coe_nat_mul_eq_nsmul
- \+ *lemma* coe_int_mul_eq_gsmul
- \- *lemma* coe_smul
- \- *lemma* coe_gsmul

Modified src/data/real/nnreal.lean




## [2020-06-09 20:16:58](https://github.com/leanprover-community/mathlib/commit/a02ab48)
refactor(group_theory/subgroup): swap `mul_mem_cancel_left/right` ([#3011](https://github.com/leanprover-community/mathlib/pull/3011))
This way the name follows the position of the term we cancel.
#### Estimated changes
Modified src/deprecated/subgroup.lean
- \+/\- *lemma* mul_mem_cancel_right
- \+/\- *lemma* mul_mem_cancel_left

Modified src/group_theory/coset.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/subgroup.lean
- \+/\- *lemma* mul_mem_cancel_right
- \+/\- *lemma* mul_mem_cancel_left
- \+ *theorem* inv_mem_iff

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
- \+ *lemma* mul_le_mul_left'
- \+ *lemma* mul_le_mul_right'
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* mul_le_mul'
- \+ *lemma* le_mul_of_one_le_right''
- \+ *lemma* le_mul_of_one_le_left''
- \+ *lemma* lt_of_mul_lt_mul_right'
- \+ *lemma* le_mul_of_one_le_of_le'
- \+ *lemma* le_mul_of_le_of_one_le'
- \+ *lemma* one_le_mul'
- \+ *lemma* mul_one_lt_of_one_lt_of_one_le'
- \+ *lemma* mul_one_lt'
- \+ *lemma* mul_one_lt_of_one_le_of_one_lt'
- \+ *lemma* mul_le_one'
- \+ *lemma* mul_le_of_le_one_of_le'
- \+ *lemma* mul_le_of_le_of_le_one'
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one'
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one'
- \+ *lemma* mul_lt_one'
- \+ *lemma* lt_mul_of_one_le_of_lt'
- \+ *lemma* lt_mul_of_lt_of_one_le'
- \+ *lemma* lt_mul_of_one_lt_of_lt'
- \+ *lemma* lt_mul_of_lt_of_one_lt'
- \+ *lemma* mul_lt_of_le_one_of_lt'
- \+ *lemma* mul_lt_of_lt_of_le_one'
- \+ *lemma* mul_lt_of_lt_one_of_lt'
- \+ *lemma* mul_lt_of_lt_of_lt_one'
- \+ *lemma* mul_eq_one_iff'
- \+ *lemma* monotone.mul'
- \+ *lemma* monotone.mul_const'
- \+ *lemma* monotone.const_mul'
- \+/\- *lemma* bit0_pos
- \+ *lemma* mul_le_mul_left''
- \+ *lemma* le_of_mul_le_mul_left'
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* lt_of_mul_lt_mul_left''
- \+ *lemma* mul_le_mul_right''
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* mul_le_mul''
- \+ *lemma* le_mul_of_one_le_right
- \+ *lemma* le_mul_of_one_le_left
- \+ *lemma* mul_lt_mul'''
- \+ *lemma* mul_lt_mul_of_le_of_lt
- \+ *lemma* mul_lt_mul_of_lt_of_le
- \+ *lemma* lt_mul_of_one_lt_right
- \+ *lemma* lt_mul_of_one_lt_left
- \+ *lemma* le_of_mul_le_mul_right'
- \+ *lemma* lt_of_mul_lt_mul_right''
- \+ *lemma* one_le_mul
- \+ *lemma* mul_one_lt
- \+ *lemma* mul_one_lt_of_one_lt_of_one_le
- \+ *lemma* mul_one_lt_of_one_le_of_one_lt
- \+ *lemma* mul_le_one''
- \+ *lemma* mul_lt_one
- \+ *lemma* mul_lt_one_of_lt_one_of_le_one
- \+ *lemma* mul_lt_one_of_le_one_of_lt_one
- \+ *lemma* mul_eq_one_iff_eq_one_and_eq_one_of_one_le_of_one_le
- \+ *lemma* le_mul_of_one_le_of_le
- \+ *lemma* le_mul_of_le_of_one_le
- \+ *lemma* lt_mul_of_one_lt_of_le
- \+ *lemma* lt_mul_of_le_of_one_lt
- \+ *lemma* mul_le_of_le_one_of_le
- \+ *lemma* mul_le_of_le_of_le_one
- \+ *lemma* mul_lt_of_lt_one_of_le
- \+ *lemma* mul_lt_of_le_of_lt_one
- \+ *lemma* lt_mul_of_one_le_of_lt
- \+ *lemma* lt_mul_of_lt_of_one_le
- \+ *lemma* lt_mul_of_one_lt_of_lt
- \+ *lemma* lt_mul_of_lt_of_one_lt
- \+ *lemma* mul_lt_of_le_one_of_lt
- \+ *lemma* mul_lt_of_lt_of_le_one
- \+ *lemma* mul_lt_of_lt_one_of_lt
- \+ *lemma* mul_lt_of_lt_of_lt_one
- \+ *lemma* mul_le_mul_iff_left
- \+ *lemma* mul_le_mul_iff_right
- \+ *lemma* mul_lt_mul_iff_left
- \+ *lemma* mul_lt_mul_iff_right
- \+ *lemma* le_mul_iff_one_le_right'
- \+ *lemma* le_mul_iff_one_le_left'
- \+ *lemma* lt_mul_iff_one_lt_right'
- \+ *lemma* lt_mul_iff_one_lt_left'
- \+ *lemma* mul_le_iff_le_one_left'
- \+ *lemma* mul_le_iff_le_one_right'
- \+ *lemma* mul_lt_iff_lt_one_right'
- \+ *lemma* mul_lt_iff_lt_one_left'
- \+ *lemma* mul_eq_one_iff_eq_one_of_one_le
- \+ *lemma* monotone.mul_strict_mono'
- \+ *lemma* strict_mono.mul_monotone'
- \+ *lemma* strict_mono.mul_const'
- \+ *lemma* strict_mono.const_mul'
- \+ *lemma* ordered_comm_group.mul_lt_mul_left'
- \+ *lemma* ordered_comm_group.le_of_mul_le_mul_left
- \+ *lemma* ordered_comm_group.lt_of_mul_lt_mul_left
- \+ *lemma* inv_le_inv'
- \+ *lemma* le_of_inv_le_inv
- \+ *lemma* one_le_of_inv_le_one
- \+ *lemma* inv_le_one_of_one_le
- \+ *lemma* le_one_of_one_le_inv
- \+ *lemma* one_le_inv_of_le_one
- \+ *lemma* inv_lt_inv'
- \+ *lemma* lt_of_inv_lt_inv
- \+ *lemma* one_lt_of_inv_inv
- \+ *lemma* inv_inv_of_one_lt
- \+ *lemma* inv_of_one_lt_inv
- \+ *lemma* one_lt_inv_of_inv
- \+ *lemma* le_inv_of_le_inv
- \+ *lemma* inv_le_of_inv_le
- \+ *lemma* lt_inv_of_lt_inv
- \+ *lemma* inv_lt_of_inv_lt
- \+ *lemma* mul_le_of_le_inv_mul
- \+ *lemma* le_inv_mul_of_mul_le
- \+ *lemma* le_mul_of_inv_mul_le
- \+ *lemma* inv_mul_le_of_le_mul
- \+ *lemma* le_mul_of_inv_mul_le_left
- \+ *lemma* inv_mul_le_left_of_le_mul
- \+ *lemma* le_mul_of_inv_mul_le_right
- \+ *lemma* inv_mul_le_right_of_le_mul
- \+ *lemma* mul_lt_of_lt_inv_mul
- \+ *lemma* lt_inv_mul_of_mul_lt
- \+ *lemma* lt_mul_of_inv_mul_lt
- \+ *lemma* inv_mul_lt_of_lt_mul
- \+ *lemma* lt_mul_of_inv_mul_lt_left
- \+ *lemma* inv_mul_lt_left_of_lt_mul
- \+ *lemma* lt_mul_of_inv_mul_lt_right
- \+ *lemma* inv_mul_lt_right_of_lt_mul
- \+ *lemma* mul_le_mul_three
- \+ *lemma* inv_lt_one_iff_one_lt
- \+ *lemma* inv_le_inv_iff
- \+ *lemma* inv_le'
- \+ *lemma* le_inv'
- \+ *lemma* inv_le_iff_one_le_mul
- \+ *lemma* le_inv_iff_mul_le_one
- \+ *lemma* inv_le_one'
- \+ *lemma* one_le_inv'
- \+ *lemma* inv_le_self
- \+ *lemma* self_le_inv
- \+ *lemma* inv_lt_inv_iff
- \+ *lemma* inv_lt_one'
- \+ *lemma* one_lt_inv'
- \+ *lemma* inv_lt'
- \+ *lemma* lt_inv'
- \+ *lemma* le_inv_mul_iff_mul_le
- \+ *lemma* inv_mul_le_iff_le_mul
- \+ *lemma* mul_inv_le_iff_le_mul
- \+ *lemma* mul_inv_le_iff_le_mul'
- \+ *lemma* inv_mul_le_iff_le_mul'
- \+ *lemma* lt_inv_mul_iff_mul_lt
- \+ *lemma* inv_mul_lt_iff_lt_mul
- \+ *lemma* inv_mul_lt_iff_lt_mul_right
- \+/\- *lemma* dist_bdd_within_interval
- \- *lemma* add_le_add_left'
- \- *lemma* add_le_add_right'
- \- *lemma* lt_of_add_lt_add_left'
- \- *lemma* add_le_add'
- \- *lemma* le_add_of_nonneg_right'
- \- *lemma* le_add_of_nonneg_left'
- \- *lemma* lt_of_add_lt_add_right'
- \- *lemma* le_add_of_nonneg_of_le'
- \- *lemma* le_add_of_le_of_nonneg'
- \- *lemma* add_nonneg'
- \- *lemma* add_pos_of_pos_of_nonneg'
- \- *lemma* add_pos'
- \- *lemma* add_pos_of_nonneg_of_pos'
- \- *lemma* add_nonpos'
- \- *lemma* add_le_of_nonpos_of_le'
- \- *lemma* add_le_of_le_of_nonpos'
- \- *lemma* add_neg_of_neg_of_nonpos'
- \- *lemma* add_neg_of_nonpos_of_neg'
- \- *lemma* add_neg'
- \- *lemma* lt_add_of_nonneg_of_lt'
- \- *lemma* lt_add_of_lt_of_nonneg'
- \- *lemma* lt_add_of_pos_of_lt'
- \- *lemma* lt_add_of_lt_of_pos'
- \- *lemma* add_lt_of_nonpos_of_lt'
- \- *lemma* add_lt_of_lt_of_nonpos'
- \- *lemma* add_lt_of_neg_of_lt'
- \- *lemma* add_lt_of_lt_of_neg'
- \- *lemma* add_eq_zero_iff'
- \- *lemma* monotone.add
- \- *lemma* monotone.add_const
- \- *lemma* monotone.const_add
- \- *lemma* add_le_add_left
- \- *lemma* le_of_add_le_add_left
- \- *lemma* add_lt_add_left
- \- *lemma* lt_of_add_lt_add_left
- \- *lemma* add_le_add_right
- \- *lemma* add_le_add
- \- *lemma* le_add_of_nonneg_right
- \- *lemma* le_add_of_nonneg_left
- \- *lemma* add_lt_add
- \- *lemma* add_lt_add_of_le_of_lt
- \- *lemma* add_lt_add_of_lt_of_le
- \- *lemma* lt_add_of_pos_right
- \- *lemma* lt_add_of_pos_left
- \- *lemma* le_of_add_le_add_right
- \- *lemma* lt_of_add_lt_add_right
- \- *lemma* add_nonneg
- \- *lemma* add_pos
- \- *lemma* add_pos_of_pos_of_nonneg
- \- *lemma* add_pos_of_nonneg_of_pos
- \- *lemma* add_nonpos
- \- *lemma* add_neg
- \- *lemma* add_neg_of_neg_of_nonpos
- \- *lemma* add_neg_of_nonpos_of_neg
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
- \- *lemma* le_add_of_nonneg_of_le
- \- *lemma* le_add_of_le_of_nonneg
- \- *lemma* lt_add_of_pos_of_le
- \- *lemma* lt_add_of_le_of_pos
- \- *lemma* add_le_of_nonpos_of_le
- \- *lemma* add_le_of_le_of_nonpos
- \- *lemma* add_lt_of_neg_of_le
- \- *lemma* add_lt_of_le_of_neg
- \- *lemma* lt_add_of_nonneg_of_lt
- \- *lemma* lt_add_of_lt_of_nonneg
- \- *lemma* lt_add_of_pos_of_lt
- \- *lemma* lt_add_of_lt_of_pos
- \- *lemma* add_lt_of_nonpos_of_lt
- \- *lemma* add_lt_of_lt_of_nonpos
- \- *lemma* add_lt_of_neg_of_lt
- \- *lemma* add_lt_of_lt_of_neg
- \- *lemma* add_le_add_iff_left
- \- *lemma* add_le_add_iff_right
- \- *lemma* add_lt_add_iff_left
- \- *lemma* add_lt_add_iff_right
- \- *lemma* le_add_iff_nonneg_right
- \- *lemma* le_add_iff_nonneg_left
- \- *lemma* lt_add_iff_pos_right
- \- *lemma* lt_add_iff_pos_left
- \- *lemma* add_le_iff_nonpos_left
- \- *lemma* add_le_iff_nonpos_right
- \- *lemma* add_lt_iff_neg_right
- \- *lemma* add_lt_iff_neg_left
- \- *lemma* add_eq_zero_iff_eq_zero_of_nonneg
- \- *lemma* monotone.add_strict_mono
- \- *lemma* strict_mono.add_monotone
- \- *lemma* strict_mono.add_const
- \- *lemma* strict_mono.const_add
- \- *lemma* ordered_add_comm_group.add_lt_add_left
- \- *lemma* ordered_add_comm_group.le_of_add_le_add_left
- \- *lemma* ordered_add_comm_group.lt_of_add_lt_add_left
- \- *lemma* neg_le_neg
- \- *lemma* le_of_neg_le_neg
- \- *lemma* nonneg_of_neg_nonpos
- \- *lemma* neg_nonpos_of_nonneg
- \- *lemma* nonpos_of_neg_nonneg
- \- *lemma* neg_nonneg_of_nonpos
- \- *lemma* neg_lt_neg
- \- *lemma* lt_of_neg_lt_neg
- \- *lemma* pos_of_neg_neg
- \- *lemma* neg_neg_of_pos
- \- *lemma* neg_of_neg_pos
- \- *lemma* neg_pos_of_neg
- \- *lemma* le_neg_of_le_neg
- \- *lemma* neg_le_of_neg_le
- \- *lemma* lt_neg_of_lt_neg
- \- *lemma* neg_lt_of_neg_lt
- \- *lemma* add_le_of_le_neg_add
- \- *lemma* le_neg_add_of_add_le
- \- *lemma* le_add_of_neg_add_le
- \- *lemma* neg_add_le_of_le_add
- \- *lemma* le_add_of_neg_add_le_left
- \- *lemma* neg_add_le_left_of_le_add
- \- *lemma* le_add_of_neg_add_le_right
- \- *lemma* neg_add_le_right_of_le_add
- \- *lemma* add_lt_of_lt_neg_add
- \- *lemma* lt_neg_add_of_add_lt
- \- *lemma* lt_add_of_neg_add_lt
- \- *lemma* neg_add_lt_of_lt_add
- \- *lemma* lt_add_of_neg_add_lt_left
- \- *lemma* neg_add_lt_left_of_lt_add
- \- *lemma* lt_add_of_neg_add_lt_right
- \- *lemma* neg_add_lt_right_of_lt_add
- \- *lemma* add_le_add_three
- \- *lemma* neg_neg_iff_pos
- \- *lemma* neg_le_neg_iff
- \- *lemma* neg_le
- \- *lemma* le_neg
- \- *lemma* neg_le_iff_add_nonneg
- \- *lemma* le_neg_iff_add_nonpos
- \- *lemma* neg_nonpos
- \- *lemma* neg_nonneg
- \- *lemma* neg_le_self
- \- *lemma* self_le_neg
- \- *lemma* neg_lt_neg_iff
- \- *lemma* neg_lt_zero
- \- *lemma* neg_pos
- \- *lemma* neg_lt
- \- *lemma* lt_neg
- \- *lemma* le_neg_add_iff_add_le
- \- *lemma* neg_add_le_iff_le_add
- \- *lemma* add_neg_le_iff_le_add
- \- *lemma* add_neg_le_iff_le_add'
- \- *lemma* neg_add_le_iff_le_add'
- \- *lemma* lt_neg_add_iff_add_lt
- \- *lemma* neg_add_lt_iff_lt_add
- \- *lemma* neg_add_lt_iff_lt_add_right
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* coe_lt_coe
- \- *theorem* add_lt_add_right
- \+ *def* ordered_comm_group.mk'
- \- *def* ordered_add_comm_group.mk'



## [2020-06-09 17:00:44](https://github.com/leanprover-community/mathlib/commit/f098c16)
feat(ring_theory/localization): more lemmas and defs about fields of fractions ([#3005](https://github.com/leanprover-community/mathlib/pull/3005))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+/\- *lemma* mem_non_zero_divisors_iff_ne_zero
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* mk'_eq_div
- \+ *lemma* is_unit_map_of_injective
- \+ *lemma* lift_mk'
- \+ *lemma* mk_eq_div
- \+ *def* fraction_ring
- \+ *def* of



## [2020-06-09 12:21:46](https://github.com/leanprover-community/mathlib/commit/ccdf1d2)
feat(category_theory/limits): prod.lift_comp_comp ([#2968](https://github.com/leanprover-community/mathlib/pull/2968))
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.lift_comp_comp
- \+ *lemma* coprod.desc_comp_comp



## [2020-06-09 11:36:39](https://github.com/leanprover-community/mathlib/commit/7cb0a85)
refactor(topology): rename `lim` to `Lim` ([#2977](https://github.com/leanprover-community/mathlib/pull/2977))
Also introduce `lim (f : filter α) (g : α → β)`.
#### Estimated changes
Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/topology/basic.lean
- \+ *lemma* Lim_spec
- \+/\- *lemma* lim_spec

Modified src/topology/dense_embedding.lean
- \+/\- *lemma* extend_eq

Modified src/topology/separation.lean
- \+ *lemma* Lim_eq
- \+ *lemma* filter.tendsto.lim_eq
- \+ *lemma* continuous.lim_eq
- \+ *lemma* Lim_nhds
- \+ *lemma* lim_nhds_id
- \+ *lemma* Lim_nhds_within
- \+ *lemma* lim_nhds_within_id
- \- *lemma* lim_eq
- \- *lemma* lim_nhds_eq
- \- *lemma* lim_nhds_eq_of_closure

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
- \+ *lemma* fst_vadd
- \+ *lemma* snd_vadd
- \+ *lemma* mk_vadd_mk
- \+ *lemma* fst_vsub
- \+ *lemma* snd_vsub
- \+ *lemma* mk_vsub_mk



## [2020-06-09 09:07:38](https://github.com/leanprover-community/mathlib/commit/4281343)
refactor(data/polynomial): redefine `C` as an `alg_hom` ([#3003](https://github.com/leanprover-community/mathlib/pull/3003))
As a side effect Lean parses `C 1` as `polynomial nat`. If you need `polynomial R`, then use `C (1:R)`.
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/data/polynomial.lean
- \+ *lemma* C_def
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \+/\- *lemma* C_mul
- \+/\- *lemma* C_add
- \+/\- *lemma* C_pow
- \+/\- *lemma* nat_cast_eq_C
- \+/\- *lemma* int_cast_eq_C
- \+/\- *lemma* C_neg
- \+/\- *lemma* C_sub
- \+/\- *def* C
- \+/\- *def* lcoeff

Modified src/field_theory/minimal_polynomial.lean




## [2020-06-09 08:13:56](https://github.com/leanprover-community/mathlib/commit/34302c6)
chore(ring_theory/algebra): add comments explaining absence of 2 `simp` attrs ([#3002](https://github.com/leanprover-community/mathlib/pull/3002))
#### Estimated changes
Modified src/ring_theory/algebra.lean




## [2020-06-09 08:13:54](https://github.com/leanprover-community/mathlib/commit/03c345f)
chore(data/real/nnreal): +2 lemmas ([#3000](https://github.com/leanprover-community/mathlib/pull/3000))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* sum_div
- \+ *lemma* div_le_iff



## [2020-06-09 08:13:52](https://github.com/leanprover-community/mathlib/commit/1091462)
feat(analysis/special_functions/pow): `inv_rpow`, `div_rpow` ([#2999](https://github.com/leanprover-community/mathlib/pull/2999))
Also use notation `ℝ≥0` and use `nnreal.eq` instead of `rw ← nnreal.coe_eq`.
#### Estimated changes
Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* log_inv

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* inv_rpow
- \+ *lemma* div_rpow
- \+/\- *lemma* one_le_rpow
- \+/\- *lemma* rpow_eq_pow
- \+/\- *lemma* coe_rpow
- \+/\- *lemma* rpow_zero
- \+/\- *lemma* rpow_eq_zero_iff
- \+/\- *lemma* zero_rpow
- \+/\- *lemma* rpow_one
- \+/\- *lemma* one_rpow
- \+/\- *lemma* rpow_add
- \+ *lemma* rpow_add'
- \+/\- *lemma* rpow_mul
- \+/\- *lemma* rpow_neg
- \+/\- *lemma* rpow_nat_cast
- \+/\- *lemma* mul_rpow
- \+/\- *lemma* rpow_le_rpow
- \+/\- *lemma* rpow_lt_rpow
- \+/\- *lemma* rpow_lt_rpow_of_exponent_lt
- \+/\- *lemma* rpow_le_rpow_of_exponent_le
- \+/\- *lemma* rpow_lt_rpow_of_exponent_gt
- \+/\- *lemma* rpow_le_rpow_of_exponent_ge
- \+/\- *lemma* rpow_le_one
- \+/\- *lemma* one_lt_rpow
- \+/\- *lemma* rpow_lt_one
- \+/\- *lemma* pow_nat_rpow_nat_inv
- \+/\- *lemma* rpow_nat_inv_pow_nat
- \+/\- *lemma* continuous_at_rpow
- \+/\- *lemma* filter.tendsto.nnrpow
- \+/\- *lemma* coe_rpow_of_ne_zero
- \+/\- *lemma* coe_rpow_of_nonneg
- \+/\- *lemma* coe_mul_rpow



## [2020-06-09 07:06:53](https://github.com/leanprover-community/mathlib/commit/45567dc)
chore(algebra/big_operators): add `@[simp] lemma sum_eq_zero_iff` ([#2998](https://github.com/leanprover-community/mathlib/pull/2998))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_eq_zero_iff



## [2020-06-09 05:24:03](https://github.com/leanprover-community/mathlib/commit/24ce416)
chore(data/matrix/basic): clean up of new lemmas on matrix numerals ([#2996](https://github.com/leanprover-community/mathlib/pull/2996))
Generalise and improve use of `@[simp]` for some newly added lemmas about matrix numerals.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* bit0_val
- \+ *lemma* bit1_val
- \+ *lemma* bit1_val_eq
- \+ *lemma* bit1_val_ne
- \- *lemma* bit0_apply_apply
- \- *lemma* bit1_apply_apply



## [2020-06-08 20:32:11](https://github.com/leanprover-community/mathlib/commit/7bb2d89)
feat(dynamics/fixed_points/topology): new file ([#2991](https://github.com/leanprover-community/mathlib/pull/2991))
* Move `is_fixed_pt_of_tendsto_iterate` from
  `topology.metric_space.contracting`, reformulate it without `∃`.
* Add `is_closed_fixed_points`.
* Move `dynamics.fixed_points` to `dynamics.fixed_points.basic`.
#### Estimated changes
Modified src/dynamics/circle/rotation_number/translation_number.lean


Renamed src/dynamics/fixed_points.lean to src/dynamics/fixed_points/basic.lean


Created src/dynamics/fixed_points/topology.lean
- \+ *lemma* is_fixed_pt_of_tendsto_iterate
- \+ *lemma* is_closed_fixed_points

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
Created src/data/real/conjugate_exponents.lean
- \+ *lemma* is_conjugate_exponent_iff
- \+ *lemma* is_conjugate_exponent_conjugate_exponent
- \+ *lemma* pos
- \+ *lemma* ne_zero
- \+ *lemma* sub_one_ne_zero
- \+ *lemma* one_div_pos
- \+ *lemma* one_div_ne_zero
- \+ *lemma* conj_eq
- \+ *def* conjugate_exponent



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
- \+/\- *lemma* prod_Ico_one_prime

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
- \+ *lemma* inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \+ *lemma* inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \+ *lemma* inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square
- \+ *lemma* abs_inner_div_norm_mul_norm_le_one
- \+ *lemma* inner_smul_self_left
- \+ *lemma* inner_smul_self_right
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \+ *lemma* inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* inner_div_norm_mul_norm_eq_neg_one_iff

Modified src/geometry/euclidean.lean
- \+ *lemma* cos_angle
- \+ *lemma* angle_comm
- \+ *lemma* angle_neg_neg
- \+ *lemma* angle_nonneg
- \+ *lemma* angle_le_pi
- \+ *lemma* angle_neg_right
- \+ *lemma* angle_neg_left
- \+ *lemma* angle_zero_left
- \+ *lemma* angle_zero_right
- \+ *lemma* angle_self
- \+ *lemma* angle_self_neg_of_nonzero
- \+ *lemma* angle_neg_self_of_nonzero
- \+ *lemma* angle_smul_right_of_pos
- \+ *lemma* angle_smul_left_of_pos
- \+ *lemma* angle_smul_right_of_neg
- \+ *lemma* angle_smul_left_of_neg
- \+ *lemma* cos_angle_mul_norm_mul_norm
- \+ *lemma* sin_angle_mul_norm_mul_norm
- \+ *lemma* angle_eq_zero_iff
- \+ *lemma* angle_eq_pi_iff
- \+ *lemma* angle_add_angle_eq_pi_of_angle_eq_pi
- \+ *lemma* inner_eq_zero_iff_angle_eq_pi_div_two
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square'
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square'
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
- \+ *lemma* angle_sub_eq_angle_sub_rev_of_norm_eq
- \+ *lemma* norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
- \+ *lemma* angle_eq_left
- \+ *lemma* angle_eq_right
- \+ *lemma* angle_eq_of_ne
- \+ *lemma* angle_eq_zero_of_angle_eq_pi_left
- \+ *lemma* angle_eq_zero_of_angle_eq_pi_right
- \+ *lemma* angle_eq_angle_of_angle_eq_pi
- \+ *lemma* dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two
- \+ *lemma* dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
- \+ *lemma* angle_eq_angle_of_dist_eq
- \+ *lemma* dist_eq_of_angle_eq_angle_of_angle_ne_pi
- \+ *def* angle



## [2020-06-08 19:05:30](https://github.com/leanprover-community/mathlib/commit/dbbd696)
feat(order/ideal): order ideals, cofinal sets and the Rasiowa-Sikorski lemma ([#2850](https://github.com/leanprover-community/mathlib/pull/2850))
We define order ideals and cofinal sets, and use them to prove the (very simple) Rasiowa-Sikorski lemma: given a countable family of cofinal subsets of an inhabited preorder, there is an upwards directed set meeting each one. This provides an API for certain recursive constructions.
#### Estimated changes
Created src/order/ideal.lean
- \+ *lemma* above_mem
- \+ *lemma* le_above
- \+ *lemma* sequence_of_cofinals.monotone
- \+ *lemma* sequence_of_cofinals.encode_mem
- \+ *lemma* mem_ideal_of_cofinals
- \+ *lemma* cofinal_meets_ideal_of_cofinals
- \+ *def* principal
- \+ *def* ideal_of_cofinals



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
- \- *lemma* centralizer.inter_units_is_subgroup
- \- *lemma* group.centralizer_closure
- \- *lemma* add_monoid.centralizer_closure
- \- *lemma* ring.centralizer_closure
- \- *theorem* mul_right
- \- *theorem* mul_left
- \- *theorem* one_right
- \- *theorem* one_left
- \- *theorem* units_inv_right
- \- *theorem* units_inv_right_iff
- \- *theorem* units_inv_left
- \- *theorem* units_inv_left_iff
- \- *theorem* pow_right
- \- *theorem* pow_left
- \- *theorem* pow_pow
- \- *theorem* self_pow
- \- *theorem* pow_self
- \- *theorem* pow_pow_self
- \- *theorem* units_coe
- \- *theorem* units_of_coe
- \- *theorem* units_coe_iff
- \- *theorem* inv_right
- \- *theorem* inv_right_iff
- \- *theorem* inv_left
- \- *theorem* inv_left_iff
- \- *theorem* inv_inv
- \- *theorem* inv_inv_iff
- \- *theorem* gpow_right
- \- *theorem* gpow_left
- \- *theorem* gpow_gpow
- \- *theorem* self_gpow
- \- *theorem* gpow_self
- \- *theorem* gpow_gpow_self
- \- *theorem* zero_right
- \- *theorem* zero_left
- \- *theorem* add_right
- \- *theorem* add_left
- \- *theorem* nsmul_right
- \- *theorem* nsmul_left
- \- *theorem* nsmul_nsmul
- \- *theorem* self_nsmul
- \- *theorem* nsmul_self
- \- *theorem* self_nsmul_nsmul
- \- *theorem* cast_nat_right
- \- *theorem* cast_nat_left
- \- *theorem* neg_right
- \- *theorem* neg_right_iff
- \- *theorem* neg_left
- \- *theorem* neg_left_iff
- \- *theorem* neg_one_right
- \- *theorem* neg_one_left
- \- *theorem* sub_right
- \- *theorem* sub_left
- \- *theorem* gsmul_right
- \- *theorem* gsmul_left
- \- *theorem* gsmul_gsmul
- \- *theorem* self_gsmul
- \- *theorem* gsmul_self
- \- *theorem* self_gsmul_gsmul
- \- *theorem* cast_int_right
- \- *theorem* cast_int_left
- \- *theorem* finv_left_iff
- \- *theorem* finv_left
- \- *theorem* finv_right_iff
- \- *theorem* finv_right
- \- *theorem* finv_finv
- \- *theorem* div_right
- \- *theorem* div_left
- \- *theorem* mem_centralizer
- \- *theorem* monoid.centralizer_closure
- \- *theorem* commute.list_prod_right
- \- *theorem* commute.list_prod_left
- \- *theorem* neg_pow
- \- *def* commute
- \- *def* centralizer
- \- *def* submonoid.centralizer
- \- *def* submonoid.set.centralizer
- \- *def* centralizer.add_submonoid
- \- *def* set.centralizer.add_submonoid

Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \- *theorem* inv_comm_of_comm

Created src/algebra/group/commute.lean
- \+ *theorem* mul_right
- \+ *theorem* mul_left
- \+ *theorem* one_right
- \+ *theorem* one_left
- \+ *theorem* units_inv_right
- \+ *theorem* units_inv_right_iff
- \+ *theorem* units_inv_left
- \+ *theorem* units_inv_left_iff
- \+ *theorem* units_coe
- \+ *theorem* units_of_coe
- \+ *theorem* units_coe_iff
- \+ *theorem* inv_right
- \+ *theorem* inv_right_iff
- \+ *theorem* inv_left
- \+ *theorem* inv_left_iff
- \+ *theorem* inv_inv
- \+ *theorem* inv_inv_iff
- \+ *def* commute

Modified src/algebra/group/hom.lean


Created src/algebra/group/semiconj.lean
- \+ *lemma* mul_right
- \+ *lemma* mul_left
- \+ *lemma* one_right
- \+ *lemma* one_left
- \+ *lemma* units_inv_right
- \+ *lemma* units_inv_right_iff
- \+ *lemma* units_inv_symm_left
- \+ *lemma* units_inv_symm_left_iff
- \+ *lemma* inv_right_iff
- \+ *lemma* inv_right
- \+ *lemma* inv_symm_left_iff
- \+ *lemma* inv_symm_left
- \+ *lemma* inv_inv_symm
- \+ *lemma* inv_inv_symm_iff
- \+ *lemma* conj_mk
- \+ *lemma* units.mk_semiconj_by
- \+ *theorem* units_coe
- \+ *theorem* units_of_coe
- \+ *theorem* units_coe_iff
- \+ *def* semiconj_by

Modified src/algebra/group_power.lean
- \+ *lemma* pow_right
- \+ *lemma* nsmul_right
- \+ *lemma* nsmul_left
- \+ *lemma* nsmul_nsmul
- \+ *lemma* commute.mul_pow
- \+ *lemma* units_gpow_right
- \+ *lemma* gpow_right
- \+ *lemma* gsmul_right
- \+ *lemma* gsmul_left
- \+ *lemma* gsmul_gsmul
- \+ *lemma* units_gpow_left
- \+ *lemma* gpow_left
- \+ *lemma* gpow_gpow
- \+ *lemma* conj_pow
- \+ *lemma* conj_pow'
- \+ *theorem* pow_right
- \+ *theorem* pow_left
- \+ *theorem* pow_pow
- \+ *theorem* self_pow
- \+ *theorem* pow_self
- \+ *theorem* pow_pow_self
- \+ *theorem* nsmul_right
- \+ *theorem* nsmul_left
- \+ *theorem* nsmul_nsmul
- \+ *theorem* self_nsmul
- \+ *theorem* nsmul_self
- \+ *theorem* self_nsmul_nsmul
- \+/\- *theorem* pow_mul_comm'
- \+ *theorem* neg_pow
- \+/\- *theorem* gpow_one
- \+ *theorem* commute.mul_gpow
- \+/\- *theorem* mul_gpow
- \+ *theorem* self_gpow
- \+ *theorem* gpow_self
- \+ *theorem* gpow_gpow_self
- \+ *theorem* self_gsmul
- \+ *theorem* gsmul_self
- \+ *theorem* self_gsmul_gsmul

Modified src/algebra/group_with_zero.lean
- \+ *lemma* inv_symm_left_iff'
- \+ *lemma* inv_symm_left'
- \+ *lemma* inv_right'
- \+ *lemma* inv_right_iff'
- \+ *lemma* div_right
- \+ *theorem* inv_left_iff'
- \+ *theorem* inv_left'
- \+ *theorem* inv_right_iff'
- \+ *theorem* inv_right'
- \+ *theorem* inv_inv'
- \+ *theorem* div_right
- \+ *theorem* div_left
- \- *theorem* inv_comm_of_comm'

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* commute.mul_fpow
- \+/\- *lemma* mul_fpow
- \+ *theorem* semiconj_by.fpow_right
- \+ *theorem* commute.fpow_right
- \+ *theorem* commute.fpow_left
- \+ *theorem* commute.fpow_fpow
- \+ *theorem* commute.fpow_self
- \+ *theorem* commute.self_fpow
- \+ *theorem* commute.fpow_fpow_self
- \- *theorem* fpow_mul_comm

Modified src/algebra/ring.lean
- \+ *lemma* add_right
- \+ *lemma* add_left
- \+ *lemma* zero_right
- \+ *lemma* zero_left
- \+ *lemma* neg_right
- \+ *lemma* neg_right_iff
- \+ *lemma* neg_left
- \+ *lemma* neg_left_iff
- \+ *lemma* neg_one_right
- \+ *lemma* neg_one_left
- \+ *lemma* sub_right
- \+ *lemma* sub_left
- \+ *theorem* add_right
- \+ *theorem* add_left
- \+ *theorem* zero_right
- \+ *theorem* zero_left
- \+ *theorem* neg_right
- \+ *theorem* neg_right_iff
- \+ *theorem* neg_left
- \+ *theorem* neg_left_iff
- \+ *theorem* neg_one_right
- \+ *theorem* neg_one_left
- \+ *theorem* sub_right
- \+ *theorem* sub_left

Deleted src/algebra/semiconj.lean
- \- *lemma* mul_right
- \- *lemma* mul_left
- \- *lemma* one_right
- \- *lemma* one_left
- \- *lemma* units_inv_right
- \- *lemma* units_inv_right_iff
- \- *lemma* units_inv_symm_left
- \- *lemma* units_inv_symm_left_iff
- \- *lemma* pow_right
- \- *lemma* units_gpow_right
- \- *lemma* inv_right_iff
- \- *lemma* inv_right
- \- *lemma* inv_symm_left_iff
- \- *lemma* inv_symm_left
- \- *lemma* inv_inv_symm
- \- *lemma* inv_inv_symm_iff
- \- *lemma* conj_mk
- \- *lemma* gpow_right
- \- *lemma* add_right
- \- *lemma* add_left
- \- *lemma* zero_right
- \- *lemma* zero_left
- \- *lemma* nsmul_right
- \- *lemma* nsmul_left
- \- *lemma* nsmul_nsmul
- \- *lemma* cast_nat_right
- \- *lemma* cast_nat_left
- \- *lemma* neg_right
- \- *lemma* neg_right_iff
- \- *lemma* neg_left
- \- *lemma* neg_left_iff
- \- *lemma* neg_one_right
- \- *lemma* neg_one_left
- \- *lemma* sub_right
- \- *lemma* sub_left
- \- *lemma* gsmul_right
- \- *lemma* gsmul_left
- \- *lemma* gsmul_gsmul
- \- *lemma* finv_symm_left_iff
- \- *lemma* finv_symm_left
- \- *lemma* mk_semiconj_by
- \- *lemma* conj_pow
- \- *lemma* conj_pow'
- \- *theorem* units_coe
- \- *theorem* units_of_coe
- \- *theorem* units_coe_iff
- \- *def* semiconj_by

Modified src/data/int/basic.lean
- \+ *lemma* cast_commute
- \+ *lemma* commute_cast
- \- *theorem* mul_cast_comm

Modified src/data/nat/cast.lean
- \+/\- *lemma* coe_cast_ring_hom
- \+ *lemma* cast_commute
- \+ *lemma* commute_cast
- \- *theorem* mul_cast_comm

Modified src/data/nat/choose.lean


Modified src/data/rat/cast.lean
- \+ *theorem* cast_commute
- \+ *theorem* commute_cast
- \- *theorem* mul_cast_comm

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
- \+ *lemma* bit0_apply_apply
- \+ *lemma* bit1_apply_apply



## [2020-06-08 15:06:15](https://github.com/leanprover-community/mathlib/commit/3ca4c27)
chore(algebra/ordered_ring): use le instead of ge ([#2986](https://github.com/leanprover-community/mathlib/pull/2986))
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* mul_nonpos_of_nonneg_of_nonpos
- \+/\- *lemma* mul_nonpos_of_nonpos_of_nonneg
- \+/\- *lemma* mul_lt_mul'
- \+/\- *lemma* mul_neg_of_pos_of_neg
- \+/\- *lemma* mul_neg_of_neg_of_pos
- \+/\- *lemma* one_lt_two
- \+ *lemma* one_le_two
- \+/\- *lemma* lt_of_mul_lt_mul_left
- \+/\- *lemma* lt_of_mul_lt_mul_right
- \+/\- *lemma* le_of_mul_le_mul_left
- \+/\- *lemma* le_of_mul_le_mul_right
- \+ *lemma* neg_one_lt_zero
- \+ *lemma* le_of_mul_le_of_one_le
- \+/\- *lemma* nonneg_le_nonneg_of_squares_le
- \- *lemma* two_gt_one
- \- *lemma* two_ge_one
- \- *lemma* zero_gt_neg_one
- \- *lemma* le_of_mul_le_of_ge_one



## [2020-06-08 15:06:12](https://github.com/leanprover-community/mathlib/commit/47f7335)
feat(data/nat/digits): digits, and divisibility tests for Freek 85 ([#2686](https://github.com/leanprover-community/mathlib/pull/2686))
I couldn't quite believe how much low hanging fruit there is on Lean's attempt at Freek's list, and so took a moment to do surely the lowest of the low...
This provides `digits b n`, which extracts the digits of a natural number `n` with respect to a base `b`, and `of_digits b L`, which reconstitutes a number from its digits, proves a few simple facts about these functions, and proves the usual divisibility by 3, 9, and 11 tests.
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* dvd_mul_sub_mul
- \+ *lemma* dvd_iff_dvd_of_dvd_sub

Modified src/data/fintype/card.lean
- \+ *lemma* alternating_sum_eq_finset_sum
- \+ *lemma* alternating_prod_eq_finset_prod

Modified src/data/int/basic.lean
- \+/\- *theorem* nat_cast_eq_coe_nat

Modified src/data/list/basic.lean
- \+ *lemma* alternating_prod_nil
- \+ *lemma* alternating_prod_singleton
- \+ *lemma* alternating_prod_cons_cons
- \+ *lemma* alternating_sum_cons_cons

Modified src/data/list/defs.lean
- \+ *def* alternating_sum
- \+ *def* alternating_prod

Modified src/data/nat/basic.lean
- \+ *lemma* div_lt_self'

Created src/data/nat/digits.lean
- \+ *lemma* digits_aux_zero
- \+ *lemma* digits_aux_def
- \+ *lemma* digits_zero
- \+ *lemma* digits_one_succ
- \+ *lemma* digits_add_two_add_one
- \+ *lemma* digits_of_lt
- \+ *lemma* digits_add
- \+ *lemma* of_digits_eq_foldr
- \+ *lemma* of_digits_one_cons
- \+ *lemma* coe_of_digits
- \+ *lemma* coe_int_of_digits
- \+ *lemma* digits_zero_of_eq_zero
- \+ *lemma* digits_of_digits
- \+ *lemma* of_digits_digits
- \+ *lemma* of_digits_one
- \+ *lemma* dvd_of_digits_sub_of_digits
- \+ *lemma* of_digits_modeq'
- \+ *lemma* of_digits_modeq
- \+ *lemma* of_digits_mod
- \+ *lemma* of_digits_zmodeq'
- \+ *lemma* of_digits_zmodeq
- \+ *lemma* of_digits_zmod
- \+ *lemma* modeq_digits_sum
- \+ *lemma* modeq_three_digits_sum
- \+ *lemma* modeq_nine_digits_sum
- \+ *lemma* dvd_iff_dvd_digits_sum
- \+ *lemma* three_dvd_iff
- \+ *lemma* nine_dvd_iff
- \+ *lemma* zmodeq_of_digits_digits
- \+ *lemma* of_digits_neg_one
- \+ *lemma* modeq_eleven_digits_sum
- \+ *lemma* dvd_iff_dvd_of_digits
- \+ *lemma* eleven_dvd_iff
- \+ *def* digits_aux_0
- \+ *def* digits_aux_1
- \+ *def* digits_aux
- \+ *def* digits
- \+ *def* of_digits



## [2020-06-08 13:54:41](https://github.com/leanprover-community/mathlib/commit/a793042)
feat(ring_theory/fractional_ideal): pushforward of fractional ideals ([#2984](https://github.com/leanprover-community/mathlib/pull/2984))
Extend `submodule.map` to fractional ideals by showing that the pushforward is also fractional.
For this, we need a slightly tweaked definition of fractional ideal: if we localize `R` at the submonoid `S`, the old definition required a nonzero `x : R` such that `xI ≤ R`, and the new definition requires `x ∈ S` instead. In the most common case, `S = non_zero_divisors R`, the results are exactly the same, and all operations are still the same.
A practical use of these pushforwards is included: `canonical_equiv` states fractional ideals don't depend on choice of localization map.
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+ *lemma* to_fun_eq_coe_fun
- \+ *lemma* refl_apply
- \+ *lemma* coe_add_equiv_refl
- \+ *lemma* coe_mul_equiv_refl
- \+ *lemma* to_ring_hom_refl
- \+ *lemma* to_monoid_hom_refl
- \+ *lemma* to_add_monoid_hom_refl
- \- *lemma* to_fun_eq_coe

Modified src/group_theory/submonoid.lean
- \+ *lemma* map_id

Modified src/ring_theory/algebra.lean
- \+ *lemma* coe_refl
- \+ *lemma* comp_symm
- \+ *lemma* symm_comp

Modified src/ring_theory/algebra_operations.lean
- \+ *lemma* map_mul

Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* val_eq_coe
- \+/\- *lemma* ext
- \+ *lemma* coe_coe_ideal
- \+ *lemma* coe_zero
- \+ *lemma* coe_ne_bot_iff_nonzero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* fractional_map
- \+ *lemma* coe_map
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_add
- \+ *lemma* map_mul
- \+ *lemma* map_equiv_apply
- \+ *lemma* map_equiv_refl
- \+ *lemma* coe_inv_of_nonzero
- \+/\- *lemma* span_singleton_fractional
- \+/\- *lemma* coe_span_singleton
- \+/\- *lemma* eq_span_singleton_of_principal
- \+ *lemma* is_principal_iff
- \+/\- *lemma* span_singleton_zero
- \+ *lemma* span_singleton_eq_zero_iff
- \+/\- *lemma* span_singleton_one
- \+/\- *lemma* span_singleton_mul_span_singleton
- \+ *lemma* coe_ideal_span_singleton
- \+/\- *lemma* mem_singleton_mul
- \+ *lemma* mul_generator_self_inv
- \- *lemma* val_coe_ideal
- \- *lemma* val_zero
- \- *lemma* nonzero_iff_val_nonzero
- \- *lemma* val_one
- \- *lemma* val_add
- \- *lemma* val_mul
- \- *lemma* val_inv_of_nonzero
- \- *lemma* val_span_singleton
- \- *lemma* invertible_of_principal
- \+ *def* map
- \+ *def* map_equiv
- \+/\- *def* span_singleton



## [2020-06-08 07:55:43](https://github.com/leanprover-community/mathlib/commit/c360e01)
feat(ring/localization): add fraction map for int to rat cast ([#2921](https://github.com/leanprover-community/mathlib/pull/2921))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* mul_denom_eq_num
- \- *lemma* mul_own_denom_eq_num

Modified src/ring_theory/localization.lean
- \+ *def* int.fraction_map



## [2020-06-08 07:00:32](https://github.com/leanprover-community/mathlib/commit/592f769)
feat(dynamics/circle): define translation number of a lift of a circle homeo ([#2974](https://github.com/leanprover-community/mathlib/pull/2974))
Define a structure `circle_deg1_lift`, a function `translation_number : circle_deg1_lift → ℝ`, and prove some basic properties
#### Estimated changes
Modified src/algebra/semiconj.lean
- \+ *lemma* mk_semiconj_by
- \+ *lemma* conj_pow
- \+ *lemma* conj_pow'
- \- *lemma* units_conj_mk

Created src/dynamics/circle/rotation_number/translation_number.lean
- \+ *lemma* coe_mk
- \+ *lemma* mono
- \+ *lemma* map_add_one
- \+ *lemma* map_one_add
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* coe_one
- \+ *lemma* units_coe
- \+ *lemma* coe_pow
- \+ *lemma* semiconj_by_iff_semiconj
- \+ *lemma* commute_iff_commute
- \+ *lemma* translate_apply
- \+ *lemma* translate_inv_apply
- \+ *lemma* translate_gpow
- \+ *lemma* translate_pow
- \+ *lemma* translate_iterate
- \+ *lemma* commute_nat_add
- \+ *lemma* commute_add_nat
- \+ *lemma* commute_sub_nat
- \+ *lemma* commute_add_int
- \+ *lemma* commute_int_add
- \+ *lemma* commute_sub_int
- \+ *lemma* map_int_add
- \+ *lemma* map_add_int
- \+ *lemma* map_sub_int
- \+ *lemma* map_add_nat
- \+ *lemma* map_nat_add
- \+ *lemma* map_sub_nat
- \+ *lemma* map_int_of_map_zero
- \+ *lemma* map_fract_sub_fract_eq
- \+ *lemma* sup_apply
- \+ *lemma* inf_apply
- \+ *lemma* iterate_monotone
- \+ *lemma* iterate_mono
- \+ *lemma* pow_mono
- \+ *lemma* pow_monotone
- \+ *lemma* map_le_of_map_zero
- \+ *lemma* map_map_zero_le
- \+ *lemma* floor_map_map_zero_le
- \+ *lemma* ceil_map_map_zero_le
- \+ *lemma* map_map_zero_lt
- \+ *lemma* le_map_of_map_zero
- \+ *lemma* le_map_map_zero
- \+ *lemma* le_floor_map_map_zero
- \+ *lemma* le_ceil_map_map_zero
- \+ *lemma* lt_map_map_zero
- \+ *lemma* dist_map_map_zero_lt
- \+ *lemma* dist_map_zero_lt_of_semiconj
- \+ *lemma* dist_map_zero_lt_of_semiconj_by
- \+ *lemma* iterate_le_of_map_le_add_int
- \+ *lemma* le_iterate_of_add_int_le_map
- \+ *lemma* iterate_eq_of_map_eq_add_int
- \+ *lemma* iterate_pos_le_iff
- \+ *lemma* iterate_pos_lt_iff
- \+ *lemma* iterate_pos_eq_iff
- \+ *lemma* le_iterate_pos_iff
- \+ *lemma* lt_iterate_pos_iff
- \+ *lemma* mul_floor_map_zero_le_floor_iterate_zero
- \+ *lemma* transnum_aux_seq_def
- \+ *lemma* translation_number_eq_of_tendsto_aux
- \+ *lemma* translation_number_eq_of_tendsto₀
- \+ *lemma* translation_number_eq_of_tendsto₀'
- \+ *lemma* transnum_aux_seq_zero
- \+ *lemma* transnum_aux_seq_dist_lt
- \+ *lemma* tendsto_translation_number_aux
- \+ *lemma* dist_map_zero_translation_number_le
- \+ *lemma* tendsto_translation_number_of_dist_bounded_aux
- \+ *lemma* translation_number_eq_of_dist_bounded
- \+ *lemma* translation_number_map_id
- \+ *lemma* translation_number_eq_of_semiconj_by
- \+ *lemma* translation_number_eq_of_semiconj
- \+ *lemma* translation_number_mul_of_commute
- \+ *lemma* translation_number_pow
- \+ *lemma* translation_number_conj_eq
- \+ *lemma* translation_number_conj_eq'
- \+ *lemma* dist_pow_map_zero_mul_translation_number_le
- \+ *lemma* tendsto_translation_number₀'
- \+ *lemma* tendsto_translation_number₀
- \+ *lemma* tendsto_translation_number
- \+ *lemma* tendsto_translation_number'
- \+ *lemma* translation_number_mono
- \+ *lemma* translation_number_translate
- \+ *lemma* translation_number_le_of_le_add
- \+ *lemma* le_translation_number_of_add_le
- \+ *lemma* translation_number_le_of_le_add_int
- \+ *lemma* translation_number_le_of_le_add_nat
- \+ *lemma* le_translation_number_of_add_int_le
- \+ *lemma* le_translation_number_of_add_nat_le
- \+ *lemma* translation_number_of_eq_add_int
- \+ *lemma* floor_sub_le_translation_number
- \+ *lemma* translation_number_le_ceil_sub
- \+ *lemma* map_lt_of_translation_number_lt_int
- \+ *lemma* map_lt_of_translation_number_lt_nat
- \+ *lemma* lt_map_of_int_lt_translation_number
- \+ *lemma* lt_map_of_nat_lt_translation_number
- \+ *lemma* translation_number_of_map_pow_eq_add_int
- \+ *lemma* forall_map_sub_of_Icc
- \+ *lemma* translation_number_lt_of_forall_lt_add
- \+ *lemma* lt_translation_number_of_forall_add_lt
- \+ *lemma* exists_eq_add_translation_number
- \+ *lemma* translation_number_eq_int_iff
- \+ *lemma* continuous_pow
- \+ *lemma* translation_number_eq_rat_iff
- \+ *theorem* coe_inj
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *def* translate
- \+ *def* transnum_aux_seq
- \+ *def* translation_number



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
- \- *def* mul_add
- \- *def* add_mul
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
- \+ *lemma* hext

Modified src/category_theory/fully_faithful.lean




## [2020-06-06 20:56:40](https://github.com/leanprover-community/mathlib/commit/2a36d25)
chore(analysis/normed_space/mazur_ulam): add `to_affine_map` ([#2963](https://github.com/leanprover-community/mathlib/pull/2963))
#### Estimated changes
Modified src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* coe_to_affine_map
- \+ *def* to_affine_map

Modified src/linear_algebra/affine_space.lean
- \+ *lemma* coe_mk'
- \+ *lemma* mk'_linear
- \+ *def* mk'



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
- \+ *lemma* zero_le_padic_val_rat_of_nat
- \+ *lemma* padic_val_rat_of_nat
- \+ *lemma* padic_val_nat_def
- \+ *def* padic_val_nat



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
Created archive/examples/mersenne_primes.lean


Modified src/data/nat/parity.lean
- \+ *lemma* two_not_dvd_two_mul_add_one
- \+ *lemma* two_not_dvd_two_mul_sub_one

Created src/number_theory/lucas_lehmer.lean
- \+ *lemma* mersenne_pos
- \+ *lemma* mersenne_int_ne_zero
- \+ *lemma* s_mod_nonneg
- \+ *lemma* s_mod_mod
- \+ *lemma* s_mod_lt
- \+ *lemma* s_zmod_eq_s
- \+ *lemma* int.coe_nat_pow_pred
- \+ *lemma* int.coe_nat_two_pow_pred
- \+ *lemma* s_zmod_eq_s_mod
- \+ *lemma* residue_eq_zero_iff_s_mod_eq_zero
- \+ *lemma* ext
- \+ *lemma* add_fst
- \+ *lemma* add_snd
- \+ *lemma* neg_fst
- \+ *lemma* neg_snd
- \+ *lemma* mul_fst
- \+ *lemma* mul_snd
- \+ *lemma* one_fst
- \+ *lemma* one_snd
- \+ *lemma* bit0_fst
- \+ *lemma* bit0_snd
- \+ *lemma* bit1_fst
- \+ *lemma* bit1_snd
- \+ *lemma* left_distrib
- \+ *lemma* right_distrib
- \+ *lemma* nat_coe_fst
- \+ *lemma* nat_coe_snd
- \+ *lemma* int_coe_fst
- \+ *lemma* int_coe_snd
- \+ *lemma* coe_mul
- \+ *lemma* coe_nat
- \+ *lemma* X_card
- \+ *lemma* units_card
- \+ *lemma* ω_mul_ωb
- \+ *lemma* ωb_mul_ω
- \+ *lemma* closed_form
- \+ *lemma* two_lt_q
- \+ *lemma* ω_unit_coe
- \+ *lemma* order_ineq
- \+ *lemma* s_mod_succ
- \+ *lemma* modeq_mersenne
- \+ *theorem* ω_pow_formula
- \+ *theorem* mersenne_coe_X
- \+ *theorem* ω_pow_eq_neg_one
- \+ *theorem* ω_pow_eq_one
- \+ *theorem* order_ω
- \+ *theorem* lucas_lehmer_sufficiency
- \+ *def* mersenne
- \+ *def* s
- \+ *def* s_zmod
- \+ *def* s_mod
- \+ *def* lucas_lehmer_residue
- \+ *def* lucas_lehmer_test
- \+ *def* q
- \+ *def* X
- \+ *def* ω
- \+ *def* ωb
- \+ *def* ω_unit



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
- \+ *lemma* units.coe_gpow
- \+ *theorem* gpow_neg_succ_of_nat
- \+ *theorem* gsmul_neg_succ_of_nat
- \- *theorem* gpow_neg_succ
- \- *theorem* gsmul_neg_succ

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* fpow_add_one
- \+ *lemma* fpow_sub_one
- \+ *lemma* fpow_add
- \+ *lemma* units.coe_gpow'
- \- *lemma* fpow_inv
- \- *lemma* unit_pow
- \- *lemma* fpow_neg_succ_of_nat
- \- *lemma* unit_gpow
- \+ *theorem* fpow_neg_succ_of_nat
- \+/\- *theorem* fpow_one_add
- \- *theorem* fpow_neg_succ
- \- *theorem* fpow_add
- \- *theorem* fpow_add_one

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
- \+ *lemma* pow_pf_c_c

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
- \+ *lemma* zero_lt_iff_ne_zero
- \+ *lemma* exists_pos_add_of_lt



## [2020-06-06 07:15:17](https://github.com/leanprover-community/mathlib/commit/d18061f)
chore(algebra/add_torsor): a few more lemmas and implicit args ([#2964](https://github.com/leanprover-community/mathlib/pull/2964))
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_left_cancel_iff
- \+ *lemma* vadd_right_cancel_iff
- \+/\- *lemma* neg_vsub_eq_vsub_rev

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
- \+ *lemma* exp_log_of_neg

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* cpow_neg_one
- \+ *lemma* zero_rpow_le_one
- \+ *lemma* zero_rpow_nonneg
- \+/\- *lemma* rpow_add
- \+ *lemma* rpow_add'
- \+ *lemma* le_rpow_add
- \+ *lemma* rpow_neg_one
- \+ *lemma* has_deriv_at_rpow_of_pos
- \+ *lemma* has_deriv_at_rpow_of_neg
- \+ *lemma* has_deriv_at_rpow
- \+ *lemma* has_deriv_at_rpow_zero_of_one_le
- \+ *lemma* has_deriv_at_rpow_of_one_le
- \+ *lemma* has_deriv_within_at.rpow
- \+ *lemma* has_deriv_at.rpow
- \+ *lemma* differentiable_within_at.rpow
- \+ *lemma* differentiable_at.rpow
- \+ *lemma* differentiable_on.rpow
- \+ *lemma* differentiable.rpow
- \+ *lemma* deriv_within_rpow
- \+ *lemma* deriv_rpow
- \+ *lemma* has_deriv_within_at.rpow_of_one_le
- \+ *lemma* has_deriv_at.rpow_of_one_le
- \+ *lemma* differentiable_within_at.rpow_of_one_le
- \+ *lemma* differentiable_at.rpow_of_one_le
- \+ *lemma* differentiable_on.rpow_of_one_le
- \+ *lemma* differentiable.rpow_of_one_le
- \+ *lemma* deriv_within_rpow_of_one_le
- \+ *lemma* deriv_rpow_of_one_le
- \+ *lemma* has_deriv_within_at.sqrt
- \+ *lemma* has_deriv_at.sqrt
- \+ *lemma* differentiable_within_at.sqrt
- \+ *lemma* differentiable_at.sqrt
- \+ *lemma* differentiable_on.sqrt
- \+ *lemma* differentiable.sqrt
- \+ *lemma* deriv_within_sqrt
- \+ *lemma* deriv_sqrt



## [2020-06-05 13:39:37](https://github.com/leanprover-community/mathlib/commit/5c851bd)
fix(tactic/squeeze_simp): make `squeeze_simp [←...]` work ([#2961](https://github.com/leanprover-community/mathlib/pull/2961))
`squeeze_simp` parses the argument list using a function in core Lean, and when support for backwards arguments was added to `simp`, it used a new function to parse the additional structure. This PR fixes the TODO left in the code to switch `squeeze_simp` to the new function by deleting the code that needed it - it wasn't used anyway!
To add a test for the fix, I moved the single existing `squeeze_simp` test from the deprecated file `examples.lean` to a new file.
#### Estimated changes
Modified src/tactic/squeeze.lean


Modified test/examples.lean


Created test/squeeze.lean




## [2020-06-05 11:58:53](https://github.com/leanprover-community/mathlib/commit/a433eb0)
feat(analysis/special_functions/pow): real powers on ennreal ([#2951](https://github.com/leanprover-community/mathlib/pull/2951))
Real powers of extended nonnegative real numbers. We develop an API based on that of real powers of reals and nnreals, proving the corresponding lemmas.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_le_one
- \+/\- *lemma* rpow_add
- \+ *lemma* rpow_eq_pow
- \+ *lemma* rpow_zero
- \+ *lemma* top_rpow_def
- \+ *lemma* top_rpow_of_pos
- \+ *lemma* top_rpow_of_neg
- \+ *lemma* zero_rpow_of_pos
- \+ *lemma* zero_rpow_of_neg
- \+ *lemma* zero_rpow_def
- \+ *lemma* coe_rpow_of_ne_zero
- \+ *lemma* coe_rpow_of_nonneg
- \+ *lemma* rpow_one
- \+ *lemma* one_rpow
- \+ *lemma* rpow_eq_zero_iff
- \+ *lemma* rpow_eq_top_iff
- \+ *lemma* rpow_neg
- \+ *lemma* rpow_neg_one
- \+ *lemma* rpow_mul
- \+ *lemma* rpow_nat_cast
- \+ *lemma* coe_mul_rpow
- \+ *lemma* mul_rpow_of_ne_top
- \+ *lemma* mul_rpow_of_ne_zero
- \+ *lemma* one_le_rpow
- \+ *lemma* rpow_le_rpow
- \+ *lemma* rpow_lt_rpow
- \+ *lemma* rpow_lt_rpow_of_exponent_lt
- \+ *lemma* rpow_le_rpow_of_exponent_le
- \+ *lemma* rpow_lt_rpow_of_exponent_gt
- \+ *lemma* rpow_le_rpow_of_exponent_ge
- \+ *lemma* one_lt_rpow
- \+ *lemma* rpow_lt_one



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
- \- *lemma* image_add_left_Icc
- \- *lemma* image_add_right_Icc
- \- *lemma* image_neg_Iio
- \- *lemma* image_neg_Iic
- \- *lemma* image_mul_right_Icc'
- \- *lemma* image_mul_right_Icc
- \- *lemma* image_mul_left_Icc'
- \- *lemma* image_mul_left_Icc

Created src/data/set/intervals/image_preimage.lean
- \+ *lemma* preimage_const_add_Ici
- \+ *lemma* preimage_const_add_Ioi
- \+ *lemma* preimage_const_add_Iic
- \+ *lemma* preimage_const_add_Iio
- \+ *lemma* preimage_const_add_Icc
- \+ *lemma* preimage_const_add_Ico
- \+ *lemma* preimage_const_add_Ioc
- \+ *lemma* preimage_const_add_Ioo
- \+ *lemma* preimage_add_const_Ici
- \+ *lemma* preimage_add_const_Ioi
- \+ *lemma* preimage_add_const_Iic
- \+ *lemma* preimage_add_const_Iio
- \+ *lemma* preimage_add_const_Icc
- \+ *lemma* preimage_add_const_Ico
- \+ *lemma* preimage_add_const_Ioc
- \+ *lemma* preimage_add_const_Ioo
- \+ *lemma* preimage_neg_Ici
- \+ *lemma* preimage_neg_Iic
- \+ *lemma* preimage_neg_Ioi
- \+ *lemma* preimage_neg_Iio
- \+ *lemma* preimage_neg_Icc
- \+ *lemma* preimage_neg_Ico
- \+ *lemma* preimage_neg_Ioc
- \+ *lemma* preimage_neg_Ioo
- \+ *lemma* preimage_sub_const_Ici
- \+ *lemma* preimage_sub_const_Ioi
- \+ *lemma* preimage_sub_const_Iic
- \+ *lemma* preimage_sub_const_Iio
- \+ *lemma* preimage_sub_const_Icc
- \+ *lemma* preimage_sub_const_Ico
- \+ *lemma* preimage_sub_const_Ioc
- \+ *lemma* preimage_sub_const_Ioo
- \+ *lemma* preimage_const_sub_Ici
- \+ *lemma* preimage_const_sub_Iic
- \+ *lemma* preimage_const_sub_Ioi
- \+ *lemma* preimage_const_sub_Iio
- \+ *lemma* preimage_const_sub_Icc
- \+ *lemma* preimage_const_sub_Ico
- \+ *lemma* preimage_const_sub_Ioc
- \+ *lemma* preimage_const_sub_Ioo
- \+ *lemma* image_const_add_Ici
- \+ *lemma* image_const_add_Iic
- \+ *lemma* image_const_add_Iio
- \+ *lemma* image_const_add_Ioi
- \+ *lemma* image_const_add_Icc
- \+ *lemma* image_const_add_Ico
- \+ *lemma* image_const_add_Ioc
- \+ *lemma* image_const_add_Ioo
- \+ *lemma* image_add_const_Ici
- \+ *lemma* image_add_const_Iic
- \+ *lemma* image_add_const_Iio
- \+ *lemma* image_add_const_Ioi
- \+ *lemma* image_add_const_Icc
- \+ *lemma* image_add_const_Ico
- \+ *lemma* image_add_const_Ioc
- \+ *lemma* image_add_const_Ioo
- \+ *lemma* image_neg_Ici
- \+ *lemma* image_neg_Iic
- \+ *lemma* image_neg_Ioi
- \+ *lemma* image_neg_Iio
- \+ *lemma* image_neg_Icc
- \+ *lemma* image_neg_Ico
- \+ *lemma* image_neg_Ioc
- \+ *lemma* image_neg_Ioo
- \+ *lemma* image_const_sub_Ici
- \+ *lemma* image_const_sub_Iic
- \+ *lemma* image_const_sub_Ioi
- \+ *lemma* image_const_sub_Iio
- \+ *lemma* image_const_sub_Icc
- \+ *lemma* image_const_sub_Ico
- \+ *lemma* image_const_sub_Ioc
- \+ *lemma* image_const_sub_Ioo
- \+ *lemma* image_sub_const_Ici
- \+ *lemma* image_sub_const_Iic
- \+ *lemma* image_sub_const_Ioi
- \+ *lemma* image_sub_const_Iio
- \+ *lemma* image_sub_const_Icc
- \+ *lemma* image_sub_const_Ico
- \+ *lemma* image_sub_const_Ioc
- \+ *lemma* image_sub_const_Ioo
- \+ *lemma* image_mul_right_Icc'
- \+ *lemma* image_mul_right_Icc
- \+ *lemma* image_mul_left_Icc'
- \+ *lemma* image_mul_left_Icc



## [2020-06-05 10:10:03](https://github.com/leanprover-community/mathlib/commit/1ef65c9)
feat(linear_algebra/quadratic_form): more constructions for quadratic forms ([#2949](https://github.com/leanprover-community/mathlib/pull/2949))
Define multiplication of two linear forms to give a quadratic form and addition of quadratic forms. With these definitions, we can write a generic binary quadratic form as `a • proj R₁ 0 0 + b • proj R₁ 0 1 + c • proj R₁ 1 1 : quadratic_form R₁ (fin 2 → R₁)`.
In order to prove the linearity conditions on the constructions, there are new `simp` lemmas `polar_add_left`, `polar_smul_left`, `polar_add_right` and `polar_smul_right` copying from the corresponding fields of the `quadratic_form` structure, that use `⇑ Q` instead of `Q.to_fun`. The original field names have a `'` appended to avoid name clashes.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* lin_mul_lin_apply
- \+ *lemma* lin_mul_lin_comp
- \+ *lemma* lin_mul_lin_comp_left
- \+ *lemma* lin_mul_lin_comp_right
- \+ *def* lin_mul_lin

Modified src/linear_algebra/quadratic_form.lean
- \+ *lemma* polar_add
- \+ *lemma* polar_neg
- \+ *lemma* polar_smul
- \+ *lemma* polar_comm
- \+ *lemma* polar_add_left
- \+ *lemma* polar_smul_left
- \+ *lemma* polar_add_right
- \+ *lemma* polar_smul_right
- \+ *lemma* zero_apply
- \+ *lemma* coe_fn_add
- \+ *lemma* add_apply
- \+ *lemma* coe_fn_neg
- \+ *lemma* neg_apply
- \+ *lemma* coe_fn_smul
- \+/\- *lemma* smul_apply
- \+ *lemma* lin_mul_lin_apply
- \+ *lemma* add_lin_mul_lin
- \+ *lemma* lin_mul_lin_add
- \+ *lemma* lin_mul_lin_comp
- \+ *lemma* proj_apply
- \+ *lemma* associated_lin_mul_lin
- \+ *lemma* pos_def.smul
- \+ *lemma* pos_def.add
- \+ *lemma* lin_mul_lin_self_pos_def
- \+/\- *lemma* discr_smul
- \- *lemma* associated_smul
- \- *lemma* smul_pos_def_of_smul_nonzero
- \- *lemma* smul_pos_def_of_nonzero
- \+ *def* polar
- \+ *def* mk_left
- \+ *def* lin_mul_lin
- \+ *def* proj
- \+/\- *def* associated
- \- *def* quadratic_form.polar



## [2020-06-05 08:41:12](https://github.com/leanprover-community/mathlib/commit/31ceb62)
feat(data/int|nat/basic): add `add_monoid_hom.ext_nat/int` ([#2957](https://github.com/leanprover-community/mathlib/pull/2957))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* eq_on_inv

Modified src/algebra/group_power.lean


Modified src/data/int/basic.lean
- \+ *lemma* coe_cast_add_hom
- \+ *theorem* ext_int
- \+ *theorem* eq_int_cast_hom
- \+ *theorem* eq_int_cast
- \- *theorem* add_monoid_hom.eq_int_cast
- \+ *def* cast_add_hom

Modified src/data/nat/cast.lean
- \+/\- *lemma* coe_cast_add_monoid_hom
- \+ *lemma* ext_nat
- \+ *lemma* eq_nat_cast
- \+ *lemma* map_nat_cast
- \- *lemma* add_monoid_hom.eq_nat_cast
- \- *lemma* ring_hom.eq_nat_cast
- \- *lemma* ring_hom.map_nat_cast
- \- *lemma* ring_hom.ext_nat
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_pred
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast



## [2020-06-05 08:41:10](https://github.com/leanprover-community/mathlib/commit/edb4422)
feat(algebra/add_torsor): add `equiv.const_vadd` and `equiv.vadd_const` ([#2907](https://github.com/leanprover-community/mathlib/pull/2907))
Also define their `isometric.*` versions in `analysis/normed_space/add_torsor`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_sub_vsub_cancel_right
- \+ *lemma* vadd_vsub_vadd_cancel_right
- \+ *lemma* vsub_sub_vsub_cancel_left
- \+ *lemma* vadd_vsub_vadd_cancel_left
- \+ *lemma* coe_vadd_const
- \+ *lemma* coe_vadd_const_symm
- \+ *lemma* coe_const_vadd
- \+ *lemma* const_vadd_zero
- \+ *lemma* const_vadd_add
- \- *lemma* vsub_sub_vsub_right_cancel
- \- *lemma* vsub_sub_vsub_left_cancel
- \+ *def* vadd_const
- \+ *def* const_vadd
- \+ *def* const_vadd_hom

Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_vadd_cancel_left
- \+ *lemma* dist_vadd_cancel_right
- \+ *lemma* coe_vadd_const
- \+ *lemma* coe_vadd_const_symm
- \+ *lemma* vadd_const_to_equiv
- \+ *lemma* coe_const_vadd
- \+ *lemma* const_vadd_zero
- \+ *def* vadd_const
- \+ *def* const_vadd



## [2020-06-05 07:28:47](https://github.com/leanprover-community/mathlib/commit/a130c73)
feat(topology/algebra/ordered): list of preconnected sets ([#2943](https://github.com/leanprover-community/mathlib/pull/2943))
A subset of a densely ordered conditionally complete lattice (e.g., `ℝ`) with order topology is preconnected if and only if it is one of the intervals.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* subset_diff_singleton
- \+ *lemma* diff_inter
- \+ *lemma* diff_compl
- \+ *lemma* diff_diff_right
- \+ *lemma* diff_diff_cancel_left
- \+/\- *lemma* mem_diff_singleton

Modified src/data/set/intervals/basic.lean
- \+ *lemma* Icc_diff_left
- \+ *lemma* Icc_diff_right
- \+ *lemma* Ico_diff_left
- \+ *lemma* Ioc_diff_right
- \+ *lemma* Icc_diff_both
- \+ *lemma* Ici_diff_left
- \+ *lemma* Iic_diff_right
- \+ *lemma* Ico_diff_Ioo_same
- \+ *lemma* Ioc_diff_Ioo_same
- \+ *lemma* Icc_diff_Ico_same
- \+ *lemma* Icc_diff_Ioc_same
- \+ *lemma* Icc_diff_Ioo_same
- \+ *lemma* Ici_diff_Ioi_same
- \+ *lemma* Iic_diff_Iio_same
- \+ *lemma* Ioi_union_left
- \+ *lemma* Iio_union_right
- \+ *lemma* mem_Ici_Ioi_of_subset_of_subset
- \+ *lemma* mem_Iic_Iio_of_subset_of_subset
- \+ *lemma* mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
- \- *lemma* Ico_diff_Ioo_eq_singleton
- \- *lemma* Ioc_diff_Ioo_eq_singleton
- \- *lemma* Icc_diff_Ico_eq_singleton
- \- *lemma* Icc_diff_Ioc_eq_singleton

Modified src/order/bounds.lean
- \+ *lemma* not_bdd_above_iff'
- \+ *lemma* not_bdd_below_iff'
- \+ *lemma* not_bdd_above_iff
- \+ *lemma* not_bdd_below_iff
- \+ *lemma* nonempty_of_not_bdd_above
- \+ *lemma* nonempty_of_not_bdd_below

Modified src/topology/algebra/ordered.lean
- \+ *lemma* is_preconnected.Icc_subset
- \+ *lemma* is_preconnected.eq_univ_of_unbounded
- \+ *lemma* is_lub.nhds_within_ne_bot
- \+ *lemma* is_glb.nhds_within_ne_bot
- \+/\- *lemma* mem_closure_of_is_lub
- \+/\- *lemma* mem_of_is_lub_of_is_closed
- \+/\- *lemma* mem_closure_of_is_glb
- \+/\- *lemma* mem_of_is_glb_of_is_closed
- \+/\- *lemma* cSup_mem_closure
- \+/\- *lemma* cInf_mem_closure
- \+/\- *lemma* cSup_mem_of_is_closed
- \+/\- *lemma* cInf_mem_of_is_closed
- \+ *lemma* is_connected.Ioo_cInf_cSup_subset
- \+ *lemma* is_preconnected.Ioi_cInf_subset
- \+ *lemma* is_preconnected.Iio_cSup_subset
- \+ *lemma* is_preconnected.mem_intervals
- \+ *lemma* set_of_is_preconnected_subset_of_ordered
- \+ *lemma* set_of_is_preconnected_eq_of_ordered
- \- *lemma* is_preconnected.forall_Icc_subset
- \- *lemma* nhds_principal_ne_bot_of_is_lub
- \- *lemma* nhds_principal_ne_bot_of_is_glb

Modified src/topology/subset_properties.lean




## [2020-06-05 05:31:21](https://github.com/leanprover-community/mathlib/commit/8f89bd8)
chore(algebra/group_power): simplify a proof ([#2955](https://github.com/leanprover-community/mathlib/pull/2955))
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *lemma* gpow_add_one
- \+ *lemma* gpow_sub_one
- \+ *lemma* gpow_add
- \+ *lemma* gpow_sub
- \+ *lemma* sub_gsmul
- \+/\- *theorem* add_one_gsmul
- \+/\- *theorem* gpow_mul
- \- *theorem* gpow_add
- \- *theorem* gpow_add_one



## [2020-06-05 05:31:19](https://github.com/leanprover-community/mathlib/commit/d7fa405)
chore(algebra/*): merge `inv_inv''` with `inv_inv'` ([#2954](https://github.com/leanprover-community/mathlib/pull/2954))
#### Estimated changes
Modified src/algebra/field.lean
- \- *lemma* inv_inv'

Modified src/algebra/group_with_zero.lean
- \+ *lemma* inv_inv'
- \- *lemma* inv_inv''

Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/pointwise.lean




## [2020-06-05 05:31:17](https://github.com/leanprover-community/mathlib/commit/8161888)
feat(group_theory/subgroup): define normal bundled subgroups ([#2947](https://github.com/leanprover-community/mathlib/pull/2947))
Most proofs are adapted from `deprecated/subgroup`.
#### Estimated changes
Modified src/group_theory/subgroup.lean
- \+ *lemma* mul_mem_cancel_left
- \+ *lemma* mul_mem_cancel_right
- \+/\- *lemma* coe_inv
- \+ *lemma* coe_mk
- \+ *lemma* normal_of_comm
- \+ *lemma* conj_mem
- \+ *lemma* mem_comm
- \+ *lemma* mem_comm_iff
- \+ *lemma* bot_normal
- \+ *lemma* mem_center_iff
- \+ *lemma* center_normal
- \+ *lemma* mem_normalizer_iff
- \+ *lemma* le_normalizer
- \+ *lemma* normal_in_normalizer
- \+ *lemma* le_normalizer_of_normal
- \+ *lemma* sub_mem
- \+ *lemma* range_top_of_surjective
- \+ *lemma* normal_ker
- \- *lemma* rang_top_of_surjective
- \+ *def* normal
- \+ *def* center
- \+ *def* normalizer



## [2020-06-05 05:31:15](https://github.com/leanprover-community/mathlib/commit/2131382)
feat(data/setoid/partition): some lemmas about partitions ([#2937](https://github.com/leanprover-community/mathlib/pull/2937))
#### Estimated changes
Modified src/data/setoid/partition.lean
- \+ *lemma* is_partition_classes
- \+ *lemma* is_partition.pairwise_disjoint
- \+ *lemma* is_partition.sUnion_eq_univ



## [2020-06-05 04:53:19](https://github.com/leanprover-community/mathlib/commit/80a52e9)
chore(analysis/convex/basic): add `finset.convex_hull_eq` ([#2956](https://github.com/leanprover-community/mathlib/pull/2956))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* finset.convex_hull_eq
- \+/\- *lemma* set.finite.convex_hull_eq



## [2020-06-04 18:38:01](https://github.com/leanprover-community/mathlib/commit/2ceb7f7)
feat(analysis/convex): preparatory statement for caratheodory ([#2944](https://github.com/leanprover-community/mathlib/pull/2944))
Proves
```lean
lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t
```
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+ *lemma* convex_hull_singleton
- \+ *lemma* convex_hull_eq_union_convex_hull_finite_subsets



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
- \+ *lemma* unop_eq_zero_iff
- \+ *lemma* op_eq_zero_iff
- \+ *lemma* unop_eq_one_iff
- \+ *lemma* op_eq_one_iff

Modified src/data/equiv/mul_add.lean
- \+ *lemma* to_fun_apply

Modified src/data/equiv/ring.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* to_opposite_apply
- \+ *lemma* to_opposite_symm_apply
- \+ *def* to_opposite

Modified src/data/opposite.lean
- \+ *lemma* equiv_to_opposite_apply
- \+ *lemma* equiv_to_opposite_symm_apply
- \+ *def* equiv_to_opposite

Modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* smul_right
- \+/\- *lemma* zero_left
- \+/\- *lemma* zero_right
- \+/\- *lemma* neg_left
- \+/\- *lemma* neg_right
- \+/\- *lemma* sym
- \+/\- *lemma* is_refl
- \+/\- *def* is_sym

Modified src/ring_theory/maps.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_ring_equiv
- \+ *lemma* map_eq_zero_iff
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* bijective
- \- *lemma* map_zero_iff
- \- *lemma* map_add
- \- *lemma* map_mul
- \- *lemma* map_one
- \- *lemma* map_neg_one
- \- *theorem* comm_ring.hom_to_anti_hom
- \- *theorem* comm_ring.anti_hom_to_hom
- \+ *def* mk'
- \- *def* to_ring_anti_equiv
- \- *def* comm_ring.equiv_to_anti_equiv
- \- *def* comm_ring.anti_equiv_to_equiv

Modified src/topology/algebra/uniform_ring.lean
- \+ *def* coe_ring_hom
- \+ *def* extension_hom
- \+ *def* map_ring_hom



## [2020-06-04 15:38:26](https://github.com/leanprover-community/mathlib/commit/7d803a9)
feat(topology/metric_space/isometry): group structure on isometries ([#2950](https://github.com/leanprover-community/mathlib/pull/2950))
Closes [#2908](https://github.com/leanprover-community/mathlib/pull/2908)
#### Estimated changes
Modified src/topology/metric_space/isometry.lean
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* inv_apply_self
- \+ *lemma* apply_inv_self



## [2020-06-04 15:38:24](https://github.com/leanprover-community/mathlib/commit/add0c9a)
feat(ring/localization): add construction of localization as a quotient type ([#2922](https://github.com/leanprover-community/mathlib/pull/2922))
#### Estimated changes
Modified src/group_theory/congruence.lean


Modified src/group_theory/monoid_localization.lean
- \+ *lemma* one_rel
- \+ *lemma* mk_one_eq_monoid_of_mk
- \+ *lemma* mk_eq_monoid_of_mk'_apply
- \+ *lemma* mk_eq_monoid_of_mk'
- \+ *lemma* mul_equiv_of_quotient_apply
- \+ *lemma* mul_equiv_of_quotient_mk'
- \+ *lemma* mul_equiv_of_quotient_mk
- \+ *lemma* mul_equiv_of_quotient_monoid_of
- \+ *lemma* mul_equiv_of_quotient_symm_mk'
- \+ *lemma* mul_equiv_of_quotient_symm_mk
- \+ *lemma* mul_equiv_of_quotient_symm_monoid_of
- \+ *theorem* ind
- \+ *theorem* induction_on
- \+ *theorem* induction_on₂
- \+ *theorem* induction_on₃
- \+ *theorem* r_of_eq
- \+ *def* mk
- \+ *def* monoid_of

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/localization.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* to_map_injective
- \+/\- *lemma* sec_spec
- \+/\- *lemma* sec_spec'
- \+/\- *lemma* eq_iff_eq
- \+/\- *lemma* mk'_eq_iff_mk'_eq
- \+/\- *lemma* lift_left_inverse
- \+ *lemma* monoid_of_eq_of
- \+ *lemma* mk_one_eq_of
- \+ *lemma* mk_eq_mk'_apply
- \+ *lemma* mk_eq_mk'
- \+ *lemma* ring_equiv_of_quotient_apply
- \+ *lemma* ring_equiv_of_quotient_mk'
- \+ *lemma* ring_equiv_of_quotient_mk
- \+ *lemma* ring_equiv_of_quotient_of
- \+ *lemma* ring_equiv_of_quotient_symm_mk'
- \+ *lemma* ring_equiv_of_quotient_symm_mk
- \+ *lemma* ring_equiv_of_quotient_symm_of
- \+ *def* to_localization_map
- \+ *def* submonoid.localization_map.to_ring_localization
- \+ *def* of
- \+/\- *def* codomain
- \+/\- *def* fraction_map
- \- *def* to_localization



## [2020-06-04 15:06:53](https://github.com/leanprover-community/mathlib/commit/2dbf550)
feat(ring_theory/eisenstein_criterion): Eisenstein's criterion ([#2946](https://github.com/leanprover-community/mathlib/pull/2946))
#### Estimated changes
Created src/ring_theory/eisenstein_criterion.lean
- \+ *lemma* map_eq_C_mul_X_pow_of_forall_coeff_mem
- \+ *lemma* le_nat_degree_of_map_eq_mul_X_pow
- \+ *lemma* eval_zero_mem_ideal_of_eq_mul_X_pow
- \+ *lemma* is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
- \+ *theorem* irreducible_of_eisenstein_criterion

Created src/ring_theory/prime.lean
- \+ *lemma* mul_eq_mul_prime_prod
- \+ *lemma* mul_eq_mul_prime_pow



## [2020-06-04 14:28:44](https://github.com/leanprover-community/mathlib/commit/c2e78d2)
refactor(data/zmod): generalize zmod.cast_hom ([#2900](https://github.com/leanprover-community/mathlib/pull/2900))
Currently, `zmod.cast_hom` would cast `zmod n` to rings `R` of characteristic `n`.
This PR builds `cast_hom` for rings `R` with characteristic `m` that divides `n`.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+/\- *lemma* cast_one
- \+/\- *lemma* cast_add
- \+/\- *lemma* cast_mul
- \+/\- *lemma* cast_hom_apply
- \+ *lemma* cast_sub
- \+ *lemma* cast_pow
- \+/\- *lemma* cast_nat_cast
- \+/\- *lemma* cast_int_cast
- \+ *lemma* cast_one'
- \+ *lemma* cast_add'
- \+ *lemma* cast_mul'
- \+ *lemma* cast_sub'
- \+ *lemma* cast_pow'
- \+ *lemma* cast_nat_cast'
- \+ *lemma* cast_int_cast'
- \+/\- *def* cast_hom

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
- \+ *lemma* le_of_forall_sub_le
- \- *lemma* ge_of_forall_ge_sub

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* le_add_of_nonneg_right
- \+/\- *lemma* le_add_of_nonneg_left
- \+/\- *lemma* lt_add_of_pos_right
- \+/\- *lemma* lt_add_of_pos_left
- \+/\- *lemma* sub_le_self
- \+/\- *lemma* sub_lt_self
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_pos_of_ne_zero

Modified src/analysis/normed_space/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/pi.lean
- \+/\- *lemma* sqrt_two_add_series_zero_nonneg
- \+/\- *lemma* sqrt_two_add_series_nonneg
- \+/\- *lemma* pi_gt_sqrt_two_add_series

Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/integration.lean


Modified src/number_theory/dioph.lean
- \+/\- *theorem* pell_dioph
- \+/\- *theorem* xn_dioph

Modified src/number_theory/pell.lean
- \+/\- *lemma* eq_pow_of_pell_lem
- \+/\- *theorem* xy_modeq_of_modeq
- \+/\- *theorem* matiyasevic

Modified src/order/complete_lattice.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/power_series.lean
- \+ *lemma* nat_le_order
- \+ *lemma* le_order
- \+ *lemma* le_order_add
- \- *lemma* order_ge_nat
- \- *lemma* order_ge
- \- *lemma* order_add_ge

Modified src/tactic/lint/misc.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean
- \+/\- *lemma* diam_closed_ball
- \+/\- *lemma* diam_ball
- \+/\- *theorem* eq_of_forall_dist_le
- \+/\- *theorem* pos_of_mem_ball
- \+/\- *theorem* mem_ball_self
- \+/\- *theorem* mem_closed_ball_self

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
- \+ *lemma* tendsto_add_one_pow_at_top_at_top_of_pos
- \+ *lemma* tendsto_pow_at_top_at_top_of_one_lt
- \+ *lemma* nat.tendsto_pow_at_top_at_top_of_one_lt
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1
- \- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

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
- \+ *def* adjunction.of_left_adjoint
- \+ *def* adjunction.of_right_adjoint

Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *def* of_cone_equiv
- \+ *def* of_cocone_equiv

Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean
- \+ *def* preserves_colimit_of_iso



## [2020-06-03 13:41:29](https://github.com/leanprover-community/mathlib/commit/e205228)
feat(data/fintype/basic): to_finset_inj ([#2938](https://github.com/leanprover-community/mathlib/pull/2938))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *theorem* to_finset_inj



## [2020-06-03 13:41:27](https://github.com/leanprover-community/mathlib/commit/74037cb)
feat(topology/algebra/ordered): IVT for two functions ([#2933](https://github.com/leanprover-community/mathlib/pull/2933))
Also rename some `is_connected_I*` lemmas to `is_preconnected_I*`.
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* closure_le_eq
- \+/\- *lemma* closure_lt_subset_le
- \+ *lemma* is_closed.is_closed_le
- \+ *lemma* intermediate_value_univ₂
- \+ *lemma* is_preconnected.intermediate_value₂
- \+/\- *lemma* intermediate_value_univ
- \+/\- *lemma* is_preconnected.forall_Icc_subset
- \+ *lemma* is_preconnected_Icc
- \+ *lemma* is_preconnected_Ioo
- \+/\- *lemma* tendsto_abs_at_top_at_top
- \- *lemma* is_connected_Icc
- \- *lemma* is_connected_Ioo

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
- \+/\- *lemma* tendsto_indicator_of_monotone
- \+/\- *lemma* tendsto_indicator_of_antimono
- \+/\- *lemma* tendsto_indicator_bUnion_finset

Modified src/tactic/localized.lean




## [2020-06-03 12:09:46](https://github.com/leanprover-community/mathlib/commit/ed91bb2)
feat(data/setoid/partition): sUnion _classes ([#2936](https://github.com/leanprover-community/mathlib/pull/2936))
#### Estimated changes
Modified src/data/setoid/partition.lean
- \+ *theorem* sUnion_classes



## [2020-06-03 12:09:44](https://github.com/leanprover-community/mathlib/commit/c3221f7)
feat(data/rat): denom_div_cast_eq_one_iff ([#2934](https://github.com/leanprover-community/mathlib/pull/2934))
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* coe_int_inj
- \+ *lemma* denom_div_cast_eq_one_iff



## [2020-06-03 12:09:43](https://github.com/leanprover-community/mathlib/commit/1f2102d)
chore(group_theory/group_action): protect_proj attribute for mul_action ([#2931](https://github.com/leanprover-community/mathlib/pull/2931))
#### Estimated changes
Modified src/group_theory/group_action.lean




## [2020-06-03 12:09:41](https://github.com/leanprover-community/mathlib/commit/687fc51)
ci(bors): set `cut_body_after` to `---` ([#2927](https://github.com/leanprover-community/mathlib/pull/2927))
#### Estimated changes
Created .github/PULL_REQUEST_TEMPLATE.md


Modified bors.toml




## [2020-06-03 12:09:39](https://github.com/leanprover-community/mathlib/commit/9fc2413)
feat(order/iterate): a few more lemmas about `f^[n]` ([#2925](https://github.com/leanprover-community/mathlib/pull/2925))
#### Estimated changes
Modified src/algebra/order.lean
- \+ *theorem* compares_iff_of_compares_impl

Modified src/logic/function/iterate.lean
- \+/\- *theorem* iterate_id

Modified src/order/iterate.lean
- \+ *lemma* iterate_pos_le_iff_map_le
- \+ *lemma* iterate_pos_le_iff_map_le'
- \+ *lemma* iterate_pos_eq_iff_map_eq
- \+ *lemma* iterate_le_of_le
- \+ *lemma* iterate_ge_of_ge



## [2020-06-03 12:09:37](https://github.com/leanprover-community/mathlib/commit/0ec9c0e)
feat(algebra/iterate_hom): add `mul_left_iterate` etc ([#2923](https://github.com/leanprover-community/mathlib/pull/2923))
#### Estimated changes
Modified src/algebra/iterate_hom.lean
- \+ *lemma* mul_left_iterate
- \+ *lemma* add_left_iterate
- \+ *lemma* mul_right_iterate
- \+ *lemma* add_right_iterate



## [2020-06-03 11:09:01](https://github.com/leanprover-community/mathlib/commit/8d9e541)
feat(group_theory/group_action): some lemmas about orbits ([#2928](https://github.com/leanprover-community/mathlib/pull/2928))
also remove the simp attribute unfolding the definition of orbit.
Depends on [#2924](https://github.com/leanprover-community/mathlib/pull/2924)
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+/\- *lemma* mem_orbit_iff
- \+ *lemma* mem_orbit_smul
- \+ *lemma* smul_mem_orbit_smul



## [2020-06-03 09:28:49](https://github.com/leanprover-community/mathlib/commit/5020285)
chore(group_theory/group_action): simp attributes on inv_smul_smul and smul_inv_smul ([#2924](https://github.com/leanprover-community/mathlib/pull/2924))
#### Estimated changes
Modified src/group_theory/group_action.lean
- \+/\- *lemma* inv_smul_smul
- \+/\- *lemma* smul_inv_smul



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
- \+ *lemma* nnnorm_one
- \+ *lemma* nnnorm_inv
- \+ *lemma* norm_eq_abs
- \+ *lemma* norm_coe_nat
- \+ *lemma* nnnorm_coe_nat
- \+ *lemma* norm_two
- \+ *lemma* nnnorm_two
- \- *lemma* real.norm_eq_abs
- \- *lemma* real.norm_two

Created src/analysis/normed_space/enorm.lean
- \+ *lemma* coe_fn_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* map_smul
- \+ *lemma* map_zero
- \+ *lemma* eq_zero_iff
- \+ *lemma* map_neg
- \+ *lemma* map_sub_rev
- \+ *lemma* map_add_le
- \+ *lemma* map_sub_le
- \+ *lemma* top_map
- \+ *lemma* coe_max
- \+ *lemma* max_map
- \+ *lemma* finite_dist_eq
- \+ *lemma* finite_edist_eq
- \+ *lemma* finite_norm_eq
- \+ *def* emetric_space
- \+ *def* finite_subspace



## [2020-06-02 21:15:28](https://github.com/leanprover-community/mathlib/commit/efae3d9)
feat(data/mv_polynomial): C_inj and C_injective ([#2920](https://github.com/leanprover-community/mathlib/pull/2920))
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* C_injective
- \+ *lemma* C_inj



## [2020-06-02 19:58:24](https://github.com/leanprover-community/mathlib/commit/607286e)
feat(data/*): ring_hom.ext_{nat,int,rat,zmod} ([#2918](https://github.com/leanprover-community/mathlib/pull/2918))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* ext_int

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
- \+ *lemma* arrow_congr_apply
- \+ *lemma* arrow_congr_comp
- \+ *lemma* conj_apply
- \+ *lemma* conj_id

Modified src/linear_algebra/matrix.lean
- \+ *def* alg_equiv_matrix'
- \+ *def* linear_equiv.alg_conj
- \+ *def* alg_equiv_matrix



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
- \+ *lemma* is_least.mono
- \+ *lemma* is_greatest.mono
- \+ *lemma* is_lub.mono
- \+ *lemma* is_glb.mono

Modified src/order/complete_lattice.lean


Created src/order/semiconj_Sup.lean
- \+ *lemma* is_order_right_adjoint_Sup
- \+ *lemma* is_order_right_adjoint_cSup
- \+ *lemma* is_order_right_adjoint.unique
- \+ *lemma* is_order_right_adjoint.right_mono
- \+ *lemma* semiconj.symm_adjoint
- \+ *lemma* semiconj_of_is_lub
- \+ *lemma* Sup_div_semiconj
- \+ *lemma* cSup_div_semiconj
- \+ *def* is_order_right_adjoint



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
- \+/\- *theorem* length_sorted_univ

Modified src/data/equiv/local_equiv.lean


Modified src/data/fin_enum.lean
- \+/\- *lemma* finset.mem_enum
- \+/\- *lemma* mem_pi
- \+/\- *lemma* pi.mem_enum
- \+/\- *def* of_nodup_list
- \+/\- *def* pi

Modified src/data/finset.lean
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* pi.cons_same
- \+/\- *lemma* pi.cons_ne
- \+/\- *lemma* exists_max_image
- \+/\- *lemma* exists_min_image
- \+/\- *lemma* disjoint_filter_filter
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* mem_union_left
- \+/\- *theorem* mem_union_right
- \+/\- *theorem* insert_union_distrib
- \+/\- *theorem* mem_of_mem_inter_left
- \+/\- *theorem* mem_of_mem_inter_right
- \+/\- *theorem* sdiff_subset_sdiff
- \+/\- *theorem* image_to_finset
- \+/\- *theorem* sigma_eq_bind
- \+/\- *theorem* fold_insert
- \+/\- *def* pi.cons

Modified src/data/int/basic.lean
- \+/\- *lemma* test_bit_ldiff
- \+/\- *lemma* shiftr_neg_succ
- \+/\- *theorem* coe_nat_le
- \+/\- *theorem* coe_nat_lt
- \+/\- *theorem* coe_nat_inj'
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* coe_nat_bit0
- \+/\- *theorem* coe_nat_bit1

Modified src/data/int/modeq.lean
- \+/\- *theorem* modeq_add_cancel_left
- \+/\- *theorem* modeq_add_cancel_right

Modified src/data/list/bag_inter.lean


Modified src/data/list/basic.lean
- \+/\- *theorem* exists_of_mem_map
- \+/\- *theorem* map_subset_iff

Modified src/data/list/defs.lean
- \+/\- *def* split_on_p_aux

Modified src/data/list/forall2.lean
- \+/\- *lemma* forall₂_cons_left_iff

Modified src/data/list/func.lean
- \+/\- *lemma* pointwise_nil

Modified src/data/list/min_max.lean


Modified src/data/list/nodup.lean
- \+/\- *theorem* nth_le_index_of
- \+/\- *theorem* nodup_erase_eq_filter
- \+/\- *theorem* nodup_join

Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean
- \+/\- *theorem* permutations_aux2_snd_cons
- \+/\- *theorem* length_permutations_aux

Modified src/data/list/range.lean
- \+/\- *theorem* map_sub_range'

Modified src/data/list/zip.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/pequiv.lean
- \+/\- *lemma* single_trans_single

Modified src/data/pnat/basic.lean
- \+/\- *lemma* bit0_le_bit0
- \+/\- *lemma* bit0_le_bit1
- \+/\- *lemma* bit1_le_bit0
- \+/\- *lemma* bit1_le_bit1

Modified src/data/polynomial.lean
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \+/\- *lemma* coeff_sub
- \+/\- *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* coeff_derivative
- \+/\- *lemma* derivative_eval

Modified src/data/quot.lean
- \+/\- *lemma* quotient.lift_beta
- \+/\- *lemma* quotient.lift_on_beta

Modified src/data/rat/basic.lean


Modified src/data/real/cau_seq.lean
- \+/\- *theorem* const_inv

Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* of_real_le_of_real_iff
- \+/\- *lemma* of_real_lt_of_real_iff

Modified src/data/real/nnreal.lean


Modified src/data/seq/computation.lean
- \+/\- *theorem* destruct_map

Modified src/data/seq/wseq.lean
- \+/\- *theorem* destruct_flatten
- \+/\- *theorem* nth_terminates_le
- \+/\- *theorem* head_terminates_of_nth_terminates
- \+/\- *theorem* destruct_terminates_of_nth_terminates

Modified src/data/ulift.lean
- \+/\- *lemma* plift.rec.constant
- \+/\- *lemma* ulift.rec.constant

Modified src/data/zmod/basic.lean


Modified src/deprecated/group.lean


Modified src/logic/relation.lean
- \+/\- *lemma* trans
- \+/\- *lemma* equivalence_join
- \+/\- *lemma* refl_trans_gen_of_transitive_reflexive

Modified src/logic/relator.lean
- \+/\- *lemma* rel_forall_of_right_total
- \+/\- *lemma* rel_exists_of_left_total

Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* integrable_smul_iff
- \+/\- *lemma* norm_of_fun
- \+/\- *lemma* dist_to_fun
- \+/\- *lemma* norm_eq_norm_to_fun

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
Created src/deprecated/subgroup.lean
- \+ *lemma* injective_mul
- \+ *lemma* additive.is_add_subgroup
- \+ *lemma* multiplicative.is_subgroup
- \+ *lemma* is_subgroup.coe_inv
- \+ *lemma* is_subgroup.coe_gpow
- \+ *lemma* is_add_subgroup.gsmul_coe
- \+ *lemma* is_subgroup_Union_of_directed
- \+ *lemma* is_subgroup.gpow_mem
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+ *lemma* gpowers_subset
- \+ *lemma* gmultiples_subset
- \+ *lemma* mem_gpowers
- \+ *lemma* mem_gmultiples
- \+ *lemma* inv_mem_iff
- \+ *lemma* mul_mem_cancel_left
- \+ *lemma* mul_mem_cancel_right
- \+ *lemma* normal_subgroup_of_comm_group
- \+ *lemma* additive.normal_add_subgroup
- \+ *lemma* multiplicative.normal_subgroup
- \+ *lemma* mem_norm_comm
- \+ *lemma* mem_norm_comm_iff
- \+ *lemma* mem_trivial
- \+ *lemma* eq_trivial_iff
- \+ *lemma* mem_center
- \+ *lemma* subset_normalizer
- \+ *lemma* mem_ker
- \+ *lemma* one_ker_inv
- \+ *lemma* one_ker_inv'
- \+ *lemma* inv_ker_one
- \+ *lemma* inv_ker_one'
- \+ *lemma* one_iff_ker_inv
- \+ *lemma* one_iff_ker_inv'
- \+ *lemma* inv_iff_ker
- \+ *lemma* inv_iff_ker'
- \+ *lemma* inj_of_trivial_ker
- \+ *lemma* trivial_ker_of_inj
- \+ *lemma* inj_iff_trivial_ker
- \+ *lemma* trivial_ker_iff_eq_one
- \+ *lemma* mem_closure
- \+ *lemma* closure_subset_iff
- \+ *lemma* closure_subgroup
- \+ *lemma* image_closure
- \+ *lemma* trivial_eq_closure
- \+ *lemma* mem_conjugates_self
- \+ *lemma* mem_conjugates_of_set_iff
- \+ *lemma* conjugates_subset
- \+ *lemma* conj_mem_conjugates_of_set
- \+ *lemma* normal_closure_subset_iff
- \+ *lemma* simple_group_of_surjective
- \+ *theorem* additive.is_add_subgroup_iff
- \+ *theorem* multiplicative.is_subgroup_iff
- \+ *theorem* is_subgroup.of_div
- \+ *theorem* is_add_subgroup.of_sub
- \+ *theorem* is_add_subgroup.sub_mem
- \+ *theorem* additive.normal_add_subgroup_iff
- \+ *theorem* multiplicative.normal_subgroup_iff
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_mono
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mclosure_subset
- \+ *theorem* mclosure_inv_subset
- \+ *theorem* closure_eq_mclosure
- \+ *theorem* mem_closure_union_iff
- \+ *theorem* gpowers_eq_closure
- \+ *theorem* subset_conjugates_of_set
- \+ *theorem* conjugates_of_set_mono
- \+ *theorem* conjugates_of_set_subset
- \+ *theorem* conjugates_of_set_subset_normal_closure
- \+ *theorem* subset_normal_closure
- \+ *theorem* normal_closure_subset
- \+ *theorem* normal_closure_mono
- \+ *theorem* additive.simple_add_group_iff
- \+ *theorem* multiplicative.simple_group_iff
- \+ *def* gpowers
- \+ *def* gmultiples
- \+ *def* trivial
- \+ *def* center
- \+ *def* normalizer
- \+ *def* ker
- \+ *def* monoid_hom.range_subtype_val
- \+ *def* monoid_hom.range_factorization
- \+ *def* closure
- \+ *def* conjugates
- \+ *def* conjugates_of_set
- \+ *def* normal_closure
- \+ *def* subgroup.of

Created src/deprecated/submonoid.lean
- \+ *lemma* additive.is_add_submonoid
- \+ *lemma* multiplicative.is_submonoid
- \+ *lemma* is_submonoid_Union_of_directed
- \+ *lemma* powers.one_mem
- \+ *lemma* multiples.zero_mem
- \+ *lemma* powers.self_mem
- \+ *lemma* multiples.self_mem
- \+ *lemma* powers.mul_mem
- \+ *lemma* multiples.add_mem
- \+ *lemma* image.is_submonoid
- \+ *lemma* is_submonoid.pow_mem
- \+ *lemma* is_add_submonoid.smul_mem
- \+ *lemma* is_submonoid.power_subset
- \+ *lemma* is_add_submonoid.multiple_subset
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* finset_prod_mem
- \+ *lemma* is_submonoid.coe_one
- \+ *lemma* is_submonoid.coe_mul
- \+ *lemma* is_submonoid.coe_pow
- \+ *lemma* is_add_submonoid.smul_coe
- \+ *lemma* image_closure
- \+ *theorem* additive.is_add_submonoid_iff
- \+ *theorem* multiplicative.is_submonoid_iff
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_mono
- \+ *theorem* closure_singleton
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mem_closure_union_iff
- \+ *def* powers
- \+ *def* multiples
- \+ *def* closure
- \+ *def* submonoid.of

Deleted src/group_theory/bundled_subgroup.lean
- \- *lemma* coe_to_submonoid
- \- *lemma* mem_coe
- \- *lemma* coe_coe
- \- *lemma* list_prod_mem
- \- *lemma* multiset_prod_mem
- \- *lemma* prod_mem
- \- *lemma* pow_mem
- \- *lemma* gpow_mem
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* coe_inv
- \- *lemma* le_def
- \- *lemma* coe_subset_coe
- \- *lemma* mem_bot
- \- *lemma* mem_top
- \- *lemma* coe_top
- \- *lemma* coe_bot
- \- *lemma* coe_inf
- \- *lemma* mem_inf
- \- *lemma* coe_Inf
- \- *lemma* mem_Inf
- \- *lemma* mem_closure
- \- *lemma* subset_closure
- \- *lemma* closure_le
- \- *lemma* closure_eq_of_le
- \- *lemma* closure_induction
- \- *lemma* closure_mono
- \- *lemma* closure_eq
- \- *lemma* closure_empty
- \- *lemma* closure_univ
- \- *lemma* closure_union
- \- *lemma* closure_Union
- \- *lemma* mem_closure_singleton
- \- *lemma* mem_supr_of_directed
- \- *lemma* mem_Sup_of_directed_on
- \- *lemma* coe_comap
- \- *lemma* mem_comap
- \- *lemma* comap_comap
- \- *lemma* coe_map
- \- *lemma* mem_map
- \- *lemma* map_map
- \- *lemma* map_le_iff_le_comap
- \- *lemma* gc_map_comap
- \- *lemma* map_sup
- \- *lemma* map_supr
- \- *lemma* comap_inf
- \- *lemma* comap_infi
- \- *lemma* map_bot
- \- *lemma* comap_top
- \- *lemma* coe_prod
- \- *lemma* mem_prod
- \- *lemma* prod_mono
- \- *lemma* prod_mono_right
- \- *lemma* prod_mono_left
- \- *lemma* prod_top
- \- *lemma* top_prod
- \- *lemma* top_prod_top
- \- *lemma* bot_prod_bot
- \- *lemma* gsmul_mem
- \- *lemma* coe_range
- \- *lemma* mem_range
- \- *lemma* map_range
- \- *lemma* range_top_iff_surjective
- \- *lemma* rang_top_of_surjective
- \- *lemma* mem_ker
- \- *lemma* comap_ker
- \- *lemma* eq_on_closure
- \- *lemma* eq_of_eq_on_top
- \- *lemma* eq_of_eq_on_dense
- \- *lemma* gclosure_preimage_le
- \- *lemma* map_closure
- \- *theorem* ext'
- \- *theorem* ext
- \- *theorem* one_mem
- \- *theorem* mul_mem
- \- *theorem* inv_mem
- \- *theorem* coe_subtype
- \- *def* subgroup.of
- \- *def* subgroup.to_add_subgroup
- \- *def* subgroup.of_add_subgroup
- \- *def* add_subgroup.to_subgroup
- \- *def* add_subgroup.of_subgroup
- \- *def* subgroup.add_subgroup_equiv
- \- *def* subtype
- \- *def* closure
- \- *def* comap
- \- *def* map
- \- *def* prod
- \- *def* prod_equiv
- \- *def* range
- \- *def* ker
- \- *def* eq_locus
- \- *def* subgroup_congr

Modified src/group_theory/coset.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/subgroup.lean
- \+ *lemma* coe_to_submonoid
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* prod_mem
- \+ *lemma* pow_mem
- \+ *lemma* gpow_mem
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_inv
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+/\- *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* mem_closure_singleton
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_mono_right
- \+ *lemma* prod_mono_left
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* bot_prod_bot
- \+ *lemma* gsmul_mem
- \+ *lemma* coe_range
- \+ *lemma* mem_range
- \+ *lemma* map_range
- \+ *lemma* range_top_iff_surjective
- \+ *lemma* rang_top_of_surjective
- \+/\- *lemma* mem_ker
- \+ *lemma* comap_ker
- \+ *lemma* eq_on_closure
- \+ *lemma* eq_of_eq_on_top
- \+ *lemma* eq_of_eq_on_dense
- \+ *lemma* gclosure_preimage_le
- \+ *lemma* map_closure
- \- *lemma* injective_mul
- \- *lemma* additive.is_add_subgroup
- \- *lemma* multiplicative.is_subgroup
- \- *lemma* is_subgroup.coe_inv
- \- *lemma* is_subgroup.coe_gpow
- \- *lemma* is_add_subgroup.gsmul_coe
- \- *lemma* is_subgroup_Union_of_directed
- \- *lemma* is_subgroup.gpow_mem
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *lemma* gpowers_subset
- \- *lemma* gmultiples_subset
- \- *lemma* mem_gpowers
- \- *lemma* mem_gmultiples
- \- *lemma* inv_mem_iff
- \- *lemma* mul_mem_cancel_left
- \- *lemma* mul_mem_cancel_right
- \- *lemma* normal_subgroup_of_comm_group
- \- *lemma* additive.normal_add_subgroup
- \- *lemma* multiplicative.normal_subgroup
- \- *lemma* mem_norm_comm
- \- *lemma* mem_norm_comm_iff
- \- *lemma* mem_trivial
- \- *lemma* eq_trivial_iff
- \- *lemma* mem_center
- \- *lemma* subset_normalizer
- \- *lemma* one_ker_inv
- \- *lemma* one_ker_inv'
- \- *lemma* inv_ker_one
- \- *lemma* inv_ker_one'
- \- *lemma* one_iff_ker_inv
- \- *lemma* one_iff_ker_inv'
- \- *lemma* inv_iff_ker
- \- *lemma* inv_iff_ker'
- \- *lemma* inj_of_trivial_ker
- \- *lemma* trivial_ker_of_inj
- \- *lemma* inj_iff_trivial_ker
- \- *lemma* trivial_ker_iff_eq_one
- \- *lemma* closure_subset_iff
- \- *lemma* closure_subgroup
- \- *lemma* image_closure
- \- *lemma* trivial_eq_closure
- \- *lemma* mem_conjugates_self
- \- *lemma* mem_conjugates_of_set_iff
- \- *lemma* conjugates_subset
- \- *lemma* conj_mem_conjugates_of_set
- \- *lemma* normal_closure_subset_iff
- \- *lemma* simple_group_of_surjective
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *theorem* inv_mem
- \+ *theorem* coe_subtype
- \- *theorem* additive.is_add_subgroup_iff
- \- *theorem* multiplicative.is_subgroup_iff
- \- *theorem* is_subgroup.of_div
- \- *theorem* is_add_subgroup.of_sub
- \- *theorem* is_add_subgroup.sub_mem
- \- *theorem* additive.normal_add_subgroup_iff
- \- *theorem* multiplicative.normal_subgroup_iff
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* closure_mono
- \- *theorem* exists_list_of_mem_closure
- \- *theorem* mclosure_subset
- \- *theorem* mclosure_inv_subset
- \- *theorem* closure_eq_mclosure
- \- *theorem* mem_closure_union_iff
- \- *theorem* gpowers_eq_closure
- \- *theorem* subset_conjugates_of_set
- \- *theorem* conjugates_of_set_mono
- \- *theorem* conjugates_of_set_subset
- \- *theorem* conjugates_of_set_subset_normal_closure
- \- *theorem* subset_normal_closure
- \- *theorem* normal_closure_subset
- \- *theorem* normal_closure_mono
- \- *theorem* additive.simple_add_group_iff
- \- *theorem* multiplicative.simple_group_iff
- \+ *def* subgroup.to_add_subgroup
- \+ *def* subgroup.of_add_subgroup
- \+ *def* add_subgroup.to_subgroup
- \+ *def* add_subgroup.of_subgroup
- \+ *def* subgroup.add_subgroup_equiv
- \+ *def* subtype
- \+/\- *def* closure
- \+ *def* comap
- \+ *def* map
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* range
- \+/\- *def* ker
- \+ *def* eq_locus
- \+ *def* subgroup_congr
- \- *def* gpowers
- \- *def* gmultiples
- \- *def* trivial
- \- *def* center
- \- *def* normalizer
- \- *def* monoid_hom.range_subtype_val
- \- *def* monoid_hom.range_factorization
- \- *def* conjugates
- \- *def* conjugates_of_set
- \- *def* normal_closure

Modified src/group_theory/submonoid.lean
- \- *lemma* additive.is_add_submonoid
- \- *lemma* multiplicative.is_submonoid
- \- *lemma* is_submonoid_Union_of_directed
- \- *lemma* powers.one_mem
- \- *lemma* multiples.zero_mem
- \- *lemma* powers.self_mem
- \- *lemma* multiples.self_mem
- \- *lemma* powers.mul_mem
- \- *lemma* multiples.add_mem
- \- *lemma* image.is_submonoid
- \- *lemma* is_submonoid.pow_mem
- \- *lemma* is_add_submonoid.smul_mem
- \- *lemma* is_submonoid.power_subset
- \- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* list_prod_mem
- \- *lemma* multiset_prod_mem
- \- *lemma* finset_prod_mem
- \- *lemma* is_submonoid.coe_one
- \- *lemma* is_submonoid.coe_mul
- \- *lemma* is_submonoid.coe_pow
- \- *lemma* is_add_submonoid.smul_coe
- \- *lemma* image_closure
- \- *theorem* additive.is_add_submonoid_iff
- \- *theorem* multiplicative.is_submonoid_iff
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* closure_mono
- \- *theorem* closure_singleton
- \- *theorem* exists_list_of_mem_closure
- \- *theorem* mem_closure_union_iff
- \- *def* powers
- \- *def* multiples
- \- *def* closure
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
- \+ *lemma* smul_single'

Modified src/data/monoid_algebra.lean
- \+ *lemma* single_one_comm
- \+ *lemma* group_smul.linear_map_apply
- \+ *lemma* equivariant_of_linear_of_comm_apply
- \+ *def* group_smul.linear_map
- \+ *def* equivariant_of_linear_of_comm

Modified src/logic/embedding.lean
- \+ *lemma* mul_left_embedding_apply
- \+ *lemma* mul_right_embedding_apply
- \+ *def* mul_left_embedding
- \+ *def* mul_right_embedding

Created src/representation_theory/maschke.lean
- \+ *lemma* conjugate_i
- \+ *lemma* equivariant_projection_condition
- \+ *lemma* monoid_algebra.exists_left_inverse_of_injective
- \+ *lemma* monoid_algebra.submodule.exists_is_compl
- \+ *def* conjugate
- \+ *def* sum_of_conjugates
- \+ *def* sum_of_conjugates_equivariant
- \+ *def* equivariant_projection

Modified src/ring_theory/algebra.lean




## [2020-06-01 19:40:48](https://github.com/leanprover-community/mathlib/commit/085aade)
chore(linear_algebra/affine_space): use implicit args ([#2905](https://github.com/leanprover-community/mathlib/pull/2905))
Whenever we have an argument `f : affine_map k V P`, Lean can figure out `k`, `V`, and `P`.
#### Estimated changes
Modified src/linear_algebra/affine_space.lean
- \+ *lemma* coe_id
- \+/\- *lemma* id_apply
- \+ *lemma* coe_comp
- \+/\- *lemma* comp_apply



## [2020-06-01 17:01:58](https://github.com/leanprover-community/mathlib/commit/17296e9)
feat(category_theory/abelian): Schur's lemma ([#2838](https://github.com/leanprover-community/mathlib/pull/2838))
I wrote this mostly to gain some familiarity with @TwoFX's work on abelian categories from [#2817](https://github.com/leanprover-community/mathlib/pull/2817).
That all looked great, and Schur's lemma was pleasantly straightforward.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* epi_of_epi_image

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* eq_zero_of_epi_kernel
- \+ *lemma* kernel_not_epi_of_nonzero
- \+ *lemma* kernel_not_iso_of_nonzero
- \+/\- *lemma* kernel.ι_of_mono
- \+ *lemma* eq_zero_of_mono_cokernel
- \+ *lemma* cokernel_not_mono_of_nonzero
- \+ *lemma* cokernel_not_iso_of_nonzero
- \+/\- *lemma* cokernel.π_of_epi
- \+/\- *def* kernel.ι_zero_is_iso
- \+/\- *def* kernel.of_mono
- \+/\- *def* kernel.of_comp_iso
- \+/\- *def* kernel.iso_kernel
- \+/\- *def* kernel.ι_of_zero
- \+ *def* cokernel.π_zero_is_iso
- \+/\- *def* cokernel.of_epi
- \+/\- *def* cokernel.π_of_zero
- \+/\- *def* cokernel.of_iso_comp
- \+/\- *def* cokernel.cokernel_iso

Modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* eq_zero_of_image_eq_zero
- \+ *lemma* nonzero_image_of_nonzero
- \+ *lemma* to_zero_ext
- \+ *lemma* from_zero_ext

Modified src/category_theory/preadditive.lean
- \+ *lemma* mono_of_kernel_zero
- \+ *lemma* epi_of_cokernel_zero
- \+/\- *def* has_limit_parallel_pair
- \+/\- *def* has_colimit_parallel_pair

Created src/category_theory/schur.lean
- \+ *def* is_iso_of_hom_simple

Created src/category_theory/simple.lean
- \+ *lemma* simple.ext
- \+ *lemma* kernel_zero_of_nonzero_from_simple
- \+ *lemma* mono_to_simple_zero_of_not_iso
- \+ *lemma* zero_not_simple
- \+ *lemma* cokernel_zero_of_nonzero_to_simple
- \+ *lemma* epi_from_simple_zero_of_not_iso
- \+ *def* is_iso_of_mono_of_nonzero
- \+ *def* simple_of_cosimple
- \+ *def* is_iso_of_epi_of_nonzero



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
Created src/linear_algebra/affine_space.lean
- \+ *lemma* mem_span_points
- \+ *lemma* span_points_nonempty_of_nonempty
- \+ *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \+ *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \+ *lemma* mem_coe
- \+ *lemma* univ_coe
- \+ *lemma* mem_univ
- \+ *lemma* affine_span_coe
- \+ *lemma* affine_span_mem
- \+ *lemma* coe_mk
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_vadd
- \+ *lemma* map_vsub
- \+ *lemma* ext
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *def* vector_span
- \+ *def* span_points
- \+ *def* univ
- \+ *def* affine_span
- \+ *def* id
- \+ *def* comp



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
- \+/\- *lemma* is_lub_le_iff
- \+/\- *lemma* le_is_glb_iff

Modified src/order/complete_lattice.lean
- \- *lemma* ord_continuous.sup
- \- *lemma* ord_continuous.mono
- \- *def* ord_continuous

Created src/order/ord_continuous.lean
- \+ *lemma* map_is_greatest
- \+ *lemma* mono
- \+ *lemma* comp
- \+ *lemma* map_sup
- \+ *lemma* le_iff
- \+ *lemma* lt_iff
- \+ *lemma* coe_to_le_order_embedding
- \+ *lemma* coe_to_lt_order_embedding
- \+ *lemma* map_Sup'
- \+ *lemma* map_Sup
- \+ *lemma* map_supr
- \+ *lemma* map_cSup
- \+ *lemma* map_csupr
- \+ *lemma* map_is_least
- \+ *lemma* map_inf
- \+ *lemma* map_Inf'
- \+ *lemma* map_Inf
- \+ *lemma* map_infi
- \+ *lemma* map_cInf
- \+ *lemma* map_cinfi
- \+ *def* left_ord_continuous
- \+ *def* right_ord_continuous
- \+ *def* to_le_order_embedding
- \+ *def* to_lt_order_embedding



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
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* mul_apply
- \+ *lemma* inv_apply_self
- \+ *lemma* apply_inv_self
- \- *lemma* to_equiv_to_fun
- \+ *theorem* to_equiv_injective
- \+/\- *theorem* coe_fn_injective
- \+ *theorem* ext
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+ *theorem* rel_symm_apply
- \+ *theorem* symm_apply_rel
- \+ *def* rsymm
- \- *def* preimage

Modified src/set_theory/ordinal.lean




## [2020-06-01 01:58:08](https://github.com/leanprover-community/mathlib/commit/73f95a7)
chore(algebra/group): move defs to `defs.lean` ([#2885](https://github.com/leanprover-community/mathlib/pull/2885))
Also delete the aliases `eq_of_add_eq_add_left` and `eq_of_add_eq_add_right`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \- *lemma* mul_assoc
- \- *lemma* mul_comm
- \- *lemma* mul_left_cancel
- \- *lemma* mul_left_cancel_iff
- \- *lemma* mul_right_cancel
- \- *lemma* mul_right_cancel_iff
- \- *lemma* one_mul
- \- *lemma* mul_one
- \- *lemma* left_inv_eq_right_inv
- \- *lemma* mul_left_inv
- \- *lemma* inv_mul_cancel_left
- \- *lemma* inv_eq_of_mul_eq_one
- \- *lemma* inv_inv
- \- *lemma* mul_right_inv
- \- *lemma* group.mul_left_cancel
- \- *lemma* group.mul_right_cancel
- \- *lemma* mul_inv_cancel_right
- \- *lemma* sub_eq_add_neg
- \- *theorem* mul_right_injective
- \- *theorem* mul_right_inj
- \- *theorem* mul_left_injective
- \- *theorem* mul_left_inj
- \- *def* eq_of_add_eq_add_left
- \- *def* eq_of_add_eq_add_right
- \- *def* inv_mul_self
- \- *def* mul_inv_self

Created src/algebra/group/defs.lean
- \+ *lemma* mul_assoc
- \+ *lemma* mul_comm
- \+ *lemma* mul_left_cancel
- \+ *lemma* mul_left_cancel_iff
- \+ *lemma* mul_right_cancel
- \+ *lemma* mul_right_cancel_iff
- \+ *lemma* one_mul
- \+ *lemma* mul_one
- \+ *lemma* left_inv_eq_right_inv
- \+ *lemma* mul_left_inv
- \+ *lemma* inv_mul_self
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* inv_eq_of_mul_eq_one
- \+ *lemma* inv_inv
- \+ *lemma* mul_right_inv
- \+ *lemma* mul_inv_self
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* sub_eq_add_neg
- \+ *theorem* mul_right_injective
- \+ *theorem* mul_right_inj
- \+ *theorem* mul_left_injective
- \+ *theorem* mul_left_inj

Modified src/set_theory/ordinal.lean


Modified src/topology/algebra/uniform_group.lean


