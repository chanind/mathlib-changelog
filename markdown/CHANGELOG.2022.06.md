## [2022-06-30 21:59:47](https://github.com/leanprover-community/mathlib/commit/9229b0e)
chore(data/nat/factorization/basic): delete `import tactic.linarith` ([#15075](https://github.com/leanprover-community/mathlib/pull/15075))
Removes the import of `tactic.linarith` that's no longer needed.
#### Estimated changes
modified src/data/nat/factorization/basic.lean



## [2022-06-30 21:59:46](https://github.com/leanprover-community/mathlib/commit/e7425e7)
feat(data/fin/basic): `induction_zero` and `induction_succ` lemmas ([#15060](https://github.com/leanprover-community/mathlib/pull/15060))
This pull request introduces `fin.induction_zero` and `fin.induction_succ` simp lemmas for `fin.induction`, similar to `fin.cases_zero` and `fin.cases_succ` for `fin.cases`.
#### Estimated changes
modified src/data/fin/basic.lean
- \+ *lemma* induction_zero
- \+ *lemma* induction_succ



## [2022-06-30 19:45:49](https://github.com/leanprover-community/mathlib/commit/806bbb0)
refactor(algebra/group/defs): rename has_scalar to has_smul ([#14559](https://github.com/leanprover-community/mathlib/pull/14559))
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy
#### Estimated changes
modified scripts/nolints.txt

modified src/algebra/algebra/basic.lean
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_smul_of_tower

modified src/algebra/algebra/subalgebra/basic.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_algebra_map
- \+/\- *lemma* smul_def
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_algebra_map
- \+/\- *lemma* smul_def

modified src/algebra/algebra/tower.lean

modified src/algebra/algebra/unitization.lean
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inl_smul
- \+/\- *lemma* coe_smul
- \+/\- *lemma* fst_mul
- \+/\- *lemma* snd_mul
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inl_smul
- \+/\- *lemma* coe_smul
- \+/\- *lemma* fst_mul
- \+/\- *lemma* snd_mul

modified src/algebra/category/Module/filtered_colimits.lean

modified src/algebra/direct_sum/module.lean

modified src/algebra/direct_sum/ring.lean

modified src/algebra/field/basic.lean

modified src/algebra/free_algebra.lean
- \+ *def* has_smul
- \- *def* has_scalar

modified src/algebra/graded_monoid.lean

modified src/algebra/group/defs.lean

modified src/algebra/group/inj_surj.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* smul_mk0
- \+/\- *lemma* smul_mk0

modified src/algebra/hom/group_action.lean

modified src/algebra/homology/additive.lean

modified src/algebra/lie/basic.lean

modified src/algebra/lie/free.lean

modified src/algebra/lie/quotient.lean

modified src/algebra/lie/subalgebra.lean

modified src/algebra/lie/submodule.lean

modified src/algebra/module/basic.lean

modified src/algebra/module/hom.lean

modified src/algebra/module/linear_map.lean
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_smul_of_tower

modified src/algebra/module/pi.lean
- \+/\- *lemma* _root_.is_smul_regular.pi
- \+/\- *lemma* _root_.is_smul_regular.pi

modified src/algebra/module/pointwise_pi.lean
- \+/\- *lemma* smul_pi_subset
- \+/\- *lemma* smul_univ_pi
- \+/\- *lemma* smul_pi_subset
- \+/\- *lemma* smul_univ_pi

modified src/algebra/module/prod.lean

modified src/algebra/module/submodule/basic.lean
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* coe_smul_of_tower
- \+/\- *lemma* smul_of_tower_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* coe_smul_of_tower

modified src/algebra/module/submodule/lattice.lean

modified src/algebra/module/torsion.lean
- \+/\- *def* is_torsion'
- \+ *def* is_torsion_by_set.has_smul
- \+/\- *def* is_torsion'
- \- *def* is_torsion_by_set.has_scalar

modified src/algebra/module/ulift.lean
- \+/\- *lemma* smul_down
- \+/\- *lemma* smul_down'
- \+/\- *lemma* smul_down
- \+/\- *lemma* smul_down'

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/opposites.lean
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul
- \+/\- *lemma* op_smul
- \+/\- *lemma* unop_smul

modified src/algebra/order/field.lean

modified src/algebra/order/module.lean
- \+/\- *lemma* antitone_smul_left
- \+/\- *lemma* strict_anti_smul_left
- \+/\- *lemma* antitone_smul_left
- \+/\- *lemma* strict_anti_smul_left

modified src/algebra/order/nonneg.lean

modified src/algebra/order/ring.lean

modified src/algebra/order/smul.lean
- \+/\- *lemma* to_dual_smul
- \+/\- *lemma* of_dual_smul
- \+/\- *lemma* monotone_smul_left
- \+/\- *lemma* strict_mono_smul_left
- \+/\- *lemma* to_dual_smul
- \+/\- *lemma* of_dual_smul
- \+/\- *lemma* monotone_smul_left
- \+/\- *lemma* strict_mono_smul_left

modified src/algebra/periodic.lean
- \+/\- *lemma* periodic.smul
- \+/\- *lemma* periodic.smul

modified src/algebra/punit_instances.lean

modified src/algebra/regular/smul.lean
- \+/\- *def* is_smul_regular
- \+/\- *def* is_smul_regular

modified src/algebra/ring/basic.lean

modified src/algebra/ring_quot.lean

modified src/algebra/smul_with_zero.lean

modified src/algebra/star/basic.lean

modified src/algebra/star/pi.lean

modified src/algebra/star/prod.lean

modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* smul_mem
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_mem
- \+/\- *lemma* coe_smul

modified src/algebra/symmetrized.lean
- \+/\- *lemma* sym_smul
- \+/\- *lemma* unsym_smul
- \+/\- *lemma* sym_smul
- \+/\- *lemma* unsym_smul

modified src/algebra/triv_sq_zero_ext.lean
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inl_smul
- \+/\- *lemma* inr_smul
- \+/\- *lemma* fst_mul
- \+/\- *lemma* snd_mul
- \+/\- *lemma* fst_smul
- \+/\- *lemma* snd_smul
- \+/\- *lemma* inl_smul
- \+/\- *lemma* inr_smul
- \+/\- *lemma* fst_mul
- \+/\- *lemma* snd_mul

modified src/algebra/tropical/basic.lean
- \+/\- *lemma* untrop_pow
- \+/\- *lemma* trop_smul
- \+/\- *lemma* untrop_pow
- \+/\- *lemma* trop_smul

modified src/analysis/box_integral/partition/additive.lean

modified src/analysis/calculus/fderiv_symmetric.lean

modified src/analysis/calculus/formal_multilinear_series.lean

modified src/analysis/complex/upper_half_plane/basic.lean

modified src/analysis/convex/basic.lean

modified src/analysis/convex/cone.lean

modified src/analysis/convex/extreme.lean

modified src/analysis/convex/function.lean

modified src/analysis/convex/quasiconvex.lean

modified src/analysis/convex/star.lean

modified src/analysis/convex/strict.lean

modified src/analysis/locally_convex/balanced_core_hull.lean

modified src/analysis/locally_convex/basic.lean

modified src/analysis/locally_convex/bounded.lean

modified src/analysis/normed/group/hom.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/lp_space.lean

modified src/analysis/seminorm.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_sup
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_sup
- \+/\- *lemma* smul_inf
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_sup
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_sup
- \+/\- *lemma* smul_inf

modified src/data/bracket.lean

modified src/data/complex/module.lean

modified src/data/dfinsupp/basic.lean

modified src/data/fin/vec_notation.lean

modified src/data/finset/pointwise.lean

modified src/data/finsupp/basic.lean
- \+ *def* comap_has_smul
- \- *def* comap_has_scalar

modified src/data/finsupp/pointwise.lean

modified src/data/finsupp/to_dfinsupp.lean

modified src/data/holor.lean

modified src/data/matrix/basic.lean
- \+/\- *lemma* map_smul
- \+/\- *lemma* _root_.is_smul_regular.matrix
- \+/\- *lemma* transpose_smul
- \+/\- *lemma* conj_transpose_smul
- \+/\- *lemma* minor_smul
- \+/\- *lemma* col_smul
- \+/\- *lemma* row_smul
- \+/\- *lemma* map_smul
- \+/\- *lemma* _root_.is_smul_regular.matrix
- \+/\- *lemma* transpose_smul
- \+/\- *lemma* conj_transpose_smul
- \+/\- *lemma* minor_smul
- \+/\- *lemma* col_smul
- \+/\- *lemma* row_smul
- \+/\- *theorem* diag_smul
- \+/\- *theorem* diag_smul

modified src/data/matrix/block.lean
- \+/\- *lemma* from_blocks_smul
- \+/\- *lemma* from_blocks_smul

modified src/data/matrix/hadamard.lean
- \+/\- *lemma* smul_hadamard
- \+/\- *lemma* hadamard_smul
- \+/\- *lemma* smul_hadamard
- \+/\- *lemma* hadamard_smul

modified src/data/matrix/kronecker.lean
- \+/\- *lemma* kronecker_map_smul_left
- \+/\- *lemma* kronecker_map_smul_right
- \+/\- *lemma* kronecker_map_smul_left
- \+/\- *lemma* kronecker_map_smul_right

modified src/data/matrix/notation.lean
- \+/\- *lemma* smul_vec2
- \+/\- *lemma* smul_vec3
- \+/\- *lemma* smul_vec2
- \+/\- *lemma* smul_vec3

modified src/data/mv_polynomial/basic.lean

modified src/data/polynomial/basic.lean

modified src/data/polynomial/laurent.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul

modified src/data/real/nnreal.lean

modified src/data/set/pointwise.lean
- \+/\- *lemma* image2_smul
- \+/\- *lemma* smul_set_range
- \+/\- *lemma* image2_smul
- \+/\- *lemma* smul_set_range
- \+/\- *theorem* range_smul_range
- \+/\- *theorem* range_smul_range

modified src/field_theory/intermediate_field.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul

modified src/field_theory/ratfunc.lean
- \+/\- *lemma* of_fraction_ring_smul
- \+/\- *lemma* to_fraction_ring_smul
- \+/\- *lemma* of_fraction_ring_smul
- \+/\- *lemma* to_fraction_ring_smul

modified src/field_theory/splitting_field.lean

modified src/geometry/manifold/algebra/left_invariant_derivation.lean

modified src/geometry/manifold/algebra/smooth_functions.lean

modified src/geometry/manifold/derivation_bundle.lean

modified src/group_theory/congruence.lean

modified src/group_theory/group_action/conj_act.lean

modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* smul_left_injective'
- \+/\- *lemma* smul_comm_class.symm
- \+/\- *lemma* smul_assoc
- \+/\- *lemma* is_central_scalar.unop_smul_eq_smul
- \+/\- *lemma* comp.is_scalar_tower
- \+/\- *lemma* comp.smul_comm_class
- \+/\- *lemma* comp.smul_comm_class'
- \+/\- *lemma* mul_smul_comm
- \+/\- *lemma* smul_mul_assoc
- \+/\- *lemma* smul_smul_smul_comm
- \+/\- *lemma* smul_one_smul
- \+/\- *lemma* smul_one_mul
- \+/\- *lemma* is_scalar_tower.of_smul_one_mul
- \+/\- *lemma* smul_comm_class.of_mul_smul_one
- \+/\- *lemma* smul_left_injective'
- \+/\- *lemma* smul_comm_class.symm
- \+/\- *lemma* smul_assoc
- \+/\- *lemma* is_central_scalar.unop_smul_eq_smul
- \+/\- *lemma* comp.is_scalar_tower
- \+/\- *lemma* comp.smul_comm_class
- \+/\- *lemma* comp.smul_comm_class'
- \+/\- *lemma* mul_smul_comm
- \+/\- *lemma* smul_mul_assoc
- \+/\- *lemma* smul_smul_smul_comm
- \+/\- *lemma* smul_one_smul
- \+/\- *lemma* smul_one_mul
- \+/\- *lemma* is_scalar_tower.of_smul_one_mul
- \+/\- *lemma* smul_comm_class.of_mul_smul_one
- \+/\- *def* comp
- \+/\- *def* comp

modified src/group_theory/group_action/embedding.lean

modified src/group_theory/group_action/opposite.lean
- \+/\- *lemma* op_smul_eq_op_smul_op
- \+/\- *lemma* unop_smul_eq_unop_smul_unop
- \+/\- *lemma* op_smul_eq_op_smul_op
- \+/\- *lemma* unop_smul_eq_unop_smul_unop

modified src/group_theory/group_action/pi.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply'
- \+/\- *lemma* update_smul
- \+/\- *lemma* piecewise_smul
- \+/\- *lemma* function.extend_smul
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply'
- \+/\- *lemma* update_smul
- \+/\- *lemma* piecewise_smul
- \+/\- *lemma* function.extend_smul

modified src/group_theory/group_action/prod.lean

modified src/group_theory/group_action/sigma.lean

modified src/group_theory/group_action/sub_mul_action.lean
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* smul_mem_iff'

modified src/group_theory/group_action/sum.lean

modified src/group_theory/group_action/units.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_is_unit
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_is_unit

modified src/group_theory/monoid_localization.lean
- \+/\- *lemma* smul_mk
- \+/\- *lemma* smul_mk

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/linear_algebra/affine_space/affine_map.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/basis.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/linear_pmap.lean

modified src/linear_algebra/matrix/circulant.lean
- \+/\- *lemma* circulant_smul
- \+/\- *lemma* circulant_smul

modified src/linear_algebra/matrix/symmetric.lean
- \+/\- *lemma* is_symm.smul
- \+/\- *lemma* is_symm.smul

modified src/linear_algebra/multilinear/basic.lean

modified src/linear_algebra/pi_tensor_product.lean

modified src/linear_algebra/quadratic_form/basic.lean

modified src/linear_algebra/quotient.lean
- \+/\- *def* restrict_scalars_equiv
- \+/\- *def* restrict_scalars_equiv

modified src/linear_algebra/span.lean
- \+/\- *lemma* span_singleton_smul_le
- \+/\- *lemma* span_singleton_group_smul_eq
- \+/\- *lemma* span_le_restrict_scalars
- \+/\- *lemma* span_subset_span
- \+/\- *lemma* span_span_of_tower
- \+/\- *lemma* span_singleton_smul_le
- \+/\- *lemma* span_singleton_group_smul_eq
- \+/\- *lemma* span_le_restrict_scalars
- \+/\- *lemma* span_subset_span
- \+/\- *lemma* span_span_of_tower

modified src/linear_algebra/tensor_product.lean
- \+/\- *theorem* smul.aux_of
- \+/\- *theorem* smul.aux_of
- \+/\- *def* smul.aux
- \+/\- *def* smul.aux

modified src/logic/equiv/transfer_instance.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/function/ae_eq_fun.lean

modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *lemma* const_smul
- \+/\- *lemma* const_smul

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/function/simple_func_dense_lp.lean

modified src/measure_theory/function/strongly_measurable.lean

modified src/measure_theory/group/action.lean

modified src/measure_theory/group/arithmetic.lean

modified src/measure_theory/group/fundamental_domain.lean

modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_eq_map
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_eq_map

modified src/measure_theory/measure/finite_measure_weak_convergence.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean
- \+/\- *theorem* smul_supr
- \+/\- *theorem* trim_smul
- \+/\- *theorem* smul_supr
- \+/\- *theorem* trim_smul

modified src/measure_theory/measure/vector_measure.lean

modified src/number_theory/arithmetic_function.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* eventually_eq.const_smul
- \+/\- *lemma* eventually_eq.smul
- \+/\- *lemma* eventually_eq.const_smul
- \+/\- *lemma* eventually_eq.smul

modified src/order/filter/germ.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul'

modified src/order/filter/pointwise.lean

modified src/probability/stopping.lean
- \+/\- *lemma* smul
- \+/\- *lemma* smul

modified src/ring_theory/adjoin/basic.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebraic.lean
- \+/\- *lemma* polynomial_smul_apply
- \+/\- *lemma* polynomial_smul_apply
- \+ *def* polynomial.has_smul_pi
- \- *def* polynomial.has_scalar_pi

modified src/ring_theory/derivation.lean
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_smul_of_tower

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/graded_algebra/homogeneous_localization.lean

modified src/ring_theory/hahn_series.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/localization/integer.lean

modified src/ring_theory/localization/localization_localization.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/subring/basic.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/ring_theory/subsemiring/basic.lean
- \+/\- *lemma* smul_def
- \+/\- *lemma* smul_def

modified src/ring_theory/witt_vector/defs.lean

modified src/ring_theory/witt_vector/truncated.lean

modified src/tactic/abel.lean

modified src/topology/algebra/const_mul_action.lean

modified src/topology/algebra/continuous_affine_map.lean

modified src/topology/algebra/module/basic.lean
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* map_smul_of_tower

modified src/topology/algebra/module/multilinear.lean

modified src/topology/algebra/module/weak_dual.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/mul_action.lean

modified src/topology/algebra/uniform_mul_action.lean

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_comp
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_comp

modified src/topology/continuous_function/bounded.lean

modified src/topology/continuous_function/zero_at_infty.lean

modified src/topology/instances/matrix.lean

modified src/topology/locally_constant/algebra.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply

modified src/topology/metric_space/algebra.lean

modified test/has_scalar_comp_loop.lean
- \+/\- *def* foo
- \+/\- *def* foo

modified test/instance_diamonds.lean

modified test/to_additive.lean



## [2022-06-30 17:18:22](https://github.com/leanprover-community/mathlib/commit/c10efa6)
refactor(algebra/hom/group): generalize basic API of `monoid_hom` to `monoid_hom_class` ([#14997](https://github.com/leanprover-community/mathlib/pull/14997))
This PR generalizes part of the basic API of monoid homs to monoid_hom_class. This notably includes things like monoid_hom.mker, submonoid.map and submonoid.comap. I left the namespaces unchanged, for example `monoid_hom.mker` remains the same even though it is now defined for any `monoid_hom_class` morphism; this way dot notation still (mostly) works for actual monoid homs.
#### Estimated changes
modified src/algebra/algebra/operations.lean

modified src/algebra/hom/group.lean

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/membership.lean
- \+/\- *lemma* map_powers
- \+/\- *lemma* map_powers

modified src/group_theory/submonoid/operations.lean
- \+/\- *lemma* coe_comap
- \+/\- *lemma* mem_comap
- \+/\- *lemma* comap_id
- \+/\- *lemma* coe_map
- \+/\- *lemma* mem_map
- \+/\- *lemma* mem_map_of_mem
- \+/\- *lemma* apply_coe_mem_map
- \+/\- *lemma* mem_map_iff_mem
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* gc_map_comap
- \+/\- *lemma* map_le_of_le_comap
- \+/\- *lemma* le_comap_of_map_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* monotone_map
- \+/\- *lemma* monotone_comap
- \+/\- *lemma* map_comap_map
- \+/\- *lemma* comap_map_comap
- \+/\- *lemma* map_sup
- \+/\- *lemma* map_supr
- \+/\- *lemma* comap_inf
- \+/\- *lemma* comap_infi
- \+/\- *lemma* map_bot
- \+/\- *lemma* comap_top
- \+/\- *lemma* coe_mrange
- \+/\- *lemma* mem_mrange
- \+/\- *lemma* mrange_eq_map
- \+/\- *lemma* mrange_top_iff_surjective
- \+/\- *lemma* mrange_top_of_surjective
- \+/\- *lemma* mclosure_preimage_le
- \+/\- *lemma* map_mclosure
- \+/\- *lemma* mem_mker
- \+/\- *lemma* coe_mker
- \+/\- *lemma* comap_bot'
- \+/\- *lemma* coe_comap
- \+/\- *lemma* mem_comap
- \+/\- *lemma* comap_id
- \+/\- *lemma* coe_map
- \+/\- *lemma* mem_map
- \+/\- *lemma* mem_map_of_mem
- \+/\- *lemma* apply_coe_mem_map
- \+/\- *lemma* mem_map_iff_mem
- \+/\- *lemma* map_le_iff_le_comap
- \+/\- *lemma* gc_map_comap
- \+/\- *lemma* map_le_of_le_comap
- \+/\- *lemma* le_comap_of_map_le
- \+/\- *lemma* le_comap_map
- \+/\- *lemma* map_comap_le
- \+/\- *lemma* monotone_map
- \+/\- *lemma* monotone_comap
- \+/\- *lemma* map_comap_map
- \+/\- *lemma* comap_map_comap
- \+/\- *lemma* map_sup
- \+/\- *lemma* map_supr
- \+/\- *lemma* comap_inf
- \+/\- *lemma* comap_infi
- \+/\- *lemma* map_bot
- \+/\- *lemma* comap_top
- \+/\- *lemma* coe_mrange
- \+/\- *lemma* mem_mrange
- \+/\- *lemma* mrange_eq_map
- \+/\- *lemma* mrange_top_iff_surjective
- \+/\- *lemma* mrange_top_of_surjective
- \+/\- *lemma* mclosure_preimage_le
- \+/\- *lemma* map_mclosure
- \+/\- *lemma* mem_mker
- \+/\- *lemma* coe_mker
- \+/\- *lemma* comap_bot'
- \+/\- *def* comap
- \+/\- *def* map
- \+/\- *def* mrange
- \+/\- *def* mker
- \+/\- *def* comap
- \+/\- *def* map
- \+/\- *def* mrange
- \+/\- *def* mker

modified src/group_theory/submonoid/pointwise.lean

modified src/linear_algebra/basic.lean
- \+ *lemma* map_to_add_submonoid'

modified src/ring_theory/finiteness.lean

modified src/ring_theory/local_properties.lean

modified src/ring_theory/localization/integral.lean

modified src/ring_theory/localization/localization_localization.lean

modified src/ring_theory/non_zero_divisors.lean



## [2022-06-30 12:40:15](https://github.com/leanprover-community/mathlib/commit/eb85260)
feat(topology/compact_open):  continuous_comp left functor C(-, γ) ([#15068](https://github.com/leanprover-community/mathlib/pull/15068))
#### Estimated changes
modified src/topology/compact_open.lean
- \+ *lemma* continuous_comp_left



## [2022-06-30 06:53:03](https://github.com/leanprover-community/mathlib/commit/050f9e6)
feat(number_theory/legendre_symbol/mul_character): alternative implementation ([#14768](https://github.com/leanprover-community/mathlib/pull/14768))
This is an alternative version of `number_theory/legendre_symbol/mul_character.lean`.
It defines `mul_character R R'` as a `monoid_hom` that sends non-units to zero.
This allows to define a `comm_group` structure on `mul_character R R'`.
There is an alternative implementation in [#14716](https://github.com/leanprover-community/mathlib/pull/14716) ([side by side comparison](https://github.com/leanprover-community/mathlib/compare/legendre_symbol_mul_char...variant)).
See the [discussion on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Implementation.20of.20multiplicative.20characters).
#### Estimated changes
created src/number_theory/legendre_symbol/mul_character.lean
- \+ *lemma* coe_coe
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* ext'
- \+ *lemma* map_nonunit
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coe_to_unit_hom
- \+ *lemma* of_unit_hom_coe
- \+ *lemma* to_unit_hom_eq
- \+ *lemma* of_unit_hom_eq
- \+ *lemma* coe_equiv_to_unit_hom
- \+ *lemma* equiv_unit_hom_symm_coe
- \+ *lemma* map_one
- \+ *lemma* map_zero
- \+ *lemma* one_apply_coe
- \+ *lemma* mul_apply
- \+ *lemma* coe_to_fun_mul
- \+ *lemma* one_mul
- \+ *lemma* mul_one
- \+ *lemma* inv_apply_eq_inv
- \+ *lemma* inv_apply_eq_inv'
- \+ *lemma* inv_apply
- \+ *lemma* inv_apply'
- \+ *lemma* inv_mul
- \+ *lemma* pow_apply_coe
- \+ *lemma* pow_apply'
- \+ *lemma* is_nontrivial_iff
- \+ *lemma* is_nontrivial.comp
- \+ *lemma* is_quadratic.comp
- \+ *lemma* is_quadratic.inv
- \+ *lemma* is_quadratic.sq_eq_one
- \+ *lemma* is_quadratic.pow_char
- \+ *lemma* is_quadratic.pow_even
- \+ *lemma* is_quadratic.pow_odd
- \+ *lemma* is_nontrivial.sum_eq_zero
- \+ *lemma* sum_one_eq_card_units
- \+ *def* trivial
- \+ *def* to_unit_hom
- \+ *def* of_unit_hom
- \+ *def* equiv_to_unit_hom
- \+ *def* mul
- \+ *def* inv
- \+ *def* is_nontrivial
- \+ *def* is_quadratic
- \+ *def* ring_hom_comp



## [2022-06-30 04:08:55](https://github.com/leanprover-community/mathlib/commit/ad154bd)
chore(scripts): update nolints.txt ([#15063](https://github.com/leanprover-community/mathlib/pull/15063))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2022-06-29 23:58:49](https://github.com/leanprover-community/mathlib/commit/5d8810a)
feat(set_theory/cardinal/*): simp lemmas for `to_nat` and `to_enat` ([#15059](https://github.com/leanprover-community/mathlib/pull/15059))
#### Estimated changes
modified src/set_theory/cardinal/basic.lean
- \+ *theorem* aleph_0_to_nat
- \+ *theorem* aleph_0_to_enat

modified src/set_theory/cardinal/continuum.lean
- \+ *theorem* continuum_to_nat
- \+ *theorem* continuum_to_enat

modified src/set_theory/cardinal/ordinal.lean
- \+ *theorem* aleph_to_nat
- \+ *theorem* aleph_to_enat



## [2022-06-29 23:58:48](https://github.com/leanprover-community/mathlib/commit/68452ec)
feat(set_theory/game/pgame): golf `le_trans`  ([#14956](https://github.com/leanprover-community/mathlib/pull/14956))
This also adds `has_le.le.move_left_lf` and `has_le.le.lf_move_right` to enable dot notation. Note that we already have other pgame lemmas in the `has_le.le` namespace like `has_le.le.not_gf`.
To make this dot notation work even when these lemmas are partially-applied, we swap the arguments of `move_left_lf_of_le` and `lf_move_right_of_le`.
#### Estimated changes
modified src/set_theory/game/impartial.lean

modified src/set_theory/game/pgame.lean
- \+/\- *theorem* move_left_lf_of_le
- \+/\- *theorem* lf_move_right_of_le
- \+/\- *theorem* lf_of_le_mk
- \+/\- *theorem* lf_of_mk_le
- \+/\- *theorem* move_left_lf
- \+/\- *theorem* lf_move_right
- \+/\- *theorem* move_left_lf_of_le
- \+/\- *theorem* lf_move_right_of_le
- \+/\- *theorem* lf_of_le_mk
- \+/\- *theorem* lf_of_mk_le
- \+/\- *theorem* move_left_lf
- \+/\- *theorem* lf_move_right

modified src/set_theory/surreal/basic.lean



## [2022-06-29 22:22:06](https://github.com/leanprover-community/mathlib/commit/501c1d4)
feat(linear_algebra/linear_pmap): add has_smul and ext ([#14915](https://github.com/leanprover-community/mathlib/pull/14915))
Adds the type-class `has_smul` for partially defined linear maps. We proof the ext lemma.
#### Estimated changes
modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* ext
- \+ *lemma* smul_apply
- \+ *lemma* coe_smul



## [2022-06-29 22:22:05](https://github.com/leanprover-community/mathlib/commit/a2a8c9b)
refactor(ring_theory/graded_algebra): use `add_submonoid_class` to generalize to graded rings ([#14583](https://github.com/leanprover-community/mathlib/pull/14583))
Now that we have `add_submonoid_class`, we don't need to consider only families of submodules.
For convenience, this keeps around `graded_algebra` as an alias for `graded_ring` over a family of submodules, as this can help with elaboration here and there.
This renames:
* `graded_algebra` to `graded_ring`
* `graded_algebra.proj_zero_ring_hom` to `graded_ring.proj_zero_ring_hom`
adds:
* `direct_sum.decompose_ring_equiv`
* `graded_ring.proj`
* `graded_algebra` (as an alias for a suitable `graded_ring`
and removes:
* `graded_algebra.is_internal`, which was just an alias anyway.
#### Estimated changes
modified src/algebra/direct_sum/internal.lean
- \+/\- *lemma* direct_sum.coe_ring_hom_of
- \+/\- *lemma* direct_sum.coe_ring_hom_of

modified src/linear_algebra/clifford_algebra/grading.lean

modified src/ring_theory/graded_algebra/basic.lean
- \+/\- *lemma* decompose_one
- \+/\- *lemma* decompose_symm_one
- \+/\- *lemma* decompose_mul
- \+/\- *lemma* decompose_symm_mul
- \+ *lemma* graded_ring.proj_apply
- \+ *lemma* graded_ring.proj_recompose
- \+ *lemma* graded_ring.mem_support_iff
- \+/\- *lemma* decompose_one
- \+/\- *lemma* decompose_symm_one
- \+/\- *lemma* decompose_mul
- \+/\- *lemma* decompose_symm_mul
- \+ *def* decompose_ring_equiv
- \+ *def* graded_ring.proj
- \+ *def* graded_algebra
- \+ *def* graded_ring.proj_zero_ring_hom
- \- *def* graded_algebra.proj_zero_ring_hom

modified src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+/\- *def* ideal.homogeneous_core'
- \+/\- *def* ideal.homogeneous_core'

modified src/ring_theory/graded_algebra/radical.lean



## [2022-06-29 20:39:00](https://github.com/leanprover-community/mathlib/commit/1116684)
chore(set_theory/game/pgame): golf various theorems about relabellings ([#15054](https://github.com/leanprover-community/mathlib/pull/15054))
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/pgame.lean
- \+ *theorem* le
- \+ *theorem* ge
- \+ *theorem* equiv
- \- *theorem* relabelling.le
- \- *theorem* relabelling.ge
- \- *theorem* relabelling.equiv
- \+/\- *def* restricted.trans
- \+ *def* restricted
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* is_empty
- \+/\- *def* restricted.trans
- \- *def* relabelling.restricted
- \- *def* relabelling.refl
- \- *def* relabelling.symm
- \- *def* relabelling.trans
- \- *def* relabelling.is_empty



## [2022-06-29 20:38:59](https://github.com/leanprover-community/mathlib/commit/108e3a0)
refactor(group_theory/coset): redefine quotient group to be quotient by action of subgroup ([#15045](https://github.com/leanprover-community/mathlib/pull/15045))
Given a group `α` and subgroup `s`, redefine the relation `left_rel` ("being in the same left coset") to
```lean
def left_rel : setoid α := mul_action.orbit_rel s.opposite α
```
This means that a quotient group is definitionally a quotient by a group action.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/two.20different.20quotients.20by.20subgroup)
#### Estimated changes
modified src/algebra/category/Group/colimits.lean

modified src/algebra/module/torsion.lean

modified src/algebra/periodic.lean

modified src/analysis/special_functions/trigonometric/angle.lean

modified src/data/zmod/quotient.lean

modified src/group_theory/abelianization.lean

modified src/group_theory/complement.lean

modified src/group_theory/coset.lean
- \+ *lemma* left_rel_apply
- \+ *lemma* left_rel_eq
- \+ *lemma* right_rel_apply
- \+ *lemma* right_rel_eq
- \+/\- *def* left_rel
- \+/\- *def* right_rel
- \+/\- *def* left_rel
- \+/\- *def* right_rel

modified src/group_theory/double_coset.lean

modified src/group_theory/group_action/quotient.lean

modified src/group_theory/index.lean

modified src/group_theory/quotient_group.lean
- \+ *lemma* mk'_eq_mk'

modified src/group_theory/sylow.lean

modified src/group_theory/transfer.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/quotient.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/class_group.lean
- \- *lemma* quotient_group.mk'_eq_mk'

modified src/ring_theory/ideal/quotient.lean

modified src/ring_theory/valuation/basic.lean



## [2022-06-29 20:38:58](https://github.com/leanprover-community/mathlib/commit/71985dc)
feat(field_theory/minpoly): generalize statements about GCD domains ([#14979](https://github.com/leanprover-community/mathlib/pull/14979))
Currently, the statements about the minimal polynomial over a GCD domain `R` require the element to be in a `K`-algebra, where `K` is the fraction field of `R`. We remove this assumption.
From flt-regular.
#### Estimated changes
modified src/field_theory/minpoly.lean
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+ *lemma* gcd_domain_eq_field_fractions'
- \+/\- *lemma* gcd_domain_dvd
- \+ *lemma* gcd_domain_degree_le_of_ne_zero
- \+ *lemma* gcd_domain_unique
- \+/\- *lemma* gcd_domain_eq_field_fractions
- \+/\- *lemma* gcd_domain_dvd

modified src/number_theory/cyclotomic/discriminant.lean

modified src/number_theory/cyclotomic/rat.lean

modified src/ring_theory/polynomial/content.lean
- \+ *lemma* aeval_prim_part_eq_zero
- \+ *lemma* eval₂_prim_part_eq_zero

modified src/ring_theory/polynomial/cyclotomic/basic.lean

modified src/ring_theory/polynomial/eisenstein.lean

modified src/ring_theory/roots_of_unity.lean



## [2022-06-29 20:38:57](https://github.com/leanprover-community/mathlib/commit/6879dd0)
feat(model_theory/satisfiability): The Łoś–Vaught Test ([#14758](https://github.com/leanprover-community/mathlib/pull/14758))
Provides more API for elementary equivalence
Shows that a `κ`-categorical theory with only infinite models is complete.
#### Estimated changes
modified docs/overview.yaml

modified src/model_theory/bundled.lean
- \+ *def* bundled_induced
- \+ *def* bundled_induced_equiv
- \+ *def* elementarily_equivalent.to_Model

modified src/model_theory/satisfiability.lean
- \+ *lemma* exists_elementary_embedding_card_eq_of_le
- \+ *lemma* exists_elementarily_equivalent_card_eq
- \+ *lemma* categorical.is_complete
- \+ *theorem* exists_elementary_embedding_card_eq_of_ge
- \+/\- *theorem* exists_elementary_embedding_card_eq
- \+ *theorem* exists_model_card_eq
- \+ *theorem* empty_infinite_Theory_is_complete
- \+/\- *theorem* exists_elementary_embedding_card_eq

modified src/model_theory/semantics.lean
- \+ *lemma* elementarily_equivalent
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* complete_theory_eq
- \+ *lemma* realize_sentence
- \+ *lemma* Theory_model_iff
- \+ *lemma* Theory_model
- \+ *lemma* nonempty_iff
- \+ *lemma* nonempty
- \+ *lemma* infinite_iff
- \+ *lemma* infinite

modified src/set_theory/cardinal/basic.lean
- \+ *lemma* lift_mk_shrink
- \+ *lemma* lift_mk_shrink'
- \+ *lemma* lift_mk_shrink''



## [2022-06-29 18:27:22](https://github.com/leanprover-community/mathlib/commit/397d45f)
feat(algebra/order/monoid): `a + b ≤ c → a ≤ c` ([#15033](https://github.com/leanprover-community/mathlib/pull/15033))
Generalize four lemmas that were left by previous PRs before `canonically_ordered_monoid` was a thing.
#### Estimated changes
modified src/algebra/order/monoid.lean
- \+ *lemma* le_of_mul_le_left
- \+ *lemma* le_of_mul_le_right

modified src/data/matrix/rank.lean

modified src/data/nat/basic.lean
- \- *lemma* le_of_add_le_left
- \- *lemma* le_of_add_le_right

modified src/data/polynomial/coeff.lean

modified src/data/polynomial/hasse_deriv.lean

modified src/data/real/nnreal.lean
- \- *lemma* le_of_add_le_left
- \- *lemma* le_of_add_le_right

modified src/ring_theory/power_series/basic.lean



## [2022-06-29 18:27:20](https://github.com/leanprover-community/mathlib/commit/07726e2)
chore(analysis/locally_convex/balanced_core_hull): Golf ([#14987](https://github.com/leanprover-community/mathlib/pull/14987))
Golf and improve lemmas based on the naming convention:
* `balanced_mem` → `balanced_iff_smul_mem`
* `zero_singleton_balanced` → `balanced_zero`
* `balanced_core_emptyset` → `balanced_core_empty`
* `balanced_core_mem_iff` → `mem_balanced_core_iff`
* `balanced_hull_mem_iff` → `mem_balanced_hull_iff`
* `balanced_core_is_closed` → `is_closed.balanced_core`
#### Estimated changes
modified src/analysis/locally_convex/balanced_core_hull.lean
- \+/\- *lemma* balanced_core_subset
- \+ *lemma* balanced_core_empty
- \+ *lemma* mem_balanced_core_iff
- \+/\- *lemma* balanced.subset_core_of_subset
- \+ *lemma* mem_balanced_core_aux_iff
- \+ *lemma* mem_balanced_hull_iff
- \+/\- *lemma* balanced.hull_subset_of_subset
- \+/\- *lemma* balanced_core_zero_mem
- \+/\- *lemma* balanced_core_nonempty_iff
- \+/\- *lemma* balanced_core_aux_balanced
- \+/\- *lemma* balanced_core_aux_maximal
- \+/\- *lemma* balanced_core_subset_balanced_core_aux
- \+/\- *lemma* balanced_core_eq_Inter
- \+/\- *lemma* subset_balanced_core
- \+/\- *lemma* balanced_core_mem_nhds_zero
- \+/\- *lemma* balanced_core_subset
- \- *lemma* balanced_core_emptyset
- \- *lemma* balanced_core_mem_iff
- \+/\- *lemma* balanced.subset_core_of_subset
- \- *lemma* balanced_core_aux_mem_iff
- \- *lemma* balanced_hull_mem_iff
- \+/\- *lemma* balanced.hull_subset_of_subset
- \+/\- *lemma* balanced_core_nonempty_iff
- \+/\- *lemma* balanced_core_zero_mem
- \+/\- *lemma* balanced_core_aux_balanced
- \+/\- *lemma* balanced_core_aux_maximal
- \+/\- *lemma* balanced_core_subset_balanced_core_aux
- \+/\- *lemma* balanced_core_eq_Inter
- \+/\- *lemma* subset_balanced_core
- \- *lemma* balanced_core_is_closed
- \+/\- *lemma* balanced_core_mem_nhds_zero

modified src/analysis/locally_convex/basic.lean
- \+ *lemma* balanced_iff_smul_mem
- \+ *lemma* balanced_zero
- \- *lemma* balanced_mem
- \- *lemma* zero_singleton_balanced

modified src/topology/algebra/module/finite_dimension.lean



## [2022-06-29 18:27:19](https://github.com/leanprover-community/mathlib/commit/478773b)
chore(data/nat/factorization/basic): golf rec_on_pos_prime_pos_coprime, remove import ([#14935](https://github.com/leanprover-community/mathlib/pull/14935))
Golf the proof of `rec_on_pos_prime_pos_coprime`, eliminating the need for `tactic.interval_cases`
#### Estimated changes
modified src/data/nat/factorization/basic.lean



## [2022-06-29 17:31:54](https://github.com/leanprover-community/mathlib/commit/ee8d588)
refactor(logic/hydra): use `is_irrefl` ([#15039](https://github.com/leanprover-community/mathlib/pull/15039))
`is_irrefl` seems to be the more commonly used spelling
#### Estimated changes
modified src/logic/hydra.lean
- \+/\- *lemma* cut_expand_iff
- \+/\- *lemma* acc_of_singleton
- \+/\- *lemma* _root_.acc.cut_expand
- \+/\- *lemma* cut_expand_iff
- \+/\- *lemma* acc_of_singleton
- \+/\- *lemma* _root_.acc.cut_expand
- \+/\- *theorem* not_cut_expand_zero
- \+/\- *theorem* not_cut_expand_zero



## [2022-06-29 14:27:11](https://github.com/leanprover-community/mathlib/commit/c8ab806)
feat(tactic/alias.lean): use current namespace in alias ([#14961](https://github.com/leanprover-community/mathlib/pull/14961))
This makes `alias foo <- bar` use the current namespace to resolve the new alias name `bar`, for consistency with `def bar := foo` and leanprover-community/mathlib4[#293](https://github.com/leanprover-community/mathlib/pull/293).
#### Estimated changes
modified scripts/nolints.txt

modified src/algebra/group_power/lemmas.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/asymptotics/theta.lean

modified src/analysis/calculus/implicit.lean

modified src/analysis/calculus/inverse.lean

modified src/analysis/normed/group/hom.lean

modified src/analysis/special_functions/complex/log.lean

modified src/category_theory/category/Bipointed.lean

modified src/category_theory/category/Pointed.lean

modified src/category_theory/category/Twop.lean

modified src/category_theory/category/preorder.lean

modified src/category_theory/functor/fully_faithful.lean

modified src/combinatorics/simple_graph/clique.lean

modified src/combinatorics/simple_graph/regularity/bound.lean

modified src/data/finset/basic.lean

modified src/data/finset/card.lean

modified src/data/finset/locally_finite.lean

modified src/data/finset/pointwise.lean

modified src/data/finset/slice.lean

modified src/data/finset/sym.lean

modified src/data/fintype/basic.lean

modified src/data/int/parity.lean

modified src/data/list/basic.lean

modified src/data/list/infix.lean

modified src/data/list/nodup.lean

modified src/data/list/pairwise.lean

modified src/data/list/perm.lean

modified src/data/multiset/basic.lean

modified src/data/multiset/dedup.lean

modified src/data/multiset/locally_finite.lean

modified src/data/multiset/nodup.lean

modified src/data/nat/cast.lean

modified src/data/nat/factorial/basic.lean

modified src/data/nat/pow.lean

modified src/data/polynomial/degree/definitions.lean

modified src/data/real/ennreal.lean

modified src/data/set/basic.lean

modified src/data/set/function.lean

modified src/data/set/lattice.lean

modified src/data/set/pairwise.lean

modified src/data/set/pointwise.lean

modified src/dynamics/flow.lean

modified src/geometry/manifold/partition_of_unity.lean

modified src/linear_algebra/matrix/to_linear_equiv.lean

modified src/linear_algebra/span.lean

modified src/logic/equiv/local_equiv.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/integrable_on.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/measure_space_def.lean

modified src/meta/expr.lean

modified src/order/compactly_generated.lean

modified src/order/compare.lean

modified src/order/filter/at_top_bot.lean

modified src/order/filter/bases.lean

modified src/order/filter/basic.lean

modified src/order/filter/germ.lean

modified src/order/filter/small_sets.lean

modified src/order/filter/ultrafilter.lean

modified src/order/succ_pred/basic.lean

modified src/order/sup_indep.lean

modified src/order/synonym.lean

modified src/probability/ident_distrib.lean

modified src/ring_theory/multiplicity.lean

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/game/pgame.lean

modified src/set_theory/surreal/basic.lean

modified src/tactic/alias.lean

modified src/tactic/core.lean

modified src/topology/bornology/basic.lean

modified src/topology/local_homeomorph.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/metric_separated.lean



## [2022-06-29 14:27:10](https://github.com/leanprover-community/mathlib/commit/5de765c)
feat(linear_algebra/linear_pmap): definition of the graph ([#14920](https://github.com/leanprover-community/mathlib/pull/14920))
Define the graph of a partial linear map as the pushforward of the graph of the underlying linear map
and prove some elementary facts.
#### Estimated changes
modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* mem_graph_iff'
- \+ *lemma* mem_graph_iff
- \+ *lemma* mem_graph
- \+ *lemma* mem_graph_snd_inj
- \+ *lemma* mem_graph_snd_inj'
- \+ *lemma* graph_fst_eq_zero_snd
- \+ *def* graph



## [2022-06-29 12:27:59](https://github.com/leanprover-community/mathlib/commit/aa812bd)
chore(group_theory/group_action/basic): split file ([#15044](https://github.com/leanprover-community/mathlib/pull/15044))
Split the file `group_theory/group_action/basic` to remove the dependency on `group_theory/quotient_group`, moving everything involving quotients to a new file `group_theory/group_action/quotient`.
#### Estimated changes
modified src/algebra/polynomial/group_ring_action.lean

modified src/category_theory/action.lean

modified src/data/zmod/quotient.lean

modified src/group_theory/commuting_probability.lean

modified src/group_theory/complement.lean

modified src/group_theory/group_action/basic.lean
- \- *lemma* quotient.smul_mk
- \- *lemma* quotient.smul_coe
- \- *lemma* quotient.mk_smul_out'
- \- *lemma* quotient.coe_smul_out'
- \- *lemma* _root_.mul_action_hom.to_quotient_apply
- \- *lemma* card_orbit_mul_card_stabilizer_eq_card_group
- \- *lemma* stabilizer_quotient
- \- *lemma* card_eq_sum_card_group_div_card_stabilizer'
- \- *lemma* card_eq_sum_card_group_div_card_stabilizer
- \- *lemma* sum_card_fixed_by_eq_card_orbits_mul_card_group
- \- *lemma* normal_core_eq_ker
- \- *theorem* of_quotient_stabilizer_mk
- \- *theorem* of_quotient_stabilizer_mem_orbit
- \- *theorem* of_quotient_stabilizer_smul
- \- *theorem* injective_of_quotient_stabilizer
- \- *theorem* orbit_equiv_quotient_stabilizer_symm_apply
- \- *def* _root_.mul_action_hom.to_quotient
- \- *def* of_quotient_stabilizer

created src/group_theory/group_action/quotient.lean
- \+ *lemma* quotient.smul_mk
- \+ *lemma* quotient.smul_coe
- \+ *lemma* quotient.mk_smul_out'
- \+ *lemma* quotient.coe_smul_out'
- \+ *lemma* _root_.mul_action_hom.to_quotient_apply
- \+ *lemma* card_orbit_mul_card_stabilizer_eq_card_group
- \+ *lemma* stabilizer_quotient
- \+ *lemma* card_eq_sum_card_group_div_card_stabilizer'
- \+ *lemma* card_eq_sum_card_group_div_card_stabilizer
- \+ *lemma* sum_card_fixed_by_eq_card_orbits_mul_card_group
- \+ *lemma* normal_core_eq_ker
- \+ *theorem* of_quotient_stabilizer_mk
- \+ *theorem* of_quotient_stabilizer_mem_orbit
- \+ *theorem* of_quotient_stabilizer_smul
- \+ *theorem* injective_of_quotient_stabilizer
- \+ *theorem* orbit_equiv_quotient_stabilizer_symm_apply
- \+ *def* _root_.mul_action_hom.to_quotient
- \+ *def* of_quotient_stabilizer

modified src/group_theory/p_group.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/quotient.lean

modified src/topology/algebra/group.lean



## [2022-06-29 10:03:54](https://github.com/leanprover-community/mathlib/commit/ea9dae2)
refactor(topology/*): Use `disjoint` ([#14950](https://github.com/leanprover-community/mathlib/pull/14950))
Replace uses of `s ∩ t = ∅` by `disjoint s t` in the topology library. This shortens proofs.
#### Estimated changes
modified src/data/set/basic.lean
- \- *theorem* subset_compl_iff_disjoint

modified src/field_theory/krull_topology.lean

modified src/group_theory/group_action/basic.lean
- \+ *lemma* disjoint_image_image_iff
- \+/\- *lemma* image_inter_image_iff
- \+/\- *lemma* image_inter_image_iff

modified src/measure_theory/constructions/polish.lean

modified src/measure_theory/function/continuous_map_dense.lean

modified src/measure_theory/measure/haar.lean

modified src/topology/alexandroff.lean

modified src/topology/algebra/const_mul_action.lean

modified src/topology/algebra/continuous_monoid_hom.lean

modified src/topology/algebra/order/basic.lean

modified src/topology/basic.lean
- \+/\- *lemma* is_open_univ
- \+ *lemma* disjoint.frontier_left
- \+ *lemma* disjoint.frontier_right
- \+/\- *lemma* is_open_univ
- \- *lemma* is_open.inter_frontier_eq_empty_of_disjoint
- \+/\- *def* is_open
- \+/\- *def* is_open

modified src/topology/compact_open.lean
- \+ *lemma* gen_empty_right

modified src/topology/connected.lean

modified src/topology/local_homeomorph.lean

modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* ball_disjoint
- \+/\- *theorem* ball_disjoint

modified src/topology/order/priestley.lean

modified src/topology/paracompact.lean

modified src/topology/separation.lean
- \+/\- *lemma* t2_space_iff_nhds
- \+/\- *lemma* t2_separation_compact_nhds
- \+/\- *lemma* t2_space_iff_nhds
- \+/\- *lemma* t2_separation_compact_nhds

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/compact_separated.lean

modified src/topology/uniform_space/separation.lean



## [2022-06-29 08:02:38](https://github.com/leanprover-community/mathlib/commit/03374ee)
feat(algebra/order/field): Linearly ordered semifields ([#15027](https://github.com/leanprover-community/mathlib/pull/15027))
Define `linear_ordered_semifield` and generalize lemmas within `algebra.order.field`.
#### Estimated changes
modified src/algebra/field_power.lean
- \+/\- *lemma* ring_hom.map_zpow
- \+/\- *lemma* ring_equiv.map_zpow
- \+/\- *lemma* zpow_bit1_neg
- \+ *lemma* rat.cast_zpow
- \+/\- *lemma* zpow_nonneg
- \+/\- *lemma* zpow_pos_of_pos
- \+/\- *lemma* zpow_le_of_le
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* zpow_le_one_of_nonpos
- \+/\- *lemma* one_le_zpow_of_nonneg
- \+/\- *lemma* nat.zpow_ne_zero_of_pos
- \+/\- *lemma* one_lt_zpow
- \+/\- *lemma* zpow_strict_mono
- \+/\- *lemma* zpow_strict_anti
- \+/\- *lemma* zpow_lt_iff_lt
- \+/\- *lemma* zpow_le_iff_le
- \+/\- *lemma* min_le_of_zpow_le_max
- \+/\- *lemma* pos_div_pow_pos
- \+/\- *lemma* div_pow_le
- \+/\- *lemma* zpow_injective
- \+/\- *lemma* zpow_inj
- \+ *lemma* zpow_bit0_nonneg
- \+ *lemma* zpow_two_nonneg
- \+ *lemma* zpow_bit0_pos
- \+ *lemma* zpow_two_pos_of_ne_zero
- \+/\- *lemma* ring_hom.map_zpow
- \+/\- *lemma* ring_equiv.map_zpow
- \+/\- *lemma* zpow_bit1_neg
- \+/\- *lemma* zpow_nonneg
- \+/\- *lemma* zpow_pos_of_pos
- \+/\- *lemma* zpow_le_of_le
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* zpow_le_one_of_nonpos
- \+/\- *lemma* one_le_zpow_of_nonneg
- \+/\- *lemma* one_lt_zpow
- \- *lemma* nat.zpow_pos_of_pos
- \+/\- *lemma* nat.zpow_ne_zero_of_pos
- \+/\- *lemma* zpow_strict_mono
- \+/\- *lemma* zpow_strict_anti
- \+/\- *lemma* zpow_lt_iff_lt
- \+/\- *lemma* zpow_le_iff_le
- \+/\- *lemma* min_le_of_zpow_le_max
- \+/\- *lemma* pos_div_pow_pos
- \+/\- *lemma* div_pow_le
- \+/\- *lemma* zpow_injective
- \+/\- *lemma* zpow_inj
- \+/\- *theorem* zpow_bit1_neg_iff
- \+/\- *theorem* zpow_bit1_nonneg_iff
- \+/\- *theorem* zpow_bit1_nonpos_iff
- \+/\- *theorem* zpow_bit1_pos_iff
- \- *theorem* zpow_bit0_nonneg
- \- *theorem* zpow_two_nonneg
- \- *theorem* zpow_bit0_pos
- \- *theorem* zpow_two_pos_of_ne_zero
- \+/\- *theorem* zpow_bit1_neg_iff
- \+/\- *theorem* zpow_bit1_nonneg_iff
- \+/\- *theorem* zpow_bit1_nonpos_iff
- \+/\- *theorem* zpow_bit1_pos_iff
- \- *theorem* rat.cast_zpow

modified src/algebra/order/field.lean
- \+/\- *lemma* one_div_strict_anti_on
- \+/\- *lemma* is_glb.mul_left
- \+/\- *lemma* is_glb.mul_right
- \+/\- *lemma* div_pos_iff
- \+/\- *lemma* div_neg_iff
- \+/\- *lemma* div_nonneg_iff
- \+/\- *lemma* div_nonpos_iff
- \+/\- *lemma* div_nonneg_of_nonpos
- \+/\- *lemma* div_pos_of_neg_of_neg
- \+/\- *lemma* div_neg_of_neg_of_pos
- \+/\- *lemma* div_neg_of_pos_of_neg
- \+/\- *lemma* div_le_iff_of_neg
- \+/\- *lemma* div_le_iff_of_neg'
- \+/\- *lemma* le_div_iff_of_neg
- \+/\- *lemma* le_div_iff_of_neg'
- \+/\- *lemma* div_lt_iff_of_neg
- \+/\- *lemma* div_lt_iff_of_neg'
- \+/\- *lemma* lt_div_iff_of_neg
- \+/\- *lemma* lt_div_iff_of_neg'
- \+/\- *lemma* inv_le_inv_of_neg
- \+/\- *lemma* inv_le_of_neg
- \+/\- *lemma* le_inv_of_neg
- \+/\- *lemma* inv_lt_inv_of_neg
- \+/\- *lemma* inv_lt_of_neg
- \+/\- *lemma* lt_inv_of_neg
- \+/\- *lemma* div_le_div_of_nonpos_of_le
- \+/\- *lemma* div_lt_div_of_neg_of_lt
- \+/\- *lemma* div_le_div_right_of_neg
- \+/\- *lemma* div_lt_div_right_of_neg
- \+/\- *lemma* one_le_div_of_neg
- \+/\- *lemma* div_le_one_of_neg
- \+/\- *lemma* one_lt_div_of_neg
- \+/\- *lemma* div_lt_one_of_neg
- \+/\- *lemma* one_div_le_of_neg
- \+/\- *lemma* one_div_lt_of_neg
- \+/\- *lemma* le_one_div_of_neg
- \+/\- *lemma* lt_one_div_of_neg
- \+/\- *lemma* one_lt_div_iff
- \+/\- *lemma* one_le_div_iff
- \+/\- *lemma* div_lt_one_iff
- \+/\- *lemma* div_le_one_iff
- \+/\- *lemma* one_div_le_one_div_of_neg_of_le
- \+/\- *lemma* one_div_lt_one_div_of_neg_of_lt
- \+/\- *lemma* le_of_neg_of_one_div_le_one_div
- \+/\- *lemma* lt_of_neg_of_one_div_lt_one_div
- \+/\- *lemma* one_div_le_one_div_of_neg
- \+/\- *lemma* one_div_lt_one_div_of_neg
- \+/\- *lemma* one_div_lt_neg_one
- \+/\- *lemma* one_div_le_neg_one
- \+/\- *lemma* sub_self_div_two
- \+/\- *lemma* div_two_sub_self
- \+/\- *lemma* add_sub_div_two_lt
- \+/\- *lemma* sub_one_div_inv_le_two
- \+/\- *lemma* mul_sub_mul_div_mul_neg_iff
- \+/\- *lemma* mul_sub_mul_div_mul_nonpos_iff
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \+/\- *lemma* le_of_forall_sub_le
- \+/\- *lemma* mul_self_inj_of_nonneg
- \+/\- *lemma* min_div_div_right_of_nonpos
- \+/\- *lemma* max_div_div_right_of_nonpos
- \+/\- *lemma* abs_inv
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_one_div
- \+ *lemma* nat.cast_le_pow_sub_div_sub
- \+/\- *lemma* div_pos_iff
- \+/\- *lemma* div_neg_iff
- \+/\- *lemma* div_nonneg_iff
- \+/\- *lemma* div_nonpos_iff
- \+/\- *lemma* div_pos_of_neg_of_neg
- \+/\- *lemma* div_neg_of_neg_of_pos
- \+/\- *lemma* div_neg_of_pos_of_neg
- \+/\- *lemma* div_nonneg_of_nonpos
- \+/\- *lemma* div_le_iff_of_neg
- \+/\- *lemma* div_le_iff_of_neg'
- \+/\- *lemma* le_div_iff_of_neg
- \+/\- *lemma* le_div_iff_of_neg'
- \+/\- *lemma* div_lt_iff_of_neg
- \+/\- *lemma* div_lt_iff_of_neg'
- \+/\- *lemma* lt_div_iff_of_neg
- \+/\- *lemma* lt_div_iff_of_neg'
- \+/\- *lemma* inv_le_inv_of_neg
- \+/\- *lemma* inv_le_of_neg
- \+/\- *lemma* le_inv_of_neg
- \+/\- *lemma* inv_lt_inv_of_neg
- \+/\- *lemma* inv_lt_of_neg
- \+/\- *lemma* lt_inv_of_neg
- \+/\- *lemma* div_le_div_of_nonpos_of_le
- \+/\- *lemma* div_lt_div_of_neg_of_lt
- \+/\- *lemma* div_le_div_right_of_neg
- \+/\- *lemma* div_lt_div_right_of_neg
- \+/\- *lemma* one_le_div_of_neg
- \+/\- *lemma* div_le_one_of_neg
- \+/\- *lemma* one_lt_div_of_neg
- \+/\- *lemma* div_lt_one_of_neg
- \+/\- *lemma* one_div_le_of_neg
- \+/\- *lemma* one_div_lt_of_neg
- \+/\- *lemma* le_one_div_of_neg
- \+/\- *lemma* lt_one_div_of_neg
- \+/\- *lemma* one_lt_div_iff
- \+/\- *lemma* one_le_div_iff
- \+/\- *lemma* div_lt_one_iff
- \+/\- *lemma* div_le_one_iff
- \+/\- *lemma* one_div_le_one_div_of_neg_of_le
- \+/\- *lemma* one_div_lt_one_div_of_neg_of_lt
- \+/\- *lemma* le_of_neg_of_one_div_le_one_div
- \+/\- *lemma* lt_of_neg_of_one_div_lt_one_div
- \+/\- *lemma* one_div_le_one_div_of_neg
- \+/\- *lemma* one_div_lt_one_div_of_neg
- \+/\- *lemma* one_div_lt_neg_one
- \+/\- *lemma* one_div_le_neg_one
- \+/\- *lemma* sub_self_div_two
- \+/\- *lemma* div_two_sub_self
- \+/\- *lemma* add_sub_div_two_lt
- \+/\- *lemma* sub_one_div_inv_le_two
- \+/\- *lemma* mul_sub_mul_div_mul_neg_iff
- \+/\- *lemma* mul_sub_mul_div_mul_nonpos_iff
- \+/\- *lemma* exists_add_lt_and_pos_of_lt
- \+/\- *lemma* le_of_forall_sub_le
- \+/\- *lemma* mul_self_inj_of_nonneg
- \+/\- *lemma* min_div_div_right_of_nonpos
- \+/\- *lemma* max_div_div_right_of_nonpos
- \+/\- *lemma* abs_div
- \+/\- *lemma* abs_one_div
- \+/\- *lemma* abs_inv
- \+/\- *lemma* one_div_strict_anti_on
- \+/\- *lemma* is_glb.mul_left
- \+/\- *lemma* is_glb.mul_right
- \+/\- *theorem* nat.cast_le_pow_div_sub
- \- *theorem* nat.cast_le_pow_sub_div_sub
- \+/\- *theorem* nat.cast_le_pow_div_sub
- \+ *def* injective.linear_ordered_semifield
- \+ *def* injective.linear_ordered_field
- \- *def* function.injective.linear_ordered_field

modified src/algebra/order/floor.lean

modified src/data/int/log.lean

modified src/data/nat/cast_field.lean

modified src/number_theory/padics/padic_numbers.lean



## [2022-06-29 02:12:43](https://github.com/leanprover-community/mathlib/commit/55ec65a)
feat(topology/algebra/module/basic): define continuous_(semi)linear_map_class ([#14674](https://github.com/leanprover-community/mathlib/pull/14674))
This PR brings the morphism refactor to continuous (semi)linear maps. We define `continuous_semilinear_map_class` and `continuous_linear_map_class` in a way that parallels the non-continuous versions, along with a few extras (i.e. `add_monoid_hom_class` instance for `normed_group_hom`).
A few things I was not too sure about:
- When generalizing lemmas to a morphism class rather than a particular type of morphism, I used `𝓕` as the type (instead of just `F` as is done for most `fun_like` types) to avoid clashing with our convention of using `E`, `F`, etc for e.g. vector spaces.
- Namespacing: I placed lemmas like `isometry_of_norm`, `continuous_of_bound`, etc, under the `add_monoid_hom_class` namespace. Maybe the root namespace would make sense here.
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/locally_convex/bounded.lean

modified src/analysis/normed/group/SemiNormedGroup.lean

modified src/analysis/normed/group/SemiNormedGroup/completion.lean

modified src/analysis/normed/group/basic.lean
- \+ *lemma* add_monoid_hom_class.lipschitz_of_bound
- \+ *lemma* add_monoid_hom_class.continuous_of_bound
- \+ *lemma* add_monoid_hom_class.uniform_continuous_of_bound
- \+ *lemma* add_monoid_hom_class.isometry_iff_norm
- \+ *lemma* add_monoid_hom_class.isometry_of_norm
- \+ *lemma* add_monoid_hom_class.lipschitz_of_bound_nnnorm
- \+ *lemma* add_monoid_hom_class.antilipschitz_of_bound
- \+ *lemma* add_monoid_hom_class.bound_of_antilipschitz
- \- *lemma* add_monoid_hom.lipschitz_of_bound
- \- *lemma* add_monoid_hom.continuous_of_bound
- \- *lemma* add_monoid_hom.isometry_iff_norm
- \- *lemma* add_monoid_hom.isometry_of_norm
- \- *lemma* add_monoid_hom.lipschitz_of_bound_nnnorm

modified src/analysis/normed/group/hom.lean
- \- *lemma* map_zero
- \- *lemma* map_add
- \- *lemma* map_sum
- \- *lemma* map_sub
- \- *lemma* map_neg
- \- *lemma* isometry_iff_norm
- \- *lemma* isometry_of_norm

modified src/analysis/normed/group/hom_completion.lean

modified src/analysis/normed/group/quotient.lean

modified src/analysis/normed_space/banach_steinhaus.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/dual.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/analysis/normed_space/linear_isometry.lean

modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* norm_image_of_norm_zero
- \+ *lemma* semilinear_map_class.bound_of_shell_semi_normed
- \+ *lemma* semilinear_map_class.bound_of_continuous
- \- *lemma* linear_map.lipschitz_of_bound
- \- *lemma* linear_map.lipschitz_of_bound_nnnorm
- \- *lemma* linear_map.bound_of_antilipschitz
- \- *lemma* linear_map.uniform_continuous_of_bound
- \- *lemma* linear_map.continuous_of_bound
- \+/\- *lemma* norm_image_of_norm_zero
- \- *lemma* linear_map.bound_of_shell_semi_normed
- \- *lemma* linear_map.bound_of_continuous
- \- *lemma* isometry_iff_norm
- \- *theorem* linear_map.antilipschitz_of_bound

modified src/analysis/normed_space/star/basic.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/bochner.lean

modified src/topology/algebra/module/basic.lean
- \- *lemma* map_smulₛₗ
- \- *lemma* map_smul

modified src/topology/algebra/module/finite_dimension.lean

modified src/topology/algebra/module/weak_dual.lean



## [2022-06-28 19:09:05](https://github.com/leanprover-community/mathlib/commit/08b07a6)
feat(order/succ_pred/basic): tag more lemmas with simp  ([#14998](https://github.com/leanprover-community/mathlib/pull/14998))
#### Estimated changes
modified src/order/succ_pred/basic.lean
- \+/\- *lemma* lt_succ_iff
- \+/\- *lemma* succ_le_iff
- \+/\- *lemma* succ_le_succ_iff
- \+/\- *lemma* succ_lt_succ_iff
- \+/\- *lemma* Ico_succ_right
- \+/\- *lemma* Ioo_succ_right
- \+/\- *lemma* Icc_succ_left
- \+/\- *lemma* Ico_succ_left
- \+/\- *lemma* pred_lt_iff
- \+/\- *lemma* le_pred_iff
- \+/\- *lemma* pred_le_pred_iff
- \+/\- *lemma* pred_lt_pred_iff
- \+/\- *lemma* Ioc_pred_left
- \+/\- *lemma* Ioo_pred_left
- \+/\- *lemma* Icc_pred_right
- \+/\- *lemma* Ioc_pred_right
- \+/\- *lemma* lt_succ_iff
- \+/\- *lemma* succ_le_iff
- \+/\- *lemma* succ_le_succ_iff
- \+/\- *lemma* succ_lt_succ_iff
- \+/\- *lemma* Ico_succ_right
- \+/\- *lemma* Ioo_succ_right
- \+/\- *lemma* Icc_succ_left
- \+/\- *lemma* Ico_succ_left
- \+/\- *lemma* pred_lt_iff
- \+/\- *lemma* le_pred_iff
- \+/\- *lemma* pred_le_pred_iff
- \+/\- *lemma* pred_lt_pred_iff
- \+/\- *lemma* Ioc_pred_left
- \+/\- *lemma* Ioo_pred_left
- \+/\- *lemma* Icc_pred_right
- \+/\- *lemma* Ioc_pred_right



## [2022-06-28 19:09:03](https://github.com/leanprover-community/mathlib/commit/7db7667)
feat(order/boolean_algebra): Interaction of disjointness and complements ([#14925](https://github.com/leanprover-community/mathlib/pull/14925))
Prove `disjoint x yᶜ ↔ x ≤ y` and similar, transfer those results to `set`.
Lemma renames
* `subset_compl_iff_disjoint` → `subset_compl_iff_disjoint_right`
* `set.subset_compl_iff_disjoint` → `set.subset_compl_iff_disjoint_right`
* `disjoint_iff_le_compl_left` → `le_compl_iff_disjoint_left`
* `disjoint_iff_le_compl_right` → `le_compl_iff_disjoint_right`
#### Estimated changes
modified src/algebra/support.lean

modified src/analysis/convex/stone_separation.lean

modified src/analysis/normed_space/riesz_lemma.lean

modified src/data/set/basic.lean
- \+ *lemma* compl_subset_comm
- \+ *lemma* subset_compl_comm
- \+/\- *lemma* compl_subset_compl
- \+ *lemma* subset_compl_iff_disjoint_left
- \+ *lemma* subset_compl_iff_disjoint_right
- \+ *lemma* disjoint_compl_left_iff_subset
- \+ *lemma* disjoint_compl_right_iff_subset
- \+/\- *lemma* compl_subset_compl
- \- *theorem* compl_subset_comm
- \- *theorem* subset_compl_comm

modified src/data/set/lattice.lean
- \+ *lemma* disjoint_Union₂_left
- \+ *lemma* disjoint_Union₂_right
- \+ *lemma* disjoint_sUnion_left
- \+ *lemma* disjoint_sUnion_right
- \- *lemma* disjoint_iff_subset_compl_right
- \- *lemma* disjoint_iff_subset_compl_left

modified src/group_theory/free_product.lean

modified src/logic/equiv/embedding.lean

modified src/order/boolean_algebra.lean
- \+ *lemma* le_compl_iff_disjoint_right
- \+ *lemma* le_compl_iff_disjoint_left
- \+ *lemma* disjoint_compl_left_iff
- \+ *lemma* disjoint_compl_right_iff
- \- *theorem* disjoint_iff_le_compl_right
- \- *theorem* disjoint_iff_le_compl_left

modified src/order/complete_boolean_algebra.lean
- \+ *lemma* supr₂_disjoint_iff
- \+ *lemma* disjoint_supr₂_iff

modified src/order/filter/bases.lean

modified src/topology/basic.lean

modified src/topology/metric_space/hausdorff_distance.lean



## [2022-06-28 15:21:02](https://github.com/leanprover-community/mathlib/commit/00c17d6)
feat(algebra/ring/boolean_ring): `bool` is a Boolean ring ([#15004](https://github.com/leanprover-community/mathlib/pull/15004))
and a few `bool` lemmas.
#### Estimated changes
modified src/algebra/ring/boolean_ring.lean

modified src/data/bool/basic.lean
- \+ *lemma* band_bor_distrib_left
- \+ *lemma* band_bor_distrib_right
- \+ *lemma* bor_band_distrib_left
- \+ *lemma* bor_band_distrib_right
- \+ *lemma* band_bxor_distrib_left
- \+ *lemma* band_bxor_distrib_right



## [2022-06-28 12:51:25](https://github.com/leanprover-community/mathlib/commit/78bc372)
feat(data/{finset, set}/basic): tweak `nonempty_coe_sort` and `is_empty_coe_sort` ([#14937](https://github.com/leanprover-community/mathlib/pull/14937))
This PR does the following:
- add lemmas `set.is_empty_coe_sort` and `finset.is_empty_coe_sort`
- made argument of both `nonempty_coe_sort` lemmas inferred
- fix some spacing
#### Estimated changes
modified src/analysis/normed_space/is_R_or_C.lean

modified src/data/finset/basic.lean
- \+/\- *lemma* coe_nonempty
- \+/\- *lemma* nonempty_coe_sort
- \+/\- *lemma* nonempty.bex
- \+ *lemma* is_empty_coe_sort
- \+/\- *lemma* coe_nonempty
- \+/\- *lemma* nonempty_coe_sort
- \+/\- *lemma* nonempty.bex

modified src/data/set/basic.lean
- \+/\- *lemma* nonempty_coe_sort
- \+ *lemma* is_empty_coe_sort
- \+/\- *lemma* nonempty_coe_sort

modified src/measure_theory/function/jacobian.lean

modified src/topology/algebra/semigroup.lean



## [2022-06-28 09:03:25](https://github.com/leanprover-community/mathlib/commit/3594b63)
feat(probability_theory/independence): if a family of pi-systems is independent, then so are the generated measurable spaces ([#9387](https://github.com/leanprover-community/mathlib/pull/9387))
The main result in this PR is `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent. We already had a version of this for two pi-systems instead of a family.
In order to prove this, and as preparation for a next PR about Kolmogorov's 0-1 law, a definition `pi_Union_Inter` is introduced to build a particular pi-system from a family of pi-systems.
#### Estimated changes
modified src/data/set/lattice.lean
- \+ *lemma* sup_closed_singleton
- \+ *lemma* sup_closed.inter
- \+ *lemma* sup_closed_of_totally_ordered
- \+ *lemma* sup_closed_of_linear_order
- \+ *def* sup_closed

modified src/measure_theory/measurable_space.lean
- \- *lemma* generate_from_mono
- \- *lemma* generate_from_sup_generate_from

modified src/measure_theory/measurable_space_def.lean
- \+ *lemma* generate_from_mono
- \+ *lemma* generate_from_sup_generate_from
- \+ *lemma* generate_from_insert_univ
- \+ *lemma* generate_from_insert_empty

modified src/measure_theory/pi_system.lean
- \+ *lemma* is_pi_system.insert_empty
- \+ *lemma* is_pi_system.insert_univ
- \+/\- *lemma* mem_generate_pi_system_Union_elim'
- \+ *lemma* is_pi_system_pi_Union_Inter
- \+ *lemma* pi_Union_Inter_mono_left
- \+ *lemma* generate_from_pi_Union_Inter_le
- \+ *lemma* subset_pi_Union_Inter
- \+ *lemma* mem_pi_Union_Inter_of_measurable_set
- \+ *lemma* le_generate_from_pi_Union_Inter
- \+ *lemma* measurable_set_supr_of_mem_pi_Union_Inter
- \+ *lemma* generate_from_pi_Union_Inter_measurable_space
- \+/\- *lemma* mem_generate_pi_system_Union_elim'
- \+ *def* pi_Union_Inter

modified src/probability/independence.lean
- \+ *lemma* Indep_sets.pi_Union_Inter_singleton
- \+ *theorem* Indep_sets.Indep_aux
- \+ *theorem* Indep_sets.Indep



## [2022-06-28 08:13:29](https://github.com/leanprover-community/mathlib/commit/728e074)
feat(measure_theory/function/lp_order): prove a `normed_lattice_add_comm_group` instance for Lp ([#14999](https://github.com/leanprover-community/mathlib/pull/14999))
#### Estimated changes
modified src/measure_theory/function/ae_eq_fun.lean
- \+ *lemma* coe_fn_abs

modified src/measure_theory/function/lp_order.lean
- \+ *lemma* coe_fn_sup
- \+ *lemma* coe_fn_inf
- \+ *lemma* coe_fn_abs

modified src/measure_theory/function/simple_func_dense_lp.lean



## [2022-06-28 03:59:01](https://github.com/leanprover-community/mathlib/commit/dcedc04)
feat(order/symm_diff): Triangle inequality for the symmetric difference ([#14847](https://github.com/leanprover-community/mathlib/pull/14847))
Prove that `a ∆ c ≤ a ∆ b ⊔ b ∆ c`.
#### Estimated changes
modified src/order/boolean_algebra.lean
- \+ *lemma* sdiff_triangle

modified src/order/symm_diff.lean
- \+ *lemma* le_symm_diff_iff_left
- \+ *lemma* le_symm_diff_iff_right
- \+ *lemma* symm_diff_triangle



## [2022-06-28 02:30:01](https://github.com/leanprover-community/mathlib/commit/ae3d572)
chore(topology/uniform_space/basic): Make `to_topological_space_inf` and `inf_uniformity` true by definition ([#14912](https://github.com/leanprover-community/mathlib/pull/14912))
Since the lattice API lets us provide a definition for `inf`, we may as well provide a nice one such that the obvious properties are true by rfl.
#### Estimated changes
modified src/order/filter/lift.lean
- \+ *lemma* lift'_inf_le

modified src/topology/uniform_space/basic.lean
- \+ *lemma* ball_inter



## [2022-06-28 00:05:04](https://github.com/leanprover-community/mathlib/commit/cf4d987)
chore(analysis/special_functions/trigonometric/angle): rfl lemmas for nat and int smul actions on angle ([#15003](https://github.com/leanprover-community/mathlib/pull/15003))
These can't be simp, because the simp-normal form is multiplication.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* coe_nsmul
- \+ *lemma* coe_zsmul



## [2022-06-28 00:05:02](https://github.com/leanprover-community/mathlib/commit/37bf8a2)
chore(topology/separation): Extract `set` product lemma ([#14958](https://github.com/leanprover-community/mathlib/pull/14958))
Move `prod_subset_compl_diagonal_iff_disjoint` to `data.set.prod`, where it belongs. Delete `diagonal_eq_range_diagonal_map` because it duplicates `set.diagonal_eq_range`. Move `set.disjoint_left`/`set.disjoint_right` to `data.set.basic` to avoid an import cycle.
Make variable semi-implicit in the RHS of `disjoint_left` and `disjoint_right`.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* _root_.disjoint.inter_eq
- \+ *lemma* disjoint_left
- \+ *lemma* disjoint_right

modified src/data/set/lattice.lean
- \- *lemma* disjoint_left
- \- *lemma* _root_.disjoint.inter_eq
- \- *theorem* disjoint_right

modified src/data/set/prod.lean
- \+ *lemma* prod_subset_compl_diagonal_iff_disjoint

modified src/linear_algebra/linear_independent.lean

modified src/topology/basic.lean

modified src/topology/separation.lean
- \- *lemma* diagonal_eq_range_diagonal_map
- \- *lemma* prod_subset_compl_diagonal_iff_disjoint

modified src/topology/urysohns_lemma.lean



## [2022-06-28 00:05:01](https://github.com/leanprover-community/mathlib/commit/ee7f38c)
chore(data/set/basic): remove duplicate `nonempty_insert` in favor of `insert_nonempty` ([#14884](https://github.com/leanprover-community/mathlib/pull/14884))
This name matches e.g. `univ_nonempty` and `singleton_nonempty`.
#### Estimated changes
modified src/data/set/basic.lean
- \- *lemma* nonempty_insert
- \+/\- *theorem* insert_nonempty
- \+/\- *theorem* insert_nonempty

modified src/order/conditionally_complete_lattice.lean

modified src/topology/algebra/order/compact.lean



## [2022-06-28 00:04:54](https://github.com/leanprover-community/mathlib/commit/365b2ee)
feat(data/bool): bnot_ne ([#10562](https://github.com/leanprover-community/mathlib/pull/10562))
#### Estimated changes
modified src/data/bool/basic.lean
- \+ *lemma* not_eq_bnot
- \+ *lemma* bnot_not_eq
- \+ *lemma* ne_bnot
- \+ *lemma* bnot_ne



## [2022-06-27 21:32:09](https://github.com/leanprover-community/mathlib/commit/f6b728f)
feat(data/finset/pointwise): `•` and `⊆` ([#14968](https://github.com/leanprover-community/mathlib/pull/14968))
Port `set` lemmas to `finset`. Tag a few more lemmas with `norm_cast`. Add some missing `to_additive` attributes.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* image_subset_image_iff

modified src/data/finset/pointwise.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* pairwise_disjoint_smul_iff
- \+ *lemma* smul_mem_smul_finset_iff
- \+ *lemma* inv_smul_mem_iff
- \+ *lemma* mem_inv_smul_finset_iff
- \+ *lemma* smul_finset_subset_smul_finset_iff
- \+ *lemma* smul_finset_subset_iff
- \+ *lemma* subset_smul_finset_iff
- \+ *lemma* smul_mem_smul_finset_iff₀
- \+ *lemma* inv_smul_mem_iff₀
- \+ *lemma* mem_inv_smul_finset_iff₀
- \+ *lemma* smul_finset_subset_smul_finset_iff₀
- \+ *lemma* smul_finset_subset_iff₀
- \+ *lemma* subset_smul_finset_iff₀
- \+ *lemma* smul_univ₀
- \+ *lemma* smul_finset_univ₀
- \+/\- *lemma* coe_one
- \+/\- *lemma* pairwise_disjoint_smul_iff

modified src/data/fintype/basic.lean
- \+/\- *lemma* coe_univ
- \+/\- *lemma* coe_univ

modified src/data/set/pointwise.lean
- \+/\- *lemma* pairwise_disjoint_smul_iff
- \+/\- *lemma* pairwise_disjoint_smul_iff



## [2022-06-27 21:32:08](https://github.com/leanprover-community/mathlib/commit/7c6cd38)
chore(set_theory/game/pgame): remove weird `simp` lemma ([#14954](https://github.com/leanprover-community/mathlib/pull/14954))
I added this back before there was much API on casting natural numbers to pre-games, as a safeguard in case I used the wrong `1`. In retrospective this theorem was kind of dumb.
#### Estimated changes
modified src/set_theory/game/pgame.lean



## [2022-06-27 21:32:07](https://github.com/leanprover-community/mathlib/commit/2cdded9)
feat(data/multiset/basic): add multiset.filter_singleton ([#14938](https://github.com/leanprover-community/mathlib/pull/14938))
Adds a lemma, similar to `finset.filter_singleton`.
#### Estimated changes
modified src/data/multiset/basic.lean
- \+ *lemma* filter_singleton



## [2022-06-27 21:32:05](https://github.com/leanprover-community/mathlib/commit/927b468)
chore(data/nat/factorization/basic): golf pow_succ_factorization_not_dvd, remove import ([#14936](https://github.com/leanprover-community/mathlib/pull/14936))
Move `pow_succ_factorization_not_dvd` below `factorization_le_iff_dvd` and use this to golf it, eliminating the need for `tactic.linarith`
#### Estimated changes
modified src/data/nat/factorization/basic.lean
- \+/\- *lemma* pow_succ_factorization_not_dvd
- \+/\- *lemma* pow_succ_factorization_not_dvd



## [2022-06-27 21:32:04](https://github.com/leanprover-community/mathlib/commit/f51286d)
feat(analysis/locally_convex/bounded): continuous linear image of bounded set is bounded ([#14907](https://github.com/leanprover-community/mathlib/pull/14907))
This is needed to prove that the usual strong topology on continuous linear maps satisfies `has_continuous_smul`.
#### Estimated changes
modified src/analysis/locally_convex/bounded.lean
- \+ *lemma* is_vonN_bounded.image



## [2022-06-27 21:32:03](https://github.com/leanprover-community/mathlib/commit/cf50ac1)
chore(algebra/group/units): mark some lemmas as simp ([#14871](https://github.com/leanprover-community/mathlib/pull/14871))
These seem like fairly natural candidates for simp lemmas.
#### Estimated changes
modified src/algebra/group/units.lean



## [2022-06-27 21:32:02](https://github.com/leanprover-community/mathlib/commit/cad1a6c)
feat(set_theory/cardinal/basic): lemmas about `#(finset α)` ([#14850](https://github.com/leanprover-community/mathlib/pull/14850))
This PR does the following:
- prove `mk_finset_of_fintype : #(finset α) = 2 ^ℕ fintype.card α` for `fintype α`
- rename `mk_finset_eq_mk` to `mk_finset_of_infinite` to match the former
- rename `mk_finset` to `mk_coe_finset` to avoid confusion with these two lemmas
#### Estimated changes
modified src/field_theory/fixed.lean

modified src/linear_algebra/dimension.lean

modified src/set_theory/cardinal/basic.lean
- \+ *lemma* mk_coe_finset
- \+ *lemma* mk_finset_of_fintype
- \- *lemma* mk_finset

modified src/set_theory/cardinal/ordinal.lean
- \+ *theorem* mk_finset_of_infinite
- \- *theorem* mk_finset_eq_mk



## [2022-06-27 21:32:00](https://github.com/leanprover-community/mathlib/commit/fef4fb8)
refactor(topology/inseparable): redefine `specializes` and `inseparable` ([#14647](https://github.com/leanprover-community/mathlib/pull/14647))
* Redefine `specializes` and `inseparable` in terms of `nhds`.
* Review API.
* Define `inseparable_setoid` and `separation_quotient`.
* Add `function.surjective.subsingleton`.
#### Estimated changes
modified src/algebraic_geometry/prime_spectrum/basic.lean

modified src/algebraic_geometry/properties.lean

modified src/logic/unique.lean

modified src/topology/inseparable.lean
- \+ *lemma* specializes_tfae
- \+ *lemma* specializes_iff_nhds
- \+ *lemma* specializes_iff_pure
- \+/\- *lemma* specializes_iff_forall_open
- \+ *lemma* specializes.mem_open
- \+ *lemma* is_open.not_specializes
- \+/\- *lemma* specializes_iff_forall_closed
- \+ *lemma* specializes.mem_closed
- \+ *lemma* is_closed.not_specializes
- \+ *lemma* specializes_iff_mem_closure
- \+/\- *lemma* specializes_iff_closure_subset
- \+/\- *lemma* specializes_rfl
- \+/\- *lemma* specializes_refl
- \+/\- *lemma* specializes.trans
- \+ *lemma* specializes_of_nhds_within
- \+ *lemma* specializes.map_of_continuous_at
- \+/\- *lemma* specializes.map
- \+ *lemma* inducing.specializes_iff
- \+ *lemma* subtype_specializes_iff
- \+ *lemma* continuous.specialization_monotone
- \+ *lemma* inseparable_def
- \+/\- *lemma* inseparable_iff_specializes_and
- \+ *lemma* inseparable.specializes
- \+ *lemma* inseparable.specializes'
- \+ *lemma* specializes.antisymm
- \+ *lemma* inseparable_iff_forall_open
- \+ *lemma* not_inseparable_iff_exists_open
- \+ *lemma* inseparable_iff_forall_closed
- \+ *lemma* inseparable_iff_mem_closure
- \+ *lemma* inseparable_iff_closure_eq
- \+ *lemma* inseparable_of_nhds_within_eq
- \+ *lemma* inducing.inseparable_iff
- \+/\- *lemma* subtype_inseparable_iff
- \+ *lemma* refl
- \+ *lemma* rfl
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* nhds_eq
- \+ *lemma* mem_open_iff
- \+ *lemma* mem_closed_iff
- \+ *lemma* map_of_continuous_at
- \+ *lemma* map
- \+ *lemma* is_closed.not_inseparable
- \+ *lemma* is_open.not_inseparable
- \+ *lemma* quotient_map_mk
- \+ *lemma* continuous_mk
- \+ *lemma* mk_eq_mk
- \+ *lemma* surjective_mk
- \+ *lemma* range_mk
- \+ *lemma* preimage_image_mk_open
- \+ *lemma* is_open_map_mk
- \+ *lemma* preimage_image_mk_closed
- \+ *lemma* inducing_mk
- \+ *lemma* is_closed_map_mk
- \+ *lemma* map_mk_nhds
- \- *lemma* specializes_def
- \+/\- *lemma* specializes_iff_closure_subset
- \+/\- *lemma* specializes_rfl
- \+/\- *lemma* specializes_refl
- \+/\- *lemma* specializes.trans
- \+/\- *lemma* specializes_iff_forall_closed
- \+/\- *lemma* specializes_iff_forall_open
- \+/\- *lemma* specializes.map
- \- *lemma* specialization_order.monotone_of_continuous
- \- *lemma* inseparable_iff_nhds_eq
- \- *lemma* inseparable.map
- \- *lemma* inseparable_iff_closed
- \- *lemma* inseparable_iff_closure
- \+/\- *lemma* inseparable_iff_specializes_and
- \+/\- *lemma* subtype_inseparable_iff
- \+/\- *def* specializes
- \+/\- *def* inseparable
- \+ *def* inseparable_setoid
- \+ *def* separation_quotient
- \+ *def* mk
- \+/\- *def* specializes
- \+/\- *def* inseparable

modified src/topology/metric_space/emetric_space.lean

modified src/topology/separation.lean
- \- *lemma* specializes_antisymm
- \+/\- *def* specialization_order
- \+/\- *def* specialization_order

modified src/topology/sets/opens.lean

modified src/topology/sober.lean



## [2022-06-27 19:03:59](https://github.com/leanprover-community/mathlib/commit/1cd2bf5)
feat(analysis/special_functions/log/deriv): more power series for log ([#14881](https://github.com/leanprover-community/mathlib/pull/14881))
This adds a power series expansion for `log ((a + 1) / a)`, and two lemmas that are needed for it. It's planned to be used in the proof of the Stirling formula.
#### Estimated changes
modified src/analysis/special_functions/log/deriv.lean
- \+ *lemma* has_sum_log_sub_log_of_abs_lt_1
- \+ *theorem* has_sum_log_one_add_inv



## [2022-06-27 16:25:12](https://github.com/leanprover-community/mathlib/commit/68e0160)
chore(data/int/cast): redo [#14890](https://github.com/leanprover-community/mathlib/pull/14890), moving field-specific lemmas ([#14995](https://github.com/leanprover-community/mathlib/pull/14995))
In [#14894](https://github.com/leanprover-community/mathlib/pull/14894), I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.defs`.
Apparently this dependency was re-added, so I'm going to have to split it again...
#### Estimated changes
modified src/data/int/cast.lean
- \- *lemma* cast_neg_nat_cast

modified src/data/int/cast_field.lean
- \+ *lemma* cast_neg_nat_cast



## [2022-06-27 16:25:11](https://github.com/leanprover-community/mathlib/commit/2558b3b)
feat(*): Upgrade to lean 3.44.1c ([#14984](https://github.com/leanprover-community/mathlib/pull/14984))
The changes are:
* `reflected a` is now spelt `reflected _ a`, as the argument was made explicit to resolve type resolution issues. We need to add new instances for `with_top` and `with_bot` as these are no longer found via the `option` instance. These new instances are an improvement, as they can now use `bot` and `top` instead of `none`.
* Some nat order lemmas in core have been renamed or had their argument explicitness adjusted.
* `dsimp` now applies `iff` lemmas, which means it can end up making more progress than it used to. This appears to impact `split_ifs` too.
* `opposite.op_inj_iff` shouldn't be proved until after `opposite` is irreducible (where `iff.rfl` no longer works as a proof), otherwise `dsimp` is tricked into unfolding the irreducibility which puts the goal state in a form where no further lemmas can apply.
We skip Lean 3.44.0c because the support in that version for `iff` lemmas in `dsimp` had some unintended consequences which required many undesirable changes.
#### Estimated changes
modified archive/100-theorems-list/45_partition.lean

modified leanpkg.toml

modified src/algebra/geom_sum.lean

modified src/algebraic_geometry/gluing.lean

modified src/algebraic_topology/simplex_category.lean

modified src/combinatorics/simple_graph/regularity/bound.lean

modified src/data/fin/tuple/basic.lean

modified src/data/fin/vec_notation.lean

modified src/data/int/basic.lean

modified src/data/list/basic.lean

modified src/data/list/sigma.lean

modified src/data/matrix/pequiv.lean

modified src/data/nat/basic.lean

modified src/data/nat/log.lean

modified src/data/nat/pow.lean

modified src/data/num/lemmas.lean

modified src/data/opposite.lean
- \+/\- *lemma* op_inj_iff
- \+/\- *lemma* unop_inj_iff
- \+/\- *lemma* op_inj_iff
- \+/\- *lemma* unop_inj_iff

modified src/data/rat/defs.lean

modified src/data/sigma/basic.lean

modified src/data/vector/basic.lean

modified src/dynamics/periodic_pts.lean

modified src/linear_algebra/projective_space/basic.lean

modified src/meta/univs.lean

modified src/number_theory/dioph.lean

modified src/number_theory/legendre_symbol/gauss_eisenstein_lemmas.lean

modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean

modified src/number_theory/primorial.lean

modified src/number_theory/sum_four_squares.lean

modified src/order/bounded_order.lean

modified src/order/filter/at_top_bot.lean

modified src/order/galois_connection.lean

modified src/set_theory/ordinal/arithmetic.lean

modified src/tactic/core.lean

modified src/tactic/doc_commands.lean

modified src/tactic/fix_reflect_string.lean

modified src/tactic/linarith/datatypes.lean

modified src/tactic/local_cache.lean

modified src/tactic/omega/term.lean

modified src/tactic/replacer.lean

modified src/topology/discrete_quotient.lean

modified src/topology/uniform_space/basic.lean



## [2022-06-27 13:50:22](https://github.com/leanprover-community/mathlib/commit/05565f4)
doc(analysis/convex/uniform_convex_space): End of sentence ([#14986](https://github.com/leanprover-community/mathlib/pull/14986))
I kept the suspense for a month.
#### Estimated changes
modified src/analysis/convex/uniform.lean



## [2022-06-27 13:50:15](https://github.com/leanprover-community/mathlib/commit/5de7c34)
feat(order/*): Miscellaneous results about the product order ([#14977](https://github.com/leanprover-community/mathlib/pull/14977))
`≤`, `<`, `⩿`, `⋖`, `is_bot`, `is_top`, `is_min`, `is_max` in `α × β`.
#### Estimated changes
modified src/order/basic.lean
- \+/\- *lemma* swap_lt_swap
- \+ *lemma* mk_le_mk_iff_left
- \+ *lemma* mk_le_mk_iff_right
- \+ *lemma* mk_lt_mk_iff_left
- \+ *lemma* mk_lt_mk_iff_right
- \+/\- *lemma* lt_iff
- \+/\- *lemma* mk_lt_mk
- \+/\- *lemma* swap_lt_swap
- \+/\- *lemma* lt_iff
- \+/\- *lemma* mk_lt_mk

modified src/order/cover.lean
- \+ *lemma* swap_wcovby_swap
- \+ *lemma* swap_covby_swap
- \+ *lemma* fst_eq_or_snd_eq_of_wcovby
- \+ *lemma* _root_.wcovby.fst
- \+ *lemma* _root_.wcovby.snd
- \+ *lemma* mk_wcovby_mk_iff_left
- \+ *lemma* mk_wcovby_mk_iff_right
- \+ *lemma* mk_covby_mk_iff_left
- \+ *lemma* mk_covby_mk_iff_right
- \+ *lemma* mk_wcovby_mk_iff
- \+ *lemma* mk_covby_mk_iff
- \+ *lemma* wcovby_iff
- \+ *lemma* covby_iff

modified src/order/max.lean
- \+ *lemma* is_bot.prod_mk
- \+ *lemma* is_top.prod_mk
- \+ *lemma* is_min.prod_mk
- \+ *lemma* is_max.prod_mk
- \+ *lemma* is_bot.fst
- \+ *lemma* is_bot.snd
- \+ *lemma* is_top.fst
- \+ *lemma* is_top.snd
- \+ *lemma* is_min.fst
- \+ *lemma* is_min.snd
- \+ *lemma* is_max.fst
- \+ *lemma* is_max.snd
- \+ *lemma* prod.is_bot_iff
- \+ *lemma* prod.is_top_iff
- \+ *lemma* prod.is_min_iff
- \+ *lemma* prod.is_max_iff



## [2022-06-27 13:50:14](https://github.com/leanprover-community/mathlib/commit/f5d2cc8)
feat(measure_theory/function/l1_space): add some integrability lemmas ([#14931](https://github.com/leanprover-community/mathlib/pull/14931))
#### Estimated changes
modified src/analysis/normed_space/lattice_ordered_group.lean
- \+ *lemma* norm_inf_le_add
- \+ *lemma* norm_sup_le_add

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* integrable.inf
- \+ *lemma* integrable.sup
- \+/\- *lemma* integrable.abs
- \+ *lemma* integrable.bdd_mul
- \+/\- *lemma* integrable.abs

modified src/measure_theory/function/lp_order.lean
- \+ *lemma* _root_.measure_theory.mem_ℒp.sup
- \+ *lemma* _root_.measure_theory.mem_ℒp.inf
- \+ *lemma* _root_.measure_theory.mem_ℒp.abs



## [2022-06-27 13:50:13](https://github.com/leanprover-community/mathlib/commit/cf8b46d)
feat(analysis/convex/special_functions): `sqrt * log` is strictly convex on x>1 ([#14822](https://github.com/leanprover-community/mathlib/pull/14822))
This convexity result can be used to golf the proof of the main inequality in the proof of Bertrand's postulate ([#8002](https://github.com/leanprover-community/mathlib/pull/8002)).
#### Estimated changes
modified src/analysis/convex/specific_functions.lean
- \+ *lemma* deriv_sqrt_mul_log
- \+ *lemma* deriv2_sqrt_mul_log
- \+ *lemma* strict_concave_on_sqrt_mul_log_Ioi



## [2022-06-27 13:50:12](https://github.com/leanprover-community/mathlib/commit/68d29f5)
feat(probability/stopping): measurability of sets related to stopping times, under countable/encodable assumptions ([#14750](https://github.com/leanprover-community/mathlib/pull/14750))
The file already contains similar lemmas under assumptions on the topology of the index set. The new results use countability hypotheses instead.
#### Estimated changes
modified src/probability/stopping.lean



## [2022-06-27 11:38:35](https://github.com/leanprover-community/mathlib/commit/331df5a)
feat(probability/moments): moments and moment generating function of a real random variable ([#14755](https://github.com/leanprover-community/mathlib/pull/14755))
This PR defines moments, central moments, moment generating function and cumulant generating function.
#### Estimated changes
created src/probability/moments.lean
- \+ *lemma* moment_zero
- \+ *lemma* central_moment_zero
- \+ *lemma* central_moment_one'
- \+ *lemma* central_moment_one
- \+ *lemma* central_moment_two_eq_variance
- \+ *lemma* mgf_zero_fun
- \+ *lemma* cgf_zero_fun
- \+ *lemma* mgf_zero_measure
- \+ *lemma* cgf_zero_measure
- \+ *lemma* mgf_const'
- \+ *lemma* mgf_const
- \+ *lemma* cgf_const'
- \+ *lemma* cgf_const
- \+ *lemma* mgf_zero'
- \+ *lemma* mgf_zero
- \+ *lemma* cgf_zero'
- \+ *lemma* cgf_zero
- \+ *lemma* mgf_undef
- \+ *lemma* cgf_undef
- \+ *lemma* mgf_nonneg
- \+ *lemma* mgf_pos'
- \+ *lemma* mgf_pos
- \+ *lemma* indep_fun.mgf_add
- \+ *lemma* indep_fun.cgf_add
- \+ *def* moment
- \+ *def* central_moment
- \+ *def* mgf
- \+ *def* cgf



## [2022-06-27 11:38:34](https://github.com/leanprover-community/mathlib/commit/3091b91)
feat(probability/stopping): if a filtration is sigma finite, then the measure restricted to the sigma algebra generated by a stopping time is sigma finite ([#14752](https://github.com/leanprover-community/mathlib/pull/14752))
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* sigma_finite_trim_mono

modified src/probability/stopping.lean



## [2022-06-27 11:38:33](https://github.com/leanprover-community/mathlib/commit/72fbe5c)
feat(measure_theory/measure/finite_measure_weak_convergence): Characterize weak convergence of finite measures in terms of integrals of bounded continuous real-valued functions. ([#14578](https://github.com/leanprover-community/mathlib/pull/14578))
Weak convergence of measures was defined in terms of integrals of bounded continuous nnreal-valued functions. This PR shows the equivalence to the textbook condition in terms of integrals of bounded continuous real-valued functions.
Also the file `measure_theory/measure/finite_measure_weak_convergence.lean` is divided to sections with dosctrings for clarity.
#### Estimated changes
modified src/algebra/order/ring.lean
- \+ *lemma* max_zero_add_max_neg_zero_eq_abs_self

modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *lemma* integrable_of_bounded_continuous_to_nnreal
- \+ *lemma* integrable_of_bounded_continuous_to_real
- \+ *lemma* _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub
- \+ *lemma* lintegral_lt_top_of_bounded_continuous_to_real
- \+ *lemma* _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral
- \- *lemma* lintegral_lt_top_of_bounded_continuous_to_nnreal
- \- *lemma* lintegral_lt_top_of_bounded_continuous_to_nnreal
- \+ *theorem* tendsto_of_forall_integral_tendsto
- \+ *theorem* tendsto_iff_forall_integral_tendsto
- \+ *theorem* tendsto_iff_forall_integral_tendsto
- \+ *def* _root_.measure_theory.finite_measure
- \- *def* finite_measure

modified src/topology/continuous_function/bounded.lean
- \+ *lemma* nnreal_part_coe_fun_eq
- \+ *lemma* nnnorm_coe_fun_eq
- \+ *lemma* self_eq_nnreal_part_sub_nnreal_part_neg
- \+ *lemma* abs_self_eq_nnreal_part_add_nnreal_part_neg
- \+ *def* nnreal_part
- \+ *def* nnnorm



## [2022-06-27 09:14:45](https://github.com/leanprover-community/mathlib/commit/cf0649c)
chore(data/sigma/basic): make `sigma.reflect` universe-polymorphic ([#14934](https://github.com/leanprover-community/mathlib/pull/14934))
#### Estimated changes
modified src/data/sigma/basic.lean



## [2022-06-27 07:39:57](https://github.com/leanprover-community/mathlib/commit/671c7c0)
chore(algebra/direct_sum/ring): add new `int_cast` and `nat_cast` fields to match `ring` and `semiring` ([#14976](https://github.com/leanprover-community/mathlib/pull/14976))
This was deliberately left to a follow up in [#12182](https://github.com/leanprover-community/mathlib/pull/12182)
#### Estimated changes
modified src/algebra/direct_sum/internal.lean
- \+ *lemma* set_like.has_graded_one.nat_cast_mem
- \+ *lemma* set_like.has_graded_one.int_cast_mem

modified src/algebra/direct_sum/ring.lean



## [2022-06-27 07:39:56](https://github.com/leanprover-community/mathlib/commit/af8ca85)
fix(linear_algebra/{exterior,clifford}_algebra/basic): add some missing namespaces ([#14975](https://github.com/leanprover-community/mathlib/pull/14975))
These lemmas are about the auxiliary `{exterior,clifford}_algebra.graded_algebra.ι` not `{exterior,clifford}_algebra.ι`, so should have `graded_algebra` in their names.
This is a follow up to [#12182](https://github.com/leanprover-community/mathlib/pull/12182)
#### Estimated changes
modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* graded_algebra.lift_ι_eq
- \- *lemma* lift_ι_eq

modified src/linear_algebra/exterior_algebra/grading.lean
- \+ *lemma* graded_algebra.lift_ι_eq
- \- *lemma* lift_ι_eq
- \+ *def* graded_algebra.lift_ι
- \- *def* lift_ι



## [2022-06-27 04:03:50](https://github.com/leanprover-community/mathlib/commit/d4f8a45)
feat(algebra/group/units): add decidability instance for `is_unit` ([#14873](https://github.com/leanprover-community/mathlib/pull/14873))
This adds a decidability instance for the `is_unit` predicate. See [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Decidability.20of.20.60is_unit.60.20on.20finite.20rings/near/286543269).
#### Estimated changes
modified src/algebra/group/units.lean



## [2022-06-27 03:03:23](https://github.com/leanprover-community/mathlib/commit/0b18823)
feat(set_theory/game/pgame): make `lt_iff_le_and_lf` true by def-eq ([#14983](https://github.com/leanprover-community/mathlib/pull/14983))
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/ordinal.lean

modified src/set_theory/game/pgame.lean
- \+/\- *theorem* lt_iff_le_and_lf
- \+/\- *theorem* lt_of_le_of_lf
- \+/\- *theorem* lf_of_lt
- \+/\- *theorem* lt_iff_le_and_lf
- \+/\- *theorem* lt_of_le_of_lf
- \+/\- *theorem* lf_of_lt

modified src/set_theory/game/short.lean

modified src/set_theory/surreal/basic.lean



## [2022-06-27 00:09:16](https://github.com/leanprover-community/mathlib/commit/894f92b)
refactor(order/upper_lower): Reverse the order on `upper_set` ([#14982](https://github.com/leanprover-community/mathlib/pull/14982))
Having `upper_set` being ordered by reverse inclusion makes it order-isomorphic to `lower_set` (and antichains once we have them as a type) and it matches the order on `filter`.
#### Estimated changes
modified src/order/upper_lower.lean
- \+/\- *lemma* coe_top
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_sup
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂
- \+ *lemma* not_mem_top
- \+ *lemma* mem_bot
- \+/\- *lemma* mem_sup_iff
- \+/\- *lemma* mem_inf_iff
- \+/\- *lemma* mem_Sup_iff
- \+/\- *lemma* mem_Inf_iff
- \+/\- *lemma* mem_supr_iff
- \+/\- *lemma* mem_infi_iff
- \+/\- *lemma* mem_supr₂_iff
- \+/\- *lemma* mem_infi₂_iff
- \+ *lemma* compl_le_compl
- \+ *lemma* compl_le_compl
- \+ *lemma* Icoi_le_Ioi
- \+ *lemma* Ioi_top
- \+ *lemma* Ici_bot
- \+/\- *lemma* Ici_sup
- \+/\- *lemma* Ici_sup_hom_apply
- \+/\- *lemma* Ici_Sup
- \+/\- *lemma* Ici_supr
- \+/\- *lemma* Ici_supr₂
- \+/\- *lemma* coe_top
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_sup
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_supr
- \+/\- *lemma* coe_infi
- \+/\- *lemma* coe_supr₂
- \+/\- *lemma* coe_infi₂
- \- *lemma* mem_top
- \- *lemma* not_mem_bot
- \+/\- *lemma* mem_sup_iff
- \+/\- *lemma* mem_inf_iff
- \+/\- *lemma* mem_Sup_iff
- \+/\- *lemma* mem_Inf_iff
- \+/\- *lemma* mem_supr_iff
- \+/\- *lemma* mem_infi_iff
- \+/\- *lemma* mem_supr₂_iff
- \+/\- *lemma* mem_infi₂_iff
- \- *lemma* Ioi_le_Ici
- \- *lemma* Ici_top
- \- *lemma* Ioi_bot
- \+/\- *lemma* Ici_sup
- \+/\- *lemma* Ici_sup_hom_apply
- \+/\- *lemma* Ici_Sup
- \+/\- *lemma* Ici_supr
- \+/\- *lemma* Ici_supr₂
- \+ *def* upper_set_iso_lower_set
- \+/\- *def* Ici_sup_hom
- \+/\- *def* Ici_Sup_hom
- \+/\- *def* Ici_sup_hom
- \+/\- *def* Ici_Sup_hom



## [2022-06-26 23:29:19](https://github.com/leanprover-community/mathlib/commit/f63d925)
feat(combinatorics/simple_graph/clique): The set of cliques ([#14827](https://github.com/leanprover-community/mathlib/pull/14827))
Define `simple_graph.clique_set`, the `set` analogue to `simple_graph.clique_finset`.
#### Estimated changes
modified src/combinatorics/simple_graph/clique.lean
- \+ *lemma* mem_clique_set_iff
- \+ *lemma* clique_set_eq_empty_iff
- \+ *lemma* clique_set_mono
- \+ *lemma* clique_set_mono'
- \+/\- *lemma* mem_clique_finset_iff
- \+ *lemma* coe_clique_finset
- \+/\- *lemma* clique_finset_mono
- \+/\- *lemma* mem_clique_finset_iff
- \+/\- *lemma* clique_finset_mono
- \+ *def* clique_set



## [2022-06-26 21:36:44](https://github.com/leanprover-community/mathlib/commit/f2b108e)
refactor(set_theory/cardinal/*): `cardinal.sup` → `supr` ([#14569](https://github.com/leanprover-community/mathlib/pull/14569))
We remove `cardinal.sup` in favor of `supr`. We tweak many other theorems relating to cardinal suprema in the process.
A noteworthy consequence is that there's no longer universe constraints on the domain and codomain of the functions one takes the supremum of. When one does still have this constraint, one can use `bdd_above_range` to immediately prove their range is bounded above.
<!-- Lemmas `lift_sup_le`, `lift_sup_le_iff`, `lift_sup_le_lift_sup`, and `lift_sup_le_lift_sup'` have been removed by virtue of being trivial consequences of basic lemmas on suprema and `lift_supr`. -->
The result of this PR is the following replacements:
* `cardinal.sup` → `supr`
* `cardinal.le_sup` → `le_csupr`
* `cardinal.sup_le` → `csupr_le'`
* `cardinal.sup_le_sup` → `csupr_mono`
* `cardinal.sup_le_sum` → `cardinal.supr_le_sum`
* `cardinal.sum_le_sup` → `cardinal.sum_le_supr`
* `cardinal.sum_le_sup_lift` → `cardinal.sum_le_supr_lift`
* `cardinal.sup_eq_zero` → `cardinal.supr_of_empty`
* `cardinal.le_sup_iff` → `le_csupr_iff'`
* `cardinal.lift_sup` → `cardinal.lift_supr`
* `cardinal.lift_sup_le` → `cardinal.lift_supr` + `csupr_le'`
* `cardinal.lift_sup_le_iff` → `cardinal.lift_supr` + `csupr_le_iff`
* `cardinal.lift_sup_le_lift_sup` → `cardinal.lift_supr` + `csupr_le_iff'`
* `cardinal.lift_sup_le_lift_sup'` → `cardinal.lift_supr` + `csupr_mono'`
* `cardinal.sup_lt_lift` → `cardinal.supr_lt_lift`
* `cardinal.sup_lt` → `cardinal.supr_lt`
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/linear_algebra/dimension.lean

modified src/measure_theory/card_measurable_space.lean

modified src/model_theory/encoding.lean

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* le_csupr_iff'
- \+ *lemma* csupr_mono'

modified src/set_theory/cardinal/basic.lean
- \+ *lemma* lift_Sup
- \+ *lemma* lift_supr
- \+ *lemma* lift_supr_le
- \+ *lemma* lift_supr_le_iff
- \+ *lemma* lift_supr_le_lift_supr
- \+ *lemma* lift_supr_le_lift_supr'
- \+/\- *lemma* mk_Union_le
- \+/\- *lemma* mk_sUnion_le
- \+/\- *lemma* le_powerlt
- \+/\- *lemma* powerlt_le
- \+ *lemma* powerlt_mono_left
- \+/\- *lemma* powerlt_succ
- \+ *lemma* powerlt_min
- \+/\- *lemma* powerlt_max
- \+/\- *lemma* powerlt_zero
- \- *lemma* lift_sup
- \- *lemma* lift_sup_le
- \- *lemma* lift_sup_le_iff
- \- *lemma* lift_sup_le_lift_sup
- \- *lemma* lift_sup_le_lift_sup'
- \+/\- *lemma* mk_Union_le
- \+/\- *lemma* mk_sUnion_le
- \+/\- *lemma* le_powerlt
- \+/\- *lemma* powerlt_le
- \+/\- *lemma* powerlt_succ
- \+/\- *lemma* powerlt_max
- \+/\- *lemma* powerlt_zero
- \+/\- *theorem* bdd_above_iff_small
- \+ *theorem* bdd_above_image
- \+ *theorem* bdd_above_range_comp
- \+ *theorem* supr_le_sum
- \+ *theorem* sum_le_supr_lift
- \+ *theorem* sum_le_supr
- \+ *theorem* lift_infi
- \+/\- *theorem* bdd_above_iff_small
- \- *theorem* le_sup
- \- *theorem* sup_le_iff
- \- *theorem* sup_le
- \- *theorem* sup_le_sup
- \- *theorem* sup_le_sum
- \- *theorem* sum_le_sup
- \- *theorem* sum_le_sup_lift
- \- *theorem* sup_eq_zero
- \- *theorem* powerlt_aux
- \+/\- *def* powerlt
- \- *def* sup
- \+/\- *def* powerlt

modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* supr_lt_lift
- \+ *theorem* supr_lt
- \+ *theorem* supr_lt_lift_of_is_regular
- \+ *theorem* supr_lt_of_is_regular
- \- *theorem* sup_lt_lift
- \- *theorem* sup_lt
- \- *theorem* sup_lt_lift_of_is_regular
- \- *theorem* sup_lt_of_is_regular

modified src/set_theory/cardinal/ordinal.lean

modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* Sup_ord
- \+ *theorem* supr_ord
- \- *theorem* sup_ord



## [2022-06-26 19:48:44](https://github.com/leanprover-community/mathlib/commit/33112c4)
feat(data/nat/totient): more general multiplicativity lemmas for totient ([#14842](https://github.com/leanprover-community/mathlib/pull/14842))
Adds lemmas: 
`totient_gcd_mul_totient_mul : φ (a.gcd b) * φ (a * b) = φ a * φ b * (a.gcd b)`
`totient_super_multiplicative : φ a * φ b ≤ φ (a * b)`
`totient_gcd_mul_totient_mul` is Theorem 2.5(b) in Apostol (1976) Introduction to Analytic Number Theory.
Developed while reviewing @CBirkbeck 's [#14828](https://github.com/leanprover-community/mathlib/pull/14828)
#### Estimated changes
modified src/data/nat/totient.lean
- \+ *lemma* totient_gcd_mul_totient_mul
- \+ *lemma* totient_super_multiplicative

modified src/ring_theory/multiplicity.lean
- \+ *lemma* prod_factors_gcd_mul_prod_factors_mul



## [2022-06-26 18:50:48](https://github.com/leanprover-community/mathlib/commit/381733a)
feat(analysis/convex/stone_separation): Stone's separation theorem ([#14677](https://github.com/leanprover-community/mathlib/pull/14677))
Disjoint convexes can be separated by a convex whose complement is also convex.
#### Estimated changes
created src/analysis/convex/stone_separation.lean
- \+ *lemma* not_disjoint_segment_convex_hull_triple
- \+ *lemma* exists_convex_convex_compl_subset



## [2022-06-26 17:01:08](https://github.com/leanprover-community/mathlib/commit/4111ed9)
docs(linear_algebra/invariant_basis_number): Drop a TODO ([#14973](https://github.com/leanprover-community/mathlib/pull/14973))
This TODO was fixed some time ago by @riccardobrasca, reference the relevant instance in the docstring.
#### Estimated changes
modified src/linear_algebra/invariant_basis_number.lean



## [2022-06-26 17:01:07](https://github.com/leanprover-community/mathlib/commit/ca070dd)
feat(analysis/special_functions/trigonometric/angle): topology ([#14969](https://github.com/leanprover-community/mathlib/pull/14969))
Give `real.angle` the structure of a `topological_add_group` (rather
than just an `add_comm_group`), so that it's possible to talk about
continuity for functions involving this type, and add associated
continuity lemmas for `coe : ℝ → angle`, `real.angle.sin` and
`real.angle.cos`.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* continuous_coe
- \+ *lemma* continuous_sin
- \+ *lemma* continuous_cos



## [2022-06-26 17:01:06](https://github.com/leanprover-community/mathlib/commit/28a6f0a)
feat(set_theory/surreal/basic): add `numeric.mk` lemma, golf ([#14962](https://github.com/leanprover-community/mathlib/pull/14962))
#### Estimated changes
modified src/set_theory/surreal/basic.lean
- \+/\- *lemma* numeric_def
- \+ *lemma* mk
- \+ *lemma* left_lt_right
- \+ *lemma* move_left
- \+ *lemma* move_right
- \+ *lemma* sub
- \+/\- *lemma* numeric_def
- \- *lemma* numeric.left_lt_right
- \- *lemma* numeric.move_left
- \- *lemma* numeric.move_right
- \- *lemma* numeric.sub
- \+/\- *theorem* numeric_of_is_empty_left_moves
- \+ *theorem* move_left_lt
- \+ *theorem* move_left_le
- \+ *theorem* lt_move_right
- \+ *theorem* le_move_right
- \+ *theorem* add
- \+/\- *theorem* numeric_of_is_empty_left_moves
- \- *theorem* numeric.move_left_lt
- \- *theorem* numeric.move_left_le
- \- *theorem* numeric.lt_move_right
- \- *theorem* numeric.le_move_right
- \- *theorem* numeric.add



## [2022-06-26 17:01:05](https://github.com/leanprover-community/mathlib/commit/54352be)
feat(combinatorics/catalan): definition and equality of recursive and explicit definition ([#14869](https://github.com/leanprover-community/mathlib/pull/14869))
This PR defines the Catalan numbers via the recursive definition $$C (n+1) = \sum_{i=0}^n C (i) * C (n-i)$$. 
Furthermore, it shows that $$ n+1 | \binom {2n}{n}$$ and that the alternative $$C(n)=\frac{1}{n+1} \binom{2n}{n}$$ holds. 
The proof is based on the following stackexchange answer: https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation which is quite elementary, so that the proof is relatively easy to formalise.
#### Estimated changes
created src/combinatorics/catalan.lean
- \+ *lemma* catalan_zero
- \+ *lemma* catalan_succ
- \+ *lemma* catalan_one
- \+ *lemma* catalan_two
- \+ *lemma* catalan_three
- \+ *theorem* catalan_eq_central_binom_div
- \+ *theorem* succ_mul_catalan_eq_central_binom
- \+ *def* catalan

modified src/data/nat/choose/central.lean
- \+ *lemma* two_dvd_central_binom_succ
- \+ *lemma* two_dvd_central_binom_of_one_le
- \+ *lemma* succ_dvd_central_binom



## [2022-06-26 14:56:15](https://github.com/leanprover-community/mathlib/commit/ee7a886)
feat({data/{finset,set},order/filter}/pointwise): Missing `smul_comm_class` instances ([#14963](https://github.com/leanprover-community/mathlib/pull/14963))
Instances of the form `smul_comm_class α β (something γ)`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* map_comm
- \+ *lemma* image_comm

modified src/data/finset/pointwise.lean

modified src/data/set/pointwise.lean
- \+/\- *lemma* smul_set_mono
- \+ *lemma* smul_set_subset_iff
- \+/\- *lemma* smul_set_mono

modified src/order/filter/pointwise.lean



## [2022-06-26 12:02:17](https://github.com/leanprover-community/mathlib/commit/32b08ef)
feat: `add_monoid_with_one`, `add_group_with_one` ([#12182](https://github.com/leanprover-community/mathlib/pull/12182))
Adds two type classes `add_monoid_with_one R` and `add_group_with_one R` with operations for `ℕ → R` and `ℤ → R`, resp.  The type classes extend `add_monoid` and `add_group` because those seem to be the weakest type classes where such a `+₀₁`-homomorphism is guaranteed to exist.  The `nat.cast` function as well as `coe : ℕ → R` are implemented in terms of `add_monoid_with_one R`, removing the infamous `nat.cast` diamond.  Fixes [#946](https://github.com/leanprover-community/mathlib/pull/946).
Some lemmas are less general now because the algebraic hierarchy is not fine-grained enough, or because the lawful coercion only exists for monoids and above.  This generality was not used in mathlib as far as I could tell.  For example:
 - `char_p.char_p_to_char_zero` now requires a group instead of a left-cancellative monoid, because we don't have the `add_left_cancel_monoid_with_one` class
 - `nat.norm_cast_le` now requires a seminormed ring instead of a seminormed group, because we don't have `semi_normed_group_with_one`
#### Estimated changes
modified archive/100-theorems-list/16_abel_ruffini.lean

modified archive/100-theorems-list/30_ballot_problem.lean

modified archive/imo/imo2013_q5.lean

modified archive/imo/imo2019_q4.lean

modified counterexamples/phillips.lean

modified src/algebra/algebra/operations.lean

modified src/algebra/algebra/subalgebra/basic.lean

modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* cast_list_sum
- \+/\- *lemma* cast_multiset_sum
- \+/\- *lemma* cast_sum
- \+/\- *lemma* cast_list_sum
- \+/\- *lemma* cast_multiset_sum
- \+/\- *lemma* cast_sum
- \+/\- *lemma* cast_list_sum
- \+/\- *lemma* cast_multiset_sum
- \+/\- *lemma* cast_sum
- \+/\- *lemma* cast_list_sum
- \+/\- *lemma* cast_multiset_sum
- \+/\- *lemma* cast_sum

modified src/algebra/big_operators/pi.lean

modified src/algebra/category/Ring/colimits.lean

modified src/algebra/char_p/algebra.lean

modified src/algebra/char_p/basic.lean
- \+/\- *lemma* char_p.cast_card_eq_zero
- \+/\- *lemma* char_p.int_cast_eq_zero_iff
- \+/\- *lemma* char_p.int_coe_eq_int_coe_iff
- \+/\- *lemma* char_p_to_char_zero
- \+/\- *lemma* char_p.cast_card_eq_zero
- \+/\- *lemma* char_p.int_cast_eq_zero_iff
- \+/\- *lemma* char_p.int_coe_eq_int_coe_iff
- \+/\- *lemma* char_p_to_char_zero
- \+/\- *theorem* char_p.cast_eq_zero
- \+/\- *theorem* char_p.eq
- \+/\- *theorem* char_p.congr
- \+/\- *theorem* char_p.cast_eq_zero
- \+/\- *theorem* char_p.eq
- \+/\- *theorem* char_p.congr

modified src/algebra/char_p/char_and_card.lean

modified src/algebra/char_zero.lean
- \- *lemma* ordered_semiring.to_char_zero
- \- *lemma* cast_add_one_ne_zero
- \- *theorem* char_zero_of_inj_zero
- \- *theorem* cast_injective
- \- *theorem* cast_inj
- \- *theorem* cast_eq_zero
- \- *theorem* cast_eq_one
- \- *theorem* cast_ne_zero
- \- *theorem* cast_ne_one

created src/algebra/char_zero/defs.lean
- \+ *lemma* cast_add_one_ne_zero
- \+ *theorem* char_zero_of_inj_zero
- \+ *theorem* cast_injective
- \+ *theorem* cast_inj
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero
- \+ *theorem* cast_eq_one
- \+ *theorem* cast_ne_one

modified src/algebra/direct_sum/internal.lean

modified src/algebra/direct_sum/ring.lean
- \+ *lemma* of_nat_cast
- \+ *lemma* of_int_cast

modified src/algebra/field/basic.lean

modified src/algebra/group/inj_surj.lean

modified src/algebra/group/opposite.lean

modified src/algebra/group/ulift.lean

modified src/algebra/group/with_one.lean

modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* zsmul_one
- \+/\- *lemma* zsmul_one
- \+/\- *theorem* nsmul_one
- \+/\- *theorem* zsmul_eq_mul
- \+/\- *theorem* nsmul_one
- \+/\- *theorem* zsmul_eq_mul

modified src/algebra/group_with_zero/power.lean

modified src/algebra/hom/group_instances.lean

modified src/algebra/lie/universal_enveloping.lean

modified src/algebra/module/basic.lean
- \+/\- *lemma* char_zero.of_module
- \+/\- *lemma* char_zero.of_module

modified src/algebra/module/linear_map.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/algebra/ne_zero.lean
- \+/\- *lemma* ne_zero.ne'
- \+/\- *lemma* of_not_dvd
- \+/\- *lemma* of_ne_zero_coe
- \+/\- *lemma* not_char_dvd
- \+/\- *lemma* pos_of_ne_zero_coe
- \+/\- *lemma* ne_zero.ne'
- \+/\- *lemma* of_not_dvd
- \+/\- *lemma* of_ne_zero_coe
- \+/\- *lemma* not_char_dvd
- \+/\- *lemma* pos_of_ne_zero_coe

modified src/algebra/order/archimedean.lean

modified src/algebra/order/field.lean

modified src/algebra/order/floor.lean
- \+/\- *lemma* lt_floor_add_one
- \+/\- *lemma* floor_zero
- \+/\- *lemma* ceil_zero
- \+/\- *lemma* ceil_eq_zero
- \+/\- *lemma* floor_nonneg
- \+/\- *lemma* floor_zero
- \+/\- *lemma* floor_add_nat
- \+/\- *lemma* floor_nat_add
- \+/\- *lemma* floor_sub_nat
- \+/\- *lemma* ceil_pos
- \+/\- *lemma* ceil_zero
- \+/\- *lemma* lt_floor_add_one
- \+/\- *lemma* floor_zero
- \+/\- *lemma* ceil_zero
- \+/\- *lemma* ceil_eq_zero
- \+/\- *lemma* floor_nonneg
- \+/\- *lemma* floor_zero
- \+/\- *lemma* floor_add_nat
- \+/\- *lemma* floor_nat_add
- \+/\- *lemma* floor_sub_nat
- \+/\- *lemma* ceil_pos
- \+/\- *lemma* ceil_zero

modified src/algebra/order/module.lean

modified src/algebra/order/nonneg.lean

modified src/algebra/order/ring.lean
- \+ *lemma* ordered_semiring.to_char_zero
- \+ *theorem* nat.strict_mono_cast

modified src/algebra/punit_instances.lean

modified src/algebra/quaternion.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg

modified src/algebra/ring/basic.lean

modified src/algebra/ring/opposite.lean

modified src/algebra/ring/prod.lean

modified src/algebra/ring/ulift.lean

modified src/algebra/ring_quot.lean

modified src/algebra/squarefree.lean

modified src/algebra/star/self_adjoint.lean

modified src/algebra/triv_sq_zero_ext.lean
- \+ *lemma* fst_mk
- \+ *lemma* snd_mk

modified src/algebra/tropical/basic.lean

modified src/analysis/calculus/cont_diff.lean

modified src/analysis/complex/basic.lean

modified src/analysis/convex/specific_functions.lean

modified src/analysis/normed/field/basic.lean
- \+ *lemma* nat.norm_cast_le

modified src/analysis/normed/group/basic.lean
- \- *lemma* nat.norm_cast_le

modified src/analysis/normed_space/enorm.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/spectrum.lean

modified src/analysis/special_functions/gamma.lean

modified src/analysis/special_functions/integrals.lean

modified src/analysis/special_functions/pow.lean

modified src/analysis/special_functions/pow_deriv.lean

modified src/analysis/special_functions/trigonometric/basic.lean

modified src/analysis/special_functions/trigonometric/complex.lean

modified src/analysis/specific_limits/basic.lean

modified src/analysis/specific_limits/normed.lean

modified src/analysis/subadditive.lean

modified src/analysis/sum_integral_comparisons.lean

modified src/combinatorics/simple_graph/regularity/bound.lean

modified src/combinatorics/simple_graph/regularity/uniform.lean

modified src/computability/language.lean

modified src/computability/tm_to_partrec.lean
- \+/\- *theorem* tr_nat_zero
- \+ *theorem* tr_nat_default
- \+/\- *theorem* tr_nat_zero

modified src/data/complex/basic.lean

modified src/data/complex/exponential.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/fin/basic.lean

modified src/data/int/basic.lean
- \+/\- *lemma* coe_nat_nonneg
- \+ *lemma* neg_of_nat_ne_zero
- \+ *lemma* zero_ne_neg_of_nat
- \+/\- *lemma* coe_nat_nonneg
- \+/\- *theorem* coe_nat_pos
- \+/\- *theorem* coe_nat_eq_zero
- \+/\- *theorem* coe_nat_ne_zero
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* coe_nat_pos
- \+/\- *theorem* coe_nat_eq_zero
- \+/\- *theorem* coe_nat_ne_zero
- \+/\- *theorem* coe_nat_abs

modified src/data/int/cast.lean
- \+/\- *lemma* coe_cast_add_hom
- \+/\- *lemma* cast_commute
- \+ *lemma* cast_neg_nat_cast
- \+/\- *lemma* fst_int_cast
- \+/\- *lemma* snd_int_cast
- \+/\- *lemma* int_apply
- \+/\- *lemma* coe_int
- \+/\- *lemma* op_int_cast
- \+/\- *lemma* unop_int_cast
- \+/\- *lemma* coe_cast_add_hom
- \+/\- *lemma* cast_commute
- \- *lemma* cast_two
- \- *lemma* cast_three
- \- *lemma* cast_four
- \+/\- *lemma* fst_int_cast
- \+/\- *lemma* snd_int_cast
- \+/\- *lemma* int_apply
- \+/\- *lemma* coe_int
- \+/\- *lemma* op_int_cast
- \+/\- *lemma* unop_int_cast
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_ite
- \- *theorem* nat_cast_eq_coe_nat
- \- *theorem* cast_zero
- \- *theorem* cast_of_nat
- \- *theorem* cast_coe_nat
- \- *theorem* cast_coe_nat'
- \- *theorem* cast_neg_succ_of_nat
- \- *theorem* cast_one
- \- *theorem* cast_sub_nat_nat
- \- *theorem* cast_neg_of_nat
- \- *theorem* cast_add
- \- *theorem* cast_neg
- \- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_ite
- \- *theorem* coe_nat_bit0
- \- *theorem* coe_nat_bit1
- \- *theorem* cast_bit0
- \- *theorem* cast_bit1
- \+/\- *def* cast_add_hom
- \+/\- *def* cast_add_hom

created src/data/int/cast/defs.lean
- \+ *lemma* neg_of_nat_eq
- \+ *lemma* cast_two
- \+ *lemma* cast_three
- \+ *lemma* cast_four
- \+ *theorem* cast_sub
- \+ *theorem* cast_pred
- \+ *theorem* cast_of_nat
- \+ *theorem* cast_neg_succ_of_nat
- \+ *theorem* cast_zero
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_one
- \+ *theorem* cast_neg
- \+ *theorem* cast_sub_nat_nat
- \+ *theorem* cast_neg_of_nat
- \+ *theorem* cast_add
- \+ *theorem* cast_sub
- \+ *theorem* coe_nat_bit0
- \+ *theorem* coe_nat_bit1
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1

modified src/data/int/char_zero.lean
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_injective
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_injective
- \+/\- *theorem* cast_ne_zero

modified src/data/int/interval.lean

modified src/data/matrix/basic.lean
- \+ *theorem* diagonal_eq_diagonal_iff

modified src/data/mv_polynomial/basic.lean

modified src/data/nat/basic.lean

modified src/data/nat/cast.lean
- \+/\- *lemma* coe_cast_add_monoid_hom
- \+/\- *lemma* ext_nat'
- \+/\- *lemma* add_monoid_hom.ext_nat
- \+/\- *lemma* map_nat_cast'
- \+/\- *lemma* nat.cast_ring_hom_nat
- \+/\- *lemma* op_nat_cast
- \+/\- *lemma* unop_nat_cast
- \+/\- *lemma* nat_apply
- \+/\- *lemma* coe_nat
- \- *lemma* bin_cast_eq
- \+/\- *lemma* coe_cast_add_monoid_hom
- \- *lemma* cast_two
- \+/\- *lemma* ext_nat'
- \+/\- *lemma* add_monoid_hom.ext_nat
- \+/\- *lemma* map_nat_cast'
- \+/\- *lemma* nat.cast_ring_hom_nat
- \+/\- *lemma* op_nat_cast
- \+/\- *lemma* unop_nat_cast
- \+/\- *lemma* nat_apply
- \+/\- *lemma* coe_nat
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* nat.cast_with_bot
- \- *theorem* cast_zero
- \- *theorem* cast_add_one
- \- *theorem* cast_succ
- \- *theorem* cast_ite
- \- *theorem* cast_one
- \- *theorem* cast_add
- \- *theorem* cast_bit0
- \- *theorem* cast_bit1
- \- *theorem* cast_pred
- \- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_nonneg
- \- *theorem* strict_mono_cast
- \+/\- *theorem* nat.cast_with_bot
- \+/\- *def* cast_add_monoid_hom
- \+/\- *def* cast_add_monoid_hom

created src/data/nat/cast/defs.lean
- \+ *lemma* bin_cast_eq
- \+ *lemma* cast_two
- \+ *theorem* cast_zero
- \+ *theorem* cast_succ
- \+ *theorem* cast_add_one
- \+ *theorem* cast_ite
- \+ *theorem* cast_one
- \+ *theorem* cast_add
- \+ *theorem* cast_bit0
- \+ *theorem* cast_bit1

modified src/data/nat/choose/sum.lean

modified src/data/nat/digits.lean

modified src/data/nat/enat.lean
- \+/\- *lemma* some_eq_coe
- \+/\- *lemma* coe_inj
- \+/\- *lemma* dom_coe
- \+/\- *lemma* some_eq_coe
- \+/\- *lemma* coe_inj
- \+/\- *lemma* dom_coe

modified src/data/num/lemmas.lean
- \+ *lemma* of_nat'_zero
- \+ *lemma* of_nat'_bit
- \+ *lemma* of_nat'_one
- \+ *lemma* bit1_succ
- \+ *lemma* of_nat'_succ
- \+/\- *theorem* cast_to_nat
- \+/\- *theorem* cast_to_int
- \+ *theorem* add_of_nat'
- \+/\- *theorem* cast_to_nat
- \+ *theorem* of_to_nat'
- \+ *theorem* of_to_nat'
- \+/\- *theorem* add_of_nat
- \+/\- *theorem* to_nat_to_int
- \+/\- *theorem* cast_to_int
- \+/\- *theorem* to_of_nat
- \+/\- *theorem* of_nat_cast
- \+/\- *theorem* of_nat_inj
- \+/\- *theorem* of_to_nat
- \+/\- *theorem* of_to_nat
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_succ'
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_to_int
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_bitm1
- \+/\- *theorem* cast_sub'
- \+/\- *theorem* cast_sub'
- \+ *theorem* to_znum_succ
- \+ *theorem* to_znum_neg_succ
- \+ *theorem* pred_succ
- \+ *theorem* succ_of_int'
- \+ *theorem* of_int'_to_znum
- \+/\- *theorem* cast_of_znum
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_succ
- \+ *theorem* of_int'_neg
- \+ *theorem* of_to_int'
- \+ *theorem* cast_sub
- \+/\- *theorem* neg_of_int
- \+/\- *theorem* of_int'_eq
- \+/\- *theorem* of_nat_to_znum
- \+/\- *theorem* of_to_int
- \+/\- *theorem* to_of_int
- \+/\- *theorem* of_nat_to_znum_neg
- \+/\- *theorem* of_int_cast
- \+/\- *theorem* of_nat_cast
- \+/\- *theorem* cast_to_nat
- \+/\- *theorem* cast_to_int
- \+/\- *theorem* add_of_nat
- \+/\- *theorem* cast_to_nat
- \+/\- *theorem* to_nat_to_int
- \+/\- *theorem* cast_to_int
- \+/\- *theorem* to_of_nat
- \+/\- *theorem* of_nat_cast
- \+/\- *theorem* of_nat_inj
- \+/\- *theorem* of_to_nat
- \+/\- *theorem* of_to_nat
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_succ'
- \+/\- *theorem* cast_succ
- \- *theorem* of_nat'_zero
- \+/\- *theorem* neg_of_int
- \+/\- *theorem* cast_to_int
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_bitm1
- \+/\- *theorem* cast_sub'
- \+/\- *theorem* cast_sub'
- \+/\- *theorem* of_nat_to_znum
- \+/\- *theorem* of_nat_to_znum_neg
- \+/\- *theorem* cast_of_znum
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_succ
- \+/\- *theorem* of_to_int
- \+/\- *theorem* to_of_int
- \+/\- *theorem* of_int_cast
- \+/\- *theorem* of_nat_cast
- \+/\- *theorem* of_int'_eq

modified src/data/polynomial/basic.lean

modified src/data/polynomial/derivative.lean

modified src/data/polynomial/laurent.lean

modified src/data/rat/cast.lean
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_coe_nat

modified src/data/rat/defs.lean
- \+/\- *theorem* coe_int_eq_mk
- \+/\- *theorem* coe_int_eq_mk

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/real/cau_seq_completion.lean

modified src/data/real/ennreal.lean

modified src/data/real/irrational.lean
- \+/\- *theorem* ne_zero
- \+/\- *theorem* ne_zero

modified src/data/real/pi/leibniz.lean

modified src/data/zmod/basic.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/field_theory/adjoin.lean

modified src/field_theory/intermediate_field.lean
- \+ *lemma* coe_nat_mem

modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/perfect_closure.lean
- \+ *lemma* mk_zero_zero

modified src/field_theory/ratfunc.lean

modified src/field_theory/subfield.lean

modified src/geometry/euclidean/basic.lean

modified src/geometry/euclidean/triangle.lean

modified src/geometry/manifold/instances/sphere.lean
- \+ *lemma* stereographic_apply
- \+ *lemma* sphere_ext_iff
- \+ *lemma* stereographic'_symm_apply

modified src/group_theory/p_group.lean

modified src/group_theory/perm/cycle/type.lean

modified src/group_theory/specific_groups/dihedral.lean

modified src/group_theory/specific_groups/quaternion.lean

modified src/linear_algebra/clifford_algebra/grading.lean
- \+ *lemma* lift_ι_eq

modified src/linear_algebra/dual.lean

modified src/linear_algebra/eigenspace.lean

modified src/linear_algebra/exterior_algebra/grading.lean
- \+ *lemma* lift_ι_eq
- \+ *def* lift_ι

modified src/linear_algebra/linear_independent.lean

modified src/linear_algebra/matrix/trace.lean

modified src/linear_algebra/matrix/zpow.lean

modified src/linear_algebra/quadratic_form/complex.lean

modified src/logic/equiv/transfer_instance.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/measure/haar.lean

modified src/measure_theory/probability_mass_function/constructions.lean

modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat_coe_apply
- \+/\- *lemma* int_coe_apply
- \+/\- *lemma* coe_coe
- \+/\- *lemma* nat_coe_one
- \+/\- *lemma* int_coe_one
- \+/\- *lemma* nat_coe_apply
- \+/\- *lemma* int_coe_apply
- \+/\- *lemma* coe_coe
- \+/\- *lemma* nat_coe_one
- \+/\- *lemma* int_coe_one

modified src/number_theory/bernoulli.lean

modified src/number_theory/bernoulli_polynomials.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/dioph.lean

modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean

modified src/number_theory/liouville/basic.lean

modified src/number_theory/liouville/measure.lean

modified src/number_theory/liouville/residual.lean

modified src/number_theory/lucas_lehmer.lean
- \+/\- *lemma* nat_coe_fst
- \+/\- *lemma* nat_coe_snd
- \+/\- *lemma* int_coe_fst
- \+/\- *lemma* int_coe_snd
- \+/\- *lemma* nat_coe_fst
- \+/\- *lemma* nat_coe_snd
- \+/\- *lemma* int_coe_fst
- \+/\- *lemma* int_coe_snd

modified src/number_theory/modular.lean

modified src/number_theory/padics/padic_integers.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_coe_int
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_coe_int
- \+/\- *lemma* coe_zero

modified src/number_theory/padics/padic_numbers.lean

modified src/number_theory/padics/ring_homs.lean

modified src/number_theory/pell.lean

modified src/number_theory/sum_four_squares.lean

modified src/number_theory/zsqrtd/basic.lean
- \+/\- *theorem* coe_nat_re
- \+/\- *theorem* coe_nat_im
- \+/\- *theorem* coe_nat_val
- \+/\- *theorem* coe_nat_re
- \+/\- *theorem* coe_nat_im
- \+/\- *theorem* coe_nat_val

modified src/number_theory/zsqrtd/gaussian_int.lean
- \+/\- *lemma* coe_nat_abs_norm
- \+/\- *lemma* coe_nat_abs_norm

modified src/order/filter/archimedean.lean

modified src/order/filter/germ.lean

modified src/probability/strong_law.lean

modified src/ring_theory/dedekind_domain/ideal.lean

modified src/ring_theory/discriminant.lean

modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_nat_cast

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/graded_algebra/basic.lean
- \+/\- *lemma* graded_algebra.mem_support_iff
- \+/\- *lemma* graded_algebra.mem_support_iff

modified src/ring_theory/graded_algebra/homogeneous_localization.lean
- \+ *lemma* nat_cast_val
- \+ *lemma* int_cast_val

modified src/ring_theory/hahn_series.lean

modified src/ring_theory/ideal/quotient.lean

modified src/ring_theory/int/basic.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/laurent_series.lean

modified src/ring_theory/nullstellensatz.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/polynomial/cyclotomic/eval.lean

modified src/ring_theory/polynomial/eisenstein.lean

modified src/ring_theory/polynomial/pochhammer.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/subring/basic.lean

modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* nat_cast_mem

modified src/ring_theory/tensor_product.lean

modified src/ring_theory/witt_vector/basic.lean
- \+ *lemma* nat_cast
- \+ *lemma* int_cast
- \- *def* map
- \- *def* constant_coeff

modified src/ring_theory/witt_vector/defs.lean

modified src/ring_theory/witt_vector/frobenius.lean

modified src/ring_theory/witt_vector/frobenius_fraction_field.lean
- \+ *lemma* exists_frobenius_solution_fraction_ring_aux
- \+/\- *lemma* exists_frobenius_solution_fraction_ring
- \+/\- *lemma* exists_frobenius_solution_fraction_ring

modified src/ring_theory/witt_vector/mul_coeff.lean

modified src/ring_theory/witt_vector/structure_polynomial.lean

modified src/ring_theory/witt_vector/truncated.lean
- \+ *lemma* truncate_fun_nat_cast
- \+ *lemma* truncate_fun_int_cast
- \- *def* truncate

modified src/ring_theory/witt_vector/verschiebung.lean

modified src/ring_theory/witt_vector/witt_polynomial.lean

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/game/basic.lean

modified src/set_theory/game/pgame.lean
- \- *theorem* nat_one

modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* card_nat
- \+/\- *theorem* card_nat

modified src/set_theory/ordinal/natural_ops.lean

modified src/set_theory/surreal/basic.lean

modified src/set_theory/surreal/dyadic.lean

modified src/tactic/norm_cast.lean

modified src/tactic/norm_num.lean

modified src/tactic/zify.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/continuous_function/algebra.lean
- \+ *lemma* coe_nat_cast
- \+ *lemma* coe_int_cast

modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_nat_cast
- \+ *lemma* coe_int_cast

modified src/topology/continuous_function/compact.lean

modified src/topology/locally_constant/algebra.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/completion.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/path_connected.lean

modified test/norm_cast.lean

modified test/norm_cast_lemma_order.lean

modified test/norm_cast_sum_lambda.lean

modified test/norm_num.lean

modified test/transport/basic.lean

modified test/zify.lean



## [2022-06-26 08:42:14](https://github.com/leanprover-community/mathlib/commit/871fcd8)
feat(data/zmod/algebra): add subsingleton instance for zmod-algebras ([#14946](https://github.com/leanprover-community/mathlib/pull/14946))
This will be used to eliminate a diamond with `galois_field.algebra` in a followup PR.
#### Estimated changes
modified src/data/zmod/algebra.lean



## [2022-06-26 08:01:37](https://github.com/leanprover-community/mathlib/commit/e0ecaa9)
feat(set_theory/ordinal/notation): fast growing hierarchy ([#14072](https://github.com/leanprover-community/mathlib/pull/14072))
Adds a definition `onote.fast_growing` which yields elements of the [fast-growing hierarchy](https://en.wikipedia.org/wiki/Fast-growing_hierarchy) up to and including ε₀. Because it is built on `onote` instead of `ordinal`, the definition is fully computable, and you can work out some small elements. For example `fast_growing_ε₀ 2 = 2048` and `fast_growing_ε₀ 3` is... big.
#### Estimated changes
modified src/set_theory/ordinal/notation.lean
- \+ *theorem* fundamental_sequence_has_prop
- \+ *theorem* fast_growing_def
- \+ *theorem* fast_growing_zero'
- \+ *theorem* fast_growing_succ
- \+ *theorem* fast_growing_limit
- \+ *theorem* fast_growing_zero
- \+ *theorem* fast_growing_one
- \+ *theorem* fast_growing_two
- \+ *theorem* fast_growing_ε₀_zero
- \+ *theorem* fast_growing_ε₀_one
- \+ *theorem* fast_growing_ε₀_two
- \+ *def* fundamental_sequence
- \+ *def* fundamental_sequence_prop
- \+ *def* fast_growing
- \+ *def* fast_growing_ε₀



## [2022-06-26 04:37:04](https://github.com/leanprover-community/mathlib/commit/cfbb97f)
feat(data/{finset,set}/basic): More `∪`/`∩` laws ([#14952](https://github.com/leanprover-community/mathlib/pull/14952))
Specialise lattice lemmas to `set` and `finset`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* union_union_distrib_left
- \+ *lemma* union_union_distrib_right
- \+ *lemma* inter_inter_distrib_left
- \+ *lemma* inter_inter_distrib_right
- \+ *lemma* union_union_union_comm
- \+ *lemma* inter_inter_inter_comm

modified src/data/set/basic.lean
- \+ *lemma* union_union_distrib_left
- \+ *lemma* union_union_distrib_right
- \+ *lemma* inter_inter_distrib_left
- \+ *lemma* inter_inter_distrib_right
- \+ *lemma* union_union_union_comm
- \+ *lemma* inter_inter_inter_comm



## [2022-06-26 04:37:03](https://github.com/leanprover-community/mathlib/commit/ccb1cf3)
feat(data/set/lattice): Preimages are disjoint iff the sets are disjoint ([#14951](https://github.com/leanprover-community/mathlib/pull/14951))
Prove `disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ disjoint s t` and `disjoint (f '' s) (f '' t) ↔ disjoint s t` when `f` is surjective/injective. Delete `set.disjoint_preimage` in favor of `disjoint.preimage`. Fix the statement of `set.preimage_eq_empty_iff` (the name referred to the RHS).
#### Estimated changes
modified src/data/set/lattice.lean
- \+ *lemma* _root_.disjoint.inter_eq
- \+ *lemma* _root_.disjoint.of_image
- \+ *lemma* disjoint_image_iff
- \+ *lemma* _root_.disjoint.of_preimage
- \+ *lemma* disjoint_preimage_iff
- \+/\- *lemma* preimage_eq_empty_iff
- \- *lemma* disjoint_preimage
- \+/\- *lemma* preimage_eq_empty_iff

modified src/topology/tietze_extension.lean



## [2022-06-26 03:02:54](https://github.com/leanprover-community/mathlib/commit/72cff84)
feat(order/symm_diff): The symmetric difference is involutive ([#14959](https://github.com/leanprover-community/mathlib/pull/14959))
`a ∆ (a ∆ b) = b` and `b ∆ a ∆ a = b`.
#### Estimated changes
modified src/order/symm_diff.lean
- \+/\- *lemma* symm_diff_symm_diff_inf
- \+/\- *lemma* inf_symm_diff_symm_diff
- \+ *lemma* symm_diff_symm_diff_cancel_left
- \+ *lemma* symm_diff_symm_diff_cancel_right
- \+ *lemma* symm_diff_left_involutive
- \+ *lemma* symm_diff_right_involutive
- \+ *lemma* symm_diff_left_injective
- \+ *lemma* symm_diff_right_injective
- \+ *lemma* symm_diff_left_surjective
- \+ *lemma* symm_diff_right_surjective
- \+/\- *lemma* symm_diff_left_inj
- \+/\- *lemma* symm_diff_right_inj
- \- *lemma* symm_diff_symm_diff_self
- \+/\- *lemma* symm_diff_right_inj
- \+/\- *lemma* symm_diff_left_inj
- \+/\- *lemma* symm_diff_symm_diff_inf
- \+/\- *lemma* inf_symm_diff_symm_diff



## [2022-06-26 00:12:23](https://github.com/leanprover-community/mathlib/commit/b8c3e61)
refactor(*): Use `finset.Iix`/`finset.Ixi` ([#14448](https://github.com/leanprover-community/mathlib/pull/14448))
Now that `finset.Iix`/`finset.Ixi` work for empty types, there is no need for `univ.filter (λ j, j < i)` and similar.
#### Estimated changes
modified src/algebra/big_operators/fin.lean
- \+ *lemma* prod_Ioi_zero
- \+ *lemma* prod_Ioi_succ
- \- *lemma* prod_filter_zero_lt
- \- *lemma* prod_filter_succ_lt

modified src/data/fin/interval.lean
- \- *lemma* card_filter_lt
- \- *lemma* card_filter_le
- \- *lemma* card_filter_gt
- \- *lemma* card_filter_ge
- \- *lemma* card_filter_lt_lt
- \- *lemma* card_filter_lt_le
- \- *lemma* card_filter_le_lt
- \- *lemma* card_filter_le_le
- \- *lemma* prod_filter_lt_mul_neg_eq_prod_off_diag

modified src/data/finset/basic.lean
- \+/\- *lemma* disjoint_left
- \+/\- *lemma* disjoint_right
- \+/\- *lemma* disjoint_left
- \+/\- *lemma* disjoint_right

modified src/data/finset/card.lean

modified src/data/finset/locally_finite.lean
- \+ *lemma* disjoint_Ioi_Iio
- \+ *lemma* Ioi_disj_union_Iio
- \+ *lemma* prod_prod_Ioi_mul_eq_prod_prod_off_diag

modified src/data/fintype/fin.lean
- \+ *lemma* Ioi_zero_eq_map
- \+ *lemma* Ioi_succ
- \- *lemma* univ_filter_zero_lt
- \- *lemma* univ_filter_succ_lt

modified src/linear_algebra/vandermonde.lean

modified src/ring_theory/discriminant.lean

modified src/ring_theory/trace.lean



## [2022-06-25 21:12:47](https://github.com/leanprover-community/mathlib/commit/7ee73e4)
feat(data/fintype/basic): Constructing an equivalence from a left inverse ([#14816](https://github.com/leanprover-community/mathlib/pull/14816))
When `f : α → β`, `g : β → α` are inverses one way and `card α ≤ card β`, then they form an equivalence.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* _root_.function.left_inverse.right_inverse_of_card_le
- \+ *lemma* _root_.function.right_inverse.left_inverse_of_card_le
- \- *lemma* right_inverse_of_left_inverse_of_card_le
- \- *lemma* left_inverse_of_right_inverse_of_card_le
- \+ *def* of_left_inverse_of_card_le
- \+ *def* of_right_inverse_of_card_le

modified src/data/zmod/basic.lean

modified src/logic/function/basic.lean
- \+ *lemma* right_inverse.left_inverse_of_surjective
- \+ *lemma* right_inverse.left_inverse_of_injective



## [2022-06-25 21:12:46](https://github.com/leanprover-community/mathlib/commit/8812752)
feat(algebra/field/basic): Semifields ([#14683](https://github.com/leanprover-community/mathlib/pull/14683))
Define division semirings and semifields.
#### Estimated changes
modified src/algebra/field/basic.lean
- \+/\- *lemma* add_div
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* same_add_div
- \+/\- *lemma* div_add_same
- \+/\- *lemma* one_add_div
- \+/\- *lemma* div_add_one
- \+/\- *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* add_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* div_add_div
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* inv_add_inv
- \+ *lemma* semifield.to_is_field
- \+/\- *lemma* field.to_is_field
- \+/\- *lemma* is_field.nontrivial
- \+/\- *lemma* not_is_field_of_subsingleton
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div
- \+/\- *lemma* div_add_div_same
- \+/\- *lemma* same_add_div
- \+/\- *lemma* one_add_div
- \+/\- *lemma* div_add_same
- \+/\- *lemma* div_add_one
- \+/\- *lemma* add_div
- \+/\- *lemma* one_div_mul_add_mul_one_div_eq_one_div_add_one_div
- \+/\- *lemma* add_div_eq_mul_add_div
- \+/\- *lemma* div_add_div
- \+/\- *lemma* one_div_add_one_div
- \+/\- *lemma* inv_add_inv
- \+/\- *lemma* add_div'
- \+/\- *lemma* div_add'
- \+/\- *lemma* field.to_is_field
- \+/\- *lemma* is_field.nontrivial
- \+/\- *lemma* not_is_field_of_subsingleton
- \+/\- *lemma* map_units_inv
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_inv
- \+/\- *lemma* map_div

modified src/data/complex/basic.lean

modified src/data/real/nnreal.lean

modified src/number_theory/cyclotomic/basic.lean

modified src/ring_theory/ideal/quotient.lean
- \+/\- *theorem* maximal_ideal_iff_is_field_quotient
- \+/\- *theorem* maximal_ideal_iff_is_field_quotient

modified src/ring_theory/witt_vector/basic.lean



## [2022-06-25 20:02:11](https://github.com/leanprover-community/mathlib/commit/f9571f0)
feat(analysis/normed*): add instances about balls and spheres ([#14808](https://github.com/leanprover-community/mathlib/pull/14808))
Non-bc change: `has_inv.inv` on the unit circle is now defined using `has_inv.inv` instead of complex conjugation.
#### Estimated changes
modified src/analysis/complex/circle.lean
- \+/\- *lemma* coe_inv_circle
- \+/\- *lemma* coe_inv_circle_eq_conj
- \+/\- *lemma* coe_inv_circle_eq_conj
- \+/\- *lemma* coe_inv_circle
- \+/\- *def* circle
- \+/\- *def* circle.to_units
- \+ *def* circle.of_conj_div_self
- \+/\- *def* circle
- \+/\- *def* circle.to_units

created src/analysis/normed/field/unit_ball.lean
- \+ *def* subsemigroup.unit_ball
- \+ *def* subsemigroup.unit_closed_ball
- \+ *def* submonoid.unit_closed_ball
- \+ *def* submonoid.unit_sphere
- \+ *def* unit_sphere_to_units

created src/analysis/normed/group/ball_sphere.lean
- \+ *lemma* coe_neg_sphere
- \+ *lemma* coe_neg_ball
- \+ *lemma* coe_neg_closed_ball

modified src/analysis/normed/group/basic.lean
- \- *lemma* coe_neg_sphere

created src/analysis/normed_space/ball_action.lean
- \+ *lemma* ne_neg_of_mem_sphere
- \+ *lemma* ne_neg_of_mem_unit_sphere

modified src/analysis/normed_space/basic.lean
- \- *lemma* ne_neg_of_mem_sphere
- \- *lemma* ne_neg_of_mem_unit_sphere

modified src/geometry/manifold/instances/sphere.lean



## [2022-06-25 13:57:10](https://github.com/leanprover-community/mathlib/commit/6f923bd)
chore(*): golf ([#14939](https://github.com/leanprover-community/mathlib/pull/14939))
Some golfs I made while working on a large refactor.
#### Estimated changes
modified src/data/W/cardinal.lean

modified src/data/analysis/filter.lean

modified src/data/set/countable.lean

modified src/data/set/finite.lean

modified src/linear_algebra/dimension.lean

modified src/topology/constructions.lean



## [2022-06-25 07:57:38](https://github.com/leanprover-community/mathlib/commit/07c83c8)
feat(linear_algebra/clifford_algebra/of_alternating): extend alternating maps to the exterior algebra ([#14803](https://github.com/leanprover-community/mathlib/pull/14803))
#### Estimated changes
modified src/linear_algebra/exterior_algebra/basic.lean

created src/linear_algebra/exterior_algebra/of_alternating.lean
- \+ *lemma* lift_alternating_ι
- \+ *lemma* lift_alternating_ι_mul
- \+ *lemma* lift_alternating_one
- \+ *lemma* lift_alternating_algebra_map
- \+ *lemma* lift_alternating_apply_ι_multi
- \+ *lemma* lift_alternating_comp_ι_multi
- \+ *lemma* lift_alternating_comp
- \+ *lemma* lift_alternating_ι_multi
- \+ *lemma* lhom_ext
- \+ *def* lift_alternating
- \+ *def* lift_alternating_equiv



## [2022-06-24 21:45:08](https://github.com/leanprover-community/mathlib/commit/4fd263b)
feat(representation_theory/character): characters of representations ([#14453](https://github.com/leanprover-community/mathlib/pull/14453))
#### Estimated changes
modified src/algebra/category/FinVect.lean
- \+ *lemma* iso.conj_eq_conj
- \+ *def* iso_to_linear_equiv
- \+ *def* linear_equiv.to_FinVect_iso

modified src/representation_theory/basic.lean
- \+/\- *lemma* dual_apply
- \+ *lemma* dual_tensor_hom_comm
- \+/\- *lemma* dual_apply
- \- *theorem* char_mul_comm
- \- *theorem* char_conj
- \- *theorem* char_one

created src/representation_theory/character.lean
- \+ *lemma* char_mul_comm
- \+ *lemma* char_one
- \+ *lemma* char_tensor
- \+ *lemma* char_iso
- \+ *lemma* char_conj
- \+ *lemma* char_dual
- \+ *lemma* char_lin_hom
- \+ *def* character

modified src/representation_theory/fdRep.lean
- \+ *lemma* iso.conj_ρ
- \+ *lemma* dual_tensor_iso_lin_hom_hom_hom
- \+ *def* ρ
- \+ *def* iso_to_linear_equiv



## [2022-06-24 19:24:10](https://github.com/leanprover-community/mathlib/commit/8bf85d7)
feat(algebra/indicator_function): add an apply version of `mul_indicator_finset_bUnion` ([#14919](https://github.com/leanprover-community/mathlib/pull/14919))
#### Estimated changes
modified src/algebra/indicator_function.lean
- \+ *lemma* mul_indicator_finset_bUnion_apply



## [2022-06-24 19:24:09](https://github.com/leanprover-community/mathlib/commit/f94a64f)
feat(probability/martingale): add some lemmas for submartingales ([#14904](https://github.com/leanprover-community/mathlib/pull/14904))
#### Estimated changes
modified src/probability/martingale.lean
- \+ *lemma* submartingale_of_condexp_sub_nonneg
- \+ *lemma* submartingale.condexp_sub_nonneg
- \+ *lemma* submartingale_iff_condexp_sub_nonneg
- \+ *lemma* submartingale_of_set_integral_le_succ
- \+ *lemma* submartingale_nat
- \+ *lemma* submartingale_of_condexp_sub_nonneg_nat



## [2022-06-24 19:24:08](https://github.com/leanprover-community/mathlib/commit/40fa2d8)
feat(topology/metric_space): a countably generated uniformity is metrizable ([#14052](https://github.com/leanprover-community/mathlib/pull/14052))
#### Estimated changes
modified docs/references.bib

modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_iff'

modified src/data/nat/lattice.lean
- \+ *lemma* Sup_mem

created src/topology/metric_space/metrizable_uniformity.lean
- \+ *lemma* dist_of_prenndist
- \+ *lemma* dist_of_prenndist_le
- \+ *lemma* le_two_mul_dist_of_prenndist
- \+ *lemma* uniform_space.metrizable_space



## [2022-06-24 17:15:45](https://github.com/leanprover-community/mathlib/commit/fe322e1)
refactor(algebra/order/monoid): use typeclasses instead of lemmas ([#14848](https://github.com/leanprover-community/mathlib/pull/14848))
Use `covariant_class`/`contravariant_class` instead of type-specific `mul_le_mul_left` etc lemmas. Also, rewrite some proofs to use API about inequalities on `with_top`/`with_bot` instead of the exact form of the current definition.
#### Estimated changes
modified src/algebra/order/monoid.lean
- \+/\- *lemma* zero_le
- \+ *lemma* zero_eq_bot
- \+ *lemma* exists_one_lt_mul_of_lt
- \+/\- *lemma* zero_le
- \- *lemma* mul_le_mul_left
- \- *lemma* lt_of_mul_lt_mul_left
- \- *lemma* exists_pos_mul_of_lt



## [2022-06-24 15:26:20](https://github.com/leanprover-community/mathlib/commit/0e5f278)
feat(linear_algebra/{multilinear, alternating}): add `cod_restrict` and lemmas ([#14927](https://github.com/leanprover-community/mathlib/pull/14927))
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+ *lemma* subtype_comp_alternating_map_cod_restrict
- \+ *lemma* comp_alternating_map_cod_restrict
- \+ *def* cod_restrict

modified src/linear_algebra/multilinear/basic.lean
- \+ *lemma* subtype_comp_multilinear_map_cod_restrict
- \+ *lemma* comp_multilinear_map_cod_restrict
- \+ *def* cod_restrict



## [2022-06-24 15:26:19](https://github.com/leanprover-community/mathlib/commit/3e326fc)
feat(data/finite/basic): add missing instances ([#14913](https://github.com/leanprover-community/mathlib/pull/14913))
* Add `finite` instances for `prod`, `pprod`, `sigma`, and `psigma`.
* Don't depend on `classical.choice` in `finite_iff_nonempty_fintype`.
* Move `not_finite_iff_infinite` up, use it to golf some proofs.
#### Estimated changes
modified src/data/finite/basic.lean
- \+/\- *lemma* not_finite_iff_infinite
- \+/\- *lemma* not_finite_iff_infinite



## [2022-06-24 15:26:17](https://github.com/leanprover-community/mathlib/commit/363bbd2)
chore(topology/basic): golf a proof ([#14911](https://github.com/leanprover-community/mathlib/pull/14911))
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* mem_closure_of_frequently_of_tendsto



## [2022-06-24 15:26:16](https://github.com/leanprover-community/mathlib/commit/475cf37)
refactor(data/polynomial): extract/add lemmas and golf ([#14888](https://github.com/leanprover-community/mathlib/pull/14888))
+ Extract lemmas `roots_multiset_prod_X_sub_C`, `nat_degree_multiset_prod_X_sub_C_eq_card`, `monic_prod_multiset_X_sub_C` from the proof of `C_leading_coeff_mul_prod_multiset_X_sub_C` in *ring_division.lean*.
+ Add the lemma `exists_prod_multiset_X_sub_C_mul` in *ring_division.lean* and `roots_ne_zero_of_splits` in *splitting_field.lean* and use them to golf `nat_degree_eq_card_roots` The proof of the latter originally depends on `eq_prod_roots_of_splits`, but now the dependency reversed, with `nat_degree_eq_card_roots` now used to golf `eq_prod_roots_of_splits` (and `roots_map` as well).
+ Move `prod_multiset_root_eq_finset_root` and `prod_multiset_X_sub_C_dvd` from *field_division.lean* to *ring_division.lean* and golf the proof of the latter, generalizing `field` to `is_domain`.
+ Remove redundant imports and the lemma `exists_multiset_of_splits`, because it is just one direction of `splits_iff_exists_multiset`, and it follows trivially from `eq_prod_roots_of_splits`. It couldn't be removed before this PR because `roots_map` and `eq_prod_roots_of_splits` depended on it.
+ Golf `splits_of_exists_multiset` (independent of other changes).
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \- *lemma* prod_multiset_root_eq_finset_root
- \- *lemma* prod_multiset_X_sub_C_dvd

modified src/data/polynomial/ring_division.lean
- \+ *lemma* roots_multiset_prod_X_sub_C
- \+ *lemma* nat_degree_multiset_prod_X_sub_C_eq_card
- \+/\- *lemma* count_map_roots
- \+ *lemma* monic_prod_multiset_X_sub_C
- \+ *lemma* prod_multiset_root_eq_finset_root
- \+ *lemma* prod_multiset_X_sub_C_dvd
- \+ *lemma* exists_prod_multiset_X_sub_C_mul
- \+/\- *lemma* count_map_roots

modified src/field_theory/abel_ruffini.lean

modified src/field_theory/separable.lean

modified src/field_theory/splitting_field.lean
- \+ *lemma* roots_ne_zero_of_splits
- \+/\- *lemma* nat_degree_eq_card_roots
- \+/\- *lemma* degree_eq_card_roots
- \+/\- *lemma* eq_prod_roots_of_splits
- \- *lemma* exists_multiset_of_splits
- \+/\- *lemma* eq_prod_roots_of_splits
- \+/\- *lemma* nat_degree_eq_card_roots
- \+/\- *lemma* degree_eq_card_roots
- \+/\- *theorem* roots_map
- \+/\- *theorem* roots_map



## [2022-06-24 15:26:15](https://github.com/leanprover-community/mathlib/commit/dabb0c6)
feat(probability/independence): equivalent ways to check indep_fun ([#14814](https://github.com/leanprover-community/mathlib/pull/14814))
Prove:
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t)`,
- `indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → indep_set (f ⁻¹' s) (g ⁻¹' t) μ`.
#### Estimated changes
modified src/measure_theory/measurable_space.lean
- \+ *lemma* comap_eq_generate_from

modified src/probability/independence.lean
- \+ *lemma* indep_fun_iff_measure_inter_preimage_eq_mul
- \+ *lemma* indep_fun_iff_indep_set_preimage



## [2022-06-24 15:26:14](https://github.com/leanprover-community/mathlib/commit/7c2ad75)
feat(field_theory.intermediate_field):  intermediate_field.inclusion ([#12596](https://github.com/leanprover-community/mathlib/pull/12596))
#### Estimated changes
modified src/field_theory/intermediate_field.lean
- \+ *lemma* inclusion_injective
- \+ *lemma* inclusion_self
- \+ *lemma* inclusion_inclusion
- \+ *lemma* coe_inclusion
- \+ *def* inclusion



## [2022-06-24 13:23:16](https://github.com/leanprover-community/mathlib/commit/e420232)
feat(data/int/basic): add a better `has_reflect int` instance ([#14906](https://github.com/leanprover-community/mathlib/pull/14906))
This closes a todo comment in `number_theory.lucas_lehmer`.
This also merges `rat.has_reflect` with `rat.reflect` to match `nat.reflect`.
#### Estimated changes
modified src/data/int/basic.lean

modified src/data/rat/meta_defs.lean

modified src/number_theory/lucas_lehmer.lean

modified test/rat.lean



## [2022-06-24 13:23:15](https://github.com/leanprover-community/mathlib/commit/f05c49f)
feat(meta/univs): Add a reflect_name tactic, make reflected instances universe polymorphic ([#14766](https://github.com/leanprover-community/mathlib/pull/14766))
The existing `list.reflect` instance only works for `Type 0`, this version works for `Type u` providing `u` is known.
#### Estimated changes
modified src/data/fin/vec_notation.lean

modified src/data/vector/basic.lean

created src/meta/univs.lean

modified test/vec_notation.lean



## [2022-06-24 11:15:40](https://github.com/leanprover-community/mathlib/commit/8187142)
feat(data/finset/pointwise): `s • t` is the union of the `a • t` ([#14696](https://github.com/leanprover-community/mathlib/pull/14696))
and a few other results leading to it. Also tag `set.coe_bUnion` with `norm_cast` and rename `finset.image_mul_prod`/`finset.add_image_prod` to `finset.image_mul_product`/`finset.image_add_product`
#### Estimated changes
modified src/data/finset/basic.lean
- \+/\- *lemma* coe_bUnion
- \+/\- *lemma* coe_bUnion

modified src/data/finset/n_ary.lean
- \+ *lemma* bUnion_image_left
- \+ *lemma* bUnion_image_right

modified src/data/finset/pointwise.lean
- \+ *lemma* image_mul_product
- \+ *lemma* bUnion_smul_finset
- \+ *lemma* pairwise_disjoint_smul_iff
- \- *lemma* image_mul_prod

modified src/data/set/lattice.lean
- \+ *lemma* prod_eq_bUnion_left
- \+ *lemma* prod_eq_bUnion_right

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint_image_right_iff
- \+ *lemma* pairwise_disjoint_image_left_iff

modified src/data/set/pointwise.lean
- \+ *lemma* bUnion_smul_set
- \+ *lemma* pairwise_disjoint_smul_iff

modified src/data/set/prod.lean
- \+ *lemma* image2_mk_eq_prod



## [2022-06-24 11:15:39](https://github.com/leanprover-community/mathlib/commit/6d00cc2)
feat(ring_theory/trace): Add `trace_eq_sum_automorphisms`, `norm_eq_prod_automorphisms`, `normal.alg_hom_equiv_aut` ([#14523](https://github.com/leanprover-community/mathlib/pull/14523))
#### Estimated changes
modified src/field_theory/normal.lean
- \+ *def* normal.alg_hom_equiv_aut

modified src/ring_theory/norm.lean
- \+ *lemma* norm_eq_prod_automorphisms

modified src/ring_theory/trace.lean
- \+ *lemma* trace_eq_sum_automorphisms



## [2022-06-24 09:56:29](https://github.com/leanprover-community/mathlib/commit/efe794c)
chore(order/filter): turn `tendsto_id'` into an `iff` lemma ([#14791](https://github.com/leanprover-community/mathlib/pull/14791))
#### Estimated changes
modified src/dynamics/omega_limit.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* tendsto_id'
- \+/\- *lemma* tendsto_id
- \+/\- *lemma* tendsto_id'
- \+/\- *lemma* tendsto_id

modified src/topology/instances/ennreal.lean

modified src/topology/order.lean
- \+ *lemma* continuous_id_iff_le

modified src/topology/separation.lean



## [2022-06-24 09:16:09](https://github.com/leanprover-community/mathlib/commit/6cefaf4)
feat(measure_theory/function/conditional_expectation): conditional expectation w.r.t. the restriction of a measure to a set ([#14751](https://github.com/leanprover-community/mathlib/pull/14751))
We prove `(μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m]`.
#### Estimated changes
modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* condexp_of_ae_strongly_measurable'
- \+/\- *lemma* condexp_indicator_aux
- \+ *lemma* condexp_restrict_ae_eq_restrict
- \+/\- *lemma* condexp_indicator_aux



## [2022-06-24 01:29:11](https://github.com/leanprover-community/mathlib/commit/ac2e9db)
feat(data/real/{e,}nnreal): add some order isomorphisms ([#14900](https://github.com/leanprover-community/mathlib/pull/14900))
* If `a` is a nonnegative real number, then
  -  `set.Icc (0 : ℝ) (a : ℝ)` is order isomorphic to `set.Iic a`;
  - `set.Iic (a : ℝ≥0∞)` is order isomorphic to `set.Iic a`;
* Also, `ℝ≥0∞` is order isomorphic both to `Iic (1 : ℝ≥0∞)` and to the unit interval in `ℝ`.
* Use the latter fact to golf `ennreal.second_countable_topology`.
* Golf `ennreal.has_continuous_inv` using `order_iso.continuous`.
* Improve definitional equalities for `equiv.subtype_subtype_equiv_subtype_exists`, `equiv.subtype_subtype_equiv_subtype_inter`, `equiv.subtype_subtype_equiv_subtype`, `equiv.set.sep`, use `simps`.
#### Estimated changes
modified src/data/real/ennreal.lean
- \+/\- *lemma* inv_three_add_inv_three
- \+ *lemma* order_iso_Iic_one_birational_symm_apply
- \+ *lemma* order_iso_Iic_coe_symm_apply_coe
- \+ *lemma* order_iso_unit_interval_birational_apply_coe
- \+/\- *lemma* inv_three_add_inv_three
- \+ *def* order_iso_Iic_one_birational
- \+ *def* order_iso_Iic_coe
- \+ *def* order_iso_unit_interval_birational

modified src/data/real/nnreal.lean
- \+ *lemma* order_iso_Icc_zero_coe_symm_apply_coe
- \+ *def* order_iso_Icc_zero_coe

modified src/logic/equiv/basic.lean
- \- *lemma* subtype_subtype_equiv_subtype_exists_apply
- \- *lemma* subtype_subtype_equiv_subtype_inter_apply
- \- *lemma* subtype_subtype_equiv_subtype_apply
- \+/\- *def* subtype_subtype_equiv_subtype_inter
- \+/\- *def* subtype_subtype_equiv_subtype
- \+/\- *def* subtype_subtype_equiv_subtype_inter
- \+/\- *def* subtype_subtype_equiv_subtype

modified src/topology/instances/ennreal.lean



## [2022-06-24 01:29:10](https://github.com/leanprover-community/mathlib/commit/cb94893)
refactor(order/complete_lattice): `Sup` lemmas before `Inf` lemmas ([#14868](https://github.com/leanprover-community/mathlib/pull/14868))
Throughout the file, we make sure that `Sup` theorems always appear immediately before their `Inf` counterparts. This ensures consistency, and makes it much easier to golf theorems or detect missing API.
We choose to put `Sup` before `Inf` rather than the other way around, since this seems to minimize the amount of things that need to be moved around, and it matches the order that we define the two operations.
We also golf a few proofs throughout, and add some missing corresponding theorems, namely:
- `infi_extend_top`
- `infi_supr_ge_nat_add`
- `unary_relation_Inf_iff`
- `binary_relation_Inf_iff`
#### Estimated changes
modified src/order/complete_lattice.lean
- \+/\- *lemma* Sup_eq_bot
- \+ *lemma* Inf_eq_top
- \+/\- *lemma* eq_singleton_top_of_Inf_eq_top_of_nonempty
- \+/\- *lemma* Inf_lt_iff
- \+/\- *lemma* Sup_eq_top
- \+/\- *lemma* monotone.le_map_supr₂
- \+/\- *lemma* monotone.le_map_Sup
- \+/\- *lemma* order_iso.map_infi
- \+/\- *lemma* order_iso.map_Inf
- \+/\- *lemma* le_infi_comp
- \+/\- *lemma* monotone.infi_comp_eq
- \+/\- *lemma* monotone.map_infi_le
- \+/\- *lemma* monotone.map_infi₂_le
- \+/\- *lemma* monotone.map_Inf_le
- \+/\- *lemma* supr_const_le
- \+/\- *lemma* le_infi_const
- \+/\- *lemma* supr_bot
- \+/\- *lemma* infi_top
- \+/\- *lemma* supr_subtype'
- \+/\- *lemma* supr_subtype''
- \+/\- *lemma* infi_subtype''
- \+/\- *lemma* supr_sup
- \+/\- *lemma* infi_inf
- \+/\- *lemma* sup_supr
- \+/\- *lemma* inf_infi
- \+/\- *lemma* supr_exists
- \+/\- *lemma* infi_exists
- \+/\- *lemma* supr_and
- \+/\- *lemma* infi_and
- \+/\- *lemma* infi_and'
- \+/\- *lemma* supr_ite
- \+/\- *lemma* infi_range
- \+/\- *lemma* supr_split
- \+/\- *lemma* infi_split
- \+/\- *lemma* supr_split_single
- \+/\- *lemma* infi_split_single
- \+ *lemma* supr_le_supr_of_subset
- \+ *lemma* infi_le_infi_of_subset
- \+/\- *lemma* infi_image
- \+ *lemma* infi_extend_top
- \+ *lemma* infi_supr_ge_nat_add
- \+/\- *lemma* supr_eq_top
- \+/\- *lemma* infi_eq_bot
- \+/\- *lemma* infi_Prop_eq
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* supr_apply
- \+ *lemma* unary_relation_Inf_iff
- \+ *lemma* binary_relation_Inf_iff
- \+/\- *lemma* supr_inf_le_inf_Sup
- \+/\- *lemma* eq_singleton_top_of_Inf_eq_top_of_nonempty
- \+/\- *lemma* Sup_eq_bot
- \+/\- *lemma* Inf_lt_iff
- \+/\- *lemma* Sup_eq_top
- \+/\- *lemma* monotone.le_map_supr₂
- \+/\- *lemma* monotone.le_map_Sup
- \+/\- *lemma* monotone.map_infi_le
- \+/\- *lemma* monotone.map_infi₂_le
- \+/\- *lemma* monotone.map_Inf_le
- \+/\- *lemma* order_iso.map_infi
- \+/\- *lemma* order_iso.map_Inf
- \+/\- *lemma* le_infi_comp
- \+/\- *lemma* monotone.infi_comp_eq
- \+/\- *lemma* supr_const_le
- \+/\- *lemma* le_infi_const
- \+/\- *lemma* infi_top
- \+/\- *lemma* supr_bot
- \+/\- *lemma* infi_subtype''
- \+/\- *lemma* infi_inf
- \+/\- *lemma* inf_infi
- \+/\- *lemma* supr_sup
- \+/\- *lemma* sup_supr
- \+/\- *lemma* infi_exists
- \+/\- *lemma* supr_exists
- \+/\- *lemma* infi_and
- \+/\- *lemma* infi_and'
- \+/\- *lemma* supr_and
- \+/\- *lemma* supr_ite
- \+/\- *lemma* infi_range
- \+/\- *lemma* infi_split
- \+/\- *lemma* infi_split_single
- \+/\- *lemma* supr_split
- \+/\- *lemma* supr_split_single
- \+/\- *lemma* infi_image
- \+/\- *lemma* supr_subtype'
- \+/\- *lemma* supr_subtype''
- \+/\- *lemma* supr_eq_top
- \+/\- *lemma* infi_eq_bot
- \+/\- *lemma* infi_Prop_eq
- \+/\- *lemma* Sup_apply
- \+/\- *lemma* supr_apply
- \+/\- *lemma* supr_inf_le_inf_Sup
- \+/\- *theorem* Sup_inter_le
- \+/\- *theorem* Sup_eq_of_forall_le_of_forall_lt_exists_gt
- \+/\- *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* supr_const
- \+/\- *theorem* infi_const
- \+/\- *theorem* infi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right
- \+/\- *theorem* supr_subtype
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* supr_sup_eq
- \+/\- *theorem* infi_inf_eq
- \+/\- *theorem* infi_false
- \+/\- *theorem* infi_or
- \+/\- *theorem* Sup_image
- \+/\- *theorem* Inf_image
- \+/\- *theorem* supr_emptyset
- \+/\- *theorem* infi_emptyset
- \+/\- *theorem* supr_univ
- \+/\- *theorem* infi_univ
- \+/\- *theorem* supr_union
- \+/\- *theorem* infi_union
- \+/\- *theorem* supr_insert
- \+/\- *theorem* supr_singleton
- \+/\- *theorem* infi_pair
- \+/\- *theorem* supr_of_empty
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* supr_prod
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_sum
- \+/\- *theorem* infi_sum
- \+/\- *theorem* supr_option
- \+/\- *theorem* infi_option
- \+/\- *theorem* Sup_inter_le
- \- *theorem* Inf_eq_top
- \+/\- *theorem* Sup_eq_of_forall_le_of_forall_lt_exists_gt
- \+/\- *theorem* Inf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* infi_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* supr_supr_eq_left
- \+/\- *theorem* supr_supr_eq_right
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* infi_inf_eq
- \+/\- *theorem* supr_sup_eq
- \+/\- *theorem* infi_false
- \+/\- *theorem* infi_or
- \+/\- *theorem* Inf_image
- \+/\- *theorem* Sup_image
- \+/\- *theorem* infi_emptyset
- \+/\- *theorem* supr_emptyset
- \+/\- *theorem* infi_univ
- \+/\- *theorem* supr_univ
- \+/\- *theorem* infi_union
- \- *theorem* infi_le_infi_of_subset
- \+/\- *theorem* supr_union
- \- *theorem* supr_le_supr_of_subset
- \+/\- *theorem* supr_insert
- \+/\- *theorem* infi_pair
- \+/\- *theorem* supr_singleton
- \+/\- *theorem* supr_of_empty
- \+/\- *theorem* supr_subtype
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod
- \+/\- *theorem* infi_sum
- \+/\- *theorem* supr_sum
- \+/\- *theorem* supr_option
- \+/\- *theorem* infi_option



## [2022-06-24 01:29:09](https://github.com/leanprover-community/mathlib/commit/649ca66)
chore(*): Disparate generalizations to division monoids ([#14686](https://github.com/leanprover-community/mathlib/pull/14686))
The leftover changes from the introduction of `division_monoid`.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean

modified src/algebra/group/commute.lean
- \+ *lemma* inv_inv
- \+ *lemma* inv_inv_iff
- \- *theorem* inv_inv
- \- *theorem* inv_inv_iff

modified src/algebra/group/conj.lean

modified src/algebra/group/prod.lean
- \+/\- *def* div_monoid_hom
- \+/\- *def* div_monoid_hom

modified src/algebra/group/semiconj.lean
- \+/\- *lemma* inv_inv_symm_iff
- \+/\- *lemma* inv_inv_symm
- \+/\- *lemma* inv_inv_symm
- \+/\- *lemma* inv_inv_symm_iff

modified src/algebra/group_with_zero/basic.lean
- \- *lemma* coe_inv'
- \- *theorem* inv_inv₀

modified src/algebra/group_with_zero/power.lean
- \- *lemma* units.coe_zpow₀

modified src/algebra/order/group.lean

modified src/analysis/normed_space/spectrum.lean

modified src/data/real/ennreal.lean

modified src/data/real/nnreal.lean

modified src/group_theory/group_action/group.lean
- \+/\- *def* arrow_action
- \+/\- *def* arrow_action

modified src/group_theory/submonoid/pointwise.lean

modified src/group_theory/subsemigroup/center.lean

modified src/number_theory/arithmetic_function.lean

modified src/ring_theory/dedekind_domain/adic_valuation.lean

modified src/ring_theory/localization/as_subring.lean

modified src/topology/algebra/field.lean



## [2022-06-23 23:27:42](https://github.com/leanprover-community/mathlib/commit/56185bd)
feat(data/finset): add some lemmas about `finset.disj_union` ([#14910](https://github.com/leanprover-community/mathlib/pull/14910))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_disj_union

modified src/data/finset/basic.lean
- \+ *lemma* forall_mem_map
- \+ *theorem* map_disj_union_aux
- \+ *theorem* map_disj_union
- \+ *theorem* map_disj_union'

modified src/data/finset/fold.lean
- \+ *theorem* fold_disj_union



## [2022-06-23 20:16:37](https://github.com/leanprover-community/mathlib/commit/198cb64)
refactor(ring_theory): generalize basic API of `ring_hom` to `ring_hom_class` ([#14756](https://github.com/leanprover-community/mathlib/pull/14756))
This PR generalizes part of the basic API of ring homs to `ring_hom_class`. This notably includes things like `ring_hom.ker`, `ideal.map` and `ideal.comap`. I left the namespaces unchanged, for example `ring_hom.ker` remains the same even though it is now defined for any `ring_hom_class` morphism; this way dot notation still (mostly) works for actual ring homs.
#### Estimated changes
modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/ideal/local_ring.lean

modified src/ring_theory/ideal/operations.lean
- \+/\- *lemma* apply_coe_mem_map
- \+/\- *lemma* map_le_comap_of_inv_on
- \+/\- *lemma* comap_le_map_of_inv_on
- \+/\- *lemma* map_le_comap_of_inverse
- \+/\- *lemma* comap_le_map_of_inverse
- \+/\- *lemma* map_span
- \+/\- *lemma* ker_eq_comap_bot
- \+/\- *lemma* comap_ker
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* ker_ne_top
- \+/\- *lemma* ker_coe_equiv
- \+ *lemma* ker_equiv
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* ker_is_maximal_of_surjective
- \+/\- *lemma* map_eq_bot_iff_le_ker
- \+/\- *lemma* ker_le_comap
- \+/\- *lemma* map_Inf
- \+/\- *lemma* apply_coe_mem_map
- \+/\- *lemma* map_le_comap_of_inv_on
- \+/\- *lemma* comap_le_map_of_inv_on
- \+/\- *lemma* map_le_comap_of_inverse
- \+/\- *lemma* comap_le_map_of_inverse
- \+/\- *lemma* map_span
- \+/\- *lemma* ker_eq_comap_bot
- \+/\- *lemma* comap_ker
- \+/\- *lemma* not_one_mem_ker
- \+/\- *lemma* ker_ne_top
- \+/\- *lemma* ker_coe_equiv
- \+/\- *lemma* ker_is_prime
- \+/\- *lemma* ker_is_maximal_of_surjective
- \+/\- *lemma* map_eq_bot_iff_le_ker
- \+/\- *lemma* ker_le_comap
- \+/\- *lemma* map_Inf
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* map_is_prime_of_surjective
- \+/\- *theorem* map_is_prime_of_equiv
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* map_is_prime_of_surjective
- \+/\- *theorem* map_is_prime_of_equiv

modified src/ring_theory/ideal/over.lean

modified src/ring_theory/ideal/prod.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/jacobson_ideal.lean

modified src/ring_theory/localization/localization_localization.lean

modified src/ring_theory/polynomial/basic.lean
- \+/\- *lemma* ker_map
- \+/\- *lemma* ker_map



## [2022-06-23 16:23:10](https://github.com/leanprover-community/mathlib/commit/44d3fc0)
chore(data/nat,int): move field-specific lemmas about cast ([#14890](https://github.com/leanprover-community/mathlib/pull/14890))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is a step in rearranging those imports: remove the definition of a field from the dependencies of the casts `ℕ → α` and `ℤ → α`, where `α` is a (semi)ring.
#### Estimated changes
modified src/algebra/big_operators/ring.lean

modified src/algebra/char_zero.lean

modified src/algebra/order/field.lean
- \+ *lemma* pow_minus_two_nonneg
- \+ *theorem* nat.cast_le_pow_sub_div_sub
- \+ *theorem* nat.cast_le_pow_div_sub

deleted src/algebra/order/field_pow.lean
- \- *lemma* pow_minus_two_nonneg
- \- *theorem* nat.cast_le_pow_sub_div_sub
- \- *theorem* nat.cast_le_pow_div_sub

modified src/algebra/order/smul.lean

modified src/analysis/special_functions/bernstein.lean

modified src/analysis/specific_limits/normed.lean

modified src/data/int/cast.lean
- \- *theorem* cast_div

created src/data/int/cast_field.lean
- \+ *theorem* cast_div

modified src/data/int/char_zero.lean

modified src/data/nat/cast.lean
- \- *lemma* cast_div_le
- \- *lemma* inv_pos_of_nat
- \- *lemma* one_div_pos_of_nat
- \- *lemma* one_div_le_one_div
- \- *lemma* one_div_lt_one_div
- \- *theorem* cast_div

created src/data/nat/cast_field.lean
- \+ *lemma* cast_div_le
- \+ *lemma* inv_pos_of_nat
- \+ *lemma* one_div_pos_of_nat
- \+ *lemma* one_div_le_one_div
- \+ *lemma* one_div_lt_one_div
- \+ *theorem* cast_div

modified src/data/nat/choose/bounds.lean

modified src/data/rat/order.lean

modified src/order/filter/at_top_bot.lean



## [2022-06-23 16:23:08](https://github.com/leanprover-community/mathlib/commit/c3e3d1a)
feat(data/set): replace `set_coe.can_lift` by `subtype.can_lift` ([#14792](https://github.com/leanprover-community/mathlib/pull/14792))
#### Estimated changes
modified src/data/set/basic.lean

modified src/tactic/lift.lean



## [2022-06-23 16:23:07](https://github.com/leanprover-community/mathlib/commit/4de20c5)
feat(analysis/../log): log_nat_eq_sum_factorization ([#14782](https://github.com/leanprover-community/mathlib/pull/14782))
#### Estimated changes
modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* log_nat_eq_sum_factorization



## [2022-06-23 16:23:06](https://github.com/leanprover-community/mathlib/commit/c2fcf9f)
feat(data/polynomial/erase_lead): Characterizations of polynomials of small support ([#14500](https://github.com/leanprover-community/mathlib/pull/14500))
This PR adds iff-lemmas `card_support_eq_one`, `card_support_eq_two`, and `card_support_eq_three`. These will be useful for irreducibility of x^n-x-1.
#### Estimated changes
modified src/data/polynomial/erase_lead.lean
- \+ *lemma* card_support_eq_one
- \+ *lemma* card_support_eq_two
- \+ *lemma* card_support_eq_three



## [2022-06-23 14:10:06](https://github.com/leanprover-community/mathlib/commit/ef24ace)
feat(order/hom/basic): some lemmas about order homs and equivs  ([#14872](https://github.com/leanprover-community/mathlib/pull/14872))
A few lemmas from [#11053](https://github.com/leanprover-community/mathlib/pull/11053), which I have seperated from the original PR following @riccardobrasca's suggestion.
#### Estimated changes
modified src/order/hom/basic.lean
- \+ *lemma* coe_eq
- \+ *def* of_hom_inv



## [2022-06-23 14:10:05](https://github.com/leanprover-community/mathlib/commit/dd2e7ad)
feat(analysis/convex/strict_convex_space): isometries of strictly convex spaces are affine ([#14837](https://github.com/leanprover-community/mathlib/pull/14837))
Add the result that isometries of (affine spaces for) real normed
spaces with strictly convex codomain are affine isometries.  In
particular, this applies to isometries of Euclidean spaces (we already
have the instance that real inner product spaces are uniformly convex
and thus strictly convex).  Strict convexity means the surjectivity
requirement of Mazur-Ulam can be avoided.
#### Estimated changes
modified src/analysis/convex/strict_convex_space.lean
- \+ *lemma* eq_line_map_of_dist_eq_mul_of_dist_eq_mul
- \+ *lemma* eq_midpoint_of_dist_eq_half
- \+ *lemma* coe_affine_isometry_of_strict_convex_space
- \+ *lemma* affine_isometry_of_strict_convex_space_apply

modified src/analysis/normed/group/add_torsor.lean
- \+ *lemma* dist_eq_norm_vsub'



## [2022-06-23 14:10:04](https://github.com/leanprover-community/mathlib/commit/966bb24)
feat(group_theory/finite_abelian): Structure of finite abelian groups ([#14736](https://github.com/leanprover-community/mathlib/pull/14736))
Any finitely generated abelian group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
Any finite abelian group is a direct sum of some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.
(TODO : prove uniqueness of this decomposition)
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/algebra/group/prod.lean
- \+ *def* prod_congr
- \+ *def* unique_prod
- \+ *def* prod_unique

modified src/data/zmod/basic.lean
- \+ *def* ring_equiv_congr

created src/group_theory/finite_abelian.lean
- \+ *theorem* equiv_free_prod_direct_sum_zmod
- \+ *theorem* equiv_direct_sum_zmod_of_fintype

modified src/group_theory/finiteness.lean

modified src/linear_algebra/prod.lean

modified src/logic/equiv/basic.lean
- \+ *def* prod_unique
- \+ *def* unique_prod



## [2022-06-23 14:10:03](https://github.com/leanprover-community/mathlib/commit/cff439d)
feat(analysis/seminorm): add add_group_seminorm ([#14336](https://github.com/leanprover-community/mathlib/pull/14336))
We introduce `add_group_seminorm` and refactor `seminorm` to extend this new definition. This new `add_group_seminorm` structure will also be used in [#14115](https://github.com/leanprover-community/mathlib/pull/14115) to define `ring_seminorm`.
#### Estimated changes
modified counterexamples/seminorm_lattice_not_distrib.lean

modified src/analysis/convex/gauge.lean

modified src/analysis/seminorm.lean
- \+ *lemma* ext
- \+ *lemma* coe_zero
- \+ *lemma* zero_apply
- \+ *lemma* coe_smul
- \+ *lemma* smul_apply
- \+ *lemma* coe_add
- \+ *lemma* add_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* smul_sup
- \+ *lemma* le_def
- \+ *lemma* lt_def
- \+ *lemma* sub_rev
- \+ *lemma* le_insert
- \+ *lemma* le_insert'
- \+ *lemma* inf_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_id
- \+ *lemma* comp_zero
- \+ *lemma* zero_comp
- \+ *lemma* comp_comp
- \+ *lemma* add_comp
- \+ *lemma* comp_add_le
- \+ *lemma* comp_mono
- \+ *lemma* comp_add_le
- \+/\- *lemma* ball_bot
- \+/\- *lemma* ball_finset_sup
- \+ *lemma* coe_norm_add_group_seminorm
- \- *lemma* comp_triangle
- \- *lemma* nonneg
- \+/\- *lemma* ball_bot
- \+/\- *lemma* ball_finset_sup
- \+ *def* comp
- \+ *def* seminorm.of
- \+ *def* norm_add_group_seminorm
- \+/\- *def* norm_seminorm
- \+/\- *def* norm_seminorm



## [2022-06-23 14:10:01](https://github.com/leanprover-community/mathlib/commit/585a1bf)
feat(number_theory): define ramification index and inertia degree ([#14332](https://github.com/leanprover-community/mathlib/pull/14332))
We define ramification index `ramification_idx` and inertia degree `inertia_deg` for `P : ideal S` over `p : ideal R` given a ring extension `f : R →+* S`. The literature generally assumes `p` is included in `P`, both are maximal, `R` is the ring of integers of a number field `K` and `S` is the integral closure of `R` in `L`, a finite separable extension of `K`; we relax these assumptions as much as is practical.
#### Estimated changes
created src/number_theory/ramification_inertia.lean
- \+ *lemma* ramification_idx_eq_find
- \+ *lemma* ramification_idx_eq_zero
- \+ *lemma* ramification_idx_spec
- \+ *lemma* ramification_idx_lt
- \+ *lemma* ramification_idx_bot
- \+ *lemma* ramification_idx_of_not_le
- \+ *lemma* ramification_idx_ne_zero
- \+ *lemma* le_pow_of_le_ramification_idx
- \+ *lemma* le_pow_ramification_idx
- \+ *lemma* ramification_idx_eq_normalized_factors_count
- \+ *lemma* ramification_idx_eq_factors_count
- \+ *lemma* ramification_idx_ne_zero
- \+ *lemma* inertia_deg_of_subsingleton
- \+ *lemma* inertia_deg_algebra_map



## [2022-06-23 11:58:10](https://github.com/leanprover-community/mathlib/commit/cc4b8e5)
feat(data/sigma,data/ulift,logic/equiv): add missing lemmas ([#14903](https://github.com/leanprover-community/mathlib/pull/14903))
Add lemmas and `equiv`s about `plift`, `psigma`, and `pprod`.
#### Estimated changes
modified src/data/sigma/basic.lean
- \+ *theorem* «forall»
- \+ *theorem* «exists»

modified src/data/ulift.lean
- \+ *lemma* up_injective
- \+ *lemma* up_surjective
- \+ *lemma* up_bijective
- \+ *lemma* up_inj
- \+ *lemma* down_surjective
- \+ *lemma* down_bijective
- \+ *lemma* up_injective
- \+ *lemma* up_surjective
- \+ *lemma* up_bijective
- \+ *lemma* up_inj
- \+ *lemma* down_surjective
- \+ *lemma* down_bijective

modified src/logic/equiv/basic.lean
- \+ *def* pprod_equiv_prod_plift
- \+ *def* psigma_equiv_sigma_plift

modified src/set_theory/cardinal/cofinality.lean



## [2022-06-23 10:25:45](https://github.com/leanprover-community/mathlib/commit/cf23199)
chore(number_theory/lucas_lehmer): remove `has_to_pexpr` instances ([#14905](https://github.com/leanprover-community/mathlib/pull/14905))
These instances are sort of out-of-place, and aren't really needed anyway.
We already use the more verbose ``%%`(n)`` notation elsewhere in mathlib, which as an operation makes more conceptual sense.
Until [#14901](https://github.com/leanprover-community/mathlib/pull/14901) these two instances were just special cases of `has_reflect.has_to_pexpr`. While unlike that instance these two instances are not diamond-forming, they're unecessary special cases that make antiquoting harder to understand.
#### Estimated changes
modified src/number_theory/lucas_lehmer.lean



## [2022-06-22 23:55:53](https://github.com/leanprover-community/mathlib/commit/416edbd)
chore(ring_theory/polynomial/symmetric): golf proofs ([#14866](https://github.com/leanprover-community/mathlib/pull/14866))
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* finset_congr_to_embedding

modified src/data/finset/powerset.lean
- \+ *theorem* powerset_len_map

modified src/data/fintype/basic.lean
- \+ *lemma* map_univ_of_surjective
- \+ *lemma* map_univ_equiv

modified src/ring_theory/polynomial/symmetric.lean



## [2022-06-22 21:42:36](https://github.com/leanprover-community/mathlib/commit/c45e5d5)
fix(meta/expr): remove `has_reflect.has_to_pexpr` ([#14901](https://github.com/leanprover-community/mathlib/pull/14901))
This instance (introduced in [#3477](https://github.com/leanprover-community/mathlib/pull/3477)) forms a diamond with the builtin `pexpr.has_to_pexpr`:
```lean
import meta.expr
#eval show tactic unit, from do
  let i1 : has_to_pexpr pexpr := pexpr.has_to_pexpr,
  let i2 : has_to_pexpr pexpr := has_reflect.has_to_pexpr,
  let e := ``(1),
  let p1 := @to_pexpr _ i1 e,
  let p2 := @to_pexpr _ i2 e,
  guard (p1 = p2) -- fails
```
The consequence is that in cases where `bar` is not a `pexpr` or `expr` but a value to be reflected, ``` ``(foo %%bar) ``` now has to be written ``` ``(foo %%`(bar)) ```; a spelling already used in various existing files.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/Instance.20diamonds.20in.20has_to_pexpr/near/287083928)
#### Estimated changes
modified src/meta/expr.lean

modified src/tactic/core.lean

modified src/tactic/transform_decl.lean

modified test/norm_swap.lean



## [2022-06-22 18:31:24](https://github.com/leanprover-community/mathlib/commit/2a732ed)
chore(analysis/special_functions/log/basic): golf a proof ([#14898](https://github.com/leanprover-community/mathlib/pull/14898))
#### Estimated changes
modified src/analysis/special_functions/log/basic.lean



## [2022-06-22 18:31:23](https://github.com/leanprover-community/mathlib/commit/23918a5)
feat(order/filter/basic): add some lemmas about `eventually_le` ([#14891](https://github.com/leanprover-community/mathlib/pull/14891))
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eventually_le.mul_le_mul
- \+ *lemma* eventually_le.mul_nonneg
- \+ *lemma* eventually_sub_nonneg



## [2022-06-22 18:31:21](https://github.com/leanprover-community/mathlib/commit/12e5f2e)
refactor(data/set/countable): make `set.countable` protected ([#14886](https://github.com/leanprover-community/mathlib/pull/14886))
I'm going to add `_root_.countable` typeclass, a data-free version of `encodable`.
#### Estimated changes
modified counterexamples/phillips.lean
- \+/\- *lemma* apply_countable
- \+/\- *lemma* countable_compl_spf
- \+/\- *lemma* countable_spf_mem
- \+/\- *lemma* apply_countable
- \+/\- *lemma* countable_compl_spf
- \+/\- *lemma* countable_spf_mem

modified src/analysis/box_integral/divergence_theorem.lean

modified src/analysis/complex/cauchy_integral.lean

modified src/analysis/special_functions/complex/log.lean
- \+/\- *lemma* countable_preimage_exp
- \+/\- *lemma* countable_preimage_exp

modified src/data/complex/cardinality.lean
- \+/\- *lemma* not_countable_complex
- \+/\- *lemma* not_countable_complex

modified src/data/real/cardinality.lean
- \+/\- *lemma* not_countable_real
- \+/\- *lemma* not_countable_real

modified src/data/set/countable.lean
- \+/\- *lemma* countable_encodable'
- \+/\- *lemma* countable_encodable
- \+/\- *lemma* countable.exists_surjective
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \+/\- *lemma* countable.mono
- \+/\- *lemma* countable.image
- \+/\- *lemma* countable_range
- \+/\- *lemma* countable.preimage_of_inj_on
- \+/\- *lemma* countable_Union
- \+/\- *lemma* countable.sUnion
- \+/\- *lemma* countable_Union_Prop
- \+/\- *lemma* countable_union
- \+/\- *lemma* countable_insert
- \+/\- *lemma* countable.insert
- \+/\- *lemma* finite.countable
- \+/\- *lemma* subsingleton.countable
- \+/\- *lemma* countable_is_top
- \+/\- *lemma* countable_is_bot
- \+/\- *lemma* countable_set_of_finite_subset
- \+/\- *lemma* countable_pi
- \+/\- *lemma* countable.image2
- \+/\- *lemma* subset_range_enumerate
- \+/\- *lemma* countable_encodable'
- \+/\- *lemma* countable_encodable
- \+/\- *lemma* countable.exists_surjective
- \+/\- *lemma* countable_empty
- \+/\- *lemma* countable_singleton
- \+/\- *lemma* countable.mono
- \+/\- *lemma* countable.image
- \+/\- *lemma* countable_range
- \+/\- *lemma* countable.preimage_of_inj_on
- \+/\- *lemma* countable_Union
- \+/\- *lemma* countable.sUnion
- \+/\- *lemma* countable_Union_Prop
- \+/\- *lemma* countable_union
- \+/\- *lemma* countable_insert
- \+/\- *lemma* countable.insert
- \+/\- *lemma* finite.countable
- \+/\- *lemma* subsingleton.countable
- \+/\- *lemma* countable_is_top
- \+/\- *lemma* countable_is_bot
- \+/\- *lemma* countable_set_of_finite_subset
- \+/\- *lemma* countable_pi
- \+/\- *lemma* countable.image2
- \+/\- *lemma* subset_range_enumerate
- \+/\- *def* countable.to_encodable
- \+/\- *def* enumerate_countable
- \- *def* countable
- \+/\- *def* countable.to_encodable
- \+/\- *def* enumerate_countable

modified src/geometry/manifold/charted_space.lean

modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_bsupr
- \+/\- *lemma* ae_measurable_bsupr
- \+/\- *lemma* measurable_binfi
- \+/\- *lemma* ae_measurable_binfi
- \+/\- *lemma* measurable_bsupr
- \+/\- *lemma* ae_measurable_bsupr
- \+/\- *lemma* measurable_binfi
- \+/\- *lemma* ae_measurable_binfi

modified src/measure_theory/constructions/polish.lean

modified src/measure_theory/covering/besicovitch.lean

modified src/measure_theory/covering/differentiation.lean

modified src/measure_theory/covering/vitali.lean

modified src/measure_theory/covering/vitali_family.lean
- \+/\- *lemma* index_countable
- \+/\- *lemma* index_countable

modified src/measure_theory/function/ae_measurable_order.lean

modified src/measure_theory/function/jacobian.lean

modified src/measure_theory/integral/circle_integral.lean

modified src/measure_theory/integral/divergence_theorem.lean

modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* lintegral_bUnion₀
- \+/\- *lemma* lintegral_bUnion
- \+/\- *lemma* lintegral_bUnion₀
- \+/\- *lemma* lintegral_bUnion

modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_set.pi
- \+/\- *lemma* measurable_set_pi
- \+/\- *lemma* measurable_set.pi
- \+/\- *lemma* measurable_set_pi

modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* measurable_set.bUnion
- \+/\- *lemma* measurable_set.sUnion
- \+/\- *lemma* measurable_set.bInter
- \+/\- *lemma* measurable_set.sInter
- \+/\- *lemma* set.countable.measurable_set
- \+/\- *lemma* measurable_set.bUnion
- \+/\- *lemma* measurable_set.sUnion
- \+/\- *lemma* measurable_set.bInter
- \+/\- *lemma* measurable_set.sInter
- \+/\- *lemma* set.countable.measurable_set

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_bUnion₀
- \+/\- *lemma* measure_bUnion
- \+/\- *lemma* measure_sUnion₀
- \+/\- *lemma* measure_sUnion
- \+/\- *lemma* tsum_measure_preimage_singleton
- \+/\- *lemma* measure_bUnion_to_measurable
- \+/\- *lemma* measure_bUnion_eq_supr
- \+/\- *lemma* restrict_bUnion_congr
- \+/\- *lemma* restrict_sUnion_congr
- \+/\- *lemma* ext_iff_of_bUnion_eq_univ
- \+/\- *lemma* ext_iff_of_sUnion_eq_univ
- \+/\- *lemma* bsupr_measure_Iic
- \+/\- *lemma* sigma_finite_of_countable
- \+/\- *lemma* measure_bUnion₀
- \+/\- *lemma* measure_bUnion
- \+/\- *lemma* measure_sUnion₀
- \+/\- *lemma* measure_sUnion
- \+/\- *lemma* tsum_measure_preimage_singleton
- \+/\- *lemma* measure_bUnion_to_measurable
- \+/\- *lemma* measure_bUnion_eq_supr
- \+/\- *lemma* restrict_bUnion_congr
- \+/\- *lemma* restrict_sUnion_congr
- \+/\- *lemma* ext_iff_of_bUnion_eq_univ
- \+/\- *lemma* ext_iff_of_sUnion_eq_univ
- \+/\- *lemma* bsupr_measure_Iic
- \+/\- *lemma* sigma_finite_of_countable

modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_bUnion_le
- \+/\- *lemma* measure_bUnion_null_iff
- \+/\- *lemma* measure_sUnion_null_iff
- \+/\- *lemma* ae_ball_iff
- \+/\- *lemma* measure_bUnion_le
- \+/\- *lemma* measure_bUnion_null_iff
- \+/\- *lemma* measure_sUnion_null_iff
- \+/\- *lemma* ae_ball_iff

modified src/measure_theory/measure/null_measurable.lean

modified src/measure_theory/measure/outer_measure.lean
- \+/\- *lemma* bUnion_null_iff
- \+/\- *lemma* sUnion_null_iff
- \+/\- *lemma* bUnion_null_iff
- \+/\- *lemma* sUnion_null_iff

modified src/order/filter/bases.lean
- \+/\- *lemma* countable_binfi_eq_infi_seq
- \+/\- *lemma* countable_binfi_eq_infi_seq'
- \+/\- *lemma* countable_binfi_principal_eq_seq_infi
- \+/\- *lemma* is_countably_generated_binfi_principal
- \+/\- *lemma* countable_binfi_eq_infi_seq
- \+/\- *lemma* countable_binfi_eq_infi_seq'
- \+/\- *lemma* countable_binfi_principal_eq_seq_infi
- \+/\- *lemma* is_countably_generated_binfi_principal

modified src/order/filter/countable_Inter.lean
- \+/\- *lemma* countable_sInter_mem
- \+/\- *lemma* countable_bInter_mem
- \+/\- *lemma* eventually_countable_ball
- \+/\- *lemma* eventually_le.countable_bUnion
- \+/\- *lemma* eventually_eq.countable_bUnion
- \+/\- *lemma* eventually_le.countable_bInter
- \+/\- *lemma* eventually_eq.countable_bInter
- \+/\- *lemma* countable_sInter_mem
- \+/\- *lemma* countable_bInter_mem
- \+/\- *lemma* eventually_countable_ball
- \+/\- *lemma* eventually_le.countable_bUnion
- \+/\- *lemma* eventually_eq.countable_bUnion
- \+/\- *lemma* eventually_le.countable_bInter
- \+/\- *lemma* eventually_eq.countable_bInter

modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* mk_set_le_aleph_0
- \+/\- *lemma* mk_subtype_le_aleph_0
- \+/\- *lemma* mk_set_le_aleph_0
- \+/\- *lemma* mk_subtype_le_aleph_0

modified src/set_theory/cardinal/ordinal.lean
- \+/\- *lemma* countable_iff_lt_aleph_one
- \+/\- *lemma* countable_iff_lt_aleph_one

modified src/topology/G_delta.lean
- \+/\- *lemma* is_Gδ_bInter_of_open
- \+/\- *lemma* is_Gδ_bInter
- \+/\- *lemma* is_Gδ_sInter
- \+/\- *lemma* set.countable.is_Gδ_compl
- \+/\- *lemma* is_Gδ_bInter_of_open
- \+/\- *lemma* is_Gδ_bInter
- \+/\- *lemma* is_Gδ_sInter
- \+/\- *lemma* set.countable.is_Gδ_compl

modified src/topology/algebra/order/basic.lean

modified src/topology/bases.lean
- \+/\- *lemma* _root_.set.countable.is_separable
- \+/\- *lemma* countable_countable_basis
- \+/\- *lemma* _root_.set.countable.is_separable
- \+/\- *lemma* countable_countable_basis

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/baire.lean
- \+/\- *theorem* dense_sInter_of_open
- \+/\- *theorem* dense_sInter_of_Gδ
- \+/\- *theorem* dense_sInter_of_open
- \+/\- *theorem* dense_sInter_of_Gδ

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/hausdorff_dimension.lean
- \+/\- *lemma* dimH_bUnion
- \+/\- *lemma* dimH_sUnion
- \+/\- *lemma* dimH_countable
- \+/\- *lemma* dimH_bUnion
- \+/\- *lemma* dimH_sUnion
- \+/\- *lemma* dimH_countable

modified src/topology/metric_space/kuratowski.lean

modified src/topology/subset_properties.lean
- \+/\- *lemma* sigma_compact_space.of_countable
- \+/\- *lemma* sigma_compact_space.of_countable



## [2022-06-22 18:31:20](https://github.com/leanprover-community/mathlib/commit/d8fc588)
refactor(data/finite/card): split from `basic` ([#14885](https://github.com/leanprover-community/mathlib/pull/14885))
#### Estimated changes
modified src/data/finite/basic.lean
- \- *lemma* nat.card_eq
- \- *lemma* finite.card_pos_iff
- \- *lemma* card_eq
- \- *lemma* card_le_one_iff_subsingleton
- \- *lemma* one_lt_card_iff_nontrivial
- \- *lemma* one_lt_card
- \- *lemma* card_option
- \- *lemma* card_sum
- \- *lemma* card_le_of_injective
- \- *lemma* card_le_of_embedding
- \- *lemma* card_le_of_surjective
- \- *lemma* card_eq_zero_iff
- \- *theorem* finite.card_subtype_le
- \- *theorem* finite.card_subtype_lt
- \- *def* finite.equiv_fin
- \- *def* finite.equiv_fin_of_card_eq

created src/data/finite/card.lean
- \+ *lemma* nat.card_eq
- \+ *lemma* finite.card_pos_iff
- \+ *lemma* card_eq
- \+ *lemma* card_le_one_iff_subsingleton
- \+ *lemma* one_lt_card_iff_nontrivial
- \+ *lemma* one_lt_card
- \+ *lemma* card_option
- \+ *lemma* card_le_of_injective
- \+ *lemma* card_le_of_embedding
- \+ *lemma* card_le_of_surjective
- \+ *lemma* card_eq_zero_iff
- \+ *lemma* card_sum
- \+ *theorem* finite.card_subtype_le
- \+ *theorem* finite.card_subtype_lt
- \+ *def* finite.equiv_fin
- \+ *def* finite.equiv_fin_of_card_eq



## [2022-06-22 18:31:18](https://github.com/leanprover-community/mathlib/commit/c2719ad)
feat(topology/basic): `sum.elim` of locally finite set families is locally finite ([#14826](https://github.com/leanprover-community/mathlib/pull/14826))
#### Estimated changes
modified src/order/filter/small_sets.lean
- \+ *lemma* frequently_small_sets
- \+ *lemma* frequently_small_sets_mem

modified src/topology/basic.lean
- \+ *lemma* locally_finite.eventually_finite
- \+ *lemma* locally_finite.sum_elim
- \+ *lemma* locally_finite.preimage_continuous



## [2022-06-22 18:31:17](https://github.com/leanprover-community/mathlib/commit/44bb35e)
feat({algebra/big_operators/basic,data/rat/cast}): Missing cast lemmas ([#14824](https://github.com/leanprover-community/mathlib/pull/14824))
`rat.cast_sum`, `rat.cast_prod` and `nat`, `int` lemmas about `multiset` and `list` big operators.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* cast_list_sum
- \+ *lemma* cast_list_prod
- \+ *lemma* cast_multiset_sum
- \+ *lemma* cast_multiset_prod
- \+ *lemma* cast_sum
- \+ *lemma* cast_prod
- \+ *lemma* cast_list_sum
- \+ *lemma* cast_list_prod
- \+ *lemma* cast_multiset_sum
- \+ *lemma* cast_multiset_prod
- \+ *lemma* cast_sum
- \+ *lemma* cast_prod
- \- *lemma* nat.cast_sum
- \- *lemma* int.cast_sum
- \- *lemma* nat.cast_prod
- \- *lemma* int.cast_prod

modified src/data/finsupp/basic.lean
- \+ *lemma* cast_finsupp_sum
- \+ *lemma* cast_finsupp_prod

modified src/data/rat/cast.lean
- \+/\- *lemma* coe_cast_hom
- \+ *lemma* cast_list_sum
- \+ *lemma* cast_multiset_sum
- \+ *lemma* cast_sum
- \+ *lemma* cast_list_prod
- \+ *lemma* cast_multiset_prod
- \+ *lemma* cast_prod
- \+/\- *lemma* coe_cast_hom
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_pow
- \+/\- *def* cast_hom
- \+/\- *def* cast_hom



## [2022-06-22 16:29:05](https://github.com/leanprover-community/mathlib/commit/38642ef)
chore(data/rat): rename `data.rat.basic` to `data.rat.defs` ([#14895](https://github.com/leanprover-community/mathlib/pull/14895))
This is a preparatory step for PR [#14893](https://github.com/leanprover-community/mathlib/pull/14893) that moves only the `field ℚ` instance (and its small set of dependencies) back to `data.rat.basic`; doing this in two moves should produce a neater set of diffs.
#### Estimated changes
modified archive/imo/imo1988_q6.lean

modified archive/imo/imo2013_q5.lean

modified src/algebraic_geometry/EllipticCurve.lean

renamed src/data/rat/basic.lean to src/data/rat/defs.lean

modified src/data/rat/meta_defs.lean

modified src/data/rat/order.lean

modified test/rewrite_search/rewrite_search.lean



## [2022-06-22 16:29:04](https://github.com/leanprover-community/mathlib/commit/f57c0cd)
chore(algebra/{group_power,order}): split off field lemmas ([#14849](https://github.com/leanprover-community/mathlib/pull/14849))
I want to refer to the rational numbers in the definition of a field, meaning we can't have `algebra.field.basic` in the transitive imports of `data.rat.basic`.
This is half of rearranging those imports: remove the definition of a field from the dependencies of basic lemmas about `nsmul`, `npow`, `zsmul` and `zpow`.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \- *theorem* nat.cast_le_pow_sub_div_sub
- \- *theorem* nat.cast_le_pow_div_sub

modified src/algebra/group_with_zero/power.lean
- \- *lemma* pow_minus_two_nonneg

created src/algebra/order/field_pow.lean
- \+ *lemma* pow_minus_two_nonneg
- \+ *theorem* nat.cast_le_pow_sub_div_sub
- \+ *theorem* nat.cast_le_pow_div_sub

modified src/analysis/special_functions/bernstein.lean

modified src/analysis/specific_limits/normed.lean



## [2022-06-22 13:46:51](https://github.com/leanprover-community/mathlib/commit/d939b0e)
feat(topology/vector_bundle/hom): define the vector bundle of continuous linear maps ([#14541](https://github.com/leanprover-community/mathlib/pull/14541))
* The changes in `topology/fiber_bundle` are not necessary for this PR, but perhaps nice additions
* Co-authored by: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
* Co-authored by: Patrick Massot <patrick.massot@u-psud.fr>
#### Estimated changes
modified src/topology/fiber_bundle.lean
- \+ *lemma* symm_apply_apply
- \+ *lemma* target_inter_preimage_symm_source_eq
- \+ *lemma* trans_source
- \+ *lemma* continuous_at_of_comp_right
- \+ *lemma* continuous_at_of_comp_left
- \+ *lemma* continuous_on_of_comp_right

modified src/topology/vector_bundle/basic.lean

created src/topology/vector_bundle/hom.lean
- \+ *lemma* continuous_on_continuous_linear_map_coord_change
- \+ *lemma* continuous_linear_map_apply
- \+ *lemma* continuous_linear_map_symm_apply
- \+ *lemma* continuous_linear_map_symm_apply'
- \+ *lemma* continuous_linear_map_coord_change_apply
- \+ *lemma* trivialization.base_set_continuous_linear_map
- \+ *lemma* trivialization.continuous_linear_map_apply
- \+ *def* bundle.continuous_linear_map
- \+ *def* continuous_linear_map_coord_change
- \+ *def* continuous_linear_map
- \+ *def* _root_.bundle.continuous_linear_map.topological_vector_prebundle
- \+ *def* trivialization.continuous_linear_map



## [2022-06-22 08:58:26](https://github.com/leanprover-community/mathlib/commit/ad49768)
feat(set_theory/surreal/basic): define map `surreal →+o game` ([#14783](https://github.com/leanprover-community/mathlib/pull/14783))
#### Estimated changes
modified src/set_theory/surreal/basic.lean
- \+ *theorem* zero_to_game
- \+ *theorem* one_to_game
- \+ *theorem* nat_to_game
- \+ *def* to_game



## [2022-06-22 04:11:06](https://github.com/leanprover-community/mathlib/commit/61b837f)
feat(combinatorics/simple_graph/connectivity): Connectivity is a graph property ([#14865](https://github.com/leanprover-community/mathlib/pull/14865))
`simple_graph.preconnected` and `simple_graph.connected` are preserved under graph isomorphisms.
#### Estimated changes
modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* preconnected.map
- \+ *lemma* iso.preconnected_iff
- \+ *lemma* connected.map
- \+ *lemma* iso.connected_iff



## [2022-06-22 02:09:00](https://github.com/leanprover-community/mathlib/commit/f3cd150)
fix(tactic/apply_fun.lean): instantiate mvars in apply_fun ([#14882](https://github.com/leanprover-community/mathlib/pull/14882))
Fixes leanprover-community/lean[#733](https://github.com/leanprover-community/mathlib/pull/733)
#### Estimated changes
modified src/tactic/apply_fun.lean

modified test/apply_fun.lean



## [2022-06-21 16:31:41](https://github.com/leanprover-community/mathlib/commit/3b6552e)
chore(linear_algebra/alternating): more lemmas about `curry_left` ([#14844](https://github.com/leanprover-community/mathlib/pull/14844))
This follows on from [#14802](https://github.com/leanprover-community/mathlib/pull/14802)
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+ *lemma* curry_left_zero
- \+ *lemma* curry_left_add
- \+ *lemma* curry_left_smul
- \+ *lemma* curry_left_comp_alternating_map
- \+ *lemma* curry_left_comp_linear_map

modified src/linear_algebra/exterior_algebra/basic.lean
- \+ *lemma* ι_multi_zero_apply
- \+ *lemma* ι_multi_succ_apply
- \+ *lemma* ι_multi_succ_curry_left



## [2022-06-21 16:31:40](https://github.com/leanprover-community/mathlib/commit/d953773)
feat(data/finsupp/basic): make `prod_add_index_of_disjoint` to_additive ([#14786](https://github.com/leanprover-community/mathlib/pull/14786))
Adds lemma `sum_add_index_of_disjoint (h : disjoint f1.support f2.support) (g : α → M → β) : (f1 + f2).sum g = f1.sum g + f2.sum g`
#### Estimated changes
modified src/data/finsupp/basic.lean



## [2022-06-21 16:31:39](https://github.com/leanprover-community/mathlib/commit/3e66afe)
feat(data/sigma): add reflected instance ([#14764](https://github.com/leanprover-community/mathlib/pull/14764))
#### Estimated changes
modified src/data/sigma/basic.lean



## [2022-06-21 16:31:38](https://github.com/leanprover-community/mathlib/commit/b779513)
feat(order/conditionally_complete_lattice): add `cInf_le_cInf'` ([#14719](https://github.com/leanprover-community/mathlib/pull/14719))
A version of `cInf_le_cInf` for `conditionally_complete_linear_order_bot`
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_le_cInf'



## [2022-06-21 14:57:41](https://github.com/leanprover-community/mathlib/commit/2d70b94)
golf(data/polynomial): factorization into linear factors when #roots=degree  ([#14862](https://github.com/leanprover-community/mathlib/pull/14862))
+ Golf the proofs of `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` and `C_leading_coeff_mul_prod_multiset_X_sub_C` and move them from *splitting_field.lean* to *ring_division.lean*; instead of using the former to deduce the latter as is currently done in mathlib, we prove the latter first and deduce the former easily. Remove the less general auxiliary, `private` `_of_field` versions.
+ Move `pairwise_coprime_X_sub` from *field_division.lean* to *ring_division.lean*. Rename it to `pairwise_coprime_X_sub_C` to conform with existing convention. Golf its proof using the more general new lemma `is_coprime_X_sub_C_of_is_unit_sub`.
+ Golf `monic.irreducible_of_irreducible_map`, but it's essentially the same proof.
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \- *theorem* pairwise_coprime_X_sub

modified src/data/polynomial/ring_division.lean
- \+ *lemma* is_coprime_X_sub_C_of_is_unit_sub
- \+ *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C
- \+ *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+ *theorem* pairwise_coprime_X_sub_C

modified src/field_theory/fixed.lean

modified src/field_theory/separable.lean

modified src/field_theory/splitting_field.lean
- \- *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \- *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C



## [2022-06-21 14:57:40](https://github.com/leanprover-community/mathlib/commit/ee12362)
feat(topology/metric_space/basic): Add `ball_comm` lemmas ([#14858](https://github.com/leanprover-community/mathlib/pull/14858))
This adds `closed_ball` and `sphere` comm lemmas to go with the existing `mem_ball_comm`.
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+/\- *theorem* mem_ball'
- \+/\- *theorem* mem_closed_ball'
- \+ *theorem* mem_sphere'
- \+ *theorem* mem_closed_ball_comm
- \+ *theorem* mem_sphere_comm
- \+/\- *theorem* mem_ball'
- \+/\- *theorem* mem_closed_ball'

modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* mem_ball'
- \+ *theorem* mem_closed_ball'
- \+ *theorem* mem_closed_ball_comm
- \+/\- *theorem* mem_ball'



## [2022-06-21 13:23:46](https://github.com/leanprover-community/mathlib/commit/2b5a577)
doc(data/polynomial/div): fix runaway code block ([#14864](https://github.com/leanprover-community/mathlib/pull/14864))
Also use a fully-qualilfied name for linking
#### Estimated changes
modified src/data/polynomial/div.lean



## [2022-06-21 13:23:45](https://github.com/leanprover-community/mathlib/commit/65031ca)
feat(ring_theory/dedekind_domain/ideal): drop an unneeded assumption ([#14444](https://github.com/leanprover-community/mathlib/pull/14444))
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean
- \+/\- *lemma* ideal.count_normalized_factors_eq
- \+/\- *lemma* ideal.count_normalized_factors_eq
- \+ *theorem* ideal.is_prime_iff_bot_or_prime

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* count_normalized_factors_eq'



## [2022-06-21 11:26:39](https://github.com/leanprover-community/mathlib/commit/273986a)
fix(topology/algebra/group_completion): add lemmas about nsmul and zsmul and fix diamonds ([#14846](https://github.com/leanprover-community/mathlib/pull/14846))
This prevents a diamond forming between `uniform_space.completion.has_scalar` and the default `add_monoid.nsmul` and `sub_neg_monoid.zsmul` fields; by manually defining the latter to match the former.
To do this, we add two new instances of `has_uniform_continuous_smul` for nat- and int- actions.
To use the existing scalar actions, we had to shuffle the imports around a bit.
#### Estimated changes
modified src/analysis/normed_space/completion.lean

modified src/topology/algebra/group_completion.lean

modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_continuous.pow_const
- \+ *lemma* uniform_continuous_pow_const
- \+ *lemma* uniform_continuous.zpow_const
- \+ *lemma* uniform_continuous_zpow_const

modified src/topology/algebra/uniform_mul_action.lean



## [2022-06-21 11:26:38](https://github.com/leanprover-community/mathlib/commit/2a7bde0)
feat(data{finset,set}/pointwise): Pointwise monoids are domains ([#14687](https://github.com/leanprover-community/mathlib/pull/14687))
`no_zero_divisors`/`no_zero_smul_divisors` instances for `set` and `finset`.
#### Estimated changes
modified src/algebra/module/basic.lean

modified src/data/finset/pointwise.lean

modified src/data/set/pointwise.lean



## [2022-06-21 09:14:05](https://github.com/leanprover-community/mathlib/commit/481f991)
refactor(algebra/{hom/equiv, ring/equiv}): rename `equiv_of_unique_of_unique` to `equiv_of_unique` ([#14861](https://github.com/leanprover-community/mathlib/pull/14861))
This matches [`equiv.equiv_of_unique`](https://leanprover-community.github.io/mathlib_docs/logic/equiv/basic.html#equiv.equiv_of_unique).
#### Estimated changes
modified src/algebra/hom/equiv.lean
- \+ *def* mul_equiv_of_unique
- \- *def* mul_equiv_of_unique_of_unique

modified src/algebra/ring/equiv.lean
- \+ *def* ring_equiv_of_unique
- \- *def* ring_equiv_of_unique_of_unique



## [2022-06-21 07:18:59](https://github.com/leanprover-community/mathlib/commit/e1d7cc7)
chore(set_theory/game/*): create `pgame` and `natural_ops` locales ([#14856](https://github.com/leanprover-community/mathlib/pull/14856))
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/birthday.lean

modified src/set_theory/game/impartial.lean

modified src/set_theory/game/ordinal.lean

modified src/set_theory/game/pgame.lean

modified src/set_theory/game/short.lean

modified src/set_theory/ordinal/natural_ops.lean



## [2022-06-21 07:18:57](https://github.com/leanprover-community/mathlib/commit/67e026c)
fix(tactic/norm_num): fix bad proof / bad test ([#14852](https://github.com/leanprover-community/mathlib/pull/14852))
This is a bug in master but it was first noticed in [#14683](https://github.com/leanprover-community/mathlib/pull/14683).
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



## [2022-06-21 05:57:01](https://github.com/leanprover-community/mathlib/commit/8ac19d3)
chore(data/finsupp/fin): fix spacing ([#14860](https://github.com/leanprover-community/mathlib/pull/14860))
#### Estimated changes
modified src/data/finsupp/fin.lean



## [2022-06-21 04:38:57](https://github.com/leanprover-community/mathlib/commit/326465d)
chore(set_theory/ordinal/natural_ops): use derive ([#14859](https://github.com/leanprover-community/mathlib/pull/14859))
#### Estimated changes
modified src/set_theory/ordinal/natural_ops.lean



## [2022-06-21 01:37:43](https://github.com/leanprover-community/mathlib/commit/3b5441c)
feat(data/fintype/basic): equivalence between `finset α` and `set α` for `fintype α` ([#14840](https://github.com/leanprover-community/mathlib/pull/14840))
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* finset.to_finset_coe
- \+ *lemma* finset_equiv_set_apply
- \+ *lemma* finset_equiv_set_symm_apply



## [2022-06-21 00:01:30](https://github.com/leanprover-community/mathlib/commit/87f4758)
feat(polynomial/ring_division): strengthen/generalize various lemmas ([#14839](https://github.com/leanprover-community/mathlib/pull/14839))
+ Generalize the assumption `function.injective f` in `le_root_multiplicity_map` to `map f p ≠ 0`. Strictly speaking this is not a generalization because the trivial case `p = 0` is excluded. If one do want to apply the lemma without assuming `p ≠ 0`, they can use the newly introduced `eq_root_multiplicity_map`, which is a strengthening of the original lemma (with the same hypothesis `function.injective f`).
+ Extract some common `variables` from four lemmas.
+ Generalize `eq_of_monic_of_dvd_of_nat_degree_le` to `eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le`: if a polynomial `q` is divisible by a monic polynomial `p` and has degree no greater than `p`, then `q = p`. Also remove the `is_domain` hypothesis and golf the proof.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/multiplicity.20of.20root.20in.20extension.20field/near/286736361)
#### Estimated changes
modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* le_root_multiplicity_map
- \+ *lemma* eq_root_multiplicity_map
- \+/\- *lemma* count_map_roots
- \+/\- *lemma* roots_map_of_injective_card_eq_total_degree
- \+ *lemma* eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le
- \+/\- *lemma* eq_of_monic_of_dvd_of_nat_degree_le
- \+/\- *lemma* le_root_multiplicity_map
- \+/\- *lemma* count_map_roots
- \+/\- *lemma* roots_map_of_injective_card_eq_total_degree
- \+/\- *lemma* eq_of_monic_of_dvd_of_nat_degree_le



## [2022-06-20 22:02:23](https://github.com/leanprover-community/mathlib/commit/125055b)
refactor(data/sym/basic): change notation for sym.cons ([#14853](https://github.com/leanprover-community/mathlib/pull/14853))
Switch from `::` to `::ₛ` for `sym.cons` so that it no longer conflicts with `list.cons`. This (finally) puts it in line with other notations, like `::ₘ` for `multiset.cons`.
#### Estimated changes
modified src/data/sym/basic.lean
- \+/\- *lemma* cons_inj_right
- \+/\- *lemma* cons_inj_left
- \+/\- *lemma* cons_swap
- \+/\- *lemma* coe_cons
- \+/\- *lemma* mem_cons
- \+/\- *lemma* mem_cons_of_mem
- \+/\- *lemma* mem_cons_self
- \+/\- *lemma* cons_of_coe_eq
- \+/\- *lemma* repeat_succ
- \+/\- *lemma* exists_eq_cons_of_succ
- \+/\- *lemma* cons_inj_right
- \+/\- *lemma* cons_inj_left
- \+/\- *lemma* cons_swap
- \+/\- *lemma* coe_cons
- \+/\- *lemma* mem_cons
- \+/\- *lemma* mem_cons_of_mem
- \+/\- *lemma* mem_cons_self
- \+/\- *lemma* cons_of_coe_eq
- \+/\- *lemma* repeat_succ
- \+/\- *lemma* exists_eq_cons_of_succ



## [2022-06-20 16:13:29](https://github.com/leanprover-community/mathlib/commit/9df2762)
chore(data/nat/totient): golf a proof ([#14851](https://github.com/leanprover-community/mathlib/pull/14851))
#### Estimated changes
modified src/data/nat/totient.lean
- \+/\- *lemma* _root_.zmod.card_units_eq_totient
- \+/\- *lemma* _root_.zmod.card_units_eq_totient



## [2022-06-20 13:49:56](https://github.com/leanprover-community/mathlib/commit/f855a4b)
feat(order/monotone): Monotonicity of `prod.map` ([#14843](https://github.com/leanprover-community/mathlib/pull/14843))
If `f` and `g` are monotone/antitone, then `prod.map f g` is as well.
#### Estimated changes
modified src/order/monotone.lean
- \+ *lemma* monotone.imp
- \+ *lemma* antitone.imp
- \+ *lemma* strict_mono.imp
- \+ *lemma* strict_anti.imp
- \+/\- *lemma* monotone_fst
- \+/\- *lemma* monotone_snd
- \+ *lemma* monotone.prod_map
- \+ *lemma* antitone.prod_map
- \+ *lemma* strict_mono.prod_map
- \+ *lemma* strict_anti.prod_map
- \+/\- *lemma* monotone_fst
- \+/\- *lemma* monotone_snd



## [2022-06-20 13:49:55](https://github.com/leanprover-community/mathlib/commit/66d3f89)
feat(logic/unique): functions from a `unique` type is `const` ([#14823](https://github.com/leanprover-community/mathlib/pull/14823))
+ A function `f` from a `unique` type is equal to the constant function with value `f default`, and the analogous heq version for dependent functions.
+ Also changes `Π a : α, Sort v` in the file to `α → Sort v`.
Inspired by https://github.com/leanprover-community/mathlib/pull/14724#discussion_r900542203
#### Estimated changes
modified src/logic/unique.lean
- \+/\- *lemma* pi.default_def
- \+/\- *lemma* pi.default_apply
- \+ *lemma* eq_const_of_unique
- \+ *lemma* heq_const_of_unique
- \+/\- *lemma* pi.default_def
- \+/\- *lemma* pi.default_apply



## [2022-06-20 13:49:54](https://github.com/leanprover-community/mathlib/commit/0b806ba)
docs(linear_algebra): refer to `pi.basis_fun` in `pi.basis` ([#14505](https://github.com/leanprover-community/mathlib/pull/14505))
This is a common question so the more ways we can point to the standard basis, the better!
See also Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Standard.20basis
#### Estimated changes
modified src/linear_algebra/std_basis.lean



## [2022-06-20 11:25:39](https://github.com/leanprover-community/mathlib/commit/c781c0e)
feat(data/prod/basic): Involutivity of `prod.map` ([#14845](https://github.com/leanprover-community/mathlib/pull/14845))
If `f` and `g` are involutive, then so is `prod.map f g`.
#### Estimated changes
modified src/data/prod/basic.lean
- \+ *lemma* injective.prod_map
- \+ *lemma* surjective.prod_map
- \+ *lemma* bijective.prod_map
- \+ *lemma* left_inverse.prod_map
- \+ *lemma* right_inverse.prod_map
- \+ *lemma* involutive.prod_map
- \- *lemma* function.injective.prod_map
- \- *lemma* function.surjective.prod_map



## [2022-06-20 11:25:38](https://github.com/leanprover-community/mathlib/commit/c1abe06)
refactor(linear_algebra/exterior_algebra): redefine `exterior_algebra` as `clifford_algebra 0` ([#14819](https://github.com/leanprover-community/mathlib/pull/14819))
The motivation here is to avoid having to duplicate API between these two types, else we end up having to repeat every definition that works on `clifford_algebra Q` on `exterior_algebra` for the case when `Q = 0`. This also:
* Removes `as_exterior : clifford_algebra (0 : quadratic_form R M) ≃ₐ[R] exterior_algebra R M` as the two types are reducibly defeq.
* Removes support for working with exterior algebras over semirings; while it is entirely possible to generalize `clifford_algebra` to semirings to make this removal unnecessary, it creates difficulties with elaboration, and the support for semirings was without mathematical motivation in the first place. This is in line with a [vote on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Exterior.20algebras.20over.20semiring/near/286660821).
The consequences are:
* A bunch of redundant code can be removed
* `x.reverse` and `x.involute` should now work on `x : exterior_algebra R M`.
* Future API will extend effortlessly from one to the other
#### Estimated changes
modified src/linear_algebra/clifford_algebra/basic.lean
- \- *def* as_exterior

modified src/linear_algebra/exterior_algebra/basic.lean
- \+/\- *def* exterior_algebra
- \+/\- *def* ι
- \+/\- *def* exterior_algebra
- \+/\- *def* ι

modified src/linear_algebra/exterior_algebra/grading.lean

modified test/free_algebra.lean



## [2022-06-20 11:25:37](https://github.com/leanprover-community/mathlib/commit/320ea39)
feat(data/dfinsupp/basic): add missing lemmas about `single` ([#14815](https://github.com/leanprover-community/mathlib/pull/14815))
These lemmas were missed in [#13076](https://github.com/leanprover-community/mathlib/pull/13076):
* `comap_domain_single`
* `comap_domain'_single`
* `sigma_curry_single`
* `sigma_uncurry_single`
* `extend_with_single_zero`
* `extend_with_zero`
These are useful since many induction principles replace a generic `dfinsupp` with `dfinsupp.single`.
#### Estimated changes
modified src/data/dfinsupp/basic.lean
- \+ *lemma* comap_domain_single
- \+ *lemma* comap_domain'_single
- \+ *lemma* sigma_curry_single
- \+ *lemma* sigma_uncurry_single
- \+ *lemma* extend_with_single_zero
- \+ *lemma* extend_with_zero



## [2022-06-20 11:25:36](https://github.com/leanprover-community/mathlib/commit/c5e13ba)
feat(algebra/order/pointwise): Supremum of pointwise operations ([#13669](https://github.com/leanprover-community/mathlib/pull/13669))
Pointwise operations of sets distribute over the (conditional) supremum/infimum.
#### Estimated changes
modified src/algebra/order/pointwise.lean
- \+ *lemma* cSup_one
- \+ *lemma* cInf_one
- \+ *lemma* cSup_inv
- \+ *lemma* cInf_inv
- \+ *lemma* cSup_mul
- \+ *lemma* cInf_mul
- \+ *lemma* cSup_div
- \+ *lemma* cInf_div
- \+ *lemma* Sup_one
- \+ *lemma* Inf_one
- \+ *lemma* Sup_inv
- \+ *lemma* Inf_inv
- \+ *lemma* Sup_mul
- \+ *lemma* Inf_mul
- \+ *lemma* Sup_div
- \+ *lemma* Inf_div



## [2022-06-20 09:15:57](https://github.com/leanprover-community/mathlib/commit/f9c339e)
feat(group_theory/group_action/sigma): Scalar action on a sigma type ([#14825](https://github.com/leanprover-community/mathlib/pull/14825))
`(Π i, has_scalar α (β i)) → has_scalar α (Σ i, β i)` and similar.
#### Estimated changes
modified src/group_theory/group_action/pi.lean

modified src/group_theory/group_action/prod.lean

created src/group_theory/group_action/sigma.lean
- \+ *lemma* smul_def
- \+ *lemma* smul_mk

modified src/group_theory/group_action/sum.lean



## [2022-06-20 09:15:55](https://github.com/leanprover-community/mathlib/commit/ff40b2c)
chore(algebra/group/basic): lemmas about `bit0`, `bit1`, and addition ([#14798](https://github.com/leanprover-community/mathlib/pull/14798))
#### Estimated changes
modified src/algebra/group/basic.lean
- \+ *lemma* bit0_add
- \+ *lemma* bit1_add
- \+ *lemma* bit1_add'
- \+ *lemma* bit0_sub
- \+ *lemma* bit1_sub

modified src/data/nat/basic.lean
- \+ *theorem* bit_add
- \+ *theorem* bit_add'



## [2022-06-20 09:15:53](https://github.com/leanprover-community/mathlib/commit/df50b88)
feat(order/filter/bases): basis for directed (b)infi of filters ([#14775](https://github.com/leanprover-community/mathlib/pull/14775))
#### Estimated changes
modified src/order/filter/bases.lean
- \+ *lemma* has_basis_infi_of_directed'
- \+ *lemma* has_basis_infi_of_directed
- \+ *lemma* has_basis_binfi_of_directed'
- \+ *lemma* has_basis_binfi_of_directed



## [2022-06-20 09:15:51](https://github.com/leanprover-community/mathlib/commit/2604c04)
feat(number_theory/number_field): add definitions and results about embeddings  ([#14749](https://github.com/leanprover-community/mathlib/pull/14749))
We consider the embeddings of a number field into an algebraic closed field (of char. 0) and prove some results about those. 
We also prove the ```number_field``` instance  for ```adjoint_root``` of an irreducible polynomial of `ℚ[X]`. 
From flt-regular
#### Estimated changes
modified src/number_theory/number_field.lean
- \+ *lemma* card
- \+ *lemma* eq_roots



## [2022-06-20 09:15:48](https://github.com/leanprover-community/mathlib/commit/8263a4b)
refactor(analysis/complex/upper_half_plane): move topology to a new file ([#14748](https://github.com/leanprover-community/mathlib/pull/14748))
Also add some instances and lemmas about topology on the upper half plane.
#### Estimated changes
modified src/analysis/complex/upper_half_plane/basic.lean

created src/analysis/complex/upper_half_plane/topology.lean
- \+ *lemma* open_embedding_coe
- \+ *lemma* embedding_coe
- \+ *lemma* continuous_coe
- \+ *lemma* continuous_re
- \+ *lemma* continuous_im



## [2022-06-20 09:15:46](https://github.com/leanprover-community/mathlib/commit/804afcb)
feat(geometry/manifold/diffeomorph): some additions needed for smooth vector bundles ([#14738](https://github.com/leanprover-community/mathlib/pull/14738))
* Define `diffeomorph.prod_comm`, `diffeomorph.prod_congr`, `diffeomorph.prod_assoc`
* Prove `cont_mdiff_on.comp_cont_mdiff`
* In `fiber_bundle`, define some lemmas for `local_triv_at` that were already there for `local_triv`
* Yes, this PR does a couple different things, but it is still very small
* This is part of [#14412](https://github.com/leanprover-community/mathlib/pull/14412)
#### Estimated changes
modified src/geometry/manifold/cont_mdiff.lean
- \+ *lemma* cont_mdiff_on.comp_cont_mdiff
- \+ *lemma* smooth_on.comp_smooth

modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* prod_congr_symm
- \+ *lemma* coe_prod_congr
- \+ *lemma* prod_comm_symm
- \+ *lemma* coe_prod_comm
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* prod_assoc

modified src/topology/fiber_bundle.lean
- \+/\- *lemma* local_triv_at_apply
- \+ *lemma* local_triv_at_apply_mk
- \+ *lemma* mem_local_triv_at_source
- \+ *lemma* mem_local_triv_at_target
- \+ *lemma* local_triv_symm_apply
- \- *lemma* local_triv_symm_fst
- \+/\- *lemma* local_triv_at_apply

modified src/topology/vector_bundle/basic.lean
- \+/\- *lemma* local_triv_at_apply
- \+ *lemma* local_triv_at_apply_mk
- \+/\- *lemma* local_triv_at_apply
- \+ *def* to_topological_fiber_bundle_core
- \- *def* to_topological_vector_bundle_core



## [2022-06-20 09:15:45](https://github.com/leanprover-community/mathlib/commit/04f4505)
feat(analysis/convex/join): Join of sets ([#14676](https://github.com/leanprover-community/mathlib/pull/14676))
Define the join of two sets as the union of all segments between them.
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_segment
- \+/\- *lemma* convex_open_segment
- \+/\- *lemma* convex_segment
- \+/\- *lemma* convex_open_segment

modified src/analysis/convex/hull.lean
- \+ *lemma* segment_subset_convex_hull
- \+/\- *lemma* convex_hull_singleton
- \+ *lemma* convex_hull_pair
- \+ *lemma* convex_hull_convex_hull_union_left
- \+ *lemma* convex_hull_convex_hull_union_right
- \+/\- *lemma* convex_hull_singleton

created src/analysis/convex/join.lean
- \+ *lemma* mem_convex_join
- \+ *lemma* convex_join_comm
- \+ *lemma* convex_join_mono
- \+ *lemma* convex_join_mono_left
- \+ *lemma* convex_join_mono_right
- \+ *lemma* convex_join_empty_left
- \+ *lemma* convex_join_empty_right
- \+ *lemma* convex_join_singleton_left
- \+ *lemma* convex_join_singleton_right
- \+ *lemma* convex_join_singletons
- \+ *lemma* convex_join_union_left
- \+ *lemma* convex_join_union_right
- \+ *lemma* convex_join_Union_left
- \+ *lemma* convex_join_Union_right
- \+ *lemma* segment_subset_convex_join
- \+ *lemma* subset_convex_join_left
- \+ *lemma* subset_convex_join_right
- \+ *lemma* convex_join_subset
- \+ *lemma* convex_join_subset_convex_hull
- \+ *lemma* convex_join_assoc_aux
- \+ *lemma* convex_join_assoc
- \+ *lemma* convex_join_left_comm
- \+ *lemma* convex_join_right_comm
- \+ *lemma* convex_join_convex_join_convex_join_comm
- \+ *lemma* convex_hull_insert
- \+ *lemma* convex_join_segments
- \+ *lemma* convex_join_segment_singleton
- \+ *lemma* convex_join_singleton_segment
- \+ *lemma* convex_hull_union
- \+ *def* convex_join



## [2022-06-20 07:16:13](https://github.com/leanprover-community/mathlib/commit/2903674)
refactor(order/conditionally_complete_lattice): tweak `well_founded.conditionally_complete_linear_order_with_bot` ([#14706](https://github.com/leanprover-community/mathlib/pull/14706))
We change the `well_founded` assumption on `well_founded.conditionally_complete_linear_order_bot` to an equivalent but more convenient `is_well_order` typeclass assumption. As such, we place it in the `is_well_order` namespace.
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean

modified src/order/well_founded.lean

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/ordinal/basic.lean



## [2022-06-20 04:10:04](https://github.com/leanprover-community/mathlib/commit/ae5b695)
refactor(number_theory/cyclotomic/*): refactor the definition of is_cyclotomic_extension ([#14463](https://github.com/leanprover-community/mathlib/pull/14463))
We modify the definition of `is_cyclotomic_extension`, requiring the existence of a primitive root of unity rather than a root of the cyclotomic polynomial. This removes almost all the `ne_zero` assumptions.
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* pow_prime_pow_mul_eq_one_iff

modified src/algebra/ne_zero.lean
- \+ *lemma* nat_of_ne_zero

modified src/number_theory/cyclotomic/basic.lean
- \+/\- *lemma* trans
- \+ *lemma* subsingleton_iff
- \+ *lemma* ne_zero
- \+ *lemma* ne_zero'
- \+/\- *lemma* adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
- \+/\- *lemma* adjoin_primitive_root_eq_top
- \+/\- *lemma* _root_.is_primitive_root.adjoin_is_cyclotomic_extension
- \+/\- *lemma* is_alg_closed.is_cyclotomic_extension
- \+/\- *lemma* trans
- \+/\- *lemma* adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
- \+/\- *lemma* adjoin_primitive_root_eq_top
- \+/\- *lemma* _root_.is_primitive_root.adjoin_is_cyclotomic_extension
- \+/\- *lemma* is_alg_closed.is_cyclotomic_extension

modified src/number_theory/cyclotomic/discriminant.lean

modified src/number_theory/cyclotomic/gal.lean
- \+/\- *lemma* from_zeta_aut_spec
- \+/\- *lemma* from_zeta_aut_spec

modified src/number_theory/cyclotomic/primitive_roots.lean
- \+/\- *lemma* zeta_spec
- \+ *lemma* aeval_zeta
- \+ *lemma* zeta_is_root
- \+/\- *lemma* finrank
- \+/\- *lemma* minpoly_sub_one_eq_cyclotomic_comp
- \+/\- *lemma* pow_sub_one_norm_prime_pow_ne_two
- \+/\- *lemma* pow_sub_one_norm_prime_ne_two
- \+/\- *lemma* sub_one_norm_prime_ne_two
- \+/\- *lemma* sub_one_norm_prime
- \+/\- *lemma* pow_sub_one_norm_two
- \+/\- *lemma* sub_one_norm_two
- \+/\- *lemma* pow_sub_one_norm_prime_pow_of_one_le
- \+/\- *lemma* prime_ne_two_pow_norm_zeta_pow_sub_one
- \+/\- *lemma* prime_ne_two_pow_norm_zeta_sub_one
- \+/\- *lemma* prime_ne_two_norm_zeta_sub_one
- \+/\- *lemma* two_pow_norm_zeta_sub_one
- \+/\- *lemma* zeta_spec
- \- *lemma* zeta_spec'
- \- *lemma* zeta_primitive_root
- \+/\- *lemma* finrank
- \+/\- *lemma* minpoly_sub_one_eq_cyclotomic_comp
- \+/\- *lemma* pow_sub_one_norm_prime_pow_ne_two
- \+/\- *lemma* pow_sub_one_norm_prime_ne_two
- \+/\- *lemma* sub_one_norm_prime_ne_two
- \+/\- *lemma* sub_one_norm_prime
- \+/\- *lemma* pow_sub_one_norm_two
- \+/\- *lemma* sub_one_norm_two
- \+/\- *lemma* pow_sub_one_norm_prime_pow_of_one_le
- \+/\- *lemma* prime_ne_two_pow_norm_zeta_pow_sub_one
- \+/\- *lemma* prime_ne_two_pow_norm_zeta_sub_one
- \+/\- *lemma* prime_ne_two_norm_zeta_sub_one
- \+/\- *lemma* two_pow_norm_zeta_sub_one

modified src/number_theory/cyclotomic/rat.lean

modified src/ring_theory/polynomial/cyclotomic/eval.lean
- \+/\- *lemma* eval_one_cyclotomic_not_prime_pow
- \+/\- *lemma* eval_one_cyclotomic_not_prime_pow

modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* mem_roots_of_unity'
- \+ *lemma* mem_roots_of_unity_prime_pow_mul_iff
- \+ *lemma* ne_zero'



## [2022-06-20 00:03:55](https://github.com/leanprover-community/mathlib/commit/10a5275)
feat(analysis/normed/group/basic): `isometry.norm_map_of_map_zero` ([#14836](https://github.com/leanprover-community/mathlib/pull/14836))
Add the lemma that an isometry of `semi_normed_group`s that preserves
0 preserves the norm.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+ *lemma* isometry.norm_map_of_map_zero



## [2022-06-19 23:24:05](https://github.com/leanprover-community/mathlib/commit/cf118ee)
feat(analysis/complex/upper_half_plane): add `upper_half_plane.mk` ([#14795](https://github.com/leanprover-community/mathlib/pull/14795))
#### Estimated changes
modified src/analysis/complex/upper_half_plane/basic.lean
- \+ *lemma* mk_re
- \+ *lemma* mk_im
- \+ *lemma* coe_mk
- \+ *lemma* mk_coe
- \+ *lemma* re_add_im
- \+ *def* mk



## [2022-06-19 17:24:08](https://github.com/leanprover-community/mathlib/commit/26279c5)
chore(algebraic_geometry/function_field): fix timeout in `function_field.algebra` ([#14830](https://github.com/leanprover-community/mathlib/pull/14830))
Reduces `elaboration of function_field.algebra` from ~29.3s to ~0.4s.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/286714162)
#### Estimated changes
modified src/algebraic_geometry/function_field.lean



## [2022-06-19 16:13:12](https://github.com/leanprover-community/mathlib/commit/65c9ffb)
feat(topology/algebra/infinite_sum) Sums over Z vs sums over N ([#14667](https://github.com/leanprover-community/mathlib/pull/14667))
This PR adds some functions for handling infinite sums indexed by the integers, relating them to sums over the naturals.
#### Estimated changes
modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.int_rec
- \+ *lemma* has_sum.nonneg_add_neg
- \+ *lemma* has_sum.pos_add_zero_add_neg
- \+ *lemma* has_sum.sum_nat_of_sum_int



## [2022-06-19 12:34:38](https://github.com/leanprover-community/mathlib/commit/f460576)
feat(group_theory/group_action/sum): Scalar action on a sum of types ([#14818](https://github.com/leanprover-community/mathlib/pull/14818))
`has_scalar α β → has_scalar α γ → has_scalar α (β ⊕ γ)` and similar.
#### Estimated changes
created src/group_theory/group_action/sum.lean
- \+ *lemma* smul_def
- \+ *lemma* smul_inl
- \+ *lemma* smul_inr
- \+ *lemma* smul_swap



## [2022-06-19 09:55:31](https://github.com/leanprover-community/mathlib/commit/5dabef8)
feat(set_theory/game/basic): Basic lemmas on `inv` ([#13840](https://github.com/leanprover-community/mathlib/pull/13840))
Note that we've redefined `inv` so that `inv x = 0` when `x ≈ 0`. This is because, in order to lift it to an operation on surreals, we need to prove that equivalent numeric games give equivalent numeric values, and this isn't the case otherwise.
#### Estimated changes
modified src/set_theory/game/basic.lean
- \+ *theorem* inv_val_is_empty
- \+ *theorem* zero_lf_inv'
- \+ *theorem* inv'_zero_equiv
- \+ *theorem* inv'_one_equiv
- \+ *theorem* inv_eq_of_equiv_zero
- \+ *theorem* inv_zero
- \+ *theorem* inv_eq_of_pos
- \+ *theorem* inv_eq_of_lf_zero
- \+ *theorem* inv_one_equiv
- \+ *def* inv'_zero
- \+ *def* inv'_one
- \+ *def* inv_one



## [2022-06-19 09:12:48](https://github.com/leanprover-community/mathlib/commit/69686e7)
feat(algebra/category/Module): Tannaka duality for rings ([#14352](https://github.com/leanprover-community/mathlib/pull/14352))
Obviously this is not the most interesting statement that one might label "Tannaka duality", but perhaps it can get the ball rolling. :-)
#### Estimated changes
modified src/algebra/category/Module/basic.lean

created src/algebra/category/Module/tannaka.lean
- \+ *def* ring_equiv_End_forget₂



## [2022-06-19 07:01:49](https://github.com/leanprover-community/mathlib/commit/7f358d0)
feat(category_theory/preadditive/eilenberg_moore): (Co)algebras over a (co)monad are preadditive ([#14811](https://github.com/leanprover-community/mathlib/pull/14811))
The category of algebras over an additive monad on a preadditive category is preadditive (and the dual result).
#### Estimated changes
created src/category_theory/preadditive/eilenberg_moore.lean



## [2022-06-18 19:10:48](https://github.com/leanprover-community/mathlib/commit/0a5b9eb)
feat(set_theory/game/pgame): tweak lemmas ([#14810](https://github.com/leanprover-community/mathlib/pull/14810))
This PR does the following:
- uncurry `le_of_forall_lf` and `le_of_forall_lt`.
- remove `lf_of_exists_le`, as it's made redundant by `lf_of_move_right_le` and `lf_of_le_move_left`.
- golfing.
#### Estimated changes
modified src/set_theory/game/ordinal.lean

modified src/set_theory/game/pgame.lean
- \+/\- *theorem* le_of_forall_lf
- \+/\- *theorem* move_left_lf_of_le
- \+/\- *theorem* lf_move_right_of_le
- \+/\- *theorem* lf_of_move_right_le
- \+/\- *theorem* lf_of_le_move_left
- \+/\- *theorem* le_of_forall_lt
- \+/\- *theorem* le_of_forall_lf
- \- *theorem* lf_of_exists_le
- \+/\- *theorem* move_left_lf_of_le
- \+/\- *theorem* lf_move_right_of_le
- \+/\- *theorem* lf_of_move_right_le
- \+/\- *theorem* lf_of_le_move_left
- \+/\- *theorem* le_of_forall_lt

modified src/set_theory/surreal/dyadic.lean



## [2022-06-18 16:59:43](https://github.com/leanprover-community/mathlib/commit/4264220)
feat(analysis/asymptotics): add several lemmas ([#14805](https://github.com/leanprover-community/mathlib/pull/14805))
Also make `𝕜` explicit in `asymptotics.is_O_with_const_one` and `asymptotics.is_O_const_one`.
#### Estimated changes
modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+ *lemma* is_o.add_is_equivalent

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/asymptotics/theta.lean
- \+/\- *lemma* is_Theta_refl
- \+ *lemma* is_Theta_rfl
- \+ *lemma* is_Theta.trans_eventually_eq
- \+ *lemma* _root_.filter.eventually_eq.trans_is_Theta
- \+ *lemma* is_Theta_norm_left
- \+ *lemma* is_Theta_norm_right
- \+ *lemma* is_Theta_of_norm_eventually_eq
- \+ *lemma* is_Theta_of_norm_eventually_eq'
- \+ *lemma* is_Theta.div
- \+/\- *lemma* is_Theta_refl



## [2022-06-18 16:59:42](https://github.com/leanprover-community/mathlib/commit/100975e)
feat(geometry/euclidean/inversion) new file ([#14692](https://github.com/leanprover-community/mathlib/pull/14692))
* Define `euclidean_geometry.inversion`.
* Prove Ptolemy's inequality.
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* dist_div_norm_sq_smul

created src/geometry/euclidean/inversion.lean
- \+ *lemma* inversion_vsub_center
- \+ *lemma* inversion_self
- \+ *lemma* inversion_dist_center
- \+ *lemma* inversion_of_mem_sphere
- \+ *lemma* dist_inversion_center
- \+ *lemma* dist_center_inversion
- \+ *lemma* inversion_inversion
- \+ *lemma* inversion_involutive
- \+ *lemma* inversion_surjective
- \+ *lemma* inversion_injective
- \+ *lemma* inversion_bijective
- \+ *lemma* dist_inversion_inversion
- \+ *lemma* mul_dist_le_mul_dist_add_mul_dist
- \+ *def* inversion



## [2022-06-18 16:59:41](https://github.com/leanprover-community/mathlib/commit/92d5fdf)
feat(topology/metric_space/baire): generalize some lemmas ([#14633](https://github.com/leanprover-community/mathlib/pull/14633))
Add `is_Gδ.dense_{s,b,}Union_interior_of_closed`.
#### Estimated changes
modified src/topology/metric_space/baire.lean
- \+ *lemma* is_Gδ.dense_Union_interior_of_closed
- \+ *lemma* is_Gδ.dense_bUnion_interior_of_closed
- \+ *lemma* is_Gδ.dense_sUnion_interior_of_closed



## [2022-06-18 16:59:40](https://github.com/leanprover-community/mathlib/commit/f1b0402)
feat(tactic/core + test/list_summands): a function extracting a list of summands from an expression ([#14617](https://github.com/leanprover-community/mathlib/pull/14617))
This meta def is used in [#13483](https://github.com/leanprover-community/mathlib/pull/13483), where `move_add` is defined.
A big reason for splitting these 5 lines off the main PR is that they are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.
#### Estimated changes
modified src/tactic/core.lean

created test/list_summands.lean



## [2022-06-18 15:26:18](https://github.com/leanprover-community/mathlib/commit/3a8e0a1)
feat(group_theory/torsion): define the p-primary component of a group ([#14312](https://github.com/leanprover-community/mathlib/pull/14312))
#### Estimated changes
modified src/group_theory/order_of_element.lean
- \+ *lemma* exists_order_of_eq_prime_pow_iff

modified src/group_theory/torsion.lean
- \+ *lemma* primary_component.exists_order_of_eq_prime_pow
- \+ *lemma* primary_component.disjoint
- \+ *lemma* primary_component.is_p_group
- \+/\- *lemma* is_torsion_free.quotient_torsion
- \+/\- *lemma* is_torsion_free.quotient_torsion
- \+ *def* primary_component
- \+ *def* primary_component



## [2022-06-18 12:50:23](https://github.com/leanprover-community/mathlib/commit/3abee05)
chore(order/pfilter): more `principal` API ([#14759](https://github.com/leanprover-community/mathlib/pull/14759))
`principal` and `Inf` form a Galois coinsertion.
#### Estimated changes
modified src/order/pfilter.lean
- \+ *lemma* mem_def
- \+ *lemma* mem_principal
- \+ *lemma* antitone_principal
- \+ *lemma* principal_le_principal_iff
- \+ *lemma* Inf_gc
- \+/\- *def* principal
- \+ *def* Inf_gi
- \+/\- *def* principal



## [2022-06-18 09:28:02](https://github.com/leanprover-community/mathlib/commit/39986ae)
chore(data/nat/lattice): add `nat.infi_of_empty` to match `_root_.infi_of_empty` ([#14797](https://github.com/leanprover-community/mathlib/pull/14797))
#### Estimated changes
modified src/data/nat/lattice.lean
- \+ *lemma* infi_of_empty



## [2022-06-18 08:28:16](https://github.com/leanprover-community/mathlib/commit/7fb5ed2)
feat(data/complex/basic): add `complex.abs_le_sqrt_two_mul_max` ([#14804](https://github.com/leanprover-community/mathlib/pull/14804))
#### Estimated changes
modified src/data/complex/basic.lean
- \+ *lemma* abs_le_sqrt_two_mul_max



## [2022-06-17 23:41:50](https://github.com/leanprover-community/mathlib/commit/bd6b98b)
feat(linear_algebra/alternating): add more compositional API ([#14802](https://github.com/leanprover-community/mathlib/pull/14802))
These will be helpful in relating `alternating_map`s to the `exterior_algebra`.
This adds:
* `alternating_map.curry_left`
* `alternating_map.const_linear_equiv_of_is_empty`
* `alternating_map.dom_dom_congr`
#### Estimated changes
modified src/linear_algebra/alternating.lean
- \+ *lemma* dom_dom_congr_refl
- \+ *lemma* dom_dom_congr_trans
- \+ *lemma* dom_dom_congr_zero
- \+ *lemma* dom_dom_congr_add
- \+ *lemma* dom_dom_congr_eq_iff
- \+ *lemma* dom_dom_congr_eq_zero_iff
- \+ *lemma* dom_dom_congr_perm
- \+/\- *lemma* coe_dom_dom_congr
- \+ *lemma* map_vec_cons_add
- \+ *lemma* map_vec_cons_smul
- \+ *lemma* curry_left_same
- \+/\- *lemma* coe_dom_dom_congr
- \+/\- *def* of_subsingleton
- \+ *def* const_of_is_empty
- \+ *def* dom_dom_congr
- \+ *def* dom_dom_congr_equiv
- \+ *def* curry_left
- \+ *def* curry_left_linear_map
- \+ *def* const_linear_equiv_of_is_empty
- \+/\- *def* of_subsingleton



## [2022-06-17 23:41:49](https://github.com/leanprover-community/mathlib/commit/0c47657)
chore(order/symm_diff): add lemma about `bxor` ([#14801](https://github.com/leanprover-community/mathlib/pull/14801))
#### Estimated changes
modified src/order/boolean_algebra.lean
- \+ *lemma* bool.sup_eq_bor
- \+ *lemma* bool.inf_eq_band
- \+ *lemma* bool.compl_eq_bnot

modified src/order/symm_diff.lean
- \+ *lemma* bool.symm_diff_eq_bxor



## [2022-06-17 22:43:38](https://github.com/leanprover-community/mathlib/commit/4ff9e93)
feat(analysis/complex/basic): add a few lemmas about `dist` on `complex` ([#14796](https://github.com/leanprover-community/mathlib/pull/14796))
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* dist_eq_re_im
- \+ *lemma* dist_mk
- \+ *lemma* dist_of_re_eq
- \+ *lemma* nndist_of_re_eq
- \+ *lemma* edist_of_re_eq
- \+ *lemma* dist_of_im_eq
- \+ *lemma* nndist_of_im_eq
- \+ *lemma* edist_of_im_eq
- \+ *lemma* nndist_conj_self
- \+/\- *lemma* dist_self_conj
- \+ *lemma* nndist_self_conj
- \+/\- *lemma* dist_self_conj



## [2022-06-17 20:37:43](https://github.com/leanprover-community/mathlib/commit/d2369bc)
feat(data/set/intervals): add two `ssubset` lemmas ([#14793](https://github.com/leanprover-community/mathlib/pull/14793))
#### Estimated changes
modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioi_ssubset_Ici_self
- \+ *lemma* Iio_ssubset_Iic_self



## [2022-06-17 18:57:26](https://github.com/leanprover-community/mathlib/commit/e23de85)
feat(algebra/algebra/basic) : add ring_hom.equiv_rat_alg_hom ([#14772](https://github.com/leanprover-community/mathlib/pull/14772))
Proves the equivalence between `ring_hom` and `rat_alg_hom`.
From flt-regular
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* to_rat_alg_hom_to_ring_hom
- \+ *lemma* alg_hom.to_ring_hom_to_rat_alg_hom
- \+ *def* ring_hom.equiv_rat_alg_hom



## [2022-06-17 17:39:07](https://github.com/leanprover-community/mathlib/commit/260d472)
feat(order/topology/**/uniform*): Lemmas about uniform convergence ([#14587](https://github.com/leanprover-community/mathlib/pull/14587))
To prove facts about uniform convergence, it is often useful to manipulate the various functions without dealing with the ε's and δ's. To do so, you need auxiliary lemmas about adding/muliplying/etc Cauchy sequences.
This commit adds several such lemmas. It supports [#14090](https://github.com/leanprover-community/mathlib/pull/14090), which we're slowly transforming to use these lemmas instead of doing direct ε/δ manipulation.
#### Estimated changes
modified src/order/filter/bases.lean
- \- *lemma* prod_assoc

modified src/order/filter/basic.lean
- \+ *lemma* map_swap4_eq_comap
- \+ *lemma* tendsto_prod_swap
- \+ *lemma* eventually.diag_of_prod
- \+ *lemma* tendsto_diag
- \+ *lemma* prod_assoc
- \+ *lemma* tendsto_prod_assoc
- \+ *lemma* tendsto_prod_assoc_symm
- \+ *lemma* map_swap4_prod
- \+ *lemma* tendsto_swap4_prod
- \+ *theorem* prod_assoc_symm

modified src/topology/algebra/uniform_group.lean
- \+ *lemma* tendsto_uniformly_on.mul
- \+ *lemma* tendsto_uniformly_on.div
- \+ *lemma* uniform_cauchy_seq_on.mul
- \+ *lemma* uniform_cauchy_seq_on.div

modified src/topology/continuous_function/algebra.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on.congr
- \+ *lemma* uniform_continuous.comp_tendsto_uniformly_on
- \+ *lemma* uniform_continuous.comp_tendsto_uniformly
- \+ *lemma* tendsto_prod_principal_iff
- \+ *lemma* tendsto_uniformly_on_empty
- \+ *lemma* tendsto_uniformly_on_singleton_iff_tendsto
- \+ *lemma* filter.tendsto.tendsto_uniformly_on_const
- \+ *lemma* uniform_cauchy_seq_on.mono
- \+ *lemma* uniform_cauchy_seq_on.comp
- \+ *lemma* uniform_continuous.comp_uniform_cauchy_seq_on
- \+ *lemma* uniform_cauchy_seq_on.prod_map
- \+ *lemma* uniform_cauchy_seq_on.prod
- \+ *lemma* uniform_cauchy_seq_on.prod'
- \- *lemma* tendsto_uniformly_on.comp'
- \- *lemma* tendsto_uniformly.comp'



## [2022-06-17 16:27:29](https://github.com/leanprover-community/mathlib/commit/545f0fb)
feat(category_theory/monad/kleisli): dualise kleisli of monad to cokleisli of comonad ([#14799](https://github.com/leanprover-community/mathlib/pull/14799))
This PR defines the (co)Kleisli category of a comonad, defines the corresponding adjunction, and proves that it gives rise to the original comonad.
#### Estimated changes
modified src/category_theory/monad/kleisli.lean
- \+ *def* cokleisli
- \+ *def* to_cokleisli
- \+ *def* from_cokleisli
- \+ *def* adj
- \+ *def* to_cokleisli_comp_from_cokleisli_iso_self



## [2022-06-17 15:08:42](https://github.com/leanprover-community/mathlib/commit/ade72ab)
refactor(linear_algebra/quadratic_form/basic): generalize to semiring ([#14303](https://github.com/leanprover-community/mathlib/pull/14303))
This uses a slightly nicer strategy than the one suggested by @adamtopaz [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Exterior.20algebras.20over.20semiring/near/282808284).
The main motivation here is to be able to talk about `0 : quadratic_form R M` even when there is no negation available, as that will let us merge `clifford_algebra`  (which currently requires negation) and `exterior_algebra` (which does not).
It's likely this generalization is broadly not very useful, so this adds a `quadratic_form.of_polar` constructor to preserve the old more convenient API.
Note the `.bib` file changed slightly as I ran the autoformatting tool.
#### Estimated changes
modified docs/references.bib

modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* polar_add_left_iff
- \+/\- *lemma* to_fun_eq_coe
- \+ *lemma* exists_companion
- \+ *lemma* map_add_add_add_map
- \+/\- *lemma* map_smul_of_tower
- \+ *lemma* some_exists_companion
- \+/\- *lemma* coe_fn_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_fn_sub
- \+/\- *lemma* sub_apply
- \+/\- *lemma* lin_mul_lin_apply
- \+/\- *lemma* add_lin_mul_lin
- \+/\- *lemma* lin_mul_lin_add
- \+/\- *lemma* lin_mul_lin_comp
- \+/\- *lemma* proj_apply
- \+/\- *lemma* basis_repr_eq_of_is_Ortho
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* map_smul_of_tower
- \+/\- *lemma* coe_fn_neg
- \+/\- *lemma* neg_apply
- \+/\- *lemma* coe_fn_sub
- \+/\- *lemma* sub_apply
- \+/\- *lemma* lin_mul_lin_apply
- \+/\- *lemma* add_lin_mul_lin
- \+/\- *lemma* lin_mul_lin_add
- \+/\- *lemma* lin_mul_lin_comp
- \+/\- *lemma* proj_apply
- \+/\- *lemma* basis_repr_eq_of_is_Ortho
- \+ *def* polar_bilin
- \+ *def* of_polar
- \+/\- *def* lin_mul_lin
- \+/\- *def* sq
- \+/\- *def* proj
- \+/\- *def* weighted_sum_squares
- \+/\- *def* lin_mul_lin
- \+/\- *def* sq
- \+/\- *def* proj
- \+/\- *def* weighted_sum_squares

modified src/linear_algebra/quadratic_form/isometry.lean

modified src/linear_algebra/quadratic_form/prod.lean



## [2022-06-17 13:35:37](https://github.com/leanprover-community/mathlib/commit/9c2b890)
feat(group_theory/sylow): API lemmas for smul and subtype  ([#14521](https://github.com/leanprover-community/mathlib/pull/14521))
This PR adds some API lemmas for smul and subtype.
#### Estimated changes
modified src/group_theory/subgroup/pointwise.lean
- \+ *lemma* conj_smul_le_of_le
- \+ *lemma* conj_smul_subgroup_of

modified src/group_theory/sylow.lean
- \+ *lemma* sylow.smul_le
- \+ *lemma* sylow.smul_subtype



## [2022-06-17 11:03:20](https://github.com/leanprover-community/mathlib/commit/0be36f6)
feat(data/list/of_fn): Add `list.of_fn_add` and `list.of_fn_mul` ([#14370](https://github.com/leanprover-community/mathlib/pull/14370))
This adds some lemmas to split up lists generated over `fin (n + m)` and `fin (n * m)` into their constituent parts.
It also adds a congr lemma to allow `list.of_fn (λ i : fin n, _)` to be rewritten into `list.of_fn (λ i : fin m, _)` by `simp` when `h : n = m` is available.
I'll need these eventually to prove some things about products of tensor powers.
#### Estimated changes
modified src/data/list/join.lean
- \+ *lemma* join_concat

modified src/data/list/of_fn.lean
- \+ *theorem* of_fn_congr
- \+ *theorem* of_fn_succ'
- \+ *theorem* of_fn_add
- \+ *theorem* of_fn_mul
- \+ *theorem* of_fn_mul'



## [2022-06-17 08:38:50](https://github.com/leanprover-community/mathlib/commit/e427a0e)
feat(set/basic, order/boolean_algebra): generalized `compl_comp_compl` ([#14784](https://github.com/leanprover-community/mathlib/pull/14784))
This PR generalizes `compl_comp_compl` to apply whenever there is a `boolean_algebra` instance. We also make the set parameter of `compl_compl_image` explicit.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *theorem* compl_compl_image
- \- *theorem* compl_comp_compl
- \+/\- *theorem* compl_compl_image

modified src/order/boolean_algebra.lean
- \+ *theorem* compl_comp_compl



## [2022-06-17 01:10:15](https://github.com/leanprover-community/mathlib/commit/d21469e)
feat(set_theory/ordinal/basic): improve docs on `lift`, add `simp` lemmas ([#14599](https://github.com/leanprover-community/mathlib/pull/14599))
This is pretty much the same thing as [#14596](https://github.com/leanprover-community/mathlib/pull/14596), just on `ordinal.lift` instead of `cardinal.lift`.
#### Estimated changes
modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* lift_umax
- \+ *theorem* lift_umax'
- \+/\- *theorem* lift_id'
- \+ *theorem* lift_uzero
- \+/\- *theorem* lift_lift
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_lift



## [2022-06-16 22:34:16](https://github.com/leanprover-community/mathlib/commit/d0b93fa)
feat(set_theory/{pgame, basic}): Notation for `relabelling`, golfing ([#14155](https://github.com/leanprover-community/mathlib/pull/14155))
We introduce the notation `≡r` for relabellings between two pre-games. We also golf many theorems on relabellings.
#### Estimated changes
modified src/set_theory/game/basic.lean
- \+/\- *theorem* mul_zero_equiv
- \+/\- *theorem* zero_mul_equiv
- \+/\- *theorem* mul_zero_equiv
- \+/\- *theorem* zero_mul_equiv
- \+/\- *def* mul_zero_relabelling
- \+/\- *def* zero_mul_relabelling
- \+/\- *def* mul_zero_relabelling
- \+/\- *def* zero_mul_relabelling

modified src/set_theory/game/birthday.lean
- \+/\- *theorem* relabelling.birthday_congr
- \+/\- *theorem* relabelling.birthday_congr

modified src/set_theory/game/impartial.lean
- \+/\- *theorem* impartial_congr
- \+/\- *theorem* impartial_congr

modified src/set_theory/game/nim.lean
- \+/\- *def* nim_zero_relabelling
- \+/\- *def* nim_zero_relabelling

modified src/set_theory/game/pgame.lean
- \+/\- *theorem* relabelling.le
- \+ *theorem* relabelling.ge
- \+/\- *theorem* relabelling.equiv
- \+/\- *theorem* equiv.is_empty
- \+/\- *theorem* relabelling.le
- \+/\- *theorem* relabelling.equiv
- \+/\- *theorem* equiv.is_empty
- \+ *def* restricted.trans
- \+/\- *def* relabelling.restricted
- \+/\- *def* relabelling.refl
- \+/\- *def* relabelling.symm
- \+/\- *def* relabelling.trans
- \+/\- *def* relabelling.is_empty
- \+/\- *def* relabel
- \+/\- *def* relabelling.neg_congr
- \+/\- *def* add_zero_relabelling
- \+/\- *def* zero_add_relabelling
- \+/\- *def* relabelling.add_congr
- \+/\- *def* relabelling.sub_congr
- \+/\- *def* neg_add_relabelling
- \+/\- *def* add_comm_relabelling
- \+/\- *def* add_assoc_relabelling
- \+/\- *def* relabelling.restricted
- \+/\- *def* relabelling.refl
- \+/\- *def* relabelling.symm
- \+/\- *def* relabelling.trans
- \+/\- *def* relabelling.is_empty
- \+/\- *def* relabel
- \+/\- *def* relabelling.neg_congr
- \+/\- *def* add_zero_relabelling
- \+/\- *def* zero_add_relabelling
- \+/\- *def* relabelling.add_congr
- \+/\- *def* relabelling.sub_congr
- \+/\- *def* neg_add_relabelling
- \+/\- *def* add_comm_relabelling
- \+/\- *def* add_assoc_relabelling



## [2022-06-16 19:20:25](https://github.com/leanprover-community/mathlib/commit/ae10dce)
feat(algebra/direct_sum/decomposition): add decompositions into a direct sum ([#14626](https://github.com/leanprover-community/mathlib/pull/14626))
This is a constructive version of `direct_sum.is_internal`, and generalizes the existing `graded_algebra`.
The main user-facing changes are:
* `graded_algebra.decompose` is now spelt `direct_sum.decompose_alg_hom`
* The simp normal form of decomposition is now `direct_sum.decompose`.
* `graded_algebra.support 𝒜 x` is now spelt `(decompose 𝒜 x).support`
* `left_inv` and `right_inv` has swapped, now with meaning "the decomposition is the (left|right) inverse of the canonical map" rather than the other way around
To keep this from growing even larger, I've left `graded_algebra.proj` alone for a future refactor.
#### Estimated changes
modified counterexamples/homogeneous_prime_not_prime.lean
- \+/\- *lemma* grading.right_inv
- \+/\- *lemma* grading.left_inv
- \+/\- *lemma* grading.left_inv
- \+/\- *lemma* grading.right_inv

created src/algebra/direct_sum/decomposition.lean
- \+ *lemma* decomposition.decompose'_eq
- \+ *lemma* decompose_symm_of
- \+ *lemma* decompose_coe
- \+ *lemma* decompose_of_mem
- \+ *lemma* decompose_of_mem_same
- \+ *lemma* decompose_of_mem_ne
- \+ *lemma* decompose_zero
- \+ *lemma* decompose_symm_zero
- \+ *lemma* decompose_add
- \+ *lemma* decompose_symm_add
- \+ *lemma* decompose_sum
- \+ *lemma* decompose_symm_sum
- \+ *lemma* sum_support_decompose
- \+ *lemma* decompose_neg
- \+ *lemma* decompose_symm_neg
- \+ *lemma* decompose_sub
- \+ *lemma* decompose_symm_sub
- \+ *lemma* decompose_smul
- \+ *def* decompose
- \+ *def* decompose_add_equiv
- \+ *def* decompose_linear_equiv

modified src/algebra/monoid_algebra/grading.lean

modified src/algebraic_geometry/projective_spectrum/topology.lean

modified src/ring_theory/graded_algebra/basic.lean
- \+ *lemma* decompose_one
- \+ *lemma* decompose_symm_one
- \+ *lemma* decompose_mul
- \+ *lemma* decompose_symm_mul
- \+/\- *lemma* graded_algebra.mem_support_iff
- \- *lemma* graded_algebra.decompose'_def
- \- *lemma* graded_algebra.decompose_symm_of
- \- *lemma* graded_algebra.decompose_coe
- \- *lemma* graded_algebra.decompose_of_mem
- \- *lemma* graded_algebra.decompose_of_mem_same
- \- *lemma* graded_algebra.decompose_of_mem_ne
- \+/\- *lemma* graded_algebra.mem_support_iff
- \- *lemma* graded_algebra.sum_support_decompose
- \+ *def* decompose_alg_equiv
- \- *def* graded_algebra.decompose
- \- *def* graded_algebra.support

modified src/ring_theory/graded_algebra/homogeneous_ideal.lean

modified src/ring_theory/graded_algebra/radical.lean



## [2022-06-16 19:20:24](https://github.com/leanprover-community/mathlib/commit/67da272)
feat(analysis/inner_product_space): Gram-Schmidt Basis ([#14514](https://github.com/leanprover-community/mathlib/pull/14514))
When the Gram-Schmidt procedure is given a basis, it produces a basis.
This pull request also refactors the lemma `gram_schmidt_span`. The new versions of the lemmas cover the span of `Iio`, the span of `Iic` and the span of the complete set of input vectors. I was also able to remove some type classes in the process.
#### Estimated changes
modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+/\- *lemma* gram_schmidt_zero
- \+ *lemma* mem_span_gram_schmidt
- \+ *lemma* gram_schmidt_mem_span
- \+ *lemma* span_gram_schmidt_Iic
- \+ *lemma* span_gram_schmidt_Iio
- \+/\- *lemma* span_gram_schmidt
- \+/\- *lemma* gram_schmidt_ne_zero_coe
- \+/\- *lemma* gram_schmidt_ne_zero
- \+ *lemma* gram_schmidt_triangular
- \+ *lemma* gram_schmidt_linear_independent
- \+ *lemma* coe_gram_schmidt_basis
- \+/\- *lemma* gram_schmidt_normed_unit_length_coe
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \+ *lemma* span_gram_schmidt_normed
- \+ *lemma* span_gram_schmidt_normed_range
- \+/\- *lemma* gram_schmidt_zero
- \+/\- *lemma* span_gram_schmidt
- \+/\- *lemma* gram_schmidt_ne_zero_coe
- \+/\- *lemma* gram_schmidt_ne_zero
- \+/\- *lemma* gram_schmidt_normed_unit_length_coe
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \+/\- *theorem* gram_schmidt_orthonormal
- \+/\- *theorem* gram_schmidt_orthonormal

modified src/linear_algebra/span.lean
- \+ *lemma* span_eq_span



## [2022-06-16 15:46:22](https://github.com/leanprover-community/mathlib/commit/988f160)
fix(data/rat/basic): Remove incorrect simp attribute ([#14765](https://github.com/leanprover-community/mathlib/pull/14765))
Remove simp attribute that breaks `field_simp`.
#### Estimated changes
modified src/data/rat/basic.lean
- \+/\- *lemma* coe_int_div_eq_mk
- \+/\- *lemma* coe_int_div_eq_mk



## [2022-06-16 15:46:20](https://github.com/leanprover-community/mathlib/commit/6c46641)
feat(linear_algebra/clifford_algebra/fold): Add recursors for folding along generators ([#14619](https://github.com/leanprover-community/mathlib/pull/14619))
This adds `clifford_algebra.fold{l,r}` and `clifford_algebra.{left,right}_induction`.
The former are analogous to `list.foldl` and `list.foldr`, while the latter are two stronger variants of `clifford_algebra.induction`.
We don't bother duplicating these for the `exterior_algebra`, as a future PR will make `exterior_algebra = clifford_algebra 0` true by `rfl`.
This construction can be used to show:
* `clifford_algebra Q ≃ₗ[R] exterior_algebra R M` (when `invertible 2`)
* `clifford_algebra Q ≃ₐ[R] clifford_algebra.even (Q' Q)` (where `Q' Q` is a quadratic form over an augmented `V`)
These will follow in future PRs.
#### Estimated changes
modified src/linear_algebra/clifford_algebra/basic.lean

created src/linear_algebra/clifford_algebra/fold.lean
- \+ *lemma* foldr_ι
- \+ *lemma* foldr_algebra_map
- \+ *lemma* foldr_one
- \+ *lemma* foldr_mul
- \+ *lemma* foldr_prod_map_ι
- \+ *lemma* foldl_reverse
- \+ *lemma* foldr_reverse
- \+ *lemma* foldl_ι
- \+ *lemma* foldl_algebra_map
- \+ *lemma* foldl_one
- \+ *lemma* foldl_mul
- \+ *lemma* foldl_prod_map_ι
- \+ *lemma* right_induction
- \+ *lemma* left_induction
- \+ *def* foldr
- \+ *def* foldl



## [2022-06-16 15:46:18](https://github.com/leanprover-community/mathlib/commit/7584a10)
feat(set_theory/game/ordinal): addition of ordinals on games matches natural addition ([#14298](https://github.com/leanprover-community/mathlib/pull/14298))
#### Estimated changes
modified src/set_theory/game/birthday.lean

modified src/set_theory/game/ordinal.lean
- \+ *theorem* to_pgame_add
- \+ *theorem* to_pgame_add_mk



## [2022-06-16 12:52:06](https://github.com/leanprover-community/mathlib/commit/b05d845)
feat(data/nat/basic): add a few lemmas ([#14718](https://github.com/leanprover-community/mathlib/pull/14718))
Add a few lemmas about sub and mod.
#### Estimated changes
modified src/algebra/order/sub.lean
- \+ *lemma* tsub_lt_of_lt

modified src/data/nat/basic.lean
- \+ *lemma* mul_add_mod
- \+ *lemma* mul_add_mod_of_lt
- \+ *lemma* pred_eq_self_iff



## [2022-06-16 11:52:28](https://github.com/leanprover-community/mathlib/commit/3feb151)
feat(algebra/homology,category_theory/abelian): exact_comp_mono_iff ([#14410](https://github.com/leanprover-community/mathlib/pull/14410))
From LTE.
#### Estimated changes
modified src/algebra/homology/exact.lean
- \+ *lemma* exact_comp_mono_iff

modified src/category_theory/abelian/exact.lean
- \+ *lemma* exact_epi_comp_iff



## [2022-06-16 02:53:25](https://github.com/leanprover-community/mathlib/commit/6834a24)
feat(analysis/asymptotics): define `is_Theta` ([#14567](https://github.com/leanprover-community/mathlib/pull/14567))
* define `f =Θ[l] g` and prove basic properties;
* add `is_O.const_smul_left`, `is_o.const_smul_left`;
* rename `is_O_const_smul_left_iff` and `is_o_const_smul_left_iff` to
  `is_O_const_smul_left` and `is_o_const_smul_left`.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* is_O.const_smul_left
- \+ *lemma* is_o.const_smul_left
- \+ *theorem* is_O_const_smul_left
- \+/\- *theorem* is_o_const_smul_left
- \- *theorem* is_O_const_smul_left_iff
- \+/\- *theorem* is_o_const_smul_left
- \- *theorem* is_o_const_smul_left_iff

created src/analysis/asymptotics/theta.lean
- \+ *lemma* is_O.antisymm
- \+ *lemma* is_Theta_refl
- \+ *lemma* is_Theta.symm
- \+ *lemma* is_Theta_comm
- \+ *lemma* is_Theta.trans
- \+ *lemma* is_O.trans_is_Theta
- \+ *lemma* is_Theta.trans_is_O
- \+ *lemma* is_o.trans_is_Theta
- \+ *lemma* is_Theta.trans_is_o
- \+ *lemma* is_Theta.is_o_congr_left
- \+ *lemma* is_Theta.is_o_congr_right
- \+ *lemma* is_Theta.is_O_congr_left
- \+ *lemma* is_Theta.is_O_congr_right
- \+ *lemma* is_Theta.mono
- \+ *lemma* is_Theta.sup
- \+ *lemma* is_Theta_sup
- \+ *lemma* is_Theta.eq_zero_iff
- \+ *lemma* is_Theta.tendsto_zero_iff
- \+ *lemma* is_Theta.tendsto_norm_at_top_iff
- \+ *lemma* is_Theta.is_bounded_under_le_iff
- \+ *lemma* is_Theta.smul
- \+ *lemma* is_Theta.mul
- \+ *lemma* is_Theta.inv
- \+ *lemma* is_Theta_inv
- \+ *lemma* is_Theta.pow
- \+ *lemma* is_Theta.zpow
- \+ *lemma* is_Theta_const_const
- \+ *lemma* is_Theta_const_const_iff
- \+ *lemma* is_Theta_zero_left
- \+ *lemma* is_Theta_zero_right
- \+ *lemma* is_Theta_const_smul_left
- \+ *lemma* is_Theta_const_smul_right
- \+ *lemma* is_Theta_const_mul_left
- \+ *lemma* is_Theta_const_mul_right
- \+ *def* is_Theta



## [2022-06-16 02:00:04](https://github.com/leanprover-community/mathlib/commit/0053e3c)
feat(analysis/special_functions/arsinh): add lemmas, review API ([#14668](https://github.com/leanprover-community/mathlib/pull/14668))
#### Estimated changes
modified src/analysis/calculus/cont_diff.lean
- \+ *theorem* homeomorph.cont_diff_symm
- \+ *theorem* homeomorph.cont_diff_symm_deriv

modified src/analysis/special_functions/arsinh.lean
- \+ *lemma* exp_arsinh
- \+ *lemma* arsinh_zero
- \+ *lemma* arsinh_neg
- \+/\- *lemma* sinh_arsinh
- \+ *lemma* cosh_arsinh
- \+/\- *lemma* sinh_surjective
- \+/\- *lemma* sinh_bijective
- \+/\- *lemma* arsinh_sinh
- \+ *lemma* arsinh_bijective
- \+ *lemma* arsinh_injective
- \+ *lemma* arsinh_surjective
- \+ *lemma* arsinh_strict_mono
- \+ *lemma* arsinh_inj
- \+ *lemma* arsinh_le_arsinh
- \+ *lemma* arsinh_lt_arsinh
- \+ *lemma* arsinh_eq_zero_iff
- \+ *lemma* arsinh_nonneg_iff
- \+ *lemma* arsinh_nonpos_iff
- \+ *lemma* arsinh_pos_iff
- \+ *lemma* arsinh_neg_iff
- \+ *lemma* has_strict_deriv_at_arsinh
- \+ *lemma* has_deriv_at_arsinh
- \+ *lemma* differentiable_arsinh
- \+ *lemma* cont_diff_arsinh
- \+ *lemma* continuous_arsinh
- \+ *lemma* filter.tendsto.arsinh
- \+ *lemma* continuous_at.arsinh
- \+ *lemma* continuous_within_at.arsinh
- \+ *lemma* continuous_on.arsinh
- \+ *lemma* continuous.arsinh
- \+ *lemma* has_strict_fderiv_at.arsinh
- \+ *lemma* has_fderiv_at.arsinh
- \+ *lemma* has_fderiv_within_at.arsinh
- \+ *lemma* differentiable_at.arsinh
- \+ *lemma* differentiable_within_at.arsinh
- \+ *lemma* differentiable_on.arsinh
- \+ *lemma* differentiable.arsinh
- \+ *lemma* cont_diff_at.arsinh
- \+ *lemma* cont_diff_within_at.arsinh
- \+ *lemma* cont_diff.arsinh
- \+ *lemma* cont_diff_on.arsinh
- \+ *lemma* has_strict_deriv_at.arsinh
- \+ *lemma* has_deriv_at.arsinh
- \+ *lemma* has_deriv_within_at.arsinh
- \+/\- *lemma* sinh_arsinh
- \+/\- *lemma* sinh_surjective
- \+/\- *lemma* sinh_bijective
- \- *lemma* sqrt_one_add_sinh_sq
- \+/\- *lemma* arsinh_sinh
- \+ *def* sinh_equiv
- \+ *def* sinh_order_iso
- \+ *def* sinh_homeomorph



## [2022-06-16 02:00:03](https://github.com/leanprover-community/mathlib/commit/22f3255)
refactor(set_theory/game/*): Delete `winner.lean` ([#14271](https://github.com/leanprover-community/mathlib/pull/14271))
The file `winner.lean` currently consists of one-line definitions and theorems, including aliases for basic inequalities. This PR removes the file, inlines all previous definitions and theorems, and golfs various proofs in the process.
#### Estimated changes
modified src/set_theory/game/impartial.lean
- \+ *lemma* mk_neg_equiv_self
- \+/\- *lemma* nonpos
- \+/\- *lemma* nonneg
- \+ *lemma* equiv_or_fuzzy_zero
- \+ *lemma* not_equiv_zero_iff
- \+ *lemma* not_fuzzy_zero_iff
- \+/\- *lemma* add_self
- \+ *lemma* mk_add_self
- \+ *lemma* equiv_iff_add_equiv_zero
- \+ *lemma* equiv_iff_add_equiv_zero'
- \+ *lemma* equiv_zero_iff_le:
- \+ *lemma* fuzzy_zero_iff_lf
- \+ *lemma* equiv_zero_iff_ge
- \+ *lemma* fuzzy_zero_iff_gf
- \+ *lemma* forall_left_moves_fuzzy_iff_equiv_zero
- \+ *lemma* forall_right_moves_fuzzy_iff_equiv_zero
- \+ *lemma* exists_left_move_equiv_iff_fuzzy_zero
- \+ *lemma* exists_right_move_equiv_iff_fuzzy_zero
- \+/\- *lemma* nonpos
- \+/\- *lemma* nonneg
- \- *lemma* winner_cases
- \- *lemma* not_first_wins
- \- *lemma* not_first_loses
- \+/\- *lemma* add_self
- \- *lemma* equiv_iff_sum_first_loses
- \- *lemma* first_loses_symm
- \- *lemma* first_wins_symm
- \- *lemma* first_loses_symm'
- \- *lemma* first_wins_symm'
- \- *lemma* no_good_left_moves_iff_first_loses
- \- *lemma* no_good_right_moves_iff_first_loses
- \- *lemma* good_left_move_iff_first_wins
- \- *lemma* good_right_move_iff_first_wins

modified src/set_theory/game/nim.lean
- \+/\- *lemma* non_zero_first_wins
- \+ *lemma* add_equiv_zero_iff_eq
- \+ *lemma* add_fuzzy_zero_iff_ne
- \- *lemma* zero_first_loses
- \+/\- *lemma* non_zero_first_wins
- \- *lemma* sum_first_loses_iff_eq
- \- *lemma* sum_first_wins_iff_neq

deleted src/set_theory/game/winner.lean
- \- *lemma* winner_cases
- \- *lemma* first_loses_is_zero
- \- *lemma* first_loses_of_equiv
- \- *lemma* first_wins_of_equiv
- \- *lemma* left_wins_of_equiv
- \- *lemma* right_wins_of_equiv
- \- *lemma* first_loses_of_equiv_iff
- \- *lemma* first_wins_of_equiv_iff
- \- *lemma* left_wins_of_equiv_iff
- \- *lemma* right_wins_of_equiv_iff
- \- *lemma* not_first_wins_of_first_loses
- \- *lemma* not_first_loses_of_first_wins
- \- *theorem* zero_first_loses
- \- *theorem* one_left_wins
- \- *theorem* star_first_wins
- \- *def* first_loses
- \- *def* first_wins
- \- *def* left_wins
- \- *def* right_wins



## [2022-06-15 23:36:05](https://github.com/leanprover-community/mathlib/commit/f991b4d)
chore(*): Bump to Lean 3.43.0 ([#14684](https://github.com/leanprover-community/mathlib/pull/14684))
Most of the changes in this upgrade are a consequence of https://github.com/leanprover-community/lean/pull/675, which removed almost all of `init/data/set.lean` from lean core so it could be migrated to mathlib. Other relevant core changes are https://github.com/leanprover-community/lean/pull/714, which removed a few order decidability instances, and https://github.com/leanprover-community/lean/pull/711, which caused a docstring to be rejected.
#### Estimated changes
modified leanpkg.toml

modified src/algebra/lie/free.lean

modified src/algebra/lie/ideal_operations.lean

modified src/analysis/inner_product_space/projection.lean

modified src/analysis/normed/group/quotient.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/combinatorics/set_family/compression/uv.lean

modified src/data/bool/basic.lean

modified src/data/set/basic.lean
- \+/\- *lemma* lt_eq_ssubset
- \- *lemma* compl_eq_compl
- \+/\- *lemma* lt_eq_ssubset
- \+/\- *theorem* mem_powerset
- \+/\- *theorem* subset_of_mem_powerset
- \+/\- *theorem* mem_powerset_iff
- \- *theorem* mem_set_of_eq
- \+/\- *theorem* mem_powerset
- \+/\- *theorem* subset_of_mem_powerset
- \+/\- *theorem* mem_powerset_iff
- \+ *def* powerset
- \+ *def* image

modified src/data/set/functor.lean

modified src/data/set/lattice.lean
- \+/\- *theorem* mem_sUnion
- \+/\- *theorem* mem_sUnion
- \+ *def* sUnion

modified src/field_theory/adjoin.lean

modified src/field_theory/primitive_element.lean

modified src/group_theory/nielsen_schreier.lean
- \+/\- *def* End_is_free
- \+/\- *def* End_is_free

modified src/group_theory/order_of_element.lean

modified src/logic/equiv/set.lean

modified src/measure_theory/constructions/borel_space.lean
- \+/\- *def* measurable_equiv.ereal_equiv_real
- \+/\- *def* measurable_equiv.ereal_equiv_real

modified src/measure_theory/covering/vitali.lean

modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/function/strongly_measurable.lean

modified src/measure_theory/measure/ae_measurable.lean

modified src/model_theory/semantics.lean
- \+ *lemma* mem_complete_theory

modified src/model_theory/syntax.lean

modified src/order/filter/basic.lean
- \+ *lemma* has_subset.subset.eventually_le
- \- *lemma* set.subset.eventually_le

modified src/order/succ_pred/basic.lean

modified src/ring_theory/local_properties.lean

modified src/set_theory/zfc.lean

modified src/tactic/core.lean

modified src/tactic/localized.lean

modified src/topology/basic.lean

modified src/topology/omega_complete_partial_order.lean
- \+/\- *theorem* is_open_univ
- \+/\- *theorem* is_open_univ

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/compact_convergence.lean

modified test/back_chaining.lean

modified test/rcases.lean



## [2022-06-15 21:34:32](https://github.com/leanprover-community/mathlib/commit/c81c6c9)
feat(data/polynomial/erase_lead): `lt_nat_degree_of_mem_erase_lead_support` ([#14745](https://github.com/leanprover-community/mathlib/pull/14745))
This PR adds a lemma `lt_nat_degree_of_mem_erase_lead_support` and adds term-mode proofs of a couple related lemmas.
#### Estimated changes
modified src/data/polynomial/erase_lead.lean
- \+ *lemma* lt_nat_degree_of_mem_erase_lead_support
- \+/\- *lemma* nat_degree_not_mem_erase_lead_support
- \+/\- *lemma* nat_degree_not_mem_erase_lead_support



## [2022-06-15 21:34:31](https://github.com/leanprover-community/mathlib/commit/ea2dbcb)
feat(analysis/special_functions/integrals): Add integral_cpow ([#14491](https://github.com/leanprover-community/mathlib/pull/14491))
Also adds various helper lemmas.
The purpose of this commit is to provide a computed integral for the `cpow` function. The proof is functionally identical to that of `integral_rpow`, but places a different set of constraints on the various parameters due to different continuity constraints of the cpow function.
Some notes on future improvments:
  * The range of valid integration can be expanded using ae_covers a la [#14147](https://github.com/leanprover-community/mathlib/pull/14147)
  * We currently only contemplate a real argument. However, this should essentially work for any continuous path in the complex plane that avoids the negative real axis. That would require a lot more machinery, not currently in mathlib.
Despite these restrictions, why is this important? This, Abel summation, [#13500](https://github.com/leanprover-community/mathlib/pull/13500), and [#14090](https://github.com/leanprover-community/mathlib/pull/14090) are the key ingredients to bootstrapping Dirichlet series.
#### Estimated changes
modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_strict_deriv_at.smul_const

modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integrable_cpow
- \+ *lemma* integral_cpow

modified src/analysis/special_functions/pow.lean
- \+ *lemma* continuous_on.cpow_const



## [2022-06-15 21:34:27](https://github.com/leanprover-community/mathlib/commit/7145043)
feat(algebra/group/pi): Technical casework lemma for when two binomials are equal to each other ([#14400](https://github.com/leanprover-community/mathlib/pull/14400))
This PR adds a technical casework lemma for when two binomials are equal to each other. It will be useful for irreducibility of x^n-x-1. If anyone can see how to golf the proof further, that would be appreciated!
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single

modified src/data/finsupp/basic.lean
- \+ *lemma* single_add_single_eq_single_add_single

modified src/data/polynomial/basic.lean
- \+/\- *lemma* monomial_left_inj
- \+ *lemma* binomial_eq_binomial
- \+/\- *lemma* nat_cast_mul
- \+/\- *lemma* monomial_left_inj
- \+/\- *lemma* nat_cast_mul



## [2022-06-15 18:51:17](https://github.com/leanprover-community/mathlib/commit/665cec2)
chore(data/nat/factorization/basic): delete two duplicate lemmas ([#14754](https://github.com/leanprover-community/mathlib/pull/14754))
Deleting two lemmas introduced in [#14461](https://github.com/leanprover-community/mathlib/pull/14461) that are duplicates of lemmas already present, as follows:
```
lemma div_factorization_pos {q r : ℕ} (hr : nat.prime r) (hq : q ≠ 0) :
  q / (r ^ (q.factorization r)) ≠ 0 := div_pow_factorization_ne_zero r hq
```
```
lemma ne_dvd_factorization_div {q r : ℕ} (hr : nat.prime r) (hq : q ≠ 0) :
  ¬(r ∣ (q / (r ^ (q.factorization r)))) := not_dvd_div_pow_factorization hr hq
```
#### Estimated changes
modified src/data/nat/factorization/basic.lean
- \- *lemma* div_factorization_pos
- \- *lemma* ne_dvd_factorization_div



## [2022-06-15 18:51:16](https://github.com/leanprover-community/mathlib/commit/a583244)
feat(representation_theory/Action): a few lemmas about the rigid structure of Action ([#14620](https://github.com/leanprover-community/mathlib/pull/14620))
#### Estimated changes
modified src/representation_theory/Action.lean
- \+ *lemma* right_dual_V
- \+ *lemma* left_dual_V
- \+ *lemma* right_dual_ρ
- \+ *lemma* left_dual_ρ



## [2022-06-15 18:51:15](https://github.com/leanprover-community/mathlib/commit/c4ef20e)
feat(order/rel_classes): an irreflexive order on a subsingleton type is a well order ([#14601](https://github.com/leanprover-community/mathlib/pull/14601))
This generalizes a previously existing lemma that the empty relation on a subsingleton type is a well order.
#### Estimated changes
modified src/order/rel_classes.lean
- \+ *lemma* not_rel
- \+ *lemma* empty_relation_apply
- \+ *lemma* eq_empty_relation
- \+ *theorem* subsingleton.is_well_order



## [2022-06-15 17:10:38](https://github.com/leanprover-community/mathlib/commit/94fa33b)
fix(tactic/congrm): support multiple binders ([#14753](https://github.com/leanprover-community/mathlib/pull/14753))
#### Estimated changes
modified src/tactic/congrm.lean

modified test/congrm.lean



## [2022-06-15 17:10:37](https://github.com/leanprover-community/mathlib/commit/430da94)
chore(analysis/normed): move `normed.normed_field` to `normed.field.basic` ([#14747](https://github.com/leanprover-community/mathlib/pull/14747))
#### Estimated changes
modified src/analysis/locally_convex/polar.lean

modified src/analysis/locally_convex/weak_dual.lean

renamed src/analysis/normed/normed_field.lean to src/analysis/normed/field/basic.lean

modified src/analysis/normed_space/basic.lean



## [2022-06-15 17:10:36](https://github.com/leanprover-community/mathlib/commit/6a0f967)
feat(data/finite/set): `finite` instances for set constructions ([#14673](https://github.com/leanprover-community/mathlib/pull/14673))
#### Estimated changes
modified src/data/finite/basic.lean

created src/data/finite/default.lean

created src/data/finite/set.lean
- \+ *lemma* set.finite_iff_finite
- \+ *lemma* finite_bUnion
- \+ *lemma* set.finite_univ_iff
- \+ *lemma* finite.of_finite_univ
- \+ *lemma* finite.set.finite_of_finite_image
- \+ *theorem* set.finite_of_finite



## [2022-06-15 17:10:35](https://github.com/leanprover-community/mathlib/commit/8eaeec2)
chore(a few random files): golfing using the new tactic `congrm` ([#14593](https://github.com/leanprover-community/mathlib/pull/14593))
This PR is simply intended to showcase some possible applications of the new tactic `congrm`, introduced in [#14153](https://github.com/leanprover-community/mathlib/pull/14153).
#### Estimated changes
modified archive/100-theorems-list/45_partition.lean

modified src/analysis/analytic/inverse.lean

modified src/analysis/calculus/cont_diff.lean

modified src/analysis/convex/gauge.lean



## [2022-06-15 14:55:51](https://github.com/leanprover-community/mathlib/commit/34ce784)
refactor(algebra/group_with_zero/basic): Golf using division monoid lemmas ([#14213](https://github.com/leanprover-community/mathlib/pull/14213))
Make all eligible `group_with_zero` lemmas one-liners from `division_monoid` ones and group them within the file.
#### Estimated changes
modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_right_inj'
- \+/\- *lemma* is_unit_iff_ne_zero
- \+/\- *lemma* div_self
- \+/\- *lemma* eq_mul_inv_iff_mul_eq₀
- \+/\- *lemma* eq_inv_mul_iff_mul_eq₀
- \+/\- *lemma* inv_mul_eq_iff_eq_mul₀
- \+/\- *lemma* mul_inv_eq_iff_eq_mul₀
- \+/\- *lemma* mul_inv_eq_one₀
- \+/\- *lemma* inv_mul_eq_one₀
- \+/\- *lemma* mul_eq_one_iff_eq_inv₀
- \+/\- *lemma* mul_eq_one_iff_inv_eq₀
- \+/\- *lemma* div_mul_cancel
- \+/\- *lemma* mul_div_cancel
- \+/\- *lemma* mul_one_div_cancel
- \+/\- *lemma* one_div_mul_cancel
- \+/\- *lemma* div_left_inj'
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff
- \+/\- *lemma* div_eq_iff_mul_eq
- \+/\- *lemma* eq_div_iff_mul_eq
- \+/\- *lemma* div_eq_of_eq_mul
- \+/\- *lemma* eq_div_of_mul_eq
- \+/\- *lemma* div_eq_one_iff_eq
- \+/\- *lemma* div_mul_left
- \+/\- *lemma* mul_div_mul_right
- \+/\- *lemma* mul_mul_div
- \+/\- *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_mul_div_cancel
- \+/\- *lemma* mul_self_mul_inv
- \+/\- *lemma* mul_inv_mul_self
- \+/\- *lemma* inv_mul_mul_self
- \+/\- *lemma* mul_self_div_self
- \+/\- *lemma* div_self_mul_self
- \+/\- *lemma* div_mul_right
- \+/\- *lemma* mul_div_cancel_left
- \+/\- *lemma* mul_div_cancel'
- \+/\- *lemma* mul_div_mul_left
- \+/\- *lemma* div_eq_div_iff
- \+/\- *lemma* div_div_cancel'
- \+/\- *lemma* div_helper
- \+/\- *lemma* mul_left_inj'
- \+/\- *lemma* mul_right_inj'
- \+/\- *lemma* mul_self_mul_inv
- \+/\- *lemma* mul_inv_mul_self
- \+/\- *lemma* inv_mul_mul_self
- \+/\- *lemma* mul_self_div_self
- \+/\- *lemma* div_self_mul_self
- \+/\- *lemma* eq_mul_inv_iff_mul_eq₀
- \+/\- *lemma* eq_inv_mul_iff_mul_eq₀
- \+/\- *lemma* inv_mul_eq_iff_eq_mul₀
- \+/\- *lemma* mul_inv_eq_iff_eq_mul₀
- \+/\- *lemma* mul_inv_eq_one₀
- \+/\- *lemma* inv_mul_eq_one₀
- \+/\- *lemma* mul_eq_one_iff_eq_inv₀
- \+/\- *lemma* mul_eq_one_iff_inv_eq₀
- \+/\- *lemma* is_unit_iff_ne_zero
- \+/\- *lemma* div_self
- \+/\- *lemma* div_mul_cancel
- \+/\- *lemma* mul_div_cancel
- \+/\- *lemma* mul_one_div_cancel
- \+/\- *lemma* one_div_mul_cancel
- \+/\- *lemma* div_left_inj'
- \+/\- *lemma* div_eq_iff_mul_eq
- \+/\- *lemma* eq_div_iff_mul_eq
- \+/\- *lemma* div_eq_of_eq_mul
- \+/\- *lemma* eq_div_of_mul_eq
- \+/\- *lemma* div_eq_one_iff_eq
- \+/\- *lemma* div_mul_left
- \+/\- *lemma* mul_div_mul_right
- \+/\- *lemma* mul_mul_div
- \+/\- *lemma* div_div_div_cancel_right
- \+/\- *lemma* div_mul_div_cancel
- \+/\- *lemma* eq_div_iff
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* div_mul_right
- \+/\- *lemma* mul_div_cancel_left
- \+/\- *lemma* mul_div_cancel'
- \+/\- *lemma* mul_div_mul_left
- \+/\- *lemma* div_helper
- \+/\- *lemma* div_eq_div_iff
- \+/\- *lemma* div_div_cancel'

modified src/data/real/pi/leibniz.lean



## [2022-06-15 14:55:50](https://github.com/leanprover-community/mathlib/commit/bbca289)
feat(dynamics/periodic_pts): `chain.pairwise` on orbit ([#12991](https://github.com/leanprover-community/mathlib/pull/12991))
We prove that a relation holds pairwise on an orbit iff it does for `f^[n] x` and `f^[n+1] x` for any `n`.
#### Estimated changes
modified src/data/list/cycle.lean
- \+ *theorem* chain_range_succ

modified src/dynamics/periodic_pts.lean
- \+ *theorem* periodic_orbit_chain
- \+ *theorem* periodic_orbit_chain'



## [2022-06-15 13:13:12](https://github.com/leanprover-community/mathlib/commit/4661473)
chore(analysis/normed/normed_field): golf 2 proofs ([#14746](https://github.com/leanprover-community/mathlib/pull/14746))
#### Estimated changes
modified src/analysis/normed/normed_field.lean
- \+/\- *lemma* exists_norm_lt_one
- \+/\- *lemma* exists_norm_lt_one



## [2022-06-15 13:13:11](https://github.com/leanprover-community/mathlib/commit/dccdef6)
chore(set_theory/ordinal/basic): golf ordinal addition definition ([#14744](https://github.com/leanprover-community/mathlib/pull/14744))
#### Estimated changes
modified src/set_theory/ordinal/basic.lean



## [2022-06-15 13:13:10](https://github.com/leanprover-community/mathlib/commit/d2bfb32)
feat(analysis/normed_space): range of `norm` ([#14740](https://github.com/leanprover-community/mathlib/pull/14740))
* Add `exists_norm_eq`, `range_norm`, `range_nnnorm`, and `nnnorm_surjective`.
* Open `set` namespace.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* exists_norm_eq
- \+ *lemma* range_norm
- \+ *lemma* nnnorm_surjective
- \+ *lemma* range_nnnorm



## [2022-06-15 13:13:09](https://github.com/leanprover-community/mathlib/commit/2aa3fd9)
feat(analysis/convex): a convex set is contractible ([#14732](https://github.com/leanprover-community/mathlib/pull/14732))
#### Estimated changes
created src/analysis/convex/contractible.lean



## [2022-06-15 13:13:08](https://github.com/leanprover-community/mathlib/commit/7430d2d)
feat(data/complex/exponential): more `simp` lemmas ([#14731](https://github.com/leanprover-community/mathlib/pull/14731))
Add `simp` attrs and `simp` lemmas.
#### Estimated changes
modified src/data/complex/exponential.lean
- \+/\- *lemma* of_real_cosh_of_real_re
- \+/\- *lemma* cosh_of_real_re
- \+/\- *lemma* cosh_add_sinh
- \+/\- *lemma* sinh_add_cosh
- \+ *lemma* exp_sub_cosh
- \+ *lemma* exp_sub_sinh
- \+/\- *lemma* cosh_sub_sinh
- \+ *lemma* sinh_sub_cosh
- \+/\- *lemma* cosh_sq_sub_sinh_sq
- \+/\- *lemma* cosh_neg
- \+/\- *lemma* cosh_add_sinh
- \+/\- *lemma* sinh_add_cosh
- \+ *lemma* exp_sub_cosh
- \+ *lemma* exp_sub_sinh
- \+/\- *lemma* cosh_sub_sinh
- \+ *lemma* sinh_sub_cosh
- \+/\- *lemma* cosh_sq_sub_sinh_sq
- \+ *lemma* cosh_sq'
- \+ *lemma* sinh_lt_cosh
- \+/\- *lemma* of_real_cosh_of_real_re
- \+/\- *lemma* cosh_of_real_re
- \+/\- *lemma* cosh_add_sinh
- \+/\- *lemma* sinh_add_cosh
- \+/\- *lemma* cosh_sub_sinh
- \+/\- *lemma* cosh_sq_sub_sinh_sq
- \+/\- *lemma* cosh_neg
- \+/\- *lemma* cosh_add_sinh
- \+/\- *lemma* sinh_add_cosh
- \+/\- *lemma* cosh_sq_sub_sinh_sq



## [2022-06-15 13:13:07](https://github.com/leanprover-community/mathlib/commit/fee91d7)
feat(data/fin/vec_notation): add has_reflect instance and tests ([#14670](https://github.com/leanprover-community/mathlib/pull/14670))
#### Estimated changes
modified src/data/fin/vec_notation.lean

created test/vec_notation.lean



## [2022-06-15 13:13:06](https://github.com/leanprover-community/mathlib/commit/764d7a9)
feat(probability/stopping): first hitting time ([#14630](https://github.com/leanprover-community/mathlib/pull/14630))
This PR adds the first hitting time (before some time) and proves that it is a stopping time in the discrete case.
#### Estimated changes
created src/probability/hitting_time.lean
- \+ *lemma* hitting_of_lt
- \+ *lemma* hitting_le
- \+ *lemma* le_hitting
- \+ *lemma* le_hitting_of_exists
- \+ *lemma* hitting_mem_Icc
- \+ *lemma* hitting_mem_set
- \+ *lemma* hitting_le_of_mem
- \+ *lemma* hitting_le_iff_of_exists
- \+ *lemma* hitting_le_iff_of_lt
- \+ *lemma* hitting_lt_iff
- \+ *lemma* hitting_is_stopping_time
- \+ *lemma* hitting_eq_Inf
- \+ *lemma* hitting_bot_le_iff



## [2022-06-15 13:13:04](https://github.com/leanprover-community/mathlib/commit/947c3c6)
refactor(order/locally_finite): Allow `finset.Iix`/`finset.Ixi` on empty types ([#14430](https://github.com/leanprover-community/mathlib/pull/14430))
Define `locally_finite_order_top` and `locally_finite_order_bot` are redefine `Ici`, `Ioi`, `iic`, `Iio` using them. Those new typeclasses are the same as `locally_finite_order` + `order_top`/`order_bot`, except that they allow the empty type, which is a surprisingly useful feature.
#### Estimated changes
modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+/\- *lemma* gram_schmidt_zero
- \+/\- *lemma* gram_schmidt_zero

modified src/combinatorics/set_family/lym.lean

modified src/data/fin/interval.lean
- \+/\- *lemma* map_subtype_embedding_Icc
- \+/\- *lemma* map_subtype_embedding_Ico
- \+/\- *lemma* map_subtype_embedding_Ioc
- \+/\- *lemma* map_subtype_embedding_Ioo
- \+/\- *lemma* Ici_eq_finset_subtype
- \+/\- *lemma* Ioi_eq_finset_subtype
- \+/\- *lemma* Iic_eq_finset_subtype
- \+/\- *lemma* Iio_eq_finset_subtype
- \+/\- *lemma* map_subtype_embedding_Ici
- \+/\- *lemma* map_subtype_embedding_Ioi
- \+/\- *lemma* map_subtype_embedding_Iic
- \+/\- *lemma* map_subtype_embedding_Iio
- \+/\- *lemma* card_Ici
- \+/\- *lemma* card_Ioi
- \+/\- *lemma* card_fintype_Ici
- \+/\- *lemma* card_fintype_Ioi
- \+/\- *lemma* card_filter_le
- \+/\- *lemma* card_filter_gt
- \+/\- *lemma* card_filter_ge
- \+/\- *lemma* card_filter_lt_lt
- \+/\- *lemma* map_subtype_embedding_Icc
- \+/\- *lemma* map_subtype_embedding_Ico
- \+/\- *lemma* map_subtype_embedding_Ioc
- \+/\- *lemma* map_subtype_embedding_Ioo
- \+/\- *lemma* Ici_eq_finset_subtype
- \+/\- *lemma* Ioi_eq_finset_subtype
- \+/\- *lemma* Iic_eq_finset_subtype
- \+/\- *lemma* Iio_eq_finset_subtype
- \+/\- *lemma* map_subtype_embedding_Ici
- \+/\- *lemma* map_subtype_embedding_Ioi
- \+/\- *lemma* map_subtype_embedding_Iic
- \+/\- *lemma* map_subtype_embedding_Iio
- \+/\- *lemma* card_Ici
- \+/\- *lemma* card_Ioi
- \+/\- *lemma* card_fintype_Ici
- \+/\- *lemma* card_fintype_Ioi
- \+/\- *lemma* card_filter_le
- \+/\- *lemma* card_filter_gt
- \+/\- *lemma* card_filter_ge
- \+/\- *lemma* card_filter_lt_lt

modified src/data/finset/locally_finite.lean
- \+/\- *lemma* Icc_subset_Ici_self
- \+/\- *lemma* Ico_subset_Ici_self
- \+/\- *lemma* Ioc_subset_Ioi_self
- \+/\- *lemma* Ioo_subset_Ioi_self
- \+/\- *lemma* Ioc_subset_Ici_self
- \+/\- *lemma* Ioo_subset_Ici_self
- \+/\- *lemma* Icc_subset_Iic_self
- \+/\- *lemma* Ioc_subset_Iic_self
- \+/\- *lemma* Ico_subset_Iio_self
- \+/\- *lemma* Ioo_subset_Iio_self
- \+/\- *lemma* Ico_subset_Iic_self
- \+/\- *lemma* Ioo_subset_Iic_self
- \+/\- *lemma* Ioi_subset_Ici_self
- \+/\- *lemma* filter_lt_eq_Ioi
- \+/\- *lemma* filter_le_eq_Ici
- \+/\- *lemma* Iio_subset_Iic_self
- \+/\- *lemma* filter_gt_eq_Iio
- \+/\- *lemma* filter_ge_eq_Iic
- \+/\- *lemma* filter_lt_eq_Ioi
- \+/\- *lemma* filter_le_eq_Ici
- \+/\- *lemma* filter_gt_eq_Iio
- \+/\- *lemma* filter_ge_eq_Iic
- \+/\- *lemma* Icc_subset_Ici_self
- \+/\- *lemma* Ico_subset_Ici_self
- \+/\- *lemma* Ioc_subset_Ici_self
- \+/\- *lemma* Ioo_subset_Ici_self
- \+/\- *lemma* Ioi_subset_Ici_self
- \+/\- *lemma* Ioc_subset_Ioi_self
- \+/\- *lemma* Ioo_subset_Ioi_self
- \+/\- *lemma* Icc_subset_Iic_self
- \+/\- *lemma* Ico_subset_Iic_self
- \+/\- *lemma* Ioc_subset_Iic_self
- \+/\- *lemma* Ioo_subset_Iic_self
- \+/\- *lemma* Iio_subset_Iic_self
- \+/\- *lemma* Ico_subset_Iio_self
- \+/\- *lemma* Ioo_subset_Iio_self

modified src/data/nat/interval.lean
- \+/\- *lemma* card_Iic
- \+/\- *lemma* card_Iio
- \+/\- *lemma* card_Iic
- \+/\- *lemma* card_Iio

modified src/order/locally_finite.lean
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* coe_Ici
- \+/\- *lemma* coe_Ioi
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* coe_Iic
- \+/\- *lemma* coe_Iio
- \+/\- *lemma* Ici_eq_Icc
- \+/\- *lemma* Ioi_eq_Ioc
- \+/\- *lemma* Iic_eq_Icc
- \+/\- *lemma* Iio_eq_Ico
- \+ *lemma* Icc_of_dual
- \+ *lemma* Ico_of_dual
- \+ *lemma* Ioc_of_dual
- \+ *lemma* Ioo_of_dual
- \+ *lemma* this
- \+ *lemma* Iic_to_dual
- \+ *lemma* Iio_to_dual
- \+ *lemma* Ici_of_dual
- \+ *lemma* Ioi_of_dual
- \+ *lemma* this
- \+ *lemma* Ici_to_dual
- \+ *lemma* Ioi_to_dual
- \+ *lemma* Iic_of_dual
- \+ *lemma* Iio_of_dual
- \+/\- *lemma* map_subtype_embedding_Icc
- \+/\- *lemma* map_subtype_embedding_Ico
- \+/\- *lemma* map_subtype_embedding_Ioc
- \+/\- *lemma* map_subtype_embedding_Ioo
- \+ *lemma* subtype_Ici_eq
- \+ *lemma* subtype_Ioi_eq
- \+ *lemma* map_subtype_embedding_Ici
- \+ *lemma* map_subtype_embedding_Ioi
- \+ *lemma* subtype_Iic_eq
- \+ *lemma* subtype_Iio_eq
- \+ *lemma* map_subtype_embedding_Iic
- \+ *lemma* map_subtype_embedding_Iio
- \+/\- *lemma* Ici_eq_Icc
- \+/\- *lemma* Ioi_eq_Ioc
- \+/\- *lemma* coe_Ici
- \+/\- *lemma* coe_Ioi
- \+/\- *lemma* mem_Ici
- \+/\- *lemma* mem_Ioi
- \+/\- *lemma* Iic_eq_Icc
- \+/\- *lemma* Iio_eq_Ico
- \+/\- *lemma* coe_Iic
- \+/\- *lemma* coe_Iio
- \+/\- *lemma* mem_Iic
- \+/\- *lemma* mem_Iio
- \+/\- *lemma* map_subtype_embedding_Icc
- \+/\- *lemma* map_subtype_embedding_Ico
- \+/\- *lemma* map_subtype_embedding_Ioc
- \+/\- *lemma* map_subtype_embedding_Ioo
- \+ *def* locally_finite_order_top.of_Ici'
- \+ *def* locally_finite_order_top.of_Ici
- \+ *def* locally_finite_order_bot.of_Iic'
- \+ *def* locally_finite_order_top.of_Iic
- \+/\- *def* Ici
- \+/\- *def* Ioi
- \+/\- *def* Iic
- \+/\- *def* Iio
- \+/\- *def* Ici
- \+/\- *def* Ioi
- \+/\- *def* Iic
- \+/\- *def* Iio



## [2022-06-15 11:13:37](https://github.com/leanprover-community/mathlib/commit/114f543)
feat(model_theory/semantics, elementary_maps): Defines elementary equivalence ([#14723](https://github.com/leanprover-community/mathlib/pull/14723))
Defines elementary equivalence of structures
Shows that the domain and codomain of an elementary map are elementarily equivalent.
#### Estimated changes
modified src/model_theory/elementary_maps.lean
- \+ *lemma* elementarily_equivalent
- \+ *lemma* elementarily_equivalent

modified src/model_theory/semantics.lean
- \+ *lemma* elementarily_equivalent_iff
- \+ *def* elementarily_equivalent



## [2022-06-15 11:13:36](https://github.com/leanprover-community/mathlib/commit/9c40f30)
refactor(set_theory/game/*): fix theorem names ([#14685](https://github.com/leanprover-community/mathlib/pull/14685))
Some theorems about `exists` had `forall` in the name, other theorems about swapped `≤` or `⧏` used `le` and `lf` instead of `ge` and `gf`.
We also golf `le_of_forall_lt`.
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/impartial.lean

modified src/set_theory/game/nim.lean

modified src/set_theory/game/pgame.lean
- \+ *theorem* lf_iff_exists_le
- \+ *theorem* lf_of_exists_le
- \+ *theorem* _root_.has_le.le.not_gf
- \+ *theorem* lf.not_ge
- \+/\- *theorem* lf_irrefl
- \+ *theorem* le_of_forall_lt
- \+/\- *theorem* lf.not_equiv
- \+/\- *theorem* lf.not_equiv'
- \+ *theorem* lf.not_gt
- \- *theorem* lf_iff_forall_le
- \- *theorem* lf_of_forall_le
- \- *theorem* _root_.has_le.le.not_lf
- \- *theorem* lf.not_le
- \+/\- *theorem* lf_irrefl
- \+/\- *theorem* lf.not_equiv
- \+/\- *theorem* lf.not_equiv'
- \- *theorem* lf.not_lt

modified src/set_theory/surreal/basic.lean
- \+ *theorem* lt_iff_exists_le
- \+ *theorem* lt_of_exists_le
- \- *theorem* le_of_forall_lt
- \- *theorem* lt_iff_forall_le
- \- *theorem* lt_of_forall_le

modified src/set_theory/surreal/dyadic.lean



## [2022-06-15 11:13:35](https://github.com/leanprover-community/mathlib/commit/c667723)
feat(model_theory/syntax, semantics): Mapping formulas given maps on terms and relations ([#14466](https://github.com/leanprover-community/mathlib/pull/14466))
Defines `first_order.language.bounded_formula.map_term_rel`, which maps formulas given maps on terms and maps on relations.
#### Estimated changes
modified src/data/fin/basic.lean
- \+ *lemma* cast_le_cast_le
- \+ *lemma* cast_le_comp_cast_le
- \+ *lemma* nat_add_last
- \+ *lemma* nat_add_cast_succ

modified src/data/fin/tuple/basic.lean
- \+ *lemma* snoc_comp_nat_add
- \+ *lemma* snoc_cast_add
- \+ *lemma* snoc_comp_cast_add

modified src/model_theory/semantics.lean
- \+ *lemma* realize_map_term_rel_id
- \+ *lemma* realize_map_term_rel_add_cast_le
- \- *lemma* realize_subst_aux

modified src/model_theory/syntax.lean
- \+/\- *lemma* relabel_id
- \+ *lemma* relabel_id_eq_id
- \+ *lemma* relabel_comp_relabel
- \+ *lemma* cast_le_rfl
- \+ *lemma* cast_le_cast_le
- \+ *lemma* cast_le_comp_cast_le
- \+ *lemma* map_term_rel_map_term_rel
- \+ *lemma* map_term_rel_id_id_id
- \+ *lemma* relabel_falsum
- \+ *lemma* relabel_bot
- \+ *lemma* relabel_imp
- \+ *lemma* relabel_not
- \+ *lemma* relabel_all
- \+ *lemma* relabel_ex
- \+/\- *lemma* relabel_id
- \+/\- *def* restrict_free_var
- \+/\- *def* alls
- \+/\- *def* exs
- \+ *def* map_term_rel
- \+/\- *def* lift_at
- \+ *def* map_term_rel_equiv
- \+/\- *def* relabel
- \+/\- *def* subst
- \+/\- *def* relabel
- \+/\- *def* restrict_free_var
- \+/\- *def* alls
- \+/\- *def* exs
- \+/\- *def* lift_at
- \+/\- *def* subst



## [2022-06-15 11:13:33](https://github.com/leanprover-community/mathlib/commit/ea97606)
feat(tactic/ring): recursive ring_nf ([#14429](https://github.com/leanprover-community/mathlib/pull/14429))
As [reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60ring_nf.60.20not.20consistently.20normalizing.3F). This allows `ring_nf` to rewrite inside the atoms of a ring expression, meaning that things like `f (a + b) + c` can simplify in both `+` expressions.
#### Estimated changes
modified src/algebra/continued_fractions/computation/approximations.lean

modified src/ring_theory/trace.lean

modified src/tactic/ring.lean

modified test/ring.lean



## [2022-06-15 10:32:10](https://github.com/leanprover-community/mathlib/commit/6e0e270)
feat(linear_algebra/matrix): positive definite ([#14531](https://github.com/leanprover-community/mathlib/pull/14531))
Define positive definite matrices and connect them to positive definiteness of quadratic forms.
#### Estimated changes
modified src/linear_algebra/matrix/hermitian.lean

created src/linear_algebra/matrix/pos_def.lean
- \+ *lemma* pos_def_of_to_quadratic_form'
- \+ *lemma* pos_def_to_quadratic_form'
- \+ *lemma* pos_def_of_to_matrix'
- \+ *lemma* pos_def_to_matrix'
- \+ *def* pos_def

modified src/linear_algebra/quadratic_form/basic.lean
- \+ *lemma* quadratic_form.is_symm_to_matrix'



## [2022-06-15 09:13:28](https://github.com/leanprover-community/mathlib/commit/784c703)
docs(topology/basic): Fix typo in library note ([#14743](https://github.com/leanprover-community/mathlib/pull/14743))
#### Estimated changes
modified src/topology/basic.lean



## [2022-06-15 08:32:58](https://github.com/leanprover-community/mathlib/commit/1fbe118)
golf(set_theory/game/pgame): golf `neg_le_neg_iff` ([#14726](https://github.com/leanprover-community/mathlib/pull/14726))
Also in this PR:
+ slightly golf `subsequent.trans`
+ replace `->` by `→`
+ replace a nonterminal `simp` by `dsimp`
#### Estimated changes
modified src/set_theory/game/pgame.lean
- \+/\- *lemma* left_moves_add_cases
- \+/\- *lemma* right_moves_add_cases
- \+/\- *lemma* left_moves_add_cases
- \+/\- *lemma* right_moves_add_cases
- \+/\- *theorem* subsequent.trans
- \+/\- *theorem* neg_le_neg_iff
- \+/\- *theorem* neg_lf_neg_iff
- \+/\- *theorem* subsequent.trans
- \+/\- *theorem* neg_le_neg_iff
- \+/\- *theorem* neg_lf_neg_iff



## [2022-06-15 08:32:57](https://github.com/leanprover-community/mathlib/commit/7958e7d)
chore(analysis/convex/extreme): Make arguments semi-implicit ([#14698](https://github.com/leanprover-community/mathlib/pull/14698))
Change the definition of `is_extreme` from
```
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ open_segment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
```
to
```
B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ open_segment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B
```
and similar for `extreme_points`.
#### Estimated changes
modified src/analysis/convex/extreme.lean



## [2022-06-15 07:00:25](https://github.com/leanprover-community/mathlib/commit/6b4f3f2)
feat(data/nat/prime): prime.even_iff ([#14688](https://github.com/leanprover-community/mathlib/pull/14688))
Adds a lemma saying that the only even prime is two.
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* prime.even_iff



## [2022-06-15 04:54:47](https://github.com/leanprover-community/mathlib/commit/e86ab0b)
refactor(src/algebra/order/monoid): make bot_eq_zero a simp lemma only when the order is linear ([#14553](https://github.com/leanprover-community/mathlib/pull/14553))
#### Estimated changes
modified src/algebra/lie/subalgebra.lean
- \- *def* canonically_ordered_add_monoid

modified src/algebra/module/submodule/pointwise.lean
- \- *def* canonically_ordered_add_monoid

modified src/algebra/order/monoid.lean
- \+/\- *lemma* bot_eq_one
- \+ *lemma* bot_eq_one'
- \+/\- *lemma* bot_eq_one

modified src/data/multiset/basic.lean
- \+ *theorem* bot_eq_zero



## [2022-06-15 04:54:45](https://github.com/leanprover-community/mathlib/commit/b4b816c)
feat(number_theory/cyclotomic/primitive_roots): generalize finrank lemma  ([#14550](https://github.com/leanprover-community/mathlib/pull/14550))
We generalize certain results from fields to domains.
#### Estimated changes
modified src/number_theory/cyclotomic/discriminant.lean

modified src/number_theory/cyclotomic/gal.lean

modified src/number_theory/cyclotomic/primitive_roots.lean



## [2022-06-15 03:13:18](https://github.com/leanprover-community/mathlib/commit/38ad656)
chore(field_theory/intermediate_field): fix timeout ([#14725](https://github.com/leanprover-community/mathlib/pull/14725))
+ Remove `@[simps]` from `intermediate_field_map` to reduce `decl post-processing of intermediate_field_map` from 18.3s to 46.4ms (on my machine).
+ Manually provide the two `simp` lemmas previously auto-generated by `@[simps]`. Mathlib compiles even without the two simp lemmas (see commit 1f5a7f1), but I am inclined to keep them in case some other branches/projects are using them.
[Zulip reports](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/285792556) about `intermediate_field_map` causing timeout in two separate branches
#### Estimated changes
modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field_map_apply_coe
- \+ *lemma* intermediate_field_map_symm_apply_coe
- \+/\- *def* intermediate_field_map
- \+/\- *def* intermediate_field_map



## [2022-06-15 03:13:17](https://github.com/leanprover-community/mathlib/commit/dd4d8e6)
feat(logic/hydra): basic lemmas on `cut_expand` ([#14408](https://github.com/leanprover-community/mathlib/pull/14408))
#### Estimated changes
modified src/logic/hydra.lean
- \+/\- *lemma* cut_expand_iff
- \+/\- *lemma* cut_expand_fibration
- \+/\- *lemma* cut_expand_iff
- \+/\- *lemma* cut_expand_fibration
- \+ *theorem* cut_expand_singleton
- \+ *theorem* cut_expand_singleton_singleton
- \+ *theorem* cut_expand_add_left
- \+ *theorem* not_cut_expand_zero
- \+/\- *def* cut_expand
- \+/\- *def* cut_expand



## [2022-06-15 03:13:16](https://github.com/leanprover-community/mathlib/commit/a16f1cf)
feat(set_theory/game/basic): cast inequalities on `pgame` to `game` ([#14405](https://github.com/leanprover-community/mathlib/pull/14405))
#### Estimated changes
modified src/set_theory/game/basic.lean
- \+ *theorem* _root_.pgame.le_iff_game_le
- \+ *theorem* _root_.pgame.lf_iff_game_lf
- \+ *theorem* _root_.pgame.lt_iff_game_lt
- \+ *theorem* _root_.pgame.equiv_iff_game_eq
- \+ *theorem* _root_.pgame.fuzzy_iff_game_fuzzy



## [2022-06-15 00:05:51](https://github.com/leanprover-community/mathlib/commit/bf2edb5)
feat(data/vector/basic): reflected instance for vectors ([#14669](https://github.com/leanprover-community/mathlib/pull/14669))
This means that a `vector` from a tactic block can be used in an expression.
#### Estimated changes
modified src/data/vector/basic.lean



## [2022-06-15 00:05:50](https://github.com/leanprover-community/mathlib/commit/b134b2f)
refactor(set_theory/game/state): rename `pgame.of` to `pgame.of_state` ([#14658](https://github.com/leanprover-community/mathlib/pull/14658))
This is so that we can redefine `pgame.of x y = {x | y}` in [#14659](https://github.com/leanprover-community/mathlib/pull/14659). Further, this is just a much clearer name.
#### Estimated changes
modified src/set_theory/game/domineering.lean
- \+/\- *def* domineering
- \+/\- *def* domineering

modified src/set_theory/game/state.lean
- \+ *def* of_state_aux
- \+ *def* of_state_aux_relabelling
- \+ *def* of_state
- \+ *def* left_moves_of_state_aux
- \+ *def* left_moves_of_state
- \+ *def* right_moves_of_state_aux
- \+ *def* right_moves_of_state
- \+/\- *def* relabelling_move_left
- \+/\- *def* relabelling_move_right
- \+ *def* of_state
- \- *def* of_aux
- \- *def* of_aux_relabelling
- \- *def* of
- \- *def* left_moves_of_aux
- \- *def* left_moves_of
- \- *def* right_moves_of_aux
- \- *def* right_moves_of
- \+/\- *def* relabelling_move_left
- \+/\- *def* relabelling_move_right
- \- *def* of



## [2022-06-15 00:05:49](https://github.com/leanprover-community/mathlib/commit/7b2970f)
feat(set_theory/cardinal/basic): improve docs on `lift`, add `simp` lemmas ([#14596](https://github.com/leanprover-community/mathlib/pull/14596))
We add some much needed documentation to the `cardinal.lift` API.  We also mark a few extra lemmas with `simp`.
#### Estimated changes
modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_umax'
- \+/\- *theorem* lift_id'
- \+/\- *theorem* lift_umax
- \+/\- *theorem* lift_umax'
- \+/\- *theorem* lift_id'



## [2022-06-15 00:05:48](https://github.com/leanprover-community/mathlib/commit/2e2d515)
feat(data/nat/factorization): add lemma `coprime_of_div_pow_factorization` ([#14576](https://github.com/leanprover-community/mathlib/pull/14576))
Add lemma `coprime_of_div_pow_factorization (hp : prime p) (hn : n ≠ 0) : coprime p (n / p ^ n.factorization p)`
Prompted by [this Zulip question](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/div.20by.20p_adic_val_nat.20is.20coprime).
#### Estimated changes
modified src/data/nat/factorization/basic.lean
- \+ *lemma* coprime_of_div_pow_factorization



## [2022-06-14 18:25:05](https://github.com/leanprover-community/mathlib/commit/16728b3)
feat(topology/homotopy/contractible): a few convenience lemmas ([#14710](https://github.com/leanprover-community/mathlib/pull/14710))
If `X` and `Y` are homotopy equivalent spaces, then one is
contractible if and only if the other one is contractible.
#### Estimated changes
modified src/topology/homotopy/contractible.lean
- \+/\- *lemma* id_nullhomotopic
- \+/\- *lemma* id_nullhomotopic



## [2022-06-14 18:25:02](https://github.com/leanprover-community/mathlib/commit/05aa960)
feat(analysis/special_functions/trigonometric/deriv): compare `sinh x` with `x` ([#14702](https://github.com/leanprover-community/mathlib/pull/14702))
#### Estimated changes
modified src/analysis/special_functions/arsinh.lean
- \- *lemma* sinh_injective

modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* sinh_log
- \+ *lemma* cosh_log

modified src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* sinh_injective
- \+ *lemma* sinh_inj
- \+ *lemma* sinh_le_sinh
- \+ *lemma* sinh_lt_sinh
- \+ *lemma* sinh_pos_iff
- \+ *lemma* sinh_nonpos_iff
- \+ *lemma* sinh_neg_iff
- \+ *lemma* sinh_nonneg_iff
- \+ *lemma* cosh_strict_mono_on
- \+ *lemma* cosh_le_cosh
- \+ *lemma* cosh_lt_cosh
- \+ *lemma* one_le_cosh
- \+ *lemma* one_lt_cosh
- \+ *lemma* sinh_sub_id_strict_mono
- \+ *lemma* self_le_sinh_iff
- \+ *lemma* sinh_le_self_iff
- \+ *lemma* self_lt_sinh_iff
- \+ *lemma* sinh_lt_self_iff

modified src/data/complex/exponential.lean
- \+ *lemma* cosh_abs



## [2022-06-14 18:24:59](https://github.com/leanprover-community/mathlib/commit/d5c7260)
feat(order/monotone): add lemmas about `cmp` ([#14689](https://github.com/leanprover-community/mathlib/pull/14689))
Also replace `order_dual.cmp_le_flip` with lemmas about `to_dual` and `of_dual`.
#### Estimated changes
modified src/data/ordmap/ordset.lean

modified src/order/compare.lean
- \+ *lemma* ordering.compares.cmp_eq
- \+ *lemma* cmp_le_to_dual
- \+ *lemma* cmp_le_of_dual
- \+ *lemma* cmp_to_dual
- \+ *lemma* cmp_of_dual
- \+ *lemma* eq_iff_eq_of_cmp_eq_cmp
- \- *lemma* order_dual.cmp_le_flip

modified src/order/monotone.lean
- \+ *lemma* strict_mono_on.cmp_map_eq
- \+ *lemma* strict_mono.cmp_map_eq
- \+ *lemma* strict_anti_on.cmp_map_eq
- \+ *lemma* strict_anti.cmp_map_eq



## [2022-06-14 17:04:56](https://github.com/leanprover-community/mathlib/commit/6cdc30d)
golf(set_theory/ordinal/basic): golf theorems on `cardinal.ord` and `ordinal.card`  ([#14709](https://github.com/leanprover-community/mathlib/pull/14709))
#### Estimated changes
modified src/set_theory/ordinal/basic.lean
- \+/\- *lemma* mk_ord_out
- \+/\- *lemma* mk_ord_out



## [2022-06-14 15:42:17](https://github.com/leanprover-community/mathlib/commit/ed033f3)
feat(linear_algebra/vandermonde): add lemmas about det equals zero ([#14695](https://github.com/leanprover-community/mathlib/pull/14695))
Adding two lemmas about when the determinant is zero.
I shortened the first with the help of some code I found in `ring_theory/trace.lean`, lemma `det_trace_matrix_ne_zero'`.
#### Estimated changes
modified src/linear_algebra/vandermonde.lean
- \+ *lemma* det_vandermonde_eq_zero_iff
- \+ *lemma* det_vandermonde_ne_zero_iff



## [2022-06-14 15:42:15](https://github.com/leanprover-community/mathlib/commit/41eb958)
feat({tactic + test}/congrm, logic/basic): `congrm = congr + pattern-match` ([#14153](https://github.com/leanprover-community/mathlib/pull/14153))
This PR defines a tactic `congrm`.  If the goal is an equality, where the sides are "almost" equal, then calling `congrm <expr_with_mvars_for_differences>` will produce goals for each place where the given expression has metavariables and will try to close the goal assuming all equalities have been proven.
For instance,
```
example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  exact h,
end
```
works.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/variant.20syntax.20for.20.60congr'.60)
#### Estimated changes
created src/tactic/congrm.lean

created test/congrm.lean



## [2022-06-14 13:35:08](https://github.com/leanprover-community/mathlib/commit/32d8fc4)
feat(topology/homeomorph): add `homeomorph.set.univ` ([#14730](https://github.com/leanprover-community/mathlib/pull/14730))
#### Estimated changes
modified src/topology/homeomorph.lean
- \+/\- *def* image
- \+ *def* set.univ
- \+/\- *def* image



## [2022-06-14 13:35:07](https://github.com/leanprover-community/mathlib/commit/1c8f995)
feat(analysis/special_functions/exp): add `real.exp_half` ([#14729](https://github.com/leanprover-community/mathlib/pull/14729))
#### Estimated changes
modified src/analysis/special_functions/exp.lean
- \+ *lemma* exp_half



## [2022-06-14 13:35:06](https://github.com/leanprover-community/mathlib/commit/da5a737)
feat(data/complex/basic): ranges of `re`, `im`, `norm_sq`, and `abs` ([#14727](https://github.com/leanprover-community/mathlib/pull/14727))
#### Estimated changes
modified src/data/complex/basic.lean
- \+ *lemma* range_norm_sq
- \+ *lemma* range_abs
- \+ *theorem* re_surjective
- \+ *theorem* im_surjective
- \+ *theorem* range_re
- \+ *theorem* range_im



## [2022-06-14 13:35:05](https://github.com/leanprover-community/mathlib/commit/b11f8e7)
refactor(algebra/order/group): unify instances ([#14705](https://github.com/leanprover-community/mathlib/pull/14705))
Drop `group.covariant_class_le.to_contravariant_class_le` etc in favor
of `group.covconv` (now an instance) and a new similar instance
`group.covconv_swap`.
#### Estimated changes
modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* group.covariant_swap_iff_contravariant_swap
- \- *lemma* group.covconv

modified src/algebra/order/group.lean



## [2022-06-14 13:35:03](https://github.com/leanprover-community/mathlib/commit/2b46992)
feat(algebra/algebra/basic): define `alg_hom_class` and `non_unital_alg_hom_class` ([#14679](https://github.com/leanprover-community/mathlib/pull/14679))
This PR defines `alg_hom_class` and `non_unital_alg_hom_class` as part of the morphism refactor.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \- *lemma* map_add
- \- *lemma* map_zero
- \- *lemma* map_mul
- \- *lemma* map_one
- \- *lemma* map_pow
- \- *lemma* map_smul
- \- *lemma* map_sum
- \- *lemma* map_finsupp_sum
- \- *lemma* map_bit0
- \- *lemma* map_bit1
- \- *lemma* map_multiset_prod
- \- *lemma* map_prod
- \- *lemma* map_finsupp_prod
- \- *lemma* map_neg
- \- *lemma* map_sub

modified src/algebra/hom/non_unital_alg.lean
- \- *lemma* map_smul
- \- *lemma* map_add
- \- *lemma* map_mul
- \- *lemma* map_zero



## [2022-06-14 13:35:02](https://github.com/leanprover-community/mathlib/commit/5d18a72)
feat(order/{conditionally_complete_lattice,galois_connection): Supremum of `set.image2` ([#14307](https://github.com/leanprover-community/mathlib/pull/14307))
`Sup` and `Inf` distribute over `set.image2` in the presence of appropriate Galois connections.
#### Estimated changes
modified src/order/complete_lattice.lean
- \+ *lemma* bsupr_prod
- \+ *lemma* binfi_prod
- \+ *lemma* Sup_image2
- \+ *lemma* Inf_image2
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_le_iff
- \+ *lemma* le_cinfi_iff
- \+ *lemma* csupr_set_le_iff
- \+ *lemma* le_cinfi_set_iff
- \+ *lemma* cSup_image2_eq_cSup_cSup
- \+ *lemma* cSup_image2_eq_cSup_cInf
- \+ *lemma* cSup_image2_eq_cInf_cSup
- \+ *lemma* cSup_image2_eq_cInf_cInf
- \+ *lemma* cInf_image2_eq_cInf_cInf
- \+ *lemma* cInf_image2_eq_cInf_cSup
- \+ *lemma* cInf_image2_eq_cSup_cInf
- \+ *lemma* cInf_image2_eq_cSup_cSup

modified src/order/galois_connection.lean
- \+ *lemma* Sup_image2_eq_Sup_Sup
- \+ *lemma* Sup_image2_eq_Sup_Inf
- \+ *lemma* Sup_image2_eq_Inf_Sup
- \+ *lemma* Sup_image2_eq_Inf_Inf
- \+ *lemma* Inf_image2_eq_Inf_Inf
- \+ *lemma* Inf_image2_eq_Inf_Sup
- \+ *lemma* Inf_image2_eq_Sup_Inf
- \+ *lemma* Inf_image2_eq_Sup_Sup



## [2022-06-14 13:35:01](https://github.com/leanprover-community/mathlib/commit/300c439)
feat(algebra/lie/weights): the zero root space is the Cartan subalgebra for a Noetherian Lie algebra ([#14174](https://github.com/leanprover-community/mathlib/pull/14174))
#### Estimated changes
modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* centralizer_eq_self_of_is_cartan_subalgebra

modified src/algebra/lie/of_associative.lean
- \+ *lemma* coe_map_to_endomorphism_le
- \+ *lemma* to_endomorphism_comp_subtype_mem
- \+ *lemma* to_endomorphism_restrict_eq_to_endomorphism
- \- *lemma* lie_submodule.coe_map_to_endomorphism_le

modified src/algebra/lie/weights.lean
- \+ *lemma* exists_pre_weight_space_zero_le_ker_of_is_noetherian
- \+ *lemma* is_nilpotent_to_endomorphism_weight_space_zero
- \+ *lemma* is_cartan_of_zero_root_subalgebra_eq
- \+ *lemma* zero_root_subalgebra_eq_of_is_cartan
- \+ *lemma* zero_root_subalgebra_eq_iff_is_cartan
- \- *lemma* zero_root_subalgebra_is_cartan_of_eq

modified src/linear_algebra/basic.lean
- \+ *lemma* pow_apply_mem_of_forall_mem
- \+ *lemma* pow_restrict

modified src/linear_algebra/eigenspace.lean
- \+ *lemma* eigenspace_zero
- \+ *lemma* generalized_eigenspace_zero



## [2022-06-14 11:24:09](https://github.com/leanprover-community/mathlib/commit/67dfb57)
feat(set_theory/cardinal/cofinality): lemma on subsets of strong limit cardinal ([#14442](https://github.com/leanprover-community/mathlib/pull/14442))
#### Estimated changes
modified src/order/rel_classes.lean
- \+ *lemma* unbounded_of_is_empty

modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* mk_bounded_subset
- \+ *theorem* mk_subset_mk_lt_cof

modified src/set_theory/ordinal/arithmetic.lean
- \+ *lemma* bounded_singleton



## [2022-06-14 01:31:50](https://github.com/leanprover-community/mathlib/commit/7fee0f1)
fix(data/list/nodup): change `Type` to `Type u` ([#14721](https://github.com/leanprover-community/mathlib/pull/14721))
Change `Type` to `Type u` in `nodup_iff_nth_ne_nth` and two other lemmas added in [#14371](https://github.com/leanprover-community/mathlib/pull/14371).
#### Estimated changes
modified src/data/list/basic.lean
- \+/\- *lemma* nth_le_eq_iff
- \+/\- *lemma* some_nth_le_eq
- \+/\- *lemma* nth_le_eq_iff
- \+/\- *lemma* some_nth_le_eq

modified src/data/list/nodup.lean
- \+/\- *lemma* nodup_iff_nth_ne_nth
- \+/\- *lemma* nodup_iff_nth_ne_nth
- \+/\- *theorem* nodup.nth_le_inj_iff
- \+/\- *theorem* nodup.nth_le_inj_iff



## [2022-06-14 01:31:49](https://github.com/leanprover-community/mathlib/commit/659983c)
feat(logic/equiv/basic): add `Pi_comm` aka `function.swap` as an `equiv` ([#14561](https://github.com/leanprover-community/mathlib/pull/14561))
#### Estimated changes
modified src/logic/equiv/basic.lean
- \+ *lemma* Pi_comm_symm
- \+ *def* Pi_comm



## [2022-06-14 01:31:48](https://github.com/leanprover-community/mathlib/commit/18bf7af)
refactor(algebra/order/monoid): Split field of `canonically_ordered_...` ([#14556](https://github.com/leanprover-community/mathlib/pull/14556))
Replace
```
(le_iff_exists_add : ∀ a b : α, a ≤ b ↔ ∃ c, b = a + c)
```
by
```
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c)
(le_self_add : ∀ a b : α, a ≤ a + b)
```
This makes our life easier because
* We can use existing `has_exists_add_of_le` instances to complete the `exists_add_of_le` field, and detect the missing ones.
* No need to substitute `b = a + c` every time.
#### Estimated changes
modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \+ *lemma* exists_add_of_le
- \+ *lemma* le_self_add
- \- *lemma* le_iff_exists_add

modified src/algebra/associated.lean

modified src/algebra/lie/subalgebra.lean

modified src/algebra/module/submodule/pointwise.lean

modified src/algebra/order/monoid.lean
- \+/\- *lemma* le_self_mul
- \+/\- *lemma* le_mul_self
- \+/\- *lemma* self_le_mul_right
- \+/\- *lemma* self_le_mul_left
- \+/\- *lemma* le_iff_exists_mul
- \+/\- *lemma* le_iff_exists_mul'
- \+/\- *lemma* le_iff_exists_mul
- \+/\- *lemma* le_iff_exists_mul'
- \+/\- *lemma* self_le_mul_right
- \+/\- *lemma* self_le_mul_left
- \+/\- *lemma* le_mul_self
- \+/\- *lemma* le_self_mul

modified src/algebra/order/nonneg.lean

modified src/algebra/order/pi.lean

modified src/algebra/punit_instances.lean

modified src/data/dfinsupp/order.lean

modified src/data/finsupp/order.lean

modified src/data/multiset/basic.lean

modified src/data/nat/basic.lean

modified src/data/nat/enat.lean

modified src/data/set/semiring.lean

modified src/set_theory/cardinal/basic.lean



## [2022-06-13 23:08:36](https://github.com/leanprover-community/mathlib/commit/2967fae)
refactor(data/option/defs): Swap arguments to `option.elim` ([#14681](https://github.com/leanprover-community/mathlib/pull/14681))
Make `option.elim` a non-dependent version of `option.rec` rather than a non-dependent version of `option.rec_on`. Same for `option.melim`.
This replaces `option.cons`, and brings `option.elim` in line with `nat.elim`, `sum.elim`, and `iff.elim`.
It addresses the TODO comment added in 22c4291217925c6957c0f5a44551c9917b56c7cf.
#### Estimated changes
modified src/algebra/big_operators/option.lean

modified src/analysis/box_integral/partition/basic.lean

modified src/analysis/calculus/lagrange_multipliers.lean

modified src/category_theory/category/PartialFun.lean
- \+/\- *def* Pointed_to_PartialFun
- \+/\- *def* Pointed_to_PartialFun

modified src/computability/tm_to_partrec.lean

modified src/data/finset/basic.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/option/basic.lean
- \+ *lemma* elim_none_some
- \- *lemma* cons_none_some
- \- *def* cons

modified src/data/option/defs.lean
- \+/\- *def* melim
- \+/\- *def* melim

modified src/logic/embedding.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/number_theory/dioph.lean

modified src/tactic/linarith/frontend.lean

modified src/topology/paracompact.lean



## [2022-06-13 21:43:10](https://github.com/leanprover-community/mathlib/commit/425dfe7)
feat(set_theory/game/ordinal): golf `to_pgame_birthday` ([#14662](https://github.com/leanprover-community/mathlib/pull/14662))
#### Estimated changes
modified src/set_theory/game/birthday.lean



## [2022-06-13 19:21:13](https://github.com/leanprover-community/mathlib/commit/3afafe6)
doc(ring_theory/algebraic): clarify docstring ([#14715](https://github.com/leanprover-community/mathlib/pull/14715))
#### Estimated changes
modified src/ring_theory/algebraic.lean



## [2022-06-13 19:21:12](https://github.com/leanprover-community/mathlib/commit/b44e742)
feat(category_theory/limits): realise products as pullbacks ([#14322](https://github.com/leanprover-community/mathlib/pull/14322))
This was mostly done in [#10581](https://github.com/leanprover-community/mathlib/pull/10581), this just adds the isomorphisms between the objects produced by the `has_limit` API.
#### Estimated changes
modified src/category_theory/limits/constructions/binary_products.lean
- \+ *def* prod_iso_pullback
- \+ *def* coprod_iso_pushout



## [2022-06-13 19:21:11](https://github.com/leanprover-community/mathlib/commit/a75460f)
feat(algebra/module/pid): Classification of finitely generated torsion modules over a PID ([#13524](https://github.com/leanprover-community/mathlib/pull/13524))
A finitely generated torsion module over a PID is isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
(TODO : This part should be generalisable to a Dedekind domain, see https://en.wikipedia.org/wiki/Dedekind_domain#Finitely_generated_modules_over_a_Dedekind_domain . Part of the proof is already generalised).
More generally, a finitely generated module over a PID is isomorphic to the product of a free module and a direct sum of some
`R ⧸ R ∙ (p i ^ e i)`.
(TODO : prove this decomposition is unique.)
(TODO : deduce the structure theorem for finite(ly generated) abelian groups).
- [x] depends on: [#13414](https://github.com/leanprover-community/mathlib/pull/13414)
- [x] depends on: [#14376](https://github.com/leanprover-community/mathlib/pull/14376) 
- [x] depends on: [#14573](https://github.com/leanprover-community/mathlib/pull/14573)
#### Estimated changes
modified docs/overview.yaml

modified src/algebra/big_operators/associated.lean
- \+ *theorem* finset_prod_mk

modified src/algebra/direct_sum/module.lean

created src/algebra/module/dedekind_domain.lean
- \+ *lemma* is_internal_prime_power_torsion_of_is_torsion_by_ideal
- \+ *theorem* is_internal_prime_power_torsion

created src/algebra/module/pid.lean
- \+ *lemma* _root_.ideal.torsion_of_eq_span_pow_p_order
- \+ *lemma* p_pow_smul_lift
- \+ *lemma* exists_smul_eq_zero_and_mk_eq
- \+ *theorem* submodule.is_internal_prime_power_torsion_of_pid
- \+ *theorem* torsion_by_prime_power_decomposition
- \+ *theorem* equiv_direct_sum_of_is_torsion
- \+ *theorem* equiv_free_prod_direct_sum

modified src/algebra/module/torsion.lean
- \- *lemma* sup_eq_top_iff_is_coprime

modified src/data/multiset/bind.lean
- \+ *lemma* le_bind

modified src/data/set/basic.lean
- \+ *lemma* insert_image_compl_eq_range

modified src/linear_algebra/quotient.lean
- \+ *lemma* mkq_surjective
- \+ *lemma* liftq_span_singleton_apply
- \+ *def* liftq_span_singleton

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* sup_eq_top_iff_is_coprime



## [2022-06-13 17:42:16](https://github.com/leanprover-community/mathlib/commit/3225926)
feat(category_theory/monoidal): monoidal functors `Type ⥤  C` acting on powers ([#14330](https://github.com/leanprover-community/mathlib/pull/14330))
#### Estimated changes
modified src/category_theory/monoidal/types.lean
- \+ *def* monoidal_functor.map_pi

modified src/logic/equiv/fin.lean
- \+ *def* equiv.pi_fin_succ



## [2022-06-13 16:22:21](https://github.com/leanprover-community/mathlib/commit/6ad2799)
chore(analysis/locally_convex/weak_dual): golf using `seminorm.comp` ([#14699](https://github.com/leanprover-community/mathlib/pull/14699))
#### Estimated changes
modified src/analysis/locally_convex/weak_dual.lean



## [2022-06-13 15:38:03](https://github.com/leanprover-community/mathlib/commit/aae786c)
feat(data/zmod/basic): fix a diamond in comm_ring and field ([#14712](https://github.com/leanprover-community/mathlib/pull/14712))
Before this change the following diamond existed:
```lean
import data.zmod.basic
variables {p : ℕ} [fact p.prime]
example :
  @euclidean_domain.to_comm_ring _ (@field.to_euclidean_domain _ (zmod.field p)) = zmod.comm_ring p :=
rfl
```
as the eta-expanded `zmod.comm_ring` was not defeq to itself, as it is defined via cases.
We fix this by instead defining each field by cases, which looks worse but at least seems to resolve the issue.
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/zmod.20comm_ring.20field.20diamond/near/285847071 for discussion
#### Estimated changes
modified src/data/zmod/basic.lean

modified test/instance_diamonds.lean



## [2022-06-13 14:24:16](https://github.com/leanprover-community/mathlib/commit/aed7f9a)
feat(topology/uniform_space/basic): add three easy lemmas about `uniform_space.comap` ([#14678](https://github.com/leanprover-community/mathlib/pull/14678))
These are uniform spaces versions of `filter.comap_inf`, `filter.comap_infi` and `filter.comap_mono`. I split them from [#14534](https://github.com/leanprover-community/mathlib/pull/14534) which is already a quite big PR.
#### Estimated changes
modified src/topology/algebra/uniform_field.lean

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_space.comap_inf
- \+ *lemma* uniform_space.comap_infi
- \+ *lemma* uniform_space.comap_mono



## [2022-06-13 13:01:51](https://github.com/leanprover-community/mathlib/commit/b7b371e)
doc(field_theory/finite/trace): fix module docstring ([#14711](https://github.com/leanprover-community/mathlib/pull/14711))
This PR just fixes the docstring in `field_theory/finite/trace.lean`. It was still mentioning a definition that was removed.
#### Estimated changes
modified src/field_theory/finite/trace.lean



## [2022-06-13 13:01:50](https://github.com/leanprover-community/mathlib/commit/46ac3cb)
chore(analysis/complex/upper_half_plane): move to a subdirectory ([#14704](https://github.com/leanprover-community/mathlib/pull/14704))
I'm going to add more files to `analysis/complex/upper_half_plane/` soon.
#### Estimated changes
renamed src/analysis/complex/upper_half_plane.lean to src/analysis/complex/upper_half_plane/basic.lean

modified src/number_theory/modular.lean



## [2022-06-13 11:39:13](https://github.com/leanprover-community/mathlib/commit/04019de)
chore(algebra/big_operators/associated,ring_theory/unique_factorization_domain): golf ([#14671](https://github.com/leanprover-community/mathlib/pull/14671))
#### Estimated changes
modified src/algebra/big_operators/associated.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* factors_unique
- \+/\- *lemma* ne_zero_of_mem_factors
- \+/\- *lemma* dvd_of_mem_factors
- \+/\- *lemma* factors_unique
- \+/\- *lemma* ne_zero_of_mem_factors
- \+/\- *lemma* dvd_of_mem_factors
- \+/\- *theorem* prime_of_factor
- \+/\- *theorem* prime_of_factor



## [2022-06-13 09:39:39](https://github.com/leanprover-community/mathlib/commit/b100037)
refactor(order/conditionally_complete_lattice): use `order_bot` ([#14568](https://github.com/leanprover-community/mathlib/pull/14568))
Use `order_bot` instead of an explicit `c = ⊥` argument in
`well_founded.conditionally_complete_linear_order_with_bot`. Also
reuse `linear_order.to_lattice` and add `well_founded.min_le`.
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean

modified src/order/well_founded.lean
- \+ *theorem* min_le

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/ordinal/basic.lean



## [2022-06-13 09:39:38](https://github.com/leanprover-community/mathlib/commit/4b67645)
chore(algebra/ring_quot): provide an explicit npow field ([#14349](https://github.com/leanprover-community/mathlib/pull/14349))
While this probably shouldn't matter since `ring_quot` is irreducible, this matches what we do for `nsmul` and `zsmul`.
#### Estimated changes
modified src/algebra/ring_quot.lean
- \+ *lemma* pow_quot



## [2022-06-13 08:58:22](https://github.com/leanprover-community/mathlib/commit/716824d)
feat(set_theory/surreal/dyadic): tweak API + golf ([#14649](https://github.com/leanprover-community/mathlib/pull/14649))
This PR does the following changes:
- Get rid of `pgame.half`, as it's def-eq to `pow_half 1`, which has strictly more API.
- Fix the docstring on `pow_half`, which incorrectly stated `pow_half 0 = 0`.
- Remove `simp` from some type equality lemmas.
- Remove the redundant theorems `pow_half_move_left'` and `pow_half_move_right'`.
- Add instances for left and right moves of `pow_half`. 
- Rename `zero_lt_pow_half` to `pow_half_pos`.
- Prove `pow_half_le_one` and `pow_half_succ_lt_one`.
- Make arguments explicit throughout.
- Golf proofs throughout.
#### Estimated changes
modified src/set_theory/game/birthday.lean
- \- *theorem* birthday_half

modified src/set_theory/game/pgame.lean
- \- *lemma* half_move_left
- \- *lemma* half_move_right
- \- *theorem* half_left_moves
- \- *theorem* half_right_moves
- \- *theorem* half_lt_one
- \- *theorem* half_add_half_equiv_one
- \- *def* half

modified src/set_theory/surreal/basic.lean
- \- *theorem* numeric_half

modified src/set_theory/surreal/dyadic.lean
- \+ *lemma* pow_half_zero
- \+/\- *lemma* pow_half_left_moves
- \+ *lemma* pow_half_zero_right_moves
- \+ *lemma* pow_half_succ_right_moves
- \+/\- *lemma* pow_half_move_left
- \+ *lemma* pow_half_succ_move_right
- \+/\- *lemma* double_pow_half_succ_eq_pow_half
- \+/\- *lemma* nsmul_pow_two_pow_half
- \+/\- *lemma* nsmul_pow_two_pow_half'
- \+/\- *lemma* pow_half_left_moves
- \- *lemma* pow_half_right_moves
- \+/\- *lemma* pow_half_move_left
- \- *lemma* pow_half_move_right
- \- *lemma* pow_half_move_left'
- \- *lemma* pow_half_move_right'
- \- *lemma* pow_half_one
- \+/\- *lemma* double_pow_half_succ_eq_pow_half
- \+/\- *lemma* nsmul_pow_two_pow_half
- \+/\- *lemma* nsmul_pow_two_pow_half'
- \+ *theorem* birthday_half
- \+/\- *theorem* numeric_pow_half
- \+/\- *theorem* pow_half_succ_lt_pow_half
- \+/\- *theorem* pow_half_succ_le_pow_half
- \+ *theorem* pow_half_le_one
- \+ *theorem* pow_half_succ_lt_one
- \+ *theorem* pow_half_pos
- \+/\- *theorem* zero_le_pow_half
- \+/\- *theorem* add_pow_half_succ_self_eq_pow_half
- \+ *theorem* half_add_half_equiv_one
- \+/\- *theorem* numeric_pow_half
- \+/\- *theorem* pow_half_succ_lt_pow_half
- \+/\- *theorem* pow_half_succ_le_pow_half
- \- *theorem* zero_lt_pow_half
- \+/\- *theorem* zero_le_pow_half
- \+/\- *theorem* add_pow_half_succ_self_eq_pow_half
- \- *theorem* add_half_self_eq_one
- \+/\- *def* pow_half
- \- *def* half
- \+/\- *def* pow_half



## [2022-06-13 03:45:17](https://github.com/leanprover-community/mathlib/commit/dc9eab6)
feat(tactic/lift): generalize pi.can_lift to Sort ([#14700](https://github.com/leanprover-community/mathlib/pull/14700))
#### Estimated changes
modified src/tactic/lift.lean



## [2022-06-12 20:34:14](https://github.com/leanprover-community/mathlib/commit/8fb92bf)
feat(measure_theory/integral/circle_integral): add lemma `circle_map_nmem_ball` ([#14643](https://github.com/leanprover-community/mathlib/pull/14643))
The lemma `set.ne_of_mem_nmem` is unrelated except that both of these should be helpful for:
https://github.com/leanprover-community/mathlib/pull/13885
#### Estimated changes
modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* circle_map_not_mem_ball
- \+ *lemma* circle_map_ne_mem_ball



## [2022-06-12 16:53:57](https://github.com/leanprover-community/mathlib/commit/d6eb634)
feat(number_theory/legendre_symbol/auxiliary, *): add/move lemmas in/to various files, delete `auxiliary.lean` ([#14572](https://github.com/leanprover-community/mathlib/pull/14572))
This is the first PR in a series that will culminate in providing the proof of Quadratic Reciprocity using Gauss sums.
Here we just add some lemmas to the file `auxiliary.lean` that will be used in new code later.
We also generalize the lemmas `neg_one_ne_one_of_char_ne_two` and `neg_ne_self_of_char_ne_two` from finite fields to more general rings.
See [this Zulipt topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A/near/285053214) for more information.
**CHANGE OF PLAN:** Following the discussion on Zulip linked to above, the lemmas in `auxiliary.lean` are supposed to be moved to there proper places. I have added suggestions to each lemma or group of lemmas (or definitions) what the proper place could be (in some cases, there are alternatives). Please comment if you do not agree or to support one of the alternatives.
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* is_square_of_char_two'
- \+ *lemma* ring.two_ne_zero
- \+ *lemma* ring.neg_one_ne_one_of_char_ne_two
- \+ *lemma* ring.eq_self_iff_eq_zero_of_char_ne_two
- \+ *lemma* int.cast_inj_on_of_ring_char_ne_two

created src/algebra/char_p/char_and_card.lean
- \+ *lemma* is_unit_iff_not_dvd_char
- \+ *lemma* prime_dvd_char_iff_dvd_card
- \+ *lemma* not_is_unit_prime_of_dvd_card

modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_pow_mod
- \+ *lemma* coe_pow_monoid_with_zero_hom
- \+ *lemma* pow_monoid_with_zero_hom_apply
- \+ *def* pow_monoid_with_zero_hom

modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* monoid_with_zero.coe_inverse
- \+ *lemma* monoid_with_zero.inverse_apply
- \+ *def* monoid_with_zero.inverse

modified src/data/nat/modeq.lean
- \+ *lemma* odd_mod_four_iff

modified src/field_theory/finite/basic.lean
- \+ *lemma* is_square_of_char_two
- \+ *lemma* even_card_iff_char_two
- \+ *lemma* even_card_of_char_two
- \+ *lemma* odd_card_of_char_ne_two
- \+ *lemma* pow_dichotomy
- \+ *lemma* unit_is_square_iff
- \+ *lemma* is_square_iff
- \+ *lemma* exists_nonsquare

created src/field_theory/finite/trace.lean
- \+ *lemma* trace_to_zmod_nondegenerate

deleted src/number_theory/legendre_symbol/auxiliary.lean
- \- *lemma* nat.odd_mod_four_iff
- \- *lemma* is_square_of_char_two'
- \- *lemma* is_square_of_char_two
- \- *lemma* even_card_iff_char_two
- \- *lemma* even_card_of_char_two
- \- *lemma* odd_card_of_char_ne_two
- \- *lemma* neg_one_ne_one_of_char_ne_two
- \- *lemma* neg_ne_self_of_char_ne_two
- \- *lemma* pow_dichotomy
- \- *lemma* unit_is_square_iff
- \- *lemma* is_square_iff
- \- *lemma* exists_nonsquare

modified src/number_theory/legendre_symbol/quadratic_char.lean

modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean

modified src/number_theory/legendre_symbol/zmod_char.lean



## [2022-06-12 16:03:11](https://github.com/leanprover-community/mathlib/commit/97c9ef8)
chore(measure_theory): use notation `measurable_set[m]` ([#14690](https://github.com/leanprover-community/mathlib/pull/14690))
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measurable_space_def.lean

modified src/measure_theory/measure/content.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/measure_theory/measure/stieltjes.lean

modified src/measure_theory/pi_system.lean

modified src/probability/independence.lean

modified src/probability/integration.lean



## [2022-06-12 11:53:19](https://github.com/leanprover-community/mathlib/commit/8cad81a)
feat(data/{finset,set}/basic): More `insert` and `erase` lemmas ([#14675](https://github.com/leanprover-community/mathlib/pull/14675))
Also turn `finset.disjoint_iff_disjoint_coe` around and change `set.finite.to_finset_insert` take `(insert a s).finite` instead of `s.finite`.
#### Estimated changes
modified src/algebra/big_operators/finprod.lean

modified src/data/finset/basic.lean
- \+ *lemma* erase_ssubset_insert
- \+ *lemma* erase_cons
- \+ *lemma* subset_insert_iff_of_not_mem
- \+ *lemma* erase_subset_iff_of_mem
- \+ *lemma* erase_inj_on'
- \+ *lemma* filter_inter_distrib
- \+ *lemma* image_inter_of_inj_on
- \+/\- *lemma* image_inter
- \+ *lemma* erase_image_subset_image_erase
- \+ *lemma* disjoint_coe
- \+ *lemma* pairwise_disjoint_coe
- \+/\- *lemma* image_inter
- \- *lemma* disjoint_iff_disjoint_coe
- \+ *theorem* pair_eq_singleton
- \- *theorem* pair_self_eq

modified src/data/finset/pointwise.lean

modified src/data/fintype/basic.lean
- \+/\- *lemma* eq_univ_iff_forall
- \+ *lemma* eq_univ_of_forall
- \+ *lemma* coe_eq_univ
- \+ *lemma* image_univ_of_surjective
- \+/\- *lemma* eq_univ_iff_forall

modified src/data/set/basic.lean
- \+ *lemma* insert_idem

modified src/data/set/finite.lean
- \+ *lemma* finite.to_finset_singleton
- \+/\- *lemma* finite.to_finset_insert
- \+ *lemma* finite.to_finset_insert'
- \+/\- *lemma* finite.to_finset_insert

modified src/data/set/lattice.lean
- \+ *lemma* Union_comm
- \+ *lemma* Inter_comm
- \+ *lemma* Union₂_comm
- \+ *lemma* Inter₂_comm
- \- *theorem* Union_comm
- \- *theorem* Inter_comm

modified src/group_theory/perm/cycle/basic.lean

modified src/group_theory/perm/support.lean

modified src/logic/basic.lean
- \+ *lemma* exists₂_comm

modified src/order/complete_lattice.lean
- \+ *lemma* supr₂_comm
- \+ *lemma* infi₂_comm



## [2022-06-12 11:13:54](https://github.com/leanprover-community/mathlib/commit/579d6f9)
feat(data/polynomial/laurent): Laurent polynomials are a localization of polynomials ([#14489](https://github.com/leanprover-community/mathlib/pull/14489))
This PR proves the lemma `is_localization (submonoid.closure ({X} : set R[X])) R[T;T⁻¹]`.
#### Estimated changes
modified src/data/polynomial/laurent.lean
- \+ *lemma* algebra_map_X_pow
- \+ *lemma* algebra_map_eq_to_laurent
- \+ *lemma* is_localization



## [2022-06-12 08:43:37](https://github.com/leanprover-community/mathlib/commit/4a3b22e)
feat(number_theory/bernoulli_polynomials): Derivative of Bernoulli polynomial ([#14625](https://github.com/leanprover-community/mathlib/pull/14625))
Add the statement that the derivative of `bernoulli k x` is `k * bernoulli (k-1) x`. This will be used in a subsequent PR to evaluate the even positive integer values of the Riemann zeta function.
#### Estimated changes
modified src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* derivative_bernoulli_add_one
- \+ *lemma* derivative_bernoulli



## [2022-06-12 05:48:33](https://github.com/leanprover-community/mathlib/commit/0926f07)
feat(data/polynomial/eval): add some lemmas for `comp` ([#14346](https://github.com/leanprover-community/mathlib/pull/14346))
#### Estimated changes
modified src/data/polynomial/eval.lean
- \+ *lemma* coe_comp_ring_hom
- \+ *lemma* coe_comp_ring_hom_apply
- \+ *lemma* list_prod_comp
- \+ *lemma* multiset_prod_comp
- \+/\- *lemma* prod_comp
- \+/\- *lemma* prod_comp

modified src/field_theory/abel_ruffini.lean



## [2022-06-12 05:09:43](https://github.com/leanprover-community/mathlib/commit/eb063e7)
feat(category_theory/Fintype): equiv_equiv_iso ([#13984](https://github.com/leanprover-community/mathlib/pull/13984))
From LTE.
#### Estimated changes
modified src/category_theory/Fintype.lean
- \+ *def* equiv_equiv_iso



## [2022-06-11 15:30:23](https://github.com/leanprover-community/mathlib/commit/053a03d)
feat(algebra/char_p): `char_p` of a local ring is zero or prime power ([#14461](https://github.com/leanprover-community/mathlib/pull/14461))
For a local commutative ring the characteristics is either zero or a prime power.
#### Estimated changes
created src/algebra/char_p/local_ring.lean
- \+ *theorem* char_p_zero_or_prime_power

modified src/data/nat/factorization/basic.lean
- \+ *lemma* div_factorization_pos
- \+ *lemma* ne_dvd_factorization_div



## [2022-06-11 14:33:12](https://github.com/leanprover-community/mathlib/commit/2e3a0a6)
feat(analysis/special_functions/log): add `real.log_sqrt` ([#14663](https://github.com/leanprover-community/mathlib/pull/14663))
#### Estimated changes
modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* log_sqrt



## [2022-06-11 11:06:30](https://github.com/leanprover-community/mathlib/commit/d1a6dd2)
feat(topology/algebra/module/locally_convex): local convexity is preserved by `Inf` and `induced` ([#12118](https://github.com/leanprover-community/mathlib/pull/12118))
I also generalized slightly `locally_convex_space.of_bases` and changed a `Sort*` to `Type*` in `filter.has_basis_infi` to correctly reflect the universe constraints.
#### Estimated changes
modified src/order/filter/bases.lean
- \+/\- *lemma* has_basis_infi
- \+/\- *lemma* has_basis_infi

modified src/topology/algebra/module/locally_convex.lean
- \+/\- *lemma* locally_convex_space.of_bases
- \+ *lemma* locally_convex_space_Inf
- \+ *lemma* locally_convex_space_infi
- \+ *lemma* locally_convex_space_inf
- \+ *lemma* locally_convex_space_induced
- \+/\- *lemma* locally_convex_space.of_bases



## [2022-06-11 08:59:36](https://github.com/leanprover-community/mathlib/commit/13b999c)
feat(algebra/{group,hom}/units): Units in division monoids ([#14212](https://github.com/leanprover-community/mathlib/pull/14212))
Copy over `group_with_zero` lemmas to the more general setting of `division_monoid`.
#### Estimated changes
modified src/algebra/group/units.lean
- \+/\- *lemma* inv_mul_of_eq
- \+/\- *lemma* mul_inv_of_eq
- \+ *lemma* mul_inv_eq_one
- \+ *lemma* inv_mul_eq_one
- \+ *lemma* mul_eq_one_iff_eq_inv
- \+ *lemma* mul_eq_one_iff_inv_eq
- \+ *lemma* is_unit.mul_left_inj
- \+ *lemma* is_unit.mul_right_inj
- \+/\- *lemma* inv_mul_of_eq
- \+/\- *lemma* mul_inv_of_eq
- \- *lemma* inv_eq_of_mul_eq_one_right
- \- *lemma* eq_iff_inv_mul
- \- *theorem* is_unit.mul_right_inj
- \- *theorem* is_unit.mul_left_inj

modified src/algebra/group_with_zero/basic.lean
- \- *theorem* divp_eq_div

modified src/algebra/hom/units.lean
- \+ *lemma* _root_.divp_eq_div
- \+ *lemma* map
- \+ *lemma* coe_lift_right
- \+ *lemma* mul_lift_right_inv
- \+ *lemma* lift_right_inv_mul
- \+ *lemma* inv
- \+ *lemma* div
- \- *lemma* is_unit.map
- \- *lemma* is_unit.coe_lift_right
- \- *lemma* is_unit.mul_lift_right_inv
- \- *lemma* is_unit.lift_right_inv_mul
- \+ *def* unit'

modified src/ring_theory/ideal/local_ring.lean



## [2022-06-11 02:10:15](https://github.com/leanprover-community/mathlib/commit/050404a)
feat(group_theory/sylow): Sylow subgroups are Hall subgroups ([#14624](https://github.com/leanprover-community/mathlib/pull/14624))
This PR adds a lemma stating that Sylow subgroups are Hall subgroups (cardinality is coprime to index).
#### Estimated changes
modified src/group_theory/sylow.lean
- \+ *lemma* card_coprime_index



## [2022-06-10 14:50:29](https://github.com/leanprover-community/mathlib/commit/18936e5)
feat(topology/uniform_space/equiv): define uniform isomorphisms ([#14537](https://github.com/leanprover-community/mathlib/pull/14537))
This adds a new file, mostly copy-pasted from `topology/homeomorph`, to analogously define uniform isomorphisms
#### Estimated changes
modified src/data/prod/basic.lean
- \+/\- *lemma* id_prod
- \+ *lemma* map_id
- \+/\- *lemma* id_prod

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_continuous_subtype_coe

created src/topology/uniform_space/equiv.lean
- \+ *lemma* uniform_equiv_mk_coe
- \+ *lemma* coe_to_equiv
- \+ *lemma* coe_symm_to_equiv
- \+ *lemma* to_equiv_injective
- \+ *lemma* ext
- \+ *lemma* trans_apply
- \+ *lemma* uniform_equiv_mk_coe_symm
- \+ *lemma* refl_symm
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm
- \+ *lemma* range_coe
- \+ *lemma* image_symm
- \+ *lemma* preimage_symm
- \+ *lemma* image_preimage
- \+ *lemma* preimage_image
- \+ *lemma* comap_eq
- \+ *lemma* prod_congr_symm
- \+ *lemma* coe_prod_congr
- \+ *lemma* prod_comm_symm
- \+ *lemma* coe_prod_comm
- \+ *lemma* coe_punit_prod
- \+ *def* simps.apply
- \+ *def* simps.symm_apply
- \+ *def* change_inv
- \+ *def* set_congr
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* prod_assoc
- \+ *def* prod_punit
- \+ *def* punit_prod
- \+ *def* fun_unique
- \+ *def* {u}
- \+ *def* fin_two_arrow
- \+ *def* image
- \+ *def* equiv.to_uniform_equiv_of_uniform_inducing

modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* uniform_inducing_id
- \+ *lemma* uniform_inducing_of_compose



## [2022-06-10 12:55:31](https://github.com/leanprover-community/mathlib/commit/8c812fd)
feat(topology/algebra/order): `coe : ℚ → 𝕜` has dense range ([#14635](https://github.com/leanprover-community/mathlib/pull/14635))
* add `rat.dense_range_cast`, use it in `rat.dense_embedding_coe_real`;
* rename `dense_iff_forall_lt_exists_mem` to `dense_iff_exists_between`;
* add `dense_of_exists_between`, use it in `dense_iff_exists_between`.
#### Estimated changes
created src/topology/algebra/order/archimedean.lean
- \+ *lemma* rat.dense_range_cast

modified src/topology/algebra/order/basic.lean
- \+ *lemma* dense_of_exists_between
- \+ *lemma* dense_iff_exists_between
- \- *lemma* dense_iff_forall_lt_exists_mem

modified src/topology/basic.lean

modified src/topology/instances/rat.lean



## [2022-06-10 12:55:30](https://github.com/leanprover-community/mathlib/commit/0f5a1f2)
feat(data/rat): Add some lemmas to work with num/denom ([#14456](https://github.com/leanprover-community/mathlib/pull/14456))
#### Estimated changes
modified src/data/rat/basic.lean
- \+ *lemma* mk_mul_mk_cancel
- \+ *lemma* mk_div_mk_cancel_left
- \+ *lemma* mk_div_mk_cancel_right
- \+ *lemma* coe_int_div_eq_mk
- \+ *lemma* mul_num_denom'
- \+ *lemma* add_num_denom'
- \+ *lemma* substr_num_denom'



## [2022-06-10 10:43:10](https://github.com/leanprover-community/mathlib/commit/95da649)
feat(analysis/inner_product_space): Generalize Gram-Schmidt ([#14379](https://github.com/leanprover-community/mathlib/pull/14379))
The generalisation is to allow a family of vectors indexed by a general indexing set `ι` (carrying appropriate order typeclasses) rather than just `ℕ`.
#### Estimated changes
modified src/analysis/box_integral/partition/basic.lean

modified src/analysis/box_integral/partition/tagged.lean

modified src/analysis/inner_product_space/gram_schmidt_ortho.lean
- \+/\- *lemma* gram_schmidt_def
- \+/\- *lemma* gram_schmidt_def'
- \+/\- *lemma* gram_schmidt_zero
- \+/\- *lemma* span_gram_schmidt
- \+ *lemma* gram_schmidt_ne_zero_coe
- \+/\- *lemma* gram_schmidt_ne_zero
- \+ *lemma* gram_schmidt_normed_unit_length_coe
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \+/\- *lemma* gram_schmidt_def
- \+/\- *lemma* gram_schmidt_def'
- \+/\- *lemma* gram_schmidt_zero
- \+/\- *lemma* span_gram_schmidt
- \+/\- *lemma* gram_schmidt_ne_zero
- \- *lemma* gram_schmidt_ne_zero'
- \+/\- *lemma* gram_schmidt_normed_unit_length
- \- *lemma* gram_schmidt_normed_unit_length'
- \+/\- *theorem* gram_schmidt_orthogonal
- \+/\- *theorem* gram_schmidt_pairwise_orthogonal
- \+/\- *theorem* gram_schmidt_orthonormal
- \+/\- *theorem* gram_schmidt_orthogonal
- \+/\- *theorem* gram_schmidt_pairwise_orthogonal
- \+/\- *theorem* gram_schmidt_orthonormal

modified src/data/finset/lattice.lean
- \- *lemma* sup_le_iff

modified src/data/finset/powerset.lean

modified src/order/rel_classes.lean
- \+ *def* is_well_order.to_has_well_founded

modified src/order/succ_pred/basic.lean
- \+ *lemma* Ioi_pred_eq_insert_of_not_is_min



## [2022-06-10 10:04:50](https://github.com/leanprover-community/mathlib/commit/391d178)
feat(set_theory/game/ordinal): golf `to_pgame_injective` ([#14661](https://github.com/leanprover-community/mathlib/pull/14661))
We also add the `eq_iff` version and remove an outdated todo comment.
#### Estimated changes
modified src/set_theory/game/ordinal.lean
- \+ *theorem* to_pgame_eq_iff

modified src/set_theory/game/pgame.lean
- \+ *theorem* equiv_of_eq



## [2022-06-10 10:04:49](https://github.com/leanprover-community/mathlib/commit/68dc07f)
refactor(set_theory/game/pgame): rename and add theorems like `-y ≤ -x ↔ x ≤ y` ([#14653](https://github.com/leanprover-community/mathlib/pull/14653))
For `*` in `le`, `lf`, `lt`, we rename `neg_*_iff : -y * -x ↔ x * y` to `neg_*_neg_iff`, and add the theorems `neg_*_iff : -y * x ↔ x * -y`.
We further add many missing corresponding theorems for equivalence and fuzziness.
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/birthday.lean

modified src/set_theory/game/impartial.lean

modified src/set_theory/game/pgame.lean
- \+ *theorem* neg_le_neg_iff
- \+ *theorem* neg_lf_neg_iff
- \+ *theorem* neg_lt_neg_iff
- \+ *theorem* neg_equiv_neg_iff
- \+ *theorem* neg_fuzzy_neg_iff
- \+/\- *theorem* neg_le_iff
- \+/\- *theorem* neg_lf_iff
- \+/\- *theorem* neg_lt_iff
- \+ *theorem* neg_equiv_iff
- \+ *theorem* neg_fuzzy_iff
- \+ *theorem* le_neg_iff
- \+ *theorem* lf_neg_iff
- \+ *theorem* lt_neg_iff
- \+ *theorem* neg_equiv_zero_iff
- \+ *theorem* neg_fuzzy_zero_iff
- \+ *theorem* zero_equiv_neg_iff
- \+ *theorem* zero_fuzzy_neg_iff
- \+/\- *theorem* neg_le_iff
- \- *theorem* neg_congr
- \+/\- *theorem* neg_lf_iff
- \+/\- *theorem* neg_lt_iff

modified src/set_theory/surreal/basic.lean



## [2022-06-10 07:36:57](https://github.com/leanprover-community/mathlib/commit/a912392)
feat(data/fintype/basic): add `card_subtype_mono` ([#14645](https://github.com/leanprover-community/mathlib/pull/14645))
This lemma naturally forms a counterpart to existing lemmas.
I've also renamed a lemma it uses that didn't seem to fit the existing naming pattern.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *theorem* card_subtype_mono



## [2022-06-10 07:36:56](https://github.com/leanprover-community/mathlib/commit/771f2b7)
chore(topology/metric_space/basic): add `metric_space.replace_bornology` ([#14638](https://github.com/leanprover-community/mathlib/pull/14638))
We have the `pseudo_metric_space` version from [#13927](https://github.com/leanprover-community/mathlib/pull/13927), but not the `metric_space` version.
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+ *lemma* metric_space.replace_bornology_eq
- \+ *def* metric_space.replace_bornology



## [2022-06-10 07:36:55](https://github.com/leanprover-community/mathlib/commit/5bccb51)
refactor(logic/equiv/basic): tweak lemmas on equivalences between `unique` types ([#14605](https://github.com/leanprover-community/mathlib/pull/14605))
This PR does various simple and highly related things:
- Rename `equiv_of_unique_of_unique` to `equiv_of_unique` and make its arguments explicit, in order to match the lemma `equiv_of_empty` added in [#14604](https://github.com/leanprover-community/mathlib/pull/14604).  
- Rename `equiv_punit_of_unique` to `equiv_punit` and make its argument explicit to match `equiv_pempty`.
- Fix their docstrings (which talked about a `subsingleton` type instead of a `unique` one).
- Move them much earlier in the file, together with the lemmas on empty types.
- Golf `prop_equiv_punit`.
#### Estimated changes
modified src/algebra/hom/equiv.lean

modified src/group_theory/perm/cycle/type.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/logic/equiv/basic.lean
- \+ *def* equiv_of_unique
- \+ *def* equiv_punit
- \+/\- *def* prop_equiv_punit
- \+/\- *def* prop_equiv_punit
- \- *def* true_equiv_punit
- \- *def* equiv_of_unique_of_unique
- \- *def* equiv_punit_of_unique

modified src/logic/equiv/fin.lean

modified src/measure_theory/measurable_space.lean

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/game/nim.lean



## [2022-06-10 07:36:53](https://github.com/leanprover-community/mathlib/commit/7691821)
feat(data/polynomial/derivative): reduce assumptions ([#14338](https://github.com/leanprover-community/mathlib/pull/14338))
The only changes here are to relax typeclass assumptions.
Specifically these changes relax `comm_semiring` to `semiring` in:
 * polynomial.derivative_eval
 * polynomial.derivative_map
 * polynomial.iterate_derivative_map
 * polynomial.iterate_derivative_cast_nat_mul
and relax `ring` to `semiring` as well as `char_zero` + `no_zero_divisors` to `no_zero_smul_divisors ℕ` in:
 * polynomial.mem_support_derivative
 * polynomial.degree_derivative_eq
#### Estimated changes
modified src/data/polynomial/derivative.lean
- \+/\- *lemma* derivative_eval
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *lemma* mem_support_derivative
- \+/\- *lemma* degree_derivative_eq
- \+/\- *lemma* derivative_eval
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *lemma* mem_support_derivative
- \+/\- *lemma* degree_derivative_eq
- \+/\- *theorem* derivative_map
- \+/\- *theorem* iterate_derivative_map
- \+/\- *theorem* derivative_map
- \+/\- *theorem* iterate_derivative_map



## [2022-06-10 07:36:52](https://github.com/leanprover-community/mathlib/commit/39184f4)
feat(dynamics/periodic_pts): Orbit under periodic function ([#12976](https://github.com/leanprover-community/mathlib/pull/12976))
#### Estimated changes
modified src/dynamics/periodic_pts.lean
- \+/\- *lemma* is_periodic_pt_minimal_period
- \+/\- *lemma* iterate_minimal_period
- \+ *lemma* iterate_add_minimal_period_eq
- \+ *lemma* iterate_mod_minimal_period_eq
- \+ *lemma* minimal_period_eq_zero_of_nmem_periodic_pts
- \+ *lemma* minimal_period_eq_zero_iff_nmem_periodic_pts
- \+ *lemma* minimal_period_apply_iterate
- \+ *lemma* minimal_period_apply
- \+ *lemma* le_of_lt_minimal_period_of_iterate_eq
- \+ *lemma* eq_of_lt_minimal_period_of_iterate_eq
- \+ *lemma* eq_iff_lt_minimal_period_of_iterate_eq
- \+/\- *lemma* is_periodic_pt.minimal_period_dvd
- \+/\- *lemma* is_periodic_pt_iff_minimal_period_dvd
- \+ *lemma* periodic_orbit_def
- \+ *lemma* periodic_orbit_eq_cycle_map
- \+ *lemma* periodic_orbit_length
- \+ *lemma* periodic_orbit_eq_nil_iff_not_periodic_pt
- \+ *lemma* periodic_orbit_eq_nil_of_not_periodic_pt
- \+ *lemma* mem_periodic_orbit_iff
- \+ *lemma* iterate_mem_periodic_orbit
- \+ *lemma* self_mem_periodic_orbit
- \+ *lemma* nodup_periodic_orbit
- \+ *lemma* periodic_orbit_apply_iterate_eq
- \+ *lemma* periodic_orbit_apply_eq
- \+/\- *lemma* is_periodic_pt_minimal_period
- \+/\- *lemma* iterate_minimal_period
- \- *lemma* iterate_eq_mod_minimal_period
- \- *lemma* iterate_injective_of_lt_minimal_period
- \+/\- *lemma* is_periodic_pt.minimal_period_dvd
- \+/\- *lemma* is_periodic_pt_iff_minimal_period_dvd
- \+ *def* periodic_orbit

modified src/group_theory/order_of_element.lean



## [2022-06-10 05:26:20](https://github.com/leanprover-community/mathlib/commit/e3dade3)
feat(data/finite/basic): `finite` predicate ([#14373](https://github.com/leanprover-community/mathlib/pull/14373))
Introduces a `Prop`-valued finiteness predicate on types and adapts some subset of the `fintype` API to get started. Uses `nat.card` as the primary cardinality function.
#### Estimated changes
created src/data/finite/basic.lean
- \+ *lemma* finite.exists_equiv_fin
- \+ *lemma* finite.of_equiv
- \+ *lemma* equiv.finite_iff
- \+ *lemma* finite.of_fintype
- \+ *lemma* finite_iff_nonempty_fintype
- \+ *lemma* finite_or_infinite
- \+ *lemma* not_finite
- \+ *lemma* finite.of_not_infinite
- \+ *lemma* infinite.of_not_finite
- \+ *lemma* not_infinite_iff_finite
- \+ *lemma* not_finite_iff_infinite
- \+ *lemma* nat.card_eq
- \+ *lemma* finite.card_pos_iff
- \+ *lemma* of_subsingleton
- \+ *lemma* exists_max
- \+ *lemma* exists_min
- \+ *lemma* of_bijective
- \+ *lemma* of_injective
- \+ *lemma* of_surjective
- \+ *lemma* card_eq
- \+ *lemma* card_le_one_iff_subsingleton
- \+ *lemma* one_lt_card_iff_nontrivial
- \+ *lemma* one_lt_card
- \+ *lemma* card_option
- \+ *lemma* prod_left
- \+ *lemma* prod_right
- \+ *lemma* sum_left
- \+ *lemma* sum_right
- \+ *lemma* card_sum
- \+ *lemma* card_le_of_injective
- \+ *lemma* card_le_of_embedding
- \+ *lemma* card_le_of_surjective
- \+ *lemma* card_eq_zero_iff
- \+ *theorem* finite.card_subtype_le
- \+ *theorem* finite.card_subtype_lt
- \+ *def* finite.equiv_fin
- \+ *def* finite.equiv_fin_of_card_eq
- \+ *def* fintype.of_finite

modified src/data/nat/totient.lean

modified src/logic/unique.lean
- \+ *lemma* unique_iff_subsingleton_and_nonempty

modified src/set_theory/cardinal/finite.lean
- \+ *lemma* card_congr
- \+ *lemma* card_eq_of_bijective
- \+ *lemma* card_eq_of_equiv_fin
- \+ *lemma* card_of_subsingleton
- \+ *lemma* card_unique
- \+ *lemma* card_eq_one_iff_unique
- \+ *lemma* card_prod
- \+ *lemma* card_ulift
- \+ *lemma* card_plift
- \+ *theorem* card_of_is_empty
- \+ *def* equiv_fin_of_card_pos



## [2022-06-10 04:32:43](https://github.com/leanprover-community/mathlib/commit/e9d2564)
chore(measure_theory): golf ([#14657](https://github.com/leanprover-community/mathlib/pull/14657))
Also use `@measurable_set α m s` instead of `m.measurable_set' s` in the definition of the partial order on `measurable_space`. This way we can use dot notation lemmas about measurable sets in a proof of `m₁ ≤ m₂`.
#### Estimated changes
modified src/measure_theory/measurable_space_def.lean

modified src/measure_theory/measure/measure_space_def.lean



## [2022-06-10 02:04:07](https://github.com/leanprover-community/mathlib/commit/ed2cfce)
feat(set_theory/ordinal/basic): tweak theorems on order type of empty relation ([#14650](https://github.com/leanprover-community/mathlib/pull/14650))
We move the theorems on the order type of an empty relation much earlier, and golf them. We also remove other redundant theorems.
`zero_eq_type_empty` is made redundant by `type_eq_zero_of_empty`, while `zero_eq_lift_type_empty`  is made redundant by the former lemma and `lift_zero`.
#### Estimated changes
modified src/order/rel_iso.lean
- \+ *def* rel_iso_of_is_empty

modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* type_eq_zero_of_empty
- \- *theorem* type_eq_zero_iff_is_empty
- \- *theorem* type_ne_zero_iff_nonempty

modified src/set_theory/ordinal/basic.lean
- \+ *theorem* type_eq_zero_of_empty
- \+ *theorem* type_eq_zero_iff_is_empty
- \+ *theorem* type_ne_zero_iff_nonempty
- \+ *theorem* type_ne_zero_of_nonempty
- \- *theorem* zero_eq_type_empty
- \- *theorem* zero_eq_lift_type_empty



## [2022-06-09 23:59:52](https://github.com/leanprover-community/mathlib/commit/2cf4746)
chore(analysis/special_functions/gamma): tidy some proofs ([#14615](https://github.com/leanprover-community/mathlib/pull/14615))
#### Estimated changes
modified src/analysis/special_functions/gamma.lean



## [2022-06-09 23:59:51](https://github.com/leanprover-community/mathlib/commit/3afb1fa)
feat(ci): Add support for "notice"-level messages ([#14443](https://github.com/leanprover-community/mathlib/pull/14443))
It looks like support for this was added recently, it's now documented at the same link already in our source code.
#### Estimated changes
modified scripts/detect_errors.py



## [2022-06-09 22:24:53](https://github.com/leanprover-community/mathlib/commit/6e13617)
feat(set_theory/ordinal/basic): better definitions for `0` and `1` ([#14651](https://github.com/leanprover-community/mathlib/pull/14651))
We define the `0` and `1` ordinals as the order types of the empty relation on `pempty` and `punit`, respectively. These definitions are definitionally equal to the previous ones, yet much clearer, for two reasons:
- They don't make use of the auxiliary `Well_order` type. 
- Much of the basic API for these ordinals uses this def-eq anyways.
#### Estimated changes
modified src/set_theory/ordinal/basic.lean



## [2022-06-09 22:24:52](https://github.com/leanprover-community/mathlib/commit/c89d319)
feat(set_theory/cardinal): add `cardinal.aleph_0_le_mul_iff'` ([#14648](https://github.com/leanprover-community/mathlib/pull/14648))
This version provides a more useful `iff.mpr`. Also review 2 proofs.
#### Estimated changes
modified src/set_theory/cardinal/basic.lean
- \+ *lemma* aleph_0_le_mul_iff'



## [2022-06-09 22:24:51](https://github.com/leanprover-community/mathlib/commit/405be36)
feat(data/matrix): Lemmas about `vec_mul`, `mul_vec`, `dot_product`, `inv` ([#14644](https://github.com/leanprover-community/mathlib/pull/14644))
#### Estimated changes
modified src/data/matrix/basic.lean
- \+/\- *lemma* dot_product_assoc
- \+ *lemma* sum_elim_dot_product_sum_elim
- \+ *lemma* sub_mul_vec
- \+ *lemma* vec_mul_sub
- \+ *lemma* mul_vec_vec_mul
- \+ *lemma* vec_mul_mul_vec
- \+/\- *lemma* dot_product_assoc

modified src/data/matrix/block.lean
- \+ *lemma* from_blocks_mul_vec
- \+ *lemma* vec_mul_from_blocks

modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *lemma* mul_nonsing_inv_cancel_right
- \+ *lemma* mul_nonsing_inv_cancel_left
- \+ *lemma* nonsing_inv_mul_cancel_right
- \+ *lemma* nonsing_inv_mul_cancel_left
- \+ *lemma* mul_inv_cancel_right_of_invertible
- \+ *lemma* mul_inv_cancel_left_of_invertible
- \+ *lemma* inv_mul_cancel_right_of_invertible
- \+ *lemma* inv_mul_cancel_left_of_invertible



## [2022-06-09 22:24:50](https://github.com/leanprover-community/mathlib/commit/3e458e2)
chore(topology/sequences): rename variables ([#14631](https://github.com/leanprover-community/mathlib/pull/14631))
* types `X`, `Y`;
* sequence `x : ℕ → X`;
* a point `a : X`;
* sets `s`, `t`.
#### Estimated changes
modified src/topology/sequences.lean
- \+/\- *lemma* subset_seq_closure
- \+/\- *lemma* is_seq_closed_of_def
- \+/\- *lemma* seq_closure_subset_closure
- \+/\- *lemma* is_closed.is_seq_closed
- \+/\- *lemma* is_seq_closed.mem_of_tendsto
- \+/\- *lemma* is_seq_closed_iff_is_closed
- \+/\- *lemma* mem_closure_iff_seq_limit
- \+/\- *lemma* continuous_iff_seq_continuous
- \+/\- *lemma* is_seq_compact.subseq_of_frequently_in
- \+/\- *lemma* seq_compact_space.tendsto_subseq
- \+/\- *lemma* is_compact.is_seq_compact
- \+/\- *lemma* is_compact.tendsto_subseq'
- \+/\- *lemma* is_compact.tendsto_subseq
- \+/\- *lemma* compact_space.tendsto_subseq
- \+/\- *lemma* lebesgue_number_lemma_seq
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space
- \+/\- *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+/\- *lemma* tendsto_subseq_of_bounded
- \+/\- *lemma* subset_seq_closure
- \+/\- *lemma* is_seq_closed_of_def
- \+/\- *lemma* seq_closure_subset_closure
- \+/\- *lemma* is_closed.is_seq_closed
- \+/\- *lemma* is_seq_closed.mem_of_tendsto
- \+/\- *lemma* is_seq_closed_iff_is_closed
- \+/\- *lemma* mem_closure_iff_seq_limit
- \+/\- *lemma* continuous_iff_seq_continuous
- \+/\- *lemma* is_seq_compact.subseq_of_frequently_in
- \+/\- *lemma* seq_compact_space.tendsto_subseq
- \+/\- *lemma* is_compact.is_seq_compact
- \+/\- *lemma* is_compact.tendsto_subseq'
- \+/\- *lemma* is_compact.tendsto_subseq
- \+/\- *lemma* compact_space.tendsto_subseq
- \+/\- *lemma* lebesgue_number_lemma_seq
- \+/\- *lemma* uniform_space.compact_space_iff_seq_compact_space
- \+/\- *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+/\- *lemma* tendsto_subseq_of_bounded
- \+/\- *def* seq_closure
- \+/\- *def* is_seq_closed
- \+/\- *def* seq_continuous
- \+/\- *def* is_seq_compact
- \+/\- *def* seq_closure
- \+/\- *def* is_seq_closed
- \+/\- *def* seq_continuous
- \+/\- *def* is_seq_compact



## [2022-06-09 19:45:28](https://github.com/leanprover-community/mathlib/commit/81ab992)
chore(set_theory/cardinal/basic): tidy lt_wf proof ([#14574](https://github.com/leanprover-community/mathlib/pull/14574))
#### Estimated changes
modified src/set_theory/cardinal/basic.lean



## [2022-06-09 19:45:27](https://github.com/leanprover-community/mathlib/commit/34a9d0d)
feat(algebra/order/ring): Binary rearrangement inequality ([#14478](https://github.com/leanprover-community/mathlib/pull/14478))
Extract the binary case of the rearrangement inequality (`a * d + b * c ≤ a * c + b * d` if `a ≤ b` and `c ≤ d`) from the general one.
#### Estimated changes
modified src/algebra/order/module.lean
- \+ *lemma* smul_add_smul_le_smul_add_smul
- \+ *lemma* smul_add_smul_le_smul_add_smul'
- \+ *lemma* smul_add_smul_lt_smul_add_smul
- \+ *lemma* smul_add_smul_lt_smul_add_smul'

modified src/algebra/order/rearrangement.lean

modified src/algebra/order/ring.lean
- \+ *lemma* mul_add_mul_le_mul_add_mul
- \+ *lemma* mul_add_mul_le_mul_add_mul'
- \+ *lemma* mul_add_mul_lt_mul_add_mul
- \+ *lemma* mul_add_mul_lt_mul_add_mul'



## [2022-06-09 19:45:25](https://github.com/leanprover-community/mathlib/commit/7fbff0f)
feat(data/nat/choose/central): arity of primes in central binomial coefficients ([#14017](https://github.com/leanprover-community/mathlib/pull/14017))
Spun off of [#8002](https://github.com/leanprover-community/mathlib/pull/8002). Lemmas about the arity of primes in central binomial coefficients.
#### Estimated changes
modified docs/references.bib

modified src/data/nat/choose/central.lean
- \- *lemma* padic_val_nat_central_binom_le
- \- *lemma* padic_val_nat_central_binom_of_large_le_one
- \- *lemma* padic_val_nat_central_binom_of_large_eq_zero

created src/data/nat/choose/factorization.lean
- \+ *lemma* factorization_choose_le_log
- \+ *lemma* pow_factorization_choose_le
- \+ *lemma* factorization_choose_le_one
- \+ *lemma* factorization_choose_of_lt_three_mul
- \+ *lemma* factorization_central_binom_of_two_mul_self_lt_three_mul
- \+ *lemma* factorization_factorial_eq_zero_of_lt
- \+ *lemma* factorization_choose_eq_zero_of_lt
- \+ *lemma* factorization_central_binom_eq_zero_of_two_mul_lt
- \+ *lemma* le_two_mul_of_factorization_central_binom_pos

modified src/data/nat/factorization/basic.lean
- \+ *lemma* factorization_eq_zero_of_lt



## [2022-06-09 18:12:47](https://github.com/leanprover-community/mathlib/commit/4d4de43)
chore(ring_theory/unique_factorization_domain): drop simp annotation for factors_pow ([#14646](https://github.com/leanprover-community/mathlib/pull/14646))
Followup to https://github.com/leanprover-community/mathlib/pull/14555.
#### Estimated changes
modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* factors_pow
- \+/\- *lemma* factors_pow



## [2022-06-09 18:12:46](https://github.com/leanprover-community/mathlib/commit/7b4680f)
feat(analysis/inner_product_space/pi_L2): Distance formula in the euclidean space ([#14642](https://github.com/leanprover-community/mathlib/pull/14642))
A few missing results about `pi_Lp 2` and `euclidean_space`.
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.dist_eq
- \+ *lemma* euclidean_space.nndist_eq
- \+ *lemma* euclidean_space.edist_eq

modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* dist_eq_of_L2
- \+ *lemma* nndist_eq_of_L2
- \+ *lemma* edist_eq_of_L2



## [2022-06-09 18:12:45](https://github.com/leanprover-community/mathlib/commit/ac0ce64)
feat(special_functions/integrals): exponential of complex multiple of x ([#14623](https://github.com/leanprover-community/mathlib/pull/14623))
We add an integral for `exp (c * x)` for `c` complex (so this cannot be reduced to integration of `exp x` on the real line). This is useful for Fourier series.
#### Estimated changes
modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_exp_mul_complex



## [2022-06-09 15:38:27](https://github.com/leanprover-community/mathlib/commit/abee649)
feat(data/set/intervals): add lemmas about unions of intervals ([#14636](https://github.com/leanprover-community/mathlib/pull/14636))
#### Estimated changes
modified src/data/set/intervals/disjoint.lean
- \+ *lemma* Union_Iic
- \+ *lemma* Union_Ici
- \+ *lemma* Union_Icc_right
- \+ *lemma* Union_Ioc_right
- \+ *lemma* Union_Icc_left
- \+ *lemma* Union_Ico_left
- \+ *lemma* Union_Iio
- \+ *lemma* Union_Ioi
- \+ *lemma* Union_Ico_right
- \+ *lemma* Union_Ioo_right
- \+ *lemma* Union_Ioc_left
- \+ *lemma* Union_Ioo_left

modified src/data/set/lattice.lean
- \+ *theorem* Inter_union



## [2022-06-09 15:38:26](https://github.com/leanprover-community/mathlib/commit/e0f3ea3)
feat(topology/constructions): add `subtype.dense_iff` ([#14632](https://github.com/leanprover-community/mathlib/pull/14632))
Also add `inducing.dense_iff`.
#### Estimated changes
modified src/topology/constructions.lean
- \+ *lemma* subtype.dense_iff

modified src/topology/maps.lean
- \+ *lemma* inducing.dense_iff



## [2022-06-09 15:38:25](https://github.com/leanprover-community/mathlib/commit/48f557d)
chore(analysis/convex/integral): use `variables` ([#14592](https://github.com/leanprover-community/mathlib/pull/14592))
* Move some implicit arguments to `variables`.
* Move `ae_eq_const_or_exists_average_ne_compl` to the root namespace.
* Add `ae_eq_const_or_norm_set_integral_lt_of_norm_le_const`.
#### Estimated changes
modified src/analysis/convex/integral.lean
- \+/\- *lemma* convex.integral_mem
- \+/\- *lemma* convex.average_mem
- \+/\- *lemma* convex.set_average_mem
- \+/\- *lemma* convex.set_average_mem_closure
- \+/\- *lemma* convex_on.average_mem_epigraph
- \+/\- *lemma* concave_on.average_mem_hypograph
- \+/\- *lemma* convex_on.map_average_le
- \+/\- *lemma* concave_on.le_map_average
- \+/\- *lemma* convex_on.set_average_mem_epigraph
- \+/\- *lemma* concave_on.set_average_mem_hypograph
- \+/\- *lemma* convex_on.map_set_average_le
- \+/\- *lemma* concave_on.le_map_set_average
- \+/\- *lemma* convex_on.map_integral_le
- \+/\- *lemma* concave_on.le_map_integral
- \+ *lemma* ae_eq_const_or_exists_average_ne_compl
- \+/\- *lemma* convex.average_mem_interior_of_set
- \+/\- *lemma* strict_convex.ae_eq_const_or_average_mem_interior
- \+/\- *lemma* strict_convex_on.ae_eq_const_or_map_average_lt
- \+/\- *lemma* strict_concave_on.ae_eq_const_or_lt_map_average
- \+ *lemma* ae_eq_const_or_norm_set_integral_lt_of_norm_le_const
- \+/\- *lemma* convex.integral_mem
- \+/\- *lemma* convex.average_mem
- \+/\- *lemma* convex.set_average_mem
- \+/\- *lemma* convex.set_average_mem_closure
- \+/\- *lemma* convex_on.average_mem_epigraph
- \+/\- *lemma* concave_on.average_mem_hypograph
- \+/\- *lemma* convex_on.map_average_le
- \+/\- *lemma* concave_on.le_map_average
- \+/\- *lemma* convex_on.set_average_mem_epigraph
- \+/\- *lemma* concave_on.set_average_mem_hypograph
- \+/\- *lemma* convex_on.map_set_average_le
- \+/\- *lemma* concave_on.le_map_set_average
- \+/\- *lemma* convex_on.map_integral_le
- \+/\- *lemma* concave_on.le_map_integral
- \- *lemma* measure_theory.integrable.ae_eq_const_or_exists_average_ne_compl
- \+/\- *lemma* convex.average_mem_interior_of_set
- \+/\- *lemma* strict_convex.ae_eq_const_or_average_mem_interior
- \+/\- *lemma* strict_convex_on.ae_eq_const_or_map_average_lt
- \+/\- *lemma* strict_concave_on.ae_eq_const_or_lt_map_average



## [2022-06-09 13:27:25](https://github.com/leanprover-community/mathlib/commit/c0b3ed7)
feat(number_theory/padics/padic_val): add `padic_val_nat_def'` and generalise `pow_padic_val_nat_dvd` ([#14637](https://github.com/leanprover-community/mathlib/pull/14637))
add `padic_val_nat_def' (hn : 0 < n) (hp : p ≠ 1) : ↑(padic_val_nat p n) = multiplicity p n`
`pow_padic_val_nat_dvd : p ^ (padic_val_nat p n) ∣ n` holds without the assumption that `p` is prime.
#### Estimated changes
modified src/number_theory/padics/padic_val.lean
- \+ *lemma* padic_val_nat_def'
- \+/\- *lemma* pow_padic_val_nat_dvd
- \+/\- *lemma* range_pow_padic_val_nat_subset_divisors
- \+/\- *lemma* pow_padic_val_nat_dvd
- \+/\- *lemma* range_pow_padic_val_nat_subset_divisors



## [2022-06-09 13:27:23](https://github.com/leanprover-community/mathlib/commit/dc766dd)
refactor(group_theory/sylow): Golf proof of `pow_dvd_card_of_pow_dvd_card` ([#14622](https://github.com/leanprover-community/mathlib/pull/14622))
This PR golfs the proof of `pow_dvd_card_of_pow_dvd_card`.
#### Estimated changes
modified src/group_theory/sylow.lean
- \+/\- *lemma* pow_dvd_card_of_pow_dvd_card
- \+/\- *lemma* pow_dvd_card_of_pow_dvd_card



## [2022-06-09 13:27:22](https://github.com/leanprover-community/mathlib/commit/cde6e63)
feat(analysis/seminorm): removed unnecessary `norm_one_class` arguments ([#14614](https://github.com/leanprover-community/mathlib/pull/14614))
#### Estimated changes
modified src/analysis/seminorm.lean
- \+/\- *lemma* nonneg
- \+/\- *lemma* sub_rev
- \+/\- *lemma* le_insert
- \+/\- *lemma* le_insert'
- \+/\- *lemma* balanced_ball_zero
- \+/\- *lemma* nonneg
- \+/\- *lemma* sub_rev
- \+/\- *lemma* le_insert
- \+/\- *lemma* le_insert'
- \+/\- *lemma* balanced_ball_zero



## [2022-06-09 13:27:21](https://github.com/leanprover-community/mathlib/commit/d997baa)
refactor(logic/equiv/basic): remove `fin_equiv_subtype` ([#14603](https://github.com/leanprover-community/mathlib/pull/14603))
The types `fin n` and `{m // m < n}` are definitionally equal, so it doesn't make sense to have a dedicated equivalence between them (other than `equiv.refl`). We remove this equivalence and golf the places where it was used.
#### Estimated changes
modified src/computability/primrec.lean

modified src/data/fintype/card.lean

modified src/field_theory/finite/polynomial.lean

modified src/logic/encodable/basic.lean

modified src/logic/equiv/basic.lean
- \- *def* fin_equiv_subtype



## [2022-06-09 13:27:20](https://github.com/leanprover-community/mathlib/commit/c2bb59e)
feat(algebra/module/torsion.lean): various lemmas about torsion modules ([#14573](https://github.com/leanprover-community/mathlib/pull/14573))
An intermediate PR for various lemmas about torsion modules needed at [#13524](https://github.com/leanprover-community/mathlib/pull/13524)
#### Estimated changes
modified src/algebra/module/torsion.lean
- \+ *lemma* sup_eq_top_iff_is_coprime
- \+/\- *lemma* is_torsion_by_singleton_iff
- \+/\- *lemma* is_torsion_by_set_iff_torsion_by_set_eq_top
- \+/\- *lemma* is_torsion_by_iff_torsion_by_eq_top
- \+/\- *lemma* is_torsion_by_set_iff_is_torsion_by_span
- \+/\- *lemma* is_torsion_by_span_singleton_iff
- \+/\- *lemma* torsion_by_set_is_torsion_by_set
- \+/\- *lemma* torsion_by_is_torsion_by
- \+/\- *lemma* torsion_by_torsion_by_eq_top
- \+/\- *lemma* torsion_by_set_torsion_by_set_eq_top
- \+ *lemma* torsion_gc
- \+ *lemma* supr_torsion_by_ideal_eq_torsion_by_infi
- \+ *lemma* sup_indep_torsion_by_ideal
- \+/\- *lemma* supr_torsion_by_eq_torsion_by_prod
- \+ *lemma* sup_indep_torsion_by
- \+ *lemma* torsion_by_set_is_internal
- \+ *lemma* torsion_by_is_internal
- \+ *lemma* is_torsion_by_ideal_of_finite_of_is_torsion
- \+/\- *lemma* is_torsion'_powers_iff
- \+ *lemma* pow_p_order_smul
- \+ *lemma* exists_is_torsion_by
- \+/\- *lemma* is_torsion_by_singleton_iff
- \+/\- *lemma* is_torsion_by_set_iff_torsion_by_set_eq_top
- \+/\- *lemma* is_torsion_by_iff_torsion_by_eq_top
- \+/\- *lemma* torsion_by_set_is_torsion_by_set
- \+/\- *lemma* torsion_by_is_torsion_by
- \+/\- *lemma* torsion_by_torsion_by_eq_top
- \+/\- *lemma* torsion_by_set_torsion_by_set_eq_top
- \+/\- *lemma* is_torsion_by_set_iff_is_torsion_by_span
- \+/\- *lemma* is_torsion_by_span_singleton_iff
- \+/\- *lemma* supr_torsion_by_eq_torsion_by_prod
- \- *lemma* torsion_by_independent
- \- *lemma* torsion_is_internal
- \+/\- *lemma* is_torsion'_powers_iff
- \+ *def* p_order

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* prod_mem_prod



## [2022-06-09 13:27:19](https://github.com/leanprover-community/mathlib/commit/dfc54a3)
feat(combinatorics/ballot): the Ballot problem ([#13592](https://github.com/leanprover-community/mathlib/pull/13592))
#### Estimated changes
created archive/100-theorems-list/30_ballot_problem.lean
- \+ *lemma* stays_positive_nil
- \+ *lemma* stays_positive_cons_pos
- \+ *lemma* counted_right_zero
- \+ *lemma* counted_left_zero
- \+ *lemma* counted_ne_nil_left
- \+ *lemma* counted_ne_nil_right
- \+ *lemma* counted_succ_succ
- \+ *lemma* counted_sequence_finite
- \+ *lemma* counted_sequence_nonempty
- \+ *lemma* sum_of_mem_counted_sequence
- \+ *lemma* mem_of_mem_counted_sequence
- \+ *lemma* length_of_mem_counted_sequence
- \+ *lemma* disjoint_bits
- \+ *lemma* count_counted_sequence
- \+ *lemma* first_vote_pos
- \+ *lemma* head_mem_of_nonempty
- \+ *lemma* first_vote_neg
- \+ *lemma* ballot_same
- \+ *lemma* ballot_edge
- \+ *lemma* counted_sequence_int_pos_counted_succ_succ
- \+ *lemma* ballot_pos
- \+ *lemma* counted_sequence_int_neg_counted_succ_succ
- \+ *lemma* ballot_neg
- \+ *theorem* ballot_problem'
- \+ *theorem* ballot_problem
- \+ *def* stays_positive
- \+ *def* counted_sequence

modified docs/100.yaml

modified src/data/list/infix.lean
- \+ *lemma* mem_of_mem_suffix

modified src/data/nat/basic.lean
- \+ *lemma* diag_induction

modified src/data/real/ennreal.lean
- \+ *lemma* eq_div_iff
- \+ *lemma* div_eq_div_iff

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* count_injective_image

modified src/probability/cond_count.lean
- \+/\- *lemma* cond_count_compl
- \+/\- *lemma* cond_count_add_compl_eq
- \+/\- *lemma* cond_count_compl
- \+/\- *lemma* cond_count_add_compl_eq



## [2022-06-09 11:44:36](https://github.com/leanprover-community/mathlib/commit/d51aacb)
feat(ring_theory/unique_factorization_domain): add some lemmas about … ([#14555](https://github.com/leanprover-community/mathlib/pull/14555))
#### Estimated changes
modified src/algebra/associated.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factors_zero
- \+ *lemma* factors_one
- \+ *lemma* factors_mul
- \+ *lemma* factors_pow



## [2022-06-09 09:58:31](https://github.com/leanprover-community/mathlib/commit/dc2f6bb)
chore(topology/metric_space): remove instances that duplicate lemmas ([#14639](https://github.com/leanprover-community/mathlib/pull/14639))
We can use the structure projections directly as instances, rather than duplicating them with primed names. This removes;
* `metric_space.to_uniform_space'` (was misnamed, now `pseudo_metric_space.to_uniform_space`)
* `pseudo_metric_space.to_bornology'` (now `pseudo_metric_space.to_bornology`)
* `pseudo_emetric_space.to_uniform_space'` (now `pseudo_metric_space.to_uniform_space`)
* `emetric_space.to_uniform_space'` (redundant)
Follows up from review comments in [#13927](https://github.com/leanprover-community/mathlib/pull/13927)
#### Estimated changes
modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/uniform_space/compare_reals.lean



## [2022-06-09 09:58:30](https://github.com/leanprover-community/mathlib/commit/bc7b342)
feat(topology/metric_space/basic): add lemma `exists_lt_mem_ball_of_mem_ball` ([#14627](https://github.com/leanprover-community/mathlib/pull/14627))
This is apparently necessary in https://github.com/leanprover-community/mathlib/pull/13885
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+ *lemma* exists_lt_mem_ball_of_mem_ball



## [2022-06-09 09:58:29](https://github.com/leanprover-community/mathlib/commit/6a1ce4e)
feat(analysis/seminorm): add a `zero_hom_class` instance and remove `seminorm.zero` ([#14613](https://github.com/leanprover-community/mathlib/pull/14613))
#### Estimated changes
modified src/analysis/locally_convex/with_seminorms.lean

modified src/analysis/seminorm.lean



## [2022-06-09 09:58:28](https://github.com/leanprover-community/mathlib/commit/6826bf0)
doc(data/vector3): improve wording ([#14610](https://github.com/leanprover-community/mathlib/pull/14610))
#### Estimated changes
modified src/data/vector3.lean



## [2022-06-09 09:58:27](https://github.com/leanprover-community/mathlib/commit/ab64f63)
refactor(algebra/sub{monoid,group,ring,semiring,field}): merge together the `restrict` and `cod_restrict` helpers ([#14548](https://github.com/leanprover-community/mathlib/pull/14548))
This uses the new subobject typeclasses to merge together:
* `monoid_hom.mrestrict`, `monoid_hom.restrict`
* `monoid_hom.cod_mrestrict`, `monoid_hom.cod_restrict`
* `ring_hom.srestrict`, `ring_hom.restrict`, `ring_hom.restrict_field`
* `ring_hom.cod_srestrict`, `ring_hom.cod_restrict`, `ring_hom.cod_restrict_field`
For consistency, this also removes the `m` prefix from `mul_hom.mrestrict`
#### Estimated changes
modified src/algebra/algebra/subalgebra/basic.lean

modified src/algebra/category/Ring/constructions.lean

modified src/field_theory/subfield.lean
- \- *lemma* restrict_field_apply
- \- *def* cod_restrict_field
- \- *def* restrict_field

modified src/group_theory/free_product.lean

modified src/group_theory/monoid_localization.lean

modified src/group_theory/subgroup/basic.lean
- \- *lemma* restrict_apply
- \- *lemma* cod_restrict_apply
- \- *def* restrict
- \- *def* cod_restrict

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* restrict_apply
- \- *lemma* mrestrict_apply
- \+ *def* restrict
- \+ *def* cod_restrict
- \- *def* mrestrict
- \- *def* cod_mrestrict

modified src/group_theory/subsemigroup/operations.lean
- \+ *lemma* restrict_apply
- \- *lemma* srestrict_apply
- \+ *def* restrict
- \+ *def* cod_restrict
- \- *def* srestrict
- \- *def* cod_srestrict

modified src/ring_theory/localization/basic.lean

modified src/ring_theory/subring/basic.lean
- \- *lemma* restrict_apply
- \- *def* cod_restrict'
- \- *def* restrict

modified src/ring_theory/subsemiring/basic.lean
- \+ *lemma* restrict_apply
- \- *lemma* srestrict_apply
- \+ *def* restrict
- \+ *def* cod_restrict
- \- *def* srestrict
- \- *def* cod_srestrict



## [2022-06-09 09:58:26](https://github.com/leanprover-community/mathlib/commit/732b79f)
feat(order/compactly_generated): an independent subset of a well-founded complete lattice is finite ([#14215](https://github.com/leanprover-community/mathlib/pull/14215))
#### Estimated changes
modified src/order/compactly_generated.lean
- \+ *lemma* well_founded.finite_of_set_independent



## [2022-06-09 07:52:18](https://github.com/leanprover-community/mathlib/commit/3a95d1d)
feat(algebra/order/monoid): `zero_le_one_class` instances for `with_top` and `with_bot` ([#14640](https://github.com/leanprover-community/mathlib/pull/14640))
#### Estimated changes
modified src/algebra/order/monoid.lean



## [2022-06-09 05:43:16](https://github.com/leanprover-community/mathlib/commit/971a9b0)
feat(logic/equiv/basic): two empty types are equivalent; remove various redundant lemmas ([#14604](https://github.com/leanprover-community/mathlib/pull/14604))
We prove `equiv_of_is_empty`, which states two empty types are equivalent. This allows us to remove various redundant lemmas.
We keep `empty_equiv_empty` and `empty_equiv_pempty` as these specific instantiations of that lemma are widely used.
#### Estimated changes
modified src/logic/equiv/basic.lean
- \+ *def* equiv_of_is_empty
- \+ *def* equiv_pempty
- \- *def* false_equiv_empty
- \- *def* {u'
- \- *def* false_equiv_pempty
- \- *def* empty_equiv_pempty
- \- *def* pempty_equiv_pempty

modified src/set_theory/ordinal/basic.lean



## [2022-06-09 04:07:37](https://github.com/leanprover-community/mathlib/commit/9f19686)
feat(logic/small): generalize + golf ([#14584](https://github.com/leanprover-community/mathlib/pull/14584))
This PR does the following:
- add a lemma `small_lift`
- generalize the lemma `small_ulift`
- golf `small_self` and `small_max`
#### Estimated changes
modified src/logic/small.lean
- \+/\- *theorem* small_map
- \+ *theorem* small_lift
- \+/\- *theorem* small_map



## [2022-06-09 01:54:18](https://github.com/leanprover-community/mathlib/commit/b392bb2)
feat(data/nat/factorization/basic): two trivial simp lemmas about factorizations ([#14634](https://github.com/leanprover-community/mathlib/pull/14634))
For any `n : ℕ`, `n.factorization 0 = 0` and `n.factorization 1 = 0`
#### Estimated changes
modified src/data/nat/factorization/basic.lean
- \+ *lemma* factorization_zero_right
- \+ *lemma* factorization_one_right



## [2022-06-09 01:54:16](https://github.com/leanprover-community/mathlib/commit/4fc3539)
refactor(data/finset/nat_antidiagonal): state lemmas with cons instead of insert ([#14533](https://github.com/leanprover-community/mathlib/pull/14533))
This puts less of a burden on the caller rewriting in the forward direction, as they don't have to prove obvious things about membership when evaluating sums.
Since this adds the missing `finset.map_cons`, a number of uses of `multiset.map_cons` now need qualified names.
#### Estimated changes
modified src/algebra/big_operators/nat_antidiagonal.lean

modified src/algebra/polynomial/big_operators.lean

modified src/data/finset/basic.lean
- \+ *lemma* map_cons

modified src/data/finset/fold.lean

modified src/data/finset/nat_antidiagonal.lean
- \+/\- *lemma* antidiagonal_succ
- \+/\- *lemma* antidiagonal_succ'
- \+/\- *lemma* antidiagonal_succ
- \+/\- *lemma* antidiagonal_succ'



## [2022-06-08 23:44:35](https://github.com/leanprover-community/mathlib/commit/0c08bd4)
chore(data/set/basic): minor style fixes ([#14628](https://github.com/leanprover-community/mathlib/pull/14628))
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *lemma* set_of_app_iff
- \+/\- *lemma* set_of_app_iff
- \+/\- *theorem* set_coe_cast
- \+/\- *theorem* set_coe_cast



## [2022-06-08 20:36:43](https://github.com/leanprover-community/mathlib/commit/c1faa2e)
feat(linear_algebra/affine_space/affine_subspace/pointwise): Translations are an action on affine subspaces ([#14230](https://github.com/leanprover-community/mathlib/pull/14230))
#### Estimated changes
modified src/linear_algebra/affine_space/affine_equiv.lean
- \+/\- *lemma* coe_refl
- \+ *lemma* coe_refl_to_affine_map
- \+/\- *lemma* refl_apply
- \+/\- *lemma* to_equiv_refl
- \+/\- *lemma* linear_refl
- \+/\- *lemma* coe_refl
- \+/\- *lemma* refl_apply
- \+/\- *lemma* to_equiv_refl
- \+/\- *lemma* linear_refl
- \+/\- *def* refl
- \+/\- *def* refl

modified src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* span_eq_top_iff
- \- *lemma* affine_equiv.span_eq_top_iff

created src/linear_algebra/affine_space/pointwise.lean
- \+ *lemma* coe_pointwise_vadd
- \+ *lemma* vadd_mem_pointwise_vadd_iff
- \+ *lemma* pointwise_vadd_bot
- \+ *lemma* pointwise_vadd_direction
- \+ *lemma* pointwise_vadd_span
- \+ *lemma* map_pointwise_vadd



## [2022-06-08 20:36:42](https://github.com/leanprover-community/mathlib/commit/84a1bd6)
refactor(topology/metric_space/basic): add `pseudo_metric_space.to_bornology'` ([#13927](https://github.com/leanprover-community/mathlib/pull/13927))
* add `pseudo_metric_space.to_bornology'` and `pseudo_metric_space.replace_bornology`;
* add `metric.is_bounded_iff` and a few similar lemmas;
* fix instances for `subtype`, `prod`, `pi`, and `pi_Lp` to use the correct bornology`;
* add `lipschitz_with.to_locally_bounded_map` and `lipschitz_with.comap_cobounded_le`;
* add `antilipschitz_with.tendsto_cobounded`.
#### Estimated changes
modified src/analysis/normed_space/enorm.lean
- \+/\- *def* emetric_space
- \+/\- *def* emetric_space

modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* aux_cobounded_eq
- \+ *def* pseudo_metric_aux

modified src/topology/metric_space/antilipschitz.lean
- \+ *lemma* tendsto_cobounded

modified src/topology/metric_space/basic.lean
- \+ *lemma* pseudo_metric_space.replace_bornology_eq
- \+ *theorem* is_bounded_iff
- \+ *theorem* is_bounded_iff_eventually
- \+ *theorem* is_bounded_iff_exists_ge
- \+ *theorem* is_bounded_iff_nndist
- \+ *def* pseudo_metric_space.replace_bornology

modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* coe_to_locally_bounded_map
- \+ *lemma* comap_cobounded_le
- \+ *def* to_locally_bounded_map



## [2022-06-08 18:51:48](https://github.com/leanprover-community/mathlib/commit/61df9c6)
feat(set_theory/ordinal/basic): tweak `type_def` + golf `type_lt` ([#14611](https://github.com/leanprover-community/mathlib/pull/14611))
We replace the original, redundant `type_def'` with a new more general lemma. We keep `type_def` as it enables `dsimp`, unlike `type_def'`. We golf `type_lt` using this new lemma.
#### Estimated changes
modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* type_def'
- \+/\- *theorem* type_def
- \+/\- *theorem* type_def
- \+/\- *theorem* type_def'



## [2022-06-08 18:51:32](https://github.com/leanprover-community/mathlib/commit/9c4a3d1)
feat(ring_theory/valuation/valuation_subring): define unit group of valuation subring and provide basic API ([#14540](https://github.com/leanprover-community/mathlib/pull/14540))
This PR defines the unit group of a valuation subring as a multiplicative subgroup of the units of the field. We show two valuation subrings are equivalent iff they have the same unit group. We show the map sending a valuation to its unit group is an order embedding.
#### Estimated changes
modified src/ring_theory/valuation/basic.lean
- \+ *lemma* map_one_add_of_lt
- \+ *lemma* map_one_sub_of_lt

modified src/ring_theory/valuation/valuation_subring.lean
- \+ *lemma* mem_unit_group_iff
- \+ *lemma* unit_group_injective
- \+ *lemma* eq_iff_unit_group
- \+ *lemma* coe_unit_group_mul_equiv_apply
- \+ *lemma* coe_unit_group_mul_equiv_symm_apply
- \+ *lemma* unit_group_le_unit_group
- \+ *lemma* unit_group_strict_mono
- \+ *def* unit_group
- \+ *def* unit_group_mul_equiv
- \+ *def* unit_group_order_embedding



## [2022-06-08 18:10:02](https://github.com/leanprover-community/mathlib/commit/d315666)
feat(model_theory/substructures): tweak universes for `lift_card_closure_le` ([#14597](https://github.com/leanprover-community/mathlib/pull/14597))
Since `cardinal.lift.{(max u v) u} = cardinal.lift.{v u}`, the latter form should be preferred.
#### Estimated changes
modified src/model_theory/substructures.lean
- \+/\- *theorem* lift_card_closure_le
- \+/\- *theorem* lift_card_closure_le



## [2022-06-08 15:58:47](https://github.com/leanprover-community/mathlib/commit/8934884)
feat(set_theory/ordinal/basic): `rel_iso.ordinal_type_eq` ([#14602](https://github.com/leanprover-community/mathlib/pull/14602))
#### Estimated changes
modified src/set_theory/ordinal/basic.lean
- \+ *theorem* _root_.rel_iso.ordinal_type_eq



## [2022-06-08 15:58:46](https://github.com/leanprover-community/mathlib/commit/09df85f)
feat(order/rel_classes): any relation on an empty type is a well-order ([#14600](https://github.com/leanprover-community/mathlib/pull/14600))
#### Estimated changes
modified src/logic/is_empty.lean
- \+ *lemma* well_founded_of_empty

modified src/order/rel_classes.lean



## [2022-06-08 15:58:45](https://github.com/leanprover-community/mathlib/commit/201a3f4)
chore(*): remove extra parentheses in universe annotations ([#14595](https://github.com/leanprover-community/mathlib/pull/14595))
We change `f.{(max u v)}` to `f.{max u v}` throughout, and similarly for `imax`. This is for consistency with the rest of the code.
Note that `max` and `imax` take an arbitrary number of parameters, so if anyone wants to add a second universe parameter, they'll have to add the parentheses again.
#### Estimated changes
modified src/algebra/category/Module/projective.lean

modified src/category_theory/category/ulift.lean

modified src/category_theory/graded_object.lean

modified src/linear_algebra/dimension.lean

modified src/set_theory/cardinal/basic.lean

modified src/set_theory/cardinal/cofinality.lean

modified src/set_theory/cardinal/ordinal.lean

modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* lift_lift
- \+/\- *theorem* lift_lift

modified src/testing/slim_check/functions.lean



## [2022-06-08 15:58:43](https://github.com/leanprover-community/mathlib/commit/3e4d6aa)
feat(algebra/algebra/basic): add instances `char_zero.no_zero_smul_divisors_int`, `char_zero.no_zero_smul_divisors_nat` ([#14395](https://github.com/leanprover-community/mathlib/pull/14395))
The proofs are taken from [#14338](https://github.com/leanprover-community/mathlib/pull/14338) where a specific need for these arose
Aside from the new instances, nothing else has changed; I moved the
`no_zero_smul_divisors` section lower down in the file since the new
instances need the `algebra ℤ R` structure carried by a ring `R`.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+/\- *lemma* of_algebra_map_injective
- \+/\- *lemma* algebra_map_injective
- \+/\- *lemma* iff_algebra_map_injective
- \+/\- *lemma* of_algebra_map_injective
- \+/\- *lemma* algebra_map_injective
- \+/\- *lemma* iff_algebra_map_injective



## [2022-06-08 13:42:41](https://github.com/leanprover-community/mathlib/commit/bfb8ec8)
feat(logic/basic): add lemma `pi_congr` ([#14616](https://github.com/leanprover-community/mathlib/pull/14616))
This lemma is used in [#14153](https://github.com/leanprover-community/mathlib/pull/14153), where `congrm` is defined.
A big reason for splitting these 3 lines off the main PR is that they are the only ones that are not in a leaf of the import hierarchy: this hopefully saves lots of CI time, when doing trivial changes to the main PR.
#### Estimated changes
modified src/logic/basic.lean
- \+ *lemma* pi_congr



## [2022-06-08 13:42:38](https://github.com/leanprover-community/mathlib/commit/700181a)
refactor(algebra/is_prime_pow): move lemmas using `factorization` to new file ([#14598](https://github.com/leanprover-community/mathlib/pull/14598))
As discussed in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization/near/285144241).
#### Estimated changes
modified src/algebra/is_prime_pow.lean
- \- *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \- *lemma* is_prime_pow_iff_factorization_eq_single
- \- *lemma* is_prime_pow_iff_card_support_factorization_eq_one
- \- *lemma* is_prime_pow_iff_unique_prime_dvd
- \- *lemma* is_prime_pow_pow_iff
- \- *lemma* nat.coprime.is_prime_pow_dvd_mul
- \- *lemma* nat.mul_divisors_filter_prime_pow

renamed src/data/nat/factorization.lean to src/data/nat/factorization/basic.lean

created src/data/nat/factorization/prime_pow.lean
- \+ *lemma* is_prime_pow.min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_of_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_min_fac_pow_factorization_eq
- \+ *lemma* is_prime_pow_iff_factorization_eq_single
- \+ *lemma* is_prime_pow_iff_card_support_factorization_eq_one
- \+ *lemma* is_prime_pow_iff_unique_prime_dvd
- \+ *lemma* is_prime_pow_pow_iff
- \+ *lemma* nat.coprime.is_prime_pow_dvd_mul
- \+ *lemma* nat.mul_divisors_filter_prime_pow

modified src/data/nat/squarefree.lean

modified src/field_theory/cardinality.lean

modified src/group_theory/nilpotent.lean

modified src/group_theory/sylow.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/padics/padic_val.lean

modified src/ring_theory/multiplicity.lean



## [2022-06-08 12:10:16](https://github.com/leanprover-community/mathlib/commit/db4531f)
doc(data/qpf/multivariate/constructions/cofix): fix doc typos ([#14609](https://github.com/leanprover-community/mathlib/pull/14609))
#### Estimated changes
modified src/data/qpf/multivariate/constructions/cofix.lean



## [2022-06-08 12:10:15](https://github.com/leanprover-community/mathlib/commit/0add876)
chore(set_theory/cardinal/basic): remove unused universe + fix spacing ([#14606](https://github.com/leanprover-community/mathlib/pull/14606))
#### Estimated changes
modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* mk_subtype_mono
- \+/\- *lemma* mk_subtype_mono



## [2022-06-08 12:10:14](https://github.com/leanprover-community/mathlib/commit/65fba4c)
feat(algebra/lie/centralizer): define the centralizer of a Lie submodule and the upper central series ([#14173](https://github.com/leanprover-community/mathlib/pull/14173))
#### Estimated changes
modified src/algebra/lie/cartan_subalgebra.lean
- \- *lemma* mem_normalizer_iff
- \- *lemma* mem_normalizer_iff'
- \- *lemma* le_normalizer
- \- *lemma* lie_mem_sup_of_mem_normalizer
- \- *lemma* ideal_in_normalizer
- \- *lemma* exists_nested_lie_ideal_of_le_normalizer
- \- *lemma* le_normalizer_of_ideal
- \- *lemma* normalizer_eq_self_iff
- \- *def* normalizer

created src/algebra/lie/centralizer.lean
- \+ *lemma* mem_centralizer
- \+ *lemma* le_centralizer
- \+ *lemma* centralizer_inf
- \+ *lemma* monotone_centalizer
- \+ *lemma* comap_centralizer
- \+ *lemma* top_lie_le_iff_le_centralizer
- \+ *lemma* gc_top_lie_centralizer
- \+ *lemma* centralizer_bot_eq_max_triv_submodule
- \+ *lemma* mem_normalizer_iff'
- \+ *lemma* mem_normalizer_iff
- \+ *lemma* le_normalizer
- \+ *lemma* coe_centralizer_eq_normalizer
- \+ *lemma* lie_mem_sup_of_mem_normalizer
- \+ *lemma* ideal_in_normalizer
- \+ *lemma* exists_nested_lie_ideal_of_le_normalizer
- \+ *lemma* normalizer_eq_self_iff
- \+ *def* centralizer
- \+ *def* normalizer

modified src/algebra/lie/engel.lean

modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_le_iff

modified src/algebra/lie/nilpotent.lean
- \+ *lemma* is_nilpotent_iff
- \+ *lemma* ucs_zero
- \+ *lemma* ucs_succ
- \+ *lemma* ucs_mono
- \+ *lemma* ucs_eq_self_of_centralizer_eq_self
- \+ *lemma* ucs_le_of_centralizer_eq_self
- \+ *lemma* lcs_add_le_iff
- \+ *lemma* lcs_le_iff
- \+ *lemma* gc_lcs_ucs
- \+ *lemma* ucs_eq_top_iff
- \+ *lemma* _root_.lie_module.is_nilpotent_iff_exists_ucs_eq_top
- \+ *lemma* ucs_comap_incl
- \+ *lemma* is_nilpotent_iff_exists_self_le_ucs
- \+ *def* ucs

modified src/algebra/lie/submodule.lean
- \+ *lemma* comap_incl_eq_top



## [2022-06-08 09:31:34](https://github.com/leanprover-community/mathlib/commit/ffad43d)
golf(*): `λ _, default` → `default` ([#14608](https://github.com/leanprover-community/mathlib/pull/14608))
#### Estimated changes
modified src/computability/turing_machine.lean

modified src/data/array/lemmas.lean

modified src/data/finset/basic.lean

modified src/data/holor.lean
- \+/\- *def* holor_index
- \+/\- *def* holor
- \+/\- *def* holor_index
- \+/\- *def* holor

modified src/data/pfunctor/multivariate/basic.lean

modified src/data/pfunctor/univariate/M.lean

modified src/data/pfunctor/univariate/basic.lean

modified src/data/prod/tprod.lean

modified src/data/qpf/multivariate/constructions/sigma.lean

modified src/data/setoid/partition.lean

modified src/data/vector/basic.lean

modified src/group_theory/sylow.lean

modified src/logic/basic.lean

modified src/logic/embedding.lean

modified src/logic/equiv/basic.lean

modified src/logic/unique.lean

modified src/measure_theory/covering/besicovitch.lean

modified src/order/jordan_holder.lean

modified src/order/omega_complete_partial_order.lean

modified src/topology/continuous_function/basic.lean

modified src/topology/vector_bundle/basic.lean

modified test/lint_coe_t.lean
- \+/\- *def* int_to_a
- \+/\- *def* int_to_a



## [2022-06-08 09:31:33](https://github.com/leanprover-community/mathlib/commit/60454dd)
feat(algebra/order/monoid): `zero_le_one'` lemma with explicit type argument ([#14594](https://github.com/leanprover-community/mathlib/pull/14594))
#### Estimated changes
modified src/algebra/geom_sum.lean

modified src/algebra/order/monoid.lean
- \+/\- *lemma* zero_le_one
- \+ *lemma* zero_le_one'
- \+/\- *lemma* zero_le_one

modified src/analysis/specific_limits/basic.lean

modified src/data/int/basic.lean

modified src/topology/algebra/order/floor.lean

modified src/topology/homotopy/basic.lean

modified src/topology/path_connected.lean



## [2022-06-08 09:31:32](https://github.com/leanprover-community/mathlib/commit/f40cd3c)
feat(topology/algebra/order/basic): in a second-countable linear order, only countably many points are isolated to the right ([#14564](https://github.com/leanprover-community/mathlib/pull/14564))
This makes it possible to remove a useless `densely_ordered` assumption in a lemma in `borel_space`.
#### Estimated changes
modified src/data/set/basic.lean
- \- *def* unique_empty

modified src/data/set/countable.lean
- \+ *lemma* countable.of_subsingleton

modified src/data/set/finite.lean
- \+ *lemma* finite.of_subsingleton

modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi_aux
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi_aux
- \+/\- *lemma* measurable_set_of_mem_nhds_within_Ioi

modified src/measure_theory/integral/set_to_l1.lean

modified src/topology/algebra/order/basic.lean
- \+ *lemma* countable_of_isolated_right
- \+ *lemma* countable_of_isolated_left
- \+ *lemma* set.pairwise_disjoint.countable_of_Ioo

modified src/topology/separation.lean
- \+ *lemma* topological_space.is_topological_basis.exists_mem_of_ne



## [2022-06-08 09:31:31](https://github.com/leanprover-community/mathlib/commit/a20032a)
feat(group_theory/sylow): The index of a sylow subgroup is indivisible by the prime ([#14518](https://github.com/leanprover-community/mathlib/pull/14518))
This PR adds a lemma stating that the index of a sylow subgroup is indivisible by the prime.
#### Estimated changes
modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.stabilizer_eq_normalizer
- \+ *lemma* not_dvd_index_sylow'
- \+ *lemma* not_dvd_index_sylow
- \+/\- *lemma* sylow.stabilizer_eq_normalizer
- \+/\- *def* comap_of_injective
- \+/\- *def* comap_of_injective



## [2022-06-08 09:31:30](https://github.com/leanprover-community/mathlib/commit/54236f5)
feat(topology/continuous_function/compact): `cstar_ring` instance on `C(α, β)` when `α` is compact ([#14437](https://github.com/leanprover-community/mathlib/pull/14437))
We define the star operation on `C(α, β)` by applying `β`'s star operation pointwise. In the case when `α` is compact, then `C(α, β)` has a norm, and we show that it is a `cstar_ring`.
#### Estimated changes
modified src/topology/algebra/star.lean
- \+ *def* star_continuous_map

modified src/topology/continuous_function/algebra.lean
- \+ *lemma* coe_star
- \+ *lemma* star_apply

modified src/topology/continuous_function/compact.lean
- \+ *lemma* _root_.bounded_continuous_function.mk_of_compact_star



## [2022-06-08 07:33:27](https://github.com/leanprover-community/mathlib/commit/e39af18)
chore(data/finset): remove duplicated lemma ([#14607](https://github.com/leanprover-community/mathlib/pull/14607))
The lemma `ssubset_iff_exists_insert_subset` was added in [#11248](https://github.com/leanprover-community/mathlib/pull/11248) but is just a duplicate of the `ssubset_iff` lemma a few lines earlier in the file. It's only used once.
#### Estimated changes
modified src/combinatorics/set_family/lym.lean

modified src/data/finset/basic.lean
- \- *lemma* ssubset_iff_exists_insert_subset



## [2022-06-08 00:23:16](https://github.com/leanprover-community/mathlib/commit/9d04844)
feat(data/int/basic): Sum of units casework lemma ([#14557](https://github.com/leanprover-community/mathlib/pull/14557))
This PR adds a casework lemma for when the sum of two units equals the sum of two units. I needed this lemma for irreducibility of x^n-x-1.
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* is_unit_add_is_unit_eq_is_unit_add_is_unit



## [2022-06-07 22:31:45](https://github.com/leanprover-community/mathlib/commit/759516c)
chore(ring_theory/dedekind_domain/ideal): speed up a proof ([#14590](https://github.com/leanprover-community/mathlib/pull/14590))
... which causes recurring timeout at irrelevant places, see https://github.com/leanprover-community/mathlib/pull/14585#issuecomment-1148222373 and referenced Zulip discussion.
Feel free to push golfs that remains fast (1-2s)!
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean



## [2022-06-07 21:09:01](https://github.com/leanprover-community/mathlib/commit/905374c)
feat(special_functions/gamma): better convergence bounds ([#14496](https://github.com/leanprover-community/mathlib/pull/14496))
Use the stronger form of FTC-2 added [#14147](https://github.com/leanprover-community/mathlib/pull/14147) to strengthen some results about the gamma function.
#### Estimated changes
modified src/analysis/special_functions/gamma.lean
- \+/\- *lemma* Gamma_integral_convergent
- \+/\- *lemma* Gamma_integral_convergent
- \+/\- *lemma* tendsto_partial_Gamma
- \+/\- *lemma* partial_Gamma_add_one
- \+/\- *lemma* Gamma_aux_recurrence1
- \+/\- *lemma* Gamma_aux_recurrence2
- \+/\- *lemma* Gamma_eq_Gamma_aux
- \+/\- *lemma* Gamma_integral_convergent
- \+/\- *lemma* Gamma_integral_convergent
- \+/\- *lemma* tendsto_partial_Gamma
- \+/\- *lemma* partial_Gamma_add_one
- \+/\- *lemma* Gamma_aux_recurrence1
- \+/\- *lemma* Gamma_aux_recurrence2
- \+/\- *lemma* Gamma_eq_Gamma_aux
- \+/\- *theorem* Gamma_integral_add_one
- \+/\- *theorem* Gamma_eq_integral
- \+/\- *theorem* Gamma_integral_add_one
- \+/\- *theorem* Gamma_eq_integral
- \+/\- *def* Gamma
- \+/\- *def* Gamma



## [2022-06-07 17:43:24](https://github.com/leanprover-community/mathlib/commit/cfa447e)
chore(logic/hydra): tweak docs + minor golf ([#14579](https://github.com/leanprover-community/mathlib/pull/14579))
#### Estimated changes
modified src/logic/hydra.lean



## [2022-06-07 13:32:20](https://github.com/leanprover-community/mathlib/commit/43f1af9)
refactor(topology/continuous_function/basic): rename `map_specialization` ([#14565](https://github.com/leanprover-community/mathlib/pull/14565))
Rename `continuous_map.map_specialization` to `continuous_map.map_specializes` to align with the name of the relation.
#### Estimated changes
modified src/algebraic_geometry/stalks.lean

modified src/topology/continuous_function/basic.lean
- \+ *lemma* map_specializes
- \- *lemma* map_specialization

modified src/topology/sheaves/stalks.lean



## [2022-06-07 12:37:21](https://github.com/leanprover-community/mathlib/commit/544fdc0)
chore(ring_theory/integral_closure): fix dot notation ([#14589](https://github.com/leanprover-community/mathlib/pull/14589))
#### Estimated changes
modified src/number_theory/function_field.lean

modified src/number_theory/number_field.lean

modified src/ring_theory/integral_closure.lean
- \+ *lemma* algebra.is_integral.is_field_iff_is_field
- \- *lemma* is_integral.is_field_iff_is_field



## [2022-06-07 11:40:32](https://github.com/leanprover-community/mathlib/commit/6906627)
refactor(algebra/squarefree): split out `nat` part to new file `data/nat/squarefree` ([#14577](https://github.com/leanprover-community/mathlib/pull/14577))
As discussed in this Zulip [thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/squarefree.2C.20is_prime_pow.2C.20and.20factorization)
#### Estimated changes
modified archive/100-theorems-list/81_sum_of_prime_reciprocals_diverges.lean

modified src/algebra/squarefree.lean
- \- *lemma* squarefree_iff_nodup_factors
- \- *lemma* squarefree.factorization_le_one
- \- *lemma* squarefree_of_factorization_le_one
- \- *lemma* squarefree_iff_factorization_le_one
- \- *lemma* squarefree.ext_iff
- \- *lemma* squarefree_pow_iff
- \- *lemma* squarefree_and_prime_pow_iff_prime
- \- *lemma* squarefree_iff_min_sq_fac
- \- *lemma* divisors_filter_squarefree
- \- *lemma* sum_divisors_filter_squarefree
- \- *lemma* sq_mul_squarefree_of_pos
- \- *lemma* sq_mul_squarefree_of_pos'
- \- *lemma* sq_mul_squarefree
- \- *lemma* squarefree_mul
- \- *lemma* squarefree_bit10
- \- *lemma* squarefree_bit1
- \- *lemma* squarefree_helper_0
- \- *lemma* squarefree_helper_1
- \- *lemma* squarefree_helper_2
- \- *lemma* squarefree_helper_3
- \- *lemma* squarefree_helper_4
- \- *lemma* not_squarefree_mul
- \- *theorem* squarefree_iff_prime_squarefree
- \- *theorem* min_sq_fac_prop_div
- \- *theorem* min_sq_fac_aux_has_prop
- \- *theorem* min_sq_fac_has_prop
- \- *theorem* min_sq_fac_prime
- \- *theorem* min_sq_fac_dvd
- \- *theorem* min_sq_fac_le_of_dvd
- \- *theorem* squarefree_two
- \- *def* min_sq_fac_aux
- \- *def* min_sq_fac
- \- *def* min_sq_fac_prop
- \- *def* squarefree_helper

created src/data/nat/squarefree.lean
- \+ *lemma* squarefree_iff_nodup_factors
- \+ *lemma* squarefree.factorization_le_one
- \+ *lemma* squarefree_of_factorization_le_one
- \+ *lemma* squarefree_iff_factorization_le_one
- \+ *lemma* squarefree.ext_iff
- \+ *lemma* squarefree_pow_iff
- \+ *lemma* squarefree_and_prime_pow_iff_prime
- \+ *lemma* squarefree_iff_min_sq_fac
- \+ *lemma* divisors_filter_squarefree
- \+ *lemma* sum_divisors_filter_squarefree
- \+ *lemma* sq_mul_squarefree_of_pos
- \+ *lemma* sq_mul_squarefree_of_pos'
- \+ *lemma* sq_mul_squarefree
- \+ *lemma* squarefree_mul
- \+ *lemma* squarefree_bit10
- \+ *lemma* squarefree_bit1
- \+ *lemma* squarefree_helper_0
- \+ *lemma* squarefree_helper_1
- \+ *lemma* squarefree_helper_2
- \+ *lemma* squarefree_helper_3
- \+ *lemma* squarefree_helper_4
- \+ *lemma* not_squarefree_mul
- \+ *theorem* squarefree_iff_prime_squarefree
- \+ *theorem* min_sq_fac_prop_div
- \+ *theorem* min_sq_fac_aux_has_prop
- \+ *theorem* min_sq_fac_has_prop
- \+ *theorem* min_sq_fac_prime
- \+ *theorem* min_sq_fac_dvd
- \+ *theorem* min_sq_fac_le_of_dvd
- \+ *theorem* squarefree_two
- \+ *def* min_sq_fac_aux
- \+ *def* min_sq_fac
- \+ *def* min_sq_fac_prop
- \+ *def* squarefree_helper

modified src/number_theory/arithmetic_function.lean

modified test/norm_num_ext.lean



## [2022-06-07 07:06:14](https://github.com/leanprover-community/mathlib/commit/4a4cd6d)
feat(topology/metric_space/metrizable): assume `regular_space` ([#14586](https://github.com/leanprover-community/mathlib/pull/14586))
#### Estimated changes
modified src/topology/metric_space/metrizable.lean
- \+ *lemma* metrizable_space_of_regular_second_countable
- \- *lemma* metrizable_space_of_normal_second_countable



## [2022-06-07 01:29:01](https://github.com/leanprover-community/mathlib/commit/de648fd)
chore(set_theory/game/basic): spacing tweaks + fix docstring typo ([#14580](https://github.com/leanprover-community/mathlib/pull/14580))
#### Estimated changes
modified src/set_theory/game/basic.lean
- \+/\- *def* to_left_moves_mul
- \+/\- *def* to_right_moves_mul
- \+/\- *def* to_left_moves_mul
- \+/\- *def* to_right_moves_mul



## [2022-06-06 22:44:27](https://github.com/leanprover-community/mathlib/commit/6ad1a55)
feat(set_theory/game/pgame): induction on left/right moves of add/mul ([#14345](https://github.com/leanprover-community/mathlib/pull/14345))
#### Estimated changes
modified src/set_theory/game/basic.lean
- \+/\- *lemma* left_moves_mul_cases
- \+/\- *lemma* right_moves_mul_cases
- \+/\- *lemma* left_moves_mul_cases
- \+/\- *lemma* right_moves_mul_cases

modified src/set_theory/game/impartial.lean

modified src/set_theory/game/nim.lean

modified src/set_theory/game/pgame.lean
- \+/\- *lemma* left_moves_add_cases
- \+/\- *lemma* right_moves_add_cases
- \+/\- *lemma* left_moves_add_cases
- \+/\- *lemma* right_moves_add_cases



## [2022-06-06 20:46:31](https://github.com/leanprover-community/mathlib/commit/c7a1319)
feat(measure_theory/measure/measure_space): add `interval_oc_ae_eq_interval` ([#14566](https://github.com/leanprover-community/mathlib/pull/14566))
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* interval_oc_ae_eq_interval



## [2022-06-06 20:46:30](https://github.com/leanprover-community/mathlib/commit/2c89306)
chore(geometry/manifold/charted_space): make `M` an explicit argument ([#14562](https://github.com/leanprover-community/mathlib/pull/14562))
#### Estimated changes
modified src/geometry/manifold/charted_space.lean
- \+/\- *lemma* charted_space.locally_compact
- \+/\- *lemma* charted_space.locally_compact

modified src/geometry/manifold/partition_of_unity.lean



## [2022-06-06 20:46:29](https://github.com/leanprover-community/mathlib/commit/d0b7ecc)
refactor(analysis/asymptotics): rename `is_O.join` to `is_O.sup` ([#14558](https://github.com/leanprover-community/mathlib/pull/14558))
* rename `is_*.join` to `is_*.sup`;
* add `iff` versions.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* is_O_sup
- \+ *lemma* is_o_sup
- \+ *theorem* is_O_with.sup
- \+ *theorem* is_O_with.sup'
- \+ *theorem* is_O.sup
- \+ *theorem* is_o.sup
- \- *theorem* is_O_with.join
- \- *theorem* is_O_with.join'
- \- *theorem* is_O.join
- \- *theorem* is_o.join

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/complex/phragmen_lindelof.lean



## [2022-06-06 20:46:28](https://github.com/leanprover-community/mathlib/commit/2b7e72b)
feat(order/liminf_limsup): add a few lemmas ([#14554](https://github.com/leanprover-community/mathlib/pull/14554))
* add `is_bounded_under.mono_le`, `is_bounded_under.mono_ge`;
* add `order_iso.is_bounded_under_le_comp`, `order_iso.is_bounded_under_ge_comp`;
* add `is_bounded_under_le_inv`, `is_bounded_under_le_inv`, and additive versions;
* rename `is_bounded_under_sup` and `is_bounded_under_inf` to `is_bounded_under.sup` and `is_bounded_under.inf`;
* add `iff` versions under names `is_bounded_under_le_sup` and `is_bounded_under_ge_inf`;
* add `is_bounded_under_le_abs`.
#### Estimated changes
modified src/order/liminf_limsup.lean
- \+ *lemma* is_bounded_under.mono_le
- \+ *lemma* is_bounded_under.mono_ge
- \+ *lemma* _root_.order_iso.is_bounded_under_le_comp
- \+ *lemma* _root_.order_iso.is_bounded_under_ge_comp
- \+ *lemma* is_bounded_under_le_inv
- \+ *lemma* is_bounded_under_ge_inv
- \+ *lemma* is_bounded_under.sup
- \+ *lemma* is_bounded_under_le_sup
- \+ *lemma* is_bounded_under.inf
- \+ *lemma* is_bounded_under_ge_inf
- \+ *lemma* is_bounded_under_le_abs
- \- *lemma* is_bounded_under_sup
- \- *lemma* is_bounded_under_inf



## [2022-06-06 20:46:27](https://github.com/leanprover-community/mathlib/commit/029a955)
refactor(../metric_space/baire): add baire_space class and instances ([#14547](https://github.com/leanprover-community/mathlib/pull/14547))
* Add a `baire_space` class containing the Baire property (a countable intersection of open dense sets is dense).
* The Baire category theorem for complete metric spaces becomes an instance of `baire_space`.
* Previous consequences of the Baire property use `baire_space` as an hypothesis, instead of `pseudo_emetric_space` `complete_space`.
* Add an instance of `baire_space` for locally compact t2 spaces, in effect extending all the consequences of the Baire property to locally compact spaces.
#### Estimated changes
modified src/topology/metric_space/baire.lean
- \+/\- *lemma* mem_residual
- \+/\- *lemma* dense_of_mem_residual
- \+/\- *lemma* mem_residual
- \+/\- *lemma* dense_of_mem_residual
- \+/\- *theorem* dense_Inter_of_open_nat
- \+/\- *theorem* dense_Inter_of_open_nat

modified src/topology/sets/compacts.lean
- \+ *lemma* _root_.exists_positive_compacts_subset



## [2022-06-06 20:46:26](https://github.com/leanprover-community/mathlib/commit/d28aa2c)
feat(analysis/normed_space/banach): closed graph theorem ([#14265](https://github.com/leanprover-community/mathlib/pull/14265))
#### Estimated changes
modified src/analysis/normed_space/banach.lean
- \+ *lemma* coe_fn_of_is_closed_graph
- \+ *lemma* coe_of_is_closed_graph
- \+ *lemma* coe_fn_of_seq_closed_graph
- \+ *lemma* coe_of_seq_closed_graph
- \+ *theorem* linear_map.continuous_of_is_closed_graph
- \+ *theorem* linear_map.continuous_of_seq_closed_graph
- \+ *def* of_is_closed_graph
- \+ *def* of_seq_closed_graph



## [2022-06-06 18:41:09](https://github.com/leanprover-community/mathlib/commit/7b7da89)
feat(algebra/order/*): typeclass for `0 ≤ 1` ([#14510](https://github.com/leanprover-community/mathlib/pull/14510))
With this new typeclass, lemmas such as `zero_le_two` and `one_le_two` can be generalized to require just a few typeclasses for notation, `zero_add_class`, and some `covariant` class.
#### Estimated changes
modified counterexamples/canonically_ordered_comm_semiring_two_mul.lean
- \- *lemma* zero_le_one

modified src/algebra/geom_sum.lean

modified src/algebra/group_power/lemmas.lean

modified src/algebra/order/monoid.lean
- \+ *lemma* zero_le_one
- \+ *lemma* zero_le_two
- \+ *lemma* one_le_two
- \+ *lemma* one_le_two'

modified src/algebra/order/ring.lean
- \- *lemma* zero_le_one
- \- *lemma* zero_le_two
- \- *lemma* one_le_two

modified src/algebra/order/with_zero.lean
- \- *lemma* zero_le_one'

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/special_functions/pow.lean

modified src/analysis/special_functions/trigonometric/inverse.lean

modified src/analysis/specific_limits/basic.lean

modified src/category_theory/preadditive/schur.lean

modified src/data/int/basic.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/probability/strong_law.lean

modified src/ring_theory/valuation/integers.lean

modified src/set_theory/game/pgame.lean
- \- *theorem* zero_le_one

modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* zero_le_one

modified src/topology/algebra/order/floor.lean

modified src/topology/homotopy/basic.lean

modified src/topology/path_connected.lean



## [2022-06-06 14:27:28](https://github.com/leanprover-community/mathlib/commit/abbc7f6)
feat(measure_theory/measure/finite_measure_weak_convergence): Prove one implication of portmanteau theorem, convergence implies a limsup condition for measures of closed sets. ([#14116](https://github.com/leanprover-community/mathlib/pull/14116))
This PR contains the proof of one implication of portmanteau theorem characterizing weak convergence: it is shown that weak convergence implies that for any closed set the limsup of measures is at most the limit measure.
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* set_lintegral_const_lt_top
- \+ *lemma* lintegral_const_lt_top

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_le_lintegral_thickened_indicator_aux
- \+ *lemma* measure_le_lintegral_thickened_indicator

modified src/measure_theory/measure/finite_measure_weak_convergence.lean
- \+ *lemma* tendsto_lintegral_nn_filter_of_le_const
- \+ *lemma* tendsto_lintegral_nn_of_le_const
- \+ *lemma* tendsto_test_against_nn_filter_of_le_const
- \+ *lemma* tendsto_test_against_nn_of_le_const
- \+ *lemma* measure_of_cont_bdd_of_tendsto_filter_indicator
- \+ *lemma* measure_of_cont_bdd_of_tendsto_indicator
- \+ *lemma* tendsto_lintegral_thickened_indicator_of_is_closed
- \+ *lemma* finite_measure.limsup_measure_closed_le_of_tendsto

modified src/topology/metric_space/thickened_indicator.lean
- \+ *lemma* indicator_le_thickened_indicator_aux
- \+ *lemma* indicator_le_thickened_indicator



## [2022-06-06 13:48:54](https://github.com/leanprover-community/mathlib/commit/d6477a8)
feat(analysis/convex/krein_milman): The Krein-Milman theorem ([#8112](https://github.com/leanprover-community/mathlib/pull/8112))
This PR proves the Krein-Milman lemma and the Krein-Milman theorem.
#### Estimated changes
modified src/analysis/convex/exposed.lean

created src/analysis/convex/krein_milman.lean
- \+ *lemma* is_compact.has_extreme_point
- \+ *lemma* closure_convex_hull_extreme_points



## [2022-06-06 12:19:21](https://github.com/leanprover-community/mathlib/commit/d490ad1)
move(set_theory/ordinal/cantor_normal_form): move `CNF` to a new file ([#14563](https://github.com/leanprover-community/mathlib/pull/14563))
We move the API for the Cantor Normal Form to a new file, in preparation for an API expansion.
#### Estimated changes
modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* CNF_rec_zero
- \- *theorem* CNF_rec_ne_zero
- \- *theorem* zero_CNF
- \- *theorem* CNF_zero
- \- *theorem* CNF_ne_zero
- \- *theorem* one_CNF
- \- *theorem* CNF_foldr
- \- *theorem* CNF_pairwise
- \- *theorem* CNF_fst_le_log
- \- *theorem* CNF_fst_le
- \- *theorem* CNF_snd_lt
- \- *theorem* CNF_lt_snd
- \- *theorem* CNF_sorted
- \- *def* CNF

created src/set_theory/ordinal/cantor_normal_form.lean
- \+ *theorem* CNF_rec_zero
- \+ *theorem* CNF_rec_ne_zero
- \+ *theorem* zero_CNF
- \+ *theorem* CNF_zero
- \+ *theorem* CNF_ne_zero
- \+ *theorem* one_CNF
- \+ *theorem* CNF_foldr
- \+ *theorem* CNF_pairwise
- \+ *theorem* CNF_fst_le_log
- \+ *theorem* CNF_fst_le
- \+ *theorem* CNF_snd_lt
- \+ *theorem* CNF_lt_snd
- \+ *theorem* CNF_sorted
- \+ *def* CNF



## [2022-06-06 10:35:42](https://github.com/leanprover-community/mathlib/commit/0f5ea39)
feat(order/antichain, order/minimal): some antichain lemmas ([#14507](https://github.com/leanprover-community/mathlib/pull/14507))
This PR adds a few lemmas about antichains, including their images under complementation and order isomorphisms.
#### Estimated changes
modified src/order/antichain.lean
- \+ *lemma* image_rel_embedding
- \+ *lemma* preimage_rel_embedding
- \+ *lemma* image_rel_iso
- \+ *lemma* preimage_rel_iso
- \+ *lemma* image_rel_embedding_iff
- \+ *lemma* image_rel_iso_iff
- \+ *lemma* image_embedding
- \+ *lemma* preimage_embedding
- \+ *lemma* image_embedding_iff
- \+ *lemma* image_iso
- \+ *lemma* image_iso_iff
- \+ *lemma* preimage_iso
- \+ *lemma* preimage_iso_iff
- \+ *lemma* to_dual
- \+ *lemma* to_dual_iff
- \+ *lemma* image_compl
- \+ *lemma* preimage_compl

modified src/order/minimal.lean
- \+ *lemma* is_antichain.max_lower_set_of
- \+ *lemma* is_antichain.min_upper_set_of



## [2022-06-06 09:16:32](https://github.com/leanprover-community/mathlib/commit/d88ecd5)
chore(linear_algebra/std_basis): minor golfs ([#14552](https://github.com/leanprover-community/mathlib/pull/14552))
#### Estimated changes
modified src/linear_algebra/std_basis.lean



## [2022-06-06 07:26:33](https://github.com/leanprover-community/mathlib/commit/789af09)
feat(algebra/char_p): add two helper lemmas about the cast of the characteristics being zero ([#14464](https://github.com/leanprover-community/mathlib/pull/14464))
- `(ring_char R : R) = 0` and
- If there exists a positive `n` lifting to zero, then the characteristics is positive.
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* nat.cast_ring_char



## [2022-06-05 20:50:27](https://github.com/leanprover-community/mathlib/commit/769a934)
feat(set_theory/*) `cardinal.min` → `Inf` ([#13410](https://github.com/leanprover-community/mathlib/pull/13410))
We discard `cardinal.min` in favor of `Inf` (the original definition is really just `infi`). 
Note: `lift_min'` is renamed to `lift_min`, as the name clash no longer exists. For consistency, `lift_max'` is renamed to `lift_max` and `lift_max` is renamed to `lift_umax_eq`.
#### Estimated changes
modified src/linear_algebra/dimension.lean

modified src/model_theory/encoding.lean

modified src/model_theory/skolem.lean

modified src/set_theory/cardinal/basic.lean
- \+ *theorem* lift_strict_mono
- \+ *theorem* lift_monotone
- \+ *theorem* Inf_empty
- \+/\- *theorem* sup_eq_zero
- \+ *theorem* lift_Inf
- \+ *theorem* lift_umax_eq
- \+/\- *theorem* lift_min
- \+/\- *theorem* lift_max
- \- *theorem* min_eq
- \- *theorem* min_le
- \- *theorem* le_min
- \+/\- *theorem* sup_eq_zero
- \+/\- *theorem* lift_min
- \+/\- *theorem* lift_max
- \- *theorem* lift_min'
- \- *theorem* lift_max'

modified src/set_theory/cardinal/cofinality.lean
- \+/\- *lemma* cof_le
- \+/\- *lemma* cof_le
- \+ *theorem* cof_nonempty
- \+ *theorem* rel_iso.cof_le_lift
- \+ *theorem* rel_iso.cof_eq_lift
- \+ *theorem* rel_iso.cof_le
- \+ *theorem* rel_iso.cof_eq
- \+ *theorem* strict_order.cof_nonempty
- \+/\- *theorem* lift_cof
- \- *theorem* rel_iso.cof.aux
- \- *theorem* rel_iso.cof
- \+/\- *theorem* lift_cof
- \+/\- *def* cof
- \+/\- *def* strict_order.cof
- \+/\- *def* cof
- \+/\- *def* strict_order.cof

modified src/set_theory/cardinal/schroeder_bernstein.lean
- \+/\- *theorem* min_injective
- \+/\- *theorem* total
- \+/\- *theorem* min_injective
- \+/\- *theorem* total

modified src/set_theory/ordinal/basic.lean



## [2022-06-05 19:28:46](https://github.com/leanprover-community/mathlib/commit/736b4e5)
feat(data/nat/factorization): Lemma on zero-ness of factorization ([#14560](https://github.com/leanprover-community/mathlib/pull/14560))
Sad naming is sad.
[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/from-referrer/)
#### Estimated changes
modified src/data/nat/factorization.lean
- \+ *lemma* factorization_eq_zero_iff'



## [2022-06-05 14:52:20](https://github.com/leanprover-community/mathlib/commit/043fa29)
feat(src/analysis/normed_space): various improvements for continuous bilinear maps ([#14539](https://github.com/leanprover-community/mathlib/pull/14539))
* Add `simps` to `arrow_congrSL`
* `continuous_linear_map.flip (compSL F E H σ₂₁ σ₁₄)` takes almost 5 seconds to elaborate, but when giving the argument `(F →SL[σ₂₄] H)` for `G` explicitly, this goes down to 1 second.
* Reorder arguments of `is_bounded_bilinear_map_comp`
* Use `continuous_linear_map` results to prove `is_bounded_bilinear_map` results.
* Make arguments to `comp_continuous_multilinear_mapL` explicit
* Add `continuous[_on].clm_comp`, `cont_diff[_on].clm_comp` and `cont_diff.comp_cont_diff_on(₂|₃)`
#### Estimated changes
modified src/analysis/calculus/cont_diff.lean
- \+/\- *lemma* cont_diff_at.continuous_linear_map_comp
- \+/\- *lemma* cont_diff_on.continuous_linear_map_comp
- \+ *lemma* cont_diff.comp_cont_diff_on₂
- \+ *lemma* cont_diff.comp_cont_diff_on₃
- \+ *lemma* cont_diff.clm_comp
- \+ *lemma* cont_diff_on.clm_comp
- \+/\- *lemma* cont_diff_at.continuous_linear_map_comp
- \+/\- *lemma* cont_diff_on.continuous_linear_map_comp

modified src/analysis/calculus/fderiv.lean

modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous.clm_comp
- \+ *lemma* continuous_on.clm_comp

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* _root_.continuous.const_clm_comp
- \+ *lemma* _root_.continuous.clm_comp_const



## [2022-06-05 12:08:46](https://github.com/leanprover-community/mathlib/commit/d9e72ff)
feat(analysis/normed_space/hahn-banach/separation): Eidelheit's theorem ([#14460](https://github.com/leanprover-community/mathlib/pull/14460))
Prove Eidelheit's theorem as a corollary to the geometric Hahn-Banach.
#### Estimated changes
modified src/analysis/normed_space/hahn_banach/separation.lean
- \+ *lemma* Inter_halfspaces_eq



## [2022-06-05 07:36:59](https://github.com/leanprover-community/mathlib/commit/b6395b3)
refactor(set_theory/*): change `omega` to `aleph_0` + golf ([#14467](https://github.com/leanprover-community/mathlib/pull/14467))
This PR does two things:
- we change `cardinal.omega` to `cardinal.aleph_0` and introduce the notation `ℵ₀`.
- we golf many proofs throughout
#### Estimated changes
modified archive/100-theorems-list/82_cubing_a_cube.lean

modified src/algebra/algebraic_card.lean
- \+ *theorem* aleph_0_le_cardinal_mk_of_char_zero
- \+/\- *theorem* cardinal_mk_le_mul
- \+/\- *theorem* cardinal_mk_le_max
- \- *theorem* omega_le_cardinal_mk_of_char_zero
- \+/\- *theorem* cardinal_mk_le_mul
- \+/\- *theorem* cardinal_mk_le_max

modified src/algebra/quaternion.lean

modified src/analysis/complex/cauchy_integral.lean

modified src/computability/encoding.lean
- \+ *lemma* encoding.card_le_aleph_0
- \+ *lemma* fin_encoding.card_le_aleph_0
- \- *lemma* encoding.card_le_omega
- \- *lemma* fin_encoding.card_le_omega

modified src/data/W/cardinal.lean
- \+ *lemma* cardinal_mk_le_max_aleph_0_of_fintype
- \- *lemma* cardinal_mk_le_max_omega_of_fintype

modified src/data/complex/cardinality.lean

modified src/data/mv_polynomial/cardinal.lean

modified src/data/polynomial/cardinal.lean
- \+/\- *lemma* cardinal_mk_le_max
- \+/\- *lemma* cardinal_mk_le_max

modified src/data/rat/denumerable.lean
- \+ *lemma* cardinal.mk_rat
- \- *lemma* mk_rat

modified src/data/real/cardinality.lean

modified src/field_theory/cardinality.lean

modified src/field_theory/finite/polynomial.lean

modified src/field_theory/finiteness.lean
- \+ *lemma* iff_dim_lt_aleph_0
- \+ *lemma* dim_lt_aleph_0
- \- *lemma* iff_dim_lt_omega
- \- *lemma* dim_lt_omega

modified src/field_theory/fixed.lean

modified src/field_theory/is_alg_closed/classification.lean
- \+/\- *lemma* cardinal_mk_le_max
- \+ *lemma* cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt
- \+/\- *lemma* cardinal_mk_le_max
- \- *lemma* cardinal_eq_cardinal_transcendence_basis_of_omega_lt

modified src/group_theory/index.lean

modified src/group_theory/schur_zassenhaus.lean

modified src/linear_algebra/dimension.lean
- \+ *lemma* basis.nonempty_fintype_index_of_dim_lt_aleph_0
- \+ *lemma* basis.finite_index_of_dim_lt_aleph_0
- \+ *lemma* basis.finite_of_vector_space_index_of_dim_lt_aleph_0
- \- *lemma* basis.nonempty_fintype_index_of_dim_lt_omega
- \- *lemma* basis.finite_index_of_dim_lt_omega
- \- *lemma* basis.finite_of_vector_space_index_of_dim_lt_omega

modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* lt_aleph_0_of_linear_independent
- \- *lemma* lt_omega_of_linear_independent

modified src/linear_algebra/finsupp_vector_space.lean
- \+ *lemma* cardinal_lt_aleph_0_of_finite_dimensional
- \- *lemma* cardinal_lt_omega_of_finite_dimensional

modified src/linear_algebra/free_module/finite/rank.lean
- \+ *lemma* rank_lt_aleph_0
- \- *lemma* rank_lt_omega

modified src/measure_theory/card_measurable_space.lean

modified src/model_theory/basic.lean
- \+ *lemma* card_le_aleph_0
- \+ *lemma* card_functions_le_aleph_0
- \+/\- *lemma* encodable.countable
- \+/\- *lemma* encodable.countable_functions
- \- *lemma* card_le_omega
- \- *lemma* card_functions_le_omega
- \+/\- *lemma* encodable.countable
- \+/\- *lemma* encodable.countable_functions

modified src/model_theory/encoding.lean
- \+ *lemma* card_le_aleph_0
- \- *lemma* card_le_omega
- \+/\- *theorem* card_le
- \+/\- *theorem* card_sigma
- \+/\- *theorem* card_le
- \+/\- *theorem* card_sigma

modified src/model_theory/satisfiability.lean

modified src/model_theory/semantics.lean

modified src/model_theory/skolem.lean

modified src/model_theory/substructures.lean

modified src/ring_theory/localization/cardinality.lean

modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* mk_nat
- \+ *lemma* add_lt_aleph_0_iff
- \+ *lemma* aleph_0_le_add_iff
- \+ *lemma* nsmul_lt_aleph_0_iff
- \+ *lemma* nsmul_lt_aleph_0_iff_of_ne_zero
- \+ *lemma* mul_lt_aleph_0_iff
- \+ *lemma* aleph_0_le_mul_iff
- \+ *lemma* mul_lt_aleph_0_iff_of_ne_zero
- \+ *lemma* aleph_0_le_mk
- \+/\- *lemma* encodable_iff
- \+ *lemma* mk_le_aleph_0
- \+/\- *lemma* denumerable_iff
- \+/\- *lemma* mk_denumerable
- \+ *lemma* mk_set_le_aleph_0
- \+ *lemma* mk_subtype_le_aleph_0
- \+ *lemma* aleph_0_add_aleph_0
- \+ *lemma* aleph_0_mul_aleph_0
- \+ *lemma* add_le_aleph_0
- \+ *lemma* to_nat_apply_of_lt_aleph_0
- \+ *lemma* to_nat_apply_of_aleph_0_le
- \+ *lemma* cast_to_nat_of_lt_aleph_0
- \+ *lemma* cast_to_nat_of_aleph_0_le
- \+ *lemma* to_nat_le_iff_le_of_lt_aleph_0
- \+ *lemma* to_nat_lt_iff_lt_of_lt_aleph_0
- \+ *lemma* to_nat_le_of_le_of_lt_aleph_0
- \+ *lemma* to_nat_lt_of_lt_of_lt_aleph_0
- \+/\- *lemma* to_nat_cast
- \+/\- *lemma* mk_to_nat_of_infinite
- \+/\- *lemma* zero_to_nat
- \+/\- *lemma* one_to_nat
- \+ *lemma* to_nat_add_of_lt_aleph_0
- \+ *lemma* to_enat_apply_of_lt_aleph_0
- \+ *lemma* to_enat_apply_of_aleph_0_le
- \+/\- *lemma* to_enat_cast
- \+/\- *lemma* mk_to_enat_of_infinite
- \+/\- *lemma* mk_int
- \+/\- *lemma* mk_pnat
- \+ *lemma* finset_card_lt_aleph_0
- \+ *lemma* mk_union_le_aleph_0
- \+/\- *lemma* mk_nat
- \- *lemma* add_lt_omega_iff
- \- *lemma* omega_le_add_iff
- \- *lemma* nsmul_lt_omega_iff
- \- *lemma* nsmul_lt_omega_iff_of_ne_zero
- \- *lemma* mul_lt_omega_iff
- \- *lemma* omega_le_mul_iff
- \- *lemma* mul_lt_omega_iff_of_ne_zero
- \- *lemma* omega_le_mk
- \+/\- *lemma* encodable_iff
- \- *lemma* mk_le_omega
- \+/\- *lemma* denumerable_iff
- \+/\- *lemma* mk_denumerable
- \- *lemma* mk_set_le_omega
- \- *lemma* mk_subtype_le_omega
- \- *lemma* omega_add_omega
- \- *lemma* omega_mul_omega
- \- *lemma* add_le_omega
- \- *lemma* to_nat_apply_of_lt_omega
- \- *lemma* to_nat_apply_of_omega_le
- \- *lemma* cast_to_nat_of_lt_omega
- \- *lemma* cast_to_nat_of_omega_le
- \- *lemma* to_nat_le_iff_le_of_lt_omega
- \- *lemma* to_nat_lt_iff_lt_of_lt_omega
- \- *lemma* to_nat_le_of_le_of_lt_omega
- \- *lemma* to_nat_lt_of_lt_of_lt_omega
- \+/\- *lemma* to_nat_cast
- \+/\- *lemma* mk_to_nat_of_infinite
- \+/\- *lemma* zero_to_nat
- \+/\- *lemma* one_to_nat
- \- *lemma* to_nat_add_of_lt_omega
- \- *lemma* to_enat_apply_of_lt_omega
- \- *lemma* to_enat_apply_of_omega_le
- \+/\- *lemma* to_enat_cast
- \+/\- *lemma* mk_to_enat_of_infinite
- \+/\- *lemma* mk_int
- \+/\- *lemma* mk_pnat
- \- *lemma* finset_card_lt_omega
- \- *lemma* mk_union_le_omega
- \+ *theorem* aleph_0_ne_zero
- \+ *theorem* aleph_0_pos
- \+ *theorem* lift_aleph_0
- \+ *theorem* aleph_0_le_lift
- \+ *theorem* lift_le_aleph_0
- \+/\- *theorem* card_le_of_finset
- \+/\- *theorem* card_le_of
- \+ *theorem* nat_lt_aleph_0
- \+ *theorem* one_lt_aleph_0
- \+ *theorem* one_le_aleph_0
- \+ *theorem* lt_aleph_0
- \+ *theorem* aleph_0_le
- \+ *theorem* lt_aleph_0_iff_fintype
- \+ *theorem* lt_aleph_0_of_fintype
- \+ *theorem* lt_aleph_0_iff_finite
- \+ *theorem* add_lt_aleph_0
- \+ *theorem* mul_lt_aleph_0
- \+ *theorem* power_lt_aleph_0
- \+/\- *theorem* infinite_iff
- \- *theorem* omega_ne_zero
- \- *theorem* omega_pos
- \- *theorem* lift_omega
- \- *theorem* omega_le_lift
- \- *theorem* lift_le_omega
- \+/\- *theorem* card_le_of_finset
- \+/\- *theorem* card_le_of
- \- *theorem* nat_lt_omega
- \- *theorem* one_lt_omega
- \- *theorem* lt_omega
- \- *theorem* omega_le
- \- *theorem* lt_omega_iff_fintype
- \- *theorem* lt_omega_of_fintype
- \- *theorem* lt_omega_iff_finite
- \- *theorem* add_lt_omega
- \- *theorem* mul_lt_omega
- \- *theorem* power_lt_omega
- \+/\- *theorem* infinite_iff
- \+ *def* aleph_0
- \- *def* omega

modified src/set_theory/cardinal/cofinality.lean
- \+ *lemma* is_regular.aleph_0_le
- \- *lemma* is_regular.omega_le
- \+/\- *theorem* nfp_family_lt_ord_lift
- \+/\- *theorem* nfp_family_lt_ord
- \+/\- *theorem* nfp_bfamily_lt_ord_lift
- \+/\- *theorem* nfp_bfamily_lt_ord
- \+/\- *theorem* nfp_lt_ord
- \+ *theorem* aleph_0_le_cof
- \+/\- *theorem* cof_omega
- \+/\- *theorem* infinite_pigeonhole
- \+ *theorem* is_limit.aleph_0_le
- \+ *theorem* is_strong_limit_aleph_0
- \+ *theorem* is_limit_aleph_0
- \+ *theorem* is_regular_aleph_0
- \+/\- *theorem* is_regular_succ
- \+/\- *theorem* is_regular_aleph'_succ
- \+/\- *theorem* nfp_lt_ord_of_is_regular
- \+/\- *theorem* deriv_lt_ord
- \+/\- *theorem* is_inaccessible.mk
- \+/\- *theorem* lt_power_cof
- \+/\- *theorem* lt_cof_power
- \+/\- *theorem* nfp_family_lt_ord_lift
- \+/\- *theorem* nfp_family_lt_ord
- \+/\- *theorem* nfp_bfamily_lt_ord_lift
- \+/\- *theorem* nfp_bfamily_lt_ord
- \+/\- *theorem* nfp_lt_ord
- \- *theorem* omega_le_cof
- \+/\- *theorem* cof_omega
- \+/\- *theorem* infinite_pigeonhole
- \- *theorem* is_limit.omega_le
- \- *theorem* is_strong_limit_omega
- \- *theorem* is_limit_omega
- \- *theorem* is_regular_omega
- \+/\- *theorem* is_regular_succ
- \+/\- *theorem* is_regular_aleph'_succ
- \+/\- *theorem* nfp_lt_ord_of_is_regular
- \+/\- *theorem* deriv_lt_ord
- \+/\- *theorem* is_inaccessible.mk
- \+/\- *theorem* lt_power_cof
- \+/\- *theorem* lt_cof_power

modified src/set_theory/cardinal/continuum.lean
- \+ *lemma* two_power_aleph_0
- \+/\- *lemma* lift_continuum
- \+ *lemma* aleph_0_lt_continuum
- \+ *lemma* aleph_0_le_continuum
- \+/\- *lemma* nat_lt_continuum
- \+ *lemma* aleph_0_add_continuum
- \+ *lemma* continuum_add_aleph_0
- \+ *lemma* continuum_mul_aleph_0
- \+ *lemma* aleph_0_mul_continuum
- \+/\- *lemma* nat_mul_continuum
- \+/\- *lemma* continuum_mul_nat
- \+ *lemma* aleph_0_power_aleph_0
- \+ *lemma* nat_power_aleph_0
- \+ *lemma* continuum_power_aleph_0
- \- *lemma* two_power_omega
- \+/\- *lemma* lift_continuum
- \- *lemma* omega_lt_continuum
- \- *lemma* omega_le_continuum
- \+/\- *lemma* nat_lt_continuum
- \- *lemma* omega_add_continuum
- \- *lemma* continuum_add_omega
- \- *lemma* continuum_mul_omega
- \- *lemma* omega_mul_continuum
- \+/\- *lemma* nat_mul_continuum
- \+/\- *lemma* continuum_mul_nat
- \- *lemma* omega_power_omega
- \- *lemma* nat_power_omega
- \- *lemma* continuum_power_omega
- \+/\- *def* continuum
- \+/\- *def* continuum

modified src/set_theory/cardinal/divisibility.lean
- \+ *lemma* dvd_of_le_of_aleph_0_le
- \+ *lemma* prime_of_aleph_0_le
- \+ *lemma* not_irreducible_of_aleph_0_le
- \+/\- *lemma* is_prime_iff
- \+/\- *lemma* is_prime_pow_iff
- \- *lemma* dvd_of_le_of_omega_le
- \- *lemma* prime_of_omega_le
- \- *lemma* not_irreducible_of_omega_le
- \+/\- *lemma* is_prime_iff
- \+/\- *lemma* is_prime_pow_iff

modified src/set_theory/cardinal/ordinal.lean
- \+ *lemma* aleph_0_lt_aleph_one
- \+ *lemma* mul_le_max_of_aleph_0_le_left
- \+ *lemma* mul_eq_max_of_aleph_0_le_left
- \+ *lemma* mul_eq_max_of_aleph_0_le_right
- \+/\- *lemma* mul_eq_max'
- \+/\- *lemma* mul_eq_left
- \+/\- *lemma* mul_eq_right
- \+/\- *lemma* mul_eq_left_iff
- \+ *lemma* eq_of_add_eq_of_aleph_0_le
- \+/\- *lemma* add_eq_left
- \+/\- *lemma* add_eq_right
- \+/\- *lemma* add_eq_left_iff
- \+/\- *lemma* add_eq_right_iff
- \+/\- *lemma* add_one_eq
- \+/\- *lemma* power_self_eq
- \+/\- *lemma* power_eq_two_power
- \+/\- *lemma* nat_power_eq
- \+/\- *lemma* power_nat_le
- \+/\- *lemma* power_nat_eq
- \+/\- *lemma* power_nat_le_max
- \+ *lemma* powerlt_aleph_0
- \+ *lemma* powerlt_aleph_0_le
- \+/\- *lemma* bit1_le_bit0
- \+/\- *lemma* bit0_lt_bit1
- \- *lemma* omega_lt_aleph_one
- \- *lemma* mul_le_max_of_omega_le_left
- \- *lemma* mul_eq_max_of_omega_le_left
- \- *lemma* mul_eq_max_of_omega_le_right
- \+/\- *lemma* mul_eq_max'
- \+/\- *lemma* mul_eq_left
- \+/\- *lemma* mul_eq_right
- \+/\- *lemma* mul_eq_left_iff
- \- *lemma* eq_of_add_eq_of_omega_le
- \+/\- *lemma* add_eq_left
- \+/\- *lemma* add_eq_right
- \+/\- *lemma* add_eq_left_iff
- \+/\- *lemma* add_eq_right_iff
- \+/\- *lemma* add_one_eq
- \+/\- *lemma* power_self_eq
- \+/\- *lemma* power_eq_two_power
- \+/\- *lemma* nat_power_eq
- \+/\- *lemma* power_nat_le
- \+/\- *lemma* power_nat_eq
- \+/\- *lemma* power_nat_le_max
- \- *lemma* powerlt_omega
- \- *lemma* powerlt_omega_le
- \+/\- *lemma* bit1_le_bit0
- \+/\- *lemma* bit0_lt_bit1
- \- *lemma* one_le_one
- \+/\- *theorem* ord_is_limit
- \+/\- *theorem* type_cardinal
- \+/\- *theorem* aleph'_lt
- \+/\- *theorem* aleph'_le
- \+/\- *theorem* aleph'_aleph_idx
- \+/\- *theorem* aleph_idx_aleph'
- \+/\- *theorem* aleph'_succ
- \+/\- *theorem* aleph'_le_of_limit
- \+/\- *theorem* aleph'_omega
- \+/\- *theorem* aleph_lt
- \+/\- *theorem* aleph_le
- \+/\- *theorem* aleph_succ
- \+/\- *theorem* aleph_zero
- \+ *theorem* aleph_0_le_aleph'
- \+ *theorem* aleph_0_le_aleph
- \+/\- *theorem* exists_aleph
- \+ *theorem* succ_aleph_0
- \+/\- *theorem* ord_card_unbounded'
- \+/\- *theorem* eq_aleph_of_eq_card_ord
- \+/\- *theorem* mul_eq_self
- \+/\- *theorem* mul_eq_max
- \+ *theorem* aleph_0_mul_eq
- \+ *theorem* mul_aleph_0_eq
- \+ *theorem* aleph_0_mul_mk_eq
- \+ *theorem* mk_mul_aleph_0_eq
- \+ *theorem* aleph_0_mul_aleph
- \+ *theorem* aleph_mul_aleph_0
- \+/\- *theorem* mul_lt_of_lt
- \+/\- *theorem* mul_le_max
- \+/\- *theorem* add_eq_self
- \+/\- *theorem* add_eq_max
- \+/\- *theorem* add_eq_max'
- \+/\- *theorem* add_le_max
- \+/\- *theorem* add_le_of_le
- \+/\- *theorem* add_lt_of_lt
- \+/\- *theorem* principal_add_ord
- \+/\- *theorem* pow_le
- \+/\- *theorem* pow_eq
- \+ *theorem* mk_list_eq_aleph_0
- \+ *theorem* mk_list_eq_max_mk_aleph_0
- \+/\- *theorem* mk_list_le_max
- \+/\- *theorem* bit0_eq_self
- \+ *theorem* bit0_lt_aleph_0
- \+ *theorem* aleph_0_le_bit0
- \+/\- *theorem* bit1_eq_self_iff
- \+ *theorem* bit1_lt_aleph_0
- \+ *theorem* aleph_0_le_bit1
- \+/\- *theorem* ord_is_limit
- \+/\- *theorem* type_cardinal
- \+/\- *theorem* aleph'_lt
- \+/\- *theorem* aleph'_le
- \+/\- *theorem* aleph'_aleph_idx
- \+/\- *theorem* aleph_idx_aleph'
- \+/\- *theorem* aleph'_succ
- \+/\- *theorem* aleph'_le_of_limit
- \+/\- *theorem* aleph'_omega
- \+/\- *theorem* aleph_lt
- \+/\- *theorem* aleph_le
- \+/\- *theorem* aleph_succ
- \+/\- *theorem* aleph_zero
- \- *theorem* omega_le_aleph'
- \- *theorem* omega_le_aleph
- \+/\- *theorem* exists_aleph
- \- *theorem* succ_omega
- \+/\- *theorem* ord_card_unbounded'
- \+/\- *theorem* eq_aleph_of_eq_card_ord
- \+/\- *theorem* mul_eq_self
- \+/\- *theorem* mul_eq_max
- \- *theorem* omega_mul_eq
- \- *theorem* mul_omega_eq
- \- *theorem* omega_mul_mk_eq
- \- *theorem* mk_mul_omega_eq
- \- *theorem* omega_mul_aleph
- \- *theorem* aleph_mul_omega
- \+/\- *theorem* mul_lt_of_lt
- \+/\- *theorem* mul_le_max
- \+/\- *theorem* add_eq_self
- \+/\- *theorem* add_eq_max
- \+/\- *theorem* add_eq_max'
- \+/\- *theorem* add_le_max
- \+/\- *theorem* add_le_of_le
- \+/\- *theorem* add_lt_of_lt
- \+/\- *theorem* principal_add_ord
- \+/\- *theorem* pow_le
- \+/\- *theorem* pow_eq
- \- *theorem* mk_list_eq_omega
- \- *theorem* mk_list_eq_max_mk_omega
- \+/\- *theorem* mk_list_le_max
- \+/\- *theorem* bit0_eq_self
- \- *theorem* bit0_lt_omega
- \- *theorem* omega_le_bit0
- \+/\- *theorem* bit1_eq_self_iff
- \- *theorem* bit1_lt_omega
- \- *theorem* omega_le_bit1
- \+/\- *def* aleph
- \+/\- *def* aleph

modified src/set_theory/game/short.lean

modified src/set_theory/ordinal/arithmetic.lean
- \+/\- *theorem* add_le_of_limit
- \+/\- *theorem* sub_nonempty
- \+/\- *theorem* one_add_omega
- \+/\- *theorem* one_add_of_omega_le
- \+/\- *theorem* mul_le_of_limit
- \+/\- *theorem* lt_mul_of_limit
- \+/\- *theorem* div_nonempty
- \+ *theorem* ord_aleph_0
- \+ *theorem* add_one_of_aleph_0_le
- \+/\- *theorem* lt_omega
- \+/\- *theorem* nat_lt_omega
- \+/\- *theorem* omega_pos
- \+/\- *theorem* omega_ne_zero
- \+/\- *theorem* one_lt_omega
- \+/\- *theorem* omega_is_limit
- \+/\- *theorem* omega_le
- \+/\- *theorem* sup_nat_cast
- \+/\- *theorem* nat_lt_limit
- \+/\- *theorem* omega_le_of_is_limit
- \+/\- *theorem* is_limit_iff_omega_dvd
- \+/\- *theorem* sup_add_nat
- \+/\- *theorem* sup_mul_nat
- \+/\- *theorem* sup_opow_nat
- \+/\- *theorem* add_le_of_limit
- \+/\- *theorem* sub_nonempty
- \+/\- *theorem* one_add_omega
- \+/\- *theorem* one_add_of_omega_le
- \+/\- *theorem* mul_le_of_limit
- \+/\- *theorem* lt_mul_of_limit
- \+/\- *theorem* div_nonempty
- \- *theorem* ord_omega
- \- *theorem* add_one_of_omega_le
- \+/\- *theorem* lt_omega
- \+/\- *theorem* nat_lt_omega
- \+/\- *theorem* omega_pos
- \+/\- *theorem* omega_ne_zero
- \+/\- *theorem* one_lt_omega
- \+/\- *theorem* omega_is_limit
- \+/\- *theorem* omega_le
- \+/\- *theorem* sup_nat_cast
- \+/\- *theorem* nat_lt_limit
- \+/\- *theorem* omega_le_of_is_limit
- \+/\- *theorem* is_limit_iff_omega_dvd
- \+/\- *theorem* sup_add_nat
- \+/\- *theorem* sup_mul_nat
- \+/\- *theorem* sup_opow_nat
- \+/\- *def* pred
- \+/\- *def* pred

modified src/set_theory/ordinal/basic.lean
- \+/\- *theorem* card_omega
- \+/\- *theorem* lift_omega
- \+/\- *theorem* univ_id
- \+/\- *theorem* mk_ordinal_out
- \+/\- *theorem* card_omega
- \+/\- *theorem* lift_omega
- \+/\- *theorem* univ_id
- \+/\- *theorem* mk_ordinal_out
- \+/\- *def* univ
- \+/\- *def* univ

modified src/set_theory/ordinal/notation.lean
- \+/\- *theorem* repr_opow_aux₁
- \+/\- *theorem* repr_opow_aux₁

modified src/topology/metric_space/gromov_hausdorff.lean



## [2022-06-05 04:57:10](https://github.com/leanprover-community/mathlib/commit/8651b70)
chore(set_theory/cardinal/cofinality): golf + fix spacing ([#14509](https://github.com/leanprover-community/mathlib/pull/14509))
#### Estimated changes
modified src/set_theory/cardinal/cofinality.lean



## [2022-06-05 02:47:09](https://github.com/leanprover-community/mathlib/commit/10f4572)
refactor(group_theory/group_action/defs): rename has_faithful_scalar ([#14515](https://github.com/leanprover-community/mathlib/pull/14515))
This is the first scalar -> smul renaming transition.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/scalar.20smul.20naming.20discrepancy
#### Estimated changes
modified scripts/nolints.txt

modified src/algebra/algebra/basic.lean
- \+/\- *theorem* to_alg_hom_injective
- \+/\- *theorem* to_alg_equiv_injective
- \+/\- *theorem* to_alg_hom_injective
- \+/\- *theorem* to_alg_equiv_injective

modified src/algebra/algebra/subalgebra/basic.lean

modified src/algebra/group_ring_action.lean
- \+/\- *theorem* to_ring_hom_injective
- \+/\- *theorem* to_ring_hom_injective

modified src/algebra/hom/aut.lean

modified src/algebra/module/basic.lean

modified src/algebra/module/equiv.lean

modified src/algebra/module/linear_map.lean

modified src/algebra/monoid_algebra/basic.lean

modified src/analysis/normed_space/M_structure.lean
- \+/\- *lemma* commute
- \+/\- *lemma* mul
- \+/\- *lemma* join
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_sup
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* le_def
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_top
- \+/\- *lemma* distrib_lattice_lemma
- \+/\- *lemma* commute
- \+/\- *lemma* mul
- \+/\- *lemma* join
- \+/\- *lemma* coe_inf
- \+/\- *lemma* coe_sup
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* le_def
- \+/\- *lemma* coe_bot
- \+/\- *lemma* coe_top
- \+/\- *lemma* distrib_lattice_lemma

modified src/data/finsupp/basic.lean

modified src/data/mv_polynomial/basic.lean

modified src/data/polynomial/basic.lean

modified src/field_theory/fixed.lean

modified src/group_theory/group_action/defs.lean
- \+/\- *lemma* smul_left_injective'
- \+/\- *lemma* smul_left_injective'

modified src/group_theory/group_action/group.lean
- \+/\- *lemma* mul_action.to_perm_injective
- \+/\- *lemma* mul_action.to_perm_injective

modified src/group_theory/group_action/opposite.lean

modified src/group_theory/group_action/pi.lean
- \+ *lemma* has_faithful_smul_at
- \- *lemma* has_faithful_scalar_at

modified src/group_theory/group_action/prod.lean

modified src/group_theory/group_action/units.lean

modified src/group_theory/perm/subgroup.lean

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/operations.lean

modified src/ring_theory/subring/basic.lean

modified src/ring_theory/subsemiring/basic.lean

modified src/topology/algebra/module/basic.lean



## [2022-06-05 01:29:35](https://github.com/leanprover-community/mathlib/commit/157013d)
feat(set_theory/cardinal/cofinality): weaker definition for regular cardinals ([#14433](https://github.com/leanprover-community/mathlib/pull/14433))
We weaken `c.ord.cof = c` to `c ≤ c.ord.cof` in the definition of regular cardinals, in order to slightly simplify proofs. The lemma `is_regular.cof_eq` shows that this leads to an equivalent definition.
#### Estimated changes
modified src/measure_theory/card_measurable_space.lean

modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* cof_ord_le
- \+/\- *theorem* is_inaccessible.mk
- \+/\- *theorem* cof_ord_le
- \+/\- *theorem* is_inaccessible.mk



## [2022-06-04 21:21:39](https://github.com/leanprover-community/mathlib/commit/741f4de)
feat(data/fin/tuple/monotone): new file ([#14483](https://github.com/leanprover-community/mathlib/pull/14483))
#### Estimated changes
created src/data/fin/tuple/monotone.lean
- \+ *lemma* lift_fun_vec_cons
- \+ *lemma* strict_mono_vec_cons
- \+ *lemma* monotone_vec_cons
- \+ *lemma* strict_anti_vec_cons
- \+ *lemma* antitone_vec_cons
- \+ *lemma* strict_mono.vec_cons
- \+ *lemma* strict_anti.vec_cons
- \+ *lemma* monotone.vec_cons
- \+ *lemma* antitone.vec_cons



## [2022-06-04 21:21:38](https://github.com/leanprover-community/mathlib/commit/f65b160)
feat(set_theory/cardinal/cofinality): basic lemmas on limit cardinals ([#14439](https://github.com/leanprover-community/mathlib/pull/14439))
#### Estimated changes
modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* is_limit.ne_zero
- \+ *theorem* is_limit.succ_lt
- \+ *theorem* is_strong_limit.ne_zero
- \+ *theorem* is_strong_limit.two_power_lt



## [2022-06-04 19:44:08](https://github.com/leanprover-community/mathlib/commit/d136cd5)
chore(data/pi/lex): turn `pi.lex.linear_order` into an instance ([#14389](https://github.com/leanprover-community/mathlib/pull/14389))
* Use `[is_well_order ι (<)]` instead of `(wf : well_founded ((<) : ι → ι → Prop))`. This way `pi.lex.linear_order` can be an instance.
* Add `pi.lex.order_bot`/`pi.lex.order_top`/`pi.lex.bounded_order`.
#### Estimated changes
modified src/data/pi/lex.lean
- \+ *lemma* is_trichotomous_lex
- \+/\- *lemma* lex.le_of_forall_le
- \+ *lemma* lex.le_of_of_lex_le
- \+ *lemma* to_lex_monotone
- \+/\- *lemma* lex.le_of_forall_le



## [2022-06-04 19:44:07](https://github.com/leanprover-community/mathlib/commit/9749297)
feat(measure_theory/integral/interval_integral): integrability of nonnegative derivatives on open intervals ([#14147](https://github.com/leanprover-community/mathlib/pull/14147))
Shows that derivatives of continuous functions are integrable when nonnegative.
#### Estimated changes
modified src/analysis/special_functions/integrals.lean
- \+ *lemma* interval_integrable_rpow'
- \+/\- *lemma* integral_rpow
- \+/\- *lemma* integral_rpow

modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* integrable_on_Ioc_of_interval_integral_norm_bounded
- \+ *lemma* integrable_on_Ioc_of_interval_integral_norm_bounded_left
- \+ *lemma* integrable_on_Ioc_of_interval_integral_norm_bounded_right

modified src/measure_theory/integral/interval_integral.lean
- \+/\- *lemma* integrable_on_Icc_iff_integrable_on_Ioc'
- \+/\- *lemma* integrable_on_Icc_iff_integrable_on_Ioc
- \+ *lemma* integrable_on_Ioc_iff_integrable_on_Ioo'
- \+ *lemma* integrable_on_Ioc_iff_integrable_on_Ioo
- \+ *lemma* integrable_on_Icc_iff_integrable_on_Ioo
- \+ *lemma* interval_integrable_iff'
- \+/\- *lemma* interval_integrable_iff_integrable_Icc_of_le
- \+ *lemma* comp_mul_left
- \+ *lemma* iff_comp_neg
- \+ *lemma* sub_le_integral_of_has_deriv_right_of_le_Ico
- \+/\- *lemma* sub_le_integral_of_has_deriv_right_of_le
- \+/\- *lemma* integral_le_sub_of_has_deriv_right_of_le
- \+/\- *lemma* integral_eq_sub_of_has_deriv_right_of_le_real
- \+ *lemma* integrable_on_deriv_right_of_nonneg
- \+ *lemma* integrable_on_deriv_of_nonneg
- \+/\- *lemma* integrable_on_Icc_iff_integrable_on_Ioc'
- \+/\- *lemma* integrable_on_Icc_iff_integrable_on_Ioc
- \+/\- *lemma* interval_integrable_iff_integrable_Icc_of_le
- \+/\- *lemma* sub_le_integral_of_has_deriv_right_of_le
- \+/\- *lemma* integral_le_sub_of_has_deriv_right_of_le
- \+/\- *lemma* integral_eq_sub_of_has_deriv_right_of_le_real
- \- *lemma* integral_eq_sub_of_has_deriv_right_of_le_real'
- \+ *theorem* interval_integrable_deriv_of_nonneg



## [2022-06-04 17:34:23](https://github.com/leanprover-community/mathlib/commit/93fb534)
refactor(topology/vector_bundle): split file ([#14535](https://github.com/leanprover-community/mathlib/pull/14535))
Also:
* Rename `pullback` -> `topological_vector_bundle.pullback`
* Use `delta_instance` instead of `local attribute [reducible]`
* Change module doc
* Remove transitive import
#### Estimated changes
modified src/geometry/manifold/tangent_bundle.lean

renamed src/topology/vector_bundle.lean to src/topology/vector_bundle/basic.lean
- \- *lemma* pullback.continuous_proj
- \- *lemma* pullback.continuous_lift
- \- *lemma* inducing_pullback_total_space_embedding
- \- *lemma* pullback.continuous_total_space_mk
- \- *lemma* prod.inducing_diag
- \- *lemma* prod.continuous_to_fun
- \- *lemma* prod.left_inv
- \- *lemma* prod.right_inv
- \- *lemma* prod.continuous_inv_fun
- \- *lemma* base_set_prod
- \- *lemma* prod_apply
- \- *lemma* prod_symm_apply
- \- *lemma* trivialization.continuous_linear_equiv_at_prod
- \- *def* pullback_topology
- \- *def* topological_vector_bundle.trivialization.pullback
- \- *def* prod.to_fun'
- \- *def* prod.inv_fun'
- \- *def* prod

created src/topology/vector_bundle/prod.lean
- \+ *lemma* prod.inducing_diag
- \+ *lemma* prod.continuous_to_fun
- \+ *lemma* prod.left_inv
- \+ *lemma* prod.right_inv
- \+ *lemma* prod.continuous_inv_fun
- \+ *lemma* base_set_prod
- \+ *lemma* prod_apply
- \+ *lemma* prod_symm_apply
- \+ *lemma* trivialization.continuous_linear_equiv_at_prod
- \+ *def* prod.to_fun'
- \+ *def* prod.inv_fun'
- \+ *def* prod

created src/topology/vector_bundle/pullback.lean
- \+ *lemma* pullback.continuous_proj
- \+ *lemma* pullback.continuous_lift
- \+ *lemma* inducing_pullback_total_space_embedding
- \+ *lemma* pullback.continuous_total_space_mk
- \+ *def* pullback_topology
- \+ *def* topological_vector_bundle.trivialization.pullback



## [2022-06-04 17:34:22](https://github.com/leanprover-community/mathlib/commit/3103a89)
feat(analysis/special_functions/exp): a lemma about `exp (f x) =O[l] const _ _` ([#14524](https://github.com/leanprover-community/mathlib/pull/14524))
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* is_O_const_left_iff_pos_le_norm

modified src/analysis/special_functions/exp.lean
- \+ *lemma* is_O_one_exp_comp



## [2022-06-04 17:34:21](https://github.com/leanprover-community/mathlib/commit/19b5786)
feat(tactic/set): fix a bug ([#14488](https://github.com/leanprover-community/mathlib/pull/14488))
We make the behaviour of `tactic.interactive.set` closer to that of `tactic.interactive.let`, this should fix the following issue reported in https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/set.20bug.3F/near/284471523:
```lean
import ring_theory.adjoin.basic
example {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] (x : S): false :=
begin
  let y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩, -- works
  set y : algebra.adjoin R ({x} : set S) := ⟨x, algebra.self_mem_adjoin_singleton R x⟩, -- error
  sorry
end
```
This is related to [lean[#555](https://github.com/leanprover-community/mathlib/pull/555)
](https://github.com/leanprover-community/lean/pull/555)
I also fix two completely unrelated docstrings (where the list syntax created two lists instead of one) as I wouldn't want to separately add them to CI...
#### Estimated changes
modified src/algebra/order/lattice_group.lean

modified src/data/nat/prime.lean

modified src/tactic/interactive.lean

modified test/set.lean



## [2022-06-04 17:34:20](https://github.com/leanprover-community/mathlib/commit/a869df9)
feat(analysis/asymptotics/asymptotics): generalize `is_*.inv_rev` ([#14486](https://github.com/leanprover-community/mathlib/pull/14486))
Use weaker assumption `∀ᶠ x in l, f x = 0 → g x = 0` instead of `∀ᶠ x in l, f x ≠ 0`.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean

modified src/measure_theory/integral/circle_integral.lean



## [2022-06-04 17:34:19](https://github.com/leanprover-community/mathlib/commit/8a6a793)
refactor(data/fin/basic): reformulate `fin.strict_mono_iff_lt_succ` ([#14482](https://github.com/leanprover-community/mathlib/pull/14482))
Use `fin.succ_cast` and `fin.succ`. This way we lose the case `n = 0`
but the statement looks more natural in other cases. Also add versions
for `monotone`, `antitone`, and `strict_anti`.
#### Estimated changes
modified src/combinatorics/composition.lean

modified src/data/fin/basic.lean
- \+ *lemma* lift_fun_iff_succ
- \+/\- *lemma* strict_mono_iff_lt_succ
- \+ *lemma* monotone_iff_le_succ
- \+ *lemma* strict_anti_iff_succ_lt
- \+ *lemma* antitone_iff_succ_le
- \+/\- *lemma* strict_mono_iff_lt_succ

modified src/order/jordan_holder.lean



## [2022-06-04 17:34:18](https://github.com/leanprover-community/mathlib/commit/cab5a45)
refactor(order/directed): use `(≥)` instead of `swap (≤)` ([#14474](https://github.com/leanprover-community/mathlib/pull/14474))
#### Estimated changes
modified src/analysis/convex/quasiconvex.lean
- \+/\- *lemma* quasiconcave_on.convex
- \+/\- *lemma* quasiconcave_on.convex

modified src/category_theory/filtered.lean

modified src/order/directed.lean
- \+/\- *lemma* exists_le_le
- \+/\- *lemma* is_bot_or_exists_lt
- \+/\- *lemma* is_bot_iff_is_min
- \+/\- *lemma* exists_le_le
- \+/\- *lemma* is_bot_or_exists_lt
- \+/\- *lemma* is_bot_iff_is_min
- \+/\- *theorem* exists_lt_of_directed_ge
- \+/\- *theorem* exists_lt_of_directed_ge

modified src/order/ideal.lean
- \+/\- *lemma* inter_nonempty
- \+/\- *lemma* inter_nonempty



## [2022-06-04 17:34:17](https://github.com/leanprover-community/mathlib/commit/b5973ba)
feat(measure_theory/measure/measure_space): there exists a ball of positive measure ([#14449](https://github.com/leanprover-community/mathlib/pull/14449))
Motivated by [#12933](https://github.com/leanprover-community/mathlib/pull/12933)
#### Estimated changes
modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* exists_pos_measure_of_cover
- \+ *lemma* exists_pos_preimage_ball
- \+ *lemma* exists_pos_ball



## [2022-06-04 15:25:58](https://github.com/leanprover-community/mathlib/commit/cfcc3a1)
chore(data/finsupp/basic): make arguments explicit ([#14551](https://github.com/leanprover-community/mathlib/pull/14551))
This follow the pattern that arguments to an `=` lemma should be explicit if they're not implied by other arguments.
#### Estimated changes
modified src/algebra/monoid_algebra/grading.lean

modified src/data/finsupp/basic.lean
- \+/\- *lemma* single_eq_update
- \+/\- *lemma* single_eq_pi_single
- \+/\- *lemma* single_zero
- \+/\- *lemma* support_single_ne_zero
- \+/\- *lemma* single_add
- \+/\- *lemma* single_neg
- \+/\- *lemma* single_sub
- \+/\- *lemma* single_eq_update
- \+/\- *lemma* single_eq_pi_single
- \+/\- *lemma* single_zero
- \+/\- *lemma* support_single_ne_zero
- \+/\- *lemma* single_add
- \+/\- *lemma* single_neg
- \+/\- *lemma* single_sub

modified src/data/finsupp/multiset.lean

modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* C_add
- \+/\- *lemma* C_add

modified src/data/mv_polynomial/variables.lean

modified src/data/polynomial/basic.lean

modified src/group_theory/free_abelian_group_finsupp.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/std_basis.lean

modified src/ring_theory/finiteness.lean

modified src/ring_theory/polynomial/homogeneous.lean

modified src/ring_theory/polynomial/symmetric.lean



## [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/b949240)
feat(algebra/{lie/subalgebra,module/submodule/pointwise}): submodules and lie subalgebras form canonically ordered additive monoids under addition ([#14529](https://github.com/leanprover-community/mathlib/pull/14529))
We can't actually make these instances because they result in loops for `simp`.
The `le_iff_exists_sup` lemma is probably not very useful for much beyond these new instances, but it matches `le_iff_exists_add`.
#### Estimated changes
modified src/algebra/lie/subalgebra.lean
- \+ *def* canonically_ordered_add_monoid

modified src/algebra/module/submodule/pointwise.lean
- \+ *def* canonically_ordered_add_monoid

modified src/order/lattice.lean
- \+ *theorem* le_iff_exists_sup

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/nilpotent.lean



## [2022-06-04 15:25:56](https://github.com/leanprover-community/mathlib/commit/83c1cd8)
feat(set_theory/cardinal/cofinality): `ω` is a strong limit cardinal ([#14436](https://github.com/leanprover-community/mathlib/pull/14436))
#### Estimated changes
modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* is_strong_limit_omega
- \+ *theorem* is_limit_omega



## [2022-06-04 15:25:55](https://github.com/leanprover-community/mathlib/commit/0746194)
feat(set_theory/cardinal/cofinality): limit cardinal is at least `ω` ([#14432](https://github.com/leanprover-community/mathlib/pull/14432))
#### Estimated changes
modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* is_limit.omega_le



## [2022-06-04 15:25:54](https://github.com/leanprover-community/mathlib/commit/15726ee)
move(set_theory/{schroeder_bernstein → cardinal/schroeder_bernstein}): move file ([#14426](https://github.com/leanprover-community/mathlib/pull/14426))
Schroeder-Bernstein is ultimately the statement that cardinals are a total order, so it should go in that folder.
#### Estimated changes
modified src/set_theory/cardinal/basic.lean

renamed src/set_theory/schroeder_bernstein.lean to src/set_theory/cardinal/schroeder_bernstein.lean



## [2022-06-04 15:25:53](https://github.com/leanprover-community/mathlib/commit/1f196cb)
feat(data/list/nodup): Add `list.nodup_iff` ([#14371](https://github.com/leanprover-community/mathlib/pull/14371))
Add `list.nodup_iff` and two helper lemmas `list.nth_le_eq_iff` and `list.some_nth_le_eq`
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* nth_le_eq_iff
- \+ *lemma* some_nth_le_eq

modified src/data/list/nodup.lean
- \+ *lemma* nodup_iff_nth_ne_nth



## [2022-06-04 13:17:06](https://github.com/leanprover-community/mathlib/commit/aa7d90b)
doc(set_theory/ordinal/natural_ops): mention alternate names ([#14546](https://github.com/leanprover-community/mathlib/pull/14546))
#### Estimated changes
modified src/set_theory/ordinal/natural_ops.lean



## [2022-06-04 13:17:05](https://github.com/leanprover-community/mathlib/commit/8ef2c02)
chore(order/bounded_order): move `order_dual` instances up, use them to golf lemmas ([#14544](https://github.com/leanprover-community/mathlib/pull/14544))
I only golf lemmas and `Prop`-valued instances to be sure that I don't add `order_dual`s to the statements.
#### Estimated changes
modified src/order/bounded_order.lean
- \+/\- *lemma* of_dual_bot
- \+/\- *lemma* of_dual_top
- \+/\- *lemma* to_dual_bot
- \+/\- *lemma* to_dual_top
- \+/\- *lemma* not_is_max_bot
- \+/\- *lemma* not_top_le_coe
- \+/\- *lemma* not_is_max_bot
- \+/\- *lemma* not_top_le_coe
- \+/\- *lemma* of_dual_bot
- \+/\- *lemma* of_dual_top
- \+/\- *lemma* to_dual_bot
- \+/\- *lemma* to_dual_top



## [2022-06-04 13:17:04](https://github.com/leanprover-community/mathlib/commit/5002452)
refactor(topology): move code around ([#14525](https://github.com/leanprover-community/mathlib/pull/14525))
Create a new file `topology/inseparable` and more the definitions of `specializes` and `inseparable` to this file. This is a preparation to a larger refactor of these definitions.
#### Estimated changes
modified src/topology/continuous_function/basic.lean
- \+ *lemma* map_specialization

created src/topology/inseparable.lean
- \+ *lemma* specializes_def
- \+ *lemma* specializes_iff_closure_subset
- \+ *lemma* specializes_rfl
- \+ *lemma* specializes_refl
- \+ *lemma* specializes.trans
- \+ *lemma* specializes_iff_forall_closed
- \+ *lemma* specializes_iff_forall_open
- \+ *lemma* specializes.map
- \+ *lemma* specialization_order.monotone_of_continuous
- \+ *lemma* inseparable_iff_nhds_eq
- \+ *lemma* inseparable.map
- \+ *lemma* inseparable_iff_closed
- \+ *lemma* inseparable_iff_closure
- \+ *lemma* inseparable_iff_specializes_and
- \+ *lemma* subtype_inseparable_iff
- \+ *def* specializes
- \+ *def* specialization_preorder
- \+ *def* inseparable

modified src/topology/separation.lean
- \+ *lemma* specializes_antisymm
- \+ *lemma* specializes.eq
- \+ *lemma* specializes_iff_eq
- \- *lemma* inseparable_iff_nhds_eq
- \- *lemma* inseparable.map
- \- *lemma* inseparable_iff_closed
- \- *lemma* inseparable_iff_closure
- \- *lemma* subtype_inseparable_iff
- \+ *def* specialization_order
- \- *def* inseparable

modified src/topology/sober.lean
- \- *lemma* specializes_def
- \- *lemma* specializes_iff_closure_subset
- \- *lemma* specializes_rfl
- \- *lemma* specializes_refl
- \- *lemma* specializes.trans
- \- *lemma* specializes_iff_forall_closed
- \- *lemma* specializes_iff_forall_open
- \- *lemma* inseparable_iff_specializes_and
- \- *lemma* specializes_antisymm
- \- *lemma* specializes.map
- \- *lemma* continuous_map.map_specialization
- \- *lemma* specializes.eq
- \- *lemma* specializes_iff_eq
- \- *lemma* specialization_order.monotone_of_continuous
- \- *def* specializes
- \- *def* specialization_preorder
- \- *def* specialization_order



## [2022-06-04 13:17:03](https://github.com/leanprover-community/mathlib/commit/66b618d)
perf(measure_theory/probability_mass_function/monad): speed up proof ([#14519](https://github.com/leanprover-community/mathlib/pull/14519))
This causes a deterministic timeout in another PR.
#### Estimated changes
modified src/measure_theory/probability_mass_function/monad.lean



## [2022-06-04 13:17:02](https://github.com/leanprover-community/mathlib/commit/3f26dfe)
feat(data/int/basic): Units are either equal or negatives of each other ([#14517](https://github.com/leanprover-community/mathlib/pull/14517))
This PR adds a lemma stating that units in the integers are either equal or negatives of each other. I have found this lemma to be useful for casework.
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* is_unit_eq_or_eq_neg



## [2022-06-04 13:17:01](https://github.com/leanprover-community/mathlib/commit/b332507)
feat(data/int/basic): Forward direction of `is_unit_iff_nat_abs_eq` ([#14516](https://github.com/leanprover-community/mathlib/pull/14516))
This PR adds the forward direction of `is_unit_iff_nat_abs_eq` as a separate lemma. This is useful since you often have `is_unit n` as a hypothesis, and `is_unit_iff_nat_abs_eq.mp hn` is a bit of a mouthful.
#### Estimated changes
modified src/data/int/basic.lean



## [2022-06-04 13:17:00](https://github.com/leanprover-community/mathlib/commit/2a9be5b)
feat(analysis/special_functions): lemmas about filter `map`/`comap` ([#14513](https://github.com/leanprover-community/mathlib/pull/14513))
* add `comap_inf_principal_range` and `comap_nhds_within_range`;
* add `@[simp]` to `real.comap_exp_nhds_within_Ioi_zero`;
* add `real.comap_exp_nhds_zero`, `complex.comap_exp_comap_abs_at_top`, `complex.comap_exp_nhds_zero`, `complex.comap_exp_nhds_within_zero`, and `complex.tendsto_exp_nhds_zero_iff`;
* add `complex.map_exp_comap_re_at_bot` and `complex.map_exp_comap_re_at_top`;
* add `comap_norm_nhds_zero` and `complex.comap_abs_nhds_zero`.
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* comap_abs_nhds_zero

modified src/analysis/normed/group/basic.lean
- \+ *lemma* comap_norm_nhds_zero

modified src/analysis/special_functions/complex/log.lean
- \+ *lemma* map_exp_comap_re_at_bot
- \+ *lemma* map_exp_comap_re_at_top

modified src/analysis/special_functions/exp.lean
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero
- \+ *lemma* comap_exp_nhds_zero
- \+ *lemma* comap_exp_comap_abs_at_top
- \+ *lemma* comap_exp_nhds_zero
- \+ *lemma* comap_exp_nhds_within_zero
- \+ *lemma* tendsto_exp_nhds_zero_iff
- \+/\- *lemma* comap_exp_nhds_within_Ioi_zero

modified src/order/filter/basic.lean
- \+ *lemma* comap_inf_principal_range

modified src/topology/continuous_on.lean
- \+ *lemma* comap_nhds_within_range



## [2022-06-04 13:16:59](https://github.com/leanprover-community/mathlib/commit/0e943b1)
feat(order/boolean_algebra, set/basic): some compl lemmas ([#14508](https://github.com/leanprover-community/mathlib/pull/14508))
Added a few lemmas about complementation, and rephrased `compl_compl` and `mem_compl_image` to apply in `boolean_algebra` rather than `set (set _ ))`.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* preimage_compl_eq_image_compl
- \+/\- *theorem* mem_compl_image
- \+/\- *theorem* compl_compl_image
- \+/\- *theorem* mem_compl_image
- \+/\- *theorem* compl_compl_image

modified src/order/boolean_algebra.lean
- \+ *theorem* compl_eq_comm
- \+ *theorem* eq_compl_comm
- \+ *theorem* disjoint_iff_le_compl_right
- \+ *theorem* disjoint_iff_le_compl_left



## [2022-06-04 13:16:58](https://github.com/leanprover-community/mathlib/commit/27c4241)
feat(set_theory/ordinal/arithmetic): `has_exists_add_of_le` instance for `ordinal` ([#14499](https://github.com/leanprover-community/mathlib/pull/14499))
#### Estimated changes
modified src/set_theory/ordinal/arithmetic.lean



## [2022-06-04 11:12:53](https://github.com/leanprover-community/mathlib/commit/7c57af9)
feat(order/bounds): Bounds on `set.image2` ([#14306](https://github.com/leanprover-community/mathlib/pull/14306))
`set.image2` analogues to the `set.image` lemmas.
#### Estimated changes
modified src/order/bounds.lean
- \+ *lemma* mem_upper_bounds_image2
- \+ *lemma* mem_lower_bounds_image2
- \+ *lemma* image2_upper_bounds_upper_bounds_subset
- \+ *lemma* image2_lower_bounds_lower_bounds_subset
- \+ *lemma* bdd_above.image2
- \+ *lemma* bdd_below.image2
- \+ *lemma* is_greatest.image2
- \+ *lemma* is_least.image2
- \+ *lemma* mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds
- \+ *lemma* mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds
- \+ *lemma* image2_upper_bounds_lower_bounds_subset_upper_bounds_image2
- \+ *lemma* image2_lower_bounds_upper_bounds_subset_lower_bounds_image2
- \+ *lemma* bdd_above.bdd_above_image2_of_bdd_below
- \+ *lemma* bdd_below.bdd_below_image2_of_bdd_above
- \+ *lemma* is_greatest.is_greatest_image2_of_is_least
- \+ *lemma* is_least.is_least_image2_of_is_greatest
- \+ *lemma* mem_upper_bounds_image2_of_mem_lower_bounds
- \+ *lemma* mem_lower_bounds_image2_of_mem_upper_bounds
- \+ *lemma* image2_upper_bounds_upper_bounds_subset_upper_bounds_image2
- \+ *lemma* image2_lower_bounds_lower_bounds_subset_lower_bounds_image2
- \+ *lemma* bdd_below.image2_bdd_above
- \+ *lemma* bdd_above.image2_bdd_below
- \+ *lemma* is_least.is_greatest_image2
- \+ *lemma* is_greatest.is_least_image2
- \+ *lemma* mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds
- \+ *lemma* mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds
- \+ *lemma* image2_lower_bounds_upper_bounds_subset_upper_bounds_image2
- \+ *lemma* image2_upper_bounds_lower_bounds_subset_lower_bounds_image2
- \+ *lemma* bdd_below.bdd_above_image2_of_bdd_above
- \+ *lemma* bdd_above.bdd_below_image2_of_bdd_above
- \+ *lemma* is_least.is_greatest_image2_of_is_greatest
- \+ *lemma* is_greatest.is_least_image2_of_is_least



## [2022-06-04 08:30:21](https://github.com/leanprover-community/mathlib/commit/85fffda)
feat(order/conditionally_complete_lattice,data/real/nnreal): add 2 lemmas ([#14545](https://github.com/leanprover-community/mathlib/pull/14545))
Add `cInf_univ` and `nnreal.Inf_empty`.
#### Estimated changes
modified src/data/real/nnreal.lean
- \+ *lemma* Inf_empty

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_univ



## [2022-06-04 06:32:56](https://github.com/leanprover-community/mathlib/commit/72ac40e)
feat(data/multiset/basic): add some lemmas ([#14421](https://github.com/leanprover-community/mathlib/pull/14421))
#### Estimated changes
modified src/data/multiset/basic.lean
- \+ *lemma* map_eq_cons
- \+ *lemma* map_surjective_of_surjective
- \+ *lemma* rel.trans
- \+ *lemma* rel.countp_eq
- \+ *theorem* countp_nsmul



## [2022-06-04 04:55:08](https://github.com/leanprover-community/mathlib/commit/a418945)
chore(set_theory/surreal/basic): golf ([#14168](https://github.com/leanprover-community/mathlib/pull/14168))
We also add some basic lemmas for simplifying the definition of `numeric` when either a game's left or right moves are empty.
#### Estimated changes
modified src/set_theory/surreal/basic.lean
- \+ *theorem* numeric_of_is_empty
- \+ *theorem* numeric_of_is_empty_left_moves
- \+ *theorem* numeric_of_is_empty_right_moves
- \+/\- *theorem* numeric_zero
- \+/\- *theorem* numeric_one
- \+/\- *theorem* numeric_zero
- \+/\- *theorem* numeric_one
- \+/\- *def* mk
- \+/\- *def* mk



## [2022-06-04 04:16:45](https://github.com/leanprover-community/mathlib/commit/e1b3351)
feat(set_theory/game/pgame): Add dot notation on many lemmas ([#14149](https://github.com/leanprover-community/mathlib/pull/14149))
#### Estimated changes
modified src/set_theory/game/basic.lean

modified src/set_theory/game/impartial.lean

modified src/set_theory/game/nim.lean
- \+/\- *lemma* grundy_value_zero
- \+/\- *lemma* grundy_value_star
- \+/\- *lemma* grundy_value_zero
- \+/\- *lemma* grundy_value_star

modified src/set_theory/game/pgame.lean
- \+ *theorem* _root_.has_le.le.not_lf
- \+ *theorem* lf.not_le
- \+/\- *theorem* lf_irrefl
- \+/\- *theorem* lf_of_lt
- \+ *theorem* equiv.le
- \+ *theorem* equiv.ge
- \+/\- *theorem* equiv_rfl
- \+/\- *theorem* equiv_refl
- \+ *theorem* lf.not_equiv
- \+ *theorem* lf.not_equiv'
- \+ *theorem* lf.not_lt
- \+/\- *theorem* lf_of_fuzzy
- \+/\- *theorem* lf_irrefl
- \+/\- *theorem* lf_of_lt
- \+/\- *theorem* equiv_rfl
- \+/\- *theorem* equiv_refl
- \- *theorem* equiv_symm
- \- *theorem* equiv_trans
- \+/\- *theorem* lf_of_fuzzy

modified src/set_theory/game/winner.lean

modified src/set_theory/surreal/basic.lean
- \+/\- *theorem* le_of_lf
- \+/\- *theorem* lt_of_lf
- \+ *theorem* lt_or_equiv_or_gt
- \+/\- *theorem* le_of_lf
- \+/\- *theorem* lt_of_lf



## [2022-06-03 22:33:16](https://github.com/leanprover-community/mathlib/commit/0098286)
feat(set_theory/ordinal/natural_ops): define natural addition ([#14291](https://github.com/leanprover-community/mathlib/pull/14291))
We define the natural addition operation on ordinals. We prove the basic properties, like commutativity, associativity, and cancellativity. We also provide the type synonym `nat_ordinal` for ordinals with natural operations, which allows us to take full advantage of this rich algebraic structure.
#### Estimated changes
created src/set_theory/ordinal/natural_ops.lean
- \+ *theorem* to_ordinal_symm_eq
- \+ *theorem* to_ordinal_to_nat_ordinal
- \+ *theorem* lt_wf
- \+ *theorem* to_ordinal_zero
- \+ *theorem* to_ordinal_one
- \+ *theorem* to_ordinal_eq_zero
- \+ *theorem* to_ordinal_eq_one
- \+ *theorem* to_ordinal_max
- \+ *theorem* to_ordinal_min
- \+ *theorem* succ_def
- \+ *theorem* induction
- \+ *theorem* to_nat_ordinal_symm_eq
- \+ *theorem* to_nat_ordinal_to_ordinal
- \+ *theorem* to_nat_ordinal_zero
- \+ *theorem* to_nat_ordinal_one
- \+ *theorem* to_nat_ordinal_eq_zero
- \+ *theorem* to_nat_ordinal_eq_one
- \+ *theorem* to_nat_ordinal_max
- \+ *theorem* to_nat_ordinal_min
- \+ *theorem* nadd_def
- \+ *theorem* lt_nadd_iff
- \+ *theorem* nadd_le_iff
- \+ *theorem* nadd_lt_nadd_left
- \+ *theorem* nadd_lt_nadd_right
- \+ *theorem* nadd_le_nadd_left
- \+ *theorem* nadd_le_nadd_right
- \+ *theorem* nadd_comm
- \+ *theorem* blsub_nadd_of_mono
- \+ *theorem* nadd_assoc
- \+ *theorem* nadd_zero
- \+ *theorem* zero_nadd
- \+ *theorem* nadd_one
- \+ *theorem* one_nadd
- \+ *theorem* nadd_succ
- \+ *theorem* succ_nadd
- \+ *theorem* nadd_nat
- \+ *theorem* nat_nadd
- \+ *theorem* add_le_nadd
- \+ *theorem* add_one_eq_succ
- \+ *theorem* to_ordinal_cast_nat
- \+ *theorem* to_nat_ordinal_cast_nat
- \+ *theorem* lt_of_nadd_lt_nadd_left
- \+ *theorem* lt_of_nadd_lt_nadd_right
- \+ *theorem* le_of_nadd_le_nadd_left
- \+ *theorem* le_of_nadd_le_nadd_right
- \+ *theorem* nadd_lt_nadd_iff_left
- \+ *theorem* nadd_lt_nadd_iff_right
- \+ *theorem* nadd_le_nadd_iff_left
- \+ *theorem* nadd_le_nadd_iff_right
- \+ *theorem* nadd_left_cancel
- \+ *theorem* nadd_right_cancel
- \+ *theorem* nadd_left_cancel_iff
- \+ *theorem* nadd_right_cancel_iff
- \+ *def* nat_ordinal
- \+ *def* ordinal.to_nat_ordinal
- \+ *def* nat_ordinal.to_ordinal



## [2022-06-03 16:16:11](https://github.com/leanprover-community/mathlib/commit/d63246c)
feat(analysis/calculus/fderiv_measurable): the right derivative is measurable ([#14527](https://github.com/leanprover-community/mathlib/pull/14527))
We already know that the full Fréchet derivative is measurable. In this PR, we follow the same proof to show that the right derivative of a function defined on the real line is also measurable (the target space may be any complete vector space).
#### Estimated changes
modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_mem_iff
- \+ *lemma* deriv_within_mem_iff
- \+ *lemma* differentiable_within_at_Ioi_iff_Ici
- \+ *lemma* deriv_within_Ioi_eq_Ici
- \+ *theorem* has_deriv_at_filter_iff_is_o
- \+ *theorem* has_deriv_within_at_iff_is_o
- \+ *theorem* has_deriv_at_iff_is_o

modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_mem_iff

modified src/analysis/calculus/fderiv_measurable.lean
- \+ *lemma* A_mem_nhds_within_Ioi
- \+ *lemma* B_mem_nhds_within_Ioi
- \+ *lemma* measurable_set_B
- \+ *lemma* A_mono
- \+ *lemma* le_of_mem_A
- \+ *lemma* mem_A_of_differentiable
- \+ *lemma* norm_sub_le_of_mem_A
- \+ *lemma* differentiable_set_subset_D
- \+ *lemma* D_subset_differentiable_set
- \+ *lemma* measurable_deriv_within_Ici
- \+ *lemma* strongly_measurable_deriv_within_Ici
- \+ *lemma* ae_measurable_deriv_within_Ici
- \+ *lemma* ae_strongly_measurable_deriv_within_Ici
- \+ *lemma* measurable_deriv_within_Ioi
- \+ *lemma* strongly_measurable_deriv_within_Ioi
- \+ *lemma* ae_measurable_deriv_within_Ioi
- \+ *lemma* ae_strongly_measurable_deriv_within_Ioi
- \+ *theorem* differentiable_set_eq_D
- \+ *theorem* measurable_set_of_differentiable_within_at_Ici_of_is_complete
- \+ *theorem* measurable_set_of_differentiable_within_at_Ici
- \+ *theorem* measurable_set_of_differentiable_within_at_Ioi
- \+ *def* A
- \+ *def* B
- \+ *def* D

modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_set_of_mem_nhds_within_Ioi_aux
- \+ *lemma* measurable_set_of_mem_nhds_within_Ioi



## [2022-06-03 16:16:10](https://github.com/leanprover-community/mathlib/commit/2a21a86)
refactor(algebra/order/ring): turn `sq_le_sq` into an `iff` ([#14511](https://github.com/leanprover-community/mathlib/pull/14511))
* `sq_le_sq` and `sq_lt_sq` are now `iff` lemmas;
* drop `abs_le_abs_of_sq_le_sq` and `abs_lt_abs_of_sq_lt_sq`.
#### Estimated changes
modified src/algebra/group_power/order.lean
- \+/\- *theorem* sq_lt_sq
- \+/\- *theorem* sq_le_sq
- \+/\- *theorem* sq_lt_sq
- \+/\- *theorem* sq_le_sq
- \- *theorem* abs_lt_abs_of_sq_lt_sq
- \- *theorem* abs_le_abs_of_sq_le_sq

modified src/analysis/inner_product_space/basic.lean

modified src/analysis/special_functions/bernstein.lean
- \+ *lemma* δ_pos

modified src/number_theory/modular.lean



## [2022-06-03 14:08:37](https://github.com/leanprover-community/mathlib/commit/fa22603)
docs(order/boolean_algebra): typo in generalized boolean algebra doc ([#14536](https://github.com/leanprover-community/mathlib/pull/14536))
#### Estimated changes
modified src/order/boolean_algebra.lean



## [2022-06-03 12:27:32](https://github.com/leanprover-community/mathlib/commit/6ca5910)
feat(measure_theory/integral/lebesgue): approximate a function by a finite integral function in a sigma-finite measure space. ([#14528](https://github.com/leanprover-community/mathlib/pull/14528))
If `L < ∫⁻ x, f x ∂μ`, then there exists a measurable function `g ≤ f` (even a simple function) with finite integral and `L < ∫⁻ x, g x ∂μ`, if the measure is sigma-finite.
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral
- \+ *lemma* exists_lt_lintegral_simple_func_of_lt_lintegral

modified src/measure_theory/measure/regular.lean

modified src/topology/instances/ennreal.lean
- \+ *lemma* exists_lt_add_of_lt_add



## [2022-06-03 10:31:17](https://github.com/leanprover-community/mathlib/commit/bec8b65)
feat(analysis/calculus/tangent_cone): unique differentiability of open interval at endpoint ([#14530](https://github.com/leanprover-community/mathlib/pull/14530))
We show that, if a point belongs to the closure of a convex set with nonempty interior, then it is a point of unique differentiability. We apply this to the specific situation of `Ioi` and `Iio`.
#### Estimated changes
modified src/analysis/calculus/tangent_cone.lean
- \+ *lemma* mem_tangent_cone_of_open_segment_subset
- \+/\- *lemma* mem_tangent_cone_of_segment_subset
- \+ *lemma* unique_diff_within_at_Ioi
- \+ *lemma* unique_diff_within_at_Iio
- \+/\- *lemma* mem_tangent_cone_of_segment_subset
- \+ *theorem* unique_diff_within_at_convex
- \+/\- *theorem* unique_diff_on_convex
- \+/\- *theorem* unique_diff_on_convex



## [2022-06-03 10:31:16](https://github.com/leanprover-community/mathlib/commit/705160e)
feat(algebra/char_zero): add a lemma `ring_hom.injective_nat` ([#14414](https://github.com/leanprover-community/mathlib/pull/14414))
Note that there is a lemma `ring_hom.injective_int`.
#### Estimated changes
modified src/algebra/char_zero.lean
- \+ *lemma* ring_hom.injective_nat



## [2022-06-03 10:31:15](https://github.com/leanprover-community/mathlib/commit/d2dcb74)
feat(data/polynomial/eval): reduce assumptions, add a lemma ([#14391](https://github.com/leanprover-community/mathlib/pull/14391))
Note that there is a lemma `mv_polynomial.support_map_of_injective`.
#### Estimated changes
modified src/data/polynomial/eval.lean
- \+/\- *lemma* support_map_subset
- \+ *lemma* support_map_of_injective
- \+/\- *lemma* support_map_subset



## [2022-06-03 10:31:14](https://github.com/leanprover-community/mathlib/commit/c9d69a4)
feat(topology/algebra/module/finite_dimension): all linear maps from a finite dimensional T2 TVS are continuous ([#13460](https://github.com/leanprover-community/mathlib/pull/13460))
Summary of the changes :
- generalize a bunch of results from `analysis/normed_space/finite_dimension` (main ones are : `continuous_equiv_fun_basis`, `linear_map.continuous_of_finite_dimensional`, and related constructions like `linear_map.to_continuous_linear_map`) to arbitrary TVSs, and move them to a new file `topology/algebra/module/finite_dimension`
- generalize `linear_map.continuous_iff_is_closed_ker` to arbitrary TVSs, and move it from `analysis/normed_space/operator_norm` to the new file
- as needed by the generalizations, add lemma `unique_topology_of_t2` : if `𝕜` is a nondiscrete normed field, any T2 topology on `𝕜` which makes it a topological vector space over itself (with the norm topology) is *equal* to the norm topology
- finally, change `pi_eq_sum_univ` to take any `decidable_eq` instance (not just the classical ones), and fix later uses
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean
- \- *lemma* linear_map.continuous_on_pi
- \- *lemma* continuous_equiv_fun_basis
- \- *lemma* coe_to_continuous_linear_map'
- \- *lemma* coe_to_continuous_linear_map
- \- *lemma* coe_to_continuous_linear_map_symm
- \- *lemma* coe_to_continuous_linear_equiv
- \- *lemma* coe_to_continuous_linear_equiv'
- \- *lemma* coe_to_continuous_linear_equiv_symm
- \- *lemma* coe_to_continuous_linear_equiv_symm'
- \- *lemma* to_linear_equiv_to_continuous_linear_equiv
- \- *lemma* to_linear_equiv_to_continuous_linear_equiv_symm
- \- *lemma* coe_to_continuous_linear_equiv_of_det_ne_zero
- \- *lemma* to_continuous_linear_equiv_of_det_ne_zero_apply
- \- *theorem* linear_map.continuous_of_finite_dimensional
- \- *def* to_continuous_linear_map
- \- *def* to_continuous_linear_equiv
- \- *def* to_continuous_linear_equiv_of_det_ne_zero

modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* linear_map.continuous_iff_is_closed_ker

modified src/linear_algebra/basic.lean
- \+/\- *lemma* pi_eq_sum_univ
- \+/\- *lemma* pi_apply_eq_sum_univ
- \+/\- *lemma* pi_eq_sum_univ
- \+/\- *lemma* pi_apply_eq_sum_univ

modified src/linear_algebra/matrix/adjugate.lean

modified src/ring_theory/ideal/quotient.lean

created src/topology/algebra/module/finite_dimension.lean
- \+ *lemma* linear_map.continuous_on_pi
- \+ *lemma* unique_topology_of_t2
- \+ *lemma* linear_map.continuous_of_is_closed_ker
- \+ *lemma* linear_map.continuous_iff_is_closed_ker
- \+ *lemma* coe_to_continuous_linear_map'
- \+ *lemma* coe_to_continuous_linear_map
- \+ *lemma* coe_to_continuous_linear_map_symm
- \+ *lemma* coe_to_continuous_linear_equiv
- \+ *lemma* coe_to_continuous_linear_equiv'
- \+ *lemma* coe_to_continuous_linear_equiv_symm
- \+ *lemma* coe_to_continuous_linear_equiv_symm'
- \+ *lemma* to_linear_equiv_to_continuous_linear_equiv
- \+ *lemma* to_linear_equiv_to_continuous_linear_equiv_symm
- \+ *lemma* coe_to_continuous_linear_equiv_of_det_ne_zero
- \+ *lemma* to_continuous_linear_equiv_of_det_ne_zero_apply
- \+ *theorem* linear_map.continuous_of_finite_dimensional
- \+ *theorem* continuous_equiv_fun_basis
- \+ *def* to_continuous_linear_map
- \+ *def* to_continuous_linear_equiv
- \+ *def* to_continuous_linear_equiv_of_det_ne_zero



## [2022-06-03 08:57:19](https://github.com/leanprover-community/mathlib/commit/31cbfbb)
feat(linear_algebra/basis): repr_support_of_mem_span ([#14504](https://github.com/leanprover-community/mathlib/pull/14504))
This lemma states that if a vector is in the span of a subset of the basis vectors, only this subset of basis vectors will be used in its `repr` representation.
#### Estimated changes
modified src/linear_algebra/basis.lean
- \+ *lemma* repr_support_subset_of_mem_span



## [2022-06-03 07:58:59](https://github.com/leanprover-community/mathlib/commit/2b69bb4)
feat(analysis/complex/upper_half_plane): extend action on upper half plane to GL_pos ([#12415](https://github.com/leanprover-community/mathlib/pull/12415))
This extends the action on the upper half plane from `SL_2` to `GL_pos`,
#### Estimated changes
modified src/analysis/complex/upper_half_plane.lean
- \+/\- *lemma* denom_ne_zero
- \+/\- *lemma* norm_sq_denom_pos
- \+/\- *lemma* norm_sq_denom_ne_zero
- \+/\- *lemma* smul_aux'_im
- \+/\- *lemma* denom_cocycle
- \+/\- *lemma* mul_smul'
- \+ *lemma* SL_on_GL_pos_smul_apply
- \+ *lemma* subgroup_on_GL_pos_smul_apply
- \+ *lemma* subgroup_on_SL_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* re_smul
- \+/\- *lemma* im_smul
- \+/\- *lemma* im_smul_eq_div_norm_sq
- \+/\- *lemma* neg_smul
- \+ *lemma* sl_moeb
- \+ *lemma* subgroup_moeb
- \+ *lemma* subgroup_to_sl_moeb
- \+ *lemma* SL_neg_smul
- \+ *lemma* special_linear_group.im_smul_eq_div_norm_sq
- \+ *lemma* denom_apply
- \+/\- *lemma* denom_ne_zero
- \+/\- *lemma* norm_sq_denom_pos
- \+/\- *lemma* norm_sq_denom_ne_zero
- \+/\- *lemma* smul_aux'_im
- \+/\- *lemma* denom_cocycle
- \+/\- *lemma* mul_smul'
- \+/\- *lemma* coe_smul
- \+/\- *lemma* re_smul
- \+/\- *lemma* im_smul
- \+/\- *lemma* im_smul_eq_div_norm_sq
- \+/\- *lemma* neg_smul
- \+/\- *def* num
- \+/\- *def* denom
- \+/\- *def* smul_aux'
- \+/\- *def* smul_aux
- \+/\- *def* num
- \+/\- *def* denom
- \+/\- *def* smul_aux'
- \+/\- *def* smul_aux

modified src/number_theory/modular.lean
- \+/\- *lemma* coe_T_zpow_smul_eq
- \- *lemma* coe_smul
- \- *lemma* re_smul
- \- *lemma* smul_coe
- \- *lemma* neg_smul
- \- *lemma* im_smul
- \- *lemma* im_smul_eq_div_norm_sq
- \- *lemma* denom_apply
- \+/\- *lemma* coe_T_zpow_smul_eq



## [2022-06-02 21:38:24](https://github.com/leanprover-community/mathlib/commit/1a1895c)
feat(data/nat/basic): add lemmas about `nat.bit_cases_on` ([#14481](https://github.com/leanprover-community/mathlib/pull/14481))
Also drop `nat.bit_cases` (was the same definition with a different
order of arguments).
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* bit_cases_on_bit
- \+ *lemma* bit_cases_on_bit0
- \+ *lemma* bit_cases_on_bit1
- \+ *lemma* bit_cases_on_injective
- \+ *lemma* bit_cases_on_inj
- \- *def* bit_cases



## [2022-06-02 19:38:29](https://github.com/leanprover-community/mathlib/commit/ade30c3)
feat(data/int/basic): Lemmas for when a square equals 1 ([#14501](https://github.com/leanprover-community/mathlib/pull/14501))
This PR adds two lemmas for when a square equals one. The `lt` lemma will be useful for irreducibility of x^n-x-1.
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* sq_eq_one_of_sq_lt_four
- \+ *lemma* sq_eq_one_of_sq_le_three



## [2022-06-02 19:38:28](https://github.com/leanprover-community/mathlib/commit/e443331)
refactor(field_theory/normal): generalize `lift_normal` and `restrict_normal` ([#14450](https://github.com/leanprover-community/mathlib/pull/14450))
This generalization seems useful. The example I have in mind is restricting a map `ϕ : E →ₐ[F] (algebraic_closure E)` to a map `ϕ : E →ₐ[F] E` when E/F is normal.
Coauthored by @mariainesdff
#### Estimated changes
modified src/field_theory/normal.lean
- \+/\- *lemma* alg_hom.lift_normal_commutes
- \+/\- *lemma* alg_hom.restrict_lift_normal
- \+/\- *lemma* alg_equiv.lift_normal_commutes
- \+/\- *lemma* alg_equiv.restrict_lift_normal
- \+/\- *lemma* alg_equiv.restrict_normal_hom_surjective
- \+/\- *lemma* is_solvable_of_is_scalar_tower
- \+/\- *lemma* alg_hom.lift_normal_commutes
- \+/\- *lemma* alg_hom.restrict_lift_normal
- \+/\- *lemma* alg_equiv.lift_normal_commutes
- \+/\- *lemma* alg_equiv.restrict_lift_normal
- \+/\- *lemma* alg_equiv.restrict_normal_hom_surjective
- \+/\- *lemma* is_solvable_of_is_scalar_tower
- \+ *def* alg_hom.restrict_normal'
- \+/\- *def* alg_equiv.restrict_normal_hom
- \+/\- *def* alg_equiv.restrict_normal_hom



## [2022-06-02 17:31:51](https://github.com/leanprover-community/mathlib/commit/ae02583)
refactor(data/set/finite): protect `set.finite` ([#14344](https://github.com/leanprover-community/mathlib/pull/14344))
This change will make it so that it does not conflict with a top-level `finite` that will be added to complement `infinite`.
#### Estimated changes
modified roadmap/topology/shrinking_lemma.lean

modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* mul_finprod_cond_ne
- \+/\- *lemma* mul_finprod_cond_ne

modified src/algebra/star/pointwise.lean
- \+/\- *lemma* finite.star
- \+/\- *lemma* finite.star

modified src/analysis/convex/combination.lean
- \+/\- *lemma* set.finite.convex_hull_eq
- \+/\- *lemma* set.finite.convex_hull_eq_image
- \+/\- *lemma* set.finite.convex_hull_eq
- \+/\- *lemma* set.finite.convex_hull_eq_image

modified src/analysis/convex/topology.lean
- \+/\- *lemma* set.finite.compact_convex_hull
- \+/\- *lemma* set.finite.is_closed_convex_hull
- \+/\- *lemma* set.finite.compact_convex_hull
- \+/\- *lemma* set.finite.is_closed_convex_hull

modified src/data/polynomial/ring_division.lean

modified src/data/set/countable.lean
- \+/\- *lemma* finite.countable
- \+/\- *lemma* finite.countable

modified src/data/set/finite.lean
- \+/\- *lemma* finite.sup
- \+/\- *lemma* finite_lt_nat
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* subsingleton.finite
- \+/\- *lemma* finite.finite_subsets
- \+/\- *lemma* finite_range_ite
- \+/\- *lemma* finite_range_const
- \+/\- *lemma* finite.fin_embedding
- \+/\- *lemma* finite_option
- \+/\- *lemma* finite_subset_Union
- \+/\- *lemma* finite_is_top
- \+/\- *lemma* finite_is_bot
- \+/\- *lemma* exists_min_image
- \+/\- *lemma* exists_max_image
- \+/\- *lemma* finite.bdd_above_bUnion
- \+/\- *lemma* finite.bdd_below_bUnion
- \+/\- *lemma* finite.sup
- \+/\- *lemma* finite_lt_nat
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* subsingleton.finite
- \+/\- *lemma* finite.finite_subsets
- \+/\- *lemma* finite_range_ite
- \+/\- *lemma* finite_range_const
- \+/\- *lemma* finite.fin_embedding
- \+/\- *lemma* finite_option
- \+/\- *lemma* finite_subset_Union
- \+/\- *lemma* finite_is_top
- \+/\- *lemma* finite_is_bot
- \+/\- *lemma* exists_min_image
- \+/\- *lemma* exists_max_image
- \+/\- *lemma* finite.bdd_above_bUnion
- \+/\- *lemma* finite.bdd_below_bUnion
- \+/\- *theorem* finite.inf_of_left
- \+/\- *theorem* finite.inf_of_right
- \+/\- *theorem* finite.of_diff
- \+/\- *theorem* finite.sUnion
- \+/\- *theorem* finite.map
- \+/\- *theorem* finite_mem_finset
- \+/\- *theorem* finite.inf_of_left
- \+/\- *theorem* finite.inf_of_right
- \+/\- *theorem* finite.of_diff
- \+/\- *theorem* finite.sUnion
- \+/\- *theorem* finite.map
- \+/\- *theorem* finite_mem_finset

modified src/data/set/pointwise.lean
- \+/\- *lemma* finite.inv
- \+/\- *lemma* finite.mul
- \+/\- *lemma* finite.smul
- \+/\- *lemma* finite.smul_set
- \+/\- *lemma* finite.vsub
- \+/\- *lemma* finite.inv
- \+/\- *lemma* finite.mul
- \+/\- *lemma* finite.smul
- \+/\- *lemma* finite.smul_set
- \+/\- *lemma* finite.vsub

modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finrank_span_le_card
- \+/\- *lemma* finrank_span_set_eq_card
- \+/\- *lemma* finrank_span_le_card
- \+/\- *lemma* finrank_span_set_eq_card

modified src/linear_algebra/linear_independent.lean

modified src/measure_theory/integral/integrable_on.lean
- \+/\- *lemma* integrable_on_finite_Union
- \+/\- *lemma* integrable_on_finite_Union

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measurable_space_def.lean
- \+/\- *lemma* set.finite.measurable_set_bUnion
- \+/\- *lemma* set.finite.measurable_set_sUnion
- \+/\- *lemma* set.finite.measurable_set_bInter
- \+/\- *lemma* set.finite.measurable_set_sInter
- \+/\- *lemma* set.finite.measurable_set
- \+/\- *lemma* set.finite.measurable_set_bUnion
- \+/\- *lemma* set.finite.measurable_set_sUnion
- \+/\- *lemma* set.finite.measurable_set_bInter
- \+/\- *lemma* set.finite.measurable_set_sInter
- \+/\- *lemma* set.finite.measurable_set

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* count_apply_finite
- \+/\- *lemma* count_apply_finite

modified src/measure_theory/measure/measure_space_def.lean
- \+/\- *lemma* measure_bUnion_lt_top
- \+/\- *lemma* measure_bUnion_lt_top

modified src/measure_theory/measure/null_measurable.lean
- \+/\- *lemma* _root_.set.finite.null_measurable_set_bUnion
- \+/\- *lemma* _root_.set.finite.null_measurable_set_sUnion
- \+/\- *lemma* _root_.set.finite.null_measurable_set_bInter
- \+/\- *lemma* _root_.set.finite.null_measurable_set_sInter
- \+/\- *lemma* _root_.set.finite.null_measurable_set_bUnion
- \+/\- *lemma* _root_.set.finite.null_measurable_set_sUnion
- \+/\- *lemma* _root_.set.finite.null_measurable_set_bInter
- \+/\- *lemma* _root_.set.finite.null_measurable_set_sInter

modified src/model_theory/finitely_generated.lean
- \+/\- *theorem* fg_closure
- \+/\- *theorem* fg_closure

modified src/order/conditionally_complete_lattice.lean
- \+/\- *lemma* set.nonempty.cSup_mem
- \+/\- *lemma* set.nonempty.cInf_mem
- \+/\- *lemma* set.finite.cSup_lt_iff
- \+/\- *lemma* set.finite.lt_cInf_iff
- \+/\- *lemma* set.nonempty.cSup_mem
- \+/\- *lemma* set.nonempty.cInf_mem
- \+/\- *lemma* set.finite.cSup_lt_iff
- \+/\- *lemma* set.finite.lt_cInf_iff

modified src/order/filter/bases.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* bInter_mem
- \+/\- *lemma* sInter_mem
- \+/\- *lemma* mem_infi_of_Inter
- \+/\- *lemma* infi_principal_finite
- \+/\- *lemma* bInter_mem
- \+/\- *lemma* sInter_mem
- \+/\- *lemma* mem_infi_of_Inter
- \+/\- *lemma* infi_principal_finite

modified src/order/filter/cofinite.lean
- \+/\- *lemma* mem_cofinite
- \+/\- *lemma* mem_cofinite

modified src/order/filter/pi.lean
- \+/\- *lemma* pi_mem_pi
- \+/\- *lemma* pi_mem_pi_iff
- \+/\- *lemma* pi_mem_pi
- \+/\- *lemma* pi_mem_pi_iff

modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* finite_sUnion_mem_iff
- \+/\- *lemma* finite_bUnion_mem_iff
- \+/\- *lemma* finite_sUnion_mem_iff
- \+/\- *lemma* finite_bUnion_mem_iff

modified src/order/locally_finite.lean
- \+/\- *lemma* finite_Icc
- \+/\- *lemma* finite_Ico
- \+/\- *lemma* finite_Ioc
- \+/\- *lemma* finite_Ioo
- \+/\- *lemma* finite_Ici
- \+/\- *lemma* finite_Ioi
- \+/\- *lemma* finite_Iic
- \+/\- *lemma* finite_Iio
- \+/\- *lemma* finite_Icc
- \+/\- *lemma* finite_Ico
- \+/\- *lemma* finite_Ioc
- \+/\- *lemma* finite_Ioo
- \+/\- *lemma* finite_Ici
- \+/\- *lemma* finite_Ioi
- \+/\- *lemma* finite_Iic
- \+/\- *lemma* finite_Iio

modified src/ring_theory/algebraic_independent.lean

modified src/ring_theory/artinian.lean

modified src/ring_theory/noetherian.lean
- \+/\- *theorem* fg_span
- \+/\- *theorem* fg_span

modified src/set_theory/cardinal/basic.lean
- \+/\- *theorem* lt_omega_iff_finite
- \+/\- *theorem* lt_omega_iff_finite

modified src/topology/G_delta.lean
- \+/\- *lemma* set.finite.is_Gδ_compl
- \+/\- *lemma* set.finite.is_Gδ
- \+/\- *lemma* set.finite.is_Gδ_compl
- \+/\- *lemma* set.finite.is_Gδ

modified src/topology/bases.lean
- \+/\- *lemma* _root_.set.finite.is_separable
- \+/\- *lemma* _root_.set.finite.is_separable

modified src/topology/basic.lean
- \+/\- *lemma* is_open_sInter
- \+/\- *lemma* is_open_bInter
- \+/\- *lemma* is_closed_bUnion
- \+/\- *lemma* is_open_sInter
- \+/\- *lemma* is_open_bInter
- \+/\- *lemma* is_closed_bUnion

modified src/topology/bornology/basic.lean
- \+/\- *lemma* is_cobounded_bInter
- \+/\- *lemma* is_cobounded_sInter
- \+/\- *lemma* is_bounded_bUnion
- \+/\- *lemma* is_bounded_sUnion
- \+/\- *lemma* is_cobounded_bInter
- \+/\- *lemma* is_cobounded_sInter
- \+/\- *lemma* is_bounded_bUnion
- \+/\- *lemma* is_bounded_sUnion

modified src/topology/constructions.lean

modified src/topology/continuous_on.lean

modified src/topology/metric_space/basic.lean
- \+/\- *lemma* bounded_bUnion
- \+/\- *lemma* bounded_of_finite
- \+/\- *lemma* bounded_bUnion
- \+/\- *lemma* bounded_of_finite

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/hausdorff_dimension.lean
- \+/\- *lemma* dimH_finite
- \+/\- *lemma* dimH_finite

modified src/topology/metric_space/metric_separated.lean
- \+/\- *lemma* finite_Union_left_iff
- \+/\- *lemma* finite_Union_right_iff
- \+/\- *lemma* finite_Union_left_iff
- \+/\- *lemma* finite_Union_right_iff

modified src/topology/metric_space/metrizable.lean

modified src/topology/metric_space/shrinking_lemma.lean
- \+/\- *lemma* exists_Union_ball_eq_radius_lt
- \+/\- *lemma* exists_Union_ball_eq_radius_lt

modified src/topology/partition_of_unity.lean

modified src/topology/separation.lean

modified src/topology/sequences.lean

modified src/topology/shrinking_lemma.lean
- \+/\- *lemma* exists_Union_eq_closure_subset
- \+/\- *lemma* exists_Union_eq_closed_subset
- \+/\- *lemma* exists_Union_eq_closure_subset
- \+/\- *lemma* exists_Union_eq_closed_subset

modified src/topology/subset_properties.lean
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* set.finite.is_compact
- \+/\- *lemma* set.finite.compact_bUnion
- \+/\- *lemma* set.finite.is_compact

modified src/topology/uniform_space/cauchy.lean



## [2022-06-02 17:31:49](https://github.com/leanprover-community/mathlib/commit/28031a8)
feat(number_theory/factorization): evaluating arithmetic functions at prime powers ([#13817](https://github.com/leanprover-community/mathlib/pull/13817))
#### Estimated changes
modified archive/100-theorems-list/70_perfect_numbers.lean

modified src/data/int/cast.lean
- \+ *theorem* cast_ite

modified src/data/list/dedup.lean
- \+ *lemma* repeat_dedup

modified src/number_theory/arithmetic_function.lean
- \+ *lemma* one_apply
- \+/\- *lemma* one_one
- \+/\- *lemma* one_apply_ne
- \+ *lemma* nat_coe_one
- \+ *lemma* int_coe_one
- \+ *lemma* mul_apply_one
- \+ *lemma* nat_coe_mul
- \+ *lemma* int_coe_mul
- \+ *lemma* pow_zero_eq_zeta
- \+/\- *lemma* sigma_one_apply
- \+ *lemma* sigma_zero_apply
- \+ *lemma* sigma_zero_apply_prime_pow
- \+ *lemma* is_multiplicative_one
- \+/\- *lemma* is_multiplicative_zeta
- \+ *lemma* card_factors_apply_prime
- \+ *lemma* card_factors_apply_prime_pow
- \+ *lemma* card_distinct_factors_one
- \+ *lemma* card_distinct_factors_apply_prime_pow
- \+ *lemma* card_distinct_factors_apply_prime
- \+/\- *lemma* moebius_apply_of_squarefree
- \+/\- *lemma* moebius_eq_zero_of_not_squarefree
- \+ *lemma* moebius_apply_one
- \+ *lemma* moebius_apply_prime
- \+ *lemma* moebius_apply_prime_pow
- \+ *lemma* moebius_apply_is_prime_pow_not_prime
- \+/\- *lemma* moebius_mul_coe_zeta
- \+/\- *lemma* coe_zeta_mul_moebius
- \+/\- *lemma* coe_moebius_mul_coe_zeta
- \+/\- *lemma* coe_zeta_mul_coe_moebius
- \+/\- *lemma* one_one
- \+/\- *lemma* one_apply_ne
- \+/\- *lemma* sigma_one_apply
- \+/\- *lemma* is_multiplicative_zeta
- \+/\- *lemma* moebius_apply_of_squarefree
- \+/\- *lemma* moebius_eq_zero_of_not_squarefree
- \+/\- *lemma* coe_moebius_mul_coe_zeta
- \+/\- *lemma* coe_zeta_mul_coe_moebius
- \+/\- *lemma* moebius_mul_coe_zeta
- \+/\- *lemma* coe_zeta_mul_moebius



## [2022-06-02 15:58:16](https://github.com/leanprover-community/mathlib/commit/0575db0)
feat(topology/vector_bundle): define some useful linear maps globally ([#14484](https://github.com/leanprover-community/mathlib/pull/14484))
* Define `pretrivialization.symmₗ`, `pretrivialization.linear_map_at`, `trivialization.symmL`, `trivialization.continuous_linear_map_at`
* These are globally-defined (continuous) linear maps. They are linear equivalences on `e.base_set`, but it is useful to define these globally. They are defined as `0` outside `e.base_set`
* These are convenient to define the vector bundle of continuous linear maps.
#### Estimated changes
modified src/topology/continuous_on.lean
- \+ *lemma* continuous_if_const

modified src/topology/vector_bundle.lean
- \+ *lemma* coe_symm_of_not_mem
- \+ *lemma* coe_linear_map_at
- \+ *lemma* coe_linear_map_at_of_mem
- \+ *lemma* linear_map_at_apply
- \+ *lemma* linear_map_at_def_of_mem
- \+ *lemma* linear_map_at_def_of_not_mem
- \+ *lemma* linear_map_at_eq_zero
- \+ *lemma* symmₗ_linear_map_at
- \+ *lemma* linear_map_at_symmₗ
- \+ *lemma* linear_equiv_at_apply
- \+ *lemma* linear_equiv_at_symm_apply
- \+ *lemma* coe_symmₗ
- \+ *lemma* coe_linear_map_at
- \+ *lemma* coe_linear_map_at_of_mem
- \+ *lemma* linear_map_at_apply
- \+ *lemma* linear_map_at_def_of_mem
- \+ *lemma* linear_map_at_def_of_not_mem
- \+ *lemma* symmₗ_linear_map_at
- \+ *lemma* linear_map_at_symmₗ
- \+ *lemma* symmL_continuous_linear_map_at
- \+ *lemma* continuous_linear_map_at_symmL
- \+ *lemma* coe_continuous_linear_equiv_at_eq
- \+ *lemma* symm_continuous_linear_equiv_at_eq
- \+ *def* continuous_linear_map_at
- \+ *def* symmL
- \+/\- *def* continuous_linear_equiv_at
- \+/\- *def* continuous_linear_equiv_at



## [2022-06-02 15:58:15](https://github.com/leanprover-community/mathlib/commit/c5f8d78)
doc(set_theory/cardinal/cofinality): add myself as author ([#14469](https://github.com/leanprover-community/mathlib/pull/14469))
#### Estimated changes
modified src/set_theory/cardinal/cofinality.lean



## [2022-06-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/4bd8c85)
feat(category_theory/limits): is_kernel_of_comp ([#14409](https://github.com/leanprover-community/mathlib/pull/14409))
From LTE.
Also rename `lift_comp_ι` to `lift_ι` for consistency with the general `has_limit` versions.
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.is_limit.lift_ι
- \+ *lemma* cofork.is_colimit.π_desc
- \- *lemma* fork.is_limit.lift_comp_ι
- \- *lemma* cofork.is_colimit.π_comp_desc

modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* is_kernel_of_comp
- \+ *def* is_cokernel_of_comp

modified src/category_theory/monad/monadicity.lean



## [2022-06-02 15:58:13](https://github.com/leanprover-community/mathlib/commit/2941590)
feat(linear_algebra/matrix): Spectral theorem for matrices ([#14231](https://github.com/leanprover-community/mathlib/pull/14231))
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.inner_eq_star_dot_product

modified src/analysis/normed_space/pi_Lp.lean
- \+/\- *lemma* equiv_apply
- \+/\- *lemma* equiv_symm_apply
- \+ *lemma* equiv_apply'
- \+ *lemma* equiv_symm_apply'
- \+/\- *lemma* equiv_apply
- \+/\- *lemma* equiv_symm_apply

modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis_to_matrix_mul
- \+ *lemma* mul_basis_to_matrix
- \+ *lemma* basis_to_matrix_basis_fun_mul

created src/linear_algebra/matrix/hermitian.lean
- \+ *lemma* is_hermitian.eq
- \+ *lemma* is_hermitian.ext
- \+ *lemma* is_hermitian.apply
- \+ *lemma* is_hermitian.ext_iff
- \+ *lemma* is_hermitian_mul_conj_transpose_self
- \+ *lemma* is_hermitian_transpose_mul_self
- \+ *lemma* is_hermitian_add_transpose_self
- \+ *lemma* is_hermitian_transpose_add_self
- \+ *lemma* is_hermitian_zero
- \+ *lemma* conj_transpose_map
- \+ *lemma* is_hermitian.map
- \+ *lemma* is_hermitian.transpose
- \+ *lemma* is_hermitian.conj_transpose
- \+ *lemma* is_hermitian.add
- \+ *lemma* is_hermitian.minor
- \+ *lemma* is_hermitian_diagonal
- \+ *lemma* is_hermitian.from_blocks
- \+ *lemma* is_hermitian_from_blocks_iff
- \+ *lemma* is_hermitian_one
- \+ *lemma* is_hermitian.neg
- \+ *lemma* is_hermitian.sub
- \+ *lemma* is_hermitian_iff_is_self_adjoint
- \+ *def* is_hermitian

created src/linear_algebra/matrix/spectrum.lean
- \+ *lemma* eigenvector_matrix_mul_inv
- \+ *theorem* spectral_theorem

modified src/linear_algebra/matrix/to_lin.lean
- \+/\- *lemma* matrix.mul_vec_std_basis
- \+ *lemma* matrix.mul_vec_std_basis_apply
- \+/\- *lemma* matrix.mul_vec_std_basis



## [2022-06-02 13:48:11](https://github.com/leanprover-community/mathlib/commit/4e1eeeb)
feat(tactic/linear_combination): allow combinations of arbitrary proofs ([#14229](https://github.com/leanprover-community/mathlib/pull/14229))
This changes the syntax of `linear_combination` so that the combination is expressed using arithmetic operation. Credit to @digama0 for the parser. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313979.20arbitrary.20proof.20terms.20in.20.60linear_combination.60) for more details.
#### Estimated changes
modified archive/100-theorems-list/37_solution_of_cubic.lean

modified archive/imo/imo2001_q6.lean

modified archive/imo/imo2008_q3.lean

modified archive/imo/imo2008_q4.lean

modified src/algebra/quadratic_discriminant.lean

modified src/data/polynomial/identities.lean

modified src/meta/expr.lean

modified src/number_theory/fermat4.lean

modified src/ring_theory/polynomial/chebyshev.lean

modified src/ring_theory/witt_vector/discrete_valuation_ring.lean

modified src/ring_theory/witt_vector/isocrystal.lean

modified src/tactic/linear_combination.lean

modified test/linear_combination.lean



## [2022-06-02 09:08:42](https://github.com/leanprover-community/mathlib/commit/57885b4)
feat(topological_space/vector_bundle): reformulate linearity condition ([#14485](https://github.com/leanprover-community/mathlib/pull/14485))
* Reformulate the linearity condition on (pre)trivializations of vector bundles using `total_space_mk`. Note: it is definitionally equal to the previous definition, but without using the coercion.
* Make one argument of `e.linear` implicit
* Simplify the proof of linearity of the product of vector bundles
#### Estimated changes
modified src/topology/vector_bundle.lean
- \- *lemma* linear



## [2022-06-01 23:57:04](https://github.com/leanprover-community/mathlib/commit/c414df7)
feat(tactic/linear_combination): allow arbitrary proof terms ([#13979](https://github.com/leanprover-community/mathlib/pull/13979))
This extends `linear_combination` to allow arbitrary proof terms of equalities instead of just local hypotheses. 
```lean
constants (qc : ℚ) (hqc : qc = 2*qc)
example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by linear_combination (h a b, 3) (hqc)
```
This changes the syntax of `linear_combination` in the case where no coefficient is provided and it defaults to 1. A space-separated list of pexprs won't parse, since there's an ambiguity in `h1 h2` between an application or two arguments. So this case now requres parentheses around the argument:
`linear_combination (h1, 3) (h2)`
Does anyone object to this syntax change?
#### Estimated changes
modified archive/imo/imo2008_q4.lean

modified src/algebra/quadratic_discriminant.lean

modified src/number_theory/fermat4.lean

modified src/tactic/linear_combination.lean

modified test/linear_combination.lean



## [2022-06-01 20:32:56](https://github.com/leanprover-community/mathlib/commit/12ad63e)
feat(order/conditionally_complete_lattice): Map `Inf` by monotone function ([#14118](https://github.com/leanprover-community/mathlib/pull/14118))
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* monotone_on.map_Inf
- \+ *lemma* monotone.map_Inf



## [2022-06-01 17:27:02](https://github.com/leanprover-community/mathlib/commit/9600f4f)
feat(order/filter/bases): view a filter as a *bundled* filter basis ([#14506](https://github.com/leanprover-community/mathlib/pull/14506))
We already have `filter.basis_sets` which says that the elements of a filter are a basis of itself (in the `has_basis` sense), but we don't have the fact that they form a filter basis (in the `filter_basis` sense), and `x ∈ f.basis_sets.is_basis.filter_basis` is not defeq to `x ∈ f`
#### Estimated changes
modified src/order/filter/bases.lean
- \+ *lemma* as_basis_filter
- \+ *def* filter.as_basis



## [2022-06-01 17:27:01](https://github.com/leanprover-community/mathlib/commit/0950ba3)
refactor(topology/separation): rename `indistinguishable` to `inseparable` ([#14401](https://github.com/leanprover-community/mathlib/pull/14401))
* Replace `indistinguishable` by `inseparable` in the definition and lemma names. The word "indistinguishable" is too generic.
* Rename `t0_space_iff_distinguishable` to `t0_space_iff_not_inseparable` because the name `t0_space_iff_separable` is misleading, slightly golf the proof.
* Add `t0_space_iff_nhds_injective`, `nhds_injective`, reorder lemmas around these two.
#### Estimated changes
modified src/algebraic_geometry/properties.lean

modified src/topology/maps.lean

modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.inseparable_iff
- \- *lemma* metric.indistinguishable_iff

modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* inseparable_iff
- \- *theorem* indistinguishable_iff

modified src/topology/separation.lean
- \+ *lemma* inseparable_iff_nhds_eq
- \+ *lemma* inseparable.map
- \+ *lemma* t0_space_iff_not_inseparable
- \+ *lemma* t0_space_iff_inseparable
- \+ *lemma* inseparable.eq
- \+ *lemma* t0_space_iff_nhds_injective
- \+ *lemma* nhds_injective
- \+/\- *lemma* nhds_eq_nhds_iff
- \+ *lemma* inseparable_iff_closed
- \+ *lemma* inseparable_iff_closure
- \+ *lemma* subtype_inseparable_iff
- \- *lemma* indistinguishable_iff_nhds_eq
- \- *lemma* indistinguishable.map
- \- *lemma* t0_space_iff_distinguishable
- \- *lemma* t0_space_iff_indistinguishable
- \+/\- *lemma* nhds_eq_nhds_iff
- \- *lemma* indistinguishable.eq
- \- *lemma* indistinguishable_iff_closed
- \- *lemma* indistinguishable_iff_closure
- \- *lemma* subtype_indistinguishable_iff
- \+ *def* inseparable
- \- *def* indistinguishable

modified src/topology/sets/opens.lean

modified src/topology/sober.lean
- \+ *lemma* inseparable_iff_specializes_and
- \- *lemma* indistinguishable_iff_specializes_and



## [2022-06-01 17:27:00](https://github.com/leanprover-community/mathlib/commit/9b3ea03)
feat(data/bundle): make arguments to proj and total_space_mk implicit ([#14359](https://github.com/leanprover-community/mathlib/pull/14359))
I will wait for a later PR to (maybe) fix the reducibility/simp of these declarations.
#### Estimated changes
modified src/data/bundle.lean
- \+/\- *lemma* total_space.proj_mk
- \+/\- *lemma* sigma_mk_eq_total_space_mk
- \+/\- *lemma* total_space.eta
- \+/\- *lemma* to_total_space_coe
- \+/\- *lemma* total_space.proj_mk
- \+/\- *lemma* sigma_mk_eq_total_space_mk
- \+/\- *lemma* total_space.eta
- \+/\- *lemma* to_total_space_coe
- \+ *def* total_space.proj
- \+/\- *def* total_space_mk
- \- *def* proj
- \+/\- *def* total_space_mk

modified src/geometry/manifold/cont_mdiff.lean

modified src/topology/fiber_bundle.lean
- \+/\- *lemma* continuous_total_space_mk
- \+/\- *lemma* continuous_total_space_mk
- \+/\- *def* proj
- \+/\- *def* proj

modified src/topology/vector_bundle.lean
- \+/\- *lemma* coe_fst
- \+/\- *lemma* mem_source
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* mk_proj_snd
- \+/\- *lemma* mk_proj_snd'
- \+/\- *lemma* proj_symm_apply
- \+ *lemma* symm_coe_proj
- \+/\- *lemma* coe_fst
- \+/\- *lemma* mem_source
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* mk_proj_snd
- \+/\- *lemma* mk_proj_snd'
- \+/\- *lemma* proj_symm_apply'
- \+/\- *lemma* apply_symm_apply'
- \+ *lemma* symm_coe_proj
- \+/\- *lemma* continuous_total_space_mk
- \+/\- *lemma* continuous_proj
- \+/\- *lemma* prod.continuous_to_fun
- \+/\- *lemma* coe_fst
- \+/\- *lemma* mem_source
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* mk_proj_snd
- \+/\- *lemma* mk_proj_snd'
- \+/\- *lemma* proj_symm_apply
- \- *lemma* symm_coe_fst'
- \+/\- *lemma* coe_fst
- \+/\- *lemma* mem_source
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* mk_proj_snd
- \+/\- *lemma* mk_proj_snd'
- \+/\- *lemma* proj_symm_apply'
- \+/\- *lemma* apply_symm_apply'
- \- *lemma* symm_coe_fst'
- \+/\- *lemma* continuous_total_space_mk
- \+/\- *lemma* continuous_proj
- \+/\- *lemma* prod.continuous_to_fun
- \+/\- *def* proj
- \+/\- *def* proj



## [2022-06-01 15:09:46](https://github.com/leanprover-community/mathlib/commit/dba797a)
feat(order/liminf_limsup): composition `g ∘ f` is bounded iff `f` is bounded ([#14479](https://github.com/leanprover-community/mathlib/pull/14479))
* If `g` is a monotone function that tends to infinity at infinity, then a filter is bounded from above under `g ∘ f` iff it is bounded under `f`, similarly for antitone functions and/or filter bounded from below.
* A filter is bounded from above under `real.exp ∘ f` iff it is is bounded from above under `f`.
* Use `monotone` in `real.exp_monotone`.
* Add `@[mono]` to `real.exp_strict_mono`.
#### Estimated changes
modified src/analysis/special_functions/exp.lean
- \+ *lemma* is_bounded_under_ge_exp_comp
- \+ *lemma* is_bounded_under_le_exp_comp

modified src/data/complex/exponential.lean
- \+/\- *lemma* exp_strict_mono
- \+/\- *lemma* exp_monotone
- \+/\- *lemma* exp_eq_one_iff
- \+/\- *lemma* exp_strict_mono
- \+/\- *lemma* exp_monotone
- \+/\- *lemma* exp_eq_one_iff

modified src/order/liminf_limsup.lean
- \+ *lemma* monotone.is_bounded_under_le_comp
- \+ *lemma* monotone.is_bounded_under_ge_comp
- \+ *lemma* antitone.is_bounded_under_le_comp
- \+ *lemma* antitone.is_bounded_under_ge_comp
- \+/\- *lemma* galois_connection.l_limsup_le
- \+/\- *lemma* galois_connection.l_limsup_le



## [2022-06-01 15:09:45](https://github.com/leanprover-community/mathlib/commit/047db39)
feat(algebra/char_p/basic): add lemma `ring_char.char_ne_zero_of_finite` ([#14454](https://github.com/leanprover-community/mathlib/pull/14454))
This adds the fact that a finite (not necessarily associative) ring cannot have characteristic zero.
See [this topic on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Statements.20about.20finite.20rings).
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* ring_char_ne_zero_of_fintype
- \+/\- *lemma* char_p_of_prime_pow_injective
- \+/\- *lemma* char_p_of_prime_pow_injective



## [2022-06-01 15:09:44](https://github.com/leanprover-community/mathlib/commit/df057e3)
feat(measure_theory/integral/lebesgue): integral over finite and countable sets ([#14447](https://github.com/leanprover-community/mathlib/pull/14447))
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean
- \+/\- *lemma* lintegral_encodable
- \+ *lemma* lintegral_singleton'
- \+ *lemma* lintegral_singleton
- \+ *lemma* lintegral_countable
- \+ *lemma* lintegral_insert
- \+ *lemma* lintegral_finset
- \+ *lemma* lintegral_fintype
- \+ *lemma* lintegral_unique
- \+/\- *lemma* lintegral_encodable



## [2022-06-01 15:09:43](https://github.com/leanprover-community/mathlib/commit/f0216ff)
refactor(combinatorics/simple_graph/basic): rename induced embedding on complete graphs ([#14404](https://github.com/leanprover-community/mathlib/pull/14404))
#### Estimated changes
modified src/combinatorics/simple_graph/basic.lean
- \- *def* complete_graph.of_embedding

modified src/combinatorics/simple_graph/coloring.lean



## [2022-06-01 15:09:42](https://github.com/leanprover-community/mathlib/commit/0a0a60c)
feat(data/set/finite,order/*): generalize some lemmas from sets to (co)frames ([#14394](https://github.com/leanprover-community/mathlib/pull/14394))
* generalize `set.Union_inter_of_monotone` to an `order.frame`;
* add dual versions, both for `(co)frame`s and sets;
* same for `set.Union_Inter_of_monotone`.
#### Estimated changes
modified src/data/set/finite.lean
- \+ *lemma* finite.supr_binfi_of_monotone
- \+ *lemma* finite.supr_binfi_of_antitone
- \+ *lemma* finite.infi_bsupr_of_monotone
- \+ *lemma* finite.infi_bsupr_of_antitone
- \+ *lemma* _root_.supr_infi_of_monotone
- \+ *lemma* _root_.supr_infi_of_antitone
- \+ *lemma* _root_.infi_supr_of_monotone
- \+ *lemma* _root_.infi_supr_of_antitone
- \+/\- *lemma* Union_Inter_of_monotone
- \+ *lemma* Union_Inter_of_antitone
- \+ *lemma* Inter_Union_of_monotone
- \+ *lemma* Inter_Union_of_antitone
- \+/\- *lemma* Union_Inter_of_monotone

modified src/data/set/lattice.lean
- \+/\- *lemma* Union_inter_of_monotone
- \+ *lemma* Union_inter_of_antitone
- \+ *lemma* Inter_union_of_monotone
- \+ *lemma* Inter_union_of_antitone
- \+/\- *lemma* Union_inter_of_monotone

modified src/order/complete_boolean_algebra.lean
- \+ *lemma* supr_inf_of_monotone
- \+ *lemma* supr_inf_of_antitone
- \+ *lemma* infi_sup_of_monotone
- \+ *lemma* infi_sup_of_antitone

modified src/order/complete_lattice.lean
- \+ *lemma* supr_infi_le_infi_supr
- \+ *lemma* le_supr_inf_supr
- \+ *lemma* infi_sup_infi_le



## [2022-06-01 15:09:41](https://github.com/leanprover-community/mathlib/commit/892f889)
feat(data/matrix/basic): lemmas about mul_vec and single ([#13835](https://github.com/leanprover-community/mathlib/pull/13835))
We seem to be proving variants of the same statement over and over again; this introduces a new lemma that we can use to prove all these variants trivially in term mode. The new lemmas are:
* `matrix.mul_vec_single`
* `matrix.single_vec_mul`
* `matrix.diagonal_mul_vec_single`
* `matrix.single_vec_mul_diagonal`
A lot of the proofs got shorter by avoiding `ext` which invokes a more powerful lemma than we actually need.
#### Estimated changes
modified src/data/matrix/basic.lean
- \+ *lemma* mul_vec_single
- \+ *lemma* single_vec_mul
- \+ *lemma* diagonal_mul_vec_single
- \+ *lemma* single_vec_mul_diagonal

modified src/linear_algebra/matrix/diagonal.lean

modified src/linear_algebra/matrix/to_lin.lean

modified src/linear_algebra/std_basis.lean



## [2022-06-01 13:00:47](https://github.com/leanprover-community/mathlib/commit/f359d55)
feat(analysis/asymptotics/asymptotics): generalize `is_O.smul` etc ([#14487](https://github.com/leanprover-community/mathlib/pull/14487))
Allow `(k₁ : α → 𝕜) (k₂ : α → 𝕜')` instead of `(k₁ k₂ : α → 𝕜)`.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* is_O_with.smul
- \+/\- *theorem* is_O.smul
- \+/\- *theorem* is_O.smul_is_o
- \+/\- *theorem* is_o.smul_is_O
- \+/\- *theorem* is_o.smul
- \+/\- *theorem* is_O_with.smul
- \+/\- *theorem* is_O.smul
- \+/\- *theorem* is_O.smul_is_o
- \+/\- *theorem* is_o.smul_is_O
- \+/\- *theorem* is_o.smul



## [2022-06-01 13:00:46](https://github.com/leanprover-community/mathlib/commit/4f1c8cf)
feat(algebra/order/group): helper lemma `0 ≤ a + |a|` ([#14457](https://github.com/leanprover-community/mathlib/pull/14457))
Helper lemma for integers and absolute values.
#### Estimated changes
modified src/algebra/order/group.lean
- \+ *lemma* add_abs_nonneg



## [2022-06-01 12:13:54](https://github.com/leanprover-community/mathlib/commit/f4fe790)
feat(topology/vector_bundle): redefine continuous coordinate change ([#14462](https://github.com/leanprover-community/mathlib/pull/14462))
* For any two trivializations, we define the coordinate change between the two trivializations: continous linear automorphism of `F`, defined by composing one trivialization with the inverse of the other. This is defined for any point in the intersection of their base sets, and we define it to be the identity function outside this set.
* Redefine `topological_vector_bundle`: we now require that this coordinate change between any two trivializations is continuous on the intersection of their base sets.
* Redefine `topological_vector_prebundle` with the existence of a continuous linear coordinate change function.
* Simplify the proofs that the coordinate change function is continuous for constructions on vector bundles.
#### Estimated changes
modified src/topology/vector_bundle.lean
- \+ *lemma* coe_coord_change
- \+ *lemma* coord_change_apply
- \+ *lemma* mk_coord_change
- \+ *lemma* coord_change_apply'
- \+ *lemma* coord_change_symm_apply
- \+/\- *lemma* comp_continuous_linear_equiv_at_eq_coord_change
- \+ *lemma* trivialization.coord_change
- \+ *lemma* trivialization_source
- \+ *lemma* trivialization_target
- \+ *lemma* local_triv_symm_apply
- \+ *lemma* local_triv_coord_change_eq
- \+/\- *lemma* continuous_on_coord_change
- \+ *lemma* coord_change_apply
- \+ *lemma* mk_coord_change
- \- *lemma* mem_source_trivialization_at
- \+/\- *lemma* continuous_on_coord_change
- \- *lemma* trans_eq_coord_change
- \+/\- *lemma* comp_continuous_linear_equiv_at_eq_coord_change
- \- *lemma* trivial_topological_vector_bundle.trivialization_source
- \- *lemma* trivial_topological_vector_bundle.trivialization_target
- \+/\- *def* linear_equiv_at
- \+/\- *def* linear_equiv_at
- \+/\- *def* coord_change
- \+ *def* trivialization
- \+/\- *def* coord_change
- \+/\- *def* linear_equiv_at
- \+/\- *def* coord_change
- \- *def* trivial_topological_vector_bundle.trivialization



## [2022-06-01 09:59:02](https://github.com/leanprover-community/mathlib/commit/60371b8)
refactor(topology/metric_space/lipschitz): use `function.End` ([#14502](https://github.com/leanprover-community/mathlib/pull/14502))
This way we avoid dependency on `category_theory`.
#### Estimated changes
modified src/topology/metric_space/lipschitz.lean



## [2022-06-01 09:59:01](https://github.com/leanprover-community/mathlib/commit/7d71343)
chore(topology/algebra/uniform_field): Wrap in namespace ([#14498](https://github.com/leanprover-community/mathlib/pull/14498))
Put everything in `topology.algebra.uniform_field` in the `uniform_space.completion` namespace.
#### Estimated changes
modified src/number_theory/function_field.lean

modified src/ring_theory/dedekind_domain/adic_valuation.lean

modified src/topology/algebra/uniform_field.lean



## [2022-06-01 09:18:43](https://github.com/leanprover-community/mathlib/commit/2a0f474)
feat(analysis/normed_space/star/character_space): compactness of the character space of a normed algebra ([#14135](https://github.com/leanprover-community/mathlib/pull/14135))
This PR puts a `compact_space` instance on `character_space 𝕜 A` for a normed algebra `A` using the Banach-Alaoglu theorem. This is a key step in developing the continuous functional calculus.
#### Estimated changes
created src/analysis/normed_space/algebra.lean
- \+ *lemma* norm_one

modified src/analysis/normed_space/weak_dual.lean
- \+ *lemma* to_normed_dual_apply

modified src/topology/algebra/module/character_space.lean
- \+ *lemma* eq_set_map_one_map_mul
- \+ *lemma* is_closed



## [2022-06-01 01:59:39](https://github.com/leanprover-community/mathlib/commit/6b18362)
feat(data/zmod/quotient): More API for `orbit_zpowers_equiv` ([#14181](https://github.com/leanprover-community/mathlib/pull/14181))
This PR adds another `symm_apply` API lemma for `orbit_zpowers_equiv`, taking `(k : ℤ)` rather than `(k : zmod (minimal_period ((•) a) b))`.
#### Estimated changes
modified src/data/zmod/quotient.lean
- \+/\- *lemma* orbit_zpowers_equiv_symm_apply
- \+ *lemma* orbit_zpowers_equiv_symm_apply'
- \+ *lemma* _root_.add_action.orbit_zmultiples_equiv_symm_apply'
- \+/\- *lemma* orbit_zpowers_equiv_symm_apply

modified src/dynamics/periodic_pts.lean
- \+ *lemma* pow_smul_mod_minimal_period
- \+ *lemma* zpow_smul_mod_minimal_period

